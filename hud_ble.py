"""
Transporte BLE para las gafas HUD de Mesa.

Módulo aparte a propósito: app80.py solo lo importa y le pasa el mismo payload
que ya manda por UDP, así el cambio en la app de siempre son 6 líneas y todo
lo nuevo (asyncio, reconexión, estado) vive acá. Si este archivo no está, o si
falta bleak, Mesa arranca igual y el HUD sigue funcionando por UDP.

Cómo se usa desde app80.py:
    import hud_ble
    hud_ble.iniciar(activo=prefs.get("hud_ble", False))
    hud_ble.enviar(payload_bytes)      # el mismo JSON que va por UDP
    hud_ble.set_activo(True/False)
    hud_ble.estado()                   # {"activo":.., "conectado":.., "detalle":".."}

Por qué un hilo con su propio event loop: bleak es asyncio y Mesa es Flask con
hilos. Mezclarlos desde el request handler sería un lío, así que acá corre un
loop propio en un hilo daemon (mismo patrón que _iniciar_pedal_serial) y los
envíos entran desde afuera con call_soon_threadsafe.

Nunca levanta una excepción hacia Mesa: si el Bluetooth no está, si las gafas
no aparecen o si la escritura falla, se anota en "detalle" y se reintenta. El
HUD es un accesorio y jamás debe poder frenar la reproducción.
"""

import asyncio
import os
import threading
import time

# Tienen que coincidir con el firmware (visorHUD-acordesBLE.ino)
NOMBRE = os.environ.get("MESA_HUD_BLE_NOMBRE", "MesaHUD")
UUID_SERVICIO = "6e6d0001-b5a3-f393-e0a9-e50e24dcca9e"
UUID_CARACT = "6e6d0002-b5a3-f393-e0a9-e50e24dcca9e"

ESCANEO_S = 8.0        # cuánto busca las gafas en cada intento
REINTENTO_S = 3.0      # pausa entre intentos fallidos
OCIOSO_S = 0.5         # cuánto duerme el hilo mientras el transporte está apagado


class _HudBLE:
    def __init__(self):
        self._loop = None
        self._hilo = None
        self._evento = None          # asyncio.Event, se crea dentro del loop
        self._activo = False
        self._conectado = False
        self._detalle = "apagado"
        self._ultimo = None          # último payload (bytes) para reenviar al reconectar
        self._pendiente = None       # payload a escribir en el próximo ciclo
        self._lock = threading.Lock()
        self._bleak_ok = None        # None = todavía no se probó a importar

    # ------------------------------------------------------------------ API

    def iniciar(self, activo=False):
        """Arranca el hilo una sola vez. Llamarla de nuevo no duplica nada."""
        self._activo = bool(activo)
        if self._hilo is not None:
            return
        self._hilo = threading.Thread(target=self._correr, daemon=True)
        self._hilo.start()

    def set_activo(self, valor):
        self._activo = bool(valor)
        if not self._activo:
            self._detalle = "apagado"
        self._despertar()

    def enviar(self, payload):
        """payload: bytes (el JSON ya serializado que se manda por UDP).
        No bloquea: deja el dato y vuelve. Si llega otro antes de que se haya
        escrito el anterior, el nuevo pisa al viejo -- lo que importa es el
        acorde actual, no la historia."""
        if not self._activo:
            return
        if isinstance(payload, str):
            payload = payload.encode("utf-8")
        with self._lock:
            self._pendiente = payload
            self._ultimo = payload
        self._despertar()

    def estado(self):
        return {
            "activo": bool(self._activo),
            "conectado": bool(self._conectado),
            "detalle": self._detalle,
            "nombre": NOMBRE,
        }

    # -------------------------------------------------------------- interno

    def _despertar(self):
        loop, evento = self._loop, self._evento
        if loop is None or evento is None:
            return
        try:
            loop.call_soon_threadsafe(evento.set)
        except RuntimeError:
            pass   # el loop se está cerrando: no es nada grave

    def _correr(self):
        self._loop = asyncio.new_event_loop()
        asyncio.set_event_loop(self._loop)
        try:
            self._loop.run_until_complete(self._principal())
        except Exception as exc:   # noqa: BLE001
            self._detalle = f"hilo BLE caído: {exc}"

    async def _principal(self):
        self._evento = asyncio.Event()
        while True:
            if not self._activo:
                self._conectado = False
                await asyncio.sleep(OCIOSO_S)
                continue

            if not self._importar_bleak():
                self._detalle = "falta bleak (pip install bleak)"
                await asyncio.sleep(REINTENTO_S * 3)
                continue

            try:
                await self._un_ciclo()
            except Exception as exc:   # noqa: BLE001
                self._conectado = False
                self._detalle = f"error: {exc}"
                await asyncio.sleep(REINTENTO_S)

    def _importar_bleak(self):
        if self._bleak_ok is not None:
            return self._bleak_ok
        try:
            import bleak  # noqa: F401
            self._bleak_ok = True
        except ImportError:
            self._bleak_ok = False
        return self._bleak_ok

    async def _un_ciclo(self):
        """Busca las gafas, se conecta y bombea acordes hasta que se corte."""
        from bleak import BleakClient, BleakScanner

        self._detalle = "buscando gafas…"
        dispositivo = await BleakScanner.find_device_by_name(NOMBRE, timeout=ESCANEO_S)
        if dispositivo is None:
            self._detalle = f"no encuentro \"{NOMBRE}\""
            await asyncio.sleep(REINTENTO_S)
            return

        self._detalle = "conectando…"
        async with BleakClient(dispositivo) as cliente:
            self._conectado = True
            self._detalle = f"conectado ({dispositivo.address})"

            # al enganchar, ponemos las gafas al día con lo último que sonó en
            # vez de dejarlas con el acorde viejo hasta el próximo cambio
            with self._lock:
                if self._ultimo is not None:
                    self._pendiente = self._ultimo

            try:
                while self._activo and cliente.is_connected:
                    with self._lock:
                        payload = self._pendiente
                        self._pendiente = None

                    if payload is not None:
                        # sin respuesta: no esperamos ACK de aplicación, así
                        # el envío no compite con el ritmo de la canción
                        await cliente.write_gatt_char(UUID_CARACT, payload, response=False)
                    else:
                        # esperamos a que llegue un acorde nuevo, con un tope
                        # para poder chequear igual si la conexión sigue viva
                        try:
                            await asyncio.wait_for(self._evento.wait(), timeout=2.0)
                        except asyncio.TimeoutError:
                            pass
                        self._evento.clear()
            finally:
                self._conectado = False
                if self._activo:
                    self._detalle = "se cortó la conexión"


_instancia = _HudBLE()

iniciar = _instancia.iniciar
set_activo = _instancia.set_activo
enviar = _instancia.enviar
estado = _instancia.estado


if __name__ == "__main__":
    # Prueba suelta, sin Mesa: manda una progresión en loop a las gafas.
    #   python hud_ble.py
    import json
    import itertools

    iniciar(activo=True)
    progresion = [("Am", "F"), ("F", "C"), ("C", "G"), ("G", "Am")]
    print(f"Buscando \"{NOMBRE}\"… (Ctrl+C para cortar)")
    try:
        for actual, siguiente in itertools.cycle(progresion):
            enviar(json.dumps({"c": actual, "n": siguiente, "d": 2.0, "b": 0, "i": 0}).encode())
            print(f"  {actual} -> {siguiente}   [{estado()['detalle']}]")
            time.sleep(2.0)
    except KeyboardInterrupt:
        print("listo")
