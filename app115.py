"""
Mesa — separador de pistas local.

Herramienta local (no hosteada) para:
  1. Subir un mp3 desde el navegador.
  2. Separarlo en pistas (voz, batería, bajo, guitarra, piano, resto) con Demucs.
  3. Reproducirlas todas sincronizadas, con mute/volumen independiente por pista.

Corre 100% en tu máquina. No sube nada a internet salvo la descarga
del modelo de Demucs la primera vez que lo usás.

Uso:
    pip install -r requirements.txt
    python app.py
    -> abrir http://127.0.0.1:5000
"""

import argparse
import io
import json
import os
import queue
import re
import socket
import ssl
import struct
import subprocess
import sys
import tempfile
import threading
import time
import unicodedata
import uuid
import wave
import zlib
from datetime import datetime, timezone
from pathlib import Path

import numpy as np
from numpy.lib.stride_tricks import sliding_window_view
from flask import Flask, Response, jsonify, redirect, render_template_string, request, send_file, send_from_directory, url_for
from werkzeug.utils import secure_filename

BASE_DIR = Path(__file__).resolve().parent
# Versión que muestra la pantalla de inicio: el número del nombre del archivo (app97.py -> "97"),
# así cada versión nueva se rotula sola. Si el archivo no tiene número, no se muestra.
_num_version = re.search(r"(\d+)", Path(__file__).stem)
VERSION_APP = _num_version.group(1) if _num_version else ""

# --- HTTPS directo, sin pasar por "tailscale serve" -------------------------
# "tailscale serve" terminaba el HTTPS y fallaba con cualquier cliente móvil
# (Android/iOS), aunque el certificado en sí es válido y la cadena está
# completa -- confirmado a mano con pyOpenSSL. La vuelta es que Flask termine
# el TLS acá mismo, con el mismo certificado, en un segundo puerto (443).
# El 5000 de siempre (http, para la ventana nativa y la LAN) sigue igual.
#
# Requisitos, una sola vez:
#   1) tailscale cert hiwifi-pc.tail356d20.ts.net   (genera los dos archivos)
#   2) tailscale serve --https=443 off              (si no, pelean por el 443)
#
# Los certificados de Tailscale duran ~90 días: cuando el aviso de "vence
# pronto" empiece a aparecer al arrancar, repetí el paso 1 (sobreescribe los
# mismos archivos, no hace falta tocar nada más acá).
TLS_CERT = Path(os.environ.get("MESA_TLS_CERT", r"C:\Windows\System32\hiwifi-pc.tail356d20.ts.net.crt"))
TLS_KEY = Path(os.environ.get("MESA_TLS_KEY", r"C:\Windows\System32\hiwifi-pc.tail356d20.ts.net.key"))
UPLOAD_DIR = BASE_DIR / "uploads"
OUTPUT_DIR = BASE_DIR / "separated"
MODEL = "htdemucs_6s"  # separa: vocals, drums, bass, guitar, piano, other
TITULO_VENTANA = "Mesa — separador de pistas"

UPLOAD_DIR.mkdir(exist_ok=True)
OUTPUT_DIR.mkdir(exist_ok=True)

app = Flask(__name__)


@app.errorhandler(ValueError)
def _error_nombre_invalido(exc):
    return jsonify({"error": str(exc)}), 400


# job_id -> {"status": "procesando"|"listo"|"error", "song": str, "log": str, "started": float}
JOBS = {}

STEM_LABELS = {
    "guitar": "Guitarra",
    "vocals": "Voz",
    "drums": "Batería",
    "bass": "Bajo",
    "piano": "Piano",
    "other": "Resto",
}
STEM_COLORS = {
    "guitar": "#e8b34c",
    "vocals": "#e2637a",
    "bass": "#4fb8b0",
    "drums": "#e0754a",
    "piano": "#9b7fd4",
    "other": "#7fb37a",
}
# Orden fijo en la consola, guitarra primero porque es el foco de la herramienta
STEM_ORDER = ["guitar", "vocals", "bass", "drums", "piano", "other"]


def escribir_atomico(ruta: Path, texto: str):
    """Escribe un archivo de datos sin dejarlo a medias nunca.

    El problema que resuelve: Path.write_text() trunca el archivo primero y
    recien despues escribe. Si el proceso muere ahi en el medio (corte de luz,
    la PC que se suspende, cerrar la ventana a mitad de un guardado), el
    archivo queda vacio o cortado -- y lo que se pierde son las correcciones
    de acordes hechas a mano, que es lo mas caro que hay aca adentro.

    La version atomica escribe en un temporal AL LADO del destino (mismo
    volumen, requisito de os.replace en Windows) y recien entonces lo renombra
    encima. os.replace es atomico: o esta el archivo viejo entero, o el nuevo
    entero, nunca uno a medio escribir.
    """
    ruta = Path(ruta)
    ruta.parent.mkdir(parents=True, exist_ok=True)
    # v103: el temporal lleva también el hilo. Con solo el PID, dos pedidos
    # simultáneos al mismo archivo compartían temporal y uno pisaba al otro.
    tmp = ruta.with_name(ruta.name + f".tmp{os.getpid()}_{threading.get_ident()}")
    try:
        with open(tmp, "w", encoding="utf-8", newline="") as f:
            f.write(texto)
            f.flush()
            os.fsync(f.fileno())   # baja a disco antes de renombrar
        os.replace(tmp, ruta)
    except Exception:
        # si algo fallo, el destino sigue intacto: solo hay que limpiar el temporal
        try:
            if tmp.exists():
                tmp.unlink()
        except OSError:
            pass
        raise


# v103: los JSON compartidos (preferencias, recientes) se leen, se modifican y
# se reescriben enteros. Sin serializar eso, dos pedidos a la vez leían el
# mismo estado viejo y el segundo en escribir borraba el cambio del primero
# (pasaba al desconectar las gafas, que apaga dos preferencias de un saque).
_LOCK_DATOS = threading.RLock()


def song_slug(filename: str) -> str:
    """Nombre de carpeta que usa demucs: el nombre de archivo sin extensión."""
    return Path(filename).stem


def stems_dir(song: str) -> Path:
    """Carpeta de stems de una canción. Valida que el nombre no se escape del
    directorio de salida: ahora que el servidor escucha en la red local, el
    nombre llega desde la URL y no hay que confiar en él a ciegas."""
    destino = (OUTPUT_DIR / MODEL / song).resolve()
    raiz = (OUTPUT_DIR / MODEL).resolve()
    # v103: la raíz misma tampoco vale. Antes "." (o "%2e" en la URL) pasaba
    # la validación y /borrar/. se llevaba la biblioteca entera.
    if raiz == destino or raiz not in destino.parents:
        raise ValueError("nombre de canción inválido")
    return destino


# Velocidades de estudio que ofrece el mezclador. Se pre-renderizan con ffmpeg
# (filtro atempo) en vez de tocar playbackRate en el navegador: playbackRate
# baja el TONO junto con la velocidad, que para practicar no sirve — los
# acordes que muestra el cartel dejarían de coincidir con lo que suena.
VELOCIDADES = (100, 85, 75, 60, 50)


# Calidades de descarga. La clave viaja en una cookie (por dispositivo), NO en
# la URL: el service worker solo cachea audio cuando la ruta no tiene
# parámetros (ver RE_AUDIO en SW_JS), así que meter "?mono=1" rompería en
# silencio la descarga offline. El sufijo del archivo mantiene separadas las
# versiones, para que alternar no obligue a reconvertir cada vez.
# "": estéreo 160k = exactamente lo que se generaba antes de que esto existiera,
# así que los mp3 ya convertidos siguen sirviendo sin tocar nada.
CALIDADES = {
    "estereo160": {"sufijo": "",        "canales": 2, "bitrate": "160k", "label": "Estéreo · 160k"},
    "mono160":    {"sufijo": "_m",      "canales": 1, "bitrate": "160k", "label": "Mono · 160k"},
    "estereo96":  {"sufijo": "_q96",    "canales": 2, "bitrate": "96k",  "label": "Estéreo · 96k"},
    "mono96":     {"sufijo": "_m_q96",  "canales": 1, "bitrate": "96k",  "label": "Mono · 96k"},
}
CALIDAD_POR_DEFECTO = "estereo160"

# Un lock por mp3 que se está generando. Sin esto, dos pedidos del mismo stem
# (la tablet y la PC a la vez, o el reintento del navegador tras un timeout
# mientras ffmpeg sigue corriendo) veían el archivo "existente" -- ffmpeg lo
# crea al arrancar -- y el segundo se llevaba un mp3 a medio escribir.
_MP3_LOCKS = {}
_MP3_LOCKS_GUARD = threading.Lock()


def _lock_mp3(ruta: Path):
    with _MP3_LOCKS_GUARD:
        return _MP3_LOCKS.setdefault(str(ruta), threading.Lock())


def calidad_pedida():
    """Calidad que pide ESTE dispositivo, por cookie. Cualquier valor raro cae
    en el default, que es el comportamiento de siempre."""
    valor = request.cookies.get("mesa_calidad", CALIDAD_POR_DEFECTO)
    return valor if valor in CALIDADES else CALIDAD_POR_DEFECTO


def asegurar_mp3_stem(carpeta: Path, stem: str, tempo: float = 1.0, calidad: str = CALIDAD_POR_DEFECTO):
    """Genera (si no existe) una versión mp3 liviana del stem, para servir al
    mezclador en vez del wav sin comprimir: por WiFi, sobre todo a otro
    dispositivo, el wav completo (varias decenas de MB por pista, x6 pistas)
    es lo que hacía que la carga tardara mucho o se colgara con una red floja.
    El wav original se conserva intacto porque el análisis de acordes/tempo
    lo sigue necesitando.

    Con tempo < 1.0 devuelve una versión más lenta CON EL MISMO TONO (atempo),
    cacheada aparte como "<stem>_t75.mp3". atempo acepta 0.5–2.0 en un solo
    filtro, así que todas las velocidades de VELOCIDADES entran directo."""
    wav = carpeta / f"{stem}.wav"
    if not wav.exists():
        return None

    cal = CALIDADES.get(calidad) or CALIDADES[CALIDAD_POR_DEFECTO]
    lento = abs(tempo - 1.0) > 1e-3
    sufijo = f"_t{int(round(tempo * 100))}" if lento else ""
    mp3 = carpeta / f"{stem}{sufijo}{cal['sufijo']}.mp3"

    def _lista():
        return mp3.exists() and mp3.stat().st_mtime >= wav.stat().st_mtime

    if _lista():
        return mp3

    # Se serializa por archivo: el segundo pedido espera a que termine el
    # primero y encuentra el mp3 ya listo, en vez de largar otro ffmpeg.
    with _lock_mp3(mp3):
        if _lista():
            return mp3
        # se escribe a un temporal al lado y recién al terminar se renombra
        # (os.replace es atómico): el nombre real nunca existe a medias.
        tmp = mp3.with_name(mp3.name + f".tmp{os.getpid()}")
        cmd = ["ffmpeg", "-y", "-i", str(wav)]
        if lento:
            cmd += ["-filter:a", f"atempo={tempo:.4f}"]
        if cal["canales"] == 1:
            cmd += ["-ac", "1"]
        cmd += ["-codec:a", "libmp3lame", "-b:a", cal["bitrate"], "-f", "mp3", str(tmp)]
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True)
            if proc.returncode != 0 or not tmp.exists():
                raise OSError(proc.stderr[-500:] if proc.stderr else "ffmpeg falló")
            os.replace(tmp, mp3)
        except (FileNotFoundError, OSError):
            try:
                if tmp.exists():
                    tmp.unlink()
            except OSError:
                pass
            return None
    return mp3


def alias_path(song: str) -> Path:
    return stems_dir(song) / "nombre.json"


def datos_cancion(song: str):
    """Título y autor/banda elegidos a mano para mostrar, si se guardaron.
    No toca la carpeta real ni ningún otro archivo -- todo lo demás (URLs,
    mezcla.json, acordes_grid.json, etc.) sigue usando el nombre de archivo
    de siempre. Si la canción tenía el alias viejo (un solo campo, de antes
    de separar título/autor), se usa como título."""
    titulo, autor = "", ""
    ruta = alias_path(song)
    if ruta.exists():
        try:
            datos = json.loads(ruta.read_text(encoding="utf-8"))
            titulo = (datos.get("titulo") or datos.get("alias") or "").strip()
            autor = (datos.get("autor") or "").strip()
        except (json.JSONDecodeError, OSError):
            pass
    return {"titulo": titulo or song, "autor": autor or "----------"}


def nombre_mostrar(song: str) -> str:
    return datos_cancion(song)["titulo"]


def iniciales_cancion(titulo: str) -> str:
    """v107: dos letras para la "portada" de cada tema (no hay carátulas)."""
    palabras = [p for p in re.split(r"[\s_\-]+", titulo or "") if p and p[0].isalnum()]
    if not palabras:
        return "?"
    if len(palabras) == 1:
        return palabras[0][:2].upper()
    return (palabras[0][0] + palabras[1][0]).upper()


def bpm_cancion(song: str):
    """v107: BPM guardado en la grilla del tema, para la lista de la portada.
    Solo lee el json que ya existe: no dispara ningún análisis."""
    try:
        bpm = json.loads((stems_dir(song) / "acordes_grid.json").read_text(encoding="utf-8")).get("bpm")
        return int(round(float(bpm))) if bpm else None
    except (OSError, ValueError, TypeError):
        return None


def _recientes_path():
    return OUTPUT_DIR / MODEL / "_recientes.json"


def registrar_apertura(song: str):
    """Anota cuándo se abrió el mezclador de esta canción, para la sección
    'Recientes' de la portada. Falla en silencio: no es crítico."""
    ruta = _recientes_path()
    with _LOCK_DATOS:
        try:
            datos = json.loads(ruta.read_text(encoding="utf-8")) if ruta.exists() else {}
        except (json.JSONDecodeError, OSError):
            datos = {}
        datos[song] = time.time()
        try:
            ruta.parent.mkdir(parents=True, exist_ok=True)
            escribir_atomico(ruta, json.dumps(datos))
        except OSError:
            pass


def obtener_recientes(canciones, n=5):
    """Las últimas canciones abiertas que sigan existiendo, más nuevas primero."""
    ruta = _recientes_path()
    if not ruta.exists():
        return []
    try:
        datos = json.loads(ruta.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return []
    disponibles = set(canciones)
    vistas = sorted((s for s in datos if s in disponibles), key=lambda s: datos[s], reverse=True)
    return vistas[:n]


def _setlists_path():
    return OUTPUT_DIR / MODEL / "_setlists.json"


def _prefs_path():
    return OUTPUT_DIR / MODEL / "_preferencias.json"


def leer_prefs():
    """Preferencias globales de la app (no por canción). Se guardan en un JSON
    en el servidor en vez de localStorage, porque en la ventana pywebview
    localStorage no es confiable (mismo motivo por el que evitamos prompt/confirm)."""
    ruta = _prefs_path()
    if not ruta.exists():
        return {}
    try:
        return json.loads(ruta.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return {}


def guardar_pref(clave, valor):
    with _LOCK_DATOS:
        prefs = leer_prefs()
        prefs[clave] = valor
        ruta = _prefs_path()
        try:
            ruta.parent.mkdir(parents=True, exist_ok=True)
            escribir_atomico(ruta, json.dumps(prefs))
        except OSError:
            pass


# --- HUD de acordes (gafas OLED) ---------------------------------------------
# Reconversión de las gafas HUD del AXIS Digital Level: en vez de recibir el
# ángulo del nivel, reciben por UDP broadcast el acorde que está sonando en
# Mesa. Todo dentro de la LAN, sin salida a internet. Portado de appVISOR1.py
# (la versión de pruebas) a la de producción, ahora con dos ajustes propios:
#   - "hud_activo": apaga/prende el envío entero. Arranca APAGADO (default
#     False) para no cambiar nada del comportamiento actual hasta que se
#     prenda a mano desde Ajustes generales.
#   - "hud_invertido": manda una bandera ("i") en el JSON que el firmware de
#     las gafas interpreta para invertir los colores de su pantalla; acá no
#     se dibuja nada, solo se propaga el flag.
# El frontend llama a POST /hud/acorde cada vez que cambia el acorde actual o
# el siguiente (ver tick() en el JS); este hilo reenvía ese último estado por
# broadcast cada HUD_KEEPALIVE_S como red de seguridad, porque UDP puede
# perder paquetes y no queremos que las gafas se queden trabadas en un acorde
# viejo hasta el próximo cambio real.
HUD_UDP_PORT = int(os.environ.get("MESA_HUD_PORT", "4211"))
HUD_KEEPALIVE_S = 1.5

# v99: tres campos más, todos opcionales para el firmware (si faltan se porta
# como siempre): "m" = modo (0 acordes, 1 título del tema, 2 cuenta regresiva),
# "t" = título (viaja solo en modo 1) y "r" = 1 cuando el PRÓXIMO acorde trae
# un cambio de rasgueo.
HUD_TITULO_MAX = 40
# v100: "p" = traste de la cejilla (viaja solo con el título, modo 1) y
# "k" = contraste del OLED 0-255, que sale del nivel de brillo 1-5 elegido en
# Ajustes generales ("hud_brillo"). El nivel 3 es el 50 que el firmware traía
# fijo, así que sin tocar nada las gafas se ven igual que antes.
HUD_BRILLOS = (1, 20, 50, 120, 255)
HUD_BRILLO_DEFECTO = 3


def _hud_nivel_brillo(valor):
    try:
        nivel = int(valor)
    except (TypeError, ValueError):
        nivel = HUD_BRILLO_DEFECTO
    return max(1, min(len(HUD_BRILLOS), nivel))


_hud_estado = {"c": "-", "n": None, "d": None, "b": -1, "i": 0, "m": 0, "t": "", "r": 0, "p": 0,
               "k": HUD_BRILLOS[HUD_BRILLO_DEFECTO - 1]}
_hud_lock = threading.Lock()
_hud_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
_hud_socket.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)

_prefs_iniciales = leer_prefs()
_hud_activo = bool(_prefs_iniciales.get("hud_activo", False))
_hud_invertido = bool(_prefs_iniciales.get("hud_invertido", False))
_hud_estado["i"] = 1 if _hud_invertido else 0
_hud_brillo = _hud_nivel_brillo(_prefs_iniciales.get("hud_brillo", HUD_BRILLO_DEFECTO))
_hud_estado["k"] = HUD_BRILLOS[_hud_brillo - 1]

# Transporte BLE para las gafas (ver hud_ble.py). Es opcional de punta a punta:
# si el módulo no está, o si falta bleak, Mesa arranca igual y el HUD sigue
# yendo por UDP exactamente como antes. Arranca APAGADO salvo que la
# preferencia diga lo contrario, igual que "hud_activo".
try:
    import hud_ble
except ImportError:
    hud_ble = None

_hud_ble_activo = bool(_prefs_iniciales.get("hud_ble", False))
if hud_ble is not None:
    hud_ble.iniciar(activo=_hud_ble_activo)


def _hud_sanear(texto):
    """La fuente por default de la librería OLED de las gafas no tiene el
    caracter — (em dash) que usa Mesa para "sin acorde": lo dibuja como
    glifos sueltos y raros. Se reemplaza por un guion ASCII simple, solo
    para lo que se manda al HUD -- no toca cómo se ve en Mesa."""
    if texto is None:
        return None
    return texto.replace("—", "-")


def _hud_sanear_titulo(texto):
    """Las fuentes del OLED son ASCII de 7 bits: una á o una ñ salen como
    glifos basura. Se pasan a su letra base (á→a, ñ→n), se descarta lo que
    no sea ASCII imprimible y se corta para que el JSON entre holgado en una
    sola escritura BLE."""
    if not texto:
        return ""
    plano = unicodedata.normalize("NFD", str(texto))
    plano = "".join(ch for ch in plano if " " <= ch <= "~")
    return " ".join(plano.split())[:HUD_TITULO_MAX]


def _hud_enviar():
    if not _hud_activo:
        return
    with _hud_lock:
        estado = dict(_hud_estado)
    if estado["m"] != 1:
        estado.pop("t", None)   # el título y la cejilla solo viajan cuando se muestran
        estado.pop("p", None)
    payload = json.dumps(estado, separators=(",", ":")).encode("utf-8")
    try:
        _hud_socket.sendto(payload, ("255.255.255.255", HUD_UDP_PORT))
    except OSError:
        pass  # sin red disponible en este momento: no corta Mesa por esto
    # El MISMO payload por BLE. enviar() no bloquea ni levanta excepciones:
    # deja el dato y vuelve; el hilo de hud_ble se encarga de escribirlo.
    if hud_ble is not None and _hud_ble_activo:
        hud_ble.enviar(payload)


def _hud_actualizar(actual, siguiente, duracion, beat, modo=0, titulo="", rasgueo=0, capo=0):
    try:
        modo = int(modo)
    except (TypeError, ValueError):
        modo = 0
    try:
        capo = max(0, min(11, int(capo)))
    except (TypeError, ValueError):
        capo = 0
    if modo not in (0, 1, 2):
        modo = 0
    with _hud_lock:
        _hud_estado["c"] = _hud_sanear(actual) or "-"
        _hud_estado["n"] = _hud_sanear(siguiente)
        _hud_estado["d"] = duracion
        _hud_estado["b"] = beat
        _hud_estado["m"] = modo
        _hud_estado["t"] = _hud_sanear_titulo(titulo)
        _hud_estado["r"] = 1 if rasgueo else 0
        _hud_estado["p"] = capo
    _hud_enviar()


def _hud_set_activo(valor):
    global _hud_activo
    _hud_activo = bool(valor)
    if _hud_activo:
        _hud_enviar()  # al prenderlo, que las gafas se pongan al día ya mismo


def _hud_set_invertido(valor):
    global _hud_invertido
    _hud_invertido = bool(valor)
    with _hud_lock:
        _hud_estado["i"] = 1 if _hud_invertido else 0
    _hud_enviar()  # que el cambio de color se vea al toque, sin esperar al próximo acorde


def _hud_set_brillo(valor):
    global _hud_brillo
    _hud_brillo = _hud_nivel_brillo(valor)
    with _hud_lock:
        _hud_estado["k"] = HUD_BRILLOS[_hud_brillo - 1]
    _hud_enviar()  # que el brillo cambie al toque
    return _hud_brillo


def _hud_ble_set_activo(valor):
    global _hud_ble_activo
    _hud_ble_activo = bool(valor)
    if hud_ble is not None:
        hud_ble.set_activo(_hud_ble_activo)
        if _hud_ble_activo:
            _hud_enviar()   # que las gafas se pongan al día apenas se prende


def _hud_keepalive_loop():
    while True:
        time.sleep(HUD_KEEPALIVE_S)
        _hud_enviar()


threading.Thread(target=_hud_keepalive_loop, daemon=True).start()


@app.route("/hud/acorde", methods=["POST"])
def hud_acorde():
    """El frontend llama esto cada vez que cambia el acorde actual/siguiente
    o el tiempo (beat) dentro del compás. Dispara el broadcast UDP para las
    gafas (si "hud_activo" está prendido). La duración ("d", en segundos) se
    manda solo para que las gafas animen la barra de avance con su propio
    reloj -- no hace falta reenviar posición en cada frame."""
    datos = request.get_json(silent=True) or {}
    _hud_actualizar(datos.get("actual"), datos.get("siguiente"), datos.get("duracion"), datos.get("beat", -1),
                    modo=datos.get("modo", 0), titulo=datos.get("titulo", ""), rasgueo=datos.get("rasgueo", 0),
                    capo=datos.get("capo", 0))
    return jsonify({"ok": True})


@app.route("/hud/estado")
def hud_estado():
    """Estado del enlace BLE con las gafas, para el chip de Ajustes generales.
    Sin esto no hay forma de saber si la PC enganchó las gafas o si las está
    buscando -- que es justo el dato que se necesita ANTES de empezar a tocar,
    no a mitad del tema."""
    if hud_ble is None:
        return jsonify({"activo": False, "conectado": False,
                        "detalle": "falta hud_ble.py", "nombre": ""})
    return jsonify(hud_ble.estado())


def leer_setlists():
    ruta = _setlists_path()
    if not ruta.exists():
        return {}
    try:
        return json.loads(ruta.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return {}


def guardar_setlists(datos):
    ruta = _setlists_path()
    ruta.parent.mkdir(parents=True, exist_ok=True)
    escribir_atomico(ruta, json.dumps(datos))


def setlists_de_cancion(song: str, setlists=None):
    """En qué setlists aparece esta canción (para no dejar referencias
    colgadas si se borra la canción)."""
    setlists = leer_setlists() if setlists is None else setlists
    return [sid for sid, sl in setlists.items() if song in sl.get("canciones", [])]


def urls_offline_cancion(song: str, setlists=None):
    """Todo lo que hay que guardar en el caché del navegador para tocar esta
    canción sin wifi: la página de la mesa (y su variante con ?setlist=... por
    cada setlist donde está, para que Anterior/Siguiente sigan andando), las
    páginas de esos setlists, los datos que la mesa pide al cargar (acordes,
    mezcla, marcas de rasgueo), la portada y los stems al 100%."""
    carpeta = stems_dir(song)
    disponibles = {p.stem for p in carpeta.glob("*.wav")}
    ids = setlists_de_cancion(song, setlists)
    urls = [url_for("mesa", song=song)]
    urls += [url_for("mesa", song=song, setlist=sid) for sid in ids]
    urls += [url_for("ver_setlist", setlist_id=sid) for sid in ids]
    urls += [url_for("acordes", song=song), url_for("obtener_mezcla", song=song),
             url_for("obtener_rasgueo", song=song), url_for("home")]
    urls += [url_for("archivo_pista", song=song, stem=stem) for stem in STEM_ORDER if stem in disponibles]
    return urls


def urls_offline_partidas(song: str, setlists=None):
    """Lo mismo que urls_offline_cancion pero devuelto en dos grupos:
    (paginas, audio). Las páginas cambian cada vez que se toca la app y pesan
    unos KB; el audio no cambia nunca una vez separado y pesa decenas de MB.
    Esa distinción es la que le permite al botón "Descargar todas" actualizar
    la biblioteca entera en segundos en vez de rebajar todo de cero."""
    carpeta = stems_dir(song)
    disponibles = {p.stem for p in carpeta.glob("*.wav")}
    ids = setlists_de_cancion(song, setlists)
    paginas = [url_for("mesa", song=song)]
    paginas += [url_for("mesa", song=song, setlist=sid) for sid in ids]
    paginas += [url_for("ver_setlist", setlist_id=sid) for sid in ids]
    paginas += [url_for("acordes", song=song), url_for("obtener_mezcla", song=song),
                url_for("obtener_rasgueo", song=song)]
    audio = [url_for("archivo_pista", song=song, stem=stem)
             for stem in STEM_ORDER if stem in disponibles]
    return paginas, audio


def _peso_audio_estimado(song: str, calidad: str):
    """Suma el tamaño de los mp3 que YA existen para esa calidad. No dispara
    ffmpeg: si un stem todavía no fue convertido cuenta 0, así que el número
    es un piso, no un total exacto. Alcanza para avisar antes de largar una
    descarga que puede ser de varios cientos de MB."""
    carpeta = stems_dir(song)
    cal = CALIDADES.get(calidad) or CALIDADES[CALIDAD_POR_DEFECTO]
    total = 0
    for stem in STEM_ORDER:
        mp3 = carpeta / f"{stem}{cal['sufijo']}.mp3"
        try:
            if mp3.exists():
                total += mp3.stat().st_size
        except OSError:
            pass
    return total


@app.route("/offline/todas")
def offline_todas():
    """Plan para guardar la biblioteca entera y poder tocar sin wifi."""
    setlists = leer_setlists()
    calidad = calidad_pedida()
    canciones = []
    for c in list_ready_songs():
        try:
            paginas, audio = urls_offline_partidas(c, setlists)
        except ValueError:
            continue   # nombre raro: se saltea en vez de tirar la lista entera
        canciones.append({
            "song": c,
            "titulo": nombre_mostrar(c),
            "paginas": paginas,
            "audio": audio,
            "bytes": _peso_audio_estimado(c, calidad),
        })
    return jsonify({"comunes": [url_for("home")], "canciones": canciones})


def jobs_activos():
    """Trabajos que todavía están corriendo, para poder volver a su pantalla
    desde la portada (antes, si cerrabas la pestaña, el job seguía pero no
    había forma de encontrarlo)."""
    activos = []
    # v112: copia de la lista; otro hilo puede agregar un job mientras se recorre
    for jid, j in list(JOBS.items()):
        if j["status"] in ("listo", "error"):
            continue
        activos.append({
            "id": jid, "status": j["status"], "song": j.get("song"),
            "elapsed": round(time.time() - j["started"]),
        })
    activos.sort(key=lambda x: -x["elapsed"])
    return activos


def list_ready_songs():
    model_dir = OUTPUT_DIR / MODEL
    if not model_dir.exists():
        return []
    return sorted(
        p.name for p in model_dir.iterdir()
        if p.is_dir() and any(p.glob("*.wav"))
    )


def _esperar_servidor(host="127.0.0.1", port=5000, intentos=50):
    """Espera a que Flask esté escuchando antes de abrir la ventana/imprimir la URL."""
    for _ in range(intentos):
        try:
            with socket.create_connection((host, port), timeout=0.3):
                return True
        except OSError:
            time.sleep(0.1)
    return False


def _ip_local():
    """IP de la PC en la red WiFi/LAN (para abrir la app desde otro dispositivo, ej. una tablet)."""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("8.8.8.8", 80))  # no se manda nada, solo sirve para elegir la interfaz de red
        return s.getsockname()[0]
    except OSError:
        return None
    finally:
        s.close()


# Navegadores donde probar sacar las cookies de YouTube, en ese orden.
# Se usan SOLO como plan B: desde agosto 2026 YouTube rechaza casi cualquier
# pedido de yt-dlp que venga con cookies ("The page needs to be reloaded",
# ver yt-dlp#17389, abierto), mientras que sin cookies los videos públicos
# bajan sin problema. Así que primero se intenta sin cookies, y recién si
# YouTube pide sesión (video privado, con restricción de edad, o "Sign in to
# confirm you're not a bot") se recorren estos navegadores.
#
# Firefox va primero a propósito: desde Chrome 127, Chrome y todo lo que
# corre sobre su motor (Edge, Brave, Opera, Vivaldi) cifra el archivo de
# cookies con una clave atada al propio proceso del navegador, y yt-dlp no
# puede leerlo ni con el navegador cerrado. Firefox no hace eso.
NAVEGADORES_COOKIES = ["firefox", "edge", "chrome"]

# Cliente de YouTube a usar cuando se mandan cookies. El que yt-dlp elige
# solo para usuarios logueados (tv_downgraded) es el que está roto; este es
# el que recomiendan los mantenedores en yt-dlp#17389.
ARGS_CLIENTE_COOKIES = ["--extractor-args", "youtube:player_client=default,web_embedded"]

# Warning que yt-dlp imprime cuando no encuentra Deno (u otro runtime de JS).
# Sin eso YouTube devuelve menos formatos y a veces falla; conviene avisar
# una vez en el log del job, sin frenar la descarga.
_AVISO_SIN_JS = "no supported javascript runtime"
_TEXTO_AVISO_DENO = (
    "Aviso: yt-dlp no encontró un runtime de JavaScript (Deno). Sin eso YouTube "
    "entrega menos formatos y algunas descargas fallan. Instalalo una sola vez con:\n"
    "  winget install DenoLand.Deno\n"
    "  pip install -U \"yt-dlp[default]\""
)


def _correr_yt_dlp(args_extra, url, timeout=None, reintentos_transitorios=2):
    """Corre yt-dlp con esos argumentos + la url al final. Si YouTube devuelve
    'The page needs to be reloaded' -- un error del lado de YouTube,
    documentado como intermitente (a veces sale bien reintentando al toque,
    ver yt-dlp#17405) -- reintenta unas pocas veces antes de rendirse, en vez
    de darlo por perdido en el primer golpe."""
    proc = None
    for _ in range(reintentos_transitorios + 1):
        proc = subprocess.run(
            [sys.executable, "-m", "yt_dlp", *args_extra, url],
            capture_output=True, text=True, timeout=timeout,
        )
        if proc.returncode == 0:
            return proc
        salida = proc.stderr or proc.stdout
        if "page needs to be reloaded" not in salida.lower():
            return proc
    return proc


def _pide_sesion(salida_baja: str) -> bool:
    """True si el error de yt-dlp es de los que se arreglan mandando cookies
    de una cuenta logueada (y no un problema del link, de la red, etc.)."""
    return any(
        marca in salida_baja
        for marca in (
            "sign in to confirm",
            "not a bot",
            "sign in to confirm your age",
            "age-restricted",
            "private video",
            "members-only",
            "login required",
            "requires login",
        )
    )


def _titulo_de(proc) -> str:
    return proc.stdout.strip().splitlines()[0] if proc.stdout.strip() else ""


def _resolver_navegador_cookies(url: str):
    """Plan B: prueba leer el título del video con las cookies de cada
    navegador de NAVEGADORES_COOKIES, hasta encontrar uno logueado en YouTube.
    Devuelve (navegador, titulo, None) si alguno funcionó -- ese mismo
    navegador se reusa después para la descarga real -- o (None, None, motivo)
    si ninguno sirvió. 'motivo' junta lo que pasó con CADA navegador (uno por
    línea), no solo el último."""
    intentos = []
    for nav in NAVEGADORES_COOKIES:
        proc = _correr_yt_dlp(
            ["--cookies-from-browser", nav, *ARGS_CLIENTE_COOKIES,
             "--print", "%(title)s", "--skip-download", "--no-playlist"],
            url, timeout=30,
        )
        if proc.returncode == 0 and _titulo_de(proc):
            return nav, _titulo_de(proc), None
        salida = proc.stderr or proc.stdout
        salida_baja = salida.lower()
        if "could not find" in salida_baja and "cookies database" in salida_baja:
            intentos.append(f"{nav}: no está instalado en esta PC")
            continue
        if "could not copy" in salida_baja and "cookie database" in salida_baja:
            intentos.append(f"{nav}: Windows le bloquea el archivo de cookies a yt-dlp (pasa siempre con Edge y Chrome)")
            continue
        if "page needs to be reloaded" in salida_baja:
            intentos.append(f"{nav}: las cookies se leyeron bien, pero YouTube rechazó el pedido (bug de YouTube con cookies, yt-dlp#17389)")
            continue
        lineas = salida.strip().splitlines()
        ultima = lineas[-1].strip() if lineas else "no se pudo leer el video"
        intentos.append(f"{nav}: {ultima}")
    return None, None, "\n".join(intentos)


def _explicar_fallo_cookies(motivo: str) -> str:
    """Arma el texto del cartel cuando ningún navegador sirvió. Mira primero
    el fallo más 'avanzado' (el que llegó hasta YouTube), no el primero de la
    lista, para no mandar a instalar Firefox cuando Firefox fue justo el que
    más lejos llegó."""
    detalle = "Ese video necesita sesión de YouTube, y no se pudo usar la de ningún navegador:\n" + motivo
    m = motivo.lower()
    if "rechazó el pedido" in m:
        detalle += (
            "\n\nEsto es un bug conocido de YouTube con yt-dlp cuando se mandan cookies "
            "(yt-dlp#17389), no un problema de tu PC ni de Mesa. Hasta que lo arreglen, "
            "los videos que exigen sesión (privados, con restricción de edad) no se pueden "
            "bajar; los públicos siguen bajando normal."
        )
    elif "sign in" in m or "not a bot" in m:
        detalle += (
            "\n\nProbá esto: iniciá sesión en tu cuenta de YouTube desde Firefox en esta PC "
            "y volvé a intentar."
        )
    elif "no está instalado" in m and "bloquea el archivo" in m:
        detalle += (
            "\n\nEdge y Chrome no se pueden usar para esto en Windows (limitación de esos "
            "navegadores). Si necesitás bajar videos con sesión: instalá Firefox e iniciá "
            "sesión en YouTube ahí una sola vez."
        )
    return detalle


def descargar_youtube(job_id: str, url: str):
    """Baja el audio de un video de YouTube como mp3 (vía yt-dlp) y lo entrega
    a run_demucs, exactamente como si lo hubieras subido a mano.

    Orden: primero SIN cookies (es lo que funciona hoy y alcanza para casi
    todo); si YouTube pide sesión, recién ahí se prueban las cookies de los
    navegadores."""
    JOBS[job_id]["status"] = "descargando"
    aviso_deno = ""
    try:
        # --- 1) sin cookies -------------------------------------------------
        proc = _correr_yt_dlp(
            ["--print", "%(title)s", "--skip-download", "--no-playlist"],
            url, timeout=30,
        )
        salida = (proc.stderr or "") + (proc.stdout or "")
        if _AVISO_SIN_JS in salida.lower():
            aviso_deno = _TEXTO_AVISO_DENO
        titulo = _titulo_de(proc) if proc.returncode == 0 else ""
        args_cookies = []

        # --- 2) con cookies, solo si hace falta sesión ----------------------
        if not titulo:
            salida_baja = salida.lower()
            if _pide_sesion(salida_baja):
                navegador, titulo, motivo = _resolver_navegador_cookies(url)
                if titulo:
                    args_cookies = ["--cookies-from-browser", navegador, *ARGS_CLIENTE_COOKIES]
                else:
                    JOBS[job_id]["status"] = "error"
                    JOBS[job_id]["log"] = _explicar_fallo_cookies(motivo or "")
                    return
            else:
                JOBS[job_id]["status"] = "error"
                if "page needs to be reloaded" in salida_baja:
                    detalle = (
                        "YouTube tuvo un traspié leyendo el video (se reintentó solo, sin éxito). "
                        "Es un problema del lado de YouTube -- probá de nuevo en un rato. Si sigue "
                        "así, actualizá yt-dlp: pip install -U \"yt-dlp[default]\""
                    )
                else:
                    lineas = salida.strip().splitlines()
                    ultima = lineas[-1].strip() if lineas else ""
                    detalle = "No se pudo leer ese video (revisá el link)."
                    if ultima:
                        detalle += "\n" + ultima
                if aviso_deno:
                    detalle += "\n\n" + aviso_deno
                JOBS[job_id]["log"] = detalle
                return

        base = secure_filename(titulo) or f"youtube_{job_id[:8]}"
        nombre, contador = base, 2
        destino = UPLOAD_DIR / f"{nombre}.mp3"
        while destino.exists():  # no pisar un mp3 ya subido con el mismo nombre
            nombre = f"{base}_{contador}"
            destino = UPLOAD_DIR / f"{nombre}.mp3"
            contador += 1

        proc = _correr_yt_dlp(
            [
                *args_cookies,
                "-x", "--audio-format", "mp3", "--audio-quality", "0",
                "--no-playlist",
                "-o", str(UPLOAD_DIR / f"{nombre}.%(ext)s"),
            ],
            url,
        )
        if proc.returncode != 0 or not destino.exists():
            JOBS[job_id]["status"] = "error"
            error_crudo = proc.stderr[-4000:] or "No se pudo descargar el audio de ese video."
            if "page needs to be reloaded" in error_crudo.lower():
                detalle = (
                    "YouTube tuvo un traspié leyendo el video (se reintentó solo, sin éxito). "
                    "Es un problema del lado de YouTube, no de tu PC -- probá de nuevo en un rato."
                )
            else:
                detalle = error_crudo
            if aviso_deno:
                detalle += "\n\n" + aviso_deno
            JOBS[job_id]["log"] = detalle
            return

        if aviso_deno:
            JOBS[job_id]["log"] = aviso_deno
        JOBS[job_id]["song"] = song_slug(destino.name)
        run_demucs(job_id, destino)
    except subprocess.TimeoutExpired:
        JOBS[job_id]["status"] = "error"
        JOBS[job_id]["log"] = "YouTube tardó demasiado en responder. Probá de nuevo."
    except FileNotFoundError:
        JOBS[job_id]["status"] = "error"
        JOBS[job_id]["log"] = (
            "No se encontró yt-dlp. Instalá las dependencias con:\n"
            "  pip install -r requirements.txt"
        )
    except Exception as exc:  # noqa: BLE001
        JOBS[job_id]["status"] = "error"
        JOBS[job_id]["log"] = str(exc)


# Demucs de a uno: dos subidas seguidas corrían dos Demucs a la vez (cada uno
# con sus GB de RAM). El estado "en_cola" ahora significa exactamente eso.
DEMUCS_LOCK = threading.Lock()


# v113: porcentaje real de la separación. Demucs dibuja una barra tqdm en la
# salida de error ("  45%|████   | 105.3/234.0 [00:30<00:37, ...]"); se lee
# en vivo en vez de esperar a que termine. Si el modelo es un "bag" de N
# modelos, Demucs lo avisa y dibuja N barras seguidas: se encadenan.
# Reparto del 100 %: separación 0–92 %, armado de los mp3 livianos 92–100 %.
_RE_PCT_DEMUCS = re.compile(r"(\d{1,3})%\|")
_RE_BAG_DEMUCS = re.compile(r"bag of (\d+) models")
_PCT_SEPARACION = 92.0


def _seguir_demucs(job: dict, proc) -> str:
    """Lee la salida de Demucs mientras corre, actualiza job["progreso"] y
    job["estimado"] (segundos totales desde que empezó el job) y devuelve el
    final del texto (para mostrarlo si falla)."""
    texto_log = []          # líneas completas (sin los redibujos de la barra)
    pendiente = ""
    n_modelos, pasada, pct_prev = 1, 0, 0
    t_barras = None         # primer % visto: excluye la carga del modelo del cálculo
    while True:
        trozo = proc.stdout.read1(4096)
        if not trozo:
            break
        pendiente += trozo.decode("utf-8", errors="replace")
        partes = re.split(r"(\r|\n)", pendiente)
        pendiente = partes.pop()            # lo último puede estar a medias
        linea = ""
        for parte in partes:
            if parte == "\n":
                if linea.strip() and not _RE_PCT_DEMUCS.search(linea):
                    texto_log.append(linea)
                linea = ""
                continue
            if parte == "\r":
                linea = ""
                continue
            linea = parte
            m = _RE_BAG_DEMUCS.search(parte)
            if m:
                n_modelos = max(1, int(m.group(1)))
            m = _RE_PCT_DEMUCS.search(parte)
            if not m:
                continue
            pct = min(100, int(m.group(1)))
            if pct + 50 < pct_prev and pasada + 1 < n_modelos:
                pasada += 1                 # arrancó la barra del modelo siguiente
            pct_prev = pct
            ahora = time.time()
            if t_barras is None:
                t_barras = ahora
                job["etapa"] = "separando"
            frac = min(1.0, (pasada + pct / 100.0) / n_modelos)
            job["progreso"] = round(frac * _PCT_SEPARACION, 1)
            if frac >= 0.03:
                ritmo = (ahora - t_barras) / frac          # segundos por "separación entera"
                restante = ritmo * (1.0 - frac) + 0.08 * ritmo   # + los mp3
                job["estimado"] = round(ahora - job["started"] + restante)
        if len(texto_log) > 200:
            del texto_log[:-200]
    if pendiente.strip():
        texto_log.append(pendiente.split("\r")[-1])
    return "\n".join(texto_log)[-4000:]


def run_demucs(job_id: str, input_path: Path):
    JOBS[job_id]["status"] = "en_cola"
    job = JOBS[job_id]
    try:
        with DEMUCS_LOCK:
            job["status"] = "procesando"
            job["etapa"] = "cargando"
            job["progreso"] = 0.0
            job.pop("estimado", None)
            entorno = dict(os.environ, PYTHONUNBUFFERED="1", PYTHONIOENCODING="utf-8")
            proc = subprocess.Popen(
                [sys.executable, "-m", "demucs", "-n", MODEL, "-o", str(OUTPUT_DIR), str(input_path)],
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=entorno,
            )
            try:
                salida = _seguir_demucs(job, proc)
            finally:
                proc.wait()
            if proc.returncode != 0:
                JOBS[job_id]["status"] = "error"
                JOBS[job_id]["log"] = salida
            else:
                carpeta = stems_dir(song_slug(input_path.name))
                job["etapa"] = "mp3"
                job["progreso"] = _PCT_SEPARACION
                t_mp3 = time.time()
                for i, stem in enumerate(STEM_ORDER):
                    asegurar_mp3_stem(carpeta, stem)
                    hechos = i + 1
                    job["progreso"] = round(_PCT_SEPARACION + (100 - _PCT_SEPARACION) * hechos / len(STEM_ORDER), 1)
                    por_stem = (time.time() - t_mp3) / hechos
                    job["estimado"] = round(time.time() - job["started"] + por_stem * (len(STEM_ORDER) - hechos))
                job["progreso"] = 100.0
                JOBS[job_id]["status"] = "listo"
    except FileNotFoundError:
        JOBS[job_id]["status"] = "error"
        JOBS[job_id]["log"] = (
            "No se encontró demucs. Instalá las dependencias con:\n"
            "  pip install -r requirements.txt"
        )
    except Exception as exc:  # noqa: BLE001
        JOBS[job_id]["status"] = "error"
        JOBS[job_id]["log"] = str(exc)


# --------------------------------------------------------- detección de acordes ----
# Chroma casero (proyección directa sobre 52 frecuencias MIDI 40-91, sin CQT/numba)
# + comparación contra plantillas de tríadas. Deliberadamente sin librosa: esa
# dependencia arrastra numba, que tuvo el mismo lío de compatibilidad con Python
# 3.14 que ya vimos con torch. Esto solo usa numpy (ya instalado por torch/demucs).

NOTE_NAMES = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]
TRIADAS = {"": [0, 4, 7], "m": [0, 3, 7], "7": [0, 4, 7, 10]}

# Sufijos que se aceptan al editar a mano en la grilla o al importar desde MIDI,
# ADEMÁS de los que ya reconoce el detector automático (TRIADAS). El detector
# nunca va a proponer estos solo (no compara contra ellos, a propósito: son muy
# parecidos a un acorde mayor común y agregarlos como plantilla arriesgaría
# confundir un C con un Cmaj7 en canciones donde no corresponde). Pero si el
# acorde viene identificado en un MIDI, o si lo escribís vos a mano, se acepta
# tal cual.
# v108: sus4 con el mismo criterio que maj7 (difiere del mayor en una sola nota:
# como plantilla del detector daría falsos positivos). Solo edición/importación.
SUFIJOS_EXTRA_EDICION = {"maj7": [0, 4, 7, 11], "sus4": [0, 5, 7]}
SUFIJOS_VALIDOS = {**TRIADAS, **SUFIJOS_EXTRA_EDICION}


def _cargar_wav_mono(path):
    with wave.open(str(path), "rb") as wf:
        sr = wf.getframerate()
        n = wf.getnframes()
        sw = wf.getsampwidth()
        ch = wf.getnchannels()
        raw = wf.readframes(n)
    if sw == 2:
        data = np.frombuffer(raw, dtype=np.int16).astype(np.float32) / 32768.0
    elif sw == 3:
        # 24 bits (demucs --int24). Antes caía en la rama de 8 bits y el análisis
        # trabajaba sobre ruido. numpy no tiene int24: se arma a mano.
        b = np.frombuffer(raw, dtype=np.uint8).reshape(-1, 3).astype(np.int32)
        enteros = b[:, 0] | (b[:, 1] << 8) | (b[:, 2] << 16)
        enteros = np.where(enteros >= (1 << 23), enteros - (1 << 24), enteros)
        data = enteros.astype(np.float32) / 8388608.0
    elif sw == 4:
        data = np.frombuffer(raw, dtype=np.int32).astype(np.float32) / 2147483648.0
    else:
        data = np.frombuffer(raw, dtype=np.uint8).astype(np.float32)
        data = (data - 128) / 128.0
    if ch > 1:
        data = data.reshape(-1, ch).mean(axis=1)
    return data, sr


def _matriz_basis(frame_len, sr, midi_min=40, midi_max=91, cents=0.0):
    """52 frecuencias (MIDI 40=E2 a 91=G6, rango práctico de guitarra). cents > 0 corre todas
    las frecuencias hacia arriba (para temas grabados más agudos que 440 Hz)."""
    midis = np.arange(midi_min, midi_max + 1)
    freqs = 440.0 * 2.0 ** ((midis - 69) / 12.0 + cents / 1200.0)
    pitch_class = midis % 12
    t = np.arange(frame_len) / sr
    base = np.exp(-2j * np.pi * np.outer(freqs, t))  # (K, frame_len)
    return base, pitch_class


def _mags_de_audio(data, sr, frame_len=8192, hop=4096, cents=0.0):
    """Magnitud por marco de las 52 notas MIDI 40-91 (antes de sumarlas por clase de altura)."""
    if len(data) < frame_len:
        data = np.pad(data, (0, frame_len - len(data)))
    marcos = sliding_window_view(data, frame_len)[::hop].copy()
    marcos *= np.hanning(frame_len)
    base, pitch_class = _matriz_basis(frame_len, sr, cents=cents)
    return np.abs(marcos @ base.T), pitch_class  # (n_frames, K)


def _mags_a_chroma(mags, pitch_class):
    chromas = np.zeros((mags.shape[0], 12))
    for pc in range(12):
        chromas[:, pc] = mags[:, pitch_class == pc].sum(axis=1)
    return chromas


def _chroma_de_audio(data, sr, frame_len=8192, hop=4096, cents=0.0):
    mags, pitch_class = _mags_de_audio(data, sr, frame_len, hop, cents)
    chromas = _mags_a_chroma(mags, pitch_class)
    energia = chromas.sum(axis=1)
    tiempos = np.arange(mags.shape[0]) * hop / sr
    return chromas, energia, tiempos


# El 3er armónico de cada nota suena una octava + quinta arriba (19 semitonos). En el chroma
# eso suma energía a la quinta de la fundamental, y el detector confundía el acorde con el de
# su quinta (D leído como A, E como B...). Se le resta a cada nota una fracción de la energía de
# la nota 19 semitonos abajo. Medido en 30 temas contra Chordify: tríada 80,6% -> 81,7%, sube en
# 12 temas y baja en 3 (lab_acordes.py --menor). Con 0 se desactiva.
SUPRESION_3ER_ARMONICO = 0.3


def _suprimir_3er_armonico(mags, fraccion):
    if not fraccion:
        return mags
    out = mags.copy()
    out[:, 19:] -= fraccion * mags[:, :-19]
    return np.maximum(out, 0.0)


# Afinación del tema. Algunas grabaciones están más agudas o más graves que 440 Hz; con media
# nota de diferencia el chroma se reparte entre dos semitonos y el detector falla por completo
# (Highway to Hell, a ~+49 cents, pasaba de 64% a 19% de coincidencia con Chordify). Se estima
# midiendo cuánto se desvían de la grilla de semitonos los picos espectrales de guitarra, piano
# y resto, y solo se corrige cuando el desvío es grande: hasta ~20 cents el detector funciona
# igual (la mayoría de los temas caen a +-5).
AFINACION_MIN_CENTS = 25.0
AFINACION_MIN_CONFIANZA = 0.25


def _estimar_afinacion(wav_paths, N=16384, paso_s=0.5, f_min=200.0, f_max=1500.0, rel=0.10,
                       max_marcos=600):
    """(cents, confianza). cents > 0: más agudo que 440 Hz. Confianza en [0, 1]: longitud del
    vector promedio (1 = todos los picos con la misma desviación)."""
    s_sin = s_cos = tot = 0.0
    hann = np.hanning(N)
    for wav in wav_paths:
        try:
            if not Path(wav).exists():
                continue
            data, sr = _cargar_wav_mono(wav)
        except Exception:  # noqa: BLE001
            continue
        if len(data) < N + 1:
            continue
        inicios = np.arange(0, len(data) - N, max(1, int(paso_s * sr)))
        if len(inicios) > max_marcos:
            inicios = inicios[np.linspace(0, len(inicios) - 1, max_marcos).astype(int)]
        hz = sr / N
        lo, hi = int(f_min / hz), int(f_max / hz)
        for i in range(0, len(inicios), 64):
            marcos = np.stack([data[j:j + N] for j in inicios[i:i + 64]]) * hann
            mag = np.abs(np.fft.rfft(marcos, axis=1))
            centro = mag[:, lo:hi + 1]
            es_pico = ((centro > mag[:, lo - 1:hi]) & (centro >= mag[:, lo + 1:hi + 2])
                       & (centro > rel * centro.max(axis=1, keepdims=True)))
            fr, bn = np.nonzero(es_pico)
            k = bn + lo
            a = np.log(mag[fr, k - 1] + 1e-12)
            b = np.log(mag[fr, k] + 1e-12)
            c = np.log(mag[fr, k + 1] + 1e-12)
            den = a - 2 * b + c
            with np.errstate(divide="ignore", invalid="ignore"):
                delta = np.where(np.abs(den) > 1e-12, 0.5 * (a - c) / den, 0.0)
            f = (k + np.clip(delta, -0.5, 0.5)) * hz
            midi = 69 + 12 * np.log2(f / 440.0)
            ang = 2 * np.pi * (midi - np.round(midi))
            w = mag[fr, k]
            s_sin += float((w * np.sin(ang)).sum())
            s_cos += float((w * np.cos(ang)).sum())
            tot += float(w.sum())
    if tot <= 0:
        return 0.0, 0.0
    return float(np.arctan2(s_sin, s_cos) / (2 * np.pi) * 100.0), float(np.hypot(s_sin, s_cos) / tot)


def _vocabulario_completo():
    """Todos los acordes que se pueden escribir a mano o que puede traer un MIDI
    importado: los del detector automático más los sufijos extra (maj7, sus4).
    Se usa para validar en el editor, no para el detector de audio en sí."""
    return sorted(NOTE_NAMES[r] + suf for r in range(12) for suf in SUFIJOS_VALIDOS)


def _plantillas_acordes():
    plantillas = {}
    for raiz in range(12):
        for sufijo, intervalos in TRIADAS.items():
            v = np.zeros(12)
            for iv in intervalos:
                v[(raiz + iv) % 12] = 1.0
            v /= np.linalg.norm(v)
            plantillas[NOTE_NAMES[raiz] + sufijo] = v
    return plantillas


def _raiz_de_nombre(nombre: str) -> int:
    """Clase de altura de la fundamental de un nombre de acorde del vocabulario."""
    raiz = nombre[:2] if nombre[:2] in NOTE_NAMES else nombre[:1]
    return NOTE_NAMES.index(raiz)


# Cuánto pesa la fundamental que toca el bajo frente al parecido del chroma.
# La similitud coseno se mueve más o menos entre 0.5 y 0.95, así que 0.30
# alcanza para desempatar relativos (Am/C, Em/G) sin llegar a imponer el bajo
# por encima de la armonía cuando el bajista toca una nota de paso.
PESO_BAJO = 0.30


def _chroma_del_bajo(path, frame_len, hop, n_frames, cents=0.0):
    """Chroma del stem de bajo, restringido a MIDI 40-67 (E2 a G4).

    No se usa el registro más grave aunque sea ahí donde está el fundamental:
    con marcos de 8192 muestras el ancho de banda ronda los 10 Hz, y abajo de
    E2 los semitonos están a menos de 5 Hz, así que no se resuelven. Desde E2
    para arriba (fundamental de la mayoría de las líneas de bajo, más el 2º
    armónico de las más graves, que es la misma clase de altura) la resolución
    alcanza de sobra para lo único que necesitamos: distinguir terceras
    menores, que es la distancia exacta de la confusión relativa mayor/menor.

    Devuelve una matriz normalizada por marco, con los marcos donde el bajo
    prácticamente no suena puestos en cero (para no amplificar ruido)."""
    data, sr = _cargar_wav_mono(path)
    if len(data) < frame_len:
        data = np.pad(data, (0, frame_len - len(data)))
    marcos = sliding_window_view(data, frame_len)[::hop].copy()
    marcos *= np.hanning(frame_len)
    base, pitch_class = _matriz_basis(frame_len, sr, midi_min=40, midi_max=67, cents=cents)
    mags = np.abs(marcos @ base.T)
    chroma = np.zeros((marcos.shape[0], 12))
    for pc in range(12):
        chroma[:, pc] = mags[:, pitch_class == pc].sum(axis=1)

    energia = chroma.sum(axis=1)
    pico = chroma.max(axis=1, keepdims=True)
    pico[pico < 1e-9] = 1.0
    chroma = chroma / pico
    if energia.max() > 0:
        chroma[energia < energia.max() * 0.05] = 0.0

    # los dos stems salen del mismo audio, así que deberían tener el mismo
    # largo; se recorta por las dudas para poder sumarlos marco a marco
    if chroma.shape[0] >= n_frames:
        return chroma[:n_frames]
    faltan = n_frames - chroma.shape[0]
    return np.vstack([chroma, np.zeros((faltan, 12))])


def _viterbi(sim, penalizacion):
    """Camino de acordes de máximo puntaje total con una penalización fija por cada
    cambio. Reemplaza al argmax marco a marco + moda de 5 marcos: en vez de decidir
    cada marco por separado, decide la secuencia entera, así un acorde que suena
    durante varios compases no se rompe por unos marcos dudosos."""
    T, K = sim.shape
    ptr = np.zeros((T, K), dtype=np.int32)
    ar = np.arange(K)
    score = sim[0].copy()
    for t in range(1, T):
        j = int(score.argmax())
        salto = score[j] - penalizacion
        quedarse = score >= salto
        ptr[t] = np.where(quedarse, ar, j)
        score = np.where(quedarse, score, salto) + sim[t]
    camino = np.empty(T, dtype=np.int32)
    k = int(score.argmax())
    for t in range(T - 1, -1, -1):
        camino[t] = k
        k = ptr[t, k]
    return camino


def _clasificar_frames(chromas, plantillas, chroma_bajo=None, peso_bajo=PESO_BAJO, penalizacion_cambio=0.0,
                       penalizacion_septima=0.0):
    nombres = list(plantillas.keys())
    M = np.stack([plantillas[n] for n in nombres])
    normas = np.linalg.norm(chromas, axis=1, keepdims=True)
    normas[normas < 1e-9] = 1.0
    similitud = (chromas / normas) @ M.T

    # Sesgo por la nota del bajo. Sin esto, el chroma con plantillas confunde
    # sistemáticamente los relativos: Am y C comparten dos de tres notas, y lo
    # único que los separa de verdad es cuál de las dos es la fundamental. Eso
    # el stem de bajo lo dice sin ambigüedad.
    if chroma_bajo is not None and peso_bajo:
        raices = np.array([_raiz_de_nombre(n) for n in nombres])
        similitud = similitud + peso_bajo * chroma_bajo[:, raices]

    # Las séptimas se elegían de más (Em -> E7, A -> A7): el séptimo armónico de cualquier nota
    # suma energía justo donde la plantilla de séptima la espera. Se les resta un puntaje fijo,
    # así que una séptima de verdad tiene que ganar por más margen.
    if penalizacion_septima:
        similitud = similitud - penalizacion_septima * np.array([1.0 if n.endswith("7") else 0.0 for n in nombres])

    idx = _viterbi(similitud, penalizacion_cambio) if penalizacion_cambio else np.argmax(similitud, axis=1)
    return [nombres[i] for i in idx]


# Ajustes elegidos midiendo contra los MIDI de Chordify de 28 temas (lab_acordes.py):
# sumar piano y resto al chroma de la guitarra, decidir la secuencia con Viterbi en vez de
# moda de 5 marcos, y un umbral de silencio más bajo. Con penalizacion_cambio=0 se recupera
# el comportamiento de app95 (moda de 5 marcos; con penalizacion_septima=0, umbral_rel=0.06 y
# corregir_afinacion=False, supresion_armonico=0; y en el pulso, TEMPO_PRIOR_OCTAVAS = 0 y
# PERIODO_FINO = False).
PENALIZACION_CAMBIO = 1.0
UMBRAL_SILENCIO = 0.02
PENALIZACION_SEPTIMA = 0.15

# v98 -- tiempo de cada marco. Un marco de 8192 muestras cubre ~186 ms y hasta app97 se le
# asignaba el tiempo de su PRIMERA muestra, así que todos los cambios de acorde salían ~93 ms
# antes de lo que suenan. La grilla lo disimulaba de casualidad: al muestrear el acorde justo
# en el instante del tiempo, el adelanto hacía que el acorde nuevo ya estuviera. Con el
# tiempo corregido ese muestreo puntual queda a cara o cruz en cada cambio (medido en audio
# sintético: grilla 93% -> 76%), por eso va junto con GRILLA_POR_MAYORIA. Con False +
# GRILLA_POR_MAYORIA = False se recupera exactamente app97.
TIEMPOS_CENTRADOS = True

# v98 -- cada tiempo de la grilla toma el acorde que más dura DENTRO de ese tiempo, en vez
# del que suena en el instante exacto del golpe. Un error de detección de pocos ms justo
# sobre el tiempo ya no se lleva el tiempo entero.
GRILLA_POR_MAYORIA = True

# v98 -- compresión logarítmica de las 52 notas antes de armar el chroma: log(1 + g*x), con
# x normalizado a la canción. En lineal, la cuerda grave y la fundamental duplicada pesan
# tanto que la plantilla de tríada "ve" casi una sola nota. Es la mejora más documentada para
# detección por plantillas (chroma CLP, Müller), pero cambia la escala de las similitudes y
# PENALIZACION_CAMBIO / PESO_BAJO / PENALIZACION_SEPTIMA se eligieron en lineal: queda APAGADA
# (0) hasta medirla en lab_acordes.py. Valores a probar: 10 y 100.
COMPRESION_LOG = 0.0


def _comprimir_log(mags, gamma):
    """log(1 + gamma * mags / ref), con ref = percentil 99,5 de la canción: así el resultado no
    depende del volumen de la grabación. Con gamma = 0 devuelve mags sin tocar."""
    if not gamma or mags.size == 0:
        return mags
    ref = float(np.percentile(mags, 99.5))
    if ref <= 0:
        return mags
    return np.log1p(gamma * mags / ref)


def detectar_acordes(wav_path, frame_len=8192, hop=4096, umbral_rel=UMBRAL_SILENCIO, min_duracion=0.35,
                     bajo_path=None, stems_extra=None, penalizacion_cambio=PENALIZACION_CAMBIO,
                     penalizacion_septima=PENALIZACION_SEPTIMA, corregir_afinacion=True,
                     supresion_armonico=SUPRESION_3ER_ARMONICO, compresion_log=None,
                     tiempos_centrados=None):
    """Devuelve [{"inicio": s, "fin": s, "acorde": "G"}, ...] a partir de un wav mono/estéreo.

    Si se le pasa el stem de bajo, lo usa para desempatar la fundamental. stems_extra es una
    lista de wavs (piano, resto) cuyo chroma se suma al de wav_path: en temas donde la guitarra
    casi no suena, los acordes están en esos stems."""
    # None = lo que digan las constantes del módulo (así lab_acordes.py puede probar ambos)
    compresion_log = COMPRESION_LOG if compresion_log is None else compresion_log
    tiempos_centrados = TIEMPOS_CENTRADOS if tiempos_centrados is None else tiempos_centrados

    data, sr = _cargar_wav_mono(wav_path)

    cents = 0.0
    if corregir_afinacion:
        est, confianza = _estimar_afinacion([wav_path] + list(stems_extra or []))
        if abs(est) >= AFINACION_MIN_CENTS and confianza >= AFINACION_MIN_CONFIANZA:
            cents = float(np.clip(round(est / 5.0) * 5, -50, 50))

    mags, pitch_class = _mags_de_audio(data, sr, frame_len, hop, cents=cents)

    for extra in stems_extra or []:
        try:
            if not Path(extra).exists():
                continue
            data2, sr2 = _cargar_wav_mono(extra)
            if sr2 != sr:
                continue
            mags2, _ = _mags_de_audio(data2, sr2, frame_len, hop, cents=cents)
            n_comun = min(mags.shape[0], mags2.shape[0])
            mags = mags[:n_comun] + mags2[:n_comun]
        except Exception:  # noqa: BLE001
            continue   # un stem extra es una ayuda, no un requisito
    # cada marco describe lo que suena alrededor de su CENTRO, no de su primera muestra
    centro = frame_len / 2 if tiempos_centrados else 0
    tiempos = (np.arange(mags.shape[0]) * hop + centro) / sr
    # la energía (para decidir silencios) se mide sin la supresión, que solo afecta qué acorde es
    energia = _mags_a_chroma(mags, pitch_class).sum(axis=1)
    chromas = _mags_a_chroma(
        _comprimir_log(_suprimir_3er_armonico(mags, supresion_armonico), compresion_log), pitch_class)

    chroma_bajo = None
    if bajo_path is not None and Path(bajo_path).exists():
        try:
            chroma_bajo = _chroma_del_bajo(bajo_path, frame_len, hop, chromas.shape[0], cents=cents)
        except Exception:  # noqa: BLE001
            chroma_bajo = None   # el bajo es una ayuda, no un requisito

    etiquetas = _clasificar_frames(chromas, _plantillas_acordes(), chroma_bajo,
                                   penalizacion_cambio=penalizacion_cambio,
                                   penalizacion_septima=penalizacion_septima)

    umbral = energia.max() * umbral_rel if energia.max() > 0 else 0
    etiquetas = ["—" if e < umbral else et for et, e in zip(etiquetas, energia)]

    # moda en ventana deslizante: evita que titile entre acordes en cada golpe de púa.
    # Con Viterbi ya viene suavizado, así que solo se usa en el modo anterior.
    n = len(etiquetas)
    suaves = list(etiquetas)
    if not penalizacion_cambio:
        for i in range(n):
            ini, fin = max(0, i - 2), min(n, i + 3)
            ventana = etiquetas[ini:fin]
            suaves[i] = max(set(ventana), key=ventana.count)

    hop_seg = hop / sr
    segmentos = []
    actual, inicio = suaves[0], 0.0
    for i in range(1, n):
        if suaves[i] != actual:
            segmentos.append({"inicio": round(float(inicio), 2), "fin": round(float(tiempos[i]), 2), "acorde": actual})
            actual, inicio = suaves[i], tiempos[i]
    segmentos.append({"inicio": round(float(inicio), 2), "fin": round(float(tiempos[-1]) + hop_seg, 2), "acorde": actual})

    # fusionar tramos cortos (ruido) con el anterior
    fusionado = [segmentos[0]]
    for seg in segmentos[1:]:
        if seg["fin"] - seg["inicio"] < min_duracion:
            fusionado[-1]["fin"] = seg["fin"]
        elif fusionado[-1]["acorde"] == seg["acorde"]:
            fusionado[-1]["fin"] = seg["fin"]
        else:
            fusionado.append(seg)
    return fusionado


# ------------------------------------------- v109: detector de acordes aprendido ----
# Red chica entrenada con los MIDI de Chordify de la biblioteca. Medido con validación
# cruzada por tema en 38 temas: tríada 86,0% -> 88,9-89,1% según la semilla, mejoran
# 22-23 temas y empeoran 2-5. Es opcional de punta a punta: si no hay
# modelo_acordes.npz, o si el modelo falla, se usa el detector por plantillas de
# siempre. Se elige en Ajustes generales ("detector_aprendido", encendido por defecto).
# v110: todo adentro de Mesa (antes acordes_ml.py + ml_dataset.py + ml_entrenar.py
# aparte) y se entrena con un botón en Ajustes generales (ver _entrenar_detector).
# Clases: 12 raíces x {mayor, menor, 7} + N (sin acorde) = 37. Solo numpy.


ML_CALIDADES = ["", "m", "7"]
ML_N_CLASES = 37
ML_CLASE_N = 36
ML_IGNORAR = -1

ML_VERSION_FEATURES = 1
ML_CONTEXTO = 6            # marcos a cada lado que se promedian (6 x 93 ms ~ 0,56 s)
ML_GAMMA_LOG = 100.0       # compresión log(1 + g*x) de las magnitudes
ML_CORTE_REGISTRO = 20     # índice de nota que separa grave (MIDI 40-59) de agudo (60-91)

# bloques de 12 que rotan al transponer, dentro del vector de un marco
# [chroma grave armónico | chroma agudo armónico | chroma bajo | energía]
ML_DIM_MARCO = 37
ML_BLOQUES_MARCO = [(0, 12), (12, 24), (24, 36)]


# ------------------------------------------------------------------ etiquetas ----

def ml_nombre_a_clase(acorde):
    """'C' -> 0, 'Cm' -> 1, 'C7' -> 2, ..., '—'/None -> N. maj7 cuenta como mayor;
    sus4 se ignora en el entrenamiento (no es ni mayor ni menor)."""
    if not acorde or acorde in ("—", "."):
        return ML_CLASE_N
    raiz = acorde[:2] if acorde[:2] in NOTE_NAMES else acorde[:1]
    if raiz not in NOTE_NAMES:
        return ML_IGNORAR
    suf = acorde[len(raiz):]
    q = {"": 0, "maj7": 0, "m": 1, "7": 2}.get(suf)
    if q is None:
        return ML_IGNORAR
    return NOTE_NAMES.index(raiz) * 3 + q


def ml_clase_a_nombre(c):
    if c == ML_CLASE_N:
        return "—"
    return NOTE_NAMES[c // 3] + ML_CALIDADES[c % 3]


def ml_etiquetas_en_tiempos(segmentos, tiempos):
    """Clase de referencia en cada instante (N donde no hay acorde). Vectorizado (v111)."""
    tiempos = np.asarray(tiempos, dtype=float)
    y = np.full(len(tiempos), ML_CLASE_N, dtype=np.int16)
    if not segmentos or not len(tiempos):
        return y
    orden = sorted(segmentos, key=lambda s: s["inicio"])
    inicios = np.array([float(s["inicio"]) for s in orden])
    fines = np.array([float(s["fin"]) for s in orden])
    clases = np.array([ml_nombre_a_clase(s["acorde"]) for s in orden], dtype=np.int16)
    idx = np.searchsorted(inicios, tiempos, side="right") - 1
    idx_c = np.clip(idx, 0, None)
    ok = (idx >= 0) & (tiempos < fines[idx_c])
    y[ok] = clases[idx_c[ok]]
    return y


# ------------------------------------------------------------------- features ----

def ml_features_marco(mags_armonicos, pitch_class, chroma_bajo, energia):
    """Vector de 37 por marco.

    mags_armonicos: (T, 52) magnitudes de guitarra+piano+resto, ya con la supresión
                    del 3er armónico (igual que el detector de Mesa).
    chroma_bajo:    (T, 12) chroma del stem de bajo normalizado (o None).
    energia:        (T,) energía sin supresión (la misma que usa Mesa para silencios)."""
    T = mags_armonicos.shape[0]
    ref = float(np.percentile(mags_armonicos, 99.5)) if mags_armonicos.size else 1.0
    m = np.log1p(ML_GAMMA_LOG * mags_armonicos / (ref if ref > 0 else 1.0))

    lo = np.zeros((T, 12))
    hi = np.zeros((T, 12))
    for pc in range(12):
        sel = pitch_class == pc
        idx = np.nonzero(sel)[0]
        lo[:, pc] = m[:, idx[idx < ML_CORTE_REGISTRO]].sum(axis=1)
        hi[:, pc] = m[:, idx[idx >= ML_CORTE_REGISTRO]].sum(axis=1)
    pico = np.maximum(lo.max(axis=1), hi.max(axis=1))[:, None]
    pico[pico < 1e-9] = 1.0
    lo, hi = lo / pico, hi / pico

    if chroma_bajo is None:
        chroma_bajo = np.zeros((T, 12))
    e = np.asarray(energia, dtype=float)
    emax = e.max() if e.size and e.max() > 0 else 1.0
    loud = np.log10(e / emax + 1e-4)[:, None] / 4.0 + 1.0   # ~[0, 1]
    return np.hstack([lo, hi, chroma_bajo[:T], loud]).astype(np.float32)


def ml_con_contexto(F, escalas=(ML_CONTEXTO,)):
    """[marco, y por cada escala k: promedio de los k anteriores, promedio de los k
    siguientes]. v111: varias escalas a la vez (ej. 4 y 16 marcos ~ 0,4 s y 1,5 s): la
    corta ve el cambio de acorde, la larga el acorde que viene sonando."""
    if isinstance(escalas, int):
        escalas = (escalas,)
    T, D = F.shape
    c = np.vstack([np.zeros((1, D), np.float64), np.cumsum(F, axis=0, dtype=np.float64)])
    i = np.arange(T)
    partes = [F]
    for k in escalas:
        a0, a1 = np.maximum(0, i - k), i
        p0, p1 = i + 1, np.minimum(T, i + 1 + k)
        na = np.maximum(1, a1 - a0)[:, None]
        np_ = np.maximum(1, p1 - p0)[:, None]
        partes += [(c[a1] - c[a0]) / na, (c[p1] - c[p0]) / np_]
    return np.hstack(partes).astype(np.float32)


def ml_bloques_contexto(dim=3 * ML_DIM_MARCO):
    """Bloques de 12 a rotar en el vector con contexto (una copia del marco por cada
    promedio; la cantidad de copias sale del ancho del vector)."""
    out = []
    for copia in range(dim // ML_DIM_MARCO):
        base = copia * ML_DIM_MARCO
        out += [(base + a, base + b) for a, b in ML_BLOQUES_MARCO]
    return out


def ml_transponer(X, y, r):
    """Sube r semitonos features y etiquetas (r puede ser un array, uno por fila)."""
    X = X.copy()
    r = np.broadcast_to(np.asarray(r) % 12, (X.shape[0],))
    filas = np.arange(X.shape[0])[:, None]
    cols = (np.arange(12)[None, :] - r[:, None]) % 12
    for a, b in ml_bloques_contexto(X.shape[1]):
        bloque = X[:, a:b]
        X[:, a:b] = bloque[filas, cols]
    y2 = y.copy()
    ok = (y2 >= 0) & (y2 < ML_CLASE_N)
    y2[ok] = ((y2[ok] // 3 + r[ok]) % 12) * 3 + y2[ok] % 3
    return X, y2


# ---------------------------------------------------------------------- modelo ----

class MLModelo:
    """Red de una capa oculta (oculta=0 -> regresión logística), en numpy."""

    def __init__(self, dim, oculta=96, semilla=0):
        rng = np.random.default_rng(semilla)
        self.oculta = oculta
        if oculta:
            self.W1 = (rng.standard_normal((dim, oculta)) * np.sqrt(2.0 / dim)).astype(np.float32)
            self.b1 = np.zeros(oculta, np.float32)
            self.W2 = (rng.standard_normal((oculta, ML_N_CLASES)) * np.sqrt(1.0 / oculta)).astype(np.float32)
        else:
            self.W1 = self.b1 = None
            self.W2 = (rng.standard_normal((dim, ML_N_CLASES)) * 0.01).astype(np.float32)
        self.b2 = np.zeros(ML_N_CLASES, np.float32)
        self.media = np.zeros(dim, np.float32)
        self.escala = np.ones(dim, np.float32)

    def params(self):
        return [p for p in (self.W1, self.b1, self.W2, self.b2) if p is not None]

    def _forward(self, X):
        Xn = (X - self.media) / self.escala
        if self.oculta:
            h = np.maximum(0, Xn @ self.W1 + self.b1)
            z = h @ self.W2 + self.b2
        else:
            h = None
            z = Xn @ self.W2 + self.b2
        z = z - z.max(axis=1, keepdims=True)
        logp = z - np.log(np.exp(z).sum(axis=1, keepdims=True))
        return Xn, h, logp

    def log_probs(self, X, lote=8192):
        return np.vstack([self._forward(X[i:i + lote])[2] for i in range(0, len(X), lote)])

    def ajustar_normalizacion(self, X):
        """Media/escala compartidas dentro de cada bloque de 12 (así la normalización
        no rompe la invariancia por transposición)."""
        self.media = X.mean(axis=0).astype(np.float32)
        self.escala = X.std(axis=0).astype(np.float32)
        for a, b in ml_bloques_contexto(X.shape[1]):
            self.media[a:b] = X[:, a:b].mean()
            self.escala[a:b] = X[:, a:b].std()
        self.escala[self.escala < 1e-6] = 1.0

    def entrenar(self, X, y, epocas=15, lote=512, lr=1e-3, l2=1e-4, semilla=0, log=None):
        rng = np.random.default_rng(semilla)
        ok = y >= 0
        X, y = X[ok], y[ok]
        self.ajustar_normalizacion(X)
        params = self.params()
        m = [np.zeros_like(p) for p in params]
        v = [np.zeros_like(p) for p in params]
        b1_, b2_, eps, paso = 0.9, 0.999, 1e-8, 0
        n = len(X)
        for ep in range(epocas):
            orden = rng.permutation(n)
            perdida = 0.0
            for i in range(0, n, lote):
                sel = orden[i:i + lote]
                # aumento de datos: cada fila con una transposición al azar
                Xb, yb = ml_transponer(X[sel], y[sel], rng.integers(0, 12, len(sel)))
                Xn, h, logp = self._forward(Xb)
                B = len(sel)
                perdida += -logp[np.arange(B), yb].sum()
                g = np.exp(logp)
                g[np.arange(B), yb] -= 1.0
                g /= B
                if self.oculta:
                    gW2 = h.T @ g + l2 * self.W2
                    gb2 = g.sum(axis=0)
                    gh = (g @ self.W2.T) * (h > 0)
                    gW1 = Xn.T @ gh + l2 * self.W1
                    gb1 = gh.sum(axis=0)
                    grads = [gW1, gb1, gW2, gb2]
                else:
                    grads = [Xn.T @ g + l2 * self.W2, g.sum(axis=0)]
                paso += 1
                for p, gr, mm, vv in zip(params, grads, m, v):
                    mm *= b1_
                    mm += (1 - b1_) * gr
                    vv *= b2_
                    vv += (1 - b2_) * gr * gr
                    p -= (lr * (mm / (1 - b1_ ** paso)) / (np.sqrt(vv / (1 - b2_ ** paso)) + eps)).astype(p.dtype)
            if log:
                log(f"    época {ep + 1}/{epocas}  pérdida {perdida / n:.3f}")

    def guardar(self, ruta, extra=None):
        datos = {"b2": self.b2, "W2": self.W2, "media": self.media, "escala": self.escala,
                 "meta": np.array(json.dumps({"oculta": self.oculta, "version_features": ML_VERSION_FEATURES,
                                              "contexto": ML_CONTEXTO, **(extra or {})}))}
        if self.oculta:
            datos.update(W1=self.W1, b1=self.b1)
        np.savez(ruta, **datos)

    @classmethod
    def cargar(cls, ruta):
        # con "with": el archivo se cierra enseguida. Abierto, Windows no dejaría
        # reemplazarlo al reentrenar.
        with np.load(ruta) as d:
            meta = json.loads(str(d["meta"]))
            dim = d["media"].shape[0]
            m = cls(dim, oculta=meta["oculta"])
            m.W2, m.b2, m.media, m.escala = d["W2"], d["b2"], d["media"], d["escala"]
            if meta["oculta"]:
                m.W1, m.b1 = d["W1"], d["b1"]
        m.meta = meta
        return m


# ------------------------------------------------------------------ decodificar ----



def ml_segmentos_desde_logp(logp, tiempos, energia, hop_seg, penalizacion=6.0,
                         umbral_rel=0.02, min_duracion=0.35):
    """Mismo armado de segmentos que detectar_acordes de Mesa (silencio por energía,
    fusión de tramos cortos), con la secuencia decidida por Viterbi sobre log-probs."""
    idx = _viterbi(logp, penalizacion) if penalizacion else logp.argmax(axis=1)
    etiquetas = [ml_clase_a_nombre(int(c)) for c in idx]
    emax = float(np.max(energia)) if len(energia) else 0.0
    umbral = emax * umbral_rel if emax > 0 else 0.0
    etiquetas = ["—" if e < umbral else et for et, e in zip(etiquetas, energia)]

    n = len(etiquetas)
    segmentos = []
    actual, inicio = etiquetas[0], 0.0
    for i in range(1, n):
        if etiquetas[i] != actual:
            segmentos.append({"inicio": round(float(inicio), 2), "fin": round(float(tiempos[i]), 2), "acorde": actual})
            actual, inicio = etiquetas[i], tiempos[i]
    segmentos.append({"inicio": round(float(inicio), 2), "fin": round(float(tiempos[-1]) + hop_seg, 2),
                      "acorde": actual})
    fusionado = [segmentos[0]]
    for seg in segmentos[1:]:
        if seg["fin"] - seg["inicio"] < min_duracion:
            fusionado[-1]["fin"] = seg["fin"]
        elif fusionado[-1]["acorde"] == seg["acorde"]:
            fusionado[-1]["fin"] = seg["fin"]
        else:
            fusionado.append(seg)
    return fusionado


MODELO_ACORDES_PATH = BASE_DIR / "modelo_acordes.npz"
_modelo_acordes_cache = {"mtime": None, "modelo": None}
_modelo_acordes_lock = threading.Lock()


def _escalas_modelo(meta):
    """Escalas de contexto con que se entrenó (v110 guardaba un solo 'contexto')."""
    esc = meta.get("escalas")
    if esc:
        return tuple(int(k) for k in esc)
    return (int(meta.get("contexto", ML_CONTEXTO)),)


def modelo_acordes():
    """El modelo entrenado, o None. Se recarga solo si el archivo cambió (después
    de reentrenar no hace falta reiniciar Mesa)."""
    if not MODELO_ACORDES_PATH.exists():
        return None
    with _modelo_acordes_lock:
        try:
            mtime = MODELO_ACORDES_PATH.stat().st_mtime
            if _modelo_acordes_cache["mtime"] != mtime:
                m = MLModelo.cargar(MODELO_ACORDES_PATH)
                meta = getattr(m, "meta", {})
                if (meta.get("version_features") != ML_VERSION_FEATURES
                        or len(_escalas_modelo(meta)) * 2 * ML_DIM_MARCO + ML_DIM_MARCO != m.media.shape[0]):
                    m = None   # entrenado con otras features: no sirve
                _modelo_acordes_cache.update(mtime=mtime, modelo=m)
            return _modelo_acordes_cache["modelo"]
        except Exception:  # noqa: BLE001
            _modelo_acordes_cache.update(mtime=None, modelo=None)
            return None


def info_modelo_acordes():
    m = modelo_acordes()
    if m is None:
        return None
    meta = getattr(m, "meta", {})
    return {"temas": meta.get("temas"), "fecha": meta.get("fecha"),
            "temas_entrenamiento": meta.get("temas_entrenamiento") or []}


def detector_aprendido_activo():
    return bool(leer_prefs().get("detector_aprendido", True)) and modelo_acordes() is not None


def _features_ml(wav_path, bajo_path=None, stems_extra=None, frame_len=8192, hop=4096):
    """Features del modelo: mismos pasos que el comienzo de detectar_acordes (afinación,
    suma de stems, supresión del 3er armónico, chroma del bajo). Es la
    misma función que usa el entrenamiento, así los dos ven exactamente lo mismo.
    Devuelve (F, energia, tiempos, hop_seg)."""
    data, sr = _cargar_wav_mono(wav_path)
    extras = [Path(x) for x in (stems_extra or [])]

    cents = 0.0
    est, conf = _estimar_afinacion([wav_path] + extras)
    if abs(est) >= AFINACION_MIN_CENTS and conf >= AFINACION_MIN_CONFIANZA:
        cents = float(np.clip(round(est / 5.0) * 5, -50, 50))

    mags, pitch_class = _mags_de_audio(data, sr, frame_len, hop, cents=cents)
    for extra in extras:
        try:
            if not extra.exists():
                continue
            d2, sr2 = _cargar_wav_mono(extra)
            if sr2 != sr:
                continue
            m2, _ = _mags_de_audio(d2, sr2, frame_len, hop, cents=cents)
            n = min(mags.shape[0], m2.shape[0])
            mags = mags[:n] + m2[:n]
        except Exception:  # noqa: BLE001
            continue

    energia = _mags_a_chroma(mags, pitch_class).sum(axis=1)
    mags_sup = _suprimir_3er_armonico(mags, SUPRESION_3ER_ARMONICO)

    chroma_bajo = None
    if bajo_path is not None and Path(bajo_path).exists():
        try:
            chroma_bajo = _chroma_del_bajo(bajo_path, frame_len, hop, mags.shape[0], cents=cents)
        except Exception:  # noqa: BLE001
            chroma_bajo = None

    F = ml_features_marco(mags_sup, pitch_class, chroma_bajo, energia)
    tiempos = (np.arange(mags.shape[0]) * hop + frame_len / 2) / sr
    return F, energia, tiempos, hop / sr


def detectar_acordes_ml(wav_path, modelo, bajo_path=None, stems_extra=None, min_duracion=0.35):
    """Misma salida que detectar_acordes, decidida por el modelo entrenado."""
    F, energia, tiempos, hop_seg = _features_ml(wav_path, bajo_path, stems_extra)
    meta = getattr(modelo, "meta", {}) or {}
    logp = modelo.log_probs(ml_con_contexto(F, _escalas_modelo(meta)))
    pen = float(meta.get("penalizacion", 9.0))
    # v111: el umbral de silencio también lo elige el entrenamiento (con 0 decide solo
    # el modelo, que tiene su propia clase "sin acorde"). Modelos viejos: el de siempre.
    umbral = float(meta.get("umbral_silencio", UMBRAL_SILENCIO))
    return ml_segmentos_desde_logp(logp, tiempos, energia, hop_seg, penalizacion=pen,
                                   umbral_rel=umbral, min_duracion=min_duracion)


def detectar_acordes_cancion(carpeta):
    """Detector que corresponda según Ajustes generales. Devuelve (segmentos, "aprendido" |
    "plantillas"). Si el modelo falla por cualquier motivo, cae al de plantillas."""
    guitarra = carpeta / "guitar.wav"
    bajo = carpeta / "bass.wav"
    extras = [carpeta / "piano.wav", carpeta / "other.wav"]
    if detector_aprendido_activo():
        try:
            return detectar_acordes_ml(guitarra, modelo_acordes(), bajo_path=bajo, stems_extra=extras), "aprendido"
        except Exception as exc:  # noqa: BLE001
            print(f"[mesa] detector aprendido falló ({exc}); se usa el de plantillas")
    return detectar_acordes(guitarra, bajo_path=bajo, stems_extra=extras), "plantillas"


# ------------------------------- v110: entrenar el detector desde Mesa (un botón) ----
# Corre en un hilo en la PC. Paso 1: por cada tema con MIDI importado, guarda en
# ml_cache/ las features, la etiqueta de cada marco y cómo le va al detector de
# plantillas (si ya estaba y no cambió nada, se reutiliza: es la misma carpeta que
# usaban los scripts de prueba). Paso 2: validación cruzada por tema (5 grupos: cada
# tema se mide con un modelo que no lo vio). Paso 3: modelo final con todos. El nuevo
# reemplaza al anterior SOLO si en la validación le gana al de plantillas.
ML_CACHE_DIR = BASE_DIR / "ml_cache"
ML_RESULTADO_PATH = ML_CACHE_DIR / "_ultimo_entrenamiento.json"
ML_PENALIZACIONES = [2.0, 4.0, 6.0, 9.0, 13.0]
ML_GRUPOS = 5
ML_EPOCAS = 20
ML_OCULTA = 96
ML_MIN_TEMAS = 5

_entreno = {"corriendo": False, "etapa": "", "i": 0, "n": 0, "error": None}
_entreno_lock = threading.Lock()


def _entreno_set(**kw):
    with _entreno_lock:
        _entreno.update(kw)


def _referencia_midi(carpeta):
    """Acordes del MIDI importado, con la sincronía aplicada (misma lógica que
    /comparar_detector). Devuelve (segmentos, fuente, firma) o (None, None, None)."""
    grid_path = carpeta / "acordes_grid.json"
    try:
        grid = json.loads(grid_path.read_text(encoding="utf-8")) if grid_path.exists() else {}
    except (json.JSONDecodeError, OSError):
        grid = {}
    es_midi = grid.get("origen") == "midi"
    ref, fuente, base_firma = None, None, None
    midi_path = carpeta / "acordes_midi.json"
    txt_path = carpeta / "acordes.txt"
    if midi_path.exists():
        try:
            ref = json.loads(midi_path.read_text(encoding="utf-8")).get("segmentos")
            fuente, base_firma = "midi", midi_path.stat().st_mtime
        except (json.JSONDecodeError, OSError):
            ref = None
    if not ref and es_midi and txt_path.exists():
        try:
            tokens = _texto_a_tokens(txt_path.read_text(encoding="utf-8"))
            ref = _tokens_a_segmentos(tokens, grid["beat_times"], grid.get("duracion", 0))
            fuente, base_firma = "grilla", txt_path.stat().st_mtime
        except Exception:  # noqa: BLE001
            ref = None
    if not ref:
        return None, None, None
    try:
        corr = float(grid.get("offset", 0.0)) if es_midi else 0.0
    except (TypeError, ValueError):
        corr = 0.0
    ref = [{"inicio": float(x["inicio"]) + corr, "fin": float(x["fin"]) + corr, "acorde": x["acorde"]} for x in ref]
    try:
        wav_mtime = (carpeta / "guitar.wav").stat().st_mtime
    except OSError:
        wav_mtime = 0
    firma = f"{fuente}|{base_firma:.0f}|{corr:.3f}|{wav_mtime:.0f}"
    return ref, fuente, firma


def _cache_cancion(carpeta):
    """Prepara (o reutiliza) ml_cache/<tema>.npz. Devuelve True si el tema sirve para entrenar."""
    ref, fuente, firma = _referencia_midi(carpeta)
    if not ref:
        return False
    destino = ML_CACHE_DIR / f"{carpeta.name}.npz"
    if destino.exists():
        try:
            # se lee todo y se cierra ANTES de reescribir: en Windows no se puede
            # reemplazar un archivo que sigue abierto
            with np.load(destino) as d:
                meta = json.loads(str(d["meta"]))
                arrays = {k: d[k] for k in d.files if k != "meta"}
            if meta.get("version_features") == ML_VERSION_FEATURES:
                if meta.get("firma") == firma:
                    return True
                if meta.get("firma") is None:
                    # hecho por los scripts de prueba: mismas features, se adopta tal cual
                    meta["firma"] = firma
                    _guardar_npz(destino, meta=np.array(json.dumps(meta)), **arrays)
                    return True
        except Exception:  # noqa: BLE001
            pass   # roto o viejo: se rehace
    F, energia, tiempos, hop_seg = _features_ml(carpeta / "guitar.wav", carpeta / "bass.wav",
                                                [carpeta / "piano.wav", carpeta / "other.wav"])
    y = ml_etiquetas_en_tiempos(ref, tiempos)
    det = detectar_acordes(carpeta / "guitar.wav", bajo_path=carpeta / "bass.wav",
                           stems_extra=[carpeta / "piano.wav", carpeta / "other.wav"])
    duracion = det[-1]["fin"]
    base = _comparar_acordes(ref, det, duracion)
    if base is None:
        return False
    _guardar_npz(destino, F=F.astype(np.float32), y=y, energia=energia.astype(np.float32), tiempos=tiempos,
                 meta=np.array(json.dumps({"cancion": carpeta.name, "fuente": fuente, "hop_seg": hop_seg,
                                           "duracion": duracion, "referencia": ref, "base": base,
                                           "version_features": ML_VERSION_FEATURES, "firma": firma})))
    return True


def _guardar_npz(destino, **arrays):
    """np.savez_compressed atómico (si se corta a la mitad no queda un archivo roto)."""
    tmp = destino.with_name(destino.stem + ".tmp.npz")
    np.savez_compressed(tmp, **arrays)
    os.replace(tmp, destino)


def _cargar_tema_cache(nombre):
    with np.load(ML_CACHE_DIR / f"{nombre}.npz") as d:
        meta = json.loads(str(d["meta"]))
        F, y, energia, tiempos = d["F"], d["y"], d["energia"], d["tiempos"]
    return {"nombre": nombre, "F": F, "y": y.astype(np.int64),
            "energia": energia, "tiempos": tiempos, "meta": meta}


def _ml_juntar(temas, escalas, paso=2):
    X = np.vstack([ml_con_contexto(t["F"], escalas)[::paso] for t in temas])
    y = np.concatenate([t["y"][::paso] for t in temas])
    return X, y


def _clave_triada(clases):
    """Clase del modelo -> (raíz, mayor/menor) como un entero; N = -1, ignorar = -2.
    C y C7 cuentan igual (como la 'tríada' de la comparación)."""
    c = np.asarray(clases)
    out = np.where(c == ML_CLASE_N, -1, (c // 3) * 2 + (c % 3 == 1))
    return np.where(c < 0, -2, out)


def _puntajes_tiempo(ref, det, duracion, paso=0.05):
    """(tríada %, global %) muestreando cada `paso` s.
    - tríada: como /comparar_detector, solo donde el MIDI tiene acorde.
    - global: TODO el tema, contando también los silencios: acierta si los dos dicen
      "sin acorde" o la misma tríada. Penaliza inventar acordes donde el MIDI no tiene
      ninguno (lo que la tríada sola no ve: bajar el umbral de silencio siempre la sube)."""
    tiempos = np.arange(0.0, max(0.0, duracion), paso)
    r = _clave_triada(ml_etiquetas_en_tiempos(ref, tiempos))
    d = _clave_triada(ml_etiquetas_en_tiempos(det, tiempos))
    validos = r != -2
    con_acorde = validos & (r >= 0)
    tri = 100.0 * float(((r == d) & con_acorde).sum()) / max(1, int(con_acorde.sum()))
    glo = 100.0 * float(((r == d) & validos).sum()) / max(1, int(validos.sum()))
    return tri, glo


# v111: qué se prueba al entrenar. Todo se elige por validación cruzada por tema con la
# métrica GLOBAL (acordes + silencios), así no gana una variante solo por inventar
# acordes donde no hay. Variantes de red: la de v110 y una con contexto en dos escalas y
# más neuronas. Umbral de silencio: el de siempre (2% del pico), uno bajo, y 0 (decide
# solo el modelo). Las combinaciones de umbral y penalización no requieren reentrenar.
ML_VARIANTES = [
    {"nombre": "v110 (contexto 0,6 s)", "escalas": (6,), "oculta": 96},
    {"nombre": "contexto 0,4 + 1,5 s", "escalas": (4, 16), "oculta": 128},
]
ML_UMBRALES = [UMBRAL_SILENCIO, 0.005, 0.0]
# Un tema donde el detector de plantillas coincide menos que esto con su MIDI casi
# siempre tiene el MIDI corrido o de otra versión (lo de Maná): se deja afuera.
ML_MIN_BASE_TRIADA = 40.0


def _entrenar_detector():
    try:
        ML_CACHE_DIR.mkdir(exist_ok=True)
        raiz = OUTPUT_DIR / MODEL
        carpetas = sorted(p for p in raiz.iterdir() if p.is_dir() and (p / "guitar.wav").exists())
        con_midi = [c for c in carpetas if _referencia_midi(c)[0]]
        _entreno_set(etapa="analizando temas", i=0, n=len(con_midi))
        nombres = []
        for i, c in enumerate(con_midi):
            _entreno_set(i=i, detalle=c.name)
            try:
                if _cache_cancion(c):
                    nombres.append(c.name)
            except Exception as exc:  # noqa: BLE001
                print(f"[mesa] entrenamiento: se saltea {c.name} ({exc})")

        temas, excluidos = [], []
        for n in nombres:
            t = _cargar_tema_cache(n)
            if t["meta"]["base"]["triada"] < ML_MIN_BASE_TRIADA:
                excluidos.append({"tema": n, "base": t["meta"]["base"]["triada"]})
            else:
                temas.append(t)
        if len(temas) < ML_MIN_TEMAS:
            raise RuntimeError(f"hay {len(temas)} temas útiles con MIDI importado; hacen falta al menos {ML_MIN_TEMAS}")

        rng = np.random.default_rng(0)
        orden = rng.permutation(len(temas))
        k = min(ML_GRUPOS, len(temas))
        grupos = [orden[g::k] for g in range(k)]
        combos = [(u, p_) for u in ML_UMBRALES for p_ in ML_PENALIZACIONES]
        # puntajes[(variante, umbral, pen)][tema] = (tríada, global)
        puntajes = {}
        total = len(ML_VARIANTES) * k
        paso_n = 0
        for vi, var in enumerate(ML_VARIANTES):
            for g, prueba in enumerate(grupos):
                _entreno_set(etapa="midiendo variantes (validación cruzada)", i=paso_n, n=total,
                             detalle=var["nombre"])
                paso_n += 1
                fuera = set(prueba.tolist())
                X, y = _ml_juntar([t for j, t in enumerate(temas) if j not in fuera], var["escalas"])
                m = MLModelo(X.shape[1], oculta=var["oculta"], semilla=g)
                m.entrenar(X, y, epocas=ML_EPOCAS, semilla=g)
                for j in prueba:
                    t = temas[j]
                    logp = m.log_probs(ml_con_contexto(t["F"], var["escalas"]))
                    for (u, p_) in combos:
                        seg = ml_segmentos_desde_logp(logp, t["tiempos"], t["energia"], t["meta"]["hop_seg"],
                                                      penalizacion=p_, umbral_rel=u)
                        puntajes.setdefault((vi, u, p_), {})[t["nombre"]] = _puntajes_tiempo(
                            t["meta"]["referencia"], seg, t["meta"]["duracion"])

        def prom(clave, idx):
            return float(np.mean([puntajes[clave][t["nombre"]][idx] for t in temas]))
        mejor = max(puntajes, key=lambda c_: (prom(c_, 1), prom(c_, 0)))
        vi, umbral, pen = mejor
        var = ML_VARIANTES[vi]
        # la configuración de v110 (variante 0, umbral de siempre), para mostrar cuánto se ganó
        ref_v110 = max(((0, UMBRAL_SILENCIO, p_) for p_ in ML_PENALIZACIONES), key=lambda c_: prom(c_, 1))

        base_tri = float(np.mean([t["meta"]["base"]["triada"] for t in temas]))
        base_ex = float(np.mean([t["meta"]["base"]["exacta"] for t in temas]))
        tri_mejor = prom(mejor, 0)
        dif = {t["nombre"]: puntajes[mejor][t["nombre"]][0] - t["meta"]["base"]["triada"] for t in temas}
        resultado = {
            "fecha": datetime.now().strftime("%Y-%m-%d %H:%M"), "temas": len(temas),
            "base_triada": round(base_tri, 1), "modelo_triada": round(tri_mejor, 1),
            "base_exacta": round(base_ex, 1),
            "modelo_global": round(prom(mejor, 1), 1),
            "v110_triada": round(prom(ref_v110, 0), 1), "v110_global": round(prom(ref_v110, 1), 1),
            "mejoran": sum(1 for v in dif.values() if v > 1), "empeoran": sum(1 for v in dif.values() if v < -1),
            "peores": [{"tema": n, "dif": round(v, 1)} for n, v in sorted(dif.items(), key=lambda x: x[1])[:3] if v < -1],
            "variante": var["nombre"], "umbral_silencio": umbral, "penalizacion": pen,
            "excluidos": excluidos,
        }

        guardado = tri_mejor > base_tri
        if guardado:
            _entreno_set(etapa="entrenando el modelo final", i=0, n=1, detalle=var["nombre"])
            X, y = _ml_juntar(temas, var["escalas"])
            final = MLModelo(X.shape[1], oculta=var["oculta"], semilla=0)
            final.entrenar(X, y, epocas=ML_EPOCAS, semilla=0)
            tmp = MODELO_ACORDES_PATH.with_name("modelo_acordes.tmp.npz")
            final.guardar(tmp, extra={"penalizacion": pen, "umbral_silencio": umbral,
                                      "escalas": list(var["escalas"]), "contexto": var["escalas"][0],
                                      "variante": var["nombre"], "temas": len(temas), "fecha": resultado["fecha"],
                                      "temas_entrenamiento": [t["nombre"] for t in temas]})
            os.replace(tmp, MODELO_ACORDES_PATH)
        resultado["guardado"] = guardado
        escribir_atomico(ML_RESULTADO_PATH, json.dumps(resultado, ensure_ascii=False))
        _entreno_set(corriendo=False, etapa="listo", error=None)
    except Exception as exc:  # noqa: BLE001
        _entreno_set(corriendo=False, etapa="error", error=str(exc))


def ultimo_entrenamiento():
    try:
        return json.loads(ML_RESULTADO_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


@app.route("/detector/entrenar", methods=["POST"])
def detector_entrenar():
    with _entreno_lock:
        if _entreno["corriendo"]:
            return jsonify({"error": "ya se está entrenando"}), 409
        _entreno.update(corriendo=True, etapa="arrancando", i=0, n=0, error=None, detalle="")
    threading.Thread(target=_entrenar_detector, daemon=True).start()
    return jsonify({"ok": True})


@app.route("/detector/estado")
def detector_estado():
    with _entreno_lock:
        estado = dict(_entreno)
    info = info_modelo_acordes()
    if info:
        info = {k: v for k, v in info.items() if k != "temas_entrenamiento"}
    estado.update(ultimo=ultimo_entrenamiento(), modelo=info,
                  detector_aprendido=bool(leer_prefs().get("detector_aprendido", True)))
    return jsonify(estado)


# --------------------------------------------------- pulso, compás y grilla editable ----
# Detecta el tempo/tiempos a partir de la batería ya separada (spectral flux +
# autocorrelación — de nuevo, solo numpy). La fase de "tiempo 1" del compás no se
# detecta directamente del audio (poco confiable); se elige la que mejor alinea
# los cambios de acorde ya detectados con un tiempo 1, que es un supuesto mucho
# más sólido. Asume 4/4 y tempo constante en toda la canción.

TEMPO_PRIOR_BPM = 120.0
TEMPO_PRIOR_OCTAVAS = 1.0
PERIODO_FINO = True


def _detectar_pulso(wav_path, hop=512, frame=1024, bpm_min=60, bpm_max=200):
    data, sr = _cargar_wav_mono(wav_path)
    if len(data) < frame:
        return [], 0.0
    marcos = sliding_window_view(data, frame)[::hop].copy()
    marcos *= np.hanning(frame)
    espectro = np.abs(np.fft.rfft(marcos, axis=1))
    flujo = np.diff(espectro, axis=0)
    flujo[flujo < 0] = 0
    envolvente = np.concatenate([[0.0], flujo.sum(axis=1)])
    return _pulso_desde_envolvente(envolvente, sr / hop, len(data) / sr, bpm_min, bpm_max)


def _pulso_desde_envolvente(envolvente, sr_hop, duracion, bpm_min=60, bpm_max=200):
    """(beat_times, bpm) a partir de la envolvente de ataques de la batería."""
    lag_min = int(sr_hop * 60 / bpm_max)
    lag_max = min(int(sr_hop * 60 / bpm_min), len(envolvente) - 1)
    if lag_max <= lag_min:
        return [], 0.0
    if not np.any(envolvente > 0):
        return [], 0.0   # batería en silencio: sin pulso (se muestran los acordes sin grilla)

    ec = envolvente - envolvente.mean()
    # autocorrelación por FFT: mismo resultado que np.correlate(ec, ec, "full"), pero en
    # milisegundos en vez de segundos (una canción son ~20.000 valores)
    espec_ac = np.fft.rfft(ec, 2 * len(ec))
    autocorr = np.fft.irfft(np.abs(espec_ac) ** 2)[:len(ec)]
    # Preferencia por tempos cercanos a 120 BPM (campana en escala logarítmica, 1 octava de ancho,
    # como el estimador de tempo de librosa). Sin esto, cuando bombo y caja se alternan el pico de
    # 2 tiempos le gana al de 1 y el tempo sale a la mitad. Medido contra el BPM de 30 MIDI de
    # Chordify: 15 -> 25 bien (arregla 11, rompe 1). Con TEMPO_PRIOR_OCTAVAS = 0 se desactiva.
    lags = np.arange(lag_min, lag_max + 1)
    puntaje = autocorr[lag_min:lag_max + 1]
    if TEMPO_PRIOR_OCTAVAS:
        peso = np.exp(-0.5 * (np.log2((60.0 * sr_hop / lags) / TEMPO_PRIOR_BPM) / TEMPO_PRIOR_OCTAVAS) ** 2)
        puntaje = np.maximum(puntaje, 0) * peso
    periodo_grueso = int(lags[int(np.argmax(puntaje))])

    # Período y fase finos. El período de arriba sale en pasos enteros de ~11,6 ms: a 130 BPM
    # eso es hasta ~1% de error, y como la grilla es de tempo constante, el error se acumula y
    # la grilla se va corriendo (varios tiempos al final de una canción de 4 minutos). Acá se
    # prueban períodos fraccionarios a +-3% del grueso, y para cada uno la fase, eligiendo el
    # peine que cae en promedio sobre más ataques a lo largo de TODA la canción. Medido contra
    # 30 temas de Chordify: la coincidencia de acordes en la grilla sube de 79,8% a 81,8%
    # (igual a la de los acordes sin cuantizar: la grilla deja de perder información).
    if PERIODO_FINO:
        periodo, mejor_fase = _afinar_periodo(envolvente, periodo_grueso,
                                              p_min=60.0 * sr_hop / bpm_max, p_max=60.0 * sr_hop / bpm_min)
    else:   # comportamiento anterior (app96): período entero y fase por pasos
        periodo, mejor_fase, mejor_score = periodo_grueso, 0, -1
        for fase in range(0, periodo, max(1, periodo // 20)):
            score = envolvente[np.arange(fase, len(envolvente), periodo)].sum()
            if score > mejor_score:
                mejor_score, mejor_fase = score, fase
    bpm = 60.0 * sr_hop / periodo

    n_beats = int(duracion / (periodo / sr_hop)) + 2
    beat_times = [(mejor_fase + i * periodo) / sr_hop for i in range(n_beats)]
    return [t for t in beat_times if t <= duracion], bpm


def _afinar_periodo(envolvente, periodo, rango=0.03, paso_rel=0.0005, paso_fase=0.25,
                    p_min=None, p_max=None):
    """(período, fase) en marcos, con decimales. Suaviza apenas la envolvente (ventana de 5
    marcos, ~58 ms) para que un ataque adelantado o atrasado unos milisegundos siga contando.
    Arranca por el período grueso y solo lo cambia si otro puntúa estrictamente mejor, así que
    sin información (envolvente plana) devuelve el mismo período que antes."""
    ventana = np.hanning(7)[1:-1]
    e = np.convolve(envolvente, ventana / ventana.sum(), mode="same")
    idx = np.arange(len(e))

    def puntuar(p):
        n = int((len(e) - 1 - p) / p)
        if n < 4:
            return None
        fases = np.arange(0, p, paso_fase)
        puntaje = np.interp(fases[:, None] + np.arange(n)[None, :] * p, idx, e).mean(axis=1)
        j = int(np.argmax(puntaje))
        return float(puntaje[j]), float(fases[j])

    inicial = puntuar(float(periodo))
    if inicial is None:
        return float(periodo), 0.0
    mejor = (inicial[0], float(periodo), inicial[1])
    for p in periodo * (1 + np.arange(-rango, rango + 1e-9, paso_rel)):
        if (p_min is not None and p < p_min) or (p_max is not None and p > p_max):
            continue
        r = puntuar(float(p))
        if r is not None and r[0] > mejor[0]:
            mejor = (r[0], float(p), r[1])
    return mejor[1], mejor[2]


def _elegir_fase_compas(beat_times, segmentos, beats_por_compas=4):
    cambios = [s["inicio"] for s in segmentos[1:]]
    if not beat_times or not cambios:
        return 0
    tolerancia = (beat_times[1] - beat_times[0]) / 2 if len(beat_times) > 1 else 0.1
    mejor_fase, mejor_score = 0, -1
    for fase in range(beats_por_compas):
        bajadas = beat_times[fase::beats_por_compas]
        score = sum(1 for c in cambios if any(abs(c - t) <= tolerancia for t in bajadas))
        if score > mejor_score:
            mejor_score, mejor_fase = score, fase
    return mejor_fase


def _acorde_por_mayoria(segmentos, desde, hasta, i0=0):
    """(acorde, i0): el acorde que más tiempo ocupa en [desde, hasta), o None si no hay ninguno.
    i0 es por dónde seguir buscando en la próxima llamada (los tiempos vienen en orden)."""
    while i0 < len(segmentos) and segmentos[i0]["fin"] <= desde:
        i0 += 1
    duraciones = {}
    i = i0
    while i < len(segmentos) and segmentos[i]["inicio"] < hasta:
        d = min(segmentos[i]["fin"], hasta) - max(segmentos[i]["inicio"], desde)
        if d > 0:
            duraciones[segmentos[i]["acorde"]] = duraciones.get(segmentos[i]["acorde"], 0.0) + d
        i += 1
    return (max(duraciones, key=duraciones.get) if duraciones else None), i0


def _grid_desde_segmentos(beat_times, segmentos, beats_por_compas=4):
    tokens = []
    anterior = None
    i0 = 0
    for k, t in enumerate(beat_times):
        if GRILLA_POR_MAYORIA:
            if k + 1 < len(beat_times):
                hasta = beat_times[k + 1]
            else:   # último tiempo: mismo largo que el anterior
                hasta = t + (t - beat_times[k - 1] if k > 0 else 0.5)
            acorde, i0 = _acorde_por_mayoria(segmentos, t, hasta, i0)
            acorde = acorde or anterior or "—"
        else:       # app97: el acorde que suena en el instante del tiempo
            acorde = next((s["acorde"] for s in segmentos if s["inicio"] <= t < s["fin"]), anterior or "—")
        tokens.append("." if acorde == anterior else acorde)
        anterior = acorde
    # recortar el compás final si quedó incompleto (prolijidad, no afecta la sincronía)
    sobra = len(tokens) % beats_por_compas
    if sobra:
        tokens, beat_times = tokens[:-sobra], beat_times[:-sobra]
    return tokens, beat_times


CABECERA_ACORDES_TXT = (
    "# Acordes por compás, 4 tiempos cada uno, separados por \"|\".\n"
    "# Un punto (.) = sigue sonando el acorde anterior.\n"
    "# Para borrar un cambio: reemplazalo por un punto, no borres la posición.\n"
    "# Siempre tienen que quedar 4 por compás, o se desincroniza todo lo que sigue.\n"
    "\n"
)


def _tokens_a_texto(tokens, beats_por_compas=4, compases_por_linea=4):
    compases = [tokens[i:i + beats_por_compas] for i in range(0, len(tokens), beats_por_compas)]
    lineas = [
        " | ".join(" ".join(c) for c in compases[i:i + compases_por_linea])
        for i in range(0, len(compases), compases_por_linea)
    ]
    return CABECERA_ACORDES_TXT + "\n".join(lineas) + "\n"


_RE_COMENTARIO = re.compile(r"(?:^|\s)#.*$")


def _texto_a_tokens(texto):
    # un "#" solo es comentario si está separado por un espacio (o al inicio de
    # línea) — así no se come acordes con sostenido como "C#" o "F#m"
    limpio = "\n".join(_RE_COMENTARIO.sub("", linea) for linea in texto.splitlines())
    return [t for t in re.split(r"[\s|]+", limpio.strip()) if t]


# Bemoles -> sostenidos: es el mismo acorde con otro nombre, así que en vez de
# rechazar "Bb" lo guardamos como "A#" (el vocabulario interno usa sostenidos).
_ENARMONICOS = {"Db": "C#", "Eb": "D#", "Gb": "F#", "Ab": "G#", "Bb": "A#"}


def normalizar_token(token: str):
    """Devuelve (token_normalizado, es_valido). Un token vacío o '.' significa
    'sigue el acorde anterior'; '—' significa 'silencio armónico' (sin acorde).
    La validación es estricta contra el vocabulario que produce el detector
    (mayor / menor / séptima) más los sufijos extra editables (maj7, sus4)."""
    t = (token or "").strip()
    if t in ("", "."):
        return ".", True
    if t == "—":
        return "—", True

    # separar raíz (con alteración) del sufijo, normalizando bemoles
    raiz, sufijo = t[:1].upper(), t[1:]
    if sufijo[:1] in ("#", "b"):
        raiz, sufijo = raiz + sufijo[0], sufijo[1:]
    if raiz in _ENARMONICOS:
        raiz = _ENARMONICOS[raiz]

    if raiz not in NOTE_NAMES:
        return t, False
    if sufijo not in SUFIJOS_VALIDOS:
        return t, False
    return raiz + sufijo, True


# ------------------------- importar acordes desde MIDI -------------------------
# Los MIDI "time aligned" de Chordify traen las tríadas en un canal y la nota del
# bajo en otro, con el tempo real de la canción. Eso es mucho más confiable que
# el detector propio, así que conviene poder usarlos cuando existen.

TIPOS_MIDI = [
    (frozenset([0, 4, 7, 10]), "7"),
    (frozenset([0, 3, 7, 10]), "m7"),
    (frozenset([0, 4, 7, 11]), "maj7"),
    (frozenset([0, 3, 6, 10]), "m7b5"),
    (frozenset([0, 4, 7]), ""),
    (frozenset([0, 3, 7]), "m"),
    (frozenset([0, 3, 6]), "dim"),
    (frozenset([0, 4, 8]), "aug"),
    (frozenset([0, 5, 7]), "sus4"),
    (frozenset([0, 2, 7]), "sus2"),
]
# Mesa maneja mayor / menor / séptima en el detector automático, más maj7 y sus4
# como sufijos aceptados al editar/importar (ver SUFIJOS_VALIDOS). El resto se
# reduce a la tríada más cercana (se avisa cuántos se simplificaron al importar).
REDUCIR_A_VOCABULARIO = {
    "": "", "m": "m", "7": "7",
    "m7": "m", "maj7": "maj7", "m7b5": "m",
    "dim": "m", "aug": "", "sus4": "sus4", "sus2": "",
}


def _identificar_acorde_midi(pcs, bajo=None):
    """v108: si hay nota de bajo, se prueba primero esa raíz. Desempata los
    conjuntos ambiguos: C-F-A# es Fsus4 con bajo F y A#sus2 con bajo A#. Las
    tríadas comunes no cambian (su conjunto de notas tiene una sola lectura)."""
    pcs = frozenset(pcs)
    orden = list(range(12))
    if bajo is not None:
        orden.remove(bajo)
        orden.insert(0, bajo)
    for raiz in orden:
        rel = frozenset((p - raiz) % 12 for p in pcs)
        for patron, sufijo in TIPOS_MIDI:
            if rel == patron:
                return NOTE_NAMES[raiz], sufijo
    return None


def leer_acordes_midi(ruta):
    """Devuelve (segmentos, bpm, simplificados). Cada segmento tiene inicio/fin en
    segundos y el nombre ya reducido al vocabulario de Mesa."""
    import mido

    m = mido.MidiFile(ruta)
    tpb = m.ticks_per_beat

    tempos, t = [], 0
    for msg in m.tracks[0]:
        t += msg.time
        if msg.type == "set_tempo":
            tempos.append((t, msg.tempo))
    if not tempos:
        tempos = [(0, 500000)]

    def ticks_a_seg(tick):
        seg, prev_tick, prev_tempo = 0.0, 0, tempos[0][1]
        for tt, tempo in tempos:
            if tt >= tick:
                break
            seg += mido.tick2second(tt - prev_tick, tpb, prev_tempo)
            prev_tick, prev_tempo = tt, tempo
        return seg + mido.tick2second(tick - prev_tick, tpb, prev_tempo)

    eventos = {}
    for track in m.tracks[1:]:
        t, activas = 0, {}
        for msg in track:
            t += msg.time
            if msg.type == "note_on" and msg.velocity > 0:
                activas[msg.note] = t
            elif msg.type == "note_off" or (msg.type == "note_on" and msg.velocity == 0):
                if msg.note in activas:
                    ini = activas.pop(msg.note)
                    e = eventos.setdefault(ini, {"acorde": set(), "bajo": set(), "fin": t})
                    (e["bajo"] if getattr(msg, "channel", 0) == 1 else e["acorde"]).add(msg.note)
                    e["fin"] = max(e["fin"], t)

    segmentos, simplificados = [], []
    for ini in sorted(eventos):
        e = eventos[ini]
        if not e["acorde"]:
            continue
        bajo_pc = (min(e["bajo"]) % 12) if e["bajo"] else None
        ident = _identificar_acorde_midi({n % 12 for n in e["acorde"]}, bajo_pc)
        if not ident:
            continue
        raiz, sufijo = ident
        base = raiz + REDUCIR_A_VOCABULARIO.get(sufijo, "")
        original = raiz + sufijo
        # bajo distinto de la fundamental (ej. Em/B): se anota como simplificación
        if e["bajo"]:
            pc_bajo = min(e["bajo"]) % 12
            if pc_bajo != NOTE_NAMES.index(raiz):
                original += "/" + NOTE_NAMES[pc_bajo]
        if original != base:
            simplificados.append(f"{original} → {base}")
        segmentos.append({
            "inicio": round(ticks_a_seg(ini), 3),
            "fin": round(ticks_a_seg(e["fin"]), 3),
            "acorde": base,
        })

    return segmentos, 60_000_000 / tempos[0][1], simplificados



# La cejilla es solo una capa de visualización: no toca el audio ni acordes.txt.
# Con cejilla en el traste N, la FORMA que agarrás suena N semitonos más arriba,
# así que para mostrar la forma se transpone el acorde real -N semitonos.

# Formas que se tocan al aire en afinación estándar (sin cejinilla con el dedo).
# Son las que hacen que valga la pena poner cejilla.
FORMAS_ABIERTAS = {
    "C", "A", "G", "E", "D",
    "Em", "Am", "Dm",
    "C7", "A7", "G7", "E7", "D7", "B7",
    "Csus4", "Dsus4", "Esus4", "Gsus4", "Asus4",   # v108
}
# Formas cómodas aunque no del todo abiertas (medio punto).
FORMAS_ACEPTABLES = {"F", "Fm", "Bm", "B", "Cm", "Gm"}


def transponer_acorde(acorde: str, semitonos: int) -> str:
    """Transpone un acorde del vocabulario. Devuelve el token tal cual si no
    es un acorde (por ejemplo '.' o '—')."""
    norm, ok = normalizar_token(acorde)
    if not ok or norm in (".", "—"):
        return acorde
    raiz = norm[:2] if norm[:2] in NOTE_NAMES else norm[:1]
    sufijo = norm[len(raiz):]
    idx = (NOTE_NAMES.index(raiz) + semitonos) % 12
    return NOTE_NAMES[idx] + sufijo


def sugerir_capo(segmentos, capo_max=7):
    """Prueba los trastes y elige el que deja más tiempo de la canción en
    formas abiertas. Pondera por duración: un acorde que suena todo el estribillo
    pesa más que uno de paso. Se limita al traste 7: más arriba es correcto en
    teoría pero impráctico (queda muy poco mástil), y ante puntajes parecidos
    conviene siempre la cejilla más baja."""
    if not segmentos:
        return 0, []

    duracion_por_acorde = {}
    for s in segmentos:
        if s["acorde"] in (".", "—"):
            continue
        dur = max(0.0, s["fin"] - s["inicio"])
        duracion_por_acorde[s["acorde"]] = duracion_por_acorde.get(s["acorde"], 0.0) + dur

    total = sum(duracion_por_acorde.values())
    if not total:
        return 0, []

    ranking = []
    for capo in range(capo_max + 1):
        puntos = 0.0
        for acorde, dur in duracion_por_acorde.items():
            forma = transponer_acorde(acorde, -capo)
            if forma in FORMAS_ABIERTAS:
                puntos += dur
            elif forma in FORMAS_ACEPTABLES:
                puntos += dur * 0.5
        cobertura = puntos / total
        ranking.append({
            "capo": capo,
            "puntaje": round(cobertura, 3),
            # desempate suave hacia trastes bajos
            "_orden": cobertura - capo * 0.005,
        })

    ranking.sort(key=lambda r: (-r["_orden"], r["capo"]))
    for r in ranking:
        r.pop("_orden", None)
    return ranking[0]["capo"], ranking


def _tokens_a_segmentos(tokens, beat_times, duracion):
    n = min(len(tokens), len(beat_times))
    if n == 0:
        return []
    acordes, ultimo = [], "—"
    for i in range(n):
        if tokens[i] != ".":
            ultimo = tokens[i]
        acordes.append(ultimo)

    segmentos = []
    actual, inicio = acordes[0], beat_times[0]
    for i in range(1, n):
        if acordes[i] != actual:
            segmentos.append({"inicio": round(inicio, 2), "fin": round(beat_times[i], 2), "acorde": actual})
            actual, inicio = acordes[i], beat_times[i]
    paso = beat_times[-1] - beat_times[-2] if n > 1 else 1.0
    segmentos.append({"inicio": round(inicio, 2), "fin": round(max(duracion, beat_times[-1] + paso), 2), "acorde": actual})
    return segmentos


# ---------------------------------------------------------------- rutas ----

def _color_cancion(song: str) -> str:
    # el color sale del nombre, no de la posición en la lista: agregar o borrar
    # una canción ya no le cambia el color a todas las que vienen después
    colores_lista = list(STEM_COLORS.values())
    return colores_lista[zlib.crc32(song.encode("utf-8")) % len(colores_lista)]


@app.route("/recientes")
def recientes():
    """v103: la lista "Últimas que abriste", sola y siempre fresca. La portada
    entera puede llegar desde la copia offline del service worker (con la red
    lenta, pasados 2,5 s, usa la guardada) y ahí la lista quedaba vieja; esta
    ruta no la cachea nadie, y la portada la pide cada vez que se muestra."""
    canciones = list_ready_songs()
    try:
        horas = json.loads(_recientes_path().read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        horas = {}
    lista = []
    for c in obtener_recientes(canciones):
        d = datos_cancion(c)
        lista.append({"song": c, "url": url_for("mesa", song=c), "titulo": d["titulo"],
                      "autor": d["autor"], "color": _color_cancion(c), "t": horas.get(c, 0)})
    return jsonify(lista), 200, {"Cache-Control": "no-store"}


@app.route("/recientes", methods=["POST"])
def sincronizar_recientes():
    """v103: aperturas anotadas en un dispositivo mientras no tenía conexión
    con la PC ({"aperturas": {cancion: hora}}). Se guardan con su hora
    original; si la PC ya tenía una más nueva para ese tema, queda la nueva."""
    aperturas = (request.get_json(silent=True) or {}).get("aperturas")
    if not isinstance(aperturas, dict):
        return jsonify({"error": "no recibí las aperturas"}), 400
    ahora = time.time()
    disponibles = set(list_ready_songs())
    ruta = _recientes_path()
    with _LOCK_DATOS:
        try:
            datos = json.loads(ruta.read_text(encoding="utf-8")) if ruta.exists() else {}
        except (json.JSONDecodeError, OSError):
            datos = {}
        for song, t in aperturas.items():
            try:
                t = min(float(t), ahora)   # un reloj adelantado no la deja "en el futuro"
            except (TypeError, ValueError):
                continue
            if song in disponibles and t > datos.get(song, 0):
                datos[song] = t
        try:
            escribir_atomico(ruta, json.dumps(datos))
        except OSError as exc:
            return jsonify({"error": str(exc)}), 500
    return jsonify({"ok": True})


def contexto_ajustes_generales():
    """v107: lo que necesita el panel de Ajustes generales (PANEL_GENERALES_HTML),
    que ahora se muestra en la mesa y también en la portada."""
    prefs = leer_prefs()

    def color(clave, defecto):
        valor = prefs.get(clave, defecto)
        return valor if valor in STEM_ORDER else defecto

    return {
        "mostrar_grados": prefs.get("mostrar_grados", True),
        "mostrar_diagramas": prefs.get("mostrar_diagramas", True),
        "colorear_duracion": prefs.get("colorear_duracion", False),
        "hud_activo": prefs.get("hud_activo", False),
        "hud_invertido": prefs.get("hud_invertido", False),
        "hud_ble": prefs.get("hud_ble", False),
        "hud_brillo": _hud_nivel_brillo(prefs.get("hud_brillo", HUD_BRILLO_DEFECTO)),
        "hud_brillos": list(HUD_BRILLOS),
        "color_corto": color("color_corto", "vocals"),
        "color_normal": color("color_normal", "guitar"),
        "color_largo": color("color_largo", "bass"),
        "stem_order": STEM_ORDER, "stem_colores": STEM_COLORS, "stem_labels": STEM_LABELS,
        "es_la_pc": request.remote_addr in ("127.0.0.1", "::1", "localhost"),
        "calidad_actual": calidad_pedida(),
    }


@app.route("/")
def home():
    canciones = list_ready_songs()
    color_por_cancion = {c: _color_cancion(c) for c in canciones}
    datos = {c: datos_cancion(c) for c in canciones}
    return render_template_string(
        HOME_HTML, canciones=canciones, recientes=obtener_recientes(canciones),
        colores=color_por_cancion, datos=datos, setlists=leer_setlists(),
        jobs=jobs_activos(), version_app=VERSION_APP,
        iniciales={c: iniciales_cancion(datos[c]["titulo"]) for c in canciones},
        bpms={c: bpm_cancion(c) for c in canciones},
        en_mesa=False, **contexto_ajustes_generales(),
    )


@app.route("/setlists/crear", methods=["POST"])
def crear_setlist():
    nombre = (request.form.get("nombre") or "").strip()[:80]
    if not nombre:
        return redirect(url_for("home"))
    with _LOCK_DATOS:   # v112
        setlists = leer_setlists()
        sid = uuid.uuid4().hex[:10]
        setlists[sid] = {"nombre": nombre, "canciones": []}
        guardar_setlists(setlists)
    return redirect(url_for("ver_setlist", setlist_id=sid))


@app.route("/setlist/<setlist_id>")
def ver_setlist(setlist_id):
    setlists = leer_setlists()
    sl = setlists.get(setlist_id)
    if sl is None:
        return redirect(url_for("home"))
    todas = list_ready_songs()
    disponibles = set(todas)
    canciones = [c for c in sl["canciones"] if c in disponibles]  # ya no muestra las borradas
    datos = {c: datos_cancion(c) for c in canciones}
    para_agregar = sorted((c for c in todas if c not in canciones), key=lambda c: datos_cancion(c)["titulo"].lower())
    datos_agregar = {c: datos_cancion(c) for c in para_agregar}
    return render_template_string(
        SETLIST_HTML, setlist_id=setlist_id, nombre=sl["nombre"],
        canciones=canciones, datos=datos, para_agregar=para_agregar, datos_agregar=datos_agregar,
        titulo_pagina=f"{sl['nombre']} · Mesa", calidad_actual=calidad_pedida(),
    )


@app.route("/setlist/<setlist_id>/offline")
def setlist_offline(setlist_id):
    """Lista de todo lo que hay que descargar para tocar el setlist entero sin
    wifi, canción por canción, para el botón "Descargar setlist"."""
    setlists = leer_setlists()
    sl = setlists.get(setlist_id)
    if sl is None:
        return jsonify({"error": "ese setlist no existe"}), 404
    canciones = [c for c in sl["canciones"] if stems_dir(c).exists()]
    return jsonify({
        "paginas": [url_for("home"), url_for("ver_setlist", setlist_id=setlist_id)],
        "canciones": [
            {"song": c, "titulo": nombre_mostrar(c), "urls": urls_offline_cancion(c, setlists)}
            for c in canciones
        ],
    })


@app.route("/setlist/<setlist_id>/agregar", methods=["POST"])
def agregar_a_setlist(setlist_id):
    with _LOCK_DATOS:   # v112
        setlists = leer_setlists()
        sl = setlists.get(setlist_id)
        if sl is None:
            return jsonify({"error": "ese setlist no existe"}), 404
        song = (request.get_json(silent=True) or {}).get("song", "")
        if song and stems_dir(song).exists() and song not in sl["canciones"]:
            sl["canciones"].append(song)
            guardar_setlists(setlists)
    return jsonify({"ok": True, "canciones": sl["canciones"]})


@app.route("/setlist/<setlist_id>/quitar", methods=["POST"])
def quitar_de_setlist(setlist_id):
    with _LOCK_DATOS:   # v112
        setlists = leer_setlists()
        sl = setlists.get(setlist_id)
        if sl is None:
            return jsonify({"error": "ese setlist no existe"}), 404
        song = (request.get_json(silent=True) or {}).get("song", "")
        sl["canciones"] = [c for c in sl["canciones"] if c != song]
        guardar_setlists(setlists)
    return jsonify({"ok": True, "canciones": sl["canciones"]})


@app.route("/setlist/<setlist_id>/orden", methods=["POST"])
def reordenar_setlist(setlist_id):
    with _LOCK_DATOS:   # v112
        setlists = leer_setlists()
        sl = setlists.get(setlist_id)
        if sl is None:
            return jsonify({"error": "ese setlist no existe"}), 404
        nuevas = (request.get_json(silent=True) or {}).get("canciones") or []
        # solo aceptamos si es una reordenación real (mismas canciones, otro orden).
        # Se compara contra las que EXISTEN: una carpeta borrada a mano dejaba un
        # nombre fantasma en la lista que la página no muestra, y el reorden se
        # rechazaba en silencio para siempre. Guardar el orden nuevo la limpia.
        existentes = [c for c in sl["canciones"] if stems_dir(c).exists()]
        if isinstance(nuevas, list) and set(nuevas) == set(existentes):
            sl["canciones"] = nuevas
            guardar_setlists(setlists)
    return jsonify({"ok": True, "canciones": sl["canciones"]})


@app.route("/setlist/<setlist_id>/borrar", methods=["POST"])
def borrar_setlist(setlist_id):
    with _LOCK_DATOS:   # v112
        setlists = leer_setlists()
        if setlist_id in setlists:
            del setlists[setlist_id]
            guardar_setlists(setlists)
    return jsonify({"ok": True})


@app.route("/borrar/<song>", methods=["POST"])
def borrar_cancion(song):
    """Borra los stems separados de una canción y su mp3 original.
    Se lleva puestas las correcciones de acordes, así que el pedido viene con
    doble confirmación desde la interfaz."""
    import shutil

    carpeta = stems_dir(song)
    if not carpeta.exists():
        return jsonify({"error": "esa canción no existe"}), 404

    try:
        shutil.rmtree(carpeta)
    except OSError as exc:
        return jsonify({"error": f"no pude borrar la carpeta: {exc}. ¿Tenés algún archivo abierto?"}), 500

    # el mp3 original, que queda ocupando lugar en uploads/
    for archivo in UPLOAD_DIR.glob("*"):
        if archivo.is_file() and archivo.stem == song:
            try:
                archivo.unlink()
            except OSError:
                pass  # si no se puede borrar el mp3, los stems ya se fueron igual

    # sacarla de cualquier setlist donde apareciera, para no dejar huecos
    with _LOCK_DATOS:   # v112
        setlists = leer_setlists()
        modificado = False
        for sl in setlists.values():
            if song in sl.get("canciones", []):
                sl["canciones"] = [c for c in sl["canciones"] if c != song]
                modificado = True
        if modificado:
            guardar_setlists(setlists)

    return jsonify({"ok": True})


@app.route("/subir", methods=["POST"])
def subir():
    archivo = request.files.get("mp3")
    if not archivo or archivo.filename == "":
        return redirect(url_for("home"))

    nombre = secure_filename(archivo.filename)
    # v112: un nombre sin letras ASCII ("曲.mp3") queda vacío o como "mp3" a secas:
    # vacío fallaba, y "mp3" hacía que dos temas así se pisaran entre sí
    if not nombre or "." not in nombre:
        nombre = f"subida_{uuid.uuid4().hex[:8]}.mp3"
    destino = UPLOAD_DIR / nombre
    archivo.save(destino)

    job_id = uuid.uuid4().hex
    JOBS[job_id] = {"status": "en_cola", "song": song_slug(nombre), "log": "", "started": time.time()}

    hilo = threading.Thread(target=run_demucs, args=(job_id, destino), daemon=True)
    hilo.start()

    return redirect(url_for("procesando", job_id=job_id))


@app.route("/youtube", methods=["POST"])
def youtube():
    url = (request.form.get("url") or "").strip()
    if not url or not re.match(r"^https?://", url):
        return redirect(url_for("home"))

    job_id = uuid.uuid4().hex
    JOBS[job_id] = {"status": "en_cola", "song": None, "log": "", "started": time.time()}

    hilo = threading.Thread(target=descargar_youtube, args=(job_id, url), daemon=True)
    hilo.start()

    return redirect(url_for("procesando", job_id=job_id))


@app.route("/procesando/<job_id>")
def procesando(job_id):
    if job_id not in JOBS:
        return redirect(url_for("home"))
    return render_template_string(PROCESANDO_HTML, job_id=job_id, titulo_pagina="Separando pistas · Mesa",
                                  titulo_tema=_titulo_job(JOBS[job_id]))


def _titulo_job(job: dict) -> str:
    """v113: nombre legible del tema para la pantalla de proceso (de YouTube
    se conoce recién al terminar la descarga)."""
    song = job.get("song")
    if not song:
        return ""
    try:
        return nombre_mostrar(song).replace("_", " ").strip()
    except Exception:  # noqa: BLE001
        return song.replace("_", " ")


@app.route("/estado/<job_id>")
def estado(job_id):
    job = JOBS.get(job_id)
    if not job:
        return jsonify({"status": "error", "log": "job desconocido"}), 404
    resp = {"status": job["status"], "elapsed": round(time.time() - job["started"]),
            # v113: datos para la ventana de progreso
            "progreso": job.get("progreso"), "estimado": job.get("estimado"),
            "etapa": job.get("etapa"), "titulo": _titulo_job(job)}
    if job["status"] == "listo":
        resp["redirect"] = url_for("mesa", song=job["song"])
    if job["status"] == "error":
        resp["log"] = job["log"]
    return jsonify(resp)


@app.route("/alias/<song>", methods=["POST"])
def guardar_alias(song):
    """Guarda (o borra, si vienen vacíos) el título/autor elegidos a mano
    para mostrar esta canción, sin tocar el nombre real de la carpeta."""
    carpeta = stems_dir(song)
    if not carpeta.exists():
        return jsonify({"error": "canción no encontrada"}), 404
    entrada = request.get_json(silent=True) or {}
    titulo = (entrada.get("titulo") or "").strip()[:120]
    autor = (entrada.get("autor") or "").strip()[:120]
    escribir_atomico(alias_path(song), json.dumps({"titulo": titulo, "autor": autor}))
    return jsonify({"titulo": titulo or song, "autor": autor or "----------"})


@app.route("/preferencia", methods=["POST"])
def guardar_preferencia():
    """Guarda una preferencia global de la app (ej. mostrar grados sí/no,
    o qué color de instrumento usar para cada banda de duración)."""
    entrada = request.get_json(silent=True) or {}
    clave = entrada.get("clave")
    if clave in ("mostrar_grados", "modo_tocar", "colorear_duracion",
                 "controles_colapsados", "mezcla_colapsada",
                 "mostrar_diagramas", "generales_colapsado", "vista_cinta",
                 "cuenta_regresiva", "detector_aprendido"):
        guardar_pref(clave, bool(entrada.get("valor")))
        return jsonify({"ok": True})
    if clave in ("hud_activo", "hud_invertido", "hud_ble"):
        valor = bool(entrada.get("valor"))
        guardar_pref(clave, valor)
        if clave == "hud_activo":
            _hud_set_activo(valor)
        elif clave == "hud_ble":
            _hud_ble_set_activo(valor)
        else:
            _hud_set_invertido(valor)
        return jsonify({"ok": True})
    if clave == "hud_brillo":
        nivel = _hud_set_brillo(entrada.get("valor"))
        guardar_pref(clave, nivel)
        return jsonify({"ok": True, "valor": nivel})
    if clave in ("color_corto", "color_normal", "color_largo"):
        valor = entrada.get("valor")
        if valor not in STEM_ORDER:   # solo los 6 colores que ya usan los canales
            return jsonify({"error": "color inválido"}), 400
        guardar_pref(clave, valor)
        return jsonify({"ok": True})
    if clave == "color_base":
        # v106: color base de toda la app. "" = paleta original. Es global
        # (prefs.json): la PC y la tablet comparten el mismo color.
        valor = str(entrada.get("valor") or "").strip().lower()
        if valor and valor != "mono" and not _RE_COLOR_BASE.match(valor):
            return jsonify({"error": "color inválido"}), 400
        guardar_pref(clave, valor)
        return jsonify({"ok": True})
    if clave == "master_pc":
        # nivel del fader Master de la PC. Solo la PC lo guarda acá: la ventana
        # pywebview no conserva cookies entre arranques (modo privado), así
        # que sin esto volvería al 100% cada vez. La tablet lo lleva en cookie.
        try:
            valor = float(entrada.get("valor"))
        except (TypeError, ValueError):
            return jsonify({"error": "valor inválido"}), 400
        guardar_pref(clave, max(0.0, min(1.0, valor)))
        return jsonify({"ok": True})
    return jsonify({"error": "preferencia desconocida"}), 400


@app.route("/mesa/<song>")
def mesa(song):
    carpeta = stems_dir(song)
    if not carpeta.exists():
        return redirect(url_for("home"))
    # v103: solo cuenta como "abierta" una navegación real. Los fetch() de
    # "Descargar todas" y de la descarga de un setlist piden esta misma página
    # para guardarla offline y llenaban "Últimas que abriste" con temas que
    # nadie abrió. El navegador los distingue con Sec-Fetch-Mode: "navigate" al
    # abrir la página, "cors" en un fetch(). Si no manda la cabecera (http por
    # IP local), se registra como siempre.
    # OJO: no sirve Sec-Fetch-Dest. Toda navegación pasa por el service worker,
    # que la reenvía con fetch(req), y ahí el destino llega "empty" aunque sea
    # una apertura real -- con eso la lista no se actualizaba nunca. El modo sí
    # se conserva (verificado en Chromium con el service worker activo).
    if request.headers.get("Sec-Fetch-Mode", "navigate") == "navigate":
        registrar_apertura(song)
    disponibles = {p.stem for p in carpeta.glob("*.wav")}
    pistas = [
        {"id": stem, "label": STEM_LABELS[stem], "color": STEM_COLORS[stem], "url": url_for("archivo_pista", song=song, stem=stem)}
        for stem in STEM_ORDER if stem in disponibles
    ]

    # si se abrió desde un setlist, armamos anterior/siguiente para navegar
    # sin volver a la portada entre canción y canción
    setlist_id = request.args.get("setlist")
    setlist_ctx = None
    if setlist_id:
        sl = leer_setlists().get(setlist_id)
        if sl:
            existentes = [c for c in sl["canciones"] if stems_dir(c).exists()]
            if song in existentes:
                idx = existentes.index(song)
                setlist_ctx = {
                    "id": setlist_id,
                    "nombre": sl["nombre"],
                    "posicion": idx + 1,
                    "total": len(existentes),
                    "anterior": existentes[idx - 1] if idx > 0 else None,
                    "siguiente": existentes[idx + 1] if idx + 1 < len(existentes) else None,
                }

    prefs = leer_prefs()
    mostrar_grados = prefs.get("mostrar_grados", True)   # por defecto encendido
    # Modo tocar es POR DISPOSITIVO (cookie): entrar en modo tocar en la tablet
    # no tiene por qué abrir la PC en modo tocar. Si este dispositivo nunca lo
    # tocó, vale la preferencia global de siempre (así nada cambia hasta que
    # se use el botón una vez).
    cookie_tocar = request.cookies.get("mesa_modo_tocar")
    modo_tocar = (cookie_tocar == "1") if cookie_tocar in ("0", "1") else prefs.get("modo_tocar", False)
    colorear_duracion = prefs.get("colorear_duracion", False)   # por defecto queda como estaba
    controles_colapsados = prefs.get("controles_colapsados", True)   # se ajusta una vez por tema, no hace falta tenerlo siempre abierto
    # la mezcla también queda guardada por canción (mezcla.json), así que
    # tampoco hace falta tenerla siempre desplegada: la cabecera del panel
    # muestra un resumen ("guitarra en mute") aunque esté cerrada
    mezcla_colapsada = prefs.get("mezcla_colapsada", True)
    # tira de compases que vienen: apagada por defecto, para que la pantalla
    # siga viéndose exactamente igual que hasta ahora hasta que la prendas
    # v87: cinta de compases que se desplaza (modo alternativo del cartel).
    # Apagada por defecto: la vista de siempre no cambia hasta que la prendas.
    vista_cinta = prefs.get("vista_cinta", False)
    # v89: cuenta regresiva 4-3-2-1 antes de arrancar (play desde pausa y
    # autoplay del setlist). Apagada por defecto.
    cuenta_regresiva = prefs.get("cuenta_regresiva", False)
    # La calidad de audio es POR DISPOSITIVO (cookie), no una preferencia global:
    # la PC lee del disco local y no gana nada bajando la calidad, mientras que
    # la tablet depende del WiFi. Por eso el selector solo aparece cuando la
    # página NO se está sirviendo a la propia PC.
    es_la_pc = request.remote_addr in ("127.0.0.1", "::1", "localhost")
    calidad_actual = calidad_pedida()
    # Master: ganancia general DEL DISPOSITIVO QUE SUENA (nodo en el navegador),
    # ya no el volumen de Windows. Por cookie en cada dispositivo; la PC además
    # lo guarda en prefs (ver "master_pc" en /preferencia).
    master_inicial = 1.0
    try:
        if "mesa_master" in request.cookies:
            master_inicial = float(request.cookies["mesa_master"])
        elif es_la_pc:
            master_inicial = float(prefs.get("master_pc", 1.0))
    except (TypeError, ValueError):
        master_inicial = 1.0
    master_inicial = max(0.0, min(1.0, master_inicial))
    urls_offline = urls_offline_cancion(song)
    # los diagramas del mástil siempre fueron globales de hecho (no dependen del
    # tema), pero hasta ahora no se guardaban: volvían a encenderse en cada
    # recarga. Ahora se recuerdan igual que los grados.
    mostrar_diagramas = prefs.get("mostrar_diagramas", True)
    # el panel de ajustes generales arranca cerrado: se toca una vez y listo
    generales_colapsado = prefs.get("generales_colapsado", True)
    # gafas HUD: arranca apagado (ver comentario junto a _hud_activo) -- se
    # lee de prefs.json para que la página muestre el estado real del server,
    # que es el mismo _hud_activo/_hud_invertido que ya está en memoria
    hud_activo = prefs.get("hud_activo", False)
    hud_invertido = prefs.get("hud_invertido", False)
    hud_ble_pref = prefs.get("hud_ble", False)
    hud_brillo = _hud_nivel_brillo(prefs.get("hud_brillo", HUD_BRILLO_DEFECTO))
    # colores por defecto de cada banda: guitarra y bajo son los mismos que ya
    # usábamos antes de que esto fuera elegible (dorado/turquesa); voz es el
    # más parecido al rojo de alerta dentro de la paleta de instrumentos
    color_corto = prefs.get("color_corto", "vocals")
    color_normal = prefs.get("color_normal", "guitar")
    color_largo = prefs.get("color_largo", "bass")
    if color_corto not in STEM_ORDER: color_corto = "vocals"
    if color_normal not in STEM_ORDER: color_normal = "guitar"
    if color_largo not in STEM_ORDER: color_largo = "bass"

    return render_template_string(
        MESA_HTML, song=song, titulo=nombre_mostrar(song), pistas=pistas,
        setlist=setlist_ctx, mostrar_grados=mostrar_grados, modo_tocar=modo_tocar,
        colorear_duracion=colorear_duracion, controles_colapsados=controles_colapsados,
        mezcla_colapsada=mezcla_colapsada, velocidades=VELOCIDADES,
        mostrar_diagramas=mostrar_diagramas, vista_cinta=vista_cinta,
        cuenta_regresiva=cuenta_regresiva,
        es_la_pc=es_la_pc, calidad_actual=calidad_actual, calidades=CALIDADES,
        generales_colapsado=generales_colapsado,
        hud_activo=hud_activo, hud_invertido=hud_invertido, hud_ble=hud_ble_pref,
        hud_brillo=hud_brillo, hud_brillos=list(HUD_BRILLOS),
        color_corto=color_corto, color_normal=color_normal, color_largo=color_largo,
        stem_order=STEM_ORDER, stem_colores=STEM_COLORS, stem_labels=STEM_LABELS,
        master_inicial=master_inicial, urls_offline=urls_offline,
        titulo_pagina=f"{nombre_mostrar(song)} · Mesa",
        # v107: cabecera tipo reproductor (portada con iniciales + autor)
        autor=("" if datos_cancion(song)["autor"] == "----------" else datos_cancion(song)["autor"]),
        iniciales=iniciales_cancion(nombre_mostrar(song)), color_cancion=_color_cancion(song),
        en_mesa=True,
    )


@app.route("/audio/<song>/<stem>.mp3")
def archivo_pista(song, stem):
    """?t=75 devuelve la pista al 75% de velocidad con el mismo tono. La primera
    vez que se pide una velocidad hay que esperar a ffmpeg (unos segundos por
    pista); después queda cacheada al lado de los stems."""
    carpeta = stems_dir(song)
    if stem not in STEM_ORDER:   # v103: el stem llega de la URL, igual que la canción
        return jsonify({"error": "pista desconocida"}), 404
    try:
        tempo = float(request.args.get("t", 100)) / 100.0
    except (TypeError, ValueError):
        tempo = 1.0
    tempo = max(0.5, min(1.0, tempo))

    mp3 = asegurar_mp3_stem(carpeta, stem, tempo, calidad_pedida())
    if mp3 is None:
        if abs(tempo - 1.0) > 1e-3:
            # sin ffmpeg no hay forma de bajar la velocidad sin bajar el tono,
            # y servir el original a velocidad normal sería peor que fallar:
            # sonaría desfasado contra las otras pistas ya cargadas lentas.
            return jsonify({"error": "no pude generar la versión lenta (¿está ffmpeg en el PATH?)"}), 500
        # ffmpeg no disponible o falló la conversión: mejor servir el wav
        # original (pesado, pero funciona) que romper la reproducción.
        return send_from_directory(carpeta, f"{stem}.wav")
    return send_from_directory(carpeta, mp3.name)


@app.route("/mezcla/<song>", methods=["GET"])
def obtener_mezcla(song):
    """Devuelve el volumen/mute guardado de cada pista para esta canción
    (vacío si todavía no se guardó nada, y el mezclador usa sus valores
    por defecto: 100% y sin mute)."""
    carpeta = stems_dir(song)
    if not carpeta.exists():
        return jsonify({"error": "canción no encontrada"}), 404
    ruta = carpeta / "mezcla.json"
    if not ruta.exists():
        return jsonify({})
    try:
        return jsonify(json.loads(ruta.read_text(encoding="utf-8")))
    except (json.JSONDecodeError, OSError):
        return jsonify({})


@app.route("/mezcla/<song>", methods=["POST"])
def guardar_mezcla(song):
    """Guarda el volumen/mute de cada pista, para recuperarlos la próxima
    vez que se abra esta canción. Se llama sola (con debounce) cada vez que
    el usuario mueve un fader o un mute, no hace falta un botón aparte."""
    carpeta = stems_dir(song)
    if not carpeta.exists():
        return jsonify({"error": "canción no encontrada"}), 404
    datos = request.get_json(silent=True) or {}
    mezcla = {}
    for stem, cfg in datos.items():
        if stem not in STEM_ORDER or not isinstance(cfg, dict):
            continue
        try:
            vol = float(cfg.get("vol", 1.0))
        except (TypeError, ValueError):
            vol = 1.0
        try:
            vol_previo = float(cfg.get("vol_previo", 1.0))
        except (TypeError, ValueError):
            vol_previo = 1.0
        mezcla[stem] = {
            "vol": max(0.0, min(1.0, vol)),
            "muted": bool(cfg.get("muted")),
            # modo guía: la pista queda bajita en vez de muteada, para
            # chequearse contra la grabación mientras se toca encima
            "guia": bool(cfg.get("guia")),
            "vol_previo": max(0.0, min(1.0, vol_previo)),
        }
    escribir_atomico((carpeta / "mezcla.json"), json.dumps(mezcla))
    return jsonify({"ok": True})


@app.route("/acordes/<song>")
def acordes(song):
    """Lee la grilla editable (acordes.txt) si ya existe; si no, analiza guitarra+batería,
    genera esa grilla (agrupada por compás) y la cachea junto a los stems."""
    carpeta = stems_dir(song)
    guitarra = carpeta / "guitar.wav"
    if not guitarra.exists():
        return jsonify({"error": "no hay pista de guitarra para esta canción"}), 404

    txt_path = carpeta / "acordes.txt"
    grid_path = carpeta / "acordes_grid.json"

    if txt_path.exists() and grid_path.exists():
        try:
            grid = json.loads(grid_path.read_text(encoding="utf-8"))
            tokens = _texto_a_tokens(txt_path.read_text(encoding="utf-8"))
            base = grid["beat_times"]

            advertencia = None
            if len(tokens) != len(base):
                advertencia = (
                    f"acordes.txt tiene {len(tokens)} posiciones pero se esperaban {len(base)} — "
                    "revisá que reemplazaste los cambios borrados por un punto (.) en vez de "
                    "borrar la posición entera, o usá \"Regenerar\" para volver a empezar."
                )

            offset = grid.get("offset", 0.0)
            beat_times = [round(t + offset, 3) for t in base]
            segmentos = _tokens_a_segmentos(tokens, beat_times, grid.get("duracion", 0))
            resp = {
                "segmentos": segmentos, "beat_times": beat_times,
                "beats_por_compas": grid.get("beats_por_compas", 4),
                "offset": offset, "bpm": grid.get("bpm"), "capo": grid.get("capo", 0),
            }
            if advertencia:
                resp["advertencia"] = advertencia
            if isinstance(grid.get("coincidencia"), dict):
                resp["coincidencia"] = grid["coincidencia"]   # v103: última comparación detector vs MIDI
            return jsonify(resp)
        except Exception as exc:  # noqa: BLE001
            return jsonify({"error": f"no se pudo leer acordes.txt: {exc}"}), 500

    try:
        segmentos_detectados, detector_usado = detectar_acordes_cancion(carpeta)
        data_dur, sr_dur = _cargar_wav_mono(guitarra)
        duracion = len(data_dur) / sr_dur

        bateria = carpeta / "drums.wav"
        beat_times, _bpm = _detectar_pulso(bateria) if bateria.exists() else ([], 0.0)

        if not beat_times:
            # sin batería o sin pulso claro: se muestra igual, pero sin grilla por compás editable
            return jsonify({"segmentos": segmentos_detectados, "beat_times": [], "beats_por_compas": 4, "offset": 0.0, "bpm": None, "capo": 0})

        fase = _elegir_fase_compas(beat_times, segmentos_detectados)
        beat_times = beat_times[fase:]
        tokens, beat_times = _grid_desde_segmentos(beat_times, segmentos_detectados)

        escribir_atomico(txt_path, _tokens_a_texto(tokens))
        escribir_atomico(
            grid_path,
            json.dumps({"beat_times": beat_times, "beats_por_compas": 4, "bpm": round(_bpm, 1), "duracion": duracion, "offset": 0.0,
                        "detector": detector_usado}),
        )

        segmentos = _tokens_a_segmentos(tokens, beat_times, duracion)
        return jsonify({"segmentos": segmentos, "beat_times": beat_times, "beats_por_compas": 4, "offset": 0.0, "bpm": round(_bpm, 1), "capo": 0})
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": f"no se pudo analizar: {exc}"}), 500


@app.route("/tempo_acordes/<song>", methods=["POST"])
def tempo_acordes(song):
    """Multiplica/divide el tempo detectado por un factor (2.0 o 0.5) y regenera
    toda la grilla a partir de eso — corrige el error clásico de octava de tempo."""
    carpeta = stems_dir(song)
    guitarra = carpeta / "guitar.wav"
    grid_path = carpeta / "acordes_grid.json"
    txt_path = carpeta / "acordes.txt"
    if not guitarra.exists() or not grid_path.exists():
        return jsonify({"error": "no hay grilla para corregir en esta canción"}), 404

    try:
        factor = float((request.get_json(silent=True) or {}).get("factor", 1.0))
        grid_actual = json.loads(grid_path.read_text(encoding="utf-8"))
        base = grid_actual["beat_times"]
        if len(base) < 2:
            return jsonify({"error": "no hay suficientes tiempos detectados para ajustar"}), 400

        if not factor > 0:
            return jsonify({"error": "factor de tempo inválido"}), 400
        # v103: el tiempo se mide con la MEDIANA de la grilla. En una grilla
        # importada de MIDI el primer intervalo es el relleno de entrada y no
        # dura un tiempo real.
        periodo_nuevo = float(np.median(np.diff(base))) / factor
        bpm_nuevo = 60.0 / periodo_nuevo

        segmentos_detectados, detector_usado = detectar_acordes_cancion(carpeta)
        data_dur, sr_dur = _cargar_wav_mono(guitarra)
        duracion = len(data_dur) / sr_dur

        fase_tiempo = base[0] % periodo_nuevo
        n_beats = int(duracion / periodo_nuevo) + 2
        beat_times = [t for t in (fase_tiempo + i * periodo_nuevo for i in range(n_beats)) if t <= duracion]

        fase = _elegir_fase_compas(beat_times, segmentos_detectados)
        beat_times = beat_times[fase:]
        tokens, beat_times = _grid_desde_segmentos(beat_times, segmentos_detectados)

        escribir_atomico(txt_path, _tokens_a_texto(tokens))
        escribir_atomico(
            grid_path,
            # v103: la cejilla y la sincronía son del tema, no del tempo: se
            # conservan. Antes se perdían las dos, y como las marcas de rasgueo
            # se guardan sin el offset, volverlo a 0 las corría de lugar.
            json.dumps({"beat_times": beat_times, "beats_por_compas": 4, "bpm": round(bpm_nuevo, 1), "duracion": duracion,
                        "offset": grid_actual.get("offset", 0.0), "capo": grid_actual.get("capo", 0),
                        "detector": detector_usado}),
        )
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": str(exc)}), 500
    return acordes(song)   # misma respuesta que da la carga normal, leída de lo recién guardado


@app.route("/desfasar_acordes/<song>", methods=["POST"])
def desfasar_acordes(song):
    """Corre el offset de toda la grilla de compases +/- delta segundos (no toca acordes.txt)."""
    grid_path = stems_dir(song) / "acordes_grid.json"
    if not grid_path.exists():
        return jsonify({"error": "no hay grilla de compases para esta canción"}), 404
    try:
        delta = float((request.get_json(silent=True) or {}).get("delta", 0.0))
        with _LOCK_DATOS:   # v112: dos toques seguidos ya no se pisan
            grid = json.loads(grid_path.read_text(encoding="utf-8"))
            grid["offset"] = round(grid.get("offset", 0.0) + delta, 3)
            escribir_atomico(grid_path, json.dumps(grid))
        return jsonify({"offset": grid["offset"]})
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": str(exc)}), 500


@app.route("/regenerar_acordes/<song>", methods=["POST"])
def regenerar_acordes(song):
    """Borra acordes.txt y la grilla, y fuerza un reanálisis completo desde cero.
    v112: la cejilla se conserva (es del tema, igual que al corregir el tempo) y
    las marcas de rasgueo se corren para que sigan en el mismo punto del audio:
    la grilla nueva arranca con sincronía 0."""
    carpeta = stems_dir(song)
    try:
        grid_viejo = json.loads((carpeta / "acordes_grid.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        grid_viejo = {}
    for nombre in ("acordes.txt", "acordes_grid.json"):
        p = carpeta / nombre
        if p.exists():
            try:
                p.unlink()
            except OSError as exc:
                return jsonify({"error": f"no pude borrar {nombre}: {exc}. ¿Lo tenés abierto en el editor? Cerralo e intentá de nuevo."}), 500
    _anclar_marcas_rasgueo(carpeta, grid_viejo.get("offset", 0.0))
    resp = acordes(song)
    capo = grid_viejo.get("capo", 0)
    grid_path = carpeta / "acordes_grid.json"
    if capo and grid_path.exists():
        with _LOCK_DATOS:
            try:
                grid = json.loads(grid_path.read_text(encoding="utf-8"))
                grid["capo"] = capo
                escribir_atomico(grid_path, json.dumps(grid))
            except (OSError, json.JSONDecodeError):
                return resp
        return acordes(song)   # relee lo guardado, ya con la cejilla
    return resp


def _anclar_marcas_rasgueo(carpeta: Path, offset_viejo):
    """v112: las marcas de rasgueo se guardan SIN la sincronía y se muestran
    sumándola. Cuando una grilla nueva reemplaza a la vieja con sincronía 0
    (regenerar, importar MIDI), sin esto las marcas quedaban corridas justo esa
    sincronía. Se les suma la vieja para que caigan en el mismo instante del
    audio que antes. El formato viejo (por posiciones) no se toca."""
    try:
        offset_viejo = float(offset_viejo or 0.0)
    except (TypeError, ValueError):
        return
    if abs(offset_viejo) < 1e-6:
        return
    ruta = carpeta / "rasgueo_marcas.json"
    if not ruta.exists():
        return
    with _LOCK_DATOS:
        try:
            datos = json.loads(ruta.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return
        tiempos = datos.get("tiempos")
        if not isinstance(tiempos, list):
            return
        corridos = []
        for t in tiempos:
            try:
                corridos.append(float(t) + offset_viejo)
            except (TypeError, ValueError):
                continue
        try:
            escribir_atomico(ruta, json.dumps({"tiempos": _limpiar_tiempos(corridos)}))
        except OSError:
            pass


@app.route("/favicon.ico")
def favicon():
    ico = BASE_DIR / "mesa.ico"
    if not ico.exists():
        return ("", 404)
    return send_file(ico, mimetype="image/x-icon")


# --------------------------------------------------------------------------
# PWA: manifest + iconos
#
# Para que Android ofrezca "Instalar app" hace falta un manifest, iconos de
# 192 y 512 px, y que la página se sirva por HTTPS (contexto seguro). El
# HTTPS lo pone `tailscale serve`, que termina el TLS con un certificado
# válido de *.ts.net y proxea a este servidor en 127.0.0.1:5000.
#
# Los iconos se dibujan acá con zlib+struct en vez de guardarse como archivo:
# son tres faders, o sea rectángulos, así que no hace falta ninguna librería
# de imágenes ni acordarse de copiar un .png al lado del script. Si igual
# querés arte propio, dejá `mesa-192.png` / `mesa-512.png` junto a app.py y
# esos ganan.
# --------------------------------------------------------------------------
_ICONO_FONDO = (0x13, 0x13, 0x15)
_ICONO_PISTA = (0x3a, 0x3c, 0x41)
_ICONO_BRASS = (0xe8, 0xb3, 0x4c)
_ICONOS_CACHE = {}


def _png_rgb(tam: int, pixeles: bytearray) -> bytes:
    """Arma un PNG RGB de 8 bits a mano (sin Pillow)."""
    crudo = bytearray()
    for y in range(tam):
        crudo.append(0)                      # filtro 0 = sin filtrar
        crudo += pixeles[y * tam * 3:(y + 1) * tam * 3]

    def bloque(tipo, datos):
        return (struct.pack(">I", len(datos)) + tipo + datos
                + struct.pack(">I", zlib.crc32(tipo + datos) & 0xFFFFFFFF))

    ihdr = struct.pack(">IIBBBBB", tam, tam, 8, 2, 0, 0, 0)
    return (b"\x89PNG\r\n\x1a\n" + bloque(b"IHDR", ihdr)
            + bloque(b"IDAT", zlib.compress(bytes(crudo), 9)) + bloque(b"IEND", b""))


def _dibujar_icono(tam: int) -> bytes:
    """Tres faders sobre fondo oscuro. Las medidas están en porcentaje del
    lado para que el dibujo entre en la zona segura de un icono maskable
    (el círculo central del 80%): si se saliera, Android le corta las puntas."""
    px = bytearray(bytes(_ICONO_FONDO) * (tam * tam))

    def rect(x0, y0, x1, y1, color):
        x0, x1 = max(0, int(x0)), min(tam, int(x1))
        if x1 <= x0:
            return
        for y in range(max(0, int(y0)), min(tam, int(y1))):
            f = y * tam * 3
            px[f + x0 * 3:f + x1 * 3] = bytes(color) * (x1 - x0)

    u = tam / 100.0
    alto = 52 * u
    arriba = (tam - alto) / 2
    ancho_pista = max(2, round(6 * u))
    ancho_cap = round(17 * u)
    alto_cap = max(3, round(6 * u))
    sep = 20 * u
    for cx, pos in zip((tam / 2 - sep, tam / 2, tam / 2 + sep), (0.62, 0.28, 0.48)):
        rect(cx - ancho_pista / 2, arriba, cx + ancho_pista / 2, arriba + alto, _ICONO_PISTA)
        y = arriba + pos * (alto - alto_cap)
        rect(cx - ancho_cap / 2, y, cx + ancho_cap / 2, y + alto_cap, _ICONO_BRASS)
    return _png_rgb(tam, px)


def version_iconos() -> str:
    """v103: marca que cambia cada vez que se reemplazan los íconos propios
    (fecha de modificación del más nuevo). Va como "?v=" en el manifest y en
    los <link> de la página: así el navegador ve una dirección nueva y no
    puede seguir usando la imagen vieja que tenga guardada."""
    marcas = []
    for nombre in ("mesa-192.png", "mesa-512.png", "mesa.ico"):
        try:
            marcas.append(int((BASE_DIR / nombre).stat().st_mtime))
        except OSError:
            pass
    return str(max(marcas)) if marcas else "0"


@app.context_processor
def _inyectar_version_iconos():
    return {"version_iconos": version_iconos()}


# v106: color base de la app (Ajustes generales). Se inyecta en TODAS las
# páginas porque BASE_STYLE lo aplica antes de pintar; vacío = paleta original.
_RE_COLOR_BASE = re.compile(r"^#[0-9a-f]{6}$")


def color_base_actual():
    valor = str(leer_prefs().get("color_base") or "").strip().lower()
    # "mono" = blanco y negro, el estilo de app103 (ver mesaColorBase)
    return valor if (valor == "mono" or _RE_COLOR_BASE.match(valor)) else ""


@app.context_processor
def _inyectar_color_base():
    return {"color_base": color_base_actual()}


@app.context_processor
def _inyectar_detector():
    # v109: estado del detector aprendido para el panel de Ajustes generales
    return {"detector_aprendido": bool(leer_prefs().get("detector_aprendido", True)),
            "modelo_info": info_modelo_acordes()}


@app.route("/icono-<int:tam>.png")
def icono(tam):
    # v103: "no-cache" en vez de un día de caché. Con max-age=86400 el celular
    # seguía mostrando el ícono viejo aunque se reinstalara la app: la copia
    # vive en la caché de Chrome, no en la app. Son unos KB: revalidar no cuesta.
    if tam not in (192, 512):
        return ("", 404)
    propio = BASE_DIR / f"mesa-{tam}.png"
    if propio.exists():
        resp = send_file(propio, mimetype="image/png")
        resp.headers["Cache-Control"] = "no-cache"
        return resp
    if tam not in _ICONOS_CACHE:
        _ICONOS_CACHE[tam] = _dibujar_icono(tam)
    return Response(_ICONOS_CACHE[tam], mimetype="image/png",
                    headers={"Cache-Control": "no-cache"})


@app.route("/manifest.webmanifest")
def manifest():
    v = version_iconos()
    datos = {
        "id": "/",
        "name": "Mesa — separador de pistas",
        "short_name": "Mesa",
        "description": "Separa las pistas de un tema y tocá encima con los acordes sincronizados.",
        "lang": "es",
        "start_url": "/",
        "scope": "/",
        # fullscreen = sin barra de direcciones NI barra de estado de Android
        # (reloj, batería, notificaciones): pantalla completa de verdad para
        # el atril. Si en algún dispositivo Android la ignora, cae solo a
        # "standalone" (sin barra de direcciones, con la barra de estado).
        "display": "fullscreen",
        "display_override": ["fullscreen", "standalone"],
        "orientation": "any",
        "background_color": "#0E0E11",
        "theme_color": "#0E0E11",
        "icons": [
            # v103: la "?v=" cambia al reemplazar los íconos; para Chrome es
            # un ícono nuevo y actualiza el de la app instalada
            {"src": f"/icono-192.png?v={v}", "sizes": "192x192", "type": "image/png", "purpose": "any"},
            {"src": f"/icono-512.png?v={v}", "sizes": "512x512", "type": "image/png", "purpose": "any"},
            {"src": f"/icono-512.png?v={v}", "sizes": "512x512", "type": "image/png", "purpose": "maskable"},
        ],
    }
    return Response(json.dumps(datos, ensure_ascii=False),
                    mimetype="application/manifest+json")


# Service worker: instalable (requisito de Android/Chrome) + sirve desde
# caché lo que el usuario descargó a propósito con "Descargar para tocar sin
# wifi". Dos estrategias distintas según qué es cada cosa:
#   - audio (los stems al 100%): "cache primero" -- el contenido no cambia
#     una vez separado, así que si ya está descargado no tiene sentido
#     volver a pedirlo por la red cada vez que se toca.
#   - la página de la mesa + los datos que necesita al cargar (acordes,
#     mezcla) + la portada: "red primero, caché como respaldo" -- si hay
#     conexión siempre se ve la versión real y actualizada; el caché solo
#     entra cuando la red falla, con lo último que se guardó al descargar.
# Ninguna de las dos cachea nada por su cuenta en cada visita: lo único que
# llena el caché es el botón de descarga (ver mesaOffline en BASE_STYLE).
SW_JS = """
const CACHE_AUDIO = "mesa-audio-v1";
const TIMEOUT_RED = 2500;          // ms que le damos a la red antes de usar el caché
const CLAVE_ESTADO = "/__estado_red";   // marca persistente de "la red no está"

const RE_AUDIO = /^\\/audio\\/[^/]+\\/[^/.]+\\.mp3$/;
const RE_MESA = /^\\/mesa\\/[^/]+$/;
const RE_SETLIST = /^\\/setlist\\/[^/]+$/;
const RE_ACORDES = /^\\/acordes\\/[^/]+$/;
const RE_MEZCLA = /^\\/mezcla\\/[^/]+$/;
const RE_RASGUEO = /^\\/rasgueo\\/[^/]+$/;

function esEstatico(pathname){
  return pathname === "/manifest.webmanifest" || pathname === "/icono-192.png" || pathname === "/icono-512.png";
}
function esCascaronDePagina(pathname){
  return pathname === "/" || RE_MESA.test(pathname) || RE_SETLIST.test(pathname)
    || RE_ACORDES.test(pathname) || RE_MEZCLA.test(pathname) || RE_RASGUEO.test(pathname) || esEstatico(pathname);
}

// Clave con la que se guarda una página. "/mesa/<song>" y
// "/mesa/<song>?setlist=<id>" son páginas DISTINTAS (la segunda trae los
// botones Anterior/Siguiente), así que el setlist forma parte de la clave.
// Cualquier otro parámetro ("&autoplay=1" al encadenar temas) se descarta:
// no cambia el HTML y duplicaría entradas. Tiene que dar exactamente la
// misma cadena que arma el servidor en urls_offline_cancion.
function claveDePagina(url){
  const sl = url.searchParams.get("setlist");
  return url.pathname + (sl ? "?setlist=" + encodeURIComponent(sl) : "");
}

// Sin esto, "sin conexión" no significa que el fetch falle: con wifi pero sin
// ruta hasta la PC (Tailscale caído, otra red), el pedido queda colgado hasta
// el timeout de TCP del sistema -- 30 a 90 segundos. Como la página espera esas
// respuestas para arrancar, se ve congelada en vez de abrir del caché.
// No abortamos el fetch (que siga si quiere): simplemente dejamos de esperarlo.
function conTope(promesa, ms){
  return new Promise((resolve, reject) => {
    const t = setTimeout(() => reject(new Error("timeout")), ms);
    promesa.then(
      (r) => { clearTimeout(t); resolve(r); },
      (e) => { clearTimeout(t); reject(e); }
    );
  });
}

// --- estado de la red -------------------------------------------------------
// Pagar TIMEOUT_RED una vez está bien; pagarlo en cada pedido del arranque
// (página + acordes + mezcla) son 5 segundos por canción. Así que en cuanto un
// pedido se cae, queda anotado y los siguientes van derecho al caché.
// El navegador mata al service worker por inactividad y se lleva las variables,
// así que la marca también va al caché: leerla de ahí es ~1 ms, muchísimo menos
// que un timeout.
let redCaida = false;      // espejo en memoria, para no ir al caché cada vez
let estadoLeido = false;
let ultimoAvisado = null;  // para no spamear a las páginas con el mismo estado

async function redEstaCaida(cache){
  if(estadoLeido) return redCaida;
  try{ redCaida = !!(await cache.match(CLAVE_ESTADO)); }catch(e){ redCaida = false; }
  estadoLeido = true;
  return redCaida;
}
async function anotarRedCaida(cache){
  redCaida = true; estadoLeido = true;
  try{ await cache.put(CLAVE_ESTADO, new Response("1")); }catch(e){}
  avisar("offline");
}
async function anotarRedOk(cache){
  // sin este chequeo, cada arranque normal avisaría "conexión recuperada"
  // aunque nunca se hubiera caído nada
  const veniaCaida = await redEstaCaida(cache);
  redCaida = false; estadoLeido = true;
  if(!veniaCaida) return;
  try{ await cache.delete(CLAVE_ESTADO); }catch(e){}
  avisar("online");
}

function avisar(estado){
  if(estado === ultimoAvisado) return;
  ultimoAvisado = estado;
  self.clients.matchAll({ type: "window" })
    .then((cs) => cs.forEach((c) => c.postMessage({ tipo: "mesa-red", estado })))
    .catch(() => {});
}

// Mientras la red está caída contestamos del caché al instante, pero probamos
// por atrás: si volvió, se limpia la marca Y se actualiza la copia guardada,
// así la próxima carga ya sale fresca. Sin este sondeo la app se quedaría
// pegada al caché para siempre.
async function sondear(cache, req){
  try{
    const resp = await conTope(fetch(req), TIMEOUT_RED);
    if(!resp) return;
    await anotarRedOk(cache);   // llegamos al servidor; hasta un 500 cuenta
    if(!resp.ok) return;
    await refrescarCopia(cache, req, resp);
  }catch(e){ /* sigue sin red: la marca queda como estaba */ }
}

// Actualiza la copia offline con lo que acaba de contestar el servidor. Solo
// pisa entradas que YA existen: el caché no crece solo, lo llena el botón de
// descarga. Única excepción: la variante "?setlist=<id>" de una mesa que YA
// está descargada -- si abrís desde un setlist nuevo un tema que ya bajaste,
// esa página (unos KB) se guarda para que offline conserve Anterior/Siguiente.
// Corre en CADA respuesta buena, no solo al recuperarse de un corte: si no,
// la página guardada se queda con el HTML de la versión de la app que estaba
// el día que se descargó, y offline abrís una app vieja.
async function refrescarCopia(cache, req, resp){
  if(!resp || !resp.ok) return;
  try{
    const url = new URL(req.url);
    const clave = claveDePagina(url);
    if(await cache.match(clave)){ await cache.put(clave, resp.clone()); return; }
    if(RE_MESA.test(url.pathname) && url.searchParams.get("setlist") && await cache.match(url.pathname)){
      await cache.put(clave, resp.clone());
    }
  }catch(e){}
}

self.addEventListener("install", (event) => {
  self.skipWaiting();
  event.waitUntil(
    caches.open(CACHE_AUDIO)
      .then((cache) => cache.addAll(["/manifest.webmanifest", "/icono-192.png", "/icono-512.png"]))
      .catch(() => {})
  );
});
self.addEventListener("activate", (e) => { e.waitUntil(self.clients.claim()); });

self.addEventListener("fetch", (event) => {
  const req = event.request;
  if(req.method !== "GET") return;   // POST (mute, tempo, borrar...) pasa sin tocarse
  const url = new URL(req.url);

  // El latido no se cachea nunca: su única razón de ser es fallar cuando no
  // hay red. Pasa por acá y no derecho a la red para que el resultado alimente
  // el mismo estado que usa todo lo demás -- así, cuando pasás a la canción
  // siguiente, el cortacircuito ya está decidido y la carga es instantánea.
  if(url.pathname === "/ping"){
    event.respondWith((async () => {
      const cache = await caches.open(CACHE_AUDIO);
      try{
        const resp = await conTope(fetch(req), TIMEOUT_RED);
        await anotarRedOk(cache);
        return resp;
      }catch(e){
        await anotarRedCaida(cache);
        return new Response("sin red", { status: 503 });
      }
    })());
    return;
  }

  // audio a velocidad normal (nunca el "?t=" de otras velocidades, que se
  // generan al vuelo y no se guardan offline): cache primero
  if(RE_AUDIO.test(url.pathname) && !url.search){
    event.respondWith(
      caches.open(CACHE_AUDIO).then(async (cache) => {
        const cacheado = await cache.match(req);
        return cacheado || fetch(req);
      })
    );
    return;
  }

  // portada, mesa de una canción, y los datos que esa página pide al cargar.
  // ignoreSearch porque "/mesa/<song>" puede llegar con "?setlist=..." y lo
  // que se guardó al descargar fue la versión sin parámetros.
  if(esCascaronDePagina(url.pathname)){
    event.respondWith((async () => {
      const cache = await caches.open(CACHE_AUDIO);
      // primero la variante exacta (con su setlist); si no está, cualquier
      // copia de la misma ruta sirve para no quedarse sin página
      const cacheado = (await cache.match(claveDePagina(url))) || (await cache.match(req, { ignoreSearch: true }));

      // ya sabemos que no hay red y tenemos copia: cero espera
      if(cacheado && await redEstaCaida(cache)){
        avisar("offline");
        event.waitUntil(sondear(cache, req));
        return cacheado;
      }

      try{
        // con copia guardada le damos a la red TIMEOUT_RED y listo; sin copia
        // no hay nada mejor que esperarla (primera visita, conexión lenta)
        const resp = await (cacheado ? conTope(fetch(req), TIMEOUT_RED) : fetch(req));
        await anotarRedOk(cache);
        if(cacheado) await refrescarCopia(cache, req, resp);
        return resp;
      }catch(e){
        await anotarRedCaida(cache);
        return cacheado || Response.error();
      }
    })());
  }
});
"""


BLE_TEST_HTML = """<!doctype html>
<html lang="es"><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Prueba BLE - Mesa</title>
<style>
  body{ background:#000; color:#fff; font:14px -apple-system,"Segoe UI",Roboto,sans-serif;
        margin:0; padding:16px; }
  h1{ font-size:16px; margin:0 0 12px; }
  button{ display:block; width:100%; margin:0 0 10px; padding:14px; font-size:15px;
          background:#fff; color:#000; border:0; border-radius:8px; font-weight:600; }
  button.sec{ background:#191919; color:#fff; border:1px solid #333; font-weight:500; }
  #log{ background:#000; color:#0f0; font:11px/1.5 monospace; padding:10px;
        border-radius:8px; word-break:break-word; min-height:220px; }
  #log div{ margin:0 0 2px; }
</style>
<h1>Prueba de Bluetooth &mdash; Mesa</h1>
<button id="b1">1. Buscar solo MesaHUD</button>
<button id="b2" class="sec">2. Ver TODOS los dispositivos BLE</button>
<button id="b3" class="sec">3. Mandar un acorde de prueba</button>
<div id="log"></div>
<script>
const SERV = "6e6d0001-b5a3-f393-e0a9-e50e24dcca9e";
const CAR  = "6e6d0002-b5a3-f393-e0a9-e50e24dcca9e";
const elLog = document.getElementById("log");
let caract = null;

function log(m){
  const d = document.createElement("div");
  d.textContent = m;
  elLog.appendChild(d);
  elLog.scrollTop = elLog.scrollHeight;
}

window.addEventListener("error", (e) => log("ERROR JS: " + e.message + " @ linea " + e.lineno));

log("Web Bluetooth: " + (navigator.bluetooth ? "SI" : "NO, este navegador no lo soporta"));
log("contexto seguro (https): " + window.isSecureContext);
log("origen: " + location.origin);
log("app instalada: " + (window.matchMedia("(display-mode: standalone)").matches
    || window.matchMedia("(display-mode: fullscreen)").matches ? "SI" : "no, pestana normal"));
if(navigator.bluetooth && navigator.bluetooth.getAvailability){
  navigator.bluetooth.getAvailability().then(v => log("adaptador BT disponible: " + (v ? "SI" : "NO, prende el Bluetooth")));
}
log("---");

async function conectar(opciones){
  if(!navigator.bluetooth){ log("ABORTADO: no hay navigator.bluetooth"); return; }
  try{
    log("pidiendo dispositivo...");
    const d = await navigator.bluetooth.requestDevice(opciones);
    log("elegido: " + (d.name || "(sin nombre)"));
    log("conectando GATT...");
    const s = await d.gatt.connect();
    log("GATT conectado");
    const srv = await s.getPrimaryService(SERV);
    log("servicio ok");
    caract = await srv.getCharacteristic(CAR);
    log("caracteristica ok. LISTO, proba el boton 3");
  }catch(e){
    log("ERROR " + e.name + ": " + e.message);
    if(e.name === "NotFoundError"){
      log("  NotFoundError = cancelaste el selector, O el Bluetooth esta apagado,");
      log("  O Chrome no tiene permiso de Ubicacion, O ninguna placa coincide.");
    }
    if(e.name === "SecurityError") log("  la pagina no esta en contexto seguro");
  }
}

document.getElementById("b1").onclick = () => conectar({
  filters: [{ name: "MesaHUD" }], optionalServices: [SERV],
});
document.getElementById("b2").onclick = () => conectar({
  acceptAllDevices: true, optionalServices: [SERV],
});
document.getElementById("b3").onclick = async () => {
  if(!caract){ log("todavia no hay conexion: usa el boton 1 o 2"); return; }
  try{
    const payload = JSON.stringify({ c: "Am", n: "F", d: 2.0, b: 0, i: 0 });
    await caract.writeValueWithoutResponse(new TextEncoder().encode(payload));
    log("enviado: " + payload + " (" + payload.length + " bytes)");
    log("  si en las gafas no aparece Am, mira el Serial del ESP32");
  }catch(e){ log("ERROR al escribir " + e.name + ": " + e.message); }
};
</script>
</html>"""


@app.route("/ble_test")
def ble_test():
    """Página suelta para probar Web Bluetooth desde el celular, sin el resto
    de Mesa cargando alrededor: separa un problema del dispositivo de un bug
    en el script grande de la mesa. No se cachea nunca."""
    return Response(BLE_TEST_HTML, mimetype="text/html",
                    headers={"Cache-Control": "no-store"})


@app.route("/ping")
def ping():
    """Latido: lo más chico que se puede contestar. La página lo pide cada 20 s
    y es lo único que hace que un corte de conexión se note MIENTRAS tocás --
    con la mesa abierta y el audio ya cargado, la app no pide nada más, así que
    sin esto no hay ningún pedido que pueda fallar y avisar."""
    return Response("ok", mimetype="text/plain",
                    headers={"Cache-Control": "no-store"})


@app.route("/sw.js")
def service_worker():
    return Response(SW_JS, mimetype="application/javascript",
                     headers={"Cache-Control": "no-cache"})


@app.route("/importar_midi/<song>", methods=["POST"])
def importar_midi(song):
    """Reemplaza los acordes de la canción con los de un MIDI (ej. de Chordify).
    Genera la misma grilla de compases que usa el resto de la app, así que el
    editor, la cejilla y los diagramas siguen funcionando igual."""
    carpeta = stems_dir(song)
    guitarra = carpeta / "guitar.wav"
    if not guitarra.exists():
        return jsonify({"error": "esta canción todavía no está separada"}), 404

    archivo = request.files.get("midi")
    if not archivo or not archivo.filename:
        return jsonify({"error": "no recibí ningún archivo"}), 400

    with tempfile.TemporaryDirectory() as tmp:
        # v112: un nombre sin letras ASCII queda vacío y se guardaba sobre la carpeta
        destino = Path(tmp) / (secure_filename(archivo.filename) or "acordes.mid")
        archivo.save(destino)
        try:
            segmentos, bpm, simplificados = leer_acordes_midi(destino)
        except ImportError:
            return jsonify({"error": "falta la librería mido. Instalá con: pip install mido"}), 500
        except Exception as exc:  # noqa: BLE001
            return jsonify({"error": f"no pude leer el MIDI: {exc}"}), 400

    if not segmentos:
        return jsonify({"error": "el MIDI no tiene acordes reconocibles"}), 400

    data, sr = _cargar_wav_mono(guitarra)
    duracion = len(data) / sr

    # La grilla se ancla a los cambios de acorde reales del MIDI en vez de imponer
    # un tempo constante: así cada cambio cae exactamente en un tiempo y no se
    # acumula deriva a lo largo de la canción (el tempo real nunca es perfecto).
    paso = 60.0 / bpm

    # El tempo declarado en el MIDI no siempre coincide con el que se desprende de
    # los acordes (en el de prueba decía 115 pero los acordes daban ~117.6). Se
    # refina el paso con la duración típica de acorde, que casi siempre es un
    # número entero de tiempos; si no, los compases nunca terminan de alinear.
    duraciones = sorted(s["fin"] - s["inicio"] for s in segmentos)
    if duraciones:
        mediana = duraciones[len(duraciones) // 2]
        n_beats = round(mediana / paso)
        if n_beats >= 1:
            candidato = mediana / n_beats
            if abs(candidato - paso) / paso < 0.12:   # solo ajustes chicos
                paso = candidato
                bpm = 60.0 / paso
    compas = paso * 4

    beat_times, tokens = [], []
    anterior = None

    def agregar_tramo(desde, hasta, acorde, minimo=1):
        nonlocal anterior
        n = max(minimo, int(round((hasta - desde) / paso)))
        if n <= 0:
            return
        ancho = (hasta - desde) / n
        for k in range(n):
            beat_times.append(round(desde + k * ancho, 3))
            tokens.append("." if (k > 0 or acorde == anterior) else acorde)
        anterior = acorde

    # relleno antes del primer acorde, en compases completos para que el primer
    # acorde caiga en el tiempo 1
    primer = segmentos[0]["inicio"]
    if primer > paso / 2:
        n_compases = max(1, int(round(primer / compas)))
        agregar_tramo(max(0.0, primer - n_compases * compas), primer, "—", minimo=n_compases * 4)

    for i, s in enumerate(segmentos):
        agregar_tramo(s["inicio"], s["fin"], s["acorde"])
        # hueco hasta el próximo acorde (silencio armónico)
        prox = segmentos[i + 1]["inicio"] if i + 1 < len(segmentos) else None
        if prox is not None and prox - s["fin"] > paso / 2:
            agregar_tramo(s["fin"], prox, "—")

    # cola hasta el final del audio
    ultimo_fin = segmentos[-1]["fin"]
    if duracion - ultimo_fin > paso / 2:
        agregar_tramo(ultimo_fin, duracion, "—")

    if not beat_times:
        return jsonify({"error": "no pude armar la grilla de compases"}), 400

    sobra = len(tokens) % 4
    if sobra:
        tokens, beat_times = tokens[:-sobra], beat_times[:-sobra]

    escribir_atomico((carpeta / "acordes.txt"), _tokens_a_texto(tokens))
    grid_previo = {}
    grid_path = carpeta / "acordes_grid.json"
    if grid_path.exists():
        try:
            grid_previo = json.loads(grid_path.read_text(encoding="utf-8"))
        except Exception:  # noqa: BLE001
            grid_previo = {}
    escribir_atomico(grid_path, json.dumps({
        "beat_times": beat_times, "beats_por_compas": 4,
        "bpm": round(bpm, 1), "duracion": duracion, "offset": 0.0,
        "capo": grid_previo.get("capo", 0), "origen": "midi",
    }))
    _anclar_marcas_rasgueo(carpeta, grid_previo.get("offset", 0.0))   # v112
    # v103: los acordes del MIDI tal como vinieron (en segundos, antes de la
    # grilla), para poder comparar el detector contra ellos cuando haga falta.
    try:
        escribir_atomico(carpeta / "acordes_midi.json",
                         json.dumps({"segmentos": segmentos, "bpm": round(bpm, 1)}))
    except OSError:
        pass   # la comparación es un extra: no rompe la importación

    resumen = {}
    for s in simplificados:
        resumen[s] = resumen.get(s, 0) + 1
    return jsonify({
        "ok": True, "bpm": round(bpm, 1), "acordes": len(segmentos),
        "simplificados": [f"{k} ({v}×)" for k, v in sorted(resumen.items(), key=lambda x: -x[1])],
    })


# ------------------- v103: coincidencia detector vs MIDI -------------------
# Cuánto se parece lo que detecta Mesa a los acordes de un MIDI importado
# (Chordify). Es la misma idea que lab_acordes.py, pero por tema y desde la
# app. Se mide en TIEMPO: de todos los instantes en que el MIDI tiene un
# acorde, en qué porcentaje el detector dice lo mismo. Tres niveles:
#   - raíz:   misma fundamental (C, Cm y C7 cuentan igual)
#   - tríada: misma fundamental y mismo modo mayor/menor (C y C7 cuentan igual)
#   - exacta: mismo acorde en el vocabulario del detector (C7 != C; el maj7 y
#             el sus4 del MIDI se toman como mayor, porque el detector no los
#             propone)
# Los silencios del MIDI no se cuentan; un silencio del detector donde el MIDI
# tiene acorde cuenta como error.

def _raiz_y_sufijo(acorde):
    """(clase de altura, sufijo) de un acorde, o None si es silencio/desconocido."""
    if not acorde or acorde in (".", "—"):
        return None
    norm, ok = normalizar_token(acorde)
    if not ok or norm in (".", "—"):
        return None
    raiz = norm[:2] if norm[:2] in NOTE_NAMES else norm[:1]
    return NOTE_NAMES.index(raiz), norm[len(raiz):]


def _acorde_en_instantes(segmentos, tiempos):
    """El acorde que rige en cada instante (None donde no hay ninguno)."""
    if not segmentos:
        return [None] * len(tiempos)
    orden = sorted(segmentos, key=lambda s: s["inicio"])
    inicios = np.array([s["inicio"] for s in orden])
    idx = np.searchsorted(inicios, tiempos, side="right") - 1
    return [orden[i]["acorde"] if i >= 0 and t < orden[i]["fin"] else None
            for t, i in zip(tiempos, idx)]


def _comparar_acordes(referencia, detectados, duracion, paso=0.05):
    """Compara dos listas de segmentos muestreando cada `paso` segundos.
    Devuelve None si la referencia no tiene ningún acorde dentro del tema."""
    tiempos = np.arange(0.0, max(0.0, duracion), paso)
    ref = _acorde_en_instantes(referencia, tiempos)
    det = _acorde_en_instantes(detectados, tiempos)
    total = exacta = triada = raiz = 0
    confusiones = {}
    for a_ref, a_det in zip(ref, det):
        r = _raiz_y_sufijo(a_ref)
        if r is None:
            continue
        total += 1
        d = _raiz_y_sufijo(a_det)
        nombre_ref = NOTE_NAMES[r[0]] + ("m" if r[1] == "m" else "")
        nombre_det = (NOTE_NAMES[d[0]] + ("m" if d[1] == "m" else "")) if d else "—"
        if d and d[0] == r[0]:
            raiz += 1
        if nombre_ref == nombre_det:
            triada += 1
            if ("" if r[1] in ("maj7", "sus4") else r[1]) == d[1]:
                exacta += 1
        else:
            clave = (nombre_ref, nombre_det)
            confusiones[clave] = confusiones.get(clave, 0) + 1
    if not total:
        return None
    peores = sorted(confusiones.items(), key=lambda x: -x[1])[:5]
    return {
        "raiz": round(100.0 * raiz / total, 1),
        "triada": round(100.0 * triada / total, 1),
        "exacta": round(100.0 * exacta / total, 1),
        "segundos": round(total * paso, 1),
        "confusiones": [{"midi": a, "detector": b, "segundos": round(n * paso, 1)} for (a, b), n in peores],
    }


@app.route("/comparar_detector/<song>", methods=["POST"])
def comparar_detector(song):
    """Corre el detector propio sobre los stems y lo mide contra los acordes
    del MIDI importado. No toca acordes.txt: solo anota el resultado en la
    grilla para mostrarlo sin tener que recalcular."""
    carpeta = stems_dir(song)
    guitarra = carpeta / "guitar.wav"
    if not guitarra.exists():
        return jsonify({"error": "esta canción todavía no está separada"}), 404

    grid_path = carpeta / "acordes_grid.json"
    txt_path = carpeta / "acordes.txt"
    midi_path = carpeta / "acordes_midi.json"
    try:
        grid = json.loads(grid_path.read_text(encoding="utf-8")) if grid_path.exists() else {}
    except (json.JSONDecodeError, OSError):
        grid = {}
    es_midi = grid.get("origen") == "midi"

    referencia, fuente = None, None
    if midi_path.exists():
        try:
            referencia = json.loads(midi_path.read_text(encoding="utf-8")).get("segmentos")
            fuente = "midi"
        except (json.JSONDecodeError, OSError):
            referencia = None
    if not referencia and es_midi and txt_path.exists():
        # importado con una versión anterior (no quedó el MIDI guardado): se
        # usa la grilla actual, que son esos acordes más lo corregido a mano
        try:
            tokens = _texto_a_tokens(txt_path.read_text(encoding="utf-8"))
            referencia = _tokens_a_segmentos(tokens, grid["beat_times"], grid.get("duracion", 0))
            fuente = "grilla"
        except Exception:  # noqa: BLE001
            referencia = None
    if not referencia:
        return jsonify({"error": "esta canción no tiene acordes importados de un MIDI contra los que comparar"}), 404

    # si la grilla sigue siendo la del MIDI, su sincronía (offset) es justo lo
    # que alinea el MIDI con el audio: se aplica a la referencia
    try:
        corrimiento = float(grid.get("offset", 0.0)) if es_midi else 0.0
    except (TypeError, ValueError):
        corrimiento = 0.0
    try:
        referencia = [{"inicio": float(s["inicio"]) + corrimiento, "fin": float(s["fin"]) + corrimiento,
                       "acorde": s["acorde"]} for s in referencia]
        detectados = detectar_acordes(
            guitarra, bajo_path=carpeta / "bass.wav",
            stems_extra=[carpeta / "piano.wav", carpeta / "other.wav"])
        duracion_cmp = detectados[-1]["fin"]
        resultado = _comparar_acordes(referencia, detectados, duracion_cmp)
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": f"no se pudo comparar: {exc}"}), 500
    if resultado is None:
        return jsonify({"error": "el MIDI no tiene acordes dentro de la duración del tema"}), 400
    resultado["referencia"] = fuente

    # v109: el detector aprendido, medido igual y sobre la misma duración. Los campos
    # de arriba siguen siendo los del de plantillas (así lo guardado antes se lee igual).
    modelo = modelo_acordes()
    if modelo is not None:
        try:
            det_ml = detectar_acordes_ml(guitarra, modelo, bajo_path=carpeta / "bass.wav",
                                         stems_extra=[carpeta / "piano.wav", carpeta / "other.wav"])
            r_ml = _comparar_acordes(referencia, det_ml, duracion_cmp)
            if r_ml is not None:
                entreno = (getattr(modelo, "meta", {}) or {}).get("temas_entrenamiento") or []
                r_ml["entrenado_con_este"] = song in entreno
                resultado["aprendido"] = r_ml
        except Exception as exc:  # noqa: BLE001
            resultado["aprendido_error"] = str(exc)
    resultado["calculado"] = datetime.now().strftime("%Y-%m-%d %H:%M")

    # se relee la grilla antes de anotar: el análisis tarda unos segundos y en
    # el medio pudo cambiar la sincronía o la cejilla
    with _LOCK_DATOS:
        try:
            if grid_path.exists():
                actual = json.loads(grid_path.read_text(encoding="utf-8"))
                actual["coincidencia"] = resultado
                escribir_atomico(grid_path, json.dumps(actual))
        except (json.JSONDecodeError, OSError):
            pass   # no se pudo anotar: el resultado se muestra igual
    return jsonify(resultado)


@app.route("/capo/<song>", methods=["POST"])
def fijar_capo(song):
    """Guarda el traste de cejilla elegido (solo visualización, no toca el audio)."""
    grid_path = stems_dir(song) / "acordes_grid.json"
    if not grid_path.exists():
        return jsonify({"error": "esta canción todavía no tiene grilla de acordes"}), 404
    try:
        capo = int((request.get_json(silent=True) or {}).get("capo", 0))
        capo = max(0, min(11, capo))
        with _LOCK_DATOS:   # v112
            grid = json.loads(grid_path.read_text(encoding="utf-8"))
            grid["capo"] = capo
            escribir_atomico(grid_path, json.dumps(grid))
        return jsonify({"capo": capo})
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": str(exc)}), 500


@app.route("/sugerir_capo/<song>", methods=["GET"])
def sugerir_capo_endpoint(song):
    """Calcula en qué traste conviene poner la cejilla para esta canción."""
    carpeta = stems_dir(song)
    txt_path = carpeta / "acordes.txt"
    grid_path = carpeta / "acordes_grid.json"
    if not txt_path.exists() or not grid_path.exists():
        return jsonify({"error": "esta canción todavía no tiene grilla de acordes"}), 404
    try:
        grid = json.loads(grid_path.read_text(encoding="utf-8"))
        tokens = _texto_a_tokens(txt_path.read_text(encoding="utf-8"))
        segmentos = _tokens_a_segmentos(tokens, grid["beat_times"], grid.get("duracion", 0))
        mejor, ranking = sugerir_capo(segmentos)
        return jsonify({"capo": mejor, "ranking": ranking})
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": str(exc)}), 500


@app.route("/grilla/<song>", methods=["GET"])
def obtener_grilla(song):
    """Tokens crudos por compás + el tiempo en que arranca cada compás (para
    poder saltar el audio ahí desde el editor)."""
    carpeta = stems_dir(song)
    txt_path = carpeta / "acordes.txt"
    grid_path = carpeta / "acordes_grid.json"
    if not txt_path.exists() or not grid_path.exists():
        return jsonify({"error": "esta canción todavía no tiene grilla de acordes"}), 404

    grid = json.loads(grid_path.read_text(encoding="utf-8"))
    tokens = _texto_a_tokens(txt_path.read_text(encoding="utf-8"))
    bpc = grid.get("beats_por_compas", 4)
    offset = grid.get("offset", 0.0)
    base = grid["beat_times"]

    compases = []
    for i in range(0, len(tokens), bpc):
        idx_beat = i
        inicio = round(base[idx_beat] + offset, 3) if idx_beat < len(base) else None
        compases.append({"tokens": tokens[i:i + bpc], "inicio": inicio})

    return jsonify({
        "compases": compases,
        "beats_por_compas": bpc,
        "vocabulario": _vocabulario_completo(),
        "posiciones_esperadas": len(base),
        # tiempos crudos (sin offset): el editor los necesita para traducir
        # entre la celda que tocás y el tiempo con el que se guardan las
        # marcas de rasgueo
        "beat_times": base,
        "offset": offset,
    })


@app.route("/grilla/<song>", methods=["POST"])
def guardar_grilla(song):
    """Guarda los tokens editados en acordes.txt (valida contra el vocabulario)."""
    carpeta = stems_dir(song)
    txt_path = carpeta / "acordes.txt"
    grid_path = carpeta / "acordes_grid.json"
    if not grid_path.exists():
        return jsonify({"error": "esta canción todavía no tiene grilla de acordes"}), 404

    datos = request.get_json(silent=True) or {}
    tokens_in = datos.get("tokens")
    if not isinstance(tokens_in, list) or not tokens_in:
        return jsonify({"error": "no recibí la lista de acordes"}), 400

    grid = json.loads(grid_path.read_text(encoding="utf-8"))
    esperadas = len(grid["beat_times"])
    if len(tokens_in) != esperadas:
        return jsonify({"error": f"llegaron {len(tokens_in)} posiciones y se esperaban {esperadas}"}), 400

    normalizados, invalidos = [], []
    for i, t in enumerate(tokens_in):
        norm, ok = normalizar_token(t)
        if not ok:
            invalidos.append({"indice": i, "valor": t})
        normalizados.append(norm)

    if invalidos:
        detalle = ", ".join(f"«{x['valor']}»" for x in invalidos[:5])
        return jsonify({"error": f"acordes no reconocidos: {detalle}", "invalidos": invalidos}), 400

    bpc = grid.get("beats_por_compas", 4)
    try:
        escribir_atomico(txt_path, _tokens_a_texto(normalizados, beats_por_compas=bpc))
    except OSError as exc:
        return jsonify({"error": f"no pude guardar acordes.txt: {exc}. ¿Lo tenés abierto en otro editor?"}), 500

    return jsonify({"ok": True})


def _beats_base(carpeta: Path):
    """Los tiempos CRUDOS de la grilla (sin el offset de sincronía aplicado).
    Es el espacio en el que se guardan las marcas de rasgueo, para que correr
    el offset mueva las marcas junto con la grilla en vez de dejarlas atrás."""
    grid_path = carpeta / "acordes_grid.json"
    if not grid_path.exists():
        return []
    try:
        base = json.loads(grid_path.read_text(encoding="utf-8")).get("beat_times") or []
        return [float(t) for t in base]
    except (json.JSONDecodeError, OSError, TypeError, ValueError):
        return []


@app.route("/rasgueo/<song>", methods=["GET"])
def obtener_rasgueo(song):
    """Tiempos (en segundos, sin offset) marcados con cambio de rasgueo. Es solo
    una capa visual sobre la grilla existente: vive en su propio archivo para no
    tocar acordes.txt ni acordes_grid.json, así que una canción sin marcas sigue
    exactamente igual que antes.

    Se guardan por TIEMPO y no por posición de la grilla a propósito: regenerar
    los acordes, corregir el tempo (x2 / ÷2 / BPM exacto) o importar un MIDI
    reescriben beat_times con otra cantidad y otro espaciado, y con marcas por
    índice eso las dejaba apuntando a cualquier lado sin aviso. El segundo 28,9
    de la canción, en cambio, sigue siendo el mismo segundo pase lo que pase con
    la grilla.

    El formato viejo (lista de posiciones) se migra solo, una única vez, usando
    la grilla que haya en ese momento."""
    carpeta = stems_dir(song)
    ruta = carpeta / "rasgueo_marcas.json"
    if not ruta.exists():
        return jsonify({"tiempos": []})
    try:
        datos = json.loads(ruta.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return jsonify({"tiempos": []})

    if isinstance(datos.get("tiempos"), list):
        return jsonify({"tiempos": _limpiar_tiempos(datos["tiempos"])})

    # --- migración del formato viejo (posiciones -> tiempos) ---------------
    posiciones = datos.get("posiciones")
    if not isinstance(posiciones, list):
        return jsonify({"tiempos": []})
    base = _beats_base(carpeta)
    tiempos = []
    for p in posiciones:
        try:
            i = int(p)
        except (TypeError, ValueError):
            continue
        if 0 <= i < len(base):
            tiempos.append(round(base[i], 3))
    tiempos = _limpiar_tiempos(tiempos)
    try:
        escribir_atomico(ruta, json.dumps({"tiempos": tiempos}))
    except OSError:
        pass  # si no se puede reescribir, se migra de nuevo la próxima vez
    return jsonify({"tiempos": tiempos, "migrado": True})


def _limpiar_tiempos(valores):
    """Solo números >= 0, sin repetidos y ordenados."""
    limpios = set()
    for v in valores or []:
        try:
            t = float(v)
        except (TypeError, ValueError):
            continue
        if t >= 0:
            limpios.add(round(t, 3))
    return sorted(limpios)


@app.route("/rasgueo/<song>", methods=["POST"])
def guardar_rasgueo(song):
    """Guarda los tiempos (segundos, sin offset) con marca de cambio de rasgueo.
    Al ser por tiempo y no por compás, un cambio que ocurre a mitad de compás
    queda marcado en el instante exacto.

    Acepta también el formato viejo ({"posiciones": [...]}) y lo convierte con
    la grilla actual, para no romper una pestaña que haya quedado abierta desde
    antes de este cambio."""
    carpeta = stems_dir(song)
    if not carpeta.exists():
        return jsonify({"error": "no existe esta canción"}), 404
    datos = request.get_json(silent=True) or {}

    if isinstance(datos.get("tiempos"), list):
        tiempos = _limpiar_tiempos(datos["tiempos"])
    elif isinstance(datos.get("posiciones"), list):
        base = _beats_base(carpeta)
        crudos = []
        for p in datos["posiciones"]:
            try:
                i = int(p)
            except (TypeError, ValueError):
                continue
            if 0 <= i < len(base):
                crudos.append(base[i])
        tiempos = _limpiar_tiempos(crudos)
    else:
        return jsonify({"error": "no recibí la lista de marcas"}), 400

    ruta = carpeta / "rasgueo_marcas.json"
    try:
        escribir_atomico(ruta, json.dumps({"tiempos": tiempos}))
    except OSError as exc:
        return jsonify({"error": f"no pude guardar rasgueo_marcas.json: {exc}"}), 500
    return jsonify({"ok": True, "tiempos": tiempos})


@app.route("/abrir_acordes/<song>", methods=["POST"])
def abrir_acordes(song):
    """Abre acordes.txt con el editor de texto asociado del sistema (Notepad en Windows)."""
    txt_path = stems_dir(song) / "acordes.txt"
    if not txt_path.exists():
        return jsonify({"error": "todavía no hay acordes.txt para esta canción"}), 404
    try:
        if sys.platform.startswith("win"):
            os.startfile(str(txt_path))  # noqa: S606
        elif sys.platform == "darwin":
            subprocess.run(["open", str(txt_path)], check=False)
        else:
            subprocess.run(["xdg-open", str(txt_path)], check=False)
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": str(exc)}), 500
    return jsonify({"ok": True})


@app.route("/exportar/<song>", methods=["POST"])
def exportar(song):
    """Mezcla las pistas no muteadas (con el volumen que tengan en el mezclador)
    y devuelve un mp3 único, vía ffmpeg. Pensado para subir después a Chordify."""
    carpeta = stems_dir(song)
    if not carpeta.exists():
        return jsonify({"error": "canción no encontrada"}), 404

    config = request.get_json(silent=True) or {}
    entradas = []  # (ruta_wav, volumen)
    for stem in STEM_ORDER:
        wav = carpeta / f"{stem}.wav"
        if not wav.exists():
            continue
        cfg = config.get(stem, {})
        if cfg.get("muted"):
            continue
        try:
            vol = float(cfg.get("vol", 1.0))
        except (TypeError, ValueError):
            vol = 1.0
        entradas.append((wav, max(0.0, min(1.0, vol))))

    if not entradas:
        return jsonify({"error": "todas las pistas están muteadas"}), 400

    with tempfile.TemporaryDirectory() as tmp:
        salida = Path(tmp) / "mezcla.mp3"
        cmd = ["ffmpeg", "-y"]
        for wav, _ in entradas:
            cmd += ["-i", str(wav)]

        if len(entradas) == 1:
            cmd += ["-filter:a", f"volume={entradas[0][1]}"]
        else:
            partes = [f"[{i}:a]volume={vol}[a{i}]" for i, (_, vol) in enumerate(entradas)]
            etiquetas = "".join(f"[a{i}]" for i in range(len(entradas)))
            filtro = ";".join(partes) + f";{etiquetas}amix=inputs={len(entradas)}:normalize=0,alimiter=limit=0.95[out]"
            cmd += ["-filter_complex", filtro, "-map", "[out]"]

        cmd += ["-codec:a", "libmp3lame", "-b:a", "256k", str(salida)]

        try:
            proc = subprocess.run(cmd, capture_output=True, text=True)
        except FileNotFoundError:
            return jsonify({"error": "no se encontró ffmpeg. Instalalo y agregalo al PATH."}), 500

        if proc.returncode != 0 or not salida.exists():
            return jsonify({"error": proc.stderr[-2000:]}), 500

        datos = salida.read_bytes()  # a memoria ANTES de salir del "with" (que borra la carpeta temporal)

    return send_file(io.BytesIO(datos), as_attachment=True, download_name=f"{song}_mezcla.mp3", mimetype="audio/mpeg")


# ---------------------------------------------------------------- HTML -----

BASE_STYLE = """<!doctype html>
<html lang="es">
<meta charset="utf-8">
<title>{{ titulo_pagina|default('Mesa') }}</title>
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<link rel="icon" href="/favicon.ico?v={{ version_iconos }}">
<link rel="manifest" href="/manifest.webmanifest">
<meta name="theme-color" content="#0E0E11">
<!-- v112: las fuentes de Google se cargan sin bloquear. Como hoja normal, si
     la tablet tiene wifi pero la red no llega a internet, la página quedaba en
     blanco hasta que el pedido se rendía (decenas de segundos), aunque el
     service worker sirviera todo lo demás al instante. Sin ellas se usan las
     del sistema (mismas reglas de respaldo de siempre). -->
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Bricolage+Grotesque:wght@600;700;800&family=Figtree:wght@400;500;600;700&family=JetBrains+Mono:wght@500;700&display=swap" media="print" onload="this.media='all'">
<script>
// v102: modo claro / oscuro. Se guarda por dispositivo (la tablet y la PC
// pueden quedar distintas) y se aplica acá arriba, antes de pintar, para que
// la página no parpadee en el otro modo al cargar.
(function(){
  var t = "oscuro";
  try { if(localStorage.getItem("mesaTema") === "claro") t = "claro"; } catch(e) {}
  document.documentElement.dataset.tema = t;
  var m = document.querySelector('meta[name="theme-color"]');
  if(m) m.setAttribute("content", t === "claro" ? "#F3F3F5" : "#0E0E11");
})();

// v106: color base de toda la app. Del color elegido se toma el TONO (y la
// saturación); la luminosidad de cada capa queda fija, así el texto se lee
// igual con cualquier color. Se generan los dos juegos (oscuro y claro) en un
// <style> propio con selectores html:root, que le ganan a los :root de la hoja
// principal sin importar el orden. Rojo de mute, celeste de rasgueo y la
// paleta de instrumentos NO se tocan: tienen significado.
// Vacío = se borra el <style> y vuelve la paleta original exacta.
(function(){
  var META = { oscuro: "#0E0E11", claro: "#F3F3F5" };
  function dos(n){ return ("0" + n.toString(16)).slice(-2); }
  function aHex(c){ return "#" + dos(c[0]) + dos(c[1]) + dos(c[2]); }
  function aTrio(c){ return c[0] + "," + c[1] + "," + c[2]; }
  function aRgba(c, a){ return "rgba(" + aTrio(c) + "," + a + ")"; }
  function hexAHs(hex){
    var r = parseInt(hex.substr(1, 2), 16) / 255, g = parseInt(hex.substr(3, 2), 16) / 255, b = parseInt(hex.substr(5, 2), 16) / 255;
    var mx = Math.max(r, g, b), mn = Math.min(r, g, b), l = (mx + mn) / 2, h = 0, s = 0;
    if(mx !== mn){
      var d = mx - mn;
      s = l > 0.5 ? d / (2 - mx - mn) : d / (mx + mn);
      if(mx === r) h = (g - b) / d + (g < b ? 6 : 0);
      else if(mx === g) h = (b - r) / d + 2;
      else h = (r - g) / d + 4;
      h *= 60;
    }
    return [h, s];
  }
  function hslARgb(h, s, l){
    h = ((h % 360) + 360) % 360; s /= 100; l /= 100;
    var c = (1 - Math.abs(2 * l - 1)) * s, x = c * (1 - Math.abs((h / 60) % 2 - 1)), m = l - c / 2;
    var r = 0, g = 0, b = 0;
    if(h < 60){ r = c; g = x; } else if(h < 120){ r = x; g = c; } else if(h < 180){ g = c; b = x; }
    else if(h < 240){ g = x; b = c; } else if(h < 300){ r = x; b = c; } else { r = c; b = x; }
    return [Math.round((r + m) * 255), Math.round((g + m) * 255), Math.round((b + m) * 255)];
  }
  function regla(sel, vars){
    var lineas = [];
    for(var k in vars) lineas.push(k + ":" + vars[k]);
    return sel + "{" + lineas.join(";") + "}";
  }
  window.mesaMetaTema = function(){
    var mm = document.querySelector('meta[name="theme-color"]');
    if(mm) mm.setAttribute("content", META[document.documentElement.dataset.tema === "claro" ? "claro" : "oscuro"]);
  };
  // blanco y negro: los valores exactos de app103, más las fuentes y radios
  // de entonces. Los halos del fondo se apagan (app103 no tenía).
  var MONO_OSCURO = {
    "--tinta": "255,255,255", "--fondo": "0,0,0", "--bg": "#000000",
    "--panel": "#131313", "--panel-2": "#1e1e1e", "--panel-3": "#2b2b2b", "--panel-4": "#3a3a3a",
    "--fg": "#ffffff", "--fg-dim": "#a6a6a6", "--fg-tenue": "#6e6e6e",
    "--brass": "#ffffff", "--sobre-acento": "#000000", "--led-off": "#3a3a3a",
    "--ok": "#ffffff", "--surco": "#000000", "--barra-bg": "rgba(14,14,14,.94)",
    "--glow1": "transparent", "--glow2": "transparent",
    "--mono": 'ui-monospace, "SF Mono", "Cascadia Mono", Consolas, "Roboto Mono", monospace',
    "--sans": 'system-ui, -apple-system, "Segoe UI Variable Text", "Segoe UI", Roboto, sans-serif',
    "--r-l": "18px", "--r-m": "12px", "--r-s": "9px"
  };
  var MONO_CLARO = {
    "--tinta": "0,0,0", "--fondo": "255,255,255", "--bg": "#e8e8e8",
    "--panel": "#ffffff", "--panel-2": "#f2f2f2", "--panel-3": "#e2e2e2", "--panel-4": "#d0d0d0",
    "--fg": "#000000", "--fg-dim": "#555555", "--fg-tenue": "#8c8c8c",
    "--brass": "#000000", "--sobre-acento": "#ffffff", "--led-off": "#c9c9c9",
    "--ok": "#000000", "--surco": "#cfcfcf", "--barra-bg": "rgba(255,255,255,.95)",
    "--glow1": "transparent", "--glow2": "transparent"
  };
  function capaV105(activa){
    var e = document.getElementById("estilo-v105");
    if(e) e.media = activa ? "all" : "not all";
  }
  window.mesaColorBase = function(hex){
    var el = document.getElementById("mesa-colores");
    // la capa v105 solo existe ya parseada cuando esto se llama en vivo; en la
    // carga inicial la decide el atributo media que pone el servidor
    capaV105(false);   // v107: la capa v105 ya no se usa (la reemplaza estilo-v107)
    if(hex === "mono"){
      if(!el){
        el = document.createElement("style");
        el.id = "mesa-colores";
        (document.head || document.documentElement).appendChild(el);
      }
      el.textContent = regla("html:root", MONO_OSCURO) + regla('html:root[data-tema="claro"]', MONO_CLARO);
      META = { oscuro: "#000000", claro: "#e8e8e8" };
      window.mesaMetaTema();
      return;
    }
    if(!hex || !/^#[0-9a-f]{6}$/i.test(hex)){
      if(el) el.parentNode.removeChild(el);
      META = { oscuro: "#0E0E11", claro: "#F3F3F5" };
      window.mesaMetaTema();
      return;
    }
    var hs = hexAHs(hex.toLowerCase()), h = hs[0], k = hs[1];
    // c(giro de tono, saturación objetivo, luminosidad): la saturación se escala
    // con la del color elegido (gris puro = paleta neutra)
    function c(dh, sat, l){ return hslARgb(h + dh, sat * k, l); }
    // oscuro: luminosidades medidas sobre la paleta original (v105)
    var bg = c(0, 56, 8), panel = c(0, 46, 13), brass = c(0, 100, 76), d2 = c(-39, 82, 46);
    var oscuro = {
      "--tinta": aTrio(c(0, 100, 96)), "--fondo": aTrio(bg),
      "--bg": aHex(bg), "--panel": aHex(panel), "--panel-2": aHex(c(0, 44, 19)),
      "--panel-3": aHex(c(0, 38, 25)), "--panel-4": aHex(c(0, 38, 34)),
      "--fg": aHex(c(0, 100, 97)), "--fg-dim": aHex(c(0, 26, 71)), "--fg-tenue": aHex(c(0, 14, 52)),
      "--brass": aHex(brass), "--sobre-acento": aHex(bg), "--led-off": aHex(c(0, 38, 34)),
      "--surco": aHex(bg), "--barra-bg": aRgba(panel, ".94"),
      "--pris": aHex(c(0, 46, 26)), "--prit": aHex(c(0, 100, 87)),
      "--g1": aHex(c(0, 86, 59)), "--g2": aHex(c(2, 100, 71)), "--sh1": aHex(c(0, 66, 33)),
      "--d1": aHex(c(0, 100, 65)), "--d2": aHex(d2), "--d3": aHex(c(-97, 54, 40)),
      "--d4": aHex(c(133, 100, 41)), "--d5": aHex(c(-71, 86, 28)),
      "--glow1": aRgba(c(0, 100, 68), ".30"), "--glow2": aRgba(d2, ".20"),
      "--diag-linea": aHex(c(0, 15, 32)), "--diag-tenue": aHex(c(0, 12, 44))
    };
    var bgC = c(0, 64, 97), tintaC = c(0, 41, 14);
    var claro = {
      "--tinta": aTrio(tintaC),
      "--bg": aHex(bgC), "--panel-2": aHex(c(0, 64, 95)),
      "--panel-3": aHex(c(0, 45, 90)), "--panel-4": aHex(c(0, 43, 85)),
      "--fg": aHex(tintaC), "--fg-dim": aHex(c(0, 17, 43)), "--fg-tenue": aHex(c(0, 14, 52)),
      "--brass": aHex(c(0, 100, 65)), "--led-off": aHex(c(0, 43, 85)), "--surco": aHex(c(0, 46, 89)),
      "--pris": aHex(c(0, 100, 95)), "--prit": aHex(c(0, 63, 50)), "--sh1": aHex(c(0, 63, 44)),
      "--glow1": aRgba(c(0, 100, 65), ".16"), "--glow2": aRgba(d2, ".10"),
      "--diag-linea": aHex(c(0, 15, 45)), "--diag-tenue": aHex(c(0, 12, 55))
    };
    if(!el){
      el = document.createElement("style");
      el.id = "mesa-colores";
      (document.head || document.documentElement).appendChild(el);
    }
    el.textContent = regla("html:root", oscuro) + regla('html:root[data-tema="claro"]', claro);
    META = { oscuro: aHex(bg), claro: aHex(bgC) };
    window.mesaMetaTema();
  };
  window.mesaColorBase({{ color_base|tojson }});
})();
</script>
<meta name="application-name" content="Mesa">
<meta name="mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-title" content="Mesa">
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
<link rel="apple-touch-icon" href="/icono-192.png?v={{ version_iconos }}">
<style>
  /* ------------------------------------------------------------------------
     Rediseño v85 (dirección B). Reglas que se siguen en todo el archivo:
       1. Jerarquía por contraste de superficies, no por bordes: fondo ->
          panel -> panel-2 -> panel-3. Los bordes quedan casi invisibles y
          solo marcan estado (dorado = activo, rojo = mute/borrar).
       2. El color significa algo, igual que antes: el del instrumento vive en
          su canal, el dorado marca "esto suena / está activo", el rojo marca
          mute o borrar. No se agregó ningún color a la paleta.
       3. Tipografía del sistema (sin fuentes externas: rompería el offline).
          Mono SOLO para acordes, cifras y valores.
       4. Mesa: el transporte es una barra fija abajo (tipo reproductor) y la
          mezcla + los ajustes viven en un cajón (lateral en pantallas anchas,
          hoja inferior en la tablet). El cartel queda solo arriba.
       5. Íconos SVG propios (se ven igual en Android y en Windows). Los
          botones cuyo texto lo reescribe el JS (play, borrar canción, play
          del editor) conservan su glifo en el DOM y el ícono se dibuja por
          CSS con una máscara, así la lógica no se toca.
     La geometría del cartel (todo medido en px * --esc) NO cambió.
     ------------------------------------------------------------------------ */
  :root{
    /* v102: rediseño monocromo con dos modos. Negro, blanco y grises
       neutros (sin tinte). Los únicos colores que quedan son los que
       significan algo, iguales en los dos modos:
         - rojo (--led-mute): pista muteada y confirmación de borrado
         - celeste (--c-bass): cambio de rasgueo
         - la paleta de instrumentos, SOLO para el color de la barra según la
           duración del acorde (los canales de la mezcla ya no la usan)
       --brass conserva el nombre porque lo usa medio archivo, pero ahora es
       el color de "activo / suena": violeta (#9585FF en oscuro, #6A4CFF en claro).
       Paleta tomada de la app de guitarra (violeta noche con luces de color).
       --tinta y --fondo son tríos r,g,b para armar transparencias con rgba().
       Estos son los valores del modo OSCURO; el claro está más abajo. */
    color-scheme:dark;
    --tinta:243,240,255; --fondo:12,9,32;
    --bg:#0E0E11;
    --panel:#161230;        /* superficie de los bloques */
    --panel-2:#211B46;      /* superficie elevada: botones, campos, celdas */
    --panel-3:#2D2758;      /* hover / presionado */
    --panel-4:#3E3678;      /* hover de un control que ya está sobre panel-3 */
    --linea:rgba(var(--tinta),.11);        /* separador */
    --linea-fuerte:rgba(var(--tinta),.22); /* borde de un bloque o un control */
    --fg:#F3F0FF; --fg-dim:#A9A3C8; --fg-tenue:#7A7396;
    --brass:#9585FF; --sobre-acento:#0E0E11; --led-off:#3E3678; --led-mute:#d14b3c;
    --ok:#4FE0AB;           /* "conectado / descargado / guardado" (antes verde) */
    --surco:#0E0E11;        /* canal por donde corre un fader */
    --barra-bg:rgba(22,18,48,.94);
    --c-guitar:#e8b34c; --c-vocals:#e2637a; --c-bass:#4fb8b0;
    --c-drums:#e0754a; --c-piano:#9b7fd4; --c-other:#7fb37a;
    /* v105 — identidad de la app de guitarra: cada sección con su color */
    --pris:#2A2360; --prit:#C9BFFF; --g1:#5B3DF0; --g2:#8B6CFF; --sh1:#2E1C8A;
    --d1:#6A4CFF; --d2:#1570D6; --d3:#2F9E6E; --d4:#D15300; --d5:#0A8484;
    --glow1:rgba(124,92,255,.30); --glow2:rgba(21,112,214,.20);
    --fd:'Bricolage Grotesque','Trebuchet MS',system-ui,sans-serif;
    --mono: "JetBrains Mono", ui-monospace, "SF Mono", "Cascadia Mono", Consolas, "Roboto Mono", monospace;
    --sans: "Figtree", system-ui, -apple-system, "Segoe UI Variable Text", "Segoe UI", Roboto, sans-serif;
    --esc:1;
    --diag-linea:#4a4e53; --diag-tenue:#6a6f74;   /* v106: grises de los diagramas */
    --r-l:24px; --r-m:16px; --r-s:12px;
    --alto-transporte:0px;   /* lo pone la mesa midiendo la barra fija */
    /* íconos para máscaras CSS (los de botones cuyo contenido reescribe el JS) */
    --i-play:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24'%3E%3Cpath d='M7.5 4.8c0-.8.9-1.3 1.6-.9l10.3 6.3c.7.4.7 1.4 0 1.8L9.1 18.4c-.7.4-1.6-.1-1.6-.9z'/%3E%3C/svg%3E");
    --i-pausa:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24'%3E%3Crect x='6' y='4.5' width='4.2' height='15' rx='1.3'/%3E%3Crect x='13.8' y='4.5' width='4.2' height='15' rx='1.3'/%3E%3C/svg%3E");
    --i-tilde:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='black' stroke-width='3' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M5 12.5l4.5 4.5L19 7.5'/%3E%3C/svg%3E");
    --i-borrar:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='black' stroke-width='1.8' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M4 7h16M9.5 7V4.8h5V7M6.5 7l.8 11.6a1.6 1.6 0 0 0 1.6 1.4h6.2a1.6 1.6 0 0 0 1.6-1.4L17.5 7M10 11v5M14 11v5'/%3E%3C/svg%3E");
  }
  :root[data-tema="claro"]{
    color-scheme:light;
    --tinta:27,21,50; --fondo:255,255,255;
    --bg:#F3F3F5;
    --panel:#ffffff;
    --panel-2:#EEEAFA;
    --panel-3:#E1DBF2;
    --panel-4:#D2CAEA;
    --linea:rgba(var(--tinta),.12);
    --linea-fuerte:rgba(var(--tinta),.24);
    --fg:#1B1532; --fg-dim:#625B80; --fg-tenue:#7A7396;
    --brass:#6A4CFF; --sobre-acento:#ffffff; --led-off:#D2CAEA;
    --ok:#0B7F53;
    --surco:#DDD6F0;
    --barra-bg:rgba(255,255,255,.95);
    --pris:#E8E3FF; --prit:#4A2FD0; --sh1:#4328B8;
    --glow1:rgba(106,76,255,.16); --glow2:rgba(21,112,214,.10);
  }
  *{box-sizing:border-box;}
  html{ overflow-x:hidden; -webkit-text-size-adjust:100%; }
  body{
    margin:0; overflow-x:hidden;
    background:radial-gradient(520px 280px at 0% 0%,var(--glow1),transparent 70%),radial-gradient(460px 260px at 100% 8%,var(--glow2),transparent 70%),var(--bg); background-attachment:fixed; color:var(--fg); font-family:var(--sans); font-size:14px;
    line-height:1.4; -webkit-font-smoothing:antialiased;
    min-height:100vh; display:flex; flex-direction:column; align-items:center;
    padding:24px 16px 40px;
  }
  h1{
    font-family:var(--sans); font-size:18px; font-weight:650; letter-spacing:-.01em;
    text-transform:none; color:var(--fg); margin:0 0 24px;
  }
  h1 span{ color:var(--fg-dim); font-weight:400; }
  .panel{
    background:var(--panel); border:1px solid var(--linea); border-radius:var(--r-l);
    padding:20px; width:100%; max-width:1080px;
  }
  svg.ico{ width:18px; height:18px; flex:0 0 auto; display:block; }

  /* --- botones -----------------------------------------------------------
     Un solo botón base y tres variantes. "destacado" = encendido (lo usa el
     JS para los toggles), "marcado" = opción elegida de un grupo,
     "peligro"/"confirmando" = acción destructiva. Sin borde por defecto: el
     relleno ya dice "esto se toca". */
  button{
    font-family:var(--sans); font-size:13px; font-weight:550;
    letter-spacing:0; text-transform:none; line-height:1.2;
    background:var(--panel-2); color:var(--fg);
    border:1px solid transparent; border-radius:var(--r-s);
    padding:9px 14px; cursor:pointer;
    transition:background .14s, border-color .14s, color .14s, opacity .14s, transform .08s;
  }
  button:hover{ background:var(--panel-3); }
  button:active:not(:disabled){ transform:scale(.97); }
  button:focus-visible, a:focus-visible, input:focus-visible, select:focus-visible{
    outline:2px solid rgba(var(--tinta),.65); outline-offset:2px;
  }
  button:disabled{ opacity:.35; cursor:not-allowed; }
  .boton-primario{
    background:var(--brass); border-color:var(--brass); color:var(--sobre-acento); font-weight:650;
  }
  .boton-primario:hover{ background:#d6d6d6; border-color:#d6d6d6; }
  .boton-chico{
    display:inline-flex; align-items:center; justify-content:center; gap:6px;
    font-family:var(--sans); font-size:12.5px; font-weight:550;
    letter-spacing:0; text-transform:none;
    background:var(--panel-2); color:var(--fg-dim);
    border:1px solid transparent; padding:8px 12px; border-radius:var(--r-s);
  }
  .boton-chico:hover{ color:var(--fg); background:var(--panel-3); }
  .boton-chico.destacado{
    color:var(--brass); border-color:rgba(var(--tinta),.35); background:rgba(var(--tinta),.11);
  }
  .boton-chico.destacado:hover{ background:rgba(var(--tinta),.17); }
  .boton-chico.marcado{
    background:var(--brass); border-color:var(--brass); color:var(--sobre-acento); font-weight:650;
  }
  .boton-chico.peligro{ color:var(--led-mute); background:rgba(209,75,60,.08); }
  .boton-chico.peligro:hover{ color:var(--led-mute); border-color:rgba(209,75,60,.5); background:rgba(209,75,60,.13); }
  .boton-chico.confirmando{
    color:#fff; border-color:var(--led-mute); background:var(--led-mute);
  }
  /* botón de solo ícono (cuadrado) y botón ícono + texto */
  .boton-icono{ padding:8px; min-width:36px; min-height:36px; }
  .boton-icono.con-texto{ padding:8px 12px 8px 9px; }
  a.boton-chico{ text-decoration:none; }
  input, select, textarea{ font-family:var(--sans); }
  input[type=text], input[type=url], input[type=number], select{
    background:var(--panel-2); color:var(--fg);
    border:1px solid var(--linea-fuerte); border-radius:var(--r-s);
    font-size:13px; padding:9px 12px;
    transition:border-color .14s, background .14s;
  }
  input:focus, select:focus{ outline:none; border-color:var(--brass); }
  ::placeholder{ color:var(--fg-tenue); }
  input[type=file]::file-selector-button{
    font-family:var(--sans); font-size:12px; font-weight:550;
    background:var(--panel-3); color:var(--fg); border:0; border-radius:8px;
    padding:7px 12px; margin-right:10px; cursor:pointer;
  }

  /* --- portada ------------------------------------------------------------ */
  .cabecera-portada{
    width:100%; max-width:1080px; display:flex; align-items:center;
    justify-content:space-between; gap:12px; flex-wrap:wrap;
    margin-bottom:24px;
  }
  .cabecera-portada h1{ margin:0; display:flex; align-items:center; gap:10px; font-size:20px; }
  .marca-app{
    width:32px; height:32px; border-radius:10px; flex:0 0 auto;
    display:flex; align-items:center; justify-content:center;
    background:rgba(var(--tinta),.12); color:var(--brass);
  }

  /* --- portada: agregar canciones --------------------------------------- */
  .panel-carga{
    display:grid; grid-template-columns:1fr 1fr; gap:10px; padding:10px;
  }
  @media (max-width: 860px){ .panel-carga{ grid-template-columns:1fr; } }
  .fila-carga{
    --acento: var(--brass);
    display:flex; align-items:center; gap:12px; flex-wrap:wrap;
    background:var(--panel-2); border:1px solid transparent; border-radius:var(--r-m);
    padding:12px 14px; min-width:0;
    transition:border-color .14s;
  }
  .fila-carga:focus-within{ border-color:var(--acento); }
  .fila-carga-icono{
    flex:0 0 auto; width:38px; height:38px; padding:8px; border-radius:10px;
    background:rgba(var(--tinta),.10);
  }
  .fila-carga-youtube .fila-carga-icono{ background:transparent; }
  .fila-carga-label{ flex:0 0 auto; color:var(--fg); font-size:13px; font-weight:550; white-space:nowrap; }
  .fila-carga input[type=file]{
    flex:1 1 160px; min-width:0; font-size:12px; color:var(--fg-dim);
  }
  .fila-carga-youtube{ --acento:var(--fg); }
  .campo-youtube{
    flex:1 1 180px; min-width:0; background:transparent; border:none; color:var(--fg);
    font-size:14px; padding:8px 0;
  }
  input.campo-youtube{ background:transparent; border:none; padding:8px 0; }
  .campo-youtube:focus{ outline:none; }
  .boton-youtube{ flex:0 0 auto; font-weight:650; }

  /* --- portada: listas --------------------------------------------------- */
  .lista{ width:100%; max-width:1080px; margin-top:32px; }
  .lista h2{
    font-family:var(--sans); font-size:13px; font-weight:600; letter-spacing:0;
    text-transform:none; color:var(--fg-dim); margin:0 0 12px;
  }
  .lista-cabecera{ display:flex; align-items:center; justify-content:space-between; gap:10px; margin-bottom:12px; }
  .lista-cabecera h2{ margin:0; flex:1 1 auto; }
  .buscador{ width:220px; font-size:13px; padding:8px 12px; border-radius:999px; }
  input.buscador{ border-radius:999px; }
  select.orden-canciones{ font-size:13px; padding:8px 12px; border-radius:999px; cursor:pointer; }
  .vacio{
    color:var(--fg-dim); font-size:13px; line-height:1.6;
    border:1px dashed var(--linea-fuerte); border-radius:var(--r-l); padding:24px; text-align:center;
  }
  .setlists-fila{ display:flex; flex-wrap:wrap; gap:8px; align-items:center; }
  .setlist-chip{
    display:flex; align-items:center; gap:8px;
    background:var(--panel); border:1px solid var(--linea); border-radius:999px;
    padding:9px 16px; text-decoration:none; color:var(--fg); font-size:13px; font-weight:550;
    transition:background .14s, border-color .14s;
  }
  .setlist-chip:hover{ background:var(--panel-2); border-color:rgba(var(--tinta),.5); }
  .setlist-chip .cant{
    color:var(--fg-dim); font-family:var(--mono); font-size:11px; font-weight:400;
    background:var(--panel-2); border-radius:999px; padding:2px 7px;
  }
  .setlist-crear{ display:flex; gap:6px; align-items:center; }
  .setlist-crear input{ border-radius:999px; width:180px; }
  input[type=text].setlist-crear-campo, .setlist-crear input[type=text]{ border-radius:999px; }
  .setlist-crear button{ border-radius:999px; }
  .grid-canciones{ display:grid; grid-template-columns:repeat(auto-fill, minmax(240px, 1fr)); gap:8px; }
  .grid-canciones-recientes{ grid-template-columns:repeat(auto-fill, minmax(200px, 1fr)); }
  .cancion-fila{ display:flex; align-items:stretch; gap:6px; }
  .cancion{
    flex:1; min-width:0; display:flex; flex-direction:column; justify-content:center; gap:3px;
    background:var(--panel); border:1px solid var(--linea);
    border-radius:var(--r-m); padding:13px 15px 13px 19px; text-decoration:none; color:var(--fg);
    transition:background .14s, border-color .14s;
  }
  /* el color de cada tema es una barrita a la izquierda, dentro de la tarjeta */
  .cancion::before{
    content:""; position:absolute; left:8px; top:14px; bottom:14px; width:3px; border-radius:2px;
    background:var(--borde, var(--linea-fuerte)); opacity:.9;
  }
  .cancion-editar::before{ display:none; }
  .cancion:hover{ background:var(--panel-2); border-color:var(--linea-fuerte); }
  .cancion-nombre{
    overflow-wrap:anywhere; line-height:1.35; min-height:2.7em; font-size:14px; font-weight:550;
    display:-webkit-box; -webkit-line-clamp:2; -webkit-box-orient:vertical; overflow:hidden;
  }
  .cancion-autor{
    font-size:12px; color:var(--fg-dim);
    white-space:nowrap; overflow:hidden; text-overflow:ellipsis;
  }
  .cancion small{ color:var(--fg-dim); font-size:11px; }
  .cancion-acciones{ display:flex; flex-direction:column; gap:6px; flex:0 0 auto; width:38px; }
  .renombrar-cancion, .borrar-cancion{
    flex:1; width:100%; background:var(--panel); color:var(--fg-tenue);
    border:1px solid var(--linea); border-radius:var(--r-s); padding:0;
    font-size:14px; cursor:pointer;
    display:flex; align-items:center; justify-content:center;
  }
  .renombrar-cancion svg{ width:16px; height:16px; }
  .renombrar-cancion:hover{ color:var(--brass); border-color:rgba(var(--tinta),.5); background:var(--panel-2); }
  /* con mouse, los dos botoncitos aparecen al pasar por la tarjeta (menos
     ruido en una grilla larga); con dedo se ven siempre */
  @media (hover: hover) and (pointer: fine){
    .cancion-acciones{ opacity:.35; transition:opacity .14s; }
    .cancion-fila:hover .cancion-acciones, .cancion-acciones:focus-within{ opacity:1; }
  }
  .cancion-editar{ cursor:default; gap:6px; padding-left:15px; }
  .cancion-editar:hover{ background:var(--panel); }
  .campo-renombrar{
    width:100%; font-size:13px;
    background:var(--panel-2); color:var(--fg); border:1px solid var(--linea-fuerte);
    border-radius:var(--r-s); padding:7px 9px;
  }
  .cancion-editar-botones{ display:flex; gap:6px; }
  .cancion-editar-botones .boton-chico{ flex:1; }
  .borrar-cancion{ font-size:13px; line-height:1.1; }
  /* el tachito lo reescribe el JS como glifo: se oculta el glifo y se dibuja
     el ícono con máscara; en "¿borrar?" y "…" se ve el texto normal */
  .borrar-cancion:not(.confirmando):not(:disabled){ font-size:0; }
  .borrar-cancion:not(.confirmando):not(:disabled)::before{
    content:""; width:16px; height:16px; background:currentColor;
    -webkit-mask:var(--i-borrar) center/contain no-repeat; mask:var(--i-borrar) center/contain no-repeat;
  }
  .borrar-cancion:hover{ color:var(--led-mute); border-color:rgba(209,75,60,.55); background:var(--panel-2); }
  .borrar-cancion.confirmando{ font-size:10px; color:#fff; border-color:var(--led-mute); background:var(--led-mute); }

  /* --- marca de "descargada para tocar sin wifi" -------------------------- */
  /* El punto lo pone marcarDescargadas() leyendo el caché, no el servidor:
     la descarga vive en el navegador de cada dispositivo, así que la tablet
     y la PC pueden tener cosas distintas descargadas y cada una muestra lo
     suyo. */
  .cancion{ position:relative; }
  .marca-offline{
    position:absolute; top:8px; right:8px;
    display:flex; align-items:center; justify-content:center;
    width:16px; height:16px; border-radius:50%;
    background:rgba(var(--tinta),.16); border:1px solid rgba(var(--tinta),.5);
    color:var(--ok); font-size:10px; line-height:1;
    pointer-events:none;
  }
  .cancion.descargada .cancion-nombre{ padding-right:18px; }
  .setlist-fila-cancion .marca-offline{ position:static; flex:0 0 auto; align-self:center; }
  .setlist-fila-cancion .cancion.descargada .cancion-nombre{ padding-right:0; }

  /* --- chips de estado ----------------------------------------------------
     Todos comparten forma: pastilla chica con un punto de color. */
  #chip-red, #chip-pedal, #chip-hud-estado, #chip-hud-ble, #chip-hud-ble-local, #chip-offline{
    display:inline-flex; align-items:center; gap:7px; flex:0 0 auto;
    padding:7px 11px; border-radius:999px; white-space:nowrap;
    font-size:11.5px; font-family:var(--sans); font-weight:500; line-height:1;
    background:var(--panel-2); border:1px solid transparent;
    color:var(--fg-dim);
    transition:opacity .25s, color .25s, border-color .25s, background .25s;
  }
  #chip-red .punto, #chip-pedal .punto, #chip-hud-estado .punto,
  #chip-hud-ble .punto, #chip-hud-ble-local .punto, #chip-offline .punto{
    width:7px; height:7px; border-radius:50%; flex:0 0 auto; background:var(--led-off);
  }

  /* red: anclado donde esté span#ancla-red; si no hay ancla, fijo abajo a la
     izquierda (zona que ni la mesa ni el modo tocar usan) */
  #chip-red.suelto{ position:fixed; left:12px; bottom:calc(12px + var(--alto-transporte)); z-index:9000; box-shadow:0 6px 18px rgba(0,0,0,.5); }
  #chip-red.en-linea{ color:var(--fg-dim); }
  #chip-red.en-linea .punto{ background:var(--ok); box-shadow:0 0 0 3px rgba(var(--tinta),.15); }
  #chip-red.sin-red{ color:var(--brass); border-color:rgba(var(--tinta),.45); background:rgba(var(--tinta),.10); }
  #chip-red.sin-red .punto{ background:var(--brass); }

  /* pedal: solo aparece cuando hay algo que decir (el JS maneja display) */
  #chip-pedal .punto{ background:var(--ok); }
  #chip-pedal.sin-pedal{ color:var(--led-mute); border-color:rgba(209,75,60,.5); background:rgba(209,75,60,.09); }
  #chip-pedal.sin-pedal .punto{ background:var(--led-mute); }

  /* HUD (dentro de Ajustes generales): gris = apagado, dorado = buscando,
     verde = conectado/transmitiendo */
  #chip-hud-ble.buscando, #chip-hud-ble-local.buscando{ color:var(--brass); border-color:rgba(var(--tinta),.45); background:rgba(var(--tinta),.10); }
  #chip-hud-ble.buscando .punto, #chip-hud-ble-local.buscando .punto{ background:var(--brass); }
  #chip-hud-ble.enlazado, #chip-hud-ble-local.enlazado{ color:var(--ok); border-color:rgba(var(--tinta),.45); background:rgba(var(--tinta),.10); }
  #chip-hud-ble.enlazado .punto, #chip-hud-ble-local.enlazado .punto{ background:var(--ok); }
  #chip-hud-estado.transmitiendo{ color:var(--ok); border-color:rgba(var(--tinta),.45); background:rgba(var(--tinta),.10); }
  #chip-hud-estado.transmitiendo .punto{ background:var(--ok); }

  /* descarga offline: es un BOTÓN (dispara descarga o borrado) */
  #chip-offline{ cursor:pointer; }
  #chip-offline:hover{ color:var(--fg); background:var(--panel-3); }
  #chip-offline.descargada{ color:var(--ok); border-color:rgba(var(--tinta),.45); background:rgba(var(--tinta),.10); }
  #chip-offline.descargada .punto{ background:var(--ok); }
  #chip-offline.trabajando{ color:var(--brass); border-color:rgba(var(--tinta),.45); background:rgba(var(--tinta),.10); cursor:progress; }
  #chip-offline.trabajando .punto{ background:var(--brass); }
  #chip-offline.confirmando{ color:#fff; border-color:var(--led-mute); background:var(--led-mute); }
  #chip-offline.confirmando .punto{ background:#fff; }
  #chip-offline:disabled{ opacity:.5; cursor:not-allowed; }

  /* --- aviso (toast) --------------------------------------------------------
     Reemplaza a alert(): no bloquea la página. Queda por encima de la barra
     de transporte fija de la mesa. */
  #mesa-toast{
    position:fixed; left:50%; bottom:calc(20px + var(--alto-transporte)); transform:translate(-50%, 8px);
    z-index:9500; max-width:min(92vw, 560px);
    background:var(--panel-3); border:1px solid var(--linea-fuerte); color:var(--fg);
    border-radius:var(--r-m); padding:12px 16px; font-size:13px; line-height:1.5;
    white-space:pre-line; box-shadow:0 12px 32px rgba(0,0,0,.55); cursor:pointer;
    opacity:0; pointer-events:none; transition:opacity .2s, transform .2s;
  }
  #mesa-toast.visible{ opacity:1; pointer-events:auto; transform:translate(-50%, 0); }
  #mesa-toast.error{ border-color:var(--led-mute); }

  body.sin-red .cancion:not(.descargada){ opacity:.35; }

  /* --- portada: trabajos en proceso ----------------------------------------- */
  .jobs-fila{ display:flex; flex-wrap:wrap; gap:8px; }
  .job-chip{
    display:inline-flex; align-items:center; gap:8px;
    background:var(--panel); border:1px solid rgba(var(--tinta),.35); border-radius:999px;
    padding:9px 16px; text-decoration:none; color:var(--fg); font-size:13px;
  }
  .job-chip:hover{ border-color:var(--brass); background:var(--panel-2); }
  .job-chip .punto{ width:8px; height:8px; border-radius:50%; background:var(--brass); flex:0 0 auto; animation:latido 1.4s ease-in-out infinite; }
  @keyframes latido{ 0%,100%{ opacity:1; } 50%{ opacity:.35; } }
  .job-chip .estado{ color:var(--fg-dim); font-family:var(--mono); font-size:11px; }
  .resumen-offline{ width:100%; max-width:1080px; margin:28px 0 0; font-size:12px; color:var(--fg-dim); text-align:center; }

  /* --- barra de transporte fija (mesa) --------------------------------------
     Es el mismo #panel-transporte de siempre, pero pegado abajo de la
     pantalla como un reproductor: siempre a mano, también con el cajón de
     ajustes abierto y en modo tocar. El contenido se centra a 1080px. */
  .barra-transporte{
    position:fixed; left:0; right:0; bottom:0; z-index:800;
    max-width:none; width:auto; margin:0;
    border:0; border-top:1px solid var(--linea-fuerte); border-radius:0;
    background:var(--barra-bg);
    -webkit-backdrop-filter:blur(16px) saturate(1.2); backdrop-filter:blur(16px) saturate(1.2);
    padding:10px max(16px, calc((100% - 1080px) / 2)) 10px;
    box-shadow:0 -10px 30px rgba(0,0,0,.35);
  }
  @supports (padding: env(safe-area-inset-bottom)){
    .barra-transporte{
      padding-bottom:max(10px, env(safe-area-inset-bottom));
      padding-left:max(16px, calc((100% - 1080px) / 2), env(safe-area-inset-left));
      padding-right:max(16px, calc((100% - 1080px) / 2), env(safe-area-inset-right));
    }
  }
  /* la página deja lugar abajo para la barra (la mide el JS de la UI) */
  body:has(#panel-transporte){ padding-bottom:calc(var(--alto-transporte, 150px) + 24px); }
  .transporte{ display:flex; align-items:center; gap:14px; }
  .transporte-botones{ display:flex; align-items:center; gap:6px; flex:0 0 auto; }
  .transporte-linea{ flex:1 1 auto; display:flex; align-items:center; gap:12px; min-width:0; }
  #tiempo{
    font-family:var(--mono); font-size:12px; color:var(--fg-dim);
    min-width:88px; white-space:nowrap; font-variant-numeric:tabular-nums;
  }

  /* play: el JS le escribe un glifo (▶ / ❚❚); el ícono lo dibuja la máscara
     y la clase .en-marcha la pone un observador según ese glifo */
  #play{
    --play-icono:18px;
    width:48px; height:48px; padding:0; border-radius:50%; font-size:0; color:var(--sobre-acento);
    background:var(--brass); border-color:var(--brass);
    display:inline-flex; align-items:center; justify-content:center; flex:0 0 auto;
    box-shadow:0 4px 16px rgba(var(--tinta),.22);
  }
  #play::before{
    content:""; width:var(--play-icono); height:var(--play-icono); background:currentColor;
    -webkit-mask:var(--i-play) center/contain no-repeat; mask:var(--i-play) center/contain no-repeat;
    margin-left:2px;
  }
  #play.en-marcha::before{
    -webkit-mask-image:var(--i-pausa); mask-image:var(--i-pausa); margin-left:0;
  }
  #play:hover{ background:#d6d6d6; }
  /* mientras bajan las pistas el play se ve "a medias": sigue siendo clickeable
     (tocarlo deja programado el arranque para cuando terminen) */
  #play.cargando{ opacity:.45; cursor:progress; }
  #rebobinar{
    width:40px; height:40px; padding:0; border-radius:50%; color:var(--fg-dim);
    display:inline-flex; align-items:center; justify-content:center; flex:0 0 auto;
    background:transparent;
  }
  #rebobinar:hover{ color:var(--fg); background:var(--panel-2); }
  #rebobinar svg{ width:20px; height:20px; }
  /* saltar de a un compás: las flechas rodean el número del compás que suena */
  .compas-nav{
    display:flex; align-items:center; gap:0;
    background:var(--panel-2); border-radius:999px; padding:2px; margin-left:4px;
  }
  .compas-nav button{
    width:32px; height:32px; padding:0; border-radius:50%; line-height:1;
    color:var(--fg-dim); background:transparent; border-color:transparent;
    display:inline-flex; align-items:center; justify-content:center;
  }
  .compas-nav button svg{ width:16px; height:16px; }
  .compas-nav button:hover{ color:var(--fg); background:var(--panel-3); }
  #compas-num{
    font-family:var(--mono); font-size:12.5px; color:var(--fg); min-width:44px; text-align:center;
    font-variant-numeric:tabular-nums;
  }
  /* el tramo del loop A-B se pinta sobre la propia barra de seek. Sin loop las
     dos variables valen 0% y el degradé es un color liso. */
  input[type=range]#seek{
    -webkit-appearance:none; appearance:none; height:4px; border-radius:2px;
    --loop-a:0%; --loop-b:0%;
    background:linear-gradient(to right,
      var(--linea-fuerte) var(--loop-a), rgba(var(--tinta),.55) var(--loop-a),
      rgba(var(--tinta),.55) var(--loop-b), var(--linea-fuerte) var(--loop-b));
    min-width:0; flex:1 1 140px; margin:0; cursor:pointer;
  }
  input[type=range]#seek::-webkit-slider-thumb{
    -webkit-appearance:none; width:14px; height:14px; border-radius:50%;
    background:var(--fg); cursor:pointer; margin-top:-5px;
    box-shadow:0 0 0 4px rgba(var(--tinta),.25);
  }
  input[type=range]#seek::-webkit-slider-runnable-track{
    height:4px; border-radius:2px;
    background:linear-gradient(to right,
      var(--linea-fuerte) var(--loop-a), rgba(var(--tinta),.55) var(--loop-a),
      rgba(var(--tinta),.55) var(--loop-b), var(--linea-fuerte) var(--loop-b));
  }
  input[type=range]#seek::-moz-range-track{
    height:4px; border-radius:2px;
    background:linear-gradient(to right,
      var(--linea-fuerte) var(--loop-a), rgba(var(--tinta),.55) var(--loop-a),
      rgba(var(--tinta),.55) var(--loop-b), var(--linea-fuerte) var(--loop-b));
  }
  input[type=range]#seek::-moz-range-thumb{
    width:14px; height:14px; border-radius:50%; border:none; background:var(--fg); cursor:pointer;
  }

  /* --- cartel de acordes --------------------------------------------------
     La geometría no cambió: todo sigue medido en píxeles multiplicados por
     --esc, así que el modo tocar escala el bloque entero sin reacomodar nada. */
  .acordes-display{
    position:relative;
    text-align:center; padding:26px 24px 18px; background:var(--panel);
    border-color:transparent; border-radius:22px;
    margin-bottom:12px;
  }
  /* --- v89: cuenta regresiva 4-3-2-1 superpuesta al cartel --------------- */
  .cuenta-regresiva{
    position:absolute; inset:0; z-index:8; display:none;
    align-items:center; justify-content:center; pointer-events:none;
    border-radius:inherit; background:rgba(0,0,0,.55);
    color:var(--brass); font-weight:800; line-height:1;
    font-size:clamp(90px, 22vh, 260px);
  }
  .cuenta-regresiva.visible{ display:flex; }
  .cuenta-regresiva.pulso{ animation:cuenta-pulso .9s ease-out; }
  @keyframes cuenta-pulso{ from{ transform:scale(1.25); opacity:.3; } 30%{ transform:scale(1); opacity:1; } }
  /* --- chip de cejilla/capotraste: arriba-izquierda del cartel ------------ */
  /* v88: el chip de cejilla y el de guitarra van apilados en una columna */
  .chips-cartel{
    position:absolute; top:14px; left:16px; z-index:5;
    display:flex; flex-direction:column; align-items:flex-start; gap:6px;
    pointer-events:none;
  }
  #chip-capo{
    display:none;
    align-items:center; gap:6px;
    padding:7px 11px; border-radius:999px; white-space:nowrap;
    font-size:11.5px; font-family:var(--sans); font-weight:550; line-height:1;
    background:rgba(var(--tinta),.10); border:1px solid rgba(var(--tinta),.4);
    color:var(--brass);
  }
  #chip-capo.visible{ display:inline-flex; }
  /* --- cinta de compases (v87, modo alternativo) ---------------------------
     Una fila de tiempos que se desliza de derecha a izquierda bajo un cabezal
     fijo; el tiempo que suena lleva un cuadrado relleno. Cada celda = 1 tiempo,
     todas del mismo ancho: el desplazamiento se interpola entre beats reales,
     así que un tempo que respira no deforma la cinta. */
  .cinta{
    display:none; position:relative; overflow:hidden;
    height:calc(64px * var(--esc)); margin:0 calc(-24px) calc(14px * var(--esc));
    background:var(--panel-2); border-radius:calc(12px * var(--esc));
  }
  body.vista-cinta .cinta{ display:block; }
  /* con la cinta arriba, el chip de cejilla baja a la esquina inferior */
  body.vista-cinta .chips-cartel{ top:auto; bottom:14px; }
  /* v90: la barra de duración del acorde se mantiene visible con la cinta */
  body.vista-cinta .puntos-compas{ display:none !important; }
  .cinta-pista{
    position:absolute; left:0; top:0; bottom:0; display:flex; will-change:transform;
  }
  .cinta-tiempo{
    position:relative; flex:0 0 auto; width:calc(46px * var(--esc)); height:100%;
    border-left:1px solid transparent;
  }
  .cinta-tiempo.inicio-compas{ border-left:calc(3px * var(--esc)) solid var(--linea-fuerte); }
  .cinta-cuadro{
    position:absolute; left:50%; bottom:calc(9px * var(--esc));
    width:calc(9px * var(--esc)); height:calc(9px * var(--esc));
    transform:translateX(-50%); border-radius:2px; background:var(--led-off);
  }
  .cinta-tiempo.activo .cinta-cuadro{
    width:calc(26px * var(--esc)); height:calc(26px * var(--esc));
    bottom:calc(6px * var(--esc)); background:var(--brass);
  }
  .cinta-acorde{
    position:absolute; left:calc(6px * var(--esc)); top:calc(5px * var(--esc));
    font-family:var(--mono); font-weight:700; line-height:1; white-space:nowrap;
    font-size:calc(22px * var(--esc)); color:var(--fg); z-index:1;
  }
  /* el acorde que suena, clavado al borde izquierdo cuando su celda de
     inicio ya salió de la cinta (acordes largos) */
  .cinta-fijo{ display:none; color:var(--brass); z-index:3; }
  .cinta-fijo.visible{ display:block; }
  .cinta-acorde .sufijo-chico{ font-size:.6em; font-weight:600; opacity:.8; }
  /* el acorde que suena ahora, en dorado */
  .cinta-tiempo.acorde-sonando .cinta-acorde{ color:var(--brass); }
  /* celeste = ahí cambia el rasgueo, igual que en el cartel y la tira */
  .cinta-tiempo.rasgueo::before{
    content:""; position:absolute; left:0; right:0; top:0; height:calc(3px * var(--esc));
    background:var(--c-bass);
  }
  .acorde-grande{
    font-family:var(--mono); font-weight:700; line-height:1; letter-spacing:.01em;
    color:var(--brass);
    transition:transform .15s ease;
  }
  .acorde-grande .sufijo-chico{
    font-size:.42em; font-weight:600; letter-spacing:0;
    color:var(--fg-dim); -webkit-text-fill-color:var(--fg-dim); opacity:.8;
  }
  .fila-acordes{ position:relative; height:calc(112px * var(--esc)); margin:0 auto; }
  #acorde-actual{
    position:absolute; top:50%; left:50%; white-space:nowrap;
    font-size:calc(104px * var(--esc)); transform:translate(-50%,-50%);
  }
  #acorde-actual.destello{ transform:translate(-50%,-50%) scale(1.06); }
  #acorde-actual.rasgueo-cambio{ color:var(--c-bass); }
  #acorde-siguiente{
    position:absolute; top:50%; left:calc(50% + 145px * var(--esc)); white-space:nowrap;
    font-size:calc(78px * var(--esc)); transform:translateY(-50%);
    color:var(--fg-dim); opacity:.45;
  }
  #acorde-siguiente.rasgueo-viene{ color:rgba(79,184,176,.85); opacity:1; }
  .diagrama{
    position:absolute; top:50%; transform:translateY(-50%);
    left:calc(50% - 230px * var(--esc)); opacity:.9;
  }
  .diagrama-sig{ left:calc(50% + 265px * var(--esc)); opacity:.4; }
  .diagrama svg{ display:block; }
  .grado-chico{
    position:absolute; top:calc(50% - 74px * var(--esc)); left:50%; transform:translateX(-50%);
    font-family:var(--mono); font-size:calc(22px * var(--esc)); font-weight:600; letter-spacing:.03em;
    color:var(--brass); opacity:.6; white-space:nowrap; pointer-events:none;
  }
  .grado-chico-sig{
    left:calc(50% + 145px * var(--esc)); font-size:calc(17px * var(--esc)); opacity:.4;
  }
  .linea-progresion{
    margin-top:14px; font-family:var(--mono); font-size:12px; letter-spacing:.04em;
    color:var(--fg-dim);
  }
  .puntos-compas{ display:flex; justify-content:center; gap:calc(12px * var(--esc)); margin-top:calc(14px * var(--esc)); }
  .barra-acorde{
    width:calc(340px * var(--esc)); height:calc(6px * var(--esc));
    margin:calc(16px * var(--esc)) auto 0; border-radius:999px;
    background:var(--panel-3); overflow:hidden;
  }
  .barra-acorde-relleno{ height:100%; width:0%; border-radius:999px; background:var(--brass); }
  .punto{
    width:calc(12px * var(--esc)); height:calc(12px * var(--esc));
    border-radius:50%; background:var(--led-off); transition:background .1s;
  }
  .punto.activo{ background:var(--brass); }

  /* --- cabecera de la mesa y navegación de setlist ------------------------
     Barra de app: volver + título a la izquierda, estado y acciones a la
     derecha. En angosto los chips "todo bien" se reducen al punto. */
  .cabecera-mesa{
    width:100%; max-width:1080px; display:flex; align-items:center;
    gap:10px; margin-bottom:14px;
  }
  .cabecera-mesa h1{
    margin:0; flex:1 1 auto; min-width:0; text-align:left; font-size:18px;
    white-space:nowrap; overflow:hidden; text-overflow:ellipsis;
  }
  .estado-grupo{ display:flex; align-items:center; gap:6px; flex:0 0 auto; }
  .acciones-cabecera{ display:flex; align-items:center; gap:6px; flex:0 0 auto; }
  #toggle-modo-tocar{ flex:0 0 auto; }
  .setlist-nav{
    width:100%; max-width:1080px; display:flex; align-items:center; justify-content:center;
    gap:6px; margin-bottom:14px;
  }
  .setlist-nav .boton-chico{ padding:7px 12px; }
  .setlist-nav-nombre{
    font-size:12.5px; color:var(--fg-dim); text-decoration:none;
    padding:7px 12px; border-radius:999px; background:var(--panel);
    white-space:nowrap; overflow:hidden; text-overflow:ellipsis; min-width:0;
  }
  .setlist-nav-nombre:hover{ color:var(--brass); }
  .setlist-nav .deshabilitado{ opacity:.3; pointer-events:none; }

  /* --- cajón de mezcla y ajustes -------------------------------------------
     Lateral a la derecha en pantallas anchas; hoja que sube desde la barra
     de transporte en la tablet. Adentro van los tres paneles plegables de
     siempre (mismos ids, mismo JS, misma preferencia de plegado). */
  .cajon-fondo{
    position:fixed; left:0; right:0; top:0; bottom:0;
    background:rgba(0,0,0,.28); z-index:850;
    opacity:0; pointer-events:none; transition:opacity .22s;
  }
  body.cajon-abierto .cajon-fondo{ opacity:1; pointer-events:auto; }
  .cajon{
    position:fixed; z-index:860; left:0; right:0; bottom:var(--alto-transporte);
    max-height:calc(100vh - var(--alto-transporte) - 48px);
    max-height:calc(100dvh - var(--alto-transporte) - 48px);
    display:flex; flex-direction:column;
    background:var(--panel); border-top:1px solid var(--linea-fuerte);
    border-radius:22px 22px 0 0;
    box-shadow:0 -20px 50px rgba(0,0,0,.5);
    transform:translateY(calc(100% + 60px)); visibility:hidden;
    transition:transform .28s cubic-bezier(.2,.8,.2,1), visibility 0s linear .28s;
  }
  body.cajon-abierto .cajon{
    transform:none; visibility:visible;
    transition:transform .28s cubic-bezier(.2,.8,.2,1), visibility 0s;
  }
  .cajon::before{   /* manija de la hoja */
    content:""; width:40px; height:4px; border-radius:2px; background:var(--linea-fuerte);
    margin:8px auto 0; flex:0 0 auto;
  }
  @media (min-width: 1100px){
    .cajon{
      left:auto; top:0; width:min(640px, 92vw); max-height:none;
      border-top:0; border-left:1px solid var(--linea-fuerte); border-radius:0;
      box-shadow:-20px 0 50px rgba(0,0,0,.45);
      transform:translateX(calc(100% + 60px));
    }
    .cajon::before{ display:none; }
  }
  .cajon-cabecera{
    display:flex; align-items:center; gap:10px; flex:0 0 auto;
    padding:12px 12px 10px 22px; border-bottom:1px solid var(--linea);
  }
  .cajon-titulo{ flex:1; font-size:15px; font-weight:650; }
  .cajon-cuerpo{ flex:1 1 auto; overflow-y:auto; overscroll-behavior:contain; -webkit-overflow-scrolling:touch; }
  .cajon .panel{
    background:transparent; border:0; border-radius:0; max-width:none;
    border-bottom:1px solid var(--linea);
  }
  .cajon .panel:last-child{ border-bottom:0; }

  /* --- paneles plegables (dentro del cajón) -------------------------------
     Una fila con el nombre, un resumen del estado y un chevron. */
  .panel-plegable{ padding:0; overflow:hidden; }
  .panel-plegable-cabecera{
    display:flex; align-items:center; gap:12px;
    padding:16px 18px 16px 22px; cursor:pointer; user-select:none;
    transition:background .14s;
  }
  .panel-plegable-cabecera:hover{ background:rgba(var(--tinta),.025); }
  .panel-plegable-titulo{ font-size:14px; font-weight:650; color:var(--fg); flex:0 0 auto; }
  .panel-plegable-resumen{
    flex:1; min-width:0; font-size:12px; color:var(--fg-dim);
    white-space:nowrap; overflow:hidden; text-overflow:ellipsis;
  }
  .panel-plegable-flecha{
    display:flex; align-items:center; justify-content:center; flex:0 0 auto;
    width:32px; height:32px; border-radius:50%;
    color:var(--fg-dim); transition:transform .18s, color .15s, background .15s;
  }
  .panel-plegable-flecha svg{ width:18px; height:18px; }
  .panel-plegable-cabecera:hover .panel-plegable-flecha{ color:var(--brass); background:var(--panel-2); }
  .panel-plegable.colapsado .panel-plegable-flecha{ transform:rotate(-90deg); }
  .panel-plegable-cuerpo{ padding:4px 22px 22px; }
  .panel-plegable.colapsado .panel-plegable-cuerpo{ display:none; }

  /* --- grupos de ajustes -------------------------------------------------- */
  .panel-controles-cuerpo{
    display:grid; grid-template-columns:repeat(auto-fit, minmax(200px, 1fr));
    gap:14px; align-items:start;
  }
  .grupo{
    display:flex; flex-direction:column; gap:8px; min-width:0;
    background:var(--panel-2); border-radius:var(--r-m); padding:14px;
  }
  .grupo-titulo{
    font-size:12px; font-weight:600; color:var(--fg-dim); margin-bottom:2px;
  }
  .grupo-cuerpo{ display:flex; flex-direction:column; gap:6px; width:100%; }
  .grupo-fila{ display:flex; gap:6px; width:100%; }
  .grupo-fila .boton-chico, .grupo-fila .campo-chico{ flex:1; min-width:0; }
  .grupo-cuerpo > .boton-chico{ width:100%; text-align:center; }
  .grupo .boton-chico{ background:var(--panel-3); }
  .grupo .boton-chico:hover{ background:var(--panel-4); }
  .grupo .boton-chico.destacado{ background:rgba(var(--tinta),.12); }
  .grupo .boton-chico.marcado{ background:var(--brass); }
  .grupo .boton-chico.peligro{ background:rgba(209,75,60,.10); }
  .grupo .boton-chico.confirmando{ background:var(--led-mute); }
  .grupo-valor{
    font-family:var(--mono); font-size:22px; color:var(--fg); padding:0 0 4px;
    font-variant-numeric:tabular-nums;
  }
  .grupo-valor.destacado-valor{ color:var(--brass); }
  .campo-chico{
    font-family:var(--mono); font-size:13px; text-align:center; padding:8px 6px;
  }
  input.campo-chico{ font-family:var(--mono); background:var(--panel); }

  /* --- editor de acordes -------------------------------------------------- */
  #panel-editor{ margin-bottom:14px; scroll-margin-top:16px; }
  .editor-cabecera{
    display:flex; align-items:center; gap:12px; flex-wrap:wrap;
    margin-bottom:16px; padding-bottom:14px; border-bottom:1px solid var(--linea);
  }
  .editor-titulo{ font-size:15px; font-weight:650; color:var(--fg); }
  .editor-ayuda{ font-size:12px; color:var(--fg-dim); flex:1 1 320px; min-width:0; }
  .editor-estado{ font-size:12px; color:var(--fg-dim); min-width:110px; text-align:right; }
  .editor-estado.sin-guardar{ color:var(--brass); }
  .editor-estado.guardado{ color:var(--ok); }
  .editor-estado.error{ color:var(--led-mute); }
  .editor-grilla{ display:flex; flex-wrap:wrap; gap:8px; max-height:420px; overflow-y:auto; padding:2px; }
  .compas{
    background:var(--panel-2); border:1px solid transparent; border-radius:var(--r-m);
    padding:6px 8px 8px; min-width:190px;
  }
  .compas.sonando{ border-color:var(--brass); background:rgba(var(--tinta),.06); }
  .compas-cab{ display:flex; align-items:center; gap:6px; margin-bottom:6px; }
  .compas-num{ font-family:var(--mono); font-size:11px; color:var(--fg-dim); }
  /* el ▶ lo genera el JS como texto: se dibuja con máscara */
  .compas-play{
    background:transparent; border:none; color:var(--fg-dim); cursor:pointer;
    font-size:0; padding:0; width:24px; height:22px; border-radius:6px;
    display:inline-flex; align-items:center; justify-content:center;
  }
  .compas-play::before{
    content:""; width:11px; height:11px; background:currentColor;
    -webkit-mask:var(--i-play) center/contain no-repeat; mask:var(--i-play) center/contain no-repeat;
  }
  .compas-play:hover{ color:var(--brass); background:rgba(var(--tinta),.12); }
  .compas-celdas{ display:flex; gap:4px; }
  .celda-wrap{ display:flex; flex-direction:column; align-items:stretch; gap:3px; }
  .celda{
    width:52px; padding:7px 2px; text-align:center;   /* entra "C#maj7" */
    font-family:var(--mono); font-size:13px; font-weight:600;
    background:var(--panel); color:var(--fg); border:1px solid var(--linea-fuerte); border-radius:7px;
  }
  input.celda{ padding:7px 2px; font-family:var(--mono); font-size:13px; background:var(--panel); }
  .celda::placeholder{ color:var(--fg-tenue); font-weight:400; }
  .celda:focus{ outline:none; border-color:var(--brass); }
  .celda.invalida{ border-color:var(--led-mute); color:var(--led-mute); }
  .celda.heredada{ color:var(--fg-dim); }
  /* el cambio de rasgueo se marca por celda: la barrita de abajo es el
     quiebre exacto; el tinte de fondo es el tramo hasta la próxima marca */
  .celda-rasgueo{
    height:5px; border-radius:3px; border:none; padding:0; cursor:pointer;
    background:var(--linea-fuerte);
  }
  .celda-rasgueo:hover{ background:rgba(79,184,176,.6); }
  .celda-rasgueo.activo{ background:var(--c-bass); }
  .celda.rasgueado{ background:rgba(79,184,176,.14); border-color:rgba(79,184,176,.45); }

  /* --- consola de faders --------------------------------------------------
     El único color de esta zona es el del propio instrumento: una franja
     arriba del canal y el cursor del fader. En el cajón los canales son
     angostos para que entren los 7 en una fila. */
  .consola{ display:flex; gap:8px; justify-content:flex-start; flex-wrap:nowrap; padding-bottom:4px; }
  .canal{
    display:flex; flex-direction:column; align-items:center;
    flex:1 1 0; min-width:0; max-width:96px; border-radius:var(--r-m); overflow:hidden;
    background:var(--panel-2); border:1px solid transparent;
  }
  .canal-cap{ height:3px; width:100%; background:var(--canal-color); }
  .canal-nombre{
    font-size:11.5px; font-weight:550; color:var(--fg); margin:12px 0 10px; text-align:center;
    white-space:nowrap; overflow:hidden; text-overflow:ellipsis; max-width:100%; padding:0 4px;
  }
  .fader-wrap{ position:relative; width:10px; height:180px; margin:0 auto; }
  input.fader{
    position:absolute; top:50%; left:50%; margin:0;
    width:180px; height:6px;
    transform:translate(-50%,-50%) rotate(-90deg);
    -webkit-appearance:none; appearance:none;
    background:var(--surco); border-radius:3px; outline:none; border:0; padding:0;
  }
  input.fader::-webkit-slider-runnable-track{ height:6px; border-radius:3px; background:var(--surco); }
  input.fader::-webkit-slider-thumb{
    -webkit-appearance:none; width:26px; height:13px; border-radius:4px;
    background:var(--canal-color); border:none; cursor:pointer; margin-top:-3.5px;
    box-shadow:0 2px 6px rgba(0,0,0,.5);
  }
  input.fader::-moz-range-thumb{ width:26px; height:13px; border-radius:4px; border:none; background:var(--canal-color); }
  .canal-valor{ font-family:var(--mono); font-size:11px; color:var(--fg-dim); margin-top:12px; font-variant-numeric:tabular-nums; }
  .canal-botones{
    display:flex; flex-direction:column; gap:4px; justify-content:center;
    margin:10px 0 10px; width:calc(100% - 12px);
  }
  .canal .mute, .canal .guia{
    padding:6px 4px; border-radius:7px; font-size:11px; font-weight:600;
    background:var(--panel-3); color:var(--fg-dim); border:1px solid transparent;
    cursor:pointer; width:100%;
  }
  .canal .mute:hover, .canal .guia:hover{ color:var(--fg); background:var(--panel-4); }
  .canal .mute.muted{ background:var(--led-mute); border-color:var(--led-mute); color:#fff; }
  /* guía activa = la pista suena bajita, no apagada: color del propio canal */
  .canal .guia.activa{ background:var(--canal-color); border-color:var(--canal-color); color:#151515; }
  .canal-master{ margin-left:8px; position:relative; }
  .canal-master::before{
    content:""; position:absolute; left:-9px; top:12px; bottom:12px; width:1px; background:var(--linea-fuerte);
  }
  .canal-master{ overflow:visible; }
  .canal-master .canal-cap{ border-radius:var(--r-m) var(--r-m) 0 0; }
  /* celular en vertical: los 7 canales entran en una sola vista */
  @media (max-width: 600px){
    .consola{ gap:4px; }
    .canal-nombre{ font-size:10px; padding:0 2px; margin:10px 0 8px; }
    .canal-valor{ font-size:10px; }
    .canal-botones{ width:calc(100% - 6px); }
    .canal .mute, .canal .guia{ font-size:10px; padding:6px 0; }
    .canal-master{ margin-left:6px; }
    .canal-master::before{ left:-6px; }
    .cajon .panel-plegable-cuerpo{ padding:4px 10px 16px; }
    .cajon .panel-plegable-cabecera{ padding-left:14px; padding-right:10px; }
    .cajon-cabecera{ padding-left:14px; }
  }
  @media (max-width: 420px){
    .canal-nombre{ font-size:9px; letter-spacing:-.02em; padding:0 1px; text-overflow:clip; }
  }
  /* celular: la barra de transporte en 3 filas compactas
       [ tiempo ─────── seek ]
       [ accesos rápidos ]
       [ ⏮ ▶ ‹c.1›   Cinta Cuenta ]
       [ Este compás A B ✕ Claqueta  sin loop ] */
  @media (max-width: 600px){
    .barra-transporte{
      display:grid; grid-template-columns:1fr auto;
      grid-template-areas:"rapidos rapidos" "linea linea" "botones vista" "loop loop";
      gap:8px; align-items:center;
    }
    #transporte, #barra-estudio{ display:contents; }
    .transporte-linea{ grid-area:linea; }
    .transporte-botones{ grid-area:botones; }
    #barra-estudio > .estudio-grupo:first-child{
      grid-area:loop; flex-wrap:nowrap; padding-top:8px; border-top:1px solid var(--linea); min-width:0;
    }
    #barra-estudio > .estudio-grupo:last-child{ grid-area:vista; flex-wrap:nowrap; justify-self:end; }
    .estudio-tit{ display:none; }
    .estudio-valor{ min-width:0; font-size:10.5px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
    .barra-estudio .boton-chico{ padding-left:8px; padding-right:8px; white-space:nowrap; }
  }

  /* --- v90: accesos rápidos (mute por pista + gafas) --------------------- */
  .rapidos{
    display:flex; align-items:center; justify-content:center; gap:8px;
    padding-bottom:10px; margin-bottom:10px; border-bottom:1px solid var(--linea);
  }
  .rapido{
    --rc:var(--brass);
    position:relative; flex:0 0 auto; width:42px; height:42px; padding:0;
    display:inline-flex; align-items:center; justify-content:center;
    border-radius:50%; cursor:pointer;
    background:color-mix(in srgb, var(--rc) 14%, var(--panel-2));
    border:1.5px solid color-mix(in srgb, var(--rc) 55%, transparent);
    color:var(--rc);
    transition:opacity .15s, background .15s, transform .1s;
  }
  .rapido:active{ transform:scale(.94); }
  .rapido svg{ width:22px; height:22px; }
  .rapido.muted{ --rc:var(--led-mute); background:var(--led-mute); border-color:var(--led-mute); color:#fff; }
  .rapido.guia{ border-style:dashed; opacity:.8; }
  .rapidos-sep{ width:1px; height:26px; background:var(--linea-fuerte); margin:0 4px; }
  .rapido-gafas.buscando{ animation:latido 1.4s ease-in-out infinite; }
  .rapido-gafas.enlazado{ --rc:var(--ok); }
  .rapido-gafas.transmitiendo{ --rc:var(--ok); border-style:dashed; }
  @media (max-width: 600px){
    .rapidos{ grid-area:rapidos; gap:6px; padding-bottom:8px; margin-bottom:0; }
    .rapido{ width:38px; height:38px; }
    .rapido svg{ width:20px; height:20px; }
  }
  @media (max-width: 380px){
    .rapidos{ gap:4px; }
    .rapido{ width:34px; height:34px; }
  }

  /* --- barra de estudio: loop A-B, claqueta y velocidad ------------------- */
  .barra-estudio{
    display:flex; flex-wrap:wrap; align-items:center; justify-content:space-between;
    gap:8px 18px; padding-top:10px; margin-top:10px;
    border-top:1px solid var(--linea);
  }
  .estudio-grupo{ display:flex; align-items:center; gap:4px; flex-wrap:wrap; }
  .estudio-tit{ font-size:11.5px; color:var(--fg-tenue); margin-right:4px; font-weight:550; }
  .estudio-valor{ font-family:var(--mono); font-size:11.5px; color:var(--fg-dim); min-width:80px; margin-left:4px; }
  .estudio-valor:empty{ min-width:0; margin:0; }
  .estudio-valor.activo{ color:var(--brass); }
  /* velocidades como control segmentado */
  .estudio-vels{ display:flex; gap:2px; background:var(--panel-2); border-radius:var(--r-s); padding:2px; }
  .estudio-vels .boton-chico{ background:transparent; border-radius:7px; }
  .estudio-vels .boton-chico:hover{ background:var(--panel-3); }
  .estudio-vels .boton-chico.marcado{ background:var(--brass); color:var(--sobre-acento); }
  .barra-estudio .boton-chico{ padding:7px 10px; }
  #loop-limpiar svg{ width:14px; height:14px; }

  /* --- cuerpo de los ajustes generales ------------------------------------ */
  .panel-generales-cuerpo{
    display:grid; grid-template-columns:repeat(auto-fit, minmax(200px, 1fr));
    gap:14px; align-items:start;
  }
  .grupo-ancho{ grid-column:1 / -1; min-width:0; }
  @media (max-width: 700px){ .grupo-ancho{ grid-column:1 / -1; } }
  /* los chips de estado del HUD dentro de un grupo: sobre panel-2 necesitan
     su propio fondo para leerse como pastilla */
  .grupo #chip-hud-estado, .grupo #chip-hud-ble, .grupo #chip-hud-ble-local{
    background:var(--panel); align-self:flex-start;
  }
  .grupo-nota{
    font-size:11.5px; color:var(--fg-dim); line-height:1.55; opacity:.85; margin-top:2px;
  }
  .grupo-nota strong{ color:var(--fg); font-weight:600; }
  /* --- color de la barra según la duración --------------------------------
     Interruptor + tres filas (corto / normal / largo). Cada fila muestra una
     muestra de la barra con el largo aproximado de esa banda y el color
     elegido, y la paleta de los 6 instrumentos como cuadraditos con tilde.
     Apagado, las filas quedan atenuadas (siguen editables). */
  .interruptor{ justify-content:flex-start !important; gap:10px; text-align:left !important; }
  .interruptor-pista{
    position:relative; flex:0 0 auto; width:32px; height:18px; border-radius:999px;
    background:var(--panel); transition:background .2s;
  }
  .interruptor-pista::after{
    content:""; position:absolute; top:2px; left:2px; width:14px; height:14px; border-radius:50%;
    background:var(--fg-tenue); transition:transform .2s, background .2s;
  }
  .interruptor.destacado .interruptor-pista{ background:rgba(var(--tinta),.35); }
  .interruptor.destacado .interruptor-pista::after{ transform:translateX(14px); background:var(--brass); }
  .colores-bandas{ display:flex; flex-direction:column; gap:6px; margin-top:4px; transition:opacity .25s, filter .25s; }
  .grupo-colores:has(#toggle-color-duracion:not(.destacado)) .colores-bandas{ opacity:.45; filter:grayscale(.5); }
  .colores-fila{
    display:grid; grid-template-columns:minmax(150px, 1fr) auto; align-items:center; gap:10px 18px;
    background:var(--panel); border-radius:10px; padding:10px 12px;
  }
  .colores-info{ display:flex; flex-direction:column; gap:8px; min-width:0; }
  .colores-etiqueta{ font-size:12.5px; font-weight:600; color:var(--fg); }
  .colores-etiqueta small{ font-weight:400; color:var(--fg-dim); font-size:11.5px; margin-left:4px; }
  .colores-muestra{ display:block; height:6px; max-width:200px; border-radius:999px; background:var(--panel-3); overflow:hidden; }
  .colores-muestra i{ display:block; height:100%; border-radius:999px; background:var(--sel, var(--brass)); transition:background .25s; }
  .colores-swatches{ display:flex; gap:6px; flex-wrap:wrap; }
  .swatch-color{
    position:relative; width:28px; height:28px; border-radius:8px; padding:0; cursor:pointer;
    background:var(--sw); border:0; box-shadow:none;
    transition:transform .12s, box-shadow .15s;
  }
  .swatch-color:hover{ background:var(--sw); transform:scale(1.08); }
  .swatch-color.seleccionado{ box-shadow:0 0 0 2px var(--panel), 0 0 0 4px var(--sw); }
  /* v106: colores de la app */
  .tema-presets{ display:flex; gap:8px; flex-wrap:wrap; align-items:center; }
  .tema-elegir{ display:flex; align-items:center; gap:10px; }
  input[type=color].campo-color{
    -webkit-appearance:none; appearance:none; width:44px; height:34px; padding:3px; flex:0 0 auto;
    border:0; border-radius:999px; background:var(--panel-2); cursor:pointer;
  }
  input[type=color].campo-color::-webkit-color-swatch-wrapper{ padding:0; }
  input[type=color].campo-color::-webkit-color-swatch{ border:0; border-radius:999px; }
  input[type=color].campo-color::-moz-color-swatch{ border:0; border-radius:999px; }
  /* el degradé no sirve como color de sombra: anillo con el color del texto */
  .tema-preset-mono{ box-shadow:inset 0 0 0 1px var(--linea-fuerte); }
  .tema-preset-mono.seleccionado{ box-shadow:0 0 0 2px var(--panel), 0 0 0 4px var(--fg); }
  .swatch-color.seleccionado::after{
    content:""; position:absolute; inset:0; background:rgba(0,0,0,.72);
    -webkit-mask:var(--i-tilde) center/16px no-repeat; mask:var(--i-tilde) center/16px no-repeat;
  }
  @media (max-width: 560px){ .colores-fila{ grid-template-columns:1fr; } }

  /* --- avisos -------------------------------------------------------------- */
  .aviso{
    width:100%; max-width:1080px; margin:0 auto 14px; padding:12px 16px; font-size:13px;
    color:var(--fg); background:var(--panel);
    border:1px solid var(--linea-fuerte); border-radius:var(--r-m); text-align:center;
  }

  /* --- vista única (v86) -------------------------------------------------
     Ya no hay "vista normal" y "modo tocar": la mesa SIEMPRE usa el cartel
     escalado al espacio libre (body.modo-tocar lo pone el JS al cargar) y
     todos los controles quedan a mano: cabecera con estado, barra de
     transporte abajo y el cajón de ajustes. El botón "Modo tocar" queda en el
     DOM (lo usa el JS) pero oculto. */
  #toggle-modo-tocar{ display:none !important; }
  body.modo-tocar{ padding:14px 14px 16px; }
  body.modo-tocar .acordes-display{
    padding:calc(20px * var(--esc)) 24px calc(14px * var(--esc));
    max-width:none;
  }
  /* con el transporte abajo, el cartel se centra en el alto que queda libre;
     con el editor abierto vuelve arriba para dejarle lugar */
  body.modo-tocar .acordes-display{ margin-top:auto; margin-bottom:auto; }
  body.modo-tocar:has(#panel-editor[style*="block"]) .acordes-display{ margin-top:0; margin-bottom:12px; }
  body.modo-tocar #panel-editor{ max-width:none; }
  body.modo-tocar .cabecera-mesa{ max-width:none; }
  body.modo-tocar .setlist-nav{ max-width:none; }
  body.modo-tocar .aviso{ max-width:none; }
  .barra-transporte{ padding-left:max(16px, calc((100% - 1280px) / 2)); padding-right:max(16px, calc((100% - 1280px) / 2)); }
  /* la línea de progresión ("C mayor · vi–IV–V–I") va en la esquina del
     cartel para no robarle alto a la escala; en angosto vuelve abajo */
  @media (min-width: 1100px){
    body.modo-tocar .linea-progresion{ position:absolute; top:14px; right:18px; margin:0; font-size:11.5px; }
  }
  /* el transporte crece con el mismo factor que el cartel, entre 1x y 1.6x:
     nunca más chico que el tamaño base (en el celular la escala es < 1) */
  body.modo-tocar #play{
    width:calc(48px * clamp(1, var(--esc), 1.6)); height:calc(48px * clamp(1, var(--esc), 1.6));
    --play-icono:calc(18px * clamp(1, var(--esc), 1.6));
  }
  body.modo-tocar #rebobinar{
    min-width:calc(40px * clamp(1, var(--esc), 1.6)); min-height:calc(40px * clamp(1, var(--esc), 1.6));
  }
  body.modo-tocar #rebobinar svg{ width:calc(20px * clamp(1, var(--esc), 1.6)); height:calc(20px * clamp(1, var(--esc), 1.6)); }
  body.modo-tocar .compas-nav button{
    min-width:calc(32px * clamp(1, var(--esc), 1.6)); min-height:calc(32px * clamp(1, var(--esc), 1.6));
  }
  body.modo-tocar .compas-nav button svg{ width:calc(16px * clamp(1, var(--esc), 1.6)); height:calc(16px * clamp(1, var(--esc), 1.6)); }
  body.modo-tocar #compas-num{ font-size:calc(12.5px * clamp(1, var(--esc), 1.5)); }
  body.modo-tocar #tiempo{ font-size:calc(12px * clamp(1, var(--esc), 1.5)); }

  /* --- ajustes abiertos: lo principal queda deshabilitado ------------------
     Mientras el cajón está abierto, cabecera, cartel, editor y transporte se
     apagan a gris de a poco y no reciben toques (además el JS de la UI les
     pone "inert" y ataja Espacio/V). Al cerrar vuelven con la misma
     transición. */
  .cabecera-mesa, .setlist-nav, .acordes-display, #panel-transporte, #panel-editor, #acordes-advertencia{
    transition:filter .45s ease, opacity .45s ease;
  }
  body.cajon-abierto .cabecera-mesa,
  body.cajon-abierto .setlist-nav,
  body.cajon-abierto .acordes-display,
  body.cajon-abierto #panel-transporte,
  body.cajon-abierto #panel-editor,
  body.cajon-abierto #acordes-advertencia{
    filter:grayscale(1) brightness(.55); opacity:.8; pointer-events:none; user-select:none;
  }

  /* PWA a pantalla completa: se respetan las zonas seguras de Android */
  @supports (padding: env(safe-area-inset-left)){
    body{
      padding-left:max(16px, env(safe-area-inset-left));
      padding-right:max(16px, env(safe-area-inset-right));
      padding-bottom:max(40px, env(safe-area-inset-bottom));
    }
    body.modo-tocar{
      padding-left:max(12px, env(safe-area-inset-left));
      padding-right:max(12px, env(safe-area-inset-right));
      padding-bottom:max(16px, env(safe-area-inset-bottom));
    }
    body:has(#panel-transporte){ padding-bottom:calc(var(--alto-transporte, 150px) + 24px); }
  }

  @media (max-width: 700px){
    body{ padding:16px 12px 32px; }
    .buscador{ width:100%; }
    .lista-cabecera{ flex-wrap:wrap; }
  }
  /* cabecera de la mesa en angosto: los chips que dicen "todo bien" quedan
     solo con el punto (el texto sigue en el title/tooltip); los que avisan
     un problema o son una acción conservan el texto */
  @media (max-width: 900px){
    .cabecera-mesa .volver-texto{ display:none; }
    .cabecera-mesa .boton-icono.con-texto:first-child{ padding:8px; }
    #chip-red.en-linea .texto, #chip-pedal:not(.sin-pedal) .texto{ display:none; }
    #chip-red.en-linea, #chip-pedal:not(.sin-pedal){ padding:7px 9px; }
  }
  @media (max-width: 760px){
    .solo-ancho{ display:none; }
    .boton-icono.con-texto{ padding:8px; }
    .cabecera-mesa h1{ font-size:16px; }
    .transporte{ flex-wrap:wrap; row-gap:8px; }
    .transporte-linea{ flex-basis:100%; order:-1; }
  }

  /* --- dedos en vez de mouse ----------------------------------------------
     La tablet está en el atril: se llevan los controles al mínimo táctil
     (44px) sin tocar nada en el monitor de la PC (pointer:coarse no aplica
     con mouse). */
  @media (pointer: coarse){
    button, .boton-chico{ min-height:44px; padding-top:11px; padding-bottom:11px; }
    .boton-icono{ min-width:44px; }
    .cancion-acciones{ width:46px; }
    .renombrar-cancion, .borrar-cancion{ min-height:0; }
    .compas-nav button{ min-width:44px; }
    .celda{ min-height:44px; width:56px; }
    input.fader::-webkit-slider-thumb{ width:34px; height:18px; margin-top:-6px; }
    input.fader::-moz-range-thumb{ width:34px; height:18px; }
    .canal .mute, .canal .guia{ min-height:38px; padding:8px 4px; }
    .compas-play{ min-height:0; width:36px; height:32px; }
    .swatch-color{ min-height:0; width:34px; height:34px; }
    .celda-rasgueo{ min-height:0; height:14px; }
    .setlist-fila-acciones button{ min-width:40px; }
    #chip-offline{ min-height:36px; padding-top:7px; padding-bottom:7px; }
    /* seek: se agranda SOLO el tirador, no la barra (lleva el tramo del loop
       pintado en 4px de alto) */
    input[type=range]#seek::-webkit-slider-thumb{ width:22px; height:22px; margin-top:-9px; }
    input[type=range]#seek::-moz-range-thumb{ width:22px; height:22px; }
  }
  /* ==========================================================================
     v102 — rediseño: estructura visible + modo claro / oscuro
     Va al final a propósito: son reglas que pisan a las de arriba sin tocar
     su estructura. La geometría del cartel (todo lo medido en px * --esc)
     sigue igual. Reglas del rediseño:
       1. Cada sección es un bloque con su propia superficie y borde: la
          página (--bg) es un tono, los bloques (--panel) otro, y lo que se
          toca adentro (--panel-2) otro más.
       2. Blanco, negro y grises. Colores con significado, iguales en los dos
          modos: rojo = mute / borrar, celeste = cambio de rasgueo, y la
          paleta de la barra según la duración del acorde.
       3. El modo (claro / oscuro) son solo variables: ver :root[data-tema].
     ========================================================================== */
  body{ letter-spacing:-.003em; }
  ::selection{ background:var(--fg); color:var(--bg); }
  .panel{ border-color:var(--linea-fuerte); }

  /* --- botones ------------------------------------------------------------- */
  .boton-chico{ border-color:var(--linea); }
  .boton-chico.destacado{ color:var(--fg); border-color:rgba(var(--tinta),.55); background:rgba(var(--tinta),.10); }
  .boton-chico.marcado{ color:var(--sobre-acento); }
  .boton-primario:hover{ background:var(--fg-dim); border-color:var(--fg-dim); }
  input:focus, select:focus{ border-color:rgba(var(--tinta),.7); }
  /* en "agregar canción" el botón se enciende recién cuando hay algo para mandar */
  .fila-carga .boton-primario, .fila-carga .boton-youtube{
    background:var(--panel-3); border-color:var(--linea); color:var(--fg);
  }
  .fila-carga .boton-primario:hover, .fila-carga .boton-youtube:hover{ background:var(--panel-4); }
  .fila-carga:has(input:valid) .boton-primario,
  .fila-carga:has(input:valid) .boton-youtube{ background:var(--fg); border-color:var(--fg); color:var(--sobre-acento); }

  /* botón de modo claro / oscuro (lo inserta el script de la base) */
  #toggle-tema{ flex:0 0 auto; }
  #toggle-tema .ico-sol{ display:none; }
  :root[data-tema="claro"] #toggle-tema .ico-sol{ display:block; }
  :root[data-tema="claro"] #toggle-tema .ico-luna{ display:none; }
  #toggle-tema.suelto{ position:fixed; top:12px; right:12px; z-index:700; }

  /* --- portada --------------------------------------------------------------
     Cabecera con las acciones, y debajo un bloque por sección. */
  .cabecera-portada{ margin:4px 0 16px; flex-wrap:nowrap; }
  .cabecera-portada h1{ font-size:26px; font-weight:700; letter-spacing:-.035em; gap:11px; flex:1 1 auto; min-width:0; }
  .cabecera-portada h1 span:not(.marca-app){ font-size:13.5px; letter-spacing:0; color:var(--fg-tenue); font-weight:450; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  .marca-app{ background:var(--fg); color:var(--sobre-acento); width:34px; height:34px; border-radius:9px; }
  #toggle-carga{ flex:0 0 auto; background:var(--fg); border-color:var(--fg); color:var(--sobre-acento); font-weight:650; padding:9px 14px 9px 10px; }
  #toggle-carga:hover{ background:var(--fg-dim); border-color:var(--fg-dim); }
  #toggle-carga[aria-expanded="true"]{ background:var(--panel-2); border-color:var(--linea-fuerte); color:var(--fg); }
  #toggle-carga[aria-expanded="true"] svg{ transform:rotate(45deg); }
  #toggle-carga svg{ transition:transform .15s; }
  @media (max-width: 560px){
    .cabecera-portada h1 span:not(.marca-app){ display:none; }
    #toggle-carga .solo-ancho{ display:none; }
    #toggle-carga{ padding:9px; }
  }

  .panel-carga{ display:none; gap:10px; padding:14px; margin-bottom:0; }
  .panel-carga.abierta{ display:grid; }
  .fila-carga{
    background:var(--panel-2); border:1px solid var(--linea); border-radius:12px;
    padding:8px 8px 8px 12px; gap:10px;
  }
  .fila-carga:focus-within{ border-color:rgba(var(--tinta),.55); }
  .fila-carga-icono{ width:30px; height:30px; padding:4px; background:transparent; opacity:.8; }
  .fila-carga-label{ color:var(--fg-dim); font-weight:500; }
  .fila-carga button{ border-radius:9px; padding:10px 16px; }

  /* cada sección de la portada es un bloque */
  .lista{
    margin-top:14px; background:var(--panel); border:1px solid var(--linea-fuerte);
    border-radius:var(--r-l); padding:16px 18px 18px;
  }
  .lista h2{ font-size:15px; font-weight:650; color:var(--fg); letter-spacing:-.01em; margin:0 0 14px; }
  .lista-cabecera{
    flex-wrap:wrap; gap:10px; margin:-16px -18px 14px; padding:14px 18px;
    border-bottom:1px solid var(--linea-fuerte);
  }
  .lista-cabecera h2{ margin:0; flex:0 0 auto; }

  .setlist-chip{ background:var(--panel-2); border-color:var(--linea-fuerte); border-radius:10px; padding:10px 14px; }
  .setlist-chip:hover{ background:var(--panel-3); border-color:rgba(var(--tinta),.55); }
  .setlist-chip .cant{ background:var(--panel); border:1px solid var(--linea); color:var(--fg-dim); }
  .setlist-crear input, .setlist-crear input[type=text], .setlist-crear button{ border-radius:10px; }
  .setlist-crear button{ border-color:var(--linea-fuerte); }

  /* buscador: en la cabecera del bloque, ancho */
  .lista-cabecera .buscador{
    order:2; flex:1 1 220px; width:auto; min-width:0; font-size:14.5px; padding:10px 14px 10px 40px;
    border-radius:10px; border-color:var(--linea-fuerte); background-color:var(--panel-2);
    background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='%23888888' stroke-width='2' stroke-linecap='round'%3E%3Ccircle cx='11' cy='11' r='6.5'/%3E%3Cpath d='M16 16l4.5 4.5'/%3E%3C/svg%3E");
    background-repeat:no-repeat; background-position:13px center; background-size:17px;
  }
  input.buscador{ border-radius:10px; }
  .lista-cabecera .buscador:focus{ border-color:rgba(var(--tinta),.7); }
  select.orden-canciones{ order:3; }
  #descargar-todas{ order:4; }
  select.orden-canciones, #descargar-todas{
    background:var(--panel-2); border:1px solid var(--linea-fuerte); border-radius:10px;
    color:var(--fg-dim); font-size:12.5px; padding:10px 12px;
  }
  select.orden-canciones:hover, #descargar-todas:hover{ color:var(--fg); background:var(--panel-3); }
  select.orden-canciones option{ background:var(--panel-2); color:var(--fg); }

  /* canciones: cada una en su recuadro, sin el color al azar por tema */
  .cancion::before{ display:none; }
  .grid-canciones{ gap:10px; }
  .cancion{
    background:var(--panel-2); border:1px solid var(--linea-fuerte); border-radius:12px; padding:13px 15px;
  }
  .cancion:hover{ background:var(--panel-3); border-color:rgba(var(--tinta),.5); }
  .cancion-autor.sin-autor{ visibility:hidden; }

  /* "Últimas que abriste": una tira que se desliza de costado */
  .grid-canciones-recientes{
    display:flex; gap:10px; overflow-x:auto; scrollbar-width:none; scroll-snap-type:x proximity;
  }
  .grid-canciones-recientes::-webkit-scrollbar{ display:none; }
  .grid-canciones-recientes .cancion-fila{ flex:0 0 200px; scroll-snap-align:start; }
  .grid-canciones-recientes .cancion-nombre{ min-height:0; display:block; white-space:nowrap; text-overflow:ellipsis; }

  /* la lista completa: el recuadro es la fila entera (canción + acciones) */
  #grid-todas{ grid-template-columns:repeat(auto-fill, minmax(300px, 1fr)); align-items:start; }
  @media (max-width: 400px){ #grid-todas{ grid-template-columns:1fr; } }
  #grid-todas .cancion-fila{
    align-items:stretch; gap:0; min-width:0; overflow:hidden;
    background:var(--panel-2); border:1px solid var(--linea-fuerte); border-radius:12px;
    transition:border-color .14s, background .14s;
  }
  #grid-todas .cancion-fila:hover{ border-color:rgba(var(--tinta),.5); }
  #grid-todas .cancion{ background:transparent; border:0; border-radius:0; gap:2px; padding:13px 8px 13px 15px; }
  #grid-todas .cancion:hover{ background:var(--panel-3); }
  #grid-todas .cancion-nombre{
    font-size:15px; font-weight:600; letter-spacing:-.01em; line-height:1.3;
    min-height:0; display:block; white-space:nowrap; text-overflow:ellipsis;
  }
  #grid-todas .cancion-autor{ font-size:12.5px; }
  #grid-todas .cancion-autor.sin-autor{ visibility:visible; font-size:0; }
  #grid-todas .cancion-autor.sin-autor::after{ content:"sin autor"; font-size:12.5px; color:var(--fg-tenue); }
  #grid-todas .cancion-acciones{
    flex-direction:row; align-items:center; width:auto; gap:0; padding:0 6px;
    border-left:1px solid var(--linea);
  }
  #grid-todas .renombrar-cancion, #grid-todas .borrar-cancion{
    flex:0 0 auto; width:34px; height:34px; border-radius:8px;
    background:transparent; border-color:transparent; color:var(--fg-dim);
  }
  #grid-todas .renombrar-cancion:hover{ color:var(--fg); background:var(--panel-3); border-color:transparent; }
  #grid-todas .borrar-cancion:hover{ color:var(--led-mute); background:var(--panel-3); border-color:transparent; }
  #grid-todas .borrar-cancion.confirmando{
    width:auto; padding:0 12px; font-size:11.5px; font-weight:650;
    color:#fff; background:var(--led-mute); border-color:var(--led-mute);
  }
  #grid-todas .cancion-editar{ padding:12px; }
  #grid-todas .cancion-editar:hover{ background:transparent; }
  @media (hover: hover) and (pointer: fine){
    .cancion-acciones{ opacity:1; }
  }
  .marca-offline{
    top:50%; right:10px; transform:translateY(-50%);
    background:transparent; border-color:rgba(var(--tinta),.35); color:var(--fg-dim);
  }
  .grid-canciones-recientes .marca-offline{ top:10px; transform:none; }
  .cancion.descargada .cancion-nombre{ padding-right:26px; }
  .vacio{ border-color:var(--linea-fuerte); border-radius:12px; padding:32px 24px; }
  .resumen-offline{ margin-top:18px; }

  /* --- chips de estado ------------------------------------------------------ */
  #chip-red, #chip-pedal, #chip-hud-estado, #chip-hud-ble, #chip-hud-ble-local, #chip-offline{
    background:var(--panel-2); border-color:var(--linea-fuerte);
  }
  #chip-red.en-linea .punto{ box-shadow:none; }
  #chip-red.sin-red{ border-style:dashed; }
  #chip-pedal.sin-pedal{ color:var(--fg); border-color:rgba(var(--tinta),.45); border-style:dashed; background:transparent; }
  #chip-pedal.sin-pedal .punto{ background:var(--led-off); }
  #chip-capo{ background:var(--panel-2); border-color:rgba(var(--tinta),.35); }
  /* v103: el punto de "en línea" y de "pedal conectado" toma el verde de la
     paleta de instrumentos (--c-other); el chip de cejilla, el celeste
     (--c-bass), para que se vea mejor sobre el cartel. Los estados de alerta
     (sin red, pedal desconectado) siguen como estaban. */
  #chip-red.en-linea .punto, #chip-pedal:not(.sin-pedal) .punto{ background:var(--c-other); }
  #chip-capo{ color:var(--c-bass); border-color:var(--c-bass); }
  .job-chip{ border-color:var(--linea-fuerte); background:var(--panel-2); }

  /* --- mesa ------------------------------------------------------------------ */
  .cabecera-mesa h1{ font-size:19px; font-weight:650; letter-spacing:-.02em; }
  .acordes-display{ background:var(--panel); border:1px solid var(--linea-fuerte); border-radius:20px; }
  .acorde-grande{ color:var(--fg); }
  .grado-chico{ color:var(--fg-dim); opacity:.8; }
  .cuenta-regresiva{ background:rgba(var(--fondo),.80); }
  .barra-acorde{ background:var(--panel-3); }
  .cinta{ border-top:1px solid var(--linea); border-bottom:1px solid var(--linea); border-radius:0; }
  #panel-editor{ border-color:var(--linea-fuerte); }
  .compas{ border-color:var(--linea); }
  .compas.sonando{ background:rgba(var(--tinta),.08); border-color:var(--fg); }

  /* accesos directos a cada grupo de ajustes (cabecera de la mesa) */
  .accesos-ajustes{ display:flex; align-items:center; gap:0; flex:0 0 auto;
    background:var(--panel); border:1px solid var(--linea-fuerte); border-radius:11px; padding:2px; }
  .accesos-ajustes .boton-chico{ background:transparent; border-color:transparent; padding:7px 10px; gap:6px; border-radius:8px; }
  .accesos-ajustes .boton-chico:hover{ background:var(--panel-3); }
  .accesos-ajustes .boton-chico.destacado{ background:var(--fg); color:var(--sobre-acento); border-color:var(--fg); }
  .accesos-ajustes .boton-chico + .boton-chico{ margin-left:1px; }
  @media (max-width: 760px){ .accesos-ajustes .solo-ancho{ display:none; } .accesos-ajustes .boton-chico{ padding:8px; } }
  /* celular: no entran; queda el botón "Ajustes" de siempre, que abre todo */
  @media (max-width: 600px){ .accesos-ajustes{ display:none; } }
  @media (min-width: 601px){ #abrir-ajustes{ display:none; } }

  /* cajón abierto en UNA sección: se ve solo ese grupo, ya desplegado (no
     cambia la preferencia de plegado, que sigue valiendo para "todo") */
  body[data-seccion] .cajon .panel-plegable{ display:none; }
  body[data-seccion="mezcla"] #panel-mezcla,
  body[data-seccion="tema"] #panel-controles,
  body[data-seccion="generales"] #panel-generales,
  body[data-seccion="gafas"] #panel-generales{ display:block; border-bottom:0; }
  body[data-seccion] .cajon .panel-plegable-cabecera{ display:none; }
  body[data-seccion] .cajon .panel-plegable .panel-plegable-cuerpo{ display:block; padding-top:18px; }
  body[data-seccion] .cajon .panel-plegable .panel-controles-cuerpo,
  body[data-seccion] .cajon .panel-plegable .panel-generales-cuerpo{ display:grid; }
  body[data-seccion="gafas"] #panel-generales .grupo:not(.grupo-gafas){ display:none; }
  body[data-seccion="generales"] #panel-generales .grupo-gafas{ display:none; }

  /* barra de transporte: superficie propia y, con ancho, dos filas en vez de
     tres: [ transporte ] / [ loop · mutes rápidos · vista ] */
  .barra-transporte{ background:var(--barra-bg); border-top:1px solid var(--linea-fuerte); box-shadow:none; }
  #play{ box-shadow:none; color:var(--sobre-acento); }
  #play:hover{ background:var(--fg-dim); }
  input[type=range]#seek::-webkit-slider-thumb{ box-shadow:0 0 0 4px rgba(var(--tinta),.16); }
  @media (min-width: 900px){
    .barra-transporte{
      display:grid; grid-template-columns:1fr auto 1fr; align-items:center; gap:10px 18px;
      grid-template-areas:"transporte transporte transporte" "loop rapidos vista";
    }
    #transporte{ grid-area:transporte; }
    #barra-estudio{ display:contents; }
    #barra-estudio > .estudio-grupo:first-child{ grid-area:loop; flex-wrap:nowrap; min-width:0; }
    #barra-estudio > .estudio-grupo:last-child{ grid-area:vista; justify-self:end; flex-wrap:nowrap; }
    .rapidos{ grid-area:rapidos; padding:0; margin:0; border:0; }
    #transporte{ padding-bottom:10px; border-bottom:1px solid var(--linea); }
  }

  /* accesos rápidos: grises; el único color es el rojo de la pista muteada */
  .rapido{ background:var(--panel-2); border:1.5px solid var(--linea-fuerte); color:var(--fg); }
  .rapido:hover{ background:var(--panel-3); }
  .rapido.muted{ background:var(--led-mute); border-color:var(--led-mute); color:#fff; }
  .rapido.muted:hover{ background:var(--led-mute); }
  .rapido.guia{ border-color:rgba(var(--tinta),.6); }
  /* gafas conectadas = botón pleno */
  .rapido-gafas.enlazado, .rapido-gafas.transmitiendo{ background:var(--fg); border-color:var(--fg); color:var(--sobre-acento); border-style:solid; }
  .rapido-gafas.buscando{ border-color:rgba(var(--tinta),.6); border-style:dashed; }

  /* consola: los canales ya no llevan el color del instrumento */
  .canal{ --canal-color:var(--fg) !important; border-color:var(--linea-fuerte); }
  .canal.canal-master{ --canal-color:var(--fg-dim) !important; }
  .canal-cap{ display:none; }
  .canal .guia.activa{ color:var(--sobre-acento); }
  .canal .mute, .canal .guia{ border-color:var(--linea); }
  input.fader::-webkit-slider-thumb{ box-shadow:0 0 0 1px var(--linea-fuerte), 0 2px 6px rgba(0,0,0,.35); }

  .cajon{ background:var(--bg); }
  .cajon-fondo{ background:rgba(0,0,0,.5); }
  .cajon-cabecera{ border-bottom-color:var(--linea-fuerte); }
  .cajon .panel{ border-bottom-color:var(--linea-fuerte); }
  .grupo{ border:1px solid var(--linea-fuerte); background:var(--panel); }
  .grupo-titulo{ color:var(--fg); font-size:13px; font-weight:650; padding-bottom:8px; margin-bottom:4px; border-bottom:1px solid var(--linea); }
  .grupo .boton-chico{ background:var(--panel-2); }
  .grupo .boton-chico:hover{ background:var(--panel-3); }
  .grupo .boton-chico.destacado{ background:rgba(var(--tinta),.10); }
  .grupo .boton-chico.marcado{ background:var(--fg); color:var(--sobre-acento); }
  .grupo .boton-chico.peligro{ background:rgba(209,75,60,.10); }
  .grupo .boton-chico.confirmando{ background:var(--led-mute); }
  input.campo-chico{ background:var(--panel-2); }
  .grupo #chip-hud-estado, .grupo #chip-hud-ble, .grupo #chip-hud-ble-local{ background:transparent; }
  .colores-fila{ background:var(--panel-2); border:1px solid var(--linea); }
  .interruptor-pista{ background:var(--panel-4); }
  .interruptor.destacado .interruptor-pista{ background:var(--fg); }
  .interruptor.destacado .interruptor-pista::after{ background:var(--sobre-acento); }
  #mesa-toast{ background:var(--fg); color:var(--sobre-acento); border-color:var(--fg); box-shadow:0 12px 40px rgba(0,0,0,.45); }
  #mesa-toast.error{ background:var(--panel-3); color:var(--fg); border-color:var(--led-mute); }

</style>
<!-- v106: la capa visual v105 (fuentes, píldoras, degradés, color por sección)
     vive en su propio <style> para poder apagarla con el estilo "blanco y negro"
     (como app103). El servidor la deja apagada de entrada si esa es la
     preferencia; mesaColorBase() la prende/apaga en vivo. -->
<style id="estilo-v105" media="not all">
  /* =====================================================================
     v105 — misma identidad visual que la app de guitarra ("escenario de
     estudio"): violeta noche con luces de color, cada bloque con su color,
     píldoras y círculos, esquinas asimétricas, botones con relieve y
     degradé. Es una capa final: solo pisa estilos, no toca estructura ni JS.
     El rojo de mute y los colores de acorde/duración quedan como estaban.
     ===================================================================== */
  h1, .lista h2, .cajon-titulo, .panel-plegable-titulo, .editor-titulo,
  .cancion-nombre, .grupo-titulo{ font-family:var(--fd); }
  h1{ font-weight:800; letter-spacing:-.01em; }
  .cabecera-portada h1{ font-size:27px; font-weight:800; letter-spacing:-.02em; }
  .cabecera-mesa h1{ font-size:19px; font-weight:800; }
  .lista h2{ font-size:19px; font-weight:700; }
  .marca-app{
    width:38px; height:38px; border-radius:50%; color:#fff;
    background:linear-gradient(135deg,var(--g1),var(--g2));
    box-shadow:0 3px 0 var(--sh1);
  }

  /* bloques */
  .panel{ border-radius:26px; border-color:var(--linea); box-shadow:0 8px 24px -14px rgba(40,20,120,.35); }
  .lista{ border-radius:30px 30px 30px 10px; border-color:var(--linea); box-shadow:0 8px 24px -14px rgba(40,20,120,.35); }
  .lista-cabecera{ border-bottom-color:var(--linea); }
  .acordes-display{ border-radius:30px 30px 30px 10px; border:2px solid color-mix(in srgb,var(--d1) 32%,var(--linea)); background:color-mix(in srgb,var(--d1) 9%,var(--panel)); }
  .cajon{ border-radius:30px 30px 0 0; border-top-color:var(--linea); box-shadow:0 -20px 50px -10px rgba(30,10,100,.5); }
  .barra-transporte{ border-radius:28px 28px 0 0; border-top:1px solid var(--linea); box-shadow:0 -10px 30px -10px rgba(30,10,100,.5); }
  .panel-plegable-cabecera:hover{ background:var(--pris); }

  /* botones: píldora; los "activos" con degradé y relieve como .btn */
  button, .boton-chico, .boton-primario, a.boton-chico{ border-radius:999px; }
  .boton-chico.boton-icono:not(.con-texto){ border-radius:50%; }
  .boton-chico, button{ font-weight:650; }
  .boton-chico.destacado{ color:var(--prit); background:var(--pris); border-color:transparent; }
  .boton-chico.destacado:hover{ background:color-mix(in srgb,var(--pris) 80%,var(--brass)); }
  .boton-primario, .boton-chico.marcado, #toggle-carga,
  .grupo .boton-chico.marcado, .estudio-vels .boton-chico.marcado{
    background:linear-gradient(135deg,var(--g1),var(--g2)); border-color:transparent; color:#fff;
    box-shadow:0 3px 0 var(--sh1);
  }
  .boton-primario:hover, .boton-chico.marcado:hover, #toggle-carga:hover{
    background:linear-gradient(135deg,var(--g1),var(--g2)); border-color:transparent; filter:brightness(1.08);
  }
  .boton-primario:active:not(:disabled), .boton-chico.marcado:active:not(:disabled), #toggle-carga:active{
    transform:translateY(2px); box-shadow:0 1px 0 var(--sh1);
  }
  #toggle-carga[aria-expanded="true"]{ background:var(--pris); color:var(--prit); box-shadow:none; }
  .fila-carga:has(input:valid) .boton-youtube{
    background:linear-gradient(135deg,var(--g1),var(--g2)); border-color:transparent; color:#fff;
  }
  #play{
    background:linear-gradient(135deg,var(--g1),var(--g2)); border-color:transparent; color:#fff;
    box-shadow:0 4px 0 var(--sh1), 0 10px 20px -8px rgba(91,61,240,.6);
  }
  #play:hover{ background:linear-gradient(135deg,var(--g1),var(--g2)); filter:brightness(1.08); }
  #play:active{ transform:translateY(3px); box-shadow:0 1px 0 var(--sh1); }
  .grupo .boton-chico.destacado{ background:var(--pris); }
  .grupo-valor.destacado-valor, .editor-estado.sin-guardar, .estudio-valor.activo{ color:var(--prit); }

  /* campos */
  input[type=text], input[type=url], input[type=number], select{ border:2px solid var(--linea); border-radius:18px; }
  input.buscador, .setlist-crear input, .setlist-crear input[type=text], select.orden-canciones{ border-radius:999px; }
  input:focus, select:focus{ border-color:var(--brass); }
  .fila-carga{ border-radius:22px; }
  .fila-carga button{ border-radius:999px; }
  .setlist-chip{ border-radius:999px; background:var(--pris); color:var(--prit); border-color:transparent; font-weight:650; }
  .setlist-chip:hover{ background:color-mix(in srgb,var(--pris) 78%,var(--brass)); border-color:transparent; }
  .setlist-nav-nombre{ background:var(--pris); color:var(--prit); font-weight:700; }

  /* canciones: ficha teñida con el color de cada tema, esquinas alternadas */
  #grid-todas .cancion-fila, .grid-canciones-recientes .cancion-fila{
    --c:var(--borde, var(--d1));
    background:color-mix(in srgb,var(--c) 13%,var(--panel));
    border:2px solid color-mix(in srgb,var(--c) 38%,var(--linea));
    border-radius:24px;
  }
  #grid-todas .cancion-fila:nth-child(2n), .grid-canciones-recientes .cancion-fila:nth-child(2n){ border-radius:24px 24px 8px 24px; }
  #grid-todas .cancion-fila:nth-child(3n), .grid-canciones-recientes .cancion-fila:nth-child(3n){ border-radius:8px 24px 24px 24px; }
  #grid-todas .cancion-fila:hover, .grid-canciones-recientes .cancion-fila:hover{
    border-color:color-mix(in srgb,var(--c) 70%,var(--linea)); background:color-mix(in srgb,var(--c) 20%,var(--panel));
  }
  #grid-todas .cancion:hover, .grid-canciones-recientes .cancion:hover{ background:transparent; }
  .cancion-nombre{ font-weight:700; font-size:15px; }
  .cancion-autor{ color:var(--mut, var(--fg-dim)); }

  /* panel de ajustes: cada grupo con su color, título tipo "eyebrow" */
  .grupo{
    --c:var(--d1);
    background:color-mix(in srgb,var(--c) 9%,var(--panel));
    border:2px solid color-mix(in srgb,var(--c) 28%,var(--linea));
    border-radius:26px 26px 26px 8px; padding:16px;
  }
  .grupo:nth-child(5n+2){ --c:var(--d2); }
  .grupo:nth-child(5n+3){ --c:var(--d3); }
  .grupo:nth-child(5n+4){ --c:var(--d4); }
  .grupo:nth-child(5n+5){ --c:var(--d5); }
  .grupo-titulo{
    display:inline-block; align-self:flex-start; font:700 11.5px var(--sans); letter-spacing:.09em; text-transform:uppercase;
    padding:6px 11px; border-radius:999px; margin-bottom:4px;
    color:color-mix(in srgb,var(--c) 62%,var(--fg)); background:color-mix(in srgb,var(--c) 16%,var(--panel-2));
  }
  .grupo .boton-chico{ background:color-mix(in srgb,var(--c) 14%,var(--panel-2)); }
  .grupo .boton-chico:hover{ background:color-mix(in srgb,var(--c) 24%,var(--panel-2)); }
  .grupo .boton-chico.destacado{ background:color-mix(in srgb,var(--c) 30%,var(--panel-2)); color:var(--fg); }
  .grupo .boton-chico.peligro{ background:rgba(209,75,60,.10); }
  .grupo .boton-chico.confirmando{ background:var(--led-mute); }
  .interruptor.destacado .interruptor-pista{ background:color-mix(in srgb,var(--brass) 60%,transparent); }

  /* mezcla: cada canal con su color, tarjeta teñida */
  .canal{ --canal-color:var(--d1) !important; border-radius:22px;
    background:color-mix(in srgb,var(--canal-color) 11%,var(--panel-2));
    border:2px solid color-mix(in srgb,var(--canal-color) 32%,var(--linea)); }
  .canal:nth-child(5n+2){ --canal-color:var(--d2) !important; }
  .canal:nth-child(5n+3){ --canal-color:var(--d3) !important; }
  .canal:nth-child(5n+4){ --canal-color:var(--d4) !important; }
  .canal:nth-child(5n+5){ --canal-color:var(--d5) !important; }
  .canal-cap{ height:5px; }
  .canal-nombre{ font-family:var(--fd); font-weight:700; }
  .canal .guia.activa{ color:#fff; }
  .canal .mute, .canal .guia{ border-radius:999px; }
  input.fader::-webkit-slider-thumb{ border-radius:999px; }
  .rapido{ --rc:var(--brass); }
  .rapidos{ border-bottom-color:var(--linea); }

  /* editor de compases y barra de estudio */
  .compas{ border-radius:20px; background:color-mix(in srgb,var(--d2) 8%,var(--panel-2)); }
  .compas.sonando{ border-color:var(--brass); background:var(--pris); }
  .estudio-vels{ border-radius:999px; }
  .estudio-vels .boton-chico{ border-radius:999px; }

  /* chips de estado, aviso y toast */
  #chip-red, #chip-pedal, #chip-hud-estado, #chip-hud-ble, #chip-hud-ble-local, #chip-offline{ font-weight:650; }
  #mesa-toast{ border-radius:999px; }
  .aviso{ border-radius:22px; }
  .swatch-color{ border-radius:50%; }
  ::selection{ background:var(--brass); color:var(--sobre-acento); }

  /* --- v105b — retoque: más limpio y prolijo, como la app tutor ----------
     Menos bordes y rayas, fondos más suaves, más aire entre bloques. */
  .panel, .lista{ border-color:transparent; box-shadow:0 10px 28px -18px rgba(30,10,100,.55); }
  .lista{ padding:20px 20px 22px; margin-top:18px; }
  .lista-cabecera{ border-bottom:0; margin:-4px -2px 14px; padding:0; }
  .lista h2{ font-size:20px; }
  input[type=text], input[type=url], input[type=number], select{
    border-color:transparent; background:var(--panel-2);
  }
  input:focus, select:focus{ border-color:var(--brass); }
  .fila-carga{ border-color:transparent; background:var(--panel-2); }
  .fila-carga:focus-within{ border-color:var(--brass); }
  .setlist-crear button{ background:var(--panel-2); border-color:transparent; }
  select.orden-canciones, #descargar-todas{ background:var(--panel-2); border-color:transparent; }

  /* canciones: una sola ficha por tema, sin bordes dobles ni rayas internas */
  #grid-todas, .grid-canciones{ gap:12px; }
  .grid-canciones-recientes{ gap:12px; padding:2px 2px 6px; }
  #grid-todas .cancion-fila, .grid-canciones-recientes .cancion-fila{
    border-width:1.5px; overflow:hidden;
    background:color-mix(in srgb,var(--c) 9%,var(--panel));
    border-color:color-mix(in srgb,var(--c) 30%,var(--linea));
  }
  #grid-todas .cancion-fila:hover, .grid-canciones-recientes .cancion-fila:hover{
    background:color-mix(in srgb,var(--c) 15%,var(--panel));
    border-color:color-mix(in srgb,var(--c) 60%,var(--linea));
  }
  .grid-canciones-recientes .cancion{ background:transparent; border:0; border-radius:0; }
  .grid-canciones-recientes .cancion:hover{ background:transparent; }
  .cancion{ padding-top:14px; padding-bottom:14px; }
  .cancion-nombre{ font-weight:650; font-size:14.5px; letter-spacing:-.005em; }
  #grid-todas .cancion-acciones{ border-left:0; padding:0 8px 0 0; gap:2px; }
  #grid-todas .renombrar-cancion, #grid-todas .borrar-cancion{ border-radius:50%; width:32px; height:32px; }
  #grid-todas .renombrar-cancion:hover, #grid-todas .borrar-cancion:hover{ background:rgba(var(--tinta),.10); }
  #grid-todas .borrar-cancion.confirmando{ border-radius:999px; width:auto; padding:0 10px; }

  /* ajustes y mezcla: fondos suaves, bordes finos */
  .grupo{ border-width:1.5px; border-color:color-mix(in srgb,var(--c) 22%,var(--linea)); background:color-mix(in srgb,var(--c) 7%,var(--panel)); }
  .canal{ border-width:1.5px; background:color-mix(in srgb,var(--canal-color) 8%,var(--panel-2)); border-color:color-mix(in srgb,var(--canal-color) 26%,var(--linea)); }
  .acordes-display{ border-width:1.5px; background:color-mix(in srgb,var(--d1) 7%,var(--panel)); }
  .setlist-chip{ border-radius:999px; }

  /* --- v105c — panel Gafas HUD ordenado + botones activos legibles ------
     Cada botón con su estado al lado (antes el estado quedaba suelto debajo),
     y el "activo" de los grupos con color sólido y texto blanco. */
  .grupo .boton-chico.destacado{ background:linear-gradient(135deg,var(--g1),var(--g2)); color:#fff; border-color:transparent; box-shadow:0 2px 0 var(--sh1); }
  .grupo .boton-chico.destacado:hover{ background:linear-gradient(135deg,var(--g1),var(--g2)); filter:brightness(1.08); }
  /* colores más apagados: el tinte de cada grupo es apenas un matiz */
  .grupo{ background:color-mix(in srgb,var(--c) 4%,var(--panel)); border-color:color-mix(in srgb,var(--c) 14%,var(--linea)); }
  .grupo .boton-chico{ background:var(--panel-2); }
  .grupo .boton-chico:hover{ background:var(--panel-3); }
  .grupo-titulo{ background:color-mix(in srgb,var(--c) 12%,var(--panel-2)); color:color-mix(in srgb,var(--c) 45%,var(--fg)); }
  .grupo-gafas{ --c:var(--d1) !important; }
</style>
<style>
  /* v106: el orden del panel de gafas (v105c) vale con cualquier estilo */
  .grupo-gafas .grupo-cuerpo{
    display:grid; grid-template-columns:minmax(0,1fr) auto; gap:8px 10px; align-items:center;
  }
  .grupo-gafas .grupo-cuerpo > .boton-chico{ width:100%; }
  .grupo-gafas .grupo-cuerpo > .grupo-fila{ grid-column:1 / -1; }
  .grupo-gafas #chip-hud-estado, .grupo-gafas #chip-hud-ble, .grupo-gafas #chip-hud-ble-local{
    justify-self:stretch; min-width:150px; justify-content:center; margin:0;
  }
  .grupo-gafas .grupo-valor{ justify-self:end; min-width:128px; text-align:center; font-size:14px; }
  .grupo-gafas #hud-brillo-menos, .grupo-gafas #hud-brillo-mas{
    font-size:20px; font-weight:700; padding:8px 12px; line-height:1;
  }
</style>
<style id="estilo-v107">
  /* ======================================================================
     v107 — estilo "app de música": fondo oscuro neutro, superficies planas,
     círculos e íconos, acento ámbar (el dorado original de Mesa). Es la
     última capa: solo pisa estilos. El selector de color de la app sigue
     andando (sus variables van en html:root y le ganan a estas). El rojo de
     mute, el celeste de rasgueo y los colores por duración no se tocan.
     ====================================================================== */
  :root{
    --tinta:242,242,244; --fondo:14,14,17;
    --bg:#0E0E11; --panel:#15151A; --panel-2:#1B1B20; --panel-3:#26262D; --panel-4:#32323A;
    --linea:rgba(var(--tinta),.07); --linea-fuerte:rgba(var(--tinta),.12);
    --fg:#F2F2F4; --fg-dim:#A0A0AA; --fg-tenue:#8A8A94;
    --brass:#F2B33D; --sobre-acento:#1A1306; --led-off:#3A3A42; --led-mute:#E5484D;
    --ok:#7FB37A; --surco:#2A2A31; --barra-bg:rgba(19,19,23,.97);
    --glow1:transparent; --glow2:transparent;
    --diag-linea:#45454E; --diag-tenue:#8A8A94;
    --mono: "JetBrains Mono", ui-monospace, "SF Mono", "Cascadia Mono", Consolas, monospace;
    --sans: "Figtree", system-ui, -apple-system, "Segoe UI", sans-serif;
    --r-l:24px; --r-m:16px; --r-s:12px;
    --ancho-pistas:380px;
    --i-altavoz:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='black' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M4 9h4l5-4v14l-5-4H4z'/%3E%3Cpath d='M16.5 9a4 4 0 0 1 0 6'/%3E%3C/svg%3E");
    --i-mudo:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='black' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M4 9h4l5-4v14l-5-4H4z'/%3E%3Cpath d='M16.5 9.5l4.5 5M21 9.5l-4.5 5'/%3E%3C/svg%3E");
  }
  :root[data-tema="claro"]{
    --tinta:20,20,24; --fondo:255,255,255;
    --bg:#F3F3F5; --panel:#FFFFFF; --panel-2:#ECECF0; --panel-3:#E0E0E6; --panel-4:#D3D3DA;
    --linea:rgba(var(--tinta),.08); --linea-fuerte:rgba(var(--tinta),.14);
    --fg:#141418; --fg-dim:#5C5C66; --fg-tenue:#6E6E78;
    --brass:#E0A21E; --sobre-acento:#1A1306; --led-off:#CFCFD6;
    --ok:#2E7D32; --surco:#DADAE0; --barra-bg:rgba(255,255,255,.97);
    --diag-linea:#9A9AA4; --diag-tenue:#6E6E78;
  }

  /* --- base -------------------------------------------------------------- */
  body{ background:var(--bg); }
  /* en modo claro el ámbar como color de texto no se lee: se oscurece */
  :root[data-tema="claro"] .boton-chico.destacado, :root[data-tema="claro"] #compas-num,
  :root[data-tema="claro"] .riel-item.activo, :root[data-tema="claro"] .grupo .boton-chico.destacado{ color:#7A4F00; }
  h1{ font-weight:700; letter-spacing:-.02em; }
  ::selection{ background:var(--brass); color:var(--sobre-acento); }
  button, .boton-chico, a.boton-chico{ border-radius:999px; }
  .boton-chico.boton-icono:not(.con-texto){ border-radius:50%; }
  .boton-chico{ border-color:transparent; }
  .boton-chico.destacado{ color:var(--brass); background:color-mix(in srgb,var(--brass) 16%,transparent); border-color:transparent; }
  .boton-chico.destacado:hover{ background:color-mix(in srgb,var(--brass) 24%,transparent); }
  .boton-chico.marcado, .boton-primario{ background:var(--brass); border-color:var(--brass); color:var(--sobre-acento); }
  .boton-primario:hover{ background:var(--brass); border-color:var(--brass); filter:brightness(1.08); }
  input[type=text], input[type=url], input[type=number], select{ background:var(--panel-2); border-color:transparent; border-radius:14px; }
  input:focus, select:focus{ border-color:var(--brass); }
  .panel{ border-color:transparent; }
  #mesa-toast{ border-radius:16px; }

  /* botones de ícono con una etiqueta corta abajo */
  .boton-chico.btn-ico-lbl{
    flex-direction:column; gap:2px; min-width:52px; min-height:52px; padding:6px 8px;
    border-radius:14px; font-size:10px; font-weight:600; line-height:1.1;
  }
  .btn-ico-lbl svg{ width:20px; height:20px; display:block; }
  /* mosaicos (ajustes): ícono grande + nombre */
  .tiles{ display:grid; grid-template-columns:repeat(auto-fill, minmax(92px, 1fr)); gap:8px; }
  .boton-chico.tile{
    flex-direction:column; gap:6px; min-height:84px; padding:10px 6px; border-radius:16px;
    font-size:12px; font-weight:600; text-align:center;
  }
  .boton-chico.tile svg{ width:24px; height:24px; }
  .tile-romano{ font:700 19px/24px var(--mono); }

  /* --- ajustes (cajón de la mesa y de la portada) ------------------------- */
  .cajon{ background:var(--panel); }
  .grupo{ background:var(--panel-2); border:0; border-radius:18px; }
  .grupo-titulo{
    font-size:11px; font-weight:700; letter-spacing:.08em; text-transform:uppercase;
    color:var(--fg-tenue); border-bottom:0; padding-bottom:2px; margin-bottom:2px;
  }
  .grupo .boton-chico{ background:var(--panel-3); }
  .grupo .boton-chico:hover{ background:var(--panel-4); }
  .grupo .boton-chico.destacado{ background:color-mix(in srgb,var(--brass) 20%,var(--panel-3)); color:var(--brass); }
  .grupo .boton-chico.marcado{ background:var(--brass); color:var(--sobre-acento); }
  .grupo .boton-chico.peligro{ background:color-mix(in srgb,var(--led-mute) 12%,var(--panel-3)); }
  .grupo .boton-chico.confirmando{ background:var(--led-mute); color:#fff; }
  .colores-fila{ background:var(--panel); border:0; }
  .swatch-color{ border-radius:50%; }
  .interruptor-pista{ background:var(--panel-4); }
  .interruptor.destacado .interruptor-pista{ background:var(--brass); }
  .interruptor.destacado .interruptor-pista::after{ background:var(--sobre-acento); }
  .grupo-gafas .grupo-cuerpo{ display:flex; flex-direction:column; align-items:stretch; gap:10px; }
  .hud-chips{ display:flex; flex-wrap:wrap; gap:6px; }
  .grupo-gafas #chip-hud-estado, .grupo-gafas #chip-hud-ble, .grupo-gafas #chip-hud-ble-local{
    min-width:0; margin:0; background:var(--panel); justify-self:auto;
  }
  .hud-brillo{ align-items:center; }
  .grupo-gafas .hud-brillo .grupo-valor{ flex:1; text-align:center; min-width:0; font-size:14px; padding:0; }
  .grupo-gafas #hud-brillo-menos, .grupo-gafas #hud-brillo-mas{ flex:0 0 52px; }

  /* --- portada ------------------------------------------------------------ */
  .riel{ display:none; }
  .riel-logo{
    width:44px; height:44px; border-radius:12px; background:var(--brass); color:var(--sobre-acento);
    display:flex; align-items:center; justify-content:center; margin-bottom:16px;
  }
  .riel-logo svg{ width:24px; height:24px; }
  .riel-item{
    width:72px; min-height:58px; padding:8px 0; border-radius:14px; border:0; background:transparent;
    color:var(--fg-dim); text-decoration:none; display:flex; flex-direction:column; align-items:center;
    justify-content:center; gap:4px; font:600 11px var(--sans); cursor:pointer;
  }
  .riel-item svg{ width:22px; height:22px; }
  .riel-item:hover{ background:var(--panel-2); color:var(--fg); }
  .riel-item.activo{ background:color-mix(in srgb,var(--brass) 15%,transparent); color:var(--brass); }
  .riel-espacio{ flex:1; }
  @media (min-width: 900px){
    body:has(.riel){ padding-left:120px; }
    .riel{
      position:fixed; left:0; top:0; bottom:0; width:88px; z-index:600; box-sizing:border-box;
      display:flex; flex-direction:column; align-items:center; gap:8px; padding:20px 0;
      background:var(--panel); border-right:1px solid var(--linea);
    }
    .cabecera-portada .marca-app, .solo-angosto{ display:none !important; }
  }
  .cabecera-portada{ margin:4px 0 8px; }
  .cabecera-portada h1{ font-size:28px; font-weight:700; }
  .cabecera-portada .boton-icono:not(.con-texto){ width:46px; height:46px; padding:0; background:var(--panel-2); color:var(--fg); }
  #toggle-carga{ background:var(--brass); border-color:var(--brass); color:var(--sobre-acento); box-shadow:none; }
  #toggle-carga:hover{ background:var(--brass); border-color:var(--brass); filter:brightness(1.08); }
  #toggle-carga[aria-expanded="true"]{ background:var(--panel-2); border-color:transparent; color:var(--fg); filter:none; }
  .panel-carga{ background:var(--panel); }
  .fila-carga{ background:var(--panel-2); border-color:transparent; border-radius:16px; }
  .lista{ background:transparent; border:0; border-radius:0; padding:0; margin-top:28px; box-shadow:none; }
  .lista h2{ font-size:16px; font-weight:600; color:var(--fg-dim); margin:0 0 12px; letter-spacing:0; }
  .lista-cabecera{ margin:0 0 10px; padding:0; border:0; }
  .lista-cabecera .buscador{ background-color:var(--panel-2); border-color:transparent; border-radius:999px; }
  input.buscador{ border-radius:999px; }
  select.orden-canciones, #descargar-todas{ background:var(--panel-2); border-color:transparent; border-radius:999px; }
  .setlist-chip{ background:var(--panel-2); border-color:transparent; border-radius:999px; color:var(--fg); }
  .setlist-chip:hover{ background:var(--panel-3); border-color:transparent; }
  .setlist-chip .cant{ background:var(--panel); border:0; }
  .job-chip{ background:var(--panel-2); border-color:transparent; }

  /* "Últimas que abriste": tarjetas con portada (iniciales del tema) */
  .grid-canciones-recientes{ gap:16px; padding-bottom:4px; }
  .grid-canciones-recientes .cancion-fila{ flex:0 0 168px; background:transparent; border:0; border-radius:0; }
  .grid-canciones-recientes a.cancion{
    display:flex; flex-direction:column; gap:2px; padding:0; background:transparent; border:0; border-radius:0;
  }
  .grid-canciones-recientes a.cancion:hover{ background:transparent; }
  .grid-canciones-recientes a.cancion::before{
    display:flex; position:static; content:attr(data-ini); width:168px; height:128px; margin-bottom:8px;
    border-radius:16px; align-items:flex-end; padding:12px; box-sizing:border-box; opacity:1;
    font:700 34px/1 var(--mono); color:var(--borde, var(--brass));
    background:color-mix(in srgb, var(--borde, var(--brass)) 22%, var(--panel));
    transition:transform .14s;
  }
  .grid-canciones-recientes a.cancion:hover::before{ transform:scale(1.03); }
  /* ancho fijo: un título largo se corta con "…" (el completo queda en el tooltip) */
  .grid-canciones-recientes .cancion-fila{ width:168px; min-width:0; max-width:168px; overflow:hidden; }
  .grid-canciones-recientes a.cancion{ min-width:0; max-width:168px; }
  .grid-canciones-recientes .cancion-nombre, .grid-canciones-recientes .cancion-autor{
    display:block; max-width:168px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; padding-right:0;
  }
  .grid-canciones-recientes .cancion-nombre{ font-size:14px; font-weight:600; }
  .grid-canciones-recientes .cancion-autor{ font-size:12.5px; }
  .grid-canciones-recientes .marca-offline{ top:10px; right:10px; transform:none; background:var(--bg); }

  /* "Todas las canciones": lista de filas, como una biblioteca de música */
  #grid-todas{ grid-template-columns:1fr; gap:2px; }
  #grid-todas .cancion-fila{ background:transparent; border:0; border-radius:12px; }
  #grid-todas .cancion-fila:hover{ background:var(--panel-2); border-color:transparent; }
  #grid-todas a.cancion{
    display:grid; grid-template-columns:44px minmax(0, 1fr) auto;
    grid-template-areas:"ini nom bpm" "ini aut bpm"; column-gap:14px; row-gap:0;
    align-items:center; padding:8px 8px 8px 10px; background:transparent;
  }
  #grid-todas a.cancion:hover{ background:transparent; }
  #grid-todas a.cancion::before{
    display:flex; grid-area:ini; position:static; content:attr(data-ini); width:44px; height:44px;
    border-radius:10px; align-items:center; justify-content:center; opacity:1;
    font:700 14px/1 var(--mono); color:var(--borde, var(--brass));
    background:color-mix(in srgb, var(--borde, var(--brass)) 22%, var(--panel));
  }
  #grid-todas .cancion-nombre{ grid-area:nom; }
  #grid-todas .cancion-autor{ grid-area:aut; }
  #grid-todas .cancion-bpm{ grid-area:bpm; font:700 12.5px var(--mono); color:var(--fg-tenue); margin-right:30px; }
  #grid-todas .cancion-bpm::after{ content:" BPM"; font-weight:500; font-size:10.5px; }
  #grid-todas .cancion-acciones{ border-left:0; padding:0 6px 0 0; opacity:1; }
  #grid-todas .renombrar-cancion:hover, #grid-todas .borrar-cancion:hover{ background:var(--panel-3); }
  #grid-todas .marca-offline{ right:8px; }

  /* --- mesa: cabecera tipo reproductor ------------------------------------ */
  .cabecera-mesa{ gap:10px; padding-bottom:12px; margin-bottom:14px; border-bottom:1px solid var(--linea); }
  .cancion-portada{
    width:46px; height:46px; flex:0 0 auto; border-radius:12px; display:flex; align-items:center;
    justify-content:center; font:700 15px/1 var(--mono); color:var(--pc, var(--brass));
    background:color-mix(in srgb, var(--pc, var(--brass)) 22%, var(--panel));
  }
  .titulo-bloque{ flex:1 1 auto; min-width:0; display:flex; flex-direction:column; gap:1px; }
  .cabecera-mesa .titulo-bloque h1{ flex:none; font-size:18px; font-weight:700; }
  #sub-cancion{ font-size:13px; color:var(--fg-dim); white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  #sub-cancion:empty{ display:none; }
  .cabecera-mesa > .boton-chico.boton-icono, .cabecera-mesa .acciones-cabecera > .boton-chico.boton-icono{
    min-width:46px; min-height:46px; border-radius:50%; background:var(--panel-2); color:var(--fg);
  }
  .cabecera-mesa > a.boton-chico:first-child{ width:46px; height:46px; padding:0; justify-content:center; border-radius:50%; }
  .cabecera-mesa .volver-texto{ display:none; }
  .accesos-ajustes{ background:transparent; border:0; padding:0; gap:6px; }
  .accesos-ajustes .boton-chico{
    width:46px; height:46px; min-height:46px; padding:0; border-radius:50%; background:var(--panel-2); color:var(--fg);
  }
  .accesos-ajustes .boton-chico + .boton-chico{ margin-left:0; }
  .accesos-ajustes .boton-chico .solo-ancho{ display:none; }
  .accesos-ajustes .boton-chico:hover{ background:var(--panel-3); }
  .accesos-ajustes .boton-chico.destacado{ background:var(--brass); color:var(--sobre-acento); border-color:transparent; }
  .accesos-ajustes .ico{ width:21px; height:21px; }
  #mostrar-pistas{ display:none; }
  body.pistas-ocultas-ancho #mostrar-pistas{ display:inline-flex; }
  #mostrar-pistas{ width:46px; height:46px; min-height:46px; padding:0; justify-content:center; border-radius:50%; background:var(--panel-2); color:var(--fg); }
  #mostrar-pistas .ico{ width:21px; height:21px; }
  body.pistas-al-lado .accesos-ajustes [data-seccion="mezcla"]{ display:none; }
  /* estado: con todo bien, solo un círculo con su ícono; con un problema o
     trabajando, la pastilla con texto de siempre */
  .ico-chip{ display:none; width:20px; height:20px; flex:0 0 auto; }
  .cabecera-mesa #chip-red.en-linea, .cabecera-mesa #chip-pedal:not(.sin-pedal),
  .cabecera-mesa #chip-offline:not(.trabajando):not(.confirmando){
    width:46px; height:46px; padding:0; justify-content:center; border-radius:50%;
    border-color:transparent; background:var(--panel-2);
  }
  .cabecera-mesa #chip-red.en-linea .texto, .cabecera-mesa #chip-pedal:not(.sin-pedal) .texto,
  .cabecera-mesa #chip-pedal:not(.sin-pedal) .punto,
  .cabecera-mesa #chip-offline:not(.trabajando):not(.confirmando) .texto,
  .cabecera-mesa #chip-offline:not(.trabajando):not(.confirmando) .punto{ display:none; }
  .cabecera-mesa #chip-red.en-linea .punto{ width:10px; height:10px; }
  .cabecera-mesa #chip-pedal:not(.sin-pedal) .ico-chip{ display:block; color:var(--ok); }
  .cabecera-mesa #chip-offline:not(.trabajando):not(.confirmando) .ico-chip{ display:block; color:var(--fg-dim); }
  .cabecera-mesa #chip-offline.descargada .ico-chip{ color:var(--ok); }
  .setlist-nav .boton-chico{ background:var(--panel-2); }
  .setlist-nav-nombre{ background:var(--panel-2); color:var(--fg); font-weight:600; }
  @media (max-width: 600px){ .cancion-portada{ display:none; } }

  /* --- mesa: cartel + pistas al costado ----------------------------------- */
  .zona-principal{ width:100%; flex:1 1 auto; min-height:0; display:flex; gap:20px; align-items:stretch; }
  .zona-acordes{ flex:1 1 auto; min-width:0; display:flex; flex-direction:column; }
  .acordes-display{ background:var(--panel); border:0; border-radius:24px; }
  .acorde-grande{ color:var(--fg); }
  #acorde-siguiente{ color:var(--fg-dim); opacity:.5; }
  .barra-acorde{ background:var(--panel-3); }
  .cinta{ background:var(--panel-2); border:0; border-radius:14px; }
  #columna-pistas{
    display:none; flex:0 0 var(--ancho-pistas); width:var(--ancho-pistas); box-sizing:border-box;
    flex-direction:column; background:var(--panel); border-radius:24px; padding:14px 10px 10px;
    overflow-y:auto; align-self:flex-start;
  }
  body.pistas-al-lado #columna-pistas{ display:flex; }
  .pistas-cabecera{ display:flex; align-items:center; gap:8px; padding:0 4px 8px 8px; }
  .pistas-titulo{ flex:1; font-size:15px; font-weight:700; }
  #columna-pistas #panel-mezcla{ background:transparent; border:0; padding:0; margin:0; max-width:none; width:100%; }
  #columna-pistas .panel-plegable-cabecera{ display:none; }
  #columna-pistas .panel-plegable-cuerpo{ display:block !important; padding:0; }
  #columna-pistas .consola{ flex-direction:column; flex-wrap:nowrap; gap:2px; padding:0; }
  #columna-pistas .canal{
    flex:none; width:100%; max-width:none; overflow:visible; box-sizing:border-box;
    display:grid; grid-template-columns:44px minmax(0, 1fr) auto;
    grid-template-areas:"ico nom bot" "ico fad bot"; align-items:center; column-gap:12px; row-gap:4px;
    padding:6px 8px; border:0; border-radius:14px; background:transparent;
  }
  #columna-pistas .canal:has(.mute.muted){ background:color-mix(in srgb, var(--led-mute) 10%, transparent); }
  #columna-pistas .canal:has(.mute.muted) .fader-wrap, #columna-pistas .canal:has(.mute.muted) .canal-nombre{ opacity:.5; }
  #columna-pistas .canal-cap{ display:none; }
  #columna-pistas .canal-icono{ grid-area:ico; width:44px; height:44px; margin:0; border-radius:12px; }
  #columna-pistas .canal-icono svg{ width:22px; height:22px; }
  #columna-pistas .canal-nombre{ grid-area:nom; justify-self:start; margin:0; padding:0; text-align:left; font-size:13px; font-weight:600; }
  #columna-pistas .canal-valor{ grid-area:nom; justify-self:end; margin:0; font-size:11px; }
  #columna-pistas .fader-wrap{ grid-area:fad; position:relative; width:100%; height:22px; margin:0; }
  #columna-pistas input.fader{
    position:absolute; top:50%; left:0; width:100%; height:6px; margin:0; transform:translateY(-50%);
  }
  #columna-pistas input.fader::-webkit-slider-thumb{
    width:20px; height:20px; border-radius:50%; margin-top:-7px; background:var(--fg);
    box-shadow:0 1px 4px rgba(0,0,0,.4);
  }
  #columna-pistas input.fader::-moz-range-thumb{ width:20px; height:20px; border-radius:50%; background:var(--fg); }
  #columna-pistas .canal-botones{ grid-area:bot; flex-direction:row; width:auto; margin:0; gap:6px; }
  #columna-pistas .canal .mute, #columna-pistas .canal .guia{
    width:44px; height:44px; min-height:44px; padding:0; border-radius:12px;
  }
  #columna-pistas .canal-master{ margin:6px 0 0; padding-top:12px; border-top:1px solid var(--linea); border-radius:0; }
  #columna-pistas .canal-master::before{ display:none; }

  /* ícono del instrumento (columna y consola vertical del cajón) */
  .canal-cap{ display:none; }
  .canal-icono{
    display:flex; align-items:center; justify-content:center; width:30px; height:30px; margin:10px auto 0;
    border-radius:10px; flex:0 0 auto; color:var(--pista-color, var(--fg));
    background:color-mix(in srgb, var(--pista-color, var(--fg)) 18%, var(--panel-3));
  }
  .canal-icono svg{ width:18px; height:18px; }
  .canal-nombre{ margin-top:6px; }
  .canal .mute, .canal .guia{ border-radius:10px; }
  .canal .mute{ font-size:0; display:inline-flex; align-items:center; justify-content:center; }
  .canal .mute::before{
    content:""; width:18px; height:18px; background:currentColor;
    -webkit-mask:var(--i-altavoz) center/contain no-repeat; mask:var(--i-altavoz) center/contain no-repeat;
  }
  .canal .mute.muted::before{ -webkit-mask-image:var(--i-mudo); mask-image:var(--i-mudo); }
  .canal .mute.muted{ background:var(--led-mute); border-color:var(--led-mute); color:#fff; }
  .canal .guia{ font-family:var(--mono); font-weight:700; font-size:13px; }
  .canal .guia.activa{ background:var(--brass); border-color:var(--brass); color:var(--sobre-acento); }

  /* --- mesa: barra de transporte ------------------------------------------ */
  .barra-transporte{ border-radius:0; border-top:1px solid var(--linea-fuerte); background:var(--barra-bg); box-shadow:none; }
  #play{ width:60px; height:60px; --play-icono:22px; background:var(--brass); border-color:var(--brass); color:var(--sobre-acento); box-shadow:none; }
  #play:hover{ background:var(--brass); filter:brightness(1.08); }
  body.modo-tocar #play{
    width:calc(60px * clamp(1, var(--esc), 1.4)); height:calc(60px * clamp(1, var(--esc), 1.4));
    --play-icono:calc(22px * clamp(1, var(--esc), 1.4));
  }
  .compas-nav{ background:var(--panel-2); }
  #compas-num{ color:var(--brass); font-weight:700; }
  input[type=range]#seek::-webkit-slider-thumb{ background:var(--brass); box-shadow:0 0 0 4px color-mix(in srgb, var(--brass) 25%, transparent); }
  input[type=range]#seek::-moz-range-thumb{ background:var(--brass); }
  .estudio-tit{ display:none; }
  .barra-estudio .boton-chico{ background:var(--panel-2); }
  .barra-estudio .boton-chico:hover{ background:var(--panel-3); }
  .barra-estudio .boton-chico.destacado{ background:color-mix(in srgb, var(--brass) 18%, var(--panel-2)); color:var(--brass); }
  .barra-estudio .boton-chico.marcado{ background:var(--brass); color:var(--sobre-acento); }
  #loop-a, #loop-b{ min-width:40px; padding-left:0; padding-right:0; font-family:var(--mono); font-weight:700; }
  .rapido{
    border:0; border-radius:14px; color:var(--pista-color, var(--fg));
    background:color-mix(in srgb, var(--pista-color, var(--fg-dim)) 16%, var(--panel-2));
  }
  .rapido:hover{ background:color-mix(in srgb, var(--pista-color, var(--fg-dim)) 26%, var(--panel-2)); }
  .rapido.muted, .rapido.muted:hover{ background:var(--led-mute); color:#fff; }
  .rapido.guia{ outline:1.5px dashed var(--pista-color, var(--fg)); outline-offset:-5px; }
  .rapido-gafas{ border-radius:50%; }
  body.pistas-al-lado .rapido[data-stem], body.pistas-al-lado .rapidos-sep{ display:none; }
  /* ancho: arriba la línea de tiempo; abajo [gafas · transporte · loop y vista] */
  @media (min-width: 900px){
    .barra-transporte{
      display:grid; grid-template-columns:minmax(0, 1fr) auto minmax(0, 1fr); align-items:center; gap:8px 18px;
      grid-template-areas:"linea linea linea" "izq botones der";
    }
    #transporte{ display:contents; }
    .transporte-linea{ grid-area:linea; }
    .transporte-botones{ grid-area:botones; gap:10px; }
    /* gafas a la izquierda y, al final de esa misma celda, cinta y cuenta;
       el loop a la derecha. Comparten celda sin pisarse: uno se alinea al
       inicio y el otro al final. */
    .rapidos{ grid-area:izq; justify-self:start; padding:0; margin:0; border:0; }
    #barra-estudio{ display:contents !important; }
    #barra-estudio > .estudio-grupo:first-child{ grid-area:der; justify-self:end; flex-wrap:nowrap; }
    #barra-estudio > .estudio-grupo:last-child{ grid-area:izq; justify-self:end; flex-wrap:nowrap; }
    /* sin columna de pistas, los mutes rápidos van en su propia fila, arriba */
    body:not(.pistas-al-lado) .barra-transporte{ grid-template-areas:"rap rap rap" "linea linea linea" "izq botones der"; }
    body:not(.pistas-al-lado) .rapidos{ grid-area:rap; justify-self:center; }
  }
  @media (min-width: 900px) and (max-width: 1199px){
    #loop-info{ display:none; }
  }

  /* --- mesa: cajón abierto apaga también la columna de pistas ------------- */
  #columna-pistas{ transition:filter .45s ease, opacity .45s ease; }
  body.cajon-abierto #columna-pistas{ filter:grayscale(1) brightness(.55); opacity:.8; pointer-events:none; user-select:none; }
</style>
<script>
// v102: botón de modo claro / oscuro. Se agrega solo en la cabecera de cada
// pantalla (portada, setlist, mesa); si una pantalla no tiene cabecera, queda
// flotando arriba a la derecha.
document.addEventListener("DOMContentLoaded", function(){
  var raiz = document.documentElement;
  var b = document.createElement("button");
  b.id = "toggle-tema"; b.type = "button"; b.className = "boton-chico boton-icono";
  b.innerHTML = '<svg class="ico ico-luna" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 14.5A8.5 8.5 0 0 1 9.5 4a8.5 8.5 0 1 0 10.5 10.5z"/></svg>'
    + '<svg class="ico ico-sol" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="4"/><path d="M12 2.5v2.5M12 19v2.5M2.5 12H5M19 12h2.5M5.3 5.3l1.8 1.8M16.9 16.9l1.8 1.8M5.3 18.7l1.8-1.8M16.9 7.1l1.8-1.8"/></svg>';
  function rotular(){
    var claro = raiz.dataset.tema === "claro";
    b.title = claro ? "Pasar a modo oscuro" : "Pasar a modo claro";
    b.setAttribute("aria-label", b.title);
  }
  b.addEventListener("click", function(){
    var nuevo = raiz.dataset.tema === "claro" ? "oscuro" : "claro";
    raiz.dataset.tema = nuevo;
    try { localStorage.setItem("mesaTema", nuevo); } catch(e) {}
    if(window.mesaMetaTema) window.mesaMetaTema();
    rotular();
  });
  rotular();
  var acciones = document.querySelector(".acciones-cabecera");
  var portada = document.querySelector(".cabecera-portada");
  var setlist = document.querySelector(".setlist-header");
  if(acciones) acciones.insertBefore(b, acciones.firstChild);
  else if(portada){ var carga = document.getElementById("toggle-carga"); portada.insertBefore(b, carga || null); }
  else if(setlist){ var borrar = document.getElementById("borrar-setlist"); setlist.insertBefore(b, borrar || null); }
  else { b.classList.add("suelto"); document.body.appendChild(b); }
});
</script>
<script>
// Panel de diagnóstico, apagado por defecto: se activa una vez visitando
// ?debug=1 (queda prendido con localStorage, sirve para todas las páginas
// después, incluida la app instalada, porque comparten el mismo storage de
// origen) y se apaga con ?debug=0. Sirve para ver en la pantalla misma qué
// pasa al abrir sin conexión, sin necesitar cable ni depuración remota.
(function(){
  const params = new URLSearchParams(location.search);
  if(params.get("debug") === "1") localStorage.setItem("mesaDebug", "1");
  if(params.get("debug") === "0") localStorage.removeItem("mesaDebug");
  if(localStorage.getItem("mesaDebug") !== "1") return;

  const panel = document.createElement("div");
  panel.id = "mesa-debug-panel";
  // pointer-events:none en el panel = se ve, pero los toques lo atraviesan y
  // llegan al botón/scroll que esté debajo. Es un cartel de solo lectura, no
  // una ventana -- nunca más debería tapar nada.
  panel.style.cssText = "position:fixed; bottom:0; left:0; right:0; max-height:35vh; overflow:auto; "
    + "background:rgba(0,0,0,.9); color:#0f0; font:10px/1.4 monospace; padding:6px; z-index:999999; "
    + "white-space:pre-wrap; border-top:2px solid #0f0; pointer-events:none;";

  function agregarPanel(){ if(document.body && !document.getElementById("mesa-debug-panel")) document.body.appendChild(panel); }
  agregarPanel();
  document.addEventListener("DOMContentLoaded", agregarPanel);

  function log(msg){
    agregarPanel();
    const linea = document.createElement("div");
    linea.textContent = `[${new Date().toLocaleTimeString()}] ${msg}`;
    panel.appendChild(linea);
    panel.scrollTop = panel.scrollHeight;
  }
  window.addEventListener("error", (e) => log(`ERROR: ${e.message} @ ${e.filename || "?"}:${e.lineno}`));
  window.addEventListener("unhandledrejection", (e) => log(`PROMESA RECHAZADA: ${(e.reason && e.reason.message) || e.reason}`));

  log(`online=${navigator.onLine}  url=${location.href}`);
  if("serviceWorker" in navigator){
    navigator.serviceWorker.getRegistration().then((reg) => {
      log(`SW registrado: ${reg ? "sí (scope " + reg.scope + ")" : "NO"}`);
      log(`SW controlando esta página: ${navigator.serviceWorker.controller ? "sí" : "NO"}`);
    });
  } else {
    log("serviceWorker NO soportado en este navegador");
  }
  if("caches" in window){
    caches.open("mesa-audio-v1").then((c) => c.keys()).then((keys) => {
      log(`caché mesa-audio-v1: ${keys.length} entradas`);
      keys.forEach((k) => log("  - " + new URL(k.url).pathname));
    }).catch((e) => log("error leyendo la caché: " + e.message));
  } else {
    log("Cache Storage NO soportado en este navegador");
  }
})();

// Aviso no bloqueante en lugar de alert(). mesaAviso(texto, {error, duracion}).
window.mesaAviso = function(texto, opciones){
  const o = opciones || {};
  let el = document.getElementById("mesa-toast");
  if(!el){
    if(!document.body){ console.warn(texto); return; }
    el = document.createElement("div");
    el.id = "mesa-toast";
    el.addEventListener("click", () => el.classList.remove("visible"));
    document.body.appendChild(el);
  }
  el.textContent = texto;
  el.classList.toggle("error", !!o.error);
  el.classList.add("visible");
  clearTimeout(el._temporizador);
  el._temporizador = setTimeout(() => el.classList.remove("visible"), o.duracion || (o.error ? 8000 : 4500));
};

// Registra el service worker (necesario para que Chrome/Android ofrezcan
// "Instalar app": el manifest ya estaba completo, esto era lo único que
// faltaba). No precachea nada del sitio: lo único que cachea es el audio que
// el usuario pide explícitamente con el chip "descargar" del encabezado, desde
// mesaOffline de acá abajo.
if("serviceWorker" in navigator){
  window.addEventListener("load", () => {
    navigator.serviceWorker.register("/sw.js").catch(() => {});
  });
}

// --- descargas offline (stems al 100%, uno por canción) -------------------
// Punto único para las dos pantallas que tocan el caché de audio: la portada
// (al borrar una canción hay que borrar también su descarga) y la mesa (para
// bajar/borrar y mostrar el estado). El caché de audio lo llena solo esto,
// nunca el service worker por su cuenta -- así no crece sin que el usuario lo
// pida. El nombre del caché tiene que ser el mismo que usa sw.js.
window.mesaOffline = (() => {
  const CACHE_AUDIO = "mesa-audio-v1";
  const soportado = ("caches" in window);

  async function disponible(urls){
    if(!soportado || !urls.length) return false;
    const cache = await caches.open(CACHE_AUDIO);
    for(const u of urls) if(!(await cache.match(u))) return false;
    return true;
  }

  async function tamanoBytes(urls){
    if(!soportado) return 0;
    const cache = await caches.open(CACHE_AUDIO);
    let total = 0;
    for(const u of urls){
      const r = await cache.match(u);
      if(!r) continue;
      try{ total += (await r.clone().blob()).size; }catch(e){ /* ignorar */ }
    }
    return total;
  }

  // Pide almacenamiento persistente la primera vez que se descarga algo
  // (con gesto del usuario, que es cuando Chrome lo concede). Sin esto, con
  // el disco lleno el navegador puede tirar el caché sin avisar.
  let persistenciaPedida = false;
  function pedirPersistencia(){
    if(persistenciaPedida) return;
    persistenciaPedida = true;
    try{
      if(navigator.storage && navigator.storage.persist) navigator.storage.persist().catch(() => {});
    }catch(e){}
  }

  // Cuánto ocupa todo lo descargado en este dispositivo (según el navegador).
  async function usoAlmacenamiento(){
    try{
      if(navigator.storage && navigator.storage.estimate){
        const e = await navigator.storage.estimate();
        return { usado: e.usage || 0, cuota: e.quota || 0 };
      }
    }catch(e){}
    return null;
  }

  async function descargar(urls, onProgreso){
    if(!soportado) throw new Error("Este navegador no permite guardar audio offline");
    pedirPersistencia();
    const cache = await caches.open(CACHE_AUDIO);
    for(let i = 0; i < urls.length; i++){
      const res = await fetch(urls[i]);
      if(!res.ok) throw new Error(`HTTP ${res.status} en ${urls[i]}`);
      await cache.put(urls[i], res);
      if(onProgreso) onProgreso(i + 1, urls.length);
    }
  }

  async function borrar(urls){
    if(!soportado) return;
    const cache = await caches.open(CACHE_AUDIO);
    await Promise.all(urls.map(u => cache.delete(u)));
  }

  // al borrar una canción entera desde la portada no sabemos qué stems tenía
  // sin pedirlos al servidor (que ya se está borrando), así que el audio se
  // limpia por prefijo de URL; la página y sus datos son rutas exactas
  async function borrarPorCancion(song){
    if(!soportado) return;
    const cache = await caches.open(CACHE_AUDIO);
    const prefijoAudio = `/audio/${song}/`;
    // se compara por pathname, así que `/mesa/<song>` también barre sus
    // variantes "?setlist=..."; las páginas de setlist y la portada son
    // compartidas con otras canciones y se dejan
    const exactas = new Set([`/mesa/${song}`, `/acordes/${song}`, `/mezcla/${song}`, `/rasgueo/${song}`]);
    const claves = await cache.keys();
    await Promise.all(
      claves
        .filter(k => {
          const p = new URL(k.url).pathname;
          return p.startsWith(prefijoAudio) || exactas.has(p);
        })
        .map(k => cache.delete(k))
    );
  }

  // Qué canciones están guardadas para tocar sin wifi. Una sola pasada por
  // las claves del caché para toda la lista: preguntar canción por canción con
  // cache.match() son cientos de lecturas en una biblioteca grande.
  // Cuenta como descargada solo si están la página Y al menos un stem, así una
  // descarga cortada a la mitad no aparece como completa.
  async function cancionesDescargadas(){
    if(!soportado) return new Set();
    const cache = await caches.open(CACHE_AUDIO);
    const paginas = new Set(), conAudio = new Set();
    for(const k of await cache.keys()){
      let p;
      try{ p = decodeURIComponent(new URL(k.url).pathname); }catch(e){ continue; }
      let m = p.match(/^\\/mesa\\/([^/]+)$/);
      if(m){ paginas.add(m[1]); continue; }
      m = p.match(/^\\/audio\\/([^/]+)\\//);
      if(m) conAudio.add(m[1]);
    }
    return new Set([...paginas].filter(s => conAudio.has(s)));
  }

  function fmtMB(bytes){ return (bytes / (1024*1024)).toFixed(1) + " MB"; }

  return { disponible, tamanoBytes, descargar, borrar, borrarPorCancion, cancionesDescargadas, usoAlmacenamiento, fmtMB, soportado };
})();

// Pinta el puntito verde en cualquier lista de canciones (portada, "últimas
// que abriste", setlist). Es una sola función para las tres porque todas usan
// la misma marca y el mismo criterio; cada plantilla solo tiene que poner
// data-song en la fila.
window.marcarDescargadas = async function(){
  const filas = document.querySelectorAll(".cancion-fila[data-song], .setlist-fila-cancion[data-song]");
  if(!filas.length || !window.mesaOffline || !window.mesaOffline.soportado) return;
  let descargadas;
  try{ descargadas = await window.mesaOffline.cancionesDescargadas(); }
  catch(e){ return; }   // sin caché legible no marcamos nada, no es crítico
  filas.forEach(fila => {
    const link = fila.querySelector(".cancion");
    if(!link) return;
    const esta = descargadas.has(fila.dataset.song);
    link.classList.toggle("descargada", esta);
    fila.classList.toggle("descargada-fila", esta);
    const marca = link.querySelector(".marca-offline");
    if(esta && !marca){
      const nueva = document.createElement("span");
      nueva.className = "marca-offline";
      nueva.setAttribute("aria-label", "descargada para tocar sin wifi");
      nueva.innerHTML = "&#8595;";
      link.appendChild(nueva);
      link.title = "Descargada para tocar sin wifi";
    } else if(!esta && marca){
      marca.remove();
      link.removeAttribute("title");
    }
  });
  // resumen de lo que ocupa en este dispositivo (solo donde haya dónde ponerlo)
  const resumen = document.getElementById("resumen-offline");
  if(resumen){
    const uso = await window.mesaOffline.usoAlmacenamiento();
    const n = descargadas.size;
    let texto = n ? `${n} ${n === 1 ? "canción descargada" : "canciones descargadas"} en este dispositivo` : "";
    if(uso && uso.usado) texto += (texto ? " · " : "") + `${window.mesaOffline.fmtMB(uso.usado)} usados`;
    resumen.textContent = texto;
    resumen.style.display = texto ? "" : "none";
  }
};
// pageshow y no DOMContentLoaded: al volver de la mesa con el botón "atrás",
// el navegador restaura la página del bfcache y DOMContentLoaded no vuelve a
// dispararse -- justo el caso en que acabás de descargar algo y querés verlo
// marcado.
window.addEventListener("pageshow", () => { window.marcarDescargadas(); });

// --- v103: "Últimas que abriste" también sin conexión ------------------------
// Cada apertura se anota en ESTE dispositivo (con su hora) además de en la PC,
// así la lista se actualiza aunque la PC no esté. Lo anotado sin conexión
// queda pendiente y se le manda a la PC apenas se la alcanza; la lista que se
// muestra mezcla lo de la PC con lo de acá, por hora.
//   mesaRecientes:          {cancion: hora}  todo lo conocido en este dispositivo
//   mesaRecientesPendiente: {cancion: hora}  lo que la PC todavía no sabe
window.mesaRecientes = (() => {
  const CLAVE = "mesaRecientes", CLAVE_PEND = "mesaRecientesPendiente";
  function leerDe(clave){
    try{ const v = JSON.parse(localStorage.getItem(clave) || "{}"); return (v && typeof v === "object") ? v : {}; }
    catch(e){ return {}; }
  }
  function guardarEn(clave, v){ try{ localStorage.setItem(clave, JSON.stringify(v)); }catch(e){} }
  function leer(){ return leerDe(CLAVE); }
  function anotar(song){
    const t = Date.now() / 1000;
    const todo = leer(); todo[song] = t; guardarEn(CLAVE, todo);
    const pend = leerDe(CLAVE_PEND); pend[song] = t; guardarEn(CLAVE_PEND, pend);
  }
  // lo que trae la PC (con su hora) se suma a lo local: queda la hora más nueva
  function mezclar(lista){
    if(!Array.isArray(lista)) return;
    const todo = leer();
    lista.forEach(r => { if(r && r.song && typeof r.t === "number" && !(todo[r.song] >= r.t)) todo[r.song] = r.t; });
    guardarEn(CLAVE, todo);
  }
  async function sincronizar(){
    const pend = leerDe(CLAVE_PEND);
    if(!Object.keys(pend).length) return true;
    try{
      const r = await fetch("/recientes", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ aperturas: pend }),
      });
      if(!r.ok) return false;
      // se borra solo lo que se mandó: si se abrió otro tema mientras tanto, queda
      const ahora = leerDe(CLAVE_PEND);
      Object.keys(pend).forEach(s => { if(ahora[s] === pend[s]) delete ahora[s]; });
      guardarEn(CLAVE_PEND, ahora);
      return true;
    }catch(e){ return false; }
  }
  return { leer, anotar, mezclar, sincronizar };
})();

// --- indicador de estado de la red ----------------------------------------
// Ojo con la tentación de usar navigator.onLine o el evento "offline": en el
// ensayo la tablet SÍ tiene wifi, lo que no tiene es ruta hasta la PC, así que
// para el navegador está online y nunca se entera. El único que lo sabe de
// verdad es el service worker, cuando el pedido se le cae. De ahí sale este
// aviso. El evento del navegador se escucha igual porque cuando sí dispara
// (wifi apagado) es correcto y llega antes.
(() => {
  // en false, el chip aparece solo cuando NO hay conexión
  const SIEMPRE_VISIBLE = true;

  let chip = null, estado = "en-linea", listo = false, temporizador = null;

  function construir(){
    if(!document.body) return;   // todavía no hay dónde ponerlo
    listo = false;               // corta la recursión con pintar()
    chip = document.createElement("span");
    chip.id = "chip-red";
    chip.innerHTML = '<span class="punto"></span><span class="texto"></span>';
    // el ancla está en el contenido de la página, que se parsea DESPUÉS de
    // este script (BASE_STYLE va primero); por eso todo esto espera al DOM
    const ancla = document.getElementById("ancla-red");
    if(ancla){ ancla.replaceWith(chip); }
    else { chip.classList.add("suelto"); document.body.appendChild(chip); }
    listo = true;
    pintar();
  }

  function pintar(){
    if(!listo) return;
    if(!chip.isConnected){ construir(); return; }   // si algo lo sacó del DOM
    const sinRed = (estado !== "en-linea");
    chip.classList.toggle("sin-red", sinRed);
    chip.classList.toggle("en-linea", !sinRed);
    chip.querySelector(".texto").textContent = sinRed
      ? "sin conexión \u00b7 usando lo descargado"
      : "en línea";
    chip.style.display = (sinRed || SIEMPRE_VISIBLE) ? "" : "none";
    if(document.body) document.body.classList.toggle("sin-red", sinRed);
  }

  function fijar(nuevo){
    if(nuevo === estado) return;
    estado = nuevo;
    pintar();
    // al recuperar la conexión el chip parpadea una vez, para que se note el
    // cambio sin tener que estar mirándolo
    if(nuevo === "en-linea" && listo){
      clearTimeout(temporizador);
      chip.style.opacity = ".25";
      temporizador = setTimeout(() => { chip.style.opacity = ""; }, 260);
    }
  }

  // Estado inicial leído del caché, no por mensaje: cuando el service worker
  // contesta la navegación desde el caché, esta página todavía no existe y el
  // postMessage se perdería. La marca en cambio está ahí para leerla.
  function leerDelCache(){
    if(!("caches" in window)) return;
    caches.open("mesa-audio-v1")
      .then((c) => c.match("/__estado_red"))
      .then((r) => fijar(r ? "sin-red" : "en-linea"))
      .catch(() => {});
  }

  if(document.readyState === "loading"){
    document.addEventListener("DOMContentLoaded", construir);
  } else {
    construir();
  }
  leerDelCache();
  window.addEventListener("pageshow", leerDelCache);   // vuelta del bfcache

  if("serviceWorker" in navigator){
    navigator.serviceWorker.addEventListener("message", (e) => {
      const d = e.data || {};
      if(d.tipo === "mesa-red") fijar(d.estado === "online" ? "en-linea" : "sin-red");
    });
  }
  window.addEventListener("offline", () => fijar("sin-red"));

  // --- latido ---------------------------------------------------------------
  // El service worker solo se entera de que no hay red cuando un pedido falla,
  // y con la mesa abierta y el audio cargado no queda ningún pedido por hacer.
  // Este es ese pedido: 2 bytes cada 20 s.
  // El tope de la página (3,5 s) es a propósito MAYOR que el del service
  // worker (2,5 s): así el que decide y anota el estado es siempre el service
  // worker, y no le abortamos el pedido por abajo antes de que concluya.
  // El tope era de 3.5s y UN solo fallo bastaba para declarar "sin red". Eso
  // daba falsos cortes: mientras bajan las 6 pistas el enlace está saturado,
  // el latido queda encolado detrás del audio, se pasa del tope y la app
  // avisaba de una caída que no existía -- justo con la descarga andando, que
  // es la prueba de que SÍ hay red. Ahora: tope más generoso (sigue entrando
  // cómodo en el intervalo de 20s), hacen falta dos fallos seguidos para
  // cortar, y un solo acierto restablece al toque.
  const PING_MS = 20000, PING_TOPE = 8000, FALLOS_PARA_CORTAR = 2;
  let pingEnVuelo = false, fallosSeguidos = 0;

  // Mientras hay audio en vuelo no tiene sentido sondear: el latido compite
  // con la descarga por el mismo enlace y pierde. Si está bajando audio, hay
  // red, y punto.
  window.mesaHayDescargaEnCurso = false;

  async function latir(){
    if(pingEnVuelo || document.hidden) return;   // en segundo plano no gastamos
    if(window.mesaHayDescargaEnCurso){ fallosSeguidos = 0; return; }
    pingEnVuelo = true;
    const ctrl = new AbortController();
    const t = setTimeout(() => ctrl.abort(), PING_TOPE);
    try{
      const r = await fetch("/ping", { cache: "no-store", signal: ctrl.signal });
      if(r.ok){ fallosSeguidos = 0; fijar("en-linea"); }
      else if(++fallosSeguidos >= FALLOS_PARA_CORTAR) fijar("sin-red");
    }catch(e){
      if(++fallosSeguidos >= FALLOS_PARA_CORTAR) fijar("sin-red");
    }finally{
      clearTimeout(t);
      pingEnVuelo = false;
    }
  }

  latir();
  setInterval(latir, PING_MS);
  // al volver a la pantalla queremos saber ya si algo cambió mientras no
  // estábamos, sin esperar hasta 20 s
  document.addEventListener("visibilitychange", () => { if(!document.hidden) latir(); });
  window.addEventListener("online", latir);
})();
</script>
"""

# v107: Ajustes generales en un solo lugar, para la mesa y la portada (mismos
# ids, así el JS de la mesa no cambia). Lo que solo sirve dentro de un tema
# (conectar las gafas por el Bluetooth del navegador) va con "en_mesa".
PANEL_GENERALES_HTML = """<div class="panel panel-plegable{{ ' colapsado' if generales_colapsado else '' }}" id="panel-generales">
  <div class="panel-plegable-cabecera" id="toggle-panel-generales">
    <span class="panel-plegable-titulo">Ajustes generales</span>
    <span class="panel-plegable-resumen">valen para todas las canciones</span>
    <span class="panel-plegable-flecha"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 9l6 6 6-6"/></svg></span>
  </div>
  <div class="panel-plegable-cuerpo panel-generales-cuerpo">

    <div class="grupo">
      <div class="grupo-titulo">Cartel de acordes</div>
      <div class="grupo-cuerpo tiles">
        <button id="toggle-diagramas" class="boton-chico tile{{ ' destacado' if mostrar_diagramas else '' }}" title="Mostrar u ocultar los diagramas del mástil"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="5" y="3" width="14" height="18" rx="1.5"/><path d="M5 8h14M5 13h14M9.7 3v18M14.3 3v18"/><circle cx="12" cy="10.5" r="1.4" fill="currentColor"/></svg><span>Diagramas</span></button>
        <button id="toggle-grados" class="boton-chico tile{{ ' destacado' if mostrar_grados else '' }}" title="Mostrar u ocultar los grados (números romanos) de los acordes"><span class="tile-romano" aria-hidden="true">IV</span><span>Grados</span></button>
      </div>
    </div>

    <!-- v109: detector de acordes aprendido (ver modelo_acordes en el backend) -->
    <div class="grupo grupo-ancho">
      <div class="grupo-titulo">Detector de acordes</div>
      <div class="grupo-cuerpo">
        <button id="toggle-detector-aprendido" class="boton-chico interruptor{{ ' destacado' if (detector_aprendido and modelo_info) else '' }}"{{ '' if modelo_info else ' disabled' }} title="Usar el detector entrenado con tus MIDI en vez del de plantillas"><span class="interruptor-pista"></span>Detector aprendido</button>
        <span id="detector-nota" class="grupo-nota">{% if modelo_info %}Entrenado con {{ modelo_info.temas }} temas{{ ' el ' ~ modelo_info.fecha if modelo_info.fecha else '' }}.{% else %}Todavía no hay modelo entrenado: se usa el detector por plantillas.{% endif %} Vale para los temas que se analicen de ahora en más (o al tocar Regenerar): no cambia los acordes ya guardados ni los importados de un MIDI.</span>
        <div class="grupo-fila">
          <button id="entrenar-detector" type="button" class="boton-chico" title="Aprende de los temas que tienen un MIDI importado (Chordify). Corre en la PC; podés seguir usando Mesa.">Entrenar con mis MIDI</button>
        </div>
        <span id="detector-estado" class="grupo-nota"></span>
      </div>
    </div>
    <script>
    // v110: detector aprendido. Este script viaja con el panel, así funciona igual
    // en la portada y en la mesa.
    (function(){
      const btnTog = document.getElementById("toggle-detector-aprendido");
      const btnEnt = document.getElementById("entrenar-detector");
      const est = document.getElementById("detector-estado");
      const nota = document.getElementById("detector-nota");
      if(!btnEnt || !est) return;
      if(btnTog) btnTog.addEventListener("click", () => {
        if(btnTog.disabled) return;
        const v = !btnTog.classList.contains("destacado");
        btnTog.classList.toggle("destacado", v);
        fetch("/preferencia", { method: "POST", headers: { "Content-Type": "application/json" },
          body: JSON.stringify({ clave: "detector_aprendido", valor: v }) }).catch(() => {});
      });
      function resumen(u){
        if(!u) return "";
        let t = `Último entrenamiento (${u.fecha}, ${u.temas} temas): plantillas ${u.base_triada}% → aprendido ${u.modelo_triada}%`
          + ` · mejoran ${u.mejoran}, empeoran ${u.empeoran}.`;
        if(u.variante) t += ` Elegido: ${u.variante}, silencio ${u.umbral_silencio ? (u.umbral_silencio * 100).toFixed(1) + "% del pico" : "lo decide el modelo"}`
          + (typeof u.v110_triada === "number" ? ` (con la configuración anterior daba ${u.v110_triada}%).` : ".");
        if(u.excluidos && u.excluidos.length) t += ` Quedaron afuera ${u.excluidos.length} con el MIDI probablemente desfasado: `
          + u.excluidos.map(x => x.tema).join(", ") + ".";
        if(!u.guardado) t += " No le ganó al de plantillas: se mantuvo el modelo anterior.";
        return t;
      }
      let timer = null;
      function pintar(d){
        if(d.corriendo){
          btnEnt.disabled = true;
          const paso = d.n ? ` ${Math.min(d.i + 1, d.n)}/${d.n}` : "";
          est.textContent = `Entrenando: ${d.etapa}${paso}…` + (d.detalle ? ` (${d.detalle})` : "");
          return;
        }
        btnEnt.disabled = false;
        if(d.etapa === "error" && d.error){ est.textContent = "No se pudo entrenar: " + d.error; return; }
        est.textContent = resumen(d.ultimo);
        if(d.modelo && btnTog){
          btnTog.disabled = false;
          btnTog.classList.toggle("destacado", !!d.detector_aprendido);
          if(nota) nota.textContent = `Entrenado con ${d.modelo.temas} temas el ${d.modelo.fecha}. `
            + "Vale para los temas que se analicen de ahora en más (o al tocar Regenerar): no cambia los acordes ya guardados ni los importados de un MIDI.";
        }
      }
      async function consultar(){
        try{
          const r = await fetch("/detector/estado", { cache: "no-store" });
          const d = await r.json();
          pintar(d);
          if(d.corriendo && !timer) timer = setInterval(consultar, 2000);
          if(!d.corriendo && timer){ clearInterval(timer); timer = null; }
        }catch(e){ /* sin conexión con la PC: el chip de red ya lo dice */ }
      }
      btnEnt.addEventListener("click", async () => {
        btnEnt.disabled = true;
        est.textContent = "Arrancando…";
        try{
          const r = await fetch("/detector/entrenar", { method: "POST" });
          const d = await r.json().catch(() => ({}));
          if(!r.ok && r.status !== 409) throw new Error(d.error || `HTTP ${r.status}`);
        }catch(e){
          est.textContent = "No se pudo arrancar: " + e.message;
          btnEnt.disabled = false;
          return;
        }
        consultar();
      });
      consultar();
    })();
    </script>

    {% if not es_la_pc %}
    <!-- Solo en dispositivos que reciben el audio por red. En la PC la ventana
         carga desde 127.0.0.1 y bajar la calidad no ahorra nada, así que ahí ni
         se muestra. Va por cookie (este dispositivo), no en prefs.json: si fuera
         global, ponerlo en mono desde la tablet degradaría también la PC. -->
    <div class="grupo" data-calidad="{{ calidad_actual }}">
      <div class="grupo-titulo">Audio en este dispositivo</div>
      <div class="grupo-cuerpo">
        <div class="grupo-fila">
          <button class="boton-chico calidad{{ ' marcado' if calidad_actual in ('estereo160','estereo96') else '' }}" data-canal="estereo">Estéreo</button>
          <button class="boton-chico calidad{{ ' marcado' if calidad_actual in ('mono160','mono96') else '' }}" data-canal="mono">Mono</button>
        </div>
        <div class="grupo-fila">
          <button class="boton-chico calidad{{ ' marcado' if calidad_actual in ('estereo160','mono160') else '' }}" data-bitrate="160">160k</button>
          <button class="boton-chico calidad{{ ' marcado' if calidad_actual in ('estereo96','mono96') else '' }}" data-bitrate="96">96k</button>
        </div>
        <span id="calidad-peso" class="grupo-valor" style="font-size:13px;"></span>
      </div>
    </div>
    {% endif %}

    <div class="grupo grupo-ancho grupo-colores">
      <div class="grupo-titulo">Barra del acorde</div>
      <div class="grupo-cuerpo">
        <button id="toggle-color-duracion" class="boton-chico interruptor{{ ' destacado' if colorear_duracion else '' }}" title="Colorear la barra según cuánto dura el acorde: medio compás, un compás o dos o más"><span class="interruptor-pista"></span>Colorear según la duración</button>
        <div id="colores-bandas" class="colores-bandas">
          {% for banda, etiqueta, detalle, largo in (('corto','Corto','medio compás o menos','22%'), ('normal','Normal','1 compás','50%'), ('largo','Largo','2 compases o más','100%')) %}
          {% set elegido = color_corto if banda=='corto' else (color_normal if banda=='normal' else color_largo) %}
          <div class="colores-fila" data-banda="{{ banda }}" style="--sel: {{ stem_colores[elegido] }};">
            <div class="colores-info">
              <span class="colores-etiqueta">{{ etiqueta }}<small>{{ detalle }}</small></span>
              <span class="colores-muestra"><i style="width:{{ largo }};"></i></span>
            </div>
            <div class="colores-swatches" role="radiogroup" aria-label="Color para la banda {{ etiqueta|lower }}">
              {% for stem in stem_order %}
              <button class="swatch-color{{ ' seleccionado' if elegido == stem else '' }}"
                      data-stem="{{ stem }}" style="--sw: {{ stem_colores[stem] }};" title="{{ stem_labels[stem] }}" aria-label="{{ stem_labels[stem] }}"></button>
              {% endfor %}
            </div>
          </div>
          {% endfor %}
        </div>
      </div>
    </div>

    <div class="grupo grupo-ancho grupo-tema-color">
      <div class="grupo-titulo">Color de la app</div>
      <div class="grupo-cuerpo">
        <div class="tema-presets" role="radiogroup" aria-label="Color base de la app">
          <button class="swatch-color tema-preset" data-color="" style="--sw: #f2b33d;" title="Ámbar (original)" aria-label="Ámbar (original)"></button>
          <button class="swatch-color tema-preset" data-color="#9585ff" style="--sw: #9585ff;" title="Violeta" aria-label="Violeta"></button>
          <button class="swatch-color tema-preset" data-color="#4c8dff" style="--sw: #4c8dff;" title="Azul" aria-label="Azul"></button>
          <button class="swatch-color tema-preset" data-color="#2fcf8a" style="--sw: #2fcf8a;" title="Verde" aria-label="Verde"></button>
          <button class="swatch-color tema-preset" data-color="#ff5a6e" style="--sw: #ff5a6e;" title="Rojo" aria-label="Rojo"></button>
          <button class="swatch-color tema-preset" data-color="#9aa0a6" style="--sw: #9aa0a6;" title="Gris neutro" aria-label="Gris neutro"></button>
          <button class="swatch-color tema-preset tema-preset-mono" data-color="mono" style="--sw: linear-gradient(135deg, #000 50%, #fff 50%);" title="Blanco y negro" aria-label="Blanco y negro"></button>
        </div>
        <div class="grupo-fila tema-elegir">
          <input id="color-base" type="color" class="campo-color" value="{{ color_base if color_base.startswith('#') else '#f2b33d' }}" title="Elegir cualquier color" aria-label="Elegir cualquier color">
          <button id="color-base-original" class="boton-chico" title="Volver a la paleta original">Volver al original</button>
        </div>
        <span class="grupo-nota">Vale para toda la app, en la PC y en la tablet. No cambian el rojo de mute, el celeste de rasgueo ni los colores de la barra.</span>
      </div>
    </div>

    <div class="grupo grupo-ancho grupo-gafas">
      <div class="grupo-titulo">Gafas HUD</div>
      <div class="grupo-cuerpo">
        <div class="tiles">
          <button id="toggle-hud" class="boton-chico tile{{ ' destacado' if hud_activo else '' }}" title="Transmitir a HUD"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M2.5 9a14 14 0 0 1 19 0M5.5 12.5a9.5 9.5 0 0 1 13 0M8.5 16a5 5 0 0 1 7 0"/><circle cx="12" cy="19" r="1" fill="currentColor"/></svg><span>Transmitir</span></button>
          <button id="toggle-hud-ble" class="boton-chico tile{{ ' destacado' if hud_ble else '' }}" title="Bluetooth desde la PC"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M7 7l10 10-5 5V2l5 5L7 17"/></svg><span>BT de la PC</span></button>
          {% if en_mesa %}
          <button id="conectar-gafas-local" class="boton-chico tile" title="Bluetooth desde este dispositivo"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="6" y="2.5" width="12" height="19" rx="2.5"/><path d="M10.5 18.5h3"/></svg><span>Conectar acá</span></button>
          {% endif %}
          <button id="toggle-hud-invertido" class="boton-chico tile{{ ' destacado' if hud_invertido else '' }}" title="Invertir colores"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="8.5"/><path d="M12 3.5a8.5 8.5 0 0 1 0 17z" fill="currentColor"/></svg><span>Invertir</span></button>
        </div>
        <div class="hud-chips">
          <span id="chip-hud-estado"><span class="punto"></span><span class="texto"></span></span>
          <span id="chip-hud-ble"><span class="punto"></span><span class="texto"></span></span>
          {% if en_mesa %}
          <span id="chip-hud-ble-local"><span class="punto"></span><span class="texto">sin conectar</span></span>
          {% endif %}
        </div>
        <div class="grupo-fila hud-brillo">
          <button id="hud-brillo-menos" class="boton-chico" title="Bajar el brillo de las gafas" aria-label="Bajar el brillo">&minus;</button>
          <span id="hud-brillo-actual" class="grupo-valor" data-nivel="{{ hud_brillo }}" data-max="{{ hud_brillos|length }}">brillo {{ hud_brillo }}/{{ hud_brillos|length }}</span>
          <button id="hud-brillo-mas" class="boton-chico" title="Subir el brillo de las gafas" aria-label="Subir el brillo">+</button>
        </div>
        {% if not en_mesa %}
        <span class="grupo-nota">«Conectar acá» (Bluetooth de la tablet) está dentro de cada tema: esa conexión se corta al salir de la pantalla del tema.</span>
        {% endif %}
      </div>
    </div>

  </div>
</div>"""

HOME_HTML = BASE_STYLE + """
<!-- Pantalla de inicio: se ve una sola vez por sesión (al abrir la app), no cada vez que se
     vuelve a la portada. Un toque la cierra antes. Es solo presentación: no bloquea la carga. -->
<style>
  #splash{
    position:fixed; inset:0; z-index:10000; background:var(--bg);
    display:flex; flex-direction:column; align-items:center; justify-content:center; gap:14px;
    transition:opacity .45s ease; cursor:pointer; -webkit-tap-highlight-color:transparent;
  }
  #splash.fuera{ opacity:0; pointer-events:none; }
  #splash .splash-logo{
    width:84px; height:84px; padding:18px; border-radius:24px; color:var(--brass);
    background:var(--panel); border:1px solid var(--linea-fuerte);
    animation:splash-entra .6s cubic-bezier(.2,.8,.2,1) both;
  }
  #splash .splash-logo svg{ width:100%; height:100%; display:block; }
  #splash .splash-nombre{
    font-family:var(--sans); font-size:38px; font-weight:700; letter-spacing:-.02em; color:var(--fg);
    animation:splash-entra .6s .08s cubic-bezier(.2,.8,.2,1) both;
  }
  #splash .splash-sub{
    font-family:var(--sans); font-size:14px; color:var(--fg-dim); margin-top:-8px;
    animation:splash-entra .6s .14s cubic-bezier(.2,.8,.2,1) both;
  }
  #splash .splash-version{
    position:absolute; bottom:28px; font-family:var(--mono); font-size:12px;
    letter-spacing:.06em; color:var(--fg-tenue);
  }
  #splash .splash-barra{
    width:120px; height:3px; border-radius:2px; background:var(--panel-2); overflow:hidden; margin-top:10px;
  }
  #splash .splash-barra::after{
    content:""; display:block; height:100%; width:40%; border-radius:2px; background:var(--brass);
    animation:splash-carga 1.1s ease-in-out infinite;
  }
  @keyframes splash-entra{ from{ opacity:0; transform:translateY(8px) scale(.97); } to{ opacity:1; transform:none; } }
  @keyframes splash-carga{ from{ transform:translateX(-100%); } to{ transform:translateX(250%); } }
  @media (prefers-reduced-motion: reduce){
    #splash, #splash *{ animation:none !important; transition:none !important; }
  }
</style>
<div id="splash" role="presentation" aria-hidden="true">
  <div class="splash-logo"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M6 20V10M12 20V4M18 20v-7"/><path d="M4 10h4M10 7h4M16 13h4"/></svg></div>
  <div class="splash-nombre">Mesa</div>
  <div class="splash-sub">separador de pistas</div>
  <div class="splash-barra"></div>
  {% if version_app %}<div class="splash-version">versión {{ version_app }}</div>{% endif %}
</div>
<script>
(function(){
  var splash = document.getElementById("splash");
  var visto = false;
  try { visto = sessionStorage.getItem("mesa-splash") === "1"; } catch(e) {}
  if (visto) { splash.remove(); return; }
  try { sessionStorage.setItem("mesa-splash", "1"); } catch(e) {}
  var cerrado = false;
  function cerrar(){
    if (cerrado) return; cerrado = true;
    splash.classList.add("fuera");
    setTimeout(function(){ splash.remove(); }, 500);
  }
  splash.addEventListener("click", cerrar);
  setTimeout(cerrar, 1600);
})();
</script>
<!-- v107: barra lateral de secciones (solo en pantallas anchas) -->
<nav class="riel" aria-label="Secciones">
  <span class="riel-logo" aria-hidden="true"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round"><path d="M6 20V10M12 20V4M18 20v-7"/><path d="M4 10h4M10 7h4M16 13h4"/></svg></span>
  <a href="#sec-todas" class="riel-item activo"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="4" y="4" width="7" height="7" rx="1.5"/><rect x="13" y="4" width="7" height="7" rx="1.5"/><rect x="4" y="13" width="7" height="7" rx="1.5"/><rect x="13" y="13" width="7" height="7" rx="1.5"/></svg>Biblioteca</a>
  <a href="#sec-setlists" class="riel-item"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 6h11M9 12h11M9 18h11M4 6h1M4 12h1M4 18h1"/></svg>Setlists</a>
  {% if jobs %}<a href="#sec-proceso" class="riel-item"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M12 3v3M12 18v3M3 12h3M18 12h3M5.6 5.6l2.1 2.1M16.3 16.3l2.1 2.1M5.6 18.4l2.1-2.1M16.3 7.7l2.1-2.1"/></svg>En proceso</a>{% endif %}
  <span class="riel-espacio"></span>
  <button type="button" class="riel-item" data-abrir-ajustes aria-controls="cajon-ajustes"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 6h9M17 6h3M4 12h3M11 12h9M4 18h11M19 18h1"/><circle cx="15" cy="6" r="2"/><circle cx="9" cy="12" r="2"/><circle cx="17" cy="18" r="2"/></svg>Ajustes</button>
</nav>
<div class="cabecera-portada">
  <h1><span class="marca-app"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 20V10M12 20V4M18 20v-7"/><path d="M4 10h4M10 7h4M16 13h4"/></svg></span>Mesa <span>&middot; separador de pistas</span></h1>
  <span id="ancla-red"></span>
  <button type="button" class="boton-chico boton-icono solo-angosto" data-abrir-ajustes aria-controls="cajon-ajustes" title="Ajustes generales" aria-label="Ajustes generales"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 6h9M17 6h3M4 12h3M11 12h9M4 18h11M19 18h1"/><circle cx="15" cy="6" r="2"/><circle cx="9" cy="12" r="2"/><circle cx="17" cy="18" r="2"/></svg></button>
  <button id="toggle-carga" type="button" class="boton-chico boton-icono con-texto" aria-controls="panel-carga" aria-expanded="{{ 'false' if canciones else 'true' }}" title="Subir un mp3 o bajar un video de YouTube"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" aria-hidden="true"><path d="M12 5v14M5 12h14"/></svg><span class="solo-ancho">Agregar canción</span></button>
</div>

<div id="panel-carga" class="panel panel-carga{{ '' if canciones else ' abierta' }}">
  <form action="{{ url_for('subir') }}" method="post" enctype="multipart/form-data" class="fila-carga">
    <svg width="26" height="26" viewBox="0 0 26 26" xmlns="http://www.w3.org/2000/svg" class="fila-carga-icono" aria-hidden="true">
      <path d="M13 4 V17 M7.5 10 L13 4.5 L18.5 10" stroke="var(--brass)" stroke-width="2" fill="none" stroke-linecap="round" stroke-linejoin="round"/>
      <path d="M5 21 H21" stroke="var(--brass)" stroke-width="2" stroke-linecap="round"/>
    </svg>
    <span class="fila-carga-label">Subir un mp3</span>
    <input type="file" name="mp3" accept="audio/mpeg,audio/mp3,.mp3" required>
    <button type="submit" class="boton-primario">Separar pistas</button>
  </form>

  <form action="{{ url_for('youtube') }}" method="post" class="fila-carga fila-carga-youtube">
    <svg width="26" height="26" viewBox="0 0 26 26" xmlns="http://www.w3.org/2000/svg" class="fila-carga-icono" aria-hidden="true">
      <rect x="2" y="5" width="22" height="16" rx="5" fill="var(--fg)"/>
      <path d="M11 9.5 L17 13 L11 16.5 Z" fill="var(--bg)"/>
    </svg>
    <input type="url" name="url" class="campo-youtube" placeholder="…o pegá el link de un video de YouTube" required>
    <button type="submit" class="boton-youtube">Descargar y separar</button>
  </form>
</div>

{% if jobs %}
<div class="lista" id="sec-proceso">
  <h2>En proceso</h2>
  <div class="jobs-fila">
    {% for j in jobs %}
      <a class="job-chip" href="{{ url_for('procesando', job_id=j.id) }}" title="Volver a la pantalla de este trabajo">
        <span class="punto"></span>
        {{ j.song or 'YouTube' }}
        <span class="estado">{% if j.status == 'descargando' %}bajando{% elif j.status == 'en_cola' %}en cola{% else %}Demucs{% endif %} · {{ j.elapsed }}s</span>
      </a>
    {% endfor %}
  </div>
</div>
{% endif %}

<div class="lista" id="sec-setlists">
  <h2>Setlists</h2>
  <div class="setlists-fila">
    {% for sid, sl in setlists.items() %}
      <a class="setlist-chip" href="{{ url_for('ver_setlist', setlist_id=sid) }}">
        {{ sl.nombre }} <span class="cant">{{ sl.canciones|length }}</span>
      </a>
    {% endfor %}
    <form class="setlist-crear" action="{{ url_for('crear_setlist') }}" method="post">
      <input type="text" name="nombre" placeholder="Nombre del setlist" maxlength="80" required>
      <button type="submit">Crear</button>
    </form>
  </div>
</div>

{% if recientes %}
<div class="lista">
  <h2>Últimas que abriste</h2>
  <div class="grid-canciones grid-canciones-recientes">
    {% for c in recientes %}
      <div class="cancion-fila" data-song="{{ c }}" style="--borde: {{ colores[c] }};">
        <a class="cancion" href="{{ url_for('mesa', song=c) }}" data-ini="{{ iniciales[c] }}">
          <span class="cancion-nombre" title="{{ datos[c].titulo }}">{{ datos[c].titulo }}</span>
          <span class="cancion-autor{{ ' sin-autor' if datos[c].autor == '----------' else '' }}" title="{{ datos[c].autor }}">{{ datos[c].autor }}</span>
        </a>
      </div>
    {% endfor %}
  </div>
</div>
{% endif %}

<div class="lista" id="sec-todas">
  {% if canciones %}
    <div class="lista-cabecera">
      <h2>Todas las canciones <span style="color:var(--fg-tenue); font-weight:400;">{{ canciones|length }}</span></h2>
      <button id="descargar-todas" type="button" class="boton-chico" title="Guardar todas las canciones en este dispositivo para tocar sin wifi, y actualizar las que ya estaban">Descargar todas</button>
      <select id="orden-canciones" class="orden-canciones" title="Ordenar la lista" aria-label="Ordenar la lista">
        <option value="titulo">Título A–Z</option>
        <option value="autor">Autor A–Z</option>
        <option value="archivo">Nombre de archivo</option>
      </select>
      <input type="text" id="buscar-cancion" class="buscador" placeholder="Buscar…" autocomplete="off">
    </div>
    <div class="grid-canciones" id="grid-todas">
      {% for c in canciones %}
        <div class="cancion-fila" data-song="{{ c }}" style="--borde: {{ colores[c] }};"
             data-buscar="{{ (datos[c].titulo ~ ' ' ~ datos[c].autor)|lower }}"
             data-titulo="{{ datos[c].titulo }}" data-autor="{{ '' if datos[c].autor == '----------' else datos[c].autor }}">
          <a class="cancion" href="{{ url_for('mesa', song=c) }}" data-ini="{{ iniciales[c] }}">
            <span class="cancion-nombre" title="{{ datos[c].titulo }}">{{ datos[c].titulo }}</span>
            <span class="cancion-autor{{ ' sin-autor' if datos[c].autor == '----------' else '' }}" title="{{ datos[c].autor }}">{{ datos[c].autor }}</span>
            {% if bpms[c] %}<span class="cancion-bpm">{{ bpms[c] }}</span>{% endif %}
          </a>
          <div class="cancion-acciones">
            <button class="renombrar-cancion" data-song="{{ c }}" data-titulo="{{ datos[c].titulo if datos[c].titulo != c else '' }}" data-autor="{{ '' if datos[c].autor == '----------' else datos[c].autor }}" title="Cambiar el título/autor que se muestran (no toca el archivo)" aria-label="Renombrar"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 20h4L18.5 9.5a2.1 2.1 0 0 0-3-3L5 17v3z"/><path d="M14 8l3 3"/></svg></button>
            <button class="borrar-cancion" data-song="{{ c }}" title="Borrar esta canción y sus pistas separadas" aria-label="Borrar">&#128465;</button>
          </div>
        </div>
      {% endfor %}
    </div>
    <p id="sin-resultados" class="vacio" style="display:none; margin-top:12px;">
      Ninguna canción coincide con la búsqueda.
    </p>
  {% else %}
    <h2>Todas las canciones</h2>
    <p class="vacio">
      Todavía no hay ninguna canción.<br>
      Subí un mp3 o pegá un link de YouTube ahí arriba y Mesa separa las pistas sola.
    </p>
  {% endif %}
</div>

<p id="resumen-offline" class="resumen-offline" style="display:none;"></p>

<!-- v107: Ajustes generales también desde la portada (el mismo panel que en
     cada tema). Los cambios se guardan en el servidor igual que allá. -->
<div id="cajon-fondo" class="cajon-fondo"></div>
<aside id="cajon-ajustes" class="cajon cajon-portada" aria-label="Ajustes generales" aria-hidden="true">
  <div class="cajon-cabecera">
    <span class="cajon-titulo">Ajustes generales</span>
    <button id="cerrar-ajustes" type="button" class="boton-chico boton-icono" title="Cerrar (Esc)" aria-label="Cerrar"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 6l12 12M18 6L6 18"/></svg></button>
  </div>
  <div class="cajon-cuerpo">
""" + PANEL_GENERALES_HTML + """
  </div>
</aside>
<style>
  .cajon-portada #panel-generales .panel-plegable-cabecera{ display:none; }
  .cajon-portada #panel-generales .panel-plegable-cuerpo{ display:grid !important; padding-top:18px; }
</style>
<script>
// v107: Ajustes generales desde la portada. Mismos controles y mismas
// preferencias que en la mesa; acá solo se guardan (no hay cartel que
// redibujar). Las gafas se manejan igual que allá, salvo "Conectar acá".
(function(){
  const cajon = document.getElementById("cajon-ajustes");
  const fondo = document.getElementById("cajon-fondo");
  if(!cajon || !fondo) return;
  function abrir(si){
    document.body.classList.toggle("cajon-abierto", si);
    cajon.setAttribute("aria-hidden", si ? "false" : "true");
    if(si) sondearBle();
  }
  document.querySelectorAll("[data-abrir-ajustes]").forEach(b => b.addEventListener("click", () => abrir(true)));
  document.getElementById("cerrar-ajustes").addEventListener("click", () => abrir(false));
  fondo.addEventListener("click", () => abrir(false));
  document.addEventListener("keydown", (e) => {
    if(e.key === "Escape" && document.body.classList.contains("cajon-abierto")) abrir(false);
  });

  function pref(clave, valor){
    return fetch("/preferencia", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ clave, valor }),
    }).then(r => r.json().catch(() => ({}))).catch(() => ({}));
  }
  function interruptor(id, clave, alCambiar){
    const b = document.getElementById(id);
    if(!b) return;
    b.addEventListener("click", () => {
      const v = !b.classList.contains("destacado");
      b.classList.toggle("destacado", v);
      pref(clave, v);
      if(alCambiar) alCambiar(v);
    });
  }

  // gafas: chips de estado
  const chipHud = document.getElementById("chip-hud-estado");
  function pintarHud(v){
    if(!chipHud) return;
    chipHud.classList.toggle("transmitiendo", v);
    chipHud.querySelector(".texto").textContent = v ? "transmitiendo" : "sin transmitir";
  }
  const btnHud = document.getElementById("toggle-hud");
  pintarHud(!!(btnHud && btnHud.classList.contains("destacado")));
  const btnBle = document.getElementById("toggle-hud-ble");
  const chipBle = document.getElementById("chip-hud-ble");
  function pintarBle(d){
    if(!chipBle) return;
    const conectado = !!(d && d.conectado);
    chipBle.classList.toggle("enlazado", conectado);
    chipBle.classList.toggle("buscando", !!(d && d.activo && !conectado));
    chipBle.querySelector(".texto").textContent =
      (!d || !d.activo) ? "bluetooth apagado" : (d.detalle || (conectado ? "conectado" : "buscando…"));
  }
  async function sondearBle(){
    if(!btnBle || !btnBle.classList.contains("destacado")){ pintarBle({ activo: false }); return; }
    try{
      const r = await fetch("/hud/estado", { cache: "no-store" });
      pintarBle(await r.json());
    }catch(e){ /* sin conexión: el chip de red ya lo dice */ }
  }
  setInterval(() => {
    if(!document.hidden && document.body.classList.contains("cajon-abierto")) sondearBle();
  }, 3000);
  sondearBle();

  interruptor("toggle-diagramas", "mostrar_diagramas");
  interruptor("toggle-grados", "mostrar_grados");
  interruptor("toggle-color-duracion", "colorear_duracion");
  interruptor("toggle-hud", "hud_activo", pintarHud);
  interruptor("toggle-hud-ble", "hud_ble", () => { pintarBle({ activo: btnBle.classList.contains("destacado"), detalle: null }); setTimeout(sondearBle, 600); });
  interruptor("toggle-hud-invertido", "hud_invertido");

  // color de la barra por banda de duración
  document.querySelectorAll(".colores-fila").forEach(fila => {
    const banda = fila.dataset.banda;
    fila.querySelectorAll(".swatch-color").forEach(btn => btn.addEventListener("click", () => {
      fila.querySelectorAll(".swatch-color").forEach(x => x.classList.toggle("seleccionado", x === btn));
      fila.style.setProperty("--sel", btn.style.getPropertyValue("--sw"));
      pref("color_" + banda, btn.dataset.stem);
    }));
  });

  // color de la app
  const presets = Array.from(document.querySelectorAll(".tema-preset"));
  const campo = document.getElementById("color-base");
  let actual = {{ color_base|tojson }};
  let temporizador = null;
  function marcar(){
    presets.forEach(b => b.classList.toggle("seleccionado", (b.dataset.color || "") === actual));
    if(campo) campo.value = (actual && actual.charAt(0) === "#") ? actual : "#f2b33d";
  }
  function elegir(hex, inmediato){
    actual = hex;
    if(window.mesaColorBase) window.mesaColorBase(hex);
    marcar();
    clearTimeout(temporizador);
    temporizador = setTimeout(() => pref("color_base", actual), inmediato ? 0 : 400);
  }
  presets.forEach(b => b.addEventListener("click", () => elegir(b.dataset.color || "", true)));
  if(campo) campo.addEventListener("input", () => elegir(campo.value.toLowerCase(), false));
  const btnOriginal = document.getElementById("color-base-original");
  if(btnOriginal) btnOriginal.addEventListener("click", () => elegir("", true));
  marcar();

  // brillo de las gafas
  const elBrillo = document.getElementById("hud-brillo-actual");
  const menos = document.getElementById("hud-brillo-menos"), mas = document.getElementById("hud-brillo-mas");
  if(elBrillo && menos && mas){
    let nivel = parseInt(elBrillo.dataset.nivel, 10) || 3;
    const tope = parseInt(elBrillo.dataset.max, 10) || 5;
    const pintar = () => {
      elBrillo.textContent = "brillo " + nivel + "/" + tope;
      menos.disabled = nivel <= 1; mas.disabled = nivel >= tope;
    };
    menos.addEventListener("click", () => { if(nivel > 1){ nivel--; pintar(); pref("hud_brillo", nivel); } });
    mas.addEventListener("click", () => { if(nivel < tope){ nivel++; pintar(); pref("hud_brillo", nivel); } });
    pintar();
  }

  // calidad del audio: por dispositivo (cookie), igual que en la mesa
  const grupoCal = document.querySelector("[data-calidad]");
  if(grupoCal){
    let cal = grupoCal.dataset.calidad || "estereo160";
    const botones = Array.from(grupoCal.querySelectorAll(".calidad"));
    const peso = document.getElementById("calidad-peso");
    const pintar = () => {
      const mono = cal.startsWith("mono"), b96 = cal.endsWith("96");
      botones.forEach(b => {
        if(b.dataset.canal) b.classList.toggle("marcado", (b.dataset.canal === "mono") === mono);
        if(b.dataset.bitrate) b.classList.toggle("marcado", (b.dataset.bitrate === "96") === b96);
      });
      if(peso) peso.textContent = (mono ? "mono" : "estéreo") + " · " + (b96 ? "96k" : "160k");
    };
    botones.forEach(btn => btn.addEventListener("click", () => {
      const mono = btn.dataset.canal ? btn.dataset.canal === "mono" : cal.startsWith("mono");
      const b96 = btn.dataset.bitrate ? btn.dataset.bitrate === "96" : cal.endsWith("96");
      cal = (mono ? "mono" : "estereo") + (b96 ? "96" : "160");
      document.cookie = "mesa_calidad=" + cal + "; path=/; max-age=31536000; SameSite=Lax";
      pintar();
    }));
    pintar();
  }
})();
</script>

<script>
// v102: el formulario de "agregar canción" arranca cerrado si ya hay
// canciones (la lista es lo que se usa todos los días) y se abre con el botón.
(function(){
  var b = document.getElementById("toggle-carga"), p = document.getElementById("panel-carga");
  if(!b || !p) return;
  b.addEventListener("click", function(){
    var abierta = p.classList.toggle("abierta");
    b.setAttribute("aria-expanded", abierta ? "true" : "false");
    if(abierta){ var c = p.querySelector(".campo-youtube"); if(c) c.focus(); }
  });
})();
</script>
<script>
// --- descargar / actualizar toda la biblioteca -----------------------------
// Un toque baja lo que falta y pone al día lo que ya estaba. La distinción la
// hace el servidor (ver urls_offline_partidas): las páginas y los datos se
// piden SIEMPRE porque son unos KB y es lo que cambia cuando se toca la app;
// el audio, que es lo pesado, solo si no está en el caché.
//
// Es una operación larga -- con la biblioteca entera por Tailscale puede ser
// media hora -- así que el mismo botón sirve para cancelar, y la cancelación
// se chequea entre archivo y archivo: lo ya bajado queda bajado.
(() => {
  const btn = document.getElementById("descargar-todas");
  if(!btn) return;

  if(!window.mesaOffline || !window.mesaOffline.soportado){
    const porHttp = location.protocol === "http:" && !["localhost","127.0.0.1"].includes(location.hostname);
    btn.textContent = porHttp ? "offline solo por https" : "sin offline";
    btn.disabled = true;
    btn.title = porHttp
      ? "Para guardar canciones hace falta entrar por https (Tailscale). Por IP local el navegador no lo permite."
      : "Este navegador no puede guardar canciones para tocar sin wifi";
    return;
  }

  let plan = null, estado = "listo", cancelar = false;

  function pintar(texto, clase, titulo){
    btn.classList.remove("destacado", "confirmando");
    if(clase) btn.classList.add(clase);
    btn.textContent = texto;
    if(titulo) btn.title = titulo;
  }

  function mb(bytes){ return (bytes / (1024 * 1024)).toFixed(0) + " MB"; }

  async function pedirPlan(){
    const r = await fetch("/offline/todas");
    if(!r.ok) throw new Error("HTTP " + r.status);
    return await r.json();
  }

  // Cuánto falta de verdad: solo cuenta el audio que no está en el caché.
  async function calcularFaltante(p){
    let temas = 0, bytes = 0;
    for(const c of p.canciones){
      if(!c.audio.length) continue;
      if(await window.mesaOffline.disponible(c.audio)) continue;
      temas++;
      bytes += c.bytes || 0;
    }
    return { temas, bytes };
  }

  async function confirmarYArrancar(){
    pintar("consultando…", "destacado");
    btn.disabled = true;
    try{
      plan = await pedirPlan();
    }catch(e){
      pintar("Descargar todas", null, "No pude consultar la biblioteca: " + e.message);
      btn.disabled = false;
      return;
    }
    const falta = await calcularFaltante(plan);
    btn.disabled = false;

    const espacio = await window.mesaOffline.usoAlmacenamiento();
    let aviso = "";
    if(espacio && espacio.cuota){
      const libre = espacio.cuota - espacio.usado;
      if(falta.bytes > libre * 0.9){
        aviso = " · OJO: puede no entrar (libre " + mb(libre) + ")";
      }
    }

    if(falta.temas === 0){
      // nada de audio nuevo, pero igual vale la pena refrescar las páginas
      estado = "confirmando";
      pintar("actualizar " + plan.canciones.length + " temas", "confirmando",
             "El audio ya está todo. Tocá de nuevo para actualizar las pantallas y los acordes guardados");
    } else {
      estado = "confirmando";
      pintar("bajar " + falta.temas + " temas (~" + mb(falta.bytes) + ")" + aviso, "confirmando",
             "Tocá de nuevo para empezar. Va a tardar; podés cancelar en cualquier momento");
    }
    setTimeout(() => {
      if(estado !== "confirmando") return;
      estado = "listo";
      pintar("Descargar todas", null);
    }, 6000);
  }

  async function correr(){
    estado = "bajando";
    cancelar = false;
    window.mesaHayDescargaEnCurso = true;
    let bajados = 0, actualizados = 0, fallados = 0;

    try{
      await window.mesaOffline.descargar(plan.comunes);
      const total = plan.canciones.length;

      for(let i = 0; i < total; i++){
        if(cancelar) break;
        const c = plan.canciones[i];
        const etiqueta = (i + 1) + "/" + total + " · " + c.titulo;

        try{
          // las páginas y los datos SIEMPRE: son unos KB y es lo que cambia
          // cuando se toca la app. La primera vez de un tema sin acordes
          // generados, /acordes dispara el análisis y puede tardar bastante.
          pintar(etiqueta + " (datos)", "destacado");
          await window.mesaOffline.descargar(c.paginas);
          actualizados++;

          if(c.audio.length && !(await window.mesaOffline.disponible(c.audio))){
            await window.mesaOffline.descargar(c.audio, (hecho, cant) => {
              btn.textContent = etiqueta + " (" + hecho + "/" + cant + ")";
            });
            bajados++;
          }
        }catch(e){
          // un tema que falla no corta la tanda entera: se sigue y se avisa al
          // final cuántos quedaron
          fallados++;
        }
      }
    }finally{
      window.mesaHayDescargaEnCurso = false;
      estado = "listo";
      pintar("Descargar todas", null, "Guardar todas las canciones en este dispositivo y actualizar las que ya estaban");
      if(window.marcarDescargadas) window.marcarDescargadas();

      let resumen = cancelar ? "Cancelado. " : "Listo. ";
      resumen += actualizados + " temas actualizados";
      if(bajados) resumen += ", " + bajados + " con audio nuevo";
      if(fallados) resumen += ". " + fallados + " fallaron (probá de nuevo)";
      mesaAviso(resumen, { error: fallados > 0, duracion: 9000 });
    }
  }

  btn.addEventListener("click", () => {
    if(estado === "bajando"){
      cancelar = true;
      pintar("cancelando…", "destacado");
      return;
    }
    if(estado === "confirmando"){ correr(); return; }
    confirmarYArrancar();
  });
})();

// v103: "Últimas que abriste" se rearma cada vez que se muestra la portada (al
// abrirla, con "Volver" y con el gesto "atrás"). Junta lo que sabe la PC
// (/recientes, que no guarda nadie en caché) con lo anotado en este dispositivo
// (window.mesaRecientes), así se actualiza también sin conexión. La portada en
// sí puede venir de una copia guardada; la lista ya no depende de eso.
(function(){
  const MAX = 5;
  function filaReciente(r){
    const fila = document.createElement("div");
    fila.className = "cancion-fila";
    fila.dataset.song = r.song;
    if(r.color) fila.style.setProperty("--borde", r.color);
    const a = document.createElement("a");
    a.className = "cancion";
    a.href = r.url;
    a.dataset.ini = r.ini || "";   // v107: portada con las iniciales del tema
    const nombre = document.createElement("span");
    nombre.className = "cancion-nombre";
    nombre.textContent = nombre.title = r.titulo;
    const autor = document.createElement("span");
    autor.className = "cancion-autor" + (r.autor === "----------" ? " sin-autor" : "");
    autor.textContent = autor.title = r.autor;
    a.appendChild(nombre); a.appendChild(autor); fila.appendChild(a);
    return fila;
  }
  // título, autor, color y enlace salen de la fila de "Todas las canciones":
  // así un tema renombrado se ve con el nombre nuevo, y uno borrado no aparece
  function datosDeFila(song){
    const fila = document.querySelector('#grid-todas .cancion-fila[data-song="' + CSS.escape(song) + '"]');
    if(!fila) return null;
    const link = fila.querySelector("a.cancion");
    return {
      song, url: link ? link.getAttribute("href") : "/mesa/" + encodeURIComponent(song),
      ini: link ? (link.dataset.ini || "") : "",
      titulo: fila.dataset.titulo || song, autor: fila.dataset.autor || "----------",
      color: fila.style.getPropertyValue("--borde").trim(),
    };
  }
  async function refrescarRecientes(){
    const R = window.mesaRecientes;
    if(R) await R.sincronizar();                 // lo abierto sin conexión, a la PC
    let deLaPc = null;
    try{
      const r = await fetch("/recientes", { cache: "no-store" });
      if(r.ok) deLaPc = await r.json();
    }catch(e){ /* sin conexión: se usa lo de este dispositivo */ }
    if(R && deLaPc) R.mezclar(deLaPc);
    const horas = R ? R.leer() : {};
    if(Array.isArray(deLaPc)) deLaPc.forEach(r => { if(!(horas[r.song] >= r.t)) horas[r.song] = r.t || 0; });
    const lista = Object.keys(horas)
      .sort((x, y) => horas[y] - horas[x])
      .map(datosDeFila).filter(Boolean).slice(0, MAX);
    if(!lista.length) return;
    let grid = document.querySelector(".grid-canciones-recientes");
    const firma = JSON.stringify(lista);
    if(grid && grid.dataset.firma === firma) return;   // ya está al día: no se toca el DOM
    if(!grid){
      // primera canción abierta: la sección todavía no existía en esta página
      const todas = document.getElementById("grid-todas");
      const destino = todas && todas.closest(".lista");
      if(!destino) return;
      const seccion = document.createElement("div");
      seccion.className = "lista";
      const h2 = document.createElement("h2");
      h2.textContent = "Últimas que abriste";
      grid = document.createElement("div");
      grid.className = "grid-canciones grid-canciones-recientes";
      seccion.appendChild(h2); seccion.appendChild(grid);
      destino.parentNode.insertBefore(seccion, destino);
    }
    grid.textContent = "";
    lista.forEach(r => grid.appendChild(filaReciente(r)));
    grid.dataset.firma = firma;
    if(window.marcarDescargadas) window.marcarDescargadas();
  }
  window.addEventListener("pageshow", refrescarRecientes);
})();

// orden de la lista: se reacomodan las filas en el navegador (no toca archivos ni la
// búsqueda). La elección se recuerda en este dispositivo; por defecto, título A-Z.
(function(){
  const selOrden = document.getElementById("orden-canciones");
  const grid = document.getElementById("grid-todas");
  if(!selOrden || !grid) return;
  const filas = Array.from(grid.querySelectorAll(".cancion-fila"));
  const cmp = new Intl.Collator("es", {sensitivity: "base", numeric: true});
  // "The Beatles" / "Los Enanitos" se ordenan igual; solo se ignoran signos al principio
  const limpio = t => (t || "").replace(/^[^0-9A-Za-zÀ-ÿ]+/, "");
  function ordenar(modo){
    const orden = filas.slice().sort((a, b) => {
      if(modo === "archivo") return cmp.compare(a.dataset.song, b.dataset.song);
      if(modo === "autor"){
        const aa = a.dataset.autor, bb = b.dataset.autor;
        if(!aa !== !bb) return aa ? -1 : 1;   // sin autor, al final
        const r = cmp.compare(limpio(aa), limpio(bb));
        if(r) return r;
      }
      return cmp.compare(limpio(a.dataset.titulo), limpio(b.dataset.titulo)) || cmp.compare(a.dataset.song, b.dataset.song);
    });
    orden.forEach(f => grid.appendChild(f));
  }
  let modo = "titulo";
  try { modo = localStorage.getItem("mesa-orden-canciones") || "titulo"; } catch(e) {}
  if(!["titulo", "autor", "archivo"].includes(modo)) modo = "titulo";
  selOrden.value = modo;
  ordenar(modo);
  selOrden.addEventListener("change", () => {
    ordenar(selOrden.value);
    try { localStorage.setItem("mesa-orden-canciones", selOrden.value); } catch(e) {}
  });
})();

// filtro en vivo de la lista de canciones: nada de servidor, solo esconder
// filas -- con la biblioteca grande es la diferencia entre buscar y scrollear
const campoBuscar = document.getElementById("buscar-cancion");
if(campoBuscar){
  const filas = Array.from(document.querySelectorAll("#grid-todas .cancion-fila"));
  const sinResultados = document.getElementById("sin-resultados");
  campoBuscar.addEventListener("input", () => {
    const q = campoBuscar.value.trim().toLowerCase();
    let visibles = 0;
    filas.forEach(f => {
      const ok = !q || (f.dataset.buscar || "").includes(q);
      f.style.display = ok ? "" : "none";
      if(ok) visibles++;
    });
    sinResultados.style.display = visibles ? "none" : "block";
  });
}

document.querySelectorAll(".renombrar-cancion").forEach(btn => {
  btn.addEventListener("click", (e) => {
    const fila = e.currentTarget.closest(".cancion-fila");
    if(fila.querySelector(".cancion-editar")) return; // ya se está editando
    const link = fila.querySelector(".cancion");
    const song = e.currentTarget.dataset.song;
    const tituloActual = e.currentTarget.dataset.titulo || "";
    const autorActual = e.currentTarget.dataset.autor || "";

    const editar = document.createElement("div");
    editar.className = "cancion cancion-editar";
    editar.innerHTML = `
      <input type="text" class="campo-renombrar campo-titulo" maxlength="120"
             placeholder="Título (vacío = nombre del archivo)">
      <input type="text" class="campo-renombrar campo-autor" maxlength="120"
             placeholder="Autor / banda (opcional)">
      <div class="cancion-editar-botones">
        <button type="button" class="boton-chico guardar-nombre">Guardar</button>
        <button type="button" class="boton-chico cancelar-nombre">Cancelar</button>
      </div>
    `;
    link.style.display = "none";
    fila.insertBefore(editar, link);
    const inputTitulo = editar.querySelector(".campo-titulo");
    const inputAutor = editar.querySelector(".campo-autor");
    inputTitulo.value = tituloActual;
    inputAutor.value = autorActual;
    inputTitulo.focus();
    inputTitulo.select();

    function cerrar(){
      editar.remove();
      link.style.display = "";
    }
    async function guardar(){
      try{
        const r = await fetch(`/alias/${encodeURIComponent(song)}`, {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({ titulo: inputTitulo.value.trim(), autor: inputAutor.value.trim() }),
        });
        const d = await r.json().catch(() => ({}));
        if(!r.ok) throw new Error(d.error || `HTTP ${r.status}`);
        // recarga entera: más simple que actualizar a mano la tarjeta en
        // "Recientes" y en "Todas" por separado
        location.reload();
      }catch(err){
        mesaAviso("No se pudo renombrar: " + err.message, { error: true });
      }
    }
    editar.querySelector(".guardar-nombre").addEventListener("click", guardar);
    editar.querySelector(".cancelar-nombre").addEventListener("click", cerrar);
    [inputTitulo, inputAutor].forEach(campo => campo.addEventListener("keydown", (ev) => {
      if(ev.key === "Enter"){ ev.preventDefault(); guardar(); }
      if(ev.key === "Escape"){ ev.preventDefault(); cerrar(); }
    }));
  });
});

document.querySelectorAll(".borrar-cancion").forEach(btn => {
  btn.addEventListener("click", async (e) => {
    const b = e.currentTarget;
    const song = b.dataset.song;
    // doble confirmación en el propio botón (window.confirm no anda bien en la
    // ventana embebida): primer click avisa, segundo dentro de 4s borra
    if(b.dataset.confirmando !== "1"){
      b.dataset.confirmando = "1";
      b.classList.add("confirmando");
      b.textContent = "¿borrar?";
      b.title = "Se borran las pistas separadas y los acordes corregidos. Tocá de nuevo para confirmar.";
      setTimeout(() => {
        if(b.dataset.confirmando !== "1") return;
        delete b.dataset.confirmando;
        b.classList.remove("confirmando");
        b.innerHTML = "&#128465;";
      }, 4000);
      return;
    }
    delete b.dataset.confirmando;
    b.disabled = true;
    b.textContent = "…";
    try{
      const r = await fetch(`/borrar/${encodeURIComponent(song)}`, { method: "POST" });
      const d = await r.json().catch(() => ({}));
      if(!r.ok) throw new Error(d.error || `HTTP ${r.status}`);
      await window.mesaOffline.borrarPorCancion(song);
      // recarga entera (no solo saca la fila) para que la sección "Recientes"
      // no quede mostrando una canción que ya no existe
      location.reload();
    }catch(err){
      mesaAviso("No se pudo borrar: " + err.message, { error: true });
      b.disabled = false;
      b.classList.remove("confirmando");
      b.innerHTML = "&#128465;";
    }
  });
});
</script>
"""

SETLIST_HTML = BASE_STYLE + """
<style>
  .setlist-header{
    width:100%; max-width:1080px; display:flex; align-items:center; gap:10px; margin-bottom:16px;
  }
  .setlist-header h1{ flex:1 1 auto; min-width:0; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  .setlist-fila-cancion{
    display:flex; align-items:center; gap:12px;
    background:var(--panel-2); border:1px solid transparent; border-radius:var(--r-m);
    padding:8px 8px 8px 14px; margin-bottom:6px;
    transition:background .14s;
  }
  .setlist-fila-cancion:hover{ background:var(--panel-3); }
  .setlist-pos{
    flex:0 0 auto; width:26px; height:26px; line-height:26px; text-align:center; font-family:var(--mono);
    color:var(--fg-dim); font-size:12px; background:var(--panel); border-radius:50%;
  }
  .setlist-fila-cancion .cancion{
    flex:1; min-width:0; display:flex; flex-direction:row; align-items:baseline; justify-content:flex-start; gap:10px;
    background:transparent; border:none; border-radius:0; padding:6px 0;
    text-decoration:none; color:var(--fg);
  }
  .setlist-fila-cancion .cancion::before{ display:none; }
  .setlist-fila-cancion .cancion:hover{ background:transparent; }
  .setlist-fila-cancion .cancion-nombre{
    -webkit-line-clamp:1; min-height:0; font-size:14px; font-weight:600;
  }
  .setlist-fila-cancion .cancion-autor{ white-space:nowrap; }
  .setlist-fila-acciones{ flex:0 0 auto; display:flex; gap:4px; }
  .setlist-fila-acciones button{
    background:transparent; color:var(--fg-tenue); border:1px solid transparent;
    border-radius:8px; padding:0; width:34px; height:34px; font-size:11px;
    display:inline-flex; align-items:center; justify-content:center;
  }
  .setlist-fila-acciones button svg{ width:16px; height:16px; }
  .setlist-fila-acciones button:hover{ color:var(--brass); background:var(--panel); }
  .setlist-fila-acciones .quitar-setlist:hover{ color:var(--led-mute); }
  .setlist-empezar{ display:flex; justify-content:center; align-items:center; gap:10px; flex-wrap:wrap; margin-bottom:20px; }
  .setlist-empezar .boton-primario{ display:inline-flex; align-items:center; gap:8px; padding:11px 20px; border-radius:999px; font-size:14px; }
  #descargar-setlist{ border-radius:999px; }
  #descargar-setlist.descargada{ color:var(--ok); border-color:rgba(var(--tinta),.45); background:rgba(var(--tinta),.10); }
  #descargar-setlist.trabajando{ color:var(--brass); border-color:rgba(var(--tinta),.45); background:rgba(var(--tinta),.10); cursor:progress; }
  .setlist-agregar{
    display:flex; gap:8px; margin-top:18px; padding-top:18px; border-top:1px solid var(--linea);
  }
  .setlist-agregar select{ flex:1; min-width:0; }
</style>

<div class="setlist-header">
  <a href="{{ url_for('home') }}" class="boton-chico boton-icono con-texto" title="Volver a la portada"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M15 18l-6-6 6-6"/></svg><span class="solo-ancho">Volver</span></a>
  <h1 style="margin:0;">{{ nombre }}</h1>
  <span id="ancla-red"></span>
  <button id="borrar-setlist" class="boton-chico boton-icono peligro" title="Borrar este setlist (no borra las canciones)" aria-label="Borrar setlist"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 7h16M9.5 7V4.8h5V7M6.5 7l.8 11.6a1.6 1.6 0 0 0 1.6 1.4h6.2a1.6 1.6 0 0 0 1.6-1.4L17.5 7M10 11v5M14 11v5"/></svg></button>
</div>

<div class="panel">
  {% if canciones %}
    <div class="setlist-empezar">
      <a id="setlist-empezar-link" href="{{ url_for('mesa', song=canciones[0]) }}?setlist={{ setlist_id }}" style="text-decoration:none;">
        <button type="button" class="boton-primario"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M7.5 4.8c0-.8.9-1.3 1.6-.9l10.3 6.3c.7.4.7 1.4 0 1.8L9.1 18.4c-.7.4-1.6-.1-1.6-.9z" fill="currentColor" stroke="none"/></svg> Empezar &middot; {{ canciones|length }} canciones</button>
      </a>
      <!-- Baja TODOS los temas del setlist de un tirón (antes había que abrir
           cada mesa y tocar su chip). Mismos tres estados que el chip de la
           mesa: gris = falta algo, verde = todo bajado (tocar = borrar, con
           confirmación), dorado = trabajando. -->
      <button id="descargar-setlist" type="button" class="boton-chico" title="Guardar todas las canciones de este setlist para tocar sin wifi">consultando…</button>
    </div>
    {% for c in canciones %}
      <div class="setlist-fila-cancion" data-song="{{ c }}">
        <span class="setlist-pos">{{ loop.index }}</span>
        <a class="cancion" href="{{ url_for('mesa', song=c) }}?setlist={{ setlist_id }}">
          <span class="cancion-nombre" title="{{ datos[c].titulo }}">{{ datos[c].titulo }}</span>
          <span class="cancion-autor{{ ' sin-autor' if datos[c].autor == '----------' else '' }}" title="{{ datos[c].autor }}">{{ datos[c].autor }}</span>
        </a>
        <div class="setlist-fila-acciones">
          <button class="mover-arriba" title="Subir" aria-label="Subir" {{ 'disabled' if loop.first else '' }}><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M18 15l-6-6-6 6"/></svg></button>
          <button class="mover-abajo" title="Bajar" aria-label="Bajar" {{ 'disabled' if loop.last else '' }}><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 9l6 6 6-6"/></svg></button>
          <button class="quitar-setlist" title="Sacar del setlist (no borra la canción)" aria-label="Sacar"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 6l12 12M18 6L6 18"/></svg></button>
        </div>
      </div>
    {% endfor %}
  {% else %}
    <p class="vacio">Este setlist todavía está vacío. Elegí una canción abajo para empezar a armarlo.</p>
  {% endif %}

  {% if para_agregar %}
    <form class="setlist-agregar" id="form-agregar">
      <select id="select-agregar">
        {% for c in para_agregar %}
          <option value="{{ c }}">{{ datos_agregar[c].titulo }}{% if datos_agregar[c].autor != '----------' %} &mdash; {{ datos_agregar[c].autor }}{% endif %}</option>
        {% endfor %}
      </select>
      <button type="submit">Agregar</button>
    </form>
  {% endif %}
</div>

<script>
const setlistId = "{{ setlist_id }}";

function ordenActual(){
  return Array.from(document.querySelectorAll(".setlist-fila-cancion")).map(f => f.dataset.song);
}

// Después de mover una fila se recalculan en el DOM el número de posición,
// los botones subir/bajar de los extremos y el link de "Empezar": ya no hace
// falta recargar la página entera por cada movimiento.
function refrescarFilas(){
  const filas = Array.from(document.querySelectorAll(".setlist-fila-cancion"));
  filas.forEach((f, i) => {
    const pos = f.querySelector(".setlist-pos");
    if(pos) pos.textContent = i + 1;
    const arriba = f.querySelector(".mover-arriba"), abajo = f.querySelector(".mover-abajo");
    if(arriba) arriba.disabled = (i === 0);
    if(abajo) abajo.disabled = (i === filas.length - 1);
  });
  const empezar = document.getElementById("setlist-empezar-link");
  if(empezar && filas.length) empezar.href = `/mesa/${encodeURIComponent(filas[0].dataset.song)}?setlist=${setlistId}`;
}

async function guardarOrden(){
  try{
    const r = await fetch(`/setlist/${setlistId}/orden`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ canciones: ordenActual() }),
    });
    if(!r.ok) throw new Error(`HTTP ${r.status}`);
  }catch(e){
    mesaAviso("No se pudo guardar el orden: " + e.message, { error: true });
  }
}

document.querySelectorAll(".mover-arriba").forEach(btn => {
  btn.addEventListener("click", async () => {
    const fila = btn.closest(".setlist-fila-cancion");
    const anterior = fila.previousElementSibling;
    if(!anterior || !anterior.classList.contains("setlist-fila-cancion")) return;
    fila.parentNode.insertBefore(fila, anterior);
    refrescarFilas();
    await guardarOrden();
  });
});
document.querySelectorAll(".mover-abajo").forEach(btn => {
  btn.addEventListener("click", async () => {
    const fila = btn.closest(".setlist-fila-cancion");
    const siguiente = fila.nextElementSibling;
    if(!siguiente || !siguiente.classList.contains("setlist-fila-cancion")) return;
    fila.parentNode.insertBefore(siguiente, fila);
    refrescarFilas();
    await guardarOrden();
  });
});

document.querySelectorAll(".quitar-setlist").forEach(btn => {
  btn.addEventListener("click", async () => {
    const song = btn.closest(".setlist-fila-cancion").dataset.song;
    try{
      await fetch(`/setlist/${setlistId}/quitar`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ song }),
      });
      location.reload();
    }catch(err){
      mesaAviso("No se pudo sacar la canción: " + err.message, { error: true });
    }
  });
});

const formAgregar = document.getElementById("form-agregar");
if(formAgregar){
  formAgregar.addEventListener("submit", async (e) => {
    e.preventDefault();
    const song = document.getElementById("select-agregar").value;
    try{
      await fetch(`/setlist/${setlistId}/agregar`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ song }),
      });
      location.reload();
    }catch(err){
      mesaAviso("No se pudo agregar la canción: " + err.message, { error: true });
    }
  });
}

const btnBorrarSetlist = document.getElementById("borrar-setlist");
btnBorrarSetlist.addEventListener("click", async () => {
  if(btnBorrarSetlist.dataset.confirmando !== "1"){
    btnBorrarSetlist.dataset.confirmando = "1";
    btnBorrarSetlist.classList.add("confirmando");
    btnBorrarSetlist.title = "Tocá de nuevo para confirmar (no borra las canciones, solo la lista)";
    setTimeout(() => {
      delete btnBorrarSetlist.dataset.confirmando;
      btnBorrarSetlist.classList.remove("confirmando");
    }, 4000);
    return;
  }
  try{
    await fetch(`/setlist/${setlistId}/borrar`, { method: "POST" });
    window.location = "{{ url_for('home') }}";
  }catch(err){
    mesaAviso("No se pudo borrar el setlist: " + err.message, { error: true });
  }
});

// --- descargar el setlist completo para tocar sin wifi ----------------------
(() => {
  const btn = document.getElementById("descargar-setlist");
  if(!btn) return;
  if(!window.mesaOffline || !window.mesaOffline.soportado){
    const porHttp = location.protocol === "http:" && !["localhost","127.0.0.1"].includes(location.hostname);
    btn.textContent = porHttp ? "offline solo por https" : "sin offline";
    btn.disabled = true;
    return;
  }
  const calidadActual = "{{ calidad_actual }}";
  let plan = null, todoBajado = false, confirmando = false, ocupado = false, temporizador = null;

  function pintar(clase, texto, titulo){
    btn.classList.remove("descargada", "trabajando", "confirmando");
    if(clase) btn.classList.add(clase);
    btn.textContent = texto;
    if(titulo) btn.title = titulo;
  }

  async function cargarPlan(){
    const r = await fetch(`/setlist/${setlistId}/offline`);
    const d = await r.json();
    if(!r.ok) throw new Error(d.error || `HTTP ${r.status}`);
    return d;
  }

  async function refrescarEstado(){
    clearTimeout(temporizador); confirmando = false;
    try{ plan = await cargarPlan(); }
    catch(e){ pintar(null, "descargar setlist", "No pude consultar el setlist: " + e.message); btn.disabled = false; return; }
    let faltan = 0, bytes = 0;
    for(const c of plan.canciones){
      if(await window.mesaOffline.disponible(c.urls)) bytes += await window.mesaOffline.tamanoBytes(c.urls);
      else faltan++;
    }
    todoBajado = plan.canciones.length > 0 && faltan === 0;
    if(todoBajado){
      pintar("descargada", `todo sin wifi · ${window.mesaOffline.fmtMB(bytes)}`, "Las " + plan.canciones.length + " canciones están guardadas. Tocá para borrar las descargas de este setlist");
    } else {
      pintar(null, faltan === plan.canciones.length ? "descargar setlist" : `descargar setlist (faltan ${faltan})`,
             "Guarda todas las canciones de este setlist para tocar sin wifi");
    }
    btn.disabled = false;
    if(window.marcarDescargadas) window.marcarDescargadas();
  }

  btn.addEventListener("click", async () => {
    if(ocupado || !plan) return;
    if(todoBajado && !confirmando){
      confirmando = true;
      pintar("confirmando", "¿borrar descargas?", "Tocá otra vez para borrar las descargas de todas las canciones del setlist");
      temporizador = setTimeout(refrescarEstado, 4000);
      return;
    }
    ocupado = true; btn.disabled = true;
    try{
      if(confirmando){
        confirmando = false;
        pintar("trabajando", "borrando…");
        for(const c of plan.canciones) await window.mesaOffline.borrarPorCancion(c.song);
      } else {
        window.mesaHayDescargaEnCurso = true;
        const total = plan.canciones.length;
        // primero las páginas comunes (portada y este setlist)
        await window.mesaOffline.descargar(plan.paginas);
        for(let i = 0; i < total; i++){
          const c = plan.canciones[i];
          if(await window.mesaOffline.disponible(c.urls)) continue;   // ya estaba
          pintar("trabajando", `${i + 1}/${total} · ${c.titulo}`);
          await window.mesaOffline.descargar(c.urls, (hecho, cant) => {
            btn.textContent = `${i + 1}/${total} · ${c.titulo} (${hecho}/${cant})`;
          });
          try{ localStorage.setItem(`mesaCalidad:${c.song}`, calidadActual); }catch(e){}
        }
      }
    }catch(err){
      mesaAviso("No se pudo completar la descarga del setlist: " + err.message, { error: true });
    }finally{
      ocupado = false;
      window.mesaHayDescargaEnCurso = false;
      await refrescarEstado();
    }
  });

  refrescarEstado();
})();
</script>
"""

PROCESANDO_HTML = BASE_STYLE + """
<!-- v113: ventana de progreso al estilo "transcribiendo": anillo con el
     porcentaje real de Demucs, barra, tiempo transcurrido / estimado y tips. -->
<style>
  body{ justify-content:center; align-items:center; min-height:100vh; }
  .proc-velo{
    position:fixed; inset:0; z-index:0; pointer-events:none;
    background:radial-gradient(600px 380px at 50% 45%, color-mix(in srgb, var(--brass) 10%, transparent), transparent 70%);
  }
  .proc-ventana{
    position:relative; z-index:1; width:min(560px, calc(100vw - 32px)); box-sizing:border-box;
    background:var(--panel); border:1px solid var(--panel-3); border-radius:16px;
    box-shadow:0 24px 60px rgba(0,0,0,.45); padding:30px 28px 22px; text-align:center;
  }
  .proc-titulo{ margin:0; font-size:18px; font-weight:550; color:var(--fg); }
  .proc-tema{
    margin:6px 0 0; font-size:15px; font-weight:700; font-style:italic; color:var(--fg);
    overflow:hidden; text-overflow:ellipsis; white-space:nowrap; min-height:20px;
  }
  .proc-anillo{ position:relative; width:118px; height:118px; margin:24px auto 26px; }
  .proc-anillo svg{ position:absolute; inset:0; width:100%; height:100%; overflow:visible; }
  .proc-anillo .pista{ stroke:var(--panel-3); }
  .proc-anillo .avance{
    stroke:var(--brass); stroke-linecap:round; transform:rotate(-90deg); transform-origin:50% 50%;
    transition:stroke-dashoffset .6s ease;
  }
  .proc-anillo .orbita{ transform-origin:50% 50%; animation:proc-gira 2.4s linear infinite; }
  .proc-anillo .orbita circle{ stroke:var(--brass); opacity:.55; stroke-linecap:round; }
  .proc-anillo.sin-pct .avance{ opacity:0; }
  .proc-anillo.sin-pct .orbita{ animation-duration:1.1s; }
  .proc-anillo.sin-pct .orbita circle{ opacity:1; }
  .proc-pct{
    position:absolute; inset:0; display:flex; align-items:center; justify-content:center;
    font-size:24px; font-weight:800; color:var(--fg); font-variant-numeric:tabular-nums;
  }
  .proc-anillo.con-error .avance, .proc-anillo.con-error .orbita circle{ stroke:var(--led-mute); }
  .proc-anillo.con-error .orbita{ display:none; }
  .proc-anillo.con-error .proc-pct{ color:var(--led-mute); }
  @keyframes proc-gira{ to{ transform:rotate(360deg); } }

  .proc-barra{ height:8px; border-radius:999px; background:var(--panel-3); overflow:hidden; }
  .proc-barra i{
    display:block; height:100%; width:0; border-radius:999px; background:var(--brass);
    transition:width .6s ease;
  }
  .proc-barra.indefinida i{ width:30%; animation:proc-corre 1.4s ease-in-out infinite; }
  .proc-barra.con-error i{ background:var(--led-mute); animation:none; }
  @keyframes proc-corre{ 0%{ transform:translateX(-100%); } 100%{ transform:translateX(340%); } }
  .proc-tiempos{
    display:flex; justify-content:space-between; gap:12px; margin:8px 0 18px;
    font-size:13px; font-weight:600; color:var(--fg); font-variant-numeric:tabular-nums;
  }
  .proc-tiempos #proc-estimado{ color:var(--fg-dim); }

  .proc-tip{
    display:flex; align-items:center; justify-content:center; gap:10px; min-height:48px;
    background:var(--panel-2); border-radius:10px; padding:12px 16px;
    font-size:13px; color:var(--fg); text-align:left; transition:opacity .35s ease;
  }
  .proc-tip svg{ flex:0 0 auto; width:18px; height:18px; color:var(--brass); }
  .proc-tip.oculto{ opacity:0; }

  .proc-error{
    display:none; margin:0 0 16px; padding:12px 14px; border-radius:10px; text-align:left;
    background:color-mix(in srgb, var(--led-mute) 12%, var(--panel-2));
    color:var(--fg); font-size:13px; line-height:1.55; white-space:pre-line;
    max-height:40vh; overflow:auto;
  }
  .proc-pie{ margin-top:16px; font-size:12.5px; }
  .proc-pie a{ color:var(--fg-dim); text-decoration:none; }
  .proc-pie a:hover{ color:var(--fg); text-decoration:underline; }
  #procesando-volver{ display:none; margin-top:4px; text-decoration:none; }
</style>
<div class="proc-velo" aria-hidden="true"></div>
<div class="proc-ventana" role="status" aria-live="polite">
  <p class="proc-titulo" id="proc-titulo">Separando pistas de:</p>
  <p class="proc-tema" id="proc-tema">{{ titulo_tema or "…" }}</p>

  <div class="proc-anillo sin-pct" id="proc-anillo">
    <svg viewBox="0 0 120 120" aria-hidden="true">
      <circle class="pista" cx="60" cy="60" r="44" fill="none" stroke-width="4"/>
      <circle class="avance" id="proc-arco" cx="60" cy="60" r="44" fill="none" stroke-width="4"
              stroke-dasharray="276.46" stroke-dashoffset="276.46"/>
      <g class="orbita">
        <circle cx="60" cy="60" r="55" fill="none" stroke-width="3" stroke-dasharray="70 276"/>
        <circle cx="60" cy="60" r="55" fill="none" stroke-width="2" stroke-dasharray="26 320" stroke-dashoffset="-175"/>
      </g>
    </svg>
    <div class="proc-pct" id="proc-pct">…</div>
  </div>

  <div class="proc-barra indefinida" id="proc-barra"><i id="proc-relleno"></i></div>
  <div class="proc-tiempos">
    <span id="proc-etapa">empezando (00:00)</span>
    <span id="proc-estimado"></span>
  </div>

  <div class="proc-error" id="proc-error"></div>
  <div class="proc-tip" id="proc-tip">
    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 18h6M10 22h4"/><path d="M12 2a7 7 0 0 0-4 12.7c.6.5 1 1.3 1 2.1V17h6v-.2c0-.8.4-1.6 1-2.1A7 7 0 0 0 12 2z"/></svg>
    <span id="proc-tip-texto">Cuando termine, la pantalla pasa sola al mezclador.</span>
  </div>
  <a id="procesando-volver" href="{{ url_for('home') }}"><button type="button" class="boton-primario">&larr; Volver</button></a>
  <div class="proc-pie" id="proc-pie">
    <a href="{{ url_for('home') }}">Ir a la portada &mdash; sigue en segundo plano</a>
  </div>
</div>
<script>
  const jobId = "{{ job_id }}";
  const $ = id => document.getElementById(id);
  const CIRC = 276.46;   // 2·π·44

  const TIPS = [
    "Cuando termine, la pantalla pasa sola al mezclador.",
    "Podés ir a la portada: el trabajo sigue en la PC y aparece en «En proceso».",
    "Demucs usa casi toda la CPU: si la PC se pone lenta mientras tanto, es normal.",
    "Si tenés el MIDI de Chordify del tema, importalo después y los acordes quedan exactos.",
    "Las pistas quedan guardadas: la próxima vez el tema abre al instante.",
  ];
  let tipIdx = 0;
  const relojTips = setInterval(() => {
    const t = $("proc-tip");
    t.classList.add("oculto");
    setTimeout(() => {
      tipIdx = (tipIdx + 1) % TIPS.length;
      $("proc-tip-texto").textContent = TIPS[tipIdx];
      t.classList.remove("oculto");
    }, 350);
  }, 7000);

  const mmss = s => {
    s = Math.max(0, Math.round(s || 0));
    const h = Math.floor(s / 3600), m = Math.floor((s % 3600) / 60), x = s % 60;
    const p = n => String(n).padStart(2, "0");
    return h ? `${h}:${p(m)}:${p(x)}` : `${p(m)}:${p(x)}`;
  };

  // El tiempo corre de a un segundo en pantalla aunque el sondeo sea cada 1,5 s
  // (o se corte un rato el wifi): se ancla al último "elapsed" del servidor.
  let base = { elapsed: 0, en: performance.now() };
  let etapaTxt = "empezando";
  let terminado = false;
  const relojTiempo = setInterval(() => {
    if(terminado) return;
    const seg = base.elapsed + (performance.now() - base.en) / 1000;
    $("proc-etapa").textContent = `${etapaTxt} (${mmss(seg)})`;
  }, 250);

  function pintarPct(pct){
    const anillo = $("proc-anillo"), barra = $("proc-barra");
    if(pct == null){
      anillo.classList.add("sin-pct"); barra.classList.add("indefinida");
      $("proc-pct").textContent = "…";
      return;
    }
    const v = Math.max(0, Math.min(100, pct));
    anillo.classList.remove("sin-pct"); barra.classList.remove("indefinida");
    $("proc-arco").style.strokeDashoffset = CIRC * (1 - v / 100);
    $("proc-relleno").style.width = v + "%";
    $("proc-pct").textContent = Math.floor(v) + "%";
  }

  const ETAPAS = {
    en_cola: "en cola",
    descargando: "descargando de YouTube",
    cargando: "cargando el modelo",
    separando: "separando",
    mp3: "preparando las pistas",
  };

  let fallosSeguidos = 0;
  async function poll(){
    let j, r;
    try{
      r = await fetch(`/estado/${jobId}`, { cache: "no-store" });
      j = await r.json();
      fallosSeguidos = 0;
    }catch(e){
      fallosSeguidos++;
      etapaTxt = `sin conexión con Mesa, reintentando (${fallosSeguidos})`;
      setTimeout(poll, Math.min(3000 + fallosSeguidos * 500, 8000));
      return;
    }
    if(r.status === 404){
      mostrarError("Mesa se reinició y este trabajo ya no existe. Volvé y subí el tema de nuevo.");
      return;
    }
    base = { elapsed: j.elapsed || 0, en: performance.now() };
    if(j.titulo) $("proc-tema").textContent = j.titulo;
    if(j.status === "listo"){
      pintarPct(100);
      etapaTxt = "listo";
      setTimeout(() => { window.location = j.redirect; }, 350);
      return;
    }
    if(j.status === "error"){
      mostrarError(j.log || "ver consola");
      return;
    }
    const clave = j.status === "procesando" ? (j.etapa || "cargando") : j.status;
    etapaTxt = ETAPAS[clave] || j.status;
    $("proc-titulo").textContent = j.status === "descargando" ? "Descargando el audio de:" : "Separando pistas de:";
    // Mientras carga el modelo o está en cola no hay porcentaje real: anillo girando.
    const hayPct = j.status === "procesando" && clave !== "cargando" && j.progreso != null;
    pintarPct(hayPct ? j.progreso : null);
    $("proc-estimado").textContent = j.estimado ? `(Estimado: ${mmss(j.estimado)})` : "";
    setTimeout(poll, 1500);
  }

  function mostrarError(texto){
    terminado = true;
    clearInterval(relojTips); clearInterval(relojTiempo);
    $("proc-titulo").textContent = "No se pudo separar:";
    $("proc-anillo").classList.remove("sin-pct");
    $("proc-anillo").classList.add("con-error");
    $("proc-pct").textContent = "!";
    $("proc-arco").style.strokeDashoffset = 0;
    $("proc-barra").classList.remove("indefinida");
    $("proc-barra").classList.add("con-error");
    $("proc-relleno").style.width = "100%";
    $("proc-etapa").textContent = "error";
    $("proc-estimado").textContent = "";
    const e = $("proc-error");
    e.textContent = texto;
    e.style.display = "block";
    $("proc-tip").style.display = "none";
    $("proc-pie").style.display = "none";
    $("procesando-volver").style.display = "inline-block";
  }
  poll();
</script>
"""

MESA_HTML = BASE_STYLE + """
<!-- Cabecera tipo barra de app: volver + título a la izquierda; estado,
     ajustes y modo tocar a la derecha. -->
<div class="cabecera-mesa">
  <a href="{{ url_for('home') }}" class="boton-chico boton-icono con-texto" style="flex:0 0 auto;" title="Volver a la portada"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M15 18l-6-6 6-6"/></svg><span class="solo-ancho volver-texto">Volver</span></a>
  <span class="cancion-portada" style="--pc: {{ color_cancion }};" aria-hidden="true">{{ iniciales }}</span>
  <div class="titulo-bloque">
    <h1>{{ titulo }}</h1>
    <span id="sub-cancion">{{ autor }}</span>
  </div>
  <div class="estado-grupo">
    <span id="ancla-red"></span>
    <span id="chip-pedal" style="display:none;"><span class="punto"></span><svg class="ico-chip" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="5" y="9" width="14" height="11" rx="2.5"/><circle cx="12" cy="14.5" r="2.4"/><path d="M8 9V6M16 9V6"/></svg><span class="texto"></span></span>
    <!-- Descarga offline: es una acción POR DISPOSITIVO (la tablet y la PC
         tienen descargas distintas), por eso vive al lado del tema. -->
    <button id="chip-offline" type="button" title="Guardar esta canción para tocarla sin wifi">
      <span class="punto"></span><svg class="ico-chip" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M12 4v11M7 10l5 5 5-5M5 20h14"/></svg><span class="texto">consultando…</span>
    </button>
  </div>
  <div class="acciones-cabecera">
    <div class="accesos-ajustes" role="group" aria-label="Ajustes">
      <button type="button" class="boton-chico" data-seccion="mezcla" title="Mezcla: volumen, mute y guía de cada pista"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 4v16M12 4v16M18 4v16"/><rect x="4" y="13" width="4" height="3" rx="1" fill="currentColor"/><rect x="10" y="6" width="4" height="3" rx="1" fill="currentColor"/><rect x="16" y="10" width="4" height="3" rx="1" fill="currentColor"/></svg><span class="solo-ancho">Mezcla</span></button>
      <button type="button" class="boton-chico" data-seccion="tema" title="Ajustes de este tema: acordes, sincronía, tempo y cejilla"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 18V6l10-2v12"/><circle cx="6.5" cy="18" r="2.5"/><circle cx="16.5" cy="16" r="2.5"/></svg><span class="solo-ancho">Tema</span></button>
      <button type="button" class="boton-chico" data-seccion="generales" title="Ajustes generales: qué se ve en el cartel, calidad y colores"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 6h9M17 6h3M4 12h3M11 12h9M4 18h11M19 18h1"/><circle cx="15" cy="6" r="2"/><circle cx="9" cy="12" r="2"/><circle cx="17" cy="18" r="2"/></svg><span class="solo-ancho">General</span></button>
      <button type="button" class="boton-chico" data-seccion="gafas" title="Gafas HUD: conexión, colores y brillo"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="7" cy="14" r="3.5"/><circle cx="17" cy="14" r="3.5"/><path d="M10.5 14h3M3.5 13 5 7M20.5 13 19 7"/></svg><span class="solo-ancho">Gafas</span></button>
    </div>
    <button id="mostrar-pistas" type="button" class="boton-chico" title="Mostrar las pistas al costado" aria-label="Mostrar las pistas al costado"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="4" width="18" height="16" rx="2"/><path d="M15 4v16M8 10l2 2-2 2"/></svg></button>
    <button id="abrir-ajustes" type="button" class="boton-chico boton-icono con-texto" title="Mezcla, ajustes del tema y ajustes generales" aria-controls="cajon-ajustes" aria-expanded="false"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 6h9M17 6h3M4 12h3M11 12h9M4 18h11M19 18h1"/><circle cx="15" cy="6" r="2"/><circle cx="9" cy="12" r="2"/><circle cx="17" cy="18" r="2"/></svg><span class="solo-ancho">Ajustes</span></button>
    <button id="toggle-modo-tocar" class="boton-chico" style="flex:0 0 auto;" title="Dejar solo el cartel de acordes y el transporte, en grande (Esc para salir)">Modo tocar</button>
  </div>
</div>

{% if setlist %}
<div class="setlist-nav">
  {% if setlist.anterior %}
    <a href="{{ url_for('mesa', song=setlist.anterior) }}?setlist={{ setlist.id }}" class="boton-chico boton-icono con-texto" title="Tema anterior del setlist"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M15 18l-6-6 6-6"/></svg><span class="solo-ancho">Anterior</span></a>
  {% else %}
    <span class="boton-chico boton-icono con-texto deshabilitado"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M15 18l-6-6 6-6"/></svg><span class="solo-ancho">Anterior</span></span>
  {% endif %}
  <a href="{{ url_for('ver_setlist', setlist_id=setlist.id) }}" class="setlist-nav-nombre">{{ setlist.nombre }} &middot; {{ setlist.posicion }}/{{ setlist.total }}</a>
  {% if setlist.siguiente %}
    <a href="{{ url_for('mesa', song=setlist.siguiente) }}?setlist={{ setlist.id }}" class="boton-chico boton-icono con-texto" style="flex-direction:row-reverse; padding-left:12px; padding-right:9px;" title="Tema siguiente del setlist"><span class="solo-ancho">Siguiente</span><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 18l6-6-6-6"/></svg></a>
  {% else %}
    <span class="boton-chico boton-icono con-texto deshabilitado" style="flex-direction:row-reverse; padding-left:12px; padding-right:9px;"><span class="solo-ancho">Siguiente</span><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 18l6-6-6-6"/></svg></span>
  {% endif %}
</div>
{% endif %}

<!-- v107: cartel (y editor) a la izquierda, lista de pistas a la derecha -->
<div class="zona-principal">
<div class="zona-acordes">

<!-- 1. Los acordes: lo único que se mira mientras tocás, solo arriba y a
        todo el ancho. -->
<div class="panel acordes-display">
  <div class="chips-cartel">
    <div id="chip-capo"></div>
  </div>
  <div id="cuenta-regresiva" class="cuenta-regresiva" aria-hidden="true"></div>
  <div id="cinta" class="cinta" aria-hidden="true">
    <div id="cinta-pista" class="cinta-pista"></div>
    <div id="cinta-fijo" class="cinta-acorde cinta-fijo"></div>
  </div>
  <div class="fila-acordes">
    <div id="diagrama-actual" class="diagrama"></div>
    <div id="grado-actual" class="grado-chico"></div>
    <div id="acorde-actual" class="acorde-grande">&mdash;</div>
    <div id="grado-siguiente" class="grado-chico grado-chico-sig"></div>
    <div id="acorde-siguiente" class="acorde-grande" title="próximo acorde">&nbsp;</div>
    <div id="diagrama-siguiente" class="diagrama diagrama-sig"></div>
  </div>
  <div class="barra-acorde">
    <div id="barra-acorde-relleno" class="barra-acorde-relleno"></div>
  </div>
  <div id="puntos-compas" class="puntos-compas">
    <span class="punto"></span><span class="punto"></span><span class="punto"></span><span class="punto"></span>
  </div>
  <div id="linea-progresion" class="linea-progresion" style="display:none;"></div>
</div>

<div id="acordes-advertencia" class="aviso" style="display:none;"></div>

<!-- 2. Editor de acordes: se abre desde el cajón de ajustes y aparece acá,
        debajo del cartel, para editar mirando el compás que suena. -->
<div id="panel-editor" class="panel" style="display:none;">
  <div class="editor-cabecera">
    <span class="editor-titulo">Editor de acordes</span>
    <span style="flex:1;"></span>
    <span id="editor-estado" class="editor-estado">&nbsp;</span>
    <button id="editor-guardar" class="boton-chico destacado">Guardar</button>
    <button id="editor-cerrar" class="boton-chico">Cerrar</button>
  </div>
  <div id="editor-grilla" class="editor-grilla"></div>
</div>

</div>
<aside id="columna-pistas" aria-label="Pistas">
  <div class="pistas-cabecera">
    <span class="pistas-titulo">Pistas</span>
    <button id="ocultar-pistas" type="button" class="boton-chico boton-icono" title="Ocultar las pistas y agrandar los acordes" aria-label="Ocultar las pistas"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="4" width="18" height="16" rx="2"/><path d="M15 4v16M10 10l-2 2 2 2"/></svg></button>
  </div>
  <div id="columna-pistas-cuerpo"></div>
</aside>
</div>

<!-- 3. Transporte + herramientas de estudio: barra fija abajo, tipo
        reproductor. Siempre visible, también en modo tocar y con el cajón
        abierto. -->
<div class="panel barra-transporte" id="panel-transporte">
  <div id="rapidos" class="rapidos">
    {% for p in pistas %}
    <button class="rapido" data-stem="{{ p.id }}" style="--pista-color: {{ p.color }};" title="{{ p.label }}" aria-label="Mute {{ p.label }}"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"></svg></button>
    {% endfor %}
    <span class="rapidos-sep"></span>
    <button id="rapido-gafas" class="rapido rapido-gafas" title="Gafas HUD" aria-label="Conectar gafas HUD"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="6.5" cy="14" r="3.5" fill="currentColor" fill-opacity=".18"/><circle cx="17.5" cy="14" r="3.5" fill="currentColor" fill-opacity=".18"/><path d="M10 14c.7-.8 3.3-.8 4 0"/><path d="M3 14l1.5-6.5L7 6.5M21 14l-1.5-6.5L17 6.5"/></svg></button>
  </div>
  <div id="transporte" class="transporte">
    <div class="transporte-botones">
      <button id="rebobinar" title="Volver al principio (o al inicio del loop, si hay uno)" aria-label="Volver al principio"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 5v14"/><path d="M18.5 5.6v12.8a.8.8 0 0 1-1.2.7L8.6 12.7a.8.8 0 0 1 0-1.4l8.7-6.4a.8.8 0 0 1 1.2.7z" fill="currentColor" stroke="none"/></svg></button>
      <button id="play" aria-label="Reproducir / pausa">&#9654;</button>
      <div class="compas-nav" title="Compás que está sonando">
        <button id="compas-ant" title="Ir al principio de este compás (de nuevo: al anterior)" aria-label="Compás anterior"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M15 18l-6-6 6-6"/></svg></button>
        <span id="compas-num">c.&mdash;</span>
        <button id="compas-sig" title="Ir al compás siguiente" aria-label="Compás siguiente"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 18l6-6-6-6"/></svg></button>
      </div>
    </div>
    <div class="transporte-linea">
      <span id="tiempo">0:00 / 0:00</span>
      <input id="seek" type="range" min="0" max="1000" value="0" aria-label="Posición">
    </div>
  </div>

  <div id="barra-estudio" class="barra-estudio">
    <div class="estudio-grupo">
      <span class="estudio-tit">Loop</span>
      <button id="loop-compas" class="boton-chico btn-ico-lbl" title="Loop de este compás"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M17 2l3 3-3 3M4 11V9a4 4 0 0 1 4-4h12M7 22l-3-3 3-3M20 13v2a4 4 0 0 1-4 4H4"/></svg>Compás</button>
      <button id="loop-a" class="boton-chico" title="Inicio del loop">A</button>
      <button id="loop-b" class="boton-chico" title="Fin del loop">B</button>
      <button id="loop-limpiar" class="boton-chico" title="Sacar el loop" aria-label="Sacar el loop"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 6l12 12M18 6L6 18"/></svg></button>
      <button id="toggle-claqueta" class="boton-chico btn-ico-lbl destacado" title="Claqueta en cada vuelta"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6.5 21L9.5 3h5l3 18z"/><path d="M12 15l5-7"/></svg>Claqueta</button>
      <span id="loop-info" class="estudio-valor">sin loop</span>
    </div>

    <!-- La tira de lo que viene se prende desde acá y no desde "Ajustes del
         tema": ese panel se oculta en modo tocar, que es justamente donde más
         falta hace ver los compases que siguen. -->
    <div class="estudio-grupo">
      <span class="estudio-tit">Vista</span>
      <button id="toggle-cinta" class="boton-chico btn-ico-lbl{{ ' destacado' if vista_cinta else '' }}" title="Vista cinta"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="7" width="18" height="10" rx="2"/><path d="M8 7v10M13 7v10M18 7v10"/></svg>Cinta</button>
      <button id="toggle-cuenta" class="boton-chico btn-ico-lbl{{ ' destacado' if cuenta_regresiva else '' }}" title="Cuenta regresiva 4-3-2-1"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="13" r="8"/><path d="M12 9v4l2.5 2M9.5 2h5"/></svg>Cuenta 4</button>
    </div>
  </div>
</div>

<!-- 4. Cajón de mezcla y ajustes: lateral en pantallas anchas, hoja inferior
        en la tablet. Adentro, los tres paneles plegables de siempre (mismos
        ids y la misma preferencia de plegado en prefs.json). -->
<div id="cajon-fondo" class="cajon-fondo"></div>
<aside id="cajon-ajustes" class="cajon" aria-label="Mezcla y ajustes" aria-hidden="true">
  <div class="cajon-cabecera">
    <span class="cajon-titulo">Mezcla y ajustes</span>
    <button id="cerrar-ajustes" type="button" class="boton-chico boton-icono" title="Cerrar (Esc)" aria-label="Cerrar"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 6l12 12M18 6L6 18"/></svg></button>
  </div>
  <div class="cajon-cuerpo">

<div class="panel panel-plegable{{ ' colapsado' if mezcla_colapsada else '' }}" id="panel-mezcla">
  <div class="panel-plegable-cabecera" id="toggle-panel-mezcla">
    <span class="panel-plegable-titulo">Mezcla</span>
    <span class="panel-plegable-resumen" id="resumen-mezcla">todas las pistas suenan</span>
    <span class="panel-plegable-flecha"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 9l6 6 6-6"/></svg></span>
  </div>
  <div class="panel-plegable-cuerpo">
    <div id="canal-lista" class="consola">
      {% for p in pistas %}
      <div class="canal" data-id="{{ p.id }}" style="--canal-color: {{ p.color }}; --pista-color: {{ p.color }};">
        <div class="canal-cap"></div>
        <span class="canal-icono" aria-hidden="true"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round"></svg></span>
        <div class="canal-nombre">{{ p.label }}</div>
        <div class="fader-wrap">
          <input class="vol fader" type="range" min="0" max="100" value="100">
        </div>
        <div class="canal-valor">100%</div>
        <div class="canal-botones">
          {% if p.id == "guitar" %}
          <button class="guia" title="Guía: la pista queda sonando bajita" aria-label="Guía (volumen bajo)">G</button>
          {% endif %}
          <button class="mute" title="Silenciar esta pista">mute</button>
        </div>
      </div>
      {% endfor %}

      <!-- Master = ganancia general DE ESTE DISPOSITIVO (un GainNode por el
           que pasan todas las pistas y la claqueta). Antes movía el volumen
           de Windows vía pycaw: desde la tablet eso cambiaba la PC de casa y
           no lo que sonaba en el ensayo. -->
      <div class="canal canal-master" style="--canal-color: #a9b4c0; --pista-color: var(--fg-dim);">
        <div class="canal-cap"></div>
        <span class="canal-icono" aria-hidden="true"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round" stroke-linejoin="round"><path d="M4 9h4l5-4v14l-5-4H4z"/><path d="M16 9a4 4 0 0 1 0 6M18.5 6.5a7.5 7.5 0 0 1 0 11"/></svg></span>
        <div class="canal-nombre">Master</div>
        <div class="fader-wrap">
          <input id="vol-master" class="fader" type="range" min="0" max="100" value="{{ (master_inicial * 100)|round|int }}">
        </div>
        <div id="vol-master-valor" class="canal-valor">{{ (master_inicial * 100)|round|int }}%</div>
        <div class="canal-botones" style="visibility:hidden;"><button class="mute">mute</button></div>
      </div>
    </div>
  </div>
</div>

<div class="panel panel-plegable{{ ' colapsado' if controles_colapsados else '' }}" id="panel-controles">
  <div class="panel-plegable-cabecera" id="toggle-panel-controles">
    <span class="panel-plegable-titulo">Ajustes del tema</span>
    <span class="panel-plegable-resumen">solo de esta canción: acordes, sincronía, tempo y cejilla</span>
    <span class="panel-plegable-flecha"><svg class="ico" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 9l6 6 6-6"/></svg></span>
  </div>
  <div class="panel-plegable-cuerpo panel-controles-cuerpo">
    <div class="grupo">
      <div class="grupo-titulo">Acordes</div>
      <div class="grupo-cuerpo">
        <button id="abrir-editor" class="boton-chico destacado">Editar acordes</button>
        <div class="grupo-fila">
          <button id="editar-acordes" class="boton-chico" title="Abrir acordes.txt con el Bloc de notas">Abrir .txt</button>
          <button id="recargar-acordes" class="boton-chico" title="Releer acordes.txt sin recargar la página">Recargar</button>
        </div>
        <button id="importar-midi" class="boton-chico" title="Importar acordes desde un MIDI (ej. el que exporta Chordify)">Importar MIDI…</button>
        <input id="archivo-midi" type="file" accept=".mid,.midi" style="display:none">
        <!-- v103: cuánto coincide el detector de Mesa con el MIDI importado -->
        <button id="comparar-detector" class="boton-chico" title="Vuelve a correr el detector de Mesa y mide cuánto coincide con los acordes del MIDI importado (no cambia los acordes)">Comparar con detector</button>
        <span id="coincidencia-midi" class="grupo-valor" style="font-size:13px; display:none;"></span>
        <!-- Antes vivía en la barra de transporte: es una acción de escritorio
             (mezclar un mp3 para subirlo a Chordify), no algo que se toque
             con la guitarra encima. -->
        <button id="exportar" class="boton-chico" title="Mezcla las pistas que no están en mute en un solo mp3 (para subir a Chordify, por ejemplo)">Exportar mp3</button>
        <!-- v114: hoja de acordes por compás para imprimir / guardar como PDF -->
        <button id="hoja-imprimir" class="boton-chico" title="Abre la hoja de acordes por compás, lista para imprimir o guardar como PDF (usa lo último guardado)">Hoja para imprimir</button>
        <button id="regenerar-acordes" class="boton-chico peligro" title="Volver a detectar los acordes desde cero (se pierden las correcciones)">Regenerar acordes</button>
      </div>
    </div>

    <div class="grupo">
      <div class="grupo-titulo">Sincronía</div>
      <div class="grupo-cuerpo">
        <span id="offset-actual" class="grupo-valor">0.00s</span>
        <div class="grupo-fila">
          <button id="offset-menos-fino" class="boton-chico" title="Atrasar 0.05s">&minus;0.05s</button>
          <button id="offset-mas-fino" class="boton-chico" title="Adelantar 0.05s">+0.05s</button>
        </div>
        <div class="grupo-fila">
          <button id="offset-menos-beat" class="boton-chico" title="Atrasar toda la grilla 1 tiempo">&laquo; 1 tiempo</button>
          <button id="offset-mas-beat" class="boton-chico" title="Adelantar toda la grilla 1 tiempo">1 tiempo &raquo;</button>
        </div>
      </div>
    </div>

    <div class="grupo">
      <div class="grupo-titulo">Tempo</div>
      <div class="grupo-cuerpo">
        <span id="bpm-actual" class="grupo-valor">BPM: &mdash;</span>
        <div class="grupo-fila">
          <button id="tempo-mitad" class="boton-chico" title="El pulso va al doble de rápido que la música real">&divide; 2</button>
          <button id="tempo-doble" class="boton-chico" title="El pulso va a la mitad de rápido que la música real">&times; 2</button>
        </div>
        <div class="grupo-fila">
          <input id="bpm-manual" type="number" step="0.1" min="1" placeholder="exacto" class="campo-chico">
          <button id="bpm-ajustar" class="boton-chico" title="Recalcula toda la grilla al BPM exacto que pongas">Ajustar</button>
        </div>
      </div>
    </div>

    <div class="grupo">
      <div class="grupo-titulo">Cejilla</div>
      <div class="grupo-cuerpo">
        <span id="capo-actual" class="grupo-valor destacado-valor">sin cejilla</span>
        <div class="grupo-fila">
          <button id="capo-menos" class="boton-chico" title="Bajar un traste">&minus;</button>
          <button id="capo-mas" class="boton-chico" title="Subir un traste">+</button>
        </div>
        <button id="capo-sugerir" class="boton-chico" title="Buscar el traste que deja los acordes más fáciles">Sugerir traste</button>
      </div>
    </div>

  </div>
</div>

""" + PANEL_GENERALES_HTML + """

  </div>
</aside>

<script>
// ------------------------------ UI del rediseño ------------------------------
// Solo presentación: abre/cierra el cajón, mide la barra de transporte fija y
// traduce el glifo que el JS de siempre le escribe al play (▶ / ❚❚) a una clase
// para el ícono. No toca estado de audio, mezcla ni preferencias.
(function(){
  const raiz = document.documentElement;
  const cajon = document.getElementById("cajon-ajustes");
  const fondo = document.getElementById("cajon-fondo");
  const btnAbrir = document.getElementById("abrir-ajustes");
  const btnCerrar = document.getElementById("cerrar-ajustes");
  const barra = document.getElementById("panel-transporte");
  const play = document.getElementById("play");

  function abrirCajon(abrir){
    document.body.classList.toggle("cajon-abierto", abrir);
    cajon.setAttribute("aria-hidden", abrir ? "false" : "true");
    btnAbrir.setAttribute("aria-expanded", abrir ? "true" : "false");
    btnAbrir.classList.toggle("destacado", abrir);
  }
  btnAbrir.addEventListener("click", () => abrirCajon(!document.body.classList.contains("cajon-abierto")));
  btnCerrar.addEventListener("click", () => abrirCajon(false));
  // mientras el cajón está abierto, lo principal queda deshabilitado de verdad
  // (no solo gris): inert saca foco y clics de cabecera, cartel y transporte
  const principales = [".cabecera-mesa", ".setlist-nav", ".acordes-display", "#panel-transporte", "#panel-editor", "#acordes-advertencia", "#columna-pistas"]
    .map(s => document.querySelector(s)).filter(Boolean);
  function inertes(si){ principales.forEach(el => { if(si) el.setAttribute("inert", ""); else el.removeAttribute("inert"); }); }
  new MutationObserver(() => inertes(document.body.classList.contains("cajon-abierto")))
    .observe(document.body, { attributes: true, attributeFilter: ["class"] });
  // Espacio (play) y V (tira) son atajos de lo principal: con el cajón abierto
  // no disparan. Se atajan en captura, antes que los handlers de siempre, y
  // sin preventDefault, así Espacio sigue activando el botón con foco del cajón.
  window.addEventListener("keydown", (e) => {
    if(!document.body.classList.contains("cajon-abierto")) return;
    if(e.code === "Space" || e.key === "v" || e.key === "V") e.stopImmediatePropagation();
  }, true);
  fondo.addEventListener("click", () => abrirCajon(false));
  document.addEventListener("keydown", (e) => {
    if(e.key === "Escape" && document.body.classList.contains("cajon-abierto")) abrirCajon(false);
  });
  // v102: accesos directos. Cada uno abre el cajón mostrando SOLO su grupo
  // (body[data-seccion] lo resuelve por CSS, sin tocar las preferencias de
  // plegado). El botón "Ajustes" de siempre sigue abriendo todo.
  const tituloCajon = cajon.querySelector(".cajon-titulo");
  const TITULOS = { mezcla: "Mezcla", tema: "Ajustes del tema", generales: "Ajustes generales", gafas: "Gafas HUD" };
  const accesos = Array.from(document.querySelectorAll(".accesos-ajustes [data-seccion]"));
  function fijarSeccion(sec){
    if(sec) document.body.dataset.seccion = sec; else delete document.body.dataset.seccion;
    if(tituloCajon) tituloCajon.textContent = TITULOS[sec] || "Mezcla y ajustes";
    accesos.forEach(b => b.classList.toggle("destacado", b.dataset.seccion === sec));
    const cuerpo = cajon.querySelector(".cajon-cuerpo");
    if(cuerpo) cuerpo.scrollTop = 0;
  }
  accesos.forEach(b => b.addEventListener("click", () => {
    const abierto = document.body.classList.contains("cajon-abierto");
    if(abierto && document.body.dataset.seccion === b.dataset.seccion){ abrirCajon(false); return; }
    fijarSeccion(b.dataset.seccion);
    if(!abierto) abrirCajon(true);
  }));
  btnAbrir.addEventListener("click", () => { if(document.body.classList.contains("cajon-abierto")) fijarSeccion(null); });
  // al cerrar se limpia la sección (después de la animación de salida)
  new MutationObserver(() => {
    if(!document.body.classList.contains("cajon-abierto")){
      accesos.forEach(b => b.classList.remove("destacado"));
      setTimeout(() => { if(!document.body.classList.contains("cajon-abierto")) fijarSeccion(null); }, 300);
    }
  }).observe(document.body, { attributes: true, attributeFilter: ["class"] });
  // el editor se abre debajo del cartel: el cajón se corre para dejarlo ver
  const btnEditor = document.getElementById("abrir-editor");
  if(btnEditor) btnEditor.addEventListener("click", () => abrirCajon(false));

  // alto real de la barra fija -> la página deja ese lugar abajo, y el cajón
  // y los avisos se apoyan encima de ella
  function medirBarra(){
    raiz.style.setProperty("--alto-transporte", barra.offsetHeight + "px");
  }
  medirBarra();
  if(window.ResizeObserver) new ResizeObserver(medirBarra).observe(barra);
  window.addEventListener("resize", medirBarra);

  // muestra de color de cada banda: sigue al cuadradito seleccionado
  const bandas = document.getElementById("colores-bandas");
  if(bandas){
    const pintarMuestras = () => bandas.querySelectorAll(".colores-fila").forEach(f => {
      const sel = f.querySelector(".swatch-color.seleccionado");
      if(sel) f.style.setProperty("--sel", sel.style.getPropertyValue("--sw"));
    });
    new MutationObserver(pintarMuestras).observe(bandas, { attributes: true, attributeFilter: ["class"], subtree: true });
  }

  // ícono del play según el glifo que le deja el JS
  function pintarPlay(){
    play.classList.toggle("en-marcha", (play.textContent || "").indexOf("\u275A") !== -1);
  }
  pintarPlay();
  new MutationObserver(pintarPlay).observe(play, { childList: true, characterData: true, subtree: true });
})();
</script>

<script>
const pistas = {{ pistas | tojson }};
const AUTOR_CANCION = {{ autor | tojson }};   // v107: subtítulo de la cabecera
{% if setlist and setlist.siguiente %}
const urlSiguienteSetlist = "{{ url_for('mesa', song=setlist.siguiente) }}?setlist={{ setlist.id }}&autoplay=1";
{% else %}
const urlSiguienteSetlist = null;
{% endif %}

// ------------------------------ descarga offline ------------------------------
// Guarda los 6 stems a velocidad normal (100%), y además la página de esta
// mesa, los acordes, la mezcla guardada y la portada -- sin esto último, aunque
// el audio estuviera descargado, abrir la app sin conexión no llegaba ni a
// mostrar nada (la página en sí no estaba disponible). Ver mesaOffline en
// BASE_STYLE: el service worker sirve todo esto desde el caché apenas falla
// la red, así que no hace falta ningún cambio en cargarUnaPista ni en cargarAcordes.
(() => {
  // Las arma el servidor (urls_offline_cancion): la mesa, su variante por
  // cada setlist donde está (para que Anterior/Siguiente anden sin wifi),
  // esas páginas de setlist, acordes, mezcla, marcas de rasgueo, portada y
  // los stems. Un tema bajado con una versión anterior de Mesa aparece como
  // "descargar" hasta que se vuelva a tocar el chip: el audio ya está en el
  // caché, así que solo baja lo nuevo (unos KB) y tarda un instante.
  const urlsOffline = {{ urls_offline | tojson }};
  // al borrar ESTA canción no se tocan la portada ni las páginas de setlist:
  // las comparten las demás canciones descargadas
  const urlsPropias = urlsOffline.filter(u => u !== "/" && !u.startsWith("/setlist/"));
  const chip = document.getElementById("chip-offline");
  const elTexto = chip.querySelector(".texto");

  function pintar(clase, texto, titulo){
    chip.classList.remove("descargada", "trabajando", "confirmando");
    if(clase) chip.classList.add(clase);
    elTexto.textContent = texto;
    if(titulo) chip.title = titulo;
  }

  if(!window.mesaOffline || !window.mesaOffline.soportado){
    // Caso habitual y confuso: entrar por http://<ip-local>:5000. Los
    // navegadores desactivan Cache Storage fuera de un contexto seguro, así
    // que no es que "falle" la descarga: esa dirección no puede soportarla.
    // Decirlo con todas las letras evita buscar el problema donde no está.
    const porHttp = location.protocol === "http:" && !["localhost","127.0.0.1"].includes(location.hostname);
    pintar(null, porHttp ? "offline solo por https" : "sin offline",
           porHttp
             ? "Para guardar la canción hace falta entrar por https (Tailscale). Por IP local el navegador no permite descargas offline."
             : "Este navegador no puede guardar la canción para tocar sin wifi");
    chip.disabled = true;
    return;
  }

  // La calidad con la que se bajó cada tema se anota acá: si después la
  // cambiás, lo descargado sigue siendo el de antes y el chip tiene que
  // decirlo en vez de mostrar un tranquilizador "ya está".
  const CLAVE_CAL = "mesaCalidad:{{ song }}";
  const calidadActual = "{{ calidad_actual }}";
  function calidadDescargada(){
    try{ return localStorage.getItem(CLAVE_CAL); }catch(e){ return null; }
  }
  function anotarCalidad(){
    try{ localStorage.setItem(CLAVE_CAL, calidadActual); }catch(e){}
  }

  // "descargada" en este dispositivo: la tablet y la PC llevan cuentas
  // separadas, porque el caché vive en cada navegador
  let descargada = false, confirmandoBorrado = false, ocupado = false, desactualizada = false;
  let temporizadorConfirmar = null;

  function cancelarConfirmacion(){
    clearTimeout(temporizadorConfirmar);
    confirmandoBorrado = false;
  }

  async function refrescarEstado(){
    descargada = await window.mesaOffline.disponible(urlsOffline);
    cancelarConfirmacion();
    if(descargada){
      const bytes = await window.mesaOffline.tamanoBytes(urlsOffline);
      const previa = calidadDescargada();
      if(previa && previa !== calidadActual){
        desactualizada = true;
        pintar("trabajando", "actualizar descarga",
               "Este tema está guardado en otra calidad. Tocá para volver a bajarlo con la actual");
      } else {
        desactualizada = false;
        pintar("descargada", `sin wifi · ${window.mesaOffline.fmtMB(bytes)}`,
               "Ya podés tocar este tema sin wifi. Tocá acá para borrar la descarga");
      }
    } else {
      desactualizada = false;
      pintar(null, "descargar", "Guarda las pistas y esta pantalla para poder tocar el tema sin wifi");
    }
    chip.disabled = false;
  }

  chip.addEventListener("click", async () => {
    if(ocupado) return;

    // ya está bajada: primer toque pregunta, segundo borra. Mismo patrón de
    // confirmación que el botón de borrar canción en la portada, así que no
    // hay forma de perder una descarga de un toque accidental en el atril.
    if(descargada && desactualizada && !confirmandoBorrado){
      ocupado = true; chip.disabled = true;
      try{
        pintar("trabajando", "actualizando…");
        await window.mesaOffline.borrar(urlsPropias);
        await window.mesaOffline.descargar(urlsOffline, (hecho, total) => {
          elTexto.textContent = `${hecho}/${total}…`;
        });
        anotarCalidad();
      }catch(err){
        pintar(null, "falló", "No se pudo actualizar: " + err.message);
      }finally{
        ocupado = false;
        await refrescarEstado();
      }
      return;
    }

    if(descargada && !confirmandoBorrado){
      confirmandoBorrado = true;
      pintar("confirmando", "¿borrar?", "Tocá otra vez para borrar la descarga");
      temporizadorConfirmar = setTimeout(refrescarEstado, 4000);
      return;
    }

    ocupado = true;
    chip.disabled = true;
    try{
      if(confirmandoBorrado){
        cancelarConfirmacion();
        pintar("trabajando", "borrando…");
        await window.mesaOffline.borrar(urlsPropias);
      } else {
        pintar("trabajando", "descargando…");
        window.mesaHayDescargaEnCurso = true;
        await window.mesaOffline.descargar(urlsOffline, (hecho, total) => {
          elTexto.textContent = `${hecho}/${total}…`;
        });
        anotarCalidad();
      }
    }catch(err){
      pintar(null, "falló", "No se pudo completar: " + err.message);
      mesaAviso("No se pudo guardar para tocar sin wifi: " + err.message, { error: true });
    }finally{
      ocupado = false;
      window.mesaHayDescargaEnCurso = false;
      await refrescarEstado();
    }
  });

  refrescarEstado();
})();
const ctx = new (window.AudioContext || window.webkitAudioContext)();
// Ganancia general de ESTE dispositivo: todas las pistas (y la claqueta)
// pasan por acá antes de salir. Es lo que mueve el fader Master.
const masterGain = ctx.createGain();
masterGain.gain.value = {{ master_inicial }};
masterGain.connect(ctx.destination);
const canales = {}; // id -> {buffer, gain, source, muted, vol}
let duracion = 0, sonando = false, offsetInicio = 0, tiempoInicioCtx = 0;
let acordes = [], beatTimes = [], beatsPorCompas = 4, offsetActual = 0, bpmActual = null, capoActual = 0;
let marcasRasgueoBase = [];   // tiempos (segundos, SIN offset) con cambio de rasgueo marcado
let marcasRasgueo = [];       // los mismos, ya con el offset de sincronía sumado, ordenados
let ajustesMezclaGuardados = {}; // id -> {vol, muted, guia, vol_previo}, cargado desde el servidor

// v103: duración de UN tiempo, en segundos (null si no hay grilla). Es la
// mediana de toda la grilla y no "beatTimes[1] - beatTimes[0]": en una grilla
// importada de MIDI ese primer intervalo es el relleno de entrada y puede
// durar cualquier cosa (0,3 s en un tema de 120 BPM), y de ahí salían mal la
// claqueta del loop, los colores por duración y el "± 1 tiempo". En una
// grilla de tempo constante la mediana es ese mismo intervalo de siempre.
let pasoBeatDe = null, pasoBeatValor = null;
function pasoBeatSeg(){
  if(beatTimes.length < 2) return null;
  if(pasoBeatDe !== beatTimes){
    const difs = [];
    for(let i = 1; i < beatTimes.length; i++) difs.push(beatTimes[i] - beatTimes[i - 1]);
    difs.sort((a, b) => a - b);
    pasoBeatValor = difs[difs.length >> 1];
    pasoBeatDe = beatTimes;
  }
  return pasoBeatValor;
}

// --- velocidad de estudio -------------------------------------------------
// El audio que sirve el servidor ya viene estirado con ffmpeg (mismo tono),
// así que el buffer dura más de lo que dura la canción. TODO lo demás de la
// app (grilla de acordes, seek, loop) sigue hablando en tiempo ORIGINAL: la
// conversión pasa solo por acá. tiempo_audio = tiempo_original / factorVel.
let factorVel = 1.0;

// --- loop A-B + claqueta --------------------------------------------------
let loopA = null, loopB = null, claqueta = true;
let clicksProgramados = [];

// --- modo tocar -----------------------------------------------------------
let escalaVisual = 1;   // multiplica también el tamaño de los diagramas SVG

// --- cejilla: solo visualización. Con cejilla en el traste N, la forma que
// agarrás suena N semitonos más arriba, así que la forma = acorde real - N.
const NOTAS = ["C","C#","D","D#","E","F","F#","G","G#","A","A#","B"];

// --- diagramas de acordes ---
// Cada entrada: trastes por cuerda de la 6ª (Mi grave) a la 1ª (Mi agudo).
// -1 = cuerda muda, 0 = al aire. "barre" indica el traste de la cejilla con el dedo.
const DIGITACIONES = {
  "C":   {f:[-1,3,2,0,1,0]},               "Cm":  {f:[-1,3,5,5,4,3], b:3},
  "C#":  {f:[-1,4,6,6,6,4], b:4},          "C#m": {f:[-1,4,6,6,5,4], b:4},
  "D":   {f:[-1,-1,0,2,3,2]},              "Dm":  {f:[-1,-1,0,2,3,1]},
  "D#":  {f:[-1,6,8,8,8,6], b:6},          "D#m": {f:[-1,6,8,8,7,6], b:6},
  "E":   {f:[0,2,2,1,0,0]},                "Em":  {f:[0,2,2,0,0,0]},
  "F":   {f:[1,3,3,2,1,1], b:1},           "Fm":  {f:[1,3,3,1,1,1], b:1},
  "F#":  {f:[2,4,4,3,2,2], b:2},           "F#m": {f:[2,4,4,2,2,2], b:2},
  "G":   {f:[3,2,0,0,0,3]},                "Gm":  {f:[3,5,5,3,3,3], b:3},
  "G#":  {f:[4,6,6,5,4,4], b:4},           "G#m": {f:[4,6,6,4,4,4], b:4},
  "A":   {f:[-1,0,2,2,2,0]},               "Am":  {f:[-1,0,2,2,1,0]},
  "A#":  {f:[-1,1,3,3,3,1], b:1},          "A#m": {f:[-1,1,3,3,2,1], b:1},
  "B":   {f:[-1,2,4,4,4,2], b:2},          "Bm":  {f:[-1,2,4,4,3,2], b:2},
  "C7":  {f:[-1,3,2,3,1,0]},               "C#7": {f:[-1,4,6,4,6,4], b:4},
  "D7":  {f:[-1,-1,0,2,1,2]},              "D#7": {f:[-1,6,8,6,8,6], b:6},
  "E7":  {f:[0,2,0,1,0,0]},                "F7":  {f:[1,3,1,2,1,1], b:1},
  "F#7": {f:[2,4,2,3,2,2], b:2},           "G7":  {f:[3,2,0,0,0,1]},
  "G#7": {f:[4,6,4,5,4,4], b:4},           "A7":  {f:[-1,0,2,0,2,0]},
  "A#7": {f:[-1,1,3,1,3,1], b:1},          "B7":  {f:[-1,2,1,2,0,2]},
  // maj7: sufijo aceptado al editar/importar aunque el detector automático no
  // lo proponga solo (ver SUFIJOS_EXTRA_EDICION en el backend). Las 12
  // verificadas nota por nota igual que las otras 36 (root + 3ra mayor + 5ta +
  // 7ma mayor, sin notas ajenas). En las de cejilla, es la misma forma que el
  // acorde mayor con la 4ta cuerda un traste más abajo.
  "Cmaj7":  {f:[-1,3,2,0,0,0]},            "C#maj7": {f:[-1,4,6,5,6,4], b:4},
  "Dmaj7":  {f:[-1,-1,0,2,2,2]},           "D#maj7": {f:[-1,6,8,7,8,6], b:6},
  "Emaj7":  {f:[-1,-1,1,1,0,0]},           "Fmaj7":  {f:[-1,-1,3,2,1,0]},
  "F#maj7": {f:[2,4,3,3,2,2], b:2},        "Gmaj7":  {f:[2,2,0,0,0,2]},
  "G#maj7": {f:[4,6,5,5,4,4], b:4},        "Amaj7":  {f:[-1,0,2,1,2,0]},
  "A#maj7": {f:[-1,1,3,2,3,1], b:1},       "Bmaj7":  {f:[-1,2,4,3,4,2], b:2},
  // v108 sus4 (root + 4ta + 5ta, sin 3ra). Al aire: C, D, E, G, A. Las de
  // cejilla: forma de E (F, F#, G#) o de A (C#, D#, A#, B) con la 3ra subida
  // un traste. Verificadas nota por nota.
  "Csus4":  {f:[-1,3,3,0,1,1]},            "C#sus4": {f:[-1,4,6,6,7,4], b:4},
  "Dsus4":  {f:[-1,-1,0,2,3,3]},           "D#sus4": {f:[-1,6,8,8,9,6], b:6},
  "Esus4":  {f:[0,2,2,2,0,0]},             "Fsus4":  {f:[1,3,3,3,1,1], b:1},
  "F#sus4": {f:[2,4,4,4,2,2], b:2},        "Gsus4":  {f:[3,3,0,0,1,3]},
  "G#sus4": {f:[4,6,6,6,4,4], b:4},        "Asus4":  {f:[-1,0,2,2,3,0]},
  "A#sus4": {f:[-1,1,3,3,4,1], b:1},       "Bsus4":  {f:[-1,2,4,4,5,2], b:2},
};

function svgAcorde(nombre, escala){
  const d = DIGITACIONES[nombre];
  if(!d) return "";
  const s = escala || 1;
  const W = 78 * s, H = 96 * s;
  const izq = 13 * s, der = W - 13 * s, arriba = 22 * s;
  const alto = H - arriba - 8 * s;
  const pasoC = (der - izq) / 5;          // 6 cuerdas
  const NTRASTES = 4;
  const pasoT = alto / NTRASTES;

  const usados = d.f.filter(x => x > 0);
  const hayAlAire = d.f.some(x => x === 0);
  const minT = usados.length ? Math.min(...usados) : 1;
  // Si alguna cuerda va al aire, el diagrama tiene que arrancar en el traste 1
  // (si no, el 0 no tendría dónde mostrarse). Solo se desplaza la ventana en
  // acordes cerrados que empiezan más arriba del mástil.
  const base = (!hayAlAire && minT > 1) ? minT : 1;

  let svg = `<svg viewBox="0 0 ${W} ${H}" width="${W}" height="${H}" xmlns="http://www.w3.org/2000/svg">`;

  // cejuela gruesa si el diagrama arranca en el traste 1
  if(base === 1){
    svg += `<rect x="${izq}" y="${arriba - 3*s}" width="${der-izq}" height="${3.5*s}" fill="var(--fg-dim)"/>`;
  } else {
    svg += `<text x="${izq - 5*s}" y="${arriba + pasoT*0.7}" font-size="${11*s}" fill="var(--fg-dim)" text-anchor="end" font-family="monospace">${base}</text>`;
  }

  // trastes y cuerdas
  for(let i = 0; i <= NTRASTES; i++){
    const y = arriba + i * pasoT;
    svg += `<line x1="${izq}" y1="${y}" x2="${der}" y2="${y}" stroke="var(--diag-linea)" stroke-width="${1*s}"/>`;
  }
  for(let i = 0; i < 6; i++){
    const x = izq + i * pasoC;
    svg += `<line x1="${x}" y1="${arriba}" x2="${x}" y2="${arriba + alto}" stroke="var(--diag-linea)" stroke-width="${1*s}"/>`;
  }

  // cejilla con el dedo
  if(d.b){
    const y = arriba + (d.b - base + 0.5) * pasoT;
    const primera = d.f.findIndex(v => v === d.b);
    const ultima = d.f.length - 1 - [...d.f].reverse().findIndex(v => v === d.b);
    svg += `<rect x="${izq + primera*pasoC - 4*s}" y="${y - 4*s}" width="${(ultima-primera)*pasoC + 8*s}" height="${8*s}" rx="${4*s}" fill="var(--brass)"/>`;
  }

  d.f.forEach((traste, i) => {
    const x = izq + i * pasoC;
    if(traste === -1){
      svg += `<text x="${x}" y="${arriba - 6*s}" font-size="${11*s}" fill="var(--diag-tenue)" text-anchor="middle" font-family="monospace">×</text>`;
    } else if(traste === 0){
      svg += `<circle cx="${x}" cy="${arriba - 9*s}" r="${3.5*s}" fill="none" stroke="var(--fg-dim)" stroke-width="${1.3*s}"/>`;
    } else if(!d.b || traste !== d.b){
      const y = arriba + (traste - base + 0.5) * pasoT;
      svg += `<circle cx="${x}" cy="${y}" r="${5*s}" fill="var(--brass)"/>`;
    }
  });

  return svg + "</svg>";
}


function transponerAcorde(acorde, semitonos){
  if(!acorde || acorde === "—" || acorde === ".") return acorde;
  let raiz = acorde.slice(0,2);
  let sufijo;
  if(NOTAS.includes(raiz)){ sufijo = acorde.slice(2); }
  else { raiz = acorde.slice(0,1); sufijo = acorde.slice(1); }
  const i = NOTAS.indexOf(raiz);
  if(i < 0) return acorde;
  return NOTAS[(i + semitonos + 120) % 12] + sufijo;
}

// lo que se muestra grande: la forma que agarrás con la cejilla puesta
function formaDeAcorde(acorde){
  return capoActual ? transponerAcorde(acorde, -capoActual) : acorde;
}

// ---- análisis armónico: tonalidad de la canción y grado de cada acorde ----
// Se calcula una vez cuando cambian los acordes (no en cada frame). La idea:
// probar las 24 tonalidades (12 mayores + 12 menores) y quedarse con la que
// deja más acordes de la canción "dentro" de su escala diatónica, ponderando
// por cuánto dura cada acorde. Es una heurística de estudio, no un análisis
// musicológico infalible (canciones que modulan o con muchos acordes prestados
// pueden dar algún grado raro, que igual es técnicamente correcto).
const GRADOS_MAYOR = ["I","II","III","IV","V","VI","VII"];   // semitonos 0,2,4,5,7,9,11
const OFFSETS_MAYOR = [0,2,4,5,7,9,11];
// calidad esperada de cada grado en una tonalidad MAYOR (mayús=mayor, minús=menor, °=dism)
const CALIDAD_MAYOR = ["maj","min","min","maj","maj","min","dim"];
// en tonalidad MENOR natural (relativa): i ii° III iv v VI VII
const CALIDAD_MENOR = ["min","dim","maj","min","min","maj","maj"];

function raizYsufijo(acorde){
  let raiz = acorde.slice(0,2);
  let sufijo;
  if(NOTAS.includes(raiz)){ sufijo = acorde.slice(2); }
  else { raiz = acorde.slice(0,1); sufijo = acorde.slice(1); }
  const i = NOTAS.indexOf(raiz);
  return i < 0 ? null : { pc: i, sufijo };
}
function calidadDe(sufijo){
  if(sufijo === "m") return "min";
  return "maj"; // "", "7", "maj7", "sus4" -> mayor a los fines del grado
}

let tonalidad = null; // {tonica: pc, modo: "maj"|"min"}

// Elige la tonalidad que mejor explica los acordes de la canción.
function detectarTonalidad(){
  // contamos cuánto tiempo suena cada nota raíz (ponderado por duración)
  const peso = {};
  for(const seg of acordes){
    const rs = raizYsufijo(seg.acorde);
    if(!rs) continue;
    const dur = Math.max(0.1, (seg.fin || 0) - (seg.inicio || 0));
    peso[seg.acorde] = (peso[seg.acorde] || 0) + dur;
  }
  const entradas = Object.entries(peso).map(([ac, w]) => {
    const rs = raizYsufijo(ac);
    return rs ? { pc: rs.pc, cal: calidadDe(rs.sufijo), w } : null;
  }).filter(Boolean);
  if(!entradas.length){ tonalidad = null; return; }

  let mejor = null, mejorPuntaje = -1;
  for(let tonica = 0; tonica < 12; tonica++){
    for(const modo of ["maj","min"]){
      const calidades = modo === "maj" ? CALIDAD_MAYOR : CALIDAD_MENOR;
      let puntaje = 0;
      for(const e of entradas){
        const rel = (e.pc - tonica + 12) % 12;
        const grado = OFFSETS_MAYOR.indexOf(modo === "maj" ? rel : (rel)); // buscamos si cae en la escala
        // escala relativa: para menor natural usamos los mismos offsets rotados
        const offs = modo === "maj" ? OFFSETS_MAYOR : [0,2,3,5,7,8,10];
        const gi = offs.indexOf(rel);
        if(gi >= 0){
          puntaje += e.w;                                   // cae en la escala: suma
          if(calidades[gi] === e.cal) puntaje += e.w * 0.5; // y además la calidad coincide: bonus
        } else {
          puntaje -= e.w * 0.3;                             // acorde fuera de tono: penaliza suave
        }
      }
      // pequeño favor a que la tónica sea un acorde que realmente suena
      if(entradas.some(e => e.pc === tonica)) puntaje += 0.01;
      if(puntaje > mejorPuntaje){ mejorPuntaje = puntaje; mejor = { tonica, modo }; }
    }
  }
  tonalidad = mejor;
}

// Traduce un acorde real (no la forma con cejilla) a su grado en la tonalidad.
// Devuelve "" si no hay tonalidad o el acorde no es analizable.
function gradoDe(acordeReal){
  if(!tonalidad || !acordeReal || acordeReal === "—" || acordeReal === ".") return "";
  const rs = raizYsufijo(acordeReal);
  if(!rs) return "";
  const offs = tonalidad.modo === "maj" ? OFFSETS_MAYOR : [0,2,3,5,7,8,10];
  const rel = (rs.pc - tonalidad.tonica + 12) % 12;
  const gi = offs.indexOf(rel);
  const cal = calidadDe(rs.sufijo);
  let base;
  if(gi >= 0){
    base = GRADOS_MAYOR[gi];
  } else {
    // acorde fuera de la escala: lo nombramos con alteración sobre el grado más cercano por debajo
    let k = rel; while(offs.indexOf(k) < 0 && k > 0) k--;
    const giAbajo = offs.indexOf(k);
    base = (giAbajo >= 0 ? GRADOS_MAYOR[giAbajo] : "I");
    base = "♯" + base; // aproximación: sostenido respecto al grado inferior
  }
  // mayúscula si es mayor, minúscula si es menor
  let roman = (cal === "min") ? base.toLowerCase() : base;
  if(rs.sufijo === "7") roman += "7";
  else if(rs.sufijo === "maj7") roman += "maj7";
  else if(rs.sufijo === "sus4") roman += "sus4";
  return roman;
}

// texto de la progresión general: tónica + acordes únicos como grados, en orden
function textoProgresion(){
  if(!tonalidad) return "";
  const nombreTonica = NOTAS[tonalidad.tonica];
  const modoTxt = tonalidad.modo === "maj" ? "mayor" : "menor";
  const vistos = [];
  for(const seg of acordes){
    const g = gradoDe(seg.acorde);
    if(g && !vistos.includes(g)) vistos.push(g);
    if(vistos.length >= 8) break; // no saturar
  }
  if(!vistos.length) return `${nombreTonica} ${modoTxt}`;
  return `${nombreTonica} ${modoTxt} · ${vistos.join(" – ")}`;
}

// --- caché de lo último dibujado en el cartel -------------------------------
// Van ACA ARRIBA a propósito. Varias preferencias de vista (diagramas, grados,
// cejilla, la tira) las ponen en null al aplicarse para forzar un redibujo, y
// algunas de esas se aplican apenas carga la página. Si la declaración quedara
// más abajo, junto al tick, esas llamadas caerían en la zona muerta temporal
// de `let`: el script muere con ReferenceError en plena carga y NINGÚN
// addEventListener posterior llega a registrarse -- la página abre pero no
// responde a un solo click. Declararlas antes de su primer uso lo evita.
let ultimoTiempoTexto = "", ultimoAcorde = null, ultimoSiguiente = null, ultimoBeat = -2, ultimoColorBarra = null, ultimoCompasTexto = "", ultimoPasoSeek = -1;
let ultimoAcordeHUD = null, ultimoSiguienteHUD = null, ultimoBeatHUD = -2;   // gafas HUD: ver /hud/acorde en tick()
// v99: ultimoAcordeHUD guarda la "firma" del último estado enviado (ver
// hudPublicar). Ponerlo en null sigue forzando un reenvío, como siempre.
let ultimoEnvioHUD = 0;
const HUD_REENVIO_MS = 5000;   // el firmware pasa a "Sin señal" a los 15 s sin datos
// Título para las gafas: las fuentes del OLED son ASCII de 7 bits, así que se
// pasan los acentos a su letra base (á→a, ñ→n) y se descarta el resto.
function hudTextoPlano(t, max){
  return String(t === null || t === undefined ? "" : t)
    .normalize("NFD").replace(/[\\u0300-\\u036f]/g, "")
    .replace(/[^ -~]/g, "").replace(/ +/g, " ").trim().slice(0, max);
}
const HUD_TITULO = hudTextoPlano({{ titulo | tojson }}, 40);
// Único punto de salida hacia las gafas. Manda cuando el estado cambió, y
// además lo repite cada HUD_REENVIO_MS: con las gafas por Bluetooth desde este
// dispositivo no hay keepalive del backend, y un título quieto (o una pausa
// larga) terminaba en "Sin señal". Repetir el mismo estado no reinicia el pie.
function hudPublicar(estadoHUD){
  if(!hudActivo) return;
  const firma = JSON.stringify(estadoHUD);
  const ahora = performance.now();
  if(firma === ultimoAcordeHUD && ahora - ultimoEnvioHUD < HUD_REENVIO_MS) return;
  ultimoAcordeHUD = firma;
  ultimoEnvioHUD = ahora;
  // Si este dispositivo tiene las gafas conectadas manda él, y el fetch al
  // backend sobra (con la PC apagada iba a fallar igual).
  if(!mandarAlHUDLocal(estadoHUD)){
    fetch("/hud/acorde", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(estadoHUD),
    }).catch(() => {});
  }
}
let ultimoEstadoRasgueo = null;

// ------------------------------ cinta de compases (v87) ----------------------
// Modo alternativo: una celda por tiempo, que se desliza bajo un cabezal fijo.
// La pista se arma UNA vez por grilla (se rearma si cambian acordes, beats,
// cejilla o marcas de rasgueo: todas se reasignan como arrays nuevos al
// recargar, así que alcanza con comparar referencias). En cada frame solo se
// mueve un transform y, al cambiar de tiempo, se pasa la clase "activo".
let vistaCinta = {{ 'true' if vista_cinta else 'false' }};
const elCinta = document.getElementById("cinta");
const elCintaPista = document.getElementById("cinta-pista");
const elCintaFijo = document.getElementById("cinta-fijo");
let cintaFijoVisible = false, cintaFijoIni = -2;
const CINTA_CELDA = 46;          // px a escala 1 (igual que .cinta-tiempo)
const CINTA_CABEZAL = 0.30;      // fracción del ancho donde está el cabezal
let cintaFirma = null, cintaCeldas = [], cintaAcordeDeBeat = [], cintaInicioAcorde = [];
let cintaUltimoBeat = -2, cintaUltimoAcordeIni = -2, cintaUltimoX = null, cintaAncho = 0;

function armarCinta(){
  elCintaPista.textContent = "";
  cintaCeldas = []; cintaAcordeDeBeat = []; cintaInicioAcorde = [];
  cintaUltimoBeat = -2; cintaUltimoAcordeIni = -2; cintaUltimoX = null;
  cintaFijoIni = -2; cintaFijoVisible = false; elCintaFijo.classList.remove("visible");
  const n = beatTimes.length;
  if(!n || !acordes.length) return;
  // acorde de cada beat (búsqueda lineal: beats y segmentos ya vienen ordenados)
  let j = 0, ini = -1, anterior = null;
  const frag = document.createDocumentFragment();
  for(let i = 0; i < n; i++){
    const t = beatTimes[i] + 1e-3;
    while(j < acordes.length - 1 && t >= acordes[j].fin) j++;
    const seg = (t >= acordes[j].inicio && t < acordes[j].fin) ? acordes[j] : null;
    const nombre = seg ? seg.acorde : "—";
    const celda = document.createElement("div");
    celda.className = "cinta-tiempo";
    if(i % beatsPorCompas === 0) celda.classList.add("inicio-compas");
    if(i === 0 || nombre !== anterior){
      ini = i;
      const et = document.createElement("div");
      et.className = "cinta-acorde";
      renderAcordeGrande(et, nombre === "—" ? "—" : formaDeAcorde(nombre));
      celda.appendChild(et);
    }
    anterior = nombre;
    cintaInicioAcorde.push(ini);
    const cuadro = document.createElement("div");
    cuadro.className = "cinta-cuadro";
    celda.appendChild(cuadro);
    frag.appendChild(celda);
    cintaCeldas.push(celda);
  }
  // marcas de cambio de rasgueo: al tiempo en el que caen
  let b = 0;
  for(const m of marcasRasgueo){
    while(b + 1 < n && beatTimes[b + 1] <= m + 1e-3) b++;
    if(beatTimes[b] <= m + 1e-3) cintaCeldas[b].classList.add("rasgueo");
  }
  elCintaPista.appendChild(frag);
}

function actualizarCinta(pos){
  if(!vistaCinta) return;
  if(!cintaFirma || cintaFirma[0] !== acordes || cintaFirma[1] !== beatTimes
     || cintaFirma[2] !== capoActual || cintaFirma[3] !== marcasRasgueo || cintaFirma[4] !== beatsPorCompas){
    cintaFirma = [acordes, beatTimes, capoActual, marcasRasgueo, beatsPorCompas];
    armarCinta();
  }
  const n = beatTimes.length;
  if(!n || !cintaCeldas.length) return;
  if(!cintaAncho) cintaAncho = elCinta.clientWidth;

  // posición continua en "tiempos": índice del beat + fracción hacia el próximo
  const i = indiceBeatEnPosicion(pos);
  let f;
  if(i < 0){
    const paso = n > 1 ? beatTimes[1] - beatTimes[0] : 0.5;
    f = (pos - beatTimes[0]) / paso;
  } else if(i + 1 < n){
    f = i + (pos - beatTimes[i]) / (beatTimes[i + 1] - beatTimes[i]);
  } else {
    f = i;
  }
  const celda = CINTA_CELDA * escalaVisual;
  const x = Math.round((cintaAncho * CINTA_CABEZAL - f * celda) * 2) / 2;
  if(x !== cintaUltimoX){
    elCintaPista.style.transform = `translateX(${x}px)`;
    cintaUltimoX = x;
  }
  if(i !== cintaUltimoBeat){
    if(cintaUltimoBeat >= 0 && cintaCeldas[cintaUltimoBeat]) cintaCeldas[cintaUltimoBeat].classList.remove("activo");
    if(i >= 0) cintaCeldas[i].classList.add("activo");
    cintaUltimoBeat = i;
    const ini = i >= 0 ? cintaInicioAcorde[i] : -1;
    if(ini !== cintaUltimoAcordeIni){
      if(cintaUltimoAcordeIni >= 0 && cintaCeldas[cintaUltimoAcordeIni]) cintaCeldas[cintaUltimoAcordeIni].classList.remove("acorde-sonando");
      if(ini >= 0) cintaCeldas[ini].classList.add("acorde-sonando");
      cintaUltimoAcordeIni = ini;
    }
  }
  // acorde largo: si su celda de inicio ya se fue por la izquierda, se clava
  // el nombre al borde para que la cinta siempre diga qué está sonando
  const iniSon = cintaUltimoAcordeIni;
  const verFijo = iniSon >= 0 && (x + iniSon * celda) < 0;
  if(verFijo && iniSon !== cintaFijoIni){
    const et = cintaCeldas[iniSon].querySelector(".cinta-acorde");
    elCintaFijo.innerHTML = et ? et.innerHTML : "";
    cintaFijoIni = iniSon;
  }
  if(verFijo !== cintaFijoVisible){
    elCintaFijo.classList.toggle("visible", verFijo);
    cintaFijoVisible = verFijo;
  }
}

function aplicarEstadoCinta(){
  document.body.classList.toggle("vista-cinta", vistaCinta);
  document.getElementById("toggle-cinta").classList.toggle("destacado", vistaCinta);
  cintaAncho = 0; cintaUltimoX = null;
  if(!vistaCinta){ elCintaPista.textContent = ""; cintaFirma = null; cintaCeldas = []; }
  if(typeof ajustarEscalaTocar === "function") ajustarEscalaTocar();
}

document.getElementById("toggle-cinta").addEventListener("click", async () => {
  vistaCinta = !vistaCinta;
  aplicarEstadoCinta();
  try{
    await fetch("/preferencia", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ clave: "vista_cinta", valor: vistaCinta }),
    });
  }catch(e){ /* sin conexión: queda aplicado igual en esta sesión */ }
});

// v89: toggle de la cuenta regresiva (preferencia global, como la cinta)
document.getElementById("toggle-cuenta").addEventListener("click", async (ev) => {
  cuentaRegresiva = !cuentaRegresiva;
  ev.currentTarget.classList.toggle("destacado", cuentaRegresiva);
  try{
    await fetch("/preferencia", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ clave: "cuenta_regresiva", valor: cuentaRegresiva }),
    });
  }catch(e){ /* sin conexión: queda aplicado igual en esta sesión */ }
});

// --- calidad del audio: por DISPOSITIVO, vía cookie ------------------------
// No usa /preferencia (que es global y compartida con la PC) ni un parámetro en
// la URL (que dejaría al service worker sin cachear el audio). La cookie la
// manda el navegador en cada pedido, incluidos los que hace el service worker,
// así que la ruta queda igual y el servidor igual sabe qué versión mandar.
{% if not es_la_pc %}
(() => {
  // El peso lo fija SOLO el bitrate: mono a 160k pesa IGUAL que estéreo a 160k.
  // Lo que cambia mono es en qué se gastan esos bits -- al haber un solo canal,
  // cada bit rinde el doble, así que mono 96k suena mejor que estéreo 96k
  // ocupando exactamente lo mismo.
  // Se muestran los MB REALES de este tema en vez de un porcentaje: así queda
  // a la vista que el botón de mono no mueve el número y el de bitrate sí,
  // que es justo lo que confunde.
  const KBPS = { estereo160:160, mono160:160, estereo96:96, mono96:96 };
  function textoPeso(cal){
    const kbps = KBPS[cal];
    if(!duracion) return `${kbps}k`;
    const mb = kbps * duracion * 6 / 8 / 1024;   // 6 pistas
    return `${mb.toFixed(0)} MB el tema completo`;
  }
  let calidad = "{{ calidad_actual }}";
  const elPeso = document.getElementById("calidad-peso");
  const botones = Array.from(document.querySelectorAll(".calidad"));

  function pintar(){
    const mono = calidad.startsWith("mono");
    const b96 = calidad.endsWith("96");
    botones.forEach(b => {
      if(b.dataset.canal) b.classList.toggle("marcado", (b.dataset.canal === "mono") === mono);
      if(b.dataset.bitrate) b.classList.toggle("marcado", (b.dataset.bitrate === "96") === b96);
    });
    elPeso.textContent = textoPeso(calidad);
  }
  pintar();
  // la duración recién se conoce cuando cargan las pistas: se repinta entonces
  // para pasar de "96k" al peso real en MB
  window.addEventListener("mesa-pistas-listas", pintar);

  botones.forEach(btn => btn.addEventListener("click", () => {
    const mono = btn.dataset.canal ? btn.dataset.canal === "mono" : calidad.startsWith("mono");
    const b96  = btn.dataset.bitrate ? btn.dataset.bitrate === "96" : calidad.endsWith("96");
    const nueva = (mono ? "mono" : "estereo") + (b96 ? "96" : "160");
    if(nueva === calidad) return;
    calidad = nueva;
    pintar();
    // un año, y en la raíz para que valga en todas las páginas de la app
    document.cookie = `mesa_calidad=${calidad}; path=/; max-age=31536000; SameSite=Lax`;
    // las pistas que ya están en memoria son de la calidad vieja: la forma más
    // simple y segura de rehacerlas es recargar, igual que al cambiar de tema
    elPeso.textContent = "aplicando…";
    setTimeout(() => location.reload(), 150);
  }));
})();
{% endif %}

function actualizarCapoUI(){
  document.getElementById("capo-actual").textContent =
    capoActual ? `traste ${capoActual}` : "sin cejilla";
  const chip = document.getElementById("chip-capo");
  chip.classList.toggle("visible", !!capoActual);
  if(capoActual) chip.textContent = `cejilla · traste ${capoActual}`;
  // fuerza el redibujo del cartel en el próximo frame
  ultimoAcorde = null; ultimoSiguiente = null;
  pintarSubtitulo();
}

// v107: "AC/DC · 116 BPM · cejilla 2" bajo el título
function pintarSubtitulo(){
  const el = document.getElementById("sub-cancion");
  if(!el) return;
  const partes = [];
  if(AUTOR_CANCION) partes.push(AUTOR_CANCION);
  if(bpmActual) partes.push(`${Math.round(bpmActual)} BPM`);
  if(capoActual) partes.push(`cejilla ${capoActual}`);
  el.textContent = partes.join(" · ");
}

// preferencia GLOBAL (todas las canciones). Antes era una variable suelta que
// volvía a encenderse en cada recarga: ahora se recuerda en el servidor igual
// que los grados, que es lo que uno espera de algo que no depende del tema.
let mostrarDiagramas = {{ 'true' if mostrar_diagramas else 'false' }};
const btnDiagramas = document.getElementById("toggle-diagramas");
function aplicarEstadoDiagramas(){
  btnDiagramas.classList.toggle("destacado", mostrarDiagramas);
  btnDiagramas.title = mostrarDiagramas ? "Ocultar los diagramas del mástil" : "Mostrar los diagramas del mástil";
  ultimoAcorde = null; ultimoSiguiente = null;   // fuerza redibujo
}
btnDiagramas.addEventListener("click", async () => {
  mostrarDiagramas = !mostrarDiagramas;
  aplicarEstadoDiagramas();
  try{
    await fetch("/preferencia", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ clave: "mostrar_diagramas", valor: mostrarDiagramas }),
    });
  }catch(e){ /* sin conexión: queda aplicado en esta sesión */ }
});
aplicarEstadoDiagramas();

// preferencia GLOBAL (todas las canciones) de mostrar u ocultar los grados
// armónicos. Se guarda en el servidor (no en localStorage, que no es confiable
// en la ventana pywebview) y viene inyectada al cargar la página.
let mostrarGrados = {{ 'true' if mostrar_grados else 'false' }};
const btnGrados = document.getElementById("toggle-grados");
function aplicarEstadoGrados(){
  btnGrados.classList.toggle("destacado", mostrarGrados);
  btnGrados.title = mostrarGrados
    ? "Ocultar los grados (números romanos) de los acordes"
    : "Mostrar los grados (números romanos) de los acordes";
  const linea = document.getElementById("linea-progresion");
  if(linea) linea.style.display = (mostrarGrados && tonalidad) ? "block" : "none";
  ultimoAcorde = null; ultimoSiguiente = null;   // fuerza redibujo de los grados chicos
}
btnGrados.addEventListener("click", async () => {
  mostrarGrados = !mostrarGrados;
  aplicarEstadoGrados();
  try{
    await fetch("/preferencia", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ clave: "mostrar_grados", valor: mostrarGrados }),
    });
  }catch(e){ /* si falla el guardado, igual queda aplicado en esta sesión */ }
});
// estado visual inicial del botón (sin tocar ultimoAcorde, que se declara más
// abajo -- el redibujo de los grados lo hace cargarAcordes() cuando corresponde)
btnGrados.classList.toggle("destacado", mostrarGrados);
btnGrados.title = mostrarGrados
  ? "Ocultar los grados (números romanos) de los acordes"
  : "Mostrar los grados (números romanos) de los acordes";

// --- color de la barra según duración del acorde -------------------------
// Tres colores fijos: rojo = medio compás o menos, dorado = ~1 compás,
// turquesa = 2 compases o más. Anclado a compases reales (no a la
// estadística de la canción), así el significado de cada color es siempre
// el mismo, tema tras tema.
let colorearDuracion = {{ 'true' if colorear_duracion else 'false' }};
let compasSegActual = null;   // duración de UN compás, en segundos
const btnColorDuracion = document.getElementById("toggle-color-duracion");

// Duración de un compás, calculada una sola vez con la grilla ya cargada. La
// canción tiene tempo constante de punta a punta (ver el comentario de
// _detectar_pulso: "asume 4/4 y tempo constante"), así que un único valor
// alcanza para clasificar TODOS los acordes del tema.
function actualizarReferenciaDuracion(){
  if(beatTimes.length > 1){
    compasSegActual = pasoBeatSeg() * (beatsPorCompas || 4);
  } else if(bpmActual){
    compasSegActual = (60 / bpmActual) * (beatsPorCompas || 4);
  } else {
    compasSegActual = null;   // sin pulso detectado: no hay con qué medir compases
  }
}

// Bandas discretas, no un degradé: tres colores bien distintos entre sí. Los
// umbrales son una duración ABSOLUTA en compases, no relativa a esta canción
// en particular: "medio compás" da siempre el mismo color, sea cual sea el
// tema, así no hay que releer la escala cada vez que abrís otra canción.
// Colores por banda ELEGIBLES (ver "Ajustes generales"): cada banda usa
// el color de uno de los 6 instrumentos, el mismo que ya conocés de la
// consola de faders -- así no hay una paleta nueva que aprender, es la de
// siempre. STEM_COLORES_JS trae el hex de cada instrumento desde el backend;
// seleccionColor guarda cuál instrumento eligió cada banda (persistido como
// preferencia global, igual que el resto de estos toggles).
const STEM_COLORES_JS = {{ stem_colores | tojson }};
let seleccionColor = { corto: "{{ color_corto }}", normal: "{{ color_normal }}", largo: "{{ color_largo }}" };

function hexARgb(hex){
  const h = hex.replace("#", "");
  const r = parseInt(h.substring(0, 2), 16), g = parseInt(h.substring(2, 4), 16), b = parseInt(h.substring(4, 6), 16);
  return `rgb(${r}, ${g}, ${b})`;
}

let COLOR_CORTO, COLOR_NORMAL, COLOR_LARGO;
function recalcularColoresBandas(){
  COLOR_CORTO  = hexARgb(STEM_COLORES_JS[seleccionColor.corto]);
  COLOR_NORMAL = hexARgb(STEM_COLORES_JS[seleccionColor.normal]);
  COLOR_LARGO  = hexARgb(STEM_COLORES_JS[seleccionColor.largo]);
}
recalcularColoresBandas();

function colorPorDuracion(dur){
  if(!compasSegActual || compasSegActual <= 0) return null;
  const compases = dur / compasSegActual;
  if(compases < 0.75) return COLOR_CORTO;
  if(compases < 1.75) return COLOR_NORMAL;
  return COLOR_LARGO;
}

function aplicarEstadoColorDuracion(){
  btnColorDuracion.classList.toggle("destacado", colorearDuracion);
  btnColorDuracion.title = colorearDuracion
    ? "Dejar la barra siempre del mismo color"
    : "Colorear la barra según la duración: rojo = medio compás o menos, dorado = 1 compás, turquesa = 2 compases o más";
  if(!colorearDuracion) elBarraAcorde.style.background = "";   // vuelve al degradé fijo del CSS
}
btnColorDuracion.addEventListener("click", async () => {
  colorearDuracion = !colorearDuracion;
  aplicarEstadoColorDuracion();
  try{
    await fetch("/preferencia", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ clave: "colorear_duracion", valor: colorearDuracion }),
    });
  }catch(e){ /* si falla el guardado, igual queda aplicado en esta sesión */ }
});
// estado visual inicial del botón (no toca elBarraAcorde -- se declara más
// abajo; si arranca prendido, tick() ya pinta la barra en el primer frame)
btnColorDuracion.classList.toggle("destacado", colorearDuracion);
btnColorDuracion.title = colorearDuracion
  ? "Dejar la barra siempre del mismo color"
  : "Colorear la barra según la duración: rojo = medio compás o menos, dorado = 1 compás, turquesa = 2 compases o más";

// --- qué instrumento le presta el color a cada banda de duración ---
// Ya no hace falta un panel flotante ni un botón para abrirlo: las filas viven
// dentro de "Ajustes generales", que es donde corresponde por ser una
// preferencia de toda la app y no de una canción.
document.querySelectorAll(".colores-fila").forEach(fila => {
  const banda = fila.dataset.banda;   // "corto" | "normal" | "largo"
  fila.querySelectorAll(".swatch-color").forEach(btn => {
    btn.addEventListener("click", async () => {
      if(btn.classList.contains("seleccionado")) return;   // ya era este
      seleccionColor[banda] = btn.dataset.stem;
      fila.querySelectorAll(".swatch-color").forEach(b => b.classList.toggle("seleccionado", b === btn));
      recalcularColoresBandas();
      ultimoColorBarra = null;   // fuerza a que tick() repinte con el color nuevo YA, no en el próximo cambio de acorde
      try{
        await fetch("/preferencia", {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({ clave: `color_${banda}`, valor: btn.dataset.stem }),
        });
      }catch(e){ /* si falla el guardado, igual queda aplicado en esta sesión */ }
    });
  });
});

// --- v106: color base de toda la app ---------------------------------------
// Se aplica al toque (window.mesaColorBase, en BASE_STYLE) y se guarda global en
// prefs.json. El selector libre manda muchos eventos al arrastrar: se guarda
// recién cuando para un momento.
(() => {
  const presets = Array.from(document.querySelectorAll(".tema-preset"));
  const campo = document.getElementById("color-base");
  if(!campo) return;
  let actual = {{ color_base|tojson }};
  let temporizador = null;
  function marcar(){
    presets.forEach(b => b.classList.toggle("seleccionado", (b.dataset.color || "") === actual));
    campo.value = (actual && actual.charAt(0) === "#") ? actual : "#f2b33d";
  }
  function elegir(hex, inmediato){
    actual = hex;
    if(window.mesaColorBase) window.mesaColorBase(hex);
    ultimoAcorde = null; ultimoSiguiente = null;   // redibuja los diagramas en el próximo frame
    cintaFirma = null;                              // y la cinta
    marcar();
    clearTimeout(temporizador);
    temporizador = setTimeout(() => {
      fetch("/preferencia", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ clave: "color_base", valor: actual }),
      }).catch(() => {});
    }, inmediato ? 0 : 400);
  }
  presets.forEach(b => b.addEventListener("click", () => elegir(b.dataset.color || "", true)));
  campo.addEventListener("input", () => elegir(campo.value.toLowerCase(), false));
  document.getElementById("color-base-original").addEventListener("click", () => elegir("", true));
  marcar();
})();

// --- Gafas HUD: transmisión por UDP a las gafas OLED reconvertidas -------
// Arranca con el valor que ya tenía guardado el servidor (prefs.json), igual
// que el resto de los ajustes generales. tick() es el que manda los datos
// (ver más abajo); acá solo viven los dos botones y el chip de estado.
let hudActivo = {{ 'true' if hud_activo else 'false' }};

// v93: el ícono rápido de gafas refleja TODOS los caminos, no solo el Web
// Bluetooth de este dispositivo: BLE local, BLE de la PC (hud_ble.py) y WiFi.
// "var" a propósito: se llama desde funciones que corren antes de que se
// declaren las secciones de BLE más abajo.
var gafasLocalClase = null;   // null | "buscando" | "enlazado"  (Web Bluetooth acá)
var gafasPcEstado = null;     // último /hud/estado de la PC
function pintarRapidoGafas(){
  const el = document.getElementById("rapido-gafas");
  if(!el) return;
  const pcOk = !!(gafasPcEstado && gafasPcEstado.activo && gafasPcEstado.conectado);
  let clase = null, titulo = "sin conectar";
  if(gafasLocalClase === "enlazado"){ clase = "enlazado"; titulo = "conectadas a este dispositivo"; }
  else if(pcOk){ clase = "enlazado"; titulo = "conectadas por Bluetooth a la PC"; }
  else if(gafasLocalClase === "buscando"){ clase = "buscando"; titulo = "conectando…"; }
  else if(hudActivo){ clase = "transmitiendo"; titulo = "transmitiendo por WiFi"; }
  el.classList.remove("buscando", "enlazado", "transmitiendo");
  if(clase) el.classList.add(clase);
  el.title = "Gafas HUD · " + titulo;
}
const btnHud = document.getElementById("toggle-hud");
const chipHud = document.getElementById("chip-hud-estado");
function aplicarEstadoHud(){
  btnHud.classList.toggle("destacado", hudActivo);
  btnHud.title = hudActivo
    ? "Dejar de enviar el acorde a las gafas HUD"
    : "Enviar el acorde actual por wifi a las gafas HUD";
  chipHud.classList.toggle("transmitiendo", hudActivo);
  chipHud.querySelector(".texto").textContent = hudActivo ? "transmitiendo" : "sin transmitir";
  pintarRapidoGafas();
}
btnHud.addEventListener("click", async () => {
  hudActivo = !hudActivo;
  aplicarEstadoHud();
  // al prender, fuerza a tick() a mandar el estado actual YA (si no, hasta que
  // cambiara el acorde las gafas seguían mostrando lo último que había antes
  // de apagarlo, o el default del backend si nunca se envió nada)
  if(hudActivo){ ultimoAcordeHUD = null; ultimoSiguienteHUD = null; ultimoBeatHUD = -2; }
  try{
    await fetch("/preferencia", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ clave: "hud_activo", valor: hudActivo }),
    });
  }catch(e){ /* sin conexión: queda aplicado en esta sesión */ }
});
aplicarEstadoHud();

// Bandera que viaja en el JSON del HUD ("i": 0/1) para que el firmware de las
// gafas invierta los colores de su pantalla. Acá no se dibuja nada -- solo
// se guarda la preferencia y se propaga.
let hudInvertido = {{ 'true' if hud_invertido else 'false' }};
const btnHudInvertido = document.getElementById("toggle-hud-invertido");
function aplicarEstadoHudInvertido(){
  btnHudInvertido.classList.toggle("destacado", hudInvertido);
  btnHudInvertido.title = hudInvertido
    ? "Colores normales"
    : "Invertir colores";
}
btnHudInvertido.addEventListener("click", async () => {
  hudInvertido = !hudInvertido;
  aplicarEstadoHudInvertido();
  try{
    await fetch("/preferencia", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ clave: "hud_invertido", valor: hudInvertido }),
    });
  }catch(e){ /* sin conexión: queda aplicado en esta sesión */ }
});
aplicarEstadoHudInvertido();

// v100: brillo de las gafas. Son 5 niveles; cada uno es un valor de contraste
// del OLED que viaja en el JSON ("k"). El nivel 3 es el que el firmware traía
// fijo. Se guarda como preferencia global, igual que invertir colores.
const HUD_BRILLOS = {{ hud_brillos | tojson }};
let hudBrillo = {{ hud_brillo }};
function aplicarHudBrillo(){
  document.getElementById("hud-brillo-actual").textContent = `brillo ${hudBrillo}/${HUD_BRILLOS.length}`;
  document.getElementById("hud-brillo-menos").disabled = hudBrillo <= 1;
  document.getElementById("hud-brillo-mas").disabled = hudBrillo >= HUD_BRILLOS.length;
}
async function fijarHudBrillo(nuevo){
  const nivel = Math.max(1, Math.min(HUD_BRILLOS.length, nuevo));
  if(nivel === hudBrillo) return;
  hudBrillo = nivel;
  aplicarHudBrillo();
  ultimoAcordeHUD = null;   // con las gafas en este dispositivo: reenviar ya, con el brillo nuevo
  try{
    await fetch("/preferencia", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ clave: "hud_brillo", valor: hudBrillo }),
    });
  }catch(e){ /* sin conexión: queda aplicado en esta sesión */ }
}
document.getElementById("hud-brillo-menos").addEventListener("click", () => fijarHudBrillo(hudBrillo - 1));
document.getElementById("hud-brillo-mas").addEventListener("click", () => fijarHudBrillo(hudBrillo + 1));
aplicarHudBrillo();


// --- enlace Bluetooth con las gafas --------------------------------------
// El envío lo hace el backend (bleak, en hud_ble.py); acá solo viven el toggle
// y un chip que dice si la PC tiene las gafas enganchadas. Se sondea cada 3 s
// y SOLO con el panel de ajustes generales abierto: cerrado no hay nada que
// mostrar y no tiene sentido gastar pedidos.
let hudBle = {{ 'true' if hud_ble else 'false' }};
const btnHudBle = document.getElementById("toggle-hud-ble");
const chipHudBle = document.getElementById("chip-hud-ble");

function pintarChipHudBle(d){
  gafasPcEstado = d || null;
  pintarRapidoGafas();
  const conectado = !!(d && d.conectado);
  const buscando = !!(d && d.activo && !conectado);
  chipHudBle.classList.toggle("enlazado", conectado);
  chipHudBle.classList.toggle("buscando", buscando);
  chipHudBle.querySelector(".texto").textContent =
    (!d || !d.activo) ? "bluetooth apagado" : (d.detalle || (conectado ? "conectado" : "buscando…"));
  chipHudBle.title = (d && d.nombre) ? `Gafas: ${d.nombre}` : "";
}

async function sondearHudBle(){
  if(!hudBle){ pintarChipHudBle({ activo: false }); return; }
  try{
    const r = await fetch("/hud/estado", { cache: "no-store" });
    pintarChipHudBle(await r.json());
  }catch(e){ /* sin conexión con Mesa: el chip de red ya lo está diciendo */ }
}

btnHudBle.addEventListener("click", async () => {
  hudBle = !hudBle;
  btnHudBle.classList.toggle("destacado", hudBle);
  pintarChipHudBle({ activo: hudBle, detalle: hudBle ? "buscando…" : null });
  try{
    await fetch("/preferencia", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ clave: "hud_ble", valor: hudBle }),
    });
  }catch(e){ /* sin conexión: queda aplicado en esta sesión */ }
  sondearHudBle();
});

setInterval(() => {
  if(document.hidden) return;
  if(!hudBle && document.getElementById("panel-generales").classList.contains("colapsado")) return;
  sondearHudBle();
}, 3000);
sondearHudBle();


// --- gafas conectadas a ESTE dispositivo (Web Bluetooth) ------------------
// El toggle de arriba ("Por Bluetooth") lo ejecuta Python en la PC: sirve
// mientras Mesa corre ahí, pero con la PC apagada no hay quien hable con las
// gafas. Esto es el otro camino: el navegador se conecta directo por BLE, así
// que el HUD anda igual que el resto de la app en modo offline.
//
// Dos límites que no son bugs:
//  1. Las gafas aceptan UN solo central a la vez. Si la PC está prendida con
//     "Por Bluetooth" activo, las tiene tomadas y desde acá no se conectan.
//  2. Web Bluetooth exige un gesto del usuario para elegir el dispositivo y no
//     hay reconexión automática confiable: un toque por sesión.
const BLE_SERVICIO = "6e6d0001-b5a3-f393-e0a9-e50e24dcca9e";
const BLE_CARACT   = "6e6d0002-b5a3-f393-e0a9-e50e24dcca9e";
const BLE_NOMBRE   = "MesaHUD";

let bleDispositivo = null, bleCaract = null;
const btnGafasLocal = document.getElementById("conectar-gafas-local");
const chipGafasLocal = document.getElementById("chip-hud-ble-local");

const btnRapidoGafas = document.getElementById("rapido-gafas");
function pintarGafasLocal(clase, texto, titulo){
  chipGafasLocal.classList.remove("buscando", "enlazado");
  if(clase) chipGafasLocal.classList.add(clase);
  gafasLocalClase = clase || null;
  pintarRapidoGafas();
  chipGafasLocal.querySelector(".texto").textContent = texto;
  if(titulo) chipGafasLocal.title = titulo;
}

// Marca de que en este dispositivo querés el HUD por Bluetooth. Solo con
// esto puesto se intenta la reconexión automática: si nunca usaste las gafas
// acá, la página no toca el Bluetooth al cargar.
const CLAVE_GAFAS = "mesaGafasLocal";
function recordarGafas(si){
  try{
    if(si) localStorage.setItem(CLAVE_GAFAS, "1");
    else localStorage.removeItem(CLAVE_GAFAS);
  }catch(e){}
}
function queriaGafas(){
  try{ return localStorage.getItem(CLAVE_GAFAS) === "1"; }catch(e){ return false; }
}

// La parte GATT, común al botón y a la reconexión automática.
async function conectarAlDispositivo(d){
  bleDispositivo = d;
  d.addEventListener("gattserverdisconnected", () => {
    bleCaract = null;
    pintarGafasLocal(null, "se desconectó", "Tocá el botón para volver a engancharlas");
  });
  pintarGafasLocal("buscando", "conectando…");
  const servidor = await d.gatt.connect();
  const servicio = await servidor.getPrimaryService(BLE_SERVICIO);
  bleCaract = await servicio.getCharacteristic(BLE_CARACT);
  pintarGafasLocal("enlazado", "gafas conectadas", "Conectadas a " + (d.name || BLE_NOMBRE));
  recordarGafas(true);
  // v90: con las gafas conectadas, la transmisión se prende sola
  if(!hudActivo) btnHud.click();
  // que se pongan al día ya, sin esperar al próximo cambio de acorde
  ultimoAcordeHUD = null; ultimoSiguienteHUD = null; ultimoBeatHUD = -2;
}

// Reconexión al cargar la página, sin diálogo ni gesto del usuario. Es lo que
// hace que pasar de canción a canción no te obligue a reconectar a mano: al
// navegar se destruye el documento y con él la conexión GATT, así que cada
// mesa arranca sin gafas y tiene que volver a engancharlas sola.
//
// getDevices() devuelve los dispositivos que este origen YA tiene permitidos.
// Hoy necesita el flag chrome://flags/#enable-web-bluetooth-new-permissions-backend
// en el Chrome de la tablet; sin él, la función no existe o devuelve vacío y
// todo queda como antes, con el botón manual.
//
// watchAdvertisements() espera a ver un anuncio de las gafas antes de intentar
// conectar: los dispositivos permitidos pueden estar apagados o fuera de
// alcance, y un gatt.connect() a ciegas se queda colgado un buen rato.
async function reconectarGafasSilencioso(){
  if(bleCaract) return;                       // ya conectadas
  if(!navigator.bluetooth || !navigator.bluetooth.getDevices) return;
  if(!queriaGafas()) return;                  // nunca se usaron acá

  let permitidos = [];
  try{ permitidos = await navigator.bluetooth.getDevices(); }catch(e){ return; }
  const d = permitidos.find(x => x.name === BLE_NOMBRE);
  if(!d) return;

  pintarGafasLocal("buscando", "reconectando…");
  try{
    if(d.watchAdvertisements){
      const corte = new AbortController();
      const alAlcance = new Promise((resolver) => {
        d.addEventListener("advertisementreceived", () => resolver(true), { once: true });
      });
      await d.watchAdvertisements({ signal: corte.signal });
      const espera = new Promise((resolver) => setTimeout(() => resolver(false), 6000));
      const visto = await Promise.race([alAlcance, espera]);
      try{ corte.abort(); }catch(e){}          // deja de escanear: batería
      if(!visto){
        pintarGafasLocal(null, "gafas fuera de alcance", "Prendé las gafas y tocá el botón");
        return;
      }
    }
    await conectarAlDispositivo(d);
  }catch(e){
    pintarGafasLocal(null, "sin conectar", "Tocá el botón para conectar las gafas");
  }
}

async function conectarGafasLocal(){
  if(!navigator.bluetooth){
    pintarGafasLocal(null, "sin Web Bluetooth");
    mesaAviso("Web Bluetooth no disponible en este navegador.", { error: true });
    return;
  }
  try{
    pintarGafasLocal("buscando", "elegí las gafas…");
    const elegido = await navigator.bluetooth.requestDevice({
      filters: [{ name: BLE_NOMBRE }],
      optionalServices: [BLE_SERVICIO],
    });
    await conectarAlDispositivo(elegido);
  }catch(err){
    bleCaract = null;
    const nombre = (err && err.name) || "Error";
    const mensaje = (err && err.message) || String(err);
    pintarGafasLocal(null, "no se pudo", nombre + ": " + mensaje);
    // NotFoundError lo tira TANTO cancelar el selector COMO el Bluetooth
    // apagado, el permiso de Ubicación denegado, o que no haya ninguna placa
    // que coincida. Tragárselo hacía que un fallo real se viera igual que no
    // hacer nada, que es lo peor para diagnosticar desde el atril.
    let detalle;
    if(nombre === "NotFoundError"){
      detalle = `${BLE_NOMBRE} no encontrado. Verificar Bluetooth, permiso de ubicación y que la PC no tenga las gafas tomadas.`;
    } else if(nombre === "SecurityError"){
      detalle = "Bluetooth bloqueado (requiere https).";
    } else {
      detalle = mensaje;
    }
    mesaAviso("Gafas por Bluetooth — " + nombre + " · " + detalle, { error: true, duracion: 15000 });
  }
}

btnGafasLocal.addEventListener("click", conectarGafasLocal);
// v94: segundo toque = desconectar. Apaga todos los caminos (BLE local, BLE de
// la PC y la transmisión), simétrico a cómo se prendieron al conectar.
async function desconectarGafas(){
  // antes de cortar, se borra la pantalla de las gafas: si no, quedan
  // mostrando el último acorde y parece que siguen conectadas
  const vacio = { actual: "-", siguiente: null, duracion: null, beat: -1 };
  mandarAlHUDLocal(vacio);
  if(hudActivo){
    try{
      await fetch("/hud/acorde", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(vacio),
      });
    }catch(e){}
  }
  await new Promise(r => setTimeout(r, 350));   // que la escritura BLE salga antes del corte
  try{
    if(bleDispositivo && bleDispositivo.gatt && bleDispositivo.gatt.connected) bleDispositivo.gatt.disconnect();
  }catch(e){}
  bleCaract = null;
  recordarGafas(false);   // que no se reconecten solas al cambiar de tema
  if(hudBle) btnHudBle.click();
  if(hudActivo) btnHud.click();
  pintarGafasLocal(null, "desconectadas");
}

btnRapidoGafas.addEventListener("click", () => {
  const pcOk = !!(gafasPcEstado && gafasPcEstado.activo && gafasPcEstado.conectado);
  if(bleCaract || pcOk || hudActivo || hudBle){ desconectarGafas(); return; }
  if(ES_LA_PC){
    // la ventana de la PC no tiene Web Bluetooth: se conecta hud_ble.py
    if(!hudBle) btnHudBle.click();
    if(!hudActivo) btnHud.click();
    return;
  }
  if(hudBle){
    mesaAviso("Las gafas están tomadas por el Bluetooth de la PC. Apagá «Por Bluetooth» en Ajustes para conectarlas acá.", { error: true });
    return;
  }
  conectarGafasLocal();
});

// Al abrir cada mesa. Se le da un respiro para no competir con la carga de los
// stems, que es lo urgente. Si el flag de permisos persistentes no está, esto
// vuelve enseguida sin hacer nada.
setTimeout(reconectarGafasSilencioso, 800);
// y al volver del bfcache (botón atrás entre canciones), donde no hay load
window.addEventListener("pageshow", (e) => { if(e.persisted) reconectarGafasSilencioso(); });

// Una escritura BLE por vez: si llega un acorde nuevo mientras la anterior
// está en vuelo, el navegador rechaza con "GATT operation already in
// progress". Se guarda el último y se manda al terminar: lo que importa es el
// acorde que suena ahora, no la cola de los que ya pasaron.
let bleEnVuelo = false, blePendiente = null;

async function bombearBLE(){
  if(bleEnVuelo || !bleCaract || blePendiente === null) return;
  bleEnVuelo = true;
  try{
    while(blePendiente !== null && bleCaract){
      const datos = blePendiente;
      blePendiente = null;
      await bleCaract.writeValueWithoutResponse(datos);
    }
  }catch(e){
    // conexión caída a mitad de camino: el listener de desconexión repinta
  }finally{
    bleEnVuelo = false;
  }
}

// Manda el estado a las gafas por el camino local. Devuelve true si lo
// resolvió acá, y entonces no hace falta molestar al backend.
function mandarAlHUDLocal(estado){
  if(!bleCaract) return false;
  // la fuente del OLED no tiene el em dash que Mesa usa para "sin acorde":
  // mismo saneo que hace _hud_sanear() en el backend
  const limpiar = (t) => (t === null || t === undefined) ? null : String(t).split("—").join("-");
  const payload = JSON.stringify({
    c: limpiar(estado.actual) || "-",
    n: limpiar(estado.siguiente),
    d: estado.duracion,
    b: estado.beat,
    i: hudInvertido ? 1 : 0,
    m: estado.modo || 0,
    // el título solo viaja cuando se muestra, para no engordar cada paquete
    t: estado.modo === 1 ? hudTextoPlano(estado.titulo, 40) : undefined,
    r: estado.rasgueo ? 1 : 0,
    // v100: cejilla (solo con el título) y contraste del OLED
    p: estado.modo === 1 ? (estado.capo || 0) : undefined,
    k: HUD_BRILLOS[hudBrillo - 1],
  });
  blePendiente = new TextEncoder().encode(payload);
  bombearBLE();
  return true;
}


// --- importar acordes desde un MIDI (ej. el que exporta Chordify) ---
document.getElementById("importar-midi").addEventListener("click", () => {
  document.getElementById("archivo-midi").click();
});

document.getElementById("archivo-midi").addEventListener("change", async (e) => {
  const archivo = e.target.files[0];
  if(!archivo) return;
  const btn = document.getElementById("importar-midi");
  const original = btn.textContent;
  btn.disabled = true;
  btn.textContent = "importando…";
  try{
    const fd = new FormData();
    fd.append("midi", archivo);
    const r = await fetch(`/importar_midi/{{ song }}`, { method: "POST", body: fd });
    const d = await r.json();
    if(!r.ok) throw new Error(d.error || `HTTP ${r.status}`);
    await cargarAcordes();
    await cargarRasgueo();   // v112: el servidor las reubicó (la sincronía volvió a 0)
    let msg = `Importados ${d.acordes} acordes a ${d.bpm} BPM.`;
    // v103: con los acordes ya en pantalla, se mide el detector contra este
    // MIDI. Si falla no pasa nada: la importación ya está hecha.
    btn.textContent = "comparando…";
    const coincidencia = await compararConDetector(false);
    if(coincidencia) msg += "\\n\\n" + textoCoincidencia(coincidencia);
    if(d.simplificados && d.simplificados.length){
      msg += "\\n\\nSe simplificaron al vocabulario de Mesa:\\n" + d.simplificados.join("\\n");
    }
    msg += "\\n\\nSi los acordes quedan corridos respecto al audio, ajustalo con los botones de Sincronía.";
    mesaAviso(msg, { duracion: 20000 });
  }catch(err){
    mesaAviso("No se pudo importar: " + err.message, { error: true });
  }finally{
    btn.disabled = false;
    btn.textContent = original;
    e.target.value = "";   // permite reimportar el mismo archivo
  }
});

// --- v103: coincidencia del detector de Mesa con el MIDI importado ---
function pintarCoincidencia(c){
  const el = document.getElementById("coincidencia-midi");
  if(!el) return;
  if(!c || typeof c.triada !== "number"){ el.style.display = "none"; return; }
  const a = c.aprendido;   // v109: detector aprendido, si hay modelo
  el.textContent = a ? `vs MIDI: plantillas ${c.triada}% · aprendido ${a.triada}%${a.entrenado_con_este ? "*" : ""}`
                     : `detector vs MIDI: ${c.triada}%`;
  el.title = `Plantillas: tríada ${c.triada}% · exacta ${c.exacta}% · raíz ${c.raiz}%`
    + (a ? `\\nAprendido: tríada ${a.triada}% · exacta ${a.exacta}% · raíz ${a.raiz}%` : "")
    + (a && a.entrenado_con_este ? "\\n* este tema se usó para entrenar: el número del aprendido sale inflado" : "")
    + (c.calculado ? `\\nmedido el ${c.calculado}` : "");
  el.style.display = "";
}

function textoCoincidencia(c){
  let t = `Detector de Mesa contra este MIDI: tríada ${c.triada}% · exacta ${c.exacta}% · raíz ${c.raiz}% (sobre ${fmt(c.segundos)} con acordes).`;
  if(c.referencia === "grilla") t += "\\nMedido contra la grilla actual: el MIDI original no quedó guardado, así que incluye lo que hayas corregido a mano.";
  if(c.confusiones && c.confusiones.length){
    t += "\\nDonde más difieren (MIDI → detector): "
      + c.confusiones.map(x => `${x.midi} → ${x.detector} ${Math.round(x.segundos)} s`).join(", ");
  }
  const a = c.aprendido;   // v109
  if(a){
    t += `\\n\\nDetector aprendido: tríada ${a.triada}% · exacta ${a.exacta}% · raíz ${a.raiz}%.`;
    if(a.entrenado_con_este) t += "\\nOjo: este tema se usó para entrenarlo, así que este número sale inflado. Los temas nuevos son los que miden de verdad.";
    if(a.confusiones && a.confusiones.length){
      t += "\\nDonde más difiere (MIDI → aprendido): "
        + a.confusiones.map(x => `${x.midi} → ${x.detector} ${Math.round(x.segundos)} s`).join(", ");
    }
  }
  return t;
}

// Devuelve el resultado, o null si no se pudo (con avisar=true lo dice).
async function compararConDetector(avisar){
  try{
    const r = await fetch(`/comparar_detector/{{ song }}`, { method: "POST" });
    const d = await r.json().catch(() => ({}));
    if(!r.ok) throw new Error(d.error || `HTTP ${r.status}`);
    pintarCoincidencia(d);
    return d;
  }catch(err){
    if(avisar) mesaAviso("No se pudo comparar: " + err.message, { error: true });
    return null;
  }
}

document.getElementById("comparar-detector").addEventListener("click", async (e) => {
  const btn = e.currentTarget;
  const original = btn.textContent;
  btn.disabled = true;
  btn.textContent = "comparando…";
  const c = await compararConDetector(true);
  btn.disabled = false;
  btn.textContent = original;
  if(c) mesaAviso(textoCoincidencia(c), { duracion: 20000 });
});

function actualizarOffsetUI(){
  const el = document.getElementById("offset-actual");
  el.textContent = `${offsetActual >= 0 ? "+" : ""}${offsetActual.toFixed(2)}s`;
}

// Las marcas viven en tiempo, no en índices. Antes cada marca se traducía al
// ÍNDICE del acorde que la contenía y el aviso se prendía al entrar a ese
// acorde: si marcabas el tiempo 3 de un acorde que venía sonando hacía dos
// compases, el aviso arrancaba dos compases antes de lo marcado. Y el "viene"
// duraba lo que durara el acorde anterior — un parpadeo si era corto, media
// vuelta si era largo. Ahora la ventana es un COMPÁS antes y un compás después
// del instante exacto, sin importar cuántos acordes entren ahí.
function recalcularMarcasRasgueo(){
  marcasRasgueo = marcasRasgueoBase
    .map(t => t + offsetActual)
    .sort((a, b) => a - b);
  idxMarcaCache = 0;
}

// Cuánto dura el aviso a cada lado de la marca. Un compás es lo que da tiempo
// a acomodar la mano; si todavía no hay pulso detectado, 2 s es un valor
// razonable para no dejar el aviso sin mostrar.
function ventanaRasgueoSeg(){
  return (compasSegActual && compasSegActual > 0) ? compasSegActual : 2;
}

// Búsqueda incremental, igual que la de acordes y beats: arranca donde quedó y
// se reinicia sola si la posición retrocede (seek, vuelta de loop).
let idxMarcaCache = 0;
function estadoRasgueoEn(pos){
  const n = marcasRasgueo.length;
  if(!n) return "";
  const ventana = ventanaRasgueoSeg();
  let i = idxMarcaCache;
  if(i >= n || pos < marcasRasgueo[i] - ventana) i = 0;
  while(i < n && marcasRasgueo[i] + ventana <= pos) i++;
  idxMarcaCache = Math.min(i, n - 1);
  if(i >= n) return "";
  const t = marcasRasgueo[i];
  if(pos >= t) return "cambio";
  if(pos >= t - ventana) return "viene";
  return "";
}

async function cargarAcordes(){
  try{
    const r = await fetch(`/acordes/{{ song }}`);
    const datos = r.ok ? await r.json() : {};
    acordes = Array.isArray(datos.segmentos) ? datos.segmentos : [];
    beatTimes = Array.isArray(datos.beat_times) ? datos.beat_times : [];
    beatsPorCompas = datos.beats_por_compas || 4;
    offsetActual = typeof datos.offset === "number" ? datos.offset : 0;
    actualizarOffsetUI();
    bpmActual = typeof datos.bpm === "number" ? datos.bpm : null;
    capoActual = typeof datos.capo === "number" ? datos.capo : 0;
    actualizarCapoUI();
    document.getElementById("bpm-actual").textContent = `BPM: ${bpmActual !== null ? bpmActual.toFixed(1) : "—"}`;
    const adv = document.getElementById("acordes-advertencia");
    if(datos.advertencia){ adv.textContent = datos.advertencia; adv.style.display = "block"; }
    else { adv.style.display = "none"; }
    pintarCoincidencia(datos.coincidencia);   // v103: última comparación guardada, si hay

    // recalcular la tonalidad y refrescar la línea de progresión + los grados
    detectarTonalidad();
    const linea = document.getElementById("linea-progresion");
    if(linea){
      linea.textContent = textoProgresion();
      linea.style.display = (mostrarGrados && tonalidad) ? "block" : "none";
    }
    ultimoAcorde = null; ultimoSiguiente = null;   // fuerza redibujo de los grados
    actualizarReferenciaDuracion();
    recalcularMarcasRasgueo();

    // si había un loop puesto, la grilla nueva puede tener los compases en
    // otro lado (corregir el tempo o el offset los mueve a todos): se vuelve
    // a encajar en el compás más cercano en vez de quedar a mitad de camino
    if(typeof reencajarLoop === "function") reencajarLoop();
  }catch(e){ /* sin acordes por ahora, no pasa nada */ }
}
cargarAcordes();

async function cargarRasgueo(){
  try{
    const r = await fetch(`/rasgueo/{{ song }}`);
    const d = r.ok ? await r.json() : { tiempos: [] };
    marcasRasgueoBase = Array.isArray(d.tiempos) ? d.tiempos.map(Number).filter(t => isFinite(t)) : [];
  }catch(e){
    marcasRasgueoBase = [];
  }
  recalcularMarcasRasgueo();
}
cargarRasgueo();

document.getElementById("editar-acordes").addEventListener("click", async () => {
  const res = await fetch(`/abrir_acordes/{{ song }}`, { method: "POST" });
  if(!res.ok){
    const err = await res.json().catch(() => ({}));
    mesaAviso("No se pudo abrir: " + (err.error || res.status), { error: true });
  }
});

// ------------------------------ editor de acordes ------------------------------
const panelEditor = document.getElementById("panel-editor");
const editorGrilla = document.getElementById("editor-grilla");
const editorEstado = document.getElementById("editor-estado");
let vocabulario = [], comienzosCompas = [], haycambios = false;
let rasgueoEditorSet = new Set();   // posiciones (0-indexadas) editadas acá; se manda al backend recién al Guardar
let celdasPorPosicion = [], totalPosicionesEditor = 0;
let beatsBaseEditor = [];   // tiempos crudos (sin offset) de cada posición de la grilla

// El editor trabaja por celda, pero las marcas se guardan por tiempo. Estas dos
// hacen la traducción: al abrir, cada tiempo guardado se pega a la celda más
// cercana (si la grilla cambió desde que se marcó, cae en la celda que le
// corresponde ahora en vez de perderse); al guardar, cada celda vuelve a ser
// el tiempo exacto de ese beat.
function posicionMasCercana(t){
  if(!beatsBaseEditor.length) return -1;
  let lo = 0, hi = beatsBaseEditor.length - 1;
  while(lo < hi){
    const mid = (lo + hi) >> 1;
    if(beatsBaseEditor[mid] < t) lo = mid + 1; else hi = mid;
  }
  // lo = primer beat >= t; el más cercano es ese o el anterior
  if(lo > 0 && Math.abs(beatsBaseEditor[lo - 1] - t) <= Math.abs(beatsBaseEditor[lo] - t)) return lo - 1;
  return lo;
}

function posicionesDesdeTiempos(tiempos){
  const set = new Set();
  (tiempos || []).forEach(t => {
    const p = posicionMasCercana(Number(t));
    if(p >= 0) set.add(p);
  });
  return set;
}

function tiemposDesdePosiciones(posiciones){
  return Array.from(posiciones)
    .sort((a, b) => a - b)
    .map(p => beatsBaseEditor[p])
    .filter(t => typeof t === "number" && isFinite(t));
}

// Cada posición en rasgueoEditorSet es un "quiebre": ahí arranca o termina un
// tramo con rasgueo distinto. Se calcula recorriendo las celdas en orden (no
// los compases, porque el cambio puede caer a mitad de uno) y prendiendo/
// apagando una bandera cada vez que se pasa por un quiebre, así que marcar el
// principio y el final de un tramo tiñe automáticamente todo lo que hay en
// el medio, sin tener que tildar celda por celda.
function posicionesPintadasDesdeQuiebres(totalPosiciones, quiebres){
  const pintadas = new Set();
  const ordenados = Array.from(quiebres).sort((a, b) => a - b);
  let activo = false, iq = 0;
  for(let p = 0; p < totalPosiciones; p++){
    while(iq < ordenados.length && ordenados[iq] === p){ activo = !activo; iq++; }
    if(activo) pintadas.add(p);
  }
  return pintadas;
}

function aplicarPintadoRasgueo(){
  const pintadas = posicionesPintadasDesdeQuiebres(totalPosicionesEditor, rasgueoEditorSet);
  celdasPorPosicion.forEach((inp, p) => {
    inp.classList.toggle("rasgueado", pintadas.has(p));
  });
}

function marcarEstado(texto, clase){
  editorEstado.textContent = texto;
  editorEstado.className = "editor-estado" + (clase ? " " + clase : "");
}

function marcarSinGuardar(){
  haycambios = true;
  marcarEstado("cambios sin guardar", "sin-guardar");
}

// Una celda vacía hereda el acorde anterior: se muestra como placeholder gris
// para que se lea igual que el "." del archivo, sin tener que escribirlo.
function refrescarHerencia(){
  const celdas = Array.from(editorGrilla.querySelectorAll(".celda"));
  let ultimo = "";
  celdas.forEach(c => {
    const v = c.value.trim();
    if(v){ ultimo = v; c.placeholder = ""; }
    else { c.placeholder = ultimo || "—"; }
  });
}

// Mismo criterio que el backend: los bemoles son el mismo acorde con otro
// nombre, así que se aceptan y se normalizan a sostenidos.
const ENARMONICOS = { "Db":"C#", "Eb":"D#", "Gb":"F#", "Ab":"G#", "Bb":"A#" };

function normalizarAcorde(v){
  const t = (v || "").trim();
  if(!t) return "";
  let raiz = t.charAt(0).toUpperCase();
  let resto = t.slice(1);
  if(resto.charAt(0) === "#" || resto.charAt(0) === "b"){
    raiz += resto.charAt(0);
    resto = resto.slice(1);
  }
  if(ENARMONICOS[raiz]) raiz = ENARMONICOS[raiz];
  return raiz + resto;
}

// v103: el silencio ("—", sin acorde) es un valor propio de la celda. Antes se
// mostraba vacío igual que "sigue el anterior", y al guardar todo lo vacío
// salía como "."; abrir y guardar el editor borraba todos los silencios del
// tema. Ahora se ve, se conserva y se puede escribir (también con un guion).
function esSilencioCelda(v){ return v === "—" || v === "–" || v === "-"; }
function tokenDeCelda(v){
  const t = (v || "").trim();
  if(!t) return ".";
  return esSilencioCelda(t) ? "—" : t;
}

function validarCelda(celda){
  const v = celda.value.trim();
  if(!v || esSilencioCelda(v)){ celda.classList.remove("invalida"); return true; }
  const ok = vocabulario.includes(normalizarAcorde(v));
  celda.classList.toggle("invalida", !ok);
  return ok;
}

function construirGrilla(datos){
  vocabulario = datos.vocabulario || [];
  comienzosCompas = datos.compases.map(c => c.inicio);
  editorGrilla.innerHTML = "";
  celdasPorPosicion = [];
  let posGlobal = 0;

  datos.compases.forEach((compas, iC) => {
    const div = document.createElement("div");
    div.className = "compas";
    div.dataset.indice = iC;

    const cab = document.createElement("div");
    cab.className = "compas-cab";
    const num = document.createElement("span");
    num.className = "compas-num";
    num.textContent = `c.${iC + 1}`;
    cab.appendChild(num);
    if(compas.inicio !== null && compas.inicio !== undefined){
      const play = document.createElement("button");
      play.className = "compas-play";
      play.innerHTML = "&#9654;";
      play.title = `Saltar a ${fmt(compas.inicio)}`;
      play.addEventListener("click", async () => {
        if(!(await esperarPistas())) return;
        if(ctx.state === "suspended") await ctx.resume();
        idxAcordeCache = 0;
        reproducirDesde(compas.inicio);
        document.getElementById("play").innerHTML = "&#10074;&#10074;";
      });
      cab.appendChild(play);
      const t = document.createElement("span");
      t.className = "compas-num";
      t.textContent = fmt(compas.inicio);
      cab.appendChild(t);
    }
    div.appendChild(cab);

    const celdas = document.createElement("div");
    celdas.className = "compas-celdas";
    compas.tokens.forEach(tok => {
      const posicion = posGlobal++;

      const wrap = document.createElement("div");
      wrap.className = "celda-wrap";

      const inp = document.createElement("input");
      inp.className = "celda";
      inp.type = "text";
      inp.maxLength = 6;   // "C#maj7"
      inp.value = (tok === ".") ? "" : tok;   // v103: el "—" se muestra, no se confunde con vacío
      inp.addEventListener("input", () => { validarCelda(inp); refrescarHerencia(); marcarSinGuardar(); });
      inp.addEventListener("blur", () => {
        const v = inp.value.trim();
        if(esSilencioCelda(v)) inp.value = "—";
        else if(v && vocabulario.includes(normalizarAcorde(v))) inp.value = normalizarAcorde(v);
        validarCelda(inp);
        refrescarHerencia();
      });
      wrap.appendChild(inp);

      // la barrita marca el quiebre exacto en esta celda puntual (el cambio
      // puede caer a mitad de compás, así que se marca acá y no en el
      // compás entero)
      const marca = document.createElement("button");
      marca.className = "celda-rasgueo";
      marca.type = "button";
      marca.title = "Marcar/desmarcar cambio de rasgueo en este acorde";
      marca.classList.toggle("activo", rasgueoEditorSet.has(posicion));
      marca.addEventListener("click", () => {
        if(rasgueoEditorSet.has(posicion)) rasgueoEditorSet.delete(posicion);
        else rasgueoEditorSet.add(posicion);
        marca.classList.toggle("activo", rasgueoEditorSet.has(posicion));
        aplicarPintadoRasgueo();
        marcarSinGuardar();
      });
      wrap.appendChild(marca);

      celdasPorPosicion[posicion] = inp;
      celdas.appendChild(wrap);
    });
    div.appendChild(celdas);
    editorGrilla.appendChild(div);
  });

  totalPosicionesEditor = posGlobal;
  aplicarPintadoRasgueo();
  refrescarHerencia();
  haycambios = false;
  marcarEstado("\u00a0");
}

async function abrirEditor(){
  marcarEstado("cargando…");
  const yaAbierto = panelEditor.style.display === "block";
  panelEditor.style.display = "block";
  // el editor queda debajo de tres paneles plegados: al abrirlo se trae a la
  // vista (no al releer tras guardar, para no mover la pantalla en la cara)
  if(!yaAbierto) panelEditor.scrollIntoView({ behavior: "smooth", block: "start" });
  try{
    const [r, rRasgueo] = await Promise.all([
      fetch(`/grilla/{{ song }}`),
      fetch(`/rasgueo/{{ song }}`),
    ]);
    const d = await r.json();
    if(!r.ok) throw new Error(d.error || `HTTP ${r.status}`);
    beatsBaseEditor = Array.isArray(d.beat_times) ? d.beat_times.map(Number) : [];
    const dRasgueo = rRasgueo.ok ? await rRasgueo.json() : { tiempos: [] };
    rasgueoEditorSet = posicionesDesdeTiempos(Array.isArray(dRasgueo.tiempos) ? dRasgueo.tiempos : []);
    construirGrilla(d);
  }catch(e){
    marcarEstado(e.message, "error");
    editorGrilla.innerHTML = "";
  }
}

document.getElementById("abrir-editor").addEventListener("click", () => {
  if(panelEditor.style.display === "block"){ panelEditor.style.display = "none"; return; }
  abrirEditor();
});

document.getElementById("editor-cerrar").addEventListener("click", () => {
  if(haycambios && !confirmarCierre()) return;
  panelEditor.style.display = "none";
});

function confirmarCierre(){
  // sin window.confirm (no anda bien en la ventana embebida): se avisa en el
  // estado y hay que tocar Cerrar de nuevo
  if(editorEstado.dataset.avisoCierre === "1"){ delete editorEstado.dataset.avisoCierre; return true; }
  editorEstado.dataset.avisoCierre = "1";
  marcarEstado("hay cambios sin guardar — Cerrar de nuevo para descartar", "error");
  setTimeout(() => { delete editorEstado.dataset.avisoCierre; }, 4000);
  return false;
}

document.getElementById("editor-guardar").addEventListener("click", async (e) => {
  const btn = e.currentTarget;
  const celdas = Array.from(editorGrilla.querySelectorAll(".celda"));
  if(!celdas.length) return;

  const invalidas = celdas.filter(c => !validarCelda(c));
  if(invalidas.length){
    marcarEstado(`${invalidas.length} acorde(s) no reconocido(s)`, "error");
    invalidas[0].focus();
    return;
  }

  const tokens = celdas.map(c => tokenDeCelda(c.value));
  btn.disabled = true;
  marcarEstado("guardando…");
  try{
    const r = await fetch(`/grilla/{{ song }}`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ tokens }),
    });
    const d = await r.json();
    if(!r.ok) throw new Error(d.error || `HTTP ${r.status}`);

    const rRasgueo = await fetch(`/rasgueo/{{ song }}`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ tiempos: tiemposDesdePosiciones(rasgueoEditorSet) }),
    });
    const dRasgueo = await rRasgueo.json();
    if(!rRasgueo.ok) throw new Error(dRasgueo.error || `HTTP ${rRasgueo.status}`);

    haycambios = false;
    marcarEstado("guardado", "guardado");
    await cargarAcordes();     // refresca el cartel grande con lo recién guardado
    await cargarRasgueo();     // idem con las marcas de cambio de rasgueo
    await abrirEditor();       // relee (por si el backend normalizó algo, ej. Bb -> A#)
    marcarEstado("guardado", "guardado");
  }catch(err){
    marcarEstado(err.message, "error");
  }finally{
    btn.disabled = false;
  }
});

// resalta el compás que está sonando, si el editor está abierto
let ultimoCompasResaltado = -1;
function resaltarCompasActual(pos){
  if(panelEditor.style.display !== "block" || !comienzosCompas.length) return;
  let idx = -1;
  for(let i = 0; i < comienzosCompas.length; i++){
    if(comienzosCompas[i] !== null && comienzosCompas[i] <= pos) idx = i; else break;
  }
  if(idx === ultimoCompasResaltado) return;
  const previo = editorGrilla.querySelector(".compas.sonando");
  if(previo) previo.classList.remove("sonando");
  if(idx >= 0){
    const el = editorGrilla.querySelector(`.compas[data-indice="${idx}"]`);
    if(el){
      el.classList.add("sonando");
      // No robamos la vista si estás escribiendo un acorde: mientras el foco
      // esté en una celda de la grilla, el scroll automático se queda quieto
      // (si no, el cursor se te va de pantalla a mitad de la corrección).
      const editando = editorGrilla.contains(document.activeElement);
      if(!editando && !scrollManualReciente()){
        // "smooth" encola animaciones y se pisan a sí mismas cuando los
        // compases duran poco (tempo rápido o compases cortos): ahí conviene
        // el salto seco, que llega siempre a tiempo.
        const durCompas = (idx + 1 < comienzosCompas.length && comienzosCompas[idx + 1] !== null)
          ? comienzosCompas[idx + 1] - comienzosCompas[idx] : 2;
        el.scrollIntoView({
          block: "start", inline: "nearest",
          behavior: durCompas < 1.2 ? "auto" : "smooth",
        });
      }
    }
  }
  ultimoCompasResaltado = idx;
}

// Si acabás de mover la grilla con el dedo, el seguimiento automático te deja
// mirar en paz un rato en vez de devolverte de un tirón al compás que suena.
// Se retoma solo, sin ningún botón que apretar.
let ultimoScrollManual = 0;
function scrollManualReciente(){ return (performance.now() - ultimoScrollManual) < 2500; }
["wheel", "touchstart", "pointerdown"].forEach((ev) => {
  editorGrilla.addEventListener(ev, () => { ultimoScrollManual = performance.now(); }, { passive: true });
});

document.getElementById("recargar-acordes").addEventListener("click", async (e) => {
  const btn = e.currentTarget;
  const original = btn.textContent;
  btn.textContent = "recargando…";
  btn.disabled = true;
  await cargarAcordes();
  btn.textContent = original;
  btn.disabled = false;
});

async function postConAviso(url, cuerpo){
  try{
    const res = await fetch(url, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: cuerpo !== undefined ? JSON.stringify(cuerpo) : undefined,
    });
    if(!res.ok){
      const err = await res.json().catch(() => ({}));
      mesaAviso(err.error || `Error ${res.status}`, { error: true });
      return false;
    }
    return true;
  }catch(e){
    mesaAviso("No se pudo conectar con el servidor: " + e.message, { error: true });
    return false;
  }
}

async function nudgeOffset(delta){
  if(await postConAviso(`/desfasar_acordes/{{ song }}`, { delta })) await cargarAcordes();
}

document.getElementById("offset-menos-beat").addEventListener("click", () => {
  nudgeOffset(-(pasoBeatSeg() || 0.5));
});
document.getElementById("offset-mas-beat").addEventListener("click", () => {
  nudgeOffset(pasoBeatSeg() || 0.5);
});
document.getElementById("offset-menos-fino").addEventListener("click", () => nudgeOffset(-0.05));
document.getElementById("offset-mas-fino").addEventListener("click", () => nudgeOffset(0.05));

// Confirmación propia (sin window.confirm — falla en algunas ventanas embebidas
// como pywebview/WebView2): primer click avisa, segundo click dentro de 4s ejecuta.
function confirmarEnBoton(boton, textoAviso, accion){
  if(boton.dataset.confirmando === "1"){
    clearTimeout(Number(boton.dataset.timeoutId));
    delete boton.dataset.confirmando;
    boton.classList.remove("confirmando");
    boton.textContent = boton.dataset.textoOriginal;
    accion();
    return;
  }
  boton.dataset.textoOriginal = boton.textContent;
  boton.dataset.confirmando = "1";
  boton.classList.add("confirmando");
  boton.textContent = textoAviso;
  boton.dataset.timeoutId = setTimeout(() => {
    delete boton.dataset.confirmando;
    boton.classList.remove("confirmando");
    boton.textContent = boton.dataset.textoOriginal;
  }, 4000);
}

// v103: corregir el tempo vuelve a detectar los acordes. El "¿Seguro?" no lo
// decía; se avisa en el primer toque, que es cuando todavía se puede frenar.
function avisarRedeteccion(boton){
  if(boton.dataset.confirmando === "1") return;
  mesaAviso("Corregir el tempo vuelve a detectar los acordes: se pierden las correcciones hechas a mano y lo importado de un MIDI. La cejilla, la sincronía y las marcas de rasgueo se conservan.", { duracion: 7000 });
}

async function corregirTempo(factor, boton){
  const original = boton.textContent;
  boton.disabled = true;
  boton.textContent = "recalculando…";
  if(await postConAviso(`/tempo_acordes/{{ song }}`, { factor })) await cargarAcordes();
  boton.disabled = false;
  boton.textContent = original;
}
document.getElementById("tempo-mitad").addEventListener("click", (e) => {
  avisarRedeteccion(e.currentTarget);
  confirmarEnBoton(e.currentTarget, "¿Seguro? tocá de nuevo", () => corregirTempo(0.5, e.currentTarget));
});
document.getElementById("tempo-doble").addEventListener("click", (e) => {
  avisarRedeteccion(e.currentTarget);
  confirmarEnBoton(e.currentTarget, "¿Seguro? tocá de nuevo", () => corregirTempo(2.0, e.currentTarget));
});

document.getElementById("bpm-ajustar").addEventListener("click", (e) => {  const objetivo = parseFloat(document.getElementById("bpm-manual").value);
  if(!objetivo || objetivo <= 0){ mesaAviso("Ingresá un BPM válido", { error: true }); return; }
  if(!bpmActual){ mesaAviso("Todavía no hay un BPM detectado para partir de ahí", { error: true }); return; }
  const factor = objetivo / bpmActual;
  avisarRedeteccion(e.currentTarget);
  confirmarEnBoton(e.currentTarget, "¿Seguro? tocá de nuevo", () => corregirTempo(factor, e.currentTarget));
});

async function ejecutarRegenerar(boton){
  const original = boton.textContent;
  boton.disabled = true;
  boton.textContent = "regenerando…";
  if(await postConAviso(`/regenerar_acordes/{{ song }}`)){ await cargarAcordes(); await cargarRasgueo(); }
  boton.disabled = false;
  boton.textContent = original;
}
// --- controles de cejilla ---
async function fijarCapo(nuevo){  capoActual = Math.max(0, Math.min(11, nuevo));
  actualizarCapoUI();
  await postConAviso(`/capo/{{ song }}`, { capo: capoActual });
}
document.getElementById("capo-menos").addEventListener("click", () => fijarCapo(capoActual - 1));
document.getElementById("capo-mas").addEventListener("click", () => fijarCapo(capoActual + 1));

document.getElementById("capo-sugerir").addEventListener("click", async (e) => {
  const btn = e.currentTarget;
  const original = btn.textContent;
  btn.disabled = true;
  btn.textContent = "buscando…";
  try{
    const r = await fetch(`/sugerir_capo/{{ song }}`);
    const d = await r.json();
    if(!r.ok) throw new Error(d.error || `HTTP ${r.status}`);
    await fijarCapo(d.capo);
    const cobertura = d.ranking && d.ranking[0] ? Math.round(d.ranking[0].puntaje * 100) : null;
    btn.textContent = d.capo === 0
      ? "ya está en tono fácil"
      : `traste ${d.capo}${cobertura !== null ? ` (${cobertura}% fácil)` : ""}`;
    setTimeout(() => { btn.textContent = original; }, 3500);
  }catch(err){
    mesaAviso("No se pudo sugerir: " + err.message, { error: true });
    btn.textContent = original;
  }finally{
    btn.disabled = false;
  }
});

document.getElementById("regenerar-acordes").addEventListener("click", (e) => {
  confirmarEnBoton(e.currentTarget, "¿Seguro? tocá de nuevo para confirmar", () => ejecutarRegenerar(e.currentTarget));
});

// --- fader Master: ganancia general de este dispositivo ---
// Se recuerda por dispositivo en una cookie (como la calidad). La ventana
// pywebview no conserva cookies entre arranques (modo privado), así que la PC
// además lo guarda como preferencia en el servidor ("master_pc").
const volMaster = document.getElementById("vol-master");
const volMasterValor = document.getElementById("vol-master-valor");
const ES_LA_PC = {{ 'true' if es_la_pc else 'false' }};

let volMasterTimeout = null;
volMaster.addEventListener("input", (e) => {
  const pct = Number(e.target.value);
  volMasterValor.textContent = `${pct}%`;
  const g = masterGain.gain, t = ctx.currentTime;
  g.cancelScheduledValues(t);
  g.setValueAtTime(g.value, t);
  g.setTargetAtTime(pct / 100, t, 0.015);   // rampa corta: sin chasquido
  clearTimeout(volMasterTimeout);
  volMasterTimeout = setTimeout(() => {
    document.cookie = `mesa_master=${(pct / 100).toFixed(2)}; path=/; max-age=31536000; SameSite=Lax`;
    if(ES_LA_PC){
      fetch("/preferencia", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ clave: "master_pc", valor: pct / 100 }),
      }).catch(() => {});
    }
  }, 300);
});

function acordeEnPosicion(pos){
  return acordes.find(s => pos >= s.inicio && pos < s.fin) || null;
}

// Índice del último beat que ya pasó (-1 si todavía no llegó el primero).
// Búsqueda incremental como la de los acordes: en cada frame arranca donde
// quedó en vez de recorrer todos los beats desde cero. Si la posición retrocede
// (seek, loop, cambio de grilla) se reinicia sola.
let idxBeatCache = 0;
function indiceBeatEnPosicion(pos){
  if(!beatTimes.length) return -1;
  let i = idxBeatCache;
  if(i >= beatTimes.length || beatTimes[i] > pos) i = 0;
  while(i + 1 < beatTimes.length && beatTimes[i + 1] <= pos) i++;
  idxBeatCache = i;
  return beatTimes[i] <= pos ? i : -1;
}

function beatActualEnCompas(pos){
  const i = indiceBeatEnPosicion(pos);
  return i < 0 ? -1 : i % beatsPorCompas;
}

// Una sola promesa compartida: si tocás play mientras todavía se están
// cargando las pistas, espera a que terminen TODAS en vez de arrancar con las
// que hubiera listas (que sonaban incompletas).
// Carga una pista con timeout (para no quedar esperando para siempre si el
// WiFi se corta a mitad de la descarga) y un reintento antes de darse por
// vencido.
// Cada cargarTodo() es una "generación": cambiar de velocidad antes de que
// termine la carga anterior aborta esos fetches y, si alguno igual llegara a
// decodificar, se descarta -- antes pisaban canales[id] con buffers de la
// velocidad vieja y las pistas quedaban desincronizadas entre sí.
let generacionCarga = 0;
const controladoresCarga = new Set();
const bytesPorPista = {};   // id -> bytes recibidos, para el contador de carga

function errorReemplazada(){
  const e = new Error("carga reemplazada por otra más nueva");
  e.reemplazada = true;
  return e;
}

// El tope ya no es por descarga entera (20 s para 6 pistas en paralelo era
// poco para un Tailscale con relay) sino por ESTANCAMIENTO: mientras sigan
// llegando bytes, se espera. La cabecera tiene su propio tope, más largo a
// velocidad reducida porque ffmpeg tiene que generar el mp3 antes de contestar.
const TOPE_ESTANCADO_MS = 20000;

async function cargarUnaPista(p, gen, intentosTotales = 2){
  let ultimoError = null;
  const pct = Math.round(factorVel * 100);
  const url = pct === 100 ? p.url : `${p.url}?t=${pct}`;
  const topeCabecera = pct === 100 ? 20000 : 120000;
  for(let intento = 1; intento <= intentosTotales; intento++){
    if(gen !== generacionCarga) throw errorReemplazada();
    const controlador = new AbortController();
    controladoresCarga.add(controlador);
    let temporizador = setTimeout(() => controlador.abort(), topeCabecera);
    try {
      const res = await fetch(url, { signal: controlador.signal });
      if(!res.ok) throw new Error(`HTTP ${res.status}`);
      let arrayBuf;
      if(res.body && res.body.getReader){
        const lector = res.body.getReader();
        const trozos = [];
        let recibidos = 0;
        while(true){
          clearTimeout(temporizador);
          temporizador = setTimeout(() => controlador.abort(), TOPE_ESTANCADO_MS);
          const { done, value } = await lector.read();
          if(done) break;
          trozos.push(value);
          recibidos += value.length;
          bytesPorPista[p.id] = recibidos;
          mostrarProgresoCarga();
        }
        const junto = new Uint8Array(recibidos);
        let desplaz = 0;
        for(const t of trozos){ junto.set(t, desplaz); desplaz += t.length; }
        arrayBuf = junto.buffer;
      } else {
        arrayBuf = await res.arrayBuffer();
      }
      clearTimeout(temporizador);
      if(gen !== generacionCarga) throw errorReemplazada();
      const audioBuf = await ctx.decodeAudioData(arrayBuf);
      if(gen !== generacionCarga) throw errorReemplazada();
      // al cambiar de velocidad se recargan los buffers pero se conserva el
      // nodo de ganancia y el estado del canal: los faders no se mueven solos
      const previo = canales[p.id];
      let gain, vol, muted;
      if(previo){
        gain = previo.gain; vol = previo.vol; muted = previo.muted;
      } else {
        gain = ctx.createGain();
        gain.connect(masterGain);
        const guardado = ajustesMezclaGuardados[p.id];
        vol = guardado ? guardado.vol : 1;
        muted = guardado ? !!guardado.muted : false;
        gain.gain.value = muted ? 0 : vol;
      }
      canales[p.id] = { buffer: audioBuf, gain, source: null, muted, vol };
      // el buffer está en tiempo de audio (estirado); la duración de la canción
      // sigue siendo la original
      duracion = Math.max(duracion, audioBuf.duration * factorVel);
      pistasCargadas++;
      mostrarProgresoCarga();
      return;
    } catch(err){
      if(err && err.reemplazada) throw err;
      if(gen !== generacionCarga) throw errorReemplazada();   // abortada por una carga nueva
      ultimoError = err;
      // AbortError = se estancó; cualquier otro error de red también vale la
      // pena reintentarlo una vez (corte breve de WiFi).
    } finally {
      clearTimeout(temporizador);
      controladoresCarga.delete(controlador);
    }
  }
  throw new Error(`No se pudo cargar "${p.label}" (${ultimoError && ultimoError.message ? ultimoError.message : ultimoError})`);
}

// Mientras bajan las pistas (por Tailscale pueden ser varios segundos) el
// contador de tiempo dice "cargando 3/6" y el play se ve a medias, para que se
// entienda por qué todavía no arranca. Tocar play igual deja el arranque
// programado para cuando terminen, como siempre.
let cargandoPistas = false, pistasCargadas = 0, ultimoTextoCarga = "";
function mostrarProgresoCarga(){
  if(!cargandoPistas) return;
  let bytes = 0;
  for(const id in bytesPorPista) bytes += bytesPorPista[id];
  const texto = `cargando ${pistasCargadas}/${pistas.length} · ${(bytes / (1024 * 1024)).toFixed(1)} MB`;
  if(texto === ultimoTextoCarga) return;   // llega un trozo por cada paquete: no reescribir el DOM al pedo
  ultimoTextoCarga = texto;
  document.getElementById("tiempo").textContent = texto;
}

let promesaCarga = null;
function cargarTodo(){
  if(promesaCarga) return promesaCarga;
  const gen = ++generacionCarga;
  // lo que estuviera bajando de una generación anterior se corta acá
  controladoresCarga.forEach(c => { try{ c.abort(); }catch(e){} });
  controladoresCarga.clear();
  for(const id in bytesPorPista) delete bytesPorPista[id];
  cargandoPistas = true; pistasCargadas = 0; ultimoTextoCarga = "";
  // avisa al chip de red que hay audio en vuelo: mientras dure, el latido no
  // sondea (competiría con la descarga y daría un "sin red" falso)
  window.mesaHayDescargaEnCurso = true;
  mostrarProgresoCarga();
  document.getElementById("play").classList.add("cargando");
  promesaCarga = Promise.all(pistas.map(p => cargarUnaPista(p, gen)))
    .then(() => {
      if(gen !== generacionCarga) throw errorReemplazada();
      cargandoPistas = false;
      window.mesaHayDescargaEnCurso = false;
      window.dispatchEvent(new Event("mesa-pistas-listas"));
      ultimoTiempoTexto = "";   // que el próximo frame vuelva a escribir el tiempo
      document.getElementById("tiempo").textContent = `${fmt(offsetInicio)} / ${fmt(duracion)}`;
      document.getElementById("play").classList.remove("cargando");
      actualizarLoopUI();   // recién ahora hay duración para pintar el loop en la barra
    })
    .catch(err => {
      // una carga reemplazada no es un error: la nueva ya está manejando la UI
      if(err && err.reemplazada) throw err;
      cargandoPistas = false;
      // si no se limpia acá, la bandera queda en true para siempre y el chip
      // nunca volvería a avisar de un corte de verdad
      window.mesaHayDescargaEnCurso = false;
      document.getElementById("play").classList.remove("cargando");
      document.getElementById("tiempo").textContent = "no se pudo cargar";
      // No dejamos la promesa fallida cacheada: así el próximo click en play
      // vuelve a intentar en vez de quedar trabado para siempre.
      promesaCarga = null;
      mesaAviso(`No se pudieron cargar las pistas (¿se cortó el WiFi?). Probá de nuevo.\n\n${err.message || err}`, { error: true });
      throw err;
    });
  return promesaCarga;
}

// Para los botones: espera las pistas y devuelve si están (false = falló o
// fue reemplazada por otra carga; el aviso ya lo dio cargarTodo).
async function esperarPistas(){
  try{ await cargarTodo(); return true; }
  catch(e){ return false; }
}

function fmt(s){
  s = Math.max(0, s);
  const m = Math.floor(s/60), ss = Math.floor(s%60).toString().padStart(2,"0");
  return `${m}:${ss}`;
}

// Siempre en tiempo ORIGINAL de la canción, sea cual sea la velocidad. Mientras
// corre la claqueta el arranque está programado a futuro, así que el término da
// negativo: en ese caso la posición se queda quieta en el punto de entrada.
function posicionActual(){
  if(!sonando) return offsetInicio;
  const transcurrido = ctx.currentTime - tiempoInicioCtx;
  if(transcurrido <= 0) return offsetInicio;
  return offsetInicio + transcurrido * factorVel;
}

function detenerFuentes(){
  Object.values(canales).forEach(c => {
    if(c.source){ try{ c.source.stop(); }catch(e){} c.source = null; }
  });
  cancelarClaqueta();
}

// offset viene en tiempo original; el buffer está estirado, por eso se divide.
// "cuando" permite programar el arranque exacto al final de la claqueta.
function reproducirDesde(offset, cuando){
  detenerFuentes();
  const start = (cuando === undefined) ? ctx.currentTime + 0.05 : cuando;
  Object.values(canales).forEach(c => {
    const src = ctx.createBufferSource();
    src.buffer = c.buffer;
    src.connect(c.gain);
    src.start(start, offset / factorVel);
    c.source = src;
  });
  offsetInicio = offset;
  tiempoInicioCtx = start;
  sonando = true;
}

function pausar(){
  offsetInicio = posicionActual();
  detenerFuentes();
  sonando = false;
}

// ------------------------------ claqueta ------------------------------
// mientras corre la claqueta, los puntos del compás se encienden al ritmo de
// los clics (antes el cartel quedaba quieto y con el volumen bajo no se sabía
// cuándo entrar). Se guarda el cronograma para que el tick lo pueda seguir.
let claquetaInfo = null;   // {t0, paso, n}

function cancelarClaqueta(){
  clicksProgramados.forEach(o => { try{ o.stop(); }catch(e){} });
  clicksProgramados = [];
  claquetaInfo = null;
  cuentaInfo = null;   // v89: la cuenta regresiva usa los mismos clics programados
}

function beatDeClaqueta(){
  if(!claquetaInfo || !sonando) return -1;
  const i = Math.floor((ctx.currentTime - claquetaInfo.t0) / claquetaInfo.paso);
  if(i < 0 || i >= claquetaInfo.n) return -1;
  return i % (beatsPorCompas || 4);
}

function clic(t, acento){
  const osc = ctx.createOscillator();
  const g = ctx.createGain();
  osc.frequency.value = acento ? 1500 : 950;
  g.gain.setValueAtTime(0.0001, t);
  g.gain.exponentialRampToValueAtTime(acento ? 0.45 : 0.26, t + 0.002);
  g.gain.exponentialRampToValueAtTime(0.0001, t + 0.07);
  osc.connect(g); g.connect(masterGain);
  osc.start(t);
  osc.stop(t + 0.09);
  clicksProgramados.push(osc);
}

// Duración real (de reloj) de un tiempo: a velocidad reducida los clics tienen
// que ir igual de lentos que la música, o la claqueta no serviría de entrada.
function pasoBeatReal(){
  let paso = 0.5;
  if(beatTimes.length > 1) paso = pasoBeatSeg();
  else if(bpmActual) paso = 60 / bpmActual;
  return paso / factorVel;
}

// Arranca en "offset" precedido por un compás de clics. Devuelve el instante
// (de ctx) en que empieza el audio.
function arrancarConClaqueta(offset){
  const paso = pasoBeatReal();
  const n = beatsPorCompas || 4;
  const t0 = ctx.currentTime + 0.08;
  detenerFuentes();
  for(let i = 0; i < n; i++) clic(t0 + i * paso, i === 0);
  claquetaInfo = { t0, paso, n };
  const inicioAudio = t0 + n * paso;
  reproducirDesdeSinCancelarClaqueta(offset, inicioAudio);
  return inicioAudio;
}

// v89: cuenta regresiva 4-3-2-1. Mismo mecanismo que la claqueta (bips y
// arranque programados con el reloj de audio, cancelables con pausar()), pero
// siempre de 1 segundo por número, sin importar tempo ni velocidad.
let cuentaRegresiva = {{ 'true' if cuenta_regresiva else 'false' }};
let cuentaInfo = null;   // {t0, n}
const CUENTA_N = 4, CUENTA_PASO = 1.0;

function arrancarConCuenta(offset){
  detenerFuentes();
  const t0 = ctx.currentTime + 0.08;
  for(let i = 0; i < CUENTA_N; i++) clic(t0 + i * CUENTA_PASO, i === CUENTA_N - 1);
  const inicioAudio = t0 + CUENTA_N * CUENTA_PASO;
  reproducirDesdeSinCancelarClaqueta(offset, inicioAudio);
  cuentaInfo = { t0, n: CUENTA_N };
  return inicioAudio;
}

// número que se está mostrando (4..1), o 0 si no hay cuenta en curso
function numeroCuenta(){
  if(!cuentaInfo || !sonando || ctx.currentTime >= tiempoInicioCtx) return 0;
  const i = Math.floor((ctx.currentTime - cuentaInfo.t0) / CUENTA_PASO);
  if(i < 0) return cuentaInfo.n;
  return Math.max(1, cuentaInfo.n - i);
}

// igual que reproducirDesde pero sin barrer los clics que acabamos de programar
function reproducirDesdeSinCancelarClaqueta(offset, cuando){
  Object.values(canales).forEach(c => {
    if(c.source){ try{ c.source.stop(); }catch(e){} c.source = null; }
    const src = ctx.createBufferSource();
    src.buffer = c.buffer;
    src.connect(c.gain);
    src.start(cuando, offset / factorVel);
    c.source = src;
  });
  offsetInicio = offset;
  tiempoInicioCtx = cuando;
  sonando = true;
}

// ------------------------------ loop A-B ------------------------------
function hayLoop(){ return loopA !== null && loopB !== null && loopB > loopA; }

// El loop se pega a los compases: marcar A a mitad de un compás casi nunca es
// lo que querés, y con la grilla ya calculada el ajuste sale gratis.
function inicioCompasDe(pos){
  if(!beatTimes.length) return Math.max(0, pos);
  let mejor = beatTimes[0];
  for(let i = 0; i < beatTimes.length; i += beatsPorCompas){
    if(beatTimes[i] <= pos + 1e-6) mejor = beatTimes[i]; else break;
  }
  return mejor;
}

function finCompasDe(pos){
  if(!beatTimes.length) return Math.min(duracion, pos + 2);
  for(let i = 0; i < beatTimes.length; i += beatsPorCompas){
    if(beatTimes[i] > pos + 1e-6) return beatTimes[i];
  }
  return duracion;
}

function numeroCompas(t){
  if(!beatTimes.length) return null;
  const i = indiceBeatEnPosicion(t + 1e-6);
  return i < 0 ? 1 : Math.floor(i / beatsPorCompas) + 1;
}

function actualizarLoopUI(){
  const info = document.getElementById("loop-info");
  const activo = hayLoop();
  info.classList.toggle("activo", activo);
  if(!activo){
    info.textContent = (loopA !== null) ? `A en ${fmt(loopA)} — falta B` : "sin loop";
  } else {
    const ca = numeroCompas(loopA), cb = numeroCompas(loopB);
    info.textContent = (ca && cb)
      ? `compás ${ca} → ${cb - 1} (${fmt(loopA)}–${fmt(loopB)})`
      : `${fmt(loopA)} – ${fmt(loopB)}`;
  }
  document.getElementById("loop-a").classList.toggle("marcado", loopA !== null);
  document.getElementById("loop-b").classList.toggle("marcado", loopB !== null);
  // el tramo del loop se pinta sobre la barra de seek (vía dos variables CSS);
  // sin loop, o sin duración todavía, ambas quedan en 0% y la barra se ve lisa
  const seek = document.getElementById("seek");
  const a = (activo && duracion) ? (loopA / duracion * 100).toFixed(2) : 0;
  const b = (activo && duracion) ? (loopB / duracion * 100).toFixed(2) : 0;
  seek.style.setProperty("--loop-a", `${a}%`);
  seek.style.setProperty("--loop-b", `${b}%`);
}

function reencajarLoop(){
  if(loopA === null && loopB === null) return;
  if(!beatTimes.length){ actualizarLoopUI(); return; }
  if(loopA !== null) loopA = inicioCompasDe(loopA);
  if(loopB !== null){
    loopB = finCompasDe(loopB - 0.001);
    if(loopA !== null && loopB <= loopA) loopB = finCompasDe(loopA);
  }
  actualizarLoopUI();
}

function reiniciarLoop(){
  idxAcordeCache = 0;
  if(claqueta) arrancarConClaqueta(loopA);
  else reproducirDesde(loopA);
}

// Un toque: A al principio y B al final del compás que suena. Después se
// puede correr B con el botón de siempre para alargar el tramo.
document.getElementById("loop-compas").addEventListener("click", () => {
  const pos = posicionActual();
  const ini = inicioCompasDe(pos), fin = finCompasDe(pos);
  if(fin <= ini) return;
  loopA = ini; loopB = fin;
  actualizarLoopUI();
});
document.getElementById("loop-a").addEventListener("click", () => {
  loopA = inicioCompasDe(posicionActual());
  if(loopB !== null && loopB <= loopA) loopB = null;
  actualizarLoopUI();
});
document.getElementById("loop-b").addEventListener("click", () => {
  const fin = finCompasDe(posicionActual());
  if(loopA !== null && fin <= loopA){ actualizarLoopUI(); return; }
  loopB = fin;
  if(loopA === null) loopA = 0;
  actualizarLoopUI();
});
document.getElementById("loop-limpiar").addEventListener("click", () => {
  loopA = loopB = null;
  actualizarLoopUI();
});

const btnClaqueta = document.getElementById("toggle-claqueta");
btnClaqueta.classList.toggle("destacado", claqueta);
btnClaqueta.addEventListener("click", () => {
  claqueta = !claqueta;
  btnClaqueta.classList.toggle("destacado", claqueta);
  btnClaqueta.style.opacity = claqueta ? "" : ".5";
});

// ------------------------------ velocidad ------------------------------
async function cambiarVelocidad(pct){
  const nuevo = pct / 100;
  if(Math.abs(nuevo - factorVel) < 1e-6) return;

  const pos = posicionActual();
  const estabaSonando = sonando;
  pausar();

  const botones = Array.from(document.querySelectorAll(".vel"));
  const estado = document.getElementById("vel-estado");
  botones.forEach(b => { b.disabled = true; });
  estado.textContent = pct === 100 ? "cargando…" : "preparando… (la 1ª vez tarda)";

  const anterior = factorVel;
  factorVel = nuevo;
  promesaCarga = null;
  duracion = 0;
  try {
    await cargarTodo();
  } catch(e){
    // otra velocidad pedida encima de esta: la nueva se encarga de todo
    if(e && e.reemplazada) return;
    factorVel = anterior;            // volvemos a lo que había y recargamos
    promesaCarga = null; duracion = 0;
    try { await cargarTodo(); } catch(e2){}
    botones.forEach(b => { b.disabled = false; });
    estado.textContent = "no se pudo";
    return;
  }

  botones.forEach(b => {
    b.disabled = false;
    b.classList.toggle("marcado", Number(b.dataset.vel) === pct);
  });
  estado.textContent = pct === 100 ? "" : "mismo tono";

  offsetInicio = Math.max(0, Math.min(pos, duracion));
  idxAcordeCache = 0;
  if(estabaSonando) reproducirDesde(offsetInicio);
}

document.querySelectorAll(".vel").forEach(b => {
  b.addEventListener("click", () => cambiarVelocidad(Number(b.dataset.vel)));
});

document.getElementById("play").addEventListener("click", async () => {
  if(ctx.state === "suspended") await ctx.resume();
  if(!(await esperarPistas())) return;
  if(sonando){
    pausar();
    document.getElementById("play").innerHTML = "&#9654;";
  } else {
    if(posicionActual() >= duracion) offsetInicio = 0;
    // con un loop puesto, dar play desde afuera del tramo entra por el principio
    if(hayLoop() && (offsetInicio < loopA || offsetInicio >= loopB)){
      offsetInicio = loopA;
      idxAcordeCache = 0;
    }
    // la claqueta solo aparece cuando hay loop: es ahí donde hace falta llegar
    // a tiempo a la entrada. Dar play normal no debería hacerte esperar.
    if(hayLoop() && claqueta) arrancarConClaqueta(offsetInicio);
    else if(!hayLoop() && cuentaRegresiva) arrancarConCuenta(offsetInicio);
    else reproducirDesde(offsetInicio);
    document.getElementById("play").innerHTML = "&#10074;&#10074;";
  }
});

document.getElementById("rebobinar").addEventListener("click", () => {
  idxAcordeCache = 0;
  const destino = hayLoop() ? loopA : 0;
  if(sonando){
    if(hayLoop() && claqueta) arrancarConClaqueta(destino);
    else reproducirDesde(destino);
  } else {
    offsetInicio = destino;
  }
  elSeek.value = duracion ? (destino / duracion) * 1000 : 0;
});

// ------------------------------ saltar por compás ------------------------------
// Con el editor cerrado (y sobre todo en modo tocar) no había forma de ir a
// "el compás 17" sin arrastrar el seek. Las flechas rodean el número del compás
// que suena. Sin grilla de beats (acordes todavía sin detectar) saltan 5 s.
function saltarA(destino){
  if(!duracion) return;
  destino = Math.max(0, Math.min(destino, duracion));
  idxAcordeCache = 0;
  if(sonando) reproducirDesde(destino); else offsetInicio = destino;
  elSeek.value = (destino / duracion) * 1000;
}
document.getElementById("compas-ant").addEventListener("click", () => {
  const pos = posicionActual();
  if(!beatTimes.length){ saltarA(pos - 5); return; }
  const ini = inicioCompasDe(pos);
  // como en cualquier reproductor: si recién empezó el compás, va al anterior
  saltarA(pos - ini > 0.35 ? ini : inicioCompasDe(ini - 0.01));
});
document.getElementById("compas-sig").addEventListener("click", () => {
  const pos = posicionActual();
  if(!beatTimes.length){ saltarA(pos + 5); return; }
  saltarA(finCompasDe(pos));
});

let arrastrandoSeek = false;
let idxAcordeCache = 0;
const elSeek = document.getElementById("seek");

// Al arrastrar, solo se actualiza la vista; el audio se reposiciona recién al
// soltar. Antes cada evento "input" recreaba las 6 fuentes (decenas de veces
// por arrastre), lo que causaba chasquidos y carga inútil de CPU.
elSeek.addEventListener("pointerdown", () => { arrastrandoSeek = true; });
elSeek.addEventListener("input", (e) => {
  if(!sonando) offsetInicio = (e.target.value/1000) * duracion;
});
function soltarSeek(){
  if(!arrastrandoSeek) return;
  arrastrandoSeek = false;
  const nuevo = (Number(elSeek.value)/1000) * duracion;
  idxAcordeCache = 0;
  if(sonando) reproducirDesde(nuevo); else offsetInicio = nuevo;
}
elSeek.addEventListener("pointerup", soltarSeek);
elSeek.addEventListener("pointercancel", soltarSeek);
elSeek.addEventListener("change", () => {
  // teclado (flechas) o cualquier cambio sin arrastre previo
  if(arrastrandoSeek){ soltarSeek(); return; }
  const nuevo = (Number(elSeek.value)/1000) * duracion;
  idxAcordeCache = 0;
  if(sonando) reproducirDesde(nuevo); else offsetInicio = nuevo;
});

// Barra espaciadora = play/pausa. Útil con la guitarra en la mano; se ignora si
// estás escribiendo en el campo de BPM.
document.addEventListener("keydown", (e) => {
  if(e.code !== "Space") return;
  const t = e.target;
  if(t && (t.tagName === "INPUT" || t.tagName === "TEXTAREA" || t.isContentEditable)) return;
  e.preventDefault();
  document.getElementById("play").click();
});

// Guarda vol/mute de todas las pistas en el servidor, con debounce para no
// mandar una request por cada pixel que se arrastra el fader.
let temporizadorGuardadoMezcla = null;
function guardarAjustesMezclaEnServidor(){
  clearTimeout(temporizadorGuardadoMezcla);
  temporizadorGuardadoMezcla = setTimeout(async () => {
    const config = {};
    document.querySelectorAll(".canal[data-id]").forEach(div => {
      const id = div.dataset.id;
      const vol = div.querySelector(".vol");
      const btn = div.querySelector(".mute");
      const btnGuia = div.querySelector(".guia");
      config[id] = {
        vol: Number(vol.value) / 100,
        muted: btn.classList.contains("muted"),
        guia: !!(btnGuia && btnGuia.classList.contains("activa")),
        vol_previo: (volPrevioGuia[id] === undefined ? 1 : volPrevioGuia[id]),
      };
    });
    try {
      await fetch(`/mezcla/{{ song }}`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(config),
      });
    } catch (e) {
      // sin conexión momentánea: no molestamos con un alert por esto,
      // el próximo cambio de fader va a reintentar guardar solo.
    }
  }, 500);
}

// Cambiar la ganancia de golpe (gain.value = x) produce un chasquido audible al
// mutear o mover el fader mientras suena. Una rampa exponencial de ~15 ms es
// inaudible como transición y elimina el clic. Se usa en todos los cambios en
// vivo; el valor inicial al crear el canal se sigue fijando directo.
function fijarGanancia(c, valor){
  const g = c.gain.gain;
  const t = ctx.currentTime;
  g.cancelScheduledValues(t);
  g.setValueAtTime(g.value, t);
  g.setTargetAtTime(valor, t, 0.015);
}

// Nivel al que queda la pista en modo guía: bajita pero audible, lo justo para
// chequearte contra la grabación sin que te tape.
const NIVEL_GUIA = 0.15;
const volPrevioGuia = {};   // id -> volumen al que volver al apagar la guía

document.querySelectorAll(".canal[data-id]").forEach(div => {
  const id = div.dataset.id;
  const btn = div.querySelector(".mute");
  const btnGuia = div.querySelector(".guia");
  const vol = div.querySelector(".vol");
  const valor = div.querySelector(".canal-valor");

  function aplicarVolumen(nuevo){
    const c = canales[id];
    const pct = Math.round(nuevo * 100);
    vol.value = pct;
    valor.textContent = `${pct}%`;
    if(!c) return;
    c.vol = nuevo;
    if(!c.muted) fijarGanancia(c, c.vol);
  }

  btn.addEventListener("click", () => {
    const c = canales[id];
    if(!c) return; // todavía cargando los stems
    c.muted = !c.muted;
    fijarGanancia(c, c.muted ? 0 : c.vol);
    btn.classList.toggle("muted", c.muted);
    guardarAjustesMezclaEnServidor();
  });

  if(btnGuia){
    btnGuia.addEventListener("click", () => {
      const c = canales[id];
      if(!c) return;
      const activando = !btnGuia.classList.contains("activa");
      if(activando){
        volPrevioGuia[id] = c.vol;
        aplicarVolumen(NIVEL_GUIA);
        // guía y mute son excluyentes: prender guía apaga el mute, si no no se
        // escucharía nada y el botón parecería roto
        if(c.muted){
          c.muted = false;
          fijarGanancia(c, c.vol);
          btn.classList.remove("muted");
        }
      } else {
        const previo = volPrevioGuia[id];
        aplicarVolumen(previo === undefined ? 1 : previo);
      }
      btnGuia.classList.toggle("activa", activando);
      guardarAjustesMezclaEnServidor();
    });
  }

  vol.addEventListener("input", () => {
    const c = canales[id];
    valor.textContent = `${vol.value}%`;
    // mover el fader a mano deja de ser "guía": el estado ya no es el que
    // puso el botón, y dejarlo encendido mentiría
    if(btnGuia && btnGuia.classList.contains("activa") && Math.abs(vol.value/100 - NIVEL_GUIA) > 1e-6){
      btnGuia.classList.remove("activa");
    }
    if(!c) return;
    c.vol = vol.value/100;
    if(!c.muted) fijarGanancia(c, c.vol);
    guardarAjustesMezclaEnServidor();
  });
});

// v114: hoja de acordes para imprimir. En la PC la ventana de pywebview no
// abre pestañas ni imprime bien, así que se le pide al servidor que la abra en
// el navegador de Windows. En la tablet se abre en una pestaña de Chrome.
document.getElementById("hoja-imprimir").addEventListener("click", async () => {
  const url = `/hoja/{{ song }}`;
  if(ES_LA_PC){
    try{
      const r = await fetch(`/abrir_hoja/{{ song }}`, { method: "POST" });
      if(r.ok) return;
    }catch(e){ /* cae a abrirla acá mismo */ }
  }
  const w = window.open(url, "_blank");
  if(!w) location.href = url;
});

document.getElementById("exportar").addEventListener("click", async () => {
  const btn = document.getElementById("exportar");
  if(!(await esperarPistas())) return;

  const config = {};
  Object.entries(canales).forEach(([id, c]) => { config[id] = { muted: c.muted, vol: c.vol }; });

  btn.disabled = true;
  const textoOriginal = btn.textContent;
  btn.textContent = "Exportando…";
  try {
    const res = await fetch(`/exportar/{{ song }}`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(config),
    });
    if(!res.ok){
      const err = await res.json().catch(() => ({}));
      mesaAviso("No se pudo exportar: " + (err.error || res.status), { error: true });
      return;
    }
    const blob = await res.blob();
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `{{ song }}_mezcla.mp3`;
    document.body.appendChild(a);
    a.click();
    a.remove();
    URL.revokeObjectURL(url);
  } finally {
    btn.disabled = false;
    btn.textContent = textoOriginal;
  }
});

// Refresco por frame (~60fps) en vez de cada 250ms: a 115 BPM un tiempo dura
// ~520ms, así que refrescar cada 250ms hacía que el acorde apareciera hasta
// medio tiempo tarde. Los elementos se cachean y solo se tocan cuando cambian.
const elTiempo = document.getElementById("tiempo");
const elPlay = document.getElementById("play");
const elAcordeActual = document.getElementById("acorde-actual");
const elAcordeSiguiente = document.getElementById("acorde-siguiente");
const elDiagramaActual = document.getElementById("diagrama-actual");
const elDiagramaSiguiente = document.getElementById("diagrama-siguiente");
const elGradoActual = document.getElementById("grado-actual");
const elGradoSiguiente = document.getElementById("grado-siguiente");
const elPuntos = Array.from(document.querySelectorAll("#puntos-compas .punto"));
const elBarraAcorde = document.getElementById("barra-acorde-relleno");
const elCompasNum = document.getElementById("compas-num");

// (las variables de caché del tick se declaran más arriba, junto a las
// preferencias de vista, porque varias de ellas las invalidan al inicializarse)

// "G", "Am", "D7" quedan como siempre. Solo los nombres largos (maj7) separan
// la raíz (tamaño normal) del sufijo (más chico, como en cualquier cifrado),
// para no ensanchar el bloque entero. El tamaño de letra y la posición del
// "próximo acorde" quedan siempre fijos — nada de reflow ni de reubicación:
// así la vista aprende dónde mirar y no hay que rebuscar el acorde en pantalla.
function renderAcordeGrande(el, texto){
  const limpio = texto || "";
  const sinNbsp = limpio.replace(/\u00a0/g, "");
  if(sinNbsp.length < 5){
    el.textContent = limpio || "\u00a0";
    return;
  }
  let raiz = sinNbsp.slice(0, 1);
  let sufijo = sinNbsp.slice(1);
  if(sufijo.charAt(0) === "#"){ raiz += "#"; sufijo = sufijo.slice(1); }
  el.textContent = "";
  el.appendChild(document.createTextNode(raiz));
  const spanSufijo = document.createElement("span");
  spanSufijo.className = "sufijo-chico";
  spanSufijo.textContent = sufijo;
  el.appendChild(spanSufijo);
}

// búsqueda incremental: arranca donde quedó en vez de recorrer todo el array
function indiceAcordeEnPosicion(pos){
  if(!acordes.length) return -1;
  let i = idxAcordeCache;
  if(i >= acordes.length || pos < acordes[i].inicio) i = 0;
  while(i < acordes.length && pos >= acordes[i].fin) i++;
  idxAcordeCache = Math.min(i, acordes.length - 1);
  return (i < acordes.length && pos >= acordes[i].inicio) ? i : -1;
}

// v90: accesos rápidos. Cada ícono de pista acciona el mismo botón mute del
// mezclador (única fuente de verdad); el estado se relee por frame y el DOM
// se toca solo al cambiar, así pedal y mezclador quedan siempre reflejados.
const ICONOS_PISTA = {"guitar":'<path d="M19 3l2 2"/><path d="M20 4l-7.5 7.5"/><path d="M10.2 10.3a3.2 3.2 0 0 0-4.6.3l-.3.4a3 3 0 0 1-1.6 1 3.4 3.4 0 0 0-1.3 5.6l1.3 1.3a3.4 3.4 0 0 0 5.6-1.3 3 3 0 0 1 1-1.6l.4-.3a3.2 3.2 0 0 0 .3-4.6z" fill="currentColor" fill-opacity=".18"/><circle cx="9" cy="15" r="1.2"/>',"vocals":'<rect x="9" y="2.5" width="6" height="11" rx="3" fill="currentColor" fill-opacity=".18"/><path d="M5.5 11a6.5 6.5 0 0 0 13 0"/><path d="M12 17.5V21"/><path d="M8.5 21h7"/>',"bass":'<path d="M18 2.5l3.5 3.5"/><path d="M19.8 4.2L11 13"/><path d="M11.8 12.2c-1.3-1.3-3.1-1.5-4.3-.4l-.5.5c-.4.4-.9.6-1.5.6-2.2.2-3.2 2.9-1.6 4.5l1.9 1.9c1.6 1.6 4.3.6 4.5-1.6 0-.6.2-1.1.6-1.5l.5-.5c1.1-1.2.9-3-.4-4.3z" fill="currentColor" fill-opacity=".18"/><path d="M17 3.5l-1 1M20.5 7l-1 1"/>',"drums":'<ellipse cx="12" cy="10" rx="8" ry="3" fill="currentColor" fill-opacity=".18"/><path d="M4 10v6c0 1.7 3.6 3 8 3s8-1.3 8-3v-6"/><path d="M8 12.6v5.9M16 12.6v5.9"/><path d="M6 3l5 5.5M18 3l-5 5.5"/>',"piano":'<rect x="3" y="4" width="18" height="16" rx="2" fill="currentColor" fill-opacity=".1"/><path d="M8 20v-6M12 20v-6M16 20v-6"/><path d="M6.5 4v10h3V4M14.5 4v10h3V4" fill="currentColor"/>',"other":'<path d="M3 12h2M7 8v8M11 5v14M15 9v6M19 11v2M21 12h0"/>'};
const rapidosPista = Array.from(document.querySelectorAll(".rapido[data-stem]")).map(b => {
  const canal = document.querySelector(`.canal[data-id="${b.dataset.stem}"]`);
  b.querySelector("svg").innerHTML = ICONOS_PISTA[b.dataset.stem] || ICONOS_PISTA.other;
  const mute = canal && canal.querySelector(".mute");
  const guia = canal && canal.querySelector(".guia");
  b.addEventListener("click", () => { if(mute) mute.click(); });
  return { b, mute, guia, estado: null };
});
// v107: el mismo ícono de cada instrumento en su fila de la mezcla
document.querySelectorAll(".canal[data-id] .canal-icono svg").forEach(svg => {
  const id = svg.closest(".canal").dataset.id;
  svg.innerHTML = ICONOS_PISTA[id] || ICONOS_PISTA.other;
});
function actualizarRapidos(){
  for(const r of rapidosPista){
    if(!r.mute) continue;
    const estado = r.mute.classList.contains("muted") ? "muted"
      : (r.guia && r.guia.classList.contains("activa")) ? "guia" : "";
    if(estado === r.estado) continue;
    r.estado = estado;
    r.b.classList.toggle("muted", estado === "muted");
    r.b.classList.toggle("guia", estado === "guia");
    r.b.setAttribute("aria-pressed", estado === "muted" ? "true" : "false");
  }
}

const elCuenta = document.getElementById("cuenta-regresiva");
let ultimoNumCuenta = 0;

function tick(){
  requestAnimationFrame(tick);
  actualizarRapidos();
  if(!duracion){
    // v99: todavía no cargaron las pistas, pero las gafas ya muestran el tema
    hudPublicar({ actual: "-", siguiente: null, duracion: null, beat: -1, modo: 1, titulo: HUD_TITULO, rasgueo: 0, capo: capoActual });
    return;
  }
  const pos = Math.min(posicionActual(), duracion);

  // vuelta del loop: se chequea antes que el fin de canción para que un loop
  // que termina justo en el último compás no dispare el salto al siguiente
  // tema del setlist
  if(sonando && hayLoop() && pos >= loopB - 0.004){
    reiniciarLoop();
    return;
  }

  const textoTiempo = `${fmt(pos)} / ${fmt(duracion)}`;
  if(!cargandoPistas && textoTiempo !== ultimoTiempoTexto){
    elTiempo.textContent = textoTiempo;
    ultimoTiempoTexto = textoTiempo;
  }
  // el slider tiene 1000 pasos: escribir el mismo valor otra vez no cambia
  // nada en pantalla pero igual obliga al navegador a recalcular estilo 60
  // veces por segundo. Se escribe solo cuando el paso realmente cambió.
  if(!arrastrandoSeek){
    const pasoSeek = Math.round((pos/duracion)*1000);
    if(pasoSeek !== ultimoPasoSeek){
      elSeek.value = pasoSeek;
      ultimoPasoSeek = pasoSeek;
    }
  }
  if(sonando && pos >= duracion){
    pausar();
    elPlay.innerHTML = "&#9654;";
    // si estamos recorriendo un setlist, encadenamos con la siguiente canción
    if(urlSiguienteSetlist){
      setTimeout(() => { window.location = urlSiguienteSetlist; }, 800);
    }
  }

  const idx = indiceAcordeEnPosicion(pos);
  const actual = idx >= 0 ? acordes[idx] : null;
  const real = actual ? actual.acorde : "—";
  const textoNuevo = actual ? formaDeAcorde(real) : "—";
  if(textoNuevo !== ultimoAcorde){
    renderAcordeGrande(elAcordeActual, textoNuevo);
    elDiagramaActual.innerHTML = mostrarDiagramas ? svgAcorde(textoNuevo, 1.25 * escalaVisual) : "";
    elGradoActual.textContent = (mostrarGrados && actual) ? gradoDe(real) : "";
    elAcordeActual.classList.add("destello");
    clearTimeout(window.__destelloTimeout);
    window.__destelloTimeout = setTimeout(() => elAcordeActual.classList.remove("destello"), 350);
    ultimoAcorde = textoNuevo;
  }
  actualizarCinta(pos);
  const sigReal = idx >= 0 && idx + 1 < acordes.length ? acordes[idx + 1].acorde : null;
  const siguiente = sigReal ? formaDeAcorde(sigReal) : null;
  if(siguiente !== ultimoSiguiente){
    renderAcordeGrande(elAcordeSiguiente, siguiente || "\u00a0");
    elDiagramaSiguiente.innerHTML = (mostrarDiagramas && siguiente) ? svgAcorde(siguiente, 0.85 * escalaVisual) : "";
    elGradoSiguiente.textContent = (mostrarGrados && sigReal) ? gradoDe(sigReal) : "";
    ultimoSiguiente = siguiente;
  }

  // v89: número de la cuenta regresiva. El DOM se toca solo cuando cambia.
  const numCuenta = numeroCuenta();
  if(numCuenta !== ultimoNumCuenta){
    elCuenta.classList.toggle("visible", numCuenta > 0);
    elCuenta.classList.remove("pulso");
    if(numCuenta > 0){
      elCuenta.textContent = numCuenta;
      void elCuenta.offsetWidth;   // reinicia la animación en cada número
      elCuenta.classList.add("pulso");
    }
    ultimoNumCuenta = numCuenta;
  }

  const enClaqueta = sonando && claquetaInfo && ctx.currentTime < tiempoInicioCtx;
  const beatActual = numCuenta > 0 ? -1
    : enClaqueta ? beatDeClaqueta() : (sonando ? beatActualEnCompas(pos) : -1);
  if(beatActual !== ultimoBeat){
    elPuntos.forEach((p, i) => p.classList.toggle("activo", i === beatActual));
    ultimoBeat = beatActual;
  }

  // celeste suave en el acorde PRÓXIMO = viene un cambio de rasgueo (arranca
  // uno nuevo, o se vuelve al de siempre); celeste sólido en el acorde ACTUAL =
  // estás dentro del cambio. Cada marca del editor es su propio aviso.
  // Se evalúa por TIEMPO en cada frame (antes se evaluaba solo al cambiar de
  // acorde, por eso el aviso se pegaba al principio del acorde en vez de al
  // instante marcado). El DOM se toca únicamente cuando el estado cambia.
  const estadoRasgueo = estadoRasgueoEn(pos);
  if(estadoRasgueo !== ultimoEstadoRasgueo){
    elAcordeSiguiente.classList.toggle("rasgueo-viene", estadoRasgueo === "viene");
    elAcordeActual.classList.toggle("rasgueo-cambio", estadoRasgueo === "cambio");
    ultimoEstadoRasgueo = estadoRasgueo;
  }

  const numCompasVal = beatTimes.length ? numeroCompas(pos) : null;
  const numCompas = numCompasVal !== null ? `c.${numCompasVal}` : "c.\u2014";
  if(numCompas !== ultimoCompasTexto){
    elCompasNum.textContent = numCompas;
    ultimoCompasTexto = numCompas;
  }

  // barra del acorde actual: se llena de 0 a 100% a lo largo del acorde, así que
  // avanza más lento cuanto más dura. Se actualiza en cada frame, no solo al
  // cambiar de acorde.
  let durAcordeActual = null;
  if(actual){
    const dur = actual.fin - actual.inicio;
    durAcordeActual = dur;
    const avance = dur > 0 ? (pos - actual.inicio) / dur : 0;
    elBarraAcorde.style.width = `${Math.max(0, Math.min(1, avance)) * 100}%`;
    const colorNuevo = colorearDuracion ? (colorPorDuracion(dur) || "") : "";
    if(colorNuevo !== ultimoColorBarra){
      elBarraAcorde.style.background = colorNuevo;
      ultimoColorBarra = colorNuevo;
    }
  } else {
    elBarraAcorde.style.width = "0%";
  }

  // gafas HUD: avisa al backend para que reenvíe por UDP broadcast a la LAN.
  // La duración del acorde solo se manda para que las gafas animen la barra
  // con su propio reloj -- no hace falta reenviar posición en cada frame.
  // Fire-and-forget y solo si "Transmitir a HUD" está prendido -- si no hay
  // gafas conectadas, si el toggle está apagado, o si falla la red, no debe
  // afectar la reproducción.
  // v89: durante la cuenta regresiva las gafas muestran el número grande en
  // lugar del acorde, y como "siguiente" el acorde con el que arranca el tema.
  const actualHUD = numCuenta > 0 ? String(numCuenta) : textoNuevo;
  const siguienteHUD = numCuenta > 0 ? textoNuevo : siguiente;
  // v99: modo de pantalla. 2 = cuenta regresiva; 1 = título, solo con el tema
  // parado al inicio (recién abierto o rebobinado); 0 = acordes. En pausa a
  // mitad del tema queda el acorde congelado, que es lo que sirve para estudiar.
  const modoHUD = numCuenta > 0 ? 2 : ((!sonando && pos < 0.05) ? 1 : 0);
  hudPublicar({
    actual: actualHUD,
    siguiente: siguienteHUD,
    duracion: (numCuenta === 0 && durAcordeActual !== null) ? +durAcordeActual.toFixed(2) : null,
    beat: beatActual,
    modo: modoHUD,
    titulo: modoHUD === 1 ? HUD_TITULO : "",
    // solo el aviso previo ("viene"): se marca el PRÓXIMO acorde
    rasgueo: (modoHUD === 0 && siguienteHUD && estadoRasgueo === "viene") ? 1 : 0,
    // v100: la cejilla se muestra debajo del título
    capo: modoHUD === 1 ? capoActual : 0,
  });

  resaltarCompasActual(pos);
}
requestAnimationFrame(tick);

// ------------------------------ modo tocar ------------------------------
// No es una pantalla aparte: es la misma página, con los paneles que no se
// tocan mientras tenés la guitarra encima colapsados por CSS, y el cartel de
// acordes escalado. La escala sale del viewport real, no del dispositivo, así
// que el monitor de la PC y la tablet usan el mismo código: en el monitor da
// letras enormes y en la tablet da lo que entre, sin duplicar reglas ni tener
// una versión distinta para cada uno.
const btnModoTocar = document.getElementById("toggle-modo-tocar");

// Espacio que ocupa lo que NO es el cartel: cabecera, transporte, barra de
// estudio y márgenes. Se mide en vivo para no depender de un número mágico.
function altoFueraDelCartel(){
  let alto = 60; // padding del body + márgenes entre paneles
  const cab = document.querySelector(".cabecera-mesa");
  const transp = document.getElementById("panel-transporte");
  const nav = document.querySelector(".setlist-nav");
  if(cab) alto += cab.offsetHeight + 12;
  if(nav) alto += nav.offsetHeight + 12;
  if(transp) alto += transp.offsetHeight + 12;
  return alto;
}

function ajustarEscalaTocar(){
  const tocando = document.body.classList.contains("modo-tocar");
  // a escala 1 el bloque mide ~680x220: los diagramas van de 50%-230 a
  // 50%+265 más su propio ancho, y la altura es fila + barra + puntos
  // v107: con las pistas al costado, el cartel tiene menos ancho
  const colPistas = document.getElementById("columna-pistas");
  const anchoCol = (document.body.classList.contains("pistas-al-lado") && colPistas) ? colPistas.offsetWidth + 20 : 0;
  const anchoDisp = Math.max(320, window.innerWidth - 40 - anchoCol);
  if(!tocando){
    // fuera de modo tocar el cartel nunca crece más allá del tamaño de
    // siempre, pero en pantallas angostas (celular, tablet en vertical) se
    // achica lo justo para entrar sin desbordar ni forzar scroll horizontal
    escalaVisual = Math.min(1, anchoDisp / 680);
  } else {
    const altoDisp = Math.max(180, window.innerHeight - altoFueraDelCartel());
    const altoBase = document.body.classList.contains("vista-cinta") ? 250 : 220;   // v87: la cinta suma ~30px netos
    escalaVisual = Math.max(0.4, Math.min(anchoDisp / 680, altoDisp / altoBase, 3));   // v86: también achica
  }
  document.documentElement.style.setProperty("--esc", escalaVisual.toFixed(3));
  // los diagramas son SVG con tamaño quemado al generarlos: hay que redibujar
  ultimoAcorde = null; ultimoSiguiente = null;
  cintaAncho = 0; cintaUltimoX = null;   // v87: la cinta vuelve a medir su ancho
}

function aplicarModoTocar(activo, guardar){
  document.body.classList.toggle("modo-tocar", activo);
  btnModoTocar.classList.toggle("destacado", activo);
  btnModoTocar.textContent = activo ? "Salir" : "Modo tocar";
  btnModoTocar.title = activo
    ? "Volver a la vista completa (Esc)"
    : "Dejar solo el cartel de acordes y el transporte, en grande (Esc para salir)";
  if(activo) cerrarEditorSiEstaAbierto();
  ajustarEscalaTocar();
  if(guardar){
    // por dispositivo: la tablet en modo tocar no obliga a la PC. La cookie
    // vale en la tablet entre sesiones; en la ventana pywebview (modo
    // privado) dura la sesión, así que la PC además guarda la preferencia.
    document.cookie = `mesa_modo_tocar=${activo ? 1 : 0}; path=/; max-age=31536000; SameSite=Lax`;
    if(ES_LA_PC){
      fetch("/preferencia", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ clave: "modo_tocar", valor: activo }),
      }).catch(() => {});
    }
  }
}

function cerrarEditorSiEstaAbierto(){
  // el editor queda oculto por CSS igual, pero conviene dejarlo cerrado de
  // verdad para que al salir del modo tocar no reaparezca a medio editar
  if(panelEditor && panelEditor.style.display !== "none"){
    panelEditor.style.display = "none";
  }
}

btnModoTocar.addEventListener("click", () => {
  aplicarModoTocar(!document.body.classList.contains("modo-tocar"), true);
});

// v86: Esc ya no sale de la vista escalada: es la única vista.

// v107: en pantallas anchas la mezcla vive al costado del cartel, como lista de
// pistas; en angostas (o si la ocultás) vuelve al cajón de siempre. Se MUEVE el
// mismo nodo (no se copia), así faders, mute, guía, pedal y resumen siguen
// atados a los mismos elementos.
(function(){
  const panel = document.getElementById("panel-mezcla");
  const destino = document.getElementById("columna-pistas-cuerpo");
  const cajonCuerpo = document.querySelector("#cajon-ajustes .cajon-cuerpo");
  if(!panel || !destino || !cajonCuerpo) return;
  const ancho = window.matchMedia("(min-width: 1000px)");
  let oculto = false;
  try{ oculto = localStorage.getItem("mesaPistasOcultas") === "1"; }catch(e){}
  function ubicar(){
    const alLado = ancho.matches && !oculto;
    document.body.classList.toggle("pistas-al-lado", alLado);
    document.body.classList.toggle("pistas-ocultas-ancho", ancho.matches && oculto);
    if(alLado){
      if(panel.parentNode !== destino) destino.appendChild(panel);
    } else if(panel.parentNode !== cajonCuerpo){
      cajonCuerpo.insertBefore(panel, cajonCuerpo.firstChild);
    }
    ajustarAlto();
    ajustarEscalaTocar();
  }
  // la columna no debe meterse debajo de la barra de transporte fija: su
  // alto máximo es lo que queda entre su borde de arriba y la barra
  function ajustarAlto(){
    const columna = document.getElementById("columna-pistas");
    const barra = document.getElementById("panel-transporte");
    if(!columna || !barra || !document.body.classList.contains("pistas-al-lado")) return;
    const arriba = columna.getBoundingClientRect().top + window.scrollY;
    columna.style.maxHeight = Math.max(240, window.innerHeight - arriba - barra.offsetHeight - 16) + "px";
  }
  window.addEventListener("resize", ajustarAlto);
  if(window.ResizeObserver) new ResizeObserver(ajustarAlto).observe(document.getElementById("panel-transporte"));
  function fijarOculto(si){
    oculto = si;
    try{ if(si) localStorage.setItem("mesaPistasOcultas", "1"); else localStorage.removeItem("mesaPistasOcultas"); }catch(e){}
    ubicar();
  }
  document.getElementById("ocultar-pistas").addEventListener("click", () => fijarOculto(true));
  document.getElementById("mostrar-pistas").addEventListener("click", () => fijarOculto(false));
  if(ancho.addEventListener) ancho.addEventListener("change", ubicar);
  else if(ancho.addListener) ancho.addListener(ubicar);
  ubicar();
})();

window.addEventListener("resize", ajustarEscalaTocar);
aplicarModoTocar(true, false);   // v86: vista única, siempre escalada
aplicarEstadoCinta();            // v87: cinta según la preferencia guardada

// Acordes/sincronía/tempo/cejilla se ajustan una vez por tema y no hace
// falta tenerlos siempre a la vista: arranca colapsado (server-side, para
// que no haya parpadeo) y el estado se recuerda como el resto de las prefs.
const panelControles = document.getElementById("panel-controles");
document.getElementById("toggle-panel-controles").addEventListener("click", () => {
  const colapsado = !panelControles.classList.contains("colapsado");
  panelControles.classList.toggle("colapsado", colapsado);
  fetch("/preferencia", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ clave: "controles_colapsados", valor: colapsado }),
  }).catch(() => {});
});

// Mismo plegado que el panel del tema, con su propia preferencia: son dos
// cosas distintas y cada uno recuerda si lo dejaste abierto o cerrado.
const panelGenerales = document.getElementById("panel-generales");
document.getElementById("toggle-panel-generales").addEventListener("click", () => {
  const colapsado = !panelGenerales.classList.contains("colapsado");
  panelGenerales.classList.toggle("colapsado", colapsado);
  fetch("/preferencia", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ clave: "generales_colapsado", valor: colapsado }),
  }).catch(() => {});
});

// Trae el volumen/mute guardado de esta canción (si hay) y lo aplica a los
// controles ANTES de empezar a cargar el audio, para que el fader ya arranque
// en la posición correcta en vez de saltar después.
async function iniciarMezclador(){
  try {
    const res = await fetch(`/mezcla/{{ song }}`);
    if(res.ok) ajustesMezclaGuardados = await res.json();
  } catch (e) {
    // sin conexión momentánea: seguimos con los valores por defecto (100%, sin mute)
  }
  document.querySelectorAll(".canal[data-id]").forEach(div => {
    const id = div.dataset.id;
    const guardado = ajustesMezclaGuardados[id];
    if(!guardado) return;
    const vol = div.querySelector(".vol");
    const valor = div.querySelector(".canal-valor");
    const btn = div.querySelector(".mute");
    const btnGuia = div.querySelector(".guia");
    const pct = Math.round(guardado.vol * 100);
    vol.value = pct;
    valor.textContent = `${pct}%`;
    btn.classList.toggle("muted", !!guardado.muted);
    if(btnGuia) btnGuia.classList.toggle("activa", !!guardado.guia);
    if(guardado.vol_previo !== undefined) volPrevioGuia[id] = guardado.vol_previo;
  });
  if(!(await esperarPistas())) return;

  // si venimos encadenados desde el tema anterior de un setlist, arrancamos
  // solos (el navegador permite autoplay porque hubo interacción del usuario
  // en la página anterior)
  if(new URLSearchParams(location.search).get("autoplay") === "1"){
    try{
      if(ctx.state === "suspended") await ctx.resume();
      if(cuentaRegresiva) arrancarConCuenta(0);
      else reproducirDesde(0);
      elPlay.innerHTML = "&#10074;&#10074;";
    }catch(e){ /* si el navegador bloquea el autoplay, queda en pausa listo para dar play */ }
  }
}
// La mezcla se guarda por canción, así que el panel puede arrancar plegado.
// Para que plegado no signifique "a ciegas", la propia cabecera dice en qué
// estado quedó la mezcla ("guitarra en mute", "voz al 40%"): se lee de un
// vistazo sin abrir nada.
const panelMezcla = document.getElementById("panel-mezcla");
const resumenMezcla = document.getElementById("resumen-mezcla");
const listaCanales = document.getElementById("canal-lista");

function actualizarResumenMezcla(){
  const partes = [];
  listaCanales.querySelectorAll(".canal[data-id]").forEach(div => {
    const nombre = (div.querySelector(".canal-nombre").textContent || "").trim().toLowerCase();
    const btnMute = div.querySelector(".mute");
    const btnGuia = div.querySelector(".guia");
    const vol = div.querySelector(".vol");
    if(btnMute && btnMute.classList.contains("muted")) partes.push(`${nombre} en mute`);
    else if(btnGuia && btnGuia.classList.contains("activa")) partes.push(`${nombre} como guía`);
    else if(vol && Number(vol.value) !== 100) partes.push(`${nombre} al ${vol.value}%`);
  });
  resumenMezcla.textContent = partes.length ? partes.join(" · ") : "todas las pistas suenan";
}

// el setTimeout(0) deja correr primero el handler propio de cada mute/fader:
// así se lee el estado ya actualizado, sin tocar ese código
["click", "input"].forEach(evento => {
  listaCanales.addEventListener(evento, () => setTimeout(actualizarResumenMezcla, 0));
});

document.getElementById("toggle-panel-mezcla").addEventListener("click", () => {
  const colapsado = !panelMezcla.classList.contains("colapsado");
  panelMezcla.classList.toggle("colapsado", colapsado);
  fetch("/preferencia", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ clave: "mezcla_colapsada", valor: colapsado }),
  }).catch(() => {});
});

// Con la tablet en el atril, lo que arruina el ensayo es que la pantalla se
// apague en la mitad del tema. El Wake Lock la mantiene despierta SOLO
// mientras algo está sonando, así que en pausa la tablet se apaga sola como
// siempre y no se queda la noche entera prendida. La API pide contexto
// seguro: anda por https (tailscale serve) y en 127.0.0.1, y donde no esté
// disponible simplemente no hace nada.
let bloqueoPantalla = null;

async function sincronizarBloqueoPantalla(){
  if(!("wakeLock" in navigator)) return;
  try{
    if(sonando && !bloqueoPantalla && document.visibilityState === "visible"){
      bloqueoPantalla = await navigator.wakeLock.request("screen");
      // Android lo suelta solo al cambiar de app: hay que enterarse para
      // poder volver a pedirlo cuando se vuelve
      bloqueoPantalla.addEventListener("release", () => { bloqueoPantalla = null; });
    } else if(!sonando && bloqueoPantalla){
      const b = bloqueoPantalla;
      bloqueoPantalla = null;
      await b.release();
    }
  }catch(e){
    // el navegador puede negarlo (batería baja, permiso): se sigue igual
    bloqueoPantalla = null;
  }
}

setInterval(sincronizarBloqueoPantalla, 1000);
document.addEventListener("visibilitychange", sincronizarBloqueoPantalla);

// Pedal físico (Arduino): escucha los eventos del pedal por SSE.
// Mute actúa sobre el mismo botón .mute de siempre (simula el click, no
// duplica lógica). Volumen mueve el fader Master y dispara su propio evento
// "input" -- así se ve correr el slider en pantalla y actúa sobre la ganancia
// del dispositivo que está sonando, con el mismo código del fader.
if(typeof EventSource !== "undefined"){
  const pedalEventos = new EventSource("/pedal/eventos");
  const PASO_VOLUMEN_PEDAL = 10;

  // El chip solo aparece cuando hay algo que decir: si en esta sesión nunca
  // hubo un pedal conectado, no se muestra nada (tocar sin pedal es un uso
  // normal y no necesita un cartel). Una vez que apareció, si se cae queda en
  // rojo -- que es justo lo que no querés enterarte a mitad del ensayo.
  const chipPedal = document.getElementById("chip-pedal");
  let huboPedal = false;
  function pintarChipPedal(d){
    if(!chipPedal) return;
    if(d.conectado) huboPedal = true;
    if(!huboPedal){ chipPedal.style.display = "none"; return; }
    chipPedal.style.display = "";
    chipPedal.classList.toggle("sin-pedal", !d.conectado);
    chipPedal.querySelector(".texto").textContent = d.conectado
      ? `pedal · ${d.puerto || "ok"}`
      : "pedal desconectado";
  }

  pedalEventos.onmessage = (e) => {
    let datos;
    try { datos = JSON.parse(e.data); } catch { return; }

    if(datos.tipo === "pedal_estado"){
      pintarChipPedal(datos);
      return;
    }

    if(datos.tipo === "mute"){
      const div = document.querySelector(`.canal[data-id="${datos.stem}"]`);
      const btn = div && div.querySelector(".mute");
      if(!btn) return;
      const debeQuedarMuted = datos.accion === "mute";
      if(btn.classList.contains("muted") !== debeQuedarMuted) btn.click();
      return;
    }

    if(datos.tipo === "play_pausa"){
      document.getElementById("play").click();
      return;
    }

    if(datos.tipo === "vol"){
      const delta = datos.direccion === "up" ? PASO_VOLUMEN_PEDAL : -PASO_VOLUMEN_PEDAL;
      const nuevo = Math.max(0, Math.min(100, Number(volMaster.value) + delta));
      volMaster.value = nuevo;
      volMaster.dispatchEvent(new Event("input", { bubbles: true }));
    }
  };
}

// v103: la apertura se anota también en este dispositivo (sirve sin conexión)
// y se intenta pasar a la PC lo que haya quedado pendiente. pageshow cubre la
// carga normal y la vuelta con "atrás" a un tema.
window.addEventListener("pageshow", () => {
  if(!window.mesaRecientes) return;
  window.mesaRecientes.anotar({{ song | tojson }});
  window.mesaRecientes.sincronizar();
});

actualizarLoopUI();
actualizarResumenMezcla();
iniciarMezclador().then(actualizarResumenMezcla);
</script>
"""

# --- v114: hoja de acordes para imprimir --------------------------------------
# Página suelta (sin BASE_STYLE: siempre blanco y negro, sin service worker ni
# fuentes externas) con los acordes por compás, lista para "Imprimir -> Guardar
# como PDF" del navegador. Se arma con lo GUARDADO en disco: acordes.txt, la
# grilla, la cejilla y las marcas de rasgueo (cambios sin guardar del editor no
# entran). Los diagramas usan el mismo DIGITACIONES/svgAcorde de MESA_HTML: se
# extrae ese bloque de ahí para no tener dos copias que se desincronicen.

_RE_DIAGRAMAS_JS = re.compile(r"const DIGITACIONES = \{.*?\n\};\n\nfunction svgAcorde\(.*?\n\}\n", re.S)
_diagramas_js_cache = None


def _diagramas_js():
    """El JS de los diagramas, o "" si no se encontró (la hoja sale sin ellos)."""
    global _diagramas_js_cache
    if _diagramas_js_cache is None:
        m = _RE_DIAGRAMAS_JS.search(MESA_HTML)
        _diagramas_js_cache = m.group(0) if m else ""
    return _diagramas_js_cache


def _partir_acorde(acorde):
    """(raíz, sufijo), para dibujar el sufijo más chico. El silencio va entero."""
    if not acorde or acorde == "—":
        return "—", ""
    raiz = acorde[:2] if acorde[:2] in NOTE_NAMES else acorde[:1]
    return raiz, acorde[len(raiz):]


def _hoja_datos(song, reales=False, por_fila=4):
    """Compases listos para dibujar, o None si el tema no tiene grilla."""
    carpeta = stems_dir(song)
    txt_path = carpeta / "acordes.txt"
    grid_path = carpeta / "acordes_grid.json"
    if not txt_path.exists() or not grid_path.exists():
        return None
    grid = json.loads(grid_path.read_text(encoding="utf-8"))
    tokens = _texto_a_tokens(txt_path.read_text(encoding="utf-8"))
    base = [float(t) for t in grid.get("beat_times") or []]
    bpc = int(grid.get("beats_por_compas", 4) or 4)
    try:
        capo = max(0, min(11, int(grid.get("capo", 0) or 0)))
    except (TypeError, ValueError):
        capo = 0
    n = min(len(tokens), len(base))
    n -= n % bpc
    if n <= 0:
        return None
    aviso = None
    if len(tokens) != len(base):
        aviso = (f"acordes.txt tiene {len(tokens)} posiciones y la grilla {len(base)}: "
                 f"la hoja usa las primeras {n}.")

    # el acorde que suena en cada tiempo ("." = sigue el anterior)
    efectivos, ultimo = [], "—"
    for t in tokens[:n]:
        if t != ".":
            ultimo = t
        efectivos.append(ultimo)
    # con cejilla, por defecto la forma que se agarra (igual que el cartel)
    if capo and not reales:
        efectivos = [transponer_acorde(a, -capo) for a in efectivos]

    # marcas de rasgueo -> tiempo de la grilla más cercano. Se guardan sin la
    # sincronía, igual que beat_times, así que se comparan directo.
    marcas = set()
    ruta_r = carpeta / "rasgueo_marcas.json"
    if ruta_r.exists():
        try:
            d = json.loads(ruta_r.read_text(encoding="utf-8"))
            arr = np.asarray(base[:n])
            if isinstance(d.get("tiempos"), list):
                for t in d["tiempos"]:
                    t = float(t)
                    i = int(np.searchsorted(arr, t))
                    cerca = [j for j in (i - 1, i) if 0 <= j < n]
                    if cerca:
                        marcas.add(min(cerca, key=lambda j: abs(arr[j] - t)))
            elif isinstance(d.get("posiciones"), list):
                marcas = {int(p) for p in d["posiciones"] if 0 <= int(p) < n}
        except (OSError, ValueError, TypeError, json.JSONDecodeError):
            marcas = set()

    compases = []
    for c in range(n // bpc):
        tiempos = efectivos[c * bpc:(c + 1) * bpc]
        items = []
        for b in range(bpc):
            if b == 0 or tiempos[b] != tiempos[b - 1]:
                items.append({"acorde": tiempos[b], "col": b})
        for k, it in enumerate(items):
            fin = items[k + 1]["col"] if k + 1 < len(items) else bpc
            it["span"] = fin - it["col"]
            it["raiz"], it["sufijo"] = _partir_acorde(it["acorde"])
        compases.append({
            "num": c + 1, "tiempos": tiempos, "partes": items,
            "silencio": all(a == "—" for a in tiempos),
            "rasgueo": sorted(p - c * bpc for p in marcas if c * bpc <= p < (c + 1) * bpc),
        })
    # fuera los compases de silencio del principio y del final (el relleno que
    # agrega el MIDI). La numeración sigue siendo la de Mesa.
    while compases and compases[0]["silencio"] and not compases[0]["rasgueo"]:
        compases.pop(0)
    while compases and compases[-1]["silencio"] and not compases[-1]["rasgueo"]:
        compases.pop()
    if not compases:
        return None

    filas = [compases[i:i + por_fila] for i in range(0, len(compases), por_fila)]
    for fila in filas:
        for k, comp in enumerate(fila):
            # "%" = igual al compás anterior. Nunca al principio de una línea:
            # ahí obligaría a mirar la línea de arriba para saber qué tocar.
            comp["repite"] = (k > 0 and not comp["silencio"]
                              and comp["tiempos"] == fila[k - 1]["tiempos"])

    usados = []
    for comp in compases:
        for it in comp["partes"]:
            if it["acorde"] != "—" and it["acorde"] not in usados:
                usados.append(it["acorde"])

    bpm = grid.get("bpm")
    try:
        bpm = int(round(float(bpm))) if bpm else None
    except (TypeError, ValueError):
        bpm = None
    return {
        "filas": filas, "bpc": bpc, "capo": capo, "bpm": bpm, "aviso": aviso,
        "usados": [{"nombre": a, "raiz": _partir_acorde(a)[0], "sufijo": _partir_acorde(a)[1]} for a in usados],
        "ultimo_num": compases[-1]["num"], "total": len(compases),
        "midi": grid.get("origen") == "midi",
    }


@app.route("/hoja/<song>")
def hoja_acordes(song):
    """Hoja de acordes por compás para imprimir. Parámetros: reales=1 (acordes
    como suenan en vez de la forma con cejilla), cpf (compases por línea) y
    diag=0 (sin diagramas)."""
    if not stems_dir(song).exists():
        return redirect(url_for("home"))
    reales = request.args.get("reales") == "1"
    try:
        por_fila = int(request.args.get("cpf", 4))
    except (TypeError, ValueError):
        por_fila = 4
    if por_fila not in (3, 4, 6, 8):
        por_fila = 4
    diagramas = request.args.get("diag", "1") != "0"

    error = None
    try:
        hoja = _hoja_datos(song, reales, por_fila)
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        hoja, error = None, str(exc)

    def url_con(**cambios):
        params = {"cpf": por_fila, "diag": 1 if diagramas else 0, "reales": 1 if reales else 0}
        params.update(cambios)
        return url_for("hoja_acordes", song=song, **params)

    d = datos_cancion(song)
    html = render_template_string(
        HOJA_HTML, song=song, titulo=d["titulo"],
        autor=("" if d["autor"] == "----------" else d["autor"]),
        hoja=hoja, error=error, reales=reales, por_fila=por_fila, diagramas=diagramas,
        diag_js=_diagramas_js(), url_con=url_con,
    )
    return Response(html, mimetype="text/html", headers={"Cache-Control": "no-store"})


@app.route("/abrir_hoja/<song>", methods=["POST"])
def abrir_hoja(song):
    """Abre la hoja en el navegador de la PC. La ventana de pywebview no abre
    pestañas nuevas ni tiene un diálogo de impresión confiable. Solo vale
    pedido desde la propia PC: no tiene sentido que la tablet abra una ventana
    en la PC de casa."""
    if request.remote_addr not in ("127.0.0.1", "::1", "localhost"):
        return jsonify({"error": "solo desde la PC"}), 403
    if not stems_dir(song).exists():
        return jsonify({"error": "canción no encontrada"}), 404
    import webbrowser
    try:
        ok = webbrowser.open("http://127.0.0.1:5000" + url_for("hoja_acordes", song=song))
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": str(exc)}), 500
    return (jsonify({"ok": True}), 200) if ok else (jsonify({"error": "no se pudo abrir el navegador"}), 500)


HOJA_HTML = """<!doctype html>
<html lang="es">
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{{ titulo }}{{ ' - ' ~ autor if autor else '' }} (acordes)</title>
<style>
  /* colores que espera svgAcorde: en papel, todo negro y grises */
  :root{ --fg-dim:#333; --diag-linea:#8a8a8a; --diag-tenue:#666; --brass:#111; }
  @page{ size:A4; margin:13mm 12mm 14mm; }
  *{ box-sizing:border-box; }
  html{ background:#e6e6ea; }
  body{
    margin:0 auto; max-width:210mm; min-height:100vh; background:#fff; color:#111;
    font:14px/1.35 system-ui, -apple-system, "Segoe UI", Roboto, sans-serif;
    padding:0 12mm 16mm; -webkit-print-color-adjust:exact; print-color-adjust:exact;
  }
  .barra{
    position:sticky; top:0; z-index:5; display:flex; flex-wrap:wrap; gap:8px; align-items:center;
    margin:0 -12mm 10mm; padding:10px 12mm; background:#1b1b20; color:#ddd; font-size:13px;
  }
  .barra a, .barra button, .barra select{
    font:inherit; color:#eee; background:#2e2e36; border:0; border-radius:999px;
    padding:8px 14px; text-decoration:none; cursor:pointer;
  }
  .barra .primario{ background:#f2b33d; color:#1a1306; font-weight:700; }
  .barra .activo{ background:rgba(242,179,61,.22); color:#f2b33d; }
  .barra .esp{ flex:1; }
  .aviso{ margin:0 0 10px; padding:8px 12px; border-radius:8px; background:#fff4d6; color:#5a4300; font-size:12.5px; }
  .vacio{ padding:40px 0; text-align:center; color:#555; }

  header{ border-bottom:2px solid #111; padding-bottom:10px; margin-bottom:12px; }
  header h1{ margin:0; font-size:26px; font-weight:800; letter-spacing:-.01em; line-height:1.15; }
  header .autor{ font-size:15px; color:#444; margin-top:2px; }
  header .meta{ margin-top:8px; font-size:13px; color:#222; display:flex; gap:6px 16px; flex-wrap:wrap; }

  .diagramas{ display:flex; flex-wrap:wrap; gap:4px 8px; margin:0 0 14px; break-inside:avoid; page-break-inside:avoid; }
  .diag{ display:flex; flex-direction:column; align-items:center; min-width:56px; }
  .diag-nombre{ font:700 14px ui-monospace, "Cascadia Mono", Consolas, monospace; margin-bottom:-2px; }
  .diag-nombre small, .ac small{ font-size:.62em; font-weight:600; }

  .fila{
    display:grid; grid-template-columns:28px repeat({{ por_fila }}, minmax(0, 1fr));
    margin:0 0 8px; break-inside:avoid; page-break-inside:avoid;
  }
  .num{ font:600 10px ui-monospace, Consolas, monospace; color:#888; text-align:right; padding:3px 6px 0 0; }
  .compas{
    position:relative; display:grid; align-items:center; min-width:0;
    height:52px; border-left:2px solid #111; padding:0 4px 0 7px;
  }
  .compas.cierra{ border-right:2px solid #111; }
  .compas.final{ border-right:6px double #111; }
  .ac{ font:700 19px/1 ui-monospace, "Cascadia Mono", Consolas, monospace; white-space:nowrap; overflow:hidden; text-overflow:clip; }
  .ac.sil{ color:#999; font-weight:400; }
  .rep{ grid-column:1 / -1; text-align:center; font:700 22px ui-monospace, Consolas, monospace; color:#555; }
  .capa{ position:absolute; left:7px; right:4px; display:grid; pointer-events:none; }
  .ticks{ bottom:5px; }
  .ticks i{ display:block; width:7px; height:2px; background:#c8c8c8; }
  .marcas{ top:1px; font-size:9px; line-height:1; color:#111; }

  .leyenda{ margin-top:14px; padding-top:8px; border-top:1px solid #ccc; font-size:11px; color:#555; display:flex; gap:6px 18px; flex-wrap:wrap; }

  @media (max-width:600px){
    body{ padding:0 10px 16px; }
    .barra{ margin:0 -10px 14px; padding:10px; }
    .ac{ font-size:15px; }
    .fila{ grid-template-columns:22px repeat({{ por_fila }}, minmax(0, 1fr)); }
  }
  @media print{
    html{ background:#fff; }
    body{ max-width:none; padding:0; min-height:0; }
    .barra, .aviso{ display:none !important; }
  }
</style>

<div class="barra">
  <button class="primario" type="button" onclick="window.print()">Imprimir / Guardar PDF</button>
  {% if hoja and hoja.capo %}
  <a class="{{ '' if reales else 'activo' }}" href="{{ url_con(reales=0) }}">Como se tocan (cejilla {{ hoja.capo }})</a>
  <a class="{{ 'activo' if reales else '' }}" href="{{ url_con(reales=1) }}">Como suenan</a>
  {% endif %}
  <select aria-label="Compases por línea" onchange="location.href=this.value">
    {% for k in (3, 4, 6, 8) %}
    <option value="{{ url_con(cpf=k) }}"{{ ' selected' if k == por_fila else '' }}>{{ k }} compases por línea</option>
    {% endfor %}
  </select>
  <a class="{{ 'activo' if diagramas else '' }}" href="{{ url_con(diag=0 if diagramas else 1) }}">Diagramas</a>
  <span class="esp"></span>
  <a href="{{ url_for('mesa', song=song) }}">Volver a Mesa</a>
</div>

<header>
  <h1>{{ titulo }}</h1>
  {% if autor %}<div class="autor">{{ autor }}</div>{% endif %}
  {% if hoja %}
  <div class="meta">
    {% if hoja.bpm %}<span>&#9833; = {{ hoja.bpm }}</span>{% endif %}
    <span>{{ hoja.bpc }}/4</span>
    {% if hoja.capo %}<span>Cejilla en traste {{ hoja.capo }} &middot; {{ 'acordes como suenan' if reales else 'acordes como se tocan' }}</span>{% endif %}
    <span>{{ hoja.total }} compases</span>
  </div>
  {% endif %}
</header>

{% if hoja %}
  {% if hoja.aviso %}<div class="aviso">{{ hoja.aviso }}</div>{% endif %}

  {% if diagramas and diag_js and hoja.usados %}
  <div class="diagramas">
    {% for a in hoja.usados %}
    <div class="diag" data-acorde="{{ a.nombre }}"><span class="diag-nombre">{{ a.raiz }}{% if a.sufijo %}<small>{{ a.sufijo }}</small>{% endif %}</span></div>
    {% endfor %}
  </div>
  {% endif %}

  {% for fila in hoja.filas %}
  <div class="fila">
    <div class="num">{{ fila[0].num }}</div>
    {% for c in fila %}
    <div class="compas{{ ' cierra' if loop.last else '' }}{{ ' final' if c.num == hoja.ultimo_num else '' }}" style="grid-template-columns:repeat({{ hoja.bpc }}, minmax(0, 1fr));">
      {% if c.repite %}<span class="rep">%</span>
      {% elif c.silencio %}<span class="ac sil" style="grid-column:1 / -1;">&mdash;</span>
      {% else %}{% for it in c.partes %}<span class="ac{{ ' sil' if it.acorde == '—' else '' }}" style="grid-column:{{ it.col + 1 }} / span {{ it.span }};">{{ it.raiz }}{% if it.sufijo %}<small>{{ it.sufijo }}</small>{% endif %}</span>{% endfor %}{% endif %}
      <div class="capa ticks" style="grid-template-columns:repeat({{ hoja.bpc }}, 1fr);">{% for b in range(hoja.bpc) %}<i></i>{% endfor %}</div>
      {% if c.rasgueo %}<div class="capa marcas" style="grid-template-columns:repeat({{ hoja.bpc }}, 1fr);">{% for b in c.rasgueo %}<span style="grid-column:{{ b + 1 }};">&#9660;</span>{% endfor %}</div>{% endif %}
    </div>
    {% endfor %}
  </div>
  {% endfor %}

  <div class="leyenda">
    <span>% = igual al compás anterior</span>
    <span>&mdash; = sin acorde</span>
    <span>&#9660; = cambio de rasgueo</span>
    <span>El número de cada línea es el compás de Mesa</span>
  </div>
{% else %}
  <p class="vacio">{{ error or 'Este tema todavía no tiene grilla de compases. Abrilo en Mesa para que se analice (si no tiene batería, no hay compases para armar la hoja).' }}</p>
{% endif %}

{% if hoja and diagramas and diag_js %}
<script>
{{ diag_js|safe }}
document.querySelectorAll(".diag[data-acorde]").forEach(function(el){
  var svg = svgAcorde(el.dataset.acorde, 0.8);
  if(svg) el.insertAdjacentHTML("beforeend", svg);
});
</script>
{% endif %}
</html>
"""


# --- Pedal físico (Arduino) --------------------------------------------------
# Un Arduino conectado por USB manda por serial: "MUTE:guitarra" / "UNMUTE:guitarra"
# al pisar/soltar el switch de mute, "VOL_UP" / "VOL_DOWN" al pisar los de
# volumen, y "PLAY_PAUSE" al pisar el de play/pausa. Este hilo las lee y las
# reenvía a los navegadores conectados vía SSE, para que actúen sobre los
# mismos controles que ya usa el mezclador (botón .mute, fader Master, botón
# play) -- el pedal solo los opera desde el lado del servidor, no duplica lógica.
# Puerto del pedal. Vacío = se detecta solo (ver _detectar_puerto_pedal).
# MESA_PEDAL_PORT="COM5" fuerza uno a mano; MESA_PEDAL_PORT="off" apaga el pedal.
PEDAL_PORT = os.environ.get("MESA_PEDAL_PORT", "").strip()
PEDAL_BAUD = int(os.environ.get("MESA_PEDAL_BAUD", "115200"))

# Chips USB-serial que usan los Arduino Nano (oficiales y clones). Se filtra por
# VID y no por el número de COM porque el número no es estable: Windows se lo
# asigna por puerto USB físico, así que cambiar de agujero cambia el COM y
# cualquier valor fijo deja de servir. El VID viaja con la placa.
#
# Se leen los METADATOS del sistema (list_ports), nunca se abre el puerto para
# "probar" si es el pedal: abrir un puerto serial sobre un Arduino lo resetea
# por DTR, así que sondear a ciegas reiniciaría cualquier otra placa enchufada.
PEDAL_VIDS = {
    0x2341: "Arduino oficial",
    0x2A03: "Arduino (arduino.org)",
    0x1A86: "CH340 (clon de Nano)",
    0x0403: "FTDI (clon de Nano)",
    0x10C4: "CP210x",
}

PEDAL_CANAL_A_STEM = {
    "guitarra": "guitar",
}

PEDAL_CLIENTES = []  # una queue.Queue por navegador conectado al SSE
PEDAL_CLIENTES_LOCK = threading.Lock()

# Para que la interfaz pueda saber si el pedal está enchufado sin mirar la
# consola (que con la ventana de pywebview no se ve).
PEDAL_ESTADO = {"conectado": False, "puerto": None}


def _puertos_candidatos():
    """Puertos serie que parecen un Arduino, más probable primero. Devuelve
    [(device, descripcion, es_probable)]. Si falta pyserial devuelve []."""
    try:
        from serial.tools import list_ports
    except ImportError:
        return []
    candidatos = []
    for p in list_ports.comports():
        desc = (p.description or p.device or "").strip()
        nombre_chip = PEDAL_VIDS.get(p.vid)
        # los COM de Bluetooth aparecen como puertos serie y nunca son el pedal
        es_bt = "bluetooth" in desc.lower()
        if es_bt:
            continue
        candidatos.append((p.device, f"{desc} [{nombre_chip}]" if nombre_chip else desc,
                           nombre_chip is not None))
    # orden natural: "COM11" después de "COM6", no antes (comparando como
    # texto, "1" < "6" y quedaba al revés)
    def _orden(c):
        m_num = re.search(r"(\d+)$", c[0])
        return (not c[2], int(m_num.group(1)) if m_num else 9999, c[0])
    candidatos.sort(key=_orden)
    return candidatos


def _detectar_puerto_pedal():
    """El puerto del pedal, o None. Solo devuelve algo si reconoce el chip: no
    conviene engancharse al primer COM que aparezca (podría ser otro aparato) y
    conectarse ahí lo resetearía."""
    probables = [c for c in _puertos_candidatos() if c[2]]
    if not probables:
        return None
    if len(probables) > 1:
        otros = ", ".join(f"{d} ({desc})" for d, desc, _ in probables[1:])
        print(f"[pedal] hay más de una placa enchufada; uso {probables[0][0]}. "
              f"Las otras: {otros}. Si elegí mal, fijá la buena con MESA_PEDAL_PORT.")
    return probables[0][0]


def _puerto_sigue_existiendo(puerto):
    return any(d == puerto for d, _, _ in _puertos_candidatos())


def _pedal_emitir(datos: dict):
    payload = json.dumps(datos)
    with PEDAL_CLIENTES_LOCK:
        muertas = []
        for q in PEDAL_CLIENTES:
            try:
                q.put_nowait(payload)
            except Exception:  # noqa: BLE001
                muertas.append(q)
        for q in muertas:
            PEDAL_CLIENTES.remove(q)


def _pedal_fijar_estado(conectado, puerto):
    """Anota el estado y lo avisa a los navegadores. Solo emite cuando algo
    cambió, para no spamear el SSE una vez por segundo."""
    if PEDAL_ESTADO["conectado"] == conectado and PEDAL_ESTADO["puerto"] == puerto:
        return
    PEDAL_ESTADO["conectado"], PEDAL_ESTADO["puerto"] = conectado, puerto
    _pedal_emitir({"tipo": "pedal_estado", "conectado": conectado, "puerto": puerto})


def _pedal_procesar_linea(linea: str):
    """Traduce una línea del Arduino a un evento para los navegadores."""
    if linea in ("VOL_UP", "VOL_DOWN"):
        _pedal_emitir({"tipo": "vol", "direccion": "up" if linea == "VOL_UP" else "down"})
        return
    if linea == "PLAY_PAUSE":
        _pedal_emitir({"tipo": "play_pausa"})
        return
    if ":" not in linea:
        return
    accion, canal = linea.split(":", 1)
    accion = accion.strip().upper()
    stem = PEDAL_CANAL_A_STEM.get(canal.strip().lower())
    if stem and accion in ("MUTE", "UNMUTE"):
        _pedal_emitir({"tipo": "mute", "stem": stem, "accion": accion.lower()})


def _iniciar_pedal_serial():
    """Busca el pedal solo y se reconecta si lo enchufás o desenchufás con la
    app abierta. Si falta pyserial, si no hay ninguna placa, o si el puerto no
    abre, la app sigue funcionando igual -- el pedal es un accesorio y nunca
    debe poder romper el arranque ni el resto de Mesa."""
    if PEDAL_PORT.lower() == "off":
        print("[pedal] desactivado por MESA_PEDAL_PORT=off.")
        return
    try:
        import serial
    except ImportError:
        print("[pedal] falta pyserial (pip install pyserial): sigo sin el pedal físico.")
        return

    def _correr():
        aviso_sin_pedal = False
        while True:
            # El puerto se resuelve en CADA vuelta, no una sola vez al arrancar:
            # así enchufar el pedal con Mesa ya abierta lo engancha solo, y
            # cambiarlo de puerto USB (que le cambia el número de COM) tampoco
            # obliga a reiniciar nada.
            puerto = PEDAL_PORT or _detectar_puerto_pedal()
            if not puerto:
                _pedal_fijar_estado(False, None)
                if not aviso_sin_pedal:
                    print("[pedal] no encuentro ninguna placa. Enchufala y la tomo sola "
                          "(o fijá el puerto con MESA_PEDAL_PORT=COM5).")
                    aviso_sin_pedal = True
                time.sleep(3)
                continue
            aviso_sin_pedal = False

            try:
                with serial.Serial(puerto, PEDAL_BAUD, timeout=1) as ser:
                    print(f"[pedal] conectado en {puerto}")
                    _pedal_fijar_estado(True, puerto)
                    vueltas_sin_datos = 0
                    while True:
                        cruda = ser.readline()
                        if not cruda:
                            # timeout sin datos: es lo normal entre pisadas. Cada
                            # tanto confirmamos que el puerto siga ahí, porque al
                            # desenchufar el Nano, Windows no siempre tira error:
                            # a veces readline() simplemente deja de devolver nada
                            # y el hilo quedaría esperando para siempre.
                            vueltas_sin_datos += 1
                            if vueltas_sin_datos >= 3 and not PEDAL_PORT:
                                vueltas_sin_datos = 0
                                if not _puerto_sigue_existiendo(puerto):
                                    print(f"[pedal] se desenchufó de {puerto}.")
                                    break
                            continue
                        vueltas_sin_datos = 0
                        linea = cruda.decode("utf-8", errors="ignore").strip()
                        if linea:
                            _pedal_procesar_linea(linea)
            except Exception as exc:  # noqa: BLE001
                print(f"[pedal] {exc} -- reintento en 3s.")
                time.sleep(3)
            _pedal_fijar_estado(False, None)

    threading.Thread(target=_correr, daemon=True).start()


# Cada cuánto se manda un comentario SSE si no hubo eventos del pedal. No es
# para mantener viva la conexión (nada la corta acá), sino al revés: sin
# escribir NADA al socket, el servidor nunca se entera de que el navegador se
# fue. Un generador bloqueado para siempre en q.get() no escribe, así que el
# hilo y la cola quedaban colgados por cada recarga o cambio de canción del
# setlist, y cada evento del pedal se seguía encolando en clientes fantasma.
# Con esto, el primer keepalive después de que el navegador se va explota con
# un error de escritura, corre el finally y se limpia el cliente.
PEDAL_KEEPALIVE_SEG = 15
# Tope por cliente: si igual quedara uno trabado, deja de crecer sin control y
# _pedal_emitir lo descarta solo (put_nowait tira queue.Full).
PEDAL_COLA_MAX = 200


@app.route("/pedal/eventos")
def pedal_eventos():
    """SSE: cada navegador conectado recibe en vivo los mute/unmute del pedal."""
    q = queue.Queue(maxsize=PEDAL_COLA_MAX)
    with PEDAL_CLIENTES_LOCK:
        PEDAL_CLIENTES.append(q)

    def _generar():
        try:
            yield f"retry: 3000\n\n"
            # estado actual apenas se conecta: una página recién abierta tiene
            # que saber si el pedal está enchufado sin esperar a que cambie algo
            yield "data: " + json.dumps({"tipo": "pedal_estado", **PEDAL_ESTADO}) + "\n\n"
            while True:
                try:
                    payload = q.get(timeout=PEDAL_KEEPALIVE_SEG)
                except queue.Empty:
                    yield ": keepalive\n\n"   # comentario SSE: el navegador lo ignora
                    continue
                yield f"data: {payload}\n\n"
        finally:
            with PEDAL_CLIENTES_LOCK:
                if q in PEDAL_CLIENTES:
                    PEDAL_CLIENTES.remove(q)

    return Response(_generar(), mimetype="text/event-stream",
                    headers={"Cache-Control": "no-cache", "X-Accel-Buffering": "no"})


def _avisar_si_vence_pronto(ruta_cert, dias_aviso=14):
    """Chequeo puramente informativo al arrancar. Si falta la librería
    "cryptography" o falla la lectura por lo que sea, no dice nada y sigue
    -- nunca vale la pena romper el arranque por un aviso."""
    try:
        from cryptography import x509
        datos = ruta_cert.read_bytes()
        cert = x509.load_pem_x509_certificate(datos)
        vence = getattr(cert, "not_valid_after_utc", None) or cert.not_valid_after.replace(tzinfo=timezone.utc)
        faltan = (vence - datetime.now(timezone.utc)).days
        if faltan <= dias_aviso:
            print(f"[https] atención: el certificado vence en {faltan} día(s) ({vence:%Y-%m-%d}). "
                  f"Renovalo con: tailscale cert {TLS_CERT.stem}")
    except Exception:  # noqa: BLE001
        pass


def _iniciar_https_directo():
    """Segundo servidor Flask en 0.0.0.0:443 con TLS terminado acá (no por
    tailscale serve). Cualquier falla acá (archivos ausentes, certificado
    vencido/corrupto, puerto ocupado) se avisa por consola y no arranca este
    hilo -- el servidor de siempre en el puerto 5000 sigue funcionando igual,
    nunca se cae la app entera por esto."""
    if not TLS_CERT.exists() or not TLS_KEY.exists():
        print(f"[https] no encontré {TLS_CERT.name} / {TLS_KEY.name}: sigo solo con el puerto 5000 (http).")
        return
    try:
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        ctx.load_cert_chain(str(TLS_CERT), str(TLS_KEY))
    except Exception as exc:  # noqa: BLE001
        print(f"[https] no pude cargar el certificado ({exc}): sigo solo con el puerto 5000 (http).")
        return

    _avisar_si_vence_pronto(TLS_CERT)

    def _correr():
        try:
            app.run(host="0.0.0.0", port=443, debug=False, use_reloader=False, threaded=True, ssl_context=ctx)
        except OSError as exc:
            print(f"[https] no pude escuchar en el puerto 443 ({exc}).")
            print('       ¿"tailscale serve" sigue prendido? Apagalo con: tailscale serve --https=443 off')

    threading.Thread(target=_correr, daemon=True).start()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--browser", action="store_true",
        help="Correr como servidor normal (pestaña de navegador) en vez de ventana nativa",
    )
    args = parser.parse_args()

    hilo_flask = threading.Thread(
        target=lambda: app.run(host="0.0.0.0", port=5000, debug=False, use_reloader=False, threaded=True),
        daemon=True,
    )
    hilo_flask.start()
    servidor_listo = _esperar_servidor()
    _iniciar_https_directo()
    _iniciar_pedal_serial()

    if PEDAL_PORT.lower() != "off":
        candidatos = _puertos_candidatos()
        probables = [c for c in candidatos if c[2]]
        if PEDAL_PORT:
            print(f"Pedal: puerto fijado a mano en {PEDAL_PORT} (MESA_PEDAL_PORT).")
        elif probables:
            print(f"Pedal: detectado en {probables[0][0]} — {probables[0][1]}")
        elif candidatos:
            otros = ", ".join(f"{d} ({desc})" for d, desc, _ in candidatos[:4])
            print("Pedal: no reconocí ninguna placa Arduino. Puertos serie que hay: " + otros)
            print("       Si el pedal es uno de esos, fijalo con: set MESA_PEDAL_PORT=COMx")
        else:
            print("Pedal: no hay ningún puerto serie. Enchufalo y lo tomo solo, sin reiniciar.")

    ip = _ip_local()
    if ip:
        print(f"Desde otro dispositivo en el mismo WiFi (ej. una tablet): http://{ip}:5000")
        print("(la primera vez, Windows va a preguntar si permite la conexión — elegí 'red privada')")
    print("Para instalarlo como app en la tablet hace falta HTTPS. Con Tailscale, sin 'serve':")
    print(f"    tailscale cert {TLS_CERT.stem}   (una sola vez, o cuando avise que vence)")
    print("    tailscale serve --https=443 off   (para que el 443 quede libre para esta app)")
    print(f"y abrí en la tablet https://{TLS_CERT.stem} — el mismo puerto 443 de siempre.")

    if args.browser or not servidor_listo:
        if not servidor_listo:
            print("No pude confirmar que el servidor arrancó a tiempo, sigo igual por las dudas.")
        print(f"Modelo Demucs: {MODEL}")
        print("Abrí http://127.0.0.1:5000")
        hilo_flask.join()
    else:
        import webview

        ruta_icono = BASE_DIR / "mesa.ico"

        def _aplicar_icono_windows():
            """pywebview no puede fijar el icono en Windows (solo GTK/QT), así que
            se lo mandamos a la ventana con la API de Windows una vez creada."""
            if not sys.platform.startswith("win") or not ruta_icono.exists():
                return
            try:
                import ctypes
                user32 = ctypes.windll.user32
                IMAGE_ICON, LR_LOADFROMFILE, LR_DEFAULTSIZE = 1, 0x0010, 0x0040
                WM_SETICON, ICON_SMALL, ICON_BIG = 0x0080, 0, 1

                hwnd = user32.FindWindowW(None, TITULO_VENTANA)
                if not hwnd:
                    return
                grande = user32.LoadImageW(None, str(ruta_icono), IMAGE_ICON, 32, 32, LR_LOADFROMFILE)
                chico = user32.LoadImageW(None, str(ruta_icono), IMAGE_ICON, 16, 16, LR_LOADFROMFILE)
                if grande:
                    user32.SendMessageW(hwnd, WM_SETICON, ICON_BIG, grande)
                if chico:
                    user32.SendMessageW(hwnd, WM_SETICON, ICON_SMALL, chico)
            except Exception:  # noqa: BLE001
                pass  # el icono es cosmético: si falla, la app sigue igual

        # hace que Windows trate la app como propia y no como "Python" en la
        # barra de tareas (si no, hereda el icono de python.exe)
        if sys.platform.startswith("win"):
            try:
                import ctypes
                ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("SIC.Mesa.SeparadorDePistas")
            except Exception:  # noqa: BLE001
                pass

        webview.settings["ALLOW_DOWNLOADS"] = True  # sin esto, "Exportar mp3" no hace nada
        # La ventana abre maximizada. pywebview acepta maximized=True desde la 4.x; si la
        # versión instalada no lo conoce, se crea normal y se maximiza con la API de Windows
        # apenas aparece. Al restaurarla (botón del medio) vuelve a 880x820.
        maximizar_a_mano = False
        try:
            ventana = webview.create_window(
                TITULO_VENTANA,
                "http://127.0.0.1:5000",
                width=880, height=820, min_size=(700, 600), maximized=True,
            )
        except TypeError:
            maximizar_a_mano = True
            ventana = webview.create_window(
                TITULO_VENTANA,
                "http://127.0.0.1:5000",
                width=880, height=820, min_size=(700, 600),
            )

        def _maximizar_windows():
            if not sys.platform.startswith("win"):
                return
            try:
                import ctypes
                hwnd = ctypes.windll.user32.FindWindowW(None, TITULO_VENTANA)
                if hwnd:
                    ctypes.windll.user32.ShowWindow(hwnd, 3)  # SW_MAXIMIZE
            except Exception:  # noqa: BLE001
                pass  # cosmético: si falla, la ventana queda en su tamaño normal

        # se aplica cuando la ventana ya existe; se reintenta un par de veces por
        # si el handle todavía no está listo
        def _al_mostrar():
            if maximizar_a_mano:
                _maximizar_windows()
            for _ in range(10):
                _aplicar_icono_windows()
                time.sleep(0.2)
        try:
            ventana.events.shown += lambda: threading.Thread(target=_al_mostrar, daemon=True).start()
        except Exception:  # noqa: BLE001
            threading.Thread(target=_al_mostrar, daemon=True).start()

        webview.start()
