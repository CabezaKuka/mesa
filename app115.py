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
import shutil
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
from urllib.parse import urlparse

import numpy as np
from numpy.lib.stride_tricks import sliding_window_view
from flask import Flask, Response, jsonify, redirect, render_template, request, send_file, send_from_directory, url_for
from werkzeug.utils import secure_filename

BASE_DIR = Path(__file__).resolve().parent
# v115: el HTML, CSS y JS de cada pantalla viven en templates/ (antes eran ~8.000
# líneas de strings dentro de este archivo). Se leen una vez al arrancar.
PLANTILLAS_DIR = BASE_DIR / "templates"


def _plantilla(nombre: str) -> str:
    return (PLANTILLAS_DIR / nombre).read_text(encoding="utf-8")
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
#   1) tailscale cert <tu-maquina>.<tu-tailnet>.ts.net   (genera los dos archivos)
#   2) tailscale serve --https=443 off                    (si no, pelean por el 443)
#
# Los certificados de Tailscale duran ~90 días: cuando el aviso de "vence
# pronto" empiece a aparecer al arrancar, repetí el paso 1 (sobreescribe los
# mismos archivos, no hace falta tocar nada más acá).
#
# v115: el certificado se busca solo. Antes la ruta por defecto tenía escrito a mano el
# nombre de UNA máquina; ahora vale MESA_TLS_CERT / MESA_TLS_KEY si están, y si no, el
# primer *.ts.net.crt (con su .key al lado) junto a Mesa o en C:\Windows\System32, que es
# donde lo deja "tailscale cert" corrido desde una consola de administrador.
_LUGARES_CERTIFICADO = [BASE_DIR, Path(r"C:\Windows\System32")]


def _buscar_certificado():
    cert, key = os.environ.get("MESA_TLS_CERT"), os.environ.get("MESA_TLS_KEY")
    if cert and key:
        return Path(cert), Path(key)
    for lugar in _LUGARES_CERTIFICADO:
        try:
            candidatos = sorted(lugar.glob("*.ts.net.crt"))
        except OSError:
            continue
        for crt in candidatos:
            clave = crt.with_suffix(".key")
            if clave.exists():
                return crt, clave
    return None, None


def _host_certificado(ruta):
    """Nombre del host (maquina.tailnet.ts.net) sacado del archivo, también con rutas de Windows."""
    nombre = str(ruta).replace("\\", "/").rsplit("/", 1)[-1]
    return nombre[:-4] if nombre.endswith(".crt") else nombre


TLS_CERT, TLS_KEY = _buscar_certificado()
UPLOAD_DIR = BASE_DIR / "uploads"
OUTPUT_DIR = BASE_DIR / "separated"
MODEL = "htdemucs_6s"  # separa: vocals, drums, bass, guitar, piano, other
TITULO_VENTANA = "Mesa — separador de pistas"

UPLOAD_DIR.mkdir(exist_ok=True)
OUTPUT_DIR.mkdir(exist_ok=True)

app = Flask(__name__, template_folder=str(PLANTILLAS_DIR))

# v115: cada pantalla se compila UNA vez (la de la mesa tardaba ~60 ms en compilarse en
# cada carga). Mismo resultado que render_template_string: pasa por los context
# processors de siempre. La clave es el string mismo (son constantes del módulo).
_COMPILADAS = {}


def _render_pagina(fuente, **contexto):
    plantilla = _COMPILADAS.get(id(fuente))
    if plantilla is None or plantilla[0] is not fuente:
        plantilla = (fuente, app.jinja_env.from_string(fuente))
        _COMPILADAS[id(fuente)] = plantilla
    return render_template(plantilla[1], **contexto)


@app.errorhandler(ValueError)
def _error_nombre_invalido(exc):
    return jsonify({"error": str(exc)}), 400


# v115: Mesa escucha en la red y no tiene usuarios, así que cualquier página de internet
# abierta en la PC podía mandarle un POST (por ejemplo a /borrar/<tema>): los formularios
# entre sitios no piden permiso. Los pedidos legítimos salen de las páginas de la propia
# Mesa, y el navegador dice de dónde viene cada uno en "Origin": si no coincide con el
# host al que se le habla, se rechaza. Sin Origin (curl, scripts locales) pasa como antes.
@app.before_request
def _rechazar_otro_origen():
    if request.method in ("GET", "HEAD", "OPTIONS"):
        return None
    origen = request.headers.get("Origin")
    if not origen:
        return None
    if urlparse(origen).netloc.lower() != (request.host or "").lower():
        return jsonify({"error": "pedido rechazado: viene de otro sitio"}), 403
    return None


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


# v115: un compás es "dudoso" si en algún tiempo con acorde el detector estuvo por debajo
# de esta confianza (el mismo valor usa el editor para marcarlos)
UMBRAL_DUDOSO = 0.6


def tonalidad_de_acordes(segmentos):
    """Tonalidad estimada a partir de los acordes ya guardados (no del audio): cada acorde
    suma sus notas por lo que dura. Devuelve ("Am", "A menor") o (None, None)."""
    chroma = np.zeros(12)
    for seg in segmentos:
        rs = _raiz_y_sufijo(seg.get("acorde"))
        if not rs:
            continue
        dur = max(0.0, float(seg["fin"]) - float(seg["inicio"]))
        for k, iv in enumerate(SUFIJOS_VALIDOS.get(rs[1], [])):
            chroma[(rs[0] + iv) % 12] += dur * (1.5 if k == 0 else 1.0)
    t = estimar_tonalidad(chroma)
    if not t:
        return None, None
    nombre = NOTE_NAMES[t[0]]
    return (nombre, f"{nombre} mayor") if t[1] == "mayor" else (nombre + "m", f"{nombre} menor")


def info_cancion(song: str):
    """v115: datos chicos para la lista de la portada, sacados de lo que ya está guardado
    (no dispara ningún análisis): BPM, tonalidad, de dónde salieron los acordes y cuántos
    compases dudosos quedan por revisar."""
    info = {"bpm": None, "tonalidad": None, "tonalidad_larga": None, "origen": None, "dudosos": 0}
    carpeta = stems_dir(song)
    try:
        grid = json.loads((carpeta / "acordes_grid.json").read_text(encoding="utf-8"))
        tokens = _texto_a_tokens((carpeta / "acordes.txt").read_text(encoding="utf-8"))
    except (OSError, ValueError, TypeError):
        return info
    try:
        info["bpm"] = int(round(float(grid.get("bpm")))) if grid.get("bpm") else None
    except (TypeError, ValueError):
        pass
    info["origen"] = "midi" if grid.get("origen") == "midi" else "detector"
    base = grid.get("beat_times") or []
    try:
        segmentos = _tokens_a_segmentos(tokens, base, grid.get("duracion", 0))
        info["tonalidad"], info["tonalidad_larga"] = tonalidad_de_acordes(segmentos)
    except Exception:  # noqa: BLE001
        pass
    conf = _leer_confianza(carpeta, base, grid)
    if conf:
        bpc = grid.get("beats_por_compas", 4) or 4
        c = conf["confianza"]
        for i in range(0, min(len(c), len(tokens)), bpc):
            valores = [c[j] for j in range(i, min(i + bpc, len(c), len(tokens))) if tokens[j] != "—"]
            if valores and min(valores) < UMBRAL_DUDOSO:
                info["dudosos"] += 1
    return info


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
# Reparto del 100 %: separación 0–90 %, armado de los mp3 livianos 90–96 %, y (v115)
# detección de acordes y pulso 96–100 %, así el tema ya abre con los acordes listos.
_RE_PCT_DEMUCS = re.compile(r"(\d{1,3})%\|")
_RE_BAG_DEMUCS = re.compile(r"bag of (\d+) models")
_PCT_SEPARACION = 90.0
_PCT_MP3 = 96.0


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
                restante = ritmo * (1.0 - frac) + 0.12 * ritmo   # + los mp3 y los acordes
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
                    job["progreso"] = round(_PCT_SEPARACION + (_PCT_MP3 - _PCT_SEPARACION) * hechos / len(STEM_ORDER), 1)
                    por_stem = (time.time() - t_mp3) / hechos
                    job["estimado"] = round(time.time() - job["started"] + por_stem * (len(STEM_ORDER) - hechos))
                # v115: acordes y pulso ahora, no al abrir el tema. Si falla, no es grave:
                # se reintenta solo la primera vez que se abra.
                job["etapa"] = "acordes"
                job["progreso"] = _PCT_MP3
                if not (carpeta / "acordes.txt").exists():
                    try:
                        _generar_grilla(carpeta)
                    except Exception as exc:  # noqa: BLE001
                        print(f"[mesa] no pude analizar los acordes de {carpeta.name} ({exc}); se intenta al abrirlo")
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


def _duracion_wav(path):
    """Duración en segundos leyendo solo el encabezado (v115: antes se cargaba el wav entero,
    ~40 MB en un tema de 4 minutos, solo para esto)."""
    with wave.open(str(path), "rb") as wf:
        return wf.getnframes() / float(wf.getframerate())


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


_MARCOS_POR_TANDA = 256


def _proyectar_notas(data, sr, frame_len=8192, hop=4096, midi_min=40, midi_max=91, cents=0.0):
    """Magnitud por marco de cada nota MIDI midi_min..midi_max: proyección de cada marco (con
    ventana de Hann) sobre la frecuencia exacta de la nota.

    v115: coseno y seno por separado, en float32 y de a tandas. Antes se multiplicaba por la
    base compleja y numpy pasaba TODOS los marcos a complex128 antes del producto: mismo
    resultado (diferencia relativa ~1e-7), pero en un tema de 4 minutos tardaba 1,75 s y
    pedía 432 MB por stem; así son 0,06 s y unos pocos MB."""
    if len(data) < frame_len:
        data = np.pad(data, (0, frame_len - len(data)))
    vista = sliding_window_view(np.asarray(data, dtype=np.float32), frame_len)[::hop]
    base, pitch_class = _matriz_basis(frame_len, sr, midi_min, midi_max, cents)
    cos_ = np.ascontiguousarray(base.real.T, dtype=np.float32)
    sin_ = np.ascontiguousarray(base.imag.T, dtype=np.float32)
    hann = np.hanning(frame_len).astype(np.float32)
    out = np.empty((vista.shape[0], len(pitch_class)), dtype=np.float64)
    for i in range(0, vista.shape[0], _MARCOS_POR_TANDA):
        marcos = vista[i:i + _MARCOS_POR_TANDA] * hann
        out[i:i + _MARCOS_POR_TANDA] = np.hypot(marcos @ cos_, marcos @ sin_)
    return out, pitch_class


def _filtros_semitono(frame_len, sr, midi_min, midi_max, cents):
    """Matriz (bins de la FFT x notas) para la variante "bandas_semitono": cada nota junta
    TODA la energía que cae a +-50 cents de ella (y se desvanece hasta +-100), en vez de
    medir una sola frecuencia exacta. En las notas graves, donde un semitono es menos de
    un bin, se toma al menos el bin más cercano y sus vecinos."""
    hz = np.arange(frame_len // 2 + 1) * sr / frame_len
    midis = np.arange(midi_min, midi_max + 1)
    centros = 440.0 * 2.0 ** ((midis - 69) / 12.0 + cents / 1200.0)
    with np.errstate(divide="ignore"):
        semitonos = 12.0 * np.log2(np.maximum(hz, 1e-9)[:, None] / centros[None, :])
    peso = np.clip(1.0 - np.maximum(0.0, np.abs(semitonos) - 0.5) / 0.5, 0.0, 1.0)
    cerca = np.abs(hz[:, None] - centros[None, :]) <= 1.0 * sr / frame_len
    peso = np.maximum(peso, cerca.astype(float))
    return peso.astype(np.float32), midis % 12


def _bandas_notas(data, sr, frame_len=8192, hop=4096, midi_min=40, midi_max=91, cents=0.0):
    """Igual que _proyectar_notas pero sumando bandas de un semitono de la FFT."""
    if len(data) < frame_len:
        data = np.pad(data, (0, frame_len - len(data)))
    vista = sliding_window_view(np.asarray(data, dtype=np.float32), frame_len)[::hop]
    filtros, pitch_class = _filtros_semitono(frame_len, sr, midi_min, midi_max, cents)
    hann = np.hanning(frame_len).astype(np.float32)
    out = np.empty((vista.shape[0], len(pitch_class)), dtype=np.float64)
    for i in range(0, vista.shape[0], _MARCOS_POR_TANDA):
        espectro = np.abs(np.fft.rfft(vista[i:i + _MARCOS_POR_TANDA] * hann, axis=1)).astype(np.float32)
        out[i:i + _MARCOS_POR_TANDA] = espectro @ filtros
    return out, pitch_class


def _mags_de_audio(data, sr, frame_len=8192, hop=4096, cents=0.0, bandas=False):
    """Magnitud por marco de las 52 notas MIDI 40-91 (antes de sumarlas por clase de altura)."""
    funcion = _bandas_notas if bandas else _proyectar_notas
    return funcion(data, sr, frame_len, hop, cents=cents)  # (n_frames, K)


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
    mags, pitch_class = _proyectar_notas(data, sr, frame_len, hop, midi_min=40, midi_max=67, cents=cents)
    chroma = np.zeros((mags.shape[0], 12))
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


def _viterbi(sim, penalizacion, costos=None):
    """Camino de acordes de máximo puntaje total con una penalización fija por cada
    cambio. Reemplaza al argmax marco a marco + moda de 5 marcos: en vez de decidir
    cada marco por separado, decide la secuencia entera, así un acorde que suena
    durante varios compases no se rompe por unos marcos dudosos.

    v115: con `costos` (matriz K x K, diagonal en 0) cada cambio cuesta según el par de
    acordes en vez de una penalización fija (variante "transiciones")."""
    T, K = sim.shape
    ptr = np.zeros((T, K), dtype=np.int32)
    ar = np.arange(K)
    score = sim[0].copy()
    if costos is None:
        for t in range(1, T):
            j = int(score.argmax())
            salto = score[j] - penalizacion
            quedarse = score >= salto
            ptr[t] = np.where(quedarse, ar, j)
            score = np.where(quedarse, score, salto) + sim[t]
    else:
        for t in range(1, T):
            candidatos = score[:, None] - costos      # [desde, hacia]
            desde = candidatos.argmax(axis=0)
            ptr[t] = desde
            score = candidatos[desde, ar] + sim[t]
    camino = np.empty(T, dtype=np.int32)
    k = int(score.argmax())
    for t in range(T - 1, -1, -1):
        camino[t] = k
        k = ptr[t, k]
    return camino


# --------------------------------------- v115: variantes del detector por plantillas ----
# Ideas para mejorar la precisión, TODAS APAGADAS por defecto: con ninguna prendida el
# detector da exactamente lo mismo que app114. No se pueden elegir a ciegas (lo que mejora
# un tema empeora otro), así que se miden contra los MIDI importados con "Medir mejoras"
# en Ajustes generales, y ahí mismo se prenden las que ganan (prefs "detector_variantes").
VARIANTES_DETECTOR = {
    "por_tiempo": "Cambios de acorde solo en los tiempos del pulso",
    "tonalidad": "Preferir los acordes de la tonalidad del tema",
    "bajo_inversiones": "Contar el bajo en la 3ª o la 5ª (inversiones)",
    "silencio_percentil": "Umbral de silencio que ignora los picos sueltos",
    "bandas_semitono": "Medir cada nota en una banda de un semitono",
    "transiciones": "Transiciones entre acordes aprendidas de tus MIDI",
}
# tonalidad: bonus a los acordes diatónicos (escala de la similitud coseno, ~0,5-0,95)
PESO_TONALIDAD = 0.06
# bajo_inversiones: bonus si el bajo toca la 3ª o la 5ª (la raíz sigue pesando PESO_BAJO)
PESO_BAJO_INVERSION = 0.15
# silencio_percentil: el umbral es UMBRAL_SILENCIO de este percentil de la energía, en vez
# del máximo (un golpe aislado muy fuerte subía el umbral y una intro tranquila salía "—")
PERCENTIL_SILENCIO = 98
# transiciones: cuánto se aparta el costo de un cambio de la penalización fija, por cada
# unidad de log-probabilidad (con transiciones equiprobables queda la penalización fija)
PESO_TRANSICIONES = 0.15
TRANSICIONES_PATH = BASE_DIR / "transiciones_acordes.json"

# perfiles de Krumhansl-Kessler para estimar la tonalidad a partir del chroma total
_PERFIL_MAYOR = np.array([6.35, 2.23, 3.48, 2.33, 4.38, 4.09, 2.52, 5.19, 2.39, 3.66, 2.29, 2.88])
_PERFIL_MENOR = np.array([6.33, 2.68, 3.52, 5.38, 2.60, 3.53, 2.54, 4.75, 3.98, 2.69, 3.34, 3.17])


def estimar_tonalidad(chroma_total):
    """(tónica, "mayor" | "menor", correlación) o None si no hay nada que medir."""
    c = np.asarray(chroma_total, dtype=float)
    if c.size != 12 or c.sum() <= 0 or np.allclose(c, c[0]):
        return None
    mejor = None
    for t in range(12):
        for modo, perfil in (("mayor", _PERFIL_MAYOR), ("menor", _PERFIL_MENOR)):
            r = float(np.corrcoef(c, np.roll(perfil, t))[0, 1])
            if mejor is None or r > mejor[2]:
                mejor = (t, modo, r)
    return mejor


def acordes_diatonicos(tonica, modo):
    """Acordes de la tonalidad: los seis de la escala mayor (o de su relativa), el V7 y el
    III/III7 (la dominante del relativo menor: E/E7 en C mayor o en A menor)."""
    mayor = tonica if modo == "mayor" else (tonica + 3) % 12
    grados = [(0, ""), (2, "m"), (4, "m"), (5, ""), (7, ""), (9, "m"), (7, "7"), (4, ""), (4, "7")]
    return {NOTE_NAMES[(mayor + iv) % 12] + suf for iv, suf in grados}


def _sufijo_de_nombre(nombre: str) -> str:
    return nombre[len(NOTE_NAMES[_raiz_de_nombre(nombre)]):]


def _bonus_bajo(chroma_bajo, nombres, peso_bajo, peso_inversion=0.0):
    """Puntaje extra según la nota que toca el bajo: peso_bajo si es la raíz del acorde y,
    con la variante de inversiones, peso_inversion si es la 3ª o la 5ª."""
    raices = np.array([_raiz_de_nombre(n) for n in nombres])
    bonus = peso_bajo * chroma_bajo[:, raices]
    if peso_inversion:
        otras = np.zeros((len(nombres), 12))
        for j, n in enumerate(nombres):
            for iv in SUFIJOS_VALIDOS[_sufijo_de_nombre(n)][1:3]:
                otras[j, (raices[j] + iv) % 12] = 1.0
        bonus = bonus + peso_inversion * (chroma_bajo[:, None, :] * otras[None, :, :]).max(axis=2)
    return bonus


def conteos_transiciones(segmentos):
    """Cambios de acorde de una referencia, relativos a la raíz (no dependen de la tonalidad):
    {"intervalo,calidad_desde,calidad_hacia": veces}. Calidades: 0 mayor, 1 menor, 2 séptima."""
    clases = [ml_nombre_a_clase(s["acorde"]) for s in sorted(segmentos, key=lambda s: s["inicio"])]
    clases = [c for c in clases if 0 <= c < ML_CLASE_N]
    conteos = {}
    for a, b in zip(clases, clases[1:]):
        if a == b:
            continue
        clave = f"{(b // 3 - a // 3) % 12},{a % 3},{b % 3}"
        conteos[clave] = conteos.get(clave, 0) + 1
    return conteos


def costos_transicion(conteos, nombres, penalizacion, peso=PESO_TRANSICIONES):
    """Matriz K x K de costos para _viterbi. Probabilidad de cada destino con suavizado de
    Laplace sobre los 35 cambios posibles; un cambio equiprobable cuesta la penalización
    fija, uno frecuente menos (nunca menos de un cuarto) y uno raro más."""
    clases = [ml_nombre_a_clase(n) for n in nombres]
    totales = {}
    for clave, n in conteos.items():
        q = int(clave.split(",")[1])
        totales[q] = totales.get(q, 0) + n
    K = len(nombres)
    costos = np.zeros((K, K))
    log_uniforme = np.log(35.0)
    for i, a in enumerate(clases):
        for j, b in enumerate(clases):
            if i == j:
                continue
            if not (0 <= a < ML_CLASE_N and 0 <= b < ML_CLASE_N):
                costos[i, j] = penalizacion
                continue
            n = conteos.get(f"{(b // 3 - a // 3) % 12},{a % 3},{b % 3}", 0)
            p = (n + 1.0) / (totales.get(a % 3, 0) + 35.0)
            costos[i, j] = max(0.25 * penalizacion, penalizacion + peso * (-np.log(p) - log_uniforme))
    return costos


def leer_transiciones():
    try:
        return json.loads(TRANSICIONES_PATH.read_text(encoding="utf-8")).get("conteos") or None
    except (OSError, json.JSONDecodeError):
        return None


def _armar_segmentos(etiquetas, inicios, fin_ultimo, min_duracion):
    """Etiquetas consecutivas -> [{"inicio", "fin", "acorde"}], fusionando con el anterior los
    tramos más cortos que min_duracion (ruido). `inicios` es el instante de cada etiqueta;
    el primer tramo arranca siempre en 0."""
    n = len(etiquetas)
    segmentos = []
    actual, inicio = etiquetas[0], 0.0
    for i in range(1, n):
        if etiquetas[i] != actual:
            segmentos.append({"inicio": round(float(inicio), 2), "fin": round(float(inicios[i]), 2), "acorde": actual})
            actual, inicio = etiquetas[i], inicios[i]
    segmentos.append({"inicio": round(float(inicio), 2), "fin": round(float(fin_ultimo), 2), "acorde": actual})

    fusionado = [segmentos[0]]
    for seg in segmentos[1:]:
        if seg["fin"] - seg["inicio"] < min_duracion:
            fusionado[-1]["fin"] = seg["fin"]
        elif fusionado[-1]["acorde"] == seg["acorde"]:
            fusionado[-1]["fin"] = seg["fin"]
        else:
            fusionado.append(seg)
    return fusionado


def _agrupar_por_tiempo(tiempos, bordes):
    """Índice del tiempo (intervalo entre bordes) donde cae cada marco, y los intervalos
    que tienen al menos un marco."""
    grupo = np.searchsorted(np.asarray(bordes, dtype=float), tiempos, side="right") - 1
    grupo = np.clip(grupo, 0, len(bordes) - 1)
    usados = np.unique(grupo)
    return np.searchsorted(usados, grupo), usados


def _decodificar(puntajes, nombres, tiempos, hop_seg, energia, penalizacion, umbral_rel, min_duracion,
                 beat_times=None, costos=None, percentil_silencio=None, moda=False):
    """Puntajes por marco (similitud o log-probabilidad, T x K) -> segmentos. Es el mismo
    armado para los dos detectores: secuencia por Viterbi, silencio por energía, fusión de
    tramos cortos. Con beat_times (variante "por_tiempo") los cambios solo pueden caer en
    un tiempo: se suman los puntajes de los marcos de cada tiempo y Viterbi decide sobre
    tiempos en vez de marcos (la penalización por cambio vale lo mismo en las dos escalas)."""
    e = np.asarray(energia, dtype=float)
    if percentil_silencio and e.size:
        ref = float(np.percentile(e, percentil_silencio))
    else:
        ref = float(e.max()) if e.size else 0.0
    umbral = ref * umbral_rel if ref > 0 else 0.0
    fin_total = float(tiempos[-1]) + hop_seg

    if beat_times is not None and len(beat_times) >= 2:
        bordes = [0.0] + [float(b) for b in beat_times if 0.0 < float(b) < fin_total]
        pos, usados = _agrupar_por_tiempo(tiempos, bordes)
        S = np.zeros((len(usados), puntajes.shape[1]))
        np.add.at(S, pos, puntajes)
        cuantos = np.bincount(pos, minlength=len(usados))
        e_media = np.bincount(pos, weights=e, minlength=len(usados)) / np.maximum(1, cuantos)
        idx = _viterbi(S, penalizacion, costos) if (penalizacion or costos is not None) else S.argmax(axis=1)
        etiquetas = ["—" if en < umbral else nombres[i] for i, en in zip(idx, e_media)]
        inicios = [bordes[g] for g in usados]
        return _armar_segmentos(etiquetas, inicios, fin_total, 0.0)

    idx = _viterbi(puntajes, penalizacion, costos) if (penalizacion or costos is not None) else np.argmax(puntajes, axis=1)
    etiquetas = [nombres[i] for i in idx]
    etiquetas = ["—" if en < umbral else et for et, en in zip(etiquetas, e)]

    # moda en ventana deslizante: evita que titile entre acordes en cada golpe de púa.
    # Con Viterbi ya viene suavizado, así que solo se usa en el modo anterior.
    if moda:
        n = len(etiquetas)
        suaves = list(etiquetas)
        for i in range(n):
            ini, fin = max(0, i - 2), min(n, i + 3)
            ventana = etiquetas[ini:fin]
            suaves[i] = max(set(ventana), key=ventana.count)
        etiquetas = suaves
    return _armar_segmentos(etiquetas, tiempos, fin_total, min_duracion)


def _puntajes_plantillas(chromas, chroma_bajo=None, peso_bajo=PESO_BAJO, penalizacion_septima=0.0,
                         variantes=()):
    """Similitud de cada marco con cada plantilla (T x 36), con los ajustes por bajo, séptima
    y tonalidad. Devuelve (similitud, nombres)."""
    plantillas = _plantillas_acordes()
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
        similitud = similitud + _bonus_bajo(chroma_bajo, nombres, peso_bajo,
                                            PESO_BAJO_INVERSION if "bajo_inversiones" in variantes else 0.0)

    # Las séptimas se elegían de más (Em -> E7, A -> A7): el séptimo armónico de cualquier nota
    # suma energía justo donde la plantilla de séptima la espera. Se les resta un puntaje fijo,
    # así que una séptima de verdad tiene que ganar por más margen.
    if penalizacion_septima:
        similitud = similitud - penalizacion_septima * np.array([1.0 if n.endswith("7") else 0.0 for n in nombres])

    if "tonalidad" in variantes:
        tonalidad = estimar_tonalidad(chromas.sum(axis=0))
        if tonalidad:
            diatonicos = acordes_diatonicos(tonalidad[0], tonalidad[1])
            similitud = similitud + PESO_TONALIDAD * np.array([1.0 if n in diatonicos else 0.0 for n in nombres])
    return similitud, nombres


def _clasificar_frames(chromas, plantillas, chroma_bajo=None, peso_bajo=PESO_BAJO, penalizacion_cambio=0.0,
                       penalizacion_septima=0.0):
    """Acorde de cada marco (sin silencios ni segmentos). Se conserva para lab_acordes.py."""
    similitud, nombres = _puntajes_plantillas(chromas, chroma_bajo, peso_bajo, penalizacion_septima)
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


def _preparar_analisis(wav_path, bajo_path=None, stems_extra=None, frame_len=8192, hop=4096,
                       corregir_afinacion=True, bandas=False, tiempos_centrados=True):
    """Lo que comparten los dos detectores (antes estaba duplicado en detectar_acordes y en
    _features_ml): afinación del tema, magnitudes de las 52 notas sumando la guitarra y los
    stems extra, energía por marco, chroma del bajo y el instante de cada marco."""
    data, sr = _cargar_wav_mono(wav_path)
    extras = [Path(x) for x in (stems_extra or [])]

    cents = 0.0
    if corregir_afinacion:
        est, confianza = _estimar_afinacion([wav_path] + extras)
        if abs(est) >= AFINACION_MIN_CENTS and confianza >= AFINACION_MIN_CONFIANZA:
            cents = float(np.clip(round(est / 5.0) * 5, -50, 50))

    mags, pitch_class = _mags_de_audio(data, sr, frame_len, hop, cents=cents, bandas=bandas)
    for extra in extras:
        try:
            if not extra.exists():
                continue
            data2, sr2 = _cargar_wav_mono(extra)
            if sr2 != sr:
                continue
            mags2, _ = _mags_de_audio(data2, sr2, frame_len, hop, cents=cents, bandas=bandas)
            n_comun = min(mags.shape[0], mags2.shape[0])
            mags = mags[:n_comun] + mags2[:n_comun]
        except Exception:  # noqa: BLE001
            continue   # un stem extra es una ayuda, no un requisito

    # cada marco describe lo que suena alrededor de su CENTRO, no de su primera muestra
    centro = frame_len / 2 if tiempos_centrados else 0
    tiempos = (np.arange(mags.shape[0]) * hop + centro) / sr
    # la energía (para decidir silencios) se mide sin la supresión, que solo afecta qué acorde es
    energia = _mags_a_chroma(mags, pitch_class).sum(axis=1)

    chroma_bajo = None
    if bajo_path is not None and Path(bajo_path).exists():
        try:
            chroma_bajo = _chroma_del_bajo(bajo_path, frame_len, hop, mags.shape[0], cents=cents)
        except Exception:  # noqa: BLE001
            chroma_bajo = None   # el bajo es una ayuda, no un requisito
    return {"mags": mags, "pitch_class": pitch_class, "energia": energia, "chroma_bajo": chroma_bajo,
            "tiempos": tiempos, "hop_seg": hop / sr, "cents": cents}


def detectar_acordes(wav_path, frame_len=8192, hop=4096, umbral_rel=UMBRAL_SILENCIO, min_duracion=0.35,
                     bajo_path=None, stems_extra=None, penalizacion_cambio=PENALIZACION_CAMBIO,
                     penalizacion_septima=PENALIZACION_SEPTIMA, corregir_afinacion=True,
                     supresion_armonico=SUPRESION_3ER_ARMONICO, compresion_log=None,
                     tiempos_centrados=None, variantes=(), beat_times=None, transiciones=None,
                     detalle=False):
    """Devuelve [{"inicio": s, "fin": s, "acorde": "G"}, ...] a partir de un wav mono/estéreo.

    Si se le pasa el stem de bajo, lo usa para desempatar la fundamental. stems_extra es una
    lista de wavs (piano, resto) cuyo chroma se suma al de wav_path: en temas donde la guitarra
    casi no suena, los acordes están en esos stems.

    v115: `variantes` (ver VARIANTES_DETECTOR; vacío = app114 tal cual), `beat_times` para
    "por_tiempo", `transiciones` (conteos) para "transiciones". Con detalle=True devuelve
    (segmentos, detalle), donde detalle trae los puntajes por marco para medir la confianza."""
    variantes = set(variantes or ())
    # None = lo que digan las constantes del módulo (así lab_acordes.py puede probar ambos)
    tiempos_centrados = TIEMPOS_CENTRADOS if tiempos_centrados is None else tiempos_centrados
    prep = _preparar_analisis(wav_path, bajo_path, stems_extra, frame_len, hop, corregir_afinacion,
                              bandas="bandas_semitono" in variantes, tiempos_centrados=tiempos_centrados)
    return _detectar_desde_prep(prep, variantes, umbral_rel=umbral_rel, min_duracion=min_duracion,
                                penalizacion_cambio=penalizacion_cambio, penalizacion_septima=penalizacion_septima,
                                supresion_armonico=supresion_armonico, compresion_log=compresion_log,
                                beat_times=beat_times, transiciones=transiciones, detalle=detalle)


def _detectar_desde_prep(prep, variantes=(), umbral_rel=UMBRAL_SILENCIO, min_duracion=0.35,
                         penalizacion_cambio=PENALIZACION_CAMBIO, penalizacion_septima=PENALIZACION_SEPTIMA,
                         supresion_armonico=SUPRESION_3ER_ARMONICO, compresion_log=None,
                         beat_times=None, transiciones=None, detalle=False):
    """El detector por plantillas a partir de _preparar_analisis (así "Medir mejoras" prepara
    el audio una sola vez y prueba todas las variantes encima)."""
    variantes = set(variantes or ())
    compresion_log = COMPRESION_LOG if compresion_log is None else compresion_log
    chromas = _mags_a_chroma(
        _comprimir_log(_suprimir_3er_armonico(prep["mags"], supresion_armonico), compresion_log), prep["pitch_class"])
    similitud, nombres = _puntajes_plantillas(chromas, prep["chroma_bajo"], penalizacion_septima=penalizacion_septima,
                                              variantes=variantes)
    costos = None
    if "transiciones" in variantes and transiciones:
        costos = costos_transicion(transiciones, nombres, penalizacion_cambio)
    segmentos = _decodificar(
        similitud, nombres, prep["tiempos"], prep["hop_seg"], prep["energia"], penalizacion_cambio,
        umbral_rel, min_duracion,
        beat_times=beat_times if "por_tiempo" in variantes else None, costos=costos,
        percentil_silencio=PERCENTIL_SILENCIO if "silencio_percentil" in variantes else None,
        moda=not penalizacion_cambio)
    if detalle:
        return segmentos, {"puntajes": similitud, "nombres": nombres, "tiempos": prep["tiempos"], "es_logp": False}
    return segmentos


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



ML_NOMBRES_CLASES = [ml_clase_a_nombre(c) for c in range(ML_N_CLASES)]   # "C", "Cm", "C7", ..., "—"


def ml_segmentos_desde_logp(logp, tiempos, energia, hop_seg, penalizacion=6.0,
                            umbral_rel=0.02, min_duracion=0.35, beat_times=None):
    """Mismo armado de segmentos que detectar_acordes de Mesa (silencio por energía,
    fusión de tramos cortos), con la secuencia decidida por Viterbi sobre log-probs.
    v115: con beat_times, decidida por tiempos del pulso (si el modelo lo eligió al entrenar)."""
    return _decodificar(logp, ML_NOMBRES_CLASES, tiempos, hop_seg, energia, penalizacion, umbral_rel,
                        min_duracion, beat_times=beat_times)


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
    prep = _preparar_analisis(wav_path, bajo_path, stems_extra, frame_len, hop)
    mags_sup = _suprimir_3er_armonico(prep["mags"], SUPRESION_3ER_ARMONICO)
    F = ml_features_marco(mags_sup, prep["pitch_class"], prep["chroma_bajo"], prep["energia"])
    return F, prep["energia"], prep["tiempos"], prep["hop_seg"]


def detectar_acordes_ml(wav_path, modelo, bajo_path=None, stems_extra=None, min_duracion=0.35,
                        beat_times=None, detalle=False):
    """Misma salida que detectar_acordes, decidida por el modelo entrenado. v115: si el
    entrenamiento eligió decidir por tiempos del pulso ("por_tiempo" en el modelo) y hay
    beat_times, se decide así."""
    F, energia, tiempos, hop_seg = _features_ml(wav_path, bajo_path, stems_extra)
    meta = getattr(modelo, "meta", {}) or {}
    logp = modelo.log_probs(ml_con_contexto(F, _escalas_modelo(meta)))
    pen = float(meta.get("penalizacion", 9.0))
    # v111: el umbral de silencio también lo elige el entrenamiento (con 0 decide solo
    # el modelo, que tiene su propia clase "sin acorde"). Modelos viejos: el de siempre.
    umbral = float(meta.get("umbral_silencio", UMBRAL_SILENCIO))
    por_tiempo = bool(meta.get("por_tiempo")) and beat_times is not None and len(beat_times) >= 2
    segmentos = ml_segmentos_desde_logp(logp, tiempos, energia, hop_seg, penalizacion=pen,
                                        umbral_rel=umbral, min_duracion=min_duracion,
                                        beat_times=beat_times if por_tiempo else None)
    if detalle:
        return segmentos, {"puntajes": logp, "nombres": ML_NOMBRES_CLASES, "tiempos": tiempos, "es_logp": True}
    return segmentos


def detectar_acordes_cancion(carpeta):
    """Detector que corresponda según Ajustes generales. Devuelve (segmentos, "aprendido" |
    "plantillas"). Si el modelo falla por cualquier motivo, cae al de plantillas.
    v115: pasa por el análisis cacheado del tema (ver _analizar_cancion)."""
    analisis = _analizar_cancion(carpeta)
    return analisis["segmentos"], analisis["detector"]


# ------------------------------------------- v115: análisis de cada tema, cacheado ----
# Antes el análisis corría entero cada vez que hacía falta: al abrir un tema sin batería
# (no se guardaba nada), al corregir el tempo (x2, /2, BPM exacto) y al comparar con el
# MIDI. Ahora acordes + pulso + puntajes por marco quedan en acordes_analisis.npz, con una
# clave que cambia si cambia cualquier cosa que afecte el resultado (stems, detector
# elegido, variantes, modelo entrenado, constantes). Se hace apenas termina la separación,
# así el tema abre listo. Un lock por tema evita que dos dispositivos lo analicen a la vez.
ANALISIS_VERSION = 1
ANALISIS_ARCHIVO = "acordes_analisis.npz"
_LOCKS_TEMA = {}
_LOCKS_TEMA_LOCK = threading.Lock()


def _lock_tema(carpeta):
    with _LOCKS_TEMA_LOCK:
        return _LOCKS_TEMA.setdefault(str(Path(carpeta).resolve()), threading.RLock())


def variantes_activas():
    """Variantes del detector por plantillas prendidas en Ajustes generales."""
    elegidas = {v for v in (leer_prefs().get("detector_variantes") or []) if v in VARIANTES_DETECTOR}
    if "transiciones" in elegidas and not TRANSICIONES_PATH.exists():
        elegidas.discard("transiciones")   # todavía no se midió nada de dónde aprenderlas
    return elegidas


def _firma_archivo(ruta):
    try:
        st = Path(ruta).stat()
        return [round(st.st_mtime, 3), st.st_size]
    except OSError:
        return None


def _clave_analisis(carpeta, usa_modelo, variantes):
    clave = {
        "v": ANALISIS_VERSION, "detector": "aprendido" if usa_modelo else "plantillas",
        "variantes": sorted(variantes),
        "stems": {n: _firma_archivo(carpeta / f"{n}.wav") for n in ("guitar", "bass", "piano", "other", "drums")},
        "ajustes": [PENALIZACION_CAMBIO, UMBRAL_SILENCIO, PENALIZACION_SEPTIMA, PESO_BAJO, SUPRESION_3ER_ARMONICO,
                    COMPRESION_LOG, TIEMPOS_CENTRADOS, TEMPO_PRIOR_BPM, TEMPO_PRIOR_OCTAVAS, PERIODO_FINO,
                    TEMPO_AMBIGUO, PESO_TONALIDAD, PESO_BAJO_INVERSION, PERCENTIL_SILENCIO, PESO_TRANSICIONES],
    }
    if usa_modelo:
        clave["modelo"] = _firma_archivo(MODELO_ACORDES_PATH)
    if "transiciones" in variantes:
        clave["transiciones"] = _firma_archivo(TRANSICIONES_PATH)
    return json.dumps(clave, sort_keys=True)


def _leer_analisis(ruta, clave):
    if not ruta.exists():
        return None
    try:
        with np.load(ruta, allow_pickle=False) as d:
            meta = json.loads(str(d["meta"]))
            if meta.get("clave") != clave:
                return None
            puntajes = d["puntajes"].astype(np.float32)
            tiempos = d["tiempos"]
            nombres = [str(n) for n in d["nombres"]]
    except Exception:  # noqa: BLE001
        return None   # roto o de otra versión: se rehace
    return {**meta, "puntajes": puntajes, "tiempos": tiempos, "nombres": nombres}


def _guardar_analisis(ruta, clave, analisis):
    meta = {k: v for k, v in analisis.items() if k not in ("puntajes", "tiempos", "nombres")}
    meta["clave"] = clave
    try:
        _guardar_npz(ruta, puntajes=np.asarray(analisis["puntajes"], dtype=np.float16),
                     tiempos=np.asarray(analisis["tiempos"], dtype=np.float64),
                     nombres=np.array(analisis["nombres"], dtype=str), meta=np.array(json.dumps(meta)))
    except OSError as exc:
        print(f"[mesa] no pude guardar el análisis de {ruta.parent.name} ({exc}); se recalcula la próxima vez")


def _analizar_cancion(carpeta):
    """Acordes y pulso de un tema con el detector que corresponda, de la caché si ya están.
    Devuelve {segmentos, detector, beat_times, bpm, bpm_alternativo, duracion, puntajes,
    nombres, tiempos, es_logp}. beat_times son los del pulso (todavía sin elegir el tiempo 1)."""
    carpeta = Path(carpeta)
    with _lock_tema(carpeta):
        usa_modelo = detector_aprendido_activo()
        variantes = set() if usa_modelo else variantes_activas()
        clave = _clave_analisis(carpeta, usa_modelo, variantes)
        ruta = carpeta / ANALISIS_ARCHIVO
        guardado = _leer_analisis(ruta, clave)
        if guardado:
            return guardado

        guitarra, bajo, bateria = carpeta / "guitar.wav", carpeta / "bass.wav", carpeta / "drums.wav"
        extras = [carpeta / "piano.wav", carpeta / "other.wav"]
        if bateria.exists():
            beat_times, bpm, bpm_alt = _detectar_pulso(bateria, detalle=True)
        else:
            beat_times, bpm, bpm_alt = [], 0.0, None

        segmentos, detalle, detector = None, None, "plantillas"
        if usa_modelo:
            try:
                segmentos, detalle = detectar_acordes_ml(guitarra, modelo_acordes(), bajo_path=bajo,
                                                         stems_extra=extras, beat_times=beat_times, detalle=True)
                detector = "aprendido"
            except Exception as exc:  # noqa: BLE001
                print(f"[mesa] detector aprendido falló ({exc}); se usa el de plantillas")
        if segmentos is None:
            segmentos, detalle = detectar_acordes(
                guitarra, bajo_path=bajo, stems_extra=extras, variantes=variantes, beat_times=beat_times,
                transiciones=leer_transiciones() if "transiciones" in variantes else None, detalle=True)

        analisis = {
            "segmentos": segmentos, "detector": detector, "variantes": sorted(variantes),
            "beat_times": [round(float(t), 4) for t in beat_times], "bpm": round(float(bpm), 1),
            "bpm_alternativo": bpm_alt, "duracion": _duracion_wav(guitarra), "es_logp": detalle["es_logp"],
            "puntajes": detalle["puntajes"], "nombres": list(detalle["nombres"]), "tiempos": detalle["tiempos"],
        }
        _guardar_analisis(ruta, clave, analisis)
        return analisis


# Para mostrar la confianza del detector de plantillas como probabilidad: softmax de la
# similitud con esta "temperatura" (una diferencia de 0,1 en similitud ~ 12 veces más probable).
TEMPERATURA_CONFIANZA = 25.0
CONFIANZA_ARCHIVO = "acordes_confianza.json"


def confianza_por_tiempo(analisis, beat_times):
    """Para cada tiempo de la grilla (beat_times crudos, sin sincronía): probabilidad del
    acorde más probable según el detector y los 3 mejores candidatos. Sirve para marcar en
    el editor los compases dudosos y ofrecer alternativas de un toque."""
    P = np.asarray(analisis["puntajes"], dtype=np.float64)
    nombres = analisis["nombres"]
    tiempos = np.asarray(analisis["tiempos"], dtype=float)
    if not len(beat_times) or not P.size:
        return [], []
    if analisis.get("es_logp"):
        prob = np.exp(P)
    else:
        z = P * TEMPERATURA_CONFIANZA
        z -= z.max(axis=1, keepdims=True)
        prob = np.exp(z)
        prob /= prob.sum(axis=1, keepdims=True)
    es_acorde = np.array([n not in (None, "—") for n in nombres])
    prob = prob[:, es_acorde]
    nombres_acorde = [n for n, ok in zip(nombres, es_acorde) if ok]

    beats = np.asarray(beat_times, dtype=float)
    paso = float(np.median(np.diff(beats))) if len(beats) > 1 else 0.5
    bordes = np.append(beats, beats[-1] + paso)
    grupo = np.searchsorted(bordes, tiempos, side="right") - 1
    dentro = (grupo >= 0) & (grupo < len(beats))
    S = np.zeros((len(beats), prob.shape[1]))
    np.add.at(S, grupo[dentro], prob[dentro])
    cuantos = np.bincount(grupo[dentro], minlength=len(beats))
    vacios = np.nonzero(cuantos == 0)[0]
    if len(vacios):   # tiempo sin ningún marco adentro: el marco más cercano
        cerca = np.clip(np.searchsorted(tiempos, beats[vacios]), 0, len(tiempos) - 1)
        S[vacios] = prob[cerca]
    S /= np.maximum(S.sum(axis=1, keepdims=True), 1e-12)
    orden = np.argsort(-S, axis=1)[:, :3]
    confianza = [round(float(S[i, orden[i, 0]]), 2) for i in range(len(beats))]
    alternativas = [[nombres_acorde[j] for j in orden[i]] for i in range(len(beats))]
    return confianza, alternativas


def _guardar_confianza(carpeta, analisis, beat_times):
    try:
        confianza, alternativas = confianza_por_tiempo(analisis, beat_times)
        escribir_atomico(carpeta / CONFIANZA_ARCHIVO, json.dumps({
            "beat_times": [round(float(t), 3) for t in beat_times], "detector": analisis["detector"],
            "confianza": confianza, "alternativas": alternativas}))
    except Exception as exc:  # noqa: BLE001
        print(f"[mesa] no pude calcular la confianza de {carpeta.name} ({exc})")


def _generar_grilla(carpeta, conservar=None):
    """Analiza el tema (o lo toma de la caché) y escribe acordes.txt, acordes_grid.json y
    acordes_confianza.json. Devuelve (analisis, tokens, beat_times); sin pulso, beat_times
    vacío y no se escribe ninguna grilla (los acordes se muestran sin compases)."""
    carpeta = Path(carpeta)
    with _lock_tema(carpeta):
        analisis = _analizar_cancion(carpeta)
        beat_times = analisis["beat_times"]
        if not beat_times:
            return analisis, None, []
        fase = _elegir_fase_compas(beat_times, analisis["segmentos"])
        tokens, beat_times = _grid_desde_segmentos(beat_times[fase:], analisis["segmentos"])
        grid = {"beat_times": beat_times, "beats_por_compas": 4, "bpm": analisis["bpm"],
                "duracion": analisis["duracion"], "offset": 0.0, "detector": analisis["detector"]}
        if analisis.get("bpm_alternativo"):
            grid["bpm_alternativo"] = analisis["bpm_alternativo"]
        grid.update(conservar or {})
        escribir_atomico(carpeta / "acordes.txt", _tokens_a_texto(tokens))
        escribir_atomico(carpeta / "acordes_grid.json", json.dumps(grid))
        _guardar_confianza(carpeta, analisis, beat_times)
        return analisis, tokens, beat_times


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
                if meta.get("firma") in (firma, None):
                    # firma None: hecho por los scripts de prueba, mismas features, se adopta.
                    # v115: los de antes no traen el pulso (para decidir por tiempos): se agrega.
                    cambio = meta.get("firma") is None or "beats" not in arrays
                    meta["firma"] = firma
                    if "beats" not in arrays:
                        arrays["beats"] = _beats_para_entrenar(carpeta)
                    if cambio:
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
                 beats=_beats_para_entrenar(carpeta),
                 meta=np.array(json.dumps({"cancion": carpeta.name, "fuente": fuente, "hop_seg": hop_seg,
                                           "duracion": duracion, "referencia": ref, "base": base,
                                           "version_features": ML_VERSION_FEATURES, "firma": firma})))
    return True


def _beats_para_entrenar(carpeta):
    """Pulso detectado de la batería (lo mismo que usaría Mesa con ese tema), para probar
    la decisión por tiempos. Vacío si no hay batería."""
    bateria = carpeta / "drums.wav"
    if not bateria.exists():
        return np.zeros(0)
    try:
        return np.asarray(_detectar_pulso(bateria)[0], dtype=np.float64)
    except Exception:  # noqa: BLE001
        return np.zeros(0)


def _guardar_npz(destino, **arrays):
    """np.savez_compressed atómico (si se corta a la mitad no queda un archivo roto)."""
    tmp = destino.with_name(destino.stem + ".tmp.npz")
    np.savez_compressed(tmp, **arrays)
    os.replace(tmp, destino)


def _cargar_tema_cache(nombre):
    with np.load(ML_CACHE_DIR / f"{nombre}.npz") as d:
        meta = json.loads(str(d["meta"]))
        F, y, energia, tiempos = d["F"], d["y"], d["energia"], d["tiempos"]
        beats = d["beats"] if "beats" in d.files else np.zeros(0)
    return {"nombre": nombre, "F": F, "y": y.astype(np.int64),
            "energia": energia, "tiempos": tiempos, "meta": meta, "beats": beats}


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
        # v115: además de umbral y penalización, si conviene decidir por tiempos del pulso
        combos = [(u, p_, pt) for u in ML_UMBRALES for p_ in ML_PENALIZACIONES for pt in (False, True)]
        # puntajes[(variante, umbral, pen, por_tiempo)][tema] = (tríada, global)
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
                    for (u, p_, pt) in combos:
                        # sin pulso no hay tiempos: se decide por marcos (igual que en Mesa)
                        beats = t["beats"] if (pt and len(t["beats"]) >= 2) else None
                        seg = ml_segmentos_desde_logp(logp, t["tiempos"], t["energia"], t["meta"]["hop_seg"],
                                                      penalizacion=p_, umbral_rel=u, beat_times=beats)
                        puntajes.setdefault((vi, u, p_, pt), {})[t["nombre"]] = _puntajes_tiempo(
                            t["meta"]["referencia"], seg, t["meta"]["duracion"])

        def prom(clave, idx):
            return float(np.mean([puntajes[clave][t["nombre"]][idx] for t in temas]))
        mejor = max(puntajes, key=lambda c_: (prom(c_, 1), prom(c_, 0)))
        vi, umbral, pen, por_tiempo = mejor
        var = ML_VARIANTES[vi]
        # la configuración de v110 (variante 0, umbral de siempre), para mostrar cuánto se ganó
        ref_v110 = max(((0, UMBRAL_SILENCIO, p_, False) for p_ in ML_PENALIZACIONES), key=lambda c_: prom(c_, 1))

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
            "por_tiempo": por_tiempo, "excluidos": excluidos,
        }

        guardado = tri_mejor > base_tri
        if guardado:
            _entreno_set(etapa="entrenando el modelo final", i=0, n=1, detalle=var["nombre"])
            X, y = _ml_juntar(temas, var["escalas"])
            final = MLModelo(X.shape[1], oculta=var["oculta"], semilla=0)
            final.entrenar(X, y, epocas=ML_EPOCAS, semilla=0)
            tmp = MODELO_ACORDES_PATH.with_name("modelo_acordes.tmp.npz")
            final.guardar(tmp, extra={"penalizacion": pen, "umbral_silencio": umbral, "por_tiempo": por_tiempo,
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


# ------------------------------------------ v115: medir las variantes contra tus MIDI ----
# Las variantes del detector por plantillas (VARIANTES_DETECTOR) arrancan apagadas: cada
# una suena bien en teoría, pero lo que mejora un tema empeora otro. Este botón las mide
# con los temas que tienen un MIDI importado, igual que "Comparar con detector" pero en
# toda la biblioteca: el detector de siempre, cada variante sola y todas juntas. Las
# transiciones de cada tema se aprenden de los OTROS temas (si no, se mide con trampa), y
# al final se guardan las de toda la biblioteca en transiciones_acordes.json.
MEDICION_PATH = ML_CACHE_DIR / "_ultima_medicion_variantes.json"
_medicion = {"corriendo": False, "etapa": "", "i": 0, "n": 0, "error": None, "detalle": ""}
_medicion_lock = threading.Lock()


def _medicion_set(**kw):
    with _medicion_lock:
        _medicion.update(kw)


def _sumar_conteos(*conteos, restar=None):
    total = {}
    for c in conteos:
        for k, v in c.items():
            total[k] = total.get(k, 0) + v
    for k, v in (restar or {}).items():
        total[k] = total.get(k, 0) - v
    return {k: v for k, v in total.items() if v > 0}


def _medir_variantes():
    try:
        ML_CACHE_DIR.mkdir(exist_ok=True)
        raiz = OUTPUT_DIR / MODEL
        carpetas = sorted(p for p in raiz.iterdir() if p.is_dir() and (p / "guitar.wav").exists())
        temas = []
        for c in carpetas:
            ref = _referencia_midi(c)[0]
            if ref:
                temas.append((c, ref))
        if not temas:
            raise RuntimeError("no hay ningún tema con un MIDI importado contra el que medir")
        conteos = {c.name: conteos_transiciones(ref) for c, ref in temas}
        todos = _sumar_conteos(*conteos.values())
        configs = [("actual", set())] + [(v, {v}) for v in VARIANTES_DETECTOR] + [("todas", set(VARIANTES_DETECTOR))]
        puntajes = {nombre: {} for nombre, _ in configs}
        for i, (c, ref) in enumerate(temas):
            _medicion_set(etapa="midiendo", i=i, n=len(temas), detalle=c.name)
            try:
                kw = {"bajo_path": c / "bass.wav", "stems_extra": [c / "piano.wav", c / "other.wav"]}
                prep = _preparar_analisis(c / "guitar.wav", **kw)
                prep_bandas = None
                bateria = c / "drums.wav"
                beats = _detectar_pulso(bateria)[0] if bateria.exists() else []
                duracion = _duracion_wav(c / "guitar.wav")
                de_los_otros = _sumar_conteos(todos, restar=conteos[c.name])
                for nombre, variantes in configs:
                    if "bandas_semitono" in variantes:
                        if prep_bandas is None:
                            prep_bandas = _preparar_analisis(c / "guitar.wav", bandas=True, **kw)
                        base = prep_bandas
                    else:
                        base = prep
                    seg = _detectar_desde_prep(base, variantes, beat_times=beats or None,
                                               transiciones=de_los_otros if "transiciones" in variantes else None)
                    puntajes[nombre][c.name] = _puntajes_tiempo(ref, seg, duracion)
            except Exception as exc:  # noqa: BLE001
                print(f"[mesa] medición: se saltea {c.name} ({exc})")
                for nombre in puntajes:
                    puntajes[nombre].pop(c.name, None)

        # mismo criterio que el entrenamiento: si el detector de siempre coincide tan poco,
        # casi seguro el MIDI está corrido o es de otra versión del tema
        actuales = puntajes["actual"]
        validos = [n for n, (tri, _g) in actuales.items() if tri >= ML_MIN_BASE_TRIADA]
        excluidos = [{"tema": n, "base": round(tri, 1)} for n, (tri, _g) in actuales.items() if tri < ML_MIN_BASE_TRIADA]
        if not validos:
            raise RuntimeError("ningún tema con MIDI sirvió para medir (¿los MIDI están desfasados?)")
        filas = []
        for nombre, _ in configs:
            tri = float(np.mean([puntajes[nombre][t][0] for t in validos]))
            glo = float(np.mean([puntajes[nombre][t][1] for t in validos]))
            dif = [puntajes[nombre][t][0] - actuales[t][0] for t in validos]
            filas.append({"variante": nombre, "triada": round(tri, 1), "global": round(glo, 1),
                          "mejoran": sum(1 for d in dif if d > 1), "empeoran": sum(1 for d in dif if d < -1)})
        escribir_atomico(TRANSICIONES_PATH, json.dumps({
            "conteos": todos, "temas": len(temas), "fecha": datetime.now().strftime("%Y-%m-%d %H:%M")}))
        resultado = {"fecha": datetime.now().strftime("%Y-%m-%d %H:%M"), "temas": len(validos),
                     "filas": filas, "excluidos": excluidos}
        escribir_atomico(MEDICION_PATH, json.dumps(resultado, ensure_ascii=False))
        _medicion_set(corriendo=False, etapa="listo", error=None)
    except Exception as exc:  # noqa: BLE001
        _medicion_set(corriendo=False, etapa="error", error=str(exc))


def ultima_medicion():
    try:
        return json.loads(MEDICION_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


@app.route("/detector/medir", methods=["POST"])
def detector_medir():
    with _medicion_lock:
        if _medicion["corriendo"]:
            return jsonify({"error": "ya se está midiendo"}), 409
        _medicion.update(corriendo=True, etapa="arrancando", i=0, n=0, error=None, detalle="")
    threading.Thread(target=_medir_variantes, daemon=True).start()
    return jsonify({"ok": True})


@app.route("/detector/medicion")
def detector_medicion():
    with _medicion_lock:
        estado = dict(_medicion)
    estado.update(ultima=ultima_medicion(), activas=sorted(variantes_activas()),
                  elegidas=sorted(v for v in (leer_prefs().get("detector_variantes") or []) if v in VARIANTES_DETECTOR),
                  nombres=VARIANTES_DETECTOR, transiciones=TRANSICIONES_PATH.exists())
    return jsonify(estado)


@app.route("/detector/variantes", methods=["POST"])
def detector_variantes():
    """Guarda qué variantes usar. Valen para los temas que se analicen de ahora en más (o al
    tocar Regenerar): los acordes ya guardados no se tocan."""
    pedidas = (request.get_json(silent=True) or {}).get("variantes") or []
    if not isinstance(pedidas, list):
        return jsonify({"error": "formato inválido"}), 400
    elegidas = sorted({v for v in pedidas if v in VARIANTES_DETECTOR})
    guardar_pref("detector_variantes", elegidas)
    return jsonify({"ok": True, "elegidas": elegidas, "activas": sorted(variantes_activas())})


# --------------------------------------------------- pulso, compás y grilla editable ----
# Detecta el tempo/tiempos a partir de la batería ya separada (spectral flux +
# autocorrelación — de nuevo, solo numpy). La fase de "tiempo 1" del compás no se
# detecta directamente del audio (poco confiable); se elige la que mejor alinea
# los cambios de acorde ya detectados con un tiempo 1, que es un supuesto mucho
# más sólido. Asume 4/4 y tempo constante en toda la canción.

TEMPO_PRIOR_BPM = 120.0
TEMPO_PRIOR_OCTAVAS = 1.0
PERIODO_FINO = True


# v115: tempo ambiguo. El error típico del pulso es elegir el doble o la mitad (bombo y
# caja alternados, platillo en corcheas). Si el pulso alternativo puntúa al menos esta
# fracción del elegido (con la misma preferencia por ~120 BPM), se guarda como
# "bpm_alternativo" y la mesa pregunta "¿el pulso va a X BPM?" con un toque para corregir.
TEMPO_AMBIGUO = 0.4


def _detectar_pulso(wav_path, hop=512, frame=1024, bpm_min=60, bpm_max=200, detalle=False):
    """(beat_times, bpm); con detalle=True, (beat_times, bpm, bpm_alternativo o None)."""
    data, sr = _cargar_wav_mono(wav_path)
    if len(data) < frame:
        return ([], 0.0, None) if detalle else ([], 0.0)
    # v115: de a tandas (antes los marcos y su espectro complejo enteros: ~250 MB en un tema
    # de 4 minutos). La resta entre marcos vecinos cruza la frontera de cada tanda.
    vista = sliding_window_view(np.asarray(data, dtype=np.float32), frame)[::hop]
    hann = np.hanning(frame).astype(np.float32)
    envolvente = np.zeros(vista.shape[0])
    anterior = None
    for i in range(0, vista.shape[0], 2048):
        espectro = np.abs(np.fft.rfft(vista[i:i + 2048] * hann, axis=1))
        if anterior is not None:
            espectro_ext = np.vstack([anterior, espectro])
            flujo = np.diff(espectro_ext, axis=0)
            destino = slice(i, i + espectro.shape[0])
        else:
            flujo = np.diff(espectro, axis=0)
            destino = slice(1, espectro.shape[0])
        flujo[flujo < 0] = 0
        envolvente[destino] = flujo.sum(axis=1)
        anterior = espectro[-1:]
    return _pulso_desde_envolvente(envolvente, sr / hop, len(data) / sr, bpm_min, bpm_max, detalle=detalle)


def _pulso_desde_envolvente(envolvente, sr_hop, duracion, bpm_min=60, bpm_max=200, detalle=False):
    """(beat_times, bpm) a partir de la envolvente de ataques de la batería. Con detalle=True
    agrega el BPM alternativo (doble o mitad) si el pulso es ambiguo (ver TEMPO_AMBIGUO)."""
    sin_pulso = ([], 0.0, None) if detalle else ([], 0.0)
    lag_min = int(sr_hop * 60 / bpm_max)
    lag_max = min(int(sr_hop * 60 / bpm_min), len(envolvente) - 1)
    if lag_max <= lag_min:
        return sin_pulso
    if not np.any(envolvente > 0):
        return sin_pulso   # batería en silencio: sin pulso (se muestran los acordes sin grilla)

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
    factor_alternativo = None
    if detalle:
        ganador = float(puntaje[periodo_grueso - lag_min])
        candidatos = []
        for factor in (2.0, 0.5):
            lag_alt = periodo_grueso * factor
            lo, hi = max(lag_min, int(lag_alt * 0.97)), min(lag_max, int(np.ceil(lag_alt * 1.03)))
            if lo <= hi:
                candidatos.append((float(puntaje[lo - lag_min:hi - lag_min + 1].max()), factor))
        if candidatos and ganador > 0:
            mejor_alt, factor = max(candidatos)
            if mejor_alt >= TEMPO_AMBIGUO * ganador:
                factor_alternativo = factor

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
    beat_times = [t for t in beat_times if t <= duracion]
    if detalle:
        bpm_alt = round(bpm / factor_alternativo, 1) if factor_alternativo else None
        if bpm_alt is not None and not (40 <= bpm_alt <= 260):
            bpm_alt = None
        return beat_times, bpm, bpm_alt
    return beat_times, bpm


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
    return _render_pagina(
        HOME_HTML, canciones=canciones, recientes=obtener_recientes(canciones),
        colores=color_por_cancion, datos=datos, setlists=leer_setlists(),
        jobs=jobs_activos(), version_app=VERSION_APP,
        iniciales={c: iniciales_cancion(datos[c]["titulo"]) for c in canciones},
        info={c: info_cancion(c) for c in canciones},
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
    return _render_pagina(
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
    return _render_pagina(PROCESANDO_HTML, job_id=job_id, titulo_pagina="Separando pistas · Mesa",
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

    return _render_pagina(
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
    genera esa grilla (agrupada por compás) y la cachea junto a los stems.
    v115: normalmente ya está hecha (se analiza al terminar la separación); si no, el
    análisis se hace una sola vez aunque lo pidan dos dispositivos a la vez, y un tema sin
    batería ya no se reanaliza cada vez que se abre."""
    carpeta = stems_dir(song)
    guitarra = carpeta / "guitar.wav"
    if not guitarra.exists():
        return jsonify({"error": "no hay pista de guitarra para esta canción"}), 404

    txt_path = carpeta / "acordes.txt"
    grid_path = carpeta / "acordes_grid.json"
    if not (txt_path.exists() and grid_path.exists()):
        try:
            with _lock_tema(carpeta):
                if not (txt_path.exists() and grid_path.exists()):
                    analisis, _tokens, beat_times = _generar_grilla(carpeta)
                    if not beat_times:
                        # sin batería o sin pulso claro: se muestra igual, pero sin grilla por compás editable
                        return jsonify({"segmentos": analisis["segmentos"], "beat_times": [], "beats_por_compas": 4,
                                        "offset": 0.0, "bpm": None, "capo": 0})
        except Exception as exc:  # noqa: BLE001
            return jsonify({"error": f"no se pudo analizar: {exc}"}), 500
    return _respuesta_acordes(carpeta)


def _respuesta_acordes(carpeta):
    txt_path = carpeta / "acordes.txt"
    grid_path = carpeta / "acordes_grid.json"
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
            "origen": grid.get("origen") or "detector",
        }
        if advertencia:
            resp["advertencia"] = advertencia
        if isinstance(grid.get("coincidencia"), dict):
            resp["coincidencia"] = grid["coincidencia"]   # v103: última comparación detector vs MIDI
        if grid.get("bpm_alternativo") and grid.get("origen") != "midi":
            resp["bpm_alternativo"] = grid["bpm_alternativo"]   # v115: "¿el pulso va a X BPM?"
        if (carpeta / RESPALDO_DIR / "acordes.txt").exists():
            resp["hay_respaldo"] = True
        return jsonify(resp)
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": f"no se pudo leer acordes.txt: {exc}"}), 500


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

        # v115: los acordes salen del análisis cacheado (antes se volvía a correr el detector entero)
        analisis = _analizar_cancion(carpeta)
        segmentos_detectados, detector_usado = analisis["segmentos"], analisis["detector"]
        duracion = analisis["duracion"]

        _respaldar_acordes(carpeta, "tempo")
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
        _guardar_confianza(carpeta, analisis, beat_times)
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
    la grilla nueva arranca con sincronía 0.
    v115: antes de borrar se guarda una copia (botón "Deshacer"), y el análisis sale de la
    caché si nada cambió desde la última vez (mismo resultado, sin esperar)."""
    carpeta = stems_dir(song)
    if not (carpeta / "guitar.wav").exists():
        return jsonify({"error": "no hay pista de guitarra para esta canción"}), 404
    with _lock_tema(carpeta):
        try:
            grid_viejo = json.loads((carpeta / "acordes_grid.json").read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            grid_viejo = {}
        _respaldar_acordes(carpeta, "regenerar")
        for nombre in ("acordes.txt", "acordes_grid.json", CONFIANZA_ARCHIVO):
            p = carpeta / nombre
            if p.exists():
                try:
                    p.unlink()
                except OSError as exc:
                    return jsonify({"error": f"no pude borrar {nombre}: {exc}. ¿Lo tenés abierto en el editor? Cerralo e intentá de nuevo."}), 500
        _anclar_marcas_rasgueo(carpeta, grid_viejo.get("offset", 0.0))
        capo = grid_viejo.get("capo", 0)
        try:
            _generar_grilla(carpeta, conservar={"capo": capo} if capo else None)
        except Exception as exc:  # noqa: BLE001
            return jsonify({"error": f"no se pudo analizar: {exc}"}), 500
    return acordes(song)


# ------------------------------------------------ v115: deshacer (una copia por tema) ----
# Regenerar, importar un MIDI y corregir el tempo reemplazan acordes.txt entero: las
# correcciones a mano se perdían sin vuelta atrás. Antes de cada una se copia lo que hay a
# .respaldo/ (una sola copia: la de la última operación) y la mesa ofrece "Deshacer".
RESPALDO_DIR = ".respaldo"
_ARCHIVOS_RESPALDO = ("acordes.txt", "acordes_grid.json", "rasgueo_marcas.json", "acordes_midi.json",
                      CONFIANZA_ARCHIVO)


def _respaldar_acordes(carpeta: Path, motivo: str) -> bool:
    if not (carpeta / "acordes.txt").exists():
        return False   # no hay nada propio que perder
    destino = carpeta / RESPALDO_DIR
    try:
        destino.mkdir(exist_ok=True)
        presentes = []
        for nombre in _ARCHIVOS_RESPALDO:
            origen = carpeta / nombre
            if origen.exists():
                shutil.copy2(origen, destino / nombre)
                presentes.append(nombre)
            elif (destino / nombre).exists():
                (destino / nombre).unlink()
        escribir_atomico(destino / "respaldo.json", json.dumps({
            "archivos": presentes, "motivo": motivo, "fecha": datetime.now().strftime("%Y-%m-%d %H:%M")}))
        return True
    except OSError as exc:
        print(f"[mesa] no pude guardar la copia de los acordes de {carpeta.name} ({exc})")
        return False


@app.route("/deshacer_acordes/<song>", methods=["POST"])
def deshacer_acordes(song):
    """Vuelve los acordes a como estaban antes de la última operación que los reemplazó."""
    carpeta = stems_dir(song)
    origen = carpeta / RESPALDO_DIR
    try:
        info = json.loads((origen / "respaldo.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return jsonify({"error": "no hay nada para deshacer en este tema"}), 404
    with _lock_tema(carpeta), _LOCK_DATOS:
        try:
            for nombre in _ARCHIVOS_RESPALDO:
                if nombre in info.get("archivos", []):
                    tmp = carpeta / (nombre + ".tmp")
                    shutil.copy2(origen / nombre, tmp)
                    os.replace(tmp, carpeta / nombre)
                elif (carpeta / nombre).exists():
                    (carpeta / nombre).unlink()
            shutil.rmtree(origen, ignore_errors=True)
        except OSError as exc:
            return jsonify({"error": f"no pude volver atrás: {exc}"}), 500
    return acordes(song)


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
SW_JS = _plantilla("sw.js")


BLE_TEST_HTML = _plantilla("ble_test.html")


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

    duracion = _duracion_wav(guitarra)

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

    respaldado = _respaldar_acordes(carpeta, "midi")   # v115: "Deshacer" vuelve a los acordes de antes
    escribir_atomico((carpeta / "acordes.txt"), _tokens_a_texto(tokens))
    try:
        (carpeta / CONFIANZA_ARCHIVO).unlink()   # el MIDI manda: no hay compases "dudosos"
    except OSError:
        pass
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
        "ok": True, "bpm": round(bpm, 1), "acordes": len(segmentos), "hay_respaldo": respaldado,
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
        # v115: con las variantes prendidas en Ajustes generales (lo que de verdad usaría Mesa)
        variantes = variantes_activas()
        beats_pulso = _analizar_cancion(carpeta)["beat_times"]
        detectados = detectar_acordes(
            guitarra, bajo_path=carpeta / "bass.wav",
            stems_extra=[carpeta / "piano.wav", carpeta / "other.wav"],
            variantes=variantes, beat_times=beats_pulso,
            transiciones=leer_transiciones() if "transiciones" in variantes else None)
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
                                         stems_extra=[carpeta / "piano.wav", carpeta / "other.wav"],
                                         beat_times=beats_pulso)
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

    resp = {
        "compases": compases,
        "beats_por_compas": bpc,
        "vocabulario": _vocabulario_completo(),
        "posiciones_esperadas": len(base),
        # tiempos crudos (sin offset): el editor los necesita para traducir
        # entre la celda que tocás y el tiempo con el que se guardan las
        # marcas de rasgueo
        "beat_times": base,
        "offset": offset,
    }
    # v115: qué tan seguro estaba el detector en cada tiempo, y sus 3 candidatos. Solo si la
    # grilla sigue siendo la del detector (con un MIDI importado no hay nada que dudar).
    confianza = _leer_confianza(carpeta, base, grid)
    if confianza:
        resp["confianza"] = confianza["confianza"]
        resp["alternativas"] = confianza["alternativas"]
    return jsonify(resp)


def _leer_confianza(carpeta, base, grid):
    if grid.get("origen") == "midi":
        return None
    try:
        datos = json.loads((carpeta / CONFIANZA_ARCHIVO).read_text(encoding="utf-8"))
        tiempos = datos.get("beat_times") or []
        if len(tiempos) != len(base) or (base and max(abs(a - b) for a, b in zip(tiempos, base)) > 0.01):
            return None   # es de otra grilla (cambió el tempo a mano en el .txt, etc.)
        return datos
    except (OSError, json.JSONDecodeError, TypeError, ValueError):
        return None


@app.route("/tempo_descartar/<song>", methods=["POST"])
def tempo_descartar(song):
    """v115: "No, el pulso está bien": deja de preguntar por el BPM alternativo."""
    grid_path = stems_dir(song) / "acordes_grid.json"
    if not grid_path.exists():
        return jsonify({"error": "esta canción todavía no tiene grilla de acordes"}), 404
    with _LOCK_DATOS:
        try:
            grid = json.loads(grid_path.read_text(encoding="utf-8"))
            grid.pop("bpm_alternativo", None)
            escribir_atomico(grid_path, json.dumps(grid))
        except (OSError, json.JSONDecodeError) as exc:
            return jsonify({"error": str(exc)}), 500
    return jsonify({"ok": True})


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
        previos = _texto_a_tokens(txt_path.read_text(encoding="utf-8")) if txt_path.exists() else []
    except OSError:
        previos = []
    try:
        escribir_atomico(txt_path, _tokens_a_texto(normalizados, beats_por_compas=bpc))
    except OSError as exc:
        return jsonify({"error": f"no pude guardar acordes.txt: {exc}. ¿Lo tenés abierto en otro editor?"}), 500

    # v115: lo que corregiste o marcaste como revisado deja de figurar como dudoso
    revisados = {int(c) for c in (datos.get("revisados") or []) if isinstance(c, int) or str(c).isdigit()}
    cambiados = {i // bpc for i, t in enumerate(normalizados) if i >= len(previos) or previos[i] != t}
    _marcar_revisados(carpeta, grid, revisados | cambiados, bpc)
    return jsonify({"ok": True})


def _marcar_revisados(carpeta, grid, compases, bpc):
    if not compases:
        return
    datos = _leer_confianza(carpeta, grid["beat_times"], grid)
    if not datos:
        return
    conf = datos["confianza"]
    for c in compases:
        for i in range(c * bpc, min(len(conf), (c + 1) * bpc)):
            conf[i] = 1.0
    try:
        escribir_atomico(carpeta / CONFIANZA_ARCHIVO, json.dumps(datos))
    except OSError:
        pass


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

BASE_STYLE = _plantilla("base.html")

# v107: Ajustes generales en un solo lugar, para la mesa y la portada (mismos
# ids, así el JS de la mesa no cambia). Lo que solo sirve dentro de un tema
# (conectar las gafas por el Bluetooth del navegador) va con "en_mesa".
PANEL_GENERALES_HTML = _plantilla("panel_generales.html")

HOME_HTML = BASE_STYLE + _plantilla("portada.html")

SETLIST_HTML = BASE_STYLE + _plantilla("setlist.html")

PROCESANDO_HTML = BASE_STYLE + _plantilla("procesando.html")

MESA_HTML = BASE_STYLE + _plantilla("mesa.html")

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
    html = _render_pagina(
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


HOJA_HTML = _plantilla("hoja.html")


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
                  f"Renovalo con: tailscale cert {_host_certificado(ruta_cert)}")
    except Exception:  # noqa: BLE001
        pass


def _iniciar_https_directo():
    """Segundo servidor Flask en 0.0.0.0:443 con TLS terminado acá (no por
    tailscale serve). Cualquier falla acá (archivos ausentes, certificado
    vencido/corrupto, puerto ocupado) se avisa por consola y no arranca este
    hilo -- el servidor de siempre en el puerto 5000 sigue funcionando igual,
    nunca se cae la app entera por esto."""
    if TLS_CERT is None:
        print("[https] no encontré ningún certificado *.ts.net.crt (ni MESA_TLS_CERT/MESA_TLS_KEY): "
              "sigo solo con el puerto 5000 (http).")
        return
    if not TLS_CERT.exists() or not TLS_KEY.exists():
        print(f"[https] no encontré {TLS_CERT} / {TLS_KEY}: sigo solo con el puerto 5000 (http).")
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
    host_tls = _host_certificado(TLS_CERT) if TLS_CERT else "<tu-maquina>.<tu-tailnet>.ts.net"
    print(f"    tailscale cert {host_tls}   (una sola vez, o cuando avise que vence)")
    print("    tailscale serve --https=443 off   (para que el 443 quede libre para esta app)")
    print(f"y abrí en la tablet https://{host_tls} — el mismo puerto 443 de siempre.")

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
