"""Temas sintéticos con stems tipo Demucs, para probar el detector sin audio real.

Acordes en registro de guitarra y piano con armónicos, bajo en la fundamental y una
batería simple (bombo 1 y 3, caja 2 y 4, platillo en corcheas). Sirven para ver que nada
se rompió, NO para medir mejoras del detector: son mucho más fáciles que una grabación.
"""
import json
import wave
from pathlib import Path

import numpy as np

SR = 22050
NOTAS = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]
CALIDADES = {"": [0, 4, 7], "m": [0, 3, 7], "7": [0, 4, 7, 10]}


def _partir(acorde):
    raiz = acorde[:2] if acorde[:2] in NOTAS else acorde[:1]
    return NOTAS.index(raiz), CALIDADES[acorde[len(raiz):]]


def _tono(f, dur, decaimiento=1.5, armonicos=(1, .5, .33, .25, .2, .15)):
    t = np.arange(int(dur * SR)) / SR
    s = sum(a * np.sin(2 * np.pi * f * k * t) for k, a in enumerate(armonicos, 1) if f * k < SR / 2)
    return s * np.exp(-t * decaimiento)


def _hz(midi, cents=0.0):
    return 440.0 * 2 ** ((midi - 69) / 12 + cents / 1200)


def _escribir(ruta, x):
    x = x / (np.abs(x).max() + 1e-9) * 0.7
    estereo = np.repeat((x * 32767).astype(np.int16)[:, None], 2, axis=1)
    with wave.open(str(ruta), "wb") as w:
        w.setnchannels(2)
        w.setsampwidth(2)
        w.setframerate(SR)
        w.writeframes(estereo.tobytes())


def generar(destino, progresion, bpm=100, cents=0.0, compases_intro=1, semilla=0):
    """Escribe guitar/bass/drums/piano/vocals/other.wav en `destino` y devuelve la
    referencia [{"inicio", "fin", "acorde"}] (un acorde por compás de 4/4)."""
    rng = np.random.default_rng(semilla)
    tiempo = 60.0 / bpm
    compas = 4 * tiempo
    n = int(((len(progresion) + compases_intro) * compas + 1.0) * SR)
    gtr, bajo, bat, piano, voz, resto = (np.zeros(n) for _ in range(6))
    referencia = []

    def sumar(pista, inicio, senal):
        a = int(inicio * SR)
        b = min(len(pista), a + len(senal))
        pista[a:b] += senal[:b - a]

    for i, acorde in enumerate(progresion):
        t0 = (i + compases_intro) * compas
        raiz, intervalos = _partir(acorde)
        referencia.append({"inicio": round(t0, 3), "fin": round(t0 + compas, 3), "acorde": acorde})
        for k in range(4):
            for j, iv in enumerate(intervalos):
                midi = 52 + ((raiz + iv - 4) % 12) + 12 * (j >= 2)
                sumar(gtr, t0 + k * tiempo + 0.01 * j, _tono(_hz(midi, cents), tiempo, 2.5) * 0.3)
            midi_bajo = 36 + raiz + (12 if raiz < 4 else 0)
            sumar(bajo, t0 + k * tiempo, _tono(_hz(midi_bajo, cents), tiempo * 0.9, 1.0, (1, .6, .3)))
        for k in (0, 2):
            for iv in intervalos:
                sumar(piano, t0 + k * tiempo, _tono(_hz(60 + (raiz + iv) % 12, cents), 2 * tiempo, 1.0, (1, .3, .1)) * 0.2)
    for c in range(len(progresion) + compases_intro):
        for k in range(8):
            t = c * compas + k * tiempo / 2
            if k in (0, 4):
                tt = np.arange(int(0.15 * SR)) / SR
                golpe = np.sin(2 * np.pi * (60 + 80 * np.exp(-tt * 30)) * tt) * np.exp(-tt * 20)
            elif k in (2, 6):
                golpe = rng.standard_normal(int(0.12 * SR)) * np.exp(-np.arange(int(0.12 * SR)) / SR * 30) * 0.6
            else:
                golpe = rng.standard_normal(int(0.04 * SR)) * np.exp(-np.arange(int(0.04 * SR)) / SR * 80) * 0.15
            sumar(bat, t, golpe)
    resto += rng.standard_normal(n) * 0.002
    voz += rng.standard_normal(n) * 0.001
    destino = Path(destino)
    destino.mkdir(parents=True, exist_ok=True)
    for nombre, x in [("guitar", gtr), ("bass", bajo), ("drums", bat), ("piano", piano),
                      ("vocals", voz), ("other", resto)]:
        _escribir(destino / f"{nombre}.wav", x)
    (destino / "_referencia.json").write_text(json.dumps(referencia))
    return referencia
