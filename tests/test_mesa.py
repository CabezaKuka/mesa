"""Pruebas de Mesa. Desde la carpeta del proyecto:

    python -m unittest discover tests

Necesitan numpy y flask (lo mismo que la app). Arman temas sintéticos en una carpeta
temporal, así que no tocan la biblioteca de verdad.
"""
import importlib.util
import json
import shutil
import sys
import tempfile
import time
import unittest
from pathlib import Path
from urllib.parse import quote

import numpy as np

RAIZ = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))
import sintetico  # noqa: E402


def _cargar_mesa():
    """La versión más nueva de appNNN.py que haya en la carpeta del proyecto."""
    candidatos = sorted(RAIZ.glob("app[0-9]*.py"), key=lambda p: int("".join(c for c in p.stem if c.isdigit())))
    spec = importlib.util.spec_from_file_location("mesa_bajo_prueba", candidatos[-1])
    modulo = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(modulo)
    return modulo


M = _cargar_mesa()
POP = ["C", "G", "Am", "F"] * 2 + ["Am", "Em", "F", "G"] + ["C", "G7", "C", "C"]


class ConBiblioteca(unittest.TestCase):
    """Biblioteca temporal con un tema sintético ya "separado"."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="mesa_prueba_"))
        cls._originales = {n: getattr(M, n) for n in ("OUTPUT_DIR", "UPLOAD_DIR", "ML_CACHE_DIR", "MEDICION_PATH",
                                                      "TRANSICIONES_PATH", "MODELO_ACORDES_PATH")}
        M.OUTPUT_DIR = cls.tmp / "separated"
        M.UPLOAD_DIR = cls.tmp / "uploads"
        M.ML_CACHE_DIR = cls.tmp / "ml_cache"
        M.MEDICION_PATH = M.ML_CACHE_DIR / "_medicion.json"
        M.TRANSICIONES_PATH = cls.tmp / "transiciones_acordes.json"
        M.MODELO_ACORDES_PATH = cls.tmp / "modelo_acordes.npz"   # sin modelo: detector por plantillas
        cls.tema = "Tema sintetico"
        cls.carpeta = M.OUTPUT_DIR / M.MODEL / cls.tema
        cls.referencia = sintetico.generar(cls.carpeta, POP, bpm=100)

    @classmethod
    def tearDownClass(cls):
        for nombre, valor in cls._originales.items():
            setattr(M, nombre, valor)
        shutil.rmtree(cls.tmp, ignore_errors=True)


class TestTextoDeAcordes(unittest.TestCase):
    def test_normalizar(self):
        self.assertEqual(M.normalizar_token("Bb"), ("A#", True))
        self.assertEqual(M.normalizar_token("ebm"), ("D#m", True))
        self.assertEqual(M.normalizar_token("."), (".", True))
        self.assertEqual(M.normalizar_token("Cmaj7"), ("Cmaj7", True))
        self.assertFalse(M.normalizar_token("H7")[1])
        self.assertFalse(M.normalizar_token("Cdim")[1])

    def test_texto_ida_y_vuelta(self):
        tokens = ["C", ".", ".", ".", "F#m", ".", "G7", "—"]
        texto = M._tokens_a_texto(tokens)
        self.assertEqual(M._texto_a_tokens(texto), tokens)
        # un "#" pegado es sostenido, separado es comentario
        self.assertEqual(M._texto_a_tokens("C# F#m | . . # comentario"), ["C#", "F#m", ".", "."])


class TestDetector(ConBiblioteca):
    def test_proyeccion_igual_a_la_compleja(self):
        """La proyección en float32 (v115) da lo mismo que la compleja de app114."""
        rng = np.random.default_rng(1)
        data = (rng.standard_normal(22050 * 5) * 0.1).astype(np.float32)
        nueva, _ = M._proyectar_notas(data, 22050)
        marcos = np.lib.stride_tricks.sliding_window_view(data, 8192)[::4096].astype(np.float64) * np.hanning(8192)
        base, _ = M._matriz_basis(8192, 22050)
        vieja = np.abs(marcos @ base.T)
        self.assertLess(float(np.abs(nueva - vieja).max() / vieja.max()), 1e-5)

    def test_acierta_el_tema_sintetico(self):
        c = self.carpeta
        seg = M.detectar_acordes(c / "guitar.wav", bajo_path=c / "bass.wav", stems_extra=[c / "piano.wav", c / "other.wav"])
        triada, _ = M._puntajes_tiempo(self.referencia, seg, seg[-1]["fin"])
        self.assertGreater(triada, 90.0)

    def test_variantes_no_rompen(self):
        c = self.carpeta
        prep = M._preparar_analisis(c / "guitar.wav", c / "bass.wav", [c / "piano.wav", c / "other.wav"])
        beats = M._detectar_pulso(c / "drums.wav")[0]
        conteos = M.conteos_transiciones(self.referencia)
        for variante in M.VARIANTES_DETECTOR:
            seg = M._detectar_desde_prep(prep, {variante}, beat_times=beats, transiciones=conteos)
            self.assertTrue(seg and all(s["fin"] >= s["inicio"] for s in seg), variante)

    def test_viterbi_con_costos_uniformes(self):
        """Con todos los cambios al mismo costo, la variante "transiciones" no cambia nada."""
        rng = np.random.default_rng(2)
        sim = rng.random((300, 36))
        costos = np.full((36, 36), 1.0)
        np.fill_diagonal(costos, 0.0)
        np.testing.assert_array_equal(M._viterbi(sim, 1.0), M._viterbi(sim, 1.0, costos))

    def test_tonalidad(self):
        chroma = np.zeros(12)
        for pc in (0, 2, 4, 5, 7, 9, 11):   # escala de do mayor
            chroma[pc] = 1.0
        chroma[0] += 1.0
        chroma[7] += 0.5
        tonica, modo, _r = M.estimar_tonalidad(chroma)
        self.assertEqual((M.NOTE_NAMES[tonica], modo), ("C", "mayor"))
        self.assertIn("G7", M.acordes_diatonicos(0, "mayor"))


class TestAnalisisYRutas(ConBiblioteca):
    def setUp(self):
        self.cliente = M.app.test_client()
        self.url = quote(self.tema)
        for nombre in ("acordes.txt", "acordes_grid.json", M.ANALISIS_ARCHIVO, M.CONFIANZA_ARCHIVO):
            (self.carpeta / nombre).unlink(missing_ok=True)
        shutil.rmtree(self.carpeta / M.RESPALDO_DIR, ignore_errors=True)

    def test_analisis_cacheado(self):
        t = time.time()
        r1 = self.cliente.get(f"/acordes/{self.url}").get_json()
        primero = time.time() - t
        self.assertTrue(r1["segmentos"])
        self.assertTrue((self.carpeta / M.ANALISIS_ARCHIVO).exists())
        self.assertTrue((self.carpeta / M.CONFIANZA_ARCHIVO).exists())
        # tempo: sale del análisis guardado, sin volver a detectar
        t = time.time()
        r2 = self.cliente.post(f"/tempo_acordes/{self.url}", json={"factor": 2.0}).get_json()
        self.assertLess(time.time() - t, primero)
        self.assertAlmostEqual(r2["bpm"], r1["bpm"] * 2, delta=1.0)
        self.assertTrue(r2.get("hay_respaldo"))

    def test_deshacer(self):
        original = self.cliente.get(f"/acordes/{self.url}").get_json()
        self.cliente.post(f"/tempo_acordes/{self.url}", json={"factor": 0.5})
        vuelta = self.cliente.post(f"/deshacer_acordes/{self.url}").get_json()
        self.assertEqual(vuelta["bpm"], original["bpm"])
        self.assertEqual(self.cliente.post(f"/deshacer_acordes/{self.url}").status_code, 404)

    def test_grilla_con_confianza(self):
        self.cliente.get(f"/acordes/{self.url}")
        g = self.cliente.get(f"/grilla/{self.url}").get_json()
        self.assertEqual(len(g["confianza"]), g["posiciones_esperadas"])
        self.assertTrue(all(len(a) == 3 for a in g["alternativas"]))

    def test_paginas(self):
        self.cliente.get(f"/acordes/{self.url}")
        for ruta in ("/", f"/mesa/{self.url}", f"/hoja/{self.url}", "/sw.js"):
            self.assertEqual(self.cliente.get(ruta).status_code, 200, ruta)

    def test_post_de_otro_sitio(self):
        r = self.cliente.post(f"/borrar/{self.url}", headers={"Origin": "https://malicioso.example"})
        self.assertEqual(r.status_code, 403)
        self.assertTrue(self.carpeta.exists())
        ok = self.cliente.post(f"/capo/{self.url}", json={"capo": 0}, headers={"Origin": "http://localhost"})
        self.assertNotEqual(ok.status_code, 403)

    def test_medir_variantes(self):
        (self.carpeta / "acordes_midi.json").write_text(json.dumps({"segmentos": self.referencia}))
        try:
            M._medir_variantes()
            resultado = M.ultima_medicion()
            self.assertIsNotNone(resultado, M._medicion.get("error"))
            filas = {f["variante"]: f for f in resultado["filas"]}
            self.assertEqual(set(filas), {"actual", "todas", *M.VARIANTES_DETECTOR})
            self.assertGreater(filas["actual"]["triada"], 90.0)
            self.assertTrue(M.TRANSICIONES_PATH.exists())
        finally:
            (self.carpeta / "acordes_midi.json").unlink(missing_ok=True)


if __name__ == "__main__":
    unittest.main()
