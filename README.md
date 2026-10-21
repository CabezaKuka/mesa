# Mesa — separador de pistas para practicar

**[English below](#english)**

Mesa es una aplicación local para practicar guitarra (o voz) **tocando encima de la grabación original**. Separa cualquier tema en pistas con inteligencia artificial, detecta los acordes y el pulso, y te deja mutear tu instrumento mientras ves los acordes sincronizados en pantalla.

Corre en tu PC, sin servidores externos ni suscripciones. Se puede usar desde la misma PC o desde una tablet o celular en la misma red, por ejemplo apoyada en el atril durante un ensayo.

---

## Qué hace

### Separación de pistas
- Subís un mp3 o pegás un link de YouTube, y Mesa lo separa en **6 pistas** con [Demucs](https://github.com/facebookresearch/demucs) (`htdemucs_6s`): voz, batería, bajo, guitarra, piano y resto.
- Durante el proceso muestra el porcentaje real y el tiempo estimado.

### Mezclador
- Volumen y mute independientes por pista, más un modo **guía** (la guitarra queda sonando bajita, para chequearte contra la grabación).
- Fader **Master** del dispositivo que está sonando.
- La mezcla se guarda por canción.

### Acordes sincronizados
- **Detección automática** de acordes (mayores, menores y séptimas) y del pulso del tema, agrupados en compases de 4/4. Se hace apenas termina la separación, así el tema abre listo.
- Hay dos detectores:
  - por plantillas (chroma + Viterbi);
  - **uno aprendido** (red neuronal chica en numpy), que se entrena con un botón usando tus propios MIDI importados.
- **Mejoras experimentales** del detector por plantillas (decidir por tiempos del pulso, tonalidad, inversiones, transiciones aprendidas…), apagadas por defecto: un botón las **mide contra tus MIDI** y prendés las que ganan.
- **Importación de MIDI** (por ejemplo, los de Chordify) para tener los acordes exactos.
- **Editor** de acordes por compás, que acepta además maj7 y sus4. Marca con **?** los compases donde el detector dudó y ofrece sus otros candidatos de un toque.
- **Deshacer** después de regenerar, importar un MIDI o corregir el tempo.
- Sincronía fina (también **tocando al ritmo**), corrección de tempo (×2 / ÷2 / BPM exacto / **tap tempo**) y sugerencia de **cejilla**. Si el pulso puede ir al doble o a la mitad, Mesa pregunta.
- Cartel grande con el acorde actual y el siguiente, diagramas del mástil, grados armónicos (I–IV–V…) y una barra de duración del acorde coloreada según su largo.
- Vista **cinta**, con los compases desplazándose bajo un cabezal fijo, y **próximos compases** debajo del cartel cuando sobra lugar (tablet en vertical, monitor).
- **Marcas de cambio de rasgueo**, que avisan antes de que llegue el cambio.
- **Hoja de acordes para imprimir** o guardar como PDF.

### Para estudiar
- **Loop A-B** ajustado a compases, con claqueta de entrada en cada vuelta.
- Cuenta regresiva 4-3-2-1 y navegación compás por compás.
- **Atajos de teclado** (tecla `?` para verlos). Las **pedaleras Bluetooth para pasar páginas** (flechas o RePág/AvPág) cambian de compás sin tocar la pantalla.

### Biblioteca y setlists
- Biblioteca con búsqueda, títulos y autores editables.
- **Setlists** que pasan solos al tema siguiente.

### En la tablet
- **App instalable (PWA)** en Android.
- Pantalla pensada para la tablet en el atril: en vertical, el cartel ocupa todo el ancho. Mantené apretado cualquier botón para ver qué hace.
- **Modo sin conexión**: los temas descargados se tocan aunque la tablet no llegue a la PC.
- Modo claro y modo oscuro, y color de la app a elección.

### Accesorios opcionales
- **Pedalera física** con Arduino por USB: mute de guitarra, volumen ± y play/pausa.
- **Gafas HUD** (ESP32-C3 + OLED) que muestran el acorde actual. Funcionan por WiFi (UDP) o por Bluetooth LE, desde la PC o directamente desde la tablet.

---

## Requisitos

- **Windows 10/11** (es donde se desarrolla y prueba; el núcleo es Python y debería andar en Linux/macOS, sin garantías).
- **Python 3.10 o más nuevo**.
- **ffmpeg** instalado y en el `PATH`.
- Una GPU NVIDIA acelera mucho a Demucs, pero no es obligatoria: con CPU anda, más lento.

### Dependencias de Python

```bash
pip install flask numpy demucs "yt-dlp[default]" mido pywebview
```

Opcionales:

| Paquete | Para qué |
|---|---|
| `pyserial` | Pedalera física por USB |
| `bleak` | Gafas HUD por Bluetooth desde la PC (requiere el módulo `hud_ble.py`) |
| `cryptography` | Avisar cuando el certificado HTTPS está por vencer |

Para descargar de YouTube conviene instalar también **Deno** (`winget install DenoLand.Deno`): sin un motor de JavaScript, YouTube entrega menos formatos y algunas descargas fallan.

---

## Uso

```bash
python app115.py
```

(Cada versión es un `appNNN.py`; la pantalla de inicio muestra el número. Desde la 115, el HTML de cada pantalla vive en la carpeta `templates/`, que tiene que estar al lado.)

Abre Mesa en una ventana propia. Para usarla en una pestaña del navegador:

```bash
python app115.py --browser
```

y entrá a `http://127.0.0.1:5000`.

La **primera separación** descarga el modelo de Demucs (unos cientos de MB). Después todo corre localmente.

### Desde una tablet o celular

En la misma red WiFi, abrí `http://<IP-de-la-PC>:5000` (la IP aparece en la consola al arrancar). La primera vez, Windows pregunta si permite la conexión: elegí *red privada*.

Para **instalarla como app**, usar el **modo sin conexión** o conectar las **gafas por Bluetooth desde la tablet**, el navegador exige HTTPS. La forma más simple es con [Tailscale](https://tailscale.com/):

```bash
tailscale cert <tu-maquina>.<tu-tailnet>.ts.net
```

Mesa busca sola el `*.ts.net.crt` (con su `.key` al lado) en su propia carpeta y en `C:\Windows\System32`. Si lo guardaste en otro lado, indicale dónde:

```bash
set MESA_TLS_CERT=C:\ruta\a\<tu-maquina>.<tu-tailnet>.ts.net.crt
set MESA_TLS_KEY=C:\ruta\a\<tu-maquina>.<tu-tailnet>.ts.net.key
```

Mesa levanta un segundo servidor HTTPS en el puerto 443, así que en la tablet se entra a `https://<tu-maquina>.<tu-tailnet>.ts.net`. Si `tailscale serve` está usando el 443, apagalo con `tailscale serve --https=443 off`.

### Variables de entorno

| Variable | Valor por defecto | Para qué |
|---|---|---|
| `MESA_TLS_CERT` / `MESA_TLS_KEY` | búsqueda automática | Certificado y clave para HTTPS |
| `MESA_PEDAL_PORT` | detección automática | Puerto del pedal (`COM5`), u `off` para desactivarlo |
| `MESA_PEDAL_BAUD` | `115200` | Velocidad del puerto serie del pedal |
| `MESA_HUD_PORT` | `4211` | Puerto UDP de las gafas HUD |

---

## Pedalera (opcional)

Un Arduino (Nano o similar) conectado por USB manda una línea de texto por evento a 115200 baudios:

| Línea | Acción |
|---|---|
| `MUTE:guitarra` / `UNMUTE:guitarra` | Mute de la guitarra |
| `VOL_UP` / `VOL_DOWN` | Fader Master ±10 % |
| `PLAY_PAUSE` | Reproducir / pausar |

Mesa detecta sola la placa (chips Arduino, CH340, FTDI y CP210x) y se reconecta si la desenchufás con la app abierta.

## Gafas HUD (opcional)

Mesa envía el acorde actual, el siguiente, el tiempo dentro del compás y algunos datos de pantalla (título, cuenta regresiva, cejilla, brillo) como un JSON corto:

- **Por WiFi:** broadcast UDP.
- **Por Bluetooth LE:** servicio `6e6d0001-b5a3-f393-e0a9-e50e24dcca9e`, característica `6e6d0002-…`, nombre `MesaHUD`.

El firmware de las gafas no está incluido en este repositorio.

---

## Dónde guarda las cosas

Todo queda junto a `app115.py`:

```
templates/                    HTML, CSS y JS de cada pantalla
uploads/                      mp3 originales
separated/htdemucs_6s/<tema>/
    *.wav, *.mp3              pistas separadas
    acordes.txt               acordes por compás (editable a mano)
    acordes_grid.json         pulso, BPM, sincronía, cejilla
    acordes_analisis.npz      análisis guardado (acordes, pulso, puntajes)
    acordes_confianza.json    qué tan seguro estaba el detector en cada tiempo
    .respaldo/                copia para "Deshacer" la última operación
    mezcla.json               volumen y mute de cada pista
    rasgueo_marcas.json       marcas de cambio de rasgueo
modelo_acordes.npz            detector aprendido (si lo entrenaste)
transiciones_acordes.json     transiciones aprendidas de tus MIDI (al medir)
```

`acordes.txt` es texto plano: 4 posiciones por compás separadas por `|`. Un `.` significa "sigue el acorde anterior".

---

## Pruebas

```bash
python -m unittest discover tests
```

Arman temas sintéticos en una carpeta temporal (no tocan tu biblioteca) y revisan el detector, el análisis guardado, deshacer y las páginas. Los temas sintéticos son mucho más fáciles que una grabación: sirven para ver que nada se rompió, no para medir mejoras del detector (para eso está «Medir con mis MIDI»).

---

## Limitaciones conocidas

- Asume compás de 4/4 y tempo constante en todo el tema.
- El detector automático solo propone acordes mayores, menores y séptimas. Los maj7 y sus4 se agregan a mano o vienen de un MIDI importado.
- Sin batería en la mezcla no hay pulso detectable: los acordes se muestran igual, pero sin grilla de compases.
- Descargar de YouTube depende de `yt-dlp` y de los cambios que YouTube hace del otro lado. Si deja de andar, actualizá con `pip install -U "yt-dlp[default]"`.

---

## Licencia

Podés **ver y usar** Mesa libremente para uso personal. **No está permitido modificarla ni redistribuir versiones modificadas.** Ver el archivo `LICENSE`.

Mesa usa [Demucs](https://github.com/facebookresearch/demucs) (Meta, licencia MIT) y [yt-dlp](https://github.com/yt-dlp/yt-dlp) (Unlicense). Descargá y separá solo material que tengas derecho a usar.

---

<a name="english"></a>

# Mesa — stem separator for practice (English)

Mesa is a local app for practicing guitar (or vocals) **by playing over the original recording**. It splits any song into stems with AI, detects chords and beats, and lets you mute your instrument while following synced chords on screen. It runs on your own PC with no external servers or subscriptions, and can be used from the PC itself or from a tablet or phone on the same network.

## Features

- **Stem separation** of an mp3 or a YouTube link into 6 stems (vocals, drums, bass, guitar, piano, other) with Demucs `htdemucs_6s`.
- **Mixer** with per-stem volume, mute and a low-level "guide" mode, plus a per-device master fader. The mix is saved per song.
- **Automatic chord and beat detection**: a template-based detector and an optional learned detector that you train with one click from your own imported MIDI files.
- **MIDI chord import** (e.g. from Chordify) and a per-bar chord editor.
- **Chord display**: current and next chord, fretboard diagrams, harmonic degrees, capo suggestion, scrolling "tape" view and strumming-change markers.
- **Printable chord sheet** (print or save as PDF).
- **Practice tools**: bar-snapped A-B looping with count-in clicks, 4-3-2-1 countdown and bar-by-bar navigation.
- **Library and setlists** with auto-advance to the next song.
- **Installable PWA** with offline playback of downloaded songs, and light/dark themes.
- **Optional hardware**: an Arduino USB foot pedal and an ESP32-C3 HUD glasses display (WiFi UDP or Bluetooth LE).

## Requirements

Windows 10/11, Python 3.10+, and ffmpeg on `PATH`. An NVIDIA GPU is recommended but optional.

```bash
pip install flask numpy demucs "yt-dlp[default]" mido pywebview
```

Optional packages: `pyserial` (pedal), `bleak` (HUD over Bluetooth from the PC), `cryptography` (certificate expiry warning). Deno is recommended for YouTube downloads.

## Running

```bash
python app115.py              # native window
python app115.py --browser    # then open http://127.0.0.1:5000
```

From another device on the same network, open `http://<PC-IP>:5000`.

PWA install, offline mode and Web Bluetooth require HTTPS:
1. Generate a certificate with `tailscale cert`.
2. Point `MESA_TLS_CERT` and `MESA_TLS_KEY` to the generated files.
3. Mesa serves HTTPS on port 443.

See the Spanish section above for environment variables, the pedal protocol and the file layout.

## Known limitations

- Assumes 4/4 time and a constant tempo.
- The detector proposes only major, minor and dominant 7th chords.
- No beat grid without a drum stem.
- YouTube downloads depend on yt-dlp keeping up with YouTube changes.

## License

You may **view and use** Mesa for personal use. **Modifying it or redistributing modified versions is not allowed.** See `LICENSE`.

Mesa relies on Demucs (MIT) and yt-dlp (Unlicense). Only download and separate material you have the right to use.
