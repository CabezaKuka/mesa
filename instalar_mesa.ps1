# Instala Mesa en esta PC (Windows 10/11). Lo corre instalar_mesa.bat; se puede volver a correr
# para reparar o actualizar: lo que ya está instalado no se vuelve a bajar.
#
# Qué se baja de internet: uv (que trae su propio Python, así que no hace falta tener Python
# instalado), PyTorch y las librerías de Mesa (quedan dentro de esta carpeta, en .venv),
# ffmpeg y Deno (con winget, para el usuario) y el modelo de Demucs (una sola vez).

$ErrorActionPreference = "Stop"
$ProgressPreference = "SilentlyContinue"
Set-Location -LiteralPath $PSScriptRoot

$TORCH = "2.7.1"      # con torchaudio de la misma versión; probado con demucs 4.0.1
$PYTHON = "3.12"

function Paso([string]$texto) { Write-Host ""; Write-Host "==> $texto" -ForegroundColor Cyan }
function Ok([string]$texto) { Write-Host "    $texto" -ForegroundColor Green }
function Aviso([string]$texto) { Write-Host "    $texto" -ForegroundColor Yellow }
function Hay([string]$comando) { [bool](Get-Command $comando -ErrorAction SilentlyContinue) }
function RefrescarPath {
    # lo que instalan uv y winget queda en el PATH del usuario, que esta consola todavía no ve
    $env:Path = [Environment]::GetEnvironmentVariable("Path", "Machine") + ";" +
                [Environment]::GetEnvironmentVariable("Path", "User") + ";" +
                (Join-Path $env:USERPROFILE ".local\bin")
}
function Correr([string]$exe, [string[]]$argumentos) {
    & $exe @argumentos
    if ($LASTEXITCODE -ne 0) { throw "falló: $exe $($argumentos -join ' ')" }
}

try {
    Write-Host "Instalador de Mesa" -ForegroundColor White
    $apps = Get-ChildItem -File -Filter "app*.py" | Where-Object { $_.BaseName -match '^app\d+$' }
    if (-not $apps) { throw "no encuentro ningún appNNN.py: corré el instalador desde la carpeta de Mesa" }
    if (-not (Test-Path "templates")) { throw "falta la carpeta 'templates' al lado de la app" }
    # archivos bajados de internet (zip): sin la marca de "descargado", Windows no pregunta por cada uno
    Get-ChildItem -Recurse -File | Unblock-File -ErrorAction SilentlyContinue

    Paso "1/6  uv (instala Python y las librerías sin tocar el resto de la PC)"
    RefrescarPath
    if (-not (Hay "uv")) {
        Invoke-RestMethod "https://astral.sh/uv/install.ps1" | Invoke-Expression
        RefrescarPath
    }
    if (-not (Hay "uv")) { throw "no se pudo instalar uv" }
    Ok (uv --version)

    Paso "2/6  Python $PYTHON en un entorno propio de Mesa (.venv)"
    if (-not (Test-Path ".venv\Scripts\python.exe")) { Correr "uv" @("venv", "--python", $PYTHON, ".venv") }
    $py = (Resolve-Path ".venv\Scripts\python.exe").Path
    Ok (& $py --version)

    Paso "3/6  PyTorch $TORCH (lo que usa Demucs para separar)"
    $indice = "cpu"
    if (Hay "nvidia-smi") {
        try {
            $placa = & nvidia-smi --query-gpu=name,compute_cap --format=csv,noheader | Select-Object -First 1
            Ok "Placa NVIDIA: $placa"
            # las RTX 50 (Blackwell, compute 12.x) necesitan la versión hecha con CUDA 12.8;
            # la de CUDA 12.6 cubre todas las anteriores, incluidas las GTX 10
            $computo = [double](($placa -split ",")[-1].Trim())
            $indice = if ($computo -ge 10.0) { "cu128" } else { "cu126" }
        } catch { $indice = "cu126" }
    } else {
        Aviso "No hay placa NVIDIA: Demucs va a usar el procesador (anda igual, pero tarda más)."
    }
    $instalado = $false
    foreach ($idx in (@($indice, "cu126", "cpu") | Select-Object -Unique)) {
        try {
            Correr "uv" @("pip", "install", "--python", $py, "torch==$TORCH", "torchaudio==$TORCH",
                          "--index-url", "https://download.pytorch.org/whl/$idx")
            Ok "PyTorch listo ($idx)"
            $instalado = $true
            break
        } catch {
            Aviso "No se pudo con '$idx', pruebo otra variante…"
        }
    }
    if (-not $instalado) { throw "no se pudo instalar PyTorch" }

    Paso "4/6  Librerías de Mesa (Demucs, Flask, yt-dlp, ventana, pedalera, gafas)"
    # la restricción evita que se reemplace el PyTorch del paso anterior por otro
    Set-Content -Encoding ascii -Path ".venv\restricciones.txt" -Value "torch==$TORCH`r`ntorchaudio==$TORCH"
    Correr "uv" @("pip", "install", "--python", $py, "-r", "requisitos.txt", "-c", ".venv\restricciones.txt")
    Ok "listo"

    Paso "5/6  ffmpeg y Deno (para preparar el audio y para bajar de YouTube)"
    RefrescarPath
    if (Hay "winget") {
        if (-not (Hay "ffmpeg")) {
            & winget install -e --id Gyan.FFmpeg --accept-source-agreements --accept-package-agreements
            RefrescarPath
        }
        if (-not (Hay "deno")) {
            & winget install -e --id DenoLand.Deno --accept-source-agreements --accept-package-agreements
            RefrescarPath
        }
    } else {
        Aviso "Esta PC no tiene winget: instalá ffmpeg a mano (https://www.gyan.dev/ffmpeg/builds/) y agregalo al PATH."
    }
    if (Hay "ffmpeg") { Ok "ffmpeg: ok" } else { Aviso "ffmpeg todavía no aparece: cerrá la sesión de Windows y volvé a entrar (o reiniciá)." }
    if (Hay "deno") { Ok "Deno: ok" } else { Aviso "Sin Deno, algunos videos de YouTube pueden fallar (separar un mp3 anda igual)." }

    Paso "6/6  Modelo de Demucs (unos cientos de MB, una sola vez) y acceso directo"
    try {
        $env:TORCH_FORCE_NO_WEIGHTS_ONLY_LOAD = "1"
        Correr $py @("-c", "from demucs.pretrained import get_model; get_model('htdemucs_6s'); print('    modelo listo')")
    } catch {
        Aviso "No se pudo bajar el modelo ahora: se baja solo la primera vez que separes un tema."
    }
    # sin acceso directo Mesa anda igual (abrir_mesa.bat): que esto no tire abajo la instalación
    try {
        $escritorio = [Environment]::GetFolderPath("Desktop")
        $shell = New-Object -ComObject WScript.Shell
        $acceso = $shell.CreateShortcut((Join-Path $escritorio "Mesa.lnk"))
        $acceso.TargetPath = Join-Path $PSScriptRoot "abrir_mesa.bat"
        $acceso.WorkingDirectory = $PSScriptRoot
        if (Test-Path "mesa.ico") { $acceso.IconLocation = Join-Path $PSScriptRoot "mesa.ico" }
        $acceso.WindowStyle = 7          # la consola arranca minimizada; la app abre su propia ventana
        $acceso.Description = "Mesa - separador de pistas"
        $acceso.Save()
        Ok "Acceso directo 'Mesa' en el escritorio"
    } catch {
        Aviso "No pude crear el acceso directo ($($_.Exception.Message)): abrí Mesa con abrir_mesa.bat."
    }

    Write-Host ""
    Write-Host "Mesa quedó instalada. Abrila con el acceso directo 'Mesa' del escritorio." -ForegroundColor Green
    Write-Host "La primera vez, Windows pregunta si deja que Mesa use la red: elegí 'red privada'." -ForegroundColor Green
} catch {
    Write-Host ""
    Write-Host "No se pudo terminar la instalación: $($_.Exception.Message)" -ForegroundColor Red
    Write-Host "Volvé a correr instalar_mesa.bat: sigue desde donde quedó." -ForegroundColor Yellow
    exit 1
}
