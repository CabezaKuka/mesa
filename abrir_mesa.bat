@echo off
rem Abre la version mas nueva de Mesa (el appNNN.py con el numero mas alto) con el Python de .venv.
rem Se le pueden pasar los mismos argumentos que a la app, por ejemplo: abrir_mesa.bat --browser
setlocal enabledelayedexpansion
cd /d "%~dp0"
if not exist ".venv\Scripts\python.exe" (
  echo Mesa todavia no esta instalada en esta PC: corre primero instalar_mesa.bat
  pause
  exit /b 1
)
set "APP="
set /a MEJOR=-1
for %%F in (app*.py) do (
  set "NOMBRE=%%~nF"
  set "NUM=!NOMBRE:app=!"
  set /a V=-1
  set /a V=!NUM! 2>nul
  if !V! GTR !MEJOR! (
    set /a MEJOR=!V!
    set "APP=%%F"
  )
)
if not defined APP (
  echo No encuentro ningun appNNN.py en %CD%
  pause
  exit /b 1
)
title Mesa - !APP!
".venv\Scripts\python.exe" "!APP!" %*
if errorlevel 1 pause
