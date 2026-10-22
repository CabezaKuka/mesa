@echo off
rem Instala Mesa en esta PC: doble clic aca. Se puede volver a correr para reparar o actualizar.
cd /d "%~dp0"
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0instalar_mesa.ps1"
echo.
pause
