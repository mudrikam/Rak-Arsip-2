@echo off
set "PYTHON_PATH=%~dp0App\Python\pythonw.exe"
if not exist "%PYTHON_PATH%" (
    echo Portable Python tidak ditemukan di folder aplikasi.
    exit /b 1
)

set "LAUNCHER_PATH=%~dp0Launcher.py"
if not exist "%LAUNCHER_PATH%" (
    echo File Launcher.py tidak ditemukan di folder aplikasi.
    exit /b 1
)

echo Menjalankan Rak Arsip...
start /b "" "%PYTHON_PATH%" "%LAUNCHER_PATH%"
