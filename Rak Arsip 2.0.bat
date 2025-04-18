@echo off
set "PYTHON_PATH=%~dp0App\Python\python.exe"
if not exist "%PYTHON_PATH%" (
    exit /b 1
)

set "LAUNCHER_PATH=%~dp0Launcher.py"
if not exist "%LAUNCHER_PATH%" (
    exit /b 1
)

start /b "" "%PYTHON_PATH%" "%LAUNCHER_PATH%" > "%~dp0run.log" 2>&1