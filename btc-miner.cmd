@echo off
setlocal
cd /d "%~dp0"
set PYTHONUTF8=1
set PYTHONDONTWRITEBYTECODE=1
if not exist ".venv\Scripts\python.exe" (
  echo Run setup.ps1 first.
  exit /b 1
)
".venv\Scripts\python.exe" -m btcminer %*
exit /b %errorlevel%
