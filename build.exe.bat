@echo off
cd /d "%~dp0"
if not exist .venv (
  py -m venv .venv
)
call .venv\Scripts\activate.bat
python -m pip install --upgrade pip
pip install -r requirements.txt
if exist build rmdir /s /q build
if exist dist rmdir /s /q dist
pyinstaller --noconfirm --clean --windowed --name "HX - Hyper eXchange" --icon "HXLAB\resources\hx_hand.ico" --add-data "HXLAB\resources\hx_hand.ico;HXLAB\resources" main.py
if exist "dist\HX - Hyper eXchange\HX - Hyper eXchange.exe" (
  echo.
  echo Build complete: dist\HX - Hyper eXchange\HX - Hyper eXchange.exe
) else (
  echo.
  echo Build failed. Check output above.
)
pause
