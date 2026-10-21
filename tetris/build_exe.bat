@echo off
chcp 65001 >nul
rem Собирает release\Тетрис.exe — одну программу, которую можно отправить другу.
rem Фото из папки photos уменьшаются и встраиваются внутрь .exe.
cd /d "%~dp0"
py tetris.py --prepare-photos "%TEMP%\tetris_build\photos"
if errorlevel 1 (echo Не удалось подготовить фото & pause & exit /b 1)
py -m PyInstaller --noconfirm --onefile --windowed --name "Тетрис" --icon "%~dp0tetris.ico" --version-file "%~dp0version_info.txt" --exclude-module numpy --exclude-module tkinter --exclude-module pkg_resources --exclude-module setuptools --add-data "%TEMP%\tetris_build\photos;photos" --workpath "%TEMP%\tetris_build" --specpath "%TEMP%\tetris_build" --distpath "%~dp0release" tetris.py
echo.
if errorlevel 1 (echo Сборка не удалась) else (echo Готово: release\Тетрис.exe)
pause
