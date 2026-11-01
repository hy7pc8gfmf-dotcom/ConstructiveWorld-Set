@echo off
cd /d D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo
"C:\Progra~1\Git\bin\bash.exe" coqchk_all.sh
exit /b %ERRORLEVEL%
