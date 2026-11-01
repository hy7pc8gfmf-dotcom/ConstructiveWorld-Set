@echo off
setlocal
set "COQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq"
set "ROCQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq"
cd /d D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo
"C:\Rocq-Platform~9.1~2026.01\bin\coqchk.exe" -o -Q . "" LW0PiIrrational > D:\ComplexAnalysis\ConstructiveWorld-Main\_chk853.log 2>&1
exit /b %ERRORLEVEL%
