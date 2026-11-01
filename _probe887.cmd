@echo off
set "COQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq"
set "ROCQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq"
cd /d D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo
"C:\Rocq-Platform~9.1~2026.01\bin\coqtop.exe" -q -Q . "" < "D:\ComplexAnalysis\ConstructiveWorld-Main\_probe887_in.v" > "D:\ComplexAnalysis\ConstructiveWorld-Main\_probe887.log" 2>&1
exit /b %ERRORLEVEL%
