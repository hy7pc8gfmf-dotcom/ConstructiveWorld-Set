@echo off
set "COQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq"
set "ROCQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq"
cd /d D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo
"C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe" -q -native-compiler no -Q . "" LW1PiMeasure.v > "D:\ComplexAnalysis\ConstructiveWorld-Main\_born887b.log" 2>&1
exit /b %ERRORLEVEL%
