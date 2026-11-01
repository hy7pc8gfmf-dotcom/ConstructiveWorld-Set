@echo off
set "COQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq"
set "ROCQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq"
cd /d D:\ComplexAnalysis\新算法实践\attn\_tlw887_sbx
"C:\Rocq-Platform~9.1~2026.01\bin\coqtop.exe" -q -Q "D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo" "" < "D:\ComplexAnalysis\新算法实践\attn\_tlw887_sbx\_g3887probe.v" > "D:\ComplexAnalysis\新算法实践\attn\_tlw887_sbx\_repl887_g3.log" 2>&1
exit /b %ERRORLEVEL%
