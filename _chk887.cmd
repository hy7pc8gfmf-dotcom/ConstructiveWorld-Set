@echo off
set "COQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq"
set "ROCQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq"
"C:\Rocq-Platform~9.1~2026.01\bin\coqchk.exe" -o -Q "D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo" "" -Q "D:\ComplexAnalysis\新算法实践\Live_X" Local Local.LW0LeibSeparation LW2TrigBridge LW1PiMeasure > "D:\ComplexAnalysis\ConstructiveWorld-Main\_chk887.log" 2>&1
exit /b %ERRORLEVEL%
