@echo off
cd /d D:\ComplexAnalysis\ConstructiveWorld-Set\ConstructiveWorld_Live
set "COQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq"
set "ROCQLIB=C:\Rocq-Platform~9.1~2026.01\lib\coq"
"C:\Progra~1\Git\bin\bash.exe" -e "D:\ComplexAnalysis\ConstructiveWorld-Set\build.sh" > "D:\ComplexAnalysis\ConstructiveWorld-Set\ConstructiveWorld_Live\_seg2_build_1506.log" 2>&1
> "D:\ComplexAnalysis\ConstructiveWorld-Set\ConstructiveWorld_Live\_exit_seg2build_1506.txt" echo BUILD_EXIT=%ERRORLEVEL%
