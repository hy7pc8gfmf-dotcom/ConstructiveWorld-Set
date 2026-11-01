#!/bin/bash
# EX-CONSOL-FIN3: resume build to fixpoint after FIN2 wedged at S14
# SW2 verbatim env; COQC full path (EXIT=127 guard); file redirection only.
export COQC="C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe"
export COQLIB="C:/Rocq-Platform~9.1~2026.01/lib/coq"
export ROCQLIB="C:/Rocq-Platform~9.1~2026.01/lib/coq"
cd /d/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo || { echo "CD_FAIL"; exit 90; }
bash build.sh > _fin3_build_run.log 2>&1
e=$?
echo "BUILD_EXIT=$e" >> _fin3_build_run.log
echo "FIN3_BUILD_DONE" >> _fin3_build_run.log
exit $e
