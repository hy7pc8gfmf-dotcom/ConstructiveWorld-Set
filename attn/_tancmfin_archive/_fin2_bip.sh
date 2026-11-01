#!/bin/bash
# EX-CONSOL-FIN2 born-in-place UpReqMinPKLChain
set -e
cd "$(dirname "$0")"
export COQLIB="C:/Rocq-Platform~9.1~2026.01/lib/coq" ROCQLIB="C:/Rocq-Platform~9.1~2026.01/lib/coq"
"C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe" -native-compiler no -Q . "" UpReqMinPKLChain.v
