(* ============================================================
   模块名: b1_extract4
   数学使命: b1_linform_machine 连分式收敛子机五个常量的
     Separate Extraction 驱动（零语句件），输出目录 extract4/。
   依赖清单: b1_linform_machine; Stdlib Extraction。
   构造性注记: 本件无语句定义; 提取目标常量出自已证 Set 承载件。
   编译配方: rocq c -native-compiler no -q -Q . "" b1_extract4.v。
   ============================================================ *)

Require Import b1_linform_machine.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "extract4".

Separate Extraction b1cfP b1cfQ b1cf_p b1cf_q b1cf_detT.
