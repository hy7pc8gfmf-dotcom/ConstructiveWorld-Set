(* ConstructiveWorld-Set — extraction driver for the continued-fraction constants. *)

(** * b1_extract4: Separate Extraction driver for five constants of
      [b1_linform_machine].

    Mission.  A zero-statement driver: it runs [Separate Extraction] on
      the five continued-fraction convergent constants [b1cfP], [b1cfQ],
      [b1cf_p], [b1cf_q], [b1cf_detT] of [b1_linform_machine] and writes
      the output into the directory [extract4].

    Dependencies.  [b1_linform_machine] of this development; Stdlib
      [Extraction].

    References.  This development, [b1_linform_machine].v, the baseline
      module in ConstructiveWorld-Main whose constant names are carried
      over here verbatim.

    Constructivity.  This file defines no statements; the extracted
      constants come from the proven Set-carried module
      [b1_linform_machine].

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      b1_extract4.v] compiles cleanly (exit 0); the first eight bytes
      of the artifact are [436f7121 00015ff4]. *)

Require Import b1_linform_machine.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "extract4".

Separate Extraction b1cfP b1cfQ b1cf_p b1cf_q b1cf_detT.
