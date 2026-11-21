(* ===================================================================== *)
(* zz_prrun_ext_lcm — extraction driver for the LCM/primality witness     *)
(* chain (executable-face artifact, not a library module).                *)
(* Mission. Expose the executable core of the LCM machinery to OCaml for  *)
(*   RunAlive witness runs: [plw_maxpow] (largest exponent w with         *)
(*   p ^ w <= n, first-order nat Fixpoint; its body repeats the recursive *)
(*   call at every level, so direct evaluation costs Theta(2^n) — keep    *)
(*   witness samples at n <= 22), [HansonLcm.hl_binom] (Pascal-recursion  *)
(*   binomial coefficients), [HansonLcm.hl_lcm_upto] (folding lcm         *)
(*   machine) and [abl_Pr_core_01.pr_prime_bool] (boolean primality       *)
(*   reflector).  This file states no propositions and declares no new    *)
(*   objects of its own; it only drives the extraction.                   *)
(* Dependencies. HansonLcm, u5c_pr_lcm_absorb (read-only Require) and     *)
(*   Stdlib Extraction.  All four extracted objects are first-order       *)
(*   nat/bool Fixpoints or Definitions, so the extracted face carries     *)
(*   no propositions.                                                     *)
(* References. [hl_binom]/[hl_lcm_upto] with their divisibility bounds in *)
(*   HansonLcm; [pr_prime_bool] with its two-way spec in abl_Pr_core_01.  *)
(* Constructivity. Extraction face only: every extracted carrier is Set   *)
(*   (nat/bool), no axioms, no proof termination, no classical imports.   *)
(* Build. coqc -Q <ConstructiveWorld_Live> "" -o zz_prrun_ext_lcm.vo      *)
(*   zz_prrun_ext_lcm.v; extraction output lands in ./mlcm.               *)
(* ===================================================================== *)

From Stdlib Require Import Extraction.
Set Extraction Output Directory "mlcm".
Require Import HansonLcm.
Require Import u5c_pr_lcm_absorb.
Separate Extraction plw_maxpow
                   HansonLcm.hl_binom
                   HansonLcm.hl_lcm_upto
                   abl_Pr_core_01.pr_prime_bool.
