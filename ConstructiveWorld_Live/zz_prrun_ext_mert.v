(* zz_prrun_ext_mert: extraction driver for the Mertens-type chain of the
   natural-number domain (divergence of the sum of prime reciprocals).

   Mission.  Issue the extraction commands that turn the named surface of
   u5c_pr_mertens_nat into OCaml sources under the mmert/ output
   directory: the main divergence statement pzs_prime_recip_diverge (a
   sigT-witnessed record carrying decidable NatLebT evidence), the
   remainder-sum function pzs_rsum, the lower-bound constant function
   pzs_B, and the boolean primality decider abl_Pr_core_01.pr_prime_bool.
   The module itself declares no statements.

   Dependencies.  Stdlib Extraction (imported explicitly, since the
   Require below does not load it transitively); u5c_pr_mertens_nat
   (read-only; it in turn imports abl_Pr_core_01).

   References.  The nat-domain divergence chain: u5c_pr_mertens_nat and
   its primality foundation abl_Pr_core_01.

   Constructivity.  Every extracted name is Set-carried in its home
   module: pzs_prime_recip_diverge is a sigT record whose evidence
   positions use NatLebT (Id (Nat.leb a b) true) and the Set-level pair
   And := A * B; pzs_rsum and pzs_B are nat-valued definitions;
   pr_prime_bool is a nat -> bool definition.  The extraction output is
   therefore expected free of Obj.magic.

   Build.  coqc -Q <world-root> "" -o zz_prrun_ext_mert.vo
   zz_prrun_ext_mert.v; the Separate Extraction command writes mmert/
   relative to the current working directory. *)

From Stdlib Require Import Extraction.
Set Extraction Output Directory "mmert".
Require Import u5c_pr_mertens_nat.
Separate Extraction pzs_prime_recip_diverge
                    pzs_rsum
                    pzs_B
                    abl_Pr_core_01.pr_prime_bool.
