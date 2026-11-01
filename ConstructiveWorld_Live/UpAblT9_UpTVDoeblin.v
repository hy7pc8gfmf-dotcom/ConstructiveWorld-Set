(* UpAblT9_UpTVDoeblin.v - instance-level certificates for the total-variation
   Doeblin development (the explicit-constant instance of UpTVDoeblin.v,
   Section TVDStar).

   Mission.  Carry the two kernel certificates of the Markov-kernel instance
     with delta* := e^(-2*gamma/T), u the uniform reference profile, and K the
     row-stochastic kernel, at the concrete carrier substitution
     K := tvd_K, u := tvd_u, delta* := tvd_dstar:  the row normalization
     (the sum of a kernel row over the enumeration equals one) and the
     minorization (delta* * u <= K pointwise, under the two-sided bounds
     -gamma <= z i j <= gamma).  Both statements mirror the discharged
     signatures of the upstream section lemmas verbatim and resolve them by
     direct application.
   Dependencies.  Stdlib List; registered tree modules S01_BaseRing through
     S15_TailFEPUp and UpTVDoeblin (read-only; the import face is exactly the
     source face, no added imports, no source-version imports).
   References.  Upstream statements: tvd_dstar UpTVDoeblin.v:1630, tvd_u
     UpTVDoeblin.v:1639, tvd_K UpTVDoeblin.v:1730, tvd_K_row
     UpTVDoeblin.v:1733, tvd_minorization UpTVDoeblin.v:1923; the instance
     theorems below instantiate them at the stated substitution.
   Constructivity.  All statements are informative; predicates ride the
     real-layer Set carriers of the tree; assumption-free closure, with the
     global-context audit printed at the tail.
   Build.  coqc -native-compiler no -q -Q . ""
  *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpTVDoeblin.
From Stdlib Require Import List.

(* Row normalization: exact instantiation of the upstream tvd_K_row (UpTVDoeblin.v:1733) at K := tvd_K. *)
Theorem uabT9_tvd_ctx_Krow :
  forall (states : list (list Real))
         (n_pos : real_lt real_zero (real_of_nat (length states)))
         (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp)
         (z : list Real -> list Real -> Real) (i : list Real),
    real_eq (real_list_sum (list Real) (tvd_K states n_pos Ttemp Ttemp_pos z i)
               states)
            real_one.
Proof.
  intros states n_pos Ttemp Ttemp_pos z i.
  exact (tvd_K_row states n_pos Ttemp Ttemp_pos z i).
Qed.

(* Minorization: exact instantiation of the upstream tvd_minorization (UpTVDoeblin.v:1923) at delta* := tvd_dstar, u := tvd_u, K := tvd_K. *)
Theorem uabT9_tvd_ctx_minorization :
  forall (states : list (list Real))
         (n_pos : real_lt real_zero (real_of_nat (length states)))
         (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp) (gamma : Real)
         (z : list Real -> list Real -> Real),
    (forall i j : list Real, real_le (real_opp gamma) (z i j)) ->
    (forall i j : list Real, real_le (z i j) gamma) ->
    forall i j : list Real,
      real_le (real_mult (tvd_dstar Ttemp Ttemp_pos gamma)
                         (tvd_u states n_pos j))
              (tvd_K states n_pos Ttemp Ttemp_pos z i j).
Proof.
  intros states n_pos Ttemp Ttemp_pos gamma z Hlb Hub i j.
  exact (tvd_minorization states n_pos Ttemp Ttemp_pos gamma z Hlb Hub i j).
Qed.

(* Global-context closure audit: both theorems print assumption-free. *)
Print Assumptions uabT9_tvd_ctx_Krow.
Print Assumptions uabT9_tvd_ctx_minorization.
