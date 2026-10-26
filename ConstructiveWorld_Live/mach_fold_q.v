(* ConstructiveWorld-Set — Machin representation of pi/4: Q-level
   folding certificates and the real-level assembly face. *)

(** * mach_fold_q: Q-level folding certificates for the Machin
      identity.

    Mission.  QeqT closed-fraction certificates for the two arctan
      folds behind 4*arctan(1/5) - arctan(1/239) = arctan(1): the
      difference and sum transforms at u = 5/12, v = 1/239, w =
      1183/2873; the fold-chain companions and range checks; the
      split [mach_q_decompose_28561] (28561 = 13^4); the pointwise
      bounds [mach_pt_bound_of_lt]; the assembly definitions
      [mach_atan_one_fifth], [mach_atan_1_239], [mach_pi_quarter].

    Dependencies.  Stdlib [QArith], [Qabs], [List], [Arith],
      [Setoid], [Lia], [ZArith]; requires the compiled chain
      [S01_BaseRing] .. [S11_TP3B5] ([Real], [cauchy_real_arctan]).

    References.  J. Machin (1706); ConstructiveWorld-Main, module
      [mach_fold_q] (statement names carried over verbatim).

    Constructivity.  Purely constructive; zero axioms.  Closed
      fractions are closed by full computational reduction; range
      checks reduce to Z cross-multiplication via [lia]; statement
      faces are carried by [Set]; extraction with [Obj.magic] = 0;
      [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -Q . "" mach_fold_q.v];
      artifact magic [436f7121 00015ff4]. *)

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
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
From Stdlib Require Import ZArith.
Import PropositionConvergenceCore.
Opaque Qred.

(* ================= Section 1. Q-level closed certificates for the
   difference and sum transforms =================

   Difference identity: arctan u - arctan v = arctan((u-v)/(1+u*v)).
   At u = 5/12 = tan(2*arctan(1/5)) (see [mach_q_tan2a]), v = 1/239:
   (5/12 - 1/239)/(1 + 5/2868) = (1183/2868)/(2873/2868) = 1183/2873.

   Sum identity: arctan u + arctan w = arctan((u+w)/(1-u*w)).
   At w = 1183/2873:
   (5/12 + 1183/2873)/(1 - 5915/34476)
     = (28561/34476)/(28561/34476) = 1 = tan(arctan 1).
   Two applications give 4*arctan(1/5) - arctan(1/239) = arctan(1). *)

(* Difference transform core: closed-fraction check that the tan value
   of arctan(5/12) - arctan(1/239) folds to arctan(1183/2873).
   Set-level statement face (QeqT), companion of the fold chain. *)
Lemma mach_q_diff_transformT :
  QeqT ((((5 # 12) - (1 # 239)) / (1 + (5 # 12) * (1 # 239)))) (1183 # 2873).
Proof.
  apply qeq_imp_qeqT.
  vm_compute.
  reflexivity.
Qed.

Lemma mach_q_diff_transform :
  QeqT ((((5 # 12) - (1 # 239)) / (1 + (5 # 12) * (1 # 239)))) (1183 # 2873).
Proof.
  vm_compute.
  reflexivity.
Qed.

(* Sum transform core: closed-fraction check that the tan value of
   arctan(5/12) + arctan(1183/2873) folds to arctan(1).
   Set-level statement face (QeqT), companion of the fold chain. *)
Lemma mach_q_add_transformT :
  QeqT ((((5 # 12) + (1183 # 2873)) / (1 - (5 # 12) * (1183 # 2873)))) 1.
Proof.
  apply qeq_imp_qeqT.
  vm_compute.
  reflexivity.
Qed.

Lemma mach_q_add_transform :
  QeqT ((((5 # 12) + (1183 # 2873)) / (1 - (5 # 12) * (1183 # 2873)))) 1.
Proof.
  vm_compute.
  reflexivity.
Qed.

(* Double-angle form: tan(2a) = 2*tan a / (1 - tan^2 a); at
   a = arctan(1/5) it gives tan(2a) = 5/12. *)
Lemma mach_q_tan2a :
  QeqT (((2 * (1 # 5)) / (1 - (1 # 5) * (1 # 5)))) (5 # 12).
Proof.
  vm_compute.
  reflexivity.
Qed.

(* Intermediate fractions of the fold chain on the numerator and the
   denominator sides: the difference step (1183/2868)/(2873/2868) and
   the sum step 28561/34476. *)
Lemma mach_q_diff_mid_num : QeqT ((5 # 12) - (1 # 239)) (1183 # 2868).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma mach_q_diff_mid_den :
  QeqT (1 + (5 # 12) * (1 # 239)) (2873 # 2868).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma mach_q_add_mid_num : QeqT ((5 # 12) + (1183 # 2873)) (28561 # 34476).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma mach_q_add_mid_den :
  QeqT (1 - (5 # 12) * (1183 # 2873)) (28561 # 34476).
Proof.
  vm_compute.
  reflexivity.
Qed.

(* ================= Section 2. Range checks =================

   [Qlt p q] unfolds to the cross-multiplication strict order
   [Qnum p * QDen q < Qnum q * QDen p].  The statements below are the
   pointwise instances, at u = 5/12, v = 1/239 and w = 1183/2873, of
   the difference premises 0 < v, v < u, u < 1 and the sum premises
   u < 1, v < 1 (with the corollary u*v < 1). *)

(* Set-level statement face (QltT), range-check companions. *)
Lemma mach_q_range_5_12_lt1T : QltT (5 # 12) 1.
Proof.
  apply Qlt_to_QltT.
  change (5 * 1 < 1 * 12)%Z.
  lia.
Qed.

Lemma mach_q_range_5_12_lt1 : QltT (5 # 12) 1.
Proof.
  apply Qlt_to_QltT.
  change (5 * 1 < 1 * 12)%Z.
  lia.
Qed.

Lemma mach_q_range_1183_2873_lt1T : QltT (1183 # 2873) 1.
Proof.
  apply Qlt_to_QltT.
  change (1183 * 1 < 1 * 2873)%Z.
  lia.
Qed.

Lemma mach_q_range_1183_2873_lt1 : QltT (1183 # 2873) 1.
Proof.
  apply Qlt_to_QltT.
  change (1183 * 1 < 1 * 2873)%Z.
  lia.
Qed.

Lemma mach_q_range_0_lt_1_239T : QltT 0 (1 # 239).
Proof.
  apply Qlt_to_QltT.
  change (0 * 239 < 1 * 1)%Z.
  lia.
Qed.

Lemma mach_q_range_0_lt_1_239 : QltT 0 (1 # 239).
Proof.
  apply Qlt_to_QltT.
  change (0 * 239 < 1 * 1)%Z.
  lia.
Qed.

Lemma mach_q_range_1_239_lt_5_12T : QltT (1 # 239) (5 # 12).
Proof.
  apply Qlt_to_QltT.
  change (1 * 12 < 5 * 239)%Z.
  lia.
Qed.

Lemma mach_q_range_1_239_lt_5_12 : QltT (1 # 239) (5 # 12).
Proof.
  apply Qlt_to_QltT.
  change (1 * 12 < 5 * 239)%Z.
  lia.
Qed.

Lemma mach_q_range_mult_lt1 : QltT ((5 # 12) * (1183 # 2873)) 1.
Proof.
  apply Qlt_to_QltT.
  change (5915 * 1 < 1 * 34476)%Z.
  lia.
Qed.

(* ================= Section 3. Structural split =================

   28561 = 13^4: the difference step gives the numerator
   1183 = 5*239 - 12 and the denominator 2873 = 12*239 + 5; in the
   sum step the numerator 5*2873 + 1183*12 = 28561 equals its
   denominator 12*2873 - 5*1183 = 28561, so the sum ratio simplifies
   to 1. *)

Lemma mach_q_decompose_28561 : Id (28561%Z) ((13 ^ 4)%Z).
Proof.
  vm_compute. apply id_refl.
Qed.

(* ================= Section 4. Pointwise bounds (supply for the
   unit-domain premises) =================

   The premises of [cauchy_real_arctan] are pointwise bounds:
   [Qabs (projT1 x n) <= 1] for every n.  The generic piece follows
   directly from 0 < u and u < 1; the two instances are
   closed-fraction special cases. *)

(* Generic pointwise bound: for 0 < u < 1 the real constant
   sequence u stays in the unit domain. *)
Lemma mach_pt_bound_of_lt :
  forall u : Q, QltT 0 u -> QltT u 1 ->
    forall n : nat, QleT' (Qabs (projT1 (real_const u) n)) 1.
Proof.
  intros u Hu0T Hu1T n.
  pose proof (QltT_to_Qlt 0 u Hu0T) as Hu0.
  pose proof (QltT_to_Qlt u 1 Hu1T) as Hu1.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs u) _).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    apply (Qabs_wd (projT1 (real_const u) n) u).
    apply qeqT_imp_qeq. apply real_const_proj.
  - apply (Qle_trans _ u).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      apply Qabs_pos.
      apply (Qlt_le_weak 0 u).
      exact Hu0.
    + apply (Qlt_le_weak u 1).
      exact Hu1.
Qed.

(* Instance: u = 1/5. *)
Lemma mach_pt_bound_1_5 :
  forall n : nat, QleT' (Qabs (projT1 (real_const (1 # 5)) n)) 1.
Proof.
  intro n.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (1 # 5)) _).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    apply (Qabs_wd (projT1 (real_const (1 # 5)) n) (1 # 5)).
    apply qeqT_imp_qeq. apply real_const_proj.
  - change (1 * 1 <= 1 * 5)%Z.
    lia.
Qed.

(* Instance: u = 1/239. *)
Lemma mach_pt_bound_1_239 :
  forall n : nat, QleT' (Qabs (projT1 (real_const (1 # 239)) n)) 1.
Proof.
  intro n.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (1 # 239)) _).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    apply (Qabs_wd (projT1 (real_const (1 # 239)) n) (1 # 239)).
    apply qeqT_imp_qeq. apply real_const_proj.
  - change (1 * 1 <= 1 * 239)%Z.
    lia.
Qed.

(* ================= Section 5. Assembly definitions =================

   The real-level definition face of the Machin vertex
   4*arctan(1/5) - arctan(1/239): the two unit-domain arctan series
   real values and their linear combination. *)

Definition mach_atan_one_fifth : Real :=
  cauchy_real_arctan (real_const (1 # 5)) mach_pt_bound_1_5.

Definition mach_atan_1_239 : Real :=
  cauchy_real_arctan (real_const (1 # 239)) mach_pt_bound_1_239.

Definition mach_pi_quarter : Real :=
  real_plus (real_mult (real_const 4) mach_atan_one_fifth)
            (real_opp mach_atan_1_239).
