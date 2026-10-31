(* ========================================================================== *)
(*  UpAblHalfPowFeed.v - statement-family collection and instantiation        *)
(*                      carriers for the half-power feed chain                *)
(* ========================================================================== *)
(*   Mission. Nine stations formalizing the half-power feed family:          *)
(*   hpw_half_step (definitional halving step in QleT' form),                *)
(*   hpw_half_pow_inv_le and hpw_half_pow_inv_pos (unit-fraction bridge      *)
(*   faces for (1/2)^n along the S03 lineage), hpw_arch_decay_instT (the     *)
(*   arch_decay statement instT-shaped with fully concrete witnesses), and   *)
(*   hpwf_slot1_sin_cauchy, hpwf_slot2_cos_cauchy, hpwf_slot3_cs_sq,         *)
(*   hpwf_slot4_add_sin, hpwf_slot5_add_cos (five slot corollaries routing   *)
(*   the sin/cos Cauchy, cs_sq, add_sin, add_cos bounds through              *)
(*   hpw_arch_decay_instT).                                                  *)
(*   Dependencies. Stdlib QArith (QArith, Qabs, Qround), ZArith, Arith,      *)
(*   Lia, Qminmax, Setoid, Morphisms; S01_BaseRing through S15_TailFEPUp     *)
(*   (Set-valued witnesses QltT/QleT'/QeqT/NatLe with the registered         *)
(*   conversion lemmas).  No further Require.                                *)
(*   References. Baseline module UpAblHalfPowFeed.v of ConstructiveWorld-    *)
(*   Main / _Live (statement faces verbatim; ordered census 9 = 9).          *)
(*   Constructivity. All statements Set-valued; every proof closed by Qed;   *)
(*   axiom-free, no classical logic; extracts with Obj.magic = 0.            *)
(*   Build. rocq c -native-compiler no -q -Q . "" UpAblHalfPowFeed.v         *)
(*   (Rocq 9.1 toolchain; single -Q root with an empty logical prefix).      *)
(* ========================================================================== *)

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
From Stdlib Require Import Setoid Morphisms.

(* ================= Section: hpw_half_step family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import ZArith Arith.Arith.
From Stdlib Require Import Lia QArith.Qminmax.

Local Open Scope Q_scope.

(* Section 0: symbol check against the library; a signature drift
   surfaces as a compile-time failure. *)

Check q_pow.
Check q_half_pow_le_inv.
Check Qle_refl.
Check QleT'_to_Qle.
Check Qle_to_QleT'.
Check QltT_to_Qlt.
Check Qlt_to_QltT.
Check Qle_lt_trans.
Check Qmult_le_compat_r.
Check Z.mul_le_mono_nonneg_r.
Check Z.mul_le_mono_nonneg_l.
Check Pos.of_succ_nat.

(* Upstream closure check: if q_half_pow_le_inv is not Closed, it would
   need a standalone proof of its own. *)
Print Assumptions q_half_pow_le_inv.

(* Section A: recursive shape (the definitional identity of geometric
   halving, in QleT' form). *)

Lemma hpw_half_step : forall n : nat,
  QleT' (q_pow (1 / 2)%Q (Datatypes.S n)) ((1 / 2)%Q * q_pow (1 / 2)%Q n).
Proof.
  intro n.
  exact (Qle_to_QleT' _ _
  (Qle_refl ((1 / 2)%Q * q_pow (1 / 2)%Q n))).
Qed.

(* Section B: unit-fraction bridge lemma (the S03 (1/2)^n lineage,
   instantiated at S t). *)

Corollary hpw_half_pow_inv_le : forall t : nat,
  QleT' (q_pow (1 / 2)%Q (Datatypes.S t))
        (1 / (Z.of_nat (Datatypes.S t + 1)%nat # 1)).
Proof.
  intro t.
  exact (q_half_pow_le_inv (Datatypes.S t)).
Qed.


(* Section C: division-form interface (the 1 # Pos.of_succ_nat shape,
   aligned with the S03 lineage of the same shape). *)

Corollary hpw_half_pow_inv_pos : forall t : nat,
  QleT' (q_pow (1 / 2)%Q (Datatypes.S t))
        (1#(Pos.of_succ_nat (Datatypes.S t))).
Proof.
  intro t.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (1 / (Z.of_nat (Datatypes.S t + 1)%nat # 1))).
  - exact (QleT'_to_Qle _ _ (q_half_pow_le_inv (Datatypes.S t))).
  - change (Z.of_nat (Datatypes.S t + 1)%nat)
      with (Z.pos (Pos.of_succ_nat (t + 1)%nat)).
    replace (t + 1)%nat with (Datatypes.S t) by (symmetry; apply Nat.add_1_r).
    unfold Qle. cbn [Qdiv Qinv Qnum Qden Qmult]. apply Z.le_refl.
Qed.

(* Section D: target statement supply (statement verbatim-equal to
   arch_decay, witnesses fully concrete).                                    *)
(*   Witness: t0 := Z.to_nat(Z.max 0 (c*f) + 1), where c/f are the           *)
(*   components of the C/eps spreads.  Chain: (1/2)^(S t0)                   *)
(*   <= 1/((S t0+1) # 1) (via the Section B lemma), hence                    *)
(*   C * (1/2)^(S t0) < eps, where the nonlinear step c*f < e*d*q is         *)
(*   supplied explicitly by the Z.mul monotonicity lemmas (Hed1/Hmul);       *)
(*   the linear part closes by lia.                                          *)

Corollary hpw_arch_decay_instT : forall (C eps : Q), QleT' 0 C -> QltT 0 eps ->
  sigT (fun t : nat => QltT (C * q_pow (1 / 2)%Q (Datatypes.S t)) eps).
Proof.
  intros C eps HC Hep.
  destruct C as [c d]. destruct eps as [e f].
  assert (Hepos : (0 < e)%Z).
  { pose proof (QltT_to_Qlt 0 (Qmake e f) Hep) as Hlt0.
    unfold Qlt in Hlt0. simpl in Hlt0.
    rewrite Z.mul_1_r in Hlt0. exact Hlt0. }
  assert (Hed1 : (1 <= e * Z.pos d)%Z).
  { assert (Hpd : (0 < Z.pos d)%Z) by exact (Pos2Z.is_pos d).
    assert (Hpd1 : (1 <= Z.pos d)%Z).
    { exact (proj2 (Z.le_succ_l 0 (Z.pos d)) Hpd). }
    assert (He1 : (1 <= e)%Z).
    { exact (proj2 (Z.le_succ_l 0 e) Hepos). }
    assert (Hstep : (Z.pos d <= e * Z.pos d)%Z).
    { pose proof (Z.mul_le_mono_nonneg_r 1 e (Z.pos d)
                     (Z.lt_le_incl 0 (Z.pos d) Hpd) He1) as Hm.
      rewrite Z.mul_1_l in Hm. exact Hm. }
    exact (Z.le_trans 1 (Z.pos d) (e * Z.pos d) Hpd1 Hstep). }
  exists (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)).
  assert (Hqv : (Z.max 0 (c * Z.pos f) + 1
                 <= Z.pos (Pos.of_succ_nat
                       (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))%Z).
  { change (Z.pos (Pos.of_succ_nat (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))
      with (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1))).
    assert (Hge : (0 <= Z.max 0 (c * Z.pos f) + 1)%Z).
    { apply (Z.le_trans 0 (Z.max 0 (c * Z.pos f))
               (Z.succ (Z.max 0 (c * Z.pos f)))).
      - exact (Z.le_max_l 0 (c * Z.pos f)).
      - exact (Z.le_le_succ_r (Z.max 0 (c * Z.pos f)) (Z.max 0 (c * Z.pos f))
                 (Z.le_refl (Z.max 0 (c * Z.pos f)))). }
    rewrite Nat2Z.inj_succ. rewrite Nat2Z.inj_add.
    rewrite (Z2Nat.id (Z.max 0 (c * Z.pos f) + 1) Hge).
    change (Z.of_nat 1) with 1%Z.
    apply (Z.le_trans (Z.max 0 (c * Z.pos f) + 1)
                      (Z.succ (Z.max 0 (c * Z.pos f) + 1))).
    - apply Z.le_succ_diag_r.
    - apply Z.le_succ_diag_r. }
  assert (Hmul : (Z.pos (Pos.of_succ_nat
                       (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)) * 1
                  <= Z.pos (Pos.of_succ_nat
                       (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1))
                       * (e * Z.pos d))%Z).
  { apply (Z.mul_le_mono_nonneg_l 1 (e * Z.pos d)
             (Z.pos (Pos.of_succ_nat
                  (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))).
    - exact (Z.lt_le_incl 0 _ (Pos2Z.is_pos _)).
    - exact Hed1. }
  assert (Hpow : Qle (q_pow (1 / 2)%Q
                            (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)))
                      * (c # d))
                     ((1 / (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)) + 1)%nat # 1))
                      * (c # d))).
  { apply (Qmult_le_compat_r (q_pow (1 / 2)%Q
                             (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1))))
                             (1 / (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)) + 1)%nat # 1))
                             (c # d)).
    - exact (QleT'_to_Qle _ _
              (q_half_pow_le_inv (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1))))).
    - apply QleT'_to_Qle. exact HC. }
  assert (Hmid : Qlt ((1 / (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)) + 1)%nat # 1))
                      * (c # d))
                     (e # f)).
  { change (Z.of_nat (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1)) + 1)%nat)
      with (Z.pos (Pos.of_succ_nat (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1))).
    unfold Qlt. cbn [Qdiv Qinv Qnum Qden Qmult].
    rewrite !Z.mul_1_l.
    assert (Hcf : Z.lt (c * Z.pos f)
                       (Z.pos (Pos.of_succ_nat
                            (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))).
    { apply (Z.lt_le_trans (c * Z.pos f) (Z.succ (c * Z.pos f))
               (Z.pos (Pos.of_succ_nat
                    (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))).
      - apply Z.lt_succ_diag_r.
      - apply (Z.le_trans (Z.succ (c * Z.pos f))
                 (Z.succ (Z.max 0 (c * Z.pos f)))
                 (Z.pos (Pos.of_succ_nat
                      (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))).
        + apply (proj1 (Z.succ_le_mono (c * Z.pos f) (Z.max 0 (c * Z.pos f)))).
          exact (Z.le_max_r 0 (c * Z.pos f)).
        + exact Hqv. }
    assert (He1 : (1 <= e)%Z).
    { exact (proj2 (Z.le_succ_l 0 e) Hepos). }
    assert (Hd1 : (1 <= Z.pos d)%Z).
    { exact (proj2 (Z.le_succ_l 0 (Z.pos d)) (Pos2Z.is_pos d)). }
    assert (HP : Z.le (Z.pos (Pos.of_succ_nat
                            (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))
                       (e * (Z.pos (Pos.of_succ_nat
                            (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1))
                             * Z.pos d))).
    { apply (Z.le_trans _ (e * Z.pos (Pos.of_succ_nat
                            (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1))) _).
      - exact (Z.mul_le_mono_nonneg_r 1 e
                 (Z.pos (Pos.of_succ_nat
                      (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))
                 (Z.lt_le_incl 0 _ (Pos2Z.is_pos _)) He1).
      - pose proof (Z.mul_le_mono_nonneg_l 1 (Z.pos d)
                       (Z.pos (Pos.of_succ_nat
                            (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))
                       (Z.lt_le_incl 0 _ (Pos2Z.is_pos _)) Hd1) as Hm2.
        rewrite Z.mul_1_r in Hm2.
        exact (Z.mul_le_mono_nonneg_l
                 (Z.pos (Pos.of_succ_nat
                      (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))
                 (Z.pos (Pos.of_succ_nat
                      (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)) * Z.pos d)
                 e (Z.lt_le_incl 0 e Hepos) Hm2). }
    exact (Z.lt_le_trans (c * Z.pos f)
             (Z.pos (Pos.of_succ_nat
                  (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)))
             (e * (Z.pos (Pos.of_succ_nat
                  (Z.to_nat (Z.max 0 (c * Z.pos f) + 1) + 1)) * Z.pos d))
             Hcf HP). }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _
          (q_pow (1 / 2)%Q (Datatypes.S (Z.to_nat (Z.max 0 (c * Z.pos f) + 1))) * (c # d)) _).
  - exact (QleT'_to_Qle _ _
            (qeq_le _ _ (qeq_imp_qeqT _ _ (Qmult_comm _ _)))).
  - exact (Qle_lt_trans _ _ _ Hpow Hmid).
Qed.

(* Assumption audit: Print Assumptions of each item below reports Closed
   (zero external unproven assumptions). *)

Print Assumptions hpw_half_step.
Print Assumptions hpw_half_pow_inv_le.
Print Assumptions hpw_half_pow_inv_pos.
Print Assumptions hpw_arch_decay_instT.
(* ================= Section: hpwf_slot1_sin_cauchy family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import ZArith Arith.Arith.
From Stdlib Require Import Lia QArith.Qminmax.

Local Open Scope Q_scope.

(* Section 0: dependency signature check; identifier drift surfaces
   at compile time. *)

Check q_pow.
Check q_fact.
Check exp_series.
Check q_arch_geom.
Check exp_series_arch.
Check q_pow_fact_nonneg.
Check q_pow_fact2_nonneg.
Check Q2_nonneg.
Check Qmult_le_0_compat.
Check Qle_to_QleT'.
Check QleT'_to_Qle.
Check QltT_to_Qlt.
Check NatLe_lift.
Check arch_decay.
Check hpw_arch_decay_instT.

(* Shape check: hpw_arch_decay_instT sits in the statement position of
   arch_decay (type annotation). *)
Check (hpw_arch_decay_instT
  : forall (C eps : Q), QleT' 0 C -> QltT 0 eps ->
      sigT (fun t : nat => QltT (C * q_pow (1 / 2)%Q (Datatypes.S t)) eps)).

(* Upstream assumption check: Print Assumptions of hpw_arch_decay_instT
   must report Closed. *)
Print Assumptions hpw_arch_decay_instT.

(* Item 1 (position of sc_sin_partial_cauchy_bounded).                      *)
(*   Proof-context reconstruction: q_arch_geom spread, then set N0', then   *)
(*   set C, then the nonneg premise HC (same expressions in place);         *)
(*   instantiate hpw_arch_decay_instT by the same expression and destruct;  *)
(*   package sigT(N0, sigT(t, QltT (C*(1/2)^(S t)) eps)).                   *)
(*   (The HN0' bound serves downstream progress after the destruct and is   *)
(*   not part of this deliverable.)                                         *)

Corollary hpwf_slot1_sin_cauchy : forall (B eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun N0 : nat =>
    sigT (fun t : nat =>
      QltT (((q_pow B (Datatypes.S (2 * N0)) / q_fact (Datatypes.S (2 * N0)))
             * (1 + 1)%Q)
            * q_pow (1 / 2)%Q (Datatypes.S t)) eps)).
Proof.
  intros B eps HB Hep.
  destruct (q_arch_geom B) as [N0 HN0].
  set (N0' := Datatypes.S (2 * N0)).
  set (C := (q_pow B N0' / q_fact N0') * (1 + 1)%Q).
  assert (HC : QleT' 0 C)
    by (unfold C; apply q_pow_fact2_nonneg; exact HB).
  destruct (hpw_arch_decay_instT C eps HC Hep) as [t Hdec].
  exists N0. exists t. exact Hdec.
Qed.

(* Item 2 (position of sc_cos_partial_cauchy_bounded).                      *)
(*   Same proof context as Item 1 (cos position); same instantiation.       *)

Corollary hpwf_slot2_cos_cauchy : forall (B eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun N0 : nat =>
    sigT (fun t : nat =>
      QltT (((q_pow B (Datatypes.S (2 * N0)) / q_fact (Datatypes.S (2 * N0)))
             * (1 + 1)%Q)
            * q_pow (1 / 2)%Q (Datatypes.S t)) eps)).
Proof.
  intros B eps HB Hep.
  destruct (q_arch_geom B) as [N0 HN0].
  set (N0' := Datatypes.S (2 * N0)).
  set (C := (q_pow B N0' / q_fact N0') * (1 + 1)%Q).
  assert (HC : QleT' 0 C)
    by (unfold C; apply q_pow_fact2_nonneg; exact HB).
  destruct (hpw_arch_decay_instT C eps HC Hep) as [t Hdec].
  exists N0. exists t. exact Hdec.
Qed.

(* Item 3 (position of sc_cs_sq_err_bound).                                 *)
(*   Proof-context reconstruction: q_arch_geom and exp_series_arch          *)
(*   spreads give HC0/Htwo0/Hfour0, then set P and the HP0 nonnegativity    *)
(*   chain (same expressions in place); instantiated via Qle_to_QleT'.      *)

Corollary hpwf_slot3_cs_sq : forall (B eps C : Q),
  QleT' 0 B -> QltT 0 eps ->
  QleT' 1 C -> (forall n : nat, QleT' (exp_series n B) C) ->
  sigT (fun N0 : nat =>
    sigT (fun t : nat =>
      QltT ((((1 + 1) * (1 + 1))
             * (C * ((q_pow B N0 / q_fact N0) * (1 + 1)%Q)))
            * q_pow (1 / 2)%Q (Datatypes.S t)) eps)).
Proof.
  intros B eps C HB Hep HC1 HC.
  destruct (q_arch_geom B) as [N0 HN0].
  assert (HC0 : Qle 0 C)
    by (apply (Qle_trans _ 1 _);
        [exact (QleT'_to_Qle _ _ Qle_0_1) | exact (QleT'_to_Qle _ _ HC1)]).
  assert (Htwo0 : Qle 0 (1 + 1))
    by exact (QleT'_to_Qle _ _ Q2_nonneg).
  assert (Hfour0 : Qle 0 ((1 + 1) * (1 + 1)))
    by (apply Qmult_le_0_compat; [exact Htwo0 | exact Htwo0]).
  set (P := ((1 + 1) * (1 + 1)) * (C * ((q_pow B N0 / q_fact N0) * (1 + 1)))).
  assert (HP0 : Qle 0 P).
  { unfold P. apply Qmult_le_0_compat.
    - exact Hfour0.
    - apply (Qmult_le_0_compat C ((q_pow B N0 / q_fact N0) * (1 + 1))).
      + exact HC0.
      + exact (QleT'_to_Qle _ _ (q_pow_fact2_nonneg B N0 HB)). }
  destruct (hpw_arch_decay_instT P eps (Qle_to_QleT' _ _ HP0) Hep) as [t Ht].
  exists N0. exists t. exact Ht.
Qed.

(* Item 4 (position of sc_add_sin_err_bound).                               *)
(*   Same proof context as Item 3 (P of the same expression); same          *)
(*   instantiation.                                                         *)

Corollary hpwf_slot4_add_sin : forall (B eps C : Q),
  QleT' 0 B -> QltT 0 eps ->
  QleT' 1 C -> (forall n : nat, QleT' (exp_series n B) C) ->
  sigT (fun N0 : nat =>
    sigT (fun t : nat =>
      QltT ((((1 + 1) * (1 + 1))
             * (C * ((q_pow B N0 / q_fact N0) * (1 + 1)%Q)))
            * q_pow (1 / 2)%Q (Datatypes.S t)) eps)).
Proof.
  intros B eps C HB Hep HC1 HC.
  destruct (q_arch_geom B) as [N0 HN0].
  assert (HC0 : Qle 0 C)
    by (apply (Qle_trans _ 1 _);
        [exact (QleT'_to_Qle _ _ Qle_0_1) | exact (QleT'_to_Qle _ _ HC1)]).
  assert (Htwo0 : Qle 0 (1 + 1))
    by exact (QleT'_to_Qle _ _ Q2_nonneg).
  assert (Hfour0 : Qle 0 ((1 + 1) * (1 + 1)))
    by (apply Qmult_le_0_compat; [exact Htwo0 | exact Htwo0]).
  set (P := ((1 + 1) * (1 + 1)) * (C * ((q_pow B N0 / q_fact N0) * (1 + 1)))).
  assert (HP0 : Qle 0 P).
  { unfold P. apply Qmult_le_0_compat.
    - exact Hfour0.
    - apply (Qmult_le_0_compat C ((q_pow B N0 / q_fact N0) * (1 + 1))).
      + exact HC0.
      + exact (QleT'_to_Qle _ _ (q_pow_fact2_nonneg B N0 HB)). }
  destruct (hpw_arch_decay_instT P eps (Qle_to_QleT' _ _ HP0) Hep) as [t Ht].
  exists N0. exists t. exact Ht.
Qed.

(* Item 5 (position of sc_add_cos_err_bound).                               *)
(*   P with the 13-coefficient expression (13 = (1+1)*(1+1+1+1+1+1)+1);     *)
(*   the HP0 chain of the same shape in place; instantiation of the         *)
(*   Item 3 form.                                                           *)

Corollary hpwf_slot5_add_cos : forall (B eps C : Q),
  QleT' 0 B -> QltT 0 eps ->
  QleT' 1 C -> (forall n : nat, QleT' (exp_series n B) C) ->
  sigT (fun N0 : nat =>
    sigT (fun t : nat =>
      QltT ((((((1 + 1) * (1 + 1 + 1 + 1 + 1 + 1)) + 1)
              * (C * (q_pow B N0 / q_fact N0))))
            * q_pow (1 / 2)%Q (Datatypes.S t)) eps)).
Proof.
  intros B eps C HB Hep HC1 HC.
  destruct (q_arch_geom B) as [N0 HN0].
  assert (HC0 : Qle 0 C)
    by (apply (Qle_trans _ 1 _);
        [exact (QleT'_to_Qle _ _ Qle_0_1) | exact (QleT'_to_Qle _ _ HC1)]).
  assert (Htwo0 : Qle 0 (1 + 1))
    by exact (QleT'_to_Qle _ _ Q2_nonneg).
  assert (Hsix0 : Qle 0 ((1 + 1) * (1 + 1 + 1))) by (unfold Qle; simpl; lia).
  set (P := (((1 + 1) * (1 + 1 + 1 + 1 + 1 + 1)) + 1) * (C * (q_pow B N0 / q_fact N0))).
  assert (HP0 : Qle 0 P).
  { unfold P. apply (Qmult_le_0_compat _ _).
    - unfold Qle; simpl; lia.
    - apply (Qmult_le_0_compat C (q_pow B N0 / q_fact N0)).
      + exact HC0.
      + exact (QleT'_to_Qle _ _ (q_pow_fact_nonneg B N0 HB)). }
  destruct (hpw_arch_decay_instT P eps (Qle_to_QleT' _ _ HP0) Hep) as [t Ht].
  exists N0. exists t. exact Ht.
Qed.

(* Assumption audit: Print Assumptions of the five items all report Closed
   (zero external unproven assumptions). *)

Print Assumptions hpwf_slot1_sin_cauchy.
Print Assumptions hpwf_slot2_cos_cauchy.
Print Assumptions hpwf_slot3_cs_sq.
Print Assumptions hpwf_slot4_add_sin.
Print Assumptions hpwf_slot5_add_cos.
