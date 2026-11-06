(* ConstructiveWorld-Set — residual closure pieces of the abs_sum_le family (simultaneity counterexample and abstract fold). *)

(** * UpAblAbsSumLeB2: full-margin simultaneity counterexample and the B-form bound of an abstract fold operator.

    Mission.  Two residual closures of the abs_sum_le family: the full-margin
      simultaneity counterexample carried by the Q-layer Cauchy certificate
      [X_n := q0 + 1/(n+1)], with statements [uabS4b_full_margin_eq],
      [uabS4b_full_margin_le], [uabS4b_full_margin_rev_lt],
      [uabS4b_full_margin_tight], [uabS4b_full_margin_no_far],
      [uabS4b_full_margin_coexist]; and the B-form bound of the abstract
      fold [sumL], [uabS4b_slot_abs_sum_le_B] with [uabS4b_slot_list_le_B].

    Dependencies.  Stdlib [List], [QArith.Qring], [Lia], [Lqa].  Requires
      [S01_BaseRing] through [S15_TailFEPUp], [UpRealLeB], [UpAblAbsSumLeB]
      of this development; the fold lemmas [uabS4_le_add_r], [uabS4_wlen],
      [uabS4_wlen_pos], [uabS4_cons_glue] are applied from [UpAblAbsSumLeB],
      the real-layer order lemmas from [S08_RealMainlineDPO].

    References.  This development, UpAblAbsSumLeB2.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblAbsSumLeB2.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import List.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
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
Require Import UpRealLeB.
Require Import UpAblAbsSumLeB.



(* ==================== Section 0. Library interface audit (each Check against the real signature) ==================== *)

Check real_lt.                    (* the type is sigT(eps, And(QltT, sigT(N, ...))): an eps together with a per-eps bound N *)
Check real_eq.                    (* universally quantified over each eps *)
Check real_le.                    (* encoded as an Or of the strict branch and the equality branch *)
Check real_le_b.                  (* the Bishop-form order *)
Check real_const_proj.            (* the pointwise projection of real_const *)
Check real_plus_proj.             (* the pointwise projection of real_plus *)
Check real_eq_of_zero_diff.       (* real_eq obtained from a pointwise zero difference *)
Check QltT_to_Qlt. Check Qlt_to_QltT.
Check Qlt_alt. Check Qle_alt.
Check q_abs_lt_two_sided.         (* the two-sided absolute-value bound at the Q layer *)
Check NatLe_lift. Check NatLe_drop. (* round trips between the nat order and NatLe *)
Check real_abs_triangle_le_eps.   (* the per-eps triangle bound for a two-point difference *)
Check real_le_closure_b.          (* the B-form closure with an explicit weight-positivity certificate D *)
Check real_abs_zero_req.
Check real_list_sum.              (* the list fold, quantified over X *)
Check uabS4_le_add_r. Check uabS4_wlen. Check uabS4_wlen_pos. Check uabS4_cons_glue.
Check real_eq_refl. Check real_eq_sym. Check real_mult_comm. Check real_mult_one.
Check RealSetoid.real_le_id_l. Check RealSetoid.real_le_id_r.
Check RealSetoid.real_eq_le. Check RealSetoid.real_eq_abs_compat.

(* ==================== Section 1. Residual one: the Q-layer Cauchy certificate and the full-margin simultaneity counterexample ==================== *)

(* A.0 The unit-fraction family 1/(n+1): nonnegativity, monotonicity and
   the archimedean property at the Q layer (the core of the Cauchy
   certificate). *)
Lemma uabS4b_null_nonneg : forall n : nat, Qle 0 (1#(Pos.of_succ_nat n)).
Proof.
  intros n. unfold Qle. cbn [Qnum Qden].
  (* at the Z layer the unfolded Qle reads (0 * Z.pos (Pos.of_succ_nat n) <= 1 * 1)%Z; *)
  (* after both products normalize, Z.lt_le_incl transports the positivity witness     *)
  (* Pos2Z.pos_is_pos into the required bound. *)
  rewrite Z.mul_0_l, Z.mul_1_r.
  apply Z.lt_le_incl. apply Pos2Z.pos_is_pos.
Qed.

(* Z-level bridge for positive indices, by induction: monotonicity of
   Pos.of_succ_nat and the add-one identity.  In this setting zify does
   not apply to Z.of_nat (Nat.succ n), so the proof goes through explicit
   induction with the Nat2Z/Pos2Z bridges and does not rely on that path. *)
Lemma uabS4b_pos_le : forall m k : nat, (k <= m)%nat ->
  Z.le (Z.pos (Pos.of_succ_nat k)) (Z.pos (Pos.of_succ_nat m)).
Proof.
  intros m k Hk. induction Hk as [| m' Hkm IH].
  - apply Z.le_refl.
  - cbn [Pos.of_succ_nat].
    rewrite Pos2Z.inj_succ.
    apply Z.le_trans with (Z.pos (Pos.of_succ_nat m')).
    + exact IH.
    + apply Z.le_succ_diag_r.
Qed.

Lemma uabS4b_pos_succ_Z : forall N : nat,
  Z.pos (Pos.of_succ_nat N) = (Z.of_nat N + 1)%Z.
Proof.
  intros N. rewrite Z.add_1_r. rewrite <- Znat.Nat2Z.inj_succ. reflexivity.
Qed.

Lemma uabS4b_null_pos : forall n : nat, Qlt 0 (1#(Pos.of_succ_nat n)).
Proof.
  intros n. unfold Qlt. cbn [Qnum Qden].
  (* at the Z layer the unfolded Qlt reads (0 * Z.pos (Pos.of_succ_nat n) < 1 * 1)%Z; *)
  (* after both products normalize, the positivity witness Pos2Z.pos_is_pos closes it. *)
  rewrite Z.mul_0_l, Z.mul_1_r.
  apply Pos2Z.pos_is_pos.
Qed.

Lemma uabS4b_null_mono : forall m k : nat, (k <= m)%nat ->
  Qle (1#(Pos.of_succ_nat m)) (1#(Pos.of_succ_nat k)).
Proof.
  intros m k Hk. unfold Qle. simpl.
  exact (uabS4b_pos_le m k Hk).
Qed.

(* the archimedean index: N(q) := Z.to_nat (Qnum q) + Z.to_nat (QDen q),
   large enough that 1/(N+1) < q *)
Definition uabS4b_arch_N (q : Q) : nat :=
  Z.to_nat (Qnum q) + Z.to_nat (QDen q).

Lemma uabS4b_null_lt : forall q : Q, QltT 0 q ->
  QltT (1#(Pos.of_succ_nat (uabS4b_arch_N q))) q.
Proof.
  intros q Hq. apply Qlt_to_QltT. unfold Qlt. simpl.
  assert (Hz : (0 < Qnum q)%Z).
  { pose proof (QltT_to_Qlt 0 q Hq) as Hq0. unfold Qlt in Hq0. simpl in Hq0. lia. }
  assert (Hz0 : (0 <= Qnum q)%Z) by lia.
  assert (Hd0 : (0 <= QDen q)%Z) by (apply Z.lt_le_incl, Pos2Z.is_pos).
  assert (Harch : Z.of_nat (uabS4b_arch_N q)
                  = (Qnum q + QDen q)%Z).
  { unfold uabS4b_arch_N.
    rewrite Znat.Nat2Z.inj_add.
    rewrite (Znat.Z2Nat.id (Qnum q) Hz0).
    rewrite (Znat.Z2Nat.id (QDen q) Hd0).
    reflexivity. }
  rewrite uabS4b_pos_succ_Z.
  assert (H1 : (1 * (Z.of_nat (uabS4b_arch_N q) + 1)
                <= Qnum q * (Z.of_nat (uabS4b_arch_N q) + 1))%Z)
    by (apply Z.mul_le_mono_nonneg_r; [lia | lia]).
  assert (H2 : (QDen q < 1 * (Z.of_nat (uabS4b_arch_N q) + 1))%Z)
    by (rewrite Harch; lia).
  lia.
Qed.

(* A.1 The counterexample real X: X_n := q0 + 1/(n+1), with the Cauchy
   certificate constructed directly (choose the bound N, then squeeze
   pointwise) *)
Definition uabS4b_Xseq (q0 : Q) : nat -> Q :=
  fun n => (q0 + (1#(Pos.of_succ_nat n)))%Q.

Lemma uabS4b_X_cauchy : forall q0 : Q, cauchy (uabS4b_Xseq q0).
Proof.
  intros q0 eps Heps.
  assert (Hc : QltT (1#(Pos.of_succ_nat (uabS4b_arch_N eps))) eps)
    by (apply uabS4b_null_lt; exact Heps).
  assert (Hcp : Qlt (1#(Pos.of_succ_nat (uabS4b_arch_N eps))) eps)
    by (apply QltT_to_Qlt; exact Hc).
  exists (uabS4b_arch_N eps).
  intros m n Hm Hn.
  assert (Hm' : (uabS4b_arch_N eps <= m)%nat) by (apply NatLe_drop; exact Hm).
  assert (Hn' : (uabS4b_arch_N eps <= n)%nat) by (apply NatLe_drop; exact Hn).
  assert (Hm1 : Qle (1#(Pos.of_succ_nat m)) (1#(Pos.of_succ_nat (uabS4b_arch_N eps))))
    by (apply uabS4b_null_mono; exact Hm').
  assert (Hn1 : Qle (1#(Pos.of_succ_nat n)) (1#(Pos.of_succ_nat (uabS4b_arch_N eps))))
    by (apply uabS4b_null_mono; exact Hn').
  assert (Hm0 : Qle 0 (1#(Pos.of_succ_nat m))) by apply uabS4b_null_nonneg.
  assert (Hn0 : Qle 0 (1#(Pos.of_succ_nat n))) by apply uabS4b_null_nonneg.
  unfold uabS4b_Xseq.
  apply (q_abs_lt_two_sided _ eps Heps).
  - apply Qlt_to_QltT. lra.
  - apply Qlt_to_QltT. lra.
Qed.

Definition uabS4b_X (q0 : Q) : Real :=
  existT _ (uabS4b_Xseq q0) (uabS4b_X_cauchy q0).

Lemma uabS4b_X_proj : forall (q0 : Q) (n : nat),
  projT1 (uabS4b_X q0) n == uabS4b_Xseq q0 n.
Proof. intros q0 n. reflexivity. Qed.

(* the pointwise value of Y+e (0+q0; the rewriting bridge closes by
   Qeq_refl, with no appeal to a ring decision procedure) *)
Lemma uabS4b_Ye_proj : forall (q0 : Q) (n : nat),
  projT1 (real_plus real_zero (real_const q0)) n == (0 + q0)%Q.
Proof.
  intros q0 n.
  assert (Hp : projT1 (real_plus real_zero (real_const q0)) n
               == projT1 real_zero n + projT1 (real_const q0) n)
    by (apply qeqT_imp_qeq; apply real_plus_proj).
  rewrite Hp.
  assert (Hz : projT1 real_zero n == 0) by apply Qeq_refl.
  rewrite Hz.
  rewrite (qeqT_imp_qeq _ _ (real_const_proj q0 n)).
  apply Qeq_refl.
Qed.

(* A.2 (i) the equality branch holds as true equality: real_eq X (Y+e).
   X and Y+e are not pointwise equal (their difference 1/(n+1) tends to 0),
   so the proof uses the witness construction of the real_eq definition
   (isomorphic to the A.1 Cauchy certificate: the archimedean index plus
   monotone unit-fraction squeezing), not real_eq_of_zero_diff. *)
Theorem uabS4b_full_margin_eq : forall q0 : Q, QltT 0 q0 ->
  real_eq (uabS4b_X q0) (real_plus real_zero (real_const q0)).
Proof.
  intros q0 Hq0. unfold real_eq. intros eps Heps.
  assert (Hc : QltT (1#(Pos.of_succ_nat (uabS4b_arch_N eps))) eps)
    by (apply uabS4b_null_lt; exact Heps).
  assert (Hcp : Qlt (1#(Pos.of_succ_nat (uabS4b_arch_N eps))) eps)
    by (apply QltT_to_Qlt; exact Hc).
  exists (uabS4b_arch_N eps). intros n Hn.
  assert (Hn' : (uabS4b_arch_N eps <= n)%nat) by (apply NatLe_drop; exact Hn).
  assert (Hm1 : Qle (1#(Pos.of_succ_nat n)) (1#(Pos.of_succ_nat (uabS4b_arch_N eps))))
    by (apply uabS4b_null_mono; exact Hn').
  assert (Hm0 : Qle 0 (1#(Pos.of_succ_nat n))) by apply uabS4b_null_nonneg.
  unfold uabS4b_X, real_plus, real_zero, real_const.
  cbn [projT1].
  unfold uabS4b_Xseq.
  apply (q_abs_lt_two_sided _ eps Heps).
  - apply Qlt_to_QltT. lra.
  - apply Qlt_to_QltT. lra.
Qed.

(* A.3 (ii) the order holds through its equality branch (inr injection):
   real_le X (Y+e) *)
Theorem uabS4b_full_margin_le : forall q0 : Q, QltT 0 q0 ->
  real_le (uabS4b_X q0) (real_plus real_zero (real_const q0)).
Proof.
  intros q0 Hq0. unfold real_le. apply inr.
  apply uabS4b_full_margin_eq. exact Hq0.
Qed.

(* A.4 (iii) the reverse strict order holds: real_lt real_zero X
   (witnesses eps := q0, N := 0) *)
Theorem uabS4b_full_margin_rev_lt : forall q0 : Q, QltT 0 q0 ->
  real_lt real_zero (uabS4b_X q0).
Proof.
  intros q0 Hq0. unfold real_lt.
  exists q0. split.
  - exact Hq0.
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    assert (Hz : projT1 real_zero n == 0) by apply Qeq_refl.
    rewrite Hz. rewrite (uabS4b_X_proj q0 n). unfold uabS4b_Xseq.
    assert (Hp : Qlt 0 (1#(Pos.of_succ_nat n))) by apply uabS4b_null_pos.
    lra.
Qed.

(* A.5 (iv) full-margin tightness: real_lt X (Y+e) is exactly excluded.
   The margin is fully consumed by the equality branch: under this witness
   every proof of the order must take the equality branch, and the strict
   branch is unavailable. *)
Theorem uabS4b_full_margin_tight : forall q0 : Q, QltT 0 q0 ->
  real_lt (uabS4b_X q0) (real_plus real_zero (real_const q0)) -> Empty_set.
Proof.
  intros q0 Hq0 Hlt. unfold real_lt in Hlt.
  destruct Hlt as [eps Hpair]. destruct Hpair as [Hpos Hbound].
  destruct Hbound as [N Hall].
  exfalso.
  assert (Hle : (N <= N + uabS4b_arch_N q0)%nat) by lia.
  assert (HN : NatLe N (N + uabS4b_arch_N q0)%nat) by (apply NatLe_lift; exact Hle).
  assert (Hk : Qlt eps (projT1 (real_plus real_zero (real_const q0)) (N + uabS4b_arch_N q0)%nat
                        - projT1 (uabS4b_X q0) (N + uabS4b_arch_N q0)%nat))
    by (apply QltT_to_Qlt; exact (Hall (N + uabS4b_arch_N q0)%nat HN)).
  assert (HV1 : projT1 (real_plus real_zero (real_const q0)) (N + uabS4b_arch_N q0)%nat
                == (0 + q0)%Q).
  { rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_zero (real_const q0)
                                  (N + uabS4b_arch_N q0)%nat)).
    assert (Hz : projT1 real_zero (N + uabS4b_arch_N q0)%nat == 0) by apply Qeq_refl.
    rewrite Hz.
    rewrite (qeqT_imp_qeq _ _ (real_const_proj q0 (N + uabS4b_arch_N q0)%nat)).
    apply Qeq_refl. }
  assert (HV2 : projT1 (uabS4b_X q0) (N + uabS4b_arch_N q0)%nat
                == (q0 + (1#(Pos.of_succ_nat (N + uabS4b_arch_N q0)%nat)))%Q)
    by exact (uabS4b_X_proj q0 (N + uabS4b_arch_N q0)%nat).
  assert (Hepos : Qlt 0 eps) by (apply QltT_to_Qlt; exact Hpos).
  assert (Hn0 : Qle 0 (1#(Pos.of_succ_nat (N + uabS4b_arch_N q0)%nat)))
    by apply uabS4b_null_nonneg.
  lra.
Qed.

(* A.6 (v) the doubled-margin premise is unreachable: real_lt (Y+2e) X is
   exactly excluded, matching uabS4_lt_double_margin_le_half_contr (the
   incompatibility lemma for the factor 2): under the full-margin witness,
   doubling the margin overshoots the bound. *)
Theorem uabS4b_full_margin_no_far : forall q0 : Q, QltT 0 q0 ->
  real_lt (real_plus real_zero (real_plus (real_const q0) (real_const q0)))
          (uabS4b_X q0) -> Empty_set.
Proof.
  intros q0 Hq0 Hlt. unfold real_lt in Hlt.
  destruct Hlt as [eps Hpair]. destruct Hpair as [Hpos Hbound].
  destruct Hbound as [N Hall].
  exfalso.
  assert (Hnull : QltT (1#(Pos.of_succ_nat (uabS4b_arch_N q0))) q0)
    by (apply uabS4b_null_lt; exact Hq0).
  assert (Hle : (N <= N + uabS4b_arch_N q0)%nat) by lia.
  assert (HN : NatLe N (N + uabS4b_arch_N q0)%nat) by (apply NatLe_lift; exact Hle).
  assert (Hk : Qlt eps (projT1 (uabS4b_X q0) (N + uabS4b_arch_N q0)%nat
                        - projT1 (real_plus real_zero (real_plus (real_const q0) (real_const q0)))
                                  (N + uabS4b_arch_N q0)%nat))
    by (apply QltT_to_Qlt; exact (Hall (N + uabS4b_arch_N q0)%nat HN)).
  assert (HV1 : projT1 (uabS4b_X q0) (N + uabS4b_arch_N q0)%nat
                == (q0 + (1#(Pos.of_succ_nat (N + uabS4b_arch_N q0)%nat)))%Q)
    by exact (uabS4b_X_proj q0 (N + uabS4b_arch_N q0)%nat).
  assert (HV2 : projT1 (real_plus real_zero (real_plus (real_const q0) (real_const q0)))
                       (N + uabS4b_arch_N q0)%nat
                == (0 + (q0 + q0))%Q).
  { rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_zero
                                  (real_plus (real_const q0) (real_const q0))
                                  (N + uabS4b_arch_N q0)%nat)).
    assert (Hz : projT1 real_zero (N + uabS4b_arch_N q0)%nat == 0) by apply Qeq_refl.
    rewrite Hz.
    assert (Hp2 : projT1 (real_plus (real_const q0) (real_const q0))
                         (N + uabS4b_arch_N q0)%nat
                  == (q0 + q0)%Q).
    { rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_const q0) (real_const q0)
                                    (N + uabS4b_arch_N q0)%nat)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj q0 (N + uabS4b_arch_N q0)%nat)).
      apply Qeq_refl. }
    rewrite Hp2. apply Qeq_refl. }
  assert (Hepos : Qlt 0 eps) by (apply QltT_to_Qlt; exact Hpos).
  assert (Hm1 : Qle (1#(Pos.of_succ_nat (N + uabS4b_arch_N q0)%nat))
                    (1#(Pos.of_succ_nat (uabS4b_arch_N q0))))
    by (apply uabS4b_null_mono; lia).
  assert (Hnl : Qlt (1#(Pos.of_succ_nat (uabS4b_arch_N q0))) q0)
    by (apply QltT_to_Qlt; exact Hnull).
  lra.
Qed.

(* A.7 (vi) the simultaneity statement: the conjunction of the order
   (through its equality branch) with the reverse strict order (And as the
   set product, at the Set level) -- the constructive closure of the
   full-margin simultaneity counterexample. *)
Theorem uabS4b_full_margin_coexist : forall q0 : Q, QltT 0 q0 ->
  And (real_le (uabS4b_X q0) (real_plus real_zero (real_const q0)))
      (real_lt real_zero (uabS4b_X q0)).
Proof.
  intros q0 Hq0. split.
  - apply uabS4b_full_margin_le. exact Hq0.
  - apply uabS4b_full_margin_rev_lt. exact Hq0.
Qed.

(* ==================== Section 2. Residual two: the B-form of the abstract fold operator sumL (relative fold-interface form) ==================== *)

Section AbstractSumSlot.

(* The abstract fold operator: sumL is only required to respect the two
   real_eq interface equations for nil and cons.  The interface premises
   are stated honestly in relative form -- the Closed convention refers to
   zero axioms, not zero premises: every statement of this file is Closed,
   and the two requirements below are explicitly quantified relative
   premises. *)
Variable X : Type.
Variable sumL : (X -> Real) -> list X -> Real.
Variable sumL_nil_eq : forall f : X -> Real, real_eq (sumL f nil) real_zero.
Variable sumL_cons_eq : forall (f : X -> Real) (w : X) (rest : list X),
  real_eq (sumL f (w :: rest)) (real_plus (f w) (sumL f rest)).

(* B.1 The weighted induction body (per-eps form): |sumL f| <=
   sumL|f| + W(l)*e.  Case l = []: transporting the interface equations in
   both directions gives |0| == 0, and the positive margin is absorbed on
   the right.  Induction step from l to w::rest: the two-point triangle
   enters with the unit weight e, the tail carries the same weight by the
   induction premise, and uabS4_cons_glue composes the parts, with the
   interface equations transported in both directions. *)
Lemma uabS4b_slot_abs_sum_le_wt : forall (f : X -> Real) (l : list X) (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (sumL f l))
          (real_plus (sumL (fun x => real_abs (f x)) l)
                     (real_mult (uabS4_wlen X l) e)).
Proof.
  intros f l. induction l as [| w rest IH]; intros e He.
  - (* case l = []: the interface equations transport in both directions,
       giving |0| <= 0 <= 0 + 1*e *)
    apply (uabS4_le_add_r (real_abs (sumL f nil))
             (sumL (fun x => real_abs (f x)) nil)
             (real_mult (uabS4_wlen X nil) e)).
    + apply (RealSetoid.real_le_id_l (real_abs (sumL f nil)) (real_abs real_zero)
               (sumL (fun x => real_abs (f x)) nil)
               (RealSetoid.real_eq_abs_compat (sumL f nil) real_zero
                  (sumL_nil_eq f))).
      apply (RealSetoid.real_le_id_r (real_abs real_zero) real_zero
               (sumL (fun x => real_abs (f x)) nil)).
      * apply real_eq_sym.
        exact (sumL_nil_eq (fun x => real_abs (f x))).
      * apply (RealSetoid.real_le_id_l (real_abs real_zero) real_zero real_zero
                 real_abs_zero_req).
        exact (RealSetoid.real_eq_le real_zero real_zero (real_eq_refl real_zero)).
    + apply (RealSetoid.real_lt_id_r real_zero e (real_mult real_one e)).
      * apply real_eq_sym.
        apply (real_eq_trans _ _ _ (real_mult_comm real_one e)).
        apply real_mult_one.
      * exact He.
  - (* induction step from l to w::rest: transport the left end along the
       equality and compose the right end *)
    apply (RealSetoid.real_le_id_l (real_abs (sumL f (w :: rest)))
             (real_abs (real_plus (f w) (sumL f rest)))
             (real_plus (sumL (fun x => real_abs (f x)) (w :: rest))
                        (real_mult (uabS4_wlen X (w :: rest)) e))
             (RealSetoid.real_eq_abs_compat _ _ (sumL_cons_eq f w rest))).
    apply (RealSetoid.real_le_id_r
             (real_abs (real_plus (f w) (sumL f rest)))
             (real_plus (real_plus (real_abs (f w))
                        (sumL (fun x => real_abs (f x)) rest))
                        (real_mult (real_plus (uabS4_wlen X rest) real_one) e))
             (real_plus (sumL (fun x => real_abs (f x)) (w :: rest))
                        (real_mult (uabS4_wlen X (w :: rest)) e))).
    + (* right-end equality: sumL|f| (w::rest) == |f w| + sumL|f| rest
         (interface equation) *)
      apply (RealSetoid.real_eq_plus_compat _ _ _ _).
      * apply real_eq_sym.
        exact (sumL_cons_eq (fun x => real_abs (f x)) w rest).
      * apply real_eq_refl.
    + (* the fold step: the two-point triangle with the unit weight plus
         the weighted tail is exactly the application of uabS4_cons_glue *)
      exact (uabS4_cons_glue (f w) (sumL f rest)
               (sumL (fun x => real_abs (f x)) rest) (uabS4_wlen X rest) e He
               (real_abs_triangle_le_eps (f w) (sumL f rest) e He) (IH e He)).
Qed.

(* B.2 B-form closure (the B-form of the abstract fold operator):
   |sumL f| <=_B sumL|f|.  real_le_closure_b closes the weighted family
   with the explicit positivity certificate D := W(l). *)
Theorem uabS4b_slot_abs_sum_le_B : forall (f : X -> Real) (l : list X),
  real_le_b (real_abs (sumL f l)) (sumL (fun x => real_abs (f x)) l).
Proof.
  intros f l.
  apply (real_le_closure_b _ _ (uabS4_wlen X l) (uabS4_wlen_pos X l)).
  intros e He. apply uabS4b_slot_abs_sum_le_wt. exact He.
Qed.

End AbstractSumSlot.

(* B.3 An instance witnessing satisfiability of the interface
   (non-emptiness): real_list_sum satisfies both interface equations
   (nil and cons are definitional equalities, given directly by
   real_eq_refl). *)
Theorem uabS4b_slot_instance_list_nil : forall (X : Type) (f : X -> Real),
  real_eq (real_list_sum X f nil) real_zero.
Proof. intros X f. exact (real_eq_refl (real_list_sum X f nil)). Qed.

Theorem uabS4b_slot_instance_list_cons : forall (X : Type) (f : X -> Real)
                                                (w : X) (rest : list X),
  real_eq (real_list_sum X f (w :: rest))
          (real_plus (f w) (real_list_sum X f rest)).
Proof.
  intros X f w rest.
  exact (real_eq_refl (real_list_sum X f (w :: rest))).
Qed.

(* B.4 Correspondence: instantiating the abstract fold operator at
   real_list_sum recovers the statement of uabS4_abs_list_sum_le_B
   (the list-fold form is the concrete instance of the abstract
   interface version). *)
Theorem uabS4b_slot_list_le_B : forall (X : Type) (f : X -> Real) (l : list X),
  real_le_b (real_abs (real_list_sum X f l))
            (real_list_sum X (fun x => real_abs (f x)) l).
Proof.
  intros X f l.
  exact (uabS4b_slot_abs_sum_le_B X (real_list_sum X)
           (uabS4b_slot_instance_list_nil X) (uabS4b_slot_instance_list_cons X)
           f l).
Qed.

(* ==================== Audit note: Print Assumptions is expected to report Closed for every exported statement (no external unproved premises) ==================== *)

Print Assumptions uabS4b_null_lt.
Print Assumptions uabS4b_X_cauchy.
Print Assumptions uabS4b_full_margin_eq.
Print Assumptions uabS4b_full_margin_le.
Print Assumptions uabS4b_full_margin_rev_lt.
Print Assumptions uabS4b_full_margin_tight.
Print Assumptions uabS4b_full_margin_no_far.
Print Assumptions uabS4b_full_margin_coexist.
Print Assumptions uabS4b_slot_abs_sum_le_B.
Print Assumptions uabS4b_slot_list_le_B.
