(* ConstructiveWorld-Set — joint two-scale fillings of the anchor target family. *)

(** * LW3JointFill: joint fillings of the anchor target [lw381_joint_target] at two scales.

    Mission.  The anchor polynomial [p381] (one plus t) is scaled by the
      factorial-reciprocal constant [lw381_scale_const] at scales one and
      zero ([N1_381]/[N0_381]); [Ef1_381]/[Ef0_381] witness
      [lw381_pnode_fam] via the general lemma [lw384_pt_le_nodewsum], the
      strict weighted-total endpoints reuse [lw381_rev_wsum1]/
      [lw381_rev_wsum0], and [lw384_joint_fill1]/[lw384_joint_fill0]
      fill [lw381_joint_target] at both scales.

    Dependencies.  Stdlib [QArith], [Lia], [Arith], [ZArith], [List],
      [QArith_base], [QArith.Qabs]; requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], the LW0/LW1/LW2 modules and
      [LW3ETranscendental] (read-only) of this development.

    References.  This development, [LW3ETranscendental].v; the baseline
      module of the same name in ConstructiveWorld-Main, whose statement
      names are carried over here verbatim.

    Constructivity.  All named statements are carried by [Set]
      ([QltT]/[QeqT]/[QleT'] forms and [match] value pins over
      [Qeq_bool]); zero admission words; no classical axioms; no new
      [Prop] forms in statement or premise positions; extraction names
      data only ([p381], [m381], [n1_381], [n0_381]).

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      LW3JointFill.v] compiles cleanly (exit 0); the first eight bytes of
      the artifact are [436f7121 00015ff4]. *)
Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import QArith_base.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW1ZPoly.
Require Import LW2Hermite.
Require Import LW2IntegMachine.
Require Import LW0FactGrowth.
Require Import LW2UpperBound.
Require Import LW2NivenInt.
Require Import LW3ETranscendental.

(* The anchor source polynomial one plus t.                                *)
Definition p381 : zpoly := cons 1%Z (cons 1%Z nil).

(* The two explicit scales of the joint accounting: one and zero.         *)
Definition N1_381 : nat := 1.
Definition N0_381 : nat := 0.

(* The rank of the factorial-reciprocal scale constant.                   *)
Definition m381 : nat := 7.

(* The factorial-reciprocal scale constant at rank m.                     *)
Definition lw381_scale_const (m : nat) : Q := / (q_fact m)%Q.

(* The scaled family face: the built integrand under the factorial-       *)
(* reciprocal scalar.  The scalar operator maps cons to cons, so the      *)
(* derivative-order count of the family is unchanged.                     *)
Definition lw381_fbuild_scaled (p : zpoly) (sg N m : nat) : QPoly :=
  qpoly_scalar (lw381_scale_const m) (lw3_fbuild p sg N).

(* The node counts at both scales.                                        *)
Definition n1_381 : nat := lw3_nodecount p381 N1_381.
Definition n0_381 : nat := lw3_nodecount p381 N0_381.

(* The scaled family instances at both scales.                            *)
Definition f1_381 : QPoly := lw381_fbuild_scaled p381 (lw3_deg p381) N1_381 m381.
Definition f0_381 : QPoly := lw381_fbuild_scaled p381 (lw3_deg p381) N0_381 m381.

(* Scalar linearity at the coefficient level: every coefficient of the    *)
(* scaled polynomial is the scale constant times the base coefficient.    *)
Lemma lw381_coef_scalar : forall (a : Q) (f : QPoly) (j : nat),
  QeqT (lw0_coef j (qpoly_scalar a f)) (a * lw0_coef j f)%Q.
Proof.
  intros a f j. apply qeq_imp_qeqT. revert j.
  induction f as [|b f IH]; intro j.
  - cbn [qpoly_scalar lw0_coef]. ring.
  - destruct j as [|j].
    + cbn [qpoly_scalar lw0_coef]. ring.
    + cbn [qpoly_scalar lw0_coef]. apply IH.
Qed.

(* First-order dual face: differentiation passes through the scalar at    *)
(* every evaluation point, so each first derivative of the scaled family  *)
(* equals the scale constant times the unscaled one.                      *)
Lemma lw381_eval_deriv1_scalar : forall (a : Q) (g : QPoly) (x : Q),
  QeqT (qpoly_eval (qpoly_deriv (qpoly_scalar a g)) x)
  (a * qpoly_eval (qpoly_deriv g) x)%Q.
Proof.
  intros a g x. apply qeq_imp_qeqT.
  destruct g as [|b g'].
  - cbn [qpoly_scalar qpoly_deriv qpoly_eval]. ring.
  - cbn [qpoly_scalar qpoly_deriv].
    rewrite qpoly_eval_add.
    rewrite qpoly_eval_add.
    cbn [qpoly_eval].
    rewrite qpoly_eval_scalar.
    rewrite qpoly_eval_deriv_scalar.
    rewrite qpoly_eval_scalar.
    cbn [qpoly_eval].
    ring.
Qed.

(* The pointwise floor on the scaled family: the sum of absolute          *)
(* derivative values over the full node and order grid.                   *)
Definition lw381_pwsum (n : nat) (f : QPoly) : Q :=
  lw2_qsum0 (fun j => lw2_qsum0 (fun k =>
      Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))
      (length f))
    (Datatypes.S (Datatypes.S n)).

(* The endpoint floor on the scaled family: the two endpoint absolute     *)
(* sums that any sound accounting of the node functional value covers.    *)
Definition lw381_rfsum (n : nat) (f : QPoly) : Q :=
  lw2_qsum0 (fun k => Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node 0)))
            (length f) +
  lw2_qsum0 (fun k =>
      Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node (Datatypes.S n))))
            (length f).

(* The per-node full sum, serving as the bound-family entry at each node. *)
Definition lw381_nodewsum (f : QPoly) (j : nat) : Q :=
  lw2_qsum0 (fun k => Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))
            (length f).

(* The bound-family entries at both scales, on the scaled instances.      *)
Definition Ef1_381 : nat -> Q := lw381_nodewsum f1_381.
Definition Ef0_381 : nat -> Q := lw381_nodewsum f0_381.

(* Reversal value pins at scale one: functional value, endpoint floor and *)
(* pointwise floor of the scaled family, all divided by the rank-seven    *)
(* factorial.                                                             *)
Definition lw381_lam1s_val :
  match Qeq_bool (lw2_lambda n1_381 f1_381) ((-265) # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw381_rf1s_val :
  match Qeq_bool (lw381_rfsum n1_381 f1_381) (281 # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw381_pw1s_val :
  match Qeq_bool (lw381_pwsum n1_381 f1_381) (613 # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

(* Reversal value pins at scale zero.                                     *)
Definition lw381_lam0s_val :
  match Qeq_bool (lw2_lambda n0_381 f0_381) ((-15) # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw381_rf0s_val :
  match Qeq_bool (lw381_rfsum n0_381 f0_381) (19 # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw381_pw0s_val :
  match Qeq_bool (lw381_pwsum n0_381 f0_381) (34 # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

(* Structure bridge pins: multiplying the scaled functional value by the  *)
(* rank-seven factorial restores the unscaled functional value, so the    *)
(* congruence structure of the integer functional transfers through the   *)
(* scale in scaled-back form.                                             *)
Definition lw381_bridge1_val :
  match Qeq_bool ((q_fact m381)%Q * lw2_lambda n1_381 f1_381)
                  ((-265) # 1)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw381_bridge0_val :
  match Qeq_bool ((q_fact m381)%Q * lw2_lambda n0_381 f0_381)
                  ((-15) # 1)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

(* Weighted total of the bound family over the scaled instance: the       *)
(* derivative-order count times the family entries, summed over the       *)
(* node grid.                                                             *)
Definition lw381_wsum (p : zpoly) (N m : nat) (Ef : nat -> Q) : Q :=
  lw0_q_of_nat (length (lw381_fbuild_scaled p (lw3_deg p) N m)) *
  lw2_qsum0 Ef (Datatypes.S (Datatypes.S (lw3_nodecount p N))).

(* Weighted-total reversal value pins at both scales: with the per-node   *)
(* full sums as entries, the weighted total of the scaled family falls    *)
(* below the unscaled pointwise floor divided by the rank-seven factorial *)
(* times the order count.                                                 *)
Definition lw381_wsum1s_val :
  match Qeq_bool (lw381_wsum p381 N1_381 m381 Ef1_381) (2452 # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw381_wsum0s_val :
  match Qeq_bool (lw381_wsum p381 N0_381 m381 Ef0_381) (102 # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

(* Strict reversal at scale one: the node functional value of the scaled  *)
(* family lies strictly below one in absolute value.                      *)
Theorem lw381_rev_lam1 :
  QltT (Qabs (lw2_lambda n1_381 f1_381)) (1 # 1)%Q.
Proof. vm_compute. constructor. Qed.

(* Strict reversal at scale one, endpoint floor.                          *)
Theorem lw381_rev_rf1 :
  QltT (lw381_rfsum n1_381 f1_381) (1 # 1)%Q.
Proof. vm_compute. constructor. Qed.

(* Strict reversal at scale one, pointwise floor.                         *)
Theorem lw381_rev_pw1 :
  QltT (lw381_pwsum n1_381 f1_381) (1 # 1)%Q.
Proof. vm_compute. constructor. Qed.

(* Strict reversal at scale one, weighted total.                          *)
Theorem lw381_rev_wsum1 :
  QltT (lw381_wsum p381 N1_381 m381 Ef1_381) (1 # 1)%Q.
Proof. vm_compute. constructor. Qed.

(* The four strict reversals at scale zero.                               *)
Theorem lw381_rev_lam0 :
  QltT (Qabs (lw2_lambda n0_381 f0_381)) (1 # 1)%Q.
Proof. vm_compute. constructor. Qed.

Theorem lw381_rev_rf0 :
  QltT (lw381_rfsum n0_381 f0_381) (1 # 1)%Q.
Proof. vm_compute. constructor. Qed.

Theorem lw381_rev_pw0 :
  QltT (lw381_pwsum n0_381 f0_381) (1 # 1)%Q.
Proof. vm_compute. constructor. Qed.

Theorem lw381_rev_wsum0 :
  QltT (lw381_wsum p381 N0_381 m381 Ef0_381) (1 # 1)%Q.
Proof. vm_compute. constructor. Qed.

(* The per-node bound-family premise in data form, reposed over the       *)
(* scaled family: every derivative value at every node is bounded by the  *)
(* family entry at that node.                                             *)
Definition lw381_pnode_fam (p : zpoly) (N m : nat) (Ef : nat -> Q) : Set :=
  forall (j k : nat),
    Nat.le j (Datatypes.S (lw3_nodecount p N)) ->
    Nat.lt k (length (lw381_fbuild_scaled p (lw3_deg p) N m)) ->
    QleT' (Qabs (qpoly_eval
                   (qpoly_deriv_iter k (lw381_fbuild_scaled p (lw3_deg p) N m))
                   (lw2_node j)))
          (Ef j).

(* The joint bearing form of the two-boundary production line, reposed    *)
(* over the scaled family at explicit scale rank: a bound family covering *)
(* every node value, whose weighted total stays below one.                *)
Definition lw381_joint_target (p : zpoly) (N m : nat) : Set :=
  sigT (fun Ef : nat -> Q =>
    And (lw381_pnode_fam p N m Ef)
        (QltT (lw381_wsum p N m Ef) (1 # 1)%Q)).


(* Nonnegativity of the summed absolute values over an order grid.          *)
Lemma lw384_qsum0_abs_nonneg : forall (n : nat) (g : nat -> Q),
  QleT' (0%Q) (lw2_qsum0 (fun i => Qabs (g i)) n).
Proof.
  intros n. induction n as [| n IH]; intros g.
  - apply Qle_to_QleT'. cbn [lw2_qsum0]. apply (Qle_refl 0%Q).
  - apply Qle_to_QleT'. cbn [lw2_qsum0]. apply (Qle_trans _ ((0%Q) + (0%Q))).
    + apply (Qle_refl (0%Q)).
    + apply Qplus_le_compat.
      * apply (QleT'_to_Qle _ _ (IH g)).
      * apply Qabs_nonneg.
Qed.

(* Membership face: one absolute term of a grid is covered by the full      *)
(* absolute sum over the same grid.                                         *)
Lemma lw384_qsum0_member_abs_le : forall (n : nat) (g : nat -> Q) (k : nat),
  Nat.lt k n ->
  QleT' (Qabs (g k)) (lw2_qsum0 (fun i => Qabs (g i)) n).
Proof.
  intros n. induction n as [| n IH]; intros g k Hk.
  - exfalso. lia.
  - cbn [lw2_qsum0]. destruct (Nat.eq_dec k n) as [He|Hne].
    + subst k. apply Qle_to_QleT'.
      apply (Qle_trans _ ((0%Q) + Qabs (g n))).
      * rewrite Qplus_0_l. apply (Qle_refl (Qabs (g n))).
      * apply Qplus_le_compat.
        -- apply (QleT'_to_Qle _ _ (lw384_qsum0_abs_nonneg n g)).
        -- apply (Qle_refl (Qabs (g n))).
    + assert (Hlt : Nat.lt k n) by lia.
      specialize (IH g k Hlt).
      apply Qle_to_QleT'.
      apply (Qle_trans _ (lw2_qsum0 (fun i => Qabs (g i)) n + (0%Q))).
      * rewrite Qplus_0_r. exact (QleT'_to_Qle _ _ IH).
      * apply Qplus_le_compat.
        -- apply (Qle_refl (lw2_qsum0 (fun i => Qabs (g i)) n)).
        -- apply Qabs_nonneg.
Qed.

(* Single-point face on the family: one derivative value at a node is       *)
(* covered by the per-node full-sum entry of the bound family.              *)
Lemma lw384_pt_le_nodewsum : forall (f : QPoly) (j k : nat),
  Nat.lt k (length f) ->
  QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))
        (lw381_nodewsum f j).
Proof.
  intros f j k Hk. unfold lw381_nodewsum.
  apply (lw384_qsum0_member_abs_le (length f)
           (fun i => qpoly_eval (qpoly_deriv_iter i f) (lw2_node j)) k Hk).
Qed.

(* Anchor filling at scale one: the per-node full-sum family witnesses      *)
(* the joint bearing form, with the weighted total strictly below one.      *)
Theorem lw384_joint_fill1 : lw381_joint_target p381 N1_381 m381.
Proof.
  exists Ef1_381. split.
  - intros j k Hj Hk. exact (lw384_pt_le_nodewsum f1_381 j k Hk).
  - exact lw381_rev_wsum1.
Qed.

(* Anchor filling at scale zero.                                            *)
Theorem lw384_joint_fill0 : lw381_joint_target p381 N0_381 m381.
Proof.
  exists Ef0_381. split.
  - intros j k Hj Hk. exact (lw384_pt_le_nodewsum f0_381 j k Hk).
  - exact lw381_rev_wsum0.
Qed.

Print Assumptions lw381_coef_scalar.
Print Assumptions lw381_eval_deriv1_scalar.
Print Assumptions lw381_lam1s_val.
Print Assumptions lw381_rf1s_val.
Print Assumptions lw381_pw1s_val.
Print Assumptions lw381_lam0s_val.
Print Assumptions lw381_rf0s_val.
Print Assumptions lw381_pw0s_val.
Print Assumptions lw381_bridge1_val.
Print Assumptions lw381_bridge0_val.
Print Assumptions lw381_wsum1s_val.
Print Assumptions lw381_wsum0s_val.
Print Assumptions lw381_rev_lam1.
Print Assumptions lw381_rev_rf1.
Print Assumptions lw381_rev_pw1.
Print Assumptions lw381_rev_wsum1.
Print Assumptions lw381_rev_lam0.
Print Assumptions lw381_rev_rf0.
Print Assumptions lw381_rev_pw0.
Print Assumptions lw381_rev_wsum0.
Print Assumptions lw381_joint_target.
Print Assumptions lw384_qsum0_abs_nonneg.
Print Assumptions lw384_qsum0_member_abs_le.
Print Assumptions lw384_pt_le_nodewsum.
Print Assumptions lw384_joint_fill1.
Print Assumptions lw384_joint_fill0.

From Stdlib Require Import Extraction.
Separate Extraction p381 m381 n1_381 n0_381.
