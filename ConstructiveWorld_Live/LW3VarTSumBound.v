(* ConstructiveWorld-Set -- variable-bound sum upper bounds for the lambda functional. *)

(** * LW3VarTSumBound: variable-bound triangle sums and lambda upper bounds.

    Mission.  This file lifts the uniform-bound triangle lemma of the 378
      skeleton to the variable-bound form: with one independent bound per
      term, the absolute value of a finite rational sum is covered by the
      sum of the per-term bounds [lw384_qsum0_abs_le_vt], with the
      constant-sum face [lw384_qsum0_const] and the scalar pull-out face
      [lw384_qsum0_scale].  The single-node face [lw384_node_term_abs_le_vt]
      feeds the per-node family upper bound [lw384_lambda_upper_nodes_vt]
      for the lambda functional; the constant specialization
      [lw384_qsum0_abs_le_uniform] recovers the uniform triangle.

    Dependencies.  Stdlib [QArith], [Arith], [ZArith], [Lia], [List],
      [QArith.Qabs], [QArith_base].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [LW0QPoly], [LW0FactGrowth], [LW2Hermite],
      [LW2UpperBound] of this development.

    References.  This development, LW3VarTSumBound.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" LW3VarTSumBound.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import QArith_base.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import LW0QPoly.
Require Import LW0FactGrowth.
Require Import LW2Hermite.
Require Import LW2UpperBound.

(* Variable-bound triangle core: with per-term independent bounds, the      *)
(* absolute value of a sum is covered by the sum of the bounds.             *)
Lemma lw384_qsum0_abs_le_vt : forall (m : nat) (g : nat -> Q) (T : nat -> Q),
  (forall j, Nat.lt j m -> QleT' (Qabs (g j)) (T j)) ->
  QleT' (Qabs (lw2_qsum0 g m)) (lw2_qsum0 T m).
Proof.
  intros m. induction m as [| m IH]; intros g T H.
  - cbn [lw2_qsum0]. apply Qle_to_QleT'.
    assert (Hz : Qabs (0#1)%Q == (0#1)%Q) by reflexivity.
    rewrite Hz. apply (Qle_refl (0#1)%Q).
  - cbn [lw2_qsum0].
    assert (Hprev : QleT' (Qabs (lw2_qsum0 g m)) (lw2_qsum0 T m))
      by (apply IH; intros j Hj; apply H; lia).
    assert (Hlast : QleT' (Qabs (g m)) (T m)) by (apply H; lia).
    apply Qle_to_QleT'.
    apply (Qle_trans _ (Qabs (lw2_qsum0 g m) + Qabs (g m))).
    + apply Qabs_triangle.
    + apply Qplus_le_compat;
        [ exact (QleT'_to_Qle _ _ Hprev) | exact (QleT'_to_Qle _ _ Hlast) ].
Qed.

(* Constant-term sum: summing one bound over the grid is the uniform        *)
(* order-count product.                                                     *)
Lemma lw384_qsum0_const : forall (m : nat) (c : Q),
  lw2_qsum0 (fun _ => c) m == lw0_q_of_nat m * c.
Proof.
  induction m as [| m IH]; intros c.
  - reflexivity.
  - cbn [lw2_qsum0]. rewrite IH.
    rewrite (qeqT_imp_qeq _ _ (lw2u_q_of_nat_succ m)). ring.
Qed.

(* Scalar pull-out: sums commute with the scalar product.                   *)
Lemma lw384_qsum0_scale : forall (m : nat) (c : Q) (g : nat -> Q),
  lw2_qsum0 (fun j => c * g j) m == c * lw2_qsum0 g m.
Proof.
  induction m as [| m IH]; intros c g.
  - cbn [lw2_qsum0]. ring.
  - cbn [lw2_qsum0]. rewrite IH. ring.
Qed.

(* Single-node face with per-order bounds: the weighted derivative sum at   *)
(* one node is covered by the sum of its order bounds.                      *)
Lemma lw384_node_term_abs_le_vt : forall (n : nat) (f : QPoly) (j : nat)
                                         (E : nat -> Q),
  (forall k, Nat.lt k (length f) ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))) (E k)) ->
  QleT' (Qabs (lw2_qsum0 (fun k =>
            ((lw2_lambda_coef n j k) # 1)%Q *
            qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
            (length f)))
        (lw2_qsum0 E (length f)).
Proof.
  intros n f j E H.
  apply (lw384_qsum0_abs_le_vt (length f)
    (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
              qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) E).
  intros k Hk. apply Qle_to_QleT'. rewrite Qabs_Qmult.
  apply (Qle_trans _ ((1 # 1)%Q *
           Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))).
  - apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ (lw2u_coef_abs_le_one n j k)).
    + apply Qabs_nonneg.
  - assert (Hx1 : (1 # 1)%Q *
             Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) ==
             Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))) by ring.
    rewrite Hx1. exact (QleT'_to_Qle _ _ (H k Hk)).
Qed.

(* Per-node-family upper face for the node functional: with one bound       *)
(* entry per node, the functional value is covered by the order count       *)
(* times the family total over the node grid.                               *)
Theorem lw384_lambda_upper_nodes_vt : forall (n : nat) (f : QPoly) (Ef : nat -> Q),
  (forall j k, Nat.le j (Datatypes.S n) -> Nat.lt k (length f) ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))) (Ef j)) ->
  QleT' (Qabs (lw2_lambda n f))
        (lw0_q_of_nat (length f) *
         lw2_qsum0 Ef (Datatypes.S (Datatypes.S n))).
Proof.
  intros n f Ef H. unfold lw2_lambda. cbv beta.
  apply (lw2u_qleT'_eq_r _
    (lw2_qsum0 (fun j => lw0_q_of_nat (length f) * Ef j)
               (Datatypes.S (Datatypes.S n)))).
  - apply (lw384_qsum0_abs_le_vt (Datatypes.S (Datatypes.S n))
      (fun j => lw2_qsum0
        (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
                  qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
        (length f))
      (fun j => lw0_q_of_nat (length f) * Ef j)).
    intros j Hj. cbv beta.
    apply (lw2u_qleT'_eq_r _ (lw2_qsum0 (fun k => Ef j) (length f))).
    + apply (lw384_node_term_abs_le_vt n f j (fun k => Ef j)).
      intros k Hk. apply H; lia.
    + cbv beta. apply lw384_qsum0_const.
  - rewrite (lw384_qsum0_scale (Datatypes.S (Datatypes.S n))
              (lw0_q_of_nat (length f)) Ef).
    reflexivity.
Qed.

(* Uniform recovery: the constant-bound triangle of the 378 skeleton is     *)
(* the constant specialization of the variable-bound core.                  *)
Corollary lw384_qsum0_abs_le_uniform : forall (m : nat) (g : nat -> Q) (T : Q),
  (forall j, Nat.lt j m -> QleT' (Qabs (g j)) T) ->
  QleT' (Qabs (lw2_qsum0 g m)) (lw0_q_of_nat m * T).
Proof.
  intros m g T H.
  apply (lw2u_qleT'_eq_r _ (lw2_qsum0 (fun _ => T) m)).
  - apply lw384_qsum0_abs_le_vt. intros j Hj. exact (H j Hj).
  - apply lw384_qsum0_const.
Qed.

Print Assumptions lw384_qsum0_abs_le_vt.
Print Assumptions lw384_qsum0_const.
Print Assumptions lw384_qsum0_scale.
Print Assumptions lw384_node_term_abs_le_vt.
Print Assumptions lw384_lambda_upper_nodes_vt.
Print Assumptions lw384_qsum0_abs_le_uniform.
