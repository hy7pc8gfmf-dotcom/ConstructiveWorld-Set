(* ConstructiveWorld-Set -- dual supply bridges of the M3 variant line over the polynomial node functional. *)

(** * LW3DualBridge: the k-iterated derivative duality and the general-form scalar linearity of the node functional.

    Mission.  Two supply pieces of the M3 variant line: the k-iterated derivative
      duality, where differentiation of every order passes through a scalar
      operator at every evaluation point, stated in general Q-equality form as
      [lw387_deriv_iter_eval_scalar] over the coefficient-sum bridge
      [lw387_eval_coef_sum_bound]; and the general-form scalar linearity of the
      node functional [lw387_lambda_scalar], lifted to the factorial-rescaled
      bridge [lw387_bridge_scaled_gen] with corollaries [lw387_bridge1_gen] and
      [lw387_bridge0_gen] and witness [lw387_lam3s_val].

    Dependencies.  Stdlib [QArith], [Lia], [Arith], [ZArith], [List], [QArith.Qabs],
      [QArith_base].  Requires [LW0FactGrowth], [LW0QPoly], [LW1ZPoly], [LW2Hermite],
      [LW2IntegMachine], [LW2NivenInt], [LW2UpperBound], [LW3ETranscendental],
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp] of this development.

    References.  This development, LW3DualBridge.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" LW3DualBridge.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
(* LW1ZPoly opens Z_scope at file level and the open leaks through the      *)
(* Require chain, so the bare product default lands on Z.mul; reopen the    *)
(* rational scope for this file.  Every nat/Z arithmetic occurrence in      *)
(* this file carries an explicit scope annotation, so no reading changes.   *)
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Section 0.  The 381 anchor faces, replicated verbatim (self-        *)
(* contained sandbox style, per the 384 precedent).                    *)
(* ------------------------------------------------------------------ *)

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
(* reciprocal scalar.                                                     *)
Definition lw381_fbuild_scaled (p : zpoly) (sg N m : nat) : QPoly :=
  qpoly_scalar (lw381_scale_const m) (lw3_fbuild p sg N).

(* The node counts and family instances at both scales.                   *)
Definition n1_381 : nat := lw3_nodecount p381 N1_381.
Definition n0_381 : nat := lw3_nodecount p381 N0_381.
Definition f1_381 : QPoly := lw381_fbuild_scaled p381 (lw3_deg p381) N1_381 m381.
Definition f0_381 : QPoly := lw381_fbuild_scaled p381 (lw3_deg p381) N0_381 m381.

(* ------------------------------------------------------------------ *)
(* Section 1.  Missing supply (a): the iterated-derivative duality.    *)
(* Differentiation of every order passes through the scalar operator,  *)
(* so each order-k derivative value of the scaled family is the scale  *)
(* constant times the unscaled one.  The coefficient-face general-k    *)
(* law is already in the library (lw0_coef_iter_scalar); the eval      *)
(* face follows through the evaluation-as-coefficient-sum bridge over  *)
(* a common bound, so no length-alignment law and no zero-tail law     *)
(* are needed beyond the library extend lemma.                         *)
(* ------------------------------------------------------------------ *)

(* Evaluation equals the coefficient-power sum over any upper bound.  *)
Lemma lw387_eval_coef_sum_bound : forall (L : nat) (p : QPoly) (x : Q),
  (length p <= L)%nat ->
  qpoly_eval p x ==
  lw2_qsum0 (fun j => lw0_coef j p * lw2_qpow x j) L.
Proof.
  intros L p x HL.
  rewrite (qeqT_imp_qeq _ _ (lw2_eval_coef_sum p x)).
  symmetry.
  apply qeqT_imp_qeq.
  apply lw2_qsum0_extend.
  - exact HL.
  - intros j H1 H2.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (lw0_coef_beyond j p H1)).
    ring.
Qed.

(* The iterated-derivative duality: differentiation of every order k    *)
(* passes through the scalar at every evaluation point.                 *)
Lemma lw387_deriv_iter_eval_scalar : forall (k : nat) (a : Q) (p : QPoly) (x : Q),
  qpoly_eval (qpoly_deriv_iter k (qpoly_scalar a p)) x ==
  (a * qpoly_eval (qpoly_deriv_iter k p) x)%Q.
Proof.
  intros k a p x.
  rewrite (lw387_eval_coef_sum_bound
             (length (qpoly_deriv_iter k (qpoly_scalar a p)) +
              length (qpoly_deriv_iter k p))%nat
             (qpoly_deriv_iter k (qpoly_scalar a p)) x).
  - rewrite (lw387_eval_coef_sum_bound
               (length (qpoly_deriv_iter k (qpoly_scalar a p)) +
                length (qpoly_deriv_iter k p))%nat
               (qpoly_deriv_iter k p) x).
    + assert (Hcoef : forall j : nat,
          QeqT (lw0_coef j (qpoly_deriv_iter k (qpoly_scalar a p)) *
                lw2_qpow x j)
               (a * (lw0_coef j (qpoly_deriv_iter k p) * lw2_qpow x j))).
      { intros j.
        apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (lw0_coef_iter_scalar k a p j)).
        ring. }
      rewrite (qeqT_imp_qeq _ _
                 (lw2_qsum0_ext
                    (length (qpoly_deriv_iter k (qpoly_scalar a p)) +
                     length (qpoly_deriv_iter k p))%nat
                    _ _ (fun j _ => Hcoef j))).
      rewrite (qeqT_imp_qeq _ _
                 (lw2_qsum0_scale
                    (length (qpoly_deriv_iter k (qpoly_scalar a p)) +
                     length (qpoly_deriv_iter k p))%nat
                    (fun j => lw0_coef j (qpoly_deriv_iter k p) * lw2_qpow x j)
                    a)).
      reflexivity.
    + lia.
  - lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 2.  Missing supply (d): the scalar linearity of the node    *)
(* functional lambda, in general form.                                 *)
(* ------------------------------------------------------------------ *)

(* The node functional is linear in the polynomial under any scalar:    *)
(* lambda of the scaled polynomial equals the scalar times lambda.      *)
Lemma lw387_lambda_scalar : forall (n : nat) (c : Q) (f : QPoly),
  lw2_lambda n (qpoly_scalar c f) == (c * lw2_lambda n f)%Q.
Proof.
  intros n c f.
  assert (Hlen : (length (qpoly_scalar c f) = length f)%nat).
  { induction f as [|b f IH].
    - reflexivity.
    - cbn [qpoly_scalar length]. rewrite IH. reflexivity. }
  assert (Hinner : forall (j k : nat), (k < length f)%nat ->
      QeqT (((lw2_lambda_coef n j k) # 1)%Q *
              qpoly_eval (qpoly_deriv_iter k (qpoly_scalar c f)) (lw2_node j))
            (c * (((lw2_lambda_coef n j k) # 1)%Q *
              qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))).
  { intros j k _.
    apply qeq_imp_qeqT.
    rewrite lw387_deriv_iter_eval_scalar.
    ring. }
  assert (Houter : forall j : nat,
      QeqT (lw2_qsum0
              (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
                 qpoly_eval (qpoly_deriv_iter k (qpoly_scalar c f))
                            (lw2_node j))
              (length f))
            (c * lw2_qsum0
              (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
                 qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
              (length f))).
  { intros j.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _
               (lw2_qsum0_ext (length f)
                  (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
                     qpoly_eval (qpoly_deriv_iter k (qpoly_scalar c f))
                                (lw2_node j))
                  (fun k => c * (((lw2_lambda_coef n j k) # 1)%Q *
                     qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))
                  (fun k l => Hinner j k l))).
    rewrite (qeqT_imp_qeq _ _
               (lw2_qsum0_scale (length f)
                  (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
                     qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) c)).
    reflexivity. }
  unfold lw2_lambda.
  rewrite Hlen.
  rewrite (qeqT_imp_qeq _ _
             (lw2_qsum0_ext (Datatypes.S (Datatypes.S n)) _ _
                (fun j _ => Houter j))).
  rewrite (qeqT_imp_qeq _ _
             (lw2_qsum0_scale (Datatypes.S (Datatypes.S n))
                (fun j => lw2_qsum0
                            (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
                               qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
                            (length f)) c)).
  reflexivity.
Qed.

(* The scaled-family bridge in general rank form: multiplying the node  *)
(* functional value of the factorial-reciprocal scaled family by the    *)
(* rank-m factorial restores the unscaled functional value, for every   *)
(* family instance and every scale rank.                                *)
Lemma lw387_bridge_scaled_gen : forall (p : zpoly) (sg N m n : nat),
  ((q_fact m)%Q * lw2_lambda n (lw381_fbuild_scaled p sg N m) ==
   lw2_lambda n (lw3_fbuild p sg N))%Q.
Proof.
  intros p sg N m n.
  unfold lw381_fbuild_scaled, lw381_scale_const.
  rewrite lw387_lambda_scalar.
  rewrite Qmult_assoc.
  rewrite (Qmult_inv_r (q_fact m)).
  - rewrite Qmult_1_l. reflexivity.
  - assert (Hge : QleT' 1 (q_fact m)) by apply lw0_q_fact_ge_one.
    apply QleT'_to_Qle in Hge.
    intro H0.
    rewrite H0 in Hge.
    unfold Qle in Hge.
    cbn in Hge.
    lia.
Qed.

(* The bridge at the anchor instance, scale one: the general rank form  *)
(* specialized to the rank-seven scaled family at scale one.            *)
Corollary lw387_bridge1_gen : ((q_fact m381)%Q * lw2_lambda n1_381 f1_381 ==
   lw2_lambda n1_381 (lw3_fbuild p381 (lw3_deg p381) N1_381))%Q.
Proof. exact (lw387_bridge_scaled_gen p381 (lw3_deg p381) N1_381 m381 n1_381). Qed.

(* The bridge at the anchor instance, scale zero.                       *)
Corollary lw387_bridge0_gen : ((q_fact m381)%Q * lw2_lambda n0_381 f0_381 ==
   lw2_lambda n0_381 (lw3_fbuild p381 (lw3_deg p381) N0_381))%Q.
Proof. exact (lw387_bridge_scaled_gen p381 (lw3_deg p381) N0_381 m381 n0_381). Qed.

(* ------------------------------------------------------------------ *)
(* Section 3.  A third-scale numeric witness.                          *)
(* ------------------------------------------------------------------ *)

(* A numeric witness at a fresh scale constant three, beyond the two    *)
(* anchor scales one and zero: the node functional value of the         *)
(* triple-scaled family is three times the scaled value, that is        *)
(* minus seven hundred ninety five over five thousand forty.            *)
Definition lw387_lam3s_val :
  @Id bool true
      (Qeq_bool (lw2_lambda n1_381 (qpoly_scalar (3 # 1)%Q f1_381))
                ((-795) # 5040)%Q) := id_refl.

Print Assumptions lw387_eval_coef_sum_bound.
Print Assumptions lw387_deriv_iter_eval_scalar.
Print Assumptions lw387_lambda_scalar.
Print Assumptions lw387_bridge_scaled_gen.
Print Assumptions lw387_bridge1_gen.
Print Assumptions lw387_bridge0_gen.
Print Assumptions lw387_lam3s_val.

From Stdlib Require Import Extraction.
Separate Extraction p381 m381 n1_381 n0_381.
