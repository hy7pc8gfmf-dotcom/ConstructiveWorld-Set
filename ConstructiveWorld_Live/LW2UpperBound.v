(* ConstructiveWorld-Set -- the explicit rational upper suppression of the Hermite endpoint functional. *)
(** * LW2UpperBound: explicit rational upper suppression of the Hermite
    endpoint functional.

    Mission.  For the node functional
      lambda n f = sum_{j=0}^{n+1} sum_{k<|f|} c_{jk} · f^{(k)}(j)
      (c_{jk} ∈ {−1,0,1}, defined in LW2Hermite), an explicit rational
      constant upper bound: under per-node suppression of the derivative
      values on the node faces {0,...,n+1}, |lambda n f| <= (node count ×
      length) · E; with the pi-bound constant 10/3 as the uniform E and the
      factorial suppression (10/3)^N <= N! capping, |lambda n f| <= c_n,
      plus the (c_n # 1) integralized corollary.

    Dependencies.  [LW0QPoly] (QPoly, eval/deriv_iter laws); [LW2Hermite]
      ([lw2_lambda], [lw2_lambda_coef], [lw2_node], [lw2_qsum0]);
      [LW0FactGrowth] (lw0_q_of_nat family, [lw0_pi_bound_dominated_even]);
      [S02_CauchyComplete] (QleT' and bridges); [S03_QExp]
      ([q_fact]/[q_pow]); Stdlib [QArith]/[Qabs], [Arith], [Lia].

    References.  Hermite 1873 (C. R. Acad. Sci. Paris 77), the upper-bound
      half; pi < 10/3 from S10_KVQuantTrig's Leibniz two-bank estimate;
      the same-name ConstructiveWorld-Main baseline.

    Constructivity.  All statements Set-carried (uniformly QleT' premises
      and conclusions, zero Prop premises, zero existential arguments);
      generic recursion with [lw2u_qsum0_abs_le] as the core; axiom-free,
      no classical logic; Obj.magic count zero after Separate Extraction.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" LW2UpperBound.v] (direct call, cpu_guard wrapped). *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith Lia.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW0FactGrowth.
Require Import LW2Hermite.

(* ------------------------------------------------------------------ *)
(* Section 1.  small auxiliary equations for the rational image of natural   *)
(* numbers and the QleT' equality bridges.                                   *)
(* ------------------------------------------------------------------ *)

(* The Qmake multiplication decomposition: the numerator of a product with a
   common denominator = the product of the numerators. *)
Lemma lw2u_make_mul : forall (a b : Z) (d e : positive),
  QeqT ((a # d) * (b # e)) ((a * b) # (d * e))%Q.
Proof.
  intros a b d e. apply qeq_imp_qeqT. unfold Qeq, Qmult. cbn [Qnum Qden]. lia.
Qed.

(* The successor decomposition of the rational image: q(n+1) = q(n) + 1. *)
Lemma lw2u_q_of_nat_succ : forall m : nat,
  QeqT (lw0_q_of_nat (Datatypes.S m)) (lw0_q_of_nat m + (1 # 1)%Q).
Proof.
  intro m. apply qeq_imp_qeqT. unfold lw0_q_of_nat, Qeq, Qplus. cbn [Qnum Qden].
  assert (Hz : Z.of_nat (Datatypes.S m) = (Z.of_nat m + 1)%Z) by lia.
  rewrite Hz. lia.
Qed.

(* The multiplicative homomorphism of the rational image: q(a·b) = q(a)·q(b). *)
Lemma lw2u_q_of_nat_mul : forall a b : nat,
  QeqT (lw0_q_of_nat (a * b)) (lw0_q_of_nat a * lw0_q_of_nat b).
Proof.
  intros a b. apply qeq_imp_qeqT. unfold lw0_q_of_nat, Qeq, Qmult. cbn [Qnum Qden].
  assert (Hz : Z.of_nat (a * b) = (Z.of_nat a * Z.of_nat b)%Z) by lia.
  rewrite Hz. lia.
Qed.

(* The QleT' right equality bridge: x ≤T' y and y == z imply x ≤T' z. *)
Lemma lw2u_qleT'_eq_r : forall x y z : Q,
  QleT' x y -> y == z -> QleT' x z.
Proof.
  intros x y z H He. apply (qleT'_trans x y z H).
  apply Qle_to_QleT'. rewrite He. apply (Qle_refl z).
Qed.

(* The QleT' left equality bridge: x == y and y ≤T' z imply x ≤T' z. *)
Lemma lw2u_qleT'_eq_l : forall x y z : Q,
  QleT' y z -> x == y -> QleT' x z.
Proof.
  intros x y z H He. apply (qleT'_trans x y z).
  - apply Qle_to_QleT'. rewrite <- He. apply (Qle_refl x).
  - exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 2.  uniform-bound suppression of the generic sum (the core of the *)
(* generic recursion).  For the sum lw2_qsum0 g m = g 0 + ... + g (m-1), if  *)
(* every term has absolute value <= T, then |lw2_qsum0 g m| <= m · T.  The   *)
(* triangle inequality advances layer by layer; the counting is carried by   *)
(* the rational image.                                                       *)
(* ------------------------------------------------------------------ *)

Lemma lw2u_qsum0_abs_le : forall (m : nat) (g : nat -> Q) (T : Q),
  (forall j, Nat.lt j m -> QleT' (Qabs (g j)) T) ->
  QleT' (Qabs (lw2_qsum0 g m)) (lw0_q_of_nat m * T).
Proof.
  intros m. induction m as [| m IH]; intros g T H.
  - (* Base case: the empty sum is 0, |0| ≤ 0·T = 0. *)
    cbn [lw2_qsum0]. apply Qle_to_QleT'.
    assert (Hz : lw0_q_of_nat 0 * T == 0%Q).
    { unfold lw0_q_of_nat. cbn [Z.of_nat]. ring. }
    rewrite Hz. apply (Qle_refl 0%Q).
  - (* Induction step: |Σ_m + g m| ≤ |Σ_m| + |g m| ≤ m·T + T = (m+1)·T. *)
    cbn [lw2_qsum0].
    assert (Hprev : QleT' (Qabs (lw2_qsum0 g m)) (lw0_q_of_nat m * T)).
    { apply IH. intros j Hj. apply H. lia. }
    assert (Hlast : QleT' (Qabs (g m)) T) by (apply H; lia).
    assert (Htri : Qle (Qabs (lw2_qsum0 g m + g m))
                       (Qabs (lw2_qsum0 g m) + Qabs (g m)))
      by apply Qabs_triangle.
    assert (Hsplit : Qle (Qabs (lw2_qsum0 g m) + Qabs (g m))
                         (lw0_q_of_nat m * T + T)).
    { apply Qplus_le_compat;
        [ exact (QleT'_to_Qle _ _ Hprev) | exact (QleT'_to_Qle _ _ Hlast) ]. }
    assert (Hstep : lw0_q_of_nat m * T + T == lw0_q_of_nat (Datatypes.S m) * T).
    { rewrite (qeqT_imp_qeq _ _ (lw2u_q_of_nat_succ m)). ring. }
    apply Qle_to_QleT'. rewrite <- Hstep.
    exact (Qle_trans _ (Qabs (lw2_qsum0 g m) + Qabs (g m)) _ Htri Hsplit).
Qed.

(* ------------------------------------------------------------------ *)
(* Section 3.  the absolute-value bound of the node coefficients.            *)
(* The coefficient table lw2_lambda_coef takes only the three values -1,0,1, *)
(* so its absolute value is <= 1.                                            *)
(* ------------------------------------------------------------------ *)

Lemma lw2u_coef_abs_le_one : forall (n j k : nat),
  QleT' (Qabs ((lw2_lambda_coef n j k) # 1)%Q) ((1 # 1)%Q).
Proof.
  intros n j k. apply Qle_to_QleT'. unfold Qabs, lw2_lambda_coef. cbn [Qnum Qden].
  destruct (Nat.eqb j 0); destruct (Nat.eqb j (Datatypes.S n));
    cbn [Z.abs]; unfold Qle; cbn [Qnum Qden]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 4.  single-node face suppression.                                 *)
(* Fixed node j: |Σ_{k<|f|} c_{jk} f^{(k)}(j)| <= |f| · E whenever every     *)
(* |f^{(k)}(j)| <= E.  Closed by the coefficient absolute value <= 1, the    *)
(* product absolute-value decomposition, and Section 2.                      *)
(* ------------------------------------------------------------------ *)

Lemma lw2u_node_term_abs_le : forall (n : nat) (f : QPoly) (j : nat) (E : Q),
  (forall k, Nat.lt k (length f) ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))) E) ->
  QleT' (Qabs (lw2_qsum0 (fun k =>
            ((lw2_lambda_coef n j k) # 1)%Q *
            qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
            (length f)))
        (lw0_q_of_nat (length f) * E).
Proof.
  intros n f j E H.
  apply (lw2u_qsum0_abs_le (length f)
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

(* ------------------------------------------------------------------ *)
(* Section 5.  the main suppression chain (per-node suppression premise ->   *)
(* explicit constant upper bound).                                           *)
(* If every |f^{(k)}(j)| <= E on the node faces j = 0,...,n+1, then          *)
(* |lambda n f| <= (n+2)·|f|·E -- the node count n+2 and the polynomial      *)
(* length |f| enter the bound explicitly.                                    *)
(* ------------------------------------------------------------------ *)

Theorem lw2_L_upper_nodes : forall (n : nat) (f : QPoly) (E : Q),
  (forall j k, Nat.le j (Datatypes.S n) -> Nat.lt k (length f) ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))) E) ->
  QleT' (Qabs (lw2_lambda n f))
        (lw0_q_of_nat (Datatypes.S (Datatypes.S n) * length f) * E).
Proof.
  intros n f E H. unfold lw2_lambda. cbv beta.
  apply (lw2u_qleT'_eq_r _
    (lw0_q_of_nat (Datatypes.S (Datatypes.S n)) *
     (lw0_q_of_nat (length f) * E))).
  - apply (lw2u_qsum0_abs_le (Datatypes.S (Datatypes.S n))
      (fun j => lw2_qsum0
        (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
                  qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
        (length f))
      (lw0_q_of_nat (length f) * E)).
    intros j Hj. apply (lw2u_node_term_abs_le n f j).
    intros k Hk. apply H; lia.
  - rewrite (qeqT_imp_qeq _ _
      (lw2u_q_of_nat_mul (Datatypes.S (Datatypes.S n)) (length f))). ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 6.  capping by the pi-bound constant: the main upper-bound piece. *)
(* Taking the uniform bound E = (10/3)^{22+2n} (10/3 is the rational upper   *)
(* bank constant of the S10 two-bank bound pi < 10/3), the factorial         *)
(* suppression (10/3)^N <= N! gives                                          *)
(*   |lambda n f| <= (n+2)·|f|·(22+2n)!  =: c_n.                             *)
(* c_n is an explicit Q constant function: it contains the node count n+2,   *)
(* the polynomial length |f|, and the endpoint of the pi-bound chain         *)
(* (22+2n)!; its power-factorial core is the suppression chain of the shape  *)
(* |L(f)| <= C^N·(N!).                                                       *)
(* ------------------------------------------------------------------ *)

Definition lw2u_c_n (n ell : nat) : Q :=
  lw0_q_of_nat (Datatypes.S (Datatypes.S n) * ell) * q_fact (22 + 2 * n)%nat.

Theorem lw2_L_upper_hermite : forall (n : nat) (f : QPoly),
  (forall j k, Nat.le j (Datatypes.S n) -> Nat.lt k (length f) ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))
           (q_pow (10 # 3) (22 + 2 * n)%nat)) ->
  QleT' (Qabs (lw2_lambda n f)) (lw2u_c_n n (length f)).
Proof.
  intros n f H.
  apply (qleT'_trans _
    (lw0_q_of_nat (Datatypes.S (Datatypes.S n) * length f) *
     q_pow (10 # 3) (22 + 2 * n)%nat)).
  - apply lw2_L_upper_nodes. exact H.
  - apply Qle_to_QleT'.
    rewrite (Qmult_comm (lw0_q_of_nat
              (Datatypes.S (Datatypes.S n) * length f))
              (q_pow (10 # 3) (22 + 2 * n)%nat)),
            (Qmult_comm (lw0_q_of_nat
              (Datatypes.S (Datatypes.S n) * length f))
              (q_fact (22 + 2 * n)%nat)).
    apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ (lw0_pi_bound_dominated_even n)).
    + exact (QleT'_to_Qle _ _
        (lw0_q_of_nat_nonneg (Datatypes.S (Datatypes.S n) * length f))).
Qed.

(* ------------------------------------------------------------------ *)
(* Section 7.  the (c_n # 1) shape corollary: the integralized constant.     *)
(* First establish the Q-image bridge for Z-layer powers: the q_pow of the   *)
(* Q image of an integer z equals the Q image of z^N; then cap, with the     *)
(* integralized enlargement 10 of the pi-bound constant (since               *)
(* (10/3)^N <= 10^N), into the Zmake shape                                   *)
(* |lambda n f| <= (rational image of (n+2)·|f| × 10^{22+2n}) # 1.           *)
(* ------------------------------------------------------------------ *)

(* The Z-power bridge with integral denominator 1: q_pow (z#1) N ==
   (z^{N} # 1).  A generic inductive structure. *)
Lemma lw2u_qpow_zmake : forall (z : Z) (N : nat),
  QeqT (q_pow (z # 1)%Q N) ((z ^ Z.of_nat N) # 1)%Q.
Proof.
  intros z. induction N as [| N IH].
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. cbn [q_pow]. rewrite (qeqT_imp_qeq _ _ IH).
    assert (Hz : Z.of_nat (Datatypes.S N) = (1 + Z.of_nat N)%Z) by lia.
    rewrite Hz. rewrite Z.pow_add_r by lia.
    rewrite (qeqT_imp_qeq _ _ (lw2u_make_mul _ _ _ _)).
    unfold Qeq. cbn [Qnum Qden].
    replace (1 * 1)%positive with 1%positive by reflexivity.
    rewrite Z.pow_1_r. lia.
Qed.

(* The main Zmake-shape corollary: the integralized constant of c_n =
   (the numerator of the rational image of node-count × length) ×
   10^{22+2n}, where 10 is the integralized enlargement of the pi-bound
   constant 10/3 (10/3 ≤ 10). *)
Theorem lw2_L_upper_hermite_zmake : forall (n : nat) (f : QPoly),
  (forall j k, Nat.le j (Datatypes.S n) -> Nat.lt k (length f) ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))
           (q_pow (10 # 3) (22 + 2 * n)%nat)) ->
  QleT' (Qabs (lw2_lambda n f))
        (((Z.of_nat (Datatypes.S (Datatypes.S n) * length f) *
           (10 ^ Z.of_nat (22 + 2 * n))) # 1)%Q).
Proof.
  intros n f H.
  assert (Hbase : QleT' (q_pow (10 # 3) (22 + 2 * n)%nat)
                        (q_pow (10 # 1) (22 + 2 * n)%nat)).
  { apply (lw0_q_pow_mono_base (10 # 3) (10 # 1) (22 + 2 * n)%nat).
    - vm_compute. reflexivity.
    - vm_compute. reflexivity. }
  assert (Hbridge : lw0_q_of_nat (Datatypes.S (Datatypes.S n) * length f) *
                    q_pow (10 # 1) (22 + 2 * n)%nat
                    == ((Z.of_nat (Datatypes.S (Datatypes.S n) * length f) *
                         (10 ^ Z.of_nat (22 + 2 * n))) # 1)%Q).
  { rewrite (qeqT_imp_qeq _ _ (lw2u_qpow_zmake 10%Z (22 + 2 * n)%nat)),
            (qeqT_imp_qeq _ _
              (lw2u_q_of_nat_mul (Datatypes.S (Datatypes.S n)) (length f))).
    unfold lw0_q_of_nat.
    rewrite !(qeqT_imp_qeq _ _ (lw2u_make_mul _ _ _ _)).
    unfold Qeq. cbn [Qnum Qden].
    replace (1 * 1)%positive with 1%positive by reflexivity.
    assert (Hzm : Z.of_nat (Datatypes.S (Datatypes.S n) * length f) =
                  (Z.of_nat (Datatypes.S (Datatypes.S n)) *
                   Z.of_nat (length f))%Z) by lia.
    rewrite Hzm. lia. }
  apply (lw2u_qleT'_eq_r _
    (lw0_q_of_nat (Datatypes.S (Datatypes.S n) * length f) *
     q_pow (10 # 1) (22 + 2 * n)%nat)).
  - apply (qleT'_trans _
      (lw0_q_of_nat (Datatypes.S (Datatypes.S n) * length f) *
       q_pow (10 # 3) (22 + 2 * n)%nat)).
    + apply lw2_L_upper_nodes. exact H.
    + apply Qle_to_QleT'.
      rewrite (Qmult_comm (lw0_q_of_nat
                (Datatypes.S (Datatypes.S n) * length f))
                (q_pow (10 # 3) (22 + 2 * n)%nat)),
              (Qmult_comm (lw0_q_of_nat
                (Datatypes.S (Datatypes.S n) * length f))
                (q_pow (10 # 1) (22 + 2 * n)%nat)).
      apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ Hbase).
      * exact (QleT'_to_Qle _ _
          (lw0_q_of_nat_nonneg (Datatypes.S (Datatypes.S n) * length f))).
  - exact Hbridge.
Qed.

(* ========================================================================= *)
(* Extraction check and axiom-face self-audit: the extraction products contain zero Obj.magic, and every statement is Closed. *)
(* ========================================================================= *)

From Stdlib Require Import Extraction.
Separate Extraction lw2_L_upper_nodes lw2_L_upper_hermite lw2_L_upper_hermite_zmake.
Print Assumptions lw2_L_upper_nodes.
Print Assumptions lw2_L_upper_hermite.
Print Assumptions lw2_L_upper_hermite_zmake.
