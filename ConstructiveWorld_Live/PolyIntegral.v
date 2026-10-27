(* ConstructiveWorld-Set — constructive integration of polynomials on [0,1]. *)

(** * PolyIntegral: constructive definite integrals of rational polynomials.

    Mission. The term-by-term definite integral [pint_integral] of a
    coefficient-list polynomial (head = constant term) with the anchor
    [pint_integral_pow_poly] (the integral of [x^k] equals [1/(k+1)]),
    evaluation agreement [pint_eval_pow_poly] with the [q_pow] engine,
    linearity [pint_integral_scale] / [pint_integral_add], and
    coefficientwise monotonicity [pint_integral_nonneg] /
    [pint_integral_mono].  [Q] division is total, so no well-definedness
    premise is needed; linearity states equal lengths explicitly, since
    under the tail-concatenation [pint_add] the unequal-length statement
    would be false.

    Dependencies. Stdlib [QArith.QArith], [QArith.Qabs], [Lists.List],
    [Arith.Arith], [ZArith.ZArith], [Lia]; requires [S01_BaseRing],
    [S02_CauchyComplete], [S03_QExp] of this development.

    References. ConstructiveWorld-Main ConstructiveWorld_Live/PolyIntegral.v,
    whose statement names are carried over here verbatim (statement-face
    Set-carrier completion).

    Constructivity. Main theorems are [QeqT]/[QleT'] Set-carrier statements;
    [Qle]/[Qeq] appear only inside proofs; all statements are Qed-closed
    with no admissions; [Obj.magic] = 0 and a [coqchk] run reports a closed
    global context.

    Build. [rocq c -native-compiler no -q -Q . "" PolyIntegral.v] compiles
    cleanly (exit 0); artifact magic [436f7121 00015ff4]. *)

From Stdlib Require Import Extraction.
From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Arith.Arith
               ZArith.ZArith Lia.
Import ListNotations.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.

(* ================ Section A. Definitions (coefficients in [Q], head = constant term) ================ *)

(* Evaluation by Horner recurrence:
   [pint_eval p x = a_0 + x * (a_1 + x * (...))] = [sum_k a_k * x^k]. *)
Fixpoint pint_eval (p : list Q) (x : Q) : Q :=
  match p with
  | [] => 0
  | a :: p' => a + x * pint_eval p' x
  end.

(* Monomial integral: the integral of [a * x^k] over [[0,1]] is [a/(k+1)];
   [k+1] is nonzero in [Q] and division is total. *)
Definition pint_monomial_int (a : Q) (k : nat) : Q :=
  a / (Z.of_nat (Datatypes.S k) # 1).

(* Definite integral with a starting offset [k] (for induction): the [i]-th
   coefficient is paired with the denominator [k+i+1]. *)
Fixpoint pint_integral_from (p : list Q) (k : nat) : Q :=
  match p with
  | [] => 0
  | a :: p' => pint_monomial_int a k + pint_integral_from p' (Datatypes.S k)
  end.

(* The main definite integral over [[0,1]]. *)
Definition pint_integral (p : list Q) : Q := pint_integral_from p 0.

(* Coefficient encoding of [x^k]: [k] zeros followed by one [1]. *)
Fixpoint pint_pow_poly (k : nat) : list Q :=
  match k with
  | 0%nat => 1 :: []
  | Datatypes.S m => 0 :: pint_pow_poly m
  end.

(* Termwise operations: scaling, addition (equal-length semantics), and the
   [i]-th coefficient ([0] out of range). *)
Fixpoint pint_scale (a : Q) (p : list Q) : list Q :=
  match p with
  | [] => []
  | c :: p' => a * c :: pint_scale a p'
  end.

Fixpoint pint_add (p q : list Q) : list Q :=
  match p with
  | [] => q
  | a :: p' =>
      match q with
      | [] => p
      | b :: q' => a + b :: pint_add p' q'
      end
  end.

Fixpoint pint_coeff (p : list Q) (i : nat) : Q :=
  match p with
  | [] => 0
  | a :: p' =>
      match i with
      | 0%nat => a
      | Datatypes.S i' => pint_coeff p' i'
      end
  end.

(* ================ Section B. Internal support at the [Q] layer ================ *)

(* Zero divided by anything is zero ([Qdiv] multiplies by [Qinv]; the zero
   product closes in one step). *)
Lemma pint_zero_div : forall d : Q, QeqT (0 / d) 0.
Proof. intros d. apply qeq_imp_qeqT. unfold Qdiv. apply Qmult_0_l. Qed.

(* Multiplication associates over division: [(a * c) / d == a * (c / d)]. *)
Lemma pint_div_mult_assoc : forall a c d : Q, QeqT (a * c / d) (a * (c / d)).
Proof. intros a c d. apply qeq_imp_qeqT. unfold Qdiv. ring. Qed.

(* Division distributes over addition: [(a + b) / d == a / d + b / d]. *)
Lemma pint_div_add_distr : forall a b d : Q, QeqT ((a + b) / d) (a / d + b / d).
Proof. intros a b d. apply qeq_imp_qeqT. unfold Qdiv. ring. Qed.

(* [1/(k+1)] is strictly positive: the inverse of [(n # 1)] with [n > 0]
   folds definitionally back to [(1 # n)]; the sign analysis of
   [Z.of_nat (S k)] splits on the [Nat2Z] bridge (the [Z0] branch is
   contradictory, the [Zneg] branch contradicts nonnegativity). *)
Lemma pint_invS_pos : forall k : nat, QltT 0 ((/ (Z.of_nat (Datatypes.S k) # 1))%Q).
Proof.
  intros k. apply Qlt_to_QltT.
  assert (Hnn : (0 <= Z.of_nat (Datatypes.S k))%Z) by apply Nat2Z.is_nonneg.
  assert (Hz : Z.of_nat (Datatypes.S k) <> 0%Z).
  { intros Hc. discriminate Hc. }
  destruct (Z.of_nat (Datatypes.S k)) as [| z | z] eqn:E.
  - exfalso. apply Hz. reflexivity.
  - unfold Qinv, Qlt. cbn [Qnum Qden Qmult]. lia.
  - exfalso. simpl in Hnn. lia.
Qed.

(* Monomial integral nonnegative: [0 <= a] implies [0 <= a/(k+1)]; the
   [QleT'] statement reduces to [Qle] only inside the proof. *)
Lemma pint_monomial_int_nonneg : forall (a : Q) (k : nat),
  QleT' 0 a -> QleT' 0 (pint_monomial_int a k).
Proof.
  intros a k Ha. apply Qle_to_QleT'.
  unfold pint_monomial_int, Qdiv.
  apply (Qle_trans 0 (0 * (1 / (Z.of_nat (Datatypes.S k) # 1)))
                    (a * (1 / (Z.of_nat (Datatypes.S k) # 1)))).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    apply Qeq_sym. apply Qmult_0_l.
  - apply (Qmult_le_compat_r 0 a).
    + exact (QleT'_to_Qle 0 a Ha).
    + apply Qlt_le_weak. apply QltT_to_Qlt. apply pint_invS_pos.
Qed.

(* ================ Section C. Evaluation agreement with the S03 power engine ================ *)

Theorem pint_eval_pow_poly : forall (k : nat) (x : Q),
  QeqT (pint_eval (pint_pow_poly k) x) (q_pow x k).
Proof.
  intros k. induction k as [| m IH]; intros x.
  - cbn [pint_eval pint_pow_poly q_pow].
    apply qeq_imp_qeqT. ring.
  - cbn [pint_eval pint_pow_poly q_pow].
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (IH x)).
    apply Qplus_0_l.
Qed.

(* ================ Section D. Correctness anchor: the integral of [x^k] ================ *)

(* Offset generalization: the integral with starting offset [k] of [x^m]
   equals [1/(k+m+1)].  Induction on [m]; the successor arithmetic on [nat]
   goes through the [lia]-proved shift, and the [Z.of_nat] atom is rewritten
   on both sides in step. *)
Lemma pint_integral_from_pow_poly : forall (m k : nat),
  QeqT (pint_integral_from (pint_pow_poly m) k)
    (1 / (Z.of_nat (Datatypes.S (k + m)) # 1)).
Proof.
  intros m k. apply qeq_imp_qeqT. revert k.
  induction m as [| m' IH]; intros k.
  - cbn [pint_integral_from pint_monomial_int pint_pow_poly].
    rewrite Nat.add_0_r. apply Qplus_0_r.
  - cbn [pint_integral_from pint_monomial_int pint_pow_poly].
    unfold pint_monomial_int. rewrite (fun d => qeqT_imp_qeq _ _ (pint_zero_div d)).
    rewrite (IH (Datatypes.S k)).
    assert (Hnat : Datatypes.S (k + Datatypes.S m')
                   = Datatypes.S (Datatypes.S k + m')) by lia.
    rewrite Hnat.
    apply Qplus_0_l.
Qed.

(* Correctness anchor (Set carrier): the integral of [x^k] equals [1/(k+1)]. *)
Theorem pint_integral_pow_poly : forall k : nat,
  QeqT (pint_integral (pint_pow_poly k)) (1 / (Z.of_nat (Datatypes.S k) # 1)).
Proof.
  intros k. apply qeq_imp_qeqT. unfold pint_integral.
  rewrite (qeqT_imp_qeq _ _ (pint_integral_from_pow_poly k 0)).
  rewrite Nat.add_0_l. reflexivity.
Qed.

(* Degenerate anchor: the integral of [1] equals [1]. *)
Theorem pint_integral_one : QeqT (pint_integral (pint_pow_poly 0)) (1 # 1).
Proof.
  apply qeq_imp_qeqT. unfold pint_integral.
  rewrite (qeqT_imp_qeq _ _ (pint_integral_from_pow_poly 0 0)).
  rewrite Nat.add_0_l. reflexivity.
Qed.

(* ================ Section E. Linearity (offset versions plus assembly) ================ *)

(* Scaling: the offset integral of [a * p] equals [a] times that of [p]. *)
Lemma pint_integral_from_scale : forall (a : Q) (p : list Q) (k : nat),
  QeqT (pint_integral_from (pint_scale a p) k) (a * pint_integral_from p k).
Proof.
  intros a p k. apply qeq_imp_qeqT. revert k.
  induction p as [| c p' IH]; intros k.
  - cbn [pint_integral_from pint_scale]. symmetry. apply Qmult_0_r.
  - cbn [pint_integral_from pint_monomial_int pint_scale].
    rewrite (qeqT_imp_qeq _ _ (pint_div_mult_assoc a c (Z.of_nat (Datatypes.S k) # 1))).
    rewrite (IH (Datatypes.S k)).
    unfold pint_monomial_int. ring.
Qed.

(* Addition (equal-length premise): the offset integral of [p + q] is the
   sum of the two offset integrals. *)
Lemma pint_integral_from_add : forall (p q : list Q) (k : nat),
  length p = length q ->
  QeqT (pint_integral_from (pint_add p q) k)
    (pint_integral_from p k + pint_integral_from q k).
Proof.
  intros p q k Hlen. apply qeq_imp_qeqT. revert q k Hlen.
  induction p as [| a p' IH]; intros q k Hlen.
  - destruct q as [| b q'].
    + cbn [pint_integral_from pint_add]. ring.
    + discriminate Hlen.
  - destruct q as [| b q'].
    + discriminate Hlen.
    + cbn [pint_integral_from pint_monomial_int pint_add].
      injection Hlen as Hlen'.
      rewrite (IH q' (Datatypes.S k) Hlen').
      rewrite (qeqT_imp_qeq _ _ (pint_div_add_distr a b (Z.of_nat (Datatypes.S k) # 1))).
      unfold pint_monomial_int. ring.
Qed.

(* Assembly at offset zero ([QeqT] carrier). *)
Theorem pint_integral_scale : forall (a : Q) (p : list Q),
  QeqT (pint_integral (pint_scale a p)) (a * pint_integral p).
Proof.
  intros a p.
  apply qeq_imp_qeqT.
  unfold pint_integral.
  exact (qeqT_imp_qeq _ _ (pint_integral_from_scale a p 0)).
Qed.

Theorem pint_integral_add : forall p q : list Q,
  length p = length q ->
  QeqT (pint_integral (pint_add p q)) (pint_integral p + pint_integral q).
Proof.
  intros p q Hlen.
  apply qeq_imp_qeqT.
  unfold pint_integral.
  exact (qeqT_imp_qeq _ _ (pint_integral_from_add p q 0 Hlen)).
Qed.

(* ================ Section F. Monotonicity companions (coefficientwise) ================ *)

(* Coefficientwise nonnegativity implies a nonnegative offset integral
   ([Qplus_le_compat] with the monomial branch and the induction branch;
   the coefficient index shift lines up definitionally with the [S] branch
   of [pint_coeff]). *)
Lemma pint_integral_from_nonneg : forall (p : list Q) (k : nat),
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  QleT' 0 (pint_integral_from p k).
Proof.
  intros p. induction p as [| a p' IH]; intros k Hcoeff.
  - reflexivity.
  - cbn [pint_integral_from].
    apply Qle_to_QleT'.
    apply (Qplus_le_compat 0 (pint_monomial_int a k)
                           0 (pint_integral_from p' (Datatypes.S k))).
    + apply QleT'_to_Qle. apply pint_monomial_int_nonneg.
      specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
    + apply QleT'_to_Qle. apply IH.
      intros i. specialize (Hcoeff (Datatypes.S i)).
      cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* Coefficientwise order (equal lengths) implies the offset integral order:
   [Qmult_le_compat_r] on both branches (the strict positivity of the right
   factor [1/(k+1)] comes from [pint_invS_pos]) plus the induction branch. *)
Lemma pint_integral_from_mono : forall (p q : list Q) (k : nat),
  length p = length q ->
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  QleT' (pint_integral_from p k) (pint_integral_from q k).
Proof.
  intros p. induction p as [| a p' IH]; intros q k Hlen Hcoeff.
  - destruct q as [| b q'].
    + reflexivity.
    + discriminate Hlen.
  - destruct q as [| b q'].
    + discriminate Hlen.
    + cbn [pint_integral_from].
      injection Hlen as Hlen'.
      apply Qle_to_QleT'.
      apply Qplus_le_compat.
      * unfold pint_monomial_int, Qdiv.
        apply (Qmult_le_compat_r a b).
        -- apply QleT'_to_Qle.
           specialize (Hcoeff 0%nat). cbn [pint_coeff] in Hcoeff. exact Hcoeff.
        -- apply Qlt_le_weak. apply QltT_to_Qlt. apply pint_invS_pos.
      * apply QleT'_to_Qle. apply IH.
        -- exact Hlen'.
        -- intros i. specialize (Hcoeff (Datatypes.S i)).
           cbn [pint_coeff] in Hcoeff. exact Hcoeff.
Qed.

(* Assembly at offset zero ([QleT'] carrier). *)
Theorem pint_integral_nonneg : forall p : list Q,
  (forall i : nat, QleT' 0 (pint_coeff p i)) ->
  QleT' 0 (pint_integral p).
Proof.
  intros p H.
  unfold pint_integral.
  exact (pint_integral_from_nonneg p 0 H).
Qed.


Theorem pint_integral_mono : forall p q : list Q,
  length p = length q ->
  (forall i : nat, QleT' (pint_coeff p i) (pint_coeff q i)) ->
  QleT' (pint_integral p) (pint_integral q).
Proof.
  intros p q Hlen Hcoeff.
  unfold pint_integral.
  exact (pint_integral_from_mono p q 0 Hlen Hcoeff).
Qed.


(* ================ Assumption audit ================ *)

Print Assumptions pint_integral_pow_poly.
Print Assumptions pint_integral_one.
Print Assumptions pint_eval_pow_poly.
Print Assumptions pint_integral_scale.
Print Assumptions pint_integral_add.
Print Assumptions pint_integral_nonneg.
Print Assumptions pint_integral_mono.
