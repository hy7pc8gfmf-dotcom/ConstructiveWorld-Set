(* ============================================================
   piu_zz_gauss_pair
   Mission.
     Algebraic carrier a + b*i (a b : Q) for the Gauss-number
     bookkeeping in the discrete kernel of the piu ZZ integral
     family, where the partial-fraction coefficients of
     R(x) = 5 x^{2n} (x^4 + 6 x^2 + 25)^{2n} /
     ((5+x)^{3n+1} (5-x)^{3n+1}) arise from products of (2+/-i)
     powers and from (1+i)^2 = 2i, (1-i)^2 = -2i, |1+/-i|^2 = 2,
     |2+/-i|^2 = 5.  Key statement: |(2+i)^m|^2 = 5^m, mirrored
     for (2-i)^m: the atomic growth fact behind the bounds.
   Dependencies.
     Stdlib only: QArith, ZArith, Qring (ring tactic over Q), Lia.
     No in-tree requires; the tree canonical faces (QltT, QleT',
     QeqT, NatLe, Id) are not consumed by this file.
   References.
     Anchor: complex multiplication on Q^2; norm (a,b) = a^2+b^2;
     the (1+/-i) chain and the (2+/-i)^m power facts of the piu ZZ family.
   Constructivity.
     Every named statement is carried in Set.  The equality
     predicates qeqT/gzeq are Set-valued inductives; propositional
     Q-equalities occur only as constructor arguments and inside
     proof terms, so the data layer (all eight operations,
     transparent) extracts to computable OCaml.  gz_inv is total;
     on the zero pair it returns zero rather than a true inverse.
   Build.
     rocq c -native-compiler no -q -Q . "" piu_zz_gauss_pair.v
     (Rocq 9.1 toolchain, thermal-guard wrapped; world dependency
     closure is empty for this Stdlib-only file).
   ============================================================ *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Qring.
From Stdlib Require Import Lia.

(* ------------------------------------------------------------------ *)
(* Carrier and operations                                              *)
(* ------------------------------------------------------------------ *)

Definition gz : Set := (Q * Q)%type.

Definition gz_add (z w : gz) : gz :=
  match z, w with
  | (a, b), (c, d) => (a + c, b + d)%Q
  end.

Definition gz_mul (z w : gz) : gz :=
  match z, w with
  | (a, b), (c, d) => (a * c - b * d, a * d + b * c)%Q
  end.

Definition gz_conj (z : gz) : gz :=
  match z with
  | (a, b) => (a, - b)%Q
  end.

Definition gz_inv (z : gz) : gz :=
  match z with
  | (a, b) =>
      let n := (a * a + b * b)%Q in
      ((a / n)%Q, ((- b) / n)%Q)
  end.

Definition gz_norm (z : gz) : Q :=
  match z with
  | (a, b) => (a * a + b * b)%Q
  end.

Fixpoint gz_pow (z : gz) (m : nat) : gz :=
  match m with
  | O => (1, 0)%Q
  | S m' => gz_mul z (gz_pow z m')
  end.

Definition gz_Re (z : gz) : Q :=
  match z with
  | (a, b) => a
  end.

Definition gz_Im (z : gz) : Q :=
  match z with
  | (a, b) => b
  end.

(* ------------------------------------------------------------------ *)
(* Set-carried equality on Q and on gz                                 *)
(* ------------------------------------------------------------------ *)

Inductive qeqT : Q -> Q -> Set :=
| qeqT_intro : forall a b : Q, (a == b)%Q -> qeqT a b.

Inductive gzeq : gz -> gz -> Set :=
| gzeq_intro : forall z w : gz,
    qeqT (gz_Re z) (gz_Re w) -> qeqT (gz_Im z) (gz_Im w) -> gzeq z w.

Definition qeqT_refl (a : Q) : qeqT a a := qeqT_intro a a (Qeq_refl a).

Lemma qeqT_sym : forall a b : Q, qeqT a b -> qeqT b a.
Proof.
  intros a b h. destruct h as [a0 b0 e]. apply qeqT_intro.
  apply Qeq_sym. exact e.
Qed.

Lemma qeqT_trans : forall a b c : Q, qeqT a b -> qeqT b c -> qeqT a c.
Proof.
  intros a b c h1 h2. destruct h1 as [a0 b0 e1]. destruct h2 as [b1 c0 e2].
  apply qeqT_intro. eapply Qeq_trans. exact e1. exact e2.
Qed.

Lemma qeqT_mul_r : forall a b c : Q, qeqT a b -> qeqT (a * c) (b * c).
Proof.
  intros a b c h. destruct h as [a0 b0 e]. apply qeqT_intro.
  rewrite e. apply Qeq_refl.
Qed.

Lemma qeqT_mul_l : forall a b c : Q, qeqT a b -> qeqT (c * a) (c * b).
Proof.
  intros a b c h. destruct h as [a0 b0 e]. apply qeqT_intro.
  rewrite e. apply Qeq_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* The (1+/-i) chain: (1+i)^2 = 2i, (1-i)^2 = -2i, |1+/-i|^2 = 2           *)
(* ------------------------------------------------------------------ *)

Lemma gz_i_sq : gzeq (gz_mul (1, 1) (1, 1)) (0, 2).
Proof. apply gzeq_intro; vm_compute; apply qeqT_refl. Qed.

Lemma gz_j_sq : gzeq (gz_mul (1, -1) (1, -1)) (0, -2).
Proof. apply gzeq_intro; vm_compute; apply qeqT_refl. Qed.

Lemma gz_norm_ii : qeqT (gz_norm (1, 1)) (2 # 1)%Q.
Proof. vm_compute. apply qeqT_refl. Qed.

Lemma gz_norm_ij : qeqT (gz_norm (1, -1)) (2 # 1)%Q.
Proof. vm_compute. apply qeqT_refl. Qed.

(* ------------------------------------------------------------------ *)
(* Multiplicativity of the norm and the (2+/-i)^m power facts            *)
(* ------------------------------------------------------------------ *)

Lemma gz_norm_mul : forall z w : gz,
  qeqT (gz_norm (gz_mul z w)) ((gz_norm z) * (gz_norm w))%Q.
Proof.
  intros [a b] [c d]. cbn [gz_mul gz_norm]. apply qeqT_intro. ring.
Qed.

Lemma gz_norm_pow_step : forall (z : gz) (m : nat),
  qeqT (gz_norm (gz_pow z (S m))) ((gz_norm z) * gz_norm (gz_pow z m))%Q.
Proof. intros z m. cbn [gz_pow]. apply gz_norm_mul. Qed.

(* Growth constants: |2+/-i|^2 = 5. *)
Lemma gz_norm_2i : qeqT (gz_norm (2, 1)) (5 # 1)%Q.
Proof. vm_compute. apply qeqT_refl. Qed.

Lemma gz_norm_2mi : qeqT (gz_norm (2, -1)) (5 # 1)%Q.
Proof. vm_compute. apply qeqT_refl. Qed.

(* The Q-level step 5^{S m} = 5 * 5^m, injected into Q. *)
Lemma gz_q5pow_step : forall m : nat,
  qeqT (((Z.of_nat (5 ^ S m)) # 1)%Q) (((5 # 1) * ((Z.of_nat (5 ^ m)) # 1))%Q).
Proof.
  intros m. rewrite Nat.pow_succ_r'. rewrite Nat2Z.inj_mul.
  apply qeqT_intro. vm_compute. reflexivity.
Qed.

Theorem gz_norm_pow_2i : forall m : nat,
  qeqT (gz_norm (gz_pow (2, 1) m)) (((Z.of_nat (5 ^ m)) # 1)%Q).
Proof.
  induction m as [| m IH].
  - vm_compute. apply qeqT_refl.
  - eapply qeqT_trans.
    + apply gz_norm_pow_step.
    + eapply qeqT_trans.
      * apply qeqT_mul_r. exact gz_norm_2i.
      * eapply qeqT_trans.
        -- apply qeqT_mul_l. exact IH.
        -- apply qeqT_sym. exact (gz_q5pow_step m).
Qed.

Theorem gz_norm_pow_2mi : forall m : nat,
  qeqT (gz_norm (gz_pow (2, -1) m)) (((Z.of_nat (5 ^ m)) # 1)%Q).
Proof.
  induction m as [| m IH].
  - vm_compute. apply qeqT_refl.
  - eapply qeqT_trans.
    + apply gz_norm_pow_step.
    + eapply qeqT_trans.
      * apply qeqT_mul_r. exact gz_norm_2mi.
      * eapply qeqT_trans.
        -- apply qeqT_mul_l. exact IH.
        -- apply qeqT_sym. exact (gz_q5pow_step m).
Qed.

(* ------------------------------------------------------------------ *)
(* Real/imaginary exits and distributivity                             *)
(* ------------------------------------------------------------------ *)

Lemma gz_Re_mul : forall z w : gz,
  qeqT (gz_Re (gz_mul z w)) ((gz_Re z * gz_Re w - gz_Im z * gz_Im w)%Q).
Proof. intros [a b] [c d]. cbn [gz_mul gz_Re gz_Im]. apply qeqT_refl. Qed.

Lemma gz_Im_mul : forall z w : gz,
  qeqT (gz_Im (gz_mul z w)) ((gz_Re z * gz_Im w + gz_Im z * gz_Re w)%Q).
Proof. intros [a b] [c d]. cbn [gz_mul gz_Re gz_Im]. apply qeqT_refl. Qed.

Lemma gz_mul_add_distr_r : forall z w u : gz,
  gzeq (gz_mul z (gz_add w u)) (gz_add (gz_mul z w) (gz_mul z u)).
Proof.
  intros [a b] [c d] [e f].
  apply gzeq_intro; cbn [gz_mul gz_add gz_Re gz_Im]; apply qeqT_intro; ring.
Qed.

Lemma gz_mul_add_distr_l : forall z w u : gz,
  gzeq (gz_mul (gz_add z w) u) (gz_add (gz_mul z u) (gz_mul w u)).
Proof.
  intros [a b] [c d] [e f].
  apply gzeq_intro; cbn [gz_mul gz_add gz_Re gz_Im]; apply qeqT_intro; ring.
Qed.

(* Base cases of the power recursion. *)
Lemma gz_pow_unit : forall z : gz, gzeq (gz_pow z 0) (1, 0).
Proof. intros z. apply gzeq_intro; vm_compute; apply qeqT_refl. Qed.

Lemma gz_pow_1 : forall z : gz, gzeq (gz_pow z 1) z.
Proof.
  intros [a b]. cbn [gz_pow]. apply gzeq_intro; cbn [gz_mul gz_Re gz_Im];
    apply qeqT_intro; ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Numeric witnesses (vm_compute-checked)                              *)
(* ------------------------------------------------------------------ *)

Lemma gz_sample_pow2 : gzeq (gz_pow (2, 1) 2) (3, 4).
Proof. apply gzeq_intro; vm_compute; apply qeqT_refl. Qed.

Lemma gz_sample_pow3_norm : qeqT (gz_norm (gz_pow (2, 1) 3)) (125 # 1)%Q.
Proof. vm_compute. apply qeqT_refl. Qed.

Lemma gz_sample_pow3j_norm : qeqT (gz_norm (gz_pow (2, -1) 3)) (125 # 1)%Q.
Proof. vm_compute. apply qeqT_refl. Qed.

Print Assumptions gz_i_sq.
Print Assumptions gz_j_sq.
Print Assumptions gz_norm_ii.
Print Assumptions gz_norm_ij.
Print Assumptions qeqT_sym.
Print Assumptions qeqT_trans.
Print Assumptions qeqT_mul_r.
Print Assumptions qeqT_mul_l.
Print Assumptions gz_norm_mul.
Print Assumptions gz_norm_pow_step.
Print Assumptions gz_norm_2i.
Print Assumptions gz_norm_2mi.
Print Assumptions gz_q5pow_step.
Print Assumptions gz_norm_pow_2i.
Print Assumptions gz_norm_pow_2mi.
Print Assumptions gz_Re_mul.
Print Assumptions gz_Im_mul.
Print Assumptions gz_mul_add_distr_r.
Print Assumptions gz_mul_add_distr_l.
Print Assumptions gz_pow_unit.
Print Assumptions gz_pow_1.
Print Assumptions gz_sample_pow2.
Print Assumptions gz_sample_pow3_norm.
Print Assumptions gz_sample_pow3j_norm.
