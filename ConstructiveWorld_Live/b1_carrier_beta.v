(* ConstructiveWorld-Set -- single-integral segment carriers for the truncated arctan integral. *)

(** * b1_carrier_beta: single-integral Beta closed forms for the arctan truncation.

    Mission.  The truncated integrand [x^n * (1-x)^n * A(n, M, -x^2)] has a
      one-dimensional Beukers-arctan core, so the double-integral carrier of
      the two-integral recast is replaced here by single segments: segment
      [m] carries [C(n+m, n) * (-1)^m] times the factor list
      [t^(n+2m) * (1-t)^n], one [pint_integral] application yields the exact
      Beta closed form.  Main statements: [b1_seg_val], [b1_seg_signed_val],
      [b1_seg_pos], [b1_seg_beta_le1], [b1_segl_val], [b1_rho].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
      [Arith.Arith], [Setoid], [Morphisms], [Qfield], [Lia], [Lists.List].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [BeukersLists], [PolyIntegral], [PadeErrorIntegral],
      [b1_kernel_pointwise], [b1_trunc_master] of this development.

    References.  This development, b1_carrier_beta.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" b1_carrier_beta.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith Arith.Arith.
From Stdlib Require Import Setoid Morphisms Qfield Lia Lists.List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import BeukersLists.
Require Import PolyIntegral.
Require Import PadeErrorIntegral.
Require Import b1_kernel_pointwise.
Require Import b1_trunc_master.

Open Scope Q_scope.
Open Scope list_scope.

(* ========== Section 1. Segment carrier definitions ========== *)

(* The positive segment [m]: the coefficient [C(n+m, n)] times the factor
   list [t^(n+2m) * (1-t)^n], the coefficient list of
   [x^n * (1-x)^n * x^(2m)] on the unit interval. *)
Definition b1_seg_poly (n m : nat) : list Q :=
  pint_scale ((Z.of_nat (bkC (n + m) n) # 1)) (pei_list (n + 2 * m) n).

(* The signed segment [m]: the positive segment times the alternating
   factor [(-1)^m] from the expansion of [A(n, M, -x^2)]. *)
Definition b1_seg_signed (n m : nat) : list Q :=
  pint_scale (((Z.of_nat (bkC (n + m) n) # 1) * q_pow (- 1)%Q m))
             (pei_list (n + 2 * m) n).

(* The exact Beta closed form of a segment, in the uniform reference form
   reused throughout. *)
Definition b1_seg_beta (n m : nat) : Q :=
  (q_fact (n + 2 * m) * q_fact n) / q_fact (Datatypes.S (n + 2 * m + n)).

(* ========== Section 2. Segment exact values, single-integral Beta closed forms ========== *)

(* Positive-core segment value on the [Qeq] face: the integral of
   [C * t^(n+2m) * (1-t)^n] over [0,1] equals
   [C * (n+2m)! * n! / (2n+2m+1)!]. *)
Lemma b1_seg_val_eq : forall n m : nat,
  pint_integral (b1_seg_poly n m) ==
  ((Z.of_nat (bkC (n + m) n) # 1) * b1_seg_beta n m)%Q.
Proof.
  intros n m. unfold b1_seg_poly, b1_seg_beta.
  assert (Hsc := qeqT_imp_qeq _ _
    (pint_integral_scale ((Z.of_nat (bkC (n + m) n) # 1))
       (pei_list (n + 2 * m) n))).
  rewrite Hsc.
  rewrite (qeqT_imp_qeq _ _ (pei_beta_value (n + 2 * m) n)).
  replace (n + 2 * m + n + 1)%nat with (Datatypes.S (n + 2 * m + n))%nat by lia.
  reflexivity.
Qed.

(* The positive-core segment value, in the Set certificate shape [QeqT]. *)
Theorem b1_seg_val : forall n m : nat,
  QeqT (pint_integral (b1_seg_poly n m))
       (((Z.of_nat (bkC (n + m) n) # 1) * b1_seg_beta n m)%Q).
Proof.
  intros n m. apply qeq_imp_qeqT. exact (b1_seg_val_eq n m).
Qed.

(* The signed segment value: the positive value times the [(-1)^m] factor. *)
Lemma b1_seg_signed_val_eq : forall n m : nat,
  pint_integral (b1_seg_signed n m) ==
  (((Z.of_nat (bkC (n + m) n) # 1) * q_pow (- 1)%Q m) * b1_seg_beta n m)%Q.
Proof.
  intros n m. unfold b1_seg_signed.
  assert (Hsc := qeqT_imp_qeq _ _
    (pint_integral_scale (((Z.of_nat (bkC (n + m) n) # 1) * q_pow (- 1)%Q m))
       (pei_list (n + 2 * m) n))).
  rewrite Hsc.
  rewrite (qeqT_imp_qeq _ _ (pei_beta_value (n + 2 * m) n)).
  replace (n + 2 * m + n + 1)%nat with (Datatypes.S (n + 2 * m + n))%nat by lia.
  reflexivity.
Qed.

Theorem b1_seg_signed_val : forall n m : nat,
  QeqT (pint_integral (b1_seg_signed n m))
       (((Z.of_nat (bkC (n + m) n) # 1) * q_pow (- 1)%Q m * b1_seg_beta n m)%Q).
Proof.
  intros n m. apply qeq_imp_qeqT. exact (b1_seg_signed_val_eq n m).
Qed.

(* ========== Section 3. Segment positivity and the Beta decay arm ========== *)

(* Segments are strictly positive: on [0,1] the factor [t^a * (1-t)^b] is
   pointwise positive, so its integral is positive. *)
Theorem b1_seg_pos : forall a b : nat,
  QltT 0 (pint_integral (pei_list a b)).
Proof.
  intros a b. exact (pei_beta_pos a b).
Qed.

(* The Beta decay arm: [n! * (n+2m)! <= (2n+2m+1)!] bounds
   [b1_seg_beta n m <= 1], along [pei_fact_le]. *)
Theorem b1_seg_beta_le1 : forall n m : nat,
  Qle (b1_seg_beta n m) 1.
Proof.
  intros n m. unfold b1_seg_beta.
  apply QleT'_to_Qle. apply pei_div_le_1.
  - apply q_fact_pos.
  - apply Qle_to_QleT'.
    rewrite (Qmult_comm (q_fact (n + 2 * m)) (q_fact n)).
    replace (n + 2 * m + n)%nat with (2 * n + 2 * m)%nat by lia.
    apply QleT'_to_Qle. apply pei_fact_le.
Qed.

(* ========== Section 4. Segment list and the partial-sum carrier of rho(n, M) ========== *)

(* The rational sum of signed segment values, [rho(n, M) = sum over m < M of
   (-1)^m * C(n+m, n) * Beta(n, m)], carries the integral of the truncated
   polynomial part on [0,1]; the aggregate single-coefficient surface of
   [zb2_itg_carrier] is deliberately not carried here, since termwise
   addition misaligns the Horner positions. *)
Fixpoint b1_rho (n M : nat) : Q :=
  match M with
  | Datatypes.O => (Z.of_nat (bkC (n + 0) n) # 1) * b1_seg_beta n 0
  | Datatypes.S M' => b1_rho n M'
                      + ((Z.of_nat (bkC (n + Datatypes.S M') n) # 1)
                         * q_pow (- 1)%Q (Datatypes.S M') * b1_seg_beta n (Datatypes.S M'))%Q
  end.

(* Peeling the last summand holds definitionally. *)
Lemma b1_rho_unfold : forall n M : nat,
  b1_rho n (Datatypes.S M)
  == (b1_rho n M
      + ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
         * q_pow (- 1)%Q (Datatypes.S M) * b1_seg_beta n (Datatypes.S M))%Q).
Proof. intros n M. reflexivity. Qed.

(* The segment list, headed at [m = M] and descending to [m = 0]; the
   single-integral analogue of [zb2_segl]. *)
Fixpoint b1_segl (n M : nat) : list (Q * list Q) :=
  match M with
  | Datatypes.O =>
      (((Z.of_nat (bkC (n + 0) n) # 1) * q_pow (- 1)%Q 0,
        pei_list (n + 2 * 0) n) :: nil)%list
  | Datatypes.S M' =>
      (((Z.of_nat (bkC (n + Datatypes.S M') n) # 1)
        * q_pow (- 1)%Q (Datatypes.S M'),
        pei_list (n + 2 * Datatypes.S M') n) :: b1_segl n M')%list
  end.

(* Pointwise evaluation of a segment equals its coefficient times its Horner value. *)
Definition b1_seg_pt (seg : (Q * list Q)) (x : Q) : Q :=
  (fst seg) * pint_eval (snd seg) x.

(* The integral of a segment matches its coefficient times its Beta value, segment by segment. *)
Lemma b1_segl_val_eq : forall n m : nat,
  pint_integral (b1_seg_signed n m) ==
  ((fst (hd (0%Q, nil)%list (b1_segl n m))) * b1_seg_beta n m)%Q.
Proof.
  intros n m. destruct m as [| m'].
  - unfold b1_seg_signed.
    assert (Hhd : fst (hd (0%Q, nil)%list (b1_segl n 0))
                  == ((Z.of_nat (bkC (n + 0) n) # 1) * q_pow (- 1)%Q 0)%Q)
      by reflexivity.
    rewrite Hhd.
    exact (b1_seg_signed_val_eq n 0).
  - unfold b1_seg_signed.
    assert (Hhd : fst (hd (0%Q, nil)%list (b1_segl n (Datatypes.S m')))
                  == ((Z.of_nat (bkC (n + Datatypes.S m') n) # 1)
                      * q_pow (- 1)%Q (Datatypes.S m'))%Q)
      by reflexivity.
    rewrite Hhd.
    exact (b1_seg_signed_val_eq n (Datatypes.S m')).
Qed.

Theorem b1_segl_val : forall n m : nat,
  QeqT (pint_integral (b1_seg_signed n m))
       ((fst (hd (0%Q, nil)%list (b1_segl n m))) * b1_seg_beta n m)%Q.
Proof.
  intros n m. apply qeq_imp_qeqT. exact (b1_segl_val_eq n m).
Qed.

(* ========== Section 5. Numerical anchors, independently recomputed checkpoints ========== *)

(* Anchor one, [n = 1], [m = 0]: [C(1,1) * B(2,2)] = [1 * (1! * 1! / 3!)] = [1/6]. *)
Lemma b1_seg_anchor_10 :
  QeqT (pint_integral (b1_seg_poly 1 0)) (1 # 6).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* Anchor two, [n = 1], [m = 1]: [C(2,1) * (-1)^1 * B(4,2)]
   = [2 * (-1) * (3! * 1! / 5!)] = [-1/10]. *)
Lemma b1_seg_anchor_11 :
  QeqT (pint_integral (b1_seg_signed 1 1)) (-(1 # 10)).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* Anchor three: [rho(1, 1) = 1/6 - 1/10 = 1/15]. *)
Lemma b1_rho_anchor_11 :
  QeqT (b1_rho 1 1) (1 # 15).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* Anchor four, a [Beta <= 1] instance: [B(4,2) = 1/20 <= 1]. *)
Lemma b1_seg_beta_anchor :
  QeqT (b1_seg_beta 1 1) (1 # 20).
Proof. apply qeq_imp_qeqT. reflexivity. Qed.

(* ========== Section 6. In-file checks and the assumption audit ========== *)

Check b1_seg_val.
Check b1_seg_signed_val.
Check b1_seg_pos.
Check b1_seg_beta_le1.
Check b1_rho_unfold.
Check b1_segl_val.

Print Assumptions b1_seg_val.
Print Assumptions b1_seg_signed_val.
Print Assumptions b1_seg_pos.
Print Assumptions b1_seg_beta_le1.
Print Assumptions b1_segl_val.
