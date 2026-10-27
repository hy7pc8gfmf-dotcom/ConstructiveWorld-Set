(* ConstructiveWorld-Set — decidable-sign instance of geometric gradient
   decay over the rationals. *)

(** * p4a_GradSignQDec: gradient decay with a decidable sign instance.

    Mission. On the computable instance [grad mu x = mu * x] the sign
    branches are dispatched by the constructive three-way comparator
    [Q_dec], so no sign premise is needed: the single-step contraction
    [gsq_grad_step_abs_contraction_full] ([|g(step x)| <= kappa * |g x|],
    [kappa = 1 - eta * mu]), the orbit decay
    [gsq_grad_decay_full_sign_iter] ([|g(x_{n+k})| <= kappa^k * |g(x_n)|])
    and the tail budget [gsq_grad_tail_budget].

    Dependencies. Stdlib [QArith_base], [Qring], [Qabs], [Lia]; requires
    [S02_CauchyComplete] of this development.

    References. ConstructiveWorld-Main ConstructiveWorld_Live/
    p4a_GradSignQDec.v, whose statement names are carried over here
    verbatim (statement-face Set-carrier completion); the statements mirror
    the real-layer full-sign decay family of S09_EntropyReal.

    Constructivity. All statements are carried by [Set] ([QleT'], [QltT],
    [QeqT]); the sign dispatch uses the [sumbool]-based [Q_dec]; premises
    are explicit; [Obj.magic] = 0 and a [coqchk] run reports a closed global
    context.

    Build. [rocq c -native-compiler no -q -Q . "" p4a_GradSignQDec.v]
    compiles cleanly (exit 0); artifact magic [436f7121 00015ff4]. *)

From Stdlib Require Import QArith_base Qring Qabs Lia.
Require Import S02_CauchyComplete.

(* ---- Definitions: gradient instance of the linear convex potential;
      the potential [Phi x = mu * x^2 / 2] has gradient [g x = mu * x] ---- *)

(* Contraction coefficient [kappa = 1 - eta * mu]; the explicit premises
   [0 < eta], [0 < mu], [eta * mu < 1] place [kappa] in [(0,1)]. *)
Definition gsq_kappa (eta mu : Q) : Q := 1 - eta * mu.

(* Rational-valued gradient instance [g x = mu * x]. *)
Definition gsq_grad (mu x : Q) : Q := mu * x.

(* Sign-branch dynamics: the positive and negative branches take the descent
   step [x - eta * g x] and the zero branch stays put.  The three branches
   are dispatched by the constructive comparator [Q_dec], which removes the
   need for any sign premise. *)
Definition gsq_step (eta mu x : Q) : Q :=
  match Q_dec (gsq_grad mu x) 0 with
  | inleft (left _) => x - eta * (gsq_grad mu x)
  | inleft (right _) => x - eta * (gsq_grad mu x)
  | inright _ => x
  end.

(* Orbit iteration from [x_0] to [x_n]. *)
Fixpoint gsq_iter (eta mu : Q) (n : nat) (x : Q) : Q :=
  match n with
  | O => x
  | S m => gsq_step eta mu (gsq_iter eta mu m x)
  end.

(* Geometric power [kappa^n] in left-multiplication form. *)
Fixpoint gsq_pow (k : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S m => k * gsq_pow k m
  end.

(* ---- Order bridges at the [Q] layer (transport along [Qeq], self-contained) ---- *)

Lemma gsq_qeq_le : forall a b : Q, a == b -> QleT' a b.
Proof.
  intros a b H. apply Qle_to_QleT'. unfold Qeq in H. unfold Qle.
  rewrite H. apply Z.le_refl.
Qed.

Lemma gsq_qeq_lt_r : forall a b c : Q, b == c -> a < b -> QltT a c.
Proof.
  intros a b c Hbc Hab. apply Qlt_to_QltT.
  apply (Qlt_le_trans a b c).
  - exact Hab.
  - exact (QleT'_to_Qle _ _ (gsq_qeq_le b c Hbc)).
Qed.

Lemma gsq_qeq_lt_l : forall a b c : Q, a == b -> b < c -> QltT a c.
Proof.
  intros a b c Hab Hbc. apply Qlt_to_QltT.
  apply (Qle_lt_trans a b c).
  - exact (QleT'_to_Qle _ _ (gsq_qeq_le a b Hab)).
  - exact Hbc.
Qed.

Lemma gsq_mult_pos : forall a b : Q, 0 < a -> 0 < b -> QltT 0 (a * b).
Proof.
  intros a b Ha Hb.
  apply (gsq_qeq_lt_r 0%Q (b * a)%Q (a * b)).
  - apply Qmult_comm.
  - apply QltT_to_Qlt. apply (gsq_qeq_lt_l 0%Q (0 * a)%Q).
    + apply Qeq_sym. apply Qmult_0_l.
    + apply (Qmult_lt_compat_r 0 (b) (a) Ha Hb).
Qed.

(* ---- [kappa] lies in [(0,1)] (carried by [Qlt_minus_iff]) ---- *)

Lemma gsq_kappa_pos : forall eta mu : Q,
  0 < eta -> 0 < mu -> eta * mu < 1 -> QltT 0 (gsq_kappa eta mu).
Proof.
  intros eta mu He Hmu Hk. apply Qlt_to_QltT.
  unfold gsq_kappa.
  apply (proj1 (Qlt_minus_iff (eta * mu) 1)).
  exact Hk.
Qed.

Lemma gsq_kappa_lt_one : forall eta mu : Q,
  0 < eta * mu -> QltT (gsq_kappa eta mu) 1.
Proof.
  intros eta mu Hm. apply Qlt_to_QltT.
  unfold gsq_kappa.
  apply (proj2 (Qlt_minus_iff (1 - eta * mu)%Q 1)).
  apply QltT_to_Qlt. apply (gsq_qeq_lt_r 0%Q (eta * mu)
                               (1 + -(1 - eta * mu))%Q).
  - ring.
  - exact Hm.
Qed.

(* ---- One-step dynamics: [step x == kappa * x], uniform across the three
      branches ---- *)

Lemma gsq_step_val : forall eta mu x : Q,
  QeqT (gsq_step eta mu x) (gsq_kappa eta mu * x).
Proof.
  intros eta mu x. apply qeq_imp_qeqT. unfold gsq_step, gsq_kappa.
  destruct (Q_dec (gsq_grad mu x) 0) as [[Hlt | Hgt] | Heq].
  - unfold gsq_grad in *. ring.
  - unfold gsq_grad in *. ring.
  - assert (Ht : (1 - eta * mu) * x == x - eta * (mu * x)) by ring.
    unfold gsq_grad in Heq |- *.
    rewrite Ht, Heq. ring.
Qed.

(* ---- Main statement 1: single-step full-sign contraction
      [|g(step x)| <= kappa * |g x|], dispatched through the [Q_dec]
      branches ---- *)

Lemma gsq_grad_step_abs_contraction_full : forall eta mu x : Q,
  0 < eta -> 0 < mu -> eta * mu < 1 ->
  QleT' (Qabs (gsq_grad mu (gsq_step eta mu x)))
      (gsq_kappa eta mu * Qabs (gsq_grad mu x)).
Proof.
  intros eta mu x He Hmu Hk.
  assert (Hval : Qabs (gsq_grad mu (gsq_step eta mu x))
                 == gsq_kappa eta mu * Qabs (gsq_grad mu x)).
  { unfold gsq_grad.
    rewrite (qeqT_imp_qeq _ _ (gsq_step_val eta mu x)).
    rewrite (Qabs_Qmult mu (gsq_kappa eta mu * x)).
    rewrite (Qabs_Qmult (gsq_kappa eta mu) x).
    rewrite (Qabs_pos (gsq_kappa eta mu)
               (Qlt_le_weak _ _ (QltT_to_Qlt _ _ (gsq_kappa_pos eta mu He Hmu Hk)))).
    rewrite (Qabs_Qmult mu x).
    ring. }
  exact (gsq_qeq_le _ _ Hval).
Qed.

(* ---- Left-multiplication monotonicity ([Qmult_le_compat_r] with the
      factors in the other order) ---- *)

Lemma gsq_le_mult_compat_l : forall a x y : Q,
  0 <= a -> Qle x y -> QleT' (a * x) (a * y).
Proof.
  intros a x y Ha Hxy. apply Qle_to_QleT'.
  apply (Qle_trans _ (x * a)).
  - exact (QleT'_to_Qle _ _ (gsq_qeq_le _ _ (Qmult_comm a x))).
  - apply (Qle_trans _ (y * a)).
    + apply Qmult_le_compat_r; assumption.
    + exact (QleT'_to_Qle _ _ (gsq_qeq_le _ _ (Qmult_comm y a))).
Qed.

(* ---- Positivity of the geometric power ---- *)

Lemma gsq_pow_nonneg : forall (k : Q) (n : nat), 0 < k -> QleT' 0 (gsq_pow k n).
Proof.
  intros k n Hk. apply Qle_to_QleT'. induction n as [| n IH].
  - cbn [gsq_pow]. apply (Qlt_le_weak _ _).
    unfold Qlt, Qle. cbn. lia.
  - cbn [gsq_pow]. apply (Qle_trans _ (0 * gsq_pow k n)%Q).
    + apply QleT'_to_Qle. apply gsq_qeq_le. apply Qeq_sym. apply Qmult_0_l.
    + apply Qmult_le_compat_r;
        [apply (Qlt_le_weak _ _ Hk) | exact IH].
Qed.

(* ---- Antitone geometric power: [N <= n] implies [kappa^n <= kappa^N] ---- *)

Lemma gsq_pow_anti_mono : forall (k : Q) (n m : nat),
  0 < k -> k < 1 -> (n <= m)%nat -> QleT' (gsq_pow k m) (gsq_pow k n).
Proof.
  intros k n m Hk Hk1 Hnm. apply Qle_to_QleT'.
  assert (Hcore : forall j : nat, Qle (gsq_pow k (n + j)%nat) (gsq_pow k n)).
  { intros j. induction j as [| j IHj].
    - replace (n + 0)%nat with n by lia. apply Qle_refl.
    - replace (n + S j)%nat with (S (n + j))%nat by lia.
      cbn [gsq_pow].
      apply (Qle_trans _ (k * gsq_pow k n)%Q).
      + apply QleT'_to_Qle. apply gsq_le_mult_compat_l;
          [apply (Qlt_le_weak _ _ Hk) | exact IHj].
      + apply (Qle_trans _ (1 * gsq_pow k n)%Q).
        * apply Qmult_le_compat_r;
            [apply (Qlt_le_weak _ _ Hk1)
             | apply QleT'_to_Qle; apply gsq_pow_nonneg; exact Hk].
        * apply QleT'_to_Qle. apply gsq_qeq_le. apply Qmult_1_l. }
  assert (Hq : m = (n + (m - n))%nat) by lia. rewrite Hq. apply Hcore.
Qed.

(* ---- Main statement 2: geometric decay along the full-sign orbit ---- *)

Theorem gsq_grad_decay_full_sign_iter : forall (eta mu x0 : Q) (n k : nat),
  0 < eta -> 0 < mu -> eta * mu < 1 ->
  QleT' (Qabs (gsq_grad mu (gsq_iter eta mu (n + k) x0)))
      (gsq_pow (gsq_kappa eta mu) k * Qabs (gsq_grad mu (gsq_iter eta mu n x0))).
Proof.
  intros eta mu x0 n k He Hmu Hk. apply Qle_to_QleT'.
  assert (Hkap : 0 < gsq_kappa eta mu)
    by (apply QltT_to_Qlt; apply gsq_kappa_pos; assumption).
  induction k as [| k IH].
  - replace (n + 0)%nat with n by lia. cbn [gsq_pow].
    apply QleT'_to_Qle. apply gsq_qeq_le. apply Qeq_sym. apply Qmult_1_l.
  - replace (n + S k)%nat with (S (n + k))%nat by lia.
    cbn [gsq_iter gsq_pow].
    apply (Qle_trans _ (gsq_kappa eta mu
                          * Qabs (gsq_grad mu (gsq_iter eta mu (n + k) x0)))).
    + apply QleT'_to_Qle. apply gsq_grad_step_abs_contraction_full; assumption.
    + apply (Qle_trans _ (gsq_kappa eta mu
                            * (gsq_pow (gsq_kappa eta mu) k
                               * Qabs (gsq_grad mu (gsq_iter eta mu n x0))))).
      * apply QleT'_to_Qle. apply gsq_le_mult_compat_l;
          [apply (Qlt_le_weak _ _ Hkap) | exact IH].
      * apply QleT'_to_Qle. apply gsq_qeq_le. apply Qmult_assoc.
Qed.

(* ---- Main statement 3: tail budget, a [Q]-layer dual of the geometric
      tail budget: choose [N] from a witness premise ---- *)

Theorem gsq_grad_tail_budget : forall (eta mu x0 : Q) (N n : nat) (eps : Q),
  0 < eta -> 0 < mu -> eta * mu < 1 ->
  (N <= n)%nat ->
  Qlt (gsq_pow (gsq_kappa eta mu) N * Qabs (gsq_grad mu x0)) eps ->
  QltT (Qabs (gsq_grad mu (gsq_iter eta mu n x0))) eps.
Proof.
  intros eta mu x0 N n eps He Hmu Hk Hn Hbudget. apply Qlt_to_QltT.
  assert (Hkpos : 0 < eta * mu)
    by (apply QltT_to_Qlt; apply gsq_mult_pos; assumption).
  assert (Hkap : 0 < gsq_kappa eta mu)
    by (apply QltT_to_Qlt; apply gsq_kappa_pos; assumption).
  assert (Hk1 : gsq_kappa eta mu < 1)
    by (apply QltT_to_Qlt; apply gsq_kappa_lt_one; exact Hkpos).
  assert (Hdec : QleT' (Qabs (gsq_grad mu (gsq_iter eta mu n x0)))
                     (gsq_pow (gsq_kappa eta mu) n * Qabs (gsq_grad mu x0))).
  { replace n with (0 + n)%nat by lia.
    apply (gsq_grad_decay_full_sign_iter eta mu x0 0 n He Hmu Hk). }
  apply (Qle_lt_trans _ (gsq_pow (gsq_kappa eta mu) N * Qabs (gsq_grad mu x0))).
  - apply (Qle_trans _ (gsq_pow (gsq_kappa eta mu) n * Qabs (gsq_grad mu x0))).
    + exact (QleT'_to_Qle _ _ Hdec).
    + apply Qmult_le_compat_r;
        [apply QleT'_to_Qle; apply gsq_pow_anti_mono; assumption
         | apply Qabs_nonneg].
  - exact Hbudget.
Qed.

(* ---- Assumption audit and extraction check ---- *)

Print Assumptions gsq_grad_step_abs_contraction_full.
Print Assumptions gsq_grad_decay_full_sign_iter.
Print Assumptions gsq_grad_tail_budget.

From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
Extraction "p4a_gradsignqdec.ml" gsq_grad_decay_full_sign_iter gsq_grad_tail_budget.

Print Assumptions gsq_kappa_pos.
