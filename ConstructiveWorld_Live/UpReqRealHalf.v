(* ConstructiveWorld-Set — Real-carrier halving infrastructure. *)

(** * UpReqRealHalf: the half function on the constructive reals and its laws.

    Mission.  The halving step of the exponential positivity chain: the half
      function [upreq_half x := real_mult (real_const (1#2)) x] with the
      doubling identity [upreq_half_plus], the pointwise projection law
      [upreq_half_proj], compatibility with opposition [upreq_half_opp],
      double-negation elimination [upreq_real_opp_opp], and the exponential
      square identities [upreq_exp_half_sq] and [upreq_exp_neg_half_sq].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Arith.Arith],
      [Setoid], [Morphisms].  Requires [AttnSqrt], [S02_CauchyComplete],
      [S03_QExp], [S07_RealSetoidExpLog] of this development.

    References.  This development, UpReqRealHalf.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim; the doubling identity consumes [sqrt_real_plus_half_half]
      of [AttnSqrt].

    Constructivity.  All statements are carried by [Set] ([real_eq] is a
      Set-valued predicate; no order face is asserted); statements extract
      with [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqRealHalf.v] compiles
      cleanly (exit 0); the artifact starts with the bytes
      [436f7121 00015ff4]. *)

Require Import AttnSqrt.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
Require Import S02_CauchyComplete S03_QExp S07_RealSetoidExpLog.

Local Open Scope Q_scope.

(* The half function: multiplication by the constant sequence (1#2);
   pointwise, each term is halved. *)
Definition upreq_half (x : Real) : Real := real_mult (real_const (1#2)) x.

(* Pointwise projection law for the half function, assembled from the
   S02 projection lemmas; an independent anchor for later budget and
   bound arguments. *)
Lemma upreq_half_proj : forall (x : Real) (n : nat),
  QeqT (projT1 (upreq_half x) n) ((1#2) * projT1 x n).
Proof.
  intros x n.
  apply qeq_imp_qeqT.
  unfold upreq_half.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_const_proj (1#2) x n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (1#2) n)).
  reflexivity.
Qed.

(* The doubling identity: half x + half x == x.  One-step consumption
   of [sqrt_real_plus_half_half] of [AttnSqrt]; the real_eq goal holds
   with the uniformity index N := 0. *)
Theorem upreq_half_plus : forall x : Real,
  real_eq (real_plus (upreq_half x) (upreq_half x)) x.
Proof.
  intro x.
  exact (sqrt_real_plus_half_half x).
Qed.

(* The half function commutes with opposition.  Pointwise, the defect
   (1/2)·(−x_n) − (−(1/2)·x_n) is zero by ring; the uniformity index is
   N := 0. *)
Lemma upreq_half_opp : forall x : Real,
  real_eq (upreq_half (real_opp x)) (real_opp (upreq_half x)).
Proof.
  intros x eps Heps.
  exists 0%nat.
  intros n Hn.
  assert (Hd : projT1 (upreq_half (real_opp x)) n
               - projT1 (real_opp (upreq_half x)) n == 0%Q).
  { assert (H1 := upreq_half_proj (real_opp x) n).
    apply qeqT_imp_qeq in H1.
    rewrite H1.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (upreq_half x) n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)).
    assert (H2 := upreq_half_proj x n).
    apply qeqT_imp_qeq in H2.
    rewrite H2.
    ring. }
  assert (Habs0 : Qabs (projT1 (upreq_half (real_opp x)) n
                        - projT1 (real_opp (upreq_half x)) n) == 0%Q).
  { apply Qeq_trans with (Qabs 0%Q).
    - apply Qabs_wd. exact Hd.
    - reflexivity. }
  apply Qlt_to_QltT.
  setoid_rewrite Habs0.
  apply QltT_to_Qlt. exact Heps.
Qed.

(* Double-negation elimination on the constructive reals; pointwise
   the defect −(−x_n) − x_n is zero by ring, uniformly at N := 0.
   This is the transport basis for cascading the exponential identities
   through the negative-exponent form. *)
Lemma upreq_real_opp_opp : forall x : Real,
  real_eq (real_opp (real_opp x)) x.
Proof.
  intros x eps Heps.
  exists 0%nat.
  intros n Hn.
  assert (Hd : projT1 (real_opp (real_opp x)) n - projT1 x n == 0%Q).
  { setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_opp x) n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)).
    ring. }
  assert (Habs0 : Qabs (projT1 (real_opp (real_opp x)) n
                        - projT1 x n) == 0%Q).
  { apply Qeq_trans with (Qabs 0%Q).
    - apply Qabs_wd. exact Hd.
    - reflexivity. }
  apply Qlt_to_QltT.
  setoid_rewrite Habs0.
  apply QltT_to_Qlt. exact Heps.
Qed.

(* The exponential square identity e^z == (e^(z/2))^2: rewrite z as
   z/2 + z/2 by the doubling identity (respectability via the
   extensionality law), then apply the additivity of the exponential.
   A pure real_eq chain; no order or disjunction face is touched. *)
Theorem upreq_exp_half_sq : forall x : Real,
  real_eq (cauchy_real_exp x)
          (real_mult (cauchy_real_exp (upreq_half x))
                     (cauchy_real_exp (upreq_half x))).
Proof.
  intro x.
  apply (real_eq_trans
          (cauchy_real_exp x)
          (cauchy_real_exp (real_plus (upreq_half x) (upreq_half x)))
          (real_mult (cauchy_real_exp (upreq_half x))
                     (cauchy_real_exp (upreq_half x)))).
  - exact (cauchy_real_exp_wd x (real_plus (upreq_half x) (upreq_half x))
             (real_eq_sym (real_plus (upreq_half x) (upreq_half x)) x
                (upreq_half_plus x))).
  - exact (cauchy_real_exp_plus (upreq_half x) (upreq_half x)).
Qed.

(* The negative-exponent variant e^(−x) == (e^(−x/2))^2: instance the
   general identity at [real_opp x] (the left side folds to
   [real_exp_neg] by definition), and transport each factor
   exp(−(x/2)) == e^(−x/2) through the opposition compatibility of the
   half function, merged by multiplicativity of real_eq.  The positive
   form e^x == (e^(x/2))^2 follows downstream by cascading this at
   [real_opp x] through double-negation elimination; that composition
   is left to the consumer. *)
Theorem upreq_exp_neg_half_sq : forall x : Real,
  real_eq (real_exp_neg x)
          (real_mult (real_exp_neg (upreq_half x))
                     (real_exp_neg (upreq_half x))).
Proof.
  intro x.
  apply (real_eq_trans
          (real_exp_neg x)
          (real_mult (cauchy_real_exp (upreq_half (real_opp x)))
                     (cauchy_real_exp (upreq_half (real_opp x))))
          (real_mult (real_exp_neg (upreq_half x))
                     (real_exp_neg (upreq_half x)))).
  - exact (upreq_exp_half_sq (real_opp x)).
  - apply (RealSetoid.real_eq_mult_compat
             (cauchy_real_exp (upreq_half (real_opp x)))
             (cauchy_real_exp (upreq_half (real_opp x)))
             (real_exp_neg (upreq_half x))
             (real_exp_neg (upreq_half x))).
    + exact (cauchy_real_exp_wd (upreq_half (real_opp x))
               (real_opp (upreq_half x)) (upreq_half_opp x)).
    + exact (cauchy_real_exp_wd (upreq_half (real_opp x))
               (real_opp (upreq_half x)) (upreq_half_opp x)).
Qed.
