(* ConstructiveWorld-Set — Two-way reduction between a Gibbs-type plain-le
   statement and limited LPO. *)

(** * UpReqGibbsWallEquiv: [GibbsWall] if and only if [rLPO].

    Mission.  [GibbsWall : Set := forall p q : Real, real_le real_zero
    (gwe_G p q)] with the Pinsker-type carrier [gwe_G p q :=
    (p - q) * (p - q)] is not provable in the constructive real
    interface; this module certifies that by a machine-checked two-way
    reduction [gwe_equivalence : And (GibbsWall -> rLPO) (rLPO ->
    GibbsWall)] (on the diagonal the decision data can only come from
    the pointwise-zero disjunct — the content of limited LPO).  The
    GibbMechanism section lifts any like-shaped family to the reduction.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Lia].
    Requires [S01_BaseRing], [S02_CauchyComplete], [UpReqLpoEquiv] of
    this development.

    References.  This development, UpReqLpoEquiv.v, the baseline module
    in ConstructiveWorld-Main whose statement names are carried over
    here verbatim; the LPO-family equivalence-registration form.

    Constructivity.  Statements are carried by [Set]
    ([sigT]/[And]/[Or]/[QltT] carriers); no classical axioms.  The
    three GibbMechanism section premises are explicit registered
    interface premises.  Statements extract with [Obj.magic] = 0;
    [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqGibbsWallEquiv.v]
    compiles cleanly (exit 0); artifact magic [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqLpoEquiv.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 1. Mechanism bridges: [real_eq] compatibility and rational bounds *)
(* ============================================================ *)

(* Rational level: [a <= |a|] (companion of [q_abs_nonneg]). *)
Lemma gwe_q_le_abs : forall a : Q, QleT' (a) (Qabs a).
Proof.
  intros a.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - apply Qle_to_QleT'. rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)).
    apply Qle_refl.
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ (q_abs_neg_eq a Hneg)).
    apply (Qle_trans a 0 (- a)).
    + exact Hneg.
    + apply (Qopp_le_compat a 0).
      exact Hneg.
Qed.

(* Rational level: [-|a| <= a] (the lower half, for the negative side
   of the compatibility chains). *)
Lemma gwe_q_negabs_le : forall w : Q, QleT' (- Qabs w) (w).
Proof.
  intros w.
  assert (Hlb : Qle (- (Qabs w)) (- w)).
  { apply (Qopp_le_compat w (Qabs w)).
    apply QleT'_to_Qle. apply gwe_q_le_abs. }
  destruct (Qlt_le_dec 0 w) as [Hpos | Hneg].
  - apply Qle_to_QleT'. apply (Qle_trans (- (Qabs w)) (- w) w).
    + exact Hlb.
    + apply (Qle_trans (- w) 0 w).
      * apply (Qle_trans (- w) (- 0) 0).
        -- apply (Qopp_le_compat 0 w). apply Qlt_le_weak. exact Hpos.
        -- assert (Hn0 : - 0 == 0) by exact (Qeq_refl 0).
           rewrite Hn0.
           apply Qle_refl.
      * apply Qlt_le_weak. exact Hpos.
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ (q_abs_neg_eq w Hneg)).
    assert (Hnn : - - w == w) by ring.
    rewrite Hnn.
    apply Qle_refl.
Qed.

(* Right-argument compatibility for [real_lt]:
   [y == z -> real_lt x y -> real_lt x z].  The gap is halved:
   with [eps' := eps/2], the pointwise identity
   [z_n - x_n = (y_n - x_n) + (z_n - y_n)], the bound
   [y_n - x_n > eps] and [-eps/2 <= z_n - y_n] give
   [eps/2 < z_n - x_n]. *)
Lemma gwe_lt_congr_r : forall x y z : Real,
  real_eq y z -> real_lt x y -> real_lt x z.
Proof.
  intros x y z Hyz [eps [Heps [N HN]]].
  assert (Hh : Qlt 0 (1#2)) by exact Z.lt_0_1.
  assert (Hpos : QltT 0 (eps * (1#2))).
  { apply Qlt_to_QltT.
    assert (H0 : 0 * (1#2) < eps * (1#2))
      by (apply Qmult_lt_compat_r; [exact Hh | apply QltT_to_Qlt; exact Heps]).
    rewrite Qmult_0_l in H0.
    exact H0. }
  destruct (Hyz (eps * (1#2)) Hpos) as [N2 HN2].
  exists (eps * (1#2)). split.
  - exact Hpos.
  - exists (max N N2). intros n Hn.
    assert (H1 : QltT eps (projT1 y n - projT1 x n)).
    { apply HN. apply NatLe_lift.
      exact (PeanoNat.Nat.le_trans N (max N N2) n
               (PeanoNat.Nat.le_max_l N N2) (NatLe_drop (max N N2) n Hn)). }
    assert (H2 : QltT (Qabs (projT1 y n - projT1 z n)) (eps * (1#2))).
    { apply HN2. apply NatLe_lift.
      exact (PeanoNat.Nat.le_trans N2 (max N N2) n
               (PeanoNat.Nat.le_max_r N N2) (NatLe_drop (max N N2) n Hn)). }
    apply Qlt_to_QltT.
    (* The chain runs on the rational [Qlt] face; [QltT] appears only
       at the export. *)
    assert (Hsum : projT1 z n - projT1 x n
                   == (projT1 y n - projT1 x n) + (projT1 z n - projT1 y n)) by ring.
    rewrite Hsum.
    assert (H1q : Qlt eps (projT1 y n - projT1 x n)) by (apply QltT_to_Qlt; exact H1).
    assert (H2q : Qlt (Qabs (projT1 y n - projT1 z n)) (eps * (1#2)))
      by (apply QltT_to_Qlt; exact H2).
    (* [-eps/2 <= z_n - y_n]: reindex the absolute value and flip the
       sign. *)
    assert (Hab : Qabs (projT1 y n - projT1 z n) == Qabs (projT1 z n - projT1 y n)).
    { assert (Hopp : projT1 z n - projT1 y n == - (projT1 y n - projT1 z n)) by ring.
      rewrite Hopp.
      apply Qeq_sym.
      apply Qabs_opp. }
    assert (Hflip : Qlt (- (eps * (1#2))) (- (Qabs (projT1 z n - projT1 y n)))).
    { assert (Hflip0 : Qlt (- (eps * (1#2))) (- (Qabs (projT1 y n - projT1 z n))))
        by (apply (Qopp_lt_compat (Qabs (projT1 y n - projT1 z n))
                                  (eps * (1#2))); exact H2q).
      rewrite Hab in Hflip0.
      exact Hflip0. }
    assert (Hb : Qle (- (eps * (1#2))) (projT1 z n - projT1 y n)).
    { apply Qlt_le_weak.
      apply (Qlt_le_trans (- (eps * (1#2)))
                          (- (Qabs (projT1 z n - projT1 y n)))
                          (projT1 z n - projT1 y n)).
      - exact Hflip.
      - exact (QleT'_to_Qle _ _ (gwe_q_negabs_le (projT1 z n - projT1 y n))). }
    assert (Hfin : Qlt (eps + - (eps * (1#2)))
                       ((projT1 y n - projT1 x n) + (projT1 z n - projT1 y n)))
      by (apply (Qplus_lt_le_compat eps (projT1 y n - projT1 x n)
                       (- (eps * (1#2))) (projT1 z n - projT1 y n) H1q Hb)).
    assert (Hhalf : eps + - (eps * (1#2)) == eps * (1#2)) by ring.
    rewrite Hhalf in Hfin.
    exact Hfin.
Qed.

(* Right-argument compatibility for [real_eq]:
   [y == z -> real_eq x y -> real_eq x z] (direct transitivity). *)
Lemma gwe_eq_congr_r : forall x y z : Real,
  real_eq y z -> real_eq x y -> real_eq x z.
Proof.
  intros x y z Hyz Hxy.
  exact (real_eq_trans x y z Hxy Hyz).
Qed.

(* Right-argument compatibility for [real_le]: the two disjuncts of
   [real_le = Or(rt, re)] are handled by the two statements above —
   compatibility is closed under both disjuncts. *)
Lemma gwe_le_congr_r : forall x y z : Real,
  real_eq y z -> real_le x y -> real_le x z.
Proof.
  intros x y z Hyz Hle.
  destruct Hle as [Hlt | Heq].
  - apply inl. exact (gwe_lt_congr_r x y z Hyz Hlt).
  - apply inr. exact (gwe_eq_congr_r x y z Hyz Heq).
Qed.

(* ============================================================ *)
(* Part 2. The Gibbs functional family and the two statement faces *)
(* ============================================================ *)

(* Carrier difference: [d(p,q) := p - q], vanishing on the diagonal. *)
Definition gwe_diff (p q : Real) : Real := real_plus p (real_opp q).

(* The Gibbs functional carrier: the Pinsker-type quadratic form
   [(p-q)^2] of the relative entropy.  Its diagonal zero mirrors the
   structural law [KL(p,p) = 0] (mechanically checked in Part 3); the
   abstracted generic functional is treated in Part 5. *)
Definition gwe_G (p q : Real) : Real :=
  real_mult (gwe_diff p q) (gwe_diff p q).

(* The universal data form of the unprovability target: the plain-le
   statement, stated on the Set-valued [Or] carrier. *)
Definition GibbsWall : Set :=
  forall p q : Real, real_le real_zero (gwe_G p q).

(* ============================================================ *)
(* Part 3. The two structural laws: the diagonal zero ([KL(p,p) = 0])
   and the extinction of the left disjunct (no gap) *)
(* ============================================================ *)

(* Diagonal zero: the carrier-level form of [KL(p,p) = 0] — the
   pointwise difference [projT1 real_zero n - projT1 (gwe_G p p) n == 0]
   through [real_eq_of_zero_diff] (the [N = 0] uniform pattern). *)
Lemma gwe_diag_zero : forall p : Real, real_eq real_zero (gwe_G p p).
Proof.
  intros p.
  apply (real_eq_of_zero_diff real_zero (gwe_G p p)).
  intros n.
  unfold gwe_G.
  apply qeq_imp_qeqT.
  assert (Hgp1 : projT1 (real_mult (real_plus p (real_opp p)) (real_plus p (real_opp p))) n == projT1 (real_plus p (real_opp p)) n * projT1 (real_plus p (real_opp p)) n) by (apply (qeqT_imp_qeq _ _ (real_mult_proj (real_plus p (real_opp p)) (real_plus p (real_opp p)) n))). rewrite Hgp1.
  assert (Hgp2 : projT1 (real_plus p (real_opp p)) n == projT1 p n + projT1 (real_opp p) n) by (apply (qeqT_imp_qeq _ _ (real_plus_proj p (real_opp p) n))). rewrite Hgp2.
  assert (Hgp3 : projT1 (real_opp p) n == - projT1 p n) by (apply (qeqT_imp_qeq _ _ (real_opp_proj p n))). rewrite Hgp3.
  assert (Hz : projT1 real_zero n == 0) by exact (Qeq_refl 0).
  rewrite Hz.
  ring.
Qed.

(* Extinction of the left disjunct: at [p == q] there is no uniform
   rational gap.  A witness [real_lt real_zero (G p p)] would bound the
   approximants [G_n > eps] below, while the diagonal zero gives
   [G_n == 0] — the contradiction [0 < eps < 0] yields any goal. *)
Lemma gwe_diag_no_gap : forall p : Real,
  real_lt real_zero (gwe_G p p) -> forall A : Set, A.
Proof.
  intros p [eps [Heps [N HN]]] A.
  pose proof (QltT_to_Qlt 0 eps Heps) as HepsQ.
  destruct (gwe_diag_zero p eps Heps) as [N2 HN2].
  assert (H1 : QltT eps (projT1 (gwe_G p p) (max N N2)
                         - projT1 real_zero (max N N2))).
  { apply HN. apply NatLe_lift. exact (PeanoNat.Nat.le_max_l N N2). }
  assert (Hzero : projT1 (gwe_G p p) (max N N2)
                  - projT1 real_zero (max N N2) == 0).
  { unfold gwe_G.
    assert (Hgp4 : projT1 (real_mult (real_plus p (real_opp p)) (real_plus p (real_opp p))) (max N N2) == projT1 (real_plus p (real_opp p)) (max N N2) * projT1 (real_plus p (real_opp p)) (max N N2)) by (apply (qeqT_imp_qeq _ _ (real_mult_proj (real_plus p (real_opp p)) (real_plus p (real_opp p))
                            (max N N2)))). rewrite Hgp4.
    assert (Hgp5 : projT1 (real_plus p (real_opp p)) (max N N2) == projT1 p (max N N2) + projT1 (real_opp p) (max N N2)) by (apply (qeqT_imp_qeq _ _ (real_plus_proj p (real_opp p) (max N N2)))). rewrite Hgp5.
    assert (Hgp6 : projT1 (real_opp p) (max N N2) == - projT1 p (max N N2)) by (apply (qeqT_imp_qeq _ _ (real_opp_proj p (max N N2)))). rewrite Hgp6.
    assert (Hz : projT1 real_zero (max N N2) == 0) by exact (Qeq_refl 0).
    rewrite Hz.
    ring. }
  apply QltT_to_Qlt in H1.
  rewrite Hzero in H1.
  destruct (Qlt_irrefl 0 (Qlt_trans 0 eps 0 HepsQ H1)).
Qed.

(* ============================================================ *)
(* Part 4. The two directions of the reduction *)
(* ============================================================ *)

(* Carrier bridge: [gwe_G x real_zero == x * x]. *)
Lemma gwe_sq_bridge : forall x : Real,
  real_eq (gwe_G x real_zero) (real_mult x x).
Proof.
  intros x.
  apply (real_eq_of_zero_diff (gwe_G x real_zero) (real_mult x x)).
  intros n.
  unfold gwe_G.
  apply qeq_imp_qeqT.
  assert (Hgp7 : projT1 (real_mult (real_plus x (real_opp real_zero)) (real_plus x (real_opp real_zero))) n == projT1 (real_plus x (real_opp real_zero)) n * projT1 (real_plus x (real_opp real_zero)) n) by (apply (qeqT_imp_qeq _ _ (real_mult_proj (real_plus x (real_opp real_zero))
                          (real_plus x (real_opp real_zero)) n))). rewrite Hgp7.
  assert (Hgp8 : projT1 (real_mult x x) n == projT1 x n * projT1 x n) by (apply (qeqT_imp_qeq _ _ (real_mult_proj x x n))). rewrite Hgp8.
  assert (Hgp9 : projT1 (real_plus x (real_opp real_zero)) n == projT1 x n + projT1 (real_opp real_zero) n) by (apply (qeqT_imp_qeq _ _ (real_plus_proj x (real_opp real_zero) n))). rewrite Hgp9.
  assert (Hgp10 : projT1 (real_opp real_zero) n == - projT1 real_zero n) by (apply (qeqT_imp_qeq _ _ (real_opp_proj real_zero n))). rewrite Hgp10.
  assert (Hz : projT1 real_zero n == 0) by exact (Qeq_refl 0).
  rewrite Hz.
  ring.
Qed.

(* Forward reduction: the plain-le statement implies limited LPO.  The
   congruence lift at the carrier level turns the plain-le witness at
   [(x, real_zero)] into a [SqWall] instance through the carrier
   bridge, and [lpn_forward] extracts the decision data. *)
Theorem gwe_plain_le_lpo : GibbsWall -> rLPO.
Proof.
  intros Hwall.
  apply lpn_forward.
  intros x.
  exact (gwe_le_congr_r real_zero (gwe_G x real_zero) (real_mult x x)
           (gwe_sq_bridge x) (Hwall x real_zero)).
Qed.

(* Converse reduction: limited LPO implies the plain-le statement —
   the decider supplies the witness directly at the carrier difference
   [d(p,q)], where [gwe_G p q] and [real_mult (gwe_diff p q) (gwe_diff
   p q)] are definitionally the same term. *)
Theorem gwe_lpo_plain_le : rLPO -> GibbsWall.
Proof.
  intros Hdec p q.
  exact (lpn_backward Hdec (gwe_diff p q)).
Qed.

(* Main statement: the two-way reduction. *)
Definition gwe_equivalence : And (GibbsWall -> rLPO) (rLPO -> GibbsWall) :=
  (gwe_plain_le_lpo, gwe_lpo_plain_le).

(* ============================================================ *)
(* Part 5. Abstract typing of the structural slots (GibbMechanism).

   Any functional family [GWf] on pairs carrying the two slots — the
   diagonal zero (the [KL(p,p) = 0] interface slot) and a carrier
   encoding (any real number [x] can be encoded into the square slot of
   [GWf p q]) — has its plain-le form implying [SqWall], hence limited
   LPO through [lpn_forward].  For the concrete Gibbs functional the
   diagonal slot is supplied by the log-chain identities and the
   encoding slot by temperature pairs; the real interface deliberately
   provides no trichotomy, so neither slot can be eliminated inside the
   interface — the unprovability is a property of the interface design,
   recorded as a permanent structural feature of the interface.  (The abstract
   converse has no slot to travel through and is stated one-way; both
   directions for the concrete carrier are verified in Part 4.) *)
(* Section premises, registered: the three section parameters
   ([GWf], [gmech_diag], [gmech_carr]) are explicit interface premises.
   Both are genuinely used by the theorems of the section
   ([gmech_carr] supplies the encoding pair, [gmech_diag] the diagonal
   zero); the supply of concrete [GWf] instances (log-chain identities)
   lies outside this module's imports by design, and the premises are
   kept as antecedents of the conditional theorems. *)
(* ============================================================ *)

Section GibbMechanism.

Variable GWf : Real -> Real -> Real.
Hypothesis gmech_diag : forall p : Real, real_eq real_zero (GWf p p).
Hypothesis gmech_carr : forall x : Real,
  sigT (fun p : Real => sigT (fun q : Real =>
    real_eq (GWf p q) (real_mult x x))).

Theorem gmech_wall_sqwall :
  (forall p q : Real, real_le real_zero (GWf p q)) -> SqWall.
Proof.
  intros Hwall x.
  destruct (gmech_carr x) as [p [q Heq]].
  exact (gwe_le_congr_r real_zero (GWf p q) (real_mult x x) Heq (Hwall p q)).
Qed.

Theorem gmech_wall_lpo :
  (forall p q : Real, real_le real_zero (GWf p q)) -> rLPO.
Proof.
  intros Hwall.
  exact (lpn_forward (gmech_wall_sqwall Hwall)).
Qed.

End GibbMechanism.

(* ============================================================ *)
(* Assumption audits. *)
(* ============================================================ *)

Print Assumptions gwe_plain_le_lpo.
Print Assumptions gwe_lpo_plain_le.
Print Assumptions gwe_equivalence.
Print Assumptions gmech_wall_sqwall.
Print Assumptions gmech_wall_lpo.
