(* ConstructiveWorld-Set — Two-way reduction between universal square nonnegativity and limited LPO. *)

(** * UpReqLpoEquiv: [SqWall] if and only if [rLPO].

    Mission.  [SqWall : Set := forall x : Real, real_le real_zero
    (x * x)] is the universal data form of the wall recorded in S02:
    an inhabitant would decide the sign of every real number
    pointwise.  This module certifies its status by a machine-checked
    two-way reduction against limited LPO: [lpn_forward : SqWall ->
    rLPO], [lpn_backward : rLPO -> SqWall], and [lpn_equivalence :
    And (SqWall -> rLPO) (rLPO -> SqWall)] — the equivalence that
    measures the statement's unprovability, not a proof of falsity.
    Rational companions: [q_sq_nonneg], [q_sq_le_abs], the strict
    multiplication bridges, the [Qeq]-to-[Qle] transfer, [q_0_lt_1].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Lia].
    Requires [S01_BaseRing], [S02_CauchyComplete] of this development.

    References.  This development, the baseline module in
    ConstructiveWorld-Main whose statement names are carried over here
    verbatim (statement-face Set-carrier completion).

    Constructivity.  Statements are carried by [Set]
    ([sigT]/[And]/[Or] carriers); no classical axioms; the main
    statements carry no hypotheses.  Statements extract with
    [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqLpoEquiv.v]
    compiles cleanly (exit 0); artifact magic [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 1. Rational companions, by the two sign cases of [Qabs_pos]
   and [Qabs_opp] *)
(* ============================================================ *)

Lemma q_0_lt_1 : QltT 0 1.
Proof.
  apply Qlt_to_QltT. apply (proj2 (Qlt_alt 0 1)).
  reflexivity.
Qed.

(* Negative case: [a <= 0] gives [|a| == -a] (transfer through
   [Qabs (-a)]). *)
Lemma q_abs_neg_eq : forall a : Q, a <= 0 -> QeqT (Qabs a) (- a).
Proof.
  intros a Ha. apply qeq_imp_qeqT.
  assert (Hpos : 0 <= - a).
  { apply (Qopp_le_compat a 0). exact Ha. }
  rewrite <- (Qabs_opp a).
  apply Qabs_pos.
  exact Hpos.
Qed.

(* [|a| >= 0]. *)
Lemma q_abs_nonneg : forall a : Q, QleT' (0) (Qabs a).
Proof.
  intros a. apply Qle_to_QleT'.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)).
    apply Qlt_le_weak.
    exact Hpos.
  - rewrite (qeqT_imp_qeq _ _ (q_abs_neg_eq a Hneg)).
    apply (Qopp_le_compat a 0).
    exact Hneg.
Qed.

(* [a * a >= 0] (two sign cases plus multiplication monotonicity). *)
Lemma q_sq_nonneg : forall a : Q, QleT' (0) (a * a).
Proof.
  intros a. apply Qle_to_QleT'.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - assert (H0 : 0 * a <= a * a) by (apply Qmult_le_compat_r; apply Qlt_le_weak; exact Hpos).
    rewrite Qmult_0_l in H0.
    exact H0.
  - assert (Habs : Qabs a == - a) by (apply qeqT_imp_qeq; apply q_abs_neg_eq; exact Hneg).
    assert (Ha : a * a == (- a) * (- a)) by ring.
    rewrite Ha.
    assert (Hnn : 0 <= - a) by (apply (Qopp_le_compat a 0); exact Hneg).
    assert (H0 : 0 * (- a) <= (- a) * (- a)) by (apply Qmult_le_compat_r; assumption).
    rewrite Qmult_0_l in H0.
    exact H0.
Qed.

(* [|a * a| == |a| * |a|] (companion of the square law for [Qabs]). *)
Lemma qabs_sq : forall a : Q, QeqT (Qabs (a * a)) (Qabs a * Qabs a).
Proof.
  intros a. apply qeq_imp_qeqT.
  assert (Hnn : 0 <= a * a) by (apply QleT'_to_Qle; apply q_sq_nonneg).
  rewrite (Qabs_pos (a * a) Hnn).
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)).
    reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (q_abs_neg_eq a Hneg)).
    ring.
Qed.

(* Nonlinear pivot: [|a| <= 1] implies [a * a <= |a|] (through the
   [1 * |a|] form). *)
Lemma q_sq_le_abs : forall a : Q, Qabs a <= 1 -> QleT' (a * a) (Qabs a).
Proof.
  intros a Hab. apply Qle_to_QleT'.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)).
    rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)) in Hab.
    assert (H1 : a * a <= 1 * a) by (apply Qmult_le_compat_r; [exact Hab | apply Qlt_le_weak; exact Hpos]).
    rewrite Qmult_1_l in H1.
    exact H1.
  - assert (Habs : Qabs a == - a) by (apply qeqT_imp_qeq; apply q_abs_neg_eq; exact Hneg).
    rewrite Habs in Hab.
    rewrite Habs.
    assert (Hrepl : (- a) * (- a) == a * a) by ring.
    setoid_rewrite <- Hrepl.
    assert (H1 : (- a) * (- a) <= 1 * (- a)) by (apply Qmult_le_compat_r; [exact Hab | apply (Qopp_le_compat a 0); exact Hneg]).
    rewrite Qmult_1_l in H1.
    exact H1.
Qed.

(* Strict multiplication bridge: [c < |a|] and [0 < c] give
   [c * c < a * a] (used for the forward gap). *)
Lemma q_sq_lt_sq : forall c a : Q, 0 < c -> c < Qabs a -> QltT (c * c) (a * a).
Proof.
  intros c a Hc0 Hca. apply Qlt_to_QltT.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - assert (Habs : Qabs a == a) by (apply Qabs_pos; apply Qlt_le_weak; exact Hpos).
    rewrite Habs in Hca.
    assert (H1 : c * c < a * c) by (apply Qmult_lt_compat_r; assumption).
    assert (H2 : c * a < a * a) by (apply Qmult_lt_compat_r; [exact Hpos | exact Hca]).
    rewrite (Qmult_comm a c) in H1.
    apply Qlt_trans with (c * a); [exact H1 | exact H2].
  - assert (Habs : Qabs a == - a) by (apply qeqT_imp_qeq; apply q_abs_neg_eq; exact Hneg).
    rewrite Habs in Hca.
    assert (Hrepl : (- a) * (- a) == a * a) by ring.
    setoid_rewrite <- Hrepl.
    assert (H1 : c * c < (- a) * c) by (apply Qmult_lt_compat_r; [exact Hc0 | exact Hca]).
    assert (Hca0 : 0 < (- a)) by (apply Qlt_le_trans with c; [exact Hc0 | apply Qlt_le_weak; exact Hca]).
    assert (H2 : c * (- a) < (- a) * (- a)) by (apply Qmult_lt_compat_r; [exact Hca0 | exact Hca]).
    rewrite (Qmult_comm (- a) c) in H1.
    apply Qlt_trans with (c * (- a)); [exact H1 | exact H2].
Qed.

(* No-square-root vanishing bridge: [|a * a| < e * e] and [0 < e] give
   [|a| < e] (the converse branch [e <= |a|] would give
   [e^2 <= |a|^2], a contradiction). *)
Lemma q_sq_abs_lt : forall a e : Q, 0 < e -> Qabs (a * a) < e * e -> QltT (Qabs a) (e).
Proof.
  intros a e He0 Hlt. apply Qlt_to_QltT.
  destruct (Qlt_le_dec (Qabs a) e) as [Hlt2 | Hge].
  - exact Hlt2.
  - exfalso.
    assert (Hge0 : 0 <= e) by (apply Qlt_le_weak; exact He0).
    assert (H1a : e * e <= Qabs a * e) by (apply (Qmult_le_compat_r e (Qabs a) e); assumption).
    assert (H1b : e * Qabs a <= Qabs a * Qabs a)
      by (apply (Qmult_le_compat_r e (Qabs a) (Qabs a));
          [exact Hge | apply QleT'_to_Qle; apply q_abs_nonneg]).
    rewrite (Qmult_comm e (Qabs a)) in H1b.
    rewrite <- (qeqT_imp_qeq _ _ (qabs_sq a)) in H1b.
    apply (Qlt_irrefl (e * e)).
    apply Qle_lt_trans with (Qabs (a * a)).
    + exact (Qle_trans (e * e) (Qabs a * e) (Qabs (a * a)) H1a H1b).
    + exact Hlt.
Qed.

(* ============================================================ *)

(*   Every transfer goes through top-face [Qabs] atoms plus the
   companion congruence laws, with no instance dependence. *)
(* ============================================================ *)

(* Top-face transfer from [Qeq] to [Qle] (case split on [Qlt_le_dec],
   refutation by [Qlt_irrefl]). *)
Lemma q_eq_le : forall a b : Q, a == b -> QleT' (a) (b).
Proof.
  intros a b H.
  destruct (Qlt_le_dec b a) as [Hlt | Hle].
  - exfalso.
    apply (Qlt_irrefl b).
    rewrite H in Hlt.
    exact Hlt.
  - apply Qle_to_QleT'. exact Hle.
Qed.

(* [Qabs] congruence: [x == y] implies [|x| == |y|]. *)
Lemma q_abs_congr : forall x y : Q, x == y -> QeqT (Qabs x) (Qabs y).
Proof.
  intros x y H. apply qeq_imp_qeqT.
  destruct (Qlt_le_dec 0 x) as [Hx | Hx].
  - (* Case [0 < x]: transfer [0 <= y] and close both faces with
       [Qabs_pos]. *)
    assert (Hxle : 0 <= x) by (apply Qlt_le_weak; exact Hx).
    pose proof Hxle as Hy.
    rewrite H in Hy.
    rewrite (Qabs_pos x Hxle).
    rewrite (Qabs_pos y Hy).
    exact H.
  - (* Case [x <= 0]: both faces via the negative-branch law, then the
       negative congruence ([Qopp_le_compat] twice and
       [Qle_antisym]). *)
    rewrite (qeqT_imp_qeq _ _ (q_abs_neg_eq x Hx)).
    rewrite H in Hx.
    rewrite (qeqT_imp_qeq _ _ (q_abs_neg_eq y Hx)).
    apply (Qle_antisym (- x) (- y)).
    + apply (Qopp_le_compat y x).
      apply QleT'_to_Qle. apply q_eq_le.
      rewrite H.
      reflexivity.
    + apply (Qopp_le_compat x y).
      apply QleT'_to_Qle. apply q_eq_le.
      exact H.
Qed.

(* ============================================================ *)
(* Part 2. The two statement faces *)
(* ============================================================ *)

(* The universal data form of the wall (the S02 remark, lifted to the
   Set-carried face). *)
Definition SqWall : Set :=
  forall x : Real, real_le real_zero (real_mult x x).

(* Limited LPO: the zero-problem decision form for Cauchy reals (a
   uniform positive lower bound of [|x|] versus pointwise vanishing). *)
Definition rLPO : Set :=
  forall x : Real,
    Or
      (sigT (fun c : Q =>
        And (QltT 0 c)
            (sigT (fun N : nat => forall n : nat, NatLe N n ->
              QltT c (Qabs (projT1 x n))))))
      (forall eps : Q, QltT 0 eps ->
        sigT (fun N : nat => forall n : nat, NatLe N n ->
          QltT (Qabs (projT1 x n)) eps)).

(* ============================================================ *)
(* Part 3. Forward direction: the wall implies limited LPO (the
   witness data yields the criterion) *)
(* ============================================================ *)

Theorem lpn_forward : SqWall -> rLPO.
Proof.
  intros Hwall x.
  destruct (Hwall x) as [Hlt | Heq].
  - (* Left disjunct: [0 < x * x] with a uniform gap [eps] gives a
       uniform positive lower bound of [|x|]. *)
    destruct Hlt as [eps [Heps [N HN]]].
    destruct (Qlt_le_dec 1 eps) as [Hbig | Hsmall].
    + (* Case [eps > 1]: take [c := 1]; if some approximant satisfied
         [|x_n| <= 1] then [x_n^2 <= |x_n| <= 1 < eps], a
         contradiction. *)
      apply inl.
      exists 1. split.
      * apply Qlt_to_QltT.
        exact (QltT_to_Qlt _ _ q_0_lt_1).
      * exists N. intros n Hn.
        specialize (HN n Hn).
        apply QltT_to_Qlt in HN.
        apply Qlt_to_QltT.
        (* [eps < projT1 (x*x) n = x_n * x_n] (projection bridge). *)
        assert (Hp : eps < projT1 x n * projT1 x n).
        { assert (Hz : projT1 real_zero n == 0) by reflexivity.
          rewrite Hz in HN.
          assert (Hm : projT1 (real_mult x x) n - 0 == projT1 (real_mult x x) n) by ring.
          rewrite Hm in HN.
          setoid_rewrite <- (qeqT_imp_qeq _ _ (real_mult_proj x x n)).
          exact HN. }
        destruct (Qlt_le_dec 1 (Qabs (projT1 x n))) as [Hbig' | Hsmall'].
        -- exact Hbig'.
        -- exfalso.
           assert (Hle : projT1 x n * projT1 x n <= Qabs (projT1 x n))
             by (apply QleT'_to_Qle; apply q_sq_le_abs; exact Hsmall').
           assert (Hlt1 : eps < 1).
           { apply Qlt_le_trans with (projT1 x n * projT1 x n).
             exact Hp.
             exact (Qle_trans (projT1 x n * projT1 x n) (Qabs (projT1 x n)) 1 Hle Hsmall'). }
           apply (Qlt_irrefl 1).
           apply Qlt_trans with eps; [exact Hbig | exact Hlt1].
    + (* Case [eps <= 1]: take [c := eps]; split on [|x_n| >= 1] versus
         [|x_n| <= 1]. *)
      apply inl.
      exists eps. split.
      * exact Heps.
      * exists N. intros n Hn.
        specialize (HN n Hn).
        apply QltT_to_Qlt in HN.
        apply Qlt_to_QltT.
        assert (Hp : eps < projT1 x n * projT1 x n).
        { assert (Hz : projT1 real_zero n == 0) by reflexivity.
          rewrite Hz in HN.
          assert (Hm : projT1 (real_mult x x) n - 0 == projT1 (real_mult x x) n) by ring.
          rewrite Hm in HN.
          setoid_rewrite <- (qeqT_imp_qeq _ _ (real_mult_proj x x n)).
          exact HN. }
        destruct (Qlt_le_dec 1 (Qabs (projT1 x n))) as [Hbig' | Hsmall'].
        -- (* [|x_n| >= 1]: then [eps <= 1 < |x_n|] (direct chain). *)
           exact (Qle_lt_trans eps 1 (Qabs (projT1 x n)) Hsmall Hbig').
        -- (* [|x_n| <= 1]: then [eps < x_n * x_n <= |x_n|] (the pivot). *)
           apply Qlt_le_trans with (projT1 x n * projT1 x n).
           ++ exact Hp.
           ++ apply QleT'_to_Qle. apply q_sq_le_abs.
              exact Hsmall'.
  - (* Right disjunct: [x * x == 0] pointwise gives [x == 0] pointwise
       (the no-square-root bridge). *)
    (* The pointwise term is [Qabs (0 - x_n * x_n)] under the
       difference-order presentation of [real_eq]; the square is
       supplied through its projection form, the top face is
       transferred by [q_abs_congr], and the gap [delta := eps * eps]
       exits through [q_sq_abs_lt] (with [e := eps]). *)
    apply inr.
    intros eps Heps.
    pose proof (QltT_to_Qlt 0 eps Heps) as HepsQ.
    assert (Hee : 0 < eps * eps).
    { assert (H0 : 0 * eps < eps * eps) by (apply Qmult_lt_compat_r; assumption).
      rewrite Qmult_0_l in H0.
      exact H0. }
    assert (HeeT : QltT 0 (eps * eps)) by (apply Qlt_to_QltT; exact Hee).
    destruct (Heq (eps * eps) HeeT) as [N HN].
    exists N. intros n Hn.
    specialize (HN n Hn).
    apply QltT_to_Qlt in HN.
    apply Qlt_to_QltT.
    (* [HN : Qabs (projT1 real_zero n - projT1 (real_mult x x) n) <
       eps * eps]. *)
    assert (Hdz : projT1 real_zero n - projT1 (real_mult x x) n
                  == 0 - projT1 x n * projT1 x n).
    { setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj x x n)).
      assert (Hz : projT1 real_zero n == 0) by reflexivity.
      rewrite Hz.
      reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (q_abs_congr _ _ Hdz)) in HN.
    assert (Hm : 0 - projT1 x n * projT1 x n == - (projT1 x n * projT1 x n)) by ring.
    rewrite (qeqT_imp_qeq _ _ (q_abs_congr _ _ Hm)) in HN.
    rewrite (Qabs_opp (projT1 x n * projT1 x n)) in HN.
    apply QltT_to_Qlt. apply (q_sq_abs_lt (projT1 x n) eps HepsQ HN).
Qed.

(* ============================================================ *)
(* Part 4. Converse direction: limited LPO implies the wall (the
   decider supplies the pointwise witnesses) *)
(* ============================================================ *)

Theorem lpn_backward : rLPO -> SqWall.
Proof.
  intros Hdec x.
  destruct (Hdec x) as [[c [Hc [N HN]]] | Hzr].
  - (* Gap disjunct: [real_lt 0 (x*x)] with gap constant [c * c]
       (guarding against the shrinking [|x_n| < 1] case). *)
    apply QltT_to_Qlt in Hc.
    apply inl.
    exists (c * c). split.
    + apply Qlt_to_QltT.
      assert (Hcc : 0 * c < c * c) by (apply Qmult_lt_compat_r; assumption).
      rewrite Qmult_0_l in Hcc.
      exact Hcc.
    + exists N. intros n Hn.
      specialize (HN n Hn).
      apply QltT_to_Qlt in HN.
      apply Qlt_to_QltT.
      (* Goal: [c * c < projT1 (x*x) n - projT1 0 n] (the
         difference-order presentation). *)
      assert (Hd : projT1 (real_mult x x) n - projT1 real_zero n
                   == projT1 x n * projT1 x n - 0).
      { setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj x x n)).
        assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz.
        ring. }
      rewrite Hd.
      assert (Hm : projT1 x n * projT1 x n - 0 == projT1 x n * projT1 x n) by ring.
      rewrite Hm.
      apply QltT_to_Qlt. apply q_sq_lt_sq; assumption.
  - (* Vanishing disjunct: [real_eq 0 (x*x)] with [delta] chosen as [1]
       when [1 < eps] and as [eps] otherwise; in-range square pivot
       [q_sq_le_abs] plus the [q_abs_congr] top-face chain. *)
    apply inr.
    intros eps Heps.
    pose proof (QltT_to_Qlt 0 eps Heps) as HepsQ.
    destruct (Qlt_le_dec 1 eps) as [Hbig | Hsmall].
    + (* [delta := 1]: [|x_n| < 1] gives [x_n * x_n <= |x_n| < 1 <= eps]. *)
      assert (H1T : QltT 0 1) by exact q_0_lt_1.
      destruct (Hzr 1 H1T) as [N HN].
      exists N. intros n Hn.
      specialize (HN n Hn).
      apply QltT_to_Qlt in HN.
      apply Qlt_to_QltT.
      (* Goal: [Qabs (projT1 0 n - projT1 (x*x) n) < eps]. *)
      assert (Hdz : projT1 real_zero n - projT1 (real_mult x x) n
                    == 0 - projT1 x n * projT1 x n).
      { setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj x x n)).
        assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz.
        reflexivity. }
      rewrite (qeqT_imp_qeq _ _ (q_abs_congr _ _ Hdz)).
      assert (Hm : 0 - projT1 x n * projT1 x n == - (projT1 x n * projT1 x n)) by ring.
      rewrite (qeqT_imp_qeq _ _ (q_abs_congr _ _ Hm)).
      rewrite (Qabs_opp (projT1 x n * projT1 x n)).
      assert (Hnn : 0 <= projT1 x n * projT1 x n) by (apply QleT'_to_Qle; apply q_sq_nonneg).
      rewrite (Qabs_pos (projT1 x n * projT1 x n) Hnn).
      assert (Hab : Qabs (projT1 x n) <= 1) by (apply Qlt_le_weak; exact HN).
      assert (Hsq : projT1 x n * projT1 x n <= Qabs (projT1 x n))
        by (apply QleT'_to_Qle; apply q_sq_le_abs; exact Hab).
      apply (Qle_lt_trans (projT1 x n * projT1 x n) (Qabs (projT1 x n)) eps Hsq
                          (Qlt_le_trans (Qabs (projT1 x n)) 1 eps HN (Qlt_le_weak 1 eps Hbig))).
    + (* [delta := eps]: [|x_n| < eps <= 1], same chain. *)
      destruct (Hzr eps Heps) as [N HN].
      exists N. intros n Hn.
      specialize (HN n Hn).
      apply QltT_to_Qlt in HN.
      apply Qlt_to_QltT.
      assert (Hdz : projT1 real_zero n - projT1 (real_mult x x) n
                    == 0 - projT1 x n * projT1 x n).
      { setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj x x n)).
        assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz.
        reflexivity. }
      rewrite (qeqT_imp_qeq _ _ (q_abs_congr _ _ Hdz)).
      assert (Hm : 0 - projT1 x n * projT1 x n == - (projT1 x n * projT1 x n)) by ring.
      rewrite (qeqT_imp_qeq _ _ (q_abs_congr _ _ Hm)).
      rewrite (Qabs_opp (projT1 x n * projT1 x n)).
      assert (Hnn : 0 <= projT1 x n * projT1 x n) by (apply QleT'_to_Qle; apply q_sq_nonneg).
      rewrite (Qabs_pos (projT1 x n * projT1 x n) Hnn).
      assert (Hab : Qabs (projT1 x n) <= 1)
        by (apply Qlt_le_weak; apply Qlt_le_trans with eps; [exact HN | exact Hsmall]).
      assert (Hsq : projT1 x n * projT1 x n <= Qabs (projT1 x n))
        by (apply QleT'_to_Qle; apply q_sq_le_abs; exact Hab).
      apply (Qle_lt_trans (projT1 x n * projT1 x n) (Qabs (projT1 x n)) eps Hsq HN).
Qed.

(* ============================================================ *)
(* Part 5. The equivalence statement *)
(* ============================================================ *)

Definition lpn_equivalence : And (SqWall -> rLPO) (rLPO -> SqWall) :=
  (lpn_forward, lpn_backward).

Print Assumptions lpn_forward.
Print Assumptions lpn_backward.
Print Assumptions lpn_equivalence.

Print Assumptions q_0_lt_1.
