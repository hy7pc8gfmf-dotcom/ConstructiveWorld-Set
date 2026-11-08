(** * abl_mixrational_wide: standalone wide-form minimality closure for the
      rp_bsearch mixed-rational proxy account of ConstructiveWorld-Set.

    Mission.  Close the rp_bsearch minimality wide form
      [QleT' (rp_bsearch t fuel lo hi) (t + (hi - lo) / rp_qpow (2#1) fuel)]
      under [QleT' lo t], self-authored from the in-host annotations
      (UpReqMixRationalProxy_R2.v:452-455, R3:449-453), AG startup pack two (A2);
      premise direction verified as lo <= t; statement prefix rpw_ has zero
      whole-library grep collisions; form A, zero cascade; closes [rpw_bsearch_min] on the R2 host and its verbatim dual-host counterpart [rpw_bsearch_min_r3].

    Dependencies.  Stdlib [QArith.QArith]; [S02_CauchyComplete] ([QleT'], [QeqT],
      [Qle_to_QleT'], [QleT'_to_Qle], [qeq_imp_qle], [qeq_imp_qeqT], [qltT_0_2],
      [QltT_to_Qlt]); [UpReqMixRationalProxy_R2]; [UpReqMixRationalProxy_R3] (Require without Import).

    References.  UpReqMixRationalProxy_R2.v:452-455 and R3:449-453 (in-host
      annotation snapshots); AG startup pack two (A2); R2:385, R2:130; R2
      header 8-15; gate round 1 red at the first [qeq_imp_qle] site: S02
      carrier drift (world S02:263 [QeqT a b -> QleT' a b] vs Main S02:130
      [a == b -> Qle a b]); six proof-body call sites adapted by the
      S02-native chain [QleT'_to_Qle + qeq_imp_qle + qeq_imp_qeqT] (idiom
      of world S02:752), statement names verbatim, per the merged
      misc-5B/abl-dist carrier-adaptation precedents.

    Constructivity.  All proofs close by Qed, no classical logic; the
      statement face stays in decidable Q form (QleT' = Id(Bool) shape,
      premises in QleT' too); Qle/field side conditions stay Prop-internal;
      induction runs at the Qle layer, closing Qle_to_QleT' once.

    Build.  In-pool rocq compile direct, green on EXIT=0 with no Error and
      artifact magic [436f7121 000160bc]; tail Print Assumptions Closed. *)
From Stdlib Require Import QArith.QArith.
Require Import S02_CauchyComplete.
Require Import UpReqMixRationalProxy_R2.
(* dual-host counterpart for R3 (Require without Import; fully qualified
   names, so zero name clashes) *)
Require UpReqMixRationalProxy_R3.

(* ============ main section: bisection minimality wide form (R2 host) ============ *)
(* r <= t + (hi - lo) / 2^fuel under the premise lo <= t (stated in the
   pure Set form QleT').  proof: structural induction on fuel; each step
   halves the interval width independently of which branch bsearch takes,
   so both branches close unconditionally; the field identity side goal
   rp_qpow (2#1) f <> 0 is bridged in from the positivity lemma
   rp_qpow_pos (change of variables through rp_qlt_eq_r, then discharged
   by Qlt_irrefl), so the closure stays inside the constructive fragment. *)
Lemma rpw_bsearch_min : forall (t : Q) (fuel : nat) (lo hi : Q),
  QleT' lo t ->
  QleT' (rp_bsearch t fuel lo hi) (t + (hi - lo) / rp_qpow (2#1) fuel).
Proof.
  intros t fuel.
  induction fuel as [| f IHf]; intros lo hi Htl.
  - (* base case fuel = 0: r = hi, and the reduced goal
        hi <= t + (hi - lo) / 1 follows from lo <= t *)
    apply Qle_to_QleT'.
    assert (Hle : Qle lo t) by (apply QleT'_to_Qle; exact Htl).
    assert (Hp : (rp_qpow (2#1) 0 == 1#1)%Q) by reflexivity.
    rewrite Hp.
    assert (Hd : Qle 0 (t - lo)).
    { apply (Qle_trans 0 (lo + -lo) (t - lo)).
      - apply QleT'_to_Qle. apply (qeq_imp_qle _ _). apply qeq_imp_qeqT. field.
      - apply (Qplus_le_compat lo t (-lo) (-lo)); [exact Hle | apply Qle_refl]. }
    apply (Qle_trans hi (hi + (t - lo)) (t + (hi - lo) / (1#1))).
    + apply (Qle_trans hi (hi + 0) (hi + (t - lo))).
      * apply QleT'_to_Qle. apply (qeq_imp_qle _ _). apply qeq_imp_qeqT. field.
      * apply (Qplus_le_compat hi hi 0 (t - lo)); [apply Qle_refl | exact Hd].
    + apply QleT'_to_Qle. apply (qeq_imp_qle _ _). apply qeq_imp_qeqT. field.
  - (* inductive step fuel = S f: both branches close by IHf plus the
       field identities *)
    apply Qle_to_QleT'.
    simpl.
    destruct (Qle_bool t ((lo + hi) / 2)) eqn:E.
    + (* test true: the left branch runs, r = bsearch t f lo mid, with
         lo unchanged *)
      assert (Eqt : (t + (hi - lo) / ((2#1) * rp_qpow (2#1) f)
                  == t + ((lo + hi) / 2 - lo) / rp_qpow (2#1) f)%Q)
        by (field; intro Hzz; apply (Qlt_irrefl 0%Q); apply QltT_to_Qlt;
            exact (rp_qlt_eq_r 0%Q (rp_qpow (2#1) f) 0%Q Hzz
                     (rp_qpow_pos (2#1) f qltT_0_2))).
      rewrite Eqt.
      exact (QleT'_to_Qle _ _ (IHf lo ((lo + hi) / 2) Htl)).
    + (* test false: the right branch runs, r = bsearch t f mid hi; from
         the branch decision E (the S02 Qle_bool form: t <= mid fails) we
         get mid <= t, which feeds the right instance of IHf.
         note: S02 defines its own Qle_bool (the Qcompare reflection form),
         which shadows the stdlib definition, and stdlib Qle_bool_iff does
         not match it by name; so the route runs over the S02 bridge
         Qle_to_QleT', and the Bool equation E is rewritten inside the Id
         to collapse it (the Id outer layer carries no setoid registration,
         and term-level replacement by a Bool equation lies outside the
         rewrite ban). *)
      assert (Hmt : Qle ((lo + hi) / 2) t).
      { apply Qlt_le_weak. apply Qnot_le_lt. intro Hq.
        apply (Qle_to_QleT' t ((lo + hi) / 2)) in Hq.
        unfold QleT' in Hq. rewrite E in Hq. inversion Hq. }
      assert (Eqf : (t + (hi - lo) / ((2#1) * rp_qpow (2#1) f)
                  == t + (hi - (lo + hi) / 2) / rp_qpow (2#1) f)%Q)
        by (field; intro Hzz; apply (Qlt_irrefl 0%Q); apply QltT_to_Qlt;
            exact (rp_qlt_eq_r 0%Q (rp_qpow (2#1) f) 0%Q Hzz
                     (rp_qpow_pos (2#1) f qltT_0_2))).
      rewrite Eqf.
      exact (QleT'_to_Qle _ _
               (IHf ((lo + hi) / 2) hi (Qle_to_QleT' _ _ Hmt))).
Qed.

(* ============ R3 dual-host counterpart (verbatim isomorphic port: the
   section 0 and section 3 rp_ toolkit copies of R3 are textually identical
   to those of R2; fully qualified names throughout) ============ *)
Lemma rpw_bsearch_min_r3 : forall (t : Q) (fuel : nat) (lo hi : Q),
  QleT' lo t ->
  QleT' (UpReqMixRationalProxy_R3.rp_bsearch t fuel lo hi)
        (t + (hi - lo) / UpReqMixRationalProxy_R3.rp_qpow (2#1) fuel).
Proof.
  intros t fuel.
  induction fuel as [| f IHf]; intros lo hi Htl.
  - (* base case fuel = 0 *)
    apply Qle_to_QleT'.
    assert (Hle : Qle lo t) by (apply QleT'_to_Qle; exact Htl).
    assert (Hp : (UpReqMixRationalProxy_R3.rp_qpow (2#1) 0 == 1#1)%Q)
      by reflexivity.
    rewrite Hp.
    assert (Hd : Qle 0 (t - lo)).
    { apply (Qle_trans 0 (lo + -lo) (t - lo)).
      - apply QleT'_to_Qle. apply (qeq_imp_qle _ _). apply qeq_imp_qeqT. field.
      - apply (Qplus_le_compat lo t (-lo) (-lo)); [exact Hle | apply Qle_refl]. }
    apply (Qle_trans hi (hi + (t - lo)) (t + (hi - lo) / (1#1))).
    + apply (Qle_trans hi (hi + 0) (hi + (t - lo))).
      * apply QleT'_to_Qle. apply (qeq_imp_qle _ _). apply qeq_imp_qeqT. field.
      * apply (Qplus_le_compat hi hi 0 (t - lo)); [apply Qle_refl | exact Hd].
    + apply QleT'_to_Qle. apply (qeq_imp_qle _ _). apply qeq_imp_qeqT. field.
  - (* inductive step fuel = S f *)
    apply Qle_to_QleT'.
    simpl.
    destruct (Qle_bool t ((lo + hi) / 2)) eqn:E.
    + assert (Eqt : (t + (hi - lo) / ((2#1) * UpReqMixRationalProxy_R3.rp_qpow (2#1) f)
                  == t + ((lo + hi) / 2 - lo)
                     / UpReqMixRationalProxy_R3.rp_qpow (2#1) f)%Q)
        by (field; intro Hzz; apply (Qlt_irrefl 0%Q); apply QltT_to_Qlt;
            exact (UpReqMixRationalProxy_R3.rp_qlt_eq_r 0%Q
                     (UpReqMixRationalProxy_R3.rp_qpow (2#1) f) 0%Q Hzz
                     (UpReqMixRationalProxy_R3.rp_qpow_pos (2#1) f qltT_0_2))).
      rewrite Eqt.
      exact (QleT'_to_Qle _ _ (IHf lo ((lo + hi) / 2) Htl)).
    + assert (Hmt : Qle ((lo + hi) / 2) t).
      { apply Qlt_le_weak. apply Qnot_le_lt. intro Hq.
        apply (Qle_to_QleT' t ((lo + hi) / 2)) in Hq.
        unfold QleT' in Hq. rewrite E in Hq. inversion Hq. }
      assert (Eqf : (t + (hi - lo) / ((2#1) * UpReqMixRationalProxy_R3.rp_qpow (2#1) f)
                  == t + (hi - (lo + hi) / 2)
                     / UpReqMixRationalProxy_R3.rp_qpow (2#1) f)%Q)
        by (field; intro Hzz; apply (Qlt_irrefl 0%Q); apply QltT_to_Qlt;
            exact (UpReqMixRationalProxy_R3.rp_qlt_eq_r 0%Q
                     (UpReqMixRationalProxy_R3.rp_qpow (2#1) f) 0%Q Hzz
                     (UpReqMixRationalProxy_R3.rp_qpow_pos (2#1) f qltT_0_2))).
      rewrite Eqf.
      exact (QleT'_to_Qle _ _
               (IHf ((lo + hi) / 2) hi (Qle_to_QleT' _ _ Hmt))).
Qed.

(* ============ evidence section ============ *)
Print Assumptions rpw_bsearch_min.
Print Assumptions rpw_bsearch_min_r3.
