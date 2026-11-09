(* ConstructiveWorld-Set -- wide minimality convergence of the rational bisection search. *)

(** * abl_mixrational_wide: the wide minimality convergence bound of the rational bisection search, for both hosts.

    Mission.  For rationals [t] [lo] [hi] and a fuel depth [fuel] with
      [QleT' lo t], the search point returned by [rp_bsearch] satisfies the
      wide minimality inequality: [rpw_bsearch_min] states
      [QleT' (rp_bsearch t fuel lo hi) (t + (hi - lo) / rp_qpow (2#1) fuel)],
      and [rpw_bsearch_min_r3] restates it over the second host through fully
      qualified names; both are proved by structural induction on [fuel].

    Dependencies.  Stdlib [QArith.QArith].  Requires [S02_CauchyComplete]
      ([QleT'], [Qle_to_QleT'], [QleT'_to_Qle], [qeq_imp_qle], [qltT_0_2])
      and [UpReqMixRationalProxy_R2] ([rp_bsearch], [rp_qpow],
      [rp_qpow_pos], [rp_qlt_eq_r]) of this development;
      [UpReqMixRationalProxy_R3] is required without [Import] for the
      qualified twin statement.

    References.  This development, abl_mixrational_wide.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_mixrational_wide.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith.
Require Import S02_CauchyComplete.
Require Import UpReqMixRationalProxy_R2.
(* mirror statement over the second host: required without Import, every reference fully qualified, no name collisions. *)
Require UpReqMixRationalProxy_R3.

(* ================= Section 1. wide minimality convergence of bisection search, first host ================= *)
(* wide bound: [rp_bsearch t fuel lo hi <= t + (hi - lo) / 2^fuel] under the
   premise [lo <= t], all carried by the pure [Set] form [QleT'].  the proof
   is structural induction on [fuel]: each branch halves the interval width
   independently of the taken side, so both branches close unconditionally
   through the induction premise.  the field identity [rp_qpow (2#1) f <> 0]
   enters as a side condition, discharged from the positivity statement
   [rp_qpow_pos] via [rp_qlt_eq_r] together with [Qlt_irrefl]. *)
Lemma rpw_bsearch_min : forall (t : Q) (fuel : nat) (lo hi : Q),
  QleT' lo t ->
  QleT' (rp_bsearch t fuel lo hi) (t + (hi - lo) / rp_qpow (2#1) fuel).
Proof.
  intros t fuel.
  induction fuel as [| f IHf]; intros lo hi Htl.
  - (* base case [fuel = 0]: the result is hi, and the reduced claim hi <= t + (hi - lo) / 1 follows from lo <= t. *)
    apply Qle_to_QleT'.
    assert (Hle : Qle lo t) by (apply QleT'_to_Qle; exact Htl).
    assert (Hp : (rp_qpow (2#1) 0 == 1#1)%Q) by reflexivity.
    rewrite Hp.
    assert (Hd : Qle 0 (t - lo)).
    { apply (Qle_trans 0 (lo + -lo) (t - lo)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. field.
      - apply (Qplus_le_compat lo t (-lo) (-lo)); [exact Hle | apply Qle_refl]. }
    apply (Qle_trans hi (hi + (t - lo)) (t + (hi - lo) / (1#1))).
    + apply (Qle_trans hi (hi + 0) (hi + (t - lo))).
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. field.
      * apply (Qplus_le_compat hi hi 0 (t - lo)); [apply Qle_refl | exact Hd].
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. field.
  - (* induction step [fuel = S f]: both branches close through IHf together with the field identities. *)
    apply Qle_to_QleT'.
    simpl.
    destruct (Qle_bool t ((lo + hi) / 2)) eqn:E.
    + (* decision true: the search takes the left branch, r = bsearch t f lo mid, with lo unchanged. *)
      assert (Eqt : (t + (hi - lo) / ((2#1) * rp_qpow (2#1) f)
                  == t + ((lo + hi) / 2 - lo) / rp_qpow (2#1) f)%Q)
        by (field; intro Hzz; apply (Qlt_irrefl 0%Q); apply QltT_to_Qlt;
            exact (rp_qlt_eq_r 0%Q (rp_qpow (2#1) f) 0%Q Hzz
                     (rp_qpow_pos (2#1) f qltT_0_2))).
      rewrite Eqt.
      exact (QleT'_to_Qle _ _ (IHf lo ((lo + hi) / 2) Htl)).
    + (* decision false: the search takes the right branch, r = bsearch t f
         mid hi; from the branch decision E (the development's own [Qle_bool],
         so [t <= mid] fails) one derives [mid <= t] and feeds the right
         instance of IHf.  the development defines [Qle_bool] as the
         reflection of [Qcompare], shadowing the Stdlib lemma of the same
         name, so the Stdlib [Qle_bool_iff] does not apply; the derivation
         goes through the bridge [Qle_to_QleT'] and a boolean equality
         rewrite on the [Id] carrier (the outer [Id] layer has no setoid
         registration, and term-level rewriting of a boolean equation is not
         restricted). *)
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

(* ================= Section 2. mirror statement over the second host ================= *)
(* the qualified [rp_] helpers of [UpReqMixRationalProxy_R3] match their
   first-host counterparts definition for definition; every reference is
   fully qualified. *)
Lemma rpw_bsearch_min_r3 : forall (t : Q) (fuel : nat) (lo hi : Q),
  QleT' lo t ->
  QleT' (UpReqMixRationalProxy_R3.rp_bsearch t fuel lo hi)
        (t + (hi - lo) / UpReqMixRationalProxy_R3.rp_qpow (2#1) fuel).
Proof.
  intros t fuel.
  induction fuel as [| f IHf]; intros lo hi Htl.
  - (* base case [fuel = 0]. *)
    apply Qle_to_QleT'.
    assert (Hle : Qle lo t) by (apply QleT'_to_Qle; exact Htl).
    assert (Hp : (UpReqMixRationalProxy_R3.rp_qpow (2#1) 0 == 1#1)%Q)
      by reflexivity.
    rewrite Hp.
    assert (Hd : Qle 0 (t - lo)).
    { apply (Qle_trans 0 (lo + -lo) (t - lo)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. field.
      - apply (Qplus_le_compat lo t (-lo) (-lo)); [exact Hle | apply Qle_refl]. }
    apply (Qle_trans hi (hi + (t - lo)) (t + (hi - lo) / (1#1))).
    + apply (Qle_trans hi (hi + 0) (hi + (t - lo))).
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. field.
      * apply (Qplus_le_compat hi hi 0 (t - lo)); [apply Qle_refl | exact Hd].
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. field.
  - (* induction step [fuel = S f]. *)
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

(* ================= Section 3. assumption audit of the main exits ================= *)
Print Assumptions rpw_bsearch_min.
Print Assumptions rpw_bsearch_min_r3.
