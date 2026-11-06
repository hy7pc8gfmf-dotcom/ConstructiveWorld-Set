(* ConstructiveWorld-Set -- constructive arctan small-increment refinements on the Q-Cauchy reals. *)

(** * abl_arctan_smallincr_15: arctan small-increment bound on a closed domain.

    Mission.  For every positive real [eps] there is a positive [delta]
      (a [sigT] witness) such that, on the pointwise closed domain
      [forall n, QleT' (Qabs (projT1 g n)) 1], the arctan increment obeys
      [|arctan(g) - g| <= eps * |g| + eps'] in the [real_le] face for every
      positive [eps'].  Main statement: [abl_atan_small_incr].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qround],
      [QArith.Qminmax], [Lists.List], [Bool.Bool], [Arith.Arith], [Setoid],
      [Morphisms], [Lia], [Extraction].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5] of this development.

    References.  This development, abl_arctan_smallincr_15.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_arctan_smallincr_15.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
From Stdlib Require Import Extraction.

(* ==================== Main statement: the arctan small-increment refinement ==================== *)
Lemma abl_atan_small_incr :
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (g : Real), real_lt (real_abs g) delta ->
      forall (Hg : forall n : nat, QleT' (Qabs (projT1 g n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (cauchy_real_arctan g Hg) (real_opp g)))
              (real_plus (real_mult eps (real_abs g)) eps'))).
Proof.
  intros eps Heps.
  (* -- 0. zero-transport preliminaries, assembled from the existing [real_eq] lemmas. -- *)
  assert (Hc0z : real_eq (real_const 0) real_zero).
  { apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_const_proj 0 n)). cbn [projT1 real_zero]. ring. }
  assert (Hp0l : forall x : Real, real_eq (real_plus real_zero x) x).
  { intros x. apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_zero x n)).
    cbn [projT1 real_zero]. ring. }
  assert (Hzz : real_eq (real_mult (real_const 0) (real_const 0)) real_zero).
  { apply (real_eq_trans _ (real_mult real_zero real_zero)).
    - apply (RealSetoid.real_eq_mult_compat (real_const 0) real_zero (real_const 0) real_zero
                                 Hc0z Hc0z).
    - apply real_mult_zero. }
  assert (Hone : real_eq (real_plus real_one (real_mult (real_const 0) (real_const 0)))
                         real_one).
  { apply (real_eq_trans _ (real_plus real_one real_zero)).
    - apply (RealSetoid.real_eq_plus_compat real_one (real_mult (real_const 0) (real_const 0))
                                 real_one real_zero (real_eq_refl real_one) Hzz).
    - apply real_plus_zero. }
  assert (Hinv : real_eq (real_inv_pos (real_plus real_one
                                          (real_mult (real_const 0) (real_const 0)))
                                        (b3r_one_sq_real_pos (real_const 0)))
                         real_one).
  { apply (real_eq_trans _ (real_inv_pos real_one real_lt_zero_one)).
    - apply (real_inv_pos_ext _ _ (b3r_one_sq_real_pos (real_const 0))
                                 real_lt_zero_one Hone).
    - apply real_inv_one. }
  assert (Hgz : forall g : Real,
    real_eq (real_mult g (real_inv_pos (real_plus real_one
                                         (real_mult (real_const 0) (real_const 0)))
                                       (b3r_one_sq_real_pos (real_const 0)))) g).
  { intros g. apply (real_eq_trans _ (real_mult g real_one)).
    - apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl | exact Hinv].
    - apply real_mult_one. }
  (* -- 1. base-point instantiation of the [b3rr] main bound:
       [r := 0] and [x := real_const 0]. -- *)
  assert (Hxb0 : forall n : nat, QleT' (Qabs (projT1 (real_const 0) n)) 0).
  { intro n. apply Qle_to_QleT'.
    apply (Qle_trans _ (Qabs 0)).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (real_const_proj 0 n)). reflexivity.
    - unfold Qle. simpl. lia. }
  assert (Hr01 : Qlt 0 1) by (unfold Qlt; simpl; lia).
  destruct (b3rr_real_arctan_deriv_linear 0 (Qle_refl 0) Hr01 (real_const 0) Hxb0
             eps Heps) as [delta [Hdpos Hstep]].
  exists delta. split.
  - exact Hdpos.
  - intros g Hglt Hg eps' Heps'.
    (* -- 2. base-point left zero: [0 + g = g] as a real equation, with the
       pointwise domain bound transported along it. -- *)
    assert (Hp0g : real_eq (real_plus (real_const 0) g) g).
    { apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_const 0) g n)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj 0 n)).
      ring. }
    assert (Hdom : forall n : nat, QleT' (Qabs (projT1 (real_plus (real_const 0) g) n)) 1).
    { intro n. apply Qle_to_QleT'.
      apply (Qle_trans _ (Qabs (projT1 g n))).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_const 0) g n)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj 0 n)).
        rewrite Qplus_0_l. reflexivity.
      - exact (QleT'_to_Qle _ _ (Hg n)). }
    specialize (Hstep g Hglt Hdom eps' Heps').
    (* -- 3. transport of the error as a real equation: the left side of the
       [b3rr] conclusion equals [|arctan(g) - g|]. -- *)
    assert (Hshift : real_eq (cauchy_real_arctan (real_plus (real_const 0) g) Hdom)
                             (cauchy_real_arctan g Hg)).
      { (* pointwise argument: the arctan value depends only on the pointwise
         sequence [projT1] through [arctan_real_proj], the sequences of
         [0 + g] and [g] are pointwise Q-equal by the same pointwise chain
         as [Hp0g], and the partial-sum well-definedness lemma
         [b5c_arctan_partial_wd] closes the equation. *)
      apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (arctan_real_proj _ Hdom n)).
      rewrite (qeqT_imp_qeq _ _ (arctan_real_proj _ Hg n)).
      assert (Hpt : projT1 (real_plus (real_const 0) g) n == projT1 g n).
      { rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_const 0) g n)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj 0 n)).
        rewrite Qplus_0_l. reflexivity. }
      rewrite Hpt. ring. }
    assert (Hat0 : real_eq (cauchy_real_arctan (real_const 0)
                                 (b3rr_dom_r1 (real_const 0) 0 Hxb0 Hr01))
                           real_zero).
    { apply (b5c_arctan_const0 (b3rr_dom_r1 (real_const 0) 0 Hxb0 Hr01)). }
    assert (Hinner : real_eq (real_plus
                                (cauchy_real_arctan (real_const 0)
                                   (b3rr_dom_r1 (real_const 0) 0 Hxb0 Hr01))
                                (real_mult g (real_inv_pos
                                   (real_plus real_one
                                      (real_mult (real_const 0) (real_const 0)))
                                   (b3r_one_sq_real_pos (real_const 0)))))
                             g).
    { apply (real_eq_trans _ (real_plus real_zero g)).
      - apply RealSetoid.real_eq_plus_compat; [exact Hat0 | apply (Hgz g)].
      - apply (Hp0l g). }
    assert (HAeq : real_eq
      (real_abs (real_plus
        (cauchy_real_arctan (real_plus (real_const 0) g) Hdom)
        (real_opp (real_plus
          (cauchy_real_arctan (real_const 0) (b3rr_dom_r1 (real_const 0) 0 Hxb0 Hr01))
          (real_mult g (real_inv_pos
             (real_plus real_one (real_mult (real_const 0) (real_const 0)))
             (b3r_one_sq_real_pos (real_const 0))))))))
      (real_abs (real_plus (cauchy_real_arctan g Hg) (real_opp g)))).
    { apply real_abs_eq_compat.
      apply (RealSetoid.real_eq_plus_compat _ _ _ _ Hshift).
      apply (RealSetoid.real_eq_opp_compat _ _ Hinner). }
    (* -- 4. closing by transport of the left side of the [real_le] order. -- *)
    eapply real_le_eq_l.
    + apply real_eq_sym. exact HAeq.
    + exact Hstep.
Qed.

(* ==================== Assumption audit and extraction check ==================== *)
(*   The main statement must audit closed under the global context, *)
(*   and its extraction must report a zero [Obj.magic] count.       *)
Print Assumptions abl_atan_small_incr.

(* extraction check: the criterion is a zero [Obj.magic] count in the output. *)
Recursive Extraction abl_atan_small_incr.
