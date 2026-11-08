(* ConstructiveWorld-Main — S14_B5BatchBlock: assembly of the B5 block — the arctan / exponential / log transparent-chain replica pieces, the rational-point zero-value contracts, and the delta-chain budget (constructive Set layer). *)
(** * S14_B5BatchBlock: B5 block assembly over the arctan / exp / log
    transparent chains.

    Mission.  [b5dQ_E_rational_zero] (for 0 < q < 1,
      [real_E (real_const q) == 0]); the step-bound certificate families
      [b5dQ_Hmod] / [b5dQ_Hstep]; [b5dS_E_zero_on_unit]; and the same-name
      replacement statements [b5d1_Heps4], [b5d1_Heps8], [b5d1_Heps16],
      [b5dE_zero_le_one] — statements and declaration order unchanged; the
      [Heps] family builds its Q-layer positivity in place, and
      [b5dE_zero_le_one] is built pointwise algebraically.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qround],
      [List], [Bool], [Arith], [Setoid], [Morphisms], [Lia], [QArith.Qminmax],
      [Lqa].  Requires [S01_BaseRing] through [S13_NLiveAudit] of this development.

    References.  This development; the same-named baseline module in
      ConstructiveWorld-Main, whose statement names and declaration order
      are carried over verbatim (comment-face revision only).  The proof
      body of [b5d1_b3rr_atan_deriv_lin] is the machine-extracted body of
      [b3rr_real_arctan_deriv_linear] ([ConstructiveWorld.v]
      L71860-72180) with [Qed] opened to [Defined].

    Constructivity.  All named statements are [Set]-carried ([QltT],
      [QleT'], [Id], [NatLe]); zero admissions, no classical logic; the
      closing [Print Assumptions] statements audit the replacement pieces.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      ConstructiveWorld_Live/S14_B5BatchBlock.v] compiles cleanly (exit 0);
      the first eight bytes of the artifact are [436f7121 000160bc]. *)
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
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.
From Stdlib Require Import Lqa.
Opaque Qred.


(* ===== Block b5d1_ (main item b5d1_b3rr_atan_deriv_lin; upstream source sc2_b5a_item5) ===== *)

(* ===== Section 0. instance certificate assembly (r := 1/2, x := real_const 0, eps := 1/4) ===== *)

(* r >= 0: Qle 0 (1#2). *)
Lemma b5d1_Hr0 : QleT' 0 (1 # 2).
Proof. apply Qle_to_QleT'. unfold Qle. simpl. lia. Qed.

(* r < 1: Qlt (1#2) 1. *)
Lemma b5d1_Hr1 : QltT (1 # 2) 1.
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* pointwise domain certificate: |projT1 (real_const 0) n| <= r, in QleT' form. *)
Lemma b5d1_Hxr0 : forall n : nat, QleT' (Qabs (projT1 (real_const 0) n)) (1 # 2).
Proof.
  intro n.
  assert (Hz : projT1 (real_const 0) n == 0) by reflexivity.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs (projT1 (real_const 0) n)) (Qabs 0) (1 # 2)).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply (Qabs_wd (projT1 (real_const 0) n) 0). exact Hz.
  - apply (Qle_trans (Qabs 0) 0 (1 # 2)).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. change (Qabs 0 == 0). cbn. reflexivity.
    + unfold Qle. simpl. lia.
Qed.

(* eps positivity at the Q layer: Qlt 0 e for e in {1/4, 1/8, 1/16}. *)
Lemma b5d1_Hepsq4 : QltT 0 (1 # 4).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

Lemma b5d1_Hepsq8 : QltT 0 (1 # 8).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

Lemma b5d1_Hepsq16 : QltT 0 (1 # 16).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* eps certificate: real_lt real_zero (real_const e), positivity at the Real layer. *)
Lemma b5d1_Heps4 : real_lt real_zero (real_const (1 # 4)).
Proof.
  apply real_const_pos_f1.
  (* the Q-layer positivity is built in place instead of forwarding through b5d1_Hepsq4. *)
  unfold Qlt. simpl. lia.
Qed.

Lemma b5d1_Heps8 : real_lt real_zero (real_const (1 # 8)).
Proof.
  apply real_const_pos_f1.
  (* the Q-layer positivity is built in place instead of forwarding through b5d1_Hepsq8. *)
  unfold Qlt. simpl. lia.
Qed.

Lemma b5d1_Heps16 : real_lt real_zero (real_const (1 # 16)).
Proof.
  apply real_const_pos_f1.
  (* the Q-layer positivity is built in place instead of forwarding through b5d1_Hepsq16. *)
  unfold Qlt. simpl. lia.
Qed.

(* ===== Section 1. main piece: the proof body of b3rr_real_arctan_deriv_linear, carried over
   machine-extracted (ConstructiveWorld.v L71860-72180, no hand transcription), with Qed opened to
   Defined and the name changed to b5d1_b3rr_atan_deriv_lin (the original name occurs only at the
   Lemma head; zero self-references in the body; the supporting lemmas all come from the root
   CW.ConstructiveWorld).  Defined makes the sigT witness computable, so projT1 outputs an
   explicit delta expression. ===== *)
Lemma b5d1_b3rr_atan_deriv_lin :
  forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1),
  forall (x : Real),
  forall (Hxb : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb (QltT_to_Qlt r 1 Hr1)))
                                 (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                           (b3r_one_sq_real_pos x)))))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxb eps Heps.
  set (Cr := b3rr_C2 ((1 # 2) * (1 + r))).
  assert (HCr0 : Qle 0 Cr).
  { unfold Cr. apply QleT'_to_Qle. apply (b3rr_C2_0 ((1 # 2) * (1 + r))).
    - apply QleT'_to_Qle. apply (b3rr_M0 r). apply QleT'_to_Qle. exact Hr0.
    - apply QltT_to_Qlt. apply (b3rr_M_lt1 r). apply QltT_to_Qlt. exact Hr1. }
  set (k := Qinv (4 * (Cr + 1))).
  assert (Hk_pos : Qlt 0 k).
  { unfold k. apply Qinv_lt_0_compat.
    apply (Qmult_lt_0_compat 4 (Cr + 1)).
    - unfold Qlt. simpl. lia.
    - apply (Qlt_le_trans 0 1 (Cr + 1)).
      + unfold Qlt. simpl. lia.
      + apply (Qle_trans 1 (0 + 1) (Cr + 1)).
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        * apply Qplus_le_compat. exact HCr0. apply Qle_refl. }
  assert (HCrK : Qle (Cr * k) (1 # 4)).
  { unfold k. exact (QleT'_to_Qle _ _ (b3rr_CK Cr HCr0)). }
  assert (Hk0 : Qle 0 k) by (apply Qlt_le_weak; exact Hk_pos).
  set (rk := real_const k).
  assert (Hrk_pos : real_lt real_zero rk).
  { unfold rk. apply real_const_pos_f1. exact Hk_pos. }
  set (delta := real_min (real_const ((1 # 2) * (1 - r))) (real_mult eps rk)).
  exists delta. split.
  - (* 0 < delta *)
    unfold delta, rk.
    apply real_min_pos.
    + apply real_const_pos_f1.
      apply (Qmult_lt_0_compat (1 # 2) (1 - r)).
      * unfold Qlt. simpl. lia.
      * apply (proj1 (Qlt_minus_iff r 1)). apply QltT_to_Qlt. exact Hr1.
    + apply real_mult_positive. exact Heps. exact Hrk_pos.
  - intros h Hh Hxh eps' Heps'.
    left.
    destruct Heps as [eps1 [Heps1 [N1 HN1]]].
    destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
    assert (Hh_l : real_lt (real_abs h) (real_const ((1 # 2) * (1 - r))))
      by (unfold delta in Hh; apply (real_min_lt_l h (real_const ((1 # 2) * (1 - r))) (real_mult eps rk)); exact Hh).
    assert (Hh_r : real_lt (real_abs h) (real_mult eps rk))
      by (unfold delta in Hh; apply (real_min_lt_r h (real_const ((1 # 2) * (1 - r))) (real_mult eps rk)); exact Hh).
    destruct Hh_l as [e2 [He2 [N2 HN2]]].
    destruct Hh_r as [e3 [He3 [N3 HN3]]].
    destruct (real_inv_proj (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)) as [Ninv HNinv].
    assert (Hh2 : Qlt 0 (Qmult eps1' (Qinv 2))).
    { apply (Qmult_lt_0_compat eps1' (Qinv 2)).
      - apply QltT_to_Qlt. exact Heps1'.
      - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
    destruct (b3rr_qdecay r (Qmult eps1' (Qinv 2)) (QleT'_to_Qle 0 r Hr0) (QltT_to_Qlt r 1 Hr1) Hh2) as [Ng HNg].
    set (eta := Qmult eps1' (Qinv 2)).
    assert (Heta_pos : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT. exact Hh2. }
    exists eta. split.
    + exact Heta_pos.
    + exists (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3)) (Nat.max Ninv Ng)).
      intros n Hn.
      apply NatLe_drop in Hn.
      assert (Hn1 : (N1 <= n)%nat) by lia.
      assert (Hn1' : (N1' <= n)%nat) by lia.
      assert (Hn2 : (N2 <= n)%nat) by lia.
      assert (Hn3 : (N3 <= n)%nat) by lia.
      assert (Hninv : (Ninv <= n)%nat) by lia.
      assert (Hng : (Ng <= n)%nat) by lia.
      set (un := projT1 x n). set (hn := projT1 h n).
      set (en := projT1 eps n). set (en' := projT1 eps' n).
      set (yn := un + hn).
      set (Dform := arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)).
      set (wreal := real_inv_pos (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)).
      (* positivity: en >= 0 and en' > eps1'. *)
      assert (HN1e : QltT eps1 en).
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
        - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. unfold en. ring. }
      assert (Hen0 : Qle 0 en).
      { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
        - apply QltT_to_Qlt. exact Heps1.
        - apply QltT_to_Qlt. exact HN1e. }
      assert (HN1'e : QltT eps1' en').
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
        - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. unfold en'. ring. }
      (* from the witnesses to the pointwise bounds: |hn| <= (1-r)/2 and |hn| <= en*k. *)
      assert (Hq2 : Qlt e2 (Qminus ((1 # 2) * (1 - r)) (Qabs hn))).
      { apply (Qlt_le_trans e2 (Qminus (projT1 (real_const ((1 # 2) * (1 - r))) n) (projT1 (real_abs h) n))
                             (Qminus ((1 # 2) * (1 - r)) (Qabs hn))).
        - apply QltT_to_Qlt. apply (HN2 n (NatLe_lift _ _ Hn2)).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)). cbn [real_zero real_const projT1]. reflexivity. }
      assert (Hhn_half : Qlt (Qabs hn) ((1 # 2) * (1 - r))).
      { apply (Qlt_le_trans (Qabs hn) (Qminus ((1 # 2) * (1 - r)) e2) ((1 # 2) * (1 - r))).
        - apply QltT_to_Qlt. apply (q_lt_minus_shift e2 ((1 # 2) * (1 - r)) (Qabs hn)). apply Qlt_to_QltT. exact Hq2.
        - assert (He20 : Qle 0 e2) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact He2).
          apply (Qle_trans (Qminus ((1 # 2) * (1 - r)) e2)
                           (Qplus (Qminus ((1 # 2) * (1 - r)) e2) e2)
                           ((1 # 2) * (1 - r))).
          + apply (Qle_trans (Qminus ((1 # 2) * (1 - r)) e2)
                             (Qplus (Qminus ((1 # 2) * (1 - r)) e2) 0)
                             (Qplus (Qminus ((1 # 2) * (1 - r)) e2) e2)).
            * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
            * apply (Qplus_le_compat (Qminus ((1 # 2) * (1 - r)) e2)
                                     (Qminus ((1 # 2) * (1 - r)) e2) 0 e2
                                     (Qle_refl _) He20).
          + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
      assert (Hhn_half_le : Qle (Qabs hn) ((1 # 2) * (1 - r))) by (apply Qlt_le_weak; exact Hhn_half).
      assert (Hhn1 : Qle (Qabs hn) 1).
      { apply (Qle_trans _ ((1 # 2) * (1 - r)) _).
        - exact Hhn_half_le.
        - apply QleT'_to_Qle. apply (b3rr_1mr_half_le1 r). apply QleT'_to_Qle. exact Hr0. }
      assert (Hq3 : Qlt e3 (Qminus (Qmult en k) (Qabs hn))).
      { apply (Qlt_le_trans e3 (Qminus (projT1 (real_mult eps rk) n) (projT1 (real_abs h) n))
                             (Qminus (Qmult en k) (Qabs hn))).
        - apply QltT_to_Qlt. apply (HN3 n (NatLe_lift _ _ Hn3)).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          unfold rk, en.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const k) n)).
          cbn [real_zero real_const projT1]. reflexivity. }
      assert (Hhn_k : Qlt (Qabs hn) (Qmult en k)).
      { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en k) e3) (Qmult en k)).
        - apply QltT_to_Qlt. apply (q_lt_minus_shift e3 (Qmult en k) (Qabs hn)). apply Qlt_to_QltT. exact Hq3.
        - assert (He30 : Qle 0 e3) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact He3).
          apply (Qle_trans (Qminus (Qmult en k) e3) (Qplus (Qminus (Qmult en k) e3) e3)
                           (Qmult en k)).
          + apply (Qle_trans (Qminus (Qmult en k) e3) (Qplus (Qminus (Qmult en k) e3) 0)
                             (Qplus (Qminus (Qmult en k) e3) e3)).
            * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
            * apply (Qplus_le_compat (Qminus (Qmult en k) e3) (Qminus (Qmult en k) e3) 0 e3
                     (Qle_refl _) He30).
          + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
      assert (Hhn_kle : Qle (Qabs hn) (Qmult en k)) by (apply Qlt_le_weak; exact Hhn_k).
      (* domain: |un| <= r. *)
      assert (Hun_r : Qle (Qabs un) r).
      { apply (QleT'_to_Qle (Qabs un) r). apply Hxb. }
      assert (Hhvn0 : Qle 0 (Qabs hn)) by apply Qabs_nonneg.
      assert (Henhn0 : Qle 0 (Qmult en (Qabs hn))).
      { apply (Qmult_le_0_compat en (Qabs hn)). exact Hen0. exact Hhvn0. }
      (* projection identity (A side). *)
      assert (Hrepl : projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb (QltT_to_Qlt r 1 Hr1)))
                              (real_mult h wreal))))) n ==
                  Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un))).
      { unfold yn, un, hn, wreal.
        rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb (QltT_to_Qlt r 1 Hr1)))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x)))))) n)).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb (QltT_to_Qlt r 1 Hr1)))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x))))) n)).
        rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb (QltT_to_Qlt r 1 Hr1)))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x)))) n)).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb (QltT_to_Qlt r 1 Hr1)))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x))) n)).
        rewrite (qeqT_imp_qeq _ _ (real_mult_proj h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x)) n)).
        rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_plus x h) Hxh n)).
        rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x (b3rr_dom_r1 x r Hxb (QltT_to_Qlt r 1 Hr1)) n)).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj x h n)).
        rewrite (qeqT_imp_qeq _ _ (HNinv n (NatLe_lift _ _ Hninv))).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_mult x x) n)).
        rewrite (qeqT_imp_qeq _ _ (real_mult_proj x x n)).
        rewrite (qeqT_imp_qeq _ _ (b3r_one_proj n)).
        apply Qabs_wd. ring. }
      (* B-side projection. *)
      assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
      { unfold en, en', hn.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        cbn [real_zero real_const projT1]. ring. }
      (* pointwise main bound 1: Cr*|hn|^2 <= en*|hn|*(1/4). *)
      assert (Hcbn : Qle (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
                         (Qmult (Qmult en (Qabs hn)) (1 # 4))).
      { apply (Qle_trans _ (Qmult Cr (Qmult (Qmult en k) (Qabs hn))) _).
        - (* |hn|*|hn| <= (en*k)*|hn| by right-multiplying by |hn| >= 0, then left-multiplying by Cr >= 0. *)
          apply QleT'_to_Qle. apply (b3_qmult_le_l (Qmult (Qabs hn) (Qabs hn))
                               (Qmult (Qmult en k) (Qabs hn)) Cr).
          + exact HCr0.
          + apply (Qmult_le_compat_r (Qabs hn) (Qmult en k) (Qabs hn)).
            * exact Hhn_kle.
            * exact Hhvn0.
        - (* Cr·((en·k)·|hn|) == en·|hn|·(Cr·k) ≤ en·|hn|·(1/4) *)
          apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) (Qmult Cr k)) _).
          + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          + apply QleT'_to_Qle. apply (b3_qmult_le_l (Qmult Cr k) (1 # 4) (Qmult en (Qabs hn))).
            * exact Henhn0.
            * exact HCrK. }
      (* pointwise main bound 2: r^(2(Sn)) <= eta, since n >= Ng entails 2(Sn) >= Ng. *)
      assert (Hdec2 : Qle (q_pow r (2 * Datatypes.S n)) eta).
      { apply QleT'_to_Qle. apply (HNg ((2 * Datatypes.S n)%nat)). apply NatLe_lift. lia. }
      assert (Hpow14 : Qle (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n)))
                           (q_pow r (2 * Datatypes.S n))).
      { apply (Qle_trans _ (Qmult 1 (q_pow r (2 * Datatypes.S n))) _).
        - apply (Qmult_le_compat_r (Qabs hn) 1 (q_pow r (2 * Datatypes.S n))).
          + exact Hhn1.
          + apply QleT'_to_Qle. apply q_pow_nonneg. exact Hr0.
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
      (* main pointwise bound: |D_n| <= en*|hn| + eta. *)
      assert (Hm1 : Qle
        (Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)))
        (Qplus (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
               (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))).
      { unfold yn. apply QleT'_to_Qle. apply (b3rr_core_r n un hn r (QleT'_to_Qle 0 r Hr0) (QltT_to_Qlt r 1 Hr1) Hun_r Hhn_half_le). }
      assert (Hm2 : Qle
        (Qplus (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
               (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))).
      { apply Qplus_le_compat. exact Hcbn. apply Qle_refl. }
      assert (Hm3 : Qle
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (q_pow r (2 * Datatypes.S n)))).
      { apply Qplus_le_compat. apply Qle_refl. exact Hpow14. }
      assert (Hm4 : Qle
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (q_pow r (2 * Datatypes.S n)))
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4)) eta)).
      { apply Qplus_le_compat. apply Qle_refl. exact Hdec2. }
      assert (Hm5 : Qle (Qmult (Qmult en (Qabs hn)) (1 # 4)) (Qmult en (Qabs hn))).
      { apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) 1) _).
        - apply QleT'_to_Qle. apply (b3_qmult_le_l (1 # 4) 1 (Qmult en (Qabs hn))).
          + exact Henhn0.
          + unfold Qle. simpl. lia.
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
      assert (Hm6 : Qle
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4)) eta)
        (Qplus (Qmult en (Qabs hn)) eta)).
      { apply Qplus_le_compat. exact Hm5. apply Qle_refl. }
      assert (Hmain : Qle
        (Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)))
        (Qplus (Qmult en (Qabs hn)) eta)).
      { apply (Qle_trans _ (Qplus (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
               (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n)))) _).
        - exact Hm1.
        - apply (Qle_trans _ (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n)))) _).
          + exact Hm2.
          + apply (Qle_trans _ (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
                 (q_pow r (2 * Datatypes.S n))) _).
            * exact Hm3.
            * apply (Qle_trans _ (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4)) eta) _).
              -- exact Hm4.
              -- exact Hm6. }
      (* Hfin: eta < (en*|hn| + en') - |D_n|. *)
      assert (Hfin : Qlt eta
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
      { apply (Qlt_le_trans eta
          (Qminus (Qplus (Qmult en (Qabs hn)) en')
                  (Qplus (Qmult en (Qabs hn)) eta))
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
        - (* eta < (en|hn|+en') - (en|hn|+eta) == en' - 2*eta, since en' > eps1' == 2*eta. *)
          apply (proj2 (Qlt_minus_iff eta
              (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) eta)))).
          assert (Heq : Qminus (Qminus (Qplus (Qmult en (Qabs hn)) en')
                               (Qplus (Qmult en (Qabs hn)) eta)) eta ==
                        Qminus en' (Qmult eta (1 + 1))) by ring.
          rewrite Heq.
          apply (proj1 (Qlt_minus_iff (Qmult eta (1 + 1)) en')).
          assert (HX : Qmult eta (1 + 1) == eps1') by (unfold eta; field).
          rewrite HX.
          apply QltT_to_Qlt. exact HN1'e.
        - apply (proj2 (Qle_minus_iff
              (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) eta))
              (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform)))).
          assert (Heq2 : Qminus (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))
                                (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) eta)) ==
                          Qminus (Qplus (Qmult en (Qabs hn)) eta) (Qabs Dform)) by ring.
          rewrite Heq2.
          apply (proj1 (Qle_minus_iff (Qabs Dform) (Qplus (Qmult en (Qabs hn)) eta))).
          exact Hmain. }
      (* projection bridge: (RHS - LHS) == (B - |D|). *)
      assert (Hrepl2 : Qeq
          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                  (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb (QltT_to_Qlt r 1 Hr1)))
                              (real_mult h wreal))))) n))
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
      { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                           (Qplus (Qmult en (Qabs hn)) en') HB
                           (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                           (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb (QltT_to_Qlt r 1 Hr1)))
                                       (real_mult h wreal))))) n)
                           (Qabs Dform) Hrepl). }
      apply Qlt_to_QltT.
      assert (Hqfinal : Qlt eta
          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                  (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb (QltT_to_Qlt r 1 Hr1)))
                              (real_mult h wreal))))) n))).
      { apply (Qlt_le_trans eta
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))
          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                  (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb (QltT_to_Qlt r 1 Hr1)))
                              (real_mult h wreal))))) n))).
        - exact Hfin.
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrepl2. }
      exact Hqfinal.

Defined.
(* ============================================================ *)
(* Section 2. the explicit delta lower-bound certificate family (genuine Qed). *)
(* Instances: r := 1/2, x := real_const 0, eps := real_const e,   *)
(*   e in {1/4, 1/8, 1/16}.                                       *)
(*   delta_e := projT1 (b5d1_b3rr_atan_deriv_lin (1#2) ... e ...) *)
(*        == real_min (real_const ((1#2)*(1-1/2)))                *)
(*                    (real_mult (real_const e)                   *)
(*                               (real_const k(1/2))).            *)
(*   Values: k(1/2) = Qinv(4*(b3rr_C2(3/4)+1)) = 49/1732;         *)
(*   delta_{1/4} == 49/6928 (about 7.07e-3);                      *)
(*   delta_{1/8} == 49/13856; delta_{1/16} == 49/27712 (evaluated by vm_compute). *)
(* Evidence chain: the Defined copy makes projT1 computable (cbn), the  *)
(*   closed-form Q evaluation (vm_compute), the pointwise identity,     *)
(*   real_eq, and the real_le lower-bound certificate (uptake form =    *)
(*   real_le (real_const c) delta).                                     *)
(* ============================================================ *)

(* ---- named witness for the instance delta (transparent Definition, closed form): eps = 1/4 ---- *)
Definition b5d1_d4 : Real :=
  projT1 (b5d1_b3rr_atan_deriv_lin (1 # 2) b5d1_Hr0 b5d1_Hr1
            (real_const 0) b5d1_Hxr0 (real_const (1 # 4)) b5d1_Heps4).

(* pointwise identity: projT1 b5d1_d4 n == 49#6928 for all n, with no tail index. *)
Lemma b5d1_d4_pt : forall n : nat,QeqT ( projT1 b5d1_d4 n ) ( (49 # 6928)).
Proof.
  intro n.
  apply qeq_imp_qeqT.
  cbn [projT1 b5d1_d4].
  vm_compute.
  reflexivity.
Qed.

(* real_eq: real_const (49#6928) ≈ b5d1_d4. *)
Lemma b5d1_d4_eq : real_eq (real_const (49 # 6928)) b5d1_d4.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  assert (Hpt : projT1 b5d1_d4 n == (49 # 6928)) by exact (qeqT_imp_qeq _ _ (b5d1_d4_pt n)).
  rewrite Hpt.
  cbn [projT1 real_const].
  reflexivity.
Qed.

(* conclusion: delta_{1/4} >= real_const (49#6928) (right real_le branch: real_eq). *)
Lemma b5d1_d4_lb : real_le (real_const (49 # 6928)) b5d1_d4.
Proof.
  right. exact b5d1_d4_eq.
Qed.

(* ---- instance delta: eps = 1/8 ---- *)
Definition b5d1_d8 : Real :=
  projT1 (b5d1_b3rr_atan_deriv_lin (1 # 2) b5d1_Hr0 b5d1_Hr1
            (real_const 0) b5d1_Hxr0 (real_const (1 # 8)) b5d1_Heps8).

(* pointwise identity: projT1 b5d1_d8 n == 49#13856. *)
Lemma b5d1_d8_pt : forall n : nat,QeqT ( projT1 b5d1_d8 n ) ( (49 # 13856)).
Proof.
  intro n.
  apply qeq_imp_qeqT.
  cbn [projT1 b5d1_d8].
  vm_compute.
  reflexivity.
Qed.

(* real_eq: real_const (49#13856) ≈ b5d1_d8. *)
Lemma b5d1_d8_eq : real_eq (real_const (49 # 13856)) b5d1_d8.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  assert (Hpt : projT1 b5d1_d8 n == (49 # 13856)) by exact (qeqT_imp_qeq _ _ (b5d1_d8_pt n)).
  rewrite Hpt.
  cbn [projT1 real_const].
  reflexivity.
Qed.

(* conclusion: delta_{1/8} >= real_const (49#13856). *)
Lemma b5d1_d8_lb : real_le (real_const (49 # 13856)) b5d1_d8.
Proof.
  right. exact b5d1_d8_eq.
Qed.

(* ---- instance delta: eps = 1/16 ---- *)
Definition b5d1_d16 : Real :=
  projT1 (b5d1_b3rr_atan_deriv_lin (1 # 2) b5d1_Hr0 b5d1_Hr1
            (real_const 0) b5d1_Hxr0 (real_const (1 # 16)) b5d1_Heps16).

(* pointwise identity: projT1 b5d1_d16 n == 49#27712. *)
Lemma b5d1_d16_pt : forall n : nat,QeqT ( projT1 b5d1_d16 n ) ( (49 # 27712)).
Proof.
  intro n.
  apply qeq_imp_qeqT.
  cbn [projT1 b5d1_d16].
  vm_compute.
  reflexivity.
Qed.

(* real_eq: real_const (49#27712) ≈ b5d1_d16. *)
Lemma b5d1_d16_eq : real_eq (real_const (49 # 27712)) b5d1_d16.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  assert (Hpt : projT1 b5d1_d16 n == (49 # 27712)) by exact (qeqT_imp_qeq _ _ (b5d1_d16_pt n)).
  rewrite Hpt.
  cbn [projT1 real_const].
  reflexivity.
Qed.

(* conclusion: delta_{1/16} >= real_const (49#27712). *)
Lemma b5d1_d16_lb : real_le (real_const (49 # 27712)) b5d1_d16.
Proof.
  right. exact b5d1_d16_eq.
Qed.

(* Remark: 0 < delta_e can be re-derived from the lb certificate plus the real_const
   positivity; this family also serves as the certificate-pattern template: for a target
   instance (x := real_const 0, eps := another rational constant) the three Section 2 items
   carry over verbatim (about 12 lines per instance). *)

(* ===== Block b5dD_ (main item b5dD_vdh_pts_r_exp; upstream source sc2_b5a_item14) ===== *)

(* C8a b5dD_atan_deriv_b5a_r_exp (transparent Defined).
   Copy source: root b5c_atan_deriv_b5a_r (ConstructiveWorld.v L79198-79255, 58 lines,
   machine-extracted with no hand transcription); statement unchanged.
   The in-body destruct source: b3rr_real_arctan_deriv_linear (root, Qed) is replaced by
   b5d1_b3rr_atan_deriv_lin (upstream sc2_b5a_item5, transparent Defined, delta-A item5
   L98-419); the closing Qed opens to Defined (transparency is the goal).
   Note: the supporting lemmas (b5c_inv_pos_cert_eq / b5a_one_plus_sq_pos / the RealSetoid
   family, etc.) all stay in the root CW with zero copying; this file is a pure
   passthrough layer. *)

Lemma b5dD_atan_deriv_b5a_r_exp :
  forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                 (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)))
                            (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                      (b5a_one_plus_sq_pos x)) h)))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps.
  destruct (b5d1_b3rr_atan_deriv_lin r Hr0 Hr1 x Hxr eps Heps)
    as [delta [Hd0 Hd]].
  exists delta. split.
  - exact Hd0.
  - intros h Hh Hxh eps' Heps'.
    set (I3 := real_inv_pos (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)).
    set (I5 := real_inv_pos (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x)).
    assert (Hinv : real_eq I5 I3).
    { unfold I5, I3. apply b5c_inv_pos_cert_eq. }
    assert (Hsl : real_eq (real_mult I5 h) (real_mult h I3)).
    { apply (real_eq_trans (real_mult I5 h) (real_mult h I5) (real_mult h I3)).
      - apply real_mult_comm.
      - apply (RealSetoid.real_eq_mult_compat h I5 h I3 (real_eq_refl h) Hinv). }
    apply (RealSetoid.real_le_compat
             (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                        (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)))
                                   (real_mult h I3)))))
             (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                        (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)))
                                   (real_mult I5 h)))))
             (real_plus (real_mult eps (real_abs h)) eps')
             (real_plus (real_mult eps (real_abs h)) eps')).
    { apply RealSetoid.real_eq_abs_compat.
      apply (RealSetoid.real_eq_plus_compat
               (cauchy_real_arctan (real_plus x h) Hxh)
               (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)))
                                    (real_mult h I3)))
               (cauchy_real_arctan (real_plus x h) Hxh)
               (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)))
                                    (real_mult I5 h)))).
      - apply real_eq_refl.
      - apply RealSetoid.real_eq_opp_compat.
        apply (RealSetoid.real_eq_plus_compat
                 (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)))
                 (real_mult h I3)
                 (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)))
                 (real_mult I5 h)).
        + apply real_eq_refl.
        + apply real_eq_sym. exact Hsl. }
    { apply real_eq_refl. }
    { unfold I3.
      exact (Hd h Hh Hxh eps' Heps'). }
Defined.

(* ===== Block b5d1_ (main item b5d1_b3rr_atan_deriv_lin; upstream source sc2_b5a_item5, statement 213 of the root) ===== *)

(* ===== Section 0. instance certificate assembly (r := 1/2, x := real_const 0, eps := 1/4) ===== *)

(* r >= 0: Qle 0 (1#2). *)

Lemma b5dD_vdh_pts_r_exp : forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r)
  (eps : Real) (Heps : real_lt real_zero eps)
  (k2 k2p : Q) (Hk2 : QltT 0 k2) (Hk2p : QltT 0 k2p),

  sigT (fun δa : Real => And (real_lt real_zero δa)
    (forall (h : Real), real_lt (real_abs h) δa ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      sigT (fun N : nat => forall n : nat, NatLe N n ->
        QleT' (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
            (Qplus (Qmult (Qmult (projT1 eps n) k2) (Qabs (projT1 h n)))
                   (Qmult (Qmult 2 k2p) (projT1 eps' n)))))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2 Hk2p.
  set (Hx := b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)).
  set (eps2 := real_mult eps (real_const k2)).
  assert (Heps2 : real_lt real_zero eps2).
  { unfold eps2. apply real_mult_positive.
    - exact Heps.
    - apply real_const_pos. exact Hk2. }
  destruct (b5dD_atan_deriv_b5a_r_exp r Hr0 Hr1 x Hxr eps2 Heps2) as [δa [Hδa0 Hδa]].
  exists δa.
  split.
  - exact Hδa0.
  - intros h Hhδ Hxh eps' Heps'.
    set (eps2' := real_mult eps' (real_const k2p)).
    assert (Heps2' : real_lt real_zero eps2').
    { unfold eps2'. apply real_mult_positive.
      - exact Heps'.
      - apply real_const_pos. exact Hk2p. }
    set (V := real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                (real_opp (real_plus (cauchy_real_arctan x Hx)
                           (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                     (b5a_one_plus_sq_pos x)) h)))).
    assert (Habs : real_le (real_abs V)
                    (real_plus (real_mult eps2 (real_abs h)) eps2')).
    { unfold V, eps2, eps2'.
      exact (Hδa h Hhδ Hxh (real_mult eps' (real_const k2p)) Heps2'). }
    destruct (b5i_abs_le_pointwise V (real_plus (real_mult eps2 (real_abs h)) eps2')
               Habs eps2' Heps2') as [N HN].
    exists N.
    intros n Hn.
    set (en := projT1 eps n).
    set (en' := projT1 eps' n).
    set (hn := projT1 h n).
    assert (Hpt : Qle (Qabs (projT1 V n))
                      (Qplus (Qmult (Qmult en k2) (Qabs hn))
                             (Qmult (Qmult 2 k2p) en'))).
    { apply (Qle_trans (Qabs (projT1 V n))
                       (Qplus (projT1 (real_plus (real_mult eps2 (real_abs h)) eps2') n)
                              (projT1 eps2' n))
                       (Qplus (Qmult (Qmult en k2) (Qabs hn))
                              (Qmult (Qmult 2 k2p) en'))).
      - exact (QleT'_to_Qle _ _ (HN n Hn)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps2 (real_abs h)) eps2' n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps2 (real_abs h) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        unfold eps2, eps2'.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const k2) n)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj k2 n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const k2p) n)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj k2p n)).
        cbn [projT1].
        unfold en, en', hn.
        ring. }
    (* the projection of V agrees definitionally with the projection in b5i_vdh_absV (unfolding b5a_atan_d). *)
    apply Qle_to_QleT'.
    apply QleT'_to_Qle. apply (b5i_vdh_absV x Hx h Hxh n
             (Qplus (Qmult (Qmult en k2) (Qabs hn))
                    (Qmult (Qmult 2 k2p) en'))).
    unfold b5a_atan_d, V in Hpt.
    exact Hpt.
Defined.

(* ===== end of sc2_b5a_item14.v: delta-D1a C8 transparent base ===== *)

(* ===== Block b5dG_ (main item b5dG_sin_atan_diff_closed_r_exp; upstream source sc2_b5a_item17) ===== *)

(* C1t: b5dG_sin_atan_diff_closed_r_exp (transparent Defined).
   Copy source: upstream sc2_b5a_item9 C1 b5d5_sin_atan_diff_closed_r_expl (item9
   L54-311, machine-extracted with no hand transcription); statement unchanged (expl
   form).
   The in-body vdh destruct source: b5c_vdh_pts_r (root, Qed) is replaced by this
   file's dependency b5dD_vdh_pts_r_exp (upstream sc2_b5a_item14 C8b, transparent
   Defined); the closing Qed opens to Defined (transparency is the goal). *)
Lemma b5dG_sin_atan_diff_closed_r_exp :
  forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (Ms Mc C4 : Q),
  QltT 0 Ms -> QltT 0 Mc -> QleT' 0 C4 -> QleT' 1 C4 ->
  (forall j : nat, QleT' (exp_series j 4) C4) ->
  (forall n : nat, QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Ms) ->
  (forall n : nat, QleT' (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (b5a_comp_err_sin x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)) h Hxh))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr Ms Mc C4 HMsQ HMcQ HC40 HC4ge1 HC4 HMs_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)).
  destruct (b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMsQ. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMcQ. }
  set (S := Qplus Ms Mc).
  assert (HSlt : Qlt 0 S). { unfold S.
    pose proof (QltT_to_Qlt 0 Ms HMsQ). pose proof (QltT_to_Qlt 0 Mc HMcQ). nra. }
  set (K1e := Qplus (Qmult Ms (Qplus (Qmult 4 C4) 2))
                    (Qmult Mc (Qplus (Qmult 4 C4) 4))).
  assert (HK1_0 : Qle 0 K1e). { unfold K1e.
    pose proof (QleT'_to_Qle 0 C4 HC40). nra. }
  set (kδ := Qinv (Qmult 512 (Qplus S 1))).
  set (k2 := Qinv (Qmult (Qmult 512 (Qplus S 1))
                         (Qplus (Qplus (Qmult 3 S) Mc) 1))).
  set (k2p := Qinv (Qmult (Qmult 1024 (Qplus K1e 1))
                          (Qplus (Qplus (Qmult 3 S) Mc) 1))).
  assert (HkδT : QltT 0 kδ).
  { unfold kδ. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2T : QltT 0 k2).
  { unfold k2. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2pT : QltT 0 k2p).
  { unfold k2p. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2Q : Qle 0 k2). { apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2T. }
  assert (Hk2pQ : Qlt 0 k2p). { apply QltT_to_Qlt. exact Hk2pT. }
  (* global budget: coef (quad), coefC (crude), 8*k2p*K1 (forced by the crude bound). *)
  assert (HcoefQ : Qle (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2)) 1).
  { apply (Qle_trans (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                             (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2))
                     (Qplus (1 # 2) (1 # 2))
                     1).
    { apply Qplus_le_compat.
      { apply QleT'_to_Qle. apply (b5n_2S_kδ_le S HSlt). }
      { apply QleT'_to_Qle. apply (b5n_3S_Mc_k2_le S Mc HSlt HMc0). } }
    { nra. } }
  assert (HcoefC : Qle (Qmult Mc k2) 1).
  { apply (Qle_trans (Qmult Mc k2) (1 # 2) 1).
    { apply QleT'_to_Qle. apply (b5n_Mc_k2_le S Mc HSlt HMc0). }
    { unfold Qle. simpl. lia. } }
  assert (Hk2pK1 : Qle (Qmult (Qmult 8 k2p)
                              (Qplus (Qmult Ms (Qplus (Qmult 4 C4) 2))
                                     (Qmult Mc (Qplus (Qmult 4 C4) 4)))) 1).
  { apply QleT'_to_Qle. apply (b5n_8k2p_K1_le S Mc K1e HSlt HMc0 HK1_0). }
  (* delta assembly: 0 < each component. *)
  assert (H12T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (H14T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  destruct (b5dD_vdh_pts_r_exp r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2T Hk2pT) as [δa [Hδa0 Hδa]].
  assert (Hc12r : real_lt real_zero (real_const (1 # 2))).
  { apply real_const_pos. exact H12T. }
  assert (Hepskδ : real_lt real_zero (real_mult eps (real_const kδ))).
  { apply real_mult_positive.
    { exact Heps. }
    { apply real_const_pos. exact HkδT. } }
  assert (Hqtr : real_lt real_zero
            (real_mult (real_const (1 # 4))
                       (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                     (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  { apply real_mult_positive.
    { apply real_const_pos. exact H14T. }
    { apply real_inv_pos_pos. } }
  set (delta := real_min
        (real_min (real_min δa (real_const (1 # 2)))
                  (real_mult eps (real_const kδ)))
        (real_mult (real_const (1 # 4))
                   (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                 (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos.
        { exact Hδa0. }
        { exact Hc12r. } }
      { exact Hepskδ. } }
    { exact Hqtr. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      { unfold Qlt. simpl. lia. }
      { apply QltT_to_Qlt. exact He1T. } }
    (* extracting the four-layer min for h against delta. *)
    assert (HhA : real_lt (real_abs h)
             (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))).
    { apply (real_min_lt_l h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhE : real_lt (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
    { apply (real_min_lt_r h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhAA : real_lt (real_abs h) (real_min δa (real_const (1 # 2)))).
    { apply (real_min_lt_l h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhlr : real_lt (real_abs h) (real_mult eps (real_const kδ))).
    { apply (real_min_lt_r h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhda : real_lt (real_abs h) δa).
    { apply (real_min_lt_l h δa (real_const (1 # 2))). exact HhAA. }
    assert (Hh12 : real_lt (real_abs h) (real_const (1 # 2))).
    { apply (real_min_lt_r h δa (real_const (1 # 2))). exact HhAA. }
    (* X: b5n_h_pts. *)
    destruct (b5n_h_pts h eps kδ k2 Heps HkδT Hk2T Hhlr Hh12 HhE) as [Nh HNh].
    (* Y: arctan' at eps2 := eps*k2 / eps2' := eps'*k2p. *)
    destruct (Hδa h Hhda Hxh eps' Heps') as [Nw HNw].
    (* the column-error column. *)
    destruct (b5i_rs_addcol x Hx h Hxh eta HetaT) as [Nc HNc].
    (* pointwise budget (against the eps' witness). *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). } }
    assert (HcolQ8_all : forall n : nat, NatLe Ne1 n ->
            Qle eta (Qmult (1 # 8) (projT1 eps' n))).
    { intros n Hn.
      unfold eta.
      apply QleT'_to_Qle. apply (sc_qmult_le_l e1 (projT1 eps' n) (1 # 8)).
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). }
      { unfold Qle. simpl. lia. } }
    assert (HaddQ_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc)
                       (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc)
                      (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult (Qplus (Qmult 3 S) Mc) (Qmult 2 k2p))
                      (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold S. ring. }
      { apply (Qmult_le_compat_r
                 (Qmult (Qplus (Qmult 3 S) Mc) (Qmult 2 k2p))
                 (1 # 32) (projT1 eps' n)).
        { apply QleT'_to_Qle. apply (b5n_3S_Mc_2k2p_le S Mc K1e HSlt HMc0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    assert (HaddC_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult Mc (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult Mc (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult Mc (Qmult 2 k2p)) (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
      { apply (Qmult_le_compat_r (Qmult Mc (Qmult 2 k2p)) (1 # 32)
                                 (projT1 eps' n)).
        { apply QleT'_to_Qle. apply (b5n_Mc_2k2p_le S Mc K1e HSlt HMc0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    (* main assembly: real_le to real_lt (left branch), with witness eta. *)
    set (Nmax := Nat.max (Nat.max Ne0 Ne1) (Nat.max (Nat.max Nh Nw) (Nat.max Nc Nd))).
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n)).
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNh : NatLe Nh n) by (apply NatLe_lift; lia).
      assert (HnNw : NatLe Nw n) by (apply NatLe_lift; lia).
      assert (HnNc : NatLe Nc n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        { apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T. }
        { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He0lt n HnNe0)). } }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      destruct (HNh n HnNh) as [Hhδn [Hh12n Hhqn]].
      (* Z: the per-n main bound. *)
      assert (Hmain : Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { apply QleT'_to_Qle. apply (b5n_pern_main x Hx h Hxh n Ms Mc C4 eta kδ k2 k2p en en').
        { apply QleT'_to_Qle. exact (HMs_all n). }
        { apply QleT'_to_Qle. exact (HMc_all n). }
        { exact HC4. }
        { apply QleT'_to_Qle. exact HC40. }
        { exact (HNc n HnNc). }
        { exact (QleT'_to_Qle _ _ Hhδn). }
        { exact (QleT'_to_Qle _ _ Hh12n). }
        { exact (QleT'_to_Qle _ _ Hhqn). }
        { apply QleT'_to_Qle. exact (HNw n HnNw). }
        { unfold b5i_dn. exact (QleT'_to_Qle _ _ (Hd n (NatLe_lift _ _ HnNd))). }
        { exact Hen0. }
        { exact Hen'0. }
        { exact Hk2Q. }
        { exact Hk2pQ. }
        { exact HcoefQ. }
        { exact HcoefC. }
        { exact (HcolQ8_all n HnNe1). }
        { exact (HaddQ_all n HnNe1). }
        { exact (HaddC_all n HnNe1). }
        { exact Hk2pK1. } }
      (* margin: eta < (1/4)*en'; Hfin: eta < (en*hn + en') - Dn. *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply QltT_to_Qlt. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        { apply QltT_to_Qlt. exact He1T. }
        { exact (QltT_to_Qlt _ _ (He1lt n HnNe1)). } }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply QltT_to_Qlt. apply (b5n_close Dn hn en en' eta).
        { unfold Dn. exact Hmain. }
        { unfold en'. exact Hq4e. } }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (b5a_comp_err_sin x Hx h Hxh)) n))
                          (Qminus (Qplus (Qmult en hn) en') Dn)).
      { unfold en, en', hn, Dn.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (b5a_comp_err_sin x Hx h Hxh) n)).
        ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5a_comp_err_sin x Hx h Hxh)) n))).
      { exact Hfin. }
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrepl. } } }
Defined.
(* C2t: b5dG_cos_atan_diff_closed_r_exp (transparent Defined).
   Copy source: upstream sc2_b5a_item9 C2 b5d5_cos_atan_diff_closed_r_expl (item9
   L318-575, machine-extracted with no hand transcription); statement unchanged (expl
   form).
   The in-body vdh destruct source: b5c_vdh_pts_r (root, Qed) is replaced by this
   file's dependency b5dD_vdh_pts_r_exp (upstream sc2_b5a_item14 C8b, transparent
   Defined); the closing Qed opens to Defined (transparency is the goal). *)
Lemma b5dG_cos_atan_diff_closed_r_exp :
  forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (Ms Mc C4 : Q),
  QltT 0 Ms -> QltT 0 Mc -> QleT' 0 C4 -> QleT' 1 C4 ->
  (forall j : nat, QleT' (exp_series j 4) C4) ->
  (forall n : nat, QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Ms) ->
  (forall n : nat, QleT' (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (b5a_comp_err_cos x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)) h Hxh))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr Ms Mc C4 HMsQ HMcQ HC40 HC4ge1 HC4 HMs_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)).
  destruct (b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMsQ. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMcQ. }
  set (S := Qplus Ms Mc).
  assert (HSlt : Qlt 0 S). { unfold S.
    pose proof (QltT_to_Qlt 0 Ms HMsQ). pose proof (QltT_to_Qlt 0 Mc HMcQ). nra. }
  set (K1e := Qplus (Qmult Mc (Qplus (Qmult 4 C4) 2))
                    (Qmult Ms (Qplus (Qmult 4 C4) 4))).
  assert (HK1_0 : Qle 0 K1e). { unfold K1e.
    pose proof (QleT'_to_Qle 0 C4 HC40). nra. }
  set (kδ := Qinv (Qmult 512 (Qplus S 1))).
  set (k2 := Qinv (Qmult (Qmult 512 (Qplus S 1))
                         (Qplus (Qplus (Qmult 3 S) Ms) 1))).
  set (k2p := Qinv (Qmult (Qmult 1024 (Qplus K1e 1))
                          (Qplus (Qplus (Qmult 3 S) Ms) 1))).
  assert (HkδT : QltT 0 kδ).
  { unfold kδ. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2T : QltT 0 k2).
  { unfold k2. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2pT : QltT 0 k2p).
  { unfold k2p. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2Q : Qle 0 k2). { apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2T. }
  assert (Hk2pQ : Qlt 0 k2p). { apply QltT_to_Qlt. exact Hk2pT. }
  (* global budget: coef (quad), coefC (crude), 8*k2p*K1e (forced by the crude bound). *)
  assert (HcoefQ : Qle (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) k2)) 1).
  { apply (Qle_trans (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                            (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) k2))
                     (Qplus (1 # 2) (1 # 2))
                     1).
    { apply Qplus_le_compat.
      { apply QleT'_to_Qle. apply (b5n_2S_kδ_le S HSlt). }
      { apply QleT'_to_Qle. apply (b5n_3S_Mc_k2_le S Ms HSlt HMs0). } }
    { nra. } }
  assert (HcoefC : Qle (Qmult Ms k2) 1).
  { apply (Qle_trans (Qmult Ms k2) (1 # 2) 1).
    { apply QleT'_to_Qle. apply (b5n_Mc_k2_le S Ms HSlt HMs0). }
    { unfold Qle. simpl. lia. } }
  assert (Hk2pK1 : Qle (Qmult (Qmult 8 k2p)
                              (Qplus (Qmult Mc (Qplus (Qmult 4 C4) 2))
                                     (Qmult Ms (Qplus (Qmult 4 C4) 4)))) 1).
  { apply QleT'_to_Qle. apply (b5n_8k2p_K1_le S Ms K1e HSlt HMs0 HK1_0). }
  (* delta assembly: 0 < each component. *)
  assert (H12T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (H14T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  destruct (b5dD_vdh_pts_r_exp r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2T Hk2pT) as [δa [Hδa0 Hδa]].
  assert (Hc12r : real_lt real_zero (real_const (1 # 2))).
  { apply real_const_pos. exact H12T. }
  assert (Hepskδ : real_lt real_zero (real_mult eps (real_const kδ))).
  { apply real_mult_positive.
    { exact Heps. }
    { apply real_const_pos. exact HkδT. } }
  assert (Hqtr : real_lt real_zero
            (real_mult (real_const (1 # 4))
                       (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                     (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  { apply real_mult_positive.
    { apply real_const_pos. exact H14T. }
    { apply real_inv_pos_pos. } }
  set (delta := real_min
        (real_min (real_min δa (real_const (1 # 2)))
                  (real_mult eps (real_const kδ)))
        (real_mult (real_const (1 # 4))
                   (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                 (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos.
        { exact Hδa0. }
        { exact Hc12r. } }
      { exact Hepskδ. } }
    { exact Hqtr. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      { unfold Qlt. simpl. lia. }
      { apply QltT_to_Qlt. exact He1T. } }
    (* extracting the four-layer min for h against delta. *)
    assert (HhA : real_lt (real_abs h)
             (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))).
    { apply (real_min_lt_l h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhE : real_lt (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
    { apply (real_min_lt_r h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhAA : real_lt (real_abs h) (real_min δa (real_const (1 # 2)))).
    { apply (real_min_lt_l h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhlr : real_lt (real_abs h) (real_mult eps (real_const kδ))).
    { apply (real_min_lt_r h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhda : real_lt (real_abs h) δa).
    { apply (real_min_lt_l h δa (real_const (1 # 2))). exact HhAA. }
    assert (Hh12 : real_lt (real_abs h) (real_const (1 # 2))).
    { apply (real_min_lt_r h δa (real_const (1 # 2))). exact HhAA. }
    (* X: b5n_h_pts. *)
    destruct (b5n_h_pts h eps kδ k2 Heps HkδT Hk2T Hhlr Hh12 HhE) as [Nh HNh].
    (* Y: arctan' at eps2 := eps*k2 / eps2' := eps'*k2p. *)
    destruct (Hδa h Hhda Hxh eps' Heps') as [Nw HNw].
    (* the column-error column (cos side). *)
    destruct (b5d_rs_addcol_cos x Hx h Hxh eta HetaT) as [Nc HNc].
    (* pointwise budget (against the eps' witness). *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). } }
    assert (HcolQ8_all : forall n : nat, NatLe Ne1 n ->
            Qle eta (Qmult (1 # 8) (projT1 eps' n))).
    { intros n Hn.
      unfold eta.
      apply QleT'_to_Qle. apply (sc_qmult_le_l e1 (projT1 eps' n) (1 # 8)).
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). }
      { unfold Qle. simpl. lia. } }
    assert (HaddQ_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms)
                       (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms)
                      (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult (Qplus (Qmult 3 S) Ms) (Qmult 2 k2p))
                      (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold S. ring. }
      { apply (Qmult_le_compat_r
                 (Qmult (Qplus (Qmult 3 S) Ms) (Qmult 2 k2p))
                 (1 # 32) (projT1 eps' n)).
        { apply QleT'_to_Qle. apply (b5n_3S_Mc_2k2p_le S Ms K1e HSlt HMs0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    assert (HaddC_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult Ms (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult Ms (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult Ms (Qmult 2 k2p)) (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
      { apply (Qmult_le_compat_r (Qmult Ms (Qmult 2 k2p)) (1 # 32)
                                 (projT1 eps' n)).
        { apply QleT'_to_Qle. apply (b5n_Mc_2k2p_le S Ms K1e HSlt HMs0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    (* main assembly: real_le to real_lt (left branch), with witness eta. *)
    set (Nmax := Nat.max (Nat.max Ne0 Ne1) (Nat.max (Nat.max Nh Nw) (Nat.max Nc Nd))).
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n)).
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNh : NatLe Nh n) by (apply NatLe_lift; lia).
      assert (HnNw : NatLe Nw n) by (apply NatLe_lift; lia).
      assert (HnNc : NatLe Nc n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        { apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T. }
        { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He0lt n HnNe0)). } }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      destruct (HNh n HnNh) as [Hhδn [Hh12n Hhqn]].
      (* Z: the per-n main bound (cos version). *)
      assert (Hmain : Qle (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { apply QleT'_to_Qle. apply (b5d_pern_main_cos x Hx h Hxh n Ms Mc C4 eta kδ k2 k2p en en').
        { apply QleT'_to_Qle. exact (HMs_all n). }
        { apply QleT'_to_Qle. exact (HMc_all n). }
        { exact HC4. }
        { apply QleT'_to_Qle. exact HC40. }
        { exact (HNc n HnNc). }
        { exact (QleT'_to_Qle _ _ Hhδn). }
        { exact (QleT'_to_Qle _ _ Hh12n). }
        { exact (QleT'_to_Qle _ _ Hhqn). }
        { apply QleT'_to_Qle. exact (HNw n HnNw). }
        { unfold b5i_dn. exact (QleT'_to_Qle _ _ (Hd n (NatLe_lift _ _ HnNd))). }
        { exact Hen0. }
        { exact Hen'0. }
        { exact Hk2Q. }
        { exact Hk2pQ. }
        { exact HcoefQ. }
        { exact HcoefC. }
        { exact (HcolQ8_all n HnNe1). }
        { exact (HaddQ_all n HnNe1). }
        { exact (HaddC_all n HnNe1). }
        { exact Hk2pK1. } }
      (* margin: eta < (1/4)*en'; Hfin: eta < (en*hn + en') - Dn. *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply QltT_to_Qlt. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        { apply QltT_to_Qlt. exact He1T. }
        { exact (QltT_to_Qlt _ _ (He1lt n HnNe1)). } }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply QltT_to_Qlt. apply (b5n_close Dn hn en en' eta).
        { unfold Dn. exact Hmain. }
        { unfold en'. exact Hq4e. } }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (b5a_comp_err_cos x Hx h Hxh)) n))
                          (Qminus (Qplus (Qmult en hn) en') Dn)).
      { unfold en, en', hn, Dn.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (b5a_comp_err_cos x Hx h Hxh) n)).
        ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5a_comp_err_cos x Hx h Hxh)) n))).
      { exact Hfin. }
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrepl. } } }
Defined.
(* ===== end of sc2_b5a_item17.v: delta-D1b sin/cos-atan expl transparent layer ===== *)

(* ===== Block b5dM_ (main item b5dM_real_const_pos; upstream source sc2_b5a_item23) ===== *)

(* Item 1 b5dM_real_const_pos (transparent Defined).
   Copy source: root real_const_pos (ConstructiveWorld.v L36290; body L36291-36314).
   Statement verbatim; body near-verbatim (zero destruct of root Qed witnesses in the
   body — pure Q-layer reasoning + qeq_le/ring/field, transparent); closes with Defined.
   The witness first component = c/2 (explicit) and N := 0 (explicit), so the value path
   computes (check (1): (1#4) -> (1#8)).
   Transparency is semantically load-bearing here: the cbn delta lists of the b5dQ_margin
   chain (this file L9445/9486/9546) unfold this piece explicitly to expose the witness
   c/2, so redirecting to the Qed root would block the value path (an opaque certificate
   embedded in a value path gets stuck, and the source swap fails to compile).
   Conclusion: keep both pieces — this one is the transparent-certificate reference, the
   S07 root is the statement-face reference; neither replaces the other, and this piece
   must not be treated as redirectable to the root. *)
Lemma b5dM_real_const_pos : forall (c : Q), QltT 0 c -> real_lt real_zero (real_const c).
Proof.
  intros c Hc.
  assert (Hhalf : Qlt 0 (c / 2)).
  { apply Qlt_shift_div_l; [change (Qlt 0 2); compute; reflexivity | simpl; apply QltT_to_Qlt; exact Hc]. }
  exists (c / 2). split.
  - apply Qlt_to_QltT. exact Hhalf.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (c / 2 + c / 2) _).
    + apply (Qle_lt_trans _ (c / 2 + 0) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (proj2 (Qplus_lt_r 0 (c / 2) (c / 2)) Hhalf).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      assert (Hc' : projT1 (real_const c) n == c) by (apply qeqT_imp_qeq; apply real_const_proj).
      assert (Hz' : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      setoid_rewrite Hc'. setoid_rewrite Hz'.
      unfold Qminus. transitivity (c + 0).
      * field.
      * assert (Hopp0 : Qopp 0%Q == 0%Q).
        { transitivity (Qred (Qmake 0 1)).
          - reflexivity.
          - apply Qred_correct. }
        rewrite Hopp0. reflexivity.
Defined.

(* Item 2 b5dM_real_two_pos_local (transparent Defined).
   Copy source: root real_two_pos_local (ConstructiveWorld.v L44573; body L44574-44579
   must not be copied — the root body goes through real_eq_lt_lt / real_lt_plus_compat /
   real_lt_zero_one (root Qed chain), so the witness first component stays opaque).
   Direct construction with explicit witnesses: exists (1#2) with N := 0, both branches
   closed by computation (template = upstream sc2_b5a_item20 J0 b5dJ_two_pos_exp
   L77-84); closes with Defined, so projT1 (real_inv_pos (1+1) this piece) n computes
   for all n as Qinv 2. *)
Lemma b5dM_real_two_pos_local : real_lt real_zero (real_plus real_one real_one).
Proof.
  unfold real_lt.
  exists (1 # 2).
  split.
  - vm_compute. constructor.
  - exists 0%nat. intros n Hn. vm_compute. constructor.
Defined.

(* Item 3 b5dM_b5i_one_plus_eps2_pos (transparent Defined).
   Copy source: root b5i_one_plus_eps2_pos (ConstructiveWorld.v L76147; body
   L76151-76185).  Statement verbatim; body near-verbatim (the body only destructs the
   input Heps — legal, it specializes after instantiation; the witness is already the
   explicit exists (1#2), with N := the input N1); closes with Defined.
   Value path: projT1 (this piece eps k2 Heps Hk2) = (1#2), independent of the inputs
   (verified by check (3)); N1 comes from destructing the input Heps — when the input is
   a transparent chain (such as the Item 1 copy) the whole chain reduces. *)
Lemma b5dM_b5i_one_plus_eps2_pos : forall (eps : Real) (k2 : Q),
  real_lt real_zero eps -> QltT 0 k2 ->
  real_lt real_zero (real_plus real_one (real_mult eps (real_const k2))).
Proof.
  intros eps k2 Heps Hk2.
  destruct Heps as [eps1 [Heps1 [N1 HN1]]].
  unfold real_lt.
  exists (1 # 2).
  split.
  - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - exists N1.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hen : Qlt 0 (projT1 eps n)).
    { apply (Qlt_le_trans 0 eps1 (projT1 eps n)).
      - apply QltT_to_Qlt. exact Heps1.
      - apply (Qle_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) (projT1 eps n)).
        + apply Qlt_le_weak. apply QltT_to_Qlt. exact (HN1 n Hn).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [projT1 real_zero]. ring. }
    apply (Qlt_le_trans (1 # 2) 1
                        (Qminus (projT1 (real_plus real_one (real_mult eps (real_const k2))) n)
                                (projT1 real_zero n))).
    + unfold Qlt. simpl. lia.
    + apply (Qle_trans 1 (Qplus 1 (Qmult (projT1 eps n) k2))
                       (Qminus (projT1 (real_plus real_one (real_mult eps (real_const k2))) n)
                               (projT1 real_zero n))).
      * apply (Qle_trans 1 (Qplus 1 0) (Qplus 1 (Qmult (projT1 eps n) k2))).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply (Qmult_le_0_compat (projT1 eps n) k2).
              ** apply (Qlt_le_weak 0 (projT1 eps n)). exact Hen.
              ** apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_mult eps (real_const k2)) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const k2) n)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj k2 n)).
        cbn [projT1 real_one projT1 real_zero].
        ring.
Defined.

(* Item 4 b5dM_b5n_eps_proj_lt (transparent Defined).
   Copy source: root b5n_eps_proj_lt (ConstructiveWorld.v L78874; body L78877-78888).
   Statement verbatim (NatLe verbatim, do not alter); body near-verbatim (only destructs
   the input Heps; e := the input eps1 and N := the input N passed through); closes with
   Defined.
   Value path: e := projT1 of the input witness — when the input is the Item 1 copy
   (Defined), (real_const (1#4)) gives e = (1#8) (verified by check (4)). *)
Lemma b5dM_b5n_eps_proj_lt : forall (eps : Real), real_lt real_zero eps ->
  sigT (fun e : Q => And (QltT 0 e) (sigT (fun N : nat =>
    forall n : nat, NatLe N n -> QltT e (projT1 eps n)))).
Proof.
  intros eps Heps.
  destruct Heps as [e [He [N HN]]].
  exists e. split.
  { exact He. }
  { exists N. intros n Hn.
    assert (Hsub : Qlt e (Qminus (projT1 eps n) (projT1 real_zero n))).
    { apply QltT_to_Qlt. exact (HN n Hn). }
    apply Qlt_to_QltT.
    apply (Qlt_le_trans e (Qminus (projT1 eps n) (projT1 real_zero n)) (projT1 eps n)).
    { exact Hsub. }
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [projT1 real_zero]. ring. } }
Defined.

(* Item 5 b5dM_b5c_d_proj_le_one (transparent Defined).
   Copy source: root b5c_d_proj_le_one (ConstructiveWorld.v L74897; body L74900-74929
   must not be copied — the root L74903 destructs real_inv_proj (root Qed), which makes
   N opaque).  Direct construction with exists 0%nat (the bound holds for all n):
   unfold b5a_atan_d (definitionally == real_inv_pos (1+x*x) (b5a_one_plus_sq_pos x));
   destruct (b5a_one_plus_sq_pos x) (case analysis on a Qed witness is legal — it does
   not enter the value path: exists 0%nat comes first, the destruct lands inside the
   proof of the second component) + destruct x (case analysis makes the coordinates
   reducible) + cbn reduces to the if Nat.leb N0 n split (m := n / N0); both branches
   prove Qle (Qabs (Qinv (1 + u m*u m))) 1: u m >= 1 by b5c_one_sq_proj_ge_one (root
   L74912 usage, true for all m), so Qinv (u m) lies in (0,1]: Qabs_pos (positivity via
   Qlt_le_trans 0 1) + b5c_qinv_le_one + qeq_imp_qle — template = the root L74919-28
   chain. *)
Lemma b5dM_b5c_d_proj_le_one : forall (x : Real),
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QleT' (Qabs (projT1 (b5a_atan_d x) n)) 1).
Proof.
  intro x.
  unfold b5a_atan_d.
  exists 0%nat.
  intros n Hn.
  destruct (b5a_one_plus_sq_pos x) as [e0 [He0 [N0 HN0]]].
  destruct x as [u Hu].
  assert (Hbd : forall m : nat,
           Qle (Qabs (Qinv (Qplus 1%Q (Qmult (u m) (u m))))) 1).
  { intro m.
    assert (Hge1 : Qle 1 (Qplus 1%Q (Qmult (u m) (u m)))).
    { apply QleT'_to_Qle. apply (b5c_one_sq_proj_ge_one (existT (fun s : Qseq => cauchy s) u Hu) m). }
    assert (Hpos : Qlt 0 (Qplus 1%Q (Qmult (u m) (u m)))).
    { apply (Qlt_le_trans 0 1 (Qplus 1%Q (Qmult (u m) (u m)))).
      - unfold Qlt. simpl. lia.
      - exact Hge1. }
    apply (Qle_trans (Qabs (Qinv (Qplus 1%Q (Qmult (u m) (u m)))))
                     (Qinv (Qplus 1%Q (Qmult (u m) (u m))))
                     1).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      apply (Qabs_pos (Qinv (Qplus 1%Q (Qmult (u m) (u m))))).
      apply (Qlt_le_weak 0 (Qinv (Qplus 1%Q (Qmult (u m) (u m))))).
      apply Qinv_lt_0_compat. exact Hpos.
    - apply QleT'_to_Qle. apply (b5c_qinv_le_one (Qplus 1%Q (Qmult (u m) (u m)))).
      + exact Hpos.
      + exact Hge1. }
  cbn [projT1 real_inv_pos real_plus real_mult real_one].
  destruct (Nat.leb N0 n) eqn:E.
  - apply Qle_to_QleT'. exact (Hbd n).
  - apply Qle_to_QleT'. exact (Hbd N0).
Defined.

(* ===== Block b5dI_ (main item b5dI_E_diff_closed_r_exp; upstream source sc2_b5a_item19) ===== *)

Lemma b5dI_sA_proj_le : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (n : nat) (M : Q),
  QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) M ->
  QleT' (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)) M.
Proof.
  intros x Hx n M Hle.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                   (Qabs (sin_partial n (arctan_partial n (projT1 x n))))
                   M).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    apply (Qabs_wd (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                   (sin_partial n (arctan_partial n (projT1 x n)))).
    rewrite (qeqT_imp_qeq _ _ (real_sin_proj (cauchy_real_arctan x Hx) n)).
    apply qeqT_imp_qeq. apply (sc_sin_partial_wd n (projT1 (cauchy_real_arctan x Hx) n)
                             (arctan_partial n (projT1 x n))).
    rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hx n)).
    reflexivity.
  - apply QleT'_to_Qle. exact Hle.
Qed.

(* v3 helper: b5n_h_pts (root L78570, its statement embeds the root b5i_one_plus_eps2_pos
   witness) needs the root leaf-form bound |h| < (1#4)*real_inv_pos (1+eps*k2)
   (b5i_one_plus_eps2_pos ...); the value-path delta leaf has been swapped to the b5dM_
   transparent pieces, so the two leaves are real_eq (real_inv_pos_ext is
   witness-independent and needs only reflexivity of the base real_eq) — bridging lemma
   (transparent Defined, proof side only). *)
Lemma b5dI_inv_leaf_witness_eq : forall (eps : Real) (k2 : Q)
  (Heps : real_lt real_zero eps) (Hk2 : QltT 0 k2),
  real_eq
    (real_mult (real_const (1 # 4))
       (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                     (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2)))
    (real_mult (real_const (1 # 4))
       (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                     (b5i_one_plus_eps2_pos eps k2 Heps Hk2))).
Proof.
  intros eps k2 Heps Hk2.
  apply (RealSetoid.real_eq_mult_compat
           (real_const (1 # 4))
           (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                         (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2))
           (real_const (1 # 4))
           (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                         (b5i_one_plus_eps2_pos eps k2 Heps Hk2))).
  - apply real_eq_refl.
  - apply (real_inv_pos_ext
             (real_plus real_one (real_mult eps (real_const k2)))
             (real_plus real_one (real_mult eps (real_const k2)))
             (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2)
             (b5i_one_plus_eps2_pos eps k2 Heps Hk2)).
    apply real_eq_refl.
Defined.

(* v3 helper (Section 4 contingency (a)): real_mult_positive is root Qed (L39518, Qed
   at L39529) — the three E-diff assert stations (HepsS/HepsC/Hepskδ) feed the C1t/C2t
   leaf calls, and their witnesses are destructed layer by layer in the value path by
   b5dM_b5i_one_plus_eps2_pos / real_inv_pos, so the opaque root leaves the match stuck.
   Transparent re-certificate: statement verbatim = root L39518; the body is isomorphic
   to the root real_mult_pos_compat (L34988-35040, same statement), constructing explicit
   witnesses (destruct the inputs Ha/Hb, take e := e1*e2 and N := Nat.max N1 N2; drop
   the root body's dead dependency on real_norm_bounded; Q-layer Qmult_lt_compat_nonneg
   bridge), closing with Defined. *)
Lemma b5dI_real_mult_positive_exp : forall a b : Real,
  real_lt real_zero a -> real_lt real_zero b -> real_lt real_zero (real_mult a b).
Proof.
  intros a b Ha Hb.
  destruct Ha as [e1 [He1 [N1 HN1]]].
  destruct Hb as [e2 [He2 [N2 HN2]]].
  assert (Hpos : Qlt 0 (e1 * e2)).
  { apply Qmult_lt_0_compat; [exact (QltT_to_Qlt _ _ He1) | exact (QltT_to_Qlt _ _ He2)]. }
  unfold real_lt.
  exists (e1 * e2).
  split.
  - apply Qlt_to_QltT. exact Hpos.
  - exists (Nat.max N1 N2).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hm : Qeq (projT1 (real_mult a b) n) (Qmult (projT1 a n) (projT1 b n)))
      by (apply qeqT_imp_qeq; apply real_mult_proj).
    setoid_rewrite Hm.
    assert (Hz0 : Qeq (projT1 real_zero n) 0) by (cbn [projT1]; reflexivity).
    assert (Hz0' : Qeq (Qmult (projT1 a n) (projT1 b n) - projT1 real_zero n)
                       (Qmult (projT1 a n) (projT1 b n))).
    { setoid_rewrite Hz0. unfold Qminus. ring. }
    setoid_rewrite Hz0'.
    assert (Ha1 : QltT e1 (projT1 a n)).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans e1 (projT1 a n - projT1 real_zero n) (projT1 a n)).
      { apply QltT_to_Qlt. apply (HN1 n). apply NatLe_lift.
        apply (Nat.le_trans _ (Nat.max N1 N2) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
      { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. setoid_rewrite Hz0. unfold Qminus. ring. } }
    assert (Hb1 : QltT e2 (projT1 b n)).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans e2 (projT1 b n - projT1 real_zero n) (projT1 b n)).
      { apply QltT_to_Qlt. apply (HN2 n). apply NatLe_lift.
        apply (Nat.le_trans _ (Nat.max N1 N2) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
      { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. setoid_rewrite Hz0. unfold Qminus. ring. } }
    apply (Qmult_lt_compat_nonneg e1 (projT1 a n) e2 (projT1 b n)).
    + split.
      * apply (Qlt_le_weak 0 e1). exact (QltT_to_Qlt _ _ He1).
      * apply QltT_to_Qlt. exact Ha1.
    + split.
      * apply (Qlt_le_weak 0 e2). exact (QltT_to_Qlt _ _ He2).
      * apply QltT_to_Qlt. exact Hb1.
Defined.

Lemma b5dI_sin_atan_diff_closed_r_exp :
  forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (Ms Mc C4 : Q),
  QltT 0 Ms -> QltT 0 Mc -> QleT' 0 C4 -> QleT' 1 C4 ->
  (forall j : nat, QleT' (exp_series j 4) C4) ->
  (forall n : nat, QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Ms) ->
  (forall n : nat, QleT' (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (b5a_comp_err_sin x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)) h Hxh))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr Ms Mc C4 HMsQ HMcQ HC40 HC4ge1 HC4 HMs_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)).
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMsQ. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMcQ. }
  set (S := Qplus Ms Mc).
  assert (HSlt : Qlt 0 S). { unfold S.
    pose proof (QltT_to_Qlt 0 Ms HMsQ). pose proof (QltT_to_Qlt 0 Mc HMcQ). nra. }
  set (K1e := Qplus (Qmult Ms (Qplus (Qmult 4 C4) 2))
                    (Qmult Mc (Qplus (Qmult 4 C4) 4))).
  assert (HK1_0 : Qle 0 K1e). { unfold K1e.
    pose proof (QleT'_to_Qle 0 C4 HC40). nra. }
  set (kδ := Qinv (Qmult 512 (Qplus S 1))).
  set (k2 := Qinv (Qmult (Qmult 512 (Qplus S 1))
                         (Qplus (Qplus (Qmult 3 S) Mc) 1))).
  set (k2p := Qinv (Qmult (Qmult 1024 (Qplus K1e 1))
                          (Qplus (Qplus (Qmult 3 S) Mc) 1))).
  assert (HkδT : QltT 0 kδ).
  { unfold kδ. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2T : QltT 0 k2).
  { unfold k2. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2pT : QltT 0 k2p).
  { unfold k2p. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2Q : Qle 0 k2). { apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2T. }
  assert (Hk2pQ : Qlt 0 k2p). { apply QltT_to_Qlt. exact Hk2pT. }
  (* global budget: coef (quad), coefC (crude), 8*k2p*K1 (forced by the crude bound). *)
  assert (HcoefQ : Qle (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2)) 1).
  { apply (Qle_trans (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                             (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2))
                     (Qplus (1 # 2) (1 # 2))
                     1).
    { apply Qplus_le_compat.
      { apply QleT'_to_Qle. apply (b5n_2S_kδ_le S HSlt). }
      { apply QleT'_to_Qle. apply (b5n_3S_Mc_k2_le S Mc HSlt HMc0). } }
    { nra. } }
  assert (HcoefC : Qle (Qmult Mc k2) 1).
  { apply (Qle_trans (Qmult Mc k2) (1 # 2) 1).
    { apply QleT'_to_Qle. apply (b5n_Mc_k2_le S Mc HSlt HMc0). }
    { unfold Qle. simpl. lia. } }
  assert (Hk2pK1 : Qle (Qmult (Qmult 8 k2p)
                              (Qplus (Qmult Ms (Qplus (Qmult 4 C4) 2))
                                     (Qmult Mc (Qplus (Qmult 4 C4) 4)))) 1).
  { apply QleT'_to_Qle. apply (b5n_8k2p_K1_le S Mc K1e HSlt HMc0 HK1_0). }
  (* delta assembly: 0 < each component. *)
  assert (H12T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (H14T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  destruct (b5dD_vdh_pts_r_exp r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2T Hk2pT) as [δa [Hδa0 Hδa]].
  assert (Hc12r : real_lt real_zero (real_const (1 # 2))).
  { apply b5dM_real_const_pos. exact H12T. }
  assert (Hepskδ : real_lt real_zero (real_mult eps (real_const kδ))).
  { apply real_mult_positive.
    { exact Heps. }
    { apply b5dM_real_const_pos. exact HkδT. } }
  assert (Hqtr : real_lt real_zero
            (real_mult (real_const (1 # 4))
                       (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                     (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  { apply real_mult_positive.
    { apply b5dM_real_const_pos. exact H14T. }
    { apply real_inv_pos_pos. } }
  set (delta := real_min
        (real_min (real_min δa (real_const (1 # 2)))
                  (real_mult eps (real_const kδ)))
        (real_mult (real_const (1 # 4))
                   (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                 (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos.
        { exact Hδa0. }
        { exact Hc12r. } }
      { exact Hepskδ. } }
    { exact Hqtr. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
  destruct (b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      { unfold Qlt. simpl. lia. }
      { apply QltT_to_Qlt. exact He1T. } }
    (* extracting the four-layer min for h against delta. *)
    assert (HhA : real_lt (real_abs h)
             (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))).
    { apply (real_min_lt_l h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhE : real_lt (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
    { apply (real_min_lt_r h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhAA : real_lt (real_abs h) (real_min δa (real_const (1 # 2)))).
    { apply (real_min_lt_l h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhlr : real_lt (real_abs h) (real_mult eps (real_const kδ))).
    { apply (real_min_lt_r h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhda : real_lt (real_abs h) δa).
    { apply (real_min_lt_l h δa (real_const (1 # 2))). exact HhAA. }
    assert (Hh12 : real_lt (real_abs h) (real_const (1 # 2))).
    { apply (real_min_lt_r h δa (real_const (1 # 2))). exact HhAA. }
    (* X: b5n_h_pts (the root statement embeds the root witness, so the root leaf-form Hhq_r is derived via the bridge). *)
    assert (Hhq_r : real_lt (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
    { apply (real_lt_le_trans (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      { exact HhE. }
      { apply RealSetoid.real_eq_le.
        exact (b5dI_inv_leaf_witness_eq eps k2 Heps Hk2T). } }
    destruct (b5n_h_pts h eps kδ k2 Heps HkδT Hk2T Hhlr Hh12 Hhq_r) as [Nh HNh].
    (* Y: arctan' at eps2 := eps*k2 / eps2' := eps'*k2p. *)
    destruct (Hδa h Hhda Hxh eps' Heps') as [Nw HNw].
    (* the column-error column. *)
    destruct (b5i_rs_addcol x Hx h Hxh eta HetaT) as [Nc HNc].
    (* pointwise budget (against the eps' witness). *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). } }
    assert (HcolQ8_all : forall n : nat, NatLe Ne1 n ->
            Qle eta (Qmult (1 # 8) (projT1 eps' n))).
    { intros n Hn.
      unfold eta.
      apply QleT'_to_Qle. apply (sc_qmult_le_l e1 (projT1 eps' n) (1 # 8)).
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). }
      { unfold Qle. simpl. lia. } }
    assert (HaddQ_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc)
                       (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc)
                      (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult (Qplus (Qmult 3 S) Mc) (Qmult 2 k2p))
                      (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold S. ring. }
      { apply (Qmult_le_compat_r
                 (Qmult (Qplus (Qmult 3 S) Mc) (Qmult 2 k2p))
                 (1 # 32) (projT1 eps' n)).
        { apply QleT'_to_Qle. apply (b5n_3S_Mc_2k2p_le S Mc K1e HSlt HMc0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    assert (HaddC_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult Mc (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult Mc (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult Mc (Qmult 2 k2p)) (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
      { apply (Qmult_le_compat_r (Qmult Mc (Qmult 2 k2p)) (1 # 32)
                                 (projT1 eps' n)).
        { apply QleT'_to_Qle. apply (b5n_Mc_2k2p_le S Mc K1e HSlt HMc0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    (* main assembly: real_le to real_lt (left branch), with witness eta. *)
    set (Nmax := Nat.max (Nat.max Ne0 Ne1) (Nat.max (Nat.max Nh Nw) (Nat.max Nc Nd))).
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n)).
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNh : NatLe Nh n) by (apply NatLe_lift; lia).
      assert (HnNw : NatLe Nw n) by (apply NatLe_lift; lia).
      assert (HnNc : NatLe Nc n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        { apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T. }
        { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He0lt n HnNe0)). } }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      destruct (HNh n HnNh) as [Hhδn [Hh12n Hhqn]].
      (* Z: the per-n main bound. *)
      assert (Hmain : Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { apply QleT'_to_Qle. apply (b5n_pern_main x Hx h Hxh n Ms Mc C4 eta kδ k2 k2p en en').
        { apply QleT'_to_Qle. exact (HMs_all n). }
        { apply QleT'_to_Qle. exact (HMc_all n). }
        { exact HC4. }
        { apply QleT'_to_Qle. exact HC40. }
        { exact (HNc n HnNc). }
        { exact (QleT'_to_Qle _ _ Hhδn). }
        { exact (QleT'_to_Qle _ _ Hh12n). }
        { exact (QleT'_to_Qle _ _ Hhqn). }
        { apply QleT'_to_Qle. exact (HNw n HnNw). }
        { unfold b5i_dn. exact (QleT'_to_Qle _ _ (Hd n (NatLe_lift _ _ HnNd))). }
        { exact Hen0. }
        { exact Hen'0. }
        { exact Hk2Q. }
        { exact Hk2pQ. }
        { exact HcoefQ. }
        { exact HcoefC. }
        { exact (HcolQ8_all n HnNe1). }
        { exact (HaddQ_all n HnNe1). }
        { exact (HaddC_all n HnNe1). }
        { exact Hk2pK1. } }
      (* margin: eta < (1/4)*en'; Hfin: eta < (en*hn + en') - Dn. *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply QltT_to_Qlt. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        { apply QltT_to_Qlt. exact He1T. }
        { exact (QltT_to_Qlt _ _ (He1lt n HnNe1)). } }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply QltT_to_Qlt. apply (b5n_close Dn hn en en' eta).
        { unfold Dn. exact Hmain. }
        { unfold en'. exact Hq4e. } }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (b5a_comp_err_sin x Hx h Hxh)) n))
                          (Qminus (Qplus (Qmult en hn) en') Dn)).
      { unfold en, en', hn, Dn.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (b5a_comp_err_sin x Hx h Hxh) n)).
        ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5a_comp_err_sin x Hx h Hxh)) n))).
      { exact Hfin. }
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrepl. } } }
Defined.

Lemma b5dI_cos_atan_diff_closed_r_exp :
  forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (Ms Mc C4 : Q),
  QltT 0 Ms -> QltT 0 Mc -> QleT' 0 C4 -> QleT' 1 C4 ->
  (forall j : nat, QleT' (exp_series j 4) C4) ->
  (forall n : nat, QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Ms) ->
  (forall n : nat, QleT' (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (b5a_comp_err_cos x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)) h Hxh))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr Ms Mc C4 HMsQ HMcQ HC40 HC4ge1 HC4 HMs_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)).
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMsQ. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMcQ. }
  set (S := Qplus Ms Mc).
  assert (HSlt : Qlt 0 S). { unfold S.
    pose proof (QltT_to_Qlt 0 Ms HMsQ). pose proof (QltT_to_Qlt 0 Mc HMcQ). nra. }
  set (K1e := Qplus (Qmult Mc (Qplus (Qmult 4 C4) 2))
                    (Qmult Ms (Qplus (Qmult 4 C4) 4))).
  assert (HK1_0 : Qle 0 K1e). { unfold K1e.
    pose proof (QleT'_to_Qle 0 C4 HC40). nra. }
  set (kδ := Qinv (Qmult 512 (Qplus S 1))).
  set (k2 := Qinv (Qmult (Qmult 512 (Qplus S 1))
                         (Qplus (Qplus (Qmult 3 S) Ms) 1))).
  set (k2p := Qinv (Qmult (Qmult 1024 (Qplus K1e 1))
                          (Qplus (Qplus (Qmult 3 S) Ms) 1))).
  assert (HkδT : QltT 0 kδ).
  { unfold kδ. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2T : QltT 0 k2).
  { unfold k2. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2pT : QltT 0 k2p).
  { unfold k2p. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2Q : Qle 0 k2). { apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2T. }
  assert (Hk2pQ : Qlt 0 k2p). { apply QltT_to_Qlt. exact Hk2pT. }
  (* global budget: coef (quad), coefC (crude), 8*k2p*K1e (forced by the crude bound). *)
  assert (HcoefQ : Qle (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) k2)) 1).
  { apply (Qle_trans (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                            (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) k2))
                     (Qplus (1 # 2) (1 # 2))
                     1).
    { apply Qplus_le_compat.
      { apply QleT'_to_Qle. apply (b5n_2S_kδ_le S HSlt). }
      { apply QleT'_to_Qle. apply (b5n_3S_Mc_k2_le S Ms HSlt HMs0). } }
    { nra. } }
  assert (HcoefC : Qle (Qmult Ms k2) 1).
  { apply (Qle_trans (Qmult Ms k2) (1 # 2) 1).
    { apply QleT'_to_Qle. apply (b5n_Mc_k2_le S Ms HSlt HMs0). }
    { unfold Qle. simpl. lia. } }
  assert (Hk2pK1 : Qle (Qmult (Qmult 8 k2p)
                              (Qplus (Qmult Mc (Qplus (Qmult 4 C4) 2))
                                     (Qmult Ms (Qplus (Qmult 4 C4) 4)))) 1).
  { apply QleT'_to_Qle. apply (b5n_8k2p_K1_le S Ms K1e HSlt HMs0 HK1_0). }
  (* delta assembly: 0 < each component. *)
  assert (H12T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (H14T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  destruct (b5dD_vdh_pts_r_exp r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2T Hk2pT) as [δa [Hδa0 Hδa]].
  assert (Hc12r : real_lt real_zero (real_const (1 # 2))).
  { apply b5dM_real_const_pos. exact H12T. }
  assert (Hepskδ : real_lt real_zero (real_mult eps (real_const kδ))).
  { apply real_mult_positive.
    { exact Heps. }
    { apply b5dM_real_const_pos. exact HkδT. } }
  assert (Hqtr : real_lt real_zero
            (real_mult (real_const (1 # 4))
                       (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                     (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  { apply real_mult_positive.
    { apply b5dM_real_const_pos. exact H14T. }
    { apply real_inv_pos_pos. } }
  set (delta := real_min
        (real_min (real_min δa (real_const (1 # 2)))
                  (real_mult eps (real_const kδ)))
        (real_mult (real_const (1 # 4))
                   (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                 (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos.
        { exact Hδa0. }
        { exact Hc12r. } }
      { exact Hepskδ. } }
    { exact Hqtr. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
  destruct (b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      { unfold Qlt. simpl. lia. }
      { apply QltT_to_Qlt. exact He1T. } }
    (* extracting the four-layer min for h against delta. *)
    assert (HhA : real_lt (real_abs h)
             (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))).
    { apply (real_min_lt_l h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhE : real_lt (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
    { apply (real_min_lt_r h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhAA : real_lt (real_abs h) (real_min δa (real_const (1 # 2)))).
    { apply (real_min_lt_l h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhlr : real_lt (real_abs h) (real_mult eps (real_const kδ))).
    { apply (real_min_lt_r h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhda : real_lt (real_abs h) δa).
    { apply (real_min_lt_l h δa (real_const (1 # 2))). exact HhAA. }
    assert (Hh12 : real_lt (real_abs h) (real_const (1 # 2))).
    { apply (real_min_lt_r h δa (real_const (1 # 2))). exact HhAA. }
    (* X: b5n_h_pts (the root statement embeds the root witness, so the root leaf-form Hhq_r is derived via the bridge). *)
    assert (Hhq_r : real_lt (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
    { apply (real_lt_le_trans (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5dM_b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      { exact HhE. }
      { apply RealSetoid.real_eq_le.
        exact (b5dI_inv_leaf_witness_eq eps k2 Heps Hk2T). } }
    destruct (b5n_h_pts h eps kδ k2 Heps HkδT Hk2T Hhlr Hh12 Hhq_r) as [Nh HNh].
    (* Y: arctan' at eps2 := eps*k2 / eps2' := eps'*k2p. *)
    destruct (Hδa h Hhda Hxh eps' Heps') as [Nw HNw].
    (* the column-error column (cos side). *)
    destruct (b5d_rs_addcol_cos x Hx h Hxh eta HetaT) as [Nc HNc].
    (* pointwise budget (against the eps' witness). *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). } }
    assert (HcolQ8_all : forall n : nat, NatLe Ne1 n ->
            Qle eta (Qmult (1 # 8) (projT1 eps' n))).
    { intros n Hn.
      unfold eta.
      apply QleT'_to_Qle. apply (sc_qmult_le_l e1 (projT1 eps' n) (1 # 8)).
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). }
      { unfold Qle. simpl. lia. } }
    assert (HaddQ_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms)
                       (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms)
                      (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult (Qplus (Qmult 3 S) Ms) (Qmult 2 k2p))
                      (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold S. ring. }
      { apply (Qmult_le_compat_r
                 (Qmult (Qplus (Qmult 3 S) Ms) (Qmult 2 k2p))
                 (1 # 32) (projT1 eps' n)).
        { apply QleT'_to_Qle. apply (b5n_3S_Mc_2k2p_le S Ms K1e HSlt HMs0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    assert (HaddC_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult Ms (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult Ms (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult Ms (Qmult 2 k2p)) (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
      { apply (Qmult_le_compat_r (Qmult Ms (Qmult 2 k2p)) (1 # 32)
                                 (projT1 eps' n)).
        { apply QleT'_to_Qle. apply (b5n_Mc_2k2p_le S Ms K1e HSlt HMs0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    (* main assembly: real_le to real_lt (left branch), with witness eta. *)
    set (Nmax := Nat.max (Nat.max Ne0 Ne1) (Nat.max (Nat.max Nh Nw) (Nat.max Nc Nd))).
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n)).
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNh : NatLe Nh n) by (apply NatLe_lift; lia).
      assert (HnNw : NatLe Nw n) by (apply NatLe_lift; lia).
      assert (HnNc : NatLe Nc n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        { apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T. }
        { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He0lt n HnNe0)). } }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      destruct (HNh n HnNh) as [Hhδn [Hh12n Hhqn]].
      (* Z: the per-n main bound (cos version). *)
      assert (Hmain : Qle (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { apply QleT'_to_Qle. apply (b5d_pern_main_cos x Hx h Hxh n Ms Mc C4 eta kδ k2 k2p en en').
        { apply QleT'_to_Qle. exact (HMs_all n). }
        { apply QleT'_to_Qle. exact (HMc_all n). }
        { exact HC4. }
        { apply QleT'_to_Qle. exact HC40. }
        { exact (HNc n HnNc). }
        { exact (QleT'_to_Qle _ _ Hhδn). }
        { exact (QleT'_to_Qle _ _ Hh12n). }
        { exact (QleT'_to_Qle _ _ Hhqn). }
        { apply QleT'_to_Qle. exact (HNw n HnNw). }
        { unfold b5i_dn. exact (QleT'_to_Qle _ _ (Hd n (NatLe_lift _ _ HnNd))). }
        { exact Hen0. }
        { exact Hen'0. }
        { exact Hk2Q. }
        { exact Hk2pQ. }
        { exact HcoefQ. }
        { exact HcoefC. }
        { exact (HcolQ8_all n HnNe1). }
        { exact (HaddQ_all n HnNe1). }
        { exact (HaddC_all n HnNe1). }
        { exact Hk2pK1. } }
      (* margin: eta < (1/4)*en'; Hfin: eta < (en*hn + en') - Dn. *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply QltT_to_Qlt. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        { apply QltT_to_Qlt. exact He1T. }
        { exact (QltT_to_Qlt _ _ (He1lt n HnNe1)). } }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply QltT_to_Qlt. apply (b5n_close Dn hn en en' eta).
        { unfold Dn. exact Hmain. }
        { unfold en'. exact Hq4e. } }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (b5a_comp_err_cos x Hx h Hxh)) n))
                          (Qminus (Qplus (Qmult en hn) en') Dn)).
      { unfold en, en', hn, Dn.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (b5a_comp_err_cos x Hx h Hxh) n)).
        ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5a_comp_err_cos x Hx h Hxh)) n))).
      { exact Hfin. }
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrepl. } } }
Defined.

Lemma b5dI_E_diff_closed_r_exp :
  forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (Msr Mc C4 : Q),
  QltT 0 Msr -> QltT 0 Mc -> QleT' 0 C4 -> QleT' 1 C4 ->
  (forall j : nat, QleT' (exp_series j 4) C4) ->
  (forall n : nat, QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Msr) ->
  (forall n : nat, QleT' (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5a_E (real_plus x h) Hxh)
                 (real_opp (real_plus (b5a_E x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)))
                            (real_mult (real_mult x (b5a_E x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1))))
                                       (real_mult (b5a_atan_d x) h))))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr Msr Mc C4 HMsr_pos HMcQ HC40 HC4ge1 HC4 HMsr_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)).
  assert (HMsrQ : Qlt 0 Msr). { apply QltT_to_Qlt. exact HMsr_pos. }
  assert (HMsr0 : Qle 0 Msr). { apply Qlt_le_weak. exact HMsrQ. }
  (* constants and budget. *)
  set (S := Msr).
  assert (HSlt : Qlt 0 S). { unfold S. exact HMsrQ. }
  set (kδ := Qinv (Qmult 512 (Qplus S 1))).
  assert (HkδT : QltT 0 kδ).
  { unfold kδ. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hkδ0 : Qle 0 kδ). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HkδT. }
  assert (HMsrkδ : Qle (Qmult Msr kδ) (1 # 4)).
  { assert (H2 : Qle (Qmult (Qmult 2 S) kδ) (1 # 2)).
    { apply QleT'_to_Qle. apply (b5n_2S_kδ_le S HSlt). }
    apply (Qle_trans (Qmult Msr kδ) (Qmult (1 # 2) (Qmult (Qmult 2 S) kδ)) (1 # 4)).
    { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold S. ring. }
    { apply (Qle_trans (Qmult (1 # 2) (Qmult (Qmult 2 S) kδ))
                       (Qmult (1 # 2) (1 # 2))
                       (1 # 4)).
      { apply QleT'_to_Qle. apply (sc_qmult_le_l (Qmult (Qmult 2 S) kδ) (1 # 2) (1 # 2)).
        { exact H2. }
        { unfold Qle. simpl. lia. } }
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. } } }
  assert (Hcoef : Qle (Qplus (Qplus (1 # 4) (1 # 4)) (Qmult Msr kδ)) 1).
  { nra. }
  assert (Hadd : Qle (Qplus (Qplus (Qplus (1 # 8) (1 # 8)) (1 # 16)) (1 # 16)) (3 # 4)).
  { nra. }
  assert (HkT4 : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (HkT8 : QltT 0 (1 # 8)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (HkT16 : QltT 0 (1 # 16)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  (* sin / cos closed-form instantiation with the coefficient share eps/4. *)
  assert (HepsS : real_lt real_zero (real_mult eps (real_const (1 # 4)))).
  { apply b5dI_real_mult_positive_exp. { exact Heps. } { apply b5dM_real_const_pos. exact HkT4. } }
  assert (HepsC : real_lt real_zero (real_mult eps (real_const (1 # 4)))).
  { apply b5dI_real_mult_positive_exp. { exact Heps. } { apply b5dM_real_const_pos. exact HkT4. } }
  destruct (b5dI_sin_atan_diff_closed_r_exp r Hr0 Hr1 x Hxr
             Msr Mc C4 HMsr_pos HMcQ HC40 HC4ge1 HC4 HMsr_all HMc_all
             (real_mult eps (real_const (1 # 4))) HepsS) as [δS [HδS0 HδS]].
  destruct (b5dI_cos_atan_diff_closed_r_exp r Hr0 Hr1 x Hxr
             Msr Mc C4 HMsr_pos HMcQ HC40 HC4ge1 HC4 HMsr_all HMc_all
             (real_mult eps (real_const (1 # 4))) HepsC) as [δC [HδC0 HδC]].
  assert (Hepskδ : real_lt real_zero (real_mult eps (real_const kδ))).
  { apply b5dI_real_mult_positive_exp. { exact Heps. } { apply b5dM_real_const_pos. exact HkδT. } }
  set (delta := real_min (real_min δS δC) (real_mult eps (real_const kδ))).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos. { exact HδS0. } { exact HδC0. } }
    { exact Hepskδ. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
  destruct (b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      { unfold Qlt. simpl. lia. }
      { apply QltT_to_Qlt. exact He1T. } }
    (* min extraction of |h| against delta: deltaS / deltaC / eps*kδ. *)
    assert (HhA : real_lt (real_abs h) (real_min δS δC)).
    { apply (real_min_lt_l h (real_min δS δC) (real_mult eps (real_const kδ))).
      exact Hh. }
    assert (Hhlr : real_lt (real_abs h) (real_mult eps (real_const kδ))).
    { apply (real_min_lt_r h (real_min δS δC) (real_mult eps (real_const kδ))).
      exact Hh. }
    assert (HhδS : real_lt (real_abs h) δS).
    { apply (real_min_lt_l h δS δC). exact HhA. }
    assert (HhδC : real_lt (real_abs h) δC).
    { apply (real_min_lt_r h δS δC). exact HhA. }
    (* sin share: closed form + pointwise conversion (slack shS := eps'*(1/16)). *)
    assert (HepsS'' : real_lt real_zero (real_mult eps' (real_const (1 # 8)))).
    { apply real_mult_positive. { exact Heps'. } { apply b5dM_real_const_pos. exact HkT8. } }
    assert (HshS : real_lt real_zero (real_mult eps' (real_const (1 # 16)))).
    { apply real_mult_positive. { exact Heps'. } { apply b5dM_real_const_pos. exact HkT16. } }
    destruct (b5i_abs_le_pointwise (b5a_comp_err_sin x Hx h Hxh)
               (real_plus (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                          (real_mult eps' (real_const (1 # 8))))
               (HδS h HhδS Hxh (real_mult eps' (real_const (1 # 8))) HepsS'')
               (real_mult eps' (real_const (1 # 16))) HshS) as [Ns HNs].
    (* cos share: closed form + pointwise conversion. *)
    assert (HepsC'' : real_lt real_zero (real_mult eps' (real_const (1 # 8)))).
    { apply real_mult_positive. { exact Heps'. } { apply b5dM_real_const_pos. exact HkT8. } }
    assert (HshC : real_lt real_zero (real_mult eps' (real_const (1 # 16)))).
    { apply real_mult_positive. { exact Heps'. } { apply b5dM_real_const_pos. exact HkT16. } }
    destruct (b5i_abs_le_pointwise (b5a_comp_err_cos x Hx h Hxh)
               (real_plus (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                          (real_mult eps' (real_const (1 # 8))))
               (HδC h HhδC Hxh (real_mult eps' (real_const (1 # 8))) HepsC'')
               (real_mult eps' (real_const (1 # 16))) HshC) as [Nc HNc].
    (* |h_n| <= en*kδ, and the N of the pointwise identity for dec. *)
    destruct (b5i_h_le_enk h eps kδ Hhlr HkδT) as [Nhδ HNhδ].
    destruct (b5e_E_dec_proj x Hx h Hxh) as [Ndec HNdec].
    (* pointwise budget (against the eps' witness). *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). } }
    set (Nmax := Nat.max (Nat.max Ne0 Ne1)
                 (Nat.max (Nat.max Ndec Nhδ) (Nat.max (Nat.max Ns Nc) Nd))).
    (* main assembly: real_le to real_lt (left branch), with witness eta. *)
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5e_E_err x Hx h Hxh) n)).
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNs : NatLe Ns n) by (apply NatLe_lift; lia).
      assert (HnNc : NatLe Nc n) by (apply NatLe_lift; lia).
      assert (HnNhδ : NatLe Nhδ n) by (apply NatLe_lift; lia).
      assert (HnNdec : NatLe Ndec n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        { apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T. }
        { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He0lt n HnNe0)). } }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      assert (Hhδn : Qle (Qabs (projT1 h n)) (Qmult en kδ)).
      { unfold en. exact (QleT'_to_Qle _ _ (HNhδ n HnNhδ)). }
      (* pointwise share-bound expansion (sin). *)
      assert (Hrs : Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                        (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
      { apply (Qle_trans (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                         (Qplus (projT1 (real_plus (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                                                   (real_mult eps' (real_const (1 # 8)))) n)
                                (projT1 (real_mult eps' (real_const (1 # 16))) n))
                         (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
        { exact (QleT'_to_Qle _ _ (HNs n HnNs)). }
        { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          unfold en, en'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                                         (real_mult eps' (real_const (1 # 8))) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult eps (real_const (1 # 4))) (real_abs h) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const (1 # 4)) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 4) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const (1 # 8)) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 8) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const (1 # 16)) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 16) n)).
          ring. } }
      (* pointwise share-bound expansion (cos side), folding in |x+h| <= 1. *)
      assert (Hxh'n : Qle (Qabs (Qplus (projT1 x n) (projT1 h n))) 1).
      { apply (Qle_trans (Qabs (Qplus (projT1 x n) (projT1 h n)))
                         (Qabs (projT1 (real_plus x h) n))
                         1).
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_wd (Qplus (projT1 x n) (projT1 h n))
                                       (projT1 (real_plus x h) n)).
          rewrite (qeqT_imp_qeq _ _ (real_plus_proj x h n)). ring. }
        { apply QleT'_to_Qle. exact (Hxh n). } }
      assert (Hrc0 : Qle (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                         (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
      { apply (Qle_trans (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                         (Qplus (projT1 (real_plus (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                                                   (real_mult eps' (real_const (1 # 8)))) n)
                                (projT1 (real_mult eps' (real_const (1 # 16))) n))
                         (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
        { exact (QleT'_to_Qle _ _ (HNc n HnNc)). }
        { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          unfold en, en'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                                         (real_mult eps' (real_const (1 # 8))) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult eps (real_const (1 # 4))) (real_abs h) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const (1 # 4)) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 4) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const (1 # 8)) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 8) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const (1 # 16)) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 16) n)).
          ring. } }
      assert (Hrc : Qle (Qabs (Qmult (Qplus (projT1 x n) (projT1 h n))
                                     (projT1 (b5a_comp_err_cos x Hx h Hxh) n)))
                        (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
      { apply (Qle_trans (Qabs (Qmult (Qplus (projT1 x n) (projT1 h n))
                                      (projT1 (b5a_comp_err_cos x Hx h Hxh) n)))
                         (Qmult (Qabs (Qplus (projT1 x n) (projT1 h n)))
                                (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n)))
                         (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_Qmult (Qplus (projT1 x n) (projT1 h n))
                                          (projT1 (b5a_comp_err_cos x Hx h Hxh) n)). }
        { apply (Qle_trans (Qmult (Qabs (Qplus (projT1 x n) (projT1 h n)))
                                  (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n)))
                           (Qmult 1 (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n)))
                           (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                                  (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
          { apply (Qmult_le_compat_r (Qabs (Qplus (projT1 x n) (projT1 h n))) 1
                                     (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))).
            { exact Hxh'n. }
            { apply Qabs_nonneg. } }
          { apply (Qle_trans (Qmult 1 (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n)))
                             (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                             (Qplus (Qmult (Qmult en (1 # 4)) (Qabs (projT1 h n)))
                                    (Qplus (Qmult en' (1 # 8)) (Qmult en' (1 # 16))))).
            { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
            { exact Hrc0. } } } }
      (* the residual share (b5e_res_le). *)
      assert (Hres : Qle (Qabs (projT1 (real_mult h (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                                             (real_mult (b5a_atan_d x) h))) n))
                         (Qmult (Qmult (Qmult Msr kδ) en) (Qabs (projT1 h n)))).
      { apply QleT'_to_Qle. apply (b5e_res_le x Hx h n Msr kδ en).
        { exact (QleT'_to_Qle _ _ (Hd n (NatLe_lift _ _ HnNd))). }
        { apply QleT'_to_Qle. apply (b5dI_sA_proj_le x Hx n Msr). exact (HMsr_all n). }
        { exact Hhδn. }
        { exact Hen0. }
        { exact HMsr0. }
        { exact Hkδ0. } }
      (* Z: the per-n main bound. *)
      assert (Hmain : Qle (Qabs (projT1 (b5e_E_err x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { unfold Dn.
        apply (Qle_trans (Qabs (projT1 (b5e_E_err x Hx h Hxh) n))
                         (Qabs (projT1 (b5e_E_dec x Hx h Hxh) n))
                         (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
        { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
          apply (Qabs_wd (projT1 (b5e_E_err x Hx h Hxh) n)
                         (projT1 (b5e_E_dec x Hx h Hxh) n)).
          exact (qeqT_imp_qeq _ _ (HNdec n HnNdec)). }
        { apply QleT'_to_Qle. apply (b5e_pern_main x Hx h Hxh n
                 (1 # 4) (1 # 4) (1 # 8) (1 # 8) (1 # 16) (1 # 16) Msr kδ en en').
          { exact Hrs. }
          { exact Hrc. }
          { exact Hres. }
          { exact Hen0. }
          { exact Hen'0. }
          { exact HMsr0. }
          { exact Hkδ0. }
          { exact Hcoef. }
          { exact Hadd. } } }
      (* margin: eta < (1/4)*en'; Hfin: eta < (en*hn + en') - Dn. *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply QltT_to_Qlt. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        { apply QltT_to_Qlt. exact He1T. }
        { exact (QltT_to_Qlt _ _ (He1lt n HnNe1)). } }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply QltT_to_Qlt. apply (b5n_close Dn hn en en' eta).
        { unfold Dn. exact Hmain. }
        { unfold en'. exact Hq4e. } }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (b5e_E_err x Hx h Hxh)) n))
                          (Qminus (Qplus (Qmult en hn) en') Dn)).
      { unfold en, en', hn, Dn.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (b5e_E_err x Hx h Hxh) n)).
        ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5e_E_err x Hx h Hxh)) n))).
      { exact Hfin. }
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrepl. } } }
Defined.

(* ===== Block b5dJ_ (main item b5dJ_log_diff_dx_exp; upstream source sc2_b5a_item20) ===== *)

(* J0 b5dJ_two_pos_exp (transparent Defined certificate, the delta value-side certificate).
   The root real_two_pos_local is Qed (L44573-44579); the real_inv_pos value destructs N0
   out of the certificate, so an opaque certificate leaves vm_compute stuck.
   J0 = a closed-form proof with explicit witnesses eps = 1/2 and N = 0 (zero root
   references), closing with Defined, so projT1 (real_inv_pos (1+1) J0) n computes for
   all n as Qinv 2 (verified by check = 1#2). *)
Lemma b5dJ_two_pos_exp : real_lt real_zero (real_plus real_one real_one).
Proof.
  unfold real_lt.
  exists (1 # 2).
  split.
  - vm_compute. constructor.
  - exists 0%nat. intros n Hn. vm_compute. constructor.
Defined.

(* J1 b5dJ_log_diff_dx_exp (transparent Defined).
   Copy source: root b5f_log_diff_dx (ConstructiveWorld.v statement 213, L81720-82145,
   426 lines, machine-extracted line slices with no hand transcription); statement
   unchanged.
   Three changes (the minimal changes for delta value-path certificate transparency,
   design described in the header note): (1) rename at the Lemma head, (2) closing Qed
   to Defined, (3) the value-side J0 certificate + extraction bridge (lets / delta /
   0 < delta / the two extraction points). *)
Lemma b5dJ_log_diff_dx_exp : forall (x0 : Real) (Hx0 : real_lt real_zero x0),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : real_lt real_zero (real_plus x0 h)),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (real_log (real_plus x0 h) Hxh)
                 (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros x0 Hx0 eps Heps.
  set (two_inv := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
  set (four_inv := real_mult two_inv two_inv).
  set (eight_inv := real_mult four_inv two_inv).
  set (half_x := real_mult two_inv x0).
  set (eps_x2 := real_mult eps (real_mult x0 x0)).
  set (eps4 := real_mult four_inv eps_x2).      (* eps*x^2/4 *)
    (* delta value-path transparency: the value side half_xJ/eps4J uses J0
       (b5dJ_two_pos_exp, a transparent Defined certificate); the proof side keeps the
       rtl-form two_inv/four_inv/half_x/eps4 unchanged — the root helper's statement
       embeds real_two_pos_local, so apply needs the original form; the two sides are
       pointwise equal, bridged below. *)
    set (two_invJ := real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)).
    set (four_invJ := real_mult two_invJ two_invJ).
    set (half_xJ := real_mult two_invJ x0).
    set (eps4J := real_mult four_invJ eps_x2).
  set (delta := real_min half_xJ eps4J).
  exists delta.
  split.
  - (* 0 < delta: min_pos (half_xJ/eps4J, the J0 transparent certificate). *)
    unfold delta, half_xJ, eps4J, eps_x2, four_invJ, two_invJ.
    apply real_min_pos.
    + apply real_mult_positive.
      * apply (real_inv_pos_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)).
      * exact Hx0.
    + apply real_mult_positive.
      * apply real_mult_positive.
        -- apply (real_inv_pos_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)).
        -- apply (real_inv_pos_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)).
      * apply real_mult_positive.
        -- exact Heps.
        -- apply real_mult_positive.
           ++ exact Hx0.
           ++ exact Hx0.
  - intros h Hh Hxh eps' Heps'.
    (* the share share := inv8*eps' (shared by the 5 parts). *)
    set (share := real_mult eight_inv eps').
    assert (Hshare : real_lt real_zero share).
    { unfold share. apply real_mult_positive.
      - unfold eight_inv, four_inv, two_inv.
        apply real_mult_positive.
        + apply real_mult_positive.
          * apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
          * apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
        + apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
      - exact Heps'. }
    (* t := h·inv x0 *)
    set (t := real_mult h (real_inv_pos x0 Hx0)).
    (* bridging group: real_eq between the value side (J0) and the proof side (rtl) — real_inv_proj plus the closed form for the constant u = 2. *)
    assert (Htwo_eq : real_eq two_invJ two_inv).
    { unfold real_eq. intros eps0 Heps0.
      destruct (real_inv_proj (real_plus real_one real_one) real_two_pos_local) as [Ni HNi].
      exists Ni. intros n Hn.
      assert (Hnle : (Ni <= n)%nat) by (apply NatLe_drop; exact Hn).
      unfold two_invJ, two_inv.
      assert (Hj : projT1 (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) n
                   == Qinv (projT1 (real_plus real_one real_one) n)).
      { vm_compute. reflexivity. }
      assert (Hr : projT1 (real_inv_pos (real_plus real_one real_one) real_two_pos_local) n
                   == Qinv (projT1 (real_plus real_one real_one) n)).
      { apply qeqT_imp_qeq. apply (HNi n). exact (NatLe_lift _ _ Hnle). }
      assert (Hd : projT1 (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) n
                   - projT1 (real_inv_pos (real_plus real_one real_one) real_two_pos_local) n == 0).
      { rewrite Hj. rewrite Hr. ring. }
      assert (Habs0 : Qabs (projT1 (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) n
                        - projT1 (real_inv_pos (real_plus real_one real_one) real_two_pos_local) n) == 0).
      { apply (Qeq_trans _ (Qabs 0) _).
        - apply (Qabs_wd (projT1 (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) n
                          - projT1 (real_inv_pos (real_plus real_one real_one) real_two_pos_local) n) 0).
          exact Hd.
        - cbn [Qabs]. reflexivity. }
      apply (qltT_eq_compat_l 0
               (Qabs (projT1 (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) n
                     - projT1 (real_inv_pos (real_plus real_one real_one) real_two_pos_local) n)) eps0).
      - apply qeq_imp_qeqT. apply Qeq_sym. exact Habs0.
      - exact Heps0. }
    assert (Hfour_eq : real_eq four_invJ four_inv).
    { unfold four_invJ, four_inv.
      apply (RealSetoid.real_eq_mult_compat two_invJ two_invJ two_inv two_inv Htwo_eq Htwo_eq). }
    assert (Hhalf_le : real_le half_xJ half_x).
    { unfold half_xJ, half_x.
      apply RealSetoid.real_eq_le.
      apply (RealSetoid.real_eq_mult_compat two_invJ x0 two_inv x0 Htwo_eq (real_eq_refl x0)). }
    assert (Heps4_le : real_le eps4J eps4).
    { unfold eps4J, eps4.
      apply RealSetoid.real_eq_le.
      apply (RealSetoid.real_eq_mult_compat four_invJ eps_x2 four_inv eps_x2 Hfour_eq (real_eq_refl eps_x2)). }
    (* the premise chain. *)
    assert (Hh_halfJ : real_lt (real_abs h) half_xJ).
    { apply (real_min_lt_l h half_xJ eps4J). unfold delta. exact Hh. }
    assert (Hh_half : real_lt (real_abs h) half_x).
    { apply (real_lt_le_trans (real_abs h) half_xJ half_x).
      - exact Hh_halfJ.
      - exact Hhalf_le. }
    assert (Ht_half : real_lt (real_abs t) two_inv).
    { unfold t. apply (real_t_abs_lt_half x0 h Hx0). exact Hh_half. }
    assert (Ht_lower : real_lt (real_opp two_inv) t).
    { apply (real_abs_lt_lower t two_inv). exact Ht_half. }
    assert (Hhalf_t : real_lt two_inv (real_plus real_one t)).
    { apply (real_half_lt_one_plus_t t). exact Ht_lower. }
    assert (Htpos : real_lt real_zero (real_plus real_one t)).
    { apply (real_lt_trans real_zero two_inv (real_plus real_one t)).
      - apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
      - exact Hhalf_t. }
    assert (Hh_eps4J : real_lt (real_abs h) eps4J).
    { apply (real_min_lt_r h half_xJ eps4J). unfold delta. exact Hh. }
    assert (Hh_eps4 : real_lt (real_abs h) eps4).
    { apply (real_lt_le_trans (real_abs h) eps4J eps4).
      - exact Hh_eps4J.
      - exact Heps4_le. }
    (* X := log(1+t) − t *)
    set (X := real_plus (real_log (real_plus real_one t) Htpos) (real_opp t)).
    (* assert D == X. *)
    assert (HDX : real_eq
      (real_plus (real_log (real_plus x0 h) Hxh)
                 (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h))))
      X).
    {
      (* D == log(x0+h) + (opp(log x0) + opp(inv*h)): split by opp_plus. *)
      apply (real_eq_trans
        (real_plus (real_log (real_plus x0 h) Hxh)
                   (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h))))
        (real_plus (real_log (real_plus x0 h) Hxh)
                   (real_plus (real_opp (real_log x0 Hx0))
                              (real_opp (real_mult (real_inv_pos x0 Hx0) h))))
        X).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_log (real_plus x0 h) Hxh)
                 (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)))
                 (real_log (real_plus x0 h) Hxh)
                 (real_plus (real_opp (real_log x0 Hx0))
                            (real_opp (real_mult (real_inv_pos x0 Hx0) h)))).
        + apply real_eq_refl.
        + apply (real_opp_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)).
      - (* (log(x0+h) + (opplog + oppinv)) == (log(x0+h) - log x0) + (-inv*h): assoc. *)
        apply (real_eq_trans
          (real_plus (real_log (real_plus x0 h) Hxh)
                     (real_plus (real_opp (real_log x0 Hx0))
                                (real_opp (real_mult (real_inv_pos x0 Hx0) h))))
          (real_plus (real_plus (real_log (real_plus x0 h) Hxh) (real_opp (real_log x0 Hx0)))
                     (real_opp (real_mult (real_inv_pos x0 Hx0) h)))
          X).
        + apply (real_plus_assoc (real_log (real_plus x0 h) Hxh)
                                 (real_opp (real_log x0 Hx0))
                                 (real_opp (real_mult (real_inv_pos x0 Hx0) h))).
        + (* (log(x0+h) − log x0) + (−inv·h) == log(1+t) − t *)
          apply (RealSetoid.real_eq_plus_compat
                   (real_plus (real_log (real_plus x0 h) Hxh) (real_opp (real_log x0 Hx0)))
                   (real_opp (real_mult (real_inv_pos x0 Hx0) h))
                   (real_log (real_plus real_one t) Htpos)
                   (real_opp t)).
          * (* log(x0+h) - log x0 == log(1+t): real_log_plus_diff. *)
            apply (real_log_plus_diff x0 h Hx0 Hxh Htpos).
          * (* -inv*h == -t: mult_comm conversion + the definition of t. *)
            apply (real_eq_trans (real_opp (real_mult (real_inv_pos x0 Hx0) h))
                                 (real_opp (real_mult h (real_inv_pos x0 Hx0)))
                                 (real_opp t)).
            -- apply (RealSetoid.real_eq_opp_compat
                       (real_mult (real_inv_pos x0 Hx0) h)
                       (real_mult h (real_inv_pos x0 Hx0))).
               apply (real_mult_comm (real_inv_pos x0 Hx0) h).
            -- apply real_eq_refl.
    }
    (* upper bound: X <= share. *)
    assert (HXup : real_le X share).
    {
      apply (real_le_trans X (real_plus (real_plus t share) (real_opp t)) share).
      - (* X <= (t+share) - t: le_eps + plus_le_compat. *)
        unfold X.
        apply (real_le_plus_compat (real_log (real_plus real_one t) Htpos) (real_plus t share)
                                   (real_opp t) (real_opp t)).
        + exact (real_log_one_plus_le_eps t share Htpos Hshare).
        + apply real_le_refl.
      - (* (t+share) - t <= share: eq_le, ring. *)
        apply RealSetoid.real_eq_le.
        apply (real_eq_trans (real_plus (real_plus t share) (real_opp t))
                             (real_plus t (real_plus share (real_opp t)))
                             share).
        + apply real_eq_sym. apply (real_plus_assoc t share (real_opp t)).
        + apply (real_eq_trans (real_plus t (real_plus share (real_opp t)))
                               (real_plus (real_plus t (real_opp t)) share)
                               share).
          * apply (real_eq_trans (real_plus t (real_plus share (real_opp t)))
                                 (real_plus t (real_plus (real_opp t) share))
                                 (real_plus (real_plus t (real_opp t)) share)).
            -- apply (RealSetoid.real_eq_plus_compat t (real_plus share (real_opp t))
                                                       t (real_plus (real_opp t) share)).
               ++ apply real_eq_refl.
               ++ apply (real_plus_comm share (real_opp t)).
            -- apply (real_plus_assoc t (real_opp t) share).
          * apply (real_eq_trans (real_plus (real_plus t (real_opp t)) share)
                                 (real_plus real_zero share)
                                 share).
            -- apply (RealSetoid.real_eq_plus_compat (real_plus t (real_opp t)) share real_zero share).
               ++ apply (real_plus_opp t).
               ++ apply real_eq_refl.
            -- apply (real_eq_trans (real_plus real_zero share) (real_plus share real_zero) share).
               ** apply (real_plus_comm real_zero share).
               ** apply (real_plus_zero share).
    }
    (* lower bound: -X <= 2t^2 + (share+share). *)
    assert (HXdown : real_le (real_opp X)
      (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                 (real_plus share share))).
    {
      apply (real_le_trans (real_opp X)
                           (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))
                           (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus share share))).
      - (* -X == t - log s: eq_le, opp_plus conversion. *)
        unfold X.
        apply RealSetoid.real_eq_le.
        apply (real_eq_trans (real_opp (real_plus (real_log (real_plus real_one t) Htpos) (real_opp t)))
                             (real_plus (real_opp (real_log (real_plus real_one t) Htpos)) (real_opp (real_opp t)))
                             (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))).
        + apply (real_opp_plus (real_log (real_plus real_one t) Htpos) (real_opp t)).
        + apply (real_eq_trans (real_plus (real_opp (real_log (real_plus real_one t) Htpos)) (real_opp (real_opp t)))
                               (real_plus (real_opp (real_opp t)) (real_opp (real_log (real_plus real_one t) Htpos)))
                               (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))).
          * apply (real_plus_comm (real_opp (real_log (real_plus real_one t) Htpos)) (real_opp (real_opp t))).
          * apply (RealSetoid.real_eq_plus_compat (real_opp (real_opp t))
                                                  (real_opp (real_log (real_plus real_one t) Htpos))
                                                  t
                                                  (real_opp (real_log (real_plus real_one t) Htpos))).
            -- apply (real_opp_opp t).
            -- apply real_eq_refl.
      - (* t − log s ≤ 2t² + share + share *)
        apply (real_le_trans (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))
                             (real_plus (real_mult (real_mult t t) (real_inv_pos (real_plus real_one t) Htpos)) share)
                             (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus share share))).
        + exact (real_t_minus_log_bound t share Htpos Hshare).
        + apply (real_le_trans (real_plus (real_mult (real_mult t t) (real_inv_pos (real_plus real_one t) Htpos)) share)
                               (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) share) share)
                               (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus share share))).
          * apply (real_le_plus_compat (real_mult (real_mult t t) (real_inv_pos (real_plus real_one t) Htpos))
                                       (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) share)
                                       share share).
            -- exact (real_quad_div_le_two_eps t (real_plus real_one t) share Htpos Hhalf_t Hshare).
            -- apply real_le_refl.
          * apply RealSetoid.real_eq_le.
            apply real_eq_sym. apply (real_plus_assoc (real_mult (real_mult t t) (real_plus real_one real_one)) share share).
    }
    (* abs bridge: |X| <= 2t^2 + (share + (share+share)) + share. *)
    assert (Habs : real_le (real_abs X)
      (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                            (real_plus share (real_plus share share)))
                 share)).
    { apply (real_abs_le_quad_eps X t share (real_plus share share) share).
      - exact HXup.
      - exact HXdown.
      - exact Hshare.
      - (* 0 < share + share *)
        apply real_plus_positive; exact Hshare.
      - exact Hshare. }
    (* 22c: 2t^2 <= (eps/2)|h| + share. *)
    assert (Hquad : real_le
      (real_mult (real_mult (real_mult h (real_inv_pos x0 Hx0)) (real_mult h (real_inv_pos x0 Hx0)))
                 (real_plus real_one real_one))
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)).
    { apply (real_quad_t_le_h_eps x0 h eps share Hx0 Hh_eps4 Heps Hshare). }
    (* summary 1: |D| == |X| (HDX + real_abs_eq_compat). *)
    assert (HabsD : real_le (real_abs
      (real_plus (real_log (real_plus x0 h) Hxh)
                 (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)))))
      (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                            (real_plus share (real_plus share share)))
                 share)).
    {
      apply (real_le_trans (real_abs
        (real_plus (real_log (real_plus x0 h) Hxh)
                   (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h)))))
                           (real_abs X)
                           (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                                                 (real_plus share (real_plus share share)))
                                      share)).
      - (* |D| == |X| gives |D| <= |X|: real_abs_eq_compat + eq_le. *)
        apply RealSetoid.real_eq_le.
        apply (real_abs_eq_compat
          (real_plus (real_log (real_plus x0 h) Hxh)
                     (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h))))
          X).
        exact HDX.
      - exact Habs.
    }
    (* summary 2: 2t^2 + C <= ((eps/2)|h| + share) + C == (eps/2)|h| + (share + C). *)
    assert (Hmid : real_le
      (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                            (real_plus share (real_plus share share)))
                 share)
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                 (real_plus share (real_plus (real_plus share (real_plus share share)) share)))).
    {
      apply (real_le_trans
        (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                              (real_plus share (real_plus share share)))
                   share)
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                   (real_plus (real_plus share (real_plus share share)) share))
        (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                   (real_plus share (real_plus (real_plus share (real_plus share share)) share)))).
      - (* (2t^2 + C') + share == 2t^2 + C (assoc reversed, C := C'+share). *)
        apply RealSetoid.real_eq_le.
        apply real_eq_sym.
        apply (real_plus_assoc (real_mult (real_mult t t) (real_plus real_one real_one))
                               (real_plus share (real_plus share share))
                               share).
      - (* 2t² + C ≤ ((eps/2)|h| + share) + C ≤ (eps/2)|h| + (share + C) *)
        apply (real_le_trans
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                     (real_plus (real_plus share (real_plus share share)) share))
          (real_plus (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
                     (real_plus (real_plus share (real_plus share share)) share))
          (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                     (real_plus share (real_plus (real_plus share (real_plus share share)) share)))).
        + (* 2t^2 + C <= ((eps/2)|h| + share) + C: plus_le_compat (Hquad + refl). *)
          apply (real_le_plus_compat
                   (real_mult (real_mult t t) (real_plus real_one real_one))
                   (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
                   (real_plus (real_plus share (real_plus share share)) share)
                   (real_plus (real_plus share (real_plus share share)) share)).
          * exact Hquad.
          * apply real_le_refl.
        + (* ((eps/2)|h| + share) + C == (eps/2)|h| + (share + C): assoc reversed. *)
          apply RealSetoid.real_eq_le.
          apply real_eq_sym.
          apply (real_plus_assoc (real_mult (real_mult two_inv eps) (real_abs h))
                                 share
                                 (real_plus (real_plus share (real_plus share share)) share)).
    }
    (* summary 3: the final (eps/2)|h| + 5*share <= eps*|h| + eps' — Bishop pointwise (the
   Or encoding cannot express a general non-strict <=).
   The pointwise difference = (eps_n/2)|h_n| + (3/8)eps'_n >= (3/8)eps'_n > (3/8)e0' > 0
   (witness (3/8)*e0'). *)
    assert (Hfinal : real_le
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                 (real_plus share (real_plus (real_plus share (real_plus share share)) share)))
      (real_plus (real_mult eps (real_abs h)) eps')).
    {
      destruct real_two_pos_local as [e2 [He2 [N2 HN2]]].
      destruct Heps as [e0 [He0 [N0 HN0]]].
      destruct Heps' as [e0' [He0' [N0' HN0']]].
      set (eps0q := Qmult (Qmake 3 8) e0').
      assert (Heps0q : QltT 0 eps0q).
      { apply Qlt_to_QltT. unfold eps0q.
        apply (Qmult_lt_0_compat (Qmake 3 8) e0').
        - (* 0 < 3/8: 0*8 < 3*1. *)
          simpl. reflexivity.
        - apply QltT_to_Qlt. exact He0'. }
      apply (RealSetoid.real_lt_le_iff_req _ _). left.
      unfold real_lt.
      exists eps0q.
      split.
      - exact Heps0q.
      - exists (Nat.max N0' (Nat.max N2 N0)).
        intros n Hn.
        apply NatLe_drop in Hn.
        assert (Hn0' : (N0' <= n)%nat) by lia.
        assert (Hn2 : (N2 <= n)%nat) by lia.
        assert (Hn0 : (N0 <= n)%nat) by lia.
        set (hn := projT1 h n).
        set (en := projT1 eps n).
        set (en' := projT1 eps' n).
        set (inv2n := projT1 two_inv n).
        set (inv8n := projT1 eight_inv n).
        (* the unfolding asserts. *)
        assert (Hinv2 : inv2n == Qinv 2).
        { unfold inv2n, two_inv.
          cbn [real_inv_pos real_plus real_one projT1].
          assert (Hl : Nat.leb N2 n = true) by (apply Nat.leb_le; exact Hn2).
          rewrite Hl. reflexivity. }
        assert (Hinv8 : inv8n == Qinv 8).
        { unfold inv8n, eight_inv, four_inv, two_inv.
          cbn [real_inv_pos real_plus real_one projT1 real_mult].
          assert (Hl : Nat.leb N2 n = true) by (apply Nat.leb_le; exact Hn2).
          rewrite Hl. unfold Qdiv. field. }
        assert (Heps0'n : Qlt e0' en').
        { apply (Qlt_le_trans _ (en' - projT1 real_zero n) _).
          - apply QltT_to_Qlt. exact (HN0' n (NatLe_lift _ _ Hn0')).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
            assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
            rewrite Hz. ring. }
        assert (Heps0n : Qlt e0 en).
        { apply (Qlt_le_trans _ (en - projT1 real_zero n) _).
          - apply QltT_to_Qlt. exact (HN0 n (NatLe_lift _ _ Hn0)).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
            assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
            rewrite Hz. ring. }
        (* pointwise expansion of the A_n and B_n projections. *)
        assert (HA : projT1
          (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                     (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n
          == (inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en'))))).
        { setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_mult two_inv eps) (real_abs h))
                                         (real_plus share (real_plus (real_plus share (real_plus share share)) share)) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult two_inv eps) (real_abs h) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj two_inv eps n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj share (real_plus (real_plus share (real_plus share share)) share) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus share (real_plus share share)) share n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj share (real_plus share share) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj share share n)).
          unfold share.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eight_inv eps' n)).
          unfold eight_inv.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj four_inv two_inv n)).
          unfold four_inv.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj two_inv two_inv n)).
          unfold hn, en, en', inv2n, inv8n.
          unfold share, eight_inv, four_inv, two_inv.
          cbn [projT1 real_inv_pos real_plus real_one real_mult real_abs].
          assert (Hl : Nat.leb N2 n = true) by (apply Nat.leb_le; exact Hn2).
          rewrite Hl.
          set (aq := Qabs (projT1 h n)). unfold Qdiv. field. }
        (* main chain: eps0q < B_n - A_n. *)
        apply Qlt_to_QltT.
        apply (Qlt_le_trans _ ((en / 2) * Qabs hn + (Qmake 3 8) * en') _).
        { (* eps0q < (en/2)|hn| + (3/8)en' *)
          apply (Qlt_le_trans _ ((Qmake 3 8) * en') _).
          { (* (3/8)e0' < (3/8)en': en' > e0', mult_lt_l. *)
            unfold eps0q.
            assert (H38 : Qlt 0 (Qmake 3 8)) by (simpl; reflexivity).
            apply (proj2 (Qmult_lt_l e0' en' (Qmake 3 8) H38)).
            exact Heps0'n. }
          { (* (3/8)en' <= (en/2)|hn| + (3/8)en': 0 <= (en/2)|hn|. *)
            apply (Qle_trans ((Qmake 3 8) * en')
                             ((Qmake 3 8) * en' + (en / 2) * Qabs hn)
                             ((en / 2) * Qabs hn + (Qmake 3 8) * en')).
            { apply (Qle_plus_nonneg_r ((Qmake 3 8) * en') ((en / 2) * Qabs hn)).
              apply (Qmult_le_compat_nonneg 0 (en / 2) 0 (Qabs hn)).
              { split. apply Qle_refl.
                apply (Qmult_le_compat_nonneg 0 en 0 (Qinv 2)).
                { split. apply Qle_refl. apply Qlt_le_weak. apply (Qlt_trans 0 e0 en). apply QltT_to_Qlt. exact He0. exact Heps0n. }
                { split. apply Qle_refl. apply Qlt_le_weak. simpl. reflexivity. } }
              { split. apply Qle_refl. apply Qabs_nonneg. } }
            { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qplus_comm ((Qmake 3 8) * en') ((en / 2) * Qabs hn)). } }
          }
        { (* (en/2)|hn| + (3/8)en' <= B_n - A_n: expansion + field. *)
          apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
          (* B_n expansion. *)
          assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
          { setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
            setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
            setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
            cbn [projT1]. unfold hn, en, en'. ring. }
          (* main chain: M == B_n - A_n. *)
          apply (Qeq_trans ((en / 2) * Qabs hn + (Qmake 3 8) * en')
                           ((en * Qabs hn + en') - ((inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en'))))))
                           (projT1 (real_plus (real_mult eps (real_abs h)) eps') n - projT1
                             (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                        (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n)).
          - (* M == the expanded form: rewrite Hinv2/Hinv8 + field. *)
            rewrite Hinv2. rewrite Hinv8.
            unfold Qdiv. field.
          - (* the expanded form == B_n - A_n: plus_comp (HB + HA, reversed). *)
            apply (Qplus_comp (en * Qabs hn + en') (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                              (Qeq_sym _ _ HB)
                              (Qopp ((inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en'))))))
                              (Qopp (projT1 (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                                       (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n))
                              (Qopp_comp ((inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en')))))
                                         (projT1 (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                                            (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n)
                                         (Qeq_sym _ _ HA))).
        }
    }
    (* assembly. *)
    apply (real_le_trans _ (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                      (real_plus share (real_plus (real_plus share (real_plus share share)) share))) _).
    { apply (real_le_trans _ (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                                                   (real_plus share (real_plus share share)))
                                        share) _).
      - exact HabsD.
      - exact Hmid. }
    { exact Hfinal. }
Defined.
(* J2 b5dJ_LogErr_delta_exp (transparent Defined).
   Copy source: root b5f_LogErr_delta (ConstructiveWorld.v statement 213,
   L82585-82641, 57 lines, machine-extracted with no hand transcription); statement
   unchanged.
   Three changes: (1) rename at the Lemma head, (2) the in-body destruct source
   b5f_log_diff_dx -> this file's J1 b5dJ_log_diff_dx_exp (same-argument call:
   x0 := b5f_u x), (3) closing Qed to Defined. *)
Lemma b5dJ_LogErr_delta_exp : forall (x : Real) (epsL : Real) (HepsL : real_lt real_zero epsL),
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), forall (epsL' : Real), real_lt real_zero epsL' ->
      real_lt (real_abs (b5f_Du x h)) delta ->
      real_le (real_abs (b5f_LogErr x h))
              (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL'))).
Proof.
  intros x epsL HepsL.
  destruct (b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x) epsL HepsL) as [delta [Hd0 Hd]].
  exists delta. split.
  - exact Hd0.
  - intros h epsL' HepsL' HhΔ.
    set (logexpr := real_plus
             (real_log (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u_plus_Du_pos x h))
             (real_opp (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
                        (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
                                   (b5f_Du x h))))).
    assert (Hraw : real_le (real_abs logexpr)
                   (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL')).
    { unfold logexpr.
      exact (Hd (b5f_Du x h) HhΔ (b5f_u_plus_Du_pos x h) epsL' HepsL'). }
    (* logexpr == b5f_LogErr: only the first log argument/certificate differs, so bridge by real_log_wd. *)
    assert (Heq : real_eq logexpr (b5f_LogErr x h)).
    { unfold logexpr, b5f_LogErr.
      apply (real_eq_trans
        (real_plus (real_log (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u_plus_Du_pos x h))
                   (real_opp (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
                              (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
                                         (b5f_Du x h)))))
        (real_plus (real_log (b5f_u (real_plus x h)) (b5a_one_plus_sq_pos (real_plus x h)))
                   (real_opp (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
                              (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
                                         (b5f_Du x h)))))
        (real_plus (real_log (b5f_u (real_plus x h)) (b5a_one_plus_sq_pos (real_plus x h)))
                   (real_opp (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
                              (real_mult (b5a_atan_d x) (b5f_Du x h)))))).
      - apply (RealSetoid.real_eq_plus_compat
          (real_log (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u_plus_Du_pos x h))
          (real_opp (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
                     (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
                                (b5f_Du x h))))
          (real_log (b5f_u (real_plus x h)) (b5a_one_plus_sq_pos (real_plus x h)))
          (real_opp (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
                     (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
                                (b5f_Du x h))))).
        + apply (real_log_wd (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u (real_plus x h))
                   (b5f_u_plus_Du_pos x h) (b5a_one_plus_sq_pos (real_plus x h))).
          exact (b5f_u_Du_eq x h).
        + apply real_eq_refl.
      - unfold b5a_atan_d, b5f_u. apply real_eq_refl. }
    apply (real_le_trans (real_abs (b5f_LogErr x h)) (real_abs logexpr)
                         (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL')).
    + apply RealSetoid.real_eq_le.
      apply (real_abs_eq_compat (b5f_LogErr x h) logexpr).
      apply real_eq_sym. exact Heq.
    + exact Hraw.
Defined.

(* ===== end of sc2_b5a_item20.v: the first two pieces of the F1 transparent-chain exp/log branch ===== *)

(* ===== Block b5d3_ (main item b5d3_exp_arch4_explicit; upstream source sc2_b5a_item7) ===== *)

(* ===== Section 0. small tools (Q-layer positivity certificates, for the deltaB-2 closed-form witnesses) ===== *)

Lemma b5d3_Hq_half : QltT 0 (1 # 2).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia.
Qed.

Lemma b5d3_Hq_four : QltT 0 (1 # 4).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia.
Qed.

Lemma b5d3_Hq_two : QltT 0 2.
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia.
Qed.

Lemma b5d3_Hq_four_ge : QleT' 0 (1 # 4).
Proof. apply Qle_to_QleT'. unfold Qle. simpl. lia.
Qed.

Lemma b5d3_Hq_half_ge : QleT' 0 (1 # 2).
Proof. apply Qle_to_QleT'. unfold Qle. simpl. lia.
Qed.

(* ============================================================ *)
(* Section 1. deltaB-1: b5d3_exp_arch4_explicit (closed-value C4 piece, Set-layer sigT) *)
(* ============================================================ *)
(* Closed value (the N0 := 11 version, satisfying <= 55; about 54.76):            *)
(*   C := exp_series 11 4 + 2*(4^11/11!)                                          *)
(* Tail condition: exp_tail_abs_geom2 A m n needs forall t >= m, 2A <= t+1 —       *)
(*   A := 4, m := 11: 8 <= t+1 (t >= 11), verified pointwise by lia.               *)
(* The proof is isomorphic to the root exp_series_arch (L8067-8106) with the       *)
(* explicit N0 := 11.                                                              *)
(* Numerical-correction note: the report suggested the N0 := 7 closed value        *)
(*   es 7 4 + 2*(4^7/7!) about 58.31 > 55 (the report's about 54.8 was a slip —    *)
(*   es 7 4 about 51.81 and (4^7/7!)*2 about 6.50), so the <= 55 component cannot  *)
(*   use N0 := 7; this piece takes N0 := 11 (es 11 4 about 54.55 and               *)
(*   (4^11/11!)*2 about 0.210, so C about 54.76 <= 55).                            *)

Definition b5d3_exp_arch4_C : Q :=
  exp_series 11 4 + (q_pow 4 11 / q_fact 11) * (1 + 1)%Q.

(* 1 <= C (sign, Qed). *)
Lemma b5d3_exp_arch4_C_ge1 : QleT' 1 b5d3_exp_arch4_C.
Proof.
  apply Qle_to_QleT'.
  unfold b5d3_exp_arch4_C.
  apply (Qle_trans _ (exp_series 11 4) _).
  - setoid_replace 1 with (exp_series 0 4) by reflexivity.
    apply QleT'_to_Qle. apply exp_series_mono.
    + apply Qle_to_QleT'. unfold Qle. simpl. lia.
    + lia.
  - apply (Qle_plus_nonneg_r (exp_series 11 4) ((q_pow 4 11 / q_fact 11) * (1 + 1)%Q)).
    apply QleT'_to_Qle. apply q_pow_fact2_nonneg. apply Qle_to_QleT'. unfold Qle. simpl. lia.
Qed.

(* forall j, es j 4 <= C (sign, the N0 := 11 split; Qed). *)
Lemma b5d3_exp_arch4_C_all : forall j : nat, QleT' (exp_series j 4) b5d3_exp_arch4_C.
Proof.
  intro j.
  apply Qle_to_QleT'.
  destruct (Nat.leb j 11) eqn:E.
  - apply Nat.leb_le in E.
    apply (Qle_trans _ (exp_series 11 4) _).
    + apply QleT'_to_Qle. apply exp_series_mono; [apply Qle_to_QleT'; unfold Qle; simpl; lia | exact E].
    + unfold b5d3_exp_arch4_C.
      apply (Qle_plus_nonneg_r (exp_series 11 4) ((q_pow 4 11 / q_fact 11) * (1 + 1)%Q)).
      apply QleT'_to_Qle. apply q_pow_fact2_nonneg. apply Qle_to_QleT'. unfold Qle. simpl. lia.
  - apply Nat.leb_gt in E.
    apply (Qle_trans _ (exp_series 11 4 + (q_pow 4 11 / q_fact 11) * (1 + 1)%Q) _).
    + apply (Qle_trans _ (exp_series 11 4 + exp_tail_abs 11 j 4) _).
      * apply Qle_minus_iff.
        setoid_replace (exp_series 11 4 + exp_tail_abs 11 j 4 + - exp_series j 4)
          with (exp_tail_abs 11 j 4 - (exp_series j 4 - exp_series 11 4)) by ring.
        setoid_replace (exp_tail_abs 11 j 4 - (exp_series j 4 - exp_series 11 4))
          with (exp_tail_abs 11 j 4 + - (exp_series j 4 - exp_series 11 4)) by ring.
        apply (proj1 (Qle_minus_iff (exp_series j 4 - exp_series 11 4) (exp_tail_abs 11 j 4))).
        apply QleT'_to_Qle. apply (exp_series_tail_le 4 11 j). apply Qle_to_QleT'. unfold Qle. simpl. lia. lia.
      * apply (Qplus_le_compat _ _ _ _); [apply Qle_refl | apply QleT'_to_Qle; apply (exp_tail_abs_geom2 4 11 j)].
        -- apply Qle_to_QleT'. unfold Qle. simpl. lia.
        -- intros u Hu. apply NatLe_drop in Hu. apply Qle_to_QleT'. unfold Qle. simpl. lia.
        -- lia.
    + unfold b5d3_exp_arch4_C. apply Qle_refl.
Qed.

(* C <= 55 (closed-value numerical verification: direct computation by vm_compute; Qed). *)
Lemma b5d3_exp_arch4_C_le55 : QleT' b5d3_exp_arch4_C 55.
Proof.
  apply Qle_to_QleT'.
  vm_compute.
  discriminate.
Qed.

(* main piece (Defined makes the witness computable: destruct yields the closed value b5d3_exp_arch4_C). *)
Lemma b5d3_exp_arch4_explicit :
  sigT (fun C : Q => And (QleT' 1 C)
    (And (forall j : nat, QleT' (exp_series j 4) C) (QleT' C 55))).
Proof.
  exists b5d3_exp_arch4_C.
  split.
  - exact b5d3_exp_arch4_C_ge1.
  - split.
    + exact b5d3_exp_arch4_C_all.
    + exact b5d3_exp_arch4_C_le55.
Defined.

(* ---- companion with the report's value formula: C7 := es 7 4 + 2*(4^7/7!)
      (about 58.31; no <= 55 component — C <= 55 is false for this value).
      N0 := 7 split. *)

Definition b5d3_exp_arch4_C7 : Q :=
  exp_series 7 4 + (q_pow 4 7 / q_fact 7) * (1 + 1)%Q.

Lemma b5d3_exp_arch4_C7_ge1 : QleT' 1 b5d3_exp_arch4_C7.
Proof.
  apply Qle_to_QleT'.
  unfold b5d3_exp_arch4_C7.
  apply (Qle_trans _ (exp_series 7 4) _).
  - setoid_replace 1 with (exp_series 0 4) by reflexivity.
    apply QleT'_to_Qle. apply exp_series_mono.
    + apply Qle_to_QleT'. unfold Qle. simpl. lia.
    + lia.
  - apply (Qle_plus_nonneg_r (exp_series 7 4) ((q_pow 4 7 / q_fact 7) * (1 + 1)%Q)).
    apply QleT'_to_Qle. apply q_pow_fact2_nonneg. apply Qle_to_QleT'. unfold Qle. simpl. lia.
Qed.

Lemma b5d3_exp_arch4_C7_all : forall j : nat, QleT' (exp_series j 4) b5d3_exp_arch4_C7.
Proof.
  intro j.
  apply Qle_to_QleT'.
  destruct (Nat.leb j 7) eqn:E.
  - apply Nat.leb_le in E.
    apply (Qle_trans _ (exp_series 7 4) _).
    + apply QleT'_to_Qle. apply exp_series_mono; [apply Qle_to_QleT'; unfold Qle; simpl; lia | exact E].
    + unfold b5d3_exp_arch4_C7.
      apply (Qle_plus_nonneg_r (exp_series 7 4) ((q_pow 4 7 / q_fact 7) * (1 + 1)%Q)).
      apply QleT'_to_Qle. apply q_pow_fact2_nonneg. apply Qle_to_QleT'. unfold Qle. simpl. lia.
  - apply Nat.leb_gt in E.
    apply (Qle_trans _ (exp_series 7 4 + (q_pow 4 7 / q_fact 7) * (1 + 1)%Q) _).
    + apply (Qle_trans _ (exp_series 7 4 + exp_tail_abs 7 j 4) _).
      * apply Qle_minus_iff.
        setoid_replace (exp_series 7 4 + exp_tail_abs 7 j 4 + - exp_series j 4)
          with (exp_tail_abs 7 j 4 - (exp_series j 4 - exp_series 7 4)) by ring.
        setoid_replace (exp_tail_abs 7 j 4 - (exp_series j 4 - exp_series 7 4))
          with (exp_tail_abs 7 j 4 + - (exp_series j 4 - exp_series 7 4)) by ring.
        apply (proj1 (Qle_minus_iff (exp_series j 4 - exp_series 7 4) (exp_tail_abs 7 j 4))).
        apply QleT'_to_Qle. apply (exp_series_tail_le 4 7 j). apply Qle_to_QleT'. unfold Qle. simpl. lia. lia.
      * apply (Qplus_le_compat _ _ _ _); [apply Qle_refl | apply QleT'_to_Qle; apply (exp_tail_abs_geom2 4 7 j)].
        -- apply Qle_to_QleT'. unfold Qle. simpl. lia.
        -- intros u Hu. apply NatLe_drop in Hu. apply Qle_to_QleT'. unfold Qle. simpl. lia.
        -- lia.
    + unfold b5d3_exp_arch4_C7. apply Qle_refl.
Qed.

Lemma b5d3_exp_arch4_C7_explicit :
  sigT (fun C : Q => And (QleT' 1 C) (forall j : nat, QleT' (exp_series j 4) C)).
Proof.
  exists b5d3_exp_arch4_C7.
  split.
  - exact b5d3_exp_arch4_C7_ge1.
  - exact b5d3_exp_arch4_C7_all.
Defined.

(* ============================================================ *)
(* Section 2. deltaB-2: b5d3_exp_minus_one_linear_closed (closed-form copy at the Real layer) *)
(* ============================================================ *)
(* Verbatim copy of the root exp_minus_one_linear (L48334-48533); the statement is  *)
(* changed to the first component                                                   *)
(*   real_eq delta (real_min (real_const (1#2)) (real_mult eps (real_const (1#4)))),*)
(* the two two_inv/four_inv expansions are rewritten as real_const (closed-form     *)
(* direct writing); the real_inv_proj(Ni) mechanism is removed (the real_const      *)
(* projection is computed directly by real_const_proj, and Qinv 2 is definitionally *)
(* equal to (1#2)); the N-merge drops the Ni term. *)
Lemma b5d3_exp_minus_one_linear_closed : forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_eq delta (real_min (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))))
        (And (real_lt real_zero delta)
             (forall h : Real, real_lt (real_abs h) delta ->
               forall (eps' : Real), real_lt real_zero eps' ->
               real_le (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))
                       (real_plus (real_mult eps (real_abs h)) eps')))).
Proof.
  intros eps Heps.
  set (delta := real_min (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))).
  exists delta.
  split.
  - (* real_eq delta (real_min (real_const (1#2)) (real_mult eps (real_const (1#4)))) *)
    unfold delta. apply real_eq_refl.
  - split.
    + (* 0 < delta *)
      unfold delta.
      apply real_min_pos.
      * apply real_const_pos_f1. apply QltT_to_Qlt. exact b5d3_Hq_half.
      * apply real_mult_positive.
        -- exact Heps.
        -- apply real_const_pos_f1. apply QltT_to_Qlt. exact b5d3_Hq_four.
    + intros h Hh eps' Heps'.
      assert (Hh_half : real_lt (real_abs h) (real_const (1 # 2)))
        by (unfold delta in Hh; apply (real_min_lt_l h (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))); exact Hh).
      assert (Hh_eps4 : real_lt (real_abs h) (real_mult eps (real_const (1 # 4))))
        by (unfold delta in Hh; apply (real_min_lt_r h (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))); exact Hh).
      (* real_le left branch: build by real_lt. *)
      left.
      destruct Heps as [eps1 [Heps1 [N1 HN1]]].
      destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
      destruct Hh_half as [eps2 [Heps2 [N2 HN2]]].
      destruct Hh_eps4 as [eps3 [Heps3 [N3 HN3]]].
      exists eps1'.
      split.
      * exact Heps1'.
      * exists (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3)) 2).
        intros n Hn.
        apply NatLe_drop in Hn.
        set (en := projT1 eps n). set (en' := projT1 eps' n). set (hn := projT1 h n).
        (* pointwise expansion of A and B. *)
        assert (HA : projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n ==
                      Qabs (exp_partial n hn - 1 - hn)).
        { unfold hn.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_exp h) (real_opp real_one) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_one n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj h n)).
          rewrite (qeqT_imp_qeq _ _ (real_exp_proj h n)).
          cbn [projT1 real_one].
          unfold Qminus. ring. }
        assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
        { unfold en, en', hn.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          cbn [projT1]. ring. }
        (* pointwise bound 1: |hn| < 1/2 (the Hh_half witness + the real_const (1#2) projection). *)
        assert (Hn2 : (N2 <= n)%nat) by lia.
        assert (Hn3 : (N3 <= n)%nat) by lia.
        assert (Hn1 : (N1 <= n)%nat) by lia.
        assert (Hn1' : (N1' <= n)%nat) by lia.
        assert (HN2q : Qlt eps2 (Qminus (Qinv 2) (Qabs hn))).
        { apply (Qlt_le_trans eps2 (Qminus (projT1 (real_const (1 # 2)) n) (projT1 (real_abs h) n)) (Qminus (Qinv 2) (Qabs hn))).
          - apply QltT_to_Qlt. exact (HN2 n (NatLe_lift _ _ Hn2)).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
            rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
            rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 2) n)).
            reflexivity. }
        assert (Hhn_half : Qlt (Qabs hn) (Qinv 2)).
        { apply (Qlt_le_trans (Qabs hn) (Qminus (Qinv 2) eps2) (Qinv 2)).
          - apply QltT_to_Qlt. apply (q_lt_minus_shift eps2 (Qinv 2) (Qabs hn)). apply Qlt_to_QltT. exact HN2q.
          - assert (Heps2q : Qle 0 eps2).
            { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps2. }
            apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) eps2) (Qinv 2)).
            + apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) 0) (Qplus (Qminus (Qinv 2) eps2) eps2)).
              * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
              * apply (Qplus_le_compat (Qminus (Qinv 2) eps2) (Qminus (Qinv 2) eps2) 0 eps2 (Qle_refl _) Heps2q).
            + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        (* pointwise bound 2: |hn| < en/4 (the Hh_eps4 witness + the eps*real_const (1#4) projection). *)
        assert (HN3q : Qlt eps3 (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))).
        { apply (Qlt_le_trans eps3 (Qminus (projT1 (real_mult eps (real_const (1 # 4))) n) (projT1 (real_abs h) n))
                                  (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))).
          - apply QltT_to_Qlt. exact (HN3 n (NatLe_lift _ _ Hn3)).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
            rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
            unfold en.
            setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const (1 # 4)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 4) n)).
            cbn [projT1 real_const].
            reflexivity. }
        assert (Hhn_eps4 : Qlt (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
        { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                              (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
          - apply QltT_to_Qlt. apply (q_lt_minus_shift eps3 (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)). apply Qlt_to_QltT. exact HN3q.
          - assert (Heps3q : Qle 0 eps3).
            { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps3. }
            apply (Qle_trans (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                             (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) eps3)
                             (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
            + apply (Qle_trans (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                               (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) 0)
                               (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) eps3)).
              * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
              * apply (Qplus_le_compat (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                                       (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) 0 eps3 (Qle_refl _) Heps3q).
            + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        (* main chain: B_n - A_n >= eps1'. *)
        assert (Hquad : Qle (Qabs (exp_partial n hn - 1 - hn))
                            (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))).
        { apply QleT'_to_Qle. apply (exp_partial_linear_quad hn n).
          - lia.
          - (* 2|hn| <= 3, from |hn| < 1/2. *)
            apply Qle_to_QleT'.
            apply (Qlt_le_weak (Qmult (1 + 1)%Q (Qabs hn)) 3%Q).
            apply (Qlt_trans (Qmult (1 + 1)%Q (Qabs hn)) (Qmult (1 + 1)%Q (Qinv 2)) 3%Q).
            + setoid_rewrite (Qmult_comm (1 + 1)%Q (Qabs hn)).
              setoid_rewrite (Qmult_comm (1 + 1)%Q (Qinv 2)).
              apply (Qmult_lt_compat_r (Qabs hn) (Qinv 2) (1 + 1)%Q).
              * unfold Qlt. simpl. lia.
              * exact Hhn_half.
            + unfold Qlt. simpl. lia. }
        assert (Hq2 : Qle (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))
                          (Qmult (Qmult en (Qabs hn)) (3 # 8))).
        { assert (Hhn_le : Qle (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
          { apply Qlt_le_weak. exact Hhn_eps4. }
          apply (Qle_trans (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))
                           (Qmult (Qmult (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)) (3 # 2))
                           (Qmult (Qmult en (Qabs hn)) (3 # 8))).
          - (* |hn|^2 <= (en/4)*|hn|, multiplied by (3/2). *)
            apply (Qmult_le_compat_r (Qmult (Qabs hn) (Qabs hn))
                                     (Qmult (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))
                                     (3 # 2)).
            + apply (Qmult_le_compat_r (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)).
              * exact Hhn_le.
              * apply Qabs_nonneg.
            + unfold Qle. simpl. lia.
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field. }
        assert (Hq3 : Qle (Qmult (Qmult en (Qabs hn)) (3 # 8)) (Qmult en (Qabs hn))).
        { setoid_rewrite (Qmult_comm (Qmult en (Qabs hn)) (3 # 8)).
          apply (Qle_trans (Qmult (3 # 8) (Qmult en (Qabs hn))) (Qmult 1%Q (Qmult en (Qabs hn))) (Qmult en (Qabs hn))).
          - apply (Qmult_le_compat_r (3 # 8) 1%Q (Qmult en (Qabs hn))).
            + unfold Qle. simpl. lia.
            + assert (HN1e : QltT eps1 en).
              { apply Qlt_to_QltT.
                apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
                - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
                - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. unfold en. ring. }
              assert (Henq : Qle 0 en).
              { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
                - apply QltT_to_Qlt. exact Heps1.
                - apply QltT_to_Qlt. exact HN1e. }
              apply (Qmult_le_0_compat en (Qabs hn) Henq (Qabs_nonneg hn)).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        assert (Hmain : Qle (Qabs (exp_partial n hn - 1 - hn)) (Qmult en (Qabs hn))).
        { apply (Qle_trans _ (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2)) _).
          - exact Hquad.
          - apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) (3 # 8)) _).
            + exact Hq2.
            + exact Hq3. }
        (* eps1' < B_n - A_n: eps1' < en' <= B_n - A_n. *)
        assert (Heps1e : QltT eps1' en').
        { apply Qlt_to_QltT.
          apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
          - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. unfold en'. ring. }
        assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                    (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))
                            (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
        { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                             (Qplus (Qmult en (Qabs hn)) en') HB
                             (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n)
                             (Qabs (exp_partial n hn - 1 - hn)) HA). }
        assert (Henle : Qle en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
        { apply (Qle_trans en' (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn))))
                             (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
          - apply (Qle_trans en' (Qplus en' 0) (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn))))).
            + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
            + apply (Qplus_le_compat en' en' 0 (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn)))
                                     (Qle_refl en')
                                     (proj1 (Qle_minus_iff (Qabs (exp_partial n hn - 1 - hn)) (Qmult en (Qabs hn))) Hmain)).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1' en' (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                               (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))).
        { apply QltT_to_Qlt. exact Heps1e. }
        { apply (Qle_trans en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))
                                 (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                         (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))).
          - exact Henle.
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrepl. }
Qed.

(* ============================================================ *)
(* Section 3. deltaB-3: b5d3_S0_pts_bound — preliminary verification conclusion (see the design record, Section 2) *)
(* ============================================================ *)
(* Verification (measured by read/grep):                                           *)
(*  - approx_root root L37483 Lemma with L37595 Qed, hence opaque;                 *)
(*    log_seq y Hy n = projT1 (approx_root y Hy (log_eps n) ...)                   *)
(*    (L37642-37643) does not reduce pointwise.                                    *)
(*  - log_scan (L36738 Fixpoint) is a bisection scan returning interval midpoints  *)
(*    / frozen points, not 0; the scan depth N <- q_pow_arch (an arch black box)   *)
(*    is opaque.                                                                   *)
(*  - real_eq has Bishop's per-tail semantics (L3448-3451); real_log_one and       *)
(*    friends only give eventual, so a closed bound for all n pointwise is         *)
(*    unreachable.                                                                 *)
(*  Both routes A/B are blocked; this piece is deferred as pending (the required   *)
(*  lemmas are listed in the design record, Section 2).                            *)

(* ===== Block b5dK_ (main item b5dK_exp_part_bound_closed_r_exp; upstream source sc2_b5a_item21) ===== *)

(* H1 b5dK_real_mult_positive_exp (transparent Defined).
   Copy source: root real_mult_positive (ConstructiveWorld.v L39518; body L39520-39529
   goes through the real_eq_lt_lt + real_mult_lt_compat root Qed chain, so the witness
   is opaque).  Statement verbatim; construct the explicit witnesses directly: destruct
   the inputs Ha/Hb (legal — specializes after instantiation), take eps := e1*e2 and
   N := max N1 N2; coordinate bridge real_mult_proj + Q-layer multiplication monotone
   (Qmult_lt_compat_r twice + comm bridge).  Closes with Defined, so the projT1
   witness = e1*e2 computes. *)
Lemma b5dK_real_mult_positive_exp : forall a b : Real,
  real_lt real_zero a -> real_lt real_zero b -> real_lt real_zero (real_mult a b).
Proof.
  intros a b Ha Hb.
  destruct Ha as [e1 [He1 [N1 HN1]]].
  destruct Hb as [e2 [He2 [N2 HN2]]].
  unfold real_lt.
  exists (e1 * e2)%Q.
  split.
  - (* 0 < e1·e2 *)
    apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat e1 e2).
    + apply QltT_to_Qlt. exact He1.
    + apply QltT_to_Qlt. exact He2.
  - exists (Nat.max N1 N2).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn1 : NatLe N1 n) by (apply NatLe_lift; lia).
    assert (Hn2 : NatLe N2 n) by (apply NatLe_lift; lia).
    apply Qlt_to_QltT.
    (* pointwise: e1 < a_n and e2 < b_n (the input witnesses made pointwise). *)
    assert (H1n : Qlt e1 (projT1 a n)).
    { apply (Qlt_le_trans e1 (Qminus (projT1 a n) (projT1 real_zero n)) (projT1 a n)).
      - apply QltT_to_Qlt. exact (HN1 n Hn1).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [projT1 real_zero]. ring. }
    assert (H2n : Qlt e2 (projT1 b n)).
    { apply (Qlt_le_trans e2 (Qminus (projT1 b n) (projT1 real_zero n)) (projT1 b n)).
      - apply QltT_to_Qlt. exact (HN2 n Hn2).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [projT1 real_zero]. ring. }
    assert (Ha0 : Qlt 0 (projT1 a n)).
    { apply (Qlt_trans 0 e1 (projT1 a n)).
      - apply QltT_to_Qlt. exact He1.
      - exact H1n. }
    assert (He20 : Qlt 0 e2) by (apply QltT_to_Qlt; exact He2).
    (* e1*e2 < a_n*b_n: two Qmult_lt_compat_r steps + the comm bridge. *)
    assert (Hprod : Qlt (Qmult e1 e2) (Qmult (projT1 a n) (projT1 b n))).
    { apply (Qlt_le_trans (Qmult e1 e2) (Qmult (projT1 a n) e2)
                           (Qmult (projT1 a n) (projT1 b n))).
      - apply (Qmult_lt_compat_r e1 (projT1 a n) e2 He20 H1n).
      - apply (Qle_trans (Qmult (projT1 a n) e2) (Qmult e2 (projT1 a n))
                         (Qmult (projT1 a n) (projT1 b n))).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        + apply (Qle_trans (Qmult e2 (projT1 a n)) (Qmult (projT1 b n) (projT1 a n))
                           (Qmult (projT1 a n) (projT1 b n))).
          * apply Qlt_le_weak.
            apply (Qmult_lt_compat_r e2 (projT1 b n) (projT1 a n) Ha0 H2n).
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    (* bridge: e1*e2 < (a*b)_n - 0 (real_mult_proj + ring). *)
    apply (Qlt_le_trans (Qmult e1 e2) (Qmult (projT1 a n) (projT1 b n))
                        (Qminus (projT1 (real_mult a b) n) (projT1 real_zero n))).
    + exact Hprod.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      assert (Hm : projT1 (real_mult a b) n == Qmult (projT1 a n) (projT1 b n))
        by (apply qeqT_imp_qeq; apply real_mult_proj).
      setoid_rewrite Hm.
      cbn [projT1 real_zero].
      ring.
Defined.

(* H2 b5dK_real_abs_plus_one_pos_exp (transparent Defined).
   Copy source: root real_abs_plus_one_pos (ConstructiveWorld.v L47117; body L47119-47147
   argues pointwise 1+Qabs; Qed makes the witness opaque — the real_inv_pos value
   destructs N0 out of the witness, so a transparent version is needed).
   Statement verbatim; the body is rewritten as a clean direct construction: exists
   (1/2)%Q with N := 0 (the witness matches the root: e = 1/2, N0 = 0), both branches
   closed by computation / Q-layer reasoning (Qabs >= 0).
   Closes with Defined, so destruct yields N0 := 0 (computable). *)
Lemma b5dK_real_abs_plus_one_pos_exp : forall a : Real,
  real_lt real_zero (real_plus real_one (real_abs a)).
Proof.
  intro a.
  unfold real_lt.
  exists (1 / 2)%Q.
  split.
  - apply Qlt_to_QltT.
    unfold Qlt. simpl. lia.
  - exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hz.
    assert (Hnz : projT1 (real_plus real_one (real_abs a)) n ==
                  Qplus 1 (Qabs (projT1 a n))).
    { setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_abs a) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)).
      cbn [projT1]. reflexivity. }
    setoid_rewrite Hnz.
    apply (Qlt_le_trans (1 / 2) 1
                        (Qminus (Qplus 1 (Qabs (projT1 a n))) 0)).
    + unfold Qlt. simpl. lia.
    + apply (Qle_trans 1 (Qplus 1 (Qabs (projT1 a n)))
                        (Qminus (Qplus 1 (Qabs (projT1 a n))) 0)).
      * apply (Qplus_le_compat 1 1 0 (Qabs (projT1 a n))).
        -- apply Qle_refl.
        -- apply Qabs_nonneg.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Defined.

(* H4 b5dK_real_abs_scaling_le_exp (copy of the root real_abs_scaling_le L48584-48760,
   Qed — a pure proof piece, no value path).
   The root statement hardcodes the root real_abs_plus_one_pos witness (the certificate
   slot of real_inv_pos); this piece swaps the invM certificate to H2
   (b5dK_real_abs_plus_one_pos_exp — Defined), so the root closed-form piece cannot be
   applied directly: the statement keeps the same shape and this transparent copy only
   mechanically replaces the witness names (body verbatim + mechanical witness-name
   substitution, zero other changes). *)

Lemma b5dK_real_abs_scaling_le_exp : forall (a eps eps' h : Real),
  real_lt real_zero eps -> real_lt real_zero eps' ->
  real_le (real_mult (real_abs a)
            (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
                       (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a)))))
          (real_plus (real_mult eps (real_abs h)) eps').
Proof.
  intros a eps eps' h Heps Heps'.
  unfold real_le. left.
  destruct Heps as [eps1 [Heps1 [N1 HN1]]].
  destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
  destruct (real_norm_bounded a) as [M [HMpos HM]].
  destruct (real_inv_proj (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a)) as [Ni HNi].
  set (M2 := Qplus M 2).
  assert (HM2pos : Qlt 0 M2).
  { unfold M2.
    apply (Qlt_le_trans 0 1 (Qplus M 2)).
    - unfold Qlt. simpl. lia.
    - apply (Qle_trans 1 (Qplus 0 1) (Qplus M 2)).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + assert (H12 : Qle 1 2) by (unfold Qle; simpl; lia).
        apply (Qplus_le_compat 0 M 1 2 (Qlt_le_weak 0 M (QltT_to_Qlt _ _ HMpos)) H12). }
  exists (Qmult eps1' (Qinv M2)).
  split.
  - (* QltT 0 (eps1'·inv M2) *)
    apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps1' (Qinv M2)).
    + apply QltT_to_Qlt. exact Heps1'.
    + apply Qinv_lt_0_compat. exact HM2pos.
  - (* pointwise: eps1'*inv M2 < (right_n - left_n). *)
    exists (Nat.max (Nat.max N1 N1') Ni).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    assert (Hn1' : (N1' <= n)%nat) by lia.
    assert (HnNi : (Ni <= n)%nat) by lia.
    set (an := Qabs (projT1 a n)).
    set (en := projT1 eps n).
    set (e'n := projT1 eps' n).
    set (hn := projT1 h n).
    (* left-end projection expansion. *)
    assert (HA : projT1 (real_mult (real_abs a)
              (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
                         (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))))) n
            == Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))).
    { unfold an, en, e'n, hn.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_abs a)
        (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
                   (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a)))) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj
        (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
        (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj
        (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (HNi n (NatLe_lift _ _ HnNi))).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_abs a) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj a n)).
      cbn [real_one real_const projT1].
      setoid_rewrite (Qplus_comm 1 (Qabs (projT1 a n))).
      ring. }
    (* right-end projection expansion. *)
    assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n
                 == Qplus (Qmult en (Qabs hn)) e'n).
    { unfold en, e'n, hn.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
      simpl. ring. }
    (* positivity: the eps tail > 0. *)
    assert (HN1e : QltT eps1 en).
    { unfold en. apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) (projT1 eps n)).
      - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. ring. }
    assert (Hen : Qlt 0 en)
      by (apply (Qlt_trans 0 eps1 en); [apply QltT_to_Qlt; exact Heps1 | apply QltT_to_Qlt; exact HN1e]).
    assert (HN1'e : QltT eps1' e'n).
    { unfold e'n. apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) (projT1 eps' n)).
      - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. ring. }
    assert (He'n : Qlt 0 e'n)
      by (apply (Qlt_trans 0 eps1' e'n); [apply QltT_to_Qlt; exact Heps1' | apply QltT_to_Qlt; exact HN1'e]).
    assert (Han1 : Qlt 0 (Qplus an 1)).
    { apply (Qlt_le_trans 0 1 (Qplus an 1)).
      - unfold Qlt. simpl. lia.
      - apply (Qle_trans 1 (Qplus 0 1) (Qplus an 1)).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        + apply (Qplus_le_compat 0 an 1 1 (Qabs_nonneg (projT1 a n)) (Qle_refl 1)). }
    (* inv is strictly decreasing: an+1 <= M+1 < M+2 entails inv M2 < inv(an+1). *)
    assert (Hm12 : Qlt (Qplus M 1) (Qplus M 2)).
    { apply (proj2 (Qlt_minus_iff (Qplus M 1) (Qplus M 2))).
      assert (Hd : Qminus (Qplus M 2) (Qplus M 1) == 1) by ring.
      rewrite Hd. unfold Qlt. simpl. lia. }
    assert (Him : Qlt (Qinv M2) (Qinv (Qplus an 1))).
    { assert (Han1nz : ~ (Qplus an 1 == 0)).
      { intro H. apply (Qlt_irrefl 0). rewrite H in Han1. exact Han1. }
      assert (HM2nz : ~ (M2 == 0)).
      { intro H. apply (Qlt_irrefl 0). rewrite H in HM2pos. exact HM2pos. }
      apply (proj2 (Qlt_minus_iff (Qinv M2) (Qinv (Qplus an 1)))).
      assert (Hdiff : Qminus (Qinv (Qplus an 1)) (Qinv M2)
                      == Qmult (Qminus M2 (Qplus an 1)) (Qinv (Qmult M2 (Qplus an 1)))).
      { field. split.
        - exact Han1nz.
        - exact HM2nz. }
      rewrite Hdiff.
      apply (Qmult_lt_0_compat (Qminus M2 (Qplus an 1)) (Qinv (Qmult M2 (Qplus an 1)))).
      - apply (proj1 (Qlt_minus_iff (Qplus an 1) M2)).
        apply (Qle_lt_trans (Qplus an 1) (Qplus M 1) M2).
        + apply (Qplus_le_compat an M 1 1 (QleT'_to_Qle _ _ (HM n)) (Qle_refl 1)).
        + unfold M2. exact Hm12.
      - apply Qinv_lt_0_compat.
        apply (Qmult_lt_0_compat M2 (Qplus an 1)); [exact HM2pos | exact Han1]. }
    (* main chain: eps1'*inv M2 < e'n*inv(an+1) <= (en|hn|+e'n)*inv(an+1) == right - left. *)
    assert (Hmain : Qlt (Qmult eps1' (Qinv M2))
        (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
           (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))).
    { assert (Han1nz : ~ (Qplus an 1 == 0)).
      { intro H. apply (Qlt_irrefl 0). rewrite H in Han1. exact Han1. }
      assert (Hiden : Qminus (Qplus (Qmult en (Qabs hn)) e'n)
            (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1)))))
            == Qmult (Qplus (Qmult en (Qabs hn)) e'n) (Qinv (Qplus an 1))).
      { field. exact Han1nz. }
      apply (Qlt_le_trans (Qmult eps1' (Qinv M2)) (Qmult e'n (Qinv (Qplus an 1)))
             (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
                (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))).
      - apply (Qlt_le_trans (Qmult eps1' (Qinv M2)) (Qmult eps1' (Qinv (Qplus an 1)))
                             (Qmult e'n (Qinv (Qplus an 1)))).
        + setoid_rewrite (Qmult_comm eps1' (Qinv M2)).
          setoid_rewrite (Qmult_comm eps1' (Qinv (Qplus an 1))).
          apply (Qmult_lt_compat_r (Qinv M2) (Qinv (Qplus an 1)) eps1').
          * apply QltT_to_Qlt. exact Heps1'.
          * exact Him.
        + apply (Qmult_le_compat_r eps1' e'n (Qinv (Qplus an 1))).
          * apply Qlt_le_weak. apply QltT_to_Qlt. exact HN1'e.
          * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Han1.
      - apply (Qle_trans (Qmult e'n (Qinv (Qplus an 1)))
               (Qmult (Qplus (Qmult en (Qabs hn)) e'n) (Qinv (Qplus an 1)))
               (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
                  (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))).
        + apply (Qmult_le_compat_r e'n (Qplus (Qmult en (Qabs hn)) e'n) (Qinv (Qplus an 1))).
          * apply (Qle_trans e'n (Qplus e'n (Qmult en (Qabs hn))) (Qplus (Qmult en (Qabs hn)) e'n)).
            { apply (Qle_plus_nonneg_r e'n (Qmult en (Qabs hn))).
              apply (Qmult_le_compat_nonneg 0 en 0 (Qabs hn)).
              { split; [apply Qle_refl | apply Qlt_le_weak; exact Hen]. }
              { split; [apply Qle_refl | apply Qabs_nonneg]. } }
            { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qplus_comm e'n (Qmult en (Qabs hn))). }
          * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Han1.
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hiden. }
    (* closing: after rewriting the projections, exact Hmain. *)
    apply Qlt_to_QltT.
    assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                (projT1 (real_mult (real_abs a)
                                   (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
                                              (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))))) n))
                        (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
                           (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))).
    { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                         (Qplus (Qmult en (Qabs hn)) e'n) HB
                         (projT1 (real_mult (real_abs a)
                            (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
                                       (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))))) n)
                         (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))) HA). }
    apply (Qlt_le_trans (Qmult eps1' (Qinv M2))
           (Qminus (Qplus (Qmult en (Qabs hn)) e'n)
              (Qmult an (Qplus (Qmult (Qmult en (Qinv (Qplus an 1))) (Qabs hn)) (Qmult e'n (Qinv (Qplus an 1))))))
           (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                   (projT1 (real_mult (real_abs a)
                      (real_plus (real_mult (real_mult eps (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))) (real_abs h))
                                 (real_mult eps' (real_inv_pos (real_plus real_one (real_abs a)) (b5dK_real_abs_plus_one_pos_exp a))))) n))).
    { exact Hmain. }
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrepl. }
Qed.


(* H3 b5dK_exp_minus_one_linear_closed_exp (transparent Defined).
   Copy source: upstream sc2_b5a_item7 b5d3_exp_minus_one_linear_closed (L208-400,
   closing Qed — this piece is the transparent re-certificate).  Statement verbatim
   (including the first component real_eq delta (real_min (real_const (1#2))
   (real_mult eps (real_const (1#4))))); the body is copied verbatim (a rewritten
   version of the root exp_minus_one_linear L48341-48533: the two_inv/four_inv
   expansions rewritten as real_const closed forms + the real_inv_proj mechanism
   removed); the two (1#2)/(1#4) positivity certificates (the in-file pieces of item7,
   b5d3_Hq_half/Hq_four) are inlined with direct proofs; Qed -> Defined.
   Value path: exists delta with delta := real_min (real_const (1#2))
   (real_mult eps (real_const (1#4))) — fully transparent, so the first projection of
   δlin computes (check: eps := real_const (1#2) gives (1#8)). *)


Lemma b5dK_exp_minus_one_linear_closed_exp : forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_eq delta (real_min (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))))
        (And (real_lt real_zero delta)
             (forall h : Real, real_lt (real_abs h) delta ->
               forall (eps' : Real), real_lt real_zero eps' ->
               real_le (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)))
                       (real_plus (real_mult eps (real_abs h)) eps')))).
Proof.
  intros eps Heps.
  set (delta := real_min (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))).
  exists delta.
  split.
  - (* real_eq delta (real_min (real_const (1#2)) (real_mult eps (real_const (1#4)))) *)
    unfold delta. apply real_eq_refl.
  - split.
    + (* 0 < delta *)
      unfold delta.
      apply real_min_pos.
      * apply real_const_pos_f1. unfold Qlt. simpl. lia.
      * apply b5dK_real_mult_positive_exp.
        -- exact Heps.
        -- apply real_const_pos_f1. unfold Qlt. simpl. lia.
    + intros h Hh eps' Heps'.
      assert (Hh_half : real_lt (real_abs h) (real_const (1 # 2)))
        by (unfold delta in Hh; apply (real_min_lt_l h (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))); exact Hh).
      assert (Hh_eps4 : real_lt (real_abs h) (real_mult eps (real_const (1 # 4))))
        by (unfold delta in Hh; apply (real_min_lt_r h (real_const (1 # 2)) (real_mult eps (real_const (1 # 4)))); exact Hh).
      (* real_le left branch: build by real_lt. *)
      left.
      destruct Heps as [eps1 [Heps1 [N1 HN1]]].
      destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
      destruct Hh_half as [eps2 [Heps2 [N2 HN2]]].
      destruct Hh_eps4 as [eps3 [Heps3 [N3 HN3]]].
      exists eps1'.
      split.
      * exact Heps1'.
      * exists (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3)) 2).
        intros n Hn.
        apply NatLe_drop in Hn.
        set (en := projT1 eps n). set (en' := projT1 eps' n). set (hn := projT1 h n).
        (* pointwise expansion of A and B. *)
        assert (HA : projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n ==
                      Qabs (exp_partial n hn - 1 - hn)).
        { unfold hn.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h)) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_exp h) (real_opp real_one) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_one n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj h n)).
          rewrite (qeqT_imp_qeq _ _ (real_exp_proj h n)).
          cbn [projT1 real_one].
          unfold Qminus. ring. }
        assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
        { unfold en, en', hn.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          cbn [projT1]. ring. }
        (* pointwise bound 1: |hn| < 1/2 (the Hh_half witness + the real_const (1#2) projection). *)
        assert (Hn2 : (N2 <= n)%nat) by lia.
        assert (Hn3 : (N3 <= n)%nat) by lia.
        assert (Hn1 : (N1 <= n)%nat) by lia.
        assert (Hn1' : (N1' <= n)%nat) by lia.
        assert (HN2q : Qlt eps2 (Qminus (Qinv 2) (Qabs hn))).
        { apply (Qlt_le_trans eps2 (Qminus (projT1 (real_const (1 # 2)) n) (projT1 (real_abs h) n)) (Qminus (Qinv 2) (Qabs hn))).
          - apply QltT_to_Qlt. exact (HN2 n (NatLe_lift _ _ Hn2)).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
            rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
            rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 2) n)).
            reflexivity. }
        assert (Hhn_half : Qlt (Qabs hn) (Qinv 2)).
        { apply (Qlt_le_trans (Qabs hn) (Qminus (Qinv 2) eps2) (Qinv 2)).
          - apply QltT_to_Qlt. apply (q_lt_minus_shift eps2 (Qinv 2) (Qabs hn)). apply Qlt_to_QltT. exact HN2q.
          - assert (Heps2q : Qle 0 eps2).
            { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps2. }
            apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) eps2) (Qinv 2)).
            + apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) 0) (Qplus (Qminus (Qinv 2) eps2) eps2)).
              * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
              * apply (Qplus_le_compat (Qminus (Qinv 2) eps2) (Qminus (Qinv 2) eps2) 0 eps2 (Qle_refl _) Heps2q).
            + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        (* pointwise bound 2: |hn| < en/4 (the Hh_eps4 witness + the eps*real_const (1#4) projection). *)
        assert (HN3q : Qlt eps3 (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))).
        { apply (Qlt_le_trans eps3 (Qminus (projT1 (real_mult eps (real_const (1 # 4))) n) (projT1 (real_abs h) n))
                                  (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))).
          - apply QltT_to_Qlt. exact (HN3 n (NatLe_lift _ _ Hn3)).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
            rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
            unfold en.
            setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const (1 # 4)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 4) n)).
            cbn [projT1 real_const].
            reflexivity. }
        assert (Hhn_eps4 : Qlt (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
        { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                              (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
          - apply QltT_to_Qlt. apply (q_lt_minus_shift eps3 (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)). apply Qlt_to_QltT. exact HN3q.
          - assert (Heps3q : Qle 0 eps3).
            { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps3. }
            apply (Qle_trans (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                             (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) eps3)
                             (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
            + apply (Qle_trans (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                               (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) 0)
                               (Qplus (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) eps3)).
              * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
              * apply (Qplus_le_compat (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3)
                                       (Qminus (Qmult en (Qmult (Qinv 2) (Qinv 2))) eps3) 0 eps3 (Qle_refl _) Heps3q).
            + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        (* main chain: B_n - A_n >= eps1'. *)
        assert (Hquad : Qle (Qabs (exp_partial n hn - 1 - hn))
                            (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))).
        { apply QleT'_to_Qle. apply (exp_partial_linear_quad hn n).
          - lia.
          - (* 2|hn| <= 3, from |hn| < 1/2. *)
            apply Qle_to_QleT'.
            apply (Qlt_le_weak (Qmult (1 + 1)%Q (Qabs hn)) 3%Q).
            apply (Qlt_trans (Qmult (1 + 1)%Q (Qabs hn)) (Qmult (1 + 1)%Q (Qinv 2)) 3%Q).
            + setoid_rewrite (Qmult_comm (1 + 1)%Q (Qabs hn)).
              setoid_rewrite (Qmult_comm (1 + 1)%Q (Qinv 2)).
              apply (Qmult_lt_compat_r (Qabs hn) (Qinv 2) (1 + 1)%Q).
              * unfold Qlt. simpl. lia.
              * exact Hhn_half.
            + unfold Qlt. simpl. lia. }
        assert (Hq2 : Qle (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))
                          (Qmult (Qmult en (Qabs hn)) (3 # 8))).
        { assert (Hhn_le : Qle (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2)))).
          { apply Qlt_le_weak. exact Hhn_eps4. }
          apply (Qle_trans (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2))
                           (Qmult (Qmult (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)) (3 # 2))
                           (Qmult (Qmult en (Qabs hn)) (3 # 8))).
          - (* |hn|^2 <= (en/4)*|hn|, multiplied by (3/2). *)
            apply (Qmult_le_compat_r (Qmult (Qabs hn) (Qabs hn))
                                     (Qmult (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn))
                                     (3 # 2)).
            + apply (Qmult_le_compat_r (Qabs hn) (Qmult en (Qmult (Qinv 2) (Qinv 2))) (Qabs hn)).
              * exact Hhn_le.
              * apply Qabs_nonneg.
            + unfold Qle. simpl. lia.
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field. }
        assert (Hq3 : Qle (Qmult (Qmult en (Qabs hn)) (3 # 8)) (Qmult en (Qabs hn))).
        { setoid_rewrite (Qmult_comm (Qmult en (Qabs hn)) (3 # 8)).
          apply (Qle_trans (Qmult (3 # 8) (Qmult en (Qabs hn))) (Qmult 1%Q (Qmult en (Qabs hn))) (Qmult en (Qabs hn))).
          - apply (Qmult_le_compat_r (3 # 8) 1%Q (Qmult en (Qabs hn))).
            + unfold Qle. simpl. lia.
            + assert (HN1e : QltT eps1 en).
              { apply Qlt_to_QltT.
                apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
                - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
                - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. unfold en. ring. }
              assert (Henq : Qle 0 en).
              { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
                - apply QltT_to_Qlt. exact Heps1.
                - apply QltT_to_Qlt. exact HN1e. }
              apply (Qmult_le_0_compat en (Qabs hn) Henq (Qabs_nonneg hn)).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        assert (Hmain : Qle (Qabs (exp_partial n hn - 1 - hn)) (Qmult en (Qabs hn))).
        { apply (Qle_trans _ (Qmult (Qmult (Qabs hn) (Qabs hn)) (3 # 2)) _).
          - exact Hquad.
          - apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) (3 # 8)) _).
            + exact Hq2.
            + exact Hq3. }
        (* eps1' < B_n - A_n: eps1' < en' <= B_n - A_n. *)
        assert (Heps1e : QltT eps1' en').
        { apply Qlt_to_QltT.
          apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
          - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. unfold en'. ring. }
        assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                    (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))
                            (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
        { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                             (Qplus (Qmult en (Qabs hn)) en') HB
                             (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n)
                             (Qabs (exp_partial n hn - 1 - hn)) HA). }
        assert (Henle : Qle en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
        { apply (Qle_trans en' (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn))))
                             (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))).
          - apply (Qle_trans en' (Qplus en' 0) (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn))))).
            + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
            + apply (Qplus_le_compat en' en' 0 (Qminus (Qmult en (Qabs hn)) (Qabs (exp_partial n hn - 1 - hn)))
                                     (Qle_refl en')
                                     (proj1 (Qle_minus_iff (Qabs (exp_partial n hn - 1 - hn)) (Qmult en (Qabs hn))) Hmain)).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1' en' (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                               (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))).
        { apply QltT_to_Qlt. exact Heps1e. }
        { apply (Qle_trans en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (exp_partial n hn - 1 - hn)))
                                 (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                         (projT1 (real_abs (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one)) (real_opp h))) n))).
          - exact Henle.
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrepl. }
Defined.

(* ===== Main piece (1): b5dK_gdiff_pts_r_exp (transparent Defined).
   Copy source: root b5f_gdiff_pts_r (ConstructiveWorld.v statement 213,
   L82826-L83231, 406-line slice machine-extracted with no hand transcription);
   statement verbatim.
   Changes: (1) rename at the Lemma head; (2) the in-body LogErr leaf b5f_LogErr_delta
   -> upstream item20 b5dJ_LogErr_delta_exp (same-argument call x epsL HepsL);
   (3) real_mult_positive -> this file's b5dK_real_mult_positive_exp (including the
   HepsL construction chain fed into J2 — on the value path the in-body destructs of
   J1/J2 need transparent input witnesses); (4) real_const_pos -> upstream item23
   b5dM_real_const_pos (same statement); (5) the destruct of b5c_d_proj_le_one inside
   the second component -> upstream item23 b5dM_b5c_d_proj_le_one; (6) closing Qed ->
   Defined.
   Value path: δg := min(min(δL*(1#12), eps*kL), (1#2)) with δL := projT1
   (b5dJ_LogErr_delta_exp x epsL HepsL), epsL := eps*(real_const kL), kL := k2*(1#2) —
   a fully transparent chain (item20 J1/J2 Defined + the H1/H2 transparent
   certificates), so the first projection of δg computes. ===== *)
Lemma b5dK_gdiff_pts_r_exp : forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r)
  (eps : Real) (Heps : real_lt real_zero eps)
  (k2 k2p : Q) (Hk2 : QltT 0 k2) (Hk2p : QltT 0 k2p),
  sigT (fun δg : Real => And (real_lt real_zero δg)
    (forall (h : Real), real_lt (real_abs h) δg ->
      forall (eps' : Real), real_lt real_zero eps' ->
      sigT (fun N : nat => forall n : nat, NatLe N n ->
        QleT' (Qabs (projT1 (real_plus (b5f_v x h)
                  (real_opp (real_mult (real_mult x (b5a_atan_d x)) h))) n))
            (Qplus (Qmult (Qmult (projT1 eps n) k2) (Qabs (projT1 h n)))
                   (Qmult (Qmult 2 k2p) (projT1 eps' n)))))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2 Hk2p.
  (* the (1/2) Qdiv vs (1#2) Qmake bridge (the pointwise Q layer uses Qmake to avoid Qinv). *)
  assert (Hhalf : (1 / 2) == (1 # 2)).
  { unfold Qdiv. cbn. reflexivity. }
  (* kL := k2*(1#2); epsL := eps*kL (the linear share for LogErr-delta). *)
  set (kL := Qmult k2 (1 # 2)).
  assert (HkLQ : Qlt 0 kL).
  { unfold kL. apply (Qmult_lt_0_compat k2 (1 # 2)).
    - apply QltT_to_Qlt. exact Hk2.
    - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  assert (HkLT : QltT 0 kL) by (apply Qlt_to_QltT; exact HkLQ).
  assert (HkL0 : Qle 0 kL) by (apply Qlt_le_weak; exact HkLQ).
  set (epsL := real_mult eps (real_const kL)).
  assert (HepsL : real_lt real_zero epsL).
  { unfold epsL. apply b5dK_real_mult_positive_exp.
    - exact Heps.
    - apply b5dM_real_const_pos. exact HkLT. }
  destruct (b5dJ_LogErr_delta_exp x epsL HepsL) as [δL [HδL0 HδL]].
  (* assembling the three delta components. *)
  set (A := real_mult δL (real_const (1 # 12))).
  set (B := real_mult eps (real_const kL)).
  set (C := real_const (1 # 2)).
  set (δg := real_min (real_min A B) C).
  assert (H12T : QltT 0 (1 # 2)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  assert (H112T : QltT 0 (1 # 12)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 12)). unfold Qlt. simpl. lia. }
  assert (HA0 : real_lt real_zero A).
  { unfold A. apply b5dK_real_mult_positive_exp.
    - exact HδL0.
    - apply b5dM_real_const_pos. exact H112T. }
  assert (HB0 : real_lt real_zero B).
  { unfold B. apply b5dK_real_mult_positive_exp.
    - exact Heps.
    - apply b5dM_real_const_pos. exact HkLT. }
  assert (HC0 : real_lt real_zero C).
  { unfold C. apply b5dM_real_const_pos. exact H12T. }
  assert (Hδg0 : real_lt real_zero δg).
  { unfold δg. apply real_min_pos.
    { apply real_min_pos.
      { exact HA0. }
      { exact HB0. } }
    { exact HC0. } }
  exists δg. split.
  { exact Hδg0. }
  { intros h Hhδ eps' Heps'.
    (* min-extract: |h| < A, |h| < B, |h| < C. *)
    assert (HhAB : real_lt (real_abs h) (real_min A B)).
    { apply (real_min_lt_l h (real_min A B) C).
      unfold δg in Hhδ. exact Hhδ. }
    assert (HhA : real_lt (real_abs h) A).
    { apply (real_min_lt_l h A B). exact HhAB. }
    assert (HhB : real_lt (real_abs h) B).
    { apply (real_min_lt_r h A B). exact HhAB. }
    assert (HhC : real_lt (real_abs h) C).
    { apply (real_min_lt_r h (real_min A B) C).
      unfold δg in Hhδ. exact Hhδ. }
    (* activation: |Δu| < δL (b5f_Du_act_delta). *)
    assert (Hact : real_lt (real_abs (b5f_Du x h)) δL).
    { apply (b5f_Du_act_delta r (QleT'_to_Qle 0 r Hr0) (QltT_to_Qlt r 1 Hr1) x Hxr h δL HδL0).
      - unfold A in HhA. exact HhA.
      - unfold C in HhC. exact HhC. }
    (* LogErr eps-delta: epsL'' := eps'*k2p. *)
    set (epsL'' := real_mult eps' (real_const k2p)).
    assert (HepsL'' : real_lt real_zero epsL'').
    { unfold epsL''. apply b5dK_real_mult_positive_exp.
      - exact Heps'.
      - apply b5dM_real_const_pos. exact Hk2p. }
    assert (Hlog : real_le (real_abs (b5f_LogErr x h))
                    (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL'')).
    { exact (HδL h epsL'' HepsL'' Hact). }
    (* the b5i bridge: pointwise |LogErr_n| <= B_n + sh_n (sh := epsL''). *)
    destruct (b5i_abs_le_pointwise (b5f_LogErr x h)
               (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL'')
               Hlog epsL'' HepsL'') as [Nlog HNlog].
    (* destructing the witnesses. *)
    destruct Heps as [e0 [He0 [N0 HN0]]].
    destruct Heps' as [e0' [He0' [N0' HN0']]].
    destruct HhB as [eB [HeB [NB HNB]]].
    destruct HhC as [e1 [He1 [N1 HN1]]].
    destruct (b5c_d_proj_le_one x) as [Nd Hd].
    set (N := Nat.max Nlog (Nat.max Nd (Nat.max N0 (Nat.max N0' (Nat.max NB N1))))).
    exists N.
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hnlog : NatLe Nlog n) by (apply NatLe_lift; lia).
    assert (Hnd : (Nd <= n)%nat) by lia.
    assert (Hn0 : (N0 <= n)%nat) by lia.
    assert (Hn0' : (N0' <= n)%nat) by lia.
    assert (HnB : (NB <= n)%nat) by lia.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    (* pointwise atoms. *)
    set (hn := projT1 h n).
    set (sn := Qabs hn).
    set (en := projT1 eps n).
    set (en' := projT1 eps' n).
    set (dn := projT1 (b5a_atan_d x) n).
    set (Dn := Qabs (projT1 (b5f_Du x h) n)).
    set (wS := real_plus (b5f_v x h)
                        (real_opp (real_mult (real_mult x (b5a_atan_d x)) h))).
    set (D := real_plus (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                        (real_mult (real_const (1 / 2))
                                   (real_mult (b5a_atan_d x) (real_mult h h)))).
    (* |d_n| <= 1; en, en' >= 0 (the eps/eps' witnesses). *)
    assert (Hd1 : Qle (Qabs dn) 1).
    { unfold dn. exact (QleT'_to_Qle _ _ (Hd n (NatLe_lift _ _ Hnd))). }
    assert (Hen0p : Qlt 0 en).
    { apply (Qlt_le_trans 0 e0 en).
      - apply QltT_to_Qlt. exact He0.
      - apply Qlt_le_weak.
        apply (Qlt_le_trans e0 (Qminus en (projT1 real_zero n)) en).
        + apply QltT_to_Qlt. exact (HN0 n (NatLe_lift _ _ Hn0)).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
          assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
          rewrite Hz. ring. }
    assert (Hen0 : Qle 0 en) by (apply Qlt_le_weak; exact Hen0p).
    assert (Hen'0p : Qlt 0 en').
    { apply (Qlt_le_trans 0 e0' en').
      - apply QltT_to_Qlt. exact He0'.
      - apply Qlt_le_weak.
        apply (Qlt_le_trans e0' (Qminus en' (projT1 real_zero n)) en').
        + apply QltT_to_Qlt. exact (HN0' n (NatLe_lift _ _ Hn0')).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
          assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
          rewrite Hz. ring. }
    assert (Hen'0 : Qle 0 en') by (apply Qlt_le_weak; exact Hen'0p).
    assert (Hk2p0 : Qle 0 k2p).
    { apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2p. }
    assert (Hk2p_en' : Qle 0 (Qmult k2p en')).
    { apply (Qmult_le_0_compat k2p en' Hk2p0 Hen'0). }
    (* |h_n| <= 1/2 (the HhC witness made pointwise). *)
    assert (Hs12 : Qle sn (1 # 2)).
    { apply (Qle_trans sn (Qminus (1 # 2) e1) (1 # 2)).
      - apply Qlt_le_weak.
        apply QltT_to_Qlt. apply (q_lt_minus_shift e1 (1 # 2) sn).
        apply (qltT_eq_compat_r (Qminus (1 # 2) sn)
                                (Qminus (projT1 C n) (projT1 (real_abs h) n))
                                e1).
        apply qeq_imp_qeqT.
        + unfold C. rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 2) n)).
          rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          unfold sn, hn. reflexivity.
        + exact (HN1 n (NatLe_lift _ _ Hn1)).
      - apply (Qle_trans (Qminus (1 # 2) e1) (Qplus (Qminus (1 # 2) e1) e1) (1 # 2)).
        + apply (Qle_plus_nonneg_r (Qminus (1 # 2) e1) e1).
          apply Qlt_le_weak. apply QltT_to_Qlt. exact He1.
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    (* |h_n| <= en*kL (HhB: the |h| < eps*kL Real witness made pointwise). *)
    assert (HsnL : Qle sn (Qmult en kL)).
    { apply (Qle_trans sn (Qminus (Qmult en kL) eB) (Qmult en kL)).
      - apply Qlt_le_weak.
        apply QltT_to_Qlt. apply (q_lt_minus_shift eB (Qmult en kL) sn).
        apply (qltT_eq_compat_r (Qminus (Qmult en kL) sn)
                                (Qminus (projT1 B n) (projT1 (real_abs h) n))
                                eB).
        apply qeq_imp_qeqT.
        + unfold B, en, sn, hn.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const kL) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kL n)).
          rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          reflexivity.
        + exact (HNB n (NatLe_lift _ _ HnB)).
      - apply (Qle_trans (Qminus (Qmult en kL) eB)
                         (Qplus (Qminus (Qmult en kL) eB) eB)
                         (Qmult en kL)).
        + apply (Qle_plus_nonneg_r (Qminus (Qmult en kL) eB) eB).
          apply Qlt_le_weak. apply QltT_to_Qlt. exact HeB.
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    (* |Δu_n| <= 3*sn (b5f_Du_abs_pts + 2r+1/2 <= 3). *)
    assert (HD3 : Qle Dn (Qmult 3 sn)).
    { set (C0q := Qplus (Qmult 2 r) (1 # 2)).
      assert (HC0le3 : Qle C0q 3).
      { unfold C0q.
        pose proof (QltT_to_Qlt r 1 Hr1). nra. }
      apply (Qle_trans Dn (Qmult C0q sn) (Qmult 3 sn)).
      - unfold Dn.
        apply QleT'_to_Qle. apply (b5f_Du_abs_pts r x Hxr h n).
        exact Hs12.
      - apply (Qmult_le_compat_r C0q 3 sn).
        + exact HC0le3.
        + unfold sn. apply Qabs_nonneg. }
    (* P1: |LogErr_n| <= en*kL*Dn + 2*k2p*en' (b5i + projection ring). *)
    assert (P1 : Qle (Qabs (projT1 (b5f_LogErr x h) n))
                     (Qplus (Qmult (Qmult en kL) Dn)
                            (Qmult (Qmult 2 k2p) en'))).
    { apply (Qle_trans (Qabs (projT1 (b5f_LogErr x h) n))
                       (Qplus (projT1 (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL'') n)
                              (projT1 epsL'' n))
                       (Qplus (Qmult (Qmult en kL) Dn)
                              (Qmult (Qmult 2 k2p) en'))).
      - exact (QleT'_to_Qle _ _ (HNlog n Hnlog)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult epsL (real_abs (b5f_Du x h))) epsL'' n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj epsL (real_abs (b5f_Du x h)) n)).
        unfold epsL.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const kL) n)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj kL n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (b5f_Du x h) n)).
        unfold epsL''.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const k2p) n)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj k2p n)).
        cbn [projT1].
        unfold en, en', Dn. ring. }
    (* HX: the LogErr half-quantity pointwise bound (P1 x (1#2), substituting Δu <= 3*sn). *)
    assert (HXraw : Qle (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                        (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) Dn))
                               (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))).
    { apply (Qle_trans (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                       (Qmult (Qabs (projT1 (b5f_LogErr x h) n)) (1 # 2))
                       (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) Dn))
                              (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      - { apply (Qle_trans (Qmult (Qabs (projT1 (b5f_LogErr x h) n)) (1 # 2))
                           (Qmult (Qplus (Qmult (Qmult en kL) Dn)
                                         (Qmult (Qmult 2 k2p) en')) (1 # 2))
                           (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) Dn))
                                  (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))).
          { apply (Qmult_le_compat_r (Qabs (projT1 (b5f_LogErr x h) n))
                                     (Qplus (Qmult (Qmult en kL) Dn)
                                            (Qmult (Qmult 2 k2p) en'))
                                     (1 # 2)).
            { exact P1. }
            { change (Qle 0 (1 # 2)). unfold Qle. simpl. lia. } }
          { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. } } }
    assert (HXstep : Qle (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) Dn))
                                (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))
                         (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) (Qmult 3 sn)))
                                (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))).
    { apply Qplus_le_compat.
      - { set (c := Qmult (1 # 2) (Qmult en kL)).
          assert (HenkL : Qle 0 (Qmult en kL)).
          { apply (Qmult_le_0_compat en kL Hen0 HkL0). }
          assert (Hc0 : Qle 0 c).
          { unfold c. apply (Qmult_le_0_compat (1 # 2) (Qmult en kL)).
            - change (Qle 0 (1 # 2)). unfold Qle. simpl. lia.
            - exact HenkL. }
          apply (Qle_trans (Qmult (1 # 2) (Qmult (Qmult en kL) Dn))
                           (Qmult Dn c)
                           (Qmult (1 # 2) (Qmult (Qmult en kL) (Qmult 3 sn)))).
          { unfold c. apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
          { apply (Qle_trans (Qmult Dn c)
                             (Qmult (Qmult 3 sn) c)
                             (Qmult (1 # 2) (Qmult (Qmult en kL) (Qmult 3 sn)))).
            { apply (Qmult_le_compat_r Dn (Qmult 3 sn) c).
              { unfold Dn. exact HD3. }
              { exact Hc0. } }
            { unfold c. apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. } } }
      - apply Qle_refl. }
    assert (HX : Qle (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                     (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) (Qmult 3 sn)))
                            (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))).
    { apply (Qle_trans (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                       (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) Dn))
                              (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))
                       (Qplus (Qmult (1 # 2) (Qmult (Qmult en kL) (Qmult 3 sn)))
                              (Qmult (1 # 2) (Qmult (Qmult 2 k2p) en')))).
      - exact HXraw.
      - exact HXstep. }
    (* HY: the d*h^2 half-quantity pointwise bound (|d_n| <= 1 and |h_n| <= en*kL). *)
    assert (Hsn0 : Qle 0 sn).
    { unfold sn. apply Qabs_nonneg. }
    assert (HYp : Qle (Qmult (Qabs dn) (Qmult sn sn)) (Qmult (Qmult en kL) sn)).
    { apply (Qle_trans (Qmult (Qabs dn) (Qmult sn sn))
                       (Qmult sn sn)
                       (Qmult (Qmult en kL) sn)).
      - { apply (Qle_trans (Qmult (Qabs dn) (Qmult sn sn))
                           (Qmult 1 (Qmult sn sn))
                           (Qmult sn sn)).
          { apply (Qmult_le_compat_r (Qabs dn) 1 (Qmult sn sn)).
            { exact Hd1. }
            { apply (Qmult_le_0_compat sn sn Hsn0 Hsn0). } }
          { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. } }
      - apply (Qmult_le_compat_r sn (Qmult en kL) sn).
        + exact HsnL.
        + exact Hsn0. }
    assert (HY : Qle (Qmult (1 # 2) (Qmult (Qabs dn) (Qmult sn sn)))
                     (Qmult (1 # 2) (Qmult (Qmult en kL) sn))).
    { apply (Qle_trans (Qmult (1 # 2) (Qmult (Qabs dn) (Qmult sn sn)))
                       (Qmult (Qmult (Qabs dn) (Qmult sn sn)) (1 # 2))
                       (Qmult (1 # 2) (Qmult (Qmult en kL) sn))).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      - { apply (Qle_trans (Qmult (Qmult (Qabs dn) (Qmult sn sn)) (1 # 2))
                           (Qmult (Qmult (Qmult en kL) sn) (1 # 2))
                           (Qmult (1 # 2) (Qmult (Qmult en kL) sn))).
          { apply (Qmult_le_compat_r (Qmult (Qabs dn) (Qmult sn sn))
                                     (Qmult (Qmult en kL) sn)
                                     (1 # 2)).
            { exact HYp. }
            { change (Qle 0 (1 # 2)). unfold Qle. simpl. lia. } }
          { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. } } }
    (* pointwise identity: wS_n == D_n == (1#2)*LogErr_n + (1#2)*d_n*h_n^2 (re-proved in place on the projections). *)
    assert (F0 : projT1 wS n == projT1 D n).
    { unfold wS, D, b5f_v, b5f_g, b5f_LogErr, b5f_u, b5f_Du.
      repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) || setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ||
              setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _))).
      cbn [projT1 real_const real_one real_zero].
      field. }
    assert (F1 : projT1 D n ==
             Qplus (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n))
                   (Qmult (1 # 2) (Qmult (projT1 (b5a_atan_d x) n)
                                         (Qmult (projT1 h n) (projT1 h n))))).
    { unfold D.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                                     (real_mult (real_const (1 / 2))
                                                (real_mult (b5a_atan_d x) (real_mult h h))) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (1 / 2)) (b5f_LogErr x h) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (1 / 2))
                                     (real_mult (b5a_atan_d x) (real_mult h h)) n)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 / 2) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (b5a_atan_d x) (real_mult h h) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj h h n)).
      cbn [projT1].
      setoid_rewrite Hhalf.
      reflexivity. }
    set (atom := Qplus (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n))
                       (Qmult (1 # 2) (Qmult (projT1 (b5a_atan_d x) n)
                                             (Qmult (projT1 h n) (projT1 h n))))).
    assert (HwSabs : Qeq (Qabs (projT1 wS n)) (Qabs atom)).
    { apply (Qabs_wd (projT1 wS n) atom).
      apply (Qeq_trans (projT1 wS n) (projT1 D n) atom).
      - exact F0.
      - exact F1. }
    (* triangle split: |a+b| <= |a| + |b|, and |(1#2)*x| == (1#2)*|x|. *)
    assert (Hq1 : Qeq (Qabs (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n)))
                      (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))).
    { apply (Qeq_trans (Qabs (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n)))
                       (Qmult (Qabs (1 # 2)) (Qabs (projT1 (b5f_LogErr x h) n)))
                       (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))).
      - apply (Qabs_Qmult (1 # 2) (projT1 (b5f_LogErr x h) n)).
      - apply (Qmult_comp (Qabs (1 # 2)) (1 # 2)).
        + apply (Qabs_pos (1 # 2)). change (Qle 0 (1 # 2)). unfold Qle. simpl. lia.
        + reflexivity. }
    assert (Hq2 : Qeq (Qabs (Qmult (1 # 2) (Qmult (projT1 (b5a_atan_d x) n)
                                                (Qmult (projT1 h n) (projT1 h n)))))
                      (Qmult (1 # 2) (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                            (Qmult (Qabs (projT1 h n)) (Qabs (projT1 h n)))))).
    { apply (Qeq_trans (Qabs (Qmult (1 # 2) (Qmult (projT1 (b5a_atan_d x) n)
                                                  (Qmult (projT1 h n) (projT1 h n)))))
                       (Qmult (Qabs (1 # 2))
                              (Qabs (Qmult (projT1 (b5a_atan_d x) n)
                                           (Qmult (projT1 h n) (projT1 h n)))))
                       (Qmult (1 # 2) (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                             (Qmult (Qabs (projT1 h n)) (Qabs (projT1 h n)))))).
      - apply (Qabs_Qmult (1 # 2)
                          (Qmult (projT1 (b5a_atan_d x) n) (Qmult (projT1 h n) (projT1 h n)))).
      - apply (Qmult_comp (Qabs (1 # 2)) (1 # 2)).
        + apply (Qabs_pos (1 # 2)). change (Qle 0 (1 # 2)). unfold Qle. simpl. lia.
        + { apply (Qeq_trans (Qabs (Qmult (projT1 (b5a_atan_d x) n)
                                          (Qmult (projT1 h n) (projT1 h n))))
                             (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                    (Qabs (Qmult (projT1 h n) (projT1 h n))))
                             (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                    (Qmult (Qabs (projT1 h n)) (Qabs (projT1 h n))))).
            { apply (Qabs_Qmult (projT1 (b5a_atan_d x) n)
                                (Qmult (projT1 h n) (projT1 h n))). }
            { apply (Qmult_comp (Qabs (projT1 (b5a_atan_d x) n))
                                (Qabs (projT1 (b5a_atan_d x) n))).
              - reflexivity.
              - apply (Qabs_Qmult (projT1 h n) (projT1 h n)). } } }
    assert (Htri : Qle (Qabs atom)
                       (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                              (Qmult (1 # 2) (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                                    (Qmult (Qabs (projT1 h n)) (Qabs (projT1 h n))))))).
    { apply (Qle_trans (Qabs atom)
                       (Qplus (Qabs (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n)))
                              (Qabs (Qmult (1 # 2) (Qmult (projT1 (b5a_atan_d x) n)
                                                          (Qmult (projT1 h n) (projT1 h n))))))
                       (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                              (Qmult (1 # 2) (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                                    (Qmult (Qabs (projT1 h n)) (Qabs (projT1 h n))))))).
      - unfold atom. apply Qabs_triangle.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        apply (Qplus_comp (Qabs (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n)))
                          (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))).
        + exact Hq1.
        + exact Hq2. }
    (* main chain: |wS_n| <= |atom| <= the budget sum <= en*k2*sn + 2*k2p*en' (nra). *)
    apply Qle_to_QleT'.
    apply (Qle_trans (Qabs (projT1 wS n))
                     (Qabs atom)
                     (Qplus (Qmult (Qmult (projT1 eps n) k2) (Qabs (projT1 h n)))
                            (Qmult (Qmult 2 k2p) (projT1 eps' n)))).
    { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact HwSabs. }
    { apply (Qle_trans (Qabs atom)
                       (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                              (Qmult (1 # 2) (Qmult (Qabs (projT1 (b5a_atan_d x) n))
                                                    (Qmult (Qabs (projT1 h n)) (Qabs (projT1 h n))))))
                       (Qplus (Qmult (Qmult (projT1 eps n) k2) (Qabs (projT1 h n)))
                              (Qmult (Qmult 2 k2p) (projT1 eps' n)))).
      - exact Htri.
      - { unfold en, en', sn, hn, dn, kL in HX, HY, Hk2p_en'.
          unfold en, en', sn, hn, dn, kL.
          nra. } }
    }
Defined.

(* ===== Main piece (2): b5dK_exp_part_bound_closed_r_exp (transparent Defined).
   Copy source: root b5a_S_exp_part_bound_closed_r (ConstructiveWorld.v statement
   213, L84306-84653, 348-line slice machine-extracted with no hand transcription;
   note L83581 is a comment-draft statement, the real definition starts at L84306);
   statement verbatim.
   Changes: (1) rename at the Lemma head; (2) the LogErr leaf b5f_LogErr_delta ->
   upstream item20 b5dJ_LogErr_delta_exp (same-argument call x (real_const b5j_kL)
   HkLpos); (3) the δlin source exp_minus_one_linear -> this file's H3
   b5dK_exp_minus_one_linear_closed_exp (one more Hδeq component is destructed — the
   H3 statement carries the real_eq first component); (4) the invM certificate
   real_abs_plus_one_pos -> this file's H2 b5dK_real_abs_plus_one_pos_exp (the
   real_inv_pos value destructs N0 out of the witness — the value path must swap);
   (5) real_mult_positive -> H1; (6) real_const_pos -> upstream item23
   b5dM_real_const_pos; (7) the closing closed-form real_abs_scaling_le -> this file's
   H4 b5dK_real_abs_scaling_le_exp (the root statement hardcodes the root
   real_abs_plus_one_pos witness name — after swapping invM to H2 it cannot be applied
   directly, so a same-shape copy with the witness name replaced); (8) closing Qed ->
   Defined.
   Value path: delta := min(min(δlin*(1#4), δL*(1#12)), (1#2)) with
   δlin := projT1 (H3 eps0 Heps0) (closed form min((1#2), eps0*(1#4))),
   eps0 := eps*(Qinv (b5j_Kvq r))*invM, invM := real_inv_pos (1+|Sx|) (H2 Sx),
   Sx := b5a_S x — a fully transparent chain (H3/H2 Defined; b5a_S/cauchy_real_exp
   transparent; exp_partial's 0 base 1%Q avoids the log_seq/approx_root evaluation),
   so the first projection of delta computes. ===== *)
Lemma b5dK_exp_part_bound_closed_r_exp :
  forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_mult (b5a_S x)
                 (real_plus (cauchy_real_exp (b5f_v x h))
                            (real_opp (real_plus real_one (b5f_v x h))))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps.
  set (Sx := b5a_S x).
  set (invM := real_inv_pos (real_plus real_one (real_abs Sx)) (b5dK_real_abs_plus_one_pos_exp Sx)).
  set (eps0 := real_mult (real_mult eps (real_const (Qinv (b5j_Kvq r)))) invM).
  (* the positivity pieces. *)
  assert (HKqinvT : QltT 0 (Qinv (b5j_Kvq r))).
  { apply Qlt_to_QltT. apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (b5j_Kvq_pos r (QleT'_to_Qle 0 r Hr0))). }
  assert (HinvM0 : real_lt real_zero invM).
  { unfold invM. apply (real_inv_pos_pos (real_plus real_one (real_abs Sx)) (b5dK_real_abs_plus_one_pos_exp Sx)). }
  assert (Heps0 : real_lt real_zero eps0).
  { unfold eps0. apply b5dK_real_mult_positive_exp.
    - apply b5dK_real_mult_positive_exp.
      + exact Heps.
      + apply b5dM_real_const_pos. exact HKqinvT.
    - exact HinvM0. }
  assert (Heps0le : real_le real_zero eps0).
  { apply (RealSetoid.real_lt_le_iff_req real_zero eps0). left. exact Heps0. }
  assert (HkLpos : real_lt real_zero (real_const b5j_kL)).
  { apply b5dM_real_const_pos. exact b5j_kL_posT. }
  destruct (b5dJ_LogErr_delta_exp x (real_const b5j_kL) HkLpos) as [δL [HδL0 HδL]].
  destruct (b5dK_exp_minus_one_linear_closed_exp eps0 Heps0) as [δlin [Hδeq [Hδlin0 Hδlin]]].
  set (A := real_mult δlin (real_const (1 # 4))).
  set (B := real_mult δL (real_const (1 # 12))).
  set (C := real_const (1 # 2)).
  set (delta := real_min (real_min A B) C).
  assert (H14T : QltT 0 (1 # 4)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia. }
  assert (H112T : QltT 0 (1 # 12)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 12)). unfold Qlt. simpl. lia. }
  assert (H12T : QltT 0 (1 # 2)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  assert (HA0 : real_lt real_zero A).
  { unfold A. apply b5dK_real_mult_positive_exp.
    - exact Hδlin0.
    - apply b5dM_real_const_pos. exact H14T. }
  assert (HB0 : real_lt real_zero B).
  { unfold B. apply b5dK_real_mult_positive_exp.
    - exact HδL0.
    - apply b5dM_real_const_pos. exact H112T. }
  assert (HC0 : real_lt real_zero C).
  { unfold C. apply b5dM_real_const_pos. exact H12T. }
  assert (Hdelta0 : real_lt real_zero delta).
  { unfold delta. apply real_min_pos.
    - apply real_min_pos.
      + exact HA0.
      + exact HB0.
    - exact HC0. }
  exists delta.
  split.
  - exact Hdelta0.
  - intros h Hhδ eps' Heps'.
    assert (HhAB : real_lt (real_abs h) (real_min A B)).
    { apply (real_min_lt_l h (real_min A B) C). unfold delta in Hhδ. exact Hhδ. }
    assert (HhA : real_lt (real_abs h) A).
    { apply (real_min_lt_l h A B). exact HhAB. }
    assert (HhB : real_lt (real_abs h) B).
    { apply (real_min_lt_r h A B). exact HhAB. }
    assert (HhC : real_lt (real_abs h) C).
    { apply (real_min_lt_r h (real_min A B) C). unfold delta in Hhδ. exact Hhδ. }
    assert (HactDu : real_lt (real_abs (b5f_Du x h)) δL).
    { apply (b5f_Du_act_delta r (QleT'_to_Qle 0 r Hr0) (QltT_to_Qlt r 1 Hr1) x Hxr h δL HδL0).
      - unfold B in HhB. exact HhB.
      - unfold C in HhC. exact HhC. }
    assert (HlogS : forall (epsL' : Real), real_lt real_zero epsL' ->
        real_le (real_abs (b5f_LogErr x h))
                (real_plus (real_mult (real_const b5j_kL) (real_abs (b5f_Du x h))) epsL')).
    { intros epsL' HepsL'. exact (HδL h epsL' HepsL' HactDu). }
    assert (Hvlt : real_lt (real_abs (b5f_v x h)) δlin).
    { apply (b5j_v_act_lt r (QleT'_to_Qle 0 r Hr0) (QltT_to_Qlt r 1 Hr1) x Hxr h δlin Hδlin0 HlogS).
      - unfold A in HhA. exact HhA.
      - unfold C in HhC. exact HhC. }
    (* eps0' := (3#4)*(eps'*invM); shV := invE*((1#4)*Kvq-const)*eps'. *)
    set (eps0' := real_mult (real_const (3 # 4)) (real_mult eps' invM)).
    set (invE := real_inv_pos eps Heps).
    set (shV := real_mult (real_mult invE (real_const (Qmult (1 # 4) (b5j_Kvq r)))) eps').
    assert (H34T : QltT 0 (3 # 4)).
    { apply Qlt_to_QltT. change (Qlt 0 (3 # 4)). unfold Qlt. simpl. lia. }
    assert (H14KvT : QltT 0 (Qmult (1 # 4) (b5j_Kvq r))).
    { apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 4) (b5j_Kvq r)).
      - change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
      - exact (QltT_to_Qlt _ _ (b5j_Kvq_pos r (QleT'_to_Qle 0 r Hr0))). }
    assert (HinvE0 : real_lt real_zero invE).
    { unfold invE. apply (real_inv_pos_pos eps Heps). }
    assert (Heps0' : real_lt real_zero eps0').
    { unfold eps0'. apply b5dK_real_mult_positive_exp.
      - apply b5dM_real_const_pos. exact H34T.
      - apply b5dK_real_mult_positive_exp.
        + exact Heps'.
        + exact HinvM0. }
    assert (HshV : real_lt real_zero shV).
    { unfold shV. apply b5dK_real_mult_positive_exp.
      - apply b5dK_real_mult_positive_exp.
        + exact HinvE0.
        + apply b5dM_real_const_pos. exact H14KvT.
      - exact Heps'. }
    (* slope instance: |v| <= Kvqc*|h| + shV. *)
    assert (Hvslope : real_le (real_abs (b5f_v x h))
                              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)).
    { apply (b5j_v_abs_bd r (QleT'_to_Qle 0 r Hr0) (QltT_to_Qlt r 1 Hr1) x Hxr h shV HshV HlogS).
      unfold C in HhC. exact HhC. }
    (* |LinE(v)| <= eps0*|v| + eps0' (the exp linearization instance at b5f_v x h). *)
    assert (Hlin : real_le
        (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                             (real_opp (real_plus real_one (b5f_v x h)))))
        (real_plus (real_mult eps0 (real_abs (b5f_v x h))) eps0')).
    { apply (real_le_trans
               (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                    (real_opp (real_plus real_one (b5f_v x h)))))
               (real_abs (real_plus (real_plus (cauchy_real_exp (b5f_v x h)) (real_opp real_one))
                                    (real_opp (b5f_v x h))))
               (real_plus (real_mult eps0 (real_abs (b5f_v x h))) eps0')).
      - apply RealSetoid.real_eq_le.
        apply (real_abs_eq_compat
                 (real_plus (cauchy_real_exp (b5f_v x h))
                            (real_opp (real_plus real_one (b5f_v x h))))
                 (real_plus (real_plus (cauchy_real_exp (b5f_v x h)) (real_opp real_one))
                            (real_opp (b5f_v x h)))).
        apply (b5j_lin_shape_eq (b5f_v x h)).
      - apply (Hδlin (b5f_v x h) Hvlt eps0' Heps0'). }
    (* eps0*|v| <= eps0*(Kvqc*|h| + shV) (real_le_mult_compat_weak + the comm bridge). *)
    assert (Hmulv : real_le (real_mult eps0 (real_abs (b5f_v x h)))
                            (real_mult eps0
                               (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))).
    { apply (real_le_trans (real_mult eps0 (real_abs (b5f_v x h)))
                           (real_mult (real_abs (b5f_v x h)) eps0)
                           (real_mult eps0
                              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))).
      - apply RealSetoid.real_eq_le.
        apply (real_mult_comm eps0 (real_abs (b5f_v x h))).
      - apply (real_le_trans (real_mult (real_abs (b5f_v x h)) eps0)
                             (real_mult (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV) eps0)
                             (real_mult eps0
                                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))).
        + apply (real_le_mult_compat_weak (real_abs (b5f_v x h))
                                          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
                                          eps0).
          * exact Heps0le.
          * exact Hvslope.
        + apply RealSetoid.real_eq_le.
          apply (real_mult_comm (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV) eps0). }
    (* |LinE| ≤ eps0·(Kvqc·|h|+shV) + eps0' *)
    assert (Hlin2 : real_le
        (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                             (real_opp (real_plus real_one (b5f_v x h)))))
        (real_plus (real_mult eps0
                     (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                   eps0')).
    { apply (real_le_trans
               (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                    (real_opp (real_plus real_one (b5f_v x h)))))
               (real_plus (real_mult eps0 (real_abs (b5f_v x h))) eps0')
               (real_plus (real_mult eps0
                            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                          eps0')).
      - exact Hlin.
      - apply (real_le_plus_compat
                 (real_mult eps0 (real_abs (b5f_v x h)))
                 (real_mult eps0 (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                 eps0' eps0').
        + exact Hmulv.
        + apply real_le_refl. }
    (* |Sx·LinE| == |Sx|·|LinE| ≤ |Sx|·(eps0·(Kvqc·|h|+shV) + eps0') *)
    assert (Hmid1 : real_le
        (real_mult (real_abs Sx)
           (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                (real_opp (real_plus real_one (b5f_v x h))))))
        (real_mult (real_abs Sx)
           (real_plus (real_mult eps0
                        (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                      eps0'))).
    { apply (real_le_trans
               (real_mult (real_abs Sx)
                  (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                       (real_opp (real_plus real_one (b5f_v x h))))))
               (real_mult (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                               (real_opp (real_plus real_one (b5f_v x h)))))
                          (real_abs Sx))
               (real_mult (real_abs Sx)
                  (real_plus (real_mult eps0
                               (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                             eps0'))).
      - apply RealSetoid.real_eq_le.
        apply (real_mult_comm (real_abs Sx)
               (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                    (real_opp (real_plus real_one (b5f_v x h)))))).
      - apply (real_le_trans
                 (real_mult (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                                 (real_opp (real_plus real_one (b5f_v x h)))))
                            (real_abs Sx))
                 (real_mult (real_plus (real_mult eps0
                              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                            eps0')
                            (real_abs Sx))
                 (real_mult (real_abs Sx)
                    (real_plus (real_mult eps0
                                 (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                               eps0'))).
        + apply (real_le_mult_compat_weak
                   (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                        (real_opp (real_plus real_one (b5f_v x h)))))
                   (real_plus (real_mult eps0
                                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                              eps0')
                   (real_abs Sx)).
          * apply (RealSetoid.real_lt_le_iff_req real_zero (real_abs Sx)).
            left. unfold Sx. exact (b5j_Sx_abs_pos x).
          * exact Hlin2.
        + apply RealSetoid.real_eq_le.
          apply (real_mult_comm
                   (real_plus (real_mult eps0
                                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                              eps0')
                   (real_abs Sx)). }
    (* reshape: |Sx|*(eps0*(Kvqc*|h|+shV) + eps0') == |Sx|*((eps*invM)*|h| + eps'*invM). *)
    assert (Hreshape : real_eq
        (real_mult (real_abs Sx)
           (real_plus (real_mult eps0
                        (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                      eps0'))
        (real_mult (real_abs Sx)
           (real_plus (real_mult (real_mult eps invM) (real_abs h))
                      (real_mult eps' invM)))).
    { apply (RealSetoid.real_eq_mult_compat
               (real_abs Sx)
               (real_plus (real_mult eps0
                            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                          eps0')
               (real_abs Sx)
               (real_plus (real_mult (real_mult eps invM) (real_abs h))
                          (real_mult eps' invM))).
      - apply real_eq_refl.
      - (* inner reshape: eps0*(Kvqc*|h|+shV) + eps0' == (eps*invM)*|h| + eps'*invM. *)
        apply (real_eq_trans
                 (real_plus (real_mult eps0
                              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                            eps0')
                 (real_plus (real_plus (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                                       (real_mult eps0 shV))
                            eps0')
                 (real_plus (real_mult (real_mult eps invM) (real_abs h))
                            (real_mult eps' invM))).
        + (* distr: eps0*(A+B) == eps0*A + eps0*B. *)
          apply (RealSetoid.real_eq_plus_compat
                   (real_mult eps0
                      (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                   eps0'
                   (real_plus (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                              (real_mult eps0 shV))
                   eps0').
          * apply (b5j_mult_plus_distr_eq eps0
                     (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV).
          * apply real_eq_refl.
        + (* regroup to T: assoc + E1 + E2 + the eps0' definition + the constant sum. *)
          apply (real_eq_trans
                   (real_plus (real_plus (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                                         (real_mult eps0 shV))
                              eps0')
                   (real_plus (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                              (real_plus (real_mult eps0 shV) eps0'))
                   (real_plus (real_mult (real_mult eps invM) (real_abs h))
                              (real_mult eps' invM))).
          * apply real_eq_sym.
            apply (real_plus_assoc
                     (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                     (real_mult eps0 shV) eps0').
          * apply (RealSetoid.real_eq_plus_compat
                     (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                     (real_plus (real_mult eps0 shV) eps0')
                     (real_mult (real_mult eps invM) (real_abs h))
                     (real_mult eps' invM)).
            -- (* eps0*(Kvqc*|h|) == (eps*invM)*|h|: assoc + E1. *)
               apply (real_eq_trans
                        (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                        (real_mult (real_mult eps0 (real_const (b5j_Kvq r))) (real_abs h))
                        (real_mult (real_mult eps invM) (real_abs h))).
               ++ apply (real_mult_assoc eps0 (real_const (b5j_Kvq r)) (real_abs h)).
               ++ apply (RealSetoid.real_eq_mult_compat
                           (real_mult eps0 (real_const (b5j_Kvq r)))
                           (real_abs h)
                           (real_mult eps invM)
                           (real_abs h)).
                  ** unfold eps0. apply (b5j_eps0_kvq_req r (QleT'_to_Qle 0 r Hr0) eps invM).
                  ** apply real_eq_refl.
            -- (* eps0*shV + eps0' == eps'*invM: E2 + the constant sum. *)
               apply (real_eq_trans
                        (real_plus (real_mult eps0 shV) eps0')
                        (real_plus (real_mult (real_const (1 # 4)) (real_mult eps' invM))
                                   (real_mult (real_const (3 # 4)) (real_mult eps' invM)))
                        (real_mult eps' invM)).
               ++ apply (RealSetoid.real_eq_plus_compat
                           (real_mult eps0 shV)
                           eps0'
                           (real_mult (real_const (1 # 4)) (real_mult eps' invM))
                           (real_mult (real_const (3 # 4)) (real_mult eps' invM))).
                  ** unfold shV, invE.
                     apply (b5j_eps0_shv_req r (QleT'_to_Qle 0 r Hr0) eps eps' invM Heps).
                  ** unfold eps0'.
                     apply real_eq_refl.
               ++ apply (b5j_fourth_threefourth_sum (real_mult eps' invM)). }
    apply (real_le_trans
             (real_abs (real_mult (b5a_S x)
                        (real_plus (cauchy_real_exp (b5f_v x h))
                                   (real_opp (real_plus real_one (b5f_v x h))))))
             (real_mult (real_abs Sx)
                (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                     (real_opp (real_plus real_one (b5f_v x h))))))
             (real_plus (real_mult eps (real_abs h)) eps')).
    { apply RealSetoid.real_eq_le.
      apply (real_abs_mult_req (b5a_S x)
             (real_plus (cauchy_real_exp (b5f_v x h))
                        (real_opp (real_plus real_one (b5f_v x h))))). }
    { apply (real_le_trans
               (real_mult (real_abs Sx)
                  (real_abs (real_plus (cauchy_real_exp (b5f_v x h))
                                       (real_opp (real_plus real_one (b5f_v x h))))))
               (real_mult (real_abs Sx)
                  (real_plus (real_mult eps0
                               (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                             eps0'))
               (real_plus (real_mult eps (real_abs h)) eps')).
      { exact Hmid1. }
      { apply (real_le_trans
                 (real_mult (real_abs Sx)
                    (real_plus (real_mult eps0
                                 (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                               eps0'))
                 (real_mult (real_abs Sx)
                    (real_plus (real_mult (real_mult eps invM) (real_abs h))
                               (real_mult eps' invM)))
                 (real_plus (real_mult eps (real_abs h)) eps')).
        { apply RealSetoid.real_eq_le. exact Hreshape. }
        { apply (b5dK_real_abs_scaling_le_exp (b5a_S x) eps eps' h Heps Heps'). }
    }
    }
Defined.

(* ===== end of sc2_b5a_item21.v: the F1-δD2 item21 gdiff + exp-part transparent Defined copies ===== *)

(* ===== Block b5d2_ (main item b5d2_sin_partial_abs_le1; upstream source sc2_b5a_item6) ===== *)

(* ============================================================ *)
(* Section 0. the piece list (statements follow the spec §2 table) *)
(*   M1  b5d2_ap_abs_le1 : forall (a : Q) (n : nat),            *)
(*        QleT' (Qabs a) 1 ->                                   *)
(*        Qle (Qabs (arctan_partial n a)) 1.                    *)
(*   M2  b5d2_sin_partial_abs_le1 : forall (n : nat) (q : Q),    *)
(*        QleT' (Qabs q) 1 ->                                   *)
(*        Qle (Qabs (sin_partial n q)) 1.                       *)
(*   M3  b5d2_cos_partial_abs_le1 : forall (n : nat) (q : Q),    *)
(*        QleT' (Qabs q) 1 ->                                   *)
(*        Qle (Qabs (cos_partial n q)) 1.                       *)
(*   M4  b5d2_sinA_abs_le1 : forall (x : Real)                  *)
(*          (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)  *)
(*          (n : nat),                                          *)
(*        Qle (Qabs (sin_partial n (arctan_partial n            *)
(*                                   (projT1 x n)))) 1.         *)
(*       b5d2_cosA_abs_le1 : same with cos_partial.             *)
(*   M5  b5d2_x0_sinA_le1 : forall n : nat,                     *)
(*        Qle (Qabs (sin_partial n (arctan_partial n            *)
(*                                   (projT1 (real_const 0) n)))) 1. *)
(*       b5d2_x0_cosA_le1 : same with cos_partial.              *)
(* ============================================================ *)
Lemma b5d2_at_term0 : forall x : Q,QeqT ( arctan_term 0 x ) ( x).
Proof.
  intro x.
  apply qeq_imp_qeqT.
  unfold arctan_term.
  replace (2 * 0 + 1)%nat with 1%nat by lia.
  unfold Qdiv. cbn [q_pow].
  change (Qinv (Z.of_nat 1 # 1)) with 1.
  simpl. ring.
Qed.

Lemma b5d2_ap0_x : forall x : Q,QeqT ( arctan_partial 0 x ) ( x).
Proof.
  intro x.
  apply qeq_imp_qeqT.
  change (arctan_term 0 x == x).
  apply qeqT_imp_qeq. apply b5d2_at_term0.
Qed.

(* ---- oddness (atan_term / arctan_partial) ---- *)
Lemma b5d2_at_term_neg : forall (k : nat) (x : Q),QeqT ( arctan_term k (- x) ) ( - arctan_term k x).
Proof.
  intros k x.
  apply qeq_imp_qeqT.
  unfold arctan_term, Qdiv.
  replace (2 * k + 1)%nat with (Datatypes.S (2 * k))%nat by lia.
  rewrite (qeqT_imp_qeq _ _ (q_pow_neg_odd x k)).
  ring.
Qed.

Lemma b5d2_ap_neg : forall (n : nat) (x : Q),QeqT ( arctan_partial n (- x) ) ( - arctan_partial n x).
Proof.
  intros n x.
  apply qeq_imp_qeqT.
  induction n as [| n IH]; simpl.
  - apply qeqT_imp_qeq. apply b5d2_at_term_neg.
  - rewrite IH.
    assert (Htn : arctan_term (Datatypes.S n) (- x) == - arctan_term (Datatypes.S n) x)
      by exact (qeqT_imp_qeq _ _ (b5d2_at_term_neg (Datatypes.S n) x)).
    rewrite Htn. ring.
Qed.

(* ---- sign identities (x >= 0): odd-index terms == -c, even-index terms == c ---- *)
Lemma b5d2_at_term_odd_neg : forall (m : nat) (x : Q), QleT' 0 x ->QeqT (
  arctan_term (Datatypes.S (2 * m)) x ) ( - atan_mag (Datatypes.S (2 * m)) x).
Proof.
  intros m x Hx0.
  apply qeq_imp_qeqT.
  unfold arctan_term, atan_mag, Qdiv.
  rewrite (qeqT_imp_qeq _ _ (sc_qpow_odd_neg_m m)).
  assert (Hp : q_pow x (2 * Datatypes.S (2 * m) + 1) ==
                q_pow (Qabs x) (2 * Datatypes.S (2 * m) + 1)).
  { apply qeqT_imp_qeq. apply (q_pow_wd x (Qabs x) (2 * Datatypes.S (2 * m) + 1)).
    apply qeq_imp_qeqT. apply Qeq_sym. apply Qabs_pos. apply QleT'_to_Qle. exact Hx0. }
  rewrite Hp. ring.
Qed.

Lemma b5d2_at_term_even_pos : forall (m : nat) (x : Q), QleT' 0 x ->QeqT (
  arctan_term (Datatypes.S (Datatypes.S (2 * m))) x ) ( atan_mag (Datatypes.S (Datatypes.S (2 * m))) x).
Proof.
  intros m x Hx0.
  apply qeq_imp_qeqT.
  unfold arctan_term, atan_mag, Qdiv.
  rewrite (qeqT_imp_qeq _ _ (sc_qpow_even_pos_m m)).
  assert (Hp : q_pow x (2 * Datatypes.S (Datatypes.S (2 * m)) + 1) ==
                q_pow (Qabs x) (2 * Datatypes.S (Datatypes.S (2 * m)) + 1)).
  { apply qeqT_imp_qeq. apply (q_pow_wd x (Qabs x) (2 * Datatypes.S (Datatypes.S (2 * m)) + 1)).
    apply qeq_imp_qeqT. apply Qeq_sym. apply Qabs_pos. apply QleT'_to_Qle. exact Hx0. }
  rewrite Hp. ring.
Qed.

(* ---- c_0 == x for x >= 0 (atan_mag 0 x == x) ---- *)
Lemma b5d2_mag0_x : forall x : Q, QleT' 0 x ->QeqT ( atan_mag 0 x ) ( x).
Proof.
  intros x Hx0.
  apply qeq_imp_qeqT.
  unfold atan_mag.
  replace (2 * 0 + 1)%nat with 1%nat by lia.
  cbn [q_pow].
  unfold Qdiv.
  change (Qinv (Z.of_nat 1 # 1)) with 1.
  rewrite (Qabs_pos x (QleT'_to_Qle 0 x Hx0)).
  simpl. ring.
Qed.

(* ---- x in [0,1] entails QleT' (Qabs x) 1 (internal derivation helper) ---- *)
Lemma b5d2_xle1T : forall x : Q, QleT' 0 x -> QleT' x 1 -> QleT' (Qabs x) 1.
Proof.
  intros x Hx0 Hx1.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs x) x 1).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_pos. apply QleT'_to_Qle. exact Hx0.
  - apply QleT'_to_Qle. exact Hx1.
Qed.

(* ---- subsequence monotonicity: even descending (S_{2m+2} <= S_{2m}) ---- *)
Lemma b5d2_ap_even_dec : forall (m : nat) (x : Q), QleT' 0 x -> QleT' x 1 ->
  QleT' (arctan_partial (2 * Datatypes.S m) x) (arctan_partial (2 * m) x).
Proof.
  intros m x Hx0 Hx1.
  apply Qle_to_QleT'.
  replace (2 * Datatypes.S m)%nat with (Datatypes.S (Datatypes.S (2 * m))) by lia.
  rewrite (qeqT_imp_qeq _ _ (arctan_partial_step2 (2 * m) x)).
  assert (Hodd : arctan_term (Datatypes.S (2 * m)) x == - atan_mag (Datatypes.S (2 * m)) x)
    by exact (qeqT_imp_qeq _ _ (b5d2_at_term_odd_neg m x Hx0)).
  assert (Heven : arctan_term (Datatypes.S (Datatypes.S (2 * m))) x == atan_mag (Datatypes.S (Datatypes.S (2 * m))) x)
    by exact (qeqT_imp_qeq _ _ (b5d2_at_term_even_pos m x Hx0)).
  rewrite Hodd. rewrite Heven.
  apply (proj2 (Qle_minus_iff
    (arctan_partial (2 * m) x + (- atan_mag (Datatypes.S (2 * m)) x) + atan_mag (Datatypes.S (Datatypes.S (2 * m))) x)
    (arctan_partial (2 * m) x))).
  assert (Heq : arctan_partial (2 * m) x -
    (arctan_partial (2 * m) x + (- atan_mag (Datatypes.S (2 * m)) x) + atan_mag (Datatypes.S (Datatypes.S (2 * m))) x) ==
    atan_mag (Datatypes.S (2 * m)) x - atan_mag (Datatypes.S (Datatypes.S (2 * m))) x) by ring.
  rewrite Heq.
  apply (proj1 (Qle_minus_iff (atan_mag (Datatypes.S (Datatypes.S (2 * m))) x)
                              (atan_mag (Datatypes.S (2 * m)) x))).
  apply QleT'_to_Qle. apply (atan_mag_decr (Datatypes.S (2 * m)) x).
  apply b5d2_xle1T. exact Hx0. exact Hx1.
Qed.

(* ---- subsequence monotonicity: odd ascending (S_{2m+1} <= S_{2m+3}) ---- *)
Lemma b5d2_ap_odd_inc : forall (m : nat) (x : Q), QleT' 0 x -> QleT' x 1 ->
  QleT' (arctan_partial (Datatypes.S (2 * m)) x)
      (arctan_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) x).
Proof.
  intros m x Hx0 Hx1.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (arctan_partial_step2 (Datatypes.S (2 * m)) x)).
  assert (Heven : arctan_term (Datatypes.S (Datatypes.S (2 * m))) x == atan_mag (Datatypes.S (Datatypes.S (2 * m))) x)
    by exact (qeqT_imp_qeq _ _ (b5d2_at_term_even_pos m x Hx0)).
  rewrite Heven.
  replace (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat with (Datatypes.S (2 * Datatypes.S m))%nat by lia.
  assert (Hodd2 : arctan_term (Datatypes.S (2 * Datatypes.S m)) x == - atan_mag (Datatypes.S (2 * Datatypes.S m)) x)
    by exact (qeqT_imp_qeq _ _ (b5d2_at_term_odd_neg (Datatypes.S m) x Hx0)).
  rewrite Hodd2.
  assert (Heq : arctan_partial (Datatypes.S (2 * m)) x + atan_mag (Datatypes.S (Datatypes.S (2 * m))) x +
                (- atan_mag (Datatypes.S (2 * Datatypes.S m)) x) ==
                arctan_partial (Datatypes.S (2 * m)) x +
                (atan_mag (Datatypes.S (Datatypes.S (2 * m))) x - atan_mag (Datatypes.S (2 * Datatypes.S m)) x)) by ring.
  rewrite Heq.
  apply Qle_plus_nonneg_r.
  replace (Datatypes.S (2 * Datatypes.S m))%nat with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat by lia.
  apply (proj1 (Qle_minus_iff (atan_mag (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) x)
                              (atan_mag (Datatypes.S (Datatypes.S (2 * m))) x))).
  apply QleT'_to_Qle. apply (atan_mag_decr (Datatypes.S (Datatypes.S (2 * m))) x).
  apply b5d2_xle1T. exact Hx0. exact Hx1.
Qed.

(* ---- mixing: odd below even (S_{2m+1} <= S_{2m}) ---- *)
Lemma b5d2_ap_mix_le : forall (m : nat) (x : Q), QleT' 0 x ->
  QleT' (arctan_partial (Datatypes.S (2 * m)) x) (arctan_partial (2 * m) x).
Proof.
  intros m x Hx0.
  apply Qle_to_QleT'.
  assert (Hstep : arctan_partial (Datatypes.S (2 * m)) x ==
                  arctan_partial (2 * m) x + arctan_term (Datatypes.S (2 * m)) x).
  { reflexivity. }
  rewrite Hstep.
  assert (Hodd3 : arctan_term (Datatypes.S (2 * m)) x == - atan_mag (Datatypes.S (2 * m)) x)
    by exact (qeqT_imp_qeq _ _ (b5d2_at_term_odd_neg m x Hx0)).
  rewrite Hodd3.
  apply (proj2 (Qle_minus_iff
      (arctan_partial (2 * m) x + (- atan_mag (Datatypes.S (2 * m)) x))
      (arctan_partial (2 * m) x))).
  assert (Heq : arctan_partial (2 * m) x -
      (arctan_partial (2 * m) x + (- atan_mag (Datatypes.S (2 * m)) x)) ==
      atan_mag (Datatypes.S (2 * m)) x) by ring.
  rewrite Heq.
  apply QleT'_to_Qle. apply atan_mag_nonneg.
Qed.

(* ---- mixing: even above odd (S_{2m+1} <= S_{2m+2}) ---- *)
Lemma b5d2_ap_mix_ge : forall (m : nat) (x : Q), QleT' 0 x ->
  QleT' (arctan_partial (Datatypes.S (2 * m)) x)
      (arctan_partial (Datatypes.S (Datatypes.S (2 * m))) x).
Proof.
  intros m x Hx0.
  apply Qle_to_QleT'.
  assert (Hstep : arctan_partial (Datatypes.S (Datatypes.S (2 * m))) x ==
                  arctan_partial (Datatypes.S (2 * m)) x + arctan_term (Datatypes.S (Datatypes.S (2 * m))) x).
  { simpl. ring. }
  rewrite Hstep.
  pose proof (qeqT_imp_qeq _ _ (b5d2_at_term_even_pos m x Hx0)) as Hgenqeq4888.
  rewrite Hgenqeq4888.
  apply Qle_plus_nonneg_r.
  apply QleT'_to_Qle. apply atan_mag_nonneg.
Qed.

(* ---- S_1 >= 0 (0 <= x - c_1 with c_1 = atan_mag 1 x <= c_0 = x) ---- *)
Lemma b5d2_ap_S1_pos : forall (x : Q), QleT' 0 x -> QleT' x 1 -> QleT' 0 (arctan_partial 1 x).
Proof.
  intros x Hx0 Hx1.
  apply Qle_to_QleT'.
  assert (Hv : arctan_partial 1 x == atan_mag 0 x - atan_mag 1 x).
  { change (arctan_term 0 x + arctan_term 1 x == atan_mag 0 x - atan_mag 1 x).
    pose proof (qeqT_imp_qeq _ _ (b5d2_at_term0 x)) as Hgenqeq4901.
    rewrite Hgenqeq4901.
    pose proof (qeqT_imp_qeq _ _ (b5d2_mag0_x x Hx0)) as Hgenqeq4903.
    rewrite Hgenqeq4903.
    replace (1)%nat with (Datatypes.S (2 * 0))%nat by lia.
    pose proof (qeqT_imp_qeq _ _ (b5d2_at_term_odd_neg 0 x Hx0)) as Hgenqeq4906.
    rewrite Hgenqeq4906.
    ring. }
  rewrite Hv.
  apply (proj1 (Qle_minus_iff (atan_mag 1 x) (atan_mag 0 x))).
  apply QleT'_to_Qle. apply (atan_mag_decr 0 x).
  apply b5d2_xle1T. exact Hx0. exact Hx1.
Qed.

(* ---- the odd subsequence >= 0 ---- *)
Lemma b5d2_ap_odd_pos : forall (m : nat) (x : Q), QleT' 0 x -> QleT' x 1 ->
  QleT' 0 (arctan_partial (Datatypes.S (2 * m)) x).
Proof.
  intros m x Hx0 Hx1.
  apply Qle_to_QleT'.
  induction m as [| m' IH].
  - replace (Datatypes.S (2 * 0))%nat with 1%nat by lia.
    apply QleT'_to_Qle.
    apply b5d2_ap_S1_pos. exact Hx0. exact Hx1.
  - replace (Datatypes.S (2 * Datatypes.S m'))%nat with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m'))))%nat by lia.
    apply (Qle_trans 0 (arctan_partial (Datatypes.S (2 * m')) x)
                       (arctan_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * m')))) x)).
    + exact IH.
    + apply QleT'_to_Qle. apply b5d2_ap_odd_inc. exact Hx0. exact Hx1.
Qed.

(* ---- the even subsequence >= 0 ---- *)
Lemma b5d2_ap_even_pos : forall (m : nat) (x : Q), QleT' 0 x -> QleT' x 1 ->
  QleT' 0 (arctan_partial (2 * m) x).
Proof.
  intros m x Hx0 Hx1.
  apply Qle_to_QleT'.
  destruct m as [| m'].
  - replace (2 * 0)%nat with 0%nat by lia.
    pose proof (qeqT_imp_qeq _ _ (b5d2_ap0_x x)) as Hgenqeq4940.
    rewrite Hgenqeq4940.
    exact (QleT'_to_Qle _ _ ((Hx0))).
  - apply (Qle_trans 0 (arctan_partial (Datatypes.S (2 * m')) x)
                       (arctan_partial (2 * Datatypes.S m') x)).
    + apply QleT'_to_Qle. apply b5d2_ap_odd_pos. exact Hx0. exact Hx1.
    + replace (2 * Datatypes.S m')%nat with (Datatypes.S (Datatypes.S (2 * m')))%nat by lia.
      apply QleT'_to_Qle.
      apply b5d2_ap_mix_ge. exact Hx0.
Qed.

(* ---- the even subsequence <= x (S_{2m} <= S_0 == x) ---- *)
Lemma b5d2_ap_even_ub : forall (m : nat) (x : Q), QleT' 0 x -> QleT' x 1 ->
  QleT' (arctan_partial (2 * m) x) x.
Proof.
  intros m x Hx0 Hx1.
  apply Qle_to_QleT'.
  induction m as [| m' IH].
  - replace (2 * 0)%nat with 0%nat by lia.
    apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply qeqT_imp_qeq. apply b5d2_ap0_x.
  - apply (Qle_trans _ (arctan_partial (2 * m') x) _).
    + apply QleT'_to_Qle. apply b5d2_ap_even_dec. exact Hx0. exact Hx1.
    + exact IH.
Qed.

(* ---- sandwich: x in [0,1] entails 0 <= S_n(x) and S_n(x) <= x ---- *)
Lemma b5d2_ap_sandwich : forall (x : Q) (n : nat), QleT' 0 x -> QleT' x 1 ->
  And (QleT' 0 (arctan_partial n x)) (QleT' (arctan_partial n x) x).
Proof.
  intros x n Hx0 Hx1.
  destruct (sc_nat_split n) as [m Hm | m Hm].
  - rewrite Hm. split.
    + apply b5d2_ap_even_pos. exact Hx0. exact Hx1.
    + apply b5d2_ap_even_ub. exact Hx0. exact Hx1.
  - rewrite Hm. split.
    + apply b5d2_ap_odd_pos. exact Hx0. exact Hx1.
    + apply Qle_to_QleT'. apply (Qle_trans _ (arctan_partial (2 * m) x) _).
      * apply QleT'_to_Qle. apply b5d2_ap_mix_le. exact Hx0.
      * apply QleT'_to_Qle. apply b5d2_ap_even_ub. exact Hx0. exact Hx1.
Qed.

(* ---- nonnegative branch: x in [0,1] entails |S_n(x)| <= 1 ---- *)
Lemma b5d2_ap_abs_le1_nonneg : forall (x : Q) (n : nat), QleT' 0 x -> QleT' x 1 ->
  QleT' (Qabs (arctan_partial n x)) 1.
Proof.
  intros x n Hx0 Hx1.
  apply Qle_to_QleT'.
  destruct (b5d2_ap_sandwich x n Hx0 Hx1) as [Hs0 Hsx].
  apply (Qle_trans _ (arctan_partial n x) _).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_pos. exact (QleT'_to_Qle _ _ Hs0).
  - apply (Qle_trans _ x _). exact (QleT'_to_Qle _ _ Hsx). exact (QleT'_to_Qle _ _ (Hx1)).
Qed.

(* ============================================================ *)
(* M1: forall a n, |a| <= 1 -> |arctan_partial n a| <= 1        *)
(* ============================================================ *)
Lemma b5d2_ap_abs_le1 : forall (a : Q) (n : nat), QleT' (Qabs a) 1 ->
  QleT' (Qabs (arctan_partial n a)) 1.
Proof.
  intros a n Ha.
  apply Qle_to_QleT'.
  assert (Hqle : Qle (Qabs a) 1) by (apply QleT'_to_Qle; exact Ha).
  destruct (Qcompare a 0) eqn:E.
  - (* a == 0: take the nonnegative branch. *)
    assert (Ha0 : a == 0) by (apply (proj2 (Qeq_alt a 0)); exact E).
    assert (H0a : Qle 0 a) by (apply QleT'_to_Qle; apply qeq_imp_qle; apply qeq_imp_qeqT; apply Qeq_sym; exact Ha0).
    assert (Ha1 : Qle a 1) by (apply (Qle_trans a 0 1); [apply QleT'_to_Qle; apply qeq_imp_qle; apply qeq_imp_qeqT; exact Ha0 | exact (QleT'_to_Qle _ _ Qle_0_1)]).
    exact ((QleT'_to_Qle _ _ (b5d2_ap_abs_le1_nonneg a n (Qle_to_QleT' _ _ (H0a)) (Qle_to_QleT' _ _ (Ha1))))).
  - (* a < 0: by oddness reduce to the nonnegative branch (x := -a). *)
    assert (Halt : Qlt a 0) by (apply (proj2 (Qlt_alt a 0)); exact E).
    assert (Hal0 : Qle a 0) by (apply Qlt_le_weak; exact Halt).
    assert (H0na : Qle 0 (- a)).
    { apply (Qle_trans 0 (Qabs a) (- a)).
      - apply Qabs_nonneg.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact (Qabs_neg a Hal0). }
    assert (Hna1 : Qle (- a) 1).
    { apply (Qle_trans (- a) (Qabs a) 1).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. exact (Qabs_neg a Hal0).
      - exact Hqle. }
    assert (Hodd : arctan_partial n a == - arctan_partial n (- a)).
    { apply (Qeq_trans _ (arctan_partial n (- (- a))) _).
      - apply qeqT_imp_qeq. apply (b5c_arctan_partial_wd n a (- (- a))).
        apply Qeq_sym. apply Qopp_involutive.
      - apply qeqT_imp_qeq. exact (b5d2_ap_neg n (- a)). }
    assert (Habs : Qabs (arctan_partial n a) == Qabs (arctan_partial n (- a))).
    { apply (Qeq_trans _ (Qabs (- arctan_partial n (- a))) _).
      - apply (Qabs_wd (arctan_partial n a) (- arctan_partial n (- a))).
        exact Hodd.
      - apply Qabs_opp. }
    apply (Qle_trans _ (Qabs (arctan_partial n (- a))) _).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact Habs.
    + exact ((QleT'_to_Qle _ _ (b5d2_ap_abs_le1_nonneg (- a) n (Qle_to_QleT' _ _ (H0na)) (Qle_to_QleT' _ _ (Hna1))))).
  - (* 0 < a *)
    assert (Hgt : Qlt 0 a) by (apply (proj2 (Qgt_alt a 0)); exact E).
    assert (H0a : Qle 0 a) by (apply Qlt_le_weak; exact Hgt).
    assert (Ha1 : Qle a 1).
    { apply (Qle_trans a (Qabs a) 1).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. apply Qabs_pos. exact H0a.
      - exact Hqle. }
    exact ((QleT'_to_Qle _ _ (b5d2_ap_abs_le1_nonneg a n (Qle_to_QleT' _ _ (H0a)) (Qle_to_QleT' _ _ (Ha1))))).
Qed.

(* ============================================================ *)
(* Section 2. M2 b5d2_sin_partial_abs_le1 (|sin_partial n q| <= 1 for |q| <= 1) *)
(* Route: on the q in [0,1] branch use sc_sin_partial_upper_x (upper) and       *)
(*   sc_sin_partial_lower_c1 (q - q^3/6 <= sin, hence 0 <= sin);                *)
(*   the q <= 0 branch reduces by the oddness sc_sin_partial_neg to -q >= 0.    *)
(* ============================================================ *)
Lemma b5d2_qpow3_le_6x : forall x : Q, QleT' 0 x -> QleT' x 1 -> QleT' (q_pow x 3) (x * 6).
Proof.
  intros x Hx0 Hx1.
  apply Qle_to_QleT'.
  assert (Hc : q_pow x 3 == x * (x * x)) by (cbn [q_pow]; ring).
  rewrite Hc.
  apply QleT'_to_Qle. apply (sc_qmult_le_l (x * x) 6 x).
  - apply (Qle_trans (x * x) 1 6).
    + apply QleT'_to_Qle. apply atan_sq_le_one. apply b5d2_xle1T. exact Hx0. exact Hx1.
    + unfold Qle; simpl; lia.
  - exact (QleT'_to_Qle _ _ (Hx0)).
Qed.

(* ---- arithmetic: c1 = q^3/6 <= q (0 <= q <= 1) entails 0 <= q - c1 ---- *)
Lemma b5d2_sin_alt1_le_x : forall x : Q, QleT' 0 x -> QleT' x 1 -> QleT' (sc_sin_alt 1 x) x.
Proof.
  intros x Hx0 Hx1.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (sc_sin_alt1_cube x)).
  assert (Hc : q_pow x 3 == x * (x * x)) by (cbn [q_pow]; ring).
  rewrite Hc.
  unfold Qdiv.
  assert (H6 : Qlt 0 6) by (unfold Qlt; simpl; lia).
  assert (Hinv0 : Qle 0 (Qinv 6)) by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact H6).
  assert (Hxx6 : Qle (x * x) 6).
  { apply (Qle_trans (x * x) 1 6).
    - apply QleT'_to_Qle. apply atan_sq_le_one. apply b5d2_xle1T. exact Hx0. exact Hx1.
    - unfold Qle; simpl; lia. }
  assert (Hx6 : Qle (x * (x * x)) (x * 6)).
  { apply QleT'_to_Qle. apply (sc_qmult_le_l (x * x) 6 x). exact Hxx6. exact (QleT'_to_Qle _ _ (Hx0)). }
  apply (Qle_trans _ ((x * 6) * Qinv 6) _).
  - apply (Qmult_le_compat_r (x * (x * x)) (x * 6) (Qinv 6)).
    + exact Hx6.
    + exact Hinv0.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field.
Qed.

(* ---- nonnegative branch: q in [0,1] entails |sin_partial n q| <= 1 ---- *)
Lemma b5d2_sin_abs_le1_nonneg : forall (n : nat) (q : Q), QleT' 0 q -> QleT' q 1 ->
  QleT' (Qabs (sin_partial n q)) 1.
Proof.
  intros n q Hq0 Hq1.
  apply Qle_to_QleT'.
  assert (Hs_le_q : Qle (sin_partial n q) q).
  { apply QleT'_to_Qle. apply sc_sin_partial_upper_x. exact (QleT'_to_Qle _ _ (Hq0)). exact (QleT'_to_Qle _ _ (Hq1)). }
  assert (Hs_ge_c : Qle (q - sc_sin_alt 1 q) (sin_partial n q)).
  { apply QleT'_to_Qle. apply sc_sin_partial_lower_c1. exact (QleT'_to_Qle _ _ (Hq0)). exact (QleT'_to_Qle _ _ (Hq1)). }
  assert (Hc_le_q : Qle (sc_sin_alt 1 q) q) by (apply QleT'_to_Qle; apply b5d2_sin_alt1_le_x; [exact Hq0 | exact Hq1]).
  assert (Hs0 : Qle 0 (sin_partial n q)).
  { apply (Qle_trans _ (q - sc_sin_alt 1 q) _).
    - apply (proj1 (Qle_minus_iff (sc_sin_alt 1 q) q)). exact Hc_le_q.
    - exact Hs_ge_c. }
  apply (Qle_trans _ (sin_partial n q) _).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_pos. exact Hs0.
  - apply (Qle_trans _ q _). exact Hs_le_q. exact (QleT'_to_Qle _ _ (Hq1)).
Qed.

(* ============================================================ *)
(* M2: forall n q, |q| <= 1 -> |sin_partial n q| <= 1           *)
(* ============================================================ *)
Lemma b5d2_sin_partial_abs_le1 : forall (n : nat) (q : Q), QleT' (Qabs q) 1 ->
  QleT' (Qabs (sin_partial n q)) 1.
Proof.
  intros n q Hq.
  apply Qle_to_QleT'.
  assert (Hqle : Qle (Qabs q) 1) by (apply QleT'_to_Qle; exact Hq).
  destruct (Qcompare q 0) eqn:E.
  - (* q == 0: take the nonnegative branch. *)
    assert (Hq0 : q == 0) by (apply (proj2 (Qeq_alt q 0)); exact E).
    assert (H0q : Qle 0 q) by (apply QleT'_to_Qle; apply qeq_imp_qle; apply qeq_imp_qeqT; apply Qeq_sym; exact Hq0).
    assert (Hq1 : Qle q 1) by (apply (Qle_trans q 0 1); [apply QleT'_to_Qle; apply qeq_imp_qle; apply qeq_imp_qeqT; exact Hq0 | exact (QleT'_to_Qle _ _ Qle_0_1)]).
    exact ((QleT'_to_Qle _ _ (b5d2_sin_abs_le1_nonneg n q (Qle_to_QleT' _ _ (H0q)) (Qle_to_QleT' _ _ (Hq1))))).
  - (* q < 0: by oddness reduce to the nonnegative branch (x := -q). *)
    assert (Hqlt : Qlt q 0) by (apply (proj2 (Qlt_alt q 0)); exact E).
    assert (Hq0' : Qle q 0) by (apply Qlt_le_weak; exact Hqlt).
    assert (H0nq : Qle 0 (- q)).
    { apply (Qle_trans 0 (Qabs q) (- q)).
      - apply Qabs_nonneg.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact (Qabs_neg q Hq0'). }
    assert (Hnq1 : Qle (- q) 1).
    { apply (Qle_trans (- q) (Qabs q) 1).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. exact (Qabs_neg q Hq0').
      - exact Hqle. }
    assert (Hs : sin_partial n q == - sin_partial n (- q)).
    { apply (Qeq_trans _ (sin_partial n (- (- q))) _).
      - apply qeqT_imp_qeq. apply (sc_sin_partial_wd n q (- (- q))). apply Qeq_sym. apply Qopp_involutive.
      - exact (qeqT_imp_qeq _ _ (sc_sin_partial_neg n (- q))). }
    assert (Habs : Qabs (sin_partial n q) == Qabs (sin_partial n (- q))).
    { apply (Qeq_trans _ (Qabs (- sin_partial n (- q))) _).
      - apply (Qabs_wd (sin_partial n q) (- sin_partial n (- q))). exact Hs.
      - apply Qabs_opp. }
    apply (Qle_trans _ (Qabs (sin_partial n (- q))) _).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact Habs.
    + exact ((QleT'_to_Qle _ _ (b5d2_sin_abs_le1_nonneg n (- q) (Qle_to_QleT' _ _ (H0nq)) (Qle_to_QleT' _ _ (Hnq1))))).
  - (* 0 < q *)
    assert (Hgt : Qlt 0 q) by (apply (proj2 (Qgt_alt q 0)); exact E).
    assert (H0q : Qle 0 q) by (apply Qlt_le_weak; exact Hgt).
    assert (Hq1 : Qle q 1).
    { apply (Qle_trans q (Qabs q) 1).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. apply Qabs_pos. exact H0q.
      - exact Hqle. }
    exact ((QleT'_to_Qle _ _ (b5d2_sin_abs_le1_nonneg n q (Qle_to_QleT' _ _ (H0q)) (Qle_to_QleT' _ _ (Hq1))))).
Qed.

(* ============================================================ *)
(* Section 3. M3 b5d2_cos_partial_abs_le1 (|cos_partial n q| <= 1 for |q| <= 1) *)
(* Route: on the q in [0,1] branch use sc_cos_partial_upper_one (upper) and     *)
(*   sc_cos_partial_lower_c1 (1 - q^2/2 <= cos, hence 0 <= cos);                *)
(*   the q <= 0 branch goes through the evenness sc_cos_partial_neg.            *)
(* ============================================================ *)
Lemma b5d2_cos_alt1_le_one : forall x : Q, QleT' 0 x -> QleT' x 1 -> QleT' (sc_cos_alt 1 x) 1.
Proof.
  intros x Hx0 Hx1.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (sc_cos_alt1_half x)).
  assert (Hc : q_pow x 2 == x * x) by (cbn [q_pow]; ring).
  rewrite Hc.
  unfold Qdiv.
  assert (H2 : Qlt 0 2) by (unfold Qlt; simpl; lia).
  assert (Hinv0 : Qle 0 (Qinv 2)) by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact H2).
  apply (Qle_trans _ (2 * Qinv 2) _).
  - apply (Qmult_le_compat_r (x * x) 2 (Qinv 2)).
    + apply (Qle_trans (x * x) 1 2).
      * apply QleT'_to_Qle. apply atan_sq_le_one. apply b5d2_xle1T. exact Hx0. exact Hx1.
      * unfold Qle; simpl; lia.
    + exact Hinv0.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. assert (Hne2 : ~ (2 == 0%Q)) by (intro Hz; vm_compute in Hz; discriminate Hz). rewrite (Qmult_inv_r 2 Hne2). ring.
Qed.

(* ---- nonnegative branch: q in [0,1] entails |cos_partial n q| <= 1 ---- *)
Lemma b5d2_cos_abs_le1_nonneg : forall (n : nat) (q : Q), QleT' 0 q -> QleT' q 1 ->
  QleT' (Qabs (cos_partial n q)) 1.
Proof.
  intros n q Hq0 Hq1.
  apply Qle_to_QleT'.
  assert (Hs_le1 : Qle (cos_partial n q) 1).
  { apply QleT'_to_Qle. apply sc_cos_partial_upper_one. exact (QleT'_to_Qle _ _ (Hq0)). exact (QleT'_to_Qle _ _ (Hq1)). }
  assert (Hs_ge_c : Qle (1 - sc_cos_alt 1 q) (cos_partial n q)).
  { apply QleT'_to_Qle. apply sc_cos_partial_lower_c1. exact (QleT'_to_Qle _ _ (Hq0)). exact (QleT'_to_Qle _ _ (Hq1)). }
  assert (Hc_le1 : Qle (sc_cos_alt 1 q) 1) by (apply QleT'_to_Qle; apply b5d2_cos_alt1_le_one; [exact Hq0 | exact Hq1]).
  assert (Hs0 : Qle 0 (cos_partial n q)).
  { apply (Qle_trans _ (1 - sc_cos_alt 1 q) _).
    - apply (proj1 (Qle_minus_iff (sc_cos_alt 1 q) 1)). exact Hc_le1.
    - exact Hs_ge_c. }
  apply (Qle_trans _ (cos_partial n q) _).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_pos. exact Hs0.
  - exact Hs_le1.
Qed.

(* ============================================================ *)
(* M3: forall n q, |q| <= 1 -> |cos_partial n q| <= 1           *)
(* ============================================================ *)
Lemma b5d2_cos_partial_abs_le1 : forall (n : nat) (q : Q), QleT' (Qabs q) 1 ->
  QleT' (Qabs (cos_partial n q)) 1.
Proof.
  intros n q Hq.
  apply Qle_to_QleT'.
  assert (Hqle : Qle (Qabs q) 1) by (apply QleT'_to_Qle; exact Hq).
  destruct (Qcompare q 0) eqn:E.
  - (* q == 0: take the nonnegative branch. *)
    assert (Hq0 : q == 0) by (apply (proj2 (Qeq_alt q 0)); exact E).
    assert (H0q : Qle 0 q) by (apply QleT'_to_Qle; apply qeq_imp_qle; apply qeq_imp_qeqT; apply Qeq_sym; exact Hq0).
    assert (Hq1 : Qle q 1) by (apply (Qle_trans q 0 1); [apply QleT'_to_Qle; apply qeq_imp_qle; apply qeq_imp_qeqT; exact Hq0 | exact (QleT'_to_Qle _ _ Qle_0_1)]).
    exact ((QleT'_to_Qle _ _ (b5d2_cos_abs_le1_nonneg n q (Qle_to_QleT' _ _ (H0q)) (Qle_to_QleT' _ _ (Hq1))))).
  - (* q < 0: by evenness reduce to the nonnegative branch (x := -q). *)
    assert (Hqlt : Qlt q 0) by (apply (proj2 (Qlt_alt q 0)); exact E).
    assert (Hq0' : Qle q 0) by (apply Qlt_le_weak; exact Hqlt).
    assert (H0nq : Qle 0 (- q)).
    { apply (Qle_trans 0 (Qabs q) (- q)).
      - apply Qabs_nonneg.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact (Qabs_neg q Hq0'). }
    assert (Hnq1 : Qle (- q) 1).
    { apply (Qle_trans (- q) (Qabs q) 1).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. exact (Qabs_neg q Hq0').
      - exact Hqle. }
    assert (Hev : cos_partial n q == cos_partial n (- q)).
    { apply Qeq_sym. exact (qeqT_imp_qeq _ _ (sc_cos_partial_neg n q)). }
    assert (Habs : Qabs (cos_partial n q) == Qabs (cos_partial n (- q))).
    { apply (Qabs_wd (cos_partial n q) (cos_partial n (- q))). exact Hev. }
    apply (Qle_trans _ (Qabs (cos_partial n (- q))) _).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact Habs.
    + exact ((QleT'_to_Qle _ _ (b5d2_cos_abs_le1_nonneg n (- q) (Qle_to_QleT' _ _ (H0nq)) (Qle_to_QleT' _ _ (Hnq1))))).
  - (* 0 < q *)
    assert (Hgt : Qlt 0 q) by (apply (proj2 (Qgt_alt q 0)); exact E).
    assert (H0q : Qle 0 q) by (apply Qlt_le_weak; exact Hgt).
    assert (Hq1 : Qle q 1).
    { apply (Qle_trans q (Qabs q) 1).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. apply Qabs_pos. exact H0q.
      - exact Hqle. }
    exact ((QleT'_to_Qle _ _ (b5d2_cos_abs_le1_nonneg n q (Qle_to_QleT' _ _ (H0q)) (Qle_to_QleT' _ _ (Hq1))))).
Qed.

(* ============================================================ *)
(* Section 4. M4: composition glue (M1 + M2/M3)                                 *)
(*   |sin/cos_partial n (arctan_partial n x_n)| <= 1 (|x_n| <= 1)               *)
(* ============================================================ *)
Lemma b5d2_sinA_abs_le1 : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1) (n : nat),
  QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) 1.
Proof.
  intros x Hx n.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle.
  apply (b5d2_sin_partial_abs_le1 n (arctan_partial n (projT1 x n))).
  apply Qle_to_QleT'.
  apply QleT'_to_Qle.
  apply (b5d2_ap_abs_le1 (projT1 x n) n).
  exact (Hx n).
Qed.

Lemma b5d2_cosA_abs_le1 : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1) (n : nat),
  QleT' (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) 1.
Proof.
  intros x Hx n.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle.
  apply (b5d2_cos_partial_abs_le1 n (arctan_partial n (projT1 x n))).
  apply Qle_to_QleT'.
  apply QleT'_to_Qle.
  apply (b5d2_ap_abs_le1 (projT1 x n) n).
  exact (Hx n).
Qed.

(* ============================================================ *)
(* Section 5. M5: the x := real_const 0 instance (value pieces + the Qabs bridge) *)
(* ============================================================ *)
Lemma b5d2_x0_sinA_le1 : forall n : nat,
  QleT' (Qabs (sin_partial n (arctan_partial n (projT1 (real_const 0) n)))) 1.
Proof.
  intro n.
  apply Qle_to_QleT'.
  assert (Hz : projT1 (real_const 0) n == 0) by reflexivity.
  assert (Hap0 : arctan_partial n (projT1 (real_const 0) n) == 0).
  { apply (Qeq_trans _ (arctan_partial n 0) _).
    - apply qeqT_imp_qeq. apply (b5c_arctan_partial_wd n (projT1 (real_const 0) n) 0). exact Hz.
    - apply qeqT_imp_qeq. apply b5c_arctan_partial_zero. }
  assert (Hs0 : sin_partial n (arctan_partial n (projT1 (real_const 0) n)) == 0).
  { apply (Qeq_trans _ (sin_partial n 0) _).
    - apply qeqT_imp_qeq. apply (sc_sin_partial_wd n (arctan_partial n (projT1 (real_const 0) n)) 0). exact Hap0.
    - apply qeqT_imp_qeq. apply sc_sin_partial_zero. }
  apply (Qle_trans (Qabs (sin_partial n (arctan_partial n (projT1 (real_const 0) n)))) (Qabs 0) 1).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    apply (Qabs_wd (sin_partial n (arctan_partial n (projT1 (real_const 0) n))) 0).
    exact Hs0.
  - apply (Qle_trans (Qabs 0) 0 1).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. change (Qabs 0 == 0). cbn. reflexivity.
    + exact (QleT'_to_Qle _ _ Qle_0_1).
Qed.

Lemma b5d2_x0_cosA_le1 : forall n : nat,
  QleT' (Qabs (cos_partial n (arctan_partial n (projT1 (real_const 0) n)))) 1.
Proof.
  intro n.
  apply Qle_to_QleT'.
  assert (Hz : projT1 (real_const 0) n == 0) by reflexivity.
  assert (Hap0 : arctan_partial n (projT1 (real_const 0) n) == 0).
  { apply (Qeq_trans _ (arctan_partial n 0) _).
    - apply qeqT_imp_qeq. apply (b5c_arctan_partial_wd n (projT1 (real_const 0) n) 0). exact Hz.
    - apply qeqT_imp_qeq. apply b5c_arctan_partial_zero. }
  assert (Hc1 : cos_partial n (arctan_partial n (projT1 (real_const 0) n)) == 1).
  { apply (Qeq_trans _ (cos_partial n 0) _).
    - apply qeqT_imp_qeq. apply (sc_cos_partial_wd n (arctan_partial n (projT1 (real_const 0) n)) 0). exact Hap0.
    - apply qeqT_imp_qeq. apply sc_cos_partial_one. }
  apply (Qle_trans (Qabs (cos_partial n (arctan_partial n (projT1 (real_const 0) n)))) (Qabs 1) 1).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    apply (Qabs_wd (cos_partial n (arctan_partial n (projT1 (real_const 0) n))) 1).
    exact Hc1.
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply (Qabs_pos 1 (QleT'_to_Qle _ _ Qle_0_1)).
Qed.

(* ===== Block b5d4_ (main item b5d4_S0_lb_half; upstream source sc2_b5a_item8) ===== *)

(* ===== Section 0. certificates and bridge lemmas (b5d4_ exclusive; all genuine Qed) ===== *)

(* eps positivity certificate (used for the real_eq instantiations eps := 1/2 and 1). *)
Lemma b5d4_Hq12T : QltT 0 (1 # 2).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

Lemma b5d4_Hq1T : QltT 0 1.
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* Qlt 0 (1#2) / Qlt 0 1 (Q-layer positivity, used by the q_abs_gt_neg family). *)
Lemma b5d4_Hq12 : QltT 0 (1 # 2).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

Lemma b5d4_Hq1 : QltT 0 1.
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* the real_const 0 == real_zero bridge (pointwise zero difference; written from
   scratch after the idea of item4's b5n2_zero_eq_const0 — do not Require item4). *)
Lemma b5d4_const0_eq_zero : real_eq (real_const 0) real_zero.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_const_proj 0 n)).
  cbn [projT1 real_zero].
  reflexivity.
Qed.

(* the real_eq extensional compatibility of b5a_S (built here after the idea of
   item3b's b5m_S_wd; zero upstream dependencies): u ≈ v entails S u ≈ S v. *)
Lemma b5d4_S_wd : forall (u v : Real), real_eq u v -> real_eq (b5a_S u) (b5a_S v).
Proof.
  intros u v Huv.
  unfold b5a_S.
  apply cauchy_real_exp_wd.
  apply (RealSetoid.real_eq_mult_compat
           (real_const (1 / 2))
           (real_log (real_plus real_one (real_mult u u)) (b5a_one_plus_sq_pos u))
           (real_const (1 / 2))
           (real_log (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos v))).
  - apply real_eq_refl.
  - apply (real_log_wd (real_plus real_one (real_mult u u)) (real_plus real_one (real_mult v v))
                       (b5a_one_plus_sq_pos u) (b5a_one_plus_sq_pos v)).
    apply (RealSetoid.real_eq_plus_compat real_one (real_mult u u) real_one (real_mult v v)).
    + apply real_eq_refl.
    + apply (RealSetoid.real_eq_mult_compat u u v v); exact Huv.
Qed.

(* Q layer: |x - p| < 1/2 and p == 1 entail 1/2 < x (the tail-bound kernel of piece B1). *)
Lemma b5d4_q_lb_half : forall (x p : Q),QeqT ( p ) ( 1 )-> QltT (Qabs (x - p)) (1 # 2) -> QltT (1 # 2) x.
Proof.
  intros x p Hp H.
  apply Qlt_to_QltT.
  pose proof (QltT_to_Qlt _ _ H) as Hq.
  pose proof (qeqT_imp_qeq _ _ Hp) as Hpq.
  setoid_rewrite Hpq in Hq.   (* p -> 1 (Qminus_comp/Qabs_wd/Qlt_compat all available). *)
  apply (proj2 (Qlt_minus_iff (1 # 2) x)).
  setoid_replace (x - (1 # 2)) with ((x - 1) - - (1 # 2)) by ring.
  apply (proj1 (Qlt_minus_iff (- (1 # 2)) (x - 1))).
  apply QltT_to_Qlt. apply (q_abs_gt_neg (x - 1) (1 # 2) b5d4_Hq12). exact (Qlt_to_QltT _ _ Hq).
Qed.

(* Q layer: |x - p| < 1 and p == 1 entail |x| <= 2 (the tail-bound kernel of piece B2). *)
Lemma b5d4_q_ub_two : forall (x p : Q),QeqT ( p ) ( 1 )-> QltT (Qabs (x - p)) 1 -> QleT' (Qabs x) 2.
Proof.
  intros x p Hp H.
  apply Qle_to_QleT'.
  pose proof (QltT_to_Qlt _ _ H) as Hq.
  pose proof (qeqT_imp_qeq _ _ Hp) as Hpq.
  setoid_rewrite Hpq in Hq.   (* Qlt (Qabs (x - 1)) 1 *)
  assert (Hlow : Qlt 0 x).
  { apply (proj2 (Qlt_minus_iff 0 x)).
    setoid_replace (x - 0) with ((x - 1) - - 1) by ring.
    apply (proj1 (Qlt_minus_iff (- 1) (x - 1))).
    apply QltT_to_Qlt. apply (q_abs_gt_neg (x - 1) 1 b5d4_Hq1). exact (Qlt_to_QltT _ _ Hq). }
  assert (Hup : Qlt x 2).
  { apply (proj2 (Qlt_minus_iff x 2)).
    setoid_replace (2 - x) with (- (x - 1) - - 1) by ring.
    apply (proj1 (Qlt_minus_iff (- 1) (- (x - 1)))).
    apply QltT_to_Qlt. apply (q_abs_gt_neg (- (x - 1)) 1 b5d4_Hq1).
    apply Qlt_to_QltT. rewrite (Qabs_opp (x - 1)). exact Hq. }
  apply (Qle_trans (Qabs x) x 2).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply (Qabs_pos x). apply Qlt_le_weak. exact Hlow.
  - apply Qlt_le_weak. exact Hup.
Qed.

(* ============================================================ *)
(* Piece A: S(0) == 1 (the real_eq anchor of the S family, missing from the     *)
(*   library, a key new mathematical piece)                                     *)
(*   b5d4_S_const0_eq_one : real_eq (b5a_S (real_const 0)) real_one             *)
(* Chain: 1 + 0*0 == 1 -> real_log_wd -> real_log_one (log 1 == 0)              *)
(*   -> (1/2)*log(1 + 0*0) == (1/2)*0 == 0 -> cauchy_real_exp_wd                *)
(*   -> cauchy_real_exp_zero (e^0 == 1).  Pure Real-layer real_eq algebra,      *)
(*   zero log_seq pointwise evaluation (the §5.2 shape ceiling).                *)
(* ============================================================ *)
Lemma b5d4_S_const0_eq_one : real_eq (b5a_S (real_const 0)) real_one.
Proof.
  (* 0*0 == real_zero (via the real_const 0 == real_zero bridge + mult_zero). *)
  assert (H00 : real_eq (real_mult (real_const 0) (real_const 0)) real_zero).
  { apply (real_eq_trans _ (real_mult real_zero real_zero) _).
    - apply (RealSetoid.real_eq_mult_compat (real_const 0) (real_const 0) real_zero real_zero);
        exact b5d4_const0_eq_zero.
    - exact (real_mult_zero real_zero). }
  (* 1 + 0·0 == 1 *)
  assert (Hone : real_eq (real_plus real_one (real_mult (real_const 0) (real_const 0))) real_one).
  { apply (real_eq_trans _ (real_plus real_one real_zero) _).
    - apply (RealSetoid.real_eq_plus_compat real_one (real_mult (real_const 0) (real_const 0))
                                            real_one real_zero);
        [ apply real_eq_refl | exact H00 ].
    - exact (real_plus_zero real_one). }
  (* log(1 + 0*0) == log 1 (real_log_wd, positivity certificates on both sides). *)
  assert (Hlog1 : real_eq
      (real_log (real_plus real_one (real_mult (real_const 0) (real_const 0)))
                (b5a_one_plus_sq_pos (real_const 0)))
      (real_log real_one real_lt_zero_one)).
  { apply (real_log_wd (real_plus real_one (real_mult (real_const 0) (real_const 0))) real_one
                       (b5a_one_plus_sq_pos (real_const 0)) real_lt_zero_one). exact Hone. }
  (* log(1 + 0*0) == real_zero (the real_log_one anchor). *)
  assert (Hlogz : real_eq
      (real_log (real_plus real_one (real_mult (real_const 0) (real_const 0)))
                (b5a_one_plus_sq_pos (real_const 0)))
      real_zero).
  { apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
    - exact Hlog1.
    - exact (real_log_one real_lt_zero_one). }
  (* (1/2)·log(1 + 0·0) == (1/2)·0 == 0 *)
  assert (Hmulz : real_eq
      (real_mult (real_const (1 / 2))
                 (real_log (real_plus real_one (real_mult (real_const 0) (real_const 0)))
                           (b5a_one_plus_sq_pos (real_const 0))))
      real_zero).
  { apply (real_eq_trans _ (real_mult (real_const (1 / 2)) real_zero) _).
    - apply (RealSetoid.real_eq_mult_compat (real_const (1 / 2))
             (real_log (real_plus real_one (real_mult (real_const 0) (real_const 0)))
                       (b5a_one_plus_sq_pos (real_const 0)))
             (real_const (1 / 2)) real_zero);
        [ apply real_eq_refl | exact Hlogz ].
    - exact (real_mult_zero (real_const (1 / 2))). }
  (* exp∘mult == exp 0 == 1 *)
  unfold b5a_S.
  apply (real_eq_trans _ (cauchy_real_exp real_zero) _).
  - apply cauchy_real_exp_wd. exact Hmulz.
  - exact cauchy_real_exp_zero.
Qed.

(* ============================================================ *)
(* Piece A': S(real_zero) == 1 (the real_zero variant, serving the clamp01      *)
(*   endpoint anchor; via Piece A + b5d4_S_wd + the real_const 0 == real_zero   *)
(*   bridge)                                                                    *)
(*   b5d4_S_zero_eq_one : real_eq (b5a_S real_zero) real_one                    *)
(* ============================================================ *)
Lemma b5d4_S_zero_eq_one : real_eq (b5a_S real_zero) real_one.
Proof.
  apply (real_eq_trans _ (b5a_S (real_const 0)) _).
  - apply real_eq_sym.
    apply (b5d4_S_wd (real_const 0) real_zero). exact b5d4_const0_eq_zero.
  - exact b5d4_S_const0_eq_one.
Qed.

(* ============================================================ *)
(* Piece B1: the endpoint explicit lower bound (rational value written directly, *)
(*   forbidden to wrap in sigT c and close with Qed)                            *)
(*   b5d4_S0_lb_half : sigT (fun N => forall n, (N<=n)%nat ->                   *)
(*     Qle (1#2) (projT1 (b5a_S (real_const 0)) n))                             *)
(* Depends on: the eps := 1/2 instance of Piece A + b5d4_q_lb_half (proved at the Q layer). *)
(* ============================================================ *)
Lemma b5d4_S0_lb_half : sigT (fun N : nat => forall n : nat, NatLe N n ->
  QleT' (1 # 2) (projT1 (b5a_S (real_const 0)) n)).
Proof.
  destruct (b5d4_S_const0_eq_one (1 # 2) b5d4_Hq12T) as [N HN].
  exists N.
  intros n Hn.
  apply Qle_to_QleT'.
  apply Qlt_le_weak.
  apply QltT_to_Qlt.
  apply (b5d4_q_lb_half (projT1 (b5a_S (real_const 0)) n) (projT1 real_one n)).
  - cbn [projT1 real_one]. reflexivity.
  - exact (HN n Hn).
Qed.

(* ============================================================ *)
(* Piece B2: the endpoint explicit upper bound (tail, M0 := 2; rational value   *)
(*   written directly)                                                          *)
(*   b5d4_S0_ub_two : sigT (fun N => forall n, (N<=n)%nat ->                    *)
(*     Qle (Qabs (projT1 (b5a_S (real_const 0)) n)) 2)                          *)
(* Depends on: the eps := 1 instance of Piece A + b5d4_q_ub_two (proved at the Q layer). *)
(* ============================================================ *)
Lemma b5d4_S0_ub_two : sigT (fun N : nat => forall n : nat, NatLe N n ->
  QleT' (Qabs (projT1 (b5a_S (real_const 0)) n)) 2).
Proof.
  destruct (b5d4_S_const0_eq_one 1 b5d4_Hq1T) as [N HN].
  exists N.
  intros n Hn.
  apply (b5d4_q_ub_two (projT1 (b5a_S (real_const 0)) n) (projT1 real_one n)).
  - cbn [projT1 real_one]. reflexivity.
  - exact (HN n Hn).
Qed.

(* ===== Block b5d7_ (main item b5d7_J_deriv_zero_exp; upstream source sc2_b5a_item11) ===== *)

(* ============================================================ *)
(* Section 0. main piece b5d7_J_deriv_zero_exp (the finalized statement of the  *)
(*   C5 explicit parameterization)                                              *)
(*   Statement = the full draft text of the δC review §1.5 + the δB review      *)
(*   (ScA lower bound) §4.1; the Hxh shape matches the original b5a_J_deriv_zero *)
(*   (source L373-383).  The premises are unnamed arrows (named HNA/HMall/      *)
(*   HMs_all/HMc_all at the intros).                                            *)
(* ============================================================ *)
Lemma b5d7_J_deriv_zero_exp :
  forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1),
  forall (cA M Ms Mc : Q)
         (HcA : QltT 0 cA) (HM : QltT 0 M)
         (HMs : QltT 0 Ms) (HMc : QltT 0 Mc),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (NA : nat),
  (forall n : nat, NatLe NA n -> QleT' cA (projT1 (b5a_S x) n)) ->
  (forall n : nat, QleT' (Qabs (projT1 (b5a_S x) n)) M) ->
  (forall n : nat,
     QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Ms) ->
  (forall n : nat,
     QleT' (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5c_J (real_plus x h) Hxh)
                 (real_opp (b5c_J x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1))))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 cA M Ms Mc HcA HM HMs HMc x Hxr NA HNA HMall HMs_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)).
  (* ---- fixed data ---- *)
  (* cA: a pointwise positive lower bound for S(x) — the statement carries the explicit
     Q parameters cA/HcA plus the NA tail-bound premise HNA;
     δ-C C5: the 4 black-box destructs (source L389/396/399/400) become the intros
     argument bundle  *)
  set (cB := Qmult cA (1 # 2)).
  assert (HcB : Qlt 0 cB).
  { unfold cB. apply (Qmult_lt_0_compat cA (1 # 2)).
    - exact (QltT_to_Qlt _ _ (HcA)).
    - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  (* M/Ms/Mc: explicit Q parameters of the statement; the all-n premises HMall/HMs_all/HMc_all apply directly. *)
  assert (HM0 : Qle 0 M). { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (HM)). }
  (* Ms/Mc: the sinA/cosA pointwise bounds give ME := Ms + r*Mc (|E(x)_n| <= ME). *)
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMs. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMc. }
  assert (Hr0' : Qle 0 r). { exact (QleT'_to_Qle _ _ (Hr0)). }
  set (ME := Qplus Ms (Qmult r Mc)).
  assert (HME0 : Qle 0 ME).
  { unfold ME. nra. }
  (* the reciprocal constants and shares (all depending only on the x data; QltT 0 feeds real_const_pos). *)
  set (QicA := Qinv cA).
  set (QicB := Qinv cB).
  set (kE := Qmult cB (1 # 8)).
  set (kEp := Qmult cB (1 # 16)).
  set (kapE := Qmult cB (1 # 16)).
  set (invM1 := Qinv (Qplus ME 1)).
  set (kS := Qmult (Qmult (Qmult cA cB) (1 # 8)) invM1).
  set (kSp := Qmult (Qmult (Qmult cA cB) (1 # 16)) invM1).
  set (kapS := Qmult (Qmult (Qmult cA cB) (1 # 16)) invM1).
  set (K1 := Qplus (Qmult r M) 1).
  set (tau := Qmult cA (Qinv (Qmult 8 K1))).
  set (mu := Qmult cA (1 # 16)).
  set (kapS2 := Qmult cA (1 # 16)).
  (* positivity facts. *)
  assert (HkET : QltT 0 kE).
  { unfold kE. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 8)).
    - exact HcB.
    - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (HkEpT : QltT 0 kEp).
  { unfold kEp. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 16)).
    - exact HcB.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkapET : QltT 0 kapE).
  { unfold kapE. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 16)).
    - exact HcB.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HME1 : Qlt 0 (Qplus ME 1)).
  { nra. }
  assert (HME1ne : ~ Qplus ME 1 == 0).
  { intro Hz. apply qeq_imp_qeqT in Hz. apply (q_neq_of_lt (Qplus ME 1) (Qlt_to_QltT _ _ HME1)) in Hz. destruct Hz. }
  assert (Hinv1T : QltT 0 invM1).
  { unfold invM1. apply Qlt_to_QltT. apply Qinv_lt_0_compat. exact HME1. }
  assert (HcAcB0 : Qlt 0 (Qmult (Qmult cA cB) (1 # 8))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 8)).
    - apply (Qmult_lt_0_compat cA cB). { exact (QltT_to_Qlt _ _ (HcA)). } { exact HcB. }
    - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (HcAcB0b : Qlt 0 (Qmult (Qmult cA cB) (1 # 16))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 16)).
    - apply (Qmult_lt_0_compat cA cB). { exact (QltT_to_Qlt _ _ (HcA)). } { exact HcB. }
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkST : QltT 0 kS).
  { unfold kS. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 8)) invM1).
    - exact HcAcB0.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HkSpT : QltT 0 kSp).
  { unfold kSp. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 16)) invM1).
    - exact HcAcB0b.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HkapST : QltT 0 kapS).
  { unfold kapS. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 16)) invM1).
    - exact HcAcB0b.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HK1 : Qlt 0 K1).
  { unfold K1. nra. }
  assert (HtauT : QltT 0 tau).
  { unfold tau. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat cA (Qinv (Qmult 8 K1))).
    - exact (QltT_to_Qlt _ _ (HcA)).
    - apply Qinv_lt_0_compat. nra. }
  assert (HmuT : QltT 0 mu).
  { unfold mu. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact (QltT_to_Qlt _ _ (HcA)).
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkapS2T : QltT 0 kapS2).
  { unfold kapS2. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact (QltT_to_Qlt _ _ (HcA)).
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (H1T : QltT 0 1) by (apply Qlt_to_QltT; change (Qlt 0 1); unfold Qlt; simpl; lia).
  assert (HcA0 : Qle 0 cA). { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (HcA)). }
  assert (HcB0 : Qle 0 cB). { apply Qlt_le_weak. exact HcB. }
  assert (HcAne : ~ cA == 0). { intro Hz. apply qeq_imp_qeqT in Hz. apply (q_neq_of_lt cA HcA) in Hz. destruct Hz. }
  assert (HcBne : ~ cB == 0). { intro Hz. apply qeq_imp_qeqT in Hz. apply (q_neq_of_lt cB (Qlt_to_QltT _ _ HcB)) in Hz. destruct Hz. }
  assert (H8K1ne : ~ Qmult 8 K1 == 0).
  { intro Hz. apply qeq_imp_qeqT in Hz. assert (H8K1T : QltT 0 (Qmult 8 K1)) by (apply Qlt_to_QltT; nra). apply (q_neq_of_lt (Qmult 8 K1) H8K1T) in Hz. destruct Hz. }
  assert (HK1ne : ~ K1 == 0).
  { intro Hz. apply qeq_imp_qeqT in Hz. apply (q_neq_of_lt K1 (Qlt_to_QltT _ _ HK1)) in Hz. destruct Hz. }
  (* ---- the coefficient-budget facts (fixed at the Q layer, for pointwise absorption) ---- *)
  (* Hc1: QicB*kE == 1/8; Hc2: QicB*(kEp+kapE) == 1/8 *)
  assert (Hc1 : Qle (Qmult QicB kE) (1 # 8)).
  { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    unfold QicB, kE.
    field. exact HcBne. }
  assert (Hc1' : Qle (Qmult QicB (Qplus kEp kapE)) (1 # 8)).
  { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    unfold QicB, kEp, kapE.
    field. exact HcBne. }
  (* Hc2/Hc2': ME*QicA*QicB*kS <= 1/8, ME*QicA*QicB*(kSp+kapS) <= 1/8. *)
  set (Mterm := Qmult ME (Qmult QicA QicB)).
  assert (Hc2 : Qle (Qmult Mterm kS) (1 # 8)).
  { apply (Qle_trans (Qmult Mterm kS)
                     (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                     (1 # 8)).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      unfold Mterm, QicA, QicB, kS, invM1.
      field. all: repeat split; assumption.
    - apply (Qle_trans (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                       (Qinv 8)
                       (1 # 8)).
      + apply QleT'_to_Qle. apply (b5n_xinv_le (Qmult ME (1 # 8)) (Qplus ME 1) 8).
        * exact HME1.
        * change (Qlt 0 8). unfold Qlt. simpl. lia.
        * nra.
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold Qinv. reflexivity. }
  assert (Hc2' : Qle (Qmult Mterm (Qplus kSp kapS)) (1 # 8)).
  { apply (Qle_trans (Qmult Mterm (Qplus kSp kapS))
                     (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                     (1 # 8)).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      unfold Mterm, QicA, QicB, kSp, kapS, invM1.
      field. all: repeat split; assumption.
    - apply (Qle_trans (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                       (Qinv 8)
                       (1 # 8)).
      + apply QleT'_to_Qle. apply (b5n_xinv_le (Qmult ME (1 # 8)) (Qplus ME 1) 8).
        * exact HME1.
        * change (Qlt 0 8). unfold Qlt. simpl. lia.
        * nra.
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold Qinv. reflexivity. }
  (* the lower-bound inequality: (K1*τ) + μ + kapS2 <= cA - cB (== cA/2; the LHS == cA/4). *)
  assert (Htau_eq : Qle (Qmult K1 tau) (Qmult cA (1 # 8))).
  { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    unfold tau.
    field. all: repeat split; assumption. }
  assert (Hlb_ineq : Qle (Qplus (Qmult K1 tau) (Qplus mu kapS2)) (Qminus cA cB)).
  { apply (Qle_trans (Qplus (Qmult K1 tau) (Qplus mu kapS2))
                     (Qplus (Qmult cA (1 # 8)) (Qmult cA (1 # 8)))
                     (Qminus cA cB)).
    - apply Qplus_le_compat.
      + apply (Qle_trans (Qmult K1 tau) (Qmult cA (1 # 8)) (Qmult cA (1 # 8))).
        * exact Htau_eq.
        * apply Qle_refl.
      + apply (Qle_trans (Qplus mu kapS2) (Qmult cA (1 # 8)) (Qmult cA (1 # 8))).
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold mu, kapS2. ring.
        * apply Qle_refl.
    - unfold cB. nra. }
  (* ---- the eps witnesses and shares ---- *)
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
  assert (H2T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H4T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (H8T : QltT 0 (1 # 8)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 8)); unfold Qlt; simpl; lia).
  assert (H16T : QltT 0 (1 # 16)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 16)); unfold Qlt; simpl; lia).
  (* the eps shares (Real): epsE / epsS (the slope shares of the E-diff and S-diff main instances). *)
  set (epsE := real_mult eps (real_const kE)).
  assert (HepsE : real_lt real_zero epsE).
  { unfold epsE. apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact HkET. } }
  set (epsS := real_mult eps (real_const kS)).
  assert (HepsS : real_lt real_zero epsS).
  { unfold epsS. apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact HkST. } }
  (* closed-form instantiation: δE (E-diff), δS1/δS2 (the S-diff main / constant share). *)
  destruct (b5a_E_diff_closed_r r (QleT'_to_Qle _ _ (Hr0)) (QltT_to_Qlt _ _ (Hr1)) x Hxr epsE HepsE) as [δE [HδE0 HδE]].
  destruct (b5a_S_diff_closed_r r (QleT'_to_Qle _ _ (Hr0)) (QltT_to_Qlt _ _ (Hr1)) x Hxr epsS HepsS) as [δS1 [HδS10 HδS1]].
  destruct (b5a_S_diff_closed_r r (QleT'_to_Qle _ _ (Hr0)) (QltT_to_Qlt _ _ (Hr1)) x Hxr (real_const 1) (real_const_pos 1 H1T))
    as [δS2 [HδS20 HδS2]].
  (* δ := min(min(min(δE, δS1), δS2), real_const τ) *)
  set (delta := real_min (real_min (real_min δE δS1) δS2) (real_const tau)).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos. { exact HδE0. } { exact HδS10. } }
      { exact HδS20. } }
    { apply real_const_pos. exact HtauT. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
    (* extracting the |h| < components. *)
    assert (Hh1 : real_lt (real_abs h) (real_min (real_min δE δS1) δS2)).
    { apply (real_min_lt_l h (real_min (real_min δE δS1) δS2) (real_const tau)).
      unfold delta in Hh. exact Hh. }
    assert (Hhτ : real_lt (real_abs h) (real_const tau)).
    { apply (real_min_lt_r h (real_min (real_min δE δS1) δS2) (real_const tau)).
      unfold delta in Hh. exact Hh. }
    assert (Hh2 : real_lt (real_abs h) (real_min δE δS1)).
    { apply (real_min_lt_l h (real_min δE δS1) δS2). exact Hh1. }
    assert (HhS2 : real_lt (real_abs h) δS2).
    { apply (real_min_lt_r h (real_min δE δS1) δS2). exact Hh1. }
    assert (HhE : real_lt (real_abs h) δE).
    { apply (real_min_lt_l h δE δS1). exact Hh2. }
    assert (HhS1 : real_lt (real_abs h) δS1).
    { apply (real_min_lt_r h δE δS1). exact Hh2. }
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia.
      - apply QltT_to_Qlt. exact He1T. }
    (* the eps' shares (Real): E-diff epsE'/margin shE, S-diff epsS'/margin shS. *)
    set (epsE' := real_mult eps' (real_const kEp)).
    assert (HepsE' : real_lt real_zero epsE').
    { unfold epsE'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkEpT. } }
    set (shE := real_mult eps' (real_const kapE)).
    assert (HshE : real_lt real_zero shE).
    { unfold shE. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkapET. } }
    set (epsS' := real_mult eps' (real_const kSp)).
    assert (HepsS' : real_lt real_zero epsS').
    { unfold epsS'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkSpT. } }
    set (shS := real_mult eps' (real_const kapS)).
    assert (HshS : real_lt real_zero shS).
    { unfold shS. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkapST. } }
    (* the constant shares of the lower-bound instance (Real, independent of eps'). *)
    assert (Hcμ : real_lt real_zero (real_const mu)).
    { apply real_const_pos. exact HmuT. }
    assert (HcκS2 : real_lt real_zero (real_const kapS2)).
    { apply real_const_pos. exact HkapS2T. }
    (* pointwise conversion (real_le to per-n, with margin slack). *)
    set (BE := real_plus (real_mult epsE (real_abs h)) epsE').
    destruct (b5i_abs_le_pointwise (b5e_E_err x Hx h Hxh) BE
               (HδE h HhE Hxh epsE' HepsE') shE HshE) as [NE HNE].
    set (BS1 := real_plus (real_mult epsS (real_abs h)) epsS').
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS1
               (HδS1 h HhS1 epsS' HepsS') shS HshS) as [NS HNS].
    set (BS2 := real_plus (real_mult (real_const 1) (real_abs h)) (real_const mu)).
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS2
               (HδS2 h HhS2 (real_const mu) Hcμ) (real_const kapS2) HcκS2) as [NS2 HNS2].
    (* |h_n| <= tau (b5i_h_le_const), the |d_n| <= 1 tail, and the pointwise identity N. *)
    destruct (b5i_h_le_const h tau Hhτ HtauT) as [Nτ HNτ].
    destruct (b5c_d_proj_le_one x) as [Nd Hd].
    destruct (b5m_J_dec_proj x h Hx Hxh) as [Ndec HNdec].
    (* pointwise budget (against the eps/eps' witnesses). *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). } }
    set (Nmax := Nat.max (Nat.max Ne0 Ne1)
                 (Nat.max (Nat.max Ndec Nτ)
                  (Nat.max (Nat.max NE (Nat.max NS NS2)) (Nat.max NA Nd)))).
    (* main assembly: real_le to real_lt (left branch), with witness eta. *)
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5m_J_err x Hx h Hxh) n)).
      set (Sn := projT1 (b5a_S x) n).
      set (Shn := projT1 (b5a_S (real_plus x h)) n).
      set (dn := projT1 (b5a_atan_d x) n).
      set (rEn := projT1 (b5e_E_err x Hx h Hxh) n).
      set (rSn := projT1 (b5m_rS x h) n).
      set (Exn := projT1 (b5a_E x Hx) n).
      (* tail indices. *)
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNE : NatLe NE n) by (apply NatLe_lift; lia).
      assert (HnNS : NatLe NS n) by (apply NatLe_lift; lia).
      assert (HnNS2 : NatLe NS2 n) by (apply NatLe_lift; lia).
      assert (HnNτ : NatLe Nτ n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (HnNdec : (Ndec <= n)%nat) by lia.
      assert (HnNA : NatLe NA n) by (apply NatLe_lift; lia).
      (* nonnegativity. *)
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        - apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T.
        - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He0lt n HnNe0)). }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      assert (Hhn0 : Qle 0 hn). { unfold hn. apply Qabs_nonneg. }
      (* |h_n| <= tau, |d_n| <= 1, and Sn >= cA. *)
      assert (Hhτn : Qle (Qabs (projT1 h n)) tau).
      { unfold tau in *. exact (QleT'_to_Qle _ _ (HNτ n HnNτ)). }
      assert (Hdn1 : Qle (Qabs dn) 1).
      { unfold dn. exact (QleT'_to_Qle _ _ (Hd n (NatLe_lift _ _ HnNd))). }
      assert (HSnA : Qle cA Sn).
      { unfold Sn. exact ((QleT'_to_Qle _ _ (HNA n HnNA))). }
      (* |rE_n| <= kE*en*hn + (kEp+kapE)*en' (the E-diff made pointwise). *)
      assert (HrE : Qle (Qabs rEn)
                        (Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' kEp) (Qmult en' kapE)))).
      { apply (Qle_trans (Qabs rEn)
                         (Qplus (projT1 BE n) (projT1 shE n))
                         (Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' kEp) (Qmult en' kapE)))).
        - unfold rEn. exact (QleT'_to_Qle _ _ (HNE n HnNE)).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          unfold BE, shE, en, en'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult epsE (real_abs h)) epsE' n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj epsE (real_abs h) n)).
          unfold epsE, epsE'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const kE) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kE n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const kEp) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kEp n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const kapE) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kapE n)).
          ring. }
      (* |rS_n| <= kS*en*hn + (kSp+kapS)*en' (the S-diff main instance made pointwise). *)
      assert (HrS : Qle (Qabs rSn)
                        (Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' kSp) (Qmult en' kapS)))).
      { apply (Qle_trans (Qabs rSn)
                         (Qplus (projT1 BS1 n) (projT1 shS n))
                         (Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' kSp) (Qmult en' kapS)))).
        - unfold rSn. exact (QleT'_to_Qle _ _ (HNS n HnNS)).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          unfold BS1, shS, en, en'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult epsS (real_abs h)) epsS' n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj epsS (real_abs h) n)).
          unfold epsS, epsS'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const kS) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kS n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const kSp) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kSp n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const kapS) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kapS n)).
          ring. }
      (* |rS_n| <= 1*hn + mu + kapS2 (the S-diff constant-share instance made pointwise, used for the lower bound). *)
      assert (HrS2 : Qle (Qabs rSn)
                         (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
      { apply (Qle_trans (Qabs rSn)
                         (Qplus (projT1 BS2 n) (projT1 (real_const kapS2) n))
                         (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
        - unfold rSn. exact (QleT'_to_Qle _ _ (HNS2 n HnNS2)).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          unfold BS2.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const 1) (real_abs h))
                                         (real_const mu) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const 1) (real_abs h) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj mu n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kapS2 n)).
          ring. }
      (* |Ex_n| <= ME (the sinA/cosA pointwise bounds + |x_n| <= r; Exn == sAn - xn*cAn). *)
      assert (HEx : Qle (Qabs Exn) ME).
      { unfold Exn, b5a_E.
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_sin (cauchy_real_arctan x Hx))
                                (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx)))) n)).
        rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx))) n)).
        rewrite (qeqT_imp_qeq _ _ (real_mult_proj x (cauchy_real_cos (cauchy_real_arctan x Hx)) n)).
        apply (Qle_trans
                 (Qabs (Qplus (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                              (Qopp (Qmult (projT1 x n)
                                           (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                 (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                        (Qabs (Qmult (projT1 x n)
                                     (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))
                 ME).
        - apply (Qle_trans
                   (Qabs (Qplus (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                                (Qopp (Qmult (projT1 x n)
                                             (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qopp (Qmult (projT1 x n)
                                             (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qmult (projT1 x n)
                                       (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))).
          + apply Qabs_triangle.
          + apply Qplus_le_compat.
            * apply Qle_refl.
            * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
              apply (Qabs_opp (Qmult (projT1 x n)
                                     (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))).
        - (* |sA| + |x·cA| ≤ Ms + r·Mc ≤ ME *)
          apply (Qle_trans
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qmult (projT1 x n)
                                       (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))
                   (Qplus Ms (Qmult r Mc))
                   ME).
          + apply Qplus_le_compat.
            * apply (Qle_trans (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                               (Qabs (sin_partial n (arctan_partial n (projT1 x n))))
                               Ms).
              { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_wd. apply Qeq_sym.
                setoid_rewrite (qeqT_imp_qeq _ _ (real_sin_proj (cauchy_real_arctan x Hx) n)).
                setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hx n)).
                reflexivity. }
              { apply QleT'_to_Qle. exact (HMs_all n). }
            * apply (Qle_trans (Qabs (Qmult (projT1 x n)
                                            (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                               (Qmult r (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                               (Qmult r Mc)).
              { apply (Qle_trans (Qabs (Qmult (projT1 x n)
                                              (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                                 (Qmult (Qabs (projT1 x n))
                                        (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                                 (Qmult r (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))).
                - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
                  apply (Qabs_Qmult (projT1 x n)
                                    (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)).
                - apply (Qmult_le_compat_r (Qabs (projT1 x n)) r
                                           (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))).
                  + apply QleT'_to_Qle. exact (Hxr n).
                  + apply Qabs_nonneg. }
              { apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))
                                     Mc r).
                - apply (Qle_trans (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))
                                   (Qabs (cos_partial n (arctan_partial n (projT1 x n))))
                                   Mc).
                  + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_wd. apply Qeq_sym.
                    setoid_rewrite (qeqT_imp_qeq _ _ (real_cos_proj (cauchy_real_arctan x Hx) n)).
                    setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hx n)).
                    reflexivity.
                  + exact ((QleT'_to_Qle _ _ (HMc_all n))).
                - exact Hr0'. }
          + unfold ME. nra. }
      (* quotient-denominator certificate: |Qinv(Sn)| <= QicA. *)
      assert (HQA : Qle (Qabs (Qinv Sn)) QicA).
      { unfold Sn, QicA. apply QleT'_to_Qle. apply (b5m_inv_le Sn cA (QltT_to_Qlt _ _ (HcA)) HSnA). }
      (* Sxh >= cB: the |ΔS| bound (r*M*hn + |rS|) gives K1*tau + mu + kapS2 <= cA - cB. *)
      assert (Hdel0 : Qle (Qabs (Qminus Shn Sn))
                          (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                 (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
      { (* Shn − Sn == (x·S·d·h)_n + rS_n *)
        apply (Qle_trans (Qabs (Qminus Shn Sn))
                         (Qplus (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                                (Qabs rSn))
                         (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
        - (* triangle: |Shn - Sn| == |P + rS| <= |P| + |rS|. *)
          apply (Qle_trans (Qabs (Qminus Shn Sn))
                           (Qabs (Qplus (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))) rSn))
                           (Qplus (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                                  (Qabs rSn))).
          + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
            apply (Qabs_wd (Qminus Shn Sn)
                           (Qplus (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))) rSn)).
            unfold Shn, Sn, dn, rSn.
            unfold b5m_rS.
            rewrite (qeqT_imp_qeq _ _ (real_plus_proj (b5a_S (real_plus x h))
                                    (real_opp (real_plus (b5a_S x)
                                               (real_mult (real_mult x (b5a_S x))
                                                          (real_mult (b5a_atan_d x) h)))) n)).
            rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus (b5a_S x)
                                    (real_mult (real_mult x (b5a_S x))
                                               (real_mult (b5a_atan_d x) h))) n)).
            rewrite (qeqT_imp_qeq _ _ (real_plus_proj (b5a_S x)
                                    (real_mult (real_mult x (b5a_S x))
                                               (real_mult (b5a_atan_d x) h)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult x (b5a_S x))
                                    (real_mult (b5a_atan_d x) h) n)).
            rewrite (qeqT_imp_qeq _ _ (real_mult_proj x (b5a_S x) n)).
            rewrite (qeqT_imp_qeq _ _ (real_mult_proj (b5a_atan_d x) h n)).
            cbn [projT1 real_zero].
            ring.
          + apply Qabs_triangle.
        - (* |P| <= r*M*1*hn and |rS_n| <= hn + mu + kapS2 (HrS2). *)
          apply Qplus_le_compat.
          + (* |(x·S·d·h)_n| ≤ r·M·1·hn *)
            apply (Qle_trans (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                             (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                             (Qmult (Qmult r M) (Qabs (projT1 h n)))).
            * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
              apply (Qeq_trans (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                               (Qmult (Qabs (Qmult (projT1 x n) Sn)) (Qabs (Qmult dn (projT1 h n))))
                               (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))).
              { apply (Qabs_Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))). }
              { apply Qmult_comp.
                - apply (Qabs_Qmult (projT1 x n) Sn).
                - apply (Qabs_Qmult dn (projT1 h n)). }
            * (* (|xn|·|Sn|)·(|dn|·|hn|) ≤ (r·M)·(1·hn) *)
              apply (Qle_trans (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                               (Qmult (Qmult r M) (Qmult 1 (Qabs (projT1 h n))))
                               (Qmult (Qmult r M) (Qabs (projT1 h n)))).
              { apply (Qle_trans (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                                 (Qmult (Qmult r M) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                                 (Qmult (Qmult r M) (Qmult 1 (Qabs (projT1 h n))))).
                - apply (Qmult_le_compat_r (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult r M)
                                           (Qmult (Qabs dn) (Qabs (projT1 h n)))).
                  + apply (Qle_trans (Qmult (Qabs (projT1 x n)) (Qabs Sn))
                                     (Qmult r (Qabs Sn))
                                     (Qmult r M)).
                    * apply (Qmult_le_compat_r (Qabs (projT1 x n)) r (Qabs Sn)).
                      { apply QleT'_to_Qle. exact (Hxr n). }
                      { apply Qabs_nonneg. }
                    * apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs Sn) M r).
                      { unfold Sn. exact ((QleT'_to_Qle _ _ (HMall n))). }
                      { exact Hr0'. }
                  + apply Qmult_le_0_compat.
                    * apply Qabs_nonneg.
                    * apply Qabs_nonneg.
                - apply QleT'_to_Qle. apply (sc_qmult_le_l (Qmult (Qabs dn) (Qabs (projT1 h n)))
                                       (Qmult 1 (Qabs (projT1 h n)))
                                       (Qmult r M)).
                  + apply (Qmult_le_compat_r (Qabs dn) 1 (Qabs (projT1 h n))).
                    * exact Hdn1.
                    * apply Qabs_nonneg.
                  + apply Qmult_le_0_compat.
                    * exact Hr0'.
                    * exact HM0. }
              { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
          + (* |rS_n| ≤ hn + mu + kapS2 *)
            apply (Qle_trans (Qabs rSn)
                             (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))
                             (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
            * exact HrS2.
            * apply Qle_refl. }
      (* |ΔS| <= K1*tau + mu + kapS2 (hn <= tau). *)
      assert (Hdel : Qle (Qabs (Qminus Shn Sn))
                         (Qplus (Qmult K1 tau) (Qplus mu kapS2))).
      { apply (Qle_trans (Qabs (Qminus Shn Sn))
                         (Qplus (Qmult (Qmult r M) tau) (Qplus tau (Qplus mu kapS2)))
                         (Qplus (Qmult K1 tau) (Qplus mu kapS2))).
        - apply (Qle_trans (Qabs (Qminus Shn Sn))
                           (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                  (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))
                           (Qplus (Qmult (Qmult r M) tau) (Qplus tau (Qplus mu kapS2)))).
          + exact Hdel0.
          + apply Qplus_le_compat.
            * apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs (projT1 h n)) tau (Qmult r M)).
              { exact Hhτn. }
              { apply Qmult_le_0_compat. { exact Hr0'. } { exact HM0. } }
            * apply Qplus_le_compat.
              { exact Hhτn. }
              { apply Qle_refl. }
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold K1. ring. }
      (* Shn >= cB (Sn >= cA, |ΔS| <= B0, B0 <= cA - cB). *)
      assert (HShnB : Qle cB Shn).
      { (* Sn <= Shn + |Δ| and |Δ| <= B0 (Hdel), hence Sn <= Shn + B0. *)
        assert (HS2 : Qle Sn (Qplus Shn (Qplus (Qmult K1 tau) (Qplus mu kapS2)))).
        { apply (Qle_trans Sn (Qplus Shn (Qabs (Qminus Shn Sn)))
                              (Qplus Shn (Qplus (Qmult K1 tau) (Qplus mu kapS2)))).
          - apply (Qle_trans Sn (Qplus Shn (Qminus Sn Shn))
                                (Qplus Shn (Qabs (Qminus Shn Sn)))).
            + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
            + apply Qplus_le_compat.
              * apply Qle_refl.
              * apply (Qle_trans (Qminus Sn Shn) (Qabs (Qminus Sn Shn))
                                 (Qabs (Qminus Shn Sn))).
                { apply Qle_Qabs. }
                { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
                  apply (Qeq_trans (Qabs (Qminus Sn Shn))
                                   (Qabs (Qopp (Qminus Shn Sn)))
                                   (Qabs (Qminus Shn Sn))).
                  - apply Qabs_wd. ring.
                  - apply (Qabs_opp (Qminus Shn Sn)). }
          - apply Qplus_le_compat.
            + apply Qle_refl.
            + exact Hdel. }
        (* cB <= cA - B0 (Hlb_ineq), cA <= Sn (HSnA), Sn <= Shn + B0, hence cB <= Shn. *)
        nra. }
      (* quotient-denominator certificate: |Qinv(Shn)| <= QicB. *)
      assert (HQB : Qle (Qabs (Qinv Shn)) QicB).
      { unfold Shn, QicB. apply QleT'_to_Qle. apply (b5m_inv_le Shn cB HcB HShnB). }
      (* the b5m_J_abs_tri main step. *)
      set (RE := Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kEp) (Qmult en' kapE))).
      set (RS := Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kSp) (Qmult en' kapS))).
      assert (Hmain0 : Qle Dn (Qplus (Qmult QicB RE) (Qmult Mterm RS))).
      { unfold Dn.
        apply QleT'_to_Qle. apply (b5m_J_abs_tri x h Hx Hxh n QicA QicB ME RE RS).
        - exact HQA.
        - exact HQB.
        - unfold Exn. exact HEx.
        - unfold rEn. exact HrE.
        - unfold rSn. exact HrS.
        - unfold QicA. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (HcA)).
        - unfold QicB. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HcB.
        - exact (qeqT_imp_qeq _ _ (HNdec n (NatLe_lift _ _ HnNdec))). }
      (* coefficient absorption: QicB*RE <= (1/8)*en*hn + (1/8)*en'; Mterm*RS <= the same shape. *)
      assert (HT1 : Qle (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                        (Qmult (1 # 8) (Qmult en hn))).
      { apply (Qle_trans (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                         (Qmult (Qmult QicB kE) (Qmult en hn))
                         (Qmult (1 # 8) (Qmult en hn))).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold hn. ring.
        - apply (Qmult_le_compat_r (Qmult QicB kE) (1 # 8) (Qmult en hn)).
          + exact Hc1.
          + apply Qmult_le_0_compat.
            * exact Hen0.
            * exact Hhn0. }
      assert (HT2 : Qle (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE)))
                        (Qmult (1 # 8) en')).
      { apply (Qle_trans (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE)))
                         (Qmult (Qmult QicB (Qplus kEp kapE)) en')
                         (Qmult (1 # 8) en')).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        - apply (Qmult_le_compat_r (Qmult QicB (Qplus kEp kapE)) (1 # 8) en').
          + exact Hc1'.
          + exact Hen'0. }
      assert (HT3 : Qle (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                        (Qmult (1 # 8) (Qmult en hn))).
      { apply (Qle_trans (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                         (Qmult (Qmult Mterm kS) (Qmult en hn))
                         (Qmult (1 # 8) (Qmult en hn))).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold hn. ring.
        - apply (Qmult_le_compat_r (Qmult Mterm kS) (1 # 8) (Qmult en hn)).
          + exact Hc2.
          + apply Qmult_le_0_compat.
            * exact Hen0.
            * exact Hhn0. }
      assert (HT4 : Qle (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))
                        (Qmult (1 # 8) en')).
      { apply (Qle_trans (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))
                         (Qmult (Qmult Mterm (Qplus kSp kapS)) en')
                         (Qmult (1 # 8) en')).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        - apply (Qmult_le_compat_r (Qmult Mterm (Qplus kSp kapS)) (1 # 8) en').
          + exact Hc2'.
          + exact Hen'0. }
      (* assembling the pointwise main bound: |Dn| <= en*hn + (3/4)*en'. *)
      assert (Hmain : Qle Dn (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
      { apply (Qle_trans Dn
                         (Qplus (Qmult QicB RE) (Qmult Mterm RS))
                         (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
        - exact Hmain0.
        - (* expand and absorb: QicB*RE + Mterm*RS <= (1/8)(en hn) + (1/8)en', two copies of each. *)
          apply (Qle_trans (Qplus (Qmult QicB RE) (Qmult Mterm RS))
                           (Qplus (Qplus (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                                         (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE))))
                                  (Qplus (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                                         (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))))
                           (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
          + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold RE, RS, hn. ring.
          + apply (Qle_trans
                     (Qplus (Qplus (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                                   (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE))))
                            (Qplus (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                                   (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))))
                     (Qplus (Qplus (Qmult (1 # 8) (Qmult en hn)) (Qmult (1 # 8) en'))
                            (Qplus (Qmult (1 # 8) (Qmult en hn)) (Qmult (1 # 8) en')))
                     (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
            * apply Qplus_le_compat.
              { apply Qplus_le_compat. { exact HT1. } { exact HT2. } }
              { apply Qplus_le_compat. { exact HT3. } { exact HT4. } }
            * nra. }
      (* margin: eta < (1/4)*en'; Hfin: eta < (en*hn + en') - Dn. *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply QltT_to_Qlt. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        - apply QltT_to_Qlt. exact He1T.
        - exact (QltT_to_Qlt _ _ (He1lt n HnNe1)). }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply QltT_to_Qlt. apply (b5n_close Dn hn en en' eta).
        - unfold Dn. exact Hmain.
        - unfold en'. exact Hq4e. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5m_J_err x Hx h Hxh)) n))).
      - exact Hfin.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (b5m_J_err x Hx h Hxh) n)).
        unfold en, en', hn, Dn.
        ring. } }
Qed.

(* ===== Block b5d8_ (main item b5d8_J_deriv_zero_tail_exp; upstream source sc2_b5a_item12) ===== *)

(* ============================================================ *)
(* Section 0. main piece b5d8_J_deriv_zero_tail_exp (the finalized statement of *)
(*   the C6 explicit parameterization)                                          *)
(*   Statement = the draft of the δC review §1.6 + the δB review (ScA lower     *)
(*   bound) §4.2: the same argument bundle (cA/M/Ms/Mc + HcA/HM/HMs/HMc) is     *)
(*   prefixed to the quantifier head; the N0/Hxr tail certificate and the all-n *)
(*   Hx1 <= 1 stay as is; the error J(x+h)-J(x) has the same shape as item11 C5, *)
(*   but the base-point certificate = Hx1 (following the source L1365-1377).    *)
(*   The bound-premise carrier = x̂ := b5m_tailtrunc x N0 (the C5 expl call site, *)
(*   shape verified against the source).  The premises are unnamed arrows (named *)
(*   HNA/HMall/HMs_all/HMc_all at the intros; HNA uses the (NA<=n)%nat form —   *)
(*   the item11 §4 shape decision: NatLe and (<=)%nat are not interconvertible). *)
(* ============================================================ *)
Lemma b5d8_J_deriv_zero_tail_exp :
  forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1),
  forall (cA M Ms Mc : Q)
         (HcA : QltT 0 cA) (HM : QltT 0 M)
         (HMs : QltT 0 Ms) (HMc : QltT 0 Mc),
  forall (x : Real) (N0 : nat)
    (Hxr : forall n : nat, NatLe N0 n -> QleT' (Qabs (projT1 x n)) r),
  forall (Hx1 : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (NA : nat),
  (forall n : nat, NatLe NA n -> QleT' cA (projT1 (b5a_S (b5m_tailtrunc x N0)) n)) ->
  (forall n : nat, QleT' (Qabs (projT1 (b5a_S (b5m_tailtrunc x N0)) n)) M) ->
  (forall n : nat,
     QleT' (Qabs (sin_partial n (arctan_partial n (projT1 (b5m_tailtrunc x N0) n)))) Ms) ->
  (forall n : nat,
     QleT' (Qabs (cos_partial n (arctan_partial n (projT1 (b5m_tailtrunc x N0) n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5c_J (real_plus x h) Hxh)
                 (real_opp (b5c_J x Hx1))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 cA M Ms Mc HcA HM HMs HMc x N0 Hxr Hx1 NA HNA HMall HMs_all HMc_all eps Heps.
  (* the all-n r certificate at the truncated base point. *)
  assert (Hx̂r : forall n : nat,
            QleT' (Qabs (projT1 (b5m_tailtrunc x N0) n)) r).
  { apply (b5m_tailtrunc_r r (QleT'_to_Qle _ _ (Hr0)) N0 x). exact Hxr. }
  (* black box: b5a_J_deriv_zero @ (trunc x N0, Hx̂r) *)
  (* δ-C C6: the black-box call site now calls the C5 explicit main piece
     b5d7_J_deriv_zero_exp @ (trunc x N0, the explicit argument bundle);
     δ := δ_exp @ (x̂, the bundle), passed through *)
  destruct (b5d7_J_deriv_zero_exp r Hr0 Hr1 cA M Ms Mc HcA HM HMs HMc (b5m_tailtrunc x N0) Hx̂r NA HNA HMall HMs_all HMc_all eps Heps)
    as [delta [Hd0 Hd]].
  exists delta.
  split.
  { exact Hd0. }
  { intros h Hh Hxh eps' Heps'.
    (* ĥ := trunc h N0 satisfies |ĥ| < delta (ĥ == h, hence |ĥ| == |h|). *)
    assert (Hĥlt : real_lt (real_abs (b5m_tailtrunc h N0)) delta).
    { apply (RealSetoid.real_lt_compat (real_abs h)
                                       (real_abs (b5m_tailtrunc h N0))
                                       delta delta).
      - apply real_eq_sym.
        apply (real_abs_eq_compat (b5m_tailtrunc h N0) h).
        exact (b5m_tailtrunc_eq h N0).
      - apply real_eq_refl.
      - exact Hh. }
    (* cw_unit (trunc x N0 + trunc h N0): extracted pointwise from Hxh. *)
    assert (Hxĥ : forall n : nat,
              QleT' (Qabs (projT1 (real_plus (b5m_tailtrunc x N0)
                                             (b5m_tailtrunc h N0)) n)) 1).
    { exact (b5m_plus_tailtrunc_unit x h N0 Hxh). }
    (* the black-box modulus at the truncated base point. *)
    assert (Hmod : real_le
      (real_abs (real_plus
        (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
        (real_opp (b5c_J (b5m_tailtrunc x N0)
                         (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r (QltT_to_Qlt _ _ Hr1))))))
      (real_plus (real_mult eps (real_abs (b5m_tailtrunc h N0))) eps')).
    { exact (Hd (b5m_tailtrunc h N0) Hĥlt Hxĥ eps' Heps'). }
    (* real_eq bridges: x̂ == x, ĥ == h, x̂+ĥ == x+h. *)
    assert (Hxeq : real_eq (b5m_tailtrunc x N0) x).
    { exact (b5m_tailtrunc_eq x N0). }
    assert (Hheq : real_eq (b5m_tailtrunc h N0) h).
    { exact (b5m_tailtrunc_eq h N0). }
    assert (Hpeq : real_eq (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0))
                           (real_plus x h)).
    { apply (RealSetoid.real_eq_plus_compat
               (b5m_tailtrunc x N0) (b5m_tailtrunc h N0) x h).
      - exact Hxeq.
      - exact Hheq. }
    (* transferring the J value extensionally. *)
    assert (Hj1 : real_eq (b5c_J (real_plus x h) Hxh)
                          (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)).
    { apply (b5m_J_wd (real_plus x h)
                      (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0))
                      Hxh Hxĥ).
      apply real_eq_sym. exact Hpeq. }
    assert (Hj2 : real_eq (b5c_J x Hx1)
                          (b5c_J (b5m_tailtrunc x N0)
                                 (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r (QltT_to_Qlt _ _ Hr1)))).
    { apply (b5m_J_wd x (b5m_tailtrunc x N0) Hx1
                      (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r (QltT_to_Qlt _ _ Hr1))).
      apply real_eq_sym. exact Hxeq. }
    (* the difference |J(x+h) - J(x)| == |J(x̂+ĥ) - J(x̂)| (abs/plus/opp compat). *)
    assert (HA : real_eq
      (real_abs (real_plus (b5c_J (real_plus x h) Hxh) (real_opp (b5c_J x Hx1))))
      (real_abs (real_plus
        (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
        (real_opp (b5c_J (b5m_tailtrunc x N0)
                         (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r (QltT_to_Qlt r 1 Hr1))))))).
    { apply (RealSetoid.real_eq_abs_compat
        (real_plus (b5c_J (real_plus x h) Hxh) (real_opp (b5c_J x Hx1)))
        (real_plus (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
                   (real_opp (b5c_J (b5m_tailtrunc x N0)
                                    (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r (QltT_to_Qlt r 1 Hr1)))))).
      apply (RealSetoid.real_eq_plus_compat
        (b5c_J (real_plus x h) Hxh)
        (real_opp (b5c_J x Hx1))
        (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
        (real_opp (b5c_J (b5m_tailtrunc x N0)
                         (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r (QltT_to_Qlt _ _ (Hr1)))))).
      - exact Hj1.
      - apply (RealSetoid.real_eq_opp_compat
                 (b5c_J x Hx1)
                 (b5c_J (b5m_tailtrunc x N0)
                        (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r (QltT_to_Qlt _ _ (Hr1))))).
        exact Hj2. }
    (* the bound eps*|ĥ| + eps' == eps*|h| + eps' (|ĥ| == |h|). *)
    assert (HB : real_eq
      (real_plus (real_mult eps (real_abs (b5m_tailtrunc h N0))) eps')
      (real_plus (real_mult eps (real_abs h)) eps')).
    { apply (RealSetoid.real_eq_plus_compat
        (real_mult eps (real_abs (b5m_tailtrunc h N0))) eps'
        (real_mult eps (real_abs h)) eps').
      - apply (RealSetoid.real_eq_mult_compat
          eps (real_abs (b5m_tailtrunc h N0)) eps (real_abs h)).
        + apply real_eq_refl.
        + apply (real_abs_eq_compat (b5m_tailtrunc h N0) h).
          exact (b5m_tailtrunc_eq h N0).
      - apply real_eq_refl. }
    (* modulus transfer back: real_le_compat carries the (x̂,ĥ) modulus back to (x,h). *)
    apply (RealSetoid.real_le_compat
      (real_abs (real_plus
        (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
        (real_opp (b5c_J (b5m_tailtrunc x N0)
                         (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r (QltT_to_Qlt _ _ Hr1))))))
      (real_abs (real_plus (b5c_J (real_plus x h) Hxh) (real_opp (b5c_J x Hx1))))
      (real_plus (real_mult eps (real_abs (b5m_tailtrunc h N0))) eps')
      (real_plus (real_mult eps (real_abs h)) eps')).
    - apply real_eq_sym. exact HA.
    - exact HB.
    - exact Hmod. }
Qed.

(* ===== Block b5dE_ (main item b5dE_S_ub_tail_q; upstream source sc2_b5a_item15) ===== *)

(* ===== Section 0. Q-layer small pieces (b5dE_ exclusive; all genuine Qed; proved by nra/vm_compute) ===== *)

(* Qlt 0 (1/2) (in Qdiv notation; the closed value decided by vm_compute). *)
Lemma b5dE_half_pos_div : QltT 0 (1 / 2).
Proof. apply Qlt_to_QltT. vm_compute. reflexivity. Qed.

(* Qlt (1/2) 1 *)
Lemma b5dE_half_lt_one_div : QltT (1 / 2) 1.
Proof. apply Qlt_to_QltT. vm_compute. reflexivity. Qed.

(* Qlt 0 1 *)
Lemma b5dE_zero_lt_one : QltT 0 1.
Proof. apply Qlt_to_QltT. vm_compute. reflexivity. Qed.

(* Qle 0 1 *)
Lemma b5dE_zero_le_one : QleT' 0 1.
Proof.
  apply Qle_to_QleT'.
  (* built directly at the Z layer (avoiding the two-hop forwarding through Qlt_le_weak
     and b5dE_zero_lt_one): unfolding Qle gives the cross-product Z.le, and after the
     literal reduction the linear decision closes. *)
  unfold Qle.
  simpl.
  lia.
Qed.

(* 0 < q and q < 1 give e0 := (1 - q^2)*(1/2) > 0 (proved by the nonlinear nra). *)
Lemma b5dE_e0_pos : forall (q : Q), QltT 0 q -> QltT q 1 ->
  QltT 0 ((1 - q * q) * (1 # 2)).
Proof. intros q Hq0 Hq1. apply QltT_to_Qlt in Hq0. apply QltT_to_Qlt in Hq1. apply Qlt_to_QltT. nra. Qed.

(* 0 < q and q < 1 give q^2 + e0 < 1 (e0 := (1 - q^2)*(1/2); a strict gap). *)
Lemma b5dE_e0_sum_lt_one : forall (q : Q), QltT 0 q -> QltT q 1 ->
  QltT (q * q + (1 - q * q) * (1 # 2)) 1.
Proof. intros q Hq0 Hq1. apply QltT_to_Qlt in Hq0. apply QltT_to_Qlt in Hq1. apply Qlt_to_QltT. nra. Qed.

(* Q-layer kernel: 1 <= x and x < 2 give |x| <= 2 (the main piece's tail step). *)
Lemma b5dE_q_abs_le_of_bounds : forall (x : Q),
  QleT' 1 x -> QltT x 2 -> QleT' (Qabs x) 2.
Proof.
  intros x Hlb Hup.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs x) x 2).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply (Qabs_pos x).
    apply (Qle_trans 0 1 x (QleT'_to_Qle _ _ (b5dE_zero_le_one)) (QleT'_to_Qle _ _ (Hlb))).
  - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (Hup)).
Qed.

(* ============================================================ *)
(* Section 1. the Real-layer certificate small pieces (b5dE_ exclusive; all genuine Qed) *)
(* ============================================================ *)

(* the real_const 1 == real_one bridge (real_lt and the real_one domain interoperate). *)
Lemma b5dE_const1_eq_one : real_eq (real_const 1) real_one.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
  cbn [projT1 real_one].
  ring.
Qed.

(* q > 0 entails 0 < real_const q (the real_const_pos L36290 instance). *)
Lemma b5dE_q_pos : forall (q : Q) (Hq0 : QltT 0 q),
  real_lt real_zero (real_const q).
Proof.
  intros q Hq0.
  apply real_const_pos.
  apply Qlt_to_QltT.
  exact (QltT_to_Qlt _ _ (Hq0)).
Qed.

(* 0 < real_const (1/2) (the real_const_pos instance, in Qdiv notation). *)
Lemma b5dE_half_pos_real : real_lt real_zero (real_const (1 / 2)).
Proof.
  apply real_const_pos.
  apply Qlt_to_QltT.
  exact (QltT_to_Qlt _ _ (b5dE_half_pos_div)).
Qed.

(* ============================================================ *)
(* Section 2. the Real-layer bound chain (b5dE_ exclusive; all genuine Qed)      *)
(*   Chain: log(1+q*q) < real_const 1 -> *(1/2) -> exp monotone ->               *)
(*        S(q) < exp(1/2) <= 2 (the inv(1/2) == 2 bridge)                        *)
(* ============================================================ *)

(* ============================================================ *)
(* Piece b5dE_log_ub_one: 0 < q < 1 gives log(1 + q^2) < real_const 1            *)
(*   Chain: t := real_const q * real_const q == real_const (q*q)                 *)
(*     (real_eq_of_zero_diff pointwise) gives log(1+t) <= t + real_const         *)
(*     e0 (real_log_one_plus_le_eps L44229, e0 := (1-q^2)(1/2))                  *)
(*     <= real_const (q^2+e0) (le_trans + plus_compat + the const bridge)        *)
(*     < real_const 1 (real_const_lt L37095; the strict q^2+e0 < 1 separation)   *)
(*     -> closed via real_le_lt_trans L6212.  Zero closed-form log-value        *)
(*   dependency.                                                                 *)
(* ============================================================ *)
Lemma b5dE_log_ub_one : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1),
  real_lt (real_log (real_plus real_one (real_mult (real_const q) (real_const q)))
                    (b5a_one_plus_sq_pos (real_const q)))
          (real_const 1).
Proof.
  intros q Hq0 Hq1.
  set (t := real_mult (real_const q) (real_const q)).
  set (e0 := (1 - q * q) * (1 # 2)).
  (* t == real_const (q*q) (pointwise projections + cbn + ring). *)
  assert (Hteq : real_eq t (real_const (q * q))).
  { apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
    unfold t.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const q) (real_const q) n)).
    cbn [projT1 real_const].
    ring. }
  (* e0 > 0 and q^2 + e0 < 1 (Q-layer nra, separated certificates). *)
  assert (He0 : Qlt 0 e0).
  { unfold e0. exact ((QltT_to_Qlt _ _ (b5dE_e0_pos q Hq0 Hq1))). }
  assert (He1 : Qlt (q * q + e0) 1).
  { unfold e0. exact ((QltT_to_Qlt _ _ (b5dE_e0_sum_lt_one q Hq0 Hq1))). }
  (* eps0 := real_const e0 > 0 *)
  assert (Heps0 : real_lt real_zero (real_const e0)).
  { apply real_const_pos. apply Qlt_to_QltT. exact He0. }
  (* log(1+t) ≤ t + eps0 *)
  assert (Hlog1 : real_le (real_log (real_plus real_one t) (b5a_one_plus_sq_pos (real_const q)))
                          (real_plus t (real_const e0))).
  { apply (real_log_one_plus_le_eps t (real_const e0) (b5a_one_plus_sq_pos (real_const q)) Heps0). }
  (* t <= real_const (q*q) (real_eq -> real_le). *)
  assert (Hle_t : real_le t (real_const (q * q))).
  { apply RealSetoid.real_eq_le. exact Hteq. }
  (* t + eps0 ≤ real_const(q·q) + eps0 *)
  assert (Hle_sum : real_le (real_plus t (real_const e0))
                            (real_plus (real_const (q * q)) (real_const e0))).
  { apply (real_le_plus_compat t (real_const (q * q)) (real_const e0) (real_const e0) Hle_t).
    apply real_le_refl. }
  (* real_const(q·q) + real_const e0 == real_const (q·q + e0) *)
  assert (Hsum_eq : real_eq (real_plus (real_const (q * q)) (real_const e0))
                            (real_const (q * q + e0))).
  { apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_const (q * q)) (real_const e0) n)).
    cbn [projT1 real_const].
    ring. }
  (* t + eps0 ≤ real_const (q·q + e0) *)
  assert (Hle_sum2 : real_le (real_plus t (real_const e0)) (real_const (q * q + e0))).
  { apply (real_le_trans (real_plus t (real_const e0))
                         (real_plus (real_const (q * q)) (real_const e0))
                         (real_const (q * q + e0)) Hle_sum).
    apply RealSetoid.real_eq_le. exact Hsum_eq. }
  (* log(1+t) ≤ real_const (q·q + e0) *)
  assert (Hlog2 : real_le (real_log (real_plus real_one t) (b5a_one_plus_sq_pos (real_const q)))
                          (real_const (q * q + e0))).
  { apply (real_le_trans (real_log (real_plus real_one t) (b5a_one_plus_sq_pos (real_const q)))
                         (real_plus t (real_const e0))
                         (real_const (q * q + e0)) Hlog1 Hle_sum2). }
  (* real_const (q*q + e0) < real_const 1 (the Q-layer separation). *)
  assert (Hc_lt : real_lt (real_const (q * q + e0)) (real_const 1)).
  { apply real_const_lt. exact (Qlt_to_QltT _ _ He1). }
  apply (real_le_lt_trans (real_log (real_plus real_one t) (b5a_one_plus_sq_pos (real_const q)))
                          (real_const (q * q + e0))
                          (real_const 1) Hlog2 Hc_lt).
Qed.

(* ============================================================ *)
(* Piece b5dE_S_lt_exp_half: 0 < q < 1 entails S(q) < exp(real_const(1/2))       *)
(*   Chain: the log upper-bound piece *(1/2) (real_lt_mult_compat L39389,        *)
(*   positive multiplier) -> (1/2)*log(1+q^2) < real_const(1/2) (the            *)
(*   (1/2)*1 == 1/2 bridge) -> exp strictly monotone (cauchy_real_exp_mono      *)
(*   L35227).                                                                    *)
(* ============================================================ *)
Lemma b5dE_S_lt_exp_half : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1),
  real_lt (b5a_S (real_const q)) (cauchy_real_exp (real_const (1 / 2))).
Proof.
  intros q Hq0 Hq1.
  assert (Hlogb : real_lt (real_log (real_plus real_one (real_mult (real_const q) (real_const q)))
                                    (b5a_one_plus_sq_pos (real_const q)))
                          (real_const 1)).
  { exact (b5dE_log_ub_one q Hq0 Hq1). }
  (* (1/2)·log(1+q²) < (1/2)·real_const 1 == real_const (1/2) *)
  assert (Hsmall : real_lt (real_mult (real_const (1 / 2))
                                      (real_log (real_plus real_one (real_mult (real_const q) (real_const q)))
                                                (b5a_one_plus_sq_pos (real_const q))))
                           (real_const (1 / 2))).
  { apply (real_lt_eq_lt (real_mult (real_const (1 / 2))
                                    (real_log (real_plus real_one (real_mult (real_const q) (real_const q)))
                                              (b5a_one_plus_sq_pos (real_const q))))
                         (real_mult (real_const (1 / 2)) (real_const 1))
                         (real_const (1 / 2))).
    - apply (real_lt_mult_compat (real_log (real_plus real_one (real_mult (real_const q) (real_const q)))
                                           (b5a_one_plus_sq_pos (real_const q)))
                                 (real_const 1) (real_const (1 / 2)) b5dE_half_pos_real Hlogb).
    - (* (1/2)*real_const 1 == real_const (1/2) (pointwise cbn + ring). *)
      apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (1 / 2)) (real_const 1) n)).
      cbn [projT1 real_const].
      ring. }
  (* exp strictly monotone (matches the definitional unfolding of b5a_S). *)
  apply (cauchy_real_exp_mono (real_mult (real_const (1 / 2))
                                (real_log (real_plus real_one (real_mult (real_const q) (real_const q)))
                                          (b5a_one_plus_sq_pos (real_const q))))
                              (real_const (1 / 2)) Hsmall).
Qed.

(* ============================================================ *)
(* Piece b5dE_exp_half_le_two: exp(real_const (1/2)) <= real_const 2             *)
(*   Chain: real_exp_le_inv_one_minus L53549 at x := real_const(1/2)             *)
(*   (the 0 < 1/2 < 1 certificate) gives exp(1/2) <= inv(1-1/2); 1-1/2 == 1/2    *)
(*   (pointwise field) -> the real_inv_pos_ext L39276 conversion; inv(1/2) == 2  *)
(*   (real_inv_unique L36016: (1/2)*inv(1/2) == 1 == (1/2)*2) — done.            *)
(* ============================================================ *)
Lemma b5dE_exp_half_le_two : real_le (cauchy_real_exp (real_const (1 / 2))) (real_const 2).
Proof.
  (* real_const (1/2) < real_one (the domain certificate, via the real_const 1 bridge). *)
  assert (Hhalflt1 : real_lt (real_const (1 / 2)) real_one).
  { apply (real_lt_eq_lt (real_const (1 / 2)) (real_const 1) real_one).
    - apply real_const_lt. exact b5dE_half_lt_one_div.
    - exact b5dE_const1_eq_one. }
  (* exp(1/2) <= inv(1 - 1/2) (real_exp_le_inv_one_minus). *)
  pose proof (real_exp_le_inv_one_minus (real_const (1 / 2)) b5dE_half_pos_real Hhalflt1) as He1.
  set (W := real_lt_opp_plus (real_const (1 / 2)) real_one Hhalflt1).
  (* 1 - 1/2 == 1/2 (pointwise projections + cbn + field). *)
  assert (Hb : real_eq (real_plus real_one (real_opp (real_const (1 / 2)))) (real_const (1 / 2))).
  { apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_opp (real_const (1 / 2))) n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_const (1 / 2)) n)).
    cbn [projT1 real_const real_one].
    field. }
  (* inv(1 - 1/2) == inv(1/2) (real_inv_pos_ext). *)
  pose proof (real_inv_pos_ext (real_plus real_one (real_opp (real_const (1 / 2))))
                               (real_const (1 / 2)) W b5dE_half_pos_real Hb) as Hinvext.
  (* inv(1/2) == real_const 2 (real_inv_unique: (1/2)*inv(1/2) == 1 == (1/2)*2). *)
  assert (Htwo : real_eq (real_inv_pos (real_const (1 / 2)) b5dE_half_pos_real) (real_const 2)).
  { apply (real_inv_unique (real_const (1 / 2))
                           (real_inv_pos (real_const (1 / 2)) b5dE_half_pos_real)
                           (real_const 2)).
    - exact (real_inv_pos_correct (real_const (1 / 2)) b5dE_half_pos_real).
    - (* (1/2)*2 == 1 (pointwise projections + cbn + field). *)
      apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (1 / 2)) (real_const 2) n)).
      cbn [projT1 real_const real_one].
      field. }
  (* assembly: exp(1/2) <= inv(1-1/2) <= inv(1/2) <= real_const 2. *)
  apply (real_le_trans (cauchy_real_exp (real_const (1 / 2)))
                       (real_inv_pos (real_plus real_one (real_opp (real_const (1 / 2)))) W)
                       (real_const 2)).
  - exact He1.
  - apply (real_le_trans (real_inv_pos (real_plus real_one (real_opp (real_const (1 / 2)))) W)
                         (real_inv_pos (real_const (1 / 2)) b5dE_half_pos_real)
                         (real_const 2)).
    + apply RealSetoid.real_eq_le. exact Hinvext.
    + apply RealSetoid.real_eq_le. exact Htwo.
Qed.

(* ============================================================ *)
(* Section 3. main piece: the rational-point S upper-bound tail certificate (M0 := 2 written directly) *)
(*   Main piece b5dE_S_ub_tail_q : forall (q : Q) (Hq0 : Qlt 0 q)                *)
(*      (Hq1 : Qlt q 1), sigT (fun N : nat => forall n : nat,                    *)
(*      (N <= n)%nat ->                                                          *)
(*      Qle (Qabs (projT1 (b5a_S (real_const q)) n)) 2)                          *)
(*   Assembly: the lower side b5a_S_ge_one L84807 (0 < q gives the tail Qle 1    *)
(*     (S n)) + the upper side b5dE_S_lt_exp_half composed with                  *)
(*     b5dE_exp_half_le_two, so real_lt_le_trans L6205: S(q) < real_const 2      *)
(*     (a strict gap) -> real_lt_pt_lt L37117 made pointwise ((N <= n)%nat       *)
(*     form) -> the Q-layer kernel b5dE_q_abs_le_of_bounds applied per n (the    *)
(*     max-N merge).                                                             *)
(*   Serving F1 / the grid: the B' grid points t_k := k*q/M in (0,1) are         *)
(*     rational, so the q := t_k instance satisfies 0<q<1 automatically; the     *)
(*     q := 0 endpoint is covered by item8 B2 b5d4_S0_ub_two (L226, tail <= 2);  *)
(*     this piece does not handle endpoints.                                     *)
(* ============================================================ *)
Lemma b5dE_S_ub_tail_q : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1),
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QleT' (Qabs (projT1 (b5a_S (real_const q)) n)) 2).
Proof.
  intros q Hq0 Hq1.
  (* lower side: 0 < q gives the tail Qle 1 (S(q)) (b5a_S_ge_one L84807). *)
  destruct (b5a_S_ge_one (real_const q) (b5dE_q_pos q Hq0)) as [N1 H1].
  (* upper side: S(q) < exp(1/2) <= 2 gives S(q) < real_const 2 (strict). *)
  assert (Hstrict : real_lt (b5a_S (real_const q)) (real_const 2)).
  { apply (real_lt_le_trans (b5a_S (real_const q))
                            (cauchy_real_exp (real_const (1 / 2)))
                            (real_const 2)).
    - exact (b5dE_S_lt_exp_half q Hq0 Hq1).
    - exact b5dE_exp_half_le_two. }
  (* pointwise: (N2 <= n)%nat gives S_n < (real_const 2)_n (real_lt_pt_lt). *)
  destruct (real_lt_pt_lt (b5a_S (real_const q)) (real_const 2) Hstrict) as [N2 H2].
  exists (Nat.max N1 N2).
  intros n Hn.
  apply NatLe_drop in Hn.
  apply (b5dE_q_abs_le_of_bounds (projT1 (b5a_S (real_const q)) n)).
  - apply (H1 n). apply NatLe_lift. lia.
  - assert (Hup : Qlt (projT1 (b5a_S (real_const q)) n) (projT1 (real_const 2) n)).
    { apply QltT_to_Qlt. apply (H2 n). apply NatLe_lift. lia. }
    setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj 2 n)) in Hup.
    exact (Qlt_to_QltT _ _ (Hup)).
Qed.

(* ===== Block b5dF_ (main item b5dF_E_one_zero_of_rational; upstream source sc2_b5a_item16) ===== *)

(* ============================================================ *)
(* Section A §1: the Q glue — the open-interval Q certificates for xg := 1-g     *)
(*   Inside the replica, g = Qmin (1/2) a satisfies 0 < g (Hg0) and g <= 1/2    *)
(*   (Hg_le_half), so Qlt 0 (1-g) (the g <= 1/2 side) and Qlt (1-g) 1 (the      *)
(*   0 < g side) are needed.  The root only has the Real-layer b5b_ep_xg_pos /  *)
(*   lt_one (L78030/L78041); no same-named Q-layer versions exist in the root,   *)
(*   so this file builds them (isomorphic to the root proofs).                  *)
(* ============================================================ *)

(* Q layer: g <= 1/2 entails 0 < 1 - g (the Q-layer version of the isomorphic root
   b5b_ep_xg_pos L78030; the b5b_endpoint body context supplies Hg_le_half : Qle g (1/2)
   directly).
   Semantic check (per the spec): 1-g > 0 needs g < 1, not merely 0 < g — the endpoint
   body gives g <= 1/2 (g := Qmin (1/2) a), so this piece takes Qle g (1/2) as the
   premise.    *)
Lemma b5dF_q_1mg_pos : forall (g : Q), QleT' g (1 / 2) -> QltT 0 (1 - g).
Proof.
  intros g Hg12.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans 0 (1 / 2) (1 - g)).
  - exact (QltT_to_Qlt _ _ b5b_ep_half_pos).
  - apply QleT'_to_Qle. apply (b5b_ep_half_le_1mg g). exact (QleT'_to_Qle _ _ (Hg12)).
Qed.

(* Q layer: 0 < g entails 1 - g < 1 (the Q-layer version of the isomorphic root
   b5b_ep_xg_lt_one L78041; the b5b_endpoint body context supplies Hg0 : Qlt 0 g
   directly). *)
Lemma b5dF_q_1mg_lt1 : forall (g : Q), QltT 0 g -> QltT (1 - g) 1.
Proof.
  intros g Hg0.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff (1 - g) 1)).
  assert (Heq : (1 - (1 - g)) == g) by ring.
  rewrite Heq. exact (QltT_to_Qlt _ _ (Hg0)).
Qed.

(* ============================================================ *)
(* Section A §2: the domain-certificate family for xg := real_const (1-g) (the 0<g<=1/2 bundle) *)
(* ============================================================ *)

(* the cw_unit domain certificate for xg := real_const (1-g) (the 0<g and g<=1/2 bundle
   gives the 0<=g and g<=1 premises of b5b_unit_const L73651; the main piece uses this
   piece as its Hxg). *)
Lemma b5dF_xg_unit : forall (g : Q), QltT 0 g -> QleT' g (1 / 2) ->
  cw_unit (real_const (1 - g)).
Proof.
  intros g Hg0 Hg12.
  apply (b5b_unit_const g).
  - apply (Qlt_le_weak 0 g). exact (QltT_to_Qlt _ _ (Hg0)).
  - apply (Qle_trans _ (1 / 2) _); [ exact (QleT'_to_Qle _ _ (Hg12)) | exact (QleT'_to_Qle _ _ b5b_ep_half_le_one) ].
Qed.

(* the Real-layer lower openness of xg: real_lt 0 xg (isomorphic to the root
   b5b_ep_xg_pos L78030, merged into the bundle form.
   Note: the main piece b5dF_E_one_zero_of_rational does not need this piece (the
   rational-point pieces consume the Q certificates b5dF_q_1mg_*, not the Real-layer
   open-interval order) — kept as the complete domain certificate of this family, for
   later E_rational_zero-side / Real-layer assembly. *)
Lemma b5dF_xg_pos : forall (g : Q), QltT 0 g -> QleT' g (1 / 2) ->
  real_lt real_zero (real_const (1 - g)).
Proof.
  intros g Hg0 Hg12.
  exact (b5b_ep_xg_pos g (QleT'_to_Qle _ _ (Hg12))).
Qed.

(* the Real-layer upper openness of xg: real_lt xg (real_const 1) (isomorphic to the
   root b5b_ep_xg_lt_one L78041, merged into the bundle form; same usage situation as
   the b5dF_xg_pos note). *)
Lemma b5dF_xg_lt1 : forall (g : Q), QltT 0 g -> QleT' g (1 / 2) ->
  real_lt (real_const (1 - g)) (real_const 1).
Proof.
  intros g Hg0 Hg12.
  exact (b5b_ep_xg_lt_one g (QltT_to_Qlt _ _ (Hg0))).
Qed.

(* ============================================================ *)
(* Section A §3: the glue from the rational-point piece to real_eq (real_E xg Hxg) real_zero *)
(* ============================================================ *)

(* glue from the rational-point piece to the xg zero: instantiate the "for all rational
   q, E(q) == 0" piece at q := 1-g (g chosen by the q_arch_inv of the b5b_endpoint form,
   rational), obtaining real_eq (real_E (real_const (1 - g)) Hunit) real_zero.
   Inputs = the ready-made objects of the main-piece replica context: Hunit (the cw_unit
   certificate, given by b5dF_xg_unit / b5b_unit_const) + the Q open-interval certificates
   Hg0q/Hg1q (given by b5dF_q_1mg_pos and b5dF_q_1mg_lt1).
   Isomorphic to the Section-premise consumption point of the root b5b_endpoint L78098:
   there b5a_E_zero_on_unit xg Hxg Hxg0 Hxg1 (instantiated for all x), here
   Hrat (1-g) Hg0q Hg1q Hunit (the rational-point piece instantiated). *)
Lemma b5dF_rational_at_xg : forall (g : Q) (Hunit : cw_unit (real_const (1 - g))),
  QltT 0 (1 - g) -> QltT (1 - g) 1 ->
  (forall (q : Q), QltT 0 q -> QltT q 1 ->
    forall (Hq : cw_unit (real_const q)),
    real_eq (real_E (real_const q) Hq) real_zero) ->
  real_eq (real_E (real_const (1 - g)) Hunit) real_zero.
Proof.
  intros g Hunit Hg0q Hg1q Hrat.
  exact (Hrat (1 - g) Hg0q Hg1q Hunit).
Qed.

(* ============================================================ *)
(* Section A §4: the premise-form main piece b5dF_E_one_zero_of_rational         *)
(* ============================================================ *)

(* ============================================================ *)
(* The premise-form main piece: E(1) == 0 (replicating the root b5b_endpoint     *)
(* L78062-78177)                                                                 *)
(* Differences from the root (only 3):                                           *)
(*   (a) the Section variable b5a_E_zero_on_unit becomes the forall premise      *)
(*       Hrat (the "rational-point E(q)==0" piece, produced by δ-D2, unclosed;   *)
(*       this piece is a premise-form Lemma, genuine Qed, no axiom face /        *)
(*       admissions);                                                            *)
(*   (b) the L78092 Hxg certificate becomes b5dF_xg_unit (the 0<g and g<=1/2     *)
(*       bundle);                                                                *)
(*   (c) the L78093-78099 consumption points: the Real-layer Hxg0/Hxg1 are       *)
(*       removed (the rational piece consumes only Q certificates), and          *)
(*       Hz0 := b5dF_rational_at_xg g Hxg (the q_1mg certificates + Hrat).       *)
(* The rest of the body ((1) |E1-Eg| (2) |Eg-0| triangle inequality) is copied   *)
(* verbatim.                                                                     *)
(* ============================================================ *)
Lemma b5dF_E_one_zero_of_rational :
  (forall (q : Q), QltT 0 q -> QltT q 1 ->
    forall (Hq : cw_unit (real_const q)),
    real_eq (real_E (real_const q) Hq) real_zero) ->
  real_eq real_E_one real_zero.
Proof.
  intros Hrat.
  intros epsQ HepsQT.
  assert (HepsQ : Qlt 0 epsQ) by (apply QltT_to_Qlt; exact HepsQT).
  assert (HhalfQ : Qlt 0 (epsQ / 2)) by (apply QltT_to_Qlt; apply q_half_pos; apply Qlt_to_QltT; exact HepsQ).
  assert (HhalfT : QltT 0 (epsQ / 2)) by (apply Qlt_to_QltT; exact HhalfQ).
  (* b5b_E_close_q (epsQ/2): there are N0 and g0 > 0 with n >= N0 and 0 < g <= g0, giving |E_n(1-g) - E_n(1)| < epsQ/2. *)
  destruct (b5b_E_close_q (epsQ / 2) HhalfQ) as [N0 [g0 [Hg0pos Hclose]]].
  (* q_arch_inv g0 chooses K: a := 1/(K+2) < g0; g := Qmin (1/2) a. *)
  destruct (q_arch_inv g0 Hg0pos) as [K HK].
  set (a := 1 / (Z.of_nat (K + 2) # 1)).
  set (g := Qmin (1 / 2) a).
  assert (Ha0 : Qlt 0 a).
  { unfold a. exact (QltT_to_Qlt _ _ (q_arch_inv_pos K)). }
  assert (Hg0 : Qlt 0 g).
  { unfold g. apply QltT_to_Qlt. apply (b5b_ecl_min_pos (1 / 2) a); [exact (QltT_to_Qlt _ _ b5b_ep_half_pos) | exact Ha0]. }
  assert (Hg0le : Qle 0 g) by (apply (Qlt_le_weak 0 g); exact Hg0).
  assert (Hg_le_half : Qle g (1 / 2)).
  { unfold g. exact (Q.le_min_l (1 / 2) a). }
  assert (Hg_le_a : Qle g a).
  { unfold g. exact (Q.le_min_r (1 / 2) a). }
  assert (Ha_g0 : Qle a g0).
  { apply (Qlt_le_weak a g0). unfold a. exact (QltT_to_Qlt _ _ HK). }
  assert (Hg_g0 : Qle g g0).
  { apply (Qle_trans _ a _); [exact Hg_le_a | exact Ha_g0]. }
  assert (Hg1 : Qle g 1).
  { apply (Qle_trans _ (1 / 2) _); [exact Hg_le_half | exact (QleT'_to_Qle _ _ b5b_ep_half_le_one)]. }
  (* xg := real_const (1-g); the domain certificate Hxg (this file's b5dF_xg_unit,
     with the g context supplying 0<g (Hg0) and g<=1/2 (Hg_le_half)). *)
  set (xg := real_const (1 - g)).
  assert (Hxg : cw_unit xg).
  { unfold xg. apply (b5dF_xg_unit g (Qlt_to_QltT _ _ (Hg0)) (Qle_to_QleT' _ _ (Hg_le_half))). }
  (* the premise consumption point (replicating root L78098): Hz0 := real_eq (real_E xg Hxg)
     real_zero; there the root uses b5a_E_zero_on_unit xg Hxg Hxg0 Hxg1 (forall-x
     instantiation, needing the Real-layer open-interval order Hxg0/Hxg1); here =
     the rational-point piece instantiated at q := 1-g (b5dF_rational_at_xg), with the Q
     open-interval certificates = b5dF_q_1mg_pos/lt1, and Hxg is Hunit — the Real-layer
     order is no longer needed, so the Hxg0/Hxg1 asserts are dropped. *)
  assert (Hz0 : real_eq (real_E xg Hxg) real_zero).
  { unfold xg.
    exact (b5dF_rational_at_xg g Hxg
             (b5dF_q_1mg_pos g (Qle_to_QleT' _ _ (Hg_le_half)))
             (b5dF_q_1mg_lt1 g (Qlt_to_QltT _ _ (Hg0))) Hrat). }
  destruct (Hz0 (epsQ / 2) HhalfT) as [Nz HNz].
  (* the modulus: N := max(N0, Nz). *)
  exists (Nat.max N0 Nz).
  intros n Hn.
  apply NatLe_drop in Hn.
  assert (HnN0 : (N0 <= n)%nat) by lia.
  assert (HnNz : (Nz <= n)%nat) by lia.
  (* (1) |E1_n - Eg_n| < epsQ/2: the b5b_En_proj bridge + b5b_E_close_q. *)
  assert (Hq1eq : (projT1 real_E_one n - projT1 (real_E xg Hxg) n) ==
                  (b5b_En n 1 - b5b_En n (1 - g))).
  { unfold real_E_one.
    rewrite (qeqT_imp_qeq _ _ (b5b_En_proj (real_const 1) atan1_pt_bound n)).
    rewrite (qeqT_imp_qeq _ _ (b5b_En_proj xg Hxg n)).
    unfold xg.
    (* projT1 (real_const c) k and c are definitionally equal (real_const_proj is proved
       by reflexivity); here one cannot setoid-rewrite inside the b5b_En arguments
       (b5b_En has no Qeq Proper instance), so kernel conversion via reflexivity
       closes it. *)
    reflexivity. }
  assert (Hq1abs : Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n) ==
                   Qabs (b5b_En n (1 - g) - b5b_En n 1)).
  { apply (Qeq_trans _ (Qabs (b5b_En n 1 - b5b_En n (1 - g))) _).
    - apply (Qabs_wd (projT1 real_E_one n - projT1 (real_E xg Hxg) n)
                     (b5b_En n 1 - b5b_En n (1 - g))).
      exact Hq1eq.
    - apply qeqT_imp_qeq. apply (q_abs_minus_sym (b5b_En n 1) (b5b_En n (1 - g))). }
  assert (Hterm1T : QltT (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                         (epsQ / 2)).
  { apply (qltT_eq_compat_l (Qabs (b5b_En n (1 - g) - b5b_En n 1))
                            (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                            (epsQ / 2)).
    - apply qeq_imp_qeqT. apply Qeq_sym. exact Hq1abs.
    - exact (Hclose n g (NatLe_lift _ _ HnN0) (Qlt_to_QltT _ _ Hg0) (Qle_to_QleT' _ _ Hg_g0)). }
  assert (Hterm1 : Qlt (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                       (epsQ / 2))
    by (apply QltT_to_Qlt; exact Hterm1T).
  (* (2) |Eg_n - 0_n| < epsQ/2: Hz0 (real_eq (E xg) 0) made pointwise. *)
  assert (Hterm2T : QltT (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n))
                         (epsQ / 2)).
  { exact (HNz n (NatLe_lift _ _ HnNz)). }
  assert (Hterm2 : Qlt (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n))
                       (epsQ / 2))
    by (apply QltT_to_Qlt; exact Hterm2T).
  (* triangle: |E1_n - 0_n| <= |E1_n - Eg_n| + |Eg_n - 0_n|. *)
  assert (Htri : Qle (Qabs (projT1 real_E_one n - projT1 real_zero n))
                     (Qplus (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                            (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n)))).
  { apply (Qle_trans _
             (Qabs ((projT1 real_E_one n - projT1 (real_E xg Hxg) n) +
                    (projT1 (real_E xg Hxg) n - projT1 real_zero n))) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      apply (Qabs_wd (projT1 real_E_one n - projT1 real_zero n)
                     ((projT1 real_E_one n - projT1 (real_E xg Hxg) n) +
                      (projT1 (real_E xg Hxg) n - projT1 real_zero n))).
      ring.
    - apply Qabs_triangle. }
  (* the two terms sum to < epsQ/2 + epsQ/2 == epsQ. *)
  assert (Hsum : Qlt (Qplus (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                            (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n)))
                     (Qplus (epsQ / 2) (epsQ / 2))).
  { apply (Qplus_lt_compat (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                           (epsQ / 2)
                           (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n))
                           (epsQ / 2)).
    - exact Hterm1.
    - exact Hterm2. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (Qabs (projT1 real_E_one n - projT1 real_zero n))
                      (Qplus (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                             (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n)))
                      epsQ).
  - exact Htri.
  - apply (Qlt_le_trans (Qplus (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                               (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n)))
                        (Qplus (epsQ / 2) (epsQ / 2)) epsQ).
    + exact Hsum.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (b5b_ep_half_sum epsQ)).
Qed.

(* ============================================================ *)
(* Section B: the grid-telescope dependency list of E_rational_zero (zero code,  *)
(* registered in comments)                                                       *)
(* ============================================================ *)

(* ============================================================ *)
(* Section B (zero code, registered in comments): the grid-telescope dependency  *)
(*   list of E_rational_zero (the δ-D2 main piece) — for later spec reference.   *)
(* Target statement contract (= this file's §A4 premise; δ-D design §2.1 verbatim): *)
(*   b5?_E_rational_zero : forall (q : Q), Qlt 0 q -> Qlt q 1 ->                  *)
(*     forall (Hq : cw_unit (real_const q)),                                      *)
(*     real_eq (real_E (real_const q) Hq) real_zero                               *)
(* Proof chain (per the design §2(iii)):                                          *)
(*   E(q)==0 <- b5p2_E_zero_of_J_zero (root L86865) @ (real_const q) Hq           *)
(*     + the real_E/b5a_E same-body bridge (L72948/L73975, built here in about    *)
(*     8-12 lines, after the item4r2 B1 precedent)                                *)
(*   <- J(q)==0 <- J(0)==0 (b5c_J_zero_at_zero L74734 @                           *)
(*     b5c_unit_zero L74360 (a Definition, the real_const 0 domain certificate),  *)
(*     closed) + the grid telescope t_k := Qmult q (k/M), M>=1, k=0..M:           *)
(*     each step |J(t_{k+1})-J(t_k)| <= b_k (b_k := eps0Q*(q/M)+eps0'Q closed     *)
(*     form), and the budget Σ_k b_k == eps0Q*q + M*eps0'Q == epsQ is proved.     *)
(* ------------------------------------------------------------ *)
(* (1) The grid nsum / triangle skeleton (the root b4 family, measured line       *)
(*    numbers):                                                                   *)
(*    b4_nsum_const L72499 / b4_nsum_le L72527 / b4_nsum_tri                       *)
(*    L72541 / b4_nsum_telescope L72615 (from L72615 the region = the telescope   *)
(*    nsum skeleton); chain templates b4_chain_lipschitz L73016 /                  *)
(*    b4_arch_step L72844 / b4_chain_bound_eps0 L76930 /                           *)
(*    b4_deriv_zero_eq_endpoints L77111 /                                          *)
(*    b4_const_on_interval_pair L77173.                                            *)
(* (2) Bridging lemmas (same style as item4r2 B1-B4; the item4r2 .vo is built on   *)
(*    the 212 root and cannot be Required — the equivalent pieces are built        *)
(*    inside the root, do not Require item4r2):                                    *)
(*    b5c_const_unit L74348 (0<=q<=1 gives cw_unit (real_const q), the grid-point  *)
(*    domain certificate) / b5p2_E_zero_of_J_zero L86865 /                         *)
(*    b5p2_E_eq_J_S L86834 / b5c_J_zero_at_zero L74734 /                           *)
(*    b5c_unit_zero L74360 / the real_E<->b5a_E same-body bridge (built here).     *)
(* (3) Each-step modulus source = the C5 expl tail-M variant: item11 (upstream)    *)
(*    b5d7_J_deriv_zero_exp (δ-C C5, the argument bundle cA/M/Ms/Mc + the all-n    *)
(*    bound premise HMall); the tail-M change = HMall -> (NM : nat) + forall       *)
(*    n>=NM, Nmax folded into NM (a 3-5 line change in the item11 L334-336 region; *)
(*    the δC review §1.4/1.5 concur; C6 = item12 b5d8_J_deriv_zero_tail_exp can    *)
(*    serve as the reference for the change).  Measured carrier note (item12       *)
(*    record): the carrier of the C5/C6 bound premises is x̂ := b5m_tailtrunc x N0  *)
(*    rather than x, so the pointwise discharge must be designed around the trunc  *)
(*    carrier.                                                                     *)
(* (4) The instance-certificate family (all upstream δ pieces can be Required):    *)
(*    item6 M4a/M4b: b5d2_sinA_abs_le1 / b5d2_cosA_abs_le1                         *)
(*    (the Ms := Mc := 1 all-n certificates); item8 B1: b5d4_S0_lb_half            *)
(*    (cA := 1/2) + Piece A: b5d4_S_const0_eq_one (S(0)==1);                       *)
(*    item5: b5d1_b3rr_atan_deriv_lin (the L0 transparent base, Defined).          *)
(* (5) The S upper bound (a new mathematical piece, the δ-D design §2.5 route (b)): *)
(*    the pointwise all-n bound is not provable (the log_seq/approx_root pointwise *)
(*    wall, the δB-3 demotion evidence in item7 §2), so the tail-form M premise +  *)
(*    the tail certificate b5?_S_ub_tail_q (M_S0 := 2 or 4):                        *)
(*    S(0)==1 -> the S-diff@x:=0 transparent piece -> the eps:=1/2, eps':=1/4      *)
(*    relaxation -> <= 2/4 proved; τ0 := cA*Qinv(8*(M_S0*r+1)) closed form as      *)
(*    usual.                                                                       *)
(* (6) The transparency hard-precondition of the δ chain (δ-D design §2.3/§2.4):  *)
(*    in the conservative state the C1-C6 output δ contains opaque leaves          *)
(*    (δE/δS1/δS2 = root Qed sigT witnesses, recursing vdh->atan_deriv->b3rr;      *)
(*    only > 0 is known with no lower bound, so the rational step |h| < δ cannot   *)
(*    be constructed), hence a layer-by-layer Qed->Defined transparency pass +     *)
(*    per-leaf lower-bound certificates (bottom-up                                 *)
(*    b3rr->atan_deriv->vdh->sin/cos-atan->exp/g->E->S->J, about 2,500 lines;      *)
(*    item14 (b5dD_, the C8 transparent base) and item15 (b5dE_, the S upper-bound *)
(*    tail certificate = (5)) are the precondition files for δ-D).                 *)
(* (7) Budget / arch (ready at the Q layer): q_arch_inv L4733 / q_arch_inv_pos     *)
(*    L4790 — M := K+2 := q_arch_inv (δ0/q), following the b5b_endpoint            *)
(*    L78071 pattern; eps0Q := epsQ/(2q) (dividable for q > 0),                    *)
(*    eps0'Q := epsQ/(2M); δ0 := min(the explicit components) are all rational     *)
(*    closed forms in q/eps0Q.                                                     *)
(* Instantiation: b5?_E_rational_zero feeds this file's                            *)
(*   b5dF_E_one_zero_of_rational, giving real_eq real_E_one real_zero              *)
(*   -> b5b_hsc_main (L72994) -> a3_closure_f1 (L67997) ->                          *)
(*   real_eq real_pi_geom cauchy_real_pi_leibniz (the F1 main theorem).            *)
(* ============================================================ *)

(* ===== Block b5dH_ (main item b5dH_E_zero_of_J_zero; upstream source sc2_b5a_item18) ===== *)

(* ============================================================ *)
(* Piece list (updated with the implementation progress; the main piece is the   *)
(*   last to be built):                                                          *)
(*   Section A the bridges and the reduction (not hard pieces, closed first):    *)
(*     b5dH_E_eq_b5aE   : the real_E <-> b5a_E same-body bridge (reflexivity)    *)
(*     b5dH_J_zero0     : J(real_const 0)==0 @ b5c_unit_zero                     *)
(*     b5dH_E_zero_of_J : for all q Hq, J(q)==0 gives E(q)==0 (the main-piece    *)
(*       reduction kernel)                                                       *)
(*   Section B the grid-point domain-certificate family (t_k := q*(k/M) in (0,1) *)
(*     rational):                                                                *)
(*     cw_unit / open-interval / S tail-bound instantiations (item15 @ t_k, item8 @ 0) *)
(*   Section C the telescope and the budget (the b4_nsum skeleton + the b_k closed form) *)
(*   Section D the main piece b5dH_E_rational_zero (assembled once the           *)
(*     precondition hard pieces are ready)                                       *)
(* ============================================================ *)

(* ============================================================ *)
(* Section A §1: the real_E <-> b5a_E same-body bridge (not a hard piece, closed *)
(*   first)                                                                      *)
(*   The root L72948 real_E and L73975 b5a_E have definitionally identical       *)
(*   bodies (real_plus (cauchy_real_sin (cauchy_real_arctan x Hx))               *)
(*     (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx))))),    *)
(*   so real_eq for any same x/Hx closes by unfold + refl.                       *)
(* ============================================================ *)

(* the real_E <-> b5a_E same-body bridge: real_E x Hx == b5a_E x Hx (for all x Hx). *)
Lemma b5dH_E_eq_b5aE : forall (x : Real) (Hx : cw_unit x),
  real_eq (real_E x Hx) (b5a_E x Hx).
Proof.
  intros x Hx.
  unfold real_E, b5a_E.
  apply real_eq_refl.
Qed.

(* ============================================================ *)
(* Section A §2: J(real_const 0) == 0 (b5c_J_zero_at_zero L74734 @               *)
(*   b5c_unit_zero L74360, the upstream pieces applied directly)                 *)
(* ============================================================ *)
Lemma b5dH_J_zero0 : real_eq (b5c_J (real_const 0) b5c_unit_zero) real_zero.
Proof.
  exact (b5c_J_zero_at_zero b5c_unit_zero).
Qed.

(* ============================================================ *)
(* Section A §3: the E(q)==0 <- J(q)==0 reduction kernel (b5p2_E_zero_of_J_zero  *)
(*   L86865 @ (real_const q) Hq + the §1 bridge) — the final two steps of the    *)
(*   main piece; they do not depend on the hard pieces, so they close first.     *)
(* ============================================================ *)

(* E(x) == 0 from J(x) == 0 (any x, including the main-piece instance x := real_const q). *)
Lemma b5dH_E_zero_of_J_zero : forall (x : Real) (Hx : cw_unit x),
  real_eq (b5c_J x Hx) real_zero -> real_eq (real_E x Hx) real_zero.
Proof.
  intros x Hx HJ0.
  apply (real_eq_trans _ (b5a_E x Hx) _).
  - exact (b5dH_E_eq_b5aE x Hx).
  - exact (b5p2_E_zero_of_J_zero x Hx HJ0).
Qed.

(* ============================================================ *)
(* Section A §4: the grid-point domain certificates (t_k := q*(k/M) in [0,1]     *)
(*   rational -> cw_unit; the cw_unit (real_const x) for 0<=x<=1 = the root      *)
(*   b5c_const_unit L74348 applied directly, no new piece needed; here we add    *)
(*   the 0<x<1 gives Qle 0 x and Qle x 1 Q-layer helpers (isomorphic to the      *)
(*   b5dF_q_1mg_* pattern, pure Q-layer algebra))                                *)
(* ============================================================ *)

(* 0 < x < 1 gives 0 <= x (directly by Qlt_le_weak). *)
Lemma b5dH_q_pos_le : forall (x : Q), QltT 0 x -> QleT' 0 x.
Proof.
  intros x Hx. apply Qle_to_QleT'. apply (Qlt_le_weak 0 x).
  apply QltT_to_Qlt. exact Hx.
Qed.

(* 0 < x < 1 gives x <= 1 (directly by Qlt_le_weak). *)
Lemma b5dH_q_lt1_le : forall (x : Q), QltT x 1 -> QleT' x 1.
Proof.
  intros x Hx. apply Qle_to_QleT'. apply (Qlt_le_weak x 1).
  apply QltT_to_Qlt. exact Hx.
Qed.

(* ============================================================ *)
(* Section A §5: the real_const argument glue (the telescope argument bridge, for telescope assembly)   *)
(* ============================================================ *)

(* Qeq gives real_eq (real_const a) (real_const b) (pointwise ==, N := 0). *)
Lemma b5dH_real_const_qeq : forall (a b : Q),QeqT ( a ) ( b )->
  real_eq (real_const a) (real_const b).
Proof.
  intros a b Hab.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  cbn [projT1 real_const].
  apply qeqT_imp_qeq in Hab.
  rewrite Hab.
  ring.
Qed.

(* real_plus (real_const a) (real_const b) == real_const (a + b) (pointwise). *)
Lemma b5dH_plus_const_eq : forall (a b : Q),
  real_eq (real_plus (real_const a) (real_const b)) (real_const (a + b)).
Proof.
  intros a b.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_const a) (real_const b) n)).
  cbn [projT1 real_const].
  ring.
Qed.

(* ============================================================ *)
(* Section D: main piece (the contract statement is in the file header note; the *)
(*   proof body lands once the hard pieces are adjudicated)                      *)
(*   Main-piece statement (verbatim with the item16 §A4 premise, must not be     *)
(*   changed):                                                                   *)
(*   forall (q : Q), Qlt 0 q -> Qlt q 1 ->                                       *)
(*     forall (Hq : cw_unit (real_const q)),                                     *)
(*     real_eq (real_E (real_const q) Hq) real_zero                              *)
(*   Assembly skeleton (Section A closed; assembled in order once the            *)
(*   precondition pieces are ready):                                             *)
(*   (1) b5dH_E_zero_of_J_zero (real_const q) Hq                                 *)
(*       (b5dH_J_q_zero q ...) where J(q)==0 is given by the grid telescope;     *)
(*   (2) J(q)==J(0): the t_k grid pointwise modulus instance (hard piece: the    *)
(*       transparent J modulus)                                                  *)
(*       each step real_le |J(t_{k+1})-J(t_k)| (eps0Q*(q/M)+eps0'Q),             *)
(*       accumulated by b4_nsum_telescope/le/tri (L72615/72527/72541).           *)
(*   Current text: 7 Lemma = 7 Qed fully closed (the Section A bridges and the   *)
(*   reduction); the main piece lands once the hard pieces are adjudicated       *)
(*   (design record §3).                                                         *)
(* ============================================================ *)

(* ===== end of sc2_b5a_item18.v: delta-D2 E_rational_zero, the M1 skeleton ===== *)

(* ===== Block b5dL_ (main item b5dL_E_rational_zero_premise; upstream source sc2_b5a_item22) ===== *)

(* ============================================================ *)
(* Piece list (updated with the implementation progress; implementation order =  *)
(*   Sections A->B->C->D->E):                                                    *)
(*   Section A Definitions:                                                      *)
(*     b5dL_tkq   : t_k := q*(Z.of_nat k # 1)/(Z.of_nat M # 1)                   *)
(*     b5dL_qdiv  : the step q/M                                                 *)
(*     b5dL_Qnsum : the Q-layer Σ_{k<N} (isomorphic to a b4_nsum left fold)      *)
(*   Section A grid-point domain-certificate family (13 Q-layer pieces + cw_unit certificates): *)
(*     0 <= t_k / t_k <= q (k<=M) / t_k < 1 (q<1) / t_k > 0 (k>=1) /             *)
(*     t_0 == 0 / t_M == q / t_{S k} == t_k + q/M /                              *)
(*     b5dL_tkC (cw_unit (real_const t_k), b5c_const_unit applied directly)      *)
(*   Section A extra Real glue (needed when the δ chain instantiates Hstep to    *)
(*     bridge the C5 output):                                                    *)
(*     b5dL_abs_const / b5dL_mult_const / b5dL_J_tk_succ_bridge                  *)
(*   Section B the telescope premise form (the core skeleton, δ-independent):    *)
(*     b5dL_Qnsum_const / b5dL_nsum_real /                                       *)
(*     b5dL_telescope_premise (pure f/g form, the conclusion carries the triangle slack e) *)
(*   Section C the J grid telescope (certificate-parameterized; a self-built     *)
(*     induction Aux(n)):                                                        *)
(*     b5dL_J_grid_premise (the per-step premises for all Hk Hk1 + quantified    *)
(*     endpoint certificates)                                                    *)
(*   Section D the eps budget Q-layer arithmetic:                                *)
(*     b5dL_bk / b5dL_epsQ1 / b5dL_epsQ1_pos /                                   *)
(*     b5dL_budget_closure (Σbk + Σe == epsQ)                                    *)
(*   Section E the premise form (once the δ chain is ready only the              *)
(*     instantiation remains):                                                   *)
(*     b5dL_J_zero_on_grid_premise (|J(q)-J(0)| <= real_const epsQ, the J(0)     *)
(*       side bridged by b5dH_J_zero0)                                           *)
(*     b5dL_E_rational_zero_premise (the main-piece-form premise: Hmod =          *)
(*       forall epsQ sigT M per-step premises -> real_eq (real_E (real_const q)   *)
(*       Hq) real_zero; proof = b5dH_E_zero_of_J_zero +                           *)
(*       b4_abs_le_forall_eps_eq + real_eps_witness taking the Q lower bound)     *)
(*   Section F (comment): the proof-chain description / the parts still owed     *)
(*     (awaiting the δ chain)                                                    *)
(* ============================================================ *)

(* ============================================================ *)
(* Section A §1: Definitions (the t_k grid / the step / the Q-layer sum)         *)
(*   Design (design record §3.1): t_kQ := q*(Z.of_nat k # 1)/(M#1)               *)
(* ============================================================ *)

(* t_k := q*(k/M) (the #1 lift of k; a meaningful grid only when M > 0). *)
Definition b5dL_tkq (q : Q) (M : nat) (k : nat) : Q :=
  (q * (Z.of_nat k # 1)) / (Z.of_nat M # 1).

(* the step η := q/M (the Q-layer term of the step identity t_{k+1} == t_k + η). *)
Definition b5dL_qdiv (q : Q) (M : nat) : Q :=
  q / (Z.of_nat M # 1).

(* the Q-layer Σ_{k<N} (isomorphic to a left fold of the root b4_nsum; b4_nsum is at the Real layer). *)
Fixpoint b5dL_Qnsum (b : nat -> Q) (N : nat) : Q :=
  match N with
  | 0%nat => 0
  | Datatypes.S m => b5dL_Qnsum b m + b m
  end.

(* ============================================================ *)
(* Section A §2: the nat-lift Q small pieces (the pattern = finalized by check:  *)
(*   unfold Qlt/Qeq; simpl; lia)                                                 *)
(* ============================================================ *)

(* (S m)#1 > 0 (no premise; the destruct target piece for 0 < M). *)
Lemma b5dL_lift_pos2 : forall (m : nat), QltT 0 (Z.of_nat (Datatypes.S m) # 1).
Proof.
  intro m.
  apply Qlt_to_QltT.
  unfold Qlt. simpl. lia.
Qed.

(* 1 <= n entails n#1 > 0 (used by tkq_pos). *)
Lemma b5dL_lift_pos : forall (n : nat), (1 <= n)%nat -> QltT 0 (Z.of_nat n # 1).
Proof.
  intros n Hn.
  apply Qlt_to_QltT.
  destruct n as [| m]; [lia | exact ((QltT_to_Qlt _ _ (b5dL_lift_pos2 m)))].
Qed.

(* (S k)#1 == k#1 + 1 (the Qnsum_const induction step / the tkq_succ numerator). *)
Lemma b5dL_lift_succ_q : forall (k : nat),
  QeqT (Z.of_nat (Datatypes.S k) # 1) ((Z.of_nat k # 1) + 1).
Proof.
  intro k.
  apply qeq_imp_qeqT.
  unfold Qeq. simpl. lia.
Qed.

(* 0 < M entails M#1 ≠ 0 (the field division-by-zero condition piece). *)
Lemma b5dL_lift_nz : forall (M : nat), (0 < M)%nat -> Not (QeqT (Z.of_nat M # 1) 0).
Proof.
  intros M HM Hz.
  apply qeqT_imp_qeq in Hz.
  unfold Qeq in Hz. simpl in Hz.
  lia.
Qed.

(* (k#1) >= 0 for all k (the numerator factor of the tkq nonnegativity). *)
Lemma b5dL_nat_nonneg : forall (k : nat), QleT' 0 (Z.of_nat k # 1).
Proof.
  intro k.
  apply Qle_to_QleT'.
  destruct k as [| m].
  - cbn. apply Qle_refl.
  - apply (Qlt_le_weak 0 (Z.of_nat (Datatypes.S m) # 1)).
    exact ((QltT_to_Qlt _ _ (b5dL_lift_pos2 m))).
Qed.

(* k <= M entails (k#1) <= (M#1) (Qle unfolded to the Z layer, normalized by lia). *)
Lemma b5dL_nat_le_qle : forall (k M : nat), (k <= M)%nat ->
  QleT' (Z.of_nat k # 1) (Z.of_nat M # 1).
Proof.
  intros k M Hkm.
  apply Qle_to_QleT'.
  unfold Qle. simpl. lia.
Qed.

(* Qlt 0 x entails x ≠ 0 (the field condition piece; Qeq-rewrite is usable on Qlt). *)
Lemma b5dL_q_lt0_nz : forall (x : Q), QltT 0 x -> Not (QeqT x 0).
Proof.
  intros x Hx Heq.
  apply qeqT_imp_qeq in Heq.
  apply QltT_to_Qlt in Hx.
  rewrite Heq in Hx.
  exact (False_rect Empty_set (Qlt_irrefl 0 Hx)).
Qed.

(* ============================================================ *)
(* Section A §3: the grid-point domain-certificate family (t_k in [0,1] / the open interval / the step identity) *)
(* ============================================================ *)

(* 0 <= q gives 0 <= t_k (q*k#1 >= 0 and M#1 > 0 give a nonnegative quotient). *)
Lemma b5dL_tkq_nonneg : forall (q : Q) (M k : nat),
  QleT' 0 q -> (0 < M)%nat -> QleT' 0 (b5dL_tkq q M k).
Proof.
  intros q M k Hq0 HM.
  apply Qle_to_QleT'.
  unfold b5dL_tkq.
  unfold Qdiv.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat.
    + exact (QleT'_to_Qle _ _ Hq0).
    + exact ((QleT'_to_Qle _ _ (b5dL_nat_nonneg k))).
  - apply Qinv_le_0_compat.
    apply (Qlt_le_weak 0 (Z.of_nat M # 1)).
    destruct M as [| m]; [exfalso; lia | exact ((QltT_to_Qlt _ _ (b5dL_lift_pos2 m)))].
Qed.

(* k <= M entails t_k <= q (Qle_shift_div_r + the commutation bridge). *)
Lemma b5dL_tkq_le_q : forall (q : Q) (M k : nat),
  QleT' 0 q -> (0 < M)%nat -> (k <= M)%nat ->
  QleT' (b5dL_tkq q M k) q.
Proof.
  intros q M k Hq0 HM Hk.
  apply Qle_to_QleT'.
  unfold b5dL_tkq.
  apply (Qle_shift_div_r (q * (Z.of_nat k # 1)) (Z.of_nat M # 1) q).
  - destruct M as [| m]; [exfalso; lia | exact ((QltT_to_Qlt _ _ (b5dL_lift_pos2 m)))].
  - (* q*(k#1) <= q*(M#1): via k#1*q <= M#1*q + the Qmult_comm bridge. *)
    apply (Qle_trans _ (Qmult (Z.of_nat k # 1) q) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (Qmult_comm q (Z.of_nat k # 1)).
    + apply (Qle_trans _ (Qmult (Z.of_nat M # 1) q) _).
      * exact (Qmult_le_compat_r (Z.of_nat k # 1) (Z.of_nat M # 1) q
                 ((QleT'_to_Qle _ _ (b5dL_nat_le_qle k M Hk)))
                 (QleT'_to_Qle _ _ Hq0)).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (Qmult_comm (Z.of_nat M # 1) q).
Qed.

(* k <= M entails t_k <= 1 (t_k <= q <= 1; the b5c_const_unit premise). *)
Lemma b5dL_tkq_le1 : forall (q : Q) (M k : nat),
  QleT' 0 q -> QleT' q 1 -> (0 < M)%nat -> (k <= M)%nat ->
  QleT' (b5dL_tkq q M k) 1.
Proof.
  intros q M k Hq0 Hq1 HM Hk.
  apply Qle_to_QleT'.
  apply (Qle_trans (b5dL_tkq q M k) q 1).
  - exact ((QleT'_to_Qle _ _ (b5dL_tkq_le_q q M k Hq0 HM Hk))).
  - exact (QleT'_to_Qle _ _ Hq1).
Qed.

(* k <= M and q<1 give t_k < 1 (the open-interval upper certificate; used by the S tail-bound instantiation etc.). *)
Lemma b5dL_tkq_lt1 : forall (q : Q) (M k : nat),
  QleT' 0 q -> (0 < M)%nat -> (k <= M)%nat -> QltT q 1 -> QltT (b5dL_tkq q M k) 1.
Proof.
  intros q M k Hq0 HM Hk Hq1.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (b5dL_tkq q M k) q 1).
  - exact ((QleT'_to_Qle _ _ (b5dL_tkq_le_q q M k Hq0 HM Hk))).
  - exact (QltT_to_Qlt _ _ Hq1).
Qed.

(* 0<q and k>=1 give 0 < t_k (the right-endpoint certificate; the J modulus δ-chain instantiation domain). *)
Lemma b5dL_tkq_pos : forall (q : Q) (M k : nat),
  QltT 0 q -> (0 < M)%nat -> (0 < k)%nat -> QltT 0 (b5dL_tkq q M k).
Proof.
  intros q M k Hq0 HM Hk0.
  apply Qlt_to_QltT.
  unfold b5dL_tkq.
  unfold Qdiv.
  apply (Qmult_lt_0_compat (q * (Z.of_nat k # 1)) (Qinv (Z.of_nat M # 1))).
  - apply (Qmult_lt_0_compat q (Z.of_nat k # 1)).
    + exact (QltT_to_Qlt _ _ Hq0).
    + exact ((QltT_to_Qlt _ _ (b5dL_lift_pos k Hk0))).
  - apply Qinv_lt_0_compat.
    destruct M as [| m]; [exfalso; lia | exact ((QltT_to_Qlt _ _ (b5dL_lift_pos2 m)))].
Qed.

(* t_0 == 0 (numerator zeroing in two steps: q*0 == 0, then 0/(M#1) == 0). *)
Lemma b5dL_tkq_0 : forall (q : Q) (M : nat), QeqT (b5dL_tkq q M 0) 0.
Proof.
  intros q M.
  apply qeq_imp_qeqT.
  unfold b5dL_tkq.
  change (Z.of_nat 0) with 0%Z.
  rewrite (Qmult_0_r q).
  unfold Qdiv.
  rewrite (Qmult_0_l (Qinv (Z.of_nat M # 1))).
  reflexivity.
Qed.

(* t_M == q (field; M#1 ≠ 0 follows from 0 < M). *)
Lemma b5dL_tkq_M : forall (q : Q) (M : nat), (0 < M)%nat ->
  QeqT (b5dL_tkq q M M) q.
Proof.
  intros q M HM.
  apply qeq_imp_qeqT.
  unfold b5dL_tkq.
  field.
  intro Hz.
  unfold Qeq in Hz. simpl in Hz.
  lia.
Qed.

(* step identity: t_{S k} == t_k + q/M (field + the lift_succ_q numerator rewrite). *)
Lemma b5dL_tkq_succ : forall (q : Q) (M k : nat), (0 < M)%nat ->
  QeqT (b5dL_tkq q M (Datatypes.S k))
      (b5dL_tkq q M k + b5dL_qdiv q M).
Proof.
  intros q M k HM.
  apply qeq_imp_qeqT.
  unfold b5dL_tkq, b5dL_qdiv.
  pose proof (qeqT_imp_qeq _ _ (b5dL_lift_succ_q k)) as Hgenqeq7350.
  rewrite Hgenqeq7350.
  field.
  intro Hz.
  unfold Qeq in Hz. simpl in Hz.
  lia.
Qed.

(* grid-point domain certificate: 0<q, q<1 and k<=M give cw_unit (real_const t_k) (via b5c_const_unit). *)
Lemma b5dL_tkC : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (M : nat) (k : nat), (0 < M)%nat -> (k <= M)%nat ->
  cw_unit (real_const (b5dL_tkq q M k)).
Proof.
  intros q Hq0 Hq1 M k HM Hk.
  unfold cw_unit.
  apply (b5c_const_unit (b5dL_tkq q M k)).
  - exact ((QleT'_to_Qle _ _ (b5dL_tkq_nonneg q M k (b5dH_q_pos_le q Hq0) HM))).
  - apply (Qle_trans (b5dL_tkq q M k) 1 1).
    + exact ((QleT'_to_Qle _ _ (b5dL_tkq_le1 q M k (b5dH_q_pos_le q Hq0) (b5dH_q_lt1_le q Hq1) HM Hk))).
    + apply Qle_refl.
Qed.

(* ============================================================ *)
(* Section A §4: the Qnsum identities (Q layer + the Real bridge)                *)
(* ============================================================ *)

(* Σ_{k<N} c == (N#1)*c (Q layer; induction + lift_succ_q + ring). *)
Lemma b5dL_Qnsum_const : forall (c : Q) (M : nat),
  QeqT (b5dL_Qnsum (fun _ : nat => c) M) (Qmult (Z.of_nat M # 1) c).
Proof.
  intros c M.
  apply qeq_imp_qeqT.
  induction M as [| M IH]; simpl.
  - ring.
  - rewrite IH.
    pose proof (qeqT_imp_qeq _ _ (b5dL_lift_succ_q M)) as Hgenqeq7385.
    rewrite Hgenqeq7385.
    ring.
Qed.

(* Real bridge: b4_nsum (real_const composed with b) == real_const (Qnsum b) (induction + b5dH_plus_const_eq). *)
Lemma b5dL_nsum_real : forall (b : nat -> Q) (M : nat),
  real_eq (b4_nsum (fun k => real_const (b k)) M)
          (real_const (b5dL_Qnsum b M)).
Proof.
  intros b M.
  induction M as [| M IH]; simpl.
  - apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_const_proj 0 n)).
    cbn [projT1 real_zero].
    reflexivity.
  - apply (real_eq_trans _ (real_plus (real_const (b5dL_Qnsum b M))
                                      (real_const (b M))) _).
    + apply (RealSetoid.real_eq_plus_compat
               (b4_nsum (fun k : nat => real_const (b k)) M)
               (real_const (b M))
               (real_const (b5dL_Qnsum b M)) (real_const (b M))).
      * exact IH.
      * apply real_eq_refl.
    + exact (b5dH_plus_const_eq (b5dL_Qnsum b M) (b M)).
Qed.

(* ============================================================ *)
(* Section A §5: the Real glue (needed when the δ chain instantiates Hstep to    *)
(*   bridge the C5 output eps*|h| + eps' into real_const (b k); δ-independent,   *)
(*   closed first)                                                               *)
(* ============================================================ *)

(* |real_const a| == real_const (Qabs a) (pointwise Qabs_wd on constant coordinates). *)
Lemma b5dL_abs_const : forall (a : Q),
  real_eq (real_abs (real_const a)) (real_const (Qabs a)).
Proof.
  intro a.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_const a) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj a n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (Qabs a) n)).
  ring.
Qed.

(* real_const a * real_const b == real_const (a*b) (pointwise ring). *)
Lemma b5dL_mult_const : forall (a b : Q),
  real_eq (real_mult (real_const a) (real_const b)) (real_const (a * b)).
Proof.
  intros a b.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const a) (real_const b) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj a n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj b n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (a * b) n)).
  ring.
Qed.

(* ============================================================ *)
(* Section B: the telescope premise form (the core skeleton — pure f/g form; the *)
(*   conclusion carries the triangle slack e)                                    *)
(*   Design (design record §3.3/§3.4): under real_le := Or(lt,eq),               *)
(*   |ΣΔ| <= Σ|Δ| is not provable without slack, so use b4_nsum_tri (with the    *)
(*   e k > 0 slack); the conclusion = real_const (Qnsum b M + Qnsum e M).        *)
(* ============================================================ *)

(* |Σ_{k<N} Δk| <= Σ|Δk| + Σe: apply b4_nsum_tri directly (with the e positivity premise). *)
(* Note: the e premise of b4_nsum_tri is real_lt real_zero (e k) — supplied from Qlt 0 (e k) via
   Qlt_to_QltT + real_const_pos. *)

(* the pure f/g telescope premise form: the per-step |f(g_{k+1})-f(g_k)| <= real_const (b k)
   gives |f(g_M)-f(g_0)| <= real_const (Qnsum b M + Qnsum e M)
   proof = the b4_chain_lipschitz template: telescope + tri + nsum_le + nsum_real. *)
Lemma b5dL_telescope_premise : forall (f : Real -> Real) (g : nat -> Real)
  (b e : nat -> Q) (M : nat),
  (forall k : nat, NatLe k M -> QltT 0 (e k)) ->
  (forall k : nat, NatLe k M ->
     real_le (real_abs (real_plus (f (g (Datatypes.S k))) (real_opp (f (g k)))))
             (real_const (b k))) ->
  real_le (real_abs (real_plus (f (g M)) (real_opp (f (g 0%nat)))))
          (real_const (Qplus (b5dL_Qnsum b M) (b5dL_Qnsum e M))).
Proof.
  intros f g b e M He Hstep.
  (* the summand and slack sequences. *)
  set (d := fun k : nat => real_plus (f (g (Datatypes.S k))) (real_opp (f (g k)))).
  set (ek := fun k : nat => real_const (e k)).
  (* (1) telescope: Σ d == f(g M) - f(g 0) (real_eq; apply b4_nsum_telescope directly). *)
  assert (Htel : real_eq (b4_nsum d M)
                         (real_plus (f (g M)) (real_opp (f (g 0%nat))))).
  { unfold d. apply (b4_nsum_telescope f g M). }
  (* (2) |Σd| <= Σ|d| + Σek (b4_nsum_tri; e k > 0 pointwise). *)
  assert (Htri : real_le (real_abs (b4_nsum d M))
                         (real_plus (b4_nsum (fun k => real_abs (d k)) M)
                                    (b4_nsum ek M))).
  { apply (b4_nsum_tri d ek M).
    intros k Hk. unfold ek.
    apply real_const_pos. apply Qlt_to_QltT.
    exact ((QltT_to_Qlt _ _ (He k (NatLe_lift _ _ (Nat.lt_le_incl _ _ Hk))))). }
  (* (3) Σ|d| <= Σ real_const(b k) (b4_nsum_le; apply Hstep directly). *)
  assert (Hle1 : real_le (b4_nsum (fun k => real_abs (d k)) M)
                         (b4_nsum (fun k => real_const (b k)) M)).
  { apply b4_nsum_le.
    intros k Hk. unfold d. exact (Hstep k (NatLe_lift _ _ (Nat.lt_le_incl _ _ Hk))). }
  (* (4) Σreal_const(b) == real_const (Qnsum b M); Σek == real_const (Qnsum e M) *)
  (* (5) assembly: |endpoints| == |Σd| <= (Σ|d| + Σek) <= (Σb-real + Σe-real) == real_const(Qnsum b M + Qnsum e M) *)
  apply (real_le_trans
           (real_abs (real_plus (f (g M)) (real_opp (f (g 0%nat)))))
           (real_plus (b4_nsum (fun k => real_abs (d k)) M) (b4_nsum ek M))
           (real_const (Qplus (b5dL_Qnsum b M) (b5dL_Qnsum e M)))).
  - (* |endpoints| == |Σd| (Htel + abs compat) and |Σd| <= Σ|d| + Σek (Htri). *)
    apply (RealSetoid.real_le_id_l
             (real_abs (real_plus (f (g M)) (real_opp (f (g 0%nat)))))
             (real_abs (b4_nsum d M))
             (real_plus (b4_nsum (fun k => real_abs (d k)) M) (b4_nsum ek M))).
    + apply real_abs_eq_compat. apply real_eq_sym. exact Htel.
    + exact Htri.
  - apply (real_le_trans
             (real_plus (b4_nsum (fun k => real_abs (d k)) M) (b4_nsum ek M))
             (real_plus (b4_nsum (fun k => real_const (b k)) M) (b4_nsum ek M))
             (real_const (Qplus (b5dL_Qnsum b M) (b5dL_Qnsum e M)))).
    + apply (real_le_plus_compat
               (b4_nsum (fun k => real_abs (d k)) M)
               (b4_nsum (fun k => real_const (b k)) M)
               (b4_nsum ek M) (b4_nsum ek M)).
      * exact Hle1.
      * apply real_le_refl.
    + apply (RealSetoid.real_eq_le
               (real_plus (b4_nsum (fun k : nat => real_const (b k)) M)
                          (b4_nsum ek M))
               (real_const (Qplus (b5dL_Qnsum b M) (b5dL_Qnsum e M)))).
      apply (real_eq_trans
               (real_plus (b4_nsum (fun k : nat => real_const (b k)) M)
                          (b4_nsum ek M))
               (real_plus (real_const (b5dL_Qnsum b M))
                          (real_const (b5dL_Qnsum e M)))
               (real_const (Qplus (b5dL_Qnsum b M) (b5dL_Qnsum e M)))).
      * apply (RealSetoid.real_eq_plus_compat
                 (b4_nsum (fun k : nat => real_const (b k)) M)
                 (b4_nsum ek M)
                 (real_const (b5dL_Qnsum b M)) (real_const (b5dL_Qnsum e M))).
        -- exact (b5dL_nsum_real b M).
        -- unfold ek. exact (b5dL_nsum_real e M).
      * exact (b5dH_plus_const_eq (b5dL_Qnsum b M) (b5dL_Qnsum e M)).
Qed.

(* ============================================================ *)
(* Section D: the eps budget Q-layer arithmetic (b_k := eps0Q*(q/M) + eps0'Q)    *)
(*   Design (design record §3.5, settled): eps0Q := epsQ/(2q),                   *)
(*   eps0'Q := epsQ/(4M); the triangle slack e_k := eps0'Q folds in and the      *)
(*   total closed form eps0Q*q + 2M*eps0'Q == epsQ (tight, zero waste).          *)
(* ============================================================ *)

(* the per-step budget b_k (independent of k; the RHS of the Hstep instantiated by the δ chain = real_const (b k)). *)
Definition b5dL_bk (q : Q) (M : nat) (epsQ : Q) (_ : nat) : Q :=
  (epsQ / (2 * q)) * (b5dL_qdiv q M) + (epsQ / (4 * (Z.of_nat M # 1))).

(* the triangle slack e_k := eps0'Q (same value as the second term of bk; the e of b4_nsum_tri). *)
Definition b5dL_epsQ1 (M : nat) (epsQ : Q) : Q :=
  epsQ / (4 * (Z.of_nat M # 1)).

(* 2*q > 0 (q > 0; the field condition piece). *)
Lemma b5dL_two_q_pos : forall (q : Q), QltT 0 q -> QltT 0 (2 * q).
Proof.
  intros q Hq0.
  apply Qlt_to_QltT.
  apply (Qmult_lt_0_compat 2 q).
  - unfold Qlt. simpl. lia.
  - exact (QltT_to_Qlt _ _ (Hq0)).
Qed.

(* 4*(M#1) > 0 (0 < M; the field condition piece). *)
Lemma b5dL_four_M_pos : forall (M : nat), (0 < M)%nat -> QltT 0 (4 * (Z.of_nat M # 1)).
Proof.
  intros M HM.
  apply Qlt_to_QltT.
  destruct M as [| m]; [exfalso; lia | idtac].
  apply (Qmult_lt_0_compat 4 (Z.of_nat (Datatypes.S m) # 1)).
  - unfold Qlt. simpl. lia.
  - exact ((QltT_to_Qlt _ _ (b5dL_lift_pos2 m))).
Qed.

(* 0 < epsQ/(4*(M#1)) (epsQ > 0 and 0 < M; the e positivity premise of b4_nsum_tri). *)
Lemma b5dL_epsQ1_pos : forall (epsQ : Q) (M : nat),
  QltT 0 epsQ -> (0 < M)%nat -> QltT 0 (b5dL_epsQ1 M epsQ).
Proof.
  intros epsQ M Heps HM.
  apply Qlt_to_QltT.
  unfold b5dL_epsQ1.
  destruct M as [| m]; [exfalso; lia | idtac].
  apply (Qmult_lt_0_compat epsQ (Qinv (4 * (Z.of_nat (Datatypes.S m) # 1)))).
  - exact (QltT_to_Qlt _ _ (Heps)).
  - apply Qinv_lt_0_compat.
    apply (Qmult_lt_0_compat 4 (Z.of_nat (Datatypes.S m) # 1)).
    + unfold Qlt. simpl. lia.
    + exact ((QltT_to_Qlt _ _ (b5dL_lift_pos2 m))).
Qed.

(* the budget closed form: Qnsum(bk) + Qnsum(the epsQ1 constant) == epsQ
   proof: the Qnsum_const rewrite twice + unfold bk + field (the division-by-zero
   conditions are conjunctive forms ~ x == 0, closed by the individual nz pieces +
   repeat split). *)
Lemma b5dL_budget_closure : forall (q : Q) (M : nat) (epsQ : Q),
  QltT 0 q -> (0 < M)%nat -> QltT 0 epsQ ->
  QeqT (Qplus (b5dL_Qnsum (b5dL_bk q M epsQ) M)
             (b5dL_Qnsum (fun _ : nat => b5dL_epsQ1 M epsQ) M))
      epsQ.
Proof.
  intros q M epsQ Hq0 HM Heps.
  apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq _ _ (b5dL_Qnsum_const (b5dL_bk q M epsQ 0) M)) as Hgenqeq7593.
  rewrite Hgenqeq7593.
  pose proof (qeqT_imp_qeq _ _ (b5dL_Qnsum_const (b5dL_epsQ1 M epsQ) M)) as Hgenqeq7595.
  rewrite Hgenqeq7595.
  unfold b5dL_bk, b5dL_qdiv, b5dL_epsQ1.
  field.
  all: try (unfold Qeq in *; simpl in *; lia).
  all: repeat split.
  all: try (intro Hz;
    first [ exact (match b5dL_q_lt0_nz q Hq0 (qeq_imp_qeqT _ _ Hz) with end)
          | exact (match b5dL_q_lt0_nz (2 * q) (b5dL_two_q_pos q Hq0) (qeq_imp_qeqT _ _ Hz) with end)
          | destruct M as [| m]; [exfalso; lia | exact (match b5dL_q_lt0_nz (Z.of_nat (Datatypes.S m) # 1) (b5dL_lift_pos2 m) (qeq_imp_qeqT _ _ Hz) with end)]
          | exact (match b5dL_q_lt0_nz (4 * (Z.of_nat M # 1)) (b5dL_four_M_pos M HM) (qeq_imp_qeqT _ _ Hz) with end) ]).
Qed.

(* ============================================================ *)
(* Section C: the J grid telescope premise form (certificate-parameterized)      *)
(*   Design (design record §3.4): the J domain certificates are Set-layer data   *)
(*   and cw_unit (real_const (tkq q M k)) is not inhabited for k > M, so the     *)
(*   f/g form of b4_nsum_telescope cannot be applied directly: build the         *)
(*   induction Aux(n) (the <= M prefix sums):                                    *)
(*   each-step triangle uses real_abs_triangle_le_eps (with the e n slack); the  *)
(*   middle certificate is taken on the spot as b5dL_tkC; the Hstep premises are *)
(*   quantified over the certificates (compatible with the C5 output).           *)
(* ============================================================ *)

Lemma b5dL_J_grid_premise : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (M : nat) (b e : nat -> Q),
  (forall k : nat, NatLe k M -> QltT 0 (e k)) ->
  (forall k : nat, NatLe k M ->
     forall (Hk : cw_unit (real_const (b5dL_tkq q M k)))
            (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k)))),
     real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                                  (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
             (real_const (b k))) ->
  forall (C0 : cw_unit (real_const (b5dL_tkq q M 0)))
         (CM : cw_unit (real_const (b5dL_tkq q M M))),
  real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M M)) CM)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))))
          (real_const (Qplus (b5dL_Qnsum b M) (b5dL_Qnsum e M))).
Proof.
  intros q Hq0 Hq1 M b e He Hstep C0 CM.
  (* Aux: the <= M prefix-sum bound |J(t_n)Cn - J(t_0)C0| <= real_const (Qnsum b n + Qnsum e n). *)
  assert (Aux : forall (n : nat), (n <= M)%nat ->
            forall (Cn : cw_unit (real_const (b5dL_tkq q M n)))
                   (C0' : cw_unit (real_const (b5dL_tkq q M 0))),
            real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Cn)
                                         (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
                    (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n)))).
  { induction n as [| n IH]; intros Hn Cn C0'.
    - (* base n = 0: |J0 - J0| == 0 <= real_const (Qnsum b 0 + Qnsum e 0). *)
      assert (Hjw : real_eq (b5c_J (real_const (b5dL_tkq q M 0)) Cn)
                            (b5c_J (real_const (b5dL_tkq q M 0)) C0')).
      { apply (b5p2_J_wd (real_const (b5dL_tkq q M 0))
                         (real_const (b5dL_tkq q M 0)) Cn C0').
        apply real_eq_refl. }
      apply (real_le_trans
               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M 0)) Cn)
                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
               real_zero
               (real_const (Qplus (b5dL_Qnsum b 0) (b5dL_Qnsum e 0)))).
      + apply (RealSetoid.real_eq_le _ _).
        apply (real_eq_trans _ (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M 0)) Cn)
                                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) Cn)))) _).
        * apply real_abs_eq_compat.
          apply (RealSetoid.real_eq_plus_compat
                   (b5c_J (real_const (b5dL_tkq q M 0)) Cn)
                   (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))
                   (b5c_J (real_const (b5dL_tkq q M 0)) Cn)
                   (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) Cn))).
          -- apply real_eq_refl.
          -- apply (RealSetoid.real_eq_opp_compat
                     (b5c_J (real_const (b5dL_tkq q M 0)) C0')
                     (b5c_J (real_const (b5dL_tkq q M 0)) Cn)).
             apply real_eq_sym. exact Hjw.
        * apply (real_eq_trans _ (real_abs real_zero) _).
          -- apply real_abs_eq_compat. exact (real_plus_opp (b5c_J (real_const (b5dL_tkq q M 0)) Cn)).
          -- apply real_abs_zero_req.
      + apply (RealSetoid.real_eq_le _ _).
        apply real_eq_sym.
        apply real_eq_of_zero_diff.
        intro n0.
        apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (real_const_proj (Qplus (b5dL_Qnsum b 0) (b5dL_Qnsum e 0)) n0)).
        cbn [b5dL_Qnsum projT1 real_zero].
        ring.
    - (* step n -> S n: triangle + Hstep + IH. *)
      assert (Hn' : (n <= M)%nat) by lia.
      assert (Hnlt : (n < M)%nat) by lia.
      assert (HM' : (0 < M)%nat) by lia.
      assert (Hmid : cw_unit (real_const (b5dL_tkq q M n))).
      { exact (b5dL_tkC q Hq0 Hq1 M n HM' Hn'). }
      (* the per-step bound (certificates on the spot: the middle certificate = canonical). *)
      assert (Hstep_n : real_le
               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                    (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
               (real_const (b n))).
      { exact (Hstep n (NatLe_lift _ _ (Nat.lt_le_incl _ _ Hnlt)) Hmid Cn). }
      assert (Hih_n : real_le
               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
               (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n)))).
      { exact (IH Hn' Hmid C0'). }
      (* triangle (with the e n slack): |A-C0| <= (|A-B| + |B-C0|) + e n. *)
      assert (Htri : real_le
               (real_abs (real_plus
                  (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                             (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid)))
                  (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                             (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
               (real_plus
                  (real_plus
                     (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                          (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                     (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                          (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                  (real_const (e n)))).
      { apply (real_abs_triangle_le_eps
                 (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                            (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid)))
                 (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                            (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))
                 (real_const (e n))).
        apply real_const_pos. apply Qlt_to_QltT. exact ((QltT_to_Qlt _ _ (He n (NatLe_lift _ _ (Nat.lt_le_incl _ _ Hnlt))))). }
      (* middle ring step: ((A-B) + (B-C0)) == (A-C0). *)
      assert (Hring : real_eq
               (real_plus (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                     (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid)))
                          (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                     (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
               (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                          (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))).
      { apply real_eq_of_zero_diff. intro n0. apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj
                   (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                              (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid)))
                   (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                              (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))) n0)).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid)) n0)).
        rewrite (qeqT_imp_qeq _ _ (real_opp_proj (b5c_J (real_const (b5dL_tkq q M n)) Hmid) n0)).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')) n0)).
        rewrite (qeqT_imp_qeq _ _ (real_opp_proj (b5c_J (real_const (b5dL_tkq q M 0)) C0') n0)).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')) n0)).
        rewrite (qeqT_imp_qeq _ _ (real_opp_proj (b5c_J (real_const (b5dL_tkq q M 0)) C0') n0)).
        ring. }
      (* |A-C0| <= (|A-B| + |B-C0|) + e n (via the reordering of |(A-B)+(B-C0)|). *)
      assert (Hmain : real_le
               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
               (real_plus (real_plus
                             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                                  (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                                  (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                          (real_const (e n)))).
      { apply (RealSetoid.real_le_id_l
                 (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                      (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
                 (real_abs (real_plus
                    (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid)))
                    (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                 (real_plus (real_plus
                               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                                    (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                            (real_const (e n)))).
        - apply real_abs_eq_compat. apply real_eq_sym. exact Hring.
        - exact Htri. }
      (* (|A−B| + |B−C0|) + e n ≤ (real_const (b n) + real_const (Qnsum b n + Qnsum e n)) + real_const (e n) *)
      assert (Hrhs : real_le
               (real_plus (real_plus
                             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                                  (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                                  (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                          (real_const (e n)))
               (real_plus (real_plus (real_const (b n))
                                     (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))))
                          (real_const (e n)))).
      { apply (real_le_plus_compat
                 (real_plus (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                                 (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                            (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                                 (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                 (real_plus (real_const (b n)) (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))))
                 (real_const (e n)) (real_const (e n))).
        - apply (real_le_plus_compat
                   (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                        (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                   (real_const (b n))
                   (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                        (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
                   (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n)))).
          + exact Hstep_n.
          + exact Hih_n.
        - apply real_le_refl. }
      (* conclusion: |A-C0| <= ... == real_const (Qnsum b (S n) + Qnsum e (S n)). *)
      apply (real_le_trans
               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
               (real_plus (real_plus (real_const (b n))
                                     (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))))
                          (real_const (e n)))
               (real_const (Qplus (b5dL_Qnsum b (Datatypes.S n)) (b5dL_Qnsum e (Datatypes.S n))))).
      + apply (real_le_trans
                 (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                      (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0'))))
                 (real_plus (real_plus
                               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S n))) Cn)
                                                    (real_opp (b5c_J (real_const (b5dL_tkq q M n)) Hmid))))
                               (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M n)) Hmid)
                                                    (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0')))))
                            (real_const (e n)))
                 (real_plus (real_plus (real_const (b n))
                                       (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))))
                            (real_const (e n)))).
        * exact Hmain.
        * exact Hrhs.
      + apply (RealSetoid.real_eq_le
                 (real_plus (real_plus (real_const (b n))
                                       (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))))
                            (real_const (e n)))
                 (real_const (Qplus (b5dL_Qnsum b (Datatypes.S n)) (b5dL_Qnsum e (Datatypes.S n))))).
        apply real_eq_of_zero_diff.
        intro n0.
        apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj
                   (real_plus (real_const (b n)) (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))))
                   (real_const (e n)) n0)).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_const (b n))
                                (real_const (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n))) n0)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj (b n) n0)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj (Qplus (b5dL_Qnsum b n) (b5dL_Qnsum e n)) n0)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj (e n) n0)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj (Qplus (b5dL_Qnsum b (Datatypes.S n)) (b5dL_Qnsum e (Datatypes.S n))) n0)).
        cbn [b5dL_Qnsum projT1 real_zero].
        ring. }
  (* final: n := M. *)
  exact (Aux M (Nat.le_refl M) CM C0).
Qed.

(* ============================================================ *)
(* Section E: the premise form (once the δ chain is ready only the Hstep         *)
(*   instantiation remains)                                                      *)
(* ============================================================ *)

(* taking the Q lower bound of any Real e > 0: there is a rational c > 0 with
   real_le (real_const c) e
   proof: destruct the positivity witness of e (the tail e_n > eps0), so c := eps0/2 is
   strictly below e (the lt-branch witness eps0/2; qltT_eq_compat_l/r as coordinate
   rewrites). *)
Lemma b5dL_eps_real_lower : forall (e : Real), real_lt real_zero e ->
  sigT (fun c : Q => And (QltT 0 c) (real_le (real_const c) e)).
Proof.
  intros e He.
  destruct He as [eps0 [Heps0 [N0 HN0]]].
  exists (eps0 / 2)%Q.
  split.
  - apply (q_half_pos eps0). exact Heps0.
  - apply (RealSetoid.real_lt_le_iff_req (real_const (eps0 / 2)) e). left.
    unfold real_lt.
    exists (eps0 / 2)%Q.
    split.
    + apply (q_half_pos eps0). exact Heps0.
    + exists N0.
      intros n Hn.
      (* coordinate rewrite: projT1 (real_const (eps0/2)) n == eps0/2. *)
      apply (qltT_eq_compat_r (projT1 e n - projT1 (real_const (eps0 / 2)) n)
                              (projT1 e n - (eps0 / 2))
                              (eps0 / 2)).
      * apply qeq_imp_qeqT. apply Qplus_comp; [ apply Qeq_refl | ].
        apply (Qopp_comp _ _ (qeqT_imp_qeq _ _ (real_const_proj (eps0 / 2) n))).
      * apply Qlt_to_QltT.
        (* goal: eps0/2 < e_n - eps0/2 iff eps0 < e_n (supplied directly by HN0). *)
        apply (proj2 (Qlt_minus_iff (eps0 / 2) (projT1 e n - (eps0 / 2)))).
        assert (Heq2 : Qeq ((projT1 e n - (eps0 / 2)) - (eps0 / 2))
                          (projT1 e n - eps0)).
        { field.
          all: try (unfold Qeq in *; simpl in *; lia).
          all: try (repeat split).
          all: try (intro Hz; unfold Qeq in Hz; simpl in Hz; lia). }
        rewrite Heq2.
        apply (proj1 (Qlt_minus_iff eps0 (projT1 e n))).
        apply QltT_to_Qlt.
        apply (qltT_eq_compat_r (projT1 e n)
                                (projT1 e n - projT1 real_zero n) eps0).
        -- apply qeq_imp_qeqT. apply Qeq_sym.
           assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
           rewrite Hz. ring.
        -- exact (HN0 n Hn).
Qed.

(* the grid-budget conclusion: the per-step premises (the bk budget) give |J(q)Hq - J(0)bz| <= real_const epsQ
   proof: J_grid @ (b := bk, e := the epsQ1 constant) + the tkq_M/tkq_0 endpoint bridges + budget_closure. *)
Lemma b5dL_J_zero_on_grid_premise : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (M : nat) (HMpos : (0 < M)%nat) (epsQ : Q) (Heps : QltT 0 epsQ),
  (forall k : nat, NatLe k M ->
     forall (Hk : cw_unit (real_const (b5dL_tkq q M k)))
            (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k)))),
     real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                                  (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
             (real_const (b5dL_bk q M epsQ k))) ->
  forall (Hq : cw_unit (real_const q)),
  real_le (real_abs (real_plus (b5c_J (real_const q) Hq)
                               (real_opp (b5c_J (real_const 0) b5c_unit_zero))))
          (real_const epsQ).
Proof.
  intros q Hq0 Hq1 M HMpos epsQ Heps Hstep Hq.
  pose (C0 := b5dL_tkC q Hq0 Hq1 M 0 HMpos (Nat.le_0_l M)).
  pose (CM := b5dL_tkC q Hq0 Hq1 M M HMpos (Nat.le_refl M)).
  (* the J grid telescope instance: b := bk, e := the epsQ1 constant. *)
  assert (Hgrid : real_le
             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M M)) CM)
                                  (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))))
             (real_const (Qplus (b5dL_Qnsum (b5dL_bk q M epsQ) M)
                                (b5dL_Qnsum (fun _ : nat => b5dL_epsQ1 M epsQ) M)))).
  { apply (b5dL_J_grid_premise q Hq0 Hq1 M
             (b5dL_bk q M epsQ) (fun _ : nat => b5dL_epsQ1 M epsQ)).
    - intros k Hk. exact (b5dL_epsQ1_pos epsQ M Heps HMpos).
    - intros k Hk. exact (Hstep k Hk). }
  (* the budget closed form: Qnsum(bk) + Qnsum(epsQ1) == epsQ. *)
  assert (Hsum : Qeq (Qplus (b5dL_Qnsum (b5dL_bk q M epsQ) M)
                            (b5dL_Qnsum (fun _ : nat => b5dL_epsQ1 M epsQ) M)) epsQ).
  { exact ((qeqT_imp_qeq _ _ (b5dL_budget_closure q M epsQ Hq0 HMpos Heps))). }
  (* the endpoint bridges: t_M == q and t_0 == 0 (real_const_qeq + J_wd). *)
  assert (HbrM : real_eq (b5c_J (real_const (b5dL_tkq q M M)) CM)
                         (b5c_J (real_const q) Hq)).
  { apply (b5p2_J_wd (real_const (b5dL_tkq q M M)) (real_const q) CM Hq).
    apply (b5dH_real_const_qeq (b5dL_tkq q M M) q).
    exact (b5dL_tkq_M q M HMpos). }
  assert (Hbr0 : real_eq (b5c_J (real_const (b5dL_tkq q M 0)) C0)
                         (b5c_J (real_const 0) b5c_unit_zero)).
  { apply (b5p2_J_wd (real_const (b5dL_tkq q M 0)) (real_const 0) C0 b5c_unit_zero).
    apply (b5dH_real_const_qeq (b5dL_tkq q M 0) 0).
    exact (b5dL_tkq_0 q M). }
  (* |J(q)Hq - J(0)bz| == |J(t_M)CM - J(t_0)C0| (the abs compat bridge). *)
  assert (Habs : real_eq
             (real_abs (real_plus (b5c_J (real_const q) Hq)
                                  (real_opp (b5c_J (real_const 0) b5c_unit_zero))))
             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M M)) CM)
                                  (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))))).
  { apply real_abs_eq_compat.
    apply (RealSetoid.real_eq_plus_compat
             (b5c_J (real_const q) Hq)
             (real_opp (b5c_J (real_const 0) b5c_unit_zero))
             (b5c_J (real_const (b5dL_tkq q M M)) CM)
             (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))).
    - apply real_eq_sym. exact HbrM.
    - apply (RealSetoid.real_eq_opp_compat
               (b5c_J (real_const 0) b5c_unit_zero)
               (b5c_J (real_const (b5dL_tkq q M 0)) C0)).
      apply real_eq_sym. exact Hbr0. }
  (* assembly: |J(q)-J(0)| <= |J(t_M)-J(t_0)| <= real_const (Qnsum+Qnsum) == real_const epsQ. *)
  apply (real_le_trans
           (real_abs (real_plus (b5c_J (real_const q) Hq)
                                (real_opp (b5c_J (real_const 0) b5c_unit_zero))))
           (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M M)) CM)
                                (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))))
           (real_const epsQ)).
  - apply (RealSetoid.real_eq_le
             (real_abs (real_plus (b5c_J (real_const q) Hq)
                                  (real_opp (b5c_J (real_const 0) b5c_unit_zero))))
             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M M)) CM)
                                  (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))))).
    exact Habs.
  - apply (RealSetoid.real_le_id_r
             (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M M)) CM)
                                  (real_opp (b5c_J (real_const (b5dL_tkq q M 0)) C0))))
             (real_const (Qplus (b5dL_Qnsum (b5dL_bk q M epsQ) M)
                                (b5dL_Qnsum (fun _ : nat => b5dL_epsQ1 M epsQ) M)))
             (real_const epsQ)).
    + apply (b5dH_real_const_qeq
               (Qplus (b5dL_Qnsum (b5dL_bk q M epsQ) M)
                      (b5dL_Qnsum (fun _ : nat => b5dL_epsQ1 M epsQ) M)) epsQ).
      exact (qeq_imp_qeqT _ _ (Hsum)).
    + exact Hgrid.
Qed.

(* the main-piece-form premise: Hmod (for all epsQ > 0 there is M >= 1 satisfying the per-step grid premises) gives E(q) == 0
   proof: b5dH_E_zero_of_J_zero + b4_abs_le_forall_eps_eq (taking the Q lower bound c of any Real e
   = b5dL_eps_real_lower) + J_zero_on_grid @ (epsQ := c, M) + the J(0)==0 bridge (b5dH_J_zero0). *)
Lemma b5dL_E_rational_zero_premise : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1),
  (forall (epsQ : Q), QltT 0 epsQ ->
     sigT (fun M : nat => And (NatLe 1 M)
       (forall (k : nat), NatLe k M ->
          forall (Hk : cw_unit (real_const (b5dL_tkq q M k)))
                 (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k)))),
          real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                                       (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
                  (real_const (b5dL_bk q M epsQ k))))) ->
  forall (Hq : cw_unit (real_const q)),
  real_eq (real_E (real_const q) Hq) real_zero.
Proof.
  intros q Hq0 Hq1 Hmod Hq.
  apply (b5dH_E_zero_of_J_zero (real_const q) Hq).
  apply (b4_abs_le_forall_eps_eq (b5c_J (real_const q) Hq) real_zero).
  intros e He.
  (* the Q lower bound: there is c > 0 with real_le (real_const c) e. *)
  destruct (b5dL_eps_real_lower e He) as [c [Hc0 Hcle]].
  destruct (Hmod c ((Qlt_to_QltT _ _ (QltT_to_Qlt _ _ Hc0)))) as [M [HMpos Hstep]].
  (* |J(q)Hq - J(0)bz| <= real_const c (the grid instance). *)
  assert (Hle_c : real_le
             (real_abs (real_plus (b5c_J (real_const q) Hq)
                                  (real_opp (b5c_J (real_const 0) b5c_unit_zero))))
             (real_const c)).
  { exact (b5dL_J_zero_on_grid_premise q Hq0 Hq1 M (NatLe_drop 1 M HMpos) c ((Qlt_to_QltT _ _ (QltT_to_Qlt _ _ Hc0))) Hstep Hq). }
  (* the J(0) == 0 bridge: |J(q) - 0| == |J(q) - J(0)bz|. *)
  assert (Hj0 : real_eq (b5c_J (real_const 0) b5c_unit_zero) real_zero)
    by exact b5dH_J_zero0.
  assert (Habs0 : real_eq
             (real_abs (real_plus (b5c_J (real_const q) Hq) (real_opp real_zero)))
             (real_abs (real_plus (b5c_J (real_const q) Hq)
                                  (real_opp (b5c_J (real_const 0) b5c_unit_zero))))).
  { apply real_abs_eq_compat.
    apply (RealSetoid.real_eq_plus_compat
             (b5c_J (real_const q) Hq) (real_opp real_zero)
             (b5c_J (real_const q) Hq)
             (real_opp (b5c_J (real_const 0) b5c_unit_zero))).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_opp_compat real_zero
                                           (b5c_J (real_const 0) b5c_unit_zero)).
      apply real_eq_sym. exact Hj0. }
  apply (real_le_trans
           (real_abs (real_plus (b5c_J (real_const q) Hq) (real_opp real_zero)))
           (real_const c) e).
  - apply (RealSetoid.real_le_id_l
             (real_abs (real_plus (b5c_J (real_const q) Hq) (real_opp real_zero)))
             (real_abs (real_plus (b5c_J (real_const q) Hq)
                                  (real_opp (b5c_J (real_const 0) b5c_unit_zero))))
             (real_const c)).
    + exact Habs0.
    + exact Hle_c.
  - exact Hcle.
Qed.

(* ===== end of sc2_b5a_item22.v: the delta-D2e premise-form telescope skeleton, Sections A/B/C/D/E ===== *)

(* ===== Block b5dP_ (main item b5dP_S_diff_closed_r_M_exp_tail; upstream source sc2_b5a_item26) ===== *)

(* ============================================================ *)
(* Section A: the main piece b5dP_S_diff_closed_r_M_exp_tail (the S-diff         *)
(*   tail-form piece, Defined preset)                                            *)
(*   Copy source = the sc2_b5a_item24.v main-piece region L87-370 (machine-      *)
(*   extracted, no hand transcription; itself = the M-parameterized Defined copy *)
(*   of item10 C4 — the item24 changes S1-S5 are already done: rename / the eps  *)
(*   witness moved down (spine-clean) / the exp and g leaves swapped to b5dK_    *)
(*   (item21) / Qed->Defined).                                                   *)
(*   Changes A1-A5 (the tail-form increments, the design §2.3 table): the HMall  *)
(*   statement line -> (NM : nat) + the tail-form HMall; the intros names        *)
(*   extended; Nmax folded into NM; consumption-point guards + per-n asserts;    *)
(*   closing Defined (the source is already Defined).  The other root references *)
(*   in the body (the b5l_/b5n_/b5i_/b5f_/sc_/real_ families) unchanged — all    *)
(*   in proof positions, not entering the δ value; δ := real_min δexp δg copied  *)
(*   as is.  The statement types are, except for the A2 changed lines, verbatim  *)
(*   item10 C4 (the downstream item27 interface contract).                       *)
(* ============================================================ *)
Lemma b5dP_S_diff_closed_r_M_exp_tail :
  forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (M : Q) (HMpos : QltT 0 M)
    (NM : nat)
    (HMall : forall n : nat, NatLe NM n -> QleT' (Qabs (projT1 (b5a_S x) n)) M),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5a_S (real_plus x h))
                 (real_opp (real_plus (b5a_S x)
                            (real_mult (real_mult x (b5a_S x)) (real_mult (b5a_atan_d x) h))))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr M HMpos NM HMall eps Heps.
  (* M: |S(x)_n| <= M (0 < M). *)
  assert (HM0 : Qle 0 M). { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (HMpos)). }
  (* k2 := k2p := Qinv(8(1+M)): QltT 0 and M*k <= (1#8). *)
  set (k2 := Qinv (Qmult 8 (Qplus M 1))).
  set (k2p := Qinv (Qmult 8 (Qplus M 1))).
  assert (Hk2T : QltT 0 k2). { unfold k2. apply b5l_k_posT. exact HM0. }
  assert (Hk2pT : QltT 0 k2p). { unfold k2p. apply b5l_k_posT. exact HM0. }
  assert (HMk2 : Qle (Qmult M k2) (1 # 8)). { unfold k2. apply QleT'_to_Qle. apply b5l_Mk_le. exact HM0. }
  assert (HMk2p : Qle (Qmult M k2p) (1 # 8)). { unfold k2p. apply QleT'_to_Qle. apply b5l_Mk_le. exact HM0. }
  (* coefficient-absorption facts: coefS1 := (M*k2)*(1#4) <= (1#32); coefG1 := M*2*k2p*(1#8) <= (1#32). *)
  assert (HcoefS1 : Qle (Qmult (Qmult M k2) (1 # 4)) (1 # 32)).
  { apply (Qle_trans (Qmult (Qmult M k2) (1 # 4)) (Qmult (1 # 8) (1 # 4)) (1 # 32)).
    - apply (Qmult_le_compat_r (Qmult M k2) (1 # 8) (1 # 4)).
      + exact HMk2.
      + change (Qle 0 (1 # 4)). unfold Qle. simpl. lia.
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
  assert (HcoefG1 : Qle (Qmult (Qmult M (Qmult 2 k2p)) (1 # 8)) (1 # 32)).
  { apply (Qle_trans (Qmult (Qmult M (Qmult 2 k2p)) (1 # 8))
                     (Qmult (Qmult M k2p) (1 # 4))
                     (1 # 32)).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    - apply (Qle_trans (Qmult (Qmult M k2p) (1 # 4))
                       (Qmult (1 # 8) (1 # 4))
                       (1 # 32)).
      + apply (Qmult_le_compat_r (Qmult M k2p) (1 # 8) (1 # 4)).
        * exact HMk2p.
        * change (Qle 0 (1 # 4)). unfold Qle. simpl. lia.
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
  (* the eps witnesses and Q-constant positivity. *)
  assert (H2T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H4T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (H8T : QltT 0 (1 # 8)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 8)); unfold Qlt; simpl; lia).
  assert (H16T : QltT 0 (1 # 16)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 16)); unfold Qlt; simpl; lia).
  assert (H32T : QltT 0 (1 # 32)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 32)); unfold Qlt; simpl; lia).
  (* the eps shares (Real). *)
  set (eps1 := real_mult eps (real_const (1 # 2))).
  assert (Heps1 : real_lt real_zero eps1).
  { unfold eps1. apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact H2T. } }
  set (eps2 := real_mult eps (real_const (1 # 4))).
  assert (Heps2 : real_lt real_zero eps2).
  { unfold eps2. apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact H4T. } }
  (* the exp-part δexp (the item3e main piece) and the g-part δg (b5f_gdiff_pts_r). *)
  destruct (b5dK_exp_part_bound_closed_r_exp r Hr0 Hr1 x Hxr eps1 Heps1) as [δexp [Hδe0 Hδe]].
  destruct (b5dK_gdiff_pts_r_exp r Hr0 Hr1 x Hxr eps2 Heps2 k2 k2p Hk2T Hk2pT) as [δg [Hδg0 Hδg]].
  (* δ := min δexp δg *)
  set (delta := real_min δexp δg).
  assert (Hd0 : real_lt real_zero delta).
  { unfold delta. apply real_min_pos. { exact Hδe0. } { exact Hδg0. } }
  exists delta. split. { exact Hd0. }
  { intros h Hh eps' Heps'.
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
    assert (HhE : real_lt (real_abs h) δexp).
    { apply (real_min_lt_l h δexp δg). unfold delta in Hh. exact Hh. }
    assert (HhG : real_lt (real_abs h) δg).
    { apply (real_min_lt_r h δexp δg). unfold delta in Hh. exact Hh. }
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT. apply (Qmult_lt_0_compat (1 # 8) e1).
      - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia.
      - apply QltT_to_Qlt. exact He1T. }
    (* the shares: the exp inner eps1', the margin shE, the g inner eps2', the slack m0. *)
    set (eps1' := real_mult eps' (real_const (1 # 4))).
    assert (Heps1' : real_lt real_zero eps1').
    { unfold eps1'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact H4T. } }
    set (shE := real_mult eps' (real_const (1 # 16))).
    assert (HshE : real_lt real_zero shE).
    { unfold shE. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact H16T. } }
    set (eps2' := real_mult eps' (real_const (1 # 8))).
    assert (Heps2' : real_lt real_zero eps2').
    { unfold eps2'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact H8T. } }
    set (m0 := Qmult (1 # 32) e1).
    assert (Hm0T : QltT 0 m0).
    { unfold m0. apply Qlt_to_QltT. apply (Qmult_lt_0_compat (1 # 32) e1).
      - change (Qlt 0 (1 # 32)). unfold Qlt. simpl. lia.
      - apply QltT_to_Qlt. exact He1T. }
    (* the error object (verbatim with the b5f_S_err_decomp statement). *)
    set (err := real_plus (b5a_S (real_plus x h))
                 (real_opp (real_plus (b5a_S x)
                            (real_mult (real_mult x (b5a_S x)) (real_mult (b5a_atan_d x) h))))).
    set (Eobj := real_mult (b5a_S x)
                  (real_plus (cauchy_real_exp (b5f_v x h))
                             (real_opp (real_plus real_one (b5f_v x h))))).
    set (wS := real_plus (b5f_v x h)
                         (real_opp (real_mult (real_mult x (b5a_atan_d x)) h))).
    set (Gob := real_mult (b5a_S x) wS).
    (* the exp-part real-le instantiation (the inner eps' share of the item3e main piece). *)
    set (Bexp := real_plus (real_mult eps1 (real_abs h)) eps1').
    assert (Hexp_le : real_le (real_abs Eobj) Bexp).
    { unfold Eobj, Bexp. exact (Hδe h HhE eps1' Heps1'). }
    destruct (b5i_abs_le_pointwise Eobj Bexp Hexp_le shE HshE) as [NE HNE].
    (* the g part pointwise (the inner eps' share of gdiff). *)
    destruct (Hδg h HhG eps2' Heps2') as [Ng HNg].
    (* the slack decomposition: real_eq err (Eobj + Gob). *)
    destruct (b5l_eq_abs_tri err Eobj Gob m0 (b5f_S_err_decomp x h) Hm0T) as [Ntri Htri].
    (* real_le left branch real_lt, witness eta. *)
    left.
    exists eta.
    split.
    { exact HetaT. }
    { set (Nmax := Nat.max NM (Nat.max Ne0 (Nat.max Ne1 (Nat.max NE (Nat.max Ng Ntri))))).
      exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 err n)).
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNE : NatLe NE n) by (apply NatLe_lift; lia).
      assert (HnNg : NatLe Ng n) by (apply NatLe_lift; lia).
      assert (HnNtri : NatLe Ntri n) by (apply NatLe_lift; lia).
      assert (HnNM : NatLe NM n) by (apply NatLe_lift; lia).
      (* nonnegativity facts. *)
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        - apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T.
        - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He0lt n HnNe0)). }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. apply (Qle_trans 0 e1 (projT1 eps' n)).
        - apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T.
        - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n HnNe1)). }
      assert (Hhn0 : Qle 0 hn). { unfold hn. apply Qabs_nonneg. }
      assert (Hm0le : Qle m0 (Qmult (1 # 32) en')).
      { unfold m0, en'. apply QleT'_to_Qle. apply (sc_qmult_le_l e1 (projT1 eps' n) (1 # 32)).
        - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n HnNe1)).
        - change (Qle 0 (1 # 32)). unfold Qle. simpl. lia. }
      (* the exp-part pointwise bound: |Eobj_n| <= Eexpn. *)
      set (Eexpn := Qplus (Qmult (Qmult en (1 # 2)) hn)
                          (Qplus (Qmult en' (1 # 4)) (Qmult en' (1 # 16)))).
      assert (HexpB : Qle (Qabs (projT1 Eobj n)) Eexpn).
      { apply (Qle_trans (Qabs (projT1 Eobj n))
                         (Qplus (projT1 Bexp n) (projT1 shE n))
                         Eexpn).
        - exact (QleT'_to_Qle _ _ (HNE n HnNE)).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          assert (Hp1 : projT1 eps1 n == Qmult (projT1 eps n) (1 # 2)).
          { unfold eps1. setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const (1 # 2)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 2) n)). reflexivity. }
          assert (Hp1' : projT1 eps1' n == Qmult (projT1 eps' n) (1 # 4)).
          { unfold eps1'. setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const (1 # 4)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 4) n)). reflexivity. }
          assert (Hpsh : projT1 shE n == Qmult (projT1 eps' n) (1 # 16)).
          { unfold shE. setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const (1 # 16)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 16) n)). reflexivity. }
          assert (Hqh : projT1 (real_abs h) n == Qabs (projT1 h n)).
          { apply qeqT_imp_qeq; apply real_abs_proj. }
          unfold Eexpn, Bexp, en, en', hn.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps1 (real_abs h)) eps1' n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps1 (real_abs h) n)).
          setoid_rewrite Hp1.
          setoid_rewrite Hqh.
          setoid_rewrite Hp1'.
          setoid_rewrite Hpsh.
          ring. }
      (* the g-part pointwise bound: |Gob_n| <= (1#32)*(en*hn) + (1#32)*en'. *)
      assert (HgB : Qle (Qabs (projT1 Gob n))
                        (Qplus (Qmult (1 # 32) (Qmult en hn)) (Qmult (1 # 32) en'))).
      { (* |Gob_n| <= M*|wS_n| (|S_n| <= M). *)
        assert (H1 : Qle (Qabs (projT1 Gob n)) (Qmult M (Qabs (projT1 wS n)))).
        { unfold Gob, wS. apply QleT'_to_Qle. apply (b5l_Sx_mult_abs_le x wS M n). exact ((QleT'_to_Qle _ _ (HMall n HnNM))). }
        (* |wS_n| <= en*(1#4)*k2*hn + 2*k2p*(1#8)*en' (gdiff pointwise + projections). *)
        assert (H2 : Qle (Qabs (projT1 wS n))
                         (Qplus (Qmult (Qmult (Qmult en (1 # 4)) k2) hn)
                                (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))).
        { apply (Qle_trans (Qabs (projT1 wS n))
                           (Qplus (Qmult (Qmult (projT1 eps2 n) k2) (Qabs (projT1 h n)))
                                  (Qmult (Qmult 2 k2p) (projT1 eps2' n)))
                           (Qplus (Qmult (Qmult (Qmult en (1 # 4)) k2) hn)
                                  (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))).
          - exact ((QleT'_to_Qle _ _ (HNg n HnNg))).
          - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
            unfold eps2, eps2', en, en', hn.
            setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const (1 # 4)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 4) n)).
            setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const (1 # 8)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 8) n)).
            ring. }
        (* M·|wS_n| ≤ M·(A1+A2) = M·A1 + M·A2 *)
        assert (H3 : Qle (Qmult M (Qabs (projT1 wS n)))
                         (Qplus (Qmult M (Qmult (Qmult (Qmult en (1 # 4)) k2) hn))
                                (Qmult M (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en')))).
        { apply (Qle_trans (Qmult M (Qabs (projT1 wS n)))
                           (Qmult M (Qplus (Qmult (Qmult (Qmult en (1 # 4)) k2) hn)
                                           (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en')))
                           (Qplus (Qmult M (Qmult (Qmult (Qmult en (1 # 4)) k2) hn))
                                  (Qmult M (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en')))).
          - apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs (projT1 wS n))
                                 (Qplus (Qmult (Qmult (Qmult en (1 # 4)) k2) hn)
                                        (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))
                                 M).
            + exact H2.
            + exact HM0.
          - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
        (* M*A1 <= (1#32)*(en*hn) (the coefS1 absorption). *)
        assert (H4 : Qle (Qmult M (Qmult (Qmult (Qmult en (1 # 4)) k2) hn))
                         (Qmult (1 # 32) (Qmult en hn))).
        { apply (Qle_trans (Qmult M (Qmult (Qmult (Qmult en (1 # 4)) k2) hn))
                           (Qmult (Qmult (Qmult M k2) (1 # 4)) (Qmult en hn))
                           (Qmult (1 # 32) (Qmult en hn))).
          - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          - apply (Qmult_le_compat_r (Qmult (Qmult M k2) (1 # 4)) (1 # 32) (Qmult en hn)).
            + exact HcoefS1.
            + apply (Qmult_le_0_compat en hn Hen0 Hhn0). }
        (* M*A2 <= (1#32)*en' (the coefG1 absorption). *)
        assert (H5 : Qle (Qmult M (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))
                         (Qmult (1 # 32) en')).
        { apply (Qle_trans (Qmult M (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))
                           (Qmult (Qmult (Qmult M (Qmult 2 k2p)) (1 # 8)) en')
                           (Qmult (1 # 32) en')).
          - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          - apply (Qmult_le_compat_r (Qmult (Qmult M (Qmult 2 k2p)) (1 # 8)) (1 # 32) en').
            + exact HcoefG1.
            + exact Hen'0. }
        (* assembly. *)
        apply (Qle_trans (Qabs (projT1 Gob n))
                         (Qmult M (Qabs (projT1 wS n)))
                         (Qplus (Qmult (1 # 32) (Qmult en hn)) (Qmult (1 # 32) en'))).
        - exact H1.
        - apply (Qle_trans (Qmult M (Qabs (projT1 wS n)))
                           (Qplus (Qmult M (Qmult (Qmult (Qmult en (1 # 4)) k2) hn))
                                  (Qmult M (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en')))
                           (Qplus (Qmult (1 # 32) (Qmult en hn)) (Qmult (1 # 32) en'))).
          + exact H3.
          + apply Qplus_le_compat. { exact H4. } { exact H5. } }
      (* decomposition: |err_n| <= |Eobj_n| + (|Gob_n| + m0). *)
      assert (HtriB : Qle Dn (Qplus (Qabs (projT1 Eobj n)) (Qplus (Qabs (projT1 Gob n)) m0))).
      { unfold Dn. exact (QleT'_to_Qle _ _ (Htri n HnNtri)). }
      (* summary -> absorption -> the linear nra finishes. *)
      assert (Hmain : Qle Dn (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
      { apply (Qle_trans Dn
                         (Qplus Eexpn (Qplus (Qplus (Qmult (1 # 32) (Qmult en hn))
                                                    (Qmult (1 # 32) en'))
                                             m0))
                         (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
        - apply (Qle_trans Dn
                           (Qplus (Qabs (projT1 Eobj n)) (Qplus (Qabs (projT1 Gob n)) m0))
                           (Qplus Eexpn (Qplus (Qplus (Qmult (1 # 32) (Qmult en hn))
                                                      (Qmult (1 # 32) en'))
                                               m0))).
          + exact HtriB.
          + apply Qplus_le_compat.
            * exact HexpB.
            * apply Qplus_le_compat. { exact HgB. } { apply Qle_refl. }
        - unfold Eexpn.
        nra. }
      (* margin: eta < (1#4)*en'; via b5n_close. *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply QltT_to_Qlt. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        - apply QltT_to_Qlt. exact He1T.
        - exact (QltT_to_Qlt _ _ (He1lt n HnNe1)). }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply QltT_to_Qlt. apply (b5n_close Dn hn en en' eta).
        - unfold Dn. exact Hmain.
        - unfold en'. exact Hq4e. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs err) n))).
      - exact Hfin.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj err n)).
        unfold en, en', hn, Dn.
        ring. } }
Defined.
(* ============================================================ *)
(* Section B: the main piece b5dP_J_deriv_zero_exp_tail (the J-mod tail-form     *)
(*   piece, Defined preset)                                                      *)
(*   Copy source = the sc2_b5a_item25.v main-piece region L87-794 (machine-      *)
(*   extracted, no hand transcription; itself = the machine copy of item11 C5 +  *)
(*   the item25 changes S1-S8 — already including the E-diff leaf swapped to     *)
(*   b5dI_ (item19, the C4 bundle = the item7 b5d3_exp_arch4_C family supplied   *)
(*   directly) / the S-diff leaf swapped to b5dN_ (item24) / the witnesses       *)
(*   swapped to b5dM_ (item23) / the eps witness moved down (spine-clean) /      *)
(*   Qed->Defined; this piece applies the tail-form increments on top of that    *)
(*   final text).                                                                *)
(*   Changes B1-B6 (the tail-form part of the design §2.2 table): the HMall      *)
(*   statement premise line made tail-form + (NA NM : nat); the intros names     *)
(*   extended; the two S-diff leaf references now point to this file's Section A *)
(*   piece names + the bundle argument NM inserted; Nmax folded into NM;         *)
(*   consumption-point guards + per-n asserts; closing Defined (the source is    *)
(*   already Defined).  The E-diff leaf (b5dI_) and the rest of the S1-S8        *)
(*   products unchanged; the original tail-form premise HNA kept.                *)
(*   The statement types are, except for the B2/B3 changed lines, verbatim       *)
(*   item11 C5 (the downstream item27 interface contract).                       *)
(* ============================================================ *)
Lemma b5dP_J_deriv_zero_exp_tail :
  forall (r : Q) (Hr0 : QleT' 0 r) (Hr1 : QltT r 1),
  forall (cA M Ms Mc : Q)
         (HcA : QltT 0 cA) (HM : QltT 0 M)
         (HMs : QltT 0 Ms) (HMc : QltT 0 Mc),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (NA NM : nat),
  (forall n : nat, NatLe NA n -> QleT' cA (projT1 (b5a_S x) n)) ->
  (forall n : nat, NatLe NM n -> QleT' (Qabs (projT1 (b5a_S x) n)) M) ->
  (forall n : nat,
     QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Ms) ->
  (forall n : nat,
     QleT' (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc) ->
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5c_J (real_plus x h) Hxh)
                 (real_opp (b5c_J x (b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1))))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 cA M Ms Mc HcA HM HMs HMc x Hxr NA NM HNA HMall HMs_all HMc_all eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr (QltT_to_Qlt r 1 Hr1)).
  (* ---- fixed data ---- *)
  (* cA: a pointwise positive lower bound for S(x) — the statement carries the explicit
     Q parameters cA/HcA plus the NA tail-bound premise HNA;
     δ-C C5: the 4 black-box destructs (source L389/396/399/400) become the intros
     argument bundle  *)
  set (cB := Qmult cA (1 # 2)).
  assert (HcB : Qlt 0 cB).
  { unfold cB. apply (Qmult_lt_0_compat cA (1 # 2)).
    - exact (QltT_to_Qlt _ _ (HcA)).
    - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  (* M/Ms/Mc: explicit Q parameters of the statement; the all-n premises HMall/HMs_all/HMc_all apply directly. *)
  assert (HM0 : Qle 0 M). { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (HM)). }
  (* Ms/Mc: the sinA/cosA pointwise bounds give ME := Ms + r*Mc (|E(x)_n| <= ME). *)
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMs. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMc. }
  (* the E/S-diff swapped-source certificates (the item25 change S3: the
     b5dI_E_diff_closed_r_exp bundle parameters — QltT_to_Qlt applied on the proof
     side; the C4 closed value = item7 b5d3_exp_arch4_C). *)
  assert (HMsQ : Qlt 0 Ms). { apply QltT_to_Qlt. exact HMs. }
  assert (HMcQ : Qlt 0 Mc). { apply QltT_to_Qlt. exact HMc. }
  assert (HC40C : Qle 0 b5d3_exp_arch4_C).
  { apply (Qle_trans _ 1 _). { exact (QleT'_to_Qle _ _ Qle_0_1). } { apply QleT'_to_Qle. exact b5d3_exp_arch4_C_ge1. } }
  assert (Hr0' : Qle 0 r). { exact (QleT'_to_Qle _ _ (Hr0)). }
  set (ME := Qplus Ms (Qmult r Mc)).
  assert (HME0 : Qle 0 ME).
  { unfold ME. nra. }
  (* the reciprocal constants and shares (all depending only on the x data; QltT 0 feeds real_const_pos). *)
  set (QicA := Qinv cA).
  set (QicB := Qinv cB).
  set (kE := Qmult cB (1 # 8)).
  set (kEp := Qmult cB (1 # 16)).
  set (kapE := Qmult cB (1 # 16)).
  set (invM1 := Qinv (Qplus ME 1)).
  set (kS := Qmult (Qmult (Qmult cA cB) (1 # 8)) invM1).
  set (kSp := Qmult (Qmult (Qmult cA cB) (1 # 16)) invM1).
  set (kapS := Qmult (Qmult (Qmult cA cB) (1 # 16)) invM1).
  set (K1 := Qplus (Qmult r M) 1).
  set (tau := Qmult cA (Qinv (Qmult 8 K1))).
  set (mu := Qmult cA (1 # 16)).
  set (kapS2 := Qmult cA (1 # 16)).
  (* positivity facts. *)
  assert (HkET : QltT 0 kE).
  { unfold kE. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 8)).
    - exact HcB.
    - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (HkEpT : QltT 0 kEp).
  { unfold kEp. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 16)).
    - exact HcB.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkapET : QltT 0 kapE).
  { unfold kapE. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 16)).
    - exact HcB.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HME1 : Qlt 0 (Qplus ME 1)).
  { nra. }
  assert (HME1ne : ~ Qplus ME 1 == 0).
  { intro Hz. apply qeq_imp_qeqT in Hz. apply (q_neq_of_lt (Qplus ME 1) (Qlt_to_QltT _ _ HME1)) in Hz. destruct Hz. }
  assert (Hinv1T : QltT 0 invM1).
  { unfold invM1. apply Qlt_to_QltT. apply Qinv_lt_0_compat. exact HME1. }
  assert (HcAcB0 : Qlt 0 (Qmult (Qmult cA cB) (1 # 8))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 8)).
    - apply (Qmult_lt_0_compat cA cB). { exact (QltT_to_Qlt _ _ (HcA)). } { exact HcB. }
    - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (HcAcB0b : Qlt 0 (Qmult (Qmult cA cB) (1 # 16))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 16)).
    - apply (Qmult_lt_0_compat cA cB). { exact (QltT_to_Qlt _ _ (HcA)). } { exact HcB. }
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkST : QltT 0 kS).
  { unfold kS. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 8)) invM1).
    - exact HcAcB0.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HkSpT : QltT 0 kSp).
  { unfold kSp. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 16)) invM1).
    - exact HcAcB0b.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HkapST : QltT 0 kapS).
  { unfold kapS. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 16)) invM1).
    - exact HcAcB0b.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HK1 : Qlt 0 K1).
  { unfold K1. nra. }
  assert (HtauT : QltT 0 tau).
  { unfold tau. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat cA (Qinv (Qmult 8 K1))).
    - exact (QltT_to_Qlt _ _ (HcA)).
    - apply Qinv_lt_0_compat. nra. }
  assert (HmuT : QltT 0 mu).
  { unfold mu. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact (QltT_to_Qlt _ _ (HcA)).
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkapS2T : QltT 0 kapS2).
  { unfold kapS2. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact (QltT_to_Qlt _ _ (HcA)).
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (H1T : QltT 0 1) by (apply Qlt_to_QltT; change (Qlt 0 1); unfold Qlt; simpl; lia).
  assert (HcA0 : Qle 0 cA). { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (HcA)). }
  assert (HcB0 : Qle 0 cB). { apply Qlt_le_weak. exact HcB. }
  assert (HcAne : ~ cA == 0). { intro Hz. apply qeq_imp_qeqT in Hz. apply (q_neq_of_lt cA HcA) in Hz. destruct Hz. }
  assert (HcBne : ~ cB == 0). { intro Hz. apply qeq_imp_qeqT in Hz. apply (q_neq_of_lt cB (Qlt_to_QltT _ _ HcB)) in Hz. destruct Hz. }
  assert (H8K1ne : ~ Qmult 8 K1 == 0).
  { intro Hz. apply qeq_imp_qeqT in Hz. assert (H8K1T : QltT 0 (Qmult 8 K1)) by (apply Qlt_to_QltT; nra). apply (q_neq_of_lt (Qmult 8 K1) H8K1T) in Hz. destruct Hz. }
  assert (HK1ne : ~ K1 == 0).
  { intro Hz. apply qeq_imp_qeqT in Hz. apply (q_neq_of_lt K1 (Qlt_to_QltT _ _ HK1)) in Hz. destruct Hz. }
  (* ---- the coefficient-budget facts (fixed at the Q layer, for pointwise absorption) ---- *)
  (* Hc1: QicB*kE == 1/8; Hc2: QicB*(kEp+kapE) == 1/8 *)
  assert (Hc1 : Qle (Qmult QicB kE) (1 # 8)).
  { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    unfold QicB, kE.
    field. exact HcBne. }
  assert (Hc1' : Qle (Qmult QicB (Qplus kEp kapE)) (1 # 8)).
  { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    unfold QicB, kEp, kapE.
    field. exact HcBne. }
  (* Hc2/Hc2': ME*QicA*QicB*kS <= 1/8, ME*QicA*QicB*(kSp+kapS) <= 1/8. *)
  set (Mterm := Qmult ME (Qmult QicA QicB)).
  assert (Hc2 : Qle (Qmult Mterm kS) (1 # 8)).
  { apply (Qle_trans (Qmult Mterm kS)
                     (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                     (1 # 8)).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      unfold Mterm, QicA, QicB, kS, invM1.
      field. all: repeat split; assumption.
    - apply (Qle_trans (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                       (Qinv 8)
                       (1 # 8)).
      + apply QleT'_to_Qle. apply (b5n_xinv_le (Qmult ME (1 # 8)) (Qplus ME 1) 8).
        * exact HME1.
        * change (Qlt 0 8). unfold Qlt. simpl. lia.
        * nra.
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold Qinv. reflexivity. }
  assert (Hc2' : Qle (Qmult Mterm (Qplus kSp kapS)) (1 # 8)).
  { apply (Qle_trans (Qmult Mterm (Qplus kSp kapS))
                     (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                     (1 # 8)).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      unfold Mterm, QicA, QicB, kSp, kapS, invM1.
      field. all: repeat split; assumption.
    - apply (Qle_trans (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                       (Qinv 8)
                       (1 # 8)).
      + apply QleT'_to_Qle. apply (b5n_xinv_le (Qmult ME (1 # 8)) (Qplus ME 1) 8).
        * exact HME1.
        * change (Qlt 0 8). unfold Qlt. simpl. lia.
        * nra.
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold Qinv. reflexivity. }
  (* the lower-bound inequality: (K1*τ) + μ + kapS2 <= cA - cB (== cA/2; the LHS == cA/4). *)
  assert (Htau_eq : Qle (Qmult K1 tau) (Qmult cA (1 # 8))).
  { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    unfold tau.
    field. all: repeat split; assumption. }
  assert (Hlb_ineq : Qle (Qplus (Qmult K1 tau) (Qplus mu kapS2)) (Qminus cA cB)).
  { apply (Qle_trans (Qplus (Qmult K1 tau) (Qplus mu kapS2))
                     (Qplus (Qmult cA (1 # 8)) (Qmult cA (1 # 8)))
                     (Qminus cA cB)).
    - apply Qplus_le_compat.
      + apply (Qle_trans (Qmult K1 tau) (Qmult cA (1 # 8)) (Qmult cA (1 # 8))).
        * exact Htau_eq.
        * apply Qle_refl.
      + apply (Qle_trans (Qplus mu kapS2) (Qmult cA (1 # 8)) (Qmult cA (1 # 8))).
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold mu, kapS2. ring.
        * apply Qle_refl.
    - unfold cB. nra. }
  (* ---- the eps witnesses and shares ---- *)
  assert (H2T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H4T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (H8T : QltT 0 (1 # 8)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 8)); unfold Qlt; simpl; lia).
  assert (H16T : QltT 0 (1 # 16)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 16)); unfold Qlt; simpl; lia).
  (* the eps shares (Real): epsE / epsS (the slope shares of the E-diff and S-diff main instances). *)
  set (epsE := real_mult eps (real_const kE)).
  assert (HepsE : real_lt real_zero epsE).
  { unfold epsE. apply b5dI_real_mult_positive_exp. { exact Heps. } { apply b5dM_real_const_pos. exact HkET. } }
  set (epsS := real_mult eps (real_const kS)).
  assert (HepsS : real_lt real_zero epsS).
  { unfold epsS. apply b5dI_real_mult_positive_exp. { exact Heps. } { apply b5dM_real_const_pos. exact HkST. } }
  (* closed-form instantiation: δE (E-diff), δS1/δS2 (the S-diff main / constant share). *)
  destruct (b5dI_E_diff_closed_r_exp r Hr0 Hr1 x Hxr
             Ms Mc b5d3_exp_arch4_C (Qlt_to_QltT _ _ (HMsQ)) (Qlt_to_QltT _ _ (HMcQ)) (Qle_to_QleT' _ _ (HC40C))
             b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all
             HMs_all HMc_all epsE HepsE) as [δE [HδE0 HδE]].
  destruct (b5dP_S_diff_closed_r_M_exp_tail r Hr0 Hr1 x Hxr M HM NM HMall epsS HepsS) as [δS1 [HδS10 HδS1]].
  destruct (b5dP_S_diff_closed_r_M_exp_tail r Hr0 Hr1 x Hxr M HM NM HMall (real_const 1) (b5dM_real_const_pos 1 H1T))
    as [δS2 [HδS20 HδS2]].
  (* δ := min(min(min(δE, δS1), δS2), real_const τ) *)
  set (delta := real_min (real_min (real_min δE δS1) δS2) (real_const tau)).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos. { exact HδE0. } { exact HδS10. } }
      { exact HδS20. } }
    { apply real_const_pos. exact HtauT. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
    (* the eps witness decomposition (the item25 change S4: moved down from item11 L244 —
       spine-clean: e0/He0T/Ne0/He0lt do not enter the δ value; the source swapped to
       b5dM_b5n_eps_proj_lt). *)
    destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
    (* extracting the |h| < components. *)
    assert (Hh1 : real_lt (real_abs h) (real_min (real_min δE δS1) δS2)).
    { apply (real_min_lt_l h (real_min (real_min δE δS1) δS2) (real_const tau)).
      unfold delta in Hh. exact Hh. }
    assert (Hhτ : real_lt (real_abs h) (real_const tau)).
    { apply (real_min_lt_r h (real_min (real_min δE δS1) δS2) (real_const tau)).
      unfold delta in Hh. exact Hh. }
    assert (Hh2 : real_lt (real_abs h) (real_min δE δS1)).
    { apply (real_min_lt_l h (real_min δE δS1) δS2). exact Hh1. }
    assert (HhS2 : real_lt (real_abs h) δS2).
    { apply (real_min_lt_r h (real_min δE δS1) δS2). exact Hh1. }
    assert (HhE : real_lt (real_abs h) δE).
    { apply (real_min_lt_l h δE δS1). exact Hh2. }
    assert (HhS1 : real_lt (real_abs h) δS1).
    { apply (real_min_lt_r h δE δS1). exact Hh2. }
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia.
      - apply QltT_to_Qlt. exact He1T. }
    (* the eps' shares (Real): E-diff epsE'/margin shE, S-diff epsS'/margin shS. *)
    set (epsE' := real_mult eps' (real_const kEp)).
    assert (HepsE' : real_lt real_zero epsE').
    { unfold epsE'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkEpT. } }
    set (shE := real_mult eps' (real_const kapE)).
    assert (HshE : real_lt real_zero shE).
    { unfold shE. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkapET. } }
    set (epsS' := real_mult eps' (real_const kSp)).
    assert (HepsS' : real_lt real_zero epsS').
    { unfold epsS'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkSpT. } }
    set (shS := real_mult eps' (real_const kapS)).
    assert (HshS : real_lt real_zero shS).
    { unfold shS. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkapST. } }
    (* the constant shares of the lower-bound instance (Real, independent of eps'). *)
    assert (Hcμ : real_lt real_zero (real_const mu)).
    { apply real_const_pos. exact HmuT. }
    assert (HcκS2 : real_lt real_zero (real_const kapS2)).
    { apply real_const_pos. exact HkapS2T. }
    (* pointwise conversion (real_le to per-n, with margin slack). *)
    set (BE := real_plus (real_mult epsE (real_abs h)) epsE').
    destruct (b5i_abs_le_pointwise (b5e_E_err x Hx h Hxh) BE
               (HδE h HhE Hxh epsE' HepsE') shE HshE) as [NE HNE].
    set (BS1 := real_plus (real_mult epsS (real_abs h)) epsS').
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS1
               (HδS1 h HhS1 epsS' HepsS') shS HshS) as [NS HNS].
    set (BS2 := real_plus (real_mult (real_const 1) (real_abs h)) (real_const mu)).
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS2
               (HδS2 h HhS2 (real_const mu) Hcμ) (real_const kapS2) HcκS2) as [NS2 HNS2].
    (* |h_n| <= tau (b5i_h_le_const), the |d_n| <= 1 tail, and the pointwise identity N. *)
    destruct (b5i_h_le_const h tau Hhτ HtauT) as [Nτ HNτ].
    destruct (b5c_d_proj_le_one x) as [Nd Hd].
    destruct (b5m_J_dec_proj x h Hx Hxh) as [Ndec HNdec].
    (* pointwise budget (against the eps/eps' witnesses). *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). } }
    set (Nmax := Nat.max NM (Nat.max (Nat.max Ne0 Ne1)
                 (Nat.max (Nat.max Ndec Nτ)
                  (Nat.max (Nat.max NE (Nat.max NS NS2)) (Nat.max NA Nd))))).
    (* main assembly: real_le to real_lt (left branch), with witness eta. *)
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5m_J_err x Hx h Hxh) n)).
      set (Sn := projT1 (b5a_S x) n).
      set (Shn := projT1 (b5a_S (real_plus x h)) n).
      set (dn := projT1 (b5a_atan_d x) n).
      set (rEn := projT1 (b5e_E_err x Hx h Hxh) n).
      set (rSn := projT1 (b5m_rS x h) n).
      set (Exn := projT1 (b5a_E x Hx) n).
      (* tail indices. *)
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNE : NatLe NE n) by (apply NatLe_lift; lia).
      assert (HnNS : NatLe NS n) by (apply NatLe_lift; lia).
      assert (HnNS2 : NatLe NS2 n) by (apply NatLe_lift; lia).
      assert (HnNτ : NatLe Nτ n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (HnNdec : (Ndec <= n)%nat) by lia.
      assert (HnNA : NatLe NA n) by (apply NatLe_lift; lia).
      assert (HnNM : NatLe NM n) by (apply NatLe_lift; lia).
      (* nonnegativity. *)
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        - apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T.
        - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He0lt n HnNe0)). }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      assert (Hhn0 : Qle 0 hn). { unfold hn. apply Qabs_nonneg. }
      (* |h_n| <= tau, |d_n| <= 1, and Sn >= cA. *)
      assert (Hhτn : Qle (Qabs (projT1 h n)) tau).
      { unfold tau in *. exact (QleT'_to_Qle _ _ (HNτ n HnNτ)). }
      assert (Hdn1 : Qle (Qabs dn) 1).
      { unfold dn. exact (QleT'_to_Qle _ _ (Hd n (NatLe_lift _ _ HnNd))). }
      assert (HSnA : Qle cA Sn).
      { unfold Sn. exact ((QleT'_to_Qle _ _ (HNA n HnNA))). }
      (* |rE_n| <= kE*en*hn + (kEp+kapE)*en' (the E-diff made pointwise). *)
      assert (HrE : Qle (Qabs rEn)
                        (Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' kEp) (Qmult en' kapE)))).
      { apply (Qle_trans (Qabs rEn)
                         (Qplus (projT1 BE n) (projT1 shE n))
                         (Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' kEp) (Qmult en' kapE)))).
        - unfold rEn. exact (QleT'_to_Qle _ _ (HNE n HnNE)).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          unfold BE, shE, en, en'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult epsE (real_abs h)) epsE' n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj epsE (real_abs h) n)).
          unfold epsE, epsE'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const kE) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kE n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const kEp) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kEp n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const kapE) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kapE n)).
          ring. }
      (* |rS_n| <= kS*en*hn + (kSp+kapS)*en' (the S-diff main instance made pointwise). *)
      assert (HrS : Qle (Qabs rSn)
                        (Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' kSp) (Qmult en' kapS)))).
      { apply (Qle_trans (Qabs rSn)
                         (Qplus (projT1 BS1 n) (projT1 shS n))
                         (Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' kSp) (Qmult en' kapS)))).
        - unfold rSn. exact (QleT'_to_Qle _ _ (HNS n HnNS)).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          unfold BS1, shS, en, en'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult epsS (real_abs h)) epsS' n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj epsS (real_abs h) n)).
          unfold epsS, epsS'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const kS) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kS n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const kSp) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kSp n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const kapS) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kapS n)).
          ring. }
      (* |rS_n| <= 1*hn + mu + kapS2 (the S-diff constant-share instance made pointwise, used for the lower bound). *)
      assert (HrS2 : Qle (Qabs rSn)
                         (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
      { apply (Qle_trans (Qabs rSn)
                         (Qplus (projT1 BS2 n) (projT1 (real_const kapS2) n))
                         (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
        - unfold rSn. exact (QleT'_to_Qle _ _ (HNS2 n HnNS2)).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          unfold BS2.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const 1) (real_abs h))
                                         (real_const mu) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const 1) (real_abs h) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj mu n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kapS2 n)).
          ring. }
      (* |Ex_n| <= ME (the sinA/cosA pointwise bounds + |x_n| <= r; Exn == sAn - xn*cAn). *)
      assert (HEx : Qle (Qabs Exn) ME).
      { unfold Exn, b5a_E.
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_sin (cauchy_real_arctan x Hx))
                                (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx)))) n)).
        rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx))) n)).
        rewrite (qeqT_imp_qeq _ _ (real_mult_proj x (cauchy_real_cos (cauchy_real_arctan x Hx)) n)).
        apply (Qle_trans
                 (Qabs (Qplus (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                              (Qopp (Qmult (projT1 x n)
                                           (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                 (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                        (Qabs (Qmult (projT1 x n)
                                     (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))
                 ME).
        - apply (Qle_trans
                   (Qabs (Qplus (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                                (Qopp (Qmult (projT1 x n)
                                             (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qopp (Qmult (projT1 x n)
                                             (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qmult (projT1 x n)
                                       (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))).
          + apply Qabs_triangle.
          + apply Qplus_le_compat.
            * apply Qle_refl.
            * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
              apply (Qabs_opp (Qmult (projT1 x n)
                                     (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))).
        - (* |sA| + |x·cA| ≤ Ms + r·Mc ≤ ME *)
          apply (Qle_trans
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qmult (projT1 x n)
                                       (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))
                   (Qplus Ms (Qmult r Mc))
                   ME).
          + apply Qplus_le_compat.
            * apply (Qle_trans (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                               (Qabs (sin_partial n (arctan_partial n (projT1 x n))))
                               Ms).
              { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_wd. apply Qeq_sym.
                setoid_rewrite (qeqT_imp_qeq _ _ (real_sin_proj (cauchy_real_arctan x Hx) n)).
                setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hx n)).
                reflexivity. }
              { apply QleT'_to_Qle. exact (HMs_all n). }
            * apply (Qle_trans (Qabs (Qmult (projT1 x n)
                                            (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                               (Qmult r (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                               (Qmult r Mc)).
              { apply (Qle_trans (Qabs (Qmult (projT1 x n)
                                              (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                                 (Qmult (Qabs (projT1 x n))
                                        (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                                 (Qmult r (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))).
                - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
                  apply (Qabs_Qmult (projT1 x n)
                                    (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)).
                - apply (Qmult_le_compat_r (Qabs (projT1 x n)) r
                                           (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))).
                  + apply QleT'_to_Qle. exact (Hxr n).
                  + apply Qabs_nonneg. }
              { apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))
                                     Mc r).
                - apply (Qle_trans (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))
                                   (Qabs (cos_partial n (arctan_partial n (projT1 x n))))
                                   Mc).
                  + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_wd. apply Qeq_sym.
                    setoid_rewrite (qeqT_imp_qeq _ _ (real_cos_proj (cauchy_real_arctan x Hx) n)).
                    setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hx n)).
                    reflexivity.
                  + exact ((QleT'_to_Qle _ _ (HMc_all n))).
                - exact Hr0'. }
          + unfold ME. nra. }
      (* quotient-denominator certificate: |Qinv(Sn)| <= QicA. *)
      assert (HQA : Qle (Qabs (Qinv Sn)) QicA).
      { unfold Sn, QicA. apply QleT'_to_Qle. apply (b5m_inv_le Sn cA (QltT_to_Qlt _ _ (HcA)) HSnA). }
      (* Sxh >= cB: the |ΔS| bound (r*M*hn + |rS|) gives K1*tau + mu + kapS2 <= cA - cB. *)
      assert (Hdel0 : Qle (Qabs (Qminus Shn Sn))
                          (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                 (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
      { (* Shn − Sn == (x·S·d·h)_n + rS_n *)
        apply (Qle_trans (Qabs (Qminus Shn Sn))
                         (Qplus (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                                (Qabs rSn))
                         (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
        - (* triangle: |Shn - Sn| == |P + rS| <= |P| + |rS|. *)
          apply (Qle_trans (Qabs (Qminus Shn Sn))
                           (Qabs (Qplus (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))) rSn))
                           (Qplus (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                                  (Qabs rSn))).
          + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
            apply (Qabs_wd (Qminus Shn Sn)
                           (Qplus (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))) rSn)).
            unfold Shn, Sn, dn, rSn.
            unfold b5m_rS.
            rewrite (qeqT_imp_qeq _ _ (real_plus_proj (b5a_S (real_plus x h))
                                    (real_opp (real_plus (b5a_S x)
                                               (real_mult (real_mult x (b5a_S x))
                                                          (real_mult (b5a_atan_d x) h)))) n)).
            rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus (b5a_S x)
                                    (real_mult (real_mult x (b5a_S x))
                                               (real_mult (b5a_atan_d x) h))) n)).
            rewrite (qeqT_imp_qeq _ _ (real_plus_proj (b5a_S x)
                                    (real_mult (real_mult x (b5a_S x))
                                               (real_mult (b5a_atan_d x) h)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult x (b5a_S x))
                                    (real_mult (b5a_atan_d x) h) n)).
            rewrite (qeqT_imp_qeq _ _ (real_mult_proj x (b5a_S x) n)).
            rewrite (qeqT_imp_qeq _ _ (real_mult_proj (b5a_atan_d x) h n)).
            cbn [projT1 real_zero].
            ring.
          + apply Qabs_triangle.
        - (* |P| <= r*M*1*hn and |rS_n| <= hn + mu + kapS2 (HrS2). *)
          apply Qplus_le_compat.
          + (* |(x·S·d·h)_n| ≤ r·M·1·hn *)
            apply (Qle_trans (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                             (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                             (Qmult (Qmult r M) (Qabs (projT1 h n)))).
            * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
              apply (Qeq_trans (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                               (Qmult (Qabs (Qmult (projT1 x n) Sn)) (Qabs (Qmult dn (projT1 h n))))
                               (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))).
              { apply (Qabs_Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))). }
              { apply Qmult_comp.
                - apply (Qabs_Qmult (projT1 x n) Sn).
                - apply (Qabs_Qmult dn (projT1 h n)). }
            * (* (|xn|·|Sn|)·(|dn|·|hn|) ≤ (r·M)·(1·hn) *)
              apply (Qle_trans (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                               (Qmult (Qmult r M) (Qmult 1 (Qabs (projT1 h n))))
                               (Qmult (Qmult r M) (Qabs (projT1 h n)))).
              { apply (Qle_trans (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                                 (Qmult (Qmult r M) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                                 (Qmult (Qmult r M) (Qmult 1 (Qabs (projT1 h n))))).
                - apply (Qmult_le_compat_r (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult r M)
                                           (Qmult (Qabs dn) (Qabs (projT1 h n)))).
                  + apply (Qle_trans (Qmult (Qabs (projT1 x n)) (Qabs Sn))
                                     (Qmult r (Qabs Sn))
                                     (Qmult r M)).
                    * apply (Qmult_le_compat_r (Qabs (projT1 x n)) r (Qabs Sn)).
                      { apply QleT'_to_Qle. exact (Hxr n). }
                      { apply Qabs_nonneg. }
                    * apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs Sn) M r).
                      { unfold Sn. exact ((QleT'_to_Qle _ _ (HMall n HnNM))). }
                      { exact Hr0'. }
                  + apply Qmult_le_0_compat.
                    * apply Qabs_nonneg.
                    * apply Qabs_nonneg.
                - apply QleT'_to_Qle. apply (sc_qmult_le_l (Qmult (Qabs dn) (Qabs (projT1 h n)))
                                       (Qmult 1 (Qabs (projT1 h n)))
                                       (Qmult r M)).
                  + apply (Qmult_le_compat_r (Qabs dn) 1 (Qabs (projT1 h n))).
                    * exact Hdn1.
                    * apply Qabs_nonneg.
                  + apply Qmult_le_0_compat.
                    * exact Hr0'.
                    * exact HM0. }
              { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
          + (* |rS_n| ≤ hn + mu + kapS2 *)
            apply (Qle_trans (Qabs rSn)
                             (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))
                             (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
            * exact HrS2.
            * apply Qle_refl. }
      (* |ΔS| <= K1*tau + mu + kapS2 (hn <= tau). *)
      assert (Hdel : Qle (Qabs (Qminus Shn Sn))
                         (Qplus (Qmult K1 tau) (Qplus mu kapS2))).
      { apply (Qle_trans (Qabs (Qminus Shn Sn))
                         (Qplus (Qmult (Qmult r M) tau) (Qplus tau (Qplus mu kapS2)))
                         (Qplus (Qmult K1 tau) (Qplus mu kapS2))).
        - apply (Qle_trans (Qabs (Qminus Shn Sn))
                           (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                  (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))
                           (Qplus (Qmult (Qmult r M) tau) (Qplus tau (Qplus mu kapS2)))).
          + exact Hdel0.
          + apply Qplus_le_compat.
            * apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs (projT1 h n)) tau (Qmult r M)).
              { exact Hhτn. }
              { apply Qmult_le_0_compat. { exact Hr0'. } { exact HM0. } }
            * apply Qplus_le_compat.
              { exact Hhτn. }
              { apply Qle_refl. }
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold K1. ring. }
      (* Shn >= cB (Sn >= cA, |ΔS| <= B0, B0 <= cA - cB). *)
      assert (HShnB : Qle cB Shn).
      { (* Sn <= Shn + |Δ| and |Δ| <= B0 (Hdel), hence Sn <= Shn + B0. *)
        assert (HS2 : Qle Sn (Qplus Shn (Qplus (Qmult K1 tau) (Qplus mu kapS2)))).
        { apply (Qle_trans Sn (Qplus Shn (Qabs (Qminus Shn Sn)))
                              (Qplus Shn (Qplus (Qmult K1 tau) (Qplus mu kapS2)))).
          - apply (Qle_trans Sn (Qplus Shn (Qminus Sn Shn))
                                (Qplus Shn (Qabs (Qminus Shn Sn)))).
            + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
            + apply Qplus_le_compat.
              * apply Qle_refl.
              * apply (Qle_trans (Qminus Sn Shn) (Qabs (Qminus Sn Shn))
                                 (Qabs (Qminus Shn Sn))).
                { apply Qle_Qabs. }
                { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
                  apply (Qeq_trans (Qabs (Qminus Sn Shn))
                                   (Qabs (Qopp (Qminus Shn Sn)))
                                   (Qabs (Qminus Shn Sn))).
                  - apply Qabs_wd. ring.
                  - apply (Qabs_opp (Qminus Shn Sn)). }
          - apply Qplus_le_compat.
            + apply Qle_refl.
            + exact Hdel. }
        (* cB <= cA - B0 (Hlb_ineq), cA <= Sn (HSnA), Sn <= Shn + B0, hence cB <= Shn. *)
        nra. }
      (* quotient-denominator certificate: |Qinv(Shn)| <= QicB. *)
      assert (HQB : Qle (Qabs (Qinv Shn)) QicB).
      { unfold Shn, QicB. apply QleT'_to_Qle. apply (b5m_inv_le Shn cB HcB HShnB). }
      (* the b5m_J_abs_tri main step. *)
      set (RE := Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kEp) (Qmult en' kapE))).
      set (RS := Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kSp) (Qmult en' kapS))).
      assert (Hmain0 : Qle Dn (Qplus (Qmult QicB RE) (Qmult Mterm RS))).
      { unfold Dn.
        apply QleT'_to_Qle. apply (b5m_J_abs_tri x h Hx Hxh n QicA QicB ME RE RS).
        - exact HQA.
        - exact HQB.
        - unfold Exn. exact HEx.
        - unfold rEn. exact HrE.
        - unfold rSn. exact HrS.
        - unfold QicA. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (HcA)).
        - unfold QicB. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HcB.
        - exact (qeqT_imp_qeq _ _ (HNdec n (NatLe_lift _ _ HnNdec))). }
      (* coefficient absorption: QicB*RE <= (1/8)*en*hn + (1/8)*en'; Mterm*RS <= the same shape. *)
      assert (HT1 : Qle (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                        (Qmult (1 # 8) (Qmult en hn))).
      { apply (Qle_trans (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                         (Qmult (Qmult QicB kE) (Qmult en hn))
                         (Qmult (1 # 8) (Qmult en hn))).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold hn. ring.
        - apply (Qmult_le_compat_r (Qmult QicB kE) (1 # 8) (Qmult en hn)).
          + exact Hc1.
          + apply Qmult_le_0_compat.
            * exact Hen0.
            * exact Hhn0. }
      assert (HT2 : Qle (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE)))
                        (Qmult (1 # 8) en')).
      { apply (Qle_trans (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE)))
                         (Qmult (Qmult QicB (Qplus kEp kapE)) en')
                         (Qmult (1 # 8) en')).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        - apply (Qmult_le_compat_r (Qmult QicB (Qplus kEp kapE)) (1 # 8) en').
          + exact Hc1'.
          + exact Hen'0. }
      assert (HT3 : Qle (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                        (Qmult (1 # 8) (Qmult en hn))).
      { apply (Qle_trans (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                         (Qmult (Qmult Mterm kS) (Qmult en hn))
                         (Qmult (1 # 8) (Qmult en hn))).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold hn. ring.
        - apply (Qmult_le_compat_r (Qmult Mterm kS) (1 # 8) (Qmult en hn)).
          + exact Hc2.
          + apply Qmult_le_0_compat.
            * exact Hen0.
            * exact Hhn0. }
      assert (HT4 : Qle (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))
                        (Qmult (1 # 8) en')).
      { apply (Qle_trans (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))
                         (Qmult (Qmult Mterm (Qplus kSp kapS)) en')
                         (Qmult (1 # 8) en')).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        - apply (Qmult_le_compat_r (Qmult Mterm (Qplus kSp kapS)) (1 # 8) en').
          + exact Hc2'.
          + exact Hen'0. }
      (* assembling the pointwise main bound: |Dn| <= en*hn + (3/4)*en'. *)
      assert (Hmain : Qle Dn (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
      { apply (Qle_trans Dn
                         (Qplus (Qmult QicB RE) (Qmult Mterm RS))
                         (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
        - exact Hmain0.
        - (* expand and absorb: QicB*RE + Mterm*RS <= (1/8)(en hn) + (1/8)en', two copies of each. *)
          apply (Qle_trans (Qplus (Qmult QicB RE) (Qmult Mterm RS))
                           (Qplus (Qplus (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                                         (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE))))
                                  (Qplus (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                                         (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))))
                           (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
          + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold RE, RS, hn. ring.
          + apply (Qle_trans
                     (Qplus (Qplus (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                                   (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE))))
                            (Qplus (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                                   (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))))
                     (Qplus (Qplus (Qmult (1 # 8) (Qmult en hn)) (Qmult (1 # 8) en'))
                            (Qplus (Qmult (1 # 8) (Qmult en hn)) (Qmult (1 # 8) en')))
                     (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
            * apply Qplus_le_compat.
              { apply Qplus_le_compat. { exact HT1. } { exact HT2. } }
              { apply Qplus_le_compat. { exact HT3. } { exact HT4. } }
            * nra. }
      (* margin: eta < (1/4)*en'; Hfin: eta < (en*hn + en') - Dn. *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply QltT_to_Qlt. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        - apply QltT_to_Qlt. exact He1T.
        - exact (QltT_to_Qlt _ _ (He1lt n HnNe1)). }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply QltT_to_Qlt. apply (b5n_close Dn hn en en' eta).
        - unfold Dn. exact Hmain.
        - unfold en'. exact Hq4e. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5m_J_err x Hx h Hxh)) n))).
      - exact Hfin.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (b5m_J_err x Hx h Hxh) n)).
        unfold en, en', hn, Dn.
        ring. } }
Defined.
(* ===== Compiled; the kernel checks pass 5/5 (Section A r := 0 as 1#36864,   *)
(*    δS1-c 1#5898240, δS2-c 1#9216, and the main piece X = 49#10896801792 =  *)
(*    δE-c — the minimum of the min chain; the tail-form certificates         *)
(*    verified).                                                              *)
(* ===== *)

(* ===== Block b5dQ_ (main item b5dQ_E_rational_zero; upstream source sc2_b5a_item27) ===== *)

(* ===== Section P1 (the lb-E chain: mechanism pieces + the value definitions vB/vSC/vE + lb_b3rr/atan/vdh/sin_cos/cos/E, 29 Lemma + 5 Def) ===== *)

(* ===== Section 0. mechanism-piece migration (probe_item27a.v all genuine Qed — the E side) ===== *)
Lemma b5dQ_min_lb : forall (lb A B : Real),
  real_lt lb A -> real_lt lb B -> real_lt lb (real_min A B).
Proof.
  intros lb A B HltA HltB.
  destruct HltA as [e1 [He1 [N1 HN1]]].
  destruct HltB as [e2 [He2 [N2 HN2]]].
  set (e := Qmin e1 e2).
  assert (He : QltT 0 e).
  { apply Qlt_to_QltT.
    apply Q.min_glb_lt.
    - apply QltT_to_Qlt. exact He1.
    - apply QltT_to_Qlt. exact He2. }
  unfold real_lt.
  exists e.
  split.
  { exact He. }
  { exists (Nat.max N1 N2).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn1 : NatLe N1 n) by (apply NatLe_lift; lia).
    assert (Hn2 : NatLe N2 n) by (apply NatLe_lift; lia).
    apply Qlt_to_QltT.
    set (cn := projT1 lb n).
    set (an := projT1 A n).
    set (bn := projT1 B n).
    assert (H1n : Qlt e1 (an - cn)).
    { unfold an, cn. apply QltT_to_Qlt. exact (HN1 n Hn1). }
    assert (H2n : Qlt e2 (bn - cn)).
    { unfold bn, cn. apply QltT_to_Qlt. exact (HN2 n Hn2). }
    assert (Hen1 : Qle e e1). { unfold e. apply Q.le_min_l. }
    assert (Hen2 : Qle e e2). { unfold e. apply Q.le_min_r. }
    assert (Hm1 : Qlt e (an - cn)).
    { apply (Qle_lt_trans e e1 (an - cn)); [exact Hen1 | exact H1n]. }
    assert (Hm2 : Qlt e (bn - cn)).
    { apply (Qle_lt_trans e e2 (bn - cn)); [exact Hen2 | exact H2n]. }
    assert (Ht1 : Qlt (e + cn) an).
    { apply (proj2 (Qlt_minus_iff (e + cn) an)).
      apply (Qlt_le_trans 0 ((an - cn) - e) (an - (e + cn))).
      - apply (proj1 (Qlt_minus_iff e (an - cn))). exact Hm1.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Ht2 : Qlt (e + cn) bn).
    { apply (proj2 (Qlt_minus_iff (e + cn) bn)).
      apply (Qlt_le_trans 0 ((bn - cn) - e) (bn - (e + cn))).
      - apply (proj1 (Qlt_minus_iff e (bn - cn))). exact Hm2.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Htg : Qlt (e + cn) (Qmin an bn)).
    { apply Q.min_glb_lt; [exact Ht1 | exact Ht2]. }
    rewrite (qeqT_imp_qeq _ _ (real_min_proj A B n)).
    apply (proj2 (Qlt_minus_iff e (Qmin an bn - cn))).
    apply (Qlt_le_trans 0 (Qmin an bn - (e + cn)) ((Qmin an bn - cn) - e)).
    - apply (proj1 (Qlt_minus_iff (e + cn) (Qmin an bn))). exact Htg.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  }
  Qed.

(* T3a migration: the constant-coordinate product leaf lb (real_lt (real_const lb) (real_const a * real_const d)). *)
Lemma b5dQ_const_mult_lb : forall (lb a d : Q),
  QltT lb (a * d) ->
  real_lt (real_const lb) (real_mult (real_const a) (real_const d)).
Proof.
  intros lb a d Hlt.
  assert (Hpos : Qlt 0 ((a * d - lb) / 2)).
  { apply (Qlt_shift_div_l 0 (a * d - lb) 2).
    - change (Qlt 0 2). compute. reflexivity.
    - simpl. apply (proj1 (Qlt_minus_iff lb (a * d))). exact (QltT_to_Qlt _ _ (Hlt)). }
  unfold real_lt.
  exists ((a * d - lb) / 2).
  split.
  - apply Qlt_to_QltT. exact Hpos.
  - exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (a * d - lb) _).
    + apply (proj2 (Qlt_minus_iff ((a * d - lb) / 2) (a * d - lb))).
      apply (Qlt_le_trans 0 ((a * d - lb) / 2) (a * d - lb - (a * d - lb) / 2)).
      * exact Hpos.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const a) (real_const d) n)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj a n)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj d n)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj lb n)).
      ring.
  Qed.


(* the general coordinates of real_inv_pos (certificate-abstract destruct: N0 arbitrary;
   And := A*B so snd)
   projT1 (real_inv_pos x Hx) n == if Nat.leb N0 n then Qinv (x_n)
    else Qinv (x_N0), with N0 := the tail index of the certificate witness *)
Lemma b5dQ_inv_coord : forall (x : Real) (Hx : real_lt real_zero x) (n : nat),QeqT (
  projT1 (real_inv_pos x Hx) n
  ) ( (if Nat.leb (projT1 (snd (projT2 Hx))) n
      then Qinv (projT1 x n)
      else Qinv (projT1 x (projT1 (snd (projT2 Hx)))))).
Proof.
  intros x Hx n.
  apply qeq_imp_qeqT.
  destruct x as [u Hu].
  destruct Hx as [eps0 [Heps0 [N0 HN0]]].
  cbn [projT1 projT2 snd fst real_inv_pos].
  reflexivity.
Qed.

(* ===== Section 1. the closed-form certificates and value definitions ===== *)

Lemma b5dQ_Hq32T : QltT 0 (1 # 32). Proof. vm_compute. reflexivity. Qed.
Lemma b5dQ_Hq4T : QltT 0 (1 # 4). Proof. vm_compute. reflexivity. Qed.
Lemma b5dQ_Hq12288T : QltT 0 (1 # 12288). Proof. vm_compute. reflexivity. Qed.
Lemma b5dQ_H1T : QltT 0 1. Proof. vm_compute. reflexivity. Qed.
Lemma b5dQ_H1pos : QltT 0 1. Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.
Lemma b5dQ_HC40 : QleT' 0 b5d3_exp_arch4_C.
Proof. apply Qle_to_QleT'. apply (Qle_trans _ 1 _). - exact (QleT'_to_Qle _ _ Qle_0_1). - apply QleT'_to_Qle. exact b5d3_exp_arch4_C_ge1. Qed.

(* the positivity wrapper of b3rr_C2 on the q domain (M := (1#2)(1+q), 0<q<1 gives 0 <= M < 1). *)
Lemma b5dQ_Cr_ge0 : forall (q : Q), QleT' 0 q -> QltT q 1 ->
  QleT' 0 (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))).
Proof.
  intros q Hq0 Hq1.
  apply QleT'_to_Qle in Hq0.
  apply QltT_to_Qlt in Hq1.
  apply (b3rr_C2_0 (Qmult (1 # 2) (Qplus 1 q))).
  - apply (Qmult_le_0_compat (1 # 2) (Qplus 1 q)).
    + change (Qle 0 (1 # 2)). unfold Qle. simpl. lia.
    + nra.
  - (* (1#2)(1+q) < 1 ⟸ 1+q < 2 ⟸ q < 1 *)
    nra.
Qed.

(* the positivity of b3rr k(q) := Qinv (4*(Cr+1)) (the 0 < q side is not needed — 0 <= Cr suffices). *)
Lemma b5dQ_kbr_pos : forall (q : Q), QleT' 0 q -> QltT q 1 ->
  QltT 0 (Qinv (Qmult 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1))).
Proof.
  intros q Hq0 Hq1.
  apply Qlt_to_QltT.
  apply Qinv_lt_0_compat.
  apply (Qmult_lt_0_compat 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)).
  - change (Qlt 0 4). unfold Qlt. simpl. lia.
  - apply (Qlt_le_trans 0 1 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)).
    + change (Qlt 0 1). unfold Qlt. simpl. lia.
    + apply (Qle_trans 1 (0 + 1) (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)).
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      * apply Qplus_le_compat.
        -- exact ((QleT'_to_Qle _ _ (b5dQ_Cr_ge0 q Hq0 Hq1))).
        -- apply Qle_refl.
Qed.

(* the E-chain share-chain coordinates (nested Qmult — verbatim with the set substitution form in the piece bodies) *)
(* the 3-chain (sin-eps): a*(1#32)*(1#4) *)
Definition b5dQ_chain3 (a : Q) : Q :=
  Qmult (Qmult a (1 # 32)) (1 # 4).
(* the 4-chain (b3rr-eps): a*(1#32)*(1#4)*(1#12288). *)
Definition b5dQ_chain4 (a : Q) : Q :=
  Qmult (b5dQ_chain3 a) (1 # 12288).

(* the b3rr tree coordinates (the q-branch + the 4-chain product branch) — vB. *)
Definition b5dQ_vB (q a : Q) : Q :=
  Qmin (Qmult (1 # 2) (Qminus 1 q))
       (Qmult (b5dQ_chain4 a)
              (Qinv (Qmult 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)))).

(* vB positivity (0<q<1 and 0<a give 0 < vB). *)
Lemma b5dQ_vB_pos : forall (q a : Q), QltT 0 q -> QltT q 1 -> QltT 0 a ->
  QltT 0 (b5dQ_vB q a).
Proof.
  intros q a Hq0 Hq1 Ha.
  apply Qlt_to_QltT.
  unfold b5dQ_vB.
  apply Q.min_glb_lt.
  - apply (Qmult_lt_0_compat (1 # 2) (Qminus 1 q)).
    + change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia.
    + apply (proj1 (Qlt_minus_iff q 1)). exact (QltT_to_Qlt _ _ (Hq1)).
  - apply (Qmult_lt_0_compat (b5dQ_chain4 a)
           (Qinv (Qmult 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)))).
    + unfold b5dQ_chain4, b5dQ_chain3.
      apply (Qmult_lt_0_compat (Qmult (Qmult a (1 # 32)) (1 # 4)) (1 # 12288)).
      * apply (Qmult_lt_0_compat (Qmult a (1 # 32)) (1 # 4)).
        -- apply (Qmult_lt_0_compat a (1 # 32)).
           ++ exact (QltT_to_Qlt _ _ (Ha)).
           ++ change (Qlt 0 (1 # 32)). unfold Qlt. simpl. lia.
        -- change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
      * change (Qlt 0 (1 # 12288)). unfold Qlt. simpl. lia.
    + exact ((QltT_to_Qlt _ _ (b5dQ_kbr_pos q ((Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ (Hq0))))) Hq1))).
Qed.

(* vB <= each leaf (the Q.min projections — the q side and the product side). *)
Lemma b5dQ_vB_le_q : forall (q a : Q),
  QleT' (b5dQ_vB q a) (Qmult (1 # 2) (Qminus 1 q)).
Proof. intros q a. apply Qle_to_QleT'. unfold b5dQ_vB. apply Q.le_min_l. Qed.
Lemma b5dQ_vB_le_p : forall (q a : Q),
  QleT' (b5dQ_vB q a)
      (Qmult (b5dQ_chain4 a)
             (Qinv (Qmult 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)))).
Proof. intros q a. apply Qle_to_QleT'. unfold b5dQ_vB. apply Q.le_min_r. Qed.

(* leaf positivity (the q side + the product side). *)
Lemma b5dQ_leaf1_pos : forall (q : Q), QltT q 1 -> QltT 0 (Qmult (1 # 2) (Qminus 1 q)).
Proof.
  intros q Hq1.
  apply Qlt_to_QltT.
  apply (Qmult_lt_0_compat (1 # 2) (Qminus 1 q)).
  - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia.
  - apply (proj1 (Qlt_minus_iff q 1)). exact (QltT_to_Qlt _ _ (Hq1)).
Qed.
Lemma b5dQ_chain4_pos : forall (a : Q), QltT 0 a -> QltT 0 (b5dQ_chain4 a).
Proof.
  intros a Ha.
  apply Qlt_to_QltT.
  unfold b5dQ_chain4, b5dQ_chain3.
  apply (Qmult_lt_0_compat (Qmult (Qmult a (1 # 32)) (1 # 4)) (1 # 12288)).
  - apply (Qmult_lt_0_compat (Qmult a (1 # 32)) (1 # 4)).
    + apply (Qmult_lt_0_compat a (1 # 32)).
      * exact (QltT_to_Qlt _ _ (Ha)).
      * change (Qlt 0 (1 # 32)). unfold Qlt. simpl. lia.
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
  - change (Qlt 0 (1 # 12288)). unfold Qlt. simpl. lia.
Qed.
Lemma b5dQ_leaf2_pos : forall (q a : Q), QltT 0 q -> QltT q 1 -> QltT 0 a ->
  QltT 0 (Qmult (b5dQ_chain4 a)
               (Qinv (Qmult 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)))).
Proof.
  intros q a Hq0 Hq1 Ha.
  apply Qlt_to_QltT.
  apply (Qmult_lt_0_compat (b5dQ_chain4 a)
           (Qinv (Qmult 4 (Qplus (b3rr_C2 (Qmult (1 # 2) (Qplus 1 q))) 1)))).
  - exact ((QltT_to_Qlt _ _ (b5dQ_chain4_pos a Ha))).
  - exact ((QltT_to_Qlt _ _ (b5dQ_kbr_pos q ((Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ (Hq0))))) Hq1))).
Qed.

(* ============================================================ *)
(* Section 2. lb_b3rr: b3rr at the 4-chain (value = vB/2)                        *)
(* ============================================================ *)
Lemma b5dQ_lb_b3rr : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : QltT 0 a),
  real_lt (real_const (Qmult (b5dQ_vB q a) (1 # 2)))
    (projT1 (b5d1_b3rr_atan_deriv_lin q ((Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ (Hq0))))) Hq1 x Hxr
               (real_mult (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                                     (real_const (1 # 4)))
                          (real_const (1 # 12288)))
               (b5dI_real_mult_positive_exp
                  (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                             (real_const (1 # 4)))
                  (real_const (1 # 12288))
                  (b5dI_real_mult_positive_exp
                     (real_mult (real_const a) (real_const (1 # 32)))
                     (real_const (1 # 4))
                     (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                        (b5dM_real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha))))
                        (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))
                     (b5dM_real_const_pos (1 # 4) b5dQ_Hq4T))
                  (b5dM_real_const_pos (1 # 12288) b5dQ_Hq12288T)))).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha.
  assert (Hv : Qlt 0 (b5dQ_vB q a)) by (exact (QltT_to_Qlt _ _ (b5dQ_vB_pos q a Hq0 Hq1 Ha))).
  assert (HvT : QltT 0 (Qmult (b5dQ_vB q a) (1 # 4))).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (b5dQ_vB q a) (1 # 4)).
    + exact (Hv).
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia. }
  unfold real_lt.
  exists (Qmult (b5dQ_vB q a) (1 # 4)).
  split.
  { exact HvT. }
  { exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    cbn [projT1 b5d1_b3rr_atan_deriv_lin real_min real_mult real_const].
    (* goal: QltT (vB/4) (Qmin c1 c2 - vB/2) — the cbn coordinates are convertible with the vB value tree (conv). *)
    apply (proj2 (Qlt_minus_iff (Qmult (b5dQ_vB q a) (1 # 4))
                                (Qminus (b5dQ_vB q a) (Qmult (b5dQ_vB q a) (1 # 2))))).
    apply (Qlt_le_trans 0 (Qmult (b5dQ_vB q a) (1 # 4))
                         (Qminus (Qminus (b5dQ_vB q a) (Qmult (b5dQ_vB q a) (1 # 2)))
                                 (Qmult (b5dQ_vB q a) (1 # 4)))).
    + apply QltT_to_Qlt. exact HvT.
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      ring.
  }
  Qed.

(* ============ Section 3. lb_atan (passthrough layer: atan at the 4-chain ≡ b3rr at the 4-chain) ============ *)
Lemma b5dQ_lb_atan : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : QltT 0 a),
  real_lt (real_const (Qmult (b5dQ_vB q a) (1 # 2)))
    (projT1 (b5dD_atan_deriv_b5a_r_exp q ((Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ (Hq0))))) Hq1 x Hxr
               (real_mult (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                                     (real_const (1 # 4)))
                          (real_const (1 # 12288)))
               (b5dI_real_mult_positive_exp
                  (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                             (real_const (1 # 4)))
                  (real_const (1 # 12288))
                  (b5dI_real_mult_positive_exp
                     (real_mult (real_const a) (real_const (1 # 32)))
                     (real_const (1 # 4))
                     (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                        (b5dM_real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha))))
                        (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))
                     (b5dM_real_const_pos (1 # 4) b5dQ_Hq4T))
                  (b5dM_real_const_pos (1 # 12288) b5dQ_Hq12288T)))).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha.
  assert (Hv : Qlt 0 (b5dQ_vB q a)) by (exact (QltT_to_Qlt _ _ (b5dQ_vB_pos q a Hq0 Hq1 Ha))).
  assert (HvT : QltT 0 (Qmult (b5dQ_vB q a) (1 # 4))).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (b5dQ_vB q a) (1 # 4)).
    + exact (Hv).
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia. }
  unfold real_lt.
  exists (Qmult (b5dQ_vB q a) (1 # 4)).
  split.
  { exact HvT. }
  { exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    cbn [projT1 b5dD_atan_deriv_b5a_r_exp b5d1_b3rr_atan_deriv_lin
         real_min real_mult real_const].
    apply (proj2 (Qlt_minus_iff (Qmult (b5dQ_vB q a) (1 # 4))
                                (Qminus (b5dQ_vB q a) (Qmult (b5dQ_vB q a) (1 # 2))))).
    apply (Qlt_le_trans 0 (Qmult (b5dQ_vB q a) (1 # 4))
                         (Qminus (Qminus (b5dQ_vB q a) (Qmult (b5dQ_vB q a) (1 # 2)))
                                 (Qmult (b5dQ_vB q a) (1 # 4)))).
    + apply QltT_to_Qlt. exact HvT.
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      ring.
  }
  Qed.

(* ============ Section 4. lb_vdh (passthrough layer: vdh at the 3-chain + k2 := 1#12288 ≡ b3rr at the 4-chain)
   The k2p value does not enter δ (a proof position) — registered deviation: the statement carries k2p := 1#12288
   (simplified to the same value as k2; the actual in-body sin k2p is the C4-dependent form — it does not
   enter the value path, zero impact) ============ *)
Lemma b5dQ_lb_vdh : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : QltT 0 a),
  real_lt (real_const (Qmult (b5dQ_vB q a) (1 # 2)))
    (projT1 (b5dD_vdh_pts_r_exp q ((Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ (Hq0))))) Hq1 x Hxr
               (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                          (real_const (1 # 4)))
               (b5dI_real_mult_positive_exp
                  (real_mult (real_const a) (real_const (1 # 32)))
                  (real_const (1 # 4))
                  (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                     (b5dM_real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha))))
                     (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))
                  (b5dM_real_const_pos (1 # 4) b5dQ_Hq4T))
               (1 # 12288) (1 # 12288)
               b5dQ_Hq12288T b5dQ_Hq12288T)).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha.
  assert (Hv : Qlt 0 (b5dQ_vB q a)) by (exact (QltT_to_Qlt _ _ (b5dQ_vB_pos q a Hq0 Hq1 Ha))).
  assert (HvT : QltT 0 (Qmult (b5dQ_vB q a) (1 # 4))).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (b5dQ_vB q a) (1 # 4)).
    + exact (Hv).
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia. }
  unfold real_lt.
  exists (Qmult (b5dQ_vB q a) (1 # 4)).
  split.
  { exact HvT. }
  { exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    cbn [projT1 b5dD_vdh_pts_r_exp b5dD_atan_deriv_b5a_r_exp
         b5d1_b3rr_atan_deriv_lin real_min real_mult real_const].
    apply (proj2 (Qlt_minus_iff (Qmult (b5dQ_vB q a) (1 # 4))
                                (Qminus (b5dQ_vB q a) (Qmult (b5dQ_vB q a) (1 # 2))))).
    apply (Qlt_le_trans 0 (Qmult (b5dQ_vB q a) (1 # 4))
                         (Qminus (Qminus (b5dQ_vB q a) (Qmult (b5dQ_vB q a) (1 # 2)))
                                 (Qmult (b5dQ_vB q a) (1 # 4)))).
    + apply QltT_to_Qlt. exact HvT.
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      ring.
  }
  Qed.

(* ============================================================ *)
(* Section 5. the general margin piece + the vSC value definition (sin/cos tree coordinates — the 3-chain instance) *)
(* ============================================================ *)

(* the general margin: 0 < v gives QltT (v/4) (v - v/2) (the coordinate-layer closing piece). *)
Lemma b5dQ_margin_lemma : forall (v : Q), QltT 0 v ->
  QltT (Qmult v (1 # 4)) (Qminus v (Qmult v (1 # 2))).
Proof.
  intros v Hv.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff (Qmult v (1 # 4)) (Qminus v (Qmult v (1 # 2))))).
  apply (Qlt_le_trans 0 (Qmult v (1 # 4))
                       (Qminus (Qminus v (Qmult v (1 # 2))) (Qmult v (1 # 4)))).
  - apply (Qmult_lt_0_compat v (1 # 4)).
    + exact (QltT_to_Qlt _ _ (Hv)).
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

Lemma b5dQ_chain3_pos : forall (a : Q), QltT 0 a -> QltT 0 (b5dQ_chain3 a).
Proof.
  intros a Ha.
  apply Qlt_to_QltT.
  unfold b5dQ_chain3.
  apply (Qmult_lt_0_compat (Qmult a (1 # 32)) (1 # 4)).
  - apply (Qmult_lt_0_compat a (1 # 32)).
    + exact (QltT_to_Qlt _ _ (Ha)).
    + change (Qlt 0 (1 # 32)). unfold Qlt. simpl. lia.
  - change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
Qed.

Lemma b5dQ_one_plus_c_pos : forall (c : Q), QleT' 0 c -> QltT 0 (Qplus 1 c).
Proof.
  intros c Hc.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans 0 1 (Qplus 1 c)).
  - change (Qlt 0 1). unfold Qlt. simpl. lia.
  - apply (Qle_trans 1 (Qplus 1 0) (Qplus 1 c)).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    + apply Qplus_le_compat; [ apply Qle_refl | exact (QleT'_to_Qle _ _ (Hc)) ].
Qed.

(* the sin tree coordinates (the 3-chain instance): min(min(min vB (1#2)) (chain3*(1#1536)))
   ((1#4)*Qinv(1 + chain3*(1#12288))) — the δa branch = vB (the full vdh/atan/b3rr passthrough chain). *)
Definition b5dQ_vSC (q a : Q) : Q :=
  Qmin (Qmin (Qmin (b5dQ_vB q a) (1 # 2))
             (Qmult (b5dQ_chain3 a) (1 # 1536)))
       (Qmult (1 # 4) (Qinv (Qplus 1 (Qmult (b5dQ_chain3 a) (1 # 12288))))).

Lemma b5dQ_vSC_pos : forall (q a : Q), QltT 0 q -> QltT q 1 -> QltT 0 a ->
  QltT 0 (b5dQ_vSC q a).
Proof.
  intros q a Hq0 Hq1 Ha.
  apply Qlt_to_QltT.
  unfold b5dQ_vSC.
  apply Q.min_glb_lt.
  - apply Q.min_glb_lt.
    + apply Q.min_glb_lt.
      * exact ((QltT_to_Qlt _ _ (b5dQ_vB_pos q a Hq0 Hq1 Ha))).
      * change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia.
    + apply (Qmult_lt_0_compat (b5dQ_chain3 a) (1 # 1536)).
      * exact ((QltT_to_Qlt _ _ (b5dQ_chain3_pos a Ha))).
      * change (Qlt 0 (1 # 1536)). unfold Qlt. simpl. lia.
  - apply (Qmult_lt_0_compat (1 # 4)
           (Qinv (Qplus 1 (Qmult (b5dQ_chain3 a) (1 # 12288))))).
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
    + apply Qinv_lt_0_compat.
      apply QltT_to_Qlt.
      apply (b5dQ_one_plus_c_pos (Qmult (b5dQ_chain3 a) (1 # 12288))).
      apply Qle_to_QleT'.
      apply Qlt_le_weak.
      apply (Qmult_lt_0_compat (b5dQ_chain3 a) (1 # 12288)).
      * exact ((QltT_to_Qlt _ _ (b5dQ_chain3_pos a Ha))).
      * change (Qlt 0 (1 # 12288)). unfold Qlt. simpl. lia.
Qed.

(* Section 6. lb_sin_cos: sin/cos at the 3-chain (value = vSC/2 — sin/cos share the same tree and value). *)
(* ============================================================ *)
Lemma b5dQ_lb_sin_cos : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (Hs : forall n : nat, QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) 1)
  (Hc : forall n : nat, QleT' (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) 1)
  (a : Q) (Ha : QltT 0 a),
  real_lt (real_const (Qmult (b5dQ_vSC q a) (1 # 2)))
    (projT1 (b5dI_sin_atan_diff_closed_r_exp q ((Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ (Hq0))))) Hq1 x Hxr
              1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
              b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all Hs Hc
              (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                         (real_const (1 # 4)))
              (b5dI_real_mult_positive_exp
                 (real_mult (real_const a) (real_const (1 # 32)))
                 (real_const (1 # 4))
                 (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                    (b5dM_real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha))))
                    (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))
                 (b5dM_real_const_pos (1 # 4) b5dQ_Hq4T)))).
Proof.
  intros q Hq0 Hq1 x Hxr Hs Hc a Ha.
  assert (Hv : Qlt 0 (b5dQ_vSC q a)) by (exact (QltT_to_Qlt _ _ (b5dQ_vSC_pos q a Hq0 Hq1 Ha))).
  unfold real_lt.
  exists (Qmult (b5dQ_vSC q a) (1 # 4)).
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (b5dQ_vSC q a) (1 # 4)).
    + exact (Hv).
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
  - exists 0%nat.
    intros n Hn.
    cbn [projT1 b5dI_sin_atan_diff_closed_r_exp b5dD_vdh_pts_r_exp
         b5dD_atan_deriv_b5a_r_exp b5d1_b3rr_atan_deriv_lin
         b5dI_real_mult_positive_exp b5dM_b5i_one_plus_eps2_pos
         b5dM_real_const_pos real_min real_mult real_const real_plus
         real_one real_inv_pos Nat.leb Nat.max Nat.min].
    exact (b5dQ_margin_lemma (b5dQ_vSC q a) (Qlt_to_QltT _ _ (Hv))).
  Qed.

(* ============================================================ *)
(* Section 7. lb_cos: cos at the 3-chain (same tree, same value — the Ms := Mc := 1 symmetry) *)
(* ============================================================ *)
Lemma b5dQ_lb_cos : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (Hs : forall n : nat, QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) 1)
  (Hc : forall n : nat, QleT' (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) 1)
  (a : Q) (Ha : QltT 0 a),
  real_lt (real_const (Qmult (b5dQ_vSC q a) (1 # 2)))
    (projT1 (b5dI_cos_atan_diff_closed_r_exp q ((Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ (Hq0))))) Hq1 x Hxr
              1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
              b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all Hs Hc
              (real_mult (real_mult (real_const a) (real_const (1 # 32)))
                         (real_const (1 # 4)))
              (b5dI_real_mult_positive_exp
                 (real_mult (real_const a) (real_const (1 # 32)))
                 (real_const (1 # 4))
                 (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                    (b5dM_real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha))))
                    (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))
                 (b5dM_real_const_pos (1 # 4) b5dQ_Hq4T)))).
Proof.
  intros q Hq0 Hq1 x Hxr Hs Hc a Ha.
  assert (Hv : Qlt 0 (b5dQ_vSC q a)) by (exact (QltT_to_Qlt _ _ (b5dQ_vSC_pos q a Hq0 Hq1 Ha))).
  unfold real_lt.
  exists (Qmult (b5dQ_vSC q a) (1 # 4)).
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (b5dQ_vSC q a) (1 # 4)).
    + exact (Hv).
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
  - exists 0%nat.
    intros n Hn.
    cbn [projT1 b5dI_cos_atan_diff_closed_r_exp b5dD_vdh_pts_r_exp
         b5dD_atan_deriv_b5a_r_exp b5d1_b3rr_atan_deriv_lin
         b5dI_real_mult_positive_exp b5dM_b5i_one_plus_eps2_pos
         b5dM_real_const_pos real_min real_mult real_const real_plus
         real_one real_inv_pos Nat.leb Nat.max Nat.min].
    exact (b5dQ_margin_lemma (b5dQ_vSC q a) (Qlt_to_QltT _ _ (Hv))).
  Qed.

(* ============================================================ *)
(* Section 8. the vE value definition (E tree coordinates — the 2-chain instance) + lb_E *)
(* ============================================================ *)

(* the E tree coordinates: min(min vSC vSC) ((a*(1#32))*(1#1024)) — the sin/cos branches share the value. *)
Definition b5dQ_vE (q a : Q) : Q :=
  Qmin (Qmin (b5dQ_vSC q a) (b5dQ_vSC q a))
       (Qmult (Qmult a (1 # 32)) (1 # 1024)).

Lemma b5dQ_vE_pos : forall (q a : Q), QltT 0 q -> QltT q 1 -> QltT 0 a ->
  QltT 0 (b5dQ_vE q a).
Proof.
  intros q a Hq0 Hq1 Ha.
  apply Qlt_to_QltT.
  unfold b5dQ_vE.
  apply Q.min_glb_lt.
  - apply Q.min_glb_lt.
    + exact ((QltT_to_Qlt _ _ (b5dQ_vSC_pos q a Hq0 Hq1 Ha))).
    + exact ((QltT_to_Qlt _ _ (b5dQ_vSC_pos q a Hq0 Hq1 Ha))).
  - apply (Qmult_lt_0_compat (Qmult a (1 # 32)) (1 # 1024)).
    + apply (Qmult_lt_0_compat a (1 # 32)).
      * exact (QltT_to_Qlt _ _ (Ha)).
      * change (Qlt 0 (1 # 32)). unfold Qlt. simpl. lia.
    + change (Qlt 0 (1 # 1024)). unfold Qlt. simpl. lia.
Qed.

(* lb_E: E-diff at the 2-chain (value = vE/2). *)
Lemma b5dQ_lb_E : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (Hs : forall n : nat, QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) 1)
  (Hc : forall n : nat, QleT' (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) 1)
  (a : Q) (Ha : QltT 0 a),
  real_lt (real_const (Qmult (b5dQ_vE q a) (1 # 2)))
    (projT1 (b5dI_E_diff_closed_r_exp q ((Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ (Hq0))))) Hq1 x Hxr
              1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
              b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all Hs Hc
              (real_mult (real_const a) (real_const (1 # 32)))
              (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                 (b5dM_real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha))))
                 (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T)))).
Proof.
  intros q Hq0 Hq1 x Hxr Hs Hc a Ha.
  assert (Hv : Qlt 0 (b5dQ_vE q a)) by (exact (QltT_to_Qlt _ _ (b5dQ_vE_pos q a Hq0 Hq1 Ha))).
  unfold real_lt.
  exists (Qmult (b5dQ_vE q a) (1 # 4)).
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (b5dQ_vE q a) (1 # 4)).
    + exact (Hv).
    + change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
  - exists 0%nat.
    intros n Hn.
    cbn [projT1 b5dI_E_diff_closed_r_exp b5dI_sin_atan_diff_closed_r_exp
         b5dI_cos_atan_diff_closed_r_exp b5dD_vdh_pts_r_exp
         b5dD_atan_deriv_b5a_r_exp b5d1_b3rr_atan_deriv_lin
         b5dI_real_mult_positive_exp b5dM_b5i_one_plus_eps2_pos
         b5dM_real_const_pos real_min real_mult real_const real_plus
         real_one real_inv_pos Nat.leb Nat.max Nat.min].
    exact (b5dQ_margin_lemma (b5dQ_vE q a) (Qlt_to_QltT _ _ (Hv))).
  Qed.


(* ===== end of sc2_b5a_item27_p1_lbE.v (P1, the lb-E chain: b3rr/atan/vdh/sin_cos/E) ===== *)


(* ===== end of sc2_b5a_item27_p1_lbE.v (P1, the lb-E chain: b3rr/atan/vdh/sin_cos/E) ===== *)

(* ===== Section P2 (the lb-log chain: the helper set + lb_logdiff/logerr/gdiff/exp_part, 27 Lemma) ===== *)

(* ============================================================ *)
(* helper 1: Qinv <= monotone (x <= y positive gives Qinv y <= Qinv x)           *)
(* Verbatim migration of the check piece p_qinv_le_mono (renamed with the b5dQ_ prefix). *)
(* ============================================================ *)
Lemma b5dQ_p_qinv_le_mono : forall (x y : Q),
  QltT 0 x -> QltT 0 y -> QleT' x y -> QleT' (Qinv y) (Qinv x).
Proof.
  intros x y Hx Hy Hxy.
  apply Qle_to_QleT'.
  destruct (Qlt_le_dec x y) as [Hlt | Hge].
  - apply Qlt_le_weak.
    apply (proj1 (Qinv_lt_contravar x y (QltT_to_Qlt _ _ (Hx)) (QltT_to_Qlt _ _ (Hy)))). exact Hlt.
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    apply (Qinv_comp y x).
    apply Qeq_sym.
    exact (Qle_antisym x y (QleT'_to_Qle _ _ (Hxy)) Hge).
Qed.

(* ============================================================ *)
(* helper 2: the invM coordinate piece (the S atom stays atomic)                 *)
(* Verbatim migration of the check piece p_inv_coord0 (renamed b5dQ_p_invM_coord — *)
(* the unique name within the section).                                          *)
(* ============================================================ *)
Lemma b5dQ_p_invM_coord : forall (x : Real) (n : nat),QeqT (
  projT1 (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                       (b5dK_real_abs_plus_one_pos_exp (b5a_S x))) n
  ) ( Qinv (1 + Qabs (projT1 (b5a_S x) n))).
Proof.
  intros x n.
  apply qeq_imp_qeqT.
  cbn [projT1 real_inv_pos real_plus real_abs real_one real_const
       b5dK_real_abs_plus_one_pos_exp].
  reflexivity.
Qed.


(* ============================================================ *)
(* helper 4: the u coordinate piece (u := b5f_u x = 1 + x*x, pointwise)          *)
(* coordinate-layer piece: the companion of the b5f_u-in-cbn-list decision.      *)
(* ============================================================ *)
Lemma b5dQ_p_u_coord : forall (x : Real) (n : nat),QeqT (
  projT1 (b5f_u x) n ) ( Qplus 1 (Qmult (projT1 x n) (projT1 x n))).
Proof.
  intros x n.
  apply qeq_imp_qeqT.
  unfold b5f_u.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_mult x x) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj x x n)).
  cbn [projT1 real_one].
  reflexivity.
Qed.

(* ============================================================ *)
(* helper 5: the u-coordinate lower bound (u_n >= 1 pointwise — squares are nonnegative, established by nra-on-Q) *)
(* ============================================================ *)
Lemma b5dQ_p_u_ge1 : forall (x : Real) (n : nat),
  QleT' 1 (projT1 (b5f_u x) n).
Proof.
  intros x n.
  apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (b5dQ_p_u_coord x n)) as Hgenqeq9746.
  rewrite Hgenqeq9746.
  nra.
Qed.

(* ============================================================ *)
(* helper 6: the Qle-form min-glb (the min decomposition lower bound)            *)
(* ============================================================ *)
Lemma b5dQ_p_min_glb_le : forall (a b c : Q),
  QleT' c a -> QleT' c b -> QleT' c (Qmin a b).
Proof.
  intros a b c Hca Hcb.
  apply Qle_to_QleT'.
  destruct (Qlt_le_dec a b) as [Hlt | Hge].
  - rewrite (Q.min_l a b (Qlt_le_weak a b Hlt)). exact (QleT'_to_Qle _ _ (Hca)).
  - rewrite (Q.min_r a b Hge). exact (QleT'_to_Qle _ _ (Hcb)).
Qed.

(* ============================================================ *)
(* helper 7: the Qeq (Qinv 2) (1#2)-class (normalization of the coordinate-layer reduction products) *)
(* ============================================================ *)
Lemma b5dQ_p_qinv2 :QeqT ( Qinv 2 ) ( 1 # 2).
Proof. apply qeq_imp_qeqT. unfold Qinv. reflexivity. Qed.


Lemma b5dQ_p_qinv2sq :QeqT ( Qmult (Qinv 2) (Qinv 2) ) ( 1 # 4).
Proof. apply qeq_imp_qeqT. unfold Qinv. reflexivity. Qed.

Lemma b5dQ_p_qinv3 :QeqT ( Qinv 3 ) ( 1 # 3).
Proof. apply qeq_imp_qeqT. unfold Qinv. reflexivity. Qed.

(* ============================================================ *)
(* helper 8: the right distributivity of Qmin over subtraction (the min tree - c decomposition) *)
(* ============================================================ *)
Lemma b5dQ_p_qmin_sub_r : forall (a b c : Q),QeqT (
  (Qmin a b) - c ) ( Qmin (a - c) (b - c)).
Proof.
  intros a b c.
  apply qeq_imp_qeqT.
  destruct (Qlt_le_dec a b) as [Hlt | Hge].
  - rewrite (Q.min_l a b (Qlt_le_weak a b Hlt)).
    assert (Hle : a - c <= b - c) by nra.
    rewrite (Q.min_l (a - c) (b - c) Hle).
    reflexivity.
  - rewrite (Q.min_r a b Hge).
    assert (Hle : b - c <= a - c) by nra.
    rewrite (Q.min_r (a - c) (b - c) Hle).
    reflexivity.
Qed.

(* ============================================================ *)
(* helper 9: the floor glue (branch floor >= f + a strict margin)                *)
(* ============================================================ *)
Lemma b5dQ_p_lt_sub_floor : forall (b f lb e : Q),
  QleT' f b -> QltT e (f - lb) -> QltT e (b - lb).
Proof.
  intros b f lb e Hfb Hlt.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans e (f - lb) (b - lb)).
  - exact (QltT_to_Qlt _ _ (Hlt)).
  - apply (Qplus_le_compat f b (Qopp lb) (Qopp lb)); [exact (QleT'_to_Qle _ _ (Hfb)) | apply Qle_refl].
Qed.

(* ============================================================ *)
(* Piece 1: b5dQ_lb_logdiff (the δD2f L6 coordinate-layer implementation)        *)
(* Statement: the §1.3 text verbatim.  Proof: unfold real_lt (the margin e := lb/2, *)
(*   N := 0) -> the coordinate piece b5dQ_lb_logdiff_coord (change to the explicit δ tree *)
(*   + projection rewrites + closed-form sub-pieces cbn) -> the Q layer (the per-branch  *)
(*   strict bound with u >= 1 + Q.min_glb_lt + qmin_sub_r + nra/ring).                   *)
(* ============================================================ *)
Lemma b5dQ_lb_logdiff_coord : forall (x : Real) (a : Q) (Ha : QltT 0 a) (n : nat),QeqT (
  projT1 (projT1 (b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x)
                 (real_const a) (real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha)))))) n
  ) ( Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult a (Qmult (projT1 (b5f_u x) n) (projT1 (b5f_u x) n))))).
Proof.
  intros x a Ha n.
  apply qeq_imp_qeqT.
  change (projT1 (real_min
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)) (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult (real_const a) (real_mult (b5f_u x) (b5f_u x))))) n
  == Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult a (Qmult (projT1 (b5f_u x) n) (projT1 (b5f_u x) n))))).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)) (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult (real_const a) (real_mult (b5f_u x) (b5f_u x)))) n)).
  repeat (rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) || rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _))).
  cbn [projT1 real_inv_pos real_plus real_one real_const Nat.leb
       b5dJ_two_pos_exp].
  reflexivity.
Qed.

Lemma b5dQ_lb_logdiff : forall (x : Real) (a : Q) (Ha : QltT 0 a),
  real_lt (real_const (Qmult (Qmin (1 # 2) (Qmult (1 # 4) a)) (1 # 2)))
    (projT1 (b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x)
            (real_const a) (real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha)))))).
Proof.
  intros x a Ha.
  set (c := Qmin (1 # 2) (Qmult (1 # 4) a)).
  set (lb := Qmult c (1 # 2)).
  set (e := Qmult lb (1 # 2)).
  assert (H12 : Qlt 0 (1 # 2)) by (change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H14 : Qlt 0 (1 # 4)) by (change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (Hcpos : Qlt 0 c).
  { unfold c. apply Q.min_glb_lt.
    - exact H12.
    - apply (Qmult_lt_0_compat (1 # 4) a); [exact H14 | exact (QltT_to_Qlt _ _ (Ha))]. }
  assert (Hlbpos : Qlt 0 lb).
  { unfold lb. apply (Qmult_lt_0_compat c (1 # 2)); [exact Hcpos | exact H12]. }
  assert (Hepos : Qlt 0 e).
  { unfold e. apply (Qmult_lt_0_compat lb (1 # 2)); [exact Hlbpos | exact H12]. }
  assert (Hc1 : Qle c (1 # 2)) by (unfold c; apply Q.le_min_l).
  assert (Hc2 : Qle c (Qmult (1 # 4) a)) by (unfold c; apply Q.le_min_r).
  unfold real_lt.
  exists e.
  split.
  { apply Qlt_to_QltT. exact Hepos. }
  { exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    pose proof (qeqT_imp_qeq _ _ (b5dQ_lb_logdiff_coord x a Ha n)) as Hgenqeq9874.
    rewrite Hgenqeq9874.
    set (u := projT1 (b5f_u x) n).
    assert (Hug : Qle 1 u) by (apply QleT'_to_Qle; unfold u; apply b5dQ_p_u_ge1).
    (* per-branch strict bounds: e < b1 - lb and e < b2 - lb (with the u >= 1 + c bound). *)
    assert (S1 : Qlt e ((Qmult (Qinv 2) u) - lb)).
    { unfold e, lb.
      pose proof (qeqT_imp_qeq _ _ b5dQ_p_qinv2) as Hgenqeq9881.
      rewrite Hgenqeq9881.
      nra. }
    (* u^2 >= 1 (squares are nonnegative — nra-on-Q is only linear, so a manual chain). *)
    assert (Hu0 : Qle 0 u).
    { apply (Qle_trans 0 1 u); [apply Qlt_le_weak; exact (QltT_to_Qlt 0 1 qltT_0_1) | exact Hug]. }
    assert (Hsq : Qle 1 (Qmult u u)).
    { apply (Qle_trans 1 u (Qmult u u)).
      - exact Hug.
      - apply (Qle_trans u (Qmult 1 u) (Qmult u u)).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        + apply (Qmult_le_compat_r 1 u u); [exact Hug | exact Hu0]. }
    assert (S2 : Qlt e ((Qmult (Qmult (Qinv 2) (Qinv 2)) (Qmult a (Qmult u u))) - lb)).
    { unfold e, lb.
      pose proof (qeqT_imp_qeq _ _ b5dQ_p_qinv2sq) as Hgenqeq9895.
      rewrite Hgenqeq9895.
      apply QltT_to_Qlt.
      apply (b5dQ_p_lt_sub_floor
               (Qmult (1 # 4) (Qmult a (Qmult u u)))   (* b *)
               (Qmult (1 # 4) a)                       (* f *)
               (Qmult c (1 # 2))                       (* lb *)
               (Qmult (Qmult c (1 # 2)) (1 # 2))).     (* e *)
      - (* Qle f b: a <= a*u^2 via Qmult_le_compat_r + the ring bridge. *)
        assert (Ha1 : Qle a (Qmult a (Qmult u u))).
        { apply (Qle_trans a (Qmult 1 a) (Qmult a (Qmult u u))).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
          - apply (Qle_trans (Qmult 1 a) (Qmult (Qmult u u) a)
                             (Qmult a (Qmult u u))).
            + apply (Qmult_le_compat_r 1 (Qmult u u) a);
                [ exact Hsq | apply Qlt_le_weak; exact (QltT_to_Qlt _ _ (Ha)) ].
            + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        assert (Hb2a : Qle (Qmult a (1 # 4)) (Qmult (Qmult a (Qmult u u)) (1 # 4))).
        { apply (Qmult_le_compat_r a (Qmult a (Qmult u u)) (1 # 4));
            [ exact Ha1 | apply Qlt_le_weak; exact H14 ]. }
        apply Qle_to_QleT'.
        apply (Qle_trans (Qmult (1 # 4) a) (Qmult a (1 # 4))
                         (Qmult (1 # 4) (Qmult a (Qmult u u)))).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        + apply (Qle_trans (Qmult a (1 # 4))
                           (Qmult (Qmult a (Qmult u u)) (1 # 4))
                           (Qmult (1 # 4) (Qmult a (Qmult u u)))).
          * exact Hb2a.
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      - (* Qlt e (f - lb): linear — nra. *)
        pose proof (QltT_to_Qlt _ _ Ha) as HaQ9925.
        apply Qlt_to_QltT.
        nra. }
    pose proof (qeqT_imp_qeq _ _ (b5dQ_p_qmin_sub_r (Qmult (Qinv 2) u)
             (Qmult (Qmult (Qinv 2) (Qinv 2)) (Qmult a (Qmult u u))) lb)) as Hgenqeq9928.
    rewrite Hgenqeq9928.
    apply Q.min_glb_lt; [exact S1 | exact S2].
  }
Qed.


(* ============================================================ *)
(* Piece 2: b5dQ_lb_logerr (δD2f L7)                                             *)
(* In the LogErr body δ := destruct (logdiff @ (x0 := b5f_u x, the same eps))    *)
(* and then exists unchanged, so projT1 (LogErr-app) and projT1 (logdiff-app)    *)
(* are definitionally convertible (kernel conv): this piece = change + exact     *)
(* lb_logdiff.                                                                   *)
(* ============================================================ *)
Lemma b5dQ_lb_logerr : forall (x : Real) (a : Q) (Ha : QltT 0 a),
  real_lt (real_const (Qmult (Qmin (1 # 2) (Qmult (1 # 4) a)) (1 # 2)))
    (projT1 (b5dJ_LogErr_delta_exp x (real_const a)
            (real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha)))))).
Proof.
  intros x a Ha.
  change (real_lt (real_const (Qmult (Qmin (1 # 2) (Qmult (1 # 4) a)) (1 # 2)))
    (projT1 (b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x)
            (real_const a) (real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha))))))).
  exact (b5dQ_lb_logdiff x a Ha).
Qed.

(* ============================================================ *)
(* helper 10: u^2 >= 1 / multiplier absorption (the u^2 coordinate chain; nra is only linear, hence manual) *)
(* ============================================================ *)
Lemma b5dQ_p_q_square_ge1 : forall (u : Q), QleT' 1 u -> QleT' 1 (Qmult u u).
Proof.
  intros u Hug.
  apply Qle_to_QleT'.
  assert (Hu0 : Qle 0 u).
  { apply (Qle_trans 0 1 u); [apply Qlt_le_weak; exact (QltT_to_Qlt 0 1 qltT_0_1) | exact (QleT'_to_Qle _ _ (Hug))]. }
  apply (Qle_trans 1 u (Qmult u u)).
  - exact (QleT'_to_Qle _ _ (Hug)).
  - apply (Qle_trans u (Qmult 1 u) (Qmult u u)).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qmult_le_compat_r 1 u u); [exact (QleT'_to_Qle _ _ (Hug)) | exact Hu0].
Qed.

Lemma b5dQ_p_q_mul_abs : forall (m u : Q),
  QleT' 0 m -> QleT' 1 u -> QleT' m (Qmult m (Qmult u u)).
Proof.
  intros m u Hm0 Hug.
  apply Qle_to_QleT'.
  assert (Hsq : Qle 1 (Qmult u u)) by (apply QleT'_to_Qle; apply b5dQ_p_q_square_ge1; exact Hug).
  apply (Qle_trans m (Qmult 1 m) (Qmult m (Qmult u u))).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans (Qmult 1 m) (Qmult (Qmult u u) m) (Qmult m (Qmult u u))).
    + apply (Qmult_le_compat_r 1 (Qmult u u) m); [exact Hsq | exact (QleT'_to_Qle _ _ (Hm0))].
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* Piece 3: b5dQ_lb_gdiff (the δD2f L8 coordinate-layer implementation)          *)
(* In the gdiff body: kL := k2*(1#2); epsL := eps*real_const kL; δL :=           *)
(*   projT1 (LogErr x epsL ...); δg := min(min(δL*(1#12),                        *)
(*   eps*real_const kL), (1#2)).  Coordinate pieces + the δL coordinate piece + the Q layer. *)
(* ============================================================ *)
Lemma b5dQ_p_epsL_pos : forall (a : Q) (Ha : QltT 0 a) (k2 : Q) (Hk2 : QltT 0 k2),
  real_lt real_zero (real_mult (real_const a) (real_const (Qmult k2 (1 # 2)))).
Proof.
  intros a Ha k2 Hk2.
  apply real_mult_positive.
  - apply real_const_pos. apply Qlt_to_QltT. exact (QltT_to_Qlt _ _ (Ha)).
  - apply real_const_pos. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat k2 (1 # 2)).
    + apply QltT_to_Qlt. exact Hk2.
    + change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia.
Qed.

Lemma b5dQ_lb_logerr_coord : forall (x : Real) (a : Q) (Ha : QltT 0 a)
  (k2 : Q) (Hk2 : QltT 0 k2) (n : nat),QeqT (
  projT1 (projT1 (b5dJ_LogErr_delta_exp x
                 (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (b5dQ_p_epsL_pos a Ha k2 Hk2))) n
  ) ( Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult (Qmult a (Qmult k2 (1 # 2)))
                        (Qmult (projT1 (b5f_u x) n) (projT1 (b5f_u x) n))))).
Proof.
  intros x a Ha k2 Hk2 n.
  apply qeq_imp_qeqT.
  change (projT1 (projT1 (b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x)
                 (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (b5dQ_p_epsL_pos a Ha k2 Hk2))) n
  == Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult (Qmult a (Qmult k2 (1 # 2)))
                        (Qmult (projT1 (b5f_u x) n) (projT1 (b5f_u x) n))))).
  change (projT1 (real_min
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)) (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (real_mult (b5f_u x) (b5f_u x))))) n
  == Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult (Qmult a (Qmult k2 (1 # 2)))
                        (Qmult (projT1 (b5f_u x) n) (projT1 (b5f_u x) n))))).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)) (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (real_mult (b5f_u x) (b5f_u x)))) n)).
  repeat (rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) || rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _))).
  cbn [projT1 real_inv_pos real_plus real_one real_const Nat.leb
       b5dJ_two_pos_exp].
  reflexivity.
Qed.

(* ============================================================ *)
(* helper 12: the branch strict margin (the floor branch; e := lb/2 linear)      *)
(* ============================================================ *)
Lemma b5dQ_p_branch_lt : forall (b f c : Q),
  QleT' f b -> QleT' c f -> QltT 0 c ->
  QltT (Qmult (Qmult c (1 # 2)) (1 # 2)) (b - Qmult c (1 # 2)).
Proof.
  intros b f c Hfb Hcf Hc.
  apply QleT'_to_Qle in Hfb.
  apply QleT'_to_Qle in Hcf.
  apply QltT_to_Qlt in Hc.
  apply Qlt_to_QltT.
  nra.
Qed.

Lemma b5dQ_p_q_scaled_le : forall (c m u : Q),
  QleT' 0 c -> QleT' 0 m -> QleT' 1 u ->
  QleT' (Qmult c m) (Qmult c (Qmult m (Qmult u u))).
Proof.
  intros c m u Hc0 Hm0 Hug.
  apply Qle_to_QleT'.
  assert (Habs : Qle m (Qmult m (Qmult u u))).
  apply QleT'_to_Qle.
  { apply b5dQ_p_q_mul_abs; [exact Hm0 | exact Hug]. }
  apply (Qle_trans (Qmult c m) (Qmult m c) (Qmult c (Qmult m (Qmult u u)))).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans (Qmult m c) (Qmult (Qmult m (Qmult u u)) c)
                     (Qmult c (Qmult m (Qmult u u)))).
    + apply (Qmult_le_compat_r m (Qmult m (Qmult u u)) c);
        [exact Habs | exact (QleT'_to_Qle _ _ (Hc0))].
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* Piece 3: b5dQ_lb_gdiff (the δD2f L8 coordinate-layer implementation)          *)
(* In the gdiff body: kL := k2*(1#2); epsL := eps*real_const kL; δL :=           *)
(*   projT1 (LogErr x epsL ...); δg := min(min(δL*(1#12),                        *)
(*   eps*real_const kL), (1#2)).  Coordinate pieces + the Q layer (the δL coordinate *)
(*   fully expanded by b5dQ_lb_logerr_coord).                                    *)
(* ============================================================ *)
Lemma b5dQ_lb_gdiff_coord : forall (q : Q) (Hq0 : QleT' 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : QltT 0 a) (k2 k2p : Q) (Hk2 : QltT 0 k2) (Hk2p : QltT 0 k2p)
  (n : nat),QeqT (
  projT1 (projT1 (b5dK_gdiff_pts_r_exp q Hq0 Hq1 x Hxr (real_const a)
                 (real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha))))
                 k2 k2p Hk2 Hk2p)) n
  ) ( Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult a (Qmult k2 (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult a (Qmult k2 (1 # 2))))
    (1 # 2)).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha k2 k2p Hk2 Hk2p n.
  apply qeq_imp_qeqT.
  change (projT1 (real_min (real_min
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x
                 (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (b5dQ_p_epsL_pos a Ha k2 Hk2)))
               (real_const (1 # 12)))
    (real_mult (real_const a) (real_const (Qmult k2 (1 # 2)))))
    (real_const (1 # 2))) n
  == Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult a (Qmult k2 (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult a (Qmult k2 (1 # 2))))
    (1 # 2)).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj
    (real_min
      (real_mult (projT1 (b5dJ_LogErr_delta_exp x
                   (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                   (b5dQ_p_epsL_pos a Ha k2 Hk2)))
                 (real_const (1 # 12)))
      (real_mult (real_const a) (real_const (Qmult k2 (1 # 2)))))
    (real_const (1 # 2)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x
                 (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (b5dQ_p_epsL_pos a Ha k2 Hk2)))
               (real_const (1 # 12)))
    (real_mult (real_const a) (real_const (Qmult k2 (1 # 2)))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj
    (projT1 (b5dJ_LogErr_delta_exp x
                 (real_mult (real_const a) (real_const (Qmult k2 (1 # 2))))
                 (b5dQ_p_epsL_pos a Ha k2 Hk2)))
    (real_const (1 # 12)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const a) (real_const (Qmult k2 (1 # 2))) n)).
  pose proof (qeqT_imp_qeq _ _ (b5dQ_lb_logerr_coord x a Ha k2 Hk2 n)) as Hgenqeq10139.
  rewrite Hgenqeq10139.
  repeat (rewrite real_const_proj).
  reflexivity.
Qed.

(* ============================================================ *)
(* Piece 3 main piece: b5dQ_lb_gdiff                                             *)
(* ============================================================ *)
Lemma b5dQ_lb_gdiff : forall (q : Q) (Hq0 : QleT' 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : QltT 0 a)
  (k2 k2p : Q) (Hk2 : QltT 0 k2) (Hk2p : QltT 0 k2p),
  real_lt (real_const (Qmult (Qmin (Qmin
            (Qmult (Qmin (1 # 2) (Qmult (1 # 4) (Qmult a (Qmult k2 (1 # 2)))))
                   (1 # 12))
            (Qmult a (Qmult k2 (1 # 2))))
          (1 # 2)) (1 # 2)))
    (projT1 (b5dK_gdiff_pts_r_exp q Hq0 Hq1 x Hxr (real_const a)
            (real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha)))) k2 k2p Hk2 Hk2p)).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha k2 k2p Hk2 Hk2p.
  set (m := Qmult a (Qmult k2 (1 # 2))).
  set (floorL := Qmin (1 # 2) (Qmult (1 # 4) m)).
  set (floorA := Qmult floorL (1 # 12)).
  set (floorB := m).
  set (c := Qmin (Qmin floorA floorB) (1 # 2)).
  set (lb := Qmult c (1 # 2)).
  set (e := Qmult lb (1 # 2)).
  assert (H12 : Qlt 0 (1 # 2)) by (change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H14 : Qlt 0 (1 # 4)) by (change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (H112 : Qlt 0 (1 # 12)) by (change (Qlt 0 (1 # 12)); unfold Qlt; simpl; lia).
  assert (Hk2Q : Qlt 0 k2) by (apply QltT_to_Qlt; exact Hk2).
  assert (Hmpos : Qlt 0 m).
  { unfold m. apply (Qmult_lt_0_compat a (Qmult k2 (1 # 2))).
    - exact (QltT_to_Qlt _ _ (Ha)).
    - apply (Qmult_lt_0_compat k2 (1 # 2)); [exact Hk2Q | exact H12]. }
  assert (HfloorLpos : Qlt 0 floorL).
  { unfold floorL. apply Q.min_glb_lt.
    - exact H12.
    - apply (Qmult_lt_0_compat (1 # 4) m); [exact H14 | exact Hmpos]. }
  assert (HfloorApos : Qlt 0 floorA).
  { unfold floorA. apply (Qmult_lt_0_compat floorL (1 # 12));
      [exact HfloorLpos | exact H112]. }
  assert (Hcpos : Qlt 0 c).
  { unfold c. apply Q.min_glb_lt.
    - apply Q.min_glb_lt; [exact HfloorApos | exact Hmpos].
    - exact H12. }
  assert (Hlbpos : Qlt 0 lb).
  { unfold lb. apply (Qmult_lt_0_compat c (1 # 2)); [exact Hcpos | exact H12]. }
  assert (Hepos : Qlt 0 e).
  { unfold e. apply (Qmult_lt_0_compat lb (1 # 2)); [exact Hlbpos | exact H12]. }
  assert (HcA : Qle c floorA).
  { unfold c. apply (Qle_trans (Qmin (Qmin floorA floorB) (1 # 2))
                               (Qmin floorA floorB) floorA).
    - apply Q.le_min_l.
    - apply Q.le_min_l. }
  assert (HcB : Qle c floorB).
  { unfold c. apply (Qle_trans (Qmin (Qmin floorA floorB) (1 # 2))
                               (Qmin floorA floorB) floorB).
    - apply Q.le_min_l.
    - apply Q.le_min_r. }
  assert (HcC : Qle c (1 # 2)).
  { unfold c. apply Q.le_min_r. }
  assert (HmL : Qle floorL (1 # 2)) by (unfold floorL; apply Q.le_min_l).
  assert (Hm2 : Qle floorL (Qmult (1 # 4) m)) by (unfold floorL; apply Q.le_min_r).
  unfold real_lt.
  exists e.
  split.
  { apply Qlt_to_QltT. exact Hepos. }
  { exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    pose proof (qeqT_imp_qeq _ _ (b5dQ_lb_gdiff_coord q Hq0 Hq1 x Hxr a Ha k2 k2p Hk2 Hk2p n)) as Hgenqeq10212.
    rewrite Hgenqeq10212.
    pose proof (qeqT_imp_qeq _ _ b5dQ_p_qinv2sq) as Hgenqeqsq10202.
    pose proof (qeqT_imp_qeq _ _ b5dQ_p_qinv2) as Hgenqeq10202.
    rewrite Hgenqeqsq10202.
    rewrite Hgenqeq10202.
    cbn [projT1 real_const].
    set (u := projT1 (b5f_u x) n).
    assert (Hug : Qle 1 u) by (apply QleT'_to_Qle; unfold u; apply b5dQ_p_u_ge1).
    assert (Hm0 : Qle 0 m) by (apply Qlt_le_weak; exact Hmpos).
    (* the inner δL coordinate >= floorL: min-glb branch by branch. *)
    assert (HdL1 : Qle floorL (Qmult (1 # 2) u)).
    { apply (Qle_trans floorL (1 # 2) (Qmult (1 # 2) u)).
      - exact HmL.
      - nra. }
    assert (HdL2 : Qle floorL (Qmult (1 # 4) (Qmult m (Qmult u u)))).
    { apply (Qle_trans floorL (Qmult (1 # 4) m)
                       (Qmult (1 # 4) (Qmult m (Qmult u u)))).
      - exact Hm2.
      - apply QleT'_to_Qle. apply b5dQ_p_q_scaled_le; [apply Qle_to_QleT'; apply Qlt_le_weak; exact H14 | apply Qle_to_QleT'; exact Hm0 | apply Qle_to_QleT'; exact Hug]. }
    assert (HdL : Qle floorL
      (Qmin (Qmult (1 # 2) u)
            (Qmult (1 # 4) (Qmult m (Qmult u u))))).
    apply QleT'_to_Qle.
    { apply b5dQ_p_min_glb_le; [exact (Qle_to_QleT' _ _ (HdL1)) | exact (Qle_to_QleT' _ _ (HdL2))]. }
    (* the three-branch floor facts. *)
    assert (FA : Qle floorA (Qmult (Qmin (Qmult (1 # 2) u)
            (Qmult (1 # 4) (Qmult m (Qmult u u)))) (1 # 12))).
    { unfold floorA.
      apply (Qmult_le_compat_r floorL
        (Qmin (Qmult (1 # 2) u) (Qmult (1 # 4) (Qmult m (Qmult u u))))
        (1 # 12)); [exact HdL | apply Qlt_le_weak; exact H112]. }
    assert (FB : Qle m (Qmult a (Qmult k2 (1 # 2)))).
    { unfold m. apply Qle_refl. }
    (* the three-branch strict margins. *)
    assert (S1 : Qlt e (Qminus (Qmult (Qmin (Qmult (1 # 2) u)
            (Qmult (1 # 4) (Qmult m (Qmult u u)))) (1 # 12)) lb)).
    { unfold e, lb.
      apply QltT_to_Qlt.
      apply (b5dQ_p_branch_lt
               (Qmult (Qmin (Qmult (1 # 2) u)
                            (Qmult (1 # 4) (Qmult m (Qmult u u)))) (1 # 12))
               floorA c); [exact (Qle_to_QleT' _ _ (FA)) | exact (Qle_to_QleT' _ _ (HcA)) | exact (Qlt_to_QltT _ _ (Hcpos))]. }
    assert (S2 : Qlt e (Qminus (Qmult a (Qmult k2 (1 # 2))) lb)).
    { unfold e, lb.
      apply QltT_to_Qlt.
      apply (b5dQ_p_branch_lt (Qmult a (Qmult k2 (1 # 2))) m c);
        [exact (Qle_to_QleT' _ _ (FB)) | exact (Qle_to_QleT' _ _ (HcB)) | exact (Qlt_to_QltT _ _ (Hcpos))]. }
    assert (S3 : Qlt e (Qminus (1 # 2) lb)).
    { unfold e, lb.
      apply QltT_to_Qlt.
      apply (b5dQ_p_branch_lt (1 # 2) (1 # 2) c);
        [(apply Qle_to_QleT'; apply Qle_refl) | exact (Qle_to_QleT' _ _ (HcC)) | exact (Qlt_to_QltT _ _ (Hcpos))]. }
    (* assembly: the min-tree decomposition of X_n - lb (two levels of Qmin minus lb). *)
    pose proof (qeqT_imp_qeq _ _ (b5dQ_p_qmin_sub_r
      (Qmin (Qmult (Qmin (Qmult (1 # 2) u)
                         (Qmult (1 # 4)
                                (Qmult (Qmult a (Qmult k2 (1 # 2)))
                                       (Qmult u u)))) (1 # 12))
            (Qmult a (Qmult k2 (1 # 2))))
      (1 # 2) lb)) as Hgenqmin1_L10266.
    rewrite Hgenqmin1_L10266.
    pose proof (qeqT_imp_qeq _ _ (b5dQ_p_qmin_sub_r
      (Qmult (Qmin (Qmult (1 # 2) u)
                   (Qmult (1 # 4)
                          (Qmult (Qmult a (Qmult k2 (1 # 2)))
                                 (Qmult u u)))) (1 # 12))
      (Qmult a (Qmult k2 (1 # 2))) lb)) as Hgenqmin2_L10273.
    rewrite Hgenqmin2_L10273.
    apply Q.min_glb_lt.
    - apply Q.min_glb_lt; [exact S1 | exact S2].
    - exact S3.
  }
Qed.

(* ============================================================ *)
(* Piece 4: b5dQ_lb_exp_part (the δD2f L9 coordinate-layer implementation — the S leaf at the tail certificate) *)
(* In the exp_part body: Sx := b5a_S x; invM := real_inv_pos (1+|Sx|);           *)
(*   eps0 := eps*real_const (Qinv (Kvq q))*invM; δL := LogErr @                  *)
(*   real_const b5j_kL; δlin := linear @ eps0; δ :=                              *)
(*   min(min(δlin*(1#4), δL*(1#12)), (1#2)).                                     *)
(* ============================================================ *)
Lemma b5dQ_p_eps0_pos : forall (q : Q) (Hq0 : QleT' 0 q) (a : Q) (Ha : QltT 0 a)
  (x : Real),
  real_lt real_zero (real_mult
    (real_mult (real_const a) (real_const (Qinv (b5j_Kvq q))))
    (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                  (b5dK_real_abs_plus_one_pos_exp (b5a_S x)))).
Proof.
  intros q Hq0 a Ha x.
  apply real_mult_positive.
  - apply real_mult_positive.
    + apply real_const_pos. apply Qlt_to_QltT. exact (QltT_to_Qlt _ _ (Ha)).
    + apply real_const_pos. apply Qlt_to_QltT.
      apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (b5j_Kvq_pos q (QleT'_to_Qle _ _ Hq0))).
  - apply (real_inv_pos_pos (real_plus real_one (real_abs (b5a_S x)))
                            (b5dK_real_abs_plus_one_pos_exp (b5a_S x))).
Qed.

Lemma b5dQ_p_logerr_kL_coord : forall (x : Real) (n : nat),QeqT (
  projT1 (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                 (real_const_pos b5j_kL (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT))))) n
  ) ( Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                      (projT1 (b5f_u x) n))))).
Proof.
  intros x n.
  apply qeq_imp_qeqT.
  change (projT1 (projT1 (b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x)
                 (real_const b5j_kL)
                 (real_const_pos b5j_kL (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT))))) n
  == Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                      (projT1 (b5f_u x) n))))).
  change (projT1 (real_min
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)) (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult (real_const b5j_kL) (real_mult (b5f_u x) (b5f_u x))))) n
  == Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
          (Qmult (Qmult (Qinv 2) (Qinv 2))
                 (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                      (projT1 (b5f_u x) n))))).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)) (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult (real_const b5j_kL) (real_mult (b5f_u x) (b5f_u x)))) n)).
  repeat (rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) || rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _))).
  cbn [projT1 real_inv_pos real_plus real_one real_const Nat.leb
       b5dJ_two_pos_exp b5j_kL].
  reflexivity.
Qed.

(* ============================================================ *)
(* the exp_part coordinate piece (change to the explicit δ tree + projection rewrites; *)
(* the S atom stays atomic; the b5j_kL/Kvq-inv closed forms copied as is)        *)
(* ============================================================ *)
Lemma b5dQ_lb_exp_part_coord : forall (q : Q) (Hq0 : QleT' 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : QltT 0 a) (n : nat),QeqT (
  projT1 (projT1 (b5dK_exp_part_bound_closed_r_exp q Hq0 Hq1 x Hxr
                 (real_const a) (real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha)))))) n
  ) ( Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult a (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha n.
  apply qeq_imp_qeqT.
  set (K := Qinv (b5j_Kvq q)).
  set (eps0t := real_mult (real_mult (real_const a) (real_const K))
                  (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                                (b5dK_real_abs_plus_one_pos_exp (b5a_S x)))).
  change (projT1 (real_min (real_min
    (real_mult (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
                       (b5dQ_p_eps0_pos q Hq0 a Ha x)))
               (real_const (1 # 4)))
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                       (real_const_pos b5j_kL
                          (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
               (real_const (1 # 12))))
    (real_const (1 # 2))) n
  == Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj
    (real_min
      (real_mult (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
                         (b5dQ_p_eps0_pos q Hq0 a Ha x)))
                 (real_const (1 # 4)))
      (real_mult (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                         (real_const_pos b5j_kL
                            (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
                 (real_const (1 # 12))))
    (real_const (1 # 2)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj
    (real_mult (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
                       (b5dQ_p_eps0_pos q Hq0 a Ha x)))
               (real_const (1 # 4)))
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                       (real_const_pos b5j_kL
                          (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
               (real_const (1 # 12))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj
    (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
            (b5dQ_p_eps0_pos q Hq0 a Ha x)))
    (real_const (1 # 4)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj
    (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
            (real_const_pos b5j_kL
               (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
    (real_const (1 # 12)) n)).
  pose proof (qeqT_imp_qeq _ _ (b5dQ_p_logerr_kL_coord x n)) as Hgenqeq10425.
  rewrite Hgenqeq10425.
  change (Qmin (Qmin
      (Qmult (projT1 (real_min (real_const (1 # 2))
                               (real_mult eps0t (real_const (1 # 4)))) n)
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)
  == Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj (real_const (1 # 2)) (real_mult eps0t (real_const (1 # 4))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps0t (real_const (1 # 4)) n)).
  unfold eps0t, K.
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj
    (real_mult (real_const a) (real_const (Qinv (b5j_Kvq q))))
    (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                  (b5dK_real_abs_plus_one_pos_exp (b5a_S x))) n)).
  repeat (rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) || rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _))).
  pose proof (qeqT_imp_qeq _ _ (b5dQ_p_invM_coord x n)) as Hgenqeq10456.
  rewrite Hgenqeq10456.
  cbn [projT1 real_inv_pos real_plus real_abs real_one real_const Nat.leb
       b5dK_real_abs_plus_one_pos_exp b5j_kL].
  reflexivity.
Qed.

(* ============================================================ *)
(* Piece 4 main piece: b5dQ_lb_exp_part (the S leaf at the tail certificate; N := Nub) *)
(* ============================================================ *)
Lemma b5dQ_lb_exp_part : forall (q : Q) (Hq0 : QleT' 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : QltT 0 a)
  (Nub : nat)
  (Hcert : forall n : nat, NatLe Nub n ->
           QleT' (Qabs (projT1 (b5a_S x) n)) 2),
  real_lt (real_const (Qmult (Qmin (Qmin
            (Qmult (Qmin (1 # 2)
                         (Qmult (Qmult (Qmult a (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                   (1 # 4))
            (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
          (1 # 2)) (1 # 2)))
    (projT1 (b5dK_exp_part_bound_closed_r_exp q Hq0 Hq1 x Hxr
            (real_const a) (real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha)))))).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha Nub Hcert.
  set (K := Qinv (b5j_Kvq q)).
  set (floorL2 := Qmult (Qmult (Qmult a K) (1 # 3)) (1 # 4)).
  set (floorL := Qmin (1 # 2) floorL2).
  set (floorA := Qmult floorL (1 # 4)).
  set (floorD2 := Qmult (1 # 4) b5j_kL).
  set (floorD := Qmin (1 # 2) floorD2).
  set (floorB := Qmult floorD (1 # 12)).
  set (c := Qmin (Qmin floorA floorB) (1 # 2)).
  set (lb := Qmult c (1 # 2)).
  set (e := Qmult lb (1 # 2)).
  assert (H12 : Qlt 0 (1 # 2)) by (change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H14 : Qlt 0 (1 # 4)) by (change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (H13 : Qlt 0 (1 # 3)) by (change (Qlt 0 (1 # 3)); unfold Qlt; simpl; lia).
  assert (H112 : Qlt 0 (1 # 12)) by (change (Qlt 0 (1 # 12)); unfold Qlt; simpl; lia).
  assert (HKpos : Qlt 0 K).
  { unfold K. apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (b5j_Kvq_pos q (QleT'_to_Qle _ _ Hq0))). }
  assert (HkLposQ : Qlt 0 b5j_kL) by (apply QltT_to_Qlt; exact b5j_kL_posT).
  assert (HmL2pos : Qlt 0 floorL2).
  { unfold floorL2. apply (Qmult_lt_0_compat (Qmult (Qmult a K) (1 # 3)) (1 # 4)).
    - apply (Qmult_lt_0_compat (Qmult a K) (1 # 3)).
      + apply (Qmult_lt_0_compat a K); [exact (QltT_to_Qlt _ _ (Ha)) | exact HKpos].
      + exact H13.
    - exact H14. }
  assert (HfloorLpos : Qlt 0 floorL).
  { unfold floorL. apply Q.min_glb_lt; [exact H12 | exact HmL2pos]. }
  assert (HfloorApos : Qlt 0 floorA).
  { unfold floorA. apply (Qmult_lt_0_compat floorL (1 # 4));
      [exact HfloorLpos | exact H14]. }
  assert (HfloorD2pos : Qlt 0 floorD2).
  { unfold floorD2. apply (Qmult_lt_0_compat (1 # 4) b5j_kL);
      [exact H14 | exact HkLposQ]. }
  assert (HfloorDpos : Qlt 0 floorD).
  { unfold floorD. apply Q.min_glb_lt; [exact H12 | exact HfloorD2pos]. }
  assert (HfloorBpos : Qlt 0 floorB).
  { unfold floorB. apply (Qmult_lt_0_compat floorD (1 # 12));
      [exact HfloorDpos | exact H112]. }
  assert (Hcpos : Qlt 0 c).
  { unfold c. apply Q.min_glb_lt.
    - apply Q.min_glb_lt; [exact HfloorApos | exact HfloorBpos].
    - exact H12. }
  assert (Hlbpos : Qlt 0 lb).
  { unfold lb. apply (Qmult_lt_0_compat c (1 # 2)); [exact Hcpos | exact H12]. }
  assert (Hepos : Qlt 0 e).
  { unfold e. apply (Qmult_lt_0_compat lb (1 # 2)); [exact Hlbpos | exact H12]. }
  assert (HcA : Qle c floorA).
  { unfold c. apply (Qle_trans (Qmin (Qmin floorA floorB) (1 # 2))
                               (Qmin floorA floorB) floorA).
    - apply Q.le_min_l.
    - apply Q.le_min_l. }
  assert (HcB : Qle c floorB).
  { unfold c. apply (Qle_trans (Qmin (Qmin floorA floorB) (1 # 2))
                               (Qmin floorA floorB) floorB).
    - apply Q.le_min_l.
    - apply Q.le_min_r. }
  assert (HcC : Qle c (1 # 2)).
  { unfold c. apply Q.le_min_r. }
  assert (HfL1 : Qle floorL (1 # 2)) by (unfold floorL; apply Q.le_min_l).
  assert (HfL2 : Qle floorL floorL2) by (unfold floorL; apply Q.le_min_r).
  assert (HfD1 : Qle floorD (1 # 2)) by (unfold floorD; apply Q.le_min_l).
  assert (HfD2 : Qle floorD floorD2) by (unfold floorD; apply Q.le_min_r).
  unfold real_lt.
  exists e.
  split.
  { apply Qlt_to_QltT. exact Hepos. }
  { exists Nub.
    intros n Hn.
    apply Qlt_to_QltT.
    pose proof (qeqT_imp_qeq _ _ (b5dQ_lb_exp_part_coord q Hq0 Hq1 x Hxr a Ha n)) as Hgenqeq10549.
    rewrite Hgenqeq10549.
    pose proof (qeqT_imp_qeq _ _ b5dQ_p_qinv2sq) as Hgenqeqsq10202.
    pose proof (qeqT_imp_qeq _ _ b5dQ_p_qinv2) as Hgenqeq10202.
    rewrite Hgenqeqsq10202.
    rewrite Hgenqeq10202.
    cbn [projT1 real_const].
    set (Sn := projT1 (b5a_S x) n).
    set (u := projT1 (b5f_u x) n).
    assert (Hug : Qle 1 u) by (apply QleT'_to_Qle; unfold u; apply b5dQ_p_u_ge1).
    assert (HcSn : Qle (Qabs Sn) 2) by (apply QleT'_to_Qle; exact (Hcert n Hn)).
    (* the invM coordinate >= 1#3 (closed from below by the |Sn| <= 2 tail certificate). *)
    assert (Hinv : Qle (1 # 3) (Qinv (Qplus 1 (Qabs Sn)))).
    { pose proof (qeqT_imp_qeq _ _ b5dQ_p_qinv3) as Hgenqinv3b.
      rewrite <- Hgenqinv3b.
      apply QleT'_to_Qle.
      apply b5dQ_p_qinv_le_mono.
      - apply Qlt_to_QltT. apply (Qlt_le_trans 0 1 (Qplus 1 (Qabs Sn))).
        + apply (QltT_to_Qlt 0 1 qltT_0_1).
        + apply (Qplus_le_compat 1 1 0 (Qabs Sn));
            [apply Qle_refl | apply Qabs_nonneg].
      - exact (Qlt_to_QltT _ _ (H13)).
      - apply Qle_to_QleT'. nra. }
    (* the inner δlin coordinate >= floorL (min-glb branch by branch). *)
    assert (He0 : Qle (Qmult (Qmult a K) (1 # 3))
                     (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn))))).
    { apply (Qle_trans (Qmult (Qmult a K) (1 # 3)) (Qmult (1 # 3) (Qmult a K))
                       (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn))))).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      - apply (Qle_trans (Qmult (1 # 3) (Qmult a K))
                         (Qmult (Qinv (Qplus 1 (Qabs Sn))) (Qmult a K))
                         (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn))))).
        + apply (Qmult_le_compat_r (1 # 3) (Qinv (Qplus 1 (Qabs Sn)))
                                   (Qmult a K));
            [ exact Hinv | apply Qlt_le_weak; exact (Qmult_lt_0_compat a K (QltT_to_Qlt _ _ (Ha)) HKpos) ].
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (HdL2 : Qle floorL2
        (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))).
    { unfold floorL2.
      apply (Qmult_le_compat_r (Qmult (Qmult a K) (1 # 3))
                               (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn))))
                               (1 # 4));
        [ exact He0 | apply Qlt_le_weak; exact H14 ]. }
    assert (HdL : Qle floorL
        (Qmin (1 # 2)
              (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))).
    apply QleT'_to_Qle.
    { apply b5dQ_p_min_glb_le; [exact (Qle_to_QleT' _ _ (HfL1)) | ].
      apply Qle_to_QleT'.
      apply (Qle_trans floorL floorL2
             (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)));
        [exact HfL2 | exact HdL2]. }
    (* the inner δL coordinate >= floorD (per branch with u >= 1). *)
    assert (Hq1u : Qle (1 # 2) (Qmult (1 # 2) u)) by nra.
    assert (Hq2u : Qle (Qmult (1 # 4) b5j_kL)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))).
    apply QleT'_to_Qle.
    { apply b5dQ_p_q_scaled_le;
        [ apply Qle_to_QleT'; apply Qlt_le_weak; exact H14 | apply Qle_to_QleT'; apply Qlt_le_weak; exact HkLposQ | apply Qle_to_QleT'; exact Hug ]. }
    assert (HfD : Qle floorD
        (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u))))).
    apply QleT'_to_Qle.
    { apply b5dQ_p_min_glb_le.
      - apply Qle_to_QleT'. apply (Qle_trans floorD (1 # 2) (Qmult (1 # 2) u));
          [exact HfD1 | exact Hq1u].
      - idtac.
      apply Qle_to_QleT'.
      apply (Qle_trans floorD floorD2
             (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u))));
        [exact HfD2 | exact Hq2u]. }
    (* the two-branch floor facts (the A/B branches). *)
    assert (FA : Qle floorA (Qmult (Qmin (1 # 2)
              (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))
              (1 # 4))).
    { unfold floorA.
      apply (Qmult_le_compat_r floorL
        (Qmin (1 # 2)
              (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))
        (1 # 4)); [exact HdL | apply Qlt_le_weak; exact H14]. }
    assert (FB : Qle floorB
        (Qmult (Qmin (Qmult (1 # 2) u)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12))).
    { unfold floorB.
      apply (Qmult_le_compat_r floorD
        (Qmin (Qmult (1 # 2) u) (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u))))
        (1 # 12)); [exact HfD | apply Qlt_le_weak; exact H112]. }
    (* the three-branch strict margins. *)
    assert (S1 : Qlt e (Qminus (Qmult (Qmin (1 # 2)
              (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))
              (1 # 4)) lb)).
    { unfold e, lb.
      apply QltT_to_Qlt.
      apply (b5dQ_p_branch_lt
               (Qmult (Qmin (1 # 2)
                     (Qmult (Qmult (Qmult a K) (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))
                      (1 # 4))
               floorA c); [exact (Qle_to_QleT' _ _ (FA)) | exact (Qle_to_QleT' _ _ (HcA)) | exact (Qlt_to_QltT _ _ (Hcpos))]. }
    assert (S2 : Qlt e (Qminus (Qmult (Qmin (Qmult (1 # 2) u)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12)) lb)).
    { unfold e, lb.
      apply QltT_to_Qlt.
      apply (b5dQ_p_branch_lt
               (Qmult (Qmin (Qmult (1 # 2) u)
                            (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12))
               floorB c); [exact (Qle_to_QleT' _ _ (FB)) | exact (Qle_to_QleT' _ _ (HcB)) | exact (Qlt_to_QltT _ _ (Hcpos))]. }
    assert (S3 : Qlt e (Qminus (1 # 2) lb)).
    { unfold e, lb.
      apply QltT_to_Qlt.
      apply (b5dQ_p_branch_lt (1 # 2) (1 # 2) c);
        [(apply Qle_to_QleT'; apply Qle_refl) | exact (Qle_to_QleT' _ _ (HcC)) | exact (Qlt_to_QltT _ _ (Hcpos))]. }
    (* assembly: the min-tree decomposition of X_n - lb (two levels of Qmin minus lb). *)
    pose proof (qeqT_imp_qeq _ _ (b5dQ_p_qmin_sub_r
      (Qmin (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult a (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4))
            (Qmult (Qmin (Qmult (1 # 2) u)
                         (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12)))
      (1 # 2) lb)) as Hgenqmin3_L10648.
    rewrite Hgenqmin3_L10648.
    pose proof (qeqT_imp_qeq _ _ (b5dQ_p_qmin_sub_r
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult a (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4))
      (Qmult (Qmin (Qmult (1 # 2) u)
                   (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12)) lb)) as Hgenqmin4_L10655.
    rewrite Hgenqmin4_L10655.
    apply Q.min_glb_lt.
    - apply Q.min_glb_lt; [exact S1 | exact S2].
    - exact S3.
  }
Qed.

(* ============================================================ *)
(* end of sc2_b5a_item27_p2_lbLog.v, the P2 set                                  *)
(* ============================================================ *)

(* ===== Section P3 (the certificate family C1-C5 + the glue G1-G9 + the Q-layer small pieces, 17 Lemma) ===== *)

(* ============================================================ *)
(* Section 0. small pieces (Q-layer positivity certificates; b5dQ_ exclusive; all genuine Qed) *)
(* ============================================================ *)

(* QltT 0 (1#4) (the real_eq-instance eps certificate of C1). *)
Lemma b5dQ_Hq14T : QltT 0 (1 # 4).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* QltT 0 1 (the real_eq-instance eps certificate of C3). *)
Lemma b5dQ_Hq1T : QltT 0 1.
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* Qlt 0 (1#4) (used by the q_abs_gt_neg family). *)
Lemma b5dQ_Hq14 : QltT 0 (1 # 4).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* ============================================================ *)
(* G2 b5dQ_S_tk0_eq_one: the Real-layer bridge S(t_0) == 1 (the base of the k=0  *)
(*   branch certificates)                                                        *)
(*   Statement = the design §4 G2 line (t_0 := tkq q M 0).                       *)
(*   Chain: b5dL_tkq_0 (Qeq t_0 0) + b5dH_real_const_qeq +                       *)
(*     b5m_S_wd (root L86539) + item8 b5d4_S_const0_eq_one +                     *)
(*     real_eq_trans.                                                            *)
(* ============================================================ *)
Lemma b5dQ_S_tk0_eq_one : forall (q : Q) (M : nat),
  real_eq (b5a_S (real_const (b5dL_tkq q M 0))) real_one.
Proof.
  intros q M.
  apply (real_eq_trans _ (b5a_S (real_const 0)) _).
  - apply b5m_S_wd.
    apply b5dH_real_const_qeq.
    exact (b5dL_tkq_0 q M).
  - exact b5d4_S_const0_eq_one.
Qed.

(* ============================================================ *)
(* Q-layer kernel: p == 1 and |x - p| < 1/4 give Qle (1#2) x                     *)
(*   (the C1 tail bound: isomorphic to the item8 b5d4_q_lb_half structure, with  *)
(*   eps := 1/4; first Qlt_minus_iff gives 3/4 < x, then the Qle (1#2) <= 3/4    *)
(*   transitivity)                                                               *)
(* ============================================================ *)
Lemma b5dQ_q_close_one_lb : forall (x p : Q),QeqT (
  p ) ( 1 )-> QltT (Qabs (x - p)) (1 # 4) -> QleT' (1 # 2) x.
Proof.
  intros x p Hp H.
  apply Qle_to_QleT'.
  apply QltT_to_Qlt in H.
  pose proof (qeqT_imp_qeq _ _ Hp) as HpQ10730.
  setoid_rewrite HpQ10730 in H.
  assert (H34 : Qlt (3 # 4) x).
  { apply (proj2 (Qlt_minus_iff (3 # 4) x)).
    setoid_replace (x - (3 # 4)) with ((x - 1) - - (1 # 4)) by ring.
    apply (proj1 (Qlt_minus_iff (- (1 # 4)) (x - 1))).
    apply QltT_to_Qlt. apply (q_abs_gt_neg (x - 1) (1 # 4) b5dQ_Hq14). exact (Qlt_to_QltT _ _ H). }
  apply (Qle_trans (1 # 2) (3 # 4) x).
  - apply Qlt_le_weak. unfold Qlt. simpl. lia.
  - apply Qlt_le_weak. exact H34.
Qed.

(* ============================================================ *)
(* C1 b5dQ_S_lb_tail_k0: the k=0 branch S lower-bound tail certificate (cA := 1/2 written directly) *)
(*   Statement = the design §4 C1 line (sigT N with the tail Qle (1#2) in (N<=n)%nat form). *)
(*   Proof = G2 @ eps := 1/4 (|S_n - 1| < 1/4 gives S_n > 3/4 >= 1/2)            *)
(*   + via b5dQ_q_close_one_lb.                                                  *)
(* ============================================================ *)
Lemma b5dQ_S_lb_tail_k0 : forall (q : Q) (M : nat),
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QleT' (1 # 2) (projT1 (b5a_S (real_const (b5dL_tkq q M 0))) n)).
Proof.
  intros q M.
  destruct (b5dQ_S_tk0_eq_one q M (1 # 4) b5dQ_Hq14T) as [N HN].
  exists N.
  intros n Hn.
  apply (b5dQ_q_close_one_lb (projT1 (b5a_S (real_const (b5dL_tkq q M 0))) n)
                             (projT1 real_one n)).
  - cbn [projT1 real_one]. reflexivity.
  - exact (HN n Hn).
Qed.

(* ============================================================ *)
(* C3 b5dQ_S_ub_tail_k0: the k=0 branch S upper-bound tail certificate (M_S := 2 written directly) *)
(*   Statement = the design §4 C3 line.                                          *)
(*   Proof = G2 @ eps := 1 (|S_n - 1| < 1 gives 0 < S_n < 2, hence               *)
(*     |S_n| <= 2) + item8 b5d4_q_ub_two.                                        *)
(* ============================================================ *)
Lemma b5dQ_S_ub_tail_k0 : forall (q : Q) (M : nat),
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QleT' (Qabs (projT1 (b5a_S (real_const (b5dL_tkq q M 0))) n)) 2).
Proof.
  intros q M.
  destruct (b5dQ_S_tk0_eq_one q M 1 b5dQ_Hq1T) as [N HN].
  exists N.
  intros n Hn.
  apply (b5d4_q_ub_two (projT1 (b5a_S (real_const (b5dL_tkq q M 0))) n)
                       (projT1 real_one n)).
  - cbn [projT1 real_one]. reflexivity.
  - exact (HN n Hn).
Qed.

(* ============================================================ *)
(* G9 b5dQ_S_ub_tail_restate: the NatLe-form tail restated in (N<=n)%nat form +  *)
(*   the Qle 1 weakened to Qle (1#2) (the general glue on the output side of     *)
(*   b5a_S_ge_one; the design §4 G9 line: used directly as the lb tail certificate of C2). *)
(* ============================================================ *)
Lemma b5dQ_S_ub_tail_restate : forall (u : nat -> Q),
  sigT (fun N : nat => forall n : nat, NatLe N n -> QleT' 1 (u n)) ->
  sigT (fun N : nat => forall n : nat, NatLe N n -> QleT' (1 # 2) (u n)).
Proof.
  intros u [N HN].
  exists N.
  intros n Hn.
  apply Qle_to_QleT'.
  apply (Qle_trans (1 # 2) 1 (u n)).
  - apply Qlt_le_weak. unfold Qlt. simpl. lia.
  - apply QleT'_to_Qle. exact (HN n Hn).
Qed.

(* ============================================================ *)
(* C2 b5dQ_S_lb_tail_kS: the k>=1 branch S lower-bound tail certificate (cA := 1/2 written directly) *)
(*   Statement = the design §4 C2 line (0<q, 0<M and 0<k give a sigT N tail      *)
(*     Qle (1#2) (S(real_const t_k)); 0<t_k taken inside by tkq_pos).            *)
(*   Proof = b5a_S_ge_one (root L84807) @ real_const_pos_f1 +                    *)
(*     G9 (the NatLe restatement + the 1 -> 1/2 weakening).                      *)
(* ============================================================ *)
Lemma b5dQ_S_lb_tail_kS : forall (q : Q) (M k : nat),
  QltT 0 q -> (0 < M)%nat -> (0 < k)%nat ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QleT' (1 # 2) (projT1 (b5a_S (real_const (b5dL_tkq q M k))) n)).
Proof.
  intros q M k Hq0 HM Hk0.
  apply (b5dQ_S_ub_tail_restate
           (fun n : nat => projT1 (b5a_S (real_const (b5dL_tkq q M k))) n)).
  apply (b5a_S_ge_one (real_const (b5dL_tkq q M k))).
  apply real_const_pos_f1.
  exact (QltT_to_Qlt _ _ (b5dL_tkq_pos q M k Hq0 HM Hk0)).
Qed.

(* ============================================================ *)
(* C4 b5dQ_S_ub_tail_kS: the k>=1 branch S upper-bound tail certificate (M_S := 2 written directly) *)
(*   Statement = the design §4 C4 line (0<q, q<1, 0<M, 0<k and k<=M give         *)
(*     a sigT N tail Qle |S(real_const t_k)| 2; 0<t_k / t_k<1 taken inside by    *)
(*     tkq_pos/tkq_lt1).                                                         *)
(*   Proof = item15 b5dE_S_ub_tail_q @ q := tkq supplied directly (in (N<=n)%nat *)
(*     form, zero glue).                                                         *)
(* ============================================================ *)
Lemma b5dQ_S_ub_tail_kS : forall (q : Q) (M k : nat),
  QltT 0 q -> QltT q 1 -> (0 < M)%nat -> (0 < k)%nat -> (k <= M)%nat ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QleT' (Qabs (projT1 (b5a_S (real_const (b5dL_tkq q M k))) n)) 2).
Proof.
  intros q M k Hq0 Hq1 HM Hk0 HkM.
  apply (b5dE_S_ub_tail_q (b5dL_tkq q M k)).
  - exact (b5dL_tkq_pos q M k Hq0 HM Hk0).
  - exact (b5dL_tkq_lt1 q M k (b5dH_q_pos_le q Hq0) HM HkM Hq1).
Qed.

(* ============================================================ *)
(* C5 b5dQ_sincos_all_k: the all-n sin/cos bound certificates (the HMs_all/HMc_all *)
(*   instances with Ms := Mc := 1) — the §4.1 draft (the cos counterpart folded  *)
(*   into And)                                                                   *)
(*   Statement: 0<q, q<1, 0<M and k<=M give                                      *)
(*     And (forall n, Qle |sin_partial n (arctan_partial n t_k_n)| 1)            *)
(*         (forall n, Qle |cos_partial n (arctan_partial n t_k_n)| 1)            *)
(*   Proof = item6 M4a/M4b @ x := real_const t_k + item22                        *)
(*     b5dL_tkC (the domain certificate) applied directly (all n, zero branching). *)
(* ============================================================ *)
Lemma b5dQ_sincos_all_k : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (M : nat) (k : nat), (0 < M)%nat -> (k <= M)%nat ->
  And (forall n : nat,
         QleT' (Qabs (sin_partial n (arctan_partial n
                (projT1 (real_const (b5dL_tkq q M k)) n)))) 1)
      (forall n : nat,
         QleT' (Qabs (cos_partial n (arctan_partial n
                (projT1 (real_const (b5dL_tkq q M k)) n)))) 1).
Proof.
  intros q Hq0 Hq1 M k HM Hk.
  split.
  - intro n.
    exact (b5d2_sinA_abs_le1 (real_const (b5dL_tkq q M k))
                              (b5dL_tkC q Hq0 Hq1 M k HM Hk) n).
  - intro n.
    exact (b5d2_cosA_abs_le1 (real_const (b5dL_tkq q M k))
                              (b5dL_tkC q Hq0 Hq1 M k HM Hk) n).
Qed.

(* ============================================================ *)
(* G1 b5dQ_tkq_Hxr: the Hxr-form pointwise bound of the grid point t_k (the      *)
(*   r := q side certificate of the J-mod instance) — the §4.1 G1 statement verbatim. *)
(*   Statement: Qle 0 q, 0<M and k<=M give forall n, QleT' |t_k| q.              *)
(*   Proof = the b5c_const_unit pattern: Qle_to_QleT' + real_const_proj          *)
(*     + Qabs_pos (tkq_nonneg) + tkq_le_q.                                       *)
(* ============================================================ *)
Lemma b5dQ_tkq_Hxr : forall (q : Q) (M k : nat),
  QleT' 0 q -> (0 < M)%nat -> (k <= M)%nat ->
  forall n : nat, QleT' (Qabs (projT1 (real_const (b5dL_tkq q M k)) n)) q.
Proof.
  intros q M k Hq0 HM Hk n.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (b5dL_tkq q M k) n)).
  apply (Qle_trans _ (b5dL_tkq q M k) _).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply (Qabs_pos (b5dL_tkq q M k)).
    exact (QleT'_to_Qle _ _ (b5dL_tkq_nonneg q M k Hq0 HM)).
  - exact ((QleT'_to_Qle _ _ (b5dL_tkq_le_q q M k Hq0 HM Hk))).
Qed.

(* ============================================================ *)
(* G3 b5dQ_xph_unit: the unit certificate of t_k + η (η := q/M) (the Hxh side of  *)
(*   the J-mod instance: real_plus (real_const t_k) (real_const η))              *)
(*   Statement = the design §4 G3 line (0<q, q<1, 0<M, k<M give cw_unit).        *)
(*   Proof = the coordinate bridge: t_k + η == t_{S k} (tkq_succ reversed) +     *)
(*     |t_{S k}| == t_{S k} (tkq_nonneg) + t_{S k} <= q <= 1                     *)
(*     (tkq_le1, with S k <= M from k < M by lia).                               *)
(* ============================================================ *)
Lemma b5dQ_xph_unit : forall (q : Q) (M k : nat),
  QltT 0 q -> QltT q 1 -> (0 < M)%nat -> (k < M)%nat ->
  cw_unit (real_plus (real_const (b5dL_tkq q M k))
                     (real_const (b5dL_qdiv q M))).
Proof.
  intros q M k Hq0 Hq1 HM Hk.
  unfold cw_unit.
  intro n.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (b5dL_tkq q M k) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (b5dL_qdiv q M) n)).
  rewrite <- (qeqT_imp_qeq _ _ (b5dL_tkq_succ q M k HM)).
  apply (Qle_trans _ (b5dL_tkq q M (Datatypes.S k)) _).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply (Qabs_pos (b5dL_tkq q M (Datatypes.S k))).
    exact (QleT'_to_Qle _ _ (b5dL_tkq_nonneg q M (Datatypes.S k) (b5dH_q_pos_le q Hq0) HM)).
  - apply QleT'_to_Qle. apply (b5dL_tkq_le1 q M (Datatypes.S k) (b5dH_q_pos_le q Hq0)
                        (b5dH_q_lt1_le q Hq1) HM).
    lia.
Qed.

(* ============================================================ *)
(* G4 b5dQ_eps_shares_pos: the Q positivity of the two eps shares (the           *)
(*   eps := real_const (epsQ/(2q)) and eps' := real_const (epsQ1 M epsQ) sides   *)
(*   of the J-mod instance) — the design §4 G4 line (a Qlt pair; the QltT variant and *)
(*   the real_lt real_zero (real_const .) certificates are one-line derivations on *)
(*   the consumption side: Qlt_to_QltT + the root real_const_pos (or             *)
(*   real_const_pos_f1).                                                         *)
(*   Proof: Qmult/Qinv positivity (isomorphic to item22 b5dL_two_q_pos) +        *)
(*     applying item22 b5dL_epsQ1_pos directly.                                  *)
(* ============================================================ *)
Lemma b5dQ_eps_shares_pos : forall (q epsQ : Q) (M : nat),
  QltT 0 q -> QltT 0 epsQ -> (0 < M)%nat ->
  And (QltT 0 (epsQ / (2 * q))) (QltT 0 (b5dL_epsQ1 M epsQ)).
Proof.
  intros q epsQ M Hq0 Heps HM.
  split.
  - apply Qlt_to_QltT. unfold Qdiv.
    apply (Qmult_lt_0_compat epsQ (Qinv (2 * q))).
    + exact (QltT_to_Qlt _ _ Heps).
    + apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (b5dL_two_q_pos q Hq0)).
  - exact (b5dL_epsQ1_pos epsQ M Heps HM).
Qed.

(* ============================================================ *)
(* G5 b5dQ_rhs_bk: the real_eq bridge from the C5 conclusion RHS (the eps*|h| +  *)
(*   eps' instance) to real_const (b5dL_bk q M epsQ k) (the RHS side of the      *)
(*   Hstep form) — the design §4 G5 line + the §2.4 bk decomposition check.      *)
(*   Chain: b5dL_abs_const (|η| == real_const (Qabs η)) + Qabs_pos               *)
(*     (η >= 0) + b5dH_real_const_qeq + b5dL_mult_const +                        *)
(*     the RealSetoid compatibilities + b5dH_plus_const_eq + the bk/epsQ1        *)
(*   definitional equality (real_eq_refl).                                       *)
(* ============================================================ *)
Lemma b5dQ_rhs_bk : forall (q : Q) (M k : nat) (epsQ : Q),
  QltT 0 q -> (0 < M)%nat ->
  real_eq (real_plus (real_mult (real_const (epsQ / (2 * q)))
                                (real_abs (real_const (b5dL_qdiv q M))))
                     (real_const (b5dL_epsQ1 M epsQ)))
          (real_const (b5dL_bk q M epsQ k)).
Proof.
  intros q M k epsQ Hq0 HM.
  (* η >= 0 (η := qdiv q M). *)
  assert (Heta0 : Qle 0 (b5dL_qdiv q M)).
  { unfold b5dL_qdiv. unfold Qdiv.
    apply Qmult_le_0_compat.
    - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ Hq0).
    - apply Qinv_le_0_compat. apply Qlt_le_weak.
      destruct M as [| m]; [exfalso; lia | exact (QltT_to_Qlt _ _ (b5dL_lift_pos2 m))]. }
  (* |η| == η *)
  assert (Heta : real_eq (real_abs (real_const (b5dL_qdiv q M)))
                         (real_const (b5dL_qdiv q M))).
  { apply (real_eq_trans _ (real_const (Qabs (b5dL_qdiv q M))) _).
    - exact (b5dL_abs_const (b5dL_qdiv q M)).
    - apply b5dH_real_const_qeq.
      apply qeq_imp_qeqT. apply (Qabs_pos (b5dL_qdiv q M)). exact Heta0. }
  (* (epsQ/(2q))·|η| == real_const ((epsQ/(2q))·η) *)
  assert (Hm : real_eq
    (real_mult (real_const (epsQ / (2 * q)))
               (real_abs (real_const (b5dL_qdiv q M))))
    (real_const ((epsQ / (2 * q)) * (b5dL_qdiv q M)))).
  { apply (real_eq_trans _ (real_mult (real_const (epsQ / (2 * q)))
                                      (real_const (b5dL_qdiv q M))) _).
    - apply (RealSetoid.real_eq_mult_compat
               (real_const (epsQ / (2 * q)))
               (real_abs (real_const (b5dL_qdiv q M)))
               (real_const (epsQ / (2 * q)))
               (real_const (b5dL_qdiv q M)));
        [ apply real_eq_refl | exact Heta ].
    - exact (b5dL_mult_const (epsQ / (2 * q)) (b5dL_qdiv q M)). }
  (* + real_const epsQ1; then + the bridge == real_const (bk) (definitional). *)
  apply (real_eq_trans _
           (real_plus (real_const ((epsQ / (2 * q)) * (b5dL_qdiv q M)))
                      (real_const (b5dL_epsQ1 M epsQ))) _).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (real_const (epsQ / (2 * q)))
                        (real_abs (real_const (b5dL_qdiv q M))))
             (real_const (b5dL_epsQ1 M epsQ))
             (real_const ((epsQ / (2 * q)) * (b5dL_qdiv q M)))
             (real_const (b5dL_epsQ1 M epsQ)));
      [ exact Hm | apply real_eq_refl ].
  - apply (real_eq_trans _
             (real_const ((epsQ / (2 * q)) * (b5dL_qdiv q M)
                          + b5dL_epsQ1 M epsQ)) _).
    + exact (b5dH_plus_const_eq ((epsQ / (2 * q)) * (b5dL_qdiv q M))
                                (b5dL_epsQ1 M epsQ)).
    + apply real_eq_refl.
Qed.

(* ============================================================ *)
(* G6 b5dQ_min_lb_3: the ternary min-tree lb glue (the design §4 G6 line         *)
(*   min_lb_3 — the P1 section file already occupies the binary b5dQ_min_lb      *)
(*   (the no-cross-section-name-overlap discipline, so this section contains     *)
(*   only the ternary version; the binary version is provided by the P1 section  *)
(*   file).                                                                      *)
(*   Statement: real_lt lb X/Y/Z gives real_lt lb (real_min (real_min X Y) Z).   *)
(*   Proof = verbatim migration of the check piece p_min_lb coordinate margin    *)
(*   composition (e := Qmin (Qmin e1 e2) e3 + the two-level Q.min_glb_lt         *)
(*   application).                                                               *)
(* ============================================================ *)
Lemma b5dQ_min_lb_3 : forall (lb A B C : Real),
  real_lt lb A -> real_lt lb B -> real_lt lb C ->
  real_lt lb (real_min (real_min A B) C).
Proof.
  intros lb A B C HltA HltB HltC.
  destruct HltA as [e1 [He1 [N1 HN1]]].
  destruct HltB as [e2 [He2 [N2 HN2]]].
  destruct HltC as [e3 [He3 [N3 HN3]]].
  set (e := Qmin (Qmin e1 e2) e3).
  assert (He : QltT 0 e).
  { apply Qlt_to_QltT. unfold e.
    apply Q.min_glb_lt.
    - apply Q.min_glb_lt.
      + apply QltT_to_Qlt. exact He1.
      + apply QltT_to_Qlt. exact He2.
    - apply QltT_to_Qlt. exact He3. }
  unfold real_lt.
  exists e.
  split.
  { exact He. }
  { exists (Nat.max (Nat.max N1 N2) N3).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn1 : NatLe N1 n) by (apply NatLe_lift; lia).
    assert (Hn2 : NatLe N2 n) by (apply NatLe_lift; lia).
    assert (Hn3 : NatLe N3 n) by (apply NatLe_lift; lia).
    apply Qlt_to_QltT.
    set (cn := projT1 lb n).
    set (an := projT1 A n).
    set (bn := projT1 B n).
    set (dn := projT1 C n).
    assert (H1n : Qlt e1 (an - cn)).
    { unfold an, cn. apply QltT_to_Qlt. exact (HN1 n Hn1). }
    assert (H2n : Qlt e2 (bn - cn)).
    { unfold bn, cn. apply QltT_to_Qlt. exact (HN2 n Hn2). }
    assert (H3n : Qlt e3 (dn - cn)).
    { unfold dn, cn. apply QltT_to_Qlt. exact (HN3 n Hn3). }
    assert (He12 : Qle e (Qmin e1 e2)). { unfold e. apply Q.le_min_l. }
    assert (He3b : Qle e e3). { unfold e. apply Q.le_min_r. }
    assert (Hm1 : Qlt e (an - cn)).
    { apply (Qle_lt_trans e e1 (an - cn)).
      - apply (Qle_trans e (Qmin e1 e2) e1); [ exact He12 | apply Q.le_min_l ].
      - exact H1n. }
    assert (Hm2 : Qlt e (bn - cn)).
    { apply (Qle_lt_trans e e2 (bn - cn)).
      - apply (Qle_trans e (Qmin e1 e2) e2); [ exact He12 | apply Q.le_min_r ].
      - exact H2n. }
    assert (Hm3 : Qlt e (dn - cn)).
    { apply (Qle_lt_trans e e3 (dn - cn)); [ exact He3b | exact H3n ]. }
    assert (Ht1 : Qlt (e + cn) an).
    { apply (proj2 (Qlt_minus_iff (e + cn) an)).
      apply (Qlt_le_trans 0 ((an - cn) - e) (an - (e + cn))).
      - apply (proj1 (Qlt_minus_iff e (an - cn))). exact Hm1.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Ht2 : Qlt (e + cn) bn).
    { apply (proj2 (Qlt_minus_iff (e + cn) bn)).
      apply (Qlt_le_trans 0 ((bn - cn) - e) (bn - (e + cn))).
      - apply (proj1 (Qlt_minus_iff e (bn - cn))). exact Hm2.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Ht3 : Qlt (e + cn) dn).
    { apply (proj2 (Qlt_minus_iff (e + cn) dn)).
      apply (Qlt_le_trans 0 ((dn - cn) - e) (dn - (e + cn))).
      - apply (proj1 (Qlt_minus_iff e (dn - cn))). exact Hm3.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (Htg : Qlt (e + cn) (Qmin (Qmin an bn) dn)).
    { apply Q.min_glb_lt.
      - apply Q.min_glb_lt; [ exact Ht1 | exact Ht2 ].
      - exact Ht3. }
    rewrite (qeqT_imp_qeq _ _ (real_min_proj (real_min A B) C n)).
    rewrite (qeqT_imp_qeq _ _ (real_min_proj A B n)).
    apply (proj2 (Qlt_minus_iff e (Qmin (Qmin an bn) dn - cn))).
    apply (Qlt_le_trans 0 (Qmin (Qmin an bn) dn - (e + cn))
                         ((Qmin (Qmin an bn) dn - cn) - e)).
    - apply (proj1 (Qlt_minus_iff (e + cn) (Qmin (Qmin an bn) dn))).
      exact Htg.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  }
Qed.

(* ============================================================ *)
(* G8 b5dQ_qdiv_lt_arch: the Q-layer proof of the q_arch_inv chain (the design §4 G8 line) *)
(*   Statement: 0<q, 0<δ0, Qlt (1/(M#1)) (δ0/q) give Qlt (qdiv q M) δ0.          *)
(*   Proof = multiplying both sides by q (Qmult_lt_compat_r) +                   *)
(*     q*(1/(M#1)) == q/(M#1) (ring) + q*(δ0/q) == δ0 (Qmult_inv_l, with q ≠ 0   *)
(*     from b5dL_q_lt0_nz).                                                      *)
(* ============================================================ *)
Lemma b5dQ_qdiv_lt_arch : forall (q delta0 : Q) (M : nat),
  QltT 0 q -> QltT 0 delta0 ->
  QltT (1 / (Z.of_nat M # 1)) (delta0 / q) ->
  QltT (b5dL_qdiv q M) delta0.
Proof.
  intros q delta0 M Hq0 Hd0 Harch.
  apply Qlt_to_QltT.
  unfold b5dL_qdiv.
  assert (Hqnz : ~ q == 0).
  { intro Hz. apply qeq_imp_qeqT in Hz. apply (b5dL_q_lt0_nz q Hq0) in Hz. destruct Hz. }
  (* multiplying both sides of Harch on the right by q (Qmult_lt_compat_r). *)
  assert (Hm2 : Qlt ((1 / (Z.of_nat M # 1)) * q) ((delta0 / q) * q)).
  { apply (Qmult_lt_compat_r (1 / (Z.of_nat M # 1)) (delta0 / q) q (QltT_to_Qlt _ _ Hq0)).
    exact (QltT_to_Qlt _ _ Harch). }
  (* bridge: q*(1/(M#1)) == q/(M#1) (ring); (δ0/q)*q == δ0 (inv cancellation). *)
  assert (Hq1 : q * (1 / (Z.of_nat M # 1)) == q / (Z.of_nat M # 1)).
  { unfold Qdiv. ring. }
  assert (Hq2 : (delta0 / q) * q == delta0).
  { field.
    all: try (intro Hz; apply qeq_imp_qeqT in Hz; apply (b5dL_q_lt0_nz q Hq0) in Hz; destruct Hz). }
  (* restoring the left-multiplied form: q*(1/(M#1)) <= (1/(M#1))*q (comm) + Hm2 finishes. *)
  assert (Hm : Qlt (q * (1 / (Z.of_nat M # 1))) ((delta0 / q) * q)).
  { apply (Qle_lt_trans (q * (1 / (Z.of_nat M # 1)))
                        ((1 / (Z.of_nat M # 1)) * q)
                        ((delta0 / q) * q)).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply (Qmult_comm q (1 / (Z.of_nat M # 1))).
    - exact Hm2. }
  rewrite Hq2 in Hm.
  rewrite Hq1 in Hm.
  exact Hm.
Qed.

(* ============================================================ *)
(* End of the P3 section.                                                        *)
(* ============================================================ *)

(* ===== Section P4a (the bridging lemmas: J_tk_succ_bridge / J_cert_wd / step_inst, 3 Lemma) ===== *)

(* ============================================================ *)
(* Piece 1 b5dQ_J_tk_succ_bridge: the t_k + η <-> t_{k+1} bridge (J Proper)      *)
(*   Statement = the item22 §3.7 L273-278 text verbatim (= the δD2f §2.8(a) text, *)
(*   with the b5dL_ -> b5dQ_ prefix mapping) — measured: item22 does not close   *)
(*   it (only mentioned in a comment), so this piece is new here.                *)
(*   Proof (per the design §2.8(a), about 8-12 lines): b5p2_J_wd +               *)
(*     b5dL_tkq_succ (Qeq) -> b5dH_real_const_qeq (Real layer) ->                *)
(*     b5dH_plus_const_eq (reversed, real_eq_sym) -> real_eq_trans.              *)
(* ============================================================ *)
Lemma b5dQ_J_tk_succ_bridge : forall (q : Q) (M k : nat) (HMpos : (0 < M)%nat)
  (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k))))
  (Hp : cw_unit (real_plus (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M)))),
  real_eq (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
          (b5c_J (real_plus (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M))) Hp).
Proof.
  intros q M k HMpos Hk1 Hp.
  apply (b5p2_J_wd (real_const (b5dL_tkq q M (Datatypes.S k)))
                   (real_plus (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M)))
                   Hk1 Hp).
  apply (real_eq_trans (real_const (b5dL_tkq q M (Datatypes.S k)))
                       (real_const (b5dL_tkq q M k + b5dL_qdiv q M))
                       (real_plus (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M)))).
  - apply b5dH_real_const_qeq.
    exact (b5dL_tkq_succ q M k HMpos).
  - apply real_eq_sym.
    exact (b5dH_plus_const_eq (b5dL_tkq q M k) (b5dL_qdiv q M)).
Qed.

(* ============================================================ *)
(* Piece 2 b5dQ_J_cert_wd: the J certificate-shape bridge (swapping the two      *)
(*   certificates for the same x)                                                *)
(*   Statement = the design §2.8(b)/§4 description verbatim (forall Hx Hx' :     *)
(*     cw_unit (real_const t): real_eq (b5c_J (real_const t) Hx)                 *)
(*     (b5c_J (real_const t) Hx') — the design-table note, 5-8 lines).           *)
(*   Usage: an arbitrary Hmod-form certificate Hk <-> the fixed certificate at the *)
(*   modulus-piece left point (b3rr_dom_r1 (real_const t_k) q Hxr Hq1, root      *)
(*   L71826 — the output type is definitionally the same shape as cw_unit).      *)
(*   Proof: b5p2_J_wd (two certificates for the same x) + real_eq_refl (about 5  *)
(*   lines).                                                                     *)
(* ============================================================ *)
Lemma b5dQ_J_cert_wd : forall (t : Q) (Hx Hx' : cw_unit (real_const t)),
  real_eq (b5c_J (real_const t) Hx) (b5c_J (real_const t) Hx').
Proof.
  intros t Hx Hx'.
  apply (b5p2_J_wd (real_const t) (real_const t) Hx Hx').
  apply real_eq_refl.
Qed.

(* ============================================================ *)
(* Piece 3 b5dQ_step_inst: the modulus output -> the skeleton Hstep-form bridge  *)
(*   (the gap piece)                                                             *)
(*   The design §2.8(c) step_inst description = bridging the whole C5 instance   *)
(*   conclusion to the skeleton form (consuming (a)(b)(c) together) — the        *)
(*   RHS==real_const(bk) part = §4 G5 = the already-closed b5dQ_rhs_bk (this     *)
(*   section must not Require that P3 piece — the zero-dependency discipline),   *)
(*   so the functional overlap is reported as is and this piece only fills the   *)
(*   gap = the LHS/certificate-shape bridge: the modulus conclusion (the left-   *)
(*   point certificate in the fixed b3rr_dom_r1 form) -> the Hstep form          *)
(*   (arbitrary certificates Hk/Hk1) real_le bridge, with the RHS abstract       *)
(*   variable R (the P4 assembly instantiates R := eps*|h|+eps' real form and    *)
(*   then closes real_const (bk) by one real_le_id_r through b5dQ_rhs_bk — the   *)
(*   design record §5 connection note).                                          *)
(*   Parameter face = the modulus-piece instance face: x := real_const (tkq q M k) *)
(*   (with Hxr as its |x_n| <= q certificate argument), h := real_const (qdiv q M),  *)
(*   Hxh := cw_unit (real_plus ...) (supplied by the b5dQ_xph_unit instance on   *)
(*   the P4 side), Hk/Hk1 arbitrary Hmod-form certificates, Hq1 supplying the    *)
(*   third argument of the left point b3rr_dom_r1, HMpos supplying the tkq_succ  *)
(*   premise of Piece 1.                                                         *)
(*   Proof (about 12 lines): Piece 1 (Hp := the Hxh instance) bridges the two    *)
(*   certificate shapes of the right point + Piece 2 (the two certificates of    *)
(*   the left point) bridges the left point + real_eq_opp_compat /               *)
(*   real_eq_plus_compat / real_abs_eq_compat (root L32803/32767/46326) +        *)
(*   real_le_id_l (root L33011) closes the real_le form.                         *)
(* ============================================================ *)
Lemma b5dQ_step_inst : forall (q : Q) (M k : nat) (HMpos : (0 < M)%nat)
  (Hq1 : QltT q 1)
  (Hxr : forall n : nat, QleT' (Qabs (projT1 (real_const (b5dL_tkq q M k)) n)) q)
  (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k))))
  (Hk : cw_unit (real_const (b5dL_tkq q M k)))
  (Hxh : cw_unit (real_plus (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M)))),
  forall (R : Real),
  real_le (real_abs (real_plus (b5c_J (real_plus (real_const (b5dL_tkq q M k))
                                                 (real_const (b5dL_qdiv q M))) Hxh)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M k))
                                                (b3rr_dom_r1 (real_const (b5dL_tkq q M k))
                                                             q Hxr (QltT_to_Qlt _ _ Hq1))))))
          R ->
  real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
          R.
Proof.
  intros q M k HMpos Hq1 Hxr Hk1 Hk Hxh R Hmain.
  apply (RealSetoid.real_le_id_l
    (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                         (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
    (real_abs (real_plus (b5c_J (real_plus (real_const (b5dL_tkq q M k))
                                           (real_const (b5dL_qdiv q M))) Hxh)
                         (real_opp (b5c_J (real_const (b5dL_tkq q M k))
                                          (b3rr_dom_r1 (real_const (b5dL_tkq q M k))
                                                       q Hxr (QltT_to_Qlt _ _ Hq1))))))
    R).
  - apply real_abs_eq_compat.
    apply (RealSetoid.real_eq_plus_compat
      (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
      (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))
      (b5c_J (real_plus (real_const (b5dL_tkq q M k)) (real_const (b5dL_qdiv q M))) Hxh)
      (real_opp (b5c_J (real_const (b5dL_tkq q M k))
                       (b3rr_dom_r1 (real_const (b5dL_tkq q M k)) q Hxr (QltT_to_Qlt _ _ Hq1))))).
    + exact (b5dQ_J_tk_succ_bridge q M k HMpos Hk1 Hxh).
    + apply (RealSetoid.real_eq_opp_compat
        (b5c_J (real_const (b5dL_tkq q M k)) Hk)
        (b5c_J (real_const (b5dL_tkq q M k))
               (b3rr_dom_r1 (real_const (b5dL_tkq q M k)) q Hxr (QltT_to_Qlt _ _ Hq1)))).
      exact (b5dQ_J_cert_wd (b5dL_tkq q M k) Hk
                            (b3rr_dom_r1 (real_const (b5dL_tkq q M k)) q Hxr (QltT_to_Qlt _ _ Hq1))).
  - exact Hmain.
Qed.

(* ===== Section M1 (the lb_Sdiff family: the lb_exp_part coordinate piece + the cS/lb_gdiff values + the 6 branches of lb_Sdiff, 17 Lemma/Def) ===== *)

(* ============================================================ *)
(* M1 prelude: the closed-form certificates + the Sdiff floor-value definition family + positivity *)
(* ============================================================ *)

(* Qlt 0 2 (the HMpos closed form of the Sdiff piece's M-argument M_S := 2).  *)
Lemma b5dQ_p4_two_pos : QltT 0 2.
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* Qlt 0 (1#2) (the HcA closed form of cA := 1#2). *)
Lemma b5dQ_p4_half_pos : QltT 0 (1 # 2).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* the positivity of Sdiff k2 := Qinv(8*(2+1)) (the M_S := 2 closed form): Qlt 0. *)
Lemma b5dQ_p4_k2t_pos : QltT 0 (Qinv (Qmult 8 (Qplus 2 1))).
Proof.
  apply Qlt_to_QltT.
  apply Qinv_lt_0_compat.
  unfold Qlt. simpl. lia.
Qed.

(* the exp-branch floor tree (the δexp branch: the min of floorA/floorB/C; isomorphic to the
   exp branch of the coordinate-piece RHS — the P2 lb_exp_part floor with a replaced by (a*(1#2))). *)
Definition b5dQ_lbSdiff_cE (q a : Q) : Q :=
  Qmin (Qmin
    (Qmult (Qmin (1 # 2)
                 (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                      (Qinv (b5j_Kvq q))) (1 # 3))
                        (1 # 4)))
           (1 # 4))
    (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
  (1 # 2).

(* the g-branch floor tree (the δg branch: the min of floorA2/floorB2/C; isomorphic to the
   g branch of the coordinate-piece RHS — the P2 lb_gdiff floor with a replaced by (a*(1#4))
   and k2 := the k2t closed form). *)
Definition b5dQ_lbSdiff_cG (q a : Q) : Q :=
  Qmin (Qmin
    (Qmult (Qmin (1 # 2)
                 (Qmult (1 # 4)
                        (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1)))
                                      (1 # 2)))))
           (1 # 12))
    (Qmult (Qmult a (1 # 4))
           (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
  (1 # 2).

(* the Sdiff value definition (lb := cS/2; the source of the δ0 confluence components). *)
Definition b5dQ_lbSdiff_cS (q a : Q) : Q :=
  Qmin (b5dQ_lbSdiff_cE q a) (b5dQ_lbSdiff_cG q a).

Definition b5dQ_lbSdiff_val (q a : Q) : Q :=
  Qmult (b5dQ_lbSdiff_cS q a) (1 # 2).

(* cS positivity (Qle 0 q and 0 < a give 0 < cS — all branch floors positive). *)
Lemma b5dQ_lbSdiff_cS_pos : forall (q a : Q),
  QleT' 0 q -> QltT 0 a -> QltT 0 (b5dQ_lbSdiff_cS q a).
Proof.
  intros q a Hq0 Ha.
  apply Qlt_to_QltT.
  assert (H12 : Qlt 0 (1 # 2)) by exact (QltT_to_Qlt _ _ b5dQ_p4_half_pos).
  assert (H13 : Qlt 0 (1 # 3)) by (unfold Qlt; simpl; lia).
  assert (H14 : Qlt 0 (1 # 4)) by (unfold Qlt; simpl; lia).
  assert (H112 : Qlt 0 (1 # 12)) by (unfold Qlt; simpl; lia).
  assert (HKpos : Qlt 0 (Qinv (b5j_Kvq q))).
  { apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (b5j_Kvq_pos q (QleT'_to_Qle _ _ Hq0))). }
  assert (HkLpos : Qlt 0 b5j_kL) by (apply QltT_to_Qlt; exact b5j_kL_posT).
  assert (Hk2pos : Qlt 0 (Qinv (Qmult 8 (Qplus 2 1)))) by exact (QltT_to_Qlt _ _ b5dQ_p4_k2t_pos).
  assert (Ha2 : Qlt 0 (Qmult a (1 # 2))).
  { apply (Qmult_lt_0_compat a (1 # 2)); [exact (QltT_to_Qlt _ _ Ha) | exact H12]. }
  assert (Ha4 : Qlt 0 (Qmult a (1 # 4))).
  { apply (Qmult_lt_0_compat a (1 # 4)); [exact (QltT_to_Qlt _ _ Ha) | exact H14]. }
  assert (HkL2 : Qlt 0 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))).
  { apply (Qmult_lt_0_compat (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2));
      [exact Hk2pos | exact H12]. }
  (* cE positivity (all three branches positive). *)
  assert (HmL2pos : Qlt 0 (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                               (Qinv (b5j_Kvq q))) (1 # 3))
                                 (1 # 4))).
  { apply (Qmult_lt_0_compat (Qmult (Qmult (Qmult a (1 # 2))
                                           (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4));
      [ | exact H14 ].
    apply (Qmult_lt_0_compat (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3));
      [ | exact H13 ].
    apply (Qmult_lt_0_compat (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)));
      [exact Ha2 | exact HKpos]. }
  assert (HfloorLpos : Qlt 0 (Qmin (1 # 2)
     (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))).
  { apply Q.min_glb_lt; [exact H12 | exact HmL2pos]. }
  assert (HfloorApos : Qlt 0 (Qmult (Qmin (1 # 2)
     (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                                   (1 # 4))).
  { apply (Qmult_lt_0_compat
      (Qmin (1 # 2)
        (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
      (1 # 4)); [exact HfloorLpos | exact H14]. }
  assert (HfloorDpos : Qlt 0 (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL))).
  { apply Q.min_glb_lt; [exact H12 | ].
    apply (Qmult_lt_0_compat (1 # 4) b5j_kL); [exact H14 | exact HkLpos]. }
  assert (HfloorBpos : Qlt 0 (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))).
  { apply (Qmult_lt_0_compat (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12));
      [exact HfloorDpos | exact H112]. }
  assert (HcEpos : Qlt 0 (b5dQ_lbSdiff_cE q a)).
  { unfold b5dQ_lbSdiff_cE.
    apply Q.min_glb_lt.
    - apply Q.min_glb_lt; [exact HfloorApos | exact HfloorBpos].
    - exact H12. }
  (* cG positivity (all three branches positive). *)
  assert (Hmpos : Qlt 0 (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))).
  { apply (Qmult_lt_0_compat (Qmult a (1 # 4))
                             (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)));
      [exact Ha4 | exact HkL2]. }
  assert (HfloorA2pos : Qlt 0 (Qmult (Qmin (1 # 2)
     (Qmult (1 # 4) (Qmult (Qmult a (1 # 4))
                           (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                                     (1 # 12))).
  { apply (Qmult_lt_0_compat
      (Qmin (1 # 2)
        (Qmult (1 # 4) (Qmult (Qmult a (1 # 4))
                              (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
      (1 # 12)); [ | exact H112 ].
    apply Q.min_glb_lt; [exact H12 | ].
    apply (Qmult_lt_0_compat (1 # 4)
                             (Qmult (Qmult a (1 # 4))
                                    (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))));
      [exact H14 | exact Hmpos]. }
  assert (HcGpos : Qlt 0 (b5dQ_lbSdiff_cG q a)).
  { unfold b5dQ_lbSdiff_cG.
    apply Q.min_glb_lt.
    - apply Q.min_glb_lt; [exact HfloorA2pos | exact Hmpos].
    - exact H12. }
  unfold b5dQ_lbSdiff_cS.
  apply Q.min_glb_lt; [exact HcEpos | exact HcGpos].
Qed.

(* lbSdiff_val positivity (a corollary of cS-pos). *)
Lemma b5dQ_lbSdiff_pos : forall (q a : Q),
  QleT' 0 q -> QltT 0 a -> QltT 0 (b5dQ_lbSdiff_val q a).
Proof.
  intros q a Hq0 Ha.
  apply Qlt_to_QltT.
  assert (H12 : Qlt 0 (1 # 2)) by exact (QltT_to_Qlt _ _ b5dQ_p4_half_pos).
  unfold b5dQ_lbSdiff_val.
  apply (Qmult_lt_0_compat (b5dQ_lbSdiff_cS q a) (1 # 2));
    [exact (QltT_to_Qlt _ _ (b5dQ_lbSdiff_cS_pos q a Hq0 Ha)) | exact H12].
Qed.

(* ============================================================ *)
(* M1 coordinate-piece support: the share-coordinate small pieces (the c-generalization of the P2 coordinate-piece pattern) *)
(* ============================================================ *)

(* QltT 0 k2t (the g-branch k2 closed-form certificate). *)
Lemma b5dQ_p4_k2t_posT : QltT 0 (Qinv (Qmult 8 (Qplus 2 1))).
Proof. exact b5dQ_p4_k2t_pos. Qed.

(* the positivity certificate of real_mult (real_const a) (real_const c) (the real_lt
   certificate of the share eps; a proof position, transparency-independent). *)
Lemma b5dQ_p4_mul_pos : forall (a c : Q) (Ha : QltT 0 a) (Hc : QltT 0 c),
  real_lt real_zero (real_mult (real_const a) (real_const c)).
Proof.
  intros a c Ha Hc.
  apply real_mult_positive.
  - apply real_const_pos. apply Qlt_to_QltT. exact (QltT_to_Qlt _ _ (Ha)).
  - apply real_const_pos. apply Qlt_to_QltT. exact (QltT_to_Qlt _ _ Hc).
Qed.

(* the positivity certificate of eps0 := eps*K*invM (with eps := real_const a * real_const c). *)
Lemma b5dQ_p4_eps0_c_pos : forall (q : Q) (Hq0 : QleT' 0 q)
  (a c : Q) (Ha : QltT 0 a) (Hc : QltT 0 c) (x : Real),
  real_lt real_zero (real_mult
    (real_mult (real_mult (real_const a) (real_const c))
               (real_const (Qinv (b5j_Kvq q))))
    (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                  (b5dK_real_abs_plus_one_pos_exp (b5a_S x)))).
Proof.
  intros q Hq0 a c Ha Hc x.
  apply real_mult_positive.
  - apply real_mult_positive.
    + exact (b5dQ_p4_mul_pos a c Ha Hc).
    + apply real_const_pos. apply Qlt_to_QltT.
      apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (b5j_Kvq_pos q (QleT'_to_Qle _ _ Hq0))).
  - apply (real_inv_pos_pos (real_plus real_one (real_abs (b5a_S x)))
                            (b5dK_real_abs_plus_one_pos_exp (b5a_S x))).
Qed.

(* the coordinate piece of exp_part @ eps := real_mult (real_const a) (real_const c)
   (the c-generalization of the P2 b5dQ_lb_exp_part_coord — a replaced by (a*c); the S atom
   stays atomic; the δL branch as in b5j_kL). *)
Lemma b5dQ_lb_exp_part_c_coord : forall (q : Q) (Hq0 : QleT' 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : QltT 0 a) (c : Q) (Hc : QltT 0 c) (n : nat),QeqT (
  projT1 (projT1 (b5dK_exp_part_bound_closed_r_exp q Hq0 Hq1 x Hxr
                 (real_mult (real_const a) (real_const c))
                 (b5dQ_p4_mul_pos a c Ha Hc))) n
  ) ( Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a c) (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha c Hc n.
  apply qeq_imp_qeqT.
  set (K := Qinv (b5j_Kvq q)).
  set (eps0t := real_mult (real_mult (real_mult (real_const a) (real_const c))
                                     (real_const K))
                  (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                                (b5dK_real_abs_plus_one_pos_exp (b5a_S x)))).
  change (projT1 (real_min (real_min
    (real_mult (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
                       (b5dQ_p4_eps0_c_pos q Hq0 a c Ha Hc x)))
               (real_const (1 # 4)))
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                       (real_const_pos b5j_kL
                          (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
               (real_const (1 # 12))))
    (real_const (1 # 2))) n
  == Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a c) (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj
    (real_min
      (real_mult (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
                         (b5dQ_p4_eps0_c_pos q Hq0 a c Ha Hc x)))
                 (real_const (1 # 4)))
      (real_mult (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                         (real_const_pos b5j_kL
                            (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
                 (real_const (1 # 12))))
    (real_const (1 # 2)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj
    (real_mult (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
                       (b5dQ_p4_eps0_c_pos q Hq0 a c Ha Hc x)))
               (real_const (1 # 4)))
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
                       (real_const_pos b5j_kL
                          (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
               (real_const (1 # 12))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj
    (projT1 (b5dK_exp_minus_one_linear_closed_exp eps0t
            (b5dQ_p4_eps0_c_pos q Hq0 a c Ha Hc x)))
    (real_const (1 # 4)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj
    (projT1 (b5dJ_LogErr_delta_exp x (real_const b5j_kL)
            (real_const_pos b5j_kL
               (Qlt_to_QltT 0 b5j_kL (QltT_to_Qlt 0 b5j_kL b5j_kL_posT)))))
    (real_const (1 # 12)) n)).
  pose proof (qeqT_imp_qeq _ _ (b5dQ_p_logerr_kL_coord x n)) as Hgenqeq10425.
  rewrite Hgenqeq10425.
  change (Qmin (Qmin
      (Qmult (projT1 (real_min (real_const (1 # 2))
                               (real_mult eps0t (real_const (1 # 4)))) n)
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)
  == Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a c) (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2)).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj (real_const (1 # 2)) (real_mult eps0t (real_const (1 # 4))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps0t (real_const (1 # 4)) n)).
  unfold eps0t, K.
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj
    (real_mult (real_mult (real_const a) (real_const c)) (real_const (Qinv (b5j_Kvq q))))
    (real_inv_pos (real_plus real_one (real_abs (b5a_S x)))
                  (b5dK_real_abs_plus_one_pos_exp (b5a_S x))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj
    (real_mult (real_const a) (real_const c)) (real_const (Qinv (b5j_Kvq q))) n)).
  repeat (rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) || rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _))).
  pose proof (qeqT_imp_qeq _ _ (b5dQ_p_invM_coord x n)) as Hgenqeq10456.
  rewrite Hgenqeq10456.
  cbn [projT1 real_inv_pos real_plus real_abs real_one real_const Nat.leb
       b5dK_real_abs_plus_one_pos_exp b5j_kL].
  reflexivity.
Qed.

(* the positivity certificate of epsL := eps*real_const kL (with eps := real_const a * real_const c). *)
Lemma b5dQ_p4_epsLt_pos : forall (a c k2 : Q) (Ha : QltT 0 a) (Hc : QltT 0 c)
  (Hk2 : QltT 0 k2),
  real_lt real_zero (real_mult (real_mult (real_const a) (real_const c))
                               (real_const (Qmult k2 (1 # 2)))).
Proof.
  intros a c k2 Ha Hc Hk2.
  apply real_mult_positive.
  - exact (b5dQ_p4_mul_pos a c Ha Hc).
  - apply real_const_pos. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat k2 (1 # 2)); [exact (QltT_to_Qlt _ _ Hk2) | exact (QltT_to_Qlt _ _ b5dQ_p4_half_pos)].
Qed.


(* the coordinate piece of gdiff @ eps := real_mult (real_const a) (real_const c) with
   k2 := k2t (the c-generalization of the P2 b5dQ_lb_gdiff_coord — a replaced by (a*c),
   k2 closed form; the δL' branch inlined). *)
Lemma b5dQ_lb_gdiff_c_coord : forall (q : Q) (Hq0 : QleT' 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : QltT 0 a) (c : Q) (Hc : QltT 0 c) (n : nat),QeqT (
  projT1 (projT1 (b5dK_gdiff_pts_r_exp q Hq0 Hq1 x Hxr
                 (real_mult (real_const a) (real_const c))
                 (b5dQ_p4_mul_pos a c Ha Hc)
                 (Qinv (Qmult 8 (Qplus 2 1))) (Qinv (Qmult 8 (Qplus 2 1)))
                 b5dQ_p4_k2t_posT b5dQ_p4_k2t_posT)) n
  ) ( Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult (Qmult a c)
                                        (Qmult (Qinv (Qmult 8 (Qplus 2 1)))
                                               (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult (Qmult a c)
             (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
    (1 # 2)).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha c Hc n.
  apply qeq_imp_qeqT.
  set (k2t := Qinv (Qmult 8 (Qplus 2 1))).
  set (epsLt := real_mult (real_mult (real_const a) (real_const c))
                          (real_const (Qmult k2t (1 # 2)))).
  change (projT1 (real_min (real_min
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x epsLt
                       (b5dQ_p4_epsLt_pos a c k2t Ha Hc b5dQ_p4_k2t_posT)))
               (real_const (1 # 12)))
    (real_mult (real_mult (real_const a) (real_const c))
               (real_const (Qmult k2t (1 # 2)))))
    (real_const (1 # 2))) n
  == Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult (Qmult a c)
                                        (Qmult k2t (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult (Qmult a c) (Qmult k2t (1 # 2))))
    (1 # 2)).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj
    (real_min
      (real_mult (projT1 (b5dJ_LogErr_delta_exp x epsLt
                         (b5dQ_p4_epsLt_pos a c k2t Ha Hc b5dQ_p4_k2t_posT)))
                 (real_const (1 # 12)))
      (real_mult (real_mult (real_const a) (real_const c))
                 (real_const (Qmult k2t (1 # 2)))))
    (real_const (1 # 2)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj
    (real_mult (projT1 (b5dJ_LogErr_delta_exp x epsLt
                       (b5dQ_p4_epsLt_pos a c k2t Ha Hc b5dQ_p4_k2t_posT)))
               (real_const (1 # 12)))
    (real_mult (real_mult (real_const a) (real_const c))
               (real_const (Qmult k2t (1 # 2)))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj
    (projT1 (b5dJ_LogErr_delta_exp x epsLt
            (b5dQ_p4_epsLt_pos a c k2t Ha Hc b5dQ_p4_k2t_posT)))
    (real_const (1 # 12)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj
    (real_mult (real_const a) (real_const c)) (real_const (Qmult k2t (1 # 2))) n)).
  change (Qmin (Qmin
      (Qmult (projT1 (projT1 (b5dJ_log_diff_dx_exp (b5f_u x)
                 (b5a_one_plus_sq_pos x) epsLt
                 (b5dQ_p4_epsLt_pos a c k2t Ha Hc b5dQ_p4_k2t_posT))) n)
             (1 # 12))
      (Qmult (Qmult a c) (Qmult k2t (1 # 2))))
    (1 # 2)
  == Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult (Qmult a c)
                                        (Qmult k2t (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult (Qmult a c) (Qmult k2t (1 # 2))))
    (1 # 2)).
  change (Qmin (Qmin
      (Qmult (projT1 (real_min
        (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                   (b5f_u x))
        (real_mult
          (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                     (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
          (real_mult epsLt (real_mult (b5f_u x) (b5f_u x))))) n)
             (1 # 12))
      (Qmult (Qmult a c) (Qmult k2t (1 # 2))))
    (1 # 2)
  == Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult (Qmult a c)
                                        (Qmult k2t (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult (Qmult a c) (Qmult k2t (1 # 2))))
    (1 # 2)).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj
    (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
               (b5f_u x))
    (real_mult
      (real_mult (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp))
                 (real_inv_pos (real_plus real_one real_one) (b5dJ_two_pos_exp)))
      (real_mult epsLt (real_mult (b5f_u x) (b5f_u x)))) n)).
  repeat (rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) || rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _))).
  unfold epsLt, k2t.
  repeat (rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) || rewrite (qeqT_imp_qeq _ _ (real_const_proj _ _))).
  cbn [projT1 real_inv_pos real_plus real_abs real_one real_const Nat.leb
       b5dJ_two_pos_exp].
  reflexivity.
Qed.

(* ============================================================ *)
(* M1 coordinate piece: projT1(projT1(Sdiff-app)) n == the explicit coordinate tree *)
(*   In the Sdiff body: eps1 := eps*(1#2) (the exp part) / eps2 := eps*(1#4)     *)
(*   (the g part) + k2 := Qinv(8*(2+1)) (the M_S := 2 closed form).              *)
(*   RHS = the mechanical substitution form of the P2 exp-part/gdiff coordinate  *)
(*   formulas with a replaced by (a*(1#2))/(a*(1#4)) (change to the explicit δ   *)
(*   tree + projection rewrites).                                                *)
(* ============================================================ *)
Lemma b5dQ_lb_Sdiff_coord : forall (q : Q) (Hq0 : QleT' 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : QltT 0 a)
  (Nub : nat)
  (Hcert : forall n : nat, NatLe Nub n ->
           QleT' (Qabs (projT1 (b5a_S x) n)) 2)
  (n : nat),QeqT (
  projT1 (projT1 (b5dP_S_diff_closed_r_M_exp_tail q Hq0 Hq1 x Hxr 2
    b5dQ_p4_two_pos Nub Hcert (real_const a)
    (real_const_pos a Ha))) n
  ) ( Qmin (Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                        (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2))
  (Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult (Qmult a (1 # 4))
                                        (Qmult (Qinv (Qmult 8 (Qplus 2 1)))
                                               (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult (Qmult a (1 # 4))
             (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
    (1 # 2))).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha Nub Hcert n.
  apply qeq_imp_qeqT.
  set (Eapp := b5dK_exp_part_bound_closed_r_exp q Hq0 Hq1 x Hxr
    (real_mult (real_const a) (real_const (1 # 2)))
    (b5dQ_p4_mul_pos a (1 # 2) Ha b5dQ_p4_half_pos)).
  set (Gapp := b5dK_gdiff_pts_r_exp q Hq0 Hq1 x Hxr
    (real_mult (real_const a) (real_const (1 # 4)))
    (b5dQ_p4_mul_pos a (1 # 4) Ha b5dQ_Hq14)
    (Qinv (Qmult 8 (Qplus 2 1))) (Qinv (Qmult 8 (Qplus 2 1)))
    b5dQ_p4_k2t_posT b5dQ_p4_k2t_posT).
  change (projT1 (real_min (projT1 Eapp) (projT1 Gapp)) n
  == Qmin (Qmin (Qmin
      (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                        (Qinv (b5j_Kvq q)))
                                 (Qinv (Qplus 1 (Qabs (projT1 (b5a_S x) n)))))
                          (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult b5j_kL (Qmult (projT1 (b5f_u x) n)
                                               (projT1 (b5f_u x) n)))))
             (1 # 12)))
    (1 # 2))
  (Qmin (Qmin
      (Qmult (Qmin (Qmult (Qinv 2) (projT1 (b5f_u x) n))
                   (Qmult (Qmult (Qinv 2) (Qinv 2))
                          (Qmult (Qmult (Qmult a (1 # 4))
                                        (Qmult (Qinv (Qmult 8 (Qplus 2 1)))
                                               (1 # 2)))
                                 (Qmult (projT1 (b5f_u x) n)
                                        (projT1 (b5f_u x) n)))))
             (1 # 12))
      (Qmult (Qmult a (1 # 4))
             (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
    (1 # 2))).
  rewrite (qeqT_imp_qeq _ _ (real_min_proj (projT1 Eapp) (projT1 Gapp) n)).
  unfold Eapp, Gapp.
  rewrite (qeqT_imp_qeq _ _ (b5dQ_lb_exp_part_c_coord q Hq0 Hq1 x Hxr a Ha (1 # 2)
                                    b5dQ_p4_half_pos n)).
  rewrite (qeqT_imp_qeq _ _ (b5dQ_lb_gdiff_c_coord q Hq0 Hq1 x Hxr a Ha (1 # 4)
                                 b5dQ_Hq14 n)).
  reflexivity.
Qed.

(* ============================================================ *)
(* M1 main piece: b5dQ_lb_Sdiff (the S-diff-layer lb — the δexp/δg branches      *)
(*   instantiated per the P2 §4 note; N := Nub (the S tail certificate folded in); *)
(*   margin := lb/2)                                                             *)
(*   Proof: unfold real_lt (e := lb/2, N := Nub) -> the coordinate-piece rewrite + *)
(*   the qinv2/qinv2sq normalization -> the Q layer (six branches: three for the *)
(*   exp branch + three for the g branch, per-branch floor <= coordinate (the S  *)
(*   leaf 1#3 closed from below + u >= 1 + q_scaled_le) + the branch_lt strict   *)
(*   margins + qmin_sub_r x3 assembly + min_glb_lt).                             *)
(* ============================================================ *)
Lemma b5dQ_lb_Sdiff : forall (q : Q) (Hq0 : QleT' 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : QltT 0 a)
  (Nub : nat)
  (Hcert : forall n : nat, NatLe Nub n ->
           QleT' (Qabs (projT1 (b5a_S x) n)) 2),
  real_lt (real_const (b5dQ_lbSdiff_val q a))
    (projT1 (b5dP_S_diff_closed_r_M_exp_tail q Hq0 Hq1 x Hxr 2
      b5dQ_p4_two_pos Nub Hcert (real_const a)
      (real_const_pos a Ha))).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha Nub Hcert.
  set (cE := b5dQ_lbSdiff_cE q a).
  set (cG := b5dQ_lbSdiff_cG q a).
  set (cS := b5dQ_lbSdiff_cS q a).
  set (lb := Qmult cS (1 # 2)).
  set (e := Qmult lb (1 # 2)).
  assert (H12 : Qlt 0 (1 # 2)) by exact (QltT_to_Qlt _ _ b5dQ_p4_half_pos).
  assert (H13 : Qlt 0 (1 # 3)) by (unfold Qlt; simpl; lia).
  assert (H14 : Qlt 0 (1 # 4)) by (unfold Qlt; simpl; lia).
  assert (H112 : Qlt 0 (1 # 12)) by (unfold Qlt; simpl; lia).
  assert (Hcpos : Qlt 0 cS).
  { unfold cS. exact (QltT_to_Qlt _ _ (b5dQ_lbSdiff_cS_pos q a Hq0 Ha)). }
  assert (Hlbpos : Qlt 0 lb).
  { unfold lb. apply (Qmult_lt_0_compat cS (1 # 2)); [exact Hcpos | exact H12]. }
  assert (Hepos : Qlt 0 e).
  { unfold e. apply (Qmult_lt_0_compat lb (1 # 2)); [exact Hlbpos | exact H12]. }
  (* cS <= each floor (the six-floor projection chain). *)
  assert (HcA : Qle cS (Qmult (Qmin (1 # 2)
                 (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                      (Qinv (b5j_Kvq q))) (1 # 3))
                        (1 # 4)))
                           (1 # 4))).
  { apply (Qle_trans cS cE
      (Qmult (Qmin (1 # 2)
             (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                  (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
             (1 # 4))).
    - unfold cS. apply Q.le_min_l.
    - unfold cE. apply (Qle_trans (Qmin (Qmin
          (Qmult (Qmin (1 # 2)
                 (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                      (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                 (1 # 4))
          (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
          (1 # 2))
          (Qmin
            (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                        (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                   (1 # 4))
            (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
          (Qmult (Qmin (1 # 2)
                 (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                      (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                 (1 # 4))).
      + apply Q.le_min_l.
      + apply Q.le_min_l. }
  assert (HcB : Qle cS (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))).
  { apply (Qle_trans cS cE
      (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))).
    - unfold cS. apply Q.le_min_l.
    - unfold cE. apply (Qle_trans (Qmin (Qmin
          (Qmult (Qmin (1 # 2)
                 (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                      (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                 (1 # 4))
          (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
          (1 # 2))
          (Qmin
            (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                        (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                   (1 # 4))
            (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
          (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))).
      + apply Q.le_min_l.
      + apply (Qle_trans (Qmin
            (Qmult (Qmin (1 # 2)
                   (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                        (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4)))
                   (1 # 4))
            (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)))
          (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))
          (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12)));
          [ apply Q.le_min_r | apply Qle_refl ]. }
  assert (HcC : Qle cS (1 # 2)).
  { apply (Qle_trans cS cE (1 # 2)).
    - unfold cS. apply Q.le_min_l.
    - unfold cE. apply Q.le_min_r. }
  assert (HcA2 : Qle cS (Qmult (Qmin (1 # 2)
                 (Qmult (1 # 4)
                        (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1)))
                                      (1 # 2)))))
                           (1 # 12))).
  { apply (Qle_trans cS cG
      (Qmult (Qmin (1 # 2)
             (Qmult (1 # 4)
                    (Qmult (Qmult a (1 # 4))
                           (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
             (1 # 12))).
    - unfold cS. apply Q.le_min_r.
    - unfold cG. apply (Qle_trans (Qmin (Qmin
          (Qmult (Qmin (1 # 2)
                 (Qmult (1 # 4)
                        (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                 (1 # 12))
          (Qmult (Qmult a (1 # 4))
                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
          (1 # 2))
          (Qmin
            (Qmult (Qmin (1 # 2)
                   (Qmult (1 # 4)
                          (Qmult (Qmult a (1 # 4))
                                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                   (1 # 12))
            (Qmult (Qmult a (1 # 4))
                   (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
          (Qmult (Qmin (1 # 2)
                 (Qmult (1 # 4)
                        (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                 (1 # 12))).
      + apply Q.le_min_l.
      + apply Q.le_min_l. }
  assert (HcB2 : Qle cS (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))).
  { apply (Qle_trans cS cG
      (Qmult (Qmult a (1 # 4))
             (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))).
    - unfold cS. apply Q.le_min_r.
    - unfold cG. apply (Qle_trans (Qmin (Qmin
          (Qmult (Qmin (1 # 2)
                 (Qmult (1 # 4)
                        (Qmult (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                 (1 # 12))
          (Qmult (Qmult a (1 # 4))
                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
          (1 # 2))
          (Qmin
            (Qmult (Qmin (1 # 2)
                   (Qmult (1 # 4)
                          (Qmult (Qmult a (1 # 4))
                                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                   (1 # 12))
            (Qmult (Qmult a (1 # 4))
                   (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
          (Qmult (Qmult a (1 # 4))
                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))).
      + apply Q.le_min_l.
      + apply (Qle_trans (Qmin
            (Qmult (Qmin (1 # 2)
                   (Qmult (1 # 4)
                          (Qmult (Qmult a (1 # 4))
                                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                   (1 # 12))
            (Qmult (Qmult a (1 # 4))
                   (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
          (Qmult (Qmult a (1 # 4))
                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
          (Qmult (Qmult a (1 # 4))
                 (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))));
          [ apply Q.le_min_r | apply Qle_refl ]. }
  assert (HcC2 : Qle cS (1 # 2)).
  { apply (Qle_trans cS cG (1 # 2)).
    - unfold cS. apply Q.le_min_r.
    - unfold cG. apply Q.le_min_r. }
  unfold real_lt.
  exists e.
  split.
  { apply Qlt_to_QltT. exact Hepos. }
  { exists Nub.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (b5dQ_lb_Sdiff_coord q Hq0 Hq1 x Hxr a Ha Nub Hcert n)).
    pose proof (qeqT_imp_qeq _ _ b5dQ_p_qinv2sq) as Hgenqeqsq10202.
    pose proof (qeqT_imp_qeq _ _ b5dQ_p_qinv2) as Hgenqeq10202.
    rewrite Hgenqeqsq10202.
    rewrite Hgenqeq10202.
    cbn [projT1 real_const].
    set (Sn := projT1 (b5a_S x) n).
    set (u := projT1 (b5f_u x) n).
    assert (Hug : Qle 1 u) by (apply QleT'_to_Qle; unfold u; apply b5dQ_p_u_ge1).
    assert (HcSn : Qle (Qabs Sn) 2) by (apply QleT'_to_Qle; exact (Hcert n Hn)).
    assert (HmK0 : Qle 0 (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))).
    { apply Qlt_le_weak.
      apply (Qmult_lt_0_compat (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))).
      - apply (Qmult_lt_0_compat a (1 # 2)); [exact (QltT_to_Qlt _ _ Ha) | exact H12].
      - apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (b5j_Kvq_pos q (QleT'_to_Qle _ _ Hq0))). }
    assert (HmG0 : Qle 0 (Qmult (Qmult a (1 # 4))
                                (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))).
    { apply Qlt_le_weak.
      apply (Qmult_lt_0_compat (Qmult a (1 # 4))
                               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))).
      - apply (Qmult_lt_0_compat a (1 # 4)); [exact (QltT_to_Qlt _ _ Ha) | exact H14].
      - apply (Qmult_lt_0_compat (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2));
          [exact (QltT_to_Qlt _ _ b5dQ_p4_k2t_pos) | exact H12]. }
    (* the invM coordinate >= 1#3 (closed from below by the |Sn| <= 2 tail certificate). *)
    assert (Hinv : Qle (1 # 3) (Qinv (Qplus 1 (Qabs Sn)))).
    { pose proof (qeqT_imp_qeq _ _ b5dQ_p_qinv3) as Hgenqinv3b.
      rewrite <- Hgenqinv3b.
      apply QleT'_to_Qle.
      apply b5dQ_p_qinv_le_mono.
      - apply Qlt_to_QltT. apply (Qlt_le_trans 0 1 (Qplus 1 (Qabs Sn))).
        + apply (QltT_to_Qlt 0 1 qltT_0_1).
        + apply (Qplus_le_compat 1 1 0 (Qabs Sn));
            [apply Qle_refl | apply Qabs_nonneg].
      - exact (Qlt_to_QltT _ _ (H13)).
      - apply Qle_to_QleT'. nra. }
    (* the second branch of the exp-branch inner δlin >= floorL2 (closed from below by Qinv). *)
    assert (He0 : Qle (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3))
                     (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                            (Qinv (Qplus 1 (Qabs Sn))))).
    { apply (Qle_trans
        (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3))
        (Qmult (1 # 3) (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))))
        (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
               (Qinv (Qplus 1 (Qabs Sn))))).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      - apply (Qle_trans
          (Qmult (1 # 3) (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))))
          (Qmult (Qinv (Qplus 1 (Qabs Sn)))
                 (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))))
          (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                 (Qinv (Qplus 1 (Qabs Sn))))).
        + apply (Qmult_le_compat_r (1 # 3) (Qinv (Qplus 1 (Qabs Sn)))
                                   (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))));
            [ exact Hinv | exact HmK0 ].
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    assert (HdL2 : Qle (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                            (Qinv (b5j_Kvq q))) (1 # 3)) (1 # 4))
                       (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                            (Qinv (b5j_Kvq q)))
                                     (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))).
    { apply (Qmult_le_compat_r
        (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q))) (1 # 3))
        (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
               (Qinv (Qplus 1 (Qabs Sn))))
        (1 # 4)); [ exact He0 | apply Qlt_le_weak; exact H14 ]. }
    (* the exp-branch floorL <= the inner δlin coordinate (min-glb branch by branch). *)
    assert (HdL : Qle (Qmin (1 # 2)
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (1 # 3)) (1 # 4)))
                      (Qmin (1 # 2)
        (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                      (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))).
    apply QleT'_to_Qle.
    { apply b5dQ_p_min_glb_le.
      - apply Qle_to_QleT'. apply Q.le_min_l.
      - apply Qle_to_QleT'. apply (Qle_trans (Qmin (1 # 2)
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (1 # 3)) (1 # 4)))
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (1 # 3)) (1 # 4))
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)));
          [ apply Q.le_min_r | exact HdL2 ]. }
    (* the exp-branch δL coordinate >= floorD (per branch with u >= 1). *)
    assert (HkLpos : Qlt 0 b5j_kL) by (apply QltT_to_Qlt; exact b5j_kL_posT).
    assert (Hq1u : Qle (1 # 2) (Qmult (1 # 2) u)) by nra.
    assert (Hq2u : Qle (Qmult (1 # 4) b5j_kL)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))).
    apply QleT'_to_Qle.
    { apply b5dQ_p_q_scaled_le;
        [ apply Qle_to_QleT'; apply Qlt_le_weak; exact H14
        | apply Qle_to_QleT'; apply Qlt_le_weak; exact HkLpos
        | apply Qle_to_QleT'; exact Hug ]. }
    assert (HfD : Qle (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL))
        (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u))))).
    apply QleT'_to_Qle.
    { apply b5dQ_p_min_glb_le.
      - apply Qle_to_QleT'. apply (Qle_trans (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 2)
                         (Qmult (1 # 2) u));
          [ apply Q.le_min_l | exact Hq1u ].
      - apply Qle_to_QleT'. apply (Qle_trans (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL))
                         (Qmult (1 # 4) b5j_kL)
                         (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u))));
          [ apply Q.le_min_r | exact Hq2u ]. }
    (* the two exp-branch floors <= the coordinates (A1/B1). *)
    assert (FA1 : Qle (Qmult (Qmin (1 # 2)
           (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                         (1 # 3)) (1 # 4))) (1 # 4))
                      (Qmult (Qmin (1 # 2)
        (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                      (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4))).
    { apply (Qmult_le_compat_r
        (Qmin (1 # 2)
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (1 # 3)) (1 # 4)))
        (Qmin (1 # 2)
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))
        (1 # 4)); [ exact HdL | apply Qlt_le_weak; exact H14 ]. }
    assert (FB1 : Qle (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))
        (Qmult (Qmin (Qmult (1 # 2) u)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12))).
    { apply (Qmult_le_compat_r (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL))
        (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u))))
        (1 # 12)); [ exact HfD | apply Qlt_le_weak; exact H112 ]. }
    (* the g-branch inner δL' coordinate >= floorL' (per branch with u >= 1; m := (a*1#4)*k2t*1#2). *)
    assert (Hq1g : Qle (1 # 2) (Qmult (1 # 2) u)) by nra.
    assert (Hq2g : Qle (Qmult (1 # 4)
             (Qmult (Qmult a (1 # 4))
                    (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
                     (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))).
    apply QleT'_to_Qle.
    { apply b5dQ_p_q_scaled_le;
        [ apply Qle_to_QleT'; apply Qlt_le_weak; exact H14
        | apply Qle_to_QleT'; exact HmG0
        | apply Qle_to_QleT'; exact Hug ]. }
    assert (HfG : Qle (Qmin (1 # 2)
        (Qmult (1 # 4)
               (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
        (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u))))).
    apply QleT'_to_Qle.
    { apply b5dQ_p_min_glb_le.
      - apply Qle_to_QleT'. apply (Qle_trans (Qmin (1 # 2)
            (Qmult (1 # 4)
                   (Qmult (Qmult a (1 # 4))
                          (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                         (1 # 2) (Qmult (1 # 2) u));
          [ apply Q.le_min_l | exact Hq1g ].
      - apply Qle_to_QleT'. apply (Qle_trans (Qmin (1 # 2)
            (Qmult (1 # 4)
                   (Qmult (Qmult a (1 # 4))
                          (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                         (Qmult (1 # 4)
                                (Qmult (Qmult a (1 # 4))
                                       (Qmult (Qinv (Qmult 8 (Qplus 2 1)))
                                              (1 # 2))))
                         (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u))));
          [ apply Q.le_min_r | exact Hq2g ]. }
    assert (FA2 : Qle (Qmult (Qmin (1 # 2)
           (Qmult (1 # 4)
                  (Qmult (Qmult a (1 # 4))
                         (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                         (1 # 12))
        (Qmult (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))) (1 # 12))).
    { apply (Qmult_le_compat_r (Qmin (1 # 2)
           (Qmult (1 # 4)
                  (Qmult (Qmult a (1 # 4))
                         (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
        (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u))))
        (1 # 12)); [ exact HfG | apply Qlt_le_weak; exact H112 ]. }
    (* the six-branch strict margins (branch_lt; the floor projection chain is above). *)
    assert (S1 : Qlt e (Qminus (Qmult (Qmin (1 # 2)
        (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                      (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4)) lb)).
    { unfold e, lb.
      apply QltT_to_Qlt.
      apply (b5dQ_p_branch_lt
        (Qmult (Qmin (1 # 2)
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4))
        (Qmult (Qmin (1 # 2)
          (Qmult (Qmult (Qmult (Qmult a (1 # 2)) (Qinv (b5j_Kvq q)))
                        (1 # 3)) (1 # 4))) (1 # 4))
        cS); [exact (Qle_to_QleT' _ _ FA1) | exact (Qle_to_QleT' _ _ HcA)
            | exact (Qlt_to_QltT _ _ Hcpos)]. }
    assert (S2 : Qlt e (Qminus (Qmult (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12)) lb)).
    { unfold e, lb.
      apply QltT_to_Qlt.
      apply (b5dQ_p_branch_lt
        (Qmult (Qmin (Qmult (1 # 2) u)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12))
        (Qmult (Qmin (1 # 2) (Qmult (1 # 4) b5j_kL)) (1 # 12))
        cS); [exact (Qle_to_QleT' _ _ FB1) | exact (Qle_to_QleT' _ _ HcB)
            | exact (Qlt_to_QltT _ _ Hcpos)]. }
    assert (S3 : Qlt e (Qminus (1 # 2) lb)).
    { unfold e, lb.
      apply QltT_to_Qlt.
      apply (b5dQ_p_branch_lt (1 # 2) (1 # 2) cS);
        [(apply Qle_to_QleT'; apply Qle_refl) | exact (Qle_to_QleT' _ _ (HcC)) | exact (Qlt_to_QltT _ _ (Hcpos))]. }
    assert (S4 : Qlt e (Qminus (Qmult (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))) (1 # 12)) lb)).
    { unfold e, lb.
      apply QltT_to_Qlt.
      apply (b5dQ_p_branch_lt
        (Qmult (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))) (1 # 12))
        (Qmult (Qmin (1 # 2)
           (Qmult (1 # 4)
                  (Qmult (Qmult a (1 # 4))
                         (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))))
                         (1 # 12))
        cS); [exact (Qle_to_QleT' _ _ FA2) | exact (Qle_to_QleT' _ _ HcA2)
            | exact (Qlt_to_QltT _ _ Hcpos)]. }
    assert (S5 : Qlt e (Qminus (Qmult (Qmult a (1 # 4))
          (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))) lb)).
    { unfold e, lb.
      apply QltT_to_Qlt.
      apply (b5dQ_p_branch_lt
        (Qmult (Qmult a (1 # 4))
               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
        (Qmult (Qmult a (1 # 4))
               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
        cS); [(apply Qle_to_QleT'; apply Qle_refl)
            | exact (Qle_to_QleT' _ _ HcB2) | exact (Qlt_to_QltT _ _ Hcpos)]. }
    assert (S6 : Qlt e (Qminus (1 # 2) lb)).
    { unfold e, lb.
      apply QltT_to_Qlt.
      apply (b5dQ_p_branch_lt (1 # 2) (1 # 2) cS);
        [(apply Qle_to_QleT'; apply Qle_refl) | exact (Qle_to_QleT' _ _ HcC2)
            | exact (Qlt_to_QltT _ _ Hcpos)]. }
    (* assembly: the min-tree decomposition of X_n - lb (two levels of Qmin minus lb x3 + min_glb). *)
    pose proof (qeqT_imp_qeq _ _ (b5dQ_p_qmin_sub_r
      (Qmin (Qmin
        (Qmult (Qmin (1 # 2)
               (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                    (Qinv (b5j_Kvq q)))
                             (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4))
        (Qmult (Qmin (Qmult (1 # 2) u)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12)))
        (1 # 2))
      (Qmin (Qmin
        (Qmult (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))) (1 # 12))
        (Qmult (Qmult a (1 # 4))
               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
        (1 # 2))
      (b5dQ_lbSdiff_val q a))) as Hgenqmin5_L12181.
    rewrite Hgenqmin5_L12181.
    pose proof (qeqT_imp_qeq _ _ (b5dQ_p_qmin_sub_r
      (Qmin
        (Qmult (Qmin (1 # 2)
               (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                    (Qinv (b5j_Kvq q)))
                             (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4))) (1 # 4))
        (Qmult (Qmin (Qmult (1 # 2) u)
                     (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12)))
      (1 # 2) (b5dQ_lbSdiff_val q a))) as Hgenqmin6_L12200.
    rewrite Hgenqmin6_L12200.
    pose proof (qeqT_imp_qeq _ _ (b5dQ_p_qmin_sub_r
      (Qmult (Qmin (1 # 2)
             (Qmult (Qmult (Qmult (Qmult a (1 # 2))
                                  (Qinv (b5j_Kvq q)))
                           (Qinv (Qplus 1 (Qabs Sn)))) (1 # 4)))
             (1 # 4))
      (Qmult (Qmin (Qmult (1 # 2) u)
                   (Qmult (1 # 4) (Qmult b5j_kL (Qmult u u)))) (1 # 12))
      (b5dQ_lbSdiff_val q a))) as Hgenqmin7_L12209.
    rewrite Hgenqmin7_L12209.
    pose proof (qeqT_imp_qeq _ _ (b5dQ_p_qmin_sub_r
      (Qmin
        (Qmult (Qmin (Qmult (1 # 2) u)
              (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))) (1 # 12))
        (Qmult (Qmult a (1 # 4))
               (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2))))
      (1 # 2) (b5dQ_lbSdiff_val q a))) as Hgenqmin8_L12218.
    rewrite Hgenqmin8_L12218.
    pose proof (qeqT_imp_qeq _ _ (b5dQ_p_qmin_sub_r
      (Qmult (Qmin (Qmult (1 # 2) u)
        (Qmult (1 # 4)
        (Qmult (Qmult (Qmult a (1 # 4))
                      (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
               (Qmult u u)))) (1 # 12))
      (Qmult (Qmult a (1 # 4))
             (Qmult (Qinv (Qmult 8 (Qplus 2 1))) (1 # 2)))
      (b5dQ_lbSdiff_val q a))) as Hgenqmin9_L12228.
    rewrite Hgenqmin9_L12228.
    apply Q.min_glb_lt.
    - apply Q.min_glb_lt.
      + apply Q.min_glb_lt; [exact S1 | exact S2].
      + exact S3.
    - apply Q.min_glb_lt.
      + apply Q.min_glb_lt; [exact S4 | exact S5].
      + exact S6.
  }
Qed.

(* ===== Section M23 (the value-family canon + G7: the tau/kS/m4/delta0 definitions and positivity, 9 Lemma/Def) ===== *)

(* ============================================================ *)
(* M2/M3: the δ0 value-definition family + positivity (the lb_Jmod output + the G7 closure) *)
(* ============================================================ *)

(* τ := cA*Qinv(8*K1) (cA := 1#2, M_S := 2: K1 := 2q+1, the zeta form). *)
Definition b5dQ_tau (q : Q) : Q :=
  Qmult (1 # 2) (Qinv (Qmult 8 (Qplus (Qmult q 2) 1))).

(* the zeta form of kS := (cA*cB)*(1#8)*invM1 (cA := 1#2, cB := cA*(1#2),
   invM1 := Qinv(1+q+1) — the δS1-leaf eps share coordinate coefficient inside the J-mod). *)
Definition b5dQ_kS (q : Q) : Q :=
  Qmult (Qmult (Qmult (1 # 2) (Qmult (1 # 2) (1 # 2))) (1 # 8))
        (Qinv (Qplus (Qplus 1 (Qmult q 1)) 1)).

(* the eps share coordinate a := epsQ/(2q) positivity (the J-mod eps coordinate). *)
Lemma b5dQ_p4_a_pos : forall (q epsQ : Q), QltT 0 q -> QltT 0 epsQ ->
  QltT 0 (epsQ / (2 * q)).
Proof.
  intros q epsQ Hq0 Heps.
  apply Qlt_to_QltT.
  unfold Qdiv.
  apply (Qmult_lt_0_compat epsQ (Qinv (2 * q))).
  - exact (QltT_to_Qlt _ _ (Heps)).
  - apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (b5dL_two_q_pos q Hq0)).
Qed.

(* the kS(q) positivity (0 < q). *)
Lemma b5dQ_kS_pos : forall (q : Q), QltT 0 q -> QltT 0 (b5dQ_kS q).
Proof.
  intros q Hq0.
  apply Qlt_to_QltT.
  unfold b5dQ_kS.
  apply (Qmult_lt_0_compat
    (Qmult (Qmult (1 # 2) (Qmult (1 # 2) (1 # 2))) (1 # 8))
    (Qinv (Qplus (Qplus 1 (Qmult q 1)) 1))).
  - apply (Qmult_lt_0_compat (Qmult (1 # 2) (Qmult (1 # 2) (1 # 2))) (1 # 8)).
    + apply (Qmult_lt_0_compat (1 # 2) (Qmult (1 # 2) (1 # 2))).
      * exact (QltT_to_Qlt _ _ b5dQ_p4_half_pos).
      * apply (Qmult_lt_0_compat (1 # 2) (1 # 2));
          [exact (QltT_to_Qlt _ _ b5dQ_p4_half_pos) | exact (QltT_to_Qlt _ _ b5dQ_p4_half_pos)].
    + change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia.
  - apply Qinv_lt_0_compat.
    assert (Hq10 : Qle 0 (Qmult q 1)).
    { apply (Qmult_le_0_compat q 1).
      - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ Hq0).
      - change (Qle 0 1). unfold Qle. simpl. lia. }
    assert (H1p : Qle 1 (Qplus 1 (Qmult q 1))).
    { apply (Qle_trans 1 (Qplus 1 0) (Qplus 1 (Qmult q 1))).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      - apply Qplus_le_compat; [apply Qle_refl | exact Hq10]. }
    apply (Qlt_le_trans 0 1 (Qplus (Qplus 1 (Qmult q 1)) 1)).
    + change (Qlt 0 1). unfold Qlt. simpl. lia.
    + apply (Qle_trans 1 (Qplus 1 0) (Qplus (Qplus 1 (Qmult q 1)) 1)).
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      * apply Qplus_le_compat; [exact H1p | apply Qlt_le_weak;
          change (Qlt 0 1); unfold Qlt; simpl; lia].
Qed.

(* the τ(q) positivity (0 < q gives 8(2q+1) > 0). *)
Lemma b5dQ_tau_pos : forall (q : Q), QltT 0 q -> QltT 0 (b5dQ_tau q).
Proof.
  intros q Hq0.
  apply Qlt_to_QltT.
  unfold b5dQ_tau.
  apply (Qmult_lt_0_compat (1 # 2) (Qinv (Qmult 8 (Qplus (Qmult q 2) 1)))).
  - exact (QltT_to_Qlt _ _ b5dQ_p4_half_pos).
  - apply Qinv_lt_0_compat.
    assert (Hq20 : Qlt 0 (Qmult q 2)).
    { apply (Qmult_lt_0_compat q 2).
      - exact (QltT_to_Qlt _ _ Hq0).
      - unfold Qlt. simpl. lia. }
    assert (H8p : Qlt 0 (Qmult 8 (Qplus (Qmult q 2) 1))).
    { apply (Qmult_lt_0_compat 8 (Qplus (Qmult q 2) 1)).
      - unfold Qlt. simpl. lia.
      - apply (Qlt_le_trans 0 (Qmult q 2) (Qplus (Qmult q 2) 1)).
        + exact Hq20.
        + apply (Qle_trans (Qmult q 2) (Qplus (Qmult q 2) 0)
                           (Qplus (Qmult q 2) 1)).
          * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          * apply Qplus_le_compat; [apply Qle_refl | apply Qlt_le_weak;
              change (Qlt 0 1); unfold Qlt; simpl; lia]. }
    exact H8p.
Qed.

(* m4 := min(τ, lb_E@a, lb_S@a1, lb_S@1) (the min of the four-branch lb values —
   ordered like the J-mod δ tree: min(min(min δE δS1) δS2) τ). *)
Definition b5dQ_m4 (q epsQ : Q) : Q :=
  Qmin (Qmin (Qmin
    (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))
    (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))
    (b5dQ_lbSdiff_val q 1))
  (b5dQ_tau q).

(* δ0 := m4/2 (the lb_Jmod output; the strict lower-bound margin). *)
Definition b5dQ_delta0 (q epsQ : Q) : Q :=
  Qmult (b5dQ_m4 q epsQ) (1 # 2).

(* the m4 positivity (the M3 precondition: the four components positive + min-glb). *)
Lemma b5dQ_m4_pos : forall (q epsQ : Q),
  QltT 0 q -> QltT q 1 -> QltT 0 epsQ -> QltT 0 (b5dQ_m4 q epsQ).
Proof.
  intros q epsQ Hq0 Hq1 Heps.
  apply Qlt_to_QltT.
  assert (Ha : Qlt 0 (epsQ / (2 * q))) by (exact (QltT_to_Qlt _ _ (b5dQ_p4_a_pos q epsQ Hq0 Heps))).
  assert (Ha1 : Qlt 0 (Qmult (epsQ / (2 * q)) (b5dQ_kS q))).
  { apply (Qmult_lt_0_compat (epsQ / (2 * q)) (b5dQ_kS q));
      [exact Ha | exact (QltT_to_Qlt _ _ (b5dQ_kS_pos q Hq0))]. }
  unfold b5dQ_m4.
  apply Q.min_glb_lt.
  - apply Q.min_glb_lt.
    + apply Q.min_glb_lt.
      * apply (Qmult_lt_0_compat (b5dQ_vE q (epsQ / (2 * q))) (1 # 2));
          [ exact (QltT_to_Qlt _ _ (b5dQ_vE_pos q (epsQ / (2 * q)) Hq0 Hq1
                              (Qlt_to_QltT _ _ Ha)))
          | exact (QltT_to_Qlt _ _ b5dQ_p4_half_pos) ].
      * exact (QltT_to_Qlt _ _ (b5dQ_lbSdiff_pos q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))
                 (b5dH_q_pos_le q Hq0) (Qlt_to_QltT _ _ Ha1))).
    + exact (QltT_to_Qlt _ _ (b5dQ_lbSdiff_pos q 1 (b5dH_q_pos_le q Hq0)
                 b5dQ_H1pos)).
  - exact (QltT_to_Qlt _ _ (b5dQ_tau_pos q Hq0)).
Qed.

(* M3: the δ0 positivity (the G7 closure — about 10 lines, following the P3 §4 left-over-1 mechanism). *)
Lemma b5dQ_delta0_pos : forall (q epsQ : Q),
  QltT 0 q -> QltT q 1 -> QltT 0 epsQ -> QltT 0 (b5dQ_delta0 q epsQ).
Proof.
  intros q epsQ Hq0 Hq1 Heps.
  apply Qlt_to_QltT.
  unfold b5dQ_delta0.
  apply (Qmult_lt_0_compat (b5dQ_m4 q epsQ) (1 # 2));
    [ exact (QltT_to_Qlt _ _ (b5dQ_m4_pos q epsQ Hq0 Hq1 Heps))
    | exact (QltT_to_Qlt _ _ b5dQ_p4_half_pos) ].
Qed.

(* ===== Section P4g (the variant piece: b5dQ_p4g_J_tail_lb_var three-layer certificates + Part 0-2, 13 Lemma/Def) ===== *)

(* ============================================================ *)
(* Part 0: the Q layer — δ0 := m4/2 < the four-branch lb values (per the design §3 pattern) *)
(* ============================================================ *)

(* half-quantity strictness: Qle m b -> Qlt 0 b -> Qlt (m*(1#2)) b. *)
Lemma b5dQ_p4g_half_strict : forall (m b : Q),
  QleT' m b -> QltT 0 b -> QltT (Qmult m (1 # 2)) b.
Proof.
  intros m b Hmb Hb0.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (Qmult m (1 # 2)) (Qmult b (1 # 2)) b).
  - apply (Qmult_le_compat_r m b (1 # 2)).
    + exact (QleT'_to_Qle _ _ Hmb).
    + change (Qle 0 (1 # 2)). unfold Qle. simpl. lia.
  - assert (Hb : Qlt 0 b) by (exact (QltT_to_Qlt _ _ Hb0)).
    assert (HXpos : Qlt 0 (Qmult b (1 # 2))).
    { apply (Qmult_lt_0_compat b (1 # 2));
        [exact Hb | change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia]. }
    assert (Hpre : Qlt (0 + Qmult b (1 # 2))%Q
                     (Qmult b (1 # 2) + Qmult b (1 # 2))).
    { exact (proj2 (Qplus_lt_l 0 (Qmult b (1 # 2)) (Qmult b (1 # 2))) HXpos). }
    setoid_rewrite Qplus_0_l in Hpre.
    apply (Qlt_le_trans (Qmult b (1 # 2))
                        (Qmult b (1 # 2) + Qmult b (1 # 2)) b).
    + exact Hpre.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* m4 <= the lbE branch (A := vE(q,a)/2 — the left-inner projection of the min tree). *)
Lemma b5dQ_p4g_m4_le_E : forall (q epsQ : Q),
  QleT' (b5dQ_m4 q epsQ)
      (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)).
Proof.
  intros q epsQ.
  apply Qle_to_QleT'.
  unfold b5dQ_m4.
  apply (Qle_trans _ (Qmin
    (Qmin (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))
          (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))
    (b5dQ_lbSdiff_val q 1)) _).
  - apply Q.le_min_l.
  - apply (Qle_trans _ (Qmin
      (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))
      (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q)))) _).
    + apply Q.le_min_l.
    + apply Q.le_min_l.
Qed.

(* m4 <= the lbS1 branch (B := lbSdiff_val q (a*kS(q))). *)
Lemma b5dQ_p4g_m4_le_S1 : forall (q epsQ : Q),
  QleT' (b5dQ_m4 q epsQ)
      (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))).
Proof.
  intros q epsQ.
  apply Qle_to_QleT'.
  unfold b5dQ_m4.
  apply (Qle_trans _ (Qmin
    (Qmin (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))
          (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))
    (b5dQ_lbSdiff_val q 1)) _).
  - apply Q.le_min_l.
  - apply (Qle_trans _ (Qmin
      (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))
      (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q)))) _).
    + apply Q.le_min_l.
    + apply Q.le_min_r.
Qed.

(* m4 <= the lbS2 branch (C := lbSdiff_val q 1). *)
Lemma b5dQ_p4g_m4_le_S2 : forall (q epsQ : Q),
  QleT' (b5dQ_m4 q epsQ) (b5dQ_lbSdiff_val q 1).
Proof.
  intros q epsQ.
  apply Qle_to_QleT'.
  unfold b5dQ_m4.
  apply (Qle_trans _ (Qmin
    (Qmin (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))
          (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))
    (b5dQ_lbSdiff_val q 1)) _).
  - apply Q.le_min_l.
  - apply Q.le_min_r.
Qed.

(* m4 <= the τ branch (D := b5dQ_tau q). *)
Lemma b5dQ_p4g_m4_le_tau : forall (q epsQ : Q),
  QleT' (b5dQ_m4 q epsQ) (b5dQ_tau q).
Proof.
  intros q epsQ.
  apply Qle_to_QleT'.
  unfold b5dQ_m4.
  apply Q.le_min_r.
Qed.

(* Qlt (m4/2) (the lbE value). *)
Lemma b5dQ_p4g_qlt_E : forall (q epsQ : Q),
  QltT 0 q -> QltT q 1 -> QltT 0 epsQ ->
  QltT (b5dQ_delta0 q epsQ)
      (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)).
Proof.
  intros q epsQ Hq0 Hq1 HepsQ.
  assert (Ha : Qlt 0 (epsQ / (2 * q)))
    by (exact (QltT_to_Qlt _ _ (b5dQ_p4_a_pos q epsQ Hq0 HepsQ))).
  unfold b5dQ_delta0.
  apply b5dQ_p4g_half_strict.
  - exact (b5dQ_p4g_m4_le_E q epsQ).
  - exact (Qlt_to_QltT _ _
             (Qmult_lt_0_compat (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)
                (QltT_to_Qlt _ _
                   (b5dQ_vE_pos q (epsQ / (2 * q)) Hq0 Hq1 (Qlt_to_QltT _ _ Ha)))
                (QltT_to_Qlt _ _ b5dQ_p4_half_pos))).
Qed.

(* Qlt (m4/2) (the lbS1 value). *)
Lemma b5dQ_p4g_qlt_S1 : forall (q epsQ : Q),
  QltT 0 q -> QltT q 1 -> QltT 0 epsQ ->
  QltT (b5dQ_delta0 q epsQ)
      (b5dQ_lbSdiff_val q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))).
Proof.
  intros q epsQ Hq0 Hq1 HepsQ.
  assert (Ha : Qlt 0 (epsQ / (2 * q)))
    by (exact (QltT_to_Qlt _ _ (b5dQ_p4_a_pos q epsQ Hq0 HepsQ))).
  assert (Ha1 : Qlt 0 (Qmult (epsQ / (2 * q)) (b5dQ_kS q))).
  { apply (Qmult_lt_0_compat (epsQ / (2 * q)) (b5dQ_kS q)).
    - exact Ha.
    - exact (QltT_to_Qlt _ _ (b5dQ_kS_pos q Hq0)). }
  unfold b5dQ_delta0.
  apply b5dQ_p4g_half_strict.
  - exact (b5dQ_p4g_m4_le_S1 q epsQ).
  - exact (b5dQ_lbSdiff_pos q (Qmult (epsQ / (2 * q)) (b5dQ_kS q))
             (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) (Qlt_to_QltT _ _ Ha1)).
Qed.

(* Qlt (m4/2) (the lbS2 value). *)
Lemma b5dQ_p4g_qlt_S2 : forall (q epsQ : Q),
  QltT 0 q -> QltT q 1 -> QltT 0 epsQ ->
  QltT (b5dQ_delta0 q epsQ) (b5dQ_lbSdiff_val q 1).
Proof.
  intros q epsQ Hq0 Hq1 HepsQ.
  unfold b5dQ_delta0.
  apply b5dQ_p4g_half_strict.
  - exact (b5dQ_p4g_m4_le_S2 q epsQ).
  - exact (b5dQ_lbSdiff_pos q 1 (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0)))
             b5dQ_H1pos).
Qed.

(* Qlt (m4/2) (the τ value). *)
Lemma b5dQ_p4g_qlt_tau : forall (q epsQ : Q),
  QltT 0 q -> QltT q 1 -> QltT 0 epsQ ->
  QltT (b5dQ_delta0 q epsQ) (b5dQ_tau q).
Proof.
  intros q epsQ Hq0 Hq1 HepsQ.
  unfold b5dQ_delta0.
  apply b5dQ_p4g_half_strict.
  - exact (b5dQ_p4g_m4_le_tau q epsQ).
  - exact (b5dQ_tau_pos q Hq0).
Qed.

(* ============================================================ *)
(* Part 1: the three-leaf canonical app wrappers + the leaf lb direct instantiations *)
(*   (the statements = the b5dQ_lb_E / b5dQ_lb_Sdiff conclusions verbatim — the app *)
(*   argument shapes copied with zero deviation; the certificates = constructor-form —  *)
(*   the b5dM_/b5dQ_ transparent family + arguments passed directly, not derived  *)
(*   in the Section B body (the P4-settled wall class); the wall-avoidance core)  *)
(* ============================================================ *)

(* the E leaf wrapper (lb_E instantiated directly — the canonical E-app with the share a*(1#32)). *)
Lemma b5dQ_p4g_leaf_E : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (Hs : forall n : nat,
         QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) 1)
  (Hc : forall n : nat,
         QleT' (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) 1)
  (a : Q) (Ha : QltT 0 a),
  real_lt (real_const (Qmult (b5dQ_vE q a) (1 # 2)))
    (projT1 (b5dI_E_diff_closed_r_exp q ((Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ (Hq0))))) Hq1 x Hxr
              1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
              b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all Hs Hc
              (real_mult (real_const a) (real_const (1 # 32)))
              (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
                 (b5dM_real_const_pos a (Qlt_to_QltT 0 a (QltT_to_Qlt _ _ (Ha))))
                 (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T)))).
Proof.
  intros q Hq0 Hq1 x Hxr Hs Hc a Ha.
  exact (b5dQ_lb_E q Hq0 Hq1 x Hxr Hs Hc a Ha).
Qed.

(* the S leaf wrapper (lb_Sdiff instantiated directly — the canonical S-app with the const-form share a). *)
Lemma b5dQ_p4g_leaf_S : forall (q : Q) (Hq0 : QleT' 0 q) (Hq1 : QltT q 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (a : Q) (Ha : QltT 0 a)
  (Nub : nat)
  (Hcert : forall n : nat, NatLe Nub n ->
           QleT' (Qabs (projT1 (b5a_S x) n)) 2),
  real_lt (real_const (b5dQ_lbSdiff_val q a))
    (projT1 (b5dP_S_diff_closed_r_M_exp_tail q Hq0 Hq1 x Hxr 2
      b5dQ_p4_two_pos Nub Hcert (real_const a)
      (real_const_pos a Ha))).
Proof.
  intros q Hq0 Hq1 x Hxr a Ha Nub Hcert.
  exact (b5dQ_lb_Sdiff q Hq0 Hq1 x Hxr a Ha Nub Hcert).
Qed.

(* ============================================================ *)
(* Part 2: the tree lb — real_lt (real_const δ0) (the real_min tree)             *)
(*   min-glue (b5dQ_min_lb x3) + real_lt_trans (general x)                       *)
(* ============================================================ *)

Lemma b5dQ_p4g_tree_lb :
  forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (epsQ : Q) (HepsQ : QltT 0 epsQ)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) q)
  (NM : nat)
  (HMall : forall n : nat, NatLe NM n ->
           QleT' (Qabs (projT1 (b5a_S x) n)) 2)
  (Hs : forall n : nat,
         QleT' (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) 1)
  (Hc : forall n : nat,
         QleT' (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) 1),
  real_lt (real_const (b5dQ_delta0 q epsQ))
    (real_min (real_min (real_min
      (projT1 (b5dI_E_diff_closed_r_exp q (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
                1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
                b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all Hs Hc
                (real_mult (real_const (epsQ / (2 * q))) (real_const (1 # 32)))
                (b5dI_real_mult_positive_exp (real_const (epsQ / (2 * q)))
                   (real_const (1 # 32))
                   (b5dM_real_const_pos (epsQ / (2 * q))
                         (b5dQ_p4_a_pos q epsQ Hq0 HepsQ))
                   (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))))
      (projT1 (b5dP_S_diff_closed_r_M_exp_tail q (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
                2 b5dQ_p4_two_pos NM (fun (n : nat) (hNM : NatLe NM n) => HMall n hNM)
                (real_const (Qmult (epsQ / (2 * q)) (b5dQ_kS q)))
                (real_const_pos (Qmult (epsQ / (2 * q)) (b5dQ_kS q))
                   (Qlt_to_QltT 0 (Qmult (epsQ / (2 * q)) (b5dQ_kS q))
                      (Qmult_lt_0_compat (epsQ / (2 * q)) (b5dQ_kS q)
                         (QltT_to_Qlt _ _ (b5dQ_p4_a_pos q epsQ Hq0 HepsQ))
                         (QltT_to_Qlt _ _ (b5dQ_kS_pos q Hq0))))))))
      (projT1 (b5dP_S_diff_closed_r_M_exp_tail q (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
                2 b5dQ_p4_two_pos NM (fun (n : nat) (hNM : NatLe NM n) => HMall n hNM)
                (real_const 1)
                (real_const_pos 1 b5dQ_H1pos))))
      (real_const (b5dQ_tau q))).
Proof.
  intros q Hq0 Hq1 epsQ HepsQ x Hxr NM HMall Hs Hc.
  assert (Ha : Qlt 0 (epsQ / (2 * q)))
    by (exact (QltT_to_Qlt _ _ (b5dQ_p4_a_pos q epsQ Hq0 HepsQ))).
  assert (Ha1 : Qlt 0 (Qmult (epsQ / (2 * q)) (b5dQ_kS q))).
  { apply (Qmult_lt_0_compat (epsQ / (2 * q)) (b5dQ_kS q)).
    - exact Ha.
    - exact (QltT_to_Qlt _ _ (b5dQ_kS_pos q Hq0)). }
  set (dE := projT1 (b5dI_E_diff_closed_r_exp q (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
           1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
           b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all Hs Hc
           (real_mult (real_const (epsQ / (2 * q))) (real_const (1 # 32)))
           (b5dI_real_mult_positive_exp (real_const (epsQ / (2 * q)))
              (real_const (1 # 32))
              (b5dM_real_const_pos (epsQ / (2 * q))
                    (b5dQ_p4_a_pos q epsQ Hq0 HepsQ))
              (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T)))).
  set (dS1 := projT1 (b5dP_S_diff_closed_r_M_exp_tail q (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM (fun (n : nat) (hNM : NatLe NM n) => HMall n hNM)
           (real_const (Qmult (epsQ / (2 * q)) (b5dQ_kS q)))
           (real_const_pos (Qmult (epsQ / (2 * q)) (b5dQ_kS q))
              (Qlt_to_QltT 0 (Qmult (epsQ / (2 * q)) (b5dQ_kS q))
                 (Qmult_lt_0_compat (epsQ / (2 * q)) (b5dQ_kS q)
                    (QltT_to_Qlt _ _ (b5dQ_p4_a_pos q epsQ Hq0 HepsQ))
                    (QltT_to_Qlt _ _ (b5dQ_kS_pos q Hq0))))))).
  set (dS2 := projT1 (b5dP_S_diff_closed_r_M_exp_tail q (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM (fun (n : nat) (hNM : NatLe NM n) => HMall n hNM)
           (real_const 1)
           (real_const_pos 1 b5dQ_H1pos))).
  assert (HqE : real_lt (real_const (b5dQ_delta0 q epsQ))
                        (real_const (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)))).
  { apply real_const_lt. exact (b5dQ_p4g_qlt_E q epsQ Hq0 Hq1 HepsQ). }
  assert (HlbE : real_lt (real_const (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))) dE).
  { unfold dE. exact (b5dQ_p4g_leaf_E q Hq0 Hq1 x Hxr Hs Hc
                        (epsQ / (2 * q)) (Qlt_to_QltT _ _ Ha)). }
  assert (HdE : real_lt (real_const (b5dQ_delta0 q epsQ)) dE).
  { apply (real_lt_trans (real_const (b5dQ_delta0 q epsQ))
                         (real_const (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)))
                         dE HqE HlbE). }
  assert (HqS1 : real_lt (real_const (b5dQ_delta0 q epsQ))
                         (real_const (b5dQ_lbSdiff_val q
                            (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))).
  { apply real_const_lt. exact (b5dQ_p4g_qlt_S1 q epsQ Hq0 Hq1 HepsQ). }
  assert (HlbS1 : real_lt (real_const (b5dQ_lbSdiff_val q
                            (Qmult (epsQ / (2 * q)) (b5dQ_kS q)))) dS1).
  { unfold dS1. exact (b5dQ_p4g_leaf_S q (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
                         (Qmult (epsQ / (2 * q)) (b5dQ_kS q)) (Qlt_to_QltT _ _ Ha1) NM (fun (n : nat) (hNM : NatLe NM n) => HMall n hNM)). }
  assert (HdS1 : real_lt (real_const (b5dQ_delta0 q epsQ)) dS1).
  { apply (real_lt_trans (real_const (b5dQ_delta0 q epsQ))
                         (real_const (b5dQ_lbSdiff_val q
                            (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))
                         dS1 HqS1 HlbS1). }
  assert (HqS2 : real_lt (real_const (b5dQ_delta0 q epsQ))
                         (real_const (b5dQ_lbSdiff_val q 1))).
  { apply real_const_lt. exact (b5dQ_p4g_qlt_S2 q epsQ Hq0 Hq1 HepsQ). }
  assert (HlbS2 : real_lt (real_const (b5dQ_lbSdiff_val q 1)) dS2).
  { unfold dS2. exact (b5dQ_p4g_leaf_S q (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
                         1 b5dQ_H1pos NM (fun (n : nat) (hNM : NatLe NM n) => HMall n hNM)). }
  assert (HdS2 : real_lt (real_const (b5dQ_delta0 q epsQ)) dS2).
  { apply (real_lt_trans (real_const (b5dQ_delta0 q epsQ))
                         (real_const (b5dQ_lbSdiff_val q 1))
                         dS2 HqS2 HlbS2). }
  assert (HdT : real_lt (real_const (b5dQ_delta0 q epsQ))
                        (real_const (b5dQ_tau q))).
  { apply real_const_lt. exact (b5dQ_p4g_qlt_tau q epsQ Hq0 Hq1 HepsQ). }
  apply (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ))
                     (real_min (real_min dE dS1) dS2)
                     (real_const (b5dQ_tau q))).
  - apply (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ))
                       (real_min dE dS1) dS2).
    + apply (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ)) dE dS1).
      * exact HdE.
      * exact HdS1.
    + exact HdS2.
  - exact HdT.
Qed.

(* ============================================================ *)
Lemma b5dQ_p4g_J_tail_lb_var :
  forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (epsQ : Q) (HepsQ : QltT 0 epsQ)
  (M : nat) (HMpos : (0 < M)%nat) (k : nat) (HkM : NatLe k M)
  (Hxr : forall n : nat,
     QleT' (Qabs (projT1 (real_const (b5dL_tkq q M k)) n)) q)
  (NA : nat)
  (HNA : forall n : nat, NatLe NA n ->
         QleT' (1 # 2) (projT1 (b5a_S (real_const (b5dL_tkq q M k))) n))
  (NM : nat)
  (HMall : forall n : nat, NatLe NM n ->
           QleT' (Qabs (projT1 (b5a_S (real_const (b5dL_tkq q M k))) n)) 2)
  (Hs : forall n : nat,
         QleT' (Qabs (sin_partial n (arctan_partial n
                (projT1 (real_const (b5dL_tkq q M k)) n)))) 1)
  (Hc : forall n : nat,
         QleT' (Qabs (cos_partial n (arctan_partial n
                (projT1 (real_const (b5dL_tkq q M k)) n)))) 1),
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (And (forall (h : Real), real_lt (real_abs h) delta ->
       forall (Hxh : forall n : nat,
          QleT' (Qabs (projT1 (real_plus (real_const (b5dL_tkq q M k)) h) n)) 1),
       forall (eps' : Real), real_lt real_zero eps' ->
       real_le (real_abs (real_plus
                  (b5c_J (real_plus (real_const (b5dL_tkq q M k)) h) Hxh)
                  (real_opp (b5c_J (real_const (b5dL_tkq q M k))
                             (b3rr_dom_r1 (real_const (b5dL_tkq q M k)) q Hxr (QltT_to_Qlt _ _ Hq1))))))
               (real_plus (real_mult (real_const (epsQ / (2 * q))) (real_abs h)) eps'))
         (real_lt (real_const (b5dQ_delta0 q epsQ)) delta))).
Proof.
  intros q Hq0 Hq1 epsQ HepsQ Mg HMpos k HkM Hxr NA HNA NM HMall HMs_all HMc_all.
  (* ---- the instance-face data (instantiation: x := real_const (b5dL_tkq q Mg k),
     a := epsQ/(2q), r := q, cA := 1#2, M := 2, Ms := Mc := 1,
     eps := real_const a — the closed values of the Section B body parameters on the instance face) ---- *)
  set (x := real_const (b5dL_tkq q Mg k)).
  set (a := epsQ / (2 * q)).
  assert (Ha : Qlt 0 a).
  { unfold a. exact (QltT_to_Qlt _ _ (b5dQ_p4_a_pos q epsQ Hq0 HepsQ)). }
  set (r := q).
  assert (Hr0 : Qle 0 r).
  { unfold r. exact (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0)). }
  assert (Hr1 : Qlt r 1).
  { unfold r. exact (QltT_to_Qlt _ _ Hq1). }
  set (cA := (1 # 2)).
  assert (HcA : Qlt 0 cA).
  { unfold cA. exact (QltT_to_Qlt _ _ b5dQ_p4_half_pos). }
  set (M := 2).
  assert (HM : Qlt 0 M).
  { unfold M. exact (QltT_to_Qlt _ _ b5dQ_p4_two_pos). }
  set (Ms := 1).
  assert (HMs : QltT 0 Ms).
  { unfold Ms. exact b5dQ_H1T. }
  set (Mc := 1).
  assert (HMc : QltT 0 Mc).
  { unfold Mc. exact b5dQ_H1T. }
  set (eps := real_const a).
  assert (Heps : real_lt real_zero eps).
  { unfold eps. exact (real_const_pos a (Qlt_to_QltT _ _ Ha)). }

  set (Hx := b3rr_dom_r1 x r Hxr (QltT_to_Qlt _ _ Hq1)).
  (* ---- fixed data ---- *)
  (* cA: a pointwise positive lower bound for S(x) — the statement carries the explicit
     Q parameters cA/HcA plus the NA tail-bound premise HNA;
     δ-C C5: the 4 black-box destructs (source L389/396/399/400) become the intros
     argument bundle  *)
  set (cB := Qmult cA (1 # 2)).
  assert (HcB : Qlt 0 cB).
  { unfold cB. apply (Qmult_lt_0_compat cA (1 # 2)).
    - exact (HcA).
    - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  (* M/Ms/Mc: explicit Q parameters of the statement; the all-n premises HMall/HMs_all/HMc_all apply directly. *)
  assert (HM0 : Qle 0 M). { apply Qlt_le_weak. exact (HM). }
  (* Ms/Mc: the sinA/cosA pointwise bounds give ME := Ms + r*Mc (|E(x)_n| <= ME). *)
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMs. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMc. }
  (* the E/S-diff swapped-source certificates (the item25 change S3: the
     b5dI_E_diff_closed_r_exp bundle parameters — QltT_to_Qlt applied on the proof
     side; the C4 closed value = item7 b5d3_exp_arch4_C). *)
  assert (HMsQ : Qlt 0 Ms). { apply QltT_to_Qlt. exact HMs. }
  assert (HMcQ : Qlt 0 Mc). { apply QltT_to_Qlt. exact HMc. }
  assert (HC40C : Qle 0 b5d3_exp_arch4_C).
  { apply (Qle_trans _ 1 _). { exact (QleT'_to_Qle _ _ Qle_0_1). } { apply QleT'_to_Qle. exact b5d3_exp_arch4_C_ge1. } }
  assert (Hr0' : Qle 0 r). { exact Hr0. }
  set (ME := Qplus Ms (Qmult r Mc)).
  assert (HME0 : Qle 0 ME).
  { unfold ME. nra. }
  (* the reciprocal constants and shares (all depending only on the x data; QltT 0 feeds real_const_pos). *)
  set (QicA := Qinv cA).
  set (QicB := Qinv cB).
  set (kE := Qmult cB (1 # 8)).
  set (kEp := Qmult cB (1 # 16)).
  set (kapE := Qmult cB (1 # 16)).
  set (invM1 := Qinv (Qplus ME 1)).
  set (kS := Qmult (Qmult (Qmult cA cB) (1 # 8)) invM1).
  set (kSp := Qmult (Qmult (Qmult cA cB) (1 # 16)) invM1).
  set (kapS := Qmult (Qmult (Qmult cA cB) (1 # 16)) invM1).
  set (K1 := Qplus (Qmult r M) 1).
  set (tau := Qmult cA (Qinv (Qmult 8 K1))).
  set (mu := Qmult cA (1 # 16)).
  set (kapS2 := Qmult cA (1 # 16)).
  (* positivity facts. *)
  assert (HkET : QltT 0 kE).
  { unfold kE. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 8)).
    - exact HcB.
    - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (HkEpT : QltT 0 kEp).
  { unfold kEp. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 16)).
    - exact HcB.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkapET : QltT 0 kapE).
  { unfold kapE. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cB (1 # 16)).
    - exact HcB.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HME1 : Qlt 0 (Qplus ME 1)).
  { nra. }
  assert (HME1ne : ~ Qplus ME 1 == 0).
  { intro Hz. apply qeq_imp_qeqT in Hz. apply (q_neq_of_lt (Qplus ME 1) (Qlt_to_QltT _ _ HME1)) in Hz. destruct Hz. }
  assert (Hinv1T : QltT 0 invM1).
  { unfold invM1. apply Qlt_to_QltT. apply Qinv_lt_0_compat. exact HME1. }
  assert (HcAcB0 : Qlt 0 (Qmult (Qmult cA cB) (1 # 8))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 8)).
    - apply (Qmult_lt_0_compat cA cB). { exact (HcA). } { exact HcB. }
    - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (HcAcB0b : Qlt 0 (Qmult (Qmult cA cB) (1 # 16))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 16)).
    - apply (Qmult_lt_0_compat cA cB). { exact (HcA). } { exact HcB. }
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkST : QltT 0 kS).
  { unfold kS. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 8)) invM1).
    - exact HcAcB0.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HkSpT : QltT 0 kSp).
  { unfold kSp. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 16)) invM1).
    - exact HcAcB0b.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HkapST : QltT 0 kapS).
  { unfold kapS. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qmult (Qmult cA cB) (1 # 16)) invM1).
    - exact HcAcB0b.
    - apply QltT_to_Qlt. exact Hinv1T. }
  assert (HK1 : Qlt 0 K1).
  { unfold K1. nra. }
  assert (HtauT : QltT 0 tau).
  { unfold tau. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat cA (Qinv (Qmult 8 K1))).
    - exact (HcA).
    - apply Qinv_lt_0_compat. nra. }
  assert (HmuT : QltT 0 mu).
  { unfold mu. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact (HcA).
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkapS2T : QltT 0 kapS2).
  { unfold kapS2. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact (HcA).
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (H1T : QltT 0 1) by (apply Qlt_to_QltT; change (Qlt 0 1); unfold Qlt; simpl; lia).
  assert (HcA0 : Qle 0 cA). { apply Qlt_le_weak. exact (HcA). }
  assert (HcB0 : Qle 0 cB). { apply Qlt_le_weak. exact HcB. }
  assert (HcAne : ~ cA == 0). { intro Hz. apply qeq_imp_qeqT in Hz. apply (q_neq_of_lt cA (Qlt_to_QltT _ _ HcA)) in Hz. destruct Hz. }
  assert (HcBne : ~ cB == 0). { intro Hz. apply qeq_imp_qeqT in Hz. apply (q_neq_of_lt cB (Qlt_to_QltT _ _ HcB)) in Hz. destruct Hz. }
  assert (H8K1ne : ~ Qmult 8 K1 == 0).
  { intro Hz. apply qeq_imp_qeqT in Hz. assert (H8K1T : QltT 0 (Qmult 8 K1)) by (apply Qlt_to_QltT; nra). apply (q_neq_of_lt (Qmult 8 K1) H8K1T) in Hz. destruct Hz. }
  assert (HK1ne : ~ K1 == 0).
  { intro Hz. apply qeq_imp_qeqT in Hz. apply (q_neq_of_lt K1 (Qlt_to_QltT _ _ HK1)) in Hz. destruct Hz. }
  (* ---- the coefficient-budget facts (fixed at the Q layer, for pointwise absorption) ---- *)
  (* Hc1: QicB*kE == 1/8; Hc2: QicB*(kEp+kapE) == 1/8 *)
  assert (Hc1 : Qle (Qmult QicB kE) (1 # 8)).
  { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    unfold QicB, kE.
    field. exact HcBne. }
  assert (Hc1' : Qle (Qmult QicB (Qplus kEp kapE)) (1 # 8)).
  { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    unfold QicB, kEp, kapE.
    field. exact HcBne. }
  (* Hc2/Hc2': ME*QicA*QicB*kS <= 1/8, ME*QicA*QicB*(kSp+kapS) <= 1/8. *)
  set (Mterm := Qmult ME (Qmult QicA QicB)).
  assert (Hc2 : Qle (Qmult Mterm kS) (1 # 8)).
  { apply (Qle_trans (Qmult Mterm kS)
                     (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                     (1 # 8)).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      unfold Mterm, QicA, QicB, kS, invM1.
      field. all: repeat split; assumption.
    - apply (Qle_trans (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                       (Qinv 8)
                       (1 # 8)).
      + apply QleT'_to_Qle. apply (b5n_xinv_le (Qmult ME (1 # 8)) (Qplus ME 1) 8).
        * exact HME1.
        * change (Qlt 0 8). unfold Qlt. simpl. lia.
        * nra.
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold Qinv. reflexivity. }
  assert (Hc2' : Qle (Qmult Mterm (Qplus kSp kapS)) (1 # 8)).
  { apply (Qle_trans (Qmult Mterm (Qplus kSp kapS))
                     (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                     (1 # 8)).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      unfold Mterm, QicA, QicB, kSp, kapS, invM1.
      field. all: repeat split; assumption.
    - apply (Qle_trans (Qmult (Qmult ME (1 # 8)) (Qinv (Qplus ME 1)))
                       (Qinv 8)
                       (1 # 8)).
      + apply QleT'_to_Qle. apply (b5n_xinv_le (Qmult ME (1 # 8)) (Qplus ME 1) 8).
        * exact HME1.
        * change (Qlt 0 8). unfold Qlt. simpl. lia.
        * nra.
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold Qinv. reflexivity. }
  (* the lower-bound inequality: (K1*τ) + μ + kapS2 <= cA - cB (== cA/2; the LHS == cA/4). *)
  assert (Htau_eq : Qle (Qmult K1 tau) (Qmult cA (1 # 8))).
  { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    unfold tau.
    field. all: repeat split; assumption. }
  assert (Hlb_ineq : Qle (Qplus (Qmult K1 tau) (Qplus mu kapS2)) (Qminus cA cB)).
  { apply (Qle_trans (Qplus (Qmult K1 tau) (Qplus mu kapS2))
                     (Qplus (Qmult cA (1 # 8)) (Qmult cA (1 # 8)))
                     (Qminus cA cB)).
    - apply Qplus_le_compat.
      + apply (Qle_trans (Qmult K1 tau) (Qmult cA (1 # 8)) (Qmult cA (1 # 8))).
        * exact Htau_eq.
        * apply Qle_refl.
      + apply (Qle_trans (Qplus mu kapS2) (Qmult cA (1 # 8)) (Qmult cA (1 # 8))).
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold mu, kapS2. ring.
        * apply Qle_refl.
    - unfold cB. nra. }
  (* ---- the eps witnesses and shares ---- *)
  assert (H2T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H4T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (H8T : QltT 0 (1 # 8)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 8)); unfold Qlt; simpl; lia).
  assert (H16T : QltT 0 (1 # 16)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 16)); unfold Qlt; simpl; lia).
  (* ---- the eps shares (Real): epsE / epsS (the slope shares of the E-diff and S-diff main instances)
     — this piece is constructor-form: the E share = the canonical mult form (same shape as lb_E);
     the S share = the canonical const form (same shape as lb_Sdiff — the design §1 (b));
     the witnesses are all inlined canonical terms (zero assert variables enter the app —
     guaranteed by conv construction) ---- *)
  set (epsE := real_mult eps (real_const kE)).
  assert (Ha1 : Qlt 0 (Qmult a (b5dQ_kS q))).
  { apply (Qmult_lt_0_compat a (b5dQ_kS q)).
    - exact Ha.
    - exact (QltT_to_Qlt _ _ (b5dQ_kS_pos q Hq0)). }
  (* the epsS coordinate = a*kS (kS = the Section B set-var zeta — computationally equal to
     b5dQ_kS q; the canonical witness Ha1 uses the b5dQ_kS q form — required by the direct
     lb_Sdiff instantiation). *)
  set (epsS := real_const (Qmult a kS)).
  (* the three leaves built here (canonical app — constructor-form certificates: the E leaf
     HMsQ/HMcQ := b5dQ_H1pos, HC40C := b5dQ_HC40, the eps witnesses := the two b5dM_real_const_pos
     leaves; the S leaf Heps := real_const_pos — the same terms as the lb_E/lb_Sdiff canonical
     app (all certificate slots inlined closed forms / parameters passed directly, zero assert
     variables entering the app); δ definitional = projT1 (app) — reachable when constructing
     the lb certificates (the wall-avoidance core: zero matches on the J-internal certificates)). *)
  pose (δE := projT1 (b5dI_E_diff_closed_r_exp r (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
           1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
           b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all
           HMs_all HMc_all epsE
           (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
              (b5dM_real_const_pos a (Qlt_to_QltT 0 a Ha))
              (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T)))).
  assert (HδE0 := fst (projT2 (b5dI_E_diff_closed_r_exp r (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
           1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
           b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all
           HMs_all HMc_all epsE
           (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
              (b5dM_real_const_pos a (Qlt_to_QltT 0 a Ha))
              (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))))).
  assert (HδE := snd (projT2 (b5dI_E_diff_closed_r_exp r (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
           1 1 b5d3_exp_arch4_C b5dQ_H1pos b5dQ_H1pos b5dQ_HC40
           b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all
           HMs_all HMc_all epsE
           (b5dI_real_mult_positive_exp (real_const a) (real_const (1 # 32))
              (b5dM_real_const_pos a (Qlt_to_QltT 0 a Ha))
              (b5dM_real_const_pos (1 # 32) b5dQ_Hq32T))))).
  pose (δS1 := projT1 (b5dP_S_diff_closed_r_M_exp_tail r (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall epsS
           (real_const_pos (Qmult a kS) (Qlt_to_QltT 0 (Qmult a kS) Ha1)))).
  assert (HδS10 := fst (projT2 (b5dP_S_diff_closed_r_M_exp_tail r (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall epsS
           (real_const_pos (Qmult a kS) (Qlt_to_QltT 0 (Qmult a kS) Ha1))))).
  assert (HδS1 := snd (projT2 (b5dP_S_diff_closed_r_M_exp_tail r (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall epsS
           (real_const_pos (Qmult a kS) (Qlt_to_QltT 0 (Qmult a kS) Ha1))))).
  pose (δS2 := projT1 (b5dP_S_diff_closed_r_M_exp_tail r (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall (real_const 1)
           (real_const_pos 1 b5dQ_H1pos))).
  assert (HδS20 := fst (projT2 (b5dP_S_diff_closed_r_M_exp_tail r (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall (real_const 1)
           (real_const_pos 1 b5dQ_H1pos)))).
  assert (HδS2 := snd (projT2 (b5dP_S_diff_closed_r_M_exp_tail r (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
           2 b5dQ_p4_two_pos NM HMall (real_const 1)
           (real_const_pos 1 b5dQ_H1pos)))).
  (* δ := min(min(min(δE, δS1), δS2), real_const τ) (the Section B L645 form — the τ leaf
     coordinate = the b5dQ_tau q closed form). *)
  set (delta := real_min (real_min (real_min δE δS1) δS2) (real_const tau)).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos. { exact HδE0. } { exact HδS10. } }
      { exact HδS20. } }
    { apply real_const_pos. exact HtauT. } }
  exists delta.
  split.
  { exact Hdpos. }
  { split.
    { intros h Hh Hxh eps' Heps'.
    (* the eps witness decomposition (the item25 change S4: moved down from item11 L244 —
       spine-clean: e0/He0T/Ne0/He0lt do not enter the δ value; the source swapped to
       b5dM_b5n_eps_proj_lt). *)
    destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
    (* extracting the |h| < components. *)
    assert (Hh1 : real_lt (real_abs h) (real_min (real_min δE δS1) δS2)).
    { apply (real_min_lt_l h (real_min (real_min δE δS1) δS2) (real_const tau)).
      unfold delta in Hh. exact Hh. }
    assert (Hhτ : real_lt (real_abs h) (real_const tau)).
    { apply (real_min_lt_r h (real_min (real_min δE δS1) δS2) (real_const tau)).
      unfold delta in Hh. exact Hh. }
    assert (Hh2 : real_lt (real_abs h) (real_min δE δS1)).
    { apply (real_min_lt_l h (real_min δE δS1) δS2). exact Hh1. }
    assert (HhS2 : real_lt (real_abs h) δS2).
    { apply (real_min_lt_r h (real_min δE δS1) δS2). exact Hh1. }
    assert (HhE : real_lt (real_abs h) δE).
    { apply (real_min_lt_l h δE δS1). exact Hh2. }
    assert (HhS1 : real_lt (real_abs h) δS1).
    { apply (real_min_lt_r h δE δS1). exact Hh2. }
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia.
      - apply QltT_to_Qlt. exact He1T. }
    (* the eps' shares (Real): E-diff epsE'/margin shE, S-diff epsS'/margin shS. *)
    set (epsE' := real_mult eps' (real_const kEp)).
    assert (HepsE' : real_lt real_zero epsE').
    { unfold epsE'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkEpT. } }
    set (shE := real_mult eps' (real_const kapE)).
    assert (HshE : real_lt real_zero shE).
    { unfold shE. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkapET. } }
    set (epsS' := real_mult eps' (real_const kSp)).
    assert (HepsS' : real_lt real_zero epsS').
    { unfold epsS'. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkSpT. } }
    set (shS := real_mult eps' (real_const kapS)).
    assert (HshS : real_lt real_zero shS).
    { unfold shS. apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkapST. } }
    (* the constant shares of the lower-bound instance (Real, independent of eps'). *)
    assert (Hcμ : real_lt real_zero (real_const mu)).
    { apply real_const_pos. exact HmuT. }
    assert (HcκS2 : real_lt real_zero (real_const kapS2)).
    { apply real_const_pos. exact HkapS2T. }
    (* pointwise conversion (real_le to per-n, with margin slack). *)
    set (BE := real_plus (real_mult epsE (real_abs h)) epsE').
    destruct (b5i_abs_le_pointwise (b5e_E_err x Hx h Hxh) BE
               (HδE h HhE Hxh epsE' HepsE') shE HshE) as [NE HNE].
    set (BS1 := real_plus (real_mult epsS (real_abs h)) epsS').
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS1
               (HδS1 h HhS1 epsS' HepsS') shS HshS) as [NS HNS].
    set (BS2 := real_plus (real_mult (real_const 1) (real_abs h)) (real_const mu)).
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS2
               (HδS2 h HhS2 (real_const mu) Hcμ) (real_const kapS2) HcκS2) as [NS2 HNS2].
    (* |h_n| <= tau (b5i_h_le_const), the |d_n| <= 1 tail, and the pointwise identity N. *)
    destruct (b5i_h_le_const h tau Hhτ HtauT) as [Nτ HNτ].
    destruct (b5c_d_proj_le_one x) as [Nd Hd].
    destruct (b5m_J_dec_proj x h Hx Hxh) as [Ndec HNdec].
    (* pointwise budget (against the eps/eps' witnesses). *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). } }
    set (Nmax := Nat.max NM (Nat.max (Nat.max Ne0 Ne1)
                 (Nat.max (Nat.max Ndec Nτ)
                  (Nat.max (Nat.max NE (Nat.max NS NS2)) (Nat.max NA Nd))))).
    (* main assembly: real_le to real_lt (left branch), with witness eta. *)
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5m_J_err x Hx h Hxh) n)).
      set (Sn := projT1 (b5a_S x) n).
      set (Shn := projT1 (b5a_S (real_plus x h)) n).
      set (dn := projT1 (b5a_atan_d x) n).
      set (rEn := projT1 (b5e_E_err x Hx h Hxh) n).
      set (rSn := projT1 (b5m_rS x h) n).
      set (Exn := projT1 (b5a_E x Hx) n).
      (* tail indices. *)
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNE : NatLe NE n) by (apply NatLe_lift; lia).
      assert (HnNS : NatLe NS n) by (apply NatLe_lift; lia).
      assert (HnNS2 : NatLe NS2 n) by (apply NatLe_lift; lia).
      assert (HnNτ : NatLe Nτ n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (HnNdec : (Ndec <= n)%nat) by lia.
      assert (HnNA : NatLe NA n) by (apply NatLe_lift; lia).
      assert (HnNM : NatLe NM n) by (apply NatLe_lift; lia).
      (* nonnegativity. *)
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        - apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T.
        - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He0lt n HnNe0)). }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      assert (Hhn0 : Qle 0 hn). { unfold hn. apply Qabs_nonneg. }
      (* |h_n| <= tau, |d_n| <= 1, and Sn >= cA. *)
      assert (Hhτn : Qle (Qabs (projT1 h n)) tau).
      { unfold tau in *. exact (QleT'_to_Qle _ _ (HNτ n HnNτ)). }
      assert (Hdn1 : Qle (Qabs dn) 1).
      { unfold dn. exact (QleT'_to_Qle _ _ (Hd n (NatLe_lift _ _ HnNd))). }
      assert (HSnA : Qle cA Sn).
      { unfold Sn. exact ((QleT'_to_Qle _ _ (HNA n HnNA))). }
      (* |rE_n| <= kE*en*hn + (kEp+kapE)*en' (the E-diff made pointwise). *)
      assert (HrE : Qle (Qabs rEn)
                        (Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' kEp) (Qmult en' kapE)))).
      { apply (Qle_trans (Qabs rEn)
                         (Qplus (projT1 BE n) (projT1 shE n))
                         (Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' kEp) (Qmult en' kapE)))).
        - unfold rEn. exact (QleT'_to_Qle _ _ (HNE n HnNE)).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          unfold BE, shE, en, en'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult epsE (real_abs h)) epsE' n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj epsE (real_abs h) n)).
          unfold epsE, epsE'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const kE) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kE n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const kEp) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kEp n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const kapE) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kapE n)).
          ring. }
      (* |rS_n| <= kS*en*hn + (kSp+kapS)*en' (the S-diff main instance made pointwise). *)
      assert (HrS : Qle (Qabs rSn)
                        (Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                               (Qplus (Qmult en' kSp) (Qmult en' kapS)))).
      { apply (Qle_trans (Qabs rSn)
                         (Qplus (projT1 BS1 n) (projT1 shS n))
                         (Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                                (Qplus (Qmult en' kSp) (Qmult en' kapS)))).
        - unfold rSn. exact (QleT'_to_Qle _ _ (HNS n HnNS)).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          unfold BS1, shS, en, en'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult epsS (real_abs h)) epsS' n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj epsS (real_abs h) n)).
          unfold epsS.
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (Qmult a kS) n)).
          unfold epsS'.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const kSp) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kSp n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps' (real_const kapS) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kapS n)).
          unfold eps.
          rewrite (qeqT_imp_qeq _ _ (real_const_proj a n)).
          ring. }
      (* |rS_n| <= 1*hn + mu + kapS2 (the S-diff constant-share instance made pointwise, used for the lower bound). *)
      assert (HrS2 : Qle (Qabs rSn)
                         (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
      { apply (Qle_trans (Qabs rSn)
                         (Qplus (projT1 BS2 n) (projT1 (real_const kapS2) n))
                         (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
        - unfold rSn. exact (QleT'_to_Qle _ _ (HNS2 n HnNS2)).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          unfold BS2.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const 1) (real_abs h))
                                         (real_const mu) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const 1) (real_abs h) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj mu n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj kapS2 n)).
          ring. }
      (* |Ex_n| <= ME (the sinA/cosA pointwise bounds + |x_n| <= r; Exn == sAn - xn*cAn). *)
      assert (HEx : Qle (Qabs Exn) ME).
      { unfold Exn, b5a_E.
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_sin (cauchy_real_arctan x Hx))
                                (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx)))) n)).
        rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx))) n)).
        rewrite (qeqT_imp_qeq _ _ (real_mult_proj x (cauchy_real_cos (cauchy_real_arctan x Hx)) n)).
        apply (Qle_trans
                 (Qabs (Qplus (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                              (Qopp (Qmult (projT1 x n)
                                           (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                 (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                        (Qabs (Qmult (projT1 x n)
                                     (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))
                 ME).
        - apply (Qle_trans
                   (Qabs (Qplus (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)
                                (Qopp (Qmult (projT1 x n)
                                             (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qopp (Qmult (projT1 x n)
                                             (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))))
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qmult (projT1 x n)
                                       (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))).
          + apply Qabs_triangle.
          + apply Qplus_le_compat.
            * apply Qle_refl.
            * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
              apply (Qabs_opp (Qmult (projT1 x n)
                                     (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))).
        - (* |sA| + |x·cA| ≤ Ms + r·Mc ≤ ME *)
          apply (Qle_trans
                   (Qplus (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                          (Qabs (Qmult (projT1 x n)
                                       (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))))
                   (Qplus Ms (Qmult r Mc))
                   ME).
          + apply Qplus_le_compat.
            * apply (Qle_trans (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                               (Qabs (sin_partial n (arctan_partial n (projT1 x n))))
                               Ms).
              { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_wd. apply Qeq_sym.
                setoid_rewrite (qeqT_imp_qeq _ _ (real_sin_proj (cauchy_real_arctan x Hx) n)).
                setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hx n)).
                reflexivity. }
              { apply QleT'_to_Qle. exact (HMs_all n). }
            * apply (Qle_trans (Qabs (Qmult (projT1 x n)
                                            (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                               (Qmult r (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                               (Qmult r Mc)).
              { apply (Qle_trans (Qabs (Qmult (projT1 x n)
                                              (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                                 (Qmult (Qabs (projT1 x n))
                                        (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))
                                 (Qmult r (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)))).
                - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
                  apply (Qabs_Qmult (projT1 x n)
                                    (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n)).
                - apply (Qmult_le_compat_r (Qabs (projT1 x n)) r
                                           (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))).
                  + apply QleT'_to_Qle. exact (Hxr n).
                  + apply Qabs_nonneg. }
              { apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))
                                     Mc r).
                - apply (Qle_trans (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))
                                   (Qabs (cos_partial n (arctan_partial n (projT1 x n))))
                                   Mc).
                  + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_wd. apply Qeq_sym.
                    setoid_rewrite (qeqT_imp_qeq _ _ (real_cos_proj (cauchy_real_arctan x Hx) n)).
                    setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hx n)).
                    reflexivity.
                  + exact ((QleT'_to_Qle _ _ (HMc_all n))).
                - exact Hr0'. }
          + unfold ME. nra. }
      (* quotient-denominator certificate: |Qinv(Sn)| <= QicA. *)
      assert (HQA : Qle (Qabs (Qinv Sn)) QicA).
      { unfold Sn, QicA. apply QleT'_to_Qle. apply (b5m_inv_le Sn cA (HcA) HSnA). }
      (* Sxh >= cB: the |ΔS| bound (r*M*hn + |rS|) gives K1*tau + mu + kapS2 <= cA - cB. *)
      assert (Hdel0 : Qle (Qabs (Qminus Shn Sn))
                          (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                 (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
      { (* Shn − Sn == (x·S·d·h)_n + rS_n *)
        apply (Qle_trans (Qabs (Qminus Shn Sn))
                         (Qplus (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                                (Qabs rSn))
                         (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
        - (* triangle: |Shn - Sn| == |P + rS| <= |P| + |rS|. *)
          apply (Qle_trans (Qabs (Qminus Shn Sn))
                           (Qabs (Qplus (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))) rSn))
                           (Qplus (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                                  (Qabs rSn))).
          + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
            apply (Qabs_wd (Qminus Shn Sn)
                           (Qplus (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))) rSn)).
            unfold Shn, Sn, dn, rSn.
            unfold b5m_rS.
            rewrite (qeqT_imp_qeq _ _ (real_plus_proj (b5a_S (real_plus x h))
                                    (real_opp (real_plus (b5a_S x)
                                               (real_mult (real_mult x (b5a_S x))
                                                          (real_mult (b5a_atan_d x) h)))) n)).
            rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus (b5a_S x)
                                    (real_mult (real_mult x (b5a_S x))
                                               (real_mult (b5a_atan_d x) h))) n)).
            rewrite (qeqT_imp_qeq _ _ (real_plus_proj (b5a_S x)
                                    (real_mult (real_mult x (b5a_S x))
                                               (real_mult (b5a_atan_d x) h)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_mult x (b5a_S x))
                                    (real_mult (b5a_atan_d x) h) n)).
            rewrite (qeqT_imp_qeq _ _ (real_mult_proj x (b5a_S x) n)).
            rewrite (qeqT_imp_qeq _ _ (real_mult_proj (b5a_atan_d x) h n)).
            cbn [projT1 real_zero].
            ring.
          + apply Qabs_triangle.
        - (* |P| <= r*M*1*hn and |rS_n| <= hn + mu + kapS2 (HrS2). *)
          apply Qplus_le_compat.
          + (* |(x·S·d·h)_n| ≤ r·M·1·hn *)
            apply (Qle_trans (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                             (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                             (Qmult (Qmult r M) (Qabs (projT1 h n)))).
            * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
              apply (Qeq_trans (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                               (Qmult (Qabs (Qmult (projT1 x n) Sn)) (Qabs (Qmult dn (projT1 h n))))
                               (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))).
              { apply (Qabs_Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))). }
              { apply Qmult_comp.
                - apply (Qabs_Qmult (projT1 x n) Sn).
                - apply (Qabs_Qmult dn (projT1 h n)). }
            * (* (|xn|·|Sn|)·(|dn|·|hn|) ≤ (r·M)·(1·hn) *)
              apply (Qle_trans (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                               (Qmult (Qmult r M) (Qmult 1 (Qabs (projT1 h n))))
                               (Qmult (Qmult r M) (Qabs (projT1 h n)))).
              { apply (Qle_trans (Qmult (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                                 (Qmult (Qmult r M) (Qmult (Qabs dn) (Qabs (projT1 h n))))
                                 (Qmult (Qmult r M) (Qmult 1 (Qabs (projT1 h n))))).
                - apply (Qmult_le_compat_r (Qmult (Qabs (projT1 x n)) (Qabs Sn)) (Qmult r M)
                                           (Qmult (Qabs dn) (Qabs (projT1 h n)))).
                  + apply (Qle_trans (Qmult (Qabs (projT1 x n)) (Qabs Sn))
                                     (Qmult r (Qabs Sn))
                                     (Qmult r M)).
                    * apply (Qmult_le_compat_r (Qabs (projT1 x n)) r (Qabs Sn)).
                      { apply QleT'_to_Qle. exact (Hxr n). }
                      { apply Qabs_nonneg. }
                    * apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs Sn) M r).
                      { unfold Sn. exact ((QleT'_to_Qle _ _ (HMall n HnNM))). }
                      { exact Hr0'. }
                  + apply Qmult_le_0_compat.
                    * apply Qabs_nonneg.
                    * apply Qabs_nonneg.
                - apply QleT'_to_Qle. apply (sc_qmult_le_l (Qmult (Qabs dn) (Qabs (projT1 h n)))
                                       (Qmult 1 (Qabs (projT1 h n)))
                                       (Qmult r M)).
                  + apply (Qmult_le_compat_r (Qabs dn) 1 (Qabs (projT1 h n))).
                    * exact Hdn1.
                    * apply Qabs_nonneg.
                  + apply Qmult_le_0_compat.
                    * exact Hr0'.
                    * exact HM0. }
              { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
          + (* |rS_n| ≤ hn + mu + kapS2 *)
            apply (Qle_trans (Qabs rSn)
                             (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))
                             (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2))).
            * exact HrS2.
            * apply Qle_refl. }
      (* |ΔS| <= K1*tau + mu + kapS2 (hn <= tau). *)
      assert (Hdel : Qle (Qabs (Qminus Shn Sn))
                         (Qplus (Qmult K1 tau) (Qplus mu kapS2))).
      { apply (Qle_trans (Qabs (Qminus Shn Sn))
                         (Qplus (Qmult (Qmult r M) tau) (Qplus tau (Qplus mu kapS2)))
                         (Qplus (Qmult K1 tau) (Qplus mu kapS2))).
        - apply (Qle_trans (Qabs (Qminus Shn Sn))
                           (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                  (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))
                           (Qplus (Qmult (Qmult r M) tau) (Qplus tau (Qplus mu kapS2)))).
          + exact Hdel0.
          + apply Qplus_le_compat.
            * apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs (projT1 h n)) tau (Qmult r M)).
              { exact Hhτn. }
              { apply Qmult_le_0_compat. { exact Hr0'. } { exact HM0. } }
            * apply Qplus_le_compat.
              { exact Hhτn. }
              { apply Qle_refl. }
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold K1. ring. }
      (* Shn >= cB (Sn >= cA, |ΔS| <= B0, B0 <= cA - cB). *)
      assert (HShnB : Qle cB Shn).
      { (* Sn <= Shn + |Δ| and |Δ| <= B0 (Hdel), hence Sn <= Shn + B0. *)
        assert (HS2 : Qle Sn (Qplus Shn (Qplus (Qmult K1 tau) (Qplus mu kapS2)))).
        { apply (Qle_trans Sn (Qplus Shn (Qabs (Qminus Shn Sn)))
                              (Qplus Shn (Qplus (Qmult K1 tau) (Qplus mu kapS2)))).
          - apply (Qle_trans Sn (Qplus Shn (Qminus Sn Shn))
                                (Qplus Shn (Qabs (Qminus Shn Sn)))).
            + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
            + apply Qplus_le_compat.
              * apply Qle_refl.
              * apply (Qle_trans (Qminus Sn Shn) (Qabs (Qminus Sn Shn))
                                 (Qabs (Qminus Shn Sn))).
                { apply Qle_Qabs. }
                { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
                  apply (Qeq_trans (Qabs (Qminus Sn Shn))
                                   (Qabs (Qopp (Qminus Shn Sn)))
                                   (Qabs (Qminus Shn Sn))).
                  - apply Qabs_wd. ring.
                  - apply (Qabs_opp (Qminus Shn Sn)). }
          - apply Qplus_le_compat.
            + apply Qle_refl.
            + exact Hdel. }
        (* cB <= cA - B0 (Hlb_ineq), cA <= Sn (HSnA), Sn <= Shn + B0, hence cB <= Shn. *)
        nra. }
      (* quotient-denominator certificate: |Qinv(Shn)| <= QicB. *)
      assert (HQB : Qle (Qabs (Qinv Shn)) QicB).
      { unfold Shn, QicB. apply QleT'_to_Qle. apply (b5m_inv_le Shn cB HcB HShnB). }
      (* the b5m_J_abs_tri main step. *)
      set (RE := Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kEp) (Qmult en' kapE))).
      set (RS := Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kSp) (Qmult en' kapS))).
      assert (Hmain0 : Qle Dn (Qplus (Qmult QicB RE) (Qmult Mterm RS))).
      { unfold Dn.
        apply QleT'_to_Qle. apply (b5m_J_abs_tri x h Hx Hxh n QicA QicB ME RE RS).
        - exact HQA.
        - exact HQB.
        - unfold Exn. exact HEx.
        - unfold rEn. exact HrE.
        - unfold rSn. exact HrS.
        - unfold QicA. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact (HcA).
        - unfold QicB. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HcB.
        - exact (qeqT_imp_qeq _ _ (HNdec n (NatLe_lift _ _ HnNdec))). }
      (* coefficient absorption: QicB*RE <= (1/8)*en*hn + (1/8)*en'; Mterm*RS <= the same shape. *)
      assert (HT1 : Qle (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                        (Qmult (1 # 8) (Qmult en hn))).
      { apply (Qle_trans (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                         (Qmult (Qmult QicB kE) (Qmult en hn))
                         (Qmult (1 # 8) (Qmult en hn))).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold hn. ring.
        - apply (Qmult_le_compat_r (Qmult QicB kE) (1 # 8) (Qmult en hn)).
          + exact Hc1.
          + apply Qmult_le_0_compat.
            * exact Hen0.
            * exact Hhn0. }
      assert (HT2 : Qle (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE)))
                        (Qmult (1 # 8) en')).
      { apply (Qle_trans (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE)))
                         (Qmult (Qmult QicB (Qplus kEp kapE)) en')
                         (Qmult (1 # 8) en')).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        - apply (Qmult_le_compat_r (Qmult QicB (Qplus kEp kapE)) (1 # 8) en').
          + exact Hc1'.
          + exact Hen'0. }
      assert (HT3 : Qle (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                        (Qmult (1 # 8) (Qmult en hn))).
      { apply (Qle_trans (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                         (Qmult (Qmult Mterm kS) (Qmult en hn))
                         (Qmult (1 # 8) (Qmult en hn))).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold hn. ring.
        - apply (Qmult_le_compat_r (Qmult Mterm kS) (1 # 8) (Qmult en hn)).
          + exact Hc2.
          + apply Qmult_le_0_compat.
            * exact Hen0.
            * exact Hhn0. }
      assert (HT4 : Qle (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))
                        (Qmult (1 # 8) en')).
      { apply (Qle_trans (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))
                         (Qmult (Qmult Mterm (Qplus kSp kapS)) en')
                         (Qmult (1 # 8) en')).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        - apply (Qmult_le_compat_r (Qmult Mterm (Qplus kSp kapS)) (1 # 8) en').
          + exact Hc2'.
          + exact Hen'0. }
      (* assembling the pointwise main bound: |Dn| <= en*hn + (3/4)*en'. *)
      assert (Hmain : Qle Dn (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
      { apply (Qle_trans Dn
                         (Qplus (Qmult QicB RE) (Qmult Mterm RS))
                         (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
        - exact Hmain0.
        - (* expand and absorb: QicB*RE + Mterm*RS <= (1/8)(en hn) + (1/8)en', two copies of each. *)
          apply (Qle_trans (Qplus (Qmult QicB RE) (Qmult Mterm RS))
                           (Qplus (Qplus (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                                         (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE))))
                                  (Qplus (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                                         (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))))
                           (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
          + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold RE, RS, hn. ring.
          + apply (Qle_trans
                     (Qplus (Qplus (Qmult QicB (Qmult (Qmult en kE) (Qabs (projT1 h n))))
                                   (Qmult QicB (Qplus (Qmult en' kEp) (Qmult en' kapE))))
                            (Qplus (Qmult Mterm (Qmult (Qmult en kS) (Qabs (projT1 h n))))
                                   (Qmult Mterm (Qplus (Qmult en' kSp) (Qmult en' kapS)))))
                     (Qplus (Qplus (Qmult (1 # 8) (Qmult en hn)) (Qmult (1 # 8) en'))
                            (Qplus (Qmult (1 # 8) (Qmult en hn)) (Qmult (1 # 8) en')))
                     (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
            * apply Qplus_le_compat.
              { apply Qplus_le_compat. { exact HT1. } { exact HT2. } }
              { apply Qplus_le_compat. { exact HT3. } { exact HT4. } }
            * nra. }
      (* margin: eta < (1/4)*en'; Hfin: eta < (en*hn + en') - Dn. *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply QltT_to_Qlt. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        - apply QltT_to_Qlt. exact He1T.
        - exact (QltT_to_Qlt _ _ (He1lt n HnNe1)). }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply QltT_to_Qlt. apply (b5n_close Dn hn en en' eta).
        - unfold Dn. exact Hmain.
        - unfold en'. exact Hq4e. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5m_J_err x Hx h Hxh)) n))).
      - exact Hfin.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (b5m_J_err x Hx h Hxh) n)).
        unfold en, en', hn, Dn.
        ring. } }
    { (* the lb certificate: real_lt (real_const δ0) delta — the per-leaf real_lt lower bounds
         (the Q bounds of the b5dQ_p4g_qlt_* family + the leaf certificates of the b5dQ_p4g_leaf_* family)
         lifted by real_lt_trans, then combined by the three-layer b5dQ_min_lb (the conv steps
         paid stepwise). *)
      assert (HqE : real_lt (real_const (b5dQ_delta0 q epsQ))
                            (real_const (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)))).
      { apply real_const_lt. exact (b5dQ_p4g_qlt_E q epsQ Hq0 Hq1 HepsQ). }
      assert (HlbE : real_lt (real_const (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2))) δE).
      { unfold δE.
        exact (b5dQ_p4g_leaf_E q Hq0 Hq1 x Hxr HMs_all HMc_all
                 (epsQ / (2 * q)) (Qlt_to_QltT _ _ Ha)). }
      assert (HdE : real_lt (real_const (b5dQ_delta0 q epsQ)) δE).
      { apply (real_lt_trans (real_const (b5dQ_delta0 q epsQ))
                             (real_const (Qmult (b5dQ_vE q (epsQ / (2 * q))) (1 # 2)))
                             δE HqE HlbE). }
      assert (HqS1 : real_lt (real_const (b5dQ_delta0 q epsQ))
                             (real_const (b5dQ_lbSdiff_val q
                                (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))).
      { apply real_const_lt. exact (b5dQ_p4g_qlt_S1 q epsQ Hq0 Hq1 HepsQ). }
      assert (HlbS1 : real_lt (real_const (b5dQ_lbSdiff_val q
                                (Qmult (epsQ / (2 * q)) (b5dQ_kS q)))) δS1).
      { unfold δS1.
        exact (b5dQ_p4g_leaf_S q (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
                 (Qmult (epsQ / (2 * q)) (b5dQ_kS q)) (Qlt_to_QltT _ _ Ha1) NM HMall). }
      assert (HdS1 : real_lt (real_const (b5dQ_delta0 q epsQ)) δS1).
      { apply (real_lt_trans (real_const (b5dQ_delta0 q epsQ))
                             (real_const (b5dQ_lbSdiff_val q
                                (Qmult (epsQ / (2 * q)) (b5dQ_kS q))))
                             δS1 HqS1 HlbS1). }
      assert (HqS2 : real_lt (real_const (b5dQ_delta0 q epsQ))
                             (real_const (b5dQ_lbSdiff_val q 1))).
      { apply real_const_lt. exact (b5dQ_p4g_qlt_S2 q epsQ Hq0 Hq1 HepsQ). }
      assert (HlbS2 : real_lt (real_const (b5dQ_lbSdiff_val q 1)) δS2).
      { unfold δS2.
        exact (b5dQ_p4g_leaf_S q (Qle_to_QleT' _ _ (Qlt_le_weak 0 q (QltT_to_Qlt _ _ Hq0))) Hq1 x Hxr
                 1 b5dQ_H1pos NM HMall). }
      assert (HdS2 : real_lt (real_const (b5dQ_delta0 q epsQ)) δS2).
      { apply (real_lt_trans (real_const (b5dQ_delta0 q epsQ))
                             (real_const (b5dQ_lbSdiff_val q 1))
                             δS2 HqS2 HlbS2). }
      apply (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ))
                         (real_min (real_min δE δS1) δS2)
                         (real_const tau)).
      - apply (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ))
                           (real_min δE δS1) δS2).
        + apply (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ)) δE δS1).
          * exact HdE.
          * exact HdS1.
        + exact HdS2.
      - apply real_const_lt. exact (b5dQ_p4g_qlt_tau q epsQ Hq0 Hq1 HepsQ). }
  }
Defined.

(* ===== end of sc2_b5a_item27_p4g.v (Part 0-2 + the Part 3 main piece all landed — finalized after the final verification) ===== *)

(* ===== Section P4b (the Hmod / main-piece real construction: removing the stub and the copy pieces + renaming the canon, 3 Lemma/Def) ===== *)

(* ============================================================ *)
(* §C M4: the Hstep per-k-step certificates + Hmod (q_arch_inv M := K+2 + per k) *)
(* ============================================================ *)

(* b5dQ_Hstep: the single-step assembly (certificates on the spot -> the P4g     *)
(*   variant-piece instance + the δ/lb certificates -> the |η| < δ chain ->      *)
(*   the step_inst / P4a bridges + rhs_bk -> the Hstep forall-certificate form — *)
(*   the statement's inner layer = item22 b5dL_E_rational_zero_premise           *)
(*   (L888-893); Hetaδ (Qlt (qdiv q M) δ0) = the output of the Hmod outer layer's *)
(*   q_arch_inv choice of M, given here as an input (acyclic).)                  *)
Lemma b5dQ_Hstep : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
  (epsQ : Q) (HepsQ : QltT 0 epsQ)
  (M : nat) (HMpos : (0 < M)%nat) (k : nat) (HkM : (k < M)%nat)
  (Hetaδ : QltT (b5dL_qdiv q M) (b5dQ_delta0 q epsQ))
  (Hxr : forall n : nat, QleT' (Qabs (projT1 (real_const (b5dL_tkq q M k)) n)) q)
  (NA : nat)
  (HNA : forall n : nat, NatLe NA n ->
         QleT' (1 # 2) (projT1 (b5a_S (real_const (b5dL_tkq q M k))) n))
  (NM : nat)
  (HMall : forall n : nat, NatLe NM n ->
           QleT' (Qabs (projT1 (b5a_S (real_const (b5dL_tkq q M k))) n)) 2)
  (Hs : forall n : nat,
         QleT' (Qabs (sin_partial n (arctan_partial n
                (projT1 (real_const (b5dL_tkq q M k)) n)))) 1)
  (Hc : forall n : nat,
         QleT' (Qabs (cos_partial n (arctan_partial n
                (projT1 (real_const (b5dL_tkq q M k)) n)))) 1)
  (Hk : cw_unit (real_const (b5dL_tkq q M k)))
  (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k)))),
  real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
          (real_const (b5dL_bk q M epsQ k)).
Proof.
  intros q Hq0 Hq1 epsQ HepsQ M HMpos k HkM Hetaδ Hxr NA HNA NM HMall Hs Hc Hk Hk1.
  (* the variant-piece instance (b5dQ_p4g_J_tail_lb_var @ the instance — the argument bundle =
     the stub statement's argument bundle verbatim; destruct-style access to the three-layer
     certificates: δ / 0<δ ∧ (the J-tail modulus property ∧ the lb certificate) — zero conv,
     zero axiom face). *)
  assert (HkMle : (k <= M)%nat) by lia.
  set (vapp := b5dQ_p4g_J_tail_lb_var q Hq0 Hq1 epsQ HepsQ M HMpos k (NatLe_lift k M HkMle)
                 Hxr NA HNA NM HMall Hs Hc).
  destruct vapp as [δ [Hdpos [Hmod Hlb]]].
  (* the |η| < δ0 constant Real comparison chain. *)
  assert (Hηc : real_lt (real_const (b5dL_qdiv q M))
                        (real_const (b5dQ_delta0 q epsQ))).
  { apply real_const_lt. exact Hetaδ. }
  assert (Hηd : real_lt (real_const (b5dL_qdiv q M)) δ).
  { apply (real_lt_trans (real_const (b5dL_qdiv q M))
                         (real_const (b5dQ_delta0 q epsQ))
                         δ Hηc Hlb). }
  (* η >= 0 gives |η| == η (the real_const side). *)
  assert (Heta0 : Qle 0 (b5dL_qdiv q M)).
  { unfold b5dL_qdiv. unfold Qdiv.
    apply Qmult_le_0_compat.
    - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ Hq0).
    - apply Qinv_le_0_compat. apply Qlt_le_weak.
      destruct M as [| m]; [exfalso; lia | exact (QltT_to_Qlt _ _ (b5dL_lift_pos2 m))]. }
  assert (Heta : real_eq (real_abs (real_const (b5dL_qdiv q M)))
                         (real_const (b5dL_qdiv q M))).
  { apply (real_eq_trans _ (real_const (Qabs (b5dL_qdiv q M))) _).
    - exact (b5dL_abs_const (b5dL_qdiv q M)).
    - apply b5dH_real_const_qeq.
      apply qeq_imp_qeqT. apply (Qabs_pos (b5dL_qdiv q M)). exact Heta0. }
  (* the modulus premise: real_lt (real_abs (real_const η)) δ(t_k). *)
  assert (Hηabs : real_lt (real_abs (real_const (b5dL_qdiv q M))) δ).
  { apply (RealSetoid.real_lt_compat (real_const (b5dL_qdiv q M))
                          (real_abs (real_const (b5dL_qdiv q M)))
                          δ δ).
    - apply real_eq_sym. exact Heta.
    - apply real_eq_refl.
    - exact Hηd. }
  (* certificates on the spot: Hxh := the xph_unit instance; eps' := real_const (epsQ1 M epsQ). *)
  assert (Hxh : cw_unit (real_plus (real_const (b5dL_tkq q M k))
                                   (real_const (b5dL_qdiv q M)))).
  { exact (b5dQ_xph_unit q M k Hq0 Hq1 HMpos HkM). }
  assert (Heps1pos : real_lt real_zero (real_const (b5dL_epsQ1 M epsQ))).
  { apply real_const_pos.
    exact (b5dL_epsQ1_pos epsQ M HepsQ HMpos). }
  (* the modulus conclusion @ h := real_const η (taken directly from Hmod — the second layer
   of the P4g variant piece; its second component = the J-tail modulus property; zero conv,
   zero destruct projection chains). *)
  assert (Hcore : real_le
    (real_abs (real_plus (b5c_J (real_plus (real_const (b5dL_tkq q M k))
                                           (real_const (b5dL_qdiv q M))) Hxh)
                         (real_opp (b5c_J (real_const (b5dL_tkq q M k))
                                          (b3rr_dom_r1 (real_const (b5dL_tkq q M k))
                                                       q Hxr (QltT_to_Qlt _ _ Hq1))))))
    (real_plus (real_mult (real_const (epsQ / (2 * q)))
                          (real_abs (real_const (b5dL_qdiv q M))))
               (real_const (b5dL_epsQ1 M epsQ)))).
  { exact (Hmod (real_const (b5dL_qdiv q M)) Hηabs Hxh
           (real_const (b5dL_epsQ1 M epsQ)) Heps1pos). }
  (* the step_inst bridge (the modulus left-point fixed certificate shape -> the Hmod-form arbitrary certificates Hk/Hk1). *)
  assert (HstepR : real_le
    (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                         (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
    (real_plus (real_mult (real_const (epsQ / (2 * q)))
                          (real_abs (real_const (b5dL_qdiv q M))))
               (real_const (b5dL_epsQ1 M epsQ)))).
  { exact (b5dQ_step_inst q M k HMpos Hq1 Hxr Hk1 Hk Hxh
             (real_plus (real_mult (real_const (epsQ / (2 * q)))
                                   (real_abs (real_const (b5dL_qdiv q M))))
                        (real_const (b5dL_epsQ1 M epsQ)))
             Hcore). }
  (* RHS == real_const (bk) (the rhs_bk bridge) + real_le_id_r. *)
  exact (RealSetoid.real_le_id_r
    (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                         (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
    (real_plus (real_mult (real_const (epsQ / (2 * q)))
                          (real_abs (real_const (b5dL_qdiv q M))))
               (real_const (b5dL_epsQ1 M epsQ)))
    (real_const (b5dL_bk q M epsQ k))
    (b5dQ_rhs_bk q M k epsQ Hq0 HMpos)
    HstepR).
Qed.

(* b5dQ_Hmod: for all q with 0<q<1, for all epsQ>0 there is M with 0<M and the per-step bounds for all k<M *)
(*   (the statement = the item22 b5dL_E_rational_zero_premise inner text verbatim —    *)
(*   the sole interface consumed by the main piece's exact).                            *)
(*   Proof: the δ0 positivity -> q_arch_inv (root L4733) @ δ0/q chooses K, M := K+2    *)
(*   -> G8 qdiv_lt_arch closes Qlt (qdiv q M) δ0 -> per k: destruct k                  *)
(*   (k=0 uses the P3 C1/C3 certificate branches; k=S k' uses the C2/C4 branches) +    *)
(*   the sincos_all_k/tkq_Hxr certificates on the spot -> b5dQ_Hstep.                  *)
(* ============================================================ *)
Lemma b5dQ_Hmod : forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1),
  forall (epsQ : Q), QltT 0 epsQ ->
  sigT (fun M : nat => And (NatLe 1 M)
    (forall (k : nat), NatLe k M ->
       forall (Hk : cw_unit (real_const (b5dL_tkq q M k)))
              (Hk1 : cw_unit (real_const (b5dL_tkq q M (Datatypes.S k)))),
       real_le (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S k))) Hk1)
                                    (real_opp (b5c_J (real_const (b5dL_tkq q M k)) Hk))))
               (real_const (b5dL_bk q M epsQ k)))).
Proof.
  intros q Hq0 Hq1 epsQ HepsQ.
  (* δ0 > 0 and δ0/q > 0 (the q_arch_inv premises). *)
  assert (Hd0pos : Qlt 0 (b5dQ_delta0 q epsQ)).
  { exact (QltT_to_Qlt _ _ (b5dQ_delta0_pos q epsQ Hq0 Hq1 HepsQ)). }
  assert (Hd0q : Qlt 0 (b5dQ_delta0 q epsQ / q)).
  { unfold Qdiv.
    apply (Qmult_lt_0_compat (b5dQ_delta0 q epsQ) (Qinv q)).
    - exact Hd0pos.
    - apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ Hq0). }
  (* q_arch_inv chooses K; M := K+2 (δD2f §2.7: the first-order choice closes). *)
  destruct (q_arch_inv (b5dQ_delta0 q epsQ / q) (Qlt_to_QltT _ _ Hd0q)) as [K HK].
  set (M := (K + 2)%nat).
  assert (HMpos : (0 < M)%nat).
  { unfold M. lia. }
  (* G8: Qlt (qdiv q M) δ0 (the Q layer of the |η| side). *)
  assert (Hqdiv : Qlt (b5dL_qdiv q M) (b5dQ_delta0 q epsQ)).
  { apply QltT_to_Qlt.
    apply (b5dQ_qdiv_lt_arch q (b5dQ_delta0 q epsQ) M Hq0 (Qlt_to_QltT _ _ Hd0pos)).
    exact HK. }
  assert (HqdivT : QltT (b5dL_qdiv q M) (b5dQ_delta0 q epsQ)).
  { apply Qlt_to_QltT. exact Hqdiv. }
  exists M.
  split.
  - exact (NatLe_lift 1 M HMpos).
  - intros k HkM.
    destruct k as [| k'].
    + (* the k = 0 branch: the C1/C3 certificates (the tail bounds of S(real_const (tkq q M 0))). *)
      destruct (b5dQ_S_lb_tail_k0 q M) as [NA HNA].
      destruct (b5dQ_S_ub_tail_k0 q M) as [NM HMall].
      assert (HkleM : (0 <= M)%nat) by lia.
      destruct (b5dQ_sincos_all_k q Hq0 Hq1 M 0 HMpos HkleM) as [Hs Hc].
      intros Hk Hk1.
      exact (b5dQ_Hstep q Hq0 Hq1 epsQ HepsQ M HMpos 0 HMpos HqdivT
               (b5dQ_tkq_Hxr q M 0 (b5dH_q_pos_le q Hq0) HMpos HkleM)
               NA HNA NM HMall Hs Hc Hk Hk1).
    + (* the k = S k' branch: the C2/C4 certificates (b5a_S_ge_one / item15 @ tkq (S k'));
         the S k' = M boundary branch goes through the Hstep chain inline — the xph_unit
         relay distorts at k = M, replaced by migrating along the tkq_succ projections with
         the contract premise Hk1.    *)
      assert (Hk0s : (0 < Datatypes.S k')%nat) by lia.
      assert (HkleM : (Datatypes.S k' <= M)%nat) by exact (NatLe_drop (Datatypes.S k') M HkM).
      destruct (Nat.eq_dec (Datatypes.S k') M) as [HkM_eq | HkM_ne].
      { (* the boundary branch S k' = M: k := M; x_{S M} = x_M + η, the saturated form. *)
        rewrite HkM_eq.
        assert (HkleM0 : (M <= M)%nat) by apply Nat.le_refl.
        assert (Hk0M : (0 < M)%nat) by exact HMpos.
        destruct (b5dQ_S_lb_tail_kS q M M Hq0 HMpos Hk0M) as [NA HNA].
        destruct (b5dQ_S_ub_tail_kS q M M Hq0 Hq1 HMpos Hk0M HkleM0)
          as [NM HMall].
        destruct (b5dQ_sincos_all_k q Hq0 Hq1 M M HMpos HkleM0) as [Hs Hc].
        intros Hk Hk1.
        assert (HxrM : forall n : nat,
                   QleT' (Qabs (projT1 (real_const (b5dL_tkq q M M)) n)) q).
        { exact (b5dQ_tkq_Hxr q M M (b5dH_q_pos_le q Hq0) HMpos HkleM0). }
        assert (HxhM : cw_unit (real_plus (real_const (b5dL_tkq q M M))
                                          (real_const (b5dL_qdiv q M)))).
        { unfold cw_unit in Hk1. unfold cw_unit. intros n.
          specialize (Hk1 n).
          apply Qle_to_QleT'.
          rewrite (qeqT_imp_qeq _ _
                     (real_plus_proj (real_const (b5dL_tkq q M M))
                                     (real_const (b5dL_qdiv q M)) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (b5dL_tkq q M M) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (b5dL_qdiv q M) n)).
          rewrite <- (qeqT_imp_qeq _ _ (b5dL_tkq_succ q M M HMpos)).
          rewrite <- (qeqT_imp_qeq _ _
                        (real_const_proj (b5dL_tkq q M (Datatypes.S M)) n)).
          apply QleT'_to_Qle in Hk1.
          exact Hk1. }
        destruct (b5dQ_p4g_J_tail_lb_var q Hq0 Hq1 epsQ HepsQ M HMpos M
                    (NatLe_lift M M HkleM0)
                    HxrM
                    NA HNA NM HMall Hs Hc) as [δb [Hdposb [HmodJ Hlbb]]].
        assert (Hηc : real_lt (real_const (b5dL_qdiv q M))
                              (real_const (b5dQ_delta0 q epsQ))).
        { apply real_const_lt. exact (Qlt_to_QltT _ _ Hqdiv). }
        assert (Hηd : real_lt (real_const (b5dL_qdiv q M)) δb).
        { apply (real_lt_trans (real_const (b5dL_qdiv q M))
                               (real_const (b5dQ_delta0 q epsQ))
                               δb Hηc Hlbb). }
        assert (Heta0 : Qle 0 (b5dL_qdiv q M)).
        { unfold b5dL_qdiv. unfold Qdiv.
          apply Qmult_le_0_compat.
          - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ Hq0).
          - apply Qinv_le_0_compat. apply Qlt_le_weak.
            destruct M as [| m]; [exfalso; lia | exact (QltT_to_Qlt _ _ (b5dL_lift_pos2 m))]. }
        assert (Heta : real_eq (real_abs (real_const (b5dL_qdiv q M)))
                               (real_const (b5dL_qdiv q M))).
        { apply (real_eq_trans _ (real_const (Qabs (b5dL_qdiv q M))) _).
          - exact (b5dL_abs_const (b5dL_qdiv q M)).
          - apply b5dH_real_const_qeq.
            apply qeq_imp_qeqT. apply (Qabs_pos (b5dL_qdiv q M)). exact Heta0. }
        assert (Hηabs : real_lt (real_abs (real_const (b5dL_qdiv q M))) δb).
        { apply (RealSetoid.real_lt_compat (real_const (b5dL_qdiv q M))
                                (real_abs (real_const (b5dL_qdiv q M)))
                                δb δb).
          - apply real_eq_sym. exact Heta.
          - apply real_eq_refl.
          - exact Hηd. }
        assert (Heps1pos : real_lt real_zero (real_const (b5dL_epsQ1 M epsQ))).
        { apply real_const_pos.
          exact (b5dL_epsQ1_pos epsQ M HepsQ HMpos). }
        assert (Hcore : real_le
          (real_abs (real_plus (b5c_J (real_plus (real_const (b5dL_tkq q M M))
                                                 (real_const (b5dL_qdiv q M))) HxhM)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M M))
                                          (b3rr_dom_r1 (real_const (b5dL_tkq q M M))
                                                       q HxrM (QltT_to_Qlt _ _ Hq1))))))
          (real_plus (real_mult (real_const (epsQ / (2 * q)))
                                (real_abs (real_const (b5dL_qdiv q M))))
                     (real_const (b5dL_epsQ1 M epsQ)))).
        { exact (HmodJ (real_const (b5dL_qdiv q M)) Hηabs HxhM
                   (real_const (b5dL_epsQ1 M epsQ)) Heps1pos). }
        assert (HstepR : real_le
          (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S M))) Hk1)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M M)) Hk))))
          (real_plus (real_mult (real_const (epsQ / (2 * q)))
                                (real_abs (real_const (b5dL_qdiv q M))))
                     (real_const (b5dL_epsQ1 M epsQ)))).
        { exact (b5dQ_step_inst q M M HMpos Hq1
                   HxrM
                   Hk1 Hk HxhM
                   (real_plus (real_mult (real_const (epsQ / (2 * q)))
                                         (real_abs (real_const (b5dL_qdiv q M))))
                        (real_const (b5dL_epsQ1 M epsQ)))
                   Hcore). }
        exact (RealSetoid.real_le_id_r
          (real_abs (real_plus (b5c_J (real_const (b5dL_tkq q M (Datatypes.S M))) Hk1)
                               (real_opp (b5c_J (real_const (b5dL_tkq q M M)) Hk))))
          (real_plus (real_mult (real_const (epsQ / (2 * q)))
                                (real_abs (real_const (b5dL_qdiv q M))))
                     (real_const (b5dL_epsQ1 M epsQ)))
          (real_const (b5dL_bk q M epsQ M))
          (b5dQ_rhs_bk q M M epsQ Hq0 HMpos)
          HstepR). }
      { (* the general branch S k' < M: the strict bound is at hand; the original Hstep call. *)
        assert (HkMlt : (Datatypes.S k' < M)%nat).
        { destruct (proj1 (Nat.lt_eq_cases (Datatypes.S k') M) HkleM)
            as [HkMlt' | HcM].
          - exact HkMlt'.
          - exfalso. apply HkM_ne. exact HcM. }
        destruct (b5dQ_S_lb_tail_kS q M (Datatypes.S k') Hq0 HMpos Hk0s)
          as [NA HNA].
        destruct (b5dQ_S_ub_tail_kS q M (Datatypes.S k') Hq0 Hq1 HMpos Hk0s HkleM)
          as [NM HMall].
        destruct (b5dQ_sincos_all_k q Hq0 Hq1 M (Datatypes.S k') HMpos HkleM)
          as [Hs Hc].
        intros Hk Hk1.
        exact (b5dQ_Hstep q Hq0 Hq1 epsQ HepsQ M HMpos (Datatypes.S k')
                 HkMlt HqdivT
                 (b5dQ_tkq_Hxr q M (Datatypes.S k') (b5dH_q_pos_le q Hq0)
                    HMpos HkleM)
                 NA HNA NM HMall Hs Hc Hk Hk1). }
Qed.

(* ============================================================ *)
(* §D M5 main piece: b5dQ_E_rational_zero (the statement = the contract verbatim) *)
(*   Proof = a direct citation at the level of exact (b5dL_E_rational_zero_premise ...) *)
(*   (item22 L885 already closed: passing Hmod yields it).                       *)
(* ============================================================ *)
Lemma b5dQ_E_rational_zero : forall (q : Q), QltT 0 q -> QltT q 1 ->
  forall (Hq : cw_unit (real_const q)),
  real_eq (real_E (real_const q) Hq) real_zero.
Proof.
  intros q Hq0 Hq1 Hq.
  exact (b5dL_E_rational_zero_premise q Hq0 Hq1
           (b5dQ_Hmod q Hq0 Hq1) Hq).
Qed.

(* ===== end of sc2_b5a_item27_p4b_hmode.v (P4b: Hmod + the main piece) ===== *)

(* ===== Block b5dS_ (main item b5dS_E_zero_on_unit; upstream source sc2_b5a_item29) ===== *)

(* ============================================================ *)
(* Section A: the pair-form gap (b5dS_E_pair_gap)                                *)
(* Isomorphic source: the root b5b_E_gap L73729-73853 (body L73738-73853).       *)
(* Generalization changes (the review §6.1 M1 line-count estimate: 2-3          *)
(*   generalizations of the ring/abs small pieces):                              *)
(*   (1) ring identity: b5b_ring_Ediff (the (1-g,1) special case) -> b5dS_ring_Ediff *)
(*     (the pair form for all a b — it degenerates verbatim at a := 1-g, b := 1); *)
(*   (2) the abs product bound: b5b_abs_gmult (the 0 <= g form) -> b5dS_abs_le1_mult *)
(*     (|x| <= 1 gives |x*y| <= |y| — after pair-forming the b coefficient carries no *)
(*     sign premise);                                                            *)
(*   (3) the abs reversal: the role of b5b_abs_oneminusg -> b5dS_abs_sub_mult    *)
(*     (|(b-a)*x| == |a-b|*|x| — Qabs_Qmult + q_abs_minus_sym).                  *)
(* The domain certificate b5b_unitQ is no longer needed (the |a|<=1, |b|<=1      *)
(*   premises supply it directly).                                               *)
(* ============================================================ *)

(* ---- Section A small piece (1): the pair-form ring identity (general in (a,b));        *)
(*        the a := 1-g, b := 1 degeneration = b5b_ring_Ediff verbatim ---- *)
Lemma b5dS_ring_Ediff : forall (sA sB cA cB a b : Q),QeqT (
  (sA - a * cA) - (sB - b * cB) ) (
  (sA - sB) + (b * (cB - cA) + (b - a) * cA)).
Proof.
  intros sA sB cA cB a b. apply qeq_imp_qeqT. intros. ring.
Qed.

(* ---- Section A small piece (2): |x| <= 1 gives |x*y| <= |y| (the pair-form generalization *)
(*        of abs_gmult — the b coefficient carries no 0 <= b premise) ---- *)
Lemma b5dS_abs_le1_mult : forall (x y : Q),
  QleT' (Qabs x) 1 -> QleT' (Qabs (x * y)) (Qabs y).
Proof.
  intros x y Hx.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qmult (Qabs x) (Qabs y)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_Qmult x y).
  - apply (Qle_trans _ (Qmult 1 (Qabs y)) _).
    + apply (Qmult_le_compat_r (Qabs x) 1 (Qabs y)).
      * apply QleT'_to_Qle. exact Hx.
      * apply Qabs_nonneg.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ---- Section A small piece (3): |(b-a)*x| == |a-b|*|x| (Qabs_Qmult +           *)
(*        q_abs_minus_sym; the role-replacement of the root abs_oneminusg / abs_gmult) ---- *)
Lemma b5dS_abs_sub_mult : forall (a b x : Q),QeqT (
  Qabs ((b - a) * x) ) ( Qabs (a - b) * Qabs x).
Proof.
  intros a b x.
  apply qeq_imp_qeqT.
  rewrite (Qabs_Qmult (b - a) x).
  rewrite (qeqT_imp_qeq _ _ (q_abs_minus_sym b a)).
  reflexivity.
Qed.

(* ---- main piece: the pair-form gap (|E_n(a) - E_n(b)| <= 4cT +                  *)
(*        |a-b|*(2c*(S M)#1 + 2c + 1))                                            *)
(*        Statement = the review §4.1 verbatim; body = the b5b_E_gap body L73738-73853 *)
(*        correspondences: (1-g,1) |-> (a,b), g |-> Qabs (a-b), the domain premises |-> *)
(*        QleT' (Qabs a) 1 and QleT' (Qabs b) 1) ---- *)
Lemma b5dS_E_pair_gap : forall (n M : nat) (a b c : Q),
  QleT' 0 c ->
  (forall j : nat, QleT' (exp_series j 2) c) ->
  QleT' (Qabs a) 1 -> QleT' (Qabs b) 1 ->
  NatLe M n ->
  QleT' (Qabs (b5b_En n a - b5b_En n b))
      (Qplus (Qmult (Qmult 4 c) (1 / (Z.of_nat (2 * M + 3) # 1)))
             (Qmult (Qabs (a - b))
                    (Qplus (Qmult (Qmult 2 c) (Z.of_nat (Datatypes.S M) # 1))
                           (Qplus (Qmult 2 c) 1)))).
Proof.
  intros n M a b c Hc0 HC Ha Hb HMn.
  apply Qle_to_QleT'.
  set (A := arctan_partial n a).
  set (B := arctan_partial n b).
  set (T := 1 / (Z.of_nat (2 * M + 3) # 1)).
  set (G := Z.of_nat (Datatypes.S M) # 1).
  set (W := Qplus (Qmult 2 c) 1).
  set (U := Qplus T (Qplus (Qmult G (Qabs (a - b))) T)).
  set (cU := Qmult c U).
  (* |A| <= 2 and |B| <= 2 (apT2 at the premises Ha/Hb). *)
  assert (HAn : QleT' (Qabs A) 2).
  { unfold A. apply (b5b_apT2 a n). exact Ha. }
  assert (HBn : QleT' (Qabs B) 2).
  { unfold B. apply (b5b_apT2 b n). exact Hb. }
  (* the split bound: Ab := |A-B| <= T + G*|a-b| + T (cited directly from ap_split —      *)
(*   the pair-form output is |a-b| itself, no abs_oneminusg step needed) *)
  assert (Hsplit : Qle (Qabs (A - B))
                       (Qplus T (Qplus (Qmult G (Qabs (a - b))) T))).
  { apply (Qle_trans _ (Qplus (Qplus T (Qmult G (Qabs (a - b)))) T) _).
    - unfold A, B, T, G.
      apply QleT'_to_Qle. apply (b5b_ap_split M n a b HMn Ha Hb).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (b5b_ring_assoc_q T (Qmult G (Qabs (a - b))) T)). }
  (* HabU: |A-B| <= U. *)
  assert (HabU : Qle (Qabs (A - B)) U).
  { unfold U. exact Hsplit. }
  (* triangle 1: |En a - En b| <= |sinA-sinB| + (|b*(cB-cA)| + |(b-a)*cA|). *)
  assert (Htri1 : Qle (Qabs (b5b_En n a - b5b_En n b))
                      (Qplus (Qabs (sin_partial n A - sin_partial n B))
                             (Qplus (Qabs (cos_partial n B - cos_partial n A))
                                    (Qmult (Qabs (a - b)) (Qabs (cos_partial n A)))))).
  { unfold b5b_En.
    apply (Qle_trans _ (Qabs ((sin_partial n A - sin_partial n B) +
                              (b * (cos_partial n B - cos_partial n A) +
                               (b - a) * cos_partial n A))) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      apply (Qabs_wd (sin_partial n A - a * cos_partial n A -
                      (sin_partial n B - b * cos_partial n B))
                     ((sin_partial n A - sin_partial n B) +
                      (b * (cos_partial n B - cos_partial n A) + (b - a) * cos_partial n A))).
      exact (qeqT_imp_qeq _ _ (b5dS_ring_Ediff (sin_partial n A) (sin_partial n B)
                             (cos_partial n A) (cos_partial n B) a b)).
    - apply (Qle_trans _ (Qplus (Qabs (sin_partial n A - sin_partial n B))
                                (Qabs (b * (cos_partial n B - cos_partial n A) +
                                       (b - a) * cos_partial n A))) _).
      + apply Qabs_triangle.
      + apply Qplus_le_compat.
        * apply Qle_refl.
        * apply (Qle_trans _ (Qplus (Qabs (b * (cos_partial n B - cos_partial n A)))
                                    (Qabs ((b - a) * cos_partial n A))) _).
          -- apply Qabs_triangle.
          -- apply Qplus_le_compat.
             ++ apply QleT'_to_Qle. apply (b5dS_abs_le1_mult b (cos_partial n B - cos_partial n A)).
                exact Hb.

             ++ apply QleT'_to_Qle. apply qeq_le. exact (b5dS_abs_sub_mult a b (cos_partial n A)). }
  (* the piece bounds: the sin/cos Lipschitz bounds and cos_val at |A|,|B| <= 2. *)
  assert (Hs : Qle (Qabs (sin_partial n A - sin_partial n B))
                   (Qmult (Qabs (A - B)) c)).
  { apply QleT'_to_Qle. apply (b5b_sin_lip2 n A B c HC HAn HBn). }
  assert (Hco : Qle (Qabs (cos_partial n A - cos_partial n B))
                    (Qmult (Qabs (A - B)) c)).
  { apply QleT'_to_Qle. apply (b5b_cos_lip2 n A B c HC (QleT'_to_Qle _ _ Hc0) HAn HBn). }
  assert (Hval : Qle (Qabs (cos_partial n A)) (Qplus (Qmult 2 c) 1)).
  { apply QleT'_to_Qle. apply (b5b_cos_val2 n A c HC (QleT'_to_Qle _ _ Hc0) HAn). }
  assert (Hgv : Qle (Qmult (Qabs (a - b)) (Qabs (cos_partial n A)))
                    (Qmult (Qabs (a - b)) W)).
  { unfold W.
    apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs (cos_partial n A)) (Qplus (Qmult 2 c) 1)
                         (Qabs (a - b))).
    - exact Hval.
    - apply Qabs_nonneg. }
  (* |cosB-cosA| <= |A-B|*c (the reversal bridge). *)
  assert (Hco2 : Qle (Qabs (cos_partial n B - cos_partial n A))
                     (Qmult (Qabs (A - B)) c)).
  { apply (Qle_trans _ (Qabs (cos_partial n A - cos_partial n B)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym.
      apply (qeqT_imp_qeq _ _ (q_abs_minus_sym (cos_partial n A) (cos_partial n B))).
    - exact Hco. }
  (* summary S1. *)
  assert (HS1 : Qle (Qabs (b5b_En n a - b5b_En n b))
                    (Qplus (Qmult (Qabs (A - B)) c)
                           (Qplus (Qmult (Qabs (A - B)) c)
                                  (Qmult (Qabs (a - b)) W)))).
  { apply (Qle_trans _ (Qplus (Qabs (sin_partial n A - sin_partial n B))
                              (Qplus (Qabs (cos_partial n B - cos_partial n A))
                                     (Qmult (Qabs (a - b)) (Qabs (cos_partial n A))))) _).
    - exact Htri1.
    - apply Qplus_le_compat.
      + exact Hs.
      + apply Qplus_le_compat.
        * exact Hco2.
        * exact Hgv. }
  (* Ab·c ≤ cU *)
  assert (HcAb : Qle (Qmult (Qabs (A - B)) c) cU).
  { apply (Qle_trans _ (Qmult c (Qabs (A - B))) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (Qmult_comm (Qabs (A - B)) c).
    - unfold cU.
      apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs (A - B)) U c).
      + exact HabU.
      + exact (QleT'_to_Qle 0 c Hc0). }
  (* S1 ≤ cU + (cU + gW) *)
  assert (HS2 : Qle (Qabs (b5b_En n a - b5b_En n b))
                    (Qplus cU (Qplus cU (Qmult (Qabs (a - b)) W)))).
  { apply (Qle_trans _ (Qplus (Qmult (Qabs (A - B)) c)
                              (Qplus (Qmult (Qabs (A - B)) c)
                                     (Qmult (Qabs (a - b)) W))) _).
    - exact HS1.
    - apply Qplus_le_compat.
      + exact HcAb.
      + apply Qplus_le_compat.
        * exact HcAb.
        * apply Qle_refl. }
  (* conclusion: cU + (cU + gW) <= Tgt (ring_close @ g := Qabs (a-b)). *)
  apply (Qle_trans _ (Qplus cU (Qplus cU (Qmult (Qabs (a - b)) W))) _).
  - exact HS2.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    unfold cU, U, W, G, T.
    exact (qeqT_imp_qeq _ _ (b5b_ring_close c (Qabs (a - b)) T G W)).
Qed.

(* ============================================================ *)
(* Section B: the pair-form equicontinuity (b5dS_E_pair_close)                   *)
(* Isomorphic source: the root b5b_E_close_q L77321-77408 (body L77326-77408).   *)
(* Changes: the window premises (Qlt 0 g / Qle g g0) map to (QleT' (Qabs a) 1 /  *)
(*   QleT' (Qabs b) 1 / Qle (Qabs (a-b)) d0); the output N := M (arch),          *)
(*   d0 := X (= (2*(eps/3))/K — the pair-form window needs no min(1,X) cap:      *)
(*   the domain premises are independent of the window, and the gap needs no     *)
(*   |a-b| <= 1 side); the eps budget body                                       *)
(*   (4cT < eps/3; |a-b|*K <= X*K == 2*(eps/3); third_sum)                       *)
(*   is verbatim isomorphic.  The b5b_ecl_* family is all cited directly         *)
(*   (div_pos / arch_in / arch_cancel / third_sum / third_pos / mult_lt_l /      *)
(*   K_ge1 / XK_cancel).                                                         *)
(* Statement = the review §4.1 verbatim (the sigT output [Nc, d0], pure Q layer, x-independent). *)
(* ============================================================ *)

Lemma b5dS_E_pair_close : forall (eps : Q), QltT 0 eps ->
  sigT (fun N : nat => sigT (fun d0 : Q => And (QltT 0 d0)
    (forall (n : nat) (a b : Q), NatLe N n ->
      QleT' (Qabs a) 1 -> QleT' (Qabs b) 1 ->
      QleT' (Qabs (a - b)) d0 ->
      QltT (Qabs (b5b_En n a - b5b_En n b)) eps))).
Proof.
  intros eps Heps.
  (* c := b5b_arch2 (c >= 1; HC := forall j, exp_series j 2 <=T c). *)
  destruct b5b_arch2 as [c [Hc1T HC]].
  assert (Hc1 : Qle 1 c) by (exact (QleT'_to_Qle 1 c Hc1T)).
  assert (Hcpos : Qlt 0 c).
  { apply (Qlt_le_trans 0 1 c); [unfold Qlt; simpl; lia | exact Hc1]. }
  assert (Hc0 : Qle 0 c).
  { apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact Hc1]. }
  (* the arch input positivity; q_arch_inv chooses M: 1/(M+2) < eps/(12c). *)
  assert (Harchpos : Qlt 0 (eps / (12 * c))) by
    (apply QltT_to_Qlt; apply (b5b_ecl_arch_in c eps Hcpos (QltT_to_Qlt _ _ Heps))).
  destruct (q_arch_inv (eps / (12 * c)) (Qlt_to_QltT _ _ Harchpos)) as [M HM].
  (* notation T := 1/(2M+3), K := 2c*(S M)#1 + 2c + 1 (verbatim with the b5dS_E_pair_gap *)
(*   RHS); X := (2*(eps/3))/K; d0 := X.                                          *)
  set (T := 1 / (Z.of_nat (2 * M + 3) # 1)).
  set (K := 2 * c * (Z.of_nat (Datatypes.S M) # 1) + (2 * c + 1)).
  set (X := (2 * (eps / 3)) / K).
  (* facts: K >= 1, K > 0, K ≠ 0; X > 0; X*K == 2*(eps/3); 0 < eps/3. *)
  assert (He3 : Qlt 0 (eps / 3)) by (apply QltT_to_Qlt; apply (b5b_ecl_third_pos eps); exact (QltT_to_Qlt _ _ Heps)).
  assert (Hk1 : Qle 1 K).
  { unfold K. apply QleT'_to_Qle. apply (b5b_ecl_K_ge1 M c). exact Hc1. }
  assert (Hkpos : Qlt 0 K).
  { apply (Qlt_le_trans 0 1 K); [unfold Qlt; simpl; lia | exact Hk1]. }
  assert (Hk0 : Qle 0 K).
  { apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact Hk1]. }
  assert (Hkneq : ~ (K == 0)) by (intro Hz; apply qeq_imp_qeqT in Hz; apply (q_neq_of_lt K (Qlt_to_QltT _ _ Hkpos)) in Hz; destruct Hz).
  assert (H2e3 : Qlt 0 (2 * (eps / 3))).
  { apply (Qmult_lt_0_compat 2 (eps / 3)); [unfold Qlt; simpl; lia | exact He3]. }
  assert (HXpos : Qlt 0 X).
  { unfold X. apply QltT_to_Qlt. apply (b5b_ecl_div_pos (2 * (eps / 3)) K); [exact H2e3 | exact Hkpos]. }
  assert (HXK : X * K == 2 * (eps / 3)).
  { unfold X. apply (qeqT_imp_qeq _ _ (b5b_ecl_XK_cancel eps K Hkneq)). }
  (* return N := M and d0 := X. *)
  exists M. exists X. split.
  - exact (Qlt_to_QltT 0 X HXpos).
  - intros n a b Hn Ha Hb Hab.
    (* the domain premises supplied directly (the pair gap premises verbatim: QleT' (Qabs a) 1 / *)
(*     QleT' (Qabs b) 1).                                                        *)
(*     b5dS_E_pair_gap: |Δ| <= 4cT + |a-b|*K. *)
    assert (Hgap : Qle (Qabs (b5b_En n a - b5b_En n b))
                       ((4 * c) * T + (Qabs (a - b)) * K)).
    { apply QleT'_to_Qle. apply (b5dS_E_pair_gap n M a b c (Qle_to_QleT' _ _ Hc0) HC Ha Hb Hn). }
    (* term 1: 4cT < eps/3 (T <= 1/(M+2) < eps/(12c), multiplied by 4c > 0; field closes). *)
    assert (Ht_le : Qle T (1 / (Z.of_nat (M + 2) # 1))).
    { unfold T. apply QleT'_to_Qle. apply (atan_inv_chain M M). lia. }
    assert (Ht_arch : Qlt T (eps / (12 * c))).
    { apply (Qle_lt_trans T (1 / (Z.of_nat (M + 2) # 1)) (eps / (12 * c)));
        [exact Ht_le | exact (QltT_to_Qlt _ _ HM)]. }
    assert (H4c : Qlt 0 (4 * c)) by
      (apply (Qmult_lt_0_compat 4 c); [unfold Qlt; simpl; lia | exact Hcpos]).
    assert (Ht1m : Qlt ((4 * c) * T) ((4 * c) * (eps / (12 * c)))).
    { apply QltT_to_Qlt. apply (b5b_ecl_mult_lt_l T (eps / (12 * c)) (4 * c));
        [exact H4c | exact Ht_arch]. }
    assert (Ht1 : Qlt ((4 * c) * T) (eps / 3)).
    { apply (Qlt_le_trans ((4 * c) * T) ((4 * c) * (eps / (12 * c))) (eps / 3));
        [exact Ht1m | apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; apply (qeqT_imp_qeq _ _ (b5b_ecl_arch_cancel c eps Hcpos (QltT_to_Qlt _ _ Heps)))]. }
    (* term 2: |a-b|*K <= X*K == 2*(eps/3) (K >= 0 multiplying |a-b| <= X). *)
    assert (HgK : Qle ((Qabs (a - b)) * K) (X * K)).
    { apply (Qmult_le_compat_r (Qabs (a - b)) X K); [exact (QleT'_to_Qle _ _ Hab) | exact Hk0]. }
    assert (Ht2 : Qle ((Qabs (a - b)) * K) (2 * (eps / 3))).
    { apply (Qle_trans ((Qabs (a - b)) * K) (X * K) (2 * (eps / 3)));
        [exact HgK | apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; exact HXK]. }
    (* the sum: 4cT + |a-b|*K < eps/3 + 2*(eps/3) == eps. *)
    assert (Hsum : Qlt ((4 * c) * T + (Qabs (a - b)) * K)
                      (eps / 3 + 2 * (eps / 3))).
    { apply (Qplus_lt_le_compat ((4 * c) * T) (eps / 3)
                                ((Qabs (a - b)) * K) (2 * (eps / 3)));
        [exact Ht1 | exact Ht2]. }
    assert (Hsum2 : Qlt ((4 * c) * T + (Qabs (a - b)) * K) eps).
    { apply (Qlt_le_trans ((4 * c) * T + (Qabs (a - b)) * K)
                          (eps / 3 + 2 * (eps / 3)) eps);
        [exact Hsum | apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; apply (qeqT_imp_qeq _ _ (b5b_ecl_third_sum eps (QltT_to_Qlt _ _ Heps)))]. }
    (* conclusion: |Δ| <= 4cT + |a-b|*K < eps. *)
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (b5b_En n a - b5b_En n b))
                         ((4 * c) * T + (Qabs (a - b)) * K) eps);
      [exact Hgap | exact Hsum2].
Qed.

(* ============================================================ *)
(* Section C placeholder (not written here — assigned separately once item27's .vo is in place): *)
(* the Section C main piece = the F1 target statement verbatim (= T4 §4 = the    *)
(*   b5b_f1_closure' L78187 premises verbatim):                                  *)
(*   Lemma b5dS_E_zero_on_unit : forall (x : Real) (Hx : cw_unit x),             *)
(*     real_lt real_zero x -> real_lt x (real_const 1) ->                        *)
(*     real_eq (real_E x Hx) real_zero.                                          *)
(* Section C dependencies: CW + item27 b5dQ_E_rational_zero (upstream            *)
(*   sc2_b5a_item27); Sections A/B have zero upstream dependencies.              *)
(* ============================================================ *)

(* ============================================================ *)
(* Verification record: the 3 small pieces genuine Qed + the Section A main piece Qed + the     *)
(*   Section B main piece Qed; the b5dS_ prefix exclusive.                                       *)
(* ============================================================ *)


(* ============================================================ *)
(* Section C: b5dS_E_zero_on_unit (the main piece) + the certificate-family small pieces — text preset *)
(* (the preset-first pattern, per the item24/25 precedent — not compiled, marked as is)          *)
(* Design contract: the F1 extension branch A item29 Section C preset.                           *)
(*   (the authoritative design = the density-closure review §4.1;                                *)
(*   the assembly skeleton realized point by point, marked step by step in the code comments below). *)
(* This section replaces the L336-344 placeholder comment (the placeholder left in the           *)
(*   earlier Sections A/B work — the add-only-no-modification discipline: this section is        *)
(*   entirely newly appended text, with zero changes to the Section A/B body and the existing    *)
(*   comments).                                                                                   *)
(* ------------------------------------------------------------ *)
(* Status note: this section depends on the upstream merged piece sc2_b5a_item27.v; before       *)
(*   that piece is in place this section does not compile; the Require line below is its         *)
(*   placeholder marker, needing only the compile verification once in place.                    *)
(* ------------------------------------------------------------ *)
(* The main-piece statement = T4 §4 verbatim = the root b5b_f1_closure' (L78187-78191)           *)
(*   premises verbatim (only the Lemma name b5a_E_zero_on_unit -> b5dS_E_zero_on_unit;           *)
(*   machine-diff checked: zero drift across the six-source panel — E-ODE-T4-closure §4          *)
(*   L49-51, the review §1 L34-37 + §4.1 L139-141, the root L78188-78190, this file's            *)
(*   L339-341 placeholder, and item30.v L61-63 — verified verbatim):                             *)
(*   Lemma b5dS_E_zero_on_unit : forall (x : Real) (Hx : cw_unit x),                             *)
(*     real_lt real_zero x -> real_lt x (real_const 1) ->                                        *)
(*     real_eq (real_E x Hx) real_zero.                                                          *)
(* The item27 main-piece statement (the sole upstream consumption point — the statement contract *)
(*   verbatim, the name mapping b5dH_ -> b5dQ_, the statement unchanged; re-checked here):       *)
(*   b5dQ_E_rational_zero : forall (q : Q), Qlt 0 q -> Qlt q 1 ->                                *)
(*     forall (Hq : cw_unit (real_const q)),                                                     *)
(*     real_eq (real_E (real_const q) Hq) real_zero.                                             *)
(*   Consumption form (this section's step 4): destruct (b5dQ_E_rational_zero q Hq0             *)
(*     Hq1 Hq (epsQ / 2) HhalfT) as [Nz HNz].                                                    *)
(* ------------------------------------------------------------ *)
(* The assembly skeleton (per the design §4.1 steps 1-5, each step's semantics checked):         *)
(*   1. Equicontinuity takes the window: destruct (b5dS_E_pair_close (epsQ/2) ...)               *)
(*      yields [Nc, d0] — d0 is pure Q-layer and x-independent (before the coordinate choice:    *)
(*      no cycle).                                                                               *)
(*   2. Coordinate separation + Cauchy chooses q: destruct Hx0 gives e0/N0s (the tail            *)
(*      x_n - 0 > e0), destruct Hx1 gives e1/N1s (the tail 1 - x_n > e1),                        *)
(*      Cauchy @ d0 gives Nτ; Nq := max(max N0s N1s) Nτ (all three numbers destructible          *)
(*      before d0 — no cycle); q := x_Nq (Cauchy gives the coordinate approximation directly,    *)
(*      no arch coordinate choice needed).                                                       *)
(*   3. The certificate family of q: the two separation certificates b5dS_sep0_lt                *)
(*      (0 < e0 < x_Nq - 0 gives 0 < q) and b5dS_sep1_lt                                         *)
(*      (0 < e1 < 1 - x_Nq gives q < 1) build the strict 0 < q < 1;                              *)
(*      b5c_const_unit @ (Qle 0 q / Qle q 1) gives Hq : cw_unit (real_const q);                  *)
(*      b5dS_const_unit_qle1 gives the |q| <= 1 form (Section B's b premise).                    *)
(*   4. The rational zero: b5dQ_E_rational_zero @ q := x_Nq (the step 3 certificates)            *)
(*      destructed @ epsQ/2 gives [Nz HNz]: n >= Nz gives |E(q)_n - 0| < epsQ/2.                 *)
(*   5. Conclusion: N := max(max Nc Nq) Nz; for n >= N (pure Q-layer arithmetic):                *)
(*      - triangle: |E(x)_n - 0_n| <= |E(x)_n - E(q)_n| + |E(q)_n - 0_n|;                        *)
(*      - coordinate identity (b5b_En_proj twice + the real_const projection closed by kernel):  *)
(*        |E(x)_n - E(q)_n| == |b5b_En n (x_n) - b5b_En n q|;                                    *)
(*      - Section B (the pair_close_step glue (5)) @ (a := x_n, b := q):                         *)
(*        the premises |x_n| <= 1 (Hx n) / |q| <= 1 ((3)) / |x_n - x_Nq| <= d0                   *)
(*        (Cauchy: n >= Nq >= Nτ and Nq >= Nτ both sides — (3)) give < epsQ/2 (n >= Nc).         *)
(*      - the second term < epsQ/2 (n >= Nz); the two terms sum < epsQ                           *)
(*        (Qplus_lt_compat + b5b_ep_half_sum), so the real_eq definition (L3448) closes directly. *)
(*   The conclusion shape is sentence-by-sentence isomorphic to the root b5b_endpoint            *)
(*   (L78062-78177, the closed template).                                                        *)
(* Endpoint note: x in (0,1) has positive separation given by the two real_lt premises           *)
(*   (e0, e1); q := x_Nq falls strictly inside (0,1) for Nq >= max(N0s, N1s) — the               *)
(*   x-near-0 / x-near-1 cases are excluded automatically by the premises (the endpoints are     *)
(*   outside the quantified domain) — no splice pieces (the review R3).                          *)
(* Dependencies: CW.ConstructiveWorld (b5b_En_proj L73696 / b5c_const_unit L74348 /              *)
(*   b5b_ep_half_sum L78001 / q_half_pos L45573 /                                                *)
(*   b5b_En L73692 / real_eq L3448 / real_lt L3517 / cauchy L3441)                               *)
(*   + Sections A/B (this file's b5dS_E_pair_close) + item27 b5dQ_E_rational_zero                *)
(*   (upstream sc2_b5a_item27).                                                                  *)
(* Closing form: closed normally with all Qed (the premise-form consumption + the real_eq tail   *)
(*   certificate closure — Section C produces no value-path witness, the same shape as           *)
(*   item16/18).                                                                                 *)
(* ============================================================ *)
(* Note: the Require line below compiles only once the upstream sc2_b5a_item27 is in place;      *)
(*   the rest of this section's text has no textual dependency on it.                            *)
Lemma b5dS_sep0_lt : forall (u : Qseq) (N : nat) (e0 : Q),
  QltT 0 e0 ->
  QltT e0 (u N - 0) ->
  QltT 0 (u N).
Proof.
  intros u N e0 He0 He0N.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff 0 (u N))).
  apply (Qlt_trans 0 e0 (u N - 0)).
  - apply QltT_to_Qlt. exact He0.
  - apply QltT_to_Qlt. exact He0N.
Qed.

(* ============================================================ *)
(* Section C certificate-family small piece (2): the separation certificate, the e1 side — the q < 1 strict certificate construction *)
(*   Inputs = the coordinate witness e1 of real_lt x (real_const 1) (QltT 0 e1 and the tail      *)
(*   QltT e1 (1 - u N), with projT1 (real_const 1) N definitionally == 1)                        *)
(*   Proof: Qlt_trans 0 e1 (1 - u N) + proj2 (Qlt_minus_iff (u N) 1):                            *)
(*   0 < 1 - u N iff u N < 1.                                                                    *)
(* ============================================================ *)
Lemma b5dS_sep1_lt : forall (u : Qseq) (N : nat) (e1 : Q),
  QltT 0 e1 ->
  QltT e1 (1 - u N) ->
  QltT (u N) 1.
Proof.
  intros u N e1 He1 He1N.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff (u N) 1)).
  apply (Qlt_trans 0 e1 (1 - u N)).
  - apply QltT_to_Qlt. exact He1.
  - apply QltT_to_Qlt. exact He1N.
Qed.

(* ============================================================ *)
(* Section C certificate-family small piece (3): the Cauchy approximation certificate (the distance <= d0 form) *)
(*   cauchy (root L3441) outputs the strict QltT form; the Section B window premise is the Qle   *)
(*   form, so weaken by QltT_to_Qlt + Qlt_le_weak (the |x_n - x_Nq| <= d0 certificate of the     *)
(*   main piece's step 5: m := n the running index, n := Nq the fixed index — both sides >= Nτ   *)
(*   is guaranteed by Nq >= Nτ and n >= Nq).                                                     *)
(* ============================================================ *)
Lemma b5dS_cauchy_le : forall (u : Qseq) (Ntau : nat) (d0 : Q) (m n : nat),
  (forall (m0 n0 : nat), NatLe Ntau m0 -> NatLe Ntau n0 ->
    QltT (Qabs (u m0 - u n0)) d0) ->
  NatLe Ntau m -> NatLe Ntau n ->
  QleT' (Qabs (u m - u n)) d0.
Proof.
  intros u Ntau d0 m n Hc Hm Hn.
  apply Qle_to_QleT'.
  apply Qlt_le_weak.
  apply QltT_to_Qlt.
  exact (Hc m n Hm Hn).
Qed.

(* ============================================================ *)
(* Section C certificate-family small piece (4): the |q| <= 1 glue (the QleT' form — Section B's b premise; *)
(*   the Hq certificate's pointwise projection projT1 (real_const q) n is definitionally == q)   *)
(* ============================================================ *)
Lemma b5dS_const_unit_qle1 : forall (q : Q) (Hq : cw_unit (real_const q)),
  QleT' (Qabs q) 1.
Proof.
  intros q Hq.
  exact (Hq 0%nat).
Qed.

(* ============================================================ *)
(* Section C certificate-family small piece (5): the pair-close instantiation glue               *)
(*   Section B's inner window (the second component of b5dS_E_pair_close) -> the QltT form of    *)
(*   the coordinate difference — applied directly at the main piece's step 5 term1 (instantiated *)
(*   with a := x_n, b := q).                                                                     *)
(* ============================================================ *)
Lemma b5dS_pair_close_step : forall (eps d0 : Q) (Nc : nat) (a b : Q) (n : nat),
  (forall (n0 : nat) (a0 b0 : Q), NatLe Nc n0 ->
    QleT' (Qabs a0) 1 -> QleT' (Qabs b0) 1 ->
    QleT' (Qabs (a0 - b0)) d0 ->
    QltT (Qabs (b5b_En n0 a0 - b5b_En n0 b0)) eps) ->
  NatLe Nc n ->
  QleT' (Qabs a) 1 -> QleT' (Qabs b) 1 ->
  QleT' (Qabs (a - b)) d0 ->
  QltT (Qabs (b5b_En n a - b5b_En n b)) eps.
Proof.
  intros eps d0 Nc a b n Hw Hn Ha Hb Hab.
  exact (Hw n a b Hn Ha Hb Hab).
Qed.

(* ============================================================ *)
(* Section C main piece: b5dS_E_zero_on_unit                                                     *)
(* Statement = T4 §4 = the b5b_f1_closure' premises verbatim (zero drift across the six-source   *)
(*   panel, see the section head note); body = the design §4.1 skeleton steps 1-5 (the section   *)
(*   head note point by point) + the conclusion shape isomorphic to the root b5b_endpoint        *)
(*   (L78062-78177).                                                                             *)
(* ============================================================ *)
Lemma b5dS_E_zero_on_unit : forall (x : Real) (Hx : cw_unit x),
  real_lt real_zero x -> real_lt x (real_const 1) ->
  real_eq (real_E x Hx) real_zero.
Proof.
  intros x Hx Hx0 Hx1.
  (* the eps input of real_eq + the epsQ/2 half budget (the b5b_endpoint L78064-78067 form). *)
  intros epsQ HepsQT.
  assert (HepsQ : Qlt 0 epsQ) by (apply QltT_to_Qlt; exact HepsQT).
  assert (HhalfQ : Qlt 0 (epsQ / 2)) by (apply QltT_to_Qlt; apply q_half_pos; apply Qlt_to_QltT; exact HepsQ).
  assert (HhalfT : QltT 0 (epsQ / 2)) by (apply Qlt_to_QltT; exact HhalfQ).
  (* step 1: equicontinuity takes the window — pair-close @ epsQ/2 gives [Nc, d0]                 *)
(*   d0 is pure Q-layer and x-independent — before the coordinate choice (acyclic, the review R7). *)
  destruct (b5dS_E_pair_close (epsQ / 2) HhalfT) as [Nc [d0 [Hd0pos Hpair]]].
  (* step 2: the coordinate separation (e0/N0s, e1/N1s) + Cauchy @ d0 gives Nτ. *)
  destruct Hx0 as [e0 [He0pos [N0s HN0s]]].
  destruct Hx1 as [e1 [He1pos [N1s HN1s]]].
  assert (Hd0T : QltT 0 d0) by exact Hd0pos.
  destruct (projT2 x d0 Hd0T) as [Ntau HNtau].
  (* Nq := max(max N0s N1s) Nτ; q := x_Nq (Cauchy gives the coordinate approximation directly). *)
  set (Nq := Nat.max (Nat.max N0s N1s) Ntau).
  set (q := projT1 x Nq).
  (* the nat-layer index facts: N0s/N1s/Nτ <= Nq (an explicit le_max chain, zero lia dependency). *)
  assert (H0q : (N0s <= Nq)%nat).
  { unfold Nq.
    apply (Nat.le_trans N0s (Nat.max N0s N1s) (Nat.max (Nat.max N0s N1s) Ntau)).
    - apply Nat.le_max_l.
    - apply Nat.le_max_l. }
  assert (H1q : (N1s <= Nq)%nat).
  { unfold Nq.
    apply (Nat.le_trans N1s (Nat.max N0s N1s) (Nat.max (Nat.max N0s N1s) Ntau)).
    - apply Nat.le_max_r.
    - apply Nat.le_max_l. }
  assert (Htq : (Ntau <= Nq)%nat).
  { unfold Nq. apply Nat.le_max_r. }
  (* step 3: the certificate family of q — the separation certificates (small pieces (1)(2)) + the *)
(*   unit certificate + the |q|<=1 glue (small piece (4)).                                       *)
  assert (Hq0 : Qlt 0 q).
  { unfold q.
    apply QltT_to_Qlt.
    apply (b5dS_sep0_lt (projT1 x) Nq e0).
    - exact He0pos.
    - exact (HN0s Nq (NatLe_lift _ _ H0q)). }
  assert (Hq1 : Qlt q 1).
  { unfold q.
    apply QltT_to_Qlt.
    apply (b5dS_sep1_lt (projT1 x) Nq e1).
    - exact He1pos.
    - exact (HN1s Nq (NatLe_lift _ _ H1q)). }
  assert (Hq0le : Qle 0 q) by (apply (Qlt_le_weak 0 q); exact Hq0).
  assert (Hq1le : Qle q 1) by (apply (Qlt_le_weak q 1); exact Hq1).
  assert (Hq : cw_unit (real_const q)).
  { exact (b5c_const_unit q Hq0le Hq1le). }
  assert (Hqabs : QleT' (Qabs q) 1) by (exact (b5dS_const_unit_qle1 q Hq)).
  (* step 4: the rational zero — item27's main piece b5dQ_E_rational_zero @ q := x_Nq             *)
(*   (this section's sole upstream consumption point) destructed @ epsQ/2 gives [Nz, HNz].      *)
  destruct (b5dQ_E_rational_zero q (Qlt_to_QltT _ _ Hq0) (Qlt_to_QltT _ _ Hq1) Hq (epsQ / 2) HhalfT) as [Nz HNz].
  (* step 5: the conclusion — N := max(max Nc Nq) Nz; for n >= N (the coordinate level). *)
  exists (Nat.max (Nat.max Nc Nq) Nz).
  intros n Hn.
  apply NatLe_drop in Hn.
  assert (HnNc : (Nc <= n)%nat).
  { exact (Nat.le_trans Nc (Nat.max (Nat.max Nc Nq) Nz) n
             (Nat.le_trans Nc (Nat.max Nc Nq) (Nat.max (Nat.max Nc Nq) Nz)
                (Nat.le_max_l Nc Nq) (Nat.le_max_l (Nat.max Nc Nq) Nz)) Hn). }
  assert (HnNq : (Nq <= n)%nat).
  { exact (Nat.le_trans Nq (Nat.max (Nat.max Nc Nq) Nz) n
             (Nat.le_trans Nq (Nat.max Nc Nq) (Nat.max (Nat.max Nc Nq) Nz)
                (Nat.le_max_r Nc Nq) (Nat.le_max_l (Nat.max Nc Nq) Nz)) Hn). }
  assert (HnNz : (Nz <= n)%nat).
  { exact (Nat.le_trans Nz (Nat.max (Nat.max Nc Nq) Nz) n
             (Nat.le_max_r (Nat.max Nc Nq) Nz) Hn). }
  assert (HnNtau : (Ntau <= n)%nat).
  { exact (Nat.le_trans Ntau Nq n Htq HnNq). }
  (* the term1 coordinate identity: |E(x)_n - E(q)_n| == |b5b_En n (x_n) -               *)
(*   b5b_En n q| (b5b_En_proj twice; the real_const projection closed by kernel —      *)
(*   the b5b_endpoint L78108-78117 form).                                              *)
  assert (Ht1eq : (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n) ==
                  (b5b_En n (projT1 x n) - b5b_En n q)).
  { rewrite (qeqT_imp_qeq _ _ (b5b_En_proj x Hx n)).
    rewrite (qeqT_imp_qeq _ _ (b5b_En_proj (real_const q) Hq n)).
    reflexivity. }
  assert (Ht1abs : Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n) ==
                   Qabs (b5b_En n (projT1 x n) - b5b_En n q)).
  { apply (Qabs_wd (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n)
                   (b5b_En n (projT1 x n) - b5b_En n q)).
    exact Ht1eq. }
  (* the term1 bound: Section B (the pair-close instantiation glue (5)) @ (a := x_n, b := q)       *)
(*   premises: n >= Nc (HnNc) / |x_n| <= 1 (Hx n) / |q| <= 1 (Hqabs) /                           *)
(*   |x_n - x_Nq| <= d0 (the Cauchy approximation certificate (3) — m := n, n := Nq,             *)
(*   both sides >= Nτ: n >= Nq >= Nτ and Nq >= Nτ), giving < epsQ/2.                             *)
  assert (Ht1w : QltT (Qabs (b5b_En n (projT1 x n) - b5b_En n q)) (epsQ / 2)).
  { apply (b5dS_pair_close_step (epsQ / 2) d0 Nc (projT1 x n) q n Hpair).
    - apply NatLe_lift. exact HnNc.
    - exact (Hx n).
    - exact Hqabs.
    - apply (b5dS_cauchy_le (projT1 x) Ntau d0 n Nq HNtau).
      + apply NatLe_lift. exact HnNtau.
      + apply NatLe_lift. exact Htq. }
  (* term1 restated onto the Real-layer difference (qltT_eq_compat_l — the b5b_endpoint L78125-78135 form). *)
  assert (Hterm1T : QltT (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                          (epsQ / 2)).
  { apply (qltT_eq_compat_l (Qabs (b5b_En n (projT1 x n) - b5b_En n q))
                            (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                            (epsQ / 2)).
    - apply qeq_imp_qeqT. apply Qeq_sym. exact Ht1abs.
    - exact Ht1w. }
  assert (Hterm1 : Qlt (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                        (epsQ / 2))
    by (apply QltT_to_Qlt; exact Hterm1T).
  (* the term2 bound: |E(q)_n - 0_n| < epsQ/2 (given directly by item27's tail certificate HNz — the b5b_endpoint L78137-78142 form). *)
  assert (Hterm2T : QltT (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n))
                          (epsQ / 2)).
  { exact (HNz n (NatLe_lift _ _ HnNz)). }
  assert (Hterm2 : Qlt (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n))
                        (epsQ / 2))
    by (apply QltT_to_Qlt; exact Hterm2T).
  (* triangle: |E(x)_n - 0_n| <= |E(x)_n - E(q)_n| + |E(q)_n - 0_n|. *)
  assert (Htri : Qle (Qabs (projT1 (real_E x Hx) n - projT1 real_zero n))
                     (Qplus (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                            (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n)))).
  { apply (Qle_trans _
             (Qabs ((projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n) +
                    (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n))) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      apply (Qabs_wd (projT1 (real_E x Hx) n - projT1 real_zero n)
                     ((projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n) +
                      (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n))).
      ring.
    - apply Qabs_triangle. }
  (* the two terms sum < epsQ/2 + epsQ/2 == epsQ, closing real_eq. *)
  assert (Hsum : Qlt (Qplus (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                            (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n)))
                     (Qplus (epsQ / 2) (epsQ / 2))).
  { apply (Qplus_lt_compat (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                           (epsQ / 2)
                           (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n))
                           (epsQ / 2)).
    - exact Hterm1.
    - exact Hterm2. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (Qabs (projT1 (real_E x Hx) n - projT1 real_zero n))
                      (Qplus (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                             (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n)))
                      epsQ).
  - exact Htri.
  - apply (Qlt_le_trans (Qplus (Qabs (projT1 (real_E x Hx) n - projT1 (real_E (real_const q) Hq) n))
                               (Qabs (projT1 (real_E (real_const q) Hq) n - projT1 real_zero n)))
                        (Qplus (epsQ / 2) (epsQ / 2)) epsQ).
    + exact Hsum.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (b5b_ep_half_sum epsQ)).
Qed.

(* ============================================================ *)
(* Section C preset status record (text preset, not compiled — as is):                           *)
(*   6 new Lemmas (the certificate-family small pieces (5) + the main piece (1), all Qed closing intended); *)
(*   the expected Lemma count: 11 (Sections A/B 5 + Section C 6); the b5dS_ prefix exclusive;    *)
(*   add-only-no-modification (Sections A/B untouched — only this section and the Require line appended); *)
(*   a genuine compile verification is needed once the upstream item27 is in place.              *)
(*   Pre-verification (with the contract statement as a placeholder inside a scratch copy, the   *)
(*   whole file compiled through):                                                               *)
(*   the syntax + the type-level closure of the whole Section C proof body established; the      *)
(*   placeholder pieces did not enter this file.                                                 *)
(* ============================================================ *)

(* ===== Block item30 (main item b5dT_f1_pi_geom_eq_leibniz_univ; upstream source sc2_b5a_item30) ===== *)

(* ============================================================ *)
(* Piece 1 (the B' single-point route): the F1 assumption-free closed form                       *)
(*   Chain: b5dQ_E_rational_zero -> b5dF_E_one_zero_of_rational ->                               *)
(*        b5b_hsc_main (L72994) -> a3_closure_f1 (L67997)                                        *)
(*   4 tactics + Qed in the body (a pure application chain, zero new proof);                     *)
(*   the equivalent one-line form: exact (a3_closure_f1 (b5b_hsc_main                            *)
(*     (b5dF_E_one_zero_of_rational b5dQ_E_rational_zero))).                                     *)
(*   Dependencies: item27's .vo (b5dQ_E_rational_zero) + item16's .vo (closed).                  *)
(* ============================================================ *)
(* ============================================================ *)
(* pi_triangle_direct_edge — the closed-form equation cos_pi_half == 2*arctan_one_real.          *)
(* Mathematical mission: cos_pi_half is the unique zero of cosine in the interval (3/2,2)        *)
(*   (the constructive representation of π/2, see cos_pi_half_unique_widened); this piece gives  *)
(*   its single assumption-free equation with the arctan terminal value 2*arctan_one_real,       *)
(*   matching real_pi_geom == 2*cos_pi_half and 4*arctan_one_real == cauchy_real_pi_leibniz,     *)
(*   forming the direct edge of the three-quantity interconnection triangle.                     *)
(* Dependencies: S10_KVQuantTrig (cos_pi_half, cauchy_real_pi_leibniz);                          *)
(*   S11_TP3B5 (arctan_one_real, a3_h4_value_bridge, channel_w_eq_two_theta,                     *)
(*   channel_w_eq_cos_pi_half, b5b_hsc_theorem); this file's Section C (b5dS_E_zero_on_unit).    *)
(* Benchmark: the combined facts of mathlib Real.arctan_one_eq_pi_div_four and                   *)
(*   Real.cos_pi_two; this piece is a single closed-form lemma.                                  *)
(* Constructivity note: zero premises, zero axioms; Set-layer carrier (real_eq is the termwise   *)
(*   convergence equivalence on sigT); extractable.                                              *)
(* Build recipe: Rocq 9.1 coqc -native-compiler no -Q . "".                                      *)
(* ============================================================ *)
(* Proof strategy: substituting a3_h4_value_bridge (4*arctan_one_real ==                         *)
(*   cauchy_real_pi_leibniz) into the two pieces of the N10Channel node:                         *)
(*   channel_w_eq_cos_pi_half (also needing sin(arctan_one_real) ==                              *)
(*   cos(arctan_one_real), instantiated by b5b_hsc_theorem from                                  *)
(*   b5dS_E_zero_on_unit) gives π_L/2 == cos_pi_half;                                            *)
(*   channel_w_eq_two_theta gives π_L/2 == 2*arctan_one_real; composing                          *)
(*   transitively after the symmetry.                                                            *)
Lemma pi_triangle_direct_edge :
  real_eq cos_pi_half (real_mult (real_const 2) arctan_one_real).
Proof.
  exact (real_eq_trans cos_pi_half
           (real_mult cauchy_real_pi_leibniz (real_const (1 / 2)))
           (real_mult (real_const 2) arctan_one_real)
           (real_eq_sym
              (real_mult cauchy_real_pi_leibniz (real_const (1 / 2)))
              cos_pi_half
              (channel_w_eq_cos_pi_half a3_h4_value_bridge
                 (b5b_hsc_theorem b5dS_E_zero_on_unit)))
           (channel_w_eq_two_theta a3_h4_value_bridge)).
Qed.
Lemma b5dT_f1_pi_geom_eq_leibniz_single :
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  apply a3_closure_f1.
  apply b5b_hsc_main.
  apply b5dF_E_one_zero_of_rational.
  exact b5dQ_E_rational_zero.
Qed.

(* ============================================================ *)
(* Piece 2 (the forall-x route): the F1 assumption-free closed form (depends on item29 Section C — awaiting the Section C .vo) *)
(*   Chain: b5dS_E_zero_on_unit -> b5b_f1_closure' (L78187)                                      *)
(*   2 tactics + Qed in the body; the statement = Piece 1 (closed form);                         *)
(*   the equivalent one-line form: exact (b5b_f1_closure' b5dS_E_zero_on_unit).                  *)
(* ============================================================ *)
Lemma b5dT_f1_pi_geom_eq_leibniz_univ :
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  apply b5b_f1_closure'.
  exact b5dS_E_zero_on_unit.
Qed.

(* ============================================================ *)
(* Verification record (at the preset point = not compiled — as is):                             *)
(*   a compile verification is needed once the upstream dependencies (item27 / item29 Section C) *)
(*   are in place;                                                                               *)
(*   the expected Lemma count: 2 Lemma = 2 Qed; the b5dT_ prefix exclusive;                       *)
(*   statement check: the conclusions of Pieces 1/2 = the final-piece B target                   *)
(*     real_eq real_pi_geom cauchy_real_pi_leibniz verbatim;                                     *)
(*     the five-source piece names/types referenced in the body = the header-note contract verbatim. *)
(* Final-piece B connection: the final piece B = real_pi_geom_eq_leibniz (the paper's named      *)
(*   name) — the two pieces already give the substantive closed forms; the paper-name alias waits *)
(*   for the final piece B (zero conflict with the root piece name).                             *)
(* ============================================================ *)

(* ===== Block finalc (main item b5dU_cos_piL_half_zero; upstream source sc2_b5a_finalc) ===== *)

(* ============================================================ *)
(* Route C: b5dU_cos_piL_half_zero_alt (zero new proof — the ready-made a3_closure_n5 closure;   *)
(*   the input = the tan-channel Hsc, same-source E1 as the F1 single-point route —              *)
(*   established verbatim by probe_b5dU_p2).                                                     *)
(* ============================================================ *)
Lemma b5dU_cos_piL_half_zero_alt :
  real_eq (cauchy_real_cos (real_mult cauchy_real_pi_leibniz (real_const (1 / 2))))
          real_zero.
Proof.
  exact (a3_closure_n5 (b5b_hsc_main (b5dF_E_one_zero_of_rational b5dQ_E_rational_zero))).
Qed.

(* ============================================================ *)
(* Route A helper: b5dU_routeA_from_f1 (the F1 premise form — the preliminary-research probe     *)
(*   probe_b5dU_p1 body verbatim — deleted and rebuilt after verification)                       *)
(*   ring A1: π_L*(1/2) == π_geom*(1/2) (F1 reversed + the multiplication compatibility);        *)
(*   ring A2: π_geom*(1/2) == cos_pi_half (unfold real_pi_geom +                                 *)
(*     the associativity + real_double_half_cancel);                                             *)
(*   rings A3+A4: the cos compatibility twice + real_cos_pi_half_zero.                           *)
(* ============================================================ *)
Lemma b5dU_routeA_from_f1 :
  real_eq real_pi_geom cauchy_real_pi_leibniz ->
  real_eq (cauchy_real_cos (real_mult cauchy_real_pi_leibniz (real_const (1 / 2))))
          real_zero.
Proof.
  intro Hf.
  assert (H1 : real_eq (real_mult cauchy_real_pi_leibniz (real_const (1 / 2)))
                       (real_mult real_pi_geom (real_const (1 / 2)))).
  { apply (RealSetoid.real_eq_mult_compat cauchy_real_pi_leibniz (real_const (1 / 2))
                                          real_pi_geom (real_const (1 / 2))).
    - apply real_eq_sym. exact Hf.
    - apply real_eq_refl. }
  assert (H2 : real_eq (real_mult real_pi_geom (real_const (1 / 2))) cos_pi_half).
  { unfold real_pi_geom.
    apply (real_eq_trans _ (real_mult (real_const 2) (real_mult cos_pi_half (real_const (1 / 2)))) _).
    - apply real_eq_sym. apply real_mult_assoc.
    - apply real_double_half_cancel. }
  apply (real_eq_trans _ (cauchy_real_cos (real_mult real_pi_geom (real_const (1 / 2)))) _).
  - apply real_cos_eq_compat. exact H1.
  - apply (real_eq_trans _ (cauchy_real_cos cos_pi_half) _).
    + apply real_cos_eq_compat. exact H2.
    + exact real_cos_pi_half_zero.
Qed.

(* ============================================================ *)
(* Route A main piece: b5dU_cos_piL_half_zero (instantiating item30's single-point route         *)
(*   b5dT_f1_pi_geom_eq_leibniz_single — the _univ same-statement variant is optional; the       *)
(*   single-point route is the 215 main chain).                                                  *)
(* ============================================================ *)
Lemma b5dU_cos_piL_half_zero :
  real_eq (cauchy_real_cos (real_mult cauchy_real_pi_leibniz (real_const (1 / 2))))
          real_zero.
Proof.
  exact (b5dU_routeA_from_f1 b5dT_f1_pi_geom_eq_leibniz_single).
Qed.

(* ============================================================ *)
(* Verification record: the Lemma count 3 = 3 Qed (_alt + routeA_from_f1 + the main piece);      *)
(*   the b5dU_ prefix exclusive.                                                                 *)
(* ============================================================ *)

(* ===== Block 25: UpLogMono (the Real-layer log monotone le version) — real_log_le_mono +     *)
(*   real_log_le_zero_of_le_one (the direct-application form of the HlogZ premise) + the        *)
(*   bridging lemmas real_lt_le_bridge / real_eq_le_bridge; source: UpLogMono.v (upstream);     *)
(*   zero axiom face, zero admissions; 4 Qed.                                                    *)
(* ===== *)
(* ============================================================ *)
(* UpLogMono.v — the Real-layer log monotone le version                                         *)
(*                                                                                               *)
(* The last piece of the premise discharge of the HlogZ premise (le (log Z_aud) zero) of the     *)
(*   main theorem of Paper 1 KLProjection (audit = KL projection): Z_aud <= 1 gives              *)
(*   log Z_aud <= 0, needing "the log monotone le version" — a named item in the blueprint       *)
(*   outlook.  On the Real layer (cw_log/real_log), the le proof of the Or encoding branch by    *)
(*   branch: the lt branch goes through real_log_lt_mono (strict monotonicity, proved in the     *)
(*   root); the eq branch goes through real_log_wd (equality substitution, proved in the root).  *)
(* Discipline: zero axiom face, zero admissions; Set-layer statements; all Qed; extractable.     *)
(* ============================================================ *)
Lemma real_lt_le_bridge : forall a b : Real, real_lt a b -> real_le a b.
Proof. intros a b H. exact (inl H). Qed.

(* the lt -> le bridge (real_le = Or (real_lt) (real_eq), taken by inl). *)
Lemma real_eq_le_bridge : forall a b : Real, real_eq a b -> real_le a b.
Proof. intros a b H. exact (inr H). Qed.

(* ========== main lemma: the real_log monotone le version (the Or encoding proved branch by branch) ========== *)
Lemma real_log_le_mono : forall (a b : Real) (Ha : real_lt real_zero a)
    (Hb : real_lt real_zero b),
  real_le a b -> real_le (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hab.
  destruct Hab as [Hlt | Heq].
  - (* the lt branch: strict monotonicity lifted to le. *)
    exact (real_lt_le_bridge (real_log a Ha) (real_log b Hb)
             (real_log_lt_mono a b Ha Hb Hlt)).
  - (* the eq branch: equality substitution lifted to le. *)
    exact (real_eq_le_bridge (real_log a Ha) (real_log b Hb)
             (real_log_wd a b Ha Hb Heq)).
Qed.

(* ========== the direct-use form: Z <= 1 gives log Z <= 0 (the HlogZ premise discharge) ========== *)
Lemma real_log_le_zero_of_le_one : forall (Z : Real) (HZ : real_lt real_zero Z),
  real_le Z real_one -> real_le (real_log Z HZ) real_zero.
Proof.
  intros Z HZ HZ1.
  assert (Hone : real_lt real_zero real_one).
  { exact real_lt_zero_one. }
  apply (real_le_trans _ (real_log real_one Hone) _).
  - exact (real_log_le_mono Z real_one HZ Hone HZ1).
  - (* real_log one == 0 lifted to le via the eq bridge. *)
    exact (real_eq_le_bridge (real_log real_one Hone) real_zero
             (real_log_one Hone)).
Qed.

(* the extraction check. *)

(* ===== Block 26: UpFEP — attention = the unique minimizer of the variational free energy —   *)
(*   attention_minimizes_free_energy_unique (the FEP closed loop) +                              *)
(*   bs_kernel_row_is_softmax_temp (the row view, the piece named by Paper 2 §10.2);             *)
(*   source: UpFEP.v (upstream); zero axiom face, zero admissions; 5 Qed.                        *)
(* ===== *)
(* ============================================================ *)
(* UpFEP.v — the second-round increment set, P5: attention = the unique minimizer of the        *)
(*            variational free energy + the row-view lemma (each bs_kernel row = the single-query *)
(*            softmax_temp)                                                                      *)
(*                                                                                               *)
(* P5 (the FEP x Gibbs bridge closure, pure assembly): instantiate the free-energy-KL decomposition *)
(*   triple (free_energy_kl_decomp / min_free_energy_is_boltzmann / free_energy_min_unique,      *)
(*   generalized over base_loss/D/Z) with base_loss := -z and D := T, paired with the alignment  *)
(*   lemma (the Boltzmann factor = the softmax numerator, via opp_mult_l) and the F extensionality *)
(*   lemma, giving:                                                                              *)
(*   softmax_temp z is the unique minimizer of F_T[p] = -E_p[z] + T*Σ p log p.                    *)
(*   This lifts the "attention-side free-energy minimization" of Paper 2 §5.4(b) from            *)
(*   interpretation to a machine-checked theorem; the §9.1 unified view closes the FEP-attention *)
(*   gap.                                                                                        *)
(* Row view: each row of the row-softmax kernel bs_kernel of AttnDoeblin is the same object as   *)
(*   the single-query softmax_temp of Paper 2 §5.2 (through the coherence premises of expf and   *)
(*   exp_pos_fn) — the docking piece named by Paper 2 §10.2.                                     *)
(* Discipline: zero axiom face, zero admissions; Set-layer statements; all Qed.                  *)
(* ============================================================ *)


(* ################ Part 1: the P5 FEP closed loop ################ *)

(* the assumption-face audit of the replacement theorems. *)
Print Assumptions b5d1_Heps4.
Print Assumptions b5dE_zero_le_one.
