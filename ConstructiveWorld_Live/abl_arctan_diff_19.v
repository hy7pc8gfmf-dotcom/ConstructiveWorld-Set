(* ConstructiveWorld-Set — arctan difference-formula continuation piece (open items 1-4). *)
(** * abl_arctan_diff_19: uniform-delta and chain-rule cores for the arctan difference formula.

    Mission.  Continues [abl_arctan_diff_16] along four open items.
      Item 1 closes here: [abl9_atan_incr_step_cond] and
      [abl9_atan_deriv_uniform] build a uniform delta
      ([delta := min((1-r)/2, eps*k)], [k = 1/(4*(Cr+1))] independent of u)
      derived from the proof body of the b3rr main lemma.  Item 2 closes at
      the Q layer: the division-free polynomial core of the chain rule for
      [w(u) := (u-v)/(1+u*v)] ([abl9_wsq_ring_id]/[abl9_wincr_ring_id] and
      the division forms [abl9_wsq_div_id]/[abl9_wincr_div_id] under
      nonzero denominators).  Items 3-4 and the main goal [abl9_atan_diff_formula] stay open.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qround],
      [Lists.List], [Bool.Bool], [Arith.Arith], [Setoid], [Morphisms],
      [Lia], [QArith.Qminmax], [Structures.GenericMinMax], [Extraction];
      requires [S01_BaseRing] through [S11_TP3B5] and
      [abl_arctan_diff_16] of this development.

    References.  This development, abl_arctan_diff_19.v, the baseline module
      in ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All six lemmas close by Qed with zero admitted
      statements, inheriting the Set-layer no-Prop caliber of the
      S-modules; extractable with [Obj.magic] count 0.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      abl_arctan_diff_19.v] compiles cleanly (exit 0); the artifact starts
      with [436f7121 00015ff4]. *)

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
Require Import abl_arctan_diff_16.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import Extraction.

(* =================== Open item 1, piece a: the conditional step-bound lemma =================== *)
(* Hypotheses: the two bounds on k (0 < k is dropped as unused here; *)
(* Cr*k <= 1/4 is kept) plus the two pointwise delta consequences *)
(* (the Real-layer forms of |h| < (1-r)/2 and |h| < eps*k); *)
(* the conclusion is the interior derivative step bound (literally the *)
(* X16 piece-1 conclusion, with the variable u). *)
(* The proof transcribes the pointwise chain of the b3rr main lemma *)
(* (the two min-unpacking steps on the delta route become hypotheses). *)
Lemma abl9_atan_incr_step_cond :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (eps : Real) (k : Q), real_lt real_zero eps ->
  Qle (b3rr_C2 ((1 # 2) * (1 + r)) * k) (1 # 4) ->
  forall (delta : Real),
  (forall (h0 : Real), real_lt (real_abs h0) delta ->
     real_lt (real_abs h0) (real_const ((1 # 2) * (1 - r)))) ->
  (forall (h0 : Real), real_lt (real_abs h0) delta ->
     real_lt (real_abs h0) (real_mult eps (real_const k))) ->
  forall (u : Real) (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) r),
  forall (h : Real), real_lt (real_abs h) delta ->
  forall (Huh : forall n : nat, QleT' (Qabs (projT1 (real_plus u h) n)) 1),
  forall (eps' : Real), real_lt real_zero eps' ->
  real_le (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                     (real_opp (real_plus (cauchy_real_arctan u
                                            (b3rr_dom_r1 u r Hu Hr1))
                                (real_mult h (real_inv_pos
                                   (real_plus real_one (real_mult u u))
                                   (b3r_one_sq_real_pos u)))))))
          (real_plus (real_mult eps (real_abs h)) eps').
Proof.
  intros r Hr0 Hr1 eps k Heps HkC delta Hhalf Hkbound u Hu h Hh Huh eps' Heps'.

  set (Cr := b3rr_C2 ((1 # 2) * (1 + r))).
  assert (HCr0 : Qle 0 Cr).
  { unfold Cr. apply QleT'_to_Qle.
    apply (b3rr_C2_0 ((1 # 2) * (1 + r))).
    - apply QleT'_to_Qle. apply (b3rr_M0 r). exact Hr0.
    - apply QltT_to_Qlt. apply (b3rr_M_lt1 r). exact Hr1. }
  assert (HCrK : Qle (Cr * k) (1 # 4)) by exact HkC.
  destruct Heps as [eps1 [Heps1 [N1 HN1]]].
  destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
  (* The two delta conditions taken directly at the Real layer (the two *)
  (* min-unpacking steps of b3rr become hypotheses here). *)
  destruct (Hhalf h Hh) as [e2 [He2 [N2 HN2]]].
  destruct (Hkbound h Hh) as [e3 [He3 [N3 HN3]]].
  destruct (real_inv_proj (real_plus real_one (real_mult u u))
             (b3r_one_sq_real_pos u)) as [Ninv HNinv].
  assert (Hh2 : Qlt 0 (Qmult eps1' (Qinv 2))).
  { apply (Qmult_lt_0_compat eps1' (Qinv 2)).
    - apply QltT_to_Qlt. exact Heps1'.
    - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
  destruct (b3rr_qdecay r (Qmult eps1' (Qinv 2)) Hr0 Hr1 Hh2) as [Ng HNg].
  set (eta := Qmult eps1' (Qinv 2)).
  assert (Heta_pos : QltT 0 eta).
  { unfold eta. apply Qlt_to_QltT. exact Hh2. }
  left.
  exists eta. split.
  + exact Heta_pos.
  + exists (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3))
              (Nat.max Ninv Ng)).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    assert (Hn1' : (N1' <= n)%nat) by lia.
    assert (Hn2 : (N2 <= n)%nat) by lia.
    assert (Hn3 : (N3 <= n)%nat) by lia.
    assert (Hninv : (Ninv <= n)%nat) by lia.
    assert (Hng : (Ng <= n)%nat) by lia.
    set (un := projT1 u n). set (hn := projT1 h n).
    set (en := projT1 eps n). set (en' := projT1 eps' n).
    set (yn := un + hn).
    set (Dform := arctan_partial n yn - arctan_partial n un
                    - hn * Qinv (1 + un * un)).
    set (wreal := real_inv_pos (real_plus real_one (real_mult u u))
                    (b3r_one_sq_real_pos u)).
    (* Positivity: en >= 0 and en' > eps1'. *)
    assert (HN1e : QltT eps1 en).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
      - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        cbn [real_zero real_const projT1]. unfold en. ring. }
    assert (Hen0 : Qle 0 en).
    { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
      - apply QltT_to_Qlt. exact Heps1.
      - apply QltT_to_Qlt. exact HN1e. }
    assert (HN1'e : QltT eps1' en').
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
      - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        cbn [real_zero real_const projT1]. unfold en'. ring. }
    (* From the witnesses to pointwise bounds: |hn| <= (1-r)/2 and |hn| <= en*k. *)
    assert (Hq2 : Qlt e2 (Qminus ((1 # 2) * (1 - r)) (Qabs hn))).
    { apply (Qlt_le_trans e2
               (Qminus (projT1 (real_const ((1 # 2) * (1 - r))) n)
                       (projT1 (real_abs h) n))
               (Qminus ((1 # 2) * (1 - r)) (Qabs hn))).
      - apply QltT_to_Qlt. apply (HN2 n (NatLe_lift _ _ Hn2)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        cbn [real_zero real_const projT1]. reflexivity. }
    assert (Hhn_half : Qlt (Qabs hn) ((1 # 2) * (1 - r))).
    { apply (Qlt_le_trans (Qabs hn) (Qminus ((1 # 2) * (1 - r)) e2)
                          ((1 # 2) * (1 - r))).
      - apply QltT_to_Qlt. apply (q_lt_minus_shift e2 ((1 # 2) * (1 - r)) (Qabs hn)).
        apply Qlt_to_QltT. exact Hq2.
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
    assert (Hhn_half_le : Qle (Qabs hn) ((1 # 2) * (1 - r)))
      by (apply Qlt_le_weak; exact Hhn_half).
    assert (Hhn1 : Qle (Qabs hn) 1).
    { apply (Qle_trans _ ((1 # 2) * (1 - r)) _).
      - exact Hhn_half_le.
      - apply QleT'_to_Qle. apply (b3rr_1mr_half_le1 r). exact Hr0. }
    assert (Hq3 : Qlt e3 (Qminus (Qmult en k) (Qabs hn))).
    { apply (Qlt_le_trans e3
               (Qminus (projT1 (real_mult eps (real_const k)) n)
                       (projT1 (real_abs h) n))
               (Qminus (Qmult en k) (Qabs hn))).
      - apply QltT_to_Qlt. apply (HN3 n (NatLe_lift _ _ Hn3)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_const k) n)).
        unfold en.
        cbn [real_zero real_const projT1]. reflexivity. }
    assert (Hhn_k : Qlt (Qabs hn) (Qmult en k)).
    { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en k) e3) (Qmult en k)).
      - apply QltT_to_Qlt. apply (q_lt_minus_shift e3 (Qmult en k) (Qabs hn)).
        apply Qlt_to_QltT. exact Hq3.
      - assert (He30 : Qle 0 e3) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact He3).
        apply (Qle_trans (Qminus (Qmult en k) e3)
                         (Qplus (Qminus (Qmult en k) e3) e3)
                         (Qmult en k)).
        + apply (Qle_trans (Qminus (Qmult en k) e3)
                           (Qplus (Qminus (Qmult en k) e3) 0)
                           (Qplus (Qminus (Qmult en k) e3) e3)).
          * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          * apply (Qplus_le_compat (Qminus (Qmult en k) e3)
                                   (Qminus (Qmult en k) e3) 0 e3
                                   (Qle_refl _) He30).
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    assert (Hhn_kle : Qle (Qabs hn) (Qmult en k)) by (apply Qlt_le_weak; exact Hhn_k).
    (* Domain: |un| <= r. *)
    assert (Hun_r : Qle (Qabs un) r).
    { apply (QleT'_to_Qle (Qabs un) r). apply Hu. }
    assert (Hhvn0 : Qle 0 (Qabs hn)) by apply Qabs_nonneg.
    assert (Henhn0 : Qle 0 (Qmult en (Qabs hn))).
    { apply (Qmult_le_0_compat en (Qabs hn)). exact Hen0. exact Hhvn0. }
    (* Projection identity (left-hand side). *)
    assert (Hrepl : projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h wreal))))) n ==
                Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un))).
    { unfold yn, un, hn, wreal.
      rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h (real_inv_pos (real_plus real_one (real_mult u u))
                                                       (b3r_one_sq_real_pos u)))))) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_arctan (real_plus u h) Huh)
                (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h (real_inv_pos (real_plus real_one (real_mult u u))
                                                       (b3r_one_sq_real_pos u))))) n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h (real_inv_pos (real_plus real_one (real_mult u u))
                                                       (b3r_one_sq_real_pos u)))) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h (real_inv_pos (real_plus real_one (real_mult u u))
                                                       (b3r_one_sq_real_pos u))) n)).
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj h (real_inv_pos (real_plus real_one (real_mult u u))
                                                       (b3r_one_sq_real_pos u)) n)).
      rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_plus u h) Huh n)).
      rewrite (qeqT_imp_qeq _ _ (arctan_real_proj u (b3rr_dom_r1 u r Hu Hr1) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj u h n)).
      rewrite (qeqT_imp_qeq _ _ (HNinv n (NatLe_lift _ _ Hninv))).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_mult u u) n)).
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj u u n)).
      rewrite (qeqT_imp_qeq _ _ (b3r_one_proj n)).
      apply Qabs_wd. ring. }
    (* Right-hand side projection. *)
    assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n
                 == en * Qabs hn + en').
    { unfold en, en', hn.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
      cbn [real_zero real_const projT1]. ring. }
    (* Pointwise bound 1: Cr*|hn|^2 <= en*|hn|*(1/4). *)
    assert (Hcbn : Qle (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
                       (Qmult (Qmult en (Qabs hn)) (1 # 4))).
    { apply (Qle_trans _ (Qmult Cr (Qmult (Qmult en k) (Qabs hn))) _).
      - apply QleT'_to_Qle. apply (b3_qmult_le_l (Qmult (Qabs hn) (Qabs hn))
                             (Qmult (Qmult en k) (Qabs hn)) Cr).
        + exact HCr0.
        + apply (Qmult_le_compat_r (Qabs hn) (Qmult en k) (Qabs hn)).
          * exact Hhn_kle.
          * exact Hhvn0.
      - apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) (Qmult Cr k)) _).
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        + apply QleT'_to_Qle. apply (b3_qmult_le_l (Qmult Cr k) (1 # 4) (Qmult en (Qabs hn))).
          * exact Henhn0.
          * exact HCrK. }
    (* Pointwise bound 2: r^(2*S n) <= eta (n >= Ng gives 2*S n >= Ng). *)
    assert (Hdec2 : Qle (q_pow r (2 * Datatypes.S n)) eta).
    { apply QleT'_to_Qle. apply (HNg ((2 * Datatypes.S n)%nat)).
      apply NatLe_lift. lia. }
    assert (Hpow14 : Qle (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n)))
                         (q_pow r (2 * Datatypes.S n))).
    { apply (Qle_trans _ (Qmult 1 (q_pow r (2 * Datatypes.S n))) _).
      - apply (Qmult_le_compat_r (Qabs hn) 1 (q_pow r (2 * Datatypes.S n))).
        + exact Hhn1.
        + apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact Hr0.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    (* Main pointwise bound: |D_n| <= en*|hn| + eta. *)
    assert (Hm1 : Qle
      (Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)))
      (Qplus (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
             (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))).
    { unfold yn. apply QleT'_to_Qle.
      apply (b3rr_core_r n un hn r Hr0 Hr1 Hun_r Hhn_half_le). }
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
      - apply (proj2 (Qlt_minus_iff eta
          (Qminus (Qplus (Qmult en (Qabs hn)) en')
                  (Qplus (Qmult en (Qabs hn)) eta)))).
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
                              (Qminus (Qplus (Qmult en (Qabs hn)) en')
                                      (Qplus (Qmult en (Qabs hn)) eta)) ==
                        Qminus (Qplus (Qmult en (Qabs hn)) eta) (Qabs Dform)) by ring.
        rewrite Heq2.
        apply (proj1 (Qle_minus_iff (Qabs Dform) (Qplus (Qmult en (Qabs hn)) eta))).
        exact Hmain. }
    (* Projection bridge: (RHS - LHS) == (B - |D|). *)
    assert (Hrepl2 : Qeq
        (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h wreal))))) n))
        (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
    { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                         (Qplus (Qmult en (Qabs hn)) en') HB
                         (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                         (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                                     (real_mult h wreal))))) n)
                         (Qabs Dform) Hrepl). }
    apply Qlt_to_QltT.
    assert (Hqfinal : Qlt eta
        (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h wreal))))) n))).
    { apply (Qlt_le_trans eta
        (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))
        (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                (real_opp (real_plus (cauchy_real_arctan u (b3rr_dom_r1 u r Hu Hr1))
                            (real_mult h wreal))))) n))).
      - exact Hfin.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qeq_sym. exact Hrepl2. }
    exact Hqfinal.
Qed.

(* =================== Open item 1, piece b: the region-relativized uniform-delta instance =================== *)
(* The main result of this file: the existentially quantified delta moves *)
(* outside the forall u — delta := min((1-r)/2, eps*k) is independent of u *)
(* (with k = 1/(4*(Cr+1)) and Cr = b3rr_C2((1+r)/2) depending only on r), *)
(* ready for the equal-step chain of open item 3. *)
Lemma abl9_atan_deriv_uniform :
  forall (rho : Q) (Hrho0 : Qle 0 rho) (Hrho1 : Qlt rho 1),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (u : Real) (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) rho),
          forall (h : Real), real_lt (real_abs h) delta ->
          forall (Huh : forall n : nat,
                    QleT' (Qabs (projT1 (real_plus u h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                     (real_opp (real_plus (cauchy_real_arctan u
                                            (b3rr_dom_r1 u rho Hu Hrho1))
                                (real_mult h (real_inv_pos
                                   (real_plus real_one (real_mult u u))
                                   (b3r_one_sq_real_pos u)))))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros rho Hrho0 Hrho1 eps Heps.
  set (Cr := b3rr_C2 ((1 # 2) * (1 + rho))).
  assert (HCr0 : Qle 0 Cr).
  { unfold Cr. apply QleT'_to_Qle.
    apply (b3rr_C2_0 ((1 # 2) * (1 + rho))).
    - apply QleT'_to_Qle. apply (b3rr_M0 rho). exact Hrho0.
    - apply QltT_to_Qlt. apply (b3rr_M_lt1 rho). exact Hrho1. }
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
  { unfold k. apply QleT'_to_Qle. exact (b3rr_CK Cr HCr0). }
  set (rk := real_const k).
  exists (real_min (real_const ((1 # 2) * (1 - rho))) (real_mult eps rk)). split.
  - apply real_min_pos.
    + apply real_const_pos_f1.
      apply (Qmult_lt_0_compat (1 # 2) (1 - rho)).
      * unfold Qlt. simpl. lia.
      * apply (proj1 (Qlt_minus_iff rho 1)). exact Hrho1.
    + apply real_mult_positive.
      * exact Heps.
      * unfold rk. apply real_const_pos_f1. exact Hk_pos.
  - intros u Hu h Hh Huh eps' Heps'.
    apply (abl9_atan_incr_step_cond rho Hrho0 Hrho1 eps k Heps HCrK
             (real_min (real_const ((1 # 2) * (1 - rho))) (real_mult eps rk))).
    + intros h0 Hh0.
      exact (abl9_min_lt_l (real_const ((1 # 2) * (1 - rho)))
              (real_mult eps rk) (real_abs h0) Hh0).
    + intros h0 Hh0.
      exact (abl9_min_lt_r (real_const ((1 # 2) * (1 - rho)))
              (real_mult eps rk) (real_abs h0) Hh0).
    + exact Hh.
    + exact Heps'.
Qed.

(* =================== Open item 2, two Q-layer pieces =================== *)
(* The division-free polynomial identity core of the chain rule, with *)
(* numerators brought to a common denominator. *)
(* Let w(u) := (u-v)/(1+u*v); then 1+w(u)^2 = (1+u^2)(1+v^2)/(1+uv)^2 and *)
(* w(u+h) - w(u) = h(1+v^2)/((1+(u+h)v)(1+uv)) as Q-layer identities under *)
(* nonzero denominators; their pure polynomial cores are the two lemmas *)
(* below (polynomial normal forms). *)
Lemma abl9_wsq_ring_id : forall u v : Q,
  QeqT ((1 + u * v) * (1 + u * v) + (u - v) * (u - v))
       ((1 + u * u) * (1 + v * v)).
Proof. intros u v. apply qeq_imp_qeqT. ring. Qed.

Lemma abl9_wincr_ring_id : forall u v h : Q,
  QeqT ((u + h - v) * (1 + u * v) - (u - v) * (1 + (u + h) * v))
       (h * (1 + v * v)).
Proof. intros u v h. apply qeq_imp_qeqT. ring. Qed.

(* Open item 2, division forms of the Q core (the common-denominator *)
(* identities under nonzero denominators, closed by field) — the direct *)
(* input shape for the Real-layer certificate bridge *)
(* (aligned with [real_inv_pos_ext]). *)
Lemma abl9_wsq_div_id : forall u v : Q, ~ (1 + u * v == 0) ->
  QeqT (1 + (u - v) * (u - v) / ((1 + u * v) * (1 + u * v)))
       ((1 + u * u) * (1 + v * v) / ((1 + u * v) * (1 + u * v))).
Proof.
  intros u v Hne. apply qeq_imp_qeqT.
  assert (Hne2 : ~ ((1 + u * v) * (1 + u * v) == 0)).
  { intros Hp. destruct (Qmult_integral (1 + u * v) (1 + u * v) Hp) as [Hz | Hz].
    - apply Hne. exact Hz.
    - apply Hne. exact Hz. }
  field; try assumption.
Qed.

Lemma abl9_wincr_div_id : forall u v h : Q,
  ~ (1 + (u + h) * v == 0) -> ~ (1 + u * v == 0) ->
  QeqT ((u + h - v) / (1 + (u + h) * v) - (u - v) / (1 + u * v))
       (h * (1 + v * v) / ((1 + (u + h) * v) * (1 + u * v))).
Proof.
  intros u v h H1 H2. apply qeq_imp_qeqT.
  assert (Hne2 : ~ ((1 + (u + h) * v) * (1 + u * v) == 0)).
  { intros Hp. destruct (Qmult_integral (1 + (u + h) * v) (1 + u * v) Hp) as [Hz | Hz].
    - apply H1. exact Hz.
    - apply H2. exact Hz. }
  field. split; assumption.
Qed.

(* =================== Final checks: the assumption face and the extraction test =================== *)
(* Triple tally: the list of 6 lemma names = 6 Qed closures = 6 Print *)
(* Assumptions statements, with zero discrepancy. *)
Print Assumptions abl9_atan_incr_step_cond.
Print Assumptions abl9_atan_deriv_uniform.
Print Assumptions abl9_wsq_ring_id.
Print Assumptions abl9_wincr_ring_id.
Print Assumptions abl9_wsq_div_id.
Print Assumptions abl9_wincr_div_id.

(* Extraction test (criterion: the output has Obj.magic count 0). *)
Recursive Extraction abl9_atan_deriv_uniform abl9_wsq_ring_id abl9_wincr_ring_id
  abl9_wsq_div_id abl9_wincr_div_id.
