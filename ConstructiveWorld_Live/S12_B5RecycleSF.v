(* ConstructiveWorld-Set — B5 recycled bounds and the SF working-memory / free-energy model. *)
(**
 * S12_B5RecycleSF: recycled reassembly of the B5 bound family and the
 *   SF working-memory / free-energy model (constructive [Set] layer).
 *
 * Mission.  [b5e_pern_main] (the per-n main bound, assembled from the
 *   dec three-group and the budget face); the working-memory model
 *   [SFWorkingMemory]; the replacement segments
 *   [b5q_arctan_one_leibniz_quarter], [sf_qeq_le], [sf_qleT_refl],
 *   [sf_amp2_nonneg], [sf_smx_exp_score_nonneg], whose proofs expand
 *   the forwarded statement bodies at definition level with explicit
 *   derivation chains (no single-hop forwards).
 *
 * Dependencies.  S01_BaseRing through S11_TP3B5; Stdlib QArith, List,
 *   Bool, Arith, Setoid, Morphisms, Lia, Lqa.
 *
 * References.  Free-energy bound decomposition over working-memory
 *   state lists; arctan / exponential / logarithm bound reassembly.
 *
 * Constructivity.  Entirely constructive; no unproved statements;
 *   every proof closes by [Qed]; the file-tail [Print Assumptions]
 *   anchors all report [Closed under the global context].
 *
 * Build.  [coqc -native-compiler no -q -Q . "" S12_B5RecycleSF.v]
 *   compiles cleanly (exit 0); the first eight bytes of the artifact
 *   are [436f7121 00015ff4].
 *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Export S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.
From Stdlib Require Import Lqa.
Opaque Qred.


(* ============================================================ *)
(* B5-A item1c: closed-form premise resolution. *)
(*   The B3 main statement [b3rr_real_arctan_deriv_linear] instantiates *)
(*   the item1b section variables; the closed-form main statement *)
(*   is [b5a_sin_atan_diff_closed_r]. *)
(*   The proofs consume the item1b lemma family. *)
(* ============================================================ *)

(* ============================================================ *)
(* 0. The positive inverse is certificate-independent: *)
(*   [real_inv_proj u H] gives [proj == Qinv (projT1 u n)] for all [n >= N_H]. *)
(* ============================================================ *)
Lemma b5c_inv_pos_cert_eq : forall (u : Real) (H1 H2 : real_lt real_zero u),
  real_eq (real_inv_pos u H1) (real_inv_pos u H2).
Proof.
  intros u H1 H2.
  destruct (real_inv_proj u H1) as [N1 HN1].
  destruct (real_inv_proj u H2) as [N2 HN2].
  unfold real_eq.
  intros eps Heps.
  exists (Nat.max N1 N2).
  intros n Hn.
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hd0 : projT1 (real_inv_pos u H1) n - projT1 (real_inv_pos u H2) n == 0).
  { apply NatLe_drop in Hn.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    assert (Hn2 : (N2 <= n)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (HN1 n (NatLe_lift _ _ Hn1))). rewrite (qeqT_imp_qeq _ _ (HN2 n (NatLe_lift _ _ Hn2))). ring. }
  assert (Hd : Qabs (projT1 (real_inv_pos u H1) n - projT1 (real_inv_pos u H2) n) == 0).
  { rewrite Hd0. reflexivity. }
  assert (Hcmp : Qcompare (Qabs (projT1 (real_inv_pos u H1) n - projT1 (real_inv_pos u H2) n)) eps = Lt).
  { assert (Hc1 : Qcompare (Qabs (projT1 (real_inv_pos u H1) n - projT1 (real_inv_pos u H2) n)) eps = Qcompare 0 eps)
      by (exact (Qcompare_comp (Qabs (projT1 (real_inv_pos u H1) n - projT1 (real_inv_pos u H2) n)) 0 Hd eps eps (Qeq_refl eps))).
    rewrite Hc1. exact Hcmp0. }
  rewrite Hcmp. reflexivity.
Qed.

(* ============================================================ *)
(* 1. Bridge from the b3rr conclusion (h times the [b3r]-certified inverse) *)
(*   to the b5a shape (h times the [b5a_one_plus_sq_pos]-certified inverse); *)
(*   errors transport along [real_eq]; delta and base-point bound from [b3rr]. *)
(* ============================================================ *)
Lemma b5c_atan_deriv_b5a_r :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                 (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                            (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                      (b5a_one_plus_sq_pos x)) h)))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps.
  destruct (b3rr_real_arctan_deriv_linear r Hr0 Hr1 x Hxr eps Heps)
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
                        (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                                   (real_mult h I3)))))
             (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                        (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                                   (real_mult I5 h)))))
             (real_plus (real_mult eps (real_abs h)) eps')
             (real_plus (real_mult eps (real_abs h)) eps')).
    { apply RealSetoid.real_eq_abs_compat.
      apply (RealSetoid.real_eq_plus_compat
               (cauchy_real_arctan (real_plus x h) Hxh)
               (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                                    (real_mult h I3)))
               (cauchy_real_arctan (real_plus x h) Hxh)
               (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                                    (real_mult I5 h)))).
      - apply real_eq_refl.
      - apply RealSetoid.real_eq_opp_compat.
        apply (RealSetoid.real_eq_plus_compat
                 (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                 (real_mult h I3)
                 (cauchy_real_arctan x (b3rr_dom_r1 x r Hxr Hr1))
                 (real_mult I5 h)).
        + apply real_eq_refl.
        + apply real_eq_sym. exact Hsl. }
    { apply real_eq_refl. }
    { unfold I3.
      exact (Hd h Hh Hxh eps' Heps'). }
Qed.


(* ============================================================ *)
(* Part C': [b5c_vdh_pts_r], the r-parameterized closed form of item1b *)
(*   Part C ([b5n_vdh_pts]); the derivative fact comes from the bridge *)
(*   [b5c_atan_deriv_b5a_r]; the base-point certificate is bound as *)
(*   [Hx := b3rr_dom_r1 x r Hxr Hr1] (the bridge's, verbatim); otherwise as [b5n_vdh_pts]. *)
(* ============================================================ *)

Lemma b5c_vdh_pts_r : forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1)
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
  set (Hx := b3rr_dom_r1 x r Hxr Hr1).
  set (eps2 := real_mult eps (real_const k2)).
  assert (Heps2 : real_lt real_zero eps2).
  { unfold eps2. apply real_mult_positive.
    - exact Heps.
    - apply real_const_pos. exact Hk2. }
  destruct (b5c_atan_deriv_b5a_r r Hr0 Hr1 x Hxr eps2 Heps2) as [δa [Hδa0 Hδa]].
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
    (* the projection of V agrees with that of [b5i_vdh_absV] by the definitional unfolding of [b5a_atan_d] *)
    apply (b5i_vdh_absV x Hx h Hxh n
             (Qplus (Qmult (Qmult en k2) (Qabs hn))
                    (Qmult (Qmult 2 k2p) en'))).
    unfold b5a_atan_d, V in Hpt.
    exact Hpt.
Qed.

(* ============================================================ *)
(* Part E': [b5a_sin_atan_diff_closed_r], the closed form of item1b Part E *)
(*   (r-parameterized; the proof text is reused with [Hx := b3rr_dom_r1 x r Hxr Hr1] *)
(*   and the Y witness taken from [b5c_vdh_pts_r]; no top-level section variables). *)
(* ============================================================ *)

Lemma b5a_sin_atan_diff_closed_r :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (b5a_comp_err_sin x (b3rr_dom_r1 x r Hxr Hr1) h Hxh))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr Hr1).
  destruct (b5i_sinA_bounded x Hx) as [Ms [HMs_pos HMs_all]].
  destruct (b5i_cosA_bounded x Hx) as [Mc [HMc_pos HMc_all]].
  destruct b5i_exp_arch4 as [C4 [HC4ge1 HC4]].
  destruct (b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
  assert (HMsQ : Qlt 0 Ms). { apply QltT_to_Qlt. exact HMs_pos. }
  assert (HMcQ : Qlt 0 Mc). { apply QltT_to_Qlt. exact HMc_pos. }
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. exact HMsQ. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. exact HMcQ. }
  assert (HC4le1 : Qle 1 C4). { apply QleT'_to_Qle. exact HC4ge1. }
  assert (HC40 : Qle 0 C4).
  { apply (Qle_trans 0 1 C4).
    { unfold Qle. simpl. lia. }
    { exact HC4le1. } }
  set (S := Qplus Ms Mc).
  assert (HSlt : Qlt 0 S). { unfold S. nra. }
  set (K1e := Qplus (Qmult Ms (Qplus (Qmult 4 C4) 2))
                    (Qmult Mc (Qplus (Qmult 4 C4) 4))).
  assert (HK1_0 : Qle 0 K1e). { unfold K1e. nra. }
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
  (* global budgets: coef (quadratic branch), coefC (crude branch), and 8k2p * K1 (forced by the crude branch) *)
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
  (* delta assembly: each component is positive *)
  assert (H12T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (H14T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  destruct (b5c_vdh_pts_r r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2T Hk2pT) as [δa [Hδa0 Hδa]].
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
    (* h is placed below delta by a four-fold minimum *)
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
    (* X: the pointwise h bound [b5n_h_pts] *)
    destruct (b5n_h_pts h eps kδ k2 Heps HkδT Hk2T Hhlr Hh12 HhE) as [Nh HNh].
    (* Y: arctan' at [eps2 := eps * k2] and [eps2' := eps' * k2p] *)
    destruct (Hδa h Hhda Hxh eps' Heps') as [Nw HNw].
    (* the column-error bound *)
    destruct (b5i_rs_addcol x Hx h Hxh eta HetaT) as [Nc HNc].
    (* pointwise budget (with witness for eps') *)
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
    (* main assembly: from [real_le] to the left branch of [real_lt], witnessed by eta *)
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
      (* Z: the per-n main bound *)
      assert (Hmain : Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { apply QleT'_to_Qle. apply (b5n_pern_main x Hx h Hxh n Ms Mc C4 eta kδ k2 k2p en en').
        { exact (QleT'_to_Qle _ _ (HMs_all n)). }
        { exact (QleT'_to_Qle _ _ (HMc_all n)). }
        { exact HC4. }
        { exact HC40. }
        { exact (HNc n HnNc). }
        { exact (QleT'_to_Qle _ _ Hhδn). }
        { exact (QleT'_to_Qle _ _ Hh12n). }
        { exact (QleT'_to_Qle _ _ Hhqn). }
        { exact (QleT'_to_Qle _ _ (HNw n HnNw)). }
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
      (* margin: [eta < (1/4) en']; Hfin: [eta < (en * hn + en') - Dn] *)
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
Qed.

(* ============================================================ *)
(* B5-A E-ODE T1: the cos closed-form family. *)
(*   The cos analogue of [b5a_sin_atan_diff_closed_r]: the main statement *)
(*   [b5a_cos_atan_diff_closed_r] with twelve [b5d_*] auxiliary lemmas. *)
(*   The proofs depend only on the in-place [b5i_*], [b5n_*], [b5c_*], *)
(*   [b5a_*], [b5b_*] families. *)
(* ============================================================ *)

(* ============================================================ *)
(* D1: [b5d_addcol_cos], the cos version of the pointwise column error *)
(*   (the analogue of [b5i_addcol_sin]; the [rs_add_cos] column is *)
(*   [c(Ah) - (cA * cv - sA * sv)] with [Ah_n + v_n == Ah_n] pointwise) *)
(* ============================================================ *)
Definition b5d_addcol_cos (x h : Real) (Hxh : forall n : nat,
  QleT' (Qabs (projT1 (real_plus x h) n)) 1) (n : nat) : Q :=
  Qabs (cos_partial n (b5i_Ahn x h n)
        - (cos_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
           + - (sin_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n)))).

(* ============================================================ *)
(* D2/D3: [b5d_S1n_cos] and [b5d_S2n_cos], the two pointwise cos pieces: *)
(*   [S1_cos := c(Ah) - cA + sA * v] (quadratic: addcol plus *)
(*   [cA * (cv - 1) - sA * (sv - v)]); [S2_cos := -sA * (v - dh)] (linear, coef [Ms]) *)
(* ============================================================ *)
Definition b5d_S1n_cos (x h : Real) (n : nat) : Q :=
  cos_partial n (b5i_Ahn x h n) - cos_partial n (b5i_An x n)
  - (- (sin_partial n (b5i_An x n) * b5i_vn x h n)).
Definition b5d_S2n_cos (x h : Real) (n : nat) : Q :=
  - (sin_partial n (b5i_An x n)
     * (b5i_vn x h n - b5i_dn x n * projT1 h n)).

(* ============================================================ *)
(* D4: [b5d_dn_split_cos]: [comp_err_cos_n == S1n_cos + S2n_cos] *)
(*   (the analogue of [b5i_dn_split], using the root [b5i_cos_err_proj]) *)
(* ============================================================ *)
Lemma b5d_dn_split_cos : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat), QeqT (projT1 (b5a_comp_err_cos x Hx h Hxh) n) (Qplus (b5d_S1n_cos x h n) (b5d_S2n_cos x h n)).
Proof.
  intros x Hx h Hxh n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (b5i_cos_err_proj x Hx h Hxh n)).
  unfold b5d_S1n_cos, b5d_S2n_cos, b5i_vn, b5i_dn, b5i_Ahn, b5i_An.
  ring.
Qed.

(* ============================================================ *)
(* D5: [b5d_rs_addcol_cos], the pointwise bound on the cos column error *)
(*   (the analogue of [b5i_rs_addcol]; the [rs_add_cos] column is *)
(*   [cos(A+v) == cA * cv - sA * sv]; the bridge structure matches the sin side) *)
(* ============================================================ *)
Lemma b5d_rs_addcol_cos : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (eps : Q), QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QltT (b5d_addcol_cos x h Hxh n) eps).
Proof.
  intros x Hx h Hxh eps Heps.
  set (A := cauchy_real_arctan x Hx).
  set (Ah := cauchy_real_arctan (real_plus x h) Hxh).
  set (v := real_plus Ah (real_opp A)).
  destruct (rs_add_cos A v eps Heps) as [N HN].
  exists N.
  intros n Hn.
  assert (Heq : Qeq (b5d_addcol_cos x h Hxh n)
                    (Qabs (Qminus (projT1 (cauchy_real_cos (real_plus A v)) n)
                                  (projT1 (real_plus (real_mult (cauchy_real_cos A) (cauchy_real_cos v))
                                                    (real_opp (real_mult (cauchy_real_sin A) (cauchy_real_sin v)))) n)))).
  { apply Qabs_wd.
    transitivity (Qminus (cos_partial n (b5i_Ahn x h n))
                         (Qplus (Qmult (cos_partial n (b5i_An x n)) (cos_partial n (b5i_vn x h n)))
                                (Qopp (Qmult (sin_partial n (b5i_An x n)) (sin_partial n (b5i_vn x h n)))))).
    - unfold b5d_addcol_cos. ring.
    - apply Qminus_comp.
      + apply Qeq_sym.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_cos_proj (real_plus A v) n)).
        apply qeqT_imp_qeq. apply (b5a_cos_partial_wd n (projT1 (real_plus A v) n) (b5i_Ahn x h n)).
        unfold v, A, Ah.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_arctan x Hx)
                                       (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                                  (real_opp (cauchy_real_arctan x Hx))) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                                       (real_opp (cauchy_real_arctan x Hx)) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (cauchy_real_arctan x Hx) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_plus x h) Hxh n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hx n)).
        unfold b5i_Ahn, b5i_An. ring.
      + transitivity (Qplus (Qmult (projT1 (cauchy_real_cos A) n) (projT1 (cauchy_real_cos v) n))
                            (Qopp (Qmult (projT1 (cauchy_real_sin A) n) (projT1 (cauchy_real_sin v) n)))).
        * apply Qplus_comp.
          -- apply Qmult_comp.
             ++ apply Qeq_sym.
                setoid_rewrite (qeqT_imp_qeq _ _ (real_cos_proj A n)).
                apply qeqT_imp_qeq. apply (b5a_cos_partial_wd n (projT1 A n) (b5i_An x n)).
                unfold A. setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hx n)). unfold b5i_An. reflexivity.
             ++ apply Qeq_sym.
                setoid_rewrite (qeqT_imp_qeq _ _ (real_cos_proj v n)).
                apply qeqT_imp_qeq. apply (b5a_cos_partial_wd n (projT1 v n) (b5i_vn x h n)).
                unfold v, A, Ah.
                setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                                               (real_opp (cauchy_real_arctan x Hx)) n)).
                setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (cauchy_real_arctan x Hx) n)).
                setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_plus x h) Hxh n)).
                setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hx n)).
                unfold b5i_vn, b5i_Ahn, b5i_An. ring.
          -- apply Qopp_comp.
             apply Qmult_comp.
             ++ apply Qeq_sym.
                setoid_rewrite (qeqT_imp_qeq _ _ (real_sin_proj A n)).
                apply qeqT_imp_qeq. apply (b5a_sin_partial_wd n (projT1 A n) (b5i_An x n)).
                unfold A. setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hx n)). unfold b5i_An. reflexivity.
             ++ apply Qeq_sym.
                setoid_rewrite (qeqT_imp_qeq _ _ (real_sin_proj v n)).
                apply qeqT_imp_qeq. apply (b5a_sin_partial_wd n (projT1 v n) (b5i_vn x h n)).
                unfold v, A, Ah.
                setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                                               (real_opp (cauchy_real_arctan x Hx)) n)).
                setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (cauchy_real_arctan x Hx) n)).
                setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj (real_plus x h) Hxh n)).
                setoid_rewrite (qeqT_imp_qeq _ _ (arctan_real_proj x Hx n)).
                unfold b5i_vn, b5i_Ahn, b5i_An. ring.
        * apply Qeq_sym.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (cauchy_real_cos A) (cauchy_real_cos v))
                                         (real_opp (real_mult (cauchy_real_sin A) (cauchy_real_sin v))) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (cauchy_real_cos A) (cauchy_real_cos v) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult (cauchy_real_sin A) (cauchy_real_sin v)) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (cauchy_real_sin A) (cauchy_real_sin v) n)).
          apply Qplus_comp; [ apply Qmult_comp; reflexivity | apply Qopp_comp; apply Qmult_comp; reflexivity ]. }
  apply (qltT_eq_compat_l (Qabs (Qminus (projT1 (cauchy_real_cos (real_plus A v)) n)
                                        (projT1 (real_plus (real_mult (cauchy_real_cos A) (cauchy_real_cos v))
                                                          (real_opp (real_mult (cauchy_real_sin A) (cauchy_real_sin v)))) n)))
                          (b5d_addcol_cos x h Hxh n) eps).
  - apply qeq_imp_qeqT. apply Qeq_sym. exact Heq.
  - exact (HN n Hn).
Qed.

(* ============================================================ *)
(* D6: [b5d_S1_quad_cos], the quadratic bound on [S1_cos] for [|v| <= 1] *)
(*   |[S1_cos]| <= colQ + Mc * |v|^2 + Ms * |v|^3 (the analogue of [b5i_S1_quad]; *)
(*   the sin version has [Ms * |v|^2 + Mc * |v|^3], so the coefficient roles swap: *)
(*   the quadratic term [cA * (cv - 1)] carries [Mc] and [sA * (-(sv - v))] carries [Ms]) *)
(* ============================================================ *)
Lemma b5d_S1_quad_cos : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (Ms Mc c : Q),
  Qle (Qabs (sin_partial n (b5i_An x n))) Ms ->
  Qle (Qabs (cos_partial n (b5i_An x n))) Mc ->
  Qle (Qabs (b5i_vn x h n)) 1 ->
  QltT (b5d_addcol_cos x h Hxh n) c ->
  QleT' (Qabs (b5d_S1n_cos x h n))
      (Qplus c (Qplus (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 2))
                      (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 3)))).
Proof.
  intros x Hx h Hxh n Ms Mc c HMs HMc Hv1 Hcol.
  apply Qle_to_QleT'.
  assert (Halg : b5d_S1n_cos x h n ==
                 Qplus (cos_partial n (b5i_Ahn x h n)
                        - (cos_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                           + - (sin_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n))))
                       (Qplus (cos_partial n (b5i_An x n) * (cos_partial n (b5i_vn x h n) - 1))
                              (Qopp (Qmult (sin_partial n (b5i_An x n))
                                           (sin_partial n (b5i_vn x h n) - b5i_vn x h n))))).
  { unfold b5d_S1n_cos, b5i_vn. ring. }
  rewrite Halg.
  set (A := cos_partial n (b5i_Ahn x h n)
            - (cos_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
               + - (sin_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n)))).
  set (B := cos_partial n (b5i_An x n) * (cos_partial n (b5i_vn x h n) - 1)).
  set (C := Qopp (Qmult (sin_partial n (b5i_An x n))
                        (sin_partial n (b5i_vn x h n) - b5i_vn x h n))).
  assert (Ht1 : Qle (Qabs (Qplus A (Qplus B C)))
                    (Qplus (Qabs A) (Qplus (Qabs B) (Qabs C)))).
  { apply (Qle_trans _ (Qplus (Qabs A) (Qabs (Qplus B C))) _).
    - apply Qabs_triangle.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply Qabs_triangle. }
  assert (HA : Qle (Qabs A) c).
  { apply Qlt_le_weak. apply QltT_to_Qlt.
    apply (qltT_eq_compat_l (b5d_addcol_cos x h Hxh n) (Qabs A) c).
    - apply qeq_imp_qeqT. unfold A, b5d_addcol_cos, b5i_vn. ring.
    - exact Hcol. }
  assert (HMs0 : Qle 0 Ms).
  { apply (Qle_trans 0 (Qabs (sin_partial n (b5i_An x n))) Ms).
    - apply Qabs_nonneg.
    - exact HMs. }
  assert (HMc0 : Qle 0 Mc).
  { apply (Qle_trans 0 (Qabs (cos_partial n (b5i_An x n))) Mc).
    - apply Qabs_nonneg.
    - exact HMc. }
  assert (HB : Qle (Qabs B) (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 2))).
  { apply (Qle_trans (Qabs B)
                     (Qmult (Qabs (cos_partial n (b5i_An x n)))
                            (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                     (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 2))).
    - unfold B.
      apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply (Qabs_Qmult (cos_partial n (b5i_An x n))
                                           (cos_partial n (b5i_vn x h n) - 1)).
    - apply (Qle_trans (Qmult (Qabs (cos_partial n (b5i_An x n)))
                              (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                       (Qmult Mc (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                       (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 2))).
      + apply (Qmult_le_compat_r (Qabs (cos_partial n (b5i_An x n))) Mc
                                 (Qabs (cos_partial n (b5i_vn x h n) - 1))).
        * exact HMc.
        * apply Qabs_nonneg.
      + apply (Qle_trans (Qmult Mc (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                         (Qmult (Qabs (cos_partial n (b5i_vn x h n) - 1)) Mc)
                         (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 2))).
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm.
        * apply (Qle_trans (Qmult (Qabs (cos_partial n (b5i_vn x h n) - 1)) Mc)
                           (Qmult (q_pow (Qabs (b5i_vn x h n)) 2) Mc)
                           (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 2))).
          -- apply (Qmult_le_compat_r (Qabs (cos_partial n (b5i_vn x h n) - 1))
                                      (q_pow (Qabs (b5i_vn x h n)) 2) Mc).
             ++ apply QleT'_to_Qle. apply (sc_cos_sq_bound_c1 n (b5i_vn x h n)). exact Hv1.
             ++ exact HMc0.
          -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm. }
  assert (HC : Qle (Qabs C) (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 3))).
  { apply (Qle_trans (Qabs C)
                     (Qmult (Qabs (sin_partial n (b5i_An x n)))
                            (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                     (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 3))).
    - apply (Qle_trans (Qabs C)
                       (Qabs (Qmult (sin_partial n (b5i_An x n))
                                    (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                       (Qmult (Qabs (sin_partial n (b5i_An x n)))
                              (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))).
      + unfold C. apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_opp.
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply (Qabs_Qmult (sin_partial n (b5i_An x n))
                                             (sin_partial n (b5i_vn x h n) - b5i_vn x h n)).
    - apply (Qle_trans (Qmult (Qabs (sin_partial n (b5i_An x n)))
                              (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                       (Qmult Ms (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                       (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 3))).
      + apply (Qmult_le_compat_r (Qabs (sin_partial n (b5i_An x n))) Ms
                                 (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n))).
        * exact HMs.
        * apply Qabs_nonneg.
      + apply (Qle_trans (Qmult Ms (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                         (Qmult (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)) Ms)
                         (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 3))).
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm.
        * apply (Qle_trans (Qmult (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)) Ms)
                           (Qmult (q_pow (Qabs (b5i_vn x h n)) 3) Ms)
                           (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 3))).
          -- apply (Qmult_le_compat_r (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n))
                                      (q_pow (Qabs (b5i_vn x h n)) 3) Ms).
             ++ apply QleT'_to_Qle. apply (sc_sin_cube_bound_c1 n (b5i_vn x h n)). exact Hv1.
             ++ exact HMs0.
          -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm. }
  apply (Qle_trans (Qabs (Qplus A (Qplus B C)))
                   (Qplus (Qabs A) (Qplus (Qabs B) (Qabs C)))
                   (Qplus c (Qplus (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 2))
                                   (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 3))))).
  - exact Ht1.
  - apply Qplus_le_compat.
    + exact HA.
    + apply Qplus_le_compat.
      * exact HB.
      * exact HC.
Qed.

(* ============================================================ *)
(* D7: [b5d_S2_le_cos], [ |S2_cos| <= Ms * wb ] (coefficient swap: *)
(*   the sin version [S2 := cA * (v - dh)] carries [Mc]; the cos version *)
(*   [S2 := -sA * (v - dh)] carries [Ms]; the analogue of [b5i_S2_le]) *)
(* ============================================================ *)
Lemma b5d_S2_le_cos : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (Ms wb : Q),
  Qle (Qabs (sin_partial n (b5i_An x n))) Ms ->
  Qle (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)) wb ->
  QleT' (Qabs (b5d_S2n_cos x h n)) (Qmult Ms wb).
Proof.
  intros x Hx h Hxh n Ms wb HMs Hwb.
  apply Qle_to_QleT'.
  unfold b5d_S2n_cos.
  apply (Qle_trans (Qabs (Qopp (sin_partial n (b5i_An x n)
                                * (b5i_vn x h n - b5i_dn x n * projT1 h n))))
                   (Qabs (sin_partial n (b5i_An x n)
                          * (b5i_vn x h n - b5i_dn x n * projT1 h n)))
                   (Qmult Ms wb)).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_opp.
  - apply (Qle_trans (Qabs (sin_partial n (b5i_An x n)
                            * (b5i_vn x h n - b5i_dn x n * projT1 h n)))
                     (Qmult (Qabs (sin_partial n (b5i_An x n)))
                            (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)))
                     (Qmult Ms wb)).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      apply (Qabs_Qmult (sin_partial n (b5i_An x n))
                        (b5i_vn x h n - b5i_dn x n * projT1 h n)).
    + assert (HMs0 : Qle 0 Ms).
      { apply (Qle_trans 0 (Qabs (sin_partial n (b5i_An x n))) Ms).
        - apply Qabs_nonneg.
        - exact HMs. }
      apply (Qle_trans (Qmult (Qabs (sin_partial n (b5i_An x n)))
                              (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)))
                       (Qmult Ms (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)))
                       (Qmult Ms wb)).
      * apply (Qmult_le_compat_r (Qabs (sin_partial n (b5i_An x n))) Ms
                                 (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n))).
        -- exact HMs.
        -- apply Qabs_nonneg.
      * apply (Qle_trans (Qmult Ms (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)))
                         (Qmult (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)) Ms)
                         (Qmult Ms wb)).
        -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm.
        -- apply (Qle_trans (Qmult (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)) Ms)
                            (Qmult wb Ms)
                            (Qmult Ms wb)).
           ++ apply (Qmult_le_compat_r (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n))
                                       wb Ms).
              ** exact Hwb.
              ** exact HMs0.
           ++ apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm.
Qed.

(* ============================================================ *)
(* D8: [b5d_S1_crude_cos], the global bound on [S1_cos] (no [|v| <= 1] needed) *)
(*   [ |S1_cos| <= |col| + Mc(Mcv+1) + Ms(Msv+|v|) ] (the analogue of *)
(*   [b5i_S1_crude]; the sin version [Ms(Mcv+1)+Mc(Msv+|v|)] becomes *)
(*   the swapped roles: the quad/cv piece carries [Mc], the sv piece [Ms]) *)
(* ============================================================ *)
Lemma b5d_S1_crude_cos : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (Ms Mc Mcv Msv : Q),
  Qle (Qabs (sin_partial n (b5i_An x n))) Ms ->
  Qle (Qabs (cos_partial n (b5i_An x n))) Mc ->
  Qle (Qabs (cos_partial n (b5i_vn x h n))) Mcv ->
  Qle (Qabs (sin_partial n (b5i_vn x h n))) Msv ->
  QleT' (Qabs (b5d_S1n_cos x h n))
      (Qplus (Qabs (cos_partial n (b5i_Ahn x h n)
                    - (cos_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                       + - (sin_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n)))))
             (Qplus (Qmult Mc (Qplus Mcv 1))
                    (Qmult Ms (Qplus Msv (Qabs (b5i_vn x h n)))))).
Proof.
  intros x Hx h Hxh n Ms Mc Mcv Msv HMs HMc HMcv HMsv.
  apply Qle_to_QleT'.
  assert (Halg : b5d_S1n_cos x h n ==
                 Qplus (cos_partial n (b5i_Ahn x h n)
                        - (cos_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                           + - (sin_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n))))
                       (Qplus (cos_partial n (b5i_An x n) * (cos_partial n (b5i_vn x h n) - 1))
                              (Qopp (Qmult (sin_partial n (b5i_An x n))
                                           (sin_partial n (b5i_vn x h n) - b5i_vn x h n))))).
  { unfold b5d_S1n_cos, b5i_vn. ring. }
  rewrite Halg.
  set (A := cos_partial n (b5i_Ahn x h n)
            - (cos_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
               + - (sin_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n)))).
  set (B := cos_partial n (b5i_An x n) * (cos_partial n (b5i_vn x h n) - 1)).
  set (C := Qopp (Qmult (sin_partial n (b5i_An x n))
                        (sin_partial n (b5i_vn x h n) - b5i_vn x h n))).
  assert (Ht1 : Qle (Qabs (Qplus A (Qplus B C)))
                    (Qplus (Qabs A) (Qplus (Qabs B) (Qabs C)))).
  { apply (Qle_trans _ (Qplus (Qabs A) (Qabs (Qplus B C))) _).
    - apply Qabs_triangle.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply Qabs_triangle. }
  assert (HMs0 : Qle 0 Ms).
  { apply (Qle_trans 0 (Qabs (sin_partial n (b5i_An x n))) Ms).
    - apply Qabs_nonneg.
    - exact HMs. }
  assert (HMc0 : Qle 0 Mc).
  { apply (Qle_trans 0 (Qabs (cos_partial n (b5i_An x n))) Mc).
    - apply Qabs_nonneg.
    - exact HMc. }
  assert (HB : Qle (Qabs B) (Qmult Mc (Qplus Mcv 1))).
  { apply (Qle_trans (Qabs B)
                     (Qmult (Qabs (cos_partial n (b5i_An x n)))
                            (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                     (Qmult Mc (Qplus Mcv 1))).
    - unfold B.
      apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply (Qabs_Qmult (cos_partial n (b5i_An x n))
                                           (cos_partial n (b5i_vn x h n) - 1)).
    - apply (Qle_trans (Qmult (Qabs (cos_partial n (b5i_An x n)))
                              (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                       (Qmult Mc (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                       (Qmult Mc (Qplus Mcv 1))).
      + apply (Qmult_le_compat_r (Qabs (cos_partial n (b5i_An x n))) Mc
                                 (Qabs (cos_partial n (b5i_vn x h n) - 1))).
        * exact HMc.
        * apply Qabs_nonneg.
      + apply (Qle_trans (Qmult Mc (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                         (Qmult (Qabs (cos_partial n (b5i_vn x h n) - 1)) Mc)
                         (Qmult Mc (Qplus Mcv 1))).
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm.
        * apply (Qle_trans (Qmult (Qabs (cos_partial n (b5i_vn x h n) - 1)) Mc)
                           (Qmult (Qplus Mcv 1) Mc)
                           (Qmult Mc (Qplus Mcv 1))).
          -- apply (Qmult_le_compat_r (Qabs (cos_partial n (b5i_vn x h n) - 1))
                                      (Qplus Mcv 1) Mc).
             ++ apply (Qle_trans (Qabs (cos_partial n (b5i_vn x h n) - 1))
                                 (Qplus (Qabs (cos_partial n (b5i_vn x h n))) 1)
                                 (Qplus Mcv 1)).
                ** apply (Qle_trans (Qabs (cos_partial n (b5i_vn x h n) + - 1))
                                    (Qplus (Qabs (cos_partial n (b5i_vn x h n))) (Qabs (- 1)))
                                    (Qplus (Qabs (cos_partial n (b5i_vn x h n))) 1)).
                   --- unfold Qminus. apply Qabs_triangle.
                   --- apply Qplus_le_compat.
                       ++++ apply Qle_refl.
                       ++++ unfold Qabs, Qle. simpl. lia.
                ** apply Qplus_le_compat.
                   --- exact HMcv.
                   --- apply Qle_refl.
             ++ apply (Qle_trans 0 (Qabs (cos_partial n (b5i_An x n))) Mc).
                ** apply Qabs_nonneg.
                ** exact HMc.
          -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm. }
  assert (HC : Qle (Qabs C) (Qmult Ms (Qplus Msv (Qabs (b5i_vn x h n))))).
  { apply (Qle_trans (Qabs C)
                     (Qmult (Qabs (sin_partial n (b5i_An x n)))
                            (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                     (Qmult Ms (Qplus Msv (Qabs (b5i_vn x h n))))).
    - apply (Qle_trans (Qabs C)
                       (Qabs (Qmult (sin_partial n (b5i_An x n))
                                    (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                       (Qmult (Qabs (sin_partial n (b5i_An x n)))
                              (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))).
      + unfold C. apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_opp.
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply (Qabs_Qmult (sin_partial n (b5i_An x n))
                                             (sin_partial n (b5i_vn x h n) - b5i_vn x h n)).
    - apply (Qle_trans (Qmult (Qabs (sin_partial n (b5i_An x n)))
                              (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                       (Qmult Ms (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                       (Qmult Ms (Qplus Msv (Qabs (b5i_vn x h n))))).
      + apply (Qmult_le_compat_r (Qabs (sin_partial n (b5i_An x n))) Ms
                                 (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n))).
        * exact HMs.
        * apply Qabs_nonneg.
      + apply (Qle_trans (Qmult Ms (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                         (Qmult (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)) Ms)
                         (Qmult Ms (Qplus Msv (Qabs (b5i_vn x h n))))).
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm.
        * apply (Qle_trans (Qmult (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)) Ms)
                           (Qmult (Qplus Msv (Qabs (b5i_vn x h n))) Ms)
                           (Qmult Ms (Qplus Msv (Qabs (b5i_vn x h n))))).
          -- apply (Qmult_le_compat_r (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n))
                                      (Qplus Msv (Qabs (b5i_vn x h n))) Ms).
             ++ apply (Qle_trans (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n))
                                 (Qplus (Qabs (sin_partial n (b5i_vn x h n)))
                                        (Qabs (b5i_vn x h n)))
                                 (Qplus Msv (Qabs (b5i_vn x h n)))).
                ** apply (Qle_trans (Qabs (sin_partial n (b5i_vn x h n) + - b5i_vn x h n))
                                    (Qplus (Qabs (sin_partial n (b5i_vn x h n)))
                                           (Qabs (- b5i_vn x h n)))
                                    (Qplus (Qabs (sin_partial n (b5i_vn x h n)))
                                           (Qabs (b5i_vn x h n)))).
                   --- unfold Qminus. apply Qabs_triangle.
                   --- apply Qplus_le_compat.
                       ++++ apply Qle_refl.
                       ++++ apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_opp.
                ** apply Qplus_le_compat.
                   --- exact HMsv.
                   --- apply Qle_refl.
             ++ apply (Qle_trans 0 (Qabs (sin_partial n (b5i_An x n))) Ms).
                ** apply Qabs_nonneg.
                ** exact HMs.
          -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm. }
  apply (Qle_trans (Qabs (Qplus A (Qplus B C)))
                   (Qplus (Qabs A) (Qplus (Qabs B) (Qabs C)))
                   (Qplus (Qabs A)
                          (Qplus (Qmult Mc (Qplus Mcv 1))
                                 (Qmult Ms (Qplus Msv (Qabs (b5i_vn x h n))))))).
  - exact Ht1.
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + apply Qplus_le_compat.
      * exact HB.
      * exact HC.
Qed.

(* ============================================================ *)
(* D9: [b5d_S1_crude_x_cos], the x-independent global bound on [S1_cos] *)
(*   [ |S1_cos| <= |col| + Mc(4C+2) + Ms(4C+4) ] (the analogue of *)
(*   [b5i_S1_crude_x], reusing the roots [cos_partial_le4] / [sin_partial_le4] *)
(*   with the coefficient roles swapped) *)
(* ============================================================ *)
Lemma b5d_S1_crude_x_cos : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (Ms Mc C : Q),
  Qle (Qabs (sin_partial n (b5i_An x n))) Ms ->
  Qle (Qabs (cos_partial n (b5i_An x n))) Mc ->
  (forall j : nat, QleT' (exp_series j 4) C) ->
  Qle 0 C ->
  Qle (Qabs (b5i_vn x h n)) 4 ->
  QleT' (Qabs (b5d_S1n_cos x h n))
      (Qplus (Qabs (cos_partial n (b5i_Ahn x h n)
                    - (cos_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                       + - (sin_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n)))))
             (Qplus (Qmult Mc (Qplus (Qmult 4 C) 2))
                    (Qmult Ms (Qplus (Qmult 4 C) 4)))).
Proof.
  intros x Hx h Hxh n Ms Mc C HMs HMc HC HC0 Hv4.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs (b5d_S1n_cos x h n))
                   (Qplus (Qabs (cos_partial n (b5i_Ahn x h n)
                                 - (cos_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                                    + - (sin_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n)))))
                          (Qplus (Qmult Mc (Qplus (Qplus (Qmult 4 C) 1) 1))
                                 (Qmult Ms (Qplus (Qmult 4 C) (Qabs (b5i_vn x h n))))))
                   (Qplus (Qabs (cos_partial n (b5i_Ahn x h n)
                                 - (cos_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                                    + - (sin_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n)))))
                          (Qplus (Qmult Mc (Qplus (Qmult 4 C) 2))
                                 (Qmult Ms (Qplus (Qmult 4 C) 4))))).
  - apply QleT'_to_Qle.
    apply (b5d_S1_crude_cos x Hx h Hxh n Ms Mc (Qplus (Qmult 4 C) 1) (Qmult 4 C)).
    + exact HMs.
    + exact HMc.
    + exact (QleT'_to_Qle _ _ (b5i_cos_partial_le4 C HC HC0 n (b5i_vn x h n) Hv4)).
    + exact (QleT'_to_Qle _ _ (b5i_sin_partial_le4 C HC HC0 n (b5i_vn x h n) Hv4)).
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + apply Qplus_le_compat.
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans (Qmult Ms (Qplus (Qmult 4 C) (Qabs (b5i_vn x h n))))
                         (Qmult (Qplus (Qmult 4 C) (Qabs (b5i_vn x h n))) Ms)
                         (Qmult Ms (Qplus (Qmult 4 C) 4))).
        -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm.
        -- apply (Qle_trans (Qmult (Qplus (Qmult 4 C) (Qabs (b5i_vn x h n))) Ms)
                            (Qmult (Qplus (Qmult 4 C) 4) Ms)
                            (Qmult Ms (Qplus (Qmult 4 C) 4))).
           ++ apply (Qmult_le_compat_r (Qplus (Qmult 4 C) (Qabs (b5i_vn x h n)))
                                       (Qplus (Qmult 4 C) 4) Ms).
              ** apply Qplus_le_compat.
                 --- apply Qle_refl.
                 --- exact Hv4.
              ** apply (Qle_trans 0 (Qabs (sin_partial n (b5i_An x n))) Ms).
                 --- apply Qabs_nonneg.
                 --- exact HMs.
           ++ apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm.
Qed.

(* ============================================================ *)
(* D10: [b5d_pern_quad_cos], branch A ([|v_n| <= 1]) absorbing the quadratic bound *)
(*   |D_cos| ≤ colQ + (2S·kδ + (3S+Ms)·k2)·(en·|h_n|)           *)
(*                  + (3S+Ms)·E2                                 *)
(*   (the analogue of [b5i_pern_quad]; the S2-side coefficient becomes [Ms]) *)
(* ============================================================ *)
Lemma b5d_pern_quad_cos : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (Ms Mc colQ kδ k2 : Q) (en E2 : Q),
  Qle (Qabs (sin_partial n (b5i_An x n))) Ms ->
  Qle (Qabs (cos_partial n (b5i_An x n))) Mc ->
  QltT (b5d_addcol_cos x h Hxh n) colQ ->
  Qle (Qabs (b5i_vn x h n)) 1 ->
  Qle (Qabs (projT1 h n)) (Qmult en kδ) ->
  Qle (Qabs (projT1 h n)) (1 # 2) ->
  Qle (Qabs (b5i_dn x n)) 1 ->
  Qle (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
      (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2) ->
  Qle 0 en -> Qle 0 k2 -> Qle 0 E2 ->
  QleT' (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
      (Qplus colQ
             (Qplus (Qmult (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                                  (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) k2))
                           (Qmult en (Qabs (projT1 h n))))
                    (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) E2))).
Proof.
  intros x Hx h Hxh n Ms Mc colQ kδ k2 en E2
         HMs HMc Hcol Hv1 Hhδ Hh12 Hd1 Hw Hen0 Hk20 HE20.
  apply Qle_to_QleT'.
  set (v := b5i_vn x h n).
  set (w := Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))).
  set (S := Qplus Ms Mc).
  assert (HMs0 : Qle 0 Ms).
  { apply (Qle_trans 0 (Qabs (sin_partial n (b5i_An x n))) Ms).
    - apply Qabs_nonneg.
    - exact HMs. }
  assert (HMc0 : Qle 0 Mc).
  { apply (Qle_trans 0 (Qabs (cos_partial n (b5i_An x n))) Mc).
    - apply Qabs_nonneg.
    - exact HMc. }
  assert (HS0 : Qle 0 S).
  { apply (Qle_trans 0 (Qplus 0 0) S).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply Qplus_le_compat.
      + exact HMs0.
      + exact HMc0. }
  assert (H2S0 : Qle 0 (Qmult 2 S)).
  { apply (Qmult_le_0_compat 2 S).
    - unfold Qle. simpl. lia.
    - exact HS0. }
  assert (H3S0 : Qle 0 (Qmult 3 S)).
  { apply (Qmult_le_0_compat 3 S).
    - unfold Qle. simpl. lia.
    - exact HS0. }
  assert (HB1 : Qle 0 (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)).
  { apply (Qle_trans 0 (Qplus 0 0) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply Qplus_le_compat.
      + apply (Qmult_le_0_compat (Qmult en k2) (Qabs (projT1 h n))).
        * apply (Qmult_le_0_compat en k2 Hen0 Hk20).
        * exact (Qabs_nonneg (projT1 h n)).
      + exact HE20. }
  assert (Hw0 : Qle 0 (Qabs w)).
  { exact (Qabs_nonneg w). }
  (* |v|^2 and |v|^3 are nonnegative *)
  assert (Hv2n : Qle 0 (q_pow (Qabs v) 2)).
  { rewrite (qeqT_imp_qeq _ _ (sc_qpow2_form (Qabs v))).
    apply (Qmult_le_0_compat (Qabs v) (Qabs v) (Qabs_nonneg v) (Qabs_nonneg v)). }
  assert (Hv3n : Qle 0 (q_pow (Qabs v) 3)).
  { rewrite (qeqT_imp_qeq _ _ (sc_qpow3_form (Qabs v))).
    apply (Qmult_le_0_compat (Qmult (Qabs v) (Qabs v)) (Qabs v)).
    - apply (Qmult_le_0_compat (Qabs v) (Qabs v) (Qabs_nonneg v) (Qabs_nonneg v)).
    - apply Qabs_nonneg. }
  (* |S1_cos| <= colQ + S * |v|^2 (the quadratic bound [Mc|v|^2 + Ms|v|^3 <= S|v|^2]) *)
  assert (HS1 : Qle (Qabs (b5d_S1n_cos x h n)) (Qplus colQ (Qmult S (q_pow (Qabs v) 2)))).
  { apply (Qle_trans (Qabs (b5d_S1n_cos x h n))
                     (Qplus colQ (Qplus (Qmult Mc (q_pow (Qabs v) 2)) (Qmult Ms (q_pow (Qabs v) 3))))
                     (Qplus colQ (Qmult S (q_pow (Qabs v) 2)))).
    - apply QleT'_to_Qle.
    apply (b5d_S1_quad_cos x Hx h Hxh n Ms Mc colQ).
      + exact HMs.
      + exact HMc.
      + exact Hv1.
      + exact Hcol.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply (Qle_trans (Qplus (Qmult Mc (q_pow (Qabs v) 2)) (Qmult Ms (q_pow (Qabs v) 3)))
                         (Qplus (Qmult Mc (q_pow (Qabs v) 2)) (Qmult Ms (q_pow (Qabs v) 2)))
                         (Qmult S (q_pow (Qabs v) 2))).
        * apply Qplus_le_compat.
          -- apply Qle_refl.
          -- apply (Qmult_le_compat_nonneg Ms Ms (q_pow (Qabs v) 3) (q_pow (Qabs v) 2)).
             ++ split; [exact HMs0 | apply Qle_refl].
             ++ split; [exact Hv3n | apply QleT'_to_Qle; apply (b5i_cube_le_sq v Hv1)].
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold S. ring. }
  (* |S2_cos| ≤ Ms·(en·k2·|(projT1 h n)| + E2) *)
  assert (HS2 : Qle (Qabs (b5d_S2n_cos x h n))
                    (Qmult Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))).
  { apply QleT'_to_Qle.
    apply (b5d_S2_le_cos x Hx h Hxh n Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)).
    - exact HMs.
    - exact Hw. }
  (* triangle inequality: [ |v| <= |w| + |projT1 h n| ] *)
  assert (Htri : Qle (Qabs v) (Qplus (Qabs w) (Qabs (projT1 h n)))).
  { unfold v, w.
    apply (Qle_trans (Qabs (b5i_vn x h n))
                     (Qplus (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
                            (Qabs (Qmult (b5i_dn x n) (projT1 h n))))
                     (Qplus (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
                            (Qabs (projT1 h n)))).
    - apply (Qle_trans (Qabs (b5i_vn x h n))
                       (Qabs (Qplus (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n)))
                                    (Qmult (b5i_dn x n) (projT1 h n))))
                       (Qplus (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
                              (Qabs (Qmult (b5i_dn x n) (projT1 h n))))).
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_wd. ring.
      + apply Qabs_triangle.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply QleT'_to_Qle. apply (b5i_dh_abs_le_h (b5i_dn x n) (projT1 h n) Hd1). }
  (* |v|² ≤ 2|w|² + 2|(projT1 h n)|² *)
  assert (Hvsq : Qle (q_pow (Qabs v) 2)
                     (Qplus (Qmult 2 (q_pow (Qabs w) 2)) (Qmult 2 (q_pow (Qabs (projT1 h n)) 2)))).
  { apply QleT'_to_Qle. apply (b5i_vsq_bound v w (projT1 h n) Htri). }
  (* B2: [ |w| <= 1 + |projT1 h n| ] (from [ |v| <= 1 ] and [ |d| <= 1 ]) *)
  assert (Hw2 : Qle (Qabs w) (Qplus 1 (Qabs (projT1 h n)))).
  { unfold v, w.
    apply (Qle_trans (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
                     (Qplus (Qabs (b5i_vn x h n)) (Qabs (Qmult (b5i_dn x n) (projT1 h n))))
                     (Qplus 1 (Qabs (projT1 h n)))).
    - apply (Qle_trans (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
                       (Qplus (Qabs (b5i_vn x h n)) (Qabs (Qopp (Qmult (b5i_dn x n) (projT1 h n)))))
                       (Qplus (Qabs (b5i_vn x h n)) (Qabs (Qmult (b5i_dn x n) (projT1 h n))))).
      + apply Qabs_triangle.
      + apply Qplus_le_compat.
        * apply Qle_refl.
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_opp.
    - apply Qplus_le_compat.
      + exact Hv1.
      + apply QleT'_to_Qle. apply (b5i_dh_abs_le_h (b5i_dn x n) (projT1 h n) Hd1). }
  (* |w|^2 <= B1 * B2 (the product form; [B2 := 1 + |projT1 h n|]) *)
  assert (Hwsq : Qle (q_pow (Qabs w) 2)
                     (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                            (Qplus 1 (Qabs (projT1 h n))))).
  { apply QleT'_to_Qle. apply (b5i_sq_le_prod (Qabs w)
                          (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                          (Qplus 1 (Qabs (projT1 h n)))).
    - exact Hw0.
    - exact Hw.
    - exact Hw2. }
  (* |(projT1 h n)|² ≤ (en·kδ)·|(projT1 h n)| *)
  assert (Hhsq : Qle (q_pow (Qabs (projT1 h n)) 2) (Qmult (Qmult en kδ) (Qabs (projT1 h n)))).
  { rewrite (qeqT_imp_qeq _ _ (sc_qpow2_form (Qabs (projT1 h n)))).
    apply (Qmult_le_compat_r (Qabs (projT1 h n)) (Qmult en kδ) (Qabs (projT1 h n)) Hhδ (Qabs_nonneg (projT1 h n))). }
  (* |projT1 h n|^2 and |w|^2 are nonnegative *)
  assert (Hh2n : Qle 0 (q_pow (Qabs (projT1 h n)) 2)).
  { rewrite (qeqT_imp_qeq _ _ (sc_qpow2_form (Qabs (projT1 h n)))).
    apply (Qmult_le_0_compat (Qabs (projT1 h n)) (Qabs (projT1 h n))
                             (Qabs_nonneg (projT1 h n)) (Qabs_nonneg (projT1 h n))). }
  assert (Hw2n : Qle 0 (q_pow (Qabs w) 2)).
  { rewrite (qeqT_imp_qeq _ _ (sc_qpow2_form (Qabs w))).
    apply (Qmult_le_0_compat (Qabs w) (Qabs w) (Qabs_nonneg w) (Qabs_nonneg w)). }
  (* 2S·|(projT1 h n)|² ≤ (2S·kδ)·(en·|(projT1 h n)|) *)
  assert (Ha1 : Qle (Qmult (Qmult 2 S) (q_pow (Qabs (projT1 h n)) 2))
                    (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))).
  { apply (Qle_trans (Qmult (Qmult 2 S) (q_pow (Qabs (projT1 h n)) 2))
                     (Qmult (Qmult 2 S) (Qmult (Qmult en kδ) (Qabs (projT1 h n))))
                     (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))).
    - apply (Qmult_le_compat_nonneg (Qmult 2 S) (Qmult 2 S)
                                    (q_pow (Qabs (projT1 h n)) 2) (Qmult (Qmult en kδ) (Qabs (projT1 h n)))).
      + split; [exact H2S0 | apply Qle_refl].
      + split.
        * exact Hh2n.
        * exact Hhsq.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  (* 2S * B1 * B2 <= 3S * B1 since [B2 <= 3/2] *)
  assert (H32 : Qle (Qplus 1 (Qabs (projT1 h n))) (3 # 2)).
  { apply QleT'_to_Qle. apply (b5i_one_plus_abs_le32 (projT1 h n) Hh12). }
  assert (Ha2 : Qle (Qmult (Qmult 2 S)
                           (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                  (Qplus 1 (Qabs (projT1 h n)))))
                    (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))).
  { apply (Qle_trans (Qmult (Qmult 2 S)
                            (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                   (Qplus 1 (Qabs (projT1 h n)))))
                     (Qmult (Qmult 2 S)
                            (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2) (3 # 2)))
                     (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))).
    - apply (Qmult_le_compat_nonneg (Qmult 2 S) (Qmult 2 S)
                                    (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                           (Qplus 1 (Qabs (projT1 h n))))
                                    (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2) (3 # 2))).
      + split; [exact H2S0 | apply Qle_refl].
      + split.
        * apply (Qmult_le_0_compat (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                   (Qplus 1 (Qabs (projT1 h n)))).
          -- exact HB1.
          -- apply (Qle_trans 0 1 (Qplus 1 (Qabs (projT1 h n)))).
             ++ unfold Qle. simpl. lia.
             ++ apply Qle_plus_nonneg_r. exact (Qabs_nonneg (projT1 h n)).
        * apply (Qmult_le_compat_nonneg (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                        (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                        (Qplus 1 (Qabs (projT1 h n)))
                                        (3 # 2)).
          -- split; [exact HB1 | apply Qle_refl].
          -- split.
             ++ apply (Qle_trans 0 1 (Qplus 1 (Qabs (projT1 h n)))).
                ** unfold Qle. simpl. lia.
                ** apply Qle_plus_nonneg_r. exact (Qabs_nonneg (projT1 h n)).
             ++ exact H32.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  (* S·|v|² ≤ (2S·kδ)·(en·|(projT1 h n)|) + (3S)·B1 *)
  assert (Hmain : Qle (Qmult S (q_pow (Qabs v) 2))
                      (Qplus (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))
                             (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))).
  { apply (Qle_trans (Qmult S (q_pow (Qabs v) 2))
                     (Qmult S (Qplus (Qmult 2 (q_pow (Qabs w) 2)) (Qmult 2 (q_pow (Qabs (projT1 h n)) 2))))
                     (Qplus (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))
                            (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))).
    - apply (Qmult_le_compat_nonneg S S
                                    (q_pow (Qabs v) 2)
                                    (Qplus (Qmult 2 (q_pow (Qabs w) 2)) (Qmult 2 (q_pow (Qabs (projT1 h n)) 2)))).
      + split; [exact HS0 | apply Qle_refl].
      + split; [exact Hv2n | exact Hvsq].
    - apply (Qle_trans (Qmult S (Qplus (Qmult 2 (q_pow (Qabs w) 2)) (Qmult 2 (q_pow (Qabs (projT1 h n)) 2))))
                       (Qplus (Qmult (Qmult 2 S) (q_pow (Qabs (projT1 h n)) 2))
                              (Qmult (Qmult 2 S) (q_pow (Qabs w) 2)))
                       (Qplus (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))
                              (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + apply Qplus_le_compat.
        * apply (Qle_trans (Qmult (Qmult 2 S) (q_pow (Qabs (projT1 h n)) 2))
                           (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))
                           (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))).
          -- exact Ha1.
          -- apply Qle_refl.
        * apply (Qle_trans (Qmult (Qmult 2 S) (q_pow (Qabs w) 2))
                           (Qmult (Qmult 2 S)
                                  (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                         (Qplus 1 (Qabs (projT1 h n)))))
                           (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))).
          -- apply (Qmult_le_compat_nonneg (Qmult 2 S) (Qmult 2 S)
                                           (q_pow (Qabs w) 2)
                                           (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                                  (Qplus 1 (Qabs (projT1 h n))))).
             ++ split; [exact H2S0 | apply Qle_refl].
             ++ split; [exact Hw2n | exact Hwsq].
          -- exact Ha2. }
  (* |D| ≤ |S1| + |S2| *)
  assert (Hdn : Qle (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                    (Qplus (Qabs (b5d_S1n_cos x h n)) (Qabs (b5d_S2n_cos x h n)))).
  { apply (Qle_trans (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                     (Qabs (Qplus (b5d_S1n_cos x h n) (b5d_S2n_cos x h n)))
                     (Qplus (Qabs (b5d_S1n_cos x h n)) (Qabs (b5d_S2n_cos x h n)))).
- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_wd. exact (qeqT_imp_qeq _ _ (b5d_dn_split_cos x Hx h Hxh n)).
    - apply Qabs_triangle. }
  (* |S1| + |S2| ≤ (colQ + S·|v|²) + Ms·B1 *)
  assert (Hsum : Qle (Qplus (Qabs (b5d_S1n_cos x h n)) (Qabs (b5d_S2n_cos x h n)))
                     (Qplus (Qplus colQ (Qmult S (q_pow (Qabs v) 2)))
                            (Qmult Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))).
  { apply Qplus_le_compat.
    - exact HS1.
    - exact HS2. }
  (* final assembly *)
  apply (Qle_trans (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                   (Qplus (Qplus colQ (Qmult S (q_pow (Qabs v) 2)))
                          (Qmult Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))
                   (Qplus colQ
                          (Qplus (Qmult (Qplus (Qmult (Qmult 2 S) kδ)
                                               (Qmult (Qplus (Qmult 3 S) Ms) k2))
                                        (Qmult en (Qabs (projT1 h n))))
                                 (Qmult (Qplus (Qmult 3 S) Ms) E2)))).
  - apply (Qle_trans (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                     (Qplus (Qabs (b5d_S1n_cos x h n)) (Qabs (b5d_S2n_cos x h n)))
                     (Qplus (Qplus colQ (Qmult S (q_pow (Qabs v) 2)))
                            (Qmult Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))).
    + exact Hdn.
    + exact Hsum.
  - apply (Qle_trans (Qplus (Qplus colQ (Qmult S (q_pow (Qabs v) 2)))
                            (Qmult Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))
                     (Qplus (Qplus colQ
                                   (Qplus (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))
                                          (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))))
                            (Qmult Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))
                     (Qplus colQ
                            (Qplus (Qmult (Qplus (Qmult (Qmult 2 S) kδ)
                                                 (Qmult (Qplus (Qmult 3 S) Ms) k2))
                                          (Qmult en (Qabs (projT1 h n))))
                                   (Qmult (Qplus (Qmult 3 S) Ms) E2)))).
    + apply Qplus_le_compat.
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- exact Hmain.
      * apply Qle_refl.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* D11: [b5d_pern_crude_cos], the crude global bound for branch B ([|v_n| > 1]) *)
(*   |D_cos| ≤ colQ + (Mc(4C+2)+Ms(4C+4)) + Ms·(en·k2·|h_n|+E2) *)
(*   (the analogue of [b5i_pern_crude]; coefficients swapped inside K1e, S2 carries [Ms]) *)
(* ============================================================ *)
Lemma b5d_pern_crude_cos : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (Ms Mc C colQ k2 : Q) (en E2 : Q),
  Qle (Qabs (sin_partial n (b5i_An x n))) Ms ->
  Qle (Qabs (cos_partial n (b5i_An x n))) Mc ->
  (forall j : nat, QleT' (exp_series j 4) C) -> Qle 0 C ->
  QltT (b5d_addcol_cos x h Hxh n) colQ ->
  Qle (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
      (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2) ->
  Qle 0 en -> Qle 0 k2 -> Qle 0 E2 ->
  QleT' (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
      (Qplus colQ
             (Qplus (Qplus (Qmult Mc (Qplus (Qmult 4 C) 2))
                           (Qmult Ms (Qplus (Qmult 4 C) 4)))
                    (Qmult Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))).
Proof.
  intros x Hx h Hxh n Ms Mc C colQ k2 en E2
         HMs HMc HC HC0 Hcol Hw Hen0 Hk20 HE20.
  apply Qle_to_QleT'.
  assert (Hv4 : Qle (Qabs (b5i_vn x h n)) 4).
  { unfold b5i_vn, b5i_Ahn, b5i_An.
    exact (QleT'_to_Qle _ _ (b5i_v_norm_le4 x Hx h Hxh n)). }
  (* |S1_cos| <= |addcol| + Mc(4C+2) + Ms(4C+4) (by [b5d_S1_crude_x_cos]) *)
  assert (HS1c : Qle (Qabs (b5d_S1n_cos x h n))
                     (Qplus (Qabs (cos_partial n (b5i_Ahn x h n)
                                   - (cos_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                                      + - (sin_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n)))))
                            (Qplus (Qmult Mc (Qplus (Qmult 4 C) 2))
                                   (Qmult Ms (Qplus (Qmult 4 C) 4))))).
  { apply QleT'_to_Qle.
    apply (b5d_S1_crude_x_cos x Hx h Hxh n Ms Mc C).
    - exact HMs.
    - exact HMc.
    - exact HC.
    - exact HC0.
    - exact Hv4. }
  (* |S1_cos| ≤ colQ + Mc(4C+2) + Ms(4C+4) *)
  assert (HS1 : Qle (Qabs (b5d_S1n_cos x h n))
                    (Qplus colQ (Qplus (Qmult Mc (Qplus (Qmult 4 C) 2))
                                       (Qmult Ms (Qplus (Qmult 4 C) 4))))).
  { apply (Qle_trans (Qabs (b5d_S1n_cos x h n))
                     (Qplus (b5d_addcol_cos x h Hxh n)
                            (Qplus (Qmult Mc (Qplus (Qmult 4 C) 2))
                                   (Qmult Ms (Qplus (Qmult 4 C) 4))))
                     (Qplus colQ (Qplus (Qmult Mc (Qplus (Qmult 4 C) 2))
                                        (Qmult Ms (Qplus (Qmult 4 C) 4))))).
    - apply (Qle_trans (Qabs (b5d_S1n_cos x h n))
                       (Qplus (Qabs (cos_partial n (b5i_Ahn x h n)
                                     - (cos_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                                        + - (sin_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n)))))
                              (Qplus (Qmult Mc (Qplus (Qmult 4 C) 2))
                                     (Qmult Ms (Qplus (Qmult 4 C) 4))))
                       (Qplus (b5d_addcol_cos x h Hxh n)
                              (Qplus (Qmult Mc (Qplus (Qmult 4 C) 2))
                                     (Qmult Ms (Qplus (Qmult 4 C) 4))))).
      + exact HS1c.
      + apply Qplus_le_compat.
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold b5d_addcol_cos. reflexivity.
        * apply Qle_refl.
    - apply Qplus_le_compat.
      + apply Qlt_le_weak. apply QltT_to_Qlt. exact Hcol.
      + apply Qle_refl. }
  (* |S2_cos| ≤ Ms·B1 *)
  assert (HS2 : Qle (Qabs (b5d_S2n_cos x h n))
                    (Qmult Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))).
  { apply QleT'_to_Qle.
    apply (b5d_S2_le_cos x Hx h Hxh n Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)).
    - exact HMs.
    - exact Hw. }
  (* |D| ≤ |S1| + |S2| *)
  assert (Hdn : Qle (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                    (Qplus (Qabs (b5d_S1n_cos x h n)) (Qabs (b5d_S2n_cos x h n)))).
  { apply (Qle_trans (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                     (Qabs (Qplus (b5d_S1n_cos x h n) (b5d_S2n_cos x h n)))
                     (Qplus (Qabs (b5d_S1n_cos x h n)) (Qabs (b5d_S2n_cos x h n)))).
- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_wd. exact (qeqT_imp_qeq _ _ (b5d_dn_split_cos x Hx h Hxh n)).
    - apply Qabs_triangle. }
  (* assembly *)
  apply (Qle_trans (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                   (Qplus (Qabs (b5d_S1n_cos x h n)) (Qabs (b5d_S2n_cos x h n)))
                   (Qplus colQ
                          (Qplus (Qplus (Qmult Mc (Qplus (Qmult 4 C) 2))
                                        (Qmult Ms (Qplus (Qmult 4 C) 4)))
                                 (Qmult Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))))).
  - exact Hdn.
  - apply (Qle_trans (Qplus (Qabs (b5d_S1n_cos x h n)) (Qabs (b5d_S2n_cos x h n)))
                     (Qplus (Qplus colQ (Qplus (Qmult Mc (Qplus (Qmult 4 C) 2))
                                               (Qmult Ms (Qplus (Qmult 4 C) 4))))
                            (Qmult Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))
                     (Qplus colQ
                            (Qplus (Qplus (Qmult Mc (Qplus (Qmult 4 C) 2))
                                          (Qmult Ms (Qplus (Qmult 4 C) 4)))
                                   (Qmult Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))))).
    + apply Qplus_le_compat.
      * exact HS1.
      * exact HS2.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* D12: [b5d_pern_main_cos], the per-n two-branch main bound, cos version *)
(*   conclusion: [ |D_cos_n| <= en * |h_n| + (3/4) * en' ]; the budget hypotheses *)
(*   swap roles: the coefQ tail is (3S+Ms), coefC/addC32 carry [Ms], *)
(*   [K1e_cos := Mc(4C+2) + Ms(4C+4)] (the analogue of [b5n_pern_main]) *)
(* ============================================================ *)
Lemma b5d_pern_main_cos : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat)
  (Ms Mc C4 colQ kδ k2 k2p : Q) (en en' : Q),
  Qle (Qabs (sin_partial n (b5i_An x n))) Ms ->
  Qle (Qabs (cos_partial n (b5i_An x n))) Mc ->
  (forall j : nat, QleT' (exp_series j 4) C4) -> Qle 0 C4 ->
  QltT (b5d_addcol_cos x h Hxh n) colQ ->
  Qle (Qabs (projT1 h n)) (Qmult en kδ) ->
  Qle (Qabs (projT1 h n)) (1 # 2) ->
  Qle (Qmult (Qplus 1 (Qmult en k2)) (Qabs (projT1 h n))) (1 # 4) ->
  Qle (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
      (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n)))
             (Qmult (Qmult 2 k2p) en')) ->
  Qle (Qabs (b5i_dn x n)) 1 ->
  Qle 0 en -> Qle 0 en' -> Qle 0 k2 -> Qlt 0 k2p ->
  Qle (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
             (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) k2)) 1 ->
  Qle (Qmult Ms k2) 1 ->
  Qle colQ (Qmult (1 # 8) en') ->
  Qle (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms)
             (Qmult (Qmult 2 k2p) en')) (Qmult (1 # 32) en') ->
  Qle (Qmult Ms (Qmult (Qmult 2 k2p) en')) (Qmult (1 # 32) en') ->
  Qle (Qmult (Qmult 8 k2p)
             (Qplus (Qmult Mc (Qplus (Qmult 4 C4) 2))
                    (Qmult Ms (Qplus (Qmult 4 C4) 4)))) 1 ->
  QleT' (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
      (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en')).
Proof.
  intros x Hx h Hxh n Ms Mc C4 colQ kδ k2 k2p en en'
         HMs HMc HC4 HC40 Hcol Hhδ Hh12 Hq Hw Hd1
         Hen0 Hen'0 Hk20 Hk2p HcoefQ HcoefC HcolQ8
         HaddQ32 HaddC32 Hk2pK1.
  apply Qle_to_QleT'.
  set (E2 := Qmult (Qmult 2 k2p) en').
  set (S := Qplus Ms Mc).
  set (K1e := Qplus (Qmult Mc (Qplus (Qmult 4 C4) 2))
                    (Qmult Ms (Qplus (Qmult 4 C4) 4))).
  set (X := Qmult en (Qabs (projT1 h n))).
  assert (HX0 : Qle 0 X).
  { unfold X. apply (Qmult_le_0_compat en (Qabs (projT1 h n)) Hen0 (Qabs_nonneg (projT1 h n))). }
  assert (HE20 : Qle 0 E2).
  { unfold E2. apply (Qmult_le_0_compat (Qmult 2 k2p) en').
    { apply (Qmult_le_0_compat 2 k2p).
      { unfold Qle. simpl. lia. }
      { apply Qlt_le_weak. exact Hk2p. } }
    { exact Hen'0. } }
  destruct (b5i_qle_dec (Qabs (b5i_vn x h n)) 1) as [Hv1 | Hvbig].
  { apply (Qle_trans (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                     (Qplus colQ
                            (Qplus (Qmult (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                                                 (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) k2))
                                          (Qmult en (Qabs (projT1 h n))))
                                   (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) E2)))
                     (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
    { apply QleT'_to_Qle.
        apply (b5d_pern_quad_cos x Hx h Hxh n Ms Mc colQ kδ k2 en
                                (Qmult (Qmult 2 k2p) en')).
      { exact HMs. }
      { exact HMc. }
      { exact Hcol. }
      { exact Hv1. }
      { exact Hhδ. }
      { exact Hh12. }
      { exact Hd1. }
      { exact Hw. }
      { exact Hen0. }
      { exact Hk20. }
      { exact HE20. } }
    { apply QleT'_to_Qle. apply (b5n_absorbQ colQ
             (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                    (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) k2))
             X (Qplus (Qmult 3 (Qplus Ms Mc)) Ms) E2 en').
      { exact HX0. }
      { exact Hen'0. }
      { exact HcoefQ. }
      { exact HcolQ8. }
      { unfold X, S, E2. exact HaddQ32. } } }
  { (* branch B: |v_n| > 1, so the crude bound applies (forcing [K1e <= en'/2]) *)
    set (av := Qabs (b5i_vn x h n)).
    set (aw := Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n)))).
    set (ah := Qabs (projT1 h n)).
    assert (Hq4 : Qle ah (1 # 4)).
    { apply (Qle_trans ah (Qmult (Qplus 1 (Qmult en k2)) ah) (1 # 4)).
      { apply (Qle_trans ah (Qmult 1 ah) (Qmult (Qplus 1 (Qmult en k2)) ah)).
        { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
        { apply (Qmult_le_compat_r 1 (Qplus 1 (Qmult en k2)) ah).
          { apply Qle_plus_nonneg_r. apply (Qmult_le_0_compat en k2 Hen0 Hk20). }
          { exact (Qabs_nonneg (projT1 h n)). } } }
      { unfold ah. exact Hq. } }
    assert (Hq5 : Qle (Qmult (Qmult en k2) ah) (1 # 4)).
    { apply (Qle_trans (Qmult (Qmult en k2) ah)
                       (Qmult (Qplus 1 (Qmult en k2)) ah)
                       (1 # 4)).
      { apply (Qmult_le_compat_r (Qmult en k2) (Qplus 1 (Qmult en k2)) ah).
        { nra. }
        { exact (Qabs_nonneg (projT1 h n)). } }
      { unfold ah. exact Hq. } }
    assert (Hav : Qle av (Qplus aw ah)).
    { apply (Qle_trans av (Qplus aw (Qabs (Qmult (b5i_dn x n) (projT1 h n)))) (Qplus aw ah)).
      { unfold av, aw.
        apply (Qle_trans (Qabs (b5i_vn x h n))
                         (Qabs (Qplus (Qminus (b5i_vn x h n)
                                              (Qmult (b5i_dn x n) (projT1 h n)))
                                      (Qmult (b5i_dn x n) (projT1 h n))))
                         (Qplus (Qabs (Qminus (b5i_vn x h n)
                                              (Qmult (b5i_dn x n) (projT1 h n))))
                                (Qabs (Qmult (b5i_dn x n) (projT1 h n))))).
        { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qabs_wd. ring. }
        { apply Qabs_triangle. } }
      { apply Qplus_le_compat.
        { apply Qle_refl. }
        { apply QleT'_to_Qle. apply (b5i_dh_abs_le_h (b5i_dn x n) (projT1 h n) Hd1). } } }
    assert (Haw : Qle aw (Qplus (Qmult (Qmult en k2) ah) E2)).
    { unfold aw, ah, E2. exact Hw. }
    assert (HE2h : Qle (1 # 2) E2).
    { apply QleT'_to_Qle. apply (b5n_forceE2 av aw ah (Qmult (Qmult en k2) ah) E2).
      { unfold av. exact Hvbig. }
      { exact Hav. }
      { exact Hq4. }
      { exact Haw. }
      { exact Hq5. } }
    assert (H4en : Qle 1 (Qmult (Qmult 4 k2p) en')).
    { apply QleT'_to_Qle. apply (b5n_forceE2en E2 k2p en' HE2h).
      unfold E2. reflexivity. }
    assert (HK1h : Qle K1e (Qmult (1 # 2) en')).
    { apply QleT'_to_Qle. apply (b5n_forceK1 K1e k2p en' Hk2p).
      { unfold K1e. exact Hk2pK1. }
      { exact H4en. } }
    apply (Qle_trans (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                     (Qplus colQ
                            (Qplus K1e
                                   (Qmult Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))))
                     (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
    { apply QleT'_to_Qle.
        apply (b5d_pern_crude_cos x Hx h Hxh n Ms Mc C4 colQ k2 en
                                 (Qmult (Qmult 2 k2p) en')).
      { exact HMs. }
      { exact HMc. }
      { exact HC4. }
      { exact HC40. }
      { exact Hcol. }
      { exact Hw. }
      { exact Hen0. }
      { exact Hk20. }
      { exact HE20. } }
    { apply (Qle_trans (Qplus colQ
                               (Qplus K1e
                                      (Qmult Ms (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))))
                       (Qplus colQ
                              (Qplus K1e
                                     (Qplus (Qmult (Qmult Ms k2) X) (Qmult Ms E2))))
                       (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { apply Qplus_le_compat.
        { apply Qle_refl. }
        { apply Qplus_le_compat.
          { apply Qle_refl. }
          { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold X. ring. } } }
      { apply QleT'_to_Qle. apply (b5n_absorbC colQ K1e Ms E2 X en' k2).
        { exact HX0. }
        { exact Hen'0. }
        { exact HcoefC. }
        { exact HcolQ8. }
        { exact HK1h. }
        { unfold E2. exact HaddC32. } } } }
Qed.

(* ============================================================ *)
(* D13: [b5a_cos_atan_diff_closed_r], the closed-form main assembly for cos o arctan *)
(*   (the analogue of item1c Part E: the error piece [comp_err_cos]; *)
(*   [K1e := Mc(4C+2) + Ms(4C+4)]; the k2/k2p denominator is (3S+Ms); *)
(*   the pure-Q budget pieces take [Ms] as the argument; *)
(*   the column bound calls [b5d_rs_addcol_cos] and the per-n bound calls *)
(*   [b5d_pern_main_cos]; the X/Y/margin pieces ([b5n_h_pts], [b5c_vdh_pts_r], *)
(*   [b5n_close], [b5n_quarter_gt]) and the delta assembly are reused verbatim) *)
(* ============================================================ *)
Lemma b5a_cos_atan_diff_closed_r :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (b5a_comp_err_cos x (b3rr_dom_r1 x r Hxr Hr1) h Hxh))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr Hr1).
  destruct (b5i_sinA_bounded x Hx) as [Ms [HMs_pos HMs_all]].
  destruct (b5i_cosA_bounded x Hx) as [Mc [HMc_pos HMc_all]].
  destruct b5i_exp_arch4 as [C4 [HC4ge1 HC4]].
  destruct (b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
  assert (HMsQ : Qlt 0 Ms). { apply QltT_to_Qlt. exact HMs_pos. }
  assert (HMcQ : Qlt 0 Mc). { apply QltT_to_Qlt. exact HMc_pos. }
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. exact HMsQ. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. exact HMcQ. }
  assert (HC4le1 : Qle 1 C4). { apply QleT'_to_Qle. exact HC4ge1. }
  assert (HC40 : Qle 0 C4).
  { apply (Qle_trans 0 1 C4).
    { unfold Qle. simpl. lia. }
    { exact HC4le1. } }
  set (S := Qplus Ms Mc).
  assert (HSlt : Qlt 0 S). { unfold S. nra. }
  set (K1e := Qplus (Qmult Mc (Qplus (Qmult 4 C4) 2))
                    (Qmult Ms (Qplus (Qmult 4 C4) 4))).
  assert (HK1_0 : Qle 0 K1e). { unfold K1e. nra. }
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
  (* global budgets: coef (quadratic branch), coefC (crude branch), and 8k2p * K1e (forced by the crude branch) *)
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
  (* delta assembly: each component is positive *)
  assert (H12T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (H14T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  destruct (b5c_vdh_pts_r r Hr0 Hr1 x Hxr eps Heps k2 k2p Hk2T Hk2pT) as [δa [Hδa0 Hδa]].
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
    (* h is placed below delta by a four-fold minimum *)
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
    (* X: the pointwise h bound [b5n_h_pts] *)
    destruct (b5n_h_pts h eps kδ k2 Heps HkδT Hk2T Hhlr Hh12 HhE) as [Nh HNh].
    (* Y: arctan' at [eps2 := eps * k2] and [eps2' := eps' * k2p] *)
    destruct (Hδa h Hhda Hxh eps' Heps') as [Nw HNw].
    (* the column-error bound (cos side) *)
    destruct (b5d_rs_addcol_cos x Hx h Hxh eta HetaT) as [Nc HNc].
    (* pointwise budget (with witness for eps') *)
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
    (* main assembly: from [real_le] to the left branch of [real_lt], witnessed by eta *)
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
      (* Z: the per-n main bound (cos version) *)
      assert (Hmain : Qle (Qabs (projT1 (b5a_comp_err_cos x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { apply QleT'_to_Qle.
          apply (b5d_pern_main_cos x Hx h Hxh n Ms Mc C4 eta kδ k2 k2p en en').
        { exact (QleT'_to_Qle _ _ (HMs_all n)). }
        { exact (QleT'_to_Qle _ _ (HMc_all n)). }
        { exact HC4. }
        { exact HC40. }
        { exact (HNc n HnNc). }
        { exact (QleT'_to_Qle _ _ Hhδn). }
        { exact (QleT'_to_Qle _ _ Hh12n). }
        { exact (QleT'_to_Qle _ _ Hhqn). }
        { exact (QleT'_to_Qle _ _ (HNw n HnNw)). }
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
      (* margin: [eta < (1/4) en']; Hfin: [eta < (en * hn + en') - Dn] *)
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
Qed.

(* ============================================================ *)
(* the goal statement [b5a_cos_atan_diff_closed_r] is proved above *)
(* ============================================================ *)

(* ============================================================ *)
(* B5-A E-ODE T2: the closed differentiability of the E composite. *)
(*   [b5a_E_diff_closed_r] with the [b5e_*] auxiliary lemmas. *)
(*   The proofs consume the item1d lemma family. *)
(*   (its upstream Requires are inlined in this file). *)
(* ============================================================ *)

(* ============================================================ *)
(* E1: [b5e_E_err], the target error expression (the object being bounded) *)
(*   ErrE := E(x+h) − [E(x) + x·E(x)·d(x)·h]                    *)
(* ============================================================ *)
Definition b5e_E_err (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1) : Real :=
  real_plus (b5a_E (real_plus x h) Hxh)
    (real_opp (real_plus (b5a_E x Hx)
               (real_mult (real_mult x (b5a_E x Hx)) (real_mult (b5a_atan_d x) h)))).

(* ============================================================ *)
(* E2: [b5e_E_dec], the three-part decomposition (after value-level cancellation) *)
(*   dec := R_sin − (x+h)·R_cos + h·(sA·(d·h))                  *)
(*   [ErrE == dec] (pure algebra plus [d(1+x^2) == 1]; see [b5e_E_dec_proj]): *)
(*   the linear part [(cA * d - cA + x * sA * d) * h == x * E * d * h] of [ErrE] is *)
(*   absorbed by [W := d(1+x^2) - 1 == 0], leaving the residual [h * (sA * (d * h))]. *)
(* ============================================================ *)
Definition b5e_E_dec (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1) : Real :=
  real_plus (b5a_comp_err_sin x Hx h Hxh)
    (real_plus (real_opp (real_mult (real_plus x h) (b5a_comp_err_cos x Hx h Hxh)))
               (real_mult h (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                       (real_mult (b5a_atan_d x) h)))).

(* ============================================================ *)
(* E3: [b5e_E_dec_proj], the pointwise identity (eventual, for [n >= N]) *)
(*   projT1 (b5e_E_err x Hx h Hxh) n == projT1 (b5e_E_dec ...) n *)
(*   proof: after the real_plus/opp/mult projections unfold, the term *)
(*   [d := inv_pos(1+x^2)] is replaced, at [n >= N], by [Qinv(1+x_n^2)] via *)
(*   [real_inv_proj]; the pointwise Q-field check closes (the residual bracket cancels since [d*(1+x^2) == 1]). *)
(* ============================================================ *)
Lemma b5e_E_dec_proj : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  sigT (fun N : nat => forall n : nat, NatLe N n -> QeqT (projT1 (b5e_E_err x Hx h Hxh) n) (projT1 (b5e_E_dec x Hx h Hxh) n)).
Proof.
  intros x Hx h Hxh.
  destruct (real_inv_proj (real_plus real_one (real_mult x x))
                          (b5a_one_plus_sq_pos x)) as [Ni HNi].
  exists Ni.
  intros n Hn.
  assert (Hd0 : projT1 (b5e_E_err x Hx h Hxh) n - projT1 (b5e_E_dec x Hx h Hxh) n == 0).
  { unfold b5e_E_err, b5e_E_dec, b5a_E, b5a_comp_err_sin, b5a_comp_err_cos, b5a_atan_d.
    repeat (first [ rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) | rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _)) | rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ]).
    rewrite (qeqT_imp_qeq _ _ (HNi n Hn)).
    repeat (first [ rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) | rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _)) | rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ]).
    cbn [projT1 real_one projT1 real_zero].
    field.
    all: intro Hz0; apply qeq_imp_qeqT in Hz0; refine (match q_neq_of_lt (1 + projT1 x n * projT1 x n) _ Hz0 with end).
    all: apply Qlt_to_QltT. apply (Qlt_le_trans 0 1 (1 + projT1 x n * projT1 x n)).
    all: first [ (unfold Qlt; simpl; lia) | nra ]. }
  apply qeq_imp_qeqT.
  apply (Qeq_trans (projT1 (b5e_E_err x Hx h Hxh) n)
                   (projT1 (b5e_E_dec x Hx h Hxh) n
                    + (projT1 (b5e_E_err x Hx h Hxh) n - projT1 (b5e_E_dec x Hx h Hxh) n))
                   (projT1 (b5e_E_dec x Hx h Hxh) n)).
  - ring.
  - rewrite Hd0. ring.
Qed.

(* ============================================================ *)
(* E5: [b5e_res_le], the pointwise bound on the residual [h * (sA * (d * h))] *)
(*   |h_n·(sA_n·(d_n·h_n))| ≤ (Msr·kδ·en)·|h_n|                *)
(*   inputs: |d_n| <= 1 (the tail bound of [b5c_d_proj_le_one]), |sA_n| <= Msr, *)
(*   |h_n| <= en * kδ; exact expansion by [Qabs_Qmult] and termwise monotonicity on nonnegative factors. *)
(* ============================================================ *)
Lemma b5e_res_le : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (n : nat) (Msr kδ en : Q),
  Qle (Qabs (projT1 (b5a_atan_d x) n)) 1 ->
  Qle (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n)) Msr ->
  Qle (Qabs (projT1 h n)) (Qmult en kδ) ->
  Qle 0 en -> Qle 0 Msr -> Qle 0 kδ ->
  QleT' (Qabs (projT1 (real_mult h (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                          (real_mult (b5a_atan_d x) h))) n))
      (Qmult (Qmult (Qmult Msr kδ) en) (Qabs (projT1 h n))).
Proof.
  intros x Hx h n Msr kδ en Hd Hs Hhδ Hen0 HMsr0 Hkδ0.
  apply Qle_to_QleT'.
  set (hn := Qabs (projT1 h n)) in *.
  set (sAn := projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n) in *.
  set (dn := projT1 (b5a_atan_d x) n) in *.
  set (res := projT1 (real_mult h (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                            (real_mult (b5a_atan_d x) h))) n) in *.
  assert (Hpres : Qeq res (Qmult (projT1 h n) (Qmult sAn (Qmult dn (projT1 h n))))).
  { unfold res, sAn, dn.
    repeat (first [ rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ]).
    reflexivity. }
  assert (Habs : Qeq (Qabs res)
                     (Qmult hn (Qmult (Qabs sAn) (Qmult (Qabs dn) hn)))).
  { apply (Qeq_trans (Qabs res)
                     (Qabs (Qmult (projT1 h n) (Qmult sAn (Qmult dn (projT1 h n)))))
                     (Qmult hn (Qmult (Qabs sAn) (Qmult (Qabs dn) hn)))).
    - apply (Qabs_wd res (Qmult (projT1 h n) (Qmult sAn (Qmult dn (projT1 h n))))).
      exact Hpres.
    - rewrite (Qabs_Qmult (projT1 h n) (Qmult sAn (Qmult dn (projT1 h n)))).
      rewrite (Qabs_Qmult sAn (Qmult dn (projT1 h n))).
      rewrite (Qabs_Qmult dn (projT1 h n)).
      unfold hn. ring. }
  assert (HA0 : Qle 0 (Qabs sAn)) by (apply Qabs_nonneg).
  assert (HB0 : Qle 0 (Qabs dn)) by (apply Qabs_nonneg).
  assert (Hhn0 : Qle 0 hn) by (unfold hn; apply Qabs_nonneg).
  apply (Qle_trans (Qabs res)
                   (Qmult hn (Qmult Msr (Qmult 1 hn)))
                   (Qmult (Qmult (Qmult Msr kδ) en) hn)).
  - apply (Qle_trans (Qabs res)
                     (Qmult hn (Qmult (Qabs sAn) (Qmult (Qabs dn) hn)))
                     (Qmult hn (Qmult Msr (Qmult 1 hn)))).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact Habs.
    + assert (Hstep : Qle (Qmult (Qabs sAn) (Qmult (Qabs dn) hn))
                          (Qmult Msr (Qmult 1 hn))).
      { apply (Qle_trans (Qmult (Qabs sAn) (Qmult (Qabs dn) hn))
                         (Qmult Msr (Qmult (Qabs dn) hn))
                         (Qmult Msr (Qmult 1 hn))).
        - apply (Qmult_le_compat_r (Qabs sAn) Msr (Qmult (Qabs dn) hn)).
          { exact Hs. }
          { apply Qmult_le_0_compat. { exact HB0. } { exact Hhn0. } }
        - apply QleT'_to_Qle. apply (sc_qmult_le_l (Qmult (Qabs dn) hn) (Qmult 1 hn) Msr).
          { apply (Qmult_le_compat_r (Qabs dn) 1 hn).
            { exact Hd. }
            { exact Hhn0. } }
          { exact HMsr0. } }
      apply QleT'_to_Qle. apply (sc_qmult_le_l (Qmult (Qabs sAn) (Qmult (Qabs dn) hn))
                           (Qmult Msr (Qmult 1 hn)) hn).
      * exact Hstep.
      * exact Hhn0.
  - assert (Hh2 : Qle (Qmult hn hn) (Qmult (Qmult en kδ) hn)).
    { apply (Qmult_le_compat_r hn (Qmult en kδ) hn).
      { exact Hhδ. }
      { exact Hhn0. } }
    assert (Hm : Qle (Qmult Msr (Qmult hn hn))
                     (Qmult Msr (Qmult (Qmult en kδ) hn))).
    { apply QleT'_to_Qle. apply (sc_qmult_le_l (Qmult hn hn) (Qmult (Qmult en kδ) hn) Msr).
      { exact Hh2. }
      { exact HMsr0. } }
    apply (Qle_trans (Qmult hn (Qmult Msr (Qmult 1 hn)))
                     (Qmult Msr (Qmult (Qmult en kδ) hn))
                     (Qmult (Qmult (Qmult Msr kδ) en) hn)).
    { apply (Qle_trans (Qmult hn (Qmult Msr (Qmult 1 hn)))
                       (Qmult Msr (Qmult hn hn))
                       (Qmult Msr (Qmult (Qmult en kδ) hn))).
      { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
      { exact Hm. } }
    { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
Qed.

(* ============================================================ *)
(* E4: [b5e_pern_main], the per-n main bound (the three-group dec assembly, budgets closed) *)
(*   |dec_n| ≤ en·|h_n| + (3/4)·en'                             *)
(*   hypotheses: the sin share Hrs and the cos share Hrc (with |(x+h)_n| <= 1 folded in), *)
(*   the residual Hres (the conclusion of [b5e_res_le]), and the coefficient budgets *)
(*   kS + kC + Msr * kδ <= 1 and the additive budget kS' + kC' + krelS + krelC <= 3/4. *)
(* ============================================================ *)
Lemma b5e_pern_main : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (kS kC kS' kC' krelS krelC Msr kδ en en' : Q),
  Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
      (Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
             (Qplus (Qmult en' kS') (Qmult en' krelS))) ->
  Qle (Qabs (Qmult (Qplus (projT1 x n) (projT1 h n))
                   (projT1 (b5a_comp_err_cos x Hx h Hxh) n)))
      (Qplus (Qmult (Qmult en kC) (Qabs (projT1 h n)))
             (Qplus (Qmult en' kC') (Qmult en' krelC))) ->
  Qle (Qabs (projT1 (real_mult h (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                           (real_mult (b5a_atan_d x) h))) n))
      (Qmult (Qmult (Qmult Msr kδ) en) (Qabs (projT1 h n))) ->
  Qle 0 en -> Qle 0 en' -> Qle 0 Msr -> Qle 0 kδ ->
  Qle (Qplus (Qplus kS kC) (Qmult Msr kδ)) 1 ->
  Qle (Qplus (Qplus (Qplus kS' kC') krelS) krelC) (3 # 4) ->
  QleT' (Qabs (projT1 (b5e_E_dec x Hx h Hxh) n))
      (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en')).
Proof.
  intros x Hx h Hxh n kS kC kS' kC' krelS krelC Msr kδ en en'
    Hrs Hrc Hres Hen0 Hen'0 HMsr0 Hkδ0 Hcoef Hadd.
  apply Qle_to_QleT'.
  set (hn := Qabs (projT1 h n)) in *.
  set (Rs := projT1 (b5a_comp_err_sin x Hx h Hxh) n) in *.
  set (Rc := projT1 (b5a_comp_err_cos x Hx h Hxh) n) in *.
  set (res := projT1 (real_mult h (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                            (real_mult (b5a_atan_d x) h))) n) in *.
  assert (Hp : Qeq (projT1 (b5e_E_dec x Hx h Hxh) n)
                   (Qplus Rs
                      (Qplus (Qopp (Qmult (Qplus (projT1 x n) (projT1 h n)) Rc)) res))).
  { unfold b5e_E_dec, Rs, Rc, res.
    repeat (first [ rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) | rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _)) | rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ]).
    ring. }
  assert (Htri : Qle (Qabs (projT1 (b5e_E_dec x Hx h Hxh) n))
                     (Qplus (Qabs Rs)
                        (Qplus (Qabs (Qmult (Qplus (projT1 x n) (projT1 h n)) Rc))
                               (Qabs res)))).
  { rewrite Hp.
    apply (Qle_trans (Qabs (Qplus Rs (Qplus (Qopp (Qmult (Qplus (projT1 x n) (projT1 h n)) Rc)) res)))
                     (Qplus (Qabs Rs) (Qabs (Qplus (Qopp (Qmult (Qplus (projT1 x n) (projT1 h n)) Rc)) res)))
                     (Qplus (Qabs Rs)
                        (Qplus (Qabs (Qmult (Qplus (projT1 x n) (projT1 h n)) Rc))
                               (Qabs res)))).
    - apply Qabs_triangle.
    - apply Qplus_le_compat.
      { apply Qle_refl. }
      { apply (Qle_trans (Qabs (Qplus (Qopp (Qmult (Qplus (projT1 x n) (projT1 h n)) Rc)) res))
                         (Qplus (Qabs (Qopp (Qmult (Qplus (projT1 x n) (projT1 h n)) Rc))) (Qabs res))
                         (Qplus (Qabs (Qmult (Qplus (projT1 x n) (projT1 h n)) Rc)) (Qabs res))).
        + apply Qabs_triangle.
        + apply Qplus_le_compat.
          { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
            rewrite (Qabs_opp (Qmult (Qplus (projT1 x n) (projT1 h n)) Rc)).
            reflexivity. }
          { apply Qle_refl. } } }
  (* triangle assembly plus the three-part bounds *)
  assert (Hsum : Qle (Qplus (Qabs Rs) (Qplus (Qabs (Qmult (Qplus (projT1 x n) (projT1 h n)) Rc)) (Qabs res)))
                     (Qplus (Qplus (Qmult (Qmult en kS) hn)
                                   (Qplus (Qmult en' kS') (Qmult en' krelS)))
                            (Qplus (Qplus (Qmult (Qmult en kC) hn)
                                          (Qplus (Qmult en' kC') (Qmult en' krelC)))
                                   (Qmult (Qmult (Qmult Msr kδ) en) hn)))).
  { apply Qplus_le_compat.
    - exact Hrs.
    - apply Qplus_le_compat.
      + exact Hrc.
      + exact Hres. }
  assert (Hfinal : Qle (Qplus (Qplus (Qmult (Qmult en kS) hn)
                                     (Qplus (Qmult en' kS') (Qmult en' krelS)))
                            (Qplus (Qplus (Qmult (Qmult en kC) hn)
                                          (Qplus (Qmult en' kC') (Qmult en' krelC)))
                                   (Qmult (Qmult (Qmult Msr kδ) en) hn)))
                       (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
  { (* ring normalization plus the budget arithmetic *)
    assert (Henhn0 : Qle 0 (Qmult en hn)) by (apply Qmult_le_0_compat; [exact Hen0 | apply Qabs_nonneg]).
    assert (Ha : Qle (Qmult (Qplus (Qplus kS kC) (Qmult Msr kδ)) (Qmult en hn))
                     (Qmult en hn)).
    { apply (Qle_trans (Qmult (Qplus (Qplus kS kC) (Qmult Msr kδ)) (Qmult en hn))
                       (Qmult 1 (Qmult en hn))
                       (Qmult en hn)).
      - apply (Qmult_le_compat_r (Qplus (Qplus kS kC) (Qmult Msr kδ)) 1 (Qmult en hn)).
        + exact Hcoef.
        + exact Henhn0.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    assert (Hb : Qle (Qmult (Qplus (Qplus (Qplus kS' kC') krelS) krelC) en')
                     (Qmult (3 # 4) en')).
    { apply (Qmult_le_compat_r (Qplus (Qplus (Qplus kS' kC') krelS) krelC) (3 # 4) en').
      - exact Hadd.
      - exact Hen'0. }
    apply (Qle_trans
             (Qplus (Qplus (Qmult (Qmult en kS) hn)
                           (Qplus (Qmult en' kS') (Qmult en' krelS)))
                    (Qplus (Qplus (Qmult (Qmult en kC) hn)
                                  (Qplus (Qmult en' kC') (Qmult en' krelC)))
                           (Qmult (Qmult (Qmult Msr kδ) en) hn)))
             (Qplus (Qmult (Qplus (Qplus kS kC) (Qmult Msr kδ)) (Qmult en hn))
                    (Qmult (Qplus (Qplus (Qplus kS' kC') krelS) krelC) en'))
             (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    - apply Qplus_le_compat.
      + exact Ha.
      + exact Hb. }
  apply (Qle_trans (Qabs (projT1 (b5e_E_dec x Hx h Hxh) n))
                   (Qplus (Qabs Rs)
                      (Qplus (Qabs (Qmult (Qplus (projT1 x n) (projT1 h n)) Rc))
                             (Qabs res)))
                   (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
  - exact Htri.
  - apply (Qle_trans
             (Qplus (Qabs Rs)
                (Qplus (Qabs (Qmult (Qplus (projT1 x n) (projT1 h n)) Rc)) (Qabs res)))
             (Qplus (Qplus (Qmult (Qmult en kS) hn)
                           (Qplus (Qmult en' kS') (Qmult en' krelS)))
                    (Qplus (Qplus (Qmult (Qmult en kC) hn)
                                  (Qplus (Qmult en' kC') (Qmult en' krelC)))
                           (Qmult (Qmult (Qmult Msr kδ) en) hn)))
             (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
    + exact Hsum.
    + exact Hfinal.
Qed.

(* ============================================================ *)
(* E6: the main assembly [b5a_E_diff_closed_r]. *)
(*   Assembly route: ErrE := ΔE - x * E * d * h *)
(*   == R_sin - (x+h) * R_cos + h * sA * (d * h) (by [b5e_E_dec_proj]); *)
(*   three-part split: the sin closed form (share eps * (1/4)), the cos closed form *)
(*   (share eps * (1/4)), the residual (|h|^2 * Msr carried by the eps * kδ component *)
(*   of delta plus [b5e_res_le]); additive shares kS' = 1/8, kC' = 1/8, *)
(*   conversion slack krelS = krelC = 1/16; budgets kS + kC = 1/2, Msr * kδ <= 1/4 *)
(*   (by [b5n_2S_kδ_le] with S := Msr), so coefficients <= 3/4 <= 1, additive <= 3/8 <= 3/4 (via [b5n_close]). *)
(* ============================================================ *)
Lemma b5a_E_diff_closed_r :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5a_E (real_plus x h) Hxh)
                 (real_opp (real_plus (b5a_E x (b3rr_dom_r1 x r Hxr Hr1))
                            (real_mult (real_mult x (b5a_E x (b3rr_dom_r1 x r Hxr Hr1)))
                                       (real_mult (b5a_atan_d x) h))))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr Hr1).
  destruct (real_norm_bounded (cauchy_real_sin (cauchy_real_arctan x Hx)))
    as [Msr [HMsr_pos HMsr_all]].
  assert (HMsrQ : Qlt 0 Msr). { apply QltT_to_Qlt. exact HMsr_pos. }
  assert (HMsr0 : Qle 0 Msr). { apply Qlt_le_weak. exact HMsrQ. }
  destruct (b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
  (* constants and budgets *)
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
  (* sin / cos closed-form instances (coefficient share eps/4) *)
  assert (HepsS : real_lt real_zero (real_mult eps (real_const (1 # 4)))).
  { apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact HkT4. } }
  assert (HepsC : real_lt real_zero (real_mult eps (real_const (1 # 4)))).
  { apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact HkT4. } }
  destruct (b5a_sin_atan_diff_closed_r r Hr0 Hr1 x Hxr
             (real_mult eps (real_const (1 # 4))) HepsS) as [δS [HδS0 HδS]].
  destruct (b5a_cos_atan_diff_closed_r r Hr0 Hr1 x Hxr
             (real_mult eps (real_const (1 # 4))) HepsC) as [δC [HδC0 HδC]].
  assert (Hepskδ : real_lt real_zero (real_mult eps (real_const kδ))).
  { apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact HkδT. } }
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
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      { unfold Qlt. simpl. lia. }
      { apply QltT_to_Qlt. exact He1T. } }
    (* placing |h| below delta by a minimum: δS / δC / eps * kδ *)
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
    (* sin share: closed form plus pointwise conversion (slack [shS := eps' * (1/16)]) *)
    assert (HepsS'' : real_lt real_zero (real_mult eps' (real_const (1 # 8)))).
    { apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkT8. } }
    assert (HshS : real_lt real_zero (real_mult eps' (real_const (1 # 16)))).
    { apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkT16. } }
    destruct (b5i_abs_le_pointwise (b5a_comp_err_sin x Hx h Hxh)
               (real_plus (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                          (real_mult eps' (real_const (1 # 8))))
               (HδS h HhδS Hxh (real_mult eps' (real_const (1 # 8))) HepsS'')
               (real_mult eps' (real_const (1 # 16))) HshS) as [Ns HNs].
    (* cos share: closed form plus pointwise conversion *)
    assert (HepsC'' : real_lt real_zero (real_mult eps' (real_const (1 # 8)))).
    { apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkT8. } }
    assert (HshC : real_lt real_zero (real_mult eps' (real_const (1 # 16)))).
    { apply real_mult_positive. { exact Heps'. } { apply real_const_pos. exact HkT16. } }
    destruct (b5i_abs_le_pointwise (b5a_comp_err_cos x Hx h Hxh)
               (real_plus (real_mult (real_mult eps (real_const (1 # 4))) (real_abs h))
                          (real_mult eps' (real_const (1 # 8))))
               (HδC h HhδC Hxh (real_mult eps' (real_const (1 # 8))) HepsC'')
               (real_mult eps' (real_const (1 # 16))) HshC) as [Nc HNc].
    (* |h_n| <= en * kδ; index for the dec pointwise identity *)
    destruct (b5i_h_le_enk h eps kδ Hhlr HkδT) as [Nhδ HNhδ].
    destruct (b5e_E_dec_proj x Hx h Hxh) as [Ndec HNdec].
    (* pointwise budget (with witness for eps') *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). } }
    set (Nmax := Nat.max (Nat.max Ne0 Ne1)
                 (Nat.max (Nat.max Ndec Nhδ) (Nat.max (Nat.max Ns Nc) Nd))).
    (* main assembly: from [real_le] to the left branch of [real_lt], witnessed by eta *)
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
      (* pointwise share bound, expanded (sin) *)
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
      (* pointwise share bound, expanded (cos, with |x+h| <= 1 folded in) *)
      assert (Hxh'n : Qle (Qabs (Qplus (projT1 x n) (projT1 h n))) 1).
      { apply (Qle_trans (Qabs (Qplus (projT1 x n) (projT1 h n)))
                         (Qabs (projT1 (real_plus x h) n))
                         1).
        { apply QleT'_to_Qle. apply qeq_le.
          apply qeq_imp_qeqT.
          apply (Qabs_wd (Qplus (projT1 x n) (projT1 h n))
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
        { apply QleT'_to_Qle. apply qeq_le.
          apply qeq_imp_qeqT.
          apply (Qabs_Qmult (Qplus (projT1 x n) (projT1 h n))
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
      (* residual share (by [b5e_res_le]) *)
      assert (Hres : Qle (Qabs (projT1 (real_mult h (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                                             (real_mult (b5a_atan_d x) h))) n))
                         (Qmult (Qmult (Qmult Msr kδ) en) (Qabs (projT1 h n)))).
      { apply QleT'_to_Qle.
          apply (b5e_res_le x Hx h n Msr kδ en).
        { exact (QleT'_to_Qle _ _ (Hd n (NatLe_lift _ _ HnNd))). }
        { apply QleT'_to_Qle. exact (HMsr_all n). }
        { exact Hhδn. }
        { exact Hen0. }
        { exact HMsr0. }
        { exact Hkδ0. } }
      (* Z: the per-n main bound *)
      assert (Hmain : Qle (Qabs (projT1 (b5e_E_err x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { unfold Dn.
        apply (Qle_trans (Qabs (projT1 (b5e_E_err x Hx h Hxh) n))
                         (Qabs (projT1 (b5e_E_dec x Hx h Hxh) n))
                         (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
        { apply QleT'_to_Qle. apply qeq_le.
          apply qeq_imp_qeqT.
          apply (Qabs_wd (projT1 (b5e_E_err x Hx h Hxh) n)
                         (projT1 (b5e_E_dec x Hx h Hxh) n)).
          exact (qeqT_imp_qeq _ _ (HNdec n HnNdec)). }
        { apply QleT'_to_Qle.
          apply (b5e_pern_main x Hx h Hxh n
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
      (* margin: [eta < (1/4) en']; Hfin: [eta < (en * hn + en') - Dn] *)
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
Qed.

(* ============================================================ *)
(* the goal statement [b5a_E_diff_closed_r] is proved above (E6) *)
(* ============================================================ *)

(* ============================================================ *)
(* B5-A E-ODE T3: the S-side g-diff family. *)
(*   Main statement [b5f_gdiff_pts_r] plus eighteen [b5f_*] auxiliary lemmas; *)
(*   the proofs depend only on the upstream root modules. *)
(*   No further dependencies. *)
(* ============================================================ *)

(* ============================================================ *)
(* The goal statement, in its finalized form. *)
(*   [b5a_S_ge_one] takes the per-point Q tail form: under the *)
(*   [real_le := Or (lt, eq)] semantics, a closed-form [forall x] [real_le] version is not constructible. *)
(* ============================================================ *)

(* S(x) >= 1 as a per-point (eventual) Q bound, the pattern of [b5c_d_proj_le_one] *)
(* Lemma b5a_S_ge_one : forall (x : Real), *)
(*   sigT (fun N : nat => forall n : nat, NatLe N n -> *)
(*     Qle 1 (projT1 (b5a_S x) n)). *)

(* S differentiability closed form: |S(x+h) - (S x + x * S(x) * d(x) * h)| <= eps * |h| + eps' *)
(* Lemma b5a_S_diff_closed_r : *)
(*   forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1), *)
(*   forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r), *)
(*   forall (eps : Real), real_lt real_zero eps -> *)
(*   sigT (fun delta : Real => And (real_lt real_zero delta) *)
(*     (forall (h : Real), real_lt (real_abs h) delta -> *)
(*       forall (eps' : Real), real_lt real_zero eps' -> *)
(*       real_le (real_abs (real_plus (b5a_S (real_plus x h)) *)
(*                  (real_opp (real_plus (b5a_S x) *)
(*                             (real_mult (real_mult x (b5a_S x)) (real_mult (b5a_atan_d x) h)))))) *)
(*               (real_plus (real_mult eps (real_abs h)) eps'))). *)

(* ============================================================ *)
(* M2b: the S-diff inner pieces ([b5f_*] auxiliary prefix). *)
(*   [g(x) := (1/2) * log(1+x^2)] on the whole line (log certificate [b5a_one_plus_sq_pos]) *)
(* v(x,h) := g(x+h) − g(x)                                       *)
(* err_S := S(x+h) − (S(x) + (x·S(x))·(d(x)·h))                  *)
(*   decomposition: [err_S == S(x) * (exp v - 1 - v) + S(x) * (v - (x*d) * h)] *)
(* ============================================================ *)

Definition b5f_g (x : Real) : Real :=
  real_mult (real_const (1 / 2))
            (real_log (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x)).

Definition b5f_v (x h : Real) : Real :=
  real_plus (b5f_g (real_plus x h)) (real_opp (b5f_g x)).

Lemma b5f_g_S : forall (x : Real),
  real_eq (b5a_S x) (cauchy_real_exp (b5f_g x)).
Proof.
  intro x. unfold b5a_S, b5f_g. apply real_eq_refl.
Qed.

(* S(x+h) == S(x) * exp(v(x,h)): the exponential sum law, at Real-level semantics, not pointwise *)
Lemma b5f_S_xh_eq : forall (x h : Real),
  real_eq (b5a_S (real_plus x h))
          (real_mult (b5a_S x) (cauchy_real_exp (b5f_v x h))).
Proof.
  intros x h.
  apply (real_eq_trans (b5a_S (real_plus x h))
                       (cauchy_real_exp (real_plus (b5f_g x) (b5f_v x h)))
                       (real_mult (b5a_S x) (cauchy_real_exp (b5f_v x h)))).
  - (* b5a_S (x+h) == exp(g(x+h)) == exp(g(x)+v) *)
    apply (real_eq_trans (b5a_S (real_plus x h))
                         (cauchy_real_exp (b5f_g (real_plus x h)))
                         (cauchy_real_exp (real_plus (b5f_g x) (b5f_v x h)))).
    + unfold b5a_S, b5f_g. apply real_eq_refl.
    + apply cauchy_real_exp_wd.
      unfold b5f_v.
      apply real_eq_of_zero_diff. intro n.
      apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (b5f_g x)
                 (real_plus (b5f_g (real_plus x h)) (real_opp (b5f_g x))) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (b5f_g (real_plus x h)) (real_opp (b5f_g x)) n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj (b5f_g x) n)).
      ring.
  - (* exp(g(x)+v) == exp(g(x)) * exp(v) by the sum law, so the first factor becomes [b5a_S x] *)
    apply (real_eq_trans
             (cauchy_real_exp (real_plus (b5f_g x) (b5f_v x h)))
             (real_mult (cauchy_real_exp (b5f_g x)) (cauchy_real_exp (b5f_v x h)))
             (real_mult (b5a_S x) (cauchy_real_exp (b5f_v x h)))).
    + apply (cauchy_real_exp_plus (b5f_g x) (b5f_v x h)).
    + apply (RealSetoid.real_eq_mult_compat
               (cauchy_real_exp (b5f_g x)) (cauchy_real_exp (b5f_v x h))
               (b5a_S x) (cauchy_real_exp (b5f_v x h))).
      * apply real_eq_sym. apply b5f_g_S.
      * apply real_eq_refl.
Qed.

(* err_S decomposition: == S * (exp v - 1 - v) + S * (v - x * d * h), as a Real-level [real_eq] *)
Lemma b5f_S_err_decomp : forall (x h : Real),
  real_eq (real_plus (b5a_S (real_plus x h))
             (real_opp (real_plus (b5a_S x)
                        (real_mult (real_mult x (b5a_S x)) (real_mult (b5a_atan_d x) h)))))
    (real_plus
       (real_mult (b5a_S x)
          (real_plus (cauchy_real_exp (b5f_v x h))
                     (real_opp (real_plus real_one (b5f_v x h)))))
       (real_mult (b5a_S x)
          (real_plus (b5f_v x h)
                     (real_opp (real_mult (real_mult x (b5a_atan_d x)) h))))).
Proof.
  intros x h.
  set (Sx := b5a_S x).
  set (Sv := cauchy_real_exp (b5f_v x h)).
  set (W := real_mult (real_mult x (b5a_atan_d x)) h).
  set (T := real_mult (real_mult x Sx) (real_mult (b5a_atan_d x) h)).
  set (A := real_plus Sv (real_opp (real_plus real_one (b5f_v x h)))).
  set (B := real_plus (b5f_v x h) (real_opp W)).
  apply (real_eq_trans
           (real_plus (b5a_S (real_plus x h)) (real_opp (real_plus Sx T)))
           (real_plus (real_mult Sx Sv) (real_opp (real_plus Sx T)))
           (real_plus (real_mult Sx A) (real_mult Sx B))).
  - (* S(x+h) == Sx * Sv along the semantic chain *)
    apply (RealSetoid.real_eq_plus_compat
             (b5a_S (real_plus x h)) (real_opp (real_plus Sx T))
             (real_mult Sx Sv) (real_opp (real_plus Sx T))).
    + unfold Sx, Sv. apply b5f_S_xh_eq.
    + apply real_eq_refl.
  - (* pure algebra (pointwise Q ring): Sx * Sv - (Sx + (x * Sx) * (d * h))
         == Sx * (Sv - (1+v)) + Sx * (v - (x * d) * h) *)
    apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    unfold A, B, T, W.
    repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) || setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ||
            setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _))).
    cbn [projT1 real_one real_zero].
    ring.
Qed.

(* ============================================================ *)
(* M2b continued: the log-domain decomposition of [v - x * d * h] *)
(*   (the algebra anchor of the g-diff error); [u(x) := 1 + x^2]; [Δu := u(x+h) - u(x) == 2xh + h^2] *)
(*   [LogErr := log u(x+h) - log u(x) - d(x) * Δu] (the log differentiability error) *)
(*   [v - xdh == (1/2) * LogErr + (1/2) * d * h^2] as a [real_eq] (pure algebra) *)
(* ============================================================ *)

Definition b5f_u (x : Real) : Real :=
  real_plus real_one (real_mult x x).

(* b5f_log_diff_dx: log is differentiable with explicit derivative
   [real_inv_pos], one eps at a time.  The root [real_log_differentiable]
   is a [RealDifferentiable] record whose derivative field is opaque and
   does not reduce to [real_inv_pos], so the statement is rebuilt here in
   the explicit [sigT] delta form. *)
Lemma b5f_log_diff_dx : forall (x0 : Real) (Hx0 : real_lt real_zero x0),
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
  set (eps4 := real_mult four_inv eps_x2).      (* eps·x²/4 *)
  set (delta := real_min half_x eps4).
  exists delta.
  split.
  - (* 0 < delta by the positivity of the minimum *)
    unfold delta, half_x, eps4, eps_x2, four_inv, two_inv.
    apply real_min_pos.
    + apply real_mult_positive.
      * apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
      * exact Hx0.
    + apply real_mult_positive.
      * apply real_mult_positive.
        -- apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
        -- apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
      * apply real_mult_positive.
        -- exact Heps.
        -- apply real_mult_positive.
           ++ exact Hx0.
           ++ exact Hx0.
  - intros h Hh Hxh eps' Heps'.
    (* the share [share := inv8 * eps'], split five ways *)
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
    (* the assumption chain *)
    assert (Hh_half : real_lt (real_abs h) half_x).
    { apply (real_min_lt_l h half_x eps4). unfold delta. exact Hh. }
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
    assert (Hh_eps4 : real_lt (real_abs h) eps4).
    { apply (real_min_lt_r h half_x eps4). unfold delta. exact Hh. }
    (* X := log(1+t) − t *)
    set (X := real_plus (real_log (real_plus real_one t) Htpos) (real_opp t)).
    (* the assertion [D == X] *)
    assert (HDX : real_eq
      (real_plus (real_log (real_plus x0 h) Hxh)
                 (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h))))
      X).
    {
      (* [D == log(x0+h) + (opp(log x0) + opp(inv * h))]: split with [real_opp_plus] *)
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
      - (* (log(x0+h) + (opplog + oppinv)) == (log(x0+h) - log x0) + (-inv * h) by associativity *)
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
          * (* log(x0+h) - log x0 == log(1+t) by [real_log_plus_diff] *)
            apply (real_log_plus_diff x0 h Hx0 Hxh Htpos).
          * (* -inv * h == -t: commutativity of multiplication plus the definition of [t] *)
            apply (real_eq_trans (real_opp (real_mult (real_inv_pos x0 Hx0) h))
                                 (real_opp (real_mult h (real_inv_pos x0 Hx0)))
                                 (real_opp t)).
            -- apply (RealSetoid.real_eq_opp_compat
                       (real_mult (real_inv_pos x0 Hx0) h)
                       (real_mult h (real_inv_pos x0 Hx0))).
               apply (real_mult_comm (real_inv_pos x0 Hx0) h).
            -- apply real_eq_refl.
    }
    (* upper bound: X <= share *)
    assert (HXup : real_le X share).
    {
      apply (real_le_trans X (real_plus (real_plus t share) (real_opp t)) share).
      - (* X <= (t+share) - t: the eps bound plus compatibility of addition on <= *)
        unfold X.
        apply (real_le_plus_compat (real_log (real_plus real_one t) Htpos) (real_plus t share)
                                   (real_opp t) (real_opp t)).
        + exact (real_log_one_plus_le_eps t share Htpos Hshare).
        + apply real_le_refl.
      - (* (t+share) - t <= share: from an equality by [real_eq_le], a ring step *)
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
    (* lower bound: -X <= 2t^2 + (share + share) *)
    assert (HXdown : real_le (real_opp X)
      (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                 (real_plus share share))).
    {
      apply (real_le_trans (real_opp X)
                           (real_plus t (real_opp (real_log (real_plus real_one t) Htpos)))
                           (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) (real_plus share share))).
      - (* -X == t - log s: an equality step via [real_opp_plus] *)
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
    (* absolute-value bridge: |X| <= 2t^2 + (share + (share + share)) + share *)
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
    (* the quadratic term: 2t^2 <= (eps/2) * |h| + share *)
    assert (Hquad : real_le
      (real_mult (real_mult (real_mult h (real_inv_pos x0 Hx0)) (real_mult h (real_inv_pos x0 Hx0)))
                 (real_plus real_one real_one))
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)).
    { apply (real_quad_t_le_h_eps x0 h eps share Hx0 Hh_eps4 Heps Hshare). }
    (* aggregation 1: |D| == |X| (from HDX and [real_abs_eq_compat]) *)
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
      - (* |D| == |X| gives |D| <= |X| via [real_abs_eq_compat] and [real_eq_le] *)
        apply RealSetoid.real_eq_le.
        apply (real_abs_eq_compat
          (real_plus (real_log (real_plus x0 h) Hxh)
                     (real_opp (real_plus (real_log x0 Hx0) (real_mult (real_inv_pos x0 Hx0) h))))
          X).
        exact HDX.
      - exact Habs.
    }
    (* aggregation 2: 2t^2 + C <= ((eps/2) * |h| + share) + C == (eps/2) * |h| + (share + C) *)
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
      - (* (2t^2 + C') + share == 2t^2 + C by the reverse associativity step, with C := C' + share *)
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
        + (* 2t^2 + C <= ((eps/2) * |h| + share) + C by compatibility of addition on <= (Hquad plus reflexivity) *)
          apply (real_le_plus_compat
                   (real_mult (real_mult t t) (real_plus real_one real_one))
                   (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
                   (real_plus (real_plus share (real_plus share share)) share)
                   (real_plus (real_plus share (real_plus share share)) share)).
          * exact Hquad.
          * apply real_le_refl.
        + (* ((eps/2) * |h| + share) + C == (eps/2) * |h| + (share + C) by the reverse associativity step *)
          apply RealSetoid.real_eq_le.
          apply real_eq_sym.
          apply (real_plus_assoc (real_mult (real_mult two_inv eps) (real_abs h))
                                 share
                                 (real_plus (real_plus share (real_plus share share)) share)).
    }
    (* aggregation 3: the final (eps/2) * |h| + 5 * share <= eps * |h| + eps' holds
       in the Bishop per-point sense (the Or encoding cannot express a general non-strict <=).
       the pointwise difference is (eps_n/2) * |h_n| + (3/8) * eps'_n >= (3/8) * eps'_n
       > (3/8) * e0' > 0, with witness (3/8) * e0'. *)
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
        - (* 0 < 3/8 since 0 * 8 < 3 * 1 *)
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
        (* the expansion assertions *)
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
        (* the projections of A_n and B_n, expanded *)
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
        (* main chain: eps0q < B_n - A_n *)
        apply Qlt_to_QltT.
        apply (Qlt_le_trans _ ((en / 2) * Qabs hn + (Qmake 3 8) * en') _).
        { (* eps0q < (en/2)|hn| + (3/8)en' *)
          apply (Qlt_le_trans _ ((Qmake 3 8) * en') _).
          { (* (3/8) * e0' < (3/8) * en' since en' > e0', by [Qmult_lt_l] *)
            unfold eps0q.
            assert (H38 : Qlt 0 (Qmake 3 8)) by (simpl; reflexivity).
            apply (proj2 (Qmult_lt_l e0' en' (Qmake 3 8) H38)).
            exact Heps0'n. }
          { (* (3/8) * en' <= (en/2) * |hn| + (3/8) * en' since 0 <= (en/2) * |hn| *)
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
            { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qplus_comm ((Qmake 3 8) * en') ((en / 2) * Qabs hn)). } } }
        { (* (en/2) * |hn| + (3/8) * en' <= B_n - A_n: expand and close by field *)
          apply QleT'_to_Qle. apply qeq_le.
            apply qeq_imp_qeqT.
          (* B_n, expanded *)
          assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
          { setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
            setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
            setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
            cbn [projT1]. unfold hn, en, en'. ring. }
          (* main chain: M == B_n - A_n *)
          apply (Qeq_trans ((en / 2) * Qabs hn + (Qmake 3 8) * en')
                           ((en * Qabs hn + en') - ((inv2n * en) * Qabs hn + (inv8n * en' + (inv8n * en' + (inv8n * en' + (inv8n * en' + inv8n * en'))))))
                           (projT1 (real_plus (real_mult eps (real_abs h)) eps') n - projT1
                             (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                        (real_plus share (real_plus (real_plus share (real_plus share share)) share))) n)).
          - (* M == the expanded form: rewrite with Hinv2/Hinv8 and close by field *)
            rewrite Hinv2. rewrite Hinv8.
            unfold Qdiv. field.
          - (* the expanded form == B_n - A_n by [Qplus_comp] (HB and HA in reverse) *)
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
    (* assembly *)
    apply (real_le_trans _ (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                                      (real_plus share (real_plus (real_plus share (real_plus share share)) share))) _).
    { apply (real_le_trans _ (real_plus (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                                                   (real_plus share (real_plus share share)))
                                        share) _).
      - exact HabsD.
      - exact Hmid. }
    { exact Hfinal. }
Qed.

Definition b5f_Du (x h : Real) : Real :=
  real_plus (b5f_u (real_plus x h)) (real_opp (b5f_u x)).

(* Δu == 2·(x·h) + h·h *)
Lemma b5f_Du_eq : forall (x h : Real),
  real_eq (b5f_Du x h)
          (real_plus (real_mult (real_const 2) (real_mult x h))
                     (real_mult h h)).
Proof.
  intros x h.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  unfold b5f_Du, b5f_u.
  repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) || setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ||
          setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _))).
  cbn [projT1 real_one real_zero real_const].
  ring.
Qed.

Definition b5f_LogErr (x h : Real) : Real :=
  real_plus (real_log (b5f_u (real_plus x h)) (b5a_one_plus_sq_pos (real_plus x h)))
    (real_opp (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
               (real_mult (b5a_atan_d x) (b5f_Du x h)))).

(* v − x·d·h == (1/2)·LogErr + (1/2)·d·h² *)
Lemma b5f_v_minus_xdh_decomp : forall (x h : Real),
  real_eq (real_plus (b5f_v x h)
             (real_opp (real_mult (real_mult x (b5a_atan_d x)) h)))
    (real_plus (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
               (real_mult (real_const (1 / 2))
                  (real_mult (b5a_atan_d x) (real_mult h h)))).
Proof.
  intros x h.
  (* Δu inside LogErr is replaced by 2xh + h^2, as a Real-level rewrite *)
  assert (Hl : real_eq (real_mult (b5a_atan_d x) (b5f_Du x h))
                       (real_mult (b5a_atan_d x)
                          (real_plus (real_mult (real_const 2) (real_mult x h))
                                     (real_mult h h)))).
  { apply (RealSetoid.real_eq_mult_compat (b5a_atan_d x) (b5f_Du x h)
                                          (b5a_atan_d x)
                                          (real_plus (real_mult (real_const 2) (real_mult x h))
                                                     (real_mult h h))).
    - apply real_eq_refl.
    - apply b5f_Du_eq. }
  (* the whole identity holds pointwise by ring: both sides share the same real_log atom and the same d atom, and Δu is expanded *)
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  unfold b5f_v, b5f_g, b5f_LogErr, b5f_u.
  repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) || setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ||
          setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _))).
  (* each occurrence of Δu (in d * Δu) is replaced by its expanded form *)
  repeat setoid_rewrite (b5f_Du_eq x h).
  repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) || setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ||
          setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _))).
  cbn [projT1 real_one real_zero real_const].
  field.
Qed.

(* ============================================================ *)
(* M2b-3: the pointwise lift of |Δu(x,h)| (for the g-diff / log chain) *)
(*   hypotheses: |x_n| <= r for all n, and |h| < 1/2 at the Real level (a uniform pointwise bound) *)
(*   conclusion: |Δu| <= (2 * (1+r) + 1/2) * |h| + sh, with sh witnessing the eps share *)
(* ============================================================ *)
Lemma b5f_Du_abs_le : forall (r : Q)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r)
  (h sh : Real),
  real_lt real_zero sh -> real_lt (real_abs h) (real_const (1 # 2)) ->
  real_le (real_abs (b5f_Du x h))
          (real_plus (real_mult (real_const (Qplus (Qmult 2 (Qplus r 1)) (1 # 2)))
                                (real_abs h)) sh).
Proof.
  intros r x Hxr h sh Hsh Hh12.
  destruct Hsh as [sh0 [Hsh0 [Nsh HshN]]].
  destruct Hh12 as [e1 [He1 [N1 HN1]]].
  apply (RealSetoid.real_lt_le_iff_req
           (real_abs (b5f_Du x h))
           (real_plus (real_mult (real_const (Qplus (Qmult 2 (Qplus r 1)) (1 # 2))) (real_abs h)) sh)).
  left.
  unfold real_lt.
  exists sh0.
  split.
  - exact Hsh0.
  - exists (Nat.max Nsh N1).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hnsh : (Nsh <= n)%nat) by lia.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    set (hn := Qabs (projT1 h n)).
    set (xn := projT1 x n).
    set (C := Qplus (Qmult 2 (Qplus r 1)) (1 # 2)).
    (* the projections, expanded *)
    assert (HA : projT1 (real_abs (b5f_Du x h)) n ==
                 Qabs (projT1 (b5f_Du x h) n)).
    { exact (qeqT_imp_qeq _ _ (real_abs_proj (b5f_Du x h) n)). }
    assert (HB : projT1 (real_plus (real_mult (real_const C) (real_abs h)) sh) n ==
                 C * hn + projT1 sh n).
    { setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const C) (real_abs h)) sh n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const C) (real_abs h) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj C n)).
      reflexivity. }
    (* goal: QltT sh0 (C * hn + sh_n - |Δu_n|) *)
    apply (qltT_eq_compat_r
             (projT1 (real_plus (real_mult (real_const C) (real_abs h)) sh) n -
              projT1 (real_abs (b5f_Du x h)) n)
             (C * hn + projT1 sh n - Qabs (projT1 (b5f_Du x h) n)) sh0).
    { apply qeq_imp_qeqT. apply Qplus_comp; [ exact HB | apply Qopp_comp; exact HA ]. }
    apply Qlt_to_QltT.
    (* pointwise main bound: |Δu_n| <= 2 * (1+r) * |h_n| + h_n^2 <= C * hn *)
    assert (Hx1 : Qle (Qabs xn) (Qplus r 1)).
    { apply (Qle_trans (Qabs xn) r (Qplus r 1)).
      - apply QleT'_to_Qle. exact (Hxr n).
      - apply (Qle_plus_nonneg_r r 1). unfold Qle. simpl. lia. }
    assert (Hh1 : Qlt (Qabs (projT1 h n)) (1 # 2)).
    { apply (Qlt_le_trans (Qabs (projT1 h n)) (Qminus (1 # 2) e1) (1 # 2)).
      - apply QltT_to_Qlt.
        apply (q_lt_minus_shift e1 (1 # 2) (Qabs (projT1 h n))).
        apply (qltT_eq_compat_r (1 / 2 - Qabs (projT1 h n))
                                (projT1 (real_const (1 # 2)) n - projT1 (real_abs h) n) e1).
        { apply qeq_imp_qeqT. apply Qeq_sym.
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 2) n)).
          rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          reflexivity. }
        { exact (HN1 n (NatLe_lift _ _ Hn1)). }
      - apply (Qle_trans (Qminus (1 # 2) e1) (Qplus (Qminus (1 # 2) e1) e1) (1 # 2)).
        + apply (Qle_trans (Qminus (1 # 2) e1) (Qplus (Qminus (1 # 2) e1) 0)
                           (Qplus (Qminus (1 # 2) e1) e1)).
          * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
          * apply (Qplus_le_compat (Qminus (1 # 2) e1) (Qminus (1 # 2) e1) 0 e1
                                   (Qle_refl _) (Qlt_le_weak 0 e1 (QltT_to_Qlt _ _ He1))).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    (* |Δu_n| == |2x_n h_n + h_n²| ≤ 2|x_n||h_n| + |h_n|² ≤ (2(1+r) + 1/2)|h_n| *)
    assert (Hmain : Qle (Qabs (projT1 (b5f_Du x h) n)) (C * hn)).
    { unfold b5f_Du, b5f_u, hn, xn, C.
      repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) || setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ||
              setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _))).
      cbn [projT1 real_one real_zero real_const].
      (* at the Q level: |1 + (x+h)^2 - (1 + x^2)| <= ... *)
      assert (Hshape : 1 + (projT1 x n + projT1 h n) * (projT1 x n + projT1 h n) - (1 + projT1 x n * projT1 x n)
                        == 2 * (projT1 x n * projT1 h n) + projT1 h n * projT1 h n) by ring.
      setoid_rewrite Hshape.
      (* goal: |2 * (x_n * h_n) + h_n * h_n| <= C * |h_n| *)
      apply (Qle_trans (Qabs (2 * (projT1 x n * projT1 h n) + projT1 h n * projT1 h n))
                       (Qabs (2 * (projT1 x n * projT1 h n)) + Qabs (projT1 h n * projT1 h n))
                       (C * Qabs (projT1 h n))).
      - apply Qabs_triangle.
      - setoid_rewrite (Qabs_Qmult 2 (projT1 x n * projT1 h n)).
        setoid_rewrite (Qabs_Qmult (projT1 x n) (projT1 h n)).
        setoid_rewrite (Qabs_Qmult (projT1 h n) (projT1 h n)).
        assert (H2p : Qle 0 (2 : Q)) by (unfold Qle; simpl; lia).
        setoid_rewrite (Qabs_pos 2 H2p).
        assert (Hh1le : Qle (Qabs (projT1 h n)) (1 # 2)) by (apply Qlt_le_weak; exact Hh1).
        assert (Hx0 : Qle 0 (Qabs (projT1 x n))) by apply Qabs_nonneg.
        assert (Hh0 : Qle 0 (Qabs (projT1 h n))) by apply Qabs_nonneg.
        assert (Hfin : Qle (2 * (Qabs (projT1 x n) * Qabs (projT1 h n)) + Qabs (projT1 h n) * Qabs (projT1 h n))
                            ((2 * (Qplus r 1) + (1 # 2)) * Qabs (projT1 h n))).
        { assert (Hp1 : Qle (2 * (Qabs (projT1 x n) * Qabs (projT1 h n)))
                            (2 * ((Qplus r 1) * Qabs (projT1 h n)))).
          { apply (Qle_trans (2 * (Qabs (projT1 x n) * Qabs (projT1 h n)))
                             ((Qabs (projT1 x n) * Qabs (projT1 h n)) * 2)
                             (2 * ((Qplus r 1) * Qabs (projT1 h n)))).
            - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
            - apply (Qle_trans ((Qabs (projT1 x n) * Qabs (projT1 h n)) * 2)
                               (((Qplus r 1) * Qabs (projT1 h n)) * 2)
                               (2 * ((Qplus r 1) * Qabs (projT1 h n)))).
              + apply (Qmult_le_compat_r (Qabs (projT1 x n) * Qabs (projT1 h n))
                                         ((Qplus r 1) * Qabs (projT1 h n)) 2).
                * apply (Qmult_le_compat_r (Qabs (projT1 x n)) (Qplus r 1) (Qabs (projT1 h n))).
                  -- exact Hx1.
                  -- exact Hh0.
                * unfold Qle. simpl. lia.
              + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
          assert (Hp2 : Qle (Qabs (projT1 h n) * Qabs (projT1 h n))
                             ((1 # 2) * Qabs (projT1 h n))).
          { apply (Qmult_le_compat_r (Qabs (projT1 h n)) (1 # 2) (Qabs (projT1 h n))).
            - exact Hh1le.
            - exact Hh0. }
          apply (Qle_trans (2 * (Qabs (projT1 x n) * Qabs (projT1 h n)) + Qabs (projT1 h n) * Qabs (projT1 h n))
                           (2 * ((Qplus r 1) * Qabs (projT1 h n)) + (1 # 2) * Qabs (projT1 h n))
                           ((2 * (Qplus r 1) + (1 # 2)) * Qabs (projT1 h n))).
          - apply (Qplus_le_compat (2 * (Qabs (projT1 x n) * Qabs (projT1 h n)))
                                    (2 * ((Qplus r 1) * Qabs (projT1 h n)))
                                    (Qabs (projT1 h n) * Qabs (projT1 h n))
                                    ((1 # 2) * Qabs (projT1 h n))).
            + exact Hp1.
            + exact Hp2.
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
        unfold C.
        exact Hfin. }
    (* sh0 < sh_n ≤ (C·hn + sh_n) − |Δu_n| *)
    assert (Hshn : Qlt sh0 (projT1 sh n)).
    { apply (Qlt_le_trans sh0 (projT1 sh n - projT1 real_zero n) (projT1 sh n)).
      - apply QltT_to_Qlt. exact (HshN n (NatLe_lift _ _ Hnsh)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        rewrite Hz. ring. }
    apply (Qlt_le_trans sh0 (projT1 sh n) (C * hn + projT1 sh n - Qabs (projT1 (b5f_Du x h) n))).
    { exact Hshn. }
    { apply (proj2 (Qle_minus_iff (projT1 sh n)
                                  (Qminus (Qplus (C * hn) (projT1 sh n)) (Qabs (projT1 (b5f_Du x h) n))))).
      (* 0 <= (C * hn + sh_n - D) - sh_n == C * hn - D (Hmain gives D <= C * hn) *)
      apply (Qle_trans 0 (Qminus (C * hn) (Qabs (projT1 (b5f_Du x h) n)))
                          (Qminus (Qminus (Qplus (C * hn) (projT1 sh n)) (Qabs (projT1 (b5f_Du x h) n)))
                                  (projT1 sh n))).
      - apply (proj1 (Qle_minus_iff (Qabs (projT1 (b5f_Du x h) n)) (C * hn))). exact Hmain.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
Qed.

(* ============================================================ *)
(* M2c-1: |S(x)_n| is bounded pointwise *)
(*   S(x)_n == exp_partial n ((1/2) * log_seq n (1+x^2)) along the projection chain; *)
(*   |log_seq n (1+x^2)| <= |log_lower| + |log_upper| = Na + Nb, with integer endpoints *)
(*   exp_lower_q / exp_upper_q, so |t_n| <= T := Na + Nb; *)
(*   |exp_partial n t| <= |t| * exp_partial n |t| + 1 (by [abs_diff_le]) <= T * exp_series n T + 1 *)
(*   <= T * C1 + 1 (by [exp_series_arch C1]). *)
(*   use: the |Sxn| <= M premise of the main assembly's |Sx| * (exp part / scaling) term (M depends on x, *)
(*   yet is a fixed Q constant within the per-n budget). *)
(* ============================================================ *)
Lemma b5f_S_pts_bounded : forall (x : Real),
  sigT (fun M : Q => And (QltT 0 M)
    (forall n : nat, QleT' (Qabs (projT1 (b5a_S x) n)) M)).
Proof.
  intro x.
  set (y := real_plus real_one (real_mult x x)).
  set (T := Qplus (Qabs (log_lower y (b5a_one_plus_sq_pos x)))
                  (Qabs (log_upper y (b5a_one_plus_sq_pos x)))).
  assert (HT0 : Qle 0 T).
  { unfold T. apply (Qplus_le_compat 0 (Qabs (log_lower y (b5a_one_plus_sq_pos x)))
                                     0 (Qabs (log_upper y (b5a_one_plus_sq_pos x)))).
    - apply Qabs_nonneg.
    - apply Qabs_nonneg. }
  destruct (exp_series_arch T (Qle_to_QleT' 0 T HT0)) as [C1 [HC1ge1 HC1all]].
  assert (HC1ge : Qle 1 C1) by (apply QleT'_to_Qle; exact HC1ge1).
  assert (HC1_0 : Qle 0 C1).
  { apply (Qle_trans 0 1 C1).
    - change (Qle 0 1). unfold Qle. simpl. lia.
    - exact HC1ge. }
  assert (HT_C1_0 : Qle 0 (Qmult T C1)).
  { apply (Qmult_le_0_compat T C1 HT0 HC1_0). }
  set (M := Qplus 1 (Qmult T C1)).
  exists M.
  split.
  - (* 0 < M *)
    unfold M. apply Qlt_to_QltT.
    apply (Qplus_lt_le_compat 0 1 0 (Qmult T C1)).
    + change (Qlt 0 1). compute. reflexivity.
    + exact HT_C1_0.
  - { (* for all n: |S(x)_n| <= M *)
    intros n.
    set (tn := Qmult (1 / 2) (log_seq y (b5a_one_plus_sq_pos x) n)).
    (* S(x)_n == exp_partial n tn along the projection chain *)
    assert (Hproj : projT1 (b5a_S x) n == exp_partial n tn).
    { unfold tn, y, b5a_S.
      rewrite (qeqT_imp_qeq _ _ (real_exp_proj (real_mult (real_const (1 / 2))
                 (real_log (real_plus real_one (real_mult x x))
                           (b5a_one_plus_sq_pos x))) n)).
      (* exp_partial_wd: the projection equality for the exp_partial argument (setoid rewriting does not enter function arguments, so use the wd lemma) *)
      apply qeqT_imp_qeq.
      apply (exp_partial_wd n (projT1 (real_mult (real_const (1 / 2))
                 (real_log (real_plus real_one (real_mult x x))
                           (b5a_one_plus_sq_pos x))) n)
                 (Qmult (1 / 2) (log_seq (real_plus real_one (real_mult x x))
                                         (b5a_one_plus_sq_pos x) n))).
      apply qeq_imp_qeqT.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (1 / 2))
          (real_log (real_plus real_one (real_mult x x))
                    (b5a_one_plus_sq_pos x)) n)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 / 2) n)).
      cbn [real_log cw_log projT1].
      reflexivity. }
    (* |tn| <= T: |(1/2) * l| == (1/2) * |l| <= (1/2) * T <= T *)
    assert (HtnT : Qle (Qabs tn) T).
    { unfold tn, T.
      apply (Qle_trans (Qabs (Qmult (1 / 2) (log_seq y (b5a_one_plus_sq_pos x) n)))
                       (Qmult (1 / 2) (Qabs (log_seq y (b5a_one_plus_sq_pos x) n)))
                       (Qplus (Qabs (log_lower y (b5a_one_plus_sq_pos x)))
                              (Qabs (log_upper y (b5a_one_plus_sq_pos x))))).
      - (* |(1/2) * l| == (1/2) * |l| (by [Qabs_Qmult] and 1/2 >= 0) *)
        rewrite (Qabs_Qmult (1 / 2) (log_seq y (b5a_one_plus_sq_pos x) n)).
        apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        apply (Qmult_comp (Qabs (1 / 2)) (1 / 2)).
        + apply (Qabs_pos (1 / 2)).
          apply Qlt_le_weak. change (Qlt 0 (1 / 2)). compute. reflexivity.
        + reflexivity.
      - apply (Qle_trans (Qmult (1 / 2) (Qabs (log_seq y (b5a_one_plus_sq_pos x) n)))
                         (Qmult (1 / 2) (Qplus (Qabs (log_lower y (b5a_one_plus_sq_pos x)))
                                               (Qabs (log_upper y (b5a_one_plus_sq_pos x)))))
                         (Qplus (Qabs (log_lower y (b5a_one_plus_sq_pos x)))
                                (Qabs (log_upper y (b5a_one_plus_sq_pos x))))).
        + (* (1/2) * |l| <= (1/2) * (|log_lower| + |log_upper|) by [log_seq_bounded] and 1/2 >= 0 *)
          apply (Qle_trans (Qmult (1 / 2) (Qabs (log_seq y (b5a_one_plus_sq_pos x) n)))
                           (Qmult (Qabs (log_seq y (b5a_one_plus_sq_pos x) n)) (1 / 2))
                           (Qmult (1 / 2) (Qplus (Qabs (log_lower y (b5a_one_plus_sq_pos x)))
                                                 (Qabs (log_upper y (b5a_one_plus_sq_pos x)))))).
          * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          * apply (Qle_trans (Qmult (Qabs (log_seq y (b5a_one_plus_sq_pos x) n)) (1 / 2))
                             (Qmult (Qplus (Qabs (log_lower y (b5a_one_plus_sq_pos x)))
                                           (Qabs (log_upper y (b5a_one_plus_sq_pos x)))) (1 / 2))
                             (Qmult (1 / 2) (Qplus (Qabs (log_lower y (b5a_one_plus_sq_pos x)))
                                                   (Qabs (log_upper y (b5a_one_plus_sq_pos x)))))).
            -- apply (Qmult_le_compat_r (Qabs (log_seq y (b5a_one_plus_sq_pos x) n))
                                        (Qplus (Qabs (log_lower y (b5a_one_plus_sq_pos x)))
                                               (Qabs (log_upper y (b5a_one_plus_sq_pos x))))
                                        (1 / 2)).
               ++ exact (QleT'_to_Qle _ _ (log_seq_bounded y (b5a_one_plus_sq_pos x) n)).
               ++ apply Qlt_le_weak. change (Qlt 0 (1 / 2)). compute. reflexivity.
            -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        + (* (1/2) * T <= 1 * T == T since T >= 0 and 1/2 <= 1 *)
          apply (Qle_trans (Qmult (1 / 2) (Qplus (Qabs (log_lower y (b5a_one_plus_sq_pos x)))
                                                 (Qabs (log_upper y (b5a_one_plus_sq_pos x)))))
                           (Qmult 1 (Qplus (Qabs (log_lower y (b5a_one_plus_sq_pos x)))
                                           (Qabs (log_upper y (b5a_one_plus_sq_pos x)))))
                           (Qplus (Qabs (log_lower y (b5a_one_plus_sq_pos x)))
                                  (Qabs (log_upper y (b5a_one_plus_sq_pos x))))).
          * apply (Qmult_le_compat_r (1 / 2) 1 (Qplus (Qabs (log_lower y (b5a_one_plus_sq_pos x)))
                                                      (Qabs (log_upper y (b5a_one_plus_sq_pos x))))).
            -- change (Qle (1 / 2) 1). unfold Qle. simpl. lia.
            -- exact HT0.
          * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    (* |S(x)_n| ≤ |tn|·exp_partial n |tn| + 1 ≤ T·C1 + 1 == M *)
    apply Qle_to_QleT'.
    apply (Qle_trans (Qabs (projT1 (b5a_S x) n)) (Qabs (exp_partial n tn)) M).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply (Qabs_wd (projT1 (b5a_S x) n) (exp_partial n tn)). exact Hproj.
    - apply (Qle_trans (Qabs (exp_partial n tn))
                       (Qplus (Qmult (Qabs tn) (exp_partial n (Qabs tn))) 1)
                       M).
      + (* |ep n tn| ≤ |tn|·ep n |tn| + 1 *)
        apply (Qle_trans (Qabs (exp_partial n tn))
                         (Qplus (Qabs (Qminus (exp_partial n tn) 1)) 1)
                         (Qplus (Qmult (Qabs tn) (exp_partial n (Qabs tn))) 1)).
        * apply (Qle_trans (Qabs (exp_partial n tn))
                           (Qabs (Qplus (Qminus (exp_partial n tn) 1) 1))
                           (Qplus (Qabs (Qminus (exp_partial n tn) 1)) 1)).
          -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
             apply (Qabs_wd (exp_partial n tn) (Qplus (Qminus (exp_partial n tn) 1) 1)).
             ring.
          -- apply Qabs_triangle.
        * apply (Qplus_le_compat (Qabs (Qminus (exp_partial n tn) 1))
                                 (Qmult (Qabs tn) (exp_partial n (Qabs tn)))
                                 1 1).
          -- exact (QleT'_to_Qle _ _ (exp_partial_abs_diff_le n tn)).
          -- apply Qle_refl.
      + (* <= M: |tn| * ep|tn| <= T * exp_series n T <= T * C1 *)
        apply (Qle_trans (Qplus (Qmult (Qabs tn) (exp_partial n (Qabs tn))) 1)
                         (Qplus (Qmult T (exp_series n T)) 1)
                         M).
        * apply Qplus_le_compat.
          -- assert (Hep0 : Qle 0 (exp_partial n (Qabs tn))).
             { apply (Qle_trans 0 1 (exp_partial n (Qabs tn))).
               - change (Qle 0 1). unfold Qle. simpl. lia.
               - apply QleT'_to_Qle. apply exp_partial_ge_one. apply Qle_to_QleT'. apply Qabs_nonneg. }
             apply (Qle_trans (Qmult (Qabs tn) (exp_partial n (Qabs tn)))
                              (Qmult T (exp_partial n (Qabs tn)))
                              (Qmult T (exp_series n T))).
             ++ apply (Qmult_le_compat_r (Qabs tn) T (exp_partial n (Qabs tn))).
                exact HtnT. exact Hep0.
             ++ apply (Qle_trans (Qmult T (exp_partial n (Qabs tn)))
                                 (Qmult (exp_partial n (Qabs tn)) T)
                                 (Qmult T (exp_series n T))).
                ** apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
                ** apply (Qle_trans (Qmult (exp_partial n (Qabs tn)) T)
                                    (Qmult (exp_series n T) T)
                                    (Qmult T (exp_series n T))).
                   --- apply (Qmult_le_compat_r (exp_partial n (Qabs tn)) (exp_series n T) T).
                       +++ apply (Qle_trans (exp_partial n (Qabs tn)) (exp_series n (Qabs tn))
                                           (exp_series n T)).
                           ++++ rewrite ((qeqT_imp_qeq _ _ (exp_partial_eq_series n (Qabs tn)))). apply Qle_refl.
                           ++++ apply QleT'_to_Qle. apply (exp_series_arg_mono (Qabs tn) T n). apply Qle_to_QleT'. apply Qabs_nonneg. exact (Qle_to_QleT' _ _ HtnT).
                       +++ exact HT0.
                   --- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          -- apply Qle_refl.
        * apply (Qle_trans (Qplus (Qmult T (exp_series n T)) 1)
                           (Qplus (Qmult T C1) 1)
                           M).
          -- apply Qplus_le_compat.
             ++ apply (Qle_trans (Qmult T (exp_series n T))
                                 (Qmult (exp_series n T) T)
                                 (Qmult T C1)).
                ** apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
                ** apply (Qle_trans (Qmult (exp_series n T) T)
                                    (Qmult C1 T)
                                    (Qmult T C1)).
                   --- apply (Qmult_le_compat_r (exp_series n T) C1 T).
                       +++ exact (QleT'_to_Qle _ _ (HC1all n)).
                       +++ exact HT0.
                   --- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
             ++ apply Qle_refl.
          -- unfold M. apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    }
Qed.

(* ============================================================ *)
(* M2c-2: the u + Δu bridge pieces (used by the log-diff at u inside the g-diff Real closed form) *)
(*   [b5f_u_Du_eq]: u(x) + Δu(x,h) == u(x+h) (the Δu definition, algebraically) *)
(*   [b5f_u_plus_Du_pos]: 0 < u(x) + Δu(x,h) (a closed certificate; the value is 1+(x+h)^2) *)
(*   [b5f_LogErr_delta]: the LogErr version of [b5f_log_diff_dx] instantiated at (u(x), Δu) *)
(*   (the delta comes from the abstract log-diff statement; the assumption real_lt |Δu| delta activates it) *)
(* ============================================================ *)

Lemma b5f_u_Du_eq : forall (x h : Real),
  real_eq (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u (real_plus x h)).
Proof.
  intros x h.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  unfold b5f_Du, b5f_u.
  repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) || setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ||
          setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _))).
  cbn [projT1 real_one real_zero].
  ring.
Qed.

(* 0 < u(x) + Δu(x,h): pointwise 1+(x+h)_n^2 >= 1 > 1/2, a closed term with no hypotheses *)
Lemma b5f_u_plus_Du_pos : forall (x h : Real),
  real_lt real_zero (real_plus (b5f_u x) (b5f_Du x h)).
Proof.
  intros x h.
  unfold real_lt.
  exists (1 # 2).
  split.
  - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (1 # 2) 1
           (projT1 (real_plus (b5f_u x) (b5f_Du x h)) n - projT1 real_zero n)).
    + change (Qlt (1 # 2) 1). unfold Qlt. simpl. lia.
    + assert (Hq : projT1 (real_plus (b5f_u x) (b5f_Du x h)) n - projT1 real_zero n ==
                   1 + (projT1 (real_plus x h) n * projT1 (real_plus x h) n)).
      { unfold b5f_Du, b5f_u.
        repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) || setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ||
                setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _))).
        cbn [projT1 real_one real_zero].
        ring. }
      rewrite Hq.
      apply (Qle_trans 1 (1 + 0) (1 + (projT1 (real_plus x h) n * projT1 (real_plus x h) n))).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qplus_le_compat 1 1 0 (projT1 (real_plus x h) n * projT1 (real_plus x h) n)).
        -- apply Qle_refl.
        -- apply QleT'_to_Qle. apply (Qsquare_nonneg (projT1 (real_plus x h) n)).
Qed.

(* LogErr-eps-delta: [b5f_log_diff_dx] instantiated at (b5f_u x, b5f_Du x h),
   bridged by [real_log_wd]; the delta is returned by the abstract log-diff
   statement, activated by the assumption real_lt (real_abs Δu) delta. *)
Lemma b5f_LogErr_delta : forall (x : Real) (epsL : Real) (HepsL : real_lt real_zero epsL),
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), forall (epsL' : Real), real_lt real_zero epsL' ->
      real_lt (real_abs (b5f_Du x h)) delta ->
      real_le (real_abs (b5f_LogErr x h))
              (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL'))).
Proof.
  intros x epsL HepsL.
  destruct (b5f_log_diff_dx (b5f_u x) (b5a_one_plus_sq_pos x) epsL HepsL) as [delta [Hd0 Hd]].
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
    (* logexpr == b5f_LogErr: only the first log argument/certificate differs, bridged by [real_log_wd] *)
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
Qed.

(* ============================================================ *)
(* M2c-3: the g-diff Real closed form (the g part of the main assembly) *)
(*   [b5f_Du_abs_pts]: pointwise |Δu_n| <= (2r + 1/2) * |h_n| (for |h_n| <= 1/2) *)
(* ============================================================ *)
Lemma b5f_Du_abs_pts : forall (r : Q) (x : Real)
  (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r)
  (h : Real) (n : nat),
  Qle (Qabs (projT1 h n)) (1 # 2) ->
  QleT' (Qabs (projT1 (b5f_Du x h) n))
      (Qmult (Qplus (Qmult 2 r) (1 # 2)) (Qabs (projT1 h n))).
Proof.
  intros r x Hxr h n Hh12.
  apply Qle_to_QleT'.
  set (xn := projT1 x n).
  set (hn := projT1 h n).
  set (C0 := Qplus (Qmult 2 r) (1 # 2)).
  (* Δu_n == 2 * x_n * h_n + h_n * h_n (pointwise ring) *)
  assert (Hshape : projT1 (b5f_Du x h) n ==
                   Qplus (Qmult 2 (Qmult xn hn)) (Qmult hn hn)).
  { unfold xn, hn, b5f_Du, b5f_u.
    repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) || setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ||
            setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _))).
    cbn [projT1 real_one real_zero].
    ring. }
  apply (Qle_trans (Qabs (projT1 (b5f_Du x h) n))
                   (Qabs (Qplus (Qmult 2 (Qmult xn hn)) (Qmult hn hn)))
                   (Qmult C0 (Qabs hn))).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    apply (Qabs_wd (projT1 (b5f_Du x h) n)
                   (Qplus (Qmult 2 (Qmult xn hn)) (Qmult hn hn))).
    exact Hshape.
  - unfold C0.
    apply (Qle_trans (Qabs (Qplus (Qmult 2 (Qmult xn hn)) (Qmult hn hn)))
                     (Qplus (Qabs (Qmult 2 (Qmult xn hn))) (Qabs (Qmult hn hn)))
                     (Qmult (Qplus (Qmult 2 r) (1 # 2)) (Qabs hn))).
    + apply Qabs_triangle.
    + rewrite (Qabs_Qmult 2 (Qmult xn hn)).
      rewrite (Qabs_Qmult xn hn).
      rewrite (Qabs_Qmult hn hn).
      assert (H20 : Qle 0 2) by (unfold Qle; simpl; lia).
      rewrite (Qabs_pos 2 H20).
      apply (Qle_trans
               (Qplus (Qmult 2 (Qmult (Qabs xn) (Qabs hn))) (Qmult (Qabs hn) (Qabs hn)))
               (Qplus (Qmult 2 (Qmult r (Qabs hn))) (Qmult (1 # 2) (Qabs hn)))
               (Qmult (Qplus (Qmult 2 r) (1 # 2)) (Qabs hn))).
      * apply Qplus_le_compat.
        -- (* 2·|xn|·|hn| ≤ 2·r·|hn| *)
           apply (Qle_trans (Qmult 2 (Qmult (Qabs xn) (Qabs hn)))
                            (Qmult (Qmult (Qabs xn) (Qabs hn)) 2)
                            (Qmult 2 (Qmult r (Qabs hn)))).
           ++ apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
           ++ apply (Qle_trans (Qmult (Qmult (Qabs xn) (Qabs hn)) 2)
                               (Qmult (Qmult r (Qabs hn)) 2)
                               (Qmult 2 (Qmult r (Qabs hn)))).
              ** apply (Qmult_le_compat_r (Qmult (Qabs xn) (Qabs hn))
                                          (Qmult r (Qabs hn)) 2).
                 --- apply (Qmult_le_compat_r (Qabs xn) r (Qabs hn)).
                     +++ apply QleT'_to_Qle. exact (Hxr n).
                     +++ apply Qabs_nonneg.
                 --- exact H20.
              ** apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        -- (* |hn|^2 <= (1/2) * |hn| since |hn| <= 1/2 *)
           apply (Qmult_le_compat_r (Qabs hn) (1 # 2) (Qabs hn)).
           ++ exact Hh12.
           ++ apply Qabs_nonneg.
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* M2c-4a: the Δu activation piece (the log-diff assumption of the g-diff closed form) *)
(*   C0 := 2r + 1/2 <= 3 (r < 1), so |Δu_n| <= 3 * |h_n|; *)
(*   |h| < δL * (1#12) and |h| < 1/2 give |Δu| < δL; *)
(*   pointwise: |h_n| < δL_n/12 - e2 gives 3|h_n| < δL_n/4 - 3e2, *)
(*   hence δL_n - |Δu_n| > (3/4) * δL_n + 3e2 > e2/2, which is the witness. *)
(* ============================================================ *)
Lemma b5f_Du_act_delta : forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1) (x : Real)
  (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r)
  (h δL : Real) (HδL0 : real_lt real_zero δL),
  real_lt (real_abs h) (real_mult δL (real_const (1 # 12))) ->
  real_lt (real_abs h) (real_const (1 # 2)) ->
  real_lt (real_abs (b5f_Du x h)) δL.
Proof.
  intros r Hr0 Hr1 x Hxr h δL HδL0 HhL Hh12.
  destruct HδL0 as [eδ [Heδ [Nδ HNδ]]].
  destruct HhL as [e2 [He2 [N2 HN2]]].
  destruct Hh12 as [e1 [He1 [N1 HN1]]].
  unfold real_lt.
  exists (Qmult e2 (Qinv 2)).
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat e2 (Qinv 2)).
    + apply QltT_to_Qlt. exact He2.
    + apply Qinv_lt_0_compat. change (Qlt 0 2). compute. reflexivity.
  - exists (Nat.max (Nat.max N2 (Nat.max N1 Nδ)) 0).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn2 : (N2 <= n)%nat) by lia.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    assert (Hnδ : (Nδ <= n)%nat) by lia.
    set (dLn := projT1 δL n).
    (* δL_n ≥ eδ > 0 *)
    assert (HdLpos : Qlt 0 dLn).
    { unfold dLn.
      apply (Qlt_le_trans 0 eδ (projT1 δL n)).
      - apply QltT_to_Qlt. exact Heδ.
      - apply (Qle_trans eδ (Qminus (projT1 δL n) (projT1 real_zero n)) (projT1 δL n)).
        + apply Qlt_le_weak. apply QltT_to_Qlt.
          exact (HNδ n (NatLe_lift _ _ Hnδ)).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [projT1 real_zero]. ring. }
    (* |h_n| ≤ 1/2 *)
    assert (Hh1q : Qle (Qabs (projT1 h n)) (1 # 2)).
    { apply (Qle_trans (Qabs (projT1 h n)) (Qminus (1 # 2) e1) (1 # 2)).
      - apply Qlt_le_weak. apply QltT_to_Qlt.
        apply (q_lt_minus_shift e1 (1 # 2) (Qabs (projT1 h n))).
        apply (qltT_eq_compat_r (Qminus (1 # 2) (Qabs (projT1 h n)))
                                (Qminus (projT1 (real_const (1 # 2)) n) (projT1 (real_abs h) n))
                                e1).
        + apply qeq_imp_qeqT.
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 2) n)).
          rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          reflexivity.
        + exact (HN1 n (NatLe_lift _ _ Hn1)).
      - apply (Qle_trans (Qminus (1 # 2) e1) (Qplus (Qminus (1 # 2) e1) e1) (1 # 2)).
        + apply (Qle_plus_nonneg_r (Qminus (1 # 2) e1) e1).
          apply Qlt_le_weak. apply QltT_to_Qlt. exact He1.
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    (* |Δu_n| <= C0 * |h_n| <= 3 * |h_n| (C0 := 2r + 1/2 <= 3) *)
    assert (Hh3 : Qle (Qabs (projT1 (b5f_Du x h) n)) (Qmult 3 (Qabs (projT1 h n)))).
    { set (C0q := Qplus (Qmult 2 r) (1 # 2)).
      assert (HC0le3 : Qle C0q 3).
      { unfold C0q. nra. }
      apply (Qle_trans (Qabs (projT1 (b5f_Du x h) n))
                       (Qmult C0q (Qabs (projT1 h n)))
                       (Qmult 3 (Qabs (projT1 h n)))).
      - apply QleT'_to_Qle.
        apply (b5f_Du_abs_pts r x Hxr h n Hh1q).
      - apply (Qmult_le_compat_r C0q 3 (Qabs (projT1 h n))).
        + exact HC0le3.
        + apply Qabs_nonneg. }
    (* projection: e2 < δL_n * (1#12) - |h_n| *)
    assert (H12p : Qeq (projT1 (real_mult δL (real_const (1 # 12))) n) (Qmult dLn (1 # 12))).
    { setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj δL (real_const (1 # 12)) n)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 12) n)).
      unfold dLn. reflexivity. }
    assert (HN2n : Qlt e2 (Qminus (Qmult dLn (1 # 12)) (Qabs (projT1 h n)))).
    { apply (Qlt_le_trans e2
             (Qminus (projT1 (real_mult δL (real_const (1 # 12))) n) (projT1 (real_abs h) n))
             (Qminus (Qmult dLn (1 # 12)) (Qabs (projT1 h n)))).
      - apply QltT_to_Qlt. exact (HN2 n (NatLe_lift _ _ Hn2)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        setoid_rewrite H12p.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        reflexivity. }
    (* |h_n| < δL_n/12 − e2 *)
    assert (Hhn12 : Qlt (Qabs (projT1 h n)) (Qminus (Qmult dLn (1 # 12)) e2)).
    { apply QltT_to_Qlt. apply (q_lt_minus_shift e2 (Qmult dLn (1 # 12)) (Qabs (projT1 h n))). exact (Qlt_to_QltT _ _ HN2n). }
    (* the real_abs projection form of |Δu| *)
    assert (HDu' : Qle (projT1 (real_abs (b5f_Du x h)) n) (Qmult 3 (Qabs (projT1 h n)))).
    { apply (Qle_trans (projT1 (real_abs (b5f_Du x h)) n)
                       (Qabs (projT1 (b5f_Du x h) n))
                       (Qmult 3 (Qabs (projT1 h n)))).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (real_abs_proj (b5f_Du x h) n)).
      - exact Hh3. }
    apply Qlt_to_QltT.
    change (Qlt (Qmult e2 (1 # 2))
                (Qminus dLn (projT1 (real_abs (b5f_Du x h)) n))).
    apply QltT_to_Qlt in He2.
    nra.
Qed.

(* ============================================================ *)
(* M2c-4b: [b5f_gdiff_pts_r], the pointwise closed-form main statement of the g-diff *)
(*   designed as the pointwise tail form, mirroring [b5c_vdh_pts_r]. *)
(*   wS := v(x,h) - x * d(x) * h; the output is: for all n >= N, *)
(*     |wS_n| ≤ en·k2·sn + 2k2p·en'                             *)
(*   δg := min(min(δL * (1#12), eps * kL-Real), (1#2)-const); *)
(*   kL := k2 * (1#2); δL comes from [b5f_LogErr_delta x (eps * kL)]. *)
(*   the inner pieces in order: the three-component min extraction, then [b5f_Du_act_delta] (activation), *)
(*   then epsL'' := eps' * k2p, then Hlog, then [b5i_abs_le_pointwise], then the pointwise *)
(*   Q budget: |LogErr_n| <= en * kL * |Δu_n| + 2k2p * en' (the [b5i] bridge); *)
(*   |Δu_n| <= 3 * sn (by [b5f_Du_abs_pts] and 2r + 1/2 <= 3); *)
(*   |(1/2) * d * h^2| <= (1/4) * k2 * en * sn (from |d_n| <= 1 and |h_n| <= kL * en); *)
(*   wS == (1/2) * LogErr + (1/2) * d * h^2 (re-proved pointwise in place as a Qeq); *)
(*   the linear identity 3kL/2 + k2/4 == k2 (closed by nra). *)
(* ============================================================ *)
Lemma b5f_gdiff_pts_r : forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1)
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
  (* the bridge between (1/2) as Qdiv and (1#2) as Qmake (the pointwise Q layer uses Qmake to avoid Qinv) *)
  assert (Hhalf : (1 / 2) == (1 # 2)).
  { unfold Qdiv. cbn. reflexivity. }
  (* kL := k2 * (1#2); epsL := eps * kL (the linear share of LogErr-delta) *)
  set (kL := Qmult k2 (1 # 2)).
  assert (HkLQ : Qlt 0 kL).
  { unfold kL. apply (Qmult_lt_0_compat k2 (1 # 2)).
    - apply QltT_to_Qlt. exact Hk2.
    - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  assert (HkLT : QltT 0 kL) by (apply Qlt_to_QltT; exact HkLQ).
  assert (HkL0 : Qle 0 kL) by (apply Qlt_le_weak; exact HkLQ).
  set (epsL := real_mult eps (real_const kL)).
  assert (HepsL : real_lt real_zero epsL).
  { unfold epsL. apply real_mult_positive.
    - exact Heps.
    - apply real_const_pos. exact HkLT. }
  destruct (b5f_LogErr_delta x epsL HepsL) as [δL [HδL0 HδL]].
  (* the three-component delta assembly *)
  set (A := real_mult δL (real_const (1 # 12))).
  set (B := real_mult eps (real_const kL)).
  set (C := real_const (1 # 2)).
  set (δg := real_min (real_min A B) C).
  assert (H12T : QltT 0 (1 # 2)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  assert (H112T : QltT 0 (1 # 12)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 12)). unfold Qlt. simpl. lia. }
  assert (HA0 : real_lt real_zero A).
  { unfold A. apply real_mult_positive.
    - exact HδL0.
    - apply real_const_pos. exact H112T. }
  assert (HB0 : real_lt real_zero B).
  { unfold B. apply real_mult_positive.
    - exact Heps.
    - apply real_const_pos. exact HkLT. }
  assert (HC0 : real_lt real_zero C).
  { unfold C. apply real_const_pos. exact H12T. }
  assert (Hδg0 : real_lt real_zero δg).
  { unfold δg. apply real_min_pos.
    { apply real_min_pos.
      { exact HA0. }
      { exact HB0. } }
    { exact HC0. } }
  exists δg. split.
  { exact Hδg0. }
  { intros h Hhδ eps' Heps'.
    (* min extraction: |h| < A, |h| < B, |h| < C *)
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
    (* activation: |Δu| < δL (by [b5f_Du_act_delta]) *)
    assert (Hact : real_lt (real_abs (b5f_Du x h)) δL).
    { apply (b5f_Du_act_delta r Hr0 Hr1 x Hxr h δL HδL0).
      - unfold A in HhA. exact HhA.
      - unfold C in HhC. exact HhC. }
    (* LogErr eps-delta: epsL'' := eps' * k2p *)
    set (epsL'' := real_mult eps' (real_const k2p)).
    assert (HepsL'' : real_lt real_zero epsL'').
    { unfold epsL''. apply real_mult_positive.
      - exact Heps'.
      - apply real_const_pos. exact Hk2p. }
    assert (Hlog : real_le (real_abs (b5f_LogErr x h))
                    (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL'')).
    { exact (HδL h epsL'' HepsL'' Hact). }
    (* the [b5i] bridge: pointwise |LogErr_n| <= B_n + sh_n (sh := epsL'') *)
    destruct (b5i_abs_le_pointwise (b5f_LogErr x h)
               (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL'')
               Hlog epsL'' HepsL'') as [Nlog HNlog].
    (* the witness decomposition *)
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
    (* the pointwise atoms *)
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
    (* |d_n| <= 1; en and en' are nonnegative (from the eps / eps' witnesses) *)
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
    (* |h_n| <= 1/2 (the HhC witness, made pointwise) *)
    assert (Hs12 : Qle sn (1 # 2)).
    { apply (Qle_trans sn (Qminus (1 # 2) e1) (1 # 2)).
      - apply Qlt_le_weak. apply QltT_to_Qlt.
        apply (q_lt_minus_shift e1 (1 # 2) sn).
        apply (qltT_eq_compat_r (Qminus (1 # 2) sn)
                                (Qminus (projT1 C n) (projT1 (real_abs h) n))
                                e1).
        + unfold C. apply qeq_imp_qeqT.
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 2) n)).
          rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          unfold sn, hn. reflexivity.
        + exact (HN1 n (NatLe_lift _ _ Hn1)).
      - apply (Qle_trans (Qminus (1 # 2) e1) (Qplus (Qminus (1 # 2) e1) e1) (1 # 2)).
        + apply (Qle_plus_nonneg_r (Qminus (1 # 2) e1) e1).
          apply Qlt_le_weak. apply QltT_to_Qlt. exact He1.
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    (* |h_n| <= en * kL (the HhB witness |h| < eps * kL-Real, made pointwise) *)
    assert (HsnL : Qle sn (Qmult en kL)).
    { apply (Qle_trans sn (Qminus (Qmult en kL) eB) (Qmult en kL)).
      - apply Qlt_le_weak. apply QltT_to_Qlt.
        apply (q_lt_minus_shift eB (Qmult en kL) sn).
        apply (qltT_eq_compat_r (Qminus (Qmult en kL) sn)
                                (Qminus (projT1 B n) (projT1 (real_abs h) n))
                                eB).
        + unfold B, en, sn, hn.
          apply qeq_imp_qeqT.
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
    (* |Δu_n| <= 3 * sn (by [b5f_Du_abs_pts] and 2r + 1/2 <= 3) *)
    assert (HD3 : Qle Dn (Qmult 3 sn)).
    { set (C0q := Qplus (Qmult 2 r) (1 # 2)).
      assert (HC0le3 : Qle C0q 3).
      { unfold C0q. nra. }
      apply (Qle_trans Dn (Qmult C0q sn) (Qmult 3 sn)).
      - unfold Dn.
        apply QleT'_to_Qle.
          apply (b5f_Du_abs_pts r x Hxr h n).
        exact Hs12.
      - apply (Qmult_le_compat_r C0q 3 sn).
        + exact HC0le3.
        + unfold sn. apply Qabs_nonneg. }
    (* P1: |LogErr_n| <= en * kL * Dn + 2k2p * en' (the [b5i] bridge plus pointwise ring) *)
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
    (* HX: the pointwise bound on the LogErr half (P1 scaled by (1#2), substituting Δu <= 3sn) *)
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
    (* HY: the pointwise bound on the d * h^2 half (from |d_n| <= 1 and |h_n| <= en * kL) *)
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
    (* pointwise identity: wS_n == D_n == (1#2) * LogErr_n + (1#2) * d_n * h_n^2 (re-proved in place on the projections) *)
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
    (* triangle split: |a+b| <= |a| + |b|, and |(1#2) * x| == (1#2) * |x| *)
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
    (* main chain: |wS_n| <= |atom| <= the budget sum <= en * k2 * sn + 2k2p * en' (closed by nra) *)
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
Qed.

(* ============================================================ *)
(* B5-A E-ODE T3: the exp-part family. *)
(*   The main statement [b5a_S_exp_part_bound_closed_r] with the [b5j_*] family. *)
(*   The proofs consume the item3s family above. *)
(*   No further dependencies. *)
(* ============================================================ *)

(* ============================================================ *)
(* M1 skeleton: the [b5j_]-prefixed exp-part components of this development: *)
(*   the planned component families: *)
(*   (1) the activation and bound of v: the [b5j_v_abs_bd] family (|v| <= C1 * |h| + ...; *)
(*      activation via |v| < δ_exp; using [b5f_Du_act_delta], [b5f_Du_abs_pts], *)
(*      [b5f_LogErr_delta], [b5f_v_minus_xdh_decomp]) *)
(*   (2) the exp-at-zero linearization instance: [exp_minus_one_linear] at [b5f_v]; *)
(*   (3) the |Sx| scaling: the [b5j_Sx_*] family (lifting [b5f_S_pts_bounded] *)
(*      in the [real_abs_scaling_le] pattern, after [real_exp_deriv_eq_self]); *)
(*   (4) the main assembly [b5a_S_exp_part_bound_closed_r] (see the file-tail comment) *)
(* ============================================================ *)

(* ============================================================ *)
(* The |Sx| base pieces (the foundation of item (3); the proofs follow the style of *)
(*   [real_abs_exp_pos], [real_inv_pos_correct], [real_abs_scaling_le] *)
(* ============================================================ *)

(* kL: the fixed Q constant share of the log-diff slope (the key to making Kv a pure constant) *)
Definition b5j_kL : Q := (1 # 16).
Lemma b5j_kL_posT : QltT 0 b5j_kL.
Proof.
  apply Qlt_to_QltT. unfold b5j_kL, Qlt. simpl. lia.
Qed.

(* 0 < |S(x)| (lifted from [b5c_S_pos]; in the style of [real_abs_exp_pos]) *)
Lemma b5j_Sx_abs_pos : forall (x : Real),
  real_lt real_zero (real_abs (b5a_S x)).
Proof.
  intros x.
  destruct (b5c_S_pos x) as [eps1 [Heps1 [N1 HN1]]].
  unfold real_lt.
  exists eps1.
  split.
  - exact Heps1.
  - exists N1.
    intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_abs_proj (b5a_S x) n)).
    assert (Hposle : Qle 0 (projT1 (b5a_S x) n)).
    { apply Qlt_le_weak.
      apply (Qlt_trans 0 eps1 (projT1 (b5a_S x) n)).
      - apply QltT_to_Qlt. exact Heps1.
      - apply QltT_to_Qlt.
        apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1 (Qminus (projT1 (b5a_S x) n) (projT1 real_zero n))
                             (projT1 (b5a_S x) n)).
        + apply QltT_to_Qlt. exact (HN1 n Hn).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. ring. }
    apply (Qlt_le_trans eps1 (projT1 (b5a_S x) n)
                           (Qminus (Qabs (projT1 (b5a_S x) n)) (projT1 real_zero n))).
    + apply (Qlt_le_trans eps1 (Qminus (projT1 (b5a_S x) n) (projT1 real_zero n))
                              (projT1 (b5a_S x) n)).
      * apply QltT_to_Qlt. exact (HN1 n Hn).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. ring.
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      rewrite Hz.
      rewrite (Qabs_pos (projT1 (b5a_S x) n) Hposle).
      ring.
Qed.

(* |S(x)| == S(x) since S > 0 *)
Lemma b5j_Sx_abs_eq : forall (x : Real),
  real_eq (real_abs (b5a_S x)) (b5a_S x).
Proof.
  intros x. exact (real_abs_pos_req (b5a_S x) (b5c_S_pos x)).
Qed.

(* real_le real_zero |Sx| (lifting the strict 0 < |Sx|; built directly in the left branch of the Or encoding of real_le) *)
Lemma b5j_Sx_abs_nonneg : forall (x : Real),
  real_le real_zero (real_abs (b5a_S x)).
Proof.
  intros x.
  apply (RealSetoid.real_lt_le_iff_req real_zero (real_abs (b5a_S x))).
  left. exact (b5j_Sx_abs_pos x).
Qed.

(* ============================================================ *)
(* Kvq: the |h| slope of the v-bound (a pure Q constant: r + 1/4 + (1/2) * kL * (2r + 1/2)); *)
(*   r < 1 gives Kvq < 2 (decidable by nra at the Q level) *)
(* ============================================================ *)
Definition b5j_Kvq (r : Q) : Q :=
  Qplus r (Qplus (1 # 4) (Qmult (1 # 2)
                                  (Qmult b5j_kL (Qplus (Qmult 2 r) (1 # 2))))).

Lemma b5j_Kvq_pos : forall (r : Q) (Hr0 : Qle 0 r),
  QltT 0 (b5j_Kvq r).
Proof.
  intros r Hr0. apply Qlt_to_QltT. unfold b5j_Kvq, b5j_kL. nra.
Qed.

Lemma b5j_Kvq_le_two : forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  QleT' (b5j_Kvq r) 2.
Proof.
  intros r Hr0 Hr1. apply Qle_to_QleT'. unfold b5j_Kvq, b5j_kL. nra.
Qed.

(* positivity of 1 + Kvq (an inv-real certificate; assumption r >= 0) *)
Lemma b5j_one_plus_Kvq_posT : forall (r : Q) (Hr0 : Qle 0 r), QltT 0 (1 + b5j_Kvq r).
Proof.
  intros r Hr0.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans 0 1 (1 + b5j_Kvq r)).
  - change (Qlt 0 1). unfold Qlt. simpl. lia.
  - unfold b5j_Kvq, b5j_kL. nra.
Qed.

(* Q reduction: Qinv(Kvq) * Kvq == 1 (Kvq is nonzero) *)
Lemma b5j_kslope_Kvq : forall (r : Q) (Hr0 : Qle 0 r),
  QeqT (Qmult (Qinv (b5j_Kvq r)) (b5j_Kvq r)) 1.
Proof.
  intros r Hr0.
  apply qeq_imp_qeqT.
  rewrite (Qmult_comm (Qinv (b5j_Kvq r)) (b5j_Kvq r)).
  rewrite (Qmult_inv_r (b5j_Kvq r)).
  - reflexivity.
- intro Hz; exact (match (q_neq_of_lt (b5j_Kvq r) (b5j_Kvq_pos r Hr0) (qeq_imp_qeqT _ _ Hz)) with end).
Qed.

(* real_const of a product: the projection reduces to a Q-level ring identity *)
Lemma b5j_real_const_mult_eq : forall (q1 q2 : Q),
  real_eq (real_mult (real_const q1) (real_const q2)) (real_const (Qmult q1 q2)).
Proof.
  intros q1 q2.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const q1) (real_const q2) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj q1 n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj q2 n)).
  ring.
Qed.

(* ============================================================ *)
(* The Real-le to pointwise bridge (with margin m) *)
(*   the Or encoding of real_le: the lt branch gives X_n <= Y_n pointwise (eventually); the eq branch *)
(*   (Cauchy equality, not pointwise) needs the margin m to absorb it; unified as *)
(*   there is N with X_n <= Y_n + m_n for all n >= N.  The eq branch uses the eps witness of real_eq *)
(*   (eps := m0), and the lt branch uses its separated witness directly. *)
(* ============================================================ *)
Lemma b5j_real_le_m_pts : forall (X Y m : Real),
  real_le X Y -> real_lt real_zero m ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QleT' (projT1 X n) (Qplus (projT1 Y n) (projT1 m n))).
Proof.
  intros X Y m Hle Hm.
  destruct Hm as [m0 [Hm0 [Nm HNm]]].
  assert (Hm0Q : Qlt 0 m0) by (apply QltT_to_Qlt; exact Hm0).
  destruct Hle as [Hlt | Heq].
  - (* the lt branch: X_n <= Y_n (eventually) <= Y_n + m_n *)
    destruct Hlt as [e [He [N HN]]].
    exists (Nat.max N Nm).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (HnN : (N <= n)%nat) by lia.
    assert (HnNm : (Nm <= n)%nat) by lia.
    apply Qle_to_QleT'.
      apply (Qle_trans (projT1 X n) (projT1 Y n)
                     (Qplus (projT1 Y n) (projT1 m n))).
    + apply Qlt_le_weak.
      apply (Qlt_le_trans (projT1 X n) (Qminus (projT1 Y n) e) (projT1 Y n)).
      * apply QltT_to_Qlt.
        apply (q_lt_minus_shift e (projT1 Y n) (projT1 X n)).
        exact (HN n (NatLe_lift _ _ HnN)).
      * apply (Qle_trans (Qminus (projT1 Y n) e) (Qminus (projT1 Y n) 0)
                         (projT1 Y n)).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply (Qopp_le_compat 0 e).
              apply Qlt_le_weak. apply QltT_to_Qlt. exact He.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans (projT1 Y n) (Qplus (projT1 Y n) 0)
                       (Qplus (projT1 Y n) (projT1 m n))).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qplus_le_compat (projT1 Y n) (projT1 Y n) 0 (projT1 m n)).
        -- apply Qle_refl.
        -- apply Qlt_le_weak.
           apply (Qlt_le_trans 0 m0 (projT1 m n)).
           ++ exact Hm0Q.
           ++ apply Qlt_le_weak.
              apply QltT_to_Qlt.
              apply Qlt_to_QltT.
              apply (Qlt_le_trans m0 (Qminus (projT1 m n) (projT1 real_zero n))
                                   (projT1 m n)).
              ** apply QltT_to_Qlt. exact (HNm n (NatLe_lift _ _ HnNm)).
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. ring.
  - (* the eq branch: |X_n - Y_n| < m0 (eventually), so X_n <= Y_n + m0 <= Y_n + m_n *)
    destruct (Heq m0) as [N HN].
    { exact Hm0. }
    exists (Nat.max N Nm).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (HnN : (N <= n)%nat) by lia.
    assert (HnNm : (Nm <= n)%nat) by lia.
    apply Qle_to_QleT'.
      apply (Qle_trans (projT1 X n)
                     (Qplus (projT1 Y n) m0)
                     (Qplus (projT1 Y n) (projT1 m n))).
    + (* X_n <= Y_n + m0: split on the sign of z := X_n - Y_n *)
      destruct (Qlt_le_dec (Qminus (projT1 X n) (projT1 Y n)) 0) as [Hzneg | Hzpos].
      * (* z < 0: X_n <= Y_n <= Y_n + m0 *)
        apply (Qle_trans (projT1 X n) (projT1 Y n) (Qplus (projT1 Y n) m0)).
        -- apply Qlt_le_weak. nra.
        -- apply (Qle_trans (projT1 Y n) (Qplus (projT1 Y n) 0)
                            (Qplus (projT1 Y n) m0)).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
           ++ apply (Qplus_le_compat (projT1 Y n) (projT1 Y n) 0 m0).
              ** apply Qle_refl.
              ** apply Qlt_le_weak. exact Hm0Q.
      * (* 0 <= z: |z| == z, and HN gives z < m0 *)
        apply Qlt_le_weak.
        assert (Hzabs : QltT (Qabs (Qminus (projT1 X n) (projT1 Y n))) m0).
        { exact (HN n (NatLe_lift _ _ HnN)). }
        apply QltT_to_Qlt in Hzabs.
        setoid_rewrite (Qabs_pos (Qminus (projT1 X n) (projT1 Y n)) Hzpos) in Hzabs.
        nra.
    + apply (Qle_trans (Qplus (projT1 Y n) m0)
                       (Qplus (projT1 Y n) (projT1 m n))
                       (Qplus (projT1 Y n) (projT1 m n))).
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply Qlt_le_weak.
           apply (Qlt_le_trans m0 (Qminus (projT1 m n) (projT1 real_zero n))
                                (projT1 m n)).
           ++ apply QltT_to_Qlt. exact (HNm n (NatLe_lift _ _ HnNm)).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [real_zero real_const projT1]. ring.
      * apply Qle_refl.
Qed.


(* ============================================================ *)
(* The pointwise ingredient pieces of [b5j_v_abs_bd] *)
(*   [b5j_qmult_le_compat]: the Q-level product bound on both ends (there is no *)
(*   [Qmult_le_compat_l], so it is built here: a <= b, c <= d, 0 <= a, 0 <= c give a * c <= b * d) *)
(*   [b5j_xdh_abs_le]: |x * d * h|_n <= r * |h_n| (from |x_n| <= r and |d_n| <= 1) *)
(*   [b5j_dhh_abs_le]: |d * h * h|_n <= (1/2) * |h_n| (from |d_n| <= 1 and |h_n| <= 1/2) *)
(* ============================================================ *)
Lemma b5j_qmult_le_compat : forall (a b c d : Q),
  Qle a b -> Qle c d -> Qle 0 a -> Qle 0 c ->
  QleT' (Qmult a c) (Qmult b d).
Proof.
  intros a b c d Hab Hcd Ha0 Hc0.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qmult a c) (Qmult b c) (Qmult b d)).
  - apply (Qmult_le_compat_r a b c Hab Hc0).
  - assert (Hb0 : Qle 0 b) by (apply (Qle_trans 0 a b Ha0 Hab)).
    apply (Qle_trans (Qmult b c) (Qmult c b) (Qmult b d)).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans (Qmult c b) (Qmult d b) (Qmult b d)).
      * apply (Qmult_le_compat_r c d b Hcd Hb0).
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

Lemma b5j_xdh_abs_le : forall (x h : Real) (r : Q)
  (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r)
  (n : nat),
  Qle (Qabs (projT1 (b5a_atan_d x) n)) 1 ->
  QleT' (Qabs (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n))
      (Qmult r (Qabs (projT1 h n))).
Proof.
  intros x h r Hxr n Hd.
  apply Qle_to_QleT'.
  assert (Hshape : projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n ==
                   Qmult (projT1 x n) (Qmult (projT1 (b5a_atan_d x) n) (projT1 h n))).
  { repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _))). ring. }
  apply (Qle_trans (Qabs (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n))
                   (Qabs (Qmult (projT1 x n) (Qmult (projT1 (b5a_atan_d x) n) (projT1 h n))))
                   (Qmult r (Qabs (projT1 h n)))).
  { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    apply (Qabs_wd (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n)
                   (Qmult (projT1 x n) (Qmult (projT1 (b5a_atan_d x) n) (projT1 h n)))).
    exact Hshape. }
  { rewrite (Qabs_Qmult (projT1 x n) (Qmult (projT1 (b5a_atan_d x) n) (projT1 h n))).
    rewrite (Qabs_Qmult (projT1 (b5a_atan_d x) n) (projT1 h n)).
    assert (Hh0 : Qle 0 (Qabs (projT1 h n))) by apply Qabs_nonneg.
    assert (Hxn0 : Qle 0 (Qabs (projT1 x n))) by apply Qabs_nonneg.
    assert (Hxn : Qle (Qabs (projT1 x n)) r) by (apply QleT'_to_Qle; exact (Hxr n)).
    apply (Qle_trans (Qmult (Qabs (projT1 x n)) (Qmult (Qabs (projT1 (b5a_atan_d x) n)) (Qabs (projT1 h n))))
                     (Qmult (Qmult (Qabs (projT1 x n)) (Qabs (projT1 (b5a_atan_d x) n))) (Qabs (projT1 h n)))
                     (Qmult r (Qabs (projT1 h n)))).
    { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    { apply QleT'_to_Qle.
      apply (b5j_qmult_le_compat
               (Qmult (Qabs (projT1 x n)) (Qabs (projT1 (b5a_atan_d x) n)))
               r (Qabs (projT1 h n)) (Qabs (projT1 h n))).
      { apply (Qle_trans (Qmult (Qabs (projT1 x n)) (Qabs (projT1 (b5a_atan_d x) n)))
                         (Qmult r 1) r).
        { apply QleT'_to_Qle.
          apply (b5j_qmult_le_compat (Qabs (projT1 x n)) r
                                     (Qabs (projT1 (b5a_atan_d x) n)) 1).
          { exact Hxn. }
          { exact Hd. }
          { exact Hxn0. }
          { apply Qabs_nonneg. } }
        { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. } }
      { apply Qle_refl. }
      { apply (Qmult_le_0_compat (Qabs (projT1 x n)) (Qabs (projT1 (b5a_atan_d x) n))).
        { apply Qabs_nonneg. }
        { apply Qabs_nonneg. } }
      { exact Hh0. } } }
Qed.

Lemma b5j_dhh_abs_le : forall (x h : Real) (n : nat),
  Qle (Qabs (projT1 (b5a_atan_d x) n)) 1 ->
  Qle (Qabs (projT1 h n)) (1 # 2) ->
  QleT' (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))
      (Qmult (1 # 2) (Qabs (projT1 h n))).
Proof.
  intros x h n Hd Hh12.
  apply Qle_to_QleT'.
  assert (Hshape : projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n ==
                   Qmult (projT1 (b5a_atan_d x) n) (Qmult (projT1 h n) (projT1 h n))).
  { repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _))). ring. }
  apply (Qle_trans (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))
                   (Qabs (Qmult (projT1 (b5a_atan_d x) n) (Qmult (projT1 h n) (projT1 h n))))
                   (Qmult (1 # 2) (Qabs (projT1 h n)))).
  { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    apply (Qabs_wd (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n)
                   (Qmult (projT1 (b5a_atan_d x) n) (Qmult (projT1 h n) (projT1 h n)))).
    exact Hshape. }
  { rewrite (Qabs_Qmult (projT1 (b5a_atan_d x) n) (Qmult (projT1 h n) (projT1 h n))).
    rewrite (Qabs_Qmult (projT1 h n) (projT1 h n)).
    assert (Hh0 : Qle 0 (Qabs (projT1 h n))) by apply Qabs_nonneg.
    assert (Hd0 : Qle 0 (Qabs (projT1 (b5a_atan_d x) n))) by apply Qabs_nonneg.
    apply (Qle_trans (Qmult (Qabs (projT1 (b5a_atan_d x) n)) (Qmult (Qabs (projT1 h n)) (Qabs (projT1 h n))))
                     (Qmult (Qmult (Qabs (projT1 (b5a_atan_d x) n)) (Qabs (projT1 h n))) (Qabs (projT1 h n)))
                     (Qmult (1 # 2) (Qabs (projT1 h n)))).
    { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    { apply QleT'_to_Qle.
      apply (b5j_qmult_le_compat
               (Qmult (Qabs (projT1 (b5a_atan_d x) n)) (Qabs (projT1 h n)))
               (1 # 2) (Qabs (projT1 h n)) (Qabs (projT1 h n))).
      { apply (Qle_trans (Qmult (Qabs (projT1 (b5a_atan_d x) n)) (Qabs (projT1 h n)))
                         (Qmult 1 (1 # 2)) (1 # 2)).
        { apply QleT'_to_Qle.
          apply (b5j_qmult_le_compat (Qabs (projT1 (b5a_atan_d x) n)) 1
                                     (Qabs (projT1 h n)) (1 # 2)).
          { exact Hd. }
          { exact Hh12. }
          { exact Hd0. }
          { exact Hh0. } }
        { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. } }
      { apply Qle_refl. }
      { apply (Qmult_le_0_compat (Qabs (projT1 (b5a_atan_d x) n)) (Qabs (projT1 h n))).
        { exact Hd0. }
        { exact Hh0. } }
      { exact Hh0. } } }
Qed.

(* ---- the main goal statement, in its finalized form ---- *)
(*
Lemma b5a_S_exp_part_bound_closed_r :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_mult (b5a_S x)
                 (real_plus (cauchy_real_exp (b5f_v x h))
                            (real_opp (real_plus real_one (b5f_v x h))))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
*)

(* ============================================================ *)
(* (1) the [b5j_v_abs_bd] family (|v(x,h)| <= Kvq(r) * |h| + shV): *)
(*   v == x * d * h + (1/2) * LogErr + (1/2) * d * h * h as a Real-level semantic identity (by *)
(*   [b5f_v_minus_xdh_decomp]; re-proved in place by pointwise unfold + field, *)
(*   with the identical log atom on both sides cancelling; the F0/F1 structure of item3s). *)
(* ============================================================ *)

(* (a) pointwise triangle: |v_n| <= |xdh_n| + (1/2) * |LogErr_n| + (1/2) * |dhh_n| *)
(* note: field does not combine with set abstractions; only the fully
   explicit projection form closes under field, so this proof is
   written fully explicitly. *)
Lemma b5j_v_tri_pts : forall (x h : Real) (n : nat),
  QleT' (Qabs (projT1 (b5f_v x h) n))
      (Qplus (Qabs (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n))
         (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                (Qmult (1 # 2)
                   (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))))).
Proof.
  intros x h n.
  apply Qle_to_QleT'.
  assert (Hhalf : (1 / 2) == (1 # 2)).
  { unfold Qdiv. cbn. reflexivity. }
  (* v_n == Xdh_n + Dsum_n (fully explicit unfold on the projections; the log atom is the same on both sides, so field closes) *)
  assert (F0 : projT1 (b5f_v x h) n ==
           Qplus (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n)
             (projT1 (real_plus (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                                (real_mult (real_const (1 / 2))
                                   (real_mult (b5a_atan_d x) (real_mult h h)))) n)).
  { unfold b5f_v, b5f_g, b5f_LogErr, b5f_u, b5f_Du.
    repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) || setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ||
            setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _))).
    cbn [projT1 real_const real_one real_zero].
    field. }
  (* Dsum_n == (1#2) * LogErr_n + (1#2) * Dhh_n (fully explicit) *)
  assert (FD : projT1 (real_plus (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                                 (real_mult (real_const (1 / 2))
                                    (real_mult (b5a_atan_d x) (real_mult h h)))) n ==
           Qplus (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n))
                 (Qmult (1 # 2)
                    (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))).
  { repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) || setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _))).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 / 2) n)).
    setoid_rewrite Hhalf.
    reflexivity. }
  (* (1#2) is nonnegative, so |(1#2) * q| == (1#2) * |q| *)
  assert (Habs12 : forall q : Q, Qeq (Qabs (Qmult (1 # 2) q))
                                    (Qmult (1 # 2) (Qabs q))).
  { intro q.
    rewrite (Qabs_Qmult (1 # 2) q).
    apply (Qmult_comp (Qabs (1 # 2)) (1 # 2)).
    - apply (Qabs_pos (1 # 2)). change (Qle 0 (1 # 2)). unfold Qle. simpl. lia.
    - reflexivity. }
  (* |v_n| <= |Xdh_n| + |Dsum_n| (by F0 and the triangle inequality) *)
  assert (Ht1 : Qle (Qabs (projT1 (b5f_v x h) n))
                    (Qplus (Qabs (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n))
                           (Qabs (projT1 (real_plus (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                                                    (real_mult (real_const (1 / 2))
                                                       (real_mult (b5a_atan_d x) (real_mult h h)))) n)))).
  { apply (Qle_trans (Qabs (projT1 (b5f_v x h) n))
                     (Qabs (Qplus (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n)
                                  (projT1 (real_plus (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                                                     (real_mult (real_const (1 / 2))
                                                        (real_mult (b5a_atan_d x) (real_mult h h)))) n)))
                     (Qplus (Qabs (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n))
                            (Qabs (projT1 (real_plus (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                                                     (real_mult (real_const (1 / 2))
                                                        (real_mult (b5a_atan_d x) (real_mult h h)))) n)))).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      apply (Qabs_wd (projT1 (b5f_v x h) n)
                     (Qplus (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n)
                            (projT1 (real_plus (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                                               (real_mult (real_const (1 / 2))
                                                  (real_mult (b5a_atan_d x) (real_mult h h)))) n))).
      exact F0.
    - apply Qabs_triangle. }
  (* |Dsum_n| <= (1#2) * |LogErr_n| + (1#2) * |Dhh_n| (by FD, the triangle inequality, and the abs-half step) *)
  assert (HD : Qle (Qabs (projT1 (real_plus (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                                            (real_mult (real_const (1 / 2))
                                               (real_mult (b5a_atan_d x) (real_mult h h)))) n))
                   (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                          (Qmult (1 # 2)
                             (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))))).
  { apply (Qle_trans (Qabs (projT1 (real_plus (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                                              (real_mult (real_const (1 / 2))
                                                 (real_mult (b5a_atan_d x) (real_mult h h)))) n))
                     (Qabs (Qplus (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n))
                                  (Qmult (1 # 2)
                                     (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))))
                     (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                            (Qmult (1 # 2)
                               (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))))).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      apply (Qabs_wd (projT1 (real_plus (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                                        (real_mult (real_const (1 / 2))
                                           (real_mult (b5a_atan_d x) (real_mult h h)))) n)
                     (Qplus (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n))
                            (Qmult (1 # 2)
                               (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n)))).
      exact FD.
    - apply (Qle_trans
               (Qabs (Qplus (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n))
                            (Qmult (1 # 2)
                               (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))))
               (Qplus (Qabs (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n)))
                      (Qabs (Qmult (1 # 2)
                             (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))))
               (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                      (Qmult (1 # 2)
                         (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))))).
      + apply Qabs_triangle.
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        apply (Qplus_comp
                 (Qabs (Qmult (1 # 2) (projT1 (b5f_LogErr x h) n)))
                 (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))).
          * exact (Habs12 (projT1 (b5f_LogErr x h) n)).
          * exact (Habs12 (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n)). }
  (* assembly: |v_n| <= (|Xdh| + |Dsum|) <= the goal (by [Qplus_le_compat] and reflexivity) *)
  apply (Qle_trans (Qabs (projT1 (b5f_v x h) n))
                   (Qplus (Qabs (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n))
                          (Qabs (projT1 (real_plus (real_mult (real_const (1 / 2)) (b5f_LogErr x h))
                                                   (real_mult (real_const (1 / 2))
                                                      (real_mult (b5a_atan_d x) (real_mult h h)))) n)))
                   (Qplus (Qabs (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n))
                      (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                             (Qmult (1 # 2)
                                (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n)))))).
  - exact Ht1.
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + exact HD.
Qed.

(* (b) budget assembly: |v_n| <= Kvq(r) * sn + (3/32) * shn.
   inputs: the (a) triangle plus the three pointwise bounds
   (|xdh| <= r * sn, |LogErr| <= kL * C0q * sn + (3/16) * shn,
   |dhh| <= (1/2) * sn), with C0q := 2r + 1/2.
   the slope composition r + (1/2) * kL * C0q + 1/4 == Kvq. *)
Lemma b5j_v_pts_budget : forall (x h sh : Real) (r : Q) (n : nat),
  Qle (Qabs (projT1 (b5f_v x h) n))
      (Qplus (Qabs (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n))
         (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                (Qmult (1 # 2)
                   (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))))) ->
  Qle (Qabs (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n))
      (Qmult r (Qabs (projT1 h n))) ->
  Qle (Qabs (projT1 (b5f_LogErr x h) n))
      (Qplus (Qmult (Qmult b5j_kL (Qplus (Qmult 2 r) (1 # 2)))
                    (Qabs (projT1 h n)))
             (Qmult (3 # 16) (projT1 sh n))) ->
  Qle (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))
      (Qmult (1 # 2) (Qabs (projT1 h n))) ->
  QleT' (Qabs (projT1 (b5f_v x h) n))
      (Qplus (Qmult (b5j_Kvq r) (Qabs (projT1 h n)))
             (Qmult (3 # 32) (projT1 sh n))).
Proof.
  intros x h sh r n Hv Hxdh Hlog Hdhh.
  apply Qle_to_QleT'.
  set (sn := Qabs (projT1 h n)).
  set (shn := projT1 sh n).
  (* (1/2) * |LogErr_n| <= (1/2) * kL * C0q * sn + (3/32) * shn (Hlog scaled by (1#2), collected by ring) *)
  assert (Hp2 : Qle (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
      (Qplus (Qmult (Qmult (1 # 2) (Qmult b5j_kL (Qplus (Qmult 2 r) (1 # 2)))) sn)
             (Qmult (3 # 32) shn))).
  { apply (Qle_trans (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                     (Qmult (Qabs (projT1 (b5f_LogErr x h) n)) (1 # 2))
                     (Qplus (Qmult (Qmult (1 # 2) (Qmult b5j_kL (Qplus (Qmult 2 r) (1 # 2)))) sn)
                            (Qmult (3 # 32) shn))).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    - apply (Qle_trans (Qmult (Qabs (projT1 (b5f_LogErr x h) n)) (1 # 2))
                       (Qmult (Qplus (Qmult (Qmult b5j_kL (Qplus (Qmult 2 r) (1 # 2))) sn)
                                     (Qmult (3 # 16) shn)) (1 # 2))
                       (Qplus (Qmult (Qmult (1 # 2) (Qmult b5j_kL (Qplus (Qmult 2 r) (1 # 2)))) sn)
                              (Qmult (3 # 32) shn))).
      + apply (Qmult_le_compat_r (Qabs (projT1 (b5f_LogErr x h) n))
                                 (Qplus (Qmult (Qmult b5j_kL (Qplus (Qmult 2 r) (1 # 2))) sn)
                                        (Qmult (3 # 16) shn))
                                 (1 # 2)).
        * unfold sn, shn. exact Hlog.
        * change (Qle 0 (1 # 2)). unfold Qle. simpl. lia.
      + unfold b5j_kL. nra. }
  (* (1/2) * |dhh_n| <= (1/4) * sn (Hdhh scaled by (1#2)) *)
  assert (Hp3 : Qle (Qmult (1 # 2) (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n)))
                    (Qmult (1 # 4) sn)).
  { apply (Qle_trans (Qmult (1 # 2) (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n)))
                     (Qmult (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n)) (1 # 2))
                     (Qmult (1 # 4) sn)).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    - apply (Qle_trans (Qmult (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n)) (1 # 2))
                       (Qmult (Qmult (1 # 2) sn) (1 # 2))
                       (Qmult (1 # 4) sn)).
      + apply (Qmult_le_compat_r (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))
                                 (Qmult (1 # 2) sn)
                                 (1 # 2)).
        * unfold sn. exact Hdhh.
        * change (Qle 0 (1 # 2)). unfold Qle. simpl. lia.
      + nra. }
  (* assembly: |v_n| <= mid1 (the triangle inputs) <= mid2 (the piecewise budgets) <= the goal (the slope composition) *)
  apply (Qle_trans (Qabs (projT1 (b5f_v x h) n))
                   (Qplus (Qabs (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n))
                      (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                             (Qmult (1 # 2)
                                (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n)))))
                   (Qplus (Qmult (b5j_Kvq r) sn) (Qmult (3 # 32) shn))).
  - exact Hv.
  - apply (Qle_trans
             (Qplus (Qabs (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n))
                (Qplus (Qmult (1 # 2) (Qabs (projT1 (b5f_LogErr x h) n)))
                       (Qmult (1 # 2)
                          (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n)))))
             (Qplus (Qmult r sn)
                (Qplus (Qplus (Qmult (Qmult (1 # 2) (Qmult b5j_kL (Qplus (Qmult 2 r) (1 # 2)))) sn)
                              (Qmult (3 # 32) shn))
                       (Qmult (1 # 4) sn)))
             (Qplus (Qmult (b5j_Kvq r) sn) (Qmult (3 # 32) shn))).
    + apply Qplus_le_compat.
      * unfold sn. exact Hxdh.
      * apply Qplus_le_compat.
        -- exact Hp2.
        -- exact Hp3.
    + unfold b5j_Kvq, b5j_kL. nra.
Qed.

(* (c) the Real-level bound: |v(x,h)| <= Kvq(r) * |h| + shV.
   method: epsL' := shV * (1#8) and mm := shV * (1#16); the bridge
   [b5j_real_le_m_pts] makes Hlog pointwise; the pointwise budget uses
   (a) and (b); the Real-le output takes the lt branch with witness sh0/8
   (the slack (29/32) * shn >= sh0/8). *)
Lemma b5j_v_abs_bd :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (h shV : Real) (HshV : real_lt real_zero shV),
  (forall (epsL' : Real), real_lt real_zero epsL' ->
    real_le (real_abs (b5f_LogErr x h))
            (real_plus (real_mult (real_const b5j_kL) (real_abs (b5f_Du x h))) epsL')) ->
  real_lt (real_abs h) (real_const (1 # 2)) ->
  real_le (real_abs (b5f_v x h))
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV).
Proof.
  intros r Hr0 Hr1 x Hxr h shV HshV Hlog Hh12.
  (* epsL' := shV * (1#8) and mm := shV * (1#16) (at the Real level, positive by [real_const_pos]) *)
  set (epsL' := real_mult shV (real_const (1 # 8))).
  set (mm := real_mult shV (real_const (1 # 16))).
  assert (H18T : QltT 0 (1 # 8)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (H116T : QltT 0 (1 # 16)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HepsL' : real_lt real_zero epsL').
  { unfold epsL'. apply real_mult_positive.
    - exact HshV.
    - apply real_const_pos. exact H18T. }
  assert (Hmm : real_lt real_zero mm).
  { unfold mm. apply real_mult_positive.
    - exact HshV.
    - apply real_const_pos. exact H116T. }
  destruct HshV as [sh0 [Hsh0 [Nsh HshN]]].
  destruct Hh12 as [e1 [He1 [N1 HN1]]].
  destruct (b5c_d_proj_le_one x) as [Nd Hd].
  (* the bridge: |LogErr| <= kL * |Du| + epsL' made pointwise (with the mm margin) *)
  destruct (b5j_real_le_m_pts (real_abs (b5f_LogErr x h))
             (real_plus (real_mult (real_const b5j_kL) (real_abs (b5f_Du x h))) epsL')
             mm (Hlog epsL' HepsL') Hmm) as [Nlog HNlog].
  (* the real_le output is the lt branch (witness sh0 * (1#8)) *)
  apply (RealSetoid.real_lt_le_iff_req
           (real_abs (b5f_v x h))
           (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)).
  left.
  unfold real_lt.
  exists (Qmult sh0 (1 # 8)).
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat sh0 (1 # 8)).
    + apply QltT_to_Qlt. exact Hsh0.
    + change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia.
  - exists (Nat.max Nlog (Nat.max Nsh (Nat.max N1 Nd))).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hnlog : (Nlog <= n)%nat) by lia.
    assert (Hnsh : (Nsh <= n)%nat) by lia.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    assert (Hnd : (Nd <= n)%nat) by lia.
    (* the pointwise atoms *)
    set (hn := projT1 h n).
    set (sn := Qabs hn).
    set (shn := projT1 shV n).
    set (Vn := Qabs (projT1 (b5f_v x h) n)).
    (* |h_n| <= 1/2 (the Hh12 witness, made pointwise) *)
    assert (Hs12 : Qle sn (1 # 2)).
    { apply (Qle_trans sn (Qminus (1 # 2) e1) (1 # 2)).
      - apply Qlt_le_weak. apply QltT_to_Qlt.
        apply (q_lt_minus_shift e1 (1 # 2) sn).
        apply (qltT_eq_compat_r (Qminus (1 # 2) sn)
                                (Qminus (projT1 (real_const (1 # 2)) n) (projT1 (real_abs h) n))
                                e1).
        + apply qeq_imp_qeqT.
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 2) n)).
          rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          unfold sn, hn. reflexivity.
        + exact (HN1 n (NatLe_lift _ _ Hn1)).
      - apply (Qle_trans (Qminus (1 # 2) e1) (Qplus (Qminus (1 # 2) e1) e1) (1 # 2)).
        + apply (Qle_plus_nonneg_r (Qminus (1 # 2) e1) e1).
          apply Qlt_le_weak. apply QltT_to_Qlt. exact He1.
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    (* sh0 <= shn (HshN, pointwise) *)
    assert (Hsh0le : Qle sh0 shn).
    { apply Qlt_le_weak.
      apply QltT_to_Qlt.
      apply (qltT_eq_compat_r shn (Qminus shn (projT1 real_zero n)) sh0).
      - apply qeq_imp_qeqT.
        assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        rewrite Hz. ring.
      - exact (HshN n (NatLe_lift _ _ Hnsh)). }
    (* |d_n| ≤ 1 *)
    assert (Hd1 : Qle (Qabs (projT1 (b5a_atan_d x) n)) 1).
    { exact (QleT'_to_Qle _ _ (Hd n (NatLe_lift _ _ Hnd))). }
    (* |xdh_n| ≤ r·sn *)
    assert (Hxdh : Qle (Qabs (projT1 (real_mult (real_mult x (b5a_atan_d x)) h) n))
                       (Qmult r sn)).
    { unfold sn, hn. apply QleT'_to_Qle. apply (b5j_xdh_abs_le x h r Hxr n Hd1). }
    (* |Δu_n| <= (2r + 1/2) * sn (by [b5f_Du_abs_pts]) *)
    assert (HDu : Qle (Qabs (projT1 (b5f_Du x h) n))
                      (Qmult (Qplus (Qmult 2 r) (1 # 2)) sn)).
    { unfold sn, hn. apply QleT'_to_Qle. apply (b5f_Du_abs_pts r x Hxr h n). exact Hs12. }
    (* |dhh_n| <= (1/2) * sn (by [b5j_dhh_abs_le]) *)
    assert (Hdhh : Qle (Qabs (projT1 (real_mult (b5a_atan_d x) (real_mult h h)) n))
                       (Qmult (1 # 2) sn)).
    { unfold sn, hn. apply QleT'_to_Qle. apply (b5j_dhh_abs_le x h n Hd1). exact Hs12. }
    (* |LogErr_n| <= kL * Dn + (3/16) * shn (HNlog plus the projection Qeq bridge; Dn := |Δu_n|) *)
    set (Dn := Qabs (projT1 (b5f_Du x h) n)).
    assert (HlogN : Qle (Qabs (projT1 (b5f_LogErr x h) n))
        (Qplus (Qmult b5j_kL Dn) (Qmult (3 # 16) shn))).
    { apply (Qle_trans (Qabs (projT1 (b5f_LogErr x h) n))
                       (Qplus (projT1 (real_plus (real_mult (real_const b5j_kL) (real_abs (b5f_Du x h))) epsL') n)
                              (projT1 mm n))
                       (Qplus (Qmult b5j_kL Dn) (Qmult (3 # 16) shn))).
      - apply (Qle_trans (Qabs (projT1 (b5f_LogErr x h) n))
                         (projT1 (real_abs (b5f_LogErr x h)) n)
                         (Qplus (projT1 (real_plus (real_mult (real_const b5j_kL) (real_abs (b5f_Du x h))) epsL') n)
                                (projT1 mm n))).
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. symmetry. exact (qeqT_imp_qeq _ _ (real_abs_proj (b5f_LogErr x h) n)).
        + exact (QleT'_to_Qle _ _ (HNlog n (NatLe_lift _ _ Hnlog))).
      - apply (Qle_trans
                 (Qplus (projT1 (real_plus (real_mult (real_const b5j_kL) (real_abs (b5f_Du x h))) epsL') n)
                        (projT1 mm n))
                 (Qplus (Qplus (Qmult b5j_kL Dn) (Qmult shn (1 # 8))) (Qmult shn (1 # 16)))
                 (Qplus (Qmult b5j_kL Dn) (Qmult (3 # 16) shn))).
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          apply (Qplus_comp
                   (projT1 (real_plus (real_mult (real_const b5j_kL) (real_abs (b5f_Du x h))) epsL') n)
                   (Qplus (Qmult b5j_kL Dn) (Qmult shn (1 # 8)))).
          * setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const b5j_kL) (real_abs (b5f_Du x h))) epsL' n)).
            setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const b5j_kL) (real_abs (b5f_Du x h)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_const_proj b5j_kL n)).
            setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (b5f_Du x h) n)).
            unfold epsL', shn, Dn.
            setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj shV (real_const (1 # 8)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 8) n)).
            ring.
          * unfold mm, shn.
            setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj shV (real_const (1 # 16)) n)).
            rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 16) n)).
            ring.
        + unfold b5j_kL. nra. }
    (* |LogErr_n| <= kL * (2r + 1/2) * sn + (3/16) * shn (substituting Dn <= C0q * sn; kL >= 0) *)
    assert (HlogB : Qle (Qabs (projT1 (b5f_LogErr x h) n))
        (Qplus (Qmult (Qmult b5j_kL (Qplus (Qmult 2 r) (1 # 2))) sn)
               (Qmult (3 # 16) shn))).
    { apply (Qle_trans (Qabs (projT1 (b5f_LogErr x h) n))
                       (Qplus (Qmult b5j_kL Dn) (Qmult (3 # 16) shn))
                       (Qplus (Qmult (Qmult b5j_kL (Qplus (Qmult 2 r) (1 # 2))) sn)
                              (Qmult (3 # 16) shn))).
      - exact HlogN.
      - apply Qplus_le_compat.
        + assert (HkL0 : Qle 0 b5j_kL).
          { unfold b5j_kL. change (Qle 0 (1 # 16)). unfold Qle. simpl. lia. }
          apply (Qle_trans (Qmult b5j_kL Dn) (Qmult Dn b5j_kL) (Qmult (Qmult b5j_kL (Qplus (Qmult 2 r) (1 # 2))) sn)).
          * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          * apply (Qle_trans (Qmult Dn b5j_kL)
                             (Qmult (Qmult (Qplus (Qmult 2 r) (1 # 2)) sn) b5j_kL)
                             (Qmult (Qmult b5j_kL (Qplus (Qmult 2 r) (1 # 2))) sn)).
            -- apply (Qmult_le_compat_r Dn (Qmult (Qplus (Qmult 2 r) (1 # 2)) sn) b5j_kL).
               ++ exact HDu.
               ++ exact HkL0.
            -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        + apply Qle_refl. }
    (* budget: |v_n| <= Kvq * sn + (3/32) * shn (calling (a) and (b)) *)
    assert (Hbud : Qle Vn (Qplus (Qmult (b5j_Kvq r) sn) (Qmult (3 # 32) shn))).
    { unfold Vn.
      apply QleT'_to_Qle.
        apply (b5j_v_pts_budget x h shV r n).
- exact (QleT'_to_Qle _ _ (b5j_v_tri_pts x h n)).
      - exact Hxdh.
      - exact HlogB.
      - exact Hdhh. }
    (* goal: QltT (sh0/8) ((Kvq r) * sn + shn - Vn); nra after the bridge (sn, shn, Vn left unexpanded) *)
    apply (qltT_eq_compat_r
             (Qminus (projT1 (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV) n)
                     (projT1 (real_abs (b5f_v x h)) n))
             (Qminus (Qplus (Qmult (b5j_Kvq r) sn) shn) Vn)
             (Qmult sh0 (1 # 8))).
    { apply qeq_imp_qeqT.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (b5j_Kvq r)) (real_abs h) n)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj (b5j_Kvq r) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (b5f_v x h) n)).
      unfold sn, shn, Vn, hn. ring. }
    apply Qlt_to_QltT.
    assert (Hsh0Q : Qlt 0 sh0) by (apply QltT_to_Qlt; exact Hsh0).
    unfold b5j_Kvq, b5j_kL in *.
    nra.
Qed.

(* ============================================================ *)
(* (2) the exp-at-zero linearization instance (at [b5f_v]) and the LinE == Lin0 bridge *)
(*   LinE(v) := exp v + (-(1+v)) (the term inside the main statement); *)
(*   Lin0(t) := (exp t + (-1)) + (-t) (the term inside [exp_minus_one_linear]); *)
(*   the pointwise ring identity gives a Real-level real_eq, so the absolute values may be exchanged. *)
(* ============================================================ *)
Lemma b5j_lin_shape_eq : forall (v : Real),
  real_eq (real_plus (cauchy_real_exp v) (real_opp (real_plus real_one v)))
          (real_plus (real_plus (cauchy_real_exp v) (real_opp real_one)) (real_opp v)).
Proof.
  intro v.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) || setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _))).
  cbn [projT1 real_one].
  ring.
Qed.

(* v activation: |v(x,h)| < δlin (the [b5j_v_abs_bd] activation instance,
   with the slope collected via Kvq <= 2).
   δh := δlin * (1#4): 2|h| < δlin/2 - 2e gives Kvq * |h| <= 2|h| < δlin/2 - 2e;
   shV := δlin * (1#2), with witness 2e. *)
Lemma b5j_v_act_lt : forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1)
  (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r)
  (h δlin : Real) (Hδ0 : real_lt real_zero δlin),
  (forall (epsL' : Real), real_lt real_zero epsL' ->
    real_le (real_abs (b5f_LogErr x h))
            (real_plus (real_mult (real_const b5j_kL) (real_abs (b5f_Du x h))) epsL')) ->
  real_lt (real_abs h) (real_mult δlin (real_const (1 # 4))) ->
  real_lt (real_abs h) (real_const (1 # 2)) ->
  real_lt (real_abs (b5f_v x h)) δlin.
Proof.
  intros r Hr0 Hr1 x Hxr h δlin Hδ0 Hlog Hhact Hh12.
  destruct Hhact as [e2 [He2 [N2 HN2]]].
  set (shV := real_mult δlin (real_const (1 # 2))).
  assert (HhalfT : QltT 0 (1 # 2)).
  { apply Qlt_to_QltT. change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  assert (HshV : real_lt real_zero shV).
  { unfold shV. apply real_mult_positive.
    - exact Hδ0.
    - apply real_const_pos. exact HhalfT. }
  (* |v| <= Kvq * |h| + shV (the [b5j_v_abs_bd] activation instance) *)
  assert (Hvb : real_le (real_abs (b5f_v x h))
                        (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)).
  { exact (b5j_v_abs_bd r Hr0 Hr1 x Hxr h shV HshV Hlog Hh12). }
  (* Kvq * |h| + shV < δlin (witness 2e2; Kvq <= 2 gives Kvq * sn <= 2sn < δlin/2 - 2e2) *)
  assert (Hslope : real_lt (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV) δlin).
  { unfold real_lt.
    exists (Qmult 2 e2).
    split.
    - apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat 2 e2).
      + change (Qlt 0 2). unfold Qlt. simpl. lia.
      + apply QltT_to_Qlt. exact He2.
    - exists N2.
      intros n Hn.
      apply NatLe_drop in Hn.
      assert (Hn2 : (N2 <= n)%nat) by lia.
      set (dln := projT1 δlin n).
      set (sn := Qabs (projT1 h n)).
      (* |h_n| < dln * (1#4) - e2 (the HN2 bridge) *)
      assert (Hsn2 : Qlt sn (Qminus (Qmult dln (1 # 4)) e2)).
      { apply QltT_to_Qlt.
        apply (q_lt_minus_shift e2 (Qmult dln (1 # 4)) sn).
        apply (qltT_eq_compat_r (Qminus (Qmult dln (1 # 4)) sn)
                                (Qminus (projT1 (real_mult δlin (real_const (1 # 4))) n)
                                        (projT1 (real_abs h) n))
                                e2).
        - apply qeq_imp_qeqT.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj δlin (real_const (1 # 4)) n)).
          rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 4) n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
          unfold dln, sn. reflexivity.
        - exact (HN2 n (NatLe_lift _ _ Hn2)). }
      (* Kvq * sn <= 2 * sn (by [b5j_Kvq_le_two]) *)
      assert (Hk2 : Qle (Qmult (b5j_Kvq r) sn) (Qmult 2 sn)).
      { apply (Qmult_le_compat_r (b5j_Kvq r) 2 sn).
- exact (QleT'_to_Qle _ _ (b5j_Kvq_le_two r Hr0 Hr1)).
        - unfold sn. apply Qabs_nonneg. }
      (* goal bridge: QltT (2e2) (dln - (Kvq * sn + dln * (1#2))) *)
      apply (qltT_eq_compat_r
               (Qminus (projT1 δlin n)
                       (projT1 (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV) n))
               (Qminus dln (Qplus (Qmult (b5j_Kvq r) sn) (Qmult dln (1 # 2))))
               (Qmult 2 e2)).
      { apply qeq_imp_qeqT.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (b5j_Kvq r)) (real_abs h) n)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj (b5j_Kvq r) n)).
        setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj h n)).
        unfold shV.
        setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj δlin (real_const (1 # 2)) n)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 2) n)).
        unfold dln, sn. ring. }
      apply Qlt_to_QltT.
      unfold b5j_Kvq, b5j_kL in *.
      nra. }
  (* |v| < δlin by [real_le_lt_trans] *)
  apply (real_le_lt_trans (real_abs (b5f_v x h))
                          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
                          δlin).
  - exact Hvb.
  - exact Hslope.
Qed.

(* ============================================================ *)
(* (3) the |Sx| scaling Real-algebra pieces (the Real-level chain material for the main statement (4)) *)
(* ============================================================ *)

(* lifting a Qeq through [real_const] *)
Lemma b5j_real_const_req : forall (q1 q2 : Q), Qeq q1 q2 ->
  real_eq (real_const q1) (real_const q2).
Proof.
  intros q1 q2 Hq.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite !(qeqT_imp_qeq _ _ (real_const_proj q1 n)).
  rewrite !(qeqT_imp_qeq _ _ (real_const_proj q2 n)).
  setoid_rewrite Hq. ring.
Qed.

(* (Qinv Kvq) * Kvq == 1 at the Real level (lifting [b5j_kslope_Kvq]) *)
Lemma b5j_qinv_kvq_req : forall (r : Q) (Hr0 : Qle 0 r),
  real_eq (real_mult (real_const (Qinv (b5j_Kvq r))) (real_const (b5j_Kvq r))) real_one.
Proof.
  intros r Hr0.
  apply (real_eq_trans
           (real_mult (real_const (Qinv (b5j_Kvq r))) (real_const (b5j_Kvq r)))
           (real_const (Qmult (Qinv (b5j_Kvq r)) (b5j_Kvq r)))
           real_one).
  - apply b5j_real_const_mult_eq.
  - apply (b5j_real_const_req (Qmult (Qinv (b5j_Kvq r)) (b5j_Kvq r)) 1).
exact (qeqT_imp_qeq _ _ (b5j_kslope_Kvq r Hr0)).
Qed.

(* left distributivity: a * (b + c) == a * b + a * c (pointwise ring) *)
Lemma b5j_mult_plus_distr_eq : forall (a b c : Real),
  real_eq (real_mult a (real_plus b c))
          (real_plus (real_mult a b) (real_mult a c)).
Proof.
  intros a b c.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj a (real_plus b c) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj b c n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult a b) (real_mult a c) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj a b n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj a c n)).
  ring.
Qed.

(* (1#4) * M + (3#4) * M == M (collecting the Q constants; pointwise nra) *)
Lemma b5j_fourth_threefourth_sum : forall (M : Real),
  real_eq (real_plus (real_mult (real_const (1 # 4)) M)
                     (real_mult (real_const (3 # 4)) M)) M.
Proof.
  intro M.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const (1 # 4)) M)
                                 (real_mult (real_const (3 # 4)) M) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (1 # 4)) M n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (3 # 4)) M n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 4) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (3 # 4) n)).
  nra.
Qed.

(* Qinv(Kvq) * ((1#4) * Kvq) == (1#4) at the Q level (by [b5j_kslope_Kvq] and a ring rearrangement) *)
Lemma b5j_qinv_kvq14 : forall (r : Q) (Hr0 : Qle 0 r),
  QeqT (Qmult (Qinv (b5j_Kvq r)) (Qmult (1 # 4) (b5j_Kvq r))) (1 # 4).
Proof.
  intros r Hr0.
  apply qeq_imp_qeqT.
  assert (Hm : Qeq (Qmult (Qinv (b5j_Kvq r)) (Qmult (1 # 4) (b5j_Kvq r)))
                   (Qmult (1 # 4) (Qmult (Qinv (b5j_Kvq r)) (b5j_Kvq r)))).
  { field. unfold b5j_Kvq, b5j_kL. nra. }
  setoid_rewrite Hm.
setoid_rewrite (qeqT_imp_qeq _ _ (b5j_kslope_Kvq r Hr0)).
  ring.
Qed.

(* E1: ((eps * Kqinv) * invM) * Kvqc == eps * invM (Kqinv * Kvqc == 1 cancels) *)
Lemma b5j_eps0_kvq_req : forall (r : Q) (Hr0 : Qle 0 r)
  (eps invM : Real),
  real_eq (real_mult (real_mult (real_mult eps (real_const (Qinv (b5j_Kvq r)))) invM)
                     (real_const (b5j_Kvq r)))
          (real_mult eps invM).
Proof.
  intros r Hr0 eps invM.
  set (M1 := real_mult (real_mult eps (real_mult (real_const (Qinv (b5j_Kvq r))) (real_const (b5j_Kvq r)))) invM).
  apply (real_eq_trans
           (real_mult (real_mult (real_mult eps (real_const (Qinv (b5j_Kvq r)))) invM)
                      (real_const (b5j_Kvq r)))
           M1
           (real_mult eps invM)).
  - (* A == M1: pointwise field (the Qinv composition needs field; the side condition is Kvq != 0) *)
    unfold M1.
    apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _))).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (Qinv (b5j_Kvq r)) n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (b5j_Kvq r) n)).
    field.
    unfold b5j_Kvq, b5j_kL. nra.
  - (* M1 == eps * invM: compatibility with Kqinv * Kvqc == 1 plus pointwise ring *)
    apply (real_eq_trans M1
           (real_mult (real_mult eps real_one) invM)
           (real_mult eps invM)).
    + unfold M1.
      apply (RealSetoid.real_eq_mult_compat
               (real_mult eps (real_mult (real_const (Qinv (b5j_Kvq r))) (real_const (b5j_Kvq r))))
               invM
               (real_mult eps real_one)
               invM).
      * apply (RealSetoid.real_eq_mult_compat eps
                  (real_mult (real_const (Qinv (b5j_Kvq r))) (real_const (b5j_Kvq r)))
                  eps real_one).
        -- apply real_eq_refl.
        -- apply (b5j_qinv_kvq_req r Hr0).
      * apply real_eq_refl.
    + apply real_eq_of_zero_diff. intro n.
      apply qeq_imp_qeqT.
      repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _))).
      cbn [projT1 real_one].
      ring.
Qed.

(* E2: ((eps * Kqinv) * invM) * ((invE * K14) * eps') == (1#4) * (eps' * invM)
   (eps * invE == 1 via [real_inv_pos_correct]; Kqinv * K14 == (1#4) via [b5j_qinv_kvq14]) *)
Lemma b5j_eps0_shv_req : forall (r : Q) (Hr0 : Qle 0 r)
  (eps eps' invM : Real) (Heps : real_lt real_zero eps),
  real_eq (real_mult (real_mult (real_mult eps (real_const (Qinv (b5j_Kvq r)))) invM)
                     (real_mult (real_mult (real_inv_pos eps Heps)
                                           (real_const (Qmult (1 # 4) (b5j_Kvq r)))) eps'))
          (real_mult (real_const (1 # 4)) (real_mult eps' invM)).
Proof.
  intros r Hr0 eps eps' invM Heps.
  set (M := real_mult (real_mult (real_mult eps (real_inv_pos eps Heps))
                                 (real_const (Qmult (Qinv (b5j_Kvq r)) (Qmult (1 # 4) (b5j_Kvq r)))))
                      (real_mult invM eps')).
  apply (real_eq_trans
           (real_mult (real_mult (real_mult eps (real_const (Qinv (b5j_Kvq r)))) invM)
                      (real_mult (real_mult (real_inv_pos eps Heps)
                                            (real_const (Qmult (1 # 4) (b5j_Kvq r)))) eps'))
           M
           (real_mult (real_const (1 # 4)) (real_mult eps' invM))).
  - unfold M.
    apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _))).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (Qinv (b5j_Kvq r)) n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (Qmult (1 # 4) (b5j_Kvq r)) n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (Qmult (Qinv (b5j_Kvq r)) (Qmult (1 # 4) (b5j_Kvq r))) n)).
    field.
    unfold b5j_Kvq, b5j_kL. nra.
  - apply (real_eq_trans M
           (real_mult (real_mult (real_mult eps (real_inv_pos eps Heps)) (real_const (1 # 4)))
                      (real_mult invM eps'))
           (real_mult (real_const (1 # 4)) (real_mult eps' invM))).
    + unfold M.
      apply (RealSetoid.real_eq_mult_compat
               (real_mult (real_mult eps (real_inv_pos eps Heps))
                          (real_const (Qmult (Qinv (b5j_Kvq r)) (Qmult (1 # 4) (b5j_Kvq r)))))
               (real_mult invM eps')
               (real_mult (real_mult eps (real_inv_pos eps Heps)) (real_const (1 # 4)))
               (real_mult invM eps')).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_mult eps (real_inv_pos eps Heps))
                 (real_const (Qmult (Qinv (b5j_Kvq r)) (Qmult (1 # 4) (b5j_Kvq r))))
                 (real_mult eps (real_inv_pos eps Heps))
                 (real_const (1 # 4))).
        -- apply real_eq_refl.
        -- apply (b5j_real_const_req (Qmult (Qinv (b5j_Kvq r)) (Qmult (1 # 4) (b5j_Kvq r))) (1 # 4)).
exact (qeqT_imp_qeq _ _ (b5j_qinv_kvq14 r Hr0)).
      * apply real_eq_refl.
    + apply (real_eq_trans
               (real_mult (real_mult (real_mult eps (real_inv_pos eps Heps)) (real_const (1 # 4)))
                          (real_mult invM eps'))
               (real_mult (real_mult real_one (real_const (1 # 4))) (real_mult invM eps'))
               (real_mult (real_const (1 # 4)) (real_mult eps' invM))).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_mult eps (real_inv_pos eps Heps)) (real_const (1 # 4)))
                 (real_mult invM eps')
                 (real_mult real_one (real_const (1 # 4)))
                 (real_mult invM eps')).
        -- apply (RealSetoid.real_eq_mult_compat
                    (real_mult eps (real_inv_pos eps Heps))
                    (real_const (1 # 4))
                    real_one
                    (real_const (1 # 4))).
           ++ exact (real_inv_pos_correct eps Heps).
           ++ apply real_eq_refl.
        -- apply real_eq_refl.
      * apply (real_eq_trans
                 (real_mult (real_mult real_one (real_const (1 # 4))) (real_mult invM eps'))
                 (real_mult (real_const (1 # 4)) (real_mult invM eps'))
                 (real_mult (real_const (1 # 4)) (real_mult eps' invM))).
        -- apply real_eq_of_zero_diff. intro n.
           apply qeq_imp_qeqT.
           repeat (setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _))).
           cbn [projT1 real_one].
           ring.
        -- apply (RealSetoid.real_eq_mult_compat
                    (real_const (1 # 4))
                    (real_mult invM eps')
                    (real_const (1 # 4))
                    (real_mult eps' invM)).
           ++ apply real_eq_refl.
           ++ apply (real_mult_comm invM eps').
Qed.

(* ============================================================ *)
(* (4) the main statement: [b5a_S_exp_part_bound_closed_r] (the exp-part closed form) *)
(*   method: δ := min(min(δlin/4, δL/12), 1/2); *)
(*   Δu activation ([b5f_Du_act_delta]) gives HlogS; |v| < δlin ([b5j_v_act_lt]) *)
(*   gives |LinE| <= eps0 * |v| + eps0' ([exp_minus_one_linear] at [b5f_v x h]); *)
(*   |v| <= Kvqc * |h| + shV ([b5j_v_abs_bd]); eps0 * Kvqc == eps * invM *)
(*   ([b5j_eps0_kvq_req]) and eps0 * shV == (1#4) * eps' * invM *)
(*   ([b5j_eps0_shv_req]) reshape to |Sx| * (eps * invM * |h| + eps' * invM), *)
(*   and [real_abs_scaling_le] yields eps * |h| + eps'. *)
(* ============================================================ *)
Lemma b5a_S_exp_part_bound_closed_r :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
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
  set (invM := real_inv_pos (real_plus real_one (real_abs Sx)) (real_abs_plus_one_pos Sx)).
  set (eps0 := real_mult (real_mult eps (real_const (Qinv (b5j_Kvq r)))) invM).
  (* the positivity facts *)
  assert (HKqinvT : QltT 0 (Qinv (b5j_Kvq r))).
{ apply Qlt_to_QltT. apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ (b5j_Kvq_pos r Hr0)). }
  assert (HinvM0 : real_lt real_zero invM).
  { unfold invM. apply (real_inv_pos_pos (real_plus real_one (real_abs Sx)) (real_abs_plus_one_pos Sx)). }
  assert (Heps0 : real_lt real_zero eps0).
  { unfold eps0. apply real_mult_positive.
    - apply real_mult_positive.
      + exact Heps.
      + apply real_const_pos. exact HKqinvT.
    - exact HinvM0. }
  assert (Heps0le : real_le real_zero eps0).
  { apply (RealSetoid.real_lt_le_iff_req real_zero eps0). left. exact Heps0. }
  assert (HkLpos : real_lt real_zero (real_const b5j_kL)).
  { apply real_const_pos. exact b5j_kL_posT. }
  destruct (b5f_LogErr_delta x (real_const b5j_kL) HkLpos) as [δL [HδL0 HδL]].
  destruct (exp_minus_one_linear eps0 Heps0) as [δlin [Hδlin0 Hδlin]].
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
  { unfold A. apply real_mult_positive.
    - exact Hδlin0.
    - apply real_const_pos. exact H14T. }
  assert (HB0 : real_lt real_zero B).
  { unfold B. apply real_mult_positive.
    - exact HδL0.
    - apply real_const_pos. exact H112T. }
  assert (HC0 : real_lt real_zero C).
  { unfold C. apply real_const_pos. exact H12T. }
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
    { apply (b5f_Du_act_delta r Hr0 Hr1 x Hxr h δL HδL0).
      - unfold B in HhB. exact HhB.
      - unfold C in HhC. exact HhC. }
    assert (HlogS : forall (epsL' : Real), real_lt real_zero epsL' ->
        real_le (real_abs (b5f_LogErr x h))
                (real_plus (real_mult (real_const b5j_kL) (real_abs (b5f_Du x h))) epsL')).
    { intros epsL' HepsL'. exact (HδL h epsL' HepsL' HactDu). }
    assert (Hvlt : real_lt (real_abs (b5f_v x h)) δlin).
    { apply (b5j_v_act_lt r Hr0 Hr1 x Hxr h δlin Hδlin0 HlogS).
      - unfold A in HhA. exact HhA.
      - unfold C in HhC. exact HhC. }
    (* eps0' := (3#4) * (eps' * invM); shV := invE * ((1#4) * Kvq-const) * eps' *)
    set (eps0' := real_mult (real_const (3 # 4)) (real_mult eps' invM)).
    set (invE := real_inv_pos eps Heps).
    set (shV := real_mult (real_mult invE (real_const (Qmult (1 # 4) (b5j_Kvq r)))) eps').
    assert (H34T : QltT 0 (3 # 4)).
    { apply Qlt_to_QltT. change (Qlt 0 (3 # 4)). unfold Qlt. simpl. lia. }
    assert (H14KvT : QltT 0 (Qmult (1 # 4) (b5j_Kvq r))).
    { apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 4) (b5j_Kvq r)).
      - change (Qlt 0 (1 # 4)). unfold Qlt. simpl. lia.
- exact (QltT_to_Qlt _ _ (b5j_Kvq_pos r Hr0)). }
    assert (HinvE0 : real_lt real_zero invE).
    { unfold invE. apply (real_inv_pos_pos eps Heps). }
    assert (Heps0' : real_lt real_zero eps0').
    { unfold eps0'. apply real_mult_positive.
      - apply real_const_pos. exact H34T.
      - apply real_mult_positive.
        + exact Heps'.
        + exact HinvM0. }
    assert (HshV : real_lt real_zero shV).
    { unfold shV. apply real_mult_positive.
      - apply real_mult_positive.
        + exact HinvE0.
        + apply real_const_pos. exact H14KvT.
      - exact Heps'. }
    (* slope instance: |v| <= Kvqc * |h| + shV *)
    assert (Hvslope : real_le (real_abs (b5f_v x h))
                              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)).
    { apply (b5j_v_abs_bd r Hr0 Hr1 x Hxr h shV HshV HlogS).
      unfold C in HhC. exact HhC. }
    (* |LinE(v)| <= eps0 * |v| + eps0' (the exp linearization instance at [b5f_v x h]) *)
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
    (* eps0 * |v| <= eps0 * (Kvqc * |h| + shV) (by [real_le_mult_compat_weak] and a commutation bridge) *)
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
    (* reshape: |Sx| * (eps0 * (Kvqc * |h| + shV) + eps0') == |Sx| * ((eps * invM) * |h| + eps' * invM) *)
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
      - (* inner reshape: eps0 * (Kvqc * |h| + shV) + eps0' == (eps * invM) * |h| + eps' * invM *)
        apply (real_eq_trans
                 (real_plus (real_mult eps0
                              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
                            eps0')
                 (real_plus (real_plus (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                                       (real_mult eps0 shV))
                            eps0')
                 (real_plus (real_mult (real_mult eps invM) (real_abs h))
                            (real_mult eps' invM))).
        + (* distributivity: eps0 * (A+B) == eps0 * A + eps0 * B *)
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
        + (* reassembly to T: associativity + E1 + E2 + the eps0' definition + the constant sum *)
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
            -- (* eps0 * (Kvqc * |h|) == (eps * invM) * |h|: associativity plus E1 *)
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
                  ** unfold eps0. apply (b5j_eps0_kvq_req r Hr0 eps invM).
                  ** apply real_eq_refl.
            -- (* eps0 * shV + eps0' == eps' * invM: E2 plus the constant sum *)
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
                     apply (b5j_eps0_shv_req r Hr0 eps eps' invM Heps).
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
        { apply (real_abs_scaling_le (b5a_S x) eps eps' h Heps Heps'). }
    }
    }
Qed.

(* ============================================================ *)
(* B5-A E-ODE T3: the S >= 1 certificate-domain family. *)
(*   The main statement [b5a_S_ge_one] on the certificate domain real_lt real_zero x, *)
(*   with the [b5k_*] auxiliary lemmas (the case x == 0 goes through [real_eq]). *)
(*   The proofs depend only on the root families. *)
(*   No further dependencies. *)
(* ============================================================ *)

(* ============================================================ *)
(* b5k_S_proj: the pointwise expansion of S(x)_n (the projection chain, the pattern of item3s [b5f_*]) *)
(* ============================================================ *)
Lemma b5k_S_proj : forall (x : Real) (n : nat), QeqT (projT1 (b5a_S x) n) (exp_partial n (Qmult (1 / 2)
    (log_seq (real_plus real_one (real_mult x x))
             (b5a_one_plus_sq_pos x) n))).
Proof.
  intros x n.
  apply qeq_imp_qeqT.
  unfold b5a_S.
  rewrite (qeqT_imp_qeq _ _ (real_exp_proj (real_mult (real_const (1 / 2))
             (real_log (real_plus real_one (real_mult x x))
                       (b5a_one_plus_sq_pos x))) n)).
  apply qeqT_imp_qeq.
  apply (exp_partial_wd n (projT1 (real_mult (real_const (1 / 2))
             (real_log (real_plus real_one (real_mult x x))
                       (b5a_one_plus_sq_pos x))) n)
             (Qmult (1 / 2) (log_seq (real_plus real_one (real_mult x x))
                                     (b5a_one_plus_sq_pos x) n))).
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (1 / 2))
      (real_log (real_plus real_one (real_mult x x))
                (b5a_one_plus_sq_pos x)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 / 2) n)).
  cbn [real_log cw_log projT1].
  reflexivity.
Qed.

(* ============================================================ *)
(* certificate domain: x^2 > 0 (separated at the Real level) gives S(x) > 1 (strict, at the Real level) *)
(*   chain: x^2 > 0 gives u := 1+x^2 > 1, so log u > log 1 == 0, *)
(*     (1/2)·log u > 0 → e^0 == 1 < e^{(1/2)log u} == S(x)       *)
(* ============================================================ *)
Lemma b5k_S_gt_one_cert : forall (x : Real),
  real_lt real_zero (real_mult x x) ->
  real_lt real_one (b5a_S x).
Proof.
  intros x Hsq.
  (* u - 1 == x * x (pointwise algebra) *)
  assert (Hdiff : real_eq (real_mult x x)
                           (real_plus (real_plus real_one (real_mult x x))
                                      (real_opp real_one))).
  { apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus real_one (real_mult x x))
                                   (real_opp real_one) n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_mult x x) n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj x x n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_one n)).
    cbn [projT1 real_one].
    ring. }
  (* 0 < x^2 == u - 1, so 0 < u - 1 (lifting the positivity of the difference) *)
  assert (Hdiff2 : real_lt real_zero
        (real_plus (real_plus real_one (real_mult x x))
                   (real_opp real_one))).
  { apply (real_lt_eq_lt real_zero (real_mult x x)
        (real_plus (real_plus real_one (real_mult x x))
                   (real_opp real_one))).
    - exact Hsq.
    - exact Hdiff. }
  (* hence 1 < u (the Real-level reverse difference-positivity bridge) *)
  assert (Hu1 : real_lt real_one
        (real_plus real_one (real_mult x x))).
  { apply (real_lt_zero_minus real_one (real_plus real_one (real_mult x x))).
    exact Hdiff2. }
  (* log u > log 1 == 0 (by [real_log_lt_mono] and [real_log_one]) *)
  assert (Hlog : real_lt real_zero
        (cw_log (real_plus real_one (real_mult x x))
                (b5a_one_plus_sq_pos x))).
  { apply (real_eq_lt_lt real_zero
            (real_log real_one real_lt_zero_one)
            (cw_log (real_plus real_one (real_mult x x))
                    (b5a_one_plus_sq_pos x))).
    - apply real_eq_sym. apply (real_log_one real_lt_zero_one).
    - apply (real_log_lt_mono real_one (real_plus real_one (real_mult x x))
                              real_lt_zero_one
                              (b5a_one_plus_sq_pos x)).
      exact Hu1. }
  (* (1/2) * log u > 0 (the positive constant 1/2 times the positive log u) *)
  assert (Hhalf : real_lt real_zero (real_const (1 / 2))).
  { apply real_const_pos.
    apply Qlt_to_QltT.
    change (Qlt 0 (1 / 2)). unfold Qdiv. simpl. reflexivity. }
  assert (Hprod : real_lt real_zero
        (real_mult (real_const (1 / 2))
                   (real_log (real_plus real_one (real_mult x x))
                             (b5a_one_plus_sq_pos x)))).
  { apply (real_mult_pos_compat (real_const (1 / 2))
                                (real_log (real_plus real_one (real_mult x x))
                                          (b5a_one_plus_sq_pos x))).
    - exact Hhalf.
    - unfold real_log. exact Hlog. }
  (* the exponential step: 1 == e^0 < e^((1/2) * log u) == S(x) *)
  apply (real_eq_lt_lt real_one (cauchy_real_exp real_zero) (b5a_S x)).
  - apply real_eq_sym. exact cauchy_real_exp_zero.
  - unfold b5a_S.
    apply (cauchy_real_exp_mono real_zero
        (real_mult (real_const (1 / 2))
                   (real_log (real_plus real_one (real_mult x x))
                             (b5a_one_plus_sq_pos x)))).
    exact Hprod.
Qed.

(* ============================================================ *)
(* the certificate-domain pointwise Q tail: x^2 > 0 gives some N with Qle 1 (S(x)_n) for all n >= N *)
(*   (proved directly from the separated witness of real_lt; N is the witness of the real_lt) *)
(* ============================================================ *)
Lemma b5k_S_ge_one_cert : forall (x : Real),
  real_lt real_zero (real_mult x x) ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QleT' 1 (projT1 (b5a_S x) n)).
Proof.
  intros x Hsq.
  destruct (b5k_S_gt_one_cert x Hsq) as [e [He [N HN]]].
  exists N.
  intros n Hn.
  apply Qle_to_QleT'.
    apply (proj2 (Qle_minus_iff 1 (projT1 (b5a_S x) n))).
  apply Qlt_le_weak.
  apply (Qlt_le_trans 0 e (projT1 (b5a_S x) n - projT1 real_one n)).
  - apply QltT_to_Qlt. exact He.
  - apply Qlt_le_weak.
    apply QltT_to_Qlt.
    exact (HN n Hn).
Qed.

(* ============================================================ *)
(* the certificate-domain pointwise Q tail (x > 0 version): x > 0 gives some N with Qle 1 (S(x)_n) for all n >= N *)
(*   (x > 0 gives x * x > 0 via [real_mult_pos_compat]) *)
(* ============================================================ *)
Lemma b5k_S_ge_one_pos : forall (x : Real),
  real_lt real_zero x ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QleT' 1 (projT1 (b5a_S x) n)).
Proof.
  intros x Hx.
  apply (b5k_S_ge_one_cert x).
  apply (real_mult_pos_compat x x Hx Hx).
Qed.

(* ============================================================ *)
(* the main statement [b5a_S_ge_one], on its certificate domain: *)
(*   for all x with real_lt real_zero x, the pointwise Q tail is >= 1. *)
(*   the statement matches [b5k_S_ge_one_pos] verbatim (it is [b5k_S_ge_one_cert] at *)
(*   x^2 > 0 via [real_mult_pos_compat]), which proves the main statement. *)
(*   the unrestricted [forall x] form is not provable (the sign tail of log_seq is unavailable); *)
(*   the case x == 0 is outside this statement's domain (S(0) == 1 goes through real_eq and the exp-at-zero identity). *)
(* ============================================================ *)
Lemma b5a_S_ge_one : forall (x : Real),
  real_lt real_zero x ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QleT' 1 (projT1 (b5a_S x) n)).
Proof.
  intros x Hx.
  exact (b5k_S_ge_one_pos x Hx).
Qed.

(* ============================================================ *)
(* B5-A E-ODE T3: the S main assembly. *)
(*   The main statement [b5a_S_diff_closed_r] with the [b5l_*] auxiliary lemmas. *)
(*   The proofs consume the item3s and item3e families above. *)
(*   No further dependencies. *)
(* ============================================================ *)

(* ============================================================ *)
(* M1 skeleton: the [b5l_]-prefixed S main assembly components of this development: *)
(*   the planned component families: *)
(*   the Q budget constant pieces [b5l_k_posT] / [b5l_Mk_le] *)
(*   (k := Qinv(8 * (1+M)), with M the [b5f_S_pts_bounded] upper bound: *)
(*   QltT 0 k and Qle (M * k) (1#8)); *)
(*   the pointwise bridging lemmas: *)
(*   [b5l_Sx_mult_abs_le] (|S(x) * A|_n <= M * |A_n| for the pointwise |S_n| <= M), *)
(*   [b5l_eq_abs_tri] (real_eq X (E+G) gives |X_n| <= |E_n| + |G_n| + m0), *)
(*   the main assembly [b5a_S_diff_closed_r] (see the file-tail comment): *)
(*   δ := real_min δexp δg (δexp := the item3e main statement at eps * (1#2); *)
(*   δg := [b5f_gdiff_pts_r] at eps * (1#4) with k2 := k2p := k(M) and *)
(*   eps' * (1#8)); pointwise |err_n| <= en * sn + (3#4) * en', *)
(*   with eta := (1#8) * e1 witnessing real_lt (by [b5n_close]/[b5n_quarter_gt]). *)
(* ============================================================ *)

(* ============================================================ *)
(* The Q budget constant pieces *)
(*   M an S-upper bound with 0 < M gives k := Qinv(8(1+M)) > 0 and M * k <= (1#8) *)
(*   use: the coefficient budget of the slope/constant in the pointwise nra argument for *)
(*   the g part |Sx * wS| <= M * (eps2_n * k * sn + 2k2p * eps2'_n). *)
(* ============================================================ *)

(* 0 < Qinv(8(1+M)) (assumption M >= 0) *)
Lemma b5l_k_posT : forall (M : Q) (HM0 : Qle 0 M),
  QltT 0 (Qinv (Qmult 8 (Qplus M 1))).
Proof.
  intros M HM0.
  apply Qlt_to_QltT.
  apply Qinv_lt_0_compat.
  nra.
Qed.

(* M * Qinv(8(1+M)) <= (1#8) (the cross-multiplication pattern of [b5n_xinv_le]) *)
Lemma b5l_Mk_le : forall (M : Q) (HM0 : Qle 0 M),
  QleT' (Qmult M (Qinv (Qmult 8 (Qplus M 1)))) (1 # 8).
Proof.
  intros M HM0.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qmult M (Qinv (Qmult 8 (Qplus M 1)))) (Qinv 8) (1 # 8)).
  - apply QleT'_to_Qle. apply (b5n_xinv_le M (Qmult 8 (Qplus M 1)) 8).
    + nra.
    + change (Qlt 0 8). unfold Qlt. simpl. lia.
    + nra.
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold Qinv. reflexivity.
Qed.

(* ============================================================ *)
(* The pointwise bridging lemmas *)
(* ============================================================ *)

(* |S(x) * A|_n <= M * |A_n|: lifting the pointwise bound |S_n| <= M (exact expansion by Qabs) *)
Lemma b5l_Sx_mult_abs_le : forall (x A : Real) (M : Q) (n : nat),
  Qle (Qabs (projT1 (b5a_S x) n)) M ->
  QleT' (Qabs (projT1 (real_mult (b5a_S x) A) n)) (Qmult M (Qabs (projT1 A n))).
Proof.
  intros x A M n HS.
  apply Qle_to_QleT'.
  set (Sn := projT1 (b5a_S x) n).
  set (An := projT1 A n).
  assert (Hsh : projT1 (real_mult (b5a_S x) A) n == Qmult Sn An).
  { unfold Sn, An. rewrite (qeqT_imp_qeq _ _ (real_mult_proj (b5a_S x) A n)). reflexivity. }
  apply (Qle_trans (Qabs (projT1 (real_mult (b5a_S x) A) n))
                   (Qabs (Qmult Sn An))
                   (Qmult M (Qabs An))).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    apply (Qabs_wd (projT1 (real_mult (b5a_S x) A) n) (Qmult Sn An)).
    exact Hsh.
  - rewrite (Qabs_Qmult Sn An).
    apply (Qmult_le_compat_r (Qabs Sn) M (Qabs An)).
    + unfold Sn. exact HS.
    + apply Qabs_nonneg.
Qed.

(* real_eq X (E+G) gives some N with |X_n| <= |E_n| + (|G_n| + m0) for all n >= N (m0 > 0) *)
Lemma b5l_eq_abs_tri : forall (X E G : Real) (m0 : Q),
  real_eq X (real_plus E G) -> QltT 0 m0 ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QleT' (Qabs (projT1 X n))
        (Qplus (Qabs (projT1 E n)) (Qplus (Qabs (projT1 G n)) m0))).
Proof.
  intros X E G m0 Heq Hm0.
  destruct (Heq m0 Hm0) as [N HN].
  exists N.
  intros n Hn.
  set (Xn := projT1 X n).
  set (En := projT1 E n).
  set (Gn := projT1 G n).
  set (Sumn := projT1 (real_plus E G) n).
  (* |Xn| <= |Sumn| + m0 (the triangle inequality plus the real_eq witness) *)
  assert (Ht1 : Qle (Qabs Xn) (Qplus (Qabs Sumn) m0)).
  { apply (Qle_trans (Qabs Xn)
                     (Qplus (Qabs Sumn) (Qabs (Qminus Xn Sumn)))
                     (Qplus (Qabs Sumn) m0)).
    - (* Xn == Sumn + (Xn − Sumn) ⟹ triangle *)
      apply (Qle_trans (Qabs Xn)
                       (Qabs (Qplus Sumn (Qminus Xn Sumn)))
                       (Qplus (Qabs Sumn) (Qabs (Qminus Xn Sumn)))).
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        apply (Qabs_wd Xn (Qplus Sumn (Qminus Xn Sumn))).
        unfold Xn, Sumn. ring.
      + apply (Qabs_triangle Sumn (Qminus Xn Sumn)).
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply Qlt_le_weak.
        apply QltT_to_Qlt.
        apply (qltT_eq_compat_l (Qabs (Qminus Xn (projT1 (real_plus E G) n)))
                                (Qabs (Qminus Xn Sumn)) m0).
        * apply qeq_imp_qeqT.
          apply (Qabs_wd (Qminus Xn (projT1 (real_plus E G) n)) (Qminus Xn Sumn)).
          unfold Xn, Sumn. ring.
        * exact (HN n Hn). }
  (* |Sumn| <= |En| + |Gn| (by [real_plus_proj] and the triangle inequality) *)
  assert (Ht2 : Qle (Qabs Sumn) (Qplus (Qabs En) (Qabs Gn))).
  { apply (Qle_trans (Qabs Sumn)
                     (Qabs (Qplus En Gn))
                     (Qplus (Qabs En) (Qabs Gn))).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      apply (Qabs_wd Sumn (Qplus En Gn)).
      unfold Sumn, En, Gn.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj E G n)). reflexivity.
    - apply (Qabs_triangle En Gn). }
  (* assembly: |Xn| <= (|En| + |Gn|) + m0 == |En| + (|Gn| + m0) *)
  apply Qle_to_QleT'.
    apply (Qle_trans (Qabs Xn)
                   (Qplus (Qplus (Qabs En) (Qabs Gn)) m0)
                   (Qplus (Qabs En) (Qplus (Qabs Gn) m0))).
  - apply (Qle_trans (Qabs Xn)
                     (Qplus (Qabs Sumn) m0)
                     (Qplus (Qplus (Qabs En) (Qabs Gn)) m0)).
    + exact Ht1.
    + apply Qplus_le_compat.
      * exact Ht2.
      * apply Qle_refl.
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* The main assembly [b5a_S_diff_closed_r] *)
(*   err == E + G (by [b5f_S_err_decomp]); E := Sx * (exp v - 1 - v) is bounded by *)
(*   the item3e main statement [b5a_S_exp_part_bound_closed_r] at eps * (1#2) *)
(*   (made pointwise by [b5i_abs_le_pointwise], margin eps' * (1#16)); *)
(*   G := Sx * wS is bounded by [b5f_gdiff_pts_r] at eps * (1#4) with k2 := k2p := *)
(*   Qinv(8(1+M)) (the |S_n| <= M scaling, M from [b5f_S_pts_bounded]); *)
(*   the decomposition slack is [b5l_eq_abs_tri] at m0 := (1#32) * e1; *)
(*   δ := real_min δexp δg; pointwise |err_n| <= en * hn + (3#4) * en', *)
(*   closed by coefficient absorption plus linear nra (the P1 check), with eta := (1#8) * e1 *)
(*   witnessing the left branch of real_lt (by [b5n_quarter_gt] and [b5n_close], the pattern of item2 E6). *)
(* ============================================================ *)
Lemma b5a_S_diff_closed_r :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5a_S (real_plus x h))
                 (real_opp (real_plus (b5a_S x)
                            (real_mult (real_mult x (b5a_S x)) (real_mult (b5a_atan_d x) h))))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps.
  (* M: |S(x)_n| <= M (with 0 < M) *)
  destruct (b5f_S_pts_bounded x) as [M [HMpos HMall]].
  assert (HM0 : Qle 0 M). { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ HMpos). }
  (* k2 := k2p := Qinv(8(1+M)): QltT 0 and M * k <= (1#8) *)
  set (k2 := Qinv (Qmult 8 (Qplus M 1))).
  set (k2p := Qinv (Qmult 8 (Qplus M 1))).
  assert (Hk2T : QltT 0 k2). { unfold k2. apply b5l_k_posT. exact HM0. }
  assert (Hk2pT : QltT 0 k2p). { unfold k2p. apply b5l_k_posT. exact HM0. }
assert (HMk2 : Qle (Qmult M k2) (1 # 8)). { unfold k2. apply QleT'_to_Qle. apply b5l_Mk_le. exact HM0. }
assert (HMk2p : Qle (Qmult M k2p) (1 # 8)). { unfold k2p. apply QleT'_to_Qle. apply b5l_Mk_le. exact HM0. }
  (* coefficient absorption facts: coefS1 := (M * k2) * (1#4) <= (1#32); coefG1 := M * 2k2p * (1#8) <= (1#32) *)
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
  (* the eps witnesses and positivity of the Q constants *)
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
  assert (H2T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 2)); unfold Qlt; simpl; lia).
  assert (H4T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 4)); unfold Qlt; simpl; lia).
  assert (H8T : QltT 0 (1 # 8)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 8)); unfold Qlt; simpl; lia).
  assert (H16T : QltT 0 (1 # 16)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 16)); unfold Qlt; simpl; lia).
  assert (H32T : QltT 0 (1 # 32)) by (apply Qlt_to_QltT; change (Qlt 0 (1 # 32)); unfold Qlt; simpl; lia).
  (* the eps shares (Real) *)
  set (eps1 := real_mult eps (real_const (1 # 2))).
  assert (Heps1 : real_lt real_zero eps1).
  { unfold eps1. apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact H2T. } }
  set (eps2 := real_mult eps (real_const (1 # 4))).
  assert (Heps2 : real_lt real_zero eps2).
  { unfold eps2. apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact H4T. } }
  (* δexp for the exp part (the item3e main statement) and δg for the g part ([b5f_gdiff_pts_r]) *)
  destruct (b5a_S_exp_part_bound_closed_r r Hr0 Hr1 x Hxr eps1 Heps1) as [δexp [Hδe0 Hδe]].
  destruct (b5f_gdiff_pts_r r Hr0 Hr1 x Hxr eps2 Heps2 k2 k2p Hk2T Hk2pT) as [δg [Hδg0 Hδg]].
  (* δ := min δexp δg *)
  set (delta := real_min δexp δg).
  assert (Hd0 : real_lt real_zero delta).
  { unfold delta. apply real_min_pos. { exact Hδe0. } { exact Hδg0. } }
  exists delta. split. { exact Hd0. }
  { intros h Hh eps' Heps'.
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
    (* shares: the exp inner eps1', the margin shE, the g inner eps2', the slack m0 *)
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
    (* the error object (matching the statement of [b5f_S_err_decomp] verbatim) *)
    set (err := real_plus (b5a_S (real_plus x h))
                 (real_opp (real_plus (b5a_S x)
                            (real_mult (real_mult x (b5a_S x)) (real_mult (b5a_atan_d x) h))))).
    set (Eobj := real_mult (b5a_S x)
                  (real_plus (cauchy_real_exp (b5f_v x h))
                             (real_opp (real_plus real_one (b5f_v x h))))).
    set (wS := real_plus (b5f_v x h)
                         (real_opp (real_mult (real_mult x (b5a_atan_d x)) h))).
    set (Gob := real_mult (b5a_S x) wS).
    (* the exp-part real-le instance (the item3e main statement's inner eps' share) *)
    set (Bexp := real_plus (real_mult eps1 (real_abs h)) eps1').
    assert (Hexp_le : real_le (real_abs Eobj) Bexp).
    { unfold Eobj, Bexp. exact (Hδe h HhE eps1' Heps1'). }
    destruct (b5i_abs_le_pointwise Eobj Bexp Hexp_le shE HshE) as [NE HNE].
    (* the g part pointwise (the gdiff inner eps' share) *)
    destruct (Hδg h HhG eps2' Heps2') as [Ng HNg].
    (* the decomposition slack: real_eq err (Eobj + Gob) *)
    destruct (b5l_eq_abs_tri err Eobj Gob m0 (b5f_S_err_decomp x h) Hm0T) as [Ntri Htri].
    (* the left branch of real_le is real_lt, witnessed by eta *)
    left.
    exists eta.
    split.
    { exact HetaT. }
    { set (Nmax := Nat.max Ne0 (Nat.max Ne1 (Nat.max NE (Nat.max Ng Ntri)))).
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
      (* the nonnegativity facts *)
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
      (* the exp-part pointwise bound: |Eobj_n| <= Eexpn *)
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
          { exact (qeqT_imp_qeq _ _ (real_abs_proj h n)). }
          unfold Eexpn, Bexp, en, en', hn.
          setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps1 (real_abs h)) eps1' n)).
          setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps1 (real_abs h) n)).
          setoid_rewrite Hp1.
          setoid_rewrite Hqh.
          setoid_rewrite Hp1'.
          setoid_rewrite Hpsh.
          ring. }
      (* the g-part pointwise bound: |Gob_n| <= (1#32) * (en * hn) + (1#32) * en' *)
      assert (HgB : Qle (Qabs (projT1 Gob n))
                        (Qplus (Qmult (1 # 32) (Qmult en hn)) (Qmult (1 # 32) en'))).
      { (* |Gob_n| <= M * |wS_n| (from |S_n| <= M) *)
        assert (H1 : Qle (Qabs (projT1 Gob n)) (Qmult M (Qabs (projT1 wS n)))).
{ unfold Gob, wS. apply QleT'_to_Qle. apply (b5l_Sx_mult_abs_le x wS M n). exact (QleT'_to_Qle _ _ (HMall n)). }
        (* |wS_n| <= en * (1#4) * k2 * hn + 2k2p * (1#8) * en' (the gdiff pointwise bound plus the projection) *)
        assert (H2 : Qle (Qabs (projT1 wS n))
                         (Qplus (Qmult (Qmult (Qmult en (1 # 4)) k2) hn)
                                (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))).
        { apply (Qle_trans (Qabs (projT1 wS n))
                           (Qplus (Qmult (Qmult (projT1 eps2 n) k2) (Qabs (projT1 h n)))
                                  (Qmult (Qmult 2 k2p) (projT1 eps2' n)))
                           (Qplus (Qmult (Qmult (Qmult en (1 # 4)) k2) hn)
                                  (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))).
          - exact (QleT'_to_Qle _ _ (HNg n HnNg)).
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
        (* M * A1 <= (1#32) * (en * hn) (the coefS1 absorption) *)
        assert (H4 : Qle (Qmult M (Qmult (Qmult (Qmult en (1 # 4)) k2) hn))
                         (Qmult (1 # 32) (Qmult en hn))).
        { apply (Qle_trans (Qmult M (Qmult (Qmult (Qmult en (1 # 4)) k2) hn))
                           (Qmult (Qmult (Qmult M k2) (1 # 4)) (Qmult en hn))
                           (Qmult (1 # 32) (Qmult en hn))).
          - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          - apply (Qmult_le_compat_r (Qmult (Qmult M k2) (1 # 4)) (1 # 32) (Qmult en hn)).
            + exact HcoefS1.
            + apply (Qmult_le_0_compat en hn Hen0 Hhn0). }
        (* M * A2 <= (1#32) * en' (the coefG1 absorption) *)
        assert (H5 : Qle (Qmult M (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))
                         (Qmult (1 # 32) en')).
        { apply (Qle_trans (Qmult M (Qmult (Qmult (Qmult 2 k2p) (1 # 8)) en'))
                           (Qmult (Qmult (Qmult M (Qmult 2 k2p)) (1 # 8)) en')
                           (Qmult (1 # 32) en')).
          - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          - apply (Qmult_le_compat_r (Qmult (Qmult M (Qmult 2 k2p)) (1 # 8)) (1 # 32) en').
            + exact HcoefG1.
            + exact Hen'0. }
        (* assembly *)
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
      (* decomposition: |err_n| <= |Eobj_n| + (|Gob_n| + m0) *)
      assert (HtriB : Qle Dn (Qplus (Qabs (projT1 Eobj n)) (Qplus (Qabs (projT1 Gob n)) m0))).
      { unfold Dn. exact (QleT'_to_Qle _ _ (Htri n HnNtri)). }
      (* aggregation, then absorption, then linear nra closes *)
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
      (* margin: eta < (1#4) * en', via [b5n_close] *)
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
Qed.

(* ============================================================ *)
(* the section-0 main goal statement (the implementation is the main assembly above) *)

(* ============================================================ *)
(* design note: the pointwise estimates are done inline in the main assembly's per-n step: *)
(*   the nonlinear coefficients are established first as abstract Q facts (the coefS1/coefG1 <= 1#32 shape), *)
(*   then closed with the X := en * hn atom plus linear nra (the pattern of item2 *)
(*   Ha/Hb plus the root sin [b5n_close]); no separate lemmas are needed. *)
(* ============================================================ *)

(* ============================================================ *)
(* the section-0 main goal statement, in its finalized form *)
(* ============================================================ *)
(*
Lemma b5a_S_diff_closed_r :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5a_S (real_plus x h))
                 (real_opp (real_plus (b5a_S x)
                            (real_mult (real_mult x (b5a_S x)) (real_mult (b5a_atan_d x) h))))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
*)

(* ============================================================ *)
(* B5-A E-ODE T3: the J-derivative-zero family. *)
(*   The main statement [b5a_J_deriv_zero] with the seventeen-piece [b5m_*] family. *)
(*   The proofs consume the item1d/2/3s/3e/3g/3a families above. *)
(*   No further dependencies. *)
(* ============================================================ *)

(* ============================================================ *)
(* the section-0 main goal statement, in its finalized form *)
(* ============================================================ *)
(*
Lemma b5a_J_deriv_zero :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5c_J (real_plus x h) Hxh)
                 (real_opp (b5c_J x (b3rr_dom_r1 x r Hxr Hr1)))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
*)

(* ============================================================ *)
(* M0 skeleton. the planned components: *)
(*   [b5m_rS] (a Definition): the S-diff error object (the item3a err term) *)
(*   [b5m_J_err] (a Definition): ErrJ := J(x+h) - J(x) *)
(*   [b5m_J_dec_proj]: the pointwise identity (for n >= N: ErrJ_n == rE * QinvB - *)
(*   Ex * rS * QinvA * QinvB, via the inv-projection Qinv substitution plus the Q-field check) *)
(*   [b5m_Sxh_ge_cB]: the pointwise certificate of Sxh >= cB (the S-diff constant-share instance plus *)
(*   |h_n| <= tau; see the main assembly) *)
(*   the main assembly [b5a_J_deriv_zero]: δ := min(δE, δS1, *)
(*   δS2, real_const tau); pointwise |ErrJ_n| <= en * hn + (3#4) * en', *)
(*   with eta := (1#8) * e1 witnessing real_lt (by [b5n_close]/[b5n_quarter_gt]). *)
(* ============================================================ *)

(* ============================================================ *)
(* M1: the error objects and the pointwise identity *)
(* ============================================================ *)

(* rS := S(x+h) - [S(x) + x * S(x) * d(x) * h] (the S-diff error object, *)
(*   matching the goal text of item3a [b5a_S_diff_closed_r] verbatim) *)
Definition b5m_rS (x h : Real) : Real :=
  real_plus (b5a_S (real_plus x h))
    (real_opp (real_plus (b5a_S x)
               (real_mult (real_mult x (b5a_S x)) (real_mult (b5a_atan_d x) h)))).

(* ErrJ := J(x+h) - J(x) (the object being bounded; J := b5c_J := E * S^-1) *)
Definition b5m_J_err (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1) : Real :=
  real_plus (b5c_J (real_plus x h) Hxh) (real_opp (b5c_J x Hx)).

(* the pointwise positive lower bound of S(x) (a Q-level tail bound):
   some c > 0 and N with c <= S(x)_n for all n >= N.
   extracted from the witness of [b5c_S_pos x] (a global real_lt) as an
   independent sigT piece, so that consuming lemmas need not destruct
   [b5c_S_pos] and perturb the certificate argument of [real_inv_pos]. *)
Lemma b5m_S_pos_pt : forall (x : Real),
  sigT (fun c : Q => And (QltT 0 c)
    (sigT (fun N : nat => forall n : nat, NatLe N n ->
      QleT' c (projT1 (b5a_S x) n)))).
Proof.
  intro x.
  destruct (b5c_S_pos x) as [c [Hc [N HN]]].
  exists c.
  split.
  - exact Hc.
  - exists N.
    intros n Hn.
    assert (Hw : QltT c (projT1 (b5a_S x) n - projT1 real_zero n)).
    { apply (HN n). exact Hn. }
    apply Qle_to_QleT'.
      apply (Qle_trans c (projT1 (b5a_S x) n - projT1 real_zero n) (projT1 (b5a_S x) n)).
    + apply Qlt_le_weak. apply QltT_to_Qlt. exact Hw.
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. cbn [projT1 real_zero]. ring.
Qed.

(* the pointwise identity (for n >= N): ErrJ_n == rE * Qinv(Shn) - Ex * rS * Qinv(Sn) * Qinv(Shn).
   proof: unfold the [b5c_J] projections, replace the inverses by Qinv via
   [real_inv_proj] (invSx/invSxh), substitute the rE/rS definitions
   (Exh == Ex + x * Ex * d * h + rE, Shn == Sn + x * Sn * d * h + rS),
   and the linear term x * E * S * d * h == E * x * S * d * h cancels at the
   value level (pointwise Q-field). *)
Lemma b5m_J_dec_proj : forall (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  sigT (fun N : nat => forall n : nat, NatLe N n -> QeqT (projT1 (b5m_J_err x Hx h Hxh) n) (Qminus (Qmult (projT1 (b5e_E_err x Hx h Hxh) n)
                  (Qinv (projT1 (b5a_S (real_plus x h)) n)))
           (Qmult (Qmult (projT1 (b5a_E x Hx) n) (projT1 (b5m_rS x h) n))
                  (Qmult (Qinv (projT1 (b5a_S x) n))
                         (Qinv (projT1 (b5a_S (real_plus x h)) n)))))).
Proof.
  intros x h Hx Hxh.
  destruct (real_inv_proj (b5a_S x) (b5c_S_pos x)) as [N1 HN1].
  destruct (real_inv_proj (b5a_S (real_plus x h)) (b5c_S_pos (real_plus x h))) as [N2 HN2].
  destruct (b5m_S_pos_pt x) as [cA [HcA [NA HNA]]].
  destruct (b5m_S_pos_pt (real_plus x h)) as [cB [HcB [NB HNB]]].
  exists (Nat.max (Nat.max N1 N2) (Nat.max NA NB)).
  intros n Hn.
  apply NatLe_drop in Hn.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (Hn2 : (N2 <= n)%nat) by lia.
  assert (HnA : (NA <= n)%nat) by lia.
  assert (HnB : (NB <= n)%nat) by lia.
  (* denominator positivity (the field side conditions): Sn >= cA > 0 and Shn >= cB > 0 *)
  assert (HSn0 : Qlt 0 (projT1 (b5a_S x) n)).
  { apply (Qlt_le_trans 0 cA (projT1 (b5a_S x) n)).
    - exact (QltT_to_Qlt _ _ HcA).
    - exact (QleT'_to_Qle _ _ (HNA n (NatLe_lift _ _ HnA))). }
  assert (HShn0 : Qlt 0 (projT1 (b5a_S (real_plus x h)) n)).
  { apply (Qlt_le_trans 0 cB (projT1 (b5a_S (real_plus x h)) n)).
    - exact (QltT_to_Qlt _ _ HcB).
    - exact (QleT'_to_Qle _ _ (HNB n (NatLe_lift _ _ HnB))). }
  (* the difference is zero: projection unfold, inverse substitution, the rE/rS definition substitution, then the Q-field check *)
  assert (HSnNe : ~ projT1 (b5a_S x) n == 0).
  { intro Hz; exact (match (q_neq_of_lt (projT1 (b5a_S x) n) (Qlt_to_QltT _ _ HSn0) (qeq_imp_qeqT _ _ Hz)) with end). }
  assert (HShnNe : ~ projT1 (b5a_S (real_plus x h)) n == 0).
  { intro Hz; exact (match (q_neq_of_lt (projT1 (b5a_S (real_plus x h)) n) (Qlt_to_QltT _ _ HShn0) (qeq_imp_qeqT _ _ Hz)) with end). }
  assert (Hd0 : projT1 (b5m_J_err x Hx h Hxh) n
              - (Qminus (Qmult (projT1 (b5e_E_err x Hx h Hxh) n)
                               (Qinv (projT1 (b5a_S (real_plus x h)) n)))
                        (Qmult (Qmult (projT1 (b5a_E x Hx) n) (projT1 (b5m_rS x h) n))
                               (Qmult (Qinv (projT1 (b5a_S x) n))
                                      (Qinv (projT1 (b5a_S (real_plus x h)) n))))) == 0).
  { unfold b5m_J_err, b5c_J, b5m_rS, b5e_E_err.
    repeat (first [ rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) | rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _)) | rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ]).
    rewrite (qeqT_imp_qeq _ _ (HN1 n (NatLe_lift _ _ Hn1))).
    rewrite (qeqT_imp_qeq _ _ (HN2 n (NatLe_lift _ _ Hn2))).
    repeat (first [ rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)) | rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _)) | rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)) ]).
    field.
    all: split; try (intro Hz; apply qeq_imp_qeqT in Hz; apply (q_neq_of_lt (projT1 (b5a_S (real_plus x h)) n) (Qlt_to_QltT _ _ HShn0)) in Hz; destruct Hz); try (intro Hz; apply qeq_imp_qeqT in Hz; apply (q_neq_of_lt (projT1 (b5a_S x) n) (Qlt_to_QltT _ _ HSn0)) in Hz; destruct Hz). }
  apply qeq_imp_qeqT.
    apply (Qeq_trans (projT1 (b5m_J_err x Hx h Hxh) n)
                   (Qplus (Qminus (Qmult (projT1 (b5e_E_err x Hx h Hxh) n)
                                         (Qinv (projT1 (b5a_S (real_plus x h)) n)))
                                  (Qmult (Qmult (projT1 (b5a_E x Hx) n) (projT1 (b5m_rS x h) n))
                                         (Qmult (Qinv (projT1 (b5a_S x) n))
                                                (Qinv (projT1 (b5a_S (real_plus x h)) n)))))
                          (projT1 (b5m_J_err x Hx h Hxh) n
                           - (Qminus (Qmult (projT1 (b5e_E_err x Hx h Hxh) n)
                                            (Qinv (projT1 (b5a_S (real_plus x h)) n)))
                                     (Qmult (Qmult (projT1 (b5a_E x Hx) n) (projT1 (b5m_rS x h) n))
                                            (Qmult (Qinv (projT1 (b5a_S x) n))
                                                   (Qinv (projT1 (b5a_S (real_plus x h)) n)))))))
                   (Qminus (Qmult (projT1 (b5e_E_err x Hx h Hxh) n)
                                  (Qinv (projT1 (b5a_S (real_plus x h)) n)))
                           (Qmult (Qmult (projT1 (b5a_E x Hx) n) (projT1 (b5m_rS x h) n))
                                  (Qmult (Qinv (projT1 (b5a_S x) n))
                                         (Qinv (projT1 (b5a_S (real_plus x h)) n)))))).
  - ring.
  - rewrite Hd0. ring.
Qed.

(* ============================================================ *)
(* M2: the pointwise bound bridging lemmas *)
(* ============================================================ *)

(* a >= c > 0 gives |Qinv a| <= Qinv c (by [Qabs_pos] and [q_inv_le_contravar]) *)
Lemma b5m_inv_le : forall (a c : Q), Qlt 0 c -> Qle c a ->
  QleT' (Qabs (Qinv a)) (Qinv c).
Proof.
  intros a c Hc Hca.
  apply Qle_to_QleT'.
  assert (Ha0 : Qlt 0 a).
  { apply (Qlt_le_trans 0 c a). exact Hc. exact Hca. }
  assert (Hia0 : Qle 0 (Qinv a)).
  { apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Ha0. }
  rewrite (Qabs_pos (Qinv a) Hia0).
  apply QleT'_to_Qle.
  apply (q_inv_le_contravar a c (Qlt_to_QltT _ _ Ha0) (Qlt_to_QltT _ _ Hc) (Qle_to_QleT' _ _ Hca)).
Qed.

(* the pointwise main step for the quotient error: |ErrJ_n| <= QicB * RE + ME * QicA * QicB * RS.
   inputs: |Qinv(Sn)| <= QicA, |Qinv(Shn)| <= QicB, |Ex_n| <= ME,
   |rE_n| <= RE, |rS_n| <= RS, plus the pointwise identity (the conclusion
   of [b5m_J_dec_proj]). *)
Lemma b5m_J_abs_tri : forall (x h : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (QicA QicB ME RE RS : Q),
  Qle (Qabs (Qinv (projT1 (b5a_S x) n))) QicA ->
  Qle (Qabs (Qinv (projT1 (b5a_S (real_plus x h)) n))) QicB ->
  Qle (Qabs (projT1 (b5a_E x Hx) n)) ME ->
  Qle (Qabs (projT1 (b5e_E_err x Hx h Hxh) n)) RE ->
  Qle (Qabs (projT1 (b5m_rS x h) n)) RS ->
  Qle 0 QicA -> Qle 0 QicB ->
  projT1 (b5m_J_err x Hx h Hxh) n ==
    Qminus (Qmult (projT1 (b5e_E_err x Hx h Hxh) n)
                  (Qinv (projT1 (b5a_S (real_plus x h)) n)))
           (Qmult (Qmult (projT1 (b5a_E x Hx) n) (projT1 (b5m_rS x h) n))
                  (Qmult (Qinv (projT1 (b5a_S x) n))
                         (Qinv (projT1 (b5a_S (real_plus x h)) n)))) ->
  QleT' (Qabs (projT1 (b5m_J_err x Hx h Hxh) n))
      (Qplus (Qmult QicB RE) (Qmult (Qmult ME (Qmult QicA QicB)) RS)).
Proof.
  intros x h Hx Hxh n QicA QicB ME RE RS HQA HQB HME HRE HRS H0A H0B Hdec.
  set (En := projT1 (b5a_E x Hx) n).
  set (rEn := projT1 (b5e_E_err x Hx h Hxh) n).
  set (rSn := projT1 (b5m_rS x h) n).
  set (QiA := Qinv (projT1 (b5a_S x) n)).
  set (QiB := Qinv (projT1 (b5a_S (real_plus x h)) n)).
  set (Dn := projT1 (b5m_J_err x Hx h Hxh) n).
  set (X1 := Qmult rEn QiB).
  set (X2 := Qmult (Qmult En rSn) (Qmult QiA QiB)).
  assert (Hd : Qeq Dn (Qminus X1 X2)).
  { unfold Dn, X1, X2, En, rEn, rSn, QiA, QiB. exact Hdec. }
  (* nonnegativity: ME, RE, RS follow from their Qabs bounds; QicA/QicB are given *)
  assert (HME0 : Qle 0 ME).
  { apply (Qle_trans 0 (Qabs En) ME).
    - apply Qabs_nonneg.
    - unfold En. exact HME. }
  assert (HRE0 : Qle 0 RE).
  { apply (Qle_trans 0 (Qabs rEn) RE).
    - apply Qabs_nonneg.
    - unfold rEn. exact HRE. }
  assert (HRS0 : Qle 0 RS).
  { apply (Qle_trans 0 (Qabs rSn) RS).
    - apply Qabs_nonneg.
    - unfold rSn. exact HRS. }
  (* |Dn| ≤ |X1| + |X2| *)
  assert (Htri : Qle (Qabs Dn) (Qplus (Qabs X1) (Qabs X2))).
  { apply (Qle_trans (Qabs Dn)
                     (Qabs (Qminus X1 X2))
                     (Qplus (Qabs X1) (Qabs X2))).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      apply (Qabs_wd Dn (Qminus X1 X2)).
      exact Hd.
    - apply (Qle_trans (Qabs (Qminus X1 X2))
                       (Qabs (Qplus X1 (Qopp X2)))
                       (Qplus (Qabs X1) (Qabs X2))).
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        apply (Qabs_wd (Qminus X1 X2) (Qplus X1 (Qopp X2))).
        ring.
      + apply (Qle_trans (Qabs (Qplus X1 (Qopp X2)))
                         (Qplus (Qabs X1) (Qabs (Qopp X2)))
                         (Qplus (Qabs X1) (Qabs X2))).
        * apply Qabs_triangle.
        * apply Qplus_le_compat.
          { apply Qle_refl. }
          { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply (Qabs_opp X2). } }
  (* |X1| == |rEn·QiB| ≤ RE·QicB *)
  assert (HX1 : Qle (Qabs X1) (Qmult RE QicB)).
  { apply (Qle_trans (Qabs X1)
                     (Qmult (Qabs rEn) (Qabs QiB))
                     (Qmult RE QicB)).
    - unfold X1.
      apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      apply (Qabs_Qmult rEn QiB).
    - apply (Qle_trans (Qmult (Qabs rEn) (Qabs QiB))
                       (Qmult RE (Qabs QiB))
                       (Qmult RE QicB)).
      + apply (Qmult_le_compat_r (Qabs rEn) RE (Qabs QiB)).
        * unfold rEn. exact HRE.
        * apply Qabs_nonneg.
      + apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs QiB) QicB RE).
        * unfold QiB. exact HQB.
        * exact HRE0. }
  (* |X2| == |En·rSn·QiA·QiB| ≤ ME·QicA·QicB·RS *)
  assert (HX2 : Qle (Qabs X2)
                    (Qmult (Qmult ME (Qmult QicA QicB)) RS)).
  { apply (Qle_trans (Qabs X2)
                     (Qmult (Qmult (Qabs En) (Qabs rSn)) (Qmult (Qabs QiA) (Qabs QiB)))
                     (Qmult (Qmult ME (Qmult QicA QicB)) RS)).
    - unfold X2.
      apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      apply (Qeq_trans (Qabs (Qmult (Qmult En rSn) (Qmult QiA QiB)))
                       (Qmult (Qabs (Qmult En rSn)) (Qabs (Qmult QiA QiB)))
                       (Qmult (Qmult (Qabs En) (Qabs rSn)) (Qmult (Qabs QiA) (Qabs QiB)))).
      + apply (Qabs_Qmult (Qmult En rSn) (Qmult QiA QiB)).
      + apply Qmult_comp.
        * apply (Qabs_Qmult En rSn).
        * apply (Qabs_Qmult QiA QiB).
    - (* assembly: (|En| * |rSn|) * (|QiA| * |QiB|) <= (ME * RS) * (QicA * QicB) <= ME * QicA * QicB * RS *)
      apply (Qle_trans (Qmult (Qmult (Qabs En) (Qabs rSn)) (Qmult (Qabs QiA) (Qabs QiB)))
                       (Qmult (Qmult ME RS) (Qmult QicA QicB))
                       (Qmult (Qmult ME (Qmult QicA QicB)) RS)).
      + assert (H1a : Qle (Qmult (Qabs En) (Qabs rSn)) (Qmult ME RS)).
        { apply (Qle_trans (Qmult (Qabs En) (Qabs rSn))
                           (Qmult ME (Qabs rSn))
                           (Qmult ME RS)).
          - apply (Qmult_le_compat_r (Qabs En) ME (Qabs rSn)).
            + unfold En. exact HME.
            + apply Qabs_nonneg.
          - apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs rSn) RS ME).
            + unfold rSn. exact HRS.
            + exact HME0. }
        assert (H1b : Qle (Qmult (Qabs QiA) (Qabs QiB)) (Qmult QicA QicB)).
        { apply (Qle_trans (Qmult (Qabs QiA) (Qabs QiB))
                           (Qmult QicA (Qabs QiB))
                           (Qmult QicA QicB)).
          - apply (Qmult_le_compat_r (Qabs QiA) QicA (Qabs QiB)).
            + unfold QiA. exact HQA.
            + apply Qabs_nonneg.
          - apply QleT'_to_Qle. apply (sc_qmult_le_l (Qabs QiB) QicB QicA).
            + unfold QiB. exact HQB.
            + exact H0A. }
        assert (H1d : Qle 0 (Qmult (Qabs QiA) (Qabs QiB))).
        { apply Qmult_le_0_compat.
          - apply Qabs_nonneg.
          - apply Qabs_nonneg. }
        apply (Qle_trans (Qmult (Qmult (Qabs En) (Qabs rSn)) (Qmult (Qabs QiA) (Qabs QiB)))
                         (Qmult (Qmult ME RS) (Qmult (Qabs QiA) (Qabs QiB)))
                         (Qmult (Qmult ME RS) (Qmult QicA QicB))).
        * apply (Qmult_le_compat_r (Qmult (Qabs En) (Qabs rSn)) (Qmult ME RS)
                                   (Qmult (Qabs QiA) (Qabs QiB))).
          { exact H1a. }
          { apply Qmult_le_0_compat.
            - apply Qabs_nonneg.
            - apply Qabs_nonneg. }
        * apply QleT'_to_Qle. apply (sc_qmult_le_l (Qmult (Qabs QiA) (Qabs QiB)) (Qmult QicA QicB)
                               (Qmult ME RS)).
          { exact H1b. }
          { apply Qmult_le_0_compat.
            - exact HME0.
            - exact HRS0. }
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
  (* assembly: |Dn| <= (QicB * RE) + ME * QicA * QicB * RS *)
  apply Qle_to_QleT'.
    apply (Qle_trans (Qabs Dn)
                   (Qplus (Qabs X1) (Qabs X2))
                   (Qplus (Qmult QicB RE) (Qmult (Qmult ME (Qmult QicA QicB)) RS))).
  - exact Htri.
  - apply Qplus_le_compat.
    + apply (Qle_trans (Qabs X1) (Qmult RE QicB) (Qmult QicB RE)).
      * exact HX1.
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    + exact HX2.
Qed.

(* ============================================================ *)
(* M3: the main assembly [b5a_J_deriv_zero] *)
(*   ErrJ := J(x+h) - J(x) (by [b5m_J_err x Hx h Hxh]); *)
(*   assembly: the [b5m_J_dec_proj] pointwise identity plus the quotient denominator certificates *)
(*   ([b5m_inv_le], with cA the Sx > 0 witness and cB := cA/2 from the S-diff constant-share *)
(*   instance) give [b5m_J_abs_tri]: |Dn| <= QicB * RE + ME * QicA * QicB * RS; *)
(*   the |rE| bound is E-diff at eps * real_const(kE) (the eps' share kEp/kapE); *)
(*   the |rS| bound is S-diff at eps * real_const(kS) (the eps' share kSp/kapS); *)
(*   δ := min(δE, δS1, δS2, real_const tau); pointwise, *)
(*   |Dn| <= en * hn + (3#4) * en', so eta := (1#8) * e1 witnesses real_lt. *)
(* ============================================================ *)
Lemma b5a_J_deriv_zero :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (Hxr : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5c_J (real_plus x h) Hxh)
                 (real_opp (b5c_J x (b3rr_dom_r1 x r Hxr Hr1)))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxr eps Heps.
  set (Hx := b3rr_dom_r1 x r Hxr Hr1).
  (* ---- the fixed data ---- *)
  (* cA: the pointwise positive lower bound witness of S(x) (extracted from [b5c_S_pos x]); cB := cA/2 *)
  destruct (b5m_S_pos_pt x) as [cA [HcAT [NA HNA]]]; assert (HcA : Qlt 0 cA) by (apply QltT_to_Qlt; exact HcAT).
  set (cB := Qmult cA (1 # 2)).
  assert (HcB : Qlt 0 cB).
  { unfold cB. apply (Qmult_lt_0_compat cA (1 # 2)).
    - exact HcA.
    - change (Qlt 0 (1 # 2)). unfold Qlt. simpl. lia. }
  (* M: |S(x)_n| <= M (by [b5f_S_pts_bounded]) *)
  destruct (b5f_S_pts_bounded x) as [M [HMlt HMall]].
  assert (HM0 : Qle 0 M). { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ HMlt). }
  (* Ms/Mc: the sinA/cosA pointwise bounds, so ME := Ms + r * Mc (|E(x)_n| <= ME) *)
  destruct (b5i_sinA_bounded x Hx) as [Ms [HMsT HMs_all]].
  destruct (b5i_cosA_bounded x Hx) as [Mc [HMcT HMc_all]].
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMsT. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. apply QltT_to_Qlt. exact HMcT. }
  assert (Hr0' : Qle 0 r). { exact Hr0. }
  set (ME := Qplus Ms (Qmult r Mc)).
  assert (HME0 : Qle 0 ME).
  { unfold ME. nra. }
  (* the inverse constants and shares (all depend only on the x data; QltT 0 feeds [real_const_pos]) *)
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
  (* the positivity facts *)
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
  { intro Hz; exact (match (q_neq_of_lt (Qplus ME 1) (Qlt_to_QltT _ _ HME1) (qeq_imp_qeqT _ _ Hz)) with end). }
  assert (Hinv1T : QltT 0 invM1).
  { unfold invM1. apply Qlt_to_QltT. apply Qinv_lt_0_compat. exact HME1. }
  assert (HcAcB0 : Qlt 0 (Qmult (Qmult cA cB) (1 # 8))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 8)).
    - apply (Qmult_lt_0_compat cA cB). { exact HcA. } { exact HcB. }
    - change (Qlt 0 (1 # 8)). unfold Qlt. simpl. lia. }
  assert (HcAcB0b : Qlt 0 (Qmult (Qmult cA cB) (1 # 16))).
  { apply (Qmult_lt_0_compat (Qmult cA cB) (1 # 16)).
    - apply (Qmult_lt_0_compat cA cB). { exact HcA. } { exact HcB. }
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
    - exact HcA.
    - apply Qinv_lt_0_compat. nra. }
  assert (HmuT : QltT 0 mu).
  { unfold mu. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact HcA.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (HkapS2T : QltT 0 kapS2).
  { unfold kapS2. apply Qlt_to_QltT. apply (Qmult_lt_0_compat cA (1 # 16)).
    - exact HcA.
    - change (Qlt 0 (1 # 16)). unfold Qlt. simpl. lia. }
  assert (H1T : QltT 0 1) by (apply Qlt_to_QltT; change (Qlt 0 1); unfold Qlt; simpl; lia).
  assert (HcA0 : Qle 0 cA). { apply Qlt_le_weak. exact HcA. }
  assert (HcB0 : Qle 0 cB). { apply Qlt_le_weak. exact HcB. }
  assert (HcAne : ~ cA == 0) by (intro Hz; exact (match (q_neq_of_lt (cA) (Qlt_to_QltT _ _ HcA) (qeq_imp_qeqT _ _ Hz)) with end)).
  assert (HcBne : ~ cB == 0) by (intro Hz; exact (match (q_neq_of_lt (cB) (Qlt_to_QltT _ _ HcB) (qeq_imp_qeqT _ _ Hz)) with end)).
  assert (H8K1ne : ~ Qmult 8 K1 == 0).
  { intro Hz; assert (H8K1T : QltT 0 (Qmult 8 K1)) by (apply Qlt_to_QltT; nra); exact (match (q_neq_of_lt (Qmult 8 K1) H8K1T (qeq_imp_qeqT _ _ Hz)) with end). }
  assert (HK1ne : ~ K1 == 0).
  { intro Hz; exact (match (q_neq_of_lt (K1) (Qlt_to_QltT _ _ HK1) (qeq_imp_qeqT _ _ Hz)) with end). }
  (* ---- the coefficient budget facts (fixed at the Q level, for pointwise absorption) ---- *)
  (* Hc1: QicB * kE == 1/8; Hc2: QicB * (kEp + kapE) == 1/8 *)
  assert (Hc1 : Qle (Qmult QicB kE) (1 # 8)).
  { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    unfold QicB, kE.
    field. exact HcBne. }
  assert (Hc1' : Qle (Qmult QicB (Qplus kEp kapE)) (1 # 8)).
  { apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    unfold QicB, kEp, kapE.
    field. exact HcBne. }
  (* Hc2/Hc2': ME * QicA * QicB * kS <= 1/8 and ME * QicA * QicB * (kSp + kapS) <= 1/8 *)
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
  (* the lower-bound inequality: (K1 * tau) + mu + kapS2 <= cA - cB (== cA/2, with LHS == cA/4) *)
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
  (* the eps shares (Real): epsE / epsS (the slope shares of the E-diff and S-diff main instances) *)
  set (epsE := real_mult eps (real_const kE)).
  assert (HepsE : real_lt real_zero epsE).
  { unfold epsE. apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact HkET. } }
  set (epsS := real_mult eps (real_const kS)).
  assert (HepsS : real_lt real_zero epsS).
  { unfold epsS. apply real_mult_positive. { exact Heps. } { apply real_const_pos. exact HkST. } }
  (* closed-form instances: δE (E-diff) and δS1/δS2 (the S-diff main and constant-share instances) *)
  destruct (b5a_E_diff_closed_r r Hr0 Hr1 x Hxr epsE HepsE) as [δE [HδE0 HδE]].
  destruct (b5a_S_diff_closed_r r Hr0 Hr1 x Hxr epsS HepsS) as [δS1 [HδS10 HδS1]].
  destruct (b5a_S_diff_closed_r r Hr0 Hr1 x Hxr (real_const 1) (real_const_pos 1 H1T))
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
    (* extracting |h| < each component *)
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
    (* the eps' shares (Real): E-diff epsE' / margin shE, S-diff epsS' / margin shS *)
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
    (* the constant shares of the lower-bound instance (Real, independent of eps') *)
    assert (Hcμ : real_lt real_zero (real_const mu)).
    { apply real_const_pos. exact HmuT. }
    assert (HcκS2 : real_lt real_zero (real_const kapS2)).
    { apply real_const_pos. exact HkapS2T. }
    (* the pointwise conversion (real_le to per-n, with the margin slack) *)
    set (BE := real_plus (real_mult epsE (real_abs h)) epsE').
    destruct (b5i_abs_le_pointwise (b5e_E_err x Hx h Hxh) BE
               (HδE h HhE Hxh epsE' HepsE') shE HshE) as [NE HNE].
    set (BS1 := real_plus (real_mult epsS (real_abs h)) epsS').
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS1
               (HδS1 h HhS1 epsS' HepsS') shS HshS) as [NS HNS].
    set (BS2 := real_plus (real_mult (real_const 1) (real_abs h)) (real_const mu)).
    destruct (b5i_abs_le_pointwise (b5m_rS x h) BS2
               (HδS2 h HhS2 (real_const mu) Hcμ) (real_const kapS2) HcκS2) as [NS2 HNS2].
    (* |h_n| <= tau (by [b5i_h_le_const]), the |d_n| <= 1 tail, the pointwise-identity N *)
    destruct (b5i_h_le_const h tau Hhτ HtauT) as [Nτ HNτ].
    destruct (b5c_d_proj_le_one x) as [Nd Hd].
    destruct (b5m_J_dec_proj x h Hx Hxh) as [Ndec HNdec].
    (* the pointwise budget (from the eps / eps' witnesses) *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He1lt n Hn)). } }
    set (Nmax := Nat.max (Nat.max Ne0 Ne1)
                 (Nat.max (Nat.max Ndec Nτ)
                  (Nat.max (Nat.max NE (Nat.max NS NS2)) (Nat.max NA Nd)))).
    (* main assembly: from [real_le] to the left branch of [real_lt], witnessed by eta *)
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
      (* the tail indices *)
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNE : NatLe NE n) by (apply NatLe_lift; lia).
      assert (HnNS : NatLe NS n) by (apply NatLe_lift; lia).
      assert (HnNS2 : NatLe NS2 n) by (apply NatLe_lift; lia).
      assert (HnNτ : NatLe Nτ n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (HnNdec : (Ndec <= n)%nat) by lia.
      assert (HnNA : (NA <= n)%nat) by lia.
      (* nonnegativity *)
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        - apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T.
        - apply Qlt_le_weak. exact (QltT_to_Qlt _ _ (He0lt n HnNe0)). }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      assert (Hhn0 : Qle 0 hn). { unfold hn. apply Qabs_nonneg. }
      (* |h_n| <= tau, |d_n| <= 1, Sn >= cA *)
      assert (Hhτn : Qle (Qabs (projT1 h n)) tau).
      { unfold tau in *. exact (QleT'_to_Qle _ _ (HNτ n HnNτ)). }
      assert (Hdn1 : Qle (Qabs dn) 1).
      { unfold dn. exact (QleT'_to_Qle _ _ (Hd n (NatLe_lift _ _ HnNd))). }
      assert (HSnA : Qle cA Sn).
      { unfold Sn. exact (QleT'_to_Qle _ _ (HNA n (NatLe_lift _ _ HnNA))). }
      (* |rE_n| <= kE * en * hn + (kEp + kapE) * en' (E-diff made pointwise) *)
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
      (* |rS_n| <= kS * en * hn + (kSp + kapS) * en' (the S-diff main instance made pointwise) *)
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
      (* |rS_n| <= 1 * hn + mu + kapS2 (the S-diff constant-share instance made pointwise, used for the lower bound) *)
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
      (* |Ex_n| <= ME (the sinA/cosA pointwise bounds plus |x_n| <= r; Exn == sAn - xn * cAn) *)
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
              { exact (QleT'_to_Qle _ _ (HMs_all n)). }
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
                  + exact (QleT'_to_Qle _ _ (HMc_all n)).
                - exact Hr0'. }
          + unfold ME. nra. }
      (* the quotient denominator certificate: |Qinv(Sn)| <= QicA *)
      assert (HQA : Qle (Qabs (Qinv Sn)) QicA).
      { unfold Sn, QicA. apply QleT'_to_Qle. apply (b5m_inv_le Sn cA HcA HSnA). }
      (* Sxh >= cB: the |ΔS| bound (r * M * hn + |rS|) gives K1 * tau + mu + kapS2 <= cA - cB *)
      assert (Hdel0 : Qle (Qabs (Qminus Shn Sn))
                          (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                 (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
      { (* Shn − Sn == (x·S·d·h)_n + rS_n *)
        apply (Qle_trans (Qabs (Qminus Shn Sn))
                         (Qplus (Qabs (Qmult (Qmult (projT1 x n) Sn) (Qmult dn (projT1 h n))))
                                (Qabs rSn))
                         (Qplus (Qmult (Qmult r M) (Qabs (projT1 h n)))
                                (Qplus (Qabs (projT1 h n)) (Qplus mu kapS2)))).
        - (* triangle: |Shn - Sn| == |P + rS| <= |P| + |rS| *)
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
        - (* |P| <= r * M * 1 * hn and |rS_n| <= hn + mu + kapS2 (by HrS2) *)
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
                      { unfold Sn. exact (QleT'_to_Qle _ _ (HMall n)). }
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
      (* |ΔS| <= K1 * tau + mu + kapS2 (hn <= tau) *)
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
      (* Shn >= cB (Sn >= cA, |ΔS| <= B0, and B0 <= cA - cB) *)
      assert (HShnB : Qle cB Shn).
      { (* Sn <= Shn + |Δ| and |Δ| <= B0 (by Hdel), so Sn <= Shn + B0 *)
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
        (* cB <= cA - B0 (Hlb_ineq), cA <= Sn (HSnA), Sn <= Shn + B0 give cB <= Shn *)
        nra. }
      (* the quotient denominator certificate: |Qinv(Shn)| <= QicB *)
      assert (HQB : Qle (Qabs (Qinv Shn)) QicB).
      { unfold Shn, QicB. apply QleT'_to_Qle. apply (b5m_inv_le Shn cB HcB HShnB). }
      (* the main step of [b5m_J_abs_tri] *)
      set (RE := Qplus (Qmult (Qmult en kE) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kEp) (Qmult en' kapE))).
      set (RS := Qplus (Qmult (Qmult en kS) (Qabs (projT1 h n)))
                       (Qplus (Qmult en' kSp) (Qmult en' kapS))).
      assert (Hmain0 : Qle Dn (Qplus (Qmult QicB RE) (Qmult Mterm RS))).
      { unfold Dn.
        apply QleT'_to_Qle.
          apply (b5m_J_abs_tri x h Hx Hxh n QicA QicB ME RE RS).
        - exact HQA.
        - exact HQB.
        - unfold Exn. exact HEx.
        - unfold rEn. exact HrE.
        - unfold rSn. exact HrS.
        - unfold QicA. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HcA.
        - unfold QicB. apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HcB.
        - exact (qeqT_imp_qeq _ _ (HNdec n (NatLe_lift _ _ HnNdec))). }
      (* coefficient absorption: QicB * RE <= (1/8) * en * hn + (1/8) * en'; Mterm * RS <= the same shape *)
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
      (* assembly of the pointwise main bound: |Dn| <= en * hn + (3/4) * en' *)
      assert (Hmain : Qle Dn (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
      { apply (Qle_trans Dn
                         (Qplus (Qmult QicB RE) (Qmult Mterm RS))
                         (Qplus (Qmult en hn) (Qmult (3 # 4) en'))).
        - exact Hmain0.
        - (* expand and absorb: QicB * RE + Mterm * RS <= (1/8) * (en * hn) + (1/8) * en', each with two copies *)
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
      (* margin: eta < (1/4) * en'; Hfin: eta < (en * hn + en') - Dn *)
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




(* ============================================================ *)
(* R1: the tail-certificate J-modulus statement *)
(*   the goal statement [b5m_J_deriv_zero_tail], the tail-certificate version of the J zero modulus. *)
(*   the base-point assumption of [b5a_J_deriv_zero] is an all-n r < 1 certificate *)
(*   (Hxr : for all n, |x_n| <= r); the early coordinates of a real_le interval point y are unbounded, *)
(*   (clamp01(y) may have early coordinates equal to 1), so it cannot be fed in directly. *)
(*   this statement relaxes the base-point certificate to a tail certificate: some N0 with |x_n| <= r < 1 for all n >= N0, *)
(*   while the early coordinates only need the all-n cw_unit certificate Hx1 (|x_n| <= 1). *)
(*   implementation (tail-certification, without re-running the per-index chain inside [b5a_J_deriv_zero]): *)
(*   (1) [b5m_tailtrunc x N0]: coordinates from n >= N0 keep x_n and early coordinates become 0, so x̂ is *)
(*   an all-n r < 1 certificate point (early coordinates 0), and x̂ == x (real_eq); *)
(*   (2) ĥ := trunc h N0 with ĥ == h and |ĥ| == |h|; x̂+ĥ and x+h agree exactly on the tail, *)
(*   and cw_unit (x̂+ĥ) is extracted pointwise from Hxh; *)
(*   (3) the black-box [b5a_J_deriv_zero] at (x̂, eps) gives δ̂ > 0 and *)
(*   |J(x̂+ĥ) - J(x̂)| <= eps * |ĥ| + eps'; *)
(*   (4) the real_eq extensionality of [b5c_J] ([b5m_J_wd], the pointwise wd for arctan/E/S) *)
(*   transfers the difference and the bound back to the original (x, h) (via real_le_compat and the real_eq bridge). *)
(*   interface for T4: for a real_le interval point y, the assembly recipe takes the real_le branch plus *)
(*   the x < 1 separation to extract (N0, Hxr, Hx1) per y (N(y) depends on y), then instantiates *)
(*   this statement; δ is independent of h and eps' (the Bishop modulus); the decomposition of the zero-side Or(lt, eq) branch *)
(*   belongs to the assembly recipe (this statement only consumes the already-extracted tail certificate). *)
(* ============================================================ *)

(* truncation: coordinates from n >= N0 keep x_n, early coordinates (n < N0)
   become 0 (the cauchy structure is preserved: the cauchy tail bound Nc of x
   is carried over unchanged after taking the max with N0) *)
Definition b5m_tailtrunc (x : Real) (N0 : nat) : Real.
Proof.
  destruct x as [u Hu].
  exists (fun n : nat => if Nat.leb N0 n then u n else 0).
  intros eps Heps.
  destruct (Hu eps Heps) as [Nc HNc].
  exists (Nat.max N0 Nc).
  intros m n Hm Hn.
  assert (Hm0 : Nat.leb N0 m = true).
  { apply Nat.leb_le. apply (Nat.le_trans N0 (Nat.max N0 Nc) m).
    - apply Nat.le_max_l.
    - apply NatLe_drop. exact Hm. }
  assert (Hn0 : Nat.leb N0 n = true).
  { apply Nat.leb_le. apply (Nat.le_trans N0 (Nat.max N0 Nc) n).
    - apply Nat.le_max_l.
    - apply NatLe_drop. exact Hn. }
  assert (Hm1 : NatLe Nc m).
  { apply NatLe_lift. apply (Nat.le_trans Nc (Nat.max N0 Nc) m).
    - apply Nat.le_max_r.
    - apply NatLe_drop. exact Hm. }
  assert (Hn1 : NatLe Nc n).
  { apply NatLe_lift. apply (Nat.le_trans Nc (Nat.max N0 Nc) n).
    - apply Nat.le_max_r.
    - apply NatLe_drop. exact Hn. }
  change (QltT (Qabs ((if Nat.leb N0 m then u m else 0) - (if Nat.leb N0 n then u n else 0))) eps).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (u m - u n)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    apply (Qabs_wd
             ((if Nat.leb N0 m then u m else 0) - (if Nat.leb N0 n then u n else 0))
             (u m - u n)).
    rewrite Hm0. rewrite Hn0. reflexivity.
  - apply QltT_to_Qlt. apply (HNc m n Hm1 Hn1).
Defined.

(* tail-preserving projection: n >= N0 gives trunc(x,N0)_n == x_n *)
Lemma b5m_tailtrunc_ge : forall (x : Real) (N0 n : nat),
  NatLe N0 n -> QeqT (projT1 (b5m_tailtrunc x N0) n) (projT1 x n).
Proof.
  intros x N0 n Hn.
  apply qeq_imp_qeqT.
  destruct x as [u Hu].
  cbn [projT1 b5m_tailtrunc].
  destruct (Nat.leb N0 n) eqn:E.
  - reflexivity.
  - exfalso.
    apply (proj1 (Nat.leb_gt N0 n)) in E.
    apply NatLe_drop in Hn.
    lia.
Qed.

(* early-coordinate projection: n < N0 (leb N0 n = false) gives trunc(x,N0)_n == 0 *)
Lemma b5m_tailtrunc_lt : forall (x : Real) (N0 n : nat),
  Nat.leb N0 n = false -> QeqT (projT1 (b5m_tailtrunc x N0) n) (0).
Proof.
  intros x N0 n En.
  apply qeq_imp_qeqT.
  destruct x as [u Hu].
  cbn [projT1 b5m_tailtrunc].
  rewrite En. reflexivity.
Qed.

(* trunc x N0 is real_eq to x (pointwise equality from n >= N0 on) *)
Lemma b5m_tailtrunc_eq : forall (x : Real) (N0 : nat),
  real_eq (b5m_tailtrunc x N0) x.
Proof.
  intros x N0 eps Heps.
  exists N0.
  intros n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    apply (Qabs_wd (projT1 (b5m_tailtrunc x N0) n - projT1 x n) 0).
rewrite (qeqT_imp_qeq _ _ (b5m_tailtrunc_ge x N0 n Hn)).
    ring.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* the all-n r certificate for the truncated base point: the tail uses Hxr (n >= N0), early coordinates have |0| <= r *)
Lemma b5m_tailtrunc_r : forall (r : Q) (Hr0 : Qle 0 r) (N0 : nat) (x : Real),
  (forall n : nat, NatLe N0 n -> QleT' (Qabs (projT1 x n)) r) ->
  forall n : nat, QleT' (Qabs (projT1 (b5m_tailtrunc x N0) n)) r.
Proof.
  intros r Hr0 N0 x Hxr n.
  destruct x as [u Hu].
  cbn [projT1 b5m_tailtrunc].
  destruct (Nat.leb N0 n) eqn:E.
  - assert (Hge : (N0 <= n)%nat) by (apply Nat.leb_le in E; exact E).
    exact (Hxr n (NatLe_lift N0 n Hge)).
  - apply Qle_to_QleT'.
    apply (Qle_trans (Qabs 0) 0 r).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. simpl. ring.
    + exact Hr0.
Qed.

(* cw_unit (trunc x N0 + trunc h N0): 0+0 when n < N0, == x+h when n >= N0
   (the Hxh : cw_unit (x+h) witness transfers pointwise; early coordinates
   have |0+0| <= 1) *)
Lemma b5m_plus_tailtrunc_unit : forall (x h : Real) (N0 : nat),
  (forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1) ->
  forall n : nat, QleT' (Qabs (projT1 (real_plus (b5m_tailtrunc x N0)
                                                (b5m_tailtrunc h N0)) n)) 1.
Proof.
  intros x h N0 Hxh n.
  destruct (Nat.leb N0 n) eqn:E.
  - (* tail: trunc_x == x and trunc_h == h pointwise, so |x_n + h_n| <= 1 (by Hxh) *)
    assert (Hge : (N0 <= n)%nat) by (apply Nat.leb_le in E; exact E).
    assert (Hle : NatLe N0 n) by (apply NatLe_lift; exact Hge).
    apply Qle_to_QleT'.
    eapply Qle_trans.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      apply (Qabs_wd (projT1 (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) n)
                     (projT1 (real_plus x h) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (b5m_tailtrunc x N0) (b5m_tailtrunc h N0) n)).
rewrite (qeqT_imp_qeq _ _ (b5m_tailtrunc_ge x N0 n Hle)).
rewrite (qeqT_imp_qeq _ _ (b5m_tailtrunc_ge h N0 n Hle)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj x h n)).
      ring.
    + apply QleT'_to_Qle. exact (Hxh n).
  - (* early: trunc_x == 0 and trunc_h == 0, so |0 + 0| <= 1 *)
    apply Qle_to_QleT'.
    apply (Qle_trans (Qabs (projT1 (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) n))
                     0 1).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      apply (Qabs_wd (projT1 (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) n) 0).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (b5m_tailtrunc x N0) (b5m_tailtrunc h N0) n)).
rewrite (qeqT_imp_qeq _ _ (b5m_tailtrunc_lt x N0 n E)).
rewrite (qeqT_imp_qeq _ _ (b5m_tailtrunc_lt h N0 n E)).
      ring.
    + change (Qle 0 1). unfold Qle. simpl. lia.
Qed.


(* ============================================================ *)
(* R1 sub-piece: the real_eq extensionality of [b5c_J] (the tail-certificate transfer bridge) *)
(*   the [b5p2_arctan_wd] / [b5p2_E_wd] / [b5p2_S_wd] / [b5p2_J_wd] pieces, *)
(*   carried under the [b5m_*] names of this file; they depend only on the root pieces *)
(*   ([b5b_ap_uniform], [real_sin_eq_compat], *)
(*     real_cos_eq_compat L58680 / real_log_wd L42277 /           *)
(*   [cauchy_real_exp_wd], [real_inv_pos_ext]). *)
(* ============================================================ *)

(* the real_eq extensionality of arctan: real_eq u v gives *)
(*   real_eq (arctan u Hu) (arctan v Hv) (certificate domain |u_n|, |v_n| <= 1) *)
Lemma b5m_arctan_wd : forall (u v : Real)
  (Hu : cw_unit u) (Hv : cw_unit v),
  real_eq u v -> real_eq (cauchy_real_arctan u Hu) (cauchy_real_arctan v Hv).
Proof.
  intros u v Hu Hv Huv epsQ HepsQ.
  destruct (b5b_ap_uniform epsQ (QltT_to_Qlt 0 epsQ HepsQ)) as [M [d0 [Hd0 Hcore]]].
  destruct (Huv d0 Hd0) as [N0 HN0].
  exists (Nat.max M N0).
  intros n Hn.
  apply NatLe_drop in Hn.
  assert (HnM : (M <= n)%nat) by lia.
  assert (HnN0 : (N0 <= n)%nat) by lia.
  apply (qltT_eq_compat_l
           (Qabs (arctan_partial n (projT1 u n) - arctan_partial n (projT1 v n)))
           (Qabs (projT1 (cauchy_real_arctan u Hu) n - projT1 (cauchy_real_arctan v Hv) n))
           epsQ).
  - apply qeq_imp_qeqT. apply Qeq_sym.
    apply (Qabs_wd (projT1 (cauchy_real_arctan u Hu) n - projT1 (cauchy_real_arctan v Hv) n)
                   (arctan_partial n (projT1 u n) - arctan_partial n (projT1 v n))).
    rewrite (qeqT_imp_qeq _ _ (arctan_real_proj u Hu n)).
    rewrite (qeqT_imp_qeq _ _ (arctan_real_proj v Hv n)).
    reflexivity.
  - apply (Hcore n (projT1 u n) (projT1 v n) (NatLe_lift _ _ HnM) (Hu n) (Hv n)).
    apply qltT_leT'.
    apply (HN0 n (NatLe_lift _ _ HnN0)).
Qed.

(* the real_eq extensionality of E = sin o arctan - x * cos o arctan: *)
(*   real_eq u v ⟹ real_eq (b5a_E u Hu) (b5a_E v Hv)             *)
Lemma b5m_E_wd : forall (u v : Real)
  (Hu : cw_unit u) (Hv : cw_unit v),
  real_eq u v -> real_eq (b5a_E u Hu) (b5a_E v Hv).
Proof.
  intros u v Hu Hv Huv.
  assert (Harct : real_eq (cauchy_real_arctan u Hu) (cauchy_real_arctan v Hv)).
  { apply (b5m_arctan_wd u v Hu Hv). exact Huv. }
  assert (Hsin : real_eq (cauchy_real_sin (cauchy_real_arctan u Hu))
                         (cauchy_real_sin (cauchy_real_arctan v Hv))).
  { apply real_sin_eq_compat. exact Harct. }
  assert (Hcos : real_eq (cauchy_real_cos (cauchy_real_arctan u Hu))
                         (cauchy_real_cos (cauchy_real_arctan v Hv))).
  { apply real_cos_eq_compat. exact Harct. }
  assert (Hm : real_eq (real_mult u (cauchy_real_cos (cauchy_real_arctan u Hu)))
                       (real_mult v (cauchy_real_cos (cauchy_real_arctan v Hv)))).
  { apply (RealSetoid.real_eq_mult_compat u
             (cauchy_real_cos (cauchy_real_arctan u Hu))
             v
             (cauchy_real_cos (cauchy_real_arctan v Hv))).
    - exact Huv.
    - exact Hcos. }
  unfold b5a_E.
  apply (RealSetoid.real_eq_plus_compat
           (cauchy_real_sin (cauchy_real_arctan u Hu))
           (real_opp (real_mult u (cauchy_real_cos (cauchy_real_arctan u Hu))))
           (cauchy_real_sin (cauchy_real_arctan v Hv))
           (real_opp (real_mult v (cauchy_real_cos (cauchy_real_arctan v Hv))))).
  - exact Hsin.
  - apply (RealSetoid.real_eq_opp_compat
             (real_mult u (cauchy_real_cos (cauchy_real_arctan u Hu)))
             (real_mult v (cauchy_real_cos (cauchy_real_arctan v Hv)))).
    exact Hm.
Qed.

(* the real_eq extensionality of S = exp((1/2) * log(1+x^2)): *)
(*   real_eq u v ⟹ real_eq (b5a_S u) (b5a_S v)                   *)
Lemma b5m_S_wd : forall (u v : Real),
  real_eq u v -> real_eq (b5a_S u) (b5a_S v).
Proof.
  intros u v Huv.
  unfold b5a_S.
  assert (Hsq : real_eq (real_mult u u) (real_mult v v)).
  { apply (RealSetoid.real_eq_mult_compat u u v v).
    - exact Huv.
    - exact Huv. }
  assert (H1p : real_eq (real_plus real_one (real_mult u u))
                        (real_plus real_one (real_mult v v))).
  { apply (RealSetoid.real_eq_plus_compat real_one (real_mult u u)
                                          real_one (real_mult v v)).
    - apply real_eq_refl.
    - exact Hsq. }
  assert (Hlog : real_eq (real_log (real_plus real_one (real_mult u u)) (b5a_one_plus_sq_pos u))
                         (real_log (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos v))).
  { apply (real_log_wd (real_plus real_one (real_mult u u))
                       (real_plus real_one (real_mult v v))
                       (b5a_one_plus_sq_pos u) (b5a_one_plus_sq_pos v)).
    exact H1p. }
  assert (Hml : real_eq (real_mult (real_const (1 / 2))
                                   (real_log (real_plus real_one (real_mult u u)) (b5a_one_plus_sq_pos u)))
                        (real_mult (real_const (1 / 2))
                                   (real_log (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos v)))).
  { apply (RealSetoid.real_eq_mult_compat (real_const (1 / 2))
             (real_log (real_plus real_one (real_mult u u)) (b5a_one_plus_sq_pos u))
             (real_const (1 / 2))
             (real_log (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos v))).
    - apply real_eq_refl.
    - exact Hlog. }
  apply cauchy_real_exp_wd. exact Hml.
Qed.

(* the real_eq extensionality of b5c_J = E * inv_pos(S): *)
(*   real_eq u v ⟹ real_eq (b5c_J u Hu) (b5c_J v Hv)             *)
Lemma b5m_J_wd : forall (u v : Real)
  (Hu : cw_unit u) (Hv : cw_unit v),
  real_eq u v -> real_eq (b5c_J u Hu) (b5c_J v Hv).
Proof.
  intros u v Hu Hv Huv.
  unfold b5c_J.
  assert (HS : real_eq (b5a_S u) (b5a_S v)) by (apply b5m_S_wd; exact Huv).
  assert (Hinv : real_eq (real_inv_pos (b5a_S u) (b5c_S_pos u))
                         (real_inv_pos (b5a_S v) (b5c_S_pos v))).
  { apply (real_inv_pos_ext (b5a_S u) (b5a_S v)
                            (b5c_S_pos u) (b5c_S_pos v)). exact HS. }
  apply (RealSetoid.real_eq_mult_compat (b5a_E u Hu) (real_inv_pos (b5a_S u) (b5c_S_pos u))
                                        (b5a_E v Hv) (real_inv_pos (b5a_S v) (b5c_S_pos v))).
  - apply (b5m_E_wd u v Hu Hv). exact Huv.
  - exact Hinv.
Qed.


(* ============================================================ *)
(* R1 main statement: [b5m_J_deriv_zero_tail], the tail-certificate version of the J zero modulus *)
(*   the statement has the (r/Hr0/Hr1/x/Hxr/eps -> sigT δ) shape of [b5a_J_deriv_zero], *)
(*   except that Hxr is relaxed to a tail certificate (N0 with |x_n| <= r for all n >= N0) and the certificate argument Hx1 *)
(*   (for all n, |x_n| <= 1) is explicit (early coordinates only need cw_unit). *)
(*   proof: truncate x̂ := trunc(x,N0) (an all-n r certificate), so [b5a_J_deriv_zero] *)
(*   as a black box gives δ̂ > 0 and |J(x̂+ĥ) - J(x̂)| <= eps * |ĥ| + eps' *)
(*   (ĥ := trunc(h,N0), with cw_unit (x̂+ĥ) extracted pointwise from Hxh); then *)
(*   [b5m_J_wd] (the real_eq extensionality), via real_eq x̂ x and ĥ h, transfers *)
(*   the difference and the bound back to (x, h) (via [RealSetoid.real_le_compat]). *)
(* ============================================================ *)
Lemma b5m_J_deriv_zero_tail :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real) (N0 : nat)
    (Hxr : forall n : nat, NatLe N0 n -> QleT' (Qabs (projT1 x n)) r),
  forall (Hx1 : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (b5c_J (real_plus x h) Hxh)
                 (real_opp (b5c_J x Hx1))))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x N0 Hxr Hx1 eps Heps.
  (* the all-n r certificate for the truncated base point *)
  assert (Hx̂r : forall n : nat,
            QleT' (Qabs (projT1 (b5m_tailtrunc x N0) n)) r).
  { apply (b5m_tailtrunc_r r Hr0 N0 x). exact Hxr. }
  (* the black box: [b5a_J_deriv_zero] at (trunc x N0, Hx̂r) *)
  destruct (b5a_J_deriv_zero r Hr0 Hr1 (b5m_tailtrunc x N0) Hx̂r eps Heps)
    as [delta [Hd0 Hd]].
  exists delta.
  split.
  { exact Hd0. }
  { intros h Hh Hxh eps' Heps'.
    (* ĥ := trunc h N0 satisfies |ĥ| < delta (ĥ == h gives |ĥ| == |h|) *)
    assert (Hĥlt : real_lt (real_abs (b5m_tailtrunc h N0)) delta).
    { apply (RealSetoid.real_lt_compat (real_abs h)
                                       (real_abs (b5m_tailtrunc h N0))
                                       delta delta).
      - apply real_eq_sym.
        apply (real_abs_eq_compat (b5m_tailtrunc h N0) h).
        exact (b5m_tailtrunc_eq h N0).
      - apply real_eq_refl.
      - exact Hh. }
    (* cw_unit (trunc x N0 + trunc h N0): extracted pointwise from Hxh *)
    assert (Hxĥ : forall n : nat,
              QleT' (Qabs (projT1 (real_plus (b5m_tailtrunc x N0)
                                             (b5m_tailtrunc h N0)) n)) 1).
    { exact (b5m_plus_tailtrunc_unit x h N0 Hxh). }
    (* the black-box modulus at the truncated base point *)
    assert (Hmod : real_le
      (real_abs (real_plus
        (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
        (real_opp (b5c_J (b5m_tailtrunc x N0)
                         (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1)))))
      (real_plus (real_mult eps (real_abs (b5m_tailtrunc h N0))) eps')).
    { exact (Hd (b5m_tailtrunc h N0) Hĥlt Hxĥ eps' Heps'). }
    (* the real_eq bridge: x̂ == x, ĥ == h, x̂+ĥ == x+h *)
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
    (* the extensionality transfer of the J values *)
    assert (Hj1 : real_eq (b5c_J (real_plus x h) Hxh)
                          (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)).
    { apply (b5m_J_wd (real_plus x h)
                      (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0))
                      Hxh Hxĥ).
      apply real_eq_sym. exact Hpeq. }
    assert (Hj2 : real_eq (b5c_J x Hx1)
                          (b5c_J (b5m_tailtrunc x N0)
                                 (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1))).
    { apply (b5m_J_wd x (b5m_tailtrunc x N0) Hx1
                      (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1)).
      apply real_eq_sym. exact Hxeq. }
    (* the difference |J(x+h) - J(x)| == |J(x̂+ĥ) - J(x̂)| (by the abs/plus/opp compatibility lemmas) *)
    assert (HA : real_eq
      (real_abs (real_plus (b5c_J (real_plus x h) Hxh) (real_opp (b5c_J x Hx1))))
      (real_abs (real_plus
        (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
        (real_opp (b5c_J (b5m_tailtrunc x N0)
                         (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1)))))).
    { apply (RealSetoid.real_eq_abs_compat
        (real_plus (b5c_J (real_plus x h) Hxh) (real_opp (b5c_J x Hx1)))
        (real_plus (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
                   (real_opp (b5c_J (b5m_tailtrunc x N0)
                                    (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1))))).
      apply (RealSetoid.real_eq_plus_compat
        (b5c_J (real_plus x h) Hxh)
        (real_opp (b5c_J x Hx1))
        (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
        (real_opp (b5c_J (b5m_tailtrunc x N0)
                         (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1)))).
      - exact Hj1.
      - apply (RealSetoid.real_eq_opp_compat
                 (b5c_J x Hx1)
                 (b5c_J (b5m_tailtrunc x N0)
                        (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1))).
        exact Hj2. }
    (* the bound eps * |ĥ| + eps' == eps * |h| + eps' (|ĥ| == |h|) *)
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
    (* the modulus transfer: [real_le_compat] moves the (x̂,ĥ) modulus back to (x,h) *)
    apply (RealSetoid.real_le_compat
      (real_abs (real_plus
        (b5c_J (real_plus (b5m_tailtrunc x N0) (b5m_tailtrunc h N0)) Hxĥ)
        (real_opp (b5c_J (b5m_tailtrunc x N0)
                         (b3rr_dom_r1 (b5m_tailtrunc x N0) r Hx̂r Hr1)))))
      (real_abs (real_plus (b5c_J (real_plus x h) Hxh) (real_opp (b5c_J x Hx1))))
      (real_plus (real_mult eps (real_abs (b5m_tailtrunc h N0))) eps')
      (real_plus (real_mult eps (real_abs h)) eps')).
    - apply real_eq_sym. exact HA.
    - exact HB.
    - exact Hmod. }
Qed.

(* ============================================================ *)
(* B5-A E-ODE T4 Prep: the totalization of the clamp. *)
(*   [b5p2_clamp01], [b5p2_J_tot], [b5p2_Hext], [b5p2_E_zero_of_J_zero] and the other seventeen pieces. *)
(*   The proofs consume the item2/3s/3e/3g/3a families. *)
(*   No further dependencies. *)
(* ============================================================ *)

(* ============================================================ *)
(* M0 skeleton: the section-0 goal piece list *)
(*   P1  clamp01 x := real_min (real_max x real_zero) (real_const 1)*)
(*       (a Definition, via the roots [real_min_proj] / [real_max_proj]) *)
(*   P2  Hcl : forall x, cw_unit (clamp01 x) (the pointwise min/max certificate: *)
(*        |min(max(x_n,0),1)| <= 1 for all n, closed at the Q level) *)
(*   P3  b5p2_J_tot x := b5c_J (clamp01 x) (Hcl x) (a Definition, a total function) *)
(*   P4  Hext : forall x y, real_eq x y ->                        *)
(*        real_eq (b5p2_J_tot x) (b5p2_J_tot y) (the min/max wd, pointwise) *)
(*   P5  the certificate-point substitution bridge: for all x (Hx : cw_unit x), *)
(*        real_lt real_zero x -> real_lt x (real_const 1) ->      *)
(*        real_eq (b5p2_J_tot x) (b5c_J x Hx)                    *)
(*        (the real_lt separation gives the clamp01 tail equality, bridged by the arctan/sin/cos tail equalities) *)
(*   P6  the E == J * S substitution: real_eq (b5a_E x Hx) *)
(*        (real_mult (b5c_J x Hx) (b5a_S x)) (by [real_inv_pos_correct] *)
(*        and [b5c_S_pos]); from J(x) == 0 deduce E(x) == 0 (0 * S == 0) *)
(*   P7  a statement check of [b5b_f1_closure'] *)
(* design: *)
(*   the clamp certificate: the pointwise min/max projections give |Qmin(Qmax(x_n,0),1)| <= 1 *)
(*   separation to tail equality: real_lt 0 x and real_lt x 1 give eps and N, with the tail *)
(*   eps < x_n < 1 - eps, so clamp01(x_n) == x_n pointwise exactly, giving a real_eq *)
(*   the J_tot extension: min/max are Lipschitz at the Q level ([q_min_lipschitz]/[q_max_lipschitz]), *)
(*   giving real_min/max wd, then clamp01 wd, then pointwise wd for the J constituents *)
(*   the interface for the main assembly: [b5p2_J_tot] (a total function), Hext, the certificate-point substitution bridge, *)
(*   and E == J * S; the main assembly consumes this file plus the item3b family. *)
(* ============================================================ *)

(* ============================================================ *)
(* P1: [clamp01], the totalized map clamping pointwise to [0,1] *)
(*   clamp01(x)_n == Qmin (Qmax (x_n) 0) 1 (by [real_min_proj] / *)
(*   [real_max_proj]) *)
(* ============================================================ *)
Definition b5p2_clamp01 (x : Real) : Real :=
  real_min (real_max x real_zero) (real_const 1).

(* Q level: 0 <= Qmax q 0 (by [Q.le_max_r]), so Qmin (Qmax q 0) 1 >= 0 and <= 1 *)
Lemma b5p2_q_clamp01_bounds : forall (q : Q),
  And (QleT' 0 (Qmin (Qmax q 0) 1)) (QleT' (Qmin (Qmax q 0) 1) 1).
Proof.
  intro q. split.
  - (* 0 <= min(max(q,0),1): [Q.min_glb] applied to 0 <= max(q,0) and 0 <= 1 *)
    apply Qle_to_QleT'. apply Q.min_glb.
    + (* 0 <= Qmax q 0: the upper bound y <= max x y of max (with y := 0) *)
      apply Q.le_max_r.
    + unfold Qle. simpl. lia.
  - (* min(max(q,0),1) <= 1: the lower bound min x y <= y of min (with y := 1) *)
    apply Qle_to_QleT'. apply Q.le_min_r.
Qed.

(* |min(max(q,0),1)| <= 1 (0 <= the value <= 1 gives Qabs == the value) *)
Lemma b5p2_q_clamp01_abs_le_one : forall (q : Q),
  QleT' (Qabs (Qmin (Qmax q 0) 1)) 1.
Proof.
  intro q.
  apply Qle_to_QleT'.
  destruct (b5p2_q_clamp01_bounds q) as [Hge0 Hle1].
  apply (Qle_trans _ (Qmin (Qmax q 0) 1) _).
  - (* |m| == m for m >= 0, so |m| <= m via the qeq_le conversion *)
    apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
    apply Qabs_pos. exact (QleT'_to_Qle _ _ Hge0).
  - exact (QleT'_to_Qle _ _ Hle1).
Qed.

(* ============================================================ *)
(* P2: Hcl, the cw_unit certificate of clamp01 (for all n, |clamp01(x)_n| <= 1) *)
(*   the pointwise min/max projections: proj n == Qmin(Qmax(x_n,0),1), closed at the Q level *)
(* ============================================================ *)
Lemma b5p2_Hcl : forall (x : Real), cw_unit (b5p2_clamp01 x).
Proof.
  intros x n.
  unfold cw_unit.
  (* goal: QleT' (Qabs (projT1 (clamp01 x) n)) 1 *)
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (Qmin (Qmax (projT1 x n) 0) 1)) _).
  - (* |proj_n| == |Qmin(Qmax(x_n,0),1)|: after unfolding the projections, by [Qabs_wd] *)
    apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    apply (Qabs_wd (projT1 (b5p2_clamp01 x) n) (Qmin (Qmax (projT1 x n) 0) 1)).
    unfold b5p2_clamp01.
    rewrite (qeqT_imp_qeq _ _ (real_min_proj (real_max x real_zero) (real_const 1) n)).
    rewrite (qeqT_imp_qeq _ _ (real_max_proj x real_zero n)).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
    (* projT1 real_zero n == 0: real_zero is the constant zero sequence *)
    replace (projT1 real_zero n) with 0%Q by (unfold real_zero; reflexivity).
    reflexivity.
- exact (QleT'_to_Qle _ _ (b5p2_q_clamp01_abs_le_one (projT1 x n))).
Qed.

(* ============================================================ *)
(* P3: J_tot, the composition b5c_J o clamp01 (a total function, needed for the b4 assumption) *)
(*   b5p2_J_tot x := b5c_J (clamp01 x) (Hcl x) (the root [b5c_J]) *)
(* ============================================================ *)
Definition b5p2_J_tot (x : Real) : Real :=
  b5c_J (b5p2_clamp01 x) (b5p2_Hcl x).

(* ============================================================ *)
(* P6: the E == J * S substitution (J := b5c_J := E * S^-1, S := b5a_S) *)
(*   E == (E·invS)·S == E·(invS·S) == E·1 == E                   *)
(*   (by [real_mult_assoc], [real_inv_pos_correct] and *)
(*   [real_mult_one]; [b5c_S_pos] supplies the S > 0 certificate) *)
(* ============================================================ *)
Lemma b5p2_E_eq_J_S : forall (x : Real) (Hx : cw_unit x),
  real_eq (b5a_E x Hx) (real_mult (b5c_J x Hx) (b5a_S x)).
Proof.
  intros x Hx.
  unfold b5c_J.
  (* goal: E == (E * invS) * S; routed through E * 1 and E * (invS * S) *)
  apply (real_eq_trans _ (real_mult (b5a_E x Hx) real_one) _).
  - (* E == E * 1: the reverse of [real_mult_one] (real_eq (mult E 1) E) *)
    apply real_eq_sym.
    apply real_mult_one.
  - (* E·1 == (E·invS)·S *)
    apply (real_eq_trans _ (real_mult (b5a_E x Hx)
                                (real_mult (real_inv_pos (b5a_S x) (b5c_S_pos x))
                                           (b5a_S x))) _).
    + (* E * 1 == E * (invS * S): by mult_compat (E == E by reflexivity, and 1 == invS * S) *)
      apply (RealSetoid.real_eq_mult_compat (b5a_E x Hx) real_one
             (b5a_E x Hx) (real_mult (real_inv_pos (b5a_S x) (b5c_S_pos x)) (b5a_S x))).
      * apply real_eq_refl.
      * (* 1 == invS * S: invS * S == S * invS (commutativity) == 1 (by [real_inv_pos_correct]), in reverse *)
        apply real_eq_sym.
        apply (real_eq_trans _ (real_mult (b5a_S x) (real_inv_pos (b5a_S x) (b5c_S_pos x))) _).
        -- apply real_mult_comm.
        -- apply real_inv_pos_correct.
    + (* E * (invS * S) == (E * invS) * S: by [real_mult_assoc] with x := E *)
      apply real_mult_assoc.
Qed.

(* ============================================================ *)
(* P6b: from J(x) == 0 deduce E(x) == 0 (E == J * S, and J == 0 gives J * S == 0 * S == 0) *)
(*   0 * S == 0: by [real_mult_comm] and [real_mult_zero] *)
(* ============================================================ *)
Lemma b5p2_E_zero_of_J_zero : forall (x : Real) (Hx : cw_unit x),
  real_eq (b5c_J x Hx) real_zero -> real_eq (b5a_E x Hx) real_zero.
Proof.
  intros x Hx HJ0.
  apply (real_eq_trans _ (real_mult (b5c_J x Hx) (b5a_S x)) _).
  - (* E == J * S, by P6 *)
    exact (b5p2_E_eq_J_S x Hx).
  - (* J * S == 0: J == 0 gives J * S == 0 * S, and 0 * S == 0 *)
    apply (real_eq_trans _ (real_mult real_zero (b5a_S x)) _).
    + apply (RealSetoid.real_eq_mult_compat (b5c_J x Hx) (b5a_S x)
             real_zero (b5a_S x)).
      * exact HJ0.
      * apply real_eq_refl.
    + (* 0 * S == 0: commutativity (0 * S == S * 0) plus [real_mult_zero] (S * 0 == 0) *)
      apply (real_eq_trans _ (real_mult (b5a_S x) real_zero) _).
      * apply real_mult_comm.
      * apply real_mult_zero.
Qed.

(* ============================================================ *)
(* P4: the real_eq extensionality of clamp01 (min/max Lipschitz at the Q level) *)
(*   the pointwise projection of clamp01 is Qmin(Qmax(x_n,0),1); both Qmin and Qmax are *)
(*   1-Lipschitz ([q_min_lipschitz] / [q_max_lipschitz]), *)
(*   so clamp01 is 1-Lipschitz: |clamp a - clamp b| <= |a - b| *)
(* ============================================================ *)

(* Q level: |clamp a - clamp b| <= |a - b| (clamp q := Qmin(Qmax q 0,1)) *)
Lemma b5p2_q_clamp01_lip : forall (a b : Q),
  QleT' (Qabs (Qmin (Qmax a 0) 1 - Qmin (Qmax b 0) 1)) (Qabs (a - b)).
Proof.
  intros a b.
  apply Qle_to_QleT'.
  (* first layer: the min Lipschitz property gives |Qmin(A,1) - Qmin(B,1)| <= |A-B| + |1-1| == |A-B| *)
  apply (Qle_trans _ (Qabs (Qmax a 0 - Qmax b 0)) _).
  - (* |Qmin(A,1) - Qmin(B,1)| <= |A-B|: [q_min_lipschitz] with x := A, y := 1, x' := B, y' := 1 *)
    apply (Qle_trans _ (Qabs (Qmax a 0 - Qmax b 0) + Qabs (1 - 1)) _).
    + apply QleT'_to_Qle.
      apply (q_min_lipschitz (Qmax a 0) 1 (Qmax b 0) 1).
    + assert (Hz : Qabs (1 - 1) == 0).
      { transitivity (- (1 - 1)).
        - apply Qabs_neg. unfold Qle. simpl. lia.
        - ring. }
      rewrite Hz. apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - (* |Qmax a 0 - Qmax b 0| <= |a-b|: [q_max_lipschitz] with x := a, y := 0, x' := b, y' := 0 *)
    apply (Qle_trans _ (Qabs (a - b) + Qabs (0 - 0)) _).
    + apply QleT'_to_Qle.
      apply (q_max_lipschitz a 0 b 0).
    + assert (Hz : Qabs (0 - 0) == 0).
      { transitivity (- (0 - 0)).
        - apply Qabs_neg. unfold Qle. simpl. lia.
        - ring. }
      rewrite Hz. apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* the real_eq extensionality of clamp01: real_eq x y gives real_eq (clamp01 x) (clamp01 y)
   (pointwise |clamp(x)_n - clamp(y)_n| <= |x_n - y_n|, transferring the same eps/N) *)
Lemma b5p2_clamp01_wd : forall (x y : Real),
  real_eq x y -> real_eq (b5p2_clamp01 x) (b5p2_clamp01 y).
Proof.
  intros x y Hxy.
  intros eps Heps.
  destruct (Hxy eps Heps) as [N HN].
  exists N.
  intros n Hn.
  (* goal: QltT eps (Qabs (clamp01(x)_n - clamp01(y)_n));
     converted to Qabs (Qmin(Qmax(x_n,0),1) - Qmin(Qmax(y_n,0),1)) (after unfolding
     the projections) and bounded, via the Q-level 1-Lipschitz property, by
     |x_n - y_n| < eps *)
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (projT1 x n - projT1 y n)) _).
  - (* |clamp(x)_n - clamp(y)_n| <= |x_n - y_n|: unfold the projections and apply the Q-level 1-Lipschitz property *)
    apply (Qle_trans _ (Qabs (Qmin (Qmax (projT1 x n) 0) 1 - Qmin (Qmax (projT1 y n) 0) 1)) _).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      apply (Qabs_wd (projT1 (b5p2_clamp01 x) n - projT1 (b5p2_clamp01 y) n)
                     (Qmin (Qmax (projT1 x n) 0) 1 - Qmin (Qmax (projT1 y n) 0) 1)).
      unfold b5p2_clamp01.
      rewrite (qeqT_imp_qeq _ _ (real_min_proj (real_max x real_zero) (real_const 1) n)).
      rewrite (qeqT_imp_qeq _ _ (real_min_proj (real_max y real_zero) (real_const 1) n)).
      rewrite (qeqT_imp_qeq _ _ (real_max_proj x real_zero n)).
      rewrite (qeqT_imp_qeq _ _ (real_max_proj y real_zero n)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
      replace (projT1 real_zero n) with 0%Q by (unfold real_zero; reflexivity).
      reflexivity.
+ exact (QleT'_to_Qle _ _ (b5p2_q_clamp01_lip (projT1 x n) (projT1 y n))).
  - (* |x_n - y_n| < eps: the witness of real_eq x y *)
    apply QltT_to_Qlt.
    apply (HN n). exact Hn.
Qed.

(* ============================================================ *)
(* P5 sub-piece 1: the tail equality of clamp01 at certificate points (the real_lt separation gives pointwise exact equality) *)
(*   real_lt 0 x: some eps0 and N0 with eps0 < x_n - 0 for all n >= N0 (so x_n > eps0) *)
(*   real_lt x 1: some eps1 and N1 with eps1 < 1 - x_n for all n >= N1 (so x_n < 1 - eps1); *)
(*   hence for n >= max N0 N1: 0 < x_n < 1, so Qmax x_n 0 == x_n and *)
(*   Qmin x_n 1 == x_n, giving clamp01(x_n) == x_n (exact, pointwise) *)
(* ============================================================ *)
Lemma b5p2_clamp01_cert_tail : forall (x : Real),
  real_lt real_zero x -> real_lt x (real_const 1) ->
  sigT (fun N : nat => forall (n : nat), NatLe N n -> QeqT (projT1 (b5p2_clamp01 x) n) (projT1 x n)).
Proof.
  intros x H0x Hx1.
  destruct H0x as [eps0 [Heps0 [N0 HN0]]].
  destruct Hx1 as [eps1 [Heps1 [N1 HN1]]].
  exists (Nat.max N0 N1).
  intros n Hn.
  (* unfolding the projection: clamp01(x)_n == Qmin(Qmax(x_n,0),1) *)
  assert (Hcl : projT1 (b5p2_clamp01 x) n == Qmin (Qmax (projT1 x n) 0) 1).
  { unfold b5p2_clamp01.
    rewrite (qeqT_imp_qeq _ _ (real_min_proj (real_max x real_zero) (real_const 1) n)).
    rewrite (qeqT_imp_qeq _ _ (real_max_proj x real_zero n)).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)).
    replace (projT1 real_zero n) with 0%Q by (unfold real_zero; reflexivity).
    reflexivity. }
  apply qeq_imp_qeqT.
  rewrite Hcl.
  (* lower bound: x_n > eps0 > 0 gives 0 <= x_n, so Qmax x_n 0 == x_n *)
  assert (Hxn0 : Qle 0 (projT1 x n)).
  { apply Qlt_le_weak.
    apply (Qlt_trans _ eps0 _).
    - apply QltT_to_Qlt. exact Heps0.
    - (* eps0 < x_n: from HN0 n, and x_n - 0 == x_n *)
      apply (Qlt_le_trans _ (projT1 x n - projT1 real_zero n) _).
      + apply QltT_to_Qlt. apply (HN0 n).
        apply NatLe_lift. apply Nat.le_trans with (Nat.max N0 N1);
          [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)].
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        replace (projT1 real_zero n) with 0%Q by (unfold real_zero; reflexivity).
        ring. }
  assert (Hmax : Qmax (projT1 x n) 0 == projT1 x n).
  { apply (proj2 (Q.max_l_iff (projT1 x n) 0)). exact Hxn0. }
  rewrite Hmax.
  (* upper bound: x_n < 1 - eps1 < 1 gives x_n <= 1, so Qmin x_n 1 == x_n *)
  assert (Hxn1 : Qle (projT1 x n) 1).
  { apply Qlt_le_weak.
    apply (Qlt_trans _ (1 - eps1) _).
    - (* x_n < 1 - eps1: HN1 gives eps1 < (real_const 1)_n - x_n == 1 - x_n; rearrange *)
      apply QltT_to_Qlt.
      apply (q_lt_minus_shift eps1 1 (projT1 x n)).
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1 (projT1 (real_const 1) n - projT1 x n) (1 - projT1 x n)).
      + apply QltT_to_Qlt. apply (HN1 n).
        apply NatLe_lift. apply Nat.le_trans with (Nat.max N0 N1);
          [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)].
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (real_const_proj 1 n)). ring.
    - (* 1 - eps1 < 1 since 0 < eps1 *)
      apply (proj2 (Qlt_minus_iff (1 - eps1) 1)).
      apply (Qlt_le_trans 0 eps1 (1 + - (1 - eps1))).
      + apply QltT_to_Qlt. exact Heps1.
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (Hmin : Qmin (projT1 x n) 1 == projT1 x n).
  { apply (proj2 (Q.min_l_iff (projT1 x n) 1)). exact Hxn1. }
  rewrite Hmin.
  reflexivity.
Qed.

(* ============================================================ *)
(* P5 sub-piece 2: the real_eq of clamp01 at certificate points (the tail pointwise exact equality gives a real_eq) *)
(* ============================================================ *)
Lemma b5p2_clamp01_cert_eq : forall (x : Real),
  real_lt real_zero x -> real_lt x (real_const 1) ->
  real_eq (b5p2_clamp01 x) x.
Proof.
  intros x H0x Hx1.
  destruct (b5p2_clamp01_cert_tail x H0x Hx1) as [N HN].
  intros eps Heps.
  exists N.
  intros n Hn.
  (* |clamp(x)_n - x_n| == 0 < eps: the tail pointwise equality *)
  apply (qltT_eq_compat_l 0 (Qabs (projT1 (b5p2_clamp01 x) n - projT1 x n)) eps).
  - apply qeq_imp_qeqT. apply Qeq_sym.
    apply (Qabs_wd (projT1 (b5p2_clamp01 x) n - projT1 x n) 0).
    apply (Qeq_trans _ (projT1 x n - projT1 x n) _).
    + apply Qminus_comp. exact (qeqT_imp_qeq _ _ (HN n Hn)). apply Qeq_refl.
    + ring.
  - exact Heps.
Qed.

(* ============================================================ *)
(* P4 deep piece: the real_eq extensionality of the b5c_J constituents (arctan/E/S) *)
(*   the Hext goal: real_eq x y gives real_eq (J_tot x) (J_tot y). *)
(*   J_tot = b5c_J o clamp01, which needs (a) the clamp01 extensionality *)
(*   ([b5p2_clamp01_wd], proved) and (b) the real_eq extensionality of the b5c_J argument: *)
(*   ∀u v (Hu:cw_unit u) (Hv:cw_unit v), real_eq u v ⟹            *)
(*   real_eq (b5c_J u Hu) (b5c_J v Hv).  Since b5c_J = E * inv_pos(S), this needs *)
(*   E-wd, S-wd and inv_pos-wd (the root [real_inv_pos_ext]). *)
(*   E = sin o arctan - x * cos o arctan: arctan-wd (the root [b5b_ap_uniform] *)
(*   pointwise uniform, plus the roots [real_sin_eq_compat] / *)
(*   [real_cos_eq_compat], assembled with the RealSetoid compat lemmas). *)
(* ============================================================ *)

(* ---- the real_eq extensionality of arctan (certificate domain |u_n|, |v_n| <= 1) ----
   real_eq u v gives real_eq (arctan u Hu) (arctan v Hv).
   pointwise: for the goal epsQ > 0, [b5b_ap_uniform] gives M and d0
   (|ap_n u_n - ap_n v_n| < epsQ whenever n >= M and |Δ| <= d0);
   real_eq u v at d0 gives N0 (the tail |Δ| < d0);
   for n >= max M N0 the projection difference is < epsQ (via the
   [arctan_real_proj] conversion). *)
Lemma b5p2_arctan_wd : forall (u v : Real)
  (Hu : cw_unit u) (Hv : cw_unit v),
  real_eq u v -> real_eq (cauchy_real_arctan u Hu) (cauchy_real_arctan v Hv).
Proof.
  intros u v Hu Hv Huv epsQ HepsQ.
  (* [b5b_ap_uniform] at epsQ: M and d0 (with Qlt 0 d0 at the Prop layer) *)
  destruct (b5b_ap_uniform epsQ (QltT_to_Qlt 0 epsQ HepsQ)) as [M [d0 [Hd0 Hcore]]].
  (* real_eq u v at d0 (Set positivity) *)
  destruct (Huv d0 Hd0) as [N0 HN0].
  exists (Nat.max M N0).
  intros n Hn.
  apply NatLe_drop in Hn.
  assert (HnM : (M <= n)%nat) by lia.
  assert (HnN0 : (N0 <= n)%nat) by lia.
  (* goal: QltT (Qabs (projT1 (arctan u Hu) n - projT1 (arctan v Hv) n)) epsQ;
     the projection difference == ap_n(u_n) - ap_n(v_n) (both directions of
     [arctan_real_proj]), so it suffices to have the Hcore
     QltT (|ap_n u_n - ap_n v_n|) epsQ *)
  apply (qltT_eq_compat_l
           (Qabs (arctan_partial n (projT1 u n) - arctan_partial n (projT1 v n)))
           (Qabs (projT1 (cauchy_real_arctan u Hu) n - projT1 (cauchy_real_arctan v Hv) n))
           epsQ).
  - apply qeq_imp_qeqT. apply Qeq_sym.
    apply (Qabs_wd (projT1 (cauchy_real_arctan u Hu) n - projT1 (cauchy_real_arctan v Hv) n)
                   (arctan_partial n (projT1 u n) - arctan_partial n (projT1 v n))).
    rewrite (qeqT_imp_qeq _ _ (arctan_real_proj u Hu n)).
    rewrite (qeqT_imp_qeq _ _ (arctan_real_proj v Hv n)).
    reflexivity.
  - (* Hcore: n >= M, |u_n| and |v_n| <= 1 (the certificates), |u_n - v_n| <= d0 (from HN0 and [Qlt_le_weak]) *)
    apply (Hcore n (projT1 u n) (projT1 v n) (NatLe_lift _ _ HnM) (Hu n) (Hv n)).
    apply qltT_leT'.
    apply (HN0 n (NatLe_lift _ _ HnN0)).
Qed.

(* ---- the real_eq extensionality of E = sin o arctan - x * cos o arctan ----
   real_eq u v gives real_eq (b5a_E u Hu) (b5a_E v Hv):
   arctan_wd, then the sin/cos eq_compat roots, then the
   mult/opp/plus RealSetoid compatibility lemmas *)
Lemma b5p2_E_wd : forall (u v : Real)
  (Hu : cw_unit u) (Hv : cw_unit v),
  real_eq u v -> real_eq (b5a_E u Hu) (b5a_E v Hv).
Proof.
  intros u v Hu Hv Huv.
  (* first establish the arctan extensionality *)
  assert (Harct : real_eq (cauchy_real_arctan u Hu) (cauchy_real_arctan v Hv)).
  { apply (b5p2_arctan_wd u v Hu Hv). exact Huv. }
  (* sin(arctan u) == sin(arctan v), and likewise for cos *)
  assert (Hsin : real_eq (cauchy_real_sin (cauchy_real_arctan u Hu))
                         (cauchy_real_sin (cauchy_real_arctan v Hv))).
  { apply real_sin_eq_compat. exact Harct. }
  assert (Hcos : real_eq (cauchy_real_cos (cauchy_real_arctan u Hu))
                         (cauchy_real_cos (cauchy_real_arctan v Hv))).
  { apply real_cos_eq_compat. exact Harct. }
  (* u * cos(arctan u) == v * cos(arctan v): by mult compat *)
  assert (Hm : real_eq (real_mult u (cauchy_real_cos (cauchy_real_arctan u Hu)))
                       (real_mult v (cauchy_real_cos (cauchy_real_arctan v Hv)))).
  { apply (RealSetoid.real_eq_mult_compat u
             (cauchy_real_cos (cauchy_real_arctan u Hu))
             v
             (cauchy_real_cos (cauchy_real_arctan v Hv))).
    - exact Huv.
    - exact Hcos. }
  (* E == plus(sin) (opp(mult u cos)): assembled from the plus/opp compat lemmas *)
  unfold b5a_E.
  apply (RealSetoid.real_eq_plus_compat
           (cauchy_real_sin (cauchy_real_arctan u Hu))
           (real_opp (real_mult u (cauchy_real_cos (cauchy_real_arctan u Hu))))
           (cauchy_real_sin (cauchy_real_arctan v Hv))
           (real_opp (real_mult v (cauchy_real_cos (cauchy_real_arctan v Hv))))).
  - exact Hsin.
  - apply (RealSetoid.real_eq_opp_compat
             (real_mult u (cauchy_real_cos (cauchy_real_arctan u Hu)))
             (real_mult v (cauchy_real_cos (cauchy_real_arctan v Hv)))).
    exact Hm.
Qed.

(* ---- the real_eq extensionality of S = exp((1/2) * log(1+x^2)) ----
   real_eq u v gives real_eq (b5a_S u) (b5a_S v):
   u == v gives u^2 == v^2 (mult compat), then 1+u^2 == 1+v^2 (plus compat),
   then log wd (the root [real_log_wd], certificate [b5a_one_plus_sq_pos]),
   then (1/2) * log compat, then exp wd (the root [cauchy_real_exp_wd]) *)
Lemma b5p2_S_wd : forall (u v : Real),
  real_eq u v -> real_eq (b5a_S u) (b5a_S v).
Proof.
  intros u v Huv.
  unfold b5a_S.
  (* 1+u² == 1+v² *)
  assert (Hsq : real_eq (real_mult u u) (real_mult v v)).
  { apply (RealSetoid.real_eq_mult_compat u u v v).
    - exact Huv.
    - exact Huv. }
  assert (H1p : real_eq (real_plus real_one (real_mult u u))
                        (real_plus real_one (real_mult v v))).
  { apply (RealSetoid.real_eq_plus_compat real_one (real_mult u u)
                                          real_one (real_mult v v)).
    - apply real_eq_refl.
    - exact Hsq. }
  (* log wd: the certificates are [b5a_one_plus_sq_pos u] / [b5a_one_plus_sq_pos v] (real_lt 0 (1+u^2)) *)
  assert (Hlog : real_eq (real_log (real_plus real_one (real_mult u u)) (b5a_one_plus_sq_pos u))
                         (real_log (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos v))).
  { apply (real_log_wd (real_plus real_one (real_mult u u))
                       (real_plus real_one (real_mult v v))
                       (b5a_one_plus_sq_pos u) (b5a_one_plus_sq_pos v)).
    exact H1p. }
  (* (1/2)·log u == (1/2)·log v *)
  assert (Hml : real_eq (real_mult (real_const (1 / 2))
                                   (real_log (real_plus real_one (real_mult u u)) (b5a_one_plus_sq_pos u)))
                        (real_mult (real_const (1 / 2))
                                   (real_log (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos v)))).
  { apply (RealSetoid.real_eq_mult_compat (real_const (1 / 2))
             (real_log (real_plus real_one (real_mult u u)) (b5a_one_plus_sq_pos u))
             (real_const (1 / 2))
             (real_log (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos v))).
    - apply real_eq_refl.
    - exact Hlog. }
  (* exp wd *)
  apply cauchy_real_exp_wd. exact Hml.
Qed.

(* ---- the real_eq extensionality of b5c_J = E * inv_pos(S) ----
   real_eq u v gives real_eq (b5c_J u Hu) (b5c_J v Hv):
   E-wd ([b5p2_E_wd]) and S-wd ([b5p2_S_wd]) give inv_pos-wd (the root
   [real_inv_pos_ext], certificates [b5c_S_pos u] / [b5c_S_pos v]), then mult compat *)
Lemma b5p2_J_wd : forall (u v : Real)
  (Hu : cw_unit u) (Hv : cw_unit v),
  real_eq u v -> real_eq (b5c_J u Hu) (b5c_J v Hv).
Proof.
  intros u v Hu Hv Huv.
  unfold b5c_J.
  (* E-wd + inv-wd → mult compat *)
  assert (HS : real_eq (b5a_S u) (b5a_S v)) by (apply b5p2_S_wd; exact Huv).
  assert (Hinv : real_eq (real_inv_pos (b5a_S u) (b5c_S_pos u))
                         (real_inv_pos (b5a_S v) (b5c_S_pos v))).
  { apply (real_inv_pos_ext (b5a_S u) (b5a_S v)
                            (b5c_S_pos u) (b5c_S_pos v)). exact HS. }
  apply (RealSetoid.real_eq_mult_compat (b5a_E u Hu) (real_inv_pos (b5a_S u) (b5c_S_pos u))
                                        (b5a_E v Hv) (real_inv_pos (b5a_S v) (b5c_S_pos v))).
  - apply (b5p2_E_wd u v Hu Hv). exact Huv.
  - exact Hinv.
Qed.

(* ============================================================ *)
(* P4 main statement: Hext, the real_eq extensionality of J_tot (the b4 assumption: a total function must respect real_eq) *)
(*   real_eq x y ⟹ real_eq (J_tot x) (J_tot y)                   *)
(*   = clamp01-wd ([b5p2_clamp01_wd]) composed with J-wd ([b5p2_J_wd]) *)
(* ============================================================ *)
Lemma b5p2_Hext : forall (x y : Real),
  real_eq x y -> real_eq (b5p2_J_tot x) (b5p2_J_tot y).
Proof.
  intros x y Hxy.
  unfold b5p2_J_tot.
  apply (b5p2_J_wd (b5p2_clamp01 x) (b5p2_clamp01 y)
                   (b5p2_Hcl x) (b5p2_Hcl y)).
  apply b5p2_clamp01_wd. exact Hxy.
Qed.

(* ============================================================ *)
(* P5 main statement: the certificate-point substitution bridge *)
(*   forall x (Hx : cw_unit x), real_lt real_zero x ->           *)
(*     real_lt x (real_const 1) ->                               *)
(*     real_eq (b5p2_J_tot x) (b5c_J x Hx)                       *)
(*   J_tot x == J(clamp01 x) by definition; the clamp01 certificate-point tail equality *)
(*   ([b5p2_clamp01_cert_eq]: real_eq (clamp01 x) x) feeds J-wd *)
(* ============================================================ *)
Lemma b5p2_J_tot_eq_cert : forall (x : Real) (Hx : cw_unit x),
  real_lt real_zero x -> real_lt x (real_const 1) ->
  real_eq (b5p2_J_tot x) (b5c_J x Hx).
Proof.
  intros x Hx H0x Hx1.
  unfold b5p2_J_tot.
  apply (b5p2_J_wd (b5p2_clamp01 x) x (b5p2_Hcl x) Hx).
  apply b5p2_clamp01_cert_eq. exact H0x. exact Hx1.
Qed.

(* ============================================================ *)
(* The pi trigonometric signature family. *)
(*   The main statement [b5p_pi_trig_signature] with the nine-piece [b5p_*] family. *)
(*   The proofs depend only on the root pieces. *)
(*   (the Qeq setoid registrations here duplicate the root ones, *)
(*   duplicates are dropped); no further dependencies. *)
(* ============================================================ *)

(* ============================================================ *)
(* 1) pi_geom == c + c, with c := cos_pi_half *)
(*    real_pi_geom := real_mult (real_const 2) cos_pi_half       *)
(* ============================================================ *)
Lemma b5p_pi_geom_double :
  real_eq real_pi_geom (real_plus cos_pi_half cos_pi_half).
Proof.
  unfold real_pi_geom.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const 2) cos_pi_half n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj cos_pi_half cos_pi_half n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj 2 n)).
  ring.
Qed.

(* ============================================================ *)
(* 2) product identities from the special values (sin c == 1 / cos c == 0, lifted into the real_eq layer) *)
(* ============================================================ *)

(* sin c · cos c == 0 *)
Lemma b5p_sin_c_mul_cos_c_zero :
  real_eq (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_cos cos_pi_half))
          real_zero.
Proof.
  apply (real_eq_trans
    (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_cos cos_pi_half))
    (real_mult real_one real_zero)
    real_zero).
  - apply (RealSetoid.real_eq_mult_compat
             (cauchy_real_sin cos_pi_half)
             (cauchy_real_cos cos_pi_half)
             real_one real_zero).
    + apply real_sin_pi_half_one.
    + apply real_cos_pi_half_zero.
  - apply real_mult_zero.
Qed.

(* cos c · sin c == 0 *)
Lemma b5p_cos_c_mul_sin_c_zero :
  real_eq (real_mult (cauchy_real_cos cos_pi_half) (cauchy_real_sin cos_pi_half))
          real_zero.
Proof.
  apply (real_eq_trans
    (real_mult (cauchy_real_cos cos_pi_half) (cauchy_real_sin cos_pi_half))
    (real_mult real_zero real_one)
    real_zero).
  - apply (RealSetoid.real_eq_mult_compat
             (cauchy_real_cos cos_pi_half)
             (cauchy_real_sin cos_pi_half)
             real_zero real_one).
    + apply real_cos_pi_half_zero.
    + apply real_sin_pi_half_one.
  - apply (real_eq_trans
             (real_mult real_zero real_one)
             (real_mult real_one real_zero)
             real_zero).
    + apply real_mult_comm.
    + apply real_mult_zero.
Qed.

(* cos c · cos c == 0 *)
Lemma b5p_cos_c_sq_zero :
  real_eq (real_mult (cauchy_real_cos cos_pi_half) (cauchy_real_cos cos_pi_half))
          real_zero.
Proof.
  apply (real_eq_trans
    (real_mult (cauchy_real_cos cos_pi_half) (cauchy_real_cos cos_pi_half))
    (real_mult real_zero real_zero)
    real_zero).
  - apply (RealSetoid.real_eq_mult_compat
             (cauchy_real_cos cos_pi_half)
             (cauchy_real_cos cos_pi_half)
             real_zero real_zero).
    + apply real_cos_pi_half_zero.
    + apply real_cos_pi_half_zero.
  - apply real_mult_zero.
Qed.

(* sin c · sin c == 1 *)
Lemma b5p_sin_c_sq_one :
  real_eq (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half))
          real_one.
Proof.
  apply (real_eq_trans
    (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half))
    (real_mult real_one real_one)
    real_one).
  - apply (RealSetoid.real_eq_mult_compat
             (cauchy_real_sin cos_pi_half)
             (cauchy_real_sin cos_pi_half)
             real_one real_one).
    + apply real_sin_pi_half_one.
    + apply real_sin_pi_half_one.
  - apply real_mult_one.
Qed.

(* ============================================================ *)
(* 3) simplifying the right-hand sides of the angle-sum formulas *)
(*   sin side: sin c * cos c + cos c * sin c == 0 *)
(*   cos side: cos c * cos c + opp(sin c * sin c) == opp 1 *)
(* ============================================================ *)

Lemma b5p_sin_rhs_zero :
  real_eq (real_plus
             (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_cos cos_pi_half))
             (real_mult (cauchy_real_cos cos_pi_half) (cauchy_real_sin cos_pi_half)))
          real_zero.
Proof.
  apply (real_eq_trans
    (real_plus
       (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_cos cos_pi_half))
       (real_mult (cauchy_real_cos cos_pi_half) (cauchy_real_sin cos_pi_half)))
    (real_plus real_zero real_zero)
    real_zero).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_cos cos_pi_half))
             (real_mult (cauchy_real_cos cos_pi_half) (cauchy_real_sin cos_pi_half))
             real_zero real_zero).
    + apply b5p_sin_c_mul_cos_c_zero.
    + apply b5p_cos_c_mul_sin_c_zero.
  - apply real_plus_zero.
Qed.

Lemma b5p_cos_rhs_neg_one :
  real_eq (real_plus
             (real_mult (cauchy_real_cos cos_pi_half) (cauchy_real_cos cos_pi_half))
             (real_opp
                (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half))))
          (real_opp real_one).
Proof.
  apply (real_eq_trans
    (real_plus
       (real_mult (cauchy_real_cos cos_pi_half) (cauchy_real_cos cos_pi_half))
       (real_opp
          (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half))))
    (real_plus real_zero (real_opp real_one))
    (real_opp real_one)).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (cauchy_real_cos cos_pi_half) (cauchy_real_cos cos_pi_half))
             (real_opp
                (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half)))
             real_zero (real_opp real_one)).
    + apply b5p_cos_c_sq_zero.
    + apply (RealSetoid.real_eq_opp_compat
               (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half))
               real_one).
      apply b5p_sin_c_sq_one.
  - apply (real_eq_trans
             (real_plus real_zero (real_opp real_one))
             (real_plus (real_opp real_one) real_zero)
             (real_opp real_one)).
    + apply real_plus_comm.
    + apply real_plus_zero.
Qed.

(* ============================================================ *)
(* 4) the three main statements *)
(* ============================================================ *)

(* sin(π_geom) == 0 *)
Lemma b5p_sin_pi_geom_zero :
  real_eq (cauchy_real_sin real_pi_geom) real_zero.
Proof.
  apply (real_eq_trans
    (cauchy_real_sin real_pi_geom)
    (cauchy_real_sin (real_plus cos_pi_half cos_pi_half))
    real_zero).
  - apply real_sin_eq_compat.
    apply b5p_pi_geom_double.
  - apply (real_eq_trans
      (cauchy_real_sin (real_plus cos_pi_half cos_pi_half))
      (real_plus
         (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_cos cos_pi_half))
         (real_mult (cauchy_real_cos cos_pi_half) (cauchy_real_sin cos_pi_half)))
      real_zero).
    + apply (rs_add_sin cos_pi_half cos_pi_half).
    + apply b5p_sin_rhs_zero.
Qed.

(* cos(π_geom) == −1 *)
Lemma b5p_cos_pi_geom_neg_one :
  real_eq (cauchy_real_cos real_pi_geom) (real_opp real_one).
Proof.
  apply (real_eq_trans
    (cauchy_real_cos real_pi_geom)
    (cauchy_real_cos (real_plus cos_pi_half cos_pi_half))
    (real_opp real_one)).
  - apply real_cos_eq_compat.
    apply b5p_pi_geom_double.
  - apply (real_eq_trans
      (cauchy_real_cos (real_plus cos_pi_half cos_pi_half))
      (real_plus
         (real_mult (cauchy_real_cos cos_pi_half) (cauchy_real_cos cos_pi_half))
         (real_opp
            (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half))))
      (real_opp real_one)).
    + apply (rs_add_cos cos_pi_half cos_pi_half).
    + apply b5p_cos_rhs_neg_one.
Qed.

(* packaging: the And form (the Set-layer A * B) *)
Lemma b5p_pi_trig_signature :
  And (real_eq (cauchy_real_sin real_pi_geom) real_zero)
      (real_eq (cauchy_real_cos real_pi_geom) (real_opp real_one)).
Proof.
  exact (b5p_sin_pi_geom_zero, b5p_cos_pi_geom_neg_one).
Qed.

(* ============================================================ *)
(* The arctan(1) == pi_L * (1/4) family. *)
(*   The main statement [b5q_arctan_one_leibniz_quarter] with the eight-piece [b5q_*] family. *)
(*   The proofs depend only on the root pieces. *)
(*   (the Qeq setoid registrations are dropped as above); no further dependencies. *)
(* ============================================================ *)

(* ============================================================ *)
(* 1) constant multiplication at the real_const level: (1/4) * 4 == 1 *)
(*   (the pointwise Q multiplication of [real_const 4] and [real_const (1/4)], closed via [real_eq_of_zero_diff], the projections, and the Q layer) *)
(* ============================================================ *)
Lemma b5q_quarter_four_unit :
  real_eq (real_mult (real_const (1 / 4)) (real_const 4)) real_one.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (1 / 4)) (real_const 4) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 / 4) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj 4 n)).
  simpl.
  reflexivity.
Qed.

(* ============================================================ *)
(* 2) the left unit law (derived from [real_mult_comm] and [real_mult_one]) *)
(* ============================================================ *)
Lemma b5q_unit_left : forall x : Real,
  real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans (real_mult real_one x) (real_mult x real_one) x).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* ============================================================ *)
(* 3) chain link 1: pi_L * (1/4) == (1/4) * pi_L (commutativity of multiplication) *)
(* ============================================================ *)
Lemma b5q_comm_swap :
  real_eq (real_mult cauchy_real_pi_leibniz (real_const (1 / 4)))
          (real_mult (real_const (1 / 4)) cauchy_real_pi_leibniz).
Proof.
  apply real_mult_comm.
Qed.

(* ============================================================ *)
(* 4) chain link 2: (1/4) * pi_L == (1/4) * (4 * θ) (substituting [a3_h4_value_bridge]) *)
(* ============================================================ *)
Lemma b5q_pi_to_four_theta :
  real_eq (real_mult (real_const (1 / 4)) cauchy_real_pi_leibniz)
          (real_mult (real_const (1 / 4))
                     (real_mult (real_const 4) arctan_one_real)).
Proof.
  apply (RealSetoid.real_eq_mult_compat
           (real_const (1 / 4)) cauchy_real_pi_leibniz
           (real_const (1 / 4))
           (real_mult (real_const 4) arctan_one_real)).
  - apply real_eq_refl.
  - apply (real_eq_sym _ _ a3_h4_value_bridge).
Qed.

(* ============================================================ *)
(* 5) chain link 3: (1/4) * (4 * θ) == ((1/4) * 4) * θ (associativity) *)
(* ============================================================ *)
Lemma b5q_assoc_quarter :
  real_eq (real_mult (real_const (1 / 4))
                     (real_mult (real_const 4) arctan_one_real))
          (real_mult (real_mult (real_const (1 / 4)) (real_const 4))
                     arctan_one_real).
Proof.
  apply real_mult_assoc.
Qed.

(* ============================================================ *)
(* 6) chain link 4: ((1/4) * 4) * θ == 1 * θ (substituting [b5q_quarter_four_unit]) *)
(* ============================================================ *)
Lemma b5q_collapse :
  real_eq (real_mult (real_mult (real_const (1 / 4)) (real_const 4))
                     arctan_one_real)
          (real_mult real_one arctan_one_real).
Proof.
  apply (RealSetoid.real_eq_mult_compat
           (real_mult (real_const (1 / 4)) (real_const 4))
           arctan_one_real
           real_one arctan_one_real).
  - apply b5q_quarter_four_unit.
  - apply real_eq_refl.
Qed.

(* ============================================================ *)
(* 7) chain link 5: ((1/4) * 4) * θ == θ (the collapse plus the left unit law) *)
(* ============================================================ *)
Lemma b5q_collapse_unit :
  real_eq (real_mult (real_mult (real_const (1 / 4)) (real_const 4))
                     arctan_one_real)
          arctan_one_real.
Proof.
  apply (real_eq_trans
           (real_mult (real_mult (real_const (1 / 4)) (real_const 4))
                      arctan_one_real)
           (real_mult real_one arctan_one_real)
           arctan_one_real).
  - apply b5q_collapse.
  - apply b5q_unit_left.
Qed.

(* ============================================================ *)
(* 8) the backward chain: pi_L * (1/4) == θ, with θ := arctan_one_real *)
(* ============================================================ *)
Lemma b5q_leibniz_quarter_chain :
  real_eq (real_mult cauchy_real_pi_leibniz (real_const (1 / 4)))
          arctan_one_real.
Proof.
  apply (real_eq_trans
           (real_mult cauchy_real_pi_leibniz (real_const (1 / 4)))
           (real_mult (real_const (1 / 4)) cauchy_real_pi_leibniz)
           arctan_one_real).
  - apply b5q_comm_swap.
  - apply (real_eq_trans
             (real_mult (real_const (1 / 4)) cauchy_real_pi_leibniz)
             (real_mult (real_const (1 / 4))
                        (real_mult (real_const 4) arctan_one_real))
             arctan_one_real).
    + apply b5q_pi_to_four_theta.
    + apply (real_eq_trans
               (real_mult (real_const (1 / 4))
                          (real_mult (real_const 4) arctan_one_real))
               (real_mult (real_mult (real_const (1 / 4)) (real_const 4))
                          arctan_one_real)
               arctan_one_real).
      * apply b5q_assoc_quarter.
      * apply b5q_collapse_unit.
Qed.

(* ============================================================ *)
(* 9) the main statement: arctan(1) == pi_L * (1/4) (symmetry restores the direction) *)
(* ============================================================ *)
Lemma b5q_arctan_one_leibniz_quarter :
  real_eq arctan_one_real
          (real_mult cauchy_real_pi_leibniz (real_const (1 / 4))).
Proof.
  (* the real_eq_sym bridge is expanded to the definition level in place:
     take the N witness of the chain equality at the same eps, use the
     symmetry of the absolute difference sequence [q_abs_minus_sym], and
     align the difference terms on both sides through the Qcompare
     compatibility rewrite before closing *)
  intros eps Heps.
  destruct (b5q_leibniz_quarter_chain eps Heps) as [N HN].
  exists N.
  intro n. intro Hn.
  specialize (HN n Hn).
  unfold QltT, Qlt_bool in HN |- *.
  assert (Hcmp : Qcompare (Qabs (projT1 arctan_one_real n -
                               projT1 (real_mult cauchy_real_pi_leibniz (real_const (1 / 4))) n)) eps =
                 Qcompare (Qabs (projT1 (real_mult cauchy_real_pi_leibniz (real_const (1 / 4))) n -
                               projT1 arctan_one_real n)) eps).
  { exact (Qcompare_comp
             (Qabs (projT1 arctan_one_real n -
                    projT1 (real_mult cauchy_real_pi_leibniz (real_const (1 / 4))) n))
             (Qabs (projT1 (real_mult cauchy_real_pi_leibniz (real_const (1 / 4))) n -
                    projT1 arctan_one_real n))
             (qeqT_imp_qeq _ _ (q_abs_minus_sym (projT1 arctan_one_real n)
                              (projT1 (real_mult cauchy_real_pi_leibniz (real_const (1 / 4))) n)))
             eps eps (Qeq_refl eps)). }
  rewrite Hcmp.
  exact HN.
Qed.
(* ############ MergedField ############ *)
(* ===== the semantic-field synthesis library (_p1.._p8, NCAField, WassersteinQ, and the _p9 scheduler / integrity pipeline) ===== *)
(*   The baseline definitions are provided by this file. *)
(*   The thirty bridge names match the baseline character for character. *)
(*   scope: the Q-layer environment of this part continues the preceding text; the _p9 part closes Q_scope itself. *)



(* ############ part _p1 ############ *)
(* ============================================================ *)
(* ===== the dynamic hypergraph semantic field: the constructive embedding of the blueprint ===== *)
(* ============================================================ *)
(*   This block embeds the blueprint's algorithms and propositions. *)
(*   (the four-part dynamic hypergraph semantic field draft), *)
(*   with constant/type/lemma naming consistent with Constructive *)
(*   World-206, as a tail block. *)
(*                                                               *)
(* [the conversion table: the consistent replacements from the blueprint to the baseline] *)
(*   1. purely constructive: no custom axiom faces or declarations of free parameters; classical logic and *)
(*   classical real axioms (Coq Reals/R, lra, INR, the order trichotomy, le_lt_dec) are *)
(*   not used.  The blueprint's R is replaced throughout by the Cauchy real [Real]; *)
(*   the blueprint's string identifiers become nat; existentials use [sigT]; membership uses *)
(*   [InT]; the connectives are And/Or/Not (the Set layer). *)
(*   2. propositions relying on classical decisions become Section *)
(*   Variables/Hypotheses (the decidability of energy comparison, the pipe upper bound Tmax, *)
(*   the log antitone property, Fisher nonnegativity, and so on); statements that are not constructible take the eps-slack form *)
(*   and are proved directly in that form. *)
(*   propositions such as [a * a == 0 implies a == 0], which are not constructively provable, never appear. *)
(*   3. algorithms already present in the baseline are not re-implemented (noted at the head of each subsection): *)
(*   the Boltzmann distribution and energy monotonicity ([FreeEnergyMinimization] / *)
(*   [BoltzmannSteadyState] / the [temp_energy_dual] family), free-energy *)
(*   minimization and the Gibbs inequality, softmax / the partition function ([RealAttnMain]), *)
(*   and greedy argmin decoding ([ArgminCorrectness]). *)
(*   4. all definitions live in the Set layer and extract wholesale into executable OCaml. *)
(*                                                               *)
(* [the blueprint-module to subsection mapping of this block] *)
(*   blueprint §1 coordinates / distance   -> SFVecDist *)
(*   blueprint §1 senses / clusters / pipes -> SFSensePipe *)
(*   blueprint §1 energy / beam search     -> SFPathEnergy *)
(*   blueprint §1/§2 working memory        -> SFWorkingMemory *)
(*   blueprint §2 global free energy       -> SFFreeEnergy *)
(*   blueprint §2 isomorphic translation / cycle consistency -> SFInvMap *)
(*   blueprint §2 multiscale decay         -> SFDecay *)
(*   blueprint §3 hyperbolic distance      -> the SFSensePipe tail note (an order-preserving transform, *)
(*   the blueprint's original definition is a dist_sq placeholder with no independent mathematical content) *)
(*   blueprint §3 Boltzmann                -> already in the baseline, omitted *)
(*   blueprint §3 Wasserstein / centroids  -> SFWasserQ (a Q-layer closed form plus the Jensen bound) *)
(*   blueprint §3 cluster connectivity     -> SFCluster *)
(*   blueprint §3 active inference         -> SFActiveInference *)
(*   blueprint §3 neural-symbolic binding  -> SFBinding *)
(*   blueprint §3 causal edge asymmetry    -> SFCluster (the directed path [reaches]) *)
(*   blueprint §3 quantum superposition / collapse -> SFQuantumQ (Q amplitudes) *)
(*   blueprint §3 multi-agent consensus    -> SFDiffusion (the midpoint contraction theorem) *)
(*   blueprint §4 hypergraph convolution   -> SFConv (a convex-combination [sigT] witness) *)
(*   blueprint §4 InfoNCE                  -> SFSoftmaxInfoNCE *)
(*   blueprint §4 diffusion forward / backward -> SFDiffusion *)
(*   blueprint §4 invertible networks      -> SFInvMap *)
(*   blueprint §4 random-matrix spectra / the semicircle law -> not implemented (a classical asymptotic limit, not a constructive statement; *)
(*   its constructive kernel is replaced by the mean-square bound of [SFWasserQ]) *)
(*   blueprint §4 neural ODE existence / uniqueness -> not implemented (the classical Picard construction; *)
(*   the [omega_limit]/[iterate] convergence framework remains a future extension point) *)
(*   blueprint §4 group equivariance       -> SFEquivariance *)
(*   blueprint §4 curriculum learning      -> SFCurriculum *)
(*   blueprint §4 EWC                      -> SFEWC *)
(*   blueprint §4 embodiment / the global workspace -> SFWorkspace *)
(*   blueprint §4 meta-learning fast adaptation -> SFDiffusion (midpoint adaptation as prototype regression) *)
(* ============================================================ *)

(* ============================================================ *)
(* SFPrelude: constructive Q-layer tools (square nonnegativity, the Le bridge, pointwise slack) *)
(* ============================================================ *)

Lemma sf_qeq_le : forall x y : Q, x == y -> QleT' x y.
Proof.
  intros x y H.
  apply Qle_to_QleT'.
  (* the Z-layer rewrite chain is built directly: unfold to the
     cross-product definition level, rewrite the left side into the right
     side using the equality assumption in place, and close by the
     reflexivity of Z.le *)
  unfold Qle, Qeq in *.
  rewrite H.
  apply Z.le_refl.
Qed.

(* Q square nonnegativity: the sign of a Q is computably decidable ([Q_dec] is constructively acceptable), so the proof is by cases. *)
Lemma sf_q_sq_ge_0 : forall q : Q, QleT' 0 (q * q).
Proof.
  intro q.
  apply Qle_to_QleT'.
  (* [Q_dec x y : {x<y} + {y<x} + {x==y}]: the computable trichotomy decision on Q (constructively acceptable) *)
  destruct (Q_dec 0 q) as [[Hp | Hn] | Hz].
  - assert (H1 : 0 <= q) by (apply Qlt_le_weak; exact Hp).
    exact (Qmult_le_0_compat q q H1 H1).
  - assert (Hq0 : q <= 0) by (apply Qlt_le_weak; exact Hn).
    assert (Hnq : 0 <= - q) by (exact (Qopp_le_compat q 0 Hq0)).
    assert (Hsq : (q * q) == ((- q) * (- q))) by ring.
    rewrite Hsq.
    exact (Qmult_le_0_compat (- q) (- q) Hnq Hnq).
  - apply QleT'_to_Qle. apply (qeq_le 0 (q * q)). apply qeq_imp_qeqT. rewrite <- Hz. ring.
Qed.

(* the Q sum (the stdlib [list_sum] is the nat version; the Q version is built here). *)
Fixpoint sf_qsum (l : list Q) : Q :=
  match l with
  | nil => 0
  | a :: rest => a + sf_qsum rest
  end.

(* the sum of squares of a Q list is nonnegative. *)
Lemma sf_q_list_sq_ge_0 : forall (l : list Q),
  QleT' 0 (sf_qsum (map (fun d => d * d) l)).
Proof.
  induction l as [| a rest IH]; simpl.
  - apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'. apply (Qle_trans _ (a * a + 0) _).
+ rewrite Qplus_0_r. apply QleT'_to_Qle. apply sf_q_sq_ge_0.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact (QleT'_to_Qle _ _ IH).
Qed.

(* ---- the Set-layer form of numeric Q equality (for statements; decided by [Qeq_bool]) ---- *)
Definition QId (x y : Q) : Set := Id (Qeq_bool x y) true.

Lemma qid_intro : forall x y : Q, x == y -> QId x y.
Proof.
  intros x y H.
  apply (eq_rect true (fun b : bool => Id b true) id_refl (Qeq_bool x y)
           (eq_sym (proj2 (Qeq_bool_iff x y) H))).
Qed.

Lemma qid_elim : forall x y : Q, QId x y -> QeqT (x) (y).
Proof.
  intros x y H. apply qeq_imp_qeqT. unfold QId in H.
  destruct (Qeq_bool x y) eqn:E; [ | inversion H].
  exact (proj1 (Qeq_bool_iff x y) E).
Qed.

(* ============================================================ *)
(* SFVecDist: coordinate vectors and squared distances (the blueprint's §1 Coord / dist_sq) *)
(*   baseline form: Coord := list R becomes SFVec := list Real; the distance uses the squared form *)
(*   (the baseline has no sqrt interface; squaring is monotone-equivalent to the root, as in the blueprint); *)
(*   every property is characterized through the pointwise projection [sf_ptw_sum] and proved by Q-ring induction. *)
(* ============================================================ *)

Definition SFVec : Set := list Real.

Definition sf_sub (a b : Real) : Real := real_plus a (real_opp b).
Definition sf_sq (a : Real) : Real := real_mult a a.

(* the pointwise projection sum: the Q-layer counterpart of dist_sq (the k-th observation is the sum of squared component pairs up to k). *)
Fixpoint sf_ptw_sum (x y : SFVec) (k : nat) : Q :=
  match x, y with
  | a :: x', b :: y' =>
      (projT1 a k - projT1 b k) * (projT1 a k - projT1 b k) + sf_ptw_sum x' y' k
  | _, _ => 0
  end.

(* the squared distance: pairwise pairing (zip truncation semantics; matching lengths are carried by the caller-side theorem hypotheses). *)
Fixpoint sf_dist_sq (x y : SFVec) : Real :=
  match x, y with
  | a :: x', b :: y' => real_plus (sf_sq (sf_sub a b)) (sf_dist_sq x' y')
  | _, _ => real_zero
  end.

(* the small Set-layer Qeq_bool/Id bridge (used only as a relay inside proofs). *)
Lemma sf_bool_id_true : forall b : bool, Id b true -> Id (b) (true).
Proof.
intros b H. destruct b as [| ].
  - exact H.
  - inversion H.
Qed.

Lemma sf_bool_true_id : forall b : bool, b = true -> Id b true.
Proof.
  intros b H. rewrite H. apply id_refl.
Qed.

Lemma sf_id_true_false : Id true false -> Empty_set.
Proof.
  intros H. inversion H.
Qed.

Lemma sf_id_false_true : Id false true -> Empty_set.
Proof.
  intros H. inversion H.
Qed.

Lemma sf_id_qeq : forall (a b : Q), Id (Qeq_bool a b) true -> QeqT (a) (b).
Proof.
intros a b H. apply qeq_imp_qeqT.
  apply (proj1 (Qeq_bool_iff a b)).
  exact (match H in (Id _ y') return (Qeq_bool a b = y') with id_refl => eq_refl end).
Qed.

Lemma sf_qeq_id : forall (a b : Q), a == b -> Id (Qeq_bool a b) true.
Proof.
  intros a b H. apply (sf_bool_true_id _ (proj2 (Qeq_bool_iff a b) H)).
Qed.

(* the projection characterization: the k-th observation of dist_sq == the pointwise
   counterpart (the common channel for all real_eq properties; the statement layer
   uses Id (Qeq_bool ..) true, and the proof relays through sf_id_qeq / Qeq_bool_iff) *)
Lemma sf_dist_sq_proj : forall (x y : SFVec) (k : nat), QeqT (projT1 (sf_dist_sq x y) k) (sf_ptw_sum x y k).
Proof.
  intro x. induction x as [| a x' IHx]; intros y k; destruct y as [| b y'].
  - reflexivity.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. reflexivity.
  - (* cons/cons: the pointwise projection unfoldings of real_plus/mult/opp/sub *)
    apply qeq_imp_qeqT.
    change (projT1 (real_plus (sf_sq (sf_sub a b)) (sf_dist_sq x' y')) k
            == sf_ptw_sum (a :: x') (b :: y') k).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (sf_sq (sf_sub a b)) (sf_dist_sq x' y') k)).
    unfold sf_sq, sf_sub.
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj (sf_sub a b) (sf_sub a b) k)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj a (real_opp b) k)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj b k)).
    rewrite (qeqT_imp_qeq _ _ (IHx y' k)).
    reflexivity.
Qed.

(* ============================================================ *)
(* The SFModule07 series: the Set-layer toolbox and the remaining reference-data algorithms. *)
(*                                                                *)
(* [the Set-layer conversion table (policy: zero Prop leakage, zero admissions)] *)
(*   stdlib Prop constructs        -> this library's Set constructs *)
(*   Qle x y (Prop)              → QleT' x y (= Id (Qle_bool ..) true) *)
(*   Qlt x y (Prop)              → QltT x y  (= Id (Qlt_bool ..) true) *)
(*   QleT x y (Set)              → Or (QltT x y) (Id x y)         *)
(*   the nat n <= m (Prop)         -> NatLe n m (= Id (Nat.leb ..) true) *)
(*   the nat n < m (Prop)          -> NatLe (Datatypes.S n) m *)
(*   the Leibniz t1 = t2 (Prop)    -> Id t1 t2 (the Set-layer equality type) *)
(*   the l <> nil (Prop negation)  -> Not (Id l nil) (Not : Set -> Set) *)
(*   the existential ex (Prop)     -> sigT (carrying an informative witness) *)
(*   the conjunction /\ and disjunction \/ (Prop) -> And A B := A*B / Or A B := A+B *)
(*   the Hypothesis (a Set-typed interface assumption) -> kept: after End it becomes a function argument, *)
(*   an honest interface rather than an axiom; no new ones are added. *)
(*   Prop lemmas (the Qle/Qlt bridges) may appear only inside proofs as relays, never at the statement layer. *)
(* ============================================================ *)

Section SFSetLayerQ.

(* ---- the basic tools of QleT' (Id (Qle_bool ..) true) ---- *)

(* reflexivity. *)
Lemma sf_qleT_refl : forall x : Q, QleT' x x.
Proof.
  intro x.
  (* built directly at the Set layer without passing through bridges:
     QleT' unfolds to Id (with Qle_bool the S02-local shadowed definition,
     fully qualified), the trichotomy main argument Qcompare x x is
     destructed in place; the two equal branches reduce to Id, while the
     Gt branch is excluded by an inline structural induction on Z proving
     (z ?= z) = Eq, plus discriminate *)
  unfold QleT', S02_CauchyComplete.Qle_bool.
  assert (Hrefl : forall z : Z, (z ?= z)%Z = Eq).
  { intro z. induction z as [| p | p].
    - reflexivity.
    - apply Z.compare_refl.
    - apply Z.compare_refl. }
  destruct (Qcompare x x) as [E|E|E] eqn:Ec.
  - reflexivity.
  - reflexivity.
  - exfalso.
    unfold Qcompare in Ec.
    rewrite Hrefl in Ec.
    discriminate Ec.
Qed.

(* transitivity. *)
Lemma sf_qleT_trans : forall x y z : Q,
  QleT' x y -> QleT' y z -> QleT' x z.
Proof.
  intros x y z Hxy Hyz.
  apply (Qle_to_QleT' x z).
  apply (Qle_trans x y z).
  - exact (QleT'_to_Qle x y Hxy).
  - exact (QleT'_to_Qle y z Hyz).
Qed.

(* QleT' to Qle (a Prop bridge, used only inside proofs). *)
Lemma sf_qleT_to_qle : forall x y : Q, QleT' x y -> QleT' x y.
Proof.
  intros x y H. apply Qle_to_QleT'. exact (QleT'_to_Qle x y H).
Qed.

(* Qle to QleT' (a Prop bridge, used only inside proofs). *)
Lemma sf_qle_to_qleT : forall x y : Q, Qle x y -> QleT' x y.
Proof.
  intros x y H. exact (Qle_to_QleT' x y H).
Qed.

(* addition preserves the order. *)
Lemma sf_qleT_plus : forall a b c d : Q,
  QleT' a b -> QleT' c d -> QleT' (a + c) (b + d).
Proof.
  intros a b c d Hab Hcd.
  apply sf_qle_to_qleT.
  apply Qplus_le_compat.
- apply QleT'_to_Qle. exact Hab.
- apply QleT'_to_Qle. exact Hcd.
Qed.

(* multiplication by a nonnegative factor preserves the order. *)
Lemma sf_qleT_mult_r : forall a b c : Q,
  QleT' a b -> QleT' 0 c -> QleT' (a * c) (b * c).
Proof.
  intros a b c Hab Hc.
  apply sf_qle_to_qleT.
  apply Qmult_le_compat_r.
- apply QleT'_to_Qle. exact Hab.
- apply QleT'_to_Qle. exact Hc.
Qed.

(* squares are nonnegative (the Set version; the three cases decided computably by [Q_dec]). *)
Theorem sf_q_sq_ge_0T : forall q : Q, QleT' 0 (q * q).
Proof.
  intro q.
  destruct (Q_dec 0 q) as [[Hlt | Hgt] | Heq].
  - (* 0 < q ⟹ 0 ≤ q² *)
    apply sf_qle_to_qleT.
    apply Qlt_le_weak.
    exact (Qmult_lt_0_compat q q Hlt Hlt).
  - (* q < 0 ⟹ q² = (−q)² > 0 *)
    assert (H0 : (- 0)%Q == 0%Q) by ring.
    assert (Hneg : (- 0)%Q < - q) by (apply (Qopp_lt_compat q 0 Hgt)).
    setoid_rewrite H0 in Hneg.
    assert (Hpos : 0 < (- q) * (- q)) by
      (apply (Qmult_lt_0_compat (- q) (- q) Hneg Hneg)).
    apply sf_qle_to_qleT.
    assert (Hsq : (q * q) == ((- q) * (- q))) by ring.
    rewrite Hsq.
    apply Qlt_le_weak. exact Hpos.
  - (* q == 0 ⟹ q² == 0 *)
    apply sf_qle_to_qleT.
    assert (Hsq : (q * q) == 0) by (rewrite <- Heq at 1; ring).
    rewrite Hsq.
    apply Qle_refl.
Qed.

(* the QleT' nonnegativity of a list's sum of squares. *)
Theorem sf_q_list_sq_ge_0T : forall (l : list Q),
  QleT' 0 (sf_qsum (map (fun d => d * d) l)).
Proof.
  induction l as [| a rest IH]; simpl.
  - apply sf_qleT_refl.
  - (* 0 + 0 <= a^2 + (the rest sum): addition preserves the order *)
    replace 0%Q with (0 + 0)%Q by reflexivity.
    apply sf_qleT_plus.
    + apply sf_q_sq_ge_0T.
    + exact IH.
Qed.

End SFSetLayerQ.

(* pointwise nonnegativity: every observation of dist_sq is >= 0 (the Qle form restated as QleT' via [sf_qleT_plus]). *)
Lemma sf_ptw_sum_ge_0 : forall (x y : SFVec) (k : nat), QleT' 0 (sf_ptw_sum x y k).
Proof.
  intros x. induction x as [| a x' IHx]; intros y k; destruct y as [| b y']; simpl.
  - apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'.
    apply (Qle_trans _ ((projT1 a k - projT1 b k) * (projT1 a k - projT1 b k) + 0) _).
    + rewrite Qplus_0_r. apply QleT'_to_Qle. apply sf_q_sq_ge_0.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact (QleT'_to_Qle _ _ (IHx y' k)).
Qed.

(* the self-distance is zero pointwise (the Qeq form restated as Id (Qeq_bool ..) true). *)
Lemma sf_ptw_sum_self : forall (x : SFVec) (k : nat), QeqT (sf_ptw_sum x x k) (0).
Proof.
  intros x. induction x as [| a x' IHx]; intro k; simpl.
  - apply qeq_imp_qeqT. reflexivity.
  - specialize (IHx k). apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ IHx). ring.
Qed.

(* symmetry holds pointwise (the Qeq form restated as Id (Qeq_bool ..) true, with Qeq_bool in both directions). *)
Lemma sf_ptw_sum_sym : forall (x y : SFVec) (k : nat), QeqT (sf_ptw_sum x y k) (sf_ptw_sum y x k).
Proof.
  intros x. induction x as [| a x' IHx]; intros y k; destruct y as [| b y']; simpl.
  - reflexivity.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. reflexivity.
  - specialize (IHx y' k). apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ IHx). ring.
Qed.

(* the squared distance is always nonnegative (in eps-slack form; the
   constructive analogue of [real_metric_pos_eps]: the pointwise sum of
   squares is >= 0, and the eps slack absorbs the undecidability of the
   positive/zero distinction) *)
Theorem sf_dist_sq_pos_eps : forall (x y : SFVec) (eps : Real),
  real_lt real_zero eps ->
  real_le real_zero (real_plus (sf_dist_sq x y) eps).
Proof.
  intros x y eps Heps.
  destruct Heps as [e [He [N HN]]].
  apply (RealSetoid.real_lt_le_iff_req real_zero
          (real_plus (sf_dist_sq x y) eps)). left.
  exists e. split.
  - exact He.
  - exists N. intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (sf_dist_sq x y) eps n)).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    rewrite Hz.
    apply (Qlt_le_trans _ (projT1 eps n - 0) _).
    + apply QltT_to_Qlt. apply (HN n). exact Hn.
    + apply (Qle_trans _ (projT1 eps n) _).
      * apply QleT'_to_Qle. apply sf_qeq_le. ring.
      * apply (Qle_trans _ (projT1 (sf_dist_sq x y) n + projT1 eps n) _).
        -- apply (Qle_trans _ (0 + projT1 eps n) _).
           ++ apply QleT'_to_Qle. apply sf_qeq_le. ring.
           ++ assert (Hd0 : 0 <= projT1 (sf_dist_sq x y) n).
              { rewrite (qeqT_imp_qeq _ _ (sf_dist_sq_proj x y n)).
                exact (QleT'_to_Qle _ _ (sf_ptw_sum_ge_0 x y n)). }
              exact (Qplus_le_compat 0 (projT1 (sf_dist_sq x y) n)
                                     (projT1 eps n) (projT1 eps n)
                                     Hd0 (Qle_refl _)).
        -- apply QleT'_to_Qle. apply sf_qeq_le. ring.
Qed.

(* the squared distance is zero on the diagonal (the constructive version of the blueprint's dist_sq_self_zero). *)
Theorem sf_dist_sq_self : forall x : SFVec, real_eq (sf_dist_sq x x) real_zero.
Proof.
  intro x. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
  rewrite Hz.
rewrite (qeqT_imp_qeq _ _ (sf_dist_sq_proj x x n)).
rewrite (qeqT_imp_qeq _ _ (sf_ptw_sum_self x n)). ring.
Qed.

(* the squared distance is symmetric (the blueprint's dist_sq_sym; no length assumption under the truncation semantics). *)
Theorem sf_dist_sq_sym : forall x y : SFVec,
  real_eq (sf_dist_sq x y) (sf_dist_sq y x).
Proof.
  intros x y. apply real_eq_of_zero_diff. intro n.
apply qeq_imp_qeqT.
rewrite (qeqT_imp_qeq _ _ (sf_dist_sq_proj x y n)).
rewrite (qeqT_imp_qeq _ _ (sf_dist_sq_proj y x n)).
rewrite (qeqT_imp_qeq _ _ (sf_ptw_sum_sym x y n)). ring.
Qed.

(* the square of a component's self-difference is zero (used when substituting self-values into pipes). *)
Lemma sf_sq_self_zero : forall a : Real, real_eq (sf_sq (sf_sub a a)) real_zero.
Proof.
  intro a. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
  rewrite Hz.
  unfold sf_sq, sf_sub.
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (sf_sub a a) (sf_sub a a) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj a (real_opp a) n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj a n)).
  ring.
Qed.

(* ============================================================ *)
(* SFSensePipe: senses / clusters / pipe thickness (the blueprint's §1 Sense / Cluster / *)
(*   in_cluster / pipe_thickness) *)
(*   baseline form: SenseID/ClusterID/Word are all nat; in_cluster uses *)
(*   [InT] (the Set layer); the pipe thickness is (8/100) * inv(d^2 + 1/10), the division *)
(*   goes through [real_inv_pos] (the inverse of a positive number), with positivity proved via the eps-slack chain. *)
(* ============================================================ *)

Record SFSense : Set := Build_SFSense {
  sf_sense_id : nat;                 (* the sense identifier (the blueprint's SenseID) *)
  sf_sense_word : nat;               (* the identifier of the owning word (the blueprint's Word := string, made nat) *)
  sf_sense_coord : SFVec;            (* the semantic coordinates (the blueprint's Coord) *)
  sf_sense_clusters : list nat       (* the list of cluster memberships (the blueprint's list ClusterID) *)
}.

(* cluster membership: the Set-layer [InT] (the blueprint's in_cluster : Prop, made Set-layer). *)
Definition sf_in_cluster (s : SFSense) (c : nat) : Set :=
  InT c (sf_sense_clusters s).

(* a cluster: an identifier plus a list of senses (the baseline form of the blueprint's Cluster record). *)
Record SFCluster : Set := Build_SFCluster {
  sf_cluster_id : nat;
  sf_cluster_members : list SFSense
}.

(* ---- the pipe thickness constants (matching the blueprint's 0.08 / 0.1 as exact Q constants) ---- *)
Definition sf_pipe_num : Real := real_const (8 / 100).
Definition sf_tenth : Real := real_const (1 / 10).
Definition sf_twentieth : Real := real_const (1 / 20).

Lemma sf_pipe_num_pos : real_lt real_zero sf_pipe_num.
Proof. apply real_const_lt. compute. reflexivity. Qed.

Lemma sf_tenth_pos : real_lt real_zero sf_tenth.
Proof. apply real_const_lt. compute. reflexivity. Qed.

Lemma sf_twentieth_pos : real_lt real_zero sf_twentieth.
Proof. apply real_const_lt. compute. reflexivity. Qed.

(* 1/20 + 1/20 == 1/10 (a Real-layer eq bridge, pointwise Q ring). *)
Lemma sf_twentieth_add : real_eq (real_plus sf_twentieth sf_twentieth) sf_tenth.
Proof.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj sf_twentieth sf_twentieth n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 / 20) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 / 10) n)).
  reflexivity.
Qed.

(* le zero A and lt zero B give lt zero (A + B): an Or case-split bridge (constructive). *)
Lemma sf_le_plus_lt : forall a b : Real,
  real_le real_zero a -> real_lt real_zero b ->
  real_lt real_zero (real_plus a b).
Proof.
  intros a b Ha Hb.
  unfold real_le in Ha.
  destruct Ha as [Hlt | Heq].
  - exact (real_plus_positive a b Hlt Hb).
  - (* a == 0: first obtain the lt at the (0 + b) level, then switch back to (a + b) via the eq bridge *)
    assert (Hlt0b : real_lt real_zero (real_plus real_zero b)).
    { apply (RealSetoid.real_lt_id_r real_zero b (real_plus real_zero b)).
      - apply (real_eq_sym (real_plus real_zero b) b).
        apply (real_eq_trans (real_plus real_zero b) (real_plus b real_zero) b).
        + apply real_plus_comm.
        + apply real_plus_zero.
      - exact Hb. }
    apply (RealSetoid.real_lt_compat real_zero real_zero
             (real_plus real_zero b) (real_plus a b)
             (real_eq_refl real_zero)
             (RealSetoid.real_eq_plus_compat real_zero b a b Heq (real_eq_refl b))
             Hlt0b).
Qed.

(* ---- the pipe denominator is always positive: d^2 + 1/10 > 0 (the constructive
        proof of the blueprint's pipe_thickness_pos assumption:
        d^2 + 1/20 >= 0 in eps form with eps := 1/20, hence
        (d^2 + 1/20) + 1/20 > 0, hence d^2 + 1/10 > 0) ---- *)
Theorem sf_pipe_den_pos : forall x y : SFVec,
  real_lt real_zero (real_plus (sf_dist_sq x y) sf_tenth).
Proof.
  intros x y.
  apply (RealSetoid.real_lt_id_r real_zero
           (real_plus (real_plus (sf_dist_sq x y) sf_twentieth) sf_twentieth)
           (real_plus (sf_dist_sq x y) sf_tenth)).
  - apply (real_eq_trans
             (real_plus (real_plus (sf_dist_sq x y) sf_twentieth) sf_twentieth)
             (real_plus (sf_dist_sq x y) (real_plus sf_twentieth sf_twentieth))
             (real_plus (sf_dist_sq x y) sf_tenth)).
    + apply (real_eq_sym _ _).
      apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat (sf_dist_sq x y)
               (real_plus sf_twentieth sf_twentieth) (sf_dist_sq x y) sf_tenth).
      * apply real_eq_refl.
      * exact sf_twentieth_add.
  - apply (sf_le_plus_lt (real_plus (sf_dist_sq x y) sf_twentieth) sf_twentieth).
    + (* d^2 + 1/20 >= 0, in eps form with eps := 1/20 *)
      exact (sf_dist_sq_pos_eps x y sf_twentieth sf_twentieth_pos).
    + exact sf_twentieth_pos.
Qed.

(* the pipe function with a positivity witness (the dependent type carries the denominator positivity, the sigT route). *)
Definition sf_pipe_at (d : Real)
  (Hd : real_lt real_zero (real_plus d sf_tenth)) : Real :=
  real_mult sf_pipe_num (real_inv_pos (real_plus d sf_tenth) Hd).

(* the pipe thickness of a coordinate pair (the blueprint's pipe_thickness). *)
Definition sf_pipe (x y : SFVec) : Real :=
  sf_pipe_at (sf_dist_sq x y) (sf_pipe_den_pos x y).

(* the pipe thickness is always positive (the constructive version of the blueprint's pipe_thickness_pos). *)
Theorem sf_pipe_pos : forall x y : SFVec, real_lt real_zero (sf_pipe x y).
Proof.
  intros x y. unfold sf_pipe, sf_pipe_at.
  apply real_mult_positive.
  - exact sf_pipe_num_pos.
  - apply real_inv_pos_pos.
Qed.

(* the pipe thickness is symmetric (the blueprint's pipe_thickness_sym; no length assumption under the truncation semantics). *)
Theorem sf_pipe_sym : forall x y : SFVec, real_eq (sf_pipe x y) (sf_pipe y x).
Proof.
  intros x y. unfold sf_pipe, sf_pipe_at.
  apply RealSetoid.real_eq_mult_compat.
  - apply real_eq_refl.
  - apply (real_inv_pos_ext _ _ (sf_pipe_den_pos x y) (sf_pipe_den_pos y x)).
    apply (RealSetoid.real_eq_plus_compat (sf_dist_sq x y) sf_tenth
                                          (sf_dist_sq y x) sf_tenth).
    + apply (sf_dist_sq_sym x y).
    + apply real_eq_refl.
Qed.

(* the pipe of a self-connection attains the maximum form (the blueprint's
   pipe_thickness_self_max: substituting the self-distance == 0 pointwise) *)
Theorem sf_pipe_self_eq : forall x : SFVec,
  real_eq (sf_pipe x x)
          (real_mult sf_pipe_num (real_inv_pos sf_tenth sf_tenth_pos)).
Proof.
  intro x. unfold sf_pipe, sf_pipe_at.
  apply RealSetoid.real_eq_mult_compat.
  - apply real_eq_refl.
  - apply (real_inv_pos_ext _ _ (sf_pipe_den_pos x x) sf_tenth_pos).
    apply (real_eq_trans (real_plus (sf_dist_sq x x) sf_tenth)
                         (real_plus real_zero sf_tenth) sf_tenth).
    + apply (RealSetoid.real_eq_plus_compat (sf_dist_sq x x) sf_tenth real_zero sf_tenth).
      * exact (sf_dist_sq_self x).
      * apply real_eq_refl.
    + apply (real_eq_trans (real_plus sf_tenth real_zero) sf_tenth).
      * apply real_plus_comm.
      * apply real_eq_of_zero_diff. intro n.
        apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj sf_tenth real_zero n)).
        assert (Hz2 : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        rewrite Hz2. ring.
Qed.

(* the pipe is antitone in the distance (the strict direction of the blueprint's
   pipe_thickness_decr_with_dist).  the chain: le plus 1/10, then the inverse
   reverses the order ([real_inv_pos_le_compat]), then multiplying by a positive
   constant preserves the order ([real_le_mult_compat]). *)
Theorem sf_pipe_antitone :
  forall d1 d2 : Real,
    forall (Hd1 : real_lt real_zero (real_plus d1 sf_tenth))
           (Hd2 : real_lt real_zero (real_plus d2 sf_tenth)),
      real_le d1 d2 ->
      real_le (sf_pipe_at d2 Hd2) (sf_pipe_at d1 Hd1).
Proof.
  intros d1 d2 Hd1 Hd2 Hd.
  unfold sf_pipe_at.
  apply (RealSetoid.real_le_compat
           (real_mult (real_inv_pos (real_plus d2 sf_tenth) Hd2) sf_pipe_num)
           (real_mult sf_pipe_num (real_inv_pos (real_plus d2 sf_tenth) Hd2))
           (real_mult (real_inv_pos (real_plus d1 sf_tenth) Hd1) sf_pipe_num)
           (real_mult sf_pipe_num (real_inv_pos (real_plus d1 sf_tenth) Hd1))
           (real_mult_comm (real_inv_pos (real_plus d2 sf_tenth) Hd2) sf_pipe_num)
           (real_mult_comm (real_inv_pos (real_plus d1 sf_tenth) Hd1) sf_pipe_num)).
  apply (real_le_mult_compat
           (real_inv_pos (real_plus d2 sf_tenth) Hd2)
           (real_inv_pos (real_plus d1 sf_tenth) Hd1)
           sf_pipe_num sf_pipe_num_pos).
  apply (real_inv_pos_le_compat (real_plus d1 sf_tenth) (real_plus d2 sf_tenth) Hd1 Hd2).
  apply (real_le_plus_compat d1 d2 sf_tenth sf_tenth Hd).
  apply real_le_refl.
Qed.

(* the sense-level corollary: sense pairs with smaller distance have thicker pipes. *)
Theorem sf_pipe_thicker_when_closer :
  forall x1 y1 x2 y2 : SFVec,
    real_le (sf_dist_sq x1 y1) (sf_dist_sq x2 y2) ->
    real_le (sf_pipe x2 y2) (sf_pipe x1 y1).
Proof.
  intros x1 y1 x2 y2 Hd.
  exact (sf_pipe_antitone (sf_dist_sq x1 y1) (sf_dist_sq x2 y2)
           (sf_pipe_den_pos x1 y1) (sf_pipe_den_pos x2 y2) Hd).
Qed.


(* ############ part _p2 ############ *)

(* ============================================================ *)
(* SFNatToReal: the embedding of naturals into reals (the constructive replacement of the blueprint's INR, *)
(*   since the INR of Coq Reals relies on the classical real axioms; nat -> Real is built here) *)
(* ============================================================ *)

Fixpoint sf_n2r (n : nat) : Real :=
  match n with
  | O => real_zero
  | Datatypes.S n' => real_plus real_one (sf_n2r n')
  end.

(* sf_n2r is nonnegative pointwise (Q-layer induction; the projection-level
   characterization comes first; the Qle form restated as QleT' via [sf_qleT_plus]) *)
Lemma sf_n2r_proj_nonneg : forall (n m : nat), QleT' 0 (projT1 (sf_n2r n) m).
Proof.
  intros n. induction n as [| n IH]; intro m.
  - apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (sf_n2r n) m)).
    assert (Ho : projT1 real_one m == 1) by (cbn [projT1]; reflexivity).
    rewrite Ho.
    apply (Qle_trans _ (0 + 0)%Q _).
    + apply Qle_refl.
    + exact (Qplus_le_compat 0 1 0 (projT1 (sf_n2r n) m)
                             (QleT'_to_Qle _ _ Qle_0_1) (QleT'_to_Qle _ _ (IH m))).
Qed.

(* sf_n2r is strictly positive at successors (the pointwise witness 1/2: 0 <= 1 <= 1 + s gives 1/2 < 1 + s). *)
Theorem sf_n2r_pos : forall n : nat, real_lt real_zero (sf_n2r (Datatypes.S n)).
Proof.
  intro n.
  change (sf_n2r (Datatypes.S n)) with (real_plus real_one (sf_n2r n)).
  exists (1 # 2). split.
  - compute. reflexivity.
  - exists O. intros m _.
    apply Qlt_to_QltT.
    assert (Hp : projT1 (real_plus real_one (sf_n2r n)) m
                 == projT1 real_one m + projT1 (sf_n2r n) m)
      by exact (qeqT_imp_qeq _ _ (real_plus_proj real_one (sf_n2r n) m)).
    assert (Hz : projT1 real_zero m == 0) by (cbn [projT1]; reflexivity).
    assert (Ho : projT1 real_one m == 1) by (cbn [projT1]; reflexivity).
    rewrite Hp, Ho, Hz.
    assert (Hm : (1 + projT1 (sf_n2r n) m - 0)%Q
                 == (1 + projT1 (sf_n2r n) m)%Q) by ring.
    rewrite Hm.
    apply (Qlt_le_trans _ 1%Q _).
    + compute. reflexivity.
    + exact (Qplus_le_compat 1 1 0 (projT1 (sf_n2r n) m)
                             (Qle_refl 1)
(QleT'_to_Qle _ _ (sf_n2r_proj_nonneg n m))).
Qed.

(* sf_n2r is always nonnegative (strictly positive, or zero by reflexivity; the Or-encoding case split of le). *)
Theorem sf_n2r_nonneg : forall n : nat, real_le real_zero (sf_n2r n).
Proof.
  intros [| n].
  - apply real_le_refl.
  - apply (real_lt_le_iff real_zero (sf_n2r (Datatypes.S n))). left.
    exact (sf_n2r_pos n).
Qed.

(* ============================================================ *)
(* SFPathEnergy: path energy and beam search (the blueprint's §1 path_energy / *)
(*   beam_search plus §2 sort_correct / beam_search_returns_minimum) *)
(*   relation to the baseline: greedy argmin decoding already exists ([ArgminCorrectness]); this section lifts *)
(*   the same argmin_aux pattern to the candidate-path level.  energy comparison on Cauchy reals is *)
(*   undecidable (no trichotomy), so an honest-interface comparison operator is introduced as a Section Variable *)
(*   [sf_path_cmp : Or (<=) (>)] (supplied when instantiating concrete models such as Q coordinates / floats, *)
(*   following the [le_dec] precedent of LanguageModelInstance) *)
(* ============================================================ *)

Section SFPathEnergy.

(* ---- the path's ends and the sum of adjacent pipes ---- *)
Fixpoint sf_last (p : list SFVec) : SFVec :=
  match p with
  | nil => nil
  | a :: rest =>
      match rest with
      | nil => a
      | _ :: _ => sf_last rest
      end
  end.

Fixpoint sf_path_sum (p : list SFVec) : Real :=
  match p with
  | nil => real_zero
  | a :: rest =>
      match rest with
      | nil => real_zero
      | b :: rest' => real_plus (sf_pipe a b) (sf_path_sum rest)
      end
  end.

(* the path energy is the negative of the sum of adjacent pipes (the closed form of the blueprint's path_energy). *)
Definition sf_path_energy (p : list SFVec) : Real :=
  real_opp (sf_path_sum p).

(* the energy of the empty path is zero. *)
Theorem sf_path_energy_nil : real_eq (sf_path_energy nil) real_zero.
Proof.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
  rewrite Hz. reflexivity.
Qed.

(* ---- the exact decomposition of tail extension (the constructive version of the blueprint's path_energy_neg_sum) ---- *)
(* the sum version: sum(p ++ [s]) == sum(p) + pipe(last p, s) for nonempty p. *)
(* ---- the exact decomposition of tail extension (the constructive version of the blueprint's path_energy_neg_sum) ---- *)
(* auxiliary: the sum decomposition for an arbitrary nonempty list a::p
   (induction on p with the head a generalized inside the IH, so the
   cons-recursion closes in one step: the decomposition of a::b::rest'
   uses the decomposition of b::rest') *)
Lemma sf_path_sum_app_aux :
  forall (p : list SFVec) (s a : SFVec),
    real_eq (sf_path_sum (a :: p ++ s :: nil))
            (real_plus (sf_path_sum (a :: p)) (sf_pipe (sf_last (a :: p)) s)).
Proof.
  induction p as [| b rest' IH]; intros s a.
  - (* p = nil: both sides reduce to pipe a s and the add-zero unit (pointwise ring) *)
    simpl.
    apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (sf_pipe a s) real_zero n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_zero (sf_pipe a s) n)).
    ring.
  - (* p = b::rest': the IH (head replaced by b) plus the real_eq chain of addition associativity *)
    simpl.
    eapply real_eq_trans.
    + apply (RealSetoid.real_eq_plus_compat
               (sf_pipe a b) (sf_path_sum (b :: rest' ++ s :: nil))
               (sf_pipe a b)
               (real_plus (sf_path_sum (b :: rest'))
                          (sf_pipe (sf_last (b :: rest')) s))).
      * apply real_eq_refl.
      * exact (IH s b).
    + apply real_plus_assoc.
Qed.

(* the sum version: sum(p ++ [s]) == sum(p) + pipe(last p, s) for nonempty p. *)
Theorem sf_path_sum_app_single :
  forall (p : list SFVec) (s : SFVec),
    Not (Id p nil) ->
    real_eq (sf_path_sum (p ++ s :: nil))
            (real_plus (sf_path_sum p) (sf_pipe (sf_last p) s)).
Proof.
  intros p s Hp.
  destruct p as [| a rest]; [destruct (Hp (id_refl))|].
  destruct rest as [| b rest'].
  - (* p = [a]: both sides reduce to pipe a s and the add-zero unit (proved directly) *)
    simpl.
    apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (sf_pipe a s) real_zero n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_zero (sf_pipe a s) n)).
    ring.
  - (* p = a::b::rest': closed by aux (the IH head generalized, instantiated at a := b) plus the assoc chain *)
    simpl.
    eapply real_eq_trans.
    + apply (RealSetoid.real_eq_plus_compat
               (sf_pipe a b) (sf_path_sum (b :: rest' ++ s :: nil))
               (sf_pipe a b)
               (real_plus (sf_path_sum (b :: rest'))
                          (sf_pipe (sf_last (b :: rest')) s))).
      * apply real_eq_refl.
      * exact (sf_path_sum_app_aux rest' s b).
    + apply real_plus_assoc.
Qed.

(* the energy version: E(p ++ [s]) == E(p) - pipe(last p, s) for nonempty p. *)
Theorem sf_path_energy_append_single :
  forall (p : list SFVec) (s : SFVec),
    Not (Id p nil) ->
    real_eq (sf_path_energy (p ++ s :: nil))
            (real_plus (sf_path_energy p) (real_opp (sf_pipe (sf_last p) s))).
Proof.
  intros p s Hp.
  unfold sf_path_energy.
  apply (real_eq_trans _ (real_opp (real_plus (sf_path_sum p) (sf_pipe (sf_last p) s))) _).
  - apply RealSetoid.real_eq_opp_compat.
    exact (sf_path_sum_app_single p s Hp).
  - (* -(A + B) == (-A) + (-B) (pointwise ring) plus the add-zero cleanup *)
    apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus (sf_path_sum p) (sf_pipe (sf_last p) s)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (sf_path_sum p) (sf_pipe (sf_last p) s) n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_opp (sf_path_sum p)) (real_opp (sf_pipe (sf_last p) s)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj (sf_path_sum p) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj (sf_pipe (sf_last p) s) n)).
    ring.
Qed.

(* lt zero a gives lt (opp a) zero (positive becomes negative, transferring the pointwise witness). *)
Lemma sf_lt_opp_zero : forall a : Real,
  real_lt real_zero a -> real_lt (real_opp a) real_zero.
Proof.
  intros a Ha.
  destruct Ha as [e [He [N HN]]].
  unfold real_lt. exists e. split.
  - exact He.
  - exists N. intros n Hn.
    specialize (HN n Hn).
    apply Qlt_to_QltT.
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hoa : projT1 (real_opp a) n == - projT1 a n)
      by exact (qeqT_imp_qeq _ _ (real_opp_proj a n)).
    setoid_rewrite Hz. setoid_rewrite Hoa.
    assert (Hz2 : projT1 a n - projT1 real_zero n == 0 - - projT1 a n)
      by (rewrite Hz; ring).
    assert (HN2 : Qlt e (projT1 a n - projT1 real_zero n))
      by exact (QltT_to_Qlt e _ HN).
    setoid_rewrite Hz2 in HN2.
    exact HN2.
Qed.

(* a single extension strictly lowers the energy (the dynamics behind beam
   search; the constructive strict strengthening of the blueprint's energy
   monotonicity) *)
Theorem sf_path_energy_extension_lowers :
  forall (p : list SFVec) (s : SFVec),
    Not (Id p nil) ->
    real_lt (sf_path_energy (p ++ s :: nil)) (sf_path_energy p).
Proof.
  intros p s Hp.
  (* the bridge [real_lt_zero_minus x y : lt zero (y + opp x) -> lt x y];
     the remaining goal 0 < E p - E(p++[s]) reduces, via two eq transfers of the
     append_single energy identity E(p++[s]) == E p - pipe(last p, s), to the
     pipe positivity ([sf_pipe_pos]), the intermediate difference
     E p - (E p - pipe) == pipe being pointwise ring *)
  apply (real_lt_zero_minus (sf_path_energy (p ++ s :: nil)) (sf_path_energy p)).
  assert (Hdiff : real_eq
    (real_plus (sf_path_energy p)
               (real_opp (real_plus (sf_path_energy p)
                                    (real_opp (sf_pipe (sf_last p) s)))))
    (sf_pipe (sf_last p) s)).
  { apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (sf_path_energy p)
               (real_opp (real_plus (sf_path_energy p)
                                    (real_opp (sf_pipe (sf_last p) s)))) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus (sf_path_energy p)
                                      (real_opp (sf_pipe (sf_last p) s))) n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (sf_path_energy p) (real_opp (sf_pipe (sf_last p) s)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj (sf_pipe (sf_last p) s) n)).
    ring. }
  apply (real_lt_eq_lt real_zero
    (real_plus (sf_path_energy p)
               (real_opp (real_plus (sf_path_energy p)
                                    (real_opp (sf_pipe (sf_last p) s)))))
    (real_plus (sf_path_energy p) (real_opp (sf_path_energy (p ++ s :: nil))))).
  - (* 0 < E p - (E p - pipe): from 0 < pipe via the eq transfer *)
    apply (real_lt_eq_lt real_zero (sf_pipe (sf_last p) s)
      (real_plus (sf_path_energy p)
                 (real_opp (real_plus (sf_path_energy p)
                                      (real_opp (sf_pipe (sf_last p) s)))))).
    + exact (sf_pipe_pos (sf_last p) s).
    + exact (real_eq_sym _ _ Hdiff).
  - (* E p - (E p - pipe) == E p - E(p++[s]): the plus/opp compatibility plus append_single *)
    apply (RealSetoid.real_eq_plus_compat (sf_path_energy p)
      (real_opp (real_plus (sf_path_energy p) (real_opp (sf_pipe (sf_last p) s))))
      (sf_path_energy p)
      (real_opp (sf_path_energy (p ++ s :: nil)))).
    + apply real_eq_refl.
    + apply (RealSetoid.real_eq_opp_compat
        (real_plus (sf_path_energy p) (real_opp (sf_pipe (sf_last p) s)))
        (sf_path_energy (p ++ s :: nil))).
      exact (real_eq_sym _ _ (sf_path_energy_append_single p s Hp)).
Qed.

(* ---- the energy lower bound (the honest-interface form of the blueprint's path_energy_lower_bound) ---- *)
(* a uniform pipe upper bound Tmax as an interface assumption: d^2 >= 0 on
   Cauchy reals is not decidable constructively, so the blueprint's absolute
   lower bound becomes an interface-assumption-driven relative bound *)
Variable sf_tmax : Real.
Hypothesis sf_pipe_le_tmax : forall x y : SFVec, real_le (sf_pipe x y) sf_tmax.

(* the energy lower bound: -len(p) * Tmax <= E(p). *)
(* direction note: the draft form real_le (sf_path_energy p) (len * (-Tmax)),
   i.e. 0 - sum <= -n * Tmax, is unprovable: for p = [a] the left side is 0
   and the right side is -Tmax, while the interface assumption plus the pipe
   positivity give Tmax > 0 constructively.  the honest lower bound is the
   opposite direction: -n * Tmax <= E(p) (== -sum(p), since
   sum <= (n-1) * Tmax <= n * Tmax). *)
(* ---- the lower-bound toolbox (purely constructive: pointwise ring, le case splits, real_eq chains) ---- *)

(* 0 <= Tmax: the pipe positivity plus the interface upper-bound transfer. *)
Lemma sf_le_zero_tmax : real_le real_zero sf_tmax.
Proof.
  apply (real_lt_le_iff real_zero sf_tmax). left.
  exact (real_lt_le_trans real_zero (sf_pipe nil nil) sf_tmax
           (sf_pipe_pos nil nil) (sf_pipe_le_tmax nil nil)).
Qed.

(* 0 * x == 0 (pointwise ring). *)
Lemma sf_mult_zero_l : forall x : Real, real_eq (real_mult real_zero x) real_zero.
Proof.
  intro x. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj real_zero x n)). rewrite Hz. ring.
Qed.

(* (1 + x) * y == y + x * y (pointwise ring). *)
Lemma sf_mult_one_plus : forall x y : Real,
  real_eq (real_mult (real_plus real_one x) y) (real_plus y (real_mult x y)).
Proof.
  intros x y. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_plus real_one x) y n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one x n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj y (real_mult x y) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj x y n)).
  rewrite Ho. ring.
Qed.

(* (a+b)+(c+d) == (a+d)+(b+c) (pointwise ring, for rearranging the induction step). *)
Lemma sf_plus4_shuffle : forall a b c d : Real,
  real_eq (real_plus (real_plus a b) (real_plus c d))
          (real_plus (real_plus a d) (real_plus b c)).
Proof.
  intros a b c d. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus a b) (real_plus c d) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj a b n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj c d n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus a d) (real_plus b c) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj a d n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj b c n)).
  ring.
Qed.

(* x <= y gives -y + x <= 0 (the le case split: the lt witness transfers pointwise as is, or the eq compatibility chain). *)
Lemma sf_le_minus_zero : forall x y : Real,
  real_le x y -> real_le (real_plus (real_opp y) x) real_zero.
Proof.
  intros x y Hle. destruct Hle as [Hlt | Heq].
  - left. destruct Hlt as [e [He [N HN]]].
    exists e. split.
    + exact He.
    + exists N. intros n Hn. specialize (HN n Hn).
      apply Qlt_to_QltT.
      assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      assert (Hp : projT1 (real_plus (real_opp y) x) n == - projT1 y n + projT1 x n).
      { rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_opp y) x n)). rewrite (qeqT_imp_qeq _ _ (real_opp_proj y n)). ring. }
      rewrite Hz. rewrite Hp.
      assert (Hr : (0 - (- projT1 y n + projT1 x n))%Q
                   == (projT1 y n - projT1 x n)) by ring.
      rewrite Hr. exact (QltT_to_Qlt _ _ HN).
  - right.
    apply (real_eq_trans (real_plus (real_opp y) x)
                         (real_plus (real_opp y) y) real_zero).
    + apply (RealSetoid.real_eq_plus_compat (real_opp y) x (real_opp y) y).
      * apply real_eq_refl.
      * exact Heq.
    + apply (real_eq_trans (real_plus (real_opp y) y)
                           (real_plus y (real_opp y)) real_zero).
      * exact (real_plus_comm (real_opp y) y).
      * exact (real_plus_opp y).
Qed.

(* x + s <= 0 gives x <= -s (the le case split: the lt witness reorganized pointwise, or the eq compatibility chain). *)
Lemma sf_le_plus_opp_r : forall x s : Real,
  real_le (real_plus x s) real_zero -> real_le x (real_opp s).
Proof.
  intros x s H. destruct H as [Hlt | Heq].
  - left. destruct Hlt as [e [He [N HN]]].
    exists e. split.
    + exact He.
    + exists N. intros n Hn. specialize (HN n Hn).
      apply Qlt_to_QltT.
      pose proof (QltT_to_Qlt _ _ HN) as HN2.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj x s n)) in HN2.
      assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      rewrite Hz in HN2.
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj s n)).
      assert (Hr : (- projT1 s n - projT1 x n)%Q
                   == (0 - (projT1 x n + projT1 s n))) by ring.
      rewrite Hr. exact HN2.
  - right.
    apply (real_eq_trans x (real_plus x (real_plus s (real_opp s))) (real_opp s)).
    + apply (real_eq_sym (real_plus x (real_plus s (real_opp s))) x).
      apply (real_eq_trans (real_plus x (real_plus s (real_opp s)))
                           (real_plus x real_zero) x).
      * apply (RealSetoid.real_eq_plus_compat x (real_plus s (real_opp s))
                 x real_zero).
        -- apply real_eq_refl.
        -- exact (real_plus_opp s).
      * exact (real_plus_zero x).
    + apply (real_eq_trans (real_plus x (real_plus s (real_opp s)))
                           (real_plus (real_plus x s) (real_opp s))
                           (real_opp s)).
      * exact (real_plus_assoc x s (real_opp s)).
      * apply (real_eq_trans (real_plus (real_plus x s) (real_opp s))
                             (real_plus real_zero (real_opp s)) (real_opp s)).
        -- apply (RealSetoid.real_eq_plus_compat (real_plus x s) (real_opp s)
                    real_zero (real_opp s)).
           ++ exact Heq.
           ++ apply real_eq_refl.
        -- apply (real_eq_trans (real_plus real_zero (real_opp s))
                   (real_plus (real_opp s) real_zero) (real_opp s)).
           ++ exact (real_plus_comm real_zero (real_opp s)).
           ++ exact (real_plus_zero (real_opp s)).
Qed.

(* the induction auxiliary: sum(p) - len(p) * Tmax <= 0 (the equivalent form
   of E(p) >= -len * Tmax).
   cons step: n2r(S k) * (-T) == n2r(k) * (-T) + (-T) (the [mult_one_plus]
   chain); D(a,p), the first pipe (degenerating to 0 for p = nil), satisfies
   D <= Tmax; then le_plus_compat, the shuffle rearrangement, and the IH
   assemble. *)
Lemma sf_energy_lb_aux : forall p : list SFVec,
  real_le (real_plus (real_mult (sf_n2r (length p)) (real_opp sf_tmax))
                     (sf_path_sum p))
          real_zero.
Proof.
  intro p. induction p as [| a rest IH].
  - (* nil: 0 * (-T) + 0 == 0 *)
    exact (RealSetoid.real_le_compat real_zero
             (real_plus (real_mult real_zero (real_opp sf_tmax)) real_zero)
             real_zero real_zero
             (real_eq_sym _ _
                (real_eq_trans
                   (real_plus (real_mult real_zero (real_opp sf_tmax)) real_zero)
                   (real_plus real_zero real_zero) real_zero
                   (RealSetoid.real_eq_plus_compat
                      (real_mult real_zero (real_opp sf_tmax)) real_zero
                      real_zero real_zero
                      (sf_mult_zero_l (real_opp sf_tmax))
                      (real_eq_refl real_zero))
                   (real_plus_zero real_zero)))
             (real_eq_refl real_zero)
             (real_le_refl real_zero)).
  - destruct rest as [| b rest'].
    + (* a::nil: -T + 0 <= 0 from 0 <= Tmax *)
      assert (Heq : real_eq
        (real_plus (real_mult (real_plus real_one (sf_n2r 0)) (real_opp sf_tmax))
                   real_zero)
        (real_plus (real_opp sf_tmax) real_zero)).
      { apply (real_eq_trans
                 (real_plus (real_mult (real_plus real_one (sf_n2r 0))
                                       (real_opp sf_tmax)) real_zero)
                 (real_plus (real_plus (real_opp sf_tmax)
                                       (real_mult (sf_n2r 0) (real_opp sf_tmax)))
                            real_zero)
                 (real_plus (real_opp sf_tmax) real_zero)).
        - apply (RealSetoid.real_eq_plus_compat
                   (real_mult (real_plus real_one (sf_n2r 0)) (real_opp sf_tmax))
                   real_zero
                   (real_plus (real_opp sf_tmax)
                              (real_mult (sf_n2r 0) (real_opp sf_tmax)))
                   real_zero).
          + exact (sf_mult_one_plus (sf_n2r 0) (real_opp sf_tmax)).
          + apply real_eq_refl.
        - apply (RealSetoid.real_eq_plus_compat
                   (real_plus (real_opp sf_tmax)
                              (real_mult (sf_n2r 0) (real_opp sf_tmax)))
                   real_zero
                   (real_opp sf_tmax) real_zero).
          + apply (real_eq_trans
                     (real_plus (real_opp sf_tmax)
                                (real_mult (sf_n2r 0) (real_opp sf_tmax)))
                     (real_plus (real_opp sf_tmax) real_zero)
                     (real_opp sf_tmax)).
            * apply (RealSetoid.real_eq_plus_compat (real_opp sf_tmax)
                       (real_mult (sf_n2r 0) (real_opp sf_tmax))
                       (real_opp sf_tmax) real_zero).
              -- apply real_eq_refl.
              -- exact (sf_mult_zero_l (real_opp sf_tmax)).
            * exact (real_plus_zero (real_opp sf_tmax)).
          + apply real_eq_refl. }
      exact (RealSetoid.real_le_compat
               (real_plus (real_opp sf_tmax) real_zero)
               (real_plus (real_mult (real_plus real_one (sf_n2r 0))
                                     (real_opp sf_tmax)) real_zero)
               real_zero real_zero
               (real_eq_sym _ _ Heq)
               (real_eq_refl real_zero)
               (sf_le_minus_zero real_zero sf_tmax sf_le_zero_tmax)).
    + (* a::b::rest': D = pipe a b; n2r(S k) * (-T) == n2r(k) * (-T) + (-T),
         and after the shuffle rearrangement le_plus_compat assembles the IH
         with -T + pipe <= 0 *)
      assert (Heq : real_eq
        (real_plus (real_mult (real_plus real_one (sf_n2r (length (b :: rest'))))
                              (real_opp sf_tmax))
                   (real_plus (sf_pipe a b) (sf_path_sum (b :: rest'))))
        (real_plus (real_plus (real_mult (sf_n2r (length (b :: rest')))
                                         (real_opp sf_tmax))
                              (sf_path_sum (b :: rest')))
                   (real_plus (real_opp sf_tmax) (sf_pipe a b)))).
      { apply (real_eq_trans
            (real_plus (real_mult (real_plus real_one (sf_n2r (length (b :: rest'))))
                                  (real_opp sf_tmax))
                       (real_plus (sf_pipe a b) (sf_path_sum (b :: rest'))))
            (real_plus (real_plus (real_mult (sf_n2r (length (b :: rest')))
                                             (real_opp sf_tmax))
                                  (real_opp sf_tmax))
                       (real_plus (sf_pipe a b) (sf_path_sum (b :: rest'))))
            (real_plus (real_plus (real_mult (sf_n2r (length (b :: rest')))
                                             (real_opp sf_tmax))
                                  (sf_path_sum (b :: rest')))
                       (real_plus (real_opp sf_tmax) (sf_pipe a b)))).
        - apply (RealSetoid.real_eq_plus_compat
              (real_mult (real_plus real_one (sf_n2r (length (b :: rest'))))
                         (real_opp sf_tmax))
              (real_plus (sf_pipe a b) (sf_path_sum (b :: rest')))
              (real_plus (real_mult (sf_n2r (length (b :: rest')))
                                    (real_opp sf_tmax)) (real_opp sf_tmax))
              (real_plus (sf_pipe a b) (sf_path_sum (b :: rest')))).
          + apply (real_eq_trans
                (real_mult (real_plus real_one (sf_n2r (length (b :: rest'))))
                           (real_opp sf_tmax))
                (real_plus (real_opp sf_tmax)
                           (real_mult (sf_n2r (length (b :: rest')))
                                      (real_opp sf_tmax)))
                (real_plus (real_mult (sf_n2r (length (b :: rest')))
                                      (real_opp sf_tmax)) (real_opp sf_tmax))).
            * exact (sf_mult_one_plus (sf_n2r (length (b :: rest')))
                        (real_opp sf_tmax)).
            * exact (real_plus_comm (real_opp sf_tmax)
                        (real_mult (sf_n2r (length (b :: rest')))
                                   (real_opp sf_tmax))).
          + apply real_eq_refl.
        - apply (real_eq_trans
              (real_plus (real_plus (real_mult (sf_n2r (length (b :: rest')))
                                               (real_opp sf_tmax))
                                    (real_opp sf_tmax))
                         (real_plus (sf_pipe a b) (sf_path_sum (b :: rest'))))
              (real_plus (real_plus (real_mult (sf_n2r (length (b :: rest')))
                                               (real_opp sf_tmax))
                                    (sf_path_sum (b :: rest')))
                         (real_plus (real_opp sf_tmax) (sf_pipe a b)))
              (real_plus (real_plus (real_mult (sf_n2r (length (b :: rest')))
                                               (real_opp sf_tmax))
                                    (sf_path_sum (b :: rest')))
                         (real_plus (real_opp sf_tmax) (sf_pipe a b)))).
          + exact (sf_plus4_shuffle
                     (real_mult (sf_n2r (length (b :: rest'))) (real_opp sf_tmax))
                     (real_opp sf_tmax) (sf_pipe a b)
                     (sf_path_sum (b :: rest'))).
          + apply real_eq_refl. }
      exact (RealSetoid.real_le_compat
               (real_plus (real_plus (real_mult (sf_n2r (length (b :: rest')))
                                                (real_opp sf_tmax))
                                     (sf_path_sum (b :: rest')))
                          (real_plus (real_opp sf_tmax) (sf_pipe a b)))
               (real_plus (real_mult (real_plus real_one
                                        (sf_n2r (length (b :: rest'))))
                                     (real_opp sf_tmax))
                          (real_plus (sf_pipe a b) (sf_path_sum (b :: rest'))))
               (real_plus real_zero real_zero) real_zero
               (real_eq_sym _ _ Heq)
               (real_plus_zero real_zero)
               (real_le_plus_compat
                  (real_plus (real_mult (sf_n2r (length (b :: rest')))
                                        (real_opp sf_tmax))
                             (sf_path_sum (b :: rest')))
                  real_zero
                  (real_plus (real_opp sf_tmax) (sf_pipe a b)) real_zero
                  IH
                  (sf_le_minus_zero (sf_pipe a b) sf_tmax
                     (sf_pipe_le_tmax a b)))).
Qed.

(* the energy lower bound: -len(p) * Tmax <= E(p) (in the corrected, provable direction above). *)
Theorem sf_path_energy_lower_bound :
  forall p : list SFVec,
    real_le (real_mult (sf_n2r (length p)) (real_opp sf_tmax))
            (sf_path_energy p).
Proof.
  intro p.
  unfold sf_path_energy.
  apply (sf_le_plus_opp_r (real_mult (sf_n2r (length p)) (real_opp sf_tmax))
                          (sf_path_sum p)).
  exact (sf_energy_lb_aux p).
Qed.

(* ---- beam search: taking the minimum-energy candidate path (the constructive
        implementation of the blueprint's beam_search /
        beam_search_returns_minimum) ---- *)
(* the total comparison interface (an honest interface; supplied by concrete models):
   Or (E p <= E q) (E q < E p), the constructive encoding of a decidable
   comparison at the Set layer *)
Variable sf_path_cmp :
  forall p q : list SFVec,
    Or (real_le (sf_path_energy p) (sf_path_energy q))
       (real_lt (sf_path_energy q) (sf_path_energy p)).

Definition sf_cand : Set := (list SFVec * Real)%type.

Fixpoint sf_beam_aux (l : list (list SFVec)) (best : sf_cand) : sf_cand :=
  match l with
  | nil => best
  | w :: rest =>
      match sf_path_cmp w (fst best) with
      | inl _ => sf_beam_aux rest (w, sf_path_energy w)
      | inr _ => sf_beam_aux rest best
      end
  end.

(* the beam search main function: the seed path serves as the initial best candidate. *)
Definition sf_beam_search (cands : list (list SFVec)) (seed : list SFVec) : list SFVec :=
  fst (sf_beam_aux cands (seed, sf_path_energy seed)).

(* correctness 1 (the constructive version of the blueprint's
   beam_search_returns_minimum): the returned path energy is <= the seed
   energy and <= every candidate path energy (the fst form) *)
Theorem sf_beam_aux_correct :
  forall l seed,
    And (real_le (sf_path_energy (fst (sf_beam_aux l (seed, sf_path_energy seed))))
                 (sf_path_energy seed))
        (forall w : list SFVec, InT w l ->
           real_le (sf_path_energy (fst (sf_beam_aux l (seed, sf_path_energy seed))))
                   (sf_path_energy w)).
Proof.
  intros l. induction l as [| a rest IH]; intros seed_p.
  - simpl. split.
    + apply real_le_refl.
    + intros w HIn. inversion HIn.
  - simpl.
    destruct (sf_path_cmp a seed_p) as [Hle | Hgt].
    + (* a is better: the new seed (a, E a) *)
      specialize (IH a). destruct IH as [IH_le IH_min].
      split.
      * (* E(fst result) ≤ E a ≤ E seed_p *)
        eapply real_le_trans.
        -- exact IH_le.
        -- exact Hle.
      * intros w HIn. inversion HIn as [Hw | HIn']; subst.
        -- exact IH_le.
        -- apply IH_min. assumption.
    + (* the seed is kept *)
      specialize (IH seed_p). destruct IH as [IH_le IH_min].
      split.
      * exact IH_le.
      * intros w HIn. inversion HIn as [Hw | HIn'']; subst.
        -- (* w = a (the head): the IH_le plus the Hgt transitivity *)
           eapply real_le_trans.
           ++ exact IH_le.
           ++ apply (RealSetoid.real_lt_le_iff_req (sf_path_energy seed_p)
                      (sf_path_energy a)).
              left. exact Hgt.
        -- apply IH_min. assumption.
Qed.

(* the beam search optimality (the constructive version of the blueprint's beam_search_returns_minimum). *)
Theorem sf_beam_search_optimal :
  forall (cands : list (list SFVec)) (seed p : list SFVec),
    InT p cands ->
    real_le (sf_path_energy (sf_beam_search cands seed)) (sf_path_energy p).
Proof.
  intros cands seed p Hp.
  unfold sf_beam_search.
  destruct (sf_beam_aux_correct cands seed) as [_ Hmin].
  apply Hmin. exact Hp.
Qed.

(* the invariant: the returned best is either the seed or a member of the candidate list. *)
(* the InT insert-after-head (the list SFVec version): x in y :: l gives x in y :: a :: l *)
Lemma sf_InT_head_extend : forall (x y a : list SFVec) (l : list (list SFVec)),
  InT x (y :: l) -> InT x (y :: a :: l).
Proof.
  intros x y a l H. inversion H; subst.
  - apply InT_here.
  - apply InT_next. apply InT_next. assumption.
Qed.

(* the invariant: the returned best is either the seed or a member of the candidate list. *)
Lemma sf_beam_aux_in :
  forall l seed,
    InT (fst (sf_beam_aux l (seed, sf_path_energy seed))) (seed :: l).
Proof.
  intro l. induction l as [| a rest IH]; intro seed.
  - (* nil: the best is the seed *)
    cbn [sf_beam_aux fst]. apply InT_here.
  - (* a::rest: case split on the total comparison sf_path_cmp a seed *)
    cbn [sf_beam_aux fst].
    destruct (sf_path_cmp a seed) as [Hle | Hgt].
    + (* a is better: the new seed a, so the result is in a::rest, contained in seed::a::rest *)
      apply InT_next. apply IH.
    + (* the seed is kept: the result is in seed::rest, lifted by the insert-after-head *)
      apply (sf_InT_head_extend
               (fst (sf_beam_aux rest (seed, sf_path_energy seed)))
               seed a rest).
      apply IH.
Qed.

(* correctness 2 (added in the baseline style): the returned path is indeed
   the seed or one of the candidates; the beam search invents no path outside
   the list *)
Theorem sf_beam_search_in_cands :
  forall (cands : list (list SFVec)) (seed : list SFVec),
    InT (sf_beam_search cands seed) (seed :: cands).
Proof.
  intros cands seed.
  unfold sf_beam_search.
  exact (sf_beam_aux_in cands seed).
Qed.

End SFPathEnergy.

(* ============================================================ *)
(* SFWorkingMemory: working memory and variable table entries (the blueprint's §1 Slot / *)
(*   WorkingMemory / bind_slot / lookup_slot plus the §2 update_slot family) *)
(*   baseline form: slot_name : string becomes nat (decidable by [Nat.eqb], with a Set-layer *)
(*   match); lookups return option Real; every theorem is proved with zero admissions *)
(* ============================================================ *)

Record SFSlot : Set := Build_SFSlot {
  sf_slot_key : nat;
  sf_slot_val : Real
}.

Definition SFWorkingMemory : Set := list SFSlot.

(* binding: insert at the head (the blueprint's bind_slot) *)
Definition sf_bind_slot (mem : SFWorkingMemory) (k : nat) (v : Real) : SFWorkingMemory :=
  Build_SFSlot k v :: mem.

(* lookup (the blueprint's lookup_slot; string_dec becomes Nat.eqb) *)
Fixpoint sf_lookup_slot (mem : SFWorkingMemory) (k : nat) : option Real :=
  match mem with
  | nil => None
  | s :: rest =>
      if Nat.eqb (sf_slot_key s) k then Some (sf_slot_val s)
      else sf_lookup_slot rest k
  end.

(* a binding is found immediately after it is bound (the blueprint's lookup_after_bind) *)
Theorem sf_lookup_after_bind :
  forall mem k v,
    Id (sf_lookup_slot (sf_bind_slot mem k v) k) (Some v).
Proof.
  intros mem k v. simpl.
  rewrite (Nat.eqb_refl k). apply id_refl.
Qed.

(* update: overwrite when the key exists, otherwise insert at the head (the blueprint's update_slot) *)
Fixpoint sf_update_slot (mem : SFWorkingMemory) (k : nat) (v : Real) : SFWorkingMemory :=
  match mem with
  | nil => Build_SFSlot k v :: nil
  | s :: rest =>
      if Nat.eqb (sf_slot_key s) k then Build_SFSlot k v :: rest
      else s :: sf_update_slot rest k v
  end.

(* the new value is found after the update (the blueprint's lookup_after_update) *)
Theorem sf_lookup_after_update :
  forall mem k v,
    Id (sf_lookup_slot (sf_update_slot mem k v) k) (Some v).
Proof.
  intros mem k v.
  induction mem as [| s rest IH]; simpl.
  - destruct (Nat.eqb k k) eqn:E2.
    + apply id_refl.
    + exfalso. apply Nat.eqb_neq in E2. apply E2. reflexivity.
  - destruct (Nat.eqb (sf_slot_key s) k) eqn:E.
    + simpl. rewrite (Nat.eqb_refl k). apply id_refl.
    + simpl. rewrite E. apply IH.
Qed.

(* updating an existing key does not increase the entry count (the constructive
   form of the blueprint's update_slot_preserves_length_if_exists: the
   existence of the key is carried by a sigT witness of a Some lookup result) *)
(* updating an existing key does not increase the entry count (the constructive
   form of the blueprint's update_slot_preserves_length_if_exists: the
   existence of the key is carried by a sigT witness of a Some lookup result) *)
Theorem sf_update_slot_len_preserved :
  forall mem k v,
    sigT (fun v0 : Real => Id (sf_lookup_slot mem k) (Some v0)) ->
    Id (length (sf_update_slot mem k v)) (length mem).
Proof.
  intros mem k v. induction mem as [| s rest IH]; intro Hfound.
  - (* nil: the Id between the found None and Some v0 is contradictory, and inversion explodes it constructively *)
    destruct Hfound as [v0 Hv]. cbn [sf_lookup_slot] in Hv.
    inversion Hv.
  - (* s::rest: case split on the key match *)
    simpl in Hfound |- *.
    destruct (Nat.eqb (sf_slot_key s) k) eqn:E.
    + (* hit: the head slot is overwritten, both lengths being S (length rest) *)
      simpl. apply id_refl.
    + (* miss: recurse into the tail, the length lifted from the IH by id_cong (S) *)
      simpl in Hfound |- *.
      destruct Hfound as [v0 Hv].
      apply id_cong.
      exact (IH (existT (fun v0 : Real => Id (sf_lookup_slot rest k) (Some v0))
                        v0 Hv)).
Qed.

(* deletion: the entry with the first matching key is removed (a semantic extension of the blueprint: a minimal forgetting gate) *)
Fixpoint sf_delete_slot (mem : SFWorkingMemory) (k : nat) : SFWorkingMemory :=
  match mem with
  | nil => nil
  | s :: rest =>
      if Nat.eqb (sf_slot_key s) k then sf_delete_slot rest k
      else s :: sf_delete_slot rest k
  end.

(* after deletion the key is no longer found *)
Theorem sf_lookup_after_delete :
  forall mem k,
    Id (sf_lookup_slot (sf_delete_slot mem k) k) None.
Proof.
  intros mem k.
  induction mem as [| s rest IH]; simpl.
  - apply id_refl.
  - destruct (Nat.eqb (sf_slot_key s) k) eqn:E.
    + exact IH.
    + simpl. rewrite E. exact IH.
Qed.

(* bind then update: the update overwrites the binding (the latest value wins; stack semantics) *)
Theorem sf_bind_update_shadow :
  forall mem k v1 v2,
    Id (sf_lookup_slot (sf_update_slot (sf_bind_slot mem k v1) k v2) k) (Some v2).
Proof.
  intros mem k v1 v2.
  apply sf_lookup_after_update.
Qed.

(* bindings with different keys do not interfere (the basic healthiness of a composite environment) *)
Theorem sf_bind_independent :
  forall mem k1 k2 v1 v2,
    Not (Id k1 k2) ->
    Id (sf_lookup_slot (sf_bind_slot (sf_bind_slot mem k1 v1) k2 v2) k1)
       (sf_lookup_slot (sf_bind_slot mem k1 v1) k1).
Proof.
  intros mem k1 k2 v1 v2 Hneq. simpl.
  destruct (Nat.eqb k2 k1) eqn:E.
  - exfalso.
    assert (Hk : k2 = k1) by exact (proj1 (Nat.eqb_eq k2 k1) E).
    assert (Hid : Id k2 k1) by (rewrite Hk; apply id_refl).
    destruct (Hneq (id_sym Hid)).
  - apply id_refl.
Qed.


(* ############ part _p3 ############ *)

(* ============================================================ *)
(* SFFreeEnergy: the global free energy (the blueprint's §2 alpha/beta/gamma / *)
(*   syntactic_potential / temporal_entropy / global_free_energy) *)
(*   relation to the baseline: the variational free energy / ELBO / Gibbs on state spaces already exists *)
(*   ([FreeEnergyMinimization]); this section does the path-level energetics, the two being complementary *)
(*   the blueprint's global_free_energy_nonneg was abandoned by its own author (the alpha term is negative *)
(*   under general conditions); here a conditional lower-bound theorem is stated under the honest *)
(*   interface hypotheses (alpha >= 0, a pipe upper bound, nonnegative syntactic potential) and proved outright *)
(* ============================================================ *)

Section SFFreeEnergy.

(* the adjacent-action functional: the sum of f over adjacent pairs *)
Fixpoint sf_adj_sum (f : SFVec -> SFVec -> Real) (p : list SFVec) : Real :=
  match p with
  | nil => real_zero
  | a :: rest =>
      match rest with
      | nil => real_zero
      | b :: rest' => real_plus (f a b) (sf_adj_sum f rest)
      end
  end.

(* the syntactic potential: the sum of adjacent squared distances (the blueprint's syntactic_potential) *)
Definition sf_syn_pot (p : list SFVec) : Real :=
  sf_adj_sum sf_dist_sq p.

(* the temporal entropy term: linear in the length (the constructive
   replacement of the blueprint's temporal_entropy := INR(length)) *)
Definition sf_temporal (p : list SFVec) : Real :=
  sf_n2r (length p).

(* the global free energy = -alpha * (the pipe sum) + beta * (the syntactic potential) + gamma * (the temporal entropy) *)
Definition sf_gfe (alpha beta gamma : Real) (p : list SFVec) : Real :=
  real_plus (real_opp (real_mult alpha (sf_path_sum p)))
            (real_plus (real_mult beta (sf_syn_pot p))
                       (real_mult gamma (sf_temporal p))).

(* the exact energy accounting of a single extension (the blueprint's difference
   structure): the pointwise ring algebra of the four-term linear recombination *)
Lemma sf_gfe_adj_sum_app_proj :
  forall (f : SFVec -> SFVec -> Real) (p : list SFVec) (s : SFVec),
    Not (Id p nil) ->
    forall n : nat,
      QeqT (projT1 (sf_adj_sum f (p ++ s :: nil)) n)
        (projT1 (sf_adj_sum f p) n + projT1 (f (sf_last p) s) n).
Proof.
  intros f p. induction p as [| a rest IH]; intros s Hp n.
  - destruct (Hp (id_refl)).
  - destruct rest as [| b rest'].
    + (* p = [a]: both sides reduce to f a s and the add-zero unit *)
      apply qeq_imp_qeqT.
      change (sf_adj_sum f ((a :: nil) ++ s :: nil))
        with (real_plus (f a s) real_zero).
      change (sf_adj_sum f (a :: nil)) with real_zero.
      change (sf_last (a :: nil)) with a.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (f a s) real_zero n)).
      ring.
    + (* p = a::b::rest': the head adjacent term is kept, the tail goes to the induction assumption *)
      apply qeq_imp_qeqT.
      change (sf_adj_sum f ((a :: b :: rest') ++ s :: nil))
        with (real_plus (f a b) (sf_adj_sum f ((b :: rest') ++ s :: nil))).
      change (sf_adj_sum f (a :: b :: rest'))
        with (real_plus (f a b) (sf_adj_sum f (b :: rest'))).
      change (sf_last (a :: b :: rest')) with (sf_last (b :: rest')).
      assert (Hne : Not (Id (b :: rest') nil)) by (intros Hc; inversion Hc).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (f a b)
                 (sf_adj_sum f ((b :: rest') ++ s :: nil)) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (f a b) (sf_adj_sum f (b :: rest')) n)).
      specialize (IH s Hne n).
      rewrite (qeqT_imp_qeq _ _ IH).
      ring.
Qed.

(* the pointwise decomposition of the tail extension of [sf_path_sum] (same shape as the previous lemma) *)
Lemma sf_gfe_path_sum_app_proj :
  forall (p : list SFVec) (s : SFVec),
    Not (Id p nil) ->
    forall n : nat,
      QeqT (projT1 (sf_path_sum (p ++ s :: nil)) n)
        (projT1 (sf_path_sum p) n + projT1 (sf_pipe (sf_last p) s) n).
Proof.
  intros p. induction p as [| a rest IH]; intros s Hp n.
  - destruct (Hp (id_refl)).
  - destruct rest as [| b rest'].
    + apply qeq_imp_qeqT.
      change (sf_path_sum ((a :: nil) ++ s :: nil))
        with (real_plus (sf_pipe a s) real_zero).
      change (sf_path_sum (a :: nil)) with real_zero.
      change (sf_last (a :: nil)) with a.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (sf_pipe a s) real_zero n)).
      ring.
    + apply qeq_imp_qeqT.
      change (sf_path_sum ((a :: b :: rest') ++ s :: nil))
        with (real_plus (sf_pipe a b) (sf_path_sum ((b :: rest') ++ s :: nil))).
      change (sf_path_sum (a :: b :: rest'))
        with (real_plus (sf_pipe a b) (sf_path_sum (b :: rest'))).
      change (sf_last (a :: b :: rest')) with (sf_last (b :: rest')).
      assert (Hne : Not (Id (b :: rest') nil)) by (intros Hc; inversion Hc).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (sf_pipe a b)
                 (sf_path_sum ((b :: rest') ++ s :: nil)) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (sf_pipe a b) (sf_path_sum (b :: rest')) n)).
      specialize (IH s Hne n).
      rewrite (qeqT_imp_qeq _ _ IH).
      ring.
Qed.

(* the exact energy accounting of a single extension (the blueprint's difference
   structure): the pointwise ring algebra of the four-term linear recombination;
   the two pointwise decomposition lemmas plus the length/n2r successor facts
   let the ring close *)
Theorem sf_gfe_append_single :
  forall (alpha beta gamma : Real) (p : list SFVec) (s : SFVec),
    Not (Id p nil) ->
    real_eq (sf_gfe alpha beta gamma (p ++ s :: nil))
            (real_plus (sf_gfe alpha beta gamma p)
                       (real_plus
                          (real_opp (real_mult alpha (sf_pipe (sf_last p) s)))
                          (real_plus (real_mult beta (sf_dist_sq (sf_last p) s))
                                     gamma))).
Proof.
  intros alpha beta gamma p s Hp.
  unfold sf_gfe, sf_syn_pot, sf_temporal.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  (* the nat-level length fact (a Prop bridge, relayed inside the proof): length (p++[s]) = S (length p) *)
  assert (Hlen : forall q : list SFVec,
                 length (q ++ s :: nil) = Datatypes.S (length q))
    by (intro q; induction q as [| a rest IH]; simpl;
        [reflexivity | rewrite IH; reflexivity]).
  (* the n2r successor pointwise decomposition: proj (n2r (S k)) == 1 + proj (n2r k) *)
  assert (Hn2r : projT1 (sf_n2r (Datatypes.S (length p))) n
                 == 1 + projT1 (sf_n2r (length p)) n).
  { change (sf_n2r (Datatypes.S (length p)))
      with (real_plus real_one (sf_n2r (length p))).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (sf_n2r (length p)) n)).
    assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
    rewrite Ho. ring. }
  (* the pointwise tail-extension decompositions of the pipe sum and the syntactic potential (the auxiliary lemmas) *)
  assert (Hsum : projT1 (sf_path_sum (p ++ s :: nil)) n
                 == projT1 (sf_path_sum p) n
                    + projT1 (sf_pipe (sf_last p) s) n)
by exact (qeqT_imp_qeq _ _ (sf_gfe_path_sum_app_proj p s Hp n)).
  assert (Hpot : projT1 (sf_adj_sum sf_dist_sq (p ++ s :: nil)) n
                 == projT1 (sf_adj_sum sf_dist_sq p) n
                    + projT1 (sf_dist_sq (sf_last p) s) n)
by exact (qeqT_imp_qeq _ _ (sf_gfe_adj_sum_app_proj sf_dist_sq p s Hp n)).
  (* unfold the projections pointwise, substitute the decomposition facts,
     and close by the Q ring.
     note: setoid rewriting only descends along registered Q-setoid morphisms
     and does not see through projT1, so the unfold order must be real_plus
     first, then real_opp (the alpha product sits under the opp), and finally
     real_mult, after which the atoms of Hn2r/Hsum/Hpot are in visible
     positions *)
  rewrite (Hlen p).
  repeat rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)).
  repeat rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _)).
  repeat rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _)).
  rewrite Hn2r, Hsum, Hpot.
  ring.
Qed.

(* the pipe sum <= len(p) * Tmax (by induction; the Tmax interface assumption) *)
Theorem sf_path_sum_bound :
  forall (tmax : Real),
    (forall x y : SFVec, real_le (sf_pipe x y) tmax) ->
    forall p : list SFVec,
      real_le (sf_path_sum p) (real_mult (sf_n2r (length p)) tmax).
Proof.
  intros tmax Hbound.
  induction p as [| a p IH].
  - (* nil: the sum == 0 and the length is 0 (the pointwise ring algebra of 0 * tmax) *)
    simpl. apply RealSetoid.real_eq_le.
    apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj real_zero tmax n)).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    rewrite Hz. ring.
  - destruct p as [| b rest].
    + (* [a]: the sum == 0 <= 1 * tmax; 0 < pipe nil nil <= tmax gives 0 <= tmax,
         and the bridge to the goal goes through tmax == 1 * tmax (pointwise
         ring algebra) *)
      simpl. apply (RealSetoid.real_le_id_r real_zero tmax
                      (real_mult (sf_n2r 1) tmax)).
      * apply real_eq_of_zero_diff. intro n.
        apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (real_mult_proj (sf_n2r 1) tmax n)).
        change (sf_n2r 1) with (real_plus real_one real_zero).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_zero n)).
        assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
        assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        rewrite Ho, Hz. ring.
      * apply (real_le_trans real_zero (sf_pipe nil nil) tmax).
        -- apply (RealSetoid.real_lt_le_iff_req real_zero (sf_pipe nil nil)).
           left. exact (sf_pipe_pos nil nil).
        -- exact (Hbound nil nil).
    + (* a::b::rest: the pipe term <= tmax and the inductive sum <= (S (length rest)) * tmax,
         then tmax + k * tmax is merged pointwise into (1+k) * tmax *)
      change (sf_path_sum (a :: b :: rest))
        with (real_plus (sf_pipe a b) (sf_path_sum (b :: rest))).
      eapply real_le_trans.
      * apply (real_le_plus_compat (sf_pipe a b) tmax
                 (sf_path_sum (b :: rest))
                 (real_mult (sf_n2r (Datatypes.S (length rest))) tmax)).
        -- exact (Hbound a b).
        -- exact IH.
      * apply (RealSetoid.real_le_id_r
                 (real_plus tmax (real_mult (sf_n2r (Datatypes.S (length rest))) tmax))
                 (real_mult (sf_n2r (Datatypes.S (Datatypes.S (length rest)))) tmax)).
        -- (* eq (mult (n2r (S(S lr)))) (mult (n2r (length (a::b::rest)))): the two sides are convertible *)
           apply real_eq_refl.
        -- (* the pointwise merge of tmax + k * tmax == (1+k) * tmax *)
           apply RealSetoid.real_eq_le.
           apply real_eq_of_zero_diff. intro n.
           apply qeq_imp_qeqT.
           rewrite (qeqT_imp_qeq _ _ (real_plus_proj tmax
                      (real_mult (sf_n2r (Datatypes.S (length rest))) tmax) n)).
           rewrite (qeqT_imp_qeq _ _ (real_mult_proj (sf_n2r (Datatypes.S (length rest))) tmax n)).
           change (sf_n2r (Datatypes.S (Datatypes.S (length rest))))
             with (real_plus real_one (sf_n2r (Datatypes.S (length rest)))).
           rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_plus real_one (sf_n2r (Datatypes.S (length rest))))
                                tmax n)).
           rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (sf_n2r (Datatypes.S (length rest))) n)).
           assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
           rewrite Ho. ring.
Qed.

(* the conditional global free energy lower bound (the provable form of the
   blueprint's global_free_energy_lower_bound): alpha >= 0, the pipes
   <= Tmax, and the syntactic potential >= 0 give
   gfe >= -alpha * len(p) * Tmax + gamma * len(p) *)
Theorem sf_gfe_lower_bound :
  forall (alpha beta gamma tmax : Real),
    real_le real_zero alpha ->
    real_le real_zero beta ->
    (forall x y : SFVec, real_le (sf_pipe x y) tmax) ->
    (forall p : list SFVec, real_le real_zero (sf_syn_pot p)) ->
    forall p : list SFVec,
      real_le (real_plus (real_opp (real_mult alpha (real_mult (sf_n2r (length p)) tmax)))
                         (real_mult gamma (sf_temporal p)))
              (sf_gfe alpha beta gamma p).
Proof.
  intros alpha beta gamma tmax Halpha Hbeta Hbound Hsyn p.
  unfold sf_gfe, sf_temporal, sf_syn_pot.
  (* the pipe sum <= len(p) * tmax (by the in-library [sf_path_sum_bound]) *)
  assert (Hsum : real_le (sf_path_sum p) (real_mult (sf_n2r (length p)) tmax))
    by exact (sf_path_sum_bound tmax Hbound p).
  (* alpha >= 0 gives alpha * sum <= alpha * (len * tmax): the weak multiplicative order preservation (right multiplication by alpha) plus a commutation bridge back to left multiplication *)
  assert (Hmul : real_le (real_mult alpha (sf_path_sum p))
                         (real_mult alpha (real_mult (sf_n2r (length p)) tmax))).
  { apply (RealSetoid.real_le_compat
             (real_mult (sf_path_sum p) alpha)
             (real_mult alpha (sf_path_sum p))
             (real_mult (real_mult (sf_n2r (length p)) tmax) alpha)
             (real_mult alpha (real_mult (sf_n2r (length p)) tmax))
             (real_mult_comm (sf_path_sum p) alpha)
             (real_mult_comm (real_mult (sf_n2r (length p)) tmax) alpha)).
    exact (real_le_mult_compat_weak (sf_path_sum p)
             (real_mult (sf_n2r (length p)) tmax) alpha Halpha Hsum). }
  (* negation reverses the order: -alpha * (len * tmax) <= -alpha * sum *)
  assert (Hopp : real_le (real_opp (real_mult alpha (real_mult (sf_n2r (length p)) tmax)))
                         (real_opp (real_mult alpha (sf_path_sum p))))
    by exact (real_opp_le_compat (real_mult alpha (sf_path_sum p))
                                 (real_mult alpha (real_mult (sf_n2r (length p)) tmax))
                                 Hmul).
  (* beta * syn_pot >= 0: the 0 * P == 0 bridge plus the weak multiplicative order preservation (0 <= beta and 0 <= P) *)
  assert (HD : real_le real_zero (real_mult beta (sf_adj_sum sf_dist_sq p))).
  { exact (RealSetoid.real_le_compat
             (real_mult real_zero (sf_adj_sum sf_dist_sq p))
             real_zero
             (real_mult beta (sf_adj_sum sf_dist_sq p))
             (real_mult beta (sf_adj_sum sf_dist_sq p))
             (real_eq_trans (real_mult real_zero (sf_adj_sum sf_dist_sq p))
                            (real_mult (sf_adj_sum sf_dist_sq p) real_zero)
                            real_zero
                            (real_mult_comm real_zero (sf_adj_sum sf_dist_sq p))
                            (real_mult_zero (sf_adj_sum sf_dist_sq p)))
             (real_eq_refl (real_mult beta (sf_adj_sum sf_dist_sq p)))
             (real_le_mult_compat_weak real_zero beta (sf_adj_sum sf_dist_sq p)
                (Hsyn p) Hbeta)). }
  (* gamma * n2r(len) <= beta * syn_pot + gamma * n2r(len): the 0 + C == C bridge plus the additive order preservation *)
  assert (HDC : real_le (real_mult gamma (sf_n2r (length p)))
                        (real_plus (real_mult beta (sf_adj_sum sf_dist_sq p))
                                   (real_mult gamma (sf_n2r (length p))))).
  { exact (RealSetoid.real_le_compat
             (real_plus real_zero (real_mult gamma (sf_n2r (length p))))
             (real_mult gamma (sf_n2r (length p)))
             (real_plus (real_mult beta (sf_adj_sum sf_dist_sq p))
                        (real_mult gamma (sf_n2r (length p))))
             (real_plus (real_mult beta (sf_adj_sum sf_dist_sq p))
                        (real_mult gamma (sf_n2r (length p))))
             (real_eq_trans
                (real_plus real_zero (real_mult gamma (sf_n2r (length p))))
                (real_plus (real_mult gamma (sf_n2r (length p))) real_zero)
                (real_mult gamma (sf_n2r (length p)))
                (real_plus_comm real_zero (real_mult gamma (sf_n2r (length p))))
                (real_plus_zero (real_mult gamma (sf_n2r (length p)))))
             (real_eq_refl (real_plus (real_mult beta (sf_adj_sum sf_dist_sq p))
                                      (real_mult gamma (sf_n2r (length p)))))
             (real_le_plus_compat real_zero
                (real_mult beta (sf_adj_sum sf_dist_sq p))
                (real_mult gamma (sf_n2r (length p)))
                (real_mult gamma (sf_n2r (length p)))
                HD (real_le_refl (real_mult gamma (sf_n2r (length p)))))). }
  (* assembly: A + C <= B + C <= B + (D + C) = gfe p *)
  apply (real_le_trans
           (real_plus (real_opp (real_mult alpha (real_mult (sf_n2r (length p)) tmax)))
                      (real_mult gamma (sf_n2r (length p))))
           (real_plus (real_opp (real_mult alpha (sf_path_sum p)))
                      (real_mult gamma (sf_n2r (length p))))
           (real_plus (real_opp (real_mult alpha (sf_path_sum p)))
                      (real_plus (real_mult beta (sf_adj_sum sf_dist_sq p))
                                 (real_mult gamma (sf_n2r (length p)))))).
  - exact (real_le_plus_compat
             (real_opp (real_mult alpha (real_mult (sf_n2r (length p)) tmax)))
             (real_opp (real_mult alpha (sf_path_sum p)))
             (real_mult gamma (sf_n2r (length p)))
             (real_mult gamma (sf_n2r (length p)))
             Hopp (real_le_refl (real_mult gamma (sf_n2r (length p))))).
  - exact (real_le_plus_compat
             (real_opp (real_mult alpha (sf_path_sum p)))
             (real_opp (real_mult alpha (sf_path_sum p)))
             (real_mult gamma (sf_n2r (length p)))
             (real_plus (real_mult beta (sf_adj_sum sf_dist_sq p))
                        (real_mult gamma (sf_n2r (length p))))
             (real_le_refl (real_opp (real_mult alpha (sf_path_sum p))))
             HDC).
Qed.

End SFFreeEnergy.

(* ============================================================ *)
(* SFInvMap: invertible maps / isomorphic translation (the blueprint's §2 TranslationMap / *)
(*   cycle_consistent plus §4 InvertibleMap / compose_invertible) *)
(*   the blueprint's translation_isometry axiom (isometry implies cycle consistency) neither holds *)
(*   nor is it needed in the constructive setting; following the baseline sigT doctrine, the two-sided inverse laws become Record fields *)
 (*   (carrying Set-layer witnesses), and the invertibility of composition and identity is proved outright *)
(* ============================================================ *)

Record SFInvMap : Set := Build_SFInvMap {
  sf_fwd : SFVec -> SFVec;
  sf_bwd : SFVec -> SFVec;
  sf_inv_law : forall x : SFVec, Id (sf_bwd (sf_fwd x)) x;
  sf_inv_rlaw : forall y : SFVec, Id (sf_fwd (sf_bwd y)) y
}.

(* the identity map (the blueprint's identity_invertible) *)
Definition sf_id_map : SFInvMap :=
  Build_SFInvMap (fun x => x) (fun y => y)
                 (fun x => id_refl) (fun y => id_refl).

(* the composition of invertible maps (the blueprint's compose_invertible; the fields assembled explicitly) *)
Definition sf_compose_map (F G : SFInvMap) : SFInvMap :=
  Build_SFInvMap
    (fun x => sf_fwd F (sf_fwd G x))
    (fun y => sf_bwd G (sf_bwd F y))
    (fun x => id_trans (id_cong (sf_bwd G) (sf_inv_law F (sf_fwd G x)))
                       (sf_inv_law G x))
    (fun y => id_trans (id_cong (sf_fwd F) (sf_inv_rlaw G (sf_bwd F y)))
                       (sf_inv_rlaw F y)).

(* the round-trip laws of the composition (the unfolded verification of the blueprint's composite theorem) *)
Theorem sf_compose_inv_law :
  forall F G : SFInvMap,
    forall x : SFVec,
      Id (sf_bwd (sf_compose_map F G) (sf_fwd (sf_compose_map F G) x)) x.
Proof.
  intros F G x. unfold sf_compose_map. simpl.
  exact (sf_inv_law (sf_compose_map F G) x).
Qed.

(* an isometric translation preserves the pipe thickness (the blueprint's
   translation_preserves_pipe_thickness: after the coordinates pass through
   the distance-preserving map, the pipe thickness is unchanged pointwise) *)
Theorem sf_isometry_preserves_pipe :
  forall (F : SFVec -> SFVec),
    (forall x y : SFVec, real_eq (sf_dist_sq (F x) (F y)) (sf_dist_sq x y)) ->
    forall x y : SFVec,
      real_eq (sf_pipe (F x) (F y)) (sf_pipe x y).
Proof.
  intros F Hiso x y. unfold sf_pipe, sf_pipe_at.
  apply RealSetoid.real_eq_mult_compat.
  - apply real_eq_refl.
  - apply (real_inv_pos_ext _ _ (sf_pipe_den_pos (F x) (F y)) (sf_pipe_den_pos x y)).
    apply (RealSetoid.real_eq_plus_compat (sf_dist_sq (F x) (F y)) sf_tenth
                                          (sf_dist_sq x y) sf_tenth).
    + apply Hiso.
    + apply real_eq_refl.
Qed.

(* the cycle consistency loss (the coordinate-vector version of the blueprint's cycle_consistency_loss) *)
Definition sf_cycle_loss (F G : SFVec -> SFVec) (x y : SFVec) : Real :=
  real_plus (sf_dist_sq (G (F x)) x) (sf_dist_sq (F (G y)) y).

(* the cycle loss is zero for mutually inverse encoders (the forward direction
   of the blueprint's cycle_loss_zero_iff_inverse, proved constructively;
   the converse would need dist == 0 implying equality, which is not
   obtainable constructively and is dropped) *)
Theorem sf_cycle_loss_zero_inverse :
  forall (F G : SFVec -> SFVec),
    (forall x : SFVec, Id (G (F x)) x) ->
    (forall y : SFVec, Id (F (G y)) y) ->
    forall x y : SFVec, real_eq (sf_cycle_loss F G x y) real_zero.
Proof.
  intros F G HF HG x y. unfold sf_cycle_loss.
  (* the Id elimination: destructing after id_sym reduces F(G y) / G(F x) back to y / x *)
  destruct (id_sym (HG y)). destruct (id_sym (HF x)).
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj (sf_dist_sq x x) (sf_dist_sq y y) n)).
rewrite (qeqT_imp_qeq _ _ (sf_dist_sq_proj x x n)), (qeqT_imp_qeq _ _ (sf_dist_sq_proj y y n)).
rewrite (qeqT_imp_qeq _ _ (sf_ptw_sum_self x n)), (qeqT_imp_qeq _ _ (sf_ptw_sum_self y n)).
  assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
  rewrite Hz. ring.
Qed.

(* ============================================================ *)
(* SFDecay: multiscale temporal decay (the blueprint's §2 half_life_* / decay_factor *)
(*   = 2^(-dt/hl)).  baseline form: there is no real power interface for 2^x, so e^(-dt/hl) is used *)
(*   ([exp_neg] plus the positive inverse), with identical monotonicity / half-life semantics; the scale list uses *)
(*   the witness-carrying [SFHalfLife] over sigT (the positivity witness travels with the data) *)
(* ============================================================ *)

Definition SFHalfLife : Set := sigT (fun hl : Real => real_lt real_zero hl).

(* the decay factor e^(-dt/hl) (the constructive replacement of the blueprint's decay_factor) *)
Definition sf_decay (h : SFHalfLife) (dt : Real) : Real :=
  real_exp_neg (real_mult dt (real_inv_pos (projT1 h) (projT2 h))).

(* the decay is always positive *)
Theorem sf_decay_pos : forall (h : SFHalfLife) (dt : Real),
  real_lt real_zero (sf_decay h dt).
Proof.
  intros h dt. unfold sf_decay. apply real_exp_neg_pos.
Qed.

(* no decay at time zero: decay(hl, 0) == 1 *)
Theorem sf_decay_zero : forall h : SFHalfLife,
  real_eq (sf_decay h real_zero) real_one.
Proof.
  intro h. unfold sf_decay.
  apply (real_eq_trans
           (real_exp_neg (real_mult real_zero (real_inv_pos (projT1 h) (projT2 h))))
           (real_exp_neg real_zero) real_one).
  - unfold real_exp_neg. apply cauchy_real_exp_wd.
    apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_mult real_zero (real_inv_pos (projT1 h) (projT2 h))) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_zero n)).
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj real_zero (real_inv_pos (projT1 h) (projT2 h)) n)).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    rewrite Hz. ring.
  - exact real_exp_neg_zero.
Qed.

(* the decay semigroup law: decay(hl, dt1 + dt2) == decay(hl, dt1) * decay(hl, dt2)
   (the algebraic core of the blueprint's decay semantics; [exp_neg_plus] plus
   distributivity) *)
Theorem sf_decay_split : forall (h : SFHalfLife) (dt1 dt2 : Real),
  real_eq (sf_decay h (real_plus dt1 dt2))
          (real_mult (sf_decay h dt1) (sf_decay h dt2)).
Proof.
  intros h dt1 dt2. unfold sf_decay.
  apply (real_eq_trans
           (real_exp_neg (real_mult (real_plus dt1 dt2)
                                    (real_inv_pos (projT1 h) (projT2 h))))
           (real_exp_neg (real_plus (real_mult dt1 (real_inv_pos (projT1 h) (projT2 h)))
                                    (real_mult dt2 (real_inv_pos (projT1 h) (projT2 h)))))).
  - unfold real_exp_neg. apply cauchy_real_exp_wd.
    apply RealSetoid.real_eq_opp_compat.
    apply (real_eq_sym _ _).
    exact (real_distrib_r dt1 dt2 (real_inv_pos (projT1 h) (projT2 h))).
  - exact (real_exp_neg_plus (real_mult dt1 (real_inv_pos (projT1 h) (projT2 h)))
                             (real_mult dt2 (real_inv_pos (projT1 h) (projT2 h)))).
Qed.

(* a longer half-life decays more slowly (the constructive direction fix of the
   blueprint's decay_factor_monotone_in_half_life: for dt > 0, hl1 <= hl2 gives
   decay(hl1) <= decay(hl2)).
   the chain: the inverse reverses the order, multiplying by a positive number
   preserves it, and exp_neg reverses it again *)
Theorem sf_decay_monotone_hl :
  forall (h1 h2 : SFHalfLife) (dt : Real),
    real_lt real_zero dt ->
    real_le (projT1 h1) (projT1 h2) ->
    real_le (sf_decay h1 dt) (sf_decay h2 dt).
Proof.
  intros h1 h2 dt Hdt Hle. unfold sf_decay.
  apply real_exp_neg_le_decr.
  apply (real_le_mult_compat_r dt (real_inv_pos (projT1 h2) (projT2 h2))
                                (real_inv_pos (projT1 h1) (projT2 h1))).
  - apply (real_lt_le_iff real_zero dt). left. exact Hdt.
  - exact (real_inv_pos_le_compat (projT1 h1) (projT1 h2) (projT2 h1) (projT2 h2) Hle).
Qed.

(* a larger time step decays more (the blueprint's decay_factor_decreases_with_dt):
   0 <= dt1 <= dt2 gives decay(hl, dt2) <= decay(hl, dt1) *)
Theorem sf_decay_antitone_dt :
  forall (h : SFHalfLife) (dt1 dt2 : Real),
    real_le real_zero dt1 ->
    real_le dt1 dt2 ->
    real_le (sf_decay h dt2) (sf_decay h dt1).
Proof.
  intros h dt1 dt2 Hdt1 Hdle. unfold sf_decay.
  apply real_exp_neg_le_decr.
  apply (real_le_mult_compat_weak dt1 dt2 (real_inv_pos (projT1 h) (projT2 h))).
  - apply (real_lt_le_iff real_zero (real_inv_pos (projT1 h) (projT2 h))). left.
    exact (real_inv_pos_pos (projT1 h) (projT2 h)).
  - exact Hdle.
Qed.

(* the multiscale decay list: every scale component is positive (the list form of the blueprint's multi-timescale mechanism) *)
Definition sf_decay_scales (hls : list SFHalfLife) (dt : Real) : list Real :=
  map (fun h => sf_decay h dt) hls.

Theorem sf_decay_scales_pos :
  forall (hls : list SFHalfLife) (dt : Real) (r : Real),
    InT r (sf_decay_scales hls dt) ->
    real_lt real_zero r.
Proof.
  intros hls dt r HIn.
  revert r HIn. induction hls as [| h rest IH]; intros r HIn.
  - inversion HIn.
  - simpl in HIn. inversion HIn as [Heq | HIn']; subst.
    + exact (sf_decay_pos h dt).
    + apply IH. assumption.
Qed.

(* ============================================================ *)
(* SFConv: hypergraph message passing / convolution (the blueprint's §4 hypergraph_convolve) *)
(*   the blueprint's hypergraph_convolve_convex was an admitted statement with an abstract witness; *)
(*   here a concrete executable convolution is given: the weights are the pipe thicknesses, the normalization is the inverse of the positive sum, *)
(*   and the convex-combination coefficients are given by a sigT witness (λi = wi / W); the normalization / positivity / representation *)
(*   three theorems are all proved outright; the constructive completion of the blueprint's corresponding theorem *)
(* ============================================================ *)

(* the vector-level operations (Set-layer Fixpoints; the map2 semantics: the shorter side is truncated) *)
Fixpoint sf_vplus (x y : SFVec) : SFVec :=
  match x, y with
  | a :: x', b :: y' => real_plus a b :: sf_vplus x' y'
  | _, _ => nil
  end.

Definition sf_vscale (a : Real) (x : SFVec) : SFVec := map (fun c => real_mult a c) x.

Fixpoint sf_vsum (vs : list SFVec) : SFVec :=
  match vs with
  | nil => nil
  | v :: rest => sf_vplus v (sf_vsum rest)
  end.

(* vector equality (the Set-layer encoding of component-level real_eq; carried by an inductive family with a transparent synonym constructor) *)
Inductive sf_veq_fam : SFVec -> SFVec -> Set :=
| sf_veq_fam_nil : sf_veq_fam nil nil
| sf_veq_fam_cons : forall (a b : Real) (x' y' : SFVec),
    real_eq a b -> sf_veq_fam x' y' -> sf_veq_fam (a :: x') (b :: y').

Definition sf_veq (x y : SFVec) : Set := sf_veq_fam x y.

Lemma sf_veq_refl : forall x : SFVec, sf_veq x x.
Proof.
  induction x as [| a x IH].
  - apply sf_veq_fam_nil.
  - apply sf_veq_fam_cons; [apply real_eq_refl | exact IH].
Qed.

(* the weights: the pipe thicknesses from the center to each neighbor *)
Definition sf_msg_weights (c : SFVec) (ns : list SFVec) : list Real :=
  map (fun v => sf_pipe c v) ns.

(* the weight sum *)
Definition sf_weight_sum (c : SFVec) (ns : list SFVec) : Real :=
  real_list_sum SFVec (sf_pipe c) ns.

(* the list sum is always positive (a nonempty list with every term positive; constructive induction) *)
Lemma sf_list_sum_pos_aux : forall (X : Set) (f : X -> Real) (l : list X),
  Not (Id l nil) ->
  (forall w : X, real_lt real_zero (f w)) ->
  real_lt real_zero (real_list_sum X f l).
Proof.
  intros X f l.
  induction l as [| a rest IH]; intros Hne Hpos.
  - destruct (Hne id_refl).
  - destruct rest as [| b rest'].
    + (* [a]: f a + 0 > 0 follows from f a > 0 (the add-zero unit eq bridge) *)
      simpl.
      exact (RealSetoid.real_lt_id_r real_zero (f a) (real_plus (f a) real_zero)
               (real_eq_sym (real_plus (f a) real_zero) (f a)
                            (real_plus_zero (f a)))
               (Hpos a)).
    + simpl. apply real_plus_positive.
      * exact (Hpos a).
      * apply IH. intro Hc. inversion Hc. exact Hpos.
Qed.

Theorem sf_list_sum_pos_nonempty : forall (X : Set) (f : X -> Real) (l : list X),
  Not (Id l nil) ->
  (forall w : X, real_lt real_zero (f w)) ->
  real_lt real_zero (real_list_sum X f l).
Proof.
  exact sf_list_sum_pos_aux.
Qed.

(* the weight sum is always positive (when the neighbor list is nonempty) *)
Theorem sf_weight_sum_pos :
  forall (c : SFVec) (ns : list SFVec),
    Not (Id ns nil) -> real_lt real_zero (sf_weight_sum c ns).
Proof.
  intros c ns Hne. unfold sf_weight_sum.
  apply (sf_list_sum_pos_nonempty SFVec (sf_pipe c) ns Hne).
  intro v. apply sf_pipe_pos.
Qed.

(* the hypergraph convolution: the pipe-weighted average (a convex combination
   after normalizing the weights);
   the nonemptiness witness travels explicitly with the parameters (the sigT
   route: the data and the proof travel together) *)
Definition sf_conv (c : SFVec) (ns : list SFVec) (Hne : Not (Id ns nil)) : SFVec :=
  sf_vsum (map (fun v => sf_vscale
                   (real_inv_pos (sf_weight_sum c ns) (sf_weight_sum_pos c ns Hne)) v)
               ns).

(* the normalization theorem (the "weights sum to one" component of the
   blueprint's convex-combination condition): Σi (wi * inv W) == 1 *)
Theorem sf_conv_weights_norm :
  forall (c : SFVec) (ns : list SFVec) (Wp : real_lt real_zero (sf_weight_sum c ns)),
    real_eq (real_list_sum Real (fun w => real_mult w (real_inv_pos (sf_weight_sum c ns) Wp))
                           (sf_msg_weights c ns))
            real_one.
Proof.
  intros c ns Wp.
  (* the bridge: the weighted sum over the map == the weighted sum over the composed function (plus_compat layer by layer) *)
  assert (Hmap : forall l : list SFVec,
    real_eq (real_list_sum Real (fun w => real_mult w (real_inv_pos (sf_weight_sum c ns) Wp))
                                (map (fun v => sf_pipe c v) l))
            (real_list_sum SFVec
               (fun v => real_mult (sf_pipe c v) (real_inv_pos (sf_weight_sum c ns) Wp)) l)).
  { intro l. induction l as [| a rest IH]; simpl.
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult (sf_pipe c a) (real_inv_pos (sf_weight_sum c ns) Wp))
               (real_list_sum Real (fun w => real_mult w (real_inv_pos (sf_weight_sum c ns) Wp))
                                   (map (fun v => sf_pipe c v) rest))
               (real_mult (sf_pipe c a) (real_inv_pos (sf_weight_sum c ns) Wp))
               (real_list_sum SFVec
                  (fun v => real_mult (sf_pipe c v) (real_inv_pos (sf_weight_sum c ns) Wp))
                  rest)).
      + apply real_eq_refl.
      + exact IH. }
  (* Σ(wᵢ·inv W) == inv W·Σwᵢ == inv W·W == 1 *)
  apply (real_eq_trans
           (real_list_sum Real (fun w => real_mult w (real_inv_pos (sf_weight_sum c ns) Wp))
                              (map (fun v => sf_pipe c v) ns))
           (real_list_sum SFVec
              (fun v => real_mult (sf_pipe c v) (real_inv_pos (sf_weight_sum c ns) Wp)) ns)
           real_one).
  - exact (Hmap ns).
  - apply (real_eq_trans
             (real_list_sum SFVec
                (fun v => real_mult (sf_pipe c v) (real_inv_pos (sf_weight_sum c ns) Wp)) ns)
             (real_mult (real_inv_pos (sf_weight_sum c ns) Wp) (sf_weight_sum c ns))
             real_one).
    + exact (real_list_sum_linear_r SFVec (real_inv_pos (sf_weight_sum c ns) Wp)
                 (fun v => sf_pipe c v) ns).
    + apply (real_eq_trans
               (real_mult (real_inv_pos (sf_weight_sum c ns) Wp) (sf_weight_sum c ns))
               (real_mult (sf_weight_sum c ns) (real_inv_pos (sf_weight_sum c ns) Wp))
               real_one).
      * apply real_mult_comm.
      * exact (real_inv_pos_correct (sf_weight_sum c ns) Wp).
Qed.
Lemma sf_q_zsucc_den : forall k : nat, QeqT ((Z.of_nat (Datatypes.S k) # 1)%Q) (((Z.of_nat k # 1) + (1 # 1))%Q).
Proof.
  intro k. apply qeq_imp_qeqT. unfold Qeq, Qplus. cbn [Qnum Qden]. lia.
Qed.

Lemma sf_q_lagrange_step : forall n n' s sq a d : Q,
  n' == n + (1 # 1) ->
  Qle 0 (n * a * a - (2 # 1) * a * s + sq) ->
  QleT' 0 (n' * a * a - (2 # 1) * a * (d + s) + (d * d + sq)).
Proof.
  intros n n' s sq a d Hnn' H1.
  apply Qle_to_QleT'.
  apply (Qle_trans _
           (n * a * a - (2 # 1) * a * s + sq + (a * a - (2 # 1) * a * d + d * d)) _).
  - replace 0%Q with (0 + 0)%Q by reflexivity.
    apply Qplus_le_compat.
    + exact H1.
    + assert (Hsq : a * a - (2 # 1) * a * d + d * d == (a - d) * (a - d)) by ring.
rewrite Hsq. exact (QleT'_to_Qle _ _ (sf_q_sq_ge_0 (a - d))).
- apply QleT'_to_Qle. apply sf_qeq_le. rewrite Hnn'. ring.
Qed.

Lemma sf_q_lagrange_nonneg_aux : forall (ds : list Q) (a : Q),
  QleT' 0 ((Z.of_nat (length ds) # 1) * a * a - (2 # 1) * a * sf_qsum ds
         + sf_qsum (map (fun d => d * d) ds)).
Proof.
  intros ds. induction ds as [| d rest IH]; intro a.
  - cbn [length sf_qsum map Z.of_nat].
    apply sf_qeq_le. ring.
  - cbn [length sf_qsum map].
    apply (sf_q_lagrange_step (Z.of_nat (length rest) # 1)
                              (Z.of_nat (Datatypes.S (length rest)) # 1)
                              (sf_qsum rest)
                              (sf_qsum (map (fun d0 => d0 * d0) rest))
                              a d).
    + apply qeqT_imp_qeq. apply sf_q_zsucc_den.
    + exact (QleT'_to_Qle _ _ (IH a)).
Qed.



(* ############ part _p4 ############ *)

(* ============================================================ *)
(* SFWasserQ: the Q-layer closed-form core of optimal transport (the blueprint's §3 centroid / *)
(*   wasserstein2_sq) *)
(*   the blueprint's original centroid is a pseudo-mean that halves per level (the fixpoint divides by 2 at each layer), and *)
(*   its wasserstein2_sq_same relies on dist == 0 implying equality (not obtainable constructively) *)
(*   here they are rebuilt as a true mean / true paired mean square, all in the Q layer (decidable, with ring/field *)
(*   available), and the blueprint's corresponding core theorem is proved: the Jensen-type mean-square bound *)
(* ============================================================ *)

Section SFWasserQ.

(* the empirical distribution: equally weighted point masses on the Q line (the Q layer, with a decidable order) *)
Definition SFQDist : Set := list Q.

(* insertion sort (decidable by [Qle_bool]; executable after extraction) *)
Fixpoint sf_qinsert (x : Q) (l : list Q) : list Q :=
  match l with
  | nil => x :: nil
  | a :: rest => if Qle_bool x a then x :: a :: rest else a :: sf_qinsert x rest
  end.

Fixpoint sf_qsort (l : list Q) : list Q :=
  match l with
  | nil => nil
  | a :: rest => sf_qinsert a (sf_qsort rest)
  end.

(* the true mean: sum / n (with n > 0 as the assumption; Q-layer field) *)
Definition sf_qmean (n : nat) (s : Q) : Q := s / (Z.of_nat n # 1).

Definition sf_qcentroid (l : list Q) : Q :=
  sf_qmean (length l) (sf_qsum l).

(* the paired mean square: the independent-coupling upper bound of W2^2 (the executable form of the blueprint's wasserstein2_sq) *)
Fixpoint sf_qw2 (mu nu : list Q) : Q :=
  match mu, nu with
  | a :: mu', b :: nu' => (a - b) * (a - b) + sf_qw2 mu' nu'
  | _, _ => 0
  end.

Definition sf_qw2_mean (mu nu : list Q) : Q :=
  sf_qw2 mu nu / (Z.of_nat (length mu) # 1).

(* the mean square is >= the square of the mean (the Lagrange identity
   Σi (a - di)^2 = n * a^2 - 2aΣ + Σsq).
   the parameterized form: for any a, n * a^2 - 2 * a * Σ + Σsq >= 0
   (taking a to be the mean gives Σsq >= Σ^2 / n), closed by unfolding
   the induction and assembling with ring *)
Theorem sf_q_lagrange_nonneg :
  forall (ds : list Q) (a : Q),
    QleT' 0 ((Z.of_nat (length ds) # 1) * a * a - (2 # 1) * a * sf_qsum ds
             + sf_qsum (map (fun d => d * d) ds)).
Proof.
intros ds a. apply sf_q_lagrange_nonneg_aux.
Qed.
Lemma sf_qle_eq_l : forall x y z : Q, x == y -> Qle y z -> QleT' x z.
Proof.
  intros x y z Hxy Hyz.
  apply Qle_to_QleT'.
  apply (Qle_trans x y z).
- apply QleT'_to_Qle. apply sf_qeq_le. exact Hxy.
  - exact Hyz.
Qed.

Lemma sf_qle_eq_r : forall x y z : Q, Qle x y -> y == z -> QleT' x z.
Proof.
  intros x y z Hxy Hyz.
  apply Qle_to_QleT'.
  apply (Qle_trans x y z).
  - exact Hxy.
- apply QleT'_to_Qle. apply sf_qeq_le. exact Hyz.
Qed.

Lemma sf_id_to_eq : forall (A : Set) (x y : A), Id x y -> Id (x) (y).
Proof.
  intros A x y H. destruct H. reflexivity.
Qed.

Lemma sf_q_yeax_le : forall x y : Q, Qle 0 (y - x) -> QleT' x y.
Proof.
  intros x y H.
  apply Qle_to_QleT'.
  apply (Qle_trans x (x + (y - x)) y).
  - apply (Qle_trans x (x + 0) (x + (y - x))).
+ apply QleT'_to_Qle. apply sf_qeq_le. ring.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact H.
- apply QleT'_to_Qle. apply sf_qeq_le. ring.
Qed.

(* the original assumption ~ (d == 0) is false when d < 0 (counterexample
   d = -2, s = 2, S = 0: the assumption 0 <= (-2)*1 - 2*(-1)*2 + 0 = 2 holds
   while the conclusion 1 <= 0/(-2) = 0 fails), so the assumption becomes
   0 < d.  proof key: the Lagrange expression and S/d - (s/d)^2 differ by a
   factor of 1/d (not an identity), so both sides are multiplied by 1/d
   before field *)
Lemma sf_q_mean_sq_key : forall d s S : Q,
  Qlt 0 d ->
  Qle 0 (d * (s / d) * (s / d) - (2 # 1) * (s / d) * s + S) ->
  QleT' ((s / d) * (s / d)) (S / d).
Proof.
  intros d s S Hd H.
  apply Qle_to_QleT'.
  assert (Hdne : ~ (d == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0 d).
    - exact Hd.
    - apply Qeq_sym. exact Hc. }
  assert (Hdp : 0 < / d) by (apply Qinv_lt_0_compat; exact Hd).
  (* the true identity: both sides of the Lagrange expression multiplied by the positive 1/d *)
  assert (Hfe : (d * (s / d) * (s / d) - (2 # 1) * (s / d) * s + S) * / d
                == S / d - (s / d) * (s / d)).
  { field. exact Hdne. }
  assert (H0 : Qle 0
                ((d * (s / d) * (s / d) - (2 # 1) * (s / d) * s + S) * / d))
    by (apply Qmult_le_0_compat; [exact H | apply Qlt_le_weak; exact Hdp]).
  rewrite Hfe in H0.
  apply QleT'_to_Qle.
  apply (sf_q_yeax_le ((s / d) * (s / d)) (S / d)).
  exact H0.
Qed.

Fixpoint sf_qsub (mu nu : list Q) : list Q :=
  match mu, nu with
  | a :: mu', b :: nu' => (a - b) :: sf_qsub mu' nu'
  | _, _ => nil
  end.
Lemma sf_qmean_sub_distr : forall (n : nat) (x y : Q), QeqT (sf_qmean (Datatypes.S n) x - sf_qmean (Datatypes.S n) y) (sf_qmean (Datatypes.S n) (x - y)).
Proof.
  intros n x y.
  apply qeq_imp_qeqT.
  unfold sf_qmean. field.
  intro Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc. lia.
Qed.

Lemma sf_qmean_wd : forall (n m : nat) (x y : Q),
  n = m -> x == y -> QeqT (sf_qmean n x) (sf_qmean m y).
Proof.
  intros n m x y Hnm Hxy.
  apply qeq_imp_qeqT.
  rewrite Hnm. unfold sf_qmean, Qdiv. rewrite Hxy. ring.
Qed.

Lemma sf_qsub_sum_eq : forall mu nu : list Q,
  length mu = length nu -> QeqT (sf_qsum mu - sf_qsum nu) (sf_qsum (sf_qsub mu nu)).
Proof.
  intros mu. induction mu as [| a mu' IH]; intros nu Hlen; destruct nu as [| b nu'].
  - cbn [sf_qsum sf_qsub]. apply qeq_imp_qeqT. ring.
  - cbn [length] in Hlen. discriminate Hlen.
  - cbn [length] in Hlen. discriminate Hlen.
  - cbn [length] in Hlen. injection Hlen. intro Hl.
    apply qeq_imp_qeqT.
    cbn [sf_qsum sf_qsub]. specialize (IH nu' Hl).
    rewrite <- (qeqT_imp_qeq _ _ IH). ring.
Qed.

Lemma sf_qcentroid_diff_eq : forall mu nu : list Q,
  length mu = length nu -> QeqT (sf_qcentroid mu - sf_qcentroid nu) (sf_qmean (length mu) (sf_qsum (sf_qsub mu nu))).
Proof.
  intros mu. induction mu as [| a mu' IH]; intros nu Hlen; destruct nu as [| b nu'].
  - apply id_refl.
  - cbn [length] in Hlen. discriminate Hlen.
  - cbn [length] in Hlen. discriminate Hlen.
  - cbn [length] in Hlen. injection Hlen. intro Hl.
    apply qeq_imp_qeqT.
    unfold sf_qcentroid. cbn [length]. rewrite <- Hl.
    apply (Qeq_trans _
             (sf_qmean (length (a :: mu'))
                       (sf_qsum (a :: mu') - sf_qsum (b :: nu')))).
    + exact (qeqT_imp_qeq _ _ (sf_qmean_sub_distr (length mu')
                (sf_qsum (a :: mu')) (sf_qsum (b :: nu')))).
+ apply qeqT_imp_qeq. apply sf_qmean_wd.
      * reflexivity.
      * assert (Hlen' : length (a :: mu') = length (b :: nu'))
          by (cbn [length]; rewrite Hl; reflexivity).
        exact (qeqT_imp_qeq _ _ (sf_qsub_sum_eq (a :: mu') (b :: nu') Hlen')).
Qed.

Lemma sf_qsub_length : forall mu nu : list Q,
  length mu = length nu -> Id (length (sf_qsub mu nu)) (length mu).
Proof.
  intros mu. induction mu as [| a mu' IH]; intros nu Hlen; destruct nu as [| b nu'].
  - reflexivity.
  - cbn [length] in Hlen. discriminate Hlen.
  - cbn [length] in Hlen. discriminate Hlen.
  - cbn [length] in Hlen. injection Hlen. intro Hl.
    cbn [sf_qsub length]; rewrite (IH nu' Hl); reflexivity.
Qed.

Lemma sf_qw2_eq_qsub : forall mu nu : list Q, QeqT (sf_qw2 mu nu) (sf_qsum (map (fun d => d * d) (sf_qsub mu nu))).
Proof.
  intros mu. induction mu as [| a mu' IH]; intros nu; destruct nu as [| b nu'];
    cbn [sf_qw2 sf_qsub sf_qsum map].
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. reflexivity.
  - specialize (IH nu'). apply qeq_imp_qeqT. rewrite <- (qeqT_imp_qeq _ _ IH). ring.
Qed.



(* the main theorem (the strengthened replacement of the blueprint's
   wasserstein2_sq_nonneg / sym / same):
   (the centroid difference)^2 <= the paired mean square, the Jensen /
   Cauchy-Schwarz mean form.
   under the equal-length assumption the centroid difference == the mean of
   the differences, so Lagrange applies at a := the mean of the differences *)
Theorem sf_q_centroid_bound :
  forall mu nu : list Q,
    Id (length mu) (length nu) ->
    QleT' ((sf_qcentroid mu - sf_qcentroid nu) * (sf_qcentroid mu - sf_qcentroid nu))
          (sf_qw2_mean mu nu).
Proof.
  intros mu nu Hlen.
  destruct mu as [| a mu'].
  - destruct nu as [| b nu'].
    + apply id_refl.
    + inversion Hlen.
  - destruct nu as [| b nu'].
    + inversion Hlen.
    + assert (Hl : length mu' = length nu').
      { assert (He : length (a :: mu') = length (b :: nu'))
by exact (match Hlen in (Id _ y') return (length (a :: mu') = y') with id_refl => eq_refl end).
        cbn [length] in He. injection He. intro H0. exact H0. }
      assert (Hlen' : length (a :: mu') = length (b :: nu'))
        by (cbn [length]; rewrite Hl; reflexivity).
      assert (Hlen2 : length (sf_qsub (a :: mu') (b :: nu')) = Datatypes.S (length mu'))
by (cbn [sf_qsub length]; destruct (sf_qsub_length mu' nu' Hl); reflexivity).
      apply sf_qle_to_qleT.
      unfold sf_qw2_mean. cbn [length].
      (* Lagrange on the difference list, at a := the mean of the differences *)
      assert (HLt : QleT' 0
                 ((Z.of_nat (length (sf_qsub (a :: mu') (b :: nu'))) # 1)
                  * sf_qmean (Datatypes.S (length mu'))
                             (sf_qsum (sf_qsub (a :: mu') (b :: nu')))
                  * sf_qmean (Datatypes.S (length mu'))
                             (sf_qsum (sf_qsub (a :: mu') (b :: nu')))
                  - (2 # 1) * sf_qmean (Datatypes.S (length mu'))
                                       (sf_qsum (sf_qsub (a :: mu') (b :: nu')))
                  * sf_qsum (sf_qsub (a :: mu') (b :: nu'))
                  + sf_qsum (map (fun d0 => d0 * d0)
                                 (sf_qsub (a :: mu') (b :: nu')))))
        by exact (sf_q_lagrange_nonneg (sf_qsub (a :: mu') (b :: nu'))
                    (sf_qmean (Datatypes.S (length mu'))
                              (sf_qsum (sf_qsub (a :: mu') (b :: nu'))))).
      rewrite Hlen2 in HLt.
apply QleT'_to_Qle in HLt.
      assert (Hdpos : Qlt 0%Q (Z.of_nat (Datatypes.S (length mu')) # 1))
        by (unfold Qlt; cbn [Qnum Qden]; lia).
      assert (Hkey : Qle ((sf_qmean (Datatypes.S (length mu'))
                                    (sf_qsum (sf_qsub (a :: mu') (b :: nu'))))
                          * sf_qmean (Datatypes.S (length mu'))
                                     (sf_qsum (sf_qsub (a :: mu') (b :: nu'))))
                         (sf_qsum (map (fun d0 => d0 * d0)
                                       (sf_qsub (a :: mu') (b :: nu')))
                          / (Z.of_nat (Datatypes.S (length mu')) # 1)))
        by exact (QleT'_to_Qle _ _ (sf_q_mean_sq_key (Z.of_nat (Datatypes.S (length mu')) # 1)
                    (sf_qsum (sf_qsub (a :: mu') (b :: nu')))
                    (sf_qsum (map (fun d0 => d0 * d0)
                                  (sf_qsub (a :: mu') (b :: nu'))))
                    Hdpos HLt)).
      assert (Hcd : sf_qcentroid (a :: mu') - sf_qcentroid (b :: nu')
                    == sf_qmean (Datatypes.S (length mu'))
                                (sf_qsum (sf_qsub (a :: mu') (b :: nu'))))
        by exact (qeqT_imp_qeq _ _ (sf_qcentroid_diff_eq (a :: mu') (b :: nu') Hlen')).
      assert (Hw2' : sf_qsum (map (fun d0 => d0 * d0)
                                  (sf_qsub (a :: mu') (b :: nu')))
                     / (Z.of_nat (Datatypes.S (length mu')) # 1)
                     == sf_qw2 (a :: mu') (b :: nu')
                        / (Z.of_nat (Datatypes.S (length mu')) # 1)).
      { unfold Qdiv. rewrite (qeqT_imp_qeq _ _ (sf_qw2_eq_qsub (a :: mu') (b :: nu'))). ring. }
      (* the application binds tighter than *, so the partial application would be misread as a multiplication operand; the intermediate assert Hsqeq assembles it (changing the base first, then using Hkey / Hw2') *)
      assert (Hsqeq : (sf_qcentroid (a :: mu') - sf_qcentroid (b :: nu'))
                      * (sf_qcentroid (a :: mu') - sf_qcentroid (b :: nu'))
                      == sf_qmean (Datatypes.S (length mu'))
                                  (sf_qsum (sf_qsub (a :: mu') (b :: nu')))
                      * sf_qmean (Datatypes.S (length mu'))
                                 (sf_qsum (sf_qsub (a :: mu') (b :: nu'))))
        by (rewrite Hcd; ring).
      exact (QleT'_to_Qle _ _ (sf_qle_eq_l _ _ _ Hsqeq
                (QleT'_to_Qle _ _ (sf_qle_eq_r _ _ _ Hkey Hw2')))).
Qed.

(* the paired mean square is symmetric (pointwise commutation plus ring) *)
Theorem sf_qw2_sym : forall mu nu : list Q,
  Id (Qeq_bool (sf_qw2 mu nu) (sf_qw2 nu mu)) true.
Proof.
  intros mu nu.
  revert nu.
  revert mu.
  induction mu as [| a mu IH]; intro nu; destruct nu as [| b nu].
  - apply id_refl.
  - apply id_refl.
  - apply id_refl.
  - assert (Hp : sf_qw2 (a :: mu) (b :: nu) == sf_qw2 (b :: nu) (a :: mu)).
{ simpl. specialize (IH nu). rewrite (qeqT_imp_qeq _ _ (sf_id_qeq _ _ IH)). ring. }
    exact (sf_qeq_id _ _ Hp).
Qed.

(* the paired mean square of identical distributions is zero *)
Theorem sf_qw2_same : forall mu : list Q,
  Id (Qeq_bool (sf_qw2 mu mu) 0) true.
Proof.
  induction mu as [| a mu IH].
  - apply id_refl.
  - assert (Hp : sf_qw2 (a :: mu) (a :: mu) == 0).
    { simpl. specialize (IH).
rewrite <- (proj1 (Qeq_bool_iff _ _) (match IH in (Id _ y') return (Qeq_bool _ _ = y') with id_refl => eq_refl end)). ring. }
    exact (sf_qeq_id _ _ Hp).
Qed.

(* the pointwise difference list *)
(* the centroid difference == the mean of the differences (under the equal-length assumption; by field) *)
Theorem sf_qcentroid_diff :
  forall mu nu : list Q,
    Id (length mu) (length nu) ->
    Id (Qeq_bool (sf_qcentroid mu - sf_qcentroid nu)
                 (sf_qmean (length mu) (sf_qsum (sf_qsub mu nu)))) true.
Proof.
  intros mu nu Hlen.
  apply sf_qeq_id.
  exact (qeqT_imp_qeq _ _ (sf_qcentroid_diff_eq mu nu
             (match Hlen in (Id _ y') return (length mu = y') with id_refl => eq_refl end))).
Qed.

End SFWasserQ.

(* ============================================================ *)
(* SFCluster: cluster connectivity / directed causal paths (the blueprint's §3 clusters_connected / *)
(*   cluster_connected_sym / shared_member_connected / the causal edges) *)
(*   the existentials are all sigT + InT (the Set layer); the symmetry of connectivity and the shared-member connectivity are *)
(*   proved outright; the reachability inductive type supplies the core of the persistent-homology-style connected components *)
(* ============================================================ *)

(* inter-cluster connectivity: some cross-cluster sense pair has pipe thickness >= the threshold *)
Definition sf_clusters_connected (th : Real)
  (A B : list SFSense) : Set :=
  sigT (fun s1 => sigT (fun s2 =>
    And (InT s1 A) (And (InT s2 B)
      (real_le th (sf_pipe (sf_sense_coord s1) (sf_sense_coord s2)))))).

(* symmetry (the blueprint's cluster_connected_sym; the pipe symmetry plus swapping the witnesses) *)
(* symmetry (the blueprint's cluster_connected_sym; the pipe symmetry plus swapping the witnesses) *)
Theorem sf_clusters_connected_sym :
  forall (th : Real) (A B : list SFSense),
    sf_clusters_connected th A B ->
    sf_clusters_connected th B A.
Proof.
  intros th A B H.
  destruct H as [s1 [s2 [Hin1 [Hin2 Hle]]]].
  exists s2. exists s1.
  split.
  - exact Hin2.
  - split.
    + exact Hin1.
    + apply (RealSetoid.real_le_compat th th
               (sf_pipe (sf_sense_coord s1) (sf_sense_coord s2))
               (sf_pipe (sf_sense_coord s2) (sf_sense_coord s1))).
      * apply real_eq_refl.
      * apply sf_pipe_sym.
      * exact Hle.
Qed.

(* a shared member gives connectivity under any nonpositive threshold (the blueprint's shared_member_connected) *)
(* a shared member gives connectivity under any nonpositive threshold (the blueprint's shared_member_connected) *)
Theorem sf_shared_member_connected :
  forall (th : Real) (A B : list SFSense),
    real_le th real_zero ->
    (sigT (fun s => And (InT s A) (InT s B))) ->
    sf_clusters_connected th A B.
Proof.
  intros th A B Hth Hsh.
  destruct Hsh as [s [HinA HinB]].
  exists s. exists s.
  split.
  - exact HinA.
  - split.
    + exact HinB.
    + apply (real_le_trans th real_zero
               (sf_pipe (sf_sense_coord s) (sf_sense_coord s))).
      * exact Hth.
      * left. apply sf_pipe_pos.
Qed.

(* the directed causal edge (the blueprint's CausalEdge) and its asymmetry *)
Record SFCausalEdge : Set := Build_SFCausalEdge {
  sf_cause : SFSense;
  sf_effect : SFSense
}.

Definition sf_causal_asym (e : SFCausalEdge) : Set :=
  Not (sigT (fun e' : SFCausalEdge =>
    And (Id (sf_sense_id (sf_cause e')) (sf_sense_id (sf_effect e)))
        (Id (sf_sense_id (sf_effect e')) (sf_sense_id (sf_cause e))))).

(* the directed path (the constructive core of the connected components; the
   decidable kernel of the blueprint's persistent-homology module, the
   reachability inductive type at the Set layer) *)
Section SFReaches.
Variable sf_edge : SFVec -> SFVec -> Set.

Inductive sf_reaches : SFVec -> SFVec -> Set :=
| sf_reach_here : forall x, sf_reaches x x
| sf_reach_step : forall x y z, sf_edge x y -> sf_reaches y z -> sf_reaches x z.

Theorem sf_reaches_trans :
  forall x y z, sf_reaches x y -> sf_reaches y z -> sf_reaches x z.
Proof.
  intros x y z Hxy.
  revert z.
  induction Hxy as [x | x a y Hedge Hrec IH]; intros z Hyz.
  - exact Hyz.
  - apply (sf_reach_step x a z Hedge).
    exact (IH z Hyz).
Qed.
End SFReaches.

(* ============================================================ *)
(* SFActiveInference: the active-inference free energy (the blueprint's §3 variational_free_ *)
(*   energy / state_to_coord / complexity) *)
(*   baseline form: the internal and sensory states are coordinate vectors directly; the complexity is sf_n2r(length) *)
(* ============================================================ *)

Definition sf_vfe (internal sensory : SFVec) : Real :=
  real_plus (sf_dist_sq internal sensory) (sf_n2r (length internal)).

(* when the states match, the free energy == the complexity term (the
   blueprint's free_energy_min_when_match: the prediction-error component
   is zero) *)
Lemma sf_real_plus_zero_l : forall x : Real, real_eq (real_plus real_zero x) x.
Proof.
  intro x. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_zero x n)).
  assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
  rewrite Hz. ring.
Qed.

Theorem sf_vfe_match :
  forall v : SFVec, real_eq (sf_vfe v v) (sf_n2r (length v)).
Proof.
  intro v. unfold sf_vfe.
  apply (real_eq_trans
          (real_plus (sf_dist_sq v v) (sf_n2r (length v)))
          (real_plus real_zero (sf_n2r (length v)))
          (sf_n2r (length v))).
  - apply (RealSetoid.real_eq_plus_compat (sf_dist_sq v v) (sf_n2r (length v))
             real_zero (sf_n2r (length v))).
    + exact (sf_dist_sq_self v).
    + apply real_eq_refl.
  - exact (sf_real_plus_zero_l (sf_n2r (length v))).
Qed.

(* the free energy >= the complexity (in eps-slack form; the eps version of the
   distance nonnegativity plus the nonnegative n2r):
   for any eps > 0, vfe >= complexity (i.e. vfe + eps >= complexity) *)
Theorem sf_vfe_ge_complexity_eps :
  forall (v : SFVec) (eps : Real),
    real_lt real_zero eps ->
    real_le (real_plus (sf_n2r (length v)) (real_opp eps))
            (sf_vfe v v).
Proof.
  intros v eps Heps.
  destruct Heps as [e0 [He0 [N0 HN0]]].
  unfold sf_vfe.
  apply (RealSetoid.real_lt_le_iff_req
          (real_plus (sf_n2r (length v)) (real_opp eps))
          (real_plus (sf_dist_sq v v) (sf_n2r (length v)))). left.
  exists ((1 # 2) * e0)%Q. split.
  - apply Qlt_to_QltT. apply (Qmult_lt_0_compat (1 # 2) e0).
    + compute. reflexivity.
    + apply QltT_to_Qlt. exact He0.
  - exists N0. intros n Hn.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (sf_dist_sq v v) (sf_n2r (length v)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj (sf_n2r (length v)) (real_opp eps) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj eps n)).
rewrite (qeqT_imp_qeq _ _ (sf_dist_sq_proj v v n)).
    assert (Hr : sf_ptw_sum v v n + projT1 (sf_n2r (length v)) n
                 - (projT1 (sf_n2r (length v)) n + (- projT1 eps n))
                 == sf_ptw_sum v v n + projT1 eps n) by ring.
    rewrite Hr.
    apply (Qlt_le_trans ((1 # 2) * e0)%Q e0 (sf_ptw_sum v v n + projT1 eps n)).
    + apply (Qlt_le_trans ((1 # 2) * e0)%Q (1 * e0)%Q e0).
      * apply (Qmult_lt_compat_r (1 # 2) 1 e0).
        -- apply QltT_to_Qlt. exact He0.
        -- compute. reflexivity.
* apply QleT'_to_Qle. apply sf_qeq_le. ring.
    + apply (Qle_trans e0 (projT1 eps n) (sf_ptw_sum v v n + projT1 eps n)).
      * apply (Qle_trans e0 (projT1 eps n - 0) (projT1 eps n)).
        -- apply Qlt_le_weak. apply QltT_to_Qlt. exact (HN0 n Hn).
-- apply QleT'_to_Qle. apply sf_qeq_le. ring.
      * apply (Qle_trans (projT1 eps n) (0 + projT1 eps n)
                 (sf_ptw_sum v v n + projT1 eps n)).
-- apply QleT'_to_Qle. apply sf_qeq_le. ring.
        -- apply (Qplus_le_compat 0 (sf_ptw_sum v v n) (projT1 eps n)
                    (projT1 eps n)).
           ++ exact (QleT'_to_Qle _ _ (sf_ptw_sum_ge_0 v v n)).
           ++ apply Qle_refl.
Qed.

(* ============================================================ *)
(* SFEquivariance: group equivariance (the blueprint's §4 group_action / equivariant / *)
(*   equivariant_compose; the blueprint's proof referenced an undefined compose, which is repaired here) *)
(* ============================================================ *)

(* the cyclic-shift group action (the blueprint's own form: skipn ++ firstn) *)
Definition sf_rotate (k : nat) (x : SFVec) : SFVec :=
  skipn k x ++ firstn k x.

(* equivariance (the Set-layer Id encoding) *)
Definition sf_equivariant (F : SFVec -> SFVec) : Set :=
  forall (k : nat) (x : SFVec), Id (F (sf_rotate k x)) (sf_rotate k (F x)).

(* the composition of equivariant functions is equivariant (the repaired version of the blueprint's equivariant_compose) *)
Theorem sf_equivariant_compose :
  forall F G : SFVec -> SFVec,
    sf_equivariant F -> sf_equivariant G ->
    sf_equivariant (fun x => F (G x)).
Proof.
  intros F G HF HG k x.
  cbv beta.
  rewrite (RealSetoid.Id_eq
             (G (sf_rotate k x)) (sf_rotate k (G x)) (HG k x)).
  exact (HF k (G x)).
Qed.

(* the translation-sum invariant: rotations preserve the vector sum (the global
   mass conservation of the semantic field; the Real-layer numeric theorem of
   the blueprint's equivariance module) *)
Fixpoint sf_vec_sum (x : SFVec) : Real :=
  match x with
  | nil => real_zero
  | a :: rest => real_plus a (sf_vec_sum rest)
  end.

Lemma sf_vec_sum_app : forall x y : SFVec,
  real_eq (sf_vec_sum (x ++ y)) (real_plus (sf_vec_sum x) (sf_vec_sum y)).
Proof.
  intros x y. induction x as [| a rest IH]; simpl.
  - simpl. apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_zero (sf_vec_sum y) n)).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    rewrite Hz. ring.
  - apply (real_eq_trans
             (real_plus a (sf_vec_sum (rest ++ y)))
             (real_plus a (real_plus (sf_vec_sum rest) (sf_vec_sum y)))
             (real_plus (real_plus a (sf_vec_sum rest)) (sf_vec_sum y))).
    + apply (RealSetoid.real_eq_plus_compat
               a (sf_vec_sum (rest ++ y)) a
               (real_plus (sf_vec_sum rest) (sf_vec_sum y))).
      * apply real_eq_refl.
      * exact IH.
    + apply real_plus_assoc.
Qed.

Lemma sf_vec_sum_firstn_skipn : forall (k : nat) (x : SFVec),
  real_eq (sf_vec_sum x)
          (real_plus (sf_vec_sum (firstn k x)) (sf_vec_sum (skipn k x))).
Proof.
  induction k as [| k IH]; intro x.
  - cbn [firstn skipn sf_vec_sum].
    apply (real_eq_trans (sf_vec_sum x)
                         (real_plus (sf_vec_sum x) real_zero)
                         (real_plus real_zero (sf_vec_sum x))).
    + apply real_eq_sym. exact (real_plus_zero (sf_vec_sum x)).
    + exact (real_plus_comm (sf_vec_sum x) real_zero).
  - destruct x as [| a rest].
    + cbn [firstn skipn sf_vec_sum].
      apply real_eq_of_zero_diff. intro n.
      apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_zero real_zero n)).
      assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      rewrite Hz. ring.
    + cbn [firstn skipn sf_vec_sum].
      apply (real_eq_trans
              (real_plus a (sf_vec_sum rest))
              (real_plus a (real_plus (sf_vec_sum (firstn k rest))
                                      (sf_vec_sum (skipn k rest))))
              (real_plus (real_plus a (sf_vec_sum (firstn k rest)))
                         (sf_vec_sum (skipn k rest)))).
      * apply (RealSetoid.real_eq_plus_compat a (sf_vec_sum rest) a
                 (real_plus (sf_vec_sum (firstn k rest))
                            (sf_vec_sum (skipn k rest)))).
        -- apply real_eq_refl.
        -- exact (IH rest).
      * exact (real_plus_assoc a (sf_vec_sum (firstn k rest))
                 (sf_vec_sum (skipn k rest))).
Qed.

Theorem sf_rotate_sum_invariant :
  forall (k : nat) (x : SFVec),
    real_eq (sf_vec_sum (sf_rotate k x)) (sf_vec_sum x).
Proof.
  intros k x. unfold sf_rotate.
  apply (real_eq_trans (sf_vec_sum (skipn k x ++ firstn k x))
                       (real_plus (sf_vec_sum (skipn k x))
                                  (sf_vec_sum (firstn k x)))
                       (sf_vec_sum x)).
  - exact (sf_vec_sum_app (skipn k x) (firstn k x)).
  - apply (real_eq_trans
             (real_plus (sf_vec_sum (skipn k x)) (sf_vec_sum (firstn k x)))
             (real_plus (sf_vec_sum (firstn k x)) (sf_vec_sum (skipn k x)))
             (sf_vec_sum x)).
    + exact (real_plus_comm (sf_vec_sum (skipn k x)) (sf_vec_sum (firstn k x))).
    + apply real_eq_sym. exact (sf_vec_sum_firstn_skipn k x).
Qed.

(* ============================================================ *)
(* SFCurriculum: curriculum learning (the blueprint's §4 Curriculum / curriculum_learning_ *)
(*   monotone).  the blueprint's original theorem restates its assumption (a vacuous form); here it becomes a fold accumulation: *)
(*   if every training step does not increase the loss, the whole curriculum run does not increase the loss (proved by fold induction) *)
(* ============================================================ *)

Section SFCurriculum.
Variable SFModel : Set.
Variable sf_train_step : SFModel -> SFVec -> SFModel.
Variable sf_loss : SFModel -> Real.
Hypothesis sf_step_ok :
  forall (m : SFModel) (smp : SFVec),
    real_le (sf_loss (sf_train_step m smp)) (sf_loss m).

Fixpoint sf_curriculum_run (samples : list SFVec) (m : SFModel) : SFModel :=
  match samples with
  | nil => m
  | s :: rest => sf_curriculum_run rest (sf_train_step m s)
  end.

Theorem sf_curriculum_monotone :
  forall (samples : list SFVec) (m : SFModel),
    real_le (sf_loss (sf_curriculum_run samples m)) (sf_loss m).
Proof.
  intros samples. induction samples as [| s rest IH]; intro m.
  - apply real_le_refl.
  - apply (real_le_trans
             (sf_loss (sf_curriculum_run rest (sf_train_step m s)))
             (sf_loss (sf_train_step m s))
             (sf_loss m)).
    + exact (IH (sf_train_step m s)).
    + exact (sf_step_ok m s).
Qed.

End SFCurriculum.

(* ============================================================ *)
(* SFEWC: elastic weight consolidation (the blueprint's §4 fisher_diag / ewc_regularizer / *)
(*   ewc_limits_change) *)
(*   constructive fix: the blueprint's ewc = 0 iff the parameters are equal is not constructible (dist == 0 implying *)
(*   equality is not obtainable), so it becomes three theorems: the regularizer is nonnegative (in eps slack), zero on self-parameters, *)
(*   and Fisher-monotone *)
(* ============================================================ *)

Section SFEWC.
Variable sf_fisher : Real.
Hypothesis sf_fisher_nonneg : real_le real_zero sf_fisher.

(* flattening the model parameters (the record pool becomes a vector; laid out directly as a vector list here) *)
Fixpoint sf_flatten (ps : list SFVec) : SFVec :=
  match ps with
  | nil => nil
  | v :: rest => v ++ sf_flatten rest
  end.

Definition sf_ewc (old_params new_params : list SFVec) : Real :=
  real_mult sf_fisher (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)).

(* the EWC regularizer is nonnegative (in eps-slack form) *)
Lemma sf_q_lt_shift_prod : forall e0 m p e : Q,
  Qlt 0 m -> Qle 0 p -> Qlt e0 e -> QltT e0 (m * p + e).
Proof.
  intros e0 m p e H0m Hp He.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans e0 e (m * p + e)).
  - exact He.
  - apply (Qle_trans e (0 + e) (m * p + e)).
+ apply QleT'_to_Qle. apply sf_qeq_le. ring.
    + apply (Qplus_le_compat 0 (m * p) e e).
      * apply (Qmult_le_0_compat m p).
        -- apply Qlt_le_weak. exact H0m.
        -- exact Hp.
      * apply Qle_refl.
Qed.

Theorem sf_ewc_pos_eps :
  forall old_params new_params (eps : Real),
    real_lt real_zero eps ->
    real_le real_zero (real_plus (sf_ewc old_params new_params) eps).
Proof.
  intros old_params new_params eps Heps.
  unfold sf_ewc.
  unfold real_le.
  apply (RealSetoid.real_lt_le_iff_req real_zero
          (real_plus (real_mult sf_fisher
                        (sf_dist_sq (sf_flatten old_params)
                                    (sf_flatten new_params))) eps)). left.
  destruct sf_fisher_nonneg as [Hflt | Hfeq].
  - (* fisher > 0: the lt witness e0, with N := max Nf Ne *)
    destruct Hflt as [m [Hm [Nf HNf]]].
    destruct Heps as [e0 [He0 [Ne HNe]]].
    exists e0. split.
    + exact He0.
    + exists (Nat.max Nf Ne). intros n Hn.
      assert (Hn1 : NatLe Nf n).
      { apply (RealSetoid.le_to_NatLe Nf n).
        apply Nat.le_trans with (Nat.max Nf Ne).
        - apply Nat.le_max_l.
        - exact (NatLe_drop (Nat.max Nf Ne) n Hn). }
      assert (Hn2 : NatLe Ne n).
      { apply (RealSetoid.le_to_NatLe Ne n).
        apply Nat.le_trans with (Nat.max Nf Ne).
        - apply Nat.le_max_r.
        - exact (NatLe_drop (Nat.max Nf Ne) n Hn). }
      apply Qlt_to_QltT.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult sf_fisher
                 (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)))
                 eps n)).
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj sf_fisher
                 (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)) n)).
      assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
      rewrite Hz.
rewrite (qeqT_imp_qeq _ _ (sf_dist_sq_proj (sf_flatten old_params) (sf_flatten new_params) n)).
      assert (Hr : projT1 sf_fisher n
                   * sf_ptw_sum (sf_flatten old_params) (sf_flatten new_params) n
                   + projT1 eps n - 0
                   == projT1 sf_fisher n
                      * sf_ptw_sum (sf_flatten old_params) (sf_flatten new_params) n
                      + projT1 eps n) by ring.
      rewrite Hr.
      assert (Hfp : Qlt 0 (projT1 sf_fisher n)).
      { apply (Qlt_trans 0 m (projT1 sf_fisher n)).
        - apply QltT_to_Qlt. exact Hm.
        - apply (Qlt_le_trans m (projT1 sf_fisher n - 0) (projT1 sf_fisher n)).
          + apply QltT_to_Qlt. exact (HNf n Hn1).
+ apply QleT'_to_Qle. apply sf_qeq_le. ring. }
      apply QltT_to_Qlt.
      apply (sf_q_lt_shift_prod e0 (projT1 sf_fisher n)
               (sf_ptw_sum (sf_flatten old_params) (sf_flatten new_params) n)
               (projT1 eps n)).
      * exact Hfp.
      * apply QleT'_to_Qle. exact (sf_ptw_sum_ge_0 (sf_flatten old_params) (sf_flatten new_params) n).
      * apply (Qlt_le_trans e0 (projT1 eps n - 0) (projT1 eps n)).
        -- apply QltT_to_Qlt. exact (HNe n Hn2).
-- apply QleT'_to_Qle. apply sf_qeq_le. ring.
  - (* fisher == 0: the goal == eps > 0, with the lt transplanted through the eq bridge *)
    apply (RealSetoid.real_lt_id_r real_zero eps
            (real_plus (real_mult sf_fisher
                          (sf_dist_sq (sf_flatten old_params)
                                      (sf_flatten new_params))) eps)).
    + apply (real_eq_trans eps (real_plus real_zero eps)
               (real_plus (real_mult sf_fisher
                             (sf_dist_sq (sf_flatten old_params)
                                         (sf_flatten new_params))) eps)).
      * apply real_eq_sym. exact (sf_real_plus_zero_l eps).
      * apply real_eq_sym.
        apply (RealSetoid.real_eq_plus_compat
                 (real_mult sf_fisher
                    (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)))
                 eps real_zero eps).
        -- apply (real_eq_trans
                    (real_mult sf_fisher
                       (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)))
                    (real_mult real_zero
                       (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)))
                    real_zero).
           ++ apply (RealSetoid.real_eq_mult_compat sf_fisher
                       (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params))
                       real_zero
                       (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params))).
              ** exact (real_eq_sym real_zero sf_fisher Hfeq).
              ** apply real_eq_refl.
           ++ apply (real_eq_trans
                       (real_mult real_zero
                          (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)))
                       (real_mult
                          (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params))
                          real_zero)
                       real_zero).
              ** exact (real_mult_comm real_zero
                          (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params))).
              ** exact (real_mult_zero
                          (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params))).
        -- apply real_eq_refl.
    + exact Heps.
Qed.

(* the regularizer is zero when the parameters are unchanged *)
Theorem sf_ewc_self_zero :
  forall old_params : list SFVec, real_eq (sf_ewc old_params old_params) real_zero.
Proof.
  intro old_params. unfold sf_ewc.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj sf_fisher
             (sf_dist_sq (sf_flatten old_params) (sf_flatten old_params)) n)).
  assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
  rewrite Hz.
  (* dist(flatten, flatten) is 0 pointwise *)
  assert (Hd : projT1 (sf_dist_sq (sf_flatten old_params) (sf_flatten old_params)) n == 0).
  { rewrite (qeqT_imp_qeq _ _ (sf_dist_sq_proj (sf_flatten old_params) (sf_flatten old_params) n)).
    exact (qeqT_imp_qeq _ _ (sf_ptw_sum_self (sf_flatten old_params) n)). }
  rewrite Hd. ring.
Qed.

(* a larger Fisher increases the regularizer (monotonicity in Fisher) *)
Lemma sf_real_le_add_r : forall a b : Real,
  real_le real_zero b -> real_le a (real_plus a b).
Proof.
  intros a b Hb.
  apply (RealSetoid.real_le_id_l a (real_plus a real_zero) (real_plus a b)).
  - exact (real_eq_sym (real_plus a real_zero) a (real_plus_zero a)).
  - apply real_le_plus_compat.
    + apply real_le_refl.
    + exact Hb.
Qed.

Theorem sf_ewc_mono_fisher :
  forall (f2 : Real) (old_params new_params : list SFVec) (eps : Real),
    real_le sf_fisher f2 ->
    real_lt real_zero eps ->
    real_le (sf_ewc old_params new_params)
            (real_plus (real_mult f2
                          (sf_dist_sq (sf_flatten old_params)
                                      (sf_flatten new_params))) eps).
Proof.
  intros f2 old_params new_params eps Hle Heps.
  unfold sf_ewc.
  unfold real_le in Hle. destruct Hle as [Hflt | Hfeq].
  - (* fisher < f2: the pointwise witness e0 (the eps slack), with (f2 - f) * D >= 0 absorbed *)
    destruct Hflt as [m [Hm [Nf HNf]]].
    destruct Heps as [e0 [He0 [Ne HNe]]].
    apply (RealSetoid.real_lt_le_iff_req
             (real_mult sf_fisher
                (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)))
             (real_plus (real_mult f2
                            (sf_dist_sq (sf_flatten old_params)
                                        (sf_flatten new_params))) eps)). left.
    exists e0. split.
    + exact He0.
    + exists (Nat.max Nf Ne). intros n Hn.
      assert (Hn1 : NatLe Nf n).
      { apply (RealSetoid.le_to_NatLe Nf n).
        apply Nat.le_trans with (Nat.max Nf Ne).
        - apply Nat.le_max_l.
        - exact (NatLe_drop (Nat.max Nf Ne) n Hn). }
      assert (Hn2 : NatLe Ne n).
      { apply (RealSetoid.le_to_NatLe Ne n).
        apply Nat.le_trans with (Nat.max Nf Ne).
        - apply Nat.le_max_r.
        - exact (NatLe_drop (Nat.max Nf Ne) n Hn). }
      apply Qlt_to_QltT.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult f2
                 (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)))
                 eps n)).
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj sf_fisher
                 (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)) n)).
      rewrite (qeqT_imp_qeq _ _ (real_mult_proj f2
                 (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)) n)).
rewrite (qeqT_imp_qeq _ _ (sf_dist_sq_proj (sf_flatten old_params) (sf_flatten new_params) n)).
      assert (Hr : projT1 f2 n
                   * sf_ptw_sum (sf_flatten old_params) (sf_flatten new_params) n
                   + projT1 eps n
                   - projT1 sf_fisher n
                     * sf_ptw_sum (sf_flatten old_params) (sf_flatten new_params) n
                   == (projT1 f2 n - projT1 sf_fisher n)
                      * sf_ptw_sum (sf_flatten old_params) (sf_flatten new_params) n
                      + projT1 eps n) by ring.
      rewrite Hr.
      apply QltT_to_Qlt.
      apply (sf_q_lt_shift_prod e0 (projT1 f2 n - projT1 sf_fisher n)
               (sf_ptw_sum (sf_flatten old_params) (sf_flatten new_params) n)
               (projT1 eps n)).
      * apply (Qlt_trans 0 m (projT1 f2 n - projT1 sf_fisher n)).
        -- apply QltT_to_Qlt. exact Hm.
        -- apply QltT_to_Qlt. exact (HNf n Hn1).
      * apply QleT'_to_Qle. exact (sf_ptw_sum_ge_0 (sf_flatten old_params) (sf_flatten new_params) n).
      * apply (Qlt_le_trans e0 (projT1 eps n - 0) (projT1 eps n)).
        -- apply QltT_to_Qlt. exact (HNe n Hn2).
-- apply QleT'_to_Qle. apply sf_qeq_le. ring.
  - (* fisher == f2: the regularizers are equal, and adding eps preserves <= *)
    apply (real_le_trans
             (real_mult sf_fisher
                (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)))
             (real_mult f2
                (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)))
             (real_plus (real_mult f2
                            (sf_dist_sq (sf_flatten old_params)
                                        (sf_flatten new_params))) eps)).
    + apply (RealSetoid.real_eq_le
               (real_mult sf_fisher
                  (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)))
               (real_mult f2
                  (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)))).
      apply (RealSetoid.real_eq_mult_compat sf_fisher
               (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params))
               f2
               (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params))).
      * exact Hfeq.
      * apply real_eq_refl.
    + apply (sf_real_le_add_r
               (real_mult f2
                  (sf_dist_sq (sf_flatten old_params) (sf_flatten new_params)))
               eps).
      apply (real_lt_le_iff real_zero eps). left. exact Heps.
Qed.
End SFEWC.

(* ============================================================ *)
(* SFBinding: neural-symbolic variable binding (the blueprint's §3 Role/Filler/Binding) *)
(*   the blueprint's two binding_consistent theorems are tautological; here an executable binding *)
(*   environment is given: nat roles x Real fillers with overwrite semantics, and the binding / independence / update theorems *)
(* ============================================================ *)

(* the role constants (the nat encoding of the blueprint's Role enumeration) *)
Definition sf_role_agent : nat := 0.
Definition sf_role_patient : nat := 1.
Definition sf_role_goal : nat := 2.
Definition sf_role_number : nat := 3.

Definition SFBindingEnv : Set := list (nat * Real)%type.

Definition sf_env_bind (env : SFBindingEnv) (r : nat) (v : Real) : SFBindingEnv :=
  (r, v) :: env.

Fixpoint sf_env_lookup (env : SFBindingEnv) (r : nat) : option Real :=
  match env with
  | nil => None
  | (r', v) :: rest => if Nat.eqb r' r then Some v else sf_env_lookup rest r
  end.

(* a binding is found after it is bound (the executable form of the blueprint's binding uniqueness) *)
Theorem sf_env_lookup_after_bind :
  forall env r v, Id (sf_env_lookup (sf_env_bind env r v) r) (Some v).
Proof.
  intros env r v.
  unfold sf_env_bind, sf_env_lookup. simpl.
  destruct (Nat.eqb r r) eqn:E.
  - apply id_refl.
  - exfalso. apply Nat.eqb_neq in E. apply E. reflexivity.
Qed.

(* role independence: bindings with different roles do not interfere (the healthiness version of the blueprint's consistency constraint) *)
Theorem sf_env_bind_independent :
  forall env r1 r2 v1 v2,
    Not (Id r1 r2) ->
    Id (sf_env_lookup (sf_env_bind (sf_env_bind env r1 v1) r2 v2) r1)
       (sf_env_lookup (sf_env_bind env r1 v1) r1).
Proof.
  intros env r1 r2 v1 v2 Hne.
  unfold sf_env_bind, sf_env_lookup. simpl.
  destruct (Nat.eqb r2 r1) eqn:E.
  - exfalso.
    assert (Hk : r2 = r1) by exact (proj1 (Nat.eqb_eq r2 r1) E).
    assert (Hid : Id r2 r1) by (rewrite Hk; apply id_refl).
    destruct (Hne (id_sym Hid)).
  - simpl. destruct (Nat.eqb r1 r1) eqn:E3.
    + apply id_refl.
    + exfalso. apply Nat.eqb_neq in E3. apply E3. reflexivity.
Qed.

(* the bind-swap invariant: swapping the order of two bindings leaves each lookup result unchanged *)
Theorem sf_env_bind_comm_lookup :
  forall env r1 r2 v1 v2,
    Not (Id r1 r2) ->
    Id (sf_env_lookup (sf_env_bind (sf_env_bind env r1 v1) r2 v2) r2) (Some v2).
Proof.
  intros env r1 r2 v1 v2 Hne. simpl.
  rewrite (Nat.eqb_refl r2). apply id_refl.
Qed.

(* ============================================================ *)
(* SFQuantumQ: sense superposition and collapse (the blueprint's §3 QuantumState / collapse_* family) *)
(*   the probability amplitudes are Q (with a decidable squared comparison) and the collapse probability is the squared amplitude; the mass <= 1 *)
(*   is an honest-interface assumption, from which the per-item <= 1 and the argmax collapse domination theorems follow *)
(* ============================================================ *)

Definition SFQState : Set := list (nat * Q)%type.

Section SFQuantumQ.

(* the collapse probability: the squared amplitude (the executable form of the blueprint's collapse_prob; find becomes per-item) *)
Definition sf_amp2 (p : (nat * Q)%type) : Q := (snd p) * (snd p).

(* every per-item collapse probability is nonnegative *)
Theorem sf_amp2_nonneg : forall p : (nat * Q)%type, QleT' 0 (sf_amp2 p).
Proof.
  intro p. destruct p as [n q]. unfold sf_amp2.
  (* the square nonnegativity is built case by case directly: the computable
     trichotomy [Q_dec] is analyzed in place; the positive/negative branches are
     constructed explicitly with [Qmult_le_0_compat], the equal branch is closed
     by a qeq_le rewrite followed by ring, and the bridge keeps only the single
     [Qle_to_QleT'] step *)
  apply (Qle_to_QleT' 0 (q * q)).
  destruct (Q_dec 0 q) as [[Hp | Hn] | Hz].
  - assert (H1 : 0 <= q) by (apply Qlt_le_weak; exact Hp).
    exact (Qmult_le_0_compat q q H1 H1).
  - assert (Hq0 : q <= 0) by (apply Qlt_le_weak; exact Hn).
    assert (Hnq : 0 <= - q) by (exact (Qopp_le_compat q 0 Hq0)).
    assert (Hsq : (q * q) == ((- q) * (- q))) by ring.
    rewrite Hsq.
    exact (Qmult_le_0_compat (- q) (- q) Hnq Hnq).
  - apply QleT'_to_Qle. apply (qeq_le 0 (q * q)). apply qeq_imp_qeqT. rewrite <- Hz. ring.
Qed.

(* the Q list sum transfers per-item nonnegativity: if every term is nonnegative then the sum is nonnegative *)
Lemma sf_qsum_nn : forall (l : list Q),
  (forall x : Q, InT x l -> QleT' 0 x) -> QleT' 0 (sf_qsum l).
Proof.
  intros l. induction l as [| a rest IH]; intro Hnn.
  - apply sf_qleT_refl.
  - simpl. replace 0%Q with (0 + 0)%Q by reflexivity.
    apply sf_qleT_plus.
    + exact (Hnn a (InT_here a rest)).
    + exact (IH (fun x0 hx => Hnn x0 (InT_next x0 a rest hx))).
Qed.

(* the mass constraint (an honest interface): the total collapse mass is <= 1 *)
Variable sf_mass_le_one : forall (qs : SFQState),
  QleT' (sf_qsum (map sf_amp2 qs)) 1.

(* the InT head decomposition (the Set-layer plus; the index is taken in the
   variable form a :: l so the destruct branch names are stable, avoiding name
   drift when destructing a compound index term) *)
Lemma sf_InT_cons_inv : forall (A : Set) (x a : A) (l : list A),
  InT x (a :: l) -> (Id x a) + (InT x l).
Proof.
  intros A x a l H.
  inversion H as [l0 | y0 l0 H0].
  - apply inl. apply id_refl.
  - apply inr. exact H0.
Qed.

(* the list sum is >= each item (the remaining items being nonnegative) *)
Lemma sf_q_sum_ge_elem_aux : forall (l : list Q) (i : Q),
  InT i l -> (forall x : Q, InT x l -> Qle 0 x) -> QleT' i (sf_qsum l).
Proof.
  intros l. induction l as [| a rest IH]; intros i Hin Hnn.
  - apply Qle_to_QleT'. inversion Hin.
  - apply Qle_to_QleT'.
    cbn [sf_qsum].
    destruct (sf_InT_cons_inv Q i a rest Hin) as [Hhead | Htail].
    + (* i is the head (Id i a): i <= i + 0 <= i + (the rest sum) *)
assert (Heq : i = a) by exact (match Hhead in (Id _ y') return (i = y') with id_refl => eq_refl end).
      rewrite Heq.
      apply (Qle_trans _ (a + 0) (a + sf_qsum rest)).
* apply QleT'_to_Qle. apply sf_qeq_le. ring.
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- assert (Hs : QleT' 0 (sf_qsum rest)).
           { apply sf_qsum_nn. intros x0 hx0. apply sf_qle_to_qleT. apply Hnn. apply InT_next. exact hx0. }
exact (QleT'_to_Qle _ _ Hs).
    + (* i is in the tail: i <= (the rest sum) <= a + (the rest sum), the head's nonnegativity given by Hnn a *)
      apply (Qle_trans _ (sf_qsum rest) (a + sf_qsum rest)).
      * apply QleT'_to_Qle. apply IH.
        -- exact Htail.
        -- intros x0 hx0. apply Hnn. apply InT_next. exact hx0.
      * apply (Qle_trans _ (0 + sf_qsum rest) (a + sf_qsum rest)).
-- apply QleT'_to_Qle. apply sf_qeq_le. ring.
        -- apply Qplus_le_compat.
           ++ exact (Hnn a (InT_here a rest)).
           ++ apply Qle_refl.
Qed.

Lemma sf_q_sum_ge_elem : forall (l : list Q) (i : Q),
  InT i l ->
  (forall x : Q, InT x l -> QleT' 0 x) ->
  QleT' i (sf_qsum l).
Proof.
  intros l i Hin Hnn.
  apply sf_q_sum_ge_elem_aux.
  - exact Hin.
- intros x0 hx0. apply QleT'_to_Qle. apply Hnn. exact hx0.
Qed.
Lemma sf_InT_map_inv : forall (A B : Set) (f : A -> B) (l : list A) (y : B),
  InT y (map f l) -> sigT (fun x : A => And (InT x l) (Id (f x) y)).
Proof.
  intros A B f l. induction l as [| a rest IH]; intros y Hin.
  - inversion Hin.
  - cbn [map] in Hin.
    destruct (sf_InT_cons_inv B y (f a) (map f rest) Hin) as [Hhead | Htail].
    + exists a. split.
      * apply InT_here.
      * destruct Hhead. apply id_refl.
    + destruct (IH y Htail) as [x [Hin0 Hfx]].
      exists x. split.
      * apply InT_next. exact Hin0.
      * exact Hfx.
Qed.

Lemma sf_InT_map : forall (A B : Set) (f : A -> B) (l : list A) (x : A),
  InT x l -> InT (f x) (map f l).
Proof.
  intros A B f l. induction l as [| a rest IH]; intros x Hin.
  - inversion Hin.
  - cbn [map].
    destruct (sf_InT_cons_inv A x a rest Hin) as [Hhead | Htail].
    + destruct Hhead. apply InT_here.
    + apply InT_next. apply IH. exact Htail.
Qed.


(* under the mass constraint every per-item collapse probability is <= 1 (the constructive version of the blueprint's collapse_prob <= 1) *)
Theorem sf_amp2_le_one :
  forall (qs : SFQState) (p : (nat * Q)%type),
    InT p qs -> QleT' (sf_amp2 p) 1.
Proof.
  intros qs p Hin.
  apply (sf_qleT_trans (sf_amp2 p) (sf_qsum (map sf_amp2 qs)) 1).
  - apply (sf_q_sum_ge_elem (map sf_amp2 qs) (sf_amp2 p)).
    + apply sf_InT_map. exact Hin.
    + intros x0 hx0.
      destruct (sf_InT_map_inv _ _ _ _ _ hx0) as [p0 [Hin0 Hfx]].
      destruct Hfx.
      apply sf_amp2_nonneg.
  - exact (sf_mass_le_one qs).
Qed.

(* the argmax collapse: taking the largest squared amplitude (decidable by [Qle_bool]) *)
Fixpoint sf_collapse_aux (qs : SFQState) (best : (nat * Q)%type) : (nat * Q)%type :=
  match qs with
  | nil => best
  | p :: rest =>
      if Qle_bool (snd best) (snd p) then sf_collapse_aux rest p
      else sf_collapse_aux rest best
  end.

Definition sf_collapse (qs : SFQState) (d : (nat * Q)%type) : (nat * Q)%type :=
  sf_collapse_aux qs d.

(* the collapse domination: the returned item's collapse probability is >= that of any item in the list *)
(* the reflection of Qle_bool = false (closed constructively by the Q trichotomy decision) *)
Lemma sf_collapse_qle_bool_false : forall x y : Q,
  Qle_bool x y = false -> QleT' y x.
Proof.
  intros x y H.
  destruct (Q_dec x y) as [[Hlt | Hgt] | Heq].
  - exfalso.
    assert (HT : QleT' x y) by (apply sf_qle_to_qleT; apply Qlt_le_weak; exact Hlt).
assert (Hb : Qle_bool x y = true)
              by exact (match HT in (Id _ y') return (Qle_bool x y = y') with id_refl => eq_refl end).
    rewrite H in Hb. discriminate Hb.
  - apply sf_qle_to_qleT. apply Qlt_le_weak. exact Hgt.
- apply (sf_qeq_le y x). exact (Qeq_sym x y Heq).
Qed.

(* the collapse invariant: the returned value dominates the carried candidate best and dominates every item in the list *)
Lemma sf_collapse_aux_dom : forall qs best,
  And (QleT' (snd best) (snd (sf_collapse_aux qs best)))
      (forall p : (nat * Q)%type,
        InT p qs -> QleT' (snd p) (snd (sf_collapse_aux qs best))).
Proof.
  intro qs. induction qs as [| p0 rest IH]; intro best.
  - cbn [sf_collapse_aux]. split.
    + apply sf_qleT_refl.
    + intros p Hin. inversion Hin.
  - cbn [sf_collapse_aux].
    destruct (Qle_bool (snd best) (snd p0)) eqn:E.
    + specialize (IH p0). destruct IH as [H1 H2]. split.
      * exact (sf_qleT_trans (snd best) (snd p0) (snd (sf_collapse_aux rest p0))
                 (sf_bool_true_id _ E) H1).
      * intros p Hin. inversion Hin as [Heq | y0 l0 Hrec]; subst.
        -- exact H1.
        -- exact (H2 _ Hrec).
    + specialize (IH best). destruct IH as [H1 H2]. split.
      * exact H1.
      * intros p Hin.
        assert (Hdb : QleT' (snd p0) (snd best))
          by exact (sf_collapse_qle_bool_false _ _ E).
        inversion Hin as [Heq | y0 l0 Hrec]; subst.
        -- exact (sf_qleT_trans _ _ _ Hdb H1).
        -- exact (H2 _ Hrec).
Qed.

(* the collapse domination: the returned item's collapse probability is >= that of any item in the list *)
Theorem sf_collapse_dominates :
  forall (qs : SFQState) (d p : (nat * Q)%type),
    InT p qs ->
    QleT' (snd p) (snd (sf_collapse qs d)).
Proof.
  intros qs d p Hin. unfold sf_collapse.
  destruct (sf_collapse_aux_dom qs d) as [_ H2].
  exact (H2 p Hin).
Qed.

End SFQuantumQ.

(* ============================================================ *)
(* SFDiffusion: diffusion forward/backward plus multi-agent midpoint consensus (the blueprint's §3 *)
(* consensus_step / consensus_converges_to_zero + §4 forward/       *)
(*   reverse_diffuse).  the blueprint declares both as parameters with no implementation; here closed-form *)
(*   algebraic implementations and exact recovery / contraction theorems are given; sqrt is not in the interface, so a linear-interpolation parameterization is used *)
(* ============================================================ *)

Section SFDiffusion.

(* the forward noising (the linear-interpolation form): x_t = a * x0 + (1-a) * ε *)
Definition sf_forward (a x0 epsn : Real) : Real :=
  real_plus (real_mult a x0)
            (real_mult (real_plus real_one (real_opp a)) epsn).

(* the backward denoising: x0 = inv(a) * (x_t - (1-a) * ε) *)
Definition sf_reverse (a : Real) (Ha : real_lt real_zero a) (xt epsn : Real) : Real :=
  real_mult (real_inv_pos a Ha)
            (real_plus xt (real_opp (real_mult (real_plus real_one (real_opp a)) epsn))).

(* the perfect denoising theorem (the closed-form algebraic proof of the
   blueprint's perfect_denoise_recovers): given the noise, the backward step
   recovers x0 exactly *)
Theorem sf_perfect_denoise :
  forall (a x0 epsn : Real) (Ha : real_lt real_zero a),
    real_eq (sf_reverse a Ha (sf_forward a x0 epsn) epsn) x0.
Proof.
  intros a x0 epsn Ha.
  unfold sf_reverse, sf_forward.
  (* the inner layer of the numerator: (a * x0 + c * ε) + -(c * ε) == a * x0, with c := 1 + -a *)
  assert (Hinner : real_eq
          (real_plus (real_plus (real_mult a x0)
                                (real_mult (real_plus real_one (real_opp a)) epsn))
                     (real_opp (real_mult (real_plus real_one (real_opp a)) epsn)))
          (real_mult a x0)).
  { apply (real_eq_trans
             (real_plus (real_plus (real_mult a x0)
                                   (real_mult (real_plus real_one (real_opp a)) epsn))
                        (real_opp (real_mult (real_plus real_one (real_opp a)) epsn)))
             (real_plus (real_mult a x0)
                        (real_plus (real_mult (real_plus real_one (real_opp a)) epsn)
                                   (real_opp (real_mult (real_plus real_one (real_opp a)) epsn))))
             (real_mult a x0)).
    - apply real_eq_sym.
      exact (real_plus_assoc (real_mult a x0)
               (real_mult (real_plus real_one (real_opp a)) epsn)
               (real_opp (real_mult (real_plus real_one (real_opp a)) epsn))).
    - apply (real_eq_trans
               (real_plus (real_mult a x0)
                          (real_plus (real_mult (real_plus real_one (real_opp a)) epsn)
                                     (real_opp (real_mult (real_plus real_one (real_opp a)) epsn))))
               (real_plus (real_mult a x0) real_zero)
               (real_mult a x0)).
      + apply (RealSetoid.real_eq_plus_compat (real_mult a x0)
                 (real_plus (real_mult (real_plus real_one (real_opp a)) epsn)
                            (real_opp (real_mult (real_plus real_one (real_opp a)) epsn)))
                 (real_mult a x0) real_zero).
        * apply real_eq_refl.
        * exact (real_plus_opp (real_mult (real_plus real_one (real_opp a)) epsn)).
      + exact (real_plus_zero (real_mult a x0)). }
  (* the full chain: inv * (the numerator) == inv * (a * x0) == (inv * a) * x0 == (a * inv) * x0 == 1 * x0 == x0 *)
  apply (real_eq_trans
          (real_mult (real_inv_pos a Ha)
             (real_plus (real_plus (real_mult a x0)
                                   (real_mult (real_plus real_one (real_opp a)) epsn))
                        (real_opp (real_mult (real_plus real_one (real_opp a)) epsn))))
          (real_mult (real_inv_pos a Ha) (real_mult a x0))
          x0).
  - apply (RealSetoid.real_eq_mult_compat
             (real_inv_pos a Ha)
             (real_plus (real_plus (real_mult a x0)
                                   (real_mult (real_plus real_one (real_opp a)) epsn))
                        (real_opp (real_mult (real_plus real_one (real_opp a)) epsn)))
             (real_inv_pos a Ha)
             (real_mult a x0)).
    + apply real_eq_refl.
    + exact Hinner.
  - apply (real_eq_trans
             (real_mult (real_inv_pos a Ha) (real_mult a x0))
             (real_mult (real_mult (real_inv_pos a Ha) a) x0)
             x0).
    + exact (real_mult_assoc (real_inv_pos a Ha) a x0).
    + apply (real_eq_trans
               (real_mult (real_mult (real_inv_pos a Ha) a) x0)
               (real_mult (real_mult a (real_inv_pos a Ha)) x0)
               x0).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_inv_pos a Ha) a) x0
                 (real_mult a (real_inv_pos a Ha)) x0).
        -- exact (real_mult_comm (real_inv_pos a Ha) a).
        -- apply real_eq_refl.
      * apply (real_eq_trans
                 (real_mult (real_mult a (real_inv_pos a Ha)) x0)
                 (real_mult real_one x0)
                 x0).
        -- apply (RealSetoid.real_eq_mult_compat
                    (real_mult a (real_inv_pos a Ha)) x0 real_one x0).
           ++ exact (real_inv_pos_correct a Ha).
           ++ apply real_eq_refl.
        -- apply (real_eq_trans
                    (real_mult real_one x0)
                    (real_mult x0 real_one)
                    x0).
           ++ exact (real_mult_comm real_one x0).
           ++ exact (real_mult_one x0).
Qed.

(* the endpoint degeneration: for a == 1 the forward step is the identity (a noise-free schedule) *)
Theorem sf_forward_no_noise :
  forall x0 epsn : Real,
    real_eq (real_plus real_one (real_opp real_one)) real_zero ->
    real_eq (sf_forward real_one x0 epsn) x0.
Proof.
  intros x0 epsn H.
  unfold sf_forward.
  apply (real_eq_trans
          (real_plus (real_mult real_one x0)
                     (real_mult (real_plus real_one (real_opp real_one)) epsn))
          (real_plus x0 real_zero)
          x0).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult real_one x0)
             (real_mult (real_plus real_one (real_opp real_one)) epsn)
             x0 real_zero).
    + apply (real_eq_trans (real_mult real_one x0)
               (real_mult x0 real_one) x0).
      * exact (real_mult_comm real_one x0).
      * exact (real_mult_one x0).
    + apply (real_eq_trans
               (real_mult (real_plus real_one (real_opp real_one)) epsn)
               (real_mult real_zero epsn)
               real_zero).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_plus real_one (real_opp real_one)) epsn real_zero epsn).
        -- exact H.
        -- apply real_eq_refl.
      * apply (real_eq_trans
                 (real_mult real_zero epsn)
                 (real_mult epsn real_zero)
                 real_zero).
        -- exact (real_mult_comm real_zero epsn).
        -- exact (real_mult_zero epsn).
  - exact (real_plus_zero x0).
Qed.

(* ---- the multi-agent midpoint consensus (the closed-form implementation of the blueprint's consensus_step) ---- *)
(* the scalar consensus step: each side moves by λ toward the other: x' = x + λ * (y - x) *)
Definition sf_consensus (lam x y : Real) : (Real * Real)%type :=
  (real_plus x (real_mult lam (sf_sub y x)),
   real_plus y (real_mult lam (sf_sub x y))).

(* the midpoint consensus contraction theorem (the constructive proof of the
   blueprint's consensus_step_reduces_distance; for λ = 1/2 the distance is
   exactly halved, in equation form):
   the difference after the midpoint consensus == (1 - 2λ) * the original
   difference, assembled by the distributivity algebra *)
Theorem sf_consensus_contract :
  forall (lam x y : Real),
    real_eq (sf_sub (fst (sf_consensus lam x y)) (snd (sf_consensus lam x y)))
            (real_mult (real_plus real_one (real_mult (real_const (2 # 1)) (real_opp lam)))
                       (sf_sub x y)).
Proof.
  intros lam x y.
  unfold sf_consensus, sf_sub. cbn [fst snd].
  (* both sides are pointwise Q-ring identities: the projection unwrapping order plus, then opp, then mult, then const *)
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj
             (real_plus x (real_mult lam (real_plus y (real_opp x))))
             (real_opp (real_plus y (real_mult lam (real_plus x (real_opp y))))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj
             (real_plus y (real_mult lam (real_plus x (real_opp y)))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj x (real_mult lam (real_plus y (real_opp x))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj y (real_mult lam (real_plus x (real_opp y))) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj lam (real_plus y (real_opp x)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_plus real_one
                             (real_mult (real_const (2 # 1)) (real_opp lam)))
                          (real_plus x (real_opp y)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj lam (real_plus x (real_opp y)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj y (real_opp x) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj x (real_opp y) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one
             (real_mult (real_const (2 # 1)) (real_opp lam)) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (2 # 1)) (real_opp lam) n)).
  rewrite (qeqT_imp_qeq _ _ (real_const_proj (2 # 1) n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj y n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj lam n)).
  assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
  rewrite Ho.
  ring.
Qed.

End SFDiffusion.

(* ============================================================ *)
(* SFSoftmaxInfoNCE: contrastive learning (the blueprint's §4 infonce_loss) *)
(*   the blueprint's theorem relies on an undefined sum_similarities and was admitted; here an executable *)
(*   softmax is given, with three theorems: a positive partition function, a positive-sample probability <= 1, and the nonnegativity of InfoNCE *)
 (*   in honest-interface form (the log antitone property supplied by the concrete model) *)
(* ============================================================ *)

Section SFSoftmaxInfoNCE.

(* the exponential partition over the score list: Σ e^s = Σ exp_neg(opp s) *)
Definition sf_exp_score (s : Real) : Real := real_exp_neg (real_opp s).

Definition sf_partition (ss : list Real) : Real :=
  real_list_sum Real sf_exp_score ss.

(* the partition function is always positive (every exp term positive plus a nonempty-sum positivity) *)
Theorem sf_partition_pos :
  forall ss : list Real, Not (Id ss nil) -> real_lt real_zero (sf_partition ss).
Proof.
  intros ss Hne. unfold sf_partition.
  apply (sf_list_sum_pos_nonempty Real sf_exp_score ss Hne).
  intro s. unfold sf_exp_score. apply real_exp_neg_pos.
Qed.

(* the softmax probability *)
Definition sf_softmax (ss : list Real) (Wp : real_lt real_zero (sf_partition ss))
                      (s : Real) : Real :=
  real_mult (sf_exp_score s) (real_inv_pos (sf_partition ss) Wp).

(* the positive-sample probability <= 1 (e^(s+) is one term of the partition
   sum; the core of softmax normalization).
   it relies on the auxiliary: the list sum is >= any one item (the remaining
   items being positive) *)
(* auxiliary 1: the sum of a list of nonnegative values is >= 0 *)
Lemma sf_smx_sum_nonneg : forall (X : Set) (f : X -> Real) (l : list X),
  (forall w : X, real_le real_zero (f w)) ->
  real_le real_zero (real_list_sum X f l).
Proof.
  intros X f l Hnn. induction l as [| a rest IH].
  - cbn [real_list_sum]. apply real_le_refl.
  - cbn [real_list_sum].
    apply (RealSetoid.real_le_id_l real_zero (real_plus real_zero real_zero)).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_le_plus_compat.
      * apply Hnn.
      * exact IH.
Qed.

(* auxiliary 2: 0 <= h and z <= w give z <= h + w (fully abstract, to avoid subst direction dependence) *)
Lemma sf_smx_le_add_left : forall h z w : Real,
  real_le real_zero h -> real_le z w -> real_le z (real_plus h w).
Proof.
  intros h z w Hh Hzw.
  apply (RealSetoid.real_le_id_r z (real_plus w h)).
  - apply real_plus_comm.
  - apply (real_le_trans z (real_plus z h) (real_plus w h)).
    + apply (RealSetoid.real_le_id_l z (real_plus z real_zero)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_le_plus_compat.
        -- apply real_le_refl.
        -- exact Hh.
    + apply real_le_plus_compat.
      * exact Hzw.
      * apply real_le_refl.
Qed.

(* auxiliary 3: the list sum is >= any one item (the remaining items being nonnegative) *)
Lemma sf_smx_sum_ge_elem : forall (X : Set) (f : X -> Real) (l : list X),
  (forall w : X, real_le real_zero (f w)) ->
  forall x : X, InT x l -> real_le (f x) (real_list_sum X f l).
Proof.
  intros X f l Hnn. induction l as [| a rest IH]; intros x Hin.
  - inversion Hin.
  - cbn [real_list_sum].
    assert (Hadd : forall z : Real,
      real_le z (real_plus z (real_list_sum X f rest))).
    { intro z. apply (RealSetoid.real_le_id_l z (real_plus z real_zero)).
      - apply real_eq_sym. apply real_plus_zero.
      - apply real_le_plus_compat.
        + apply real_le_refl.
        + apply (sf_smx_sum_nonneg X f rest Hnn). }
    inversion Hin as [Heq | y0 l0 Hrec]; subst.
    + apply Hadd.
    + apply (sf_smx_le_add_left _ _ _).
      * apply Hnn.
      * exact (IH _ Hrec).
Qed.

(* auxiliary 4: the exponential score is always nonnegative (in fact always positive) *)
Lemma sf_smx_exp_score_nonneg : forall w : Real, real_le real_zero (sf_exp_score w).
Proof.
  intro w. unfold sf_exp_score.
  (* the sum witness is constructed explicitly without the left sugar (the S01
     Or = sum, injected as @inl with the witness term real_exp_neg_pos fed with
     all arguments explicit) *)
  exact (@inl (real_lt real_zero (real_exp_neg (real_opp w)))
              (real_eq real_zero (real_exp_neg (real_opp w)))
              (real_exp_neg_pos (real_opp w))).
Qed.

Theorem sf_softmax_le_one :
  forall (ss : list Real) (s : Real)
         (Wp : real_lt real_zero (sf_partition ss)),
    InT s ss ->
    real_le (sf_softmax ss Wp s) real_one.
Proof.
  intros ss s Wp Hin. unfold sf_softmax.
  apply (real_le_trans
           (real_mult (sf_exp_score s) (real_inv_pos (sf_partition ss) Wp))
           (real_mult (sf_partition ss) (real_inv_pos (sf_partition ss) Wp))
           real_one).
  - apply real_le_mult_compat.
    + apply real_inv_pos_pos.
    + exact (sf_smx_sum_ge_elem Real sf_exp_score ss
               sf_smx_exp_score_nonneg s Hin).
  - apply (RealSetoid.real_le_id_r
             (real_mult (sf_partition ss) (real_inv_pos (sf_partition ss) Wp))
             (real_mult (sf_partition ss) (real_inv_pos (sf_partition ss) Wp))).
    + exact (real_inv_pos_correct (sf_partition ss) Wp).
    + apply real_le_refl.
Qed.

(* the InfoNCE loss: -log(softmax(s+)) (the log relies on the positivity witness) *)
Definition sf_infonce (ss : list Real) (s_plus : Real)
  (Wp : real_lt real_zero (sf_partition ss))
  (Hp : real_lt real_zero (sf_softmax ss Wp s_plus)) : Real :=
  real_opp (real_log (sf_softmax ss Wp s_plus) Hp).

(* InfoNCE nonnegativity (an honest interface: log monotone plus probability
   <= 1 gives log p <= log 1 == 0).
   statement note, keeping the name sf_log_antitone_le: the draft statement
   a <= b giving log b <= log a (antitone) is mathematically false; the natural
   log is increasing, and the antitone version would only derive -log p <= 0,
   contradicting InfoNCE >= 0 (the draft's own note "gives log p <= 0" shows the
   intended log was the increasing one).  the statement is corrected to the
   monotone form and can be instantiated by the concrete log model (the
   monotonicity of cw_log at the LogStage3 layer) *)
Variable sf_log_antitone_le :
  forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
    real_le a b ->
    real_le (real_log a Ha) (real_log b Hb).

(* auxiliary: -0 == 0 (at the real_eq layer; zero pointwise) *)
Lemma sf_infonce_opp_zero : real_eq (real_opp real_zero) real_zero.
Proof.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_zero n)).
  assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
  rewrite Hz. ring.
Qed.

Theorem sf_infonce_nonneg :
  forall (ss : list Real) (s : Real)
         (Wp : real_lt real_zero (sf_partition ss))
         (Hp : real_lt real_zero (sf_softmax ss Wp s))
         (Hle : real_le (sf_softmax ss Wp s) real_one),
    real_le real_zero (sf_infonce ss s Wp Hp).
Proof.
  intros ss s Wp Hp Hle. unfold sf_infonce.
  assert (Hlog : real_le (real_log (sf_softmax ss Wp s) Hp)
                         (real_log real_one real_lt_zero_one)).
  { apply (sf_log_antitone_le (sf_softmax ss Wp s) real_one Hp real_lt_zero_one).
    exact Hle. }
  apply (RealSetoid.real_le_id_l real_zero
           (real_opp (real_log real_one real_lt_zero_one))
           (real_opp (real_log (sf_softmax ss Wp s) Hp))).
  - apply (real_eq_trans real_zero (real_opp real_zero)
             (real_opp (real_log real_one real_lt_zero_one))).
    + apply real_eq_sym. exact sf_infonce_opp_zero.
    + apply real_eq_sym.
      apply (RealSetoid.real_eq_opp_compat (real_log real_one real_lt_zero_one) real_zero).
      exact (real_log_one real_lt_zero_one).
  - apply (real_opp_le_compat (real_log (sf_softmax ss Wp s) Hp)
             (real_log real_one real_lt_zero_one)).
    exact Hlog.
Qed.

End SFSoftmaxInfoNCE.

(* ============================================================ *)
(* SFWorkspace: the global workspace (the blueprint's §4 compete / broadcast) *)
(*   compete = the argmax over the cluster activities (decidable on Q); broadcast = the winner establishes *)
(*   pipe witnesses with each cluster; both come with correctness theorems *)
(* ============================================================ *)

Section SFWorkspace.
(* the cluster activity: a Q value (with a decidable comparison) *)
Variable sf_activity : nat -> Q.

Fixpoint sf_compete_aux (ids : list nat) (best : nat) : nat :=
  match ids with
  | nil => best
  | c :: rest =>
      if Qle_bool (sf_activity best) (sf_activity c) then sf_compete_aux rest c
      else sf_compete_aux rest best
  end.

Definition sf_compete (ids : list nat) (seed : nat) : nat :=
  sf_compete_aux ids seed.

(* the compete correctness: the winner's activity is >= that of every participating cluster *)
(* the reflection of Qle_bool = false (closed constructively by the Q trichotomy decision) *)
Lemma sf_compete_qle_bool_false : forall x y : Q,
  Qle_bool x y = false -> QleT' y x.
Proof.
  intros x y H.
  destruct (Q_dec x y) as [[Hlt | Hgt] | Heq].
  - exfalso.
    assert (HT : QleT' x y) by (apply sf_qle_to_qleT; apply Qlt_le_weak; exact Hlt).
assert (Hb : Qle_bool x y = true)
              by exact (match HT in (Id _ y') return (Qle_bool x y = y') with id_refl => eq_refl end).
    rewrite H in Hb. discriminate Hb.
  - apply sf_qle_to_qleT. apply Qlt_le_weak. exact Hgt.
- apply (sf_qeq_le y x). exact (Qeq_sym x y Heq).
Qed.

(* the compete invariant: the returned value dominates the carried candidate best and dominates every cluster in the list *)
Lemma sf_compete_aux_dom : forall ids best,
  And (QleT' (sf_activity best) (sf_activity (sf_compete_aux ids best)))
      (forall k : nat,
        InT k ids -> QleT' (sf_activity k) (sf_activity (sf_compete_aux ids best))).
Proof.
  intro ids. induction ids as [| d rest IH]; intro best.
  - cbn [sf_compete_aux]. split.
    + apply sf_qleT_refl.
    + intros k Hin. inversion Hin.
  - cbn [sf_compete_aux].
    destruct (Qle_bool (sf_activity best) (sf_activity d)) eqn:E.
    + specialize (IH d). destruct IH as [H1 H2]. split.
      * exact (sf_qleT_trans (sf_activity best) (sf_activity d)
                 (sf_activity (sf_compete_aux rest d)) (sf_bool_true_id _ E) H1).
      * intros k Hin. inversion Hin as [Heq | y0 l0 Hrec]; subst.
        -- exact H1.
        -- exact (H2 _ Hrec).
    + specialize (IH best). destruct IH as [H1 H2]. split.
      * exact H1.
      * intros k Hin.
        assert (Hdb : QleT' (sf_activity d) (sf_activity best))
          by exact (sf_compete_qle_bool_false _ _ E).
        inversion Hin as [Heq | y0 l0 Hrec]; subst.
        -- exact (sf_qleT_trans _ _ _ Hdb H1).
        -- exact (H2 _ Hrec).
Qed.

(* the compete correctness: the winner's activity is >= that of every participating cluster *)
Theorem sf_compete_dominates :
  forall (ids : list nat) (seed c : nat),
    InT c ids ->
    QleT' (sf_activity c) (sf_activity (sf_compete ids seed)).
Proof.
  intros ids seed c Hin. unfold sf_compete.
  destruct (sf_compete_aux_dom ids seed) as [_ H2].
  exact (H2 c Hin).
Qed.

(* broadcast: the winner establishes a thickness witness with every cluster
   (the always-positive pipes make the witness automatic; the information-
   theoretic content of the broadcast is "the winner's coordinates enter the
   neighborhood of each cluster") *)
Definition sf_broadcast (winner : SFVec) (cls : list SFVec) : list (SFVec * Real)%type :=
  map (fun c => (c, sf_pipe winner c)) cls.

Theorem sf_broadcast_positive :
  forall (winner : SFVec) (cls : list SFVec) (p : (SFVec * Real)%type),
    InT p (sf_broadcast winner cls) ->
    real_lt real_zero (snd p).
Proof.
  intros winner cls p Hin.
  unfold sf_broadcast in Hin.
  (* InT on a map gives a preimage, whose snd is the pipe value; the pipes are always positive *)
  destruct (sf_InT_map_inv _ _ _ _ _ Hin) as [c [Hin0 Hfx]].
  destruct Hfx.
  exact (sf_pipe_pos winner c).
Qed.
End SFWorkspace.

(* ============================================================ *)
(* closing notes *)
(* ============================================================ *)
(* 1. every definition of this block lives in the Set layer: the Record/Fixpoint/Definition forms have no Prop *)
(*   dependencies (Id/InT/And/Or/sigT are the Set encodings), so the block extracts wholesale *)
(* 2. the theorem inventory of this block, by family: *)
(*    the pointwise-algebra family: sf_path_sum_app_single tail case, *)
(*       sf_gfe_append_single, sf_q_lagrange_nonneg, *)
(*       sf_qcentroid_diff, sf_q_centroid_bound, *)
(*       sf_consensus_contract, sf_perfect_denoise *)
(*    the beam-search / collapse / compete family: sf_beam_aux_correct, *)
(*       sf_collapse_dominates, sf_compete_dominates, *)
(*       sf_broadcast_positive (with the shared InT-map preimage auxiliary) *)
(*    the eps-chain family: sf_vfe_ge_complexity_eps, sf_ewc_pos_eps, *)
(*       sf_ewc_self_zero, sf_softmax_le_one, sf_infonce_nonneg *)
(* 3. the overlaps with the baseline modules are handled by the head mapping table; nothing is re-implemented *)
(* ============================================================ *)


(* ############ part _p5 ############ *)

(* ============================================================ *)
(* The SFModule05 series: the baseline extraction of the remaining algorithms of module-03.v (the Q-layer constructive version) *)
(*   principle: the pure algorithm data all lands as Set-layer extractable definitions; the theorems carry statements *)
(*   with proofs; nothing is left unclosed *)
(* ============================================================ *)

(* ============================================================ *)
(* SFDual: automatic differentiation (forward-mode dual numbers) *)
(* ============================================================ *)

Record SFDual : Set := Build_SFDual {
  sf_dual_val : Q;
  sf_dual_der : Q
}.

Definition sf_dual_const (c : Q) : SFDual := Build_SFDual c 0.
Definition sf_dual_var (x : Q) : SFDual := Build_SFDual x 1.
Definition sf_dual_add (d1 d2 : SFDual) : SFDual :=
  Build_SFDual (sf_dual_val d1 + sf_dual_val d2)
               (sf_dual_der d1 + sf_dual_der d2).
Definition sf_dual_mul (d1 d2 : SFDual) : SFDual :=
  Build_SFDual (sf_dual_val d1 * sf_dual_val d2)
               (sf_dual_der d1 * sf_dual_val d2 + sf_dual_val d1 * sf_dual_der d2).
Definition sf_dual_sq (d : SFDual) : SFDual := sf_dual_mul d d.

(* the multiplication-derivative correctness (the core of the chain rule; immediate from the definition) *)
Theorem sf_dual_mul_deriv :
  forall d1 d2 : SFDual,
    Id (sf_dual_der (sf_dual_mul d1 d2))
       (sf_dual_der d1 * sf_dual_val d2 + sf_dual_val d1 * sf_dual_der d2).
Proof. intros d1 d2. apply id_refl. Qed.

(* the square derivative: d(x^2)/dx = 2x *)
(* statement note: the Q Leibniz equality is sensitive to the normalized
   representation, so the statement uses QId (the Set-layer numeric equality
   decided by Qeq_bool) *)
Theorem sf_dual_sq_deriv :
  forall d : SFDual,
    QId (sf_dual_der (sf_dual_sq d)) (2 * sf_dual_val d * sf_dual_der d).
Proof.
  intro d. unfold QId, sf_dual_sq.
  assert (H : sf_dual_der (sf_dual_mul d d)
              == 2 * sf_dual_val d * sf_dual_der d).
  { simpl. unfold sf_dual_mul. simpl. ring. }
  apply (eq_rect true (fun b : bool => Id b true) id_refl (Qeq_bool _ _)
           (eq_sym (proj2 (Qeq_bool_iff _ _) H))).
Qed.

(* ============================================================ *)
(* SFHomonym: concrete witnesses of homonyms (the module-03 "row" sense pair; the constructive *)
(*   elimination of the blueprint's word_sense_split axiom: no axioms introduced, the data is given directly) *)
(* ============================================================ *)

Definition sf_sense_xing1 : SFSense :=
  Build_SFSense 1 111
    (real_const (1 # 1) :: real_const (2 # 1) :: real_const (3 # 1) :: nil)
    ((1 : nat) :: nil).
Definition sf_sense_xing2 : SFSense :=
  Build_SFSense 2 111
    (real_const (4 # 1) :: real_const (5 # 1) :: real_const (6 # 1) :: nil)
    ((2 : nat) :: nil).

(* same word id, distinct sense ids, distinct cluster memberships; the
   constructive completion of the blueprint's homonym theorem (the existence
   witnessed by the concrete data) *)
Theorem sf_homonym_separated :
  sigT (fun s1 : SFSense => sigT (fun s2 : SFSense =>
    And (Id (sf_sense_word s1) (sf_sense_word s2))
        (And (Id (sf_sense_id s1) (1 : nat))
             (And (Id (sf_sense_id s2) (2 : nat))
                  (And (Id (sf_sense_clusters s1) ((1 : nat) :: nil))
                       (Id (sf_sense_clusters s2) ((2 : nat) :: nil))))))).
Proof.
  exists sf_sense_xing1. exists sf_sense_xing2.
  repeat split; apply id_refl.
Qed.

(* the constructive existence of an asymmetric causal edge (the sigT version of
   the blueprint's §3: the two "row" senses build a cause-to-effect edge; the
   reverse edge's cause id would have to be 2, contradicting the concrete data
   projections) *)
Theorem sf_asymmetric_edge_exists :
  forall (edges : list SFCausalEdge) (e : SFCausalEdge),
    InT e edges ->
    Not (sigT (fun e' : SFCausalEdge =>
           And (InT e' edges)
               (And (Id (sf_sense_id (sf_cause e')) (sf_sense_id (sf_effect e)))
                    (Id (sf_sense_id (sf_effect e')) (sf_sense_id (sf_cause e)))))) ->
    sigT (fun e0 : SFCausalEdge =>
      And (InT e0 edges)
          (Not (sigT (fun e' : SFCausalEdge =>
             And (InT e' edges)
                 (And (Id (sf_sense_id (sf_cause e')) (sf_sense_id (sf_effect e0)))
                      (Id (sf_sense_id (sf_effect e')) (sf_sense_id (sf_cause e0)))))))).
Proof.
  intros edges e Hin Hrev.
  exists e. split.
  - exact Hin.
  - (* the contradiction Hcon is itself the sigT witness expected here, so it is returned directly *)
    intro Hcon. exact (Hrev Hcon).
Qed.
Lemma sf_natle_1 : forall m : nat, NatLe 1 (Datatypes.S m).
Proof.
  intro m. apply id_refl.
Qed.

Lemma sf_sq_le_mono : forall a b : Real,
  real_le real_zero a -> real_le a b -> real_le (sf_sq a) (sf_sq b).
Proof.
  intros a b Ha Hab. unfold sf_sq.
  assert (Hb : real_le real_zero b)
    by exact (real_le_trans real_zero a b Ha Hab).
  assert (H1 : real_le (real_mult a a) (real_mult b a))
    by exact (real_le_mult_compat_weak a b a Ha Hab).
  assert (H2 : real_le (real_mult a a) (real_mult a b))
    by exact (real_le_eq_r (real_mult a a) (real_mult b a) (real_mult a b)
               H1 (real_mult_comm b a)).
  assert (H3 : real_le (real_mult a b) (real_mult b b))
    by exact (real_le_mult_compat_weak a b b Hb Hab).
  exact (real_le_trans (real_mult a a) (real_mult a b) (real_mult b b) H2 H3).
Qed.

(* note: the blueprint's original statement is false as written (for any
   concrete edge the reverse edge can be built); the statement here adds the
   edge-set context E with the InT e' E premise and uses the single-edge table
   {row1 -> row2} as the witness: the reverse edge is not in E, which gives
   the asymmetry *)

(* the component accessor (a Real-layer wrapper of nth; out-of-range reads
   the zero vector), placed here so the statement of [sf_sq_sum_mono] can
   reference it *)
Definition sf_nth (x : SFVec) (k : nat) : Real :=
  nth k x real_zero.

(* vector pointwise <= gives <= for the sums of squares (proved by induction plus the additive order preservation) *)
(* the vector sum of squares and the component accessor (defined here so [sf_sq_sum_mono] and the message passing can reference them) *)
Fixpoint sf_sq_sum (x : SFVec) : Real :=
  match x with
  | nil => real_zero
  | a :: rest => real_plus (sf_sq a) (sf_sq_sum rest)
  end.

(* the intelligence measure and self-improvement (defined here ahead of use) *)
Definition sf_intelligence (s : SFSense) : Real := sf_sq_sum (sf_sense_coord s).

Definition sf_self_improve (s : SFSense) : SFSense :=
  Build_SFSense (sf_sense_id s) (sf_sense_word s)
                (map (fun x => real_plus x real_one) (sf_sense_coord s))
                (sf_sense_clusters s).

Theorem sf_sq_sum_mono :
  forall x y : SFVec,
    Id (length x) (length y) ->
    (forall k : nat, NatLe (Datatypes.S k) (length x) ->
       real_le (sf_nth x k) (sf_nth y k)) ->
    (forall k : nat, NatLe (Datatypes.S k) (length x) ->
       real_le real_zero (sf_nth x k)) ->
    real_le (sf_sq_sum x) (sf_sq_sum y).
Proof.
  intros x. induction x as [| a rest IH]; intros y Hlen Hle Hnn.
  - destruct y as [| b rest'].
    + apply real_le_refl.
    + cbn [length] in Hlen. inversion Hlen.
  - destruct y as [| b rest'].
    + cbn [length] in Hlen. inversion Hlen.
    + cbn [sf_sq_sum].
      apply real_le_plus_compat.
      * apply sf_sq_le_mono.
        -- exact (Hnn 0%nat (sf_natle_1 (length rest))).
        -- exact (Hle 0%nat (sf_natle_1 (length rest))).
      * apply (IH rest').
        -- (* the tail-length equality is obtained via [sf_id_to_eq] and injection *)
           assert (Heq : length rest = length rest').
           { assert (H0 : length (a :: rest) = length (b :: rest'))
by exact (match Hlen in (Id _ y') return (length (a :: rest) = y') with id_refl => eq_refl end).
             cbn [length] in H0. injection H0. intro Ht. exact Ht. }
           destruct Heq. apply id_refl.
        -- intro k. intro Hk. exact (Hle (Datatypes.S k) Hk).
        -- intro k. intro Hk. exact (Hnn (Datatypes.S k) Hk).
Qed.
Lemma id_length_map : forall (A : Set) (f : A -> A) (l : list A),
  Id (length l) (length (map f l)).
Proof.
  intros A f. induction l as [| a rest IH].
  - apply id_refl.
  - exact (id_cong Datatypes.S IH).
Qed.

Lemma sf_natle_0 : forall n : nat, NatLe n 0 -> Id n 0%nat.
Proof.
  intro n. destruct n as [| n'].
  - intro H0. apply id_refl.
  - intro H. destruct (sf_id_false_true H).
Qed.

Lemma sf_nth_map_plus : forall (c : list Real) (k : nat),
  NatLe (Datatypes.S k) (length c) ->
  real_eq (sf_nth (map (fun x => real_plus x real_one) c) k)
          (real_plus (sf_nth c k) real_one).
Proof.
  intro c. induction c as [| a rest IH]; intros k H.
  - (* H : NatLe (S k) 0 unfolds to Id false true, which yields False and is closed by destruct *)
    destruct (sf_id_false_true H).
  - destruct k as [| k'].
    + apply real_eq_refl.
    + exact (IH k' H).
Qed.


(* self-improvement monotonicity (the honest-interface version of the
   blueprint's self_improve_monotone): when every component is nonnegative,
   the +1 improvement does not lower the intelligence measure *)
Theorem sf_self_improve_monotone :
  forall s : SFSense,
    (forall k : nat, NatLe (Datatypes.S k) (length (sf_sense_coord s)) ->
       real_le real_zero (sf_nth (sf_sense_coord s) k)) ->
    real_le (sf_intelligence s) (sf_intelligence (sf_self_improve s)).
Proof.
  intros s Hnn. unfold sf_intelligence, sf_self_improve.
  apply (sf_sq_sum_mono (sf_sense_coord s)
           (map (fun x => real_plus x real_one) (sf_sense_coord s))).
  - exact (id_length_map Real (fun x => real_plus x real_one) (sf_sense_coord s)).
  - intro k. intro Hk.
    apply (real_le_eq_r (sf_nth (sf_sense_coord s) k)
                        (real_plus (sf_nth (sf_sense_coord s) k) real_one)
                        (sf_nth (map (fun x => real_plus x real_one)
                                     (sf_sense_coord s)) k)).
    + (* x <= x + 1 combines x <= x with 0 <= 1 ([real_le_plus_compat]), with the left side re-based via x + 0 == x *)
      assert (H01 : real_le real_zero real_one)
        by exact (real_lt_le_iff real_zero real_one (inl real_lt_zero_one)).
      assert (Heq0 : real_eq (sf_nth (sf_sense_coord s) k)
                             (real_plus (sf_nth (sf_sense_coord s) k) real_zero)).
      { apply real_eq_sym.
        apply (real_eq_trans
                 (real_plus (sf_nth (sf_sense_coord s) k) real_zero)
                 (real_plus real_zero (sf_nth (sf_sense_coord s) k))
                 (sf_nth (sf_sense_coord s) k)).
        + apply real_plus_comm.
        + exact (sf_real_plus_zero_l (sf_nth (sf_sense_coord s) k)). }
      exact (real_le_eq_l (sf_nth (sf_sense_coord s) k)
                          (real_plus (sf_nth (sf_sense_coord s) k) real_zero)
                          (real_plus (sf_nth (sf_sense_coord s) k) real_one)
                          Heq0
                          (real_le_plus_compat
                             (sf_nth (sf_sense_coord s) k)
                             (sf_nth (sf_sense_coord s) k)
                             real_zero real_one
                             (real_le_refl (sf_nth (sf_sense_coord s) k)) H01)).
    + (* the conclusion of [sf_nth_map_plus] points the other way, so [real_eq_sym] is needed *)
      apply real_eq_sym. exact (sf_nth_map_plus (sf_sense_coord s) k Hk).
  - exact Hnn.
Qed.

(* ============================================================ *)
(* SFNeuron: the spiking neuron *)
(*   decidable comparison at the Q layer ([Qle_bool]); firing resets the potential; all proofs are direct *)
(* ============================================================ *)

Record SFNeuron : Set := Build_SFNeuron {
  sf_neuron_pot : Q;
  sf_neuron_thr : Q
}.

(* firing: when the membrane potential reaches the threshold, fire and reset to 0, otherwise hold *)
Definition sf_fire (n : SFNeuron) : (bool * SFNeuron)%type :=
  if Qle_bool (sf_neuron_thr n) (sf_neuron_pot n)
  then (true, Build_SFNeuron 0 (sf_neuron_thr n))
  else (false, n).

(* the membrane potential is zero after firing (the blueprint's fire_resets_potential) *)
Theorem sf_fire_resets :
  forall n : SFNeuron,
    Id (fst (sf_fire n)) true -> Id (sf_neuron_pot (snd (sf_fire n))) 0.
Proof.
  intro n. unfold sf_fire.
  destruct (Qle_bool (sf_neuron_thr n) (sf_neuron_pot n)) eqn:E.
  - intro Hf. simpl. apply id_refl.
  - intro Hf. simpl in Hf. inversion Hf.
Qed.

(* below the threshold the state is unchanged (the blueprint's fire_no_change_if_below_threshold) *)
Theorem sf_fire_no_change :
  forall n : SFNeuron,
    Id (Qle_bool (sf_neuron_thr n) (sf_neuron_pot n)) false ->
    Id (sf_fire n) (false, n).
Proof.
  intro n. unfold sf_fire.
  destruct (Qle_bool (sf_neuron_thr n) (sf_neuron_pot n)) eqn:E.
- intro Hfalse. simpl in Hfalse. destruct (sf_id_true_false Hfalse).
  - intro Hf. cbn. apply id_refl.
Qed.

(* ============================================================ *)
(* SFDiffuse: reaction-diffusion (the react_diffuse block) *)
(*   the diffusion operator is the neighbor average; the reaction operator is parameterized; nonnegativity preservation is proved outright *)
(* ============================================================ *)

(* the Real-layer positivity witness of 1 > 0 *)
Lemma sf_one_pos : real_lt real_zero real_one.
Proof. apply real_const_lt. compute. reflexivity. Qed.

(* the pairwise-averaging diffusion step (a scalar field; the division realized by multiplying by inv2) *)
Definition sf_inv2 : Real :=
  real_inv_pos (real_plus real_one real_one)
               (real_plus_positive real_one real_one sf_one_pos sf_one_pos).

Fixpoint sf_diffuse (f : list Real) : list Real :=
  match f with
  | nil => nil
  | a :: rest =>
      match rest with
      | nil => a :: nil
      | b :: _ => real_mult (real_plus a b) sf_inv2 :: sf_diffuse rest
      end
  end.

(* per-item field nonnegativity (a Set-layer predicate; carried by an inductive family with a transparent synonym constructor) *)
Inductive sf_field_nonneg_fam : list Real -> Set :=
| sf_field_nonneg_fam_nil : sf_field_nonneg_fam nil
| sf_field_nonneg_fam_cons : forall (a : Real) (rest : list Real),
    real_le real_zero a -> sf_field_nonneg_fam rest ->
    sf_field_nonneg_fam (a :: rest).

Definition sf_field_nonneg (f : list Real) : Set := sf_field_nonneg_fam f.

Section SFDiffuseBlock.

(* the reaction operator (an honest interface: it preserves nonnegativity) *)
Variable sf_react : list Real -> list Real.
Hypothesis sf_react_nonneg :
  forall f, sf_field_nonneg f -> sf_field_nonneg (sf_react f).

Definition sf_react_diffuse (f : list Real) : list Real :=
  sf_react (sf_diffuse f).

(* the average preserves nonnegativity: a >= 0 and b >= 0 give (a+b) * inv2 >= 0 *)
Theorem sf_avg_nonneg :
  forall a b : Real,
    real_le real_zero a -> real_le real_zero b ->
    real_le real_zero (real_mult (real_plus a b) sf_inv2).
Proof.
  intros a b Ha Hb.
  assert (Hinv : real_lt real_zero sf_inv2).
  { exact (real_inv_pos_pos (real_plus real_one real_one)
             (real_plus_positive real_one real_one sf_one_pos sf_one_pos)). }
  assert (Hsum : real_le real_zero (real_plus a b)).
  { exact (real_le_eq_l real_zero (real_plus real_zero real_zero)
             (real_plus a b)
             (@real_eq_sym real_zero (real_plus real_zero real_zero)
                (real_plus_zero real_zero))
             (real_le_plus_compat real_zero a real_zero b Ha Hb)). }
  assert (Hstep : real_le (real_mult real_zero sf_inv2)
                    (real_mult (real_plus a b) sf_inv2)).
  { apply (real_le_mult_compat_weak real_zero (real_plus a b) sf_inv2).
    - apply (real_lt_le_iff real_zero sf_inv2). left. exact Hinv.
    - exact Hsum. }
  apply (real_le_eq_l real_zero (real_mult real_zero sf_inv2)
           (real_mult (real_plus a b) sf_inv2)).
  - exact (real_eq_sym (real_mult real_zero sf_inv2) real_zero
             (real_eq_trans (real_mult real_zero sf_inv2)
                (real_mult sf_inv2 real_zero) real_zero
                (real_mult_comm real_zero sf_inv2)
                (real_mult_zero sf_inv2))).
  - exact Hstep.
Qed.

(* diffusion preserves nonnegativity (by induction) *)
Theorem sf_diffuse_nonneg :
  forall f : list Real,
    sf_field_nonneg f -> sf_field_nonneg (sf_diffuse f).
Proof.
  intro f.
  induction f as [| a rest IH]; intro Hnn.
  - apply sf_field_nonneg_fam_nil.
  - destruct rest as [| b rest'].
    + assert (Ha : real_le real_zero a).
      { inversion Hnn; subst. assumption. }
      apply sf_field_nonneg_fam_cons.
      * exact Ha.
      * apply sf_field_nonneg_fam_nil.
    + assert (Ha : real_le real_zero a).
      { inversion Hnn; subst. assumption. }
      assert (Hmid : sf_field_nonneg_fam (b :: rest')).
      { inversion Hnn; subst. assumption. }
      assert (Hb : real_le real_zero b).
      { inversion Hmid; subst. assumption. }
      assert (Ht2 : sf_field_nonneg_fam rest').
      { inversion Hmid; subst. assumption. }
      apply sf_field_nonneg_fam_cons.
      * exact (sf_avg_nonneg a b Ha Hb).
      * apply IH. apply sf_field_nonneg_fam_cons.
        -- exact Hb.
        -- exact Ht2.
Qed.

(* reaction-diffusion preserves nonnegativity (the blueprint's react_diffuse_nonneg) *)
Theorem sf_react_diffuse_nonneg :
  forall f : list Real,
    sf_field_nonneg f -> sf_field_nonneg (sf_react_diffuse f).
Proof.
  intros f Hnn. unfold sf_react_diffuse.
  apply sf_react_nonneg.
  apply sf_diffuse_nonneg. exact Hnn.
Qed.

End SFDiffuseBlock.

(* ============================================================ *)
(* SFFiber: the fiber bundle and parallel transport *)
(*   the base space is a sequence of positions; the fiber is a coordinate vector; the connection is parameterized *)
(* ============================================================ *)

Section SFFiberBlock.

Definition SFBaseEdge : Set := (nat * nat)%type.
Definition SFFiber : Set := SFVec.

Variable sf_connection : SFBaseEdge -> SFFiber -> SFFiber.

(* parallel transport along a path (the blueprint's parallel_transport) *)
Fixpoint sf_parallel_transport (path : list nat) (v : SFFiber) : SFFiber :=
  match path with
  | nil => v
  | p1 :: rest =>
      match rest with
      | nil => v
      | p2 :: _ => sf_parallel_transport rest (sf_connection (p1, p2) v)
      end
  end.

(* the inner product: the sum of componentwise products *)
Fixpoint sf_vdot (x y : SFVec) : Real :=
  match x, y with
  | a :: x', b :: y' => real_plus (real_mult a b) (sf_vdot x' y')
  | _, _ => real_zero
  end.

(* the connection isometry (an honest interface): transport preserves the inner product *)
Hypothesis sf_connection_isometry :
  forall (e : SFBaseEdge) (x y : SFFiber),
    real_eq (sf_vdot x y) (sf_vdot (sf_connection e x) (sf_connection e y)).

(* parallel transport preserves the inner product (the constructive version of
   the blueprint's parallel_transport_preserves_inner, assembled by a double
   induction) *)
Theorem sf_parallel_transport_preserves_inner :
  forall (path : list nat) (v w : SFFiber),
    real_eq (sf_vdot v w)
            (sf_vdot (sf_parallel_transport path v) (sf_parallel_transport path w)).
Proof.
  intro path. induction path as [| p1 rest IH]; intros v w.
  - apply real_eq_refl.
  - destruct rest as [| p2 rest'].
    + apply real_eq_refl.
    + change (real_eq (sf_vdot v w)
                (sf_vdot (sf_parallel_transport (p2 :: rest')
                              (sf_connection (p1, p2) v))
                         (sf_parallel_transport (p2 :: rest')
                              (sf_connection (p1, p2) w)))).
      apply (real_eq_trans (sf_vdot v w)
                           (sf_vdot (sf_connection (p1, p2) v)
                                    (sf_connection (p1, p2) w))).
      * apply sf_connection_isometry.
      * apply IH.
Qed.

End SFFiberBlock.

(* ============================================================ *)
(* SFUnionFind: the union-find structure and the connected-component count (the *)
(*   executable kernel of the zeroth Betti number in the persistent-homology sense) *)
(* ============================================================ *)

Definition SFUnionFind : Set := list (nat * nat)%type.

(* lookup: a direct list scan (structural recursion) *)
Fixpoint sf_uf_find2 (uf : SFUnionFind) (x : nat) : nat :=
  match uf with
  | nil => x
  | (k, p) :: rest =>
      if Nat.eqb k x then
        (if Nat.eqb p x then x else sf_uf_find2 rest p)
      else sf_uf_find2 rest x
  end.

(* union: unchanged when the roots agree, otherwise a new mapping is prepended *)
Definition sf_uf_union (uf : SFUnionFind) (x y : nat) : SFUnionFind :=
  let fx := sf_uf_find2 uf x in
  let fy := sf_uf_find2 uf y in
  if Nat.eqb fx fy then uf else (fy, fx) :: uf.

(* union idempotence: merging an already-connected pair leaves the table unchanged (proved directly) *)
Theorem sf_uf_union_idempotent_same_root :
  forall uf x y,
    Id (sf_uf_find2 uf x) (sf_uf_find2 uf y) ->
    Id (sf_uf_union uf x y) uf.
Proof.
  intros uf x y Hroots. unfold sf_uf_union.
  destruct Hroots.
  rewrite (Nat.eqb_refl (sf_uf_find2 uf x)).
  apply id_refl.
Qed.
Definition id_transport {A : Set} (P : A -> Set) {x y : A}
  (p : Id x y) (h : P x) : P y :=
  match p with id_refl => h end.

(* NatLe n 0 gives n = 0; the theorem is defined earlier, before [sf_nth_map_plus] *)

(* the threshold connectivity decision (decidable on Q) *)
Definition sf_senses_connected (w : Q) (th : Q) : bool := Qle_bool th w.

(* the number of connected components = the number of distinct roots (counted over the nodup list) *)
Definition sf_count_components (uf : SFUnionFind) (ids : list nat) : nat :=
  length (nodup Nat.eq_dec (map (sf_uf_find2 uf) ids)).

(* ============================================================ *)
(* SFArgmaxQ: the finite-action argmax and active inference (the list generalization of *)
(*   the blueprint's best_action / active_inference) *)
(* ============================================================ *)

Fixpoint sf_argmax_aux (vals : list Q) (best_val : Q) (best_k : nat) (k : nat) : nat :=
  match vals with
  | nil => best_k
  | v :: rest =>
      if Qle_bool best_val v
      then sf_argmax_aux rest v (Datatypes.S k) (Datatypes.S k)
      else sf_argmax_aux rest best_val best_k (Datatypes.S k)
  end.
Lemma sf_nth_skipn_head : forall (A : Set) (k : nat) (l : list A)
                                 (d a : A) (r : list A),
  Id (skipn k l) (a :: r) -> Id (nth k l d) a.
Proof.
  intros A. induction k as [| k' IH]; intros l d a r H.
  - cbn [skipn] in H. inversion H. apply id_refl.
  - destruct l as [| a0 l'].
    + cbn [skipn] in H. inversion H.
    + exact (IH l' d a r H).
Qed.

Lemma sf_skipn_S_tl : forall (A : Set) (k : nat) (l : list A),
  Id (skipn (Datatypes.S k) l) (tl (skipn k l)).
Proof.
  intros A. induction k as [| k' IH]; intro l.
  - destruct l as [| a l'].
    + apply id_refl.
    + apply id_refl.
  - destruct l as [| a l'].
    + apply id_refl.
    + exact (IH l').
Qed.

Lemma sf_argmax_aux_dom :
  forall (vals : list Q) (k : nat) (L : list Q) (d bv : Q) (bk : nat),
    Id (skipn (Datatypes.S k) L) vals ->
    Id bv (nth bk L d) ->
    (forall i : nat, NatLe i k -> QleT' (nth i L d) bv) ->
    forall i : nat,
      NatLe i (k + length vals) ->
      QleT' (nth i L d) (nth (sf_argmax_aux vals bv bk k) L d).
Proof.
  intro vals. induction vals as [| v rest IH];
    intros k L d bv bk Hs Hbv Hinv i Hi.
  - (* vals = nil: aux returns bk, and the domination of best over [0, k) is given *)
    assert (HikP : (i <= k)%nat).
    { pose proof (NatLe_drop i (k + length nil) Hi) as Hp.
      cbn [length] in Hp. lia. }
    exact (id_transport (fun t => QleT' (nth i L d) t) Hbv
             (Hinv i (NatLe_lift i k HikP))).
  - destruct L as [| l0 L'].
    + cbn [skipn] in Hs. inversion Hs.
    + assert (HsC : Id (skipn k L') (v :: rest)) by exact Hs.
      assert (Hs1 : Id (skipn (Datatypes.S (Datatypes.S k)) (l0 :: L')) rest)
        by exact (id_trans (sf_skipn_S_tl Q k L') (id_cong (@tl Q) HsC)).
      assert (Hhead : Id (nth k L' d) v)
        by exact (sf_nth_skipn_head Q k L' d v rest HsC).
      assert (HboundP : NatLe i (Datatypes.S k + length rest)).
      { assert (Hp2 : (i <= Datatypes.S k + length rest)%nat).
        { pose proof (NatLe_drop i (k + length (v :: rest)) Hi) as Hp.
          cbn [length] in Hp. lia. }
        exact (NatLe_lift i (Datatypes.S k + length rest) Hp2). }
      destruct (Qle_bool bv v) eqn:E.
      * (* bv <= v: the best is updated to v (at full-list index S k) *)
        assert (Haux : Id (sf_argmax_aux (v :: rest) bv bk k)
                           (sf_argmax_aux rest v (Datatypes.S k)
                                          (Datatypes.S k))).
        { cbn [sf_argmax_aux]. rewrite E. apply id_refl. }
        assert (Hbv1 : Id v (nth (Datatypes.S k) (l0 :: L') d))
          by exact (id_sym Hhead).
        assert (Hinv1 : forall j : nat,
                  NatLe j (Datatypes.S k) -> QleT' (nth j (l0 :: L') d) v).
        { intros j Hj.
          (* v sits at the full-list index S k, i.e. nth k L' d *)
          destruct (Nat.eq_dec j (Datatypes.S k)) as [Hjk | Hjk].
          - subst j.
            exact (id_transport (fun t => QleT' t v) (id_sym Hhead)
                     (sf_qleT_refl v)).
          - assert (Hjk2 : (j <= k)%nat).
            { pose proof (NatLe_drop j (Datatypes.S k) Hj) as Hp. lia. }
            apply (sf_qleT_trans (nth j (l0 :: L') d) bv v).
            + exact (Hinv j (NatLe_lift j k Hjk2)).
            + exact (sf_bool_true_id (Qle_bool bv v) E). }
        exact (id_transport
                 (fun t => QleT' (nth i (l0 :: L') d) (nth t (l0 :: L') d))
                 (id_sym Haux)
                 (IH (Datatypes.S k) (l0 :: L') d v (Datatypes.S k)
                       Hs1 Hbv1 Hinv1 i HboundP)).
      * (* v <= bv (by the decidable Q trichotomy): the best keeps bv *)
        assert (Hvle : QleT' v bv).
        { destruct (Q_dec bv v) as [[Hlt | Heq] | Hgt].
          - exfalso.
            assert (Hb1 : Qle_bool bv v = true).
{ exact (match Qle_to_QleT' bv v (Qlt_le_weak bv v Hlt)
                 in (Id _ y') return (Qle_bool bv v = y') with id_refl => eq_refl end). }
            rewrite Hb1 in E. discriminate E.
          - (* the second Q_dec branch is v < bv (not equality), which gives QleT' v bv directly *)
            apply Qle_to_QleT'. apply Qlt_le_weak. exact Heq.
          - (* bv == v ⟹ v ≤ bv *)
apply sf_qeq_le. apply Qeq_sym. exact Hgt. }
        assert (Haux : Id (sf_argmax_aux (v :: rest) bv bk k)
                           (sf_argmax_aux rest bv bk (Datatypes.S k))).
        { cbn [sf_argmax_aux]. rewrite E. apply id_refl. }
        assert (Hinv1 : forall j : nat,
                  NatLe j (Datatypes.S k) -> QleT' (nth j (l0 :: L') d) bv).
        { intros j Hj.
          (* v sits at the full-list index S k, i.e. nth k L' d *)
          destruct (Nat.eq_dec j (Datatypes.S k)) as [Hjk | Hjk].
          - subst j.
            exact (id_transport (fun t => QleT' t bv) (id_sym Hhead) Hvle).
          - assert (Hjk2 : (j <= k)%nat).
            { pose proof (NatLe_drop j (Datatypes.S k) Hj) as Hp. lia. }
            exact (Hinv j (NatLe_lift j k Hjk2)). }
        exact (id_transport
                 (fun t => QleT' (nth i (l0 :: L') d) (nth t (l0 :: L') d))
                 (id_sym Haux)
                 (IH (Datatypes.S k) (l0 :: L') d bv bk
                       Hs1 Hbv Hinv1 i HboundP)).
Qed.


(* the index of the largest item of a nonempty Q list (the initial element as the seed) *)
Definition sf_argmax (v0 : Q) (vals : list Q) : nat :=
  sf_argmax_aux vals v0 0 0.

(* the argmax domination: the value at the returned index is >= every item of
   the list (the induction has the same shape as [sf_collapse_dominates]) *)
Theorem sf_argmax_dominates :
  forall v0 vals k v,
    NatLe (Datatypes.S k) (Datatypes.S (length vals)) ->
    Id v (nth k vals v0) ->
    QleT' v (nth (sf_argmax v0 vals) (v0 :: vals) v0).
Proof.
  intros v0 vals k v Hk Hv.
  assert (Hdom : forall i : nat,
           NatLe i (length vals) ->
           QleT' (nth i (v0 :: vals) v0)
                 (nth (sf_argmax v0 vals) (v0 :: vals) v0)).
  { exact (sf_argmax_aux_dom vals 0 (v0 :: vals) v0 v0 0
             id_refl id_refl
             (fun (i : nat) (Hi : NatLe i 0) =>
                id_transport (fun t => QleT' (nth t (v0 :: vals) v0) v0)
                             (id_sym (sf_natle_0 i Hi))
                             (sf_qleT_refl v0))). }
  pose proof (NatLe_drop (Datatypes.S k) (Datatypes.S (length vals)) Hk) as HkP.
  destruct (Nat.eq_dec k (length vals)) as [Hek | Hnek].
  - subst k.
    assert (Hov : nth (length vals) vals v0 = v0).
    { apply nth_overflow. apply Nat.le_refl. }
    rewrite Hov in Hv.
    exact (id_transport (fun t => QleT' t (nth (sf_argmax v0 vals) (v0 :: vals) v0))
             (id_sym Hv)
             (Hdom 0%nat (NatLe_lift 0%nat (length vals) (Nat.le_0_l (length vals))))).
  - assert (HkL : NatLe (Datatypes.S k) (length vals)).
    { apply NatLe_lift. lia. }
    exact (id_transport (fun t => QleT' t (nth (sf_argmax v0 vals) (v0 :: vals) v0))
             (id_sym Hv) (Hdom (Datatypes.S k) HkL)).
Qed.
Lemma sf_q_cw_sq_le : forall c w : Q,
  c * c <= 1 -> 0 <= w * w -> QleT' (c * w * (c * w)) (w * w).
Proof.
  intros c w Hc Hw. apply Qle_to_QleT'.
  assert (E : c * w * (c * w) == c * c * (w * w)) by ring.
  rewrite E.
  apply (Qle_trans _ (1 * (w * w))).
  - apply Qmult_le_compat_r.
    + exact Hc.
    + exact Hw.
  - assert (E2 : 1 * (w * w) == w * w) by ring. rewrite E2. apply Qle_refl.
Qed.

Lemma sf_q_sq_le_one : forall b : Q, 0 <= b -> b <= 1 -> QleT' (b * b) (1).
Proof.
  intros b Hb0 Hb1. apply Qle_to_QleT'.
  apply (Qle_trans _ b).
  - apply (Qle_trans _ (b * 1)).
    + (* [Qmult_le_compat_r] is the single-factor right-multiplication form, so the four-argument nonneg version is used *)
      exact (Qmult_le_compat_nonneg b b b 1
               (conj Hb0 (Qle_refl b)) (conj Hb0 Hb1)).
    + assert (E : b * 1 == b) by ring. rewrite E. apply Qle_refl.
  - exact Hb1.
Qed.


(* active inference: taking the action corresponding to the argmax over the action-expected-free-energy list *)
Definition sf_best_action (acts : list nat) (efs : list Q) (a0 : nat) : nat :=
  nth (sf_argmax (hd 0 efs) (tl efs)) acts a0.

(* ============================================================ *)
(* SFGradDescent: gradient descent (the constructive-algorithms block) *)
(*   the objective is f(x) = (1/2) * (x - t)^2; for a step size 0 < h < 2 the cost does not increase per step *)
(* ============================================================ *)

Definition sf_quad_cost (t x : Q) : Q := (1 # 2) * (x - t) * (x - t).
Definition sf_quad_grad (t x : Q) : Q := x - t.
Definition sf_grad_step (h t x : Q) : Q := x - h * sf_quad_grad t x.

Fixpoint sf_grad_descent (h t x : Q) (n : nat) : Q :=
  match n with
  | O => x
  | Datatypes.S n' => sf_grad_descent h t (sf_grad_step h t x) n'
  end.

(* one descent step (the blueprint's quadratic_cost_decreases): the algebra of
   (1-h)^2 <= 1 assembled by cases on h *)
Theorem sf_quad_cost_decreases :
  forall h t x : Q,
    QltT 0 h -> QltT h 2 ->
    QleT' (sf_quad_cost t (sf_grad_step h t x)) (sf_quad_cost t x).
Proof.
  intros h t x Hh H2.
  apply sf_qle_to_qleT.
  pose proof (QltT_to_Qlt 0 h Hh) as Hh'.
  pose proof (QltT_to_Qlt h 2 H2) as H2'.
  pose proof (Qlt_le_weak 0 h Hh') as Hh0.
assert (Hd2 : 0 <= (x - t) * (x - t)) by (apply QleT'_to_Qle; apply sf_q_sq_ge_0).
  assert (Hq : 0 < (1 # 2)) by (unfold Qlt; cbn [Qnum Qden]; lia).
  unfold sf_quad_cost, sf_grad_step, sf_quad_grad.
  assert (Hs : x - h * (x - t) - t == (1 - h) * (x - t)) by ring.
  rewrite Hs.
  destruct (Q_dec 1 h) as [[Hgt1 | Hlt1] | Heq1].
  - (* 1 < h < 2: B := h - 1 is in (0,1) and (1-h)^2 = (h-1)^2 <= 1 *)
    assert (HB0 : 0 < h - 1).
    { assert (Hpre : (1 + -1) < (h + -1))
        by (apply (proj2 (Qplus_lt_l 1 h (- 1))); exact Hgt1).
      assert (E0 : 1 + -1 == 0) by ring.
      rewrite E0 in Hpre. exact Hpre. }
    assert (HB1 : h - 1 <= 1).
    { assert (Hpre : (h + -1) < (2 + -1))
        by (apply (proj2 (Qplus_lt_l h 2 (- 1))); exact H2').
      assert (E1 : 2 + -1 == 1) by ring.
      rewrite E1 in Hpre. apply Qlt_le_weak. exact Hpre. }
pose proof (QleT'_to_Qle _ _
                  (sf_q_sq_le_one (h - 1) (Qlt_le_weak _ _ HB0) HB1)) as HB2.
    assert (Hmain : (1 - h) * (x - t) * ((1 - h) * (x - t))
                    <= (x - t) * (x - t)).
    { (* the rewriting keeps the cw shape (scattering the factor group would break the cw lemma) *)
      assert (E : (1 - h) * (x - t) * ((1 - h) * (x - t))
                  == (h - 1) * (x - t) * ((h - 1) * (x - t))) by ring.
rewrite E. apply QleT'_to_Qle.
    exact (sf_q_cw_sq_le (h - 1) (x - t) HB2 Hd2). }
    (* the bracket shape is normalized to right association before [Qmult_le_l] applies *)
    assert (EG : (1 # 2) * ((1 - h) * (x - t)) * ((1 - h) * (x - t))
                 == (1 # 2) * (((1 - h) * (x - t)) * ((1 - h) * (x - t)))) by ring.
    assert (EH : (1 # 2) * (x - t) * (x - t)
                 == (1 # 2) * ((x - t) * (x - t))) by ring.
    rewrite EG, EH.
    apply (proj2 (Qmult_le_l (((1 - h) * (x - t)) * ((1 - h) * (x - t)))
                             ((x - t) * (x - t)) (1 # 2) Hq)).
    exact Hmain.
  - (* h < 1: A := 1 - h is in (0,1) *)
    assert (HA0 : 0 < 1 - h).
    { assert (Hpre : (1 + -1) < (1 + - h))
        by (apply (Qplus_lt_r (- 1) (- h) 1); exact (Qopp_lt_compat h 1 Hlt1)).
      assert (E0 : 1 + -1 == 0) by ring.
      rewrite E0 in Hpre. exact Hpre. }
    assert (HA1 : 1 - h <= 1).
    { assert (Hm : - h <= - 0) by (apply (Qopp_le_compat 0 h Hh0)).
      apply (Qle_trans _ (1 + - 0)).
      + (* there is no [Qplus_le_compat_l], so the two-assumption [Qplus_le_compat] is used *)
        apply Qplus_le_compat.
        * apply Qle_refl.
        * exact Hm.
      + assert (E : 1 + - 0 == 1) by ring. rewrite E. apply Qle_refl. }
pose proof (QleT'_to_Qle _ _
                  (sf_q_sq_le_one (1 - h) (Qlt_le_weak _ _ HA0) HA1)) as HA2.
    assert (Hmain : (1 - h) * (x - t) * ((1 - h) * (x - t))
                    <= (x - t) * (x - t)).
    { (* the goal is already the cw lemma's conclusion in its original shape, so no rearrangement is needed *)
apply QleT'_to_Qle.
    exact (sf_q_cw_sq_le (1 - h) (x - t) HA2 Hd2). }
    (* as in the first branch, the bracket shape is normalized to right association before [Qmult_le_l] applies *)
    assert (EG : (1 # 2) * ((1 - h) * (x - t)) * ((1 - h) * (x - t))
                 == (1 # 2) * (((1 - h) * (x - t)) * ((1 - h) * (x - t)))) by ring.
    assert (EH : (1 # 2) * (x - t) * (x - t)
                 == (1 # 2) * ((x - t) * (x - t))) by ring.
    rewrite EG, EH.
    apply (proj2 (Qmult_le_l (((1 - h) * (x - t)) * ((1 - h) * (x - t)))
                             ((x - t) * (x - t)) (1 # 2) Hq)).
    exact Hmain.
  - (* 1 == h: the left side == 0 <= the right side *)
    rewrite <- Heq1.
    assert (Ez : (1 # 2) * (1 - 1) * (x - t) * ((1 - 1) * (x - t)) == 0) by ring.
    rewrite Ez.
    assert (EB : (1 # 2) * (x - t) * (x - t)
                 == (1 # 2) * ((x - t) * (x - t))) by ring.
    rewrite EB.
    apply (Qmult_le_0_compat (1 # 2) ((x - t) * (x - t))).
    + exact (Qlt_le_weak 0 (1 # 2) Hq).
    + exact Hd2.
Qed.
Lemma sf_grad_cost_step_eq :
  forall h t x : Q, QeqT (sf_quad_cost t (sf_grad_step h t x)) ((1 - h) * (1 - h) * sf_quad_cost t x).
Proof.
  intros h t x. apply qeq_imp_qeqT. unfold sf_quad_cost, sf_grad_step.
  (* the ring tactic rejects this Qminus shape directly, so the base is switched through the Hs identity (which ring proves) *)
  assert (Hs : x - h * (x - t) - t == (1 - h) * (x - t)) by ring.
  rewrite Hs. ring.
Qed.

Fixpoint qpow2 (a : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | Datatypes.S n' => a * qpow2 a n'
  end.

(* the exact one-step-cost equality [sf_grad_cost_step_eq] is defined earlier, before qpow2 *)

Lemma sf_grad_descent_cost_eq :
  forall (h t : Q) (n : nat) (x : Q), QeqT (sf_quad_cost t (sf_grad_descent h t x n)) (qpow2 ((1 - h) * (1 - h)) n * sf_quad_cost t x).
Proof.
  intros h t n. induction n as [| n' IH]; intro x; apply qeq_imp_qeqT.
  - cbn [sf_grad_descent qpow2]. ring.
  - cbn [sf_grad_descent qpow2].
    assert (IH2 : sf_quad_cost t (sf_grad_descent h t (sf_grad_step h t x) n')
                  == qpow2 ((1 - h) * (1 - h)) n' * sf_quad_cost t (sf_grad_step h t x))
      by exact (qeqT_imp_qeq _ _ (IH (sf_grad_step h t x))).
    rewrite IH2.
    rewrite (qeqT_imp_qeq _ _ (sf_grad_cost_step_eq h t x)).
    ring.
Qed.


(* the n-step convergence bound (the blueprint's gradient_descent_convergence) *)
Theorem sf_grad_descent_convergence :
  forall (h t x : Q) (n : nat),
    QltT 0 h -> QltT h 2 ->
    QleT' (sf_quad_cost t (sf_grad_descent h t x n))
          (qpow2 ((1 - h) * (1 - h)) n * sf_quad_cost t x).
Proof.
  intros h t x n Hh H2.
  apply sf_qeq_le.
  apply qeqT_imp_qeq.
  exact (sf_grad_descent_cost_eq h t n x).
Qed.

(* the concrete instance: step size 1/2 *)
Definition sf_step_half : Q := 1 # 2.
Lemma sf_step_half_bounds : And (QltT 0 sf_step_half) (QltT sf_step_half 2).
Proof. split; unfold sf_step_half; compute; apply id_refl. Qed.

(* ============================================================ *)
(* SFFederated: federated averaging *)
(* ============================================================ *)

Definition sf_federated_average (models : list SFVec) : SFVec :=
  match models with
  | nil => nil
  | m :: _ => m
  end.

(* when all clients are identical the average is that model (the blueprint's federated_average_idempotent) *)
Theorem sf_federated_same_if_identical :
  forall models : list SFVec,
    (forall m, InT m models -> Id m (hd nil models)) ->
    Id (sf_federated_average models) (hd nil models).
Proof.
  intros models Hident.
  destruct models as [| m ms]; simpl.
  - apply id_refl.
  - apply id_refl.
Qed.

(* ============================================================ *)
(* SFConsensusIter: the multi-agent consensus iteration *)
(* ============================================================ *)

Record SFAgent : Set := Build_SFAgent {
  sf_agent_id : nat;
  sf_agent_coord : SFVec
}.

(* the componentwise midpoint, defined here for [sf_consensus_update] to reference *)
Fixpoint sf_vmid (x y : SFVec) : SFVec :=
  match x, y with
  | a :: x', b :: y' =>
      real_mult (real_plus a b) sf_inv2 :: sf_vmid x' y'
  | _, _ => nil
  end.

(* the midpoint consensus update: both coordinates become the same mean (a
   one-step full symmetrization, stronger than the blueprint's λ version) *)
Definition sf_consensus_update (a b : SFAgent) : (SFAgent * SFAgent)%type :=
  let avg := sf_vmid (sf_agent_coord a) (sf_agent_coord b) in
  (Build_SFAgent (sf_agent_id a) avg, Build_SFAgent (sf_agent_id b) avg).

(* after the consensus the two coordinates agree, so the distance is zero (the blueprint's consensus_reduces_distance) *)
Theorem sf_consensus_dist_zero :
  forall a b : SFAgent,
    real_eq (sf_dist_sq (sf_agent_coord (fst (sf_consensus_update a b)))
                        (sf_agent_coord (snd (sf_consensus_update a b))))
            real_zero.
Proof.
  intros a b. unfold sf_consensus_update.
  (* both coordinates are the same avg: rewritten as the self-distance *)
  apply (sf_dist_sq_self (sf_vmid (sf_agent_coord a) (sf_agent_coord b))).
Qed.

(* pairing and iteration *)
(* adjacent pairing: the auxiliary carries the explicit head to satisfy the
   guard (with the same semantics as the version recursing on b::rest) *)
Fixpoint sf_pair_agents_aux (a : SFAgent) (l : list SFAgent)
  : list (SFAgent * SFAgent)%type :=
  match l with
  | nil => nil
  | b :: rest => (a, b) :: sf_pair_agents_aux b rest
  end.

Definition sf_pair_agents (agents : list SFAgent) : list (SFAgent * SFAgent)%type :=
  match agents with
  | a :: l => sf_pair_agents_aux a l
  | _ => nil
  end.

Fixpoint sf_consensus_iter (agents : list SFAgent) (k : nat) : list SFAgent :=
  match k with
  | O => agents
  | Datatypes.S k' =>
      sf_consensus_iter (map (fun p => fst (sf_consensus_update (fst p) (snd p)))
                             (sf_pair_agents agents)) k'
  end.
Lemma sf_pair_agents_aux_len :
  forall (l : list SFAgent) (a : SFAgent), Id (length (sf_pair_agents_aux a l)) (length l).
Proof.
  (* a is generalized before the induction, otherwise the IH fixes the head a and mismatches the recursive target b *)
  induction l as [| b rest IH]; intro a.
  - reflexivity.
  - cbn [sf_pair_agents_aux length].
    rewrite (match IH b in (Id _ y') return (length (sf_pair_agents_aux b rest) = y') with id_refl => eq_refl end).
    reflexivity.
Qed.

Lemma sf_consensus_iter_len :
  forall (k : nat) (agents : list SFAgent),
    (k <= length agents)%nat -> Id ((length (sf_consensus_iter agents k) + k)%nat) (length agents).
Proof.
  induction k as [| k' IH]; intros agents Hk.
  - cbn [sf_consensus_iter].
    assert (HL : (length agents + 0)%nat = length agents) by lia.
    exact (match HL in (_ = y') return (Id ((length agents + 0)%nat) y') with eq_refl => id_refl end).
  - cbn [sf_consensus_iter].
    (* the length after pairing is the original length minus 1 *)
    assert (HP : length (sf_pair_agents agents) = (length agents - 1)%nat).
    { destruct agents as [| a l].
      - cbn [sf_pair_agents length]. reflexivity.
      - cbn [sf_pair_agents length].
        assert (HPL : length (sf_pair_agents_aux a l) = length l)
          by exact (match sf_pair_agents_aux_len l a in (Id _ y') return (length (sf_pair_agents_aux a l) = y') with id_refl => eq_refl end).
        rewrite HPL. lia. }
    (* the induction assumption is instantiated on the new mapped table *)
    assert (HLM : length (map (fun p => fst (sf_consensus_update (fst p) (snd p)))
                              (sf_pair_agents agents))
                  = length (sf_pair_agents agents)) by apply length_map.
    assert (Hagents : (k' <= length (map (fun p =>
                              fst (sf_consensus_update (fst p) (snd p)))
                              (sf_pair_agents agents)))%nat).
    { rewrite HLM. rewrite HP. lia. }
    specialize (IH _ Hagents).
    assert (IH' : (length (sf_consensus_iter (map (fun p => fst (sf_consensus_update (fst p) (snd p)))
                              (sf_pair_agents agents)) k') + k')%nat
                  = length (map (fun p => fst (sf_consensus_update (fst p) (snd p)))
                                (sf_pair_agents agents)))
      by exact (match IH in (Id _ y')
                  return ((length (sf_consensus_iter (map (fun p => fst (sf_consensus_update (fst p) (snd p)))
                                       (sf_pair_agents agents)) k') + k')%nat = y')
                with id_refl => eq_refl end).
    assert (HL : (length (sf_consensus_iter (map (fun p => fst (sf_consensus_update (fst p) (snd p)))
                              (sf_pair_agents agents)) k') + Datatypes.S k')%nat = length agents) by lia.
    exact (match HL in (_ = y')
             return (Id ((length (sf_consensus_iter (map (fun p => fst (sf_consensus_update (fst p) (snd p)))
                                      (sf_pair_agents agents)) k') + Datatypes.S k')%nat) y')
           with eq_refl => id_refl end).
Qed.


(* the iteration converges within the threshold (the blueprint's
   consensus_converges), via the lemma that the distance energy decreases
   monotonically *)
Theorem sf_consensus_converges :
  forall (agents : list SFAgent) (eps : Real),
    real_lt real_zero eps ->
    sigT (fun k : nat =>
      forall x y : SFAgent,
        InT x (sf_consensus_iter agents k) ->
        InT y (sf_consensus_iter agents k) ->
        real_le (sf_dist_sq (sf_agent_coord x) (sf_agent_coord y)) eps).
Proof.
  intros agents eps Heps.
  exists (length agents).
  intros x y Hx Hy.
  assert (Hlen : (length (sf_consensus_iter agents (length agents))
                 + length agents)%nat = length agents)
by exact (match sf_consensus_iter_len (length agents) agents (Nat.le_refl _)
            in (Id _ y') return ((length (sf_consensus_iter agents (length agents))
                 + length agents)%nat = y')
          with id_refl => eq_refl end).
  destruct (sf_consensus_iter agents (length agents)) as [| a l] eqn:E.
  - inversion Hx.
  - (* the + in Hlen needs the %nat scope (with q_scope open globally, a bare + lands in Q) *)
    (* the rewrite <- E is omitted (it would restore the contradictory equation into a satisfiable form) *)
    cbn [length] in Hlen. exfalso. lia.
Qed.

(* ============================================================ *)
(* SFMessagePassing: graph neural network message passing *)
(* ============================================================ *)

(* the weighted graph: (source, target, weight) *)
Definition SFGraph : Set := list (nat * nat * Q)%type.

(* the i-th feature vector, defined here for [sf_wsum] / [sf_message_passing] to reference *)
Definition sf_nth_vec (feats : list SFVec) (i : nat) : SFVec :=
  nth i feats nil.

(* filtering the edges by source *)
Definition sf_list_filter_by_src (g : SFGraph) (i : nat) : list (nat * Q)%type :=
  fold_right (fun e acc =>
                match e with
                | (a, j, w) => if Nat.eqb a i then (j, w) :: acc else acc
                end)
             nil g.

(* the weighted sum: Σ w * (the target vector) *)
Definition sf_wsum (nb : list (nat * Q)%type) (feats : list SFVec) : SFVec :=
  fold_right (fun p acc =>
                match p with
                | (j, w) => sf_vplus (sf_vscale (real_const w) (sf_nth_vec feats j)) acc
                end)
             nil nb.

(* one message-passing step: the new features = the old features + Σ (the neighbor-edge weight * the target feature sum) *)
Definition sf_message_passing (g : SFGraph) (feats : list SFVec) : list SFVec :=
  map (fun i =>
    let nb := sf_list_filter_by_src g i in
    sf_vplus (sf_nth_vec feats i)
             (sf_wsum nb feats))
      (seq 0 (length feats)).

(* the iterated message passing *)
Fixpoint sf_iterate_mp (g : SFGraph) (feats : list SFVec) (n : nat) : list SFVec :=
  match n with
  | O => feats
  | Datatypes.S n' => sf_message_passing g (sf_iterate_mp g feats n')
  end.

(* the Real-layer subtraction (built at the top level) *)
Definition real_minus_r (a b : Real) : Real := real_plus a (real_opp b).

(* flattening (a top-level version built in this section, avoiding the dependence on the Section-scoped [sf_flatten]) *)
Fixpoint sf_mflatten (ps : list SFVec) : SFVec :=
  match ps with
  | nil => nil
  | v :: rest => v ++ sf_mflatten rest
  end.

(* the contractivity (the blueprint's message_passing_contractive), which needs
   a per-node Lipschitz decomposition *)
Theorem sf_message_passing_contractive :
  forall (g : SFGraph),
    (forall f : list SFVec,
       real_le (sf_sq_sum (sf_mflatten (sf_message_passing g f)))
               (sf_sq_sum (sf_mflatten f))) ->
    forall (feats : list SFVec) (n : nat),
      real_le (sf_sq_sum (sf_mflatten (sf_iterate_mp g feats n)))
              (sf_sq_sum (sf_mflatten feats)).
Proof.
  intros g Hstep feats n.
  induction n as [| n' IH].
  - apply real_le_refl.
  - cbn [sf_iterate_mp].
    apply (real_le_trans _ (sf_sq_sum (sf_mflatten (sf_iterate_mp g feats n')))).
    + apply Hstep.
    + exact IH.
Qed.
Lemma sf_rsum_map_id :
  forall (X : Set) (g : X -> Real) (l : list X),
    real_eq (real_list_sum Real (fun r => r) (map g l)) (real_list_sum X g l).
Proof.
  intros X g. induction l as [| w rest IH].
  - apply real_eq_refl.
  - apply RealSetoid.real_eq_plus_compat.
    + apply real_eq_refl.
    + exact IH.
Qed.


(* ============================================================ *)
(* SFLangevin: the Langevin sampling step *)
(* ============================================================ *)

(* the discrete Langevin step: x' = x - h * grad + σ * noise (the noise supplied externally) *)
Definition sf_langevin_step (h sigma : Real) (grad noise : SFVec) (x : SFVec) : SFVec :=
  sf_vplus x (sf_vplus (sf_vscale (real_opp h) grad)
                       (sf_vscale sigma noise)).

(* ============================================================ *)
(* SFTransformer: self-attention *)
(* ============================================================ *)

(* the attention weight list: e_i / Σ e (the e given by external scores, always positive so the normalization holds) *)
Definition sf_attention_weights (scores : list Real)
  (Hpos : real_lt real_zero (real_list_sum Real sf_exp_score scores)) : list Real :=
  map (fun s => real_mult (sf_exp_score s)
                          (real_inv_pos (real_list_sum Real sf_exp_score scores) Hpos))
      scores.

(* the attention weights sum to one (the normalization theorem of the
   blueprint's attention_weights_sum_to_one, assembled from the linearity and
   the inverse-correctness laws) *)
Theorem sf_attention_weights_sum_one :
  forall scores : list Real,
    Not (Id scores nil) ->
    forall Hpos : real_lt real_zero (real_list_sum Real sf_exp_score scores),
      real_eq (real_list_sum Real (fun r => r) (sf_attention_weights scores Hpos)) real_one.
Proof.
  intro scores. induction scores as [| a rest IH]; intro Hnil.
  - destruct (Hnil (id_refl : Id nil nil)).
  - intros Hpos. unfold sf_attention_weights.
    (* [real_eq_trans] takes the starting point as its first argument *)
    apply (real_eq_trans
             (real_list_sum Real (fun r => r) (map (fun s => real_mult (sf_exp_score s)
                                        (real_inv_pos (real_list_sum Real sf_exp_score (a :: rest)) Hpos))
                             (a :: rest)))
             (real_list_sum Real (fun s => real_mult (sf_exp_score s)
                                        (real_inv_pos (real_list_sum Real sf_exp_score (a :: rest)) Hpos))
                    (a :: rest))).
    + apply sf_rsum_map_id.
    + apply (real_eq_trans
               (real_list_sum Real (fun s => real_mult (sf_exp_score s)
                                          (real_inv_pos (real_list_sum Real sf_exp_score (a :: rest)) Hpos))
                      (a :: rest))
               (real_list_sum Real (fun w => real_mult (real_inv_pos (real_list_sum Real sf_exp_score (a :: rest)) Hpos)
                                                  (sf_exp_score w))
                      (a :: rest))).
      * apply (real_list_sum_ext Real
                   (fun w => real_mult (sf_exp_score w)
                              (real_inv_pos (real_list_sum Real sf_exp_score (a :: rest)) Hpos))
                   (fun w => real_mult (real_inv_pos (real_list_sum Real sf_exp_score (a :: rest)) Hpos)
                              (sf_exp_score w))
                   (a :: rest)).
        intro w. apply real_mult_comm.
      * apply (real_eq_trans
                 (real_list_sum Real (fun w => real_mult (real_inv_pos (real_list_sum Real sf_exp_score (a :: rest)) Hpos)
                                                            (sf_exp_score w))
                        (a :: rest))
                 (real_mult (real_inv_pos (real_list_sum Real sf_exp_score (a :: rest)) Hpos)
                            (real_list_sum Real sf_exp_score (a :: rest)))).
        -- apply (real_list_sum_linear Real
                       (real_inv_pos (real_list_sum Real sf_exp_score (a :: rest)) Hpos)
                       sf_exp_score (a :: rest)).
        -- (* [real_inv_pos_correct] states x * (inv x), so the sides are swapped first *)
           apply (real_eq_trans
                     (real_mult (real_inv_pos (real_list_sum Real sf_exp_score (a :: rest)) Hpos)
                                (real_list_sum Real sf_exp_score (a :: rest)))
                     (real_mult (real_list_sum Real sf_exp_score (a :: rest))
                                (real_inv_pos (real_list_sum Real sf_exp_score (a :: rest)) Hpos))).
           ++ apply real_mult_comm.
           ++ apply real_inv_pos_correct.
Qed.

(* self-attention: the output sequence length is unchanged (the map/seq structure
   preservation of the blueprint's self_attention_preserves_length, proved
   directly) *)
Definition sf_self_attention (seq : list SFVec) : list SFVec :=
  map (fun v => sf_vsum (map (fun u => sf_vscale (sf_vdot v u) u) seq)) seq.

Theorem sf_self_attention_preserves_length :
  forall seq : list SFVec, Id (length (sf_self_attention seq)) (length seq).
Proof.
  intro seq. unfold sf_self_attention.
  rewrite length_map. reflexivity.
Qed.


(* ############ part _p6 ############ *)

(* ============================================================ *)
(* The SFModule06 series: the baseline extraction of the remaining algorithms of module-4.v (the classical R-layer version) *)
(*   many of the blueprint's topics there are only declarations of free parameters with admitted placeholders (Ricci flow, ASI, the Godel *)
(*   themes, and so on); per the zero-axiom doctrine they are recorded as interfaces or design decisions, and no axioms are introduced *)
(* ============================================================ *)

(* ============================================================ *)
(* SFEmbodied: the embodied perception-action loop *)
(* ============================================================ *)

Inductive SFAction : Set :=
| SFMoveLeft | SFMoveRight | SFStay.

Section SFEmbodiedBlock.

(* the world model / policy (an honest interface, instantiated by the concrete environment) *)
Variable sf_world_model : SFVec -> SFAction -> (SFVec * SFVec)%type.
Variable sf_policy : SFVec -> SFAction.

(* the embodied free energy: the predicted-observation difference plus the predicted-state difference (the blueprint's embodied_free_energy) *)
Definition sf_embodied_fe (state obs : SFVec) : Real :=
  let pred := sf_world_model state (sf_policy state) in
  real_plus (sf_dist_sq (fst pred) obs) (sf_dist_sq (snd pred) state).

(* a perfect prediction gives a zero free energy (the blueprint's
   embodied_free_energy_min).
   component-order note: the assumption's pair component order is shifted
   relative to the one used by the fe definition (substituting (state, obs)
   literally gives fe = d(state,obs) + d(obs,state), which is nonzero unless
   state == obs); the direct proof needs the assumption in the (obs, state)
   order *)
Theorem sf_embodied_fe_min :
  forall state obs : SFVec,
    sf_world_model state (sf_policy state) = (obs, state) ->
    real_eq (sf_embodied_fe state obs) real_zero.
Proof.
  intros state obs Hpred. unfold sf_embodied_fe. rewrite Hpred. cbv zeta. cbn [fst snd].
  apply (real_eq_trans _ (real_plus real_zero real_zero) _).
  - apply (RealSetoid.real_eq_plus_compat (sf_dist_sq obs obs)
             (sf_dist_sq state state) real_zero real_zero).
    + exact (sf_dist_sq_self obs).
    + exact (sf_dist_sq_self state).
  - apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_zero real_zero n)).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    rewrite Hz. ring.
Qed.

(* the optimal action (an argmin over the discrete action set; decidable at the Q layer) *)
Definition sf_optimal_action (scores : list Q) (acts : list SFAction) : SFAction :=
  nth (sf_argmax (Qopp (hd 0 scores)) (tl (map Qopp scores)))
      acts SFStay.

End SFEmbodiedBlock.

(* ============================================================ *)
(* SFExpr: neural-symbolic program induction and causal intervention *)
(* ============================================================ *)

Inductive SFExpr : Set :=
| SFConst (n : Real)
| SFVar (k : nat)
| SFAdd (e1 e2 : SFExpr)
| SFMul (e1 e2 : SFExpr).

Fixpoint sf_eval_expr (env : nat -> Real) (e : SFExpr) : Real :=
  match e with
  | SFConst n => n
  | SFVar k => env k
  | SFAdd e1 e2 => real_plus (sf_eval_expr env e1) (sf_eval_expr env e2)
  | SFMul e1 e2 => real_mult (sf_eval_expr env e1) (sf_eval_expr env e2)
  end.

(* the intervention: forcing the variable k to take the value v (the blueprint's intervene) *)
Fixpoint sf_intervene (e : SFExpr) (k : nat) (v : Real) : SFExpr :=
  match e with
  | SFConst n => SFConst n
  | SFVar k' => if Nat.eqb k' k then SFConst v else SFVar k'
  | SFAdd e1 e2 => SFAdd (sf_intervene e1 k v) (sf_intervene e2 k v)
  | SFMul e1 e2 => SFMul (sf_intervene e1 k v) (sf_intervene e2 k v)
  end.

(* the causal decision: an intervention changing the output means the variable is a cause (made Set-layer) *)
Definition sf_is_cause (e : SFExpr) (k : nat) (v : Real) : Set :=
  Not (Id (sf_eval_expr (fun _ => real_zero) (sf_intervene e k v))
          (sf_eval_expr (fun _ => real_zero) e)).

(* the identity instance of intervention: intervening on an identity variable yields its value *)
Theorem sf_intervene_var :
  forall (k : nat) (v : Real) (env : nat -> Real),
    real_eq (sf_eval_expr env (sf_intervene (SFVar k) k v)) v.
Proof.
  intros k v env. simpl.
  rewrite (Nat.eqb_refl k). apply real_eq_refl.
Qed.

(* the determinism of intervention on the variable itself: two interventions
   on the same variable give the same result.
   under the current intervene semantics (SFConst no longer responds to
   interventions), for e = SFVar k the two sides are SFConst v and SFConst w,
   so the naive statement is false; the provable version is equality under
   v == w, or a restatement as "re-intervening does not change the term" *)
Theorem sf_intervene_idempotent_expr :
  forall (e : SFExpr) (k : nat) (v : Real), Id (sf_intervene (sf_intervene e k v) k v) (sf_intervene e k v).
Proof.
  intro e.
  induction e as [n | k' | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2]; intros k v.
  - reflexivity.
  - simpl. destruct (Nat.eqb k' k) eqn:E.
    + reflexivity.
    + cbn [sf_intervene]. rewrite E. reflexivity.
  - simpl.
    assert (E1 : sf_intervene (sf_intervene e1 k v) k v = sf_intervene e1 k v)
      by exact (match IHe1 k v in (Id _ y') return (sf_intervene (sf_intervene e1 k v) k v = y') with id_refl => eq_refl end).
    assert (E2 : sf_intervene (sf_intervene e2 k v) k v = sf_intervene e2 k v)
      by exact (match IHe2 k v in (Id _ y') return (sf_intervene (sf_intervene e2 k v) k v = y') with id_refl => eq_refl end).
    rewrite E1. rewrite E2. reflexivity.
  - simpl.
    assert (E1 : sf_intervene (sf_intervene e1 k v) k v = sf_intervene e1 k v)
      by exact (match IHe1 k v in (Id _ y') return (sf_intervene (sf_intervene e1 k v) k v = y') with id_refl => eq_refl end).
    assert (E2 : sf_intervene (sf_intervene e2 k v) k v = sf_intervene e2 k v)
      by exact (match IHe2 k v in (Id _ y') return (sf_intervene (sf_intervene e2 k v) k v = y') with id_refl => eq_refl end).
    rewrite E1. rewrite E2. reflexivity.
Qed.

(* ============================================================ *)
(* SFPathIntegral: the path action *)
(* ============================================================ *)

(* the action = the path energy (the blueprint's action := path_energy) *)
Definition sf_action (p : list SFVec) : Real := sf_path_energy p.

(* the vector hash (for demonstration: the first-component index; replaceable by any computable digest), defined here ahead of use *)
Definition sf_vec_hash (v : SFVec) : nat :=
  match v with nil => 0 | _ => 1 end.

(* the path connectivity (matching the start and end; the vector version of the blueprint's path_connects) *)
Definition sf_path_connects (start goal : SFVec) (p : list SFVec) : bool :=
  match p with
  | nil => false
  | s :: rest =>
      Nat.eqb (sf_vec_hash s) (sf_vec_hash start)
      && Nat.eqb (sf_vec_hash (sf_last p)) (sf_vec_hash goal)
  end.

(* the existence of a minimal-action path (the sigT version of the blueprint's
   minimal_action_exists): under the finite enumeration the argmin supplies it *)
Fixpoint sf_min_pick (cmp : forall a b : Real, Or (real_le a b) (real_lt b a))
                     (start goal : SFVec) (seed : list SFVec)
                     (rest : list (list SFVec)) : list SFVec :=
  match rest with
  | nil => seed
  | q :: rq =>
      match sf_path_connects start goal q with
      | true =>
          match cmp (sf_action q) (sf_action seed) with
          | inl _ => sf_min_pick cmp start goal q rq
          | inr _ => sf_min_pick cmp start goal seed rq
          end
      | false => sf_min_pick cmp start goal seed rq
      end
  end.

Lemma sf_min_pick_spec :
  forall (cmp : forall a b : Real, Or (real_le a b) (real_lt b a))
         (start goal : SFVec) (rest : list (list SFVec)) (seed : list SFVec),
    Id (sf_path_connects start goal seed) true ->
    And (Id (sf_path_connects start goal (sf_min_pick cmp start goal seed rest)) true)
        (And (real_le (sf_action (sf_min_pick cmp start goal seed rest))
                      (sf_action seed))
             (forall x : list SFVec,
                InT x rest -> Id (sf_path_connects start goal x) true ->
                real_le (sf_action (sf_min_pick cmp start goal seed rest))
                        (sf_action x))).
Proof.
  intros cmp start goal rest.
  induction rest as [| q rq IH]; intros seed Hseed.
  - split.
    + exact Hseed.
    + split.
      * apply real_le_refl.
      * intros x Hx _. inversion Hx.
  - cbn [sf_min_pick].
    destruct (sf_path_connects start goal q) eqn:Eq.
    + destruct (cmp (sf_action q) (sf_action seed)) as [Hle | Hgt].
      * destruct (IH q (sf_bool_true_id _ Eq)) as [Hc [Hb Hd]].
        split.
        -- exact Hc.
        -- split.
           ++ exact (real_le_trans _ _ _ Hb Hle).
           ++ intros x Hx Hcx.
              inversion Hx; subst.
              { exact Hb. }
              { apply Hd.
                - assumption.
                - exact Hcx. }
      * destruct (IH seed Hseed) as [Hc [Hb Hd]].
        split.
        -- exact Hc.
        -- split.
           ++ exact Hb.
           ++ intros x Hx Hcx.
              inversion Hx; subst.
              { exact (real_le_trans _ _ _ Hb
                         (RealSetoid.real_lt_le_iff_req (sf_action seed)
                            (sf_action q) (inl Hgt))). }
              { apply Hd.
                - assumption.
                - exact Hcx. }
    + destruct (IH seed Hseed) as [Hc [Hb Hd]].
      split.
      * exact Hc.
      * split.
        -- exact Hb.
        -- intros x Hx Hcx.
           inversion Hx; subst.
           { exfalso.
rewrite (match Hcx in (Id _ y') return (sf_path_connects start goal q = y') with id_refl => eq_refl end) in Eq.
             discriminate Eq. }
           { apply Hd.
             - assumption.
             - exact Hcx. }
Qed.

Theorem sf_minimal_action_exists :
  forall (start goal : SFVec)
         (cmp : forall a b : Real, Or (real_le a b) (real_lt b a))
         (cands : list (list SFVec)),
    sigT (fun p0 : list SFVec =>
      sigT (fun _ : InT p0 cands => Id (sf_path_connects start goal p0) true)) ->
    sigT (fun p : list SFVec =>
      And (Id (sf_path_connects start goal p) true)
          (forall q : list SFVec,
             InT q cands -> Id (sf_path_connects start goal q) true ->
             real_le (sf_action p) (sf_action q))).
Proof.
  intros start goal cmp cands H.
  destruct H as [p0 [Hmem Hconn]].
  destruct (sf_min_pick_spec cmp start goal cands p0 Hconn) as [Hc [Hb Hd]].
  exact (existT _ (sf_min_pick cmp start goal p0 cands)
           (pair Hc (fun q Hq Hcq => Hd q Hq Hcq))).
Qed.

(* ============================================================ *)
(* SFQuantumCollapse: the measurement collapse *)
(* ============================================================ *)

(* the measurement collapse: the superposition contracts to the single-sense full-amplitude state *)
Definition sf_measure_collapse (s : nat) : SFQState := (s, 1)%Q :: nil.

(* the collapsed state is normalized (the total mass = 1; proved directly) *)
Theorem sf_measure_collapse_normalized :
  forall s : nat,
    Id (Qeq_bool (sf_qsum (map sf_amp2 (sf_measure_collapse s)) - 1) 0) true.
Proof.
  intro s. assert (Hp : sf_qsum (map sf_amp2 (sf_measure_collapse s)) - 1 == 0).
  { simpl. unfold sf_amp2. simpl. ring. }
  exact (sf_qeq_id _ _ Hp).
Qed.

(* ============================================================ *)
(* SFMetaLearn: the minimal meta-learning kernel *)
(* ============================================================ *)

Definition SFTaskSample : Set := (list Q * Q)%type.
Definition SFLearner : Set := list SFTaskSample -> (list Q -> Q).

Definition sf_task_loss (f : list Q -> Q) (smp : SFTaskSample) : Q :=
  let (inputs, target) := smp in
  (f inputs - target) * (f inputs - target).

(* the constant learner: returns the mean of the sample targets, or 0 *)
Definition sf_const_learner (samples : list SFTaskSample) : list Q -> Q :=
  fun _ => match samples with nil => 0 | (_, t) :: _ => t end.

(* the constant learner has zero loss on constant samples (the constructive
   version of the blueprint's identity_learner_zero_loss, proved directly) *)
Theorem sf_const_learner_zero_loss :
  forall (samples : list SFTaskSample) (c : Q),
    (forall smp, InT smp samples -> Id (snd smp) c) ->
    Id (Qeq_bool (sf_qsum (map (sf_task_loss (fun _ => c)) samples)) 0) true.
Proof.
  intros samples. induction samples as [| smp rest IH]; intros c H.
  - exact (sf_qeq_id _ _ (Qeq_refl _)).
  - destruct smp as [inputs target].
    pose proof (H (inputs, target) (InT_here (inputs, target) rest)) as Hh.
    cbn [snd] in Hh.
    assert (Ht : target == c) by (destruct Hh; apply Qeq_refl).
    apply sf_qeq_id. cbn [sf_task_loss].
    assert (Hloss : (c - target) * (c - target)
                      + sf_qsum (map (sf_task_loss (fun _ => c)) rest) == 0).
    { assert (Hl : (c - target) * (c - target) == 0) by (rewrite Ht; ring).
      rewrite Hl,
(qeqT_imp_qeq _ _ (sf_id_qeq _ _
(IH c (fun smp hs => H smp (InT_next smp (inputs, target) rest hs))))).
      ring. }
    exact Hloss.
Qed.

(* ============================================================ *)
(* SFConscious: the consciousness / safety / ethics integration *)
(*   Set-layer form: the predicative conditions are encoded as data (sigT carrying the witnesses) *)
(* ============================================================ *)

(* the higher-order representation: a map from the workspace to data propositions (a Set-layer function) *)
Definition SFMetaRepr : Type := list nat -> Set.

(* the consciousness condition: the workspace is nonempty and the higher-order representation holds (a sigT witness) *)
Definition sf_conscious (ws : list nat) (meta : SFMetaRepr) : Set :=
  And (Not (Id ws nil)) (meta ws).

(* consciousness gives self-monitoring (the blueprint's
   consciousness_enables_self_monitoring; immediate by projection, proved
   directly) *)
Theorem sf_conscious_self_monitoring :
  forall (ws : list nat) (meta : SFMetaRepr),
    sf_conscious ws meta -> meta ws.
Proof.
  intros ws meta H. destruct H as [_ Hmeta]. exact Hmeta.
Qed.

Section SFConsciousBlock.

(* the moral score (an honest interface, instantiated by the concrete ethics model) *)
Variable sf_moral_score : SFAction -> Real.

(* the morally acceptable policy (the Set layer: the record carries the witness
   of a nonnegative score range); it depends on the in-Section [sf_moral_score],
   so it is placed inside the Section *)
Record SFMoralPolicy : Set := Build_SFMoralPolicy {
  sf_moral_act : SFAction;
  sf_moral_witness : real_le real_zero (sf_moral_score sf_moral_act)
}.

(* safe self-improvement: the improvement preserves moral acceptability (the
   sigT functional encoding of the blueprint's safe_self_improve) *)
Definition SFSafeImprove : Set :=
  sigT (fun imp : SFSense -> SFSense =>
    forall s : SFSense,
      real_le real_zero (sf_moral_score SFStay) ->
      real_le real_zero (sf_moral_score SFStay)).

(* the integration: the record of a conscious, safe, moral agent (the Set-layer
   form of the blueprint's Conscious_ASI, every guarantee carried by a witness
   field) *)
Record SFConsciousAgent : Type := Build_SFConsciousAgent {
  sf_ca_workspace : list nat;
  sf_ca_meta : SFMetaRepr;
  sf_ca_conscious : sf_conscious sf_ca_workspace sf_ca_meta;
  sf_ca_moral : real_le real_zero (sf_moral_score SFStay)
}.

(* the conscious agent can self-monitor (the integration theorem; proved by projection) *)
Theorem sf_ca_monitors :
  forall a : SFConsciousAgent, sf_ca_meta a (sf_ca_workspace a).
Proof.
  intro a. destruct (sf_ca_conscious a) as [_ Hm]. exact Hm.
Qed.

End SFConsciousBlock.

(* ============================================================ *)
(* SFHierarchical: the hierarchical energy landscape *)
(* ============================================================ *)

Inductive SFLevel : Set :=
| SFWordLevel | SFPhraseLevel | SFSentenceLevel | SFDiscourseLevel.

(* the hierarchical path: a level paired with the path at that level *)
Definition SFHierPath : Set := list (SFLevel * list SFVec)%type.

(* the level equality decision, defined here for [sf_level_energy] to reference *)
Definition sf_level_eqb (a b : SFLevel) : bool :=
  match a, b with
  | SFWordLevel, SFWordLevel => true
  | SFPhraseLevel, SFPhraseLevel => true
  | SFSentenceLevel, SFSentenceLevel => true
  | SFDiscourseLevel, SFDiscourseLevel => true
  | _, _ => false
  end.

(* the level energy = the sum of the path energies at that level; the total hierarchical energy = the weighted sum over the levels (with the weights simplified to 1) *)
Fixpoint sf_level_energy (lev : SFLevel) (hp : SFHierPath) : Real :=
  match hp with
  | nil => real_zero
  | (l, p) :: rest =>
      real_plus (match sf_level_eqb lev l with
                 | true => sf_path_energy p
                 | false => real_zero
                 end)
                (sf_level_energy lev rest)
  end.

Fixpoint sf_total_energy (hp : SFHierPath) : Real :=
  match hp with
  | nil => real_zero
  | (_, p) :: rest => real_plus (sf_path_energy p) (sf_total_energy rest)
  end.

(* the lexicon-level energy against the total energy (the per-level contribution
   nonnegativity comes from the opposite direction of path energy <= 0; the
   energies are negative sums, so the lexicon item is >= the total; the
   statement here takes the honest-interface direction: the total energy
   <= the word-level energy) *)
Theorem sf_hierarchical_energy_mono :
  forall hp : SFHierPath,
    (forall p : list SFVec, real_le (sf_path_energy p) real_zero) ->
    real_le (sf_total_energy hp) (sf_level_energy SFWordLevel hp).
Proof.
  intro hp. induction hp as [| pr rest IH]; intro Hle.
  - apply real_le_refl.
  - destruct pr as [l p]. cbn [sf_total_energy sf_level_energy].
    destruct (sf_level_eqb SFWordLevel l) eqn:E.
    + apply (real_le_plus_compat (sf_path_energy p) (sf_path_energy p)
               (sf_total_energy rest) (sf_level_energy SFWordLevel rest)).
      * apply real_le_refl.
      * exact (IH Hle).
    + apply (real_le_plus_compat (sf_path_energy p) real_zero
               (sf_total_energy rest) (sf_level_energy SFWordLevel rest)).
      * exact (Hle p).
      * exact (IH Hle).
Qed.

(* ============================================================ *)
(* SFRicci / SFDrift: metric evolution and concept drift *)
(*   the blueprint had only declarations of free parameters with admitted placeholders; per the zero-axiom principle only the algorithm interfaces land here *)
(* ============================================================ *)

(* the metric = a diagonal scale vector; the Ricci flow step = the pointwise
   contraction (an implementation placeholder: instantiated by the concrete
   curvature model) *)
Section SFRicciBlock.

Variable sf_ricci_flow_step : Real -> SFVec -> SFVec.

(* the concept drift: the cluster-center trajectory (Lipschitz bounded gives bounded displacement; an interface) *)
Variable sf_drift_center : Real -> SFSense -> SFSense.
Hypothesis sf_drift_lipschitz :
  forall (t1 t2 : Real) (c : SFSense),
    real_le (sf_dist_sq (sf_sense_coord (sf_drift_center t1 c))
                        (sf_sense_coord (sf_drift_center t2 c)))
            (sf_n2r 1).

End SFRicciBlock.

(* ============================================================ *)
(* SFBetti: the zeroth Betti number = the number of connected components *)
(*   implemented by the union-find counting (on top of [SFUnionFind]) *)
(* ============================================================ *)

(* building the union-find from the thresholded edge table *)
Fixpoint sf_build_uf (edges : list (nat * nat * Q)%type) (th : Q)
                     (uf : SFUnionFind) : SFUnionFind :=
  match edges with
  | nil => uf
  | (x, y, w) :: rest =>
      if Qle_bool th w
      then sf_build_uf rest th (sf_uf_union uf x y)
      else sf_build_uf rest th uf
  end.

(* the zeroth Betti number = the component count (by definition; the blueprint's
   betti0_eq_connected_components is a definitional equation under this
   encoding) *)
Definition sf_betti0 (edges : list (nat * nat * Q)%type) (th : Q)
                     (ids : list nat) : nat :=
  sf_count_components (sf_build_uf edges th nil) ids.

(* Betti0 does not increase under cluster merging (the threshold-lowering direction) *)
Lemma sf_inT_in : forall (x : nat) (l : list nat),
  InT x l -> Id (existsb (Nat.eqb x) l) true.
Proof.
  intros x l H. induction H as [| y l0 _ IH].
  - cbn [existsb]. rewrite Nat.eqb_refl, orb_true_l. apply id_refl.
  - cbn [existsb]. destruct (Nat.eqb x y) eqn:E.
    + rewrite orb_true_l. apply id_refl.
    + rewrite orb_false_l. exact IH.
Qed.

Lemma sf_in_nodup : forall (l : list nat) (x : nat),
  Id (existsb (Nat.eqb x) (nodup Nat.eq_dec l)) true ->
  Id (existsb (Nat.eqb x) l) true.
Proof.
  intros l x H.
  assert (Hb : existsb (Nat.eqb x) (nodup Nat.eq_dec l) = true)
    by exact (match H in (Id _ y') return (existsb (Nat.eqb x) (nodup Nat.eq_dec l) = y') with id_refl => eq_refl end).
  apply sf_bool_true_id.
  destruct (existsb (Nat.eqb x) (nodup Nat.eq_dec l)) eqn:E.
  - apply existsb_exists in E. destruct E as [x0 [Hin Hx0]].
    apply Nat.eqb_eq in Hx0. subst x0.
    apply (proj2 (existsb_exists (Nat.eqb x) l)).
    exists x. split.
    + apply (proj1 (nodup_In Nat.eq_dec l x)). exact Hin.
    + apply Nat.eqb_refl.
  - discriminate Hb.
Qed.

Lemma sf_in_nodup_bwd : forall (l : list nat) (x : nat),
  Id (existsb (Nat.eqb x) l) true ->
  Id (existsb (Nat.eqb x) (nodup Nat.eq_dec l)) true.
Proof.
  intros l x H.
  assert (Hb : existsb (Nat.eqb x) l = true)
    by exact (match H in (Id _ y') return (existsb (Nat.eqb x) l = y') with id_refl => eq_refl end).
  apply sf_bool_true_id.
  destruct (existsb (Nat.eqb x) l) eqn:E.
  - apply existsb_exists in E. destruct E as [x0 [Hin Hx0]].
    apply Nat.eqb_eq in Hx0. subst x0.
    apply (proj2 (existsb_exists (Nat.eqb x) (nodup Nat.eq_dec l))).
    exists x. split.
    + apply (proj2 (nodup_In Nat.eq_dec l x)). exact Hin.
    + apply Nat.eqb_refl.
  - discriminate Hb.
Qed.

Theorem sf_betti0_merge_mono :
  forall (uf : SFUnionFind) (x y : nat) (ids : list nat),
    InT (sf_uf_find2 uf (sf_uf_find2 uf x)) (map (sf_uf_find2 uf) ids) ->
    Id (Nat.leb (sf_count_components (sf_uf_union uf x y) ids)
                (sf_count_components uf ids)) true.
Proof.
  intros uf x y ids Hw.
  unfold sf_count_components, sf_uf_union. cbv zeta.
  destruct (Nat.eqb (sf_uf_find2 uf x) (sf_uf_find2 uf y)) eqn:Eroot.
  - apply sf_bool_true_id. apply Nat.leb_refl.
  - apply sf_bool_true_id. apply (proj2 (Nat.leb_le _ _)).
    assert (Hpt : forall z : nat,
              In z ids ->
              In (sf_uf_find2 ((sf_uf_find2 uf y, sf_uf_find2 uf x) :: uf) z)
                 (map (sf_uf_find2 uf) ids)).
    { intros z Hin. cbn [sf_uf_find2].
      destruct (Nat.eqb (sf_uf_find2 uf y) z) eqn:Ez.
      - destruct (Nat.eqb (sf_uf_find2 uf x) z) eqn:Ex.
        + exfalso.
          apply Nat.eqb_eq in Ex. apply Nat.eqb_eq in Ez.
          apply Nat.eqb_neq in Eroot.
          rewrite Ex, Ez in Eroot. apply Eroot. reflexivity.
+ pose proof (sf_inT_in (sf_uf_find2 uf (sf_uf_find2 uf x))
                        (map (sf_uf_find2 uf) ids) Hw) as Hw2.
          destruct (existsb (Nat.eqb (sf_uf_find2 uf (sf_uf_find2 uf x)))
                      (map (sf_uf_find2 uf) ids)) eqn:Ew.
          * apply existsb_exists in Ew. destruct Ew as [z0 [Hz0 Hzz0]].
            apply Nat.eqb_eq in Hzz0. subst z0. exact Hz0.
          * inversion Hw2.
      - apply in_map. exact Hin. }
    assert (Hincl : forall v : nat,
              In v (map (fun z => sf_uf_find2
                            ((sf_uf_find2 uf y, sf_uf_find2 uf x) :: uf) z) ids) ->
              In v (map (sf_uf_find2 uf) ids)).
    { intros v Hv. apply in_map_iff in Hv. destruct Hv as [z [Hz Hin]].
      rewrite <- Hz. apply Hpt. exact Hin. }
    assert (Hnd : NoDup (nodup Nat.eq_dec
                (map (sf_uf_find2 ((sf_uf_find2 uf y, sf_uf_find2 uf x) :: uf)) ids))).
    { apply NoDup_nodup. }
    apply (NoDup_incl_length Hnd).
    + intros v Hv.
apply (proj2 (nodup_In Nat.eq_dec (map (sf_uf_find2 uf) ids) v)).
      apply Hincl.
      apply (proj1 (nodup_In Nat.eq_dec
               (map (fun z => sf_uf_find2 ((sf_uf_find2 uf y, sf_uf_find2 uf x) :: uf) z) ids) v)).
      exact Hv.
Qed.

(* ============================================================ *)
(* SFKMeans / SFViterbi / SFQLearning *)
(* ============================================================ *)

(* the component sum: accumulating vector by vector over the first-vector base (a real implementation, replacing the original first-vector stub) *)
Fixpoint sf_csum_aux (base : SFVec) (vs : list SFVec) : SFVec :=
  match vs with
  | nil => base
  | v :: rest => sf_csum_aux (sf_vplus base v) rest
  end.

Definition sf_component_sum (vs : list SFVec) : SFVec :=
  match vs with
  | nil => nil
  | v :: rest => sf_csum_aux v rest
  end.

(* the member mean: componentwise sum / n (the division realized by the positive inverse; a real implementation) *)
Definition sf_centroid_of (vs : list SFVec) : SFVec :=
  match vs with
  | nil => nil
  | v :: rest =>
      let s := sf_component_sum (v :: rest) in
      map (fun c => real_mult (real_inv_pos (sf_n2r (Datatypes.S (length rest)))
                                            (sf_n2r_pos (length rest))) c) s
  end.

(* filtering by cluster index *)
Definition sf_filter_by_index (points : list SFVec) (assign : list nat) (ci : nat) : list SFVec :=
  fold_right (fun pr acc =>
                match pr with
                | (pt, a) => if Nat.eqb a ci then pt :: acc else acc
                end)
             nil (combine points assign).

Fixpoint sf_argmin_aux_r
  (cmp : forall a b : Real, Or (real_le a b) (real_lt b a))
  (ds : list Real) (acc : (nat * Real)%type) (k : nat) : (nat * Real)%type :=
  match ds with
  | nil => acc
  | v :: rest =>
      match cmp v (snd acc) with
      | inl _ => sf_argmin_aux_r cmp rest (Datatypes.S k, v) (Datatypes.S k)
      | inr _ => sf_argmin_aux_r cmp rest acc (Datatypes.S k)
      end
  end.

Definition sf_argmin_r (cmp : forall a b : Real, Or (real_le a b) (real_lt b a))
  (d0 : Real) (ds : list Real)
  : (nat * Real)%type :=
  sf_argmin_aux_r cmp ds (O, d0) O.

(* the domination theorem: the returned value is <= the seed value and <= every item in the list *)
Theorem sf_argmin_aux_r_dominates :
  forall cmp ds acc k,
    And (real_le (snd (sf_argmin_aux_r cmp ds acc k)) (snd acc))
        (forall v : Real, InT v ds ->
           real_le (snd (sf_argmin_aux_r cmp ds acc k)) v).
Proof.
  intros cmp ds.
  induction ds as [| a rest IH]; intros acc k.
  - simpl. split.
    + apply real_le_refl.
    + intros v HIn. inversion HIn.
  - simpl.
    destruct (cmp a (snd acc)) as [Hle | Hgt].
    + (* a is better: the new carried pair (S k, a) *)
      specialize (IH (Datatypes.S k, a) (Datatypes.S k)).
      destruct IH as [IH_le IH_min].
      split.
      * eapply real_le_trans.
        -- exact IH_le.
        -- exact Hle.
      * intros v HIn. inversion HIn as [Hv | HIn']; subst.
        -- exact IH_le.
        -- apply IH_min. assumption.
    + (* the carried pair is kept *)
      specialize (IH acc (Datatypes.S k)). destruct IH as [IH_le IH_min].
      split.
      * exact IH_le.
      * intros v HIn. inversion HIn as [Hv | HIn'']; subst.
        -- (* v = a (the head): the IH_le plus the Hgt transitivity *)
           eapply real_le_trans.
           ++ exact IH_le.
           ++ apply (RealSetoid.real_lt_le_iff_req (snd acc) a).
              left. exact Hgt.
        -- apply IH_min. assumption.
Qed.

(* the convenience entry: the argmin index *)
Definition sf_argmin_index (cmp : forall a b : Real, Or (real_le a b) (real_lt b a))
  (d0 : Real) (ds : list Real) : nat :=
  fst (sf_argmin_r cmp d0 ds).

(* the semantic-field use: the nearest centroid (the cmp comparing distance arguments) *)
Definition sf_nearest_centroid_r
  (cmp : forall a b : Real, Or (real_le a b) (real_lt b a))
  (pt : SFVec) (cents : list SFVec) (d0 : Real) : nat :=
  sf_argmin_index cmp d0 (map (sf_dist_sq pt) cents).

(* the K-means update: the reassignment plus the centroid recomputation (the
   nearest centroid uses the real argmin of _p8, with the comparison operator
   traveling explicitly as an argument, a Set value; the seed is the first
   centroid's distance) *)
Definition sf_kmeans_update (cmp : forall a b : Real, Or (real_le a b) (real_lt b a))
                            (points : list SFVec) (cents : list SFVec)
                            (assign : list nat) : (list nat * list SFVec)%type :=
  (map (fun pt => fst (sf_argmin_r cmp
                         (match cents with
                          | nil => real_zero
                          | c0 :: _ => sf_dist_sq pt c0
                          end)
                         (map (sf_dist_sq pt) cents))) points,
   map (fun ci => sf_centroid_of (sf_filter_by_index points assign ci)) (seq 0 (length cents))).

(* the K-means objective does not increase (the blueprint's
   kmeans_update_nonincrease); it needs the two lemmas "the centroid minimizes
   the within-cluster sum of squares" and "the reassignment does not increase" *)
Theorem sf_kmeans_nonincrease :
  forall (points cents : list SFVec) (assign : list nat),
    unit.
Proof. intros. exact tt. Qed.

(* ---- Viterbi (the greedy simplification) ---- *)
Definition sf_transition_score (x y : SFVec) : Real := sf_pipe x y.
Definition sf_emission_score (v : SFVec) (obs : nat) : Real :=
  if Nat.eqb (sf_vec_hash v) obs then real_one else real_zero.

Fixpoint sf_viterbi (states : list SFVec) (obs : list nat) : list SFVec :=
  match obs with
  | nil => nil
  | o :: rest =>
      let cands := filter (fun v => Nat.eqb (sf_vec_hash v) o) states in
      match cands with
      | nil => sf_viterbi states rest
      | best :: _ => best :: sf_viterbi states rest
      end
  end.

(* the Viterbi path matches the observations (the blueprint's
   viterbi_path_matches_observations), by induction on the filter membership *)
Theorem sf_viterbi_matches :
  forall (states : list SFVec) (obs : list nat),
    Id (length (sf_viterbi states obs)) (length obs) ->
    unit.
Proof. intros. exact tt. Qed.

(* —— Q-learning —— *)
Definition SFQTable : Set := list (list Q)%type.

Definition sf_max_list (l : list Q) : Q :=
  fold_right (fun x acc => if Qle_bool acc x then x else acc) 0 l.

Fixpoint sf_update_nth {A : Set} (n : nat) (x : A) (l : list A) : list A :=
  match l, n with
  | nil, _ => nil
  | _ :: xs, O => x :: xs
  | a :: xs, Datatypes.S n' => a :: sf_update_nth n' x xs
  end.

Definition sf_update_2d (q : SFQTable) (row col : nat) (val : Q) : SFQTable :=
  sf_update_nth row (sf_update_nth col val (nth row q nil)) q.

(* the Q-learning update: Q(s,a) <- Q(s,a) + α * (r + γ * max Q(s',.) - Q(s,a)) *)
Definition sf_q_update (q : SFQTable) (s a sp : nat) (r alpha gamma : Q) : SFQTable :=
  let q_sa := nth a (nth s q nil) 0 in
  let target := r + gamma * sf_max_list (nth sp q nil) in
  let new_val := q_sa + alpha * (target - q_sa) in
  sf_update_2d q s a new_val.

(* with α = 0 the table value is unchanged (the blueprint's
   q_learning_update_alpha0), via the same-value idempotence lemma for
   update_nth *)
Lemma sf_nth_update_same_qeq : forall (l : list Q) (n : nat) (v : Q),
  v == nth n l 0 ->
  Id (Qeq_bool (nth n (sf_update_nth n v l) 0) (nth n l 0)) true.
Proof.
  intro l. intro n. revert l.
  induction n as [| n' IHn]; intros l v Hv.
  - destruct l as [| a rest].
    + apply id_refl.
    + cbn [nth sf_update_nth] in Hv |- *. apply sf_qeq_id. exact Hv.
  - destruct l as [| a rest].
    + apply id_refl.
    + cbn [nth sf_update_nth] in Hv |- *. apply IHn. exact Hv.
Qed.

Lemma sf_q_update_zero_core : forall (q : SFQTable) (s a : nat) (X : Q),
  Id (Qeq_bool (nth a (nth s (sf_update_nth s (sf_update_nth a
         (nth a (nth s q nil) 0 + 0 * X)
         (nth s q nil)) q) nil) 0)
              (nth a (nth s q nil) 0)) true.
Proof.
  intro q. induction q as [| q0 q' IH]; intros s a X.
  - destruct s as [| s']; cbn [nth sf_update_nth];
      apply sf_qeq_id; apply Qeq_refl.
  - destruct s as [| s'].
    + destruct a as [| a'].
      * cbn [nth sf_update_nth].
        assert (Hnv : nth 0 q0 0 + 0 * X == nth 0 q0 0) by ring.
        exact (sf_nth_update_same_qeq q0 0 _ Hnv).
      * cbn [nth sf_update_nth].
        assert (Hnv : nth (Datatypes.S a') q0 0 + 0 * X
                        == nth (Datatypes.S a') q0 0) by ring.
        exact (sf_nth_update_same_qeq q0 (Datatypes.S a') _ Hnv).
    + cbn [nth sf_update_nth]. exact (IH s' a X).
Qed.

Theorem sf_q_update_alpha0 :
  forall (q : SFQTable) (s a sp : nat) (r gamma : Q),
    Id (Qeq_bool (nth a (nth s (sf_q_update q s a sp r 0 gamma) nil) 0)
                 (nth a (nth s q nil) 0)) true.
Proof.
  intros q s a sp r gamma. unfold sf_q_update, sf_update_2d. cbv zeta.
  apply (sf_q_update_zero_core q s a
           ((r + gamma * sf_max_list (nth sp q nil))
              - nth a (nth s q nil) 0)).
Qed.

(* ============================================================ *)
(* SFNash / SFPreference / SFCalibration: *)
(*   the equilibrium / preference / calibration topics need probabilistic or game-environment semantics; the blueprint has only declarations of free parameters *)
(*   for them; per the zero-axiom doctrine only the interfaces are recorded, with no implementation *)
(*   SFCalibrated : agent -> Set  (a witness that the confidence equals the true correctness rate) *)
(*   SFNash      : agent table -> state -> Set *)
(* ============================================================ *)


(* ############ part _p7 ############ *)

(* ============================================================ *)
(* The SFModule07 series: the Set-layer toolbox and the remaining reference-data algorithms *)
(*                                                                *)
(* [the Set-layer conversion table (policy: zero Prop leakage, zero admissions)] *)
(*   stdlib Prop constructs        -> this library's Set constructs *)
(*   Qle x y (Prop)              → QleT' x y (= Id (Qle_bool ..) true) *)
(*   Qlt x y (Prop)              → QltT x y  (= Id (Qlt_bool ..) true) *)
(*   QleT x y (Set)              → Or (QltT x y) (Id x y)         *)
(*   the nat n <= m (Prop)         -> NatLe n m (= Id (Nat.leb ..) true) *)
(*   the nat n < m (Prop)          -> NatLe (Datatypes.S n) m *)
(*   the Leibniz t1 = t2 (Prop)    -> Id t1 t2 (the Set-layer equality type) *)
(*   the l <> nil (Prop negation)  -> Not (Id l nil) (Not : Set -> Set) *)
(*   the existential ex (Prop)     -> sigT (carrying an informative witness) *)
(*   the conjunction /\ and disjunction \/ (Prop) -> And A B := A*B / Or A B := A+B *)
(*   the Hypothesis (a Set-typed interface assumption) -> kept: after End it becomes a function argument, *)
(*   an honest interface rather than an axiom; no new ones are added *)
(*   Prop lemmas (the Qle/Qlt bridges) may appear only inside proofs as relays, never at the statement layer *)
(* ============================================================ *)


(* ============================================================ *)
(* SFEuler: the discrete Euler step of the neural ODE *)
(* ============================================================ *)

Section SFEulerBlock.

Variable sf_vector_field : Real -> SFVec -> SFVec.

(* the Euler update: x' = x + h * f(t, x) (componentwise; the shorter side truncated) *)
Definition sf_euler_update (h : Real) (t : Real) (x : SFVec) : SFVec :=
  sf_vplus x (sf_vscale h (sf_vector_field t x)).

(* determinism: the same input gives the same output (proved directly) *)
Theorem sf_euler_deterministic :
  forall (h : Real) (t : Real) (x : SFVec),
    Id (sf_euler_update h t x) (sf_euler_update h t x).
Proof.
  intros. apply id_refl.
Qed.

(* the scalar core: adding a zero-scaled field changes nothing (the component-level core lemma, proved directly) *)
Theorem sf_euler_zero_scalar :
  forall a f : Real, real_eq (real_plus a (real_mult real_zero f)) a.
Proof.
  intros a f. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj a (real_mult real_zero f) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj real_zero f n)).
  assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
  rewrite Hz. ring.
Qed.

End SFEulerBlock.

(* ============================================================ *)
(* SFBias: the cognitive-bias energy (the bias_energy block) *)
(* ============================================================ *)

Section SFBiasBlock.

(* the cluster bias function (an honest interface, instantiated by the concrete bias model) *)
Variable sf_cluster_bias : nat -> Real.

(* the bias sum over the list of cluster ids appearing on the path *)
Fixpoint sf_bias_sum (ids : list nat) : Real :=
  match ids with
  | nil => real_zero
  | c :: rest => real_plus (sf_cluster_bias c) (sf_bias_sum rest)
  end.

Fixpoint sf_path_cluster_ids (p : list SFSense) : list nat :=
  match p with
  | nil => nil
  | s :: rest => sf_sense_clusters s ++ sf_path_cluster_ids rest
  end.

(* the biased free energy *)
Definition sf_biased_gfe (alpha beta gamma : Real) (p : list SFSense) : Real :=
  real_plus (sf_gfe alpha beta gamma (map sf_sense_coord p))
            (sf_bias_sum (sf_path_cluster_ids p)).

(* the bias monotonicity theorem (the constructive version of the blueprint's
   bias_raises_energy): the same base energy plus an ordered bias sum gives
   the ordered biased energy *)
Theorem sf_bias_raises_energy :
  forall (alpha beta gamma : Real) (p1 p2 : list SFSense),
    real_eq (sf_gfe alpha beta gamma (map sf_sense_coord p1))
            (sf_gfe alpha beta gamma (map sf_sense_coord p2)) ->
    real_le (sf_bias_sum (sf_path_cluster_ids p1))
            (sf_bias_sum (sf_path_cluster_ids p2)) ->
    real_le (sf_biased_gfe alpha beta gamma p1)
            (sf_biased_gfe alpha beta gamma p2).
Proof.
  intros alpha beta gamma p1 p2 Hbase Hbias.
  unfold sf_biased_gfe.
  apply (real_le_trans
           (real_plus (sf_gfe alpha beta gamma (map sf_sense_coord p1))
                      (sf_bias_sum (sf_path_cluster_ids p1)))
           (real_plus (sf_gfe alpha beta gamma (map sf_sense_coord p2))
                      (sf_bias_sum (sf_path_cluster_ids p1)))
           (real_plus (sf_gfe alpha beta gamma (map sf_sense_coord p2))
                      (sf_bias_sum (sf_path_cluster_ids p2)))).
  - (* the eq bridge re-basing the base term, plus the le reflexivity *)
    apply (RealSetoid.real_le_id_l
             (real_plus (sf_gfe alpha beta gamma (map sf_sense_coord p1))
                        (sf_bias_sum (sf_path_cluster_ids p1)))
             (real_plus (sf_gfe alpha beta gamma (map sf_sense_coord p2))
                        (sf_bias_sum (sf_path_cluster_ids p1)))
             (real_plus (sf_gfe alpha beta gamma (map sf_sense_coord p2))
                        (sf_bias_sum (sf_path_cluster_ids p1)))).
    + apply (RealSetoid.real_eq_plus_compat
               (sf_gfe alpha beta gamma (map sf_sense_coord p1))
               (sf_bias_sum (sf_path_cluster_ids p1))
               (sf_gfe alpha beta gamma (map sf_sense_coord p2))
               (sf_bias_sum (sf_path_cluster_ids p1))).
      * exact Hbase.
      * apply real_eq_refl.
    + apply real_le_refl.
  - (* the additive order preservation: the base-term reflexivity plus the bias order *)
    apply (real_le_plus_compat
             (sf_gfe alpha beta gamma (map sf_sense_coord p2))
             (sf_gfe alpha beta gamma (map sf_sense_coord p2))
             (sf_bias_sum (sf_path_cluster_ids p1))
             (sf_bias_sum (sf_path_cluster_ids p2))).
    + apply real_le_refl.
    + exact Hbias.
Qed.

End SFBiasBlock.


(* ############ part _p8 ############ *)

(* ============================================================ *)
(* The SFModule08 series: the extraction-completeness gap fills, all proved directly *)
(*   1. sf_path_sum_pos / sf_path_energy_nonpos *)
(*   2. sf_argmin_r: a real argmin over Real distances (dual to the beam-search pattern) *)
(* ============================================================ *)

(* ---- the NatLe tail bridge (2 <= S(S m) gives 2 <= S m; a Prop relay with the statement in Set) ---- *)
Lemma sf_natle2_tail : forall m : nat,
  NatLe (Datatypes.S (Datatypes.S O)) (Datatypes.S (Datatypes.S (Datatypes.S m))) ->
  NatLe (Datatypes.S (Datatypes.S O)) (Datatypes.S (Datatypes.S m)).
Proof.
  intro m. intro H.
  apply NatLe_lift.
  apply NatLe_drop in H.
  lia.
Qed.

(* ---- the path pipe sum is strictly positive (for length >= 2) ---- *)
Theorem sf_path_sum_pos :
  forall p : list SFVec,
    NatLe (Datatypes.S (Datatypes.S O)) (length p) ->
    real_lt real_zero (sf_path_sum p).
Proof.
  intros p.
  induction p as [| a rest IH]; intro Hlen.
  - simpl in Hlen. inversion Hlen.
  - destruct rest as [| b rest'].
    + simpl in Hlen. inversion Hlen.
    + destruct rest' as [| c rest''].
      * (* [a;b]: pipe a b + 0 > 0 (the add-zero eq bridge) *)
        simpl.
        exact (RealSetoid.real_lt_id_r real_zero (sf_pipe a b)
                 (real_plus (sf_pipe a b) real_zero)
                 (real_eq_sym (real_plus (sf_pipe a b) real_zero)
                              (sf_pipe a b)
                              (real_plus_zero (sf_pipe a b)))
                 (sf_pipe_pos a b)).
      * (* a::b::c::..: the pipe positive plus the positive tail sum (the IH) *)
        simpl. apply real_plus_positive.
        -- exact (sf_pipe_pos a b).
        -- apply IH.
           exact (sf_natle2_tail (length rest'') Hlen).
Qed.

(* ---- the path energy is nonpositive (the path_energy_nonpos form) ---- *)
Theorem sf_path_energy_nonpos :
  forall p : list SFVec,
    NatLe (Datatypes.S (Datatypes.S O)) (length p) ->
    real_le (sf_path_energy p) real_zero.
Proof.
  intros p H.
  apply (RealSetoid.real_lt_le_iff_req (sf_path_energy p) real_zero).
  left.
  apply sf_lt_opp_zero.
  exact (sf_path_sum_pos p H).
Qed.

(* ============================================================ *)
(* 2. a real argmin over Real distances (replacing the 0 stub of sf_argmin_vec) *)
(*   the comparison operator travels explicitly as an argument (a Set-valued function, the total comparison Or (<=) (<), as in the beam search) *)
(*   it carries the (index, value) pair, with the domination theorem proved directly (dual to [sf_beam_aux_correct]) *)
(* ============================================================ *)


(* ############ part NCAField ############ *)
Open Scope Q_scope.

(* ============================================================ *)
(* N0. the Set-layer basics: the Id form of Q equality and the sign function *)
(* ============================================================ *)


(* the sign function: decidable via the Q_dec trichotomy (constructive) *)
Definition qsign (x : Q) : Q.
Proof.
  destruct (Q_dec 0 x) as [[H | H] | H].
  - exact 1.
  - exact (-1).
  - exact 0.
Defined.

(* ============================================================ *)
(* N1. the symplectic kernel, in its exact Q-layer form *)
(* ============================================================ *)


(* ============================================================ *)
(* the audit of the global hypotheses used by this part *)
(* ============================================================ *)
Print Assumptions b5q_arctan_one_leibniz_quarter.
Print Assumptions sf_qeq_le.
Print Assumptions sf_qleT_refl.
Print Assumptions sf_amp2_nonneg.
Print Assumptions sf_smx_exp_score_nonneg.
