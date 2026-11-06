(* ConstructiveWorld-Set -- explicit interpolation of attention error across the temperature axis. *)

(** * UpReqTempInterp: explicit thresholds and error bounds across the temperature range.

    Mission.  Formalizes explicit interpolation between the two temperature
      extremes of soft attention: the error function [ti_err] realizes the
      explicit bound [e^(2*Delta/T) - 1] for [Delta > 0] and [T > 0], and the
      antitone law [ti_err_antitone] makes that bound decrease monotonically
      in [T]; the named thresholds [ti_Th] and [ti_T0] make the two endpoint
      existential thresholds explicit, and the main statements [ti_temp_interp]
      and [ti_hard_threshold] package threshold completion with monotone control.

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [UpTempWindow], [AttnHardLimit218] of this development.

    References.  This development, UpReqTempInterp.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqTempInterp.v] compiles cleanly
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
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpTempWindow.
Require Import AttnHardLimit218.

(* ================== Section 1. The error function: ti_err Delta T := e^(2*Delta/T) - 1 ================== *)

Definition ti_err (Delta T : Real) (Ht : real_lt real_zero T) : Real :=
  real_plus (cauchy_real_exp (real_mult (real_plus Delta Delta)
                           (real_inv_pos T Ht)))
            (real_opp real_one).

(* Base step: [0 < Delta + Delta]. *)
Lemma ti_two_pos : forall Delta : Real,
  real_lt real_zero Delta -> real_lt real_zero (real_plus Delta Delta).
Proof.
  intros Delta HD.
  apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
           (real_plus Delta Delta)).
  - apply real_eq_sym. apply real_plus_zero.
  - exact (real_lt_plus_compat real_zero Delta real_zero Delta HD HD).
Qed.

(* Positivity of the error function: [Delta > 0] and [T > 0] give [0 < ti_err Delta T],
   since [2*Delta/T > 0] and the exponential-minus-one term is positive on positive
   inputs. *)
Lemma ti_err_pos : forall (Delta T : Real) (HD : real_lt real_zero Delta)
                            (Ht : real_lt real_zero T),
  real_lt real_zero (ti_err Delta T Ht).
Proof.
  intros Delta T HD Ht. unfold ti_err.
  apply (cauchy_real_exp_minus_one_pos
           (real_mult (real_plus Delta Delta) (real_inv_pos T Ht))).
  apply real_mult_pos_compat.
  - exact (ti_two_pos Delta HD).
  - apply real_inv_pos_pos.
Qed.

(* ================== Section 2. The bound relation: the error is antitone in temperature (the global interpolation skeleton). ================== *)

(* Statement: for [Delta > 0] and [0 < T <= T'], [ti_err Delta T' <= ti_err Delta T].
   Route: the reciprocal reverses order ([real_inv_pos_le_compat]), multiplication on
   the left by a positive factor preserves order (the out-of-Section export
   [real_le_mult_compat_l_aux] of [AttnHardLimit218]), the exponential is monotone
   ([tw_exp_mono_le]), and addition preserves order. *)

Lemma ti_err_antitone : forall (Delta T T' : Real)
  (HD : real_lt real_zero Delta) (Ht : real_lt real_zero T)
  (Ht' : real_lt real_zero T'),
  real_le T T' -> real_le (ti_err Delta T' Ht') (ti_err Delta T Ht).
Proof.
  intros Delta T T' HD Ht Ht' Hle. unfold ti_err.
  apply real_le_plus_compat.
  - apply tw_exp_mono_le.
    apply (real_le_mult_compat_l_aux _ _ _ (ti_two_pos Delta HD)).
    exact (real_inv_pos_le_compat T T' Ht Ht' Hle).
  - apply real_le_refl.
Qed.

(* ================== Section 3. The explicit high-temperature threshold: positivity of [cw_log (1 + eps)] and the threshold definition. ================== *)

(* [1 < 1 + eps]: a same-shape copy of the HU1 chain inside [temp_window_T_infty]. *)
Lemma ti_one_eps_lt_one : forall eps : Real,
  real_lt real_zero eps -> real_lt real_one (real_plus real_one eps).
Proof.
  intros eps Heps.
  apply (real_eq_lt_lt real_one (real_plus real_one real_zero)
           (real_plus real_one eps)).
  - apply (real_eq_trans real_one (real_plus real_one real_zero)
             (real_plus real_zero real_one)).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_plus_comm.
  - apply (real_lt_eq_lt (real_plus real_zero real_one)
             (real_plus eps real_one) (real_plus real_one eps)).
    + exact (real_lt_plus_compat_lt_le real_zero eps real_one real_one
               Heps (real_le_refl real_one)).
    + apply real_plus_comm.
Qed.

(* 0 < 1+eps *)
Lemma ti_one_eps_pos : forall eps : Real,
  real_lt real_zero eps -> real_lt real_zero (real_plus real_one eps).
Proof.
  intros eps Heps.
  apply (real_lt_le_trans real_zero real_one (real_plus real_one eps)
           real_lt_zero_one).
  apply tw_le_plus_nonneg_r.
  apply tw_lt_le. exact Heps.
Qed.


Lemma ti_log_one_eps_pos : forall (eps : Real) (Heps : real_lt real_zero eps),
  real_lt real_zero (cw_log (real_plus real_one eps) (ti_one_eps_pos eps Heps)).
Proof.
  intros eps Heps.
  apply (real_eq_lt_lt real_zero (cw_log real_one real_lt_zero_one)
           (cw_log (real_plus real_one eps) (ti_one_eps_pos eps Heps))).
  - apply real_eq_sym. apply log_inv_one_thm.
  - exact (real_log_lt_mono real_one (real_plus real_one eps)
             real_lt_zero_one (ti_one_eps_pos eps Heps)
             (ti_one_eps_lt_one eps Heps)).
Qed.

(* The explicit high-temperature threshold: [ti_Th Delta il := 2*Delta*il + 1], with
   [il] the reciprocal of [cw_log (1 + eps)]. *)
Definition ti_Th (Delta il : Real) : Real :=
  real_plus (real_mult (real_plus Delta Delta) il) real_one.

(* Positivity of the threshold: [Delta > 0] and [il > 0] give [0 < ti_Th Delta il]; the
   chain mirrors the endpoint [T2] positivity proof, through [0 < 1 <= ti_Th Delta il]. *)
Lemma ti_Th_pos : forall (Delta il : Real) (HD : real_lt real_zero Delta)
                          (Hil : real_lt real_zero il),
  real_lt real_zero (ti_Th Delta il).
Proof.
  intros Delta il HD Hil. unfold ti_Th.
  assert (H2D : real_lt real_zero (real_plus Delta Delta))
    by exact (ti_two_pos Delta HD).
  assert (H2Dil : real_lt real_zero
                    (real_mult (real_plus Delta Delta) il))
    by exact (real_mult_pos_compat (real_plus Delta Delta) il H2D Hil).
  apply (real_lt_le_trans real_zero real_one
           (real_plus (real_mult (real_plus Delta Delta) il) real_one)
           real_lt_zero_one).
  apply (tw_le_eq_l (real_plus real_zero real_one)
           (real_plus (real_mult (real_plus Delta Delta) il) real_one)
           real_one).
  + apply real_le_plus_compat.
    * apply tw_lt_le. exact H2Dil.
    * apply real_le_refl.
  + apply (real_eq_trans real_one (real_plus real_one real_zero)
             (real_plus real_zero real_one)).
    * apply real_eq_sym. apply real_plus_zero.
    * apply real_plus_comm.
Qed.

(* ================== Section 4. Main statement: explicit interpolation across the whole temperature range (an explicit witness function with a two-fold characterization). ================== *)

(* Branch 1 (threshold completion): [T > ti_Th Delta il] implies [ti_err Delta T <= eps];
   the algebraic chain mirrors the [Th*L = 2*Delta + L] computation inside
   [temp_window_T_infty].  Branch 2 (global monotonicity): [0 < T <= T'] implies
   [ti_err Delta T' <= ti_err Delta T], so the error at any intermediate temperature is
   pinned pointwise by the explicit function, and the behavior at the two endpoint
   regimes is interpolated by this monotone skeleton. *)

Theorem ti_temp_interp :
  forall (Delta eps : Real),
    real_lt real_zero Delta ->
    real_lt real_zero eps ->
    sigT (fun Th => And (real_lt real_zero Th)
      (And (forall (T : Real) (Ht : real_lt real_zero T),
              real_lt Th T -> real_le (ti_err Delta T Ht) eps)
           (forall (T T' : Real) (Ht : real_lt real_zero T)
                                (Ht' : real_lt real_zero T'),
              real_le T T' ->
              real_le (ti_err Delta T' Ht') (ti_err Delta T Ht)))).
Proof.
  intros Delta eps HD Heps.
  pose (il := real_inv_pos (cw_log (real_plus real_one eps)
                              (ti_one_eps_pos eps Heps))
             (ti_log_one_eps_pos eps Heps)).
  pose (HL0 := ti_log_one_eps_pos eps Heps).
  exists (ti_Th Delta il). split.
  - apply (ti_Th_pos Delta il HD). apply real_inv_pos_pos.
  - split.
    + (* Branch 1: [T > ti_Th Delta il] implies [ti_err Delta T <= eps]; the same algebraic chain as in [temp_window_T_infty]. *)
      intros T Ht HT2T.
      pose (L := cw_log (real_plus real_one eps) (ti_one_eps_pos eps Heps)).
      pose (twoD := real_plus Delta Delta).
      assert (Ha : real_lt (real_mult (ti_Th Delta il) L) (real_mult T L))
        by exact (real_mult_lt_compat (ti_Th Delta il) T L HT2T HL0).
      assert (Hb : real_eq (real_mult (ti_Th Delta il) L)
                           (real_plus twoD L)).
      { apply (real_eq_trans
                 (real_mult (ti_Th Delta il) L)
                 (real_plus (real_mult twoD (real_mult L il)) L)
                 (real_plus twoD L)).
        - apply (real_eq_trans
                   (real_mult (ti_Th Delta il) L)
                   (real_mult L (ti_Th Delta il))
                   (real_plus (real_mult twoD (real_mult L il)) L)).
          + apply real_mult_comm.
          + exact (tw_ring_t2 Delta L il).
        - apply (RealSetoid.real_eq_plus_compat
                   (real_mult twoD (real_mult L il)) L twoD L).
          + apply (real_eq_trans (real_mult twoD (real_mult L il))
                     (real_mult twoD real_one) twoD).
            * apply (RealSetoid.real_eq_mult_compat twoD (real_mult L il)
                       twoD real_one (real_eq_refl twoD)
                       (real_inv_pos_correct L HL0)).
            * apply real_mult_one.
          + apply real_eq_refl. }
      assert (HinvT : real_lt real_zero (real_inv_pos T Ht))
        by apply real_inv_pos_pos.
      assert (Hc : real_lt (real_plus twoD L) (real_mult T L))
        by exact (real_eq_lt_lt (real_plus twoD L)
                    (real_mult (ti_Th Delta il) L) (real_mult T L)
                    (real_eq_sym _ _ Hb) Ha).
      assert (Hd : real_lt (real_mult (real_plus twoD L) (real_inv_pos T Ht))
                           (real_mult (real_mult T L) (real_inv_pos T Ht)))
        by exact (real_mult_lt_compat (real_plus twoD L) (real_mult T L)
                    (real_inv_pos T Ht) Hc HinvT).
      assert (He : real_eq (real_mult (real_mult T L) (real_inv_pos T Ht)) L).
      { apply (real_eq_trans
                 (real_mult (real_mult T L) (real_inv_pos T Ht))
                 (real_mult (real_mult T (real_inv_pos T Ht)) L) L).
        - apply tw_ring_abc_acb.
        - apply (real_eq_trans
                   (real_mult (real_mult T (real_inv_pos T Ht)) L)
                   (real_mult real_one L) L).
          + apply (RealSetoid.real_eq_mult_compat
                     (real_mult T (real_inv_pos T Ht)) L real_one L
                     (real_inv_pos_correct T Ht) (real_eq_refl L)).
          + apply tw_ring_mult_one_l. }
      assert (Hf : real_lt (real_mult (real_plus twoD L)
                                 (real_inv_pos T Ht)) L)
        by exact (real_lt_eq_lt (real_mult (real_plus twoD L)
                                      (real_inv_pos T Ht))
                   (real_mult (real_mult T L) (real_inv_pos T Ht)) L
                   Hd He).
      assert (HddT : real_eq (real_mult (real_plus twoD L)
                                   (real_inv_pos T Ht))
                             (real_plus (real_mult twoD (real_inv_pos T Ht))
                                (real_mult L (real_inv_pos T Ht))))
        by exact (tw_ring_ddl Delta L (real_inv_pos T Ht)).
      assert (HLiT : real_lt real_zero (real_mult L (real_inv_pos T Ht)))
        by (apply (real_mult_pos_compat L (real_inv_pos T Ht));
            [exact HL0 | exact HinvT]).
      assert (Hh : real_lt (real_plus (real_mult twoD (real_inv_pos T Ht))
                                (real_mult L (real_inv_pos T Ht))) L)
        by exact (real_eq_lt_lt
                    (real_plus (real_mult twoD (real_inv_pos T Ht))
                       (real_mult L (real_inv_pos T Ht)))
                    (real_mult (real_plus twoD L) (real_inv_pos T Ht)) L
                    (real_eq_sym _ _ HddT) Hf).
      assert (Hi : real_lt (real_mult twoD (real_inv_pos T Ht)) L).
      { apply (real_lt_trans (real_mult twoD (real_inv_pos T Ht))
                 (real_plus (real_mult twoD (real_inv_pos T Ht))
                    (real_mult L (real_inv_pos T Ht))) L).
        - apply tw_lt_plus_r_zero. exact HLiT.
        - exact Hh. }
      assert (Hj : real_lt (cauchy_real_exp
                              (real_mult twoD (real_inv_pos T Ht)))
                           (real_plus real_one eps))
        by exact (real_lt_eq_lt
                    (cauchy_real_exp (real_mult twoD (real_inv_pos T Ht)))
                    (cauchy_real_exp L) (real_plus real_one eps)
                    (cauchy_real_exp_mono
                       (real_mult twoD (real_inv_pos T Ht)) L Hi)
                    (cw_log_exp_right (real_plus real_one eps)
                       (ti_one_eps_pos eps Heps))).
      unfold ti_err.
      apply (real_le_trans
               (real_plus (cauchy_real_exp
                             (real_mult twoD (real_inv_pos T Ht)))
                          (real_opp real_one))
               (real_plus (real_plus real_one eps) (real_opp real_one))
               eps).
      * apply real_le_plus_compat; [exact (inl Hj) | apply real_le_refl].
      * apply tw_eq_le. exact (tw_ring_one_eps_minus eps).
    + (* Branch 2: global monotonicity, a direct application of [ti_err_antitone]. *)
      intros T T' Ht Ht' Hle.
      exact (ti_err_antitone Delta T T' HD Ht Ht' Hle).
Qed.

(* ================== Section 5. The explicit low-temperature threshold [ti_T0], the counterpart of the [hard_attention_limit] endpoint of [AttnHardLimit218]; its threshold-completion property is delivered in Section 7. ================== *)

Definition ti_T0 (gamma il : Real) : Real := real_mult gamma il.

Lemma ti_T0_pos : forall (gamma il : Real) (Hg : real_lt real_zero gamma)
                          (Hil : real_lt real_zero il),
  real_lt real_zero (ti_T0 gamma il).
Proof.
  intros gamma il Hg Hil. unfold ti_T0.
  exact (real_mult_pos_compat gamma il Hg Hil).
Qed.

(* ================== Section 6. Bridge to the endpoint world: the uniform TV distance of [UpTempWindow] is bounded pointwise by the error function ([tv_unif <= ti_err Delta T]); this is the consistency link between the full-range description and the endpoint modules. ================== *)

Lemma ti_tv_unif_le_err :
  forall (Tok : Set) (states : list Tok) (Hne : Not (Id states nil))
         (zz : Tok -> Real) (Delta : Real) (HD : real_lt real_zero Delta)
         (Hlo : forall x : Tok, real_le (real_opp Delta) (zz x))
         (Hhi : forall x : Tok, real_le (zz x) Delta)
         (T : Real) (Ht : real_lt real_zero T),
    real_le (tv_unif Tok states Hne zz T Ht)
            (ti_err Delta T Ht).
Proof.
  intros Tok states Hne zz Delta HD Hlo Hhi T Ht.
  exact (tv_unif_le Tok states Hne zz Delta HD Hlo Hhi T Ht).
Qed.

(* ================== Inventory: 10 proof items and 3 definition items ([ti_err], [ti_Th], [ti_T0]). ================== *)

(* The witness position of the main statement [ti_temp_interp] is an explicit function
   (not a search): it upgrades the existential threshold [exists T2] of the
   high-temperature endpoint [temp_window_T_infty] to the named threshold [ti_Th] with
   its positivity lemma [ti_Th_pos] and the completion branch of the main statement;
   the global interpolation semantics is the monotone skeleton of the second branch. *)

Print Assumptions ti_temp_interp.
Print Assumptions ti_err_antitone.
Print Assumptions ti_tv_unif_le_err.

(* ================== Section 7. Incremental part (low-temperature completion): replay of the threshold-completion property for [ti_T0]. ================== *)

(* This replays the proof body of the corresponding Section inside [AttnHardLimit218]
   [hard_attention_limit] as top-level statements outside that Section.  Two facts fix
   the statement shapes.  First, the Section arguments are all named explicitly, and
   which of them disappear in the exported statements was checked by [About]:
   [tv_hard] takes 6+2 arguments (no [gamma]), [tv_hard_le_decay_scale] takes 11 (it
   needs [gap_le], not [gamma_pos]), and [vocab_len_pos] takes 7.  Second, the inner
   machinery of [h_abs] and [decay_T] (about 150 lines: [hsum_split], [hsum_nonm_le]
   and their siblings) is not rebuilt: the exported lemma [tv_hard_le_decay_scale] is
   used directly. *)

From Stdlib Require Import List.

Theorem ti_hard_threshold :
  forall (Tok : Set) (vocab : list Tok) (Hne : Not (Id vocab nil))
         (Hdec : forall a b : Tok, Or (Id a b) (Not (Id a b)))
         (zz : Tok -> Real)
         (m : Tok) (Hmv : InT m vocab)
         (Hmc : @Id nat (count_token Tok Hdec m vocab) (Datatypes.S O))
         (gamma : Real) (Hg : real_lt real_zero gamma)
         (Hgap : forall x : Tok, Not (Id x m) ->
                   real_le (real_plus (zz x) gamma) (zz m))
         (eps : Real) (Heps : real_lt real_zero eps),
    sigT (fun T0 => And (real_lt real_zero T0)
      (forall (T : Real) (Ht : real_lt real_zero T), real_lt T T0 ->
        real_le (tv_hard Tok vocab Hne Hdec zz m T Ht) eps)).
Proof.
  intros Tok vocab Hne Hdec zz m Hmv Hmc gamma Hg Hgap eps Heps.
  set (N := length vocab).
  set (EN := real_of_nat N).
  set (M := real_mult EN (real_inv_pos eps Heps)).
  set (ylog := real_plus M real_one).
  assert (HM : real_lt real_zero M).
  { apply real_mult_pos_compat.
    - exact (vocab_len_pos Tok vocab Hne Hdec m Hmv Hmc).
    - apply real_inv_pos_pos. }
  assert (Hy : real_lt real_zero ylog).
  { apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero) _).
    - apply real_eq_sym. apply real_plus_zero.
    - apply real_lt_plus_compat.
      + exact HM.
      + apply real_lt_zero_one. }
  assert (Hy1 : real_lt real_one ylog).
  { apply (real_eq_lt_lt real_one (real_plus real_zero real_one) ylog).
    - apply (real_eq_trans _ (real_plus real_one real_zero) _).
      + apply real_eq_sym. exact (real_plus_comm real_zero real_one).
      + exact (real_plus_zero real_one).
    - apply (real_lt_plus_compat_lt_le real_zero M real_one real_one HM
               (real_le_refl real_one)). }
  assert (HL : real_lt real_zero (cw_log ylog Hy)).
  { apply exp_reflects_lt.
    apply (real_eq_lt_lt (cauchy_real_exp real_zero) real_one
             (cauchy_real_exp (cw_log ylog Hy))).
    - exact cauchy_real_exp_zero.
    - apply (real_lt_eq_lt real_one ylog (cauchy_real_exp (cw_log ylog Hy))).
      + exact Hy1.
      + exact (real_eq_sym (cauchy_real_exp (cw_log ylog Hy)) ylog
                 (cw_log_exp_right ylog Hy)). }
  exists (ti_T0 gamma (real_inv_pos (cw_log ylog Hy) HL)). split.
  - apply (ti_T0_pos gamma (real_inv_pos (cw_log ylog Hy) HL) Hg).
    apply real_inv_pos_pos.
  - intros T Ht Hlt.
    set (invT := real_inv_pos T Ht).
    assert (HinvT : real_lt real_zero invT) by apply real_inv_pos_pos.
    set (a := real_mult invT gamma).
    (* Step 1: [T * L < gamma]. *)
    assert (Hs1 : real_lt (real_mult T (cw_log ylog Hy)) gamma).
    { apply (real_lt_eq_lt (real_mult T (cw_log ylog Hy))
               (real_mult (real_mult gamma (real_inv_pos (cw_log ylog Hy) HL))
                  (cw_log ylog Hy)) gamma).
      - apply (real_mult_lt_compat T
                  (real_mult gamma (real_inv_pos (cw_log ylog Hy) HL))
                  (cw_log ylog Hy) Hlt HL).
      - apply (real_eq_trans _
                 (real_mult gamma
                    (real_mult (real_inv_pos (cw_log ylog Hy) HL)
                               (cw_log ylog Hy))) _).
        + apply real_eq_sym. apply real_mult_assoc.
        + apply (real_eq_trans _
                   (real_mult gamma
                      (real_mult (cw_log ylog Hy)
                         (real_inv_pos (cw_log ylog Hy) HL))) _).
          * apply (RealSetoid.real_eq_mult_compat gamma
                     (real_mult (real_inv_pos (cw_log ylog Hy) HL)
                                (cw_log ylog Hy))
                     gamma
                     (real_mult (cw_log ylog Hy)
                                (real_inv_pos (cw_log ylog Hy) HL))).
            -- apply real_eq_refl.
            -- apply real_mult_comm.
          * apply (real_eq_trans _ (real_mult gamma real_one) _).
            -- apply (RealSetoid.real_eq_mult_compat gamma
                        (real_mult (cw_log ylog Hy)
                           (real_inv_pos (cw_log ylog Hy) HL)) gamma real_one).
               ++ apply real_eq_refl.
               ++ apply (real_inv_pos_correct (cw_log ylog Hy) HL).
            -- apply real_mult_one. }
    (* Step 2: [L < gamma / T]. *)
    assert (Hs2 : real_lt (cw_log ylog Hy) a).
    { assert (Hmul : real_lt (real_mult invT (real_mult T (cw_log ylog Hy)))
                             (real_mult invT gamma))
        by (apply (real_mult_lt_compat_l _ _ invT Hs1 HinvT)).
      apply (real_lt_eq_lt (cw_log ylog Hy) (real_mult invT gamma) a).
      + apply (real_eq_lt_lt (cw_log ylog Hy)
                 (real_mult invT (real_mult T (cw_log ylog Hy)))
                 (real_mult invT gamma)).
        * apply real_eq_sym.
          exact (real_eq_trans _ _ _
                   (real_eq_trans _ _ _
                     (real_eq_trans _ _ _
                       (real_mult_assoc invT T (cw_log ylog Hy))
                       (RealSetoid.real_eq_mult_compat
                          (real_mult invT T) (cw_log ylog Hy)
                          (real_mult T invT) (cw_log ylog Hy)
                          (real_mult_comm invT T)
                          (real_eq_refl (cw_log ylog Hy))))
                     (RealSetoid.real_eq_mult_compat
                        (real_mult T invT) (cw_log ylog Hy)
                        real_one (cw_log ylog Hy)
                        (real_inv_pos_correct T Ht)
                        (real_eq_refl (cw_log ylog Hy))))
                   (real_eq_trans _ _ _
                     (real_mult_comm real_one (cw_log ylog Hy))
                     (real_mult_one (cw_log ylog Hy)))).
        * exact Hmul.
      + apply real_eq_refl. }
    (* Step 3: [M <= e^(gamma/T)]. *)
    assert (Hs3 : real_le M (cauchy_real_exp a)).
    { apply (real_le_trans _ (cauchy_real_exp (cw_log ylog Hy)) _).
      - apply (RealSetoid.real_le_id_r M ylog
                 (cauchy_real_exp (cw_log ylog Hy))).
        + exact (real_eq_sym (cauchy_real_exp (cw_log ylog Hy)) ylog
                   (cw_log_exp_right ylog Hy)).
        + apply real_le_plus_nonneg_r_aux.
          apply real_le_from_lt_aux. apply real_lt_zero_one.
      - apply real_exp_le_mono. exact (real_le_from_lt_aux _ _ Hs2). }
    (* Step 4: [N <= eps * e^(gamma/T)]. *)
    assert (Hs4 : real_le EN (real_mult eps (cauchy_real_exp a))).
    { apply (RealSetoid.real_le_id_l EN (real_mult eps M) _).
      - exact (real_eq_sym _ _
          (real_eq_trans _ _ _
            (real_mult_assoc eps EN (real_inv_pos eps Heps))
            (real_eq_trans _ _ _
              (RealSetoid.real_eq_mult_compat
                 (real_mult eps EN) (real_inv_pos eps Heps)
                 (real_mult EN eps) (real_inv_pos eps Heps)
                 (real_mult_comm eps EN)
                 (real_eq_refl (real_inv_pos eps Heps)))
              (real_eq_trans _ _ _
                (real_eq_sym _ _ (real_mult_assoc EN eps (real_inv_pos eps Heps)))
                (real_eq_trans _ _ _
                  (RealSetoid.real_eq_mult_compat
                     EN (real_mult eps (real_inv_pos eps Heps))
                     EN real_one
                     (real_eq_refl EN) (real_inv_pos_correct eps Heps))
                  (real_mult_one EN)))))).
      - apply (real_le_mult_compat_l_aux M (cauchy_real_exp a) eps
                 Heps Hs3). }
    (* Step 5: [e^(-gamma/T) * N <= eps]. *)
    assert (Hs5 : real_le
                    (real_mult (cauchy_real_exp (real_opp a)) EN) eps).
    { apply (RealSetoid.real_le_id_r
               (real_mult (cauchy_real_exp (real_opp a)) EN)
               (real_mult (cauchy_real_exp (real_opp a))
                  (real_mult eps (cauchy_real_exp a))) eps).
      - apply (real_eq_trans _
                 (real_mult (cauchy_real_exp (real_opp a))
                            (real_mult (cauchy_real_exp a) eps)) _).
        + apply (RealSetoid.real_eq_mult_compat
                    (cauchy_real_exp (real_opp a))
                    (real_mult eps (cauchy_real_exp a))
                    (cauchy_real_exp (real_opp a))
                    (real_mult (cauchy_real_exp a) eps)).
          * apply real_eq_refl.
          * apply real_mult_comm.
        + apply (real_eq_trans _
                     (real_mult
                        (real_mult (cauchy_real_exp (real_opp a))
                                   (cauchy_real_exp a))
                        eps) _).
          * apply real_mult_assoc.
          * apply (real_eq_trans _ (real_mult real_one eps) _).
            -- apply (RealSetoid.real_eq_mult_compat
                        (real_mult (cauchy_real_exp (real_opp a))
                                   (cauchy_real_exp a))
                        eps
                        real_one eps).
               ++ apply exp_mult_opp_l_aux.
               ++ apply real_eq_refl.
            -- apply (real_eq_trans _ (real_mult eps real_one) _).
               ++ apply real_mult_comm.
               ++ apply real_mult_one.
      - apply (real_le_mult_compat_l_aux EN
                 (real_mult eps (cauchy_real_exp a))
                 (cauchy_real_exp (real_opp a))).
        + apply cauchy_real_exp_pos.
        + exact Hs4. }
    (* Completion: [tv_hard <= N * e^(-gamma/T) <= e^(-gamma/T) * N <= eps]. *)
    apply (real_le_trans _
             (real_mult (real_of_nat N)
                        (decay_T gamma T Ht)) _).
    + exact (tv_hard_le_decay_scale Tok vocab Hne Hdec zz m Hmv Hmc
               gamma Hgap T Ht).
    + apply (real_le_trans _
               (real_mult (cauchy_real_exp (real_opp a)) (real_of_nat N)) _).
      * apply (RealSetoid.real_eq_le). apply real_mult_comm.
      * exact Hs5.
Qed.

Print Assumptions ti_hard_threshold.

(* Inventory addendum: the proof items of this file go from 10 to 11 (adding
   [ti_hard_threshold]); the definition items stay at 3 ([ti_err], [ti_Th], [ti_T0]).
   The existential threshold [exists T0] of the low-temperature endpoint
   [hard_attention_limit] is upgraded to the named function [ti_T0] with its positivity
   lemma [ti_T0_pos] and the completion statement [ti_hard_threshold]; both temperature
   extremes (high: [ti_temp_interp], low: [ti_hard_threshold]) now carry the
   explicit-threshold plus quantitative-bound shape. *)
