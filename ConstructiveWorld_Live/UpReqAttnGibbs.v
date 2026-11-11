(* ConstructiveWorld-Set — req-layer attention Gibbs/softmax family: temperature annealing, the Boltzmann correspondence, eviction and the Top-K TV identity. *)

(** * UpReqAttnGibbs: req-layer construction of the attention Gibbs/softmax family.

    Mission.  The unit-temperature softmax mixture ([ag_softmax_mix_normalized],
      [ag_softmax_is_prob]); the temperature-annealed and scaled families
      with their duality in temperature ([ag_temp_is_scale_duality]); the
      Boltzmann correspondence ([ag_attention_is_gibbs_temp]); the eviction,
      top-k tail and Top-K TV clusters ([ag_evicted_boltzmann_normalized],
      [ag_topk_tv_identity_strict]); the eps-wise machine: gap concentration,
      zero-temperature limit, hard-attention collapse ([ag_sum_le_r_max_eps],
      [ag_hard_attention_collapse_eps]).

    Dependencies.  Stdlib [List] with [ListNotations]; requires [S01_BaseRing]
      through [S15_TailFEPUp] plus [UpReqAlgebra], [UpReqDist], [UpReqCauchy]
      of this development; imports [RealInterfaceEnhancedMod].

    References.  This development; the baseline module CW_ConstructiveWorld_219
      (Section AttentionGibbsBridge, first segment = the softmax family) of
      ConstructiveWorld-Main, whose statement names are carried over verbatim;
      already-migrated prerequisites are consumed as given; not carried over:
      the list machinery; the [eviction_db] row keeps its distinct form.

    Constructivity.  Statements on the [Set] layer (carriers [req], [lt], [le],
      [req_minus]); pure term-mode [req_trans]/compat-chain proofs; every
      interface gap is an explicit section premise; [Print Assumptions] audit.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      ConstructiveWorld_Live/UpReqAttnGibbs.v] compiles cleanly (exit 0);
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
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqCauchy.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the global Real
   (S07_RealSetoidExpLog.v:8075 zero-argument Class RealInterfaceEnhancedSetoid + global
   Instance RealEnhancedReal; Notation passthrough per the world's own UpReqAlign3.v
   precedent). *)
Notation R := Real.

(* ============================================================ *)
(* Section ReqAttnGibbs: req-layer migration of the first segment  *)
(*   of the baseline AttentionGibbsBridge.  The summation honest   *)
(*   interface = the Id SumOver triple of properties plus [add],   *)
(*   as in the baseline Setoid section.                            *)
(* ============================================================ *)
Section ReqAttnGibbs.
(* A-face adaptation (M43 nw10cure, per UpReqAlign3.v precedent): the argument-bearing
   generation binders Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}. are
   deleted; the carrier R is bound to the global Real by the file-top Notation above,
   and the class fields (req/lt/le/zero/one/plus/mult/opp/abs/inv_pos/exp_neg) resolve
   through the global instance RealEnhancedReal. Zero magic constructors, zero
   Prop casts, statement faces and premise positions preserved verbatim. *)

Variable S : Set.
Variable sumf : (S -> R) -> R.

Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).

(* the temperature (the Id Variables [T]/[T_pos], carried at matching req positions). *)
Variable T : R.
Variable T_pos : lt zero T.

(* ---- auxiliary: [a + (1 − a) == one] (the tail chain shared by the mixture family; genuinely proved) ---- *)
Lemma aux_alpha_plus_omda : forall a : R, req (plus a (req_minus one a)) one.
Proof.
  intro a.
  apply (req_trans _ (plus (plus a one) (opp a)) _).
  - exact (plus_assoc a one (opp a)).
  - apply (req_trans (plus (plus a one) (opp a))
                     (plus (plus one a) (opp a)) _).
    + exact (req_plus_compat (plus a one) (plus one a) (opp a) (opp a)
                (plus_comm a one) (req_refl _)).
    + apply (req_trans (plus (plus one a) (opp a))
                       (plus one (plus a (opp a))) _).
      * exact (req_sym _ _ (plus_assoc one a (opp a))).
      * apply (req_trans (plus one (plus a (opp a))) (plus one zero) one).
        -- exact (req_plus_compat one one (plus a (opp a)) zero
                      (req_refl one) (plus_opp a)).
        -- exact (plus_zero one).
Qed.

(* ---- the unit-temperature softmax family (depends on the baseline [softmax_setoid] family) ---- *)

(* normalization is preserved under convex combinations (assembled from the sum interfaces). *)
Theorem ag_softmax_mix_normalized :
  forall (z z' : S -> R) (alpha : R) (Halpha : lt zero alpha)
         (Halpha1 : lt zero (req_minus one alpha)),
    req (sumf (fun s : S =>
            plus (mult alpha (softmax_setoid S sumf sum_pos z s))
                 (mult (req_minus one alpha)
                       (softmax_setoid S sumf sum_pos z' s))))
        one.
Proof.
  intros z z' alpha Halpha Halpha1.
  assert (Hp : req (sumf (fun s : S => softmax_setoid S sumf sum_pos z s)) one)
    by exact (softmax_normalized_setoid S sumf sum_ext sum_linear sum_pos z).
  assert (Hq : req (sumf (fun s : S => softmax_setoid S sumf sum_pos z' s)) one)
    by exact (softmax_normalized_setoid S sumf sum_ext sum_linear sum_pos z').
  apply (req_trans _ (plus
        (sumf (fun s : S => mult alpha (softmax_setoid S sumf sum_pos z s)))
        (sumf (fun s : S => mult (req_minus one alpha)
                                 (softmax_setoid S sumf sum_pos z' s)))) _).
  - exact (sum_add (fun s : S => mult alpha (softmax_setoid S sumf sum_pos z s))
                   (fun s : S => mult (req_minus one alpha)
                                      (softmax_setoid S sumf sum_pos z' s))).
  - apply (req_trans _ (plus
        (mult alpha (sumf (fun s : S => softmax_setoid S sumf sum_pos z s)))
        (mult (req_minus one alpha)
              (sumf (fun s : S => softmax_setoid S sumf sum_pos z' s)))) _).
    + exact (req_plus_compat _ _ _ _
               (sum_linear alpha (fun s : S => softmax_setoid S sumf sum_pos z s))
               (sum_linear (req_minus one alpha)
                           (fun s : S => softmax_setoid S sumf sum_pos z' s))).
    + apply (req_trans _ (plus (mult alpha one)
                               (mult (req_minus one alpha) one)) _).
      * exact (req_plus_compat _ _ _ _
                   (req_mult_compat alpha alpha
                      (sumf (fun s : S => softmax_setoid S sumf sum_pos z s)) one
                      (req_refl alpha) Hp)
                   (req_mult_compat (req_minus one alpha) (req_minus one alpha)
                      (sumf (fun s : S => softmax_setoid S sumf sum_pos z' s)) one
                      (req_refl (req_minus one alpha)) Hq)).
      * apply (req_trans _ (plus alpha (req_minus one alpha)) _).
        -- exact (req_plus_compat (mult alpha one) alpha
                       (mult (req_minus one alpha) one) (req_minus one alpha)
                       (mult_one alpha) (mult_one (req_minus one alpha))).
        -- exact (aux_alpha_plus_omda alpha).
Qed.

(* the softmax is a probability distribution (positivity + normalization; assembled). *)
Theorem ag_softmax_is_prob :
  forall z : S -> R,
    And (forall s : S, le zero (softmax_setoid S sumf sum_pos z s))
        (req (sumf (fun s : S => softmax_setoid S sumf sum_pos z s)) one).
Proof.
  intro z. split.
  - intro s. exact (lt_le_iff _ _ (inl (softmax_pos_setoid S sumf sum_pos z s))).
  - exact (softmax_normalized_setoid S sumf sum_ext sum_linear sum_pos z).
Qed.

(* ---- the temperature-annealed family (baseline L28195 region; depends on [reqd_softmax_temp_param]) ---- *)

Definition partition_function_temp_r (z : S -> R) : R :=
  sumf (fun s : S => exp_pos_fn_setoid (mult (inv_pos T T_pos) (z s))).

Lemma ag_partition_function_temp_pos :
  forall z : S -> R, lt zero (partition_function_temp_r z).
Proof.
  intro z. unfold partition_function_temp_r.
  apply sum_pos.
  intro s. exact (exp_neg_pos (opp (mult (inv_pos T T_pos) (z s)))).
Qed.

Lemma ag_softmax_temp_pos :
  forall (z : S -> R) (s : S),
    lt zero (reqd_softmax_temp_param S sumf sum_pos T T_pos z s).
Proof.
  intros z s.
  unfold reqd_softmax_temp_param.
  pose (Pw := (fun s0 : S => exp_neg (mult (inv_pos T T_pos) (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult (inv_pos T T_pos) (z s0))))).
  exact (mult_positive (exp_neg (mult (inv_pos T T_pos) (z s)))
                       (inv_pos (sumf Pw) Wp)
                       (exp_neg_pos (mult (inv_pos T T_pos) (z s)))
                       (inv_pos_pos (sumf Pw) Wp)).
Qed.

Lemma ag_softmax_temp_normalized :
  forall z : S -> R,
    req (sumf (fun s : S =>
           reqd_softmax_temp_param S sumf sum_pos T T_pos z s)) one.
Proof.
  intro z.
  unfold reqd_softmax_temp_param.
  pose (Pw := (fun s0 : S => exp_neg (mult (inv_pos T T_pos) (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult (inv_pos T T_pos) (z s0))))).
  pose (IV := (inv_pos (sumf Pw) Wp)).
  apply (req_trans _ (sumf (fun s : S => mult IV (exp_neg (mult (inv_pos T T_pos) (z s))))) _).
  - apply (sum_ext (fun s : S => mult (exp_neg (mult (inv_pos T T_pos) (z s))) IV)
                   (fun s : S => mult IV (exp_neg (mult (inv_pos T T_pos) (z s))))).
    intro s. exact (mult_comm (exp_neg (mult (inv_pos T T_pos) (z s))) IV).
  - apply (req_trans _ (mult IV (sumf Pw)) _).
    + exact (sum_linear IV Pw).
    + exact (req_trans _ _ _ (mult_comm IV (sumf Pw)) (inv_pos_correct (sumf Pw) Wp)).
Qed.

(* normalization is preserved under convex combinations of the temperature-annealed softmax (assembled). *)
Theorem ag_softmax_temp_mix_normalized :
  forall (z z' : S -> R) (alpha : R) (Halpha : lt zero alpha)
         (Halpha1 : lt zero (req_minus one alpha)),
    req (sumf (fun s : S =>
            plus (mult alpha
                       (reqd_softmax_temp_param S sumf sum_pos T T_pos z s))
                 (mult (req_minus one alpha)
                       (reqd_softmax_temp_param S sumf sum_pos T T_pos z' s))))
        one.
Proof.
  intros z z' alpha Halpha Halpha1.
  assert (Hp : req (sumf (fun s : S =>
                   reqd_softmax_temp_param S sumf sum_pos T T_pos z s)) one)
    by exact (ag_softmax_temp_normalized z).
  assert (Hq : req (sumf (fun s : S =>
                   reqd_softmax_temp_param S sumf sum_pos T T_pos z' s)) one)
    by exact (ag_softmax_temp_normalized z').
  apply (req_trans _ (plus
        (sumf (fun s : S =>
           mult alpha (reqd_softmax_temp_param S sumf sum_pos T T_pos z s)))
        (sumf (fun s : S =>
           mult (req_minus one alpha)
                (reqd_softmax_temp_param S sumf sum_pos T T_pos z' s)))) _).
  - exact (sum_add
             (fun s : S => mult alpha (reqd_softmax_temp_param S sumf sum_pos T T_pos z s))
             (fun s : S => mult (req_minus one alpha)
                                (reqd_softmax_temp_param S sumf sum_pos T T_pos z' s))).
  - apply (req_trans _ (plus
        (mult alpha (sumf (fun s : S =>
                    reqd_softmax_temp_param S sumf sum_pos T T_pos z s)))
        (mult (req_minus one alpha)
              (sumf (fun s : S =>
                    reqd_softmax_temp_param S sumf sum_pos T T_pos z' s)))) _).
    + exact (req_plus_compat _ _ _ _
               (sum_linear alpha
                  (fun s : S => reqd_softmax_temp_param S sumf sum_pos T T_pos z s))
               (sum_linear (req_minus one alpha)
                  (fun s : S => reqd_softmax_temp_param S sumf sum_pos T T_pos z' s))).
    + apply (req_trans _ (plus (mult alpha one)
                               (mult (req_minus one alpha) one)) _).
      * exact (req_plus_compat _ _ _ _
                   (req_mult_compat alpha alpha
                      (sumf (fun s : S => reqd_softmax_temp_param S sumf sum_pos T T_pos z s)) one
                      (req_refl alpha) Hp)
                   (req_mult_compat (req_minus one alpha) (req_minus one alpha)
                      (sumf (fun s : S => reqd_softmax_temp_param S sumf sum_pos T T_pos z' s)) one
                      (req_refl (req_minus one alpha)) Hq)).
      * apply (req_trans _ (plus alpha (req_minus one alpha)) _).
        -- exact (req_plus_compat (mult alpha one) alpha
                       (mult (req_minus one alpha) one) (req_minus one alpha)
                       (mult_one alpha) (mult_one (req_minus one alpha))).
        -- exact (aux_alpha_plus_omda alpha).
Qed.

(* relative form: [softmax_temp z s == softmax_temp z s' · e^{-(z s - z s')/T}]
   (a genuine signature change: the Id [softmax_temp] family uses the
   [exp_pos] convention [e^{+z/T}] while [reqd_softmax_temp_param]
   uses the Boltzmann convention [e^{-z/T}], so the relative-form
   factor moves from [exp_pos_fn (invT·Δz)] to [exp_neg (invT·Δz)];
   genuinely proved: additivity of [exp] plus a [req_minus]
   rearrangement chain). *)
Theorem ag_softmax_temp_relative :
  forall (z : S -> R) (s s' : S),
    req (reqd_softmax_temp_param S sumf sum_pos T T_pos z s)
        (mult (reqd_softmax_temp_param S sumf sum_pos T T_pos z s')
              (exp_neg (mult (inv_pos T T_pos) (req_minus (z s) (z s'))))).
Proof.
  intros z s s'.
  assert (Hzs : req (z s) (plus (z s') (req_minus (z s) (z s')))).
  { exact (req_sym _ _ (req_minus_plus_cancel (z s') (z s))). }
  assert (Hf : req (exp_neg (mult (inv_pos T T_pos) (z s)))
                   (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                         (exp_neg (mult (inv_pos T T_pos)
                                       (req_minus (z s) (z s')))))).
  { exact (req_trans
             (exp_neg (mult (inv_pos T T_pos) (z s)))
             (exp_neg (plus (mult (inv_pos T T_pos) (z s'))
                            (mult (inv_pos T T_pos)
                                  (req_minus (z s) (z s')))))
             (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                   (exp_neg (mult (inv_pos T T_pos)
                                  (req_minus (z s) (z s')))))
             (exp_neg_req_compat_setoid
                (mult (inv_pos T T_pos) (z s))
                (plus (mult (inv_pos T T_pos) (z s'))
                      (mult (inv_pos T T_pos) (req_minus (z s) (z s'))))
                (req_trans (mult (inv_pos T T_pos) (z s))
                           (mult (inv_pos T T_pos)
                                 (plus (z s') (req_minus (z s) (z s'))))
                           (plus (mult (inv_pos T T_pos) (z s'))
                                 (mult (inv_pos T T_pos)
                                       (req_minus (z s) (z s'))))
                           (req_mult_compat (inv_pos T T_pos)
                              (inv_pos T T_pos) (z s)
                              (plus (z s') (req_minus (z s) (z s')))
                              (req_refl _) Hzs)
                           (distrib (inv_pos T T_pos) (z s')
                                    (req_minus (z s) (z s')))))
             (exp_neg_plus (mult (inv_pos T T_pos) (z s'))
                           (mult (inv_pos T T_pos)
                                 (req_minus (z s) (z s'))))). }
  unfold reqd_softmax_temp_param.
  pose (Pw := (fun s0 : S => exp_neg (mult (inv_pos T T_pos) (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult (inv_pos T T_pos) (z s0))))).
  pose (IV := (inv_pos (sumf Pw) Wp)).
  assert (Has : req (mult (exp_neg (mult (inv_pos T T_pos) (z s))) IV)
                   (mult IV
                      (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                            (exp_neg (mult (inv_pos T T_pos)
                                           (req_minus (z s) (z s'))))))).
  { apply (req_trans _ (mult IV (exp_neg (mult (inv_pos T T_pos) (z s)))) _).
    - exact (mult_comm (exp_neg (mult (inv_pos T T_pos) (z s))) IV).
    - exact (req_mult_compat IV IV (exp_neg (mult (inv_pos T T_pos) (z s)))
                (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                      (exp_neg (mult (inv_pos T T_pos)
                                     (req_minus (z s) (z s')))))
                (req_refl _) Hf). }
  assert (Har : req (mult IV
                       (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                             (exp_neg (mult (inv_pos T T_pos)
                                            (req_minus (z s) (z s'))))))
                   (mult (mult (exp_neg (mult (inv_pos T T_pos) (z s'))) IV)
                         (exp_neg (mult (inv_pos T T_pos)
                                        (req_minus (z s) (z s')))))).
  { exact (req_trans
             (mult IV
                (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                      (exp_neg (mult (inv_pos T T_pos)
                                     (req_minus (z s) (z s'))))))
             (mult (mult IV (exp_neg (mult (inv_pos T T_pos) (z s'))))
                   (exp_neg (mult (inv_pos T T_pos)
                                  (req_minus (z s) (z s')))))
             (mult (mult (exp_neg (mult (inv_pos T T_pos) (z s'))) IV)
                   (exp_neg (mult (inv_pos T T_pos)
                                  (req_minus (z s) (z s')))))
             (mult_assoc IV (exp_neg (mult (inv_pos T T_pos) (z s')))
                (exp_neg (mult (inv_pos T T_pos)
                               (req_minus (z s) (z s')))))
             (req_mult_compat (mult IV (exp_neg (mult (inv_pos T T_pos) (z s'))))
                (mult (exp_neg (mult (inv_pos T T_pos) (z s'))) IV)
                (exp_neg (mult (inv_pos T T_pos) (req_minus (z s) (z s'))))
                (exp_neg (mult (inv_pos T T_pos) (req_minus (z s) (z s'))))
                (mult_comm IV (exp_neg (mult (inv_pos T T_pos) (z s'))))
                (req_refl _))). }
  apply (req_trans _ (mult IV
         (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
               (exp_neg (mult (inv_pos T T_pos)
                              (req_minus (z s) (z s')))))) _).
  - exact Has.
  - exact Har.
Qed.

(* ---- the scaled family (baseline L28535 region; depends on [reqd_softmax_scaled]) ---- *)

Lemma ag_partition_function_scaled_pos :
  forall (c : R) (z : S -> R),
    lt zero (sumf (fun s : S => exp_pos_fn_setoid (mult c (z s)))).
Proof.
  intros c z. apply sum_pos.
  intro s. exact (exp_neg_pos (opp (mult c (z s)))).
Qed.

Lemma ag_softmax_scaled_pos :
  forall (c : R) (z : S -> R) (s : S),
    lt zero (reqd_softmax_scaled S sumf sum_pos c z s).
Proof.
  intros c z s.
  unfold reqd_softmax_scaled.
  pose (Pw := (fun s0 : S => exp_neg (mult c (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult c (z s0))))).
  exact (mult_positive (exp_neg (mult c (z s)))
                       (inv_pos (sumf Pw) Wp)
                       (exp_neg_pos (mult c (z s)))
                       (inv_pos_pos (sumf Pw) Wp)).
Qed.

Lemma ag_softmax_scaled_normalized :
  forall (c : R) (z : S -> R),
    req (sumf (fun s : S => reqd_softmax_scaled S sumf sum_pos c z s)) one.
Proof.
  intros c z.
  unfold reqd_softmax_scaled.
  pose (Pw := (fun s0 : S => exp_neg (mult c (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult c (z s0))))).
  pose (IV := (inv_pos (sumf Pw) Wp)).
  apply (req_trans _ (sumf (fun s : S => mult IV (exp_neg (mult c (z s))))) _).
  - apply (sum_ext (fun s : S => mult (exp_neg (mult c (z s))) IV)
                   (fun s : S => mult IV (exp_neg (mult c (z s))))).
    intro s. exact (mult_comm (exp_neg (mult c (z s))) IV).
  - apply (req_trans _ (mult IV (sumf Pw)) _).
    + exact (sum_linear IV Pw).
    + exact (req_trans _ _ _ (mult_comm IV (sumf Pw)) (inv_pos_correct (sumf Pw) Wp)).
Qed.

(* ---- scale-temperature duality and the square-dimension instances (baseline L28600 region) ---- *)

(* the inverse symmetry (the delta-idempotent dual; depends on [reqd_scale_temp_duality]). *)
Lemma ag_temp_is_scale_duality :
  forall (c : R) (Hc : lt zero c) (z : S -> R) (s : S),
    req (reqd_softmax_temp_param S sumf sum_pos c Hc z s)
        (reqd_softmax_scaled S sumf sum_pos (inv_pos c Hc) z s).
Proof.
  intros c Hc z s.
  unfold reqd_softmax_temp_param, reqd_softmax_scaled.
  exact (req_refl _).
Qed.

(* the [d = 4 = 2²] witness (depends on [req_two_mult], genuinely proved). *)
Lemma ag_sq_witness_4 :
  reqd_sqrt_witness (plus (plus one one) (plus one one)) (plus one one).
Proof.
  apply (req_trans (mult (plus one one) (plus one one))
                   (plus (mult (plus one one) one) (mult (plus one one) one))
                   (plus (plus one one) (plus one one))).
  - exact (distrib (plus one one) one one).
  - exact (req_plus_compat (mult (plus one one) one) (plus one one)
                           (mult (plus one one) one) (plus one one)
                           (mult_one (plus one one)) (mult_one (plus one one))).
Qed.

(* general square-dimension duality: whenever [d = r²] (with a
   witness), scaling by [1/r] equals temperature [r] ([Hw] enters
   only in the statement accounting, isomorphic to the Id original). *)
Theorem ag_scale_sqrt_witness_dual :
  forall (d r : R) (Hr : lt zero r), reqd_sqrt_witness d r ->
  forall (z : S -> R) (s : S),
    req (reqd_softmax_scaled S sumf sum_pos (inv_pos r Hr) z s)
        (reqd_softmax_temp_param S sumf sum_pos r Hr z s).
Proof.
  intros d r Hr Hw z s.
  unfold reqd_softmax_scaled, reqd_softmax_temp_param.
  exact (req_refl _).
Qed.

(* the [d = 4] ([r = 2]) instance: [softmax(z/2)] equals the softmax at temperature 2. *)
Lemma ag_half_scale_is_temp_two :
  forall (z : S -> R) (s : S),
    req (reqd_softmax_scaled S sumf sum_pos
              (inv_pos (plus one one) req_two_pos) z s)
        (reqd_softmax_temp_param S sumf sum_pos (plus one one) req_two_pos z s).
Proof.
  intros z s.
  unfold reqd_softmax_scaled, reqd_softmax_temp_param.
  exact (req_refl _).
Qed.

(* ============================================================ *)
(*   Baseline originals: L28586-28710 (the Variables [D]/[D_pos]/  *)
(*   [energy], [boltzmann_factor]/[Z_thermo]/[boltzmann_dist_attn],*)
(*   [attention_is_gibbs_temp] L28634,                             *)
(*   [scale_inv_T_eq_softmax_temp] L28679 and                      *)
(*   [scaled_attention_is_gibbs_temp] L28694).  The earlier        *)
(*   pilot's [req_attention_is_gibbs_temp] (UpSigMigrate.v         *)
(*   ReqGibbsPilot, fixed-z form with an [exp_neg] compat bridge   *)
(*   premise) already exists; the lemmas of this section are the   *)
(*   section-parameterized [softmax_temp_r] form serving the       *)
(*   scaled composition, kept side by side under the [ag_] prefix. *)
(*   Boltzmann convention notes: [ag_attention_is_gibbs_temp] keeps*)
(*   the Id [e^{+z/T}] convention (the [exp_pos_fn_setoid] copy,   *)
(*   the factor keeps its sign); the bridge                        *)
(*   [ag_scale_inv_T_eq_softmax_temp] matches the req-native       *)
(*   [e^{-z/T}] family ([reqd_softmax_scaled]) against the         *)
(*   [e^{+z/T}] temperature family with a sign-flipped scaling     *)
(*   coefficient.                                                  *)

(* ============================================================ *)

(* ---- Boltzmann-side infrastructure (copy of the baseline L28600 region; honest Variable positions) ---- *)
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.

Definition boltzmann_factor_r (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition Z_thermo_r : R := sumf boltzmann_factor_r.

Variable Z_thermo_r_pos : lt zero Z_thermo_r.

Definition boltzmann_dist_attn_r (s : S) : R :=
  mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s).

(* the temperature-annealed softmax (the [e^{+z/T}]-convention copy;
   the denominator positivity depends directly on the earlier
   [ag_partition_function_temp_pos], no new premises). *)
Definition softmax_temp_r (z : S -> R) (s : S) : R :=
  mult (exp_pos_fn_setoid (mult (inv_pos T T_pos) (z s)))
       (inv_pos (partition_function_temp_r z) (ag_partition_function_temp_pos z)).

(* key theorem: at any temperature [softmax_temp] equals the
   Boltzmann correspondence (the reasoning temperature equals the
   physical temperature; genuinely proved: the [exp] compat bridge
   + a [req_opp_mult_l] rearrangement + unifying the normalization
   inverses by [inv_pos_ext]). *)
Theorem ag_attention_is_gibbs_temp :
  forall z : S -> R,
    req (inv_pos T T_pos) (inv_pos D D_pos) ->
    (forall s : S, req (energy s) (opp (z s))) ->
    req Z_thermo_r (partition_function_temp_r z) ->
    forall s : S, req (softmax_temp_r z s) (boltzmann_dist_attn_r s).
Proof.
  intros z HD Henergy HZ s.
  assert (Hf : req (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                   (exp_neg (mult (inv_pos D D_pos) (energy s)))).
  { apply (exp_neg_req_compat_setoid
             (opp (mult (inv_pos T T_pos) (z s)))
             (mult (inv_pos D D_pos) (energy s))).
    apply (req_trans (opp (mult (inv_pos T T_pos) (z s)))
                     (mult (inv_pos T T_pos) (opp (z s)))
                     (mult (inv_pos D D_pos) (energy s))).
    - exact (req_sym _ _ (req_opp_mult_l (inv_pos T T_pos) (z s))).
    - exact (req_mult_compat (inv_pos T T_pos) (inv_pos D D_pos)
               (opp (z s)) (energy s)
               HD (req_sym _ _ (Henergy s))). }
  assert (Hie : req (inv_pos Z_thermo_r Z_thermo_r_pos)
                    (inv_pos (partition_function_temp_r z)
                             (ag_partition_function_temp_pos z)))
    by exact (inv_pos_ext Z_thermo_r (partition_function_temp_r z)
               Z_thermo_r_pos (ag_partition_function_temp_pos z) HZ).
  unfold softmax_temp_r, boltzmann_dist_attn_r, boltzmann_factor_r,
         exp_pos_fn_setoid.
  apply (req_trans
           (mult (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                 (inv_pos (partition_function_temp_r z)
                          (ag_partition_function_temp_pos z)))
           (mult (exp_neg (mult (inv_pos D D_pos) (energy s)))
                 (inv_pos (partition_function_temp_r z)
                          (ag_partition_function_temp_pos z)))
           (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                 (exp_neg (mult (inv_pos D D_pos) (energy s))))).
  - exact (req_mult_compat _ _ _ _ Hf (req_refl _)).
  - apply (req_trans
             (mult (exp_neg (mult (inv_pos D D_pos) (energy s)))
                   (inv_pos (partition_function_temp_r z)
                            (ag_partition_function_temp_pos z)))
             (mult (inv_pos (partition_function_temp_r z)
                            (ag_partition_function_temp_pos z))
                   (exp_neg (mult (inv_pos D D_pos) (energy s))))
             (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                   (exp_neg (mult (inv_pos D D_pos) (energy s))))).
    + exact (mult_comm _ _).
    + exact (req_mult_compat _ _ _ _ (req_sym _ _ Hie) (req_refl _)).
Qed.

(* bridge: the [1/T]-scaled family (req-native [e^{-z/T}],
   sign-flipped coefficient [c := opp(1/T)]) equals the [e^{+z/T}]
   temperature family [softmax_temp_r].  In the Id original both
   sides use the [e^{+}] convention and close literally; on the req
   side crossing the [reqd_softmax_scaled] engine needs a genuine
   bridge: the sign flip of the factor [exp_neg ∘ opp] + the
   denominator by [sum_ext] + [inv_pos_ext]. *)
Lemma ag_scale_inv_T_eq_softmax_temp :
  forall (z : S -> R) (s : S),
    req (reqd_softmax_scaled S sumf sum_pos (opp (inv_pos T T_pos)) z s)
        (softmax_temp_r z s).
Proof.
  intros z s.
  pose (Pw := (fun s0 : S => exp_neg (mult (opp (inv_pos T T_pos)) (z s0)))).
  pose (Wp := (sum_pos Pw
                 (fun s0 : S => exp_neg_pos (mult (opp (inv_pos T T_pos)) (z s0))))).
  assert (Harg : forall s0 : S,
           req (mult (opp (inv_pos T T_pos)) (z s0))
               (opp (mult (inv_pos T T_pos) (z s0))))
    by (intro s0; exact (req_opp_mult_r (inv_pos T T_pos) (z s0))).
  assert (Hden : req (sumf Pw) (partition_function_temp_r z)).
  { apply (sum_ext Pw
             (fun s0 : S => exp_pos_fn_setoid (mult (inv_pos T T_pos) (z s0)))).
    intro s0. exact (exp_neg_req_compat_setoid _ _ (Harg s0)). }
  unfold reqd_softmax_scaled, softmax_temp_r, exp_pos_fn_setoid.
  apply (req_trans
           (mult (exp_neg (mult (opp (inv_pos T T_pos)) (z s)))
                 (inv_pos (sumf Pw) Wp))
           (mult (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                 (inv_pos (sumf Pw) Wp))
           (mult (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                 (inv_pos (partition_function_temp_r z)
                          (ag_partition_function_temp_pos z)))).
  - exact (req_mult_compat _ _ _ _
             (exp_neg_req_compat_setoid _ _ (Harg s)) (req_refl _)).
  - exact (req_mult_compat _ _ _ _
             (req_refl _)
             (inv_pos_ext (sumf Pw) (partition_function_temp_r z) Wp
                          (ag_partition_function_temp_pos z) Hden)).
Qed.

(* composition: the [1/T]-scaled attention equals the Boltzmann
   correspondence at temperature T (assembled: the bridge +
   [ag_attention_is_gibbs_temp]).  Reading: in the Id original
   "1/√d scaling (e^{+}) == Boltzmann at temperature √d"; on the
   req side the scaled family takes the native [e^{-}] convention
   (coefficient [opp(1/T)]) with the same conclusion strength. *)
Theorem ag_scaled_attention_is_gibbs_temp :
  forall z : S -> R,
    req (inv_pos T T_pos) (inv_pos D D_pos) ->
    (forall s : S, req (energy s) (opp (z s))) ->
    req Z_thermo_r (partition_function_temp_r z) ->
    forall s : S,
      req (reqd_softmax_scaled S sumf sum_pos (opp (inv_pos T T_pos)) z s)
          (boltzmann_dist_attn_r s).
Proof.
  intros z HD Henergy HZ s.
  apply (req_trans
           (reqd_softmax_scaled S sumf sum_pos (opp (inv_pos T T_pos)) z s)
           (softmax_temp_r z s)
           (boltzmann_dist_attn_r s)).
  - exact (ag_scale_inv_T_eq_softmax_temp z s).
  - exact (ag_attention_is_gibbs_temp z HD Henergy HZ s).
Qed.

(* ============================================================ *)
(*   Baseline originals: L29360-29626 (KV eviction:                *)
(*   detailed-balance breaking, optimal-policy support and         *)
(*   steady-state deviation quantification).  The [eviction_db]    *)
(*   pair ([eviction_db_breaking_bound] L29385 /                   *)
(*   [eviction_db_zero_full] L29573) is excluded here; this        *)
(*   section adds the honest interface premises [sum_le] (copy of  *)
(*   baseline L1415) and [abs_sum_le_r] (copy of baseline L1431),  *)
(*   in the style of the Id SumOver fields (cf. UpReqDist L206     *)
(*   [sum_le] / L1008 [fsum_le], both declared as Section          *)
(*   premises).                                                    *)
(* ============================================================ *)

Variable transition : S -> S -> R.
Variable keep : S -> Set.
Variable keep_dec : forall s : S, Or (keep s) (Not (keep s)).

Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).

Hypothesis abs_sum_le_r :
  forall f : S -> R, le (abs (sumf f)) (sumf (fun s : S => abs (f s))).

Definition evicted_transition_r (s s' : S) : R :=
  if keep_dec s then
    (if keep_dec s' then transition s s' else zero)
  else zero.

Definition evicted_partition_r : R :=
  sumf (fun s : S => if keep_dec s then boltzmann_factor_r s else zero).

Variable evicted_partition_r_pos : lt zero evicted_partition_r.

Definition evicted_boltzmann_r (s : S) : R :=
  if keep_dec s then
    mult (inv_pos evicted_partition_r evicted_partition_r_pos) (boltzmann_factor_r s)
  else zero.

(* the parameterized kept-set partition function (copy of the Id [evicted_partition_of] L29447). *)
Definition evicted_partition_of_r
  (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : R :=
  sumf (fun s : S => if kd s then boltzmann_factor_r s else zero).

(* the eviction breaking term (copy of the Id [db_breaking] L29380;
   used only by the steady-deviation statement — the breaking-bound
   and zero-breaking theorems belong to the excluded zone and are
   not migrated by this block). *)
Definition db_breaking_r (s s' : S) : R :=
  abs (req_minus (mult (evicted_boltzmann_r s) (evicted_transition_r s s'))
                 (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))).

(* ---- summation negation/subtraction machinery (in-section
   req-side rebuild of the Id [sum_over_S_opp] L15820 / [_minus]
   L15830; genuinely proved via the [sum_linear (opp one)] route)
   ---- *)

Lemma ag_sum_opp : forall f : S -> R,
  req (sumf (fun s : S => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans _ (sumf (fun s : S => mult (opp one) (f s))) _).
  - apply (sum_ext (fun s : S => opp (f s))
             (fun s : S => mult (opp one) (f s))).
    intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s)))
                     (mult (opp one) (f s))).
    + exact (req_opp_compat _ _ (req_sym _ _ (req_mult_one_l (f s)))).
    + exact (req_sym _ _ (req_opp_mult_r one (f s))).
  - apply (req_trans _ (mult (opp one) (sumf f)) _).
    + exact (sum_linear (opp one) f).
    + apply (req_trans _ (opp (mult one (sumf f))) _).
      * exact (req_opp_mult_r one (sumf f)).
      * exact (req_opp_compat _ _ (req_mult_one_l (sumf f))).
Qed.

Lemma ag_sum_minus : forall f g : S -> R,
  req (sumf (fun s : S => req_minus (f s) (g s)))
      (req_minus (sumf f) (sumf g)).
Proof.
  intros f g. unfold req_minus.
  apply (req_trans _ (plus (sumf f) (sumf (fun s : S => opp (g s)))) _).
  - exact (sum_add f (fun s : S => opp (g s))).
  - exact (req_plus_compat _ _ _ _ (req_refl _) (ag_sum_opp g)).
Qed.

(* ---- the core lemmas of the cluster (point-by-point req form of the baseline L29555 region) ---- *)

(* pointwise identity: [if k s then a·f s else 0 ==
   a·(if k s then f s else 0)] (genuinely proved: the keep branch by
   reflexivity, the else branch by [mult_zero]). *)
Lemma ag_eviction_if_linear :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (a : R) (f : S -> R) (s : S),
    req (if kd s then mult a (f s) else zero)
        (mult a (if kd s then f s else zero)).
Proof.
  intros k kd a f s.
  destruct (kd s) as [Hk | Hnk].
  - apply req_refl.
  - exact (req_sym _ _ (req_mult_zero_r a)).
Qed.

(* pointwise monotonicity: [k1 ⊆ k2] gives the [k1]-branch term bounded by the [k2]-branch term (genuinely proved). *)
Lemma ag_eviction_pointwise_le :
  forall (k1 k2 : S -> Set) (Hsub : forall s : S, k1 s -> k2 s)
         (kd1 : forall s : S, Or (k1 s) (Not (k1 s)))
         (kd2 : forall s : S, Or (k2 s) (Not (k2 s))),
    forall s : S,
      le (if kd1 s then boltzmann_factor_r s else zero)
         (if kd2 s then boltzmann_factor_r s else zero).
Proof.
  intros k1 k2 Hsub kd1 kd2 s.
  destruct (kd1 s) as [H1 | Hn1].
  - destruct (kd2 s) as [H2 | Hn2].
    + apply le_refl.
    + exact (match Hn2 (Hsub s H1) with end).
  - destruct (kd2 s) as [H2 | Hn2].
    + apply (lt_le_iff zero (boltzmann_factor_r s)).
      left. unfold boltzmann_factor_r. apply exp_neg_pos.
    + apply le_refl.
Qed.

(* the evicted distribution is still normalized: [Σ ev_b == 1]
   (assembled: if-linearity + [sum_linear] + [inv_pos_correct]; the
   delta position folds definitionally into [evicted_partition_r]). *)
Theorem ag_evicted_boltzmann_normalized :
  req (sumf (fun s : S => evicted_boltzmann_r s)) one.
Proof.
  assert (H1 : req (sumf (fun s : S => evicted_boltzmann_r s))
                   (sumf (fun s : S =>
                      mult (inv_pos evicted_partition_r evicted_partition_r_pos)
                           (if keep_dec s then boltzmann_factor_r s else zero)))).
  { apply (sum_ext (fun s : S => evicted_boltzmann_r s)
             (fun s : S =>
                mult (inv_pos evicted_partition_r evicted_partition_r_pos)
                     (if keep_dec s then boltzmann_factor_r s else zero))).
    intro s. unfold evicted_boltzmann_r.
    exact (ag_eviction_if_linear keep keep_dec
             (inv_pos evicted_partition_r evicted_partition_r_pos)
             boltzmann_factor_r s). }
  assert (H2 : req (sumf (fun s : S =>
                     mult (inv_pos evicted_partition_r evicted_partition_r_pos)
                          (if keep_dec s then boltzmann_factor_r s else zero)))
                   (mult (inv_pos evicted_partition_r evicted_partition_r_pos)
                         (sumf (fun s : S =>
                            if keep_dec s then boltzmann_factor_r s else zero))))
    by exact (sum_linear (inv_pos evicted_partition_r evicted_partition_r_pos)
                (fun s : S => if keep_dec s then boltzmann_factor_r s else zero)).
  apply (req_trans _ _ _ H1).
  apply (req_trans _ _ _ H2).
  apply (req_trans
           (mult (inv_pos evicted_partition_r evicted_partition_r_pos)
                 (sumf (fun s : S => if keep_dec s then boltzmann_factor_r s else zero)))
           (mult (inv_pos evicted_partition_r evicted_partition_r_pos) evicted_partition_r)
           one).
  - apply req_refl.
  - exact (req_trans _ _ _
             (mult_comm (inv_pos evicted_partition_r evicted_partition_r_pos)
                        evicted_partition_r)
             (inv_pos_correct evicted_partition_r evicted_partition_r_pos)).
Qed.

(* support (b): monotone expansion of the kept set gives a partition
   function that does not decrease (assembled: pointwise
   monotonicity + the [sum_le] interface position). *)
Theorem ag_eviction_partition_monotone :
  forall (k1 k2 : S -> Set) (Hsub : forall s : S, k1 s -> k2 s)
         (kd1 : forall s : S, Or (k1 s) (Not (k1 s)))
         (kd2 : forall s : S, Or (k2 s) (Not (k2 s))),
    le (evicted_partition_of_r k1 kd1) (evicted_partition_of_r k2 kd2).
Proof.
  intros k1 k2 Hsub kd1 kd2.
  unfold evicted_partition_of_r.
  apply (sum_le (fun s : S => if kd1 s then boltzmann_factor_r s else zero)
                (fun s : S => if kd2 s then boltzmann_factor_r s else zero)).
  intro s. exact (ag_eviction_pointwise_le k1 k2 Hsub kd1 kd2 s).
Qed.

(* pointwise: [if k s then f s else 0 <= f s] (genuinely proved). *)
Lemma ag_eviction_if_le :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))),
    forall s : S,
      le (if kd s then boltzmann_factor_r s else zero) (boltzmann_factor_r s).
Proof.
  intros k kd s.
  destruct (kd s) as [Hk | Hnk].
  - apply le_refl.
  - apply (lt_le_iff zero (boltzmann_factor_r s)).
    left. unfold boltzmann_factor_r. apply exp_neg_pos.
Qed.

(* support (c): the partition over any kept set is bounded by
   [Z_thermo] — full retention is the mass upper bound (this single
   parameterized statement also covers the Id conclusion
   [topk_kept_le_Zthermo] L30355, whose [keep_top_k] instance is
   the [kd]-parameterized special case; assembled from the pointwise
   bound + [sum_le]). *)
Theorem ag_eviction_partition_le_full :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))),
    le (evicted_partition_of_r k kd) Z_thermo_r.
Proof.
  intros k kd.
  unfold evicted_partition_of_r, Z_thermo_r.
  apply (sum_le (fun s : S => if kd s then boltzmann_factor_r s else zero)
                boltzmann_factor_r).
  intro s. exact (ag_eviction_if_le k kd s).
Qed.

(* support (d): full retention gives [evicted_transition ==
   transition] (genuinely proved: branch reduction to both cases +
   contradiction elimination). *)
Theorem ag_eviction_transition_full :
  (forall s : S, keep s) ->
  forall s s' : S, req (evicted_transition_r s s') (transition s s').
Proof.
  intros Hkall s s'.
  unfold evicted_transition_r.
  destruct (keep_dec s) as [Hks | Hnks].
  - destruct (keep_dec s') as [Hks' | Hnks'].
    + apply req_refl.
    + exact (match Hnks' (Hkall s') with end).
  - exact (match Hnks (Hkall s) with end).
Qed.

(* support (d'): full retention plus equal partitions gives the
   evicted distribution back as the original distribution (genuinely
   proved: [inv_pos_ext] + [req_mult_compat]). *)
Theorem ag_eviction_boltzmann_full :
  (forall s : S, keep s) ->
  req evicted_partition_r Z_thermo_r ->
  forall s : S, req (evicted_boltzmann_r s) (boltzmann_dist_attn_r s).
Proof.
  intros Hkall HZ s.
  unfold evicted_boltzmann_r, boltzmann_dist_attn_r, boltzmann_factor_r.
  destruct (keep_dec s) as [Hks | Hnks].
  - assert (Hie : req (inv_pos evicted_partition_r evicted_partition_r_pos)
                      (inv_pos Z_thermo_r Z_thermo_r_pos))
      by exact (inv_pos_ext evicted_partition_r Z_thermo_r
                 evicted_partition_r_pos Z_thermo_r_pos HZ).
    exact (req_mult_compat
             (inv_pos evicted_partition_r evicted_partition_r_pos)
             (inv_pos Z_thermo_r Z_thermo_r_pos)
             (exp_neg (mult (inv_pos D D_pos) (energy s)))
             (exp_neg (mult (inv_pos D D_pos) (energy s)))
             Hie (req_refl _)).
  - exact (match Hnks (Hkall s) with end).
Qed.

(* the steady-state deviation of eviction is bounded by the sum of
   breakings (proved/assembled: [sum_linear] + [ag_sum_minus] + the
   [abs_sum_le_r] interface position + a sign reversal by
   [req_abs_minus_sym]). *)
Theorem ag_eviction_steady_deviation :
  forall s : S,
    le (abs (req_minus
               (sumf (fun s' : S => mult (evicted_boltzmann_r s')
                                         (evicted_transition_r s' s)))
               (mult (evicted_boltzmann_r s)
                     (sumf (fun s' : S => evicted_transition_r s s')))))
       (sumf (fun s' : S => db_breaking_r s s')).
Proof.
  intro s.
  assert (Hlin : req (sumf (fun s' : S => mult (evicted_boltzmann_r s)
                                               (evicted_transition_r s s')))
                     (mult (evicted_boltzmann_r s)
                           (sumf (fun s' : S => evicted_transition_r s s'))))
    by exact (sum_linear (evicted_boltzmann_r s)
                (fun s' : S => evicted_transition_r s s')).
  assert (Hdiff : req (req_minus
                        (sumf (fun s' : S => mult (evicted_boltzmann_r s')
                                                  (evicted_transition_r s' s)))
                        (sumf (fun s' : S => mult (evicted_boltzmann_r s)
                                                  (evicted_transition_r s s'))))
                      (sumf (fun s' : S =>
                         req_minus (mult (evicted_boltzmann_r s')
                                         (evicted_transition_r s' s))
                                   (mult (evicted_boltzmann_r s)
                                         (evicted_transition_r s s')))))
    by exact (req_sym _ _ (ag_sum_minus
                 (fun s' : S => mult (evicted_boltzmann_r s') (evicted_transition_r s' s))
                 (fun s' : S => mult (evicted_boltzmann_r s) (evicted_transition_r s s')))).
  assert (Hlhs : req (req_minus
                        (sumf (fun s' : S => mult (evicted_boltzmann_r s')
                                                  (evicted_transition_r s' s)))
                        (mult (evicted_boltzmann_r s)
                              (sumf (fun s' : S => evicted_transition_r s s'))))
                    (req_minus
                        (sumf (fun s' : S => mult (evicted_boltzmann_r s')
                                                  (evicted_transition_r s' s)))
                        (sumf (fun s' : S => mult (evicted_boltzmann_r s)
                                                  (evicted_transition_r s s')))))
    by exact (reqd_minus_compat _ _ _ _ (req_refl _) (req_sym _ _ Hlin)).
  apply (le_id_l
           (abs (req_minus
                  (sumf (fun s' : S => mult (evicted_boltzmann_r s')
                                            (evicted_transition_r s' s)))
                  (mult (evicted_boltzmann_r s)
                        (sumf (fun s' : S => evicted_transition_r s s')))))
           (abs (sumf (fun s' : S =>
                   req_minus (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))
                             (mult (evicted_boltzmann_r s) (evicted_transition_r s s')))))
           (sumf (fun s' : S => db_breaking_r s s'))).
  - apply (req_abs_compat _ _).
    exact (req_trans _ _ _ Hlhs Hdiff).
  - assert (Hpt : req (sumf (fun s' : S =>
                        abs (req_minus (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))
                                       (mult (evicted_boltzmann_r s) (evicted_transition_r s s')))))
                      (sumf (fun s' : S => db_breaking_r s s'))).
    { apply (sum_ext
               (fun s' : S =>
                  abs (req_minus (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))
                                 (mult (evicted_boltzmann_r s) (evicted_transition_r s s'))))
               (fun s' : S => db_breaking_r s s')
               (fun s' : S =>
                  req_abs_minus_sym
                    (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))
                    (mult (evicted_boltzmann_r s) (evicted_transition_r s s')))). }
    apply (le_id_r _ _ _ Hpt).
    exact (abs_sum_le_r (fun s' : S =>
              req_minus (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))
                        (mult (evicted_boltzmann_r s) (evicted_transition_r s s')))).
Qed.

(* ============================================================ *)
(*   Baseline originals: L29719 [top_k_tail_bound], L29732         *)
(*   [tail_plus_kept_full], L29782-29818 (three algebra            *)
(*   auxiliaries), L29820 [top_k_exchange], L29845                 *)
(*   [eviction_tail_pointwise_le], L29872 [top_k_tail_antitone],   *)
(*   L30306-30363 (positivity/conservation of the kept family).    *)
(*   Parameterization note: the Id [tail_mass]/[evicted_partition] *)
(*   fixed to [keep_dec] and the [keep_top_k] instances            *)
(*   (L30289-30294) are unified here into the decidable kept-set   *)
(*   parameters [(k : S -> Set)] + [kd]; so                        *)
(*   [ag_eviction_partition_le_full] covers both it and            *)
(*   [topk_kept_le_Zthermo] L30355, and [ag_tail_plus_kept_full]   *)
(*   covers both it and [topk_kept_plus_tail_full] L30330.         *)
(*   Not carried over: [top_k_majorization] L30047,                *)
(*   [top_k_swap_no_gain] L30073 and [top_k_majorization_mem]      *)
(*   L30264 — their proof engine is the counting/[firstn]/[skipn]/ *)
(*   sorting list machinery (13 lemmas, Id/nat layer), for which   *)
(*   the req layer has no bridging lemmas.                         *)
(* ============================================================ *)

Definition tail_mass_of_r
  (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : R :=
  sumf (fun s : S => if kd s then zero else boltzmann_factor_r s).

(* ---- the three algebra auxiliaries (req proofs of the baseline L29793/L29804 pair) ---- *)

Lemma ag_le_minus_le_zero : forall a b : R, le a b -> le (req_minus a b) zero.
Proof.
  intros a b Hab. unfold req_minus.
  apply (le_id_r (plus a (opp b)) (plus a (opp a)) zero (req_plus_opp_r a)).
  exact (le_plus_compat a a (opp b) (opp a) (le_refl a) (opp_le_compat a b Hab)).
Qed.

Lemma ag_le_plus_zero_l : forall a b : R, le b zero -> le (plus a b) a.
Proof.
  intros a b Hb.
  apply (le_trans (plus a b) (plus a zero) a).
  - exact (le_plus_compat a a b zero (le_refl a) Hb).
  - apply (le_id_l (plus a zero) a a (plus_zero a)).
    apply le_refl.
Qed.

Lemma ag_minus_plus_swap : forall a b c : R,
  req (plus (req_minus a b) c) (plus a (req_minus c b)).
Proof.
  intros a b c. unfold req_minus.
  apply (req_trans (plus (plus a (opp b)) c)
                   (plus a (plus (opp b) c))
                   (plus a (plus c (opp b)))).
  - exact (req_sym _ _ (plus_assoc a (opp b) c)).
  - exact (req_plus_compat a a (plus (opp b) c) (plus c (opp b))
              (req_refl a) (plus_comm (opp b) c)).
Qed.

(* ---- the tail-mass family ---- *)

(* tail-mass bound: the eviction loss is bounded by the total mass (assembled via [sum_le]). *)
Theorem ag_top_k_tail_bound :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))),
    le (tail_mass_of_r k kd) Z_thermo_r.
Proof.
  intros k kd. unfold tail_mass_of_r, Z_thermo_r.
  apply (sum_le (fun s : S => if kd s then zero else boltzmann_factor_r s)
                boltzmann_factor_r).
  intro s. destruct (kd s) as [Hk | Hnk].
  - apply (lt_le_iff zero (boltzmann_factor_r s)).
    left. unfold boltzmann_factor_r. apply exp_neg_pos.
  - apply le_refl.
Qed.

(* mass conservation: tail + kept == total (one parameterized
   statement covering the Id L29732 form and
   [topk_kept_plus_tail_full] L30330; assembled). *)
Theorem ag_tail_plus_kept_full :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))),
    req (plus (tail_mass_of_r k kd) (evicted_partition_of_r k kd)) Z_thermo_r.
Proof.
  intros k kd.
  unfold tail_mass_of_r, evicted_partition_of_r, Z_thermo_r.
  assert (Hpt : forall s : S,
           req (plus (if kd s then zero else boltzmann_factor_r s)
                     (if kd s then boltzmann_factor_r s else zero))
               (boltzmann_factor_r s)).
  { intro s. destruct (kd s) as [Hk | Hnk].
    - exact (req_plus_zero_l (boltzmann_factor_r s)).
    - exact (plus_zero (boltzmann_factor_r s)). }
  assert (Hext : req (sumf (fun s : S =>
                        plus (if kd s then zero else boltzmann_factor_r s)
                             (if kd s then boltzmann_factor_r s else zero)))
                   (sumf boltzmann_factor_r))
    by exact (sum_ext _ _ Hpt).
  assert (Hadd : req (sumf (fun s : S =>
                        plus (if kd s then zero else boltzmann_factor_r s)
                             (if kd s then boltzmann_factor_r s else zero)))
                   (plus (sumf (fun s : S => if kd s then zero else boltzmann_factor_r s))
                         (sumf (fun s : S => if kd s then boltzmann_factor_r s else zero))))
    by exact (sum_add _ _).
  apply (req_trans (plus (sumf (fun s : S => if kd s then zero else boltzmann_factor_r s))
                         (sumf (fun s : S => if kd s then boltzmann_factor_r s else zero)))
                   (sumf (fun s : S =>
                        plus (if kd s then zero else boltzmann_factor_r s)
                             (if kd s then boltzmann_factor_r s else zero)))
                   (sumf boltzmann_factor_r)).
  - exact (req_sym _ _ Hadd).
  - exact Hext.
Qed.

(* the exchange lemma (the greedy-optimality kernel): if the kept
   state s weighs no more than the evicted state s', swapping does
   not increase the tail mass (assembled from the three algebra
   auxiliaries). *)
Theorem ag_top_k_exchange :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s s' : S),
    k s -> Not (k s') ->
    le (boltzmann_factor_r s) (boltzmann_factor_r s') ->
    le (plus (req_minus (tail_mass_of_r k kd) (boltzmann_factor_r s'))
             (boltzmann_factor_r s))
       (tail_mass_of_r k kd).
Proof.
  intros k kd s s' Hks Hnks' Hff.
  assert (Hr : req (plus (req_minus (tail_mass_of_r k kd) (boltzmann_factor_r s'))
                         (boltzmann_factor_r s))
                   (plus (tail_mass_of_r k kd)
                         (req_minus (boltzmann_factor_r s) (boltzmann_factor_r s'))))
    by exact (ag_minus_plus_swap (tail_mass_of_r k kd)
                (boltzmann_factor_r s') (boltzmann_factor_r s)).
  assert (Hmm : le (req_minus (boltzmann_factor_r s) (boltzmann_factor_r s')) zero)
    by exact (ag_le_minus_le_zero _ _ Hff).
  assert (Hfin : le (plus (tail_mass_of_r k kd)
                          (req_minus (boltzmann_factor_r s) (boltzmann_factor_r s')))
                    (tail_mass_of_r k kd))
    by exact (ag_le_plus_zero_l _ _ Hmm).
  exact (le_id_l _ _ _ Hr Hfin).
Qed.

(* pointwise antitonicity of the tail: [k1 ⊆ k2] gives the [k2] tail term bounded by the [k1] tail term. *)
Lemma ag_eviction_tail_pointwise_le :
  forall (k1 k2 : S -> Set) (Hsub : forall s : S, k1 s -> k2 s)
         (kd1 : forall s : S, Or (k1 s) (Not (k1 s)))
         (kd2 : forall s : S, Or (k2 s) (Not (k2 s))),
    forall s : S,
      le (if kd2 s then zero else boltzmann_factor_r s)
         (if kd1 s then zero else boltzmann_factor_r s).
Proof.
  intros k1 k2 Hsub kd1 kd2 s.
  destruct (kd2 s) as [H2 | Hn2].
  - destruct (kd1 s) as [H1 | Hn1].
    + apply le_refl.
    + apply (lt_le_iff zero (boltzmann_factor_r s)).
      left. unfold boltzmann_factor_r. apply exp_neg_pos.
  - destruct (kd1 s) as [H1 | Hn1].
    + exact (match Hn2 (Hsub s H1) with end).
    + apply le_refl.
Qed.

(* antitonicity of the tail mass: expanding the kept set never
   increases the loss (dual to [ag_eviction_partition_monotone];
   assembled via [sum_le]). *)
Theorem ag_top_k_tail_antitone :
  forall (k1 k2 : S -> Set) (Hsub : forall s : S, k1 s -> k2 s)
         (kd1 : forall s : S, Or (k1 s) (Not (k1 s)))
         (kd2 : forall s : S, Or (k2 s) (Not (k2 s))),
    le (tail_mass_of_r k2 kd2) (tail_mass_of_r k1 kd1).
Proof.
  intros k1 k2 Hsub kd1 kd2. unfold tail_mass_of_r.
  apply (sum_le (fun s : S => if kd2 s then zero else boltzmann_factor_r s)
                (fun s : S => if kd1 s then zero else boltzmann_factor_r s)).
  intro s. exact (ag_eviction_tail_pointwise_le k1 k2 Hsub kd1 kd2 s).
Qed.

(* ---- positivity/conservation of the kept family (req form of the baseline L30363 region) ---- *)

(* positivity of the one-argument Boltzmann factor (a direct citation of [exp_neg_pos]). *)
Lemma ag_boltzmann_factor_pos_attn : forall s : S, lt zero (boltzmann_factor_r s).
Proof.
  intro s. unfold boltzmann_factor_r. apply exp_neg_pos.
Qed.

(* the if-form kept term is nonnegative. *)
Lemma ag_kept_term_nonneg :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s : S),
    le zero (if kd s then boltzmann_factor_r s else zero).
Proof.
  intros k kd s. destruct (kd s) as [Hk | Hnk].
  - apply (lt_le_iff _ _). left. apply ag_boltzmann_factor_pos_attn.
  - apply le_refl.
Qed.

(* the if-form kept term is bounded by the factor. *)
Lemma ag_kept_term_le_factor :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s : S),
    le (if kd s then boltzmann_factor_r s else zero) (boltzmann_factor_r s).
Proof.
  intros k kd s. destruct (kd s) as [Hk | Hnk].
  - apply le_refl.
  - apply (lt_le_iff _ _). left. apply ag_boltzmann_factor_pos_attn.
Qed.

(* the inverse reverses order: [kept <= Z] gives [1/Z <= 1/kept]
   (direct citation of the interface field [inv_pos_le_compat] +
   [ag_eviction_partition_le_full]). *)
Theorem ag_inv_Z_le_inv_kept :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)),
    le (inv_pos Z_thermo_r Z_thermo_r_pos)
       (inv_pos (evicted_partition_of_r k kd) Hkpos).
Proof.
  intros k kd Hkpos.
  apply (inv_pos_le_compat (evicted_partition_of_r k kd) Z_thermo_r
             Hkpos Z_thermo_r_pos).
  exact (ag_eviction_partition_le_full k kd).
Qed.

(* ============================================================ *)
(* Top-K truncation: the exact TV identity chain.                  *)
(*   Chain (isomorphic to the Id original): conservation -> kept   *)
(*   <= Z -> the inverse reverses order -> sign branch (abs        *)
(*   elimination) -> pointwise difference decomposition ->         *)
(*   summation split -> final normalization algebra.               *)
(*   Honest bridge: [req_lt_plus_compat_lt_le_h] — the req setoid  *)
(*   interface only carries the doubly-strict and doubly-non-strict*)
(*   plus-compatibility fields, and the mixed form is not          *)
(*   derivable (a constructive order has no two-sided              *)
(*   cancellation); it is satisfiable by the Real instance and     *)
(*   feeds the [lt_minus_cc] sign step.                            *)
(*   Main theorem: [ag_topk_tv_identity_strict].                   *)
(* ============================================================ *)

(* the mixed plus-compatibility bridge (a premise at the same position as ReqStrictOrderBridge L1468). *)
Hypothesis req_lt_plus_compat_lt_le_h :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).

(* the Top-K kept partition and the renormalized distribution (parameterized copies of the baseline L30300 region). *)
Definition topk_renorm_r (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
           (Hkpos : lt zero (evicted_partition_of_r k kd)) (s : S) : R :=
  if kd s then
    mult (inv_pos (evicted_partition_of_r k kd) Hkpos) (boltzmann_factor_r s)
  else zero.

(* total variation (an in-section req copy; same shape as the Id [tv_dist] L28785, with the 1/2 factor). *)
Definition tv_dist_r (mu nu : S -> R) : R :=
  mult (inv_pos (plus one one) req_two_pos)
       (sumf (fun s : S => abs (req_minus (mu s) (nu s)))).

(* ---- the five Id [_cc] auxiliaries in req form (baseline L30372-30410) ---- *)

Lemma ag_inv_one_cc : req (inv_pos one one_pos) one.
Proof.
  apply (req_trans _ (mult (inv_pos one one_pos) one) _).
  - exact (req_sym _ _ (mult_one (inv_pos one one_pos))).
  - apply (req_trans (mult (inv_pos one one_pos) one)
                     (mult one (inv_pos one one_pos)) one).
    + exact (mult_comm (inv_pos one one_pos) one).
    + exact (inv_pos_correct one one_pos).
Qed.

Lemma ag_opp_zero_cc : req (opp zero) zero.
Proof.
  exact (req_add_cancel_l (opp zero) zero zero
           (req_trans (plus (opp zero) zero) (plus zero (opp zero))
                      (plus zero zero)
             (plus_comm (opp zero) zero)
             (req_trans (plus zero (opp zero)) zero (plus zero zero)
                        (plus_opp zero) (req_sym _ _ (plus_zero zero))))).
Qed.

Lemma ag_lt_minus_cc : forall a b : R, lt a b -> lt (req_minus a b) zero.
Proof.
  intros a b Hab. unfold req_minus.
  apply (lt_id_r (plus a (opp b)) (plus b (opp b)) zero (req_plus_opp_r b)).
  exact (req_lt_plus_compat_lt_le_h a b (opp b) (opp b) Hab (le_refl (opp b))).
Qed.

Lemma ag_abs_neg_cc : forall a : R, lt a zero -> req (abs a) (opp a).
Proof.
  intros a Ha.
  apply (req_trans (abs a) (abs (opp a)) (opp a)).
  - exact (req_sym _ _ (abs_opp a)).
  - apply abs_pos.
    apply (lt_id_l zero (opp zero) (opp a)
             (req_sym _ _ ag_opp_zero_cc) (opp_lt_compat a zero Ha)).
Qed.

Lemma ag_minus_zero_cc : forall x : R, req (req_minus x zero) x.
Proof.
  intro x. unfold req_minus.
  apply (req_trans (plus x (opp zero)) (plus x zero) x).
  - exact (req_plus_compat x x (opp zero) zero (req_refl x)
             (req_add_cancel_l (opp zero) zero zero
               (req_trans (plus (opp zero) zero) (plus zero (opp zero))
                          (plus zero zero)
                 (plus_comm (opp zero) zero)
                 (req_trans (plus zero (opp zero)) zero (plus zero zero)
                            (plus_opp zero) (req_sym _ _ (plus_zero zero)))))).
  - apply plus_zero.
Qed.

(* ---- pointwise difference decomposition (baseline L30477/L30516) ---- *)

(* keep branch: [|b/Z − b/Z_keep| == b·(1/Z_keep − 1/Z)]
   (premised on [lt invZ invKeep], the strict premise at the Id
   position; genuinely proved: the reversed [req_mult_minus_distr_r]
   + [abs_mult] + [abs_pos] + [abs_neg]). *)
Lemma ag_tv_pointwise_keep :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)) (s : S),
    k s ->
    lt (inv_pos Z_thermo_r Z_thermo_r_pos)
       (inv_pos (evicted_partition_of_r k kd) Hkpos) ->
    req (abs (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s))
                        (mult (inv_pos (evicted_partition_of_r k kd) Hkpos)
                              (boltzmann_factor_r s))))
        (mult (boltzmann_factor_r s)
              (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                         (inv_pos Z_thermo_r Z_thermo_r_pos))).
Proof.
  intros k kd Hkpos s Hk Hst.
  assert (Hfac : req (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s))
                                (mult (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                      (boltzmann_factor_r s)))
                     (mult (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                      (inv_pos (evicted_partition_of_r k kd) Hkpos))
                           (boltzmann_factor_r s)))
    by exact (req_sym _ _ (req_mult_minus_distr_r (inv_pos Z_thermo_r Z_thermo_r_pos)
                             (inv_pos (evicted_partition_of_r k kd) Hkpos)
                             (boltzmann_factor_r s))).
  assert (Habs : req (abs (mult (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (inv_pos (evicted_partition_of_r k kd) Hkpos))
                                (boltzmann_factor_r s)))
                     (mult (boltzmann_factor_r s)
                           (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (inv_pos (evicted_partition_of_r k kd) Hkpos))))).
  { apply (req_trans (abs (mult (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (inv_pos (evicted_partition_of_r k kd) Hkpos))
                                (boltzmann_factor_r s)))
                     (mult (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (inv_pos (evicted_partition_of_r k kd) Hkpos)))
                           (abs (boltzmann_factor_r s)))
                     (mult (boltzmann_factor_r s)
                           (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (inv_pos (evicted_partition_of_r k kd) Hkpos))))).
    - exact (abs_mult _ _).
    - apply (req_trans (mult (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                             (inv_pos (evicted_partition_of_r k kd) Hkpos)))
                             (abs (boltzmann_factor_r s)))
                       (mult (abs (boltzmann_factor_r s))
                             (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                             (inv_pos (evicted_partition_of_r k kd) Hkpos))))
                       (mult (boltzmann_factor_r s)
                             (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                             (inv_pos (evicted_partition_of_r k kd) Hkpos))))).
      + exact (mult_comm _ _).
      + exact (req_mult_compat (abs (boltzmann_factor_r s)) (boltzmann_factor_r s)
                  (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                  (inv_pos (evicted_partition_of_r k kd) Hkpos)))
                  (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                  (inv_pos (evicted_partition_of_r k kd) Hkpos)))
                  (abs_pos (boltzmann_factor_r s) (ag_boltzmann_factor_pos_attn s))
                  (req_refl _)). }
  assert (Hsign : req (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                      (inv_pos (evicted_partition_of_r k kd) Hkpos)))
                      (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                 (inv_pos Z_thermo_r Z_thermo_r_pos))).
  { apply (req_trans
             (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                             (inv_pos (evicted_partition_of_r k kd) Hkpos)))
             (opp (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                             (inv_pos (evicted_partition_of_r k kd) Hkpos)))
             (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                        (inv_pos Z_thermo_r Z_thermo_r_pos))).
    - exact (ag_abs_neg_cc _ (ag_lt_minus_cc _ _ Hst)).
    - apply (req_trans (opp (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                       (inv_pos (evicted_partition_of_r k kd) Hkpos)))
                       (plus (opp (inv_pos Z_thermo_r Z_thermo_r_pos))
                             (inv_pos (evicted_partition_of_r k kd) Hkpos))
                       (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                  (inv_pos Z_thermo_r Z_thermo_r_pos))).
      + exact (req_opp_minus _ _).
      + exact (plus_comm (opp (inv_pos Z_thermo_r Z_thermo_r_pos))
                         (inv_pos (evicted_partition_of_r k kd) Hkpos)). }
  apply (req_trans
           (abs (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s))
                           (mult (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                 (boltzmann_factor_r s))))
           (abs (mult (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                 (inv_pos (evicted_partition_of_r k kd) Hkpos))
                      (boltzmann_factor_r s)))
           (mult (boltzmann_factor_r s)
                 (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                            (inv_pos Z_thermo_r Z_thermo_r_pos)))).
  - apply (req_abs_compat _ _). exact Hfac.
  - apply (req_trans
             (abs (mult (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                   (inv_pos (evicted_partition_of_r k kd) Hkpos))
                        (boltzmann_factor_r s)))
             (mult (boltzmann_factor_r s)
                   (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                   (inv_pos (evicted_partition_of_r k kd) Hkpos))))
             (mult (boltzmann_factor_r s)
                   (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                              (inv_pos Z_thermo_r Z_thermo_r_pos)))).
    + exact Habs.
    + exact (req_mult_compat _ _ _ _ (req_refl _) Hsign).
Qed.

(* evict branch: [|b/Z − 0| == b/Z]. *)
Lemma ag_tv_pointwise_evict :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)) (s : S),
    Not (k s) ->
    req (abs (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s)) zero))
        (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s)).
Proof.
  intros k kd Hkpos s Hnk.
  assert (Hz : req (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s)) zero)
                   (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s)))
    by exact (ag_minus_zero_cc _).
  apply (req_trans _ _ _ (req_abs_compat _ _ Hz)).
  apply abs_pos.
  apply mult_positive.
  - apply (inv_pos_pos Z_thermo_r Z_thermo_r_pos).
  - apply ag_boltzmann_factor_pos_attn.
Qed.

(* the pointwise identity, conditionalized. *)
Lemma ag_tv_pointwise :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)) (s : S),
    lt (inv_pos Z_thermo_r Z_thermo_r_pos)
       (inv_pos (evicted_partition_of_r k kd) Hkpos) ->
    req (abs (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s))
                        (topk_renorm_r k kd Hkpos s)))
        (if kd s
         then mult (boltzmann_factor_r s)
                   (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                              (inv_pos Z_thermo_r Z_thermo_r_pos))
         else mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s)).
Proof.
  intros k kd Hkpos s Hst.
  unfold topk_renorm_r.
  destruct (kd s) as [Hk | Hnk].
  - exact (ag_tv_pointwise_keep k kd Hkpos s Hk Hst).
  - exact (ag_tv_pointwise_evict k kd Hkpos s Hnk).
Qed.

(* the if-split and the else-branch linearity (baseline L30505). *)
Lemma ag_tv_if_split : forall (X Y : R) (k : S -> Set)
                              (kd : forall s : S, Or (k s) (Not (k s))) (s : S),
  req (if kd s then X else Y)
      (plus (if kd s then X else zero) (if kd s then zero else Y)).
Proof.
  intros X Y k kd s. destruct (kd s) as [Hk | Hnk].
  - exact (req_sym _ _ (plus_zero X)).
  - exact (req_trans (Y) (plus Y zero) (plus zero Y)
             (req_sym _ _ (plus_zero Y)) (plus_comm Y zero)).
Qed.

Lemma ag_eviction_if_linear_else :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (a : R) (f : S -> R) (s : S),
    req (if kd s then zero else mult a (f s))
        (mult a (if kd s then zero else f s)).
Proof.
  intros k kd a f s. destruct (kd s) as [Hk | Hnk].
  - exact (req_sym _ _ (req_mult_zero_r a)).
  - apply req_refl.
Qed.

(* summation split: [Σ(if keep then b·D else b/Z) == kept·D +
   invZ·tail] (assembled: the if-split + [sum_add] + the two
   if-linearity lemmas + [sum_linear]). *)
Theorem ag_tv_sum_decomp :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)),
    req (sumf (fun s : S => if kd s
                            then mult (boltzmann_factor_r s)
                                      (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                 (inv_pos Z_thermo_r Z_thermo_r_pos))
                            else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                      (boltzmann_factor_r s)))
        (plus (mult (evicted_partition_of_r k kd)
                    (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                               (inv_pos Z_thermo_r Z_thermo_r_pos)))
              (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
Proof.
  intros k kd Hkpos.
  assert (Hsplit : req (sumf (fun s : S => if kd s
                                           then mult (boltzmann_factor_r s)
                                                     (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                                (inv_pos Z_thermo_r Z_thermo_r_pos))
                                           else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                     (boltzmann_factor_r s)))
                      (sumf (fun s : S => plus (if kd s
                                                then mult (boltzmann_factor_r s)
                                                          (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                                     (inv_pos Z_thermo_r Z_thermo_r_pos))
                                                else zero)
                                               (if kd s
                                                then zero
                                                else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                          (boltzmann_factor_r s))))).
  { apply (sum_ext
             (fun s : S => if kd s
                           then mult (boltzmann_factor_r s)
                                     (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                (inv_pos Z_thermo_r Z_thermo_r_pos))
                           else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                     (boltzmann_factor_r s))
             (fun s : S => plus (if kd s
                                 then mult (boltzmann_factor_r s)
                                           (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                      (inv_pos Z_thermo_r Z_thermo_r_pos))
                                 else zero)
                                (if kd s
                                 then zero
                                 else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (boltzmann_factor_r s)))).
    intro s. exact (ag_tv_if_split
                      (mult (boltzmann_factor_r s)
                            (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                       (inv_pos Z_thermo_r Z_thermo_r_pos)))
                      (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s))
                      k kd s). }
  apply (req_trans _ _ _ Hsplit).
  apply (req_trans _ (plus (sumf (fun s : S => if kd s
                                                then mult (boltzmann_factor_r s)
                                                          (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                                     (inv_pos Z_thermo_r Z_thermo_r_pos))
                                                else zero))
                           (sumf (fun s : S => if kd s
                                               then zero
                                               else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                         (boltzmann_factor_r s)))) _).
  - exact (sum_add (fun s : S => if kd s
                                 then mult (boltzmann_factor_r s)
                                           (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                      (inv_pos Z_thermo_r Z_thermo_r_pos))
                                 else zero)
                   (fun s : S => if kd s
                                 then zero
                                 else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (boltzmann_factor_r s))).
  - apply (req_plus_compat
             (sumf (fun s : S => if kd s
                                 then mult (boltzmann_factor_r s)
                                           (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                      (inv_pos Z_thermo_r Z_thermo_r_pos))
                                 else zero))
             (mult (evicted_partition_of_r k kd)
                   (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                              (inv_pos Z_thermo_r Z_thermo_r_pos)))
             (sumf (fun s : S => if kd s
                                 then zero
                                 else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (boltzmann_factor_r s)))
             (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
    + apply (req_trans (sumf (fun s : S => if kd s
                                            then mult (boltzmann_factor_r s)
                                                      (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                                 (inv_pos Z_thermo_r Z_thermo_r_pos))
                                            else zero))
                       (sumf (fun s : S => mult (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                          (inv_pos Z_thermo_r Z_thermo_r_pos))
                                                (if kd s then boltzmann_factor_r s else zero))) _).
      * apply (sum_ext
                 (fun s : S => if kd s
                               then mult (boltzmann_factor_r s)
                                         (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                    (inv_pos Z_thermo_r Z_thermo_r_pos))
                               else zero)
                 (fun s : S => mult (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                (inv_pos Z_thermo_r Z_thermo_r_pos))
                                    (if kd s then boltzmann_factor_r s else zero))).
        -- intro s. destruct (kd s) as [Hk | Hnk].
           ++ exact (mult_comm (boltzmann_factor_r s)
                        (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                   (inv_pos Z_thermo_r Z_thermo_r_pos))).
           ++ exact (req_sym _ _ (req_mult_zero_r (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos) (inv_pos Z_thermo_r Z_thermo_r_pos)))).
      * apply (req_trans (sumf (fun s : S => mult (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                             (inv_pos Z_thermo_r Z_thermo_r_pos))
                                                  (if kd s then boltzmann_factor_r s else zero)))
                         (mult (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                          (inv_pos Z_thermo_r Z_thermo_r_pos))
                               (sumf (fun s : S => if kd s then boltzmann_factor_r s else zero)))
                         (mult (evicted_partition_of_r k kd)
                               (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                          (inv_pos Z_thermo_r Z_thermo_r_pos)))).
         -- exact (sum_linear (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                         (inv_pos Z_thermo_r Z_thermo_r_pos))
                    (fun s : S => if kd s then boltzmann_factor_r s else zero)).
         -- exact (mult_comm (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                        (inv_pos Z_thermo_r Z_thermo_r_pos))
                    (evicted_partition_of_r k kd)).
    + apply (req_trans (sumf (fun s : S => if kd s
                                            then zero
                                            else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                      (boltzmann_factor_r s)))
                       (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                             (sumf (fun s : S => if kd s then zero else boltzmann_factor_r s)))
                       (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
      * apply (req_trans (sumf (fun s : S => if kd s
                                             then zero
                                             else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                       (boltzmann_factor_r s)))
                         (sumf (fun s : S => mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                   (if kd s then zero else boltzmann_factor_r s)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                               (sumf (fun s : S => if kd s then zero else boltzmann_factor_r s)))).
        -- apply (sum_ext
                    (fun s : S => if kd s
                                  then zero
                                  else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                            (boltzmann_factor_r s))
                    (fun s : S => mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                       (if kd s then zero else boltzmann_factor_r s))).
           ++ intro s. exact (ag_eviction_if_linear_else k kd (inv_pos Z_thermo_r Z_thermo_r_pos)
                                boltzmann_factor_r s).
        -- exact (sum_linear (inv_pos Z_thermo_r Z_thermo_r_pos)
                   (fun s : S => if kd s then zero else boltzmann_factor_r s)).
      * apply req_refl.
Qed.

(* the closing algebra: [kept·D + invZ·tail == 2·(invZ·tail)]. *)
Theorem ag_tv_sum_collapse :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)),
    req (plus (mult (evicted_partition_of_r k kd)
                    (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                               (inv_pos Z_thermo_r Z_thermo_r_pos)))
              (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd)))
        (mult (plus one one) (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                   (tail_mass_of_r k kd))).
Proof.
  intros k kd Hkpos.
  assert (Hk1 : req (mult (evicted_partition_of_r k kd)
                          (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                     (inv_pos Z_thermo_r Z_thermo_r_pos)))
                    (req_minus one (mult (evicted_partition_of_r k kd)
                                         (inv_pos Z_thermo_r Z_thermo_r_pos)))).
  { apply (req_trans (mult (evicted_partition_of_r k kd)
                           (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                      (inv_pos Z_thermo_r Z_thermo_r_pos)))
                     (req_minus (mult (evicted_partition_of_r k kd)
                                      (inv_pos (evicted_partition_of_r k kd) Hkpos))
                                (mult (evicted_partition_of_r k kd)
                                      (inv_pos Z_thermo_r Z_thermo_r_pos)))
                     (req_minus one (mult (evicted_partition_of_r k kd)
                                          (inv_pos Z_thermo_r Z_thermo_r_pos)))).
    - exact (req_mult_minus_distr_l (evicted_partition_of_r k kd)
                (inv_pos (evicted_partition_of_r k kd) Hkpos)
                (inv_pos Z_thermo_r Z_thermo_r_pos)).
    - apply (reqd_minus_compat _ _ _ _).
      + apply (req_trans (mult (evicted_partition_of_r k kd)
                               (inv_pos (evicted_partition_of_r k kd) Hkpos))
                         (mult (inv_pos (evicted_partition_of_r k kd) Hkpos)
                               (evicted_partition_of_r k kd))
                         one).
        * exact (mult_comm (evicted_partition_of_r k kd)
                    (inv_pos (evicted_partition_of_r k kd) Hkpos)).
        * apply (req_trans (mult (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                 (evicted_partition_of_r k kd))
                           (mult (evicted_partition_of_r k kd)
                                 (inv_pos (evicted_partition_of_r k kd) Hkpos))
                           one).
          -- exact (mult_comm (inv_pos (evicted_partition_of_r k kd) Hkpos)
                              (evicted_partition_of_r k kd)).
          -- exact (inv_pos_correct (evicted_partition_of_r k kd) Hkpos).
      + apply req_refl. }
  assert (Hk2 : req (plus (mult (evicted_partition_of_r k kd)
                                (inv_pos Z_thermo_r Z_thermo_r_pos))
                          (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                (tail_mass_of_r k kd)))
                    one).
  { apply (req_trans (plus (mult (evicted_partition_of_r k kd)
                                 (inv_pos Z_thermo_r Z_thermo_r_pos))
                           (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                 (tail_mass_of_r k kd)))
                     (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                           (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd)))
                     one).
    - apply (req_trans (plus (mult (evicted_partition_of_r k kd)
                                   (inv_pos Z_thermo_r Z_thermo_r_pos))
                             (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                   (tail_mass_of_r k kd)))
                       (plus (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                   (evicted_partition_of_r k kd))
                             (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                   (tail_mass_of_r k kd)))
                       (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                             (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd)))).
      + exact (req_plus_compat _ _ _ _
                  (mult_comm (evicted_partition_of_r k kd) (inv_pos Z_thermo_r Z_thermo_r_pos))
                  (req_refl _)).
      + apply (req_trans (plus (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                     (evicted_partition_of_r k kd))
                               (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                     (tail_mass_of_r k kd)))
                         (plus (mult (evicted_partition_of_r k kd)
                                     (inv_pos Z_thermo_r Z_thermo_r_pos))
                               (mult (tail_mass_of_r k kd)
                                     (inv_pos Z_thermo_r Z_thermo_r_pos)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                               (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd)))).
        * exact (req_plus_compat _ _ _ _
                    (mult_comm (inv_pos Z_thermo_r Z_thermo_r_pos)
                               (evicted_partition_of_r k kd))
                    (mult_comm (inv_pos Z_thermo_r Z_thermo_r_pos)
                               (tail_mass_of_r k kd))).
        * apply (req_trans (plus (mult (evicted_partition_of_r k kd)
                                       (inv_pos Z_thermo_r Z_thermo_r_pos))
                                 (mult (tail_mass_of_r k kd)
                                       (inv_pos Z_thermo_r Z_thermo_r_pos)))
                           (mult (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd))
                                 (inv_pos Z_thermo_r Z_thermo_r_pos))
                           (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                 (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd)))).
          -- exact (req_sym _ _ (req_mult_plus_distr_r (evicted_partition_of_r k kd)
                                  (tail_mass_of_r k kd) (inv_pos Z_thermo_r Z_thermo_r_pos))).
          -- exact (mult_comm (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd))
                              (inv_pos Z_thermo_r Z_thermo_r_pos)).
    - apply (req_trans (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                             (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd)))
                       (mult (inv_pos Z_thermo_r Z_thermo_r_pos) Z_thermo_r) one).
      + apply (req_trans (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                               (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                               (plus (tail_mass_of_r k kd) (evicted_partition_of_r k kd)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos) Z_thermo_r)).
        * exact (req_mult_compat _ _ _ _ (req_refl _)
                    (plus_comm (evicted_partition_of_r k kd) (tail_mass_of_r k kd))).
        * exact (req_mult_compat _ _ _ _ (req_refl _)
                    (ag_tail_plus_kept_full k kd)).
      + apply (req_trans (mult (inv_pos Z_thermo_r Z_thermo_r_pos) Z_thermo_r)
                         (mult Z_thermo_r (inv_pos Z_thermo_r Z_thermo_r_pos)) one).
        * exact (mult_comm (inv_pos Z_thermo_r Z_thermo_r_pos) Z_thermo_r).
        * exact (inv_pos_correct Z_thermo_r Z_thermo_r_pos). }
  assert (Hk3 : req (req_minus one (mult (evicted_partition_of_r k kd)
                                         (inv_pos Z_thermo_r Z_thermo_r_pos)))
                    (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
  { apply (req_trans (req_minus one (mult (evicted_partition_of_r k kd)
                                          (inv_pos Z_thermo_r Z_thermo_r_pos)))
                     (req_minus (plus (mult (evicted_partition_of_r k kd)
                                            (inv_pos Z_thermo_r Z_thermo_r_pos))
                                      (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                            (tail_mass_of_r k kd)))
                                (mult (evicted_partition_of_r k kd)
                                      (inv_pos Z_thermo_r Z_thermo_r_pos)))
                     (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
    - exact (reqd_minus_compat _ _ _ _ (req_sym _ _ Hk2) (req_refl _)).
    - exact (req_minus_plus_cancel_r (mult (evicted_partition_of_r k kd)
                                           (inv_pos Z_thermo_r Z_thermo_r_pos))
                (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))). }
  apply (req_trans (plus (mult (evicted_partition_of_r k kd)
                               (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                          (inv_pos Z_thermo_r Z_thermo_r_pos)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd)))
                   (plus (req_minus one (mult (evicted_partition_of_r k kd)
                                              (inv_pos Z_thermo_r Z_thermo_r_pos)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd)))
                   (mult (plus one one) (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                              (tail_mass_of_r k kd)))).
  - exact (req_plus_compat _ _ _ _ Hk1 (req_refl _)).
  - apply (req_trans (plus (req_minus one (mult (evicted_partition_of_r k kd)
                                                (inv_pos Z_thermo_r Z_thermo_r_pos)))
                           (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd)))
                     (plus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))
                           (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd)))
                     (mult (plus one one) (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                (tail_mass_of_r k kd)))).
    + exact (req_plus_compat _ _ _ _ Hk3 (req_refl _)).
    + exact (req_sym _ _ (req_two_mult (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                             (tail_mass_of_r k kd)))).
Qed.

(* the main theorem: strict eviction gives
   [TV(boltzmann, topk renormalized) == tail/Z_thermo] (the req copy
   of the conditionalized exact identity). *)
Theorem ag_topk_tv_identity_strict :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)),
    lt (inv_pos Z_thermo_r Z_thermo_r_pos)
       (inv_pos (evicted_partition_of_r k kd) Hkpos) ->
    req (tv_dist_r boltzmann_dist_attn_r (topk_renorm_r k kd Hkpos))
        (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd)).
Proof.
  intros k kd Hkpos Hst.
  assert (Hpt : req (sumf (fun s : S =>
                       abs (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                            (boltzmann_factor_r s))
                                      (topk_renorm_r k kd Hkpos s))))
                    (sumf (fun s : S => if kd s
                                        then mult (boltzmann_factor_r s)
                                                  (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                             (inv_pos Z_thermo_r Z_thermo_r_pos))
                                        else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                  (boltzmann_factor_r s))))
    by exact (sum_ext _ _ (fun s : S => ag_tv_pointwise k kd Hkpos s Hst)).
  unfold tv_dist_r, boltzmann_dist_attn_r.
  apply (req_trans _ (mult (inv_pos (plus one one) req_two_pos)
                           (sumf (fun s : S =>
                              if kd s
                              then mult (boltzmann_factor_r s)
                                        (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                   (inv_pos Z_thermo_r Z_thermo_r_pos))
                              else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                        (boltzmann_factor_r s)))) _).
  - exact (req_mult_compat _ _ _ _ (req_refl _) Hpt).
  - apply (req_trans _ (mult (inv_pos (plus one one) req_two_pos)
                             (plus (mult (evicted_partition_of_r k kd)
                                         (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                    (inv_pos Z_thermo_r Z_thermo_r_pos)))
                                   (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                         (tail_mass_of_r k kd)))) _).
    + exact (req_mult_compat _ _ _ _ (req_refl _)
                (ag_tv_sum_decomp k kd Hkpos)).
    + apply (req_trans _ (mult (inv_pos (plus one one) req_two_pos)
                               (mult (plus one one)
                                     (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (tail_mass_of_r k kd)))) _).
      * exact (req_mult_compat _ _ _ _ (req_refl _)
                  (ag_tv_sum_collapse k kd Hkpos)).
      * apply (req_trans (mult (inv_pos (plus one one) req_two_pos)
                               (mult (plus one one)
                                     (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (tail_mass_of_r k kd))))
                         (mult (mult (inv_pos (plus one one) req_two_pos) (plus one one))
                               (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                     (tail_mass_of_r k kd)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
        -- exact (mult_assoc (inv_pos (plus one one) req_two_pos) (plus one one)
                    (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
        -- apply (req_trans (mult (mult (inv_pos (plus one one) req_two_pos) (plus one one))
                                  (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                        (tail_mass_of_r k kd)))
                            (mult one (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                            (tail_mass_of_r k kd)))
                            (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
           ++ exact (req_mult_compat _ _ _ _
                       (req_trans (mult (inv_pos (plus one one) req_two_pos) (plus one one))
                                  (mult (plus one one) (inv_pos (plus one one) req_two_pos))
                                  one
                                  (mult_comm (inv_pos (plus one one) req_two_pos) (plus one one))
                                  (inv_pos_correct (plus one one) req_two_pos))
                       (req_refl _)).
           ++ apply (req_trans (mult one (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                               (tail_mass_of_r k kd)))
                               (mult (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (tail_mass_of_r k kd)) one)
                               (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                     (tail_mass_of_r k kd))).
              ** exact (mult_comm one (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                            (tail_mass_of_r k kd))).
              ** exact (mult_one (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                       (tail_mass_of_r k kd))).
Qed.

(* ============================================================ *)
(*   ---------------------------------------------------------------- *)
(*   A. The eps-wise bounded-sum machine (three genuinely proved   *)
(*   lemmas).  It depends on the interface min/r_max eps-wise      *)
(*   fields (baseline L40529-40539: [min_le_l]/[r_max_le_l]/       *)
(*   [r_max_l_iff], all in eps-wise form) plus the in-section      *)
(*   premises [sum_le]/[sum_add]/[sum_ext]; the plain form is not  *)
(*   derivable (the order has no cancellation, as with             *)
(*   [metric_nonneg] in RestB Part 4), so the machine is stated in *)
(*   the eps-wise caliber — isomorphic to the interface's native   *)
(*   form (the same caliber as [log_le_linear_eps]).  The proof    *)
(*   core is pure algebra ([softmax_temp_relative] +               *)
(*   [exp_neg_le_decr] + [le_mult_compat_r]); the machine lemmas   *)
(*   (group A) stand alone, while the transplanted statements      *)
(*   (group B) assemble along the Id pure-algebra path.            *)
(*   B. Gap concentration + the zero-temperature limit (transplant *)
(*   of the baseline L28337 region; proved/assembled).  Convention *)
(*   notes (along the earlier [ag_softmax_temp_relative]): the Id  *)
(*   [e^{+z/T}]-convention premise [minus (z s_star) (z s)]        *)
(*   becomes the req-native [e^{-z/T}] (Boltzmann) convention      *)
(*   premise [req_minus (z s) (z s_star)] (the gap position is the *)
(*   positive half-axis of the loss difference); the conclusion    *)
(*   factor [exp_neg (invT·gamma)] is identical under both         *)
(*   conventions; [softmax_temp] becomes [reqd_softmax_temp_param]*)
(*   C. The annealing engine (a coefficient-generalized replay of  *)
(*   group B, consumed by group D).  [ag_softmax_temp_relative]    *)
(*   with the temperature position generalized to a free           *)
(*   coefficient [kappa] over the [reqd_softmax_scaled] family;    *)
(*   the group-T statements' signatures carry no temperature       *)
(*   position, so this honest replay is not a downgrade.           *)
(*   D. The T→0 completion, eps-wise (the constructive reading of  *)
(*   the Id comment semantics L28330-28335).                       *)
(*   [ag_hard_attention_collapse_eps]: for every [eps > 0] there   *)
(*   is an inverse-temperature coefficient [kappa := (1/T)·2^N]    *)
(*   making the ratio [<= eps] (temperature [1/κ → 0] as the Id    *)
(*   "T→0").                                                      *)
(*                                                                  *)
(*   The closure lemmas [req_r_pow]/[req_r_pow_pos] plus the       *)
(*   premise position [exp_neg_geo_break] (a same-position         *)
(*   transplant of the UpReqCauchy [r_arch_pow] Variable;          *)
(*   satisfiable by the Real instance since [2^N·d → ∞]).          *)
(*   Honest boundary note: the [cauchy_complete]/[lim] fields are  *)
(*   in the interface (L40589-40596), but the [lim u zero] form    *)
(*   needs the metric-norm compatibility premise group           *)
(*   ([metric_abs_norm]/[abs_nonneg_plain]/[lim_metric_approx]/    *)
(*   [le_all_eps_zero] — all living as Variables inside the        *)
(*   UpReqCauchy section, with no corresponding interface fields); *)
(*   that is the precise landing point of the "chain length" in   *)
(*   the original conclusion.  This section delivers the same      *)
(*   semantic content in the interface's native eps-wise form, and *)
(*   the four-field group is listed as a future upgrade path   *)
(*   (not fabricated).                                             *)
(* ============================================================ *)

(* ---- A. the eps-wise bounded-sum machine (three genuinely proved lemmas) ---- *)

(* upper bound: [Σf <= Σ(r_max f g) + Σ(constant eps)] (pointwise
   [r_max_le_l] via [sum_le], the sums moved out by [sum_add],
   closed by [le_id_l]; genuinely proved). *)
Lemma ag_sum_le_r_max_eps :
  forall (f g : S -> R) (eps : R), lt zero eps ->
    le (sumf f)
       (plus (sumf (fun s : S => r_max (f s) (g s)))
             (sumf (fun _ : S => eps))).
Proof.
  intros f g eps Heps.
  apply (le_trans (sumf f)
                  (sumf (fun s : S => plus (r_max (f s) (g s)) eps))
                  (plus (sumf (fun s : S => r_max (f s) (g s)))
                        (sumf (fun _ : S => eps)))).
  - apply (sum_le f (fun s : S => plus (r_max (f s) (g s)) eps)).
    intro s. exact (r_max_le_l (f s) (g s) eps Heps).
  - apply (le_id_l
             (sumf (fun s : S => plus (r_max (f s) (g s)) eps))
             (plus (sumf (fun s : S => r_max (f s) (g s)))
                   (sumf (fun _ : S => eps)))
             (plus (sumf (fun s : S => r_max (f s) (g s)))
                   (sumf (fun _ : S => eps)))).
    + exact (sum_add (fun s : S => r_max (f s) (g s)) (fun _ : S => eps)).
    + apply le_refl.
Qed.

(* min upper bound: [Σ(min f g) <= Σf + Σ(constant eps)] (pointwise
   [min_le_l] via [sum_le], sums moved out by [sum_add]; genuinely
   proved). *)
Lemma ag_sum_min_le_eps :
  forall (f g : S -> R) (eps : R), lt zero eps ->
    le (sumf (fun s : S => min (f s) (g s)))
       (plus (sumf f) (sumf (fun _ : S => eps))).
Proof.
  intros f g eps Heps.
  apply (le_trans (sumf (fun s : S => min (f s) (g s)))
                  (sumf (fun s : S => plus (f s) eps))
                  (plus (sumf f) (sumf (fun _ : S => eps)))).
  - apply (sum_le (fun s : S => min (f s) (g s))
                  (fun s : S => plus (f s) eps)).
    intro s. exact (min_le_l (f s) (g s) eps Heps).
  - apply (le_id_l
             (sumf (fun s : S => plus (f s) eps))
             (plus (sumf f) (sumf (fun _ : S => eps)))
             (plus (sumf f) (sumf (fun _ : S => eps)))).
    + exact (sum_add f (fun _ : S => eps)).
    + apply le_refl.
Qed.

(* collapse: [g] pointwise [<= f] gives [Σ(r_max f g) == Σf]
   (pointwise [r_max_l_iff] + [sum_ext]; genuinely proved). *)
Lemma ag_sum_r_max_collapse :
  forall f g : S -> R, (forall s : S, le (g s) (f s)) ->
    req (sumf (fun s : S => r_max (f s) (g s))) (sumf f).
Proof.
  intros f g Hle. exact (sum_ext (fun s : S => r_max (f s) (g s)) f (fun s : S => r_max_l_iff (f s) (g s) (Hle s))).
Qed.

(* ---- B. gap concentration + the zero-temperature limit (transplant of the baseline L28337 region) ---- *)

(* gap concentration (genuinely proved: [ag_softmax_temp_relative] +
   [exp_neg_le_decr] + [req_le_mult_compat_r] assembled; see the
   group-B convention notes in the section banner). *)
Theorem ag_softmax_gap_concentration :
  forall (z : S -> R) (s_star : S) (gamma : R),
    lt zero gamma ->
    forall s : S,
      le (mult (inv_pos T T_pos) gamma)
         (mult (inv_pos T T_pos) (req_minus (z s) (z s_star))) ->
      le (reqd_softmax_temp_param S sumf sum_pos T T_pos z s)
         (mult (reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star)
               (exp_neg (mult (inv_pos T T_pos) gamma))).
Proof.
  intros z s_star gamma Hgamma s Hgap.
  apply (le_id_l
           (reqd_softmax_temp_param S sumf sum_pos T T_pos z s)
           (mult (reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star)
                 (exp_neg (mult (inv_pos T T_pos)
                                (req_minus (z s) (z s_star)))))
           (mult (reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star)
                 (exp_neg (mult (inv_pos T T_pos) gamma)))).
  - exact (ag_softmax_temp_relative z s s_star).
  - exact (req_le_mult_compat_r
             (reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star)
             (exp_neg (mult (inv_pos T T_pos) (req_minus (z s) (z s_star))))
             (exp_neg (mult (inv_pos T T_pos) gamma))
             (lt_le_iff zero
                (reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star)
                (inl (ag_softmax_temp_pos z s_star)))
             (exp_neg_le_decr
                (mult (inv_pos T T_pos) gamma)
                (mult (inv_pos T T_pos) (req_minus (z s) (z s_star)))
                Hgap)).
Qed.

(* the zero-temperature limit in ratio form (genuinely proved:
   [ag_softmax_gap_concentration] + the inverse-cancellation chain,
   a replay isomorphic to [req_markov_temperature_zero_limit]). *)
Theorem ag_temperature_zero_limit :
  forall (z : S -> R) (s_star : S) (gamma : R),
    lt zero gamma ->
    forall s : S,
      le (mult (inv_pos T T_pos) gamma)
         (mult (inv_pos T T_pos) (req_minus (z s) (z s_star))) ->
      le (mult (reqd_softmax_temp_param S sumf sum_pos T T_pos z s)
               (inv_pos (reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star)
                        (ag_softmax_temp_pos z s_star)))
         (exp_neg (mult (inv_pos T T_pos) gamma)).
Proof.
  intros z s_star gamma Hgamma s Hgap.
  pose (A := reqd_softmax_temp_param S sumf sum_pos T T_pos z s).
  pose (B := reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star).
  pose (HB := ag_softmax_temp_pos z s_star).
  pose (C := exp_neg (mult (inv_pos T T_pos) gamma)).
  assert (Hgc : le A (mult B C)).
  { exact (ag_softmax_gap_concentration z s_star gamma Hgamma s Hgap). }
  assert (Hinv : le zero (inv_pos B HB)).
  { apply (lt_le_iff zero (inv_pos B HB)). left. apply inv_pos_pos. }
  assert (Hdiv : le (mult (inv_pos B HB) A) (mult (inv_pos B HB) (mult B C)))
    by exact (req_le_mult_compat_r (inv_pos B HB) A (mult B C) Hinv Hgc).
  assert (Hsw : req (mult A (inv_pos B HB)) (mult (inv_pos B HB) A))
    by exact (mult_comm A (inv_pos B HB)).
  assert (Hlhs : le (mult A (inv_pos B HB)) (mult (inv_pos B HB) (mult B C)))
    by exact (le_id_l _ _ _ Hsw Hdiv).
  assert (Hrhs : req (mult (inv_pos B HB) (mult B C)) C).
  { exact (req_trans
             (mult (inv_pos B HB) (mult B C))
             (mult (mult (inv_pos B HB) B) C)
             C
             (mult_assoc (inv_pos B HB) B C)
             (req_trans
                (mult (mult (inv_pos B HB) B) C)
                (mult one C)
                C
                (req_mult_compat (mult (inv_pos B HB) B) one C C
                   (req_trans (mult (inv_pos B HB) B)
                              (mult B (inv_pos B HB))
                              one
                              (mult_comm (inv_pos B HB) B)
                              (inv_pos_correct B HB))
                   (req_refl C))
                (req_trans (mult one C) (mult C one) C
                   (mult_comm one C) (mult_one C)))). }
  assert (Hfin : le (mult A (inv_pos B HB)) C) by exact (le_id_r _ _ _ Hrhs Hlhs).
  unfold A, B, C in Hfin. exact Hfin.
Qed.

(* ---- C. the annealing engine (coefficient-generalized replay; consumed by group D) ---- *)

(* the scaled-family relative form: [ag_softmax_temp_relative] with
   the temperature position generalized to [kappa] (genuinely
   proved). *)
Lemma ag_softmax_scaled_relative :
  forall (kappa : R) (z : S -> R) (s s' : S),
    req (reqd_softmax_scaled S sumf sum_pos kappa z s)
        (mult (reqd_softmax_scaled S sumf sum_pos kappa z s')
              (exp_neg (mult kappa (req_minus (z s) (z s'))))).
Proof.
  intros kappa z s s'.
  assert (Hzs : req (z s) (plus (z s') (req_minus (z s) (z s'))))
    by exact (req_sym _ _ (req_minus_plus_cancel (z s') (z s))).
  assert (Hf : req (exp_neg (mult kappa (z s)))
                   (mult (exp_neg (mult kappa (z s')))
                         (exp_neg (mult kappa (req_minus (z s) (z s')))))).
  { exact (req_trans
             (exp_neg (mult kappa (z s)))
             (exp_neg (plus (mult kappa (z s'))
                            (mult kappa (req_minus (z s) (z s')))))
             (mult (exp_neg (mult kappa (z s')))
                   (exp_neg (mult kappa (req_minus (z s) (z s')))))
             (exp_neg_req_compat_setoid
                (mult kappa (z s))
                (plus (mult kappa (z s'))
                      (mult kappa (req_minus (z s) (z s'))))
                (req_trans (mult kappa (z s))
                           (mult kappa (plus (z s') (req_minus (z s) (z s'))))
                           (plus (mult kappa (z s'))
                                 (mult kappa (req_minus (z s) (z s'))))
                           (req_mult_compat kappa kappa (z s)
                              (plus (z s') (req_minus (z s) (z s')))
                              (req_refl _) Hzs)
                           (distrib kappa (z s') (req_minus (z s) (z s')))))
             (exp_neg_plus (mult kappa (z s'))
                           (mult kappa (req_minus (z s) (z s'))))). }
  unfold reqd_softmax_scaled.
  pose (Pw := (fun s0 : S => exp_neg (mult kappa (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult kappa (z s0))))).
  pose (IV := (inv_pos (sumf Pw) Wp)).
  assert (Has : req (mult (exp_neg (mult kappa (z s))) IV)
                   (mult IV
                      (mult (exp_neg (mult kappa (z s')))
                            (exp_neg (mult kappa
                                           (req_minus (z s) (z s'))))))).
  { apply (req_trans _ (mult IV (exp_neg (mult kappa (z s)))) _).
    - exact (mult_comm (exp_neg (mult kappa (z s))) IV).
    - exact (req_mult_compat IV IV (exp_neg (mult kappa (z s)))
                (mult (exp_neg (mult kappa (z s')))
                      (exp_neg (mult kappa (req_minus (z s) (z s')))))
                (req_refl _) Hf). }
  assert (Har : req (mult IV
                       (mult (exp_neg (mult kappa (z s')))
                             (exp_neg (mult kappa (req_minus (z s) (z s'))))))
                   (mult (mult (exp_neg (mult kappa (z s'))) IV)
                         (exp_neg (mult kappa (req_minus (z s) (z s')))))).
  { exact (req_trans
             (mult IV
                (mult (exp_neg (mult kappa (z s')))
                      (exp_neg (mult kappa (req_minus (z s) (z s'))))))
             (mult (mult IV (exp_neg (mult kappa (z s'))))
                   (exp_neg (mult kappa (req_minus (z s) (z s')))))
             (mult (mult (exp_neg (mult kappa (z s'))) IV)
                   (exp_neg (mult kappa (req_minus (z s) (z s')))))
             (mult_assoc IV (exp_neg (mult kappa (z s')))
                (exp_neg (mult kappa (req_minus (z s) (z s')))))
             (req_mult_compat (mult IV (exp_neg (mult kappa (z s'))))
                (mult (exp_neg (mult kappa (z s'))) IV)
                (exp_neg (mult kappa (req_minus (z s) (z s'))))
                (exp_neg (mult kappa (req_minus (z s) (z s'))))
                (mult_comm IV (exp_neg (mult kappa (z s'))))
                (req_refl _))). }
  apply (req_trans _ (mult IV
         (mult (exp_neg (mult kappa (z s')))
               (exp_neg (mult kappa (req_minus (z s) (z s')))))) _).
  - exact Has.
  - exact Har.
Qed.

(* gap concentration for the scaled family (the [kappa]-generalization
   of [ag_softmax_gap_concentration]; proved in the same shape). *)
Lemma ag_softmax_scaled_gap :
  forall (kappa : R) (z : S -> R) (s_star : S) (gamma : R) (s : S),
    le (mult kappa gamma) (mult kappa (req_minus (z s) (z s_star))) ->
    le (reqd_softmax_scaled S sumf sum_pos kappa z s)
       (mult (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
             (exp_neg (mult kappa gamma))).
Proof.
  intros kappa z s_star gamma s Hgap.
  apply (le_id_l
           (reqd_softmax_scaled S sumf sum_pos kappa z s)
           (mult (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
                 (exp_neg (mult kappa (req_minus (z s) (z s_star)))))
           (mult (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
                 (exp_neg (mult kappa gamma)))).
  - exact (ag_softmax_scaled_relative kappa z s s_star).
  - exact (req_le_mult_compat_r
             (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
             (exp_neg (mult kappa (req_minus (z s) (z s_star))))
             (exp_neg (mult kappa gamma))
             (lt_le_iff zero (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
                        (inl (ag_softmax_scaled_pos kappa z s_star)))
             (exp_neg_le_decr (mult kappa gamma)
                              (mult kappa (req_minus (z s) (z s_star)))
                              Hgap)).
Qed.

(* the ratio form for the scaled family (the [kappa]-generalization
   of [ag_temperature_zero_limit]; proved in the same shape). *)
Lemma ag_softmax_scaled_ratio_limit :
  forall (kappa : R) (z : S -> R) (s_star : S) (gamma : R) (s : S),
    le (mult kappa gamma) (mult kappa (req_minus (z s) (z s_star))) ->
    le (mult (reqd_softmax_scaled S sumf sum_pos kappa z s)
             (inv_pos (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
                      (ag_softmax_scaled_pos kappa z s_star)))
       (exp_neg (mult kappa gamma)).
Proof.
  intros kappa z s_star gamma s Hgap.
  pose (A := reqd_softmax_scaled S sumf sum_pos kappa z s).
  pose (B := reqd_softmax_scaled S sumf sum_pos kappa z s_star).
  pose (HB := ag_softmax_scaled_pos kappa z s_star).
  pose (C := exp_neg (mult kappa gamma)).
  assert (Hgc : le A (mult B C)).
  { exact (ag_softmax_scaled_gap kappa z s_star gamma s Hgap). }
  assert (Hinv : le zero (inv_pos B HB)).
  { apply (lt_le_iff zero (inv_pos B HB)). left. apply inv_pos_pos. }
  assert (Hdiv : le (mult (inv_pos B HB) A) (mult (inv_pos B HB) (mult B C)))
    by exact (req_le_mult_compat_r (inv_pos B HB) A (mult B C) Hinv Hgc).
  assert (Hsw : req (mult A (inv_pos B HB)) (mult (inv_pos B HB) A))
    by exact (mult_comm A (inv_pos B HB)).
  assert (Hlhs : le (mult A (inv_pos B HB)) (mult (inv_pos B HB) (mult B C)))
    by exact (le_id_l _ _ _ Hsw Hdiv).
  assert (Hrhs : req (mult (inv_pos B HB) (mult B C)) C).
  { exact (req_trans
             (mult (inv_pos B HB) (mult B C))
             (mult (mult (inv_pos B HB) B) C)
             C
             (mult_assoc (inv_pos B HB) B C)
             (req_trans
                (mult (mult (inv_pos B HB) B) C)
                (mult one C)
                C
                (req_mult_compat (mult (inv_pos B HB) B) one C C
                   (req_trans (mult (inv_pos B HB) B)
                              (mult B (inv_pos B HB))
                              one
                              (mult_comm (inv_pos B HB) B)
                              (inv_pos_correct B HB))
                   (req_refl C))
                (req_trans (mult one C) (mult C one) C
                   (mult_comm one C) (mult_one C)))). }
  assert (Hfin : le (mult A (inv_pos B HB)) C) by exact (le_id_r _ _ _ Hrhs Hlhs).
  unfold A, B, C in Hfin. exact Hfin.
Qed.

(* ---- D. the T→0 completion, eps-wise (lim-cluster dependencies + a transplanted premise position) ---- *)

(* the eps-wise geometric-breakdown premise position (a same-position
   transplant of the UpReqCauchy [r_arch_pow] Variable; exponential
   form: [exp_neg (2^N·d) <= eps].  Satisfiable by the Real instance
   since [2^N·d → ∞]; at [End] it enters the closure signature as an
   explicit premise and [Print Assumptions] stays Closed). *)
Hypothesis exp_neg_geo_break :
  forall d : R, lt zero d ->
    forall eps : R, lt zero eps ->
      sigT (fun N : nat =>
        le (exp_neg (mult (req_r_pow (plus one one) N) d)) eps).

(* the T→0 semantics completed: for every [eps > 0] there is an
   inverse-temperature coefficient [kappa := (1/T)·2^N] making the
   softmax ratio [<= eps] (temperature [1/κ → 0] as the Id "T→0"
   reading — the constructive eps-wise form of hard-attention
   collapse; depends on the [exp_neg_geo_break] premise position +
   UpReqCauchy [req_r_pow]/[req_r_pow_pos]/[req_mult_swap_mid] + the
   three group-C lemmas). *)
Theorem ag_hard_attention_collapse_eps :
  forall (z : S -> R) (s_star : S) (gamma : R) (s : S),
    lt zero gamma ->
    le (mult (inv_pos T T_pos) gamma)
       (mult (inv_pos T T_pos) (req_minus (z s) (z s_star))) ->
    forall eps : R, lt zero eps ->
    sigT (fun kappa : R =>
      le (mult (reqd_softmax_scaled S sumf sum_pos kappa z s)
               (inv_pos (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
                        (ag_softmax_scaled_pos kappa z s_star)))
          eps).
Proof.
  intros z s_star gamma s Hgamma Hgap eps Heps.
  destruct (exp_neg_geo_break (mult (inv_pos T T_pos) gamma)
             (mult_positive (inv_pos T T_pos) gamma (inv_pos_pos T T_pos) Hgamma)
             eps Heps)
    as [N HN].
  exists (mult (inv_pos T T_pos) (req_r_pow (plus one one) N)).
  (* [kappa·x == 2^N·(invT·x)] (coefficient swap, [req_mult_swap_mid] + [mult_comm]). *)
  assert (Hkap : forall x : R,
           req (mult (mult (inv_pos T T_pos) (req_r_pow (plus one one) N)) x)
               (mult (req_r_pow (plus one one) N) (mult (inv_pos T T_pos) x))).
  { intro x.
    exact (req_trans
             (mult (mult (inv_pos T T_pos) (req_r_pow (plus one one) N)) x)
             (mult (mult (inv_pos T T_pos) x) (req_r_pow (plus one one) N))
             (mult (req_r_pow (plus one one) N) (mult (inv_pos T T_pos) x))
             (req_mult_swap_mid (inv_pos T T_pos)
                                (req_r_pow (plus one one) N) x)
             (mult_comm (mult (inv_pos T T_pos) x)
                        (req_r_pow (plus one one) N))). }
  (* rescaling the gap: [kappa·gamma <= kappa·(z s − z s_star)] ([Hgap] multiplied by [2^N]). *)
  assert (Hscale : le (mult (mult (inv_pos T T_pos)
                                  (req_r_pow (plus one one) N)) gamma)
                      (mult (mult (inv_pos T T_pos)
                                  (req_r_pow (plus one one) N))
                            (req_minus (z s) (z s_star)))).
  { apply (le_id_l
             (mult (mult (inv_pos T T_pos) (req_r_pow (plus one one) N)) gamma)
             (mult (req_r_pow (plus one one) N) (mult (inv_pos T T_pos) gamma))
             (mult (mult (inv_pos T T_pos) (req_r_pow (plus one one) N))
                   (req_minus (z s) (z s_star)))
             (Hkap gamma)
             (le_id_r
                (mult (req_r_pow (plus one one) N)
                      (mult (inv_pos T T_pos) gamma))
                (mult (req_r_pow (plus one one) N)
                      (mult (inv_pos T T_pos) (req_minus (z s) (z s_star))))
                (mult (mult (inv_pos T T_pos) (req_r_pow (plus one one) N))
                      (req_minus (z s) (z s_star)))
                (req_sym _ _
                   (Hkap (req_minus (z s) (z s_star))))
                (req_le_mult_compat_r (req_r_pow (plus one one) N)
                   (mult (inv_pos T T_pos) gamma)
                   (mult (inv_pos T T_pos) (req_minus (z s) (z s_star)))
                   (lt_le_iff zero (req_r_pow (plus one one) N)
                      (inl (req_r_pow_pos (plus one one) N req_two_pos)))
                   Hgap))). }
  apply (le_trans
           (mult (reqd_softmax_scaled S sumf sum_pos
                    (mult (inv_pos T T_pos) (req_r_pow (plus one one) N)) z s)
                 (inv_pos
                    (reqd_softmax_scaled S sumf sum_pos
                       (mult (inv_pos T T_pos) (req_r_pow (plus one one) N))
                       z s_star)
                    (ag_softmax_scaled_pos
                       (mult (inv_pos T T_pos) (req_r_pow (plus one one) N))
                       z s_star)))
           (exp_neg (mult (mult (inv_pos T T_pos)
                                (req_r_pow (plus one one) N)) gamma))
           eps).
  - exact (ag_softmax_scaled_ratio_limit
             (mult (inv_pos T T_pos) (req_r_pow (plus one one) N))
             z s_star gamma s Hscale).
  - exact (le_id_l
             (exp_neg (mult (mult (inv_pos T T_pos)
                                  (req_r_pow (plus one one) N)) gamma))
             (exp_neg (mult (req_r_pow (plus one one) N)
                            (mult (inv_pos T T_pos) gamma)))
             eps
             (exp_neg_req_compat_setoid
                (mult (mult (inv_pos T T_pos) (req_r_pow (plus one one) N))
                      gamma)
                (mult (req_r_pow (plus one one) N)
                      (mult (inv_pos T T_pos) gamma))
                (Hkap gamma))
             HN).
Qed.

(* ============================================================ *)


(*   Id originals excerpted:                                         *)
(*   row 3, L28494 [Definition partition_function_temp_param         *)
(*     (T0 : R) (HT0 : lt zero T0) (z : logits) := sum_over_S        *)
(*     (fun s => exp_pos_fn (mult (inv_pos T0 HT0) (z s)))];         *)
(*     L28500 [partition_function_temp_param_pos]: forall T0 HT0 z,  *)
(*     [lt zero (partition_function_temp_param T0 HT0 z)] (proved by *)
(*     [sum_pos_preserved] + [exp_neg_pos]).                         *)
(*   row 2, L29573 [Theorem eviction_db_zero_full]: (forall s,       *)
(*     keep s) -> [Id evicted_partition Z_thermo] -> forall s s' : S,*)
(*     [Id (db_breaking s s') zero] (proved by                       *)
(*     [eviction_boltzmann_full] + [eviction_transition_full] + the  *)
(*     detailed_balance section Variable + [minus_self_zero] +       *)
(*     [abs_zero]).                                                  *)
(*   Id→req difference notes (genuinely proved, not transcribed):    *)
(*     - [sum_over_S] becomes [sumf] (the in-section three-property  *)
(*       honest interface) and [sum_pos_preserved] becomes the       *)
(*       [sum_pos] premise position; [exp_pos_fn] becomes          *)
(*       [exp_pos_fn_setoid] (the req copy);                         *)
(*     - [minus] becomes [req_minus] (UpReqAlgebra L728              *)
(*       [req_minus_self_zero]); Id identity chains become           *)
(*       [req_trans] chains with [req_mult_compat] arms;             *)
(*     - [detailed_balance] (an Id section Variable) becomes the     *)
(*       honest premise position [detailed_balance_r], a pointwise   *)
(*       copy;                                                       *)
(*     - abs elimination: the interface field [abs_zero]             *)
(*       ([req (abs zero) zero]) is pulled back through              *)
(*       [req_abs_compat], with no new axioms.                       *)
(*     row 1 (L29385) keeps its distinct form and stays out of       *)
(*     scope; row 2 (L29573) is discharged below.                    *)
(* ============================================================ *)

(* ---- row 3: the temperature-parameterized partition function (a copy) ---- *)
Definition partition_function_temp_param_r (T0 : R) (HT0 : lt zero T0)
  (z : S -> R) : R :=
  sumf (fun s : S => exp_pos_fn_setoid (mult (inv_pos T0 HT0) (z s))).

(* ---- the row-3 counterpart (genuinely proved: the [sum_pos]
   premise position + [exp_neg_pos], the same proof shape as the
   earlier [ag_partition_function_temp_pos]) ---- *)
Lemma ag_partition_function_temp_param_pos :
  forall (T0 : R) (HT0 : lt zero T0) (z : S -> R),
    lt zero (partition_function_temp_param_r T0 HT0 z).
Proof.
  intros T0 HT0 z.
  unfold partition_function_temp_param_r.
  apply sum_pos.
  intro s. exact (exp_neg_pos (opp (mult (inv_pos T0 HT0) (z s)))).
Qed.

(* ---- the [detailed_balance] honest interface position (a pointwise
   req copy of the baseline section Variable; [boltzmann_dist_attn]
   becomes [boltzmann_dist_attn_r], Id becomes req) ---- *)
Hypothesis detailed_balance_r :
  forall s s' : S,
    req (mult (boltzmann_dist_attn_r s) (transition s s'))
        (mult (boltzmann_dist_attn_r s') (transition s' s)).

(* ---- the row-2 counterpart: full retention gives zero breaking —
   eviction is the only source of breaking.  Assembled genuine
   proof: [ag_eviction_boltzmann_full] (the L29555 counterpart) +
   [ag_eviction_transition_full] (the L29540 counterpart) +
   [detailed_balance_r] + [req_minus_self_zero] +
   [req_abs_compat]/[abs_zero] — no new axioms. ---- *)
Theorem ag_eviction_db_zero_full :
  (forall s : S, keep s) ->
  req evicted_partition_r Z_thermo_r ->
  forall s s' : S, req (db_breaking_r s s') zero.
Proof.
  intros Hkall HZ s s'.
  unfold db_breaking_r.
  assert (Heb : forall t : S, req (evicted_boltzmann_r t) (boltzmann_dist_attn_r t))
    by exact (ag_eviction_boltzmann_full Hkall HZ).
  assert (Het : forall t u : S, req (evicted_transition_r t u) (transition t u))
    by exact (ag_eviction_transition_full Hkall).
  assert (Harg : req (req_minus (mult (evicted_boltzmann_r s) (evicted_transition_r s s'))
                                (mult (evicted_boltzmann_r s') (evicted_transition_r s' s)))
                     zero).
  { apply (req_minus_self_zero
             (mult (evicted_boltzmann_r s) (evicted_transition_r s s'))
             (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))).
    apply (req_trans
             (mult (evicted_boltzmann_r s) (evicted_transition_r s s'))
             (mult (boltzmann_dist_attn_r s) (transition s s'))
             (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))).
    - exact (req_mult_compat (evicted_boltzmann_r s) (boltzmann_dist_attn_r s)
                (evicted_transition_r s s') (transition s s')
                (Heb s) (Het s s')).
    - apply (req_trans
               (mult (boltzmann_dist_attn_r s) (transition s s'))
               (mult (boltzmann_dist_attn_r s') (transition s' s))
               (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))).
      + exact (detailed_balance_r s s').
      + exact (req_sym _ _
                  (req_mult_compat (evicted_boltzmann_r s') (boltzmann_dist_attn_r s')
                    (evicted_transition_r s' s) (transition s' s)
                    (Heb s') (Het s' s))). }
  exact (req_trans
           (abs (req_minus (mult (evicted_boltzmann_r s) (evicted_transition_r s s'))
                           (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))))
           (abs zero) zero
           (req_abs_compat _ _ Harg) abs_zero).
Qed.

End ReqAttnGibbs.

(* ---- assumption audit of the discharged statements (end of file) ---- *)
Print Assumptions ag_temp_is_scale_duality.
Print Assumptions ag_scale_sqrt_witness_dual.
Print Assumptions ag_half_scale_is_temp_two.
Print Assumptions ag_sq_witness_4.
Print Assumptions ag_opp_zero_cc.
Print Assumptions ag_minus_zero_cc.
