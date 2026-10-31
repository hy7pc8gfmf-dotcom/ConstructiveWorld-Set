(* ====================================================================
   UpEntropyGainReq.v - entropy-gain family, req-carrier companion.
Mission.  Formulation of the properties stated by the entropy-gain family's req-carrier companion piece: 11 pieces = 4 Id-statement lemmas + 1 Id-assumption slot + 6 Id-transport theorems (grep census 11 declarations; plan said ~10, actual 11, all delivered, zero frozen).  Piece map (req name <- source module attn/UpEntropyGain.v, list A2 second_law_irreversible, Id original @ line; companion pieces live in a standalone req_* Section of the same tree): 1 req_dynamics_gradient_step (slot) L64; 2 req_eg_minus_def (delta piece) L84; 3 req_eg_minus_plus_cancel L88; 4 req_eg_step_diff L99; 5 req_eg_step_neg_diff L115; 6 req_eg_minus_pos L131; 7 req_eg_tangent_shift L141; 8 req_eg_grad_lower L228; 9 req_entropy_step_gain_lower (main one) L327; 10 req_entropy_gain_positive L379; 11 req_second_law_quant (main two) L409.
Ablation drop-piece provenance: the original text is kept verbatim; only the proof bodies of the two listed statements req_eg_minus_pos (orig L204, 4-sentence toy proof) and req_eg_minus_def (orig L95, 3-sentence toy proof) are replaced by toy proofs (substantive-nontrivial three criteria: definitional controlled unfolding / explicit witness direct extraction / structural replay, engine positions surveyed in advance); statement face and reference face untouched, zero new Requires, proof-closing marks conserved piece by piece, purely constructive closure, trailing Print Assumptions surface kept.  Identity conservation: the two listed proof bodies are verbatim-identical to the Main current-version original (blade body = original body).
Dependencies.  Requires S01_BaseRing .. S15_TailFEPUp + UpReqAlgebra + UpReqDist (17 pieces, all present in tree 109) and the CW base as in the source module's dependency face (CW_ConstructiveWorld_219).
References.  Source module attn/UpEntropyGain.v line anchors as in the piece map above; batch-1 registry table slot 1 for the delta piece.
Constructivity.  Zero conceding statements (mechanically checked).  Honest interface: assumption slots preserved bit-for-bit, zero amplification.  gradient_lipschitz / entropy_tangent: le statements, zero Id content, only minus -> req_minus shape-shift (source module L68/L71).  abs_ge_value: source module L76; the setoid interface has no le a (abs a) field (only per-eps abs_nonneg), slot kept as-is.  lt_plus_compat_lt_le: source module L78; the setoid interface only has the strict-strict lt_plus_compat field, slot kept as-is.  Piece 2 is the delta piece: req_minus definitional unfolding (batch-1 registry table 1).  Id-layer statements are carried by assumption slots with per-eps reification; each Variable premise kept in place.
Nontriviality grading: piece 8 = A+ (longest req chain of this file, segments (i)-(vi) all req-transport); pieces 4/5/7/9/11 = A (multi-hop req chains, true proofs); pieces 3/6 = A- (short chains); piece 10 = B (cascaded assembly); piece 2 = delta trivial; piece 1 = slot transport.  Discipline: pure term-mode (zero rewrite, zero Morphisms); statements all Set-level (req/le/lt are interface Set fields, zero Prop leakage); all closed by Qed.
Build.  rocq c -native-compiler no -q -Q . "" UpEntropyGainReq.v.  Adaptation note: this tree's interface class is unparameterized with carrier Real, so the Section runs without the RIS context and Notation R := Real after Import RealInterfaceEnhancedMod (precedent UpReqAlgebra:47-49, nw1 ToyR piece).
   ==================================================================== *)

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
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the
   global Real (same adaptation as UpReqAlgebra / nw1 ToyR precedent). *)
Notation R := Real.

Section EntropyGainReq.

(* ===== Honest interface (source module L59-79, req-carried) ===== *)
Variable entropy : R -> R.
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.
Variable eta_pos : lt zero eta.

(* Piece 1: source module L64 dynamics_gradient_step, req shape (slot preserved bit-for-bit) *)
Variable req_dynamics_gradient_step : forall x : R,
  req (dynamics x) (plus x (mult eta (entropy_gradient x))).

Variable L : R.
Variable L_pos : lt zero L.
(* le statement, zero Id content, minus -> req_minus shape-shift (source module L68) *)
Variable gradient_lipschitz : forall x y : R,
  le (abs (req_minus (entropy_gradient x) (entropy_gradient y)))
     (mult L (abs (req_minus x y))).
(* le statement, zero Id content, minus -> req_minus shape-shift (source module L71) *)
Variable entropy_tangent : forall x y : R,
  le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (req_minus y x))).
(* Source module L76: the setoid interface has no le a (abs a) field, slot kept *)
Variable abs_ge_value : forall a : R, le a (abs a).
(* Source module L78: the setoid interface only has the strict-strict field, slot kept *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* ===== Piece 2: subtraction delta piece (req_minus definitional unfolding; source module L84 id_refl) ===== *)
Lemma req_eg_minus_def : forall a b : R, req (req_minus a b) (plus a (opp b)).
Proof.
  intros a b.
  unfold req_minus.
  exact (req_refl (plus a (opp b))).
Qed.

(* ===== Piece 3: subtraction invertible (source module L88 chain, req field at each hop) ===== *)
Lemma req_eg_minus_plus_cancel : forall a b : R,
  req (plus (req_minus a b) b) a.
Proof.
  intros a b. unfold req_minus.
  apply (req_trans (plus (plus a (opp b)) b) (plus a (plus (opp b) b)) a).
  - exact (req_sym (plus a (plus (opp b) b)) (plus (plus a (opp b)) b)
                   (plus_assoc a (opp b) b)).
  - apply (req_trans (plus a (plus (opp b) b)) (plus a (plus b (opp b))) a).
    + exact (req_plus_compat a a (plus (opp b) b) (plus b (opp b))
                             (req_refl a) (plus_comm (opp b) b)).
    + apply (req_trans (plus a (plus b (opp b))) (plus a zero) a).
      * exact (req_plus_compat a a (plus b (opp b)) zero
                               (req_refl a) (plus_opp b)).
      * apply plus_zero.
Qed.

(* ===== Piece 4: K0 one-step unfolding (source module L99 seven-hop chain, req field at each hop) ===== *)
Lemma req_eg_step_diff : forall x : R,
  req (req_minus (dynamics x) x) (mult eta (entropy_gradient x)).
Proof.
  intros x. unfold req_minus.
  apply (req_trans (plus (dynamics x) (opp x))
                   (plus (plus x (mult eta (entropy_gradient x))) (opp x))
                   (mult eta (entropy_gradient x))).
  - exact (req_plus_compat (dynamics x)
                           (plus x (mult eta (entropy_gradient x)))
                           (opp x) (opp x)
                           (req_dynamics_gradient_step x) (req_refl (opp x))).
  - apply (req_trans (plus (plus x (mult eta (entropy_gradient x))) (opp x))
                     (plus x (plus (mult eta (entropy_gradient x)) (opp x)))
                     (mult eta (entropy_gradient x))).
    + exact (req_sym (plus x (plus (mult eta (entropy_gradient x)) (opp x)))
                     (plus (plus x (mult eta (entropy_gradient x))) (opp x))
                     (plus_assoc x (mult eta (entropy_gradient x)) (opp x))).
    + apply (req_trans (plus x (plus (mult eta (entropy_gradient x)) (opp x)))
                       (plus x (plus (opp x) (mult eta (entropy_gradient x))))
                       (mult eta (entropy_gradient x))).
      * exact (req_plus_compat x x
                               (plus (mult eta (entropy_gradient x)) (opp x))
                               (plus (opp x) (mult eta (entropy_gradient x)))
                               (req_refl x)
                               (plus_comm (mult eta (entropy_gradient x)) (opp x))).
      * apply (req_trans (plus x (plus (opp x) (mult eta (entropy_gradient x))))
                         (plus (plus x (opp x)) (mult eta (entropy_gradient x)))
                         (mult eta (entropy_gradient x))).
        -- exact (plus_assoc x (opp x) (mult eta (entropy_gradient x))).
        -- apply (req_trans (plus (plus x (opp x)) (mult eta (entropy_gradient x)))
                            (plus zero (mult eta (entropy_gradient x)))
                            (mult eta (entropy_gradient x))).
           ++ exact (req_plus_compat (plus x (opp x)) zero
                                     (mult eta (entropy_gradient x))
                                     (mult eta (entropy_gradient x))
                                     (plus_opp x)
                                     (req_refl (mult eta (entropy_gradient x)))).
           ++ apply (req_trans (plus zero (mult eta (entropy_gradient x)))
                               (plus (mult eta (entropy_gradient x)) zero)
                               (mult eta (entropy_gradient x))).
              ** exact (plus_comm zero (mult eta (entropy_gradient x))).
              ** apply plus_zero.
Qed.

(* ===== Piece 5: K0' reverse difference (source module L115 six-hop chain, req field at each hop) ===== *)
Lemma req_eg_step_neg_diff : forall x : R,
  req (req_minus x (dynamics x)) (opp (mult eta (entropy_gradient x))).
Proof.
  intros x. unfold req_minus.
  apply (req_trans (plus x (opp (dynamics x)))
                   (plus x (opp (plus x (mult eta (entropy_gradient x)))))
                   (opp (mult eta (entropy_gradient x)))).
  - exact (req_plus_compat x x (opp (dynamics x))
                              (opp (plus x (mult eta (entropy_gradient x))))
                              (req_refl x)
                              (req_opp_compat (dynamics x)
                                              (plus x (mult eta (entropy_gradient x)))
                                              (req_dynamics_gradient_step x))).
  - apply (req_trans (plus x (opp (plus x (mult eta (entropy_gradient x)))))
                     (plus x (plus (opp x) (opp (mult eta (entropy_gradient x)))))
                     (opp (mult eta (entropy_gradient x)))).
    + exact (req_plus_compat x x (opp (plus x (mult eta (entropy_gradient x))))
                                (plus (opp x) (opp (mult eta (entropy_gradient x))))
                                (req_refl x)
                                (req_opp_plus x (mult eta (entropy_gradient x)))).
    + apply (req_trans (plus x (plus (opp x) (opp (mult eta (entropy_gradient x)))))
                       (plus (plus x (opp x)) (opp (mult eta (entropy_gradient x))))
                       (opp (mult eta (entropy_gradient x)))).
      * exact (plus_assoc x (opp x) (opp (mult eta (entropy_gradient x)))).
      * apply (req_trans (plus (plus x (opp x)) (opp (mult eta (entropy_gradient x))))
                         (plus zero (opp (mult eta (entropy_gradient x))))
                         (opp (mult eta (entropy_gradient x)))).
        -- exact (req_plus_compat (plus x (opp x)) zero
                                  (opp (mult eta (entropy_gradient x)))
                                  (opp (mult eta (entropy_gradient x)))
                                  (plus_opp x)
                                  (req_refl (opp (mult eta (entropy_gradient x))))).
        -- apply (req_trans (plus zero (opp (mult eta (entropy_gradient x))))
                            (plus (opp (mult eta (entropy_gradient x))) zero)
                            (opp (mult eta (entropy_gradient x)))).
           ++ exact (plus_comm zero (opp (mult eta (entropy_gradient x)))).
           ++ apply plus_zero.
Qed.

(* ===== Piece 6: strict subtraction positive (source module L131; direct cite of the req interface lt_id_l field) ===== *)
Lemma req_eg_minus_pos : forall u v : R, lt u v -> lt zero (req_minus v u).
Proof.
  intros u v Huv.
  unfold req_minus.
  apply (lt_id_l zero (plus u (opp u)) (plus v (opp u))                 (req_sym (plus u (opp u)) zero (plus_opp u))).
  apply (lt_plus_compat_lt_le u v (opp u) (opp u) Huv (le_refl (opp u))).
Qed.

(* ===== Piece 7: core A tangent reversal (source module L141 three-segment assembly, req field at each hop) ===== *)
Lemma req_eg_tangent_shift : forall x : R,
  le (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
     (req_minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x.
  pose proof (entropy_tangent (dynamics x) x) as Ht.
  (* Segment A: tangent reshaping le e (e' - W), W := g'*(eta*g) (req interface le_id_r field) *)
  assert (Ht1 : le (entropy x)
                   (plus (entropy (dynamics x))
                         (opp (mult (entropy_gradient (dynamics x))
                                    (mult eta (entropy_gradient x)))))).
  { apply (le_id_r (entropy x)
                   (plus (entropy (dynamics x))
                         (mult (entropy_gradient (dynamics x))
                               (req_minus x (dynamics x))))
                   (plus (entropy (dynamics x))
                         (opp (mult (entropy_gradient (dynamics x))
                                    (mult eta (entropy_gradient x)))))).
    - exact (req_plus_compat
                (entropy (dynamics x)) (entropy (dynamics x))
                (mult (entropy_gradient (dynamics x)) (req_minus x (dynamics x)))
                (opp (mult (entropy_gradient (dynamics x))
                           (mult eta (entropy_gradient x))))
                (req_refl (entropy (dynamics x)))
                (req_trans
                   (mult (entropy_gradient (dynamics x)) (req_minus x (dynamics x)))
                   (mult (entropy_gradient (dynamics x))
                         (opp (mult eta (entropy_gradient x))))
                   (opp (mult (entropy_gradient (dynamics x))
                              (mult eta (entropy_gradient x))))
                   (req_mult_compat (entropy_gradient (dynamics x))
                                    (entropy_gradient (dynamics x))
                                    (req_minus x (dynamics x))
                                    (opp (mult eta (entropy_gradient x)))
                                    (req_refl (entropy_gradient (dynamics x)))
                                    (req_eg_step_neg_diff x))
                   (req_opp_mult_l (entropy_gradient (dynamics x))
                                   (mult eta (entropy_gradient x))))).
    - exact Ht. }
  (* Segment B: move to le (e + W) e' (le_plus_compat + req_eg_minus_plus_cancel finish it) *)
  assert (Ht2 : le (plus (entropy x)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (entropy (dynamics x))).
  { pose proof (le_plus_compat
                   (entropy x)
                   (plus (entropy (dynamics x))
                         (opp (mult (entropy_gradient (dynamics x))
                                    (mult eta (entropy_gradient x)))))
                   (mult (entropy_gradient (dynamics x))
                         (mult eta (entropy_gradient x)))
                   (mult (entropy_gradient (dynamics x))
                         (mult eta (entropy_gradient x)))
                   Ht1
                   (le_refl (mult (entropy_gradient (dynamics x))
                                  (mult eta (entropy_gradient x))))) as Hadd.
    apply (le_id_r (plus (entropy x)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (plus (plus (entropy (dynamics x))
                               (opp (mult (entropy_gradient (dynamics x))
                                          (mult eta (entropy_gradient x)))))
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (entropy (dynamics x))).
    - exact (req_eg_minus_plus_cancel (entropy (dynamics x))
                                      (mult (entropy_gradient (dynamics x))
                                            (mult eta (entropy_gradient x)))).
    - exact Hadd. }
  (* Segment C: add opp e to extract le W (e' - e) (req interface le_id_l field) *)
  assert (Hrot : req (plus (plus (entropy x)
                                 (mult (entropy_gradient (dynamics x))
                                       (mult eta (entropy_gradient x))))
                           (opp (entropy x)))
                     (mult (entropy_gradient (dynamics x))
                           (mult eta (entropy_gradient x)))).
  { apply (req_trans
              (plus (plus (entropy x)
                          (mult (entropy_gradient (dynamics x))
                                (mult eta (entropy_gradient x))))
                    (opp (entropy x)))
              (plus (plus (entropy x) (opp (entropy x)))
                    (mult (entropy_gradient (dynamics x))
                          (mult eta (entropy_gradient x))))
              (mult (entropy_gradient (dynamics x))
                    (mult eta (entropy_gradient x)))).
    - exact (reqd_plus_rot (entropy x)
                           (mult (entropy_gradient (dynamics x))
                                 (mult eta (entropy_gradient x)))
                           (opp (entropy x))).
    - apply (req_trans
                (plus (plus (entropy x) (opp (entropy x)))
                      (mult (entropy_gradient (dynamics x))
                            (mult eta (entropy_gradient x))))
                (plus zero (mult (entropy_gradient (dynamics x))
                                 (mult eta (entropy_gradient x))))
                (mult (entropy_gradient (dynamics x))
                      (mult eta (entropy_gradient x)))).
      + exact (req_plus_compat (plus (entropy x) (opp (entropy x))) zero
                               (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x)))
                               (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x)))
                               (plus_opp (entropy x))
                               (req_refl (mult (entropy_gradient (dynamics x))
                                               (mult eta (entropy_gradient x))))).
      + exact (req_trans (plus zero (mult (entropy_gradient (dynamics x))
                                          (mult eta (entropy_gradient x))))
                         (plus (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x))) zero)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x)))
                         (plus_comm zero (mult (entropy_gradient (dynamics x))
                                               (mult eta (entropy_gradient x))))
                         (plus_zero (mult (entropy_gradient (dynamics x))
                                          (mult eta (entropy_gradient x))))). }
  apply (le_id_l (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
                 (plus (plus (entropy x)
                             (mult (entropy_gradient (dynamics x))
                                   (mult eta (entropy_gradient x))))
                       (opp (entropy x)))
                 (plus (entropy (dynamics x)) (opp (entropy x)))).
  - exact (req_sym
              (plus (plus (entropy x)
                          (mult (entropy_gradient (dynamics x))
                                (mult eta (entropy_gradient x))))
                    (opp (entropy x)))
              (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
              Hrot).
  - exact (le_plus_compat (plus (entropy x)
                                (mult (entropy_gradient (dynamics x))
                                      (mult eta (entropy_gradient x))))
                          (entropy (dynamics x))
                          (opp (entropy x)) (opp (entropy x))
                          Ht2 (le_refl (opp (entropy x)))).
Qed.

(* ===== Piece 8: core B Lipschitz one-sided extraction (source module L228; grade A+: segments (i)-(vi) all req-transport) ===== *)
Lemma req_eg_grad_lower : forall x : R,
  lt zero (entropy_gradient x) ->
  le (mult (req_minus one (mult L eta)) (entropy_gradient x))
     (entropy_gradient (dynamics x)).
Proof.
  intros x Hgx.
  (* (i) |x' - x| == eta*g (true req proof: abs compatibility / product / positivity, three hops) *)
  assert (Habsstep : req (abs (req_minus (dynamics x) x))
                         (mult eta (entropy_gradient x))).
  { apply (req_trans (abs (req_minus (dynamics x) x))
                     (abs (mult eta (entropy_gradient x)))
                     (mult eta (entropy_gradient x))).
    - exact (req_abs_compat (req_minus (dynamics x) x)
                            (mult eta (entropy_gradient x))
                            (req_eg_step_diff x)).
    - apply (req_trans (abs (mult eta (entropy_gradient x)))
                       (mult (abs eta) (abs (entropy_gradient x)))
                       (mult eta (entropy_gradient x))).
      + exact (abs_mult eta (entropy_gradient x)).
      + exact (req_mult_compat (abs eta) eta
                               (abs (entropy_gradient x)) (entropy_gradient x)
                               (abs_pos eta eta_pos)
                               (abs_pos (entropy_gradient x) Hgx)). }
  (* |x - x'| == eta*g (opp reshaping via the abs_opp field) *)
  assert (Habsneg : req (abs (req_minus x (dynamics x)))
                        (mult eta (entropy_gradient x))).
  { apply (req_trans (abs (req_minus x (dynamics x)))
                     (abs (opp (mult eta (entropy_gradient x))))
                     (mult eta (entropy_gradient x))).
    - exact (req_abs_compat (req_minus x (dynamics x))
                            (opp (mult eta (entropy_gradient x)))
                            (req_eg_step_neg_diff x)).
    - apply (req_trans (abs (opp (mult eta (entropy_gradient x))))
                       (abs (mult eta (entropy_gradient x)))
                       (mult eta (entropy_gradient x))).
      + exact (abs_opp (mult eta (entropy_gradient x))).
      + exact (req_trans (abs (mult eta (entropy_gradient x)))
                         (mult (abs eta) (abs (entropy_gradient x)))
                         (mult eta (entropy_gradient x))
                         (abs_mult eta (entropy_gradient x))
                         (req_mult_compat (abs eta) eta
                                          (abs (entropy_gradient x))
                                          (entropy_gradient x)
                                          (abs_pos eta eta_pos)
                                          (abs_pos (entropy_gradient x) Hgx))). }
  (* (ii) Lipschitz at (x, x') (req interface le_id_r field) *)
  assert (Hlip : le (abs (req_minus (entropy_gradient x)
                                    (entropy_gradient (dynamics x))))
                    (mult L (mult eta (entropy_gradient x)))).
  { apply (le_id_r (abs (req_minus (entropy_gradient x)
                                   (entropy_gradient (dynamics x))))
                   (mult L (abs (req_minus x (dynamics x))))
                   (mult L (mult eta (entropy_gradient x)))).
    - exact (req_mult_compat L L (abs (req_minus x (dynamics x)))
                                (mult eta (entropy_gradient x))
                                (req_refl L) Habsneg).
    - exact (gradient_lipschitz x (dynamics x)). }
  (* (iii) one-sided extraction (relies on the abs_ge_value slot) *)
  assert (Hone : le (req_minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                    (mult L (mult eta (entropy_gradient x)))).
  { apply (le_trans (req_minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                    (abs (req_minus (entropy_gradient x)
                                    (entropy_gradient (dynamics x))))
                    (mult L (mult eta (entropy_gradient x)))).
    - exact (abs_ge_value (req_minus (entropy_gradient x)
                                     (entropy_gradient (dynamics x)))).
    - exact Hlip. }
  (* (iv) move to le g ((L*eta)*g + g') (req_eg_minus_plus_cancel + le_plus_compat) *)
  assert (H1 : le (entropy_gradient x)
                  (plus (mult L (mult eta (entropy_gradient x)))
                        (entropy_gradient (dynamics x)))).
  { apply (le_id_l (entropy_gradient x)
                   (plus (req_minus (entropy_gradient x)
                                    (entropy_gradient (dynamics x)))
                         (entropy_gradient (dynamics x)))
                   (plus (mult L (mult eta (entropy_gradient x)))
                         (entropy_gradient (dynamics x)))).
    - exact (req_sym (plus (req_minus (entropy_gradient x)
                                      (entropy_gradient (dynamics x)))
                           (entropy_gradient (dynamics x)))
                     (entropy_gradient x)
                     (req_eg_minus_plus_cancel (entropy_gradient x)
                                               (entropy_gradient (dynamics x)))).
    - exact (le_plus_compat (req_minus (entropy_gradient x)
                                       (entropy_gradient (dynamics x)))
                            (mult L (mult eta (entropy_gradient x)))
                            (entropy_gradient (dynamics x))
                            (entropy_gradient (dynamics x))
                            Hone (le_refl (entropy_gradient (dynamics x)))). }
  (* (v) reshaping le (g + opp((L*eta)*g)) g' (req interface le_id_r field + three hops) *)
  assert (H2 : le (plus (entropy_gradient x)
                        (opp (mult L (mult eta (entropy_gradient x)))))
                  (entropy_gradient (dynamics x))).
  { apply (le_id_r (plus (entropy_gradient x)
                         (opp (mult L (mult eta (entropy_gradient x)))))
                   (plus (plus (mult L (mult eta (entropy_gradient x)))
                               (entropy_gradient (dynamics x)))
                         (opp (mult L (mult eta (entropy_gradient x)))))
                   (entropy_gradient (dynamics x))).
    - apply (req_trans
                (plus (plus (mult L (mult eta (entropy_gradient x)))
                            (entropy_gradient (dynamics x)))
                      (opp (mult L (mult eta (entropy_gradient x)))))
                (plus (plus (entropy_gradient (dynamics x))
                            (mult L (mult eta (entropy_gradient x))))
                      (opp (mult L (mult eta (entropy_gradient x)))))
                (entropy_gradient (dynamics x))).
      + exact (req_plus_compat
                  (plus (mult L (mult eta (entropy_gradient x)))
                        (entropy_gradient (dynamics x)))
                  (plus (entropy_gradient (dynamics x))
                        (mult L (mult eta (entropy_gradient x))))
                  (opp (mult L (mult eta (entropy_gradient x))))
                  (opp (mult L (mult eta (entropy_gradient x))))
                  (plus_comm (mult L (mult eta (entropy_gradient x)))
                             (entropy_gradient (dynamics x)))
                  (req_refl (opp (mult L (mult eta (entropy_gradient x)))))).
      + apply (req_trans
                  (plus (plus (entropy_gradient (dynamics x))
                              (mult L (mult eta (entropy_gradient x))))
                        (opp (mult L (mult eta (entropy_gradient x)))))
                  (plus (entropy_gradient (dynamics x)) zero)
                  (entropy_gradient (dynamics x))).
        * exact (req_trans
                    (plus (plus (entropy_gradient (dynamics x))
                                (mult L (mult eta (entropy_gradient x))))
                          (opp (mult L (mult eta (entropy_gradient x)))))
                    (plus (entropy_gradient (dynamics x))
                          (plus (mult L (mult eta (entropy_gradient x)))
                                (opp (mult L (mult eta (entropy_gradient x))))))
                    (plus (entropy_gradient (dynamics x)) zero)
                    (req_sym
                       (plus (entropy_gradient (dynamics x))
                             (plus (mult L (mult eta (entropy_gradient x)))
                                   (opp (mult L (mult eta (entropy_gradient x))))))
                       (plus (plus (entropy_gradient (dynamics x))
                                   (mult L (mult eta (entropy_gradient x))))
                             (opp (mult L (mult eta (entropy_gradient x)))))
                       (plus_assoc (entropy_gradient (dynamics x))
                                   (mult L (mult eta (entropy_gradient x)))
                                   (opp (mult L (mult eta (entropy_gradient x))))))
                    (req_plus_compat (entropy_gradient (dynamics x))
                                     (entropy_gradient (dynamics x))
                                     (plus (mult L (mult eta (entropy_gradient x)))
                                           (opp (mult L (mult eta (entropy_gradient x)))))
                                     zero
                                     (req_refl (entropy_gradient (dynamics x)))
                                     (plus_opp (mult L (mult eta (entropy_gradient x)))))).
        * apply plus_zero.
    - exact (le_plus_compat (entropy_gradient x)
                            (plus (mult L (mult eta (entropy_gradient x)))
                                  (entropy_gradient (dynamics x)))
                            (opp (mult L (mult eta (entropy_gradient x))))
                            (opp (mult L (mult eta (entropy_gradient x))))
                            H1 (le_refl (opp (mult L (mult eta (entropy_gradient x)))))). }
  (* (vi) final reshaping: (1 - L*eta)*g == g + opp((L*eta)*g) (two req hops) *)
  apply (le_id_l (mult (req_minus one (mult L eta)) (entropy_gradient x))
                 (plus (entropy_gradient x)
                       (opp (mult L (mult eta (entropy_gradient x)))))).
  - exact (req_trans (mult (req_minus one (mult L eta)) (entropy_gradient x))
                     (plus (mult one (entropy_gradient x))
                           (mult (opp (mult L eta)) (entropy_gradient x)))
                     (plus (entropy_gradient x)
                           (opp (mult L (mult eta (entropy_gradient x)))))
                     (req_mult_plus_distr_r one (opp (mult L eta))
                                            (entropy_gradient x))
                     (req_trans
                        (plus (mult one (entropy_gradient x))
                              (mult (opp (mult L eta)) (entropy_gradient x)))
                        (plus (entropy_gradient x)
                              (opp (mult (mult L eta) (entropy_gradient x))))
                        (plus (entropy_gradient x)
                              (opp (mult L (mult eta (entropy_gradient x)))))
                        (req_plus_compat (mult one (entropy_gradient x))
                                         (entropy_gradient x)
                                         (mult (opp (mult L eta)) (entropy_gradient x))
                                         (opp (mult (mult L eta) (entropy_gradient x)))
                                         (req_mult_one_l (entropy_gradient x))
                                         (req_opp_mult_r (mult L eta)
                                                         (entropy_gradient x)))
                        (req_plus_compat (entropy_gradient x) (entropy_gradient x)
                                         (opp (mult (mult L eta) (entropy_gradient x)))
                                         (opp (mult L (mult eta (entropy_gradient x))))
                                         (req_refl (entropy_gradient x))
                                         (req_opp_compat
                                             (mult (mult L eta) (entropy_gradient x))
                                             (mult L (mult eta (entropy_gradient x)))
                                             (req_sym
                                                 (mult L (mult eta (entropy_gradient x)))
                                                 (mult (mult L eta)
                                                       (entropy_gradient x))
                                                 (mult_assoc L eta
                                                             (entropy_gradient x))))))).
  - exact H2.
Qed.

(* ============================================================ *)
(* Piece 9 (main one): req_entropy_step_gain_lower                                *)
(*   Source module L327: eta*(1 - L*eta)*g^2 <= e(x') - e(x).  Assembly:   *)
(*   core B multiplied by g > 0 (interface le_mult_compat field), then by   *)
(*   eta > 0 (batch-1 req_le_mult_compat_r), cascaded with piece 7.         *)
(* ============================================================ *)
Theorem req_entropy_step_gain_lower : forall x : R,
  lt zero (entropy_gradient x) ->
  le (mult (mult eta (req_minus one (mult L eta)))
           (mult (entropy_gradient x) (entropy_gradient x)))
     (req_minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x Hgx.
  pose proof (req_eg_grad_lower x Hgx) as Hlow.
  pose proof (le_mult_compat (mult (req_minus one (mult L eta)) (entropy_gradient x))
                             (entropy_gradient (dynamics x))
                             (entropy_gradient x) Hgx Hlow) as Hm1.
  assert (Hm1' : le (mult (req_minus one (mult L eta))
                          (mult (entropy_gradient x) (entropy_gradient x)))
                    (mult (entropy_gradient (dynamics x)) (entropy_gradient x))).
  { apply (le_id_l (mult (req_minus one (mult L eta))
                         (mult (entropy_gradient x) (entropy_gradient x)))
                   (mult (mult (req_minus one (mult L eta)) (entropy_gradient x))
                         (entropy_gradient x))
                   (mult (entropy_gradient (dynamics x)) (entropy_gradient x))).
    - exact (mult_assoc (req_minus one (mult L eta)) (entropy_gradient x)
                        (entropy_gradient x)).
    - exact Hm1. }
  pose proof (lt_le_iff zero eta (inl eta_pos)) as Hle_eta.
  pose proof (req_le_mult_compat_r eta
                                   (mult (req_minus one (mult L eta))
                                         (mult (entropy_gradient x) (entropy_gradient x)))
                                   (mult (entropy_gradient (dynamics x))
                                         (entropy_gradient x))
                                   Hle_eta Hm1') as Hm2.
  assert (Hm2' : le (mult (mult eta (req_minus one (mult L eta)))
                          (mult (entropy_gradient x) (entropy_gradient x)))
                    (mult (entropy_gradient (dynamics x))
                          (mult eta (entropy_gradient x)))).
  { apply (le_id_l (mult (mult eta (req_minus one (mult L eta)))
                         (mult (entropy_gradient x) (entropy_gradient x)))
                   (mult eta (mult (req_minus one (mult L eta))
                                   (mult (entropy_gradient x) (entropy_gradient x))))
                   (mult (entropy_gradient (dynamics x))
                         (mult eta (entropy_gradient x)))).
    - exact (req_sym (mult eta (mult (req_minus one (mult L eta))
                                     (mult (entropy_gradient x) (entropy_gradient x))))
                     (mult (mult eta (req_minus one (mult L eta)))
                           (mult (entropy_gradient x) (entropy_gradient x)))
                     (mult_assoc eta (req_minus one (mult L eta))
                                 (mult (entropy_gradient x) (entropy_gradient x)))).
    - apply (le_id_r (mult eta (mult (req_minus one (mult L eta))
                                     (mult (entropy_gradient x) (entropy_gradient x))))
                     (mult eta (mult (entropy_gradient (dynamics x))
                                     (entropy_gradient x)))
                     (mult (entropy_gradient (dynamics x))
                           (mult eta (entropy_gradient x)))).
      + exact (req_trans
                  (mult eta (mult (entropy_gradient (dynamics x)) (entropy_gradient x)))
                  (mult (mult eta (entropy_gradient (dynamics x))) (entropy_gradient x))
                  (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
                  (mult_assoc eta (entropy_gradient (dynamics x)) (entropy_gradient x))
                  (req_trans
                     (mult (mult eta (entropy_gradient (dynamics x))) (entropy_gradient x))
                     (mult (mult (entropy_gradient (dynamics x)) eta) (entropy_gradient x))
                     (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
                     (req_mult_compat (mult eta (entropy_gradient (dynamics x)))
                                      (mult (entropy_gradient (dynamics x)) eta)
                                      (entropy_gradient x) (entropy_gradient x)
                                      (mult_comm eta (entropy_gradient (dynamics x)))
                                      (req_refl (entropy_gradient x)))
                     (req_sym (mult (entropy_gradient (dynamics x))
                                    (mult eta (entropy_gradient x)))
                              (mult (mult (entropy_gradient (dynamics x)) eta)
                                    (entropy_gradient x))
                              (mult_assoc (entropy_gradient (dynamics x)) eta
                                          (entropy_gradient x))))).
      + exact Hm2. }
  exact (le_trans (mult (mult eta (req_minus one (mult L eta)))
                        (mult (entropy_gradient x) (entropy_gradient x)))
                  (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
                  (req_minus (entropy (dynamics x)) (entropy x))
                  Hm2' (req_eg_tangent_shift x)).
Qed.

(* ============================================================ *)
(* Piece 10: req_entropy_gain_positive (source module L379; grade B cascaded assembly) *)
(* ============================================================ *)
Theorem req_entropy_gain_positive : forall x : R,
  lt zero (entropy_gradient x) ->
  lt (mult L eta) one ->
  lt zero (req_minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x Hgx HetaL.
  assert (Hc : lt zero (req_minus one (mult L eta)))
    by exact (req_eg_minus_pos (mult L eta) one HetaL).
  assert (Hc1 : lt zero (mult eta (req_minus one (mult L eta))))
    by exact (mult_positive eta (req_minus one (mult L eta)) eta_pos Hc).
  assert (Haa : lt zero (mult (entropy_gradient x) (entropy_gradient x)))
    by exact (mult_positive (entropy_gradient x) (entropy_gradient x) Hgx Hgx).
  assert (HA : lt zero (mult (mult eta (req_minus one (mult L eta)))
                             (mult (entropy_gradient x) (entropy_gradient x))))
    by exact (mult_positive (mult eta (req_minus one (mult L eta)))
                            (mult (entropy_gradient x) (entropy_gradient x))
                            Hc1 Haa).
  pose proof (req_entropy_step_gain_lower x Hgx) as Hlow.
  exact (lt_le_trans zero
                     (mult (mult eta (req_minus one (mult L eta)))
                           (mult (entropy_gradient x) (entropy_gradient x)))
                     (req_minus (entropy (dynamics x)) (entropy x))
                     HA Hlow).
Qed.

(* ============================================================ *)
(* Piece 11 (main two): req_second_law_quant (source module L409)             *)
(*   Root L27796 SecondLaw section: the constructive replacement of the       *)
(*   strict_entropy_increase interface assumption, restated at the same       *)
(*   position on the req side: concrete entropy-gradient dynamics plus        *)
(*   honest sufficient conditions (eta*L < 1, g(x) > 0) yield                 *)
(*   lt (entropy x) (entropy (dynamics x)).                                   *)
(* ============================================================ *)
Theorem req_second_law_quant : forall x : R,
  lt zero (entropy_gradient x) ->
  lt (mult L eta) one ->
  lt (entropy x) (entropy (dynamics x)).
Proof.
  intros x Hgx HetaL.
  pose proof (req_entropy_gain_positive x Hgx HetaL) as Hpos.
  apply (lt_id_r (entropy x)
                 (plus (req_minus (entropy (dynamics x)) (entropy x)) (entropy x))
                 (entropy (dynamics x))).
  - exact (req_eg_minus_plus_cancel (entropy (dynamics x)) (entropy x)).
  - apply (lt_id_l (entropy x) (plus zero (entropy x))
                   (plus (req_minus (entropy (dynamics x)) (entropy x)) (entropy x))).
    + exact (req_trans (entropy x) (plus (entropy x) zero) (plus zero (entropy x))
                       (req_sym (plus (entropy x) zero) (entropy x)
                                (plus_zero (entropy x)))
                       (plus_comm (entropy x) zero)).
    + exact (lt_plus_compat_lt_le zero
                                  (req_minus (entropy (dynamics x)) (entropy x))
                                  (entropy x) (entropy x)
                                  Hpos (le_refl (entropy x))).
Qed.

End EntropyGainReq.
