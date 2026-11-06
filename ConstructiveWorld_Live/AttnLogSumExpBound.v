(* ConstructiveWorld-Set -- attention aggregation bounds over the decidable real interface. *)

(** * AttnLogSumExpBound: log-partition upper bounds for attention aggregation.

    Mission.  The log-partition upper bound family for attention aggregation
      over positive fields with values in [[0,B]]: [attn_log_partition_bound]
      and [attn_log_partition_bound_full] give [log(Z·Agg) <= log Z + log B],
      [attn_tilted_le_log_bound] carries the bound to the tilted partition
      through the identity [T = Σ e^s·f(s) = Z·Agg], and
      [attn_logit_le_log_partition] gives the per-logit bound [s <= log Z];
      [attn_log_partition_bound_B] exits through the boolean order, with
      [Agg = Σ_s (e^s/Z)·f(s)] and [Z = sf_partition ss = Σ e^s].

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [G01_CoreMicro], [G08_Gibbs],
      [S12_B5RecycleSF], [S14_B5BatchBlock] (UpLogMono bridge lemmas) and [UpRealLeB] of this development.

    References.  This development, AttnLogSumExpBound.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" AttnLogSumExpBound.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import List.
Import ListNotations.

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import G01_CoreMicro.
Require Import G08_Gibbs.
Require Import S12_B5RecycleSF.
Require Import S14_B5BatchBlock.
Require Import UpRealLeB.

(* ============================================================ *)
(* 0. The attention aggregation definitions: [attn_aggregate] is the   *)
(*   pointwise function form of the S12 [sf_attention_weights], and    *)
(*   [Wp] carries the partition positivity witness.                    *)
(* ============================================================ *)

(* the attention weight: equal to [sf_softmax ss Wp s], the pointwise  *)
(* form of [sf_attention_weights].                                     *)
Definition attn_weight (ss : list Real)
  (Wp : real_lt real_zero (sf_partition ss)) (s : Real) : Real :=
  real_mult (sf_exp_score s) (real_inv_pos (sf_partition ss) Wp).

(* the attention aggregate: the weighted average Σ_s w(s)·f(s) of a    *)
(* value field f.                                                      *)
Definition attn_aggregate (ss : list Real) (f : Real -> Real)
  (Wp : real_lt real_zero (sf_partition ss)) : Real :=
  real_list_sum Real (fun s => real_mult (attn_weight ss Wp s) (f s)) ss.

(* the tilted partition, the numerator face of the log-partition:      *)
(* [T = Σ_s e^s·f(s)].                                                 *)
Definition attn_tilted (ss : list Real) (f : Real -> Real) : Real :=
  real_list_sum Real (fun s => real_mult (sf_exp_score s) (f s)) ss.

(* ============================================================ *)
(* 1. The part-A bridge: the weight sum equals one, transported from   *)
(*   the map face to the pointwise function face.                      *)
(* ============================================================ *)

Lemma attn_weights_sum_one_pt :
  forall ss : list Real,
    Not (Id ss nil) ->
    forall Wp : real_lt real_zero (sf_partition ss),
      real_eq (real_list_sum Real (attn_weight ss Wp) ss) real_one.
Proof.
  intros ss Hnil Wp.
  apply (real_eq_trans
           (real_list_sum Real (attn_weight ss Wp) ss)
           (real_list_sum Real (fun x => x) (map (attn_weight ss Wp) ss))
           real_one).
  - apply real_eq_sym.
    exact (sf_rsum_map_id Real (attn_weight ss Wp) ss).
  - exact (sf_attention_weights_sum_one ss Hnil Wp).
Qed.

(* ============================================================ *)
(* 2. Support, the list-level bounded-mass bound Σ w·f <= B·Σw, for w  *)
(*   strictly positive and f pointwise <= B: each term is scaled by a  *)
(*   positive factor preserving the order, then linearity extracts the *)
(*   common factor.                                                    *)
(* ============================================================ *)

Lemma attn_wsum_le_scale :
  forall (ss : list Real) (w f : Real -> Real) (B : Real),
    (forall s : Real, real_lt real_zero (w s)) ->
    (forall s : Real, real_le (f s) B) ->
    real_le (real_list_sum Real (fun s => real_mult (w s) (f s)) ss)
            (real_mult B (real_list_sum Real w ss)).
Proof.
  intros ss w f B Hw Hf.
  apply (real_le_trans
           _ (real_list_sum Real (fun s => real_mult (w s) B) ss)).
  - apply (real_list_sum_le Real).
    intro s.
    apply (real_le_trans
             (real_mult (w s) (f s))
             (real_mult (f s) (w s))
             (real_mult (w s) B)).
    + apply real_eq_le_bridge. apply real_mult_comm.
    + apply (real_le_trans
               (real_mult (f s) (w s))
               (real_mult B (w s))
               (real_mult (w s) B)).
      * exact (real_le_mult_compat (f s) B (w s) (Hw s) (Hf s)).
      * apply real_eq_le_bridge. apply real_eq_sym. apply real_mult_comm.
  - apply real_eq_le_bridge.
    apply (real_eq_trans
             (real_list_sum Real (fun s => real_mult (w s) B) ss)
             (real_list_sum Real (fun s => real_mult B (w s)) ss)
             (real_mult B (real_list_sum Real w ss))).
    + apply (real_list_sum_ext Real).
      intro s. apply real_mult_comm.
    + exact (real_list_sum_linear Real B w ss).
Qed.

(* ============================================================ *)
(* 3. Support, transporting the weight normalization (consuming part 1): *)
(*   a value field pointwise <= B gives an aggregate <= B, closed by   *)
(*   the normalization Σw == 1.                                        *)
(* ============================================================ *)

Lemma attn_aggregate_le_bound :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss)) (B : Real),
    Not (Id ss nil) ->
    (forall s : Real, real_le (f s) B) ->
    real_le (attn_aggregate ss f Wp) B.
Proof.
  intros ss f Wp B Hnil Hub. unfold attn_aggregate.
  assert (Hwp : forall s : Real, real_lt real_zero (attn_weight ss Wp s)).
  { intro s. unfold attn_weight.
    exact (real_mult_positive
             (sf_exp_score s) (real_inv_pos (sf_partition ss) Wp)
             (real_exp_neg_pos (real_opp s))
             (real_inv_pos_pos (sf_partition ss) Wp)). }
  apply (real_le_trans
           _ (real_mult B (real_list_sum Real (attn_weight ss Wp) ss))).
  - exact (attn_wsum_le_scale ss (attn_weight ss Wp) f B Hwp Hub).
  - apply real_eq_le_bridge.
    apply (real_eq_trans
             (real_mult B (real_list_sum Real (attn_weight ss Wp) ss))
             (real_mult B real_one)
             B).
    + apply (RealSetoid.real_eq_mult_compat
               B (real_list_sum Real (attn_weight ss Wp) ss) B real_one).
      * apply real_eq_refl.
      * exact (attn_weights_sum_one_pt ss Hnil Wp).
    + exact (real_mult_one B).
Qed.

(* ============================================================ *)
(* 4. Support, the max <= sum bound at the list level with pointwise   *)
(*   InT bounds: the sum of a pointwise nonnegative list is            *)
(*   nonnegative, and any element is <= the full sum.                  *)
(* ============================================================ *)

Lemma attn_sum_nonneg :
  forall (X : Set) (g : X -> Real) (l : list X),
    (forall w : X, InT w l -> real_le real_zero (g w)) ->
    real_le real_zero (real_list_sum X g l).
Proof.
  intros X g l Hnn. induction l as [| a rest IH].
  - cbn [real_list_sum]. apply real_le_refl.
  - cbn [real_list_sum].
    apply (RealSetoid.real_le_id_l real_zero (real_plus real_zero real_zero)).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_le_plus_compat.
      * apply Hnn. apply InT_here.
      * apply IH. intros w Hw. apply Hnn. apply InT_next. exact Hw.
Qed.

Lemma attn_elem_le_sum :
  forall (X : Set) (g : X -> Real) (l : list X),
    (forall w : X, InT w l -> real_le real_zero (g w)) ->
    forall x : X, InT x l -> real_le (g x) (real_list_sum X g l).
Proof.
  intros X g l. induction l as [| a rest IH]; intros Hnn x Hin.
  - inversion Hin.
  - cbn [real_list_sum].
    assert (Hadd : forall z : Real,
              real_le z (real_plus z (real_list_sum X g rest))).
    { intro z. apply (RealSetoid.real_le_id_l z (real_plus z real_zero)).
      - apply real_eq_sym. apply real_plus_zero.
      - apply real_le_plus_compat.
        + apply real_le_refl.
        + apply (attn_sum_nonneg X g rest).
          intros w Hw. apply Hnn. apply InT_next. exact Hw. }
    assert (Hnnr : forall w : X, InT w rest -> real_le real_zero (g w)).
    { intros w Hw. apply Hnn. apply InT_next. exact Hw. }
    inversion Hin as [Heq | y0 l0 Hrec]; subst.
    + apply Hadd.
    + apply (sf_smx_le_add_left (g a) (g x) (real_list_sum X g rest)).
      * apply Hnn. apply InT_here.
      * exact (IH Hnnr x Hrec).
Qed.

(* ============================================================ *)
(* 5. Positivity of the aggregate and of the tilted partition:         *)
(*   pointwise positivity plus element domination plus lt-le           *)
(*   transitivity.                                                     *)
(* ============================================================ *)

Lemma attn_aggregate_pos :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss)),
    Not (Id ss nil) ->
    (forall s : Real, InT s ss -> real_lt real_zero (f s)) ->
    real_lt real_zero (attn_aggregate ss f Wp).
Proof.
  intros ss f Wp Hnil Hb. unfold attn_aggregate.
  destruct ss as [| a rest].
  - destruct (Hnil (id_refl : Id nil nil)).
  - apply (real_lt_le_trans
             real_zero
             (real_mult (attn_weight (a :: rest) Wp a) (f a))
             (real_list_sum Real
                (fun s => real_mult (attn_weight (a :: rest) Wp s) (f s))
                (a :: rest))).
    + apply (real_mult_positive
               (attn_weight (a :: rest) Wp a) (f a)).
      * unfold attn_weight.
        apply (real_mult_positive
                 (sf_exp_score a) (real_inv_pos (sf_partition (a :: rest)) Wp)
                 (real_exp_neg_pos (real_opp a))
                 (real_inv_pos_pos (sf_partition (a :: rest)) Wp)).
      * apply (Hb a). apply InT_here.
    + apply (attn_elem_le_sum Real
               (fun s => real_mult (attn_weight (a :: rest) Wp s) (f s))
               (a :: rest)).
      * intros w Hw. left.
        apply (real_mult_positive
                 (attn_weight (a :: rest) Wp w) (f w)).
        -- unfold attn_weight.
           apply (real_mult_positive
                    (sf_exp_score w) (real_inv_pos (sf_partition (a :: rest)) Wp)
                    (real_exp_neg_pos (real_opp w))
                    (real_inv_pos_pos (sf_partition (a :: rest)) Wp)).
        -- exact (Hb w Hw).
      * apply InT_here.
Qed.

Lemma attn_tilted_pos :
  forall (ss : list Real) (f : Real -> Real),
    Not (Id ss nil) ->
    (forall s : Real, InT s ss -> real_lt real_zero (f s)) ->
    real_lt real_zero (attn_tilted ss f).
Proof.
  intros ss f Hnil Hb. unfold attn_tilted.
  destruct ss as [| a rest].
  - destruct (Hnil (id_refl : Id nil nil)).
  - apply (real_lt_le_trans
             real_zero
             (real_mult (sf_exp_score a) (f a))
             (real_list_sum Real
                (fun s => real_mult (sf_exp_score s) (f s)) (a :: rest))).
    + apply (real_mult_positive (sf_exp_score a) (f a)).
      * apply (real_exp_neg_pos (real_opp a)).
      * apply (Hb a). apply InT_here.
    + apply (attn_elem_le_sum Real
               (fun s => real_mult (sf_exp_score s) (f s)) (a :: rest)).
      * intros w Hw. left.
        apply (real_mult_positive (sf_exp_score w) (f w)).
        -- apply (real_exp_neg_pos (real_opp w)).
        -- exact (Hb w Hw).
      * apply InT_here.
Qed.

(* ============================================================ *)
(* 6. Dependency slot of part B (G08:192 [gibbsd_p_mult_ratio]): the   *)
(*   tilted partition identity T == Z·Agg, assembled termwise by       *)
(*   [real_list_sum_ext]; the main dependency of part B inside the     *)
(*   A-by-B assembly.                                                  *)
(* ============================================================ *)

Lemma attn_tilted_eq :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss)),
    real_eq (attn_tilted ss f)
            (real_mult (sf_partition ss) (attn_aggregate ss f Wp)).
Proof.
  intros ss f Wp. unfold attn_tilted, attn_aggregate.
  apply (real_eq_trans
           (real_list_sum Real (fun s => real_mult (sf_exp_score s) (f s)) ss)
           (real_list_sum Real
              (fun s => real_mult
                          (real_mult (sf_partition ss) (attn_weight ss Wp s)) (f s))
              ss)
           (real_mult (sf_partition ss)
              (real_list_sum Real
                 (fun s => real_mult (attn_weight ss Wp s) (f s)) ss))).
  - apply (real_list_sum_ext Real).
    intro s.
    apply (RealSetoid.real_eq_mult_compat
             (sf_exp_score s) (f s)
             (real_mult (sf_partition ss) (attn_weight ss Wp s)) (f s)).
    + apply real_eq_sym.
      exact (gibbsd_p_mult_ratio (sf_partition ss) (sf_exp_score s) Wp).
    + apply real_eq_refl.
  - apply (real_eq_trans
             (real_list_sum Real
                (fun s => real_mult
                            (real_mult (sf_partition ss) (attn_weight ss Wp s)) (f s))
                ss)
             (real_list_sum Real
                (fun s => real_mult (sf_partition ss)
                            (real_mult (attn_weight ss Wp s) (f s)))
                ss)
             (real_mult (sf_partition ss)
                (real_list_sum Real
                   (fun s => real_mult (attn_weight ss Wp s) (f s)) ss))).
    + apply (real_list_sum_ext Real).
      intro s. apply real_eq_sym.
      exact (real_mult_assoc (sf_partition ss) (attn_weight ss Wp s) (f s)).
    + exact (real_list_sum_linear Real (sf_partition ss)
               (fun s => real_mult (attn_weight ss Wp s) (f s)) ss).
Qed.

(* ============================================================ *)
(* 7. The main bound: a log-partition type upper bound for attention   *)
(*   aggregation, stated in plain [real_le] and running only in the    *)
(*   monotone direction of log.  From Z·Agg <= Z·B, the aggregate      *)
(*   bound plus order preservation under positive scaling, to          *)
(*   log(Z·Agg) <= log Z + log B by [real_log_le_mono] and             *)
(*   [real_log_mult].                                                  *)
(* ============================================================ *)

Theorem attn_log_partition_bound :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss))
         (B : Real) (HB : real_lt real_zero B)
         (HposAgg : real_lt real_zero (attn_aggregate ss f Wp))
         (HAggB : real_le (attn_aggregate ss f Wp) B),
    real_le (real_log (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
                       (real_mult_positive (sf_partition ss)
                          (attn_aggregate ss f Wp) Wp HposAgg))
            (real_plus (real_log (sf_partition ss) Wp) (real_log B HB)).
Proof.
  intros ss f Wp B HB HposAgg HAggB.
  assert (Hscale : real_le (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
                           (real_mult (sf_partition ss) B)).
  { apply (real_le_trans
             (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
             (real_mult (attn_aggregate ss f Wp) (sf_partition ss))
             (real_mult (sf_partition ss) B)).
    - apply real_eq_le_bridge. apply real_mult_comm.
    - apply (real_le_trans
               (real_mult (attn_aggregate ss f Wp) (sf_partition ss))
               (real_mult B (sf_partition ss))
               (real_mult (sf_partition ss) B)).
      + exact (real_le_mult_compat
                 (attn_aggregate ss f Wp) B (sf_partition ss) Wp HAggB).
      + apply real_eq_le_bridge. apply real_eq_sym. apply real_mult_comm. }
  apply (real_le_trans
           (real_log (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
                     (real_mult_positive (sf_partition ss)
                        (attn_aggregate ss f Wp) Wp HposAgg))
           (real_log (real_mult (sf_partition ss) B)
                     (real_mult_positive (sf_partition ss) B Wp HB))
           (real_plus (real_log (sf_partition ss) Wp) (real_log B HB))).
  - apply (real_log_le_mono
             (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
             (real_mult (sf_partition ss) B)
             (real_mult_positive (sf_partition ss)
                (attn_aggregate ss f Wp) Wp HposAgg)
             (real_mult_positive (sf_partition ss) B Wp HB)).
    exact Hscale.
  - apply real_eq_le_bridge.
    exact (real_log_mult (sf_partition ss) B Wp HB).
Qed.

(* ============================================================ *)
(* 8. The honest full interface of the main bound: the positivity and  *)
(*   aggregate bound witnesses are discharged by the supports of this  *)
(*   file.                                                             *)
(* ============================================================ *)

Theorem attn_log_partition_bound_full :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss))
         (B : Real) (HB : real_lt real_zero B),
    forall (Hnil : Not (Id ss nil)),
    forall (Hb : forall s : Real, InT s ss -> real_lt real_zero (f s)),
    forall (Hub : forall s : Real, real_le (f s) B),
    real_le (real_log (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
                       (real_mult_positive (sf_partition ss)
                          (attn_aggregate ss f Wp) Wp
                          (attn_aggregate_pos ss f Wp Hnil Hb)))
            (real_plus (real_log (sf_partition ss) Wp) (real_log B HB)).
Proof.
  intros ss f Wp B HB Hnil Hb Hub.
  exact (attn_log_partition_bound ss f Wp B HB
           (attn_aggregate_pos ss f Wp Hnil Hb)
           (attn_aggregate_le_bound ss f Wp B Hnil Hub)).
Qed.

(* ============================================================ *)
(* 9. The tilted partition face: log(Σ e^s·f(s)) <= log Z + log B,     *)
(*   transported by the part-B identity [attn_tilted_eq] into the main *)
(*   bound.                                                            *)
(* ============================================================ *)

Theorem attn_tilted_le_log_bound :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss))
         (B : Real) (HB : real_lt real_zero B)
         (HposT : real_lt real_zero (attn_tilted ss f))
         (HposAgg : real_lt real_zero (attn_aggregate ss f Wp))
         (HAggB : real_le (attn_aggregate ss f Wp) B),
    real_le (real_log (attn_tilted ss f) HposT)
            (real_plus (real_log (sf_partition ss) Wp) (real_log B HB)).
Proof.
  intros ss f Wp B HB HposT HposAgg HAggB.
  apply (real_le_trans
           (real_log (attn_tilted ss f) HposT)
           (real_log (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
                     (real_mult_positive (sf_partition ss)
                        (attn_aggregate ss f Wp) Wp HposAgg))
           (real_plus (real_log (sf_partition ss) Wp) (real_log B HB))).
  - apply real_eq_le_bridge.
    exact (real_log_wd (attn_tilted ss f)
             (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
             HposT
             (real_mult_positive (sf_partition ss)
                (attn_aggregate ss f Wp) Wp HposAgg)
             (attn_tilted_eq ss f Wp)).
  - exact (attn_log_partition_bound ss f Wp B HB HposAgg HAggB).
Qed.

(* ============================================================ *)
(* 10. Dependency slot of part A (S12:12017 [sf_softmax_le_one]) and    *)
(*   the second dependency slot of part B: each logit is dominated by  *)
(*   the partition, s <= log Z, the lower face of the log-partition    *)
(*   domination.                                                       *)
(* ============================================================ *)

Theorem attn_logit_le_log_partition :
  forall (ss : list Real) (Wp : real_lt real_zero (sf_partition ss))
         (s : Real),
    InT s ss ->
    real_le s (real_log (sf_partition ss) Wp).
Proof.
  intros ss Wp s Hin.
  assert (Hw1 : real_le (attn_weight ss Wp s) real_one).
  { unfold attn_weight. exact (sf_softmax_le_one ss s Wp Hin). }
  assert (H1 : real_eq (real_mult (sf_partition ss) (attn_weight ss Wp s))
                       (sf_exp_score s)).
  { exact (gibbsd_p_mult_ratio (sf_partition ss) (sf_exp_score s) Wp). }
  assert (H2 : real_le (real_mult (sf_partition ss) (attn_weight ss Wp s))
                       (real_mult (sf_partition ss) real_one)).
  { apply (real_le_trans
             (real_mult (sf_partition ss) (attn_weight ss Wp s))
             (real_mult (attn_weight ss Wp s) (sf_partition ss))
             (real_mult (sf_partition ss) real_one)).
    - apply real_eq_le_bridge. apply real_mult_comm.
    - apply (real_le_trans
               (real_mult (attn_weight ss Wp s) (sf_partition ss))
               (real_mult real_one (sf_partition ss))
               (real_mult (sf_partition ss) real_one)).
      + exact (real_le_mult_compat
                 (attn_weight ss Wp s) real_one (sf_partition ss) Wp Hw1).
      + apply real_eq_le_bridge. apply real_eq_sym. apply real_mult_comm. }
  assert (HewZ : real_le (sf_exp_score s) (sf_partition ss)).
  { apply (real_le_trans
             (sf_exp_score s)
             (real_mult (sf_partition ss) (attn_weight ss Wp s))
             (sf_partition ss)).
    - apply real_eq_le_bridge. apply real_eq_sym. exact H1.
    - apply (real_le_trans
               (real_mult (sf_partition ss) (attn_weight ss Wp s))
               (real_mult (sf_partition ss) real_one)
               (sf_partition ss)).
      + exact H2.
      + apply real_eq_le_bridge. exact (real_mult_one (sf_partition ss)). }
  apply (real_le_trans
           s
           (real_log (sf_exp_score s) (real_exp_neg_pos (real_opp s)))
           (real_log (sf_partition ss) Wp)).
  - apply real_eq_le_bridge.
    apply (real_eq_trans
             s
             (real_opp (real_opp s))
             (real_log (sf_exp_score s) (real_exp_neg_pos (real_opp s)))).
    + apply real_eq_sym. exact (real_opp_opp s).
    + apply real_eq_sym. exact (real_log_exp_neg (real_opp s)).
  - exact (real_log_le_mono
             (sf_exp_score s)
             (sf_partition ss)
             (real_exp_neg_pos (real_opp s))
             Wp
             HewZ).
Qed.

(* ============================================================ *)
(* 11. The boolean-shaped exit through the one-way bridge              *)
(*   [real_le_to_le_b] of UpRealLeB.                                   *)
(* ============================================================ *)

Corollary attn_log_partition_bound_B :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss))
         (B : Real) (HB : real_lt real_zero B)
         (HposAgg : real_lt real_zero (attn_aggregate ss f Wp))
         (HAggB : real_le (attn_aggregate ss f Wp) B),
    real_le_b (real_log (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
                        (real_mult_positive (sf_partition ss)
                           (attn_aggregate ss f Wp) Wp HposAgg))
              (real_plus (real_log (sf_partition ss) Wp) (real_log B HB)).
Proof.
  intros ss f Wp B HB HposAgg HAggB.
  exact (real_le_to_le_b _ _
    (attn_log_partition_bound ss f Wp B HB HposAgg HAggB)).
Qed.

(* ============================================================ *)
(* 12. Assumption audit: the [Print Assumptions] block at the end of   *)
(*   the file covers the main exits.                                   *)
(* ============================================================ *)

Print Assumptions attn_log_partition_bound.
Print Assumptions attn_log_partition_bound_full.
Print Assumptions attn_tilted_le_log_bound.
Print Assumptions attn_logit_le_log_partition.
Print Assumptions attn_log_partition_bound_B.
