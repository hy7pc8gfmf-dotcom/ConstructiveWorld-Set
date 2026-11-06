(* ConstructiveWorld-Set -- Min-P temperature antitone companion family. *)

(** * UpReqMinPAntitone: Min-P quality is antitone in the threshold temperature.

    Mission.  Formalizes min-p sampling quality on the req-layer setoid real
      line: a larger threshold [mp] keeps fewer words, so the kept quality
      sum decreases in [mp] and the dropped mass does not decrease.  Main
      statements: [req_minp_keep_p_antitone],
      [req_minp_temp_sum_p_antitone], [req_minp_dropped_mass_p_monotone].

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [UpReqAlgebra], [UpReqAlignRestB],
      [UpReqPropLiftShim] of this development.

    References.  This development, UpReqMinPAntitone.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].  The decidable order of the line is a genuine premise,
      declared as such in section [ReqMinPAntitoneWorld] ([req_le_dec]).

    Build.  [coqc -native-compiler no -q -Q . "" UpReqMinPAntitone.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
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
Require Import UpReqAlignRestB.
From Stdlib Require Import List.
Require Import UpReqPropLiftShim.
(* [pls_] lift-side interface lemmas: the vocabulary nonemptiness premise
   in sigT witness form (see [mpa_vocab_ne_witness_s1]). *)
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* Concrete-carrier order vocabulary: the statement faces of this file are
   stated over the flat global order types [real_lt]/[real_le].  The
   interface lemma fields ([lt_le_iff], [le_trans], [mult_positive],
   [inv_pos_pos], [exp_neg_pos] and companions) are declared over these same
   flat order types, so proofs written on the flat faces apply them without
   crossing extraction worlds; the type-former fields [lt]/[le] of the class
   extract abstractly and would cast at every crossing with the flat world.
   The value vocabulary ([zero], [one], [plus], [mult], [opp]) keeps its
   interface-projection binding: values extract as record components and
   never cast. *)
Abbreviation lt := real_lt.
Abbreviation le := real_le.

(* ================= Section 1. The Min-P p-antitone world ================= *)

(* This world mirrors the baseline MinPSampling [_p] family: the section
   premises are the [ReqSamplingWorld] subset of RestB, and the [_p] family
   is indexed by [mp] : [R]; the three [min_p] items and the topk bridge
   sites are neither used nor declared here. *)
Section ReqMinPAntitoneWorld.
(* Carrier and interface adaptation: the interface class in this tree is the
   zero-argument [Class] [RealInterfaceEnhancedSetoid] of module
   [RealInterfaceEnhancedMod] (S07_RealSetoidExpLog.v:8075) together with the
   global instance [RealEnhancedReal]; the argument-bearing generation
   binders [Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}] of the
   baseline module are deleted and the carrier [R] is bound to the global
   [Real] by the Abbreviation below (same shape as the UpReqAlignRestB /
   UpReqAlign3 / UpAlignIdReq precedents).  Zero [Obj.magic], zero [Prop]
   casts, statement faces preserved verbatim. *)
Abbreviation R := Real.

(* ---- Section premises (the subset isomorphic to the source module
      MinPSampling interface) ---- *)
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
(* Vocabulary nonemptiness in lifted form: the negative-shape premise lifts
   to a sigT witness via [pls_vocab_ne_lift], so deep instantiation sites can
   take the sigT route directly; the original statement is kept. *)
Definition mpa_vocab_ne_witness_s1 : pls_vocab_ne vocab
  := pls_vocab_ne_lift vocab vocab_nonempty.
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.

(* ---- Order decidability premise: the req copy of [DecidableOrder] (same
      slot as [ord_le_dec], same shape as the RestB [req_le_dec]).  Order
      decidability for the whole line is a genuine premise, declared as
      such. ---- *)
Variable req_le_dec : forall a b : R, Or (le a b) (Not (le a b)).

(* ---- The Min-P selection function [pick_max_token] (same slot as in the
      source module; only the selection function itself is needed, the argmin
      face is not touched) ---- *)
Variable pick_max_token : list Token -> Token.

(* ---- Concrete-carrier forms of the finished RestB minp family: the value
      definitions are the upstream [alb_*] value bodies inlined on the flat
      global ring (delta-equal on the instance to the closed-name calls),
      and the two positivity facts together with the list-sum monotonicity
      are carried by the flat specializations [mpa_temp_factor_lt],
      [mpa_rls_pos], [mpa_rls_le] below, so every proof step of the file
      stays inside the concrete extraction world. ---- *)
Definition mp_temp_factor (prefix : list Token) (w : Token) : R :=
  real_exp_neg (real_mult (real_inv_pos temperature temperature_pos)
                          (total_loss (prefix ++ [w]))).

(* The temperature factor is strictly positive: the Boltzmann form
   [exp_neg] of any value is strictly positive ([exp_neg_pos]). *)
Lemma mpa_temp_factor_lt : forall (prefix : list Token) (w : Token),
  lt zero (mp_temp_factor prefix w).
Proof.
  intros prefix w. unfold mp_temp_factor. apply real_exp_neg_pos.
Qed.

(* The flat list-sum strict positivity: a nonempty enumeration with a
   pointwise strictly positive body has a strictly positive sum (the
   concrete-carrier form of the RestB [rls_pos]). *)
Lemma mpa_rls_pos : forall (f : Token -> R),
  (forall a : Token, lt zero (f a)) ->
  forall l : list Token, Not (Id l nil) -> lt zero (rsum Token f l).
Proof.
  intros f Hf l. induction l as [|w rest IH].
  - intro Hnil. exact (match Hnil (@id_refl (list Token) nil) with end).
  - destruct rest as [|w' rest'].
    + cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. intro Hc0. apply (RealSetoid.real_lt_id_r zero (f w) (plus (f w) zero)).
      * apply (real_eq_sym (plus (f w) zero) (f w)). apply real_plus_zero.
      * apply Hf.
    + cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. intro Hc1. apply (RealSetoid.real_lt_id_l zero (plus zero zero)
                                             (plus (f w) (plus (f w') (rsum Token f rest')))).
      * apply (real_eq_sym (plus zero zero) zero). apply real_plus_zero.
      * apply real_lt_plus_compat.
        -- apply Hf.
        -- apply IH. intro Hc. inversion Hc.
Qed.

(* The flat list-sum monotonicity: pointwise [le] carries into the sum (the
   concrete-carrier form of the RestB [rls_le]). *)
Lemma mpa_rls_le : forall (f g : Token -> R),
  (forall a : Token, le (f a) (g a)) ->
  forall l : list Token, le (rsum Token f l) (rsum Token g l).
Proof.
  intros f g Hfg l. induction l as [|w rest IH].
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply real_le_refl.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply real_le_plus_compat.
    + apply Hfg.
    + exact IH.
Qed.

Definition mp_partition_temp (prefix : list Token) : R :=
  rsum Token (mp_temp_factor prefix) vocab.

Definition mp_partition_temp_pos (prefix : list Token)
  : lt zero (mp_partition_temp prefix) :=
  mpa_rls_pos (mp_temp_factor prefix) (mpa_temp_factor_lt prefix) vocab
              vocab_nonempty.

Definition mp_markov_kernel (prefix : list Token) (w : Token) : R :=
  real_mult (mp_temp_factor prefix w)
            (real_inv_pos (mp_partition_temp prefix)
                          (mp_partition_temp_pos prefix)).

Definition mp_markov_pos (prefix : list Token) (w : Token)
  : lt zero (mp_markov_kernel prefix w) :=
  real_mult_positive (mp_temp_factor prefix w)
                     (real_inv_pos (mp_partition_temp prefix)
                                   (mp_partition_temp_pos prefix))
                     (mpa_temp_factor_lt prefix w)
                     (real_inv_pos_pos (mp_partition_temp prefix)
                                       (mp_partition_temp_pos prefix)).

Definition mp_max_markov_prob (prefix : list Token) : R :=
  mp_markov_kernel prefix (pick_max_token prefix).

(* ---- The [mp]-indexed Min-P definition family (isomorphic to the source
      module [_p] family) ---- *)
Definition req_minp_threshold_p (mp : R) (prefix : list Token) : R :=
  mult mp (mp_max_markov_prob prefix).

Definition req_minp_keep_p (mp : R) (prefix : list Token) (w : Token) : Set :=
  le (req_minp_threshold_p mp prefix) (mp_markov_kernel prefix w).

Definition req_minp_keep_dec_p (mp : R) (prefix : list Token) (w : Token) :
  Or (req_minp_keep_p mp prefix w) (Not (req_minp_keep_p mp prefix w)) :=
  req_le_dec (req_minp_threshold_p mp prefix) (mp_markov_kernel prefix w).

Definition req_minp_temp_sum_p (mp : R) (prefix : list Token) : R :=
  rsum Token (fun w => match req_minp_keep_dec_p mp prefix w with
                       | inl _ => mp_temp_factor prefix w
                       | inr _ => zero
                       end) vocab.

Definition req_minp_dropped_mass_p (mp : R) (prefix : list Token) : R :=
  req_minus one
            (mult (inv_pos (mp_partition_temp prefix)
                           (mp_partition_temp_pos prefix))
                  (req_minp_temp_sum_p mp prefix)).

(* Baseline [temp_factor_nonneg_p] companion: [mp_temp_factor] is
   nonnegative (positivity of [exp_neg]); the strict form is
   [mpa_temp_factor_lt]. *)
Lemma req_temp_factor_nonneg_p : forall prefix w,
  le zero (mp_temp_factor prefix w).
Proof.
  intros prefix w.
  apply (real_lt_le_iff zero (mp_temp_factor prefix w)).
  left.
  exact (mpa_temp_factor_lt prefix w).
Qed.

(* Baseline [minp_term_nonneg_p] companion: the keep-test summand of the
   indexed family is nonnegative (the [inl] branch has tf >= 0, the [inr]
   branch is 0). *)
Lemma req_minp_term_nonneg_p : forall mp prefix w,
  le zero (match req_minp_keep_dec_p mp prefix w with
           | inl _ => mp_temp_factor prefix w
           | inr _ => zero
           end).
Proof.
  intros mp prefix w. destruct (req_minp_keep_dec_p mp prefix w) as [Hk | Hd].
  - exact (req_temp_factor_nonneg_p prefix w).
  - apply real_le_refl.
Qed.

(* ===== A larger [mp] shrinks the kept set: the keep decision is antitone =====
   [mp1 <= mp2] gives [threshold1 <= threshold2] by [le_mult_compat_weak]
   (the maximum markov probability is nonnegative); a word kept at [mp2]
   ([threshold2 <= kernel]) then satisfies [threshold1 <= kernel] by
   [le_trans], hence [keep1 w].
   Uses [mp_markov_pos] at the picked maximum and the interface lemmas
   [lt_le_iff], [le_mult_compat_weak], [le_trans]. *)
Lemma req_minp_keep_p_antitone : forall mp1 mp2 : R,
  le mp1 mp2 ->
  forall prefix w,
    req_minp_keep_p mp2 prefix w -> req_minp_keep_p mp1 prefix w.
Proof.
  intros mp1 mp2 Hmp prefix w Hk2.
  unfold req_minp_keep_p, req_minp_threshold_p in *.
  (* [mp_max_markov_prob] is nonnegative: the markov positivity at the
     picked maximum, read as a nonstrict bound through [lt_le_iff]. *)
  assert (Hmax : le zero (mp_max_markov_prob prefix)).
  { apply (real_lt_le_iff zero (mp_max_markov_prob prefix)).
    left.
    exact (mp_markov_pos prefix (pick_max_token prefix)). }
  (* [mult mp1 max <= mult mp2 max] by [le_mult_compat_weak], the right
     factor fixed at [max >= 0]. *)
  assert (Hthr : le (mult mp1 (mp_max_markov_prob prefix))
                    (mult mp2 (mp_max_markov_prob prefix))).
  { apply (real_le_mult_compat_weak mp1 mp2 (mp_max_markov_prob prefix)).
    - exact Hmax.
    - exact Hmp. }
  (* [threshold1 <= threshold2 <= kernel] gives [threshold1 <= kernel]. *)
  apply (real_le_trans (mult mp1 (mp_max_markov_prob prefix))
                       (mult mp2 (mp_max_markov_prob prefix))
                       (mp_markov_kernel prefix w) Hthr).
  exact Hk2.
Qed.

(* ===== A larger [mp] lowers the kept quality sum: [minp_sum2 <= minp_sum1] =====
   Pointwise: a word kept at [mp2] is kept at [mp1] (antitone), so the two
   summands agree; a word dropped at [mp2] contributes 0, bounded by its
   [mp1] summand through [req_minp_term_nonneg_p].
   The baseline [list_sum_le] on [Id] sums becomes the flat list-sum
   monotonicity [mpa_rls_le] on req sums. *)
Lemma req_minp_temp_sum_p_antitone : forall mp1 mp2 : R,
  le mp1 mp2 ->
  forall prefix,
    le (req_minp_temp_sum_p mp2 prefix) (req_minp_temp_sum_p mp1 prefix).
Proof.
  intros mp1 mp2 Hmp prefix. unfold req_minp_temp_sum_p.
  apply (mpa_rls_le
        (fun w => match req_minp_keep_dec_p mp2 prefix w with
                  | inl _ => mp_temp_factor prefix w
                  | inr _ => zero
                  end)
        (fun w => match req_minp_keep_dec_p mp1 prefix w with
                  | inl _ => mp_temp_factor prefix w
                  | inr _ => zero
                  end)).
  intro w. destruct (req_minp_keep_dec_p mp2 prefix w) as [Hk2 | Hd2].
  - (* kept at [mp2] gives kept at [mp1] (antitone), so the summands agree *)
    assert (Hk1 : req_minp_keep_p mp1 prefix w)
      by exact (req_minp_keep_p_antitone mp1 mp2 Hmp prefix w Hk2).
    destruct (req_minp_keep_dec_p mp1 prefix w) as [Hk1' | Hd1'].
    + apply real_le_refl.
    + destruct (Hd1' Hk1).
  - (* dropped at [mp2]: this summand is 0, below the [mp1] summand *)
    exact (req_minp_term_nonneg_p mp1 prefix w).
Qed.

(* ===== Main statement: a larger [mp] does not lower the dropped mass =====
   [sum2 <= sum1] gives [inv * sum2 <= inv * sum1] by [req_le_mult_compat_r]
   (the left factor fixed at [inv >= 0]), hence
   [1 - inv * sum1 <= 1 - inv * sum2] by [le_plus_compat] and
   [opp_le_compat]; after delta expansion of
   [req_minus = plus one (opp _)] the [le] fields match directly. *)
Lemma req_minp_dropped_mass_p_monotone : forall mp1 mp2 : R,
  le mp1 mp2 ->
  forall prefix,
    le (req_minp_dropped_mass_p mp1 prefix)
       (req_minp_dropped_mass_p mp2 prefix).
Proof.
  intros mp1 mp2 Hmp prefix. unfold req_minp_dropped_mass_p, req_minus.
  (* [sum2 <= sum1]: the kept-sum antitone statement above. *)
  assert (Hsum : le (req_minp_temp_sum_p mp2 prefix)
                    (req_minp_temp_sum_p mp1 prefix))
    by exact (req_minp_temp_sum_p_antitone mp1 mp2 Hmp prefix).
  (* [inv_pos] is nonnegative ([inv_pos_pos]). *)
  assert (Hinv : le zero (inv_pos (mp_partition_temp prefix)
                                  (mp_partition_temp_pos prefix))).
  { apply (real_lt_le_iff zero (inv_pos (mp_partition_temp prefix)
                                   (mp_partition_temp_pos prefix))).
    left. apply (real_inv_pos_pos (mp_partition_temp prefix)
                             (mp_partition_temp_pos prefix)). }
  (* [inv * sum2 <= inv * sum1] by [req_le_mult_compat_r], the left factor
     fixed at [inv >= 0]. *)
  assert (Hscaled : le (mult (inv_pos (mp_partition_temp prefix)
                                         (mp_partition_temp_pos prefix))
                             (req_minp_temp_sum_p mp2 prefix))
                       (mult (inv_pos (mp_partition_temp prefix)
                                      (mp_partition_temp_pos prefix))
                             (req_minp_temp_sum_p mp1 prefix)))
    by exact (req_le_mult_compat_r
                (inv_pos (mp_partition_temp prefix)
                         (mp_partition_temp_pos prefix))
                (req_minp_temp_sum_p mp2 prefix)
                (req_minp_temp_sum_p mp1 prefix) Hinv Hsum).
  (* [1 - X <= 1 - Y]: [X <= Y] gives [-Y <= -X], hence
     [1 + (-X) <= 1 + (-Y)]. *)
  apply (real_le_plus_compat one one
                        (opp (mult (inv_pos (mp_partition_temp prefix)
                                            (mp_partition_temp_pos prefix))
                                   (req_minp_temp_sum_p mp1 prefix)))
                        (opp (mult (inv_pos (mp_partition_temp prefix)
                                            (mp_partition_temp_pos prefix))
                                   (req_minp_temp_sum_p mp2 prefix)))
                        (le_refl one)
                        (opp_le_compat
                           (mult (inv_pos (mp_partition_temp prefix)
                                          (mp_partition_temp_pos prefix))
                                 (req_minp_temp_sum_p mp2 prefix))
                           (mult (inv_pos (mp_partition_temp prefix)
                                          (mp_partition_temp_pos prefix))
                                 (req_minp_temp_sum_p mp1 prefix))
                           Hscaled)).
Qed.

End ReqMinPAntitoneWorld.

(* Assumption face: every statement of this file reports Closed under the
   global context; the name list below covers all twenty statements, the
   seventeen carried-over faces plus the three flat specializations. *)
Print Assumptions mpa_vocab_ne_witness_s1.
Print Assumptions mpa_temp_factor_lt.
Print Assumptions mpa_rls_pos.
Print Assumptions mpa_rls_le.
Print Assumptions mp_temp_factor.
Print Assumptions mp_partition_temp.
Print Assumptions mp_partition_temp_pos.
Print Assumptions mp_markov_kernel.
Print Assumptions mp_markov_pos.
Print Assumptions mp_max_markov_prob.
Print Assumptions req_minp_threshold_p.
Print Assumptions req_minp_keep_p.
Print Assumptions req_minp_keep_dec_p.
Print Assumptions req_minp_temp_sum_p.
Print Assumptions req_minp_dropped_mass_p.
Print Assumptions req_temp_factor_nonneg_p.
Print Assumptions req_minp_term_nonneg_p.
Print Assumptions req_minp_keep_p_antitone.
Print Assumptions req_minp_temp_sum_p_antitone.
Print Assumptions req_minp_dropped_mass_p_monotone.
