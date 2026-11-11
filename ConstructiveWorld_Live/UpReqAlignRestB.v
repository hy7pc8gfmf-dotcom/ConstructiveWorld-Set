(* ConstructiveWorld-Set — req-layer rest of the alignment sampling family: list-sum machinery, Min-P/Top-k Markov kernels, entropy definitions, and KV-quant eviction bounds. *)

(** * UpReqAlignRestB: setoid rest of the alignment sampling family.

    Mission.  List-summation machinery over the setoid interface ([rsum], [rls_ext],
      [rls_linear], [rls_nonneg], [rls_single_le], [rls_pos], [rls_le],
      [rls_kernel_norm_gen]) and its consumers: the Min-P/Top-k sampling worlds with
      combined keep ([req_minp_markov_kernel_normalized],
      [req_topp_markov_kernel_normalized],
      [req_combined_topk_markov_kernel_normalized]), the entropy definition group
      ([req_E_B_ent], [req_Omega_total_ent], [req_entropy_ent],
      [req_Omega_total_pos]), and the KV-quant eviction world ([req_epos],
      [req_boltzmann_diff_bound], [req_db_breaking_bound_eps]).
    Dependencies.  Stdlib [Datatypes], [List] with [ListNotations].  Requires
      [S01_BaseRing] through [S15_TailFEPUp], [UpReqAlgebra], [UpReqPropLiftShim] of
      this development; imports [RealInterfaceEnhancedMod].
    References.  The baseline module CW_ConstructiveWorld_219 (sections
      MinPSampling, TopPSampling, EntropyDiffReal, RealKVQuantMain) of
      ConstructiveWorld-Main, whose statement names carry over here verbatim
      (statement-face Set-carrier completion; [minus] to [req_minus], [Id]-equality
      to [req]).  Fields absent from the setoid interface are explicit premises:
      [req_le_dec], [req_lt_dec], [pick_max_in_vocab], [req_boltzmann_diff_bridge],
      [transition_nonneg].
    Constructivity.  All statements are carried by [Set] (the interface carriers
      [req], [lt], [le], [req_minus] with [Not]/[And]/[Or] and [Id] on
      nat/bool/list); proofs are closed term-mode derivations, the decidability
      lemmas end in [Defined], and no statement is left unproved.
    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      ConstructiveWorld_Live/UpReqAlignRestB.v] compiles cleanly (exit 0); the
      first eight bytes of the artifact are [436f7121 000160bc]. *)

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
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.
Require Import UpReqPropLiftShim.
(* [pls_] adapter lemmas lift the negation-form premises to [sigT] witness form. *)
(* Pool-build cure (seat_abl19, M43 nw10cure per UpReqAlign3.v precedent): the
   interface class in this tree is unparameterized (S07_RealSetoidExpLog.v:8075
   zero-argument Class RealInterfaceEnhancedSetoid + global Instance
   RealEnhancedReal); the argument-bearing generation binders
   the argument-bearing generation binders Context {R : Set}
   {RIS : RealInterfaceEnhancedSetoid R}. are deleted and the carrier R is bound
   to the global Real by the file-top Notation below. Zero Obj.magic, zero Prop
   casts, statement faces preserved verbatim. *)
Notation R := Real.

(* ============================================================ *)
(* Section 1. req list-summation machinery (req form of the       *)
(*   baseline MinPSampling list_sum cluster L30710-30768/         *)
(*   L31104; generalized once the [rls_*] section closes, and     *)
(*   shared by the Min-P and Top-k worlds).                       *)
(* ============================================================ *)
Section ReqListSumTool.
Variable A : Set.

Fixpoint rsum (f : A -> R) (l : list A) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (f w) (rsum f rest)
  end.

(* baseline [list_sum_ext] L30734: pointwise [req] gives [req] of the sums. *)
Lemma rls_ext : forall f g : A -> R,
  (forall a : A, req (f a) (g a)) -> forall l : list A, req (rsum f l) (rsum g l).
Proof.
  intros f g Hfg l. induction l as [|w rest IH].
  - apply req_refl.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply req_plus_compat.
    + apply Hfg.
    + exact IH.
Qed.

(* baseline [list_sum_linear] L30710: summing [a * f] yields [a * sum f] ([req_trans] plus the reversed [distrib] step). *)
Lemma rls_linear : forall (a : R) (f : A -> R) (l : list A),
  req (rsum (fun x => mult a (f x)) l) (mult a (rsum f l)).
Proof.
  intros a f l. induction l as [|w rest IH].
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply req_sym. apply mult_zero.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
    apply (req_trans (plus (mult a (f w)) (rsum (fun x => mult a (f x)) rest))
                     (plus (mult a (f w)) (mult a (rsum f rest)))
                     (mult a (plus (f w) (rsum f rest)))).
    + apply (req_plus_compat (mult a (f w)) (mult a (f w))
                             (rsum (fun x => mult a (f x)) rest)
                             (mult a (rsum f rest))).
      * apply req_refl.
      * exact IH.
    + apply (req_sym (mult a (plus (f w) (rsum f rest)))
                     (plus (mult a (f w)) (mult a (rsum f rest)))).
      apply distrib.
Qed.

(* baseline [list_sum_nonneg] L30742: pointwise nonnegativity gives nonnegativity of the sum. *)
Lemma rls_nonneg : forall f : A -> R,
  (forall a : A, le zero (f a)) -> forall l : list A, le zero (rsum f l).
Proof.
  intros f Hf l. induction l as [|w rest IH].
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply le_refl.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
    apply (le_id_l zero (plus zero zero) (plus (f w) (rsum f rest))).
    + apply (req_sym (plus zero zero) zero). apply plus_zero.
    + apply (le_plus_compat zero (f w) zero (rsum f rest)).
      * apply Hf.
      * exact IH.
Qed.

(* baseline [list_sum_single_le_total] L30753: a single term is bounded by the total sum (induction on the [InT] derivation). *)
Lemma rls_single_le : forall (f : A -> R) (x : A) (l : list A),
  InT x l -> (forall y : A, le zero (f y)) -> le (f x) (rsum f l).
Proof.
  intros f x l Hin Hnn.
  induction Hin as [l0 | y l0 Hin IH].
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. exact (req_le_plus_nonneg_r (f x) (rsum f l0) (rls_nonneg f Hnn l0)).
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply (le_trans (f x) (rsum f l0) (plus (f y) (rsum f l0))).
    + exact IH.
    + exact (le_id_r (rsum f l0) (plus (rsum f l0) (f y))
                     (plus (f y) (rsum f l0)) (plus_comm (rsum f l0) (f y))
                     (req_le_plus_nonneg_r (rsum f l0) (f y) (Hnn y))).
Qed.

(* baseline [sum_temp_positive] L30769: a nonempty list with pointwise positivity has a positive sum. *)
Lemma rls_pos : forall f : A -> R,
  (forall a : A, lt zero (f a)) ->
  forall l : list A, Not (Id l nil) -> lt zero (rsum f l).
Proof.
  intros f Hf l. induction l as [|w rest IH].
  - intro Hnil. exact (match Hnil (@id_refl (list A) nil) with end).
  - destruct rest as [|w' rest'].
    + cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. intro Hc0. apply (lt_id_r zero (f w) (plus (f w) zero)).
      * apply (req_sym (plus (f w) zero) (f w)). apply plus_zero.
      * apply Hf.
    + cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. intro Hc1. apply (lt_id_l zero (plus zero zero)
                                             (plus (f w) (plus (f w') (rsum f rest')))).
      * apply (req_sym (plus zero zero) zero). apply plus_zero.
      * apply lt_plus_compat.
        -- apply Hf.
        -- apply IH. intro Hc. inversion Hc.
Qed.

(* baseline [list_sum_le] L31104: pointwise order gives the order of the sums. *)
Lemma rls_le : forall f g : A -> R,
  (forall a : A, le (f a) (g a)) -> forall l : list A, le (rsum f l) (rsum g l).
Proof.
  intros f g Hfg l. induction l as [|w rest IH].
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply le_refl.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply le_plus_compat.
    + apply Hfg.
    + exact IH.
Qed.

(* generic req normalization kernel: the req proof of the algebraic
   skeleton shared by the four baseline normalization theorems (the
   baseline repeats the same Id-style proof for minp/topp/combined/
   combined_topk, and each [temp_sum] definition here is the delta
   expansion of this kernel's S term). *)
Lemma rls_kernel_norm_gen :
  forall (l : list A)
         (P : A -> Set) (kd : forall w : A, Or (P w) (Not (P w)))
         (g : A -> R)
         (HS : lt zero (rsum (fun w => match kd w with
                                       | inl _ => g w
                                       | inr _ => zero
                                       end) l)),
  req (rsum (fun w => match kd w with
                      | inl _ => mult (g w)
                                      (inv_pos (rsum (fun w => match kd w with
                                                               | inl _ => g w
                                                               | inr _ => zero
                                                               end) l)
                                               HS)
                      | inr _ => zero
                      end) l)
      one.
Proof.
  intros l P kd g HS.
  apply (req_trans
    (rsum (fun w => match kd w with
                    | inl _ => mult (g w)
                                    (inv_pos (rsum (fun w => match kd w with
                                                             | inl _ => g w
                                                             | inr _ => zero
                                                             end) l)
                                             HS)
                    | inr _ => zero
                    end) l)
    (mult (inv_pos (rsum (fun w => match kd w with
                                   | inl _ => g w
                                   | inr _ => zero
                                   end) l)
                   HS)
          (rsum (fun w => match kd w with
                          | inl _ => g w
                          | inr _ => zero
                          end) l))
    one).
  - apply (req_trans
      (rsum (fun w => match kd w with
                      | inl _ => mult (g w)
                                      (inv_pos (rsum (fun w => match kd w with
                                                               | inl _ => g w
                                                               | inr _ => zero
                                                               end) l)
                                             HS)
                      | inr _ => zero
                      end) l)
      (rsum (fun w => mult (inv_pos (rsum (fun w => match kd w with
                                                    | inl _ => g w
                                                    | inr _ => zero
                                                    end) l)
                                   HS)
                           (match kd w with
                            | inl _ => g w
                            | inr _ => zero
                            end)) l)
      (mult (inv_pos (rsum (fun w => match kd w with
                                     | inl _ => g w
                                     | inr _ => zero
                                     end) l)
                     HS)
            (rsum (fun w => match kd w with
                            | inl _ => g w
                            | inr _ => zero
                            end) l))).
    + apply (rls_ext (fun w => match kd w with
                               | inl _ => mult (g w)
                                               (inv_pos (rsum (fun w => match kd w with
                                                                        | inl _ => g w
                                                                        | inr _ => zero
                                                                        end) l)
                                                        HS)
                               | inr _ => zero
                               end)
                     (fun w => mult (inv_pos (rsum (fun w => match kd w with
                                                             | inl _ => g w
                                                             | inr _ => zero
                                                             end) l)
                                            HS)
                                    (match kd w with
                                     | inl _ => g w
                                     | inr _ => zero
                                     end))).
      intro w. destruct (kd w) as [Hp | Hnp].
      * apply mult_comm.
      * apply req_sym. apply mult_zero.
    + apply rls_linear.
  - apply (req_trans
      (mult (inv_pos (rsum (fun w => match kd w with
                                     | inl _ => g w
                                     | inr _ => zero
                                     end) l)
                     HS)
            (rsum (fun w => match kd w with
                            | inl _ => g w
                            | inr _ => zero
                            end) l))
      (mult (rsum (fun w => match kd w with
                            | inl _ => g w
                            | inr _ => zero
                            end) l)
            (inv_pos (rsum (fun w => match kd w with
                                     | inl _ => g w
                                     | inr _ => zero
                                     end) l)
                     HS))
      one).
    + apply mult_comm.
    + apply inv_pos_correct.
Qed.

End ReqListSumTool.


(* ============================================================ *)
(* Section 2. generic small lemmas (req form of baseline           *)
(*   [lt_zero_le_trans] L31065 / [le_mult_le_one_r] L30881; fully  *)
(*   generalized and shared by the sampling and eviction worlds).  *)
(* ============================================================ *)
Section ReqOrdTools.

(* baseline [lt_zero_le_trans] L31065: [0 < a] and [a <= b] give
   [0 < b].  req-layer differences: [minus] becomes [req_minus], and
   the Id-rewrite chain becomes [req_trans] + [req_minus_plus_cancel]. *)
Lemma req_lt_zero_le_trans : forall a b : R,
  lt zero a -> le a b -> lt zero b.
Proof.
  intros a b Ha Hab.
  assert (Hnonneg : le zero (req_minus b a)).
  { apply req_le_minus_nonneg. exact Hab. }
  assert (Hpos : lt zero (plus (req_minus b a) a)).
  { apply req_plus_le_lt_pos.
    - exact Hnonneg.
    - exact Ha. }
  apply (lt_id_r zero (plus (req_minus b a) a) b).
  - apply (req_trans (plus (req_minus b a) a)
                     (plus a (req_minus b a)) b).
    + apply plus_comm.
    + apply req_minus_plus_cancel.
  - exact Hpos.
Qed.

(* baseline [le_mult_le_one_r] L30881: [0 <= a] and [b <= 1] give
   [b * a <= a].  req-layer differences: [minus] becomes [req_minus]
   and the Id-rewrite finish becomes [le_id_l] +
   [req_minus_plus_cancel]; each of the five identity segments of H3
   is proved by an explicit [req_trans]. *)
Lemma req_le_mult_le_one_r : forall a b : R,
  le zero a -> le b one -> le (mult b a) a.
Proof.
  intros a b Ha Hb.
  assert (H1 : le zero (req_minus one b)).
  { apply req_le_minus_nonneg. exact Hb. }
  assert (H2 : le zero (mult (req_minus one b) a)).
  { apply (le_id_l zero (mult a zero) (mult (req_minus one b) a)).
    - apply (req_sym (mult a zero) zero). apply mult_zero.
    - apply (le_id_r (mult a zero) (mult a (req_minus one b))
                     (mult (req_minus one b) a)).
      + apply mult_comm.
      + exact (req_le_mult_compat_r a zero (req_minus one b) Ha H1). }
  assert (H3 : req (mult (req_minus one b) a) (req_minus a (mult b a))).
  { apply (req_trans (mult (req_minus one b) a)
                     (mult a (req_minus one b))
                     (req_minus a (mult b a))).
    - apply mult_comm.
    - apply (req_trans (mult a (req_minus one b))
                       (req_minus (mult a one) (mult a b))
                       (req_minus a (mult b a))).
      + apply req_mult_minus_distr_l.
      + unfold req_minus. apply req_plus_compat.
        * apply mult_one.
        * apply req_opp_compat. apply mult_comm. }
  assert (H2' : le zero (req_minus a (mult b a))).
  { exact (le_id_r zero (mult (req_minus one b) a)
                   (req_minus a (mult b a)) H3 H2). }
  assert (H4 : le (plus (mult b a) zero)
                  (plus (mult b a) (req_minus a (mult b a)))).
  { apply (le_plus_compat (mult b a) (mult b a) zero (req_minus a (mult b a))).
    - apply le_refl.
    - exact H2'. }
  exact (le_id_r (mult b a) (plus (mult b a) (req_minus a (mult b a))) a
                 (req_minus_plus_cancel (mult b a) a)
                 (le_id_l (mult b a) (plus (mult b a) zero)
                          (plus (mult b a) (req_minus a (mult b a)))
                          (req_sym (plus (mult b a) zero) (mult b a)
                                   (plus_zero (mult b a)))
                          H4)).
Qed.

End ReqOrdTools.

(* ============================================================ *)
(* Section 3. sampling world (Min-P region L30684-31866 and the    *)
(*   Top-k region L31872-32542).  The baseline TopP section uses   *)
(*   the MinP machinery in explicitly parameterized closure form   *)
(*   (the same 12-argument explicit calls as L31914); the req      *)
(*   layer merges both regions into one isomorphic section with    *)
(*   every definition and statement still in bijection with the    *)
(*   baseline.  [top_p_keep] (the sort_kernel membership form,     *)
(*   L31962) is not carried over: its sorting/membership machinery *)
(*   lives in the list-[Id] domain, and every baseline theorem     *)
(*   uses the [le]-form [topp_keep] (L31990).                      *)
(* ============================================================ *)
Section ReqSamplingWorld.

(* ---- interface assumptions (isomorphic to MinPSampling L30693-30701) ---- *)
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
(* the negation-form premise is lifted to [sigT] witness form by the
   [pls_] adapter lemma: [pls_vocab_ne_lift] raises it in place, so
   downstream consumers can take the [sigT] route directly; the old
   statement is kept. *)
Definition alb_vocab_ne_witness_s1 : pls_vocab_ne vocab
  := pls_vocab_ne_lift vocab vocab_nonempty.
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.

(* ---- Min-P parameters (same positions as L30870-30872) ---- *)
Variable min_p : R.
Variable min_p_pos : lt zero min_p.
Variable min_p_lt_one : lt min_p one.

(* ---- interface premise 1: the req dual of the baseline
     DecidableOrder [ord_le_dec] (same position as L331/332); the
     setoid class has no decidable-order field, so the premise
     sits at the pointwise-matching position ---- *)
Hypothesis req_le_dec : forall a b : R, Or (le a b) (Not (le a b)).

(* ---- interface premise 2: the three-way decider (req dual of
     [lt_dec_field_tk] L32385); the middle branch tests equality
     with [req] instead of [Id], since equality on R in the req
     world is [req] ---- *)
Hypothesis req_lt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)).

(* ---- interface premise 3: the list machinery is postulated
     (the 13 argmin lemmas are not carried over); only the
     top-level fact that [pick_max_token prefix] lies in [vocab]
     is assumed ---- *)
Variable pick_max_token : list Token -> Token.
Hypothesis pick_max_in_vocab : forall prefix : list Token,
  InT (pick_max_token prefix) vocab.

(* ---- basic infrastructure (isomorphic to L30703-30715; [list_sum] becomes [rsum]) ---- *)
Definition alb_temp_factor (prefix : list Token) (w : Token) : R :=
  exp_neg (mult (inv_pos temperature temperature_pos)
                (total_loss (prefix ++ [w]))).

Definition alb_partition_temp (prefix : list Token) : R :=
  rsum Token (alb_temp_factor prefix) vocab.

(* baseline [req_partition_temp_pos] L30768. *)
Lemma req_partition_temp_pos : forall prefix : list Token,
  lt zero (alb_partition_temp prefix).
Proof.
  intro prefix. unfold alb_partition_temp.
  apply (rls_pos Token (alb_temp_factor prefix)).
  - intro w. unfold alb_temp_factor. apply exp_neg_pos.
  - apply vocab_nonempty.
Qed.

Definition alb_markov_kernel (prefix : list Token) (w : Token) : R :=
  mult (alb_temp_factor prefix w)
       (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix)).

(* baseline [markov_pos] L30861. *)
Lemma req_markov_pos : forall (prefix : list Token) (w : Token),
  lt zero (alb_markov_kernel prefix w).
Proof.
  intros prefix w. unfold alb_markov_kernel. apply mult_positive.
  - unfold alb_temp_factor. apply exp_neg_pos.
  - apply (inv_pos_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix)).
Qed.

(* baseline [markov_kernel_unfold] L31156 (definitional). *)
Lemma req_markov_kernel_unfold : forall (prefix : list Token) (w : Token),
  req (alb_markov_kernel prefix w)
      (mult (alb_temp_factor prefix w)
            (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))).
Proof.
  intros prefix w. apply req_refl.
Qed.

(* ---- Min-P threshold and its decider (isomorphic to L30919-30945) ---- *)
Definition alb_max_markov_prob (prefix : list Token) : R :=
  alb_markov_kernel prefix (pick_max_token prefix).

Definition alb_minp_threshold (prefix : list Token) : R :=
  mult min_p (alb_max_markov_prob prefix).

Definition alb_minp_keep (prefix : list Token) (w : Token) : Set :=
  le (alb_minp_threshold prefix) (alb_markov_kernel prefix w).

Definition alb_minp_keep_dec (prefix : list Token) (w : Token) :
  Or (alb_minp_keep prefix w) (Not (alb_minp_keep prefix w)) :=
  req_le_dec (alb_minp_threshold prefix) (alb_markov_kernel prefix w).

Definition alb_minp_temp_sum (prefix : list Token) : R :=
  rsum Token (fun w => match alb_minp_keep_dec prefix w with
                       | inl _ => alb_temp_factor prefix w
                       | inr _ => zero
                       end) vocab.

(* baseline [pick_max_token_minp_keep] L30954 (uses [req_le_mult_le_one_r]). *)
Lemma req_pick_max_minp_keep : forall prefix : list Token,
  alb_minp_keep prefix (pick_max_token prefix).
Proof.
  intro prefix. unfold alb_minp_keep.
  apply (req_le_mult_le_one_r (alb_markov_kernel prefix (pick_max_token prefix))
                              min_p).
  - apply (lt_le_iff zero (alb_markov_kernel prefix (pick_max_token prefix))).
    left. apply req_markov_pos.
  - apply (lt_le_iff min_p one). left. exact min_p_lt_one.
Qed.

(* the temperature factor of [pick_max] is bounded by
   [alb_minp_temp_sum] (core arm of [temp_factor_max_le_sum] L31328;
   shared by [req_minp_temp_sum_pos] and
   [req_minp_scaled_sum_ge_max]). *)
Lemma req_pick_max_tf_le_minp_sum : forall prefix : list Token,
  le (alb_temp_factor prefix (pick_max_token prefix)) (alb_minp_temp_sum prefix).
Proof.
  intro prefix. unfold alb_minp_temp_sum.
  assert (Heq : req (alb_temp_factor prefix (pick_max_token prefix))
                    (match alb_minp_keep_dec prefix (pick_max_token prefix) with
                     | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                     | inr _ => zero
                     end)).
  { destruct (alb_minp_keep_dec prefix (pick_max_token prefix)) as [Hk | Hd].
    - apply req_refl.
    - destruct (Hd (req_pick_max_minp_keep prefix)). }
  apply (le_id_l (alb_temp_factor prefix (pick_max_token prefix))
                 (match alb_minp_keep_dec prefix (pick_max_token prefix) with
                  | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                  | inr _ => zero
                  end)
                 (rsum Token
                        (fun w => match alb_minp_keep_dec prefix w with
                                  | inl _ => alb_temp_factor prefix w
                                  | inr _ => zero
                                  end) vocab)).
  - exact Heq.
  - apply (rls_single_le Token
           (fun w => match alb_minp_keep_dec prefix w with
                     | inl _ => alb_temp_factor prefix w
                     | inr _ => zero
                     end)
           (pick_max_token prefix) vocab).
    + apply pick_max_in_vocab.
    + intro w. destruct (alb_minp_keep_dec prefix w) as [Hk2 | Hd2].
      * apply (lt_le_iff zero (alb_temp_factor prefix w)). left.
        unfold alb_temp_factor. apply exp_neg_pos.
      * apply le_refl.
Qed.

(* baseline [req_minp_temp_sum_pos] L30981. *)
Lemma req_minp_temp_sum_pos : forall prefix : list Token,
  lt zero (alb_minp_temp_sum prefix).
Proof.
  intro prefix.
  apply (req_lt_zero_le_trans (alb_temp_factor prefix (pick_max_token prefix))
                              (alb_minp_temp_sum prefix)).
  - unfold alb_temp_factor. apply exp_neg_pos.
  - exact (req_pick_max_tf_le_minp_sum prefix).
Qed.

(* ---- the truncated Min-P kernel (isomorphic to L31009-31049) ---- *)
Definition alb_minp_markov_kernel (prefix : list Token) (w : Token) : R :=
  match alb_minp_keep_dec prefix w with
  | inl _ =>
      mult (alb_temp_factor prefix w)
           (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))
  | inr _ => zero
  end.

(* baseline [minp_markov_kernel_nonneg] L31022 (disjunctive form, matching the baseline point by point). *)
Lemma req_minp_markov_kernel_nonneg : forall (prefix : list Token) (w : Token),
  Or (req (alb_minp_markov_kernel prefix w) zero)
     (lt zero (alb_minp_markov_kernel prefix w)).
Proof.
  intros prefix w. unfold alb_minp_markov_kernel.
  destruct (alb_minp_keep_dec prefix w) as [Hkeep | Hdrop].
  - right. apply mult_positive.
    + unfold alb_temp_factor. apply exp_neg_pos.
    + apply (inv_pos_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix)).
  - left. apply req_refl.
Qed.

(* baseline [minp_markov_kernel_keep_pos] L31036 (conditional positivity). *)
Lemma req_minp_markov_kernel_keep_pos : forall (prefix : list Token) (w : Token),
  alb_minp_keep prefix w -> lt zero (alb_minp_markov_kernel prefix w).
Proof.
  intros prefix w Hkeep. unfold alb_minp_markov_kernel.
  destruct (alb_minp_keep_dec prefix w) as [Hk | Hdrop].
  - apply mult_positive.
    + unfold alb_temp_factor. apply exp_neg_pos.
    + apply (inv_pos_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix)).
  - destruct (Hdrop Hkeep).
Qed.

(* baseline [minp_markov_kernel_unfold_keep] L31166. *)
Lemma req_minp_markov_kernel_unfold_keep : forall (prefix : list Token) (w : Token),
  alb_minp_keep prefix w ->
  req (alb_minp_markov_kernel prefix w)
      (mult (alb_temp_factor prefix w)
            (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))).
Proof.
  intros prefix w Hkeep. unfold alb_minp_markov_kernel.
  destruct (alb_minp_keep_dec prefix w) as [Hk | Hdrop].
  - apply req_refl.
  - destruct (Hdrop Hkeep).
Qed.

(* ===== baseline [minp_markov_kernel_normalized] L31050 (the req-form
   main theorem) ===== the Id-layer proof chains the rewrites Hext /
   Hlin / Hdef; here the algebraic skeleton is proved once by
   [rls_kernel_norm_gen] and this statement instantiates it, with
   the definitions of [alb_minp_markov_kernel] and
   [alb_minp_temp_sum] delta-expanding to the kernel's S term. *)
Theorem req_minp_markov_kernel_normalized : forall prefix : list Token,
  req (rsum Token (fun w => alb_minp_markov_kernel prefix w) vocab) one.
Proof.
  intro prefix.
  exact (rls_kernel_norm_gen Token vocab
           (fun w : Token => le (alb_minp_threshold prefix) (alb_markov_kernel prefix w))
           (fun w : Token => alb_minp_keep_dec prefix w) (alb_temp_factor prefix)
           (req_minp_temp_sum_pos prefix)).
Qed.

(* baseline [minp_temp_sum_le_partition] L31112 (finished by [rls_le]). *)
Lemma req_minp_temp_sum_le_partition : forall prefix : list Token,
  le (alb_minp_temp_sum prefix) (alb_partition_temp prefix).
Proof.
  intro prefix. unfold alb_minp_temp_sum, alb_partition_temp.
  apply (rls_le Token
           (fun w => match alb_minp_keep_dec prefix w with
                     | inl _ => alb_temp_factor prefix w
                     | inr _ => zero
                     end)
           (alb_temp_factor prefix)).
  intro w. destruct (alb_minp_keep_dec prefix w) as [Hk | Hd].
  - apply le_refl.
  - apply (lt_le_iff zero (alb_temp_factor prefix w)). left.
    unfold alb_temp_factor. apply exp_neg_pos.
Qed.

(* ===== baseline [minp_markov_kernel_keep_ge_full] L31127: for a kept token the truncated kernel dominates the full kernel ===== *)
Lemma req_minp_markov_kernel_keep_ge_full : forall (prefix : list Token) (w : Token),
  alb_minp_keep prefix w ->
  le (alb_markov_kernel prefix w) (alb_minp_markov_kernel prefix w).
Proof.
  intros prefix w Hkeep. unfold alb_minp_markov_kernel, alb_markov_kernel.
  destruct (alb_minp_keep_dec prefix w) as [Hk | Hd].
  - apply (req_le_mult_compat_r (alb_temp_factor prefix w)
                                (inv_pos (alb_partition_temp prefix)
                                         (req_partition_temp_pos prefix))
                                (inv_pos (alb_minp_temp_sum prefix)
                                         (req_minp_temp_sum_pos prefix))).
    + apply (lt_le_iff zero (alb_temp_factor prefix w)). left.
      unfold alb_temp_factor. apply exp_neg_pos.
    + apply (inv_pos_le_compat (alb_minp_temp_sum prefix) (alb_partition_temp prefix)
                               (req_minp_temp_sum_pos prefix)
                               (req_partition_temp_pos prefix)).
      exact (req_minp_temp_sum_le_partition prefix).
  - destruct (Hd Hkeep).
Qed.

(* ===== baseline [minp_markov_kernel_dropped_zero] L31147 (req form) ===== *)
Lemma req_minp_markov_kernel_dropped_zero : forall (prefix : list Token) (w : Token),
  Not (alb_minp_keep prefix w) -> req (alb_minp_markov_kernel prefix w) zero.
Proof.
  intros prefix w Hdrop. unfold alb_minp_markov_kernel.
  destruct (alb_minp_keep_dec prefix w) as [Hk | Hd].
  - destruct (Hdrop Hk).
  - apply req_refl.
Qed.

(* ===== baseline [minp_kernel_ratio] L31182: explicit form of the
   scaling factor ===== the Id layer chains five [id_cong] steps;
   the req layer proves the inner identity Hinner and supplies
   [req_mult_compat] with explicit arguments (each of the five
   inverse segments is proved on its own). *)
Lemma req_minp_kernel_ratio : forall (prefix : list Token) (w : Token),
  alb_minp_keep prefix w ->
  req (alb_minp_markov_kernel prefix w)
      (mult (alb_markov_kernel prefix w)
            (mult (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))
                  (alb_partition_temp prefix))).
Proof.
  intros prefix w Hkeep.
  assert (Hinner : req (mult (inv_pos (alb_partition_temp prefix)
                                       (req_partition_temp_pos prefix))
                             (mult (inv_pos (alb_minp_temp_sum prefix)
                                            (req_minp_temp_sum_pos prefix))
                                   (alb_partition_temp prefix)))
                       (inv_pos (alb_minp_temp_sum prefix)
                                (req_minp_temp_sum_pos prefix))).
  { apply (req_trans
      (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
            (mult (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))
                  (alb_partition_temp prefix)))
      (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
            (mult (alb_partition_temp prefix)
                  (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))))
      (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))).
    - apply req_mult_compat.
      + apply req_refl.
      + apply mult_comm.
    - apply (req_trans
        (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
              (mult (alb_partition_temp prefix)
                    (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))))
        (mult (mult (inv_pos (alb_partition_temp prefix)
                                 (req_partition_temp_pos prefix))
                    (alb_partition_temp prefix))
              (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix)))
        (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))).
      + apply mult_assoc.
      + apply (req_trans
          (mult (mult (inv_pos (alb_partition_temp prefix)
                                   (req_partition_temp_pos prefix))
                      (alb_partition_temp prefix))
                (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix)))
          (mult (mult (alb_partition_temp prefix)
                      (inv_pos (alb_partition_temp prefix)
                               (req_partition_temp_pos prefix)))
                (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix)))
          (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))).
        * apply req_mult_compat.
          -- apply mult_comm.
          -- apply req_refl.
        * apply (req_trans
            (mult (mult (alb_partition_temp prefix)
                        (inv_pos (alb_partition_temp prefix)
                                 (req_partition_temp_pos prefix)))
                  (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix)))
            (mult one (inv_pos (alb_minp_temp_sum prefix)
                               (req_minp_temp_sum_pos prefix)))
            (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))).
          -- apply req_mult_compat.
             ++ apply inv_pos_correct.
             ++ apply req_refl.
          -- apply (req_trans
               (mult one (inv_pos (alb_minp_temp_sum prefix)
                                  (req_minp_temp_sum_pos prefix)))
               (mult (inv_pos (alb_minp_temp_sum prefix)
                              (req_minp_temp_sum_pos prefix)) one)
               (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))
               (mult_comm one
                          (inv_pos (alb_minp_temp_sum prefix)
                                   (req_minp_temp_sum_pos prefix)))
               (mult_one (inv_pos (alb_minp_temp_sum prefix)
                                  (req_minp_temp_sum_pos prefix)))). }
  exact (req_trans
           (alb_minp_markov_kernel prefix w)
           (mult (alb_temp_factor prefix w)
                 (inv_pos (alb_minp_temp_sum prefix)
                          (req_minp_temp_sum_pos prefix)))
           (mult (alb_markov_kernel prefix w)
                 (mult (inv_pos (alb_minp_temp_sum prefix)
                                (req_minp_temp_sum_pos prefix))
                       (alb_partition_temp prefix)))
           (req_minp_markov_kernel_unfold_keep prefix w Hkeep)
           (req_trans
              (mult (alb_temp_factor prefix w)
                    (inv_pos (alb_minp_temp_sum prefix)
                             (req_minp_temp_sum_pos prefix)))
              (mult (alb_temp_factor prefix w)
                    (mult (inv_pos (alb_partition_temp prefix)
                                   (req_partition_temp_pos prefix))
                          (mult (inv_pos (alb_minp_temp_sum prefix)
                                         (req_minp_temp_sum_pos prefix))
                                (alb_partition_temp prefix))))
              (mult (alb_markov_kernel prefix w)
                    (mult (inv_pos (alb_minp_temp_sum prefix)
                                   (req_minp_temp_sum_pos prefix))
                          (alb_partition_temp prefix)))
              (req_mult_compat
                 (alb_temp_factor prefix w) (alb_temp_factor prefix w)
                 (inv_pos (alb_minp_temp_sum prefix)
                          (req_minp_temp_sum_pos prefix))
                 (mult (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix))
                       (mult (inv_pos (alb_minp_temp_sum prefix)
                                      (req_minp_temp_sum_pos prefix))
                             (alb_partition_temp prefix)))
                 (req_refl (alb_temp_factor prefix w))
                 (req_sym
                    (mult (inv_pos (alb_partition_temp prefix)
                                   (req_partition_temp_pos prefix))
                          (mult (inv_pos (alb_minp_temp_sum prefix)
                                         (req_minp_temp_sum_pos prefix))
                                (alb_partition_temp prefix)))
                    (inv_pos (alb_minp_temp_sum prefix)
                             (req_minp_temp_sum_pos prefix))
                    Hinner))
              (mult_assoc (alb_temp_factor prefix w)
                          (inv_pos (alb_partition_temp prefix)
                                   (req_partition_temp_pos prefix))
                          (mult (inv_pos (alb_minp_temp_sum prefix)
                                         (req_minp_temp_sum_pos prefix))
                                (alb_partition_temp prefix))))).
Qed.

(* ---- the truncated mass (L31257-31451; signature change: [minus] becomes [req_minus]) ---- *)
Definition alb_minp_dropped_mass (prefix : list Token) : R :=
  req_minus one
            (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
                  (alb_minp_temp_sum prefix)).

(* baseline [minp_dropped_mass_nonneg] L31261 ([le_minus_nonneg] becomes [req_le_minus_nonneg]). *)
Lemma req_minp_dropped_mass_nonneg : forall prefix : list Token,
  le zero (alb_minp_dropped_mass prefix).
Proof.
  intro prefix. unfold alb_minp_dropped_mass.
  apply req_le_minus_nonneg.
  apply (le_id_r
    (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
          (alb_minp_temp_sum prefix))
    (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
          (alb_partition_temp prefix))
    one).
  - apply (req_trans
      (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
            (alb_partition_temp prefix))
      (mult (alb_partition_temp prefix)
            (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix)))
      one).
    + apply mult_comm.
    + apply inv_pos_correct.
  - apply (req_le_mult_compat_r
             (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
             (alb_minp_temp_sum prefix) (alb_partition_temp prefix)).
    + apply (lt_le_iff zero
                       (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix))).
      left. apply (inv_pos_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix)).
    + exact (req_minp_temp_sum_le_partition prefix).
Qed.

(* baseline [temp_factor_max_eq] L31298: the temperature factor of
   [pick_max] equals [max_prob * partition] (delta-expanding the
   definition of [alb_markov_kernel], [max_prob] equals [tf * inv_p];
   in the req layer that delta step is the conversion [req_refl]
   while the associativity step is proved). *)
Lemma req_temp_factor_max_eq : forall prefix : list Token,
  req (alb_temp_factor prefix (pick_max_token prefix))
      (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix)).
Proof.
  intro prefix.
  apply (req_trans
    (alb_temp_factor prefix (pick_max_token prefix))
    (mult (alb_temp_factor prefix (pick_max_token prefix))
          (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
                (alb_partition_temp prefix)))
    (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix))).
  - apply (req_trans
      (alb_temp_factor prefix (pick_max_token prefix))
      (mult (alb_temp_factor prefix (pick_max_token prefix)) one)
      (mult (alb_temp_factor prefix (pick_max_token prefix))
            (mult (inv_pos (alb_partition_temp prefix)
                           (req_partition_temp_pos prefix))
                  (alb_partition_temp prefix)))).
    + apply (req_sym (mult (alb_temp_factor prefix (pick_max_token prefix)) one)
                     (alb_temp_factor prefix (pick_max_token prefix))).
      apply mult_one.
    + apply req_mult_compat.
      * apply req_refl.
      * apply (req_trans
          one
          (mult (alb_partition_temp prefix)
                (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix)))
          (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
                (alb_partition_temp prefix))).
        -- apply (req_sym
                    (mult (alb_partition_temp prefix)
                          (inv_pos (alb_partition_temp prefix)
                                   (req_partition_temp_pos prefix)))
                    one).
           apply inv_pos_correct.
        -- apply mult_comm.
  - apply (req_trans
      (mult (alb_temp_factor prefix (pick_max_token prefix))
            (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
                  (alb_partition_temp prefix)))
      (mult (mult (alb_temp_factor prefix (pick_max_token prefix))
                  (inv_pos (alb_partition_temp prefix)
                           (req_partition_temp_pos prefix)))
            (alb_partition_temp prefix))
      (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix))).
    + apply (req_sym
        (mult (mult (alb_temp_factor prefix (pick_max_token prefix))
                    (inv_pos (alb_partition_temp prefix)
                             (req_partition_temp_pos prefix)))
              (alb_partition_temp prefix))
              (mult (alb_temp_factor prefix (pick_max_token prefix))
              (mult (inv_pos (alb_partition_temp prefix)
                             (req_partition_temp_pos prefix))
                    (alb_partition_temp prefix)))).
      (* the outer [req_sym] has already flipped the pairing, so the
         associativity step is the symmetric orientation of
         [mult_assoc]; an explicit [req_sym] restores the standard
         orientation. *)
      apply (req_sym
        (mult (alb_temp_factor prefix (pick_max_token prefix))
              (mult (inv_pos (alb_partition_temp prefix)
                             (req_partition_temp_pos prefix))
                    (alb_partition_temp prefix)))
        (mult (mult (alb_temp_factor prefix (pick_max_token prefix))
                    (inv_pos (alb_partition_temp prefix)
                             (req_partition_temp_pos prefix)))
              (alb_partition_temp prefix))).
      apply mult_assoc.
    + apply req_refl.
Qed.

(* baseline [minp_scaled_sum_ge_max] L31313: [max_prob <= inv_p * minp_sum]. *)
Lemma req_minp_scaled_sum_ge_max : forall prefix : list Token,
  le (alb_max_markov_prob prefix)
     (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
           (alb_minp_temp_sum prefix)).
Proof.
  intro prefix.
  assert (Hid : req (mult (inv_pos (alb_partition_temp prefix)
                                   (req_partition_temp_pos prefix))
                          (mult (alb_max_markov_prob prefix)
                                (alb_partition_temp prefix)))
                    (alb_max_markov_prob prefix)).
  { apply (req_trans
      (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
            (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix)))
      (mult (mult (inv_pos (alb_partition_temp prefix)
                           (req_partition_temp_pos prefix))
                  (alb_max_markov_prob prefix))
            (alb_partition_temp prefix))
      (alb_max_markov_prob prefix)).
    - apply mult_assoc.
    - apply (req_trans
        (mult (mult (inv_pos (alb_partition_temp prefix)
                             (req_partition_temp_pos prefix))
                    (alb_max_markov_prob prefix))
              (alb_partition_temp prefix))
        (mult (mult (alb_max_markov_prob prefix)
                    (inv_pos (alb_partition_temp prefix)
                             (req_partition_temp_pos prefix)))
              (alb_partition_temp prefix))
        (alb_max_markov_prob prefix)).
      + apply req_mult_compat.
        * apply mult_comm.
        * apply req_refl.
      + apply (req_trans
          (mult (mult (alb_max_markov_prob prefix)
                      (inv_pos (alb_partition_temp prefix)
                               (req_partition_temp_pos prefix)))
                (alb_partition_temp prefix))
          (mult (alb_max_markov_prob prefix)
                (mult (inv_pos (alb_partition_temp prefix)
                               (req_partition_temp_pos prefix))
                      (alb_partition_temp prefix)))
          (alb_max_markov_prob prefix)).
        * apply (req_sym
            (mult (alb_max_markov_prob prefix)
                  (mult (inv_pos (alb_partition_temp prefix)
                                 (req_partition_temp_pos prefix))
                        (alb_partition_temp prefix)))
            (mult (mult (alb_max_markov_prob prefix)
                        (inv_pos (alb_partition_temp prefix)
                                 (req_partition_temp_pos prefix)))
                  (alb_partition_temp prefix))).
          apply mult_assoc.
        * apply (req_trans
            (mult (alb_max_markov_prob prefix)
                  (mult (inv_pos (alb_partition_temp prefix)
                                 (req_partition_temp_pos prefix))
                        (alb_partition_temp prefix)))
            (mult (alb_max_markov_prob prefix) one)
            (alb_max_markov_prob prefix)).
          -- apply req_mult_compat.
             ++ apply req_refl.
             ++ apply (req_trans
                 (mult (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix))
                       (alb_partition_temp prefix))
                 (mult (alb_partition_temp prefix)
                       (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix)))
                 one).
                ** apply mult_comm.
                ** apply inv_pos_correct.
          -- apply mult_one. }
  assert (H1 : le (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix))
                  (alb_minp_temp_sum prefix)).
  { exact (le_id_l (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix))
                   (alb_temp_factor prefix (pick_max_token prefix))
                   (alb_minp_temp_sum prefix)
                   (req_sym (alb_temp_factor prefix (pick_max_token prefix))
                            (mult (alb_max_markov_prob prefix)
                                  (alb_partition_temp prefix))
                            (req_temp_factor_max_eq prefix))
                   (req_pick_max_tf_le_minp_sum prefix)). }
  apply (le_id_l (alb_max_markov_prob prefix)
                 (mult (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix))
                       (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix)))
                 (mult (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix))
                       (alb_minp_temp_sum prefix))).
  - apply (req_sym (mult (inv_pos (alb_partition_temp prefix)
                                  (req_partition_temp_pos prefix))
                         (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix)))
                   (alb_max_markov_prob prefix)).
    exact Hid.
  - apply (req_le_mult_compat_r
             (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
             (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix))
             (alb_minp_temp_sum prefix)).
    + apply (lt_le_iff zero
                       (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix))).
      left. apply (inv_pos_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix)).
    + exact H1.
Qed.

(* baseline [minp_dropped_mass_le_one_minus_max] L31451 ([opp] reversal plus the monotone shift). *)
Lemma req_minp_dropped_mass_le_one_minus_max : forall prefix : list Token,
  le (alb_minp_dropped_mass prefix) (req_minus one (alb_max_markov_prob prefix)).
Proof.
  intro prefix. unfold alb_minp_dropped_mass.
  apply (le_plus_compat one one
           (opp (mult (inv_pos (alb_partition_temp prefix)
                               (req_partition_temp_pos prefix))
                      (alb_minp_temp_sum prefix)))
           (opp (alb_max_markov_prob prefix))).
  - apply le_refl.
  - apply opp_le_compat.
    exact (req_minp_scaled_sum_ge_max prefix).
Qed.

(* ============================================================ *)
(* Section 3 (cont.). Top-k region (counterpart of the baseline    *)
(*   TopPSampling L31872-32542).                                   *)
(* ============================================================ *)

(* baseline [topp_keep] L31990 ([le] form). *)
Definition alb_topp_keep (p : R) (prefix : list Token) (w : Token) : Set :=
  le p (alb_markov_kernel prefix w).

Definition alb_topp_keep_dec (p : R) (prefix : list Token) (w : Token) :
  Or (alb_topp_keep p prefix w) (Not (alb_topp_keep p prefix w)) :=
  req_le_dec p (alb_markov_kernel prefix w).

Definition alb_topp_temp_sum (p : R) (prefix : list Token) : R :=
  rsum Token (fun w => match alb_topp_keep_dec p prefix w with
                       | inl _ => alb_temp_factor prefix w
                       | inr _ => zero
                       end) vocab.

(* baseline [topp_temp_sum_pos] L32014: keep-ness of [pick_max]
   comes from the premise [le p max] ([alb_topp_keep p prefix
   (pick_max_token prefix)] is conversion-equal to
   [le p (alb_max_markov_prob prefix)]). *)
Lemma req_topp_temp_sum_pos : forall (p : R) (prefix : list Token),
  le p (alb_max_markov_prob prefix) -> lt zero (alb_topp_temp_sum p prefix).
Proof.
  intros p prefix Hp.
  assert (Hle : le (alb_temp_factor prefix (pick_max_token prefix))
                   (alb_topp_temp_sum p prefix)).
  { unfold alb_topp_temp_sum.
    assert (Heq : req (alb_temp_factor prefix (pick_max_token prefix))
                      (match alb_topp_keep_dec p prefix (pick_max_token prefix) with
                       | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                       | inr _ => zero
                       end)).
    { destruct (alb_topp_keep_dec p prefix (pick_max_token prefix)) as [Hk | Hd].
      - apply req_refl.
      - destruct (Hd Hp). }
    apply (le_id_l (alb_temp_factor prefix (pick_max_token prefix))
                   (match alb_topp_keep_dec p prefix (pick_max_token prefix) with
                    | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                    | inr _ => zero
                    end)
                   (rsum Token
                          (fun w => match alb_topp_keep_dec p prefix w with
                                    | inl _ => alb_temp_factor prefix w
                                    | inr _ => zero
                                    end) vocab)).
    - exact Heq.
    - apply (rls_single_le Token
               (fun w => match alb_topp_keep_dec p prefix w with
                         | inl _ => alb_temp_factor prefix w
                         | inr _ => zero
                         end)
               (pick_max_token prefix) vocab).
      + apply pick_max_in_vocab.
      + intro w. destruct (alb_topp_keep_dec p prefix w) as [Hk2 | Hd2].
        * apply (lt_le_iff zero (alb_temp_factor prefix w)). left.
          unfold alb_temp_factor. apply exp_neg_pos.
        * apply le_refl. }
  apply (req_lt_zero_le_trans (alb_temp_factor prefix (pick_max_token prefix))
                              (alb_topp_temp_sum p prefix)).
  - unfold alb_temp_factor. apply exp_neg_pos.
  - exact Hle.
Qed.

(* baseline [topp_markov_kernel] L32085 (the [Hpmax] premise position matches the baseline). *)
Definition alb_topp_markov_kernel (p : R)
  (Hpmax : forall prefix : list Token, le p (alb_max_markov_prob prefix))
  (prefix : list Token) (w : Token) : R :=
  match alb_topp_keep_dec p prefix w with
  | inl _ =>
      mult (alb_temp_factor prefix w)
           (inv_pos (alb_topp_temp_sum p prefix)
                    (req_topp_temp_sum_pos p prefix (Hpmax prefix)))
  | inr _ => zero
  end.

(* ===== baseline [topp_markov_kernel_normalized] L32084 (the req-form main theorem) ===== *)
Theorem req_topp_markov_kernel_normalized : forall (p : R)
  (Hpmax : forall prefix : list Token, le p (alb_max_markov_prob prefix))
  (prefix : list Token),
  req (rsum Token (fun w => alb_topp_markov_kernel p Hpmax prefix w) vocab) one.
Proof.
  intros p Hpmax prefix.
  exact (rls_kernel_norm_gen Token vocab (alb_topp_keep p prefix)
           (fun w => alb_topp_keep_dec p prefix w) (alb_temp_factor prefix)
           (req_topp_temp_sum_pos p prefix (Hpmax prefix))).
Qed.

(* ---- combined keep (Min-P and Top-p, baseline L32152-32262) ---- *)
Definition alb_combined_keep (p : R) (prefix : list Token) (w : Token) : Set :=
  And (alb_minp_keep prefix w) (alb_topp_keep p prefix w).

Definition alb_combined_keep_dec (p : R) (prefix : list Token) (w : Token) :
  Or (alb_combined_keep p prefix w) (Not (alb_combined_keep p prefix w)).
Proof.
  unfold alb_combined_keep.
  destruct (alb_minp_keep_dec prefix w) as [Hmin | Hnotmin].
  - destruct (alb_topp_keep_dec p prefix w) as [Htp | Hntp].
    + left. split; assumption.
    + right. intros [Hm Ht]. exact (Hntp Ht).
  - right. intros [Hm Ht]. exact (Hnotmin Hm).
Defined.

Definition alb_combined_temp_sum (p : R) (prefix : list Token) : R :=
  rsum Token (fun w => match alb_combined_keep_dec p prefix w with
                       | inl _ => alb_temp_factor prefix w
                       | inr _ => zero
                       end) vocab.

(* baseline [combined_temp_sum_pos] L32182: [pick_max] is kept on both counts (by the Min-P lemma and the Top-p premise). *)
Lemma req_combined_temp_sum_pos : forall (p : R) (prefix : list Token),
  le p (alb_max_markov_prob prefix) -> lt zero (alb_combined_temp_sum p prefix).
Proof.
  intros p prefix Hp.
  assert (Hle : le (alb_temp_factor prefix (pick_max_token prefix))
                   (alb_combined_temp_sum p prefix)).
  { unfold alb_combined_temp_sum.
    assert (Heq : req (alb_temp_factor prefix (pick_max_token prefix))
                      (match alb_combined_keep_dec p prefix (pick_max_token prefix) with
                       | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                       | inr _ => zero
                       end)).
    { destruct (alb_combined_keep_dec p prefix (pick_max_token prefix)) as [Hk | Hd].
      - apply req_refl.
      - destruct (Hd (pair (req_pick_max_minp_keep prefix) Hp)). }
    apply (le_id_l (alb_temp_factor prefix (pick_max_token prefix))
                   (match alb_combined_keep_dec p prefix (pick_max_token prefix) with
                    | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                    | inr _ => zero
                    end)
                   (rsum Token
                          (fun w => match alb_combined_keep_dec p prefix w with
                                    | inl _ => alb_temp_factor prefix w
                                    | inr _ => zero
                                    end) vocab)).
    - exact Heq.
    - apply (rls_single_le Token
               (fun w => match alb_combined_keep_dec p prefix w with
                         | inl _ => alb_temp_factor prefix w
                         | inr _ => zero
                         end)
               (pick_max_token prefix) vocab).
      + apply pick_max_in_vocab.
      + intro w. destruct (alb_combined_keep_dec p prefix w) as [Hk2 | Hd2].
        * apply (lt_le_iff zero (alb_temp_factor prefix w)). left.
          unfold alb_temp_factor. apply exp_neg_pos.
        * apply le_refl. }
  apply (req_lt_zero_le_trans (alb_temp_factor prefix (pick_max_token prefix))
                              (alb_combined_temp_sum p prefix)).
  - unfold alb_temp_factor. apply exp_neg_pos.
  - exact Hle.
Qed.

(* baseline [combined_markov_kernel] L32354 (explicit [Hpmax] premise, as in the baseline). *)
Definition alb_combined_markov_kernel (p : R)
  (Hpmax : forall prefix : list Token, le p (alb_max_markov_prob prefix))
  (prefix : list Token) (w : Token) : R :=
  match alb_combined_keep_dec p prefix w with
  | inl _ =>
      mult (alb_temp_factor prefix w)
           (inv_pos (alb_combined_temp_sum p prefix)
                    (req_combined_temp_sum_pos p prefix (Hpmax prefix)))
  | inr _ => zero
  end.

(* ===== baseline [combined_markov_kernel_normalized] L32262 (the req-form main theorem) ===== *)
Theorem req_combined_markov_kernel_normalized : forall (p : R)
  (Hpmax : forall prefix : list Token, le p (alb_max_markov_prob prefix))
  (prefix : list Token),
  req (rsum Token (fun w => alb_combined_markov_kernel p Hpmax prefix w) vocab) one.
Proof.
  intros p Hpmax prefix.
  exact (rls_kernel_norm_gen Token vocab (alb_combined_keep p prefix)
           (fun w => alb_combined_keep_dec p prefix w) (alb_temp_factor prefix)
           (req_combined_temp_sum_pos p prefix (Hpmax prefix))).
Qed.

(* ---- Top-k count-based keep (isomorphic to baseline L32366-32396) ---- *)
(* the [Id]-based deciders on nat/bool/list are kept verbatim *)
Definition alb_NatLt_tk (n m : nat) : Set := Id (Nat.ltb n m) true.

Lemma urb_id_false_true : forall (H : Id false true), Empty_set.
Proof. intro H. inversion H. Qed.

Fixpoint alb_count_kernel_heavier (prefix : list Token) (w : Token)
         (l : list Token) : nat :=
  match l with
  | nil => Datatypes.O
  | a :: rest =>
      match req_lt_dec (alb_markov_kernel prefix w) (alb_markov_kernel prefix a) with
      | inl _ => Datatypes.S (alb_count_kernel_heavier prefix w rest)
      | inr _ => alb_count_kernel_heavier prefix w rest
      end
  end.

Definition alb_topk_keep (K : nat) (prefix : list Token) (w : Token) : Set :=
  alb_NatLt_tk (alb_count_kernel_heavier prefix w vocab) K.

Definition alb_topk_keep_dec (K : nat) (prefix : list Token) (w : Token) :
  Or (alb_topk_keep K prefix w) (Not (alb_topk_keep K prefix w)) :=
  match Nat.ltb (alb_count_kernel_heavier prefix w vocab) K as b
        return Or (Id b true) (Not (Id b true)) with
  | true => inl id_refl
  | false => inr (fun H => urb_id_false_true H)
  end.

(* honest interface premise (a Variable at the same position as baseline L32346): a weakened form of the sorting-correctness property. *)
Variable topk_pickmax_head : forall (K : nat) (prefix : list Token),
  (1 <= K)%nat -> alb_topk_keep K prefix (pick_max_token prefix).

(* ---- combined keep (Min-P and Top-k, baseline L32403-32481) ---- *)
Definition alb_combined_topk_keep (K : nat) (prefix : list Token) (w : Token) : Set :=
  And (alb_minp_keep prefix w) (alb_topk_keep K prefix w).

Definition alb_combined_topk_keep_dec (K : nat) (prefix : list Token) (w : Token) :
  Or (alb_combined_topk_keep K prefix w) (Not (alb_combined_topk_keep K prefix w)).
Proof.
  unfold alb_combined_topk_keep.
  destruct (alb_minp_keep_dec prefix w) as [Hmin | Hnotmin].
  - destruct (alb_topk_keep_dec K prefix w) as [Htop | Hntop].
    + left. split; assumption.
    + right. intros [Hm Ht]. exact (Hntop Ht).
  - right. intros [Hm Ht]. exact (Hnotmin Hm).
Defined.

Definition alb_combined_topk_temp_sum (K : nat) (prefix : list Token) : R :=
  rsum Token (fun w => match alb_combined_topk_keep_dec K prefix w with
                       | inl _ => alb_temp_factor prefix w
                       | inr _ => zero
                       end) vocab.

(* baseline [combined_topk_temp_sum_pos] L32406: [K >= 1] together with the premise [topk_pickmax_head]. *)
Lemma req_combined_topk_temp_sum_pos : forall (K : nat) (prefix : list Token),
  (1 <= K)%nat -> lt zero (alb_combined_topk_temp_sum K prefix).
Proof.
  intros K prefix HK.
  assert (Hle : le (alb_temp_factor prefix (pick_max_token prefix))
                   (alb_combined_topk_temp_sum K prefix)).
  { unfold alb_combined_topk_temp_sum.
    assert (Heq : req (alb_temp_factor prefix (pick_max_token prefix))
                      (match alb_combined_topk_keep_dec K prefix
                                 (pick_max_token prefix) with
                       | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                       | inr _ => zero
                       end)).
    { destruct (alb_combined_topk_keep_dec K prefix (pick_max_token prefix))
              as [Hk | Hd].
      - apply req_refl.
      - destruct (Hd (pair (req_pick_max_minp_keep prefix)
                           (topk_pickmax_head K prefix HK))). }
    apply (le_id_l (alb_temp_factor prefix (pick_max_token prefix))
                   (match alb_combined_topk_keep_dec K prefix
                                 (pick_max_token prefix) with
                    | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                    | inr _ => zero
                    end)
                   (rsum Token
                          (fun w => match alb_combined_topk_keep_dec K prefix w with
                                    | inl _ => alb_temp_factor prefix w
                                    | inr _ => zero
                                    end) vocab)).
    - exact Heq.
    - apply (rls_single_le Token
               (fun w => match alb_combined_topk_keep_dec K prefix w with
                         | inl _ => alb_temp_factor prefix w
                         | inr _ => zero
                         end)
               (pick_max_token prefix) vocab).
      + apply pick_max_in_vocab.
      + intro w. destruct (alb_combined_topk_keep_dec K prefix w) as [Hk2 | Hd2].
        * apply (lt_le_iff zero (alb_temp_factor prefix w)). left.
          unfold alb_temp_factor. apply exp_neg_pos.
        * apply le_refl. }
  apply (req_lt_zero_le_trans (alb_temp_factor prefix (pick_max_token prefix))
                              (alb_combined_topk_temp_sum K prefix)).
  - unfold alb_temp_factor. apply exp_neg_pos.
  - exact Hle.
Qed.

(* baseline [combined_topk_markov_kernel] L32473 (explicit [HK] premise, as in the baseline). *)
Definition alb_combined_topk_markov_kernel (K : nat)
  (HK : forall prefix : list Token, (1 <= K)%nat)
  (prefix : list Token) (w : Token) : R :=
  match alb_combined_topk_keep_dec K prefix w with
  | inl _ =>
      mult (alb_temp_factor prefix w)
           (inv_pos (alb_combined_topk_temp_sum K prefix)
                    (req_combined_topk_temp_sum_pos K prefix (HK prefix)))
  | inr _ => zero
  end.

(* ===== baseline [combined_topk_markov_kernel_normalized] L32481 (the req-form main theorem) ===== *)
Theorem req_combined_topk_markov_kernel_normalized :
  forall (K : nat) (HK : forall prefix : list Token, (1 <= K)%nat)
         (prefix : list Token),
  req (rsum Token (fun w => alb_combined_topk_markov_kernel K HK prefix w) vocab) one.
Proof.
  intros K HK prefix.
  exact (rls_kernel_norm_gen Token vocab (alb_combined_topk_keep K prefix)
           (fun w => alb_combined_topk_keep_dec K prefix w) (alb_temp_factor prefix)
           (req_combined_topk_temp_sum_pos K prefix (HK prefix))).
Qed.

End ReqSamplingWorld.

(* ============================================================ *)
(* Section 4. entropy dynamics, interface-level remainder (req     *)
(*   counterpart of the baseline EntropyDiffReal L46821-51392; the *)
(*   RealDifferentiable family stays with the baseline, and this   *)
(*   section carries only the algebra/order remainder and the      *)
(*   entropy definition group, all interface [Set] values).        *)
(* ============================================================ *)
Section ReqEntropyWorld.

(* ---- req-layer extensionality engine for [exp_neg] (counterpart of
   the baseline L66223 [exp_neg_req_compat_setoid]); the interface
   has no [exp_neg_ext] field, so the engine is rebuilt
   self-contained from [le_antisym] + [exp_neg_le_decr] +
   [lt_le_iff], the same chain as the baseline ---- *)
Lemma req_exp_neg_ext_local : forall x y : R, req x y -> req (exp_neg x) (exp_neg y).
Proof.
  intros x y Hxy.
  apply (le_antisym (exp_neg x) (exp_neg y)).
  - apply (exp_neg_le_decr y x).
    apply (lt_le_iff y x). right. apply (req_sym x y Hxy).
  - apply (exp_neg_le_decr x y).
    apply (lt_le_iff x y). right. exact Hxy.
Qed.

(* ---- counterpart of the baseline [real_le_eps_Kone] L47809
   ([e <= k * (1+e)]) ---- chain: [e <= 1 * e <= k * e] by
   [le_mult_compat] with [1 < k], hence [e <= k * e + k], and the
   right side equals [k * (1+e)] by [distrib], [mult_one] and
   commutativity ---- *)
Lemma req_le_eps_Kone : forall e k : R,
  lt zero e -> lt zero k -> lt one k -> le e (mult k (plus one e)).
Proof.
  intros e k He Hk Hk1.
  assert (Hlek : le e (mult k e)).
  { apply (le_trans e (mult one e) (mult k e)).
    - apply (le_id_l e (mult one e) (mult one e)
               (req_sym (mult one e) e (req_mult_one_l e))
               (le_refl (mult one e))).
    - apply (le_mult_compat one k e He).
      apply (lt_le_iff one k). left. exact Hk1. }
  apply (le_id_r e (plus (mult k e) k) (mult k (plus one e))).
  - apply (req_sym (mult k (plus one e)) (plus (mult k e) k)).
    apply (req_trans (mult k (plus one e))
                     (plus (mult k one) (mult k e))
                     (plus (mult k e) k)).
    + apply distrib.
    + apply (req_trans (plus (mult k one) (mult k e))
                       (plus k (mult k e))
                       (plus (mult k e) k)).
      * apply (req_plus_compat (mult k one) k (mult k e) (mult k e)
                               (mult_one k) (req_refl (mult k e))).
      * apply plus_comm.
  - apply (le_trans e (mult k e) (plus (mult k e) k)).
    + exact Hlek.
    + apply (req_le_plus_nonneg_r (mult k e) k).
      apply (lt_le_iff zero k). left. exact Hk.
Qed.

(* ---- counterpart of the baseline [real_scal_sum_ge] L47997
   ([s * a <= s * (a+b+c+d+1)]) ---- chain: three [plus_assoc] steps
   reassociate the nested sum into [a + (b + (c + (d + 1)))],
   [distrib] peels off [s * a], and the positivity of
   [W = b + (c + (d + 1))] comes segment-wise from [plus_positive]
   ---- *)
Lemma req_scal_sum_ge : forall (s a b c d : R),
  lt zero s -> lt zero a -> lt zero b -> lt zero c -> lt zero d ->
  le (mult s a)
     (mult s (plus (plus (plus (plus a b) c) d) one)).
Proof.
  intros s a b c d Hs Ha Hb Hc Hd.
  assert (Hd1 : lt zero (plus d one))
    by (apply (plus_positive d one); [exact Hd | apply one_pos]).
  assert (Hcd1 : lt zero (plus c (plus d one)))
    by (apply (plus_positive c (plus d one)); [exact Hc | exact Hd1]).
  assert (HW : lt zero (plus b (plus c (plus d one))))
    by (apply (plus_positive b (plus c (plus d one))); [exact Hb | exact Hcd1]).
  apply (le_id_r (mult s a)
                 (plus (mult s a) (mult s (plus b (plus c (plus d one)))))
                 (mult s (plus (plus (plus (plus a b) c) d) one))).
  - apply (req_sym (mult s (plus (plus (plus (plus a b) c) d) one))
                   (plus (mult s a) (mult s (plus b (plus c (plus d one)))))).
    apply (req_trans (mult s (plus (plus (plus (plus a b) c) d) one))
                     (mult s (plus a (plus b (plus c (plus d one)))))
                     (plus (mult s a) (mult s (plus b (plus c (plus d one)))))).
    + apply (req_mult_compat s s (plus (plus (plus (plus a b) c) d) one)
                             (plus a (plus b (plus c (plus d one))))).
      * apply (req_refl s).
      * apply (req_trans (plus (plus (plus (plus a b) c) d) one)
                         (plus (plus (plus a b) c) (plus d one))
                         (plus a (plus b (plus c (plus d one))))).
        -- apply (req_sym (plus (plus (plus a b) c) (plus d one))
                          (plus (plus (plus (plus a b) c) d) one)
                          (plus_assoc (plus (plus a b) c) d one)).
        -- apply (req_trans (plus (plus (plus a b) c) (plus d one))
                            (plus (plus a b) (plus c (plus d one)))
                            (plus a (plus b (plus c (plus d one))))).
           ++ apply (req_sym (plus (plus a b) (plus c (plus d one)))
                             (plus (plus (plus a b) c) (plus d one))
                             (plus_assoc (plus a b) c (plus d one))).
           ++ apply (req_sym (plus a (plus b (plus c (plus d one))))
                             (plus (plus a b) (plus c (plus d one)))
                             (plus_assoc a b (plus c (plus d one)))).
    + apply distrib.
  - apply (req_le_plus_nonneg_r (mult s a)
                                (mult s (plus b (plus c (plus d one))))).
    apply (lt_le_iff zero (mult s (plus b (plus c (plus d one))))).
    left. apply (mult_positive s (plus b (plus c (plus d one))) Hs HW).
Qed.

(* ---- counterpart of the baseline [real_M_inv_absorb] L48129
   ([M * (M^-1 * x) == x]) ---- chain: associativity, reshaping by
   [inv_pos_correct], then left multiplication by one ---- *)
Lemma req_M_inv_absorb : forall (M x : R) (HM : lt zero M),
  req (mult M (mult (inv_pos M HM) x)) x.
Proof.
  intros M x HM.
  apply (req_trans (mult M (mult (inv_pos M HM) x))
                   (mult (mult M (inv_pos M HM)) x)
                   x).
  - apply mult_assoc.
  - apply (req_trans (mult (mult M (inv_pos M HM)) x)
                     (mult one x)
                     x).
    + apply (req_mult_compat (mult M (inv_pos M HM)) one x x
                             (inv_pos_correct M HM) (req_refl x)).
    + apply (req_mult_one_l x).
Qed.

(* ---- counterpart of the baseline [real_abs_exp_pos] L48538
   ([0 < |e^{-x}|]) ---- interface engine: [exp_neg_pos] (the
   self-contained req counterpart of the baseline engine
   [cauchy_real_exp_pos]) plus reshaping by [abs_pos] ---- *)
Lemma req_abs_exp_pos : forall x : R, lt zero (abs (exp_neg x)).
Proof.
  intro x.
  apply (lt_id_r zero (exp_neg x) (abs (exp_neg x))).
  - exact (req_sym (abs (exp_neg x)) (exp_neg x)
                   (abs_pos (exp_neg x) (exp_neg_pos x))).
  - apply exp_neg_pos.
Qed.

(* ---- entropy definition group (point-by-point req form of baseline L51341-51355) ---- *)
Variable Omega_A : forall (E_A : R), lt zero E_A -> R.
Variable Omega_B : forall (E_B : R), lt zero E_B -> R.
Variable Omega_A_pos : forall (E_A : R) (H : lt zero E_A),
  lt zero (Omega_A E_A H).
Variable Omega_B_pos : forall (E_B : R) (H : lt zero E_B),
  lt zero (Omega_B E_B H).
Variable E_total : R.
Variable k_B : R.
Variable E_B_pos : forall (E_A : R) (H : lt zero E_A),
  lt zero (plus E_total (opp E_A)).

(* baseline [real_E_B_ent] L51341 (premise positions match point by point; [dOmega_*] and [Omega_B_wd] stay with the baseline). *)
Definition req_E_B_ent (E_A : R) (H : lt zero E_A) : R :=
  plus E_total (opp E_A).

(* baseline [real_Omega_total_ent] L51343. *)
Definition req_Omega_total_ent (E_A : R) (H : lt zero E_A) : R :=
  mult (Omega_A E_A H) (Omega_B (req_E_B_ent E_A H) (E_B_pos E_A H)).

(* ===== counterpart of the baseline [real_Omega_total_pos] L51345 ([Omega_A * Omega_B > 0]) ===== *)
Lemma req_Omega_total_pos : forall (E_A : R) (H : lt zero E_A),
  lt zero (req_Omega_total_ent E_A H).
Proof.
  intros E_A H. unfold req_Omega_total_ent.
  apply (mult_positive (Omega_A E_A H)
                       (Omega_B (req_E_B_ent E_A H) (E_B_pos E_A H))).
  - exact (Omega_A_pos E_A H).
  - exact (Omega_B_pos (req_E_B_ent E_A H) (E_B_pos E_A H)).
Qed.

(* baseline [real_entropy_ent] L51357: [S := k_B * log Omega_total] (third member of the entropy definition group). *)
Definition req_entropy_ent (E_A : R) (H : lt zero E_A) : R :=
  mult k_B (log (req_Omega_total_ent E_A H) (req_Omega_total_pos E_A H)).

End ReqEntropyWorld.


(* ============================================================ *)
(* Section 5. eviction world, interface-level req form             *)
(*   (counterpart of the baseline RealKVQuantMain L53932-54965,    *)
(*   plus the [req_epos] definition group and the P1 bridge        *)
(*   premise).  Signature changes: the interface has no plain   *)
(*   [exp], so every exponential is rebuilt as [req_epos]          *)
(*   ([:= exp_neg ∘ opp]); where the abstract interface [le] field *)
(*   cannot be decomposed, the baseline [real_le]-shaped           *)
(*   premise positions take the disjunctive [Or] form           *)
(*   (isomorphic point by point).                                  *)
(* ============================================================ *)
Section ReqKVQuantWorld.
Variable S : Type.

(* ---- eviction structure (same shape as baseline L53938-53940: decidable at the [Set] layer) ---- *)
Variable keep : S -> Set.
Variable keep_dec : forall s : S, Or (keep s) (Not (keep s)).

Variable transition : S -> S -> R.
(* point-by-point req dual of the baseline [real_transition_nonneg]
   ([real_le zero T], where [real_le] is really an [Or] form): the
   abstract [le] field of the setoid interface cannot be decomposed,
   so the premise takes the disjunctive [Or] form, isomorphic
   point by point; where the interface form [le zero T] is needed it
   is recovered by [lt_le_iff] (part B4 of this section). *)
Variable transition_nonneg : forall s s' : S,
  Or (lt zero (transition s s')) (req zero (transition s s')).
Variable transition_sym : forall s s' : S,
  req (transition s s') (transition s' s).

Variable energy : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable L : R.
Variable L_pos : lt zero L.
Variable E_max : R.
Variable metric : S -> S -> R.
Variable metric_nonneg : forall s s' : S, le zero (metric s s').
(* energy Lipschitz condition: [|e(s) - e(s')| <= L * metric s s'] (an explicitly postulated interface assumption, isomorphic point by point). *)
Variable energy_lipschitz : forall s s' : S,
  le (abs (plus (energy s) (opp (energy s'))))
     (mult L (metric s s')).
(* energy lower bound: [-E_max <= e(s)] *)
Variable energy_lower : forall s : S, le (opp E_max) (energy s).
Variable sum_over_S : (S -> R) -> R.

(* ---- [req_epos] definition group: positive exponentials
   [e^{x} := exp_neg (opp x)] ---- (the interface has no plain
   [exp]; this is the req reconstruction as the inverse of
   [exp_neg], and the [e^{E_max/D}], [e^{|u-v|}], [e^{Ulips}] of
   parts B3/B4 are all stated in this form) ---- *)
Definition req_epos (x : R) : R := exp_neg (opp x).

Lemma req_epos_le_mono : forall x y : R, le x y -> le (req_epos x) (req_epos y).
Proof.
  intros x y Hxy. unfold req_epos.
  apply (exp_neg_le_decr (opp y) (opp x)).
  apply (opp_le_compat x y). exact Hxy.
Qed.

(* ---- the P1 bridge premise: the req dual of the baseline
   [real_exp_neg_diff_bound] L53901.  Its engine
   [real_exp_abs_minus_one_eps] is Real/Q-layer exponential
   analysis, and the setoid interface has no exp-linear-epsilon
   field, so P1 is postulated as a bridge; every remaining member
   of B2/B3a/B3b/B3c/B4 is proved outright ---- *)
Variable req_boltzmann_diff_bridge : forall (u v eps : R),
  lt zero eps ->
  le (abs (plus (exp_neg u) (opp (exp_neg v))))
     (mult (exp_neg v)
           (plus (mult (abs (plus u (opp v))) (req_epos (abs (plus u (opp v)))))
                 eps)).

(* ---- tool A (counterpart of the baseline L54018
   [real_mult_minus_l]): [a*x + -(a*y) == a*(x + -y)] by
   [distrib] + [req_opp_mult_l] ---- *)
Lemma req_mult_minus_l : forall a x y : R,
  req (plus (mult a x) (opp (mult a y))) (mult a (plus x (opp y))).
Proof.
  intros a x y.
  apply (req_sym (mult a (plus x (opp y))) (plus (mult a x) (opp (mult a y)))).
  apply (req_trans (mult a (plus x (opp y)))
                   (plus (mult a x) (mult a (opp y)))
                   (plus (mult a x) (opp (mult a y)))).
  - apply distrib.
  - apply (req_plus_compat (mult a x) (mult a x)
                           (mult a (opp y)) (opp (mult a y))
                           (req_refl (mult a x)) (req_opp_mult_l a y)).
Qed.

(* ---- tool C (counterpart of the baseline L54037
   [real_mult_minus_r]): [x*z + -(y*z) == (x + -y)*z] by
   [req_opp_mult_r] + right distributivity ---- *)
Lemma req_mult_minus_r : forall x y z : R,
  req (plus (mult x z) (opp (mult y z))) (mult (plus x (opp y)) z).
Proof.
  intros x y z.
  apply (req_trans (plus (mult x z) (opp (mult y z)))
                   (plus (mult x z) (mult (opp y) z))
                   (mult (plus x (opp y)) z)).
  - apply (req_plus_compat (mult x z) (mult x z)
                           (opp (mult y z)) (mult (opp y) z)
                           (req_refl (mult x z))).
    apply (req_sym (mult (opp y) z) (opp (mult y z))).
    apply req_opp_mult_r.
  - apply (req_sym (mult (plus x (opp y)) z) (plus (mult x z) (mult (opp y) z))).
    apply req_mult_plus_distr_r.
Qed.

(* ---- tool E' (export of [le zero] under scaling): [0 < p] and
   [0 <= x] give [0 <= p*x] ---- with the abstract [le] field
   indecomposable, nonnegativity of [p*x] is derived at interface
   level: [zero*p <= x*p] by [le_mult_compat] (strict positivity of
   [p]) plus commutativity transport ---- *)
Lemma req_le_zero_mult_pos_l : forall p x : R,
  lt zero p -> le zero x -> le zero (mult p x).
Proof.
  intros p x Hp Hx.
  apply (le_id_l zero (mult zero p) (mult p x)).
  - apply (req_sym (mult zero p) zero).
    apply (req_trans (mult zero p) (mult p zero) zero).
    + apply mult_comm.
    + apply mult_zero.
  - apply (le_trans (mult zero p) (mult x p) (mult p x)).
    + apply (le_mult_compat zero x p Hp Hx).
    + apply (le_id_l (mult x p) (mult p x) (mult p x)
                     (mult_comm x p) (le_refl (mult p x))).
Qed.

(* ---- tool D' ([Or]-form counterpart of the baseline L54054
   [real_abs_nonneg_req]): [Or (0 < x) (0 == x)] gives
   [|x| == x] ---- *)
Lemma req_abs_nonneg_id_or : forall x : R,
  Or (lt zero x) (req zero x) -> req (abs x) x.
Proof.
  intros x Hx. destruct Hx as [Hlt | Heq].
  - apply abs_pos. exact Hlt.
  - apply (req_trans (abs x) zero x).
    + apply (req_trans (abs x) (abs zero) zero).
      * apply (req_abs_compat x zero (req_sym zero x Heq)).
      * apply abs_zero.
    + exact Heq.
Qed.

(* ---- tool 1 (counterpart of the baseline L53731
   [real_exp_neg_split]): [e^{-u} == e^{-v} * e^{-(u-v)}] by
   [req_exp_neg_ext_local] + [exp_neg_plus] ---- *)
Lemma req_exp_neg_split : forall u v : R,
  req (exp_neg u) (mult (exp_neg v) (exp_neg (plus u (opp v)))).
Proof.
  intros u v.
  assert (Hsum : req (plus v (plus u (opp v))) u).
  { apply (req_trans (plus v (plus u (opp v)))
                     (plus (plus v u) (opp v))
                     u).
    - apply plus_assoc.
    - apply (req_trans (plus (plus v u) (opp v))
                       (plus (plus u v) (opp v))
                       u).
      + apply (req_plus_compat (plus v u) (plus u v) (opp v) (opp v)
                               (plus_comm v u) (req_refl (opp v))).
      + apply (req_trans (plus (plus u v) (opp v))
                         (plus u (plus v (opp v)))
                         u).
        * apply (req_sym (plus u (plus v (opp v)))
                         (plus (plus u v) (opp v))).
          apply plus_assoc.
        * apply (req_trans (plus u (plus v (opp v)))
                           (plus u zero)
                           u).
          -- apply (req_plus_compat u u (plus v (opp v)) zero
                                    (req_refl u) (plus_opp v)).
          -- apply plus_zero. }
  apply (req_trans (exp_neg u)
                   (exp_neg (plus v (plus u (opp v))))
                   (mult (exp_neg v) (exp_neg (plus u (opp v))))).
  - apply (req_exp_neg_ext_local u (plus v (plus u (opp v)))).
    apply (req_sym (plus v (plus u (opp v))) u). exact Hsum.
  - apply exp_neg_plus.
Qed.

(* ---- tool 2b (counterpart of the baseline L53767
   [real_mult_minus_one_distr]): [a*(c - 1) == a*c + -a] ---- *)
Lemma req_mult_minus_one_distr : forall a c : R,
  req (mult a (plus c (opp one))) (plus (mult a c) (opp a)).
Proof.
  intros a c.
  apply (req_trans (mult a (plus c (opp one)))
                   (plus (mult a c) (mult a (opp one)))
                   (plus (mult a c) (opp a))).
  - apply distrib.
  - apply (req_plus_compat (mult a c) (mult a c)
                           (mult a (opp one)) (opp a)
                           (req_refl (mult a c))).
    apply (req_trans (mult a (opp one)) (opp (mult a one)) (opp a)).
    + apply req_opp_mult_l.
    + apply (req_opp_compat (mult a one) a). apply mult_one.
Qed.

(* ===== counterpart of the baseline L53790
   [real_exp_neg_diff_abs]:
   [|e^{-u} - e^{-v}| == e^{-v} * |e^{-(u-v)} - 1|] ---- chain:
   factor with the split tool, [req_mult_minus_one_distr],
   [req_abs_compat], [abs_mult], then reshape by
   [abs_pos (e^{-v})] ---- *)
Lemma req_exp_neg_diff_abs : forall u v : R,
  req (abs (plus (exp_neg u) (opp (exp_neg v))))
      (mult (exp_neg v)
            (abs (plus (exp_neg (plus u (opp v))) (opp one)))).
Proof.
  intros u v.
  pose proof (req_exp_neg_split u v) as Hsplit.
  apply (req_trans (abs (plus (exp_neg u) (opp (exp_neg v))))
                   (abs (mult (exp_neg v)
                              (plus (exp_neg (plus u (opp v))) (opp one))))
                   (mult (exp_neg v)
                         (abs (plus (exp_neg (plus u (opp v))) (opp one))))).
  - apply (req_abs_compat (plus (exp_neg u) (opp (exp_neg v)))
                          (mult (exp_neg v)
                                (plus (exp_neg (plus u (opp v))) (opp one)))).
    apply (req_trans (plus (exp_neg u) (opp (exp_neg v)))
                     (plus (mult (exp_neg v) (exp_neg (plus u (opp v))))
                           (opp (exp_neg v)))
                     (mult (exp_neg v)
                           (plus (exp_neg (plus u (opp v))) (opp one)))).
    + apply (req_plus_compat (exp_neg u)
                             (mult (exp_neg v) (exp_neg (plus u (opp v))))
                             (opp (exp_neg v)) (opp (exp_neg v))
                             Hsplit (req_refl (opp (exp_neg v)))).
    + apply (req_sym (mult (exp_neg v)
                           (plus (exp_neg (plus u (opp v))) (opp one)))
                     (plus (mult (exp_neg v) (exp_neg (plus u (opp v))))
                           (opp (exp_neg v)))).
      apply (req_mult_minus_one_distr (exp_neg v)
                                      (exp_neg (plus u (opp v)))).
  - apply (req_trans (abs (mult (exp_neg v)
                                (plus (exp_neg (plus u (opp v))) (opp one))))
                     (mult (abs (exp_neg v))
                           (abs (plus (exp_neg (plus u (opp v))) (opp one))))
                     (mult (exp_neg v)
                           (abs (plus (exp_neg (plus u (opp v))) (opp one))))).
    + apply abs_mult.
    + apply (req_mult_compat (abs (exp_neg v)) (exp_neg v)
                             (abs (plus (exp_neg (plus u (opp v))) (opp one)))
                             (abs (plus (exp_neg (plus u (opp v))) (opp one)))
                             (abs_pos (exp_neg v) (exp_neg_pos v))
                             (req_refl (abs (plus (exp_neg (plus u (opp v)))
                                                  (opp one))))).
Qed.

(* ---- Boltzmann factors and the evicted distribution (point-by-point req form of baseline L53963-53990) ---- *)
Definition req_kv_boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition req_evicted_partition : R :=
  sum_over_S (fun s : S => match keep_dec s with
                           | inl _ => req_kv_boltzmann_factor s
                           | inr _ => zero
                           end).

Variable req_evicted_partition_pos : lt zero req_evicted_partition.

Definition req_evicted_transition (s s' : S) : R :=
  match keep_dec s with
  | inl _ =>
      match keep_dec s' with
      | inl _ => transition s s'
      | inr _ => zero
      end
  | inr _ => zero
  end.

Definition req_evicted_boltzmann (s : S) : R :=
  match keep_dec s with
  | inl _ =>
      mult (inv_pos req_evicted_partition req_evicted_partition_pos)
           (req_kv_boltzmann_factor s)
  | inr _ => zero
  end.

(* detailed-balance breaking induced by eviction (point-by-point req form of baseline L53992). *)
Definition req_db_breaking (s s' : S) : R :=
  abs (plus (mult (req_evicted_boltzmann s) (req_evicted_transition s s'))
            (opp (mult (req_evicted_boltzmann s') (req_evicted_transition s' s)))).

(* ===== counterpart of the baseline L54055
   [real_db_breaking_evicted_l]: if [s] is evicted then
   [db(s, s') == 0] ---- *)
Lemma req_db_breaking_evicted_l : forall s s' : S, Not (keep s) ->
  req (req_db_breaking s s') zero.
Proof.
  intros s s' Hnk. unfold req_db_breaking.
  assert (H1 : req (mult (req_evicted_boltzmann s) (req_evicted_transition s s'))
                   zero).
  { unfold req_evicted_boltzmann, req_evicted_transition.
    destruct (keep_dec s) as [Hks | Hnks].
    - exact (match Hnk Hks with end).
    - apply (mult_zero zero). }
  assert (H2 : req (mult (req_evicted_boltzmann s') (req_evicted_transition s' s))
                   zero).
  { unfold req_evicted_boltzmann, req_evicted_transition.
    destruct (keep_dec s') as [Hks' | Hnks'].
    + destruct (keep_dec s) as [Hks | Hnks].
      * exact (match Hnk Hks with end).
      * apply (mult_zero (mult (inv_pos req_evicted_partition
                                          req_evicted_partition_pos)
                               (req_kv_boltzmann_factor s'))).
    + destruct (keep_dec s) as [Hks | Hnks].
      * exact (match Hnk Hks with end).
      * apply (mult_zero zero). }
  assert (Hopp : req (opp (mult (req_evicted_boltzmann s')
                                (req_evicted_transition s' s)))
                     zero).
  { apply (req_trans (opp (mult (req_evicted_boltzmann s')
                                (req_evicted_transition s' s)))
                     (opp zero) zero).
    - apply (req_opp_compat (mult (req_evicted_boltzmann s')
                                  (req_evicted_transition s' s))
                            zero H2).
    - apply (req_trans (opp zero) (plus (opp zero) zero) zero).
      + apply (req_sym (plus (opp zero) zero) (opp zero)).
        apply plus_zero.
      + apply (req_trans (plus (opp zero) zero) (plus zero (opp zero)) zero).
        * apply plus_comm.
        * apply plus_opp. }
  apply (req_trans (abs (plus (mult (req_evicted_boltzmann s)
                                    (req_evicted_transition s s'))
                              (opp (mult (req_evicted_boltzmann s')
                                         (req_evicted_transition s' s)))))
                   (abs (plus zero zero))
                   zero).
  - apply (req_abs_compat (plus (mult (req_evicted_boltzmann s)
                                      (req_evicted_transition s s'))
                                (opp (mult (req_evicted_boltzmann s')
                                           (req_evicted_transition s' s))))
                          (plus zero zero)).
    apply (req_plus_compat (mult (req_evicted_boltzmann s)
                                         (req_evicted_transition s s'))
                           zero
                           (opp (mult (req_evicted_boltzmann s')
                                      (req_evicted_transition s' s)))
                           zero H1 Hopp).
  - apply (req_trans (abs (plus zero zero)) (abs zero) zero).
    + apply (req_abs_compat (plus zero zero) zero (plus_zero zero)).
    + apply abs_zero.
Qed.

(* ---- B3a (counterpart of the baseline L54461
   [real_energy_lipschitz_scaled]): [|u - v| <= (invD*L) * metric]
   with [u := invD*e(s)] and [v := invD*e(s')] ---- chain: tool A
   factors out the left multiplier, [abs_mult] + [abs_pos(invD)],
   order preservation under multiplication ([invD > 0] plus the
   Lipschitz premise), then reshaping by associativity ---- *)
Lemma req_energy_lipschitz_scaled : forall s s' : S,
  le (abs (plus (mult (inv_pos D D_pos) (energy s))
                (opp (mult (inv_pos D D_pos) (energy s')))))
     (mult (mult (inv_pos D D_pos) L) (metric s s')).
Proof.
  intros s s'.
  assert (Hw : req (plus (mult (inv_pos D D_pos) (energy s))
                         (opp (mult (inv_pos D D_pos) (energy s'))))
                   (mult (inv_pos D D_pos)
                         (plus (energy s) (opp (energy s'))))).
  { apply (req_mult_minus_l (inv_pos D D_pos) (energy s) (energy s')). }
  assert (Habs : req (abs (plus (mult (inv_pos D D_pos) (energy s))
                                (opp (mult (inv_pos D D_pos) (energy s')))))
                     (mult (inv_pos D D_pos)
                           (abs (plus (energy s) (opp (energy s')))))).
  { apply (req_trans (abs (plus (mult (inv_pos D D_pos) (energy s))
                                (opp (mult (inv_pos D D_pos) (energy s')))))
                     (abs (mult (inv_pos D D_pos)
                                (plus (energy s) (opp (energy s')))))
                     (mult (inv_pos D D_pos)
                           (abs (plus (energy s) (opp (energy s')))))).
    - apply (req_abs_compat (plus (mult (inv_pos D D_pos) (energy s))
                                  (opp (mult (inv_pos D D_pos) (energy s'))))
                            (mult (inv_pos D D_pos)
                                  (plus (energy s) (opp (energy s')))) Hw).
    - apply (req_trans (abs (mult (inv_pos D D_pos)
                                  (plus (energy s) (opp (energy s')))))
                       (mult (abs (inv_pos D D_pos))
                             (abs (plus (energy s) (opp (energy s')))))
                       (mult (inv_pos D D_pos)
                             (abs (plus (energy s) (opp (energy s')))))).
      + apply abs_mult.
      + apply (req_mult_compat (abs (inv_pos D D_pos)) (inv_pos D D_pos)
                               (abs (plus (energy s) (opp (energy s'))))
                               (abs (plus (energy s) (opp (energy s'))))
                               (abs_pos (inv_pos D D_pos) (inv_pos_pos D D_pos))
                               (req_refl (abs (plus (energy s)
                                                    (opp (energy s')))))). }
  assert (Hle : le (mult (inv_pos D D_pos)
                         (abs (plus (energy s) (opp (energy s')))))
                   (mult (inv_pos D D_pos) (mult L (metric s s')))).
  { apply (req_le_mult_compat_r (inv_pos D D_pos)
                                (abs (plus (energy s) (opp (energy s'))))
                                (mult L (metric s s'))).
    - apply (lt_le_iff zero (inv_pos D D_pos)). left.
      apply (inv_pos_pos D D_pos).
    - exact (energy_lipschitz s s'). }
  apply (le_trans (abs (plus (mult (inv_pos D D_pos) (energy s))
                             (opp (mult (inv_pos D D_pos) (energy s')))))
                  (mult (inv_pos D D_pos)
                        (abs (plus (energy s) (opp (energy s')))))
                  (mult (mult (inv_pos D D_pos) L) (metric s s'))).
  - apply (le_id_l (abs (plus (mult (inv_pos D D_pos) (energy s))
                              (opp (mult (inv_pos D D_pos) (energy s')))))
                   (mult (inv_pos D D_pos)
                         (abs (plus (energy s) (opp (energy s')))))
                   (mult (inv_pos D D_pos)
                         (abs (plus (energy s) (opp (energy s')))))
                   Habs (le_refl (mult (inv_pos D D_pos)
                                       (abs (plus (energy s)
                                                  (opp (energy s'))))))).
  - apply (le_id_r (mult (inv_pos D D_pos)
                         (abs (plus (energy s) (opp (energy s')))))
                   (mult (inv_pos D D_pos) (mult L (metric s s')))
                   (mult (mult (inv_pos D D_pos) L) (metric s s'))).
    + apply mult_assoc.
    + exact Hle.
Qed.

(* ---- B3b (counterpart of the baseline L54529
   [real_boltzmann_upper]): [b(s') <= e^{E_max/D}]
   (= [req_epos (invD*E_max)]) ---- chain:
   [invD*(-E_max) <= invD*e(s')] by order preservation and the
   energy lower bound, antitonicity of [exp_neg], then
   [-(invD*(-E_max)) == invD*E_max] by [req_opp_mult_l] ---- *)
Lemma req_boltzmann_upper : forall s' : S,
  le (req_kv_boltzmann_factor s')
     (req_epos (mult (inv_pos D D_pos) E_max)).
Proof.
  intro s'.
  assert (Hle : le (mult (inv_pos D D_pos) (opp E_max))
                   (mult (inv_pos D D_pos) (energy s'))).
  { apply (req_le_mult_compat_r (inv_pos D D_pos) (opp E_max) (energy s')).
    - apply (lt_le_iff zero (inv_pos D D_pos)). left.
      apply (inv_pos_pos D D_pos).
    - exact (energy_lower s'). }
  assert (Hdec : le (exp_neg (mult (inv_pos D D_pos) (energy s')))
                    (exp_neg (mult (inv_pos D D_pos) (opp E_max)))).
  { apply (exp_neg_le_decr (mult (inv_pos D D_pos) (opp E_max))
                           (mult (inv_pos D D_pos) (energy s'))).
    exact Hle. }
  apply (le_id_r (req_kv_boltzmann_factor s')
                 (exp_neg (mult (inv_pos D D_pos) (opp E_max)))
                 (req_epos (mult (inv_pos D D_pos) E_max))).
  - unfold req_epos.
    apply (req_exp_neg_ext_local (mult (inv_pos D D_pos) (opp E_max))
                                 (opp (mult (inv_pos D D_pos) E_max))).
    apply req_opp_mult_l.
  - unfold req_kv_boltzmann_factor. exact Hdec.
Qed.


(* ---- B3c (counterpart of the baseline L54604
   [real_abs_diff_prod_bound]):
   [|u-v| * e^{|u-v|} <= Ulips * e^{Ulips} + eps'] with
   [Ulips := (invD*L) * metric]; [le zero Ulips] is derived from
   [metric_nonneg] by [req_le_zero_mult_pos_l] (the baseline handles
   this step through the Q-pointwise [real_abs_prod_le_eps], while
   the setoid layer goes through the two-stage monotonicity of
   [le_mult_compat] / [req_le_mult_compat_r]) ---- *)
Definition req_ulips (s s' : S) : R :=
  mult (mult (inv_pos D D_pos) L) (metric s s').

Definition req_duv (s s' : S) : R :=
  plus (mult (inv_pos D D_pos) (energy s))
       (opp (mult (inv_pos D D_pos) (energy s'))).

Lemma req_abs_diff_prod_bound : forall (s s' : S) (eps' : R),
  lt zero eps' ->
  le (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s'))))
     (plus (mult (req_ulips s s') (req_epos (req_ulips s s'))) eps').
Proof.
  intros s s' eps' Hep'.
  assert (H1 : le (abs (req_duv s s')) (req_ulips s s')).
  { exact (req_energy_lipschitz_scaled s s'). }
  assert (HzU : le zero (req_ulips s s')).
  { unfold req_ulips.
    apply (req_le_zero_mult_pos_l (mult (inv_pos D D_pos) L) (metric s s')).
    - apply (mult_positive (inv_pos D D_pos) L (inv_pos_pos D D_pos) L_pos).
    - exact (metric_nonneg s s'). }
  assert (HltE : lt zero (req_epos (abs (req_duv s s')))).
  { unfold req_epos. apply exp_neg_pos. }
  assert (Hmono : le (req_epos (abs (req_duv s s')))
                     (req_epos (req_ulips s s'))).
  { apply (req_epos_le_mono (abs (req_duv s s')) (req_ulips s s')). exact H1. }
  apply (le_trans (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s'))))
                  (mult (req_ulips s s') (req_epos (abs (req_duv s s'))))
                  (plus (mult (req_ulips s s') (req_epos (req_ulips s s')))
                        eps')).
  - apply (le_mult_compat (abs (req_duv s s')) (req_ulips s s')
                          (req_epos (abs (req_duv s s'))) HltE H1).
  - apply (le_trans (mult (req_ulips s s') (req_epos (abs (req_duv s s'))))
                    (mult (req_ulips s s') (req_epos (req_ulips s s')))
                    (plus (mult (req_ulips s s') (req_epos (req_ulips s s')))
                          eps')).
    + apply (req_le_mult_compat_r (req_ulips s s')
                                  (req_epos (abs (req_duv s s')))
                                  (req_epos (req_ulips s s')) HzU Hmono).
    + apply (req_le_plus_nonneg_r
               (mult (req_ulips s s') (req_epos (req_ulips s s'))) eps').
      apply (lt_le_iff zero eps'). left. exact Hep'.
Qed.

(* ---- B2c (counterpart of the baseline L54304
   [real_db_breaking_kept_final]): with both states kept,
   [db == invZ * (T * |b(s) - b(s')|)] ---- chain: [T' == T] by
   symmetry, tool C factors [T] out on the right, [abs_mult] with
   [|T| == T] (tool D'), then commutativity; the structural
   identity goes unfold + delta branches, reversed associativity
   with tool A factoring [invZ] out, then [abs_mult] +
   [abs_pos(invZ)]; the final segment transports Hinner through
   [req_mult_compat] ---- *)
Lemma req_db_breaking_kept_final : forall s s' : S,
  keep s -> keep s' ->
  req (req_db_breaking s s')
      (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
            (mult (transition s s')
                  (abs (plus (req_kv_boltzmann_factor s)
                             (opp (req_kv_boltzmann_factor s')))))).
Proof.
  intros s s' Hs Hs'.
  assert (Hinner : req (abs (plus (mult (req_kv_boltzmann_factor s)
                                        (transition s s'))
                                  (opp (mult (req_kv_boltzmann_factor s')
                                             (transition s' s)))))
                       (mult (transition s s')
                             (abs (plus (req_kv_boltzmann_factor s)
                                        (opp (req_kv_boltzmann_factor s')))))).
  { apply (req_trans
             (abs (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                        (opp (mult (req_kv_boltzmann_factor s')
                                   (transition s' s)))))
             (abs (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                        (opp (mult (req_kv_boltzmann_factor s')
                                   (transition s s')))))
             (mult (transition s s')
                   (abs (plus (req_kv_boltzmann_factor s)
                              (opp (req_kv_boltzmann_factor s')))))).
    - apply (req_abs_compat
               (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                     (opp (mult (req_kv_boltzmann_factor s')
                                (transition s' s))))
               (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                     (opp (mult (req_kv_boltzmann_factor s')
                                (transition s s'))))).
      apply (req_plus_compat
               (mult (req_kv_boltzmann_factor s) (transition s s'))
               (mult (req_kv_boltzmann_factor s) (transition s s'))
               (opp (mult (req_kv_boltzmann_factor s') (transition s' s)))
               (opp (mult (req_kv_boltzmann_factor s') (transition s s')))
               (req_refl (mult (req_kv_boltzmann_factor s) (transition s s')))
               (req_opp_compat
                  (mult (req_kv_boltzmann_factor s') (transition s' s))
                  (mult (req_kv_boltzmann_factor s') (transition s s'))
                  (req_mult_compat (req_kv_boltzmann_factor s')
                                   (req_kv_boltzmann_factor s')
                                   (transition s' s) (transition s s')
                                   (req_refl (req_kv_boltzmann_factor s'))
                                   (transition_sym s' s)))).
    - apply (req_trans
               (abs (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                          (opp (mult (req_kv_boltzmann_factor s')
                                     (transition s s')))))
               (abs (mult (plus (req_kv_boltzmann_factor s)
                                (opp (req_kv_boltzmann_factor s')))
                          (transition s s')))
               (mult (transition s s')
                     (abs (plus (req_kv_boltzmann_factor s)
                                (opp (req_kv_boltzmann_factor s')))))).
      + apply (req_abs_compat
                 (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                       (opp (mult (req_kv_boltzmann_factor s')
                                  (transition s s'))))
                 (mult (plus (req_kv_boltzmann_factor s)
                             (opp (req_kv_boltzmann_factor s')))
                       (transition s s'))).
        apply (req_mult_minus_r (req_kv_boltzmann_factor s)
                                (req_kv_boltzmann_factor s')
                                (transition s s')).
      + apply (req_trans
                 (abs (mult (plus (req_kv_boltzmann_factor s)
                                  (opp (req_kv_boltzmann_factor s')))
                            (transition s s')))
                 (mult (abs (plus (req_kv_boltzmann_factor s)
                                  (opp (req_kv_boltzmann_factor s'))))
                       (abs (transition s s')))
                 (mult (transition s s')
                       (abs (plus (req_kv_boltzmann_factor s)
                                  (opp (req_kv_boltzmann_factor s')))))).
        * apply abs_mult.
        * apply (req_trans
                   (mult (abs (plus (req_kv_boltzmann_factor s)
                                    (opp (req_kv_boltzmann_factor s'))))
                         (abs (transition s s')))
                   (mult (abs (plus (req_kv_boltzmann_factor s)
                                    (opp (req_kv_boltzmann_factor s'))))
                         (transition s s'))
                   (mult (transition s s')
                         (abs (plus (req_kv_boltzmann_factor s)
                                    (opp (req_kv_boltzmann_factor s')))))).
          -- apply (req_mult_compat
                      (abs (plus (req_kv_boltzmann_factor s)
                                 (opp (req_kv_boltzmann_factor s'))))
                      (abs (plus (req_kv_boltzmann_factor s)
                                 (opp (req_kv_boltzmann_factor s'))))
                      (abs (transition s s')) (transition s s')
                      (req_refl (abs (plus (req_kv_boltzmann_factor s)
                                           (opp (req_kv_boltzmann_factor s')))))
                      (req_abs_nonneg_id_or (transition s s')
                                            (transition_nonneg s s'))).
          -- apply mult_comm. }
  assert (Hk : req (req_db_breaking s s')
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (abs (plus (mult (req_kv_boltzmann_factor s)
                                          (transition s s'))
                                    (opp (mult (req_kv_boltzmann_factor s')
                                               (transition s' s))))))).
  { unfold req_db_breaking, req_evicted_boltzmann, req_evicted_transition.
    destruct (keep_dec s) as [Hks | Hnks].
    - destruct (keep_dec s') as [Hks' | Hnks'].
      + apply (req_trans
                 (abs (plus (mult (mult (inv_pos req_evicted_partition
                                              req_evicted_partition_pos)
                                       (req_kv_boltzmann_factor s))
                                 (transition s s'))
                           (opp (mult (mult (inv_pos req_evicted_partition
                                                req_evicted_partition_pos)
                                           (req_kv_boltzmann_factor s'))
                                      (transition s' s)))))
                 (abs (mult (inv_pos req_evicted_partition
                                     req_evicted_partition_pos)
                            (plus (mult (req_kv_boltzmann_factor s)
                                        (transition s s'))
                                  (opp (mult (req_kv_boltzmann_factor s')
                                             (transition s' s))))))
                 (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                       (abs (plus (mult (req_kv_boltzmann_factor s)
                                        (transition s s'))
                                  (opp (mult (req_kv_boltzmann_factor s')
                                             (transition s' s))))))).
        * apply (req_abs_compat
                   (plus (mult (mult (inv_pos req_evicted_partition
                                               req_evicted_partition_pos)
                                        (req_kv_boltzmann_factor s))
                                 (transition s s'))
                           (opp (mult (mult (inv_pos req_evicted_partition
                                                req_evicted_partition_pos)
                                           (req_kv_boltzmann_factor s'))
                                      (transition s' s))))
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (plus (mult (req_kv_boltzmann_factor s)
                                     (transition s s'))
                               (opp (mult (req_kv_boltzmann_factor s')
                                          (transition s' s)))))).
          apply (req_trans
                   (plus (mult (mult (inv_pos req_evicted_partition
                                                req_evicted_partition_pos)
                                         (req_kv_boltzmann_factor s))
                               (transition s s'))
                         (opp (mult (mult (inv_pos req_evicted_partition
                                              req_evicted_partition_pos)
                                          (req_kv_boltzmann_factor s'))
                                    (transition s' s))))
                   (plus (mult (inv_pos req_evicted_partition
                                        req_evicted_partition_pos)
                               (mult (req_kv_boltzmann_factor s)
                                     (transition s s')))
                         (opp (mult (inv_pos req_evicted_partition
                                             req_evicted_partition_pos)
                                    (mult (req_kv_boltzmann_factor s')
                                          (transition s' s)))))
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (plus (mult (req_kv_boltzmann_factor s)
                                     (transition s s'))
                               (opp (mult (req_kv_boltzmann_factor s')
                                          (transition s' s)))))).
          -- apply (req_plus_compat
                      (mult (mult (inv_pos req_evicted_partition
                                               req_evicted_partition_pos)
                                        (req_kv_boltzmann_factor s))
                            (transition s s'))
                      (mult (inv_pos req_evicted_partition
                                     req_evicted_partition_pos)
                            (mult (req_kv_boltzmann_factor s)
                                  (transition s s')))
                      (opp (mult (mult (inv_pos req_evicted_partition
                                                   req_evicted_partition_pos)
                                       (req_kv_boltzmann_factor s'))
                                 (transition s' s)))
                      (opp (mult (inv_pos req_evicted_partition
                                          req_evicted_partition_pos)
                                 (mult (req_kv_boltzmann_factor s')
                                       (transition s' s))))
                      (req_sym
                         (mult (inv_pos req_evicted_partition
                                        req_evicted_partition_pos)
                               (mult (req_kv_boltzmann_factor s)
                                     (transition s s')))
                         (mult (mult (inv_pos req_evicted_partition
                                              req_evicted_partition_pos)
                                     (req_kv_boltzmann_factor s))
                               (transition s s'))
                         (mult_assoc
                            (inv_pos req_evicted_partition
                                     req_evicted_partition_pos)
                            (req_kv_boltzmann_factor s) (transition s s')))
                      (req_opp_compat
                         (mult (mult (inv_pos req_evicted_partition
                                              req_evicted_partition_pos)
                                     (req_kv_boltzmann_factor s'))
                               (transition s' s))
                         (mult (inv_pos req_evicted_partition
                                        req_evicted_partition_pos)
                               (mult (req_kv_boltzmann_factor s')
                                     (transition s' s)))
                         (req_sym
                            (mult (inv_pos req_evicted_partition
                                           req_evicted_partition_pos)
                                  (mult (req_kv_boltzmann_factor s')
                                        (transition s' s)))
                            (mult (mult (inv_pos req_evicted_partition
                                                 req_evicted_partition_pos)
                                        (req_kv_boltzmann_factor s'))
                                  (transition s' s))
                            (mult_assoc
                               (inv_pos req_evicted_partition
                                        req_evicted_partition_pos)
                               (req_kv_boltzmann_factor s')
                               (transition s' s))))).
          -- apply (req_mult_minus_l
                      (inv_pos req_evicted_partition req_evicted_partition_pos)
                      (mult (req_kv_boltzmann_factor s) (transition s s'))
                      (mult (req_kv_boltzmann_factor s') (transition s' s))).
        * apply (req_trans
                   (abs (mult (inv_pos req_evicted_partition
                                       req_evicted_partition_pos)
                              (plus (mult (req_kv_boltzmann_factor s)
                                          (transition s s'))
                                    (opp (mult (req_kv_boltzmann_factor s')
                                               (transition s' s))))))
                   (mult (abs (inv_pos req_evicted_partition
                                       req_evicted_partition_pos))
                         (abs (plus (mult (req_kv_boltzmann_factor s)
                                          (transition s s'))
                                    (opp (mult (req_kv_boltzmann_factor s')
                                               (transition s' s))))))
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (abs (plus (mult (req_kv_boltzmann_factor s)
                                          (transition s s'))
                                    (opp (mult (req_kv_boltzmann_factor s')
                                               (transition s' s))))))).
          -- apply abs_mult.
          -- apply (req_mult_compat
                      (abs (inv_pos req_evicted_partition
                                    req_evicted_partition_pos))
                      (inv_pos req_evicted_partition req_evicted_partition_pos)
                      (abs (plus (mult (req_kv_boltzmann_factor s)
                                       (transition s s'))
                                 (opp (mult (req_kv_boltzmann_factor s')
                                            (transition s' s)))))
                      (abs (plus (mult (req_kv_boltzmann_factor s)
                                       (transition s s'))
                                 (opp (mult (req_kv_boltzmann_factor s')
                                            (transition s' s)))))
                      (abs_pos (inv_pos req_evicted_partition
                                        req_evicted_partition_pos)
                               (inv_pos_pos req_evicted_partition
                                            req_evicted_partition_pos))
                      (req_refl (abs (plus (mult (req_kv_boltzmann_factor s)
                                                 (transition s s'))
                                           (opp (mult (req_kv_boltzmann_factor s')
                                                      (transition s' s))))))).
      + exact (match Hnks' Hs' with end).
    - exact (match Hnks Hs with end). }
  apply (req_trans (req_db_breaking s s')
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (abs (plus (mult (req_kv_boltzmann_factor s)
                                          (transition s s'))
                                    (opp (mult (req_kv_boltzmann_factor s')
                                               (transition s' s))))))
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (mult (transition s s')
                               (abs (plus (req_kv_boltzmann_factor s)
                                          (opp (req_kv_boltzmann_factor s'))))))).
  - exact Hk.
  - apply (req_mult_compat
             (inv_pos req_evicted_partition req_evicted_partition_pos)
             (inv_pos req_evicted_partition req_evicted_partition_pos)
             (abs (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                        (opp (mult (req_kv_boltzmann_factor s')
                                   (transition s' s)))))
             (mult (transition s s')
                   (abs (plus (req_kv_boltzmann_factor s)
                              (opp (req_kv_boltzmann_factor s')))))
             (req_refl (inv_pos req_evicted_partition req_evicted_partition_pos))
             Hinner).
Qed.

Definition req_Emax_exp : R := req_epos (mult (inv_pos D D_pos) E_max).
Definition req_eulips (s s' : S) : R := req_epos (req_ulips s s').

(* ---- B3 final (counterpart of the baseline L54636
   [real_boltzmann_diff_bound]):
   [|b(s) - b(s')| <= E*(U*eU) + (E*eps + eps')] -- everything
   except the P1 bridge is proved outright ---- *)
Lemma req_boltzmann_diff_bound : forall (s s' : S) (eps eps' : R),
  lt zero eps -> lt zero eps' ->
  le (abs (plus (req_kv_boltzmann_factor s) (opp (req_kv_boltzmann_factor s'))))
     (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
           (plus (mult req_Emax_exp eps) eps')).
Proof.
  intros s s' eps eps' Hep Hep'.
  assert (HleEv : le (req_kv_boltzmann_factor s') req_Emax_exp).
  { exact (req_boltzmann_upper s'). }
  assert (H1 : le (abs (req_duv s s')) (req_ulips s s')).
  { exact (req_energy_lipschitz_scaled s s'). }
  assert (HltE : lt zero (req_epos (abs (req_duv s s')))).
  { unfold req_epos. apply exp_neg_pos. }
  assert (Hmono : le (req_epos (abs (req_duv s s'))) (req_eulips s s')).
  { apply (req_epos_le_mono (abs (req_duv s s')) (req_ulips s s')). exact H1. }
  assert (Hexp : req (mult (req_kv_boltzmann_factor s')
                           (plus (mult (abs (req_duv s s'))
                                       (req_epos (abs (req_duv s s'))))
                                 eps))
                     (plus (mult (req_kv_boltzmann_factor s')
                                 (mult (abs (req_duv s s'))
                                       (req_epos (abs (req_duv s s')))))
                           (mult (req_kv_boltzmann_factor s') eps))).
  { unfold req_kv_boltzmann_factor. apply distrib. }
  assert (Hle1 : le (abs (plus (req_kv_boltzmann_factor s)
                               (opp (req_kv_boltzmann_factor s'))))
                    (plus (mult (req_kv_boltzmann_factor s')
                                (mult (abs (req_duv s s'))
                                      (req_epos (abs (req_duv s s')))))
                          (mult (req_kv_boltzmann_factor s') eps))).
  { apply (le_id_r
             (abs (plus (req_kv_boltzmann_factor s)
                        (opp (req_kv_boltzmann_factor s'))))
             (mult (req_kv_boltzmann_factor s')
                   (plus (mult (abs (req_duv s s'))
                               (req_epos (abs (req_duv s s'))))
                         eps))
             (plus (mult (req_kv_boltzmann_factor s')
                         (mult (abs (req_duv s s'))
                               (req_epos (abs (req_duv s s')))))
                   (mult (req_kv_boltzmann_factor s') eps)))
    ; [ exact Hexp
      | exact (req_boltzmann_diff_bridge (mult (inv_pos D D_pos) (energy s))
                                         (mult (inv_pos D D_pos) (energy s'))
                                         eps Hep) ]. }
  assert (Hltduv : lt zero (mult (req_kv_boltzmann_factor s')
                                 (req_epos (abs (req_duv s s'))))).
  { unfold req_kv_boltzmann_factor.
    apply (mult_positive (exp_neg (mult (inv_pos D D_pos) (energy s')))
                         (req_epos (abs (req_duv s s')))).
    - apply exp_neg_pos.
    - exact HltE. }
  assert (Hmono2 : le (mult (req_kv_boltzmann_factor s')
                            (req_epos (abs (req_duv s s'))))
                      (mult req_Emax_exp (req_eulips s s'))).
  { apply (le_trans (mult (req_kv_boltzmann_factor s')
                          (req_epos (abs (req_duv s s'))))
                    (mult req_Emax_exp (req_epos (abs (req_duv s s'))))
                    (mult req_Emax_exp (req_eulips s s'))).
    - apply (le_mult_compat (req_kv_boltzmann_factor s') req_Emax_exp
                            (req_epos (abs (req_duv s s'))) HltE HleEv).
    - apply (req_le_mult_compat_r req_Emax_exp
                                  (req_epos (abs (req_duv s s')))
                                  (req_eulips s s')).
      + apply (lt_le_iff zero req_Emax_exp). left.
        unfold req_Emax_exp, req_epos. apply exp_neg_pos.
      + exact Hmono. }
  assert (Heq1 : req (mult (req_kv_boltzmann_factor s')
                           (mult (abs (req_duv s s'))
                                 (req_epos (abs (req_duv s s')))))
                     (mult (abs (req_duv s s'))
                           (mult (req_kv_boltzmann_factor s')
                                 (req_epos (abs (req_duv s s')))))).
  { apply (req_trans
             (mult (req_kv_boltzmann_factor s')
                   (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s')))))
             (mult (mult (req_kv_boltzmann_factor s') (abs (req_duv s s')))
                   (req_epos (abs (req_duv s s'))))
             (mult (abs (req_duv s s'))
                   (mult (req_kv_boltzmann_factor s')
                         (req_epos (abs (req_duv s s')))))).
    - apply mult_assoc.
    - apply (req_trans
               (mult (mult (req_kv_boltzmann_factor s') (abs (req_duv s s')))
                     (req_epos (abs (req_duv s s'))))
               (mult (mult (abs (req_duv s s')) (req_kv_boltzmann_factor s'))
                     (req_epos (abs (req_duv s s'))))
               (mult (abs (req_duv s s'))
                     (mult (req_kv_boltzmann_factor s')
                           (req_epos (abs (req_duv s s')))))).
      + apply (req_mult_compat
                 (mult (req_kv_boltzmann_factor s') (abs (req_duv s s')))
                 (mult (abs (req_duv s s')) (req_kv_boltzmann_factor s'))
                 (req_epos (abs (req_duv s s')))
                 (req_epos (abs (req_duv s s')))
                 (mult_comm (req_kv_boltzmann_factor s') (abs (req_duv s s')))
                 (req_refl (req_epos (abs (req_duv s s'))))).
      + apply (req_sym
                 (mult (abs (req_duv s s'))
                       (mult (req_kv_boltzmann_factor s')
                             (req_epos (abs (req_duv s s')))))
                 (mult (mult (abs (req_duv s s'))
                             (req_kv_boltzmann_factor s'))
                       (req_epos (abs (req_duv s s'))))).
        apply mult_assoc. }
  assert (HzU : le zero (req_ulips s s')).
  { unfold req_ulips.
    apply (req_le_zero_mult_pos_l (mult (inv_pos D D_pos) L) (metric s s')).
    - apply (mult_positive (inv_pos D D_pos) L (inv_pos_pos D D_pos) L_pos).
    - exact (metric_nonneg s s'). }
  assert (HstepY : le (mult (req_ulips s s')
                            (mult (req_kv_boltzmann_factor s')
                                  (req_epos (abs (req_duv s s')))))
                      (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))).
  { apply (req_le_mult_compat_r (req_ulips s s')
                                (mult (req_kv_boltzmann_factor s')
                                      (req_epos (abs (req_duv s s'))))
                                (mult req_Emax_exp (req_eulips s s')))
    ; [ exact HzU | exact Hmono2 ]. }
  assert (Hbig1 : le (mult (abs (req_duv s s'))
                           (mult (req_kv_boltzmann_factor s')
                                 (req_epos (abs (req_duv s s')))))
                      (plus (mult (req_ulips s s')
                                  (mult req_Emax_exp (req_eulips s s')))
                            eps')).
  { apply (le_trans
             (mult (abs (req_duv s s'))
                   (mult (req_kv_boltzmann_factor s') (req_epos (abs (req_duv s s')))))
             (mult (req_ulips s s') (mult (req_kv_boltzmann_factor s') (req_epos (abs (req_duv s s')))))
             (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')).
    - apply (le_mult_compat (abs (req_duv s s')) (req_ulips s s')
                            (mult (req_kv_boltzmann_factor s')
                                  (req_epos (abs (req_duv s s'))))
                            Hltduv H1).
    - apply (le_trans
               (mult (req_ulips s s') (mult (req_kv_boltzmann_factor s') (req_epos (abs (req_duv s s')))))
               (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
               (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')).
      + exact HstepY.
      + apply (req_le_plus_nonneg_r
                 (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps').
        apply (lt_le_iff zero eps'). left. exact Hep'. }
  assert (Hbig1a : le (mult (req_kv_boltzmann_factor s')
                            (mult (abs (req_duv s s'))
                                  (req_epos (abs (req_duv s s')))))
                      (plus (mult (req_ulips s s')
                                  (mult req_Emax_exp (req_eulips s s')))
                            eps')).
  { exact (le_id_l (mult (req_kv_boltzmann_factor s')
                         (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s')))))
                   (mult (abs (req_duv s s'))
                         (mult (req_kv_boltzmann_factor s') (req_epos (abs (req_duv s s')))))
                   (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                   Heq1 Hbig1). }
  assert (Hbig2 : le (mult (req_kv_boltzmann_factor s') eps)
                     (mult req_Emax_exp eps)).
  { apply (le_mult_compat (req_kv_boltzmann_factor s') req_Emax_exp eps
                          Hep HleEv). }
  assert (Hsum : le (plus (mult (req_kv_boltzmann_factor s')
                                (mult (abs (req_duv s s'))
                                      (req_epos (abs (req_duv s s')))))
                          (mult (req_kv_boltzmann_factor s') eps))
                    (plus (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                          (mult req_Emax_exp eps))).
  { apply (le_plus_compat
             (mult (req_kv_boltzmann_factor s') (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s')))))
             (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
             (mult (req_kv_boltzmann_factor s') eps)
             (mult req_Emax_exp eps)
             Hbig1a Hbig2). }
  assert (HrA : req (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                    (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))).
  { apply (req_trans (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                     (mult (mult (req_ulips s s') req_Emax_exp) (req_eulips s s'))
                     (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))).
    - apply mult_assoc.
    - apply (req_trans (mult (mult (req_ulips s s') req_Emax_exp) (req_eulips s s'))
                       (mult (mult req_Emax_exp (req_ulips s s')) (req_eulips s s'))
                       (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))).
      + apply (req_mult_compat (mult (req_ulips s s') req_Emax_exp)
                               (mult req_Emax_exp (req_ulips s s'))
                               (req_eulips s s') (req_eulips s s')
                               (mult_comm (req_ulips s s') req_Emax_exp)
                               (req_refl (req_eulips s s'))).
      + apply (req_sym (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                       (mult (mult req_Emax_exp (req_ulips s s')) (req_eulips s s'))).
        apply mult_assoc. }
  assert (Hr : req
                 (plus (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                       (mult req_Emax_exp eps))
                 (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                       (plus (mult req_Emax_exp eps) eps'))).
  { apply (req_trans
             (plus (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                   (mult req_Emax_exp eps))
             (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                   (plus (mult req_Emax_exp eps) eps'))
             (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                   (plus (mult req_Emax_exp eps) eps'))).
    - apply (req_trans
               (plus (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                     (mult req_Emax_exp eps))
               (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                     (plus eps' (mult req_Emax_exp eps)))
               (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                     (plus (mult req_Emax_exp eps) eps'))).
      + apply (req_sym (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                             (plus eps' (mult req_Emax_exp eps)))
                       (plus (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                             (mult req_Emax_exp eps))).
        apply plus_assoc.
      + apply (req_plus_compat
                 (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                 (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                 (plus eps' (mult req_Emax_exp eps))
                 (plus (mult req_Emax_exp eps) eps')
                 (req_refl (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))))
                 (plus_comm eps' (mult req_Emax_exp eps))).
    - apply (req_plus_compat
               (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
               (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
               (plus (mult req_Emax_exp eps) eps')
               (plus (mult req_Emax_exp eps) eps')
               HrA
               (req_refl (plus (mult req_Emax_exp eps) eps'))). }
  apply (le_trans (abs (plus (req_kv_boltzmann_factor s) (opp (req_kv_boltzmann_factor s'))))
                  (plus (mult (req_kv_boltzmann_factor s')
                              (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s')))))
                        (mult (req_kv_boltzmann_factor s') eps))
                  (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                        (plus (mult req_Emax_exp eps) eps'))).
  - exact Hle1.
  - exact (le_id_r (plus (mult (req_kv_boltzmann_factor s')
                                    (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s')))))
                              (mult (req_kv_boltzmann_factor s') eps))
                   (plus (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                         (mult req_Emax_exp eps))
                   (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                         (plus (mult req_Emax_exp eps) eps'))
                   Hr Hsum).
Qed.

(* ---- B4 final theorem (counterpart of the baseline L54841
   [real_db_breaking_bound_eps]):
   [db(s,s') <= invZ * T * [E*(U*eU) + (E*eps + eps')]] --
   assembly: the B2c structural identity, the B3 quantitative
   bound, two layers of order preservation under multiplication
   (resolving the [Or]-form [T >= 0] and [invZ > 0]), closed by
   [le_trans] ---- *)
Theorem req_db_breaking_bound_eps : forall (s s' : S) (eps eps' : R),
  keep s -> keep s' -> lt zero eps -> lt zero eps' ->
  le (req_db_breaking s s')
     (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
           (mult (transition s s')
                 (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                       (plus (mult req_Emax_exp eps) eps')))).
Proof.
  intros s s' eps eps' Hs Hs' Hep Hep'.
  assert (Hk : le (req_db_breaking s s')
                  (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                        (mult (transition s s')
                              (abs (plus (req_kv_boltzmann_factor s)
                                         (opp (req_kv_boltzmann_factor s'))))))).
  { exact (le_id_l (req_db_breaking s s')
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (mult (transition s s')
                               (abs (plus (req_kv_boltzmann_factor s)
                                          (opp (req_kv_boltzmann_factor s'))))))
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (mult (transition s s')
                               (abs (plus (req_kv_boltzmann_factor s)
                                          (opp (req_kv_boltzmann_factor s'))))))
                   (req_db_breaking_kept_final s s' Hs Hs')
                   (le_refl (mult (inv_pos req_evicted_partition
                                             req_evicted_partition_pos)
                                  (mult (transition s s')
                                        (abs (plus (req_kv_boltzmann_factor s)
                                                   (opp (req_kv_boltzmann_factor s')))))))). }
  pose proof (req_boltzmann_diff_bound s s' eps eps' Hep Hep') as Hbd.
  assert (Hin : le (mult (transition s s')
                         (abs (plus (req_kv_boltzmann_factor s)
                                    (opp (req_kv_boltzmann_factor s')))))
                   (mult (transition s s')
                         (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                               (plus (mult req_Emax_exp eps) eps')))).
  { apply (req_le_mult_compat_r
             (transition s s')
             (abs (plus (req_kv_boltzmann_factor s) (opp (req_kv_boltzmann_factor s'))))
             (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                   (plus (mult req_Emax_exp eps) eps'))).
    - apply (lt_le_iff zero (transition s s')). exact (transition_nonneg s s').
    - exact Hbd. }
  assert (Hout : le (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                          (mult (transition s s')
                                (abs (plus (req_kv_boltzmann_factor s)
                                           (opp (req_kv_boltzmann_factor s'))))))
                    (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                          (mult (transition s s')
                                (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                                      (plus (mult req_Emax_exp eps) eps'))))).
  { apply (req_le_mult_compat_r
             (inv_pos req_evicted_partition req_evicted_partition_pos)
             (mult (transition s s')
                   (abs (plus (req_kv_boltzmann_factor s) (opp (req_kv_boltzmann_factor s')))))
             (mult (transition s s')
                   (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                         (plus (mult req_Emax_exp eps) eps')))).
    - apply (lt_le_iff zero (inv_pos req_evicted_partition req_evicted_partition_pos)).
      left. apply (inv_pos_pos req_evicted_partition req_evicted_partition_pos).
    - exact Hin. }
  apply (le_trans (req_db_breaking s s')
                  (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                        (mult (transition s s')
                              (abs (plus (req_kv_boltzmann_factor s)
                                         (opp (req_kv_boltzmann_factor s'))))))
                  (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                        (mult (transition s s')
                              (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                                    (plus (mult req_Emax_exp eps) eps'))))).
  - exact Hk.
  - exact Hout.
Qed.

End ReqKVQuantWorld.

