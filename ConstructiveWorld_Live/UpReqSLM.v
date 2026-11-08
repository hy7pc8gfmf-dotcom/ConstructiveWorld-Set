(* ConstructiveWorld-Set — stochastic language modeling over the req carrier. *)

(** * UpReqSLM: temperature allocation, Markov kernels and softmax over [req].

    Mission.  The stochastic language model (Section [ReqSLM]): temperature
      factor and partition, the Markov kernels [slm_markov_kernel] and
      [slm_softmax], entropy [slm_markov_entropy], the temperature-zero
      limit [slm_markov_temperature_zero_limit] with [k_d]; greedy bounds
      [req_greedy_kernel_limit]/[req_nonoptimal_probability_absolute]
      (slots [in_vocab]/[optimal], discharged in [ReqSLMGreedyDischarge]);
      [req_markov_pos_slm]/[req_markov_normalized]/[req_markov_entropy_nonneg].

    Dependencies.  Requires the backbone [S01_BaseRing] .. [S15_TailFEPUp],
      [UpReqAlgebra], [UpReqDist], [UpReqAlignRestB], [G09_MiscSmall]; Stdlib [List].

    References.  Statements are carried over verbatim from the
      StochasticLanguageModel and LogDiff3 tail sections of the upstream
      ConstructiveWorld-Main baseline.  Adaptations: minus is [req_minus];
      [log] carries an [lt zero] premise; [list_sum] is the [rsum] Fixpoint;
      Id-ring lemmas become [UpReqAlgebra] req proofs; [markov_normalized]
      instantiates [rls_kernel_norm_gen].

    Constructivity.  Pure constructive: zero admission words, no classical
      logic, term-mode proofs without setoid rewriting; statement faces are
      carried by [Set] ([req]/[lt]/[le]/[Id]/[And := A*B] all Set-valued);
      the log slots [log_le_linear_plain]/[log_req_compat_plain] remain explicit.

    Build.  [coqc -native-compiler no -q -Q . "" UpReqSLM.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 000160bc]. *)

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
Require Import UpReqAlignRestB.
Require Import G09_MiscSmall.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.
(* Pool-build adaptation: the interface class in this tree is unparameterized
   ([S07_RealSetoidExpLog.v] zero-argument Class [RealInterfaceEnhancedSetoid]
   with the global Instance [RealEnhancedReal]); the argument-bearing binders
   [Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}] of the upstream
   revision are dropped, the carrier R is bound to the global Real by the
   file-top Notation below, and the two carrier-bearing premise classes
   [ReqNonnegPlain]/[ReqLogPlain] and [reqDecidableOrder] are re-anchored
   zero-argument (the zero-argument Class [reqDecidableOrder] sits in
   [G09_MiscSmall.v]). Zero Obj.magic, zero Prop casts, statement faces
   preserved verbatim. *)
Notation R := Real.

(* ===================================================================== *)

(* ===================================================================== *)

(* the plain nonnegativity premise class (abs and metric are nonnegative) *)
Class ReqNonnegPlain := {
  abs_nonneg_plain : forall a : R, le zero (abs a);
  metric_pos_plain : forall a b : R, le zero (metric a b)
}.

(* the log-family premise class (the same slots as the gibbs_inequality family):
   [log_le_linear_plain] is the fieldwise copy of the Id-face [log_le_linear]
   field, and [log_req_compat_plain] mirrors the [log_req_compat] slot of
   [ReqLogBridge] in [UpReqAlgebra] — required by [req_log_inv_one_inv] and by
   the lower-bound lemmas of the [LogDiff3] section below *)
Class ReqLogPlain := {
  log_le_linear_plain : forall (x : R) (Hx : lt zero x),
    le (log x Hx) (req_minus x one);
  log_req_compat_plain : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy)
}.

(* the le-zero-mult field chain is provable outright, so it is stated as a lemma
   instead of a declared slot *)
Section ReqWaveZero.

Lemma req_le_zero_mult_nonneg : forall a b : R,
  le zero a -> le zero b -> le zero (mult a b).
Proof.
  intros a b Ha Hb.
  apply (le_id_l zero (mult zero b) (mult a b)).
  - apply (req_sym (mult zero b) zero).
    apply (req_trans (mult zero b) (mult b zero) zero).
    + apply mult_comm.
    + apply mult_zero.
  - exact (le_mult_compat_weak zero a b Hb Ha).
Qed.

End ReqWaveZero.

(* ===================================================================== *)
(* Part 1. The reqSLM definition block and the SLM 17(b) statement family *)
(* ===================================================================== *)
Section ReqSLM.


Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable total_loss : list Token -> R.   (* the sequence loss (the loss of prefix ++ [w]) *)
Variable temperature : R.
Variable temperature_pos : lt zero temperature.

(* ---- definition block: slm_temp_factor / list_sum / slm_partition_temp /
   slm_markov_kernel / expected_loss / markov_entropy / softmax are all
   expressed through exp_neg / inv_pos; the carrier [rsum] is the list_sum
   Fixpoint carried verbatim from [UpReqAlignRestB] ---- *)

Definition slm_temp_factor (prefix : list Token) (w : Token) : R :=
  exp_neg (mult (inv_pos temperature temperature_pos) (total_loss (prefix ++ [w]))).

Definition slm_partition_temp (prefix : list Token) : R :=
  rsum Token (slm_temp_factor prefix) vocab.

Definition slm_partition_temp_pos (prefix : list Token) :
  lt zero (slm_partition_temp prefix) :=
  rls_pos Token (slm_temp_factor prefix)
    (fun w => exp_neg_pos (mult (inv_pos temperature temperature_pos)
                                (total_loss (prefix ++ [w]))))
    vocab vocab_nonempty.

Definition slm_markov_kernel (prefix : list Token) (w : Token) : R :=
  mult (slm_temp_factor prefix w)
       (inv_pos (slm_partition_temp prefix) (slm_partition_temp_pos prefix)).

Definition slm_expected_loss (prefix : list Token) : R :=
  rsum Token (fun w => mult (slm_markov_kernel prefix w) (total_loss (prefix ++ [w]))) vocab.

(* ---- item 2: list_sum_add (list induction, the rls_* template) ---- *)

Lemma req_list_sum_add : forall (f g : Token -> R) (l : list Token),
  req (rsum Token (fun w => plus (f w) (g w)) l)
      (plus (rsum Token f l) (rsum Token g l)).
Proof.
  intros f g l. induction l as [| w rest IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - apply req_sym. apply plus_zero.
  - apply (req_trans _ (plus (plus (f w) (g w))
                             (plus (rsum Token f rest) (rsum Token g rest))) _).
    + apply req_plus_compat.
      * apply req_refl.
      * exact IH.
    + apply req_plus_swap_mid.
Qed.

(* ---- item 10: list_sum_zero_fn ---- *)

Lemma req_list_sum_zero_fn : forall l : list Token,
  req (rsum Token (fun _ : Token => zero) l) zero.
Proof.
  intro l. induction l as [| w rest IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - apply req_refl.
  - exact (req_trans _ _ _ (plus_comm zero (rsum Token (fun _ : Token => zero) rest))
             (req_trans _ _ _ (plus_zero (rsum Token (fun _ : Token => zero) rest)) IH)).
Qed.

(* ---- helper: the InT-restricted form of list_sum_le_on_list (its premise
   shape differs from rls_le of [UpReqAlignRestB] — see the header adaptation
   note); proved by a short induction, without restating rls_le itself ---- *)

Lemma req_list_sum_le_on_list : forall (l : list Token) (f g : Token -> R),
  (forall w : Token, InT w l -> le (f w) (g w)) ->
  le (rsum Token f l) (rsum Token g l).
Proof.
  intros l f g Hfg. induction l as [| w rest IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - apply le_refl.
  - apply le_plus_compat.
    + apply Hfg. apply InT_here.
    + apply IH. intros w0 Hw0. apply Hfg. exact (InT_next w0 w rest Hw0).
Qed.

(* ---- item 1: temp_factor_antitone (exp_neg_le_decr + req_le_mult_compat_r
   + the inv_pos slot) ---- *)

Lemma req_temp_factor_antitone : forall (prefix : list Token) (w1 w2 : Token),
  le (total_loss (prefix ++ [w1])) (total_loss (prefix ++ [w2])) ->
  le (slm_temp_factor prefix w2) (slm_temp_factor prefix w1).
Proof.
  intros prefix w1 w2 Hloss.
  unfold slm_temp_factor.
  assert (Hinv_nonneg : le zero (inv_pos temperature temperature_pos))
    by (apply (lt_le_iff _ _); left; apply inv_pos_pos).
  exact (exp_neg_le_decr _ _
           (req_le_mult_compat_r (inv_pos temperature temperature_pos)
                                 (total_loss (prefix ++ [w1]))
                                 (total_loss (prefix ++ [w2]))
                                 Hinv_nonneg Hloss)).
Qed.

(* ---- item 3: markov_kernel_antitone (item 1 + a shared inv ordering chain) ---- *)

Lemma req_markov_kernel_antitone : forall (prefix : list Token) (w1 w2 : Token),
  le (total_loss (prefix ++ [w1])) (total_loss (prefix ++ [w2])) ->
  le (slm_markov_kernel prefix w2) (slm_markov_kernel prefix w1).
Proof.
  intros prefix w1 w2 Hloss.
  unfold slm_markov_kernel.
  assert (Htf : le (slm_temp_factor prefix w2) (slm_temp_factor prefix w1))
    by exact (req_temp_factor_antitone prefix w1 w2 Hloss).
  assert (Hinv_nonneg : le zero (inv_pos (slm_partition_temp prefix)
                                         (slm_partition_temp_pos prefix)))
    by (apply (lt_le_iff _ _); left; apply inv_pos_pos).
  assert (Hm1 : le (mult (inv_pos (slm_partition_temp prefix) (slm_partition_temp_pos prefix))
                         (slm_temp_factor prefix w2))
                   (mult (inv_pos (slm_partition_temp prefix) (slm_partition_temp_pos prefix))
                         (slm_temp_factor prefix w1)))
    by exact (req_le_mult_compat_r _ _ _ Hinv_nonneg Htf).
  assert (Hsw2 : le (mult (slm_temp_factor prefix w2)
                          (inv_pos (slm_partition_temp prefix) (slm_partition_temp_pos prefix)))
                    (mult (inv_pos (slm_partition_temp prefix) (slm_partition_temp_pos prefix))
                          (slm_temp_factor prefix w2)))
    by exact (le_id_l _ _ _ (mult_comm _ _) (le_refl _)).
  assert (Hsw3 : le (mult (inv_pos (slm_partition_temp prefix) (slm_partition_temp_pos prefix))
                          (slm_temp_factor prefix w1))
                    (mult (slm_temp_factor prefix w1)
                          (inv_pos (slm_partition_temp prefix) (slm_partition_temp_pos prefix))))
    by exact (le_id_l _ _ _ (mult_comm _ _) (le_refl _)).
  exact (le_trans _ _ _ Hsw2 (le_trans _ _ _ Hm1 Hsw3)).
Qed.

(* ---- the markov_pos lemma: the counterpart of [UpReqAlignRestB]'s
   req_markov_pos is closed inside its Min-P domain section and cannot be
   instantiated here, so the same statement is proved directly ---- *)

Lemma req_markov_pos_slm : forall prefix w, lt zero (slm_markov_kernel prefix w).
Proof.
  intros prefix w. unfold slm_markov_kernel. apply mult_positive.
  - unfold slm_temp_factor. apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* ---- item 4: markov_normalized (instantiating rls_kernel_norm_gen) ---- *)

Theorem req_markov_normalized : forall prefix,
  req (rsum Token (fun w => slm_markov_kernel prefix w) vocab) one.
Proof.
  intro prefix.
  exact (rls_kernel_norm_gen Token vocab (fun _ : Token => True) (fun _ : Token => inl I)                             (slm_temp_factor prefix) (slm_partition_temp_pos prefix)).
Qed.

(* ---- item 5: markov_relative (the largest (b)-class statement of the SLM
   block; the exp_neg congruence relies on req_exp_neg_ext_local of
   [UpReqAlignRestB]) ---- *)

Theorem req_markov_relative :
  forall (prefix : list Token) (w wstar : Token),
    req (slm_markov_kernel prefix w)
        (mult (slm_markov_kernel prefix wstar)
              (exp_neg (mult (inv_pos temperature temperature_pos)
                             (req_minus (total_loss (prefix ++ [w]))
                                        (total_loss (prefix ++ [wstar])))))).
Proof.
  intros prefix w wstar.
  unfold slm_markov_kernel, slm_temp_factor.
  set (A := exp_neg (mult (inv_pos temperature temperature_pos)
                          (total_loss (prefix ++ [wstar])))).
  set (B := exp_neg (mult (inv_pos temperature temperature_pos)
                          (req_minus (total_loss (prefix ++ [w]))
                                     (total_loss (prefix ++ [wstar]))))).
  set (C := inv_pos (slm_partition_temp prefix) (slm_partition_temp_pos prefix)).
  set (Ap := exp_neg (mult (inv_pos temperature temperature_pos)
                           (total_loss (prefix ++ [w])))).
  (* regrouping: mult (mult A C) B == mult (mult A B) C *)
  assert (Hre : req (mult (mult A C) B) (mult (mult A B) C)).
  { exact (req_trans _ _ _
             (req_sym (mult A (mult C B)) (mult (mult A C) B) (mult_assoc A C B))
             (req_trans _ _ _
               (req_mult_compat A A (mult C B) (mult B C) (req_refl A) (mult_comm C B))
               (mult_assoc A B C))). }
  (* exponent addition: A*B == Ap (exp_neg_plus + distrib + a minus-cancellation chain) *)
  assert (Hprod : req (mult A B) Ap).
  { assert (Hep : req (mult A B)
                      (exp_neg (plus (mult (inv_pos temperature temperature_pos)
                                          (total_loss (prefix ++ [wstar])))
                                     (mult (inv_pos temperature temperature_pos)
                                           (req_minus (total_loss (prefix ++ [w]))
                                                      (total_loss (prefix ++ [wstar])))))))
      by (apply req_sym; apply exp_neg_plus).
    assert (Halg : req (plus (mult (inv_pos temperature temperature_pos)
                                   (total_loss (prefix ++ [wstar])))
                             (mult (inv_pos temperature temperature_pos)
                                   (req_minus (total_loss (prefix ++ [w]))
                                              (total_loss (prefix ++ [wstar])))))
                       (mult (inv_pos temperature temperature_pos)
                             (total_loss (prefix ++ [w])))).
    { assert (Hd : req (plus (mult (inv_pos temperature temperature_pos)
                                   (total_loss (prefix ++ [wstar])))
                             (mult (inv_pos temperature temperature_pos)
                                   (req_minus (total_loss (prefix ++ [w]))
                                              (total_loss (prefix ++ [wstar])))))
                       (mult (inv_pos temperature temperature_pos)
                             (plus (total_loss (prefix ++ [wstar]))
                                   (req_minus (total_loss (prefix ++ [w]))
                                              (total_loss (prefix ++ [wstar]))))))
        by (apply req_sym; apply distrib).
      assert (Hc : req (plus (total_loss (prefix ++ [wstar]))
                             (req_minus (total_loss (prefix ++ [w]))
                                        (total_loss (prefix ++ [wstar]))))
                       (total_loss (prefix ++ [w])))
        by exact (req_minus_plus_cancel _ _).
      exact (req_trans _ _ _ Hd (req_mult_compat _ _ _ _ (req_refl _) Hc)). }
    exact (req_trans _ _ _ Hep (req_exp_neg_ext_local _ _ Halg)). }
  (* assembly: mult Ap C == mult (mult A C) B *)
  assert (Hmid : req (mult (mult A B) C) (mult Ap C))
    by exact (req_mult_compat (mult A B) Ap C C Hprod (req_refl C)).
  exact (req_sym (mult (mult A C) B) (mult Ap C) (req_trans _ _ _ Hre Hmid)).
Qed.

(* ---- item 6: markov_temperature_zero_limit (item 5 + an inv-cancellation chain) ---- *)

Theorem req_markov_temperature_zero_limit :
  forall (prefix : list Token) (w wstar : Token),
    le (total_loss (prefix ++ [wstar])) (total_loss (prefix ++ [w])) ->
    le (mult (slm_markov_kernel prefix w)
             (inv_pos (slm_markov_kernel prefix wstar) (req_markov_pos_slm prefix wstar)))
       (exp_neg (mult (inv_pos temperature temperature_pos)
                      (req_minus (total_loss (prefix ++ [w]))
                                 (total_loss (prefix ++ [wstar]))))).
Proof.
  intros prefix w wstar Hloss.
  assert (Hrel : req (slm_markov_kernel prefix w)
                     (mult (slm_markov_kernel prefix wstar)
                           (exp_neg (mult (inv_pos temperature temperature_pos)
                                          (req_minus (total_loss (prefix ++ [w]))
                                                     (total_loss (prefix ++ [wstar])))))))
    by exact (req_markov_relative prefix w wstar).
  set (A := slm_markov_kernel prefix w).
  set (B := slm_markov_kernel prefix wstar).
  set (C := exp_neg (mult (inv_pos temperature temperature_pos)
                          (req_minus (total_loss (prefix ++ [w]))
                                     (total_loss (prefix ++ [wstar]))))).
  assert (Hgc : le A (mult B C)).
  { unfold A, B, C. exact (reqd_le_of_req _ _ Hrel). }
  assert (Hinv : le zero (inv_pos B (req_markov_pos_slm prefix wstar))).
  { apply (lt_le_iff _ _). left. apply inv_pos_pos. }
  assert (Hdiv : le (mult (inv_pos B (req_markov_pos_slm prefix wstar)) A)
                    (mult (inv_pos B (req_markov_pos_slm prefix wstar)) (mult B C)))
    by exact (req_le_mult_compat_r _ _ _ Hinv Hgc).
  assert (Hsw : req (mult (inv_pos B (req_markov_pos_slm prefix wstar)) A)
                    (mult A (inv_pos B (req_markov_pos_slm prefix wstar))))
    by exact (mult_comm _ _).
  assert (Hswf : req (mult A (inv_pos B (req_markov_pos_slm prefix wstar)))
                     (mult (inv_pos B (req_markov_pos_slm prefix wstar)) A))
    by exact (req_sym (mult (inv_pos B (req_markov_pos_slm prefix wstar)) A)
                      (mult A (inv_pos B (req_markov_pos_slm prefix wstar))) Hsw).
  assert (Hlhs : le (mult A (inv_pos B (req_markov_pos_slm prefix wstar)))
                    (mult (inv_pos B (req_markov_pos_slm prefix wstar)) (mult B C)))
    by exact (le_id_l _ _ _ Hswf Hdiv).
  assert (Hrhs : req (mult (inv_pos B (req_markov_pos_slm prefix wstar)) (mult B C)) C).
  { exact (req_trans _ _ _
             (mult_assoc (inv_pos B (req_markov_pos_slm prefix wstar)) B C)
             (req_trans _ _ _
               (req_mult_compat _ _ _ _
                 (req_trans _ _ _ (mult_comm (inv_pos B (req_markov_pos_slm prefix wstar)) B)
                                 (inv_pos_correct B (req_markov_pos_slm prefix wstar)))
                 (req_refl C))
               (req_trans _ _ _ (mult_comm one C) (mult_one C)))). }
  assert (Hfin : le (mult A (inv_pos B (req_markov_pos_slm prefix wstar))) C)
    by exact (le_id_r _ _ _ Hrhs Hlhs).
  unfold A, B, C in Hfin. exact Hfin.
Qed.

(* ---- item 7: expected_loss_min_bound (relies on rls_ext / rls_linear and
   req_list_sum_le_on_list) ---- *)

Theorem req_expected_loss_min_bound :
  forall prefix wstar,
    (forall w : Token, InT w vocab ->
      le (total_loss (prefix ++ [wstar])) (total_loss (prefix ++ [w]))) ->
    le (total_loss (prefix ++ [wstar])) (slm_expected_loss prefix).
Proof.
  intros prefix wstar Hmin. unfold slm_expected_loss.
  assert (Hpt : forall w : Token, InT w vocab ->
    le (mult (slm_markov_kernel prefix w) (total_loss (prefix ++ [wstar])))
       (mult (slm_markov_kernel prefix w) (total_loss (prefix ++ [w])))).
  { intros w Hw.
    exact (req_le_mult_compat_r (slm_markov_kernel prefix w)
                                (total_loss (prefix ++ [wstar]))
                                (total_loss (prefix ++ [w]))
                                (lt_le_iff _ _ (inl (req_markov_pos_slm prefix w)))
                                (Hmin w Hw)). }
  assert (Hsum_le : le (rsum Token (fun w => mult (slm_markov_kernel prefix w)
                                                  (total_loss (prefix ++ [wstar]))) vocab)
                       (rsum Token (fun w => mult (slm_markov_kernel prefix w)
                                                  (total_loss (prefix ++ [w]))) vocab)).
  { apply req_list_sum_le_on_list. exact Hpt. }
  assert (Hlin : req (rsum Token (fun w => mult (slm_markov_kernel prefix w)
                                                (total_loss (prefix ++ [wstar]))) vocab)
                     (mult (total_loss (prefix ++ [wstar]))
                           (rsum Token (slm_markov_kernel prefix) vocab))).
  { assert (Hswap : req (rsum Token (fun w => mult (slm_markov_kernel prefix w)
                                                   (total_loss (prefix ++ [wstar]))) vocab)
                        (rsum Token (fun w => mult (total_loss (prefix ++ [wstar]))
                                                   (slm_markov_kernel prefix w)) vocab))
      by exact (rls_ext Token _ _ (fun w => mult_comm _ _) vocab).
    exact (req_trans _ _ _ Hswap
             (rls_linear Token (total_loss (prefix ++ [wstar])) (slm_markov_kernel prefix) vocab)). }
  assert (Hnorm : req (rsum Token (slm_markov_kernel prefix) vocab) one)
    by exact (req_markov_normalized prefix).
  assert (Hunit : req (mult (total_loss (prefix ++ [wstar]))
                            (rsum Token (slm_markov_kernel prefix) vocab))
                      (total_loss (prefix ++ [wstar]))).
  { exact (req_trans _ _ _
             (req_mult_compat _ _ _ _ (req_refl _) Hnorm)
             (mult_one _)). }
  exact (le_id_l _ _ _ (req_sym _ _ (req_trans _ _ _ Hlin Hunit)) Hsum_le).
Qed.

(* ---- item 8: markov_kernel_le_one (relies on rls_single_le) ---- *)

Theorem req_markov_kernel_le_one :
  forall prefix w, InT w vocab -> le (slm_markov_kernel prefix w) one.
Proof.
  intros prefix w Hin.
  assert (Hle : le (slm_markov_kernel prefix w)
                   (rsum Token (slm_markov_kernel prefix) vocab)).
  { exact (rls_single_le Token (slm_markov_kernel prefix) w vocab Hin
                         (fun w' => lt_le_iff _ _ (inl (req_markov_pos_slm prefix w')))). }
  exact (le_id_r _ _ _ (req_markov_normalized prefix) Hle).
Qed.



Context {RLL : ReqLogPlain}.

(* ---- definition block, continued: markov_entropy (the log positivity premise
   is inlined as markov_pos — a definition-level signature difference; the
   premise is provable, as the lemma below confirms) ---- *)

Definition slm_markov_entropy (prefix : list Token) : R :=
  rsum Token (fun w => mult (slm_markov_kernel prefix w)
                            (opp (log (slm_markov_kernel prefix w)
                                      (req_markov_pos_slm prefix w)))) vocab.

(* ---- item 11: markov_entropy_pointwise_nonneg (the [log_le_linear_plain]
   slot + an opp_minus chain + req_le_mult_compat_r) ---- *)

Lemma req_markov_entropy_pointwise_nonneg : forall prefix w,
  InT w vocab ->
  le zero (mult (slm_markov_kernel prefix w)
                (opp (log (slm_markov_kernel prefix w)
                          (req_markov_pos_slm prefix w)))).
Proof.
  intros prefix w Hin.
  assert (Hle1 : le (slm_markov_kernel prefix w) one)
    by exact (req_markov_kernel_le_one prefix w Hin).
  assert (Hmp : le zero (req_minus one (slm_markov_kernel prefix w)))
    by exact (req_le_minus_nonneg (slm_markov_kernel prefix w) one Hle1).
  (* le zero (one - P) gives le (P - one) zero (req_opp_minus + plus_comm + an opp chain) *)
  assert (Hopp : le (opp (req_minus one (slm_markov_kernel prefix w))) (opp zero))
    by exact (opp_le_compat _ _ Hmp).
  assert (Hflip : req (opp (req_minus one (slm_markov_kernel prefix w)))
                      (req_minus (slm_markov_kernel prefix w) one))
    by exact (req_trans _ _ _ (req_opp_minus _ _) (plus_comm _ _)).
  assert (Hmp' : le (req_minus (slm_markov_kernel prefix w) one) zero)
    by exact (le_id_l _ _ _ (req_sym _ _ Hflip) (le_id_r _ _ _ reqd_opp_zero Hopp)).
  (* log P <= P - 1 (the slot premise) and P - 1 <= 0 give log P <= 0, hence 0 <= -log P *)
  assert (Hlog : le (log (slm_markov_kernel prefix w) (req_markov_pos_slm prefix w))
                    (req_minus (slm_markov_kernel prefix w) one))
    by exact (log_le_linear_plain (slm_markov_kernel prefix w) (req_markov_pos_slm prefix w)).
  assert (Hlog0 : le (log (slm_markov_kernel prefix w) (req_markov_pos_slm prefix w)) zero)
    by exact (le_trans _ _ _ Hlog Hmp').
  assert (Hoppl : le zero (opp (log (slm_markov_kernel prefix w)
                                    (req_markov_pos_slm prefix w))))
    by exact (le_id_l zero (opp zero) _
             (req_sym (opp zero) zero reqd_opp_zero)
             (opp_le_compat _ _ Hlog0)).
  (* P*(-log P) >= 0 (strict positivity of P + req_le_mult_compat_r) *)
  assert (Hp_nonneg : le zero (slm_markov_kernel prefix w))
    by (apply (lt_le_iff _ _); left; apply req_markov_pos_slm).
  assert (Hprod0 : le (mult (slm_markov_kernel prefix w) zero)
                      (mult (slm_markov_kernel prefix w)
                            (opp (log (slm_markov_kernel prefix w)
                                      (req_markov_pos_slm prefix w)))))
    by exact (req_le_mult_compat_r _ _ _ Hp_nonneg Hoppl).
  exact (le_id_l zero _ _ (req_sym (mult (slm_markov_kernel prefix w) zero) zero
                             (mult_zero (slm_markov_kernel prefix w))) Hprod0).
Qed.

(* ---- item 12: markov_entropy_nonneg (the pointwise lemma lifted through the InT-restricted sum) ---- *)

Theorem req_markov_entropy_nonneg : forall prefix, le zero (slm_markov_entropy prefix).
Proof.
  intro prefix. unfold slm_markov_entropy.
  assert (Hle : le (rsum Token (fun _ : Token => zero) vocab)
                   (rsum Token (fun w => mult (slm_markov_kernel prefix w)
                             (opp (log (slm_markov_kernel prefix w)
                                       (req_markov_pos_slm prefix w)))) vocab)).
  { apply (req_list_sum_le_on_list vocab).
    intros w Hw. exact (req_markov_entropy_pointwise_nonneg prefix w Hw). }
  exact (le_id_l zero _ _ (req_sym _ _ (req_list_sum_zero_fn vocab)) Hle).
Qed.

(* ---- items 14/15/16: the softmax alias trio ---- *)

Definition slm_softmax (prefix : list Token) (w : Token) : R :=
  slm_markov_kernel prefix w.

Theorem req_softmax_pos : forall prefix w, lt zero (slm_softmax prefix w).
Proof.
  intros prefix w.
  unfold slm_softmax.
  apply req_markov_pos_slm.
Qed.

Theorem req_softmax_normalized : forall prefix,
  req (rsum Token (fun w => slm_softmax prefix w) vocab) one.
Proof.
  intro prefix.
  unfold slm_softmax.
  apply req_markov_normalized.
Qed.

Theorem req_softmax_bounded : forall prefix w,
  InT w vocab ->
  And (le zero (slm_softmax prefix w)) (le (slm_softmax prefix w) one).
Proof.
  intros prefix w Hin. split.
  - apply (lt_le_iff _ _). left. apply req_softmax_pos.
  - unfold slm_softmax. apply (req_markov_kernel_le_one prefix w Hin).
Qed.

(* ---- the greedy block (the argmin/list Id-layer machinery; its two top-level
   facts are declared as section slots here): their resolution is Part 3
   (req_pick_best_token / req_pick_best_token_optimal) ---- *)

Section ReqSLMGreedy.

Variable pick_best_token : list Token -> Token.
Hypothesis pick_best_in_vocab : forall prefix : list Token,
  InT (pick_best_token prefix) vocab.
Hypothesis pick_best_optimal : forall (prefix : list Token) (w : Token),
  InT w vocab ->
  le (total_loss (prefix ++ [pick_best_token prefix])) (total_loss (prefix ++ [w])).

(* ---- item 9: temperature_zero_exponential_bound (through the pick_best_in_vocab slot) ---- *)

Theorem req_temperature_zero_exponential_bound :
  forall (prefix : list Token) (w : Token),
    InT w vocab ->
    lt (total_loss (prefix ++ [pick_best_token prefix]))
       (total_loss (prefix ++ [w])) ->
    le (slm_markov_kernel prefix w)
       (exp_neg (mult (inv_pos temperature temperature_pos)
                      (req_minus (total_loss (prefix ++ [w]))
                                 (total_loss (prefix ++ [pick_best_token prefix]))))).
Proof.
  intros prefix w Hvocab Hlt.
  assert (Hrel : req (slm_markov_kernel prefix w)
                     (mult (slm_markov_kernel prefix (pick_best_token prefix))
                           (exp_neg (mult (inv_pos temperature temperature_pos)
                                          (req_minus (total_loss (prefix ++ [w]))
                                                     (total_loss (prefix ++ [pick_best_token prefix])))))))
    by exact (req_markov_relative prefix w (pick_best_token prefix)).
  assert (Hstar_le_one : le (slm_markov_kernel prefix (pick_best_token prefix)) one)
    by (apply req_markov_kernel_le_one; apply pick_best_in_vocab).
  set (E := exp_neg (mult (inv_pos temperature temperature_pos)
                          (req_minus (total_loss (prefix ++ [w]))
                                     (total_loss (prefix ++ [pick_best_token prefix]))))).
  assert (Hexp_nonneg : le zero E)
    by (unfold E; apply (lt_le_iff _ _); left; apply exp_neg_pos).
  assert (Hbound : le (mult (slm_markov_kernel prefix (pick_best_token prefix)) E) E).
  { assert (H1 : le (mult E (slm_markov_kernel prefix (pick_best_token prefix))) (mult E one))
      by exact (req_le_mult_compat_r E _ _ Hexp_nonneg Hstar_le_one).
    assert (H2 : le (mult (slm_markov_kernel prefix (pick_best_token prefix)) E)
                    (mult E (slm_markov_kernel prefix (pick_best_token prefix))))
      by exact (le_id_l _ _ _ (mult_comm _ _) (le_refl _)).
    exact (le_id_r _ _ _ (mult_one E) (le_trans _ _ _ H2 H1)). }
  exact (le_id_l _ _ _ Hrel Hbound).
Qed.

(* ---- item 13: greedy_kernel_limit (markov_temperature_zero_limit + the
   pick_best_optimal slot) ---- *)

Theorem req_greedy_kernel_limit :
  forall (prefix : list Token) (w : Token),
    InT w vocab ->
    le (mult (slm_markov_kernel prefix w)
             (inv_pos (slm_markov_kernel prefix (pick_best_token prefix))
                      (req_markov_pos_slm prefix (pick_best_token prefix))))
       (exp_neg (mult (inv_pos temperature temperature_pos)
                      (req_minus (total_loss (prefix ++ [w]))
                                 (total_loss (prefix ++ [pick_best_token prefix]))))).
Proof.
  intros prefix w Hw.
  apply (req_markov_temperature_zero_limit prefix w (pick_best_token prefix)).
  exact (pick_best_optimal prefix w Hw).
Qed.

(* ---- item 17: nonoptimal_probability_absolute (its Id-layer proof body is
   reproduced independently: unlike item 9 the statement carries no lt
   premise, so no exact-reuse applies) ---- *)

Theorem req_nonoptimal_probability_absolute :
  forall (prefix : list Token) (w : Token),
    InT w vocab ->
    le (slm_markov_kernel prefix w)
       (exp_neg (mult (inv_pos temperature temperature_pos)
                      (req_minus (total_loss (prefix ++ [w]))
                                 (total_loss (prefix ++ [pick_best_token prefix]))))).
Proof.
  intros prefix w Hw.
  set (E := exp_neg (mult (inv_pos temperature temperature_pos)
                          (req_minus (total_loss (prefix ++ [w]))
                                     (total_loss (prefix ++ [pick_best_token prefix]))))).
  assert (Hrel : req (slm_markov_kernel prefix w)
                     (mult (slm_markov_kernel prefix (pick_best_token prefix)) E))
    by (unfold E; exact (req_markov_relative prefix w (pick_best_token prefix))).
  assert (Hstar_le_one : le (slm_markov_kernel prefix (pick_best_token prefix)) one)
    by (apply req_markov_kernel_le_one; apply pick_best_in_vocab).
  assert (Hexp_nonneg : le zero E)
    by (unfold E; apply (lt_le_iff _ _); left; apply exp_neg_pos).
  assert (Hbound : le (mult (slm_markov_kernel prefix (pick_best_token prefix)) E) E).
  { assert (H1 : le (mult E (slm_markov_kernel prefix (pick_best_token prefix))) (mult E one))
      by exact (req_le_mult_compat_r E _ _ Hexp_nonneg Hstar_le_one).
    assert (H2 : le (mult (slm_markov_kernel prefix (pick_best_token prefix)) E)
                    (mult E (slm_markov_kernel prefix (pick_best_token prefix))))
      by exact (le_id_l _ _ _ (mult_comm _ _) (le_refl _)).
    exact (le_id_r _ _ _ (mult_one E) (le_trans _ _ _ H2 H1)). }
  exact (le_id_l _ _ _ Hrel Hbound).
Qed.

End ReqSLMGreedy.

End ReqSLM.

(* ===================================================================== *)
(* Part 2. The LogDiff3 tail section (13 statements carried over directly +
   2 with dependencies + 2 per-eta side lemmas): minus becomes req_minus (a
   definitional unfolding); log premises are made explicit; the Id-ring
   lemmas are replaced by the req proofs of [UpReqAlgebra]. *)
(* ===================================================================== *)
Section ReqLogDiff3.

Context {RLL : ReqLogPlain}.

(* ---- item 1: minus_one_plus_t (a ring chain) ---- *)

Lemma req_ld3_minus_one_plus_t : forall t : R, req (req_minus (plus one t) one) t.
Proof.
  intro t. unfold req_minus.
  assert (H1 : req (plus (plus one t) (opp one)) (plus one (plus t (opp one))))
    by exact (req_sym (plus one (plus t (opp one)))
                      (plus (plus one t) (opp one)) (plus_assoc one t (opp one))).
  assert (H2 : req (plus one (plus t (opp one))) (plus one (plus (opp one) t)))
    by exact (req_plus_compat one one (plus t (opp one)) (plus (opp one) t)
                             (req_refl one) (plus_comm t (opp one))).
  assert (H3 : req (plus one (plus (opp one) t)) (plus (plus one (opp one)) t))
    by exact (plus_assoc one (opp one) t).
  assert (H4 : req (plus (plus one (opp one)) t) (plus zero t))
    by exact (req_plus_compat (plus one (opp one)) zero t t
                              (plus_opp one) (req_refl t)).
  assert (H5 : req (plus zero t) t)
    by exact (req_trans _ _ _ (plus_comm zero t) (plus_zero t)).
  exact (req_trans _ _ _ H1 (req_trans _ _ _ H2 (req_trans _ _ _ H3 (req_trans _ _ _ H4 H5)))).
Qed.

(* ---- item 3: set_eq_le (one step through reqd_le_of_req of [UpReqDist]; the
   eq->le direction is derivable at the interface) ---- *)

Lemma req_set_eq_le : forall a b : R, req a b -> le a b.
Proof.
  intros a b H.
  exact (reqd_le_of_req a b H).
Qed.

(* ---- item 4: set_square_nonneg ---- *)

Lemma req_set_square_nonneg : forall t : R, le zero t -> le zero (mult t t).
Proof.
  intros t Ht.
  apply (le_trans _ (mult t zero) _).
  - exact (req_set_eq_le zero (mult t zero) (req_sym (mult t zero) zero (mult_zero t))).
  - exact (req_le_mult_compat_r t zero t Ht Ht).
Qed.

(* ---- item 5: set_cube_nonneg ---- *)

Lemma req_set_cube_nonneg : forall t : R, le zero t -> le zero (mult t (mult t t)).
Proof.
  intros t Ht.
  apply (le_trans _ (mult t zero) _).
  - exact (req_set_eq_le zero (mult t zero) (req_sym (mult t zero) zero (mult_zero t))).
  - exact (req_le_mult_compat_r t zero (mult t t) Ht (req_set_square_nonneg t Ht)).
Qed.

(* ---- item 6: set_minus_mult — relies on req_mult_minus_distr_l of
   [UpReqAlgebra] (referenced directly, no alias) ---- *)
(* ---- item 7: set_opp_zero — relies on reqd_opp_zero of [UpReqDist] ---- *)

(* ---- item 8: set_quad_cube (a fully explicit ring chain) ---- *)

Lemma req_set_quad_cube : forall t : R,
  req (plus (req_minus t (mult t t)) (req_minus (mult t t) (mult t (mult t t))))
      (req_minus t (mult t (mult t t))).
Proof.
  intro t. unfold req_minus.
  assert (H1 : req (plus (plus t (opp (mult t t)))
                         (plus (mult t t) (opp (mult t (mult t t)))))
                   (plus t (plus (opp (mult t t))
                                 (plus (mult t t) (opp (mult t (mult t t)))))))
    by exact (req_sym
                (plus t (plus (opp (mult t t))
                              (plus (mult t t) (opp (mult t (mult t t))))))
                (plus (plus t (opp (mult t t)))
                      (plus (mult t t) (opp (mult t (mult t t)))))
                (plus_assoc t (opp (mult t t))
                            (plus (mult t t) (opp (mult t (mult t t)))))).
  assert (H2 : req (plus t (plus (opp (mult t t)) (plus (mult t t) (opp (mult t (mult t t))))))
                   (plus t (plus (plus (opp (mult t t)) (mult t t))
                                 (opp (mult t (mult t t))))))
    by exact (req_plus_compat t t _ _
                             (req_refl t)
                             (plus_assoc (opp (mult t t)) (mult t t) (opp (mult t (mult t t))))).
  assert (Hopp_zero : req (plus (opp (mult t t)) (mult t t)) zero)
    by exact (req_trans _ _ _ (plus_comm (opp (mult t t)) (mult t t)) (plus_opp (mult t t))).
  assert (H3 : req (plus t (plus (plus (opp (mult t t)) (mult t t)) (opp (mult t (mult t t)))))
                   (plus t (plus zero (opp (mult t (mult t t))))))
    by exact (req_plus_compat t t _ _
                             (req_refl t)
                             (req_plus_compat _ _ _ _
                                              Hopp_zero
                                              (req_refl (opp (mult t (mult t t)))))).
  assert (H4 : req (plus t (plus zero (opp (mult t (mult t t)))))
                   (plus t (plus (opp (mult t (mult t t))) zero)))
    by exact (req_plus_compat t t _ _
                             (req_refl t)
                             (plus_comm zero (opp (mult t (mult t t))))).
  assert (H5 : req (plus t (plus (opp (mult t (mult t t))) zero))
                   (plus t (opp (mult t (mult t t)))))
    by exact (req_plus_compat t t _ _
                             (req_refl t)
                             (plus_zero (opp (mult t (mult t t))))).
  exact (req_trans _ _ _ H1 (req_trans _ _ _ H2 (req_trans _ _ _ H3 (req_trans _ _ _ H4 H5)))).
Qed.

(* ---- item 9: set_quad_prod (distrib + the dependency items + item 8) ---- *)

Lemma req_set_quad_prod : forall t : R,
  req (mult (req_minus t (mult t t)) (plus one t))
      (req_minus t (mult t (mult t t))).
Proof.
  intro t.
  assert (H1 : req (mult (req_minus t (mult t t)) (plus one t))
                   (plus (mult (req_minus t (mult t t)) one)
                         (mult (req_minus t (mult t t)) t)))
    by exact (distrib (req_minus t (mult t t)) one t).
  assert (H2b : req (mult (req_minus t (mult t t)) t)
                    (req_minus (mult t t) (mult t (mult t t))))
    by exact (req_trans _ _ _
              (mult_comm (req_minus t (mult t t)) t)
              (req_mult_minus_distr_l t t (mult t t))).
  assert (H2 : req (plus (mult (req_minus t (mult t t)) one)
                         (mult (req_minus t (mult t t)) t))
                   (plus (req_minus t (mult t t))
                         (req_minus (mult t t) (mult t (mult t t)))))
    by exact (req_plus_compat _ _ _ _
                             (mult_one (req_minus t (mult t t))) H2b).
  exact (req_trans _ _ _ H1 (req_trans _ _ _ H2 (req_set_quad_cube t))).
Qed.

(* ---- item 10: set_minus_cube_le (relies on reqd_opp_zero) ---- *)

Lemma req_set_minus_cube_le : forall t : R, le zero t ->
  le (req_minus t (mult t (mult t t))) t.
Proof.
  intros t Ht. unfold req_minus.
  apply (le_trans _ (plus t zero) _).
  - apply (le_plus_compat t t (opp (mult t (mult t t))) zero).
    + apply le_refl.
    + apply (le_id_r _ _ _ reqd_opp_zero).
      exact (opp_le_compat zero (mult t (mult t t)) (req_set_cube_nonneg t Ht)).
  - exact (req_set_eq_le (plus t zero) t (plus_zero t)).
Qed.

(* ---- item 11: set_one_plus_pos ---- *)

Lemma req_set_one_plus_pos : forall t : R, le zero t -> lt zero (plus one t).
Proof.
  intros t Ht0.
  apply (lt_le_trans zero one (plus one t)).
  - exact one_pos.
  - apply (le_id_l _ _ _ (req_sym (plus one zero) one (plus_zero one))).
    exact (le_plus_compat one one zero t (le_refl one) Ht0).
Qed.

(* ---- item 12: set_inv_mul ---- *)

Lemma req_set_inv_mul : forall (s : R) (Hs : lt zero s),
  req (mult (inv_pos s Hs) s) one.
Proof.
  intros s Hs.
  exact (req_trans _ _ _ (mult_comm (inv_pos s Hs) s) (inv_pos_correct s Hs)).
Qed.

(* ---- item 13: set_div_linear_ge_quad ---- *)

Lemma req_set_div_linear_ge_quad : forall (t : R) (Ht0 : le zero t)
                                          (Hs : lt zero (plus one t)),
  le (req_minus t (mult t t)) (mult t (inv_pos (plus one t) Hs)).
Proof.
  intros t Ht0 Hs.
  set (s := plus one t) in *.
  assert (Hcore : le (mult (req_minus t (mult t t)) s) t).
  { apply (le_trans _ (req_minus t (mult t (mult t t))) _).
    - exact (req_set_eq_le (mult (req_minus t (mult t t)) s)
                           (req_minus t (mult t (mult t t)))
                           (req_set_quad_prod t)).
    - exact (req_set_minus_cube_le t Ht0). }
  apply (le_trans _ (mult (mult (req_minus t (mult t t)) s) (inv_pos s Hs)) _).
  - apply req_set_eq_le.
    exact (req_trans _ _ _
             (req_sym (mult (req_minus t (mult t t)) one)
                      (req_minus t (mult t t))
                      (mult_one (req_minus t (mult t t))))
             (req_trans _ _ _
               (req_mult_compat (req_minus t (mult t t)) (req_minus t (mult t t))
                                one (mult s (inv_pos s Hs))
                                (req_refl (req_minus t (mult t t)))
                                (req_sym (mult s (inv_pos s Hs)) one
                                         (inv_pos_correct s Hs)))
               (mult_assoc (req_minus t (mult t t)) s (inv_pos s Hs)))).
  - exact (le_mult_compat (mult (req_minus t (mult t t)) s) t (inv_pos s Hs)
                          (inv_pos_pos s Hs) Hcore).
Qed.

(* ---- item 14: set_inv_minus_one_opp (a req_opp_minus-shaped restatement) ---- *)

Lemma req_set_inv_minus_one_opp : forall (t : R) (Hs : lt zero (plus one t)),
  req (mult t (inv_pos (plus one t) Hs))
      (opp (req_minus (inv_pos (plus one t) Hs) one)).
Proof.
  intros t Hs.
  set (s := plus one t) in *.
  assert (H1 : req (mult t (inv_pos s Hs)) (mult (req_minus s one) (inv_pos s Hs))).
  { apply (req_mult_compat t (req_minus s one) (inv_pos s Hs) (inv_pos s Hs)).
    - exact (req_sym (req_minus s one) t (req_ld3_minus_one_plus_t t)).
    - apply req_refl. }
  assert (H2 : req (mult (req_minus s one) (inv_pos s Hs))
                   (mult (inv_pos s Hs) (req_minus s one)))
    by exact (mult_comm _ _).
  assert (H3 : req (mult (inv_pos s Hs) (req_minus s one))
                   (req_minus (mult (inv_pos s Hs) s) (mult (inv_pos s Hs) one)))
    by exact (req_mult_minus_distr_l (inv_pos s Hs) s one).
  assert (H4 : req (req_minus (mult (inv_pos s Hs) s) (mult (inv_pos s Hs) one))
                   (req_minus one (mult (inv_pos s Hs) one))).
  { apply (req_plus_compat _ _ _ _).
    - exact (req_set_inv_mul s Hs).
    - apply req_refl. }
  assert (H5 : req (req_minus one (mult (inv_pos s Hs) one))
                   (req_minus one (inv_pos s Hs))).
  { apply (req_plus_compat _ _ _ _).
    - apply req_refl.
    - exact (req_opp_compat (mult (inv_pos s Hs) one) (inv_pos s Hs)
                            (mult_one (inv_pos s Hs))). }
  assert (H6 : req (req_minus one (inv_pos s Hs))
                   (opp (req_minus (inv_pos s Hs) one))).
  { apply (req_sym (opp (req_minus (inv_pos s Hs) one)) (plus one (opp (inv_pos s Hs)))).
    exact (req_trans _ _ _
              (req_opp_minus (inv_pos s Hs) one)
              (plus_comm (opp (inv_pos s Hs)) one)). }
  exact (req_trans _ _ _ H1 (req_trans _ _ _ H2 (req_trans _ _ _ H3
         (req_trans _ _ _ H4 (req_trans _ _ _ H5 H6))))).
Qed.

(* ---- item 2: log_one_plus_le (the main route through the assumption slot) ---- *)

Lemma req_log_one_plus_le : forall (t : R) (Hpos : lt zero (plus one t)),
  le (log (plus one t) Hpos) t.
Proof.
  intros t Hpos.
  apply (le_trans _ (req_minus (plus one t) one) _).
  - exact (log_le_linear_plain (plus one t) Hpos).
  - exact (lt_le_iff _ _ (inr (req_ld3_minus_one_plus_t t))).
Qed.

(* ---- item 2, Bishop per-eta side form (proved outright with no slots, straight from log_le_linear_eps) ---- *)

Lemma req_log_one_plus_le_eps : forall (t : R) (Hpos : lt zero (plus one t)) (eta : R),
  lt zero eta -> le (log (plus one t) Hpos) (plus t eta).
Proof.
  intros t Hpos eta Heta.
  exact (le_id_r _ _ _           (req_plus_compat (plus (plus one t) (opp one)) t eta eta                            (req_ld3_minus_one_plus_t t) (req_refl eta))           (log_le_linear_eps (plus one t) Hpos eta Heta)).
Qed.

(* ---- item 15: log_one_plus_ge (the main route through the assumption slot; chain = item 13 + item 14 + ...) ---- *)


Lemma req_log_one_plus_ge : forall (t : R), le zero t ->
  forall (Hs : lt zero (plus one t)),
  le (req_minus t (mult t t)) (log (plus one t) Hs).
Proof.
  intros t Ht0 Hs.
  set (s := plus one t) in *.
  pose proof (req_set_div_linear_ge_quad t Ht0 Hs) as Hseg1.
  pose proof (req_set_inv_minus_one_opp t Hs) as Hio.
  pose proof (log_le_linear_plain (inv_pos s Hs) (inv_pos_pos s Hs)) as Hlin.
  pose proof (opp_le_compat (log (inv_pos s Hs) (inv_pos_pos s Hs))
                            (req_minus (inv_pos s Hs) one) Hlin) as Hoc.
  pose proof (le_id_l (mult t (inv_pos s Hs))
                      (opp (req_minus (inv_pos s Hs) one))
                      (opp (log (inv_pos s Hs) (inv_pos_pos s Hs)))
                      Hio Hoc) as Hseg2a.
  assert (Ho2 : req (opp (log (inv_pos s Hs) (inv_pos_pos s Hs))) (log s Hs)).
  { exact (req_trans _ _ _
             (req_opp_compat (log (inv_pos s Hs) (inv_pos_pos s Hs))
                             (opp (log s Hs))
                             (req_log_inv_one_inv log_req_compat_plain s Hs))
             (req_double_neg (log s Hs))). }
  pose proof (le_id_r (mult t (inv_pos s Hs))
                      (opp (log (inv_pos s Hs) (inv_pos_pos s Hs)))
                      (log s Hs) Ho2 Hseg2a) as Hseg2.
  apply (le_trans _ (mult t (inv_pos s Hs)) _).
  - exact Hseg1.
  - exact Hseg2.
Qed.

(* ---- item 15, Bishop per-eta side form (proved outright with no slots): the
   two conjuncts of the opp chain around Hoc are restated (the
   req_opp_plus / req_opp_minus / Hio duality) and the tail folds by
   req_minus_plus_cancel. The whole chain relies on log_le_linear_eps,
   with zero slot dependencies ---- *)

Lemma req_log_one_plus_ge_eps : forall (t : R), le zero t ->
  forall (Hs : lt zero (plus one t)) (eta : R), lt zero eta ->
  le (req_minus t (mult t t)) (plus (log (plus one t) Hs) eta).
Proof.
  intros t Ht0 Hs eta Heta.
  set (s := plus one t) in *.
  set (invs := inv_pos s Hs).
  pose proof (req_set_div_linear_ge_quad t Ht0 Hs) as Hseg1.
  pose proof (req_set_inv_minus_one_opp t Hs) as Hio.
  pose proof (log_le_linear_eps invs (inv_pos_pos s Hs) eta Heta) as Heps.
  pose proof (opp_le_compat (log invs (inv_pos_pos s Hs))
                            (plus (req_minus invs one) eta) Heps) as Hoc.
  (* conjunct A: opp (invs - 1) == one - invs == t*invs (req_opp_minus + the dual restatement) *)
  assert (Hone_minus : req (plus one (opp invs)) (mult t invs)).
  { apply (req_trans _ (opp (req_minus invs one))).
    - apply (req_trans _ (plus (opp invs) (opp (opp one)))).
      + apply (req_trans _ (plus (opp invs) one)).
        * apply plus_comm.
        * apply (req_plus_compat (opp invs) (opp invs) one (opp (opp one))
                                 (req_refl (opp invs))
                                 (req_sym (opp (opp one)) one (req_double_neg one))).
      + exact (req_sym (opp (plus invs (opp one)))
                       (plus (opp invs) (opp (opp one)))
                       (req_opp_plus invs (opp one))).
    - exact (req_sym (mult t invs) (opp (req_minus invs one)) Hio). }
  assert (HLflip : req (opp (plus (req_minus invs one) eta))
                      (req_minus (mult t invs) eta)).
  { apply (req_trans _ (plus (opp (req_minus invs one)) (opp eta))).
    - apply req_opp_plus.
    - apply (req_trans _ (plus (plus one (opp invs)) (opp eta))).
      + apply (req_plus_compat _ _ _ _
                 (req_trans _ _ _
                    (req_opp_minus invs one) (plus_comm (opp invs) one))
                 (req_refl (opp eta))).
      + apply (req_plus_compat (plus one (opp invs)) (mult t invs) (opp eta) (opp eta)
                               Hone_minus (req_refl (opp eta))). }
  
  assert (Ho2 : req (opp (log invs (inv_pos_pos s Hs))) (log s Hs)).
  { exact (req_trans _ _ _
             (req_opp_compat (log invs (inv_pos_pos s Hs)) (opp (log s Hs))
                             (req_log_inv_one_inv log_req_compat_plain s Hs))
             (req_double_neg (log s Hs))). }
  assert (Hoc' : le (req_minus (mult t invs) eta) (log s Hs)).
  { exact (le_id_r _ _ _ Ho2
             (le_id_l _ _ _
                (req_sym (opp (plus (req_minus invs one) eta))
                         (req_minus (mult t invs) eta) HLflip)
                Hoc)). }
  (* t - t*t - eta <= log s gives t - t*t <= log s + eta *)
  assert (Hdiff : le (req_minus (req_minus t (mult t t)) eta) (log s Hs)).
  { apply (le_trans _ (req_minus (mult t invs) eta)).
    - exact (le_plus_compat (req_minus t (mult t t))
                            (mult t (inv_pos (plus one t) Hs))
                            (opp eta) (opp eta)
                            Hseg1 (le_refl (opp eta))).
    - exact Hoc'. }
  exact (le_id_l (req_minus t (mult t t))
                 (plus (req_minus (req_minus t (mult t t)) eta) eta)
                 (plus (log s Hs) eta)
                 (req_sym (plus (req_minus (req_minus t (mult t t)) eta) eta)
                          (req_minus t (mult t t))
                          (req_trans _ _ _
                             (plus_comm (req_minus (req_minus t (mult t t)) eta) eta)
                             (req_minus_plus_cancel eta (req_minus t (mult t t)))))
                 (le_plus_compat (req_minus (req_minus t (mult t t)) eta)
                                 (log s Hs) eta eta
                                 Hdiff (le_refl eta))).
Qed.

End ReqLogDiff3.

(* ===================================================================== *)
(* Part 3. Resolving the two slots of [ReqSLMGreedy] (the declared premises theoremized) *)

(*   The closure signature of req_pick_best_token / req_pick_best_token_optimal
   is {R}{RIS}{DO} Token vocab total_loss default_token prefix w.
   Slot faces: the two slots of [ReqSLMGreedy] are
     optimal  : forall prefix w, InT w vocab ->
                le (total_loss (prefix++[pick prefix]))
                   (total_loss (prefix++[w]))
     in_vocab : forall prefix, InT (pick prefix) vocab
   The optimal face matches the statement of req_pick_best_token_optimal
   one-to-one and resolves directly; the in_vocab face has no machine-layer
   counterpart usable here, so this section proves it by induction on the req
   side (slm_discharge_aux_acc, the same helper-proved-not-restated pattern as
   req_list_sum_le_on_list). With both slots resolved, the three dependent
   statements are upgraded to slot-free theorems (the _noslot forms).
   Honest signature difference: the slot-free statements carry two extra
   closure binders, DO : reqDecidableOrder and default_token : Token; DO stays
   a permanently declared class premise (the LPO-flavored conclusion rides
   with the bridge; the library declares no Instance for it, and the class
   premise enters the closure signature at End with Print Assumptions
   Closed). *)
(* ===================================================================== *)
Section ReqSLMGreedyDischarge.

Context {DO : reqDecidableOrder}.

Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.
Variable default_token : Token.

(* ---- in-section shorthands (the ReqSLM closure statements fed with all arguments) ---- *)

Definition k_d (prefix : list Token) (w : Token) : R :=
  slm_markov_kernel Token vocab vocab_nonempty total_loss temperature
    temperature_pos prefix w.

Definition pos_d (prefix : list Token) (w : Token) : lt zero (k_d prefix w) :=
  req_markov_pos_slm Token vocab vocab_nonempty total_loss temperature
    temperature_pos prefix w.

(* ---- the greedy selection (instantiating req_pick_best_token; slot-free) ---- *)

Definition slm_discharge_pick_in (prefix : list Token) : Token :=
  req_pick_best_token Token vocab total_loss default_token prefix.

(* ---- resolving the in_vocab slot, preparation: induction over the argmin
   traversal (proved on the req side). Invariant: after traversing l, the
   fst result lands in any superset super of btk :: l; by induction + the
   two branches of rord_le_dec + inversion on InT (with the three names
   bound explicitly, since too-few binder names get swallowed by subst)
   ---- *)

Lemma slm_discharge_aux_acc :
  forall (prefix : list Token) (l : list Token) (btk : Token) (bls : R),
    forall super : list Token,
      (forall w : Token, InT w (btk :: l) -> InT w super) ->
      InT (fst (req_argmin_aux_token Token total_loss prefix l (btk, bls)))
          super.
Proof.
  intros prefix l. induction l as [| a rest IH]; intros btk bls super Hsuper.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply Hsuper. apply InT_here.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
    assert (Hmem : forall w : Token,
              InT w (a :: rest) -> InT w (btk :: a :: rest)).
    { intros w Hw. exact (InT_next w btk (a :: rest) Hw). }
    destruct (rord_le_dec (total_loss (prefix ++ [a])) bls) as [Hle | Hnot].
    + apply (IH a (total_loss (prefix ++ [a])) super).
      intros w Hw. apply Hsuper. exact (Hmem w Hw).
    + assert (Hmem2 : forall w : Token,
                InT w (btk :: rest) -> InT w (btk :: a :: rest)).
      { intros w Hw. inversion Hw as [Hw_here | y l0 Hw']; subst.
        - exact (InT_here _ (a :: rest)).
        - exact (InT_next w btk (a :: rest) (InT_next w a rest Hw')). }
      apply (IH btk bls super).
      intros w Hw. apply Hsuper. exact (Hmem2 w Hw).
Qed.

(* ---- resolving the in_vocab slot (the counterpart of pick_best_in_vocab) ---- *)

Lemma slm_discharge_pick_in_vocab :
  forall prefix : list Token, InT (slm_discharge_pick_in prefix) vocab.
Proof.
  intro prefix. unfold slm_discharge_pick_in, req_pick_best_token.
  destruct vocab as [| w0 rest].
  - destruct (vocab_nonempty id_refl).
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
    exact (slm_discharge_aux_acc prefix rest w0
             (total_loss (prefix ++ [w0])) (w0 :: rest)
             (fun w Hw => Hw)).
Qed.

(* ---- resolving the optimal slot (the counterpart of pick_best_optimal; one-to-one reliance) ---- *)

Lemma slm_discharge_pick_optimal :
  forall (prefix : list Token) (w : Token),
    InT w vocab ->
    le (total_loss (prefix ++ [slm_discharge_pick_in prefix]))
       (total_loss (prefix ++ [w])).
Proof.
  intros prefix w Hw.
  unfold slm_discharge_pick_in.
  exact (req_pick_best_token_optimal Token vocab total_loss default_token          prefix w Hw).
Qed.

(* ---- slot-free statement 1: req_greedy_kernel_limit upgraded (its slot dependency now proved) ---- *)

Theorem req_greedy_kernel_limit_noslot :
  forall (prefix : list Token) (w : Token),
    InT w vocab ->
    le (mult (k_d prefix w)
             (inv_pos (k_d prefix (slm_discharge_pick_in prefix))
                      (pos_d prefix (slm_discharge_pick_in prefix))))
       (exp_neg (mult (inv_pos temperature temperature_pos)
                      (req_minus (total_loss (prefix ++ [w]))
                                 (total_loss (prefix ++
                                    [slm_discharge_pick_in prefix]))))).
Proof.
  intros prefix w Hw.
  apply (req_markov_temperature_zero_limit Token vocab vocab_nonempty           total_loss temperature temperature_pos           prefix w (slm_discharge_pick_in prefix)).
  exact (slm_discharge_pick_optimal prefix w Hw).
Qed.

(* ---- slot-free statement 2: temperature_zero_exponential_bound upgraded ---- *)

Theorem req_temperature_zero_exponential_bound_noslot :
  forall (prefix : list Token) (w : Token),
    InT w vocab ->
    lt (total_loss (prefix ++ [slm_discharge_pick_in prefix]))
       (total_loss (prefix ++ [w])) ->
    le (k_d prefix w)
       (exp_neg (mult (inv_pos temperature temperature_pos)
                      (req_minus (total_loss (prefix ++ [w]))
                                 (total_loss (prefix ++
                                    [slm_discharge_pick_in prefix]))))).
Proof.
  intros prefix w Hvocab Hlt.
  assert (Hrel : req (k_d prefix w)
                     (mult (k_d prefix (slm_discharge_pick_in prefix))
                           (exp_neg (mult (inv_pos temperature temperature_pos)
                                          (req_minus (total_loss (prefix ++ [w]))
                                                     (total_loss (prefix ++
                                                        [slm_discharge_pick_in prefix])))))))
    by exact (req_markov_relative Token vocab vocab_nonempty total_loss
                temperature temperature_pos prefix w
                (slm_discharge_pick_in prefix)).
  assert (Hstar_le_one : le (k_d prefix (slm_discharge_pick_in prefix)) one)
    by exact (req_markov_kernel_le_one Token vocab vocab_nonempty total_loss
                temperature temperature_pos prefix
                (slm_discharge_pick_in prefix)
                (slm_discharge_pick_in_vocab prefix)).
  set (E := exp_neg (mult (inv_pos temperature temperature_pos)
                          (req_minus (total_loss (prefix ++ [w]))
                                     (total_loss (prefix ++
                                        [slm_discharge_pick_in prefix]))))).
  assert (Hexp_nonneg : le zero E)
    by (unfold E; apply (lt_le_iff _ _); left; apply exp_neg_pos).
  assert (Hbound : le (mult (k_d prefix (slm_discharge_pick_in prefix)) E) E).
  { assert (H1 : le (mult E (k_d prefix (slm_discharge_pick_in prefix)))
                    (mult E one))
      by exact (req_le_mult_compat_r E _ _ Hexp_nonneg Hstar_le_one).
    assert (H2 : le (mult (k_d prefix (slm_discharge_pick_in prefix)) E)
                    (mult E (k_d prefix (slm_discharge_pick_in prefix))))
      by exact (le_id_l _ _ _ (mult_comm _ _) (le_refl _)).
    exact (le_id_r _ _ _ (mult_one E) (le_trans _ _ _ H2 H1)). }
  exact (le_id_l _ _ _ Hrel Hbound).
Qed.

(* ---- slot-free statement 3: nonoptimal_probability_absolute upgraded ---- *)

Theorem req_nonoptimal_probability_absolute_noslot :
  forall (prefix : list Token) (w : Token),
    InT w vocab ->
    le (k_d prefix w)
       (exp_neg (mult (inv_pos temperature temperature_pos)
                      (req_minus (total_loss (prefix ++ [w]))
                                 (total_loss (prefix ++
                                    [slm_discharge_pick_in prefix]))))).
Proof.
  intros prefix w Hw.
  set (E := exp_neg (mult (inv_pos temperature temperature_pos)
                          (req_minus (total_loss (prefix ++ [w]))
                                     (total_loss (prefix ++
                                        [slm_discharge_pick_in prefix]))))).
  assert (Hrel : req (k_d prefix w)
                     (mult (k_d prefix (slm_discharge_pick_in prefix)) E))
    by (unfold E;
        exact (req_markov_relative Token vocab vocab_nonempty total_loss
                 temperature temperature_pos prefix w
                 (slm_discharge_pick_in prefix))).
  assert (Hstar_le_one : le (k_d prefix (slm_discharge_pick_in prefix)) one)
    by exact (req_markov_kernel_le_one Token vocab vocab_nonempty total_loss
                temperature temperature_pos prefix
                (slm_discharge_pick_in prefix)
                (slm_discharge_pick_in_vocab prefix)).
  assert (Hexp_nonneg : le zero E)
    by (unfold E; apply (lt_le_iff _ _); left; apply exp_neg_pos).
  assert (Hbound : le (mult (k_d prefix (slm_discharge_pick_in prefix)) E) E).
  { assert (H1 : le (mult E (k_d prefix (slm_discharge_pick_in prefix)))
                    (mult E one))
      by exact (req_le_mult_compat_r E _ _ Hexp_nonneg Hstar_le_one).
    assert (H2 : le (mult (k_d prefix (slm_discharge_pick_in prefix)) E)
                    (mult E (k_d prefix (slm_discharge_pick_in prefix))))
      by exact (le_id_l _ _ _ (mult_comm _ _) (le_refl _)).
    exact (le_id_r _ _ _ (mult_one E) (le_trans _ _ _ H2 H1)). }
  exact (le_id_l _ _ _ Hrel Hbound).
Qed.

End ReqSLMGreedyDischarge.

(* ===================================================================== *)
(* File tail: machine-layer facts and notes on the explicit premise slots (no proof lines here) *)
(* --------------------------------------------------------------------- *)
(* Machine-layer statements not carried over (nat/list Id layer; they stay in
   the backbone): five statements of the SLM block — InT_head_extend /
   argmin_aux_token_mem / argmin_aux_token_snd_correct (the Leibniz correctness
   companion) / pick_best_in_vocab' / pick_best_in_vocab (the alias).
   req_temperature_zero_exponential_bound and
   req_nonoptimal_probability_absolute of this file depend on those top-level
   facts through the pick_best_in_vocab slot: the machine layer is required as
   is, and the conclusions are assembled on the req layer. *)
(* The decidable-order explicit premise classes (reqDecidableOrder + reqArgmin):
   two statements of the SLM block — argmin_aux_token_min / pick_best_optimal —
   have purely le statements and map one-to-one to req; their proof machine is
   ord_le_dec induction (a decidable total order is LPO-equivalent, and the
   library declares no Instance, so the req side keeps a permanently declared
   class premise isomorphic to the Id form). Both slots are resolved by Part 3
   (optimal relies one-to-one on req_pick_best_token_optimal; in_vocab is
   proved by induction on the req side), and the three dependent statements
   are upgraded to the slot-free _noslot theorems. The ReqSLMGreedy slot
   section of this file is the interface declaration face; consumers should
   rely on the slot-free statements of Part 3. *)
(* ===================================================================== *)
