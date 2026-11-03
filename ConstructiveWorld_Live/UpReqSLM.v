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
      the log slots [log_le_zero_slot]/[log_req_compat_plain] remain explicit.

    Build.  [coqc -native-compiler no -q -Q . "" UpReqSLM.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

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
(* Pool-build cure (seat_abl19, M43 nw10cure per UpReqAlign3.v/G09_MiscSmall.v
   precedent): the interface class in this tree is unparameterized
   (S07_RealSetoidExpLog.v:8075 zero-argument Class RealInterfaceEnhancedSetoid +
   global Instance RealEnhancedReal); the argument-bearing generation binders
   the argument-bearing generation binders Context {R : Set}
   {RIS : RealInterfaceEnhancedSetoid R}. are deleted, the carrier R is bound to
   the global Real by the file-top Notation below, and the two carrier-bearing
   premise classes ReqNonnegPlain/ReqLogPlain and
   reqDecidableOrder are re-anchored zero-argument (pool zero-arg
   Class reqDecidableOrder at G09_MiscSmall.v:897). Zero Obj.magic, zero Prop
   casts, statement faces preserved verbatim. *)
Notation R := Real.

(* ===================================================================== *)

(* ===================================================================== *)

(* plain 非负假设位组（T2①；Real 消解显式假设见头注波 0 核对） *)
Class ReqNonnegPlain := {
  abs_nonneg_plain : forall a : R, le zero (abs a);
  metric_pos_plain : forall a b : R, le zero (metric a b)
}.

(* log 族假设位组（gibbs_inequality 同参数位家族）：
   log_le_linear_plain（Id log_le_linear 字段逐位副本）+ log_req_compat_plain
   （UpReqAlgebra ReqLogBridge log_req_compat 参数位同构 L1492——req_log_inv_one_inv
   依存所需；LogDiff3 下界件必需） *)
Class ReqLogPlain := {
  log_le_linear_plain : forall (x : R) (Hx : lt zero x),
    le (log x Hx) (req_minus x one);
  log_req_compat_plain : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy)
}.

(* 清单「按需假设位」实测可字段链真证——定理化（假设位省一枚） *)
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
(* Part 1：reqSLM 定义块 + SLM 17(b)（清单 §3 逐件）                            *)
(* ===================================================================== *)
Section ReqSLM.


Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable total_loss : list Token -> R.   (* 序列损失（prefix ++ [w] 的损失） *)
Variable temperature : R.
Variable temperature_pos : lt zero temperature.

(* ---- 定义块（清单 §3：alb_temp_factor/list_sum/alb_partition_temp/alb_markov_kernel/ *)
(*        expected_loss/markov_entropy/softmax 全部 exp_neg/inv_pos 表出；       *)
(*        carrier rsum@RestB L126 逐字同构 list_sum） --------------------------- *)

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

(* ---- 件 2：list_sum_add（L2097，list 归纳 rls_* 同模板） -------------------- *)

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

(* ---- 件 10：list_sum_zero_fn（L2705） ------------------------------------- *)

Lemma req_list_sum_zero_fn : forall l : list Token,
  req (rsum Token (fun _ : Token => zero) l) zero.
Proof.
  intro l. induction l as [| w rest IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - apply req_refl.
  - exact (req_trans _ _ _ (plus_comm zero (rsum Token (fun _ : Token => zero) rest))
             (req_trans _ _ _ (plus_zero (rsum Token (fun _ : Token => zero) rest)) IH)).
Qed.

(* ---- 辅件：list_sum_le_on_list 的 InT 限制形（对位 rls_le@RestB L210 前提形  *)
(*        差异——见头注核对；6 行归纳真证，rls_le 本体不重证） ------------------- *)

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

(* ---- 件 1：temp_factor_antitone（L2060：exp_neg_le_decr + req_le_mult_     *)
(*        compat_r + inv_pos 位） -------------------------------------------- *)

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

(* ---- 件 3：markov_kernel_antitone（L2147：件 1 + 共同 inv 序链） ------------- *)

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

(* ---- (a) 让步件：markov_pos（L2184；对位 req_markov_pos@RestB L477 闭在      *)
(*        Min-P 域节内不可实例化——3 行同语句真证，见头注核对） ------------------ *)

Lemma req_markov_pos_slm : forall prefix w, lt zero (slm_markov_kernel prefix w).
Proof.
  intros prefix w. unfold slm_markov_kernel. apply mult_positive.
  - unfold slm_temp_factor. apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* ---- 件 4：markov_normalized（L2193；rls_kernel_norm_gen@RestB L224 实例化） -- *)

Theorem req_markov_normalized : forall prefix,
  req (rsum Token (fun w => slm_markov_kernel prefix w) vocab) one.
Proof.
  intro prefix.
  exact (rls_kernel_norm_gen Token vocab (fun _ : Token => True) (fun _ : Token => inl I)                             (slm_temp_factor prefix) (slm_partition_temp_pos prefix)).
Qed.

(* ---- 件 5：markov_relative（L2216，SLM 区最大 (b) 件；exp_neg 同余依存        *)
(*        req_exp_neg_ext_local@RestB L1354） -------------------------------- *)

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
  (* 重组：mult (mult A C) B == mult (mult A B) C *)
  assert (Hre : req (mult (mult A C) B) (mult (mult A B) C)).
  { exact (req_trans _ _ _
             (req_sym (mult A (mult C B)) (mult (mult A C) B) (mult_assoc A C B))
             (req_trans _ _ _
               (req_mult_compat A A (mult C B) (mult B C) (req_refl A) (mult_comm C B))
               (mult_assoc A B C))). }
  (* 指数相加：A·B == Ap（exp_neg_plus + distrib + minus 消去链） *)
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
  (* 组装：mult Ap C == mult (mult A C) B *)
  assert (Hmid : req (mult (mult A B) C) (mult Ap C))
    by exact (req_mult_compat (mult A B) Ap C C Hprod (req_refl C)).
  exact (req_sym (mult (mult A C) B) (mult Ap C) (req_trans _ _ _ Hre Hmid)).
Qed.

(* ---- 件 6：markov_temperature_zero_limit（L2277：件 5 + inv 消去链） --------- *)

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

(* ---- 件 7：expected_loss_min_bound（L2356；rls_ext/rls_linear (a) 依存 +      *)
(*        req_list_sum_le_on_list） ------------------------------------------ *)

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

(* ---- 件 8：markov_kernel_le_one（L2611；rls_single_le (a) 依存） -------------- *)

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

(* ---- 定义块续：markov_entropy（log 前提位 markov_pos 内联——定义级签名差异     *)
(*        登记表 2；清单「前提位 provable」结论实证） --------------------------- *)

Definition slm_markov_entropy (prefix : list Token) : R :=
  rsum Token (fun w => mult (slm_markov_kernel prefix w)
                            (opp (log (slm_markov_kernel prefix w)
                                      (req_markov_pos_slm prefix w)))) vocab.

(* ---- 件 11：markov_entropy_pointwise_nonneg（L2715，(b)+假设位：              *)
(*        log_le_linear_plain 参数位 + opp_minus 链 + req_le_mult_compat_r） ------- *)

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
  (* le zero (one − P) ⟹ le (P − one) zero（req_opp_minus + plus_comm + opp 链） *)
  assert (Hopp : le (opp (req_minus one (slm_markov_kernel prefix w))) (opp zero))
    by exact (opp_le_compat _ _ Hmp).
  assert (Hflip : req (opp (req_minus one (slm_markov_kernel prefix w)))
                      (req_minus (slm_markov_kernel prefix w) one))
    by exact (req_trans _ _ _ (req_opp_minus _ _) (plus_comm _ _)).
  assert (Hmp' : le (req_minus (slm_markov_kernel prefix w) one) zero)
    by exact (le_id_l _ _ _ (req_sym _ _ Hflip) (le_id_r _ _ _ reqd_opp_zero Hopp)).
  (* log P ≤ P − 1（参数位）且 P − 1 ≤ 0 ⟹ log P ≤ 0 ⟹ 0 ≤ −log P *)
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
  (* P·(−log P) ≥ 0（P > 0 严格位 + req_le_mult_compat_r） *)
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

(* ---- 件 12：markov_entropy_nonneg（L2791：点态 + InT 限制和提升） ------------- *)

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

(* ---- 件 14/15/16：softmax 别名三件（L2856/L2862/L2869） --------------------- *)

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

(* ---- 贪心域（argmin/list Id 机器域；两顶层事实以参数位申报）：          *)
(*      其消解见 Part 3（req_pick_best_token / req_pick_best_token_optimal） --------- *)

Section ReqSLMGreedy.

Variable pick_best_token : list Token -> Token.
Hypothesis pick_best_in_vocab : forall prefix : list Token,
  InT (pick_best_token prefix) vocab.
Hypothesis pick_best_optimal : forall (prefix : list Token) (w : Token),
  InT w vocab ->
  le (total_loss (prefix ++ [pick_best_token prefix])) (total_loss (prefix ++ [w])).

(* ---- 件 9：temperature_zero_exponential_bound（L2630；pick_best_in_vocab 参数位） *)

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

(* ---- 件 13：greedy_kernel_limit（L2819；markov_temperature_zero_limit +        *)
(*        pick_best_optimal 参数位） --------------------------------------------- *)

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

(* ---- 件 17：nonoptimal_probability_absolute（L2887；Id 证明体独立复刻——       *)
(*        与件 9 语句前提不同（无 lt 前提），非 exact 复用） --------------------- *)

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
(* Part 2：ReqLogDiffPhase3 尾节（13 件直迁 + 2 件依存 + 2 eps 副道件）     *)
(*   源坐标 L26405-26685。minus -> req_minus（δ 透明）；log 前提化；        *)
(*   Id 环引理全换 UpReqAlgebra req 真证件（头注登记表 4）。                        *)
(* ===================================================================== *)
Section ReqLogDiff3.

Context {RLL : ReqLogPlain}.

(* ---- 件 1：minus_one_plus_t（L26409，ring） -------------------------------- *)

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

(* ---- 件 3：set_eq_le（L26435；1 行依存 reqd_le_of_req@UpReqDist——eq->le       *)
(*        方向接口可导，清单判「非完成类」） ----------------------------------- *)

Lemma req_set_eq_le : forall a b : R, req a b -> le a b.
Proof.
  intros a b H.
  exact (reqd_le_of_req a b H).
Qed.

(* ---- 件 4：set_square_nonneg（L26441） ------------------------------------- *)

Lemma req_set_square_nonneg : forall t : R, le zero t -> le zero (mult t t).
Proof.
  intros t Ht.
  apply (le_trans _ (mult t zero) _).
  - exact (req_set_eq_le zero (mult t zero) (req_sym (mult t zero) zero (mult_zero t))).
  - exact (req_le_mult_compat_r t zero t Ht Ht).
Qed.

(* ---- 件 5：set_cube_nonneg（L26450） --------------------------------------- *)

Lemma req_set_cube_nonneg : forall t : R, le zero t -> le zero (mult t (mult t t)).
Proof.
  intros t Ht.
  apply (le_trans _ (mult t zero) _).
  - exact (req_set_eq_le zero (mult t zero) (req_sym (mult t zero) zero (mult_zero t))).
  - exact (req_le_mult_compat_r t zero (mult t t) Ht (req_set_square_nonneg t Ht)).
Qed.

(* ---- 件 6：set_minus_mult（L26461）= (a) 依存 req_mult_minus_distr_l@         *)
(*        UpReqAlgebra L525（别名直引，不设 alias 壳） ------------------------- *)
(* ---- 件 7：set_opp_zero（L26468）= (a) 依存 reqd_opp_zero@UpReqDist L171 ------- *)

(* ---- 件 8：set_quad_cube（L26477，全显式环链） ------------------------------ *)

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

(* ---- 件 9：set_quad_prod（L26507；distrib + (a) 件 + 件 8） ------------------ *)

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

(* ---- 件 10：set_minus_cube_le（L26527；(a) reqd_opp_zero 依存位） ------------- *)

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

(* ---- 件 11：set_one_plus_pos（L26541） ------------------------------------- *)

Lemma req_set_one_plus_pos : forall t : R, le zero t -> lt zero (plus one t).
Proof.
  intros t Ht0.
  apply (lt_le_trans zero one (plus one t)).
  - exact one_pos.
  - apply (le_id_l _ _ _ (req_sym (plus one zero) one (plus_zero one))).
    exact (le_plus_compat one one zero t (le_refl one) Ht0).
Qed.

(* ---- 件 12：set_inv_mul（L26557） ------------------------------------------ *)

Lemma req_set_inv_mul : forall (s : R) (Hs : lt zero s),
  req (mult (inv_pos s Hs) s) one.
Proof.
  intros s Hs.
  exact (req_trans _ _ _ (mult_comm (inv_pos s Hs) s) (inv_pos_correct s Hs)).
Qed.

(* ---- 件 13：set_div_linear_ge_quad（L26566） -------------------------------- *)

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

(* ---- 件 14：set_inv_minus_one_opp（L26605；req_opp_minus 形重述） ------------- *)

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

(* ---- 件 2：log_one_plus_le（L26423，(b)+假设位主道） ------------------------ *)

Lemma req_log_one_plus_le : forall (t : R) (Hpos : lt zero (plus one t)),
  le (log (plus one t) Hpos) t.
Proof.
  intros t Hpos.
  apply (le_trans _ (req_minus (plus one t) one) _).
  - exact (log_le_linear_plain (plus one t) Hpos).
  - exact (lt_le_iff _ _ (inr (req_ld3_minus_one_plus_t t))).
Qed.

(* ---- 件 2 副道：Bishop 逐 eta 形（零参数位真证，log_le_linear_eps 直导） --------- *)

Lemma req_log_one_plus_le_eps : forall (t : R) (Hpos : lt zero (plus one t)) (eta : R),
  lt zero eta -> le (log (plus one t) Hpos) (plus t eta).
Proof.
  intros t Hpos eta Heta.
  exact (le_id_r _ _ _           (req_plus_compat (plus (plus one t) (opp one)) t eta eta                            (req_ld3_minus_one_plus_t t) (req_refl eta))           (log_le_linear_eps (plus one t) Hpos eta Heta)).
Qed.

(* ---- 件 15：log_one_plus_ge（L26638，(b)+假设位主道；链 = 件 13 + 件 14 +      *)


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

(* ---- 件 15 副道：Bishop 逐 eta 形（零参数位真证；Hoc 的 opp 链两个合取肢重述 ------------ *)
(*        （req_opp_plus/req_opp_minus/Hio 对偶），末端 req_minus_plus_cancel      *)
(*        折叠。全链依存 log_le_linear_eps，假设位零依赖。） ---------------------- *)

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
  (* 肢 A：opp (invs − 1) == one − invs == t·invs（req_opp_minus + 对偶重述） *)
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
  (* t−t² − eta ≤ log s ⟹ t−t² ≤ log s + eta *)
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
(* Part 3：ReqSLMGreedy 两参数位消解（显式假设位的定理化收束）              *)

(*   req_pick_best_token / req_pick_best_token_optimal 闭包参数面 =         *)
(*   {R}{RIS}{DO} Token vocab total_loss default_token prefix w            *)
(*   （Check 检验在案）。                                                   *)
(*   参数位面核对：ReqSLMGreedy 两参数位面 =                                       *)
(*     optimal  : forall prefix w, InT w vocab ->                          *)
(*                le (total_loss (prefix++[pick prefix]))                  *)
(*                   (total_loss (prefix++[w]))                            *)
(*     in_vocab : forall prefix, InT (pick prefix) vocab                   *)
(*   optimal 面 = req_pick_best_token_optimal 语句 1:1 对齐——直接消解；     *)
(*   in_vocab 面 C1 机未结果（(d) 冻结 list 机域），本节 req 侧归纳自证     *)
(*   （slm_discharge_aux_acc——req_list_sum_le_on_list「辅件自证非重证」    *)
(*   先例同款，不触 (d) 禁区本体）。两参数位就此全消解，依存面三件升级          *)
(*   无参数位定理（_noslot）。                                                 *)
(*   诚实签名差异：无参数位件闭包签名增 DO : reqDecidableOrder R RIS 与        *)
(*   default_token : Token 两位（C1 机同款面；DO 为永久假设类参数位——      *)
(*   LPO 结论随桥：全库零 Instance 与 Id 同构，Class 假设位非禁词面，    *)
(*   End 时入闭包签名，Print Assumptions Closed）。                        *)
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

(* ---- 节内简写（ReqSLM 闭包件全参喂定；签名检验 Check 在案） ---- *)

Definition k_d (prefix : list Token) (w : Token) : R :=
  slm_markov_kernel Token vocab vocab_nonempty total_loss temperature
    temperature_pos prefix w.

Definition pos_d (prefix : list Token) (w : Token) : lt zero (k_d prefix w) :=
  req_markov_pos_slm Token vocab vocab_nonempty total_loss temperature
    temperature_pos prefix w.

(* ---- 贪心选取（C1 机 req_pick_best_token 实例化；无参数位） ---------------- *)

Definition slm_discharge_pick_in (prefix : list Token) : Token :=
  req_pick_best_token Token vocab total_loss default_token prefix.

(* ---- 参数 in_vocab 消解前置：argmin 遍历成员归纳（req 侧自证） ---------- *)
(*   不变式：遍历 l 后 fst 结果 ∈ (btk::l 的任一超集 super)。归纳 +        *)
(*   rord_le_dec 双支 + InT 反转（inversion as 三名显式——OrderArgmin      *)
(*   卡「名不足绑首参被 subst 吞」坑对位）。                                *)

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

(* ---- 参数 in_vocab 消解（pick_best_in_vocab L2575 对位） ----------------- *)

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

(* ---- 参数 optimal 消解（pick_best_optimal L2545 对位；C1 机 1:1 依存） --- *)

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

(* ---- 无参数位件 1：req_greedy_kernel_limit 升级（L2819 依存位已证明） -------- *)

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

(* ---- 无参数位件 2：temperature_zero_exponential_bound 升级（L2630） -------- *)

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

(* ---- 无参数位件 3：nonoptimal_probability_absolute 升级（L2887） ------------ *)

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
(* 文件尾：机器域事实与显式假设位注记（零证明行）                          *)
(* --------------------------------------------------------------------- *)
(* 机器域不迁移件（nat/list Id 层，恒等保留于基座）：                     *)
(*   SLM 区 5 件：InT_head_extend L2451 / argmin_aux_token_mem L2461 /            *)
(*     argmin_aux_token_snd_correct L2517（Leibniz = 正确性伴件）                 *)
(*     / pick_best_in_vocab' L2531 / pick_best_in_vocab L2575（别名件）。          *)
(*   本文件 req_temperature_zero_exponential_bound /                              *)
(*     req_nonoptimal_probability_absolute 经 pick_best_in_vocab 假设位依存其顶层事实： *)
(*     机器域原样 Require、结论以 req 层组装。                                    *)
(* 可判定序显式假设类（reqDecidableOrder+reqArgmin）：                       *)
(*   SLM 区 2 件：argmin_aux_token_min L2481 / pick_best_optimal L2545——            *)
(*     语句纯 le 可 req 1:1；证明机 = ord_le_dec 归纳（DecidableOrder                *)
(*     = 整体三分律 = LPO 等价、全库零 Instance，req 侧永久假设类与 Id 同构）。        *)
(*   两假设位已由 Part 3 消解（optimal = req_pick_best_token_optimal 1:1 依存；       *)
(*     in_vocab = req 侧归纳自证）+ 依存面三件升级 _noslot 无假设位定理。           *)
(*     本文件 ReqSLMGreedy 假设位节为接口申报面，依存面以 Part 3 无假设位件为准。      *)
(* ===================================================================== *)
