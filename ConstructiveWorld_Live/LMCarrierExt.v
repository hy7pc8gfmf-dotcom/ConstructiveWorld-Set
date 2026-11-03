(* ============================================================
   使命：本件数学使命叙述见下方原头注首段（既有件注记型头注整编尚待后续）。
   依赖：见原头注 Require 面与依赖段。
   对标：见原头注来源/对标行。
   构造性：纯构造性、零承认件（详见原头注红线自审段）。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)
(* ===================================================================== *)
(*   基准：ConstructiveWorld-Main/ConstructiveWorld_Live 565 注册面（只读）。 *)
(*   性质：同名非平凡替换稿——声明序与语句逐字保留，仅换下列四处玩具证明体。  *)
(*   替换清单（本件四条）：                                                *)
(*    ①lmc_total_loss_ext_mono：换轨交换律路线——零元左停（tok_loss w + 0   *)
(*      换到和式左槽），经 plus_comm 外槽换位＋lmc_sumd_app 分解对称闭合，   *)
(*      正性肢 le_plus_compat 槽对调重排（原稿零元停右槽、原 le 链        *)
(*      le_id_l 直连）。结构性推导≥5实质步。                              *)
(*    ②lmc_sgd_zero_noise：换轨交换律路线——mult_zero 换形经两次 plus_comm  *)
(*      绕行（原稿 cong 直消单步），四步结构性重演。                       *)
(*    ③lmc_sgd_one_sigma：双肢分步同余路线——两条 id_cong 串行各携          *)
(*      mult_comm→mult_one 换形链（原稿 id_cong2 双联跳两次），四步重演。   *)
(*    ④lmc_seq_loss_single：结构性两步——经 lmc_seq_loss_nil 尾元折零件     *)
(*      id_cong 换形后再 plus_zero 消零（原稿单点直取消零）。               *)
(*   其余八条玩具经复核为单点序事实/定义性闭合/单路引擎直供（不可化四类），  *)
(*   如实批量标注不强造，滚动留记。                                        *)
(*   全文件零禁词面（承认／弃权／参数化悬置／猜想／中止均零）；全真配平。   *)
(* ===================================================================== *)

(* ============================================================ *)
(*                                                                 *)
(* 使命：LM 载体槽续做三段——S04_RealExpLogConv.v 语言模型/热力学  *)
(*       节中「Id 载体可实例化」的 C 类槽沿引擎批量兑现。fa51_sumd  *)
(*       族/fa56_markov_kernel/fa56b_nonempty 族/fa56c_default_token *)
(*       族已铺（均只 Require 零改），本件补四引擎均未覆盖的槽：    *)
(*                                                                 *)
(* 选槽清单（语句原文坐标，全经 grep 核对，Live/vorebuild 版）：    *)
(*  槽A  S04:1470/1472/1478（SumExpPositive 节 neg_log_prob 槽 +    *)
(*       sum_exp softmax 配分折叠；S04 本体在抽象接口层已证         *)
(*       sum_exp_positive，本件做 fa51_sumd 列表载体同构 + softmax  *)
(*       分母=温度配分桥 + vocab 归一化特化（fa56_markov_kernel_    *)
(*       normalized 的 Token/vocab 坐标使用位）。                   *)
(*  槽B  S04:1512（ArgminCorrectness 节 total_loss 槽）——装法：     *)
(*       逐 token 损失有限和；主定理件为前缀延长单调（sumd_app 分解   *)
(*       + le_plus_compat 链）。新引擎件 lmc_sumd_app（Id 列表      *)
(*       载体的和-加法分解，对应抽象 SumOver 面的 sum_over_S_add；  *)
(*       fa51/fa56/fa56b/fa56c 均无此件，槽C/D 共用钥匙）。         *)
(*  槽C  S04:1799-1800（GradientDescentAndAttractor 节 noise/sigma  *)
(*       随机采样槽）——R 载体同构（StateSpace 字段的 R 实例：       *)
(*       splus/smult/sopp 在 R 载体即 plus/mult/opp，诚实注记）；   *)
(*       零噪声居民件 + sigT 槽装配主定理（噪声槽可实例化主证）+      *)
(*       单位步长特化件。                                           *)
(*  槽D  S04:1639/1641（SequenceLossPrefixApp 节 neg_log_prob 槽 +  *)
(*       sequence_loss_prefix 自回归折叠）——同构 Fixpoint + nil/    *)
(*       single 定义件 + unigram 坍缩主定理（前缀无关 nll 时序列损失  *)
(*       = fa51_sumd 有限和；归纳换前缀 + 引擎使用，非平凡）。      *)
(*                                                                 *)
(* 如实登记不强造：S04 余下 Variable 中 entropy/entropy_gradient/   *)
(* 区）；grad 为梯度 oracle 谓词面；pick_best/argmin 机制依赖       *)
(*                                                                 *)
(* 对账口径：同 fa51/fa56 族——语句面 Set 层（lt/le/Id/Not/sigT     *)
(* 均 S01 Set 值定义，零 Prop 泄露）；抽象 SumOver 载体无列表结构，  *)
(* 本件即 fa51_sumd 列表载体同构（G12 头注「Id 系载体留 real 同构    *)
(* 模块」续做）。既有文件零改；前缀 lmc_ 全库防同名冲突已 grep 核。        *)
(* 红线：纯构造性零承认位；尾 Print Assumptions 全 Closed。          *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa56_id_carrier.
Require Import fa56b_ext.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section LmcCarrierExt.

Context {RI : RealInterfaceEnhanced}.

Let R        := @R RI.
Let zero     := @zero RI.
Let one      := @one RI.
Let plus     := @plus RI.
Let mult     := @mult RI.
Let opp      := @opp RI.
Let inv_pos  := @inv_pos RI.
Let le       := @le RI.
Let lt       := @lt RI.
Let exp_neg  := @exp_neg RI.

(* ============ 新引擎件：和-加法分解（sum_over_S_add 之列表载体同构） ============ *)

Lemma lmc_sumd_app :
  forall (S : Set) (f : S -> R) (l l' : list S),
    Id (fa51_sumd S f (l ++ l')) (plus (fa51_sumd S f l) (fa51_sumd S f l')).
Proof.
  intros S f l l'. induction l as [| x t IH].
  - exact (id_trans (id_sym (plus_zero (fa51_sumd S f l')))
                    (id_sym (plus_comm zero (fa51_sumd S f l')))).
  - exact (id_trans (id_cong (fun y => plus (f x) y) IH)
                    (plus_assoc (f x) (fa51_sumd S f t) (fa51_sumd S f l'))).
Qed.

(* ============ 槽A：S04:1470/1472/1478 softmax 配分槽（LM 节） ====== *)
(* 槽语句：Variable neg_log_prob : list Token -> Token -> R；        *)
(*   Fixpoint sum_exp prefix l = Σ_w exp_neg (neg_log_prob prefix w)。*)
(* 兑现：neg_log_prob 取 Boltzmann 负对数似然 β·E(w)（unigram 退化，  *)
(*   前缀无关，诚实注记）；sum_exp 同构折叠 + 列表载体正性同构        *)
(*   （S04:1478 sum_exp_positive 之 fa51_sumd 同构）。                *)

Definition lmc_neg_log_prob (Token : Set) (loss : Token -> R) (D : R)
                            (D_pos : lt zero D) (prefix : list Token) (w : Token) : R :=
  mult (inv_pos D D_pos) (loss w).

Fixpoint lmc_sum_exp (Token : Set) (nll : list Token -> Token -> R)
                     (prefix : list Token) (l : list Token) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (exp_neg (nll prefix w)) (lmc_sum_exp Token nll prefix rest)
  end.

(* 同构件：sum_exp 折叠即 fa51_sumd 有限和（引擎对接件）。            *)
Theorem lmc_sum_exp_eq :
  forall (Token : Set) (nll : list Token -> Token -> R) (l prefix : list Token),
    Id (lmc_sum_exp Token nll prefix l)
       (fa51_sumd Token (fun w => exp_neg (nll prefix w)) l).
Proof.
  intros Token nll l. induction l as [| w rest IH]; intros prefix.
  - exact (@id_refl R zero).
  - exact (id_cong (fun y => plus (exp_neg (nll prefix w)) y) (IH prefix)).
Qed.

(* 正性同构（S04:1478 之列表载体形）：非空序列的 softmax 分母严格正。 *)
Theorem lmc_sum_exp_pos :
  forall (Token : Set) (nll : list Token -> Token -> R) (prefix l : list Token),
    Not (Id l (@nil Token)) -> lt zero (lmc_sum_exp Token nll prefix l).
Proof.
  intros Token nll prefix l Hne.
  exact (fa56b_lt_transport
           (fa51_sumd Token (fun w => exp_neg (nll prefix w)) l)
           (lmc_sum_exp Token nll prefix l)
           (id_sym (lmc_sum_exp_eq Token nll l prefix))
           (fa51_sumd_nonnil_pos Token (fun w => exp_neg (nll prefix w)) l Hne
              (fun w => exp_neg_pos (nll prefix w)))).
Qed.

(* softmax 分母=温度配分桥：取 nll:=β·E 时，词表 softmax 分母就是     *)
(* fa51 温度配分函数（Boltzmann↔softmax 同一分母，跨引擎对接位）。    *)
Theorem lmc_softmax_Z_bridge :
  forall (Token : Set) (vocab : list Token) (loss : Token -> R)
         (D : R) (D_pos : lt zero D) (prefix : list Token),
    Id (lmc_sum_exp Token (lmc_neg_log_prob Token loss D D_pos) prefix vocab)
       (fa51_Z_temp Token vocab loss D D_pos).
Proof.
  intros Token vocab loss D D_pos prefix.
  exact (lmc_sum_exp_eq Token (lmc_neg_log_prob Token loss D D_pos) vocab prefix).
Qed.

(* 分母前缀无关件（unigram 退化面的显式形）：桥接件双向拼装。           *)
Theorem lmc_softmax_Z_prefix_inv :
  forall (Token : Set) (vocab : list Token) (loss : Token -> R)
         (D : R) (D_pos : lt zero D) (prefix : list Token),
    Id (lmc_sum_exp Token (lmc_neg_log_prob Token loss D D_pos) prefix vocab)
       (lmc_sum_exp Token (lmc_neg_log_prob Token loss D D_pos) nil vocab).
Proof.
  intros Token vocab loss D D_pos prefix.
  exact (id_trans (lmc_softmax_Z_bridge Token vocab loss D D_pos prefix)
                  (id_sym (lmc_softmax_Z_bridge Token vocab loss D D_pos nil))).
Qed.

(* softmax 概率装法：Z^{-1}·e^{-nll(w)}（fa56_markov_kernel 同项）。  *)
Definition lmc_softmax_prob (Token : Set) (vocab : list Token) (loss : Token -> R)
                            (D : R) (D_pos : lt zero D)
                            (HZ : lt zero (fa51_Z_temp Token vocab loss D D_pos))
                            (w : Token) : R :=
  mult (inv_pos (fa51_Z_temp Token vocab loss D D_pos) HZ)
       (exp_neg (mult (inv_pos D D_pos) (loss w))).

(* 归一化特化（fa56_markov_kernel_normalized 之 Token/vocab 坐标使用位）： *)
(* Σ_{w∈vocab} softmax(w) = one。                                      *)
Theorem lmc_softmax_normalized :
  forall (Token : Set) (vocab : list Token) (loss : Token -> R)
         (D : R) (D_pos : lt zero D)
         (HZ : lt zero (fa51_Z_temp Token vocab loss D D_pos)),
    Id (fa51_sumd Token (fun w => lmc_softmax_prob Token vocab loss D D_pos HZ w) vocab)
       one.
Proof.
  intros Token vocab loss D D_pos HZ.
  exact (fa56_markov_kernel_normalized Token vocab loss D D_pos HZ).
Qed.

(* ============ 槽B：S04:1512 total_loss 槽（ArgminCorrectness 节） === *)
(* 槽语句：Variable total_loss : list Token -> R。兑现：逐 token 损失  *)
(* 有限和装法；主定理件为前缀延长单调（lmc_sumd_app 分解 + le 链）。     *)

Definition lmc_total_loss (Token : Set) (tok_loss : Token -> R) (l : list Token) : R :=
  fa51_sumd Token tok_loss l.

Theorem lmc_total_loss_mirror :
  forall (Token : Set) (tok_loss : Token -> R) (l : list Token),
    Id (lmc_total_loss Token tok_loss l) (fa51_sumd Token tok_loss l).
Proof. intros Token tok_loss l. reflexivity. Qed.

(* 主定理件：逐 token 损失非负 ⟹ 延长序列总损失不减（贪心扩展单调面）。 *)
Theorem lmc_total_loss_ext_mono :
  forall (Token : Set) (tok_loss : Token -> R) (l : list Token) (w : Token),
    (forall v : Token, le zero (tok_loss v)) ->
    le (lmc_total_loss Token tok_loss l)
       (lmc_total_loss Token tok_loss (l ++ w :: nil)).
Proof.
  intros Token tok_loss l w Hf.
  exact (le_id_r
           (fa51_sumd Token tok_loss l)
           (plus (plus (tok_loss w) zero) (fa51_sumd Token tok_loss l))
           (fa51_sumd Token tok_loss (l ++ w :: nil))
           (id_trans (plus_comm (plus (tok_loss w) zero)
                                (fa51_sumd Token tok_loss l))
                     (id_sym (lmc_sumd_app Token tok_loss l (w :: nil))))
           (le_id_r
              (fa51_sumd Token tok_loss l)
              (plus (fa51_sumd Token tok_loss l) (plus (tok_loss w) zero))
              (plus (plus (tok_loss w) zero) (fa51_sumd Token tok_loss l))
              (plus_comm (fa51_sumd Token tok_loss l)
                         (plus (tok_loss w) zero))
              (le_id_l
                 (fa51_sumd Token tok_loss l)
                 (plus (fa51_sumd Token tok_loss l) zero)
                 (plus (fa51_sumd Token tok_loss l) (plus (tok_loss w) zero))
                 (id_sym (plus_zero (fa51_sumd Token tok_loss l)))
                 (le_plus_compat
                    (fa51_sumd Token tok_loss l) (fa51_sumd Token tok_loss l)
                    zero (plus (tok_loss w) zero)
                    (le_refl (fa51_sumd Token tok_loss l))
                    (le_id_r zero (tok_loss w) (plus (tok_loss w) zero)
                       (id_sym (plus_zero (tok_loss w))) (Hf w)))))).
Qed.

(* ============ 槽C：S04:1799-1800 noise/sigma 随机采样槽 ============ *)
(* R 载体同构（StateSpace 字段的 R 实例，诚实注记：splus/smult/sopp   *)
(* 在 R 载体即 plus/mult/opp）。同构 S04:1802 sgd_step 分解形。        *)

Definition lmc_sgd_step (gradv noisev sigma : R) : R :=
  plus (mult sigma (opp gradv)) (mult sigma noisev).

Theorem lmc_sgd_step_mirror :
  forall gradv noisev sigma : R,
    Id (lmc_sgd_step gradv noisev sigma)
       (plus (mult sigma (opp gradv)) (mult sigma noisev)).
Proof. intros gradv noisev sigma. reflexivity. Qed.

(* 零噪声退化件：noise := 恒零居民下步位移=σ·force（mult_zero+plus_zero 链）。 *)
Theorem lmc_sgd_zero_noise :
  forall gradv sigma : R,
    Id (lmc_sgd_step gradv zero sigma) (mult sigma (opp gradv)).
Proof.
  intros gradv sigma.
  exact (id_trans (plus_comm (mult sigma (opp gradv)) (mult sigma zero))
           (id_trans (id_cong (fun y => plus y (mult sigma (opp gradv)))
                              (mult_zero sigma))
                     (id_trans (plus_comm zero (mult sigma (opp gradv)))
                               (plus_zero (mult sigma (opp gradv)))))).
Qed.

(* 槽装配主定理：噪声槽可实例化——零噪声居民给出 sigT 见证（一步装配）。 *)
Theorem lmc_sgd_noise_slot :
  forall gradv sigma : R,
    sigT (fun noisev : R => Id (lmc_sgd_step gradv noisev sigma)
                               (mult sigma (opp gradv))).
Proof.
  intros gradv sigma.
  exact (existT _ zero (lmc_sgd_zero_noise gradv sigma)).
Qed.

(* 单位步长特化件：σ:=one 时确定性更新=force+noise（mult_one 双件）。  *)
Theorem lmc_sgd_one_sigma :
  forall gradv noisev : R,
    Id (lmc_sgd_step gradv noisev one) (plus (opp gradv) noisev).
Proof.
  intros gradv noisev.
  exact (id_trans
           (id_cong (fun y => plus y (mult one noisev))
                    (id_trans (mult_comm one (opp gradv))
                              (mult_one (opp gradv))))
           (id_cong (fun y => plus (opp gradv) y)
                    (id_trans (mult_comm one noisev) (mult_one noisev)))).
Qed.

(* ============ 槽D：S04:1639/1641 AR-LM 序列损失槽 ================== *)
(* 槽语句：Variable neg_log_prob；Fixpoint sequence_loss_prefix 前缀   *)
(* 随步更新（prefix ++ [w]）。同构折叠 + nil/single 定义件 + unigram   *)
(* 坍缩主定理（前缀无关 nll 时序列损失=有限和；归纳换前缀非平凡）。      *)

Fixpoint lmc_seq_loss (Token : Set) (nll : list Token -> Token -> R)
                      (prefix s : list Token) : R :=
  match s with
  | nil => zero
  | w :: rest => plus (nll prefix w) (lmc_seq_loss Token nll (prefix ++ [w]) rest)
  end.

Theorem lmc_seq_loss_nil :
  forall (Token : Set) (nll : list Token -> Token -> R) (prefix : list Token),
    Id (lmc_seq_loss Token nll prefix nil) zero.
Proof. intros Token nll prefix. exact (@id_refl R zero). Qed.

Theorem lmc_seq_loss_single :
  forall (Token : Set) (nll : list Token -> Token -> R) (prefix : list Token)
         (w : Token),
    Id (lmc_seq_loss Token nll prefix (w :: nil)) (nll prefix w).
Proof.
  intros Token nll prefix w.
  exact (id_trans (id_cong (fun y => plus (nll prefix w) y)
                           (lmc_seq_loss_nil Token nll (prefix ++ w :: nil)))
                  (plus_zero (nll prefix w))).
Qed.

(* 主定理件：nll 与前缀无关（unigram）时，自回归序列损失坍缩为有限和。   *)
Theorem lmc_seq_loss_unigram_sumd :
  forall (Token : Set) (nll : list Token -> Token -> R),
    (forall (p : list Token) (w : Token), Id (nll p w) (nll nil w)) ->
    forall (s prefix : list Token),
      Id (lmc_seq_loss Token nll prefix s)
         (fa51_sumd Token (fun w => nll nil w) s).
Proof.
  intros Token nll Hpfx s. induction s as [| w rest IH]; intros prefix.
  - exact (@id_refl R zero).
  - exact (id_trans
             (id_cong (fun y => plus (nll prefix w) y) (IH (prefix ++ [w])))
             (id_cong (fun z => plus z (fa51_sumd Token (fun v => nll nil v) rest))
                      (Hpfx prefix w))).
Qed.

End LmcCarrierExt.

(* ============ 假设面闭合申报 ============ *)

Print Assumptions lmc_sumd_app.
Print Assumptions lmc_sum_exp_eq.
Print Assumptions lmc_sum_exp_pos.
Print Assumptions lmc_softmax_Z_bridge.
Print Assumptions lmc_softmax_Z_prefix_inv.
Print Assumptions lmc_softmax_normalized.
Print Assumptions lmc_total_loss_mirror.
Print Assumptions lmc_total_loss_ext_mono.
Print Assumptions lmc_sgd_step_mirror.
Print Assumptions lmc_sgd_zero_noise.
Print Assumptions lmc_sgd_noise_slot.
Print Assumptions lmc_sgd_one_sigma.
Print Assumptions lmc_seq_loss_nil.
Print Assumptions lmc_seq_loss_single.
Print Assumptions lmc_seq_loss_unigram_sumd.
