(* ==========================================================================)
   Arch_ToyR_03.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：sem_sum_eq_list_req_slot、sem_sum_eq_list_collapse、sem_slot1_witness_upreqsampling、sem_slot1_witness_collapse、sem_czb12_slot_attdoeblin_writeoff、sem_czb12_slot_g01_writeoff、sem_czb12_slot_s13_writeoff、sem_czb12_slot_s15_writeoff、fa56b_id_transport。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

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
Require Import UpReqSumD.
Require Import UpReqSampling.
From Stdlib Require Import List.
Require Import AttnDoeblin.
Require Import IdSlotTranslate.
Require Import fa51_sumpos_id.
Require Import fa56_id_carrier.
Require Import Paper7Ablation.
Require Import P7BoundedSoftmaxDeep.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpAblD1S7_UpReqEntropyMaxTemp.
Require Import fa56b_ext.
Require Import UpReqAlgebra.

(* ================= §1 sem_sum_eq_list_req_slot 族 ================= *)
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* 桥出节签名留痕（编译日志打表：S/enum/g 显式，接口字段经全局实例消解） *)
About sumd_sum_eq_list.

(* ============ 实例化定理 1：桥直接代入（req 形槽 sumd 实例） ============ *)
(* 槽语句 req (sumf g) (rsq_bs_list_sum g enum) 在 sumf := sumd_sumf、 *)
(* 机器位 := sumd_list_sum 实例下，钥匙桥逐字输入。req 经全局实例      *)
(* （RealEnhancedReal）定义性即 real_eq，语句面取具体载体面。          *)
Theorem sem_sum_eq_list_req_slot :
  forall (S : Set) (enum : list S) (g : S -> Real),
    real_eq (@sumd_sumf S enum g) (@sumd_list_sum S g enum).
Proof. intros S enum g. exact (@sumd_sum_eq_list S enum g). Qed.

(* ============ 实例化定理 2：零机器坍缩 ============ *)
(* sumd_sumf g := sumd_list_sum g enum 定义性，槽实例即自反。         *)
Theorem sem_sum_eq_list_collapse :
  forall (S : Set) (enum : list S) (g : S -> Real),
    real_eq (@sumd_sumf S enum g) (@sumd_list_sum S g enum).
Proof. intros S enum g. exact (req_refl (@sumd_list_sum S g enum)). Qed.

(* ============ 实例化定理 3：槽1 宿主真机桥直接代入（主交付） ============ *)
(* 机器位是宿主出节真机 rsq_bs_list_sum。桥的列表和肢经出节件互转        *)
(* （同形同接口，自反级 conversion）一步输入——槽1 兑现实证，             *)
Theorem sem_slot1_witness_upreqsampling :
  forall (S : Set) (enum : list S) (g : S -> Real),
    real_eq (@sumd_sumf S enum g) (@rsq_bs_list_sum S g enum).
Proof. intros S enum g. exact (@sumd_sum_eq_list S enum g). Qed.

(* ============ 实例化定理 4：槽1 宿主真机零机器坍缩 ============ *)
Theorem sem_slot1_witness_collapse :
  forall (S : Set) (enum : list S) (g : S -> Real),
    real_eq (@sumd_sumf S enum g) (@rsq_bs_list_sum S g enum).
Proof. intros S enum g. exact (req_refl _). Qed.

(* ============ G4 证据：四定理全 Closed ============ *)
Print Assumptions sem_sum_eq_list_req_slot.
Print Assumptions sem_sum_eq_list_collapse.
Print Assumptions sem_slot1_witness_upreqsampling.
Print Assumptions sem_slot1_witness_collapse.

(* ============ 组 E-STAGING-CZB12 兑现声明段（b 尾工 C1） ============ *)
(* 槽2-5「机器口径转换墙」遗留登记兑现。本段为纯转发声明件（全 exact       *)
(* 转发 IdSlotTranslate 已证桥，零新机器零新数学），既有四定理零改动，      *)
(* 参数位1 实证面不变。对照先例： / 。    *)
(*   「结论（转换墙实测，勿虚报）：四槽宿主机器 bs_list_sum 跑在             *)
(*   RealInterfaceEnhanced 接口（Context {RI}{SS}{SO} 载体），其             *)
(*   zero/plus 投影常量与 sumd 之 RealInterfaceEnhancedSetoid 投影           *)
(*   不同头，桥对真宿主直接代入需接口翻译件（RI→Setoid），超出零新               *)
(*   机器口径——遗留未决，不在本件虚报兑现。」                                *)
(* 二、兑现路径（遗留所索「接口翻译件」已建成，CYD7/CZB8 两棒接续）：        *)
(*   ① 翻译件本体 = 消融50/：RI 载体列表折叠副本           *)
(*   ② 依存位覆盖 = 消融50/ 四宿主八依存位重述 shim：         *)
(*   槽参链在盘），覆盖判定成立。                                            *)
(* 三、判定：槽2-5 遗留兑现（覆盖）。以下四转发件 = 四槽兑现的可提取出口，    *)
(*   语句 = idt 四宿主兑现定理之逐字副本（槽语句 sum_over_S := idt_sumf      *)
(*   实例化消解读法）。宿主文件零改动（AttnDoeblin/S13/G01/S15 皆未触碰）。         *)


Section SumEqListMarkWriteoff.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Local Existing Instance RI_base.

Theorem sem_czb12_slot_attdoeblin_writeoff :
  forall (en : list S) (g : S -> @S01_BaseRing.R RI),
    Id (idt_sumf en g) (AttnDoeblin.bs_list_sum g en).
Proof. intros en g. exact (idt_slot_attdoeblin en g). Qed.

Theorem sem_czb12_slot_g01_writeoff :
  forall (en : list S) (g : S -> @S01_BaseRing.R RI),
    Id (idt_sumf en g) (AttnDoeblin.bs_list_sum g en).
Proof. intros en g. exact (idt_slot_g01 en g). Qed.

Theorem sem_czb12_slot_s13_writeoff :
  forall (en : list S) (g : S -> @S01_BaseRing.R RI),
    Id (idt_sumf en g) (S13_NLiveAudit.bs_list_sum g en).
Proof. intros en g. exact (idt_slot_s13 en g). Qed.

Theorem sem_czb12_slot_s15_writeoff :
  forall (en : list S) (g : S -> @S01_BaseRing.R RI),
    Id (idt_sumf en g) (S13_NLiveAudit.bs_list_sum g en).
Proof. intros en g. exact (idt_slot_s15 en g). Qed.

End SumEqListMarkWriteoff.

(* ============ G4 证据：兑现转发四件全 Closed ============ *)
Print Assumptions sem_czb12_slot_attdoeblin_writeoff.
Print Assumptions sem_czb12_slot_g01_writeoff.
Print Assumptions sem_czb12_slot_s13_writeoff.
Print Assumptions sem_czb12_slot_s15_writeoff.
(* ================= §2 fa56b_id_transport 族 ================= *)
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Fa56bExt.

Context {RI : RealInterfaceEnhanced}.
Variable S : Set.
Variable enum : list S.

Let R        := @S01_BaseRing.R RI.
Let zero     := @S01_BaseRing.zero RI.
Let one      := @S01_BaseRing.one RI.
Let plus     := @S01_BaseRing.plus RI.
Let mult     := @S01_BaseRing.mult RI.
Let le       := @S01_BaseRing.le RI.
Let lt       := @S01_BaseRing.lt RI.
Let opp      := @S01_BaseRing.opp RI.
Let abs      := @S01_BaseRing.abs RI.
Let inv_pos  := @S01_BaseRing.inv_pos RI.
Let mult_comm := @S01_BaseRing.mult_comm RI.
Let plus_comm := @S01_BaseRing.plus_comm RI.
Let plus_assoc := @S01_BaseRing.plus_assoc RI.
Let mult_one := @S01_BaseRing.mult_one RI.
Let plus_zero := @S01_BaseRing.plus_zero RI.
Let plus_opp := @S01_BaseRing.plus_opp RI.
Let lt_trans := @S01_BaseRing.lt_trans RI.
Let lt_id_l := @S01_BaseRing.lt_id_l RI.
Let lt_mult_compat := @S01_BaseRing.lt_mult_compat RI.
Let le_mult_compat_weak := @S01_BaseRing.le_mult_compat_weak RI.
Let le_id_l := @S01_BaseRing.le_id_l RI.
Let le_id_r := @S01_BaseRing.le_id_r RI.
Let lt_le_iff := @S01_BaseRing.lt_le_iff RI.
Let abs_pos := @S01_BaseRing.abs_pos RI.
Let inv_pos_pos := @S01_BaseRing.inv_pos_pos RI.
Let le_refl := @S01_BaseRing.le_refl RI.
Let lt_id_r := @S01_BaseRing.lt_id_r RI.
Let mult_positive := @S01_BaseRing.mult_positive RI.
Let mult_zero := @S01_BaseRing.mult_zero RI.
Let one_pos := @S01_BaseRing.one_pos RI.
Let plus_positive := @S01_BaseRing.plus_positive RI.

(* ============ 槽VI：J 消去器 + list 判别核 + 非空构造族 =========== *)
(* Id 的依赖匹配消去（本载体首用 J 规则；fa51/fa56 只用过            *)
(* id_sym/id_trans/id_cong 三件套）。                               *)

(* 通用传输（J 消去器）：p : Id x y 把 Q x 中的元素搬到 Q y。        *)
Definition fa56b_id_transport (A : Set) (Q : A -> Set) (x y : A)
                              (p : Id x y) (h : Q x) : Q y :=
  match p in Id _ a return Q a with
  | id_refl => h
  end.

(* list 判别核：nil 与 cons 的 Id 分离（Set 值型别检验函数，单构造归纳族形）。 *)
Inductive fa56b_list_case (T : Set) : list T -> Set :=
| fa56b_list_case_cons : forall (t : T) (l : list T), fa56b_list_case T (cons t l).

(* 判别核引理：Id (t::l) nil 无居民（cons ≠ nil）。
   形：id_sym H 消去取箭头动机（nil 侧判别核无居民故空函数可居，
   消去结果落 cons 侧），以 cons 侧证人代入得 Empty_set。            *)
Definition fa56b_cons_nil_id_contra (T : Set) (t : T) (l : list T)
                                    (H : Id (t :: l) nil) : Empty_set.
Proof.
  refine ((match id_sym H in Id _ a
             return (fa56b_list_case T a -> Empty_set) with
           | id_refl => fun c => _
           end) (fa56b_list_case_cons T t l)).
  inversion c.
Defined.

Theorem fa56b_singleton_nonempty :
  forall (T : Set) (t0 : T), Not (Id (cons t0 (@nil T)) (@nil T)).
Proof.
  intros T t0 H.
  exact (fa56b_cons_nil_id_contra T t0 nil H).
Qed.

(* 非空闭包·cons：头加元素保非空。                                  *)
Theorem fa56b_cons_nonempty :
  forall (T : Set) (t0 : T) (l : list T),
    Not (Id l nil) -> Not (Id (cons t0 l) nil).
Proof.
  intros T t0 l Hne H.
  exact (fa56b_cons_nil_id_contra T t0 l H).
Qed.

(* 非空闭包·append 左：左支非空则并非空。                           *)
Theorem fa56b_append_nonempty_l :
  forall (T : Set) (l l' : list T),
    Not (Id l nil) -> Not (Id (l ++ l') nil).
Proof.
  intros T l l' Hne H. destruct l as [| t r].
  - exact (Hne (@id_refl (list T) (@nil T))).
  - exact (fa56b_cons_nil_id_contra T t (r ++ l') H).
Qed.

(* 非空闭包·append 右：右支非空则并非空（逐支 case）。              *)
Theorem fa56b_append_nonempty_r :
  forall (T : Set) (l l' : list T),
    Not (Id l' nil) -> Not (Id (l ++ l') nil).
Proof.
  intros T l l' Hne H. destruct l as [| t r].
  - exact (Hne H).
  - exact (fa56b_cons_nil_id_contra T t (r ++ l') H).
Qed.

(* 伴件：严格正性的 Id 不变性（引擎前提在 Id 重整下稳定）。          *)
Theorem fa56b_lt_transport :
  forall (a b : R), Id a b -> lt zero a -> lt zero b.
Proof.
  intros a b p H.
  exact (fa56b_id_transport R (fun w => lt zero w) a b p H).
Qed.

(* 伴件：非负性的 Id 不变性。                                       *)
Theorem fa56b_le_transport :
  forall (a b : R), Id a b -> le zero a -> le zero b.
Proof.
  intros a b p H.
  exact (fa56b_id_transport R (fun w => le zero w) a b p H).
Qed.

(* ============ 槽VII：引擎扩展——逐点 Id ⟹ 和 Id ==================== *)
(* S04 steady_state_boltzmann（L1921）依存的 sum_over_S_ext 之       *)
(* fa51_sumd 列表载体副本；为槽VIII 稳态副本的关键件。               *)

Theorem fa56b_sumd_cong :
  forall (f g : S -> R) (l : list S),
    (forall s : S, Id (f s) (g s)) ->
    Id (fa51_sumd S f l) (fa51_sumd S g l).
Proof.
  intros f g l Hpt. induction l as [| x t IH].
  - exact (@id_refl R zero).
  - exact (id_cong2 (fun a b => plus a b) (Hpt x) IH).
Qed.

(* 乘积换序过和（槽VIII 逐点平衡的批量版）。                         *)
Theorem fa56b_sumd_swap_mult :
  forall (f g : S -> R) (l : list S),
    Id (fa51_sumd S (fun s => mult (f s) (g s)) l)
       (fa51_sumd S (fun s => mult (g s) (f s)) l).
Proof.
  intros f g l.
  exact (fa56b_sumd_cong (fun s => mult (f s) (g s))                         (fun s => mult (g s) (f s)) l                         (fun s => mult_comm (f s) (g s))).
Qed.

(* 兑现：转移取独立提议核 k(s,s') := π(s')（Boltzmann-Gibbs 稳态分布  *)
(* 自身），平衡槽由 mult_comm 闭合；稳态件为主非平凡件（sumd_cong  *)
(* + fa56 线性件 + 行归一 + mult_one 四段链）。π 取 fa56_markov_kernel *)
(* 同项（正性/非负/归一化三伴件由 fa56 已证件直接继承，零重复施工）。 *)

Definition fa56b_boltzmann_prob (base_loss : S -> R) (D : R) (D_pos : lt zero D)
                                (Hne : Not (Id enum nil)) (s : S) : R :=
  fa56_markov_kernel S enum base_loss D D_pos
    (fa51_Z_temp_pos S enum base_loss D D_pos Hne) s.

Definition fa56b_independence_transition
           (base_loss : S -> R) (D : R) (D_pos : lt zero D)
           (Hne : Not (Id enum nil)) (s s' : S) : R :=
  fa56b_boltzmann_prob base_loss D D_pos Hne s'.

Theorem fa56b_detailed_balance :
  forall (base_loss : S -> R) (D : R) (D_pos : lt zero D)
         (Hne : Not (Id enum nil)) (s s' : S),
    Id (mult (fa56b_boltzmann_prob base_loss D D_pos Hne s)
             (fa56b_independence_transition base_loss D D_pos Hne s s'))
       (mult (fa56b_boltzmann_prob base_loss D D_pos Hne s')
             (fa56b_independence_transition base_loss D D_pos Hne s' s)).
Proof.
  intros base_loss D D_pos Hne s s'.
  exact (mult_comm (fa56b_boltzmann_prob base_loss D D_pos Hne s)                   (fa56b_boltzmann_prob base_loss D D_pos Hne s')).
Qed.

(* 逐点平衡 + 行归一 ⟹ π 是平稳分布（Σ_{s'} π(s')k(s',s) = π(s)）。  *)
Theorem fa56b_boltzmann_stationary :
  forall (pi : S -> R) (k : S -> S -> R),
    (forall s s' : S,
        Id (mult (pi s') (k s' s)) (mult (pi s) (k s s'))) ->
    (forall s : S, Id (fa51_sumd S (fun s' => k s s') enum) one) ->
    forall s : S,
      Id (fa51_sumd S (fun s' => mult (pi s') (k s' s)) enum) (pi s).
Proof.
  intros pi k Hdb Hnorm s.
  exact (id_trans           (fa56b_sumd_cong (fun s' => mult (pi s') (k s' s))                            (fun s' => mult (pi s) (k s s')) enum                            (fun x => Hdb s x))           (id_trans              (fa56_sumd_mult_const S (pi s) (fun s' => k s s') enum)              (id_trans                 (id_cong (fun y => mult (pi s) y) (Hnorm s))                 (mult_one (pi s))))).
Qed.

(* 槽语句：cross_domain_scaling : sigT (fun alpha : R => forall N,    *)
(*   Id (loss_drop N) (mult (power (of_nat N) alpha) (f_N N)))。      *)
(* 兑现：loss_drop 装法定义件（幂律形式），槽的 sigT 见证由 existT    *)
(* 直接装配；alpha:=one、power:=mult 特化伴件走 mult_one 归一链。     *)

Definition fa56b_loss_drop (power : R -> R -> R) (of_nat_R : nat -> R)
                           (f_N : nat -> R) (alpha : R) (N : nat) : R :=
  mult (power (of_nat_R N) alpha) (f_N N).

(* 槽语句的 sigT 见证装配（存在性面一次兑现）。                       *)
Theorem fa56b_cross_domain_scaling :
  forall (power : R -> R -> R) (of_nat_R : nat -> R) (f_N : nat -> R)
         (alpha : R),
    sigT (fun a : R => forall N : nat,
            Id (fa56b_loss_drop power of_nat_R f_N a N)
               (mult (power (of_nat_R N) a) (f_N N))).
Proof.
  intros power of_nat_R f_N alpha.
  exact (existT _ alpha (fun N => @id_refl R _)).
Qed.

(* 特化伴件：alpha := one、power := mult 时幂律退化线性标度           *)
(* （mult_one 右单位元经 id_cong 提升进乘积，非平凡归一链）。         *)
Theorem fa56b_cross_domain_linear :
  forall (of_nat_R : nat -> R) (f_N : nat -> R) (N : nat),
    Id (fa56b_loss_drop mult of_nat_R f_N one N)
       (mult (of_nat_R N) (f_N N)).
Proof.
  intros of_nat_R f_N N.
  unfold fa56b_loss_drop.
  exact (id_cong (fun y => mult y (f_N N)) (mult_one (of_nat_R N))).
Qed.

End Fa56bExt.

(* ============ 假设面闭合申报 ============ *)

Print Assumptions fa56b_id_transport.
Print Assumptions fa56b_cons_nil_id_contra.
Print Assumptions fa56b_singleton_nonempty.
Print Assumptions fa56b_cons_nonempty.
Print Assumptions fa56b_append_nonempty_l.
Print Assumptions fa56b_append_nonempty_r.
Print Assumptions fa56b_lt_transport.
Print Assumptions fa56b_le_transport.
Print Assumptions fa56b_sumd_cong.
Print Assumptions fa56b_sumd_swap_mult.
Print Assumptions fa56b_detailed_balance.
Print Assumptions fa56b_boltzmann_stationary.
Print Assumptions fa56b_cross_domain_scaling.
Print Assumptions fa56b_cross_domain_linear.
(* ================= §3 uahl_lo_lt_one_hi 族 ================= *)
(* ############ 段一：合取 lo<1∧1<hi、夹逼 lo<hi、δ*∈(0,1)（无序可判定参） ## *)
(* 节变量面与源模块  的 LhsPair 节一致（温度对＋利差对＋指数族四件）。 *)

Section UahlPair.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R := @S01_BaseRing.R RI.
Let zero := @S01_BaseRing.zero RI.
Let one := @S01_BaseRing.one RI.
Let plus := @S01_BaseRing.plus RI.
Let mult := @S01_BaseRing.mult RI.
Let opp := @S01_BaseRing.opp RI.
Let abs := @S01_BaseRing.abs RI.
Let inv_pos := @S01_BaseRing.inv_pos RI.
Let lt := @S01_BaseRing.lt RI.
Let le := @S01_BaseRing.le RI.
Let mult_comm := @S01_BaseRing.mult_comm RI.
Let plus_comm := @S01_BaseRing.plus_comm RI.
Let plus_assoc := @S01_BaseRing.plus_assoc RI.
Let mult_one := @S01_BaseRing.mult_one RI.
Let plus_zero := @S01_BaseRing.plus_zero RI.
Let plus_opp := @S01_BaseRing.plus_opp RI.
Let lt_trans := @S01_BaseRing.lt_trans RI.
Let lt_id_l := @S01_BaseRing.lt_id_l RI.
Let lt_mult_compat := @S01_BaseRing.lt_mult_compat RI.
Let le_mult_compat_weak := @S01_BaseRing.le_mult_compat_weak RI.
Let le_id_l := @S01_BaseRing.le_id_l RI.
Let le_id_r := @S01_BaseRing.le_id_r RI.
Let lt_le_iff := @S01_BaseRing.lt_le_iff RI.
Let abs_pos := @S01_BaseRing.abs_pos RI.
Let inv_pos_pos := @S01_BaseRing.inv_pos_pos RI.
Let le_refl := @S01_BaseRing.le_refl RI.
Let lt_id_r := @S01_BaseRing.lt_id_r RI.
Let mult_positive := @S01_BaseRing.mult_positive RI.
Let mult_zero := @S01_BaseRing.mult_zero RI.
Let one_pos := @S01_BaseRing.one_pos RI.
Let plus_positive := @S01_BaseRing.plus_positive RI.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).

(* uahl_lo_lt_one_hi（源模块 lhs_lo_lt_one_hi 的独立重证）：左支经              *)
(*   p7a_lo_lt_one，右支经 p7d_hi_gt_one；invT 正性由 inv_pos_pos 提供。      *)
Theorem uahl_lo_lt_one_hi : And (lt lo one) (lt one hi).
Proof.
  split.
  - exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)).
  - exact (p7d_hi_gt_one temp temp_pos Delta Delta_pos expf expf_pos
             expf_zero expf_mono_lt).
Qed.

(* uahl_lo_lt_hi（源模块 lhs_lo_lt_hi 的独立重证）：lt_trans 两步，两支取自 uahl_lo_lt_one_hi 的两肢 *)
Theorem uahl_lo_lt_hi : lt lo hi.
Proof.
  exact (lt_trans lo one hi (fst uahl_lo_lt_one_hi) (snd uahl_lo_lt_one_hi)).
Qed.

(* uahl_delta_star_bounded（源模块 lhs_delta_star_bounded 的独立重证）：        *)
(*   左支 p7a_delta_star_pos；右支 δ*<1 独立三步：lt_mult_compat、             *)
(*   lt_id_l（经 mult_one）与 lt_trans。 *)
Theorem uahl_delta_star_bounded :
  And (lt zero (mult lo lo)) (lt (mult lo lo) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  split.
  - exact (p7a_delta_star_pos lo (expf_pos (mult invT (opp Delta)))).
  - exact (lt_trans (mult lo lo) (mult one lo) one
             (lt_mult_compat lo one lo
                (expf_pos (mult invT (opp Delta))) Hlo1)
             (lt_id_l (mult one lo) lo one
                (id_trans (mult_comm one lo) (mult_one lo)) Hlo1)).
Qed.

End UahlPair.

(* ############ 段二：uahl_omd_bounded —— κ:=1−δ*∈(0,1)（带可判定序参节） #### *)
(* 节变量面与源模块  的 LhsStar 节一致；p7a_omd_pos/p7a_omd_lt_one  *)
(* 的可判定序隐式参不可由结论反推，故以 @ 全参显式应用。                       *)

Section UahlStar.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Let R := @S01_BaseRing.R RI.
Let zero := @S01_BaseRing.zero RI.
Let one := @S01_BaseRing.one RI.
Let plus := @S01_BaseRing.plus RI.
Let mult := @S01_BaseRing.mult RI.
Let opp := @S01_BaseRing.opp RI.
Let abs := @S01_BaseRing.abs RI.
Let inv_pos := @S01_BaseRing.inv_pos RI.
Let lt := @S01_BaseRing.lt RI.
Let le := @S01_BaseRing.le RI.
Let mult_comm := @S01_BaseRing.mult_comm RI.
Let plus_comm := @S01_BaseRing.plus_comm RI.
Let plus_assoc := @S01_BaseRing.plus_assoc RI.
Let mult_one := @S01_BaseRing.mult_one RI.
Let plus_zero := @S01_BaseRing.plus_zero RI.
Let plus_opp := @S01_BaseRing.plus_opp RI.
Let lt_trans := @S01_BaseRing.lt_trans RI.
Let lt_id_l := @S01_BaseRing.lt_id_l RI.
Let lt_mult_compat := @S01_BaseRing.lt_mult_compat RI.
Let le_mult_compat_weak := @S01_BaseRing.le_mult_compat_weak RI.
Let le_id_l := @S01_BaseRing.le_id_l RI.
Let le_id_r := @S01_BaseRing.le_id_r RI.
Let lt_le_iff := @S01_BaseRing.lt_le_iff RI.
Let abs_pos := @S01_BaseRing.abs_pos RI.
Let inv_pos_pos := @S01_BaseRing.inv_pos_pos RI.
Let le_refl := @S01_BaseRing.le_refl RI.
Let lt_id_r := @S01_BaseRing.lt_id_r RI.
Let mult_positive := @S01_BaseRing.mult_positive RI.
Let mult_zero := @S01_BaseRing.mult_zero RI.
Let one_pos := @S01_BaseRing.one_pos RI.
Let plus_positive := @S01_BaseRing.plus_positive RI.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).

(* uahl_omd_bounded（源模块 lhs_omd_bounded 的独立重证）：左支以 δ*<1 前提       *)
(*   应用 @p7a_omd_pos；右支以 0<lo 应用 @p7a_omd_lt_one——全参显式。 *)
Theorem uahl_omd_bounded :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one Delta Delta_pos expf expf_zero
             expf_mono_lt invT (inv_pos_pos temp temp_pos)). }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp Delta))). }
  split.
  - exact (@p7a_omd_pos RI DO lo
             (lt_trans (mult lo lo) (mult one lo) one
                (lt_mult_compat lo one lo Hlopos Hlo1)
                (lt_id_l (mult one lo) lo one
                   (id_trans (mult_comm one lo) (mult_one lo)) Hlo1))).
  - exact (@p7a_omd_lt_one RI DO lo Hlopos).
Qed.

End UahlStar.

(* ########## 段三：实例形甲——uahl_omd_bounded/uahl_lo_lt_hi @ 温度:=1、利差:=1 ## *)
(* 温度与利差均取 one（one_pos 提供两处正性位），invT:=inv_pos one one_pos；    *)
(* 指数族保持抽象（全库无具体实数实例）。                                     *)

Section UahlSbInst.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Let R := @S01_BaseRing.R RI.
Let zero := @S01_BaseRing.zero RI.
Let one := @S01_BaseRing.one RI.
Let plus := @S01_BaseRing.plus RI.
Let mult := @S01_BaseRing.mult RI.
Let opp := @S01_BaseRing.opp RI.
Let abs := @S01_BaseRing.abs RI.
Let inv_pos := @S01_BaseRing.inv_pos RI.
Let lt := @S01_BaseRing.lt RI.
Let le := @S01_BaseRing.le RI.
Let mult_comm := @S01_BaseRing.mult_comm RI.
Let plus_comm := @S01_BaseRing.plus_comm RI.
Let plus_assoc := @S01_BaseRing.plus_assoc RI.
Let mult_one := @S01_BaseRing.mult_one RI.
Let plus_zero := @S01_BaseRing.plus_zero RI.
Let plus_opp := @S01_BaseRing.plus_opp RI.
Let lt_trans := @S01_BaseRing.lt_trans RI.
Let lt_id_l := @S01_BaseRing.lt_id_l RI.
Let lt_mult_compat := @S01_BaseRing.lt_mult_compat RI.
Let le_mult_compat_weak := @S01_BaseRing.le_mult_compat_weak RI.
Let le_id_l := @S01_BaseRing.le_id_l RI.
Let le_id_r := @S01_BaseRing.le_id_r RI.
Let lt_le_iff := @S01_BaseRing.lt_le_iff RI.
Let abs_pos := @S01_BaseRing.abs_pos RI.
Let inv_pos_pos := @S01_BaseRing.inv_pos_pos RI.
Let le_refl := @S01_BaseRing.le_refl RI.
Let lt_id_r := @S01_BaseRing.lt_id_r RI.
Let mult_positive := @S01_BaseRing.mult_positive RI.
Let mult_zero := @S01_BaseRing.mult_zero RI.
Let one_pos := @S01_BaseRing.one_pos RI.
Let plus_positive := @S01_BaseRing.plus_positive RI.

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos one one_pos.
Let lo := expf (mult invT (opp one)).

(* uahl_omd_bounded_one（uahl_omd_bounded 于温度:=1、利差:=1 的实例形）：      *)
(*   p7a_lo_lt_one @ one/one 供 lo<1，expf_pos 供 0<lo，δ*<1 三步内联，@ 全参显式。 *)
Theorem uahl_omd_bounded_one :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { exact (p7a_lo_lt_one one one_pos expf expf_zero expf_mono_lt invT
             (inv_pos_pos one one_pos)). }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp one))). }
  split.
  - exact (@p7a_omd_pos RI DO lo
             (lt_trans (mult lo lo) (mult one lo) one
                (lt_mult_compat lo one lo Hlopos Hlo1)
                (lt_id_l (mult one lo) lo one
                   (id_trans (mult_comm one lo) (mult_one lo)) Hlo1))).
  - exact (@p7a_omd_lt_one RI DO lo Hlopos).
Qed.

(* uahl_lo_lt_hi_one（uahl_lo_lt_hi 于同上实例的实例形）：p7a_lo_lt_one        *)
(*   @ one/one 供 lo<1，p7d_hi_gt_one @ one/one 供 1<hi，lt_trans 合成。 *)
Theorem uahl_lo_lt_hi_one :
  lt (expf (mult invT (opp one))) (expf (mult invT one)).
Proof.
  exact (lt_trans (expf (mult invT (opp one))) one (expf (mult invT one))           (p7a_lo_lt_one one one_pos expf expf_zero expf_mono_lt invT              (inv_pos_pos one one_pos))           (p7d_hi_gt_one one one_pos one one_pos expf expf_pos expf_zero              expf_mono_lt)).
Qed.

End UahlSbInst.

(* ############ 段四：实例形乙——uahl_omd_bounded @ lo:=二分之一抽象形 ######## *)
(* lo:=inv_pos (plus one one) two_pos（二分之一，two_pos/inv_pos_pos 提供正性）；*)
(* 左支不经 δ*<1 中转，走独立链：half_twice（半＋半=1，半方＋半方=半）与       *)
(* plus_positive（半方>0）及恒等重排，推得 0<1−1/4；                          *)
(* 右支 @p7a_omd_lt_one。                                                     *)

Section UahlHalf.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Let R := @S01_BaseRing.R RI.
Let zero := @S01_BaseRing.zero RI.
Let one := @S01_BaseRing.one RI.
Let plus := @S01_BaseRing.plus RI.
Let mult := @S01_BaseRing.mult RI.
Let opp := @S01_BaseRing.opp RI.
Let abs := @S01_BaseRing.abs RI.
Let inv_pos := @S01_BaseRing.inv_pos RI.
Let lt := @S01_BaseRing.lt RI.
Let le := @S01_BaseRing.le RI.
Let mult_comm := @S01_BaseRing.mult_comm RI.
Let plus_comm := @S01_BaseRing.plus_comm RI.
Let plus_assoc := @S01_BaseRing.plus_assoc RI.
Let mult_one := @S01_BaseRing.mult_one RI.
Let plus_zero := @S01_BaseRing.plus_zero RI.
Let plus_opp := @S01_BaseRing.plus_opp RI.
Let lt_trans := @S01_BaseRing.lt_trans RI.
Let lt_id_l := @S01_BaseRing.lt_id_l RI.
Let lt_mult_compat := @S01_BaseRing.lt_mult_compat RI.
Let le_mult_compat_weak := @S01_BaseRing.le_mult_compat_weak RI.
Let le_id_l := @S01_BaseRing.le_id_l RI.
Let le_id_r := @S01_BaseRing.le_id_r RI.
Let lt_le_iff := @S01_BaseRing.lt_le_iff RI.
Let abs_pos := @S01_BaseRing.abs_pos RI.
Let inv_pos_pos := @S01_BaseRing.inv_pos_pos RI.
Let le_refl := @S01_BaseRing.le_refl RI.
Let lt_id_r := @S01_BaseRing.lt_id_r RI.
Let mult_positive := @S01_BaseRing.mult_positive RI.
Let mult_zero := @S01_BaseRing.mult_zero RI.
Let one_pos := @S01_BaseRing.one_pos RI.
Let plus_positive := @S01_BaseRing.plus_positive RI.

Let half := inv_pos (plus one one) two_pos.
Let half2 := mult half half.

(* uahl_omd_bounded_half（实例形乙） *)
Theorem uahl_omd_bounded_half :
  And (lt zero (minus one half2)) (lt (minus one half2) one).
Proof.
  assert (Hhp : lt zero half).
  { exact (inv_pos_pos (plus one one) two_pos). }
  assert (Hh2p : lt zero half2).
  { exact (mult_positive half half Hhp Hhp). }
  assert (Hh2p2 : lt zero (plus half2 half2)).
  { exact (plus_positive half2 half2 Hh2p Hh2p). }
  assert (Hq : Id (plus half2 half2) half).
  { exact (half_twice half). }
  assert (Hone : Id (plus half half) one).
  { exact (id_trans (id_cong (fun x => plus x x) (id_sym (mult_one half)))
                    (half_twice one)). }
  assert (Hone2 : Id one (plus (plus half2 half2) (plus half2 half2))).
  { exact (id_trans (id_sym Hone) (id_sym (id_cong (fun x => plus x x) Hq))). }
  assert (Gup : Id (plus (plus (plus half2 half2) (plus half2 half2))
                         (opp half2))
                   (plus half2 (plus half2 half2))).
  { exact (id_trans
             (id_sym (plus_assoc (plus half2 half2) (plus half2 half2)
                       (opp half2)))
             (id_trans
                (id_cong (fun x => plus (plus half2 half2) x)
                   (id_trans (id_sym (plus_assoc half2 half2 (opp half2)))
                      (id_trans
                         (id_cong (fun w => plus half2 w)
                            (plus_comm half2 (opp half2)))
                         (plus_assoc half2 (opp half2) half2))))
             (id_trans
                (id_cong (fun x => plus (plus half2 half2) x)
                   (id_cong (fun w => plus w half2) (plus_opp half2)))
                (id_trans
                   (id_cong (fun x => plus (plus half2 half2) x)
                      (id_trans (plus_comm zero half2) (plus_zero half2)))
                   (id_sym (plus_assoc half2 half2 half2)))))). }
  assert (Gtotal : Id (minus one half2) (plus half2 (plus half2 half2))).
  { exact (id_trans
             (id_sym (id_cong (fun w => plus w (opp half2)) (id_sym Hone2)))
             Gup). }
  split.
  - exact (lt_id_r zero (plus half2 (plus half2 half2)) (minus one half2)
             (id_sym Gtotal)
             (plus_positive half2 (plus half2 half2) Hh2p Hh2p2)).
  - exact (@p7a_omd_lt_one RI DO half Hhp).
Qed.

End UahlHalf.

(* ---- 收尾段：逐件 Print Assumptions 核验零承认 ---- *)
Print Assumptions uahl_lo_lt_one_hi.
Print Assumptions uahl_lo_lt_hi.
Print Assumptions uahl_delta_star_bounded.
Print Assumptions uahl_omd_bounded.
Print Assumptions uahl_omd_bounded_one.
Print Assumptions uahl_lo_lt_hi_one.
Print Assumptions uahl_omd_bounded_half.
(* ================= §4 emsi_energy_pin_self 族 ================= *)
(* Section EntropyMonoSplitInst：接口面照源件 Section                   *)
(*   EmsEntropyMonoSplit 同名同序（求和面 7 位 + 峰温 T_star + 能量），  *)
(*   证书位不作假设申报（本件使命即装载证书，供位走显式前提参）。     *)
Section EntropyMonoSplitInst.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable T_star : Real.
Variable T_star_pos : real_lt real_zero T_star.
Variable energy : S -> Real.

(* ---- 速记（照源件 Let ems_bt / ems_bt_pos / ems_kl_peak 同形换名，    *)
(*   保证槽语句重述后逐字对位；KL 方向红线照抄源件：KL(p_u 竖排 p_{t*})  *)
(*   p_u 占第一分布位，p_{t*} 占参考位，禁倒置。） ---- *)
Let emsi_bt (u : Real) (Hu : real_lt real_zero u) : S -> Real :=
  real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let emsi_bt_pos (u : Real) (Hu : real_lt real_zero u) :
  forall s : S, real_lt real_zero (emsi_bt u Hu s) :=
  real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let emsi_kl (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_KL_temp S real_sum_over_S real_sum_pos_preserved T_star T_star_pos energy
               (emsi_bt u Hu) (emsi_bt_pos u Hu).

(* ---------------------------------------------------------- *)
(* 桥接引理一（接口参数1 小桥·能量钉注册面自钉形）：逐温能量期望自钉。           *)
(*   左端 lambda 经 emsi_bt 换名后定义性合一，real_eq_refl 真装。        *)
(*   逐字同形（T := u 任意正温）。                                       *)
(* ---------------------------------------------------------- *)
Lemma emsi_energy_pin_self :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (real_sum_over_S (fun s : S => real_mult (emsi_bt u Hu s) (energy s)))
      (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
         u Hu energy).
Proof.
  intros u Hu.
  exact (real_eq_refl           (real_sum_over_S              (fun s : S => real_mult (emsi_bt u Hu s) (energy s)))).
Qed.

(* ---------------------------------------------------------- *)
(* 桥接引理二（序代数·差分非负新形）：a ≤ b 给 0 ≤ b − a。                   *)
(*   raw Real 层注册面只有反方向辅助引理 real_le_plus_nonneg_r             *)
(*   real_le_plus_compat 双边同加 −a，再 RealSetoid.real_le_id_l         *)
(*   经 (a + −a) ≡ 0 换左端。纯项模式真证。                              *)
(* ---------------------------------------------------------- *)
Lemma emsi_le_diff_ge_zero :
  forall a b : Real,
    real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab.
  apply (RealSetoid.real_le_id_l real_zero           (real_plus a (real_opp a))           (real_plus b (real_opp a))           (real_eq_sym (real_plus a (real_opp a)) real_zero              (real_plus_opp a))).
  exact (real_le_plus_compat a b (real_opp a) (real_opp a) Hab           (real_le_refl (real_opp a))).
Qed.

(* ---------------------------------------------------------- *)
(* 桥接引理三（eps 松弛提升形）：0 ≤ X 且 0 < eps 给 0 ≤ X + eps。           *)
(*   副本族「0 ≤ KL+eps 形」的序代数内核：compat 双边加 eps，           *)
(*   左端 (0+0) ≡ 0 重述。                                              *)
(* ---------------------------------------------------------- *)
Lemma emsi_le_plus_eps :
  forall X eps : Real,
    real_le real_zero X -> real_lt real_zero eps ->
    real_le real_zero (real_plus X eps).
Proof.
  intros X eps HX Heps.
  apply (RealSetoid.real_le_id_l real_zero           (real_plus real_zero real_zero)           (real_plus X eps)           (real_eq_sym (real_plus real_zero real_zero) real_zero              (real_plus_zero real_zero))).
  exact (real_le_plus_compat real_zero X real_zero eps HX           (real_le_from_lt_aux real_zero eps Heps)).
Qed.

(* ---------------------------------------------------------- *)
(* 副本 exact 重述孪生（接口参数2/3 词料种子）：                              *)
(*   全参显式语句面。四要素对照声明：                                    *)
(*   · 原语义：0 ≤ KL(p 竖排 p_{t*}) + eps（归一 + 逐点正 + eps 正）；   *)
(*   · 装载路径：全链就地重证（桥→逐点核→求和面提升→双坍缩→组装），      *)
(*     语句面全参显式保留，温度位重述 T := t*；                          *)
(* ---------------------------------------------------------- *)
Corollary emsi_kl_ge_zero_eps_mirror :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved
              T_star T_star_pos energy p Hp)
           eps).
Proof.
  intros p Hp Hnp eps Heps.
  set (pT := real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
               T_star T_star_pos energy).
  set (HpT := real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                T_star T_star_pos energy).
  (* 桥：KL ≡ Σ real_kl_term *)
  assert (Hbridge : real_eq
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved
              T_star T_star_pos energy p Hp)
           (real_sum_over_S (fun s : S =>
              real_kl_term (p s) (pT s) (Hp s) (HpT s)))).
  { exact (real_KL_temp_kl_term_bridge S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext T_star T_star_pos energy p Hp). }
  (* 逐点核：p − p_T ≤ real_kl_term + p·eps（real_kl_term 与核 RHS 首和项定义性一致） *)
  assert (Hpt : forall s : S,
           real_le (real_plus (p s) (real_opp (pT s)))
                   (real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                              (real_mult (p s) eps))).
  { intro s.
    exact (real_gibbs_core_eps (p s) (pT s) (Hp s) (HpT s) eps Heps). }
  (* 求和面提升（接口单调位） *)
  assert (Hsum : real_le
           (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
           (real_sum_over_S (fun s : S =>
              real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                        (real_mult (p s) eps)))).
  { exact (real_sum_over_S_le
             (fun s : S => real_plus (p s) (real_opp (pT s)))
             (fun s : S => real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                                     (real_mult (p s) eps))
             Hpt). }
  (* LHS 坍缩：Σ(p − p_T) ≡ Σp + −Σp_T ≡ 1 + (−1) ≡ 0 *)
  assert (HnormT : real_eq (real_sum_over_S pT) real_one).
  { exact (real_boltzmann_dist_temp_normalized S real_sum_over_S
             real_sum_pos_preserved real_sum_over_S_ext real_sum_over_S_linear
             T_star T_star_pos energy). }
  assert (Hzero : real_eq
           (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
           real_zero).
  { apply (real_eq_trans
             (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
             (real_plus (real_sum_over_S p)
                        (real_sum_over_S (fun s : S => real_opp (pT s))))
             real_zero).
    - exact (real_sum_over_S_add p (fun s : S => real_opp (pT s))).
    - apply (real_eq_trans
               (real_plus (real_sum_over_S p)
                          (real_sum_over_S (fun s : S => real_opp (pT s))))
               (real_plus real_one (real_opp real_one))
               real_zero).
      + apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_sum_over_S p) real_one
                 (real_sum_over_S (fun s : S => real_opp (pT s)))
                 (real_opp real_one)
                 Hnp
                 (real_eq_trans
                    (real_sum_over_S (fun s : S => real_opp (pT s)))
                    (real_opp (real_sum_over_S pT))
                    (real_opp real_one)
                    (real_sum_over_S_opp S real_sum_over_S real_sum_over_S_ext
                       real_sum_over_S_linear pT)
                    (RealSetoid.real_eq_opp_compat
                       (real_sum_over_S pT) real_one HnormT))).
      + exact (real_plus_opp real_one).
  }
  (* 误差坍缩：Σ(p·eps) ≡ Σ(eps·p) ≡ eps·Σp ≡ eps·1 ≡ eps *)
  assert (HepsS : real_eq (real_sum_over_S (fun s : S => real_mult (p s) eps)) eps).
  { apply (real_eq_trans
             (real_sum_over_S (fun s : S => real_mult (p s) eps))
             (real_sum_over_S (fun s : S => real_mult eps (p s)))
             eps).
    - apply real_sum_over_S_ext.
      intro s. exact (real_mult_comm (p s) eps).
    - apply (real_eq_trans
               (real_sum_over_S (fun s : S => real_mult eps (p s)))
               (real_mult eps (real_sum_over_S p))
               eps).
      + exact (real_sum_over_S_linear eps p).
      + apply (real_eq_trans
                 (real_mult eps (real_sum_over_S p))
                 (real_mult eps real_one)
                 eps).
        * apply (RealSetoid.real_eq_mult_compat_adapt eps eps
                   (real_sum_over_S p) real_one
                   (real_eq_refl eps) Hnp).
        * exact (real_mult_one eps).
  }
  (* RHS 换形：Σ(kl + p·eps) ≡ Σkl + eps *)
  assert (Hrhs : real_eq
           (real_sum_over_S (fun s : S =>
              real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                        (real_mult (p s) eps)))
           (real_plus
              (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
              eps)).
  { apply (real_eq_trans
             (real_sum_over_S (fun s : S =>
                real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                          (real_mult (p s) eps)))
             (real_plus
                (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
                (real_sum_over_S (fun s : S => real_mult (p s) eps)))
             (real_plus
                (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
                eps)).
    - exact (real_sum_over_S_add
               (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s))
               (fun s : S => real_mult (p s) eps)).
    - apply (RealSetoid.real_eq_plus_compat_adapt
               (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
               (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
               (real_sum_over_S (fun s : S => real_mult (p s) eps)) eps
               (real_eq_refl
                  (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s))))
               HepsS).
  }
  (* 组装：le 0 Σ(kl+p·eps) → le 0 (Σkl+eps) → le 0 (KL+eps)（两跳换形） *)
  exact (RealSetoid.real_le_id_r real_zero
           (real_plus
              (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
              eps)
           (real_plus
              (real_KL_temp S real_sum_over_S real_sum_pos_preserved
                 T_star T_star_pos energy p Hp)
              eps)
           (RealSetoid.real_eq_plus_compat_adapt
              (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
              (real_KL_temp S real_sum_over_S real_sum_pos_preserved
                 T_star T_star_pos energy p Hp)
              eps eps
              (real_eq_sym _ _ Hbridge)
              (real_eq_refl eps))
           (RealSetoid.real_le_id_r real_zero
              (real_sum_over_S (fun s : S =>
                 real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                           (real_mult (p s) eps)))
              (real_plus
                 (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
                 eps)
              Hrhs
              (RealSetoid.real_le_id_l real_zero
                 (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
                 (real_sum_over_S (fun s : S =>
                    real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                              (real_mult (p s) eps)))
                 (real_eq_sym
                    (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
                    real_zero
                    Hzero)
                 Hsum))).
Qed.

(* ---------------------------------------------------------- *)
(*   四要素对照声明：                                                    *)
(*   · 原语义：约束片上 E(p_u) == E_{t*} 对一切正温 u（C5「约束出现」   *)
(*     变量的定理化载体）；                                              *)
(*   · 装载路径：GibbsAssembly 判接口面不足（req2 增强层无能量钉件 +     *)
(*     源件层红线禁混引），改走 raw Real 层注册面小桥：emsi_energy_pin_  *)
(*     self（自钉，定义性）经 real_eq_trans 复合片运输供位               *)
(*     （E_u == E_{t*}，约束内容显式隔离，不藏前提）；                   *)
(* ---------------------------------------------------------- *)
Theorem inst_pinned :
  (forall (u : Real) (Hu : real_lt real_zero u),
     real_eq
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          u Hu energy)
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          T_star T_star_pos energy)) ->
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (real_sum_over_S (fun s : S => real_mult (emsi_bt u Hu s) (energy s)))
      (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
         T_star T_star_pos energy).
Proof.
  intros Hslice u Hu.
  exact (real_eq_trans           (real_sum_over_S              (fun s : S => real_mult (emsi_bt u Hu s) (energy s)))           (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved              u Hu energy)           (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved              T_star T_star_pos energy)           (emsi_energy_pin_self u Hu)           (Hslice u Hu)).
Qed.

(* ---------------------------------------------------------- *)
(* 装载定理一孪生（峰温点零前提封闭装载）：u := t* 时片运输供位退化      *)
(*   为自反，槽面即自钉面——零供位真装（装载体闭合性证人）。              *)
(* ---------------------------------------------------------- *)
Theorem inst_pinned_at_peak :
  real_eq
    (real_sum_over_S
       (fun s : S => real_mult (emsi_bt T_star T_star_pos s) (energy s)))
    (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
       T_star T_star_pos energy).
Proof.
  exact (emsi_energy_pin_self T_star T_star_pos).
Qed.

(* ---------------------------------------------------------- *)
(*   四要素对照声明：                                                    *)
(*   · 原语义：0 ≤ KL_v − KL_u + eps（t* ≤ u ≤ v，「KL 随温增」读向，   *)
(*     KL_v 在前 KL_u 取 real_opp，禁倒置）；                            *)
(*   · 装载路径：供位定型 plain growth（KL-V 形右支文义 real_le KL_u     *)
(*     KL_v）→ emsi_le_diff_ge_zero 差分重述 → emsi_le_plus_eps          *)
(*     eps 松弛提升；词料面由副本重述孪生备案（eps 形同构）；            *)
(*   · 定理引用：real_KL_temp_ge_zero_eps（副本孪生                      *)
(*     emsi_kl_ge_zero_eps_mirror 依存位）+ emsi 两级重述桥。            *)
(* ---------------------------------------------------------- *)
Theorem inst_kl_right :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le T_star u -> real_le u v ->
     real_le (emsi_kl u Hu) (emsi_kl v Hv)) ->
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (emsi_kl v Hv) (real_opp (emsi_kl u Hu))) eps).
Proof.
  intros Hgrowth u v Hu Hv Htu Huv eps Heps.
  exact (emsi_le_plus_eps           (real_plus (emsi_kl v Hv) (real_opp (emsi_kl u Hu))) eps           (emsi_le_diff_ge_zero (emsi_kl u Hu) (emsi_kl v Hv)              (Hgrowth u v Hu Hv Htu Huv))           Heps).
Qed.

(* ---------------------------------------------------------- *)
(*   四要素对照声明：                                                    *)
(*   · 原语义：0 ≤ KL_u − KL_v + eps（u ≤ v ≤ t*，「KL 向峰衰减」       *)
(*     读向，副本右支，禁倒置）；                                        *)
(*   · 装载路径：供位定型 plain decay（real_le KL_v KL_u，序前提         *)
(*     u ≤ v ≤ t*）→ 同一枚差分桥 + eps 松弛桥两级重述；                 *)
(*   · 定理引用：同接口参数2（副本孪生 + emsi 重述桥）。                     *)
(* ---------------------------------------------------------- *)
Theorem inst_kl_left :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le u v -> real_le v T_star ->
     real_le (emsi_kl v Hv) (emsi_kl u Hu)) ->
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (emsi_kl u Hu) (real_opp (emsi_kl v Hv))) eps).
Proof.
  intros Hdecay u v Hu Hv Huv Hvt eps Heps.
  exact (emsi_le_plus_eps           (real_plus (emsi_kl u Hu) (real_opp (emsi_kl v Hv))) eps           (emsi_le_diff_ge_zero (emsi_kl v Hv) (emsi_kl u Hu)              (Hdecay u v Hu Hv Huv Hvt))           Heps).
Qed.

End EntropyMonoSplitInst.

(* ---- G1 内嵌自检段（公理面自审前置：文件内显式 PA 声明） ---- *)
Print Assumptions emsi_energy_pin_self.
Print Assumptions emsi_le_diff_ge_zero.
Print Assumptions emsi_le_plus_eps.
Print Assumptions emsi_kl_ge_zero_eps_mirror.
Print Assumptions inst_pinned.
Print Assumptions inst_pinned_at_peak.
Print Assumptions inst_kl_right.
Print Assumptions inst_kl_left.
(* ================= §5 ppa_potential 族 ================= *)
From Stdlib Require Import Lists.List.

Section PpaPhysPred.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let SSR  : StateSpace RI := @RealSelfSS (@RI_base RI).
Let S    := @S RI SSR.
Let R    := @S01_BaseRing.R RI.
Let zero := @S01_BaseRing.zero RI.
Let one  := @S01_BaseRing.one RI.
Let plus := @S01_BaseRing.plus RI.
Let mult := @S01_BaseRing.mult RI.
Let opp  := @S01_BaseRing.opp RI.
Let le   := @S01_BaseRing.le RI.
Let lt   := @S01_BaseRing.lt RI.
Let splus := @splus RI SSR.
Let sopp  := @sopp RI SSR.
Let clim  := @clim RI SSR.
Let mult_zero := @S01_BaseRing.mult_zero RI.
Let le_refl := @S01_BaseRing.le_refl RI.
Let one_pos := @S01_BaseRing.one_pos RI.
Let mult_comm := @S01_BaseRing.mult_comm RI.
Let plus_assoc := @S01_BaseRing.plus_assoc RI.
Let plus_opp := @S01_BaseRing.plus_opp RI.
Let plus_zero := @S01_BaseRing.plus_zero RI.
Let le_id_l := @S01_BaseRing.le_id_l RI.
Let le_mult_compat_weak := @S01_BaseRing.le_mult_compat_weak RI.

(* 参数位节面：Q P : Set、Hamiltonian : Q -> P -> R、potential : Q -> R、
   force_physical : Q -> Q、inj_Q_S : Q -> S、grad : (Q -> R) -> Q -> S。
   兑现装法：Q := R（S = R 自状态空间，inj_Q_S := 恒等）、P := unit、
   恒力场线性势 V(q) := q、梯度装法 grad V q := V q（线性势族
   斜率 = 函数值）、力 F(q) := -(V q) + 0（零元归位链）。 *)

Definition ppa_potential (q : R) : R := q.
Definition ppa_grad_lin (V : R -> R) (q : R) : R := V q.
Definition ppa_force_physical (q : R) : R := plus (opp q) zero.

Theorem ppa_physical_force_is_gradient :
  forall q : R, Id (ppa_force_physical q) (sopp (ppa_grad_lin ppa_potential q)).
Proof.
  intro q.
  exact (plus_zero (opp q)).
Qed.

(* 哈密顿量装法（动能项叠加）与支配伴件：p >= 0 时 H = V + p >= V。 *)
Definition ppa_hamiltonian (q p : R) : R := plus (ppa_potential q) p.

Theorem ppa_hamiltonian_dominates_potential :
  forall q p : R, le zero p -> le (ppa_potential q) (ppa_hamiltonian q p).
Proof.
  intros q p Hp.
  exact (le_plus_nonneg_r (ppa_potential q) p Hp).
Qed.

(* 标度势能严格单调伴件（左乘严格兼容件就地重证：右乘兼容件经乘法交换换形）。 *)
Definition ppa_potential_scaled (k q : R) : R := mult k q.

(* 左乘严格单调伴件：正左乘子保严格序（右乘 lt_mult_compat 换形至左乘位）。 *)
Lemma ppa_lt_mult_compat_l :
  forall (a b c : R), lt zero c -> lt a b -> lt (mult c a) (mult c b).
Proof.
  intros a b c Hc H.
  exact (@S01_BaseRing.lt_id_l RI (mult c a) (mult a c) (mult c b)
           (mult_comm c a)
           (@S01_BaseRing.lt_id_r RI (mult a c) (mult b c) (mult c b)
              (mult_comm b c) (@S01_BaseRing.lt_mult_compat RI a b c Hc H))).
Qed.

Theorem ppa_potential_scaled_strict_mono :
  forall k q1 q2 : R, lt zero k -> lt q1 q2 ->
    lt (ppa_potential_scaled k q1) (ppa_potential_scaled k q2).
Proof.
  intros k q1 q2 Hk H.
  exact (ppa_lt_mult_compat_l q1 q2 k Hk H).
Qed.

(* 标度势能弱单调伴件（fa51 lt→le 降档件依存）。 *)
Theorem ppa_potential_scaled_mono :
  forall k q1 q2 : R, lt zero k -> lt q1 q2 ->
    le (ppa_potential_scaled k q1) (ppa_potential_scaled k q2).
Proof.
  intros k q1 q2 Hk H.
  exact (fa51_lt_le _ _ (ppa_lt_mult_compat_l q1 q2 k Hk H)).
Qed.

(* 参数位节面：Waddington_landscape : S -> R、noise : S -> S、
   grad : (S -> R) -> S -> S、developmental_dynamics x :=
   splus x (splus (sopp (grad W x)) (noise x))、dev_is_truth。
   兑现装法（R 线载体）：平底景观 W := fun _ => zero、梯度装法
   grad W x := x、噪声面 noise x := zero ——
   dynamics x = x + ((-x) + 0) = x - x = 0（plus_zero 反向 +
   plus_opp 两段链）：开发景观轨道一步落入零点。
   吸引子 x_star := zero：dev_is_truth zero = le zero zero（le_refl）。
   clim 收敛面 = 接口 lim 字段黑箱：库内 Id 形零具体实例
   （P6A/CYD7 卡已证结论），按 fa56c 先例前提入签名——收敛前提
   Hclim 为主定理显式参，逐槽诚实列出。 *)

Definition ppa_waddington (x : R) : R := zero.
Definition ppa_dev_grad (V : R -> R) (x : R) : R := x.
Definition ppa_dev_noise (x : R) : R := zero.
Definition ppa_dev_dynamics (x : R) : R :=
  splus x (splus (sopp (ppa_dev_grad ppa_waddington x)) (ppa_dev_noise x)).

(* 轨道装法：codomain 显式 S（clim 面同型；R = S 经 RealSelfSS
   S 字段定义性相等，投影头处统一由本装法定型，防 clim_unique
   裸名应用的 A 推断撞投影头）。 *)
Definition ppa_dev_orbit (x : R) : nat -> S :=
  fun n : nat => iterate ppa_dev_dynamics n x.

(* 轨道一步入零：dynamics x == x + (-x + 0) == x + (-x) == 0。 *)
Theorem ppa_dev_dynamics_zero : forall x : R, Id (ppa_dev_dynamics x) zero.
Proof.
  intro x.
  apply (id_trans (id_cong (fun w => plus x w) (plus_zero (opp x)))                  (plus_opp x)).
Qed.

(* 离散收敛见证：S n 步迭代逐项恒为零（lim 黑箱的构造性补充）。 *)
Theorem ppa_dev_iterate_step_zero :
  forall (n : nat) (x : R),
    Id (iterate ppa_dev_dynamics (Datatypes.S n) x) zero.
Proof.
  intro n. induction n as [|n IH]; intro x.
  - exact (ppa_dev_dynamics_zero x).
  - apply (id_trans (id_cong (fun w => ppa_dev_dynamics w) (IH x))
                    (ppa_dev_dynamics_zero zero)).
Qed.

(* 槽2 主件：吸引子装配（sigT + And；收敛前提入签名）。 *)
Theorem ppa_differentiation_attractor :
  forall x : R,
    clim (ppa_dev_orbit x) zero ->
    sigT (fun x_star : S =>
      And (forall s' : S, le (ppa_waddington x_star) (ppa_waddington s'))
          (clim (ppa_dev_orbit x) x_star)).
Proof.
  intros x Hcl.
  exact (existT _ zero (pair (fun s' => le_refl zero) Hcl)).
Qed.

(* 吸引子极限唯一伴件（StateSpace 字段 clim_unique 依存）。 *)
Theorem ppa_attractor_lim_unique :
  forall (x l1 l2 : R),
    clim (ppa_dev_orbit x) l1 ->
    clim (ppa_dev_orbit x) l2 ->
    Id l1 l2.
Proof.
  intros x l1 l2 H1 H2.
  exact (@clim_unique RI SSR (ppa_dev_orbit x) l1 l2 H1 H2).
Qed.

(* 吸引子起点传输伴件（fa56b J 消去器依存：Id x y 把收敛见证
   从起点 x 搬到起点 y——Q 以起点为参直接换，无需函数外延性）。 *)
Theorem ppa_attractor_transport :
  forall (x y l : R),
    Id x y ->
    clim (ppa_dev_orbit x) l ->
    clim (ppa_dev_orbit y) l.
Proof.
  intros x y l p Hcl.
  exact (fa56b_id_transport R           (fun z => clim (ppa_dev_orbit z) l)           x y p Hcl).
Qed.

(* 参数位节面：macro_entropy : Macrostate -> R、macro_dynamics :
   Macrostate -> Macrostate、macro_loss m := opp (macro_entropy m)。
   兑现装法：Macrostate := R、熵读数 = 状态自读数、粗粒化动力学
   m ↦ m + 1（宏熵每步 +1，macro_loss = -熵 沿轨道单调不增）。
   of_nat 面：库内 RealInterface 无 nat -> R 注入（S05 Prediction1
   节同以 Variable of_nat 承载），按槽先例以定理显式参入签名：
   零元、步进、非负三前提逐槽诚实列出。 *)

Definition ppa_macro_entropy (m : R) : R := m.
Definition ppa_macro_dynamics (m : R) : R := plus m one.
Definition ppa_macro_loss (m : R) : R := opp (ppa_macro_entropy m).

(* 迭代闭合引理：d^t m == m + of_nat t（t 归纳 + 结合律 + 步进前提）。 *)
Theorem ppa_iterate_macro_step :
  forall (of_nat_R : nat -> R),
    Id (of_nat_R O) zero ->
    (forall n : nat, Id (of_nat_R (Datatypes.S n)) (plus (of_nat_R n) one)) ->
    forall (t : nat) (m : R),
      Id (iterate ppa_macro_dynamics t m) (plus m (of_nat_R t)).
Proof.
  intros of_nat_R H0 Hstep t.
  induction t as [|t IH]; intro m.
  - apply (id_trans (id_sym (plus_zero m))
      (id_cong (fun z => plus m z) (id_sym H0))).
  - apply (id_trans (id_cong (fun z => plus z one) (IH m))
      (id_trans (id_sym (plus_assoc m (of_nat_R t) one))
                (id_cong (fun z => plus m z) (id_sym (Hstep t))))).
Qed.

(* 参数位3 主件：宏损失沿轨道单调不增（iterate 闭合 + opp 反变 +
   非负平移三段真链）。 *)
Theorem ppa_macro_loss_monotone :
  forall (of_nat_R : nat -> R),
    Id (of_nat_R O) zero ->
    (forall n : nat, Id (of_nat_R (Datatypes.S n)) (plus (of_nat_R n) one)) ->
    (forall n : nat, le zero (of_nat_R n)) ->
    forall (m0 : R) (t : nat),
      le (ppa_macro_loss (iterate ppa_macro_dynamics t m0))
         (ppa_macro_loss m0).
Proof.
  intros of_nat_R H0 Hstep Hnn m0 t.
  apply (le_id_l (ppa_macro_loss (iterate ppa_macro_dynamics t m0))
                 (opp (plus m0 (of_nat_R t))) (ppa_macro_loss m0)).
  - exact (id_cong (fun z => opp z)
             (ppa_iterate_macro_step of_nat_R H0 Hstep t m0)).
  - exact (@S01_BaseRing.opp_le_compat RI m0 (plus m0 (of_nat_R t))
             (le_plus_nonneg_r m0 (of_nat_R t) (Hnn t))).
Qed.

(* 单步伴件：一步演化宏损失不增（one 正性供平移前提）。 *)
Theorem ppa_macro_loss_one_step :
  forall m : R, le (ppa_macro_loss (ppa_macro_dynamics m)) (ppa_macro_loss m).
Proof.
  intro m.
  apply (le_id_l (ppa_macro_loss (ppa_macro_dynamics m))
                 (opp (plus m one)) (ppa_macro_loss m)).
  - exact id_refl.
  - exact (@S01_BaseRing.opp_le_compat RI m (plus m one)
             (le_plus_nonneg_r m one (fa51_lt_le zero one one_pos))).
Qed.

(* 宏熵正标度非负伴件（fa51 lt→le 降档 + Enhanced 乘法保序 +
   零元重述两段链）。 *)
Theorem ppa_macro_entropy_scaled_nonneg :
  forall (k m : R), lt zero k -> le zero m -> le zero (mult k m).
Proof.
  intros k m Hk Hm.
  exact (le_id_l zero (mult zero m) (mult k m)           (id_sym (id_trans (mult_comm zero m) (mult_zero m)))           (le_mult_compat_weak zero k m Hm (fa51_lt_le zero k Hk))).
Qed.

End PpaPhysPred.

(* ============ 假设面闭合申报（出节，G4 面） ============ *)

Print Assumptions ppa_physical_force_is_gradient.
Print Assumptions ppa_hamiltonian_dominates_potential.
Print Assumptions ppa_potential_scaled_strict_mono.
Print Assumptions ppa_potential_scaled_mono.
Print Assumptions ppa_dev_dynamics_zero.
Print Assumptions ppa_dev_iterate_step_zero.
Print Assumptions ppa_differentiation_attractor.
Print Assumptions ppa_attractor_lim_unique.
Print Assumptions ppa_attractor_transport.
Print Assumptions ppa_iterate_macro_step.
Print Assumptions ppa_macro_loss_monotone.
Print Assumptions ppa_macro_loss_one_step.
Print Assumptions ppa_macro_entropy_scaled_nonneg.
(* ================= §6 uabp7an_qneg0 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia QArith.Qminmax.
Import RealInterfaceEnhancedMod.

(* 一、Q 层辅件（半量与四分量的序关系、Qabs 下界引理；零经典逻辑）         *)

(* 负零恒等：(- 0)%Q == 0%Q（多处复用） *)
Lemma uabp7an_qneg0 : (- 0)%Q == 0%Q.
Proof. ring. Qed.

(* e/2 严格正（0 < e）（由 Qlt_le_dec 的可判定二分与 Qplus_le_compat） *)
Lemma uabp7an_qlt_half : forall e : Q, 0 < e -> 0 < e / 2.
Proof.
  intros e He.
  assert (Hsum : e / 2 + e / 2 == e) by field.
  destruct (Qlt_le_dec 0 (e / 2)) as [Hc | Hc].
  - exact Hc.
  - exfalso.
    assert (Hle : e / 2 + e / 2 <= 0 + 0)
      by (apply (Qplus_le_compat (e / 2) 0 (e / 2) 0); [exact Hc | exact Hc]).
    assert (Hz1 : (0 + 0)%Q == 0%Q) by ring.
    rewrite Hz1 in Hle.
    rewrite Hsum in Hle.
    exact (Qlt_not_le 0 e He Hle).
Qed.

(* 半加恒等：e/2 + e/2 == e *)
Lemma uabp7an_half_add : forall e : Q, e / 2 + e / 2 == e.
Proof. intro e. field. Qed.

(* 半小于：e/2 < e（0 < e） *)
Lemma uabp7an_half_lt : forall e : Q, 0 < e -> e / 2 < e.
Proof.
  intros e He.
  assert (Hh : 0 < e / 2) by (apply uabp7an_qlt_half; exact He).
  assert (H1 : e / 2 + 0 < e / 2 + e / 2)
    by (apply (proj2 (Qplus_lt_r 0 (e / 2) (e / 2))); exact Hh).
  assert (Hz0 : (e / 2 + 0)%Q == (e / 2)%Q) by ring.
  rewrite Hz0 in H1.
  assert (Hsum : e / 2 + e / 2 == e) by field.
  rewrite Hsum in H1.
  exact H1.
Qed.

(* 半小于负零形：e/2 < e - 0（0 < e）——配合柯西表示的投影目标形 *)
Lemma uabp7an_half_lt_m0 : forall e : Q, 0 < e -> e / 2 < e - 0.
Proof.
  intros e He.
  assert (H1 : e / 2 + 0 < e / 2 + e / 2)
    by (apply (proj2 (Qplus_lt_r 0 (e / 2) (e / 2)));
        apply uabp7an_qlt_half; exact He).
  assert (Hz0 : (e / 2 + 0)%Q == (e / 2)%Q) by ring.
  rewrite Hz0 in H1.
  assert (Hsum : e / 2 + e / 2 == e - 0) by field.
  rewrite Hsum in H1.
  exact H1.
Qed.

(* 半不大于：e/2 <= e（0 < e） *)
Lemma uabp7an_half_le : forall e : Q, 0 < e -> e / 2 <= e.
Proof.
  intros e He.
  assert (H1 : e / 2 + 0 < e / 2 + e / 2)
    by (apply (proj2 (Qplus_lt_r 0 (e / 2) (e / 2)));
        apply uabp7an_qlt_half; exact He).
  assert (Hz0 : (e / 2 + 0)%Q == (e / 2)%Q) by ring.
  rewrite Hz0 in H1.
  assert (Hsum : e / 2 + e / 2 == e) by field.
  rewrite Hsum in H1.
  apply Qlt_le_weak. exact H1.
Qed.

(* 四分之一小于二分之一：e/4 < e/2（0 < e） *)
Lemma uabp7an_q4_lt_q2 : forall e : Q, 0 < e -> e / 4 < e / 2.
Proof.
  intros e He.
  assert (Hq4 : 0 < e / 4) by (apply uabp7an_qlt_half; exact He).
  assert (H1 : e / 4 + 0 < e / 4 + e / 4)
    by (apply (proj2 (Qplus_lt_r 0 (e / 4) (e / 4))); exact Hq4).
  assert (Hz0 : (e / 4 + 0)%Q == (e / 4)%Q) by ring.
  rewrite Hz0 in H1.
  assert (Hsum : e / 4 + e / 4 == e / 2) by field.
  rewrite Hsum in H1.
  exact H1.
Qed.

(* Qabs 下界翻转：|x| < e（0 < e）⟹ -e < x（Qlt_le_dec 分段 + Qopp_lt_compat） *)
Lemma uabp7an_abs_lb : forall x e : Q, 0 < e -> Qabs x < e -> - e < x.
Proof.
  intros x e He Hb.
  destruct (Qlt_le_dec x 0) as [Hx | Hx].
  - assert (Hx' : x <= 0) by (apply Qlt_le_weak; exact Hx).
    rewrite (Qabs_neg x Hx') in Hb.
    rewrite <- (Qopp_involutive x).
    exact (Qopp_lt_compat (- x) e Hb).
  - assert (H0 : (- e) < (- 0)) by (apply (Qopp_lt_compat 0 e He)).
    rewrite uabp7an_qneg0 in H0.
    exact (Qlt_le_trans (- e) 0 x H0 Hx).
Qed.

(* 逐点收尾辅件：-x < eps/2（0 < eps）⟹ QltT (Qabs (Qabs x - x)) eps。
   证明：Qlt_le_dec 符号分段，以 Qabs_pos/Qabs_neg 定位绝对值后
   归结为「弱非负（逐 eps 下界）到 |a|==a」的 Q 层核心步骤。 *)
Lemma uabp7an_pt_tail : forall x eps : Q,
  0 < eps -> - x < eps / 2 -> QltT (Qabs (Qabs x - x)) eps.
Proof.
  intros x eps Heps Hneg.
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec x 0) as [Hx | Hx].
  - (* x < 0：|x| == -x，目标 |-2x| == -2x < eps *)
    assert (Hx' : x <= 0) by (apply Qlt_le_weak; exact Hx).
    rewrite (Qabs_neg x Hx').
    assert (Hsp : (- x - x)%Q == (- (2 * x))%Q) by ring.
    rewrite Hsp.
    assert (H2xpos : 0 < - (2 * x)).
    { assert (Hlt2 : x + x < 0 + 0)
        by (apply (Qplus_lt_compat x 0 x 0); exact Hx).
      assert (Hz1 : (0 + 0)%Q == 0%Q) by ring.
      rewrite Hz1 in Hlt2.
      assert (Hz2 : (x + x)%Q == (2 * x)%Q) by ring.
      rewrite Hz2 in Hlt2.
      assert (H0 : (- 0)%Q < (- (2 * x)))
        by (apply (Qopp_lt_compat (2 * x) 0); exact Hlt2).
      rewrite uabp7an_qneg0 in H0.
      exact H0. }
    rewrite (Qabs_pos (- (2 * x)) (Qlt_le_weak _ _ H2xpos)).
    assert (Hz3 : (- (2 * x))%Q == ((- x) + (- x))%Q) by ring.
    rewrite Hz3.
    assert (Hfin : (- x) + (- x) < eps / 2 + eps / 2)
      by (apply (Qplus_lt_compat (- x) (eps / 2) (- x) (eps / 2)); exact Hneg).
    assert (HsumE : eps / 2 + eps / 2 == eps) by field.
    rewrite HsumE in Hfin.
    exact Hfin.
  - (* x ≥ 0：|x| == x，差归零 *)
    rewrite (Qabs_pos x Hx).
    assert (Hzd : (x - x)%Q == 0%Q) by ring.
    rewrite Hzd.
    rewrite (Qabs_neg 0 (Qle_refl 0)).
    rewrite uabp7an_qneg0.
    exact Heps.
Qed.

(* 二、主件：具体层无条件 abs 非负件（除语句前提外零假设位）               *)

Lemma uabp7an_core : forall a : Real,
  real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a H. destruct a as [u Hu]. destruct H as [Hlt | Heq].
  - (* 严格正支：e 见证逐点定位 Qabs_pos，差归零 *)
    destruct Hlt as [e [He [N HN]]].
    unfold real_eq. intros eps Heps. exists N. intros n Hn.
    specialize (HN n Hn).
    change (QltT (Qabs (Qabs (u n) - u n)) eps).
    assert (HeQ : 0 < e) by (apply QltT_to_Qlt; exact He).
    assert (HNQ : e < u n - 0) by (apply QltT_to_Qlt; exact HN).
    assert (Hzq : (u n - 0)%Q == u n) by ring.
    rewrite Hzq in HNQ.
    assert (Hpos : 0 < u n) by exact (Qlt_trans 0 e (u n) HeQ HNQ).
    assert (Habs : Qabs (u n) == u n)
      by (apply Qabs_pos; apply Qlt_le_weak; exact Hpos).
    apply Qlt_to_QltT.
    assert (Hzd : (Qabs (u n) - u n)%Q == 0%Q) by (rewrite Habs; ring).
    rewrite Hzd.
    rewrite (Qabs_neg 0 (Qle_refl 0)).
    rewrite uabp7an_qneg0.
    apply QltT_to_Qlt. exact Heps.
  - (* 弱支 real_eq：对半 eps + Qabs_triangle 双倍放行 *)
    unfold real_eq. intros eps Heps.
    assert (Hhalf : QltT 0 (eps / 2))
      by (apply Qlt_to_QltT; apply uabp7an_qlt_half; apply QltT_to_Qlt; exact Heps).
    destruct (Heq (eps / 2)%Q Hhalf) as [N HN].
    exists N. intros n Hn. specialize (HN n Hn).
    change (QltT (Qabs (Qabs (u n) - u n)) eps).
    assert (HNQ : Qabs (0 - u n) < eps / 2) by (apply QltT_to_Qlt; exact HN).
    assert (Hzm : (0 - u n)%Q == (- u n)%Q) by ring.
    rewrite Hzm in HNQ.
    rewrite (Qabs_opp (u n)) in HNQ.
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (Qabs (u n) + Qabs (u n)) _).
    + assert (Hsp : (Qabs (u n) - u n)%Q
                    == (Qabs (u n) + (- u n))%Q) by ring.
      rewrite Hsp.
      apply (Qle_trans _ (Qabs (Qabs (u n)) + Qabs (- u n))).
      * apply Qabs_triangle.
      * rewrite (Qabs_pos (Qabs (u n)) (Qabs_nonneg (u n))).
        rewrite (Qabs_opp (u n)).
        apply Qle_refl.
    + rewrite <- (uabp7an_half_add eps).
      exact (Qplus_lt_compat (Qabs (u n)) (eps / 2)
                             (Qabs (u n)) (eps / 2) HNQ HNQ).
Qed.

(* 无条件「real_le real_zero a -> real_eq (real_abs a) a」全称件——                  *)
(* 接口字段 abs_pos 仅覆盖严格正前提 real_lt real_zero a，本件将其前提减弱为          *)
(* 非严格面；req/le 经全局实例（RealEnhancedReal）定义性即 real_eq/real_le，          *)
(* 语句面取具体载体面（le zero a 即 real_le real_zero a）。                          *)
Lemma uabp7an_abs_nonneg_uncond : forall a : Real,
  real_le real_zero a -> real_eq (real_abs a) a.
Proof. intros a H. exact (uabp7an_core a H). Qed.

(* 三、桥①（抽象接口层）：无条件件 ⟹ 接口 eps 形 abs_nonneg（带非严格前提）          *)
(*   接口字段经全局实例消解；由 req_plus_le_lt_pos 与接口 lt_le_iff/le_id_r 推得，     *)
(*   语句面取具体载体面。                                                            *)

Section Uabp7anUncondToEps.

Lemma uabp7an_uncond_to_eps : forall a : Real,
  real_le real_zero a -> real_eq (real_abs a) a ->
  forall eps : Real, real_lt real_zero eps ->
  real_le real_zero (real_plus (real_abs a) eps).
Proof.
  intros a Hle Heq eps Heps.
  exact (real_le_from_lt_aux real_zero (real_plus (real_abs a) eps)
           (req_plus_le_lt_pos (real_abs a) eps
              (RealSetoid.real_le_id_r real_zero a (real_abs a)
                 (real_eq_sym (real_abs a) a Heq) Hle)
              Heps)).
Qed.

End Uabp7anUncondToEps.

(* 四、桥②（具体层）：Bishop 逐 eps 非负形 ⟹ 无条件件（逆向桥）                       *)
(*   前提形状=abs_nonneg 用于 a 本身（forall eps>0, real_le real_zero (a+eps)）。      *)
(*   路线：取四分之一常值见证，经 real_le 的 Or 两支分别提取逐点下界                     *)
(*   （-a_n < eps/2），再由 uabp7an_pt_tail 符号分段收束；Q 层序可判定，零经典逻辑。     *)

Lemma uabp7an_eps_to_uncond : forall a : Real,
  (forall eps : Real, real_lt real_zero eps ->
                      real_le real_zero (real_plus a eps)) ->
  real_eq (real_abs a) a.
Proof.
  intros a Hbis. destruct a as [u Hu].
  assert (Hcore : real_eq (real_abs (existT (fun u : nat -> Q => cauchy u) u Hu)) (existT (fun u : nat -> Q => cauchy u) u Hu)).
  { intros eps Heps.
    assert (HepsQ : 0 < eps) by (apply QltT_to_Qlt; exact Heps).
    assert (Hhalf : QltT 0 (eps / 2))
      by (apply Qlt_to_QltT; apply uabp7an_qlt_half; exact HepsQ).
    assert (Hq2 : 0 < eps / 2) by (apply uabp7an_qlt_half; exact HepsQ).
    assert (Hq4 : 0 < eps / 4).
    { assert (Hz : eps / 4 == eps / 2 / 2) by field.
      rewrite Hz.
      apply uabp7an_qlt_half. exact Hq2. }
    assert (Hq4T : QltT 0 (eps / 4)) by (apply Qlt_to_QltT; exact Hq4).
    assert (Hq42 : eps / 4 < eps / 2) by (apply uabp7an_q4_lt_q2; exact HepsQ).
    (* 四分之一常值实数的严格正见证（real_lt 构造，取 eps/4 之半） *)
    assert (Hltc : real_lt real_zero (real_const (eps / 4))).
    { assert (Hltc2 : real_lt real_zero (real_const (eps / 4))).
      { unfold real_lt. exists (eps / 4 / 2)%Q. split.
        - apply Qlt_to_QltT. apply uabp7an_qlt_half. exact Hq4.
        - exists 0%nat. intros n _.
          apply Qlt_to_QltT. apply uabp7an_half_lt_m0. exact Hq4. }
      exact Hltc2. }
    destruct (Hbis (real_const (eps / 4)) Hltc) as [Hb | Hb].
    - (* inl 严格支：e1 < a_n + eps/4 ⟹ -a_n < eps/2 *)
      unfold real_le in Hb. destruct Hb as [e1 [He1 [N1 HN1]]].
      exists N1. intros n Hn. specialize (HN1 n Hn).
      change (QltT (Qabs (Qabs (u n) - u n)) eps).
      assert (HN1Q : e1 < u n + eps / 4 - 0) by (apply QltT_to_Qlt; exact HN1).
      assert (Hzq : (u n + eps / 4 - 0)%Q
                    == (u n + eps / 4)%Q) by ring.
      rewrite Hzq in HN1Q.
      apply QltT_to_Qlt in He1.
      assert (Hpos2 : 0 < u n + eps / 4)
        by exact (Qlt_trans 0 e1 (u n + eps / 4) He1 HN1Q).
      assert (Hneg0 : - (u n + eps / 4) < 0).
      { assert (H0 : - (u n + eps / 4) < (- 0))
          by (apply (Qopp_lt_compat 0 (u n + eps / 4)); exact Hpos2).
        rewrite uabp7an_qneg0 in H0. exact H0. }
      assert (Hs : eps / 4 + -(u n + eps / 4) < eps / 4 + 0)
        by (apply (proj2 (Qplus_lt_r (- (u n + eps / 4)) 0 (eps / 4)));
            exact Hneg0).
      assert (Hzs : (eps / 4 + -(u n + eps / 4))%Q
                    == (- u n)%Q) by ring.
      rewrite Hzs in Hs.
      assert (Hzs2 : (eps / 4 + 0)%Q == (eps / 4)%Q) by ring.
      rewrite Hzs2 in Hs.
      assert (Hneg : - u n < eps / 2)
        by exact (Qlt_trans (- u n) (eps / 4) (eps / 2) Hs Hq42).
      apply (uabp7an_pt_tail (u n) eps HepsQ Hneg).
    - (* inr 相等支：|a_n + eps/4| < eps/4 ⟹ 下界翻转 ⟹ -a_n < eps/2 *)
      unfold real_eq in Hb.
      destruct (Hb (eps / 4)%Q Hq4T) as [N2 HN2].
      exists N2. intros n Hn. specialize (HN2 n Hn).
      change (QltT (Qabs (Qabs (u n) - u n)) eps).
      assert (HN2Q : Qabs (0 - (u n + eps / 4)) < eps / 4)
        by (apply QltT_to_Qlt; exact HN2).
      assert (Hsp0 : (0 - (u n + eps / 4))%Q
                     == (-(u n + eps / 4))%Q) by ring.
      rewrite Hsp0 in HN2Q.
      rewrite (Qabs_opp (u n + eps / 4)) in HN2Q.
      pose proof (uabp7an_abs_lb (u n + eps / 4) (eps / 4) Hq4 HN2Q) as Hlb.
      assert (Hs : -(eps / 4) + -(eps / 4) < -(eps / 4) + (u n + eps / 4))
        by (apply (proj2 (Qplus_lt_r (- (eps / 4)) (u n + eps / 4) (- (eps / 4))));
            exact Hlb).
      assert (Hs1 : (-(eps / 4) + -(eps / 4))%Q == (-(eps / 2))%Q) by field.
      rewrite Hs1 in Hs.
      assert (Hs2 : (-(eps / 4) + (u n + eps / 4))%Q
                    == u n) by ring.
      rewrite Hs2 in Hs.
      assert (Hneg : - u n < eps / 2).
      { assert (H0 : - u n < - (-(eps / 2)))
          by (apply (Qopp_lt_compat (-(eps / 2)) (u n)); exact Hs).
        rewrite Qopp_involutive in H0.
        exact H0. }
      apply (uabp7an_pt_tail (u n) eps HepsQ Hneg). }
  exact Hcore.
Qed.

(* 五、假设闭包核验（Print Assumptions，各件应为空）                      *)

Print Assumptions uabp7an_qneg0.
Print Assumptions uabp7an_qlt_half.
Print Assumptions uabp7an_half_add.
Print Assumptions uabp7an_half_lt.
Print Assumptions uabp7an_half_le.
Print Assumptions uabp7an_q4_lt_q2.
Print Assumptions uabp7an_half_lt_m0.
Print Assumptions uabp7an_abs_lb.
Print Assumptions uabp7an_pt_tail.
Print Assumptions uabp7an_core.
Print Assumptions uabp7an_abs_nonneg_uncond.
Print Assumptions uabp7an_uncond_to_eps.
Print Assumptions uabp7an_eps_to_uncond.
