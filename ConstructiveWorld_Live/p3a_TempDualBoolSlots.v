(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   p3a_bsum_ext（原 L51，7 句刀体）                                    *)
(* ============================================================ *)

(* ============================================================ *)
(*   （B 可消融，坐标 L828 定理 10.13 四求和槽；= 开放池 S05 三槽）。   *)
(*                                                                *)
(*   槽语句：第二定律受体升级件四求和槽 sumpos/sumext/sumlinear/        *)
(*   sumadd——list 载体面已全闭（SecondLawQuantified.slq_second_law_     *)
(*   eps_list 喂 real_list_sum），余槽 = 任意 StateSpace 实例化。       *)
(*                                                                *)
(*   施工：最小有限枚举 StateSpace 实例化——二点空间 S := bool，          *)
(*   求和泛函 bsum f := f true + f false（二元 real_plus 直接折叠），    *)
(*   四槽逐一真证装载，并使用基座件：                                   *)
(*     ① real_entropy_deficit_kl_temp（UpReqEntropyDeficitTemp.v:518，  *)
(*        13 参全 arity 显式应用——KL 熵亏分解 T6b 主件）；              *)
(*     ② real_boltzmann_dist_temp / _pos / real_energy_exp_temp /        *)
(*        real_entropy_dist / real_KL_temp（UpReqTempDefs 温度族，       *)
(*        Section 按需消散 6/8 参形）；                                  *)
(*     ③ real_list_sum（S08_RealMainlineDPO.v:288）——bsum↔list 转换      *)
(*        桥（SumEqListFeed 转换 shim 的求和面同构），把本实例接回        *)
(*        list 载体已闭面。                                             *)
(*                                                                *)
(*   纪律：纯构造性；Set 层语句（real_lt/real_eq）；零经典逻辑；          *)
(*   全部 Qed 闭合；G1-G4 四检候跑。                                    *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith.
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
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.

(* ---- 二点有限枚举状态空间与求和泛函 ---- *)

Definition p3a_bsum (f : bool -> Real) : Real :=
  real_plus (f true) (f false).

(* ---- 槽 1 sumpos：保正性 ---- *)

Lemma p3a_bsum_pos : forall f : bool -> Real,
  (forall s : bool, real_lt real_zero (f s)) ->
  real_lt real_zero (p3a_bsum f).
Proof.
  intros f Hf. unfold p3a_bsum.
  apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)).
  - apply real_eq_sym. apply real_plus_zero.
  - exact (real_lt_plus_compat real_zero (f true) real_zero (f false)
             (Hf true) (Hf false)).
Qed.

(* ---- 槽 2 sumext：外延性 ---- *)

Lemma p3a_bsum_ext : forall f g : bool -> Real,
  (forall s : bool, real_eq (f s) (g s)) ->
  real_eq (p3a_bsum f) (p3a_bsum g).
Proof.
  intros f g Hfg.
  assert (Ht : real_eq (f true) (g true)).
  { exact (Hfg true). }
  assert (Hff : real_eq (f false) (g false)).
  { exact (Hfg false). }
  unfold p3a_bsum.
  exact (RealSetoid.real_eq_plus_compat (f true) (f false) (g true) (g false) Ht Hff).
Qed.

(* ---- 槽 3 sumlinear：线性性（分配律 + 因子序转换） ---- *)

Lemma p3a_bsum_lin : forall (a : Real) (f : bool -> Real),
  real_eq (p3a_bsum (fun s : bool => real_mult a (f s)))
          (real_mult a (p3a_bsum f)).
Proof.
  intros a f. unfold p3a_bsum.
  apply (real_eq_trans
           (real_plus (real_mult a (f true)) (real_mult a (f false)))
           (real_plus (real_mult (f true) a) (real_mult (f false) a))).
  - apply RealSetoid.real_eq_plus_compat.
    + apply real_mult_comm.
    + apply real_mult_comm.
  - apply (real_eq_trans
             (real_plus (real_mult (f true) a) (real_mult (f false) a))
             (real_mult (real_plus (f true) (f false)) a)).
    + exact (real_distrib_r_local (f true) (f false) a).
    + exact (real_mult_comm (real_plus (f true) (f false)) a).
Qed.

(* ---- 槽 4 sumadd：可加性（assoc/comm 四项重排） ---- *)

Lemma p3a_bsum_add : forall f g : bool -> Real,
  real_eq (p3a_bsum (fun s : bool => real_plus (f s) (g s)))
          (real_plus (p3a_bsum f) (p3a_bsum g)).
Proof.
  intros f g. unfold p3a_bsum.
  apply (real_eq_trans
           (real_plus (real_plus (f true) (g true))
                      (real_plus (f false) (g false)))
           (real_plus (f true)
                      (real_plus (g true) (real_plus (f false) (g false))))).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans
             (real_plus (f true)
                        (real_plus (g true) (real_plus (f false) (g false))))
             (real_plus (f true)
                        (real_plus (f false) (real_plus (g true) (g false))))).
    + apply RealSetoid.real_eq_plus_compat.
      * apply real_eq_refl.
      * (* g true + (f false + g false) == f false + (g true + g false) *)
        apply (real_eq_trans
                 (real_plus (g true) (real_plus (f false) (g false)))
                 (real_plus (real_plus (g true) (f false)) (g false))).
        -- apply real_plus_assoc.
        -- apply (real_eq_trans
                    (real_plus (real_plus (g true) (f false)) (g false))
                    (real_plus (real_plus (f false) (g true)) (g false))).
           ++ apply RealSetoid.real_eq_plus_compat.
              ** apply real_plus_comm.
              ** apply real_eq_refl.
           ++ apply real_eq_sym. apply real_plus_assoc.
    + apply real_plus_assoc.
Qed.

(* ---- 转换桥：bsum ↔ list 求和（二点枚举 [true; false] 输入） ---- *)

Lemma p3a_bsum_list_feed : forall f : bool -> Real,
  real_eq (p3a_bsum f) (real_list_sum bool f (true :: false :: nil)).
Proof.
  intros f. unfold p3a_bsum. cbn [real_list_sum].
  apply (real_eq_trans (real_plus (f true) (f false))
           (real_plus (real_plus (f true) (f false)) real_zero)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_eq_sym. apply real_plus_assoc.
Qed.

(* ---- 主件：二点空间熵亏 KL 分解槽装载（real_entropy_deficit_kl_temp    *)
(*      13 参全 arity 实例化——第二定律四求和槽在有限枚举载体的兑现） ---- *)

Theorem p3a_two_state_entropy_deficit_kl_zero :
  forall (T : Real) (Ht : real_lt real_zero T)
         (energy p : bool -> Real)
         (Hp : forall s : bool, real_lt real_zero (p s)),
    real_eq (p3a_bsum p) real_one ->
    real_eq (p3a_bsum (fun s : bool => real_mult (p s) (energy s)))
            (real_energy_exp_temp bool p3a_bsum p3a_bsum_pos T Ht energy) ->
    real_eq (real_minus_r
               (real_entropy_dist bool p3a_bsum
                  (real_boltzmann_dist_temp bool p3a_bsum p3a_bsum_pos T Ht energy)
                  (real_boltzmann_dist_temp_pos bool p3a_bsum p3a_bsum_pos T Ht energy))
               (real_entropy_dist bool p3a_bsum p Hp))
            (real_KL_temp bool p3a_bsum p3a_bsum_pos T Ht energy p Hp).
Proof.
  intros T Ht energy p Hp Hnormp Henergy.
  exact (real_entropy_deficit_kl_temp bool p3a_bsum p3a_bsum_pos
           p3a_bsum_ext p3a_bsum_lin p3a_bsum_add
           T Ht energy p Hp Hnormp Henergy).
Qed.

(* ---- 四检备件：PA 口径 + G3 提取检验 ---- *)

Print Assumptions p3a_bsum_add.
Print Assumptions p3a_two_state_entropy_deficit_kl_zero.
Print Assumptions p3a_bsum_list_feed.

From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
Extraction "p3a_tempdualboolslots.ml" p3a_two_state_entropy_deficit_kl_zero p3a_bsum_list_feed.
