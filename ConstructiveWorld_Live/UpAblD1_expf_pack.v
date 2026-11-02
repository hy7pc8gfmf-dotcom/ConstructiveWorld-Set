(* ==========================================================================)
   UpAblD1_expf_pack.v — UpReqAttnMixTime expf 迷你接口六槽的组合实例化件
   使命: 以 AttnDoeblin 的 real_expf_realizable（expf 五字段一次性 sigT 组合件）逐槽投影拆包，给出 uabd1x_expf 与五字段槽定理（pos/zero/plus/mono_lt/mono_le），零重证。
   依赖: CW_ConstructiveWorld_219、AttnDoeblin。
   对标: 指数函数五字段接口的可实现性（库内 P1 先例同构）。
   构造性: 典范 Real 载体 req 面实例化（Instance RealEnhancedReal 字段映照）；零新增假设面；文尾逐件 Print Assumptions 收尾。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树原地重编），cpu_guard 包裹限载。
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
Require Import AttnDoeblin.

(* ---- 槽1（L94 expf : R -> R）：组合件签名投影＝载体函数槽的居住形 ---- *)
Definition uabd1x_expf : Real -> Real := projT1 real_expf_realizable.

(* ---- 组合件字段束一次性分解（五字段具名，逐槽引用公用） ---- *)
Lemma uabd1x_pack_fields :
  And (forall x : Real, real_lt real_zero (uabd1x_expf x))
    (And (real_eq (uabd1x_expf real_zero) real_one)
    (And (forall a b : Real,
          real_eq (uabd1x_expf (real_plus a b)) (real_mult (uabd1x_expf a) (uabd1x_expf b)))
    (And (forall a b : Real, real_lt a b -> real_lt (uabd1x_expf a) (uabd1x_expf b))
         (forall a b : Real, real_le a b -> real_le (uabd1x_expf a) (uabd1x_expf b))))).
Proof.
  unfold uabd1x_expf.
  exact (projT2 real_expf_realizable).
Qed.

(* 注记：Set 面 And（S01:66 定义 = A * B，    *)
(*   即 Stdlib prod）的投影是 fst/snd；proj1/proj2 在本树属 Prop 面 and 投影  *)
(*   ——面-面不可混（AT7 卡③同款教训），逐槽引用一律 fst/snd。               *)

(* ---- 槽2（L95 expf_pos）逐字引用形 ---- *)
Theorem uabd1x_expf_pos : forall x : Real, real_lt real_zero (uabd1x_expf x).
Proof. intros x. exact (fst uabd1x_pack_fields x). Qed.

(* ---- 槽3（L96 expf_zero；Id 面槽在典范载体 req 幺等下取 req 形）逐字引用形 ---- *)
Theorem uabd1x_expf_zero : real_eq (uabd1x_expf real_zero) real_one.
Proof. exact (fst (snd uabd1x_pack_fields)). Qed.

(* ---- 槽4（L97 expf_plus）逐字引用形 ---- *)
Theorem uabd1x_expf_plus : forall a b : Real,
  real_eq (uabd1x_expf (real_plus a b)) (real_mult (uabd1x_expf a) (uabd1x_expf b)).
Proof. exact (fst (snd (snd uabd1x_pack_fields))). Qed.

(* ---- 槽5（L98 expf_mono_lt）逐字引用形 ---- *)
Theorem uabd1x_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (uabd1x_expf a) (uabd1x_expf b).
Proof. exact (fst (snd (snd (snd uabd1x_pack_fields)))). Qed.

(* ---- 槽6（L99 expf_mono_le；Or 拆支已在组合件内逐支消解—— *)
(*      inl→cauchy_real_exp_mono / inr→cauchy_real_exp_wd，本件整槽引用 ---- *)
Theorem uabd1x_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (uabd1x_expf a) (uabd1x_expf b).
Proof. exact (snd (snd (snd (snd uabd1x_pack_fields)))). Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabd1x_expf.
Print Assumptions uabd1x_pack_fields.
Print Assumptions uabd1x_expf_pos.
Print Assumptions uabd1x_expf_zero.
Print Assumptions uabd1x_expf_plus.
Print Assumptions uabd1x_expf_mono_lt.
Print Assumptions uabd1x_expf_mono_le.
