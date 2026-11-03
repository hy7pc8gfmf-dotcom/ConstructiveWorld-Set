(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* RealEnergyTempMono.v — real_energy_exp_temp_mono 恒等档        *)
(* ============================================================ *)
(* 使命：交付 real_energy_exp_temp_mono 的恒等档（Real 层对位）。    *)
(*   Id 原件：S04_RealExpLogConv.v:3733 energy_exp_temp_mono       *)
(*   （乘正消去闭合前的恒等核 = (b1−b2)·(E2−E1) ≡ KL1+KL2）。       *)
(*   req 层同位件：UpReqTempEntropy.v:90 req_entropy_temp_explicit、 *)
(*   :225 req_relative_entropy_temp_decomp、:1208                  *)
(*   req_temp_strict_ident2（KL(p_{t2}‖p_{t1}) + KL(p_{t1}‖p_{t2})  *)
(*   == (b1−b2)·(E2−E1)）——本文件为其 Real 层逐点对位。            *)
(*                                                                 *)
(*   · UpReqAlign3.v:1446-1450「KL ≥ 0 的 plain-le 形态不可由接口    *)
(*     逐 eps 字段导出（序无消去）；保留假设位，待 UpReqFreeEnergy   *)
(*     （批 2 FEP）交付后降为使用件」。                              *)
(*   · UpReqAlign4.v:469-473「[供给槽②·诚实假设位] sup_gibbs…序无   *)
(*     消去，plain-le 不可由接口逐 eps 字段导出…待 UpReqFreeEnergy   *)
(*     （批 2 FEP）交付后降为使用件」；:509-510「Real 层闭合实例：    *)
(*     槽2/N4 无（sup_gibbs 的 Real 供给 = Real 层 KL≥0 件，属       *)
(*     UpReqFreeEnergy 批 2 范围，批外）」。                          *)
(*   · G07_KLWall.v:2824-2830 裁定结论 C「逐项 real_le real_zero (G s)   *)
(*     （Or 形）对任意 p,q 不可构造（等号点不可判定）…逐项 Bishop    *)
(*     形（eps 余量）无前提路线由库侧 real_gibbs_core_eps /          *)
(*     real_gibbs_inequality_eps 承载」。                            *)
(*   S01:69 Or := A + B 为 Set 值和，须交分支见证）；real_lt 需一致  *)
(*   有理 gap（S02:456），p==q 点 KL==0 无 gap、real_eq 分支不可判定 *)
(*   ⟹ plain KL≥0 实 LPO 等价（同 E-STAGING-DPOLip-StrongLeAbs 卡）  *)
(*   ；Id 层能证只因 Id 接口带 lt_dec 三分律字段（S01:333），req     *)
(*   接口刻意降逐 eps（既有判例）后无消去。逐 eps 件可证机理：eps 松   *)
(*   弛使左支严格（real_exp_ge_linear_eps S07:8404 unfold real_le;   *)
(*   left 实证）。故恒等档（real_eq 链，零 le 使用）为本位无条件闭  *)
(*   合的最强免费形；单调性档需使用 KL≥0，留待批 2 FEP/Bishop 桥。   *)
(*                                                                 *)
(* 交付件（retm_ 前缀，全库防撞 grep=0）：                           *)
(*   retm_Ztemp/retm_pB/retm_pB_pos/retm_Eexp/retm_LZ/retm_KL 定义族 *)
(*   retm_Ztemp_pos        两温度 Boltzmann 配分函数正性（cons 载体）  *)
(*   retm_pB_Z_mult        p_t(s)·Z_t == e^{−β·u_s}                   *)
(*   retm_pB_norm          Σ_s p_t(s) == 1（归一化）                  *)
(*   retm_log_inv_pos_gen  log(1/x) == −log x（一般件）               *)
(*   retm_log_pB           log p_t(s) == −β·u_s − log Z_t             *)
(*   retm_kl_point         real_kl_term 逐点温度分解                   *)
(*   retm_KL_decomp        KL(p_{t1}‖p_{t2}) == (β2−β1)·E1 + (logZ2−logZ1) *)
(*   retm_energy_temp_kl_pair_ident（主定理恒等档主定理）               *)
(*                         KL(p_{t2}‖p_{t1}) + KL(p_{t1}‖p_{t2})      *)
(*                         == (β1−β2)·(E2−E1)                          *)
(*                                                                 *)
(* 红线自审：① 零 公理/承认件/参数/猜想/弃证/经典逻辑  *)
(*   （依赖全为库内 Closed 件）；② 语句面全 Set（real_eq/real_lt/    *)
(*   real_list_sum，零 Prop 前提；real_list_sum_pos 的 <> 前提仅在   *)
(*   证内以 discriminate 使用，语句面以 cons 载体 s0::l 非空化）；    *)
(*   ③ 真证 Qed 全闭合、无条件语句（非平凡：温度 KL 分解 + 归一化    *)
(*   + log/inv 桥 + 代数链）；④ 可提取（G3 检验独立文件实测           *)
(*   Obj.magic=0）。                                                  *)
(* 编译配方：source Live/toolchain/env.sh && cd Live/build &&        *)
(*   rocq c -Q . '' RealEnergyTempMono.v（cpu_guard 包裹）。         *)
(* 依赖：CW_ConstructiveWorld_219（S01–S15 薄壳，.vo 在 Live/build， *)
(*   幻数 _364 同轨，E-STAGING-CWA 卡实测）。                         *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
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

(* ============================================================ *)
(* Part 0：定义族（两温度 Boltzmann 有限状态载体 s0 :: l）          *)
(* ============================================================ *)

(* 配分函数 Z_t := Σ_{s ∈ s0::l} e^{−β·u_s}，β := 1/t *)
Definition retm_Ztemp (X : Type) (u : X -> Real) (s0 : X) (l : list X)
           (t : Real) (Ht : real_lt real_zero t) : Real :=
  real_list_sum X (fun s => real_exp_neg (real_mult (real_inv_pos t Ht) (u s))) (s0 :: l).

(* Z_t > 0：逐点正 + cons 载体非空（real_list_sum_pos 的 <> 前提
   在证内以 discriminate 使用，语句面零 Prop） *)
Lemma retm_Ztemp_pos : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t : Real) (Ht : real_lt real_zero t),
  real_lt real_zero (retm_Ztemp X u s0 l t Ht).
Proof.
  intros X u s0 l t Ht. unfold retm_Ztemp.
  apply (real_list_sum_pos X (fun s => real_exp_neg (real_mult (real_inv_pos t Ht) (u s))) (s0 :: l)).
  - intro s. apply real_exp_neg_pos.
  - discriminate.
Qed.

(* Boltzmann 分布 p_t(s) := e^{−β·u_s}·inv(Z_t) *)
Definition retm_pB (X : Type) (u : X -> Real) (s0 : X) (l : list X)
           (t : Real) (Ht : real_lt real_zero t) (s : X) : Real :=
  real_mult (real_exp_neg (real_mult (real_inv_pos t Ht) (u s)))
            (real_inv_pos (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht)).

(* 正性证书（透明 Definition，proof-relevant 数据随定义走） *)
Definition retm_pB_pos (X : Type) (u : X -> Real) (s0 : X) (l : list X)
           (t : Real) (Ht : real_lt real_zero t) (s : X) :
  real_lt real_zero (retm_pB X u s0 l t Ht s) :=
  real_mult_positive (real_exp_neg (real_mult (real_inv_pos t Ht) (u s)))
    (real_inv_pos (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht))
    (real_exp_neg_pos (real_mult (real_inv_pos t Ht) (u s)))
    (real_inv_pos_pos (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht)).

(* 期望能量 E_t := Σ p_t·u *)
Definition retm_Eexp (X : Type) (u : X -> Real) (s0 : X) (l : list X)
           (t : Real) (Ht : real_lt real_zero t) : Real :=
  real_list_sum X (fun s => real_mult (retm_pB X u s0 l t Ht s) (u s)) (s0 :: l).

(* log Z_t *)
Definition retm_LZ (X : Type) (u : X -> Real) (s0 : X) (l : list X)
           (t : Real) (Ht : real_lt real_zero t) : Real :=
  real_log (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht).

(* KL(p_{t1}‖p_{t2}) := Σ real_kl_term（库件 real_kl_term = p·(−log(q/p))） *)
Definition retm_KL (X : Type) (u : X -> Real) (s0 : X) (l : list X)
           (t1 : Real) (Ht1 : real_lt real_zero t1)
           (t2 : Real) (Ht2 : real_lt real_zero t2) : Real :=
  real_list_sum X (fun s => real_kl_term (retm_pB X u s0 l t1 Ht1 s) (retm_pB X u s0 l t2 Ht2 s)
                                          (retm_pB_pos X u s0 l t1 Ht1 s) (retm_pB_pos X u s0 l t2 Ht2 s))
                  (s0 :: l).

(* 代数恒等捷径：加/乘/负/原子项上的 real_eq 一步 ring 闭合。
   逐点投影 real_*_proj 现为 QeqT 面（S02_CauchyComplete），故经
   qeq_imp_qeqT / qeqT_imp_qeq 两向门转 Qeq 环面后 ring 闭合。 *)
Ltac retm_alg :=
  apply real_eq_of_zero_diff; intro; apply qeq_imp_qeqT;
  repeat first [ rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _))
               | rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _))
               | rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _)) ];
  ring.

(* ============================================================ *)
(* Part 1：代数助手 + log/inv 桥                                   *)
(* ============================================================ *)

(* a + b == 0 ⟹ b == −a（real_eq 链） *)
Lemma retm_plus_zero_l_opp : forall a b : Real,
  real_eq (real_plus a b) real_zero -> real_eq b (real_opp a).
Proof.
  intros a b H.
  apply (real_eq_trans b (real_plus b real_zero) (real_opp a)).
  - exact (real_eq_sym (real_plus b real_zero) b (real_plus_zero b)).
  - apply (real_eq_trans (real_plus b real_zero)
                         (real_plus b (real_plus a (real_opp a))) _).
    + exact (RealSetoid.real_eq_plus_compat b real_zero b
               (real_plus a (real_opp a)) (real_eq_refl b)
               (real_eq_sym (real_plus a (real_opp a)) real_zero (real_plus_opp a))).
    + apply (real_eq_trans (real_plus b (real_plus a (real_opp a)))
                           (real_plus (real_plus b a) (real_opp a)) _).
      * exact (real_plus_assoc b a (real_opp a)).
      * apply (real_eq_trans (real_plus (real_plus b a) (real_opp a))
                             (real_plus (real_plus a b) (real_opp a)) _).
        -- exact (RealSetoid.real_eq_plus_compat (real_plus b a) (real_opp a)
                    (real_plus a b) (real_opp a) (real_plus_comm b a)
                    (real_eq_refl (real_opp a))).
        -- apply (real_eq_trans (real_plus (real_plus a b) (real_opp a))
                                (real_plus real_zero (real_opp a)) _).
           ++ exact (RealSetoid.real_eq_plus_compat (real_plus a b) (real_opp a)
                       real_zero (real_opp a)
                       H
                       (real_eq_refl (real_opp a))).
           ++ apply (real_eq_trans (real_plus real_zero (real_opp a))
                                   (real_plus (real_opp a) real_zero) _).
              ** exact (real_plus_comm real_zero (real_opp a)).
              ** exact (real_plus_zero (real_opp a)).
Qed.

(* log(1/x) == −log x（一般件；由 log(x·inv x) == log 1 == 0 + 助手） *)
Lemma retm_log_inv_pos_gen : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
          (real_opp (real_log x Hx)).
Proof.
  intros x Hx.
  assert (Hmult := real_log_mult x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx)).
  assert (Hto1 : real_eq (real_log real_one real_lt_zero_one)
                         (real_log (real_mult x (real_inv_pos x Hx))
                                   (real_mult_positive x (real_inv_pos x Hx) Hx
                                      (real_inv_pos_pos x Hx)))).
  { apply (real_log_wd real_one (real_mult x (real_inv_pos x Hx)) real_lt_zero_one
             (real_mult_positive x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx))).
    exact (real_eq_sym (real_mult x (real_inv_pos x Hx)) real_one
             (real_inv_pos_correct x Hx)). }
  assert (Hz : real_eq
                 (real_plus (real_log x Hx)
                            (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                 real_zero).
  { apply (real_eq_trans
             (real_plus (real_log x Hx)
                        (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
             (real_log (real_mult x (real_inv_pos x Hx))
                       (real_mult_positive x (real_inv_pos x Hx) Hx
                          (real_inv_pos_pos x Hx))) _).
    - exact (real_eq_sym _ _ Hmult).
    - apply (real_eq_trans
               (real_log (real_mult x (real_inv_pos x Hx))
                         (real_mult_positive x (real_inv_pos x Hx) Hx
                            (real_inv_pos_pos x Hx)))
               (real_log real_one real_lt_zero_one) _).
      + exact (real_eq_sym _ _ Hto1).
      + exact (real_log_one real_lt_zero_one). }
  exact (retm_plus_zero_l_opp (real_log x Hx)
          (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)) Hz).
Qed.

(* ============================================================ *)
(* Part 2：Boltzmann 分布基本恒等                                  *)
(* ============================================================ *)

(* p_t(s)·Z_t == e^{−β·u_s}：(e·invZ)·Z == e·(invZ·Z) == e·(Z·invZ) == e·1 == e *)
Lemma retm_pB_Z_mult : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t : Real) (Ht : real_lt real_zero t) (s : X),
  real_eq (real_mult (retm_pB X u s0 l t Ht s) (retm_Ztemp X u s0 l t Ht))
          (real_exp_neg (real_mult (real_inv_pos t Ht) (u s))).
Proof.
  intros X u s0 l t Ht s.
  unfold retm_pB, retm_Ztemp.
  set (e := real_exp_neg (real_mult (real_inv_pos t Ht) (u s))).
  set (Z := real_list_sum X (fun w => real_exp_neg (real_mult (real_inv_pos t Ht) (u w))) (s0 :: l)).
  set (iv := real_inv_pos Z (retm_Ztemp_pos X u s0 l t Ht)).
  apply (real_eq_trans (real_mult (real_mult e iv) Z) (real_mult e (real_mult iv Z)) _).
  - exact (real_eq_sym _ _ (real_mult_assoc e iv Z)).
  - apply (real_eq_trans (real_mult e (real_mult iv Z)) (real_mult e (real_mult Z iv)) _).
    + exact (RealSetoid.real_eq_mult_compat e (real_mult iv Z) e (real_mult Z iv)
               (real_eq_refl e) (real_mult_comm iv Z)).
    + apply (real_eq_trans (real_mult e (real_mult Z iv)) (real_mult e real_one) _).
      * exact (RealSetoid.real_eq_mult_compat e (real_mult Z iv) e real_one
                 (real_eq_refl e) (real_inv_pos_correct Z (retm_Ztemp_pos X u s0 l t Ht))).
      * exact (real_mult_one e).
Qed.

(* 归一化：Σ_s p_t(s) == 1（linear_r + inv_pos_correct） *)
Lemma retm_pB_norm : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t : Real) (Ht : real_lt real_zero t),
  real_eq (real_list_sum X (fun s => retm_pB X u s0 l t Ht s) (s0 :: l)) real_one.
Proof.
  intros X u s0 l t Ht.
  unfold retm_pB.
  set (iv := real_inv_pos (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht)).
  apply (real_eq_trans
           (real_list_sum X
              (fun s => real_mult (real_exp_neg (real_mult (real_inv_pos t Ht) (u s))) iv)
              (s0 :: l))
           (real_mult iv (retm_Ztemp X u s0 l t Ht)) real_one).
  - exact (real_list_sum_linear_r X iv
             (fun s => real_exp_neg (real_mult (real_inv_pos t Ht) (u s))) (s0 :: l)).
  - apply (real_eq_trans (real_mult iv (retm_Ztemp X u s0 l t Ht))
                         (real_mult (retm_Ztemp X u s0 l t Ht) iv) _).
    + exact (real_mult_comm iv (retm_Ztemp X u s0 l t Ht)).
    + exact (real_inv_pos_correct (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht)).
Qed.

(* log p_t(s) == −β·u_s − log Z_t（log_mult + log_exp_neg + log_inv 桥） *)
Lemma retm_log_pB : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t : Real) (Ht : real_lt real_zero t) (s : X),
  real_eq (real_log (retm_pB X u s0 l t Ht s) (retm_pB_pos X u s0 l t Ht s))
          (real_plus (real_opp (real_mult (real_inv_pos t Ht) (u s)))
                     (real_opp (retm_LZ X u s0 l t Ht))).
Proof.
  intros X u s0 l t Ht s. unfold retm_pB, retm_LZ.
  apply (real_eq_trans
           (real_log (real_mult (real_exp_neg (real_mult (real_inv_pos t Ht) (u s)))
                                (real_inv_pos (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht)))
                     (retm_pB_pos X u s0 l t Ht s))
           (real_plus (real_log (real_exp_neg (real_mult (real_inv_pos t Ht) (u s)))
                                (real_exp_neg_pos (real_mult (real_inv_pos t Ht) (u s))))
                      (real_log (real_inv_pos (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht))
                                (real_inv_pos_pos (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht))))
           _).
  - exact (real_log_mult (real_exp_neg (real_mult (real_inv_pos t Ht) (u s)))
                         (real_inv_pos (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht))
                         (real_exp_neg_pos (real_mult (real_inv_pos t Ht) (u s)))
                         (real_inv_pos_pos (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht))).
  - exact (RealSetoid.real_eq_plus_compat
             (real_log (real_exp_neg (real_mult (real_inv_pos t Ht) (u s)))
                       (real_exp_neg_pos (real_mult (real_inv_pos t Ht) (u s))))
             (real_log (real_inv_pos (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht))
                       (real_inv_pos_pos (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht)))
             (real_opp (real_mult (real_inv_pos t Ht) (u s)))
             (real_opp (real_log (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht)))
             (real_log_exp_neg (real_mult (real_inv_pos t Ht) (u s)))
             (retm_log_inv_pos_gen (retm_Ztemp X u s0 l t Ht) (retm_Ztemp_pos X u s0 l t Ht))).
Qed.

(* ============================================================ *)
(* Part 3：KL 逐点温度分解                                         *)
(* ============================================================ *)

(* real_kl_term(p_{t1}(s), p_{t2}(s)) == p_{t1}(s)·((β2−β1)·u_s + (logZ2−logZ1))
   链：kl_term = p1·(−log(p2/p1))；log(p2/p1) == log p2 + log(inv p1)
   == (−β2·u_s−LZ2) + −(−β1·u_s−LZ1)；展开 + 代数闭合。 *)
Lemma retm_kl_point : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2) (s : X),
  real_eq (real_kl_term (retm_pB X u s0 l t1 Ht1 s) (retm_pB X u s0 l t2 Ht2 s)
                        (retm_pB_pos X u s0 l t1 Ht1 s) (retm_pB_pos X u s0 l t2 Ht2 s))
          (real_mult (retm_pB X u s0 l t1 Ht1 s)
                     (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t1 Ht1))) (u s))
                                (real_plus (retm_LZ X u s0 l t2 Ht2) (real_opp (retm_LZ X u s0 l t1 Ht1))))).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 s.
  unfold real_kl_term.
  set (p1 := retm_pB X u s0 l t1 Ht1 s). set (p2 := retm_pB X u s0 l t2 Ht2 s).
  set (Hp1 := retm_pB_pos X u s0 l t1 Ht1 s). set (Hp2 := retm_pB_pos X u s0 l t2 Ht2 s).
  set (b1 := real_inv_pos t1 Ht1). set (b2 := real_inv_pos t2 Ht2).
  set (L1 := retm_LZ X u s0 l t1 Ht1). set (L2 := retm_LZ X u s0 l t2 Ht2).
  assert (H4t1 : real_eq (real_log p1 Hp1)
                         (real_plus (real_opp (real_mult b1 (u s))) (real_opp L1)))
    by exact (retm_log_pB X u s0 l t1 Ht1 s).
  assert (H4t2 : real_eq (real_log p2 Hp2)
                         (real_plus (real_opp (real_mult b2 (u s))) (real_opp L2)))
    by exact (retm_log_pB X u s0 l t2 Ht2 s).
  assert (Hinv1 : real_eq (real_opp (real_log (real_inv_pos p1 Hp1) (real_inv_pos_pos p1 Hp1)))
                          (real_plus (real_opp (real_mult b1 (u s))) (real_opp L1))).
  { apply (real_eq_trans
             (real_opp (real_log (real_inv_pos p1 Hp1) (real_inv_pos_pos p1 Hp1)))
             (real_opp (real_opp (real_log p1 Hp1))) _).
    - exact (RealSetoid.real_eq_opp_compat
               (real_log (real_inv_pos p1 Hp1) (real_inv_pos_pos p1 Hp1))
               (real_opp (real_log p1 Hp1)) (retm_log_inv_pos_gen p1 Hp1)).
    - apply (real_eq_trans (real_opp (real_opp (real_log p1 Hp1)))
                           (real_opp (real_opp (real_plus (real_opp (real_mult b1 (u s))) (real_opp L1)))) _).
      + exact (RealSetoid.real_eq_opp_compat
                 (real_opp (real_log p1 Hp1))
                 (real_opp (real_plus (real_opp (real_mult b1 (u s))) (real_opp L1)))
                 (RealSetoid.real_eq_opp_compat (real_log p1 Hp1)
                    (real_plus (real_opp (real_mult b1 (u s))) (real_opp L1)) H4t1)).
      + exact (real_opp_opp (real_plus (real_opp (real_mult b1 (u s))) (real_opp L1))). }
  apply (RealSetoid.real_eq_mult_compat p1
           (real_opp (real_log (real_mult p2 (real_inv_pos p1 Hp1))
                               (real_mult_positive p2 (real_inv_pos p1 Hp1) Hp2 (real_inv_pos_pos p1 Hp1))))
           p1
           (real_plus (real_mult (real_plus b2 (real_opp b1)) (u s)) (real_plus L2 (real_opp L1)))
           (real_eq_refl p1)).
  apply (real_eq_trans
           (real_opp (real_log (real_mult p2 (real_inv_pos p1 Hp1))
                               (real_mult_positive p2 (real_inv_pos p1 Hp1) Hp2 (real_inv_pos_pos p1 Hp1))))
           (real_plus (real_opp (real_log p2 Hp2))
                      (real_opp (real_log (real_inv_pos p1 Hp1) (real_inv_pos_pos p1 Hp1)))) _).
  - apply (real_eq_trans
             (real_opp (real_log (real_mult p2 (real_inv_pos p1 Hp1))
                                 (real_mult_positive p2 (real_inv_pos p1 Hp1) Hp2 (real_inv_pos_pos p1 Hp1))))
             (real_opp (real_plus (real_log p2 Hp2)
                                  (real_log (real_inv_pos p1 Hp1) (real_inv_pos_pos p1 Hp1)))) _).
    + exact (RealSetoid.real_eq_opp_compat
               (real_log (real_mult p2 (real_inv_pos p1 Hp1))
                         (real_mult_positive p2 (real_inv_pos p1 Hp1) Hp2 (real_inv_pos_pos p1 Hp1)))
               (real_plus (real_log p2 Hp2)
                          (real_log (real_inv_pos p1 Hp1) (real_inv_pos_pos p1 Hp1)))
               (real_log_mult p2 (real_inv_pos p1 Hp1) Hp2 (real_inv_pos_pos p1 Hp1))).
    + exact (real_opp_plus (real_log p2 Hp2)
                           (real_log (real_inv_pos p1 Hp1) (real_inv_pos_pos p1 Hp1))).
  - apply (real_eq_trans
             (real_plus (real_opp (real_log p2 Hp2))
                        (real_opp (real_log (real_inv_pos p1 Hp1) (real_inv_pos_pos p1 Hp1))))
             (real_plus (real_opp (real_plus (real_opp (real_mult b2 (u s))) (real_opp L2)))
                        (real_plus (real_opp (real_mult b1 (u s))) (real_opp L1))) _).
    + exact (RealSetoid.real_eq_plus_compat
               (real_opp (real_log p2 Hp2))
               (real_opp (real_log (real_inv_pos p1 Hp1) (real_inv_pos_pos p1 Hp1)))
               (real_opp (real_plus (real_opp (real_mult b2 (u s))) (real_opp L2)))
               (real_plus (real_opp (real_mult b1 (u s))) (real_opp L1))
               (RealSetoid.real_eq_opp_compat (real_log p2 Hp2)
                  (real_plus (real_opp (real_mult b2 (u s))) (real_opp L2)) H4t2)
               Hinv1).
    + (* 纯代数：−(−β2·u−LZ2) + (−β1·u−LZ1) == (β2−β1)·u + (LZ2−LZ1) *)
      retm_alg.
Qed.

(* KL(p_{t1}‖p_{t2}) == (β2−β1)·E1 + (logZ2−logZ1)
   （Real 层对位 UpReqTempEntropy.v:225 req_relative_entropy_temp_decomp）
   链：逐点展开（retm_kl_point）+ distrib 拆和 + 常数提取（linear_r）
   + 逐点换形（assoc/comm/comm）+ 归一化（retm_pB_norm）+ mult_one。 *)
Lemma retm_KL_decomp : forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
  (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2),
  real_eq (retm_KL X u s0 l t1 Ht1 t2 Ht2)
          (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t1 Ht1)))
                                (retm_Eexp X u s0 l t1 Ht1))
                     (real_plus (retm_LZ X u s0 l t2 Ht2) (real_opp (retm_LZ X u s0 l t1 Ht1)))).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2.
  set (p1 := fun s => retm_pB X u s0 l t1 Ht1 s).
  set (Hp1 := fun s => retm_pB_pos X u s0 l t1 Ht1 s).
  set (p2 := fun s => retm_pB X u s0 l t2 Ht2 s).
  set (Hp2 := fun s => retm_pB_pos X u s0 l t2 Ht2 s).
  set (b1 := real_inv_pos t1 Ht1). set (b2 := real_inv_pos t2 Ht2).
  set (L1 := retm_LZ X u s0 l t1 Ht1). set (L2 := retm_LZ X u s0 l t2 Ht2).
  set (k := real_plus b2 (real_opp b1)). set (C := real_plus L2 (real_opp L1)).
  set (E1 := real_list_sum X (fun s => real_mult (p1 s) (u s)) (s0 :: l)).
  unfold retm_KL, retm_Eexp.
  apply (real_eq_trans
           (real_list_sum X (fun s => real_kl_term (p1 s) (p2 s) (Hp1 s) (Hp2 s)) (s0 :: l))
           (real_plus (real_mult k E1) C) _).
  - apply (real_eq_trans
             (real_list_sum X (fun s => real_kl_term (p1 s) (p2 s) (Hp1 s) (Hp2 s)) (s0 :: l))
             (real_list_sum X (fun s => real_mult (p1 s) (real_plus (real_mult k (u s)) C)) (s0 :: l)) _).
    + apply (real_list_sum_ext X (fun s => real_kl_term (p1 s) (p2 s) (Hp1 s) (Hp2 s))
                                 (fun s => real_mult (p1 s) (real_plus (real_mult k (u s)) C)) (s0 :: l)).
      intro w. exact (retm_kl_point X u s0 l t1 Ht1 t2 Ht2 w).
    + apply (real_eq_trans
               (real_list_sum X (fun s => real_mult (p1 s) (real_plus (real_mult k (u s)) C)) (s0 :: l))
               (real_plus (real_mult k E1) C) _).
      * apply (real_eq_trans
                 (real_list_sum X (fun s => real_mult (p1 s) (real_plus (real_mult k (u s)) C)) (s0 :: l))
                 (real_plus (real_list_sum X (fun s => real_mult (p1 s) (real_mult k (u s))) (s0 :: l))
                            (real_list_sum X (fun s => real_mult (p1 s) C) (s0 :: l))) _).
        -- apply (real_eq_trans
                     (real_list_sum X (fun s => real_mult (p1 s) (real_plus (real_mult k (u s)) C)) (s0 :: l))
                     (real_list_sum X (fun s => real_plus (real_mult (p1 s) (real_mult k (u s))) (real_mult (p1 s) C))
                                     (s0 :: l)) _).
           ++ apply (real_list_sum_ext X
                        (fun s => real_mult (p1 s) (real_plus (real_mult k (u s)) C))
                        (fun s => real_plus (real_mult (p1 s) (real_mult k (u s))) (real_mult (p1 s) C))
                        (s0 :: l)).
              intro w. exact (real_distrib (p1 w) (real_mult k (u w)) C).
           ++ exact (real_list_sum_add X (fun s => real_mult (p1 s) (real_mult k (u s)))
                                        (fun s => real_mult (p1 s) C) (s0 :: l)).
        -- apply (RealSetoid.real_eq_plus_compat
                    (real_list_sum X (fun s => real_mult (p1 s) (real_mult k (u s))) (s0 :: l))
                    (real_list_sum X (fun s => real_mult (p1 s) C) (s0 :: l))
                    (real_mult k E1)
                    C).
           ++ (* 肢 1：Σ(p1·(k·u)) == k·Σ(p1·u)：逐点换形 + linear_r *)
              apply (real_eq_trans
                       (real_list_sum X (fun s => real_mult (p1 s) (real_mult k (u s))) (s0 :: l))
                       (real_list_sum X (fun s => real_mult (real_mult (p1 s) (u s)) k) (s0 :: l)) _).
              ** apply (real_list_sum_ext X (fun s => real_mult (p1 s) (real_mult k (u s)))
                          (fun s => real_mult (real_mult (p1 s) (u s)) k) (s0 :: l)).
                 intro w. retm_alg.
              ** exact (real_list_sum_linear_r X k (fun s => real_mult (p1 s) (u s)) (s0 :: l)).
           ++ (* 肢 2：Σ(p1·C) == C·Σp1 == C·1 == C *)
              apply (real_eq_trans (real_list_sum X (fun s => real_mult (p1 s) C) (s0 :: l))
                                   (real_mult C (real_list_sum X p1 (s0 :: l))) _).
              ** exact (real_list_sum_linear_r X C p1 (s0 :: l)).
              ** apply (real_eq_trans (real_mult C (real_list_sum X p1 (s0 :: l)))
                                      (real_mult C real_one) _).
                 --- exact (RealSetoid.real_eq_mult_compat C (real_list_sum X p1 (s0 :: l)) C real_one
                              (real_eq_refl C) (retm_pB_norm X u s0 l t1 Ht1)).
                 --- exact (real_mult_one C).
      * exact (real_eq_refl (real_plus (real_mult k E1) C)).
  - (* 中项与目标转换：E1 δ 同 retm_Eexp 展开 *)
    exact (real_eq_refl _).
Qed.

(* ============================================================ *)
(* Part 4：主定理恒等档主定理                                         *)
(* ============================================================ *)

(* KL(p_{t2}‖p_{t1}) + KL(p_{t1}‖p_{t2}) == (β1−β2)·(E2−E1)
   （Real 层对位 UpReqTempEntropy.v:1208 req_temp_strict_ident2，
   Id temp_strict_ident2 @17879；energy_exp_temp_mono 恒等档） *)
Theorem retm_energy_temp_kl_pair_ident :
  forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
    (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2),
  real_eq (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1) (retm_KL X u s0 l t1 Ht1 t2 Ht2))
          (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t2 Ht2)))
                     (real_plus (retm_Eexp X u s0 l t2 Ht2) (real_opp (retm_Eexp X u s0 l t1 Ht1)))).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2.
  assert (H21 := retm_KL_decomp X u s0 l t2 Ht2 t1 Ht1).
  assert (H12 := retm_KL_decomp X u s0 l t1 Ht1 t2 Ht2).
  apply (real_eq_trans
           (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1) (retm_KL X u s0 l t1 Ht1 t2 Ht2))
           (real_plus
              (real_plus (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t2 Ht2)))
                                    (retm_Eexp X u s0 l t2 Ht2))
                         (real_plus (retm_LZ X u s0 l t1 Ht1) (real_opp (retm_LZ X u s0 l t2 Ht2))))
              (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t1 Ht1)))
                                    (retm_Eexp X u s0 l t1 Ht1))
                         (real_plus (retm_LZ X u s0 l t2 Ht2) (real_opp (retm_LZ X u s0 l t1 Ht1))))) _).
  - exact (RealSetoid.real_eq_plus_compat
             (retm_KL X u s0 l t2 Ht2 t1 Ht1)
             (retm_KL X u s0 l t1 Ht1 t2 Ht2)
             (real_plus (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t2 Ht2)))
                                   (retm_Eexp X u s0 l t2 Ht2))
                        (real_plus (retm_LZ X u s0 l t1 Ht1) (real_opp (retm_LZ X u s0 l t2 Ht2))))
             (real_plus (real_mult (real_plus (real_inv_pos t2 Ht2) (real_opp (real_inv_pos t1 Ht1)))
                                   (retm_Eexp X u s0 l t1 Ht1))
                        (real_plus (retm_LZ X u s0 l t2 Ht2) (real_opp (retm_LZ X u s0 l t1 Ht1))))
             H21 H12).
  - (* 纯代数：(b1−b2)E2 + (L1−L2) + (b2−b1)E1 + (L2−L1) == (b1−b2)(E2−E1) *)
    retm_alg.
Qed.

(* ============================================================ *)
(* G4 证据：全件零外部未证假设                                       *)
(* ============================================================ *)
Print Assumptions retm_Ztemp_pos.
Print Assumptions retm_pB_Z_mult.
Print Assumptions retm_pB_norm.
Print Assumptions retm_log_inv_pos_gen.
Print Assumptions retm_log_pB.
Print Assumptions retm_kl_point.
Print Assumptions retm_KL_decomp.
Print Assumptions retm_energy_temp_kl_pair_ident.
