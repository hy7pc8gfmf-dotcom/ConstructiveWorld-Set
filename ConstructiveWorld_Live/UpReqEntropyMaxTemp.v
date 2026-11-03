(* ==========================================================================)
   UpReqEntropyMaxTemp.v — 最大熵分布的温度参数刻画
   使命: real_max_entropy_is_boltzmann_temp_eps：固定能量下最大熵分布为 Boltzmann 分布的 ε 形；支撑件 real_sum_le_list_carrier_instance/le_plus_nonneg_r/plus_neg_cancel_shift_eps。
   依赖: CW_ConstructiveWorld_219、UpReqTempDefs、UpReqEntropyDeficitTemp。
   对标: 最大熵原理（变分刻画 Boltzmann-Gibbs 分布，统计力学经典）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
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
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.

(* ---------------------------------------------------------- *)
(* 件 0：接口非空证（具体载体实例）：real_list_sum 载体的逐点-求和        *)
(*   单调提升件已在库（S08 L421），抽象接口扩容位有现货满足证。           *)
(* ---------------------------------------------------------- *)
Corollary real_sum_le_list_carrier_instance :
  forall (X : Type) (f g : X -> Real) (l : list X),
    (forall w : X, real_le (f w) (g w)) ->
    real_le (real_list_sum X f l) (real_list_sum X g l).
Proof.
  exact (fun (X : Type) (f g : X -> Real) (l : list X)           (H : forall w : X, real_le (f w) (g w)) =>           real_list_sum_le X f g l H).
Qed.

(* ---------------------------------------------------------- *)
(* 辅助引理 A：0 ≤ b ⟹ a ≤ a+b（Id le_plus_nonneg_r Real 对位；            *)
(*   real_le_plus_compat + real_plus_zero（右零消去形 x+0 ≡ x））         *)
(* ---------------------------------------------------------- *)
Lemma real_le_plus_nonneg_r :
  forall a b : Real,
    real_le real_zero b -> real_le a (real_plus a b).
Proof.
  intros a b Hb.
  apply (RealSetoid.real_le_id_l a (real_plus a real_zero) (real_plus a b)           (real_eq_sym (real_plus a real_zero) a (real_plus_zero a))).
  exact (real_le_plus_compat a a real_zero b (real_le_refl a) Hb).
Qed.

(* ---------------------------------------------------------- *)
(* 辅助引理 B：a + ((b + (−a)) + eps) ≡ b + eps                            *)
(*   （Id minus_plus_cancel 的 eps 形副本；六肢换形链：assoc → 内层       *)
(*   assoc → comm → assoc 反向 → plus_opp → plus_zero）                   *)
(* ---------------------------------------------------------- *)
Lemma real_plus_neg_cancel_shift_eps :
  forall (a b eps : Real),
    real_eq (real_plus a (real_plus (real_plus b (real_opp a)) eps))
            (real_plus b eps).
Proof.
  intros a b eps.
  apply (real_eq_trans
           (real_plus a (real_plus (real_plus b (real_opp a)) eps))
           (real_plus (real_plus b real_zero) eps)
           (real_plus b eps)).
  - (* 肢 1a：换形五肢至 (b+0)+eps *)
    apply (real_eq_trans
             (real_plus a (real_plus (real_plus b (real_opp a)) eps))
             (real_plus (real_plus a (real_plus b (real_opp a))) eps)
             (real_plus (real_plus b real_zero) eps)).
    + exact (real_plus_assoc a (real_plus b (real_opp a)) eps).
    + apply (real_eq_trans
               (real_plus (real_plus a (real_plus b (real_opp a))) eps)
               (real_plus (real_plus (real_plus a b) (real_opp a)) eps)
               (real_plus (real_plus b real_zero) eps)).
      * apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_plus a (real_plus b (real_opp a)))
                 (real_plus (real_plus a b) (real_opp a))
                 eps eps
                 (real_plus_assoc a b (real_opp a))
                 (real_eq_refl eps)).
      * apply (real_eq_trans
                 (real_plus (real_plus (real_plus a b) (real_opp a)) eps)
                 (real_plus (real_plus b (real_plus a (real_opp a))) eps)
                 (real_plus (real_plus b real_zero) eps)).
        -- apply (real_eq_trans
                    (real_plus (real_plus (real_plus a b) (real_opp a)) eps)
                    (real_plus (real_plus (real_plus b a) (real_opp a)) eps)
                    (real_plus (real_plus b (real_plus a (real_opp a))) eps)).
           ++ apply (RealSetoid.real_eq_plus_compat_adapt
                       (real_plus (real_plus a b) (real_opp a))
                       (real_plus (real_plus b a) (real_opp a))
                       eps eps
                       (RealSetoid.real_eq_plus_compat_adapt
                          (real_plus a b) (real_plus b a)
                          (real_opp a) (real_opp a)
                          (real_plus_comm a b)
                          (real_eq_refl (real_opp a)))
                       (real_eq_refl eps)).
           ++ apply (RealSetoid.real_eq_plus_compat_adapt
                       (real_plus (real_plus b a) (real_opp a))
                       (real_plus b (real_plus a (real_opp a)))
                       eps eps
                       (real_eq_sym (real_plus b (real_plus a (real_opp a)))
                                    (real_plus (real_plus b a) (real_opp a))
                                    (real_plus_assoc b a (real_opp a)))
                       (real_eq_refl eps)).
        -- apply (RealSetoid.real_eq_plus_compat_adapt
                    (real_plus b (real_plus a (real_opp a)))
                    (real_plus b real_zero)
                    eps eps
                    (RealSetoid.real_eq_plus_compat_adapt
                       b b
                       (real_plus a (real_opp a)) real_zero
                       (real_eq_refl b)
                       (real_plus_opp a))
                    (real_eq_refl eps)).
  - (* 肢 1b：(b+0)+eps ≡ b+eps（plus_zero 右零消去形） *)
    apply (RealSetoid.real_eq_plus_compat_adapt
             (real_plus b real_zero) b
             eps eps
             (real_plus_zero b)
             (real_eq_refl eps)).
Qed.

(* ============================================================ *)
(* Section RealEntropyMaxTemp：求和面/温度/能量参数照 UpReqTempDefs      *)
(*   同名同序；扩容位：real_sum_over_S_le（紧随 ext，接口单调位）。      *)
(* ============================================================ *)
Section RealEntropyMaxTemp.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
(* 接口扩容位（T6b 余留指认；G06_BForm L35 / UpRealLeB L268 同形先例；   *)
(*   具体载体实例见本文件件 0：real_list_sum_le，S08 L421 在库）。       *)
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable energy : S -> Real.

(* ---------------------------------------------------------- *)
(* 件 1：KL 逐 eps 非负（Id gibbs_inequality 温度特化 Real 对位）：       *)
(*   归一 p、逐点正、eps > 0 ⟹ 0 ≤ KL(p‖p_T) + eps。                     *)
(*   链：桥（T6b 件 5）→ 逐点核（real_gibbs_core_eps）→ 扩容接口提升     *)
(*   → LHS 坍缩（Σp−p_T ≡ 1−1 ≡ 0）→ 误差坍缩（Σp·eps ≡ eps）。          *)
(* ---------------------------------------------------------- *)
Theorem real_KL_temp_ge_zero_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
           eps).
Proof.
  intros p Hp Hnp eps Hepspos.
  set (pT := real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy).
  set (HpT := real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                T T_pos energy).
  (* 0. 桥：KL ≡ Σ real_kl_term（T6b 件 5，全 arity 9 参显式应用） *)
  assert (Hbridge : real_eq
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
           (real_sum_over_S (fun s : S =>
              real_kl_term (p s) (pT s) (Hp s) (HpT s)))).
  { exact (real_KL_temp_kl_term_bridge S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext T T_pos energy p Hp). }
  (* 1. 逐点核：p − p_T ≤ real_kl_term + p·eps（显式应用；real_kl_term  *)
  (*    与 real_gibbs_core_eps RHS 首和项定义性一致，S08 L508 同款依存）  *)
  assert (Hpt : forall s : S,
           real_le (real_plus (p s) (real_opp (pT s)))
                   (real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                              (real_mult (p s) eps))).
  { intro s.
    exact (real_gibbs_core_eps (p s) (pT s) (Hp s) (HpT s) eps Hepspos). }
  (* 2. 求和面提升（扩容接口位） *)
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
  (* 3. LHS 坍缩：Σ(p − p_T) ≡ Σp + −Σp_T ≡ 1 + (−1) ≡ 0 *)
  assert (HnormT : real_eq (real_sum_over_S pT) real_one).
  { exact (real_boltzmann_dist_temp_normalized S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext real_sum_over_S_linear T T_pos energy). }
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
  (* 4. 误差坍缩：Σ(p·eps) ≡ Σ(eps·p) ≡ eps·Σp ≡ eps·1 ≡ eps *)
  assert (Heps : real_eq (real_sum_over_S (fun s : S => real_mult (p s) eps)) eps).
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
  (* 5. RHS 换形：Σ(kl + p·eps) ≡ Σkl + eps *)
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
               Heps).
  }
  (* 6. 组装：le 0 Σ(kl+p·eps) → le 0 (Σkl+eps) → le 0 (KL+eps)（两跳换形） *)
  exact (RealSetoid.real_le_id_r real_zero
           (real_plus
              (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
              eps)
           (real_plus
              (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
              eps)
           (RealSetoid.real_eq_plus_compat_adapt
              (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
              (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
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
(* 件 2（主件）：定理 4.6b 逐 eps 形（Id max_entropy_is_boltzmann_temp   *)
(*   S04 L3935 逐参数位对位）：同约束能量 E(p) == E_T ⟹ S[p] ≤ S[p_T] + eps。 *)
(*   链：熵亏温度版（T6b）→ KL 逐 eps 非负（件 1）→ le 链完成。          *)
(* ---------------------------------------------------------- *)
Theorem real_max_entropy_is_boltzmann_temp_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy) ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (real_entropy_dist S real_sum_over_S p Hp)
              (real_plus
                 (real_entropy_dist S real_sum_over_S
                    (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                       T T_pos energy)
                    (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                       T T_pos energy))
                 eps).
Proof.
  intros p Hp Hnp Henergy eps Hepspos.
  set (Sp := real_entropy_dist S real_sum_over_S p Hp).
  set (Spt := real_entropy_dist S real_sum_over_S
                (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                   T T_pos energy)
                (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                   T T_pos energy)).
  set (KL := real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp).
  (* 步 1：熵亏温度版（T6b 主件全 arity 13 参显式应用；Id Hdef 对位；          *)
  (*   real_minus_r 定义性展开 real_plus Spt (real_opp Sp)） *)
  assert (Hdef : real_eq (real_plus Spt (real_opp Sp)) KL).
  { exact (real_entropy_deficit_kl_temp S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext real_sum_over_S_linear real_sum_over_S_add
             T T_pos energy p Hp Hnp Henergy). }
  (* 步 2：KL 逐 eps 非负（件 1；Id Hkl 对位） *)
  assert (Hkl : real_le real_zero (real_plus KL eps)).
  { exact (real_KL_temp_ge_zero_eps p Hp Hnp eps Hepspos). }
  (* 步 3：换形到 Spt 肢（Id Hnonneg 对位；real_le_id_r + eq 兼容肢） *)
  assert (Hstep : real_le real_zero (real_plus (real_plus Spt (real_opp Sp)) eps)).
  { apply (RealSetoid.real_le_id_r real_zero (real_plus KL eps)
             (real_plus (real_plus Spt (real_opp Sp)) eps)
             (RealSetoid.real_eq_plus_compat_adapt KL (real_plus Spt (real_opp Sp))
                eps eps
                (real_eq_sym (real_plus Spt (real_opp Sp)) KL Hdef)
                (real_eq_refl eps))).
    exact Hkl. }
  (* 步 4：非负加法肢（辅助引理 A；Id Hle 对位） *)
  assert (H1 : real_le Sp (real_plus Sp (real_plus (real_plus Spt (real_opp Sp)) eps))).
  { exact (real_le_plus_nonneg_r Sp (real_plus (real_plus Spt (real_opp Sp)) eps)
             Hstep). }
  (* 步 5：完成（辅助引理 B eq 肢 + real_le_id_r；Id Hplus + 末步对位） *)
  exact (RealSetoid.real_le_id_r Sp
           (real_plus Sp (real_plus (real_plus Spt (real_opp Sp)) eps))
           (real_plus Spt eps)
           (real_plus_neg_cancel_shift_eps Sp Spt eps)
           H1).
Qed.

End RealEntropyMaxTemp.
