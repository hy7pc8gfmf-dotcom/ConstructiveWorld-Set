(* ==========================================================================)
   Arch_ToyR_04.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：gfe_le_of_lt（Gibbs 族）、bv_term（Beukers
   级数族）、pi_ptilde（p̃ 整化族）、bk_Qn_int（q̃ 整性族）。
   依赖：件内 Require 声明面所列库件；SecondLawQuantified 不在本世界可用
   库件之列，slc_minus_r_plus_cancel 等九件第二定律依存语句随该 Require
   一并移出本件，由其原件 SecondLawConsume.v 另件承载。
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
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
From Stdlib Require Import List.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import UpReqKLStrictB.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral.
Require Import PadeErrorIntegral BeukersLists PintMono.
Require Import BeukersLists HansonLcm.

(* ================= §2 gfe_le_of_lt 族 ================= *)
Import ListNotations.

(* Part 0：序代数支撑件（四件）                                          *)

(* 0.1 严格正到弱非负桥（温度前提降级：β>0 出口喂 β≥0 入口）。
   real_le 为 Or 编码（CW219 S02:460），lt 支 inl 直连——
   零中介件（S07 real_lt_le_iff_req 不入 CW219 聚合出口，实测）。 *)
Lemma gfe_le_of_lt : forall b : Real,
  real_lt real_zero b -> real_le real_zero b.
Proof.
  intros b Hb.
  exact (inl Hb).
Qed.

(* 0.2 (q−p)+(p−q) == 0：非对称对消核（assoc 三跳链，零 opp 分配依赖；
   对称 Jeffreys 形的对消引擎） *)
Lemma gfe_pq_shift_zero : forall p q : Real,
  real_eq (real_plus (real_plus q (real_opp p)) (real_plus p (real_opp q)))
          real_zero.
Proof.
  intros p q.
  assert (Hopp0 : real_eq (real_plus (real_opp p) p) real_zero).
  { exact (real_eq_trans (real_plus (real_opp p) p)
                         (real_plus p (real_opp p)) real_zero
             (real_plus_comm (real_opp p) p) (real_plus_opp p)). }
  (* 步1：assoc 两跳把 p 肢并入 q 肢 *)
  assert (Hs1 : real_eq (real_plus (real_plus q (real_opp p))
                                   (real_plus p (real_opp q)))
                        (real_plus (real_plus q (real_plus (real_opp p) p))
                                   (real_opp q))).
  { apply (real_eq_trans
             (real_plus (real_plus q (real_opp p)) (real_plus p (real_opp q)))
             (real_plus (real_plus (real_plus q (real_opp p)) p) (real_opp q))
             (real_plus (real_plus q (real_plus (real_opp p) p)) (real_opp q))).
    - exact (real_plus_assoc (real_plus q (real_opp p)) p (real_opp q)).
    - apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_plus q (real_opp p)) p)
               (real_opp q)
               (real_plus q (real_plus (real_opp p) p))
               (real_opp q)).
      + apply (real_eq_sym (real_plus q (real_plus (real_opp p) p))
                           (real_plus (real_plus q (real_opp p)) p)).
        exact (real_plus_assoc q (real_opp p) p).
      + apply real_eq_refl. }
  (* 步2：内层 (−p)+p 对消为 0 *)
  assert (Hs2 : real_eq (real_plus (real_plus q (real_plus (real_opp p) p))
                                   (real_opp q))
                        (real_plus (real_plus q real_zero) (real_opp q))).
  { apply (RealSetoid.real_eq_plus_compat
             (real_plus q (real_plus (real_opp p) p))
             (real_opp q)
             (real_plus q real_zero)
             (real_opp q)).
    - apply (RealSetoid.real_eq_plus_compat q
               (real_plus (real_opp p) p) q real_zero).
      + apply real_eq_refl.
      + exact Hopp0.
    - apply real_eq_refl. }
  (* 步3+4：(q+0)+(−q) 换形后 plus_opp 闭合 *)
  assert (Hs3 : real_eq (real_plus (real_plus q real_zero) (real_opp q))
                        real_zero).
  { apply (real_eq_trans
             (real_plus (real_plus q real_zero) (real_opp q))
             (real_plus q (real_opp q))
             real_zero).
    - apply (RealSetoid.real_eq_plus_compat (real_plus q real_zero)
               (real_opp q) q (real_opp q)).
      + exact (real_plus_zero q).
      + apply real_eq_refl.
    - exact (real_plus_opp q). }
  exact (real_eq_trans
           (real_plus (real_plus q (real_opp p)) (real_plus p (real_opp q)))
           (real_plus (real_plus q (real_plus (real_opp p) p)) (real_opp q))
           real_zero
           Hs1
           (real_eq_trans
              (real_plus (real_plus q (real_plus (real_opp p) p)) (real_opp q))
              (real_plus (real_plus q real_zero) (real_opp q))
              real_zero Hs2 Hs3)).
Qed.

(* 0.3 平移对消恒等式：(a+s)+(d+t) == a+d（当 s+t == 0）；
   swap_mid 一跳闭合——对称 Jeffreys 主恒等式的引擎 *)
Lemma gfe_sym_sum_eq : forall (a d s t : Real),
  real_eq (real_plus s t) real_zero ->
  real_eq (real_plus (real_plus a s) (real_plus d t)) (real_plus a d).
Proof.
  intros a d s t Hst.
  apply (real_eq_trans
           (real_plus (real_plus a s) (real_plus d t))
           (real_plus (real_plus a d) (real_plus s t))
           (real_plus a d)).
  - exact (real_plus_swap_mid a s d t).
  - apply (real_eq_trans
             (real_plus (real_plus a d) (real_plus s t))
             (real_plus (real_plus a d) real_zero)
             (real_plus a d)).
    + apply (RealSetoid.real_eq_plus_compat (real_plus a d) (real_plus s t)
               (real_plus a d) real_zero).
      * apply real_eq_refl.
      * exact Hst.
    + exact (real_plus_zero (real_plus a d)).
Qed.

(* 0.4 Bishop 形右元换形器（族级组合器：le_b x y + y==z 给 le_b x z；
   左元换形 leb3_le_b_eq_l 的对偶件，UpRealLeB3 无右元版） *)
Lemma gfe_le_b_eq_r : forall (x y z : Real),
  real_le_b x y -> real_eq y z -> real_le_b x z.
Proof.
  intros x y z Hxy Heq. unfold real_le_b in Hxy. unfold real_le_b.
  intros eps Heps.
  apply (RealSetoid.real_lt_compat x x
           (real_plus y eps) (real_plus z eps)).
  - apply real_eq_refl.
  - apply (RealSetoid.real_eq_plus_compat y eps z eps).
    + exact Heq.
    + apply real_eq_refl.
  - exact (Hxy eps Heps).
Qed.

(* Part A：温度参数化形（真缺变体面 A；β 加权 Gibbs 族五件）             *)

(* A1 温度参数化逐点核 eps 形（β ≥ 0 弱前提——容许零温退化）：
   β·(p−q) ≤ β·kl(p‖q) + β·p·eps。
   证书链：real_gibbs_core_eps → 左乘保序 real_le_mult_compat_r
   → distrib 换形（三步组装，系数全程显式追踪）。 *)
Lemma gfe_gibbs_core_temp_eps : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_le real_zero b) (eps : Real) (Heps : real_lt real_zero eps),
  real_le (real_mult b (real_plus p (real_opp q)))
          (real_plus (real_mult b (real_kl_term p q Hp Hq))
                     (real_mult b (real_mult p eps))).
Proof.
  intros p q b Hp Hq Hb eps Heps.
  apply (RealSetoid.real_le_id_r
           (real_mult b (real_plus p (real_opp q)))
           (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                   (real_mult p eps)))
           (real_plus (real_mult b (real_kl_term p q Hp Hq))
                      (real_mult b (real_mult p eps)))).
  - exact (real_distrib b (real_kl_term p q Hp Hq) (real_mult p eps)).
  - exact (real_le_mult_compat_r b (real_plus p (real_opp q))
             (real_plus (real_kl_term p q Hp Hq) (real_mult p eps)) Hb
             (real_gibbs_core_eps p q Hp Hq eps Heps)).
Qed.

(* A2 温度参数化逐点核 Bishop 形（β > 0 严格前提）：
   β·(p−q) ≤_B β·kl(p‖q)。
   闭合器：real_le_closure_b，D := β·p（正性证书 real_mult_positive）；
   逐 eps 余量 (β·p)·eps 由 A1 经 mult_assoc 换形供给。
   注：β = 0 时 D 证书无从供给——Bishop 形前提强于 eps 形，
   即 §4.3 形态选择在温度参数化下的构造性分化。 *)
Theorem gfe_gibbs_core_temp_B : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_lt real_zero b),
  real_le_b (real_mult b (real_plus p (real_opp q)))
            (real_mult b (real_kl_term p q Hp Hq)).
Proof.
  intros p q b Hp Hq Hb.
  apply (real_le_closure_b
           (real_mult b (real_plus p (real_opp q)))
           (real_mult b (real_kl_term p q Hp Hq))
           (real_mult b p) (real_mult_positive b p Hb Hp)).
  intros eps Heps.
  apply (RealSetoid.real_le_id_r
           (real_mult b (real_plus p (real_opp q)))
           (real_plus (real_mult b (real_kl_term p q Hp Hq))
                      (real_mult b (real_mult p eps)))
           (real_plus (real_mult b (real_kl_term p q Hp Hq))
                      (real_mult (real_mult b p) eps))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult b (real_kl_term p q Hp Hq))
             (real_mult b (real_mult p eps))
             (real_mult b (real_kl_term p q Hp Hq))
             (real_mult (real_mult b p) eps)).
    + apply real_eq_refl.
    + exact (real_mult_assoc b p eps).
  - exact (gfe_gibbs_core_temp_eps p q b Hp Hq (gfe_le_of_lt b Hb) eps Heps).
Qed.

(* A3 温度参数化有限和 eps 形（β ≥ 0 弱前提）：
   0 ≤ β·Σ_s kl(p s‖q s) + β·eps。
   证书链：real_gibbs_inequality_eps → 左乘保序 → distrib 换形，
   左端 β·0 == 0 经 mult_zero 换形（归一化消去在温度下保持）。 *)
Lemma gfe_gibbs_inequality_temp_eps : forall (X : Type) (l : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hnormp : real_eq (real_list_sum X p l) real_one)
  (Hnormq : real_eq (real_list_sum X q l) real_one)
  (b : Real) (Hb : real_le real_zero b) (eps : Real)
  (Heps : real_lt real_zero eps),
  real_le real_zero
    (real_plus (real_mult b (real_list_sum X
                  (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))
               (real_mult b eps)).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq b Hb eps Heps.
  apply (RealSetoid.real_le_id_l real_zero (real_mult b real_zero)
           (real_plus
              (real_mult b (real_list_sum X
                  (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))
              (real_mult b eps))).
  - exact (real_eq_sym (real_mult b real_zero) real_zero (real_mult_zero b)).
  - apply (RealSetoid.real_le_id_r (real_mult b real_zero)
             (real_mult b (real_plus (real_list_sum X
                  (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
                  eps))
             (real_plus
                (real_mult b (real_list_sum X
                   (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))
                (real_mult b eps))).
    + exact (real_distrib b (real_list_sum X
                 (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
                 eps).
    + exact (real_le_mult_compat_r b real_zero
                (real_plus (real_list_sum X
                    (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
                  eps) Hb
                (real_gibbs_inequality_eps X l p q Hp Hq Hnormp Hnormq
                   eps Heps)).
Qed.

(* A4 温度参数化有限和 Bishop 形（β > 0 严格前提）：
   0 ≤_B β·Σ_s kl(p s‖q s)。
   闭合器：real_le_closure_b，D := β；A3 出口余量形状
   (β·Σkl) + β·eps 与 closure 供给形 y + D·eps 逐字同形，一步直接代入。 *)
Theorem gfe_gibbs_inequality_temp_B : forall (X : Type) (l : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hnormp : real_eq (real_list_sum X p l) real_one)
  (Hnormq : real_eq (real_list_sum X q l) real_one)
  (b : Real) (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_list_sum X
        (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq b Hb.
  apply (real_le_closure_b real_zero           (real_mult b (real_list_sum X               (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))           b Hb).
  intros eps Heps.
  exact (gfe_gibbs_inequality_temp_eps X l p q Hp Hq Hnormp Hnormq b           (gfe_le_of_lt b Hb) eps Heps).
Qed.

(* A5 族级组合器：Bishop 形正数乘保序器（全库无 ≤_B 乘法出口，本件补位）：
   x ≤_B y ∧ 0 < β ⟹ β·x ≤_B β·y。
   证书链：le_b 逐 eps 展形 → real_lt_le_iff_req 升 le →
   左乘保序 → distrib 换形 → closure_b（D := β）再闭合。 *)
Lemma gfe_le_b_mult_pos : forall (x y b : Real),
  real_lt real_zero b -> real_le_b x y -> real_le_b (real_mult b x) (real_mult b y).
Proof.
  intros x y b Hb Hxy.
  apply (real_le_closure_b (real_mult b x) (real_mult b y) b Hb).
  intros eps Heps.
  apply (RealSetoid.real_le_id_r (real_mult b x)
           (real_mult b (real_plus y eps))
           (real_plus (real_mult b y) (real_mult b eps))).
  - exact (real_distrib b y eps).
  - apply (real_le_mult_compat_r b x (real_plus y eps) (gfe_le_of_lt b Hb)).
    exact (inl (Hxy eps Heps)).
Qed.

(* A6 温度参数化无条件 gap Bishop 形（β > 0）：
   0 ≤_B β·(kl(p‖q) + (q−p))。
   证书链：klstb_gibbs_core_shift_B（零前提 gap Bishop 形）经 A5 组合器
   一次升温——第二定律读法在温度缩放下的不变性。 *)
Theorem gfe_gibbs_temp_gap_B : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_plus (real_kl_term p q Hp Hq)
                            (real_plus q (real_opp p)))).
Proof.
  intros p q b Hp Hq Hb.
  apply (leb3_le_b_eq_l (real_mult b real_zero) real_zero
           (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                   (real_plus q (real_opp p))))).
  - exact (real_mult_zero b).
  - exact (gfe_le_b_mult_pos real_zero
             (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
             b Hb (klstb_gibbs_core_shift_B p q Hp Hq)).
Qed.

(* A6b 展开形推论：0 ≤_B β·kl(p‖q) + β·(q−p)（distrib 换形面）。 *)
Lemma gfe_gibbs_temp_gap_B_flat : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_plus (real_mult b (real_kl_term p q Hp Hq))
               (real_mult b (real_plus q (real_opp p)))).
Proof.
  intros p q b Hp Hq Hb.
  apply (gfe_le_b_eq_r real_zero
           (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                   (real_plus q (real_opp p))))
           (real_plus (real_mult b (real_kl_term p q Hp Hq))
                      (real_mult b (real_plus q (real_opp p))))).
  - exact (gfe_gibbs_temp_gap_B p q b Hp Hq Hb).
  - exact (real_distrib b (real_kl_term p q Hp Hq)
             (real_plus q (real_opp p))).
Qed.

(* Part B：对称 Jeffreys 形（真缺变体面 B；非对称互补面两件）            *)

(* B1 对称 Jeffreys 逐点 Bishop 形（非对称形的互补闭合）：
   0 ≤_B kl(p‖q) + kl(q‖p)。
   证书链：klstb 两支 shift 形各自 ≥_B 0 → real_le_b_plus_compat
   相加 → 平移对消项 (q−p)+(p−q) 经 gfe_sym_sum_eq（swap_mid 引擎）
   从和式中闭合剥除。 *)
Theorem gfe_jeffreys_sym_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_le_b real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_kl_term q p Hq Hp)).
Proof.
  intros p q Hp Hq.
  apply (gfe_le_b_eq_r real_zero
           (real_plus (real_plus (real_kl_term p q Hp Hq)
                                 (real_plus q (real_opp p)))
                      (real_plus (real_kl_term q p Hq Hp)
                                 (real_plus p (real_opp q))))
           (real_plus (real_kl_term p q Hp Hq) (real_kl_term q p Hq Hp))).
  - apply (leb3_le_b_eq_l (real_plus real_zero real_zero) real_zero _
             (real_plus_zero real_zero)
             (real_le_b_plus_compat real_zero
                (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
                real_zero
                (real_plus (real_kl_term q p Hq Hp) (real_plus p (real_opp q)))
                (klstb_gibbs_core_shift_B p q Hp Hq)
                (klstb_gibbs_core_shift_B q p Hq Hp))).
  - exact (gfe_sym_sum_eq (real_kl_term p q Hp Hq) (real_kl_term q p Hq Hp)
             (real_plus q (real_opp p)) (real_plus p (real_opp q))
             (gfe_pq_shift_zero p q)).
Qed.

(* B2 对称 Jeffreys 有限和 Bishop 形：
   0 ≤_B Σ_s (kl(p s‖q s) + kl(q s,p s))。
   证书链：klstb_list_sum_le_b 逐点喂 B1 + 零常量和 klstb_list_sum_zero
   换形（求和层闭合对称族）。 *)
Theorem gfe_jeffreys_sym_list_B : forall (X : Type) (l : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s)),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                               (real_kl_term (q s) (p s) (Hq s) (Hp s))) l).
Proof.
  intros X l p q Hp Hq.
  apply (leb3_le_b_eq_l
           (real_list_sum X (fun _ : X => real_zero) l)
           real_zero
           (real_list_sum X
              (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                      (real_kl_term (q s) (p s) (Hq s) (Hp s)))
              l)).
  - exact (klstb_list_sum_zero X l).
  - apply (klstb_list_sum_le_b X (fun _ : X => real_zero)
             (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                     (real_kl_term (q s) (p s) (Hq s) (Hp s)))
             l).
    intro s. exact (gfe_jeffreys_sym_B (p s) (q s) (Hp s) (Hq s)).
Qed.

(* 闭合审计（G4：Print Assumptions 全 Closed）                           *)

Print Assumptions gfe_le_of_lt.
Print Assumptions gfe_pq_shift_zero.
Print Assumptions gfe_sym_sum_eq.
Print Assumptions gfe_le_b_eq_r.
Print Assumptions gfe_gibbs_core_temp_eps.
Print Assumptions gfe_gibbs_core_temp_B.
Print Assumptions gfe_gibbs_inequality_temp_eps.
Print Assumptions gfe_gibbs_inequality_temp_B.
Print Assumptions gfe_le_b_mult_pos.
Print Assumptions gfe_gibbs_temp_gap_B.
Print Assumptions gfe_gibbs_temp_gap_B_flat.
Print Assumptions gfe_jeffreys_sym_B.
Print Assumptions gfe_jeffreys_sym_list_B.
(* ================= §3 bv_term 族 ================= *)
From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.

Open Scope nat_scope.

(* §A 级数定形：级数项 bv_term = C(n+m,n)·B(n+2m+1, 2n+1) 与其正性        *)

Definition bv_term (n m : nat) : Q :=
  ((Z.of_nat (bkC (n + m) n) # 1) *
     (q_fact (n + 2 * m) * q_fact (2 * n + 1) / q_fact (3 * n + 2 * m + 2)))%Q.

(* bv_term n m == C(n+m,n)·∫₀¹ t^{n+2m}(1−t)^{2n+1} dt（由 pei_beta_value 归到 pint_integral） *)
Lemma bv_term_value : forall n m : nat,
  bv_term n m ==
  ((Z.of_nat (bkC (n + m) n) # 1) * pint_integral (pei_list (n + 2 * m) (2 * n + 1)))%Q.
Proof.
  intros n m. unfold bv_term.
  rewrite (qeqT_imp_qeq _ _ (pei_beta_value (n + 2 * m) (2 * n + 1))).
  replace ((n + 2 * m) + (2 * n + 1) + 1)%nat with (3 * n + 2 * m + 2)%nat by lia.
  reflexivity.
Qed.

(** bv_term_pos：级数项严格正——bkC ≥ 1 与 q_fact 正性相乘。 *)
Theorem bv_term_pos : forall n m : nat, QltT 0 (bv_term n m).
Proof.
  intros n m. apply Qlt_to_QltT. unfold bv_term. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - assert (Hb : NatLe 1 (bkC (n + m) n)) by (apply bkC_pos; apply NatLe_lift; lia).
    pose proof (NatLe_drop _ _ Hb) as HbP.
    assert (Hz : (0 <= Z.of_nat (bkC (n + m) n))%Z) by apply Nat2Z.is_nonneg.
    unfold Qlt. cbn [Qnum Qden Qmult Pos.mul]. lia.
  - apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos.
    + apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* §B 截断承载：bv_pad（补两个零系数）与 bv_carrier（pei_eb_list 同型）   *)

Definition bv_pad (p : list Q) : list Q := pei_ztail (pei_ztail p).

Lemma bv_pad_eval : forall (p : list Q) (x : Q),
  pint_eval (bv_pad p) x == pint_eval p x.
Proof.
  intros p x. unfold bv_pad.
  rewrite (qeqT_imp_qeq _ _ (pei_eval_ztail (pei_ztail p) x)),
          (qeqT_imp_qeq _ _ (pei_eval_ztail p x)).
  reflexivity.
Qed.

Lemma bv_pad_int : forall p : list Q,
  pint_integral (bv_pad p) == pint_integral p.
Proof.
  intro p. unfold bv_pad.
  rewrite (qeqT_imp_qeq _ _ (pei_integral_ztail (pei_ztail p))),
          (qeqT_imp_qeq _ _ (pei_integral_ztail p)).
  reflexivity.
Qed.

Lemma bv_pad_length : forall p : list Q, length (bv_pad p) = (length p + 2)%nat.
Proof.
  intro p. unfold bv_pad, pei_ztail.
  rewrite app_length, app_length. cbn [length]. lia.
Qed.

(* bv_carrier n M：部分和 Σ_{m≤M} C(n+m,n)·t^{n+2m}(1−t)^{2n+1} 的系数表（pei_eb_list 同型） *)
Fixpoint bv_carrier (n M : nat) : list Q :=
  match M with
  | 0 => pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                    (pei_list (n + 2 * 0) (2 * n + 1))
  | Datatypes.S m =>
      pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                           (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
               (bv_pad (bv_carrier n m))
  end.

Lemma bv_carrier_length : forall n M : nat,
  length (bv_carrier n M) = (3 * n + 2 * M + 2)%nat.
Proof.
  intros n M. induction M as [| m IH].
  - change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    rewrite (RealSetoid.Id_eq _ _
              (pei_scale_length ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                                (pei_list (n + 2 * 0) (2 * n + 1)))),
            (RealSetoid.Id_eq _ _
              (pei_list_length (n + 2 * 0) (2 * n + 1))).
    lia.
  - change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                    (bv_pad (bv_carrier n m))).
    assert (HL : Id (length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                        (pei_list (n + 2 * Datatypes.S m) (2 * n + 1))))
                    (length (bv_pad (bv_carrier n m)))).
    { apply RealSetoid.eq_Id.
      rewrite (RealSetoid.Id_eq _ _
                (pei_scale_length ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                  (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))),
              (RealSetoid.Id_eq _ _
                (pei_list_length (n + 2 * Datatypes.S m) (2 * n + 1))),
              bv_pad_length, IH. lia. }
    rewrite (RealSetoid.Id_eq _ _ (pei_add_length
              (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                          (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
              (bv_pad (bv_carrier n m)) HL)),
            (RealSetoid.Id_eq _ _
              (pei_scale_length ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))),
            (RealSetoid.Id_eq _ _
              (pei_list_length (n + 2 * Datatypes.S m) (2 * n + 1))).
    lia.
Qed.

(** bv_carrier_eval：逐点值 == tⁿ(1−t)^{2n+1}·Σ_{m≤M} C(n+m,n)(t²)^m（负二项型截断）。 *)
Theorem bv_carrier_eval : forall (n M : nat) (t : Q),
  pint_eval (bv_carrier n M) t ==
  q_pow t n * q_pow (1 - t)%Q (2 * n + 1) *
    bk_psQ (fun m : nat => (Z.of_nat (bkC (n + m) n) # 1)%Q)
           (Datatypes.S M) (t * t)%Q.
Proof.
  intros n M. induction M as [| m IH]; intro t.
  - change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    change (bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                   (Datatypes.S 0) (t * t)%Q)
      with (0 + (Z.of_nat (bkC (n + 0) n) # 1) * 1)%Q.
    rewrite (qeqT_imp_qeq _ _
              (pei_eval_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                              (pei_list (n + 2 * 0) (2 * n + 1)) t)).
    rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + 2 * 0) (2 * n + 1) t)).
    replace (n + 2 * 0)%nat with n%nat by lia.
    ring.
  - change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                    (bv_pad (bv_carrier n m))).
    rewrite (qeqT_imp_qeq _ _
              (pei_eval_add
                 (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                             (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                 (bv_pad (bv_carrier n m)) t)).
    rewrite (qeqT_imp_qeq _ _
              (pei_eval_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                              (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)) t)).
    rewrite (qeqT_imp_qeq _ _
              (pei_beta_eval (n + 2 * Datatypes.S m) (2 * n + 1) t)).
    rewrite (bv_pad_eval (bv_carrier n m) t).
    rewrite (IH t).
    assert (HpsQ : bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                          (Datatypes.S (Datatypes.S m)) (t * t)%Q
                   == bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                          (Datatypes.S m) (t * t)%Q
                      + (Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q
                          * q_pow (t * t)%Q (Datatypes.S m))
      by reflexivity.
    rewrite HpsQ.
    rewrite (qeqT_imp_qeq _ _ (q_pow_add t n (2 * Datatypes.S m))).
    replace (2 * Datatypes.S m)%nat with (Datatypes.S m + Datatypes.S m)%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (q_pow_add t (Datatypes.S m) (Datatypes.S m))).
    rewrite <- (qeqT_imp_qeq _ _ (bk_q_pow_mul t t (Datatypes.S m))).
    ring.
Qed.

(* §C 截断积分：bv_carrier_value 精确值、bv_sum_mono 单调、bv_sum_pos 正性  *)

Fixpoint bv_zeros (L : nat) : list Q :=
  match L with
  | 0 => nil
  | Datatypes.S m => 0%Q :: bv_zeros m
  end.

Lemma bv_zeros_length : forall L : nat, length (bv_zeros L) = L.
Proof.
  induction L as [| l IH].
  - reflexivity.
  - cbn [bv_zeros length]. rewrite IH. reflexivity.
Qed.

Lemma bv_zeros_int : forall (L k : nat), pint_integral_from (bv_zeros L) k == 0%Q.
Proof.
  induction L as [| l IH]; intros k.
  - reflexivity.
  - cbn [bv_zeros pint_integral_from]. unfold pint_monomial_int.
    rewrite (qeqT_imp_qeq _ _ (pint_zero_div (Z.of_nat (Datatypes.S k) # 1))),
            Qplus_0_l. apply IH.
Qed.

Theorem bv_zeros_int0 : forall L : nat, pint_integral (bv_zeros L) == 0%Q.
Proof. intro L. unfold pint_integral. apply bv_zeros_int. Qed.

Lemma bv_c_pos_le : forall n m : nat, QleT' 0 ((Z.of_nat (bkC (n + m) n) # 1)%Q).
Proof.
  intros n m. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
  assert (Hb : NatLe 1 (bkC (n + m) n)) by (apply bkC_pos; apply NatLe_lift; lia).
  pose proof (NatLe_drop _ _ Hb) as HbP.
  assert (Hz : (0 <= Z.of_nat (bkC (n + m) n))%Z) by apply Nat2Z.is_nonneg.
  lia.
Qed.

Lemma bv_pos_cint : forall n m : nat,
  QleT' 0 (pint_integral (pei_list (n + 2 * m) (2 * n + 1))).
Proof.
  intros n m.
  exact (Qle_to_QleT' 0
    (pint_integral (pei_list (n + 2 * m) (2 * n + 1)))
    (Qlt_le_weak 0 (pint_integral (pei_list (n + 2 * m) (2 * n + 1)))
       (QltT_to_Qlt 0 (pint_integral (pei_list (n + 2 * m) (2 * n + 1)))
          (pei_beta_pos (n + 2 * m) (2 * n + 1))))).
Qed.

(** bv_carrier_value：截断积分 == 级数部分和 Σ_{m≤M} bv_term n m（精确 QeqT）。 *)
Theorem bv_carrier_value : forall n M : nat,
  pint_integral (bv_carrier n M) == sum_upto (Datatypes.S M) (fun m : nat => bv_term n m).
Proof.
  intros n M. induction M as [| m IH].
  - change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    change (sum_upto (Datatypes.S 0) (fun m0 : nat => bv_term n m0))
      with (0 + bv_term n 0)%Q.
    rewrite (qeqT_imp_qeq _ _
              (pint_integral_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                                   (pei_list (n + 2 * 0) (2 * n + 1)))).
    rewrite (qeqT_imp_qeq _ _ (pei_beta_value (n + 2 * 0) (2 * n + 1))).
    unfold bv_term.
    replace (n + 2 * 0)%nat with n%nat by lia.
    replace (3 * n + 2 * 0 + 2)%nat with (n + (2 * n + 1) + 1)%nat by lia.
    ring.
  - change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                    (bv_pad (bv_carrier n m))).
    change (sum_upto (Datatypes.S (Datatypes.S m)) (fun m0 : nat => bv_term n m0))
      with (sum_upto (Datatypes.S m) (fun m0 : nat => bv_term n m0)
              + bv_term n (Datatypes.S m))%Q.
    assert (HL : length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                    (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                 = length (bv_pad (bv_carrier n m))).
    { rewrite (RealSetoid.Id_eq _ _
                (pei_scale_length ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                  (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))),
              (RealSetoid.Id_eq _ _
                (pei_list_length (n + 2 * Datatypes.S m) (2 * n + 1))),
              bv_pad_length, bv_carrier_length. lia. }
    rewrite (qeqT_imp_qeq _ _ (pint_integral_add _ _ HL)).
    rewrite (bv_pad_int (bv_carrier n m)).
    rewrite (qeqT_imp_qeq _ _
              (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                   (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))).
    rewrite (qeqT_imp_qeq _ _
              (pei_beta_value (n + 2 * Datatypes.S m) (2 * n + 1))),
            IH. unfold bv_term.
    replace ((n + 2 * Datatypes.S m) + (2 * n + 1) + 1)%nat
      with (3 * n + 2 * Datatypes.S m + 2)%nat by lia.
    ring.
Qed.

(** bv_sum_mono：截断积分对 M 单调（QleT'）；由 PintMono 的 pm_scale_mono、
   pm_add_mono 与同值替换 pm_qle_wd_l、pm_qle_wd_r 合成。 *)
Theorem bv_sum_mono : forall n M : nat,
  QleT' (pint_integral (bv_carrier n M))
        (pint_integral (bv_carrier n (Datatypes.S M))).
Proof.
  intros n M.
  change (pint_integral (bv_carrier n (Datatypes.S M)))
    with (pint_integral (pint_add
             (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                         (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
             (bv_pad (bv_carrier n M)))).
  assert (Hlen : length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                    (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
                 = length (bv_pad (bv_carrier n M))).
  { rewrite pei_scale_length, pei_list_length, bv_pad_length, bv_carrier_length. lia. }
  assert (HId1 : Id (length (bv_zeros (3 * n + 2 * M + 2 + 2)))
                    (length (bv_pad (bv_carrier n M)))).
  { rewrite bv_zeros_length, bv_pad_length, bv_carrier_length. reflexivity. }
  assert (HId2 : Id (length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                        (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
                    (length (bv_pad (bv_carrier n M)))).
  { rewrite <- Hlen. reflexivity. }
  (* 中间断言 HleX：0 ≤ C(n+M,n)·∫t^{n+2M}(1−t)^{2n+1}，经 bv_c_pos_le、bv_pos_cint 与 pm_scale_mono。 *)
  assert (HleX : QleT' 0 (pint_integral
                    (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))).
  { apply (pm_qle_wd_r
             (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
               pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)
             (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                        (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
             0%Q).
    - apply Qeq_sym. apply qeqT_imp_qeq.
      apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
    - apply (pm_qle_wd_l
               (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                          (bv_zeros (3 * n + 2 * M + 2 + 2))))
               0%Q
               (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                 pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)).
      + transitivity (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                       pint_integral (bv_zeros (3 * n + 2 * M + 2 + 2)))%Q).
        * apply qeqT_imp_qeq.
          apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                     (bv_zeros (3 * n + 2 * M + 2 + 2))).
        * rewrite bv_zeros_int0. apply Qmult_0_r.
      + apply (pm_qle_wd_r
                 (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                            (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
                 (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                   pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)
                 (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                            (bv_zeros (3 * n + 2 * M + 2 + 2))))).
        * apply qeqT_imp_qeq.
          apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                     (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
        * apply (pm_scale_mono ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                   (bv_zeros (3 * n + 2 * M + 2 + 2))
                   (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
          -- apply bv_c_pos_le.
          -- apply (pm_qle_wd_l 0%Q _ _).
             ++ apply Qeq_sym. apply bv_zeros_int0.
             ++ apply bv_pos_cint. }
  (* 中间断言 Hmove：bv_zeros 与 bv_pad (bv_carrier n M) 之和的积分 == pint_integral (bv_carrier n M)。 *)
  assert (Hmove : pint_integral (pint_add (bv_zeros (3 * n + 2 * M + 2 + 2))
                                          (bv_pad (bv_carrier n M)))
                 == pint_integral (bv_carrier n M)).
  { assert (HLz : length (bv_zeros (3 * n + 2 * M + 2 + 2))
                  = length (bv_pad (bv_carrier n M)))
      by (rewrite bv_zeros_length, bv_pad_length, bv_carrier_length; reflexivity).
    rewrite (qeqT_imp_qeq _ _ (pint_integral_add _ _ HLz)).
    rewrite bv_zeros_int0, bv_pad_int. ring. }
  apply (pm_qle_wd_l
           (pint_integral (pint_add (bv_zeros (3 * n + 2 * M + 2 + 2))
                                    (bv_pad (bv_carrier n M))))
           (pint_integral (bv_carrier n M))
           (pint_integral (pint_add
                (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                            (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
                (bv_pad (bv_carrier n M))))).
  - exact Hmove.
  - apply (pm_add_mono (bv_zeros (3 * n + 2 * M + 2 + 2))
             (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                         (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
             (bv_pad (bv_carrier n M)) (bv_pad (bv_carrier n M))).
    + exact HId1.
    + exact HId2.
    + apply (pm_qle_wd_l 0%Q _ _).
      * apply Qeq_sym. apply bv_zeros_int0.
      * exact HleX.
    + apply qleT'_refl.
Qed.

(* bv_sum_upto_pos：部分和严格正（对 M 归纳；由 bv_term_pos 与 pei_lt_le_plus） *)
Lemma bv_sum_upto_pos : forall n M : nat,
  QltT 0 (sum_upto (Datatypes.S M) (fun m : nat => bv_term n m)).
Proof.
  intros n. induction M as [| m IH].
  - change (sum_upto (Datatypes.S 0) (fun m0 : nat => bv_term n m0))
      with (0 + bv_term n 0)%Q.
    apply (pei_qeq_lt (bv_term n 0) (0 + bv_term n 0)%Q 0%Q).
    + apply qeq_imp_qeqT. ring.
    + exact (bv_term_pos n 0).
  - change (sum_upto (Datatypes.S (Datatypes.S m)) (fun m0 : nat => bv_term n m0))
      with (sum_upto (Datatypes.S m) (fun m0 : nat => bv_term n m0)
              + bv_term n (Datatypes.S m))%Q.
    apply pei_lt_le_plus.
    + exact IH.
    + apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt. apply bv_term_pos.
Qed.

(** bv_sum_pos：截断积分严格正——由 bv_carrier_value 换为部分和，再用 bv_sum_upto_pos。 *)
Theorem bv_sum_pos : forall n M : nat,
  QltT 0 (pint_integral (bv_carrier n M)).
Proof.
  intros n M.
  apply (pei_qeq_lt (sum_upto (Datatypes.S M) (fun m : nat => bv_term n m))
                    (pint_integral (bv_carrier n M)) 0%Q).
  - apply qeq_imp_qeqT. apply Qeq_sym.
    exact (bv_carrier_value n M).
  - exact (bv_sum_upto_pos n M).
Qed.

(* §D ln2 系数离散核：bv_delannoy_eq_qtilde（升幂 Delannoy 和 == q̃_n）    *)
(*   bv_D_asc n == Σ_{a≤n} C(n,a)²·2^a（经 bk_psd_ext、bk_Qn_sym 调整次序）；*)
(*   系数恒等式：[u^n](u−1)ⁿ(2−u)ⁿ = Σ_{a+b=n} C(n,a)C(n,b)2^{n−b}(−1)^{n−a+b}；*)
(*   取 b=n−a 时符号 (−1)^{2n−2a}=1，故 = Σ_a C(n,a)²2^a = D_n = q̃_n。   *)

Definition bv_D_asc (n : nat) : nat :=
  bk_psd (fun k => bkC n (n - k) * bkC n (n - k)) (Datatypes.S n).

Theorem bv_delannoy_eq_qtilde : forall n : nat,
  QeqT ((Z.of_nat (bv_D_asc n) # 1)%Q) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n. apply qeq_imp_qeqT. unfold bv_D_asc.
  assert (H : Id (bk_psd (fun k => bkC n (n - k) * bkC n (n - k)) (Datatypes.S n))
                 (bk_psd (fun k => bkC n k * bkC n k) (Datatypes.S n))).
  { apply bk_psd_ext. intros k Hk.
    assert (Hle : k <= n) by (pose proof (NatLe_drop _ _ Hk); lia).
    pose proof (RealSetoid.Id_eq _ _ (bk_Qn_sym n k (NatLe_lift _ _ Hle))) as Hq.
    rewrite <- Hq. reflexivity. }
  pose proof (RealSetoid.Id_eq _ _ H) as Hp.
  rewrite Hp. reflexivity.
Qed.

(* §E 分子闭式 bv_p（Laurent 系数符号和）与数值锚组                        *)
(*   p_n = −Σ_{j≠n, j≤2n} c_j·(2^{j−n}−1)/(j−n)（锚值 p: 0, 2, 9, 131/3）。*)

Fixpoint bv_negpow (k : nat) : Q :=
  match k with
  | 0 => 1%Q
  | Datatypes.S k' => (- bv_negpow k')%Q
  end.

(* 2 的带符号幂（Z 指数） *)
Definition bv_q2 (k : Z) : Q :=
  match Z.leb 0 k with
  | true => q_pow (2 # 1)%Q (Z.to_nat k)
  | false => 1%Q / q_pow (2 # 1)%Q (Z.to_nat (Z.opp k))
  end.

(* Laurent 系数 c_j = (−1)^{n+j}·Σ_{a≤j, a≤n, j−a≤n} C(n,a)C(n,j−a)2^{n−(j−a)} *)
Definition bv_c (n j : nat) : Q :=
  bv_negpow (n + j) *
  bk_psQ (fun a : nat =>
            if andb (Nat.leb a n) (Nat.leb (j - a) n)
            then ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) *
                  q_pow (2 # 1)%Q (n - (j - a)))%Q
            else 0%Q)
         (Datatypes.S j) 1%Q.

(* bv_p：分子闭式（闭式见 §E；Laurent 系数符号和） *)
Definition bv_p (n : nat) : Q :=
  (- bk_psQ (fun j : nat =>
               if Nat.eqb j n then 0%Q
               else (bv_c n j *
                     ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                      ((Z.of_nat j - Z.of_nat n)%Z # 1))%Q))
            (Datatypes.S (2 * n)) 1%Q)%Q.

(* 真归一近似子 x_n := p_n/q̃_n（定形：无 2 幂） *)
Definition bv_x (n : nat) : Q := bv_p n / (Z.of_nat (bk_Qn_qtilde n) # 1)%Q.

(* bv_x2pow：2 幂归一形 x''_n := p_n/(2^n·q̃_n)，与真归一形不相容（见 bv_x2pow_sep1） *)
Definition bv_x2pow (n : nat) : Q :=
  bv_p n / (q_pow (2 # 1)%Q n * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q.

(* ---- 数值锚组（各锚由 vm_compute 精确判定）---- *)

Theorem bv_q1_anchor : QeqT ((Z.of_nat (bk_Qn_qtilde 1) # 1)%Q) (3 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c11_anchor : QeqT (bv_c 1 1) (3 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c22_anchor : QeqT (bv_c 2 2) (13 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c33_anchor : QeqT (bv_c 3 3) (63 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p0_anchor : QeqT (bv_p 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p1_anchor : QeqT (bv_p 1) (2 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p2_anchor : QeqT (bv_p 2) (9 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p3_anchor : QeqT (bv_p 3) (131 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x0_anchor : QeqT (bv_x 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x1_anchor : QeqT (bv_x 1) (2 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x2_anchor : QeqT (bv_x 2) (9 # 13)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 跨变体核对：bv_p 2 == 9，与原变体关系 r_2 == 2^{3}·p_2 == 72 一致。 *)
Theorem bv_cross2_anchor : QeqT ((bv_p 2 * (Z.of_nat 8 # 1))%Q) (72 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(** bv_x2pow_sep1：分离见证——bv_x2pow 1 == 1/3 < 2/3 == bv_x 1（QltT，Set 层）。 *)
Theorem bv_x2pow_sep1 : QltT (bv_x2pow 1) (bv_x 1).
Proof. vm_compute. reflexivity. Qed.

(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。        *)

Print Assumptions bv_delannoy_eq_qtilde.
Print Assumptions bv_term_pos.
Print Assumptions bv_carrier_eval.
Print Assumptions bv_carrier_value.
Print Assumptions bv_sum_mono.
Print Assumptions bv_sum_pos.
Print Assumptions bv_p3_anchor.
Print Assumptions bv_x2pow_sep1.
(* ================= §4 pi_pow3_ge1 族 ================= *)
From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia Lists.List.

Open Scope nat_scope.

(* §A 幂与正性引理（nat 层）                                            *)

Lemma pi_pow3_ge1 : forall n : nat, 1 <= 3 ^ n.
Proof.
  induction n as [| n IH].
  - cbn [Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma pi_pow4b : forall n : nat, 4 ^ n = 2 ^ n * 2 ^ n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite !Nat.pow_succ_r'. rewrite IH. ring.
Qed.

Lemma pi_pow8 : forall n : nat, 8 ^ n = 4 ^ n * 2 ^ n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite !Nat.pow_succ_r'. rewrite IH. ring.
Qed.

(* bk_psd 常系数闭式：Σ_{k<N} c·2^{N−1−k} = c·(2^N−1) *)
Lemma pi_psd_const : forall (N c : nat),
  bk_psd (fun _ : nat => c) N = c * (2 ^ N - 1).
Proof.
  induction N as [| N IH]; intro c.
  - cbn [bk_psd Nat.pow]. lia.
  - cbn [bk_psd]. rewrite IH. rewrite Nat.pow_succ_r'.
    pose proof (hl_le_t_to_le 1 (2 ^ N) (hl_pow2_ge1 N)). nia.
Qed.

(* §B bkC ↔ hl_binom 双 Pascal 桥：pi_bkC_hl                             *)

Lemma pi_bkC_hl : forall n k : nat, bkC n k = hl_binom n k.
Proof.
  induction n as [| n IH]; intro k.
  - destruct k as [| k'].
    + reflexivity.
    + reflexivity.
  - destruct k as [| k'].
    + reflexivity.
    + cbn [bkC]. rewrite (IH k'). rewrite (IH (Datatypes.S k')).
      symmetry. apply hl_id_eq. exact (hl_binom_S n k').
Qed.

(* §C Q 层乘除微引理（Q 域域律，全部非零前提显式）                        *)

(* 正分母分数乘整数：分母合并不展开 Qinv 分量 *)
Lemma pi_Qden_cancel : forall (u : Z) (p : positive),
  ((u # p) * ((Z.pos p) # 1))%Q == (u # 1)%Q.
Proof.
  intros u p. unfold Qeq. cbn [Qnum Qden Qmult]. rewrite Pos.mul_1_r. ring.
Qed.

Lemma pi_Qneq0_Zpos : forall p : positive, ~ (((Z.pos p) # 1) == 0)%Q.
Proof.
  intros p Hc. unfold Qeq in Hc. vm_compute in Hc. discriminate Hc.
Qed.

Lemma pi_Qneq0_nat : forall m : nat, 1 <= m -> ~ ((Z.of_nat m # 1) == 0)%Q.
Proof.
  intros m Hm Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc. lia.
Qed.

(* pi_Qmul_cancel_r_to：Q 域右消去（由 stdlib Qmult_inv_r） *)
Lemma pi_Qmul_cancel_r_to : forall a b c : Q,
  ~ (c == 0)%Q -> a * c == b * c -> a == b.
Proof.
  intros a b c Hc H.
  assert (Hc1 : (c * (/ c))%Q == 1%Q) by (apply Qmult_inv_r; exact Hc).
  transitivity (((a * c) * (/ c)))%Q.
  - rewrite <- Qmult_assoc, Hc1. symmetry. apply Qmult_1_r.
  - rewrite H. rewrite <- Qmult_assoc, Hc1. apply Qmult_1_r.
Qed.

(* 除法等式单侧引入：y≠0 ⟹ x == b·y ⟹ x/y == b *)
Lemma pi_Qdiv_eq_intro : forall x y b : Q,
  ~ (y == 0)%Q -> x == b * y -> x / y == b.
Proof.
  intros x y b Hy Hxy. unfold Qdiv. rewrite Hxy.
  assert (Hy1 : (y * (/ y))%Q == 1%Q) by (apply Qmult_inv_r; exact Hy).
  rewrite <- Qmult_assoc, Hy1. apply Qmult_1_r.
Qed.

(* pi_Qmul_inv_r_eq：除法交叉等价（Q 域域律） *)
Lemma pi_Qmul_inv_r_eq : forall x y z : Q,
  ~ (y == 0)%Q -> ((x * (/ y)) == z <-> x == z * y).
Proof.
  intros x y z Hy. split; intro H.
  - assert (Hy1 : (y * (/ y))%Q == 1%Q) by (apply Qmult_inv_r; exact Hy).
    transitivity (((x * (/ y)) * y))%Q.
    + rewrite <- Qmult_assoc. rewrite (Qmult_comm (/ y) y). rewrite Hy1.
      symmetry. apply Qmult_1_r.
    + rewrite H. reflexivity.
  - assert (Hy1 : (y * (/ y))%Q == 1%Q) by (apply Qmult_inv_r; exact Hy).
    rewrite H. rewrite <- Qmult_assoc, Hy1. apply Qmult_1_r.
Qed.

(* §D 整除换商与 H_k 整化主桥：pi_div_Qeq、pi_hsum_spec                   *)

(* pi_div_Qeq：j ∣ D ⟹ Q#D·(1/Q#j) == Q#(D/j)（由 Nat.div_mul） *)
Lemma pi_div_Qeq : forall (D j : nat), 1 <= j -> Nat.divide j D ->
  ((Z.of_nat D # 1) * ((1 # 1) / (Z.of_nat j # 1)))%Q
  == (Z.of_nat (D / j) # 1)%Q.
Proof.
  intros D j Hj Hd. destruct Hd as [c Hc].
  assert (Hj0 : ~ ((Z.of_nat j # 1) == 0)%Q) by (apply pi_Qneq0_nat; exact Hj).
  assert (Hdq : D / j = c).
  { rewrite Hc. apply Nat.div_mul. lia. }
  rewrite Hdq. unfold Qdiv.
  transitivity ((((Z.of_nat D # 1) * (1 # 1)) * (/ (Z.of_nat j # 1))))%Q.
  - ring.
  - apply (proj2 (pi_Qmul_inv_r_eq _ _ _ Hj0)).
    rewrite Qmult_1_r.
    rewrite Hc.
    rewrite (qeqT_imp_qeq _ _ (bk_Qmul_nat c j)).
    reflexivity.
Qed.

(* 整化和承载：pi_hsum D k = Σ_{j=1}^{k} D/j（D 固定，变指标求商和） *)
Fixpoint pi_hsum (D k : nat) : nat :=
  match k with
  | 0 => 0
  | Datatypes.S m => pi_hsum D m + D / Datatypes.S m
  end.

(* pi_hsum_spec：D_n·H_k == Q#(Σ_{j≤k} D_n/j)；对 k 归纳，逐项由 hl_lcm_divide_all 与 pi_div_Qeq。 *)
Lemma pi_hsum_spec : forall (n k : nat), k <= n ->
  ((Z.of_nat (hl_lcm_upto n) # 1) * bk_H k)%Q
  == (Z.of_nat (pi_hsum (hl_lcm_upto n) k) # 1)%Q.
Proof.
  intros n k. induction k as [| k IH]; intro Hk.
  - cbn [bk_H pi_hsum]. ring.
  - assert (Hle : k <= n) by lia.
    specialize (IH Hle).
    cbn [bk_H pi_hsum].
    rewrite Qmult_plus_distr_r.
    rewrite IH.
    assert (H1 : 1 <= Datatypes.S k) by lia.
    assert (Hd := hl_lcm_divide_all n (Datatypes.S k) H1 Hk).
    assert (Hdv := pi_div_Qeq (hl_lcm_upto n) (Datatypes.S k) H1 Hd).
    rewrite Hdv.
    exact (qeqT_imp_qeq _ _
            (bk_Qadd_nat (pi_hsum (hl_lcm_upto n) k)
                         (hl_lcm_upto n / Datatypes.S k))).
Qed.

(* §E bk_psQ 逐点外延与常数提出：pi_psQ_ext、pi_psQ_mul                   *)

Lemma pi_psQ_ext : forall (N : nat) (f g : nat -> Q) (z : Q),
  (forall k : nat, k < N -> f k == g k) -> bk_psQ f N z == bk_psQ g N z.
Proof.
  induction N as [| N IH]; intros f g z H.
  - reflexivity.
  - cbn [bk_psQ].
    rewrite (IH f g z) by (intros k Hk; apply H; lia).
    rewrite (H N) by lia.
    reflexivity.
Qed.

Lemma pi_psQ_mul : forall (N : nat) (c : Q) (f : nat -> Q) (z : Q),
  bk_psQ (fun k => (c * f k)%Q) N z == (c * bk_psQ f N z)%Q.
Proof.
  induction N as [| N IH]; intros c f z.
  - cbn [bk_psQ]. ring.
  - cbn [bk_psQ]. rewrite IH. ring.
Qed.

(* §F p̃_n 整化主件：pi_Pn_int（系数取 C²·D_n，见头部防错注记①）          *)

(* 系数整化（逐点）：(Z#(C²·D_n))·H_k == Z#(C²·S_k)，S_k := pi_hsum D_n k *)
Lemma pi_coeff_Zeq : forall (n k : nat), k <= n ->
  ((Z.of_nat (bkC n k * bkC n k * hl_lcm_upto n) # 1) * bk_H k)%Q
  == (Z.of_nat (bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k) # 1)%Q.
Proof.
  intros n k Hk.
  rewrite <- (qeqT_imp_qeq _ _
               (bk_Qmul_nat (bkC n k * bkC n k) (hl_lcm_upto n))).
  transitivity ((Z.of_nat (bkC n k * bkC n k) # 1)
                  * ((Z.of_nat (hl_lcm_upto n) # 1) * bk_H k))%Q.
  - ring.
  - rewrite (pi_hsum_spec n k Hk).
    exact (qeqT_imp_qeq _ _
            (bk_Qmul_nat (bkC n k * bkC n k)
                         (pi_hsum (hl_lcm_upto n) k))).
Qed.

(* pi_ptilde：p̃_n := Σ_{k≤n} C(n,k)²·S_k，S_k := pi_hsum D_n k *)
Definition pi_ptilde (n : nat) : nat :=
  bk_psd (fun k => bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k)
         (Datatypes.S n).

(* pi_Pn_eval_eq：bk_Pn_eval 的 Qeq 形（经 S02 qeqT_imp_qeq 转换，供 == 目标改写） *)
Lemma pi_Pn_eval_eq : forall (n : nat) (z : Q),
  bkQ (bk_Pn_list n) z
  == bk_psQ (fun k : nat => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
          (Datatypes.S n) z.
Proof.
  intros n z.
  apply qeqT_imp_qeq.
  apply bk_Pn_eval.
Qed.

(* 半整数点闭式：D_n·2^n·P_n(1/2) == Q#p̃_n（p̃_n ∈ nat 承载） *)
Lemma pi_Pn_half : forall n : nat,
  ((Z.of_nat (hl_lcm_upto n) # 1)
     * (q_pow (2 # 1)%Q n * bkQ (bk_Pn_list n) (1 # 2)%Q))%Q
  == (Z.of_nat (pi_ptilde n) # 1)%Q.
Proof.
  intro n. unfold pi_ptilde.
  rewrite (pi_Pn_eval_eq n (1 # 2)%Q).
  assert (Hmul := pi_psQ_mul (Datatypes.S n)
                    (Z.of_nat (hl_lcm_upto n) # 1)%Q
                    (fun k : nat => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
                    (1 # 2)%Q).
  transitivity ((q_pow (2 # 1)%Q n
    * ((Z.of_nat (hl_lcm_upto n) # 1)
         * bk_psQ (fun k : nat => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
               (Datatypes.S n) (1 # 2)%Q))%Q).
  - ring.
  - rewrite <- Hmul.
    assert (Hpt : forall k : nat, k < Datatypes.S n ->
        (((Z.of_nat (hl_lcm_upto n) # 1)
            * ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k))%Q)
        == ((Z.of_nat (bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k) # 1))%Q).
    { intro k. intro Hk. assert (Hle : k <= n) by lia.
      transitivity ((Z.of_nat (bkC n k * bkC n k) # 1)
                      * ((Z.of_nat (hl_lcm_upto n) # 1) * bk_H k))%Q.
      - ring.
      - rewrite (pi_hsum_spec n k Hle).
        exact (qeqT_imp_qeq _ _
                (bk_Qmul_nat (bkC n k * bkC n k)
                             (pi_hsum (hl_lcm_upto n) k))). }
    rewrite (pi_psQ_ext (Datatypes.S n) _ _ _ Hpt).
    exact (qeqT_imp_qeq _ _
            (bk_half_psd n
               (fun k : nat => bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k))).
Qed.

(* pi_Pn_int：p̃_n ∈ Z 的 sigT 整性见证（Set 面） *)

Theorem pi_Pn_int : forall n : nat,
  sigT (fun z : Z =>
    QeqT (q_pow (2 # 1)%Q n
            * ((Z.of_nat (hl_lcm_upto n) # 1) * bkQ (bk_Pn_list n) (1 # 2)%Q)%Q)
         ((z # 1)%Q)).
Proof.
  intro n. exists (Z.of_nat (pi_ptilde n)). apply qeq_imp_qeqT.
  transitivity ((Z.of_nat (hl_lcm_upto n) # 1)
                  * (q_pow (2 # 1)%Q n * bkQ (bk_Pn_list n) (1 # 2)%Q))%Q.
  - ring.
  - apply pi_Pn_half.
Qed.

(* §G q̃_n ≤ (n+1)·8^n：pi_Qn_le_8pow（QleT' Set 面）                     *)

Theorem pi_Qn_le_8pow : forall n : nat,
  QleT' ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q)
        ((Z.of_nat (Datatypes.S n * 8 ^ n) # 1)%Q).
Proof.
  intro n. apply bk_Qle_nat. apply NatLe_lift.
  unfold bk_Qn_qtilde.
  assert (Hpt : forall k : nat, k < Datatypes.S n ->
      bkC n k * bkC n k <= 4 ^ n).
  { intro k. intro Hk.
    pose proof (hl_le_t_to_le (hl_binom n k) (2 ^ n)
                  (hl_binom_le_pow2 n k)) as Hb.
    rewrite <- (pi_bkC_hl n k) in Hb.
    rewrite (pi_pow4b n).
    nia. }
  pose proof (bk_psd_mono (Datatypes.S n)
               (fun k => bkC n k * bkC n k)
               (fun _ : nat => 4 ^ n)
               (fun k Hk => NatLe_lift _ _ (Hpt k (NatLe_drop _ _ Hk)))) as Hmono.
  rewrite pi_psd_const in Hmono.
  rewrite Nat.pow_succ_r' in Hmono.
  destruct n as [| n'].
  - cbn [bk_psd bkC Nat.pow] in *. lia.
  - assert (Hs1 : 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n' - 1)
                  <= 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n'))
      by (apply Nat.mul_le_mono_l; lia).
    assert (Hs2 : 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n')
                  = 2 * (4 ^ Datatypes.S n' * 2 ^ Datatypes.S n')) by ring.
    assert (Hs3 : 2 * (4 ^ Datatypes.S n' * 2 ^ Datatypes.S n')
                  <= Datatypes.S (Datatypes.S n') * (4 ^ Datatypes.S n' * 2 ^ Datatypes.S n')).
    { apply Nat.mul_le_mono_r. lia. }
    rewrite (pi_pow8 (Datatypes.S n')).
    apply Nat.le_trans with
      (m := 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n' - 1)).
    + pose proof (NatLe_drop _ _ Hmono) as HmonoL. exact HmonoL.
    + apply Nat.le_trans with
        (m := 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n')).
      * exact Hs1.
      * rewrite Hs2. exact Hs3.
Qed.

(* §H x'_n 的显式分母：pi_x_n_frac 与 sigT 弱面 pi_den_divide             *)

Lemma pi_lcm_pos : forall a b : nat, 1 <= a -> 1 <= b -> 1 <= Nat.lcm a b.
Proof.
  intros a b Ha Hb. unfold Nat.lcm.
  destruct (Nat.gcd a b) as [| g] eqn:Eg.
  - exfalso.
    destruct (Nat.gcd_divide_r a b) as [q Hq].
    rewrite Eg, Nat.mul_0_r in Hq. lia.
  - assert (Hbg : 0 < b / Datatypes.S g).
    { apply Nat.div_str_pos.
      destruct (Nat.gcd_divide_r a b) as [q Hq]. rewrite Eg in Hq.
      destruct q as [| q'].
      - lia.
      - split.
        + lia.
        + assert (Hg1 : Datatypes.S g * 1 <= Datatypes.S g * Datatypes.S q')
            by (apply Nat.mul_le_mono_l; lia).
          rewrite Nat.mul_1_r in Hg1.
          rewrite Hq, Nat.mul_comm. exact Hg1. }
    nia.
Qed.

Lemma pi_lcm_upto_pos : forall n : nat, 1 <= hl_lcm_upto n.
Proof.
  induction n as [| n IH].
  - cbn [hl_lcm_upto]. lia.
  - cbn [hl_lcm_upto]. apply pi_lcm_pos.
    + exact IH.
    + lia.
Qed.

Lemma pi_qtilde_pos : forall n : nat, 1 <= bk_Qn_qtilde n.
Proof.
  intro n. pose proof (NatLe_drop _ _ (bk_Qn_ge_3pow_nat n)).
    pose proof (pi_pow3_ge1 n). lia.
Qed.

(* pi_Qn_nz：2·Q_n(1/2) 非零（由 bk_Qn_half_closed 与 q̃_n ≥ 3^n > 0） *)
Lemma pi_Qn_nz : forall n : nat,
  ~ (((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q) == 0)%Q.
Proof.
  intro n. intro H0.
  assert (HQ : bkQ (bk_Qn_list n) (1 # 2)%Q == 0%Q).
  { apply (pi_Qmul_cancel_r_to (bkQ (bk_Qn_list n) (1 # 2)%Q) 0%Q (2 # 1)%Q).
    - apply pi_Qneq0_Zpos.
    - rewrite (Qmult_comm (bkQ (bk_Qn_list n) (1 # 2)%Q) (2 # 1)%Q).
      rewrite Qmult_0_l. exact H0. }
  assert (Hh := qeqT_imp_qeq _ _ (bk_Qn_half_closed n)).
  rewrite HQ in Hh. rewrite Qmult_0_r in Hh.
  pose proof (NatLe_drop _ _ (bk_Qn_ge_3pow_nat n)).
  unfold Qeq in Hh. cbn [Qnum Qden] in Hh.
  rewrite !Z.mul_1_r in Hh.
  replace 0%Z with (Z.of_nat 0) in Hh by reflexivity.
  apply Znat.Nat2Z.inj in Hh.
  pose proof (pi_pow3_ge1 n).
  lia.
Qed.

(* 交叉恒等式：P_n(1/2)·(2·D_n·q̃_n) == p̃_n·(2·Q_n(1/2))（Q 域纯环） *)
Lemma pi_x_cross : forall n : nat,
  (bkQ (bk_Pn_list n) (1 # 2)%Q
     * (Z.of_nat (2 * hl_lcm_upto n * bk_Qn_qtilde n) # 1))%Q
  == ((Z.of_nat (pi_ptilde n) # 1)
        * ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q.
Proof.
  intro n.
  replace (2 # 1)%Q with ((Z.of_nat 2 # 1)%Q) by reflexivity.
  rewrite <- (qeqT_imp_qeq _ _
               (bk_Qmul_nat (2 * hl_lcm_upto n) (bk_Qn_qtilde n))).
  rewrite <- (qeqT_imp_qeq _ _ (bk_Qmul_nat 2 (hl_lcm_upto n))).
  rewrite <- (qeqT_imp_qeq _ _ (bk_Qn_half_closed n)).
  rewrite <- (pi_Pn_half n).
  ring.
Qed.

(* pi_x_n_frac：x'_n == p̃_n /(2·D_n·q̃_n)，分母显式构造。
   防错注记：Z.pos (Pos.of_nat M) 数值为 M+1（无零偏移），用它陈述为假命题；
   Pos.of_succ_nat (Nat.pred M) 数值恰为 M（定义性换算）。 *)
Theorem pi_x_n_frac : forall n : nat,
  QeqT (bkQ (bk_Pn_list n) (1 # 2)%Q
          / ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q
       ((Z.of_nat (pi_ptilde n)
           # Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))%Q).
Proof.
  intro n. apply qeq_imp_qeqT.
  assert (Hm1 : 1 <= 2 * hl_lcm_upto n * bk_Qn_qtilde n)
    by (pose proof (pi_lcm_upto_pos n); pose proof (pi_qtilde_pos n); lia).
  assert (Hpm : Z.pos (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))
              = Z.of_nat (2 * hl_lcm_upto n * bk_Qn_qtilde n)).
  { assert (Hs : Datatypes.S (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n))
               = 2 * hl_lcm_upto n * bk_Qn_qtilde n) by lia.
    transitivity (Z.of_nat (Datatypes.S (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))).
    - reflexivity.
    - rewrite Hs. reflexivity. }
  apply pi_Qdiv_eq_intro.
  - apply pi_Qn_nz.
  - apply (pi_Qmul_cancel_r_to (bkQ (bk_Pn_list n) (1 # 2)%Q)
             (((Z.of_nat (pi_ptilde n)
                  # Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))
                 * ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q)
             ((Z.pos (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n))) # 1)%Q)).
    + apply pi_Qneq0_Zpos.
    + rewrite Hpm.
      transitivity ((Z.of_nat (pi_ptilde n) # 1)
                      * ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q.
      * exact (pi_x_cross n).
      * rewrite <- (pi_Qden_cancel (Z.of_nat (pi_ptilde n))
                          (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))).
        rewrite Hpm.
        ring.
Qed.

(* pi_den_divide：存在正分母 p 使 x'_n == p̃_n/p（sigT 弱面） *)
Theorem pi_den_divide : forall n : nat,
  sigT (fun p : positive =>
    QeqT (bkQ (bk_Pn_list n) (1 # 2)%Q
            / ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q
         ((Z.of_nat (pi_ptilde n) # p)%Q)).
Proof.
  intro n.
  exists (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n))).
  apply pi_x_n_frac.
Qed.

(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。         *)

Print Assumptions pi_bkC_hl.
Print Assumptions pi_div_Qeq.
Print Assumptions pi_hsum_spec.
Print Assumptions pi_psQ_ext.
Print Assumptions pi_Pn_int.
Print Assumptions pi_Qn_le_8pow.
Print Assumptions pi_x_n_frac.
Print Assumptions pi_den_divide.
(* ================= §5 bkC 族 ================= *)
From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.

(* QArith 泄漏 Q_scope（裸数字被判读为 Q 构造元），压回 nat 优先 *)
Open Scope nat_scope.

(* §A nat 层二项式系数（Pascal 递归）与对称引理                          *)

(* Pascal 递归二项式系数 C(n,k)（名字 bkC 避免与 C 遮蔽冲突） *)
Fixpoint bkC (n k : nat) : nat :=
  match n with
  | 0 => match k with
         | 0 => 1
         | Datatypes.S _ => 0
         end
  | Datatypes.S n' =>
      match k with
      | 0 => 1
      | Datatypes.S k' => bkC n' k' + bkC n' (Datatypes.S k')
      end
  end.

(* 出界件：k > n 时 C(n,k) = 0 *)
Lemma bkC_out : forall n k : nat, n < k -> bkC n k = 0.
Proof.
  induction n as [| n IH]; intros k Hk.
  - destruct k as [| k'].
    + lia.
    + reflexivity.
  - destruct k as [| k'].
    + lia.
    + cbn [bkC].
      rewrite (IH k') by lia.
      rewrite (IH (Datatypes.S k')) by lia.
      reflexivity.
Qed.

(* 对角件：C(n,n) = 1 *)
Lemma bkC_diag : forall n : nat, bkC n n = 1.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [bkC].
    rewrite IH.
    rewrite (bkC_out n (Datatypes.S n)) by lia.
    reflexivity.
Qed.

(* 正性件：k ≤ n 时 C(n,k) ≥ 1 *)
Lemma bkC_pos : forall n k : nat, k <= n -> 1 <= bkC n k.
Proof.
  induction n as [| n IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. cbn [bkC]. lia.
  - destruct k as [| k'].
    + cbn [bkC]. lia.
    + cbn [bkC].
      destruct (le_lt_dec (Datatypes.S k') n) as [Hle | Hlt].
      * assert (H1 : 1 <= bkC n k') by (apply IH; lia).
        assert (H2 : 1 <= bkC n (Datatypes.S k')) by (apply IH; lia).
        lia.
      * assert (Hk' : k' = n) by lia. subst k'.
        rewrite (bkC_out n (Datatypes.S n)) by lia.
        assert (H1 : 1 <= bkC n n) by (apply IH; lia).
        lia.
Qed.

(* 逐点 Pascal 恒等：shift(C n)(k) + C(n,k) = C(S n,k)（k 分支全定义性） *)
Lemma bkC_pascal_shift : forall n k : nat,
  (match k with
   | 0 => 0
   | Datatypes.S j => bkC n j
   end) + bkC n k = bkC (Datatypes.S n) k.
Proof.
  intros n k. destruct k as [| j].
  - destruct n as [| n']; reflexivity.
  - cbn [bkC]. reflexivity.
Qed.

(* 对称引理：C(n,k) = C(n,n−k)（后续恒等式归纳用——P2 接口件） *)
Lemma bk_Qn_sym : forall n k : nat, k <= n -> bkC n k = bkC n (n - k).
Proof.
  induction n as [| n IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. reflexivity.
  - destruct k as [| k'].
    + replace (Datatypes.S n - 0) with (Datatypes.S n) by lia.
      rewrite (bkC_diag (Datatypes.S n)). reflexivity.
    + replace (Datatypes.S n - Datatypes.S k') with (n - k') by lia.
      destruct (le_lt_dec (Datatypes.S k') n) as [Hle | Hlt].
      * assert (H1 : bkC n k' = bkC n (n - k')) by (apply IH; lia).
        assert (H2 : bkC n (Datatypes.S k') = bkC n (n - Datatypes.S k'))
          by (apply IH; lia).
        assert (Hn1 : n - k' = Datatypes.S (n - Datatypes.S k')) by lia.
        rewrite Hn1 in H1.
        rewrite Hn1.
        cbn [bkC]. lia.
      * assert (Hk' : k' = n) by lia. subst k'.
        replace (n - n) with 0 by lia.
        rewrite (bkC_diag (Datatypes.S n)).
        reflexivity.
Qed.

(* §B nat 层降幂加权和 bk_psd 与二项定理 (1+2)^n                        *)
(*   bk_psd f n = Σ_{k<n} f(k)·2^{n−1−k}，递归 bk_psd f (S m) =        *)
(*   2·bk_psd f m + f m（降幂步进恰为翻倍）。                           *)

Fixpoint bk_psd (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => 0
  | Datatypes.S m => 2 * bk_psd f m + f m
  end.

Lemma bk_psd_ext : forall (N : nat) (f g : nat -> nat),
  (forall k : nat, k < N -> f k = g k) -> bk_psd f N = bk_psd g N.
Proof.
  induction N as [| N IH]; intros f g H.
  - reflexivity.
  - cbn [bk_psd].
    rewrite (IH f g) by (intro k; intro Hk; apply H; lia).
    rewrite (H N) by lia.
    reflexivity.
Qed.

Lemma bk_psd_add : forall (N : nat) (f g : nat -> nat),
  bk_psd (fun k => f k + g k) N = bk_psd f N + bk_psd g N.
Proof.
  induction N as [| N IH]; intros f g.
  - reflexivity.
  - cbn [bk_psd]. rewrite IH. lia.
Qed.

(* 移位件：系数行整体右移一位（头部垫零） ⟹ 和恰为原和降一档 *)
Lemma bk_psd_shift : forall (m : nat) (g : nat -> nat),
  bk_psd (fun k => match k with
                   | 0 => 0
                   | Datatypes.S j => g j
                   end) (Datatypes.S m) = bk_psd g m.
Proof.
  induction m as [| m IH]; intros g.
  - reflexivity.
  - assert (Hunf : bk_psd (fun k => match k with
                                    | 0 => 0
                                    | Datatypes.S j => g j
                                    end) (Datatypes.S (Datatypes.S m))
                 = 2 * bk_psd (fun k => match k with
                                        | 0 => 0
                                        | Datatypes.S j => g j
                                        end) (Datatypes.S m)
                   + g m)
      by reflexivity.
    rewrite Hunf, IH. reflexivity.
Qed.

(* 二项定理降幂形：Σ_{k≤n} C(n,k)·2^{n−k} = (1+2)^n = 3^n
   （stdlib 无二项定理，自建——库存勘定见头注） *)
Lemma bk_psd_binom : forall n : nat,
  bk_psd (fun k => bkC n k) (Datatypes.S n) = 3 ^ n.
Proof.
  induction n as [| n IH].
  - cbn [bk_psd]. replace (2 * 0)%nat with 0%nat by lia. reflexivity.
  - replace (bk_psd (fun k => bkC (Datatypes.S n) k) (Datatypes.S (Datatypes.S n)))
      with (bk_psd (fun k => (match k with
                             | 0 => 0
                             | Datatypes.S j => bkC n j
                             end) + bkC n k) (Datatypes.S (Datatypes.S n)))
      by (apply bk_psd_ext; intro k; intro Hk; apply bkC_pascal_shift).
    rewrite bk_psd_add.
    assert (IH' : bk_psd (bkC n) (Datatypes.S n) = 3 ^ n) by exact IH.
    assert (Hsh : bk_psd (fun k => match k with
                                   | 0 => 0
                                   | Datatypes.S j => bkC n j
                                   end) (Datatypes.S (Datatypes.S n))
                = bk_psd (bkC n) (Datatypes.S n))
      by (apply (bk_psd_shift (Datatypes.S n) (bkC n))).
    assert (Hunf : bk_psd (bkC n) (Datatypes.S (Datatypes.S n))
                 = 2 * bk_psd (bkC n) (Datatypes.S n)
                   + bkC n (Datatypes.S n))
      by reflexivity.
    rewrite Hsh, Hunf, IH'.
    rewrite (bkC_out n (Datatypes.S n)) by lia.
    rewrite Nat.pow_succ_r'.
    lia.
Qed.

(* 单调件：逐点 ≤ ⟹ 和 ≤ *)
Lemma bk_psd_mono : forall (N : nat) (f h : nat -> nat),
  (forall k : nat, k < N -> f k <= h k) -> bk_psd f N <= bk_psd h N.
Proof.
  induction N as [| N IH]; intros f h H.
  - reflexivity.
  - cbn [bk_psd].
    assert (H1 : bk_psd f N <= bk_psd h N)
      by (apply IH; intro k; intro Hk; apply H; lia).
    assert (H2 : f N <= h N) by (apply H; lia).
    lia.
Qed.

(* §C nat 层 q̃_n 与 3^n 下界（nat 脚手架面）                            *)

(* q̃_n := Σ_{k≤n} C(n,k)²·2^{n−k}（= 2^n·Q_n(1/2) 的 nat 承载） *)
Definition bk_Qn_qtilde (n : nat) : nat :=
  bk_psd (fun k => bkC n k * bkC n k) (Datatypes.S n).

Lemma bk_Qn_ge_3pow_nat : forall n : nat, 3 ^ n <= bk_Qn_qtilde n.
Proof.
  intro n.
  unfold bk_Qn_qtilde.
  assert (Hpt : forall k : nat, k < Datatypes.S n -> bkC n k <= bkC n k * bkC n k).
  { intro k. intro Hk.
    assert (Hk' : k <= n) by lia.
    assert (Hpos : NatLe 1 (bkC n k)) by (apply BeukersLists.bkC_pos; apply NatLe_lift; exact Hk').
    pose proof (NatLe_drop _ _ Hpos) as HposP.
    assert (H1 : bkC n k * 1 <= bkC n k * bkC n k)
      by (apply Nat.mul_le_mono_l; exact HposP).
    rewrite Nat.mul_1_r in H1. exact H1. }
  assert (Hmono := bk_psd_mono (Datatypes.S n)
                     (fun k => bkC n k)
                     (fun k => bkC n k * bkC n k) Hpt).
  rewrite <- (bk_psd_binom n).
  exact Hmono.
Qed.

(* nat→Q 桥：Qle 的 nat 像 *)
Lemma bk_Qle_nat : forall a b : nat, (a <= b)%nat -> Qle (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b H.
  unfold Qle. cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  apply Nat2Z.inj_le.
  exact H.
Qed.

(* §D Q 层：Q_n 系数列表、求值面与整性见证                               *)

(* Horner 折叠求值（头为常数项） *)
Fixpoint bkQ (p : list Q) (z : Q) : Q :=
  match p with
  | nil => 0%Q
  | c :: p' => c + z * bkQ p' z
  end.

(* 索引列表核：bk_idx N = [0;1;...;N−1]（列表 Fixpoint 承载字母） *)
Fixpoint bk_idx (N : nat) : list nat :=
  match N with
  | 0 => nil
  | Datatypes.S m => bk_idx m ++ (m :: nil)
  end.

Lemma bk_idx_seq : forall N : nat, bk_idx N = seq 0 N.
Proof.
  induction N as [| N IH].
  - reflexivity.
  - cbn [bk_idx]. rewrite IH.
    rewrite (seq_S N 0). reflexivity.
Qed.

(* Q_n 系数列表：第 k 项 = C(n,k)²（bkC 平方的 Q 像），k = 0..n *)
Definition bk_Qn_list (n : nat) : list Q :=
  map (fun k => (Z.of_nat (bkC n k * bkC n k) # 1)%Q) (bk_idx (Datatypes.S n)).

(* 求值函数（列表折叠面） *)
Definition bk_Qn_eval (n : nat) (z : Q) : Q := bkQ (bk_Qn_list n) z.

(* Q 层指标和核：bk_psQ f N z = Σ_{k<N} f(k)·z^k *)
Fixpoint bk_psQ (f : nat -> Q) (N : nat) (z : Q) : Q :=
  match N with
  | 0 => 0%Q
  | Datatypes.S m => bk_psQ f m z + f m * q_pow z m
  end.

Lemma bkQ_app : forall (p q : list Q) (z : Q),
  bkQ (p ++ q) z == bkQ p z + q_pow z (length p) * bkQ q z.
Proof.
  induction p as [| a p' IH]; intros q z.
  - cbn [app length bkQ q_pow]. ring.
  - cbn [app length bkQ].
    rewrite IH.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ z (length p'))).
    ring.
Qed.

(* 列表↔指标和：bkQ (map f (seq 0 (S N))) z == Σ_{k<S N} f(k)·z^k *)
Lemma bkQ_seq_map : forall (N : nat) (f : nat -> Q) (z : Q),
  bkQ (map f (seq 0 (Datatypes.S N))) z == bk_psQ f (Datatypes.S N) z.
Proof.
  induction N as [| N IH]; intros f z.
  - cbn [seq map bkQ bk_psQ q_pow]. ring.
  - replace (seq 0 (Datatypes.S (Datatypes.S N)))
      with (seq 0 (Datatypes.S N) ++ (Datatypes.S N :: nil))
      by (rewrite (seq_S (Datatypes.S N) 0); reflexivity).
    rewrite map_app.
    rewrite bkQ_app.
    rewrite map_length, seq_length.
    cbn [map bkQ].
    rewrite IH.
    assert (Hunf : bk_psQ f (Datatypes.S (Datatypes.S N)) z
                 = (bk_psQ f (Datatypes.S N) z
                    + f (Datatypes.S N) * q_pow z (Datatypes.S N))%Q)
      by reflexivity.
    rewrite Hunf.
    ring.
Qed.

(* 逐项像：k 越界排除下 map+seq 的第 k 项 == f k *)
Lemma bk_nth_map_lt : forall (f : nat -> Q) (l : list nat) (k : nat) (d : Q),
  k < length l -> nth k (map f l) d == f (nth k l 0).
Proof.
  intros f l. induction l as [| a l' IH]; intros k d Hk.
  - exfalso. cbn [length] in Hk. lia.
  - destruct k as [| k'].
    + cbn [map nth]. apply Qeq_refl.
    + cbn [map nth]. apply IH. cbn [length] in Hk. lia.
Qed.

Lemma bk_nth_map_seq : forall (f : nat -> Q) (N k : nat) (d : Q),
  k < Datatypes.S N -> nth k (map f (seq 0 (Datatypes.S N))) d == f k.
Proof.
  intros f N k d Hk.
  replace (f k) with (f (nth k (seq 0 (Datatypes.S N)) 0)).
  - apply (bk_nth_map_lt f (seq 0 (Datatypes.S N)) k d).
    rewrite seq_length. lia.
  - apply f_equal. rewrite seq_nth by lia. reflexivity.
Qed.

(* 系数逐项刻画：第 k 项 == C(n,k)² 的 Q 像 *)
Lemma bk_Qn_list_nth : forall n k : nat, k <= n ->
  nth k (bk_Qn_list n) 0%Q == (Z.of_nat (bkC n k * bkC n k) # 1)%Q.
Proof.
  intros n k Hk.
  unfold bk_Qn_list. rewrite bk_idx_seq.
  apply bk_nth_map_seq. lia.
Qed.

(* §D2 换基核心与整性见证（本件非平凡主件）                              *)

Lemma bk_q_pow_mul : forall (x y : Q) (k : nat),
  q_pow (x * y) k == q_pow x k * q_pow y k.
Proof.
  intros x y k. induction k as [| k IH].
  - cbn [q_pow]. ring.
  - cbn [q_pow]. rewrite IH. ring.
Qed.

Lemma bk_q_pow_one : forall k : nat, q_pow 1%Q k == 1%Q.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. reflexivity.
Qed.

Lemma bk_Qmul_nat : forall a b : nat,
  ((Z.of_nat a # 1) * (Z.of_nat b # 1))%Q == (Z.of_nat (a * b) # 1)%Q.
Proof.
  intros a b. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
  rewrite !Z.mul_1_r, !Nat2Z.inj_mul. reflexivity.
Qed.

Lemma bk_Qadd_nat : forall a b : nat,
  ((Z.of_nat a # 1) + (Z.of_nat b # 1))%Q == (Z.of_nat (a + b) # 1)%Q.
Proof.
  intros a b. unfold Qeq. cbn [Qnum Qden Qplus Pos.mul].
  rewrite !Z.mul_1_r, !Nat2Z.inj_add. reflexivity.
Qed.

(* 换基核心（非平凡主件）：2^n·Σ_{k<S n} Q#f(k)·(1/2)^k == Q#Σ_{k<S n} f(k)2^{n−k}
   ——降幂 nat 和 bk_psd 承载，纯点算归纳，免对称重排 *)
Lemma bk_half_psd : forall (n : nat) (g : nat -> nat),
  q_pow (2 # 1)%Q n
    * bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q) (Datatypes.S n) (1 # 2)%Q
  == (Z.of_nat (bk_psd g (Datatypes.S n)) # 1)%Q.
Proof.
  intros n g. induction n as [| n IH].
  - cbn [q_pow bk_psQ bk_psd].
    replace (2 * 0)%nat with 0%nat by lia.
    cbn [Nat.add]. ring.
  - assert (Hhalf : (2 # 1)%Q * (1 # 2)%Q == 1%Q)
      by (compute; reflexivity).
    assert (Hunf : bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                     (Datatypes.S (Datatypes.S n)) (1 # 2)%Q
                 = (bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                     (Datatypes.S n) (1 # 2)%Q
                   + ((Z.of_nat (g (Datatypes.S n)) # 1)
                        * q_pow (1 # 2)%Q (Datatypes.S n))%Q)%Q)
      by reflexivity.
    rewrite Hunf.
    rewrite Qmult_plus_distr_r.
    assert (EA : q_pow (2 # 1)%Q (Datatypes.S n)
                   * bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                       (Datatypes.S n) (1 # 2)%Q
                 == (Z.of_nat (2 * bk_psd g (Datatypes.S n)) # 1)%Q).
    { rewrite (qeqT_imp_qeq _ _ (q_pow_succ (2 # 1)%Q n)).
      rewrite <- (Qmult_assoc (2 # 1)%Q (q_pow (2 # 1)%Q n)
                    (bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                        (Datatypes.S n) (1 # 2)%Q)).
      rewrite IH.
      replace (2 # 1)%Q with (Z.of_nat 2 # 1)%Q by reflexivity.
      apply bk_Qmul_nat. }
    assert (EB : q_pow (2 # 1)%Q (Datatypes.S n)
                   * ((Z.of_nat (g (Datatypes.S n)) # 1)
                        * q_pow (1 # 2)%Q (Datatypes.S n))
                 == (Z.of_nat (g (Datatypes.S n)) # 1) * 1%Q).
    { transitivity ((Z.of_nat (g (Datatypes.S n)) # 1)
                      * (q_pow (2 # 1)%Q (Datatypes.S n)
                           * q_pow (1 # 2)%Q (Datatypes.S n)))%Q.
      - ring.
      - rewrite <- (bk_q_pow_mul (2 # 1)%Q (1 # 2)%Q (Datatypes.S n)).
        rewrite Hhalf. rewrite bk_q_pow_one. reflexivity. }
    rewrite EA, EB, Qmult_1_r.
    apply bk_Qadd_nat.
Qed.

(* 半整数点闭式：bkQ (bk_Qn_list n) (1/2) 的 2^n 升格 == Q#q̃_n *)
Lemma bk_Qn_half_closed : forall n : nat,
  q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2)%Q
  == (Z.of_nat (bk_Qn_qtilde n) # 1)%Q.
Proof.
  intro n.
  unfold bk_Qn_list.
  rewrite bk_idx_seq.
  rewrite bkQ_seq_map.
  apply bk_half_psd.
Qed.

(* 主件②：整性见证 q̃_n = 2^n·Q_n(1/2) ∈ Z（sigT + QeqT，Set 面） *)
Theorem bk_Qn_int : forall n : nat,
  sigT (fun z : Z =>
    QeqT ((q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q) ((z # 1)%Q)).
Proof.
  intro n.
  exists (Z.of_nat (bk_Qn_qtilde n)).
  apply qeq_imp_qeqT.
  apply bk_Qn_half_closed.
Qed.

(* 主件③：q̃_n ≥ 3^n（QleT' Set 面） *)
Theorem bk_Qn_ge_3pow : forall n : nat,
  QleT' ((Z.of_nat (3 ^ n) # 1)%Q) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n.
  apply Qle_to_QleT'.
  apply bk_Qle_nat.
  apply bk_Qn_ge_3pow_nat.
Qed.

(* 求值面语义：bk_Qn_eval n z == Σ_{k≤n} C(n,k)²·z^k（QeqT Set 面） *)
Theorem bk_Qn_eval_sem : forall (n : nat) (z : Q),
  QeqT (bk_Qn_eval n z)
       (bk_psQ (fun k => (Z.of_nat (bkC n k * bkC n k) # 1)%Q) (Datatypes.S n) z).
Proof.
  intros n z. unfold bk_Qn_eval, bk_Qn_list.
  rewrite bk_idx_seq.
  apply qeq_imp_qeqT.
  apply bkQ_seq_map.
Qed.


(* 谐和数 H_k = Σ_{j=1}^{k} 1/j（Q 层 Fixpoint） *)
Fixpoint bk_H (k : nat) : Q :=
  match k with
  | 0 => 0%Q
  | Datatypes.S k' => bk_H k' + (1%Q / (Z.of_nat (Datatypes.S k') # 1))%Q
  end.

(* P_n 系数列表：第 k 项 = C(n,k)²·H_k *)
Definition bk_Pn_list (n : nat) : list Q :=
  map (fun k => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
      (bk_idx (Datatypes.S n)).

(* 求值面：bkQ (bk_Pn_list n) z == Σ_{k≤n} C(n,k)²·H_k·z^k（QeqT Set 面） *)
Theorem bk_Pn_eval : forall (n : nat) (z : Q),
  QeqT (bkQ (bk_Pn_list n) z)
       (bk_psQ (fun k => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
               (Datatypes.S n) z).
Proof.
  intros n z. unfold bk_Pn_list.
  rewrite bk_idx_seq.
  apply qeq_imp_qeqT.
  apply bkQ_seq_map.
Qed.

(* P_n 系数逐项刻画 *)
Lemma bk_Pn_list_nth : forall n k : nat, k <= n ->
  nth k (bk_Pn_list n) 0%Q == ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q.
Proof.
  intros n k Hk.
  unfold bk_Pn_list. rewrite bk_idx_seq.
  apply bk_nth_map_seq. lia.
Qed.

(* 假设审计留痕：Print Assumptions（G4 复核位）                          *)

Print Assumptions bk_Qn_sym.
Print Assumptions bk_psd_binom.
Print Assumptions bk_Qn_ge_3pow_nat.
Print Assumptions bk_Qn_int.
Print Assumptions bk_Qn_ge_3pow.
Print Assumptions bk_Qn_eval_sem.
Print Assumptions bk_Qn_list_nth.
Print Assumptions bk_Pn_eval.
Print Assumptions bk_Pn_list_nth.
