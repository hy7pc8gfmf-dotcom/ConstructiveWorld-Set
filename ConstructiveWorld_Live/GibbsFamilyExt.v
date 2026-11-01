(* ==========================================================================)
   GibbsFamilyExt.v — Gibbs 不等式族的温度扩展
   使命: gfe_gibbs_core_temp_B/gibbs_inequality_temp_B（温度参数化 Gibbs）、gibbs_temp_gap_B 及 flat 形、le_b_mult_pos（正乘保序）、Jeffreys 对称熵两件（gfe_jeffreys_sym_B/sym_list_B）。
   依赖: CW_ConstructiveWorld_219、UpRealLeB/2/3、UpReqKLStrictB；Stdlib List。
   对标: Gibbs 不等式（相对熵非负性）与 Jeffreys 散度的族化。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
Import ListNotations.
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
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import UpReqKLStrictB.

(* ============================================================ *)
(* Part 0：序代数支撑件（四件）                                          *)
(* ============================================================ *)

(* 0.1 严格正到弱非负桥（温度前提降级：β>0 出口喂 β≥0 入口）。
   real_le 为 Or 编码（CW219 S02:460），lt 支 inl 直连——
   零中介件（S07 real_lt_le_iff_req 不入 CW219 聚合出口，实测）。 *)
Lemma gfe_le_of_lt : forall b : Real,
  real_lt real_zero b -> real_le real_zero b.
Proof.
  intros b Hb. exact (inl Hb).
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

(* ============================================================ *)
(* Part A：温度参数化形（真缺变体面 A；β 加权 Gibbs 族五件）             *)
(* ============================================================ *)

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
  exact (real_le_closure_b real_zero
           (real_mult b (real_list_sum X
               (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))
           b Hb
           (fun eps Heps => gfe_gibbs_inequality_temp_eps X l p q Hp Hq
              Hnormp Hnormq b (gfe_le_of_lt b Hb) eps Heps)).
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

(* ============================================================ *)
(* Part B：对称 Jeffreys 形（真缺变体面 B；非对称互补面两件）            *)
(* ============================================================ *)

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

(* ============================================================ *)
(* 闭合审计（G4：Print Assumptions 全 Closed）                           *)
(* ============================================================ *)

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
