(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpReqKLStrictB.v *)
(* 目的： KLStrict 族的 ≤_B 显式对照与完成件。 *)
(* 主件： klstb_kl_sum_strict_B / klstb_gibbs_core_zero_B：严格核的 B 形完成。 *)
(* 依赖： CW_ConstructiveWorld_219、UpRealLeB、UpRealLeB2、UpRealLeB3、G07_KLWall。 *)
(* 备注： 结论 C 为显式假设件（G07_KLWall 成员承担）；对照形与原 eps 形并存。 *)
(* ============================================================ *)
(*   尾注结论 C：「逐项 Bishop 形（eps 余量）无前提路线由库侧 real_gibbs_core_eps/    *)
(*   real_gibbs_inequality_eps 承载；E.12 real_gibbs_core_B（UpRealLeB L578）与       *)
(*   E.13 real_gibbs_inequality_B（UpRealLeB L592）两件「eps 形源件 -> ≤_B」直接完成器  *)
(*   已在盘（real_le_closure_b D:=p 实例/closure_b_one 单步定式），本件不再复刻——本件  *)
(*   覆盖其未覆盖余留面：A. 严格层 sigT 正陈述 -> ≤_B 的显式单向桥（real_lt ->         *)
(*   real_le_b）；B. ≤_B 右平移兼容器（plus_compat + 自反一步合成）；C. 逐项无条件      *)
(*   B 面：0 ≤_B kl_term(p,q)+(q−p)（零比较零归一化前提，仅 Hp/Hq 供 real_kl_term       *)
(*   类型位；p<q 与 p==q 与 q<p 三支合一）；D. ≤_B 逐点求和保序器（族级组合器；          *)
(*   UpRealLeB/2/3 无 list 版）；E. 无条件平移和件（0 ≤_B Σ_s (kl_term+(q−p))）；        *)
(*   F. klst 严格族两主件的 ≤_B 对照形（签名逐位对位，结论换 ≤_B）；G. 退化对照件        *)
(*   klst_gibbs_core_zero 的 ≤_B 对偶面。基座（全在盘只读使用）：UpRealLeB               *)
(*   （real_le_b L63 定义/real_le_to_le_b L78/real_le_closure_b_one L373/E.12/E.13）、    *)
(*   UpRealLeB2（real_le_b_plus_compat L336）、UpRealLeB3（leb3_le_b_refl L45/           *)
(*   leb3_le_b_eq_l L51）、G07_KLWall（klst_kl_sum_strict/klst_kl_energy_nonconst/       *)
(*   klst_gibbs_core_zero/real_kl_term/real_list_sum）。红线自审：real_le_b 为 Set 值    *)
(*   全称谓词（UpRealLeB L63），real_lt 为 sigT 见证集值，语句面全 Set 零类域降级；       *)
(*   纯构造（弱三分内消解，不引入排中形态前提）；全件 Qed。                              *)
(*   编译配方：-Q ConstructiveWorld_vo "" -Q 本目录 ""。                                 *)
(* ============================================================ *)

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
Require Import G07_KLWall.

(* ============================================================ *)
(* Part 0：换形辅件——平移量正负对消的等式面                            *)
(* ============================================================ *)

(* (p−q)+(q−p) == 0：assoc/comm/opp/zero 显式链（无环法，G07 C0 同款手法） *)
Lemma klstb_pq_shift_zero : forall p q : Real,
  real_eq (real_plus (real_plus p (real_opp q)) (real_plus q (real_opp p)))
          real_zero.
Proof.
  intros p q.
  apply (real_eq_trans
           (real_plus (real_plus p (real_opp q)) (real_plus q (real_opp p)))
           (real_plus p (real_opp p))
           real_zero).
  - apply (real_eq_trans
             (real_plus (real_plus p (real_opp q)) (real_plus q (real_opp p)))
             (real_plus p (real_plus (real_opp q) (real_plus q (real_opp p))))
             (real_plus p (real_opp p))).
    + apply real_eq_sym. apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat p
               (real_plus (real_opp q) (real_plus q (real_opp p)))
               p (real_opp p)).
      * apply real_eq_refl.
      * (* 内层：(−q) + (q + (−p)) == −p *)
        apply (real_eq_trans
                 (real_plus (real_opp q) (real_plus q (real_opp p)))
                 (real_plus (real_plus (real_opp q) q) (real_opp p))
                 (real_opp p)).
        -- apply real_plus_assoc.
        -- apply (real_eq_trans
                    (real_plus (real_plus (real_opp q) q) (real_opp p))
                    (real_plus (real_plus q (real_opp q)) (real_opp p))
                    (real_opp p)).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus (real_opp q) q) (real_opp p)
                       (real_plus q (real_opp q)) (real_opp p)).
              ** apply real_plus_comm.
              ** apply real_eq_refl.
           ++ apply (real_eq_trans
                       (real_plus (real_plus q (real_opp q)) (real_opp p))
                       (real_plus real_zero (real_opp p))
                       (real_opp p)).
              ** apply (RealSetoid.real_eq_plus_compat
                          (real_plus q (real_opp q)) (real_opp p)
                          real_zero (real_opp p)).
                 --- apply real_plus_opp.
                 --- apply real_eq_refl.
              ** apply (real_eq_trans
                          (real_plus real_zero (real_opp p))
                          (real_plus (real_opp p) real_zero)
                          (real_opp p)).
                 --- apply real_plus_comm.
                 --- apply real_plus_zero.
  - apply real_plus_opp.
Qed.

(* ============================================================ *)
(* Part A：严格 → ≤_B 显式单向桥（结论 C 需求件之一）                    *)
(* ============================================================ *)

(* x < y（sigT 正陈述）⟹ x ≤_B y：real_lt_le_iff_req 左支入 Or 面，      *)
(*   再经 real_le_to_le_b 单向桥（Set 层全程，零类域降级）                *)
Lemma klstb_lt_le_b : forall x y : Real,
  real_lt x y -> real_le_b x y.
Proof.
  intros x y Hlt.
  apply real_le_to_le_b.
  apply (RealSetoid.real_lt_le_iff_req x y).
  left. exact Hlt.
Qed.

(* ============================================================ *)
(* Part B：≤_B 右平移兼容器                                              *)
(* ============================================================ *)

Lemma klstb_le_b_translate_r : forall x y z : Real,
  real_le_b x y -> real_le_b (real_plus x z) (real_plus y z).
Proof.
  intros x y z H.
  apply (real_le_b_plus_compat x y z z H).
  apply leb3_le_b_refl.
Qed.

(* ============================================================ *)
(* Part C：逐项无条件 B 面——0 ≤_B kl_term + (q−p)                       *)
(*   （结论 C「无前提路线」≤_B 显形：零比较前提、零归一化前提；          *)
(*    证书供给 = E.12 real_gibbs_core_B 右平移 (q−p) + Part 0 对消）     *)
(* ============================================================ *)

Lemma klstb_gibbs_core_shift_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_le_b real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))).
Proof.
  intros p q Hp Hq.
  apply (leb3_le_b_eq_l
           (real_plus (real_plus p (real_opp q)) (real_plus q (real_opp p)))
           real_zero
           (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
           (klstb_pq_shift_zero p q)).
  apply (klstb_le_b_translate_r (real_plus p (real_opp q))
                                (real_kl_term p q Hp Hq)
                                (real_plus q (real_opp p))).
  unfold real_kl_term.
  exact (real_gibbs_core_B p q Hp Hq).
Qed.

(* ============================================================ *)
(* Part D：≤_B 逐点求和保序器（族级组合器；real_list_sum 形）            *)
(* ============================================================ *)

Lemma klstb_list_sum_zero : forall (X : Type) (l : list X),
  real_eq (real_list_sum X (fun _ : X => real_zero) l) real_zero.
Proof.
  intros X l.
  induction l as [| w l IH].
  - apply real_eq_refl.
  - cbn [real_list_sum].
    apply (real_eq_trans
             (real_plus real_zero (real_list_sum X (fun _ : X => real_zero) l))
             (real_plus (real_list_sum X (fun _ : X => real_zero) l) real_zero)
             real_zero).
    + apply real_plus_comm.
    + apply (real_eq_trans
               (real_plus (real_list_sum X (fun _ : X => real_zero) l) real_zero)
               (real_list_sum X (fun _ : X => real_zero) l)
               real_zero).
      * apply real_plus_zero.
      * exact IH.
Qed.

Lemma klstb_list_sum_le_b : forall (X : Type) (f g : X -> Real) (l : list X),
  (forall s : X, real_le_b (f s) (g s)) ->
  real_le_b (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l H.
  induction l as [| w l IH].
  - apply leb3_le_b_refl.
  - cbn [real_list_sum].
    apply (real_le_b_plus_compat (f w) (g w)
             (real_list_sum X f l) (real_list_sum X g l)).
    + apply H.
    + exact IH.
Qed.

(* ============================================================ *)
(* Part E：无条件平移和件——0 ≤_B Σ_s (kl_term + (q−p))                  *)
(*   （零比较前提、零归一化前提；逐项 Part C 经 Part D 完成）            *)
(* ============================================================ *)

Lemma klstb_kl_sum_shift_B : forall (X : Type) (l : list X) (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s)),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                               (real_plus (q s) (real_opp (p s)))) l).
Proof.
  intros X l p q Hp Hq.
  apply (leb3_le_b_eq_l
           (real_list_sum X (fun _ : X => real_zero) l)
           real_zero
           (real_list_sum X
              (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                      (real_plus (q s) (real_opp (p s)))) l)
           (klstb_list_sum_zero X l)).
  apply (klstb_list_sum_le_b X
           (fun _ : X => real_zero)
           (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                   (real_plus (q s) (real_opp (p s)))) l).
  intro s.
  apply (klstb_gibbs_core_shift_B (p s) (q s) (Hp s) (Hq s)).
Qed.

(* ============================================================ *)
(* Part F：klst 严格族两主件的 ≤_B 对照形（签名逐位对位）                *)
(*   对照件语义：前提面照抄族件、结论面由 strict 换 ≤_B——               *)
(*   严格层与 Bishop 层在同型语句面上的可达性显形。                      *)
(* ============================================================ *)

(* 对位 klst_kl_sum_strict（G07 Part D，单向弱序支）：使命点名件          *)
Lemma klstb_kl_sum_strict_B : forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hpq : forall s : X, real_le (p s) (q s))
  (Hnormp : real_eq (real_list_sum X p (l₁ ++ s₀ :: l₂)) real_one)
  (Hnormq : real_eq (real_list_sum X q (l₁ ++ s₀ :: l₂)) real_one)
  (Hdiv : real_lt (p s₀) (q s₀)),
  real_le_b real_zero
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                    (l₁ ++ s₀ :: l₂)).
Proof.
  intros X l₁ s₀ l₂ p q Hp Hq Hpq Hnormp Hnormq Hdiv.
  apply (klstb_lt_le_b real_zero
          (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                         (l₁ ++ s₀ :: l₂))).
  exact (klst_kl_sum_strict X l₁ s₀ l₂ p q Hp Hq Hpq Hnormp Hnormq Hdiv).
Qed.

(* 对位 klst_kl_energy_nonconst（G07 Part G，双向弱序无条件主件）         *)
Lemma klstb_kl_energy_nonconst_B : forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hpq : forall s : X, Or (real_le (p s) (q s)) (real_le (q s) (p s)))
  (Hnormp : real_eq (real_list_sum X p (l₁ ++ s₀ :: l₂)) real_one)
  (Hnormq : real_eq (real_list_sum X q (l₁ ++ s₀ :: l₂)) real_one)
  (Hdiv : Or (real_lt (p s₀) (q s₀)) (real_lt (q s₀) (p s₀))),
  real_le_b real_zero
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                    (l₁ ++ s₀ :: l₂)).
Proof.
  intros X l₁ s₀ l₂ p q Hp Hq Hpq Hnormp Hnormq Hdiv.
  apply (klstb_lt_le_b real_zero
          (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                         (l₁ ++ s₀ :: l₂))).
  exact (klst_kl_energy_nonconst X l₁ s₀ l₂ p q Hp Hq Hpq Hnormp Hnormq Hdiv).
Qed.

(* ============================================================ *)
(* Part G：退化对照件的 ≤_B 对偶面                                       *)
(*   （p == q ⟹ kl_term+(q−p) == 0，经 eq 面右支入桥；与 Part C 成对——   *)
(*    C 支 q≠p 无前提、G 支等号点，三支在 ≤_B 面合流）                   *)
(* ============================================================ *)

Lemma klstb_gibbs_core_zero_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hpq : real_eq p q),
  real_le_b real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))).
Proof.
  intros p q Hp Hq Hpq.
  apply real_le_to_le_b.
  apply (RealSetoid.real_eq_le real_zero
           (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))).
  apply real_eq_sym.
  exact (klst_gibbs_core_zero p q Hp Hq Hpq).
Qed.

(* ============================================================ *)
(* 闭合审计（Print Assumptions 须全 Closed）                             *)
(* ============================================================ *)

Print Assumptions klstb_pq_shift_zero.
Print Assumptions klstb_lt_le_b.
Print Assumptions klstb_le_b_translate_r.
Print Assumptions klstb_gibbs_core_shift_B.
Print Assumptions klstb_list_sum_zero.
Print Assumptions klstb_list_sum_le_b.
Print Assumptions klstb_kl_sum_shift_B.
Print Assumptions klstb_kl_sum_strict_B.
Print Assumptions klstb_kl_energy_nonconst_B.
Print Assumptions klstb_gibbs_core_zero_B.
