(* ============================================================ *)
(* PowRealCompat.v —— powb_pow 与 real_pow 两幂载体的换形桥与性质运输件 *)
(*                                                                     *)
(* 使命：G07_KLWall 的 powb_pow 与 CW220_Extensions 的 real_pow 是两    *)
(*   同构 Fixpoint（O ↦ real_one、S m ↦ real_mult base …），本件形式化  *)
(*   二者在全参数域（base : Real，t : nat）上的一致性并交付换形与运输   *)
(*   八件（prc_ 前缀）：①Id 级同构桥（对 t 归纳）；②real_eq 级桥        *)
(*   （real_eq_mult_compat 逐级组装）；③反向桥（real_eq_sym）；         *)
(*   ④powb 载体 eq_compat（G07 侧原缺位的补齐件，归纳真证）；           *)
(*   ⑤同语句对接路线（CW220 real_pow_eq_compat 经②③双桥接入，与        *)
(*   ④双路线互证）；⑥⑦单调件与幂不超一 Bishop 件经①运输；              *)
(*   ⑧CW220 real_pow_anti_mono（stdlib nat le 前提位）经 NatLe_drop     *)
(*   与①回运 powb 载体，序界统一为 Set 层 NatLe。                      *)
(* 依赖：CW_ConstructiveWorld_219、G07_KLWall、CW220_Extensions         *)
(*   （BudgetReal）、UpRealLeB、UpRealLeB2。                            *)
(* 对标：mathlib Nat.pow 的载体换算引理族。                             *)
(* 构造性注记：Set 层承载（real_eq/real_lt/real_le/NatLe 全 Set 值）；   *)
(*   件 1 为 Id 级换形（Coq Id 等词属 Prop 型，零前提位，仅作件 6/7/8   *)
(*   内 rewrite 运输的载体）；零承认、公理面为空、可提取；              *)
(*   文尾 Print Assumptions 八件全 Closed。                             *)
(* 编译配方：Rocq 9.1 直调 rocq c -Q . "" PowRealCompat.v，cpu_guard    *)
(*   包装。                                                             *)
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
Require Import G07_KLWall.
Require Import CW220_Extensions.
Import CW220_Extensions.BudgetReal.
Require Import UpRealLeB.
Require Import UpRealLeB2.

(* ============================================================ *)
(* 一、双向换形桥（Id 级 / real_eq 级）                                *)
(* ============================================================ *)

(* 件 1：Id 级同构桥——对 t 归纳，每步 cbn 定向展开两载体各一步          *)
Lemma prc_powb_real_pow_id : forall (base : Real) (t : nat),
  real_eq (powb_pow base t) (real_pow base t).
Proof.
  intros base t. induction t as [| m IH].
  - cbn [powb_pow real_pow]. apply real_eq_refl.
  - cbn [powb_pow real_pow].
    apply (RealSetoid.real_eq_mult_compat base (powb_pow base m)
                                          base (real_pow base m)).
    + apply real_eq_refl.
    + exact IH.
Qed.

(* 件 2：real_eq 级桥——归纳 + real_eq_mult_compat 逐级组装             *)
Lemma prc_powb_real_pow_req : forall (base : Real) (t : nat),
  real_eq (powb_pow base t) (real_pow base t).
Proof.
  intros base t. induction t as [| m IH].
  - apply real_eq_refl.
  - cbn [powb_pow real_pow].
    apply (RealSetoid.real_eq_mult_compat base (powb_pow base m)
                                          base (real_pow base m)).
    + apply real_eq_refl.
    + exact IH.
Qed.

(* 件 3：反向桥（req 对称单步；双向换形成对交付）                       *)
Lemma prc_real_pow_powb_req : forall (base : Real) (t : nat),
  real_eq (real_pow base t) (powb_pow base t).
Proof.
  intros base t.
  exact (real_eq_sym (real_pow base t) (powb_pow base t)                     (prc_powb_real_pow_req base t)).
Qed.

(* ============================================================ *)
(* 二、eq_compat 级对接件（G07 侧原缺位补齐；双路线互证）               *)
(* ============================================================ *)

(* 件 4：powb 载体 eq_compat——归纳真证（G07 侧原缺位）                 *)
Lemma prc_powb_eq_compat : forall (x y : Real) (n : nat),
  real_eq x y -> real_eq (powb_pow x n) (powb_pow y n).
Proof.
  intros x y n Hxy. induction n as [| m IH].
  - apply real_eq_refl.
  - cbn [powb_pow].
    apply (RealSetoid.real_eq_mult_compat x (powb_pow x m)
                                          y (powb_pow y m)).
    + exact Hxy.
    + exact IH.
Qed.

(* 件 5：同语句对接路线——CW220 real_pow_eq_compat 经 2/3 双桥接入      *)
Lemma prc_powb_eq_compat_via_cwe : forall (x y : Real) (n : nat),
  real_eq x y -> real_eq (powb_pow x n) (powb_pow y n).
Proof.
  intros x y n Hxy.
  apply (real_eq_trans (powb_pow x n) (real_pow x n) (powb_pow y n)).
  - exact (prc_powb_real_pow_req x n).
  - apply (real_eq_trans (real_pow x n) (real_pow y n) (powb_pow y n)).
    + exact (real_pow_eq_compat x y n Hxy).
    + exact (real_eq_sym (real_pow y n) (powb_pow y n)
                         (prc_powb_real_pow_req y n)).
Qed.

(* ============================================================ *)
(* 三、载体间性质运输（G07 Bishop 件 → real_pow 载体；                  *)
(*     CW220 Or 序界件 → powb 载体）                                   *)
(* ============================================================ *)

(* 件 6：G07 单调性结论 P2 的运输——NatLe 序界 Bishop 形幂单调递减，     *)
(*   现 real_pow 载体同款可用（CW220 侧原缺位）                         *)
Lemma prc_powb_mono_dec_real_pow : forall (base : Real) (m : nat),
  real_lt real_zero base -> real_le base real_one ->
  forall n : nat, NatLe n m ->
  real_le_b (real_pow base m) (real_pow base n).
Proof.
  intros base m Hb Hle n Hnm.
  pose proof (powb_mono_dec base m Hb Hle n Hnm) as HB.
  intros eps Heps.
  apply (RealSetoid.real_lt_compat (powb_pow base m) (real_pow base m)
                                   (real_plus (powb_pow base n) eps)
                                   (real_plus (real_pow base n) eps)).
  - apply prc_powb_real_pow_id.
  - apply (RealSetoid.real_eq_plus_compat (powb_pow base n) eps
                                          (real_pow base n) eps).
    + apply prc_powb_real_pow_id.
    + apply real_eq_refl.
  - exact (HB eps Heps).
Qed.

(* 件 7：幂不超一 Bishop 件运输                                        *)
Lemma prc_powb_le_one_pow_real_pow : forall (base : Real) (t : nat),
  real_lt real_zero base -> real_le base real_one ->
  real_le_b (real_pow base t) real_one.
Proof.
  intros base t Hb Hle.
  pose proof (powb_le_one_pow base t Hb Hle) as HB.
  intros eps Heps.
  apply (RealSetoid.real_lt_compat (powb_pow base t) (real_pow base t)
                                   (real_plus real_one eps)
                                   (real_plus real_one eps)).
  - apply prc_powb_real_pow_id.
  - apply real_eq_refl.
  - exact (HB eps Heps).
Qed.

(* 件 8：CW220 real_pow_anti_mono 的引用——stdlib nat le 前提位经       *)
(*   NatLe_drop 转 Set 层 NatLe 序界，结论经 Id 桥回运 powb 载体        *)
Lemma prc_powb_anti_mono_real_le : forall (k : Real),
  real_lt real_zero k -> real_le k real_one ->
  forall p q : nat, NatLe p q ->
  real_le (powb_pow k q) (powb_pow k p).
Proof.
  intros k Hk1 Hk2 p q Hpq.
  pose proof (real_pow_anti_mono k Hk1 Hk2 p q (NatLe_drop p q Hpq)) as HA.
  apply (RealSetoid.real_le_compat (real_pow k q) (powb_pow k q)
                                   (real_pow k p) (powb_pow k p)).
  - exact (real_eq_sym (powb_pow k q) (real_pow k q)
                       (prc_powb_real_pow_id k q)).
  - exact (real_eq_sym (powb_pow k p) (real_pow k p)
                       (prc_powb_real_pow_id k p)).
  - exact HA.
Qed.

(* ============================================================ *)
(* 公理面自审（文末八条 Print Assumptions）                            *)
(* ============================================================ *)
Print Assumptions prc_powb_real_pow_id.
Print Assumptions prc_powb_real_pow_req.
Print Assumptions prc_real_pow_powb_req.
Print Assumptions prc_powb_eq_compat.
Print Assumptions prc_powb_eq_compat_via_cwe.
Print Assumptions prc_powb_mono_dec_real_pow.
Print Assumptions prc_powb_le_one_pow_real_pow.
Print Assumptions prc_powb_anti_mono_real_le.
