(* ========================================================================= *)
(*  DTPT_Entropy.v — 多熵函数族扩展 + 多熵评估套件                           *)
(*                                                                            *)
(*  使命：香农熵 Q 离散版（频域计数 H_devsum／H_freq）、条件熵 H_cond         *)
(*    （原文附录三.4「上下文依赖度」）、λ-插值混合熵 H_lam 的 Q 载体          *)
(*    构造与非负／单调／置换面定理族；多熵评估套件（Record                    *)
(*    MultiEntropyEval 与 me_cert 联合相干证书）；熵族拼接卷积与             *)
(*    数值锚。                                                                *)
(*                                                                            *)
(*  依赖：QArith（QArith/Qabs）、List、Arith、Lia、Permutation、DTPT。       *)
(*    与 DTPT.v 的 xq_ 工具箱簇为双副本维持（同名同构，头注互指）。          *)
(*                                                                            *)
(*  对标：原典 §2.3 多熵族 ℋ = {H_alg, H_Sh, H_vN, H_str, H_Rényi,          *)
(*    H_min, H_max, H_top, H_cond} + 附录三「多熵评估套件」。                *)
(*                                                                            *)
(*  构造性注记：零公理、零承认、无经典逻辑，Set 层零公理面，全程 Qed；       *)
(*    B2 补证件 H_lam_mono／H_shannon_q_nonneg 已证；                         *)
(*    H_shannon_q_perm_inv 经核查为假（H_devsum 取后缀最小值，置换改变       *)
(*    后缀结构），以 H_shannon_q_perm_inv_counterex 构造性反例替代           *)
(*    （见文内注）。                                                          *)
(*                                                                            *)
(*  编译配方：coqc -native-compiler no -q -Q . "" DTPT_Entropy.v                 *)
(*    （先编依赖 DTPT.v）。文件内分节 §1-§A8，各节头注为该节要点索引。       *)
(* ========================================================================= *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Notation S := Datatypes.S.
From Stdlib Require Import Setoid Morphisms.

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Permutation.
Import ListNotations.
Open Scope Q_scope.

(* ========== Set 承载桥 twin（born-clean·与 DTPT.v 同名同构·头注互指） ========== *)
(* Id/NatLe/QeqT/QleT'/QltT 及其升降桥由 S01_BaseRing/S02_CauchyComplete 供给； *)
(* 此处补 eq→Id 桥 twin 与 IffT 承载（S01 未导出、DTPT.v:32-37 同构副本）。 *)
(* born-clean：零 Prop 语句面、零承认；IffT A B := (A->B)*(B->A) Set 承载当且仅当。 *)

Lemma eq_imp_id {A : Set} {x y : A} (H : x = y) : Id x y.
Proof. destruct H. apply id_refl. Qed.

Definition IffT (A B : Set) : Set := (A -> B) * (B -> A).
Fixpoint insert_q (x : Q) (l : list Q) : list Q :=
  match l with
  | [] => [x]
  | y :: ys => if Qle_bool x y then x :: y :: ys else y :: insert_q x ys
  end.

Fixpoint P0 (l : list Q) : list Q :=
  match l with
  | [] => []
  | x :: xs => insert_q x (P0 xs)
  end.

Definition rot (n : nat) (l : list Q) : list Q :=
  firstn n l ++ skipn n l.

Definition Pinf (l : list Q) (s : nat) : list Q :=
  rot (S s) l.

Lemma insert_q_perm_cons : forall (x : Q) (l : list Q),
  Permutation (x :: l) (insert_q x l).
Proof.
  intros x l. induction l as [| y ys IH]; simpl.
  - simpl. apply perm_skip. apply perm_nil.
  - destruct (Qle_bool x y) eqn:Hxy.
    + apply perm_skip. apply Permutation_refl.
    + etransitivity.
      * apply perm_swap.
      * apply perm_skip. exact IH.
Qed.

Theorem D5_P0_perm : forall l : list Q, Permutation l (P0 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply Permutation_refl.
  - etransitivity.
    + apply perm_skip. exact IH.
    + apply insert_q_perm_cons.
Qed.

(* 【弃用注记】本件在 rot=firstn++skipn 恒等基础模块下为恒等推论伪装；操作语义以 DTPT_ROTC/DTPT_Cyc/DTPT_RotSpec 真化层为准。 *)

Theorem D5_Pinf_perm : forall (l : list Q) (s : nat), Permutation l (Pinf l s).
Proof.
  intros l s. unfold Pinf, rot.
  rewrite firstn_skipn.
  apply Permutation_refl.
Qed.

(* D5_Pmid_perm: general lam is false (firstn/skipn truncation not a permutation); covered by endpoint theorems. *)

Fixpoint dedup_aux (x : Q) (l : list Q) : list Q :=
  match l with
  | [] => []
  | y :: ys => if Qeq_bool x y then dedup_aux x ys else y :: dedup_aux x ys
  end.

Fixpoint dedup (l : list Q) : list Q :=
  match l with
  | [] => []
  | x :: xs => x :: dedup_aux x (dedup xs)
  end.

Definition H_ms (l : list Q) : Q := (Z.of_nat (length (dedup l)) # 1)%Q.

Fixpoint sum_adjdiff (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => 0
               | y :: _ => Qabs (y - x) + sum_adjdiff xs
               end
  end.

Definition H_adj (l : list Q) : Q := sum_adjdiff l.

(* ========== 补证段 B2：Q 工具箱（lia 不支持 Q，全部 Z 反射直解） ========== *)

Lemma Qle_bool_false_le : forall x y : Q, Qle_bool x y = false -> QleT' (y) (x).
Proof.
  intros x y H. apply Qle_to_QleT'. unfold Qle_bool in H. unfold Qle.
  destruct (Z.leb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E.
  - discriminate.
  - apply Z.leb_gt in E. lia.
Qed.

Lemma Qle_dec' : forall x y : Q, Or (QleT' x y) (QleT' y x).
Proof.
  intros x y. destruct (Qle_bool x y) eqn:E.
  - left. apply Qle_to_QleT'. apply Qle_bool_iff in E. exact E.
  - right. apply Qle_bool_false_le. exact E.
Qed.

Lemma qadd_le : forall a b c d : Q, a <= b -> c <= d -> QleT' (a + c) (b + d).
Proof.
  intros [an ad] [bn bd] [cn cd] [dn dd] H H0.
  apply Qle_to_QleT'.
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos dd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos dd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  assert (H2 : ((cn * Zpos dd) * (Zpos ad * Zpos bd)
                <= (dn * Zpos cd) * (Zpos ad * Zpos bd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H0]).
  lia.
Qed.

Lemma qopp_le : forall a b : Q, a <= b -> QleT' (- b) (- a).
Proof.
  intros [an ad] [bn bd] H.
  apply Qle_to_QleT'.
  simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

Lemma qmul_le_r : forall n m p : Q, n <= m -> 0 <= p -> QleT' (n * p) (m * p).
Proof.
  intros [nn nd] [mn md] [pn pd] H H0.
  apply Qle_to_QleT'.
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((nn * Zpos md) * (pn * Zpos pd)
                <= (mn * Zpos nd) * (pn * Zpos pd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Qed.

Lemma Qle_0_sub' : forall x y : Q, IffT (QleT' x y) (QleT' 0 (y - x)).
Proof.
  intros [nx dx] [ny dy]; simpl; split; intros H.
  - apply Qle_to_QleT'.
    pose proof (QleT'_to_Qle _ _ H) as Hq.
    unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl; lia.
  - apply Qle_to_QleT'.
    pose proof (QleT'_to_Qle _ _ H) as Hq.
    unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl; lia.
Qed.

Lemma abs_eq : forall a : Q, 0 <= a -> QeqT (Qabs a) (a).
Proof.
  intros [n d] H. apply qeq_imp_qeqT. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - reflexivity.
  - exfalso. lia.
Qed.

Lemma abs_neg : forall a : Q, a <= 0 -> QeqT (Qabs a) (- a).
Proof.
  intros [n d] H. apply qeq_imp_qeqT. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - exfalso. lia.
  - reflexivity.
Qed.

Lemma abs_nonneg : forall a : Q, QleT' (0) (Qabs a).
Proof.
  intros [n d]. apply Qle_to_QleT'. unfold Qle. destruct n; simpl; lia.
Qed.

Lemma Qeqb_true_of : forall x y : Q, x == y -> Id (Qeq_bool x y) (true).
Proof.
  intros x y H. apply eq_imp_id. unfold Qeq in H. unfold Qeq_bool.
  destruct (Z.eqb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E; [reflexivity|].
  exfalso. apply Z.eqb_neq in E. lia.
Qed.

Lemma Qeqb_sym : forall x y : Q, Id (Qeq_bool x y) (Qeq_bool y x).
Proof.
  intros x y. apply eq_imp_id. destruct (Qeq_bool x y) eqn:E1, (Qeq_bool y x) eqn:E2; try reflexivity.
  - exfalso. apply Qeq_bool_eq in E1.
    assert (E1' : y == x) by (apply Qeq_sym; exact E1).
    assert (E1b : Id (Qeq_bool y x) true) by (apply Qeqb_true_of; exact E1').
    assert (E1c : Qeq_bool y x = true) by (destruct (id_sym E1b); reflexivity).
    congruence.
  - exfalso. apply Qeq_bool_eq in E2.
    assert (E2' : x == y) by (apply Qeq_sym; exact E2).
    assert (E2b : Id (Qeq_bool x y) true) by (apply Qeqb_true_of; exact E2').
    assert (E2c : Qeq_bool x y = true) by (destruct (id_sym E2b); reflexivity).
    congruence.
Qed.

Lemma Qeqb_trans : forall a b c : Q,
  Qeq_bool a b = true -> Qeq_bool b c = true -> Id (Qeq_bool a c) (true).
Proof.
  intros a b c H1 H2. apply Qeqb_true_of.
  apply Qeq_bool_eq in H1. apply Qeq_bool_eq in H2.
  transitivity b; assumption.
Qed.

(* ========== 补证段 B2：N9_ms_perm_inv 基建（Qeq 成员 + dedup 特征） ========== *)

Definition Qmem (a : Q) (l : list Q) : Set :=
  Id (existsb (fun y => Qeq_bool a y) l) true.

Lemma Qmem_cons : forall a x (l : list Q),
  IffT (Qmem a (x :: l))
       (Or (Id (Qeq_bool a x) true) (Qmem a l)).
Proof.
  intros a x l. split.
  - intro H. unfold Qmem in *. simpl in H.
    assert (Hb : (Qeq_bool a x || existsb (fun y => Qeq_bool a y) l)%bool = true)
      by (destruct (id_sym H); reflexivity).
    destruct (Qeq_bool a x) eqn:Ex.
    + left. apply eq_imp_id. reflexivity.
    + right. apply eq_imp_id. exact Hb.
  - intro H. destruct H as [E | Hl].
    + apply eq_imp_id. simpl. rewrite E. reflexivity.
    + apply eq_imp_id. simpl. destruct (id_sym Hl). apply orb_true_r.
Qed.

Lemma Qmem_refl_cons : forall x (l : list Q), Qmem x (x :: l).
Proof.
  intros x l. apply (snd (Qmem_cons x x l)). left.
  apply eq_imp_id. apply Qeq_bool_refl.
Qed.

Lemma Qmem_dedup_aux_keep : forall a x (l : list Q),
  Qmem a (dedup_aux x l) -> Qmem a l.
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H. inversion H.
  - intros H. destruct (Qeq_bool x y).
    + apply (snd (Qmem_cons _ _ _)). right. exact (IH H).
    + apply (fst (Qmem_cons _ _ _)) in H. destruct H as [H|H].
      * apply (snd (Qmem_cons _ _ _)). left. exact H.
      * apply (snd (Qmem_cons _ _ _)). right. exact (IH H).
Qed.

Lemma Qmem_dedup_aux_drop : forall a x (l : list Q),
  Qmem a l -> Qeq_bool a x = false -> Qmem a (dedup_aux x l).
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H _. inversion H.
  - intros H Hax. apply (fst (Qmem_cons _ _ _)) in H.
    destruct (Qeq_bool x y) eqn:Hxy.
    + destruct H as [H|H].
      * exfalso.
        assert (Hay : Qeq_bool a y = true) by (destruct (id_sym H); reflexivity).
        apply Qeq_bool_sym in Hay.
        assert (HxaI : Id (Qeq_bool x a) true)
          by (apply (Qeqb_trans x y a); assumption).
        assert (Hxa : Qeq_bool x a = true)
          by (destruct (id_sym HxaI); reflexivity).
        apply Qeq_bool_sym in Hxa. rewrite Hxa in Hax. discriminate.
      * exact (IH H Hax).
    + apply (snd (Qmem_cons _ _ _)). destruct H as [H|H].
      * left. exact H.
      * right. exact (IH H Hax).
Qed.

Lemma dedup_Qmem_l : forall (l : list Q) a, Qmem a (dedup l) -> Qmem a l.
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - intros H. inversion H.
  - intros H. apply (fst (Qmem_cons _ _ _)) in H. destruct H as [H|H].
    + apply (snd (Qmem_cons _ _ _)). left. exact H.
    + apply (snd (Qmem_cons _ _ _)). right. apply IH.
      exact (Qmem_dedup_aux_keep a x _ H).
Qed.

Lemma dedup_Qmem_r : forall (l : list Q) a, Qmem a l -> Qmem a (dedup l).
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - intros H. inversion H.
  - intros H. apply (snd (Qmem_cons _ _ _)).
    apply (fst (Qmem_cons _ _ _)) in H.
    destruct H as [H|H].
    + left. exact H.
    + destruct (Qeq_bool a x) eqn:Hax.
      * left. apply eq_imp_id. reflexivity.
      * right. apply Qmem_dedup_aux_drop.
        -- apply IH. exact H.
        -- exact Hax.
Qed.

Definition gate_pass (threshold H : Q) : bool :=
  if Qle_bool H threshold then true else false.

(* ============================================================
   §8 归并段 M1：并入 DTPT_CGen.v —— C_gen 排序泛化族
   源件 DTPT-U1（Top-1 热点升级单）。仅移除独立文件的
   Require/Import/Open Scope 头（由本文件头统一承载），
   注释与全部证明体、Qed 面、Print Assumptions 审计出口零改动。
   ============================================================ *)
(* ============================================================
   DTPT_CGen.v — 热点升级单 C-GEN（扫描 Top-1 推荐）
   源件：DTPT-U1（新建文件，Require DTPT，不碰既有八件）

   主定理（定理 C 全排列类泛化）：
     C_gen : forall (l p : list Q), Permutation l p -> H_adj (P0 l) <= H_adj p
   现役主定理 DTPT.C_sorted_min_adj 只证「排序 <= 恒等排列」；
   本件把比较对象泛化到 l 的任意排列 p（全排列类）。

   路线：H_adj (P0 l) 经 xq_telescope（排序伸缩）== lastq - hd，
   首尾成员性经 D5_P0_perm + 置换传递搬到 p，再用 xq_pair_dist_le
   （跨度下界：表内任意两元 Qabs 距离 <= H_adj）闭合。

   加分项：
     C_gen_sym_rev  —— SYM 前置件：反转不变 H_adj (rev l) == H_adj l
     C_gen_attained —— 紧性见证：p := P0 l 直构，界在排列类内取得
     C_gen_sorted   —— 现役主定理 C_sorted_min_adj 的泛化重推（特例核对）

   纪律：零公理、零承认、零中止，全程 Qed；Q 层 lia 禁用，
   全部不等式走 xq_ 桥 + ring（Qabs/lastq/H_adj 作原子）。
   ============================================================ *)

(* 原独立文件 Require/Import/Open Scope 头（From Stdlib QArith/List/Permutation、
   Require Import DTPT、Import ListNotations、Open Scope Q_scope）已于归并时移除。 *)

(* ========== §0 snoc 面小工具（SYM 前置件） ========== *)

(* 表末追加一个元素后，尾元就是它（Leibniz 版） *)


Module DTPT_Entropy.

(* ========== 香农熵 Q 离散版（频域计数×对数，Shannon on Q-list） ========== *)

Fixpoint count_val (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (count_val x ys) else count_val x ys
  end.

Fixpoint H_devsum (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => Qabs (x - hd 0 (P0 l)) + H_devsum xs
  end.

(* ADJ-1 适配层：旧名兼容（only parsing），语义零漂移；改名对账见 DTPT_ADJ1_改名报告.md *)
Notation H_shannon_q := H_devsum (only parsing).

Definition H_cond (l : list Q) (ctx : list Q) : Q :=
  H_devsum l - H_devsum ctx.

(* ========== λ-插值混合熵（原文 D12.3 P_mid 插值的熵版本） ========== *)
Definition H_lam (l : list Q) (s : nat) (lam : Q) : Q :=
  lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s).

(* ========== 多熵评估套件（原典附录三「可操作启发 1」的构造性化） ========== *)

Record MultiEntropyEval : Type := mkME {
  me_carrier : list Q;        (* 评估载体 *)
  me_Hadj    : Q;             (* 序列熵（相邻差） *)
  me_Hms     : Q;             (* 多重集熵（相异值计数） *)
  me_Hsh     : Q;             (* 香农熵（频域计数） *)
  me_Hcond   : Q              (* 条件熵（上下文依赖度） *)
}.

Definition mkMEval (l : list Q) (ctx : list Q) : MultiEntropyEval :=
  mkME l (H_adj l) (H_ms l) (H_devsum l) (H_cond l ctx).

(* ========== 原典附录三的六条操作启发（构造性声明面） ========== *)

(* 启发1：熵相评估——判断输出在 P0/P∞/Pmid 哪一侧 *)
Definition phase_side (l : list Q) (s : nat) : nat :=
  (* 0 = 偏 P0；1 = 偏 P∞（由序列熵与阈值比较，差值数据非 Prop） *)
  if Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s)) then 0 else 1.

(* 启发3：幻觉抑制——极端相位降权（余零过滤的构造性化） *)
Definition gate_low_entropy (H : Q) (threshold : Q) : bool :=
  Qle_bool H threshold.

(* 启发4：对齐策略——λ 偏向 P0 的可验证知识 *)
(*
   （DTPT_Rotation.v §S7 救活块四件 align_lambda_id/H_lam/
   lam_opt_min_align/range 现役使用，签名不可变，双件共存裁决）；
   真定义见文尾 §A7 align_lambda_opt（h0/h1 双熵输入的最优 λ
   选择器，与 Rotation §S7 lam_opt/lam_opt_cyc 同构语义）。 *)
Definition align_lambda (lam : Q) : Q := lam.

(* ========== 关键定理（临时承认搭架） ========== *)

(* 混合熵随 λ 单调——P_mid 插值的熵连续性 *)
Lemma qadd_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> QleT' (0) (a + b).
Proof.
  intros [an ad] [bn bd] H H0.
  apply Qle_to_QleT'.
  simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

Theorem H_lam_mono : forall (l : list Q) (s : nat),
  H_adj (Pinf l s) <= H_adj (P0 l) ->
  forall lam1 lam2 : Q,
    (lam1 <= lam2)%Q -> QleT' (H_lam l s lam1) (H_lam l s lam2).
Proof.
  intros l s Hle lam1 lam2 Hlam. apply Qle_to_QleT'. unfold H_lam.
  change (1 - lam1) with (1 + - lam1)%Q.
  change (1 - lam2) with (1 + - lam2)%Q.
  assert (Hd : (0 <= H_adj (P0 l) + - H_adj (Pinf l s))%Q)
    by (apply QleT'_to_Qle; apply (fst (Qle_0_sub' _ _));
        exact (Qle_to_QleT' _ _ Hle)).
  assert (E1 : lam1 * H_adj (P0 l) + (1 + - lam1) * H_adj (Pinf l s)
             == H_adj (Pinf l s) + lam1 * (H_adj (P0 l) + - H_adj (Pinf l s)))
    by ring.
  assert (E2 : lam2 * H_adj (P0 l) + (1 + - lam2) * H_adj (Pinf l s)
             == H_adj (Pinf l s) + lam2 * (H_adj (P0 l) + - H_adj (Pinf l s)))
    by ring.
  rewrite E1, E2.
  apply QleT'_to_Qle.
  apply qadd_le;
    [ apply Qle_refl
    | apply QleT'_to_Qle; apply qmul_le_r; [exact Hlam | exact Hd] ].
Qed.

(* 香农熵非负（Q 离散版） *)
Theorem H_shannon_q_nonneg : forall l : list Q, QleT' (0) (H_devsum l).
Proof.
  intro l. apply Qle_to_QleT'.
  induction l as [| x xs IH]; simpl.
  - apply Qle_refl.
  - apply QleT'_to_Qle. apply qadd_nonneg.
    + apply QleT'_to_Qle. apply (abs_nonneg (x - hd 0 (P0 (x :: xs)))).
    + exact IH.
Qed.

(*
   H_devsum 沿列表递归取「后缀最小值」(hd 0 (P0 l))，
   置换会改变后缀结构。以下给出构造性反例替代原命题。 *)
Theorem H_shannon_q_perm_inv_counterex :
  sigT (fun l : list Q => sigT (fun p : list Q =>
    And (Permutation l p) (Not (Id (H_devsum l) (H_devsum p))))).
Proof.
  apply (existT _ [3; 1; 2]). apply (existT _ [2; 1; 3]). split.
  - apply perm_trans with (l' := [1; 3; 2]).
    + apply perm_swap.
    + apply perm_trans with (l' := [1; 2; 3]).
      * apply perm_skip. apply perm_swap.
      * apply perm_swap.
  - intro Hc. vm_compute in Hc. inversion Hc.
Qed.

(* ============================================================
   W9 跨相熵桥接定理件 · 补强区块（仅追加，不动上方既有内容）
   目标：把本文件从「定义收集」升级为「定理体系」——
     (1) P0 最小化序列熵 H_adj (P0 l) <= H_adj l
         （配对-望远镜路线：有序表熵=max-min，任意配对距离<=序列熵；
         与 DTPT.v 的 C_sorted_min_adj 相互独立，熵模块自足）
     (2) 跨相下界 H_adj (P0 l) <= H_adj (Pinf l s)
         （关键发现：rot = firstn ++ skipn 恒等，Pinf l s = l）
     (3) λ-插值混合熵跨相夹界
         H_adj (P0 l) <= H_lam l s lam <= H_adj (Pinf l s)，0<=lam<=1
     (4) P0 相零化香农偏差熵 H_devsum (P0 l) == 0 及其最小化
     (5) 频域计数置换不变 + 频谱跨相不变（对照 N9 序列熵可分）
     (6) 条件熵：自条件零、反对称、守卫非负、可负反例（界定适用域）
   注：规格原列「H_devsum 置换不变」「无条件 0 <= H_cond l ctx」
   「H_adj (P0 l) <= H_adj (Pmid l s lam)」三条经核查为假（第一条的
   反例即上方 H_shannon_q_perm_inv_counterex；另两条反例见补强报告），
   已按可证命题重新表述，全部构造性落地。
   本区块 xq_ 前缀引理为局部工具；全程 Qed、零公理；仅依赖 DTPT 中
   已证的 D5_P0_perm / D5_Pinf_perm / insert_q_perm_cons / qadd_le /
   Qle_bool_false_le。
   ============================================================ *)

(* ---------- xq 局部工具：Q 序与绝对值 ---------- *)

Lemma xq_Qle_bool_true : forall x y : Q, (x <= y)%Q -> Id (Qle_bool x y) (true).
Proof.
  intros [nx dx] [ny dy] H. apply eq_imp_id.
  unfold Qle in H. unfold Qle_bool; simpl. apply Z.leb_le. unfold Z.le.
  destruct (Z.compare (nx * Z.pos dy) (ny * Z.pos dx)) eqn:E.
  - discriminate.
  - discriminate.
  - exfalso. apply H. exact E.
Qed.

Lemma xq_Qle_bool_le : forall x y : Q, Qle_bool x y = true -> QleT' (x) (y).
Proof.
  intros [nx dx] [ny dy] H. apply Qle_to_QleT'.
  unfold Qle_bool; simpl. apply Z.leb_le. exact H.
Qed.

Lemma xq_Qle_antisym : forall x y : Q, (x <= y)%Q -> (y <= x)%Q -> QeqT x y.
Proof.
  intros [nx dx] [ny dy] H1 H2. apply qeq_imp_qeqT.
  unfold Qle in H1, H2; simpl in H1, H2.
  unfold Qeq; simpl. lia.
Qed.

(* Rocq 9 的 Qabs 以 Z.abs 实现：Qabs (n # d) = (Z.abs n # d) *)
Lemma xq_abs_id : forall x : Q, (0 <= x)%Q -> QeqT (Qabs x) (x).
Proof.
  intros [n d] Hx. apply qeq_imp_qeqT. unfold Qle in Hx; simpl in Hx.
  assert (Hn : (0 <= n)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite (Z.abs_eq n Hn). reflexivity.
Qed.

Lemma xq_abs_eq0 : forall x : Q, x == 0 -> QeqT (Qabs x) 0.
Proof.
  intros [n d] Hx. apply qeq_imp_qeqT.
  unfold Qeq in Hx; simpl in Hx.
  assert (Hn : (n = 0)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite Hn. reflexivity.
Qed.

Lemma xq_minus_self : forall x : Q, QeqT (x - x) 0.
Proof.
  intros [n d]. apply qeq_imp_qeqT.
  unfold Qminus, Qeq; simpl. lia.
Qed.

Lemma xq_abs_zero : forall x : Q, QeqT (Qabs (x - x)) 0.
Proof.
  intro x. apply xq_abs_eq0.
  apply qeqT_imp_qeq. apply xq_minus_self.
Qed.

Lemma xq_abs_eq : forall x y : Q, x == y -> QeqT (Qabs x) (Qabs y).
Proof.
  intros [n1 d1] [n2 d2] Hxy. apply qeq_imp_qeqT.
  unfold Qeq in Hxy; simpl in Hxy.
  unfold Qabs; simpl. unfold Qeq; simpl.
  pose proof (Z.abs_spec n1) as Ha1. pose proof (Z.abs_spec n2) as Ha2.
  destruct Ha1 as [[A1 B1] | [A1 B1]];
    destruct Ha2 as [[A2 B2] | [A2 B2]];
    try rewrite B1; try rewrite B2; lia.
Qed.

Lemma xq_abs_opp : forall x : Q, QeqT (Qabs (- x)) (Qabs x).
Proof.
  intros [n d]. apply qeq_imp_qeqT.
  unfold Qabs, Qopp; simpl. unfold Qeq; simpl.
  rewrite Z.abs_opp. reflexivity.
Qed.

Lemma xq_minus_opp : forall a b : Q, QeqT (b - a) (- (a - b)).
Proof.
  intros [na da] [nb db]. apply qeq_imp_qeqT.
  unfold Qminus, Qopp, Qeq; simpl.
  rewrite (Pos.mul_comm db da). ring.
Qed.

Lemma xq_abs_sub_comm : forall a b : Q, QeqT (Qabs (a - b)) (Qabs (b - a)).
Proof.
  intros a b. apply qeq_imp_qeqT.
  assert (H1 : Qabs (-(a - b)) == Qabs (a - b)) by (apply qeqT_imp_qeq; apply xq_abs_opp).
  rewrite <- H1.
  apply qeqT_imp_qeq. apply xq_abs_eq. symmetry. apply qeqT_imp_qeq. apply xq_minus_opp.
Qed.

Lemma xq_H_adj_nonneg : forall l : list Q, QleT' (0) (H_adj l).
Proof.
  intro l. apply Qle_to_QleT'. induction l as [| a rest IH].
  - apply Qle_refl.
  - destruct rest as [| b bs].
    + apply Qle_refl.
    + change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      apply QleT'_to_Qle. apply qadd_nonneg;
        [ apply QleT'_to_Qle; apply abs_nonneg | exact IH ].
Qed.

Lemma xq_le_add_abs : forall t h : Q, QleT' (h) (Qabs t + h).
Proof.
  intros t h.
  pose proof (qadd_le 0 (Qabs t) h h
    (QleT'_to_Qle _ _ (abs_nonneg t)) (Qle_refl h)) as HS.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ HS) as HS2.
  rewrite Qplus_0_l in HS2.
  exact HS2.
Qed.

(* ---------- xq 局部工具：升序谓词与 P0 规范形 ---------- *)

Inductive SortedQ : list Q -> Set :=
| sortQ_nil : SortedQ []
| sortQ_cons : forall x xs,
    SortedQ xs -> Forall (fun z => (x <= z)%Q) xs -> SortedQ (x :: xs).

Lemma xq_sortQ_insert : forall (x : Q) (l : list Q),
  SortedQ l -> SortedQ (insert_q x l).
Proof.
  intros x l. revert x. induction l as [| y ys IH]; intros x HS.
  - simpl. apply sortQ_cons; [ apply sortQ_nil | apply Forall_nil ].
  - inversion HS as [| x0 xs0 HSys HFall]; subst.
    rewrite Forall_forall in HFall.
    simpl. destruct (Qle_bool x y) eqn:E.
    + apply sortQ_cons; [ exact HS | ].
      rewrite Forall_forall. intros z Hz. destruct Hz as [Heq | Hz].
      * subst. apply QleT'_to_Qle. apply xq_Qle_bool_le. exact E.
      * apply (Qle_trans x y z).
        -- apply QleT'_to_Qle. apply xq_Qle_bool_le. exact E.
        -- apply HFall. exact Hz.
    + apply sortQ_cons; [ apply IH; exact HSys | ].
      rewrite Forall_forall. intros z Hz.
      assert (Hin : In z (x :: ys)).
      { apply Permutation_in with (l := insert_q x ys).
        - apply Permutation_sym. apply insert_q_perm_cons.
        - exact Hz. }
      destruct Hin as [Heq | Hin].
      * subst. apply QleT'_to_Qle. apply Qle_bool_false_le. exact E.
      * apply HFall. exact Hin.
Qed.

Lemma xq_P0_sorted : forall l : list Q, SortedQ (P0 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply sortQ_nil.
  - apply xq_sortQ_insert. exact IH.
Qed.

(* xq_insert_q_head_aux：insert_q 在「插入点不小于被比元素」时直接置首 *)
Lemma xq_insert_q_head_aux : forall (a b : Q) (bs : list Q),
  (a <= b)%Q -> Id (insert_q a (b :: bs)) (a :: b :: bs).
Proof.
  intros a b bs H. apply eq_imp_id. simpl.
  destruct (id_sym (xq_Qle_bool_true _ _ H)). reflexivity.
Qed.

Lemma xq_sortQ_P0_id : forall l : list Q, SortedQ l -> Id (P0 l) (l).
Proof.
  intro l. induction l as [| a rest IH]; intro HS; apply eq_imp_id.
  - reflexivity.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    change (P0 (a :: rest)) with (insert_q a (P0 rest)).
    destruct (id_sym (IH HSr)). destruct rest as [| b bs].
    + reflexivity.
    + destruct (id_sym (xq_insert_q_head_aux a b bs
                   (HFa b (or_introl eq_refl)))).
      reflexivity.
Qed.

(* ---------- xq 局部工具：lastq 尾元与望远镜方程 ---------- *)

Fixpoint lastq (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => x
               | _ :: _ => lastq xs
               end
  end.

Lemma xq_lastq_In : forall m : list Q, m <> [] -> In (lastq m) m.
Proof.
  induction m as [| a rest IH]; intros Hne.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b bs].
    + simpl. left. reflexivity.
    + simpl. right. apply IH. simpl. discriminate.
Qed.

Lemma xq_hd_In_gen : forall m : list Q, m <> [] -> In (hd 0 m) m.
Proof.
  intros [| h t] H; [ exfalso; apply H; reflexivity | simpl; left; reflexivity ].
Qed.

Lemma xq_P0_cons_ne : forall (x : Q) (xs : list Q), P0 (x :: xs) <> [].
Proof.
  intros x xs. cbn [P0].
  destruct (P0 xs) as [| y ys]; cbn [insert_q].
  - discriminate.
  - destruct (Qle_bool x y); discriminate.
Qed.

Lemma xq_hd_le_lastq : forall l : list Q, SortedQ l -> QleT' (hd 0 l) (lastq l).
Proof.
  intro l. induction l as [| a rest IH]; intro HS; apply Qle_to_QleT'.
  - simpl. apply Qle_refl.
  - destruct rest as [| b bs].
    + simpl. apply Qle_refl.
    + inversion HS as [| x0 xs0 HSr HFa]; subst.
      rewrite Forall_forall in HFa.
      apply (Qle_trans a b).
      * apply HFa. left. reflexivity.
      * apply QleT'_to_Qle. apply IH. exact HSr.
Qed.

(* 望远镜方程：升序表的相邻差总和 == 尾元 - 首元 *)
Lemma xq_telescope : forall l : list Q, SortedQ l -> QeqT (H_adj l) (lastq l - hd 0 l).
Proof.
  induction l as [| a rest IH]; intro HS.
  - apply qeq_imp_qeqT. reflexivity.
  - destruct rest as [| b bs].
    + apply qeq_imp_qeqT.
      change (H_adj [a]) with 0%Q.
      change (lastq [a] - hd 0 [a]) with (a - a)%Q.
      symmetry. apply qeqT_imp_qeq. apply xq_minus_self.
    + apply qeq_imp_qeqT.
      inversion HS as [| x0 xs0 HSr HFa]; subst.
      rewrite Forall_forall in HFa.
      change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      assert (Hab : (0 <= b - a)%Q).
      { apply QleT'_to_Qle. apply (fst (Qle_0_sub' a b)).
        apply Qle_to_QleT'. apply HFa. left. reflexivity. }
      rewrite (qeqT_imp_qeq _ _ (xq_abs_id _ Hab)).
      rewrite (qeqT_imp_qeq _ _ (IH HSr)).
      change (lastq (a :: b :: bs)) with (lastq (b :: bs)).
      change (hd 0 (a :: b :: bs)) with a.
      change (hd 0 (b :: bs)) with b.
      ring.
Qed.

(* 配对距离界：表中任意两元素的 Qabs 距离不超过序列熵 *)
Lemma xq_pair_dist_le : forall (l : list Q) (x y : Q),
  In x l -> In y l -> QleT' (Qabs (x - y)) (H_adj l).
Proof.
  intro l. induction l as [| a rest IH]; intros x y Hx Hy; apply Qle_to_QleT'.
  - exfalso. exact Hx.
  - destruct rest as [| b bs].
    + destruct Hx as [Hx | []]; destruct Hy as [Hy | []]; subst.
      rewrite (qeqT_imp_qeq _ _ (xq_abs_zero _)). apply Qle_refl.
    + change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
      * rewrite (qeqT_imp_qeq _ _ (xq_abs_zero _)).
        apply QleT'_to_Qle. apply qadd_nonneg;
          [ apply QleT'_to_Qle; apply abs_nonneg
          | apply QleT'_to_Qle; apply xq_H_adj_nonneg ].
      * assert (Hr1 : a - y == (a - b) + (b - y)) by ring.
        rewrite Hr1.
        apply (Qle_trans _ (Qabs (a - b) + Qabs (b - y))).
        -- apply Qabs_triangle.
        -- rewrite (qeqT_imp_qeq _ _ (xq_abs_sub_comm a b)).
           apply QleT'_to_Qle. apply qadd_le; [ apply Qle_refl
                          | apply QleT'_to_Qle; apply IH;
                            [ left; reflexivity | exact Hy ] ].
      * assert (Hr2 : x - a == (x - b) + (b - a)) by ring.
        rewrite Hr2.
        apply (Qle_trans _ (Qabs (x - b) + Qabs (b - a))).
        -- apply Qabs_triangle.
        -- rewrite (Qplus_comm (Qabs (x - b)) (Qabs (b - a))).
           apply QleT'_to_Qle. apply qadd_le; [ apply Qle_refl
                          | apply QleT'_to_Qle; apply IH;
                            [ exact Hx | left; reflexivity ] ].
      * apply (Qle_trans _ (H_adj (b :: bs))).
        -- apply QleT'_to_Qle. apply IH; assumption.
        -- apply QleT'_to_Qle. apply xq_le_add_abs.
Qed.

(* ========== W9 主定理 1：P0 最小化序列熵（框架核心） ========== *)

Theorem H_adj_P0_min : forall l : list Q, QleT' (H_adj (P0 l)) (H_adj l).
Proof.
  intro l. apply Qle_to_QleT'. destruct l as [| a rest].
  - apply Qle_refl.
  - assert (HP : H_adj (P0 (a :: rest))
                 == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest)))
      by (apply qeqT_imp_qeq; apply xq_telescope; apply xq_P0_sorted).
    assert (HP2 : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest))).
    { rewrite (qeqT_imp_qeq _ _ (xq_abs_sub_comm (hd 0 (P0 (a :: rest))) (lastq (P0 (a :: rest))))).
      apply qeqT_imp_qeq. apply xq_abs_id.
      apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
      apply xq_hd_le_lastq. apply xq_P0_sorted. }
    rewrite HP. rewrite <- HP2.
    assert (Hm1 : In (hd 0 (P0 (a :: rest))) (a :: rest)).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - apply Permutation_sym. apply D5_P0_perm.
      - apply xq_hd_In_gen. apply xq_P0_cons_ne. }
    assert (Hm2 : In (lastq (P0 (a :: rest))) (a :: rest)).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - apply Permutation_sym. apply D5_P0_perm.
      - apply xq_lastq_In. apply xq_P0_cons_ne. }
    apply QleT'_to_Qle. apply xq_pair_dist_le; assumption.
Qed.

(* ========== W9 主定理 2：跨相下界（P∞ 侧） ========== *)

Corollary Pinf_eq_l : forall (l : list Q) (s : nat), Id (Pinf l s) (l).
Proof.
  intros l. induction l as [| a rest IH]; intros s; apply eq_imp_id.
  - reflexivity.
  - unfold Pinf, rot. destruct s as [| s'].
    + reflexivity.
    + change (firstn (S (S s')) (a :: rest) ++ skipn (S (S s')) (a :: rest) = a :: rest)
        with (a :: (firstn (S s') rest ++ skipn (S s') rest) = a :: rest).
      f_equal. change (firstn (S s') rest ++ skipn (S s') rest) with (Pinf rest s').
      destruct (id_sym (IH s')). reflexivity.
Qed.

Theorem H_adj_cross_phase_lb : forall (l : list Q) (s : nat), QleT' (H_adj (P0 l)) (H_adj (Pinf l s)).
Proof.
  intros l s. apply Qle_to_QleT'.
  destruct (id_sym (Pinf_eq_l l s)).
  apply QleT'_to_Qle. apply H_adj_P0_min.
Qed.

(* ========== W9 主定理 3：λ-插值混合熵跨相夹界 ========== *)

Lemma xq_mul_nonneg : forall a b : Q, (0 <= a)%Q -> (0 <= b)%Q -> QleT' (0) (a * b).
Proof.
  intros [an ad] [bn bd] Ha Hb. apply Qle_to_QleT'. unfold Qle in Ha, Hb; simpl in Ha, Hb.
  unfold Qle, Qmult; simpl. lia.
Qed.

Theorem H_lam_cross_phase_bounds : forall (l : list Q) (s : nat) (lam : Q),
  (0 <= lam)%Q -> (lam <= 1)%Q ->
  And (QleT' (H_adj (P0 l)) (H_lam l s lam))
      (QleT' (H_lam l s lam) (H_adj (Pinf l s))).
Proof.
  intros l s lam Hlam0 Hlam1.
  assert (Hle : (H_adj (P0 l) <= H_adj (Pinf l s))%Q)
    by (apply QleT'_to_Qle; apply H_adj_cross_phase_lb).
  unfold H_lam.
  assert (Hlo : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - H_adj (P0 l))%Q).
  { assert (Er1 : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                  - H_adj (P0 l)
                  == (1 - lam) * (H_adj (Pinf l s) - H_adj (P0 l))) by ring.
    rewrite Er1.
    apply QleT'_to_Qle. apply xq_mul_nonneg.
    - apply QleT'_to_Qle. apply (fst (Qle_0_sub' lam 1)).
      apply Qle_to_QleT'. exact Hlam1.
    - apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
      apply Qle_to_QleT'. exact Hle. }
  assert (Hup : (0 <= H_adj (Pinf l s)
                 - (lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)))%Q).
  { assert (Er2 : H_adj (Pinf l s)
                  - (lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s))
                  == lam * (H_adj (Pinf l s) - H_adj (P0 l))) by ring.
    rewrite Er2.
    apply QleT'_to_Qle; apply xq_mul_nonneg;
      [ exact Hlam0
      | apply QleT'_to_Qle; apply (fst (Qle_0_sub' _ _));
        apply Qle_to_QleT'; exact Hle ]. }
  split.
  - apply (snd (Qle_0_sub' _ _)). apply Qle_to_QleT'. exact Hlo.
  - apply (snd (Qle_0_sub' _ _)). apply Qle_to_QleT'. exact Hup.
Qed.

(* ========== W9 主定理 4：P0 相零化香农偏差熵 + 最小化 ========== *)

Lemma xq_H_shannon_sortQ : forall l : list Q, SortedQ l -> QeqT (H_devsum l) (0).
Proof.
  intro l. induction l as [| a rest IH]; intro HS; apply qeq_imp_qeqT.
  - reflexivity.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    cbn [H_devsum].
    destruct (id_sym (xq_sortQ_P0_id (a :: rest) HS)).
    change (hd 0 (a :: rest)) with a.
    rewrite (qeqT_imp_qeq _ _ (IH HSr)).
    rewrite (qeqT_imp_qeq _ _ (xq_abs_zero _)). ring.
Qed.

Theorem H_shannon_q_P0_zero : forall l : list Q, QeqT (H_devsum (P0 l)) 0.
Proof.
  intro l. apply xq_H_shannon_sortQ. apply xq_P0_sorted.
Qed.

Theorem H_shannon_q_P0_min : forall l : list Q,
  QleT' (H_devsum (P0 l)) (H_devsum l).
Proof.
  intro l. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (H_shannon_q_P0_zero l)).
  apply QleT'_to_Qle. apply H_shannon_q_nonneg.
Qed.

(* ========== W9 主定理 5：频域计数置换/跨相不变（对照 N9 序列熵可分） ========== *)

Theorem count_val_perm : forall (x : Q) (l p : list Q),
  Permutation l p -> Id (count_val x l) (count_val x p).
Proof.
  intros x l p H.
  apply eq_imp_id.
  induction H; simpl.
  - reflexivity.
  - match goal with
    | [ I : count_val x _ = count_val x _ |- _ ] => rewrite I
    end.
    reflexivity.
  - match goal with
    | [ |- context[Qeq_bool x ?u] ] => destruct (Qeq_bool x u) eqn:E1
    end;
    match goal with
    | [ |- context[Qeq_bool x ?u] ] => destruct (Qeq_bool x u) eqn:E2
    end;
    simpl; try match goal with
                  | [ I : count_val x _ = count_val x _ |- _ ] => rewrite I
                  end; reflexivity.
  - match goal with
    | [ I1 : count_val x ?u = count_val x ?v,
        I2 : count_val x ?v = count_val x ?w |- _ ] =>
        etransitivity; [ exact I1 | exact I2 ]
    end.
Qed.

Theorem count_val_phase_spectrum : forall (x : Q) (l : list Q) (s : nat),
  And (Id (count_val x (P0 l)) (count_val x l))
      (Id (count_val x (Pinf l s)) (count_val x l)).
Proof.
  intros x l s. split.
  - apply eq_imp_id.
    rewrite <- (count_val_perm x l (P0 l) (D5_P0_perm l)). reflexivity.
  - apply eq_imp_id.
    rewrite <- (count_val_perm x l (Pinf l s) (D5_Pinf_perm l s)). reflexivity.
Qed.

(* ========== W9 主定理 6：条件熵四要素（守卫非负 + 反例界定） ========== *)

Theorem H_cond_self : forall l : list Q, QeqT (H_cond l l) 0.
Proof.
  intro l. apply qeq_imp_qeqT. unfold H_cond. ring.
Qed.

Theorem H_cond_antisym : forall (l ctx : list Q),
  QeqT (H_cond l ctx) (- H_cond ctx l).
Proof.
  intros l ctx. apply qeq_imp_qeqT. unfold H_cond. ring.
Qed.

Theorem H_cond_nonneg_guarded : forall (l ctx : list Q),
  (H_devsum ctx <= H_devsum l)%Q -> QleT' (0) (H_cond l ctx).
Proof.
  intros l ctx H. apply Qle_to_QleT'. unfold H_cond.
  apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
  apply Qle_to_QleT'. exact H.
Qed.

(* 无条件非负为假：空表条件于高熵上下文时 H_cond = -2 < 0 *)
Theorem H_cond_neg_counterex :
  sigT (fun l : list Q => sigT (fun ctx : list Q => QltT (H_cond l ctx) 0)).
Proof.
  apply (existT _ []). apply (existT _ [5; 3]). apply Qlt_to_QltT.
  unfold H_cond. vm_compute. reflexivity.
Qed.

(* ============================================================
   DTPT-S2 分析+补强件 · 追加区块（只加末尾，不动上方任何既有行）
   四族内容：
   (1) 计数上界族【主定理】：count_val <= length（nat/Q 双形）
       + H_devsum 计数上界（按定义实形适配：逐项 |x - 后缀最小|
         走配对界 <= H_adj，逐和 <= 长度系数 × H_adj，系数经 S 化归）
   (2) MultiEntropyEval 相干性：mkMEval 投影往返（eta 面）
       + 多重集熵退化 H_ms == 1 ⟹ H_devsum == 0
       （dedup 计数 → 全同值 → 排序 → 零化四步桥）
       + 反向面为假的构造性反例（升序表零化但相异值非单一）
   (3) H_lam 端点退化：lam = 1 / lam = 0 分别收回 P0 / Pinf 相熵
   (4) gate_low_entropy / phase_side 行为定理（Qle_bool 双向桥）
   全程 Qed；复用 DTPT.v 的 qmul_le_r / Qle_bool_iff /
   Qle_bool_false_le / dedup_Qmem_r 与盘上 xq_ 工具箱；零新前提。
   ============================================================ *)

(* ---------- xq 局部工具：长度系数的 Q 桥 ---------- *)

Lemma xq_Zlen_nonneg : forall n : nat, QleT' (0) ((Z.of_nat n # 1)%Q).
Proof.
  intro n. apply Qle_to_QleT'. unfold Qle; simpl. lia.
Qed.

Lemma xq_Zlen_S : forall n : nat,
  QeqT (Z.of_nat (S n) # 1) (1 + (Z.of_nat n # 1))%Q.
Proof.
  intro n. apply qeq_imp_qeqT.
  assert (Hz : (Z.of_nat (S n) = 1 + Z.of_nat n)%Z) by lia.
  rewrite Hz. unfold Qeq, Qplus. cbn [Qnum Qden]. lia.
Qed.

Lemma xq_Zlen_inj1 : forall n : nat, ((Z.of_nat n # 1) == 1)%Q -> Id (n) (1%nat).
Proof.
  intros n H. apply eq_imp_id. unfold Qeq in H; simpl in H. lia.
Qed.

Lemma xq_Qeq_le : forall x y : Q, x == y -> QleT' (x) (y).
Proof.
  intros [nx dx] [ny dy] Hxy. apply Qle_to_QleT'. unfold Qeq in Hxy; simpl in Hxy.
  unfold Qle; simpl. lia.
Qed.

(* ---------- 主定理 1a：频域计数的长度上界（nat 形） ---------- *)

Lemma count_val_le_length : forall (x : Q) (l : list Q), NatLe (count_val x l) ((length l)%nat).
Proof.
  intros x l. apply NatLe_lift. induction l as [| y ys IH]; simpl.
  - lia.
  - destruct (Qeq_bool x y); lia.
Qed.

(* 主定理 1b：同上界的 Q 域形式（长度系数口径一致） *)
Lemma count_val_Zle_length : forall (x : Q) (l : list Q),
  QleT' (Z.of_nat (count_val x l) # 1) (Z.of_nat (length l) # 1).
Proof.
  intros x l. apply Qle_to_QleT'.
  pose proof (count_val_le_length x l) as Hn.
  pose proof (NatLe_drop _ _ Hn) as Hn2.
  unfold Qle; simpl. lia.
Qed.

(* ---------- 主定理 1c：H_devsum 计数上界（按定义实形适配） ----------
   H_devsum 的每项是 |x - 后缀最小值|：配对界给出
   逐项 <= H_adj，故总和 <= 长度系数 × H_adj。非平凡点：
   后缀单调（加头只增）+ 系数 S 化归 + 因子序统一。 ---------- *)

Lemma xq_H_adj_suffix_le : forall (a : Q) (l : list Q), QleT' (H_adj l) (H_adj (a :: l)).
Proof.
  intros a l. apply Qle_to_QleT'. destruct l as [| b bs].
  - cbn [H_adj sum_adjdiff]. apply Qle_refl.
  - change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
    apply QleT'_to_Qle. apply xq_le_add_abs.
Qed.

Lemma xq_head_term_le : forall (x : Q) (xs : list Q), QleT' (Qabs (x - hd 0 (P0 (x :: xs)))) (H_adj (x :: xs)).
Proof.
  intros x xs. apply Qle_to_QleT'. apply QleT'_to_Qle. apply xq_pair_dist_le.
  - left. reflexivity.
  - apply Permutation_in with (l := P0 (x :: xs)).
    + apply Permutation_sym. apply D5_P0_perm.
    + apply xq_hd_In_gen. apply xq_P0_cons_ne.
Qed.

Theorem H_shannon_q_count_ub : forall l : list Q, QleT' (H_devsum l) (H_adj l * (Z.of_nat (length l) # 1)).
Proof.
  intro l. induction l as [| x xs IH]; apply Qle_to_QleT'.
  - cbn [H_devsum]. apply QleT'_to_Qle. apply xq_mul_nonneg.
    + apply QleT'_to_Qle. apply xq_H_adj_nonneg.
    + apply QleT'_to_Qle. apply xq_Zlen_nonneg.
  - cbn [H_devsum].
    assert (Hs : (H_devsum xs
                  <= H_adj (x :: xs) * (Z.of_nat (length xs) # 1))%Q).
    { apply (Qle_trans _ (H_adj xs * (Z.of_nat (length xs) # 1))).
      - apply QleT'_to_Qle. exact IH.
      - apply QleT'_to_Qle. apply qmul_le_r.
        + apply QleT'_to_Qle. apply xq_H_adj_suffix_le.
        + apply QleT'_to_Qle. apply xq_Zlen_nonneg. }
    assert (Hh : (Qabs (x - hd 0 (P0 (x :: xs))) <= H_adj (x :: xs))%Q)
      by (apply QleT'_to_Qle; apply xq_head_term_le).
    assert (Hlen : ((Z.of_nat (length (x :: xs)) # 1)
                    == 1 + (Z.of_nat (length xs) # 1))%Q)
      by (cbn [length]; apply qeqT_imp_qeq; apply xq_Zlen_S).
    apply (Qle_trans _ (H_adj (x :: xs)
                        + H_adj (x :: xs) * (Z.of_nat (length xs) # 1))).
    + apply QleT'_to_Qle. apply qadd_le; [exact Hh | exact Hs].
    + rewrite Hlen.
      assert (Heq : H_adj (x :: xs) * (1 + (Z.of_nat (length xs) # 1))
                    == H_adj (x :: xs)
                       + H_adj (x :: xs) * (Z.of_nat (length xs) # 1))
        by ring.
      rewrite Heq. apply Qle_refl.
Qed.

(* ---------- 相干性 2a：全同值表的 H_devsum 零化 ---------- *)

Lemma xq_insert_const_head : forall (a y : Q) (ys : list Q),
  y == a -> Id (insert_q a (y :: ys)) (a :: y :: ys).
Proof.
  intros a y ys Hya. apply eq_imp_id. cbn [insert_q].
  destruct (id_sym (xq_Qle_bool_true a y
              (QleT'_to_Qle _ _ (xq_Qeq_le a y (Qeq_sym y a Hya))))).
  reflexivity.
Qed.

Lemma xq_P0_const_id : forall (a : Q) (l : list Q),
  Forall (fun z => z == a) l -> Id (P0 l) (l).
Proof.
  intros a l. induction l as [| x xs IH]; intro Hfa; apply eq_imp_id.
  - reflexivity.
  - inversion Hfa as [| z zs Hzx Hfxs]; subst.
    cbn [P0]. destruct (id_sym (IH Hfxs)).
    destruct xs as [| y ys].
    + cbn [insert_q]. reflexivity.
    + destruct (id_sym (xq_insert_const_head x y ys
                   (Qeq_trans y a x (Forall_inv Hfxs) (Qeq_sym x a Hzx)))).
      reflexivity.
Qed.

Theorem H_shannon_q_const_zero : forall (a : Q) (l : list Q),
  Forall (fun z => z == a) l -> QeqT (H_devsum l) (0).
Proof.
  intros a l. revert a. induction l as [| x xs IH]; intros a Hfa;
    apply qeq_imp_qeqT.
  - reflexivity.
  - assert (Hfa' : Forall (fun z => z == a) (x :: xs)) by exact Hfa.
    inversion Hfa as [| z zs Hzx Hfxs]; subst.
    cbn [H_devsum].
    destruct (id_sym (xq_P0_const_id a (x :: xs) Hfa')).
    cbn [hd]. rewrite (qeqT_imp_qeq _ _ (xq_abs_zero _)).
    rewrite (qeqT_imp_qeq _ _ (IH a Hfxs)). ring.
Qed.

(* ---------- 相干性 2b：多重集熵退化 ⟹ 香农偏差熵零化 ---------- *)

Lemma xq_len1_el : forall m : list Q,
  length m = 1%nat -> sigT (fun a : Q => Id m (a :: nil)).
Proof.
  intros [| b bs] H; cbn [length] in H.
  - discriminate H.
  - destruct bs as [| c cs].
    + apply (existT _ b). apply eq_imp_id. reflexivity.
    + discriminate H.
Qed.

Lemma xq_In_Qmem : forall (z : Q) (l : list Q), In z l -> Qmem z l.
Proof.
  intros z l. induction l as [| y ys IH]; intro Hind.
  - destruct Hind.
  - simpl in Hind. destruct (Qeq_bool z y) eqn:E.
    + apply (snd (Qmem_cons _ _ _)). left. apply eq_imp_id. exact E.
    + apply (snd (Qmem_cons _ _ _)). right. apply IH.
      destruct Hind as [Heq | Hind].
      * rewrite <- Heq in E. rewrite Qeq_bool_refl in E. discriminate E.
      * exact Hind.
Qed.

Lemma xq_dedup1_all_eq : forall (l : list Q) (a : Q),
  dedup l = a :: nil -> forall z : Q, In z l -> QeqT z a.
Proof.
  intros l a Hd z Hz.
  assert (Hm : Qmem z (dedup l)).
  { apply dedup_Qmem_r. apply xq_In_Qmem. exact Hz. }
  rewrite Hd in Hm.
  destruct (fst (Qmem_cons z a nil) Hm) as [Hm1 | Hm1].
  - assert (E : Qeq_bool z a = true)
      by (destruct (id_sym Hm1); reflexivity).
    apply qeq_imp_qeqT. apply Qeq_bool_eq. exact E.
  - simpl in Hm1. inversion Hm1.
Qed.

Theorem H_ms1_Hshannon0 : forall l : list Q,
  (H_ms l == 1)%Q -> QeqT (H_devsum l) 0.
Proof.
  intro l. unfold H_ms. intro H.
  assert (HI : Id (length (dedup l)) 1%nat)
    by (apply (xq_Zlen_inj1 (length (dedup l))); exact H).
  assert (Hlen : length (dedup l) = 1%nat)
    by (destruct (id_sym HI); reflexivity).
  destruct (xq_len1_el (dedup l) Hlen) as [b Hb].
  apply (H_shannon_q_const_zero b l).
  assert (Hbe : dedup l = [b]) by (destruct (id_sym Hb); reflexivity).
  apply Forall_forall. intros z Hz. apply qeqT_imp_qeq.
  apply (xq_dedup1_all_eq l b Hbe z Hz).
Qed.

(* 反向面为假：升序表 [1;2] 香农偏差为零但多重集熵 = 2 ≠ 1 *)
Theorem Hshannon0_not_Hms1_counterex :
  And (QeqT (H_devsum [1; 2]) 0) (Not (QeqT (H_ms [1; 2]) 1)).
Proof.
  split.
  - apply qeq_imp_qeqT. vm_compute. reflexivity.
  - intro Hc. apply (False_rect Empty_set). apply qeqT_imp_qeq in Hc.
    unfold H_ms in Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* ---------- 相干性 2c：mkMEval 构造后投影往返（eta 面） ---------- *)

Theorem mkMEval_eta : forall (l ctx : list Q),
  And (Id (me_carrier (mkMEval l ctx)) l)
  (And (QeqT (me_Hadj (mkMEval l ctx)) (H_adj l))
  (And (QeqT (me_Hms (mkMEval l ctx)) (H_ms l))
  (And (QeqT (me_Hsh (mkMEval l ctx)) (H_devsum l))
       (QeqT (me_Hcond (mkMEval l ctx)) (H_cond l ctx))))).
Proof.
  intros l ctx. repeat split.
  - apply qeq_imp_qeqT. unfold Qeq. simpl. reflexivity.
  - apply qeq_imp_qeqT. unfold Qeq. simpl. reflexivity.
  - apply qeq_imp_qeqT. unfold Qeq. simpl. reflexivity.
  - apply qeq_imp_qeqT. unfold Qeq. simpl. reflexivity.
Qed.

Theorem mkMEval_Hms1_Hsh0 : forall (l ctx : list Q),
  (me_Hms (mkMEval l ctx) == 1)%Q -> QeqT (me_Hsh (mkMEval l ctx)) (0).
Proof.
  intros l ctx H. apply qeq_imp_qeqT. unfold mkMEval in H. simpl in H.
  unfold mkMEval. simpl. exact (qeqT_imp_qeq _ _ (H_ms1_Hshannon0 l H)).
Qed.

(* ---------- 端点 3：H_lam 的 λ=1 / λ=0 退化 ---------- *)

Theorem H_lam_lam1 : forall (l : list Q) (s : nat),
  QeqT (H_lam l s 1) (H_adj (P0 l)).
Proof.
  intros l s. apply qeq_imp_qeqT. unfold H_lam.
  replace (1 - 1)%Q with 0%Q by reflexivity.
  ring.
Qed.

Theorem H_lam_lam0 : forall (l : list Q) (s : nat),
  QeqT (H_lam l s 0) (H_adj (Pinf l s)).
Proof.
  intros l s. apply qeq_imp_qeqT. unfold H_lam.
  replace (1 - 0)%Q with 1%Q by reflexivity.
  ring.
Qed.

(* ---------- 门控 4：gate_low_entropy / phase_side 行为定理 ---------- *)

Theorem gate_low_entropy_spec : forall H threshold : Q,
  IffT (Id (gate_low_entropy H threshold) true) (QleT' H threshold).
Proof.
  intros H threshold. split.
  - intro E. apply Qle_to_QleT'.
    assert (Eb : Qle_bool H threshold = true)
      by (unfold gate_low_entropy in E; destruct (id_sym E); reflexivity).
    apply (proj1 (Qle_bool_iff H threshold)). exact Eb.
  - intro Hle. apply eq_imp_id. unfold gate_low_entropy.
    apply (proj2 (Qle_bool_iff H threshold)).
    apply (QleT'_to_Qle _ _ Hle).
Qed.

Theorem gate_low_entropy_false_le : forall H threshold : Q,
  gate_low_entropy H threshold = false -> QleT' threshold H.
Proof.
  intros H threshold Hfalse.
  exact (Qle_bool_false_le _ _ Hfalse).
Qed.

Theorem gate_low_entropy_dec : forall H threshold : Q,
  Or (Id (gate_low_entropy H threshold) true)
     (Id (gate_low_entropy H threshold) false).
Proof.
  intros H threshold. unfold gate_low_entropy.
  destruct (Qle_bool H threshold).
  - left. apply eq_imp_id. reflexivity.
  - right. apply eq_imp_id. reflexivity.
Qed.

Theorem phase_side_spec : forall (l : list Q) (s : nat),
  IffT (Id (phase_side l s) 0%nat) (QleT' (H_adj (P0 l)) (H_adj (Pinf l s))).
Proof.
  intros l s. split.
  - intro E. assert (Eb : phase_side l s = 0%nat)
      by (destruct (id_sym E); reflexivity).
    unfold phase_side in Eb.
    destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))) eqn:Ex.
    + apply Qle_to_QleT'. apply (proj1 (Qle_bool_iff _ _)). exact Ex.
    + simpl in Eb. discriminate Eb.
  - intro Hle. apply eq_imp_id. unfold phase_side.
    destruct (id_sym (xq_Qle_bool_true _ _ (QleT'_to_Qle _ _ Hle))).
    reflexivity.
Qed.

Theorem phase_side_values : forall (l : list Q) (s : nat),
  Or (Id (phase_side l s) 0%nat) (Id (phase_side l s) 1%nat).
Proof.
  intros l s. unfold phase_side.
  destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))).
  - left. apply eq_imp_id. reflexivity.
  - right. apply eq_imp_id. reflexivity.
Qed.

(* ============================================================
   §A2 归并棒 S3：并入 DTPT_Entropy2.v —— 真频率香农熵
   H_freq 定理族（qn/freq_q/nsum/sqsum 自包含定义面 + 置换不变主定理
   H_freq_perm + 简并双向刻画）与数据处理不等式族（M3 归并版 §7-§12
   整体随行）。
   仅剥去独立文件的 Require/Import 头与 Module 壳行（stdlib 与 DTPT
   由本文件头统一承载）——并入后位于 Module DTPT_Entropy 内，其对
   DTPT 基础（qadd_le/qopp_le/Qle_0_sub' 等）的引用改同文件直引，
   语义零变；其中 qn_nonneg 使用的 qadd_nonneg 由 DTPT 份换绑为本
   文件既有的同陈述件（逐字恒等，零漂移）；注释与全部证明体、Qed 面、
   文尾 Print Assumptions 审计出口零改动逐字迁移（CRLF 归一）。
   ============================================================ *)

(* ============================================================
   DTPT_Entropy2.v — 真频率香农熵、置换不变定理族与数据处理不等式
                     （M3 归并版）
   ------------------------------------------------------------
   【职责】
   · 真频率香农熵（Q 域有理替代形）自包含定义面：qn（nat→Q 嵌入）、
     freq_q（Qeq_bool 判等频数）、nsum（泛求和）、sqsum（免 dedup
     碰撞和）、H_freq = 1 − Σ_v p_v² 及其定理族（置换不变
     H_freq_perm / 非负 / 简并双向刻画）。背景：旧 H_devsum 实为
     质心偏移和、置换不变性为假（反例见 DTPT_Entropy.v），本件为
     其诚实替代——H_freq ∈ [0,1)，全同值/length≤1 取 0。
   · 数据处理不等式族（M3 并入段 §7-§12）：粗粒化观测 map f 不增熵
     ——计数形 freq_q_map、逐点支配 freq_q_map_ge（Qeq 形态假设
     进场）、碰撞和单调 sqsum_map_ge、补形反号 hfreq_core_anti、
     主定理 H_freq_dpi、端点双例与迭代不衰减链。
   【依赖】stdlib（QArith / Qabs / List / Arith / Lia / Permutation）
     + 基础 DTPT（qopp_le / Qeq 环境等）。无其它外部依赖。
   【归并记录】M3：U17 件「H_freq 数据处理不等式」件
     整体并入本文件尾（其对本文件的 Require 行随之删除，变同文件
     直引，对 DTPT 的 Require 保留）；撞名预检 15 个并入顶层名
     全 0 撞（dpi_ 系命名天然区分，未加前缀）；全工作区无下游
     Require 该退役件，源已删、.retired_M3 快照留存；拓扑无新增
     依赖。
   【认证】文尾审计 15 件 Print Assumptions 全 "Closed under the
     global context"（零公理）；.vo 于 M3 归并后重编全部通过。
   【纪律】Set 层零公理、零承认、零中途放弃，全程 Qed 闭合；
     nat 全显式 %nat；仅 Require DTPT 与 stdlib，禁 Require 外部件。
   ============================================================ *)

(* ========== §1 qn：nat → Q 嵌入（自包含，免 Z.of_nat 依赖面） ========== *)

Fixpoint qn (n : nat) : Q :=
  match n with
  | O => 0%Q
  | S k => (1 + qn k)%Q
  end.

Lemma qn_nonneg : forall n : nat, QleT' (0) (qn n).
Proof.
  intro n. induction n as [| k IH]; apply Qle_to_QleT'.
  - apply Qle_refl.
  - simpl. apply QleT'_to_Qle. apply qadd_nonneg.
    + apply (Qlt_le_weak 0 1). reflexivity.
    + apply QleT'_to_Qle. exact IH.
Qed.

Lemma qn_S_pos : forall k : nat, QltT (0) (qn (S k)).
Proof.
  intros k. apply Qlt_to_QltT. simpl. apply (Qlt_le_trans 0 1 (1 + qn k)%Q).
  - reflexivity.
  - pose proof (qadd_le 1 1 0 (qn k) (Qle_refl 1)
      (QleT'_to_Qle _ _ (qn_nonneg k))) as HH.
    simpl in HH. exact (QleT'_to_Qle _ _ HH).
Qed.

Lemma qn_pos : forall n : nat, (0 < n)%nat -> QltT (0) (qn n).
Proof.
  intros n Hn. apply Qlt_to_QltT. destruct n as [| m].
  - exfalso. lia.
  - apply QltT_to_Qlt. apply qn_S_pos.
Qed.

Lemma qn_add : forall a b : nat, QeqT (qn (a + b)%nat) (qn a + qn b).
Proof.
  intros a. induction a as [| a IH]; intros b; apply qeq_imp_qeqT.
  - rewrite Nat.add_0_l. cbn [qn]. rewrite Qplus_0_l. reflexivity.
  - cbn [qn Nat.add]. rewrite (qeqT_imp_qeq _ _ (IH b)). ring.
Qed.

Lemma qn_mul : forall a b : nat, QeqT (qn (a * b)%nat) (qn a * qn b).
Proof.
  intros a. induction a as [| a IH]; intros b; apply qeq_imp_qeqT.
  - simpl. symmetry. apply Qmult_0_l.
  - simpl. rewrite (qeqT_imp_qeq _ _ (qn_add b (a * b))).
    rewrite (qeqT_imp_qeq _ _ (IH b)). ring.
Qed.

Lemma qn_le : forall a b : nat, (a <= b)%nat -> QleT' (qn a) (qn b).
Proof.
  intros a. induction a as [| a IH]; intros b Hle; apply Qle_to_QleT'.
  - apply QleT'_to_Qle. apply qn_nonneg.
  - destruct b as [| b'].
    + exfalso. lia.
    + simpl. apply QleT'_to_Qle. apply (qadd_le 1 1 (qn a) (qn b')).
      * apply Qle_refl.
      * apply QleT'_to_Qle. apply IH. apply (le_S_n _ _ Hle).
Qed.

Lemma qn_inj : forall a b : nat, qn a == qn b -> Id (a) (b).
Proof.
  intros a. induction a as [| a IH]; intros b Heq; apply eq_imp_id.
  - destruct b as [| b'].
    + reflexivity.
    + simpl in Heq. pose proof (qn_S_pos b') as HP. simpl in HP.
      apply QltT_to_Qlt in HP. rewrite <- Heq in HP.
      exfalso. exact (Qlt_irrefl 0 HP).
  - destruct b as [| b'].
    + simpl in Heq. pose proof (qn_S_pos a) as HP. simpl in HP.
      apply QltT_to_Qlt in HP. rewrite Heq in HP.
      exfalso. exact (Qlt_irrefl 0 HP).
    + simpl in Heq.
      rewrite (Qplus_comm 1 (qn a)) in Heq.
      rewrite (Qplus_comm 1 (qn b')) in Heq.
      pose proof (proj1 (Qplus_inj_r (qn a) (qn b') 1) Heq) as H'.
      pose proof (IH b' H') as Hab. destruct (id_sym Hab). reflexivity.
Qed.

(* ========== §2 Q 除法/减号工具（Qminus 先展开再 ring；零除法前提漏洞） ========== *)

Lemma qlt_neq0 : forall y : Q, 0 < y -> y <> 0.
Proof.
  intros y Hpy Heq. rewrite Heq in Hpy. exact (Qlt_irrefl 0 Hpy).
Qed.

Lemma qpos_neq0 : forall y : Q, 0 < y -> Not (QeqT y 0).
Proof.
  intros y Hpy Heq. apply qeqT_imp_qeq in Heq.
  apply (False_rect Empty_set). apply (Qlt_not_eq 0 y Hpy).
  apply (Qeq_sym y 0). exact Heq.
Qed.

(* 本平台 9.0 stdlib 的 Qmult_inv_r 是 x * /x == 1 形而非消去形，
   自建消去引理（field 的除法侧条件恰为 Qeq 形 ~ (B == 0)） *)
Lemma qmult_inv_cancel_r : forall A B : Q, ~ (B == 0) -> QeqT (A * / B * B) (A).
Proof.
  intros A B HB. apply qeq_imp_qeqT. field. exact HB.
Qed.

Lemma qsub_eq0 : forall a b : Q, a - b == 0 -> QeqT (a) (b).
Proof.
  intros a b H.
  apply qeq_imp_qeqT.
  assert (Ha : a == (a - b) + b).
  { unfold Qminus. ring. }
  rewrite H in Ha. rewrite Qplus_0_l in Ha. exact Ha.
Qed.

(* 分子为零（含零分母的平凡情形）则商为零：0/0 == 0 亦被覆盖 *)
Lemma qdiv_zero_num : forall A B : Q, A == 0 -> QeqT (A / B) (0).
Proof.
  intros A B H. apply qeq_imp_qeqT. unfold Qdiv. rewrite H. apply Qmult_0_l.
Qed.

Lemma qdiv_eq0_num : forall A B : Q, 0 < B -> A / B == 0 -> QeqT A 0.
Proof.
  intros A B HB H. apply qeq_imp_qeqT. unfold Qdiv in H.
  assert (HBne : ~ (B == 0)).
  { intro Hb. destruct (qpos_neq0 B HB (qeq_imp_qeqT _ _ Hb)). }
  pose proof (qeqT_imp_qeq _ _ (qmult_inv_cancel_r A B HBne)) as Hcancel.
  rewrite H in Hcancel. rewrite Qmult_0_l in Hcancel.
  apply (Qeq_sym 0 A). exact Hcancel.
Qed.

Lemma qdiv_nonneg : forall A B : Q, 0 <= A -> 0 < B -> QleT' (0) (A / B).
Proof.
  intros A B HA HB. apply Qle_to_QleT'. unfold Qdiv. apply Qmult_le_0_compat.
  - exact HA.
  - apply Qlt_le_weak. apply (Qinv_lt_0_compat B HB).
Qed.

Lemma qnum_zero : forall n s : nat, qn (n * n) == qn s -> QeqT (qn n * qn n - qn s) (0).
Proof.
  intros n s H. apply qeq_imp_qeqT.
  rewrite <- (qeqT_imp_qeq _ _ (qn_mul n n)). rewrite <- H.
  unfold Qminus. apply Qplus_opp_r.
Qed.

Lemma qeqb_false_neq : forall x y : Q, Qeq_bool x y = false -> x <> y.
Proof.
  intros x y H Hxy.
  assert (Ht : Qeq_bool x y = true).
  { apply (proj2 (Qeq_bool_iff x y)). rewrite <- Hxy. apply Qeq_refl. }
  rewrite Ht in H. discriminate H.
Qed.

(* ========== §3 freq_q：自包含频数计数（Qeq_bool 判等） ========== *)

Fixpoint freq_q (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (freq_q x ys) else freq_q x ys
  end.

Lemma freq_q_le_length : forall (x : Q) (l : list Q), NatLe (freq_q x l) ((length l)%nat).
Proof.
  intros x l. apply NatLe_lift. induction l as [| y ys IH]; simpl.
  - lia.
  - simpl. destruct (Qeq_bool x y); lia.
Qed.

(* 保底件：拼接频数可加 *)
Theorem freq_q_app : forall (x : Q) (l p : list Q), Id (freq_q x (l ++ p)) ((freq_q x l + freq_q x p)%nat).
Proof.
  intros x l p. apply eq_imp_id. induction l as [| a l IH].
  - reflexivity.
  - simpl. destruct (Qeq_bool x a); rewrite IH; lia.
Qed.

(* 主定理前置：频数置换不变（对 Permutation 构造子归纳；perm_swap
   分支因计数同一 x0 而只需四分支字面重排，无需 Qeq_bool 对称性） *)
Theorem freq_q_perm : forall (x : Q) (l p : list Q),
  Permutation l p -> Id (freq_q x l) (freq_q x p).
Proof.
  intros x l p H.
  apply eq_imp_id.
  induction H as [ | y l' p' Hy IH | y z l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. destruct (Qeq_bool x y); rewrite IH; reflexivity.
  - simpl. destruct (Qeq_bool x y); destruct (Qeq_bool x z); reflexivity.
  - rewrite IH1. exact IH2.
Qed.

Lemma freq_q_eq_all : forall (x : Q) (l : list Q),
  (forall z, In z l -> z == x) -> Id (freq_q x l) (length l).
Proof.
  intros x l. induction l as [| y ys IH]; intros H; apply eq_imp_id.
  - reflexivity.
  - assert (Hy : Qeq_bool x y = true).
    { apply (proj2 (Qeq_bool_iff x y)). apply (Qeq_sym y x). apply H.
      left. reflexivity. }
    simpl. rewrite Hy. f_equal.
    destruct (id_sym (IH (fun z Hz => H z (or_intror Hz)))). reflexivity.
Qed.

Lemma freq_q_full_count : forall (x : Q) (l : list Q),
  freq_q x l = length l -> forall y, In y l -> QeqT (y) (x).
Proof.
  intros x l. induction l as [| a l IH]; intros Hcnt y0 Hy0.
  - destruct Hy0.
  - apply qeq_imp_qeqT. destruct Hy0 as [Hy0 | Hy0].
    + subst y0. destruct (Qeq_bool x a) eqn:Hyb.
      * apply (Qeq_sym x a). apply (proj1 (Qeq_bool_iff x a)). exact Hyb.
      * exfalso. simpl in Hcnt. rewrite Hyb in Hcnt.
        pose proof (NatLe_drop _ _ (freq_q_le_length x l)) as HL. lia.
    + apply qeqT_imp_qeq. apply IH.
      * destruct (Qeq_bool x a) eqn:Hyb.
        -- simpl in Hcnt. rewrite Hyb in Hcnt. lia.
        -- exfalso. simpl in Hcnt. rewrite Hyb in Hcnt.
           pose proof (NatLe_drop _ _ (freq_q_le_length x l)) as HL. lia.
      * exact Hy0.
Qed.

(* ========== §4 nsum：Q 索引 nat 泛求和 ========== *)

Fixpoint nsum (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => (f y + nsum f ys)%nat
  end.

Lemma nsum_ext_in : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> f x = g x) -> Id (nsum f l) (nsum g l).
Proof.
  intros f g l. induction l as [| y ys IH]; simpl; intros H; apply eq_imp_id.
  - reflexivity.
  - rewrite (H y (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

Lemma nsum_perm : forall (f : Q -> nat) (l p : list Q),
  Permutation l p -> Id (nsum f l) (nsum f p).
Proof.
  intros f l p H.
  apply eq_imp_id.
  induction H as [ | x l' p' Hx IH | x y l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. lia.
  - rewrite IH1. exact IH2.
Qed.

Lemma nsum_const : forall (n : nat) (l : list Q), Id (nsum (fun _ => n) l) ((length l * n)%nat).
Proof.
  intros n l. apply eq_imp_id. induction l as [| y ys IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma nsum_bound : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) -> NatLe (nsum f l) ((length l * B)%nat).
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (Hy : (f y <= B)%nat) by (apply H; left; reflexivity).
    assert (Hys : NatLe (nsum f ys) (length ys * B))
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ Hys). lia.
Qed.

Lemma nsum_bound_eq : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) ->
  nsum f l = (length l * B)%nat ->
  forall x, In x l -> Id (f x) (B).
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros Hsat Heq x0 Hx0;
    apply eq_imp_id.
  - destruct Hx0.
  - assert (Hy : (f y <= B)%nat) by (apply Hsat; left; reflexivity).
    assert (Hys : NatLe (nsum f ys) (length ys * B))
      by (apply (nsum_bound f ys B); intros x Hx; apply Hsat; right; exact Hx).
    pose proof (NatLe_drop _ _ Hys) as HysL.
    assert (Hfy : f y = B) by lia.
    assert (HysEq : nsum f ys = (length ys * B)%nat) by lia.
    destruct Hx0 as [Hx0 | Hx0].
    + subst x0. exact Hfy.
    + destruct (id_sym (IH (fun z Hz => Hsat z (or_intror Hz)) HysEq x0 Hx0)).
      reflexivity.
Qed.

(* ========== §5 sqsum：Σ_{x∈l} freq_q x l = Σ_v c_v²（免 dedup） ========== *)

Definition sqsum (l : list Q) : nat := nsum (fun x => freq_q x l) l.

Definition all_same (l : list Q) : Set :=
  forall a b, In a l -> In b l -> QeqT a b.

Theorem sqsum_perm : forall l p : list Q,
  Permutation l p -> Id (sqsum l) (sqsum p).
Proof.
  intros l p H. unfold sqsum.
  assert (Hex : forall x, In x l -> freq_q x l = freq_q x p).
  { intros x _. destruct (freq_q_perm x l p H). reflexivity. }
  destruct (id_sym (nsum_ext_in (fun x => freq_q x l) (fun x => freq_q x p) l Hex)).
  exact (nsum_perm (fun x => freq_q x p) l p H).
Qed.

Lemma sqsum_le : forall l : list Q, NatLe (sqsum l) ((length l * length l)%nat).
Proof.
  intros l. unfold sqsum.
  apply (nsum_bound (fun x => freq_q x l) l (length l)).
  intros x _. apply NatLe_drop. apply freq_q_le_length.
Qed.

Lemma freq_q_all_same : forall (x : Q) (l : list Q),
  In x l -> all_same l -> Id (freq_q x l) (length l).
Proof.
  intros x l Hin Hs. apply freq_q_eq_all. intros z Hz.
  unfold all_same in Hs. apply qeqT_imp_qeq. apply Hs.
  - exact Hz.
  - exact Hin.
Qed.

Lemma sqsum_all_same : forall l : list Q,
  all_same l -> Id (sqsum l) ((length l * length l)%nat).
Proof.
  intros l Hs. unfold sqsum.
  assert (Hex : forall x, In x l -> freq_q x l = length l).
  { intros x Hx. destruct (id_sym (freq_q_all_same x l Hx Hs)). reflexivity. }
  destruct (id_sym (nsum_ext_in (fun x => freq_q x l)
              (fun _ : Q => length l) l Hex)).
  apply nsum_const.
Qed.

Lemma sqsum_eq_all_same : forall l : list Q,
  sqsum l = (length l * length l)%nat -> all_same l.
Proof.
  intros l Heq. destruct l as [| x xs].
  - intros a b Ha Hb. destruct Ha.
  - unfold sqsum in Heq.
    pose proof (nsum_bound_eq (fun x0 => freq_q x0 (x :: xs)) (x :: xs)
                  (length (x :: xs))
                  (fun x0 _ => NatLe_drop _ _ (freq_q_le_length x0 (x :: xs)))
                  Heq x (or_introl eq_refl)) as Hfx.
    assert (HfxE : freq_q x (x :: xs) = length (x :: xs))
      by (destruct Hfx; reflexivity).
    pose proof (freq_q_full_count x (x :: xs) HfxE) as Hall.
    intros a b Ha Hb. apply qeq_imp_qeqT. apply (Qeq_trans a x b).
    + apply qeqT_imp_qeq. apply Hall. exact Ha.
    + apply (Qeq_sym b x). apply qeqT_imp_qeq. apply Hall. exact Hb.
Qed.

(* ========== §6 H_freq：真频率香农熵的有理替代形与主定理定理 ========== *)

(* H_freq l = 1 − Σ_v p_v² = (n² − Σ_v c_v²)/n²（Q 域；n=0 时取 0） *)
Definition H_freq (l : list Q) : Q :=
  (qn (length l) * qn (length l) - qn (sqsum l))
    / (qn (length l) * qn (length l)).

(* 【主定理】置换不变——旧 H_devsum 因质心偏移形而造不出的定理 *)
Theorem H_freq_perm : forall l p : list Q,
  Permutation l p -> QeqT (H_freq l) (H_freq p).
Proof.
  intros l p Hp. apply qeq_imp_qeqT. unfold H_freq.
  destruct (id_sym (sqsum_perm l p Hp)).
  rewrite (Permutation_length Hp).
  reflexivity.
Qed.

(* 非负（按所选形：n² ≥ Σc_v² 且除正保号；空表分子分母同零取 0） *)
Theorem H_freq_nonneg : forall l : list Q, QleT' (0) (H_freq l).
Proof.
  intros l. apply Qle_to_QleT'. destruct l as [| x xs].
  - assert (Hz : H_freq [] == 0).
    { unfold H_freq. apply qeqT_imp_qeq. apply qdiv_zero_num.
      apply qeqT_imp_qeq. apply qnum_zero. reflexivity. }
    rewrite Hz. apply Qle_refl.
  - unfold H_freq. apply QleT'_to_Qle. apply qdiv_nonneg.
    + apply QleT'_to_Qle. apply (fst (Qle_0_sub' (qn (sqsum (x :: xs)))
                 (qn (length (x :: xs)) * qn (length (x :: xs))))).
      apply Qle_to_QleT'.
      rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs)) (length (x :: xs)))).
      apply QleT'_to_Qle. apply qn_le. apply NatLe_drop. apply sqsum_le.
    + rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs)) (length (x :: xs)))).
      apply QltT_to_Qlt. apply qn_pos. simpl. apply Nat.lt_0_succ.
Qed.

(* 简并刻画（正向）：全同值面 ⟹ H_freq 取 0 *)
Theorem H_freq_all_same_zero : forall l : list Q,
  all_same l -> QeqT (H_freq l) (0).
Proof.
  intros l Hs. apply qeq_imp_qeqT. unfold H_freq.
  apply qeqT_imp_qeq. apply qdiv_zero_num.
  apply qeqT_imp_qeq. apply qnum_zero.
  destruct (id_sym (sqsum_all_same l Hs)). reflexivity.
Qed.

Theorem H_freq_len_le_1 : forall l : list Q,
  (length l <= 1)%nat -> QeqT (H_freq l) (0).
Proof.
  intros l Hl. destruct l as [| x xs].
  - apply H_freq_all_same_zero. intros a b Ha Hb. destruct Ha.
  - simpl in Hl. destruct xs as [| y ys].
    + apply H_freq_all_same_zero. intros a b Ha Hb.
      destruct (Qeq_bool a x) eqn:Ea.
      * apply qeq_imp_qeqT. apply (Qeq_trans a x b).
        -- apply (proj1 (Qeq_bool_iff a x)). exact Ea.
        -- destruct (Qeq_bool b x) eqn:Eb.
           ++ apply (Qeq_sym b x). apply (proj1 (Qeq_bool_iff b x)). exact Eb.
           ++ exfalso. destruct Hb as [Hb | Hb].
              ** rewrite <- Hb in Eb. rewrite Qeq_bool_refl in Eb.
                 discriminate Eb.
              ** exact Hb.
      * exfalso. destruct Ha as [Ha | Ha].
        -- rewrite <- Ha in Ea. rewrite Qeq_bool_refl in Ea. discriminate Ea.
        -- exact Ha.
    + simpl in Hl. exfalso. lia.
Qed.

(* 简并刻画（反向）：H_freq 取 0 ⟹ 全同值面（双向闭合） *)
Theorem H_freq_eq0_all_same : forall l : list Q,
  H_freq l == 0 -> all_same l.
Proof.
  intros l Heq. unfold H_freq in Heq. destruct l as [| x xs].
  - intros a b Ha Hb. destruct Ha.
  - assert (HB : 0 < qn (length (x :: xs)) * qn (length (x :: xs))).
    { rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs))
                     (length (x :: xs)))).
      apply QltT_to_Qlt. apply qn_pos. simpl. apply Nat.lt_0_succ. }
    assert (Hnum : qn (length (x :: xs)) * qn (length (x :: xs))
                   - qn (sqsum (x :: xs)) == 0)
      by (apply (qeqT_imp_qeq _ _ (qdiv_eq0_num _ _ HB Heq))).
    pose proof (qeqT_imp_qeq _ _
      (qsub_eq0 (qn (length (x :: xs)) * qn (length (x :: xs)))
                  (qn (sqsum (x :: xs))) Hnum)) as Hab.
    rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs))
                     (length (x :: xs)))) in Hab.
    pose proof (qn_inj (length (x :: xs) * length (x :: xs))
                  (sqsum (x :: xs)) Hab) as Heqnat.
    assert (HeqnatE : sqsum (x :: xs)
                      = (length (x :: xs) * length (x :: xs))%nat)
      by (destruct Heqnat; reflexivity).
    apply sqsum_eq_all_same. exact HeqnatE.
Qed.

(* ############################################################
   M3 归并段【U17 件 · H_freq 数据处理不等式族】（§7-§12）
   原独立文件整体并入：内容零改动，仅删其 Require 行（变同文件
   直引）、节号顺延 §7-§12、审计并档文尾。
   ############################################################ *)

(* ========== §7 列表/求和迁移工具 ========== *)

(* map 保长（stdlib 9.0 length_map 改名风险规避，自建） *)
Lemma length_map_self : forall (f : Q -> Q) (l : list Q), Id (length (map f l)) (length l).
Proof.
  intros f l. induction l as [| a l IH]; simpl; apply eq_imp_id.
  - reflexivity.
  - destruct (id_sym IH). reflexivity.
Qed.

(* 泛求和逐点单调 *)
Lemma nsum_le : forall (g h : Q -> nat) (l : list Q),
  (forall x, In x l -> (g x <= h x)%nat) -> NatLe (nsum g l) ((nsum h l)%nat).
Proof.
  intros g h l. induction l as [| a l IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (H1 : (g a <= h a)%nat) by (apply H; left; reflexivity).
    assert (H2 : NatLe (nsum g l) (nsum h l))
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ H2). lia.
Qed.

(* 求和过 map = 复合求和（nsum 与 map 的交换桥） *)
Lemma nsum_map : forall (g : Q -> nat) (f : Q -> Q) (l : list Q), Id (nsum g (map f l)) (nsum (fun x => g (f x)) l).
Proof.
  intros g f l. induction l as [| a l IH]; simpl; apply eq_imp_id.
  - reflexivity.
  - destruct (id_sym IH). reflexivity.
Qed.

(* ========== §8 保底件：推前计数引理与逐点支配 ========== *)

(* 【保底件·推前引理·计数形】map 后 y 的频数 = 原表中命中 f x == y 的票数
*)
Theorem freq_q_map : forall (f : Q -> Q) (y : Q) (l : list Q), Id (freq_q y (map f l)) (nsum (fun x : Q => if Qeq_bool y (f x) then 1%nat else 0%nat) l).
Proof.
  intros f y l. induction l as [| a l IH]; simpl; apply eq_imp_id.
  - reflexivity.
  - destruct (Qeq_bool y (f a)); destruct (id_sym IH); reflexivity.
Qed.

(* 【Qeq 形态桥】逐点支配：x 在原表中的票数 <= f x 在像表中的票数。
   真票（x == a）在 f 作用下仍命中（形态假设保命中），且像表可能
   额外并票（他值同像），故只增不减——这是 DPI 的微观机理。 *)
Lemma freq_q_map_ge : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall (x : Q) (l : list Q), NatLe (freq_q x l) ((freq_q (f x) (map f l))%nat).
Proof.
  intros f Hf x l. induction l as [| a l IH]; simpl; apply NatLe_lift.
  - lia.
  - pose proof (NatLe_drop _ _ IH) as IHL.
    destruct (Qeq_bool x a) eqn:H1.
    + assert (H2 : Qeq_bool (f x) (f a) = true).
      { apply (proj2 (Qeq_bool_iff (f x) (f a))). apply Hf.
        apply (proj1 (Qeq_bool_iff x a)). exact H1. }
      rewrite H2. lia.
    + destruct (Qeq_bool (f x) (f a)); lia.
Qed.

(* 【质量合并单调】碰撞和面：sqsum (map f l) >= sqsum l。
   求和过 map（nsum_map）+ 逐点支配（freq_q_map_ge）两步归堆。 *)
Theorem sqsum_map_ge : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall l : list Q, NatLe (sqsum l) ((sqsum (map f l))%nat).
Proof.
  intros f Hf l. unfold sqsum.
  destruct (id_sym (nsum_map (fun y => freq_q y (map f l)) f l)).
  apply nsum_le. intros x _. apply NatLe_drop. apply freq_q_map_ge. exact Hf.
Qed.

(* ========== §9 Q 除法/减号单调工具（DPI 的补形反号机件） ========== *)

(* 同分母商的减法分配（Qminus、Qdiv 先 unfold 再 ring，Qinv 为原子） *)
Lemma qdiv_sub_distr : forall A B D : Q, QeqT (A / D - B / D) ((A - B) / D).
Proof.
  intros A B D. apply qeq_imp_qeqT. unfold Qminus, Qdiv. ring.
Qed.

(* 减法右单调：A <= B 则 D - B <= D - A（补形单调反号的内核） *)
Lemma qsub_mono_r : forall D A B : Q, A <= B -> QleT' (D - B) (D - A).
Proof.
  intros D A B H. apply Qle_to_QleT'. unfold Qminus.
  apply QleT'_to_Qle. apply (qadd_le D D (- B) (- A)).
  - apply Qle_refl.
  - apply QleT'_to_Qle. apply qopp_le. exact H.
Qed.

(* 核形：N >= 1 时碰撞和在 [0, N²] 内单调反号穿过补形商。
   （qdiv_sub_distr 把商之差归并为单商，qdiv_nonneg 保号；
   N = 0 时 A = B = 0 两侧字面相同。） *)
Lemma hfreq_core_anti : forall (N A B : nat), (A <= B)%nat -> (B <= N * N)%nat -> QleT' ((qn N * qn N - qn B) / (qn N * qn N)) ((qn N * qn N - qn A) / (qn N * qn N)).
Proof.
  intros N A B HAB HBN.
  apply Qle_to_QleT'.
  destruct N as [| m].
  - assert (HA : A = 0%nat) by lia.
    assert (HB : B = 0%nat) by lia.
    subst. apply Qle_refl.
  - assert (HD : 0 < qn (S m) * qn (S m)).
    { rewrite <- (qeqT_imp_qeq _ _ (qn_mul (S m) (S m))).
      apply QltT_to_Qlt. apply qn_pos. simpl. apply Nat.lt_0_succ. }
    pose proof (qpos_neq0 (qn (S m) * qn (S m)) HD) as HDneq.
    apply QleT'_to_Qle. apply (snd (Qle_0_sub'
              ((qn (S m) * qn (S m) - qn B) / (qn (S m) * qn (S m)))
              ((qn (S m) * qn (S m) - qn A) / (qn (S m) * qn (S m))))).
    apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ (qdiv_sub_distr (qn (S m) * qn (S m) - qn A)
                            (qn (S m) * qn (S m) - qn B)
                            (qn (S m) * qn (S m)))).
    apply QleT'_to_Qle. apply qdiv_nonneg.
    + apply QleT'_to_Qle. apply (fst (Qle_0_sub' (qn (S m) * qn (S m) - qn B)
                               (qn (S m) * qn (S m) - qn A))).
      apply qsub_mono_r. apply QleT'_to_Qle. apply qn_le. exact HAB.
    + exact HD.
Qed.

(* ========== §10 【主定理】数据处理不等式 DPI ========== *)

(* 观测（粗粒化合并质量）不增 H_freq：H_freq (map f l) <= H_freq l。
   形态假设 = 等价类合并语义的 Qeq 诚实守恒（对任意裸函数 f 该命题
   为假——裸函数可观测 Q 的 Record 表示，如取分子；反例
   l = [1/2; 2/4]，H_freq l = 0 而 H_freq (map (取分子) l) = 1/2。
   故主定理带形态假设 (forall x y : Q, x == y -> f x == f y)。 *)
Theorem H_freq_dpi : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall l : list Q, QleT' (H_freq (map f l)) (H_freq l).
Proof.
  intros f Hf l.
  apply Qle_to_QleT'.
  assert (Hlen : length (map f l) = length l)
    by (destruct (length_map_self f l); reflexivity).
  destruct l as [| x xs].
  - replace (map f (@nil Q)) with (@nil Q) by reflexivity.
    apply Qle_refl.
  - unfold H_freq. rewrite Hlen.
    apply QleT'_to_Qle. apply (hfreq_core_anti (length (x :: xs))
                           (sqsum (x :: xs)) (sqsum (map f (x :: xs)))).
    + apply NatLe_drop. apply sqsum_map_ge. exact Hf.
    + pose proof (sqsum_le (map f (x :: xs))) as Hs.
      rewrite Hlen in Hs. exact (NatLe_drop _ _ Hs).
Qed.

(* ========== §11 端点双例：DPI 两端的行为钉死 ========== *)

(* 端点一【恒等不衰减】：恒等映射（最细观测）零损耗——列表面
   Leibniz 相等直接桥接，无需形态假设。 *)
Theorem H_freq_map_id : forall l : list Q, QeqT (H_freq (map (fun x : Q => x) l)) (H_freq l).
Proof.
  intros l.
  apply qeq_imp_qeqT.
  assert (Hid : map (fun x : Q => x) l = l).
  { induction l as [| a l IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity. }
  rewrite Hid. apply Qeq_refl.
Qed.

(* 常数映射的像全同值（列表面 Leibniz） *)
Lemma in_map_const : forall (c : Q) (l : list Q) (a : Q),
  In a (map (fun _ : Q => c) l) -> QeqT (a) (c).
Proof.
  intros c l. induction l as [| b l IH]; simpl; intros a H; apply qeq_imp_qeqT.
  - destruct H.
  - destruct H as [H | H].
    + subst a. apply Qeq_refl.
    + apply qeqT_imp_qeq. apply IH. exact H.
Qed.

(* 端点二【常数全坍缩】：最粗观测（全部并成一桶）H_freq 取 0
   （简并面；对空表亦真，空表 H_freq 本为 0）。 *)
Theorem H_freq_map_const : forall (c : Q) (l : list Q), QeqT (H_freq (map (fun _ : Q => c) l)) (0).
Proof.
  intros c l. apply H_freq_all_same_zero.
  intros a b Ha Hb. apply qeq_imp_qeqT. apply (Qeq_trans a c b).
  - exact (qeqT_imp_qeq _ _ (in_map_const c l a Ha)).
  - apply (Qeq_sym b c). exact (qeqT_imp_qeq _ _ (in_map_const c l b Hb)).
Qed.

(* ========== §12 加分：迭代不衰减链 ========== *)

(* 两步复合直推：第二次观测仍不增（需 g 亦为形态） *)
Theorem H_freq_map_twice : forall (f g : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  (forall x y : Q, x == y -> g x == g y) ->
  forall l : list Q, QleT' (H_freq (map g (map f l))) (H_freq (map f l)).
Proof.
  intros f g Hf Hg l. apply (H_freq_dpi g Hg (map f l)).
Qed.

(* 链式：H_freq (map g (map f l)) <= H_freq (map f l) <= H_freq l *)
Theorem H_freq_map_chain : forall (f g : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  (forall x y : Q, x == y -> g x == g y) ->
  forall l : list Q, QleT' (H_freq (map g (map f l))) (H_freq l).
Proof.
  intros f g Hf Hg l.
  apply Qle_to_QleT'.
  apply (Qle_trans (H_freq (map g (map f l))) (H_freq (map f l)) (H_freq l)).
  - apply QleT'_to_Qle. apply (H_freq_dpi g Hg (map f l)).
  - apply QleT'_to_Qle. apply (H_freq_dpi f Hf l).
Qed.

(* ============================================================
   §A3 归并棒 S3：并入 DTPT_EntFam2.v —— 多熵族缺位
   三成员（collide/maxfreq/H_min_q·H_max_q）+ Rényi 阶梯序链主定理
   H_chain + H_freq 相干桥与置换不变收尾。
   仅剥去独立文件的 Require/Import 头与 Module 壳行；原对
   DTPT_Entropy2 的 Require 随并入变同文件直引（§A2 先行定位，
   引用面零改写），对 DTPT 基础引用经本文件头 Import 不变，语义
   零变；注释与全部证明体、Qed 面、文尾 Print Assumptions 审计
   出口零改动逐字迁移（CRLF 归一）。撞名预检：两源顶层名对宿主
   既有面 grep 全零命中（实测为准，纯追加零 uniquify）。
   ============================================================ *)

(* ============================================================
   DTPT_EntFam2.v — 多熵函数族缺位成员三件套（collide / maxfreq / H_min_q·H_max_q）
   职责：补多熵族缺位三成员的 Q 域有理代理面并证其序链——
         collide（Rényi 阶 2 碰撞熵内积面核 Σp_v²）、maxfreq（最大
         频率归一化，序链主定理）、H_max_q = 1 − maxfreq、H_min_q = 1 −
         collide（规格指定形）；Rényi 阶梯 1/n≤collide≤maxfreq≤1
         （非空 l，三成员一次入链）+ H_freq 相干桥 + 置换不变全套。
   依赖：QArith（QArith/Qabs）、List、Arith、Lia、Permutation、
         DTPT、DTPT_Entropy2。
   归并记录：无（原生成模块；件 DTPT-U9 新建件，禁碰既有件）。
   认证：零承认零公理；全树 coqchk EXIT=0。
   纪律：纯构造性；温控协议；Set 层零公理面、全程 Qed。
   附注：选形声明（详见 DTPT_EntFam2_升级报告_U9.md）——
         1. collide l = qn (sqsum l) / (qn n · qn n)，复用 S6 泛求和
            路线（sqsum 免 dedup、天然置换不变）；
         2. maxfreq l = qn (maxcount l) / qn n，空表取 0；
         3. 对照口径：−log max p 文献常记 H_min、−log Σp² 为 Rényi₂/
            碰撞熵；Q 域无 log，取「熵补 1−x」有理代理，与 −log x
            同为减函数 ⟹ 单调同向，序性质全部保真；命名遵规格，
            语义以「补形单调同向代理」自洽；
         4. 主定理序链 1/qn n <= collide l <= maxfreq l <= 1
            （Σp² >= 1/n 即 Cauchy-Schwarz 离散形；Σp² <= max p · Σ p
            经典不等式的 nat 层归纳实现，nat 侧闭合后 Q 层除法桥接）；
         5. H_freq l == 1 − collide l（非空 l；S6 件直推——H_freq 即
            1 − collide 的别名面）。
         原典对照（数字全域—熵相三元论·基座）：L22 裁决表·熵行
         「采用多熵函数族 ℋ，不强行选单一熵」；L148-152 成员清单
         H_alg/H_Sh/H_vN/H_str + 可扩展 H_Rényi/H_min/H_max/H_top/
         H_cond；盘面在册状态（B1 已证结论）：H_devsum（占位件）+
         H_cond + H_freq（S6，算半个 H_Rényi₂ 面）——九成员仅 2.5 个
         在册，本件补三成员。语义面：collide/maxfreq ∈ [1/n, 1]
         （非空）、空表取 0；H_max_q/H_min_q ∈ [0, 1]；全同值面
         maxfreq 取 1（熵补取 0）；置换不变全套。
   ============================================================ *)

(* ========== §1 Q 序/除法工具（stdlib 形变自建层） ========== *)

(* Qeq 可直接改写进 Qle 目标（S6 已实证） *)
Lemma qeq_le_l : forall x y : Q, x == y -> QleT' (x) (y).
Proof.
  intros x y H. apply Qle_to_QleT'. rewrite H. apply Qle_refl.
Qed.

(* qn n >= 1（n >= 1；经 qadd_le，S6 qn_S_pos 同款配方） *)
Lemma qn_ge1 : forall n : nat, (1 <= n)%nat -> QleT' (1:Q) (qn n).
Proof.
  intros n Hn. apply Qle_to_QleT'. destruct n as [| k].
  - exfalso. lia.
  - simpl.
    pose proof (qadd_le 1 1 0 (qn k) (Qle_refl 1)
      (QleT'_to_Qle _ _ (qn_nonneg k))) as HH.
    simpl in HH. exact (QleT'_to_Qle _ _ HH).
Qed.

(* qn 乘积正性（nat 侧非负乘法 + qn 单调，绕开 stdlib 严格乘法名赌博） *)
Lemma qn_mul_pos : forall a b : nat, (0 < a)%nat -> (0 < b)%nat -> QltT (0) (qn a * qn b).
Proof.
  intros a b Ha Hb.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans 0 (qn a) (qn a * qn b)).
  - apply QltT_to_Qlt. apply qn_pos. exact Ha.
  - assert (Hab : (a <= a * b)%nat).
    { apply (Nat.le_trans a (a * 1) (a * b)).
      - lia.
      - apply Nat.mul_le_mono_l. lia. }
    rewrite <- (qeqT_imp_qeq _ _ (qn_mul a b)).
    apply QleT'_to_Qle. apply qn_le. exact Hab.
Qed.

(* 非空表长度正性（纯 nat 侧，simpl 只在 nat 目标上做——Q 目标 simpl
   会把 Qlt 展成 Qnum/Qden 编码形致 apply 失配） *)
Lemma qlen_pos : forall (x : Q) (l : list Q), NatLe 1 (length (x :: l)).
Proof.
  intros x l. apply NatLe_lift.
  change (length (x :: l)) with (S (length l)). lia.
Qed.

(* 非空表长度嵌入的乘积正性（序链 Q 侧统一入口） *)
Lemma qlen_mul_pos : forall (x : Q) (l : list Q), QltT (0) (qn (length (x :: l)) * qn (length (x :: l))).
Proof.
  intros x l. apply qn_mul_pos;
    [ apply NatLe_drop, qlen_pos | apply NatLe_drop, qlen_pos ].
Qed.

(* 同分母除法对分子单调（分母为正；Qmult_le_compat_r 带非负前提，
   逆元正性经 Qinv_lt_0_compat——本 9.0 stdlib 无 Qmult_le_compat_l） *)
Lemma qdiv_ge_num : forall A C B : Q, 0 < B -> C <= A -> QleT' (C / B) (A / B).
Proof.
  intros A C B HB Hle. apply Qle_to_QleT'. unfold Qdiv.
  apply Qmult_le_compat_r.
  - exact Hle.
  - apply (Qlt_le_weak 0 (/ B)). apply (Qinv_lt_0_compat B HB).
Qed.

(* 分子不超分母则商不超 1（Qmult_inv_r 是乘出 1 的特化形，S6 卡在案） *)
Lemma qdiv_le_1 : forall A B : Q, A <= B -> 0 < B -> QleT' (A / B) (1).
Proof.
  intros A B Hle HB. apply Qle_to_QleT'. unfold Qdiv.
  assert (Hpos : 0 <= / B)
    by (apply (Qlt_le_weak 0 (/ B)); apply (Qinv_lt_0_compat B HB)).
  assert (Hm : A * / B <= B * / B) by (apply Qmult_le_compat_r; assumption).
  apply (Qle_trans (A * / B) (B * / B) 1 Hm).
  apply QleT'_to_Qle. apply qeq_le_l. apply Qmult_inv_r.
  intro Hc. assert (Hc2 : B == 0) by (rewrite Hc; reflexivity).
  destruct (qpos_neq0 B HB (qeq_imp_qeqT _ _ Hc2)).
Qed.

(* 归一化：1/P == P/(P·P)（field 除法侧条件为 Qeq 形，由上下文假设实例化消解） *)
Lemma qdiv_norm : forall P : Q, ~ (P == 0) -> ~ (P * P == 0) -> QeqT (1 / P) (P / (P * P)).
Proof.
  intros P HP1 HP2. apply qeq_imp_qeqT. field; assumption.
Qed.

(* 减法保序反变（z 固定；Qminus 先展开再 qadd_le，避开 apply 单化病） *)
Lemma qsub_le : forall x y z : Q, x <= y -> QleT' (z - y) (z - x).
Proof.
  intros x y z H. apply Qle_to_QleT'. unfold Qminus.
  apply QleT'_to_Qle. apply (qadd_le z z (- y) (- x)).
  - apply Qle_refl.
  - exact (Qopp_le_compat x y H).
Qed.

(* ========== §2 nmax：Q 索引 nat 泛取大（与 S6 nsum 同构） ========== *)

Fixpoint nmax (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => Nat.max (f y) (nmax f ys)
  end.

Lemma nmax_bound : forall (f : Q -> nat) (l : list Q) (y : Q),
  In y l -> NatLe (f y) ((nmax f l)%nat).
Proof.
  intros f l y Hy. revert Hy.
  induction l as [| z zs IH]; simpl; intros Hy; apply NatLe_lift.
  - destruct Hy.
  - destruct Hy as [Hz | Hy].
    + subst z. apply Nat.le_max_l.
    + apply (Nat.le_trans (f y) (nmax f zs) (Nat.max (f z) (nmax f zs))).
      * apply NatLe_drop. apply IH. exact Hy.
      * apply Nat.le_max_r.
Qed.

Lemma nmax_le_bound : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) -> NatLe (nmax f l) ((B)%nat).
Proof.
  intros f l B. induction l as [| z zs IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (Hz : (f z <= B)%nat) by (apply H; left; reflexivity).
    assert (Hzs : NatLe (nmax f zs) B)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ Hzs). lia.
Qed.

Lemma nmax_ext_in : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> f x = g x) -> Id (nmax f l) (nmax g l).
Proof.
  intros f g l. induction l as [| y ys IH]; simpl; intros H; apply eq_imp_id.
  - reflexivity.
  - rewrite (H y (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

(* 泛取大置换不变（perm_swap 分支 lia 收 Nat.max 交换） *)
Lemma nmax_perm : forall (f : Q -> nat) (l p : list Q),
  Permutation l p -> Id (nmax f l) (nmax f p).
Proof.
  intros f l p H.
  apply eq_imp_id.
  induction H as [ | x l' p' Hx IH | x y l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. lia.
  - rewrite IH1. exact IH2.
Qed.

(* ========== §3 频数补充件（保底件 nat 侧承重） ========== *)

(* 成员频率至少 1（Qeq_bool 假分支经 S6 qeqb_false_neq 矛盾闭合） *)
Lemma freq_q_ge1 : forall (x : Q) (l : list Q), In x l -> NatLe (1) ((freq_q x l)%nat).
Proof.
  intros x l Hin. revert Hin.
  induction l as [| y ys IH]; intros Hin; simpl; apply NatLe_lift.
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + subst y. destruct (Qeq_bool x x) eqn:Exx.
      * lia.
      * exfalso. apply (qeqb_false_neq x x Exx). reflexivity.
    + destruct (Qeq_bool x y) eqn:Exy.
      * lia.
      * apply NatLe_drop. apply IH. exact Hin.
Qed.

(* 泛求和下界（nsum_bound 的对偶） *)
Lemma nsum_ge_const : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (B <= f x)%nat) -> NatLe (length l * B) ((nsum f l)%nat).
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (Hy : (B <= f y)%nat) by (apply H; left; reflexivity).
    assert (Hys : NatLe (length ys * B) (nsum f ys))
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ Hys). lia.
Qed.

(* 保底件 nat 侧核心：sqsum >= length（逐点 freq >= 1，Cauchy-Schwarz 下界入口） *)
Lemma sqsum_ge_length : forall l : list Q, NatLe (length l) ((sqsum l)%nat).
Proof.
  intros l. unfold sqsum.
  pose proof (nsum_ge_const (fun x => freq_q x l) l 1
                (fun x Hx => NatLe_drop _ _ (freq_q_ge1 x l Hx))) as Hge.
  rewrite Nat.mul_1_r in Hge. exact Hge.
Qed.

(* ========== §4 collide：Rényi₂/碰撞熵核 Σp² 与界定理（保底件） ========== *)

(* collide l = Σ_{x∈l} (freq_q x l / n)² = qn (sqsum l) / (qn n · qn n) *)
Definition collide (l : list Q) : Q :=
  qn (sqsum l) / (qn (length l) * qn (length l)).

Lemma collide_zero : QeqT (collide []) (0).
Proof. apply qeq_imp_qeqT.
  assert (Hz : (qn (sqsum []) == 0)%Q).
  { change (qn (nsum (fun x => freq_q x []) []) == 0%Q).
    change (qn 0 == 0%Q).
    reflexivity. }
  unfold collide. unfold Qdiv. rewrite Hz. apply Qmult_0_l.
Qed.

(* 上界：collide <= 1（全表；sqsum <= n² 经 S6 sqsum_le） *)
Theorem collide_upper : forall l : list Q, QleT' (collide l) (1).
Proof.
  intros l. destruct l as [| x xs].
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ collide_zero).
    apply (Qlt_le_weak 0 1). reflexivity.
  - unfold collide. apply qdiv_le_1.
    + assert (Hle : qn (sqsum (x :: xs))
                    <= qn (length (x :: xs)) * qn (length (x :: xs))).
      { rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs))
                         (length (x :: xs)))).
        apply QleT'_to_Qle. apply qn_le. apply NatLe_drop. apply sqsum_le. }
      exact Hle.
    + apply QltT_to_Qlt. apply qlen_mul_pos.
Qed.

(* 下界：1/n <= collide（非空；1/n == n/n² 经 qdiv_norm，分子经 sqsum_ge_length） *)
Theorem collide_lower : forall l : list Q,
  (0 < length l)%nat -> QleT' (1 / qn (length l)) (collide l).
Proof.
  intros l Hl. apply Qle_to_QleT'. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold collide.
    pose proof (QltT_to_Qlt _ _ (qlen_mul_pos x xs)) as HPP.
    assert (HP2 : ~ (qn (length (x :: xs)) * qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 _ HPP (qeq_imp_qeqT _ _ Hc)). }
    assert (HP1 : ~ (qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 (qn (length (x :: xs)))
        (QltT_to_Qlt 0 (qn (length (x :: xs)))
          (qn_pos (length (x :: xs)) (NatLe_drop 1 (length (x :: xs)) (qlen_pos x xs))))
        (qeq_imp_qeqT _ _ Hc)). }
    assert (Hge : (length (x :: xs) <= sqsum (x :: xs))%nat)
      by (apply NatLe_drop; apply sqsum_ge_length).
    assert (Hnum : qn (length (x :: xs)) <= qn (sqsum (x :: xs)))
      by (apply QleT'_to_Qle; apply qn_le; exact Hge).
    rewrite (qeqT_imp_qeq _ _
      (qdiv_norm (qn (length (x :: xs))) HP1 HP2)).
    apply QleT'_to_Qle. apply qdiv_ge_num.
    + exact HPP.
    + exact Hnum.
Qed.

(* 置换不变（sqsum_perm + Permutation_length 两步，S6 同款） *)
Theorem collide_perm : forall l p : list Q,
  Permutation l p -> QeqT (collide l) (collide p).
Proof.
  intros l p H. apply qeq_imp_qeqT. unfold collide.
  destruct (id_sym (sqsum_perm l p H)).
  rewrite (Permutation_length H). reflexivity.
Qed.

(* ========== §5 maxfreq：最大频率归一化与序链闭环（主定理） ========== *)

Definition maxcount (l : list Q) : nat := nmax (fun x => freq_q x l) l.

Definition maxfreq (l : list Q) : Q := qn (maxcount l) / qn (length l).

(* 【主定理序链】collide <= maxfreq：
   nat 侧 sqsum <= n · maxcount（S6 nsum_bound + nmax_bound 逐点），
   Q 侧同分母单调 + 场内归一（field 侧条件由上下文实例化消解） *)
Theorem collide_le_maxfreq : forall l : list Q, QleT' (collide l) (maxfreq l).
Proof.
  intros l. destruct l as [| x xs].
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ collide_zero).
    assert (Hz : maxfreq [] == 0)
      by (unfold maxfreq; apply qeqT_imp_qeq; apply qdiv_zero_num;
         reflexivity).
    rewrite Hz. apply Qle_refl.
  - unfold collide, maxfreq.
    pose proof (QltT_to_Qlt _ _ (qlen_mul_pos x xs)) as HPP.
    pose proof (qpos_neq0 _ HPP) as HP2.
    assert (HP1 : ~ (qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 (qn (length (x :: xs)))
        (QltT_to_Qlt 0 (qn (length (x :: xs)))
          (qn_pos (length (x :: xs)) (NatLe_drop 1 (length (x :: xs)) (qlen_pos x xs))))
        (qeq_imp_qeqT _ _ Hc)). }
    assert (Hnat : (sqsum (x :: xs)
                    <= length (x :: xs) * maxcount (x :: xs))%nat).
    { unfold sqsum, maxcount. apply NatLe_drop. apply nsum_bound.
      intros x0 Hx0. apply NatLe_drop.
      exact (nmax_bound (fun x0 => freq_q x0 (x :: xs)) (x :: xs) x0 Hx0). }
    assert (HQ : qn (sqsum (x :: xs))
                 <= qn (length (x :: xs)) * qn (maxcount (x :: xs))).
    { rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs))
                         (maxcount (x :: xs)))).
      apply QleT'_to_Qle. apply qn_le. exact Hnat. }
    assert (HA : qn (sqsum (x :: xs)) / (qn (length (x :: xs)) * qn (length (x :: xs)))
                 <= (qn (length (x :: xs)) * qn (maxcount (x :: xs)))
                    / (qn (length (x :: xs)) * qn (length (x :: xs)))).
    { apply QleT'_to_Qle. apply qdiv_ge_num.
      - exact HPP.
      - exact HQ. }
    assert (HB : (qn (length (x :: xs)) * qn (maxcount (x :: xs)))
                 / (qn (length (x :: xs)) * qn (length (x :: xs)))
                 == qn (maxcount (x :: xs)) / qn (length (x :: xs))).
    { field; assumption. }
    exact (Qle_to_QleT' _ _
      (Qle_trans _ _ _ HA (QleT'_to_Qle _ _ (qeq_le_l _ _ HB)))).
Qed.

(* 下界：1/n <= maxfreq（非空；maxcount >= 1 经逐点成员频率 >= 1） *)
Theorem maxfreq_lower : forall l : list Q,
  (0 < length l)%nat -> QleT' (1 / qn (length l)) (maxfreq l).
Proof.
  intros l Hl. apply Qle_to_QleT'. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold maxfreq.
    assert (Hge : (1 <= maxcount (x :: xs))%nat).
    { pose proof (NatLe_drop _ _
          (freq_q_ge1 x (x :: xs) (or_introl eq_refl))) as H1.
      assert (Hb : (freq_q x (x :: xs) <= maxcount (x :: xs))%nat).
      { unfold maxcount.
        exact (NatLe_drop _ _
                 (nmax_bound (fun x0 => freq_q x0 (x :: xs)) (x :: xs) x
                    (or_introl eq_refl))). }
      lia. }
    apply QleT'_to_Qle. apply qdiv_ge_num.
    + apply QltT_to_Qlt. apply qn_pos. apply NatLe_drop. apply qlen_pos.
    + assert (Hq1 : qn 1 == (1:Q)) by reflexivity.
      rewrite <- Hq1. exact (QleT'_to_Qle _ _ (qn_le 1 (maxcount (x :: xs)) Hge)).
Qed.

(* 上界：maxfreq <= 1（全表；maxcount <= length 经 nmax_le_bound 逐点） *)
Theorem maxfreq_upper : forall l : list Q, QleT' (maxfreq l) (1).
Proof.
  intros l. destruct l as [| x xs].
  - apply Qle_to_QleT'. assert (Hz : maxfreq [] == 0)
      by (unfold maxfreq; apply qeqT_imp_qeq; apply qdiv_zero_num; reflexivity).
    rewrite Hz. apply (Qlt_le_weak 0 1). reflexivity.
  - unfold maxfreq. apply qdiv_le_1.
    + assert (Hb : (maxcount (x :: xs) <= length (x :: xs))%nat).
      { unfold maxcount. apply NatLe_drop. apply nmax_le_bound.
        intros y Hy. apply NatLe_drop. apply freq_q_le_length. }
      apply (QleT'_to_Qle _ _ (qn_le (maxcount (x :: xs)) (length (x :: xs)) Hb)).
    + apply QltT_to_Qlt. apply qn_pos. apply NatLe_drop. apply qlen_pos.
Qed.

(* 简并面：全同值 ⟹ maxfreq 取 1（maxcount == length 双向夹） *)
Theorem maxfreq_all_same_one : forall l : list Q,
  all_same l -> (0 < length l)%nat -> QeqT (maxfreq l) 1.
Proof.
  intros l Hs Hl. apply qeq_imp_qeqT. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold maxfreq.
    assert (Hmc : (maxcount (x :: xs) = length (x :: xs))%nat).
    { unfold maxcount. apply Nat.le_antisymm.
      - apply NatLe_drop. apply nmax_le_bound.
        intros y Hy. apply NatLe_drop. apply freq_q_le_length.
      - apply (Nat.le_trans (length (x :: xs)) (freq_q x (x :: xs))
                 (nmax (fun x0 => freq_q x0 (x :: xs)) (x :: xs))).
        + destruct (id_sym (freq_q_eq_all x (x :: xs)
                        (fun z Hz => qeqT_imp_qeq _ _
                           (Hs z x Hz (or_introl eq_refl))))).
          apply Nat.le_refl.
        + exact (NatLe_drop _ _
                   (nmax_bound (fun x0 => freq_q x0 (x :: xs)) (x :: xs) x
                      (or_introl eq_refl))). }
    rewrite Hmc.
    assert (HPne : ~ (qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 (qn (length (x :: xs)))
        (QltT_to_Qlt 0 (qn (length (x :: xs)))
          (qn_pos (length (x :: xs)) (NatLe_drop 1 (length (x :: xs)) (qlen_pos x xs))))
        (qeq_imp_qeqT _ _ Hc)). }
    field; assumption.
Qed.

(* maxcount 置换不变（nmax_ext_in 点点相等桥 + nmax_perm，sqsum_perm 同款） *)
Theorem maxcount_perm : forall l p : list Q,
  Permutation l p -> Id (maxcount l) (maxcount p).
Proof.
  intros l p H. unfold maxcount.
  assert (Hex : forall x, In x l -> freq_q x l = freq_q x p).
  { intros x _. destruct (freq_q_perm x l p H). reflexivity. }
  destruct (id_sym (nmax_ext_in (fun x => freq_q x l)
              (fun x => freq_q x p) l Hex)).
  exact (nmax_perm (fun x => freq_q x p) l p H).
Qed.

(* maxfreq 置换不变 *)
Theorem maxfreq_perm : forall l p : list Q,
  Permutation l p -> QeqT (maxfreq l) (maxfreq p).
Proof.
  intros l p H. apply qeq_imp_qeqT. unfold maxfreq.
  destruct (id_sym (maxcount_perm l p H)).
  rewrite (Permutation_length H). reflexivity.
Qed.

(* 【序链合读】非空 l：1/n <= collide <= maxfreq <= 1 三成员一次入链 *)
Theorem H_chain : forall l : list Q, (0 < length l)%nat ->
  And (QleT' (1 / qn (length l)) (collide l))
      (And (QleT' (collide l) (maxfreq l)) (QleT' (maxfreq l) 1)).
Proof.
  intros l Hl. split.
  - apply collide_lower. exact Hl.
  - split.
    + apply collide_le_maxfreq.
    + apply maxfreq_upper.
Qed.

(* ========== §6 H_max_q / H_min_q：多熵族补形有理代理面（主件） ========== *)

Definition H_max_q (l : list Q) : Q := 1 - maxfreq l.

Definition H_min_q (l : list Q) : Q := 1 - collide l.

(* 单调面：maxfreq 越大 H_max_q 越小（经 qsub_le 反变桥） *)
Theorem H_max_q_anti : forall l p : list Q,
  maxfreq l <= maxfreq p -> QleT' (H_max_q p) (H_max_q l).
Proof.
  intros l p H. unfold H_max_q. exact (qsub_le (maxfreq l) (maxfreq p) 1 H).
Qed.

Theorem H_max_q_nonneg : forall l : list Q, QleT' 0 (H_max_q l).
Proof.
  intros l. unfold H_max_q. exact (fst (Qle_0_sub' (maxfreq l) 1) (maxfreq_upper l)).
Qed.

Theorem H_max_q_le_one : forall l : list Q, QleT' (H_max_q l) 1.
Proof.
  intros l. apply Qle_to_QleT'. unfold H_max_q.
  assert (H0 : 0 <= maxfreq l).
  { destruct l as [| x xs].
    - assert (Hz : maxfreq [] == 0)
        by (unfold maxfreq; apply qeqT_imp_qeq; apply qdiv_zero_num;
           reflexivity).
      rewrite Hz. apply Qle_refl.
    - unfold maxfreq. apply QleT'_to_Qle. apply qdiv_nonneg.
      + apply QleT'_to_Qle. apply qn_nonneg.
      + apply QltT_to_Qlt. apply qn_pos. apply NatLe_drop. apply qlen_pos. }
  apply (Qle_trans (1 - maxfreq l) (1 - 0) 1).
  - apply QleT'_to_Qle. apply qsub_le. exact H0.
  - assert (Hz : (1:Q) - 0 == 1) by reflexivity.
    rewrite Hz. apply Qle_refl.
Qed.

(* 与下界的耦合：H_max_q l <= 1 - 1/n（非空） *)
Theorem H_max_q_le_inv : forall l : list Q, (0 < length l)%nat ->
  QleT' (H_max_q l) (1 - 1 / qn (length l)).
Proof.
  intros l Hl. unfold H_max_q.
  exact (qsub_le (1 / qn (length l)) (maxfreq l) 1
    (QleT'_to_Qle _ _ (maxfreq_lower l Hl))).
Qed.

Theorem H_min_q_nonneg : forall l : list Q, QleT' 0 (H_min_q l).
Proof.
  intros l. unfold H_min_q. exact (fst (Qle_0_sub' (collide l) 1) (collide_upper l)).
Qed.

Theorem H_min_q_le_one : forall l : list Q, QleT' (H_min_q l) 1.
Proof.
  intros l. apply Qle_to_QleT'. unfold H_min_q.
  assert (Hc : 0 <= collide l).
  { destruct l as [| x xs].
    - rewrite (qeqT_imp_qeq _ _ collide_zero). apply Qle_refl.
    - unfold collide. apply QleT'_to_Qle. apply qdiv_nonneg.
      + apply QleT'_to_Qle. apply qn_nonneg.
      + apply QltT_to_Qlt. apply qlen_mul_pos. }
  apply (Qle_trans (1 - collide l) (1 - 0) 1).
  - apply QleT'_to_Qle. apply qsub_le. exact Hc.
  - assert (Hz : (1:Q) - 0 == 1) by reflexivity.
    rewrite Hz. apply Qle_refl.
Qed.

(* 熵族内部相干桥：H_freq == 1 − collide（非空；S6 件定义直推，field 闭合） *)
Theorem H_freq_eq_bridge : forall l : list Q,
  (0 < length l)%nat -> QeqT (H_freq l) (H_min_q l).
Proof.
  intros l Hl. apply qeq_imp_qeqT. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold H_freq, H_min_q, collide.
    assert (HP1 : ~ (qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 (qn (length (x :: xs)))
        (QltT_to_Qlt 0 (qn (length (x :: xs)))
          (qn_pos (length (x :: xs)) (NatLe_drop 1 (length (x :: xs)) (qlen_pos x xs))))
        (qeq_imp_qeqT _ _ Hc)). }
    pose proof (QltT_to_Qlt _ _ (qlen_mul_pos x xs)) as HPP.
    assert (HP2 : ~ (qn (length (x :: xs)) * qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 _ HPP (qeq_imp_qeqT _ _ Hc)). }
    field; assumption.
Qed.

(* 简并面：全同值 ⟹ H_max_q 取 0（与 S6 H_freq_all_same_zero 对偶） *)
Theorem H_max_q_all_same_zero : forall l : list Q,
  all_same l -> (0 < length l)%nat -> QeqT (H_max_q l) 0.
Proof.
  intros l Hs Hl. apply qeq_imp_qeqT. unfold H_max_q.
  assert (H1 : maxfreq l == 1) by (apply qeqT_imp_qeq; apply maxfreq_all_same_one; assumption).
  rewrite H1. reflexivity.
Qed.

(* ========== §7 置换不变收尾（加分项） ========== *)

Theorem H_min_q_perm : forall l p : list Q,
  Permutation l p -> QeqT (H_min_q l) (H_min_q p).
Proof.
  intros l p H. apply qeq_imp_qeqT. unfold H_min_q.
  rewrite (qeqT_imp_qeq _ _ (collide_perm l p H)). reflexivity.
Qed.

Theorem H_max_q_perm : forall l p : list Q,
  Permutation l p -> QeqT (H_max_q l) (H_max_q p).
Proof.
  intros l p H. apply qeq_imp_qeqT. unfold H_max_q.
  rewrite (qeqT_imp_qeq _ _ (maxfreq_perm l p H)). reflexivity.
Qed.


(* ============================================================
   §A4 归并棒 S4：并入 DTPT_ME2.v —— MultiEntropyEval
   相干性二波（热点 X2-6）：第 0 节局部工具（abs 三角/聚合权/dedup
   计数）+ 第一节五字段定义方程族（复用 S2 mkMEval_eta 禁重证）+
   第二节主定理 me_cert 九联合相干证书 + 第三节 X2-6 套件级 lifts
   与跨字段桥 + 第四节聚合面 me_total 三件。
   仅剥去独立文件的 Require/Import 头与 Module 壳行（stdlib 与
   DTPT 基础由本文件头统一承载；并入后位于 Module DTPT_Entropy
   内，对 mkMEval/H_devsum/H_cond 等本文件面的引用变同文件直引，
   语义零变）；注释与全部证明体、Qed 面、文尾 Print Assumptions
   审计出口零改动逐字迁移（CRLF 归一）。撞名预检：23 个并入顶层
   名对宿主既有面整词 grep 全零命中（实测为准，纯追加零 uniquify）。
   ============================================================ *)

(* ============================================================
   DTPT_ME2.v — MultiEntropyEval 相干性二波：从「数据束」升级为
   「自证证书」（热点升级单 X2-6，扫描件 DTPT-U16）
   原典映射：附录三「多熵评估套件」+ DTPT_Entropy.v L46-58 定义面
   ------------------------------------------------------------
   基础（只 Require DTPT / DTPT_Entropy / stdlib，零新前提）：
   - DTPT_Entropy.v：mkMEval/mkMEval_eta（S2 已证五投影，复用禁重证）、
     H_shannon_q_nonneg、xq_H_adj_nonneg、H_shannon_q_count_ub、
     H_adj_P0_min、H_cond_nonneg_guarded、mkMEval_Hms1_Hsh0、
     xq_Zlen_nonneg、xq_Qle_bool_le、qadd_nonneg
   - DTPT.v：H_ms、gate_pass、Qle_dec'、abs_eq、abs_neg、
     Qle_0_sub'、qmul_le_r、qadd_le、qsub 工具
   - stdlib：Qle_trans、Qle_refl、ring/lia
   ------------------------------------------------------------
   分层交付：
   - 保底（一档）：五字段逐一定义方程（组合复用 mkMEval_eta，零重证）
   - 主定理（二档）：me_cert —— 载体一致 + 四熵等值 + Hadj/Hsh 非负 +
     Hsh 计数上界 + Hcond 三角界，九联合相干合取面
     （me_coherent 证书谓词 + mkMEval 构造见证）
   - 主件（三档）：X2-6 六件套件级 lifts + H_ms1→Hsh0 逆否桥 +
     |me_Hcond| 三角界/计数面证书版 + gate 双门桥
     （H_cond_abs_bound 在 ZeroLocus 盘面，按红线禁 Require，不使用）
   - 加分（四档）：me_total 等权聚合 + 守卫非负界 + 2 倍香农上界
   红线自查：承认件/中断件/经典排中面等禁词全零（字面自查见
   升级报告 G1 行），全程 Qed 闭合；nat 全显式 %nat。
   ============================================================ *)

(* ============================================================
   第 0 节 局部工具（abs 三角 / 聚合权 / dedup 计数）
   ============================================================ *)

(* 非负二元差 abs 三角：0 <= a、0 <= b -> |a - b| <= a + b
   （Qle_dec' 两分定形 + abs_eq/abs_neg，正负两支各经 Qle_0_sub' 移项） *)
Lemma me2_abs_sub_triangle : forall a b : Q,
  (0 <= a)%Q -> (0 <= b)%Q -> QleT' (Qabs (a - b)) (a + b).
Proof.
  intros a b Ha Hb.
  apply Qle_to_QleT'.
  destruct (Qle_dec' a b) as [Hab | Hba].
  - (* 支一 a <= b：|a-b| = -(a-b) = b-a，经 (a+b)-(b-a) = 2a >= 0 *)
    assert (Hneg : (a - b <= 0)%Q).
    { apply QleT'_to_Qle. apply (snd (Qle_0_sub' (a - b) 0)).
      apply Qle_to_QleT'.
      assert (Hr : (0 - (a - b))%Q == b - a) by ring.
      rewrite Hr. exact (QleT'_to_Qle _ _ (fst (Qle_0_sub' a b) Hab)). }
    rewrite (qeqT_imp_qeq _ _ (abs_neg (a - b) Hneg)).
    assert (Heq : (- (a - b))%Q == b - a) by ring.
    rewrite Heq.
    apply QleT'_to_Qle. apply (snd (Qle_0_sub' (b - a) (a + b))).
    apply Qle_to_QleT'.
    assert (Hr2 : ((a + b) - (b - a))%Q == a + a) by ring.
    rewrite Hr2. apply QleT'_to_Qle. apply qadd_nonneg; exact Ha.
  - (* 支二 b <= a：|a-b| = a-b，经 (a+b)-(a-b) = 2b >= 0 *)
    assert (Hpos : (0 <= a - b)%Q).
    { apply QleT'_to_Qle. apply (fst (Qle_0_sub' b a)). exact Hba. }
    rewrite (qeqT_imp_qeq _ _ (abs_eq (a - b) Hpos)).
    apply QleT'_to_Qle. apply (snd (Qle_0_sub' (a - b) (a + b))).
    apply Qle_to_QleT'.
    assert (Hr3 : ((a + b) - (a - b))%Q == b + b) by ring.
    rewrite Hr3. apply QleT'_to_Qle. apply qadd_nonneg; exact Hb.
Qed.

(* 聚合权 1/4 非负（字面 Qle_bool 计算） *)
Lemma me2_weight_nonneg : QleT' (0) ((1 # 4)%Q).
Proof. apply Qle_to_QleT'.
  change (Z.le (0 * 4) (1 * 1))%Z.
  lia.
Qed.

(* 非空表的 dedup 计数 >= 1（nat 全显式） *)
Lemma me2_dedup_len_ge1 : forall l : list Q,
  l <> [] -> NatLe (1) ((length (dedup l))%nat).
Proof.
  intros [| x xs] H.
  apply NatLe_lift.
  - exfalso. apply H. reflexivity.
  - cbn [dedup length]. reflexivity.
Qed.

(* ============================================================
   第一节 保底件：五字段逐一定义方程（复用 S2 mkMEval_eta，禁重证）
   ============================================================ *)

Theorem me2_carrier_eq : forall (l ctx : list Q), Id (me_carrier (mkMEval l ctx)) (l).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [Hc _]. exact Hc.
Qed.

Theorem me2_Hadj_eq : forall (l ctx : list Q), QeqT (me_Hadj (mkMEval l ctx)) (H_adj l).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [Ha _]]. exact Ha.
Qed.

Theorem me2_Hms_eq : forall (l ctx : list Q),
  QeqT (me_Hms (mkMEval l ctx)) (H_ms l).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [_ [Hm _]]]. exact Hm.
Qed.

Theorem me2_Hsh_eq : forall (l ctx : list Q), QeqT (me_Hsh (mkMEval l ctx)) (H_devsum l).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [_ [_ [Hs _]]]]. exact Hs.
Qed.

Theorem me2_Hcond_eq : forall (l ctx : list Q), QeqT (me_Hcond (mkMEval l ctx)) (H_cond l ctx).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [_ [_ [_ Hc]]]]. exact Hc.
Qed.

(* ============================================================
   第二节 主定理：me_cert —— mkMEval 自证证书（九联合相干合取面）
   载体一致 + 四熵等值 + Hadj/Hsh 非负 + Hsh 计数上界 + Hcond 三角界
   ============================================================ *)

Definition me_coherent (m : MultiEntropyEval) (l ctx : list Q) : Set :=
  And (Id (me_carrier m) l)
  (And (QeqT (me_Hadj m) (H_adj l))
  (And (QeqT (me_Hms m) (H_ms l))
  (And (QeqT (me_Hsh m) (H_devsum l))
  (And (QeqT (me_Hcond m) (H_cond l ctx))
  (And (QleT' 0 (me_Hadj m))
  (And (QleT' 0 (me_Hsh m))
  (And (QleT' (me_Hsh m) (me_Hadj m * (Z.of_nat (length (me_carrier m)) # 1)))
       (QleT' (Qabs (me_Hcond m)) (me_Hsh m + H_devsum ctx))))))))).

Theorem me_cert : forall (l ctx : list Q),
  me_coherent (mkMEval l ctx) l ctx.
Proof.
  intros l ctx.
  destruct (mkMEval_eta l ctx) as [Hc [Ha [Hm [Hs Hcond]]]].
  (* repeat split 直收前五个定义性合取面（载体 eq + 四 Qeq，
     Z.eq 为 Prop 级单构造子，投影 delta 归约后 eq_refl 可解），
     余下四个 Qle 相干面逐条复用基础件 *)
  unfold me_coherent, And. repeat split.
  - exact Ha.
  - exact Hm.
  - exact Hs.
  - exact Hcond.
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ Ha).
    apply QleT'_to_Qle. apply xq_H_adj_nonneg.
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ Hs).
    apply QleT'_to_Qle. apply H_shannon_q_nonneg.
  - apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ Hs), (qeqT_imp_qeq _ _ Ha).
    destruct (id_sym Hc).
    exact (QleT'_to_Qle _ _ (H_shannon_q_count_ub l)).
  - apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ Hcond), (qeqT_imp_qeq _ _ Hs).
    unfold H_cond.
    apply QleT'_to_Qle. apply me2_abs_sub_triangle;
      apply QleT'_to_Qle, H_shannon_q_nonneg.
Qed.

(* ============================================================
   第三节 主件：X2-6 套件级 lifts + 跨字段桥（证书版）
   ============================================================ *)

(* 3.1 P0 最小性提升：H_adj (P0 载体) <= me_Hadj *)
Theorem mkMEval_Hadj_min : forall (l ctx : list Q),
  QleT' (H_adj (P0 (me_carrier (mkMEval l ctx)))) (me_Hadj (mkMEval l ctx)).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [Hc [Ha _]].
  apply Qle_to_QleT'.
  destruct (id_sym Hc).
  rewrite (qeqT_imp_qeq _ _ Ha).
  exact (QleT'_to_Qle _ _ (H_adj_P0_min l)).
Qed.

(* 3.2 香农字段非负 *)
Theorem mkMEval_Hsh_nonneg : forall (l ctx : list Q),
  QleT' 0 (me_Hsh (mkMEval l ctx)).
Proof.
  intros l ctx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hsh_eq l ctx)).
  exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l)).
Qed.

(* 3.3 香农字段计数上界（H_adj × 长度系数） *)
Theorem mkMEval_Hsh_ub : forall (l ctx : list Q),
  QleT' (me_Hsh (mkMEval l ctx))
        (me_Hadj (mkMEval l ctx) * (Z.of_nat (length l) # 1)).
Proof.
  intros l ctx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hsh_eq l ctx)),
          (qeqT_imp_qeq _ _ (me2_Hadj_eq l ctx)).
  exact (QleT'_to_Qle _ _ (H_shannon_q_count_ub l)).
Qed.

(* 3.4 多重集熵非空下界：载体非空 -> 1 <= me_Hms（Z 桥） *)
Theorem mkMEval_Hms_ge1 : forall (l ctx : list Q),
  l <> [] -> QleT' 1 (me_Hms (mkMEval l ctx)).
Proof.
  intros l ctx Hl. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hms_eq l ctx)). unfold H_ms.
  assert (Hn : (1 <= length (dedup l))%nat)
    by (apply NatLe_drop; apply me2_dedup_len_ge1; exact Hl).
  assert (Hz : (1 <= Z.of_nat (length (dedup l)))%Z) by lia.
  unfold Qle. cbn [Qnum Qden]. lia.  (* 记录字段真名小写 Qden（S2 卡坑四） *)
Qed.

(* 3.5 条件熵负侧界：-H_sh ctx <= me_Hcond（H_shannon_q_nonneg 移项） *)
Theorem mkMEval_Hcond_lb : forall (l ctx : list Q),
  QleT' (- H_devsum ctx) (me_Hcond (mkMEval l ctx)).
Proof.
  intros l ctx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hcond_eq l ctx)). unfold H_cond.
  apply QleT'_to_Qle. apply (snd (Qle_0_sub' (- H_devsum ctx)
                           (H_devsum l - H_devsum ctx))).
  apply Qle_to_QleT'.
  assert (Hr : (H_devsum l - H_devsum ctx) - (- H_devsum ctx)
               == H_devsum l) by ring.
  rewrite Hr. exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l)).
Qed.

(* 3.6 双门同一 Qle_bool：低熵门 == gate_pass（跨定义面） *)
Theorem mkMEval_gate_bridge : forall (l ctx : list Q) (t : Q), Id (gate_low_entropy (me_Hsh (mkMEval l ctx)) t) (gate_pass t (H_devsum l)).
Proof.
  intros l ctx t. apply eq_imp_id. unfold gate_low_entropy, gate_pass, mkMEval.
  cbn [me_Hsh]. destruct (Qle_bool (H_devsum l) t); reflexivity.
Qed.

(* 3.7 跨字段桥证书版：H_ms==1 -> Hsh==0 的逆否面
   （复用 S2 mkMEval_Hms1_Hsh0，零重证） *)
Theorem mkMEval_notHsh0_notHms1 : forall (l ctx : list Q),
  ~ (me_Hsh (mkMEval l ctx) == 0)%Q -> Not (QeqT (me_Hms (mkMEval l ctx)) 1).
Proof.
  intros l ctx H0 Hms1. apply qeqT_imp_qeq in Hms1.
  exact (False_rect Empty_set
    (H0 (qeqT_imp_qeq _ _ (mkMEval_Hms1_Hsh0 l ctx Hms1)))).
Qed.

(* 3.8 三角界证书版：|me_Hcond| <= me_Hsh + H_sh ctx（Entropy 内件组合；
   H_cond_abs_bound 在 ZeroLocus 盘面按红线禁 Require，不使用） *)
Theorem mkMEval_Hcond_abs_ub : forall (l ctx : list Q),
  QleT' (Qabs (me_Hcond (mkMEval l ctx)))
        (me_Hsh (mkMEval l ctx) + H_devsum ctx).
Proof.
  intros l ctx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hcond_eq l ctx)),
          (qeqT_imp_qeq _ _ (me2_Hsh_eq l ctx)). unfold H_cond.
  apply QleT'_to_Qle. apply me2_abs_sub_triangle;
    [ exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l))
    | exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg ctx)) ].
Qed.

(* 3.9 计数面证书版：|me_Hcond| <= me_Hadj×n_l + H_adj ctx×n_ctx
   （3.8 三角界 × H_shannon_q_count_ub 双臂） *)
Theorem mkMEval_Hcond_count_ub : forall (l ctx : list Q), QleT' (Qabs (me_Hcond (mkMEval l ctx))) (me_Hadj (mkMEval l ctx) * (Z.of_nat (length l) # 1)
       + H_adj ctx * (Z.of_nat (length ctx) # 1)).
Proof.
  intros l ctx. pose proof (mkMEval_eta l ctx) as Heta.
  destruct Heta as [Hc Hr1]. destruct Hr1 as [Ha Hr2].
  destruct Hr2 as [Hm Hr3]. destruct Hr3 as [Hs Hcond].
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ Hcond), (qeqT_imp_qeq _ _ Ha).
  unfold H_cond.
  apply (Qle_trans _ (H_devsum l + H_devsum ctx)%Q).
  - apply QleT'_to_Qle. apply me2_abs_sub_triangle;
      [ exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l))
      | exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg ctx)) ].
  - apply QleT'_to_Qle. apply qadd_le.
    + exact (QleT'_to_Qle _ _ (H_shannon_q_count_ub l)).
    + exact (QleT'_to_Qle _ _ (H_shannon_q_count_ub ctx)).
Qed.

(* ============================================================
   第四节 加分：聚合面 me_total（等权 1/4）+ 守卫非负界 + 2 倍上界
   ============================================================ *)

Definition me_total (m : MultiEntropyEval) : Q :=
  (1 # 4)%Q * (me_Hadj m + me_Hms m + me_Hsh m + me_Hcond m)%Q.

(* 聚合定义方程（mkMEval 上投影定义性） *)
Theorem me_total_eq : forall (l ctx : list Q), QeqT (me_total (mkMEval l ctx)) ((1 # 4)%Q * (H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q).
Proof.
  intros l ctx.
  apply qeq_imp_qeqT.
  change (me_total (mkMEval l ctx))
    with ((1 # 4)%Q * (me_Hadj (mkMEval l ctx) + me_Hms (mkMEval l ctx)
          + me_Hsh (mkMEval l ctx) + me_Hcond (mkMEval l ctx))%Q).
  change (me_Hadj (mkMEval l ctx)) with (H_adj l).
  change (me_Hms (mkMEval l ctx)) with (H_ms l).
  change (me_Hsh (mkMEval l ctx)) with (H_devsum l).
  change (me_Hcond (mkMEval l ctx)) with (H_cond l ctx).
  reflexivity.
Qed.

(* 守卫非负界：H_sh ctx <= H_sh l -> 0 <= me_total
   （四熵在守卫下全非负，qadd_nonneg 链 + qmul_le_r） *)
Theorem me_total_nonneg_guarded : forall (l ctx : list Q),
  (H_devsum ctx <= H_devsum l)%Q ->
  QleT' 0 (me_total (mkMEval l ctx)).
Proof.
  intros l ctx Hle. apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ (me_total_eq l ctx)).
  assert (Hc : (0 <= H_cond l ctx)%Q)
    by (apply QleT'_to_Qle; apply H_cond_nonneg_guarded; exact Hle).
  assert (Hms : (0 <= H_ms l)%Q)
    by (unfold H_ms; apply QleT'_to_Qle; apply xq_Zlen_nonneg).
  assert (Hsum : (0 <= H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q).
  { apply QleT'_to_Qle. apply qadd_nonneg.
    - apply QleT'_to_Qle. apply qadd_nonneg.
      + apply QleT'_to_Qle. apply qadd_nonneg;
          [ apply QleT'_to_Qle; apply xq_H_adj_nonneg | exact Hms ].
      + exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l)).
    - exact Hc. }
  exact (QleT'_to_Qle _ _ (xq_mul_nonneg ((1 # 4)%Q)
    ((H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q)
    (QleT'_to_Qle _ _ me2_weight_nonneg) Hsum)).
Qed.

(* 聚合上界：me_total <= (1/4)×(H_adj + H_ms + 2×H_sh)
   （负侧恰由 H_cond <= H_sh l 吃掉：-H_sh ctx <= 0） *)
Theorem me_total_ub : forall (l ctx : list Q), QleT' (me_total (mkMEval l ctx)) ((1 # 4)%Q * (H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q).
Proof.
  intros l ctx. apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ (me_total_eq l ctx)).
  assert (Hcc : (H_cond l ctx <= H_devsum l)%Q).
  { unfold H_cond. apply QleT'_to_Qle. apply (snd (Qle_0_sub' _ _)).
    apply Qle_to_QleT'.
    assert (Hr : H_devsum l - (H_devsum l - H_devsum ctx)
                 == H_devsum ctx) by ring.
    rewrite Hr. apply QleT'_to_Qle. apply H_shannon_q_nonneg. }
  assert (Hsub : (H_devsum l + H_cond l ctx
                  <= (2 # 1)%Q * H_devsum l)%Q).
  { assert (Hr2 : (2 # 1)%Q * H_devsum l
                  == H_devsum l + H_devsum l) by ring.
    rewrite Hr2. apply QleT'_to_Qle. apply qadd_le.
    - apply Qle_refl.
    - exact Hcc. }
  assert (Hassoc : (H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q
                   == (H_adj l + H_ms l + (H_devsum l + H_cond l ctx))%Q)
    by ring.
  rewrite Hassoc.
  assert (Hinner : (H_adj l + H_ms l + (H_devsum l + H_cond l ctx)
                    <= H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q).
  { apply QleT'_to_Qle. apply qadd_le.
    - apply Qle_refl.
    - exact Hsub. }
  (* qmul_le_r 为右乘子形且要求同乘子：两侧权重各 ring 换序到右 *)
  assert (Hsw1 : (1 # 4)%Q
                   * (H_adj l + H_ms l + (H_devsum l + H_cond l ctx))%Q
               == (H_adj l + H_ms l + (H_devsum l + H_cond l ctx))%Q
                    * (1 # 4)%Q) by ring.
  assert (Hsw2 : (1 # 4)%Q
                   * (H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q
               == (H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q
                    * (1 # 4)%Q) by ring.
  rewrite Hsw1, Hsw2. apply QleT'_to_Qle. apply qmul_le_r.
  - exact Hinner.
  - exact (QleT'_to_Qle _ _ me2_weight_nonneg).
Qed.

(* ============================================================
   §A5 归并棒 S4：并入 DTPT_ZeroLocus.v —— 零点刻画
   （热点 X2-2）：占位熵 H_devsum 零点集结构刻画五节——工具面
   （xqz_ 系 abs0/sub/plus_eq0）+ 主定理 H_shannon_q_zero_iff_sorted
   （零点 ⟺ 升序表 SortedQ）+ 主件A H_ms1_all_eq/H_ms1_iff_const
   + 主件B H_cond_nonneg_iff/H_cond_abs_bound/H_cond_zero_iff +
   加分 H_shannon_q_perm_inv_if_sorted/zero_locus_joint/
   zero_locus_contrast_sorted_not_const。
   仅剥去独立文件的 Require/Import 头与 Module 壳行（stdlib 与
   DTPT 基础由本文件头统一承载；并入后位于 Module DTPT_Entropy
   内，对 H_devsum/xq_H_shannon_sortQ/xq_Zlen_inj1 等 S2 面的
   引用变同文件直引，语义零变）；ADJ-1 复合名保留件
   （H_shannon_q_* 系）整词对照零改名；注释与全部证明体、Qed 面、
   文尾 Print Assumptions 审计出口零改动逐字迁移（CRLF 归一）。
   撞名预检：17 个并入顶层名对宿主既有面整词 grep 全零命中。
   ============================================================ *)

(* ============================================================
   DTPT_ZeroLocus.v — 零点刻画件 U4（热点升级单 X2-2，X2 扫描 Top-2）
   职责：占位「质心偏移」香农偏差熵 H_devsum（DTPT_Entropy.v，
         逐项 |x - 后缀 P0 最小| 之和）的零点集结构刻画：
         零点 ⟺ 升序表（SortedQ）；内容分级：
         主定理  H_shannon_q_zero_iff_sorted（正向 = 盘上
               xq_H_shannon_sortQ；反向本件新证：和零 + 双项非负
               ⟹ 逐项零 ⟹ 首元 == 后缀 P0 最小 ⟹ 升序 cons，
               配 hd 最小性新引理 xqz_sorted_hd_min）
         主件A H_ms1_all_eq / H_ms1_iff_const（H_ms == 1 全同值
               刻画；诚实口径：空表 H_ms [] == 0 而「全成员同值」
               空真，故 iff 右侧带 l <> [] 守卫——对 X2-2 草式的
               必要修正）
         主件B H_cond_nonneg_iff / H_cond_abs_bound / H_cond_zero_iff
               （绝对值界：|H_cond| <= H_devsum l + H_devsum ctx）
         加分  H_shannon_q_perm_inv_if_sorted（反例①的 restricted
               正形：双侧升序时置换不变成立）、zero_locus_joint
               （反例③的正面孪生：双零点 ⟺ 非空常值表）、
               zero_locus_contrast_sorted_not_const（[1;2] 对照锚）
   依赖：QArith（QArith/Qabs）、List、Arith、Lia、Permutation、
         DTPT（D5_P0_perm / dedup 系 / Qmem 系 / qadd_le /
         Qle_0_sub' / Qeqb_true_of）、DTPT_Entropy（xq_H_shannon_sortQ、
         xq_Zlen_inj1、xq_len1_el、xq_dedup1_all_eq、
         H_shannon_q_const_zero、H_shannon_q_nonneg）。
   归并记录：无（原生成模块）。
   认证：零承认零公理；全树 coqchk EXIT=0。
   纪律：纯构造性；温控协议；新名一律 xqz_ 前缀防撞名；
         nat 全显式 %nat；Qeq 口径显式迁移（Qeq_trans/Qeq_sym
         值参显式位）；全部声明以 Qed 闭合。
   附注：与 S6 真频率熵的对照定位——占位熵 H_devsum 零点可含
         相异值（[1;2] 是零点但非常值），真频率熵 H_freq 零点必为
         常值表；对照锚 zero_locus_contrast_sorted_not_const 给出
         可执行见证，S6 落盘后可经 Require 直接拼装双向对照引理
         （首期不做）；本件不定义任何频率/对数对象，S5 测度面零接触。
   ============================================================ *)

(* ========== §1 工具：绝对值零点、减法零点、非负和零分解 ========== *)

(* Qabs x == 0 -> x == 0（对 Qnum 三分直解，stdlib 无 Qeq 形现成件） *)
Lemma xqz_abs0_eq : forall x : Q, Qabs x == 0 -> QeqT x 0.
Proof.
  intros [n d] H. apply qeq_imp_qeqT. unfold Qeq. destruct n as [| p | p].
  - reflexivity.
  - unfold Qabs in H. simpl in H. discriminate H.
  - unfold Qabs in H. simpl in H. discriminate H.
Qed.

(* x - y == 0 -> x == y（Qle_0_sub' 双向 + 反对称，零 setoid 重写） *)
Lemma xqz_sub_eq0 : forall x y : Q, (x - y == 0)%Q -> QeqT x y.
Proof.
  intros x y H. apply qeq_imp_qeqT.
  assert (Hyx : (y - x == 0)%Q).
  { assert (Hmo : y - x == - (x - y)) by (apply qeqT_imp_qeq; apply xq_minus_opp).
    rewrite Hmo, H. reflexivity. }
  apply qeqT_imp_qeq. apply (xq_Qle_antisym x y).
  - apply QleT'_to_Qle. apply (snd (Qle_0_sub' x y)).
    apply xq_Qeq_le. apply Qeq_sym. exact Hyx.
  - apply QleT'_to_Qle. apply (snd (Qle_0_sub' y x)).
    apply xq_Qeq_le. apply Qeq_sym. exact H.
Qed.

(* 非负两项和为零 ⟹ 首项为零（a <= a+b == 0 与 0 <= a 夹挤） *)
Lemma xqz_plus_eq0_le : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> QeqT a 0.
Proof.
  intros a b Hab Ha Hb. apply qeq_imp_qeqT.
  assert (Hle : QleT' (a + 0) (a + b))
    by (apply qadd_le; [apply Qle_refl | exact Hb]).
  assert (Hle' : a <= 0).
  { apply QleT'_to_Qle in Hle. rewrite Hab in Hle.
    rewrite Qplus_0_r in Hle. exact Hle. }
  apply qeqT_imp_qeq. exact (xq_Qle_antisym a 0 Hle' Ha).
Qed.

(* 非负两项和为零 ⟹ 两项皆零（交换后复用） *)
Lemma xqz_plus_eq0 : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> And (QeqT a 0) (QeqT b 0).
Proof.
  intros a b Hab Ha Hb. split.
  - exact (xqz_plus_eq0_le a b Hab Ha Hb).
  - rewrite Qplus_comm in Hab.
    exact (xqz_plus_eq0_le b a Hab Hb Ha).
Qed.

(* ========== §2 主定理：H_devsum 零点集 = 升序表 ========== *)

(* hd 最小性：升序表的首元不超过表内任何成员 *)
Lemma xqz_sorted_hd_min : forall (l : list Q) (z : Q),
  SortedQ l -> In z l -> QleT' (hd 0 l) (z).
Proof.
  intros [| a rest] z HS Hin.
  - apply Qle_to_QleT'. destruct Hin.
  - apply Qle_to_QleT'.
    destruct HS as [| c1 c2 HSr HFa].
    * destruct Hin.
    * subst.
      rewrite Forall_forall in HFa.
      change (hd 0 (a :: rest)) with a.
      destruct Hin as [Heq | Hin].
      { subst. apply Qle_refl. }
      { apply HFa. exact Hin. }
Qed.

(* P0 规范形的首元是全表下界（经置换迁移成员性） *)
Lemma xqz_P0_hd_min_all : forall (l : list Q) (z : Q),
  In z l -> QleT' (hd 0 (P0 l)) (z).
Proof.
  intros l z Hin.
  apply (xqz_sorted_hd_min (P0 l) z).
  - apply xq_P0_sorted.
  - apply Permutation_in with (l := l).
    + apply D5_P0_perm.
    + exact Hin.
Qed.

(* 主定理反向：占位熵零 ⟹ 升序（逐层剥 |首差| + 归纳） *)
Theorem H_shannon_q_zero_sorted : forall l : list Q,
  H_devsum l == 0 -> SortedQ l.
Proof.
  induction l as [| x xs IH]; intro H.
  - apply sortQ_nil.
  - cbn [H_devsum] in H.
    destruct (xqz_plus_eq0
                (Qabs (x - hd 0 (P0 (x :: xs)))) (H_devsum xs) H
                (QleT'_to_Qle _ _ (abs_nonneg (x - hd 0 (P0 (x :: xs)))))
                (QleT'_to_Qle _ _ (H_shannon_q_nonneg xs))) as [Ha Hs].
    assert (Hxm : x == hd 0 (P0 (x :: xs))).
    { apply qeqT_imp_qeq. apply xqz_sub_eq0. apply qeqT_imp_qeq.
      apply xqz_abs0_eq. apply qeqT_imp_qeq. exact Ha. }
    apply sortQ_cons.
    + apply IH. apply qeqT_imp_qeq. exact Hs.
    + rewrite Forall_forall. intros z Hz.
      apply (Qle_trans x (hd 0 (P0 (x :: xs))) z).
      * apply QleT'_to_Qle. apply xq_Qeq_le. exact Hxm.
      * apply QleT'_to_Qle. apply xqz_P0_hd_min_all. simpl. right. exact Hz.
Qed.

(* 主定理：占位香农偏差熵的零点集 = 升序表
   （正向 = 盘上 xq_H_shannon_sortQ；对照 S6 真频率熵零点 = 常值表） *)
Theorem H_shannon_q_zero_iff_sorted : forall l : list Q,
  And (QeqT (H_devsum l) 0 -> SortedQ l) (SortedQ l -> QeqT (H_devsum l) 0).
Proof.
  intro l. split.
  - intro H. apply qeqT_imp_qeq in H.
    apply H_shannon_q_zero_sorted. exact H.
  - intro Hs. apply xq_H_shannon_sortQ. exact Hs.
Qed.

(* 对照锚（可执行）：[1;2] 升序且是占位熵零点，但非常值表
   ——「占位熵零点 ≠ 真香农零点」的构造性见证（S6 对照面） *)
Theorem zero_locus_contrast_sorted_not_const :
  And (SortedQ [1; 2]) (And (QeqT (H_devsum [1; 2]) 0)
    (Not (sigT (fun a : Q => Forall (fun z => z == a) [1; 2])))).
Proof.
  split.
  - apply (sortQ_cons 1 [2]).
    + apply (sortQ_cons 2 []).
      * apply sortQ_nil.
      * apply Forall_nil.
    + apply Forall_cons; [ unfold Qle; simpl; lia | apply Forall_nil ].
  - split.
    + apply qeq_imp_qeqT. vm_compute. reflexivity.
    + intros [a Hfa]. apply (False_rect Empty_set).
      inversion Hfa as [| z1 zs1 Hz1 Hf1]; subst.
      inversion Hf1 as [| z2 zs2 Hz2 Hf2]; subst.
      assert (H12 : (1 == 2)%Q)
        by (apply (Qeq_trans 1 a 2 Hz1 (Qeq_sym 2 a Hz2))).
      vm_compute in H12. discriminate H12.
Qed.

(* ========== §3 主件A：H_ms == 1 的全同值刻画 ========== *)

(* dedup_aux 消元：成员全同值于 x 时收空（Qmem 口径，不经 In） *)
Lemma xqz_dedup_aux_nil : forall (x : Q) (m : list Q),
  (forall z : Q, Qmem z m -> x == z) -> Id (dedup_aux x m) ([]).
Proof.
  intros x m. induction m as [| y ys IH]; intro Hall; apply eq_imp_id.
  - reflexivity.
  - cbn [dedup_aux].
    assert (HxyI : Id (Qeq_bool x y) true).
    { apply Qeqb_true_of. apply Hall. apply Qmem_refl_cons. }
    assert (Hxy : Qeq_bool x y = true)
      by (destruct (id_sym HxyI); reflexivity).
    rewrite Hxy.
    assert (Hall' : forall z : Q, Qmem z ys -> x == z).
    { intros z Hz. apply Hall. apply (snd (Qmem_cons _ _ _)). right.
      exact Hz. }
    destruct (IH Hall'). reflexivity.
Qed.

(* 全等刻画：H_ms l == 1 ⟹ 任意两成员 Qeq 同值
   （dedup 长度 1 + dedup_Qmem_r 结构，零 In 依赖） *)
Theorem H_ms1_all_eq : forall l : list Q,
  (H_ms l == 1)%Q -> forall a b : Q, Qmem a l -> Qmem b l -> QeqT (a) (b).
Proof.
  intro l. intro H. unfold H_ms in H.
  assert (HI : Id (length (dedup l)) 1%nat)
    by (apply (xq_Zlen_inj1 (length (dedup l))); exact H).
  assert (Hlen : length (dedup l) = 1%nat)
    by (destruct (id_sym HI); reflexivity).
  destruct (xq_len1_el (dedup l) Hlen) as [c Hc].
  intros a b Ha Hb.
  assert (Qa : Qmem a (dedup l)) by (apply dedup_Qmem_r; exact Ha).
  assert (Qb : Qmem b (dedup l)) by (apply dedup_Qmem_r; exact Hb).
  revert Qb. revert Qa. destruct (id_sym Hc). intros Qa Qb.
  destruct (Qmem_cons a c nil) as [Qapc _].
  assert (Qa1 : Or (Id (Qeq_bool a c) true) (Qmem a nil))
    by (apply Qapc; exact Qa).
  destruct (Qmem_cons b c nil) as [Qbpc _].
  assert (Qb1 : Or (Id (Qeq_bool b c) true) (Qmem b nil))
    by (apply Qbpc; exact Qb).
  destruct Qa1 as [QaL | QaR];
    [ | unfold Qmem in QaR; simpl in QaR; inversion QaR ].
  destruct Qb1 as [QbL | QbR];
    [ | unfold Qmem in QbR; simpl in QbR; inversion QbR ].
  apply qeq_imp_qeqT. apply Qeq_bool_eq.
  assert (Ea : Qeq_bool a c = true) by (destruct (id_sym QaL); reflexivity).
  assert (Eb : Qeq_bool b c = true) by (destruct (id_sym QbL); reflexivity).
  assert (Eb' : Qeq_bool c b = true)
    by (destruct (Qeqb_sym b c); exact Eb).
  destruct (Qeqb_trans a c b Ea Eb'). reflexivity.
Qed.

(* 主件A：H_ms == 1 ⟺ 非空且全成员 Qeq 同值（exists-Forall 形） *)
Theorem H_ms1_iff_const : forall l : list Q,
  IffT (QeqT (H_ms l) 1)
       (And (l <> []) (sigT (fun a : Q => Forall (fun z => z == a) l))).
Proof.
  intro l. split.
  - intro H.
    assert (HlenI : Id (length (dedup l)) 1%nat)
      by (unfold H_ms in H; apply xq_Zlen_inj1;
         apply qeqT_imp_qeq; exact H).
    assert (Hlen : length (dedup l) = 1%nat)
      by (destruct (id_sym HlenI); reflexivity).
    destruct (xq_len1_el (dedup l) Hlen) as [c Hc].
    split.
    + intro He. rewrite He in Hc. simpl in Hc. inversion Hc.
    + apply (existT _ c). apply Forall_forall. intros z Hz.
      assert (HcE : dedup l = [c]) by (destruct (id_sym Hc); reflexivity).
      apply qeqT_imp_qeq. apply (xq_dedup1_all_eq l c HcE z Hz).
  - intros [Hne [a Hfa]].
    destruct l as [| x xs]; [ exfalso; apply Hne; reflexivity | ].
    apply qeq_imp_qeqT. unfold H_ms.
    inversion Hfa as [| z0 zs Hzx Hfxs]; subst.
    assert (HdI : Id (dedup_aux x (dedup xs)) []).
    { rewrite Forall_forall in Hfxs.
      apply xqz_dedup_aux_nil. intros z Hz.
      assert (Qxs : Qmem z xs) by (apply (dedup_Qmem_l xs z); exact Hz).
      assert (QxsE : existsb (fun y => Qeq_bool z y) xs = true)
        by (destruct (id_sym Qxs); reflexivity).
      apply existsb_exists in QxsE.
      destruct QxsE as [w [Hw Hzw]].
      apply (Qeq_trans x a z Hzx).
      apply (Qeq_sym z a).
      apply (Qeq_trans z w a (Qeq_bool_eq z w Hzw) (Hfxs w Hw)). }
    assert (Hd : dedup_aux x (dedup xs) = [])
      by (destruct (id_sym HdI); reflexivity).
    unfold H_ms. cbn [dedup length]. rewrite Hd. reflexivity.
Qed.

(* ========== §4 主件B：H_cond 面（非负 iff + 绝对值界 + 零点 iff） ========== *)

(* 反例②（无条件非负为假）的精确 iff 化：缺失前提恰为
   H_devsum ctx <= H_devsum l（盘上 H_cond_nonneg_guarded 的
   双向强化） *)
Theorem H_cond_nonneg_iff : forall l ctx : list Q,
  IffT (QleT' 0 (H_cond l ctx)) (QleT' (H_devsum ctx) (H_devsum l)).
Proof.
  intros l ctx. unfold H_cond. split.
  - intro H. apply (snd (Qle_0_sub' (H_devsum ctx) (H_devsum l))).
    exact H.
  - intro H. apply (fst (Qle_0_sub' (H_devsum ctx) (H_devsum l))).
    exact H.
Qed.

(* 绝对值界（Qabs_triangle）：|H_cond l ctx| <= H_devsum l + H_devsum ctx
   （两熵皆非负，三角和即保守上界；按 H_cond 定义实形选形，无生造） *)
Theorem H_cond_abs_bound : forall l ctx : list Q, QleT' (Qabs (H_cond l ctx)) ((H_devsum l + H_devsum ctx)%Q).
Proof.
  intros l ctx. apply Qle_to_QleT'. unfold H_cond, Qminus.
  apply (Qle_trans _ (Qabs (H_devsum l) + Qabs (- H_devsum ctx))).
  - apply Qabs_triangle.
  - rewrite (qeqT_imp_qeq _ _ (xq_abs_id (H_devsum l)
               (QleT'_to_Qle _ _ (H_shannon_q_nonneg l)))).
    rewrite (qeqT_imp_qeq _ _ (xq_abs_opp (H_devsum ctx))).
    rewrite (qeqT_imp_qeq _ _ (xq_abs_id (H_devsum ctx)
               (QleT'_to_Qle _ _ (H_shannon_q_nonneg ctx)))).
    apply Qle_refl.
Qed.

(* 条件熵零点：H_cond l ctx == 0 ⟺ 两占位熵相等 *)
Theorem H_cond_zero_iff : forall l ctx : list Q,
  IffT (QeqT (H_cond l ctx) 0) (QeqT (H_devsum l) (H_devsum ctx)).
Proof.
  intros l ctx. unfold H_cond. split.
  - intro H. apply qeq_imp_qeqT.
    apply (Qeq_trans (H_devsum l)
                     (H_devsum l - H_devsum ctx + H_devsum ctx) (H_devsum ctx)).
    + ring.
    + pose proof (qeqT_imp_qeq _ _ H) as Hm.
      rewrite Hm at 1. apply Qplus_0_l.
  - intro H. apply qeq_imp_qeqT.
    rewrite <- (qeqT_imp_qeq _ _ H).
    apply (qeqT_imp_qeq _ _ (xq_minus_self (H_devsum l))).
Qed.

(* ========== §5 加分：反例正化收尾 ========== *)

(* 反例①的 restricted 正形：置换不变在「双侧升序」前提恰成立
   （反例 [3;1;2] vs [2;1;3] 的病根 = 置换破坏升序性） *)
Theorem H_shannon_q_perm_inv_if_sorted : forall l p : list Q,
  Permutation l p -> SortedQ l -> SortedQ p -> QeqT (H_devsum l) (H_devsum p).
Proof.
  intros l p _Hp Hl Hpp.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (xq_H_shannon_sortQ l Hl)).
  rewrite (qeqT_imp_qeq _ _ (xq_H_shannon_sortQ p Hpp)).
  reflexivity.
Qed.

(* 反例③的正面孪生：双零点（占位熵零 ∧ 多重集熵 1）⟺ 非空常值表
   （联合零点；⟸ 向组装 H_shannon_q_const_zero + H_ms1_iff_const） *)
Theorem zero_locus_joint : forall l : list Q,
  IffT (And (QeqT (H_devsum l) 0) (QeqT (H_ms l) 1))
       (And (l <> []) (sigT (fun a : Q => Forall (fun z => z == a) l))).
Proof.
  intro l. split.
  - intros [Hh Hm]. exact (fst (H_ms1_iff_const l) Hm).
  - intros [Hne [a Hfa]]. split.
    + apply (H_shannon_q_const_zero a l Hfa).
    + apply (snd (H_ms1_iff_const l)). split.
      * exact Hne.
      * apply (existT _ a). exact Hfa.
Qed.

(* ============================================================
   §A6 果实件 F2：F6 频数拼接单调族
   盘面现役件组合（零生造）：§3 freq_q_app（拼接频数可加）×
   §4 nsum / §5 sqsum / nmax 面。
   保底件两件：
   · sqsum_app_ge_l / sqsum_app_ge_r：sqsum (l1++l2) >= sqsum l1
     （及右）——拼接后逐点频数增大 + 支撑并集，碰撞和质量只增不减。
   加分件：
   · sqsum_app_eq：精确交叉项分解
       sqsum (l1++l2) = sqsum l1 + sqsum l2
                        + Σ_{x∈l1} freq_q x l2 + Σ_{x∈l2} freq_q x l1。
   随行面：
   · sqsum_app_ge_sum：质量面 sqsum l1 + sqsum l2 <= sqsum (l1++l2)；
   · maxcount_app_ge_l / _r：频数极值面（collide/maxfreq 共享分子）。
   诚实障碍（构造反例钉界，禁特设构造）：H_freq/collide 的拼接单调
   「不成立」：H_freq ([0]++[1]) = 1/2 > 0 = H_freq [0]；collide [0]
   = 1 > 1/2 = collide ([0]++[1])。根因：sqsum 单调（分子增）的同时
   分母 n² 同步增大，归一化商无定向——任务卡条件句「H_freq
   (l1++l2) <= H_freq l1 型若 sqsum 单调成立即随行」之前件不蕴含
   后件，如实以 H_freq_app_mono_false / collide_app_mono_false 闭合。
   ============================================================ *)

(* ---------- §A6.0 承重件：nsum 拼接可加 / 逐点可加 ---------- *)

Lemma nsum_app : forall (f : Q -> nat) (l p : list Q), Id (nsum f (l ++ p)) ((nsum f l + nsum f p)%nat).
Proof.
  intros f l p. apply eq_imp_id. induction l as [| a l IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma nsum_add : forall (f g : Q -> nat) (l : list Q), Id (nsum (fun x => (f x + g x)%nat) l) ((nsum f l + nsum g l)%nat).
Proof.
  intros f g l. apply eq_imp_id. induction l as [| a l IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

(* ---------- §A6.1 保底件：sqsum 拼接单调两件 ---------- *)

Theorem sqsum_app_ge_l : forall l1 l2 : list Q, NatLe (sqsum l1) ((sqsum (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. unfold sqsum. rewrite nsum_app.
  assert (H1 : (nsum (fun x => freq_q x l1) l1
                <= nsum (fun x => freq_q x (l1 ++ l2)) l1)%nat).
  { apply NatLe_drop. apply nsum_le. intros x _.
    destruct (id_sym (freq_q_app x l1 l2)). lia. }
  lia.
Qed.

Theorem sqsum_app_ge_r : forall l1 l2 : list Q, NatLe (sqsum l2) ((sqsum (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. unfold sqsum. rewrite nsum_app.
  assert (H2 : (nsum (fun x => freq_q x l2) l2
                <= nsum (fun x => freq_q x (l1 ++ l2)) l2)%nat).
  { apply NatLe_drop. apply nsum_le. intros x _.
    destruct (id_sym (freq_q_app x l1 l2)). lia. }
  lia.
Qed.

(* ---------- §A6.2 加分件：sqsum 拼接精确交叉项分解 ---------- *)

Theorem sqsum_app_eq : forall l1 l2 : list Q, Id (sqsum (l1 ++ l2)) ((sqsum l1 + sqsum l2
   + nsum (fun x => freq_q x l2) l1
   + nsum (fun x => freq_q x l1) l2)%nat).
Proof.
  intros l1 l2. apply eq_imp_id. unfold sqsum. rewrite nsum_app.
  assert (Hext1 : forall x : Q, In x l1 ->
    freq_q x (l1 ++ l2) = (freq_q x l1 + freq_q x l2)%nat).
  { intros x _. destruct (id_sym (freq_q_app x l1 l2)). reflexivity. }
  assert (Hext2 : forall x : Q, In x l2 ->
    freq_q x (l1 ++ l2) = (freq_q x l1 + freq_q x l2)%nat).
  { intros x _. destruct (id_sym (freq_q_app x l1 l2)). reflexivity. }
  rewrite (nsum_ext_in (fun x => freq_q x (l1 ++ l2))
                       (fun x => (freq_q x l1 + freq_q x l2)%nat) l1 Hext1).
  rewrite (nsum_ext_in (fun x => freq_q x (l1 ++ l2))
                       (fun x => (freq_q x l1 + freq_q x l2)%nat) l2 Hext2).
  rewrite (nsum_add (fun x => freq_q x l1) (fun x => freq_q x l2) l1),
          (nsum_add (fun x => freq_q x l1) (fun x => freq_q x l2) l2).
  lia.
Qed.

(* 质量面随行：两段碰撞质量之和不超拼接碰撞质量（交叉项非负） *)
Corollary sqsum_app_ge_sum : forall l1 l2 : list Q, NatLe (sqsum l1 + sqsum l2) ((sqsum (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. rewrite (sqsum_app_eq l1 l2). lia.
Qed.

(* ---------- §A6.3 随行面：maxcount 极值拼接单调（分子面） ---------- *)

Lemma nmax_app : forall (f : Q -> nat) (l p : list Q), Id (nmax f (l ++ p)) (Nat.max (nmax f l) (nmax f p)).
Proof.
  intros f l p. apply eq_imp_id. induction l as [| a l IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma nmax_le_app_l : forall (f : Q -> nat) (l p : list Q), NatLe (nmax f l) ((nmax f (l ++ p))%nat).
Proof.
  intros f l p. apply NatLe_lift. rewrite nmax_app. apply Nat.le_max_l.
Qed.

Lemma nmax_le_app_r : forall (f : Q -> nat) (l p : list Q), NatLe (nmax f l) ((nmax f (p ++ l))%nat).
Proof.
  intros f l p. apply NatLe_lift. rewrite nmax_app. apply Nat.le_max_r.
Qed.

Lemma nmax_mono : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> (f x <= g x)%nat) -> NatLe (nmax f l) ((nmax g l)%nat).
Proof.
  intros f g l. induction l as [| a t IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (H1 : (f a <= g a)%nat) by (apply H; left; reflexivity).
    assert (H2 : NatLe (nmax f t) (nmax g t))
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ H2). lia.
Qed.

Theorem maxcount_app_ge_l : forall l1 l2 : list Q, NatLe (maxcount l1) ((maxcount (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. unfold maxcount.
  apply (Nat.le_trans (nmax (fun x => freq_q x l1) l1)
                      (nmax (fun x => freq_q x (l1 ++ l2)) l1)
                      (nmax (fun x => freq_q x (l1 ++ l2)) (l1 ++ l2))).
  - apply NatLe_drop.
    apply (nmax_mono (fun x => freq_q x l1)
                     (fun x => freq_q x (l1 ++ l2)) l1).
    intros x _. destruct (id_sym (freq_q_app x l1 l2)). lia.
  - exact (NatLe_drop _ _ (nmax_le_app_l (fun x => freq_q x (l1 ++ l2)) l1 l2)).
Qed.

Theorem maxcount_app_ge_r : forall l1 l2 : list Q, NatLe (maxcount l2) ((maxcount (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. unfold maxcount.
  apply (Nat.le_trans (nmax (fun x => freq_q x l2) l2)
                      (nmax (fun x => freq_q x (l1 ++ l2)) l2)
                      (nmax (fun x => freq_q x (l1 ++ l2)) (l1 ++ l2))).
  - apply NatLe_drop.
    apply (nmax_mono (fun x => freq_q x l2)
                     (fun x => freq_q x (l1 ++ l2)) l2).
    intros x _. destruct (id_sym (freq_q_app x l1 l2)). lia.
  - exact (NatLe_drop _ _ (nmax_le_app_r (fun x => freq_q x (l1 ++ l2)) l2 l1)).
Qed.

(* ---------- §A6.4 诚实障碍：归一化商面拼接无定向（反例钉界） ---------- *)

(* 具体值面（vm_compute 闭合，供反例改写使用） *)
Lemma H_freq_01_val : QeqT (H_freq [0;1]) (1#2)%Q.
Proof. apply qeq_imp_qeqT. unfold H_freq. vm_compute. reflexivity. Qed.

Lemma H_freq_0_val : QeqT (H_freq [0]) 0%Q.
Proof. apply qeq_imp_qeqT. unfold H_freq. vm_compute. reflexivity. Qed.

Lemma collide_01_val : QeqT (collide [0;1]) (1#2)%Q.
Proof. apply qeq_imp_qeqT. unfold collide. vm_compute. reflexivity. Qed.

Lemma collide_0_val : QeqT (collide [0]) 1%Q.
Proof. apply qeq_imp_qeqT. unfold collide. vm_compute. reflexivity. Qed.

(* H_freq 拼接单调不成立：加一异值元素使熵增
   （0 < H_freq [0;1] = 1/2 与 H : 1/2 <= 0 相撞） *)
Lemma H_freq_app_mono_false :
  Not (forall l1 l2 : list Q, QleT' (H_freq (l1 ++ l2)) (H_freq l1)).
Proof.
  intro H. specialize (H [0] [1]). apply QleT'_to_Qle in H.
  assert (Hn : H_freq ([0] ++ [1]) == H_freq [0;1]) by reflexivity.
  rewrite Hn in H. rewrite (qeqT_imp_qeq _ _ H_freq_01_val) in H.
  rewrite (qeqT_imp_qeq _ _ H_freq_0_val) in H.
  assert (Hgt : 0%Q < (1#2)%Q) by (unfold Qlt; simpl; lia).
  exact (False_rect Empty_set
    (Qlt_irrefl 0%Q (Qlt_le_trans 0%Q (1#2)%Q 0%Q Hgt H))).
Qed.

(* collide 拼接下有向单调不成立：全同值表加异值元素使碰撞熵减
   （H : 1 <= 1/2 与 1/2 < 1 相撞） *)
Lemma collide_app_mono_false :
  Not (forall l1 l2 : list Q, QleT' (collide l1) (collide (l1 ++ l2))).
Proof.
  intro H. specialize (H [0] [1]). apply QleT'_to_Qle in H.
  assert (Hn : collide ([0] ++ [1]) == collide [0;1]) by reflexivity.
  rewrite Hn in H. rewrite (qeqT_imp_qeq _ _ collide_01_val) in H.
  rewrite (qeqT_imp_qeq _ _ collide_0_val) in H.
  assert (Hlt : (1#2)%Q < 1%Q) by (unfold Qlt; simpl; lia).
  exact (False_rect Empty_set
    (Qlt_irrefl 1%Q (Qle_lt_trans 1%Q (1#2)%Q 1%Q H Hlt))).
Qed.

(* AUDIT-2 审计 A1/A2（F4）闭合：恒等占位 align_lambda（本文件 L86 区）
   保留原名原义零改动（Rotation §S7 救活块四件现役使用，签名零波及，
   调度件路径-steering 裁决＝双件共存）；本区新增真定义 align_lambda_opt
   —— h0/h1 双熵输入的最优 λ 选择器（if Qle_bool h0 h1 then 1 else 0）。
   跨文件对账注记（加分面）：与 DTPT_Rotation.v §S7 的 lam_opt（定义
   逐字同构）/§M3 归并段 lam_opt_cyc（lam_opt 的周期族别名，L1929：
   lam_opt_cyc h0 hk := lam_opt h0 hk）同构语义。Entropy 先于 Rotation
   编译（Rotation Require 本文件），不可反向 Require 复用 lam_opt，
   故本区独立给出同语义本体；定理面与 Rotation 侧 lam_opt_values /
   lam_opt_range / lam_opt_min（H_lam 使用形＝H_lam_lam_opt_min）逐条
   同型，陈述以盘面现役形为准。 *)

Definition align_lambda_opt (h0 h1 : Q) : Q := if Qle_bool h0 h1 then 1 else 0.

(* 两分支取值面：端点选择器恒取 λ 值 1 或 0（两分支各一构造）。 *)
Theorem align_lambda_opt_values : forall h0 h1 : Q,
  Or (Id (align_lambda_opt h0 h1) 1%Q) (Id (align_lambda_opt h0 h1) 0%Q).
Proof.
  intros h0 h1. unfold align_lambda_opt.
  destruct (Qle_bool h0 h1).
  - left. apply eq_imp_id. reflexivity.
  - right. apply eq_imp_id. reflexivity.
Qed.

(* 值域 {0,1} 面：选择器像含于 [0,1]（经 values 面 + 字面 Qle 装配）。 *)
Theorem align_lambda_opt_range : forall h0 h1 : Q,
  And (QleT' 0 (align_lambda_opt h0 h1)) (QleT' (align_lambda_opt h0 h1) 1).
Proof.
  intros h0 h1. destruct (align_lambda_opt_values h0 h1) as [E | E].
  - destruct (id_sym E). split.
    + exact (xq_Qle_bool_le 0 1 eq_refl).
    + apply Qle_to_QleT'. apply Qle_refl.
  - destruct (id_sym E). split.
    + apply Qle_to_QleT'. apply Qle_refl.
    + exact (xq_Qle_bool_le 0 1 eq_refl).
Qed.

(* 最优性（H_lam 使用形·主件）：端点选择器的混合熵不超过 [0,1] 内
   任意 λ 的混合熵。两分支各化归一次乘法非负装配（仿射差分路线，
   与 Rotation §S7 lam_opt_min 同型）：
   h0 <= h1 分支取 λ* = 1，差 = (1-lam)·(h1-h0)；
   否则取 λ* = 0，差 = lam·(h0-h1)。 *)
Theorem align_lambda_opt_min : forall (l : list Q) (s : nat) (lam : Q),
  (0 <= lam <= 1)%Q -> QleT' (H_lam l s (align_lambda_opt (H_adj (P0 l)) (H_adj (Pinf l s)))) (H_lam l s lam).
Proof.
  intros l s lam H01. apply Qle_to_QleT'. destruct H01 as [Hlam0 Hlam1].
  unfold H_lam, align_lambda_opt.
  destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))) eqn:E.
  - (* h0 <= h1：λ* = 1，最优值 = h0 *)
    assert (Hd : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                       - (1 * H_adj (P0 l) + (1 - 1) * H_adj (Pinf l s)))%Q).
    { assert (Er : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - (1 * H_adj (P0 l) + (1 - 1) * H_adj (Pinf l s))
                 == (1 - lam) * (H_adj (Pinf l s) - H_adj (P0 l))) by ring.
      rewrite Er. apply QleT'_to_Qle. apply xq_mul_nonneg.
      + apply QleT'_to_Qle. apply (fst (Qle_0_sub' lam 1)).
        apply Qle_to_QleT'. exact Hlam1.
      + apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
        apply xq_Qle_bool_le. exact E. }
    apply QleT'_to_Qle. apply (snd (Qle_0_sub' _ _)). apply Qle_to_QleT'. exact Hd.
  - (* h0 > h1：λ* = 0，最优值 = h1 *)
    assert (Hge : (H_adj (Pinf l s) <= H_adj (P0 l))%Q)
      by (apply QleT'_to_Qle; apply Qle_bool_false_le; exact E).
    assert (Hd : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                       - (0 * H_adj (P0 l) + (1 - 0) * H_adj (Pinf l s)))%Q).
    { assert (Er : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - (0 * H_adj (P0 l) + (1 - 0) * H_adj (Pinf l s))
                 == lam * (H_adj (P0 l) - H_adj (Pinf l s))) by ring.
      rewrite Er. apply QleT'_to_Qle. apply xq_mul_nonneg.
      + exact Hlam0.
      + apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
        apply Qle_to_QleT'. exact Hge. }
    apply QleT'_to_Qle. apply (snd (Qle_0_sub' _ _)). apply Qle_to_QleT'. exact Hd.
Qed.

(* 端点求值桥（随行加分）：选择器的混合熵取值恒为某一端的相熵
   （使用「端点 3」H_lam_lam1 / H_lam_lam0）。 *)
Theorem align_lambda_opt_endpoint : forall (l : list Q) (s : nat),
  Or (QeqT (H_lam l s (align_lambda_opt (H_adj (P0 l)) (H_adj (Pinf l s))))
           (H_adj (P0 l)))
     (QeqT (H_lam l s (align_lambda_opt (H_adj (P0 l)) (H_adj (Pinf l s))))
           (H_adj (Pinf l s))).
Proof.
  intros l s.
  destruct (align_lambda_opt_values (H_adj (P0 l)) (H_adj (Pinf l s)))
    as [E | E].
  - left. destruct (id_sym E). apply H_lam_lam1.
  - right. destruct (id_sym E). apply H_lam_lam0.
Qed.

(* ============================================================
   §A8 果实件 F5：F6 深化——拼接精确卷积式
   熵族拼接卷积的完整恒等式（论文 α §4 熵族节闭合定理位）。
   使用（零生造）：§3 freq_q_app / §4 nsum 面 / §A6 sqsum_app_eq
   （交叉项精确分解，对账使用）× §6 collide / H_freq 定义 +
   H_freq_eq_bridge（H_freq == 1 − collide 桥面，field 路线先例）。
   全件先 vm_compute 数值检验验真值再落笔（FRUIT-2 假命题教训），
   检验以 *_val 件永久在册（§A8.4）。
   诚实边界：collide/H_freq 卷积式取 n1、n2 双非空卫哨——field
   路线需全部商分母非零；n1=0/n2=0 退化面中 w=0 商恒零使恒等式
   仍真，但归一化拼接无定向已由 §A6 H_freq_app_mono_false /
   collide_app_mono_false 反例钉界，本件不扩张卫哨外陈述。
   ============================================================ *)

(* ---------- §A8.0 卷积代数小件 ---------- *)

(* Q 无零因子面（field 侧条件供件）：非零 × 非零 ≠ 0 *)
Lemma qmul_neq0 : forall x y : Q,
  ~ (x == 0) -> ~ (y == 0) -> Not (QeqT (x * y) 0).
Proof.
  intros [xn xd] [yn yd] Hx Hy Hxy. apply qeqT_imp_qeq in Hxy.
  assert (Hxn : (xn <> 0)%Z).
  { intros Hz. apply Hx. unfold Qeq. simpl. rewrite Hz. reflexivity. }
  assert (Hyn : (yn <> 0)%Z).
  { intros Hz. apply Hy. unfold Qeq. simpl. rewrite Hz. reflexivity. }
  unfold Qeq, Qmult in Hxy. simpl in Hxy.
  rewrite ? Z.mul_1_r in Hxy.
  apply Z.mul_eq_0 in Hxy.
  exfalso. destruct Hxy as [E | E]; [exact (Hxn E) | exact (Hyn E)].
Qed.

(* 指示器求和 = 频数（nsum 与 freq_q 的换基桥） *)
Lemma nsum_freq_q_ind : forall (a : Q) (l : list Q), Id (nsum (fun x => if Qeq_bool x a then 1%nat else 0%nat) l) (freq_q a l).
Proof.
  intros a l. apply eq_imp_id. induction l as [| y ys IH].
  - reflexivity.
  - simpl. rewrite IH.
    destruct (Qeq_bool y a) eqn:E1; destruct (Qeq_bool a y) eqn:E2; try lia.
    + exfalso.
      assert (C : Qeq_bool a y = true).
      { apply (proj2 (Qeq_bool_iff a y)). apply Qeq_sym.
        apply (proj1 (Qeq_bool_iff y a)). exact E1. }
      rewrite C in E2. discriminate.
    + exfalso.
      assert (C : Qeq_bool y a = true).
      { apply (proj2 (Qeq_bool_iff y a)). apply Qeq_sym.
        apply (proj1 (Qeq_bool_iff a y)). exact E2. }
      rewrite C in E1. discriminate.
Qed.

(* ---------- §A8.1 保底件：交叉项显式形 + 对称双和 ---------- *)

(* 对账件：与 §A6 sqsum_app_eq 同形（freq_q_app 双侧展开 + nsum
   分配的精确交叉项分解），依调度令以 sqsum_app_cross 之名在册
   （保底名位），本体使用 §A6 主定理零重证。 *)
Theorem sqsum_app_cross : forall l1 l2 : list Q, Id (sqsum (l1 ++ l2)) ((sqsum l1 + sqsum l2
   + nsum (fun x => freq_q x l2) l1
   + nsum (fun x => freq_q x l1) l2)%nat).
Proof. intros l1 l2. apply eq_imp_id. destruct (sqsum_app_eq l1 l2). reflexivity. Qed.

(* 对称双和：两交叉项相等（同计配对集 {(p,q)∈l1×l2 : p==q}）——
   审计 F6 预告件，卷积式标准化 2X 形的承重面。 *)
Theorem sqsum_cross_sym : forall l1 l2 : list Q, Id (nsum (fun x => freq_q x l2) l1) ((nsum (fun x => freq_q x l1) l2)%nat).
Proof.
  intros l1. induction l1 as [| a t IH]; intros l2; apply eq_imp_id.
  - cbn [nsum]. symmetry.
    rewrite (nsum_ext_in (fun x : Q => freq_q x []) (fun _ : Q => 0%nat) l2
               (fun x _ => eq_refl)).
    pose proof (nsum_const 0%nat l2) as HC. rewrite HC. lia.
  - cbn [nsum].
    assert (Eext : forall x : Q,
      freq_q x (a :: t) = (freq_q x t + (if Qeq_bool x a then 1%nat else 0%nat))%nat).
    { intros x. simpl. destruct (Qeq_bool x a); lia. }
    rewrite (nsum_ext_in (fun x : Q => freq_q x (a :: t))
              (fun x : Q => (freq_q x t + (if Qeq_bool x a then 1%nat else 0%nat))%nat)
              l2 (fun x _ => Eext x)).
    rewrite nsum_add.
    rewrite (nsum_freq_q_ind a l2).
    rewrite IH. lia.
Qed.

(* 标准化 2X 形：交叉项以对称双和归并（sqsum_app_cross + cross_sym） *)
Theorem sqsum_app_eq2 : forall l1 l2 : list Q, Id (sqsum (l1 ++ l2)) ((sqsum l1 + sqsum l2 + 2 * nsum (fun x => freq_q x l2) l1)%nat).
Proof.
  intros l1 l2. apply eq_imp_id. rewrite (sqsum_app_cross l1 l2).
  rewrite (sqsum_cross_sym l1 l2). lia.
Qed.

(* ---------- §A8.2 主定理件：collide 拼接卷积（加权精确式） ---------- *)

(* collide (l1++l2) = (n1/(n1+n2))²·collide l1 + (n2/(n1+n2))²·collide l2
   + (Σ_{x∈l1} freq_q x l2 + Σ_{x∈l2} freq_q x l1)/(n1+n2)²。
   权重平方型加权组合 + 交叉修正项；非空卫哨 n1,n2（field 路线）。 *)
Theorem collide_app_eq : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat -> QeqT (collide (l1 ++ l2)) ((qn (length l1) / qn (length l1 + length l2)%nat)
      * (qn (length l1) / qn (length l1 + length l2)%nat) * collide l1
    + (qn (length l2) / qn (length l1 + length l2)%nat)
      * (qn (length l2) / qn (length l1 + length l2)%nat) * collide l2
    + (qn (nsum (fun x => freq_q x l2) l1)
       + qn (nsum (fun x => freq_q x l1) l2))
      / (qn (length l1 + length l2)%nat * qn (length l1 + length l2)%nat)).
Proof.
  intros l1 l2 H1 H2.
  apply qeq_imp_qeqT.
  unfold collide.
  rewrite length_app.
  rewrite (sqsum_app_eq l1 l2).
  assert (qn_addP : forall a b : nat, qn (a + b)%nat == qn a + qn b)
    by (intros a b; exact (qeqT_imp_qeq _ _ (qn_add a b))).
  rewrite ! qn_addP.
  assert (Hnn : (0 < length l1 + length l2)%nat) by lia.
  assert (HN : ~ (qn (length l1 + length l2)%nat == 0)).
  { intro Hc. destruct (qpos_neq0 (qn (length l1 + length l2)%nat)
      (QltT_to_Qlt 0 (qn (length l1 + length l2)%nat) (qn_pos _ Hnn))
      (qeq_imp_qeqT _ _ Hc)). }
  assert (Ha : ~ (qn (length l1) == 0)).
  { intro Hc. destruct (qpos_neq0 (qn (length l1))
      (QltT_to_Qlt 0 (qn (length l1)) (qn_pos _ H1))
      (qeq_imp_qeqT _ _ Hc)). }
  assert (Hb : ~ (qn (length l2) == 0)).
  { intro Hc. destruct (qpos_neq0 (qn (length l2))
      (QltT_to_Qlt 0 (qn (length l2)) (qn_pos _ H2))
      (qeq_imp_qeqT _ _ Hc)). }
  assert (HPP1 : ~ (qn (length l1) * qn (length l1) == 0)).
  { intro Hc. destruct (qmul_neq0 (qn (length l1)) (qn (length l1)) Ha Ha
         (qeq_imp_qeqT _ _ Hc)). }
  assert (HPP2 : ~ (qn (length l2) * qn (length l2) == 0)).
  { intro Hc. destruct (qmul_neq0 (qn (length l2)) (qn (length l2)) Hb Hb
         (qeq_imp_qeqT _ _ Hc)). }
  assert (HN2 : ~ (qn (length l1) + qn (length l2) == 0)).
  { intro Zc. apply HN.
    rewrite (qeqT_imp_qeq _ _ (qn_add (length l1) (length l2))). exact Zc. }
  assert (HNN2 : ~ ((qn (length l1) + qn (length l2))
                    * (qn (length l1) + qn (length l2)) == 0)).
  { intro Hc.
    destruct (qmul_neq0 (qn (length l1) + qn (length l2))
      (qn (length l1) + qn (length l2)) HN2 HN2
      (qeq_imp_qeqT _ _ Hc)). }
  field; repeat split; assumption.
Qed.

(* ---------- §A8.3 主件：H_freq 拼接卷积（加权 + 2w1w2 交叉修正） ---------- *)

(* H_freq (l1++l2) = w1²·H_freq l1 + w2²·H_freq l2 + 2·w1·w2
                     − (Σ_{x∈l1} freq_q x l2 + Σ_{x∈l2} freq_q x l1)/(n1+n2)²。
   使用 collide_app_eq + H_freq_eq_bridge（== 1 − collide）；
   交叉修正项 2·w1·w2 − X/(n1+n2)² 非负有界（2(n1n2−X)/(n1+n2)² ≥ 0，
   X ≤ n1·n2 经 freq_q_le_length 逐点），熵族拼接卷积完整恒等式。 *)
Theorem H_freq_app_eq : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat -> QeqT (H_freq (l1 ++ l2)) ((qn (length l1) / qn (length l1 + length l2)%nat)
      * (qn (length l1) / qn (length l1 + length l2)%nat) * H_freq l1
    + (qn (length l2) / qn (length l1 + length l2)%nat)
      * (qn (length l2) / qn (length l1 + length l2)%nat) * H_freq l2
    + 2 * (qn (length l1) / qn (length l1 + length l2)%nat)
        * (qn (length l2) / qn (length l1 + length l2)%nat)
    - (qn (nsum (fun x => freq_q x l2) l1)
       + qn (nsum (fun x => freq_q x l1) l2))
      / (qn (length l1 + length l2)%nat * qn (length l1 + length l2)%nat)).
Proof.
  intros l1 l2 H1 H2.
  apply qeq_imp_qeqT.
  assert (Hnn : (0 < length (l1 ++ l2))%nat) by (rewrite length_app; lia).
  assert (Hnn2 : (0 < length l1 + length l2)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (H_freq_eq_bridge (l1 ++ l2) Hnn)). unfold H_min_q.
  rewrite (qeqT_imp_qeq _ _ (collide_app_eq l1 l2 H1 H2)).
  assert (B1 : collide l1 == 1 - H_freq l1).
  { pose proof (qeqT_imp_qeq _ _ (H_freq_eq_bridge l1 H1)) as T.
    unfold H_min_q in T. rewrite T. ring. }
  assert (B2 : collide l2 == 1 - H_freq l2).
  { pose proof (qeqT_imp_qeq _ _ (H_freq_eq_bridge l2 H2)) as T.
    unfold H_min_q in T. rewrite T. ring. }
  rewrite B1, B2.
  rewrite (qeqT_imp_qeq _ _ (qn_add (length l1) (length l2))).
  assert (HN2 : ~ (qn (length l1) + qn (length l2) == 0)).
  { intro Hc.
    rewrite <- (qeqT_imp_qeq _ _ (qn_add (length l1) (length l2))) in Hc.
    destruct (qpos_neq0 (qn (length l1 + length l2)%nat)
      (QltT_to_Qlt 0 (qn (length l1 + length l2)%nat) (qn_pos _ Hnn2))
      (qeq_imp_qeqT _ _ Hc)). }
  assert (HNN2 : ~ ((qn (length l1) + qn (length l2))
                    * (qn (length l1) + qn (length l2)) == 0)).
  { intro Hc.
    destruct (qmul_neq0 (qn (length l1) + qn (length l2))
      (qn (length l1) + qn (length l2)) HN2 HN2
      (qeq_imp_qeqT _ _ Hc)). }
  field; repeat split; assumption.
Qed.

(* ---------- §A8.4 加分件：三段拼接结合律卷积一致性（值面） ---------- *)

(* (l1++l2)++l3 与 l1++(l2++l3) 同表（app_assoc 定义性），故三个
   卷积量在两种分组下逐点重合——卷积式对三段拼接的一致性闭合面。 *)
Theorem sqsum_app_assoc : forall (l1 l2 l3 : list Q), Id (sqsum ((l1 ++ l2) ++ l3)) (sqsum (l1 ++ (l2 ++ l3))).
Proof. intros l1 l2 l3. apply eq_imp_id. rewrite <- app_assoc. reflexivity. Qed.

Theorem collide_app_assoc : forall (l1 l2 l3 : list Q),
  QeqT (collide ((l1 ++ l2) ++ l3)) (collide (l1 ++ (l2 ++ l3))).
Proof. intros l1 l2 l3. apply qeq_imp_qeqT.
  rewrite <- app_assoc. reflexivity. Qed.

Theorem H_freq_app_assoc : forall (l1 l2 l3 : list Q),
  QeqT (H_freq ((l1 ++ l2) ++ l3)) (H_freq (l1 ++ (l2 ++ l3))).
Proof. intros l1 l2 l3. apply qeq_imp_qeqT.
  rewrite <- app_assoc. reflexivity. Qed.

(* ---------- §A8.5 数值锚（vm_compute 检验件；G3 对账表用） ---------- *)

(* 检验实例：l1 = [0;1]，l2 = [1;1]（含非平凡交叉项 X1 = X2 = 2）。
   实测：sqsum (l1++l2) = 10，collide = 5/8，H_freq = 3/8；
   两主定理 RHS 加权式逐一求值同值——陈述形先验为真再落笔的记录件。 *)
Lemma sqsum_app_cross_val : Id (sqsum ([0;1] ++ [1;1])) (10%nat).
Proof. apply eq_imp_id.
  change (sqsum [0; 1; 1; 1] = 10%nat).
  change (nsum (fun x => freq_q x [0; 1; 1; 1]) [0; 1; 1; 1] = 10%nat).
  change (Nat.add (freq_q 0 [0; 1; 1; 1])
            (Nat.add (freq_q 1 [0; 1; 1; 1])
               (Nat.add (freq_q 1 [0; 1; 1; 1])
                  (Nat.add (freq_q 1 [0; 1; 1; 1]) 0%nat))) = 10%nat).
  change ((1 + (3 + (3 + (3 + 0))))%nat = 10%nat).
  reflexivity.
Qed.

Lemma sqsum_cross_sym_val : Id (nsum (fun x => freq_q x [1;1]) [0;1]) (nsum (fun x => freq_q x [0;1]) [1;1]).
Proof. apply eq_imp_id.
  change (Nat.add (freq_q 0 [1; 1]) (freq_q 1 [1; 1])
          = Nat.add (freq_q 1 [0; 1]) (freq_q 1 [0; 1])).
  change ((0 + 2)%nat = (1 + 1)%nat).
  reflexivity.
Qed.

Lemma collide_app_eq_val : QeqT (collide ([0;1] ++ [1;1])) (5#8)%Q.
Proof. apply qeq_imp_qeqT. unfold collide. vm_compute. reflexivity. Qed.

Lemma collide_app_eq_rhs_val : QeqT ((qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat)
    * (qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat) * collide [0;1]
  + (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat)
    * (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat) * collide [1;1]
  + (qn (nsum (fun x => freq_q x [1;1]) [0;1])
     + qn (nsum (fun x => freq_q x [0;1]) [1;1]))
    / (qn (length [0;1] + length [1;1])%nat
       * qn (length [0;1] + length [1;1])%nat)) ((5#8)%Q).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Lemma H_freq_app_eq_val : QeqT (H_freq ([0;1] ++ [1;1])) (3#8)%Q.
Proof. apply qeq_imp_qeqT. unfold H_freq. vm_compute. reflexivity. Qed.

Lemma H_freq_app_eq_rhs_val : QeqT ((qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat)
    * (qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat) * H_freq [0;1]
  + (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat)
    * (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat) * H_freq [1;1]
  + 2 * (qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat)
      * (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat)
  - (qn (nsum (fun x => freq_q x [1;1]) [0;1])
     + qn (nsum (fun x => freq_q x [0;1]) [1;1]))
    / (qn (length [0;1] + length [1;1])%nat
       * qn (length [0;1] + length [1;1])%nat)) ((3#8)%Q).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

End DTPT_Entropy.

Import DTPT_Entropy.

(* ========== 审计：零公理实证（M3 归并后 15 件并档） ========== *)

Print Assumptions freq_q_app.
Print Assumptions freq_q_perm.
Print Assumptions H_freq_perm.
Print Assumptions H_freq_nonneg.
Print Assumptions H_freq_all_same_zero.
Print Assumptions H_freq_len_le_1.
Print Assumptions H_freq_eq0_all_same.
Print Assumptions freq_q_map.
Print Assumptions freq_q_map_ge.
Print Assumptions sqsum_map_ge.
Print Assumptions H_freq_dpi.
Print Assumptions H_freq_map_id.
Print Assumptions H_freq_map_const.
Print Assumptions H_freq_map_twice.
Print Assumptions H_freq_map_chain.

(* ========== 审计：零公理面实证 ========== *)

Print Assumptions collide_lower.
Print Assumptions collide_upper.
Print Assumptions collide_le_maxfreq.
Print Assumptions maxfreq_lower.
Print Assumptions maxfreq_upper.
Print Assumptions H_freq_eq_bridge.
Print Assumptions H_max_q_anti.
Print Assumptions H_chain.
Print Assumptions maxfreq_perm.
Print Assumptions collide_perm.
Print Assumptions H_max_q_perm.
Print Assumptions H_min_q_perm.

(* ========== 审计：S4 并入件零公理实证（ME2 4 件 + ZeroLocus 4 件） ========== *)

Print Assumptions me_cert.
Print Assumptions mkMEval_gate_bridge.
Print Assumptions mkMEval_Hcond_count_ub.
Print Assumptions me_total_ub.
Print Assumptions H_shannon_q_zero_iff_sorted.
Print Assumptions H_ms1_iff_const.
Print Assumptions H_cond_abs_bound.
Print Assumptions zero_locus_joint.


Print Assumptions sqsum_app_ge_l.
Print Assumptions sqsum_app_ge_r.
Print Assumptions sqsum_app_eq.
Print Assumptions sqsum_app_ge_sum.
Print Assumptions maxcount_app_ge_l.
Print Assumptions maxcount_app_ge_r.
Print Assumptions H_freq_app_mono_false.
Print Assumptions collide_app_mono_false.


Print Assumptions align_lambda_opt_values.
Print Assumptions align_lambda_opt_range.
Print Assumptions align_lambda_opt_min.
Print Assumptions align_lambda_opt_endpoint.


Print Assumptions qmul_neq0.
Print Assumptions nsum_freq_q_ind.
Print Assumptions sqsum_app_cross.
Print Assumptions sqsum_cross_sym.
Print Assumptions sqsum_app_eq2.
Print Assumptions collide_app_eq.
Print Assumptions H_freq_app_eq.
Print Assumptions sqsum_app_assoc.
Print Assumptions collide_app_assoc.
Print Assumptions H_freq_app_assoc.
Print Assumptions sqsum_app_cross_val.
Print Assumptions sqsum_cross_sym_val.
Print Assumptions collide_app_eq_val.
Print Assumptions collide_app_eq_rhs_val.
Print Assumptions H_freq_app_eq_val.
Print Assumptions H_freq_app_eq_rhs_val.

(* ============================================================
   归并棒 S3退役记录：DTPT_EntFam2.v
   —— 并入本文件 §A3 后退役；实测全工作区零使用者（对全部活体
   .v grep Require/Import 零命中），源件五件产物以 .retired_S3
   前缀快照留存。
   同棒并入源 DTPT_Entropy2.v 保留不退役：下游 DTPT_RotSpec.v
   的 Require/Import 在册（任务卡预警的 DTPT_Cyc.v 经实测无
   Entropy2 Require，Entropy2 下游仅 RotSpec 一件，如实说明），
   随棒 5/6 并入 DTPT_Rotation 时自然消化，届时再退役。
   ============================================================ *)

(* ============================================================
   归并棒 S4退役记录：DTPT_ME2.v 与 DTPT_ZeroLocus.v
   —— 分别并入本文件 §A4/§A5 后退役；实测全工作区对两源
   Require/Import 零使用者（对全部活体 .v grep 零命中，ME2/
   ZeroLocus 处依赖叶），两源五件产物以 .retired_S4 前缀快照
   留存。
   ============================================================ *)

Print Assumptions DTPT_Entropy.DTPT_Entropy.xq_Qle_bool_true.
Print Assumptions DTPT_Entropy.DTPT_Entropy.xq_Qle_bool_le.
Print Assumptions DTPT_Entropy.DTPT_Entropy.Pinf_eq_l.
Print Assumptions DTPT_Entropy.DTPT_Entropy.qlen_pos.
Print Assumptions DTPT_Entropy.DTPT_Entropy.collide_zero.
Print Assumptions DTPT_Entropy.DTPT_Entropy.me2_weight_nonneg.
Print Assumptions DTPT_Entropy.DTPT_Entropy.me_total_eq.
Print Assumptions DTPT_Entropy.DTPT_Entropy.sqsum_app_cross_val.
Print Assumptions DTPT_Entropy.DTPT_Entropy.sqsum_cross_sym_val.
