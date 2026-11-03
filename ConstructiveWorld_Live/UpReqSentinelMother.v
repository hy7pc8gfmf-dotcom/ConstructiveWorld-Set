(* ===================================================================== UpReqSentinelMother —— 使命行：锚不可达引理源模块对（锚支配＋域界不可达）
(* 原申报对照：源自库内定理景观普查的方法论型候选项——「锚不可达引理源模块   *) (* 数学坐标：G10_LoebFam.v dmin 空带锚 999（不变式纯注释级）；                *)
(* DenPosGeneral.v 低段严格数值锚（族 1，已成族无需源模块）。族 2 不可达锚    *) (* 源模块化即本件主旨。                                                      *)
(* 主件（源模块对，Section 泛化，零外加假设，前提显式参；前缀 stm_，避免与     *) (* 库内既有名冲突）：                                                      *)
(*   源模块 A（锚支配面）：枚举器 smin 的输出被表内任一成员的核值支配——      *)
(*     stm_domin_in / stm_domin_head；伴随 singleton 正面可达面              *)
(*     stm_smin_singleton。                                                *)
(*   源模块 B（域界不可达面）：显式枚举表长非空＋全表核值受界＋锚在域外       *)
(*     ⟹ 锚位永不被命中——stm_unreach_lookup（查表型）/                     *)
(*     stm_unreach_global（全域核型）/ stm_hitcount_zero（count 型，命中      *)
(*     计数恒零）；合流门 stm_domain_gate（输出落域内 ∧ 锚不可达）。        *)
(*   Set 层证人包（提取存活，Prop 位擦除为 __ 标准形非 magic）：              *)
(*     stm_head_witness（sigT 非空表首元证人）/ stm_arg（argmin 条目）＋      *)
(*     stm_arg_sound（证人落在表内且核值恰等于枚举器输出）。                  *)
(*   实例化件（G10 dmin 场景，G10 只读零接触，依存 Require 对接）：           *)
(*     stm_g10_dmin 副本＋桥接引理 stm_g10_bridge（与 G10 dmin 逐点可证相等）＋   *)
(*     999 空带锚数值核对（族 1 口径 vm_compute/reflexivity）＋999 不可达   *)
(*     实例。                                                              *)
(* 备注：公理面自审：本件零外加公理、零承认出口、零占位收尾、零经典逻辑；     *)
(*   主定理全部 Closed under the global context。纯构造性：不可达分支经       *)
(*   空类型消去（False 消除）与 sigT 证人组合完成，无排中律依存。             *)
(*   Set 层纪律：定义面（smin/stm_arg/stm_head_witness/stm_hitcount/         *)
(*   stm_g10_dmin）全 Set/Type 值，零 Prop 数据流入计算位；不可达结论的       *)
(*   Prop 位置不回灌 Set。                                                   *)
   依赖：CW_ConstructiveWorld_219；Stdlib ZArith、Lia、List。
   构造性注记：零外加公理、零承认出口、零占位收尾、零经典逻辑；不可达分支经
   空类型消去（False 消除）与 sigT 证人组合完成；定义面全 Set/Type 值。
   编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。
   =====================================================================*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.
Require S01_BaseRing.
Open Scope Z_scope.

(* Set 层可判定载体：本模块比较面与成员面的证书形（提取面 Prop 位擦除标准形）。 *)
Inductive stm_ZleT (x y : Z) : Set :=
| stm_ZleT_i : x <= y -> stm_ZleT x y.

Inductive stm_ZltT (x y : Z) : Set :=
| stm_ZltT_i : x < y -> stm_ZltT x y.

Inductive stm_ZeqT (x y : Z) : Set :=
| stm_ZeqT_i : x = y -> stm_ZeqT x y.

Inductive stm_ZneT (x y : Z) : Set :=
| stm_ZneT_i : x <> y -> stm_ZneT x y.

Inductive stm_NatLtT (n m : nat) : Set :=
| stm_NatLtT_i : (n < m)%nat -> stm_NatLtT n m.

(* ===================================================================== *)
(* §1 源模块区：锚支配 + 域界不可达（Section 泛化，双参 dist/s 实例化消解）               *)
(* ===================================================================== *)

Section SentinelMother.

(* dist：距离核（实例化 G10 位形取 Z.abs (x - a)）；s：锚值（实例化 999）。 *)
Variable dist : Z -> Z -> Z.
Variable s : Z.

(* 枚举器母形：副本 G10 dmin 结构——空表吐锚 s，非空表取核值逐项最小。 *)
Fixpoint smin (x : Z) (l : list Z) : Z :=
  match l with
  | nil => s
  | a :: l' => Z.min (dist x a) (smin x l')
  end.

(* —— 源模块 A（锚支配面）—— *)

(* 支配主引理：表内任一成员的核值从上方支配枚举器输出（构造性归纳）。 *)
Lemma stm_domin_in : forall (x a : Z) (l : list Z),
  S01_BaseRing.InT a l -> stm_ZleT (smin x l) (dist x a).
Proof.
  intros x a l Hin. revert Hin.
  induction l as [|b l' IH]; intro Hin.
  - inversion Hin.
  - simpl. apply stm_ZleT_i.
    inversion Hin as [l0 | c l0 HinT]; subst.
    + apply Z.le_min_l.
    + etransitivity.
      * apply Z.le_min_r.
      * destruct (IH HinT) as [Hle2]. exact Hle2.
Qed.

(* 支配头元特化：非空表输出被头元核值支配（G10 调用位依存形）。 *)
Lemma stm_domin_head : forall (x a : Z) (l : list Z),
  stm_ZleT (smin x (a :: l)) (dist x a).
Proof.
  intros x a l. apply stm_ZleT_i.
  exact (Z.le_min_l (dist x a) (smin x l)).
Qed.

(* 正面可达面（单调忠实性）：单元素表且核值在锚下界内时，输出恰为该核值
   ——枚举器是真最小化器非常量吐锚，源模块非空壳的正面印证。 *)
Lemma stm_smin_singleton : forall (x a : Z),
  stm_ZleT (dist x a) s -> stm_ZeqT (smin x (a :: nil)) (dist x a).
Proof.
  intros x a H. destruct H as [Hle].
  apply stm_ZeqT_i. apply Z.min_l. exact Hle.
Qed.

(* —— Set 层证人包（sigT 范式；提取后 Prop 位擦除为 __，数据位存活）—— *)

(* 非空表首元证人：显式表长有限性（0 < length）给出 sigT 载体的域内成员。 *)
Definition stm_head_witness (l : list Z) (H : stm_NatLtT 0 (length l)%nat) : {a : Z & S01_BaseRing.InT a l}.
Proof.
  destruct l as [|a l'].
  - exfalso. destruct H as [H0l]. simpl in H0l. lia.
  - exact (@existT _ (fun a0 : Z => S01_BaseRing.InT a0 (a :: l')) a
           (@S01_BaseRing.InT_here Z a l')).
Defined.

(* argmin 条目选择器：返回实现最小核值的表内条目（纯 Set 计算）。 *)
Fixpoint stm_arg (x : Z) (l : list Z) : Z :=
  match l with
  | nil => 0%Z
  | a :: l' => if Z.leb (dist x a) (smin x l') then a else stm_arg x l'
  end.

(* argmin 可靠性：非空表 + 全表受界 + 锚在域外 ⟹ 条目落在表内
   且其核值恰等于枚举器输出（Set 数据包 + Prop 证书的构造性组合）。 *)
Lemma stm_arg_sound : forall (B x : Z) (l : list Z),
  (forall a, S01_BaseRing.InT a l -> stm_ZleT (dist x a) B) -> stm_ZltT B s ->
  stm_NatLtT 0 (length l)%nat ->
  S01_BaseRing.And (S01_BaseRing.InT (stm_arg x l) l)
    (stm_ZeqT (dist x (stm_arg x l)) (smin x l)).
Proof.
  intros B x l. induction l as [|a l' IH]; intros Hcert Hlt Hlen.
  - destruct Hlen as [Hlen']. simpl in Hlen'. exfalso. lia.
  - destruct l' as [|b l''].
    + (* 单元素表：条目即头元 *)
      assert (Hle : dist x a <= s).
      { pose proof (Hcert a (@S01_BaseRing.InT_here Z a nil)) as Hc.
        destruct Hc as [Hc2]. destruct Hlt as [Hlt2]. lia. }
      assert (Hb : Z.leb (dist x a) (smin x nil) = true).
      { apply Z.leb_le. exact Hle. }
      cbn [stm_arg]. rewrite Hb. split.
      * apply (@S01_BaseRing.InT_here Z a nil).
      * apply stm_ZeqT_i. cbn [smin]. symmetry. apply Z.min_l. exact Hle.
    + (* 多元素表：头元与尾表最小者之争 *)
      assert (Hlen'T : stm_NatLtT 0 (length (b :: l''))%nat)
        by (apply stm_NatLtT_i; simpl; lia).
      destruct (Z.leb (dist x a) (smin x (b :: l''))) eqn:Hbranch.
      * cbn [stm_arg]. rewrite Hbranch. cbn [stm_arg]. split.
        -- apply (@S01_BaseRing.InT_here Z a (b :: l'')).
        -- apply stm_ZeqT_i. cbn [smin]. symmetry. apply Z.min_l.
           apply Z.leb_le. exact Hbranch.
      * assert (Hgt : smin x (b :: l'') < dist x a).
        { apply Z.leb_gt. exact Hbranch. }
        change (smin x (b :: l''))
          with (Z.min (dist x b) (smin x l'')) in Hgt.
        destruct (IH (fun a0 Ha0 => Hcert a0
                       (@S01_BaseRing.InT_next Z a0 a (b :: l'') Ha0)) Hlt Hlen'T)
          as [Hin Heq].
        cbn [stm_arg]. rewrite Hbranch. split.
        -- apply (@S01_BaseRing.InT_next Z (stm_arg x (b :: l'')) a (b :: l'') Hin).
        -- apply stm_ZeqT_i. cbn [smin].
           destruct Heq as [Heq2].
           rewrite Z.min_r by lia. exact Heq2.
Qed.

(* —— 源模块 B（域界不可达面）—— *)

(* 查表型主引理：显式枚举表长非空 + 表内全体核值受界（Z.le 显式前提）
   + 锚在域外（Z.lt 显式前提）⟹ 锚位永不被命中。
   构造性：sigT 证人 + 支配 + 传递 + 空类型消去，零经典逻辑。 *)
Lemma stm_unreach_lookup : forall (B x : Z) (l : list Z),
  (forall a, S01_BaseRing.InT a l -> stm_ZleT (dist x a) B) -> stm_ZltT B s ->
  stm_NatLtT 0 (length l)%nat ->
  smin x l <> s.
Proof.
  intros B x l Hcert Hlt Hlen.
  destruct (stm_head_witness l Hlen) as [a Ha].
  destruct (stm_domin_in x a l Ha) as [Hd].
  destruct (Hcert a Ha) as [Hc].
  destruct Hlt as [Hlt2].
  intro Heq. rewrite Heq in Hd.
  exfalso. lia.
Qed.

(* 全域核型推论：核在全域受界（双参量词）时表非空即免锚
   （证书形升级包装，不可达本体仍由查表型主引理承担）。 *)
Lemma stm_unreach_global : forall (B x : Z) (l : list Z),
  (forall y a, stm_ZleT (dist y a) B) -> stm_ZltT B s -> l <> nil ->
  smin x l <> s.
Proof.
  intros B x l Hdom Hlt Hne.
  apply (stm_unreach_lookup B x l).
  - intros a _. apply Hdom.
  - exact Hlt.
  - destruct l as [|a l'].
    + exfalso. apply Hne. reflexivity.
    + simpl. apply stm_NatLtT_i. lia.
Qed.

(* count 型泛化：逐后缀位锚命中计数器（查表协议同形）。 *)
Fixpoint stm_hitcount (x : Z) (l : list Z) : nat :=
  match l with
  | nil => 0%nat
  | a :: l' => Nat.add (if Z.eqb (smin x (a :: l')) s then 1%nat else 0%nat)
                       (stm_hitcount x l')
  end.

(* 命中计数恒零：受界 + 锚在域外 ⟹ 任何表上计数器一次都不触发
   （每一受检位形是非空表，由查表型主引理逐位排除）。 *)
Lemma stm_hitcount_zero : forall (B x : Z) (l : list Z),
  (forall a, S01_BaseRing.InT a l -> stm_ZleT (dist x a) B) -> stm_ZltT B s ->
  S01_BaseRing.Id (stm_hitcount x l) 0%nat.
Proof.
  intros B x l Hcert Hlt.
  induction l as [|a l' IH].
  - reflexivity.
  - assert (Hne : smin x (a :: l') <> s).
    { apply (stm_unreach_lookup B x (a :: l')).
      - intros a0 Ha0. apply Hcert. exact Ha0.
      - exact Hlt.
      - simpl. apply stm_NatLtT_i. lia. }
    cbn [stm_hitcount].
    rewrite (proj2 (Z.eqb_neq (smin x (a :: l')) s) Hne).
    rewrite (IH (fun a0 Ha0 => Hcert a0 (@S01_BaseRing.InT_next Z a0 a l' Ha0))).
    reflexivity.
Qed.

(* 正面伴随：输出落域内（支配 + 全表受界的直接复合）。 *)
Lemma stm_output_in_range : forall (B x : Z) (l : list Z),
  (forall a, S01_BaseRing.InT a l -> stm_ZleT (dist x a) B) ->
  stm_NatLtT 0 (length l)%nat ->
  stm_ZleT (smin x l) B.
Proof.
  intros B x l Hcert Hlen.
  destruct (stm_head_witness l Hlen) as [a Ha].
  destruct (stm_domin_in x a l Ha) as [Hd1].
  destruct (Hcert a Ha) as [Hc1].
  apply stm_ZleT_i. etransitivity.
  - exact Hd1.
  - exact Hc1.
Qed.

(* 合流门（源模块对主）：输出落域内 ∧ 锚不可达 双面一次交付。 *)
Corollary stm_domain_gate : forall (B x : Z) (l : list Z),
  (forall a, S01_BaseRing.InT a l -> stm_ZleT (dist x a) B) -> stm_ZltT B s ->
  stm_NatLtT 0 (length l)%nat ->
  S01_BaseRing.And (stm_ZleT (smin x l) B) (stm_ZneT (smin x l) s).
Proof.
  intros B x l Hcert Hlt Hlen. split.
  - apply (stm_output_in_range B x l Hcert Hlen).
  - apply stm_ZneT_i. apply (stm_unreach_lookup B x l Hcert Hlt Hlen).
Qed.

End SentinelMother.

(* ===================================================================== *)
(* §2 G10 dmin 场景实例化（G10_LoebFam.v 只读零接触；本节独立重构对照形）         *)
(* ===================================================================== *)

(* 位形常量：锚 999（G10:1400 空带支）；域界 998，恰在锚之下（锚在域外）。 *)
Definition stm_g10_s : Z := 999.
Definition stm_g10_B : Z := 998.
Definition stm_g10_dist (x a : Z) : Z := Z.abs (x - a).

(* dmin 副本：源模块枚举器 smin 在 G10 位形下的实例（形合 G10:1398-1402）。 *)
Definition stm_g10_dmin (x : Z) (l : list Z) : Z :=
  smin stm_g10_dist stm_g10_s x l.

(* —— 族 1 口径数值锚（核对 G10 dwm 轨迹 L1430-1444）—— *)

(* 空带支吐锚本体：999 位形落地（空表可达面 = 锚位的定义面）。 *)
Lemma stm_g10_nil_sentinel : forall x : Z, stm_ZeqT (stm_g10_dmin x nil) 999.
Proof.
  intros x. apply stm_ZeqT_i. reflexivity.
Qed.

(* 发射 2 于带 [0]：费 = |2-0| = 2（核对 G10 dwm_W1 = 4 - 2）。 *)
Lemma stm_g10_fee_emit2 : stm_ZeqT (stm_g10_dmin 2 (0 :: nil)) 2.
Proof.
  apply stm_ZeqT_i. reflexivity.
Qed.

(* 发射 1 于带 [2,0]：费 = min(1,1) = 1（核对 G10 dwm_W2 = 2 - 1）。 *)
Lemma stm_g10_fee_emit1 : stm_ZeqT (stm_g10_dmin 1 (2 :: 0 :: nil)) 1.
Proof.
  apply stm_ZeqT_i. reflexivity.
Qed.

(* 发射 3 于带 [2,1,0]：费 = min(1,2,3) = 1（核对 G10 dwm_emit3_legal 前提）。 *)
Lemma stm_g10_fee_emit3 : stm_ZeqT (stm_g10_dmin 3 (2 :: 1 :: 0 :: nil)) 1.
Proof.
  apply stm_ZeqT_i. reflexivity.
Qed.

(* —— 族 2 口径：999 锚不可达（源模块 B 实例化）—— *)

(* 窗口形实例化：查表值与带内条目同落宽 ≤ 998 的窗口 ⟹ 999 永不被吐出
   （证书面由 Z.abs_le + lia 逐点实例化消解，lt/le 前提全显式）。 *)
Lemma stm_g10_unreach_window : forall (x lo hi : Z) (l : list Z),
  stm_ZleT (hi - lo) stm_g10_B -> stm_ZleT lo x -> stm_ZleT x hi ->
  (forall a, S01_BaseRing.InT a l ->
     S01_BaseRing.And (stm_ZleT lo a) (stm_ZleT a hi)) -> l <> nil ->
  stm_g10_dmin x l <> stm_g10_s.
Proof.
  intros x lo hi l Hwidth Hxlo Hxhi Hmem Hne.
  destruct Hwidth as [Hw]. destruct Hxlo as [Hxl]. destruct Hxhi as [Hxh].
  unfold stm_g10_dmin.
  apply (stm_unreach_lookup stm_g10_dist stm_g10_s stm_g10_B x l).
  - intros a Ha. destruct (Hmem a Ha) as [Halo Hahi].
    destruct Halo as [Hal]. destruct Hahi as [Hah].
    apply stm_ZleT_i. unfold stm_g10_dist, stm_g10_B in *.
    apply Z.abs_le. lia.
  - apply stm_ZltT_i. unfold stm_g10_B, stm_g10_s. lia.
  - destruct l as [|a l'].
    + exfalso. apply Hne. reflexivity.
    + simpl. apply stm_NatLtT_i. lia.
Qed.

(* 具体实例：G10 文档轨迹的带 [2,1,0]、查表 3——注释级不变式定理化落地。 *)
Theorem stm_g10_sentinel_unreachable_3_210 :
  stm_g10_dmin 3 (2 :: 1 :: 0 :: nil) <> stm_g10_s.
Proof.
  apply (stm_g10_unreach_window 3 0 3 (2 :: 1 :: 0 :: nil)).
  - apply stm_ZleT_i. unfold stm_g10_B. lia.
  - apply stm_ZleT_i. lia.
  - apply stm_ZleT_i. lia.
  - intros a Ha. inversion Ha as [l0 | y0 l0 Hnext]; subst.
    + split; apply stm_ZleT_i; lia.
    + inversion Hnext as [l1 | y1 l1 Hnext1]; subst.
      * split; apply stm_ZleT_i; lia.
      * inversion Hnext1 as [l2 | y2 l2 Hnext2]; subst.
        -- split; apply stm_ZleT_i; lia.
        -- inversion Hnext2.
  - discriminate.
Qed.

(* ===================================================================== *)
(* §3 G10 原位对接（依存 Require）：桥接引理 + 公理面审计 + 提取审计                *)
(* ===================================================================== *)

Require Import G10_LoebFam.

(* 桥接引理：G10 dmin（只读原形 G10:1398-1402）与源模块副本 stm_g10_dmin 逐点可证相等——
   本件全部源模块定理经此桥直接回账 G10 调用位（dwm_emit/halt_cert），G10 本体零改。 *)
Lemma stm_g10_bridge : forall (x : Z) (l : list Z),
  stm_ZeqT (dmin x l) (stm_g10_dmin x l).
Proof.
  intros x l. apply stm_ZeqT_i.
  unfold stm_g10_dmin, stm_g10_dist, stm_g10_s.
  induction l as [|a l' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* —— 公理面审计（以下各条须全部 Closed under the global context）—— *)
Print Assumptions stm_domin_in.
Print Assumptions stm_unreach_lookup.
Print Assumptions stm_unreach_global.
Print Assumptions stm_hitcount_zero.
Print Assumptions stm_domain_gate.
Print Assumptions stm_arg_sound.
Print Assumptions stm_g10_unreach_window.
Print Assumptions stm_g10_sentinel_unreachable_3_210.
Print Assumptions stm_g10_bridge.

(* —— 提取审计（输出件名由下方 Extraction 命令所定）—— *)
From Stdlib Require Import Extraction.
Extraction "_tq24s_extract" smin stm_arg stm_head_witness stm_hitcount stm_g10_dmin.
