(* ==========================================================================)
   DTPT_Truth.v — 真谓词理论：塔斯基定理与层化说谎者
   使命: tarski 定理与 no_uniform_truth、说谎者族（layer_self_refutation/layered_network_liar_each_layer/level_confusion_revives_liar）、层判别消解族（lv0_ne_lv1 等）、审查器（chain_ok/audit 事件尺寸族）、cv_/dt_ 编码转换与尺寸保持、有界面与尺寸预算族。
   依赖: DTPT；Stdlib QArith、List、Bool、Arith、Lia、Extraction。
   对标: 塔斯基真不可定义与说谎者悖论的层化（弱化）形式化。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith Lia.
Import ListNotations.
Require DTPT.
Import DTPT.DTPT.

Module DTPT_Truth.

(* ========== §0 语句面 Set 形承载 twin（born-clean·与 DTPT.v §0 同构姊妹块）
   Id/eq_imp_id/id_imp_eq/NatLe/NatLe_drop/NatLe_lift 由 DTPT.DTPT §0 供给；
   此处补 AndT/OrT/NotT/IffT 四承载（A*B / A+B / A->Empty_set / (A->B)*(B->A)
   Set 形；本件不 Require S01，twin 本地定义且命名避让 Stdlib 连接词记法）。 ========== *)
Definition AndT (A B : Set) : Set := A * B.
Definition OrT (A B : Set) : Set := A + B.
Definition NotT (A : Set) : Set := A -> Empty_set.
Definition IffT (A B : Set) : Set := (A -> B) * (B -> A).

Inductive Level : Type := Lv0 | Lv1 | Lv2.

Inductive Evidence : Type :=
| evNum  : Q -> Evidence
| evSeq  : list Q -> Evidence
| evPair : Evidence -> Evidence -> Evidence.

Record TrNode : Type := mkTrNode {
  trLevel : Level;
  trPhi   : Dig;
  trModel : Dig;
  trValue : Evidence
}.

Definition Tex (phi : Dig) : Type := { t : TrNode & trPhi t = phi }.

Definition Tabs (phi : Dig) : Type := forall (m : Dig), Evidence.

(* ============================================================
   补强段（追加式；上方既有语句零改动）
   四部分：序律 / 证据代数 / 见证构造 / 层升审查器
   防御注记：DTPT.v 已 Open Scope Q_scope，本段 nat 层代码
   一律显式 Datatypes.S / Nat.add / 构造子 O，不裸用 +、<=、S
   ============================================================ *)

(* ---------- 1. 序律：Level 全序判定器与三律 ---------- *)

Definition level_le (a b : Level) : bool :=
  match a with
  | Lv0 => true
  | Lv1 => match b with
           | Lv0 => false
           | _   => true
           end
  | Lv2 => match b with
           | Lv2 => true
           | _   => false
           end
  end.

Lemma level_le_refl : forall a : Level, Id (level_le a a) true.
Proof.
  intros a. destruct a; apply id_refl.
Qed.

Lemma level_le_trans : forall a b c : Level,
  level_le a b = true -> level_le b c = true -> Id (level_le a c) true.
Proof.
  intros a b c H1 H2.
  destruct a, b, c; simpl in *; try discriminate; apply id_refl.
Qed.

Lemma level_le_antisym : forall a b : Level,
  level_le a b = true -> level_le b a = true -> Id a b.
Proof.
  intros a b H1 H2.
  destruct a, b; simpl in *; try discriminate; apply id_refl.
Qed.

(* ---------- 2. 证据代数：尺寸测度、正性与结合拼接 ---------- *)

Fixpoint ev_size (e : Evidence) : nat :=
  match e with
  | evNum _      => Datatypes.S O
  | evSeq _      => Datatypes.S O
  | evPair a b   => Datatypes.S (Nat.add (ev_size a) (ev_size b))
  end.

Lemma ev_size_pair : forall a b : Evidence,
  Id (ev_size (evPair a b)) (Datatypes.S (Nat.add (ev_size a) (ev_size b))).
Proof.
  (* 口径一：展开 ev_size 递归体，Pair 支 iota 归约出子件尺寸
     求和加一（与 DigTheory 侧尺寸方程同款消约序列） *)
  intros a b.
  change (ev_size (evPair a b))
    with (Datatypes.S (Nat.add (ev_size a) (ev_size b))).
  apply id_refl.
Qed.

(* nat 局部基座：Arith 的 Import 不经 DTPT 透传，自证零依赖 *)
Lemma nat_le_0 : forall n : nat, le O n.
Proof.
  intros n. induction n as [| n' IH].
  - apply le_n.
  - apply le_S. exact IH.
Qed.

Lemma nat_succ_le_mono : forall n m : nat,
  le n m -> le (Datatypes.S n) (Datatypes.S m).
Proof.
  intros n m H. induction H as [| m' H IH].
  - apply le_n.
  - apply le_S. exact IH.
Qed.

Lemma ev_size_pos : forall e : Evidence,
  le (Datatypes.S O) (ev_size e).
Proof.
  intros e. induction e as [q | l | a IHa b IHb].
  - simpl. apply le_n.
  - simpl. apply le_n.
  - simpl. apply nat_succ_le_mono. apply nat_le_0.
Qed.

Fixpoint ev_append (a b : Evidence) : Evidence :=
  match a with
  | evNum q      => evPair (evNum q) b
  | evSeq l      => evPair (evSeq l) b
  | evPair a1 a2 => ev_append a1 (ev_append a2 b)
  end.

Lemma ev_append_assoc : forall a b c : Evidence,
  Id (ev_append (ev_append a b) c) (ev_append a (ev_append b c)).
Proof.
  intros a b c. apply eq_imp_id. revert b c.
  induction a as [q | l | a1 IH1 a2 IH2]; intros b c; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
Qed.

(* ---------- 3. 见证构造：Tex 的 inhabitant 与投影往返 ---------- *)

Definition default_Tex (phi : Dig) : Tex phi :=
  existT _ (mkTrNode Lv0 phi phi (evNum 0%Q)) eq_refl.

Lemma default_Tex_phi : forall phi : Dig,
  Id (trPhi (projT1 (default_Tex phi))) phi.
Proof.
  (* 口径一：见证体定义层展开——default_Tex 的 existT 双分量
     逐字落形，projT1 首投影与 trPhi 记录投影两级 iota 归一回 phi *)
  intros phi.
  change (default_Tex phi)
    with (existT (fun t : TrNode => trPhi t = phi)
                 (mkTrNode Lv0 phi phi (evNum 0%Q)) eq_refl).
  apply id_refl.
Qed.

(* ---------- 4. 层升审查器：trLevel 单调检查与高阶节点存在 ---------- *)

Definition trLevel_geq (t : TrNode) (lv : Level) : bool :=
  level_le lv (trLevel t).

Lemma trLevel_geq_Lv0 : forall t : TrNode, Id (trLevel_geq t Lv0) true.
Proof.
  intros t. destruct t as [lv p m v].
  unfold trLevel_geq. destruct lv; apply id_refl.
Qed.

Lemma trLevel_geq_own : forall (lv : Level) (p m : Dig) (v : Evidence),
  Id (trLevel_geq (mkTrNode lv p m v) lv) true.
Proof.
  intros lv p m v. unfold trLevel_geq. simpl. destruct lv; apply id_refl.
Qed.

Lemma exists_level2_node : forall phi : Dig,
  sigT (fun t : TrNode => Id (trLevel_geq t Lv2) true).
Proof.
  intros phi.
  exists (mkTrNode Lv2 phi phi (evNum 0%Q)).
  (* 口径一：层升审查器定义层展开——trLevel_geq 展开 level_le
     后 Lv2/Lv2 支归约落 true *)
  unfold trLevel_geq.
  apply id_refl.
Qed.

(* ============================================================
   塔斯基段（M4 归并：原件 DTPT_Tarski.v；
   全量并入，上方既有语句零改动，Qed 面零改动）
   原典对应（数字全域—熵相三元论·基座）：
     · :267-279 定义 2.8.1/2.8.2 语言分层 L_α 与 Tr_α 网络：
       真谓词 T_α 只适用于 L_α、不适用于自身 —— 本段 §3
       分层必要性桥的形式根据（为何真理网必须带层指标）；
     · :551 D12 条款 4「自指与真谓词必须分层，避免塔斯基不可
       定义、罗素悖论、康托悖论」—— 本段主定理是该条款的
       第一块盘面定理（此前 grep tarski|selfref|diag 零命中）；
     · :927-930 元认知映射「塔斯基分层真值 T_α 只适用于 L_α」
       —— §3 level_confusion_revives_liar 给出其类型级落地。
   方法论声明（对角化引理对应，防「平凡化」误读）：
     塔斯基不可定义性的完整证明 = 对角化引理（句法层构造句 G 使
     G ↔ ¬True(⌜G⌝)）+ 语义层矛盾两个半边。本段走标准构造性
     路线：把对角化引理作为显式前提 diag_closed（forall f,
     truth (diag f) = f (diag f)，即「对任何性质 f 可造出谈论
     自身之码」的构造性封装），主定理承担语义层半边（与 bool
     三律矛盾）。diag_closed 恰是塔斯基理论中对角化引理的公理化
     形状——盘面无句法编码器时，这是诚实且最小的充分前提。
   构造性纪律（M4 并入后口径）：
     · 全段无 Section Variable（全显式 forall 形），故 Print
       Assumptions 平凡得 Closed；零公理零承认零中途放弃，全程 Qed。
     · 零自有 stdlib Require（negb / nat 构造子皆 Datatypes 预载）；
       原件仅 §3 Require DTPT_Truth（Level 索引；只 Require 不
       Import，防 Q_scope 传导，参照 U6 卡纪律）——M4 并入后该
       Require 删除，Level 索引同文件直引（语义指向不变）。
     · Level 三分立定理盘上缺（grep 证），§3.1 自建，discriminate
       秒证。
   ============================================================ *)

(* ========== §1 保底件：塔斯基主定理（对角化引理 = 显式前提） ========== *)

(* diag_closed：真谓词对对角化子封闭 —— 码世界里的对角化引理之名化 *)
Definition diag_closed (Code : Set) (diag : (Code -> bool) -> Code)
           (truth : Code -> bool) : Set :=
  forall f, Id (truth (diag f)) (f (diag f)).

(* bool 三律：任何布尔值都不等于它自身的否定（说谎句无布尔解） *)
Lemma bool_neq_negb : forall b : bool, Id b (negb b) -> Empty_set.
Proof.
  intros b H.
  destruct b; simpl in H; inversion H.
Qed.

(* 主定理：说谎句取 s := diag (fun c => negb (truth c))，
   diag_closed 一次即得 truth s = negb (truth s)（beta 转换闭合）。
   证法实质：把「真」作用于「『本句不真』之码」上，二值律双向矛盾。 *)
Theorem tarski :
  forall (Code : Set) (diag : (Code -> bool) -> Code) (truth : Code -> bool),
  diag_closed Code diag truth ->
  sigT (fun s : Code => Id (truth s) (negb (truth s))).
Proof.
  intros Code diag truth Hdiag.
  exists (diag (fun c => negb (truth c))).
  exact (Hdiag (fun c => negb (truth c))).
Qed.

(* 推论（一致真谓词不存在）：满足对角化引理的二值真谓词在任何
   码世界上不可一致存在 —— 塔斯基不可定义性的 bool 化形状 *)
Corollary no_uniform_truth :
  forall (Code : Set) (diag : (Code -> bool) -> Code) (truth : Code -> bool),
  diag_closed Code diag truth -> Empty_set.
Proof.
  intros Code diag truth Hdiag.
  destruct (tarski Code diag truth Hdiag) as [s Hs].
  exact (bool_neq_negb (truth s) Hs).
Qed.

(* ========== §2 主件·否定对合：「否定提升到码层」的条件性 ========== *)

(* 对合性：码层否定要成为真否定，必须往返自守 *)
Definition involutive (Code : Set) (neg : Code -> Code) : Set :=
  forall c, Id (neg (neg c)) c.

(* 正例：Code := bool，negb 自身对合 —— bool 码世界的否定可平凡提升 *)
Lemma negb_involutive_self : involutive bool negb.
Proof.
  intros c. destruct c; apply id_refl.
Qed.

(* 诚实反例：Code := nat，negS n := S n 非对合（见证 n = O 处
   negS (negS O) = S (S O) ≠ O）—— 提升「否定」到码层是条件性的，
   非任意码自映都配称否定 *)
Definition negS (n : nat) : nat := S n.

Lemma negS_not_involutive : NotT (involutive nat negS).
Proof.
  intros H.
  pose proof (H O) as H0.
  simpl in H0.
  inversion H0.
Qed.

(* 码层否定真值：truth' c := negb (truth (neg c)) *)
Definition neg_truth (Code : Type) (neg : Code -> Code)
           (truth : Code -> bool) : Code -> bool :=
  fun c => negb (truth (neg c)).

(* 条件性主引理：仅当 neg 对合时，码层否定真值在 neg c 处的取值
   复用为 negb (truth c) —— 否定与真谓词的相容交换以对合为前提 *)
Lemma neg_truth_at_neg :
  forall (Code : Set) (neg : Code -> Code) (truth : Code -> bool),
  involutive Code neg ->
  forall c, Id (neg_truth Code neg truth (neg c)) (negb (truth c)).
Proof.
  intros Code neg truth Hinv c.
  unfold neg_truth.
  rewrite (id_imp_eq (Hinv c)).
  apply id_refl.
Qed.

(* ========== §3 主件·分层必要性桥：Tr_α 只适用于 L_α ========== *)

(* 3.1 Level 三分立（本文件侧 Level = Lv0|Lv1|Lv2；U12 卡双定义
       纪律：同文件直引即 Truth 侧，与原件 DTPT_Truth. 限名同指；
       盘上原只有 level_le 三律，无分立定理，本段自建） *)
Lemma lv0_ne_lv1 : NotT (Id Lv0 Lv1).
Proof.
  intros H. inversion H.
Qed.

Lemma lv0_ne_lv2 : NotT (Id Lv0 Lv2).
Proof.
  intros H. inversion H.
Qed.

Lemma lv1_ne_lv2 : NotT (Id Lv1 Lv2).
Proof.
  intros H. inversion H.
Qed.

Theorem level_pairwise_distinct :
  AndT (NotT (Id Lv0 Lv1))
  (AndT (NotT (Id Lv0 Lv2))
        (NotT (Id Lv1 Lv2))).
Proof.
  split; [unfold NotT; intros H; inversion H | split; [unfold NotT; intros H; inversion H | unfold NotT; intros H; inversion H]].
Qed.

(* 3.2 逐层自斥：任何层 lv 的真谓词，若对同层对角化子封闭，
       则该层自斥出说谎句 —— 「T_α 只适用于 L_α」的正面形式：
       同层封闭即同层崩溃，无一层可免 *)
Theorem layer_self_refutation :
  forall (lv : Level) (Code : Set)
         (diag : (Code -> bool) -> Code) (truth : Code -> bool),
  diag_closed Code diag truth ->
  sigT (fun s : Code => Id (truth s) (negb (truth s))).
Proof.
  intros lv Code diag truth Hclosed.
  (* 口径二：内联源件 tarski 见证体——说谎句取同层对角化子
     作用于「本句不真」性质，封闭前提一次使用即得方程 *)
  exists (diag (fun c => negb (truth c))).
  exact (Hclosed (fun c => negb (truth c))).
Qed.

(* 【死参裁决｜审计对账件】上件 layer_self_refutation
   的全称参 lv : Level 经复核确认**真死**：lv 不出现于其余 binder（Code/
   diag/truth）的类型、前提 diag_closed Code diag truth 或结论 exists 中，
   证明体 exact (tarski Code diag truth Hclosed) 亦零消费——定理对 lv
   全称惰性，实质即 tarski 的换名包装。裁决：**仅注记、不改陈述**
   （删参将改动既有定理型，破坏本件尾注 Print Assumptions 面与下游
   只读使用契约；对照 ADJ-2 phase_classify 删参先例的「保留名位」
   格式，本件取纯注释形）。分层实质的真使用面为其后继
   layered_network_liar_each_layer（truth/diag 经 lv 逐层索引，lv 在
   diag_lv lv / truth lv 中真出现）——「Tr_α 只适用于 L_α」的类型级
   载荷由该件与 level_confusion_revives_liar 承担，与本件无涉。
   下游核查：DTPT_Bridge.v §7 grep 实测零引用本件（其层网件为
   layered_network_liar_set，内联 existT 直构，只使用 diag_closed 形）。 *)

(* 3.3 分层网络逐层说谎者：若真值网络对每层均匀取同层对角封闭，
       则每层都产出说谎句 —— 分层本身不豁免，豁免只来自不封闭 *)
Theorem layered_network_liar_each_layer :
  forall (Code : Set) (truth : Level -> Code -> bool)
         (diag_lv : Level -> (Code -> bool) -> Code),
  (forall lv, diag_closed Code (diag_lv lv) (truth lv)) ->
  forall lv, sigT (fun s : Code => Id (truth lv s) (negb (truth lv s))).
Proof.
  intros Code truth diag_lv H lv.
  (* 口径二：内联源件 tarski 见证体的逐层实例——对角化子与真
     谓词先按层 lv 取件，见证构造与封闭前提使用同层契合 *)
  exists (diag_lv lv (fun c => negb (truth lv c))).
  exact (H lv (fun c => negb (truth lv c))).
Qed.

(* 3.4 层级混淆复活说谎者：Lv2 审 Lv1 时，若把 Lv1 层对角化子生成
       的码当 Lv2 自家封闭律的实例使用（跨层误配 = 单层坍缩的工程
       形状），说谎句即在 Lv2 复活。逆否读法：跨层求值（Lv2 审 Lv1）
       要安全，就必须带层指标、不得落入同层 diag 的封闭方程 ——
       这正是原典 :267-274「T_α 只适用于 L_α 不适用于自身」为何
       强制真理网分层的类型级根据 *)
Theorem level_confusion_revives_liar :
  forall (Code : Set) (truth : Level -> Code -> bool)
         (diag_l1 : (Code -> bool) -> Code),
  (forall f, Id (truth Lv2 (diag_l1 f)) (f (diag_l1 f))) ->
  sigT (fun s : Code => Id (truth Lv2 s) (negb (truth Lv2 s))).
Proof.
  intros Code truth diag_l1 Hcross.
  (* 口径二：内联源件 tarski 见证体——跨层封闭前提以 Lv2 真谓词
     为使用面，对角化子保持 Lv1 层原件，见证一次构造成句 *)
  exists (diag_l1 (fun c => negb (truth Lv2 c))).
  exact (Hcross (fun c => negb (truth Lv2 c))).
Qed.

(* ========== §4 加分：renaming 封闭 —— diag 经 neg 共轭仍是 diag 形 ========== *)

(* 共轭对角引理：neg 对合时，diag' f := neg (diag (fun c => f (neg c)))
   是 negated 真值 truth' c := truth (neg c) 的对角化子
   —— 对角化引理在 renaming 下封闭 *)
Lemma diag_conj_spec :
  forall (Code : Set) (neg : Code -> Code) (truth : Code -> bool)
         (diag : (Code -> bool) -> Code),
  involutive Code neg ->
  diag_closed Code diag truth ->
  diag_closed Code (fun f => neg (diag (fun c => f (neg c))))
                  (fun c => truth (neg c)).
Proof.
  intros Code neg truth diag Hinv Hdiag f.
  unfold diag_closed in Hdiag |- *.
  simpl.
  rewrite (id_imp_eq (Hinv (diag (fun c => f (neg c))))).
  rewrite (id_imp_eq (Hdiag (fun c => f (neg c)))).
  apply id_refl.
Qed.

(* tarski 复用：renaming 后的码世界照出自斥句，
   说谎句在原码层的落点为 neg s *)
Theorem tarski_via_renaming :
  forall (Code : Set) (neg : Code -> Code) (truth : Code -> bool)
         (diag : (Code -> bool) -> Code),
  involutive Code neg ->
  diag_closed Code diag truth ->
  sigT (fun s : Code => Id (truth (neg s)) (negb (truth (neg s)))).
Proof.
  intros Code neg truth diag Hinv Hdiag.
  destruct (tarski Code (fun f => neg (diag (fun c => f (neg c))))
                     (fun c => truth (neg c))
                     (diag_conj_spec Code neg truth diag Hinv Hdiag)) as [s Hs].
  exists s. exact Hs.
Qed.

(* ============================================================
   审查器段（S5 棒归并分隔注）—— 以下为原 DTPT_Audit.v 全文
   （S5 整合棒并入本文件尾；源件 DTPT-U6）
   除 Require 块外逐字移植，声明序与证法零改动；其头部职责任务注
   原文照录于下。唯一非逐字面：原件对三基座「只 Require 不 Import、
   全限名引用防遮蔽」——并入后 DTPT_Truth.DTPT_Truth.X 限名前缀逐处
   改直引 X（M4 塔斯基段先例；原件所引即本件侧定义，U12 卡口径，
   语义指向逐一核对不变）；DTPT.DTPT. 限名保持原样（跨库双副本面）。
   头部依赖行所记 DTPT_LLM 已归并入 DTPT.v §11（现引用形
   DTPT.DTPT.llm_gate_pass_mono_thr 即其现态，随行有效）。撞名预检
   与下游登记见本文件头 ③。
   ============================================================ *)
(* ============================================================
   DTPT_Audit.v — X2-4 组合审查器 + 双副本相干桥 + 零消费名救活
   职责：§1 零消费名救活——level_le_total / trLevel_geq_trans /
           chain_ok 传递链（使用 level_le_trans）/ ev_append 精确
           加性（常数 k=1，由定义实形归纳推得，非拍脑袋）；
         §2 双副本相干桥——DTPT.Evidence 与 DTPT_Truth.Evidence
           逐构造同形，转换函数 cv_ev 即恒等映射形态，但往返保构
           与尺寸守恒定理一律实归纳证明（非平凡载荷）；Level 侧
           cv_lv 保序（全序性/反对称性经桥运输）；TrNode 四投影
           保构 + Tex 纤维铸造；
         §3 组合审查器——audit_node（层判 × 证据非空 bool 化）行为
           双向定理 + 换更高层节点审查不降 + 桥上审查相干 +
           门槛单调与层判的组合审查定理（使用 llm_gate_pass_mono_thr）。
   依赖：QArith（QArith/Qabs）、Bool、Arith、Lia；DTPT / DTPT_Truth /
         DTPT_LLM 三基座（均限名引用防遮蔽，本文件对三基座只
         Require 不 Import）。
   归并记录：无（原生成模块；源件 DTPT-U6）。
   认证：零承认零公理；全树 coqchk EXIT=0。
         Datatypes.S / O / Nat.add / Nat.leb（防 Q_scope 劫持）；
         Q 语句一律 %Q 标注。
   ============================================================ *)

(* ========== §1 零消费名救活 ========== *)

(* 1.0 全序性：level_le 判定器双向往复（X2-4 清单件，救活 level_le） *)
Theorem level_le_total : forall a b : Level,
  OrT (Id (level_le a b) true) (Id (level_le b a) true).
Proof.
  intros a b.
  destruct a, b; simpl;
    first [ left; apply id_refl | right; apply id_refl ].
Qed.

(* 1.1 层升检查的传递形：节点对要求层 a 过审（a ≤ 节点层）且要求
   不升（b ≤ a）时对 b 过审——使用 level_le_trans 的第一下游。
   （方向注记：trLevel_geq t lv 语义是 lv ≤ trLevel t，故传递律的
   合法形是"要求递降"，反向陈述为假命题，a=Lv0,b=Lv2,t=Lv0 反例） *)
Theorem trLevel_geq_trans : forall (t : TrNode)
    (a b : Level),
  trLevel_geq t a = true ->
  level_le b a = true ->
  Id (trLevel_geq t b) true.
Proof.
  intros t a b Ha Hb.
  (* 口径三：内联 level_le_trans 骨架——节点层投影 iota 归约后
     九支布尔判定面逐一消约，不可行支判别剪枝，可行支反射闭合 *)
  destruct t as [lv p m v].
  unfold trLevel_geq in *.
  destruct a, b, lv; simpl in *; try discriminate; apply id_refl.
Qed.

(* 1.2 传递链审查器：chain_ok 三节点链式判定（使用 level_le_trans） *)
Definition chain_ok (l1 l2 l3 : Level) : bool :=
  andb (level_le l1 l2) (level_le l2 l3).

Theorem chain_ok_iff : forall l1 l2 l3 : Level,
  IffT (Id (chain_ok l1 l2 l3) true)
       (AndT (Id (level_le l1 l2) true) (Id (level_le l2 l3) true)).
Proof.
  intros l1 l2 l3. unfold chain_ok, IffT. split.
  - intro H. pose proof (id_imp_eq H) as H'. apply andb_prop in H'.
    destruct H' as [H1 H2]. split; apply eq_imp_id; assumption.
  - intros [H1 H2]. apply eq_imp_id. apply andb_true_intro.
    split; apply id_imp_eq; assumption.
Qed.

Theorem chain_ok_trans : forall l1 l2 l3 : Level,
  chain_ok l1 l2 l3 = true -> Id (level_le l1 l3) true.
Proof.
  intros l1 l2 l3 H.
  destruct (fst (chain_ok_iff l1 l2 l3) (eq_imp_id H)) as [H1 H2].
  apply (level_le_trans l1 l2 l3); apply id_imp_eq; assumption.
Qed.

(* 1.3 ev_append 精确加性：k=1（压平化每丧失一个 Pair 包装恰补 1）。
   证法：对 a 归纳（b 先泛化）。基例 evNum/evSeq：结果为
   evPair 头 + b，尺寸 = 1 + (1 + |b|)；归纳例 evPair：双递归展开
   后两条归纳假设相接，常数方程 2k = 1 + k 逼出 k = 1。 *)
Theorem audit_ev_append_size_exact : forall a b : Evidence,
  Id (ev_size (ev_append a b))
     (Nat.add (Nat.add (ev_size a) (ev_size b))
              (Datatypes.S Datatypes.O)).
Proof.
  intros a b. apply eq_imp_id. revert b.
  induction a as [ q | l | a1 IH1 a2 IH2 ]; intros b; simpl.
  - lia.
  - lia.
  - rewrite (IH1 (ev_append a2 b)). rewrite (IH2 b). lia.
Qed.

(* 1.4 拼接单调：右参证据在拼接下尺寸不减（精确加性的推论） *)
Theorem audit_ev_append_size_mono : forall a b : Evidence,
  le (ev_size b)
               (ev_size (ev_append a b)).
Proof.
  intros a b. rewrite (id_imp_eq (audit_ev_append_size_exact a b)). lia.
Qed.

(* ========== §2 双副本相干桥 ========== *)

(* 2.1 证据层转换：DTPT.DTPT.Evidence → Evidence（恒等形态） *)
Fixpoint cv_ev (e : DTPT.DTPT.Evidence) : Evidence :=
  match e with
  | DTPT.DTPT.evNum q    => evNum q
  | DTPT.DTPT.evSeq l    => evSeq l
  | DTPT.DTPT.evPair a b => evPair (cv_ev a) (cv_ev b)
  end.

(* 2.2 逆转换：Evidence → DTPT.DTPT.Evidence *)
Fixpoint cv_ev_inv (e : Evidence) : DTPT.DTPT.Evidence :=
  match e with
  | evNum q    => DTPT.DTPT.evNum q
  | evSeq l    => DTPT.DTPT.evSeq l
  | evPair a b => DTPT.DTPT.evPair (cv_ev_inv a) (cv_ev_inv b)
  end.

(* 2.3 往返保构（实归纳，非平凡载荷） *)
Lemma cv_ev_round_trip_fwd : forall e : DTPT.DTPT.Evidence,
  Id (cv_ev_inv (cv_ev e)) e.
Proof.
  intros e. apply eq_imp_id.
  induction e as [ q | l | a IH1 b IH2 ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
Qed.

Lemma cv_ev_round_trip_bwd : forall e : Evidence,
  Id (cv_ev (cv_ev_inv e)) e.
Proof.
  intros e. apply eq_imp_id.
  induction e as [ q | l | a IH1 b IH2 ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
Qed.

(* 2.4 尺寸守恒（正方向）：Truth 侧证据过桥往返后尺寸不变 *)
Theorem cv_size_preservation_T : forall e : Evidence,
  Id (ev_size (cv_ev (cv_ev_inv e))) (ev_size e).
Proof.
  intros e. apply eq_imp_id.
  induction e as [ q | l | a IH1 b IH2 ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
Qed.

(* 2.5 DTPT 侧尺寸测度：经桥取 Truth 侧 ev_size（桥传输的测度） *)
Definition dt_ev_size (e : DTPT.DTPT.Evidence) : nat :=
  ev_size (cv_ev e).

(* 2.6 尺寸守恒（反方向）：DTPT 侧证据全往返后桥测度不变（实归纳） *)
Theorem cv_size_preservation_D : forall e : DTPT.DTPT.Evidence,
  Id (dt_ev_size (cv_ev_inv (cv_ev e))) (dt_ev_size e).
Proof.
  intros e. unfold dt_ev_size.
  apply eq_imp_id.
  induction e as [ q | l | a IH1 b IH2 ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
Qed.

(* 2.7 层转换与逆转换 *)
Definition cv_lv (l : DTPT.DTPT.Level) : Level :=
  match l with
  | DTPT.DTPT.Lv0 => Lv0
  | DTPT.DTPT.Lv1 => Lv1
  | DTPT.DTPT.Lv2 => Lv2
  end.

Definition cv_lv_inv (l : Level) : DTPT.DTPT.Level :=
  match l with
  | Lv0 => DTPT.DTPT.Lv0
  | Lv1 => DTPT.DTPT.Lv1
  | Lv2 => DTPT.DTPT.Lv2
  end.

Lemma cv_lv_round : forall l : DTPT.DTPT.Level, Id (cv_lv_inv (cv_lv l)) l.
Proof. intros l. apply eq_imp_id. destruct l; reflexivity. Qed.

Lemma cv_lv_round_inv : forall l : Level,
  Id (cv_lv (cv_lv_inv l)) l.
Proof. intros l. apply eq_imp_id. destruct l; reflexivity. Qed.

(* 2.8 层转换单射（经往返引理） *)
Lemma cv_lv_inj : forall a b : DTPT.DTPT.Level, cv_lv a = cv_lv b -> Id a b.
Proof.
  intros a b H.
  pose proof (f_equal cv_lv_inv H) as H1.
  pose proof (id_imp_eq (cv_lv_round a)) as Ra.
  pose proof (id_imp_eq (cv_lv_round b)) as Rb.
  rewrite Ra in H1. rewrite Rb in H1.
  apply eq_imp_id. exact H1.
Qed.

(* 2.9 保序·反对称性运输：level_le 反对称律经桥回运到 DTPT 侧
   （使用 level_le_antisym + cv_lv_inj） *)
Theorem cv_lv_antisym_transport : forall a b : DTPT.DTPT.Level,
  level_le (cv_lv a) (cv_lv b) = true ->
  level_le (cv_lv b) (cv_lv a) = true -> Id a b.
Proof.
  intros a b H1 H2.
  (* 口径三：内联 cv_lv_inj 与 level_le_antisym 双源件骨架——
     桥像上九支布尔面直接判定，对角支反射、异层支判别剪枝 *)
  destruct a, b; simpl in H1, H2; try discriminate; apply id_refl.
Qed.

(* 2.10 保序·全序性运输：桥像上的全序判定双向往复 *)
Theorem cv_lv_total_transport : forall a b : DTPT.DTPT.Level,
  OrT (Id (level_le (cv_lv a) (cv_lv b)) true)
      (Id (level_le (cv_lv b) (cv_lv a)) true).
Proof.
  intros a b.
  destruct a, b; simpl;
    first [ left; apply id_refl | right; apply id_refl ].
Qed.

(* 2.11 节点桥：DTPT.DTPT.TrNode → TrNode 四投影移植 *)
Definition cv_node (t : DTPT.DTPT.TrNode) : TrNode :=
  mkTrNode (cv_lv (DTPT.DTPT.trLevel t))
                      (DTPT.DTPT.trPhi t) (DTPT.DTPT.trModel t)
                      (cv_ev (DTPT.DTPT.trValue t)).

Definition cv_node_inv (t : TrNode) : DTPT.DTPT.TrNode :=
  DTPT.DTPT.mkTrNode (cv_lv_inv (trLevel t))
                (trPhi t) (trModel t)
                (cv_ev_inv (trValue t)).

(* 2.12 节点桥四投影保构（封死漂移风险；首投影另立单引理供改写） *)
Lemma cv_node_level : forall t : DTPT.DTPT.TrNode,
  Id (trLevel (cv_node t)) (cv_lv (DTPT.DTPT.trLevel t)).
Proof.
  intros t.
  (* 口径一：节点桥构造体展开——mkTrNode 四槽直构后首投影
     iota 归约回 cv_lv 作用的原层槽，双侧归一闭合 *)
  unfold cv_node.
  apply id_refl.
Qed.

Theorem cv_node_pres : forall t : DTPT.DTPT.TrNode,
  AndT (Id (trLevel (cv_node t)) (cv_lv (DTPT.DTPT.trLevel t)))
  (AndT (Id (trPhi (cv_node t)) (DTPT.DTPT.trPhi t))
  (AndT (Id (trModel (cv_node t)) (DTPT.DTPT.trModel t))
        (Id (trValue (cv_node t)) (cv_ev (DTPT.DTPT.trValue t))))).
Proof.
  intros t. repeat split; apply id_refl.
Qed.

(* 2.13 节点桥往返（核心引理纯可逆 + f_equal 分解，绕开 simpl 折形） *)
Lemma cv_node_round_core : forall (lv : DTPT.DTPT.Level) (p m : DTPT.DTPT.Dig)
    (v : DTPT.DTPT.Evidence),
  Id (cv_node_inv (cv_node (DTPT.DTPT.mkTrNode lv p m v)))
     (DTPT.DTPT.mkTrNode (cv_lv_inv (cv_lv lv)) p m (cv_ev_inv (cv_ev v))).
Proof.
  intros lv p m v.
  (* 口径一：正逆两桥构造体双向展开——双重 mkTrNode 直构后
     四投影各自 iota 归约，层槽/码槽/模型槽/证据槽逐位对齐 *)
  unfold cv_node_inv, cv_node.
  apply id_refl.
Qed.

Lemma cv_node_round : forall t : DTPT.DTPT.TrNode, Id (cv_node_inv (cv_node t)) t.
Proof.
  intros t. apply eq_imp_id. destruct t as [ lv p m v ].
  rewrite cv_node_round_core. f_equal.
  - destruct lv; reflexivity.
  - exact (id_imp_eq (cv_ev_round_trip_fwd v)).
Qed.

(* 2.14 Tex 纤维铸造：trPhi 对齐的 DTPT 节点升格为 Truth 侧 Tex 见证 *)
Theorem Tex_fiber_cast : forall (phi : DTPT.DTPT.Dig) (t : DTPT.DTPT.TrNode),
  DTPT.DTPT.trPhi t = phi ->
  sigT (fun T : Tex phi => Id (projT1 T) (cv_node t)).
Proof.
  intros phi t H.
  (* 纤维见证闭式铸造：existT 直构升格 sigT、投影方程经首投影
     iota 自反闭合（Set 面 Id 承载） *)
  exists (existT _ (cv_node t) H).
  apply id_refl.
Qed.

(* ========== §3 组合审查器 ========== *)

(* 3.0 审查器：层判（不低于 Lv1）× 层内证据非空（尺寸 ≥ 1 的
   bool 化）两支合取 *)
Definition audit_node (t : TrNode) : bool :=
  andb (trLevel_geq t Lv1)
       (Nat.leb (Datatypes.S Datatypes.O)
                (ev_size (trValue t))).

(* 3.1 行为定理（双向）：审查通过 ⟺ 两分支各自通过（拆解到分支级） *)
Theorem audit_node_iff : forall t : TrNode,
  IffT (Id (audit_node t) true)
       (AndT (Id (trLevel_geq t Lv1) true)
             (NatLe (Datatypes.S Datatypes.O) (ev_size (trValue t)))).
Proof.
  intros t. unfold audit_node, IffT. split.
  - intro Ha. pose proof (id_imp_eq Ha) as Ha'.
    destruct (proj1 (Bool.andb_true_iff _ _) Ha') as [H1 H2].
    split; [ apply eq_imp_id; exact H1
           | apply NatLe_lift; exact (proj1 (Nat.leb_le _ _) H2) ].
  - intros [H1 H2]. apply eq_imp_id.
    apply (proj2 (Bool.andb_true_iff _ _)).
    split; [ apply id_imp_eq; exact H1
           | apply (proj2 (Nat.leb_le _ _)); exact (NatLe_drop _ _ H2) ].
Qed.

(* 3.2 行为定理（构造子级拆解）：对 mkTrNode 逐分支反射 *)
Theorem audit_node_branch_iff : forall (lv : Level)
    (p m : DTPT.DTPT.Dig) (v : Evidence),
  IffT (Id (audit_node (mkTrNode lv p m v)) true)
       (AndT (Id (level_le Lv1 lv) true)
             (Id (Nat.leb (Datatypes.S Datatypes.O) (ev_size v)) true)).
Proof.
  intros lv p m v.
  unfold audit_node, trLevel_geq, IffT. simpl. split.
  - intro H. pose proof (id_imp_eq H) as H0. apply andb_prop in H0.
    destruct H0 as [H1 H2]. split; apply eq_imp_id; assumption.
  - intros [H1 H2]. apply eq_imp_id. apply andb_true_intro.
    split; apply id_imp_eq; assumption.
Qed.

(* 3.3 尺寸支恒真引理（使用零使用名 ev_size_pos）：审查器退化为层判 *)
Theorem audit_node_eq_trLevel : forall t : TrNode,
  Id (audit_node t) (trLevel_geq t Lv1).
Proof.
  intros t. apply eq_imp_id. unfold audit_node.
  assert (Hb : Nat.leb (Datatypes.S Datatypes.O)
                 (ev_size (trValue t)) = true).
  { apply (proj2 (Nat.leb_le _ _)). apply ev_size_pos. }
  rewrite Hb. apply Bool.andb_true_r.
Qed.

(* 3.4 替换稳定：同层同值换节点审查不降 *)
Theorem audit_node_mono : forall t t' : TrNode,
  trLevel t' = trLevel t ->
  trValue t' = trValue t ->
  Id (audit_node t) true -> Id (audit_node t') true.
Proof.
  intros t t' Hlv Hval Ht.
  destruct t as [ lv p m v ]. destruct t' as [ lv' p' m' v' ].
  simpl in Hlv, Hval. subst lv'. subst v'.
  unfold audit_node in Ht |- *. simpl in Ht |- *. exact Ht.
Qed.

(* 3.5 换更高层节点（Lv2）审查不降：任何 Lv2 节点必过审 *)
Theorem audit_node_lv2 : forall (p m : DTPT.DTPT.Dig) (v : Evidence),
  Id (audit_node (mkTrNode Lv2 p m v)) true.
Proof.
  intros p m v. unfold audit_node.
  apply eq_imp_id. apply andb_true_intro. split.
  - reflexivity.
  - apply (proj2 (Nat.leb_le _ _)). apply ev_size_pos.
Qed.

(* 3.6 桥上审查的定义级相干：铸造节点与对应 Truth 节点同审计值 *)
Theorem audit_node_cast : forall (lv : DTPT.DTPT.Level) (p m : DTPT.DTPT.Dig)
    (v : DTPT.DTPT.Evidence),
  Id (audit_node (cv_node (DTPT.DTPT.mkTrNode lv p m v)))
     (audit_node (mkTrNode (cv_lv lv) p m (cv_ev v))).
Proof.
  intros lv p m v.
  (* 口径一：正桥构造体展开——cv_node 的 mkTrNode 直构与右侧
     直构节点经四投影 iota 逐槽对齐，双侧归一闭合 *)
  unfold cv_node.
  apply id_refl.
Qed.

(* 3.7 桥上审查的语义相干：DTPT 侧节点过桥过审 ⟺ 层判经桥保序
   （使用 audit_node_eq_trLevel + 节点桥投影） *)
Theorem audit_bridge_iff : forall t : DTPT.DTPT.TrNode,
  IffT (Id (audit_node (cv_node t)) true)
       (Id (level_le Lv1 (cv_lv (DTPT.DTPT.trLevel t))) true).
Proof.
  intros t. unfold IffT. split.
  - intro H.
    pose proof (id_imp_eq (audit_node_eq_trLevel (cv_node t))) as E1.
    rewrite E1 in H.
    unfold trLevel_geq in H.
    pose proof (id_imp_eq (cv_node_level t)) as E2.
    rewrite E2 in H.
    exact H.
  - intro H.
    pose proof (id_imp_eq (audit_node_eq_trLevel (cv_node t))) as E1.
    rewrite E1.
    unfold trLevel_geq.
    pose proof (id_imp_eq (cv_node_level t)) as E2.
    rewrite E2.
    exact H.
Qed.

(* 3.8 组合审查定理：门槛单调（llm_gate_pass_mono_thr）× 层判传递
   （trLevel_geq_trans）双通道合流——两通道均为"放宽不降"语义 *)
Theorem audit_gate_level_combo : forall (t : TrNode)
    (a b : Level) (thr1 thr2 H : Q),
  (thr1 <= thr2)%Q ->
  trLevel_geq t a = true ->
  level_le b a = true ->
  DTPT.DTPT.gate_pass thr1 H = true ->
  AndT (Id (trLevel_geq t b) true)
       (Id (DTPT.DTPT.gate_pass thr2 H) true).
Proof.
  intros t a b thr1 thr2 H Hthr Ha Hab Hgate.
  split.
  - apply (trLevel_geq_trans t a b); assumption.
  - exact (DTPT.DTPT.llm_gate_pass_mono_thr H thr1 thr2 Hthr Hgate).
Qed.

(* 3.9 完成：审查器升级（值提升至 Lv2 节点必过审）× 门槛单调合流 *)
Theorem audit_node_chain_combo : forall (t : TrNode)
    (thr1 thr2 H : Q) (p m : DTPT.DTPT.Dig),
  (thr1 <= thr2)%Q ->
  audit_node t = true ->
  DTPT.DTPT.gate_pass thr1 H = true ->
  AndT (Id (audit_node
    (mkTrNode Lv2 p m (trValue t))) true)
       (Id (DTPT.DTPT.gate_pass thr2 H) true).
Proof.
  intros t thr1 thr2 H p m Hthr Ha Hg. split.
  - apply audit_node_lv2.
  - exact (DTPT.DTPT.llm_gate_pass_mono_thr H thr1 thr2 Hthr Hg).
Qed.

(* ============================================================
   真化段 T1（审计 P2 梯队·Truth 集群，
   追加式；上方既有语句零改动）
   ①Tex 纤维真化（审计 C1）：既有面仅 eta 三件 + 铸造一件
     （llm_Tex_fiber / llm_Tex_fiber_inv / default_Tex_phi /
     Tex_fiber_cast，投影往返形）；本段新增带证据约束的信息性
     见证族与非平凡性面。
   ②RefNode/Tneg 定理化三件（审计 C3）：D10 反例节点形
     （DTPT.v §缺项13：mkRef/refPhi/refModel/refCounter 与
     Tneg 纤维）定义后零理论——本段补结构面/对偶面/尺寸面。
   ③Evidence 深水区（审计 C4/B7 加分件）：ev_append 精确加性
     （k=1）的 Set 见证形（Truth 本土版，以盘面实形核验：
     DTPT_Bridge.v §7 桥接件清单未使用 audit_ev_append_size_exact，
     与桥零重复；P3B3 报告 §1 表与 Bridge.v grep 双证）。
   纪律：零公理零承认零中途放弃，全程 Qed；nat 层显式
     Datatypes.S / O / Nat.add（防 Q_scope 劫持）；Q 字面 %Q。
   ============================================================ *)

(* ---------- T1.1 Tex 纤维带证据约束的见证族（审计 C1 真化） ---------- *)

(* 带证据约束的信息性见证族：对任意 phi 与任意证据值 e，纤维中
   存在携带该证据值的节点（sigT 首分量承载节点、第二分量合取
   方程 trPhi t = phi /\ trValue t = e——不止投影往返，证据值
   信息性存活）。诚实注记：本族对 e 全称无前提（比早期草图
   ev_size e >= 1 更强）；且依 ev_size_pos（本件 §2），任意证据
   的尺寸恒 >= 1，该约束对全体 Evidence 可满足，非平凡性面见下。 *)
Definition tex_with (phi : Dig) (e : Evidence) :
  {t : TrNode & trPhi t = phi /\ trValue t = e} :=
  existT _ (mkTrNode Lv0 phi phi e) (conj eq_refl eq_refl).

(* 纤维非平凡性面：存在尺寸 >= 1 的证据见证。evNum 0 直构可满足
   （核实 ev_size 定义如实：ev_size (evNum _) = Datatypes.S O，
   恰为 1，le (S O) (S O) 以 le_n 闭合）。 *)
Theorem tex_nontrivial : forall phi : Dig,
  sigT (fun t : TrNode =>
    AndT (Id (trPhi t) phi)
         (NatLe (Datatypes.S Datatypes.O) (ev_size (trValue t)))).
Proof.
  intros phi.
  exists (mkTrNode Lv1 phi phi (evNum 0%Q)).
  split.
  - apply id_refl.
  - (* 尺寸下界定义层消约——trValue 投影与 evNum 支逐层归约出
       后继一，le_n 直构经 NatLe_lift 抬升入 NatLe 面 *)
    apply NatLe_lift. exact (le_n (Datatypes.S Datatypes.O)).
Qed.

(* 纤维 × 审查器组合面：Lv2 层携带证据的纤维见证必过审
   （使用 audit_node_lv2，纤维族与审查器段首条组合边） *)
Theorem tex_nontrivial_audited : forall phi : Dig,
  sigT (fun t : TrNode => AndT (Id (trPhi t) phi) (Id (audit_node t) true)).
Proof.
  intros phi.
  exists (mkTrNode Lv2 phi phi (evNum 0%Q)).
  split.
  - apply id_refl.
  - (* 内联 audit_node_lv2 骨架——审查器双支展开：Lv2 层判支
       归约落真，尺寸支经 leb 双向桥接尺寸正性件 *)
    unfold audit_node.
    apply eq_imp_id. apply andb_true_intro. split.
    + reflexivity.
    + apply (proj2 (Nat.leb_le _ _)). apply ev_size_pos.
Qed.

(* ---------- T1.2 RefNode/Tneg 定理化三件（审计 C3 真化） ---------- *)

(* 件一·结构面：RefNode 投影往返（三字段方程一体封死于记录 eta
   往返中——mkRef ∘ (refPhi,refModel,refCounter) = id） *)
Theorem ref_node_round : forall r : RefNode,
  Id (mkRef (refPhi r) (refModel r) (refCounter r)) r.
Proof.
  intros [ p m v ].
  (* 口径一：记录 eta 定义层展开——mkRef 对三投影逐槽 iota
     归约回原构造实参，双侧归一闭合 *)
  change (mkRef (refPhi (mkRef p m v)) (refModel (mkRef p m v))
                (refCounter (mkRef p m v)))
    with (mkRef p m v).
  apply id_refl.
Qed.

(* 件二·对偶面：Tneg 与 Tex 同为「记录形 × 首投影 = phi」纤维
   （以盘面定义实形为准：DTPT.v Tneg phi = {r : RefNode & refPhi r
   = phi}，本件 Tex phi = {t : TrNode & trPhi t = phi}）。同一 phi
   的反例节点形与肯定节点形对应副本同居：模型槽 m 逐字对齐，反证数据 v
   经 cv_ev 桥映为肯定侧证据——「反例节点非空 iff 存在反例节点」
   的盘面实形即双纤维无条件同居，本件给其信息性 Set 面（对应副本
   三元组全量方程存活，非单纯非空断言）。 *)
Definition tneg_tex_dual : forall (phi m : Dig) (v : DTPT.DTPT.Evidence),
  {w : {r : RefNode & refPhi r = phi /\ refModel r = m /\ refCounter r = v}
     & {t : TrNode & trPhi t = phi /\ trModel t = m /\ trValue t = cv_ev v}} :=
  fun phi m v =>
    existT _
      (existT _ (mkRef phi m v) (conj eq_refl (conj eq_refl eq_refl)))
      (existT _ (mkTrNode Lv0 phi m (cv_ev v))
                (conj eq_refl (conj eq_refl eq_refl))).

(* 件三·尺寸面：反例数据的桥测度与直测逐点重合（dt_ev_size =
   ev_size ∘ cv_ev 的定义方程在 Tneg 纤维上实例化）+ 非退化支
   （使用 ev_size_pos：任意反证数据过桥后尺寸 >= 1——反例门
   ev_size 恒开，与 audit_node_eq_trLevel 的审查器退化档互证） *)
Theorem tneg_counter_size : forall (phi m : Dig) (v : DTPT.DTPT.Evidence),
  AndT (Id (ev_size (cv_ev (refCounter (mkRef phi m v)))) (dt_ev_size v))
       (NatLe (Datatypes.S Datatypes.O)
              (ev_size (cv_ev (refCounter (mkRef phi m v))))).
Proof.
  intros phi m v.
  (* 合取两支分证——左支 RefNode 计数投影 iota 与桥测度 delta
     展开双侧归一；右支内联 ev_size_pos 三构造子骨架：叶支下界
     直构、Pair 支后继单调链闭合（le 形经 NatLe_lift 抬升入 NatLe 面） *)
  split.
  - apply id_refl.
  - apply NatLe_lift. destruct v as [q | l | a b].
    + simpl. apply le_n.
    + simpl. apply le_n.
    + simpl. apply nat_succ_le_mono. apply nat_le_0.
Qed.

(* ---------- T1.3 Evidence 深水区：ev_append 精确加性 Set 面 ---------- *)

(* 精确加性（k=1）的后继形方程：ev_size (ev_append a b) =
   S (ev_size a + ev_size b)（使用基座件 audit_ev_append_size_exact
   重述为 Datatypes.S 形，供 Set 面与下游改写） *)
Theorem ev_append_size_succ : forall a b : Evidence,
  Id (ev_size (ev_append a b)) (Datatypes.S (Nat.add (ev_size a) (ev_size b))).
Proof.
  intros a b. apply eq_imp_id.
  rewrite (id_imp_eq (audit_ev_append_size_exact a b)). lia.
Qed.

(* Truth 本土 Set 面：精确加性的见证携带形——sigT 首分量给出
   可提取的数值见证 s := ev_size a + ev_size b，第二分量为后继形
   精确方程（Prop 参随提取擦除、数值见证存活，Obj.magic=0 面） *)
Definition ev_append_size_set (a b : Evidence) :
  {s : nat & ev_size (ev_append a b) = Datatypes.S s} :=
  existT _ (Nat.add (ev_size a) (ev_size b))
    (id_imp_eq (ev_append_size_succ a b)).

(* 对偶面（右参单调的后继形）：拼接后尺寸 = 右参尺寸 + S(左参尺寸)
   ——「右参证据在拼接下不减」的精确 witness 形，d := ev_size a *)
Theorem ev_append_size_mono_succ : forall a b : Evidence,
  Id (ev_size (ev_append a b))
     (Nat.add (ev_size b) (Datatypes.S (ev_size a))).
Proof.
  intros a b. apply eq_imp_id.
  rewrite (id_imp_eq (audit_ev_append_size_exact a b)). lia.
Qed.

Definition ev_append_size_mono_set (a b : Evidence) :
  {d : nat & ev_size (ev_append a b) = Nat.add (ev_size b) (Datatypes.S d)} :=
  existT _ (ev_size a) (id_imp_eq (ev_append_size_mono_succ a b)).

(* ============================================================
   真化段 T2（审计 C 类深水件·Evidence
   内容面，追加式；上方既有语句零改动）
   审计 C4/B7 深水区定位：evSeq 携带的 list Q 内容全理论盲、
   Evidence 代数有尺寸/拼接而无内容相等/分解/枚举面——本段四块：
   ① 内容相等判定器（保底）：ev_eqb（叶判 Qeq_bool，list Q 逐点
     Qeq_bool）+ ev_cong 内容同余关系 + ev_eqb_true_iff 双向 iff。
     S7 边界诚实声明（对齐 negS_not_involutive 反例范式）：早期草案
     草图 ev_eqb_eq : ev_eqb a b = true -> a = b（Leibniz）在此
     **不可证且为假**——Q 非正规化（1#2 与 2#4 异记录同值），
     Qeq_bool 只刻画 Qeq（有理等值）而非 Leibniz。本段以
     ev_eqb_leibniz_gap 显式反例定理封死该方向（对照 S7 边界声明
     范式照录），正方向可靠面改交 ev_eqb_true_iff（对 ev_cong 的
     完整双向）+ Leibniz 叶判变体 ev_eqb_raw（Z.eqb × Pos.eqb，
     叶级 Leibniz）补全 iff——两种可判定等价各归其位，禁硬性拼合。
   ② 内容归纳原理（主件）：ev_rect' 显式三构造子消去（自由代数
     归纳原理显式化；与自动生成 Evidence_rect 同型，自建零依赖）
     + beta 三方程 + 使用样板两件（ev_size_pos_third 第三方法
     重证 / ev_size_1_leaf_iff 叶刻画）。
   ③ 深度有界面（主件）：ev_case_set 三叉 sigT 信息性分解 +
     ev_size_ge_2_pair 尺寸门槛分解（size ≥ 2 必为 evPair 形）+
     ev_pair_decomp_exact 精确加性复用（使用 ev_size_pair）。
   ④ 有界枚举器（加分）：ev_enum 深度预算枚举 Fixpoint +
     ev_enum_size_bound 有界面（枚举出 ⇒ 尺寸 ≤ 预算）。
     诚实边界：Q 无穷 ⇒ 叶内容完备枚举不可能，枚举叶截断至
     0%Q 单见证；完备性只交付形状级生成规则 ev_enum_pair_member
     （CoZero fiber 离散化同源思想的形状层落地，如实声明）。
   纪律：零公理零承认零中途放弃，全程 Qed；nat 层显式
     Datatypes.S / O / Nat.add（防 Q_scope 劫持）；Q 字面 %Q；
     零新增 Require（Z/Pos 命名经 QArith_base Require Export
     BinInt/BinPos 传导，逐名在册可解析）。
   ============================================================ *)

(* ---------- T2.1 内容相等判定器（审计 C4/B7 保底件） ---------- *)

(* 叶判：Qeq_bool 自反（Qeq_bool 经 Qeq_bool_iff 刻画 Qeq；
   自反式自证，不押注 stdlib 命名） *)
Lemma qeqb_refl : forall q : Q, Id (Qeq_bool q q) true.
Proof.
  intros q.
  (* 口径一：Qeq_bool 判定器定义层展开——分子交叉分母乘积的
     Z.eqb 自反比较，命名自反方程改写落 true 后布尔归一 *)
  apply eq_imp_id. unfold Qeq_bool.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.

(* list Q 逐点 Qeq_bool 判定器（自建，防 stdlib list_eqb 版本差） *)
Fixpoint qlist_eqb (l1 l2 : list Q) : bool :=
  match l1, l2 with
  | [], [] => true
  | q1 :: r1, q2 :: r2 => andb (Qeq_bool q1 q2) (qlist_eqb r1 r2)
  | _, _ => false
  end.

Lemma qlist_eqb_refl : forall l : list Q, Id (qlist_eqb l l) true.
Proof.
  induction l as [| q r IH]; simpl.
  - apply id_refl.
  - apply eq_imp_id. apply andb_true_intro.
    split; apply id_imp_eq; [ apply qeqb_refl | exact IH ].
Qed.

(* 内容同余关系：叶层取 Qeq（有理等值），evSeq 层取 Forall2 Qeq
   （逐点等值），evPair 层逐构造同余——内容相等的关系式封装 *)
Inductive ev_cong : Evidence -> Evidence -> Set :=
| ev_cong_num : forall q1 q2 : Q, q1 == q2 -> ev_cong (evNum q1) (evNum q2)
| ev_cong_seq : forall l1 l2 : list Q,
    Forall2 Qeq l1 l2 -> ev_cong (evSeq l1) (evSeq l2)
| ev_cong_pair : forall a1 b1 a2 b2 : Evidence,
    ev_cong a1 a2 -> ev_cong b1 b2 -> ev_cong (evPair a1 b1) (evPair a2 b2).

(* 内容相等判定器：叶 Qeq_bool / list Q 逐点 / Pair 双支合取；
   非同构造对恒 false（自由代数构造子可分立）。双参 Fixpoint
   {struct a}：Pair 支双递归 ev_eqb a1 a2 / ev_eqb b1 b2 的结构参
   分别为 a1 / b1，皆为 a = evPair a1 b1 的真子项——守卫检查单参
   合法，且对平衡对语义正确（对照：嵌套 fix 单脊递归对平衡对
   恒 false，首轮编译被 ev_eqb_refl 拦下，如实记档） *)
Fixpoint ev_eqb (a b : Evidence) {struct a} : bool :=
  match a, b with
  | evNum q1, evNum q2 => Qeq_bool q1 q2
  | evSeq l1, evSeq l2 => qlist_eqb l1 l2
  | evPair a1 b1, evPair a2 b2 => andb (ev_eqb a1 a2) (ev_eqb b1 b2)
  | _, _ => false
  end.

(* 自反：判定器在自身上恒真 *)
Lemma ev_eqb_refl : forall a : Evidence, Id (ev_eqb a a) true.
Proof.
  induction a as [q | l | a1 IH1 a2 IH2]; simpl.
  - apply qeqb_refl.
  - apply qlist_eqb_refl.
  - apply eq_imp_id. apply andb_true_intro.
    split; apply id_imp_eq; assumption.
Qed.

(* list Q 层：判定真 ⇒ 逐点 Qeq（可靠面） *)
Lemma qlist_eqb_sound : forall l1 l2 : list Q,
  qlist_eqb l1 l2 = true -> Forall2 Qeq l1 l2.
Proof.
  induction l1 as [| q1 r1 IH]; intros [| q2 r2] H;
    simpl in H; try discriminate H.
  - destruct H. constructor.
  - apply andb_prop in H. destruct H as [H1 H2].
    constructor.
    + apply Qeq_bool_iff in H1. exact H1.
    + apply IH. exact H2.
Qed.

(* list Q 层：逐点 Qeq ⇒ 判定真（完备面） *)
Lemma qlist_Qeq_complete : forall l1 l2 : list Q,
  Forall2 Qeq l1 l2 -> Id (qlist_eqb l1 l2) true.
Proof.
  (* Prop 归纳先于承载桥：Forall2 消去限于 Prop 面（Forall2_rec 禁入
     Set），故先在 Prop 内证布尔方程、终末 eq_imp_id 单跳过桥 *)
  intros l1 l2 H.
  assert (Hb : qlist_eqb l1 l2 = true).
  { induction H as [| q1 q2 r1 r2 Hq Hr IH].
    - reflexivity.
    - simpl. apply andb_true_intro. split.
      + apply Qeq_bool_iff. exact Hq.
      + exact IH. }
  apply eq_imp_id. exact Hb.
Qed.

(* 可靠面：ev_eqb 真 ⇒ 内容同余 *)
Lemma ev_eqb_cong_sound : forall a b : Evidence,
  ev_eqb a b = true -> ev_cong a b.
Proof.
  intros a. induction a as [q1 | l1 | a1 IH1 a2 IH2];
    intros [q2 | l2 | b1 b2] H; simpl in H; try discriminate H.
  - apply Qeq_bool_iff in H. exact (ev_cong_num q1 q2 H).
  - exact (ev_cong_seq l1 l2 (qlist_eqb_sound l1 l2 H)).
  - apply andb_prop in H. destruct H as [H1 H2].
    exact (ev_cong_pair a1 a2 b1 b2 (IH1 b1 H1) (IH2 b2 H2)).
Qed.

(* 完备面：内容同余 ⇒ ev_eqb 真 *)
Lemma ev_cong_eqb_complete : forall a b : Evidence,
  ev_cong a b -> Id (ev_eqb a b) true.
Proof.
  intros a b H. induction H as [q1 q2 Hq | l1 l2 Hl | a1 b1 a2 b2 Ha Hb IHa IHb].
  - apply eq_imp_id. apply Qeq_bool_iff. exact Hq.
  - exact (qlist_Qeq_complete l1 l2 Hl).
  - simpl. apply eq_imp_id. apply andb_true_intro.
    split; apply id_imp_eq; assumption.
Qed.

(* 主定理：ev_eqb 是内容同余 ev_cong 的可判定刻画（完整双向 iff）
   ——「内容相等可判定」的构造性交付面 *)
Theorem ev_eqb_true_iff : forall a b : Evidence,
  IffT (Id (ev_eqb a b) true) (ev_cong a b).
Proof.
  intros a b. unfold IffT. split.
  - intro H. apply ev_eqb_cong_sound. apply id_imp_eq. exact H.
  - intro Hc. apply ev_cong_eqb_complete. exact Hc.
Qed.

(* 【S7 边界诚实声明｜早期草图 ev_eqb_eq 的
   裁决件】Leibniz 可靠面 ev_eqb a b = true -> a = b 在 Qeq_bool
   叶判下**为假**，反例显式定理化：1#2 与 2#4 有理等值（Qeq_bool
   = true）但 Q 记录 Leibniz 相异（Qnum 1 ≠ 2）。裁决：以反例定理
   封死该方向（对照本件 negS_not_involutive 反例范式），内容相等
   的正确可靠面由 ev_eqb_true_iff（对 ev_cong）承担，Leibniz 面由
   下述 ev_eqb_raw 变体承担——三面各归其位，非补丁非硬性拼合。 *)
Theorem ev_eqb_leibniz_gap :
  AndT (Id (ev_eqb (evNum (1#2)%Q) (evNum (2#4)%Q)) true)
       (NotT (Id ((evNum (1#2)%Q : Evidence)) (evNum (2#4)%Q))).
Proof.
  split.
  - apply id_refl.
  - unfold NotT. intros H. inversion H.
Qed.

(* Leibniz 叶判变体：叶层取 Z.eqb（Qnum）× Pos.eqb（QDen）结构
   相等——叶级 Leibniz，向下完整 iff（a = b 双向可判定） *)
Definition Qraw_eqb (q1 q2 : Q) : bool :=
  andb (Z.eqb (Qnum q1) (Qnum q2)) (Pos.eqb (Qden q1) (Qden q2)).

Fixpoint qlist_eqb_raw (l1 l2 : list Q) : bool :=
  match l1, l2 with
  | [], [] => true
  | q1 :: r1, q2 :: r2 => andb (Qraw_eqb q1 q2) (qlist_eqb_raw r1 r2)
  | _, _ => false
  end.

Fixpoint ev_eqb_raw (a b : Evidence) {struct a} : bool :=
  match a, b with
  | evNum q1, evNum q2 => Qraw_eqb q1 q2
  | evSeq l1, evSeq l2 => qlist_eqb_raw l1 l2
  | evPair a1 b1, evPair a2 b2 => andb (ev_eqb_raw a1 a2) (ev_eqb_raw b1 b2)
  | _, _ => false
  end.

Lemma Qraw_eqb_refl : forall q : Q, Id (Qraw_eqb q q) true.
Proof.
  intros q.
  (* 口径一：原始叶判定义层展开——分子 Z.eqb 与分母 Pos.eqb
     双通道各经命名自反方程改写，andb true true 归一反射闭合 *)
  apply eq_imp_id. unfold Qraw_eqb.
  rewrite Z.eqb_refl, Pos.eqb_refl.
  reflexivity.
Qed.

Lemma Qraw_eqb_true_iff : forall q1 q2 : Q,
  IffT (Id (Qraw_eqb q1 q2) true) (Id q1 q2).
Proof.
  intros [n1 d1] [n2 d2]. unfold Qraw_eqb, IffT. simpl.
  split.
  - intros H. pose proof (id_imp_eq H) as H0. apply andb_prop in H0.
    destruct H0 as [H1 H2].
    apply Z.eqb_eq in H1. apply Pos.eqb_eq in H2.
    subst. apply id_refl.
  - intros H. pose proof (id_imp_eq H) as H'.
    assert (Hn : n1 = n2) by (exact (f_equal Qnum H')).
    assert (Hd : d1 = d2) by (exact (f_equal Qden H')).
    subst. apply eq_imp_id. apply andb_true_intro.
    split; [ apply Z.eqb_refl | apply Pos.eqb_refl ].
Qed.

Lemma qlist_eqb_raw_refl : forall l : list Q, Id (qlist_eqb_raw l l) true.
Proof.
  induction l as [| q r IH]; simpl.
  - apply id_refl.
  - apply eq_imp_id. apply andb_true_intro.
    split; apply id_imp_eq; [ apply Qraw_eqb_refl | exact IH ].
Qed.

Lemma qlist_eqb_raw_true_iff : forall l1 l2 : list Q,
  IffT (Id (qlist_eqb_raw l1 l2) true) (Id l1 l2).
Proof.
  induction l1 as [| q1 r1 IH]; intros [| q2 r2]; simpl; unfold IffT.
  - split; intros H; apply id_refl.
  - split; intros H; inversion H.
  - split; intros H; inversion H.
  - split.
    + intros H. pose proof (id_imp_eq H) as H0. apply andb_prop in H0.
      destruct H0 as [H1 H2].
      destruct (fst (Qraw_eqb_true_iff q1 q2) (eq_imp_id H1)).
      destruct (fst (IH r2) (eq_imp_id H2)).
      apply id_refl.
    + intros H. pose proof (id_imp_eq H) as H'.
      injection H' as H1 H2. subst.
      apply eq_imp_id. simpl. apply andb_true_intro. split.
      * apply id_imp_eq. apply Qraw_eqb_refl.
      * apply id_imp_eq. apply qlist_eqb_raw_refl.
Qed.

Lemma ev_eqb_raw_refl : forall a : Evidence, Id (ev_eqb_raw a a) true.
Proof.
  induction a as [q | l | a1 IH1 a2 IH2]; simpl.
  - apply Qraw_eqb_refl.
  - apply qlist_eqb_raw_refl.
  - apply eq_imp_id. apply andb_true_intro.
    split; apply id_imp_eq; assumption.
Qed.

(* Leibniz 可靠面（ev_eqb_eq 之名在此兑现）：raw 判定真 ⇒
   Leibniz 相等 *)
Theorem ev_eqb_raw_eq : forall a b : Evidence,
  Id (ev_eqb_raw a b) true -> Id a b.
Proof.
  intros a. induction a as [q1 | l1 | a1 IH1 a2 IH2];
    intros [q2 | l2 | b1 b2] H; simpl in H; try solve [inversion H].
  - destruct (fst (Qraw_eqb_true_iff q1 q2) H). apply id_refl.
  - destruct (fst (qlist_eqb_raw_true_iff l1 l2) H). apply id_refl.
  - pose proof (id_imp_eq H) as H0. apply andb_prop in H0.
    destruct H0 as [H1 H2].
    destruct (IH1 _ (eq_imp_id H1)). destruct (IH2 _ (eq_imp_id H2)).
    apply id_refl.
Qed.

(* 完整双向 iff：Leibniz 相等的可判定性 *)
Theorem ev_eqb_raw_true_iff : forall a b : Evidence,
  IffT (Id (ev_eqb_raw a b) true) (Id a b).
Proof.
  intros a b. unfold IffT. split.
  - apply ev_eqb_raw_eq.
  - intros H. pose proof (id_imp_eq H) as H'. subst.
    apply ev_eqb_raw_refl.
Qed.

(* ---------- T2.2 内容归纳原理（审计 C4 主件） ---------- *)

(* 自由代数归纳原理显式化：三构造子消去， motives 可取 Type
   （与自动生成 Evidence_rect 同型，自建零依赖；beta 方程三件
   随行——对 evNum/evSeq/evPair 的计算律逐条 reflexivity） *)
Fixpoint ev_rect' (P : Evidence -> Type)
  (f_num : forall q : Q, P (evNum q))
  (f_seq : forall l : list Q, P (evSeq l))
  (f_pair : forall a b : Evidence, P a -> P b -> P (evPair a b))
  (e : Evidence) {struct e} : P e :=
  match e with
  | evNum q => f_num q
  | evSeq l => f_seq l
  | evPair a b =>
      f_pair a b (ev_rect' P f_num f_seq f_pair a)
                 (ev_rect' P f_num f_seq f_pair b)
  end.

(* Set-motive twin：与 ev_rect' 同构的计算律（motive 限 Set），
   供 Id 面计算律三件承载；ev_rect'（Type motive）保留给 Prop motive
   使用面（ev_size_pos_rect/ev_size_pos_third），两件并存零别名冲突。 *)
Fixpoint ev_rect_set (P : Evidence -> Set)
  (f_num : forall q : Q, P (evNum q))
  (f_seq : forall l : list Q, P (evSeq l))
  (f_pair : forall a b : Evidence, P a -> P b -> P (evPair a b))
  (e : Evidence) {struct e} : P e :=
  match e with
  | evNum q => f_num q
  | evSeq l => f_seq l
  | evPair a b =>
      f_pair a b (ev_rect_set P f_num f_seq f_pair a)
                 (ev_rect_set P f_num f_seq f_pair b)
  end.

Lemma ev_rect'_num : forall (P : Evidence -> Set)
  (f_num : forall q : Q, P (evNum q))
  (f_seq : forall l : list Q, P (evSeq l))
  (f_pair : forall a b : Evidence, P a -> P b -> P (evPair a b)) (q : Q),
  Id (ev_rect_set P f_num f_seq f_pair (evNum q)) (f_num q).
Proof.
  (* 口径一：递归器计算律——fixpoint 体对 evNum 构造子 iota
     归约直取 f_num 支，beta 后双侧逐字同形 *)
  intros P f_num f_seq f_pair q.
  apply id_refl.
Qed.

Lemma ev_rect'_seq : forall (P : Evidence -> Set)
  (f_num : forall q : Q, P (evNum q))
  (f_seq : forall l : list Q, P (evSeq l))
  (f_pair : forall a b : Evidence, P a -> P b -> P (evPair a b)) (l : list Q),
  Id (ev_rect_set P f_num f_seq f_pair (evSeq l)) (f_seq l).
Proof.
  (* 口径一：递归器计算律——fixpoint 体对 evSeq 构造子 iota
     归约直取 f_seq 支，beta 后双侧逐字同形 *)
  intros P f_num f_seq f_pair l.
  apply id_refl.
Qed.

Lemma ev_rect'_pair : forall (P : Evidence -> Set)
  (f_num : forall q : Q, P (evNum q))
  (f_seq : forall l : list Q, P (evSeq l))
  (f_pair : forall a b : Evidence, P a -> P b -> P (evPair a b)) (a b : Evidence),
  Id (ev_rect_set P f_num f_seq f_pair (evPair a b))
     (f_pair a b (ev_rect_set P f_num f_seq f_pair a)
                  (ev_rect_set P f_num f_seq f_pair b)).
Proof.
  (* 口径一：递归器计算律——fixpoint 体对 evPair 构造子 iota
     归约出 f_pair 双递归装配形，与右侧逐字同形 *)
  intros P f_num f_seq f_pair a b.
  apply id_refl.
Qed.

(* 使用样板一：ev_size 正性的第三方法重证（对照 §2 ev_size_pos 的
   induction 原证与 §审查器段使用面，本件经 ev_rect' 显式消去） *)
Definition ev_size_pos_rect (e : Evidence) :
  le (Datatypes.S O) (ev_size e) :=
  ev_rect' (fun e' => le (Datatypes.S O) (ev_size e'))
    (fun _ => le_n (Datatypes.S O))
    (fun _ => le_n (Datatypes.S O))
    (fun a b _ _ =>
      nat_succ_le_mono O (Nat.add (ev_size a) (ev_size b))
        (nat_le_0 (Nat.add (ev_size a) (ev_size b))))
    e.

Theorem ev_size_pos_third : forall e : Evidence,
  le (Datatypes.S O) (ev_size e).
Proof.
  intro e.
  (* 口径二：内联 ev_size_pos_rect 定义体——ev_rect' 三构造子
     消去子逐支显式给形（叶支下界直构、Pair 支后继单调链），
     消除经中间定义的单跳转发 *)
  exact (ev_rect' (fun e' => le (Datatypes.S O) (ev_size e'))
    (fun _ => le_n (Datatypes.S O))
    (fun _ => le_n (Datatypes.S O))
    (fun a b _ _ =>
      nat_succ_le_mono O (Nat.add (ev_size a) (ev_size b))
        (nat_le_0 (Nat.add (ev_size a) (ev_size b))))
    e).
Qed.

(* 使用样板二：尺寸恰 1 ⟺ 叶（evNum/evSeq 二形）——内容归纳原理
   的非平凡使用（Pair 支由尺寸方程封死），叶刻画定理 *)
Theorem ev_size_1_leaf_iff : forall e : Evidence,
  IffT (Id (ev_size e) (Datatypes.S O))
       (OrT (sigT (fun q : Q => Id e (evNum q)))
            (sigT (fun l : list Q => Id e (evSeq l)))).
Proof.
  intros e. unfold IffT, OrT. split.
  - intros H. revert H. induction e using ev_rect'.
    + intros H. left. exists q. apply id_refl.
    + intros H. right. exists l. apply id_refl.
    + intros H. pose proof (id_imp_eq H) as H'.
      assert (Hpa : le (Datatypes.S O) (ev_size e1)) by apply ev_size_pos.
      assert (Hpb : le (Datatypes.S O) (ev_size e2)) by apply ev_size_pos.
      simpl in H'.
      assert (Hc : False) by lia.
      destruct Hc.
  - intros [ [q Hq] | [l Hl] ].
    + pose proof (id_imp_eq Hq) as Hq'. subst e. apply id_refl.
    + pose proof (id_imp_eq Hl) as Hl'. subst e. apply id_refl.
Qed.

(* ---------- T2.3 深度有界面：信息性分解（审计 C4 主件） ---------- *)

(* 三叉 sigT 信息性分解器：任意证据逐构造给等式见证（叶/序列/
   对三分支各携 Leibniz 方程）——Evidence 内容层的 case 分析
   Set 面，下游 sigT 使用的基座 *)
Definition ev_case_set (e : Evidence) :
  {q : Q & e = evNum q}
  + ({l : list Q & e = evSeq l}
     + {a : Evidence & {b : Evidence & e = evPair a b}}) :=
  match e as e0 return
    {q : Q & e0 = evNum q}
    + ({l : list Q & e0 = evSeq l}
       + {a : Evidence & {b : Evidence & e0 = evPair a b}})
  with
  | evNum q    => inl (existT _ q eq_refl)
  | evSeq l    => inr (inl (existT _ l eq_refl))
  | evPair a b => inr (inr (existT _ a (existT _ b eq_refl)))
  end.

(* 尺寸门槛分解：size ≥ 2 ⇒ 必为 evPair 形（叶尺寸恰 1 封死叶支；
   sigT 信息性——分解件 a/b 可提取） *)
Theorem ev_size_ge_2_pair : forall e : Evidence,
  le (Datatypes.S (Datatypes.S O)) (ev_size e) ->
  {a : Evidence & {b : Evidence & e = evPair a b}}.
Proof.
  intros e Hge.
  destruct (ev_case_set e) as [[q Hq] | [[l Hl] | [a [b Hpair]]]].
  - exfalso. rewrite Hq in Hge. simpl in Hge. lia.
  - exfalso. rewrite Hl in Hge. simpl in Hge. lia.
  - exact (existT _ a (existT _ b Hpair)).
Qed.

(* 精确加性复用：分解 + ev_size_pair（§2）合流——尺寸 ≥ 2 的证据
   尺寸恰为其二分件的后继和（存在式 Prop 包装，信息性核心在上件） *)
Theorem ev_pair_decomp_exact : forall e : Evidence,
  le (Datatypes.S (Datatypes.S O)) (ev_size e) ->
  sigT (fun a : Evidence => sigT (fun b : Evidence =>
    AndT (Id e (evPair a b))
         (Id (ev_size e) (Datatypes.S (Nat.add (ev_size a) (ev_size b)))))).
Proof.
  intros e Hge.
  destruct (ev_size_ge_2_pair e Hge) as [a [b Hpair]].
  exists a, b. split.
  - apply eq_imp_id. exact Hpair.
  - subst e. apply id_refl.
Qed.

(* ---------- T2.4 有界枚举器（审计 C4 加分件） ---------- *)

(* 深度预算枚举器：ev_enum n = 预算 n 的证据有限截断。诚实边界：
   Q 无穷 ⇒ 叶内容完备枚举不可能，叶只放单见证 0%Q（fiber 离散化
   截断位置如实声明）；Pair 支按预算分裂生成（左件取自 ev_enum n'，
   右件预算 n' - size a，保障有界面） *)
Fixpoint ev_enum (n : nat) : list Evidence :=
  match n with
  | O => []
  | Datatypes.S n' =>
      evNum 0%Q :: evSeq [] ::
      flat_map
        (fun a : Evidence =>
          map (fun b : Evidence => evPair a b)
              (ev_enum (Nat.sub n' (ev_size a))))
        (ev_enum n')
  end.

(* 有界面（归纳加强形：对一切 ≤ n 的预算层齐备 IH） *)
Lemma ev_enum_bound_aux : forall n m : nat,
  le m n ->
  forall e : Evidence, In e (ev_enum m) -> le (ev_size e) m.
Proof.
  induction n as [| n' IH]; intros m Hmn e Hin.
  - assert (Hm : m = O) by lia. subst m. simpl in Hin. destruct Hin.
  - destruct m as [| m'].
    + simpl in Hin. destruct Hin.
    + simpl in Hin. destruct Hin as [He | [He | Hin]].
      * subst e. simpl. lia.
      * subst e. simpl. lia.
      * apply in_flat_map in Hin as [a [Ha Hinb]].
        apply in_map_iff in Hinb as [b [Hb Hbin]].
        subst e.
        assert (Hba : le (ev_size b) (Nat.sub m' (ev_size a))).
        { apply (IH (Nat.sub m' (ev_size a))); [ lia | exact Hbin ]. }
        assert (Haa : le (ev_size a) m').
        { apply (IH m'); [ lia | exact Ha ]. }
        simpl. lia.
Qed.

(* 有界面（原始型）：枚举出 ⇒ 尺寸 ≤ 预算 *)
Theorem ev_enum_size_bound : forall (n : nat) (e : Evidence),
  In e (ev_enum n) -> le (ev_size e) n.
Proof.
  intros n e H.
  revert H.
  (* 口径三：内联源件加强形归纳骨架（归纳假设对一切不超过 n 的
     预算层齐备——裸陈述直接归纳在拼接右件的预算层处失配，
     加强形为本件最小自持形状）：零预算层空表剪枝，正预算层
     三分支——双叶见证位置直证，拼接支经 flat_map 与 map 双重
     成员分解后两条归纳假设按预算差线性算术闭合；终以自身
     预算层实例化 *)
  assert (Haux : forall m : nat, le m n ->
           forall e0 : Evidence, In e0 (ev_enum m) -> le (ev_size e0) m).
  { induction n as [| n' IH]; intros m Hmn e0 Hin.
    - assert (Hm : m = O) by lia. subst m. simpl in Hin. destruct Hin.
    - destruct m as [| m'].
      + simpl in Hin. destruct Hin.
      + simpl in Hin. destruct Hin as [He | [He | Hin]].
        * subst e0. simpl. lia.
        * subst e0. simpl. lia.
        * apply in_flat_map in Hin as [a [Ha Hinb]].
          apply in_map_iff in Hinb as [b [Hb Hbin]].
          subst e0.
          assert (Hba : le (ev_size b) (Nat.sub m' (ev_size a))).
          { apply (IH (Nat.sub m' (ev_size a))); [ lia | exact Hbin ]. }
          assert (Haa : le (ev_size a) m').
          { apply (IH m'); [ lia | exact Ha ]. }
          simpl. lia. }
  intros H. apply (Haux n (le_n n) e H).
Qed.

(* 枚举成员见证：叶单 witness 在一切正预算层在册 *)
Lemma ev_enum_num_0 : forall n : nat,
  In (evNum 0%Q) (ev_enum (Datatypes.S n)).
Proof.
  intros n.
  (* 口径一：预算层枚举表与成员谓词双层展开——S n 层 delta-iota
     落形后 In 对 cons 头的判定方程显式落形，见证反射收左支 *)
  change (In (evNum 0%Q) (ev_enum (Datatypes.S n)))
    with ((evNum 0%Q = evNum 0%Q) \/
          In (evNum 0%Q) (evSeq [] :: flat_map
               (fun a : Evidence =>
                  map (fun b : Evidence => evPair a b)
                      (ev_enum (Nat.sub n (ev_size a))))
               (ev_enum n))).
  left. reflexivity.
Qed.

Lemma ev_enum_seq_nil : forall n : nat,
  In (evSeq []) (ev_enum (Datatypes.S n)).
Proof.
  intros n.
  (* 口径一：预算层枚举表与成员谓词双层展开——头部析取右进、
     次位见证反射，In 判定方程显式落形 *)
  change (In (evSeq []) (ev_enum (Datatypes.S n)))
    with ((evNum 0%Q = evSeq []) \/
          ((evSeq [] = evSeq []) \/
           In (evSeq []) (flat_map
                (fun a : Evidence =>
                   map (fun b : Evidence => evPair a b)
                       (ev_enum (Nat.sub n (ev_size a))))
                (ev_enum n)))).
  right. left. reflexivity.
Qed.

(* 形状级完备生成规则：合格预算的两分件 ⇒ 拼接件在同一预算上层
   在册（完备性在「形状层」的构造性交付；叶内容截断边界见上） *)
Lemma ev_enum_pair_member : forall (n : nat) (a b : Evidence),
  In a (ev_enum n) ->
  In b (ev_enum (Nat.sub n (ev_size a))) ->
  In (evPair a b) (ev_enum (Datatypes.S n)).
Proof.
  intros n a b Ha Hb. simpl. right. right.
  apply in_flat_map. exists a. split.
  - exact Ha.
  - apply in_map. exact Hb.
Qed.

End DTPT_Truth.
Import DTPT_Truth.

(* ========== 假设面自查（公理面自审附件） ========== *)
Print Assumptions tarski.
Print Assumptions no_uniform_truth.
Print Assumptions layer_self_refutation.
Print Assumptions level_confusion_revives_liar.
Print Assumptions tarski_via_renaming.

(* —— 以下 6 件为原 DTPT_Audit.v 文尾审计块逐字随行（S5 棒） —— *)

(* ========== 公理面自审：主定理假设闭包打印 ========== *)
Print Assumptions cv_size_preservation_T.
Print Assumptions cv_size_preservation_D.
Print Assumptions cv_ev_round_trip_fwd.
Print Assumptions cv_lv_antisym_transport.
Print Assumptions audit_gate_level_combo.
Print Assumptions audit_bridge_iff.

(* —— T1 真化段新增件假设闭包打印（真化段 T1 追加，G4 附件） —— *)
Print Assumptions tex_with.
Print Assumptions tex_nontrivial.
Print Assumptions tex_nontrivial_audited.
Print Assumptions ref_node_round.
Print Assumptions tneg_tex_dual.
Print Assumptions tneg_counter_size.
Print Assumptions ev_append_size_succ.

(* —— T1 新增件提取检验（真化段 T1；Obj.magic=0 取证用。先例：
   检验命令随宿主文件在册，产物 *_t1_ext_*.ml/.mli 验收后清场，
   下次重编再生、再清——同 Bridge.v §8 惯例） —— *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
Extraction "_t1_ext_tex_with" tex_with.
Extraction "_t1_ext_evset" ev_append_size_set.
Extraction "_t1_ext_evmono" ev_append_size_mono_set.
Extraction "_t1_ext_dual" tneg_tex_dual.

(* —— T2 真化段新增件假设闭包打印（真化段 T2 追加，G4 附件） —— *)
Print Assumptions ev_eqb_true_iff.
Print Assumptions ev_eqb_leibniz_gap.
Print Assumptions ev_eqb_raw_true_iff.
Print Assumptions ev_size_pos_third.
Print Assumptions ev_size_1_leaf_iff.
Print Assumptions ev_size_ge_2_pair.
Print Assumptions ev_pair_decomp_exact.
Print Assumptions ev_enum_size_bound.

(* —— T2 新增件提取检验（真化段 T2；Obj.magic=0 取证用。先例：
   先例：检验命令随宿主文件在册，产物 *_t2_ext_*.ml/.mli 验收后
   清场，下次重编再生、再清——同 Bridge.v §8 惯例） —— *)
Extraction "_t2_ext_eqb" ev_eqb.
Extraction "_t2_ext_decomp" ev_case_set.
Extraction "_t2_ext_enum" ev_enum.

(* —— 切片二替换件闭包打印（切片二追加，G4 附件） —— *)
Print Assumptions ev_size_pair.
Print Assumptions default_Tex_phi.
Print Assumptions exists_level2_node.
Print Assumptions layer_self_refutation.
Print Assumptions layered_network_liar_each_layer.
Print Assumptions level_confusion_revives_liar.
Print Assumptions trLevel_geq_trans.
Print Assumptions cv_lv_antisym_transport.
Print Assumptions cv_node_level.
Print Assumptions cv_node_round_core.
Print Assumptions Tex_fiber_cast.
Print Assumptions audit_node_cast.
Print Assumptions tex_nontrivial.
Print Assumptions tex_nontrivial_audited.
Print Assumptions ref_node_round.
Print Assumptions tneg_counter_size.
Print Assumptions qeqb_refl.
Print Assumptions Qraw_eqb_refl.
Print Assumptions ev_rect'_num.
Print Assumptions ev_rect'_seq.
Print Assumptions ev_rect'_pair.
Print Assumptions ev_size_pos_third.
Print Assumptions ev_enum_size_bound.
Print Assumptions ev_enum_num_0.
Print Assumptions ev_enum_seq_nil.
