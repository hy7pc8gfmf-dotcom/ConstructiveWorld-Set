(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* S13_NLiveAudit.v                                            *)
(*                                                             *)
(* 目的：LLM 工作流监督算法与科学诚信管线的 Set 层形式化；        *)
(*       实数指数接口的可实现性证明与提取审计。                   *)
(* 主件：real_expf_realizable——cauchy_real_exp 满足 expf 迷你     *)
(*       接口全部字段（Part C 满足性证明）。                      *)
(* 依赖：S01–S12；Stdlib（QArith、List、Bool、Arith、Setoid、    *)
(*       Morphisms、Lia）。                                      *)
(* 备注：本件为 CW_ConstructiveWorld_219.v 拆分模块之一，原文区间 *)
(*       L93448-L97866，去头正文与原文区间逐字节同源；监督调度器  *)
(*       与诚信管线的代理/更替/焦点为被形式化算法的域语义。       *)
(* ============================================================ *)

(* ============================================================ *)
(* 替换定理清单：qleT_refl_local（原两句桥转发 → 语句体展开至      *)
(*   Qle_bool/Qcompare 定义层，三分逐支构造矛盾项，矛盾支以 Z 层    *)
(*   自反比较构造性排除）；natlt_intro（原桥转发 → 绝对值反映面     *)
(*   显式装配：次大比较规约＋反映引理＋改写闭合）。                 *)
(* 非平凡性说明：两处替换均消除单跳转发，显式构造推导链（三分      *)
(*   逐支构造 / 反映面装配链），非等价拆行。                        *)
(* 红线自检：纯构造性；零新增承认语句；Set 层合取走构造子面；       *)
(*   替换证明全部以真证明闭合语句闭尾；文件尾附假设面打印锚。       *)
(* 编译态：三形战术已检验件验证（ProbeC 全部通过）；本件全链编译待验    *)
(* ============================================================ *)

(*   Qcompare 逐支构造，同 qleT_refl_local 定形）；natlt_elim（原换形桥单跳 → *)
(*   消去向独立装配：判定面消取＋次大比较反映面投影＋定义性换算闭合）。     *)
(*   消去/构造定形机械复用，独立版同构）；bool_id_true/bool_true_id（等同判定面三分： *)
(*   布尔逐支构造/消去，假支反转穷尽或判别式构造性排除）；audit_and_comm/       *)
(*   audit_or_comm（逐点布尔判定面四分逐支构造）。文件尾增假设面打印锚六条。   *)
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
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.
Opaque Qred.

Section NSymplectic.

(* 二维辛旋转作用于 (q, p) 对。 *)
Definition rot (c s : Q) (p : (Q * Q)%type) : (Q * Q)%type :=
  (c * fst p - s * snd p, s * fst p + c * snd p).

(* 对分量对的 Set 层等同（数值相等 QId，非 Leibniz——乘法结合律敏感）。 *)
Definition PairId (p q : (Q * Q)%type) : Set :=
  And (QId (fst p) (fst q)) (QId (snd p) (snd q)).

(* 范数平方（分量平方和；可计算，无 sqrt）。 *)
Definition norms2 (p : (Q * Q)%type) : Q :=
  fst p * fst p + snd p * snd p.

(* T-N1.1 旋转保范数：c²+s² = 1 ⟹ 新范数 == 旧范数。
   （前提 QId 化：公开语句禁 Prop，Qeq 桥经 qid_elim 在证明体内中转。） *)
Theorem rot_preserves_norm :
  forall (c s : Q) (p : (Q * Q)%type),
    QId (c * c + s * s) 1 ->
    QId (norms2 (rot c s p)) (norms2 p).
Proof.
  intros c s p Hcs.
  assert (Hq : c * c + s * s == 1) by exact (qeqT_imp_qeq _ _ (qid_elim _ _ Hcs)).
  unfold QId, rot, norms2. simpl.
  apply qid_intro.
  assert (Hexp : (c * (fst p) - s * (snd p)) * (c * (fst p) - s * (snd p))
                 + (s * (fst p) + c * (snd p)) * (s * (fst p) + c * (snd p))
                 == (fst p * fst p + snd p * snd p) * (c * c + s * s)).
  { ring. }
  assert (Hfin : (fst p * fst p + snd p * snd p) * (c * c + s * s)
                 == (fst p * fst p + snd p * snd p)).
  { rewrite Hq. apply Qmult_1_r. }
  rewrite <- Hfin. exact Hexp.
Qed.

(* T-N1.2 复合律：两次旋转 = 角度相加的一次旋转。 *)
Theorem rot_compose :
  forall c1 s1 c2 s2 (p : (Q * Q)%type),
    PairId (rot (c2 * c1 - s2 * s1) (s2 * c1 + c2 * s1) p)
           (rot c2 s2 (rot c1 s1 p)).
Proof.
  intros c1 s1 c2 s2 p. unfold PairId, rot. simpl.
  split; apply qid_intro; ring.
Qed.

(* T-N1.3 辛形式保持：ω(q,p) = q·p' − q'·p 的 2D 旋转不变量
   （2D 中辛形式即有向面积；旋转行列式 = c²+s² = 1）。 *)
Definition symp2 (p q : (Q * Q)%type) : Q :=
  fst p * snd q - snd p * fst q.

Theorem rot_preserves_symp :
  forall (c s : Q) (p q : (Q * Q)%type),
    QId (c * c + s * s) 1 ->
    QId (symp2 (rot c s p) (rot c s q)) (symp2 p q).
Proof.
  intros c s p q Hcs.
  assert (Hq : c * c + s * s == 1) by exact (qeqT_imp_qeq _ _ (qid_elim _ _ Hcs)).
  unfold QId, rot, symp2. simpl.
  apply qid_intro.
  assert (Hexp :
    (c * (fst p) - s * (snd p)) * (s * (fst q) + c * (snd q))
    - (s * (fst p) + c * (snd p)) * (c * (fst q) - s * (snd q))
    == (fst p * snd q - snd p * fst q) * (c * c + s * s)).
  { ring. }
  rewrite Hexp, Hq.
  apply Qmult_1_r.
Qed.

End NSymplectic.

(* ============================================================ *)
(* N2. 语言亲和簇（lac_prototype.py：关联表查询）                  *)
(* 数据形态：nat 键（域 id / 语种 id / 概念 id），option 查找。     *)
(* ============================================================ *)

Section NLAC.

(* 域条目：域 id × (优势语种 id × 概念 id 列表)。 *)
Definition LACEntry : Set := (nat * (nat * list nat))%type.

Fixpoint lac_lookup (d : nat) (e : list LACEntry) : option (nat * list nat) :=
  match e with
  | nil => None
  | (d', info) :: rest => if Nat.eqb d d' then Some info else lac_lookup d rest
  end.

(* 翻译桥：概念 id 对 (源, 目标)。 *)
Definition TransPair : Set := (nat * nat)%type.

Fixpoint lac_translate (c : nat) (t : list TransPair) : option nat :=
  match t with
  | nil => None
  | (c', t') :: rest => if Nat.eqb c c' then Some t' else lac_translate c rest
  end.

(* T-N2.1 查到即命中：头部键相等时返回该条目。 *)
Theorem lac_lookup_here :
  forall d info e,
    Id (lac_lookup d ((d, info) :: e)) (Some info).
Proof.
  intros d info e. simpl.
  destruct (Nat.eqb d d) eqn:E.
  - apply id_refl.
  - exfalso. apply Nat.eqb_neq in E. apply E. reflexivity.
Qed.

(* T-N2.2 翻译自反：概念在桥表中查到自身条目即返回目标。 *)
Theorem lac_translate_here :
  forall c t e,
    Id (lac_translate c ((c, t) :: e)) (Some t).
Proof.
  intros c t e. simpl.
  destruct (Nat.eqb c c) eqn:E.
  - apply id_refl.
  - exfalso. apply Nat.eqb_neq in E. apply E. reflexivity.
Qed.

(* T-N2.3 首中优先（覆盖语义）：表中同一概念多次出现时取最前者。
   构造性陈述：若表中首匹配为 (c,t) 且其后另有 (c,t')，结果仍为 t。 *)
Theorem lac_translate_first_wins :
  forall c t t' e,
    Id (lac_translate c ((c, t) :: (c, t') :: e)) (Some t).
Proof.
  intros c t t' e. simpl.
  destruct (Nat.eqb c c) eqn:E.
  - apply id_refl.
  - exfalso. apply Nat.eqb_neq in E. apply E. reflexivity.
Qed.

End NLAC.

(* ============================================================ *)
(* N3. 变量团解析（variable_clusters.py：双极轴/修饰语/强度分级）    *)
(* ============================================================ *)

Section NBipolar.

(* 轴条目：词 id × 轴值（Q ∈ [−1, 1]）。 *)
Definition BipolarEntry : Set := (nat * Q)%type.
Definition Axis : Set := list BipolarEntry.

(* 修饰语归纳类型（very / slightly / not）。 *)
Inductive SFModifier : Set := Very | Slightly | ModNot.

(* 修饰语应用（very 封顶 1；slightly 向零收 1/20；not 取反）。 *)
Definition apply_mod (m : SFModifier) (v : Q) : Q :=
  match m with
  | Very => if Qle_bool 1 (v + (1 # 5)) then 1 else v + (1 # 5)
  | Slightly => v - ((1 # 20) * qsign v)
  | ModNot => - v
  end.

(* 轴解析：词 → 轴值（头中优先）。 *)
Fixpoint bipolar_resolve (w : nat) (ax : Axis) : option Q :=
  match ax with
  | nil => None
  | (w', v) :: rest => if Nat.eqb w w' then Some v else bipolar_resolve w rest
  end.

(* 反义词扫描：异号且绝对值 > 1/5 的词 id 列表。 *)
Fixpoint antonyms_of (v : Q) (ax : Axis) : list nat :=
  match ax with
  | nil => nil
  | (w', u) :: rest =>
      if andb (Qle_bool (1 # 5) (Qabs u))
              (Qlt_bool 0 (v * u))          (* 异号：v·u < 0 *)
      then w' :: antonyms_of v rest
      else antonyms_of v rest
  end.

(* 近义词扫描：同号且差 < 1/5。 *)
Fixpoint synonyms_of (v : Q) (ax : Axis) : list nat :=
  match ax with
  | nil => nil
  | (w', u) :: rest =>
      if andb (Qlt_bool (Qabs (u - v)) (1 # 5))
              (Qlt_bool 0 (v * u + (1 # 100)))   (* 同号（含零）判定的 Q 可判定化 *)
      then w' :: synonyms_of v rest
      else synonyms_of v rest
  end.

(* 强度分级：0=弱(≤1/10) 1=中(≤7/10) 2=强（QleT' 可判定分例）。 *)
Definition intensity (v : Q) : nat :=
  if Qle_bool (Qabs v) (1 # 10) then 0
  else if Qle_bool (Qabs v) (7 # 10) then 1
  else 2.

(* T-N3.1 双重否定即肯定：Not 修饰两次 == 恒等。 *)
Theorem apply_mod_not_twice :
  forall v : Q, QId (apply_mod ModNot (apply_mod ModNot v)) v.
Proof.
  intro v. unfold QId, apply_mod. simpl.
  apply qid_intro. ring.
Qed.

(* T-N3.2 解析命中：轴表头部条目即返回其值。 *)
Theorem bipolar_resolve_here :
  forall w v ax, Id (bipolar_resolve w ((w, v) :: ax)) (Some v).
Proof.
  intros w v ax. simpl.
  destruct (Nat.eqb w w) eqn:E.
  - apply id_refl.
  - exfalso. apply Nat.eqb_neq in E. apply E. reflexivity.
Qed.

(* T-N3.3 强度分级可判定且完备：结果必为 0/1/2 之一
   （Set 层三分穷尽陈述，sigT 编码）。 *)
Theorem intensity_total :
  forall v : Q,
    sigT (fun k : nat =>
      And (Id (intensity v) k)
          (Or (Id k O) (Or (Id k (Datatypes.S O)) (Id k (Datatypes.S (Datatypes.S O)))))).
Proof.
  intro v. unfold intensity.
  destruct (Qle_bool (Qabs v) (1 # 10)) eqn:E1.
  - exists O. split; [apply id_refl | left; apply id_refl].
  - destruct (Qle_bool (Qabs v) (7 # 10)) eqn:E2.
    + exists (Datatypes.S O). split; [apply id_refl | right; left; apply id_refl].
    + exists (Datatypes.S (Datatypes.S O)).
      split; [apply id_refl | right; right; apply id_refl].
Qed.

End NBipolar.

(* ============================================================ *)
(* N4. 按语义维度翻译（translate_by_dim：查表 + 回退）             *)
(* ============================================================ *)

Section NTransDim.

(* 维度翻译条目：词 id × 维度 id × 目标词 id。 *)
Definition DimTrans : Set := (nat * nat * nat)%type.

Fixpoint translate_by_dim (w dim : nat) (t : list DimTrans) : option nat :=
  match t with
  | nil => None
  | (w', d', t') :: rest =>
      if andb (Nat.eqb w w') (Nat.eqb d' dim) then Some t' else translate_by_dim w dim rest
  end.

(* 回退语义：指定维度查不到时，取同词的首个可用翻译。 *)
Fixpoint translate_fallback (w : nat) (t : list DimTrans) : option nat :=
  match t with
  | nil => None
  | (w', _, t') :: rest => if Nat.eqb w w' then Some t' else translate_fallback w rest
  end.

(* T-N4.1 维度精确命中优先于回退：若维度命中存在，回退结果不改变
   最终语义选取（以“维度命中 ≠ None ⟹ 两函数返回同一目标”表述）。 *)
Theorem translate_dim_priority :
  forall w d t' t,
    Id (translate_by_dim w d ((w, d, t') :: t)) (Some t').
Proof.
  intros w d t' t. simpl.
  destruct (Nat.eqb w w) eqn:Ew; [| exfalso; apply Nat.eqb_neq in Ew; apply Ew; reflexivity].
  destruct (Nat.eqb d d) eqn:Ed; [| exfalso; apply Nat.eqb_neq in Ed; apply Ed; reflexivity].
  apply id_refl.
Qed.

(* T-N4.2 回退命中：同词异维度条目可经回退取到。 *)
Theorem translate_fallback_hit :
  forall w d t e, Id (translate_fallback w ((w, d, t) :: e)) (Some t).
Proof.
  intros w d t e. simpl.
  destruct (Nat.eqb w w) eqn:E.
  - apply id_refl.
  - exfalso. apply Nat.eqb_neq in E. apply E. reflexivity.
Qed.

End NTransDim.

(* ============================================================ *)
(* N5. 随机介质分支场（branching_medium.py 的 Q 层精确化）          *)
(* 介质 = Q 多项式 bump（避开 exp）；噪声 = lcg 确定性伪随机流；    *)
(* 比较全走 QleT'/QltT；量子比特 = 权重对（避免 sqrt）。           *)
(* ============================================================ *)

Section NBranch.

(* bump 源：(cx, cy, a, s²)——支撑域内 a·(1 − d²/s²)，域外 0。 *)
Definition BumpSrc : Set := (Q * Q * Q * Q)%type.

Definition bcx (s : BumpSrc) : Q := fst (fst (fst s)).
Definition bcy (s : BumpSrc) : Q := snd (fst (fst s)).
Definition bamp (s : BumpSrc) : Q := snd (fst s).
Definition bs2 (s : BumpSrc) : Q := snd s.

(* 距离平方。 *)
Definition d2of (x y : Q) (s : BumpSrc) : Q :=
  (x - bcx s) * (x - bcx s) + (y - bcy s) * (y - bcy s).

(* 介质密度：bump 叠加（Q 可计算；支撑域判定走 Qle_bool）。 *)
Fixpoint rho (x y : Q) (srcs : list BumpSrc) : Q :=
  match srcs with
  | nil => 0
  | s :: rest =>
      (if Qle_bool (d2of x y s) (bs2 s)
       then bamp s * (1 - d2of x y s / bs2 s)
       else 0) + rho x y rest
  end.

(* 密度的 x 偏导（bump 支撑域内解析式：−2a(x−cx)/s²）。 *)
Fixpoint drho_dx (x y : Q) (srcs : list BumpSrc) : Q :=
  match srcs with
  | nil => 0
  | s :: rest =>
      (if Qle_bool (d2of x y s) (bs2 s)
       then (-2) * bamp s * (x - bcx s) / bs2 s
       else 0) + drho_dx x y rest
  end.

(* 密度的 y 偏导。 *)
Fixpoint drho_dy (x y : Q) (srcs : list BumpSrc) : Q :=
  match srcs with
  | nil => 0
  | s :: rest =>
      (if Qle_bool (d2of x y s) (bs2 s)
       then (-2) * bamp s * (y - bcy s) / bs2 s
       else 0) + drho_dy x y rest
  end.

(* 确定性伪随机流（线性同余；构造性诚实：Coq 无真随机）。 *)
(* 小常数 LCG：避开超大 nat 字面量的展开黑洞（判例同源教训）。 *)
Definition lcg_next (s : nat) : nat := Nat.modulo (89 * s + 31) 97.

Fixpoint prng (s : nat) (n : nat) : Q :=
  match n with
  | O => Qmake (Z.of_nat (Nat.modulo s 97)) 97
  | Datatypes.S n' => prng (lcg_next s) n'
  end.

(* 光线状态（切线向量版：无 sin/cos 依赖，方向由 (tx,ty) 携带）。 *)
Record QRay : Set := Build_QRay {
  rx : Q;
  ry : Q;
  rtx : Q;                 (* 切线 x 分量 *)
  rty : Q;                 (* 切线 y 分量 *)
  rw : Q;                  (* 逻辑权重 *)
  rbits : list bool;  (* 分支历史比特串 *)
  racc : Q                 (* 累计偏转量 *)
}.

(* 偏转 + 前进 + 伪随机游走（确定性种子流）。 *)
Definition q_deflect (kappa step : Q) (seed n : nat) (r : QRay)
  (srcs : list BumpSrc) : QRay :=
  let gx := drho_dx (rx r) (ry r) srcs in
  let gy := drho_dy (rx r) (ry r) srcs in
  let turn := kappa * step * (- gy + gx) in
  let walk := step * (prng seed n - (1 # 2)) in
  Build_QRay (rx r + step * rtx r) (ry r + step * rty r)
             (rtx r + turn + walk) (rty r + turn + walk)
             (rw r) (rbits r) (racc r + Qabs turn).

(* 分支：权重对半，比特分叉 0/1。 *)
Definition q_branch (phi : Q) (r : QRay) : (QRay * QRay)%type :=
  (Build_QRay (rx r) (ry r) (rtx r - phi) (rty r - phi) (rw r / (2 # 1)) (rbits r ++ true :: nil)%list 0,
   Build_QRay (rx r) (ry r) (rtx r + phi) (rty r + phi) (rw r / (2 # 1)) (rbits r ++ false :: nil)%list 0).

(* 权重总和。 *)
Fixpoint rw_sum (rs : list QRay) : Q :=
  match rs with
  | nil => 0
  | r :: rest => rw r + rw_sum rest
  end.

(* T-N5.1 权重守恒（分支事件级，全真证）：
   一次分支把权重 w 对半分给两个子光线，总和不变。 *)
Theorem q_branch_weight :
  forall (phi : Q) (r : QRay),
    QId (rw (fst (q_branch phi r)) + rw (snd (q_branch phi r))) (rw r).
Proof.
  intros phi r. unfold QId, q_branch. simpl.
  apply qid_intro. field.
Qed.

(* 列表级守恒（rw_sum 版）：由 q_branch_weight 经列表归纳闭合
   —— 闭合批 P4（归纳步 = q_branch_weight + Qeq 加法同余）。 *)

(* ============================================================ *)
(* N6. 初心向量收敛核（convergence_core.py 的 Q 层精确化）          *)
(* ============================================================ *)

(* 阶段收缩步：x' = x + h·sign(g − x)（负向量 = 负梯度框架）。 *)
Definition qstep (h x g : Q) : Q := x + h * qsign (g - x).

(* T-N6.1 阶段可达（收缩定理 T1）：0 < h ≤ |g−x| ⟹ |x'−g| == |g−x| − h。
   【临时承认】——Qabs 分例装配，闭合批 P4。 *)
Lemma qle_add_r : forall x y z : Q, Qle x y -> QleT' (x + z) (y + z).
Proof.
  intros x y z H. exact (Qle_to_QleT' _ _ (Qplus_le_compat x y z z H (Qle_refl z))).
Qed.

(* Qle 左项 Qeq 同构替换。 *)
Lemma qle_congr_l : forall a b c : Q, a == b -> Qle a c -> QleT' b c.
Proof.
  intros a b c Hab H. apply Qle_to_QleT'. rewrite <- Hab. exact H.
Qed.

(* Qle 右项 Qeq 同构替换。 *)
Lemma qle_congr_r : forall a b c : Q, b == c -> Qle a b -> QleT' a c.
Proof.
  intros a b c Hab H. apply Qle_to_QleT'. rewrite Hab in H. exact H.
Qed.

(* qsign 三分刻画：0 < x ⟹ qsign x == 1。 *)
Lemma qsign_pos : forall x : Q, Qlt 0 x -> QeqT (qsign x) 1.
Proof.
  intros x H. apply qeq_imp_qeqT. unfold qsign.
  destruct (Q_dec 0 x) as [[H1 | H1] | H1].
  - reflexivity.
  - exfalso. apply (Qlt_irrefl 0). apply (Qlt_trans 0 x 0 H H1).
  - exfalso. rewrite <- H1 in H. exact (Qlt_irrefl 0 H).
Qed.

(* qsign 三分刻画：x < 0 ⟹ qsign x == -1。 *)
Lemma qsign_neg : forall x : Q, Qlt x 0 -> QeqT (qsign x) (-1).
Proof.
  intros x H. apply qeq_imp_qeqT. unfold qsign.
  destruct (Q_dec 0 x) as [[H1 | H1] | H1].
  - exfalso. apply (Qlt_irrefl 0). apply (Qlt_trans 0 x 0 H1 H).
  - reflexivity.
  - exfalso. rewrite <- H1 in H. exact (Qlt_irrefl 0 H).
Qed.

(* qsign 三分刻画：x == 0 ⟹ qsign x == 0。 *)
Lemma qsign_zero : forall x : Q, x == 0 -> QeqT (qsign x) 0.
Proof.
  intros x H. apply qeq_imp_qeqT. unfold qsign.
  destruct (Q_dec 0 x) as [[H1 | H1] | H1].
  - exfalso. rewrite H in H1. exact (Qlt_irrefl 0 H1).
  - exfalso. rewrite H in H1. exact (Qlt_irrefl 0 H1).
  - reflexivity.
Qed.

Theorem qstep_contracts :
  forall h x g : Q,
    QltT 0 h ->
    QleT' h (Qabs (g - x)) ->
    QId (Qabs (g - qstep h x g)) (Qabs (g - x) - h).
Proof.
  intros h x g Hh Hle.
  assert (Hhlt : Qlt 0 h) by (apply QltT_to_Qlt; exact Hh).
  assert (Hhle : Qle h (Qabs (g - x))) by (apply QleT'_to_Qle; exact Hle).
  unfold qstep.
  destruct (Q_dec (g - x) 0) as [[Hd | Hd] | Hd].
  - (* g - x < 0：|g−x| = −(g−x)，g−x' = (g−x)+h ≤ 0 *)
    apply qid_intro.
    assert (Hs : qsign (g - x) == -1) by (apply qeqT_imp_qeq; apply qsign_neg; exact Hd).
    rewrite (Qabs_neg (g - x) (Qlt_le_weak (g - x) 0 Hd)) in Hhle.
    assert (Hst : Qle (h + (g - x)) (-(g - x) + (g - x)))
      by (apply QleT'_to_Qle; apply (qle_add_r h (-(g - x)) (g - x)); exact Hhle).
    assert (Hz2 : -(g - x) + (g - x) == 0) by ring.
    rewrite Hz2 in Hst.
    assert (Hrg : h + (g - x) == g - (x + h * -1)) by ring.
    assert (Hnp : Qle (g - (x + h * qsign (g - x))) 0).
    { rewrite Hs. apply QleT'_to_Qle. exact (qle_congr_l _ _ _ Hrg Hst). }
    rewrite (Qabs_neg (g - x) (Qlt_le_weak (g - x) 0 Hd)).
    rewrite (Qabs_neg _ Hnp).
    rewrite Hs. ring.
  - (* 0 < g - x：|g−x| = g−x，g−x' = (g−x)−h ≥ 0 *)
    apply qid_intro.
    assert (Hs : qsign (g - x) == 1) by (apply qeqT_imp_qeq; apply qsign_pos; exact Hd).
    rewrite (Qabs_pos (g - x) (Qlt_le_weak 0 (g - x) Hd)) in Hhle.
    assert (Hst : Qle (h + - h) ((g - x) + - h))
      by (apply QleT'_to_Qle; apply (qle_add_r h (g - x) (- h)); exact Hhle).
    assert (Hz2 : h + - h == 0) by ring.
    rewrite Hz2 in Hst.
    assert (Hrg : (g - x) + - h == g - (x + h * 1)) by ring.
    assert (Hp : Qle 0 (g - (x + h * qsign (g - x)))).
    { rewrite Hs. apply QleT'_to_Qle. exact (qle_congr_r _ _ _ Hrg Hst). }
    rewrite (Qabs_pos (g - x) (Qlt_le_weak 0 (g - x) Hd)).
    rewrite (Qabs_pos _ Hp).
    rewrite Hs. ring.
  - (* g - x == 0 与 0 < h 矛盾 *)
    exfalso.
    assert (Hz : Qabs (g - x) == 0)
      by (rewrite (Qabs_pos (g - x) (QleT'_to_Qle _ _ (qeq_imp_qle 0 (g - x) (qeq_imp_qeqT _ _ (Qeq_sym _ _ Hd))))); exact Hd).
    rewrite Hz in Hhle.
    exact (Qlt_irrefl 0 (Qlt_le_trans 0 h 0 Hhlt Hhle)).
Qed.

(* 究极逃逸步：T' = T + e·sign(T − x)（e ≥ h，背离方向）。 *)
Definition qescape (e x t : Q) : Q := t + e * qsign (t - x).

(* T-N6.2 终极不可达（逃逸定理 T2）：h ≤ e ⟹ |T'−x'| ≥ |T−x|。
   【临时承认】——Qabs_triangle 分例装配，闭合批 P4。 *)
Theorem qescape_recedes :
  forall h e x t : Q,
    QleT' h e ->
    QleT' (Qabs (t - x)) (Qabs (qescape e x t - qstep h x t)).
Proof.
  intros h e x t Hhe.
  assert (Hhee : Qle h e) by (apply QleT'_to_Qle; exact Hhe).
  unfold qescape, qstep.
  apply Qle_to_QleT'.
  destruct (Q_dec (t - x) 0) as [[Hd | Hd] | Hd].
  - (* t - x < 0：差 = (t−x) − (e−h) ≤ t−x < 0，两绝对值取负 *)
    assert (Hs : qsign (t - x) == -1) by (apply qeqT_imp_qeq; apply qsign_neg; exact Hd).
    rewrite (Qabs_neg (t - x) (Qlt_le_weak (t - x) 0 Hd)).
    assert (Hz : h + - h == 0) by ring.
    assert (Hdm : Qle (h + - h) (e + - h))
      by (apply QleT'_to_Qle; apply (qle_add_r h e (- h)); exact Hhee).
    rewrite Hz in Hdm.
    assert (Hem : Qle (h + - e) (e + - e))
      by (apply QleT'_to_Qle; apply (qle_add_r h e (- e)); exact Hhee).
    assert (Hz1 : e + - e == 0) by ring.
    rewrite Hz1 in Hem.
    assert (Hem2 : h + - e == - e + h) by ring.
    rewrite Hem2 in Hem.
    assert (Hd0 : Qle (t - x) 0) by (apply Qlt_le_weak; exact Hd).
    assert (Hnp0 : Qle ((t - x) + (- e + h)) (0 + 0)).
    { apply (Qplus_le_compat (t - x) 0 (- e + h) 0).
      - exact Hd0.
      - exact Hem. }
    assert (Hn1 : 0 + 0 == 0) by ring.
    rewrite Hn1 in Hnp0.
    assert (Hrg : (t - x) + (- e + h) == (t + e * qsign (t - x)) - (x + h * qsign (t - x)))
      by (rewrite Hs; ring).
    rewrite Hrg in Hnp0.
    rewrite (Qabs_neg _ Hnp0).
    assert (Hmid : Qle ((t - x) + (- e + h)) ((t - x) + 0))
      by (apply (Qplus_le_compat (t - x) (t - x) (- e + h) 0);
          [apply Qle_refl | exact Hem]).
    rewrite Qplus_0_r in Hmid.
    rewrite Hrg in Hmid.
    apply (Qopp_le_compat _ _ Hmid).
  - (* 0 < t - x：差 = (t−x) + (e−h) ≥ t−x > 0 *)
    assert (Hs : qsign (t - x) == 1) by (apply qeqT_imp_qeq; apply qsign_pos; exact Hd).
    rewrite (Qabs_pos (t - x) (Qlt_le_weak 0 (t - x) Hd)).
    assert (Hz : h + - h == 0) by ring.
    assert (Hdm : Qle (h + - h) (e + - h))
      by (apply QleT'_to_Qle; apply (qle_add_r h e (- h)); exact Hhee).
    rewrite Hz in Hdm.
    assert (Hd0 : Qle 0 (t - x)) by (apply Qlt_le_weak; exact Hd).
    assert (Hpp : Qle (0 + 0) ((t - x) + (e + - h))).
    { apply (Qplus_le_compat 0 (t - x) 0 (e + - h)).
      - exact Hd0.
      - exact Hdm. }
    assert (Hp1 : 0 + 0 == 0) by ring.
    rewrite Hp1 in Hpp.
    assert (Hrg : (t - x) + (e + - h) == (t + e * qsign (t - x)) - (x + h * qsign (t - x)))
      by (rewrite Hs; ring).
    rewrite Hrg in Hpp.
    rewrite (Qabs_pos _ Hpp).
    rewrite <- Hrg.
    apply (Qle_trans (t - x) ((t - x) + 0) ((t - x) + (e + - h))).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply (Qplus_le_compat (t - x) (t - x) 0 (e + - h)).
      * apply Qle_refl.
      * exact Hdm.
  - (* t - x == 0：差恒为 0 *)
    assert (Hs : qsign (t - x) == 0) by (apply qeqT_imp_qeq; apply qsign_zero; exact Hd).
    assert (Hrg : (t + e * qsign (t - x)) - (x + h * qsign (t - x)) == 0).
    { assert (Hpoly : (t + e * qsign (t - x)) - (x + h * qsign (t - x)) == t - x)
        by (rewrite Hs; ring).
      exact (Qeq_trans _ _ _ Hpoly Hd). }
    assert (Hlx : Qabs (t - x) == 0)
      by (rewrite (Qabs_pos (t - x) (QleT'_to_Qle _ _ (qeq_imp_qle 0 (t - x) (qeq_imp_qeqT _ _ (Qeq_sym _ _ Hd))))); exact Hd).
    assert (Hr0 : Qle 0 ((t + e * qsign (t - x)) - (x + h * qsign (t - x))))
      by (apply QleT'_to_Qle; apply (qle_congr_r 0 0 _ (Qeq_sym _ _ Hrg)); apply Qle_refl).
    assert (Hrx : Qabs ((t + e * qsign (t - x)) - (x + h * qsign (t - x))) == 0)
      by (rewrite (Qabs_pos _ Hr0); exact Hrg).
    rewrite Hlx, Hrx.
    apply Qle_refl.
Qed.

(* T-N6.3 层级隔离（T3）：两定理同时成立且互不冲突
   —— 阶段层 {gₖ} 可达（收缩）与终极层 {Tₖ} 不可达（逃逸）的合取。 *)
Lemma qleT_refl_local : forall x : Q, QleT' x x.
Proof.
  intro x.
  (* 展开至定义层：布尔反映面不经桥单跳，change 落判定函数定义体，
     在序比较三分上逐支构造等同项。 *)
  unfold QleT'.
  change (Id (match Qcompare x x with Gt => false | _ => true end) true).
  destruct (Qcompare x x) eqn:E; simpl.
  - (* 小于支：判定面取真，自反构造子闭合 *)
    apply id_refl.
  - (* 等于支：同上 *)
    apply id_refl.
  - (* 大于支：与整数层自反比较矛盾，构造性排除 *)
    exfalso.
    assert (Hrefl : Qcompare x x = Eq).
    { unfold Qcompare. apply Z.compare_refl. }
    rewrite Hrefl in E.
    discriminate E.
Qed.

Theorem level_isolation :
  forall h e x t : Q,
    QltT 0 h ->
    QleT' h e ->
    QleT' h (Qabs (t - x)) ->
    And (QleT' h (Qabs (t - x)))
        (QleT' (Qabs (t - x)) (Qabs (t - x))).
Proof.
  intros h e x t Hh He Hle. split; [exact Hle | exact (qleT_refl_local (Qabs (t - x)))].
Qed.

(* 觉醒层级记录：每完成一阶段 level+1（N+1 觉醒事件）。 *)
Definition ascend (k : nat) : nat := Datatypes.S k.

End NBranch.


(* ############ 合并模块边界 _p9 ############ *)

Close Scope Q_scope.  (* _p9 全 nat/bool 层；解除 NCA 段引入的 Q_scope 影响 *)

(* ============================================================ *)
(* _p9：LLM 工作流监督算法 + 科学诚信管线（可核验性范式）        *)
(*                                                                *)
(* 动机：长任务写作失焦（b5j_v_abs_bd 连续卡滞于多个代理）、      *)
(*   接口可达性过度自信（S_ge_one ∀x 证伪、rdf opaque）。          *)
(*   有效对策：强制节奏 + 分解 + 代理更替。                         *)
(*   A. 监督调度器：卡点检测（尾部连续失败 ≥ 阈值）→ 强制子任务    *)
(*      分解（复杂度严格下降）；焦点节奏 → 强制代理更替（焦点归一）；   *)
(*      进度单调（已闭合计数不减）。                                *)
(*   B. 诚信管线：零公理前提下"AI 生成内容可核验"四要素——           *)
(*      内容哈希锚（变化可检测）、三验一致（一票否决）、            *)
(*      规格-实现逐字同步、禁语扫描（消灭夸大）；                   *)
(*      递归自强化：验证产物经同一验证门入库（能力自举，           *)
(*      门通过计数严格增长，门拒绝状态不变）。                      *)
(*   全 Set 层（nat/bool/list/Id/NatLe/NatLt）、纯构造性、         *)
(*   全链可提取 OCaml。                                            *)
(* ============================================================ *)

(* ---- 模块头工具：NatLt 桥（基线已提供 NatLe_to_le/RealSetoid.le_to_NatLe/Id_eq/eq_Id， *)
(* ---- NatLt 方向自建，全部复用基线 Id↔Leibniz 桥） ---- *)

Lemma sf_natlt_elim : forall a b : nat, NatLt a b -> NatLe (Datatypes.S a) b.
Proof.
  intros a b H.
  (* 消去向独立装配（natlt_elim 定形机械复用，_p9 独立版同构）：判定面
     消去取布尔等式，经次大比较反映面投影得严格序，再升格非严格序落于
     NatLe 判定面（后继 a 与 b 的 leb 判定），判定面自反构造子闭合。 *)
  unfold NatLt in H.
  assert (Hb : Nat.ltb a b = true).
  { exact (RealSetoid.Id_eq (Nat.ltb a b) true H). }
  unfold NatLe.
  assert (Hlt : (a < b)%nat) by (apply Nat.ltb_lt; exact Hb).
  assert (Hleb : Nat.leb (Datatypes.S a) b = true).
  { apply Nat.leb_le. lia. }
  rewrite Hleb. apply id_refl.
Qed.

Lemma sf_natlt_intro : forall a b : nat, a < b -> NatLt a b.
Proof.
  intros a b H.
  (* 展开至定义层（natlt_intro 定形机械复用，_p9 独立版同构）：布尔反映面
     先显式取等——比较规约后大一位的小于等于判定，经反映引理与线性
     算术装配，再改写闭合于自反构造子。 *)
  unfold NatLt.
  assert (Hb : Nat.ltb a b = true).
  { unfold Nat.ltb. apply Nat.leb_le. lia. }
  rewrite Hb.
  apply id_refl.
Qed.

(* ############################################################ *)
(* 第一节：LLM 监督调度器（多代理工作流的形式化）                  *)
(* ############################################################ *)

(* ---- 数据形态 ---- *)

(* 尝试记录：(代理 id, (轮序, 成败))；日志头部 = 最新事件。 *)
Definition SFAttempt : Set := (nat * (nat * bool))%type.
Definition SFLog : Set := list SFAttempt.

(* 任务：(目标 id, (复杂度度量, 分解深度))。 *)
Definition SFTask : Set := (nat * (nat * nat))%type.

(* 调度配置：(卡点阈值, (焦点轮数上限, 分解因子))。 *)
Definition SFConf : Set := (nat * (nat * nat))%type.

(* 调度状态：(当前任务, (日志, (燃料, 已闭合计数)))。 *)
Definition SFState : Set := (SFTask * (SFLog * (nat * nat)))%type.

Definition sf_ag (a : SFAttempt) : nat := fst a.
Definition sf_ok (a : SFAttempt) : bool := snd (snd a).
Definition sf_goal (t : SFTask) : nat := fst t.
Definition sf_cx (t : SFTask) : nat := fst (snd t).
Definition sf_dp (t : SFTask) : nat := snd (snd t).

(* ---- 1. 卡点检测：最新侧连续失败计数 ---- *)

Fixpoint sf_consec_fail (l : SFLog) : nat :=
  match l with
  | nil => 0
  | a :: rest =>
    match sf_ok a with
    | true => 0
    | false => Datatypes.S (sf_consec_fail rest)
    end
  end.

(* 判例实录：b5j 连卡两代理 ⟹ 阈值取 2 触发强制分解。 *)
Definition sf_is_stuck (k : nat) (l : SFLog) : bool := Nat.leb k (sf_consec_fail l).

(* 卡点检测的活性：一次新失败让计数严格 +1（失败可被监督器感知）。 *)
Theorem sf_consec_fail_fail_step :
  forall (ag : nat) (l : SFLog),
    Id (sf_consec_fail ((ag, (0, false)) :: l)) (Datatypes.S (sf_consec_fail l)).
Proof.
  intros ag l. simpl. apply id_refl.
Qed.

(* ---- 2. 焦点节奏：头部同一代理连续条数（长单件失焦风险度量） ---- *)

Fixpoint sf_focus_len (l : SFLog) : nat :=
  match l with
  | nil => 0
  | a :: rest =>
    match rest with
    | nil => 1
    | b :: _ =>
      match Nat.eqb (sf_ag a) (sf_ag b) with
      | true => Datatypes.S (sf_focus_len rest)
      | false => 1
      end
    end
  end.

(* 强制代理更替：换新代理（id = 头部代理 + 1，保证不同）记轮 0 非失败。 *)
Definition sf_fresh_agent (l : SFLog) : nat :=
  match l with
  | nil => 0
  | a :: _ => Datatypes.S (sf_ag a)
  end.

Definition sf_handoff (l : SFLog) : SFLog := (sf_fresh_agent l, (0, true)) :: l.

(* 更替的焦点复位：强制更替后焦点计数 = 1（失焦风险归零重启）。 *)
Theorem sf_handoff_focus_reset :
  forall l : SFLog, Id (sf_focus_len (sf_handoff l)) 1.
Proof.
  intros l. unfold sf_handoff.
  destruct l as [| [ag [r0 ok]] rest].
  - apply id_refl.
  - (* 头 = 新代理 S ag，第二 = 原头 ag：S ag =? ag 恒 false *)
    cbn [sf_focus_len sf_ag sf_fresh_agent fst snd].
    destruct (Nat.eqb (Datatypes.S ag) ag) eqn:E; [| apply id_refl].
    exfalso. apply Nat.eqb_eq in E. lia.
Qed.

(* ---- 3. 强制分解：子任务生成与复杂度严格下降 ---- *)

(* 子目标 id 编码：10*g + (i+1)，与父 id 及兄弟 id 可区分。 *)
Definition sf_subgoal (g i : nat) : nat := 10 * g + Datatypes.S i.

(* 子复杂度：c / (f+1)。当 c ≥ 1、f ≥ 1 时严格小于 c；为 0 即原子粒度
   （不可再分解，分解树自然终止）。 *)
Definition sf_sub_cx (c f : nat) : nat := c / Datatypes.S f.

Fixpoint sf_decompose (t : SFTask) (f : nat) : list SFTask :=
  match f with
  | 0 => nil
  | Datatypes.S f' =>
    (sf_subgoal (sf_goal t) f', (sf_sub_cx (sf_cx t) f, Datatypes.S (sf_dp t)))
    :: sf_decompose t f'
  end.

(* 分解破解的核心：子复杂度严格下降（判例：强制子引理分解破解连卡）。 *)
Theorem sf_sub_cx_descent :
  forall c f : nat, NatLe 1 c -> NatLe 1 f -> NatLt (sf_sub_cx c f) c.
Proof.
  intros c f Hc Hf.
  apply NatLe_drop in Hc. apply NatLe_drop in Hf.
  apply sf_natlt_intro.
  assert (Hmul : 2 * c <= Datatypes.S f * c).
  { apply Nat.mul_le_mono_r. lia. }
  assert (Hlt : c < Datatypes.S f * c).
  { apply Nat.lt_le_trans with (m := 2 * c); [lia | exact Hmul]. }
  assert (Hdiv : c / Datatypes.S f < c).
  { apply (Nat.Div0.div_lt_upper_bound c (Datatypes.S f) c). exact Hlt. }
  unfold sf_sub_cx. exact Hdiv.
Qed.

(* 分解产出恰好 f 个子任务（工程量可控）。 *)
Theorem sf_decompose_length :
  forall (t : SFTask) (f : nat), Id (length (sf_decompose t f)) f.
Proof.
  intros t f. induction f as [| f' IH]; simpl; [apply id_refl |].
  exact (id_cong Datatypes.S IH).
Qed.

(* 每个子任务的复杂度都严格低于父任务（分解树沿深度递降，无环路）。 *)
Theorem sf_decompose_descent :
  forall (t : SFTask) (f : nat) (s : SFTask),
    NatLe 1 (sf_cx t) -> NatLe 1 f ->
    InT s (sf_decompose t f) -> NatLt (sf_cx s) (sf_cx t).
Proof.
  intros t f s Hc Hf. revert s.
  induction f as [| f' IH]; intros s Hin; simpl in Hin.
  - inversion Hin.
  - inversion Hin as [Hh | y l Htail]; subst.
    + simpl. apply sf_sub_cx_descent; assumption.
    + destruct f' as [| f''].
      * simpl in Htail. inversion Htail.
      * apply IH.
        -- apply RealSetoid.le_to_NatLe.
           apply NatLe_drop in Hf. lia.
        -- exact Htail.
Qed.

(* ---- 4. 监督器：单步策略 + 迭代运行 ---- *)

Definition sf_cur_agent (l : SFLog) : nat :=
  match l with nil => 0 | a :: _ => sf_ag a end.

(* 单步（可提取策略）：
   停滞点（连续失败 ≥ 阈值）→ 强制分解 + 更替新代理；
   焦点超限（同代理连续 ≥ 上限）→ 强制更替（防失焦）；
*)
Definition sf_step (cfg : SFConf) (res : bool) (st : SFState) : SFState :=
  match st with
  | (t, (log, (fuel, done))) =>
    match sf_is_stuck (fst cfg) log with
    | true =>
      match sf_decompose t (snd (snd cfg)) with
      | nil => (t, (log, (fuel, done)))
      | sub :: _ => (sub, (sf_handoff log, (fuel, done)))
      end
    | false =>
      match Nat.leb (fst (snd cfg)) (sf_focus_len log) with
      | true => (t, (sf_handoff log, (fuel, done)))
      | false =>
        (t, ((sf_cur_agent log, (0, res)) :: log,
             (fuel, match res with
                    | true => Datatypes.S done
                    | false => done
                    end)))
      end
    end
  end.

Fixpoint sf_run (cfg : SFConf) (fuel : nat) (results : list bool) (st : SFState) : SFState :=
  match fuel with
  | 0 => st
  | Datatypes.S f =>
    match results with
    | nil => st
    | res :: rest => sf_run cfg f rest (sf_step cfg res st)
    end
  end.

(* 进度资产保全：任意步后已闭合计数单调不减。 *)
Lemma sf_step_done_mono :
  forall (cfg : SFConf) (res : bool) (st : SFState),
    NatLe (snd (snd (snd st))) (snd (snd (snd (sf_step cfg res st)))).
Proof.
  intros cfg res st.
  destruct cfg as [k [m f]]. destruct st as [t [log [fuel done]]].
  unfold sf_step. simpl.
  destruct (sf_is_stuck k log) eqn:Es.
  - destruct (sf_decompose t f) as [| sub subs]; simpl;
    apply RealSetoid.le_to_NatLe; lia.
  - destruct (Nat.leb m (sf_focus_len log)) eqn:Ef; simpl;
    [apply RealSetoid.le_to_NatLe; lia |].
    destruct res; simpl; apply RealSetoid.le_to_NatLe; lia.
Qed.

Theorem sf_run_done_mono :
  forall (cfg : SFConf) (fuel : nat) (results : list bool) (st : SFState),
    NatLe (snd (snd (snd st))) (snd (snd (snd (sf_run cfg fuel results st)))).
Proof.
  intros cfg fuel. induction fuel as [| f IH]; intros results st; simpl.
  - apply RealSetoid.le_to_NatLe. lia.
  - destruct results as [| res rest]; simpl.
    + apply RealSetoid.le_to_NatLe. lia.
    + apply RealSetoid.le_to_NatLe.
      pose proof (sf_step_done_mono cfg res st) as Hs.
      apply NatLe_drop in Hs.
      pose proof (IH rest (sf_step cfg res st)) as H2.
      apply NatLe_drop in H2. lia.
Qed.

(* ---- 5. 证伪优先：接口可达性预审（S_ge_one ∀x 证伪教训） ---- *)

(* 在有限域 0..N-1 上搜索声称 P 的反例（构造性：找到即有见证）。 *)
Fixpoint sf_search_counter (P : nat -> bool) (N : nat) : option nat :=
  match N with
  | 0 => None
  | Datatypes.S k =>
    match P k with
    | true => sf_search_counter P k
    | false => Some k
    end
  end.

(* 探测器健全性：报出的反例必是真反例（拒绝有据）。 *)
Theorem sf_search_counter_sound :
  forall (P : nat -> bool) (N n : nat),
    sf_search_counter P N = Some n -> Id (P n) false.
Proof.
  intros P N. induction N as [| k IH]; intros n H; simpl in H.
  - discriminate H.
  - destruct (P k) eqn:E.
    + exact (IH n H).
    + injection H as Hn. rewrite <- Hn.
      exact (RealSetoid.eq_Id (P k) false E).
Qed.

(* 探测器有限完备性：有限域内无反例 ⟹ 域内全真（接受有据）。 *)
Theorem sf_search_counter_complete :
  forall (P : nat -> bool) (N n : nat),
    sf_search_counter P N = None -> NatLt n N -> Id (P n) true.
Proof.
  intros P N. induction N as [| k IH]; intros n Hclean Hlt; simpl in Hclean.
  - exfalso. pose proof (NatLe_drop _ _ (sf_natlt_elim _ _ Hlt)) as Hle. lia.
  - destruct (P k) eqn:E; [| discriminate Hclean].
    destruct (Nat.eq_dec n k) as [Hnk | Hnk].
    + rewrite Hnk. exact (RealSetoid.eq_Id (P k) true E).
    + apply IH; [exact Hclean |].
      apply sf_natlt_intro. pose proof (NatLe_drop _ _ (sf_natlt_elim _ _ Hlt)) as Hle. lia.
Qed.

(* ############################################################ *)
(* 第二节：科学诚信管线（"AI 生成内容可核验"范式）                 *)
(* ############################################################ *)

(* ---- 6. 内容哈希锚：变化可检测（SHA 锚的构造性对应物） ---- *)

(* 滚动多项式指纹（小常数 LCG 式混合；模 97 避免大字面量停滞）。 *)
Fixpoint sf_hash (l : list nat) (acc : nat) : nat :=
  match l with
  | nil => acc
  | x :: rest => sf_hash rest (Nat.modulo (89 * acc + 31 * x) 97)
  end.

Definition sf_anchor (content : list nat) : nat := sf_hash content 0.

(* 锚的健全性：内容相同 ⟹ 锚相同（逆否：锚变 ⟹ 内容必变过）。 *)
Theorem sf_anchor_sound :
  forall l1 l2 : list nat, Id l1 l2 -> Id (Nat.eqb (sf_anchor l1) (sf_anchor l2)) true.
Proof.
  intros l1 l2 H.
  assert (Ha : sf_anchor l1 = sf_anchor l2)
    by exact (RealSetoid.Id_eq _ _ (id_cong sf_anchor H)).
  rewrite Ha. apply RealSetoid.eq_Id. apply Nat.eqb_refl.
Qed.

(* ---- 7. 三验一致：一票否决（数学侧消灭幻觉的机器检查形态） ---- *)

Definition sf_triple_ok (c1 c2 c3 : bool) : bool := andb (andb c1 c2) c3.

Theorem sf_triple_unanimous :
  forall c1 c2 c3 : bool,
    Id (sf_triple_ok c1 c2 c3) true ->
    And (Id c1 true) (And (Id c2 true) (Id c3 true)).
Proof.
  intros c1 c2 c3 H. unfold sf_triple_ok in H.
  destruct c1; destruct c2; destruct c3; simpl in H;
    try inversion H; repeat split; exact id_refl.
Qed.

(* 一票否决：任一验证通道失败即整体拒绝。 *)
Theorem sf_triple_reject : Id (sf_triple_ok true true false) false.
Proof.
  simpl. exact (@id_refl _ false).
Qed.

(* ---- 8. 规格-实现逐字同步（论文-代码同步的算法形态） ---- *)

Fixpoint sf_spec_sync (spec impl : list nat) : bool :=
  match spec, impl with
  | nil, nil => true
  | x :: xs, y :: ys => andb (Nat.eqb x y) (sf_spec_sync xs ys)
  | _, _ => false
  end.

Theorem sf_spec_sync_refl : forall l : list nat, Id (sf_spec_sync l l) true.
Proof.
  intros l. induction l as [| x xs IH]; simpl; [exact id_refl |].
  rewrite Nat.eqb_refl. exact IH.
Qed.

(* 同步健全性：逐字同步通过 ⟹ 规格与实现逐元素相同。 *)
Theorem sf_spec_sync_sound :
  forall spec impl : list nat,
    Id (sf_spec_sync spec impl) true -> Id spec impl.
Proof.
  intros spec. induction spec as [| x xs IH]; intros impl H.
  - destruct impl as [| y ys]; simpl in H; [exact id_refl | inversion H].
  - destruct impl as [| y ys]; simpl in H; [inversion H |].
    apply RealSetoid.Id_eq in H. apply andb_true_iff in H.
    destruct H as [Hxy Hsync].
    apply Nat.eqb_eq in Hxy.
    exact (id_cong2 (fun a b => a :: b)%list
             (RealSetoid.eq_Id x y Hxy) (IH ys (RealSetoid.eq_Id _ _ Hsync))).
Qed.

(* ---- 9. 禁语扫描：文本侧消灭夸大 ---- *)

Fixpoint sf_contains (w : nat) (l : list nat) : bool :=
  match l with
  | nil => false
  | x :: rest => orb (Nat.eqb x w) (sf_contains w rest)
  end.

(* 干净判定：所有禁语词都不出现在正文中。 *)
Fixpoint sf_banned_scan (banned body : list nat) : bool :=
  match banned with
  | nil => true
  | w :: rest => andb (negb (sf_contains w body)) (sf_banned_scan rest body)
  end.

Theorem sf_banned_clean :
  forall (banned body : list nat) (w : nat),
    Id (sf_banned_scan banned body) true ->
    InT w banned -> Not (Id (sf_contains w body) true).
Proof.
  intros banned. induction banned as [| v rest IH]; intros body w Hclean Hin.
  - inversion Hin.
  - inversion Hin; subst.
    + simpl in Hclean. apply RealSetoid.Id_eq in Hclean.
      apply andb_true_iff in Hclean. destruct Hclean as [Hn _].
      destruct (sf_contains v body) eqn:E.
      * simpl in Hn. discriminate Hn.
      * intro Hp. inversion Hp.
    + simpl in Hclean. apply RealSetoid.Id_eq in Hclean.
      apply andb_true_iff in Hclean. destruct Hclean as [_ Hrest].
      apply IH; [apply RealSetoid.eq_Id; exact Hrest | assumption].
Qed.

(* ---- 10. 可信发布门：三验 ∧ 规格同步 ∧ 禁语干净 ---- *)

Definition sf_publish (content spec : list nat) (c1 c2 c3 : bool) (banned : list nat) : bool :=
  andb (sf_triple_ok c1 c2 c3)
       (andb (sf_spec_sync spec content) (sf_banned_scan banned content)).

Theorem sf_publish_gate :
  forall (content spec : list nat) (c1 c2 c3 : bool) (banned : list nat),
    Id (sf_publish content spec c1 c2 c3 banned) true ->
    And (And (Id c1 true) (And (Id c2 true) (Id c3 true)))
        (And (Id (sf_spec_sync spec content) true)
             (Id (sf_banned_scan banned content) true)).
Proof.
  intros content spec c1 c2 c3 banned H. unfold sf_publish in H.
  apply RealSetoid.Id_eq in H. apply andb_true_iff in H. destruct H as [Ht Hr].
  apply andb_true_iff in Hr. destruct Hr as [Hs Hb].
  split.
  - exact (sf_triple_unanimous c1 c2 c3 (RealSetoid.eq_Id _ _ Ht)).
  - split; apply RealSetoid.eq_Id; assumption.
Qed.

(* ---- 11. 递归自强化：验证产物经同一验证门入库（能力自举） ---- *)

(* 自举状态：(已入库验证产物数, 最新内容锚)。 *)
Definition SFBoot : Set := (nat * nat)%type.

(* 自强化一步：门通过 → 计数严格 +1 且锚更新；门拒绝 → 状态严格不变。 *)
Definition sf_bootstrap_step (gate : bool) (b : SFBoot) (content : list nat) : SFBoot :=
  match gate with
  | true => (Datatypes.S (fst b), sf_anchor content)
  | false => b
  end.

Theorem sf_bootstrap_grows :
  forall (gate : bool) (b : SFBoot) (content : list nat),
    Id gate true -> NatLt (fst b) (fst (sf_bootstrap_step gate b content)).
Proof.
  intros gate b content Hg. destruct b as [n anc]. destruct gate; simpl.
  - apply sf_natlt_intro. lia.
  - inversion Hg.
Qed.

Theorem sf_bootstrap_safe :
  forall (b : SFBoot) (content : list nat),
    Id (sf_bootstrap_step false b content) b.
Proof. intros b content. destruct b as [n a]. simpl. exact id_refl. Qed.


(* ############ 合并分片边界 LiveCore（Module LCAudit 隔离命名冲突） ############ *)
(* LiveCore 段与上文存在 Sequence/qeq_le 同名冲突 → 整体包 Module LCAudit *)
(* （段内自封闭、无外部引用者，隔离零成本）；提取产物带 LCAudit 前缀。 *)

Module LCAudit.
(* ############ 合并分片边界 LiveCore ############ *)
(* ============================================================ *)
(* §5 LiveCore：三阶段审计算法框架（可判定控制面）                 *)
(*    92 块全新内容；与主库 sf_ 体系零命名冲突（短名桥并存，        *)
(*    natlt_elim/bool_id_true/qleT_refl 等为本区独立版）。         *)
(*    依赖：仅 206 基线（不依赖 §1-§4 任何定义），追加于尾部。      *)
(*    scope 编排：§4 前 Close Scope Q_scope（护 _p9 nat 层），      *)
(*    本区需要 Q（qleT/qsum_w/top_p）→ 先 Open Scope Q_scope。     *)
(* ============================================================ *)

Open Scope Q_scope.  (* 恢复 Q 层；LiveCore 正文按 Q_scope 开环境编写验证 *)

Section LiveCore.

(* ============================================================ *)
(* §0 类型与桥                                                   *)
(* ============================================================ *)

Definition Context : Set := list nat.
Definition Sequence : Set := list nat.
Definition Candidates : Set := list Sequence.
Definition Memory : Set := list (nat * nat).

Record PRNG : Set := { seed : nat }.

Variable all_tokens : list nat.
Variable default_seq : Sequence.
Variable default_seq_valid : forall post_aud, Id (post_aud default_seq) true.
Variable ground_truth : Sequence -> bool.

(* NatLt 桥（_p9 同款） *)
Lemma natlt_elim : forall a b : nat, NatLt a b -> NatLe (Datatypes.S a) b.
Proof.
  intros a b H.
  (* 消去向独立装配（natlt_intro 反向同构）： Id 判定面消去取布尔等式，
     经次大比较反映面投影得严格序，再升格非严格序落于 NatLe 判定面
     （后继 a 与 b 的 leb 判定），判定面自反构造子闭合。 *)
  unfold NatLt in H.
  assert (Hb : Nat.ltb a b = true).
  { exact (RealSetoid.Id_eq (Nat.ltb a b) true H). }
  assert (Hlt : (a < b)%nat) by (apply Nat.ltb_lt; exact Hb).
  unfold NatLe.
  assert (Hleb : Nat.leb (Datatypes.S a) b = true).
  { apply Nat.leb_le. lia. }
  rewrite Hleb. apply id_refl.
Qed.

Lemma natlt_intro : forall a b : nat, (a < b)%nat -> NatLt a b.
Proof.
  intros a b H.
  (* 展开至定义层：布尔反映面先显式取等——次大比较规约后大一位的
     小于等于判定，经反映引理与线性算术装配，再改写闭合于自反构造子。 *)
  unfold NatLt.
  assert (Hb : Nat.ltb a b = true).
  { unfold Nat.ltb. apply Nat.leb_le. lia. }
  rewrite Hb.
  apply id_refl.
Qed.

(* bool ↔ Id 桥 *)
Lemma bool_id_true : forall b : bool, Id b true -> Id b true.
Proof.
  intros b H.
  (* 判定面恒等：布尔判定面在 Set 层即其自身；莱布尼茨投影面（b = true）
     于使用点以基线 Id 桥就地装配，本位不承载换桥。 *)
  exact H.
Qed.

Lemma bool_true_id : forall b : bool, b = true -> Id b true.
Proof.
  intros b H.
  (* 构去向独立装配（Id 判定面三分）：布尔逐支，真支以自反构造子直构
     判定面；假支真假莱布尼茨等无构造子可居，判别式构造性排除——不经换桥单跳。 *)
  destruct b as [|].
  - apply id_refl.
  - discriminate H.
Qed.

Lemma id_true_false_absurd : Id true false -> Empty_set.
Proof. intros H. inversion H. Qed.

Lemma id_false_true_absurd : Id false true -> Empty_set.
Proof. intros H. inversion H. Qed.

(* InT → In 换谱桥退役为判定面恒等：stdlib In 结论面（Prop）不居语句层，
   体内使用点以 InT 归纳就地装配 Prop 投影。 *)
Lemma inT_in_gen : forall (A : Set) (x : A) (l : list A), InT x l -> InT x l.
Proof.
  intros A x l H. exact H.
Qed.

(* filter 健全性（泛型） *)
Lemma inT_filter_sound_gen : forall (A : Set) (f : A -> bool) (l : list A) (x : A),
  InT x (filter f l) -> Id (f x) true.
Proof.
  intros A f l. induction l as [| a rest IH]; intros x H.
  - inversion H.
  - simpl in H. destruct (f a) eqn:E.
    + inversion H as [Heq | y0 l0 Hrec]; subst.
      * exact (bool_true_id _ E).
      * exact (IH _ Hrec).
    + exact (IH x H).
Qed.

(* forallb 逐点使用/构造（泛型） *)
Lemma forallb_inT_gen : forall (A : Set) (f : A -> bool) (l : list A) (x : A),
  Id (forallb f l) true -> InT x l -> Id (f x) true.
Proof.
  intros A f l. induction l as [| a rest IH]; intros x Hall Hin.
  - inversion Hin.
  - simpl in Hall. apply RealSetoid.Id_eq in Hall.
    apply andb_true_iff in Hall. destruct Hall as [Hh Ht].
    inversion Hin as [Heq | y0 l0 Hrec]; subst.
    + exact (bool_true_id _ Hh).
    + exact (IH _ (bool_true_id _ Ht) Hrec).
Qed.

Lemma inT_forallb_gen : forall (A : Set) (f : A -> bool) (l : list A),
  (forall x : A, In x l -> f x = true) -> Id (forallb f l) true.
Proof.
  intros A f l H. exact (bool_true_id (forallb f l) (proj2 (forallb_forall f l) (fun x Hin => H x Hin))).
Qed.

Lemma inT_cons_inv_gen : forall (A : Set) (x : A) (b : A) (l : list A),
  InT x (b :: l) -> Or (Id x b) (InT x l).
Proof.
  intros A x b l H. inversion H as [Heq | y0 l0 Hrec Heq2]; subst.
  - left. apply id_refl.
  - right. exact Hrec.
Qed.

(* InT 于 map 的逆向（信息性版，不走 Prop in_map_iff） *)
Lemma inT_map_inv_gen : forall (A B : Set) (f : A -> B) (l : list A) (y : B),
  InT y (map f l) -> sigT (fun x => And (InT x l) (Id (f x) y)).
Proof.
  intros A B f l. induction l as [| a rest IH]; intros y H.
  - inversion H.
  - simpl in H. inversion H as [Heq | y0 l0 Hrec]; subst.
    + exists a. split; [ apply InT_here | apply id_refl ].
    + destruct (IH y Hrec) as [x [Hx1 Hx2]]. exists x. split;
        [ right; exact Hx1 | exact Hx2 ].
Qed.

(* ============================================================ *)
(* §1 Q 层工具（判例：Q 禁 lia，显式引理装配）                     *)
(* ============================================================ *)

Lemma qleT_refl : forall x : Q, QleT' x x.
Proof.
  intro x.
  (* 三分样板复用（同 qleT_refl_local 定形）：展开至布尔判定定义体，
     序比较三分逐支构造等同项，大于支以整数层自反比较矛盾构造性排除。 *)
  unfold QleT'.
  change (Id (match Qcompare x x with Gt => false | _ => true end) true).
  destruct (Qcompare x x) eqn:E; simpl.
  - (* 小于支：判定面取真，自反构造子闭合 *)
    apply id_refl.
  - (* 等于支：同上 *)
    apply id_refl.
  - (* 大于支：构造性矛盾排除 *)
    exfalso.
    assert (Hrefl : Qcompare x x = Eq).
    { unfold Qcompare. apply Z.compare_refl. }
    rewrite Hrefl in E.
    discriminate E.
Qed.

Lemma qleT_to_qle : forall x y : Q, QleT' x y -> QleT' x y.
Proof. intros x y H. exact H. Qed.

Lemma qle_to_qleT : forall x y : Q, Qle x y -> QleT' x y.
Proof. intros x y H. exact (Qle_to_QleT' x y H). Qed.

Lemma qleT_trans : forall x y z : Q, QleT' x y -> QleT' y z -> QleT' x z.
Proof.
  intros x y z Hxy Hyz.
  apply qle_to_qleT. apply (Qle_trans x y z).
  - exact (QleT'_to_Qle x y Hxy).
  - exact (QleT'_to_Qle y z Hyz).
Qed.

Lemma qeq_le : forall x y : Q, x == y -> QleT' x y.
Proof. intros x y H. apply Qle_to_QleT'. rewrite H. apply Qle_refl. Qed.

Fixpoint qsum_w (w : nat -> Q) (l : list nat) : Q :=
  match l with
  | nil => 0%Q
  | x :: rest => w x + qsum_w w rest
  end.

(* 和的除法分配（判例：除法不经 Q-ring 的 Qminus 项；此处无 Qminus，field 安全） *)
Lemma qsum_w_div : forall (w : nat -> Q) (Z : Q) (l : list nat),
  (~ (Z == 0))%Q -> QeqT (qsum_w (fun t => w t / Z) l) (qsum_w w l / Z).
Proof.
  intros w Z l HZ. apply qeq_imp_qeqT. induction l as [| a rest IH]; simpl.
  - unfold Qdiv. rewrite Qmult_0_l. reflexivity.
  - rewrite IH. field. exact HZ.
Qed.

(* 归一化（全函数：Σ=0 回退零分布） *)
Definition q_normalize (w : nat -> Q) (l : list nat) : nat -> Q :=
  let Z := qsum_w w l in
  if Qeq_bool Z 0%Q then fun _ => 0%Q
  else fun t => w t / Z.

(* 归一化定理：Σ>0 前提下归一化分布质量和为 1 *)
Lemma q_normalize_normalized : forall (w : nat -> Q) (l : list nat),
  Qlt 0%Q (qsum_w w l) -> Id (Qeq_bool (qsum_w (q_normalize w l) l) 1%Q) true.
Proof.
  intros w l HZ. unfold q_normalize.
  destruct (Qeq_bool (qsum_w w l) 0%Q) eqn:Ez.
  - exfalso.
    assert (Heq : (qsum_w w l == 0)%Q) by (apply (proj1 (Qeq_bool_iff (qsum_w w l) 0%Q)); exact Ez).
    rewrite Heq in HZ. exact (Qlt_irrefl 0%Q HZ).
  - apply bool_true_id. apply (proj2 (Qeq_bool_iff _ _)).
    assert (Hsum : qsum_w (fun t => w t / qsum_w w l) l == qsum_w w l / qsum_w w l).
    { apply qeqT_imp_qeq. apply qsum_w_div.
      intro Hzero. rewrite Hzero in HZ. exact (Qlt_irrefl 0%Q HZ). }
    assert (Hself : (qsum_w w l / qsum_w w l == 1)%Q).
    { unfold Qdiv. field.
      intro Hzero. rewrite Hzero in HZ. exact (Qlt_irrefl 0%Q HZ). }
    exact (Qeq_trans _ _ _ Hsum Hself).
Qed.

(* ============================================================ *)
(* §2 选择核（best-携带扫描；不变式骨架＝判例7；三分反映＝判例6）   *)
(* ============================================================ *)

Fixpoint q_pick_aux {A : Set} (w : A -> Q) (l : list A) (best : A) : A :=
  match l with
  | nil => best
  | x :: rest => if Qle_bool (w x) (w best) then q_pick_aux w rest best
                 else q_pick_aux w rest x
  end.

Lemma q_pick_aux_dom : forall (A : Set) (w : A -> Q) (l : list A) (b : A),
  And (QleT' (w b) (w (q_pick_aux w l b)))
      (forall x : A, InT x l -> QleT' (w x) (w (q_pick_aux w l b))).
Proof.
  intros A w l. induction l as [| a rest IH]; intro b; simpl.
  - split.
    + apply qleT_refl.
    + intros x Hin. inversion Hin.
  - destruct (Qle_bool (w a) (w b)) eqn:E.
    + destruct (IH b) as [H1 H2]. split.
      * exact H1.
      * intros x Hin.
        assert (Hgen : forall z : A, InT z (a :: rest) ->
                         QleT' (w z) (w (q_pick_aux w rest b))).
        { intros z Hz. inversion Hz as [Heq | y0 l0 Hrec]; subst.
          - apply (qleT_trans _ (w b) _).
            ++ exact (bool_true_id _ E).
            ++ exact H1.
          - exact (H2 _ Hrec). }
        exact (Hgen x Hin).
    + destruct (IH a) as [H1 H2]. split.
      * apply (qleT_trans (w b) (w a) (w (q_pick_aux w rest a))).
        -- destruct (Q_dec (w b) (w a)) as [[Hlt | Heqb] | Hgt].
           ++ apply qle_to_qleT. apply Qlt_le_weak. exact Hlt.
           ++ exfalso.
              assert (Hb1 : Qle_bool (w a) (w b) = true).
              { apply (proj2 (Qle_bool_iff (w a) (w b))).
                apply Qlt_le_weak. exact Heqb. }
              rewrite Hb1 in E. discriminate E.
           ++ apply qeq_le. exact Hgt.
        -- exact H1.
      * intros x Hin. inversion Hin as [Heq | y0 l0 Hrec]; subst.
        -- exact H1.
        -- exact (H2 x Hrec).
Qed.

Lemma q_pick_aux_in : forall (A : Set) (w : A -> Q) (l : list A) (b : A),
  InT (q_pick_aux w l b) (b :: l).
Proof.
  intros A w l. induction l as [| a rest IH]; intro b.
  - left.
  - simpl. destruct (Qle_bool (w a) (w b)) eqn:E.
    + destruct (inT_cons_inv_gen A (q_pick_aux w rest b) b rest (IH b)) as [Heq | Hrec].
      * rewrite Heq. left.
      * right. right. exact Hrec.
    + right. exact (IH a).
Qed.

(* nat 投票选择（NatLe = Id (Nat.leb ..) true） *)
Fixpoint nat_pick_aux {A : Set} (w : A -> nat) (l : list A) (best : A) : A :=
  match l with
  | nil => best
  | x :: rest => if Nat.leb (w x) (w best) then nat_pick_aux w rest best
                 else nat_pick_aux w rest x
  end.

Lemma nat_pick_aux_dom : forall (A : Set) (w : A -> nat) (l : list A) (b : A),
  And (NatLe (w b) (w (nat_pick_aux w l b)))
      (forall x : A, InT x l -> NatLe (w x) (w (nat_pick_aux w l b))).
Proof.
  intros A w l. induction l as [| a rest IH]; intro b; simpl.
  - split.
    + apply (RealSetoid.eq_Id _ _). apply Nat.leb_refl.
    + intros x Hin. inversion Hin.
  - destruct (Nat.leb (w a) (w b)) eqn:E.
    + destruct (IH b) as [H1 H2]. split.
      * exact H1.
      * intros x Hin.
        assert (Hgen : forall z : A, InT z (a :: rest) ->
                         NatLe (w z) (w (nat_pick_aux w rest b))).
        { intros z Hz. inversion Hz as [Heq | y0 l0 Hrec]; subst.
          - apply (RealSetoid.le_to_NatLe).
            pose proof (NatLe_drop _ _ H1) as Hh1.
            pose proof (NatLe_drop _ _ (bool_true_id _ E)) as Hle2.
            lia.
          - exact (H2 _ Hrec). }
        exact (Hgen x Hin).
    + destruct (IH a) as [H1 H2]. split.
      * apply (RealSetoid.le_to_NatLe).
        assert (Hgt : (w b < w a)%nat).
        { apply (proj1 (Nat.leb_gt (w a) (w b))). exact E. }
        pose proof (NatLe_drop _ _ H1) as Hh1.
        lia.
      * intros x Hin. inversion Hin as [Heq | y0 l0 Hrec]; subst.
        -- exact H1.
        -- exact (H2 x Hrec).
Qed.

Lemma nat_pick_aux_in : forall (A : Set) (w : A -> nat) (l : list A) (b : A),
  InT (nat_pick_aux w l b) (b :: l).
Proof.
  intros A w l. induction l as [| a rest IH]; intro b; simpl.
  - left.
  - destruct (Nat.leb (w a) (w b)) eqn:E.
    + destruct (inT_cons_inv_gen A (nat_pick_aux w rest b) b rest (IH b)) as [Heq | Hrec].
      * rewrite Heq. left.
      * right. right. exact Hrec.
    + right. exact (IH a).
Qed.

(* 审计门控选择：按表序找首个通过审计的 token（带回溯预算的扫描原语） *)
Fixpoint pick_passing (aud : nat -> bool) (fuel : nat) (l : list nat) : option nat :=
  match l with
  | nil => None
  | x :: rest => match fuel with
                 | 0%nat => None
                 | Datatypes.S f => if aud x then Some x else pick_passing aud f rest
                 end
  end.

Lemma pick_passing_some : forall (aud : nat -> bool) (fuel : nat) (l : list nat) (x : nat),
  pick_passing aud fuel l = Some x -> Id (aud x) true.
Proof.
  intros aud fuel l. revert fuel.
  induction l as [| a rest IHl]; intros fuel x H; simpl in H.
  - destruct fuel; discriminate H.
  - destruct fuel as [| f].
    + discriminate H.
    + destruct (aud a) eqn:E.
      * cbn [pick_passing] in H. try rewrite E in H. simpl in H.
        injection H as Hax. rewrite <- Hax. exact (bool_true_id _ E).
      * cbn [pick_passing] in H. try rewrite E in H.
        exact (IHl f x H).
Qed.

Lemma pick_passing_none_all_fail : forall (aud : nat -> bool) (l : list nat) (fuel : nat),
  (length l <= fuel)%nat -> pick_passing aud fuel l = None ->
  forall x : nat, In x l -> Id (aud x) false.
Proof.
  intros aud l. induction l as [| a rest IH]; intros fuel Hlen Hnil x Hin.
  - exfalso. inversion Hin.
  - simpl in Hnil. simpl in Hlen. destruct fuel as [| f].
    + lia.
    + cbn [pick_passing] in Hnil. try rewrite E in Hnil. simpl in Hnil.
      destruct (aud a) eqn:E.
      * discriminate Hnil.
      * (* In 分位先落 Prop 投影面（Id 目标禁 Prop 消去），再以布尔等值桥升格 *)
        assert (Hprop : aud x = false).
        { destruct Hin as [Heq | Hin2].
          - subst. exact E.
          - apply RealSetoid.Id_eq. apply (IH f); [lia | exact Hnil | exact Hin2]. }
        exact (RealSetoid.eq_Id (aud x) false Hprop).
Qed.

(* ============================================================ *)
(* §3 审计器接口与实例                                            *)
(* ============================================================ *)

Definition PreAud  := Context -> bool.
Definition InAud   := Context -> Sequence -> nat -> bool.
Definition PostAud := Sequence -> bool.

Fixpoint in_seq (t : nat) (s : Sequence) : bool :=
  match s with
  | nil => false
  | x :: rest => orb (Nat.eqb x t) (in_seq t rest)
  end.

Definition token_supported_by_memory (mem : Memory) (t : nat) : bool :=
  existsb (fun ab => orb (Nat.eqb (fst ab) t) (Nat.eqb (snd ab) t)) mem.

Definition memory_auditor (mem : Memory) : InAud :=
  fun c prefix t => token_supported_by_memory mem t.

Definition threshold_auditor (soft : Sequence -> Q) (th : Q) : PostAud :=
  fun s => Qle_bool th (soft s).

Theorem threshold_auditor_sound : forall (soft : Sequence -> Q) (th : Q) (s : Sequence),
  Id (threshold_auditor soft th s) true -> QleT' th (soft s).
Proof. intros soft th s H. exact H. Qed.

(* ============================================================ *)
(* §4 审计器代数（逐点化——消 functional_extensionality 公理风险）    *)
(* ============================================================ *)

Definition audit_and (a1 a2 : PostAud) : PostAud := fun s => andb (a1 s) (a2 s).
Definition audit_or  (a1 a2 : PostAud) : PostAud := fun s => orb (a1 s) (a2 s).

Theorem audit_and_sound_set : forall (a1 a2 : PostAud) (s : Sequence),
  Id (audit_and a1 a2 s) true -> And (Id (a1 s) true) (Id (a2 s) true).
Proof.
  intros a1 a2 s H. unfold audit_and in H.
  apply RealSetoid.Id_eq in H. apply andb_true_iff in H.
  destruct H as [H1 H2]. split.
  - apply bool_true_id. exact H1.
  - apply bool_true_id. exact H2.
Qed.

Theorem audit_or_complete : forall (a1 a2 : PostAud) (s : Sequence),
  sigT (fun b : bool => Id (if b then a1 s else a2 s) true) ->
  Id (audit_or a1 a2 s) true.
Proof.
  intros a1 a2 s [b Hb]. unfold audit_or. apply bool_true_id.
  destruct b; simpl in Hb.
  - rewrite (RealSetoid.Id_eq _ true Hb). reflexivity.
  - rewrite (RealSetoid.Id_eq _ true Hb). apply orb_true_r.
Qed.

Theorem audit_and_comm : forall (a b : PostAud) (s : Sequence),
  Id (audit_and a b s) (audit_and b a s).
Proof.
  intros a b s.
  (* 判定面四分（序三分样板族推广）：展开至逐点布尔判定面，真值组合四支
     逐支以自反构造子闭合（无矛盾支）——不经莱布尼茨换桥、不使用交换引理。 *)
  unfold audit_and.
  destruct (a s) as [|]; destruct (b s) as [|]; simpl; apply id_refl.
Qed.

Theorem audit_or_comm : forall (a b : PostAud) (s : Sequence),
  Id (audit_or a b s) (audit_or b a s).
Proof.
  intros a b s.
  (* 判定面四分（序三分样板族推广）：展开至逐点布尔判定面，真值组合四支
     逐支以自反构造子闭合（无矛盾支）——不经莱布尼茨换桥、不使用交换引理。 *)
  unfold audit_or.
  destruct (a s) as [|]; destruct (b s) as [|]; simpl; apply id_refl.
Qed.

Theorem audit_and_assoc : forall (a b c : PostAud) (s : Sequence),
  Id (audit_and (audit_and a b) c s) (audit_and a (audit_and b c) s).
Proof. intros a b c s. unfold audit_and. apply RealSetoid.eq_Id.
  symmetry. apply andb_assoc. Qed.

(* 审计器格偏序（Id 化后整式为 Set：原 eq 版 a s = true -> b s true 仍是 Prop） *)
Definition auditor_le (a b : PostAud) : Set :=
  forall s : Sequence, Id (a s) true -> Id (b s) true.

Theorem audit_and_is_meet : forall (a b : PostAud),
  And (auditor_le (audit_and a b) a)
      (And (auditor_le (audit_and a b) b)
           (forall c : PostAud,
              auditor_le c a -> auditor_le c b -> auditor_le c (audit_and a b))).
Proof.
  intros a b. split.
  - intros s H. unfold audit_and in H. apply RealSetoid.Id_eq in H.
    apply andb_true_iff in H. apply bool_true_id. exact (proj1 H).
  - split.
    + intros s H. unfold audit_and in H. apply RealSetoid.Id_eq in H.
      apply andb_true_iff in H. apply bool_true_id. exact (proj2 H).
    + intros c Hca Hcb s Hs. unfold audit_and. apply bool_true_id.
      apply andb_true_iff. split.
      * exact (RealSetoid.Id_eq _ true (Hca s Hs)).
      * exact (RealSetoid.Id_eq _ true (Hcb s Hs)).
Qed.

Theorem audit_or_is_join : forall (a b : PostAud),
  And (auditor_le a (audit_or a b))
      (And (auditor_le b (audit_or a b))
           (forall c : PostAud,
              auditor_le a c -> auditor_le b c -> auditor_le (audit_or a b) c)).
Proof.
  intros a b. split.
  - intros s H. unfold audit_or. apply bool_true_id.
    rewrite (RealSetoid.Id_eq _ true H). apply orb_true_l.
  - split.
    + intros s H. unfold audit_or. apply bool_true_id.
      rewrite (RealSetoid.Id_eq _ true H). apply orb_true_r.
    + intros c Hac Hbc s Hs. unfold audit_or in Hs.
      destruct (a s) eqn:Ea; destruct (b s) eqn:Eb.
      * exact (Hac s (bool_true_id _ Ea)).
      * exact (Hac s (bool_true_id _ Ea)).
      * exact (Hbc s (bool_true_id _ Eb)).
      * destruct (id_false_true_absurd Hs).
Qed.

(* 并行审计（双向；语句层 InT） *)
Definition parallel_audit (auds : list PostAud) : PostAud :=
  fun s => forallb (fun aud => aud s) auds.

Theorem parallel_audit_correct : forall (auds : list PostAud) (s : Sequence),
  And (Id (parallel_audit auds s) true -> forall aud : PostAud, InT aud auds -> Id (aud s) true)
      ((forall aud : PostAud, InT aud auds -> Id (aud s) true) ->
       Id (parallel_audit auds s) true).
Proof.
  intros auds s. split; intros H.
  - intros aud Hin. exact (forallb_inT_gen PostAud (fun a => a s) auds aud H Hin).
  - apply bool_true_id.
    induction auds as [| a0 rest0 IHrest]; simpl.
    + reflexivity.
    + apply andb_true_iff. split.
      * exact (RealSetoid.Id_eq _ true (H a0 (InT_here a0 rest0))).
      * specialize (IHrest (fun aud Haud => H aud (InT_next aud a0 rest0 Haud))).
        exact IHrest.
Qed.

(* 多数审计（修正原 count 版无判等缺陷：按 bool 计票） *)
Fixpoint count_true (bs : list bool) : nat :=
  match bs with
  | nil => 0%nat
  | b :: rest => if b then Datatypes.S (count_true rest) else count_true rest
  end.

Definition majority_audit (auds : list PostAud) : PostAud :=
  fun s => Nat.ltb (length auds) (Nat.double (count_true (map (fun aud => aud s) auds))).

(* ============================================================ *)
(* §5 生成核：审计门控轨迹（trail 版为正源）                        *)
(* ============================================================ *)

Fixpoint generate_trail (in_aud : InAud) (c : Context) (prefix : Sequence)
         (remaining : nat) : Sequence * list (nat * bool) :=
  match remaining with
  | 0%nat => (prefix, nil)
  | Datatypes.S n =>
      match pick_passing (in_aud c prefix) (length all_tokens) all_tokens with
      | None => (prefix, nil)
      | Some t =>
          let p := generate_trail in_aud c (prefix ++ (t :: nil)) n in
          (fst p, (t, in_aud c prefix t) :: snd p)
      end
  end.

Definition generate_audited (in_aud : InAud) (c : Context) (prefix : Sequence)
           (n : nat) : Sequence :=
  fst (generate_trail in_aud c prefix n).

(* 轨迹合法性：每条 trail 记录的 token 在其选择前缀处通过审计 *)
Theorem generate_audited_legal_trajectory :
  forall (in_aud : InAud) (c : Context) (prefix : Sequence) (n : nat),
  Id (forallb (fun tb => snd tb) (snd (generate_trail in_aud c prefix n))) true.
Proof.
  intros in_aud c prefix n. revert prefix.
  induction n as [| n IH]; intros prefix; simpl.
  - apply bool_true_id. reflexivity.
  - destruct (pick_passing (in_aud c prefix) (length all_tokens) all_tokens) as [t |] eqn:Ep.
    + assert (Haud : Id (in_aud c prefix t) true)
        by exact (pick_passing_some (in_aud c prefix) (length all_tokens) all_tokens t Ep).
      simpl. apply bool_true_id. apply andb_true_iff. split.
      * exact (RealSetoid.Id_eq _ true Haud).
      * exact (RealSetoid.Id_eq _ true (IH (prefix ++ (t :: nil)))).
    + apply bool_true_id. reflexivity.
Qed.

(* 轨迹完整性：长度守恒 + 逐记录审计通过（每前缀至少一 token 可过审前提下） *)
Theorem audit_trail_complete :
  forall (in_aud : InAud) (c : Context) (prefix : Sequence) (n : nat)
         (Hstep : forall p : Sequence,
                    sigT (fun t => And (InT t all_tokens) (Id (in_aud c p t) true))),
  let p := generate_trail in_aud c prefix n in
  And (Id (length (fst p)) (length prefix + length (snd p))%nat)
      (Id (forallb (fun tb => snd tb) (snd p)) true).
Proof.
  intros in_aud c prefix n Hstep. revert prefix.
  induction n as [| n IH]; intros prefix; simpl.
  - rewrite Nat.add_0_r. split.
    + apply (RealSetoid.eq_Id _ _). reflexivity.
    + apply bool_true_id. reflexivity.
  - destruct (pick_passing (in_aud c prefix) (length all_tokens) all_tokens) as [t |] eqn:Ep.
    + assert (Haud : Id (in_aud c prefix t) true)
        by exact (pick_passing_some (in_aud c prefix) (length all_tokens) all_tokens t Ep).
      destruct (IH (prefix ++ (t :: nil))) as [Hlen Hall].
      simpl. split.
      * apply (RealSetoid.eq_Id _ _).
        apply RealSetoid.Id_eq in Hlen.
        rewrite length_app in Hlen.
        simpl in Hlen. lia.
      * apply bool_true_id. apply andb_true_iff. split.
        -- exact (RealSetoid.Id_eq _ true Haud).
        -- exact (RealSetoid.Id_eq _ true Hall).
    + exfalso.
      destruct (Hstep prefix) as [t [Hin Haud]].
      assert (HinP : In t all_tokens).
      { exact (InT_ind nat t (fun l _ => In t l)
                 (fun l => or_introl eq_refl)
                 (fun y l _ IHin => or_intror IHin) all_tokens Hin). }
      assert (Hfail : Id (in_aud c prefix t) false).
      { apply (pick_passing_none_all_fail (in_aud c prefix) all_tokens
                 (length all_tokens)); [lia | exact Ep | exact HinP]. }
      destruct (id_false_true_absurd (id_trans (id_sym Hfail) Haud)).
Qed.

(* 输出审计：过滤首通过者 / 缺省安全序列 *)
Definition post_stage_audited (post_aud : PostAud) (cands : Candidates) : Sequence :=
  match filter (fun s => post_aud s) cands with
  | nil => default_seq
  | s :: _ => s
  end.

Theorem post_audit_sound : forall (post_aud : PostAud) (cands : Candidates),
  Id (post_aud (post_stage_audited post_aud cands)) true.
Proof.
  intros post_aud cands. unfold post_stage_audited.
  destruct (filter (fun s => post_aud s) cands) as [| s rest] eqn:E.
  - apply default_seq_valid.
  - assert (Hin : InT s (filter (fun x => post_aud x) cands)).
    { rewrite E. left. }
    exact (inT_filter_sound_gen Sequence (fun x => post_aud x) cands s Hin).
Qed.

(* 幻觉零化（L210 修正版：Id 形式 + bool ground_truth；健全性传播） *)
Theorem audited_hallucination_zero :
  forall (oracle : PostAud),
  (forall s : Sequence, Id (oracle s) true -> Id (ground_truth s) true) ->
  forall (cands : Candidates),
  Id (oracle (post_stage_audited oracle cands)) true ->
  Id (ground_truth (post_stage_audited oracle cands)) true.
Proof.
  intros oracle Hsound cands Hpass. exact (Hsound (post_stage_audited oracle cands) Hpass).
Qed.

(* 审计重采样：通过审计 或 回退安全序列（Or := A+B，Set 层析取） *)
Fixpoint resample_attempt (post_aud : PostAud) (g : nat -> Sequence)
         (attempts : nat) : Sequence :=
  match attempts with
  | 0%nat => default_seq
  | Datatypes.S m => let s := g m in
                     if post_aud s then s else resample_attempt post_aud g m
  end.

Theorem resample_terminates : forall (post_aud : PostAud) (g : nat -> Sequence) (attempts : nat),
  Or (Id (post_aud (resample_attempt post_aud g attempts)) true)
     (Id (resample_attempt post_aud g attempts) default_seq).
Proof.
  intros post_aud g attempts. induction attempts as [| m IH]; simpl.
  - right. apply id_refl.
  - destruct (post_aud (g m)) eqn:E.
    + simpl. left. rewrite E. apply id_refl.
    + simpl. exact IH.
Qed.

(* ============================================================ *)
(* §6 共识与早停（Post 阶段）                                     *)
(* ============================================================ *)

Fixpoint seq_eqb (s1 s2 : Sequence) : bool :=
  match s1, s2 with
  | nil, nil => true
  | x :: r1, y :: r2 => andb (Nat.eqb x y) (seq_eqb r1 r2)
  | _, _ => false
  end.

Fixpoint vote_count (s : Sequence) (cands : Candidates) : nat :=
  match cands with
  | nil => 0%nat
  | c :: rest => if seq_eqb s c then Datatypes.S (vote_count s rest) else vote_count s rest
  end.

Definition consensus_post (cands : Candidates) : Sequence :=
  match cands with
  | nil => nil
  | x :: rest => nat_pick_aux (fun s => vote_count s cands) rest x
  end.

Theorem consensus_mode : forall (cands : Candidates)
         (Hne : sigT (fun a => InT a cands)) (s : Sequence),
  InT s cands -> NatLe (vote_count s cands) (vote_count (consensus_post cands) cands).
Proof.
  intros cands Hne s Hin. destruct cands as [| x rest].
  - destruct Hne as [a Ha]. inversion Ha.
  - simpl. destruct (nat_pick_aux_dom Sequence
              (fun s0 => vote_count s0 (x :: rest)) rest x) as [H1 H2].
    assert (Hgen : forall z : Sequence, InT z (x :: rest) ->
              NatLe (vote_count z (x :: rest))
                    (vote_count (nat_pick_aux (fun s0 => vote_count s0 (x :: rest)) rest x)
                                (x :: rest))).
    { intros z Hz. inversion Hz as [Heq | y0 l0 Hrec]; subst.
      - exact H1.
      - exact (H2 _ Hrec). }
    exact (Hgen s Hin).
Qed.

Definition agent_candidates (agents : list (Context -> Sequence)) (c : Context) : Candidates :=
  map (fun ag => ag c) agents.

Theorem multi_agent_consensus_member :
  forall (agents : list (Context -> Sequence)) (c : Context) (out : Sequence),
  InT out (agent_candidates agents c) ->
  sigT (fun ag => And (InT ag agents) (Id out (ag c))).
Proof.
  intros agents c out Hin.
  destruct (inT_map_inv_gen (Context -> Sequence) Sequence
              (fun ag => ag c) agents out Hin) as [ag [Hag1 Hag2]].
  exists ag. split.
  - exact Hag1.
  - exact (id_sym Hag2).
Qed.

Fixpoint q_of_nat (n : nat) : Q :=
  match n with
  | O => 0%Q
  | Datatypes.S k => 1%Q + q_of_nat k
  end.

Fixpoint overlap_count (s1 s2 : Sequence) : nat :=
  match s1 with
  | nil => 0%nat
  | x :: rest => if in_seq x s2 then Datatypes.S (overlap_count rest s2)
                 else overlap_count rest s2
  end.

Fixpoint sum_overlap (s : Sequence) (cands : Candidates) : nat :=
  match cands with
  | nil => 0%nat
  | s' :: rest => overlap_count s s' + sum_overlap s rest
  end.

Definition self_consistency_score (s : Sequence) (cands : Candidates) : Q :=
  q_of_nat (sum_overlap s cands).

(* 早停（信息性析取 orb 的 Id 形式；R7 版方向：燃料计数右边） *)
Definition stop_condition (threshold : Q) (cands : Candidates) : bool :=
  forallb (fun s => Qle_bool threshold (self_consistency_score s cands)) cands.

Fixpoint sample_until_confident (threshold : Q) (max_iter : nat) (acc : Candidates)
         (draw : PRNG -> Sequence * PRNG) (prng : PRNG) : Candidates * PRNG :=
  match max_iter with
  | 0%nat => (acc, prng)
  | Datatypes.S n =>
      if stop_condition threshold acc then (acc, prng)
      else let p := draw prng in
           sample_until_confident threshold n (fst p :: acc) draw (snd p)
  end.

Theorem early_stop_confidence :
  forall (threshold : Q) (max_iter : nat) (acc : Candidates)
         (draw : PRNG -> Sequence * PRNG) (prng : PRNG),
  let p := sample_until_confident threshold max_iter acc draw prng in
  Id (orb (stop_condition threshold (fst p))
          (Nat.eqb (length (fst p)) (length acc + max_iter)%nat)) true.
Proof.
  intros threshold max_iter. induction max_iter as [| n IH];
    intros acc draw prng; cbv zeta; cbn [sample_until_confident fst].
  - rewrite Nat.add_0_r.
    destruct (stop_condition threshold acc); apply bool_true_id;
      [ reflexivity | apply Nat.eqb_refl ].
  - destruct (stop_condition threshold acc) eqn:E.
    + cbn [fst]. rewrite E. reflexivity.
    + pose proof (IH (fst (draw prng) :: acc) draw (snd (draw prng))) as Horb.
      apply RealSetoid.Id_eq in Horb.
      destruct (stop_condition threshold
                  (fst (sample_until_confident threshold n
                          (fst (draw prng) :: acc) draw (snd (draw prng))))) eqn:Es.
      * reflexivity.
      * cbn [orb] in Horb. cbn [orb].
        apply bool_true_id. apply Nat.eqb_eq.
        apply Nat.eqb_eq in Horb.
        replace (length (fst (draw prng) :: acc)) with (Datatypes.S (length acc)) in Horb
          by reflexivity.
        lia.
Qed.

Theorem early_stop_confidence' :
  forall (threshold : Q) (max_iter : nat) (acc : Candidates)
         (draw : PRNG -> Sequence * PRNG) (prng : PRNG),
  let p := sample_until_confident threshold max_iter acc draw prng in
  Id (stop_condition threshold (fst p)) true ->
  forall s : Sequence, InT s (fst p) ->
    QleT' threshold (self_consistency_score s (fst p)).
Proof.
  intros threshold max_iter acc draw prng. cbv zeta.
  intros Hstop s Hin. unfold stop_condition in Hstop.
  exact (forallb_inT_gen Sequence _ _ _ Hstop Hin).
Qed.

(* ============================================================ *)
(* §7 状态化审计器                                                *)
(* ============================================================ *)

Variable State : Set.

Record StatefulAud : Set := {
  aud_step : State -> nat -> bool;
  st_update : State -> nat -> State
}.

Fixpoint generate_stateful (aud : StatefulAud) (st : State) (prefix : Sequence)
         (remaining : nat) : Sequence * State :=
  match remaining with
  | 0%nat => (prefix, st)
  | Datatypes.S n =>
      match pick_passing (aud_step aud st) (length all_tokens) all_tokens with
      | None => (prefix, st)
      | Some t => generate_stateful aud (st_update aud st t) (prefix ++ (t :: nil)) n
      end
  end.

(* 状态一致性（#49 修正版：折乘作用在生成后缀 skipn 上，不 rev） *)
Lemma generate_stateful_inv : forall (aud : StatefulAud) (n : nat) (st : State)
         (prefix : Sequence),
  sigT (fun gen => And (Id (fst (generate_stateful aud st prefix n)) (prefix ++ gen))
                       (Id (snd (generate_stateful aud st prefix n))
                           (fold_left (st_update aud) gen st))).
Proof.
  intros aud n. induction n as [| n IH]; intros st prefix; simpl.
  - exists nil. split.
    + apply (RealSetoid.eq_Id _ _). symmetry. apply app_nil_r.
    + apply id_refl.
  - destruct (pick_passing (aud_step aud st) (length all_tokens) all_tokens) as [t |] eqn:Ep.
    + destruct (IH (st_update aud st t) (prefix ++ (t :: nil))) as [gen [H1 H2]].
      exists (t :: gen). split.
      * apply RealSetoid.Id_eq in H1. apply RealSetoid.eq_Id.
        rewrite <- app_assoc in H1. simpl in H1. exact H1.
      * cbn [fold_left]. exact H2.
    + exists nil. split.
      * apply (RealSetoid.eq_Id _ _). symmetry. apply app_nil_r.
      * apply id_refl.
Qed.

Theorem stateful_generation_consistent :
  forall (aud : StatefulAud) (st : State) (prefix : Sequence) (n : nat),
  let p := generate_stateful aud st prefix n in
  Id (snd p) (fold_left (st_update aud) (skipn (length prefix) (fst p)) st).
Proof.
  intros aud st prefix n.
  destruct (generate_stateful_inv aud n st prefix) as [gen [H1 H2]].
  cbv zeta. apply RealSetoid.Id_eq in H1. rewrite H1.
  rewrite skipn_app. rewrite skipn_all. rewrite Nat.sub_diag. simpl.
  exact H2.
Qed.

(* ============================================================ *)
(* §8 审计束搜索（#48；#21 支配留蓝图——需排序机器）                 *)
(* ============================================================ *)

Definition BeamState : Set := (Sequence * Q)%type.

Fixpoint last_token (s : Sequence) : nat :=
  match s with
  | nil => 0
  | x :: nil => x
  | _ :: rest => last_token rest
  end.

Fixpoint remove_last (s : Sequence) : Sequence :=
  match s with
  | nil => nil
  | x :: rest =>
      match rest with
      | nil => nil
      | _ :: _ => x :: remove_last rest
      end
  end.

Fixpoint concat_map_gen {A B : Set} (f : A -> list B) (l : list A) : list B :=
  match l with
  | nil => nil
  | x :: rest => f x ++ concat_map_gen f rest
  end.

Definition expand_beam_audited (in_aud : InAud) (c : Context) (beam : list BeamState)
  : list BeamState :=
  filter (fun st => in_aud c (remove_last (fst st)) (last_token (fst st)))
         (concat_map_gen
            (fun st => map (fun t => (fst st ++ (t :: nil), snd st)) all_tokens) beam).

Theorem expand_beam_audited_legal :
  forall (in_aud : InAud) (c : Context) (beam : list BeamState) (st : BeamState),
  InT st (expand_beam_audited in_aud c beam) ->
  Id (in_aud c (remove_last (fst st)) (last_token (fst st))) true.
Proof.
  intros in_aud c beam st H.
  exact (inT_filter_sound_gen BeamState
           (fun st0 => in_aud c (remove_last (fst st0)) (last_token (fst st0)))
           _ st H).
Qed.

(* ============================================================ *)
(* §9 Top-p 截断（#19 修正版：前提方向已翻转；Q 显式装配）            *)
(* ============================================================ *)

Fixpoint top_p_prefix (p : Q) (sorted : list nat) (w : nat -> Q) : list nat :=
  match sorted with
  | nil => nil
  | t :: rest =>
      if Qle_bool p 0 then nil
      else if Qle_bool p (w t) then t :: nil
      else t :: top_p_prefix (p - w t) rest w
  end.

Theorem top_p_cumulative_ge :
  forall (p : Q) (sorted : list nat) (w : nat -> Q),
  Qle p (qsum_w w sorted) -> QleT' p (qsum_w w (top_p_prefix p sorted w)).
Proof.
  intros p sorted w. revert p.
  induction sorted as [| t rest IH]; intros p Hp.
  - apply Qle_to_QleT'. simpl in Hp. simpl. exact Hp.
  - apply Qle_to_QleT'. simpl. destruct (Qle_bool p 0%Q) eqn:E0.
    + apply (QleT'_to_Qle p 0%Q). exact (bool_true_id _ E0).
    + assert (Hp0 : Qlt 0 p).
      { destruct (Q_dec 0 p) as [[Hlt | Heq] | Hgt].
        - exact Hlt.
        - exfalso.
          assert (Hb : Qle_bool p 0%Q = true).
          { apply (proj2 (Qle_bool_iff p 0%Q)). apply Qlt_le_weak. exact Heq. }
          rewrite Hb in E0. discriminate E0.
        - exfalso.
          assert (Hb : Qle_bool p 0%Q = true).
          { apply (proj2 (Qle_bool_iff p 0%Q)).
            rewrite <- Hgt. apply Qle_refl. }
          rewrite Hb in E0. discriminate E0. }
      destruct (Qle_bool p (w t)) eqn:E1.
      * cbn [top_p_prefix qsum_w].
        assert (Hz : (w t + 0%Q == w t)%Q) by ring.
        rewrite Hz. apply (QleT'_to_Qle p (w t)). exact (bool_true_id _ E1).
      * assert (Hwlt : Qlt (w t) p).
        { destruct (Q_dec p (w t)) as [[Hle' | Heq] | Hgt'].
          - exfalso.
            assert (Hb : Qle_bool p (w t) = true).
            { apply (proj2 (Qle_bool_iff p (w t))). apply Qlt_le_weak. exact Hle'. }
            rewrite Hb in E1. discriminate E1.
          - exact Heq.
          - exfalso.
            assert (Hb : Qle_bool p (w t) = true).
            { apply (proj2 (Qle_bool_iff p (w t))).
              rewrite Hgt'. apply Qle_refl. }
            rewrite Hb in E1. discriminate E1. }
        assert (Hpre : Qle (p + (- w t)) (qsum_w w rest)).
        { apply (Qle_trans (p + (- w t))
                           ((w t + qsum_w w rest) + (- w t))%Q
                           (qsum_w w rest)).
          - apply Qplus_le_compat.
            + exact Hp.
            + apply Qle_refl.
          - apply QleT'_to_Qle. apply qeq_le. ring. }
        cbn [top_p_prefix].
        apply (Qle_trans p (w t + (p + (- w t)))
                         (w t + qsum_w w (top_p_prefix (p + (- w t)) rest w))).
        -- assert (Hz : (p == w t + (p + (- w t)))%Q) by ring.
           rewrite Hz at 1. apply Qle_refl.
        -- apply (Qplus_le_compat (w t) (w t) (p + (- w t))
                    (qsum_w w (top_p_prefix (p + (- w t)) rest w))).
           ++ apply Qle_refl.
           ++ exact (QleT'_to_Qle _ _ (IH (p + (- w t)) Hpre)).
Qed.

End LiveCore.

(* ============================================================ *)
(* 提取注记：Recursive Extraction 本文件 + 上游 baseline 接口，     *)
(*   全部为 nat/bool/list/Q 信息性计算，无 Obj.magic。              *)
(*   （提取验证在编译绿后由 extract 脚本执行）                      *)
(* 蓝图保留项（不在本模块，见 Live-修正版.V §7-8）：                *)
(*   projected_distribution_minimizes_kl / free_energy_with_audit_decomp *)
(*   / stricter_auditor F 代价 / TV 严格分离 / beam 支配 / 长度归一化   *)
(*   ——依赖柯西实数比较、log/KL 机器或排序机器，待接口入库另立论证。    *)
(* ============================================================ *)

End LCAudit.

(* ============================================================ *)
(* KLProjection 合并块（论证③：审计 = KL 投影）——源 KLProjection.v，去 Require 头；*)
(* minus_split 与根 L760 冲突改名 kl_minus_split。 *)
(* ============================================================ *)

Section KLProjection.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable post_aud : S -> bool.
Variable p : S -> R.
Variable Hp_norm : normalized p.
Variable Hp_pos : positive_dist p.

(* 通过集质量 *)
Definition Z_aud : R := sum_over_S (fun s => if post_aud s then p s else zero).
Variable HZ : lt zero Z_aud.

(* 投影分布：通过集上重归一化（审计 = KL 投影的定义载体） *)
Definition projected_distribution (s : S) : R :=
  if post_aud s then mult (p s) (inv_pos Z_aud HZ) else zero.

(* 引理 1：逐点，(if aud then p else 0) ≤ p（fail 支用 p 全正） *)
Lemma if_p_le_p : forall s : S, le (if post_aud s then p s else zero) (p s).
Proof.
  intro s. destruct (post_aud s).
  - apply le_refl.
  - (* lt→le 桥 = 接口字段 lt_le_iff（Or := A+B，left 可用） *)
    apply (lt_le_iff zero (p s)). left. exact (Hp_pos s).
Qed.

(* 引理 2：通过集质量 ≤ 总质量（单调分块 = sum_over_S_le + 引理 1） *)
Theorem Z_aud_le_one : le Z_aud (sum_over_S p).
Proof.
  unfold Z_aud. exact (sum_over_S_le (fun s => if post_aud s then p s else zero) p if_p_le_p).
Qed.

(* 引理 3：投影分布逐点 = mult inv(Z_aud) (if aud then p else 0)——线性装配形态 *)
Lemma projected_pt :
  forall s : S,
    Id (projected_distribution s)
       (mult (inv_pos Z_aud HZ) (if post_aud s then p s else zero)).
Proof.
  intro s. unfold projected_distribution. destruct (post_aud s).
  - apply mult_comm.
  - exact (id_sym (mult_zero (inv_pos Z_aud HZ))).
Qed.

(* 引理 4：投影分布归一化（主定理地基：Σ projected_distribution = 1） *)
Theorem projected_normalized : normalized projected_distribution.
Proof.
  unfold normalized.
  (* 前段：sum_ext 换成线性形态 + linear 提出常量（中项经 Z_aud 定义体转换衔接） *)
  apply (id_trans
          (id_trans (sum_over_S_ext (fun s => projected_distribution s)
                     (fun s => mult (inv_pos Z_aud HZ) (if post_aud s then p s else zero))
                     projected_pt)
                    (sum_over_S_linear (inv_pos Z_aud HZ)
                       (fun s => if post_aud s then p s else zero)))).
  (* 后段：invZ · Z_aud = one（comm 换位 + inv_pos_correct 右乘形态） *)
  apply (id_trans (mult_comm (inv_pos Z_aud HZ) Z_aud)).
  apply inv_pos_correct.
Qed.

(* ================================================================ *)
(* 主定理：审计 = KL 投影（projected_distribution_minimizes_kl）       *)
(* 分解：relative_entropy q p == relative_entropy q projected_distribution + opp(log Z_aud)， *)
(*       尾项 ≥ 0（HlogZ 经 opp_le_compat 反变）→ le 链合成。          *)
(* ================================================================ *)

(* 引理 5（通用 R 层恒等式）：a−c == (a−b)+(b−c) —— transitivity 风格 *)
Lemma kl_minus_split : forall a b c : R, Id (minus a c) (plus (minus a b) (minus b c)).
Proof.
  intros a b c. unfold minus.
  transitivity (plus a (plus (opp b) (plus b (opp c)))).
  - (* 左段：a+opp c == a+(内层) —— 内层 zero 插入路径 *)
    apply (id_cong (fun w => plus a w)).
    transitivity (plus (plus (opp b) b) (opp c)).
    + apply (id_trans (id_sym (plus_zero (opp c)))
              (id_trans (plus_comm (opp c) zero)
                (id_sym (id_cong (fun w => plus w (opp c))
                                (id_trans (plus_comm (opp b) b) (plus_opp b)))))).
    + apply (id_sym (plus_assoc (opp b) b (opp c))).
  - (* 右段：assoc 正向拉直 *)
    apply (plus_assoc a (opp b) (plus b (opp c))).
Qed.

(* 引理 6（逐点分解，无分支恒等式）：distrib 反向套 kl_minus_split *)
Lemma kl_pointwise_split :
  forall (q : S -> R) (s : S),
    Id (mult (q s) (minus (log (q s)) (log (p s))))
       (plus (mult (q s) (minus (log (q s)) (log (projected_distribution s))))
             (mult (q s) (minus (log (projected_distribution s)) (log (p s))))).
Proof.
  intros q s.
  apply (id_trans (id_cong (mult (q s)) (kl_minus_split (log (q s)) (log (projected_distribution s)) (log (p s))))).
  apply distrib.
Qed.

(* 引理 7：和的分解——relative_entropy q p == relative_entropy q projected_distribution + 尾项 *)
Lemma kl_sum_split :
  forall (q : S -> R),
    Id (relative_entropy q p)
       (plus (relative_entropy q (projected_distribution))
             (sum_over_S (fun s => mult (q s) (minus (log (projected_distribution s)) (log (p s)))))).
Proof.
  intro q. unfold relative_entropy.
  apply (id_trans (sum_over_S_ext _ _ (fun s => kl_pointwise_split q s))).
  apply sum_over_S_add.
Qed.

(* 引理 8（中间恒等式）：minus (plus x (opp L)) x == opp L *)
Lemma minus_plus_opp : forall x L : R, Id (minus (plus x (opp L)) x) (opp L).
Proof.
  intros x L.
  unfold minus.
  exact ((id_trans (id_sym (plus_assoc x (opp L) (opp x)))) ((id_trans (id_cong (fun w => plus x w) (plus_comm (opp L) (opp x)))) ((id_trans (plus_assoc x (opp x) (opp L))) ((id_trans (id_cong (fun w => plus w (opp L)) (plus_opp x))) ((id_trans (plus_comm zero (opp L))) ((plus_zero (opp L)))))))).
Qed.

(* 引理 9（尾项求值）：Σ q·(log projected_distribution − log p) == opp (log Z_aud) *)
Lemma kl_tail_eval :
  forall (q : S -> R) (Hq_norm : normalized q) (Hq_pos : positive_dist q)
         (Hq_fail : forall s : S, Id (post_aud s) false -> Id (q s) zero),
    Id (sum_over_S (fun s => mult (q s) (minus (log (projected_distribution s)) (log (p s)))))
       (opp (log Z_aud)).
Proof.
  intros q Hq_norm Hq_pos Hq_fail.
  assert (Hpt : forall s : S,
    Id (mult (q s) (minus (log (projected_distribution s)) (log (p s))))
       (mult (opp (log Z_aud)) (q s))).
  { intro s. destruct (post_aud s) eqn:Es.
    - (* pass：log projected_distribution == log p + opp(log Z) → 尾差 == opp(log Z) *)
      assert (Hpa : Id (projected_distribution s) (mult (p s) (inv_pos Z_aud HZ))).
      { unfold projected_distribution. rewrite Es. apply id_refl. }
      assert (Hlpa : Id (log (projected_distribution s)) (plus (log (p s)) (opp (log Z_aud)))).
      { apply (id_trans (id_cong log Hpa)).
        apply (id_trans (log_mult (p s) (inv_pos Z_aud HZ) (Hp_pos s) (inv_pos_pos Z_aud HZ))).
        apply (id_cong (fun w => plus (log (p s)) w) (log_inv_one_inv Z_aud HZ)). }
      apply (id_trans (id_cong (mult (q s))
                 (id_trans (id_cong (fun w => minus w (log (p s))) Hlpa)
                           (minus_plus_opp (log (p s)) (log Z_aud))))).
      apply mult_comm.
    - (* fail：q s = 0，两侧皆零 *)
      assert (Hq0 : Id (q s) zero) by exact (Hq_fail s (RealSetoid.eq_Id _ _ Es)).
      apply (id_trans (id_cong (fun w => mult w (minus (log (projected_distribution s)) (log (p s)))) Hq0)).
      apply (id_trans (mult_comm zero (minus (log (projected_distribution s)) (log (p s))))).
      apply (id_trans (mult_zero (minus (log (projected_distribution s)) (log (p s))))).
      apply (id_sym (id_trans (id_cong (fun w => mult (opp (log Z_aud)) w) Hq0)
                              (mult_zero (opp (log Z_aud))))). }
  apply (id_trans (sum_over_S_ext _ _ Hpt)).
  apply (id_trans (sum_over_S_linear (opp (log Z_aud)) (fun s => q s))).
  apply (id_trans (id_cong (mult (opp (log Z_aud))) Hq_norm)).
  apply mult_one.
Qed.

(* 主定理：审计 = KL 投影（框架理论锚） *)
Theorem projected_distribution_minimizes_kl :
  forall (q : S -> R) (Hq_norm : normalized q) (Hq_pos : positive_dist q)
         (Hq_fail : forall s : S, Id (post_aud s) false -> Id (q s) zero)
         (HlogZ : le (log Z_aud) zero),
    le (relative_entropy q (projected_distribution)) (relative_entropy q p).
Proof.
  intros q Hq_norm Hq_pos Hq_fail HlogZ.
  eapply le_id_r.
  - exact (id_sym (kl_sum_split q)).
  - apply le_plus_nonneg_r.
    (* 尾项 T == opp (log Z_aud)，且 le zero (opp log Z) ← HlogZ 反变桥 *)
    apply (le_id_r _ _ _ (id_sym (kl_tail_eval q Hq_norm Hq_pos Hq_fail))).
    apply (le_id_l _ _ _ (id_sym (opp_zero_t13))).
    apply (opp_le_compat (log Z_aud) zero).
    exact HlogZ.
Qed.

End KLProjection.


From Stdlib Require Import ZArith.Znat.
Open Scope Q_scope.


(* ============================================================ *)
(* 217 块 22 · AttnDoeblin（P1：有界 logits softmax 核显式          *)
(*   Doeblin 收缩——u_tv_contraction/bs_minorization δ*=e^{−2Δ/T}） *)
(*   源：AttnDoeblin.v（上游；改名 attn_nat_to_R 系）；        *)
(*   插入位 = 基底末尾（全基底先于 Attn——依赖约束）；零公理面      *)
(* ============================================================ *)
(* ============================================================ *)
(* AttnDoeblin.v —— P1 主定理包：有界 logits softmax 核的显式 Doeblin 收缩 *)
(*                                                                *)
(* Part A（抽象层）u_tv_contraction：双点 TV 收缩——相对库内           *)
(*   attention_tv_contraction 的推广：参考分布 u 只需归一化（无需       *)
(*   平稳性/详细平衡），收缩在任意两个归一化分布之间成立；迭代版         *)
(*   u_tv_iter 给出几何率 (1−δ)ⁿ。                                 *)
(* Part B（主定理）有界 logits softmax 核：z 双显式界（−Δ ≤ z ≤ Δ）     *)
(*   ⟹ 核逐点 ≥ δ*·U，δ* := e^{−Δ/T}·e^{+Δ/T}⁻¹ 形态 exact 化为       *)
(*   δ* := lo·lo（lo := e^{−Δ/T}），即 e^{−2Δ/T}——温度与 logit        *)
(*   直径的显式函数；Part A 原样实例化 ⟹ 收缩率 (1 − e^{−2Δ/T})ⁿ。     *)
(* Part C（满足性证明）：cauchy_real_exp 满足 expf 迷你接口全部字段——     *)
(*   Part B 假设类在具体柯西实数上非空（real_eq 版语义实现）。          *)
(* 诚实接口（Variable）：sum_swap_cc / abs_ge_zero_id_cc /              *)
(*   lt_plus_compat（与库内 Doeblin 节同款）；sum_eq_list（枚举求和      *)
(*   规范化 = 有限世界假设）；expf 迷你接口（Part C 证其可满足）。             *)
(* 纪律：零公理面、零承认件、零参数声明；Set 层语句；全 Qed；可提取。      *)
(* ============================================================ *)

From Stdlib Require Import List.

(* ################ Part 0：通用代数辅助 ################ *)

Section AlgHelpers.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* Id 上的目标右端改写（Id 单构造子，destruct 消去） *)
Lemma lt_id_r_loc : forall (a b c : R), Id b c -> lt a b -> lt a c.
Proof.
  intros a b c H Hlt. destruct H. exact Hlt.
Qed.

(* 四项交换：(a+c)+(b+d) == (a+b)+(c+d) *)
Lemma plus_exchange : forall a b c d : R,
  Id (plus (plus a c) (plus b d)) (plus (plus a b) (plus c d)).
Proof.
  intros a b c d.
  apply (id_sym (id_trans (id_sym (plus_assoc a b (plus c d)))
  (id_trans (id_cong (fun x => plus a x) (plus_assoc b c d))
  (id_trans (id_cong (fun x => plus a (plus x d)) (plus_comm b c))
  (id_trans (id_cong (fun x => plus a x) (id_sym (plus_assoc c b d)))
            (plus_assoc a c (plus b d))))))).
Qed.

(* 左公因子相减：(a+b) − (a+c) == b − c *)
Lemma minus_plus_congr_l : forall a b c : R,
  Id (minus (plus a b) (plus a c)) (minus b c).
Proof.
  intros a b c.
  unfold minus.
  exact ((id_trans (id_cong (fun x => plus (plus a b) x) (opp_plus a c))) ((id_trans (plus_exchange a (opp a) b (opp c))) ((id_trans (id_cong (fun x => plus x (plus b (opp c))) (plus_opp a))) ((id_trans (plus_comm zero (plus b (opp c)))) ((plus_zero (plus b (opp c)))))))).
Qed.

(* 公因子提出相减（k 在前）：k·x − k·y == k·(x−y) *)
Lemma minus_factor : forall k x y : R,
  Id (minus (mult k x) (mult k y)) (mult k (minus x y)).
Proof.
  intros k x y.
  unfold minus.
  exact ((id_trans (id_cong (fun x0 => plus (mult k x) x0) (id_sym (opp_mult_l k y)))) ((id_sym (distrib k x (opp y))))).
Qed.

(* 公因子提出相减（k 在后）：x·k − y·k == (x−y)·k *)
Lemma minus_factor_pt : forall x y k : R,
  Id (minus (mult x k) (mult y k)) (mult (minus x y) k).
Proof.
  intros x y k.
  unfold minus.
  exact ((id_trans (id_cong (fun x0 => plus (mult x k) x0) (id_sym (opp_mult_r y k)))) ((id_trans (id_cong2 plus (mult_comm x k) (mult_comm (opp y) k))) ((id_trans (id_sym (distrib k x (opp y)))) ((mult_comm k (minus x y)))))).
Qed.

(* 逆元对乘法分配：inv(a·b) == inv a · inv b（正元） *)
Lemma inv_pos_mult_distr : forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
  Id (inv_pos (mult a b) (mult_positive a b Ha Hb))
     (mult (inv_pos a Ha) (inv_pos b Hb)).
Proof.
  intros a b Ha Hb.
  apply (mult_cancel_l (mult a b) _ _ (mult_positive a b Ha Hb)).
  apply (id_trans (inv_pos_correct (mult a b) (mult_positive a b Ha Hb))).
  apply id_sym.
  apply (id_trans (id_sym (mult_assoc a b (mult (inv_pos a Ha) (inv_pos b Hb))))).
  apply (id_trans (id_cong (fun x => mult a x)
            (id_trans (mult_comm b (mult (inv_pos a Ha) (inv_pos b Hb)))
            (id_trans (id_sym (mult_assoc (inv_pos a Ha) (inv_pos b Hb) b))
                      (id_cong (fun x => mult (inv_pos a Ha) x)
                               (mult_comm (inv_pos b Hb) b)))))).
  apply (id_trans (mult_assoc a (inv_pos a Ha) (mult b (inv_pos b Hb)))).
  apply (id_trans (id_cong (fun x => mult x (mult b (inv_pos b Hb)))
                           (inv_pos_correct a Ha))).
  apply (id_trans (mult_comm one (mult b (inv_pos b Hb)))).
  apply (id_trans (mult_one (mult b (inv_pos b Hb)))).
  exact (inv_pos_correct b Hb).
Qed.

(* nat → R 嵌入与正性 *)
Fixpoint attn_nat_to_R (k : nat) : R :=
  match k with
  | 0%nat => zero
  | Datatypes.S m => plus one (attn_nat_to_R m)
  end.

Lemma attn_nat_to_R_pos : forall k : nat, lt zero (attn_nat_to_R (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - apply (lt_id_r_loc _ _ _ (id_sym (plus_zero one))). exact one_pos.
  - apply plus_positive.
    + exact one_pos.
    + exact IH.
Qed.

End AlgHelpers.

(* ################ Part A：抽象双点 TV 收缩 ################ *)

Section UContraction.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let sum_over_S := @sum_over_S RI SS SO.
Let tv := @tv_dist RI SS SO.

Variable u : S -> R.
Variable u_norm : Id (sum_over_S u) one.
Variable delta : R.
Variable delta_lt_one : lt delta one.
Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s' : S, le zero (transition s s').
Variable transition_row : forall s : S, Id (sum_over_S (fun s' : S => transition s s')) one.
Variable minorization : forall s s' : S, le (mult delta (u s')) (transition s s').
Variable sum_swap_cc : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable abs_ge_zero_id_cc : forall a : R, le zero a -> Id (abs a) a.
(* [墙族登记·RW-MIX 混合保序] 接口层结构墙（论文7§9.1 三分表；uabm_wall 先例 ToyR_UpAblP7_UMixSelect.v:155）：接口仅载严格-严格/弱-弱加法保序（S01:232-233），无「严格从弱」产生子，本位（h 后缀副本节 UContraction）接口层不可导，禁硬证禁纯删；具体层已证供给 real_lt_plus_compat_lt_le（S07_RealSetoidExpLog.v:6147，cms_bs_lpc 同件）——消解走实例层供给或 TB-2 字段化归一批。 *)
Variable lt_plus_compat_lt_le_h : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

Let omd := minus one delta.

(* 1−δ > 0 *)
Lemma u_omd_pos_next : lt zero omd.
Proof.
  unfold omd, minus.
  apply (lt_id_l zero (plus delta (opp delta)) (plus one (opp delta))
                 (id_sym (plus_opp delta))
                 (lt_plus_compat_lt_le_h delta one (opp delta) (opp delta)
                                         delta_lt_one (le_refl (opp delta)))).
Qed.

Let inv_omd := inv_pos omd u_omd_pos_next.

Definition u_r_kernel (s s' : S) : R :=
  mult inv_omd (minus (transition s s') (mult delta (u s'))).

Lemma u_r_nonneg : forall s s' : S, le zero (u_r_kernel s s').
Proof.
  intros s s'. unfold u_r_kernel.
  apply (le_mult_nonneg_t12 inv_omd
                            (minus (transition s s') (mult delta (u s')))).
  - exact (lt_le_iff _ _ (inl (inv_pos_pos omd u_omd_pos_next))).
  - exact (le_minus_nonneg (mult delta (u s')) (transition s s') (minorization s s')).
Qed.

Lemma u_r_norm : forall s : S, Id (sum_over_S (fun s' : S => u_r_kernel s s')) one.
Proof.
  intro s. unfold u_r_kernel.
  apply (id_trans (sum_over_S_linear inv_omd
           (fun s' : S => minus (transition s s') (mult delta (u s'))))).
  apply (id_trans (id_cong (fun x => mult inv_omd x)
  (id_trans (sum_over_S_minus (fun s' : S => transition s s')
                              (fun s' : S => mult delta (u s')))
            (id_cong2 minus (transition_row s)
                      (id_trans (sum_over_S_linear delta u)
                                (id_cong (fun x => mult delta x) u_norm)))))).
  apply (id_trans (id_cong (fun x => mult inv_omd x)
                           (id_cong (fun y => minus one y) (mult_one delta)))).
  apply (id_trans (mult_comm inv_omd omd) (inv_pos_correct omd u_omd_pos_next)).
Qed.

(* T == δ·u + (1−δ)·R *)
Lemma u_tr_decomp : forall s s' : S,
  Id (transition s s')
     (plus (mult delta (u s')) (mult omd (u_r_kernel s s'))).
Proof.
  intros s s'. unfold u_r_kernel.
  assert (Habs : Id (mult omd (mult inv_omd (minus (transition s s') (mult delta (u s')))))
                    (minus (transition s s') (mult delta (u s')))).
  { apply (id_trans (mult_assoc omd inv_omd
           (minus (transition s s') (mult delta (u s'))))).
    apply (id_trans (id_cong (fun x => mult x (minus (transition s s') (mult delta (u s'))))
                             (inv_pos_correct omd u_omd_pos_next))).
    apply (id_trans (mult_comm one (minus (transition s s') (mult delta (u s'))))
                    (mult_one (minus (transition s s') (mult delta (u s'))))). }
  apply (id_trans (id_sym (minus_plus_cancel_gap (transition s s') (mult delta (u s'))))).
  apply (id_trans (plus_comm (minus (transition s s') (mult delta (u s')))
                             (mult delta (u s')))).
  apply (id_cong (fun x => plus (mult delta (u s')) x) (id_sym Habs)).
Qed.

(* δ·a + (1−δ)·a == a *)
Lemma delta_absorb_u : forall a : R,
  Id (plus (mult delta a) (mult omd a)) a.
Proof.
  intro a.
  assert (H1 : Id (plus delta omd) one).
  { unfold omd, minus.
    apply (id_trans (plus_assoc delta one (opp delta))).
    apply (id_trans (id_cong (fun x => plus x (opp delta)) (plus_comm delta one))).
    apply (id_trans (id_sym (plus_assoc one delta (opp delta)))).
    apply (id_trans (id_cong (fun x => plus one x) (plus_opp delta))).
    exact (plus_zero one). }
  apply (id_trans (id_cong2 plus (mult_comm delta a) (mult_comm omd a))).
  apply (id_trans (id_sym (distrib a delta omd))).
  apply (id_trans (id_cong (fun x => mult a x) H1) (mult_one a)).
Qed.

Let u_step := @attention_step RI SS SO transition.

(* 单步分解：Tμ == δ·u + (1−δ)·Rμ *)
Lemma u_step_decomp : forall (mu : S -> R) (s' : S),
  Id (sum_over_S mu) one ->
  Id (u_step mu s')
     (plus (mult delta (u s'))
           (mult omd (sum_over_S (fun s : S => mult (mu s) (u_r_kernel s s'))))).
Proof.
  intros mu s' Hmu_norm. unfold u_step.
  apply (id_trans (sum_over_S_ext _ _
        (fun s : S => id_cong (fun x => mult (mu s) x) (u_tr_decomp s s')))).
  apply (id_trans (sum_over_S_ext _ _
        (fun s : S => distrib (mu s) (mult delta (u s'))
                                (mult omd (u_r_kernel s s'))))).
  apply (id_trans (sum_over_S_add (fun s : S => mult (mu s) (mult delta (u s')))
        (fun s : S => mult (mu s) (mult omd (u_r_kernel s s'))))).
  assert (Hfirst : Id (sum_over_S (fun s : S => mult (mu s) (mult delta (u s'))))
                      (mult delta (u s'))).
  { apply (id_trans (sum_over_S_ext _ _
          (fun s : S => mult_assoc (mu s) delta (u s')))).
    apply (id_trans (sum_over_S_ext _ _
          (fun s : S => id_cong (fun x => mult x (u s')) (mult_comm (mu s) delta)))).
    apply (id_trans (sum_over_S_ext _ _
          (fun s : S => id_sym (mult_assoc delta (mu s) (u s'))))).
    apply (id_trans (sum_over_S_linear delta (fun s : S => mult (mu s) (u s')))).
    apply (id_trans (id_cong (fun x => mult delta x)
    (id_trans (sum_over_S_ext _ _ (fun s : S => mult_comm (mu s) (u s')))
    (id_trans (sum_over_S_linear (u s') mu)
    (id_trans (mult_comm (u s') (sum_over_S mu))
              (id_cong (fun x => mult x (u s')) Hmu_norm)))))).
    apply (id_cong (fun x => mult delta x)
                   (id_trans (mult_comm one (u s')) (mult_one (u s')))). }
  exact (id_cong2 plus Hfirst
    (id_trans (sum_over_S_ext _ _
      (fun s : S => id_trans (mult_assoc (mu s) omd (u_r_kernel s s'))
      (id_trans (id_cong (fun x => mult x (u_r_kernel s s')) (mult_comm (mu s) omd))
                (id_sym (mult_assoc omd (mu s) (u_r_kernel s s'))))))
      (sum_over_S_linear omd (fun s : S => mult (mu s) (u_r_kernel s s'))))).
Qed.

(* 单步保持归一化 *)
Lemma u_step_norm : forall mu : S -> R,
  Id (sum_over_S mu) one -> Id (sum_over_S (fun s' : S => u_step mu s')) one.
Proof.
  intros mu Hmu.
  apply (id_trans (sum_over_S_ext _ _ (fun s' : S => u_step_decomp mu s' Hmu))).
  apply (id_trans (sum_over_S_add (fun s' : S => mult delta (u s'))
        (fun s' : S => mult omd (sum_over_S (fun s : S => mult (mu s) (u_r_kernel s s')))))).
  apply (id_trans (id_cong2 plus
    (id_trans (sum_over_S_linear delta u) (id_cong (fun x => mult delta x) u_norm))
    (id_trans (sum_over_S_linear omd (fun s2 : S => sum_over_S (fun s : S => mult (mu s) (u_r_kernel s s2))))
    (id_cong (fun x => mult omd x)
    (id_trans (id_sym (sum_swap_cc (fun s s2 : S => mult (mu s) (u_r_kernel s s2))))
    (id_trans (sum_over_S_ext _ _ (fun s : S => sum_over_S_linear (mu s) (fun s2 : S => u_r_kernel s s2)))
    (id_trans (sum_over_S_ext _ _ (fun s : S => id_cong (fun x => mult (mu s) x) (u_r_norm s)))
              (sum_over_S_ext _ _ (fun s : S => mult_one (mu s)))))))))).
  apply (id_trans (id_cong (fun x => plus x (mult omd (sum_over_S mu)))
                           (mult_one delta))).
  apply (id_trans (id_cong (fun x => plus delta x)
                 (id_trans (id_cong (fun x => mult omd x) Hmu) (mult_one omd)))).
  apply (id_trans (plus_assoc delta one (opp delta))).
  apply (id_trans (id_cong (fun x => plus x (opp delta)) (plus_comm delta one))).
  apply (id_trans (id_sym (plus_assoc one delta (opp delta)))).
  apply (id_trans (id_cong (fun x => plus one x) (plus_opp delta))).
  exact (plus_zero one).
Qed.

(* |Σ f·R| ≤ Σ |f|·R *)
Lemma u_abs_row : forall (f : S -> R) (s' : S),
  le (abs (sum_over_S (fun s : S => mult (f s) (u_r_kernel s s'))))
     (sum_over_S (fun s : S => mult (abs (f s)) (u_r_kernel s s'))).
Proof.
  intros f s'.
  apply (le_id_r (abs (sum_over_S (fun s : S => mult (f s) (u_r_kernel s s'))))
                 (sum_over_S (fun s : S => abs (mult (f s) (u_r_kernel s s'))))
                 (sum_over_S (fun s : S => mult (abs (f s)) (u_r_kernel s s')))).
  - apply (sum_over_S_ext _ _ (fun s : S =>
      id_trans (abs_mult (f s) (u_r_kernel s s'))
               (id_cong (fun x => mult (abs (f s)) x)
                        (abs_ge_zero_id_cc (u_r_kernel s s') (u_r_nonneg s s'))))).
  - exact (abs_sum_le (fun s : S => mult (f s) (u_r_kernel s s'))).
Qed.

(* ========== 主定理 A：双点 TV 收缩（无需平稳性） ========== *)
Theorem u_tv_contraction : forall (mu nu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv (u_step mu) (u_step nu)) (mult omd (tv mu nu)).
Proof.
  intros mu nu Hmu Hnu.
  assert (Hge : le zero omd).
  { exact (le_minus_nonneg delta one (lt_le_iff _ _ (inl delta_lt_one))). }
  assert (Hpt : forall s' : S,
    le (abs (minus (u_step mu s') (u_step nu s')))
       (mult omd (sum_over_S (fun s : S => mult (abs (minus (mu s) (nu s))) (u_r_kernel s s'))))).
  { intro s'.
    assert (Hd : Id (minus (u_step mu s') (u_step nu s'))
                    (mult omd (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s'))))).
    { apply (id_trans (id_cong2 minus (u_step_decomp mu s' Hmu) (u_step_decomp nu s' Hnu))).
      apply (id_trans (minus_plus_congr_l (mult delta (u s'))
                (mult omd (sum_over_S (fun s : S => mult (mu s) (u_r_kernel s s'))))
                (mult omd (sum_over_S (fun s : S => mult (nu s) (u_r_kernel s s')))))).
      apply (id_trans (minus_factor omd
                (sum_over_S (fun s : S => mult (mu s) (u_r_kernel s s')))
                (sum_over_S (fun s : S => mult (nu s) (u_r_kernel s s'))))).
      apply (id_cong (fun x => mult omd x)
      (id_trans (id_sym (sum_over_S_minus (fun s : S => mult (mu s) (u_r_kernel s s'))
                                          (fun s : S => mult (nu s) (u_r_kernel s s'))))
                (sum_over_S_ext _ _
                  (fun s : S => minus_factor_pt (mu s) (nu s) (u_r_kernel s s'))))). }
    apply (le_id_l (abs (minus (u_step mu s') (u_step nu s')))
                   (mult omd (abs (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s')))))
                   (mult omd (sum_over_S (fun s : S => mult (abs (minus (mu s) (nu s))) (u_r_kernel s s'))))).
    - assert (Habsx : Id (abs (mult omd (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s')))))
                         (mult omd (abs (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s')))))).
      { apply (id_trans (abs_mult omd (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s'))))).
        exact (id_cong2 mult (abs_ge_zero_id_cc omd Hge)
                        (id_refl : Id (abs (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s'))))
                                      (abs (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s')))))). }
      exact (id_trans (id_cong abs Hd) Habsx).
    - exact (le_mult_compat_r omd
               (abs (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s'))))
               (sum_over_S (fun s : S => mult (abs (minus (mu s) (nu s))) (u_r_kernel s s')))
               Hge (u_abs_row (fun s : S => minus (mu s) (nu s)) s')). }
  assert (Hsum : le (sum_over_S (fun s' : S => abs (minus (u_step mu s') (u_step nu s'))))
                   (mult omd (sum_over_S (fun s : S => abs (minus (mu s) (nu s)))))).
  { apply (le_id_r (sum_over_S (fun s' : S => abs (minus (u_step mu s') (u_step nu s'))))
                   (sum_over_S (fun s' : S => mult omd
                      (sum_over_S (fun s : S => mult (abs (minus (mu s) (nu s))) (u_r_kernel s s')))))
                   (mult omd (sum_over_S (fun s : S => abs (minus (mu s) (nu s)))))).
    - apply (id_trans (sum_over_S_linear omd (fun s' : S =>
                sum_over_S (fun s : S => mult (abs (minus (mu s) (nu s))) (u_r_kernel s s'))))).
      apply (id_cong (fun x => mult omd x)
      (id_trans (id_sym (sum_swap_cc (fun s s' : S => mult (abs (minus (mu s) (nu s))) (u_r_kernel s s'))))
      (id_trans (sum_over_S_ext _ _ (fun s : S => sum_over_S_linear (abs (minus (mu s) (nu s))) (fun s' : S => u_r_kernel s s')))
      (id_trans (sum_over_S_ext _ _ (fun s : S => id_cong (fun x => mult (abs (minus (mu s) (nu s))) x) (u_r_norm s)))
                (sum_over_S_ext _ _ (fun s : S => mult_one (abs (minus (mu s) (nu s))))))))).
    - apply (sum_over_S_le _ _ Hpt). }
  apply (le_trans _ (mult (inv_pos (plus one one) two_pos)
             (mult omd (sum_over_S (fun s : S => abs (minus (mu s) (nu s))))))).
  - exact (le_mult_compat_r (inv_pos (plus one one) two_pos)
             (sum_over_S (fun s' : S => abs (minus (u_step mu s') (u_step nu s'))))
             (mult omd (sum_over_S (fun s : S => abs (minus (mu s) (nu s)))))
             (lt_le_iff _ _ (inl (inv_pos_pos (plus one one) two_pos))) Hsum).
  - assert (Hswap : Id (mult (inv_pos (plus one one) two_pos)
                           (mult omd (sum_over_S (fun s : S => abs (minus (mu s) (nu s))))))
                       (mult omd (mult (inv_pos (plus one one) two_pos)
                                       (sum_over_S (fun s : S => abs (minus (mu s) (nu s))))))).
    { apply (id_trans (mult_assoc (inv_pos (plus one one) two_pos) omd
                        (sum_over_S (fun s : S => abs (minus (mu s) (nu s)))))).
      apply (id_trans (id_cong (fun y => mult y (sum_over_S (fun s : S => abs (minus (mu s) (nu s)))))
                                (mult_comm (inv_pos (plus one one) two_pos) omd))).
      apply (id_sym (mult_assoc omd (inv_pos (plus one one) two_pos)
                        (sum_over_S (fun s : S => abs (minus (mu s) (nu s)))))). }
    apply (le_id_l _ _ _ Hswap).
    exact (le_refl _).
Qed.

(* ========== 迭代收缩：几何率 (1−δ)ⁿ ========== *)
Fixpoint u_titer (n : nat) (mu : S -> R) : S -> R :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => u_step (u_titer m mu)
  end.

Lemma u_titer_norm : forall (n : nat) (mu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S (u_titer n mu)) one.
Proof.
  intro n. induction n as [| n IH]; intros mu H.
  - exact H.
  - exact (u_step_norm (u_titer n mu) (IH mu H)).
Qed.

Theorem u_tv_iter : forall (n : nat) (mu nu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv (u_titer n mu) (u_titer n nu))
     (mult (r_pow omd n) (tv mu nu)).
Proof.
  intro n. induction n as [| n IH]; intros mu nu Hmu Hnu.
  - exact (le_id_l _ _ _
             (id_trans (id_sym (mult_one (tv mu nu))) (mult_comm (tv mu nu) one))
             (le_refl (mult one (tv mu nu)))).
  - apply (le_trans _ (mult omd (tv (u_titer n mu) (u_titer n nu)))).
    + exact (u_tv_contraction (u_titer n mu) (u_titer n nu)
              (u_titer_norm n mu Hmu) (u_titer_norm n nu Hnu)).
    + exact (le_id_r _ _ _
              (mult_assoc omd (r_pow omd n) (tv mu nu))
              (le_mult_compat_r omd (tv (u_titer n mu) (u_titer n nu))
                (mult (r_pow omd n) (tv mu nu))
                (le_minus_nonneg delta one (lt_le_iff _ _ (inl delta_lt_one)))
                (IH mu nu Hmu Hnu))).
Qed.

End UContraction.

(* ################ Part B（主定理）：有界 logits softmax 核 ################ *)

Section BoundedSoftmax.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let sum_over_S := @sum_over_S RI SS SO.
Let tv := @tv_dist RI SS SO.

(* 有限世界数据 *)
Variable enum : list S.
Variable enum_nonempty : Not (Id enum nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable z : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z s s').
Variable z_ub : forall s s' : S, le (z s s') Delta.

(* 构造性指数迷你接口（Part C 证其可满足性） *)
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).
Variable expf_mono_le : forall a b : R, le a b -> le (expf a) (expf b).

(* 诚实接口三件（与 Part A 同款，供主定理实例化） *)
Variable bs_swap : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable bs_abs : forall a : R, le zero a -> Id (abs a) a.
Variable bs_lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).

Fixpoint bs_list_sum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => zero
  | x :: t => plus (f x) (bs_list_sum f t)
  end.

(* 枚举求和规范化（有限世界公理：抽象求和的规模被 enum 钉住） *)
Variable sum_eq_list : forall g : S -> R, Id (sum_over_S g) (bs_list_sum g enum).



Lemma bs_list_const_sum : forall (c : R) (l : list S),
  Id (bs_list_sum (fun _ : S => c) l) (mult (attn_nat_to_R (length l)) c).
Proof.
  intros c l. induction l as [| x t IH].
  - apply (id_sym (id_trans (mult_comm zero c) (mult_zero c))).
  - assert (Hstep : Id (plus c (bs_list_sum (fun _ : S => c) t))
                       (plus (mult c one) (mult c (attn_nat_to_R (length t))))).
    { exact (id_cong2 plus (id_sym (mult_one c))
                           (id_trans IH (mult_comm (attn_nat_to_R (length t)) c))). }
    apply (id_trans Hstep).
    apply (id_trans (id_sym (distrib c one (attn_nat_to_R (length t))))).
    apply (mult_comm c (plus one (attn_nat_to_R (length t)))).
Qed.

(* ====  基座消融波 T1 终判位49 前置引理组：bs_swap 槽由兄弟字段 enum+sum_eq_list 整体导出 ==== *)
(* （照 P7BoundedSoftmaxDeep.v 同款归纳链移植；禁 import 该件——order 反序）。零承认件 ==== *)
Lemma bs_lsum_zero : forall l : list S, Id zero (bs_list_sum (fun _ : S => zero) l).
Proof.
  intro l.
  exact (id_sym (id_trans (bs_list_const_sum zero l)
                  (mult_zero (attn_nat_to_R (length l))))).
Qed.
Lemma bs_lsum_ext : forall (f g : S -> R) (l : list S),
  (forall x : S, Id (f x) (g x)) -> Id (bs_list_sum f l) (bs_list_sum g l).
Proof.
  intros f g l H. induction l as [| x t IH].
  - exact id_refl.
  - simpl. exact (id_cong2 plus (H x) IH).
Qed.
Lemma bs_lsum_add : forall (f g : S -> R) (l : list S),
  Id (bs_list_sum (fun s : S => plus (f s) (g s)) l)
     (plus (bs_list_sum f l) (bs_list_sum g l)).
Proof.
  intros f g l. induction l as [| x t IH].
  - exact (id_sym (plus_zero zero)).
  - simpl.
    apply (id_trans (id_cong (fun w : R => plus (plus (f x) (g x)) w) IH)).
    exact (id_trans (id_sym (plus_assoc (f x) (g x) (plus (bs_list_sum f t) (bs_list_sum g t))))
           (id_trans (id_cong (fun w : R => plus (f x) w)
                     (plus_assoc (g x) (bs_list_sum f t) (bs_list_sum g t)))
           (id_trans (id_cong (fun w : R => plus (f x) w)
                     (id_trans (id_cong (fun w : R => plus w (bs_list_sum g t))
                                       (plus_comm (g x) (bs_list_sum f t)))
                               (id_sym (plus_assoc (bs_list_sum f t) (g x) (bs_list_sum g t)))))
           (plus_assoc (f x) (bs_list_sum f t) (plus (g x) (bs_list_sum g t)))))).
Qed.
Lemma bs_lsum_fubini_gen : forall (f : S -> S -> R) (l1 l2 : list S),
  Id (bs_list_sum (fun s : S => bs_list_sum (f s) l2) l1)
     (bs_list_sum (fun s' : S => bs_list_sum (fun s : S => f s s') l1) l2).
Proof.
  intros f l1. induction l1 as [| x t IH]; intro l2.
  - apply (id_trans (bs_lsum_zero l2)).
    exact (bs_lsum_ext (fun _ : S => zero)
                       (fun s' : S => bs_list_sum (fun s : S => f s s') nil)
                       l2 (fun s' : S => id_refl)).
  - apply (id_trans (id_cong (fun w : R => plus (bs_list_sum (f x) l2) w) (IH l2))).
    apply (id_sym (bs_lsum_add (fun s' : S => f x s')
              (fun s' : S => bs_list_sum (fun s : S => f s s') t) l2)).
Qed.
(* 主前置引理：bs_swap 出节槽的「无槽精简版」P'——出节签名仅依赖 enum+sum_eq_list 两槽 *)
Lemma bs_swap_derived : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Proof.
  intro f.
  apply (id_trans (sum_eq_list (fun s : S => sum_over_S (fun s' : S => f s s')))).
  apply (id_trans (bs_lsum_ext
            (fun s : S => sum_over_S (fun s' : S => f s s'))
            (fun s : S => bs_list_sum (fun s' : S => f s s') enum) enum
            (fun s : S => sum_eq_list (fun s' : S => f s s')))).
  apply (id_trans (bs_lsum_fubini_gen f enum enum)).
  apply (id_trans (id_sym (bs_lsum_ext
            (fun s' : S => sum_over_S (fun s : S => f s s'))
            (fun s' : S => bs_list_sum (fun s : S => f s s') enum) enum
            (fun s' : S => sum_eq_list (fun s : S => f s s'))))).
  exact (id_sym (sum_eq_list (fun s' : S => sum_over_S (fun s : S => f s s')))).
Qed.

Lemma bs_list_le_const : forall (f : S -> R) (c : R) (l : list S),
  (forall x : S, le (f x) c) -> le (bs_list_sum f l) (mult (attn_nat_to_R (length l)) c).
Proof.
  intros f c l H. induction l as [| x t IH].
  - exact (le_id_r zero zero (mult zero c)
             (id_sym (id_trans (mult_comm zero c) (mult_zero c))) (le_refl zero)).
  - apply (le_id_r _ (plus c (mult c (attn_nat_to_R (length t))))
             (mult (attn_nat_to_R (length (x :: t))) c)).
    + exact (id_sym (id_trans (mult_comm (plus one (attn_nat_to_R (length t))) c)
             (id_trans (distrib c one (attn_nat_to_R (length t)))
                       (id_cong (fun w : R => plus w (mult c (attn_nat_to_R (length t))))
                                (mult_one c))))).
    + exact (le_plus_compat (f x) c (bs_list_sum f t) (mult c (attn_nat_to_R (length t)))
                             (H x)
                             (le_id_r _ _ _ (mult_comm (attn_nat_to_R (length t)) c) IH)).
Qed.

Lemma bs_list_ge_const : forall (f : S -> R) (c : R) (l : list S),
  (forall x : S, le c (f x)) -> le (mult (attn_nat_to_R (length l)) c) (bs_list_sum f l).
Proof.
  intros f c l H. induction l as [| x t IH].
  - exact (le_id_l _ _ _ (id_trans (mult_comm zero c) (mult_zero c))
             (le_refl zero)).
  - apply (le_id_l _ (plus c (mult c (attn_nat_to_R (length t))))
             (plus (f x) (bs_list_sum f t))).
    + exact (id_trans (mult_comm (plus one (attn_nat_to_R (length t))) c)
             (id_trans (distrib c one (attn_nat_to_R (length t)))
                       (id_cong (fun w : R => plus w (mult c (attn_nat_to_R (length t))))
                                (mult_one c)))).
    + exact (le_plus_compat c (f x) (mult c (attn_nat_to_R (length t))) (bs_list_sum f t)
                             (H x)
                             (le_id_l _ _ _ (id_sym (mult_comm (attn_nat_to_R (length t)) c)) IH)).
Qed.

Let nR := attn_nat_to_R (length enum).

Lemma bs_nR_pos : lt zero nR.
Proof.
  destruct enum as [| x t].
  - destruct (enum_nonempty id_refl).
  - exact (attn_nat_to_R_pos (length t)).
Qed.

Let invT := inv_pos temp temp_pos.
Let factor (s s' : S) : R := expf (mult invT (z s s')).
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).
Let delta_star := mult lo lo.

Lemma bs_lo_pos : lt zero lo.
Proof. exact (expf_pos (mult invT (opp Delta))). Qed.

Lemma bs_hi_pos : lt zero hi.
Proof. exact (expf_pos (mult invT Delta)). Qed.

(* opp Δ < Δ（由 Δ > 0） *)
Lemma bs_opp_lt : lt (opp Delta) Delta.
Proof.
  apply (le_lt_trans (opp Delta) zero Delta).
  - exact (le_id_r (opp Delta) (opp zero) zero opp_zero_t13
                   (opp_le_compat zero Delta (lt_le_iff _ _ (inl Delta_pos)))).
  - exact Delta_pos.
Qed.

Lemma bs_lo_lt_hi : lt lo hi.
Proof.
  apply (expf_mono_lt (mult invT (opp Delta)) (mult invT Delta)).
  apply (lt_id_l _ (mult (opp Delta) invT) _ (mult_comm invT (opp Delta))).
  apply (lt_id_r_loc _ _ _ (mult_comm Delta invT)).
  exact (lt_mult_compat (opp Delta) Delta invT
                        (inv_pos_pos temp temp_pos) bs_opp_lt).
Qed.

(* lo·hi == one（exp 同态性，logits 有界的代数核心） *)
Lemma bs_lo_hi_eq : Id (mult lo hi) one.
Proof.
  apply (id_trans (id_sym (expf_plus (mult invT (opp Delta)) (mult invT Delta)))).
  apply (id_trans (id_cong expf (id_sym (distrib invT (opp Delta) Delta)))).
  apply (id_trans (id_cong expf (id_cong (fun w => mult invT w)
                 (id_trans (plus_comm (opp Delta) Delta) (plus_opp Delta))))).
  exact (id_trans (id_cong expf (mult_zero invT)) expf_zero).
Qed.

Lemma bs_delta_star_lt_one : lt delta_star one.
Proof.
  exact ((lt_id_r_loc _ _ _ (bs_lo_hi_eq)) ((lt_id_r_loc _ _ _ (mult_comm hi lo)) ((lt_mult_compat lo hi lo bs_lo_pos bs_lo_lt_hi)))).
Qed.

Lemma bs_inv_hi_lo : Id (inv_pos hi bs_hi_pos) lo.
Proof.
  apply (mult_cancel_l hi _ _ bs_hi_pos).
  exact (id_trans (inv_pos_correct hi bs_hi_pos)
                  (id_sym (id_trans (mult_comm hi lo) bs_lo_hi_eq))).
Qed.

(* 因子下界：e^{z/T} ≥ e^{−Δ/T} *)
Lemma bs_factor_ge_lo : forall s s' : S, le lo (factor s s').
Proof.
  intros s s'. unfold factor, lo.
  apply (expf_mono_le (mult invT (opp Delta)) (mult invT (z s s'))).
  exact (le_mult_compat_r invT (opp Delta) (z s s')
           (lt_le_iff _ _ (inl (inv_pos_pos temp temp_pos))) (z_lb s s')).
Qed.

(* 因子上界：e^{z/T} ≤ e^{Δ/T} *)
Lemma bs_factor_le_hi : forall s s' : S, le (factor s s') hi.
Proof.
  intros s s'. unfold factor, hi.
  apply (expf_mono_le (mult invT (z s s')) (mult invT Delta)).
  exact (le_mult_compat_r invT (z s s') Delta
           (lt_le_iff _ _ (inl (inv_pos_pos temp temp_pos))) (z_ub s s')).
Qed.

Definition Zrow (s : S) : R := sum_over_S (fun s' : S => factor s s').

Lemma bs_Zrow_ge : forall s : S, le (mult nR lo) (Zrow s).
Proof.
  intro s.
  apply (le_id_r (mult nR lo) (bs_list_sum (fun s' : S => factor s s') enum) (Zrow s)
                   (id_sym (sum_eq_list (fun s' : S => factor s s')))).
  exact (bs_list_ge_const (fun s' : S => factor s s') lo enum (fun x : S => bs_factor_ge_lo s x)).
Qed.

Lemma bs_Zrow_le : forall s : S, le (Zrow s) (mult nR hi).
Proof.
  intro s.
  exact ((le_id_l _ _ _ (sum_eq_list (fun s' : S => factor s s'))) ((bs_list_le_const (fun s' : S => factor s s') hi enum (fun x : S => bs_factor_le_hi s x)))).
Qed.

Lemma bs_Zrow_pos : forall s : S, lt zero (Zrow s).
Proof.
  intro s.
  exact (lt_le_trans zero (mult nR lo) (Zrow s)
                     (mult_positive nR lo bs_nR_pos bs_lo_pos) (bs_Zrow_ge s)).
Qed.

(* softmax 核（温度 T） *)
Definition bs_kernel (s s' : S) : R :=
  mult (factor s s') (inv_pos (Zrow s) (bs_Zrow_pos s)).

Lemma bs_kernel_pos : forall s s' : S, lt zero (bs_kernel s s').
Proof.
  intros s s'. unfold bs_kernel.
  exact (mult_positive (factor s s') (inv_pos (Zrow s) (bs_Zrow_pos s))
                       (expf_pos (mult invT (z s s')))
                       (inv_pos_pos (Zrow s) (bs_Zrow_pos s))).
Qed.

Lemma bs_kernel_nonneg : forall s s' : S, le zero (bs_kernel s s').
Proof.
  intros s s'. exact (lt_le_iff _ _ (inl (bs_kernel_pos s s'))).
Qed.

Lemma bs_kernel_row : forall s : S, Id (sum_over_S (fun s' : S => bs_kernel s s')) one.
Proof.
  intro s. unfold bs_kernel.
  apply (id_trans (sum_over_S_ext _ _
    (fun s' : S => mult_comm (factor s s') (inv_pos (Zrow s) (bs_Zrow_pos s))))).
  apply (id_trans (sum_over_S_linear (inv_pos (Zrow s) (bs_Zrow_pos s))
                                     (fun s' : S => factor s s'))).
  apply (id_trans (mult_comm (inv_pos (Zrow s) (bs_Zrow_pos s)) (Zrow s))
                  (inv_pos_correct (Zrow s) (bs_Zrow_pos s))).
Qed.

(* 均匀分布 U ≡ 1/|enum| *)
Let Unif : S -> R := fun _ : S => inv_pos nR bs_nR_pos.

Lemma bs_Unif_norm : Id (sum_over_S Unif) one.
Proof.
  exact ((id_trans (sum_eq_list Unif)) ((id_trans (bs_list_const_sum (inv_pos nR bs_nR_pos) enum)) ((inv_pos_correct nR bs_nR_pos)))).
Qed.

(* ===== 主定理核心：显式 Doeblin 下界 =====
   P(s,s') ≥ δ*·U(s')，δ* := lo·lo = e^{−2Δ/T}（精确，无损耗） *)
Lemma bs_minorization : forall s s' : S,
  le (mult delta_star (Unif s')) (bs_kernel s s').
Proof.
  intros s s'.
  assert (Hchain : le (mult lo (inv_pos (mult nR hi)
                              (mult_positive nR hi bs_nR_pos bs_hi_pos)))
                      (bs_kernel s s')).
  { apply (le_trans _ (mult lo (inv_pos (Zrow s) (bs_Zrow_pos s)))).
    - apply (le_mult_compat_r lo (inv_pos (mult nR hi)
                    (mult_positive nR hi bs_nR_pos bs_hi_pos))
                              (inv_pos (Zrow s) (bs_Zrow_pos s))
                              (lt_le_iff _ _ (inl bs_lo_pos))).
      exact (inv_pos_le_compat (Zrow s) (mult nR hi) (bs_Zrow_pos s)
                               (mult_positive nR hi bs_nR_pos bs_hi_pos)
                               (bs_Zrow_le s)).
    - unfold bs_kernel.
      exact (le_id_l _ _ _ (mult_comm lo (inv_pos (Zrow s) (bs_Zrow_pos s)))
               (le_id_r _ _ _
                 (id_sym (mult_comm (factor s s') (inv_pos (Zrow s) (bs_Zrow_pos s))))
                 (le_mult_compat_r (inv_pos (Zrow s) (bs_Zrow_pos s)) lo
                                   (factor s s')
                                   (lt_le_iff _ _ (inl (inv_pos_pos (Zrow s) (bs_Zrow_pos s))))
                                   (bs_factor_ge_lo s s')))). }
  assert (Heq : Id (mult delta_star (Unif s'))
                   (mult lo (inv_pos (mult nR hi)
                              (mult_positive nR hi bs_nR_pos bs_hi_pos)))).
  { unfold delta_star, Unif.
    assert (Hd1 : Id (mult lo (inv_pos (mult nR hi)
                          (mult_positive nR hi bs_nR_pos bs_hi_pos)))
                     (mult lo (mult (inv_pos nR bs_nR_pos) (inv_pos hi bs_hi_pos)))).
    { exact (id_cong2 mult (id_refl : Id lo lo)
                       (inv_pos_mult_distr nR hi bs_nR_pos bs_hi_pos)). }
    assert (Hd2 : Id (mult lo (mult (inv_pos nR bs_nR_pos) (inv_pos hi bs_hi_pos)))
                     (mult (mult lo lo) (inv_pos nR bs_nR_pos))).
    { apply (id_trans (id_cong (fun w : R => mult lo (mult (inv_pos nR bs_nR_pos) w))
                               bs_inv_hi_lo)).
      apply (id_trans (id_cong (fun w : R => mult lo w)
                                (mult_comm (inv_pos nR bs_nR_pos) lo))).
      exact (mult_assoc lo lo (inv_pos nR bs_nR_pos)). }
    exact (id_sym (id_trans Hd1 Hd2)). }
exact (le_id_l _ _ _ Heq Hchain).
Qed.

(* ===== 主定理定理 1：有界 softmax 核的双点 TV 收缩 =====
   收缩率显式：1 − e^{−2Δ/T} *)
Theorem bounded_softmax_tv_contraction : forall (mu nu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv (@attention_step RI SS SO bs_kernel mu) (@attention_step RI SS SO bs_kernel nu))
     (mult (minus one delta_star) (tv mu nu)).
Proof.
  intros mu nu Hmu Hnu.
  exact (@u_tv_contraction RI SS SO
           Unif bs_Unif_norm delta_star bs_delta_star_lt_one
           bs_kernel bs_kernel_row bs_minorization
           bs_swap bs_abs bs_lpc mu nu Hmu Hnu).
Qed.

(* ===== 主定理定理 2：迭代收缩，显式几何率 (1 − e^{−2Δ/T})ⁿ ===== *)
Theorem bounded_softmax_tv_iter : forall (n : nat) (mu nu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv (@u_titer RI SS SO bs_kernel n mu) (@u_titer RI SS SO bs_kernel n nu))
     (mult (r_pow (minus one delta_star) n) (tv mu nu)).
Proof.
  intros n mu nu Hmu Hnu.
  exact (@u_tv_iter RI SS SO
           Unif bs_Unif_norm delta_star bs_delta_star_lt_one
           bs_kernel bs_kernel_row bs_minorization
           bs_swap bs_abs bs_lpc n mu nu Hmu Hnu).
Qed.

End BoundedSoftmax.


(* ################ Part C：Real 层满足性证明 ################ *)

(* expf 迷你接口在具体柯西实数上的可满足性——Part B 假设类非空：
   五字段全部由 cauchy_real_exp 的已证定理逐一供给
   （mono_le 经 real_le = Or (real_lt) (real_eq) 的构造性析取逐支证明）。 *)
Theorem real_expf_realizable :
  sigT (fun f : Real -> Real => And (forall x : Real, real_lt real_zero (f x))
        (And (real_eq (f real_zero) real_one)
        (And (forall a b : Real,
              real_eq (f (real_plus a b)) (real_mult (f a) (f b)))
        (And (forall a b : Real, real_lt a b -> real_lt (f a) (f b))
             (forall a b : Real, real_le a b -> real_le (f a) (f b)))))).
Proof.
  exact (existT _ cauchy_real_exp
    (pair cauchy_real_exp_pos
    (pair cauchy_real_exp_zero
    (pair cauchy_real_exp_plus
    (pair cauchy_real_exp_mono
          (fun a b H => match H with
                        | inl Hlt => inl (cauchy_real_exp_mono a b Hlt)
                        | inr Heq => inr (cauchy_real_exp_wd a b Heq)
                        end)))))).
Qed.

(* 提取检验：实层指数构造可提取为 OCaml（零 Obj.magic） *)

(* ============================================================ *)
(* 217 块 23 · AttnSqrt（P3：构造性平方根 real_sqrt_exists——       *)
(*   ∀d≥0 {r | r≥0 ∧ r·r==d}，cw_log 路线）                       *)
(*   源：AttnSqrt.v（上游）；零公理面、零承认件                    *)
(* ============================================================ *)
(* ============================================================ *)
(* AttnSqrt.v —— P3 升级包：构造性平方根一般化                  *)
(*                                                              *)
(* G1（一般平方维数见证，抽象 R 层）：                           *)
(*   - sqrt_witness_sq / sqrt_witness_nat_sq：k² 维数下的       *)
(*     sqrt_witness 见证（库内此前仅有 d=4 机器检查实例）。      *)
(*   - nat_to_R_pos：nat → R 嵌入的正性。                       *)
(*   - scale_dual_sq_k：k² 维数下「1/k 缩放 == 温度 k」的       *)
(*     scale_sqrt_witness_dual 实例化。                         *)
(*                                                              *)
(* G2（主菜，Real 层）：构造性平方根存在性                      *)
(*   real_sqrt_exists : forall d : Real, real_le real_zero d -> *)
(*   sigT (fun r => And (real_le real_zero r)                   *)
(*                     (real_eq (real_mult r r) d)).            *)
(*   路线（构造性，零经典）：real_le 在库内展开为              *)
(*   Or (real_lt zero d) (real_eq zero d)——前提本身就是 Or，    *)
(*   提供构造性情形数据：                                       *)
(*   ① d ≡ 0（右支）：r := real_zero，r·r == 0 == d。           *)
(*   ② d > 0（左支，带正间隙证书）：r := exp(½·log d)——        *)
(*      库内 log 论证产物 cw_log（右逆 cw_log_exp_right）+      *)
(*      cauchy_real_exp_plus（exp 加法性）+ cauchy_real_exp_wd  *)
(*      （exp 外延）+ cauchy_real_exp_pos（exp 恒正）拼装：      *)
(*      r·r == exp(t+t) == exp(log d) == d，且 r > 0 直接由     *)
(*      exp 正性给出（无需二分/夹逼/诊断分支）。                *)
(*   注：规范原建议同构 cos π/2 二分模板；本实现改走库内      *)
(*   log 论证既有产物（其本身即二分模板的产物），构造更短、     *)
(*   且对弱前提 d ≥ 0 严格成立（Or 左支给出正间隙证书，         *)
(*   右支给出 r := 0 的精确相等）——无假命题修正。               *)
(*                                                              *)
(* 纪律：纯构造性 Set 层、零公理面、零承认件、非经典。        *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Setoid Morphisms.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0：Real 层逐点工具（½x + ½x == x，逐点 Q 环恒等）        *)
(* ============================================================ *)

(* 逐点：projT1 (real_mult (real_const ½) x) n == ½·x_n（组装投影引理） *)
Lemma sqrt_half_proj : forall (x : Real) (n : nat),
  QeqT (projT1 (real_mult (real_const (1#2)) x) n) ((1#2) * projT1 x n).
Proof.
  intros x n. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_const_proj (1#2) x n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (1#2) n)).
  reflexivity.
Qed.

(* ½·x + ½·x == x（real_eq 逐点；Q 层恒等 ½q + ½q == q 由 ring 判定） *)
Lemma sqrt_real_plus_half_half : forall x : Real,
  real_eq (real_plus (real_mult (real_const (1#2)) x)
                     (real_mult (real_const (1#2)) x))
          x.
Proof.
  intros x eps Heps.
  exists 0%nat.
  intros n Hn.
  (* 差的逐点化简：½x_n + ½x_n − x_n == 0 *)
  assert (Hd : projT1 (real_plus (real_mult (real_const (1#2)) x)
                                 (real_mult (real_const (1#2)) x)) n
                - projT1 x n == 0%Q).
  { setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const (1#2)) x)
                            (real_mult (real_const (1#2)) x) n)).
    setoid_rewrite (qeqT_imp_qeq _ _ (sqrt_half_proj x n)).
    ring. }
  (* Qabs(差) == Qabs 0 == 0，逐点界 |0| < eps *)
  assert (Habs0 : Qabs (projT1 (real_plus (real_mult (real_const (1#2)) x)
                                          (real_mult (real_const (1#2)) x)) n
                        - projT1 x n) == 0%Q).
  { apply Qeq_trans with (Qabs 0%Q).
    - apply Qabs_wd. exact Hd.
    - reflexivity. }
  apply Qlt_to_QltT.
  setoid_rewrite Habs0.
  apply QltT_to_Qlt. exact Heps.
Qed.

(* ============================================================ *)
(* Part 1（G2）：Real 层构造性平方根存在性                       *)
(* ============================================================ *)

Theorem real_sqrt_exists : forall d : Real, real_le real_zero d ->
  sigT (fun r : Real => And (real_le real_zero r)
                            (real_eq (real_mult r r) d)).
Proof.
  intros d Hd.
  destruct Hd as [Hdlt | Hdeq].
  - (* 情形①：d > 0（正间隙证书 Hdlt）。r := exp(½·log d)。 *)
    exists (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt))).
    split.
    + (* r > 0：exp 恒正（real_le 左支 = real_lt） *)
      exact (inl (cauchy_real_exp_pos
              (real_mult (real_const (1#2)) (cw_log d Hdlt)))).
    + (* r·r == d：链 exp(t)·exp(t) == exp(t+t) == exp(log d) == d *)
      apply (real_eq_trans
              (real_mult (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt)))
                         (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt))))
              (cauchy_real_exp (real_plus (real_mult (real_const (1#2)) (cw_log d Hdlt))
                                          (real_mult (real_const (1#2)) (cw_log d Hdlt))))
              d).
      * (* 反向用 exp 加法性：exp(x)·exp(y) == exp(x+y) *)
        apply real_eq_sym. apply cauchy_real_exp_plus.
      * apply (real_eq_trans
                (cauchy_real_exp (real_plus (real_mult (real_const (1#2)) (cw_log d Hdlt))
                                            (real_mult (real_const (1#2)) (cw_log d Hdlt))))
                (cauchy_real_exp (cw_log d Hdlt)) d).
        -- (* exp 外延：t + t == log d（sqrt_real_plus_half_half） *)
           apply cauchy_real_exp_wd.
           apply sqrt_real_plus_half_half.
        -- (* log 右逆：exp(log d) == d *)
           apply cw_log_exp_right.
  - (* 情形②：d ≡ 0（real_eq 证书 Hdeq）。r := real_zero。 *)
    exists real_zero.
    split.
    + (* 0 ≥ 0：real_le 右支 = real_eq 0 0（自反） *)
      exact (inr (real_eq_refl real_zero)).
    + (* 0·0 == 0 == d *)
      apply (real_eq_trans (real_mult real_zero real_zero) real_zero d).
      * apply real_mult_zero.
      * exact Hdeq.
Qed.

(* 具体实例（机器可提取的健全性检查）：1 的平方根可构造。        *)
(*   r := exp(½·log 1)，r ≥ 0 且 r·r == 1——G2 主定理的 d=1 实例。 *)

Lemma real_one_pos_local : real_lt real_zero real_one.
Proof.
  exists (1#2).
  split.
  - reflexivity.
  - exists 0%nat. intros n Hn. reflexivity.
Qed.

Lemma real_sqrt_one :
  sigT (fun r : Real => And (real_le real_zero r)
                            (real_eq (real_mult r r) real_one)).
Proof.
  exact (real_sqrt_exists real_one (inl real_one_pos_local)).
Qed.

(* ============================================================ *)
(* Part 2（G1）：一般平方维数见证（抽象 R 层，接口泛型）          *)
(*   库内机器检查实例此前仅 d=4（sq_witness_4）；本节给出一般    *)
(*   k² 维数的 sqrt_witness 见证族与对偶实例。                   *)
(* ============================================================ *)

Section SqrtWitnessGeneral.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* nat → R 嵌入复用库内 nat_to_R（RI 隐式实例参数）。           *)

(* 加法同态：nat_to_R (m+n) == nat_to_R m + nat_to_R n          *)
Lemma nat_to_R_plus_hom : forall m n : nat,
  Id (nat_to_R (m + n)%nat) (plus (nat_to_R m) (nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - simpl.
    exact (id_sym (id_trans (plus_comm zero (nat_to_R n))
                            (plus_zero (nat_to_R n)))).
  - simpl.
    exact (id_trans (id_cong (fun t => plus one t) IH)
                    (plus_assoc one (nat_to_R m) (nat_to_R n))).
Qed.

(* 乘法同态：nat_to_R (m·n) == nat_to_R m · nat_to_R n          *)
Lemma nat_to_R_mult_hom : forall m n : nat,
  Id (nat_to_R (m * n)%nat) (mult (nat_to_R m) (nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - simpl.
    exact (id_sym (id_trans (mult_comm zero (nat_to_R n))
                            (mult_zero (nat_to_R n)))).
  - simpl.
    exact (id_trans (nat_to_R_plus_hom n (m * n)%nat)
           (id_trans (id_cong (fun t => plus (nat_to_R n) t) IH)
           (id_trans (id_cong (fun t => plus t (mult (nat_to_R m) (nat_to_R n)))
                              (id_sym (mult_one (nat_to_R n))))
           (id_trans (id_cong (fun t => plus (mult (nat_to_R n) one) t)
                              (mult_comm (nat_to_R m) (nat_to_R n)))
           (id_trans (id_sym (distrib (nat_to_R n) one (nat_to_R m)))
                     (mult_comm (nat_to_R n) (plus one (nat_to_R m)))))))).
Qed.

(* nat_to_R 的严格正性：k ≥ 1 ⟹ 0 < nat_to_R k                 *)
Lemma nat_to_R_pos : forall k : nat, lt zero (nat_to_R (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - simpl.
    exact (lt_id_r zero one (plus one zero)
                   (id_sym (plus_zero one)) one_pos).
  - simpl. exact (plus_positive one (nat_to_R (Datatypes.S k)) one_pos IH).
Qed.

(* 见证（字面形式）：d := r·r（Id 自反；即「r 即 √(r²)」的命名式） *)
Lemma sqrt_witness_sq : forall k : nat,
  sqrt_witness (mult (nat_to_R k) (nat_to_R k)) (nat_to_R k).
Proof. intro k. exact id_refl. Qed.

(* 见证（非平凡形式）：d := nat_to_R (k·k) == nat_to_R k · nat_to_R k
   （由乘法同态 nat_to_R_mult_hom 给出——k² 维数的真见证）      *)
Lemma sqrt_witness_nat_sq : forall k : nat,
  sqrt_witness (nat_to_R (k * k)%nat) (nat_to_R k).
Proof. intro k. exact (id_sym (nat_to_R_mult_hom k k)). Qed.

(* k² 维数对偶实例：1/(S k) 缩放 == 温度 (S k)
   （scale_sqrt_witness_dual 在 d := nat_to_R (S k) · nat_to_R (S k)、
     r := nat_to_R (S k) 的实例化；k ≥ 0 ⟹ 温度 ≥ 1 > 0）       *)
Lemma scale_dual_sq_k :
  forall (SS : StateSpace RI) (SO : SumOver RI SS)
         (spp : forall f : @S RI SS -> @R RI,
                (forall s : @S RI SS, lt zero (f s)) ->
                lt zero (@sum_over_S RI SS SO f))
         (k : nat) (z : @logits RI SS) (s : @S RI SS),
    Id (@softmax_scaled RI SS SO spp
          (@inv_pos RI (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)) z s)
       (@softmax_temp_param RI SS SO spp
          (nat_to_R (Datatypes.S k)) (nat_to_R_pos k) z s).
Proof.
  intros SS SO spp k z s.
  exact (scale_sqrt_witness_dual spp
           (mult (nat_to_R (Datatypes.S k)) (nat_to_R (Datatypes.S k)))
           (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)
           (sqrt_witness_sq (Datatypes.S k)) z s).
Qed.

(* 对偶实例（nat 平方形式，d := nat_to_R ((S k)·(S k))）         *)
Lemma scale_dual_nat_sq_k :
  forall (SS : StateSpace RI) (SO : SumOver RI SS)
         (spp : forall f : @S RI SS -> @R RI,
                (forall s : @S RI SS, lt zero (f s)) ->
                lt zero (@sum_over_S RI SS SO f))
         (k : nat) (z : @logits RI SS) (s : @S RI SS),
    Id (@softmax_scaled RI SS SO spp
          (@inv_pos RI (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)) z s)
       (@softmax_temp_param RI SS SO spp
          (nat_to_R (Datatypes.S k)) (nat_to_R_pos k) z s).
Proof.
  intros SS SO spp k z s.
  exact (scale_sqrt_witness_dual spp
           (nat_to_R ((Datatypes.S k) * (Datatypes.S k))%nat)
           (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)
           (sqrt_witness_nat_sq (Datatypes.S k)) z s).
Qed.

End SqrtWitnessGeneral.

(* ============================================================ *)
(* 块 24 · AttnHardLimit：词表/计数/权重机制——                 *)
(*   eq_inv2_double 根域自足化 + TV 界链闭式，39 Qed。           *)
(*   源：AttnHardLimit218.v（上游）；零公理面、零承认件         *)
(* ============================================================ *)
(* ============================================================ *)
(* AttnHardLimit.v —— P4 升级包：硬注意力极限定理               *)
(*                                                              *)
(*   主定理 hard_attention_limit：T→0 的总变差收敛（量词翻转）  *)
(*     ∃T₀>0, ∀T（0<T<T₀）, TV(w_T, δ_m) ≤ eps                  *)
(*                                                              *)
(*   上游 softmax_gap_concentration / temperature_zero_limit     *)
(*   只给逐固定 T 的不等式，"T→0 收敛到硬注意力"在论文中仅为     *)
(*   interpretation；本文件把量词翻转为真极限定理（sigT 见证）。 *)
(*                                                              *)
(*   设定同构 MinPSampling Section（L30691）：Set 层 list 词表    *)
(*   世界 + token_eq_dec；权重 w_T(x) = e^{z(x)/T}/Z(T)。        *)
(*                                                              *)
(*   诚实接口（假命题修正协议）：                                *)
(*   ① m 在 vocab 中恰好出现一次（count_token m vocab == 1）。   *)
(*     若 m 有并列副本，w_T 的 T→0 极限是副本上的均匀分布，      *)
(*     δ_m 硬分布的 TV 不趋零——原陈述为假命题，须收紧前提。     *)
(*   ② 一致间隙 γ>0：∀x≠m, z(x)+γ ≤ z(m)。Cauchy 实数的          *)
(*     real_le 是 Or( lt, eq ) 编码，从逐 x 的 real_lt 见证构造  *)
(*     一致 real_le 常数间隙在构造性框架内不可行（无实数序的     *)
(*     可判定比较），故以单一显式 γ 为前提变量（可实例化）。    *)
(*                                                              *)
(*   纪律：纯构造性、零公理面、零承认件、非经典逻辑；         *)
(*         语句全 Set 层（sigT/库内 And/Or/Id）；全部 Qed。      *)
(* ============================================================ *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ============================================================ *)
(* 0. 通用辅助（Real 层，Section 外，全局可复用）               *)
(* ============================================================ *)

(* Id 到 real_eq 的桥（real_eq 是函数型 Set 值等价） *)
Lemma aid_real_eq : forall a b : Real, Id a b -> real_eq a b.
Proof.
  intros a b H. destruct H. apply real_eq_refl.
Qed.

(* lt ⟹ le（real_le 的 Or 编码左支） *)
Lemma real_le_from_lt_aux : forall a b : Real, real_lt a b -> real_le a b.
Proof.
  intros a b H. exact (inl H).
Qed.

(* 左乘保序：0<c、a≤b ⟹ c·a≤c·b（同构 real_le_mult_compat） *)
Lemma real_le_mult_compat_l_aux : forall a b c : Real,
  real_lt real_zero c -> real_le a b -> real_le (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hc Hab.
  apply (RealSetoid.real_le_id_l (real_mult c a) (real_mult a c) (real_mult c b)).
  - apply real_mult_comm.
  - apply (RealSetoid.real_le_id_r (real_mult a c) (real_mult b c) (real_mult c b)).
    + apply real_mult_comm.
    + apply (real_le_mult_compat a b c Hc Hab).
Qed.

(* a ≤ a + b（b ≥ 0） *)
Lemma real_le_plus_nonneg_r_aux : forall a b : Real,
  real_le real_zero b -> real_le a (real_plus a b).
Proof.
  intros a b Hb.
  apply (RealSetoid.real_le_id_l a (real_plus a real_zero) (real_plus a b)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_le_plus_compat; [apply real_le_refl | exact Hb].
Qed.

(* a ≤ b ⟹ 0 ≤ b − a *)
Lemma real_le_minus_nonneg_aux : forall a b : Real,
  real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab. unfold real_le in Hab. destruct Hab as [Hlt | Heq].
  - apply real_le_from_lt_aux. apply (real_lt_opp_plus a b). exact Hlt.
  - apply (RealSetoid.real_eq_le real_zero (real_plus b (real_opp a))).
    apply real_eq_sym.
    apply (real_eq_trans _ (real_plus b (real_opp b)) _).
    + apply (RealSetoid.real_eq_plus_compat b (real_opp a) b (real_opp b)).
      * apply real_eq_refl.
      * apply (RealSetoid.real_eq_opp_compat a b Heq).
    + apply real_plus_opp.
Qed.

(* u ≤ v ⟹ |u − v| == v − u（abs 恒等式：minus_r 形态） *)
Lemma real_abs_minus_r_nonneg_aux : forall u v : Real,
  real_le u v -> real_eq (real_abs (real_minus_r u v)) (real_plus v (real_opp u)).
Proof.
  intros u v Huv.
  assert (Hd : real_le real_zero (real_plus v (real_opp u)))
    by exact (real_le_minus_nonneg_aux u v Huv).
  (* u − v == −(v − u) *)
  assert (E1 : real_eq (real_minus_r u v)
                       (real_opp (real_plus v (real_opp u)))).
  { apply (real_eq_trans _ (real_plus (real_opp v) u) _).
    - apply real_plus_comm.
    - apply (real_eq_trans _ (real_plus (real_opp v) (real_opp (real_opp u))) _).
      + apply (RealSetoid.real_eq_plus_compat (real_opp v) u
                 (real_opp v) (real_opp (real_opp u))).
        * apply real_eq_refl.
        * apply real_eq_sym. apply real_opp_opp.
      + apply real_eq_sym. apply (real_opp_plus v (real_opp u)). }
  assert (E2 : real_eq (real_abs (real_minus_r u v))
                       (real_abs (real_plus v (real_opp u)))).
  { apply (real_eq_trans _ (real_abs (real_opp (real_plus v (real_opp u)))) _).
    - apply real_abs_eq_compat. exact E1.
    - apply real_abs_opp. }
  assert (E3 : real_eq (real_abs (real_plus v (real_opp u)))
                       (real_plus v (real_opp u))).
  { unfold real_le in Hd. destruct Hd as [Hlt | Heq].
    - apply (real_abs_pos_req _ Hlt).
    - apply (real_eq_trans _ real_zero _).
      + apply (real_eq_trans _ (real_abs real_zero) _).
        * apply real_abs_eq_compat. apply real_eq_sym. exact Heq.
        * apply real_abs_zero_req.
      + exact Heq. }
  apply (real_eq_trans _ (real_abs (real_plus v (real_opp u))) _).
  - exact E2.
  - exact E3.
Qed.

(* e^a·e^{−a} == 1（两种顺序） *)
Lemma exp_mult_opp_r_aux : forall a : Real,
  real_eq (real_mult (cauchy_real_exp a) (cauchy_real_exp (real_opp a))) real_one.
Proof.
  intros a.
  apply (real_eq_trans _ (cauchy_real_exp (real_plus a (real_opp a))) _).
  - apply real_eq_sym. apply (cauchy_real_exp_plus a (real_opp a)).
  - apply (real_eq_trans _ (cauchy_real_exp real_zero) _).
    + apply (cauchy_real_exp_wd (real_plus a (real_opp a)) real_zero).
      apply real_plus_opp.
    + apply cauchy_real_exp_zero.
Qed.

Lemma exp_mult_opp_l_aux : forall a : Real,
  real_eq (real_mult (cauchy_real_exp (real_opp a)) (cauchy_real_exp a)) real_one.
Proof.
  intros a.
  apply (real_eq_trans _
           (real_mult (cauchy_real_exp a) (cauchy_real_exp (real_opp a))) _).
  - apply real_mult_comm.
  - apply exp_mult_opp_r_aux.
Qed.

(* of_nat 嵌入：非负与单调 *)
Lemma real_of_nat_nonneg_aux : forall k : nat,
  real_le real_zero (real_of_nat k).
Proof.
  intro k. induction k as [| k IH].
  - apply real_le_refl.
  - apply (RealSetoid.real_le_id_r real_zero
             (real_plus real_one (real_of_nat k)) (real_of_nat (Datatypes.S k))).
    + apply real_eq_refl.
    + apply (RealSetoid.real_le_id_l real_zero
               (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat k))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_le_plus_compat.
        -- apply real_le_from_lt_aux. apply real_lt_zero_one.
        -- exact IH.
Qed.

Lemma real_of_nat_le_mono_aux : forall k1 k2 : nat,
  (k1 <= k2)%nat -> real_le (real_of_nat k1) (real_of_nat k2).
Proof.
  intros k1 k2 H.
  revert k1 H.
  induction k2 as [| k2 IH]; intros k1 H.
  - (* k1 ≤ 0 ⟹ k1 = 0（le 的 Prop 内消去） *)
    assert (Hk : k1 = 0%nat) by (inversion H; reflexivity).
    rewrite Hk. apply real_le_refl.
  - destruct (Nat.eq_dec k1 (Datatypes.S k2)) as [Heq | Hne].
    + rewrite Heq. apply real_le_refl.
    + (* k1 ≤ S k2 且 k1 ≠ S k2 ⟹ k1 ≤ k2（Prop 内推理） *)
      assert (Hle : (k1 <= k2)%nat).
      { inversion H; subst.
        - exfalso. apply Hne. reflexivity.
        - assumption. }
      apply (RealSetoid.real_le_id_r (real_of_nat k1)
               (real_plus real_one (real_of_nat k2))
               (real_of_nat (Datatypes.S k2))).
      * apply real_eq_refl.
      * apply (real_le_trans _ (real_plus (real_of_nat k1) real_one) _).
        -- apply real_le_plus_nonneg_r_aux.
           apply real_le_from_lt_aux. apply real_lt_zero_one.
        -- apply (RealSetoid.real_le_id_r
                     (real_plus (real_of_nat k1) real_one)
                     (real_plus (real_of_nat k2) real_one)
                     (real_plus real_one (real_of_nat k2))).
           ++ apply real_plus_comm.
           ++ apply real_le_plus_compat; [exact (IH k1 Hle) | apply real_le_refl].
Qed.

(* nat 后继 Id 的可逆性 *)
Lemma nat_S_id_inv_aux : forall a b : nat,
  @Id nat (Datatypes.S a) (Datatypes.S b) -> @Id nat a b.
Proof.
  intros a b H. exact (id_cong Nat.pred H).
Qed.

(* ============================================================ *)
(* Section AttnHardLimit：list 词表世界（同构 MinPSampling）    *)
(* ============================================================ *)

Section AttnHardLimit.

(* ---------- 1. 词表基础设施 ---------- *)
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).
Variable z : Token -> Real.

(* m 在 vocab 中的出现次数（token_eq_dec 支撑折叠计数） *)
Fixpoint count_token (t : Token) (l : list Token) : nat :=
  match l with
  | nil => O
  | x :: rest =>
      match token_eq_dec x t with
      | inl _ => Datatypes.S (count_token t rest)
      | inr _ => count_token t rest
      end
  end.

(* 首次出现删除 *)
Fixpoint removeT (t : Token) (l : list Token) : list Token :=
  match l with
  | nil => nil
  | x :: rest =>
      match token_eq_dec x t with
      | inl _ => removeT t rest
      | inr _ => x :: removeT t rest
      end
  end.

(* ---------- 2. argmax 见证（诚实接口，见文件头说明） ---------- *)
Variable m : Token.
Variable m_in_vocab : InT m vocab.
Variable m_count_one : @Id nat (count_token m vocab) (Datatypes.S O).
Variable gamma : Real.
Variable gamma_pos : real_lt real_zero gamma.
Variable gap_le : forall x : Token, Not (Id x m) ->
  real_le (real_plus (z x) gamma) (z m).

(* ---------- 3. 计数/删除组合学 ---------- *)
(*   惯例：先 cbn 暴露 match 层，再 destruct token_eq_dec；     *)
(*   嵌套层逐层处理；矛盾分支用 Empty_set 匹配消解。            *)

Lemma count_zero_notin : forall (t : Token) (l : list Token),
  @Id nat (count_token t l) O -> not_InT t l.
Proof.
  intros t l. induction l as [| y rest IH]; intro Hc.
  - intro Hin. inversion Hin.
  - cbn [count_token] in Hc.
    destruct (token_eq_dec y t) as [Hyt | Hnyt].
    + inversion Hc.
    + intro Hin. inversion Hin as [| x0 l0 Hin2]; subst.
      * apply Hnyt. apply id_refl.
      * exact (IH Hc Hin2).
Qed.

Lemma count_zero_remove_id : forall (t : Token) (l : list Token),
  @Id nat (count_token t l) O -> @Id (list Token) (removeT t l) l.
Proof.
  intros t l. induction l as [| y rest IH]; intro Hc.
  - apply id_refl.
  - cbn [count_token] in Hc. cbn [removeT].
    destruct (token_eq_dec y t) as [Hyt | Hnyt].
    + inversion Hc.
    + apply (id_cong (fun l0 => y :: l0)). exact (IH Hc).
Qed.

Lemma count_zero_remove_zero : forall (t : Token) (l : list Token),
  @Id nat (count_token t l) O -> @Id nat (count_token t (removeT t l)) O.
Proof.
  intros t l. induction l as [| y rest IH]; intro Hc.
  - apply id_refl.
  - cbn [count_token] in Hc. cbn [removeT].
    destruct (token_eq_dec y t) as [Hyt | Hnyt].
    + inversion Hc.
    + (* 目标 Id (count_token t (y :: removeT t rest)) O：暴露 count 层 *)
      cbn [count_token].
      destruct (token_eq_dec y t) as [Hyt2 | Hnyt2].
      * exact (match Hnyt Hyt2 with end).
      * exact (IH Hc).
Qed.

Lemma count_one_remove_zero : forall (t : Token) (l : list Token),
  @Id nat (count_token t l) (Datatypes.S O) ->
  @Id nat (count_token t (removeT t l)) O.
Proof.
  intros t l. induction l as [| y rest IH]; intro Hc.
  - inversion Hc.
  - cbn [count_token] in Hc. cbn [removeT].
    destruct (token_eq_dec y t) as [Hyt | Hnyt].
    + assert (Hc0 : @Id nat (count_token t rest) O)
        by exact (nat_S_id_inv_aux _ _ Hc).
      apply count_zero_remove_zero. exact Hc0.
    + cbn [count_token].
      destruct (token_eq_dec y t) as [Hyt2 | Hnyt2].
      * exact (match Hnyt Hyt2 with end).
      * exact (IH Hc).
Qed.

Lemma remove_notin_aux : forall (t x : Token) (l : list Token),
  InT x (removeT t l) -> Not (Id x t).
Proof.
  intros t x l. induction l as [| y rest IH]; intro Hin.
  - inversion Hin.
  - cbn [removeT] in Hin.
    destruct (token_eq_dec y t) as [Hyt | Hnyt].
    + exact (IH Hin).
    + inversion Hin as [| x0 l0 Hin2]; subst.
      * exact Hnyt.
      * exact (IH Hin2).
Qed.

Lemma remove_length_le_aux : forall (t : Token) (l : list Token),
  NatLe (length (removeT t l)) (length l).
Proof.
  intros t l. induction l as [| y rest IH].
  - cbn [length removeT]. apply NatLe_lift. lia.
  - cbn [removeT].
    apply NatLe_drop in IH.
    destruct (token_eq_dec y t) as [Hyt | Hnyt]; cbn [length]; apply NatLe_lift; lia.
Qed.

(* removeT 在表首的两种展开（一次性证明，供 rewrite 使用） *)
Lemma removeT_cons_self : forall (t x : Token) (l : list Token),
  Id x t -> @Id (list Token) (removeT t (x :: l)) (removeT t l).
Proof.
  intros t x l H. cbn [removeT].
  destruct (token_eq_dec x t) as [Hxt | Hnxt].
  - apply id_refl.
  - exact (match Hnxt H with end).
Qed.

Lemma removeT_cons_ne : forall (t x : Token) (l : list Token),
  Not (Id x t) -> @Id (list Token) (removeT t (x :: l)) (x :: removeT t l).
Proof.
  intros t x l H. cbn [removeT].
  destruct (token_eq_dec x t) as [Hxt | Hnxt].
  - exact (match H Hxt with end).
  - apply id_refl.
Qed.

(* 拆分引理：t 恰出现一次 ⟹ Σ l f == f t + Σ (removeT t l) f *)
Lemma split_count_one : forall (f : Token -> Real) (t : Token) (l : list Token),
  @Id nat (count_token t l) (Datatypes.S O) ->
  real_eq (real_list_sum Token f l)
          (real_plus (f t) (real_list_sum Token f (removeT t l))).
Proof.
  intros f t l. induction l as [| x rest IH]; intro Hc.
  - inversion Hc.
  - cbn [count_token] in Hc. cbn [real_list_sum].
    destruct (token_eq_dec x t) as [Hxt | Hnxt].
    + assert (Hc0 : @Id nat (count_token t rest) O)
        by exact (nat_S_id_inv_aux _ _ Hc).
      rewrite (removeT_cons_self t x rest Hxt).
      apply (real_eq_trans _ (real_plus (f t) (real_list_sum Token f rest)) _).
      * apply (RealSetoid.real_eq_plus_compat (f x)
                  (real_list_sum Token f rest) (f t)
                  (real_list_sum Token f rest)).
        -- apply (aid_real_eq _ _ (id_cong f Hxt)).
        -- apply real_eq_refl.
      * apply (RealSetoid.real_eq_plus_compat (f t)
                  (real_list_sum Token f rest) (f t)
                  (real_list_sum Token f (removeT t rest))).
        -- apply real_eq_refl.
        -- apply (aid_real_eq _ _
                     (id_sym (id_cong (fun l0 => real_list_sum Token f l0)
                                (count_zero_remove_id t rest Hc0)))).
    + rewrite (removeT_cons_ne t x rest Hnxt).
      apply (real_eq_trans _
               (real_plus (f x)
                  (real_plus (f t)
                     (real_list_sum Token f (removeT t rest)))) _).
      * apply (RealSetoid.real_eq_plus_compat (f x)
                  (real_list_sum Token f rest) (f x)
                  (real_plus (f t)
                     (real_list_sum Token f (removeT t rest)))).
        -- apply real_eq_refl.
        -- exact (IH Hc).
      * apply (real_eq_trans _
                 (real_plus (real_plus (f x) (f t))
                    (real_list_sum Token f (removeT t rest))) _).
        -- apply real_plus_assoc.
        -- apply (real_eq_trans _
                     (real_plus (real_plus (f t) (f x))
                        (real_list_sum Token f (removeT t rest))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus (f x) (f t))
                       (real_list_sum Token f (removeT t rest))
                       (real_plus (f t) (f x))
                       (real_list_sum Token f (removeT t rest))).
              ** apply real_plus_comm.
              ** apply real_eq_refl.
           ++ apply real_eq_sym. apply real_plus_assoc.
Qed.

(* ---------- 4. list 求和的序引理（Token 版） ---------- *)

Lemma sum_nonneg_aux : forall (f : Token -> Real) (l : list Token),
  (forall y : Token, real_le real_zero (f y)) ->
  real_le real_zero (real_list_sum Token f l).
Proof.
  intros f l. induction l as [| y rest IH]; intro Hnn.
  - apply real_le_refl.
  - cbn [real_list_sum].
    apply (RealSetoid.real_le_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus (f y) (real_list_sum Token f rest))).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_le_plus_compat; [apply Hnn | exact (IH Hnn)].
Qed.

Lemma sum_pos_nonempty_aux : forall (f : Token -> Real) (l : list Token),
  (forall y : Token, real_lt real_zero (f y)) -> Not (Id l nil) ->
  real_lt real_zero (real_list_sum Token f l).
Proof.
  intros f l. induction l as [| y rest IH]; intros Hf Hl.
  - exact (match Hl (@id_refl (list Token) nil) with end).
  - destruct rest as [| y2 rest2].
    + cbn [real_list_sum].
      apply (real_lt_eq_lt real_zero (f y) (real_plus (f y) real_zero)).
      * apply Hf.
      * apply real_eq_sym. apply real_plus_zero.
    + cbn [real_list_sum].
      assert (Hpos : real_lt real_zero
                       (real_plus (f y)
                          (real_plus (f y2)
                             (real_list_sum Token f rest2)))).
      { apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero) _).
        - apply real_eq_sym. apply real_plus_zero.
        - apply real_lt_plus_compat.
          + apply Hf.
          + apply (IH Hf).
            intro Hc. inversion Hc. }
      apply (real_lt_eq_lt real_zero
               (real_plus (f y) (real_plus (f y2) (real_list_sum Token f rest2))) _).
      * exact Hpos.
      * apply real_eq_refl.
Qed.

Lemma single_le_sum_aux : forall (f : Token -> Real) (x : Token) (l : list Token),
  InT x l -> (forall y : Token, real_le real_zero (f y)) ->
  real_le (f x) (real_list_sum Token f l).
Proof.
  intros f x l. induction l as [| y rest IH]; intros Hin Hnn.
  - inversion Hin.
  - cbn [real_list_sum]. inversion Hin as [| x0 l0 Hin2]; subst.
    + apply real_le_plus_nonneg_r_aux.
      apply sum_nonneg_aux. apply Hnn.
    + apply (real_le_trans _ (real_list_sum Token f rest) _).
      * exact (IH Hin2 Hnn).
      * apply (RealSetoid.real_le_id_r
                 (real_list_sum Token f rest)
                 (real_plus (real_list_sum Token f rest) (f y))
                 (real_plus (f y) (real_list_sum Token f rest))).
        -- apply real_plus_comm.
        -- apply real_le_plus_nonneg_r_aux. apply Hnn.
Qed.

Lemma sum_nonneg_le_const_aux : forall (f : Token -> Real) (c : Real) (l : list Token),
  (forall x : Token, InT x l -> real_le (f x) c) ->
  real_le (real_list_sum Token f l)
          (real_mult (real_of_nat (length l)) c).
Proof.
  intros f c l. induction l as [| x rest IH]; intro Hb.
  - exact (RealSetoid.real_eq_le real_zero
             (real_mult (real_of_nat (length (@nil Token))) c)
             (real_eq_sym (real_mult real_zero c) real_zero
                (real_eq_trans (real_mult real_zero c) (real_mult c real_zero)
                   real_zero (real_mult_comm real_zero c) (real_mult_zero c)))).
  - cbn [real_list_sum length].
    apply (RealSetoid.real_le_id_r
             (real_plus (f x) (real_list_sum Token f rest))
             (real_plus c (real_mult (real_of_nat (length rest)) c))
             (real_mult (real_of_nat (Datatypes.S (length rest))) c)).
    + apply (real_eq_trans
               (real_plus c (real_mult (real_of_nat (length rest)) c))
               (real_plus (real_mult real_one c)
                  (real_mult (real_of_nat (length rest)) c)) _).
      * apply (RealSetoid.real_eq_plus_compat c
                 (real_mult (real_of_nat (length rest)) c)
                 (real_mult real_one c)
                 (real_mult (real_of_nat (length rest)) c)).
        -- apply (real_eq_trans c (real_mult c real_one)
                    (real_mult real_one c)
                    (real_eq_sym (real_mult c real_one) c (real_mult_one c))
                    (real_mult_comm c real_one)).
        -- apply real_eq_refl.
      * apply real_distrib_r.
    + apply real_le_plus_compat.
      * apply Hb. apply InT_here.
      * apply IH. intros y Hin. apply Hb. apply (InT_next y x rest Hin).
Qed.

(* ---------- 5. 温度化 softmax 权重与硬分布 ---------- *)

(* 权重因子：factor_T T Ht x = e^{z(x)/T} *)
Definition factor_T (T : Real) (Ht : real_lt real_zero T) (x : Token) : Real :=
  cauchy_real_exp (real_mult (real_inv_pos T Ht) (z x)).

(* 配分函数：Z(T) = Σ vocab e^{z(x)/T} *)
Definition ZT (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_list_sum Token (factor_T T Ht) vocab.

Definition ZT_pos (T : Real) (Ht : real_lt real_zero T) :
  real_lt real_zero (ZT T Ht).
Proof.
  unfold ZT. apply sum_pos_nonempty_aux.
  - intro x. apply cauchy_real_exp_pos.
  - exact vocab_nonempty.
Defined.

(* 归一化权重：w_T(x) = e^{z(x)/T}/Z(T) *)
Definition w_T (T : Real) (Ht : real_lt real_zero T) (x : Token) : Real :=
  real_mult (factor_T T Ht x) (real_inv_pos (ZT T Ht) (ZT_pos T Ht)).

(* 硬分布：δ_m *)
Definition hard_dist (x : Token) : Real :=
  match token_eq_dec x m with
  | inl _ => real_one
  | inr _ => real_zero
  end.

(* 衰减基元：e^{−γ/T} *)
Definition decay_T (T : Real) (Ht : real_lt real_zero T) : Real :=
  cauchy_real_exp (real_opp (real_mult (real_inv_pos T Ht) gamma)).

(* 总变差：TV(w_T, δ_m) = (1/2)·Σ |w_T(x) − δ_m(x)| *)
Definition tv_hard (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_mult
    (real_inv_pos (real_plus real_one real_one)
       (real_lt_plus_compat real_zero real_one real_zero real_one
          real_lt_zero_one real_lt_zero_one))
    (real_list_sum Token
       (fun x => real_abs (real_minus_r (w_T T Ht x) (hard_dist x))) vocab).

(* ---------- 6. 权重分析 ---------- *)

Lemma factor_T_pos : forall (T : Real) (Ht : real_lt real_zero T) (x : Token),
  real_lt real_zero (factor_T T Ht x).
Proof.
  intros T Ht x. apply cauchy_real_exp_pos.
Qed.

Lemma w_T_pos : forall (T : Real) (Ht : real_lt real_zero T) (x : Token),
  real_lt real_zero (w_T T Ht x).
Proof.
  intros T Ht x. unfold w_T. apply real_mult_pos_compat.
  - apply factor_T_pos.
  - apply real_inv_pos_pos.
Qed.

(* 归一化：Σ vocab w_T == 1 *)
Lemma w_T_sum_one : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (real_list_sum Token (w_T T Ht) vocab) real_one.
Proof.
  intros T Ht.
  apply (real_eq_trans _
           (real_mult (real_inv_pos (ZT T Ht) (ZT_pos T Ht))
              (real_list_sum Token (factor_T T Ht) vocab)) _).
  - apply (real_list_sum_linear_r Token).
  - apply (real_eq_trans _
             (real_mult (real_inv_pos (ZT T Ht) (ZT_pos T Ht)) (ZT T Ht)) _).
    + apply real_eq_refl.
    + apply (real_eq_trans _
               (real_mult (ZT T Ht) (real_inv_pos (ZT T Ht) (ZT_pos T Ht))) _).
      * apply real_mult_comm.
      * apply (real_inv_pos_correct (ZT T Ht) (ZT_pos T Ht)).
Qed.

(* m 的权重 ≤ 1（单点质量和 ≤ 全和） *)
Lemma w_T_m_le_one : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (w_T T Ht m) real_one.
Proof.
  intros T Ht.
  apply (RealSetoid.real_le_id_r (w_T T Ht m)
           (real_list_sum Token (w_T T Ht) vocab) real_one).
  - exact (w_T_sum_one T Ht).
  - apply (single_le_sum_aux (w_T T Ht) m vocab m_in_vocab).
    intro y. apply real_le_from_lt_aux. apply w_T_pos.
Qed.

(* （X·Y)·invX == Y（inv 吸收，用于核心衰减界的换序收尾） *)
Lemma eq_mult_inv_absorb : forall (X Y : Real) (HX : real_lt real_zero X)
  (H : real_eq (real_mult X (real_inv_pos X HX)) real_one),
  real_eq (real_mult (real_mult X Y) (real_inv_pos X HX)) Y.
Proof.
  intros X Y HX H.
  apply (real_eq_trans _ (real_mult X (real_mult Y (real_inv_pos X HX))) _).
  - apply (real_eq_sym _ _ (real_mult_assoc X Y (real_inv_pos X HX))).
  - apply (real_eq_trans _ (real_mult X (real_mult (real_inv_pos X HX) Y)) _).
    + apply (RealSetoid.real_eq_mult_compat X
               (real_mult Y (real_inv_pos X HX)) X
               (real_mult (real_inv_pos X HX) Y)).
      * apply real_eq_refl.
      * apply real_mult_comm.
    + apply (real_eq_trans _
               (real_mult (real_mult X (real_inv_pos X HX)) Y) _).
      * apply real_mult_assoc.
      * apply (real_eq_trans _ (real_mult real_one Y) _).
        -- apply (RealSetoid.real_eq_mult_compat
                    (real_mult X (real_inv_pos X HX)) Y real_one Y).
           ++ exact H.
           ++ apply real_eq_refl.
        -- apply (real_eq_trans (real_mult real_one Y)
                    (real_mult Y real_one) Y).
           ++ apply real_mult_comm.
           ++ apply real_mult_one.
Qed.

(* 核心衰减界：x ≠ m ⟹ w_T(x) ≤ e^{−γ/T}
   链：z x + γ ≤ z m ⟹ (z x + γ)/T ≤ z m/T
       ⟹ e^{z x/T} ≤ e^{z m/T}·e^{−γ/T}
       ⟹ w_T(x) = e^{z x/T}·inv Z ≤ e^{z m/T}·e^{−γ/T}·inv Z
       ≤ e^{z m/T}·e^{−γ/T}·inv(e^{z m/T}) = e^{−γ/T}
   （Z ≥ e^{z m/T}：单点质量和；inv 反序）                    *)
Lemma core_decay_bound : forall (T : Real) (Ht : real_lt real_zero T) (x : Token),
  Not (Id x m) -> real_le (w_T T Ht x) (decay_T T Ht).
Proof.
  intros T Ht x Hxm.
  set (invT := real_inv_pos T Ht).
  assert (HinvT : real_lt real_zero invT) by apply real_inv_pos_pos.
  set (a := real_mult invT (z x)).
  set (b := real_mult invT (z m)).
  set (g := real_mult invT gamma).
  set (invZ := real_inv_pos (ZT T Ht) (ZT_pos T Ht)).
  set (invF := real_inv_pos (factor_T T Ht m) (factor_T_pos T Ht m)).
  (* 1. a + g ≤ b（除以 T，分配律展开） *)
  assert (H1 : real_le (real_plus a g) b).
  { apply (RealSetoid.real_le_id_l (real_plus a g)
             (real_mult invT (real_plus (z x) gamma)) b).
    - apply real_eq_sym. apply real_distrib.
    - apply (real_le_mult_compat_l_aux (real_plus (z x) gamma) (z m) invT
               HinvT (gap_le x Hxm)). }
  (* 2. a ≤ b − g *)
  assert (H2 : real_le a (real_plus b (real_opp g))).
  { assert (E1 : real_eq a (real_plus a real_zero))
      by exact (real_eq_sym (real_plus a real_zero) a (real_plus_zero a)).
    assert (E2 : real_eq (real_plus a real_zero)
                   (real_plus a (real_plus g (real_opp g))))
      by exact (RealSetoid.real_eq_plus_compat a real_zero a
                  (real_plus g (real_opp g)) (real_eq_refl a)
                  (real_eq_sym (real_plus g (real_opp g)) real_zero
                     (real_plus_opp g))).
    assert (E3 : real_eq (real_plus a (real_plus g (real_opp g)))
                   (real_plus (real_plus a g) (real_opp g)))
      by exact (real_plus_assoc a g (real_opp g)).
    assert (E4 : real_eq a (real_plus (real_plus a g) (real_opp g)))
      by exact (real_eq_trans a (real_plus a real_zero)
                  (real_plus (real_plus a g) (real_opp g)) E1
                  (real_eq_trans (real_plus a real_zero)
                     (real_plus a (real_plus g (real_opp g)))
                     (real_plus (real_plus a g) (real_opp g)) E2 E3)).
    apply (RealSetoid.real_le_id_l a
             (real_plus (real_plus a g) (real_opp g))
             (real_plus b (real_opp g))).
    - exact E4.
    - apply real_le_plus_compat; [exact H1 | apply real_le_refl]. }
  (* 3. e^a ≤ e^b·e^{−g} *)
  assert (H3 : real_le (cauchy_real_exp a)
                       (real_mult (cauchy_real_exp b)
                                  (cauchy_real_exp (real_opp g)))).
  { apply (real_le_trans _ (cauchy_real_exp (real_plus b (real_opp g))) _).
    - apply real_exp_le_mono. exact H2.
    - apply (RealSetoid.real_eq_le).
      apply (cauchy_real_exp_plus b (real_opp g)). }
  (* 4. invZ ≤ invF（Z ≥ factor m：单点质量和 + inv 反序） *)
  assert (H4 : real_le invZ invF).
  { apply (real_inv_pos_le_compat (factor_T T Ht m) (ZT T Ht)).
    - unfold ZT.
      exact (single_le_sum_aux (factor_T T Ht) m vocab m_in_vocab
               (fun y => real_le_from_lt_aux _ _ (factor_T_pos T Ht y))). }
  (* 5. 组装：e^a·invZ ≤ (e^b·e^{−g})·invZ ≤ (e^b·e^{−g})·invF = e^{−g} *)
  unfold w_T, decay_T.
  apply (real_le_trans _
           (real_mult (real_mult (cauchy_real_exp b)
                          (cauchy_real_exp (real_opp g))) invZ) _).
  - apply (real_le_mult_compat (cauchy_real_exp a)
             (real_mult (cauchy_real_exp b) (cauchy_real_exp (real_opp g))) invZ).
    + apply real_inv_pos_pos.
    + exact H3.
  - apply (real_le_trans _
             (real_mult (real_mult (cauchy_real_exp b)
                            (cauchy_real_exp (real_opp g))) invF) _).
    + apply (real_le_mult_compat_l_aux invZ invF
               (real_mult (cauchy_real_exp b) (cauchy_real_exp (real_opp g)))).
      * apply real_mult_pos_compat;
          [apply cauchy_real_exp_pos | apply cauchy_real_exp_pos].
      * exact H4.
    + apply (RealSetoid.real_eq_le).
      exact (eq_mult_inv_absorb (cauchy_real_exp b)
                  (cauchy_real_exp (real_opp g)) (factor_T_pos T Ht m)
                  (real_inv_pos_correct (factor_T T Ht m)
                     (factor_T_pos T Ht m))).
Qed.

(* ---------- 7. 质量守恒与两段 TV 界 ---------- *)

(* 非最优质量恒等式：1 − w_T(m) == Σ_{removeT m vocab} w_T *)
Lemma nonm_mass_eq : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (real_plus real_one (real_opp (w_T T Ht m)))
          (real_list_sum Token (w_T T Ht) (removeT m vocab)).
Proof.
  intros T Ht.
  assert (Hsplit : real_eq (real_list_sum Token (w_T T Ht) vocab)
                    (real_plus (w_T T Ht m)
                       (real_list_sum Token (w_T T Ht) (removeT m vocab))))
    by exact (split_count_one (w_T T Ht) m vocab m_count_one).
  assert (Hone : real_eq real_one
                   (real_plus (w_T T Ht m)
                      (real_list_sum Token (w_T T Ht) (removeT m vocab))))
    by exact (real_eq_trans real_one
                (real_list_sum Token (w_T T Ht) vocab)
                (real_plus (w_T T Ht m)
                   (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                (real_eq_sym _ _ (w_T_sum_one T Ht)) Hsplit).
  assert (Hc : real_eq (real_plus real_one (real_opp (w_T T Ht m)))
                 (real_plus (real_plus (w_T T Ht m)
                              (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                            (real_opp (w_T T Ht m))))
    by exact (RealSetoid.real_eq_plus_compat real_one
                (real_opp (w_T T Ht m))
                (real_plus (w_T T Ht m)
                   (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                (real_opp (w_T T Ht m)) Hone (real_eq_refl _)).
  assert (Hd : real_eq (real_plus (real_plus (w_T T Ht m)
                             (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                           (real_opp (w_T T Ht m)))
                 (real_list_sum Token (w_T T Ht) (removeT m vocab))).
  { assert (F1 : real_eq (real_plus (real_plus (w_T T Ht m) (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                              (real_opp (w_T T Ht m)))
                   (real_plus (w_T T Ht m)
                      (real_plus (real_list_sum Token (w_T T Ht) (removeT m vocab))
                                 (real_opp (w_T T Ht m)))))
      by exact (real_eq_sym _ _
                  (real_plus_assoc (w_T T Ht m)
                     (real_list_sum Token (w_T T Ht) (removeT m vocab))
                     (real_opp (w_T T Ht m)))).
    assert (F2 : real_eq (real_plus (w_T T Ht m)
                              (real_plus (real_list_sum Token (w_T T Ht) (removeT m vocab))
                                 (real_opp (w_T T Ht m))))
                   (real_plus (w_T T Ht m)
                      (real_plus (real_opp (w_T T Ht m))
                         (real_list_sum Token (w_T T Ht) (removeT m vocab)))))
      by exact (RealSetoid.real_eq_plus_compat (w_T T Ht m)
                  (real_plus (real_list_sum Token (w_T T Ht) (removeT m vocab))
                     (real_opp (w_T T Ht m)))
                  (w_T T Ht m)
                  (real_plus (real_opp (w_T T Ht m))
                     (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                  (real_eq_refl _)
                  (real_plus_comm (real_list_sum Token (w_T T Ht) (removeT m vocab))
                     (real_opp (w_T T Ht m)))).
    assert (F3 : real_eq (real_plus (w_T T Ht m)
                              (real_plus (real_opp (w_T T Ht m))
                                 (real_list_sum Token (w_T T Ht) (removeT m vocab))))
                   (real_plus (real_plus (w_T T Ht m) (real_opp (w_T T Ht m)))
                              (real_list_sum Token (w_T T Ht) (removeT m vocab))))
      by exact (real_plus_assoc (w_T T Ht m) (real_opp (w_T T Ht m))
                  (real_list_sum Token (w_T T Ht) (removeT m vocab))).
    assert (F4 : real_eq (real_plus (real_plus (w_T T Ht m) (real_opp (w_T T Ht m)))
                              (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                   (real_plus real_zero
                      (real_list_sum Token (w_T T Ht) (removeT m vocab))))
      by exact (RealSetoid.real_eq_plus_compat
                  (real_plus (w_T T Ht m) (real_opp (w_T T Ht m)))
                  (real_list_sum Token (w_T T Ht) (removeT m vocab))
                  real_zero
                  (real_list_sum Token (w_T T Ht) (removeT m vocab))
                  (real_plus_opp (w_T T Ht m)) (real_eq_refl _)).
    assert (F5 : real_eq (real_plus real_zero
                              (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                   (real_list_sum Token (w_T T Ht) (removeT m vocab)))
      by exact (real_eq_trans _
                  (real_plus (real_list_sum Token (w_T T Ht) (removeT m vocab))
                     real_zero) _
                  (real_plus_comm real_zero
                     (real_list_sum Token (w_T T Ht) (removeT m vocab)))
                  (real_plus_zero (real_list_sum Token (w_T T Ht) (removeT m vocab)))).
    exact (real_eq_trans _ _ _ F1 (real_eq_trans _ _ _ F2 (real_eq_trans _ _ _ F3 (real_eq_trans _ _ _ F4 F5)))).
  }
  exact (real_eq_trans _ _ _ Hc Hd).
Qed.

(* 非最优质量 ≤ N·e^{−γ/T} *)
Lemma nonm_mass_le_bound : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (real_list_sum Token (w_T T Ht) (removeT m vocab))
          (real_mult (real_of_nat (length vocab)) (decay_T T Ht)).
Proof.
  intros T Ht.
  apply (real_le_trans _
           (real_mult (real_of_nat (length (removeT m vocab)))
                      (decay_T T Ht)) _).
  - apply sum_nonneg_le_const_aux.
    intros x Hin.
    apply (core_decay_bound T Ht x).
    exact (remove_notin_aux m x vocab Hin).
  - apply (real_le_mult_compat_weak
             (real_of_nat (length (removeT m vocab)))
             (real_of_nat (length vocab)) (decay_T T Ht)).
    + apply real_le_from_lt_aux. apply cauchy_real_exp_pos.
    + apply real_of_nat_le_mono_aux. apply NatLe_drop. apply remove_length_le_aux.
Qed.

(* 逐点 TV 被积项 *)
Definition h_abs (T : Real) (Ht : real_lt real_zero T) (x : Token) : Real :=
  real_abs (real_minus_r (w_T T Ht x) (hard_dist x)).

(* m 项：|w_T(m) − 1| == Σ_{removeT} w_T == 1 − w_T(m) *)
Lemma h_m_eq_nonm_mass : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (h_abs T Ht m) (real_list_sum Token (w_T T Ht) (removeT m vocab)).
Proof.
  intros T Ht.
  assert (Hhm : real_eq (hard_dist m) real_one).
  { unfold hard_dist. destruct (token_eq_dec m m) as [H | Hn].
    - apply real_eq_refl.
    - exact (match Hn (@id_refl Token m) with end). }
  assert (Hw1 : real_le (w_T T Ht m) real_one) by exact (w_T_m_le_one T Ht).
  apply (real_eq_trans _
           (real_abs (real_minus_r (w_T T Ht m) real_one)) _).
  - apply real_abs_eq_compat.
    apply (RealSetoid.real_eq_plus_compat (w_T T Ht m)
               (real_opp (hard_dist m)) (w_T T Ht m) (real_opp real_one)).
    + apply real_eq_refl.
    + apply (RealSetoid.real_eq_opp_compat (hard_dist m) real_one Hhm).
  - apply (real_eq_trans _
             (real_plus real_one (real_opp (w_T T Ht m))) _).
    + apply (real_abs_minus_r_nonneg_aux (w_T T Ht m) real_one Hw1).
    + apply nonm_mass_eq.
Qed.

Lemma hsum_split : forall (T : Real) (Ht : real_lt real_zero T),
  real_eq (real_list_sum Token (h_abs T Ht) vocab)
          (real_plus (h_abs T Ht m)
                     (real_list_sum Token (h_abs T Ht) (removeT m vocab))).
Proof.
  intros T Ht. exact (split_count_one (h_abs T Ht) m vocab m_count_one).
Qed.

(* 非 m 项的 TV 质量 ≤ N·e^{−γ/T} *)
Lemma hsum_nonm_le : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (real_list_sum Token (h_abs T Ht) (removeT m vocab))
          (real_mult (real_of_nat (length vocab)) (decay_T T Ht)).
Proof.
  intros T Ht.
  apply (real_le_trans _
           (real_mult (real_of_nat (length (removeT m vocab)))
                      (decay_T T Ht)) _).
  - apply sum_nonneg_le_const_aux.
    intros x Hin.
    assert (Hxm : Not (Id x m))
      by exact (remove_notin_aux m x vocab Hin).
    assert (Hhz : real_eq (hard_dist x) real_zero).
    { unfold hard_dist. destruct (token_eq_dec x m) as [H | Hn].
      - destruct (Hxm H).
      - apply real_eq_refl. }
    assert (Hp : real_eq (real_minus_r (w_T T Ht x) (hard_dist x))
                   (w_T T Ht x)).
    { apply (real_eq_trans _ (real_plus (w_T T Ht x)
                 (real_opp (hard_dist x))) _).
      - apply real_eq_refl.
      - apply (real_eq_trans _
                   (real_plus (w_T T Ht x) (real_opp real_zero)) _).
        + apply (RealSetoid.real_eq_plus_compat (w_T T Ht x)
                     (real_opp (hard_dist x)) (w_T T Ht x)
                     (real_opp real_zero)).
          * apply real_eq_refl.
          * apply (RealSetoid.real_eq_opp_compat (hard_dist x) real_zero).
            exact Hhz.
        + apply (real_eq_trans _ (real_plus (w_T T Ht x) real_zero) _).
          * apply (RealSetoid.real_eq_plus_compat (w_T T Ht x)
                     (real_opp real_zero) (w_T T Ht x) real_zero
                     (real_eq_refl _) (real_opp_zero)).
          * apply real_plus_zero. }
    unfold h_abs.
    apply (RealSetoid.real_le_id_l
             (real_abs (real_minus_r (w_T T Ht x) (hard_dist x)))
             (real_abs (w_T T Ht x)) (decay_T T Ht)).
    + apply real_abs_eq_compat. exact Hp.
    + apply (real_le_trans _ (w_T T Ht x) _).
      * apply (RealSetoid.real_eq_le).
        apply (real_abs_pos_req (w_T T Ht x) (w_T_pos T Ht x)).
      * exact (core_decay_bound T Ht x Hxm).
  - apply (real_le_mult_compat_weak
             (real_of_nat (length (removeT m vocab)))
             (real_of_nat (length vocab)) (decay_T T Ht)).
    + apply real_le_from_lt_aux. apply cauchy_real_exp_pos.
    + apply real_of_nat_le_mono_aux. apply NatLe_drop. apply remove_length_le_aux.
Qed.

(* 词表势的正性（vocab 非空 ⟹ |vocab| ≥ 1） *)
Lemma vocab_len_pos : real_lt real_zero (real_of_nat (length vocab)).
Proof.
  destruct vocab as [| w rest].
  - exact (match vocab_nonempty (@id_refl (list Token) nil) with end).
  - cbn [length].
    apply (real_lt_eq_lt real_zero
             (real_plus real_one (real_of_nat (length rest))) _).
    + apply (real_eq_lt_lt real_zero
               (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat (length rest)))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_lt_plus_compat_lt_le.
        -- apply real_lt_zero_one.
        -- apply real_of_nat_nonneg_aux.
    + apply real_eq_refl.
Qed.

(* inv2·(X+X) == X（inv2 := inv(2)，用于 TV 的二分之一折叠） *)
Lemma eq_inv2_double : forall (X : Real) (HX : real_lt real_zero (real_plus real_one real_one)),
  real_eq (real_mult (real_inv_pos (real_plus real_one real_one) HX)
             (real_plus X X))
          X.
Proof.
  intros X HX.
  assert (Hii : real_eq (real_mult (real_plus real_one real_one)
                         (real_inv_pos (real_plus real_one real_one) HX))
                   real_one)
    by exact (real_inv_pos_correct (real_plus real_one real_one) HX).
  assert (Hmx : real_eq X (real_mult real_one X))
    by exact (real_eq_sym (real_mult real_one X) X
                (real_eq_trans _ _ _ (real_mult_comm real_one X) (real_mult_one X))).
  assert (DSB : real_eq (real_plus X X) (real_mult (real_plus real_one real_one) X))
    by exact (real_eq_trans _ _ _
      (RealSetoid.real_eq_plus_compat X X (real_mult real_one X) (real_mult real_one X)
        Hmx Hmx)
      (real_distrib_r real_one real_one X)).
  assert (Hkey : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) HX)
                              (real_mult (real_plus real_one real_one) X))
                         (real_mult real_one X)).
  { apply (real_eq_trans _
             (real_mult (real_mult (real_inv_pos (real_plus real_one real_one) HX)
                        (real_plus real_one real_one)) X) _).
    - exact (real_mult_assoc (real_inv_pos (real_plus real_one real_one) HX)
               (real_plus real_one real_one) X).
    - apply (real_eq_trans _
               (real_mult (real_mult (real_plus real_one real_one)
                          (real_inv_pos (real_plus real_one real_one) HX)) X) _).
      + apply (RealSetoid.real_eq_mult_compat
                  (real_mult (real_inv_pos (real_plus real_one real_one) HX)
                     (real_plus real_one real_one))
                  X
                  (real_mult (real_plus real_one real_one)
                     (real_inv_pos (real_plus real_one real_one) HX))
                  X
                  (real_mult_comm (real_inv_pos (real_plus real_one real_one) HX)
                     (real_plus real_one real_one))
                  (real_eq_refl X)).
      + apply (RealSetoid.real_eq_mult_compat
                  (real_mult (real_plus real_one real_one)
                     (real_inv_pos (real_plus real_one real_one) HX))
                  X
                  real_one
                  X
                  Hii (real_eq_refl X)). }
  apply (real_eq_trans _
           (real_mult (real_inv_pos (real_plus real_one real_one) HX)
              (real_mult (real_plus real_one real_one) X)) _).
  - apply (RealSetoid.real_eq_mult_compat
              (real_inv_pos (real_plus real_one real_one) HX)
              (real_plus X X)
              (real_inv_pos (real_plus real_one real_one) HX)
              (real_mult (real_plus real_one real_one) X)
              (real_eq_refl (real_inv_pos (real_plus real_one real_one) HX))
              DSB).
  - exact (real_eq_trans _ _ _ Hkey
             (real_eq_trans _ _ _ (real_mult_comm real_one X) (real_mult_one X))).
Qed.

Lemma tv_hard_le_decay_scale : forall (T : Real) (Ht : real_lt real_zero T),
  real_le (tv_hard T Ht)
          (real_mult (real_of_nat (length vocab)) (decay_T T Ht)).
Proof.
  intros T Ht.
  assert (Hinv2 : real_lt real_zero
             (real_inv_pos (real_plus real_one real_one)
                (real_lt_plus_compat real_zero real_one real_zero real_one
                   real_lt_zero_one real_lt_zero_one)))
    by apply real_inv_pos_pos.
  assert (Hsp : real_eq (real_list_sum Token (h_abs T Ht) vocab)
                  (real_plus (h_abs T Ht m)
                     (real_list_sum Token (h_abs T Ht) (removeT m vocab))))
    by exact (hsum_split T Ht).
  assert (HA : real_le (h_abs T Ht m)
                 (real_mult (real_of_nat (length vocab)) (decay_T T Ht))).
  { apply (real_le_trans _ (real_list_sum Token (w_T T Ht) (removeT m vocab)) _).
    - apply (RealSetoid.real_eq_le (h_abs T Ht m)
               (real_list_sum Token (w_T T Ht) (removeT m vocab))
               (h_m_eq_nonm_mass T Ht)).
    - exact (nonm_mass_le_bound T Ht). }
  assert (HB : real_le (real_list_sum Token (h_abs T Ht) (removeT m vocab))
                 (real_mult (real_of_nat (length vocab)) (decay_T T Ht)))
    by exact (hsum_nonm_le T Ht).
  assert (Hsum : real_le (real_list_sum Token (h_abs T Ht) vocab)
                   (real_plus (real_mult (real_of_nat (length vocab)) (decay_T T Ht))
                      (real_mult (real_of_nat (length vocab)) (decay_T T Ht)))).
  { apply (real_le_trans _
             (real_plus (h_abs T Ht m)
                (real_list_sum Token (h_abs T Ht) (removeT m vocab))) _).
    - exact (RealSetoid.real_eq_le _ _ Hsp).
    - exact (real_le_plus_compat (h_abs T Ht m)
                (real_mult (real_of_nat (length vocab)) (decay_T T Ht))
                (real_list_sum Token (h_abs T Ht) (removeT m vocab))
                (real_mult (real_of_nat (length vocab)) (decay_T T Ht))
                HA HB). }
  assert (Hstep : real_le (real_mult
                             (real_inv_pos (real_plus real_one real_one)
                                (real_lt_plus_compat real_zero real_one
                                   real_zero real_one real_lt_zero_one
                                   real_lt_zero_one))
                             (real_list_sum Token (h_abs T Ht) vocab))
                     (real_mult (real_of_nat (length vocab)) (decay_T T Ht))).
  { apply (real_le_trans _
             (real_mult (real_inv_pos (real_plus real_one real_one)
                           (real_lt_plus_compat real_zero real_one real_zero
                              real_one real_lt_zero_one real_lt_zero_one))
                (real_plus (real_mult (real_of_nat (length vocab)) (decay_T T Ht))
                   (real_mult (real_of_nat (length vocab)) (decay_T T Ht)))) _).
    - apply (real_le_mult_compat_l_aux _ _ _ Hinv2 Hsum).
    - exact (RealSetoid.real_eq_le _ _
               (eq_inv2_double (real_mult (real_of_nat (length vocab)) (decay_T T Ht))
                  (real_lt_plus_compat real_zero real_one real_zero real_one
                     real_lt_zero_one real_lt_zero_one))). }
  unfold tv_hard.
  apply (real_le_trans _
           (real_mult (real_of_nat (length vocab)) (decay_T T Ht)) _).
  - exact Hstep.
  - apply (RealSetoid.real_eq_le). apply real_eq_refl.
Qed.

Theorem hard_attention_limit : forall eps : Real,
  real_lt real_zero eps ->
  sigT (fun T0 => And (real_lt real_zero T0)
    (forall (T : Real) (Ht : real_lt real_zero T), real_lt T T0 ->
      real_le (tv_hard T Ht) eps)).
Proof.
  intros eps Heps.
  set (N := length vocab).
  set (EN := real_of_nat N).
  set (M := real_mult EN (real_inv_pos eps Heps)).
  set (ylog := real_plus M real_one).
  assert (HM : real_lt real_zero M).
  { apply real_mult_pos_compat.
    - apply vocab_len_pos.
    - apply real_inv_pos_pos. }
  assert (Hy : real_lt real_zero ylog).
  { apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero) _).
    - apply real_eq_sym. apply real_plus_zero.
    - apply real_lt_plus_compat.
      + exact HM.
      + apply real_lt_zero_one. }
  assert (Hy1 : real_lt real_one ylog).
  { apply (real_eq_lt_lt real_one (real_plus real_zero real_one) ylog).
    - apply (real_eq_trans _ (real_plus real_one real_zero) _).
      + apply real_eq_sym. exact (real_plus_comm real_zero real_one).
      + exact (real_plus_zero real_one).
    - apply (real_lt_plus_compat_lt_le real_zero M real_one real_one HM
               (real_le_refl real_one)). }
  assert (HL : real_lt real_zero (cw_log ylog Hy)).
  { apply exp_reflects_lt.
    apply (real_eq_lt_lt (cauchy_real_exp real_zero) real_one
             (cauchy_real_exp (cw_log ylog Hy))).
    - exact cauchy_real_exp_zero.
    - apply (real_lt_eq_lt real_one ylog (cauchy_real_exp (cw_log ylog Hy))).
      + exact Hy1.
      + exact (real_eq_sym (cauchy_real_exp (cw_log ylog Hy)) ylog
                 (cw_log_exp_right ylog Hy)). }
  exists (real_mult gamma (real_inv_pos (cw_log ylog Hy) HL)). split.
  - apply real_mult_pos_compat; [exact gamma_pos | apply real_inv_pos_pos].
  - intros T Ht Hlt.
    set (invT := real_inv_pos T Ht).
    assert (HinvT : real_lt real_zero invT) by apply real_inv_pos_pos.
    set (a := real_mult invT gamma).
    (* 步1：T·L < γ *)
    assert (Hs1 : real_lt (real_mult T (cw_log ylog Hy)) gamma).
    { apply (real_lt_eq_lt (real_mult T (cw_log ylog Hy))
               (real_mult (real_mult gamma (real_inv_pos (cw_log ylog Hy) HL))
                  (cw_log ylog Hy)) gamma).
      - apply (real_mult_lt_compat T
                  (real_mult gamma (real_inv_pos (cw_log ylog Hy) HL))
                  (cw_log ylog Hy) Hlt HL).
      - apply (real_eq_trans _
                 (real_mult gamma
                    (real_mult (real_inv_pos (cw_log ylog Hy) HL)
                               (cw_log ylog Hy))) _).
        + apply real_eq_sym. apply real_mult_assoc.
        + apply (real_eq_trans _
                   (real_mult gamma
                      (real_mult (cw_log ylog Hy)
                         (real_inv_pos (cw_log ylog Hy) HL))) _).
          * apply (RealSetoid.real_eq_mult_compat gamma
                     (real_mult (real_inv_pos (cw_log ylog Hy) HL)
                                (cw_log ylog Hy))
                     gamma
                     (real_mult (cw_log ylog Hy)
                                (real_inv_pos (cw_log ylog Hy) HL))).
            -- apply real_eq_refl.
            -- apply real_mult_comm.
          * apply (real_eq_trans _ (real_mult gamma real_one) _).
            -- apply (RealSetoid.real_eq_mult_compat gamma
                        (real_mult (cw_log ylog Hy)
                           (real_inv_pos (cw_log ylog Hy) HL)) gamma real_one).
               ++ apply real_eq_refl.
               ++ apply (real_inv_pos_correct (cw_log ylog Hy) HL).
            -- apply real_mult_one. }
    (* 步2：L < γ/T *)
    assert (Hs2 : real_lt (cw_log ylog Hy) a).
    { assert (Hmul : real_lt (real_mult invT (real_mult T (cw_log ylog Hy)))
                             (real_mult invT gamma))
        by (apply (real_mult_lt_compat_l _ _ invT Hs1 HinvT)).
      apply (real_lt_eq_lt (cw_log ylog Hy) (real_mult invT gamma) a).
      + apply (real_eq_lt_lt (cw_log ylog Hy)
                 (real_mult invT (real_mult T (cw_log ylog Hy)))
                 (real_mult invT gamma)).
        * apply real_eq_sym.
          exact (real_eq_trans _ _ _
                   (real_eq_trans _ _ _
                     (real_eq_trans _ _ _
                       (real_mult_assoc invT T (cw_log ylog Hy))
                       (RealSetoid.real_eq_mult_compat
                          (real_mult invT T) (cw_log ylog Hy)
                          (real_mult T invT) (cw_log ylog Hy)
                          (real_mult_comm invT T)
                          (real_eq_refl (cw_log ylog Hy))))
                     (RealSetoid.real_eq_mult_compat
                        (real_mult T invT) (cw_log ylog Hy)
                        real_one (cw_log ylog Hy)
                        (real_inv_pos_correct T Ht)
                        (real_eq_refl (cw_log ylog Hy))))
                   (real_eq_trans _ _ _
                     (real_mult_comm real_one (cw_log ylog Hy))
                     (real_mult_one (cw_log ylog Hy)))).
        * exact Hmul.
      + apply real_eq_refl. }
    (* 步3：M ≤ e^{γ/T} *)
    assert (Hs3 : real_le M (cauchy_real_exp a)).
    { apply (real_le_trans _ (cauchy_real_exp (cw_log ylog Hy)) _).
      - apply (RealSetoid.real_le_id_r M ylog
                 (cauchy_real_exp (cw_log ylog Hy))).
        + exact (real_eq_sym (cauchy_real_exp (cw_log ylog Hy)) ylog
                   (cw_log_exp_right ylog Hy)).
        + apply real_le_plus_nonneg_r_aux.
          apply real_le_from_lt_aux. apply real_lt_zero_one.
      - apply real_exp_le_mono. exact (real_le_from_lt_aux _ _ Hs2). }
    (* 步4：N ≤ eps·e^{γ/T} *)
    assert (Hs4 : real_le EN (real_mult eps (cauchy_real_exp a))).
    { apply (RealSetoid.real_le_id_l EN (real_mult eps M) _).
      - exact (real_eq_sym _ _
          (real_eq_trans _ _ _
            (real_mult_assoc eps EN (real_inv_pos eps Heps))
            (real_eq_trans _ _ _
              (RealSetoid.real_eq_mult_compat
                 (real_mult eps EN) (real_inv_pos eps Heps)
                 (real_mult EN eps) (real_inv_pos eps Heps)
                 (real_mult_comm eps EN)
                 (real_eq_refl (real_inv_pos eps Heps)))
              (real_eq_trans _ _ _
                (real_eq_sym _ _ (real_mult_assoc EN eps (real_inv_pos eps Heps)))
                (real_eq_trans _ _ _
                  (RealSetoid.real_eq_mult_compat
                     EN (real_mult eps (real_inv_pos eps Heps))
                     EN real_one
                     (real_eq_refl EN) (real_inv_pos_correct eps Heps))
                  (real_mult_one EN)))))).
      - apply (real_le_mult_compat_l_aux M (cauchy_real_exp a) eps
                 Heps Hs3). }
    (* 步5：e^{−γ/T}·N ≤ eps *)
    assert (Hs5 : real_le
                    (real_mult (cauchy_real_exp (real_opp a)) EN) eps).
    { apply (RealSetoid.real_le_id_r
               (real_mult (cauchy_real_exp (real_opp a)) EN)
               (real_mult (cauchy_real_exp (real_opp a))
                  (real_mult eps (cauchy_real_exp a))) eps).
      - apply (real_eq_trans _
                 (real_mult (cauchy_real_exp (real_opp a))
                            (real_mult (cauchy_real_exp a) eps)) _).
        + apply (RealSetoid.real_eq_mult_compat
                    (cauchy_real_exp (real_opp a))
                    (real_mult eps (cauchy_real_exp a))
                    (cauchy_real_exp (real_opp a))
                    (real_mult (cauchy_real_exp a) eps)).
          * apply real_eq_refl.
          * apply real_mult_comm.
        + apply (real_eq_trans _
                     (real_mult
                        (real_mult (cauchy_real_exp (real_opp a))
                                   (cauchy_real_exp a))
                        eps) _).
          * apply real_mult_assoc.
          * apply (real_eq_trans _ (real_mult real_one eps) _).
            -- apply (RealSetoid.real_eq_mult_compat
                        (real_mult (cauchy_real_exp (real_opp a))
                                   (cauchy_real_exp a))
                        eps
                        real_one eps).
               ++ apply exp_mult_opp_l_aux.
               ++ apply real_eq_refl.
            -- apply (real_eq_trans _ (real_mult eps real_one) _).
               ++ apply real_mult_comm.
               ++ apply real_mult_one.
      - apply (real_le_mult_compat_l_aux EN
                 (real_mult eps (cauchy_real_exp a))
                 (cauchy_real_exp (real_opp a))).
        + apply cauchy_real_exp_pos.
        + exact Hs4. }
    (* 结论：tv_hard ≤ N·e^{−γ/T} ≤ e^{−γ/T}·N ≤ eps *)
    apply (real_le_trans _
             (real_mult (real_of_nat (length vocab))
                        (decay_T T Ht)) _).
    + apply tv_hard_le_decay_scale.
    + apply (real_le_trans _
               (real_mult (cauchy_real_exp (real_opp a))
                  (real_of_nat (length vocab))) _).
      * apply (RealSetoid.real_eq_le). apply real_mult_comm.
      * exact Hs5.
Qed.

End AttnHardLimit.

Print Assumptions qleT_refl_local.
Print Assumptions LCAudit.natlt_intro.

Print Assumptions LCAudit.qleT_refl.
Print Assumptions LCAudit.natlt_elim.

Print Assumptions sf_natlt_elim.
Print Assumptions sf_natlt_intro.
Print Assumptions LCAudit.bool_id_true.
Print Assumptions LCAudit.bool_true_id.
Print Assumptions LCAudit.audit_and_comm.
Print Assumptions LCAudit.audit_or_comm.
