(* 五字段指针｜使命：194 段判据窗口边界定理——188 裁决 δ 支（π_L 整数残差失败支约束
   |r_n| ≤ 5b·D_n/(2n+1) 永不把整数压到 <1）升格为正形边界定理。(i) 交错余项双侧界
   （偶支升/奇支降＋显式 gap）；(ii) 公分母整除性 q'_n := (2n+1)! 使 q'_n·S_n ∈ Z（见证
   P_n）；(iii) 边界主件：极限 x₀（交错级数自身 cauchy 极限，恒真无 π 前提，不预设与 π
   相等）到部分和距离 ≥ gap_n := 8/((2n+1)(2n+3))，margin q'_n·gap_n = 8·(2n)!/(2n+3)
   无界；(iv) 逃逸认证残差律：自然窗 b·q'_n·t_n = 4b·(2n)! 无界（188 观察的定理化）＋
   近极限 q 的逃逸窗障碍定理；(c) 族定理：Niven/阶乘族 margin ≤ 1 有界 vs Leibniz 族
   margin 无界的分离对照。
  依赖：Stdlib QArith/ZArith/Lia（lra 由 Lia 链加载）＋S01_BaseRing/S02_CauchyComplete
   （Set 面承载 Id/And 与 QltT/QleT'/QeqT 判定器及双向回向桥）；判据接口
   形状按 UpReqIrrationalCriterion.v :237/:242/:247 核对逐字重述于 §6（lic_* 定义仅形
   重述，使用面以注释指认原件行号；本件不 Require 判据体）。
  构造性：零公理声明／零自证收尾；正形主语句 Set 层（sigT＋Id bool 形，与
   S02_CauchyComplete.v :48 的「Id＋bool 判定器＝true」同形）；否定面引理 Prop 型
   （¬ 无 Set 形，脚手架级）；证内 Prop（Qlt/Qle）仅脚手架。全程零 arctan／零 π_geom
   使用——本定理族恒真无 π 前提。
  编译配方：rocq compile -native-compiler no -q -Q <世界根> "" LW0LeibWindow.v
   （S01/S02 由世界根 -Q 供给；语句面洗形后全部 Set 承载）
  命名：leiblw_ 前缀（全树 grep -w 查重零占用，2026-09 实测）。 *)
(* 对标：UpReqIrrationalCriterion.v :237/:242/:247（形逐字重述，使用面以注释指认原件行号）。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import micromega.Lqa.
Require Import S01_BaseRing S02_CauchyComplete.

(* QArith.QArith 默认开 Q_scope——本件以 nat_scope 为默认，Q 位字面量一律 %Q 注记 *)
Local Open Scope nat_scope.

(* ============================================================ *)
(* §0 工具层：奇偶、Z 桥、Q 原生表示比较器、Qabs 引理                   *)
(* ============================================================ *)

Fixpoint leiblw_even (n : nat) : bool :=
  match n with
  | 0 => true
  | Datatypes.S k => negb (leiblw_even k)
  end.


(* k = 2j 或 k = 2j+1 的构造性二分 *)
Lemma leiblw_par_decomp : forall k : nat,
  sum (sigT (fun j : nat => k = 2 * j)) (sigT (fun j : nat => k = 2 * j + 1)).
Proof.
  induction k as [|k IH].
  - left. exists 0. reflexivity.
  - destruct IH as [[j Hj]|[j Hj]].
    + right. exists j. rewrite Hj. lia.
    + left. exists (Datatypes.S j). rewrite Hj. lia.
Qed.

(* Set 值恒等型（S02_CauchyComplete.v :48 的 Id 形在本件自备：零库件依赖） *)
Inductive leiblw_Id {A : Type} (a : A) : A -> Set := leiblw_id_intro : leiblw_Id a a.

Lemma leiblw_id_eq : forall b : bool, b = true -> leiblw_Id b true.
Proof. intros b H. rewrite H. apply leiblw_id_intro. Qed.

(* 泛 Set 等词桥（leiblw_Id 面承载，A : Type 通用）：语句面等词站正形；
   反向（Id → eq）不设具名语句（回向桥语句面无 Set 形），使用处以
   destruct (<Id 事实>); reflexivity 就地消去（Id 消去律 J 计算） *)
Lemma leiblw_eq_id : forall (A : Type) (x y : A), x = y -> leiblw_Id x y.
Proof. intros A x y H. rewrite H. apply leiblw_id_intro. Qed.

Lemma leiblw_even_2m : forall m : nat, leiblw_Id (leiblw_even (2 * m)) true.
Proof.
  intros m. apply leiblw_eq_id.
  induction m as [|m IH]; [reflexivity|].
  replace (2 * Datatypes.S m) with (Datatypes.S (Datatypes.S (2 * m))) by lia.
  cbn [leiblw_even]. rewrite IH. reflexivity.
Qed.

Lemma leiblw_even_2m1 : forall m : nat, leiblw_Id (leiblw_even (2 * m + 1)) false.
Proof.
  intros m. apply leiblw_eq_id.
  replace (2 * m + 1) with (Datatypes.S (2 * m)) by lia.
  cbn [leiblw_even].
  assert (H2 : leiblw_even (2 * m) = true).
  { induction m as [|m IH2]; [reflexivity|].
    replace (2 * Datatypes.S m) with (Datatypes.S (Datatypes.S (2 * m))) by lia.
    cbn [leiblw_even]. rewrite IH2. reflexivity. }
  rewrite H2. reflexivity.
Qed.

(* Set 值 Q 严格序判定（本环境 QArith 无 Qlt_bool——以 Q 比较自备，S02:48 同位） *)
Definition leiblw_Qltb (x y : Q) : bool :=
  match Qcompare x y with Lt => true | _ => false end.

Lemma leiblw_Qltb_true : forall x y : Q, Qlt x y -> leiblw_Id (leiblw_Qltb x y) true.
Proof.
  intros x y H. apply leiblw_id_eq. unfold leiblw_Qltb.
  destruct (Qcompare_spec x y) as [Heq|Hlt'|Hgt].
  - exfalso. unfold Qeq, Qlt in *. cbn [Qnum Qden] in *. nia.
  - reflexivity.
  - exfalso. unfold Qgt, Qlt in *. cbn [Qnum Qden] in *. nia.
Qed.

(* Z.of_nat 正性桥（本环境 lia 不自带 zify；前提 1 <= n——Z.of_nat 0 = 0 不可） *)
Lemma leiblw_znat_pos : forall n : nat, (1 <= n)%nat -> leiblw_Id (Z.ltb 0 (Z.of_nat n)) true.
Proof.
  intros n Hn. apply leiblw_eq_id. apply (proj2 (Z.ltb_lt _ _)).
  destruct n as [|k]; [lia|].
  cbn [Z.of_nat]. apply Pos2Z.is_pos.
Qed.

(* Z.pos (Pos.of_succ_nat k) = k+1 —— 把一切 Q 分母化到 lia/nia 可解面 *)
Lemma leiblw_pos_succ : forall k : nat, leiblw_Id (Z.pos (Pos.of_succ_nat k)) (Z.of_nat (Datatypes.S k)).
Proof.
  intros k. apply leiblw_eq_id.
  induction k as [|k IH]; [reflexivity|].
  simpl Pos.of_succ_nat. rewrite Pos2Z.inj_succ.
  assert (Heq : Z.pos (Pos.of_succ_nat k) = Z.of_nat (Datatypes.S k))
    by (destruct IH; reflexivity).
  rewrite Heq. lia.
Qed.

(* 线性化战术：pos_succ（Id 面事实就地 destruct 取 eq）→ inj 系 *)
Ltac leiblw_ps k :=
  let H := fresh "Hps" in
  assert (H : Z.pos (Pos.of_succ_nat k) = Z.of_nat (Datatypes.S k))
    by (destruct (leiblw_pos_succ k); reflexivity);
  rewrite H.

Ltac leiblw_zpos_goal :=
  match goal with
  | |- context [Z.pos (Pos.of_succ_nat ?k)] =>
      let H := fresh "Hps" in
      assert (H : Z.pos (Pos.of_succ_nat k) = Z.of_nat (Datatypes.S k))
        by (destruct (leiblw_pos_succ k); reflexivity);
      rewrite H; leiblw_zpos_goal
  | _ => idtac
  end.

Ltac leiblw_zlin := leiblw_zpos_goal;
  rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_add, ?Nat2Z.inj_mul, ?Pos2Z.inj_mul, ?Nat2Z.inj_sub in *.

(* pos_succ 直落 +1 形（绕开 zlin 链的 inj_succ 二次归约） *)
Lemma leiblw_pos_succ1 : forall k : nat, leiblw_Id (Z.pos (Pos.of_succ_nat k)) (Z.of_nat k + 1)%Z.
Proof. intros k. apply leiblw_eq_id. leiblw_ps k. lia. Qed.

Lemma leiblw_qmake_eq : forall (a b : Z) (p q : positive),
  (a # p)%Q == (b # q)%Q -> leiblw_Id ((a * Z.pos q)%Z) ((b * Z.pos p)%Z).
Proof.
  intros a b p q H. apply leiblw_eq_id. unfold Qeq in H. cbn [Qnum Qden] in H. exact H.
Qed.

Lemma leiblw_qmake_lt : forall (a b : Z) (p q : positive),
  Qlt (a # p)%Q (b # q)%Q -> leiblw_Id (Z.ltb ((a * Z.pos q)%Z) ((b * Z.pos p)%Z)) true.
Proof.
  intros a b p q H. apply leiblw_eq_id. apply (proj2 (Z.ltb_lt _ _)).
  unfold Qlt in H. cbn [Qnum Qden] in H. apply Z.compare_lt_iff in H. exact H.
Qed.

Lemma leiblw_qmake_le : forall (a b : Z) (p q : positive),
  Qle (a # p)%Q (b # q)%Q -> leiblw_Id (Z.leb ((a * Z.pos q)%Z) ((b * Z.pos p)%Z)) true.
Proof.
  intros a b p q H. apply leiblw_eq_id. apply (proj2 (Z.leb_le _ _)).
  unfold Qle in H. cbn [Qnum Qden] in H. apply Z.compare_le_iff in H. exact H.
Qed.

Lemma leiblw_qabs_id : forall q : Q, Qle 0%Q q -> QeqT (Qabs q) q.
Proof.
  intros [z p] H. apply qeq_imp_qeqT. unfold Qle in H. cbn [Qnum Qden] in H.
  cbn [Qabs]. unfold Qeq. cbn [Qnum Qden]. destruct z as [|z'|z'].
  - reflexivity.
  - reflexivity.
  - exfalso. pose proof (Pos2Z.is_pos z') as Hp. simpl in H. lia.
Qed.

Lemma leiblw_qabs_neg : forall q : Q, Qle q 0%Q -> QeqT (Qabs q) (- q)%Q.
Proof.
  intros [z p] H. apply qeq_imp_qeqT. unfold Qle in H. cbn [Qnum Qden] in H.
  cbn [Qabs Qopp]. unfold Qeq. cbn [Qnum Qden]. destruct z as [|z'|z'].
  - reflexivity.
  - exfalso. pose proof (Pos2Z.is_pos z') as Hp. simpl in H. lia.
  - reflexivity.
Qed.

(* ============================================================ *)
(* §1 级数本体：t_k := 4·(−1)^k/(2k+1)，S_n := Σ_{k<n} t_k            *)
(* ============================================================ *)

Definition leiblw_t (k : nat) : Q :=
  if leiblw_even k
  then (4 # Pos.of_succ_nat (2 * k))%Q
  else ((-4) # Pos.of_succ_nat (2 * k))%Q.

Fixpoint leiblw_S (n : nat) : Q :=
  match n with
  | 0 => 0%Q
  | Datatypes.S m => leiblw_S m + leiblw_t m
  end.

Lemma leiblw_S_SS : forall n : nat,
  QeqT (leiblw_S (Datatypes.S (Datatypes.S n))) (leiblw_S n + leiblw_t n + leiblw_t (Datatypes.S n))%Q.
Proof. intros n. apply qeq_imp_qeqT. unfold Qeq. cbn [leiblw_S]. lia. Qed.

Lemma leiblw_S_step : forall n : nat, QeqT (leiblw_S (Datatypes.S n)) (leiblw_S n + leiblw_t n)%Q.
Proof. intros n. apply qeq_imp_qeqT. apply Qeq_refl. Qed.

Lemma leiblw_t_pos_case : forall k : nat,
  leiblw_even k = true -> QeqT (leiblw_t k) (4 # Pos.of_succ_nat (2 * k))%Q.
Proof. intros k H. apply qeq_imp_qeqT. unfold leiblw_t. rewrite H. reflexivity. Qed.

Lemma leiblw_t_neg_case : forall k : nat,
  leiblw_even k = false -> QeqT (leiblw_t k) ((-4) # Pos.of_succ_nat (2 * k))%Q.
Proof. intros k H. apply qeq_imp_qeqT. unfold leiblw_t. rewrite H. reflexivity. Qed.

Lemma leiblw_t_even : forall m : nat,
  QeqT (leiblw_t (2 * m)) (4 # Pos.of_succ_nat (4 * m))%Q.
Proof.
  intros m.
  assert (Hev : leiblw_even (2 * m) = true) by (destruct (leiblw_even_2m m); reflexivity).
  apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_pos_case (2 * m) Hev)) as Htp. rewrite Htp.
  replace (2 * (2 * m)) with (4 * m) by lia. reflexivity.
Qed.

Lemma leiblw_t_odd : forall m : nat,
  QeqT (leiblw_t (2 * m + 1)) ((-4) # Pos.of_succ_nat (4 * m + 2))%Q.
Proof.
  intros m.
  assert (Hev : leiblw_even (2 * m + 1) = false) by (destruct (leiblw_even_2m1 m); reflexivity).
  apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_neg_case (2 * m + 1) Hev)) as Htp. rewrite Htp.
  replace (2 * (2 * m + 1)) with (4 * m + 2) by lia. reflexivity.
Qed.

Lemma leiblw_t_even_pos : forall m : nat, QltT 0%Q (leiblw_t (2 * m))%Q.
Proof.
  intros m. apply Qlt_to_QltT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_even m)) as He. rewrite He.
  unfold Qlt. cbn [Qnum Qden]. apply Z.compare_lt_iff.
  leiblw_zlin.
  assert (0 <= Z.of_nat (4 * m))%Z by apply Nat2Z.is_nonneg. lia.
Qed.

Lemma leiblw_t_odd_neg : forall m : nat, QltT (leiblw_t (2 * m + 1))%Q 0%Q.
Proof.
  intros m. apply Qlt_to_QltT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd m)) as He. rewrite He.
  unfold Qlt. cbn [Qnum Qden]. apply Z.compare_lt_iff.
  leiblw_zlin. lia.
Qed.

(* ============================================================ *)
(* §1½ Q 分数代数工作层：加和规范形／shunt／比较器                      *)
(* ============================================================ *)

(* 加和规范形：(a#p)+(b#q) == ((a·q'+b·p')#(p·q)) *)
Lemma leiblw_qplus_norm : forall (a b : Z) (p q : positive),
  QeqT ((a # p) + (b # q))%Q ((a * Z.pos q + b * Z.pos p) # (Pos.mul p q))%Q.
Proof.
  intros a b p q. apply qeq_imp_qeqT. unfold Qeq. cbn [Qnum Qden Qplus Qmult Pos.mul].
  rewrite Pos2Z.inj_mul. ring.
Qed.

Lemma leiblw_qplus_lt0 : forall (a b : Z) (p q : positive),
  (0 < a * Z.pos q + b * Z.pos p)%Z -> QltT 0%Q (((a # p) + (b # q))%Q).
Proof.
  intros a b p q H. apply Qlt_to_QltT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qplus_norm a b p q)) as Hn. rewrite Hn.
  unfold Qlt. cbn [Qnum Qden]. apply Z.compare_lt_iff.
  rewrite Z.mul_0_l, Z.mul_1_r. exact H.
Qed.

Lemma leiblw_qplus_lt0b : forall (a b : Z) (p q : positive),
  (a * Z.pos q + b * Z.pos p < 0)%Z -> QltT ((a # p) + (b # q))%Q 0%Q.
Proof.
  intros a b p q H. apply Qlt_to_QltT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qplus_norm a b p q)) as Hn. rewrite Hn.
  unfold Qlt. cbn [Qnum Qden]. apply Z.compare_lt_iff.
  rewrite Z.mul_1_r, Z.mul_0_l. exact H.
Qed.

Lemma leiblw_qplus_le0 : forall (a b : Z) (p q : positive),
  (a * Z.pos q + b * Z.pos p <= 0)%Z -> QleT' (((a # p) + (b # q))%Q) 0%Q.
Proof.
  intros a b p q H. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qplus_norm a b p q)) as Hn. rewrite Hn.
  unfold Qle. cbn [Qnum Qden]. apply Z.compare_le_iff.
  rewrite Z.mul_1_r, Z.mul_0_l. exact H.
Qed.

Lemma leiblw_qplus_eq : forall (a b : Z) (p q : positive) (c : Z) (r : positive),
  ((a * Z.pos q + b * Z.pos p) * Z.pos r = c * Z.pos (Pos.mul p q))%Z ->
  QeqT ((a # p) + (b # q))%Q (c # r)%Q.
Proof.
  intros a b p q c r H. apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qplus_norm a b p q)) as Hn. rewrite Hn.
  unfold Qeq. cbn [Qnum Qden]. exact H.
Qed.

Lemma leiblw_qopp_distr : forall x y : Q, QeqT (-(x + y))%Q ((- x) + (- y))%Q.
Proof.
  intros x y. apply qeq_imp_qeqT. unfold Qeq. cbn [Qnum Qden Qplus Qopp]. ring.
Qed.

(* 带负号的规范形：-((a#p)+(b#q)) == (c#r) *)
Lemma leiblw_qneg_plus_eq : forall (a b : Z) (p q : positive) (c : Z) (r : positive),
  (((- a) * Z.pos q + (- b) * Z.pos p) * Z.pos r = c * Z.pos (Pos.mul p q))%Z ->
  QeqT (-((a # p) + (b # q)))%Q (c # r)%Q.
Proof.
  intros a b p q c r H. apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qopp_distr (a # p)%Q (b # q)%Q)) as Hd.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qplus_eq (- a)%Z (- b)%Z p q c r H)) as Hq.
  rewrite Hd. unfold Qopp. cbn [Qnum Qden]. rewrite Hq. apply Qeq_refl.
Qed.

(* shunt：((A+U)+V)−A == U+V *)
Lemma leiblw_qshunt : forall A U V : Q, QeqT (((A + U) + V) - A)%Q (U + V)%Q.
Proof.
  intros A U V. apply qeq_imp_qeqT. unfold Qminus.
  rewrite <- (Qplus_assoc (A + U)%Q V (- A)%Q).
  rewrite <- (Qplus_assoc A U (V + (- A))%Q).
  rewrite (Qplus_assoc U V (- A)%Q).
  rewrite (Qplus_assoc A (U + V)%Q (- A)%Q).
  rewrite (Qplus_comm A (U + V)%Q).
  rewrite <- (Qplus_assoc (U + V)%Q A (- A)%Q).
  rewrite Qplus_opp_r. apply Qplus_0_r.
Qed.

Lemma leiblw_qplus_opp_l0 : forall A X : Q, QeqT (A + (-(A + X)))%Q (- X)%Q.
Proof. intros A X. apply qeq_imp_qeqT. lra. Qed.

(* 反向 shunt：A−((A+U)+V) == −(U+V) *)
Lemma leiblw_qshunt_neg : forall A U V : Q, QeqT (A - ((A + U) + V))%Q (-(U + V))%Q.
Proof.
  intros A U V. apply qeq_imp_qeqT.
  rewrite <- (Qplus_assoc A U V).
  unfold Qminus. exact (qeqT_imp_qeq _ _ (leiblw_qplus_opp_l0 A (U + V)%Q)).
Qed.

Lemma leiblw_qopp_lt : forall x : Q, Qlt 0%Q x -> QltT (- x)%Q 0%Q.
Proof.
  intros x H. apply Qlt_to_QltT. unfold Qlt in *. cbn [Qnum Qden Qopp] in *. lia.
Qed.

Lemma leiblw_qminus_flip : forall x y : Q, QeqT (y - x)%Q (-(x - y))%Q.
Proof. intros x y. apply qeq_imp_qeqT. lra. Qed.

Lemma leiblw_qle_add_r : forall A U : Q, Qle U 0%Q -> QleT' (A + U)%Q A.
Proof. intros A U H. apply Qle_to_QleT'. lra. Qed.

Lemma leiblw_qle_add2_r : forall A U V : Q, Qle (U + V)%Q 0%Q -> QleT' ((A + U) + V)%Q A.
Proof.
  intros A U V H. apply Qle_to_QleT'.
  assert (H2 : Qle (((A + U) + V) - A)%Q 0%Q)
    by (pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt A U V)) as Hs; rewrite Hs; exact H).
  lra.
Qed.

Lemma leiblw_qle_add_l : forall A W : Q, Qle 0%Q W -> QleT' A (A + W)%Q.
Proof. intros A W H. apply Qle_to_QleT'. lra. Qed.

Lemma leiblw_qplus_le0b : forall (a b : Z) (p q : positive),
  (0 <= a * Z.pos q + b * Z.pos p)%Z -> QleT' 0%Q ((a # p) + (b # q))%Q.
Proof.
  intros a b p q H. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qplus_norm a b p q)) as Hn. rewrite Hn.
  unfold Qle. cbn [Qnum Qden]. apply Z.compare_le_iff.
  rewrite Z.mul_0_l, Z.mul_1_r. exact H.
Qed.

Lemma leiblw_zpos_mul : forall j k : nat,
  leiblw_Id (Z.pos (Pos.mul (Pos.of_succ_nat j) (Pos.of_succ_nat k)))
            (Z.of_nat (Datatypes.S j) * Z.of_nat (Datatypes.S k))%Z.
Proof.
  intros j k. apply leiblw_eq_id. rewrite Pos2Z.inj_mul.
  leiblw_ps j. leiblw_ps k. reflexivity.
Qed.

(* Id 面事实 → Prop 面 Z 序的两步转换（goal 含 true 位时 destruct 即代换） *)
Ltac leiblw_id_inv_in Hx :=
  let T := type of Hx in
  match T with
  | leiblw_Id ?x ?y =>
      let He := fresh "Hid" in
      assert (He : x = y) by (destruct Hx; reflexivity);
      clear Hx; rename He into Hx
  end.

(* Id 面 Z 序事实 → Prop 面 Z 序（bool 等词先代换再 Z.leb_le/Z.ltb_lt 投影） *)
Ltac leiblw_zle_of Hx H :=
  let T := type of Hx in
  match T with
  | leiblw_Id (Z.leb ?a ?b) true =>
      let Hb := fresh "Hb" in
      assert (Hb : Z.leb a b = true) by (destruct Hx; reflexivity);
      assert (H : (a <= b)%Z) by (apply (proj1 (Z.leb_le _ _)); exact Hb);
      clear Hb
  end.

Ltac leiblw_zlt_of Hx H :=
  let T := type of Hx in
  match T with
  | leiblw_Id (Z.ltb ?a ?b) true =>
      let Hb := fresh "Hb" in
      assert (Hb : Z.ltb a b = true) by (destruct Hx; reflexivity);
      assert (H : (a < b)%Z) by (apply (proj1 (Z.ltb_lt _ _)); exact Hb);
      clear Hb
  end.

Ltac leiblw_zpmul j k := let H := fresh "Hzm" in
  assert (H : forall a b : nat,
              Z.pos (Pos.mul (Pos.of_succ_nat a) (Pos.of_succ_nat b)) =
              (Z.of_nat (Datatypes.S a) * Z.of_nat (Datatypes.S b))%Z)
    by (intros a b; destruct (leiblw_zpos_mul a b); reflexivity);
  rewrite (H j k).

(* ============================================================ *)
(* §2 (i) 交错余项双侧界：偶支升、奇支降、交织                           *)
(* ============================================================ *)

Lemma leiblw_step_even_pos : forall m : nat,
  QltT 0%Q (leiblw_S (2 * m + 2) - leiblw_S (2 * m))%Q.
Proof.
  intros m. apply Qlt_to_QltT.
  replace (2 * m + 2) with (Datatypes.S (Datatypes.S (2 * m))) by lia.
  cbn [leiblw_S].
  pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt (leiblw_S (2 * m)) (leiblw_t (2 * m))
                                 (leiblw_t (Datatypes.S (2 * m))))) as Hs. rewrite Hs.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_even m)) as Ht1. rewrite Ht1.
  replace (2 * (2 * m)) with (4 * m) by lia.
  replace (Datatypes.S (2 * m)) with (2 * m + 1) by lia.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd m)) as Ht2. rewrite Ht2.
  apply QltT_to_Qlt. apply leiblw_qplus_lt0.
  leiblw_ps (4 * m). leiblw_ps (4 * m + 2).
  assert (H1 : (Z.of_nat (4 * m) + 2 = Z.of_nat (4 * m + 2))%Z).
  { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  lia.
Qed.

Lemma leiblw_step_odd_neg : forall m : nat,
  QltT (leiblw_S (2 * m + 3) - leiblw_S (2 * m + 1))%Q 0%Q.
Proof.
  intros m. apply Qlt_to_QltT.
  replace (2 * m + 3) with (Datatypes.S (Datatypes.S (2 * m + 1))) by lia.
  cbn [leiblw_S].
  pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt (leiblw_S (2 * m + 1)) (leiblw_t (2 * m + 1))
                                 (leiblw_t (Datatypes.S (2 * m + 1))))) as Hs. rewrite Hs.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd m)) as Ht1. rewrite Ht1.
  replace (Datatypes.S (2 * m + 1)) with (2 * m + 2) by lia.
  replace (2 * m + 2) with (2 * (m + 1)) by lia.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_even (m + 1))) as Ht2. rewrite Ht2.
  replace (4 * (m + 1)) with (4 * m + 4) by lia.
  apply QltT_to_Qlt. apply leiblw_qplus_lt0b.
  leiblw_ps (4 * m + 4). leiblw_ps (4 * m + 2).
  assert (H1 : (Z.of_nat (4 * m + 2) + 2 = Z.of_nat (4 * m + 4))%Z).
  { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  lia.
Qed.

Lemma leiblw_interlace : forall m : nat,
  QleT' (leiblw_S (2 * m + 2)) (leiblw_S (2 * m + 1))%Q.
Proof.
  intros m.
  replace (2 * m + 2) with (Datatypes.S (2 * m + 1)) by lia.
  cbn [leiblw_S].
  apply leiblw_qle_add_r.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd m)) as Ht. rewrite Ht.
  unfold Qle. cbn [Qnum Qden]. apply (proj2 (Z.compare_le_iff _ _)).
  leiblw_ps (4 * m + 2). lia.
Qed.

Lemma leiblw_mono_even : forall j m : nat, (m <= j)%nat ->
  QleT' (leiblw_S (2 * m)) (leiblw_S (2 * j))%Q.
Proof.
  intros j m Hm. apply Qle_to_QleT'. revert Hm.
  induction j as [|j IH]; intros Hm.
  - assert (m = 0) by lia. subst. apply Qle_refl.
  - destruct (Nat.eq_dec m (Datatypes.S j)) as [He|Hne].
    + subst. apply Qle_refl.
    + assert (Hmj : (m <= j)%nat) by lia.
      apply (Qle_trans _ (leiblw_S (2 * j))).
      * apply IH. exact Hmj.
      * replace (2 * Datatypes.S j) with (Datatypes.S (Datatypes.S (2 * j))) by lia.
        cbn [leiblw_S].
        rewrite <- (Qplus_assoc (leiblw_S (2 * j)) (leiblw_t (2 * j)) (leiblw_t (Datatypes.S (2 * j)))).
        assert (H0 : Qle 0%Q (leiblw_t (2 * j) + leiblw_t (Datatypes.S (2 * j)))%Q).
        { replace (Datatypes.S (2 * j)) with (2 * j + 1) by lia.
          pose proof (qeqT_imp_qeq _ _ (leiblw_t_even j)) as H1. setoid_rewrite H1.
          pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd j)) as H2. setoid_rewrite H2.
          replace (2 * (2 * j)) with (4 * j) by lia.
          assert (HZ : (0 <= 4 * Z.pos (Pos.of_succ_nat (4 * j + 2))
                              + (-4) * Z.pos (Pos.of_succ_nat (4 * j)))%Z).
          { leiblw_ps (4 * j). leiblw_ps (4 * j + 2).
            assert (H1z : (Z.of_nat (4 * j) + 2 = Z.of_nat (4 * j + 2))%Z).
            { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
            lia. }
          pose proof (leiblw_qplus_le0b 4%Z (-4)%Z
                        (Pos.of_succ_nat (4 * j)) (Pos.of_succ_nat (4 * j + 2)) HZ) as Hq0.
          exact (QleT'_to_Qle _ _ Hq0). }
        exact (QleT'_to_Qle _ _ (leiblw_qle_add_l (leiblw_S (2 * j))
                                   (leiblw_t (2 * j) + leiblw_t (Datatypes.S (2 * j)))%Q H0)).
Qed.

Lemma leiblw_mono_odd : forall j m : nat, (m <= j)%nat ->
  QleT' (leiblw_S (2 * j + 1)) (leiblw_S (2 * m + 1))%Q.
Proof.
  intros j m Hm. apply Qle_to_QleT'. revert Hm.
  induction j as [|j IH]; intros Hm.
  - assert (m = 0) by lia. subst. apply Qle_refl.
  - destruct (Nat.eq_dec m (Datatypes.S j)) as [He|Hne].
    + subst. apply Qle_refl.
    + assert (Hmj : (m <= j)%nat) by lia.
      apply (Qle_trans _ (leiblw_S (2 * j + 1))).
      * replace (2 * Datatypes.S j + 1) with (Datatypes.S (Datatypes.S (2 * j + 1))) by lia.
        cbn [leiblw_S].
        assert (Huv : Qle (leiblw_t (2 * j + 1) + leiblw_t (Datatypes.S (2 * j + 1)))%Q 0%Q).
        { replace (Datatypes.S (2 * j + 1)) with (2 * (j + 1)) by lia.
          pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd j)) as H1. setoid_rewrite H1.
          pose proof (qeqT_imp_qeq _ _ (leiblw_t_even (j + 1))) as H2. setoid_rewrite H2.
          replace (4 * (j + 1)) with (4 * j + 4) by lia.
          assert (HZ : ((-4) * Z.pos (Pos.of_succ_nat (4 * j + 4))
                        + 4 * Z.pos (Pos.of_succ_nat (4 * j + 2)) <= 0)%Z).
          { leiblw_ps (4 * j + 4). leiblw_ps (4 * j + 2).
            assert (H1z : (Z.of_nat (4 * j + 2) + 2 = Z.of_nat (4 * j + 4))%Z).
            { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
            lia. }
          pose proof (leiblw_qplus_le0 (-4)%Z 4%Z
                        (Pos.of_succ_nat (4 * j + 2)) (Pos.of_succ_nat (4 * j + 4)) HZ) as Hq0.
          exact (QleT'_to_Qle _ _ Hq0). }
        exact (QleT'_to_Qle _ _ (leiblw_qle_add2_r (leiblw_S (2 * j + 1)) _ _ Huv)).
      * apply IH. exact Hmj.
Qed.

(* ============================================================ *)
(* §3 显式 gap：gap n := 8/((2n+1)(2n+3))＝同侧相邻部分和步长           *)
(* ============================================================ *)

Definition leiblw_gap (n : nat) : Q :=
  (8 # (Pos.mul (Pos.of_succ_nat (2 * n)) (Pos.of_succ_nat (2 * n + 2))))%Q.

Lemma leiblw_gap_pos : forall n : nat, QltT 0%Q (leiblw_gap n).
Proof.
  intros n. apply Qlt_to_QltT. unfold leiblw_gap.
  unfold Qlt. cbn [Qnum Qden]. apply (proj2 (Z.compare_lt_iff _ _)).
  apply Pos2Z.is_pos.
Qed.

Lemma leiblw_gap_even_step : forall m : nat,
  QeqT (leiblw_S (2 * m + 2) - leiblw_S (2 * m))%Q (leiblw_gap (2 * m)).
Proof.
  intros m. apply qeq_imp_qeqT. unfold leiblw_gap.
  replace (2 * m + 2) with (Datatypes.S (Datatypes.S (2 * m))) by lia.
  cbn [leiblw_S].
  pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt (leiblw_S (2 * m)) (leiblw_t (2 * m))
                                 (leiblw_t (Datatypes.S (2 * m))))) as Hs. rewrite Hs.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_even m)) as Hte. setoid_rewrite Hte.
  replace (2 * (2 * m)) with (4 * m) by lia.
  replace (Datatypes.S (2 * m)) with (2 * m + 1) by lia.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd m)) as Hto. setoid_rewrite Hto.
  apply qeqT_imp_qeq. apply leiblw_qplus_eq.
  leiblw_ps (4 * m). leiblw_ps (4 * m + 2).
  assert (Hw : (Z.pos (Pos.mul (Pos.of_succ_nat (4 * m)) (Pos.of_succ_nat (4 * m + 2))) =
                Z.of_nat (4 * m + 1) * Z.of_nat (4 * m + 3))%Z)
    by (leiblw_zpmul (4 * m) (4 * m + 2); f_equal; lia).
  rewrite Hw.
  assert (H1 : (Z.of_nat (4 * m) + 2 = Z.of_nat (4 * m + 2))%Z).
  { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  assert (H2 : (Z.of_nat (4 * m) + 1 = Z.of_nat (4 * m + 1))%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  assert (H3 : (Z.of_nat (4 * m + 2) + 1 = Z.of_nat (4 * m + 3))%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  nia.
Qed.

Lemma leiblw_gap_odd_step : forall m : nat,
  QeqT (leiblw_S (2 * m + 1) - leiblw_S (2 * m + 3))%Q (leiblw_gap (2 * m + 1)).
Proof.
  intros m. apply qeq_imp_qeqT. unfold leiblw_gap.
  replace (2 * m + 3) with (Datatypes.S (Datatypes.S (2 * m + 1))) by lia.
  cbn [leiblw_S].
  pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt_neg (leiblw_S (2 * m + 1)) (leiblw_t (2 * m + 1))
                                   (leiblw_t (Datatypes.S (2 * m + 1))))) as Hs. rewrite Hs.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd m)) as Hto. setoid_rewrite Hto.
  replace (Datatypes.S (2 * m + 1)) with (2 * m + 2) by lia.
  replace (2 * m + 2) with (2 * (m + 1)) by lia.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_even (m + 1))) as Hte. setoid_rewrite Hte.
  replace (4 * (m + 1)) with (4 * m + 4) by lia.
  replace (2 * (2 * m + 1)) with (4 * m + 2) by lia.
  replace (2 * (2 * m + 1) + 2) with (4 * m + 4) by lia.
  apply qeqT_imp_qeq. apply leiblw_qneg_plus_eq.
  leiblw_ps (4 * m + 4). leiblw_ps (4 * m + 2).
  assert (Hw : (Z.pos (Pos.mul (Pos.of_succ_nat (4 * m + 2)) (Pos.of_succ_nat (4 * m + 4))) =
                Z.of_nat (4 * m + 3) * Z.of_nat (4 * m + 5))%Z)
    by (leiblw_zpmul (4 * m + 2) (4 * m + 4); f_equal; lia).
  rewrite Hw.
  assert (H1 : (Z.of_nat (4 * m + 2) + 2 = Z.of_nat (4 * m + 4))%Z).
  { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  assert (H2 : (Z.of_nat (4 * m + 2) + 1 = Z.of_nat (4 * m + 3))%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  assert (H3 : (Z.of_nat (4 * m + 4) + 1 = Z.of_nat (4 * m + 5))%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  nia.
Qed.

(* ============================================================ *)
(* §4 (ii) 公分母整除性：q'_n := (2n+1)!，q'_n·S_n ∈ Z（见证 P_n）      *)
(* ============================================================ *)

Fixpoint leiblw_zf (n : nat) : Z :=
  match n with
  | 0 => 1%Z
  | Datatypes.S k => Z.pos (Pos.of_succ_nat k) * leiblw_zf k
  end.

Definition leiblw_qf (n : nat) : Q := (leiblw_zf n # 1)%Q.

Lemma leiblw_zf_ge1 : forall n : nat, leiblw_Id (Z.leb 1 (leiblw_zf n)) true.
Proof.
  intros n. apply leiblw_eq_id. apply (proj2 (Z.leb_le _ _)).
  induction n as [|n IH]; cbn [leiblw_zf].
  - lia.
  - pose proof (Pos2Z.is_pos (Pos.of_succ_nat n)). nia.
Qed.

Lemma leiblw_zf_ge_id : forall n : nat, (1 <= n)%nat ->
  leiblw_Id (Z.leb (Z.of_nat n) (leiblw_zf n)) true.
Proof.
  intros n Hn. apply leiblw_eq_id. apply (proj2 (Z.leb_le _ _)).
  replace n with (Datatypes.S (n - 1)) by lia.
  cbn [leiblw_zf]. leiblw_ps (n - 1).
  assert (Hn' : (1 <= Datatypes.S (n - 1))%nat) by lia.
  assert (Hlt : Z.ltb 0 (Z.of_nat (Datatypes.S (n - 1))) = true)
    by (destruct (leiblw_znat_pos (Datatypes.S (n - 1)) Hn'); reflexivity).
  assert (Hn0 : (0 < Z.of_nat (Datatypes.S (n - 1)))%Z)
    by (apply (proj1 (Z.ltb_lt _ _)); exact Hlt).
  pose proof (leiblw_zf_ge1 (n - 1)) as Hg. leiblw_zle_of Hg H1.
  nia.
Qed.

(* zf 的一步/三步原生展开（2n+k 非构造子头，需 replace+cbn） *)
Lemma leiblw_zf_2n1 : forall n : nat,
  leiblw_Id (leiblw_zf (2 * n + 1)) (Z.pos (Pos.of_succ_nat (2 * n)) * leiblw_zf (2 * n))%Z.
Proof.
  intros n. apply leiblw_eq_id.
  replace (2 * n + 1) with (Datatypes.S (2 * n)) by lia.
  cbn [leiblw_zf]. reflexivity.
Qed.

(* (2n+1)! 的原生三因子展开：zf(2n+3) = (2n+3)·(2n+2)·((2n+1)·zf(2n)) *)
Lemma leiblw_zf_2n3 : forall n : nat,
  leiblw_Id (leiblw_zf (2 * n + 3))
            (Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n)))) *
             (Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n))) *
              (Z.pos (Pos.of_succ_nat (2 * n)) * leiblw_zf (2 * n))))%Z.
Proof.
  intros n. apply leiblw_eq_id.
  replace (2 * n + 3) with (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) by lia.
  cbn [leiblw_zf]. reflexivity.
Qed.

Ltac leiblw_zf21 n := let H := fresh "Hzf" in
  assert (H : forall x : nat,
              leiblw_zf (2 * x + 1) = (Z.pos (Pos.of_succ_nat (2 * x)) * leiblw_zf (2 * x))%Z)
    by (intros x; destruct (leiblw_zf_2n1 x); reflexivity);
  rewrite (H n).
Ltac leiblw_zf21_in n Hx := let H := fresh "Hzf" in
  assert (H : forall x : nat,
              leiblw_zf (2 * x + 1) = (Z.pos (Pos.of_succ_nat (2 * x)) * leiblw_zf (2 * x))%Z)
    by (intros x; destruct (leiblw_zf_2n1 x); reflexivity);
  rewrite (H n) in Hx.
Ltac leiblw_zf23 n := let H := fresh "Hzf" in
  assert (H : forall x : nat,
              leiblw_zf (2 * x + 3) =
              (Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * x)))) *
               (Z.pos (Pos.of_succ_nat (Datatypes.S (2 * x))) *
                (Z.pos (Pos.of_succ_nat (2 * x)) * leiblw_zf (2 * x))))%Z)
    by (intros x; destruct (leiblw_zf_2n3 x); reflexivity);
  rewrite (H n).
Theorem leiblw_integrality : forall n : nat,
  sigT (fun p : Z => (leiblw_qf (2 * n + 1) * leiblw_S n)%Q == (p # 1)%Q).
Proof.
  induction n as [|n IH].
  - exists 0%Z. unfold leiblw_qf. cbn [leiblw_zf leiblw_S].
    unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. lia.
  - destruct IH as [p Hp].
    replace (2 * Datatypes.S n + 1) with (2 * n + 3) by lia.
    unfold leiblw_qf in Hp. leiblw_zf21_in n Hp.
    destruct (leiblw_even n) eqn:Hev.
    + exists (Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n)))) *
              (Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n))) *
               (p + 4 * leiblw_zf (2 * n)))%Z)%Z.
      cbn [leiblw_S]. pose proof (qeqT_imp_qeq _ _ (leiblw_t_pos_case n Hev)) as Htp. setoid_rewrite Htp.
      unfold leiblw_qf at 1. leiblw_zf23 n.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) Hp) as Hp2.
      rewrite Z.mul_1_r in Hp2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) +
                     (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite Hp2. ring.
    + exists (Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n)))) *
              (Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n))) *
               (p - 4 * leiblw_zf (2 * n)))%Z)%Z.
      cbn [leiblw_S]. pose proof (qeqT_imp_qeq _ _ (leiblw_t_neg_case n Hev)) as Htp. setoid_rewrite Htp.
      unfold leiblw_qf at 1. leiblw_zf23 n.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) Hp) as Hp2.
      rewrite Z.mul_1_r in Hp2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) -
                     (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite Hp2. ring.
Qed.

(* ============================================================ *)
(* §5 (iii) 边界主件：距离 ≥ gap n（两支各一条）＋Set 面 eps-def 封装     *)
(* ============================================================ *)

(* 偶侧·k 偶：j ≥ m+1 ⟹ S_{2j} − S_{2m} ≥ gap(2m) *)
Lemma leiblw_lower_even_e : forall j m : nat, (m + 1 <= j)%nat ->
  QleT' (leiblw_gap (2 * m)) (leiblw_S (2 * j) - leiblw_S (2 * m))%Q.
Proof.
  intros j m Hj. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (leiblw_gap_even_step m)) as Hg. rewrite <- Hg.
  replace (2 * m + 2) with (2 * (m + 1)) by lia.
  assert (Hme : Qle (leiblw_S (2 * (m + 1))) (leiblw_S (2 * j)))
    by (apply QleT'_to_Qle; apply leiblw_mono_even; lia).
  lra.
Qed.

(* 偶侧·k 奇：j ≥ m ⟹ S_{2j+1} − S_{2m} ≥ gap(2m) *)
Lemma leiblw_lower_even_o : forall j m : nat, (m <= j)%nat ->
  QleT' (leiblw_gap (2 * m)) (leiblw_S (2 * j + 1) - leiblw_S (2 * m))%Q.
Proof.
  intros j m Hj. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (leiblw_gap_even_step m)) as Hg. rewrite <- Hg.
  assert (Hme : Qle (leiblw_S (2 * m + 2)) (leiblw_S (2 * j + 2))).
  { replace (2 * m + 2) with (2 * (m + 1)) by lia.
    replace (2 * j + 2) with (2 * (j + 1)) by lia.
    apply QleT'_to_Qle. apply leiblw_mono_even. lia. }
  assert (Hi : Qle (leiblw_S (2 * j + 2)) (leiblw_S (2 * j + 1)))
    by (apply QleT'_to_Qle; apply leiblw_interlace).
  lra.
Qed.

(* 奇侧·k 偶：j ≥ m+1 ⟹ S_{2m+1} − S_{2j} ≥ gap(2m+1) *)
Lemma leiblw_lower_odd_e : forall j m : nat, (m + 1 <= j)%nat ->
  QleT' (leiblw_gap (2 * m + 1)) ((leiblw_S (2 * m + 1) - leiblw_S (2 * j))%Q).
Proof.
  intros j m Hj. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (leiblw_gap_odd_step m)) as Hstep.
  pose proof (qeqT_imp_qeq _ _ (leiblw_S_step (2 * j))) as Hst.
  assert (Hsyn : (2 * j + 1 = Datatypes.S (2 * j))%nat) by lia.
  rewrite <- Hsyn in Hst.
  pose proof (QltT_to_Qlt _ _ (leiblw_t_even_pos j)) as Hp.
  pose proof (leiblw_mono_odd j (m + 1) Hj) as Hmo. apply QleT'_to_Qle in Hmo.
  replace (2 * (m + 1) + 1) with (2 * m + 3) in Hmo by lia.
  lra.
Qed.

(* 奇侧·k 奇：j ≥ m+1 ⟹ S_{2m+1} − S_{2j+1} ≥ gap(2m+1) *)
Lemma leiblw_lower_odd_o : forall j m : nat, (m + 1 <= j)%nat ->
  QleT' (leiblw_gap (2 * m + 1)) (leiblw_S (2 * m + 1) - leiblw_S (2 * j + 1))%Q.
Proof.
  intros j m Hj. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (leiblw_gap_odd_step m)) as Hg. rewrite <- Hg.
  replace (2 * m + 3) with (2 * (m + 1) + 1) by lia.
  assert (Hle : Qle (leiblw_S (2 * j + 1)) (leiblw_S (2 * (m + 1) + 1)))
    by (apply QleT'_to_Qle; apply leiblw_mono_odd; lia).
  lra.
Qed.

(* 主距离定理（Q 层，两支合一）：k ≥ n+1 ⟹ gap n ≤ |S_k − S_n| *)
Theorem leiblw_dist : forall n k : nat, (Datatypes.S n <= k)%nat ->
  QleT' (leiblw_gap n) (Qabs (leiblw_S k - leiblw_S n))%Q.
Proof.
  intros n k Hk. apply Qle_to_QleT'.
  destruct (leiblw_par_decomp n) as [[m Hm]|Hm].
  - destruct (leiblw_par_decomp k) as [[j Hj]|Hj].
    + assert (Hc : (m + 1 <= j)%nat) by lia.
      pose proof (leiblw_lower_even_e j m Hc) as L. apply QleT'_to_Qle in L.
      assert (Hy : Qle 0%Q ((leiblw_S (2 * j) - leiblw_S (2 * m))%Q)).
      { pose proof (QltT_to_Qlt _ _ (leiblw_gap_pos (2 * m))). lra. }
      pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_id _ Hy)) as E1.
      assert (L2 : Qle (leiblw_gap (2 * m))
                       (Qabs ((leiblw_S (2 * j) - leiblw_S (2 * m))%Q))) by lra.
      exact (eq_ind (2 * m)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j)
                 (fun v => Qle (leiblw_gap (2 * m))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
    + destruct Hj as [j Hj].
      assert (Hc : (m <= j)%nat) by lia.
      pose proof (leiblw_lower_even_o j m Hc) as L. apply QleT'_to_Qle in L.
      assert (Hy : Qle 0%Q ((leiblw_S (2 * j + 1) - leiblw_S (2 * m))%Q)).
      { pose proof (QltT_to_Qlt _ _ (leiblw_gap_pos (2 * m))). lra. }
      pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_id _ Hy)) as E1.
      assert (L2 : Qle (leiblw_gap (2 * m))
                       (Qabs ((leiblw_S (2 * j + 1) - leiblw_S (2 * m))%Q))) by lra.
      exact (eq_ind (2 * m)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j + 1)
                 (fun v => Qle (leiblw_gap (2 * m))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
  - destruct Hm as [m Hm].
    destruct (leiblw_par_decomp k) as [[j Hj]|Hj].
    + assert (Hc : (m + 1 <= j)%nat) by lia.
      pose proof (leiblw_lower_odd_e j m Hc) as L0. apply QleT'_to_Qle in L0.
      assert (Hy2 : Qle ((leiblw_S (2 * j) - leiblw_S (2 * m + 1))%Q) 0%Q).
      { pose proof (QltT_to_Qlt _ _ (leiblw_gap_pos (2 * m + 1))). lra. }
      pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_neg _ Hy2)) as E1.
      pose proof (leiblw_qminus_flip (leiblw_S (2 * m + 1)) (leiblw_S (2 * j))) as Hz.
      assert (L2 : Qle (leiblw_gap (2 * m + 1))
                       (Qabs ((leiblw_S (2 * j) - leiblw_S (2 * m + 1))%Q))) by lra.
      exact (eq_ind (2 * m + 1)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j)
                 (fun v => Qle (leiblw_gap (2 * m + 1))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m + 1))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
    + destruct Hj as [j Hj].
      assert (Hc : (m + 1 <= j)%nat) by lia.
      pose proof (leiblw_lower_odd_o j m Hc) as L0. apply QleT'_to_Qle in L0.
      assert (Hy : Qle ((leiblw_S (2 * j + 1) - leiblw_S (2 * m + 1))%Q) 0%Q).
      { pose proof (QltT_to_Qlt _ _ (leiblw_gap_pos (2 * m + 1))). lra. }
      pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_neg _ Hy)) as E1.
      assert (L2 : Qle (leiblw_gap (2 * m + 1))
                       (Qabs ((leiblw_S (2 * j + 1) - leiblw_S (2 * m + 1))%Q))) by lra.
      exact (eq_ind (2 * m + 1)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j + 1)
                 (fun v => Qle (leiblw_gap (2 * m + 1))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m + 1))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
Qed.

(* Set 值 Q 非严格序判定（≤ 的 bool 判定，Qltb 同工艺；208 增补） *)
Definition leiblw_Qleb (x y : Q) : bool :=
  match Qcompare x y with Gt => false | _ => true end.

Lemma leiblw_Qleb_true : forall x y : Q, Qle x y -> leiblw_Id (leiblw_Qleb x y) true.
Proof.
  intros x y H. apply leiblw_id_eq. unfold leiblw_Qleb.
  destruct (Qcompare_spec x y) as [Heq|Hlt'|Hgt].
  - reflexivity.
  - reflexivity.
  - exfalso. unfold Qgt, Qle in *. cbn [Qnum Qden] in *. nia.
Qed.

(* Set 面 eps-def 封装（S02:48 同形 Id＋bool 判定；208 核对：stdlib QArith 无
   Qlt_bool（QArith_base.v 仅 Qeq_bool/Qle_bool，0930），故以 §0 自备
   leiblw_Qleb 实装；原稿严格序 gap n < |S_k−S_n| 在 k=n+2 取等处为假，
   依 leiblw_dist 改非严格序 gap n ≤ |S_k−S_n|——语句面修正，Set 层不变） *)
Theorem leiblw_dist_set : forall n : nat,
  sigT (fun N : nat => forall k : nat, (N <= k)%nat ->
    leiblw_Id (leiblw_Qleb (leiblw_gap n) (Qabs (leiblw_S k - leiblw_S n))) true).
Proof.
  intros n. exists (Datatypes.S n). intros k Hk.
  apply leiblw_Qleb_true.
  apply QleT'_to_Qle. apply leiblw_dist. exact Hk.
Qed.

(* ============================================================ *)
(* §6 (iv) margin 无界定理＋逃逸窗障碍定理；lic 接口形状重述              *)
(* ============================================================ *)

(* margin_n := q'_n·gap_n = 8·(2n)!/(2n+3)（(ii)+(iii) 的自然见证位残差下界） *)
Definition leiblw_margin (n : nat) : Q := (leiblw_qf (2 * n + 1) * leiblw_gap n)%Q.

(* —— §6 余件（208 续装，0930）：自然认证窗 b·q'_n·|t_n| = 4b·(2n)!
   （188 观察的定理化）：残差律恒等式、自然窗下界/单调、部分和值域 0 ≤ S_n ≤ 4、
   (b) 近极限 q 逃逸窗障碍（窗口不可达主件）、自然窗无界（Set 面）、
   margin 无界（Set 面）。—— *)

(* 自然认证窗：W b n := 4b·(2n)!（= b·q'_n·|t_n|，残差律见下） *)
Definition leiblw_natwin (b n : nat) : Q :=
  (4 * Z.of_nat b * leiblw_zf (2 * n) # 1)%Q.

Lemma leiblw_qabs_make : forall q : Q,
  QeqT (Qabs q) ((Z.abs (Qnum q)) # (Qden q))%Q.
Proof. intros [z p]. apply qeq_imp_qeqT. reflexivity. Qed.

(* 残差律（定理化）：W b n == b·q'_n·|t_n| —— 188 观察的恒等式收束 *)
Lemma leiblw_natwin_residual : forall b n : nat,
  QeqT (leiblw_natwin b n)%Q
       ((Z.of_nat b # 1) * (leiblw_qf (2 * n + 1) * Qabs (leiblw_t n)))%Q.
Proof.
  intros b n. apply qeq_imp_qeqT. unfold leiblw_natwin, leiblw_qf.
  destruct (leiblw_even n) eqn:Hev.
  - pose proof (qeqT_imp_qeq _ _ (leiblw_t_pos_case n Hev)) as Htp. rewrite Htp.
    unfold Qeq. cbn [Qnum Qden Qmult Qopp Pos.mul Qabs Z.abs].
    leiblw_zf21 n. ring.
  - pose proof (qeqT_imp_qeq _ _ (leiblw_t_neg_case n Hev)) as Htp. rewrite Htp.
    unfold Qeq. cbn [Qnum Qden Qmult Qopp Pos.mul Qabs Z.abs].
    leiblw_zf21 n. ring.
Qed.

Lemma leiblw_natwin_ge : forall b n : nat,
  (1 <= b)%nat -> QleT' (4 # 1)%Q (leiblw_natwin b n).
Proof.
  intros b n Hb. apply Qle_to_QleT'. unfold leiblw_natwin.
  unfold Qle. cbn [Qnum Qden]. apply (proj2 (Z.compare_le_iff _ _)).
  pose proof (leiblw_znat_pos b Hb) as Hpz. leiblw_zlt_of Hpz Hp.
  pose proof (leiblw_zf_ge1 (2 * n)) as Hfz. leiblw_zle_of Hfz Hf.
  nia.
Qed.

Lemma leiblw_natwin_mono : forall b n : nat,
  QleT' (leiblw_natwin b n) (leiblw_natwin b (Datatypes.S n)).
Proof.
  intros b n. apply Qle_to_QleT'. unfold leiblw_natwin.
  unfold Qle. cbn [Qnum Qden]. apply (proj2 (Z.compare_le_iff _ _)).
  rewrite !Z.mul_1_r.
  replace (2 * Datatypes.S n) with (Datatypes.S (Datatypes.S (2 * n))) by lia.
  cbn [leiblw_zf].
  leiblw_ps (Datatypes.S (2 * n)). leiblw_ps (2 * n).
  pose proof (Nat2Z.is_nonneg (Datatypes.S (Datatypes.S (2 * n)))) as Ha.
  pose proof (Nat2Z.is_nonneg (Datatypes.S (2 * n))) as Hc.
  pose proof (leiblw_zf_ge1 (2 * n)) as Hfz. leiblw_zle_of Hfz Hf.
  pose proof (Nat2Z.is_nonneg b) as Hd.
  nia.
Qed.

(* 部分和值域：0 ≤ S_n ≤ 4（S_1 = 4 为最大部分和）——障碍定理燃料 *)
Lemma leiblw_S1_4 : QeqT (leiblw_S 1) (4 # 1)%Q.
Proof. apply qeq_imp_qeqT. cbn [leiblw_S leiblw_t leiblw_even]. reflexivity. Qed.

Lemma leiblw_S_le4 : forall n : nat, QleT' (leiblw_S n) (4 # 1)%Q.
Proof.
  intros n. apply Qle_to_QleT'. destruct (leiblw_par_decomp n) as [[j Hj]|[j Hj]].
  - rewrite Hj. destruct j as [|j'].
    + replace (2 * 0) with 0 by lia. cbn [leiblw_S]. unfold Qle. cbn [Qnum Qden].
      apply (proj2 (Z.compare_le_iff _ _)). lia.
    + replace (2 * Datatypes.S j') with (Datatypes.S (2 * j' + 1)) by lia.
      cbn [leiblw_S].
      assert (Ht : Qle (leiblw_t (2 * j' + 1)) 0%Q).
      { pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd j')) as Hto. rewrite Hto.
        assert (Hb : Z.leb ((-4) * Z.pos 1)
                           (0 * Z.pos (Pos.of_succ_nat (4 * j' + 2))) = true)
          by (leiblw_ps (4 * j' + 2); lia).
        unfold Qle. cbn [Qnum Qden].
        apply (proj1 (Z.compare_le_iff _ _)). apply (proj1 (Z.leb_le _ _)). exact Hb. }
      pose proof (leiblw_mono_odd j' 0 (Nat.le_0_l j')) as Hm. apply QleT'_to_Qle in Hm.
      replace (2 * 0 + 1) with 1 in Hm by lia.
      pose proof (qeqT_imp_qeq _ _ leiblw_S1_4) as Hs1.
      lra.
  - pose proof (leiblw_mono_odd j 0 (Nat.le_0_l j)) as Hm. apply QleT'_to_Qle in Hm.
    replace (2 * 0 + 1) with 1 in Hm by lia.
    rewrite Hj.
    pose proof (qeqT_imp_qeq _ _ leiblw_S1_4) as Hs1.
    lra.
Qed.

Lemma leiblw_S_ge0 : forall n : nat, QleT' 0%Q (leiblw_S n).
Proof.
  intros n. apply Qle_to_QleT'. destruct (leiblw_par_decomp n) as [[j Hj]|[j Hj]].
  - rewrite Hj. pose proof (leiblw_mono_even j 0 (Nat.le_0_l j)) as Hm.
    apply QleT'_to_Qle in Hm.
    assert (H0 : leiblw_S (2 * 0) == 0%Q) by reflexivity.
    lra.
  - rewrite Hj. pose proof (leiblw_interlace j) as Hi. apply QleT'_to_Qle in Hi.
    pose proof (leiblw_mono_even (j + 1) 0 (Nat.le_0_l (j + 1))) as Hm.
    apply QleT'_to_Qle in Hm.
    replace (2 * (j + 1)) with (2 * j + 2) in Hm by lia.
    assert (H0 : leiblw_S (2 * 0) == 0%Q) by reflexivity.
    lra.
Qed.

(* |x| ≤ c：双侧夹逼（Qabs 逐点三情形，零经典决策） *)
Lemma leiblw_qabs_bound : forall x c : Q,
  Qle x c -> Qle (- x)%Q c -> QleT' (Qabs x) c.
Proof.
  intros x c H1 H2. apply Qle_to_QleT'.
  destruct x as [z p]. cbn [Qabs]. cbn [Qopp] in H2.
  destruct z as [|z'|z']; [exact H1 | exact H1 | exact H2].
Qed.

(* (b) 窗口不可达主件·近极限 q 的逃逸窗障碍：q 处于第 m 围包 [S_{2m+2}, S_{2m+1}]
   内时，|q − S_n| ≤ 4 < 8 ≤ W b n（2 ≤ b）对一切 n 成立——自然窗下逃逸不可达。
   （Prop 脚手架面：负命题无 Set 形；Set 交付面 = leiblw_dist_set／
   leiblw_natwin_unbounded／leiblw_margin_unbounded） *)
Theorem leiblw_escape_obstacle : forall (b m : nat) (q : Q), (2 <= b)%nat ->
  Qle (leiblw_S (2 * m + 2)) q -> Qle q (leiblw_S (2 * m + 1)) ->
  forall n : nat, QleT' (Qabs ((q - leiblw_S n)%Q)) (leiblw_natwin b n).
Proof.
  intros b m q Hb Hlo Hhi n.
  assert (Hb1 : (1 <= b)%nat) by lia.
  pose proof (leiblw_natwin_ge b n Hb1) as Hw.
  assert (Hq4 : Qle q (4 # 1)%Q).
  { pose proof (leiblw_mono_odd m 0 (Nat.le_0_l m)) as Hm. apply QleT'_to_Qle in Hm.
    replace (2 * 0 + 1) with 1 in Hm by lia.
    pose proof (qeqT_imp_qeq _ _ leiblw_S1_4) as Hs1.
    lra. }
  assert (Hq0 : Qle 0%Q q).
  { pose proof (leiblw_interlace m) as Hi. apply QleT'_to_Qle in Hi.
    pose proof (leiblw_mono_even (m + 1) 0 (Nat.le_0_l (m + 1))) as Hm.
    apply QleT'_to_Qle in Hm.
    replace (2 * (m + 1)) with (2 * m + 2) in Hm by lia.
    assert (H0 : leiblw_S (2 * 0) == 0%Q) by reflexivity.
    lra. }
  assert (Hs4 : Qle (leiblw_S n) (4 # 1)%Q) by (apply QleT'_to_Qle; apply leiblw_S_le4).
  assert (Hs0 : Qle 0%Q (leiblw_S n)) by (apply QleT'_to_Qle; apply leiblw_S_ge0).
  apply Qle_to_QleT'. apply (Qle_trans _ (4 # 1)%Q).
  - assert (Hb2 : QleT' (Qabs ((q - leiblw_S n)%Q)) (4 # 1)%Q).
    { apply leiblw_qabs_bound.
      + lra.
      + pose proof (qeqT_imp_qeq _ _ (leiblw_qminus_flip q (leiblw_S n))) as Hz.
        rewrite <- Hz. lra. }
    exact (QleT'_to_Qle _ _ Hb2).
  - exact (QleT'_to_Qle _ _ Hw).
Qed.

(* (iv) 自然窗无界（Set 面）：任意 nat 界 B 被 n := S (B+B) 处自然窗超越——
   zf(2n) ≥ 2n ≥ B+1 > B 且 4b ≥ 4 *)
Theorem leiblw_natwin_unbounded : forall b B : nat, (1 <= b)%nat ->
  sigT (fun n : nat =>
    leiblw_Id (leiblw_Qltb ((Z.of_nat B # 1)%Q) (leiblw_natwin b n)) true).
Proof.
  intros b B Hb. exists (Datatypes.S (B + B)).
  apply leiblw_Qltb_true.
  unfold leiblw_natwin.
  unfold Qlt. cbn [Qnum Qden]. apply (proj2 (Z.compare_lt_iff _ _)).
  assert (H1 : (1 <= 2 * Datatypes.S (B + B))%nat) by lia.
  pose proof (leiblw_zf_ge_id (2 * Datatypes.S (B + B)) H1) as Hfz. leiblw_zle_of Hfz Hf.
  pose proof (leiblw_znat_pos b Hb) as Hpz. leiblw_zlt_of Hpz Hp.
  pose proof (Nat2Z.is_nonneg B) as Hnn.
  nia.
Qed.

(* (iv) margin 无界（Set 面）：q'_n·gap_n ≥ n+1（n ≥ 2），任意 nat 界被超越——
   (ii)+(iii) 自然见证位残差下界发散（非平凡化定量面） *)
Theorem leiblw_margin_unbounded : forall B : nat,
  sigT (fun n : nat =>
    leiblw_Id (leiblw_Qltb ((Z.of_nat B # 1)%Q) (leiblw_margin n)) true).
Proof.
  intros B. exists (B + 2).
  apply leiblw_Qltb_true.
  unfold leiblw_margin, leiblw_qf, leiblw_gap.
  unfold Qlt. cbn [Qnum Qden]. apply (proj2 (Z.compare_lt_iff _ _)).
  cbn [Qnum Qden Qmult Pos.mul].
  leiblw_zpmul (2 * (B + 2)) (2 * (B + 2) + 2).
  leiblw_zf21 (B + 2).
  assert (Hidx : (2 * (B + 2) = 2 * B + 4)%nat) by lia.
  rewrite Hidx.
  leiblw_ps (2 * B + 4).
  assert (Hidx2 : (2 * B + 4 = Datatypes.S (2 * B + 3))%nat) by lia.
  rewrite Hidx2. cbn [leiblw_zf].
  leiblw_ps (2 * B + 3).
  assert (H1 : (1 <= 2 * B + 3)%nat) by lia.
  pose proof (leiblw_zf_ge_id (2 * B + 3) H1) as Hfz. leiblw_zle_of Hfz Hf3.
  pose proof (Nat2Z.is_nonneg (2 * B + 3)) as Hnn.
  nia.
Qed.

(* —— lic 接口形状重述（UpReqIrrationalCriterion.v :237/:242/:247 同形；
   原件的 Set 序包装＋Prop 合取在本件以 sigT 嵌套＋leiblw_Id 保 Set 层，
   语句内容逐字不变；判定器以 §0 自备 leiblw_Qltb 实装）—— *)

Definition leiblw_lic_tail_bounded (x e : nat -> Q) : Set :=
  forall n k : nat, (1 <= n)%nat -> (n <= k)%nat ->
    leiblw_Id (leiblw_Qltb (Qabs ((x k - x n)%Q)) (e n)) true.

Definition leiblw_lic_escape_window (x e : nat -> Q) : Set :=
  forall q : Q,
    sigT (fun n : nat =>
      sigT (fun _ : (1 <= n)%nat =>
        leiblw_Id (leiblw_Qltb (e n) (Qabs ((q - x n)%Q))) true)).

Definition leiblw_lic_vanish (e : nat -> Q) : Set :=
  forall eps : Q, leiblw_Id (leiblw_Qltb 0%Q eps) true ->
    sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
      leiblw_Id (leiblw_Qltb (e n) eps) true).

(* ============================================================ *)
(* §7 (c) 族定理非平凡化：阶乘族（Niven 型）认证窗有界 vs Leibniz 族
   自然窗无界的分离对照（论文面新小节素材：只证不写文）                *)
(* ============================================================ *)

(* 阶乘族认证窗（Niven 型）：w_niv n := 1/(2n+1)——q·δ ≤ 1/(2n+1) < 1 的
   认证残差窗标准形（判据可达族的窗口形状） *)
Definition leiblw_nivwin (n : nat) : Q := (1 # Pos.of_succ_nat (n + n + 1))%Q.

(* 阶乘族窗 ≤ 1 恒成立（有界）——与 leiblw_natwin_unbounded 分离 *)
Theorem leiblw_nivwin_bounded : forall n : nat, QleT' (leiblw_nivwin n) 1%Q.
Proof.
  intros n. apply Qle_to_QleT'. unfold leiblw_nivwin.
  unfold Qle. cbn [Qnum Qden]. apply (proj2 (Z.compare_le_iff _ _)).
  pose proof (Pos2Z.is_pos (Pos.of_succ_nat (n + n + 1))). nia.
Qed.

(* 分离对照主句（Set 面）：Leibniz 自然窗在 n=1 即超 1（4·(2·1)! = 8 > 1），
   而阶乘族窗恒 ≤ 1（leiblw_nivwin_bounded）——「窗 ≤ 1」非平凡性判准对
   Niven 族可达、对 Leibniz 族不可达 *)
Theorem leiblw_family_separation :
  sigT (fun n : nat => leiblw_Id (leiblw_Qltb 1%Q (leiblw_natwin 1 n)) true).
Proof.
  exists 1. apply leiblw_Qltb_true.
  unfold leiblw_natwin.
  unfold Qlt. cbn [Qnum Qden]. apply (proj2 (Z.compare_lt_iff _ _)).
  replace (2 * 1) with 2 by lia.
  cbn [leiblw_zf Z.of_nat Pos.of_succ_nat]. lia.
Qed.

(* ============================================================ *)
(* §8 计算面抽查＋Set 交付面提取＋全局公理审计（尾 PA）                  *)
(* ============================================================ *)

(* 边距表 vm_compute 抽查：margin n = 8·(2n)!/(2n+3) 前四项 *)
Lemma leiblw_margin_tbl :
  And (QeqT (leiblw_margin 0) (8 # 3)%Q)
       (And (QeqT (leiblw_margin 1) (16 # 5)%Q)
            (And (QeqT (leiblw_margin 2) (192 # 7)%Q)
                 (QeqT (leiblw_margin 3) (640 # 1)%Q))).
Proof.
  repeat split; vm_compute; apply id_refl.
Qed.

(* 自然窗表抽查：W 1 n = 4·(2n)! 前四项（发散直观） *)
Lemma leiblw_natwin_tbl :
  And (QeqT (leiblw_natwin 1 0) (4 # 1)%Q)
       (And (QeqT (leiblw_natwin 1 1) (8 # 1)%Q)
            (And (QeqT (leiblw_natwin 1 2) (96 # 1)%Q)
                 (QeqT (leiblw_natwin 1 3) (2880 # 1)%Q))).
Proof.
  repeat split; vm_compute; apply id_refl.
Qed.

(* Set 交付面提取（G3 关：提取面魔数计数须为零；E887 卡：9.1 须前置 Require） *)
From Stdlib Require Import Extraction.
Separate Extraction leiblw_dist_set leiblw_natwin leiblw_gap leiblw_nivwin.

(* 尾 Print Assumptions（G4 关：全部 Closed under the global context） *)
Print Assumptions leiblw_dist.
Print Assumptions leiblw_integrality.
Print Assumptions leiblw_dist_set.
Print Assumptions leiblw_natwin_residual.
Print Assumptions leiblw_natwin_unbounded.
Print Assumptions leiblw_margin_unbounded.
Print Assumptions leiblw_escape_obstacle.
Print Assumptions leiblw_nivwin_bounded.
Print Assumptions leiblw_family_separation.
Print Assumptions leiblw_margin_tbl.
Print Assumptions leiblw_natwin_tbl.

(* ============================================================ *)
(* §9 方案 B·计算证书器（调度段 0930 钉定；另起段不动 §0-§8 存量）   *)
(*   核心零战术：pof/cert_core 为纯程序（Fixpoint/Definition），vm_compute    *)
(*   收敛即证；规格语句 Set 面（forall n＋sigT＋积型合取）；见证包＝          *)
(*   交错余项上/下界两个 Q 值＋公分母 (2n+1)! 整除见证 P_n＋边距 gap 值。    *)
(* ============================================================ *)

(* P_n 公分母整除见证：零战术 Fixpoint（仿写 §4 integrality 构造步：
   p_{k+1} = (2k+3)·(2k+2)·(p_k ± 4·zf(2k))，± 随 k 奇偶） *)
Fixpoint leiblw_pof (n : nat) : Z :=
  match n with
  | 0 => 0%Z
  | Datatypes.S k =>
      Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * k)))) *
      (Z.pos (Pos.of_succ_nat (Datatypes.S (2 * k))) *
       (match leiblw_even k with
        | true => leiblw_pof k + 4 * leiblw_zf (2 * k)
        | false => leiblw_pof k - 4 * leiblw_zf (2 * k)
        end)%Z)
  end.

Ltac leiblw_d2e m := let H := fresh "Hd2" in
  assert (H : Nat.div2 (2 * m) = m) by (apply Nat.div2_double);
  rewrite H.
Ltac leiblw_d2e_in m Hx := let H := fresh "Hd2" in
  assert (H : Nat.div2 (2 * m) = m) by (apply Nat.div2_double);
  rewrite H in Hx.
Ltac leiblw_d2o m := let H := fresh "Hd2" in
  assert (H : Nat.div2 (2 * m + 1) = m)
    by (replace (2 * m + 1) with (Datatypes.S (2 * m)) by lia;
        apply Nat.div2_succ_double);
  rewrite H.

(* P_n 规格（Set 面语句·归纳＋Set 值 IH＋Qeq_bool 计算闭合） *)
Lemma leiblw_pof_spec : forall n : nat,
  leiblw_Id (Qeq_bool (leiblw_qf (2 * n + 1) * leiblw_S n) (leiblw_pof n # 1)) true.
Proof.
  induction n as [|n IH].
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    cbn [leiblw_pof leiblw_qf leiblw_zf leiblw_S Qnum Qden Qmult]. lra.
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    leiblw_id_inv_in IH. apply (proj1 (Qeq_bool_iff _ _)) in IH.
    unfold leiblw_qf in IH. leiblw_zf21_in n IH.
    replace (2 * Datatypes.S n + 1) with (2 * n + 3) by lia.
    cbn [leiblw_pof]. destruct (leiblw_even n) eqn:Hev.
    + cbn [leiblw_S]. pose proof (qeqT_imp_qeq _ _ (leiblw_t_pos_case n Hev)) as Htp. setoid_rewrite Htp.
      unfold leiblw_qf at 1. leiblw_zf23 n.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) IH) as IH2.
      rewrite Z.mul_1_r in IH2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) + (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite IH2. ring.
    + cbn [leiblw_S]. pose proof (qeqT_imp_qeq _ _ (leiblw_t_neg_case n Hev)) as Htp. setoid_rewrite Htp.
      unfold leiblw_qf at 1. leiblw_zf23 n.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) IH) as IH2.
      rewrite Z.mul_1_r in IH2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) - (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite IH2. ring.
Qed.

(* 证书器核心：纯数据四元组（lo 下界见证, hi 上界见证, P_n, gap 值）——零战术 *)
Definition leiblw_cert_core (n : nat) : (Q * (Q * (Z * Q)))%type :=
  (leiblw_S (2 * Nat.div2 n),
   (leiblw_S (2 * Nat.div2 n + 1),
    (leiblw_pof n, leiblw_gap n))).

(* 证书器（①形：forall n＋sigT＋积型合取·Set 面；三核检全为 Id+Qeq_bool） *)
Theorem leiblw_cert : forall n : nat,
  sigT (fun lo : Q =>
    sigT (fun hi : Q =>
      sigT (fun p : Z =>
        sigT (fun g : Q =>
          (leiblw_Id (Qeq_bool ((hi - lo)%Q) (leiblw_t (2 * Nat.div2 n))) true *
           (leiblw_Id (Qeq_bool (leiblw_qf (2 * n + 1) * leiblw_S n) (p # 1)) true *
            leiblw_Id (Qeq_bool (p # 1) (leiblw_qf (2 * n + 1) * leiblw_S n)) true))%type)))).
Proof.
  intros n.
  exists (leiblw_S (2 * Nat.div2 n)).
  exists (leiblw_S (2 * Nat.div2 n + 1)).
  exists (leiblw_pof n). exists (leiblw_gap n).
  split.
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    destruct (leiblw_par_decomp n) as [[m Hm]|[m Hm]].
    + rewrite Hm. leiblw_d2e m.
      replace (2 * m + 1) with (Datatypes.S (2 * m)) by lia.
      cbn [leiblw_S].
      match goal with |- ?G => idtac "TLW208P3:" G end.
      lra.
    + rewrite Hm. leiblw_d2o m.
      replace (2 * m + 1) with (Datatypes.S (2 * m)) by lia.
      cbn [leiblw_S].
      lra.
  - split.
    + exact (leiblw_pof_spec n).
    + apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
      pose proof (leiblw_pof_spec n) as Hps.
      leiblw_id_inv_in Hps. apply (proj1 (Qeq_bool_iff _ _)) in Hps.
      apply Qeq_sym. exact Hps.
Qed.

(* 可执行演示（⑦/G5）：vm_compute 收敛实录——三发 n=1,2,3 *)
Eval vm_compute in (leiblw_cert_core 1).
Eval vm_compute in (leiblw_cert_core 2).
Eval vm_compute in (leiblw_cert_core 3).

(* G3 增强：证书器本体可提取 *)
Separate Extraction leiblw_pof leiblw_cert_core.

(* 尾 Print Assumptions（§9 面：G4 关） *)
Print Assumptions leiblw_pof_spec.
Print Assumptions leiblw_cert.

(* ============================================================ *)
(* §10 实层胶合段（219 段·LeibWindow 实层胶合，0930）           *)
(*   使命：以 S02 eps-def 面直造「极限到部分和距离 ≥ 兄弟 gap」实层定理：    *)
(*     证书器 lo/hi/g 直供 eps-def 谓词位。                              *)
(*   依赖：本件 §9 证书器输出（leiblw_cert_core 访问器形）＋本件 §4 交错界  *)
(*     存量（leiblw_gap_even_step/gap_odd_step/mono_even/mono_odd/       *)
(*     interlace/qabs_bound/t_even_pos）＋库面 S01_BaseRing/S02_         *)
(*     CauchyComplete（Real/real_eq/real_lt/real_const/QleT'/QltT/      *)
(*     NatLe＝Nat.leb 证书面；Main vo 树，S02 全闭包 coqchk 公理段       *)
(*     <none> 核对 0930＝_tlw219_coqchk_s02.log）。               *)
(*   构造性：语句面全 Set（sigT/real_lt/real_eq/And/QleT'/QltT/leiblw_Id  *)
(*     积型）；零 ==/Qeq 断言、零 lia 语句原子；nat 序＝NatLe 证书面；      *)
(*     Qeq 移写走 bool 判定面 eq 重写（零 Prop 传输）；证内 Q 层 lra 与     *)
(*     nat 计数 lia 脚手架按 §0-§9 存量工艺。零公理（尾 PA 增列 8）。      *)
(*   对标：S02_CauchyComplete.v :48（QltT＝Id＋bool 判定器 eps-def 同形）、  *)
(*     :399 real_eq、:468 real_lt、:859 real_const；本件 §9 核检①（宽度    *)
(*     hi−lo＝t(2·div2 n)）在胶合供件形上重立。                          *)
(*   编译：同文件头配方（S01/S02 由 Main vo 树 -Q 挂根供给，零新增配方）。  *)
(* ============================================================ *)

Require Import S01_BaseRing S02_CauchyComplete.
Local Open Scope nat_scope.

(* —— §10.0 证书器组件访问器：§9 输出的实层供件形 —— *)
Definition leiblw_env_lo (n : nat) : Q := fst (leiblw_cert_core n).
Definition leiblw_env_hi (n : nat) : Q := fst (snd (leiblw_cert_core n)).
Definition leiblw_env_g (n : nat) : Q := snd (snd (snd (leiblw_cert_core n))).

(* 端点核验（leiblw_Id＋Qeq_bool 面，§9 同形）：访问器值＝部分和端点/兄弟 gap 本值 *)
Lemma leiblw_env_lo_val : forall n : nat,
  leiblw_Id (Qeq_bool (leiblw_env_lo n) (leiblw_S (2 * Nat.div2 n))) true.
Proof.
  intros n. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
  cbn [leiblw_env_lo leiblw_cert_core fst]. apply Qeq_refl.
Qed.

Lemma leiblw_env_hi_val : forall n : nat,
  leiblw_Id (Qeq_bool (leiblw_env_hi n) (leiblw_S (2 * Nat.div2 n + 1))) true.
Proof.
  intros n. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
  cbn [leiblw_env_hi leiblw_cert_core fst snd]. apply Qeq_refl.
Qed.

Lemma leiblw_env_g_val : forall n : nat,
  leiblw_Id (Qeq_bool (leiblw_env_g n) (leiblw_gap n)) true.
Proof.
  intros n. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
  cbn [leiblw_env_g leiblw_cert_core fst snd]. apply Qeq_refl.
Qed.

(* §9 核检①（宽度 hi−lo＝t(2·div2 n)）在胶合供件形上重立——证书器使用面 *)
Lemma leiblw_cert_width_check : forall n : nat,
  leiblw_Id (Qeq_bool ((leiblw_env_hi n - leiblw_env_lo n)%Q)
                       (leiblw_t (2 * Nat.div2 n))) true.
Proof.
  intros n. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
  destruct (leiblw_par_decomp n) as [[m Hm]|[m Hm]].
  - rewrite Hm.
    cbn [leiblw_env_hi leiblw_env_lo leiblw_cert_core fst snd].
    leiblw_d2e m.
    replace (2 * m + 1) with (Datatypes.S (2 * m)) by (symmetry; apply Nat.add_1_r).
    cbn [leiblw_S].
    pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt (leiblw_S (2 * m)) (leiblw_t (2 * m)) 0%Q)) as Hs.
    rewrite (Qplus_0_r (leiblw_S (2 * m) + leiblw_t (2 * m))) in Hs.
    rewrite (Qplus_0_r (leiblw_t (2 * m))) in Hs.
    exact Hs.
  - rewrite Hm.
    cbn [leiblw_env_hi leiblw_env_lo leiblw_cert_core fst snd].
    leiblw_d2o m.
    replace (2 * m + 1) with (Datatypes.S (2 * m)) by (symmetry; apply Nat.add_1_r).
    cbn [leiblw_S].
    pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt (leiblw_S (2 * m)) (leiblw_t (2 * m)) 0%Q)) as Hs.
    rewrite (Qplus_0_r (leiblw_S (2 * m) + leiblw_t (2 * m))) in Hs.
    rewrite (Qplus_0_r (leiblw_t (2 * m))) in Hs.
    exact Hs.
Qed.

(* Qeq 同值移写（bool 判定面 eq 层重写，Set 合法零 Prop 传输；
   Qcompare_comp＝QArith_base :537 Proper 实例，S02 real_const 同款用法） *)
Lemma leiblw_QltT_comp_l : forall x y z : Q,
  leiblw_Id (Qeq_bool x y) true -> QltT x z -> QltT y z.
Proof.
  intros x y z Hxy H. leiblw_id_inv_in Hxy.
  apply (proj1 (Qeq_bool_iff _ _)) in Hxy.
  unfold QltT, Qlt_bool in *.
  rewrite (Qcompare_comp x y Hxy z z (Qeq_refl z)) in H. exact H.
Qed.

Lemma leiblw_QltT_comp_r : forall x y z : Q,
  leiblw_Id (Qeq_bool y z) true -> QltT x y -> QltT x z.
Proof.
  intros x y z Hyz H. leiblw_id_inv_in Hyz.
  apply (proj1 (Qeq_bool_iff _ _)) in Hyz.
  unfold QltT, Qlt_bool in *.
  rewrite (Qcompare_comp x x (Qeq_refl x) y z Hyz) in H. exact H.
Qed.

Lemma leiblw_QleT'_comp_l : forall x y z : Q,
  leiblw_Id (Qeq_bool x y) true -> QleT' x z -> QleT' y z.
Proof.
  intros x y z Hxy H. leiblw_id_inv_in Hxy.
  apply (proj1 (Qeq_bool_iff _ _)) in Hxy.
  unfold QleT', Qle_bool in *.
  rewrite (Qcompare_comp x y Hxy z z (Qeq_refl z)) in H. exact H.
Qed.

Lemma leiblw_QleT'_comp_r : forall x y z : Q,
  leiblw_Id (Qeq_bool y z) true -> QleT' x y -> QleT' x z.
Proof.
  intros x y z Hyz H. leiblw_id_inv_in Hyz.
  apply (proj1 (Qeq_bool_iff _ _)) in Hyz.
  unfold QleT', Qle_bool in *.
  rewrite (Qcompare_comp x x (Qeq_refl x) y z Hyz) in H. exact H.
Qed.

(* 宽度值正性（(i) 宽度见证使用）：核检① × t_{2·div2 n} > 0 存量——
   围包非退化性证书 *)
Lemma leiblw_glue_width_pos : forall m : nat,
  QltT 0%Q ((leiblw_env_hi (2 * m) - leiblw_env_lo (2 * m))%Q).
Proof.
  intros m.
  pose proof (leiblw_cert_width_check (2 * m)) as Hc.
  leiblw_id_inv_in Hc.
  apply (proj1 (Qeq_bool_iff _ _)) in Hc.
  leiblw_d2e_in m Hc.
  apply (leiblw_QltT_comp_r 0%Q (leiblw_t (2 * m))).
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)). symmetry. exact Hc.
  - exact (leiblw_t_even_pos m).
Qed.

(* —— §10.1 eps-def 胶合升桥（谓词＝库 Set 面 real_lt/real_eq；S02 :48 同形） —— *)

(* 升桥·下侧：u j ≥ c 终成立 ⟹ ∀d>0，real_lt (real_const (c−d)) x
   （「x₀ ≥ c」的 δ 收缩构造形——实层 ≥ 经严格 eps-def 面） *)
Lemma leiblw_lift_low : forall (x : Real) (c : Q),
  sigT (fun N : nat => forall j : nat, NatLe N j -> QleT' c (projT1 x j)) ->
  forall d : Q, QltT 0 d -> real_lt (real_const ((c - d)%Q)) x.
Proof.
  intros x c [N HN] d Hd. unfold real_lt.
  exists (d / 2)%Q. split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l.
    + reflexivity.
    + simpl. apply QltT_to_Qlt. exact Hd.
  - exists N. intros j Hj.
    specialize (HN j Hj). apply QleT'_to_Qle in HN.
    pose proof (QltT_to_Qlt 0 d Hd) as Hdp.
    apply Qlt_to_QltT.
    change (projT1 (real_const ((c - d)%Q)) j) with ((c - d)%Q).
    apply (Qlt_shift_div_r d (2 # 1)%Q ((projT1 x j - (c - d))%Q)).
    + reflexivity.
    + lra.
Qed.

(* 升桥·上侧（仿写）：u j ≤ c 终成立 ⟹ ∀d>0，real_lt x (real_const (c+d)) *)
Lemma leiblw_lift_high : forall (x : Real) (c : Q),
  sigT (fun N : nat => forall j : nat, NatLe N j -> QleT' (projT1 x j) c) ->
  forall d : Q, QltT 0 d -> real_lt x (real_const ((c + d)%Q)).
Proof.
  intros x c [N HN] d Hd. unfold real_lt.
  exists (d / 2)%Q. split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l.
    + reflexivity.
    + simpl. apply QltT_to_Qlt. exact Hd.
  - exists N. intros j Hj.
    specialize (HN j Hj). apply QleT'_to_Qle in HN.
    pose proof (QltT_to_Qlt 0 d Hd) as Hdp.
    apply Qlt_to_QltT.
    change (projT1 (real_const ((c + d)%Q)) j) with ((c + d)%Q).
    apply (Qlt_shift_div_r d (2 # 1)%Q (((c + d) - projT1 x j)%Q)).
    + reflexivity.
    + lra.
Qed.

(* 升桥·等词（库 Set 面 real_eq 使用）：u j＝c 终成立（QleT' 双侧证书）
   ⟹ real_eq x (real_const c)——S02 real_const 自证同工艺（Qeq_trans 链） *)
Lemma leiblw_lift_eq : forall (x : Real) (c : Q),
  sigT (fun N : nat => forall j : nat, NatLe N j ->
    And (QleT' c (projT1 x j)) (QleT' (projT1 x j) c)) ->
  real_eq x (real_const c).
Proof.
  intros x c [N HN] eps Heps. unfold real_eq.
  exists N. intros j Hj. specialize (HN j Hj). destruct HN as [H1 H2].
  apply QleT'_to_Qle in H1. apply QleT'_to_Qle in H2.
  assert (Hant : projT1 x j == c) by (apply Qle_antisym; [exact H2 | exact H1]).
  assert (Hz : Qabs ((projT1 x j - c)%Q) == 0%Q).
  { setoid_rewrite Hant.
    apply (Qeq_trans _ (Qabs 0%Q) _).
    - apply Qabs_wd. ring.
    - apply (Qeq_trans _ (- 0)%Q _).
      + apply Qabs_neg. apply Qle_refl.
      + apply Qeq_refl. }
  pose proof (QltT_to_Qlt 0 eps Heps) as Hlt0.
  apply Qlt_to_QltT. cbn [real_const projT1].
  setoid_rewrite Hz. exact Hlt0.
Qed.

(* —— §10.2 宽度见证（③）：列终入围包 ⟹ |x₀−lo| ≤ hi−lo
   —— §4 交错界存量（leiblw_qabs_bound）支撑，宽度值即 §9 核检①载荷 —— *)
Lemma leiblw_glue_width : forall (m : nat) (x : Real),
  sigT (fun N : nat => forall j : nat, NatLe N j ->
    And (QleT' (leiblw_env_lo (2 * m)) (projT1 x j))
        (QleT' (projT1 x j) (leiblw_env_hi (2 * m)))) ->
  sigT (fun N0 : nat => forall j : nat, NatLe N0 j ->
    QleT' (Qabs ((projT1 x j - leiblw_env_lo (2 * m))%Q))
          ((leiblw_env_hi (2 * m) - leiblw_env_lo (2 * m))%Q)).
Proof.
  intros m x [N HN]. exists N. intros j Hj.
  specialize (HN j Hj). destruct HN as [Hlo Hhi].
  apply QleT'_to_Qle in Hlo. apply QleT'_to_Qle in Hhi.
  apply leiblw_qabs_bound; lra.
Qed.

(* —— §10.3 主胶合定理：「极限到部分和距离 ≥ 兄弟 gap」
   ——证书器 lo/hi/g 直供 eps-def 谓词位。
   带归属假设＝x₀ 代表列终入内缘带 [S_{2m+2}, S_{2m+3}]（第 m/(m+1) 围包
   内缘带，极限的界定性质形；lo+g＝S_{2m+2} 与 hi−g＝S_{2m+3} 由 §3
   gap_even_step/gap_odd_step 存量等值，见 §10.4 带归属实例）：
   下侧 dist(x₀, lo) ≥ env_g(2m)＝lo 的兄弟 gap（x₀ ≥ lo+gap(2m) 的 δ 收缩形）；
   上侧 dist(x₀, hi) ≥ env_g(2m+1)＝hi 的兄弟 gap（x₀ ≤ hi−gap(2m+1) 的 δ 收缩形）。 *)
Theorem leiblw_glue_dist : forall (m : nat) (x : Real),
  sigT (fun N : nat => forall j : nat, NatLe N j ->
    And (QleT' ((leiblw_env_lo (2 * m) + leiblw_env_g (2 * m))%Q) (projT1 x j))
        (QleT' (projT1 x j)
               ((leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1))%Q))) ->
  And (forall d : Q, QltT 0 d ->
        real_lt (real_const (((leiblw_env_lo (2 * m) + leiblw_env_g (2 * m)) - d)%Q)) x)
      (forall d : Q, QltT 0 d ->
        real_lt x (real_const (((leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1)) + d)%Q))).
Proof.
  intros m x [N HN].
  assert (Hlow : sigT (fun N0 : nat => forall j : nat, NatLe N0 j ->
            QleT' ((leiblw_env_lo (2 * m) + leiblw_env_g (2 * m))%Q) (projT1 x j))).
  { exists N. intros j Hj. specialize (HN j Hj). destruct HN as [H1 _]. exact H1. }
  assert (Hhigh : sigT (fun N0 : nat => forall j : nat, NatLe N0 j ->
            QleT' (projT1 x j)
                  ((leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1))%Q))).
  { exists N. intros j Hj. specialize (HN j Hj). destruct HN as [_ H2]. exact H2. }
  split.
  - intros d Hd. exact (leiblw_lift_low x _ Hlow d Hd).
  - intros d Hd. exact (leiblw_lift_high x _ Hhigh d Hd).
Qed.

(* —— §10.4 带归属实例（胶合假设的非空性见证）：部分和列自身 j ≥ 2m+3
   终入内缘带——(i) 交错界存量（mono_even/mono_odd/interlace）直供；
   等值桥 lo+g＝S_{2m+2}、hi−g＝S_{2m+3} 由 §3 gap 步长存量承载。
   （真极限 Real 的构造＝cauchy 见证＋t_n→0 消没，候后续段；本件交付
   「证书器×交错界→实层面」直连。） *)
Lemma leiblw_glue_band_S : forall (m j : nat), NatLe (2 * m + 3) j ->
  And (QleT' ((leiblw_env_lo (2 * m) + leiblw_env_g (2 * m))%Q) (leiblw_S j))
      (QleT' (leiblw_S j)
             ((leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1))%Q)).
Proof.
  intros m j Hj. apply NatLe_drop in Hj.
  assert (HvL : leiblw_S (2 * m + 2)
                == (leiblw_env_lo (2 * m) + leiblw_env_g (2 * m))%Q).
  { cbn [leiblw_env_lo leiblw_env_g leiblw_cert_core fst snd].
    leiblw_d2e m.
    pose proof (qeqT_imp_qeq _ _ (leiblw_gap_even_step m)). lra. }
  assert (HvH : (leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1))%Q
                == leiblw_S (2 * m + 3)).
  { cbn [leiblw_env_hi leiblw_env_g leiblw_cert_core fst snd].
    leiblw_d2o m.
    pose proof (qeqT_imp_qeq _ _ (leiblw_gap_odd_step m)). lra. }
  split.
  - apply (leiblw_QleT'_comp_l (leiblw_S (2 * m + 2)));
      [apply leiblw_id_eq; apply (proj2 (Qeq_bool_iff _ _)); exact HvL|].
    apply Qle_to_QleT'.
    destruct (leiblw_par_decomp j) as [[i Hi]|[i Hi]]; rewrite Hi.
    + assert (Hij : (m + 1 <= i)%nat) by lia.
      pose proof (leiblw_mono_even i (m + 1) Hij) as H1. apply QleT'_to_Qle in H1.
      replace (2 * (m + 1)) with (2 * m + 2) in H1 by lia.
      lra.
    + assert (Hij : (m + 1 <= i)%nat) by lia.
      pose proof (leiblw_mono_even i (m + 1) Hij) as H1. apply QleT'_to_Qle in H1.
      pose proof (QltT_to_Qlt _ _ (leiblw_t_even_pos i)) as Ht.
      pose proof (QleT'_to_Qle _ _ (leiblw_qle_add_l (leiblw_S (2 * i)) (leiblw_t (2 * i))
                    (Qlt_le_weak _ _ Ht))) as H3.
      pose proof (qeqT_imp_qeq _ _ (leiblw_S_step (2 * i))) as H4.
      replace (2 * (m + 1)) with (2 * m + 2) in H1 by lia.
      replace (2 * i + 1) with (Datatypes.S (2 * i)) by (symmetry; apply Nat.add_1_r).
      lra.
  - apply (leiblw_QleT'_comp_r (leiblw_S j) (leiblw_S (2 * m + 3)));
      [apply leiblw_id_eq; apply (proj2 (Qeq_bool_iff _ _)); symmetry; exact HvH|].
    apply Qle_to_QleT'.
    destruct (leiblw_par_decomp j) as [[i Hi]|[i Hi]]; rewrite Hi.
    + assert (Hij : (m + 2 <= i)%nat) by lia.
      destruct i as [|i']; [lia|].
      assert (Hij2 : (m + 1 <= i')%nat) by lia.
      pose proof (leiblw_interlace i') as H2. apply QleT'_to_Qle in H2.
      pose proof (leiblw_mono_odd i' (m + 1) Hij2) as H3. apply QleT'_to_Qle in H3.
      replace (2 * (m + 1) + 1) with (2 * m + 3) in H3 by lia.
      replace (2 * Datatypes.S i') with (2 * i' + 2) by lia.
      lra.
    + assert (Hij : (m + 1 <= i)%nat) by lia.
      pose proof (leiblw_mono_odd i (m + 1) Hij) as H3. apply QleT'_to_Qle in H3.
      replace (2 * (m + 1) + 1) with (2 * m + 3) in H3 by lia.
      lra.
Qed.

(* —— §10.5 可执行演示（G5）与公理审计 —— *)
(* 证书器访问器三件套 vm_compute 实录（与 §9 演示值对账：n=1 → (0, 4, 8#15)，
   n=2 → (8#3, 52#15, 8#35)） *)
Eval vm_compute in (leiblw_env_lo 1, (leiblw_env_hi 1, leiblw_env_g 1)).
Eval vm_compute in (leiblw_env_lo 2, (leiblw_env_hi 2, leiblw_env_g 2)).

(* 尾 Print Assumptions（§10 面：G4 关，PA 只增不破——承 208 十三×Closed） *)
Print Assumptions leiblw_cert_width_check.
Print Assumptions leiblw_lift_low.
Print Assumptions leiblw_lift_high.
Print Assumptions leiblw_lift_eq.
Print Assumptions leiblw_glue_width_pos.
Print Assumptions leiblw_glue_width.
Print Assumptions leiblw_glue_band_S.
Print Assumptions leiblw_glue_dist.
(* ============================================================ *)
(* §11 真极限 Real 构造（232 段·LeibWindow 真极限构造，0930）    *)
(*   使命（219 候令①）：以 S02 cauchy 机器构造 x₀＝级数自身 cauchy-real *)
(*   极限（不认领 π/4——194 设计铁律：分离论证只需要「这个族有多慢」，  *)
(*   不需要「它等于多少」）；|t_n|→0 消没见证＝§4 交错余项界存量直供；     *)
(*   置入后实例化 leiblw_glue_dist＋leiblw_glue_band_S——胶合假设非空、    *)
(*   主胶合定理对真 x₀ 成立＝边界定理线全通。                            *)
(*   面：win_even/odd（尾部围包 QleT' 双侧——mono_even/mono_odd/          *)
(*   interlace＋S_step＋t_even_pos 存量直供）＋win_width（Id＋Qeq_bool    *)
(*   宽度等值＝|t_N| 本值）＋S_pair_win_even/odd＋S_pair_abs_t           *)
(*   （|S_m−S_n| ≤ |t_N|，qabs_bound 存量使用）＋t_abs＋t_vanish          *)
(*   （|t_n|→0 消没见证：nat 见证 N := 4·(Qden eps)+1，4/(2n+1)＜eps 的   *)
(*   Z 面单调链）＋S_cauchy（cauchy 机器实例，Qle_lt_trans 收束）＋        *)
(*   x0（existT 封装＝级数自身 cauchy-real 极限）＋x0_proj＋glue_x0_band  *)
(*   （§10.4 带归属对 x₀ 实例化＝胶合假设非空）＋glue_x0（§10.3 主胶合     *)
(*   定理对真 x₀ 实例化＝边界定理线全通）＋env_lo_2m/env_hi_2m（§10.0     *)
(*   访问器端点 2m 特化桥）＋glue_env_x0＋glue_width_x0（§10.2 宽度见证   *)
(*   对 x₀ 实例化＝(i) 宽度见证使用面）。                                 *)
(*   构造性：语句面全 Set sanctioned（sigT/And/QleT'/QltT/leiblw_Id＋     *)
(*   Qeq_bool/NatLe/cauchy/Real/real_lt）；新段语句面零 ==、零 Qeq 断言、  *)
(*   零 lia 语句原子；证内 Q 层 lra/nia 与 nat 计数 lia＝§0-§10 存量工艺。 *)
(*   零公理（尾 PA 增列 7——承 219 二十一×Closed 只增不破）。            *)
(*   微检核判定（_tlw232_p1）：Z.to_nat (Z.pos p) 参型、Nat2Z.inj_le       *)
(*   iff-apply 可行、Z2Nat.id (Z.pos p)、Qopp 双否定 cbn+lia 面、消没      *)
(*   不等式链 nia 一发收束。                                             *)
(* ============================================================ *)

(* —— §11.0 尾部围包（cauchy 燃料·(i) 交错余项双侧界存量直供）：
   N ≤ k ⟹ S_k 夹于宽度 |t_N| 的窗内——even/odd 双面 —— *)

Lemma leiblw_win_even : forall j k : nat, NatLe (2 * j) k ->
  And (QleT' (leiblw_S (2 * j)) (leiblw_S k))
      (QleT' (leiblw_S k) (leiblw_S (2 * j + 1))).
Proof.
  intros j k Hk. apply NatLe_drop in Hk.
  destruct (leiblw_par_decomp k) as [[i Hi]|[i Hi]]; subst k.
  - split.
    + apply leiblw_mono_even. lia.
    + apply Qle_to_QleT'. apply (Qle_trans _ (leiblw_S (2 * i + 1))).
      * replace (2 * i + 1) with (Datatypes.S (2 * i)) by lia.
        pose proof (qeqT_imp_qeq _ _ (leiblw_S_step (2 * i))) as Hs. rewrite Hs.
        pose proof (leiblw_qle_add_l (leiblw_S (2 * i)) (leiblw_t (2 * i))
                      (Qlt_le_weak _ _ (QltT_to_Qlt _ _ (leiblw_t_even_pos i)))) as H3.
        exact (QleT'_to_Qle _ _ H3).
      * apply QleT'_to_Qle. apply leiblw_mono_odd. lia.
  - split.
    + apply Qle_to_QleT'. apply (Qle_trans _ (leiblw_S (2 * i))).
      * apply QleT'_to_Qle. apply leiblw_mono_even. lia.
      * replace (2 * i + 1) with (Datatypes.S (2 * i)) by lia.
        pose proof (qeqT_imp_qeq _ _ (leiblw_S_step (2 * i))) as Hs. rewrite Hs.
        pose proof (leiblw_qle_add_l (leiblw_S (2 * i)) (leiblw_t (2 * i))
                      (Qlt_le_weak _ _ (QltT_to_Qlt _ _ (leiblw_t_even_pos i)))) as H3.
        exact (QleT'_to_Qle _ _ H3).
    + apply leiblw_mono_odd. lia.
Qed.

Lemma leiblw_win_odd : forall j k : nat, NatLe (2 * j + 1) k ->
  And (QleT' (leiblw_S (2 * j + 2)) (leiblw_S k))
      (QleT' (leiblw_S k) (leiblw_S (2 * j + 1))).
Proof.
  intros j k Hk. apply NatLe_drop in Hk.
  destruct (leiblw_par_decomp k) as [[i Hi]|[i Hi]]; subst k.
  - split.
    + replace (2 * j + 2) with (2 * (j + 1)) by lia.
      apply leiblw_mono_even. lia.
    + apply Qle_to_QleT'. apply (Qle_trans _ (leiblw_S (2 * i + 1))).
      * replace (2 * i + 1) with (Datatypes.S (2 * i)) by lia.
        pose proof (qeqT_imp_qeq _ _ (leiblw_S_step (2 * i))) as Hs. rewrite Hs.
        pose proof (leiblw_qle_add_l (leiblw_S (2 * i)) (leiblw_t (2 * i))
                      (Qlt_le_weak _ _ (QltT_to_Qlt _ _ (leiblw_t_even_pos i)))) as H3.
        exact (QleT'_to_Qle _ _ H3).
      * apply QleT'_to_Qle. apply leiblw_mono_odd. lia.
  - split.
    + apply Qle_to_QleT'. apply (Qle_trans _ (leiblw_S (2 * i + 2))).
      * replace (2 * j + 2) with (2 * (j + 1)) by lia.
        replace (2 * i + 2) with (2 * (i + 1)) by lia.
        apply QleT'_to_Qle. apply leiblw_mono_even. lia.
      * apply QleT'_to_Qle. apply leiblw_interlace.
    + apply leiblw_mono_odd. lia.
Qed.

(* 围包宽度等值（Id＋Qeq_bool 面）：窗宽＝|t_N| 本值——(i) 宽度见证的
   尾部余项形（B−A＝S_{N+1}−S_N＝t_N，奇支取负＝Qabs） *)
Lemma leiblw_win_width_even : forall j : nat,
  leiblw_Id (Qeq_bool ((leiblw_S (2 * j + 1) - leiblw_S (2 * j))%Q)
                      (Qabs (leiblw_t (2 * j)))) true.
Proof.
  intros j. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
  assert (Hst : leiblw_S (2 * j + 1) == (leiblw_S (2 * j) + leiblw_t (2 * j))%Q).
  { replace (2 * j + 1) with (Datatypes.S (2 * j)) by lia.
    pose proof (leiblw_S_step (2 * j)) as Hs. exact (qeqT_imp_qeq _ _ Hs). }
  apply (Qeq_trans _ (leiblw_t (2 * j)) _).
  - lra.
  - symmetry.
    assert (Htp : Qle 0%Q (leiblw_t (2 * j)))
      by (apply Qlt_le_weak; apply QltT_to_Qlt; apply leiblw_t_even_pos).
    pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_id _ Htp)) as Hab.
    exact Hab.
Qed.

Lemma leiblw_win_width_odd : forall j : nat,
  leiblw_Id (Qeq_bool ((leiblw_S (2 * j + 1) - leiblw_S (2 * j + 2))%Q)
                      (Qabs (leiblw_t (2 * j + 1)))) true.
Proof.
  intros j. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
  assert (Hst : leiblw_S (2 * j + 2) == (leiblw_S (2 * j + 1) + leiblw_t (2 * j + 1))%Q).
  { replace (2 * j + 2) with (Datatypes.S (2 * j + 1)) by lia.
    pose proof (leiblw_S_step (2 * j + 1)) as Hs. exact (qeqT_imp_qeq _ _ Hs). }
  apply (Qeq_trans _ ((- leiblw_t (2 * j + 1))%Q) _).
  - lra.
  - symmetry.
    assert (Htn : Qle (leiblw_t (2 * j + 1)) 0%Q)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; apply leiblw_t_odd_neg).
    pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_neg _ Htn)) as Hab.
    exact Hab.
Qed.

(* —— §11.1 cauchy 主燃料：|S_m−S_n| ≤ |t_N|（同窗双侧，零三角不等式） —— *)

Lemma leiblw_S_pair_win_even : forall j m n : nat,
  NatLe (2 * j) m -> NatLe (2 * j) n ->
  QleT' (Qabs ((leiblw_S m - leiblw_S n)%Q)) (Qabs (leiblw_t (2 * j))).
Proof.
  intros j m n Hm Hn.
  destruct (leiblw_win_even j m Hm) as [A1 B1].
  destruct (leiblw_win_even j n Hn) as [A2 B2].
  apply QleT'_to_Qle in A1. apply QleT'_to_Qle in B1.
  apply QleT'_to_Qle in A2. apply QleT'_to_Qle in B2.
  pose proof (leiblw_win_width_even j) as Hw.
  (* Qabs 挡在 lra 外：先以 Qabs-free 窗宽 D 出双侧 Qle，qabs_bound 合成后 comp_r 移写 *)
  assert (Hd1 : Qle ((leiblw_S m - leiblw_S n)%Q)
                    ((leiblw_S (2 * j + 1) - leiblw_S (2 * j))%Q)) by lra.
  assert (Hd2 : Qle ((- (leiblw_S m - leiblw_S n))%Q)
                    ((leiblw_S (2 * j + 1) - leiblw_S (2 * j))%Q)) by lra.
  pose proof (leiblw_qabs_bound _ _ Hd1 Hd2) as Habs.
  apply (leiblw_QleT'_comp_r (Qabs ((leiblw_S m - leiblw_S n)%Q))
                             ((leiblw_S (2 * j + 1) - leiblw_S (2 * j))%Q)).
  - exact Hw.
  - exact Habs.
Qed.

Lemma leiblw_S_pair_win_odd : forall j m n : nat,
  NatLe (2 * j + 1) m -> NatLe (2 * j + 1) n ->
  QleT' (Qabs ((leiblw_S m - leiblw_S n)%Q)) (Qabs (leiblw_t (2 * j + 1))).
Proof.
  intros j m n Hm Hn.
  destruct (leiblw_win_odd j m Hm) as [A1 B1].
  destruct (leiblw_win_odd j n Hn) as [A2 B2].
  apply QleT'_to_Qle in A1. apply QleT'_to_Qle in B1.
  apply QleT'_to_Qle in A2. apply QleT'_to_Qle in B2.
  pose proof (leiblw_win_width_odd j) as Hw.
  assert (Hd1 : Qle ((leiblw_S m - leiblw_S n)%Q)
                    ((leiblw_S (2 * j + 1) - leiblw_S (2 * j + 2))%Q)) by lra.
  assert (Hd2 : Qle ((- (leiblw_S m - leiblw_S n))%Q)
                    ((leiblw_S (2 * j + 1) - leiblw_S (2 * j + 2))%Q)) by lra.
  pose proof (leiblw_qabs_bound _ _ Hd1 Hd2) as Habs.
  apply (leiblw_QleT'_comp_r (Qabs ((leiblw_S m - leiblw_S n)%Q))
                             ((leiblw_S (2 * j + 1) - leiblw_S (2 * j + 2))%Q)).
  - exact Hw.
  - exact Habs.
Qed.

Lemma leiblw_S_pair_abs_t : forall N m n : nat, NatLe N m -> NatLe N n ->
  QleT' (Qabs ((leiblw_S m - leiblw_S n)%Q)) (Qabs (leiblw_t N)).
Proof.
  intros N m n Hm Hn.
  destruct (leiblw_par_decomp N) as [[j HN]|[j HN]]; subst N.
  - apply leiblw_S_pair_win_even; assumption.
  - apply leiblw_S_pair_win_odd; assumption.
Qed.

(* —— §11.2 |t_n|→0 消没见证（②）：§4 交错余项界存量直供。
   |t_n|＝4/(2n+1)＜eps ⟸ 4·Qden eps＜Qnum eps·(2n+1)——nat 见证
   N := 4·(Qden eps)+1：2N+1＝8·den+3＞4·den（Z 面单调链，微检核判定形） —— *)

Lemma leiblw_t_abs : forall n : nat,
  leiblw_Id (Qeq_bool (Qabs (leiblw_t n)) ((4 # Pos.of_succ_nat (2 * n))%Q)) true.
Proof.
  intros n. destruct (leiblw_even n) eqn:Hev.
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    pose proof (qeqT_imp_qeq _ _ (leiblw_t_pos_case n Hev)) as Htp. setoid_rewrite Htp.
    assert (Hp0 : Qle 0%Q (4 # Pos.of_succ_nat (2 * n))%Q).
    { assert (Hb0 : Z.leb (0 * Z.pos (Pos.of_succ_nat (2 * n))) (4 * Z.pos 1) = true) by lia.
      unfold Qle. cbn [Qnum Qden].
      apply (proj1 (Z.compare_le_iff _ _)). apply (proj1 (Z.leb_le _ _)). exact Hb0. }
    pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_id _ Hp0)) as Hab. exact Hab.
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    pose proof (qeqT_imp_qeq _ _ (leiblw_t_neg_case n Hev)) as Htp. setoid_rewrite Htp.
    assert (Hp1 : Qle ((-4) # Pos.of_succ_nat (2 * n))%Q 0%Q).
    { assert (Hb1 : Z.leb ((-4) * Z.pos 1) (0 * Z.pos (Pos.of_succ_nat (2 * n))) = true) by lia.
      unfold Qle. cbn [Qnum Qden].
      apply (proj1 (Z.compare_le_iff _ _)). apply (proj1 (Z.leb_le _ _)). exact Hb1. }
    pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_neg _ Hp1)) as Han. rewrite Han.
    unfold Qeq. cbn [Qnum Qden Qopp]. lia.
Qed.

Lemma leiblw_t_vanish : forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QltT (Qabs (leiblw_t n)) eps).
Proof.
  intros eps Heps.
  pose proof (QltT_to_Qlt 0 eps Heps) as Hlt.
  destruct eps as [z p]. unfold Qlt in Hlt. cbn [Qnum Qden] in Hlt.
  assert (Hz1 : (1 <= z)%Z) by lia.
  assert (Hp1 : (0 <= Z.pos p)%Z) by apply Pos2Z.is_nonneg.
  exists (Datatypes.S (4 * Z.to_nat (Z.pos p))).
  intros n Hn.
  assert (Hle : (Datatypes.S (4 * Z.to_nat (Z.pos p)) <= n)%nat)
    by (apply NatLe_drop; exact Hn).
  assert (Hmono : (Z.of_nat (Datatypes.S (4 * Z.to_nat (Z.pos p))) <= Z.of_nat n)%Z)
    by (apply Nat2Z.inj_le; exact Hle).
  assert (HNval : Z.of_nat (Datatypes.S (4 * Z.to_nat (Z.pos p))) = (4 * Z.pos p + 1)%Z).
  { replace (Datatypes.S (4 * Z.to_nat (Z.pos p))) with (4 * Z.to_nat (Z.pos p) + 1)%nat by lia.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, (Z2Nat.id (Z.pos p) Hp1). lia. }
  assert (Hn2 : Z.of_nat (Datatypes.S (2 * n)) = (2 * Z.of_nat n + 1)%Z).
  { replace (Datatypes.S (2 * n)) with (2 * n + 1)%nat by lia.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul. lia. }
  apply (leiblw_QltT_comp_l ((4 # Pos.of_succ_nat (2 * n))%Q) (Qabs (leiblw_t n)) (z # p)%Q).
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    apply Qeq_sym. apply (proj1 (Qeq_bool_iff _ _)).
    assert (Hta := leiblw_t_abs n). leiblw_id_inv_in Hta. exact Hta.
  - apply Qlt_to_QltT.
    unfold Qlt. cbn [Qnum Qden]. apply (proj2 (Z.compare_lt_iff _ _)).
    leiblw_ps (2 * n). rewrite Hn2. nia.
Qed.

(* —— §11.3 cauchy 机器实例＋x₀ 封装（①）：级数自身 cauchy-real 极限。
   不认领 π/4——x₀ 的唯一载荷＝「这个族有多慢」（|t_n|→0＋围包宽度），     *)
(*   其值恒真无 π 前提。 —— *)

Lemma leiblw_S_cauchy : cauchy (fun n : nat => leiblw_S n).
Proof.
  intros eps Heps.
  destruct (leiblw_t_vanish eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  apply Qlt_to_QltT. apply (Qle_lt_trans _ (Qabs (leiblw_t N))).
  - apply QleT'_to_Qle. apply leiblw_S_pair_abs_t.
    + exact Hm.
    + exact Hn.
  - apply QltT_to_Qlt. apply HN. apply NatLe_lift. apply Nat.le_refl.
Qed.

Definition leiblw_x0 : Real :=
  existT (fun u : Qseq => cauchy u) (fun n : nat => leiblw_S n) leiblw_S_cauchy.

(* x₀ 代表列＝部分和列本值（Id＋Qeq_bool 面，机器可核） *)
Lemma leiblw_x0_proj : forall n : nat,
  leiblw_Id (Qeq_bool (projT1 leiblw_x0 n) (leiblw_S n)) true.
Proof.
  intros n. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)). reflexivity.
Qed.

(* —— §11.4 胶合实例化（③）：胶合假设非空＋主胶合定理对真 x₀ 成立
   ＝边界定理线全通。 —— *)

(* §10.4 带归属对 x₀：j ≥ 2m+3 终入内缘带（glue_band_S 存量直供——
   projT1 x₀ j 转换即 leiblw_S j） *)
Lemma leiblw_glue_x0_band : forall m : nat,
  sigT (fun N : nat => forall j : nat, NatLe N j ->
    And (QleT' ((leiblw_env_lo (2 * m) + leiblw_env_g (2 * m))%Q) (projT1 leiblw_x0 j))
        (QleT' (projT1 leiblw_x0 j)
               ((leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1))%Q))).
Proof.
  intros m. exists (2 * m + 3). intros j Hj.
  exact (leiblw_glue_band_S m j Hj).
Qed.

(* §10.3 主胶合定理对真 x₀：dist(x₀, lo) ≥ 兄弟 gap 与 dist(x₀, hi) ≥
   兄弟 gap 的 eps-def 双侧成立＝「极限到部分和距离 ≥ gap」全通 *)
Theorem leiblw_glue_x0 : forall m : nat,
  And (forall d : Q, QltT 0 d ->
        real_lt (real_const (((leiblw_env_lo (2 * m) + leiblw_env_g (2 * m)) - d)%Q)) leiblw_x0)
      (forall d : Q, QltT 0 d ->
        real_lt leiblw_x0 (real_const (((leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1)) + d)%Q))).
Proof.
  intros m. exact (leiblw_glue_dist m leiblw_x0 (leiblw_glue_x0_band m)).
Qed.

(* §10.0 访问器端点 2m 特化桥：env_lo(2m)＝S_{2m}、env_hi(2m)＝S_{2m+1}
   （env_*_val 存量＋div2_even 存量直供） *)
Lemma leiblw_env_lo_2m : forall m : nat,
  leiblw_Id (Qeq_bool (leiblw_env_lo (2 * m)) (leiblw_S (2 * m))) true.
Proof.
  intros m. pose proof (leiblw_env_lo_val (2 * m)) as H.
  leiblw_d2e_in m H. leiblw_id_inv_in H.
  apply leiblw_id_eq. exact H.
Qed.

Lemma leiblw_env_hi_2m : forall m : nat,
  leiblw_Id (Qeq_bool (leiblw_env_hi (2 * m)) (leiblw_S (2 * m + 1))) true.
Proof.
  intros m. pose proof (leiblw_env_hi_val (2 * m)) as H.
  leiblw_d2e_in m H. leiblw_id_inv_in H.
  apply leiblw_id_eq. exact H.
Qed.

(* §10.2 宽度见证对 x₀ 的围包前提：j ≥ 2m 终入围包 [env_lo(2m), env_hi(2m)]
   （win_even 存量＋2m 特化桥＋QleT' 移写桥 §10.0½） *)
Lemma leiblw_glue_env_x0 : forall m : nat,
  sigT (fun N : nat => forall j : nat, NatLe N j ->
    And (QleT' (leiblw_env_lo (2 * m)) (projT1 leiblw_x0 j))
        (QleT' (projT1 leiblw_x0 j) (leiblw_env_hi (2 * m)))).
Proof.
  intros m. exists (2 * m). intros j Hj.
  destruct (leiblw_win_even m j Hj) as [A B].
  apply QleT'_to_Qle in A. apply QleT'_to_Qle in B.
  pose proof (leiblw_env_lo_2m m) as HL. leiblw_id_inv_in HL.
  pose proof (leiblw_env_hi_2m m) as HH. leiblw_id_inv_in HH.
  split.
  - apply (leiblw_QleT'_comp_l (leiblw_S (2 * m))).
    + apply leiblw_id_eq. apply Qeq_bool_sym. exact HL.
    + apply Qle_to_QleT'. exact A.
  - apply (leiblw_QleT'_comp_r (projT1 leiblw_x0 j) (leiblw_S (2 * m + 1))).
    + apply leiblw_id_eq. apply Qeq_bool_sym. exact HH.
    + apply Qle_to_QleT'. exact B.
Qed.

(* (i) 宽度见证使用面：|x₀ 列−lo| ≤ 围包宽度（glue_width 存量直供） *)
Lemma leiblw_glue_width_x0 : forall m : nat,
  sigT (fun N0 : nat => forall j : nat, NatLe N0 j ->
    QleT' (Qabs ((projT1 leiblw_x0 j - leiblw_env_lo (2 * m))%Q))
          ((leiblw_env_hi (2 * m) - leiblw_env_lo (2 * m))%Q)).
Proof.
  intros m. exact (leiblw_glue_width m leiblw_x0 (leiblw_glue_env_x0 m)).
Qed.

(* —— §11.5 可执行演示（G5）＋提取＋公理审计 —— *)
(* x₀ 代表列 vm_compute 两发（S_6/S_7＝交错部分和收敛实录）＋
   n=20 处 |t_20|×围包宽度×Qeq_bool 自证三发（核检①数值化：宽度＝|t_{2·div2 20}|，
   Qeq_bool 应为 true；原始 Q 运算不约分，宽度以大分母原形打印，数学值＝4/41） *)
Eval vm_compute in (projT1 leiblw_x0 6, projT1 leiblw_x0 7).
Eval vm_compute in (Qabs (leiblw_t 20), (leiblw_env_hi 20 - leiblw_env_lo 20)%Q,
                    Qeq_bool (Qabs (leiblw_t 20)) ((leiblw_env_hi 20 - leiblw_env_lo 20)%Q)).

(* G3 增强：真极限本体可提取（E979 判例：Real＝(Qseq,cauchy) sigT 提取零伪影） *)
Separate Extraction leiblw_x0.

(* 尾 Print Assumptions（§11 面：G4 关，PA 只增不破——承 219 二十一×Closed） *)
Print Assumptions leiblw_t_vanish.
Print Assumptions leiblw_S_cauchy.
Print Assumptions leiblw_x0.
Print Assumptions leiblw_glue_x0_band.
Print Assumptions leiblw_glue_x0.
Print Assumptions leiblw_glue_env_x0.
Print Assumptions leiblw_glue_width_x0.

(* ============================================================ *)
(* §12 real_lim 对接段（232 候令④·纯胶合加装）：部分和列        *)
(*     （Q 层 leiblw_S 经 real 嵌入 real_const）real_lim→x₀。      *)
(* ============================================================ *)
(* 口径：语句面 sanctioned＝QltT／sigT／And／NatLe／Real／real_lim      *)
(* （real_const／real_plus／real_opp 为 S02 real_lim 定义面连带件）；   *)
(* 零 ==／零 Qeq 断言／零 lia 语句原子；lra 喂料全常数乘形（p2 检核     *)
(* T1/T3 判定 micromega-Q 不拆 Qdiv 除法原子—— witness 取 (1#2)·eps，   *)
(* real_lt 见证位任意 Q 合法，零除法进件）。                           *)
(* 尾窗法：cauchy((1#2)·eps) 见证 N＋win 存量（k≥N ⟹ S_k 夹于           *)
(* [min(S_N,S_{N+1}),max(S_N,S_{N+1})]）⟹ 双侧 margin＞eps−(1#2)·eps    *)
(* ＝witness（严格链由 cauchy 严格界直供，零三角不等式零 t_vanish）。   *)

Lemma leiblw_S_tail_two_sided :
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall n k : nat, NatLe N n -> NatLe N k ->
    And (QltT ((1 # 2) * eps)%Q ((leiblw_S k + eps - leiblw_S n)%Q))
        (QltT ((1 # 2) * eps)%Q ((leiblw_S n - (leiblw_S k + (- eps)))%Q))).
Proof.
  intros eps Heps.
  assert (Hw0 : QltT 0 ((1 # 2) * eps)%Q).
  { apply Qlt_to_QltT.
    assert (H0 : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
    lra. }
  destruct (leiblw_S_cauchy ((1 # 2) * eps)%Q Hw0) as [Nc Hc].
  assert (Habs2 : forall x e : Q, QltT (Qabs x) e -> And (QltT (- e) x) (QltT x e)).
  { intros x e H.
    assert (Hl : Qlt (Qabs x) e) by (apply QltT_to_Qlt; exact H).
    destruct (Qlt_le_dec x 0) as [Hx0 | Hx0].
    - assert (Habs : Qabs x == - x) by (apply Qabs_neg; apply Qlt_le_weak; exact Hx0).
      rewrite Habs in Hl. split; apply Qlt_to_QltT; lra.
    - assert (Habs : Qabs x == x) by (apply Qabs_pos; exact Hx0).
      rewrite Habs in Hl. split; apply Qlt_to_QltT; lra. }
  exists Nc. intros n k Hn Hk.
  destruct (leiblw_par_decomp Nc) as [[j Hj]|[j Hj]]; subst Nc.
  - (* Nc ＝ 2j（偶窗：S_{2j} ≤ S_k ≤ S_{2j+1}） *)
    assert (Hrefl : NatLe (2 * j) (2 * j)) by (apply NatLe_lift; lia).
    assert (Hle1 : NatLe (2 * j) (2 * j + 1)) by (apply NatLe_lift; lia).
    assert (Hcn : QltT (Qabs ((leiblw_S (2 * j) - leiblw_S n)%Q))
                       ((1 # 2) * eps)%Q)
      by exact (Hc (2 * j) n Hrefl Hn).
    assert (Hcn1 : QltT (Qabs ((leiblw_S (2 * j + 1) - leiblw_S n)%Q))
                        ((1 # 2) * eps)%Q)
      by exact (Hc (2 * j + 1) n Hle1 Hn).
    destruct (leiblw_win_even j k Hk) as [A B].
    apply QleT'_to_Qle in A. apply QleT'_to_Qle in B.
    pose proof (Habs2 (leiblw_S (2 * j) - leiblw_S n)%Q ((1 # 2) * eps)%Q Hcn)
      as [Hlo1 Hhi1].
    apply QltT_to_Qlt in Hlo1.
    apply QltT_to_Qlt in Hhi1.
    pose proof (Habs2 (leiblw_S (2 * j + 1) - leiblw_S n)%Q ((1 # 2) * eps)%Q Hcn1)
      as [Hlo2 Hhi2].
    apply QltT_to_Qlt in Hlo2.
    apply QltT_to_Qlt in Hhi2.
    split.
    + apply Qlt_to_QltT. lra.
    + apply Qlt_to_QltT. lra.
  - (* Nc ＝ 2j+1（奇窗：S_{2j+2} ≤ S_k ≤ S_{2j+1}） *)
    assert (Hrefl : NatLe (2 * j + 1) (2 * j + 1)) by (apply NatLe_lift; lia).
    assert (Hle1 : NatLe (2 * j + 1) (2 * j + 2)) by (apply NatLe_lift; lia).
    assert (Hcn : QltT (Qabs ((leiblw_S (2 * j + 1) - leiblw_S n)%Q))
                        ((1 # 2) * eps)%Q)
      by exact (Hc (2 * j + 1) n Hrefl Hn).
    assert (Hcn0 : QltT (Qabs ((leiblw_S (2 * j + 2) - leiblw_S n)%Q))
                        ((1 # 2) * eps)%Q)
      by exact (Hc (2 * j + 2) n Hle1 Hn).
    destruct (leiblw_win_odd j k Hk) as [A B].
    apply QleT'_to_Qle in A. apply QleT'_to_Qle in B.
    pose proof (Habs2 (leiblw_S (2 * j + 1) - leiblw_S n)%Q ((1 # 2) * eps)%Q Hcn)
      as [Hlo1 Hhi1].
    apply QltT_to_Qlt in Hlo1.
    apply QltT_to_Qlt in Hhi1.
    pose proof (Habs2 (leiblw_S (2 * j + 2) - leiblw_S n)%Q ((1 # 2) * eps)%Q Hcn0)
      as [Hlo2 Hhi2].
    apply QltT_to_Qlt in Hlo2.
    apply QltT_to_Qlt in Hhi2.
    split.
    + apply Qlt_to_QltT. lra.
    + apply Qlt_to_QltT. lra.
Qed.

Theorem leiblw_S_real_lim :
  real_lim (fun n : nat => real_const (leiblw_S n)) leiblw_x0.
Proof.
  intros eps Heps.
  destruct (leiblw_S_tail_two_sided eps Heps) as [N HN].
  exists N. intros n Hn.
  assert (Hn' : NatLe N n) by (apply NatLe_lift; exact Hn).
  assert (Hw0 : QltT 0 ((1 # 2) * eps)%Q).
  { apply Qlt_to_QltT.
    assert (H0 : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
    lra. }
  split.
  - (* 上侧：real_lt (u n) (x₀＋eps)——见证 (1#2)·eps；exact 消投影 conversion *)
    exists ((1 # 2) * eps)%Q. split.
    + exact Hw0.
    + exists N. intros k Hk.
      destruct (HN n k Hn' Hk) as [HA HB].
      exact HA.
  - (* 下侧：real_lt (x₀−eps) (u n)——第二分量取 real_lt 归约原形，exact 直消 *)
    exists ((1 # 2) * eps)%Q. split.
    + exact Hw0.
    + exists N. intros k Hk.
      destruct (HN n k Hn' Hk) as [HA HB].
      exact HB.
Qed.

(* 尾 Print Assumptions（§12 面：G4 关，PA 只增不破——承 232 二十八×Closed） *)
Print Assumptions leiblw_S_tail_two_sided.
Print Assumptions leiblw_S_real_lim.
