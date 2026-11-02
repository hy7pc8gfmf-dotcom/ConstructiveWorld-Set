(* ============================================================
   模块：LW0FactGrowth.v
   使命：本件形式化有理数层阶乘的增长下界：对每个自然数 n，
         n! 不小于半数底幂 (n/2)^(n/2)（取半为 Nat.div2）；并给
         出显式有理常数 10/3 的幂被阶乘压制的两条推论——对一切
         n = 22+2k 与 n = 23+2k（k 为自然数，两族合取覆盖一切
         n ≥ 22），(10/3)^n ≤ n!。结合库内圆周率的有理上界
         10/3（S10_KVQuantTrig 的 Leibniz 级数双岸估计，其中
         real_pi_leibniz_lt_ten_thirds 给出 π < 10/3），本件构成
         「π 的幂增长被 n! 压制」这一事实的有理常数侧引擎；实数
         层幂运算的转移不在本件范围。
   依赖：S02_CauchyComplete（QleT' 判定及其双向桥）、S03_QExp
         （q_fact、q_pow）；Stdlib QArith、Arith、ZArith、Lia。
   对标：n! ≥ (n/2)^(n/2) 为初等组合学的标准估计（因子表中自
         n/2 起的因子逐个不小于 n/2）；Coq 标准库无有理数层对
         应物；库内先例为 BetaLower（QleT' 语句形与件内提取检
         验同构）。
   构造性：全部语句 Set 层承载：结论与前提位一律用全局 QleT'，
         零 Prop 前提位、零存在变元；零公理、零承认、零经典逻
         辑；因子表分解为真构造的 Fixpoint 归纳结构；主语句支
         持 Separate Extraction 且 Obj.magic 计数为零。
   编译配方：coqc -native-compiler no -q -Q ConstructiveWorld_vo "" LW0FactGrowth.v（COQLIB/ROCQLIB 环境前缀直调）
   ============================================================ *)

From Stdlib Require Import QArith.QArith Arith.Arith ZArith.ZArith Lia.
Require Import S02_CauchyComplete.
Require Import S03_QExp.

(* ================= §1 有理数层的保序支撑件 ================= *)

(* 自然数的有理像（与 q_fact 步进系数同形，便于定义性归约）。 *)
Definition lw0_q_of_nat (n : nat) : Q := (Z.of_nat n # 1)%Q.

(* 自然数的有理像非负。 *)
Lemma lw0_q_of_nat_nonneg : forall n : nat, QleT' 0 (lw0_q_of_nat n).
Proof.
  intro n. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
Qed.

(* 自然数的后继有理像不小于 1。 *)
Lemma lw0_q_of_nat_ge_one : forall n : nat, QleT' 1 (lw0_q_of_nat (Datatypes.S n)).
Proof.
  intro n. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
Qed.

(* 有理像关于后继的单调性。 *)
Lemma lw0_q_of_nat_le_succ : forall n : nat,
  QleT' (lw0_q_of_nat n) (lw0_q_of_nat (Datatypes.S n)).
Proof.
  intro n. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
Qed.

(* 有理像关于加法的单调性：a 的有理像不超过 a+b 的有理像。 *)
Lemma lw0_q_of_nat_le_add : forall a b : nat,
  QleT' (lw0_q_of_nat a) (lw0_q_of_nat (a + b)%nat).
Proof.
  intros a b. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
Qed.

(* 幂关于底的单调性：0 ≤ x ≤ y 蕴含 x^n ≤ y^n。 *)
Lemma lw0_q_pow_mono_base : forall (x y : Q) (n : nat),
  QleT' 0 x -> QleT' x y -> QleT' (q_pow x n) (q_pow y n).
Proof.
  intros x y n H0 Hxy. apply Qle_to_QleT'.
  induction n as [| n IH].
  - apply Qle_refl.
  - cbn [q_pow].
    apply (Qle_trans _ (x * q_pow y n)%Q).
    + rewrite (Qmult_comm x (q_pow x n)), (Qmult_comm x (q_pow y n)).
      apply Qmult_le_compat_r.
      * exact IH.
      * exact (QleT'_to_Qle _ _ H0).
    + apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ Hxy).
      * apply QleT'_to_Qle. apply q_pow_nonneg. apply (qleT'_trans 0 x y H0 Hxy).
Qed.

(* 幂的后继放大：x ≥ 1 蕴含 x^n ≤ x^(n+1)。 *)
Lemma lw0_q_pow_le_succ_pow : forall (x : Q) (n : nat),
  QleT' 1 x -> QleT' (q_pow x n) (q_pow x (Datatypes.S n)).
Proof.
  intros x n Hx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ x n)).
  apply (Qle_trans _ (1 * q_pow x n)%Q).
  - rewrite (Qmult_comm 1 (q_pow x n)), Qmult_1_r. apply Qle_refl.
  - apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ Hx).
    + apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. apply (Qle_trans 0%Q 1%Q x).
      * unfold Qle. cbn [Qnum Qden]. lia.
      * exact (QleT'_to_Qle _ _ Hx).
Qed.

(* ================= §2 阶乘的因子表分解与半数底幂下界 ================= *)

(* 阶乘的步进等式：q_fact (n+1) == (n+1)·q_fact n（系数与 lw0_q_of_nat 定义性一致）。 *)
Lemma lw0_q_fact_step : forall k : nat,
  QeqT (q_fact (Datatypes.S k)) (lw0_q_of_nat (Datatypes.S k) * q_fact k).
Proof. intro k. apply qeq_imp_qeqT. reflexivity. Qed.

(* 阶乘不小于 1。 *)
Lemma lw0_q_fact_ge_one : forall k : nat, QleT' 1 (q_fact k).
Proof.
  intro k. apply Qle_to_QleT'.
  induction k as [| k IH].
  - apply Qle_refl.
  - rewrite (qeqT_imp_qeq _ _ (lw0_q_fact_step k)).
    apply Qmult_le_1_compat.
    + exact (QleT'_to_Qle _ _ (lw0_q_of_nat_ge_one k)).
    + exact IH.
Qed.

(* 阶乘的双步等式：q_fact (n+2) == (n+2)·(n+1)·q_fact n。 *)
Lemma lw0_q_fact_step2 : forall k : nat,
  QeqT (q_fact (Datatypes.S (Datatypes.S k)))
  (lw0_q_of_nat (Datatypes.S (Datatypes.S k)) * lw0_q_of_nat (Datatypes.S k) * q_fact k).
Proof.
  intro k. apply qeq_imp_qeqT.
  transitivity (lw0_q_of_nat (Datatypes.S (Datatypes.S k)) *
                (lw0_q_of_nat (Datatypes.S k) * q_fact k))%Q.
  - reflexivity.
  - ring.
Qed.

(* 因子表尾段：(a+1)·(a+2)···(a+k)，真构造的归纳结构。 *)
Fixpoint lw0_fact_range (a k : nat) : Q :=
  match k with
  | 0%nat => 1%Q
  | Datatypes.S j => lw0_q_of_nat (a + Datatypes.S j) * lw0_fact_range a j
  end.

(* 因子表分解：q_fact (a+k) == q_fact a·(a+1)···(a+k)。 *)
Lemma lw0_q_fact_split : forall a k : nat,
  QeqT (q_fact (a + k)%nat) (q_fact a * lw0_fact_range a k).
Proof.
  intros a k. apply qeq_imp_qeqT. induction k as [| k IH].
  - rewrite Nat.add_0_r, Qmult_1_r. reflexivity.
  - cbn [lw0_fact_range].
    replace (a + Datatypes.S k)%nat with (Datatypes.S (a + k))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (lw0_q_fact_step (a + k)%nat)), IH. ring.
Qed.

(* 尾段因子的幂下界：(a+1)^k ≤ (a+1)·(a+2)···(a+k)，逐因子比较。 *)
Lemma lw0_fact_range_ge_pow : forall a k : nat,
  QleT' (q_pow (lw0_q_of_nat (Datatypes.S a)) k) (lw0_fact_range a k).
Proof.
  intros a k. induction k as [| k IH].
  - apply qleT'_refl.
  - apply Qle_to_QleT'.
    cbn [lw0_fact_range q_pow].
    apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S a) * lw0_fact_range a k)%Q).
    + rewrite (Qmult_comm (lw0_q_of_nat (Datatypes.S a))
                          (q_pow (lw0_q_of_nat (Datatypes.S a)) k)),
              (Qmult_comm (lw0_q_of_nat (Datatypes.S a)) (lw0_fact_range a k)).
      apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ IH).
      * apply QleT'_to_Qle. apply lw0_q_of_nat_nonneg.
    + apply Qmult_le_compat_r.
      * unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
      * apply (Qle_trans 0%Q (q_pow (lw0_q_of_nat (Datatypes.S a)) k)
                           (lw0_fact_range a k)).
        -- apply QleT'_to_Qle. apply q_pow_nonneg. apply lw0_q_of_nat_nonneg.
        -- exact (QleT'_to_Qle _ _ IH).
Qed.

(** 半数底幂的双倍下界：对每个自然数 m，m^m ≤ (2m)!。数学含义：因子表
    1·2···(2m) 的尾段 (m+1)···(2m) 共 m 个因子，逐个不小于 m+1 ≥ m。
    证明策略：因子表分解至尾段，尾段逐因子与 (m+1)^m 比较，再乘回前段。 *)
Lemma lw0_pow_half_le_fact_double : forall m : nat,
  QleT' (q_pow (lw0_q_of_nat m) m) (q_fact (2 * m)%nat).
Proof.
  intro m.
  apply (qleT'_trans (q_pow (lw0_q_of_nat m) m) (q_pow (lw0_q_of_nat (Datatypes.S m)) m)).
  - exact (lw0_q_pow_mono_base (lw0_q_of_nat m) (lw0_q_of_nat (Datatypes.S m)) m
      (lw0_q_of_nat_nonneg m) (lw0_q_of_nat_le_succ m)).
  - apply (qleT'_trans (q_pow (lw0_q_of_nat (Datatypes.S m)) m) (lw0_fact_range m m)).
    + exact (lw0_fact_range_ge_pow m m).
    + replace (2 * m)%nat with (m + m)%nat by lia.
      apply Qle_to_QleT'.
      rewrite (qeqT_imp_qeq _ _ (lw0_q_fact_split m m)).
      apply (Qle_trans _ (1 * lw0_fact_range m m)%Q).
      * rewrite (Qmult_comm 1 (lw0_fact_range m m)), Qmult_1_r. apply Qle_refl.
      * apply Qmult_le_compat_r.
        -- exact (QleT'_to_Qle _ _ (lw0_q_fact_ge_one m)).
        -- apply (Qle_trans 0%Q (q_pow (lw0_q_of_nat (Datatypes.S m)) m)
                             (lw0_fact_range m m)).
           ++ apply QleT'_to_Qle. apply q_pow_nonneg. apply lw0_q_of_nat_nonneg.
           ++ exact (QleT'_to_Qle _ _ (lw0_fact_range_ge_pow m m)).
Qed.

(** 阶乘的半数底幂下界：对每个自然数 n，(n/2)^(n/2) ≤ n!，其中取半为
    Nat.div2。数学含义：n 的因子表中自 n/2 起的因子逐个不小于 n/2。
    证明策略：以 Nat.div2_odd 的奇偶方程按 Nat.odd 的布尔值分情形，
    偶情形归约到双倍下界，奇情形再乘入最后一个因子。 *)
Theorem lw0_fact_lower_growth : forall n : nat,
  QleT' (q_pow (lw0_q_of_nat (Nat.div2 n)) (Nat.div2 n)) (q_fact n).
Proof.
  intro n.
  pose proof (Nat.div2_odd n) as Hd.
  destruct (Nat.odd n) eqn:Hodd.
  - (* 情形 n 为奇数：n = 2·(n/2)+1。 *)
    cbn [Nat.b2n] in Hd |- *.
    set (m := Nat.div2 n) in *.
    rewrite Hd.
    apply (qleT'_trans (q_pow (lw0_q_of_nat m) m) (q_fact (2 * m))).
    + exact (lw0_pow_half_le_fact_double m).
    + replace (2 * m + 1)%nat with (Datatypes.S (2 * m))%nat by lia.
      apply Qle_to_QleT'.
      rewrite (qeqT_imp_qeq _ _ (lw0_q_fact_step (2 * m)%nat)).
      apply (Qle_trans _ (1 * q_fact (2 * m))%Q).
      * rewrite (Qmult_comm 1 (q_fact (2 * m))), Qmult_1_r. apply Qle_refl.
      * apply Qmult_le_compat_r.
        -- exact (QleT'_to_Qle _ _ (lw0_q_of_nat_ge_one (2 * m))).
        -- apply (Qlt_le_weak 0). apply QltT_to_Qlt. apply q_fact_pos.
  - (* 情形 n 为偶数：n = 2·(n/2)。 *)
    cbn [Nat.b2n] in Hd |- *. rewrite Nat.add_0_r in Hd.
    set (m := Nat.div2 n) in *.
    rewrite Hd.
    exact (lw0_pow_half_le_fact_double m).
Qed.

(* ================= §3 圆周率有理上界的幂被阶乘压制 ================= *)

(* 双步推进引理：若 1 ≤ c ≤ n+1 的有理像且 c^n ≤ n!，则 c^(n+2) ≤ (n+2)!。
   由 c^(n+2) = c·(c·c^n) 与 (n+2)! = (n+2)·(n+1)·n! 逐因子放缩。 *)
Lemma lw0_q_pow_fact_step2 : forall (c : Q) (n : nat),
  QleT' 1 c ->
  QleT' c (lw0_q_of_nat (Datatypes.S n)) ->
  QleT' (q_pow c n) (q_fact n) ->
  QleT' (q_pow c (Datatypes.S (Datatypes.S n)))
        (q_fact (Datatypes.S (Datatypes.S n))).
Proof.
  intros c n H1c Hcn IH. apply Qle_to_QleT'.
  pose proof (fun (x : Q) (m : nat) => qeqT_imp_qeq _ _ (q_pow_succ x m)) as Hqs.
  rewrite (qeqT_imp_qeq _ _ (lw0_q_fact_step2 n)), !Hqs.
  rewrite <- (Qmult_assoc (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                          (lw0_q_of_nat (Datatypes.S n)) (q_fact n))%Q.
  assert (H0c : Qle 0 c).
  { apply (Qle_trans 0%Q 1%Q c).
    - unfold Qle. cbn [Qnum Qden]. lia.
    - exact (QleT'_to_Qle _ _ H1c). }
  assert (H0P : Qle 0 (q_pow c n))
    by (apply QleT'_to_Qle; apply q_pow_nonneg; apply Qle_to_QleT'; exact H0c).
  assert (HcP : Qle (c * q_pow c n)
                    (lw0_q_of_nat (Datatypes.S n) * q_fact n)).
  { apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S n) * q_pow c n)).
    - apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ Hcn).
      + exact H0P.
    - rewrite (Qmult_comm (lw0_q_of_nat (Datatypes.S n)) (q_pow c n)),
              (Qmult_comm (lw0_q_of_nat (Datatypes.S n)) (q_fact n)).
      apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ IH).
      + exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg (Datatypes.S n))). }
  assert (H0cP : Qle 0 (c * q_pow c n))
    by (apply Qmult_le_0_compat; assumption).
  assert (H0BF : Qle 0 (lw0_q_of_nat (Datatypes.S n) * q_fact n)).
  { apply Qmult_le_0_compat.
    - exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg (Datatypes.S n))).
    - apply (Qlt_le_weak 0). apply QltT_to_Qlt. apply q_fact_pos. }
  assert (HBA : Qle (lw0_q_of_nat (Datatypes.S n))
                    (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))).
  { replace (Datatypes.S (Datatypes.S n))%nat with (Datatypes.S n + 1)%nat by lia.
    exact (QleT'_to_Qle _ _ (lw0_q_of_nat_le_add (Datatypes.S n) 1)). }
  apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S n) * (c * q_pow c n))%Q).
  - apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ Hcn).
    + exact H0cP.
  - apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S n) *
                        (lw0_q_of_nat (Datatypes.S n) * q_fact n))%Q).
    + rewrite (Qmult_comm (lw0_q_of_nat (Datatypes.S n)) (c * q_pow c n)),
              (Qmult_comm (lw0_q_of_nat (Datatypes.S n))
                          (lw0_q_of_nat (Datatypes.S n) * q_fact n)).
      apply Qmult_le_compat_r.
      * exact HcP.
      * exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg (Datatypes.S n))).
    + apply Qmult_le_compat_r.
      * exact HBA.
      * exact H0BF.
Qed.

(** 圆周率有理上界的幂的阶乘压制（偶数族）：对每个自然数 k，
    (10/3)^(22+2k) ≤ (22+2k)!。数学含义：结合库内估计 π < 10/3
    （S10_KVQuantTrig 的 real_pi_leibniz_lt_ten_thirds），对一切偶数
    n ≥ 22，π 的上界 10/3 的 n 次幂不超过 n!。证明策略：基例以数值
    判定闭合，归纳步由双步推进引理完成。 *)
Theorem lw0_pi_bound_dominated_even : forall k : nat,
  QleT' (q_pow (10 # 3) (22 + 2 * k)%nat) (q_fact (22 + 2 * k)%nat).
Proof.
  intro k.
  induction k as [| k IH].
  - (* 基例 k = 0，即 n = 22：数值判定。 *)
    vm_compute. reflexivity.
  - (* 归纳步：由 k 到 S k，即由 n 到 n+2。 *)
    replace (22 + 2 * Datatypes.S k)%nat
      with (Datatypes.S (Datatypes.S (22 + 2 * k)))%nat by lia.
    apply (lw0_q_pow_fact_step2 (10 # 3)%Q (22 + 2 * k)%nat).
    + vm_compute. reflexivity.
    + replace (Datatypes.S (22 + 2 * k)) with (23 + 2 * k)%nat by lia.
      apply (qleT'_trans (10 # 3)%Q (lw0_q_of_nat 23)).
      * vm_compute. reflexivity.
      * apply lw0_q_of_nat_le_add.
    + exact IH.
Qed.

(** 圆周率有理上界的幂的阶乘压制（奇数族）：对每个自然数 k，
    (10/3)^(23+2k) ≤ (23+2k)!。与偶数族合取，覆盖一切 n ≥ 22。
    证明策略与偶数族相同：基例数值判定，归纳步双步推进。 *)
Theorem lw0_pi_bound_dominated_odd : forall k : nat,
  QleT' (q_pow (10 # 3) (23 + 2 * k)%nat) (q_fact (23 + 2 * k)%nat).
Proof.
  intro k.
  induction k as [| k IH].
  - (* 基例 k = 0，即 n = 23：数值判定。 *)
    vm_compute. reflexivity.
  - (* 归纳步：由 k 到 S k，即由 n 到 n+2。 *)
    replace (23 + 2 * Datatypes.S k)%nat
      with (Datatypes.S (Datatypes.S (23 + 2 * k)))%nat by lia.
    apply (lw0_q_pow_fact_step2 (10 # 3)%Q (23 + 2 * k)%nat).
    + vm_compute. reflexivity.
    + replace (Datatypes.S (23 + 2 * k)) with (24 + 2 * k)%nat by lia.
      apply (qleT'_trans (10 # 3)%Q (lw0_q_of_nat 24)).
      * vm_compute. reflexivity.
      * apply lw0_q_of_nat_le_add.
    + exact IH.
Qed.

(* 提取检验与公理面自审：提取产物零 Obj.magic，各语句 Closed。 *)

From Stdlib Require Import Extraction.
Separate Extraction lw0_fact_lower_growth lw0_pi_bound_dominated_even lw0_pi_bound_dominated_odd.

Print Assumptions lw0_fact_lower_growth.
Print Assumptions lw0_pi_bound_dominated_even.
Print Assumptions lw0_pi_bound_dominated_odd.
