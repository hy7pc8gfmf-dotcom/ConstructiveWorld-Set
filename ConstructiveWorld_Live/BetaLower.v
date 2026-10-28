(* ============================================================ *)
(*  BetaLower.v —— Beta 闭式承载的 c·σⁿ 型下界族                     *)
(*  使命: 以 lne_B n = (n!)²/(2n+1)!（Beta 闭式，lne_B_closed）为承载  *)
(*        的 c·σⁿ 型下界族：                                           *)
(*        主件 bl_beta_lower：(1/2)·(3/16)ⁿ ≤ lne_B n（QleT'）；        *)
(*        族最优 bl_beta_lower_opt：(98/135)·(3/14)ⁿ ≤ lne_B n          *)
(*        （n=2、n=3 双缚等号；任何 c·σⁿ 下界族中 σ ≤ min_{n≥2} 步比    *)
(*        = 3/14，此对在「n≥2 缚」意义下不可改进）；                    *)
(*        变体 bl_variant_shift：(1/4)·(3/32)ⁿ ≤ 2^{−(n+1)}·lne_B n     *)
(*        = 2^{−(n+2)}·(3/16)ⁿ。                                        *)
(*        背景：I_n = ∫₀¹ tⁿ(1−t)ⁿ/(1−t/2)^{n+1} dt 满足                *)
(*        ln2 − x'_n = I_n/(2^{n+1}·q̃_n)，且 I_n ≥ lne_B n；            *)
(*        I_n 本体（有理被积函数）的积分对象不在库内，本件交付以        *)
(*        lne_B 为承载的 I_n 可证下界形。数值锚：lne_B 0..3 =           *)
(*        1, 1/6, 1/30, 1/140（vm_compute 实例 ×9＋值见证 ×3）。        *)
(*  依赖: S02_CauchyComplete（QleT'/QltT 桥）、S03_QExp（q_pow/q_fact）、*)
(*        SumInvFactEscape（sif_qfact_Z）、PolyIntegral、               *)
(*        Ln2Escape（lne_B 承载）；Stdlib QArith、Arith、ZArith、        *)
(*        Arith.Factorial、Lia。                                        *)
(*  对标: PadeErrorIntegral pei_beta 族／Ln2Escape lne_beta_value        *)
(*        （Beta 闭式配方溯沿）；lne_div_eq（除法比较器同构）。          *)
(*  构造性: 语句面全 Set（QleT'/QeqT；Q 层 Prop 仅内部脚手架）；         *)
(*        零承认语句、零经典逻辑；纯 nat 阶乘不等式归纳                  *)
(*        （bl_nat_core16/14：3(2n+3) ≤ 8(n+1) / ≤ 7(n+1) 线性 lia）；   *)
(*        除法比较器 bl_div_le（配 bl_div_ge 对偶）；                    *)
(*        提取检验 Obj.magic=0。                                        *)
(*  编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树  *)
(*        同世界重编），COQLIB/ROCQLIB 全字面环境前缀。                  *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith Arith.Arith ZArith.ZArith Lia.
From Stdlib Require Import Arith.Factorial.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S01_BaseRing (Id, id_refl, NatLe, NatLe_lift, NatLe_drop, Not).
Require Import SumInvFactEscape.
Require Import PolyIntegral.
Require Import Ln2Escape.

(* ============================================================ *)
(* §1 Q 层支撑件（内件，Prop 面仅脚手架）                              *)
(* ============================================================ *)

(* k^n ≥ 1（正底幂非零下界；供 Qlt cast 支路用） *)
Lemma bl_mul_ge1 : forall k n : nat, (1 <= k)%nat -> NatLe 1 (k ^ n).
Proof.
  intros k n Hk. apply NatLe_lift. induction n as [| n IH].
  - cbn. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* Qmake 乘法桥：(a#1)·(b#1) == (a·b#1)（定义级） *)
Lemma bl_qmake_mul : forall a b : Z, QeqT ((a # 1) * (b # 1)) ((a * b # 1)%Q).
Proof.
  intros a b. apply qeq_imp_qeqT. unfold Qmult. cbn [Pos.mul]. reflexivity.
Qed.

(* 乘除结合桥接引理：x·(y/z) == (x·y)/z（Qdiv 的定义即乘 Qinv，展开后为结合律） *)
Lemma bl_mult_div_assoc : forall x y z : Q, QeqT (x * (y / z)) ((x * y) / z).
Proof. intros x y z. apply qeq_imp_qeqT. unfold Qdiv. ring. Qed.

(* 同幂相乘桥接引理：q_pow x n · q_pow y n == q_pow (x·y) n（bl_variant_shift 使用） *)
Lemma bl_qpow_mul : forall (x y : Q) (n : nat), QeqT (q_pow x n * q_pow y n) (q_pow (x * y) n).
Proof.
  intros x y n. apply qeq_imp_qeqT. induction n as [| n IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (q_pow_succ x n)), (qeqT_imp_qeq _ _ (q_pow_succ y n)),
           (qeqT_imp_qeq _ _ (q_pow_succ (x * y) n)).
    transitivity ((x * y) * (q_pow x n * q_pow y n)).
    + ring.
    + rewrite IH. ring.
Qed.

(* Qinv 对乘积分配（双非零前提；bl_pow_div/桥接引理用） *)
Lemma bl_qinv_mult : forall x y : Q,
  ~ (x == 0%Q) -> ~ (y == 0%Q) -> QeqT (Qinv (x * y)) (Qinv x * Qinv y).
Proof.
  intros x y Hx Hy. apply qeq_imp_qeqT.
  apply (lne_mult_canc (Qinv (x * y)) (Qinv x * Qinv y) (x * y)).
  - transitivity (1%Q).
    + rewrite (Qmult_comm (Qinv (x * y)) (x * y)).
      apply Qmult_inv_r.
      intro E. apply Hx. apply (lne_mult_canc x 0%Q y).
      * rewrite Qmult_0_l. exact E.
      * exact Hy.
    + assert (E1 : (Qinv x * Qinv y) * (x * y) == (x * Qinv x) * (y * Qinv y)) by ring.
      rewrite E1.
      rewrite (Qmult_inv_r x Hx). rewrite (Qmult_inv_r y Hy). ring.
  - apply (lne_mult_nz x y Hx Hy).
Qed.

(* 正底幂非零：~ (q_pow y n == 0) *)
Lemma bl_qpow_nz : forall (y : Q) (n : nat),
  ~ (y == 0%Q) -> Not (QeqT (q_pow y n) 0%Q).
Proof.
  intros y n Hy.
  assert (Hprop : forall m : nat, ~ (q_pow y m == 0%Q)).
  { intro m. induction m as [| m IH].
    - intro E. vm_compute in E. lia.
    - apply (lne_mult_nz y (q_pow y m)).
      + exact Hy.
      + apply IH. }
  intro E. exact (False_rect _ (Hprop n (qeqT_imp_qeq _ _ E))).
Qed.

(* 幂的除法分配：q_pow (x/y) n == q_pow x n / q_pow y n *)
Lemma bl_pow_div : forall (x y : Q) (n : nat),
  ~ (y == 0%Q) -> QeqT (q_pow (x / y) n) (q_pow x n / q_pow y n).
Proof.
  intros x y n Hy. apply qeq_imp_qeqT. induction n as [| n IH].
  - reflexivity.
  - assert (Hzn : ~ (q_pow y n == 0%Q)).
    { intro E. exact (match bl_qpow_nz y n Hy (qeq_imp_qeqT _ _ E) with end). }
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (x / y) n)), (qeqT_imp_qeq _ _ (q_pow_succ x n)),
            (qeqT_imp_qeq _ _ (q_pow_succ y n)).
    rewrite IH.
    unfold Qdiv.
    rewrite (qeqT_imp_qeq _ _ (bl_qinv_mult y (q_pow y n) Hy Hzn)).
    ring.
Qed.

(* 整数 cast 幂桥：q_pow (k#1) n == (k^n # 1) *)
Lemma bl_pZ : forall k n : nat, QeqT (q_pow (Z.of_nat k # 1) n) ((Z.of_nat (k ^ n) # 1)%Q).
Proof.
  intros k n. apply qeq_imp_qeqT. induction n as [| n IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (q_pow_succ (Z.of_nat k # 1) n)). rewrite IH. rewrite Nat.pow_succ_r'.
    unfold Qmult. cbn [Pos.mul]. rewrite Nat2Z.inj_mul. reflexivity.
Qed.

(* 左乘保序：x ≤ y、0 ≤ z ⟹ z·x ≤ z·y（Qmult_le_compat_r 的左乘封装） *)
Lemma bl_mlc : forall x y z : Q, Qle x y -> Qle 0 z -> QleT' (z * x) (z * y).
Proof.
  intros x y z H Hz. apply Qle_to_QleT'.
  rewrite (Qmult_comm z x), (Qmult_comm z y).
  exact (Qmult_le_compat_r x y z H Hz).
Qed.

(* 除法下界比较器（lne_div_le_inv 对偶）：0 < y、z·y ≤ x ⟹ z ≤ x/y *)
Lemma bl_div_ge : forall x y z : Q, Qlt 0 y -> Qle (z * y) x -> QleT' z (x / y).
Proof.
  intros x y z Hy Hzy. apply Qle_to_QleT'. unfold Qdiv.
  assert (Hy0 : ~ (y == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q y Hy). exact (Qeq_sym _ _ E). }
  assert (Ey : (y * Qinv y)%Q == 1%Q) by (apply Qmult_inv_r; exact Hy0).
  assert (H1 : Qle ((z * y) * Qinv y) (x * Qinv y)).
  { apply (Qmult_le_compat_r (z * y) x).
    - exact Hzy.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hy. }
  rewrite <- (Qmult_assoc z y (Qinv y)) in H1.
  rewrite Ey in H1. rewrite Qmult_1_r in H1.
  exact H1.
Qed.

(* 右消元器：0 < s、a·s ≤ b·s ⟹ a ≤ b（内部走 bl_div_ge） *)
Lemma bl_cancel_r : forall a b s : Q, Qlt 0 s -> Qle (a * s) (b * s) -> QleT' a b.
Proof.
  intros a b s Hs H.
  assert (Hs0 : ~ (s == 0%Q)).
  { intro Ee. apply (Qlt_not_eq 0%Q s Hs). exact (Qeq_sym _ _ Ee). }
  assert (H1 : Qle a ((b * s) / s))
    by (apply QleT'_to_Qle; apply (bl_div_ge (b * s) s a Hs H)).
  assert (E : (b * s) / s == b).
  { unfold Qdiv.
    assert (E0 : (b * s) * Qinv s == b * (s * Qinv s)) by ring.
    rewrite E0, (Qmult_inv_r s Hs0), Qmult_1_r. reflexivity. }
  rewrite E in H1. exact (Qle_to_QleT' _ _ H1).
Qed.

(* 除法比较器（lne_div_eq 的不等式版）：0<y、0<s、x·s ≤ y·r ⟹ x/y ≤ r/s *)
Lemma bl_div_le : forall x y r s : Q,
  Qlt 0 y -> Qlt 0 s -> Qle (x * s) (y * r) -> QleT' (x / y) (r / s).
Proof.
  intros x y r s Hy Hs Hc. apply Qle_to_QleT'.
  assert (Hy0 : ~ (y == 0%Q)).
  { intro Ee. apply (Qlt_not_eq 0%Q y Hy). exact (Qeq_sym _ _ Ee). }
  assert (Hs0 : ~ (s == 0%Q)).
  { intro Ee. apply (Qlt_not_eq 0%Q s Hs). exact (Qeq_sym _ _ Ee). }
  assert (E : x / y == (x * s) / (y * s)).
  { apply (lne_div_eq x y (x * s) (y * s)).
    - exact Hy.
    - apply Qmult_lt_0_compat; assumption.
    - ring. }
  rewrite E. unfold Qdiv.
  rewrite (qeqT_imp_qeq _ _ (bl_qinv_mult y s Hy0 Hs0)).
  assert (E2 : (x * s) * (Qinv y * Qinv s) == (x * Qinv y) * (s * Qinv s)) by ring.
  rewrite E2.
  apply (Qle_trans _ (x * Qinv y)).
  - apply QleT'_to_Qle. apply qeq_imp_qle.
    assert (HT : (s * Qinv s)%Q == 1) by (apply Qmult_inv_r; exact Hs0).
    apply qeq_imp_qeqT. rewrite HT, Qmult_1_r. reflexivity.
  - apply QleT'_to_Qle. apply (bl_cancel_r (x * Qinv y) (r * Qinv s) s Hs).
    assert (E3 : (x * Qinv y) * s == (x * s) * Qinv y) by ring.
    rewrite E3.
    assert (E5 : (r * Qinv s) * s == r).
    { assert (E6 : (r * Qinv s) * s == r * (s * Qinv s)) by ring.
      rewrite E6, (Qmult_inv_r s Hs0), Qmult_1_r. reflexivity. }
    rewrite E5.
    apply (Qle_trans _ ((y * r) * Qinv y)).
    + apply (Qmult_le_compat_r (x * s) (y * r) (Qinv y)).
      * exact Hc.
      * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hy.
    + assert (E4 : (y * r) * Qinv y == r).
      { assert (E7 : (y * r) * Qinv y == r * (y * Qinv y)) by ring.
        rewrite E7, (Qmult_inv_r y Hy0), Qmult_1_r. reflexivity. }
      rewrite E4. apply Qle_refl.
Qed.

(* ============================================================ *)
(* §2 纯 nat 阶乘不等式核（lne_nat_core 同型；核证书线性 lia）          *)
(* ============================================================ *)

(* 主件核：3^n·8·(2n+1)! ≤ 16^n·16·(n!)²
   （⟺ (1/2)(3/16)^n ≤ (n!)²/(2n+1)!；步乘子 3(2n+3)(2n+2) ≤ 16(n+1)²
     经线性证书 3(2n+3) ≤ 8(n+1)（n≥1）×(2n+2) 达成） *)
Lemma bl_nat_core16 : forall n : nat,
  NatLe (3 ^ n * 8 * fact (2 * n + 1)) (16 ^ n * 16 * fact n * fact n).
Proof.
  intros n. apply NatLe_lift. induction n as [| n IH].
  - cbn. lia.
  - destruct n as [| m].
    + cbn. lia.
    + replace (2 * Datatypes.S (Datatypes.S m) + 1)%nat
        with (Datatypes.S (Datatypes.S (2 * Datatypes.S m + 1)))%nat by lia.
      cbn [fact].
      change (3 ^ Datatypes.S (Datatypes.S m))%nat with (3 * 3 ^ Datatypes.S m)%nat.
      change (16 ^ Datatypes.S (Datatypes.S m))%nat with (16 * 16 ^ Datatypes.S m)%nat.
      replace (Datatypes.S (Datatypes.S (2 * Datatypes.S m + 1)))
        with (2 * Datatypes.S (Datatypes.S m) + 1)%nat by lia.
      replace (Datatypes.S (2 * Datatypes.S m + 1))
        with (2 * Datatypes.S (Datatypes.S m))%nat by lia.
      assert (H1 : (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                    <= 8 * Datatypes.S (Datatypes.S m))%nat) by lia.
      assert (H2 : (3 * (2 * Datatypes.S (Datatypes.S m) + 1) * (2 * Datatypes.S (Datatypes.S m))
                    <= 8 * Datatypes.S (Datatypes.S m) * (2 * Datatypes.S (Datatypes.S m)))%nat)
        by (apply Nat.mul_le_mono_r; exact H1).
      assert (HAB : (3 * (2 * Datatypes.S (Datatypes.S m) + 1) * (2 * Datatypes.S (Datatypes.S m))
                     <= 16 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m))%nat).
      { apply (Nat.le_trans _ (8 * Datatypes.S (Datatypes.S m)
                                 * (2 * Datatypes.S (Datatypes.S m)))%nat).
        - exact H2.
        - lia. }
      transitivity ((16 ^ Datatypes.S m * 16 * fact (Datatypes.S m) * fact (Datatypes.S m))
                      * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                           * (2 * Datatypes.S (Datatypes.S m))))%nat.
      * replace ((3 * 3 ^ Datatypes.S m) * 8
                   * ((2 * Datatypes.S (Datatypes.S m) + 1)
                        * ((2 * Datatypes.S (Datatypes.S m)) * fact (2 * Datatypes.S m + 1))))%nat
          with ((3 ^ Datatypes.S m * 8 * fact (2 * Datatypes.S m + 1))
                  * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                       * (2 * Datatypes.S (Datatypes.S m))))%nat by ring.
        apply Nat.mul_le_mono_r. exact IH.
      * replace (Datatypes.S m * fact m)%nat with (fact (Datatypes.S m))%nat by reflexivity.
        replace ((16 * 16 ^ Datatypes.S m) * 16
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m))
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m)))%nat
          with ((16 ^ Datatypes.S m * 16 * fact (Datatypes.S m) * fact (Datatypes.S m))
                  * (16 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m)))%nat by ring.
        apply Nat.mul_le_mono_l. exact HAB.

Qed.

(* 最优档核：3^n·98·(2n+1)! ≤ 14^n·135·(n!)²
   （⟺ (98/135)(3/14)^n ≤ (n!)²/(2n+1)!；步乘子 3(2n+3)(2n+2) ≤ 14(n+1)²
     经线性证书 3(2n+3) ≤ 7(n+1)（n≥2）×(2n+2) 达成；n=2 等号 105840） *)
Lemma bl_nat_core14 : forall n : nat,
  NatLe (3 ^ n * 98 * fact (2 * n + 1)) (14 ^ n * 135 * fact n * fact n).
Proof.
  intros n. apply NatLe_lift. induction n as [| n IH].
  - cbn. lia.
  - destruct n as [| m].
    + cbn. lia.
    + destruct (Nat.eq_dec m 0) as [Hm0 | Hmpos].
      { subst m. cbn. lia. }
      replace (2 * Datatypes.S (Datatypes.S m) + 1)%nat
        with (Datatypes.S (Datatypes.S (2 * Datatypes.S m + 1)))%nat by lia.
      cbn [fact].
      change (3 ^ Datatypes.S (Datatypes.S m))%nat with (3 * 3 ^ Datatypes.S m)%nat.
      change (14 ^ Datatypes.S (Datatypes.S m))%nat with (14 * 14 ^ Datatypes.S m)%nat.
      replace (Datatypes.S (Datatypes.S (2 * Datatypes.S m + 1)))
        with (2 * Datatypes.S (Datatypes.S m) + 1)%nat by lia.
      replace (Datatypes.S (2 * Datatypes.S m + 1))
        with (2 * Datatypes.S (Datatypes.S m))%nat by lia.
      assert (H1 : (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                    <= 7 * Datatypes.S (Datatypes.S m))%nat) by lia.
      assert (H2 : (3 * (2 * Datatypes.S (Datatypes.S m) + 1) * (2 * Datatypes.S (Datatypes.S m))
                    <= 7 * Datatypes.S (Datatypes.S m) * (2 * Datatypes.S (Datatypes.S m)))%nat)
        by (apply Nat.mul_le_mono_r; exact H1).
      assert (HAB : (3 * (2 * Datatypes.S (Datatypes.S m) + 1) * (2 * Datatypes.S (Datatypes.S m))
                     <= 14 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m))%nat).
      { apply (Nat.le_trans _ (7 * Datatypes.S (Datatypes.S m)
                                 * (2 * Datatypes.S (Datatypes.S m)))%nat).
        - exact H2.
        - lia. }
      transitivity ((14 ^ Datatypes.S m * 135 * fact (Datatypes.S m) * fact (Datatypes.S m))
                      * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                           * (2 * Datatypes.S (Datatypes.S m))))%nat.
      * replace ((3 * 3 ^ Datatypes.S m) * 98
                   * ((2 * Datatypes.S (Datatypes.S m) + 1)
                        * ((2 * Datatypes.S (Datatypes.S m)) * fact (2 * Datatypes.S m + 1))))%nat
          with ((3 ^ Datatypes.S m * 98 * fact (2 * Datatypes.S m + 1))
                  * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                       * (2 * Datatypes.S (Datatypes.S m))))%nat by ring.
        apply Nat.mul_le_mono_r. exact IH.
      * replace (Datatypes.S m * fact m)%nat with (fact (Datatypes.S m))%nat by reflexivity.
        replace ((14 * 14 ^ Datatypes.S m) * 135
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m))
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m)))%nat
          with ((14 ^ Datatypes.S m * 135 * fact (Datatypes.S m) * fact (Datatypes.S m))
                  * (14 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m)))%nat by ring.
        apply Nat.mul_le_mono_l. exact HAB.

Qed.

(* ============================================================ *)
(* §3 Q 桥：目标常数幂 → 单除法 Z cast 形                               *)
(* ============================================================ *)

(* (1/2)·(3/16)^n == (3^n·8 # 1)/(16^n·16 # 1)
   （(1/2)(3/16)^n = 3^n/(2·16^n) = (8·3^n)/(16·16^n)） *)
Lemma bl_half_pow : forall n : nat,
  QeqT ((1 # 2) * q_pow (3 # 16) n)
       ((Z.of_nat (3 ^ n * 8) # 1) / (Z.of_nat (16 ^ n * 16) # 1)%Q).
Proof.
  (* 策略：3/16 拆为 3/1 ÷ 16/1 后由 bl_pow_div 分配幂，bl_pZ 换算
     cast，bl_mult_div_assoc 与 bl_qmake_mul 合并因子，lne_div_eq 收束。 *)
  intro n. apply qeq_imp_qeqT.
  replace (3 # 16)%Q with ((Z.of_nat 3 # 1) / (Z.of_nat 16 # 1))%Q by reflexivity.
  assert (Hnz : ~ ((Z.of_nat 16 # 1) == 0%Q)).
  { intro Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc.
    pose proof (proj1 (Nat2Z.inj_lt 0 16) ltac:(lia)). lia. }
  rewrite (qeqT_imp_qeq _ _ (bl_pow_div (Z.of_nat 3 # 1) (Z.of_nat 16 # 1) n Hnz)),
          (qeqT_imp_qeq _ _ (bl_pZ 3 n)), (qeqT_imp_qeq _ _ (bl_pZ 16 n)).
  assert (E1 : (Z.of_nat (3 ^ n * 8))%Z = (8 * Z.of_nat (3 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  assert (E2 : (Z.of_nat (16 ^ n * 16))%Z = (16 * Z.of_nat (16 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  rewrite E1, E2.
  rewrite (qeqT_imp_qeq _ _
             (bl_mult_div_assoc (1 # 2)%Q (Z.of_nat (3 ^ n) # 1) (Z.of_nat (16 ^ n) # 1))).
  rewrite <- (qeqT_imp_qeq _ _ (bl_qmake_mul 8%Z (Z.of_nat (3 ^ n)))).
  rewrite <- (qeqT_imp_qeq _ _ (bl_qmake_mul 16%Z (Z.of_nat (16 ^ n)))).
  apply lne_div_eq.
  - unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (NatLe_drop _ _ (bl_mul_ge1 16 n ltac:(lia))).
    pose proof (proj1 (Nat2Z.inj_lt 0 (16 ^ n)) ltac:(lia)). lia.
  - unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (NatLe_drop _ _ (bl_mul_ge1 16 n ltac:(lia))).
    pose proof (proj1 (Nat2Z.inj_lt 0 (16 ^ n)) ltac:(lia)). lia.
  - ring.
Qed.

(* (98/135)·(3/14)^n == (3^n·98 # 1)/(14^n·135 # 1) *)
Lemma bl_opt_pow : forall n : nat,
  QeqT ((98 # 135) * q_pow (3 # 14) n)
       ((Z.of_nat (3 ^ n * 98) # 1) / (Z.of_nat (14 ^ n * 135) # 1)%Q).
Proof.
  (* 策略与 bl_half_pow 相同：bl_pow_div 分配幂后合并为单一分式，
     经 bl_mult_div_assoc、bl_qmake_mul 与 lne_div_eq 收束。 *)
  intro n. apply qeq_imp_qeqT.
  replace (3 # 14)%Q with ((Z.of_nat 3 # 1) / (Z.of_nat 14 # 1))%Q by reflexivity.
  assert (Hnz : ~ ((Z.of_nat 14 # 1) == 0%Q)).
  { intro Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc.
    pose proof (proj1 (Nat2Z.inj_lt 0 14) ltac:(lia)). lia. }
  rewrite (qeqT_imp_qeq _ _ (bl_pow_div (Z.of_nat 3 # 1) (Z.of_nat 14 # 1) n Hnz)),
          (qeqT_imp_qeq _ _ (bl_pZ 3 n)), (qeqT_imp_qeq _ _ (bl_pZ 14 n)).
  assert (E1 : (Z.of_nat (3 ^ n * 98))%Z = (98 * Z.of_nat (3 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  assert (E2 : (Z.of_nat (14 ^ n * 135))%Z = (135 * Z.of_nat (14 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  rewrite E1, E2.
  rewrite (qeqT_imp_qeq _ _
             (bl_mult_div_assoc (98 # 135)%Q (Z.of_nat (3 ^ n) # 1) (Z.of_nat (14 ^ n) # 1))).
  rewrite <- (qeqT_imp_qeq _ _ (bl_qmake_mul 98%Z (Z.of_nat (3 ^ n)))).
  rewrite <- (qeqT_imp_qeq _ _ (bl_qmake_mul 135%Z (Z.of_nat (14 ^ n)))).
  apply lne_div_eq.
  - unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (NatLe_drop _ _ (bl_mul_ge1 14 n ltac:(lia))).
    pose proof (proj1 (Nat2Z.inj_lt 0 (14 ^ n)) ltac:(lia)). lia.
  - unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (NatLe_drop _ _ (bl_mul_ge1 14 n ltac:(lia))).
    pose proof (proj1 (Nat2Z.inj_lt 0 (14 ^ n)) ltac:(lia)). lia.
  - ring.
Qed.

(* ============================================================ *)
(* §4 主件（Set 面）                                                   *)
(* ============================================================ *)

(* 主件（规格档）：(1/2)·(3/16)^n ≤ lne_B n *)
Theorem bl_beta_lower : forall n : nat, QleT' ((1 # 2) * q_pow (3 # 16) n) (lne_B n).
Proof.
  intro n. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (bl_half_pow n)). rewrite lne_B_closed.
  apply QleT'_to_Qle. apply bl_div_le.
  - unfold Qlt. cbn [Qnum Qden].
    pose proof (NatLe_drop _ _ (bl_mul_ge1 16 n ltac:(lia))). lia.
  - apply QltT_to_Qlt. apply q_fact_pos.
  - rewrite (sif_qfact_Z n), (sif_qfact_Z (Datatypes.S (n + n))).
    pose proof (NatLe_drop _ _ (bl_nat_core16 n)) as Hnat.
    replace (2 * n + 1)%nat with (Datatypes.S (n + n))%nat in Hnat by lia.
    unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. lia.
Qed.

(* 最优档（族最优对，n=2/3 双缚等号）：(98/135)·(3/14)^n ≤ lne_B n *)
Theorem bl_beta_lower_opt : forall n : nat, QleT' ((98 # 135) * q_pow (3 # 14) n) (lne_B n).
Proof.
  intro n. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (bl_opt_pow n)). rewrite lne_B_closed.
  apply QleT'_to_Qle. apply bl_div_le.
  - unfold Qlt. cbn [Qnum Qden].
    pose proof (NatLe_drop _ _ (bl_mul_ge1 14 n ltac:(lia))). lia.
  - apply QltT_to_Qlt. apply q_fact_pos.
  - rewrite (sif_qfact_Z n), (sif_qfact_Z (Datatypes.S (n + n))).
    pose proof (NatLe_drop _ _ (bl_nat_core14 n)) as Hnat.
    replace (2 * n + 1)%nat with (Datatypes.S (n + n))%nat in Hnat by lia.
    unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. lia.
Qed.

(* 变体偏移件（(1+t) 面）：(1/4)·(3/32)^n ≤ 2^{−(n+1)}·lne_B n。
   注：右端 2^{−(n+1)}·lne_B n 是 (1+t)^{n+1} 变体积分 I'_n 的可证折叠
   承载（I'_n ≥ 2^{−(n+1)}·lne_B n 需全段逐点机，精确偏移另文登记）；
   (1/4)(3/32)^n = 2^{−(n+2)}(3/16)^n 与 Λ_n 下界需求精确匹配。 *)
Theorem bl_variant_shift : forall n : nat,
  QleT' ((1 # 4) * q_pow (3 # 32) n) (q_pow (1 # 2) (Datatypes.S n) * lne_B n).
Proof.
  intro n. apply Qle_to_QleT'.
  apply (Qle_trans _ (q_pow (1 # 2) (Datatypes.S n) * ((1 # 2) * q_pow (3 # 16) n))).
  - (* 左支路：(1/4)(3/32)^n == (1/2)^{n+1}·(1/2)(3/16)^n 等号桥（LHS 无 A·因子形，
       bl_mlc 结论 z·x ≤ z·y 与之 unify 必败——须走 qeq_imp_qle 等式轨） *)
    apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    replace (3 # 32) with ((1 # 2) * (3 # 16))%Q by reflexivity.
    rewrite <- (qeqT_imp_qeq _ _ (bl_qpow_mul (1 # 2) (3 # 16) n)).
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 # 2) n)).
    ring.
  - (* 右支路：A·(1/2)(3/16)^n ≤ A·lne_B n——bl_mlc（0 ≤ A 左乘保序）正位 *)
    apply QleT'_to_Qle. apply (bl_mlc _ _ (q_pow (1 # 2) (Datatypes.S n))).
    + apply QleT'_to_Qle. apply bl_beta_lower.
    + apply QleT'_to_Qle. apply (q_pow_nonneg (1 # 2) (Datatypes.S n)).
      apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* ============================================================ *)
(* §5 数值锚哨（n=0..3 vm_compute 实例 + 载体值见证）                    *)
(* ============================================================ *)

Lemma bl_spec_anchor0 : QleT' ((1 # 2) * q_pow (3 # 16) 0) (lne_B 0).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_spec_anchor1 : QleT' ((1 # 2) * q_pow (3 # 16) 1) (lne_B 1).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_spec_anchor2 : QleT' ((1 # 2) * q_pow (3 # 16) 2) (lne_B 2).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_spec_anchor3 : QleT' ((1 # 2) * q_pow (3 # 16) 3) (lne_B 3).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_opt_anchor0 : QleT' ((98 # 135) * q_pow (3 # 14) 0) (lne_B 0).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_opt_anchor1 : QleT' ((98 # 135) * q_pow (3 # 14) 1) (lne_B 1).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_opt_anchor2 : QleT' ((98 # 135) * q_pow (3 # 14) 2) (lne_B 2).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_opt_anchor3 : QleT' ((98 # 135) * q_pow (3 # 14) 3) (lne_B 3).
Proof. vm_compute. reflexivity. Qed.

(* 变体折叠 n=3 锚：2^{-4}·(1/140) = 1/2240 ≥ 27/131072 *)
Lemma bl_var_anchor3 : QleT' ((1 # 4) * q_pow (3 # 32) 3) (q_pow (1 # 2) 3 * lne_B 3).
Proof. vm_compute. reflexivity. Qed.

(* 载体值见证（Beta 闭式数值面）：1, 1/6, 1/30, 1/140 *)
Lemma bl_value1 : QeqT (lne_B 1) (1 # 6).
Proof. apply qeq_imp_qeqT. rewrite lne_B_closed. reflexivity. Qed.

Lemma bl_value2 : QeqT (lne_B 2) (1 # 30).
Proof. apply qeq_imp_qeqT. rewrite lne_B_closed. reflexivity. Qed.

Lemma bl_value3 : QeqT (lne_B 3) (1 # 140).
Proof. apply qeq_imp_qeqT. rewrite lne_B_closed. reflexivity. Qed.

(* ============================================================ *)
(* §6 提取检验 + 公理面自审                                             *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction bl_beta_lower bl_beta_lower_opt bl_variant_shift
  bl_spec_anchor3 bl_var_anchor3 lne_B q_pow.

Print Assumptions bl_beta_lower.
Print Assumptions bl_beta_lower_opt.
Print Assumptions bl_variant_shift.
