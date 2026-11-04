(* ============================================================ *)
(* abl_z2_valbridge.v —— ζ2 塔 Hanson 链 M1′ 赋值桥（B(n) ∣ C(n)）      *)
(*                                                               *)
(* 使命：d_n := lcm(1..n) ≤ 3^n（Hanson 1972）终前置件第二段。交付      *)
(*   赋值桥：对 C(n) := n!/∏_i⌊n/a_i⌋!（a_i 为 Sylvester 序列，         *)
(*   承载沿用 abl_z2_dub3 之 z2d_sylv_a/z2d_sylv_sum），证明            *)
(*   B(n) := hl_lcm_upto n 整除 C(n)。证途三步：其一，Legendre 和        *)
(*   恒等式 v_p(m!) = Σ_{j≥1}⌊m/p^j⌋（以库内赋值函数 plm_v 为仲裁，      *)
(*   燃料式定和 z2v_leg 两向夹逼）；其二，嵌套除法                        *)
(*   ⌊⌊n/p^j⌋/a⌋ = ⌊n/(a·p^j)⌋（stdlib Nat.div_div）；其三，逐层比较：   *)
(*   对每层 j 取 s = ⌊n/p^j⌋ ≥ 1，Sylvester 稠密不等式（z2d_sylv_floor_t）*)
(*   给 1 + Σ_i⌊s/a_{j+1}⌋ ≤ s，逐层求和得 ⌊log_p n⌋ ≤ v_p(C(n))，      *)
(*   再经全数整除折叠（h3_lcm_fold_divide）与强归纳素因子拆分完成证明。      *)
(* 数学内容：Hanson（Canad. Math. Bull. 15 (1972)，33–37）引理二：       *)
(*   v_p(C(n)) = Σ_j⌊n/p^j⌋ − Σ_{i,j}⌊n/(a_i p^j)⌋                      *)
(*   ≥ Σ_{j≤⌊log_p n⌋}[⌊n/p^j⌋ − Σ_i⌊⌊n/p^j⌋/a_i⌋] ≥ ⌊log_p n⌋。        *)
(*   分母积 ∏_i⌊n/a_i⌋! 整除 n! 由二项式系数阶乘拆分式                    *)
(*   fact(s+m) = fact s · fact m · C(s+m, m)（h3_prod_binom_fact 之      *)
(*   恒等式形）与 Sylvester 和的有限性（Σ_i⌊n/a_i⌋ < n）承担。           *)
(* 依赖：Stdlib（Arith.Arith/Arith.Factorial/Lia）+ HansonLcm +          *)
(*   Hanson3Pow + abl_z2_dub3（Sylvester 承载与稠密不等式）+             *)
(*   abl_Pr_core_01/abl_Pr_lcmdecomp_04（素性谓词与赋值函数 plm_v）。    *)
(* 构造性：全件 Qed，零公理声明、零承认、零经典逻辑；主语句面             *)
(*   z2v_dvd_t : Set（hl_id 承载，mod 零判据）；支撑引理语句面谓词位      *)
(*   以 hl_id/hl_le_t 承载（Set）；z2v_leg/z2v_cnt/z2v_pc/z2v_den/z2v_lsum *)
(*   皆 Fixpoint 可执行；文尾 Print Assumptions 全语句清单复核。         *)
(* 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*   ulimit -s 65532 && nice -19 rocq c -native-compiler no               *)
(*   -Q vo_local_world_unified_0930 "" -Q . "" abl_z2_valbridge.v         *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith Arith.Factorial List Lia.
Require Import HansonLcm.
Require Import Hanson3Pow.
Require Import abl_z2_dub3.
Require Import S01_BaseRing (Id, id_refl, NatLe, NatLe_drop).
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.

(* ============================================================ *)
(* §0 承载定义                                                          *)
(* ============================================================ *)

(* Σ_{i<K} ⌊m/p^{i+1}⌋：Legendre 定和（燃料式；p^{i+1} > m 的项自然为零） *)
Fixpoint z2v_leg (p K m : nat) : nat :=
  match K with
  | O => 0
  | S K' => z2v_leg p K' m + m / p ^ (S K')
  end.

(* #{i < K : p^{i+1} ∣ t}：逐层整除计数（Legendre 和的增量形式） *)
Fixpoint z2v_cnt (p K t : nat) : nat :=
  match K with
  | O => 0
  | S K' => z2v_cnt p K' t + (if Nat.eqb (t mod p ^ (S K')) 0 then 1 else 0)
  end.

(* #{i < K : p^{i+1} ≤ n}：层计数（⌊log_p n⌋ 的燃料式承载） *)
Fixpoint z2v_pc (p K n : nat) : nat :=
  match K with
  | O => 0
  | S K' => z2v_pc p K' n + (if Nat.leb 1 (n / p ^ (S K')) then 1 else 0)
  end.

(* ∏_{j<k} ⌊n/a_{j+1}⌋!：C(n) 的分母积（a_{j+1} > n 的因子为 0! = 1） *)
Fixpoint z2v_den (k n : nat) : nat :=
  match k with
  | O => 1
  | S k' => z2v_den k' n * fact (n / z2d_sylv_a k')
  end.

(* Σ_{i<K} z2d_sylv_sum k ⌊n/p^{i+1}⌋：逐层 Sylvester 和之层和 *)
Fixpoint z2v_lsum (p K k n : nat) : nat :=
  match K with
  | O => 0
  | S K' => z2v_lsum p K' k n + z2d_sylv_sum k (n / p ^ (S K'))
  end.

(* C(n) := n!/∏_i⌊n/a_i⌋!（分母积取 k = n 的规范层界） *)
Definition z2v_C (n : nat) : nat := fact n / z2v_den n n.

(* Set 面整除判据：b mod a = 0 的 hl_id 承载 *)
Definition z2v_dvd_t (a b : nat) : Set := hl_id (Nat.modulo b a) 0.

(* 幂分裂见证型：sigT 体位 `*` 记法作用域坑的显 `: Set` 注记承载 *)
Definition z2v_split_t (p c x y c1 c2 : nat) : Set :=
  (hl_id (c1 + c2) c) *
  (z2v_dvd_t (p ^ c1) x * z2v_dvd_t (p ^ c2) y).

(* S01 Id 承载到 Prop 等式的消除桥（J 消除式·id_sym 家族同构） *)
Lemma z2v_idS_eq : forall (A : Set) (x y : A), Id x y -> x = y.
Proof.
  intros A x y H.
  exact (match H in Id _ z return x = z with id_refl => eq_refl end).
Qed.

(* Prop 等式到 hl_id 承载的传递桥（hl_id_eq 之对偶方向） *)
Lemma z2v_id_of_eq : forall (A : Set) (x y : A), x = y -> hl_id x y.
Proof.
  intros A x y E. induction E. apply hl_idrefl.
Qed.

(* ============================================================ *)
(* §1 幂与和的小工具                                                    *)
(* ============================================================ *)

(* 幂的单调整除：a ≤ b 则 p^a ∣ p^b *)
Lemma z2v_pow_dvd : forall p a b : nat,
  a <= b -> Nat.divide (p ^ a) (p ^ b).
Proof.
  intros p a b Hle.
  replace b with (a + (b - a)) by lia.
  rewrite Nat.pow_add_r.
  exists (p ^ (b - a)). apply Nat.mul_comm.
Qed.

(* 幂正性：1 ≤ p 则 1 ≤ p^e *)
Lemma z2v_pow_pos : forall p e : nat, 1 <= p -> hl_le_t 1 (p ^ e).
Proof.
  intros p e Hp. apply hl_le_to_le_t. assert (Hp0 : p <> 0) by lia.
  pose proof (Nat.pow_nonzero p e Hp0). lia.
Qed.

(* Sylvester 和的零底：z2d_sylv_sum k 0 = 0 *)
Lemma z2v_sylv_sum_0 : forall k : nat, hl_id (z2d_sylv_sum k 0) 0.
Proof.
  intros k. apply z2v_id_of_eq.
  induction k as [| k IH]; [reflexivity |].
  cbn [z2d_sylv_sum]. rewrite IH, Nat.Div0.div_0_l. lia.
Qed.

(* Legendre 和的零底：z2v_leg p K 0 = 0 *)
Lemma z2v_leg_0 : forall p K : nat, hl_id (z2v_leg p K 0) 0.
Proof.
  intros p K. apply z2v_id_of_eq.
  induction K as [| K IH]; [reflexivity |].
  cbn [z2v_leg]. rewrite IH, Nat.Div0.div_0_l. lia.
Qed.

(* 分母积正性：1 ≤ z2v_den k n *)
Lemma z2v_den_pos : forall k n : nat, hl_le_t 1 (z2v_den k n).
Proof.
  induction k as [| k IH]; intro n.
  - cbn [z2v_den]. apply hl_le_to_le_t. lia.
  - cbn [z2v_den]. apply hl_le_to_le_t.
    pose proof (hl_le_t_to_le _ _ (IH n)) as IHp.
    pose proof (hl_le_t_to_le _ _ (h3_fact_pos (n / z2d_sylv_a k))) as Hfp.
    lia.
Qed.

(* ============================================================ *)
(* §2 赋值面：plm_v 的加性与幂分裂                                      *)
(* ============================================================ *)

(* plm_v p 1 = 0（1 < p） *)
Lemma z2v_v_1 : forall p : nat, 1 < p -> hl_id (plm_v p 1) 0.
Proof.
  intros p Hp. apply z2v_id_of_eq. unfold plm_v. cbn [plm_vmax Nat.pow].
  rewrite Nat.mul_1_r.
  rewrite (Nat.mod_small 1 p) by lia.
  reflexivity.
Qed.

(* 幂分裂：p^c ∣ x·y 则存在 c₁ + c₂ = c 的双整除拆分
   （素数整除积则整除一因子，逐层消 p 递降） *)
Lemma z2v_pow_split : forall p c x y : nat,
  pr_prime p -> Nat.divide (p ^ c) (x * y) ->
  sigT (fun c1 : nat => sigT (fun c2 : nat =>
    z2v_split_t p c x y c1 c2)).
Proof.
  intros p c. induction c as [| c IH]; intros x y Hpp Hd.
  - exists 0, 0. split; [apply z2v_id_of_eq; reflexivity | split].
    + unfold z2v_dvd_t. cbn [Nat.pow]. rewrite Nat.mod_1_r. apply hl_idrefl.
    + unfold z2v_dvd_t. cbn [Nat.pow]. rewrite Nat.mod_1_r. apply hl_idrefl.
  - assert (Hp0 : p <> 0) by (pose proof (NatLe_drop _ _ (fst Hpp)); lia).
    assert (Hp1 : Nat.divide p (x * y)).
    { apply (hl_div_trans p (p ^ S c) (x * y)); [| exact Hd].
      exists (p ^ c). rewrite Nat.pow_succ_r'. apply Nat.mul_comm. }
    destruct (plm_prime_dvd_mul p x y Hpp Hp1) as [Hdx | Hdy].
    + assert (Hxm : x mod p = 0).
      { exact (z2v_idS_eq _ _ _ (pr_dvd_mod0 p x ltac:(lia) Hdx)). }
      assert (Hxq : x = p * (x / p))
        by (pose proof (Nat.div_mod_eq x p) as Hdm;
            rewrite Hxm in Hdm; rewrite Nat.add_0_r in Hdm; exact Hdm).
      assert (Hdc : Nat.divide (p ^ c) ((x / p) * y)).
      { destruct Hd as [t Ht]. exists t.
        pose proof (Nat.pow_succ_r' p c) as HpS. rewrite HpS in Ht.
        rewrite Hxq in Ht.
        apply (proj1 (Nat.mul_cancel_r ((x / p) * y) (t * p ^ c) p Hp0)).
        replace ((x / p) * y * p) with (p * (x / p) * y) by ring.
        rewrite Ht. ring. }
      destruct (IH (x / p) y Hpp Hdc) as [c1 [c2 [Heq [Hd1 Hd2]]]].
      pose proof (hl_id_eq _ _ _ Heq) as HeqP.
      exists (S c1), c2. split; [apply z2v_id_of_eq; lia | split].
      * unfold z2v_dvd_t. apply z2v_id_of_eq.
        assert (Hxt : Nat.divide (p ^ S c1) x).
        { rewrite Hxq.
          destruct (pr_mod0_dvd (p ^ c1) (x / p)
                      ltac:(pose proof (Nat.pow_nonzero p c1 Hp0); lia)
                      (hl_id_eq _ _ _ Hd1)) as [q Hq].
          exists q. rewrite Hq, Nat.pow_succ_r'. ring. }
        exact (z2v_idS_eq _ _ _
                 (pr_dvd_mod0 (p ^ S c1) x
                    ltac:(pose proof (Nat.pow_nonzero p (S c1) Hp0); lia)
                    Hxt)).
      * exact Hd2.
    + assert (Hym : y mod p = 0).
      { exact (z2v_idS_eq _ _ _ (pr_dvd_mod0 p y ltac:(lia) Hdy)). }
      assert (Hyq : y = p * (y / p))
        by (pose proof (Nat.div_mod_eq y p) as Hdm;
            rewrite Hym in Hdm; rewrite Nat.add_0_r in Hdm; exact Hdm).
      assert (Hdc : Nat.divide (p ^ c) (x * (y / p))).
      { destruct Hd as [t Ht]. exists t.
        pose proof (Nat.pow_succ_r' p c) as HpS. rewrite HpS in Ht.
        rewrite Hyq in Ht.
        apply (proj1 (Nat.mul_cancel_r (x * (y / p)) (t * p ^ c) p Hp0)).
        replace (x * (y / p) * p) with (x * (p * (y / p))) by ring.
        rewrite Ht. ring. }
      destruct (IH x (y / p) Hpp Hdc) as [c1 [c2 [Heq [Hd1 Hd2]]]].
      pose proof (hl_id_eq _ _ _ Heq) as HeqP.
      exists c1, (S c2). split; [apply z2v_id_of_eq; lia | split].
      * exact Hd1.
      * unfold z2v_dvd_t. apply z2v_id_of_eq.
        assert (Hyt : Nat.divide (p ^ S c2) y).
        { rewrite Hyq.
          destruct (pr_mod0_dvd (p ^ c2) (y / p)
                      ltac:(pose proof (Nat.pow_nonzero p c2 Hp0); lia)
                      (hl_id_eq _ _ _ Hd2)) as [q Hq].
          exists q. rewrite Hq, Nat.pow_succ_r'. ring. }
        exact (z2v_idS_eq _ _ _
                 (pr_dvd_mod0 (p ^ S c2) y
                    ltac:(pose proof (Nat.pow_nonzero p (S c2) Hp0); lia)
                    Hyt)).
Qed.

(* 赋值加性：v_p(x·y) = v_p(x) + v_p(y)（x, y ≥ 1，p 素）
   下界：p^{a+b} ∣ x·y 而 p^{v+1} ∤ x·y 夹逼；上界：p^{S(a+b)} ∣ x·y
   经幂分裂得 p^{S a} ∣ x 或 p^{S b} ∣ y，与极大性相斥。 *)
Lemma z2v_v_add : forall p x y : nat,
  pr_prime p -> 1 <= x -> 1 <= y ->
  hl_id (plm_v p (x * y)) (plm_v p x + plm_v p y).
Proof.
  intros p x y Hpp Hx Hy. apply z2v_id_of_eq.
  pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2. assert (Hp1lt : 1 < p) by lia.
  assert (Hp0 : p <> 0) by lia.
  assert (Hxy1 : 1 <= x * y) by lia.
  pose proof (plm_v_dvd p (x * y)) as Hdxy.
  pose proof (plm_v_max p (x * y) Hp1lt Hxy1) as Hndxy.
  pose proof (plm_v_dvd p x) as Hdx.
  pose proof (plm_v_max p x Hp1lt Hx) as Hndx.
  pose proof (plm_v_dvd p y) as Hdy.
  pose proof (plm_v_max p y Hp1lt Hy) as Hndy.
  assert (Hge : plm_v p x + plm_v p y <= plm_v p (x * y)).
  { destruct (Nat.le_gt_cases (plm_v p x + plm_v p y) (plm_v p (x * y))) as [H|H];
      [exact H |].
    exfalso. apply Hndxy.
    apply (hl_div_trans (p ^ S (plm_v p (x * y)))
             (p ^ (plm_v p x + plm_v p y)) (x * y)).
    - apply z2v_pow_dvd. lia.
    - rewrite Nat.pow_add_r.
      destruct Hdx as [w1 Hw1]. destruct Hdy as [w2 Hw2].
      exists (w1 * w2).
      rewrite Hw1 at 1. rewrite Hw2 at 1. ring. }
  assert (Hle : plm_v p (x * y) <= plm_v p x + plm_v p y).
  { destruct (Nat.le_gt_cases (plm_v p (x * y)) (plm_v p x + plm_v p y)) as [H|H];
      [exact H |].
    exfalso.
    assert (Hd2 : Nat.divide (p ^ S (plm_v p x + plm_v p y)) (x * y)).
    { apply (hl_div_trans (p ^ S (plm_v p x + plm_v p y))
               (p ^ plm_v p (x * y)) (x * y)).
      - apply z2v_pow_dvd. lia.
      - exact Hdxy. }
    destruct (z2v_pow_split p (S (plm_v p x + plm_v p y)) x y Hpp Hd2)
      as [c1 [c2 [Hc [Hc1 Hc2]]]].
    pose proof (hl_id_eq _ _ _ Hc) as HcP.
    assert (Hc1a : c1 <= plm_v p x).
    { destruct (Nat.le_gt_cases c1 (plm_v p x)) as [Hk1|Hgt]; [exact Hk1 |].
      exfalso. apply Hndx.
      apply (hl_div_trans (p ^ S (plm_v p x)) (p ^ c1) x).
      - apply z2v_pow_dvd. lia.
      - apply (pr_mod0_dvd (p ^ c1) x).
        + pose proof (Nat.pow_nonzero p c1 Hp0). lia.
        + exact (hl_id_eq _ _ _ Hc1). }
    assert (Hc2b : c2 <= plm_v p y).
    { destruct (Nat.le_gt_cases c2 (plm_v p y)) as [Hk2|Hgt]; [exact Hk2 |].
      exfalso. apply Hndy.
      apply (hl_div_trans (p ^ S (plm_v p y)) (p ^ c2) y).
      - apply z2v_pow_dvd. lia.
      - apply (pr_mod0_dvd (p ^ c2) y).
        + pose proof (Nat.pow_nonzero p c2 Hp0). lia.
        + exact (hl_id_eq _ _ _ Hc2). }
    lia. }
  lia.
Qed.

(* ============================================================ *)
(* §3 Legendre 恒等式（精确两向：plm_v p (fact m) = z2v_leg p K m）      *)
(* ============================================================ *)

(* 逐层增量：S m / d = m / d + [d ∣ S m]（商在层界的跳变恰为指示子） *)
Lemma z2v_inc : forall m d : nat,
  1 <= d ->
  hl_id (S m / d) (m / d + (if Nat.eqb (S m mod d) 0 then 1 else 0)).
Proof.
  intros m d Hd. apply z2v_id_of_eq. destruct d as [| d'].
  - lia.
  - pose proof (Nat.div_mod_eq m (S d')) as Hdm.
    pose proof (Nat.mod_upper_bound m (S d') ltac:(lia)) as Hlt.
    destruct (Nat.eq_dec (m mod S d' + 1) (S d')) as [Ecase|Ecase].
    + (* 满层档：r + 1 = d，S m 被 d 整除 *)
      assert (HSm : S m = S d' * S (m / S d')).
      { rewrite Hdm at 1. rewrite <- Nat.add_1_r, <- Nat.add_assoc, Ecase.
        rewrite (Nat.mul_succ_r (S d') (m / S d')). reflexivity. }
      rewrite HSm. rewrite (Nat.mul_comm (S d') (S (m / S d'))).
      rewrite Nat.div_mul by lia. rewrite Nat.mod_mul by lia.
      rewrite Nat.eqb_refl. change (if true then 1 else 0) with 1. lia.
    + (* 不满层档：r + 1 < d，商不变且余非零 *)
      assert (Hne : m mod S d' + 1 <> 0) by lia.
      assert (HSm : S m = S d' * (m / S d') + (m mod S d' + 1)).
      { rewrite Hdm at 1. rewrite <- Nat.add_1_r. lia. }
      rewrite HSm.
      rewrite (Nat.add_comm (S d' * (m / S d')) (m mod S d' + 1)).
      rewrite (Nat.mul_comm (S d') (m / S d')).
      rewrite (Nat.div_add (m mod S d' + 1) (m / S d') (S d')) by lia.
      rewrite (Nat.mod_add (m mod S d' + 1) (m / S d') (S d')) by lia.
      rewrite (Nat.div_small (m mod S d' + 1) (S d')) by lia.
      rewrite (Nat.mod_small (m mod S d' + 1) (S d')) by lia.
      pose proof (proj2 (Nat.eqb_neq (m mod S d' + 1) 0) Hne) as Eeqb.
      rewrite Eeqb. change (if false then 1 else 0) with 0. lia.
Qed.

(* Legendre 和的增量式：z2v_leg p K (S m) = z2v_leg p K m + 层计数 *)
Lemma z2v_leg_cnt : forall p K m : nat,
  1 <= p ->
  hl_id (z2v_leg p K (S m)) (z2v_leg p K m + z2v_cnt p K (S m)).
Proof.
  intros p K m Hp. apply z2v_id_of_eq. induction K as [| K IH].
  - reflexivity.
  - cbn [z2v_leg z2v_cnt]. rewrite IH.
    assert (HleK : 1 <= p ^ S K)
      by (exact (hl_le_t_to_le _ _ (z2v_pow_pos p (S K) Hp))).
    pose proof (hl_id_eq _ _ _ (z2v_inc m (p ^ S K) HleK)) as Hinc.
    rewrite Hinc. lia.
Qed.

(* 层计数的极小值形：z2v_cnt p K t = min K (plm_v p t)
   逐档：p^{S K} ∣ t 则 S K ≤ v 且前 K 层全计；否则 v < S K 且计满 v 层。 *)
Lemma z2v_cnt_min : forall p K t : nat,
  pr_prime p -> 1 <= t -> hl_id (z2v_cnt p K t) (Nat.min K (plm_v p t)).
Proof.
  intros p K t Hpp Ht. apply z2v_id_of_eq. pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  assert (Hp1lt : 1 < p) by lia.
  induction K as [| K IH].
  - reflexivity.
  - cbn [z2v_cnt]. rewrite IH.
    destruct (Nat.eqb (t mod p ^ S K) 0) eqn:Em.
    + apply Nat.eqb_eq in Em.
      assert (Hdv : Nat.divide (p ^ S K) t)
        by (apply (pr_mod0_dvd (p ^ S K) t);
            [pose proof (hl_le_t_to_le _ _ (z2v_pow_pos p (S K) ltac:(lia))); lia
            | exact Em]).
      assert (HKv : S K <= plm_v p t).
      { destruct (Nat.le_gt_cases (S K) (plm_v p t)) as [H|H]; [exact H|].
        exfalso. apply (plm_v_max p t Hp1lt Ht).
        apply (hl_div_trans (p ^ S (plm_v p t)) (p ^ S K) t).
        - apply z2v_pow_dvd. lia.
        - exact Hdv. }
      rewrite (Nat.min_l K (plm_v p t)) by lia.
      rewrite (Nat.min_l (S K) (plm_v p t)) by lia.
      change (if true then 1 else 0) with 1. lia.
    + apply Nat.eqb_neq in Em.
      assert (Hndv : Nat.divide (p ^ S K) t -> False).
      { intro Hdv. apply Em.
        exact (z2v_idS_eq _ _ _ (pr_dvd_mod0 (p ^ S K) t
                   ltac:(pose proof (hl_le_t_to_le _ _
                           (z2v_pow_pos p (S K) ltac:(lia))); lia)
                   Hdv)). }
      assert (HKv : plm_v p t <= K).
      { destruct (Nat.le_gt_cases (plm_v p t) K) as [H|H]; [exact H|].
        exfalso. apply Hndv.
        apply (hl_div_trans (p ^ S K) (p ^ plm_v p t) t).
        - apply z2v_pow_dvd. lia.
        - apply (plm_v_dvd p t). }
      rewrite (Nat.min_r K (plm_v p t)) by lia.
      rewrite (Nat.min_r (S K) (plm_v p t)) by lia.
      change (if false then 1 else 0) with 0. lia.
Qed.

(* Legendre 恒等式（精确）：p^K > m 则 v_p(m!) = Σ_{i<K}⌊m/p^{i+1}⌋。
   对 m 归纳：v_p((S m)!) = v_p(S m) + v_p(m!)（加性），而层和的增量
   恰为层计数 = min(K, v_p(S m)) = v_p(S m)（v_p(S m) < K 由 p^K > S m）。 *)
Lemma z2v_fact_ex : forall p m K : nat,
  pr_prime p -> p ^ K > m -> hl_id (plm_v p (fact m)) (z2v_leg p K m).
Proof.
  intros p m K Hpp. revert K.
  induction m as [| m IH]; intros K HK; apply z2v_id_of_eq.
  - cbn [fact]. assert (Hp1lt : 1 < p) by (pose proof (NatLe_drop _ _ (fst Hpp)); lia).
    pose proof (hl_id_eq _ _ _ (z2v_v_1 p Hp1lt)) as Hv1.
    pose proof (hl_id_eq _ _ _ (z2v_leg_0 p K)) as Hl0.
    rewrite Hv1, Hl0. reflexivity.
  - pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
    assert (HKm : p ^ K > m) by lia.
    assert (HvK : plm_v p (S m) < K).
    { destruct (Nat.le_gt_cases K (plm_v p (S m))) as [Hle|Hgt].
      - exfalso.
        pose proof (plm_v_dvd p (S m)) as Hdv.
        pose proof (Nat.divide_pos_le (p ^ plm_v p (S m)) (S m)
                      ltac:(lia) Hdv) as Hle1.
        pose proof (Nat.pow_le_mono_r p K (plm_v p (S m))
                      ltac:(lia) Hle) as Hpw.
        lia.
      - exact Hgt. }
    cbn [fact].
    pose proof (hl_id_eq _ _ _ (z2v_v_add p (S m) (fact m) Hpp ltac:(lia)
                  (hl_le_t_to_le _ _ (h3_fact_pos m)))) as Hvadd.
    rewrite Hvadd.
    rewrite (IH K HKm).
    pose proof (hl_id_eq _ _ _ (z2v_leg_cnt p K m
                  ltac:(pose proof (NatLe_drop _ _ (fst Hpp)); lia))) as Hlc.
    rewrite Hlc.
    pose proof (hl_id_eq _ _ _ (z2v_cnt_min p K (S m) Hpp ltac:(lia))) as Hcm.
    rewrite Hcm.
    rewrite (Nat.min_r K (plm_v p (S m))) by lia.
    lia.
Qed.

(* ============================================================ *)
(* §4 分母积的层界（嵌套除法）与整除面                                  *)
(* ============================================================ *)

(* 层和的换层恒等式：k 层推进一时，层和的增量恰为分母新因子的
   Legendre 和——逐层用嵌套除法 ⌊⌊n/p^j⌋/a⌋ = ⌊n/(a·p^j)⌋ = ⌊⌊n/a⌋/p^j⌋。 *)
Lemma z2v_lsum_S_k : forall p K k n : nat,
  1 <= p ->
  hl_id (z2v_lsum p K (S k) n)
        (z2v_lsum p K k n + z2v_leg p K (n / z2d_sylv_a k)).
Proof.
  intros p K k n Hp. apply z2v_id_of_eq. induction K as [| K IH].
  - reflexivity.
  - cbn [z2v_lsum z2v_leg]. rewrite IH. cbn [z2d_sylv_sum].
    assert (Hpk : p ^ S K <> 0)
      by (pose proof (Nat.pow_nonzero p (S K) ltac:(lia)); lia).
    assert (E : (n / p ^ S K) / z2d_sylv_a k = (n / z2d_sylv_a k) / p ^ S K).
    { rewrite (Nat.div_div n (z2d_sylv_a k) (p ^ S K))
        by (first [apply z2d_sylv_a_neq0 | exact Hpk]).
      rewrite (Nat.div_div n (p ^ S K) (z2d_sylv_a k))
        by (first [exact Hpk | apply z2d_sylv_a_neq0]).
      rewrite (Nat.mul_comm (p ^ S K) (z2d_sylv_a k)). reflexivity. }
    lia.
Qed.

(* 分母积的赋值上界：v_p(∏_{j<k}⌊n/a_{j+1}⌋!) ≤ Σ_{i<K} z2d_sylv_sum k ⌊n/p^{i+1}⌋
   （分母各因子的精确 Legendre 和经换层恒等式逐层归入 Sylvester 和） *)
Lemma z2v_den_val : forall p k n K : nat,
  pr_prime p -> p ^ K > n ->
  hl_le_t (plm_v p (z2v_den k n)) (z2v_lsum p K k n).
Proof.
  intros p k. induction k as [| k IH]; intros n K Hpp HK.
  - apply hl_le_to_le_t. cbn [z2v_den z2v_lsum].
    assert (Hp1lt : 1 < p) by (pose proof (NatLe_drop _ _ (fst Hpp)); lia).
    pose proof (hl_id_eq _ _ _ (z2v_v_1 p Hp1lt)) as Hv1. rewrite Hv1. lia.
  - apply hl_le_to_le_t.
    assert (Ha0 : z2d_sylv_a k <> 0) by apply z2d_sylv_a_neq0.
    assert (Ha1 : 1 <= z2d_sylv_a k) by lia.
    assert (Hle : n / z2d_sylv_a k <= n).
    { apply Nat.div_le_upper_bound; [exact Ha0 |].
      pose proof (Nat.mul_le_mono_r 1 (z2d_sylv_a k) n Ha1) as Hm.
      rewrite Nat.mul_1_l in Hm. exact Hm. }
    assert (HKm : p ^ K > n / z2d_sylv_a k) by lia.
    pose proof (hl_id_eq _ _ _ (z2v_lsum_S_k p K k n
                  ltac:(pose proof (NatLe_drop _ _ (fst Hpp)); lia))) as Hls.
    rewrite Hls.
    pose proof (hl_id_eq _ _ _ (z2v_v_add p (z2v_den k n)
                  (fact (n / z2d_sylv_a k)) Hpp
                  (hl_le_t_to_le _ _ (z2v_den_pos k n))
                  (hl_le_t_to_le _ _ (h3_fact_pos (n / z2d_sylv_a k))))) as Vadd.
    pose proof (hl_le_t_to_le _ _ (IH n K Hpp HK)) as VIH.
    pose proof (hl_id_eq _ _ _ (z2v_fact_ex p (n / z2d_sylv_a k) K Hpp HKm)) as Vex.
    cbn [z2v_den]. lia.
Qed.

(* 逐层 Sylvester 点态不等式：层指示子与层 Sylvester 和之和不超层商
   （s ≥ 1 用 z2d_sylv_floor_t 全强度；s = 0 两肢皆零） *)
Lemma z2v_pointwise : forall k s : nat,
  hl_le_t ((if Nat.leb 1 s then 1 else 0) + z2d_sylv_sum k s) s.
Proof.
  intros k s. apply hl_le_to_le_t. destruct (Nat.leb 1 s) eqn:E.
  - apply Nat.leb_le in E. change (if true then 1 else 0) with 1.
    pose proof (hl_le_t_to_le (z2d_sylv_sum k s + 1) s
                  (z2d_sylv_floor_t k s E)). lia.
  - apply Nat.leb_nle in E. change (if false then 1 else 0) with 0.
    assert (Hs0 : s = 0) by lia. subst s.
    rewrite z2v_sylv_sum_0. lia.
Qed.

(* 层和闭环：Σ_{i<K}[⌊n/p^{i+1}⌋ ≥ 1] + Σ_{i<K} z2d_sylv_sum k ⌊n/p^{i+1}⌋
   ≤ Σ_{i<K}⌊n/p^{i+1}⌋——逐层点态不等式的求和。 *)
Lemma z2v_layersum_bound : forall p K k n : nat,
  hl_le_t (z2v_lsum p K k n + z2v_pc p K n) (z2v_leg p K n).
Proof.
  intros p K k n. apply hl_le_to_le_t. induction K as [| K IH].
  - cbn [z2v_lsum z2v_pc z2v_leg]. lia.
  - cbn [z2v_lsum z2v_pc z2v_leg].
    pose proof (hl_le_t_to_le _ _ (z2v_pointwise k (n / p ^ S K))). lia.
Qed.

(* 层计数的下界：p^e ≤ n 且 e ≤ K 则 e ≤ #{i < K : p^{i+1} ≤ n} *)
Lemma z2v_pc_ge : forall p K e n : nat,
  1 < p -> p ^ e <= n -> e <= K -> hl_le_t e (z2v_pc p K n).
Proof.
  intros p K. induction K as [| K IH]; intros e n Hp He HKe;
    apply hl_le_to_le_t.
  - lia.
  - assert (Hp0 : p <> 0) by lia.
    destruct (Nat.eq_dec e (S K)) as [E|NE].
    + subst e. cbn [z2v_pc].
      assert (H1 : 1 <= n / p ^ S K).
      { destruct (n / p ^ S K) eqn:Eq.
        - exfalso.
          pose proof (Nat.div_mod_eq n (p ^ S K)) as Hdm. rewrite Eq in Hdm.
          pose proof (Nat.mod_upper_bound n (p ^ S K)
                        (Nat.pow_nonzero p (S K) Hp0)) as Hmb.
          lia.
        - lia. }
      pose proof (proj2 (Nat.leb_le 1 (n / p ^ S K)) H1) as Elb.
      rewrite Elb. change (if true then 1 else 0) with 1.
      assert (HpK : p ^ K <= n).
      { pose proof (Nat.pow_le_mono_r p K (S K) Hp0 (Nat.le_succ_diag_r K)).
        lia. }
      pose proof (hl_le_t_to_le _ _ (IH K n Hp HpK (Nat.le_refl K))). lia.
    + cbn [z2v_pc].
      pose proof (hl_le_t_to_le _ _ (IH e n Hp He ltac:(lia))). lia.
Qed.

(* 二因子阶乘拆分：fact (a + b) = fact b · h3_prod_from (S b) a——
   区间积承载的步进式恒等（h3_prod_binom_fact 给出二项式系数形）。 *)
Lemma z2v_fact_split : forall a b : nat,
  hl_id (fact (a + b)) (fact b * h3_prod_from (S b) a).
Proof.
  intros a b. apply z2v_id_of_eq. induction a as [| a IH].
  - rewrite Nat.mul_1_r. reflexivity.
  - replace (S a + b) with (S (a + b)) by lia.
    cbn [fact h3_prod_from]. rewrite IH.
    replace (S b + a) with (S (b + a)) by lia. ring.
Qed.

(* 分母积整除（一般形）：Σ_{j<k}⌊n/a_{j+1}⌋ + s ≤ n 则
   ∏_{j<k}⌊n/a_{j+1}⌋! · s! ∣ (s + Σ)!——逐因子以二项式系数为见证
   的伸缩（归纳不变量：分母积 · 剩余阶乘整除总阶乘）。 *)
Lemma z2v_den_dvd_gen : forall k n s : nat,
  s + z2d_sylv_sum k n <= n ->
  Nat.divide (z2v_den k n * fact s) (fact (s + z2d_sylv_sum k n)).
Proof.
  induction k as [| k IH]; intros n s Hs.
  - cbn [z2v_den z2d_sylv_sum]. rewrite Nat.add_0_r.
    exists 1. rewrite Nat.mul_1_l. ring.
  - cbn [z2v_den z2d_sylv_sum]. cbn [z2d_sylv_sum] in Hs.
    assert (Hstep : Nat.divide
              (fact (n / z2d_sylv_a k) * fact s)
              (fact (s + n / z2d_sylv_a k))).
    { pose proof (z2v_fact_split (n / z2d_sylv_a k) s) as Hfs.
      rewrite (Nat.add_comm (n / z2d_sylv_a k) s) in Hfs.
      pose proof (hl_id_eq _ _ _
                    (h3_prod_binom_fact s (n / z2d_sylv_a k))) as Hpb.
      rewrite Hpb in Hfs.
      exists (hl_binom (s + n / z2d_sylv_a k) (n / z2d_sylv_a k)).
      rewrite Hfs. ring. }
    assert (Hcomb : Nat.divide
              ((z2v_den k n * fact (n / z2d_sylv_a k)) * fact s)
              (z2v_den k n * fact (s + n / z2d_sylv_a k))).
    { destruct Hstep as [w Hw]. exists w.
      rewrite Hw. ring. }
    assert (HIH : Nat.divide
              (z2v_den k n * fact (s + n / z2d_sylv_a k))
              (fact ((s + n / z2d_sylv_a k) + z2d_sylv_sum k n))).
    { apply IH. lia. }
    rewrite <- Nat.add_assoc in HIH.
    rewrite (Nat.add_comm (n / z2d_sylv_a k) (z2d_sylv_sum k n)) in HIH.
    apply (hl_div_trans
             ((z2v_den k n * fact (n / z2d_sylv_a k)) * fact s)
             (z2v_den k n * fact (s + n / z2d_sylv_a k))
             (fact (s + (z2d_sylv_sum k n + n / z2d_sylv_a k)))).
    + exact Hcomb.
    + exact HIH.
Qed.

(* 分母积整除（主形）：1 ≤ n 则 ∏_{j≤n}⌊n/a_{j+1}⌋! ∣ n!——
   取 s = n − Σ（Sylvester 稠密不等式给 Σ + 1 ≤ n，故 s + Σ = n）。 *)
Lemma z2v_den_dvd : forall n : nat,
  1 <= n -> Nat.divide (z2v_den n n) (fact n).
Proof.
  intros n Hn.
  pose proof (hl_le_t_to_le (z2d_sylv_sum n n + 1) n
                (z2d_sylv_floor_t n n Hn)) as Hfl.
  pose proof (z2v_den_dvd_gen n n (n - z2d_sylv_sum n n) ltac:(lia)) as Hd.
  rewrite (Nat.sub_add (z2d_sylv_sum n n) n ltac:(lia)) in Hd.
  destruct Hd as [t Ht].
  exists (t * fact (n - z2d_sylv_sum n n)). rewrite Ht. ring.
Qed.

(* ============================================================ *)
(* §5 每素数定理：层计数 ≤ v_p(C(n))（逐层比较合拢）                     *)
(* ============================================================ *)

(* 每素数主链：z2v_pc p (S n) n ≤ plm_v p (C n)。
   链序：fact n = C n · den（分母积整除面的精确方程）⟹
   v_p(fact n) = v_p(den) + v_p(C n)（加性）；
   v_p(fact n) = z2v_leg p (S n) n（Legendre 精确式）；
   v_p(den) ≤ z2v_lsum（分母积层界）；
   z2v_lsum + z2v_pc ≤ z2v_leg（逐层比较闭环）。 *)
Theorem z2v_v_C_ge : forall p n : nat,
  pr_prime p -> 1 <= n -> hl_le_t (z2v_pc p (S n) n) (plm_v p (z2v_C n)).
Proof.
  intros p n Hpp Hn. apply hl_le_to_le_t. pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  pose proof (z2v_den_dvd n Hn) as Hdd.
  pose proof (hl_le_t_to_le _ _ (z2v_den_pos n n)) as Hdenpos.
  assert (Heq : fact n = z2v_den n n * z2v_C n).
  { unfold z2v_C.
    pose proof (z2v_idS_eq _ _ _
                  (pr_dvd_mod0 (z2v_den n n) (fact n) Hdenpos Hdd)) as Hm0.
    pose proof (Nat.div_mod_eq (fact n) (z2v_den n n)) as Hdm.
    rewrite Hm0, Nat.add_0_r in Hdm. exact Hdm. }
  assert (HCpos : 1 <= z2v_C n).
  { destruct (z2v_C n) eqn:EC.
    - exfalso. rewrite Nat.mul_0_r in Heq.
      pose proof (hl_le_t_to_le _ _ (h3_fact_pos n)). lia.
    - lia. }
  assert (Hgt : p ^ S n > n).
  { pose proof (Nat.pow_gt_lin_r p n Hp2) as H1.
    pose proof (Nat.pow_le_mono_r p n (S n)
                  ltac:(lia) (Nat.le_succ_diag_r n)) as H2. lia. }
  pose proof (hl_id_eq _ _ _
                (z2v_v_add p (z2v_den n n) (z2v_C n) Hpp Hdenpos HCpos)) as V1.
  rewrite <- Heq in V1.
  pose proof (hl_id_eq _ _ _ (z2v_fact_ex p n (S n) Hpp Hgt)) as V2.
  pose proof (hl_le_t_to_le _ _ (z2v_den_val p n n (S n) Hpp Hgt)) as V3.
  pose proof (hl_le_t_to_le _ _ (z2v_layersum_bound p (S n) n n)) as V4.
  lia.
Qed.

(* 素幂整除 C(n)：p^e ≤ n 则 p^e ∣ C(n)——Hanson 引理二的可用形态
   （e ≤ ⌊log_p n⌋ = 层计数 ≤ v_p(C n)，幂单调传递）。 *)
Theorem z2v_ppow_dvd_C : forall p e n : nat,
  pr_prime p -> p ^ e <= n -> Nat.divide (p ^ e) (z2v_C n).
Proof.
  intros p e n Hpp He. pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  assert (Hp1lt : 1 < p) by lia.
  assert (Hen : e <= S n) by (pose proof (Nat.pow_gt_lin_r p e Hp1lt); lia).
  assert (Hn1 : 1 <= n)
    by (pose proof (hl_le_t_to_le _ _ (z2v_pow_pos p e ltac:(lia))); lia).
  pose proof (hl_le_t_to_le _ _ (z2v_pc_ge p (S n) e n Hp1lt He Hen)) as Hpc.
  pose proof (hl_le_t_to_le _ _ (z2v_v_C_ge p n Hpp Hn1)) as V.
  apply (hl_div_trans (p ^ e) (p ^ plm_v p (z2v_C n)) (z2v_C n)).
  - apply z2v_pow_dvd. lia.
  - apply (plm_v_dvd p (z2v_C n)).
Qed.

(* ============================================================ *)
(* §6 全数整除与主定理：B(n) = hl_lcm_upto n ∣ C(n)                       *)
(* ============================================================ *)

(* 素幂的因子两分：d ∣ p^e 则 d = 1 或 p ∣ d（素数逐层消去） *)
Lemma z2v_dvd_pow_split : forall p e d : nat,
  pr_prime p -> hl_id ((p ^ e) mod d) 0 -> hl_id d 1 + z2v_dvd_t p d.
Proof.
  intros p e. induction e as [| e IH]; intros d Hpp Hd.
  - cbn [Nat.pow] in Hd.
    destruct d as [| d'].
    + right. unfold z2v_dvd_t. rewrite Nat.Div0.mod_0_l. apply hl_idrefl.
    + pose proof (hl_id_eq _ _ _ Hd) as Hm0.
      assert (Hd1 : S d' = 1).
      { pose proof (pr_mod0_dvd (S d') 1 ltac:(lia) Hm0) as Hdiv.
        destruct Hdiv as [z Hz].
        pose proof (proj1 (Nat.mul_eq_1 z (S d')) (eq_sym Hz)) as [Hz1 Hz2].
        exact Hz2. }
      left. apply z2v_id_of_eq. exact Hd1.
  - assert (Hp0 : p <> 0) by (pose proof (NatLe_drop _ _ (fst Hpp)); lia).
    assert (Hdpos : 1 <= d).
    { destruct d as [| d'].
      - exfalso. pose proof (hl_id_eq _ _ _ Hd) as Hmz.
        rewrite Nat.mod_0_r in Hmz.
        pose proof (Nat.pow_nonzero p (S e) Hp0). lia.
      - lia. }
    pose proof (hl_id_eq _ _ _ Hd) as Hm0.
    pose proof (pr_mod0_dvd d (p ^ S e) ltac:(exact Hdpos) Hm0) as Hdd.
    assert (Hzeq : p ^ S e = (p ^ S e / d) * d)
      by (pose proof (Nat.div_mod_eq (p ^ S e) d) as Hdm;
          rewrite Hm0, Nat.add_0_r in Hdm;
          rewrite (Nat.mul_comm d (p ^ S e / d)) in Hdm; exact Hdm).
    assert (Hpzd : Nat.divide p ((p ^ S e / d) * d)).
    { exists (p ^ e). rewrite <- Hzeq, Nat.pow_succ_r'. ring. }
    destruct (plm_prime_dvd_mul p (p ^ S e / d) d Hpp Hpzd) as [Hdz | Hdd2].
    + assert (Hd' : Nat.divide d (p ^ e)).
      { destruct Hdz as [w Hw].
        exists w.
        apply (proj1 (Nat.mul_cancel_r (p ^ e) (w * d) p Hp0)).
        rewrite (Nat.mul_comm (p ^ e) p).
        change (p * p ^ e) with (p ^ S e).
        rewrite Hzeq, Hw. ring. }
      assert (Hin : hl_id ((p ^ e) mod d) 0).
      { apply z2v_id_of_eq.
        exact (z2v_idS_eq _ _ _ (pr_dvd_mod0 d (p ^ e) Hdpos Hd')). }
      destruct (IH d Hpp Hin) as [Hi | Hid].
      * left. exact Hi.
      * right. exact Hid.
    + right. unfold z2v_dvd_t. apply z2v_id_of_eq.
      exact (z2v_idS_eq _ _ _ (pr_dvd_mod0 p d ltac:(lia) Hdd2)).
Qed.

(* 素幂与素的互素：p 素且 p 不整除 u 则 gcd(p^e, u) = 1 *)
Lemma z2v_gcd_pow_prime : forall p e u : nat,
  pr_prime p -> (Nat.divide p u -> False) ->
  hl_id (Nat.gcd (p ^ e) u) 1.
Proof.
  intros p e u Hpp Hu.
  assert (Hp0 : p <> 0) by (pose proof (NatLe_drop _ _ (fst Hpp)); lia).
  pose proof (Nat.gcd_divide_l (p ^ e) u) as Hgl.
  assert (Hgcd : 1 <= Nat.gcd (p ^ e) u).
  { destruct (Nat.eq_dec (Nat.gcd (p ^ e) u) 0) as [Ez | NEz]; [| lia].
    exfalso.
    destruct Hgl as [z Hz]. rewrite Ez in Hz.
    pose proof (Nat.pow_nonzero p e Hp0). lia. }
  assert (Hin : hl_id ((p ^ e) mod Nat.gcd (p ^ e) u) 0).
  { apply z2v_id_of_eq.
    exact (z2v_idS_eq _ _ _ (pr_dvd_mod0 (Nat.gcd (p ^ e) u) (p ^ e)
               Hgcd Hgl)). }
  destruct (z2v_dvd_pow_split p e (Nat.gcd (p ^ e) u) Hpp Hin) as [H1 | Hpd].
  - exact H1.
  - exfalso. apply Hu.
    apply (hl_div_trans p (Nat.gcd (p ^ e) u) u).
    + apply (pr_mod0_dvd p (Nat.gcd (p ^ e) u));
        [pose proof (NatLe_drop _ _ (fst Hpp)); lia
        | exact (hl_id_eq _ _ _ Hpd)].
    + apply Nat.gcd_divide_r.
Qed.

(* 全数整除（强归纳）：1 ≤ m ≤ n 则 m ∣ C(n)。
   归纳步：素因子分解见证取素因子 p，m = p^e·u（e = v_p(m) 全幂拆分，
   u 与 p 互素）；u ∣ C(n) 归纳，p^e ∣ C(n) 由素幂定理，二者以
   gcd = 1 的乘法整除合成；m = 1 平凡。 *)
Theorem z2v_m_dvd_C : forall m n : nat,
  1 <= m -> m <= n -> Nat.divide m (z2v_C n).
Proof.
  intro m. induction m as [m IH] using (well_founded_induction_type Wf_nat.lt_wf).
  intros n Hm1 Hmn. destruct m as [| m'].
  - lia.
  - destruct (Nat.eq_dec (S m') 1) as [E1|NE1].
    + rewrite E1. apply Nat.divide_1_l.
    + assert (Hm2 : 2 <= S m') by lia.
      destruct (pr_factor_exists (S m') Hm2) as [l [Hprim Hfold]].
      destruct l as [| p rest].
      * cbn [fold_right] in Hfold.
        pose proof (z2v_idS_eq _ _ _ Hfold) as HfoldP. lia.
      * pose proof (Hprim p (or_introl eq_refl)) as Hpp.
        pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2. assert (Hp1lt : 1 < p) by lia.
        cbn [fold_right] in Hfold.
        set (m0 := fold_right Nat.mul 1 rest) in Hfold.
        pose proof (z2v_idS_eq _ _ _ Hfold) as HfoldP.
        pose proof (plm_v_dvd p (S m')) as Hpe0.
        destruct Hpe0 as [u Hu].
        assert (Hdivp : Nat.divide p (S m')).
        { exists m0. rewrite <- HfoldP. apply Nat.mul_comm. }
        assert (He1 : 1 <= plm_v p (S m')).
        { destruct (Nat.eq_dec (plm_v p (S m')) 0) as [E0|Hne0]; [| lia].
          exfalso. apply (plm_v_max p (S m') Hp1lt ltac:(lia)).
          rewrite E0. cbn [Nat.pow]. rewrite Nat.mul_1_r. exact Hdivp. }
        assert (Hnpu : Nat.divide p u -> False).
        { intro Hpu. destruct Hpu as [w Hw].
          apply (plm_v_max p (S m') Hp1lt ltac:(lia)).
          exists w. rewrite Hu at 1. rewrite Nat.pow_succ_r', Hw. ring. }
        pose proof (hl_id_eq _ _ _
                      (z2v_gcd_pow_prime p (plm_v p (S m')) u Hpp Hnpu)) as Hgc.
        assert (Hu1 : 1 <= u).
        { destruct u as [| u'']; [rewrite Nat.mul_0_l in Hu; lia | lia]. }
        assert (HpE2 : 2 <= p ^ plm_v p (S m')).
        { pose proof (Nat.pow_le_mono_r p 1 (plm_v p (S m')) ltac:(lia) He1) as H1.
          cbn [Nat.pow] in H1. lia. }
        assert (Hult : u < S m').
        { pose proof (Nat.mul_le_mono_l 2 (p ^ plm_v p (S m')) u HpE2). lia. }
        assert (HpeC : Nat.divide (p ^ plm_v p (S m')) (z2v_C n)).
        { apply (z2v_ppow_dvd_C p (plm_v p (S m')) n Hpp).
          pose proof (Nat.divide_pos_le (p ^ plm_v p (S m')) (S m')
                        ltac:(lia) (plm_v_dvd p (S m'))) as Hle1.
          lia. }
        assert (HuC : Nat.divide u (z2v_C n)).
        { apply IH; [lia | exact Hu1 |].
          apply (Nat.le_trans u (S m') n);
            [exact (Nat.lt_le_incl _ _ Hult) | exact Hmn]. }
        pose proof (plm_dvd_mul_coprime (p ^ plm_v p (S m')) u (z2v_C n)
                      HpeC HuC Hgc) as Hcomb.
        rewrite Hu, (Nat.mul_comm u (p ^ plm_v p (S m'))). exact Hcomb.
Qed.

(* 主定理（Prop 面）：B(n) = hl_lcm_upto n ∣ C(n)
   ——h3_lcm_fold_divide 以全数整除假设折叠。 *)
Theorem z2v_lcm_dvd_C : forall n : nat, Nat.divide (hl_lcm_upto n) (z2v_C n).
Proof.
  intro n. apply (h3_lcm_fold_divide n (z2v_C n)).
  intros m Hm1 Hm2. apply (z2v_m_dvd_C m n Hm1 Hm2).
Qed.

(* 主定理（Set 面）：B(n) ∣ C(n) 的 mod 零判据形。 *)
Theorem z2v_lcm_dvd_C_t : forall n : nat, z2v_dvd_t (hl_lcm_upto n) (z2v_C n).
Proof.
  intro n. unfold z2v_dvd_t. apply z2v_id_of_eq.
  exact (z2v_idS_eq _ _ _
    (pr_dvd_mod0 (hl_lcm_upto n) (z2v_C n)
       (hl_le_t_to_le _ _ (h3_lcm_pos n)) (z2v_lcm_dvd_C n))).
Qed.

(* 数值锚：C(6) = 6!/(3!·2!·0!·…) = 720/12 = 60 = lcm(1..6) *)
Lemma z2v_C_6 : hl_id (z2v_C 6) 60.
Proof. apply z2v_id_of_eq. reflexivity. Qed.

(* 数值锚（Set 面可执行）：B(6) ∣ C(6) 之 mod 零判据直算 *)
Lemma z2v_dvd_t_smoke_6 : z2v_dvd_t (hl_lcm_upto 6) (z2v_C 6).
Proof. reflexivity. Qed.

(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。
   （Print Assumptions 日志不回显定理名，证据按本清单挂序对照。） *)
Print Assumptions z2v_pow_dvd.
Print Assumptions z2v_pow_pos.
Print Assumptions z2v_sylv_sum_0.
Print Assumptions z2v_leg_0.
Print Assumptions z2v_den_pos.
Print Assumptions z2v_v_1.
Print Assumptions z2v_pow_split.
Print Assumptions z2v_v_add.
Print Assumptions z2v_inc.
Print Assumptions z2v_leg_cnt.
Print Assumptions z2v_cnt_min.
Print Assumptions z2v_fact_ex.
Print Assumptions z2v_lsum_S_k.
Print Assumptions z2v_den_val.
Print Assumptions z2v_pointwise.
Print Assumptions z2v_layersum_bound.
Print Assumptions z2v_pc_ge.
Print Assumptions z2v_fact_split.
Print Assumptions z2v_den_dvd_gen.
Print Assumptions z2v_den_dvd.
Print Assumptions z2v_v_C_ge.
Print Assumptions z2v_ppow_dvd_C.
Print Assumptions z2v_dvd_pow_split.
Print Assumptions z2v_gcd_pow_prime.
Print Assumptions z2v_m_dvd_C.
Print Assumptions z2v_lcm_dvd_C.
Print Assumptions z2v_lcm_dvd_C_t.
Print Assumptions z2v_C_6.
Print Assumptions z2v_dvd_t_smoke_6.
