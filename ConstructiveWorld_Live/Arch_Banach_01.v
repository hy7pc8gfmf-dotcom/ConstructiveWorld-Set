(* ==========================================================================)
   Arch_Banach_01.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：bnhn_bnorm_plus、bnhn_bnorm_mult、bxcb_q_choose_out、bxcb_binom_eq_choose、bxcb_sentinel_bpa_4_2、bxcb_sentinel_qchoose_4_2、bxcb_sentinel_bridge_4_2、bxcb_sentinel_out_bpa_1_2、bxcb_sentinel_out_qchoose_1_2。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqBanachInstB.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import UpReqBanachAdd.
Require Import UpReqBanachProd2.
From Stdlib Require Import Setoid.
Require Import UpReqBanachExp.
Require Import UpReqBanachExpDef.
Require Import UpReqBanachProd.
Require Import UpReqBanachExpAdd.
Require Import UpReqBanachClassExt.
Require Import UpReqBanachLimUniq.
Require Import UpReqNormConv.
Require Import BanachNoHyp.
From Stdlib Require Import Setoid Lia.
Require Import UpReqBanachCauchyD.
Require Import UpReqBanachDouble.
Require Import UpReqBanachInvPre.

(* ================= §1 bnhn_bnorm_plus 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* 件一：bnorm_plus 字段位（次可加）——                               *)
(*   QleT' (bnorm (eplus a b)) (bnorm a + bnorm b)                  *)
(*   （类字段 bnorm_plus 在 E-载体 bxib_E 上的同位定理；双层 qnorm    *)
(*     退化 + Qabs_triangle 三段运输。）                             *)

Lemma bnhn_bnorm_plus : forall a b : bxib_E,
  QleT' (bxib_bnorm (bxib_eplus a b))
        (bxib_bnorm a + bxib_bnorm b)%Q.
Proof.
  intros a b. unfold bxib_bnorm.
  change (bxib_ev (bxib_eplus a b))
    with (bxib_qnorm (Qplus (bxib_ev a) (bxib_ev b))).
  (* 双层 qnorm 退化（Id 不动点，QleT' 目标内 Leibniz 改写合法位） *)
  rewrite (bxib_qnorm_fix_id (Qplus (bxib_ev a) (bxib_ev b))).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxib_ev a + bxib_ev b)%Q) _).
  - (* 左端换形：|qnorm (x+y)| ≤ |x+y|（Qeq 运输，非钉定位） *)
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    exact (Qabs_wd _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev a + bxib_ev b)%Q))).
  - apply (Qle_trans _ (Qabs (bxib_ev a)%Q + Qabs (bxib_ev b)%Q)%Q _).
    + (* 三角不等式（stdlib Qabs_triangle） *)
      apply Qabs_triangle.
    + (* 右端换形：|x|+|y| ≤ |qnorm x|+|qnorm y|
         （Qplus_comp Proper 项式：x x' Hx y y' Hy 交错参序） *)
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      exact (Qplus_comp (Qabs (bxib_ev a)%Q) (Qabs (bxib_qnorm (bxib_ev a)))
               (Qabs_wd _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev a)))))
               (Qabs (bxib_ev b)%Q) (Qabs (bxib_qnorm (bxib_ev b)))
               (Qabs_wd _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev b)))))).
Qed.

(* 件二：bnorm_mult 字段位（次可乘）——                               *)
(*   QleT' (bnorm (emult a b)) (bnorm a * bnorm b)                  *)
(*   （类字段 bnorm_mult 在 E-载体 bxib_E 上的同位定理；退化同款 +    *)
(*     Qabs_Qmult 等式换形（Qeq 强于 Qle 经 qeq_le 降取）。）         *)

Lemma bnhn_bnorm_mult : forall a b : bxib_E,
  QleT' (bxib_bnorm (bxib_emult a b))
        (bxib_bnorm a * bxib_bnorm b)%Q.
Proof.
  intros a b. unfold bxib_bnorm.
  change (bxib_ev (bxib_emult a b))
    with (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev b))).
  rewrite (bxib_qnorm_fix_id (Qmult (bxib_ev a) (bxib_ev b))).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxib_ev a * bxib_ev b)%Q) _).
  - (* 左端换形：|qnorm (x*y)| ≤ |x*y| *)
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    exact (Qabs_wd _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev a * bxib_ev b)%Q))).
  - apply (Qle_trans _ (Qabs (bxib_ev a)%Q * Qabs (bxib_ev b)%Q)%Q _).
    + (* |x*y| == |x|·|y|（stdlib Qabs_Qmult，Qeq 经 qeq_le 降取 Qle） *)
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
    + (* 右端换形：|x|·|y| ≤ |qnorm x|·|qnorm y|
         （Qmult_comp Proper 项式：x x' Hx y y' Hy 交错参序） *)
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      exact (Qmult_comp (Qabs (bxib_ev a)%Q) (Qabs (bxib_qnorm (bxib_ev a)))
               (Qabs_wd _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev a)))))
               (Qabs (bxib_ev b)%Q) (Qabs (bxib_qnorm (bxib_ev b)))
               (Qabs_wd _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev b)))))).
Qed.

(* 核验记录（对称申报，不落承认件面）：                             *)
(*   ① 本件即 INSTB 未消解项① 的闭合件：乘法群四面（bxem_ 系）+    *)
(*     bnorm_plus/bnorm_mult（本件 bnhn_）全数补齐，E-载体对冻结类     *)
(*     代数/范数字段位无剩余缺口（完备性字段照 INS 先例另列，        *)
(*     bnorm_coef 钉定语句面修订属上游改形——两处维持原未消解项状态）。 *)
(*   ② 伴随注：bxem_mult 与 bxib_emult 为 delta 同一定义              *)
(*     （bxem_mult a b := bxib_emult a b），本件语句面取构造子直形。   *)
(*   ③ 退化机同源性：本件双层退化 = bxem_mult_wd 同款                 *)
(*     （fix_id → qnorm_id_of_qeqT → fix_id 链的 QleT' 版），          *)
(*     序面用 Qabs_triangle/Qabs_Qmult 替 bxem 的 qeqT cong 位。       *)

Separate Extraction bnhn_bnorm_plus bnhn_bnorm_mult.

Print Assumptions bnhn_bnorm_plus.
Print Assumptions bnhn_bnorm_mult.
(* ================= §2 bxcb_q_choose_out 族 ================= *)
(* ================= §1 bxcb_q_choose_out 族 ================= *)
(* ================= §1 bxcb_q_choose_out 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* S1：出界语义对齐件——q_choose 的 Nat.sub 截断形显式化            *)
(* k>n 时 (n−k) 截断为 0，分母 q_fact 0 = 1，故 q_choose n k        *)
(*   == q_fact n / q_fact k == q_fact n * Qinv (q_fact k) ≠ 0，    *)
(* 与 bpa_binom_out（== 0）形成两侧出界语义分账。                  *)

Lemma bxcb_q_choose_out : forall n k : nat, (n < k)%nat ->
  q_choose n k == q_fact n * Qinv (q_fact k).
Proof.
  intros n k H.
  unfold q_choose.
  assert (E : (n - k)%nat = 0%nat) by lia.
  rewrite E.
  change (q_fact 0%nat) with (1%Q).
  unfold Qdiv.
  setoid_rewrite (Qmult_1_r (q_fact k)).
  reflexivity.
Qed.

(* S2：主桥 bxcb_binom_eq_choose（对 n 归纳 + k 分段）             *)
(*   forall n k, (k <= n)%nat -> bpa_binom n k == q_choose n k    *)
(* 分段：k=0（bpa_binom_0 ↔ q_choose_0）；k=S n' 对角              *)
(*   （bpa_binom_diag ↔ q_choose_n）；S k' < S n' 递归步——左 Pascal *)
(*   是 bpa_binom 定义形（change/reflexivity 级，BA 手法），右      *)
(*   Pascal 取 S07 q_choose_succ（复用不重写），末尾 (S k'−1)≡k'    *)
(*   为 iota 转换取 Qeq_refl。                                    *)

Lemma bxcb_binom_eq_choose : forall n k : nat, (k <= n)%nat ->
  bpa_binom n k == q_choose n k.
Proof.
  intros n. induction n as [| n' IH]; intros k Hk.
  - destruct k as [| k']; [ apply Qeq_refl | lia ].
  - destruct k as [| k'].
    + rewrite bpa_binom_0.
      apply Qeq_sym. apply qeqT_imp_qeq. apply q_choose_0.
    + destruct (Nat.eq_dec k' n') as [Heq | Hne].
      * rewrite Heq.
        setoid_rewrite (qeqT_imp_qeq _ _ (bpa_binom_diag (Datatypes.S n'))).
        apply Qeq_sym. apply qeqT_imp_qeq. apply q_choose_n.
      * change (bpa_binom (Datatypes.S n') (Datatypes.S k'))
          with (bpa_binom n' k' + bpa_binom n' (Datatypes.S k'))%Q.
        setoid_rewrite (IH k' ltac:(lia)).
        setoid_rewrite (IH (Datatypes.S k') ltac:(lia)).
        setoid_rewrite (qeqT_imp_qeq _ _ (q_choose_succ n' (Datatypes.S k') ltac:(lia) ltac:(lia))).
        (* 项序与 sub 双坑：q_choose_succ 尾项是 (S k'−1)（变量 k' 下
           Nat.sub 不约化，S-形免截断手法的对照坑），lia 桥 nat 层等式
           换回 k'；bpa 定义形 k' 项在前，Qplus 非定义性交换再换位——
           两步后两侧同形，Qeq_refl 闭合 *)
        assert (Esub : (Datatypes.S k' - 1)%nat = k'%nat) by lia.
        rewrite Esub.
        setoid_rewrite (Qplus_comm (q_choose n' k') (q_choose n' (Datatypes.S k'))).
        apply Qeq_refl.
Qed.

(* S3：锚数值面（reflexivity/vm_compute 级烟测）                 *)

Lemma bxcb_sentinel_bpa_4_2 : bpa_binom 4%nat 2%nat == (6 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma bxcb_sentinel_qchoose_4_2 : q_choose 4%nat 2%nat == (6 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* 桥上核验：主桥在 (4,2) 的直接实例 ==6 两侧一致 *)
Lemma bxcb_sentinel_bridge_4_2 : bpa_binom 4%nat 2%nat == q_choose 4%nat 2%nat.
Proof. apply bxcb_binom_eq_choose. lia. Qed.

(* 出界锚对（反例实形入账）：n=1,k=2 两侧分歧——bpa 侧 0，        *)
(* q_choose 侧 1!/2! = 1/2（Qinv (2#1)）；两件合账即证无假设全值域    *)
(* 桥不可立，语义对齐 (k<=n) 面为必需。                            *)
Lemma bxcb_sentinel_out_bpa_1_2 : bpa_binom 1%nat 2%nat == 0%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma bxcb_sentinel_out_qchoose_1_2 : q_choose 1%nat 2%nat == Qinv (2 # 1).
Proof. vm_compute. reflexivity. Qed.

(* S4：主件 bxcb_term_split——C(k,j)/k! == 1/(j!·(k−j)!)            *)
(* 下游 #29 exp_term_split 依存形。S07 已有同型原件                 *)
(*   q_choose_div_fact（B2Tv2 卡点名），复用不重写；另附 BA 侧      *)
(*   （bpa 系数）依存形 bxcb_term_split_binom。                    *)

Lemma bxcb_term_split : forall k j : nat,
  q_choose k j / q_fact k == Qinv (q_fact j) * Qinv (q_fact (k - j)%nat).
Proof.
  intros k j.
  apply qeqT_imp_qeq. apply (q_choose_div_fact k j).
Qed.

Lemma bxcb_term_split_binom : forall k j : nat, (j <= k)%nat ->
  bpa_binom k j / q_fact k == Qinv (q_fact j) * Qinv (q_fact (k - j)%nat).
Proof.
  intros k j Hj.
  setoid_rewrite (bxcb_binom_eq_choose k j Hj).
  apply qeqT_imp_qeq. apply (q_choose_div_fact k j).
Qed.

(* S5：薄桥——bpr2_q_choose（Prod2 阶乘比双层移植形）实例化           *)
(* bpr2_q_choose n k := q_fact n / (q_fact k * q_fact (Nat.sub n k)) *)
(* 与 q_choose n k 定义同构（delta 级），change 换形后主桥直用。    *)
(* 分工：S07 q_choose=冻结原件；bpr2_=Prod2 移植形；bpa_binom=      *)
(* Add Pascal 形。本桥把三形收拢到同一等价面。                     *)

Lemma bxcb_binom_eq_bpr2 : forall n k : nat, (k <= n)%nat ->
  bpa_binom n k == bpr2_q_choose n k.
Proof.
  intros n k H.
  change (bpr2_q_choose n k) with (q_choose n k).
  apply bxcb_binom_eq_choose. exact H.
Qed.

(*   「Closed under the global context」；Separate Extraction       *)
(*   UpReqBanachBinomBridge.ml Obj.magic 计数 =0；coqchk -o 全件     *)

(* ---- ToyR 追印：清单件假设面逐件打印，判读全闭 ---- *)
Print Assumptions bxcb_term_split.
(* ================= §2 bxdef_emul 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* S0：bxdef_emul——exp 元素乘法（主件左元连接位；普查全树无先名）    *)

Definition bxdef_emul (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x y : BA) : BA :=
  @bmult _ _ B x y.

(* S1：Q 层工具件（Prop 引擎内衬，零 lia）                          *)

Lemma bxae_1p1_neq_0 : ~ ((1 + 1)%Q == 0)%Q.
Proof. intros Hz. vm_compute in Hz. discriminate. Qed.

Lemma bxae_qlt_0_1 : Qlt 0 1%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma bxae_qlt_0_2 : Qlt 0 (1 + 1)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma bxae_qltT_0_1 : QltT 0 1%Q.
Proof. apply Qlt_to_QltT. exact bxae_qlt_0_1. Qed.

(* x ≤ x + y（0 ≤ y） *)
Lemma bxae_Qle_add_r : forall x y : Q, Qle 0 y -> Qle x (x + y)%Q.
Proof.
  intros x y Hy.
  apply (Qle_trans x (0 + x)%Q (x + y)%Q).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans (0 + x)%Q (y + x)%Q (x + y)%Q).
    + apply (Qplus_le_compat 0%Q y x x).
      * exact Hy.
      * apply Qle_refl.
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

(* x ≤ y + x（0 ≤ y） *)
Lemma bxae_Qle_add_l : forall x y : Q, Qle 0 y -> Qle x (y + x)%Q.
Proof.
  intros x y Hy.
  apply (Qle_trans x (0 + x)%Q (y + x)%Q).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - apply (Qplus_le_compat 0%Q y x x).
    + exact Hy.
    + apply Qle_refl.
Qed.

(* 1 ≤ 2 *)
Lemma bxae_Qle_1_2 : Qle 1%Q (1 + 1)%Q.
Proof. apply bxae_Qle_add_r. apply QleT'_to_Qle. apply Qle_0_1. Qed.

(* 右乘严格单调（Qmult_lt_r iff 面） *)
Lemma bxae_mult_lt_r : forall x y z : Q,
  Qlt x y -> Qlt 0 z -> Qlt (x * z) (y * z)%Q.
Proof.
  intros x y z Hxy Hz.
  exact (proj2 (Qmult_lt_r x y z Hz) Hxy).
Qed.

(* 域律消去：e·/(y·x)·x == e·/y *)
Lemma bxae_cancel_mul : forall e x y : Q,
  ~ (y == 0) -> ~ (y * x == 0) -> (e * / (y * x)) * x == e * / y.
Proof.
  intros e x y Hy Hyx.
  assert (Hx0 : ~ (x == 0)).
  { intros Hx. apply Hyx. rewrite Hx. ring. }
  field. split; assumption.
Qed.

(* 半和合并：e·/2 + e·/2 == e *)
Lemma bxae_half_add : forall e : Q, (e * / (1 + 1) + e * / (1 + 1))%Q == e%Q.
Proof. intros e. field. Qed.

(* 级数项非负：0 ≤ X^k/k! *)
Lemma bxae_term_nonneg : forall (X : Q) (k : nat),
  Qle 0 X -> Qle 0 (q_pow X k / q_fact k)%Q.
Proof.
  intros X k HX. unfold Qdiv.
  assert (Hinv : Qlt 0 (Qinv (q_fact k)))
    by (apply Qinv_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos).
  apply (Qle_trans 0%Q (0 * Qinv (q_fact k))%Q
                   (q_pow X k * Qinv (q_fact k))%Q).
  - rewrite Qmult_0_l. apply Qle_refl.
  - apply (proj2 (Qmult_le_r 0 (q_pow X k) (Qinv (q_fact k)) Hinv)).
    apply QleT'_to_Qle. apply (q_pow_nonneg X k).
    apply Qle_to_QleT'. exact HX.
Qed.

(* 尾和非负 *)
Lemma bxae_etab_nonneg : forall (X : Q) (m n : nat),
  Qle 0 X -> Qle 0 (exp_tail_abs m n X).
Proof.
  intros X m n HX. induction n as [| n' IH].
  - simpl. apply Qle_refl.
  - change (exp_tail_abs m (Datatypes.S n') X)
      with (exp_tail_abs m n' X
            + (if Nat.leb m n'
               then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
               else 0)%Q).
    destruct (Nat.leb m n').
    + apply (Qplus_le_compat 0%Q (exp_tail_abs m n' X) 0%Q
               (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))).
      * exact IH.
      * exact (bxae_term_nonneg X (Datatypes.S n') HX).
    + apply (Qle_trans 0%Q (exp_tail_abs m n' X) (exp_tail_abs m n' X + 0)%Q).
      * exact IH.
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. symmetry. apply Qplus_0_r.
Qed.


(* 尾和对起点反单调：m1 ≤ m2 ⟹ tail(m2..n) ≤ tail(m1..n) *)
Lemma bxae_etab_mono_start : forall (X : Q) (m1 m2 n : nat),
  Qle 0 X -> (m1 <= m2)%nat -> Qle (exp_tail_abs m2 n X) (exp_tail_abs m1 n X).
Proof.
  intros X m1 m2 n HX Hm. revert m1 m2 Hm.
  induction n as [| n' IH]; intros m1 m2 Hm.
  - simpl. apply Qle_refl.
  - change (exp_tail_abs m1 (Datatypes.S n') X)
      with (exp_tail_abs m1 n' X
            + (if Nat.leb m1 n'
               then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
               else 0)%Q).
    change (exp_tail_abs m2 (Datatypes.S n') X)
      with (exp_tail_abs m2 n' X
            + (if Nat.leb m2 n'
               then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
               else 0)%Q).
    destruct (Nat.leb m2 n') eqn:Em2.
    { assert (Hm2n' : (m2 <= n')%nat) by (apply Nat.leb_le; exact Em2).
      assert (Hm1n' : (m1 <= n')%nat) by lia.
      rewrite (proj2 (Nat.leb_le m1 n') Hm1n').
      apply (Qplus_le_compat (exp_tail_abs m2 n' X) (exp_tail_abs m1 n' X)
               (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))
               (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))).
      - exact (IH m1 m2 Hm).
      - apply (Qle_refl (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))). }
    { assert (E0 : (exp_tail_abs m2 n' X + 0)%Q == exp_tail_abs m2 n' X) by ring.
      apply (Qle_trans _ (exp_tail_abs m1 n' X)).
      - apply (Qle_trans _ (exp_tail_abs m2 n' X)).
        + exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ E0))).
        + exact (IH m1 m2 Hm).
      - apply bxae_Qle_add_r. destruct (Nat.leb m1 n').
        + exact (bxae_term_nonneg X (Datatypes.S n') HX).
        + apply Qle_refl. }
Qed.
(* 尾和分裂可加：tail(m1..n) == tail(m1..m2) + tail(m2..n) *)
Lemma bxae_etab_split : forall (X : Q) (m1 m2 n : nat),
  (m1 <= m2)%nat -> (m2 <= n)%nat ->
  exp_tail_abs m1 n X == (exp_tail_abs m1 m2 X + exp_tail_abs m2 n X)%Q.
Proof.
  intros X m1 m2 n Hm12 Hm2n. revert m1 m2 Hm12 Hm2n.
  induction n as [| n' IH]; intros m1 m2 Hm12 Hm2n.
  - assert (Hm20 : m2 = 0%nat) by lia. subst m2.
    assert (Hm10 : m1 = 0%nat) by lia. subst m1.
    simpl. ring.
  - destruct (Nat.leb m2 n') eqn:Em2.
    + assert (Hm2n' : (m2 <= n')%nat) by (apply Nat.leb_le; exact Em2).
      assert (Hm1n' : (m1 <= n')%nat) by lia.
      change (exp_tail_abs m1 (Datatypes.S n') X)
        with (exp_tail_abs m1 n' X
              + (if Nat.leb m1 n'
                 then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
                 else 0)%Q).
      change (exp_tail_abs m2 (Datatypes.S n') X)
        with (exp_tail_abs m2 n' X
              + (if Nat.leb m2 n'
                 then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
                 else 0)%Q).
      rewrite (proj2 (Nat.leb_le m1 n') Hm1n').
      rewrite (IH m1 m2 Hm12 Hm2n').
      rewrite Em2.
      set (T := (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))%Q).
      ring.
    + assert (Hlt : (n' < m2)%nat) by (apply Nat.leb_gt; exact Em2).
      assert (Hm2 : m2 = Datatypes.S n') by lia. subst m2.
      rewrite (qeqT_imp_qeq _ _ (exp_tail_abs_le_m (Datatypes.S n') (Datatypes.S n') X
                 (Nat.le_refl _))).
      ring.
Qed.

(* 尾和任意小：∃N，m ≥ N ⟹ tail(m..n) < e（任意 n） *)
Lemma bxae_etab_small : forall (X e : Q),
  Qle 0 X -> QltT 0 e ->
  sigT (fun N : nat => forall m n : nat, (N <= m)%nat ->
    Qlt (exp_tail_abs m n X) e).
Proof.
  intros X e HX Heps.
  destruct (q_arch_geom X) as [N0 HN0].
  assert (Harch : forall u : nat, (N0 <= u)%nat ->
            Qle (Qmult (1 + 1)%Q X) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply QleT'_to_Qle. apply (HN0 u). apply NatLe_lift. exact Hu. }
  assert (H0C : QleT' 0 ((q_pow X N0 / q_fact N0) * (1 + 1))%Q).
  { exact (q_pow_fact2_nonneg X N0 (Qle_to_QleT' 0 X HX)). }
  destruct (arch_decay ((q_pow X N0 / q_fact N0) * (1 + 1)%Q) e H0C Heps)
    as [t Hdec].
  exists (N0 + Datatypes.S t)%nat.
  intros m n Hm.
  destruct (Nat.leb m n) eqn:Emn.
  - apply Nat.leb_le in Emn.
    apply (Qle_lt_trans _ ((q_pow X m / q_fact m) * (1 + 1)%Q) e).
    + apply QleT'_to_Qle.
      exact (exp_tail_abs_geom2 X m n (Qle_to_QleT' 0 X HX)
               (fun t0 Ht => HN0 t0 (NatLe_lift _ _
                 (Nat.le_trans N0 m t0 ltac:(lia) (NatLe_drop _ _ Ht)))) Emn).
    + apply QltT_to_Qlt.
      apply (exp_tail_arch X N0 t m e (Qle_to_QleT' 0 X HX) HN0 Heps Hdec).
      lia.
  - apply Nat.leb_gt in Emn.
    assert (Hnm : (n <= m)%nat) by lia.
    exact (QltT_to_Qlt _ _
             (QeqT_Qlt_bool_cong 0 (exp_tail_abs m n X) e
                (qeqT_sym_hw _ _ (exp_tail_abs_le_m m n X Hnm)) Heps)).
Qed.

(* α 部分和 == 1 + 尾（α_k := X^k/k!） *)
Lemma bxae_ncvsum_alpha : forall (X : Q) (n : nat),
  ncv_qsum (fun i : nat => q_pow X i / q_fact i) (Datatypes.S n)
  == (1 + exp_tail_abs 0 n X)%Q.
Proof.
  intros X n. induction n as [| n' IH].
  - simpl. unfold Qdiv. vm_compute. reflexivity.
  - change (ncv_qsum (fun i : nat => q_pow X i / q_fact i)
              (Datatypes.S (Datatypes.S n')))
      with (ncv_qsum (fun i : nat => q_pow X i / q_fact i) (Datatypes.S n')
            + (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))%Q).
    rewrite IH.
    change (exp_tail_abs 0 (Datatypes.S n') X)
      with (exp_tail_abs 0 n' X
            + (if Nat.leb 0 n'
               then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
               else 0)%Q).
    assert (H0b : Nat.leb 0 n' = true) by (apply Nat.leb_le; lia).
    rewrite H0b.
    ring.
Qed.

(* qsum 分裂（前窗 + 位移窗） *)
Lemma bxae_ncvsum_split_eq : forall (f : nat -> Q) (n1 d : nat),
  ncv_qsum f (Datatypes.S (n1 + d))%nat
  == (ncv_qsum f (Datatypes.S n1)
      + ncv_qsum (fun i : nat => f ((Datatypes.S n1 + i)%nat)) d)%Q.
Proof.
  intros f n1 d. induction d as [| d' IH].
  - rewrite Nat.add_0_r.
    change (ncv_qsum (fun i : nat => f ((Datatypes.S n1 + i)%nat)) 0%nat)
      with 0%Q.
    ring.
  - replace ((n1 + Datatypes.S d')%nat) with (Datatypes.S (n1 + d')) by lia.
    change (ncv_qsum f (Datatypes.S (Datatypes.S (n1 + d'))))
      with (ncv_qsum f (Datatypes.S (n1 + d'))
            + f (Datatypes.S (n1 + d')))%Q.
    rewrite IH.
    change (ncv_qsum (fun i : nat => f ((Datatypes.S n1 + i)%nat))
              (Datatypes.S d'))
      with (ncv_qsum (fun i : nat => f ((Datatypes.S n1 + i)%nat)) d'
            + f (Datatypes.S (n1 + d'))%Q).
    ring.
Qed.

(* 窗内逐点控制（range 限定前提，前窗点态界用） *)
Lemma bxae_ncvsum_le_ranged : forall (f g : nat -> Q) (n : nat),
  (forall k : nat, (k < n)%nat -> QleT' (f k) (g k)) ->
  QleT' (ncv_qsum f n) (ncv_qsum g n).
Proof.
  intros f g n Hle. induction n as [| m IH].
  - change (ncv_qsum f 0%nat) with 0%Q. change (ncv_qsum g 0%nat) with 0%Q.
    apply qleT'_refl.
  - change (ncv_qsum f (Datatypes.S m)) with (ncv_qsum f m + f m)%Q.
    change (ncv_qsum g (Datatypes.S m)) with (ncv_qsum g m + g m)%Q.
    apply (qleT'_plus_compat _ _ _ _).
    + apply IH. intros k Hk. apply Hle. lia.
    + apply Hle. lia.
Qed.

(* 位移 α 窗和 == 尾和 *)
Lemma bxae_ncvsum_alpha_shift : forall (X : Q) (m d : nat),
  ncv_qsum (fun i : nat => q_pow X (Datatypes.S m + i) / q_fact (Datatypes.S m + i)) d
  == exp_tail_abs m (m + d)%nat X.
Proof.
  intros X m d. induction d as [| d' IH].
  - rewrite Nat.add_0_r.
    change (ncv_qsum (fun i : nat => q_pow X (Datatypes.S m + i) / q_fact (Datatypes.S m + i)) 0%nat)
      with 0%Q.
    apply Qeq_sym. apply qeqT_imp_qeq. apply (exp_tail_abs_le_m m m X (Nat.le_refl _)).
  - replace ((m + Datatypes.S d')%nat) with (Datatypes.S (m + d'))%nat by lia.
    change (ncv_qsum (fun i : nat => q_pow X (Datatypes.S m + i) / q_fact (Datatypes.S m + i))
              (Datatypes.S d'))
      with (ncv_qsum (fun i : nat => q_pow X (Datatypes.S m + i) / q_fact (Datatypes.S m + i)) d'
            + (q_pow X (Datatypes.S m + d') / q_fact (Datatypes.S m + d'))%Q).
    change (exp_tail_abs m (Datatypes.S (m + d'))%nat X)
      with (exp_tail_abs m (m + d')%nat X
            + (if Nat.leb m (m + d')%nat
               then q_pow X (Datatypes.S (m + d'))%nat / q_fact (Datatypes.S (m + d'))%nat
               else 0)%Q).
    assert (Hleb : Nat.leb m (m + d')%nat = true)
      by (apply Nat.leb_le; lia).
    rewrite Hleb.
    replace ((Datatypes.S m + d')%nat) with (Datatypes.S (m + d'))%nat by lia.
    rewrite IH. ring.
Qed.

(* 主 Q 件：块和任意小（Mertens 型分窗） *)
Lemma bxae_qblock_small : forall (X Y eps : Q),
  Qle 0 X -> Qle 0 Y -> QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qlt (ncv_qsum (fun i : nat =>
           q_pow X i / q_fact i * exp_tail_abs (Nat.sub n i) n Y)
         (Datatypes.S n)) eps).
Proof.
  intros X Y eps HX HY He.
  (* Y 尾 < 1 阈 ⟹ 全局 β 和界 Bb *)
  destruct (bxae_etab_small Y 1%Q HY bxae_qltT_0_1) as [Ny Hy].
  assert (Hb : forall n : nat,
           Qle (1 + exp_tail_abs 0 n Y)%Q ((1 + 1)%Q + exp_tail_abs 0 Ny Y)).
  { intro n. destruct (Nat.leb_spec n Ny) as [Hle | Hgt].
    - assert (Hsp : exp_tail_abs 0 Ny Y
                    == (exp_tail_abs 0 n Y + exp_tail_abs n Ny Y)%Q)
        by (apply bxae_etab_split with (m2 := n); lia).
      rewrite Hsp.
      apply (Qplus_le_compat 1%Q (1 + 1)%Q
               (exp_tail_abs 0 n Y)
               (exp_tail_abs 0 n Y + exp_tail_abs n Ny Y)).
      + exact bxae_Qle_1_2.
      + apply bxae_Qle_add_r.
        exact (bxae_etab_nonneg Y n Ny HY).
    - assert (Hsp : exp_tail_abs 0 n Y
                    == (exp_tail_abs 0 Ny Y + exp_tail_abs Ny n Y)%Q)
        by (apply bxae_etab_split with (m2 := Ny); lia).
      rewrite Hsp.
      assert (E1a : (1 + (exp_tail_abs 0 Ny Y + exp_tail_abs Ny n Y))%Q
                    == ((1 + exp_tail_abs Ny n Y) + exp_tail_abs 0 Ny Y)%Q) by ring.
      apply (Qle_trans _ ((1 + exp_tail_abs Ny n Y) + exp_tail_abs 0 Ny Y)%Q).
      + exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ E1a))).
      + apply (Qplus_le_compat (1 + exp_tail_abs Ny n Y)%Q (1 + 1)%Q
                 (exp_tail_abs 0 Ny Y) (exp_tail_abs 0 Ny Y)).
        * apply (Qplus_le_compat 1%Q 1%Q (exp_tail_abs Ny n Y) 1%Q).
          -- apply Qle_refl.
          -- apply Qlt_le_weak. exact (Hy Ny n (Nat.le_refl Ny)).
        * apply Qle_refl. }
  (* β 全局界 Bb 及其正性/抵消恒等（HP2 缩放链用） *)
  set (Bb := ((1 + 1)%Q + exp_tail_abs 0 Ny Y)%Q).
  assert (HBb : Qlt 0 Bb).
  { unfold Bb.
    setoid_rewrite (Qplus_comm (1 + 1)%Q (exp_tail_abs 0 Ny Y)).
    apply (Qle_lt_trans 0%Q (exp_tail_abs 0 Ny Y + 0)%Q
             (exp_tail_abs 0 Ny Y + (1 + 1)%Q)).
    - rewrite Qplus_0_r. exact (bxae_etab_nonneg Y 0 Ny HY).
    - apply (proj2 (Qplus_lt_r 0%Q (1 + 1)%Q (exp_tail_abs 0 Ny Y))).
      exact bxae_qlt_0_2. }
  assert (HtwoBb : QltT 0 ((1 + 1) * Bb)%Q)
    by (apply (ncv_qmult_lt0 (1 + 1) Bb); [exact bxae_qlt_0_2 | exact HBb]).
  assert (HcanBb : ((eps * / ((1 + 1) * Bb)) * Bb == eps * / (1 + 1))%Q).
  { apply bxae_cancel_mul.
    - apply bxae_1p1_neq_0.
    - intros Hz.
      exact (match q_neq_of_lt ((1 + 1) * Bb)%Q HtwoBb
               (qeq_imp_qeqT _ _ Hz) with end). }
  (* X 侧窗阈值（eps·/(2·Bb) 缩放额） *)
  assert (HltE : Qlt 0 (eps * / (1 + 1))%Q).
  { apply QltT_to_Qlt. apply (ncv_qmult_lt0 eps (Qinv (1 + 1))).
    - exact (QltT_to_Qlt 0 eps He).
    - apply Qinv_lt_0_compat. exact bxae_qlt_0_2. }
  destruct (bxae_etab_small X (eps * / ((1 + 1) * Bb))%Q HX
              (ncv_qmult_lt0 eps (Qinv ((1 + 1) * Bb))
                 (QltT_to_Qlt 0 eps He)
                 (Qinv_lt_0_compat _ (QltT_to_Qlt _ _ HtwoBb)))) as [Na Ha].
  set (SN := (1 + exp_tail_abs 0 Na X)%Q).
  assert (HposSN : Qlt 0 SN).
  { unfold SN. apply (Qlt_le_trans 0%Q 1%Q SN).
    - exact bxae_qlt_0_1.
    - apply bxae_Qle_add_r. exact (bxae_etab_nonneg X 0 Na HX). }
  assert (HtwoSN : QltT 0 ((1 + 1) * SN)%Q)
    by (apply (ncv_qmult_lt0 (1 + 1) SN); [exact bxae_qlt_0_2 | exact HposSN]).
  destruct (bxae_etab_small Y (eps * / ((1 + 1) * SN))%Q HY
              (ncv_qmult_lt0 eps (Qinv ((1 + 1) * SN))
                 (QltT_to_Qlt 0 eps He)
                 (Qinv_lt_0_compat _ (QltT_to_Qlt _ _ HtwoSN)))) as [Ny1 Hy1].
  exists (Na + Ny1)%nat. intros n Hn.
  assert (Hnd : n = (Na + (n - Na))%nat) by lia.
  set (d := (n - Na)%nat).
  assert (HcanSN : ((eps * / ((1 + 1) * SN)) * SN == eps * / (1 + 1))%Q).
  { apply bxae_cancel_mul.
    - apply bxae_1p1_neq_0.
    - intros Hz.
      exact (match q_neq_of_lt ((1 + 1) * SN)%Q HtwoSN
               (qeq_imp_qeqT _ _ Hz) with end). }
  (* 分窗 *)
  set (F := fun i : nat =>
              (q_pow X i / q_fact i) * exp_tail_abs (Nat.sub n i) n Y).
  replace (ncv_qsum F (Datatypes.S n)) with (ncv_qsum F (Datatypes.S (Na + d)))%nat
    by (f_equal; lia).
  rewrite bxae_ncvsum_split_eq.
  (* 前窗：i ≤ Na *)
  assert (HP1 : Qlt (ncv_qsum F (Datatypes.S Na)) (eps * / (1 + 1))%Q).
  { assert (Hlt1 : Qlt (exp_tail_abs (Nat.sub n Na) n Y * SN)
                       ((eps * / ((1 + 1) * SN)) * SN)%Q).
    { apply (bxae_mult_lt_r (exp_tail_abs (Nat.sub n Na) n Y)
        (eps * / ((1 + 1) * SN)) SN).
      - apply (Hy1 (Nat.sub n Na) n). lia.
      - exact HposSN. }
    rewrite HcanSN in Hlt1.
    assert (Hpt : forall i : nat, (i <= Na)%nat ->
              QleT' (F i) (exp_tail_abs (Nat.sub n Na) n Y
                           * (q_pow X i / q_fact i))%Q).
    { intros i Hi. unfold F. apply Qle_to_QleT'.
      apply (Qle_trans _
               (exp_tail_abs (Nat.sub n i) n Y
                * (q_pow X i / q_fact i))%Q).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      - apply (Qmult_le_compat_r _ _ (q_pow X i / q_fact i)).
        + apply (bxae_etab_mono_start Y (Nat.sub n Na) (Nat.sub n i) n HY).
          lia.
        + apply (bxae_term_nonneg X i HX). }
    assert (Hle1 : QleT' (ncv_qsum F (Datatypes.S Na))
                   (ncv_qsum (fun i : nat =>
                      exp_tail_abs (Nat.sub n Na) n Y * (q_pow X i / q_fact i))
                      (Datatypes.S Na)))
      by (apply bxae_ncvsum_le_ranged; intros k Hk; apply Hpt; lia).
    assert (Hsc : ncv_qsum (fun i : nat =>
                 exp_tail_abs (Nat.sub n Na) n Y * (q_pow X i / q_fact i))
                 (Datatypes.S Na)
                 == (exp_tail_abs (Nat.sub n Na) n Y
                     * ncv_qsum (fun i : nat => q_pow X i / q_fact i)
                       (Datatypes.S Na))%Q)
      by (apply qeqT_imp_qeq; apply ncv_qsum_scalar_l).
    apply (Qle_lt_trans _ (exp_tail_abs (Nat.sub n Na) n Y * SN)%Q).
    - apply (Qle_trans _ (ncv_qsum (fun i : nat =>
                 exp_tail_abs (Nat.sub n Na) n Y * (q_pow X i / q_fact i))
                 (Datatypes.S Na))%Q).
      + exact (QleT'_to_Qle _ _ Hle1).
      + apply (Qle_trans _ (exp_tail_abs (Nat.sub n Na) n Y
                 * ncv_qsum (fun i : nat => q_pow X i / q_fact i)
                   (Datatypes.S Na))%Q).
        * exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Hsc))).
        * rewrite (Qmult_comm (exp_tail_abs (Nat.sub n Na) n Y)
                    (ncv_qsum (fun i : nat => q_pow X i / q_fact i)
                       (Datatypes.S Na))).
          rewrite (Qmult_comm (exp_tail_abs (Nat.sub n Na) n Y) SN).
          apply (Qmult_le_compat_r _ _ (exp_tail_abs (Nat.sub n Na) n Y)).
          -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold SN. exact (bxae_ncvsum_alpha X Na).
          -- exact (bxae_etab_nonneg Y (Nat.sub n Na) n HY).
    - exact Hlt1. }
  (* 后窗：i > Na（位移窗） *)
  assert (HP2 : Qlt (ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)
                    (eps * / (1 + 1))%Q).
  { assert (Hpt : forall i : nat,
              QleT' (F ((Datatypes.S Na + i)%nat))
                (((1 + 1)%Q + exp_tail_abs 0 Ny Y)
                 * (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat)))%Q).
    { intros i. unfold F. apply Qle_to_QleT'.
      apply (Qle_trans _
               ((q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))
                * ((1 + 1)%Q + exp_tail_abs 0 Ny Y))%Q).
      - rewrite (Qmult_comm (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))
                  (exp_tail_abs (Nat.sub n ((Datatypes.S Na + i)%nat)) n Y)).
        rewrite (Qmult_comm (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))
                  ((1 + 1)%Q + exp_tail_abs 0 Ny Y)).
        apply (Qmult_le_compat_r _ _
                 (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))).
        + (* tail(n−j, n) ≤ 1 + tail(0, n) ≤ Bb *)
          apply (Qle_trans _ (1 + exp_tail_abs 0 n Y)%Q).
          * assert (Hsp2 : exp_tail_abs 0 n Y
                           == (exp_tail_abs 0 (Nat.sub n ((Datatypes.S Na + i)%nat)) Y
                               + exp_tail_abs (Nat.sub n ((Datatypes.S Na + i)%nat)) n Y)%Q)
              by (apply bxae_etab_split with (m2 := Nat.sub n ((Datatypes.S Na + i)%nat)); lia).
            assert (Ht1 : exp_tail_abs (Nat.sub n ((Datatypes.S Na + i)%nat)) n Y
                          <= exp_tail_abs 0 n Y).
            { apply (Qle_trans _
                       (exp_tail_abs 0 (Nat.sub n ((Datatypes.S Na + i)%nat)) Y
                        + exp_tail_abs (Nat.sub n ((Datatypes.S Na + i)%nat)) n Y)%Q).
              - apply bxae_Qle_add_l.
                exact (bxae_etab_nonneg Y 0%nat (Nat.sub n ((Datatypes.S Na + i)%nat)) HY).
              - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. symmetry. exact Hsp2. }
            apply (Qle_trans _ (exp_tail_abs 0 n Y)).
            -- exact Ht1.
            -- apply bxae_Qle_add_l. apply QleT'_to_Qle. apply Qle_0_1.
          * apply Hb.
        + apply (bxae_term_nonneg X ((Datatypes.S Na + i)%nat) HX).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm. }
    assert (Hle2 : QleT' (ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)
                   (ncv_qsum (fun i : nat =>
                      ((1 + 1)%Q + exp_tail_abs 0 Ny Y)
                      * (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))) d))
      by (apply ncv_qsum_le; exact Hpt).
    assert (Hsc : ncv_qsum (fun i : nat =>
                 ((1 + 1)%Q + exp_tail_abs 0 Ny Y)
                 * (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))) d
                 == (((1 + 1)%Q + exp_tail_abs 0 Ny Y)
                     * ncv_qsum (fun i : nat =>
                          q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat)) d)%Q)
      by (apply qeqT_imp_qeq; apply ncv_qsum_scalar_l).
    pose proof Hle2 as Hle3.
    apply QleT'_to_Qle in Hle3.
    rewrite Hsc in Hle3.
    rewrite (bxae_ncvsum_alpha_shift X Na d) in Hle3.
    replace (Na + d)%nat with n in Hle3 by lia.
    assert (Hlt2 : Qlt (exp_tail_abs Na n X * Bb)
                       ((eps * / ((1 + 1) * Bb)) * Bb)%Q).
    { apply (bxae_mult_lt_r (exp_tail_abs Na n X)
              (eps * / ((1 + 1) * Bb)) Bb).
      - exact (Ha Na n (Nat.le_refl Na)).
      - exact HBb. }
    setoid_rewrite HcanBb in Hlt2.
    setoid_rewrite (Qmult_comm (exp_tail_abs Na n X) Bb) in Hlt2.
    apply (Qle_lt_trans _ (Bb * exp_tail_abs Na n X)%Q).
    - exact Hle3.
    - exact Hlt2. }
  (* 合流：P1 < e/2，P2 < e/2 ⟹ P1 + P2 < e *)
  apply (Qle_lt_trans _
           (eps * / (1 + 1) + ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)%Q).
  - apply (Qplus_le_compat _ _ _ _).
    + apply Qlt_le_weak. exact HP1.
    + apply Qle_refl.
  - apply (Qlt_le_trans
             (eps * / (1 + 1)
              + ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)
             (eps * / (1 + 1) + eps * / (1 + 1))%Q eps).
    + apply (proj2 (Qplus_lt_r (ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)
                       (eps * / (1 + 1)) (eps * / (1 + 1)))).
      exact HP2.
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply bxae_half_add.
Qed.

(* S2：Banach 层（行形三角 + 块分解 + 范数界 + 极限移位 + 主件）      *)

(* QleT' 乘法双单调（0 ≤ x2 与 0 ≤ y1 显式前提，免 stdlib compat_l 缺位） *)
Lemma bxae_qleT'_mul_le : forall x1 y1 x2 y2 : Q,
  Qle x1 y1 -> Qle x2 y2 -> Qle 0 x2 -> Qle 0 y1 -> QleT' (x1 * x2) (y1 * y2)%Q.
Proof.
  intros x1 y1 x2 y2 H1 H2 H3a H3b.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (y1 * x2)%Q).
  - apply (Qmult_le_compat_r x1 y1 x2); assumption.
  - rewrite (Qmult_comm y1 x2). rewrite (Qmult_comm y1 y2).
    apply (Qmult_le_compat_r x2 y2 y1); assumption.
Qed.

(* bsum 与 ncv_sum 同形桥 *)
Lemma bxae_bsum_ncvsum : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (x : nat -> BA) (n : nat),
  bae (bsum _ _ B n x) (ncv_sum _ _ B x n).
Proof.
  intros BA bae B x n. induction n as [| m IH].
  - apply (@bae_refl _ _ B).
  - change (bsum _ _ B (Datatypes.S m) x)
      with (@bplus _ _ B (bsum _ _ B m x) (x m)).
    change (ncv_sum _ _ B x (Datatypes.S m))
      with (@bplus _ _ B (ncv_sum _ _ B x m) (x m)).
    apply (@bplus_wd _ _ B).
    + exact IH.
    + apply (@bae_refl _ _ B).
Qed.

(* 零次幂项即单位：bpow x 0·(1/0!) == bone *)
Lemma bxae_B0_one : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x : BA),
  bae (@bmult _ _ B (bpow _ _ B x 0%nat) (@bcoef _ _ B (/ q_fact 0%nat))) (@bone _ _ B).
Proof.
  intros BA bae B x.
  assert (Hq0 : (/ q_fact 0%nat)%Q = 1%Q) by reflexivity.
  rewrite Hq0.
  change (bpow _ _ B x 0%nat) with (@bone _ _ B).
  eapply bae_trans with (b := @bcoef _ _ B 1%Q).
  - exact (@bmult_one_l _ _ B (@bcoef _ _ B 1%Q)).
  - exact (@bcoef_one _ _ B).
Qed.

(* 项重排：coef c·(a^j·b^i) == (a^j·coef x)·(b^i·coef y)（c == x·y） *)
Lemma bxae_term_reassoc : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
                                 (a b : BA) (j i : nat) (x y c : Q),
  c == (x * y)%Q ->
  bae (@bmult _ _ B (@bcoef _ _ B c) (@bmult _ _ B (bpow _ _ B a j) (bpow _ _ B b i)))
       (@bmult _ _ B (@bmult _ _ B (bpow _ _ B a j) (@bcoef _ _ B x))
                   (@bmult _ _ B (bpow _ _ B b i) (@bcoef _ _ B y))).
Proof.
  intros BA bae B a b j i x y c Hc.
  assert (Hswap : bae (@bmult _ _ B (@bmult _ _ B (bpow _ _ B b i) (@bcoef _ _ B x))
                                    (@bcoef _ _ B y))
                         (@bmult _ _ B (@bcoef _ _ B x)
                                   (@bmult _ _ B (bpow _ _ B b i) (@bcoef _ _ B y)))).
  { eapply bae_trans with
      (b := @bmult _ _ B (@bmult _ _ B (@bcoef _ _ B x) (bpow _ _ B b i)) (@bcoef _ _ B y)).
    - apply (@bmult_wd _ _ B).
      + exact (@bcoef_comm _ _ B x (bpow _ _ B b i)).
      + apply (@bae_refl _ _ B).
    - apply (@bae_sym _ _ B).
      exact (@bmult_assoc _ _ B (@bcoef _ _ B x) (bpow _ _ B b i) (@bcoef _ _ B y)). }
  eapply bae_trans with
    (b := @bmult _ _ B (@bmult _ _ B (bpow _ _ B a j) (bpow _ _ B b i))
                    (@bcoef _ _ B (x * y)%Q)).
  - eapply bae_trans with
      (b := @bmult _ _ B (@bmult _ _ B (bpow _ _ B a j) (bpow _ _ B b i)) (@bcoef _ _ B c)).
    + apply (@bae_sym _ _ B).
      exact (@bcoef_comm _ _ B c (@bmult _ _ B (bpow _ _ B a j) (bpow _ _ B b i))).
    + apply (@bmult_wd _ _ B).
      * apply (@bae_refl _ _ B).
        * apply (@bcoef_wd _ _ B). apply qeq_imp_qeqT. exact Hc.
  - eapply bae_trans with
      (b := @bmult _ _ B (bpow _ _ B a j)
                      (@bmult _ _ B (bpow _ _ B b i) (@bcoef _ _ B (x * y)%Q))).
    + apply (@bae_sym _ _ B).
      exact (@bmult_assoc _ _ B (bpow _ _ B a j) (bpow _ _ B b i)
                             (@bcoef _ _ B (x * y)%Q)).
    + eapply bae_trans with
        (b := @bmult _ _ B (bpow _ _ B a j)
                        (@bmult _ _ B (bpow _ _ B b i)
                                 (@bmult _ _ B (@bcoef _ _ B x) (@bcoef _ _ B y)))).
      * apply (@bmult_wd _ _ B).
        -- apply (@bae_refl _ _ B).
        -- apply (@bmult_wd _ _ B).
           ++ apply (@bae_refl _ _ B).
           ++ exact (@bcoef_mult _ _ B x y).
      * eapply bae_trans with
          (b := @bmult _ _ B (bpow _ _ B a j)
                          (@bmult _ _ B (@bmult _ _ B (bpow _ _ B b i) (@bcoef _ _ B x))
                                    (@bcoef _ _ B y))).
        -- apply (@bmult_wd _ _ B).
           ++ apply (@bae_refl _ _ B).
           ++ exact (@bmult_assoc _ _ B (bpow _ _ B b i) (@bcoef _ _ B x)
                                  (@bcoef _ _ B y)).
        -- eapply bae_trans with
             (b := @bmult _ _ B (bpow _ _ B a j)
                             (@bmult _ _ B (@bcoef _ _ B x)
                                       (@bmult _ _ B (bpow _ _ B b i)
                                                  (@bcoef _ _ B y)))).
           ++ apply (@bmult_wd _ _ B).
              ** apply (@bae_refl _ _ B).
              ** exact Hswap.
           ++ exact (@bmult_assoc _ _ B (bpow _ _ B a j) (@bcoef _ _ B x)
                                  (@bmult _ _ B (bpow _ _ B b i) (@bcoef _ _ B y))).
Qed.
(* ①③ 对接：(a+b)^k/k! == Σ_{j≤k} A j·B (k−j)（行形，CBR 桥供系数） *)
Lemma bxae_binom_row : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall k : nat,
    bae (@bmult _ _ B (bpow _ _ B (@bplus _ _ B a b) k) (@bcoef _ _ B (/ q_fact k)))
           (bsum _ _ B (Datatypes.S k)
              (fun j : nat =>
                 @bmult _ _ B (@bmult _ _ B (bpow _ _ B a j) (@bcoef _ _ B (/ q_fact j)))
                          (@bmult _ _ B (bpow _ _ B b (Nat.sub k j))
                                   (@bcoef _ _ B (/ q_fact (Nat.sub k j)))))).
Proof.
  intros BA bae B a b hab k.
  eapply bae_trans.
  - exact (bnh_esp_term_binom _ _ B a b hab k).
  - apply (bsum_ext _ _ B (Datatypes.S k)
             (fun j : nat =>
                @bmult _ _ B (@bcoef _ _ B (bpa_binom k j * / q_fact k)%Q)
                         (@bmult _ _ B (bpow _ _ B a j)
                                  (bpow _ _ B b (Nat.sub k j))))
             (fun j : nat =>
                @bmult _ _ B (@bmult _ _ B (bpow _ _ B a j) (@bcoef _ _ B (/ q_fact j)))
                         (@bmult _ _ B (bpow _ _ B b (Nat.sub k j))
                                  (@bcoef _ _ B (/ q_fact (Nat.sub k j)))))).
    intros j Hj.
    apply (bxae_term_reassoc _ _ B a b j (Nat.sub k j)
               (/ q_fact j) (/ q_fact (Nat.sub k j))
               (bpa_binom k j * / q_fact k)%Q).
    + exact (bxcb_term_split_binom k j ltac:(lia)).
Qed.

(* ② 方块行形：esp a n·esp b n == Σ_{i≤n} A i·esp b n *)
Lemma bxae_prod_row : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA) (n : nat),
  bae (@bmult _ _ B (exp_series_partial _ _ B a n) (exp_series_partial _ _ B b n))
         (bsum _ _ B (Datatypes.S n)
            (fun i : nat =>
               @bmult _ _ B (@bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))
                        (exp_series_partial _ _ B b n))).
Proof.
  intros BA bae B a b n.
  eapply bae_trans.
  - apply (@bmult_wd _ _ B).
    + exact (esp_as_bsum _ _ B a n).
    + apply (@bae_refl _ _ B).
  - apply (@bae_sym _ _ B).
    exact (bpa_bsum_mult_r _ _ B (Datatypes.S n) (exp_series_partial _ _ B b n)
             (fun i : nat =>
                @bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))).
Qed.

(* ④ 行形三角（自建归纳，免 bd2 转置）：
   esp (a+b) n == Σ_{i≤n} A i·esp b (n−i) *)
Lemma bxae_tri_row : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall n : nat,
    bae (exp_series_partial _ _ B (@bplus _ _ B a b) n)
           (bsum _ _ B (Datatypes.S n)
              (fun i : nat =>
                 @bmult _ _ B (@bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))
                          (exp_series_partial _ _ B b (Nat.sub n i)))).
Proof.
  intros BA bae B a b hab n.
  induction n as [| n' IH].
  - (* 基例：bone == bzero + A 0·esp b 0 *)
    assert (Hq0 : (/ q_fact 0%nat)%Q = 1%Q) by reflexivity.
    change (exp_series_partial _ _ B (@bplus _ _ B a b) 0%nat) with (@bone _ _ B).
    change (bsum _ _ B (Datatypes.S 0%nat)
              (fun i : nat =>
                 @bmult _ _ B (@bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))
                          (exp_series_partial _ _ B b (Nat.sub 0 i))))
      with (@bplus _ _ B (@bzero _ _ B)
              (@bmult _ _ B (@bmult _ _ B (bpow _ _ B a 0%nat) (@bcoef _ _ B (/ q_fact 0%nat)))
                       (exp_series_partial _ _ B b (Nat.sub 0 0)))).
    rewrite Hq0.
    change (bpow _ _ B a 0%nat) with (@bone _ _ B).
    change (exp_series_partial _ _ B b (Nat.sub 0 0)) with (@bone _ _ B).
    eapply bae_trans with
      (b := @bmult _ _ B (@bmult _ _ B (@bone _ _ B) (@bcoef _ _ B 1%Q)) (@bone _ _ B)).
    + eapply bae_trans with (b := @bmult _ _ B (@bcoef _ _ B 1%Q) (@bone _ _ B)).
      * eapply bae_trans with (b := @bcoef _ _ B 1%Q).
        -- apply (@bae_sym _ _ B). exact (@bcoef_one _ _ B).
        -- apply (@bae_sym _ _ B). exact (@bmult_one_r _ _ B (@bcoef _ _ B 1%Q)).
      * apply (@bmult_wd _ _ B).
        -- apply (@bae_sym _ _ B). exact (@bmult_one_l _ _ B (@bcoef _ _ B 1%Q)).
        -- apply (@bae_refl _ _ B).
    + apply (@bae_sym _ _ B).
      exact (@bplus_zero_l _ _ B (@bmult _ _ B (@bmult _ _ B (@bone _ _ B) (@bcoef _ _ B 1%Q)) (@bone _ _ B))).
  - (* 归纳步：set 命名短项结构 *)
    assert (Esub : Nat.sub (Datatypes.S n') (Datatypes.S n') = 0%nat) by lia.
    set (Ai := fun i : nat => @bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i))).
    set (Bj := fun j : nat => @bmult _ _ B (bpow _ _ B b j) (@bcoef _ _ B (/ q_fact j))).
    set (Hrow := fun i : nat =>
                   @bmult _ _ B (Ai i) (exp_series_partial _ _ B b (Nat.sub n' i))).
    set (Fj := fun j : nat =>
                 @bmult _ _ B (Ai j) (Bj (Nat.sub (Datatypes.S n') j))).
    set (Tl := @bmult _ _ B (Ai (Datatypes.S n')) (Bj 0%nat)).
    set (R := fun i : nat =>
                @bmult _ _ B (Ai i)
                    (exp_series_partial _ _ B b (Nat.sub (Datatypes.S n') i))).
    (* LHS 前置 change：esp(S n') == esp n' + C，RHS bsum 剥末项 *)
    change (exp_series_partial _ _ B (@bplus _ _ B a b) (Datatypes.S n'))
      with (@bplus _ _ B (exp_series_partial _ _ B (@bplus _ _ B a b) n')
                (@bmult _ _ B (bpow _ _ B (@bplus _ _ B a b) (Datatypes.S n'))
                          (@bcoef _ _ B (/ q_fact (Datatypes.S n'))))).
    change (bsum _ _ B (Datatypes.S (Datatypes.S n')) R)
      with (@bplus _ _ B (bsum _ _ B (Datatypes.S n') R) (R (Datatypes.S n'))).
    (* R (S n') ≡ Tl（B0↔esp b 0） *)
    assert (HRtl : bae Tl (R (Datatypes.S n'))).
    { unfold Tl, R, Ai, Bj. rewrite Esub.
      change (exp_series_partial _ _ B b 0%nat) with (@bone _ _ B).
      apply (@bmult_wd _ _ B); [apply (@bae_refl _ _ B) | exact (bxae_B0_one _ _ B b)]. }
    (* C 行形 *)
    assert (HC : bae (@bmult _ _ B (bpow _ _ B (@bplus _ _ B a b) (Datatypes.S n'))
                                  (@bcoef _ _ B (/ q_fact (Datatypes.S n'))))
                         (bsum _ _ B (Datatypes.S (Datatypes.S n')) Fj)).
    { unfold Fj. exact (bxae_binom_row _ _ B a b hab (Datatypes.S n')). }
    (* 剥末项：bsum (S (S n')) Fj == bsum (S n') Fj + Tl *)
    assert (Hpeel : bae (bsum _ _ B (Datatypes.S (Datatypes.S n')) Fj)
                           (@bplus _ _ B (bsum _ _ B (Datatypes.S n') Fj) Tl)).
    { unfold Fj, Tl, Ai, Bj.
      change (bsum _ _ B (Datatypes.S (Datatypes.S n'))
                (fun j : nat =>
                   @bmult _ _ B (@bmult _ _ B (bpow _ _ B a j) (@bcoef _ _ B (/ q_fact j)))
                            (@bmult _ _ B (bpow _ _ B b (Nat.sub (Datatypes.S n') j))
                                     (@bcoef _ _ B (/ q_fact (Nat.sub (Datatypes.S n') j))))))
        with (@bplus _ _ B (bsum _ _ B (Datatypes.S n')
                          (fun j : nat =>
                             @bmult _ _ B (@bmult _ _ B (bpow _ _ B a j)
                                                  (@bcoef _ _ B (/ q_fact j)))
                                      (@bmult _ _ B (bpow _ _ B b
                                                   (Nat.sub (Datatypes.S n') j))
                                               (@bcoef _ _ B
                                                  (/ q_fact (Nat.sub (Datatypes.S n') j))))))
                  (@bmult _ _ B (@bmult _ _ B (bpow _ _ B a (Datatypes.S n'))
                                      (@bcoef _ _ B (/ q_fact (Datatypes.S n'))))
                           (@bmult _ _ B (bpow _ _ B b
                                        (Nat.sub (Datatypes.S n') (Datatypes.S n')))
                                    (@bcoef _ _ B
                                       (/ q_fact (Nat.sub (Datatypes.S n') (Datatypes.S n'))))))).
      rewrite Esub. apply (@bae_refl _ _ B). }
    (* 逐项合并：Hrow i + Fj i == R i（i < S n'） *)
    assert (HR : forall i : nat, (i < Datatypes.S n')%nat ->
                   bae (@bplus _ _ B (Hrow i) (Fj i)) (R i)).
    { intros i Hi. unfold Hrow, Fj, R, Ai, Bj.
      assert (E2 : Nat.sub (Datatypes.S n') i
                   = Datatypes.S (Nat.sub n' i)) by lia.
      rewrite E2.
      change (exp_series_partial _ _ B b (Datatypes.S (Nat.sub n' i)))
        with (@bplus _ _ B (exp_series_partial _ _ B b (Nat.sub n' i))
                  (@bmult _ _ B (bpow _ _ B b (Datatypes.S (Nat.sub n' i)))
                           (@bcoef _ _ B (/ q_fact (Datatypes.S (Nat.sub n' i)))))).
      apply (@bae_sym _ _ B). apply (@bdistrib_l _ _ B). }
    (* 总链（EXPADD5 重排）：esp+C → esp+ΣFj → esp+(ΣFj'+Tl) → 重结合
       → (ΣHrow+ΣFj)+Tl → +R(S n') → Σ(Hrow+Fj)+R(S n') → 目标 *)
    eapply bae_trans with
      (b := @bplus _ _ B (exp_series_partial _ _ B (@bplus _ _ B a b) n')
                      (bsum _ _ B (Datatypes.S (Datatypes.S n')) Fj)).
    { apply (@bplus_wd_r _ _ B). exact HC. }
    eapply bae_trans with
      (b := @bplus _ _ B (exp_series_partial _ _ B (@bplus _ _ B a b) n')
                      (@bplus _ _ B (bsum _ _ B (Datatypes.S n') Fj) Tl)).
    { apply (@bplus_wd_r _ _ B). exact Hpeel. }
    eapply bae_trans with
      (b := @bplus _ _ B (@bplus _ _ B (exp_series_partial _ _ B (@bplus _ _ B a b) n')
                            (bsum _ _ B (Datatypes.S n') Fj)) Tl).
    { apply (@bplus_assoc _ _ B). }
    eapply bae_trans with
      (b := @bplus _ _ B (@bplus _ _ B (bsum _ _ B (Datatypes.S n') Hrow)
                            (bsum _ _ B (Datatypes.S n') Fj)) Tl).
    { apply (@bplus_wd_l _ _ B). apply (@bplus_wd_l _ _ B). exact IH. }
    eapply bae_trans with
      (b := @bplus _ _ B (@bplus _ _ B (bsum _ _ B (Datatypes.S n') Hrow)
                            (bsum _ _ B (Datatypes.S n') Fj)) (R (Datatypes.S n'))).
    { apply (@bplus_wd_r _ _ B). exact HRtl. }
    apply (@bplus_wd_l _ _ B).
    eapply bae_trans with
      (b := bsum _ _ B (Datatypes.S n') (fun i : nat => @bplus _ _ B (Hrow i) (Fj i))).
    { apply (@bae_sym _ _ B). exact (bsum_plus _ _ B (Datatypes.S n') Hrow Fj). }
    { apply (bsum_ext _ _ B (Datatypes.S n')
                (fun i : nat => @bplus _ _ B (Hrow i) (Fj i)) R).
      intros i Hi. exact (HR i Hi). }
Qed.
(* 差=块和：esp a n·esp b n − esp (a+b) n == Σ_{i≤n} A i·(esp b n − esp b (n−i)) *)
Lemma bxae_diff_block : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall (n : nat),
  bae (@bplus _ _ B (@bmult _ _ B (exp_series_partial _ _ B a n)
                             (exp_series_partial _ _ B b n))
                   (@bopp _ _ B (exp_series_partial _ _ B (@bplus _ _ B a b) n)))
         (bsum _ _ B (Datatypes.S n)
            (fun i : nat =>
               @bmult _ _ B (@bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))
                        (@bplus _ _ B (exp_series_partial _ _ B b n)
                                 (@bopp _ _ B (exp_series_partial _ _ B b
                                              (Nat.sub n i)))))).
Proof.
  intros BA bae B a b hab n.
  set (Ai := fun i : nat => @bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i))).
  set (Hrow := fun i : nat =>
                 @bmult _ _ B (Ai i) (exp_series_partial _ _ B b (Nat.sub n i))).
  set (Kf := fun i : nat =>
               @bmult _ _ B (Ai i)
                        (@bplus _ _ B (exp_series_partial _ _ B b n)
                                 (@bopp _ _ B (exp_series_partial _ _ B b
                                            (Nat.sub n i))))).
  (* 逐项：A i·esp b n == Hrow i + Kf i *)
  assert (Hpt : forall i : nat,
             bae (@bmult _ _ B (Ai i) (exp_series_partial _ _ B b n))
                    (@bplus _ _ B (Hrow i) (Kf i))).
  { intros i. unfold Hrow, Kf.
    (* A·u == A·(v+(u+−v)) == A·v + A·(u+−v)（分配反演+群律消去） *)
    eapply bae_trans with
      (b := @bmult _ _ B (Ai i)
                      (@bplus _ _ B (exp_series_partial _ _ B b (Nat.sub n i))
                               (@bplus _ _ B (exp_series_partial _ _ B b n)
                                        (@bopp _ _ B (exp_series_partial _ _ B b
                                                   (Nat.sub n i)))))).
    - apply (@bmult_wd _ _ B).
      + apply (@bae_refl _ _ B).
      + apply (@bae_sym _ _ B).
        eapply bae_trans with
          (b := @bplus _ _ B (@bplus _ _ B (exp_series_partial _ _ B b (Nat.sub n i))
                                  (exp_series_partial _ _ B b n))
                         (@bopp _ _ B (exp_series_partial _ _ B b
                                    (Nat.sub n i)))).
        * apply (@bplus_assoc _ _ B).
        * eapply bae_trans with
            (b := @bplus _ _ B (@bplus _ _ B (exp_series_partial _ _ B b n)
                                    (exp_series_partial _ _ B b (Nat.sub n i)))
                           (@bopp _ _ B (exp_series_partial _ _ B b
                                      (Nat.sub n i)))).
          -- apply (@bplus_wd_l _ _ B). apply (@bplus_comm _ _ B).
          -- eapply bae_trans with
               (b := @bplus _ _ B (exp_series_partial _ _ B b n)
                              (@bplus _ _ B (exp_series_partial _ _ B b (Nat.sub n i))
                                       (@bopp _ _ B (exp_series_partial _ _ B b
                                                  (Nat.sub n i))))).
             ++ apply (@bae_sym _ _ B). apply (@bplus_assoc _ _ B).
             ++ eapply bae_trans with
                  (b := @bplus _ _ B (exp_series_partial _ _ B b n) (@bzero _ _ B)).
                ** apply (@bplus_wd_r _ _ B).
                   exact (@bplus_opp _ _ B (exp_series_partial _ _ B b (Nat.sub n i))).
                ** apply (@bplus_zero _ _ B (exp_series_partial _ _ B b n)).
    - apply (@bdistrib_l _ _ B). }
  assert (H1 : bae (@bplus _ _ B (@bmult _ _ B (exp_series_partial _ _ B a n)
                                         (exp_series_partial _ _ B b n))
                              (@bopp _ _ B (exp_series_partial _ _ B
                                          (@bplus _ _ B a b) n)))
                     (@bplus _ _ B (bsum _ _ B (Datatypes.S n)
                                  (fun i : nat =>
                                     @bmult _ _ B (Ai i)
                                         (exp_series_partial _ _ B b n)))
                              (@bopp _ _ B (bsum _ _ B (Datatypes.S n) Hrow)))).
  { apply (@bplus_wd _ _ B).
    - exact (bxae_prod_row _ _ B a b n).
    - apply (@bopp_wd _ _ B).
      destruct n as [| n'].
      + exact (bxae_tri_row _ _ B a b hab 0%nat).
      + exact (bxae_tri_row _ _ B a b hab (Datatypes.S n')). }
  assert (H2 : bae (bsum _ _ B (Datatypes.S n)
                         (fun i : nat =>
                            @bmult _ _ B (Ai i) (exp_series_partial _ _ B b n)))
                     (@bplus _ _ B (bsum _ _ B (Datatypes.S n) Hrow)
                              (bsum _ _ B (Datatypes.S n) Kf))).
  { eapply bae_trans with
      (b := bsum _ _ B (Datatypes.S n)
               (fun i : nat => @bplus _ _ B (Hrow i) (Kf i))).
    - apply (bsum_ext _ _ B (Datatypes.S n)
                (fun i : nat => @bmult _ _ B (Ai i) (exp_series_partial _ _ B b n))
                (fun i : nat => @bplus _ _ B (Hrow i) (Kf i))).
      intros k _. exact (Hpt k).
    - exact (bsum_plus _ _ B (Datatypes.S n) Hrow Kf). }
  assert (H3 : bae (@bplus _ _ B (@bplus _ _ B (bsum _ _ B (Datatypes.S n) Hrow)
                                        (bsum _ _ B (Datatypes.S n) Kf))
                              (@bopp _ _ B (bsum _ _ B (Datatypes.S n) Hrow)))
                     (bsum _ _ B (Datatypes.S n) Kf)).
  { apply (@bae_sym _ _ B).
    eapply bae_trans with
      (b := @bplus _ _ B (bsum _ _ B (Datatypes.S n) Kf)
                   (@bplus _ _ B (bsum _ _ B (Datatypes.S n) Hrow)
                            (@bopp _ _ B (bsum _ _ B (Datatypes.S n) Hrow)))).
    - (* bsum Kf == bsum Kf + (bsum Hrow + -bsum Hrow)：先 == 自身+0，再 wd_r *)
      eapply bae_trans with
        (b := @bplus _ _ B (bsum _ _ B (Datatypes.S n) Kf) (@bzero _ _ B)).
      + apply (@bae_sym _ _ B).
        exact (@bplus_zero _ _ B (bsum _ _ B (Datatypes.S n) Kf)).
      + apply (@bplus_wd_r _ _ B). apply (@bae_sym _ _ B).
        exact (@bplus_opp _ _ B (bsum _ _ B (Datatypes.S n) Hrow)).
    - (* bsum Kf + (bsum Hrow + -bsum Hrow) == (bsum Hrow + bsum Kf) + -bsum Hrow *)
      eapply bae_trans with
        (b := @bplus _ _ B (@bplus _ _ B (bsum _ _ B (Datatypes.S n) Kf)
                                (bsum _ _ B (Datatypes.S n) Hrow))
                       (@bopp _ _ B (bsum _ _ B (Datatypes.S n) Hrow))).
      + apply (@bplus_assoc _ _ B _ _ _).
      + apply (@bplus_wd_l _ _ B).
        exact (@bplus_comm _ _ B (bsum _ _ B (Datatypes.S n) Kf)
                             (bsum _ _ B (Datatypes.S n) Hrow)). }
  eapply bae_trans with
    (b := @bplus _ _ B (bsum _ _ B (Datatypes.S n)
                       (fun i : nat =>
                          @bmult _ _ B (Ai i) (exp_series_partial _ _ B b n)))
                  (@bopp _ _ B (bsum _ _ B (Datatypes.S n) Hrow))).
  - exact H1.
  - eapply bae_trans with
      (b := @bplus _ _ B (@bplus _ _ B (bsum _ _ B (Datatypes.S n) Hrow)
                              (bsum _ _ B (Datatypes.S n) Kf))
                     (@bopp _ _ B (bsum _ _ B (Datatypes.S n) Hrow))).
    + apply (@bplus_wd_l _ _ B). exact H2.
    + exact H3.
Qed.
(* ④ 块和范数界：‖块 n‖ ≤T Σ_{i≤n} ‖a‖^i/i!·tail(‖b‖; n−i..n) *)
Lemma bxae_block_norm_le : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall n : nat,
    QleT' (@bnorm _ _ B (@bplus _ _ B (@bmult _ _ B (exp_series_partial _ _ B a n)
                                                (exp_series_partial _ _ B b n))
                                  (@bopp _ _ B (exp_series_partial _ _ B
                                          (@bplus _ _ B a b) n))))
          (ncv_qsum (fun i : nat =>
                 q_pow (@bnorm _ _ B a) i / q_fact i
                 * exp_tail_abs (Nat.sub n i) n (@bnorm _ _ B b))
               (Datatypes.S n)).
Proof.
  intros BA bae B a b hab n.
  eapply (QeqT_Qle_bool_cong _ _ _
            (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _
               (bxae_diff_block _ _ B a b hab n)))).
  eapply qleT'_trans.
  - eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _
               (bxae_bsum_ncvsum _ _ B
                  (fun i : nat =>
                     @bmult _ _ B (@bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))
                              (@bplus _ _ B (exp_series_partial _ _ B b n)
                                       (@bopp _ _ B (exp_series_partial _ _ B b
                                                  (Nat.sub n i)))))
                  (Datatypes.S n))))).
    exact (ncv_norm_sum_le _ _ B
             (fun i : nat =>
                @bmult _ _ B (@bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))
                         (@bplus _ _ B (exp_series_partial _ _ B b n)
                                  (@bopp _ _ B (exp_series_partial _ _ B b
                                               (Nat.sub n i)))))
             (Datatypes.S n)).
  - apply ncv_qsum_le. intros i. destruct i as [| i'].
    + (* i = 0：‖A 0‖ == 1（经 bcoef 1） *)
      assert (Hn0 : (Nat.sub n 0 <= n)%nat) by lia.
      assert (HA0 : bae (@bmult _ _ B (bpow _ _ B a 0%nat)
                                  (@bcoef _ _ B (/ q_fact 0%nat)))
                           (@bcoef _ _ B 1%Q)).
      { assert (Hq0 : (/ q_fact 0%nat)%Q = 1%Q) by reflexivity.
        rewrite Hq0.
        change (bpow _ _ B a 0%nat) with (@bone _ _ B).
        exact (@bmult_one_l _ _ B (@bcoef _ _ B 1%Q)). }
      eapply qleT'_trans.
      * exact (@bnorm_mult _ _ B (@bmult _ _ B (bpow _ _ B a 0%nat)
                                      (@bcoef _ _ B (/ q_fact 0%nat)))
                             (@bplus _ _ B (exp_series_partial _ _ B b n)
                                      (@bopp _ _ B (exp_series_partial _ _ B b
                                                  (Nat.sub n 0))))).
      * eapply qleT'_trans.
        { eapply (qleT'_mult_compat_r).
          { apply (@bnorm_pos _ _ B). }
          { eapply (QeqT_Qle_bool_cong _ _ _
                      (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _ HA0))).
            eapply (QeqT_Qle_bool_cong _ _ _
                      (qeqT_sym_hw _ _ (@bnorm_coef _ _ B 1%Q))).
            apply qleT'_refl. } }
        { apply (bxae_qleT'_mul_le (Qabs 1%Q)
                   (q_pow (@bnorm _ _ B a) 0%nat / q_fact 0%nat)%Q).
          -- apply Qle_refl.
          -- apply QleT'_to_Qle.
             exact (esp_diff_le_tail _ _ B b (Nat.sub n 0) n Hn0).
          -- apply QleT'_to_Qle. apply (@bnorm_pos _ _ B).
          -- exact (QleT'_to_Qle _ _ Qle_0_1). }
    + (* i = S i'：bnorm_esp_term × esp_diff_le_tail *)
      assert (HnS : (Nat.sub n (Datatypes.S i') <= n)%nat) by lia.
      eapply qleT'_trans.
      * exact (@bnorm_mult _ _ B (@bmult _ _ B (bpow _ _ B a (Datatypes.S i'))
                                       (@bcoef _ _ B (/ q_fact (Datatypes.S i'))))
                             (@bplus _ _ B (exp_series_partial _ _ B b n)
                                      (@bopp _ _ B (exp_series_partial _ _ B b
                                                  (Nat.sub n (Datatypes.S i')))))).
      * apply (bxae_qleT'_mul_le).
        -- apply QleT'_to_Qle. apply (bnorm_esp_term _ _ B a i').
        -- apply QleT'_to_Qle.
           exact (esp_diff_le_tail _ _ B b (Nat.sub n (Datatypes.S i')) n HnS).
        -- apply QleT'_to_Qle. apply (@bnorm_pos _ _ B).
        -- apply (bxae_term_nonneg (@bnorm _ _ B a) (Datatypes.S i')).
           apply QleT'_to_Qle. exact (@bnorm_pos _ _ B a).
Qed.

(* ④ 差小：∀eps>0 ∃N，n≥N ⟹ ‖esp a n·esp b n − esp (a+b) n‖ < eps *)
Lemma bxae_diff_small : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    QltT (@bnorm _ _ B (@bplus _ _ B (@bmult _ _ B (exp_series_partial _ _ B a n)
                                                (exp_series_partial _ _ B b n))
                                  (@bopp _ _ B (exp_series_partial _ _ B
                                          (@bplus _ _ B a b) n)))) eps).
Proof.
  intros BA bae B a b hab eps Heps.
  destruct (bxae_qblock_small (@bnorm _ _ B a) (@bnorm _ _ B b) eps
              (QleT'_to_Qle 0 (@bnorm _ _ B a) (@bnorm_pos _ _ B a))
              (QleT'_to_Qle 0 (@bnorm _ _ B b) (@bnorm_pos _ _ B b))
              Heps) as [N HN].
  exists N. intros n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _
           (ncv_qsum (fun i : nat =>
                 q_pow (@bnorm _ _ B a) i / q_fact i
                 * exp_tail_abs (Nat.sub n i) n (@bnorm _ _ B b))
               (Datatypes.S n)) eps).
  - exact (QleT'_to_Qle _ _
             (bxae_block_norm_le _ _ B a b hab n)).
  - exact (HN n Hn).
Qed.

(* 极限移位：v→l 且 ‖u n − v n‖→0 ⟹ u→l *)
Lemma bxae_lim_shift : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (u v : nat -> BA) (l : BA),
  blim _ _ B v l ->
  (forall eps : Q, QltT 0 eps ->
     sigT (fun N : nat => forall n : nat, NatLe N n ->
       QltT (@bnorm _ _ B (@bplus _ _ B (u n) (@bopp _ _ B (v n)))) eps)) ->
  blim _ _ B u l.
Proof.
  intros BA bae B u v l Hv Hdiff eps Heps.
  assert (Hh : QltT 0 (eps / 2)%Q) by (apply bxuq_half_pos; exact Heps).
  destruct (Hdiff (eps / 2)%Q Hh) as [N1 HN1].
  destruct (Hv (eps / 2)%Q Hh) as [N2 HN2].
  exists (Nat.max N1 N2). intros n Hn.
  eapply (QeqT_Qlt_bool_cong _ _ _
            (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _
               (bxuq_diff_split _ _ B (u n) (v n) l)))).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _
           ((@bnorm _ _ B (@bplus _ _ B (u n) (@bopp _ _ B (v n)))) +
            (@bnorm _ _ B (@bplus _ _ B (v n) (@bopp _ _ B l))))%Q eps).
  - exact (QleT'_to_Qle _ _
             (@bnorm_plus _ _ B (@bplus _ _ B (u n) (@bopp _ _ B (v n)))
                           (@bplus _ _ B (v n) (@bopp _ _ B l)))).
  - apply QltT_to_Qlt.
    apply (bxuq_sum_half_lt
             (@bnorm _ _ B (@bplus _ _ B (u n) (@bopp _ _ B (v n))))
             (@bnorm _ _ B (@bplus _ _ B (v n) (@bopp _ _ B l)))).
    + assert (Hle1 : (N1 <= n)%nat).
      * apply (Nat.le_trans N1 (Nat.max N1 N2) n).
        -- apply Nat.le_max_l.
        -- exact (NatLe_drop _ _ Hn).
      * exact (HN1 n (NatLe_lift _ _ Hle1)).
    + assert (Hle2 : (N2 <= n)%nat).
      * apply (Nat.le_trans N2 (Nat.max N1 N2) n).
        -- apply Nat.le_max_r.
        -- exact (NatLe_drop _ _ Hn).
      * exact (HN2 n (NatLe_lift _ _ Hle2)).
Qed.

(* 六环合成：⑤ 左极限 + ④ 差小移位 + ⑥ 唯一性                      *)
(* 迁移史注：bxae_ 族七件（term_reassoc/binom_row/tri_row/           *)
(* diff_block/block_norm_le/diff_small/exp_add）签名收窄至零假设，   *)
(* bnh_esp_term_binom 同位供给，hplus/hwd 形参全摘。                 *)

Theorem bxae_exp_add : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae)
  (a b : BA),
  bae (@bmult _ _ (@bxce_base _ _ E) a b) (@bmult _ _ (@bxce_base _ _ E) b a) ->
  bae (@bxdef_emul _ _ (@bxce_base _ _ E) (bxdef_exp _ _ (@bxce_base _ _ E) a)
                    (bxdef_exp _ _ (@bxce_base _ _ E) b))
       (bxdef_exp _ _ (@bxce_base _ _ E) (@bplus _ _ (@bxce_base _ _ E) a b)).
Proof.
  intros BA bae E a b hab.
  unfold bxdef_emul.
  apply (bxuq_lim_uniq _ _ E
           (fun n : nat =>
              @bmult _ _ (@bxce_base _ _ E) (exp_series_partial _ _ (@bxce_base _ _ E) a n)
                                    (exp_series_partial _ _ (@bxce_base _ _ E) b n))).
  - exact (bxadd_esp_prod_blim _ _ (@bxce_base _ _ E) a b).
  - apply (bxae_lim_shift _ _ (@bxce_base _ _ E)
             (fun n : nat =>
                @bmult _ _ (@bxce_base _ _ E) (exp_series_partial _ _ (@bxce_base _ _ E) a n)
                                      (exp_series_partial _ _ (@bxce_base _ _ E) b n))
             (exp_series_partial _ _ (@bxce_base _ _ E) (@bplus _ _ (@bxce_base _ _ E) a b))
             (bxdef_exp _ _ (@bxce_base _ _ E) (@bplus _ _ (@bxce_base _ _ E) a b))).
    + exact (bxdef_exp_spec _ _ (@bxce_base _ _ E)
                (@bplus _ _ (@bxce_base _ _ E) a b)).
    + intros eps Heps.
      destruct (bxae_diff_small _ _ (@bxce_base _ _ E) a b hab eps Heps)
        as [N HN].
      exists N. intros n Hn.
      apply HN. exact (NatLe_drop _ _ Hn).
Qed.
(* ================= §2 bxoo_lim_esp_zero_bone 族 ================= *)
(* ================= §1 bxoo_lim_esp_zero_bone 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* S1 机械件一（bzero 邻域换骨）：零元级数部分和序列收敛到 bone。  *)
(*   部分和恒一（bxdef_esp_zero_series/BXB bxb_series_zero 同面） *)
(*   ⟹ 距离恒为 ‖bone+(−bone)‖=0 ⟹ N=0 闭式证书。               *)

Lemma bxoo_lim_esp_zero_bone : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae),
  blim _ _ B (fun n : nat => exp_series_partial _ _ B (@bzero _ _ B) n) (@bone _ _ B).
Proof.
  intros BA bae B q Hq.
  refine (existT (fun N : nat => forall n : nat, NatLe N n ->
            QltT (@bnorm _ _ B (@bplus _ _ B (exp_series_partial _ _ B (@bzero _ _ B) n)
                                     (@bopp _ _ B (@bone _ _ B)))) q) 0%nat _).
  intros n Hn.
  pose proof (@bnorm_wd _ _ B
      (@bplus _ _ B (exp_series_partial _ _ B (@bzero _ _ B) n)
               (@bopp _ _ B (@bone _ _ B)))
      (@bplus _ _ B (@bone _ _ B) (@bopp _ _ B (@bone _ _ B)))
      (@bplus_wd _ _ B (exp_series_partial _ _ B (@bzero _ _ B) n)
                  (@bopp _ _ B (@bone _ _ B))
                  (@bone _ _ B) (@bopp _ _ B (@bone _ _ B))
                  (bxdef_esp_zero_series _ _ B n)
                  (@bae_refl _ _ B (@bopp _ _ B (@bone _ _ B))))) as HW1.
  pose proof (@bnorm_wd _ _ B
      (@bplus _ _ B (@bone _ _ B) (@bopp _ _ B (@bone _ _ B)))
      (@bzero _ _ B)
      (@bplus_opp _ _ B (@bone _ _ B))) as HW2.
  eapply (QeqT_Qlt_bool_cong _ _ _ (qeqT_sym_hw _ _ HW1)).
  eapply (QeqT_Qlt_bool_cong _ _ _ (qeqT_sym_hw _ _ HW2)).
  rewrite (@bnorm_zero _ _ B).
  exact Hq.
Qed.

(* S1 机械件二（CD3 形→blim 换骨）：near-one 邻域形与 blim 形     *)
(*   在 l=bone 处逐字同构（blim u bone 展开=本假设形）。          *)
(*   CD3 连接槽：若 bxcd_prod_near_one 实形为                    *)
(*     forall B a q, QltT 0 q -> sigT N, forall n, NatLe N n ->  *)
(*       QltT (bnorm (bplus (esp a n·esp(bopp a) n) (bopp bone))) q*)
(*   则 bxoo_nearone_blim _ _ B _ (bxcd_prod_near_one _ _ B a) 一步上桥。 *)

Lemma bxoo_nearone_blim : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (S : nat -> BA),
  (forall q : Q, QltT 0 q ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
      QltT (@bnorm _ _ B (@bplus _ _ B (S n) (@bopp _ _ B (@bone _ _ B)))) q)) ->
  blim _ _ B S (@bone _ _ B).
Proof.
  intros BA bae B S H q Hq. exact (H q Hq).
Qed.

(* S1 机械件三（emul 整理件）：乘法结合对称面（非交换类下唯一     *)
(*   保安的整理形；类无 bmult_comm，交换面不可造，如实不强造）。   *)

Lemma bxoo_bmult_assoc_sym : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (x y z : BA),
  bae (@bmult _ _ B (@bmult _ _ B x y) z) (@bmult _ _ B x (@bmult _ _ B y z)).
Proof.
  intros BA bae B x y z. exact (@bae_sym _ _ B _ _ (@bmult_assoc _ _ B x y z)).
Qed.

(* S2 UNQ 连接形状（Set 面）：同序列双极限 bae 相等——            *)
(*   主件必要件的形状钉。UNQ 落盘后若 bxuq_lim_uniq 与此同形，    *)
(*   连接= exact (bxuq_lim_uniq B)；若参序/类索引异形，           *)
(*   按本形状包一层换序适配（eps 留记为零，纯参序迁移）。          *)

Definition bxoo_uniq_shape (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) : Set :=
  forall (u : nat -> BA) (x y : BA),
    blim _ _ B u x -> blim _ _ B u y -> bae x y.

(* S3 尾件（④，参数化于③）：bxdef_exp bzero == bone。            *)
(*   两条极限链同喂唯一性：bxdef_exp_spec（ExpDef 出口）+         *)
(*   bxoo_lim_esp_zero_bone（S1 机械件一）。                      *)

Lemma bxoo_bzero_eq_bone_assembly : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae),
  bxoo_uniq_shape _ _ B -> bae (bxdef_exp _ _ B (@bzero _ _ B)) (@bone _ _ B).
Proof.
  intros BA bae B Hunq.
  exact (Hunq (fun n : nat => exp_series_partial _ _ B (@bzero _ _ B) n)
              (bxdef_exp _ _ B (@bzero _ _ B)) (@bone _ _ B)
              (bxdef_exp_spec _ _ B (@bzero _ _ B))
              (bxoo_lim_esp_zero_bone _ _ B)).
Qed.

(* S4 主装配件（①+②+③+④ 合取闭合，参数化于②③两闸门）：         *)
(*   bae (e^a·e^(−a)) (e^0) := bae_trans                          *)
(*     (唯一性：序列左极限 e^a·e^(−a) == 近邻极限 bone)            *)
(*     (对称(④尾件))。                                            *)
(*   全部装配步骤真实现（bae_trans 合取 + 唯一性两次使用 +         *)
(*   对称换向），唯②的 blim 槽与③的 uniq 槽为显式假设。           *)

Theorem bxoo_exp_opp_one_assembly : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a : BA),
  bxoo_uniq_shape _ _ B ->
  blim _ _ B (fun n : nat => @bmult _ _ B (exp_series_partial _ _ B a n)
                                  (exp_series_partial _ _ B (@bopp _ _ B a) n))
         (@bone _ _ B) ->
  bae (@bmult _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B (@bopp _ _ B a)))
        (bxdef_exp _ _ B (@bzero _ _ B)).
Proof.
  intros BA bae B a Hunq Hnear.
  exact (@bae_trans _ _ B
           (@bmult _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B (@bopp _ _ B a)))
           (@bone _ _ B)
           (bxdef_exp _ _ B (@bzero _ _ B))
           (Hunq (fun n : nat => @bmult _ _ B (exp_series_partial _ _ B a n)
                                  (exp_series_partial _ _ B (@bopp _ _ B a) n))
                 (@bmult _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B (@bopp _ _ B a)))
                 (@bone _ _ B)
                 (bxadd_esp_prod_blim _ _ B a (@bopp _ _ B a))
                 Hnear)
           (@bae_sym _ _ B (bxdef_exp _ _ B (@bzero _ _ B)) (@bone _ _ B)
             (bxoo_bzero_eq_bone_assembly _ _ B Hunq))).
Qed.

(* S5 UNQ 闸闭合件（ o 落盘，检验预验后   *)
(* 正册获取）：bxdef_exp bzero == bone——Ext 层无条件 bae 全等式，  *)
(* B25 留记②「exp(0)=one 完全等式面」对 Ext 实例兑现。             *)

Corollary bxoo_bzero_eq_bone : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae),
  bae (bxdef_exp _ _ (@bxce_base _ _ E) (@bzero _ _ (@bxce_base _ _ E)))
      (@bone _ _ (@bxce_base _ _ E)).
Proof.
  intros BA bae E.
  apply (bxoo_bzero_eq_bone_assembly _ _ (@bxce_base _ _ E)).
  exact (bxuq_lim_uniq _ _ E).
Qed.

(*   ② CD12 真件 bxcd_prod_near_one（，          *)
(*     调用位随之去 bxce_coef_plus/bxce_coef_wd 两实参——             *)
(*     hplus/hwd 摘除后无须再喂字段，终面钉 Ext 层不变。              *)
(*   ③ bxuq_lim_uniq _ _ E 剥 E 后=bxoo_uniq_shape base 同构。          *)
(*   主件 bxoo_exp_opp_one：无条件 bae 全等式——                     *)
(*     bae_trans（唯一性：序列左极限 e^a·e^(−a) == 近邻极限 bone）   *)
(*     （对称（④尾件）），与 S4 装配件合取面逐字一致。              *)

Theorem bxoo_exp_opp_one : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae)
  (a : BA),
  bae (@bmult _ _ (@bxce_base _ _ E) (bxdef_exp _ _ (@bxce_base _ _ E) a)
                   (bxdef_exp _ _ (@bxce_base _ _ E) (@bopp _ _ (@bxce_base _ _ E) a)))
      (bxdef_exp _ _ (@bxce_base _ _ E) (@bzero _ _ (@bxce_base _ _ E))).
Proof.
  intros BA bae E a.
  apply (bxoo_exp_opp_one_assembly _ _ (@bxce_base _ _ E) a
           (bxuq_lim_uniq _ _ E)).
  apply (bxoo_nearone_blim _ _ (@bxce_base _ _ E)).
  exact (bxcd_prod_near_one _ _ (@bxce_base _ _ E) a).
Qed.
(* ================= §2 s3c_hplus_of 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* 类字段→显式假设形供给锚（bnh 锚一同位：字段形≡假设形） *)
Definition s3c_hplus_of (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  : forall q r : Q,
    bae (@bplus _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r)) (@bcoef _ _ B (q + r)%Q)
  := @bcoef_plus _ _ B.

Definition s3c_hwd_of (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  : forall q r : Q, q == r -> bae (@bcoef _ _ B q) (@bcoef _ _ B r)
  := fun q r Hq => @bcoef_wd _ _ B q r (qeq_imp_qeqT _ _ Hq).

(* ① E 载体无条件 exp_add（消 bxae_exp_add 的 hplus/hwd 显式钉）    *)

Theorem s3c_exp_add_base : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae)
  (a b : BA),
  bae (@bmult _ _ (@bxce_base _ _ E) a b)
       (@bmult _ _ (@bxce_base _ _ E) b a) ->
  bae (@bxdef_emul _ _ (@bxce_base _ _ E) (bxdef_exp _ _ (@bxce_base _ _ E) a)
                    (bxdef_exp _ _ (@bxce_base _ _ E) b))
       (bxdef_exp _ _ (@bxce_base _ _ E) (@bplus _ _ (@bxce_base _ _ E) a b)).
Proof.
  intros BA bae E a b hab.
  exact (bxae_exp_add _ _ E a b hab).
Qed.

(* ② plain B 载体 exp_add 装配（六环合流：⑤左极限 + ④差小移位      *)
(*   + ⑥唯一性（假设化）；唯一性槽以 bxoo_uniq_shape 显式给出——     *)
(*   plain 类无 sep 字段，与 bxoo_exp_opp_one_assembly 同口径）      *)

Theorem s3c_exp_add_plain : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  bxoo_uniq_shape _ _ B ->
  bae (@bxdef_emul _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B b))
       (bxdef_exp _ _ B (@bplus _ _ B a b)).
Proof.
  intros BA bae B a b hab Hunq.
  unfold bxdef_emul.
  apply (Hunq (fun n : nat =>
                 @bmult _ _ B (exp_series_partial _ _ B a n)
                          (exp_series_partial _ _ B b n))).
  - (* ⑤ 左极限：部分积序列 → e^a·e^b *)
    exact (bxadd_esp_prod_blim _ _ B a b).
  - (* ④ 差小移位：部分积序列 → e^(a+b) *)
    apply (bxae_lim_shift _ _ B
             (fun n : nat =>
                @bmult _ _ B (exp_series_partial _ _ B a n)
                         (exp_series_partial _ _ B b n))
             (fun n : nat => exp_series_partial _ _ B (@bplus _ _ B a b) n)
             (bxdef_exp _ _ B (@bplus _ _ B a b))
             (bxdef_exp_spec _ _ B (@bplus _ _ B a b))).
    intros eps Heps.
    destruct (bxae_diff_small _ _ B a b hab eps Heps) as [N HN].
    exists N. intros n Hn.
    exact (HN n (NatLe_drop N n Hn)).
Qed.

(* ③ 可逆性合流：(e^a) 的逆元 = e^{-a}                              *)
(*   ③a Ext 载体无条件：e^a·e^{-a} == e^0 与 e^0 == bone 两绿件      *)

Theorem s3c_exp_opp_one_base : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae)
  (a : BA),
  bae (@bmult _ _ (@bxce_base _ _ E) (bxdef_exp _ _ (@bxce_base _ _ E) a)
                    (bxdef_exp _ _ (@bxce_base _ _ E) (@bopp _ _ (@bxce_base _ _ E) a)))
       (bxdef_exp _ _ (@bxce_base _ _ E) (@bzero _ _ (@bxce_base _ _ E))).
Proof.
  intros BA bae E a. exact (bxoo_exp_opp_one _ _ E a).
Qed.

Theorem s3c_exp_inv_base : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae)
  (a : BA),
  bae (@bmult _ _ (@bxce_base _ _ E) (bxdef_exp _ _ (@bxce_base _ _ E) a)
                    (bxdef_exp _ _ (@bxce_base _ _ E) (@bopp _ _ (@bxce_base _ _ E) a)))
       (@bone _ _ (@bxce_base _ _ E)).
Proof.
  intros BA bae E a.
  apply (@bae_trans _ _ (@bxce_base _ _ E)
           (@bmult _ _ (@bxce_base _ _ E) (bxdef_exp _ _ (@bxce_base _ _ E) a)
                        (bxdef_exp _ _ (@bxce_base _ _ E) (@bopp _ _ (@bxce_base _ _ E) a)))
           (bxdef_exp _ _ (@bxce_base _ _ E) (@bzero _ _ (@bxce_base _ _ E)))
           (@bone _ _ (@bxce_base _ _ E))).
  - exact (bxoo_exp_opp_one _ _ E a).
  - exact (bxoo_bzero_eq_bone _ _ E).
Qed.

(*   ③b plain 载体：bxoo_exp_opp_one_assembly 的 Hnear 槽闭合——     *)
(*   bxcd_prod_near_one 的 hplus/hwd 显式假设喂基类字段（S6 注记     *)
(*   「plain 喂不进」系类迁移前旧账，bnh 锚一后即通）。               *)

Theorem s3c_exp_opp_one_plain : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a : BA),
  bxoo_uniq_shape _ _ B ->
  bae (@bmult _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B (@bopp _ _ B a)))
       (bxdef_exp _ _ B (@bzero _ _ B)).
Proof.
  intros BA bae B a Hunq.
  apply (bxoo_exp_opp_one_assembly _ _ B a Hunq).
  apply (bxoo_nearone_blim _ _ B
           (fun n : nat =>
              @bmult _ _ B (exp_series_partial _ _ B a n)
                       (exp_series_partial _ _ B (@bopp _ _ B a) n))).
  exact (bxcd_prod_near_one _ _ B a).
Qed.

Theorem s3c_exp_inv_plain : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a : BA),
  bxoo_uniq_shape _ _ B ->
  bae (@bmult _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B (@bopp _ _ B a)))
       (@bone _ _ B).
Proof.
  intros BA bae B a Hunq.
  apply (@bae_trans _ _ B
           (@bmult _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B (@bopp _ _ B a)))
           (bxdef_exp _ _ B (@bzero _ _ B))
           (@bone _ _ B)).
  - exact (s3c_exp_opp_one_plain _ _ B a Hunq).
  - exact (bxoo_bzero_eq_bone_assembly _ _ B Hunq).
Qed.

(* G4 假设面自证（PA≥1：主件四件）                                  *)
Print Assumptions s3c_exp_add_base.
Print Assumptions s3c_exp_add_plain.
Print Assumptions s3c_exp_inv_base.
Print Assumptions s3c_exp_inv_plain.
