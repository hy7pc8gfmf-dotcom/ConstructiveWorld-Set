(* ========================================================================= *)
(* LW2UpperBound - explicit rational upper suppression of the Hermite        *)
(* endpoint functional.                                                      *)
(* 模块名：LW2UpperBound.  数学使命：对节点泛函                              *)
(*         lambda n f = sum_{j=0}^{n+1} sum_{k<|f|} c_{jk} * f^{(k)}(j)      *)
(*         （c_{jk} ∈ {−1,0,1}，定义在 LW2Hermite）建立显式有理常数上界：    *)
(*         在「节点 {0,…,n+1} 面上各阶导数取值的逐节点压制」前提下，         *)
(*         |lambda n f| ≤ (节点个数 × 多项式长度) · E，继而取 π 界常数       *)
(*         10/3（S10 双岸界 real_pi_leibniz_lt_ten_thirds 的有理上岸）的     *)
(*         幂为统一界 E，经阶乘压制链 (10/3)^N ≤ N!（LW0FactGrowth）封顶于   *)
(*         |lambda n f| ≤ c_n，c_n 为含节点个数与 π 界的显式 Q 常数函数，    *)
(*         并给出 (c_n # 1) 字形的整数化推论。                  *)
(* 依赖清单：LW0QPoly（QPoly 及 eval/deriv_iter 点态律）；LW2Hermite         *)
(*         （lw2_lambda / lw2_lambda_coef / lw2_node / lw2_qsum0）；         *)
(*         LW0FactGrowth（lw0_q_of_nat 族、lw0_pi_bound_dominated_even、     *)
(*         lw0_q_pow_mono_base）；S02_CauchyComplete（QleT' 及双向桥、       *)
(*         qleT'_trans）；S03_QExp（q_fact / q_pow）；Stdlib QArith/Qabs、   *)
(*         Arith、Lia。                                                      *)
(* 对标行：Hermite 1873 (C. R. Acad. Sci. Paris 77) 的上界半边——组合分部    *)
(*         积分证明中 |L(f)| ≤ C·max|f^{(k)}(j)| 的显式常数形态；π<10/3      *)
(*         取自库内 S10_KVQuantTrig 的 Leibniz 级数双岸估计（仅取 10/3）。   *)
(* 构造性注记：全部语句 Set 层承载——前提位与结论位一律 QleT'（Id 判定形），  *)
(*         零 Prop 前提位、零存在变元；归纳为泛形递推结构（m 泛形和压制件    *)
(*         lw2u_qsum0_abs_le 为核心）；零公理、零承认、零经典逻辑；          *)
(*         Separate Extraction 后 Obj.magic 计数为零。                      *)
(* 编译配方：env COQLIB/ROCQLIB 指向 Rocq 9.1 库，沙箱内同置依赖件           *)
(*         （LW0QPoly/LW2Hermite/LW0FactGrowth 的 .v 先行编译绿、S01/S02/S03 *)
(*         的 .vo 暂存），然后                                              *)
(*         "coqc.exe -q -Q . "" LW2UpperBound.v"。                           *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith Lia.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW0FactGrowth.
Require Import LW2Hermite.

(* ------------------------------------------------------------------ *)
(* 第 1 节.  自然数有理像的小辅助等式与 QleT' 等式桥.                   *)
(* ------------------------------------------------------------------ *)

(* Qmake 乘法分解：同分母积的分子 = 分子积。 *)
Lemma lw2u_make_mul : forall (a b : Z) (d e : positive),
  QeqT ((a # d) * (b # e)) ((a * b) # (d * e))%Q.
Proof.
  intros a b d e. apply qeq_imp_qeqT. unfold Qeq, Qmult. cbn [Qnum Qden]. lia.
Qed.

(* 有理像的后继分解：q(n+1) = q(n) + 1。 *)
Lemma lw2u_q_of_nat_succ : forall m : nat,
  QeqT (lw0_q_of_nat (Datatypes.S m)) (lw0_q_of_nat m + (1 # 1)%Q).
Proof.
  intro m. apply qeq_imp_qeqT. unfold lw0_q_of_nat, Qeq, Qplus. cbn [Qnum Qden].
  assert (Hz : Z.of_nat (Datatypes.S m) = (Z.of_nat m + 1)%Z) by lia.
  rewrite Hz. lia.
Qed.

(* 有理像的乘法同态：q(a·b) = q(a)·q(b)。 *)
Lemma lw2u_q_of_nat_mul : forall a b : nat,
  QeqT (lw0_q_of_nat (a * b)) (lw0_q_of_nat a * lw0_q_of_nat b).
Proof.
  intros a b. apply qeq_imp_qeqT. unfold lw0_q_of_nat, Qeq, Qmult. cbn [Qnum Qden].
  assert (Hz : Z.of_nat (a * b) = (Z.of_nat a * Z.of_nat b)%Z) by lia.
  rewrite Hz. lia.
Qed.

(* QleT' 右侧等式桥：x ≤T' y 且 y == z 蕴含 x ≤T' z。 *)
Lemma lw2u_qleT'_eq_r : forall x y z : Q,
  QleT' x y -> y == z -> QleT' x z.
Proof.
  intros x y z H He. apply (qleT'_trans x y z H).
  apply Qle_to_QleT'. rewrite He. apply (Qle_refl z).
Qed.

(* QleT' 左侧等式桥：x == y 且 y ≤T' z 蕴含 x ≤T' z。 *)
Lemma lw2u_qleT'_eq_l : forall x y z : Q,
  QleT' y z -> x == y -> QleT' x z.
Proof.
  intros x y z H He. apply (qleT'_trans x y z).
  - apply Qle_to_QleT'. rewrite <- He. apply (Qle_refl x).
  - exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* 第 2 节.  泛形和的统一界压制（n 泛形递推核心）.                      *)
(* 对和 lw2_qsum0 g m = g 0 + … + g (m-1)，若每项绝对值 ≤ T，则         *)
(* |lw2_qsum0 g m| ≤ m · T。三角形不等式逐层推进，计数由有理像承载。    *)
(* ------------------------------------------------------------------ *)

Lemma lw2u_qsum0_abs_le : forall (m : nat) (g : nat -> Q) (T : Q),
  (forall j, Nat.lt j m -> QleT' (Qabs (g j)) T) ->
  QleT' (Qabs (lw2_qsum0 g m)) (lw0_q_of_nat m * T).
Proof.
  intros m. induction m as [| m IH]; intros g T H.
  - (* 基例：空和为 0，|0| ≤ 0·T = 0。 *)
    cbn [lw2_qsum0]. apply Qle_to_QleT'.
    assert (Hz : lw0_q_of_nat 0 * T == 0%Q).
    { unfold lw0_q_of_nat. cbn [Z.of_nat]. ring. }
    rewrite Hz. apply (Qle_refl 0%Q).
  - (* 归纳步：|Σ_m + g m| ≤ |Σ_m| + |g m| ≤ m·T + T = (m+1)·T。 *)
    cbn [lw2_qsum0].
    assert (Hprev : QleT' (Qabs (lw2_qsum0 g m)) (lw0_q_of_nat m * T)).
    { apply IH. intros j Hj. apply H. lia. }
    assert (Hlast : QleT' (Qabs (g m)) T) by (apply H; lia).
    assert (Htri : Qle (Qabs (lw2_qsum0 g m + g m))
                       (Qabs (lw2_qsum0 g m) + Qabs (g m)))
      by apply Qabs_triangle.
    assert (Hsplit : Qle (Qabs (lw2_qsum0 g m) + Qabs (g m))
                         (lw0_q_of_nat m * T + T)).
    { apply Qplus_le_compat;
        [ exact (QleT'_to_Qle _ _ Hprev) | exact (QleT'_to_Qle _ _ Hlast) ]. }
    assert (Hstep : lw0_q_of_nat m * T + T == lw0_q_of_nat (Datatypes.S m) * T).
    { rewrite (qeqT_imp_qeq _ _ (lw2u_q_of_nat_succ m)). ring. }
    apply Qle_to_QleT'. rewrite <- Hstep.
    exact (Qle_trans _ (Qabs (lw2_qsum0 g m) + Qabs (g m)) _ Htri Hsplit).
Qed.

(* ------------------------------------------------------------------ *)
(* 第 3 节.  节点系数的绝对值界.                                        *)
(* 系数表 lw2_lambda_coef 只取 −1,0,1 三值，故其绝对值 ≤ 1。            *)
(* ------------------------------------------------------------------ *)

Lemma lw2u_coef_abs_le_one : forall (n j k : nat),
  QleT' (Qabs ((lw2_lambda_coef n j k) # 1)%Q) ((1 # 1)%Q).
Proof.
  intros n j k. apply Qle_to_QleT'. unfold Qabs, lw2_lambda_coef. cbn [Qnum Qden].
  destruct (Nat.eqb j 0); destruct (Nat.eqb j (Datatypes.S n));
    cbn [Z.abs]; unfold Qle; cbn [Qnum Qden]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 第 4 节.  单节点面压制.                                              *)
(* 固定节点 j：|Σ_{k<|f|} c_{jk} f^{(k)}(j)| ≤ |f| · E，只要每个         *)
(* |f^{(k)}(j)| ≤ E。由系数绝对值 ≤ 1、乘积绝对值分解与第 2 节闭合。     *)
(* ------------------------------------------------------------------ *)

Lemma lw2u_node_term_abs_le : forall (n : nat) (f : QPoly) (j : nat) (E : Q),
  (forall k, Nat.lt k (length f) ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))) E) ->
  QleT' (Qabs (lw2_qsum0 (fun k =>
            ((lw2_lambda_coef n j k) # 1)%Q *
            qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
            (length f)))
        (lw0_q_of_nat (length f) * E).
Proof.
  intros n f j E H.
  apply (lw2u_qsum0_abs_le (length f)
    (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
              qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) E).
  intros k Hk. apply Qle_to_QleT'. rewrite Qabs_Qmult.
  apply (Qle_trans _ ((1 # 1)%Q *
           Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))).
  - apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ (lw2u_coef_abs_le_one n j k)).
    + apply Qabs_nonneg.
  - assert (Hx1 : (1 # 1)%Q *
             Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) ==
             Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))) by ring.
    rewrite Hx1. exact (QleT'_to_Qle _ _ (H k Hk)).
Qed.

(* ------------------------------------------------------------------ *)
(* 第 5 节.  主压制链（逐节点压制前提 → 显式常数上界）.                 *)
(* 若节点 j = 0,…,n+1 面上一切 |f^{(k)}(j)| ≤ E，则                     *)
(* |lambda n f| ≤ (n+2)·|f|·E——节点个数 n+2 与多项式长度 |f| 显式入界。  *)
(* ------------------------------------------------------------------ *)

Theorem lw2_L_upper_nodes : forall (n : nat) (f : QPoly) (E : Q),
  (forall j k, Nat.le j (Datatypes.S n) -> Nat.lt k (length f) ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))) E) ->
  QleT' (Qabs (lw2_lambda n f))
        (lw0_q_of_nat (Datatypes.S (Datatypes.S n) * length f) * E).
Proof.
  intros n f E H. unfold lw2_lambda. cbv beta.
  apply (lw2u_qleT'_eq_r _
    (lw0_q_of_nat (Datatypes.S (Datatypes.S n)) *
     (lw0_q_of_nat (length f) * E))).
  - apply (lw2u_qsum0_abs_le (Datatypes.S (Datatypes.S n))
      (fun j => lw2_qsum0
        (fun k => ((lw2_lambda_coef n j k) # 1)%Q *
                  qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
        (length f))
      (lw0_q_of_nat (length f) * E)).
    intros j Hj. apply (lw2u_node_term_abs_le n f j).
    intros k Hk. apply H; lia.
  - rewrite (qeqT_imp_qeq _ _
      (lw2u_q_of_nat_mul (Datatypes.S (Datatypes.S n)) (length f))). ring.
Qed.

(* ------------------------------------------------------------------ *)
(* 第 6 节.  π 界常数封顶：上界主件.                                    *)
(* 取统一界 E = (10/3)^{22+2n}（10/3 为 S10 双岸界 π < 10/3 的有理      *)
(* 上岸常数），经阶乘压制 (10/3)^N ≤ N! 得                              *)
(*   |lambda n f| ≤ (n+2)·|f|·(22+2n)!  =: c_n.                         *)
(* c_n 为显式 Q 常数函数：含节点个数 n+2、多项式长度 |f| 与 π 界链终点  *)
(* (22+2n)!；其幂-阶乘核为 |L(f)| ≤ C^N·(N!) 形压制链。                  *)
(* ------------------------------------------------------------------ *)

Definition lw2u_c_n (n ell : nat) : Q :=
  lw0_q_of_nat (Datatypes.S (Datatypes.S n) * ell) * q_fact (22 + 2 * n)%nat.

Theorem lw2_L_upper_hermite : forall (n : nat) (f : QPoly),
  (forall j k, Nat.le j (Datatypes.S n) -> Nat.lt k (length f) ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))
           (q_pow (10 # 3) (22 + 2 * n)%nat)) ->
  QleT' (Qabs (lw2_lambda n f)) (lw2u_c_n n (length f)).
Proof.
  intros n f H.
  apply (qleT'_trans _
    (lw0_q_of_nat (Datatypes.S (Datatypes.S n) * length f) *
     q_pow (10 # 3) (22 + 2 * n)%nat)).
  - apply lw2_L_upper_nodes. exact H.
  - apply Qle_to_QleT'.
    rewrite (Qmult_comm (lw0_q_of_nat
              (Datatypes.S (Datatypes.S n) * length f))
              (q_pow (10 # 3) (22 + 2 * n)%nat)),
            (Qmult_comm (lw0_q_of_nat
              (Datatypes.S (Datatypes.S n) * length f))
              (q_fact (22 + 2 * n)%nat)).
    apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ (lw0_pi_bound_dominated_even n)).
    + exact (QleT'_to_Qle _ _
        (lw0_q_of_nat_nonneg (Datatypes.S (Datatypes.S n) * length f))).
Qed.

(* ------------------------------------------------------------------ *)
(* 第 7 节.  (c_n # 1) 字形推论：整数化常数.                            *)
(* 先立 Z 层幂的 Q 像桥：整数 z 的 Q 像的 q_pow 等于 z^N 的 Q 像；再以   *)
(* π 界常数的整数化放大 10（因 (10/3)^N ≤ 10^N）封顶为 Zmake 字形       *)
(* |lambda n f| ≤ ((n+2)·|f| 之有理像 × 10^{22+2n}) # 1。               *)
(* ------------------------------------------------------------------ *)

(* 整分母 1 的 Z 幂桥：q_pow (z#1) N == (z^{N} # 1)。泛形归纳结构。 *)
Lemma lw2u_qpow_zmake : forall (z : Z) (N : nat),
  QeqT (q_pow (z # 1)%Q N) ((z ^ Z.of_nat N) # 1)%Q.
Proof.
  intros z. induction N as [| N IH].
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. cbn [q_pow]. rewrite (qeqT_imp_qeq _ _ IH).
    assert (Hz : Z.of_nat (Datatypes.S N) = (1 + Z.of_nat N)%Z) by lia.
    rewrite Hz. rewrite Z.pow_add_r by lia.
    rewrite (qeqT_imp_qeq _ _ (lw2u_make_mul _ _ _ _)).
    unfold Qeq. cbn [Qnum Qden].
    replace (1 * 1)%positive with 1%positive by reflexivity.
    rewrite Z.pow_1_r. lia.
Qed.

(* Zmake 字形主推论：c_n 的整数化常数 =
   (节点个数×长度之有理像的分子) × 10^{22+2n}，其中 10 为 π 界常数
   10/3 的整数化放大（10/3 ≤ 10）。 *)
Theorem lw2_L_upper_hermite_zmake : forall (n : nat) (f : QPoly),
  (forall j k, Nat.le j (Datatypes.S n) -> Nat.lt k (length f) ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))
           (q_pow (10 # 3) (22 + 2 * n)%nat)) ->
  QleT' (Qabs (lw2_lambda n f))
        (((Z.of_nat (Datatypes.S (Datatypes.S n) * length f) *
           (10 ^ Z.of_nat (22 + 2 * n))) # 1)%Q).
Proof.
  intros n f H.
  assert (Hbase : QleT' (q_pow (10 # 3) (22 + 2 * n)%nat)
                        (q_pow (10 # 1) (22 + 2 * n)%nat)).
  { apply (lw0_q_pow_mono_base (10 # 3) (10 # 1) (22 + 2 * n)%nat).
    - vm_compute. reflexivity.
    - vm_compute. reflexivity. }
  assert (Hbridge : lw0_q_of_nat (Datatypes.S (Datatypes.S n) * length f) *
                    q_pow (10 # 1) (22 + 2 * n)%nat
                    == ((Z.of_nat (Datatypes.S (Datatypes.S n) * length f) *
                         (10 ^ Z.of_nat (22 + 2 * n))) # 1)%Q).
  { rewrite (qeqT_imp_qeq _ _ (lw2u_qpow_zmake 10%Z (22 + 2 * n)%nat)),
            (qeqT_imp_qeq _ _
              (lw2u_q_of_nat_mul (Datatypes.S (Datatypes.S n)) (length f))).
    unfold lw0_q_of_nat.
    rewrite !(qeqT_imp_qeq _ _ (lw2u_make_mul _ _ _ _)).
    unfold Qeq. cbn [Qnum Qden].
    replace (1 * 1)%positive with 1%positive by reflexivity.
    assert (Hzm : Z.of_nat (Datatypes.S (Datatypes.S n) * length f) =
                  (Z.of_nat (Datatypes.S (Datatypes.S n)) *
                   Z.of_nat (length f))%Z) by lia.
    rewrite Hzm. lia. }
  apply (lw2u_qleT'_eq_r _
    (lw0_q_of_nat (Datatypes.S (Datatypes.S n) * length f) *
     q_pow (10 # 1) (22 + 2 * n)%nat)).
  - apply (qleT'_trans _
      (lw0_q_of_nat (Datatypes.S (Datatypes.S n) * length f) *
       q_pow (10 # 3) (22 + 2 * n)%nat)).
    + apply lw2_L_upper_nodes. exact H.
    + apply Qle_to_QleT'.
      rewrite (Qmult_comm (lw0_q_of_nat
                (Datatypes.S (Datatypes.S n) * length f))
                (q_pow (10 # 3) (22 + 2 * n)%nat)),
              (Qmult_comm (lw0_q_of_nat
                (Datatypes.S (Datatypes.S n) * length f))
                (q_pow (10 # 1) (22 + 2 * n)%nat)).
      apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ Hbase).
      * exact (QleT'_to_Qle _ _
          (lw0_q_of_nat_nonneg (Datatypes.S (Datatypes.S n) * length f))).
  - exact Hbridge.
Qed.

(* ========================================================================= *)
(* 提取检验与公理面自审：提取产物零 Obj.magic，各语句 Closed。               *)
(* ========================================================================= *)

From Stdlib Require Import Extraction.
Separate Extraction lw2_L_upper_nodes lw2_L_upper_hermite lw2_L_upper_hermite_zmake.
Print Assumptions lw2_L_upper_nodes.
Print Assumptions lw2_L_upper_hermite.
Print Assumptions lw2_L_upper_hermite_zmake.
