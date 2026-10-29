(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   lic_e_irrational_criterion（原 L747，2 句玩具证）                    *)
(*   lic_qltt_comp_r（原 L58，5 句玩具证）                                *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqIrrationalCriterion.v                                    *)
(*                                                               *)
(* 目的：单实例「e 部分和逃离一切有理数」引擎（SumInvFactEscape）      *)
(*       普遍化为构造性无理性判据母定理：                              *)
(*         近似序列 x_n + 误差窗 e_n，若 (i) 尾控 |x_k−x_n| < e_n        *)
(*         (n≥1)、(ii) 每个有理数 q 有 n≥1 使 e_n < |q−x_n|、             *)
(*         (iii) e_n→0（Q 层显式），则 X := lim x_n 满足                    *)
(*         ∀q:Q，存在 Q 层正分离常数 c 使 real_const c < |X−q|            *)
(*         （real_lt sigT 见证形，先例判例语句面）。                    *)
(* 主件：lic_irrational_criterion；伴件 lic_seq_cauchy（柯西性推导）、     *)
(*       lic_e_irrational_criterion（e 实例回验：真走母定理）。          *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、                  *)
(*       SumInvFactEscape（sif_d 递推/整化桥/零点两步逃逸/判定件复用）；    *)
(*       Stdlib QArith、ZArith、Arith.Factorial、Lia、Lra、Qfield。     *)
(* 备注：公理面——本件纯构造性（零经典逻辑、零排中、零 承认）；           *)
(*       语句面全 Set 层（QltT/real_lt/sigT 形，无 Prop 泄露位）；         *)
(*       证内 Prop（Qlt/Qle）仅作 Q 层推理脚手架，不进结论面。             *)
(*       e 实例窗口见证的「零号升级」：sif_escape 见证可为 n=0，              *)
(*       而 n≥1 窗口见证由本件 lic_enum（复用 sif_dec_pt 判定件）+          *)
(*       lic_window_shift（sif_window 的平移克隆，指数窗 [1,2b+2]）+        *)
(*       sif_zero_escape 联立导出——升级不引入新数学内容，零强造。            *)
(* 命名：lic_ 前缀（开工 grep 零撞名）。                              *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* S0：Q 层通用小件                                                *)
(* ============================================================ *)

(* Qlt 沿 Qeq 的右端替换 *)
Lemma lic_qlt_comp_r : forall x1 x2 z : Q, x1 == x2 -> Qlt z x1 -> Qlt z x2.
Proof.
  intros x1 x2 z Heq Hlt.
  destruct x1 as [a b]. destruct x2 as [c d]. destruct z as [e f].
  unfold Qlt, Qeq in *. cbn [Qnum Qden] in *.
  assert (Hb0 : (0 < Z.pos b)%Z) by (apply Pos2Z.is_pos).
  assert (Hd0 : (0 < Z.pos d)%Z) by (apply Pos2Z.is_pos).
  assert (H1 : (e * (Z.pos b * Z.pos d) < (a * Z.pos d) * Z.pos f)%Z).
  { assert (H0 : (e * Z.pos b * Z.pos d < a * Z.pos f * Z.pos d)%Z).
    { apply (Zmult_lt_compat_r (e * Z.pos b) (a * Z.pos f)
                     (Z.pos d) Hd0). exact Hlt. }
    lia. }
  rewrite Heq in H1.
    all: try nia.
Qed.

(* QltT 沿 Qeq 的右端替换 *)
Lemma lic_qltt_comp_r : forall x1 x2 z : Q, x1 == x2 -> QltT z x1 -> QltT z x2.
Proof.
  intros x1 x2 z Heq Hlt.
  exact (Qlt_to_QltT z x2
    (lic_qlt_comp_r x1 x2 z Heq (QltT_to_Qlt z x1 Hlt))).
Qed.


Lemma lic_fact_pos1 : forall n : nat, (1 <= fact n)%nat.
Proof.
  induction n as [|n IH].
  - cbn [fact]. lia.
  - cbn [fact].
    apply Nat.le_trans with (Datatypes.S n * 1)%nat.
    + lia.
    + apply Nat.mul_le_mono; [lia | exact IH].
Qed.

Lemma lic_fact_ge_self : forall n : nat, (1 <= n)%nat -> (n <= fact n)%nat.
Proof.
  induction n as [|n IH].
  - intros Hn. cbn [fact]. lia.
  - intros _. cbn [fact].
    apply Nat.le_trans with (Datatypes.S n * 1)%nat.
    + lia.
    + apply Nat.mul_le_mono; [lia | apply lic_fact_pos1].
Qed.

(* 线性 Qle 拼装：u+v ≤ w 且 t ≤ v ⟹ u+t ≤ w *)
Lemma lic_le_add_le : forall u v w t : Q, Qle (u + v) w -> Qle t v -> Qle (u + t) w.
Proof.
  intros u v w t H1 H2. apply (Qle_trans _ (u + v)).
  - apply (Qplus_le_compat u u t v); [apply Qle_refl | exact H2].
  - exact H1.
Qed.

(* Q 序小件（全 destruct-Q 机械模式，零 micromega-on-Q 依赖） *)

(* 右加保序 *)
Lemma lic_qlt_add_r : forall x y z : Q, Qlt x y -> Qlt (x + z) (y + z).
Proof.
  intros x y z H.
  assert (Hle : Qle (x + z) (y + z))
    by (apply (Qplus_le_compat x y z z);
        [apply Qlt_le_weak; exact H | apply Qle_refl]).
  destruct (Qle_lt_or_eq (x + z) (y + z) Hle) as [Hlt | Heq].
  - exact Hlt.
  - exfalso. apply (Qlt_not_eq x y H).
    assert (Hxz : ((x + z) + (- z))%Q == x).
    { rewrite <- Qplus_assoc, Qplus_opp_r, Qplus_0_r. reflexivity. }
    assert (Hyz : ((y + z) + (- z))%Q == y).
    { rewrite <- Qplus_assoc, Qplus_opp_r, Qplus_0_r. reflexivity. }
    apply (Qeq_trans _ ((x + z) + (- z))%Q).
    + apply Qeq_sym. exact Hxz.
    + setoid_rewrite Heq. exact Hyz.
Qed.

(* 左加保序 *)
Lemma lic_qlt_add_l : forall z x y : Q, Qlt x y -> Qlt (z + x) (z + y).
Proof.
  intros z x y H.
  assert (Hle : Qle (z + x) (z + y))
    by (apply (Qplus_le_compat z z x y); [apply Qle_refl | exact (Qlt_le_weak x y H)]).
  destruct (Qle_lt_or_eq (z + x) (z + y) Hle) as [Hlt | Heq].
  - exact Hlt.
  - exfalso. apply (Qlt_not_eq x y H).
    assert (HL : forall t : Q, ((- z) + (z + t))%Q == t).
    { intro t. rewrite (Qplus_assoc (- z) z t), (Qplus_comm (- z) z),
        Qplus_opp_r, Qplus_0_l. reflexivity. }
    apply (Qeq_trans _ ((- z) + (z + x))%Q).
    + symmetry. apply HL.
    + apply (Qeq_trans _ ((- z) + (z + y))%Q).
      * setoid_rewrite Heq. reflexivity.
      * apply HL.
Qed.

(* 加法严格化：0 < b ⟹ a < a + b *)
Lemma lic_qlt_lt_add_r : forall a b : Q, Qlt 0 b -> Qlt a (a + b).
Proof.
  intros [an ad] [bn bd]. unfold Qlt in *. cbn [Qnum Qden Qplus] in *. lia.
Qed.

(* 减法正性：E < A ⟹ 0 < A − E *)
Lemma lic_qlt_0_minus : forall E A : Q, Qlt E A -> Qlt 0 ((A - E)%Q).
Proof.
  intros [en ed] [an ad]. unfold Qlt in *.
  cbn [Qnum Qden Qminus Qplus Qopp] in *. lia.
Qed.

(* Qlt_bool 桥（全序可判定，destruct-Q 机械模式） *)
Lemma lic_qlt_bool_true : forall x y : Q, Qlt_bool x y = true -> Qlt x y.
Proof.
  intros x y H. unfold Qlt_bool in H.
  destruct (Qcompare x y) eqn:Ecc; try discriminate.
  apply (proj2 (Qlt_alt x y)). exact Ecc.
Qed.

Lemma lic_qlt_bool_false_le : forall x y : Q, Qlt_bool x y = false -> Qle y x.
Proof.
  intros x y H. unfold Qlt_bool in H.
  destruct (Qcompare x y) eqn:Ecc; try discriminate.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT, Qeq_sym. unfold Qeq, Qcompare in Ecc.
    exact (proj1 (Z.compare_eq_iff (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) Ecc).
  - apply Qlt_le_weak. unfold Qlt, Qcompare in Ecc.
    exact (proj1 (Z.compare_gt_iff (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) Ecc).
Qed.

(* 减法加法回加：((B − c) + c) == B *)
Lemma lic_qlt_minus_add_r : forall B c : Q, ((B - c) + c)%Q == B.
Proof.
  intros B c. unfold Qminus.
  rewrite <- Qplus_assoc, (Qplus_comm (- c) c), Qplus_opp_r, Qplus_0_r.
  reflexivity.
Qed.

(* 左加消去 *)
Lemma lic_qlt_add_l_cancel : forall z x y : Q, Qlt (z + x) (z + y) -> Qlt x y.
Proof.
  intros z x y H.
  destruct (Qlt_bool x y) eqn:Ec.
  - exact (lic_qlt_bool_true x y Ec).
  - exfalso.
    pose proof (lic_qlt_bool_false_le x y Ec) as Hle1.
    assert (Hle2 : Qle (z + y) (z + x))
      by (apply (Qplus_le_compat z z y x); [apply Qle_refl | exact Hle1]).
    exact (Qlt_not_eq (z + y) (z + y)
             (Qle_lt_trans (z + y) (z + x) (z + y) Hle2 H) (Qeq_refl (z + y))).
Qed.

(* 右加消去 *)
Lemma lic_qlt_add_r_cancel_r : forall x y z : Q, Qlt (x + z) (y + z) -> Qlt x y.
Proof.
  intros x y z H.
  setoid_rewrite (Qplus_comm x z) in H.
  setoid_rewrite (Qplus_comm y z) in H.
  exact (lic_qlt_add_l_cancel z x y H).
Qed.

(* 三角分解：q − a == (q − b) + (b − a) *)
Lemma lic_qlt_tri_decomp : forall q a b : Q, (q - a)%Q == ((q - b) + (b - a))%Q.
Proof.
  intros [qn qd] [an ad] [bn bd].
  unfold Qeq. cbn [Qnum Qden Qminus Qplus Qopp Qmult] in *.
    all: try nia.
Qed.

(* 全序补全：¬(y < x) ⟹ x ≤ y *)
Lemma lic_qlt_dec_le : forall x y : Q, ~ Qlt y x -> Qle x y.
Proof.
  intros [xn xd] [yn yd] H. unfold Qlt, Qle in *. cbn [Qnum Qden] in *. lia.
Qed.

(* 半值桥：c == (A − E)/2 ⟹ c + c == A − E *)
Lemma lic_half_bridge : forall (c A E : Q),
  c == ((A - E) * (1 # 2))%Q -> (c + c == (A - E))%Q.
Proof.
  intros c A E HEc.
  assert (Hhalf : ((1 # 2) + (1 # 2))%Q == 1%Q)
    by (unfold Qeq; cbn [Qnum Qden Qplus Qmult Pos.mul]; lia).
  pose proof (Qmult_plus_distr_r (A - E)%Q (1 # 2)%Q (1 # 2)%Q) as Hstep1.
  rewrite HEc. rewrite <- Hstep1. rewrite Hhalf. rewrite Qmult_1_r.
  reflexivity.
Qed.

(* ============================================================ *)
(* S1：母定理（构造性无理性判据）                                    *)
(* ============================================================ *)

(* 尾控：n≥1 起，序列尾部 n 之后的项都在以 x_n 为心、e_n 为半径的窗内 *)
Definition lic_tail_bounded (x e : nat -> Q) : Set :=
  forall n k : nat, (1 <= n)%nat -> (n <= k)%nat ->
    QltT (Qabs ((x k - x n)%Q)) (e n).

(* 逃逸窗：每个有理数 q 都在某 n≥1 处逃出 e_n 窗（Q 层显式见证） *)
Definition lic_escape_window (x e : nat -> Q) : Set :=
  forall q : Q,
    sigT (fun n : nat => And ((1 <= n)%nat) (QltT (e n) (Qabs ((q - x n)%Q)))).

(* 窗宽消失：e_n -> 0（逐 eps 显式 N） *)
Definition lic_vanish (e : nat -> Q) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall n : nat, (N <= n)%nat -> QltT (e n) eps).

(* 柯西性推导：尾控 + 窗宽消失 ⟹ x 柯西（N 取 max N 1 避开 n=0 区） *)
Lemma lic_seq_cauchy : forall (x e : nat -> Q),
  lic_tail_bounded x e -> lic_vanish e -> cauchy x.
Proof.
  intros x e Ht Hv eps Heps.
  destruct (Hv eps Heps) as [N HN].
  exists (Nat.max N 1). intros m n Hm Hn.
  apply NatLe_drop in Hm. apply NatLe_drop in Hn.
  assert (Hm1 : (1 <= m)%nat) by lia.
  assert (Hn1 : (1 <= n)%nat) by lia.
  destruct (Nat.leb n m) eqn:Hleb.
  - apply Nat.leb_le in Hleb.
    apply (qltT_trans _ (e n)).
    + apply (Ht n m Hn1 Hleb).
    + apply HN. lia.
  - apply Nat.leb_gt in Hleb.
    apply (qltT_trans _ (e m)).
    + apply Qlt_to_QltT.
      pose proof (QltT_to_Qlt _ _ (Ht m n Hm1 (Nat.lt_le_incl _ _ Hleb))) as HH.
      rewrite <- (Qabs_Qminus (x m) (x n)) in HH.
      exact HH.
    + apply HN. lia.
Defined.

(* real_metric 逐点投影（real_abs/real_plus/real_opp/real_const 全 Defined 可归约） *)
Lemma lic_metric_proj : forall (X : Real) (q : Q) (k : nat),
  projT1 (real_metric X (real_const q)) k == Qabs ((projT1 X k - q)%Q).
Proof.
  intros X q k. unfold real_metric, real_abs, real_plus, real_opp, real_const.
  destruct X as [u Hu]. cbn [projT1]. reflexivity.
Qed.

(* ===== 母定理主件 ===== *)
(* 语义：q 若总在有限窗外逃逸而极限被窗罩住，则 X 与 q 有正间隔。        *)
Theorem lic_irrational_criterion : forall (x e : nat -> Q)
  (Ht : lic_tail_bounded x e) (Hw : lic_escape_window x e) (Hv : lic_vanish e),
  forall q : Q,
    sigT (fun c : Q => And (QltT 0 c)
      (real_lt (real_const c)
         (real_metric (existT (fun u : Qseq => cauchy u) x
                         (lic_seq_cauchy x e Ht Hv))
                      (real_const q)))).
Proof.
  intros x e Ht Hw Hv q.
  destruct (Hw q) as [n0 [Hn01 Hesc]].
  pose proof (QltT_to_Qlt _ _ Hesc) as Hesc'.
  remember (Qabs ((q - x n0)%Q)) as A eqn:HA.
  assert (Hcpos : Qlt 0 ((A - e n0) * (1 # 2))%Q).
  { apply (Qmult_lt_0_compat (A - e n0)%Q (1 # 2)%Q).
    - apply lic_qlt_0_minus. exact Hesc'.
    - unfold Qlt. cbn [Qnum Qden]. lia. }
  remember ((A - e n0) * (1 # 2))%Q as c eqn:HEc.
  assert (Hcv : (c + c == (A - e n0))%Q)
    by (apply lic_half_bridge; rewrite <- HEc; apply Qeq_refl).
  assert (HA2 : A == ((c + c) + e n0)%Q).
  { rewrite Hcv. symmetry. apply lic_qlt_minus_add_r. }
  exists c.
  split.
  - apply Qlt_to_QltT. exact Hcpos.
  - unfold real_lt.
    exists c.
    split.
    + apply Qlt_to_QltT. exact Hcpos.
    + exists n0. intros k HkN.
      apply NatLe_drop in HkN.
      pose proof (QltT_to_Qlt _ _ (Ht n0 k Hn01 HkN)) as Ht0'.
      assert (Hpre : (q - x n0)%Q == ((q - x k) + (x k - x n0))%Q)
        by exact (lic_qlt_tri_decomp q (x n0) (x k)).
      assert (Htri : Qle (Qabs ((q - x n0)%Q))
                         (Qabs ((q - x k)%Q) + Qabs ((x k - x n0)%Q))).
      { pose proof (Qabs_triangle ((q - x k)%Q) ((x k - x n0)%Q)) as HT.
        apply (Qle_trans (Qabs ((q - x n0)%Q))
                 (Qabs (((q - x k) + (x k - x n0))%Q))).
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. setoid_rewrite Hpre. apply Qeq_refl.
        - exact HT. }
      rewrite <- HA in Htri.
      remember (Qabs ((q - x k)%Q)) as Bk eqn:HB.
      remember (Qabs ((x k - x n0)%Q)) as Ek eqn:HE.
      assert (Hlt1 : Qlt (Bk + Ek) (Bk + e n0))
        by (apply (lic_qlt_add_l Bk Ek (e n0)); exact Ht0').
      assert (Hlt2 : Qlt A (Bk + e n0))
        by (apply (Qle_lt_trans A (Bk + Ek)); [exact Htri | exact Hlt1]).
      rewrite HA2 in Hlt2.
      setoid_rewrite (Qplus_comm (c + c) (e n0)) in Hlt2.
      setoid_rewrite (Qplus_comm Bk (e n0)) in Hlt2.
      assert (Hle3 : Qle (c + c) Bk).
      { apply (lic_qlt_dec_le (c + c) Bk).
        intro Hcontra.
        assert (Hbad : Qlt (Bk + e n0) ((c + c) + e n0))
          by (apply (lic_qlt_add_r Bk (c + c) (e n0)); exact Hcontra).
        setoid_rewrite (Qplus_comm (c + c) (e n0)) in Hbad.
        setoid_rewrite (Qplus_comm Bk (e n0)) in Hbad.
        exact (Qlt_not_eq (e n0 + Bk) (e n0 + Bk)
                 (Qlt_trans (e n0 + Bk) (e n0 + (c + c)) (e n0 + Bk)
                    Hbad Hlt2) (Qeq_refl (e n0 + Bk))). }
      destruct (Qlt_bool (c + c) Bk) eqn:Ecb.
      * assert (Hlt3 : Qlt (c + c) Bk) by exact (lic_qlt_bool_true _ _ Ecb).
        assert (Hfin : Qlt c (Bk - c)%Q).
        { apply (lic_qlt_add_r_cancel_r c (Bk - c) c).
          rewrite (lic_qlt_minus_add_r Bk c). exact Hlt3. }
        assert (HPr : projT1 (real_metric (existT (fun u : Qseq => cauchy u) x
                                     (lic_seq_cauchy x e Ht Hv)) (real_const q)) k
                    == Qabs ((x k - q)%Q))
          by apply lic_metric_proj.
        apply (lic_qltt_comp_r ((Qabs ((q - x k)%Q)) - c)
                 (projT1 (real_metric (existT (fun u : Qseq => cauchy u) x
                                        (lic_seq_cauchy x e Ht Hv)) (real_const q)) k
                  - projT1 (real_const c) k) c).
        -- rewrite (qeqT_imp_qeq _ _ (real_const_proj c k)). rewrite HPr.
           rewrite (Qabs_Qminus q (x k)). reflexivity.
        -- rewrite HB in Hfin. apply Qlt_to_QltT. exact Hfin.
      * exfalso.
        pose proof (lic_qlt_bool_false_le (c + c) Bk Ecb) as Hle4.
        assert (Hle5 : Qle (Bk + e n0) ((c + c) + e n0))
          by (apply (Qplus_le_compat Bk (c + c) (e n0) (e n0));
              [exact Hle4 | apply Qle_refl]).
        setoid_rewrite (Qplus_comm Bk (e n0)) in Hle5.
        setoid_rewrite (Qplus_comm (c + c) (e n0)) in Hle5.
        exact (Qlt_not_eq (e n0 + (c + c)) (e n0 + (c + c))
                 (Qlt_le_trans (e n0 + (c + c)) (e n0 + Bk) (e n0 + (c + c))
                    Hlt2 Hle5) (Qeq_refl (e n0 + (c + c))%Q)).
Qed.

(* ============================================================ *)
(* S2：e 实例的 Q 层供给（尾控 + 窗宽消失）                            *)
(* ============================================================ *)

(* 尾部尾和：Σ_{i=1}^{K} 1/(n+i)! *)
Fixpoint lic_rsum (n K : nat) : Q :=
  match K with
  | 0%nat => 0%Q
  | Datatypes.S k => lic_rsum n k + (1%Q / q_fact (n + Datatypes.S k))
  end.

Lemma lic_rsum_ge0 : forall n K : nat, Qle 0%Q (lic_rsum n K).
Proof.
  intros n K. induction K as [|k IH].
  - cbn [lic_rsum]. apply Qle_refl.
  - cbn [lic_rsum].
    assert (Hp : Qle 0 (1%Q / q_fact (n + Datatypes.S k))).
    { pose proof (QltT_to_Qlt _ _ (q_fact_pos (n + Datatypes.S k))) as Hpos.
      rewrite (qeqT_imp_qeq _ _ (sif_qfact_Z (n + Datatypes.S k))) in Hpos.
      unfold Qlt in Hpos. cbn [Qnum Qden] in Hpos.
      rewrite (qeqT_imp_qeq _ _ (sif_qfact_Z (n + Datatypes.S k))).
      unfold Qle, Qdiv, Qinv.
      destruct (Z.of_nat (fact (n + Datatypes.S k))) as [|pp|pp];
        cbn in *; lia. }
    apply (Qplus_le_compat 0%Q (lic_rsum n k) 0%Q
             (1%Q / q_fact (n + Datatypes.S k))); [exact IH | exact Hp].
Qed.

(* exp_series 差 = 尾和（bno_exp_series_succ_frac 递推 + 归纳） *)
Lemma lic_exp_diff : forall (n K : nat),
  exp_series (n + K) 1%Q - exp_series n 1%Q == lic_rsum n K.
Proof.
  intros n K. induction K as [|k IH].
  - rewrite Nat.add_0_r. cbn [lic_rsum]. unfold Qminus. ring.
  - assert (Hadv : (n + Datatypes.S k)%nat = Datatypes.S (n + k)) by lia.
    rewrite Hadv. rewrite (qeqT_imp_qeq _ _ (bno_exp_series_succ_frac (n + k))).
    cbn [lic_rsum]. replace (n + Datatypes.S k)%nat with (Datatypes.S (n + k))%nat by lia.
    assert (Hring : ((exp_series (n + k)%nat 1%Q + 1%Q / q_fact (Datatypes.S (n + k)%nat))%Q
                     - exp_series n 1%Q)%Q
                    == ((exp_series (n + k)%nat 1%Q - exp_series n 1%Q)%Q
                        + (1%Q / q_fact (Datatypes.S (n + k)%nat)))%Q).
    { unfold Qminus. ring. }
    rewrite Hring. rewrite IH. reflexivity.
Qed.

(* 核心归纳：C·(A·Σ) + A ≤ C，其中 A=n!、C=(n+K)!（r_{K+1}=r_K/(n+K+1) 倍增形） *)
Lemma lic_core : forall (n K : nat), (1 <= n)%nat ->
  Qle (q_fact (n + K) * (q_fact n * lic_rsum n K) + q_fact n) (q_fact (n + K)).
Proof.
  intros n K Hn. induction K as [|k IH].
  - rewrite Nat.add_0_r. cbn [lic_rsum].
    rewrite Qmult_0_r. rewrite Qmult_0_r. rewrite Qplus_0_l. apply Qle_refl.
  - assert (Hadv : (n + Datatypes.S k)%nat = Datatypes.S (n + k)) by lia.
    rewrite Hadv.
    cbn [lic_rsum].
    replace (n + Datatypes.S k)%nat with (Datatypes.S (n + k))%nat by lia.
    assert (HCdef : q_fact (Datatypes.S (n + k))
                    == ((Z.of_nat (Datatypes.S (n + k)) # 1) * q_fact (n + k))%Q)
      by reflexivity.
    remember (Z.of_nat (Datatypes.S (n + k))) as z eqn:Ezz.
    remember (q_fact n) as A eqn:EA.
    remember (q_fact (n + k)) as B eqn:EB.
    remember (lic_rsum n k) as L eqn:EL.
    assert (Hz2 : (2 <= z)%Z) by (rewrite Ezz; lia).
    assert (Hzc : Qle (2%Q) ((z # 1)%Q)).
    { unfold Qle. cbn [Qnum Qden]. rewrite Ezz. lia. }
    assert (Hzpos : Qle 0%Q ((z # 1)%Q)).
    { unfold Qle. cbn [Qnum Qden]. rewrite Ezz. lia. }
    assert (HCdef2 : q_fact (Datatypes.S (n + k)) == ((z # 1) * B)%Q)
      by exact HCdef.
    (* 目标：((z#1)*B) * (A * (L + V)) + A ≤ (z#1)*B，V := 1/((z#1)*B) *)
    rewrite HCdef2.
    remember (1%Q / ((z # 1) * B)) as V eqn:EV.
    assert (HVX : (V * ((z # 1) * B))%Q == 1%Q).
    { rewrite EV, Qmult_comm. apply qeqT_imp_qeq. apply bno_mul_div_self.
      intro Hc. apply (Qlt_not_eq 0%Q _ (QltT_to_Qlt _ _ (q_fact_pos (Datatypes.S (n + k))))).
      rewrite <- HCdef2 in Hc. apply Qeq_sym. exact Hc. }
    assert (HXAV : ((z # 1) * B) * (A * V)%Q == A%Q).
    { rewrite (Qmult_comm A V).
      rewrite (Qmult_assoc ((z # 1) * B) V A).
      rewrite (Qmult_comm ((z # 1) * B) V).
      rewrite HVX. apply Qmult_1_l. }
    assert (HAle : Qle A (A + A)%Q).
    { apply (Qle_trans A (0 + A)%Q (A + A)%Q).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT, Qeq_sym, Qplus_0_l.
      - apply (Qplus_le_compat 0%Q A A%Q A%Q);
          [rewrite EA; exact (Qlt_le_weak 0%Q _ (QltT_to_Qlt _ _ (q_fact_pos n))) | apply Qle_refl]. }
    assert (HAAeq : (A + A == 2%Q * A)%Q) by ring.
    assert (H2A : Qle (A + A)%Q ((z # 1) * A)%Q).
    { rewrite HAAeq. apply Qmult_le_compat_r;
        [exact Hzc | rewrite EA; exact (Qlt_le_weak 0%Q _ (QltT_to_Qlt _ _ (q_fact_pos n)))]. }
    assert (HIH : Qle (((z # 1) * B) * (A * L) + ((z # 1) * A))%Q
                       ((z # 1) * B)%Q).
    { pose proof (Qmult_le_compat_r (B * (A * L) + A) B (z # 1) IH Hzpos) as Hm.
      setoid_rewrite (Qmult_comm (B * (A * L) + A) (z # 1)) in Hm.
      setoid_rewrite (Qmult_comm B (z # 1)) in Hm.
      setoid_rewrite (Qmult_plus_distr_r (z # 1) (B * (A * L)) A) in Hm.
      setoid_rewrite (Qmult_assoc (z # 1) B (A * L)) in Hm.
      exact Hm. }
    rewrite (Qmult_plus_distr_r A L V).
    rewrite (Qmult_plus_distr_r ((z # 1) * B) (A * L) (A * V)).
    setoid_rewrite HXAV.
    setoid_rewrite <- (Qplus_assoc ((z # 1) * B * (A * L)) A A).
    apply (lic_le_add_le ((z # 1) * B * (A * L)) ((z # 1) * A) ((z # 1) * B)
             (A + A)%Q).
    + exact HIH.
    + exact H2A.
Qed.

(* 形状重排：c*(a*b) < c ⟹ (c*a)*b < c*1（destruct-Q 机械模式） *)
Lemma lic_shuffle_lt : forall c a b : Q,
  Qlt (c * (a * b)) c -> Qlt ((c * a) * b) (c * 1).
Proof.
  intros [cn cd] [an ad] [bn bd]. unfold Qlt in *.
  cbn [Qnum Qden Qmult Qplus] in *.
  destruct cn as [|pn|pn]; destruct an as [|pm|pm]; destruct bn as [|pbn|pbn];
    cbn in *; try lia; nia.
Qed.




(* 尾和 < 1/n!（n ≥ 1） *)
(* 辅助：1/x 的正性 *)
Lemma lic_inv_pos : forall x : Q, Qlt 0%Q x -> Qlt 0%Q (1%Q / x).
Proof.
  intros [xn xd] Hx. unfold Qlt in *. cbn [Qnum Qden] in *.
  destruct xn; cbn in *; try lia.
Qed.

(* 尾和 < 1/n!（n ≥ 1） *)
Lemma lic_rsum_lt : forall (n K : nat), (1 <= n)%nat ->
  Qlt (lic_rsum n K) (1%Q / q_fact n).
Proof.
  intros n K Hn.
  pose proof (lic_core n K Hn) as HC.
  pose proof (QltT_to_Qlt _ _ (q_fact_pos n)) as HA.
  pose proof (QltT_to_Qlt _ _ (q_fact_pos (n + K))) as HC2.
  (* 严格化：qf·(n!·X) < qf（加 n! 严格增，再 ≤ qf，n! > 0） *)
  assert (Hsa : Qlt (q_fact (n + K) * (q_fact n * lic_rsum n K) + 0%Q)
                     (q_fact (n + K) * (q_fact n * lic_rsum n K) + q_fact n)).
  { apply (proj2 (Qplus_lt_r 0%Q (q_fact n)
                   (q_fact (n + K) * (q_fact n * lic_rsum n K)))).
    exact HA. }
  rewrite Qplus_0_r in Hsa.
  assert (Hs1 : Qlt (q_fact (n + K) * (q_fact n * lic_rsum n K))
                     (q_fact (n + K)))
    by (apply (Qlt_le_trans _ _ _ Hsa HC)).
  (* 除以 (n+K)!：n!·X < 1 *)
  assert (Hs2 : Qlt (q_fact n * lic_rsum n K) 1%Q).
  { apply (proj1 (Qmult_lt_r (q_fact n * lic_rsum n K) 1%Q (q_fact (n + K)) HC2)).
    rewrite (Qmult_comm (q_fact n * lic_rsum n K) (q_fact (n + K))).
    rewrite (Qmult_1_l (q_fact (n + K))).
    exact Hs1. }
  (* 除以 n!：X < 1/n! *)
  apply (proj1 (Qmult_lt_r (lic_rsum n K) (1%Q / q_fact n) (q_fact n) HA)).
  rewrite (Qmult_comm (lic_rsum n K) (q_fact n)).
  rewrite (Qmult_comm (1%Q / q_fact n) (q_fact n)).
  assert (Hnz : ~ (q_fact n == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q _ HA); apply Qeq_sym; exact Hc).
  rewrite (qeqT_imp_qeq _ _ (bno_mul_div_self (q_fact n) Hnz)).
  exact Hs2.
Qed.

(* 尾控实例：|exp_series k 1 − exp_series n 1| = 尾和 < 1/n!（n ≥ 1）
   （QltT 目标先降 Qlt Prop 层再做 Qeq 换元——lic_qltt_comp_r 同款 idiom） *)
Definition lic_tail_e : lic_tail_bounded (fun n => exp_series n 1)
                                         (fun n => 1%Q / q_fact n).
Proof.
  intros n k Hn1 Hnk.
  remember (k - n)%nat as K eqn:HK.
  assert (Hk : k = (n + K)%nat) by (rewrite HK; lia).
  rewrite Hk.
  pose proof (lic_rsum_lt n K Hn1) as Hlt0.
  rewrite <- (lic_exp_diff n K) in Hlt0.
  pose proof (lic_rsum_ge0 n K) as Hge.
  rewrite <- (lic_exp_diff n K) in Hge.
  apply Qlt_to_QltT.
  rewrite (Qabs_pos (exp_series (n + K) 1%Q - exp_series n 1%Q)%Q Hge).
  exact Hlt0.
Defined.

(* 窗宽消失实例：1/n! -> 0（显式 N := den(eps)+1：n > den ⟹ 1/n ≤ 1/n! < eps；
   Q 层链：1/eps ≤ den(eps) < n ≤ n! ，末步 Qinv_lt_contravar 转置） *)
Definition lic_vanish_e : lic_vanish (fun n => 1%Q / q_fact n).
Proof.
  intro eps. destruct eps as [pn pd].
  intro Heps.
  pose proof (QltT_to_Qlt 0%Q (pn # pd) Heps) as Heps0.
  pose proof Heps0 as Heps'.
  unfold Qlt in Heps'. cbn [Qnum Qden] in Heps'.
  assert (Hnum : (0 < pn)%Z) by lia.
  pose proof (sif_posZ pd) as Hden.
  assert (HpdQ : Qle (Qinv (pn # pd)) ((Z.pos pd) # 1)).
  { unfold Qinv, Qle. destruct pn as [|pp|pp]; cbn in *; try lia; nia. }
  exists (Datatypes.S (Z.to_nat (Z.pos pd))).
  intros n Hn.
  assert (Hn1 : (1 <= n)%nat) by lia.
  assert (Hdn : (Z.pos pd < Z.of_nat n)%Z) by lia.
  assert (Hfn : (n <= fact n)%nat) by (apply lic_fact_ge_self; exact Hn1).
  assert (HltB : Qlt ((Z.pos pd) # 1) ((Z.of_nat n) # 1)).
  { unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (HgeA : Qle ((Z.of_nat n) # 1) ((Z.of_nat (fact n)) # 1)).
  { unfold Qle. cbn [Qnum Qden]. lia. }
  assert (HposA : Qlt 0 ((Z.of_nat (fact n)) # 1)).
  { unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (Hmid : Qlt ((Z.pos pd) # 1) ((Z.of_nat (fact n)) # 1))
    by (apply (Qlt_le_trans ((Z.pos pd) # 1) ((Z.of_nat n) # 1)
                 ((Z.of_nat (fact n)) # 1)); assumption).
  assert (Hk : Qlt (Qinv (pn # pd)) ((Z.of_nat (fact n)) # 1))
    by (apply (Qle_lt_trans (Qinv (pn # pd)) ((Z.pos pd) # 1)
                 ((Z.of_nat (fact n)) # 1)); assumption).
  apply Qlt_to_QltT.
  rewrite (qeqT_imp_qeq _ _ (sif_qfact_Z n)).
  unfold Qdiv.
  rewrite <- (Qinv_involutive (pn # pd)).
  rewrite (Qmult_1_l (Qinv ((Z.of_nat (fact n)) # 1))).
  apply (proj1 (Qinv_lt_contravar (Qinv (pn # pd)) ((Z.of_nat (fact n)) # 1)
                  (Qinv_lt_0_compat _ Heps0) HposA)).
  exact Hk.
Defined.
(* S3：e 实例的窗口供给（见证 n ≥ 1 升级：枚举 + 平移窗 + 零点两步逃逸）   *)
(* ============================================================ *)

(* sif 逃逸见证的窗形式换算：1 < |n!·(q − s_n)| ⟺ 1/n! < |q − s_n| *)
Lemma lic_qwin_convert : forall (n : nat) (q : Q),
  QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q)) ->
  QltT (1%Q / q_fact n) (Qabs ((q - exp_series n 1)%Q)).
Proof.
  intros n q Hw. apply Qlt_to_QltT. apply QltT_to_Qlt in Hw.
  rewrite Qabs_Qmult in Hw.
  assert (HAp : Qabs (q_fact n) == q_fact n).
  { apply Qabs_pos. apply (Qlt_le_weak 0%Q _ (QltT_to_Qlt _ _ (q_fact_pos n))). }
  rewrite HAp in Hw.
  assert (Hpos_inv : Qlt 0 (1%Q / q_fact n)).
  { pose proof (Qinv_lt_0_compat (q_fact n) (QltT_to_Qlt _ _ (q_fact_pos n))) as Hi.
    rewrite <- (Qmult_1_l (Qinv (q_fact n))) in Hi.
    unfold Qdiv. exact Hi. }
  assert (Hwf : Qlt (1%Q * (1%Q / q_fact n))
                     ((q_fact n * Qabs ((q - exp_series n 1)%Q))
                      * (1%Q / q_fact n))).
  { apply (Qmult_lt_compat_r 1%Q (q_fact n * Qabs ((q - exp_series n 1)%Q))
             (1%Q / q_fact n) Hpos_inv Hw). }
  rewrite (Qmult_comm (q_fact n) (Qabs ((q - exp_series n 1)%Q))) in Hwf.
  rewrite <- (Qmult_assoc (Qabs ((q - exp_series n 1)%Q)) (q_fact n)
               (1%Q / q_fact n)) in Hwf.
  assert (Hnzw : ~ (q_fact n == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q _ (QltT_to_Qlt _ _ (q_fact_pos n))); apply Qeq_sym; exact Hc).
  rewrite (qeqT_imp_qeq _ _ (bno_mul_div_self (q_fact n) Hnzw)) in Hwf.
  rewrite Qmult_1_r in Hwf.
  rewrite Qmult_1_l in Hwf.
  exact Hwf.
Qed.

(* 平移窗引理（sif_window 的 [1,2b+2] 克隆）：d_k 序列若在 k ∈ [1,2b+2]
   全程非零且 |d_k| ≤ b，则矛盾。负支一步逃逸（k≥1 保系数 ≥2）、
   正支回溯窗 (2b+2)·d_{2b+1} = d_{2b+2} + b ≤ 2b 与 d_{2b+1} ≥ 1 矛盾。 *)
Lemma lic_window_shift : forall q : Q,
  (forall k : nat, (1 <= k)%nat ->
     (k <= Z.to_nat (2 * Z.pos (Qden q) + 2))%nat ->
     sif_d q k <> 0%Z /\
     (sif_d q k <= Z.pos (Qden q) /\ - Z.pos (Qden q) <= sif_d q k))%Z -> False.
Proof.
  intros q Hall.
  assert (Hbq : (0 < Z.pos (Qden q))%Z).
  { apply (proj1 (Z.ltb_lt 0%Z (Z.pos (Qden q)))).
    destruct (sif_posZ (Qden q)); reflexivity. }
  assert (Hsucc : forall n : nat,
    sif_d q (Datatypes.S n) =
    (Z.of_nat (Datatypes.S n) * sif_d q n - Z.pos (Qden q))%Z)
    by (intro n; destruct (sif_d_succ q n); reflexivity).
  assert (Hpos : forall k : nat, (1 <= k)%nat ->
                 (k < Z.to_nat (2 * Z.pos (Qden q) + 2))%nat ->
                 (0 < sif_d q k)%Z).
  { intros k Hk1 HkN.
    destruct (Z_le_gt_dec 0 (sif_d q k)) as [Hle | Hgt].
    - destruct (Z.eq_dec (sif_d q k) 0) as [Heq | Hne].
      + exfalso. destruct (Hall k Hk1 (Nat.lt_le_incl _ _ HkN)) as [Hne2 _].
        congruence.
      + lia.
    - exfalso.
      assert (Hge2 : (2 <= Z.of_nat (Datatypes.S k))%Z) by lia.
      assert (Hprod : (Z.of_nat (Datatypes.S k) * sif_d q k <= 2 * sif_d q k)%Z)
        by nia.
      assert (Hdn : (sif_d q (Datatypes.S k) < - Z.pos (Qden q))%Z)
        by (rewrite Hsucc; lia).
      destruct (Hall (Datatypes.S k) ltac:(lia) ltac:(lia)) as [_ [_ Hubl]].
      lia. }
  assert (HN1 : (1 <= Z.to_nat (2 * Z.pos (Qden q) + 2))%nat) by lia.
  assert (HzN : (Z.of_nat (Z.to_nat (2 * Z.pos (Qden q) + 2))
                 = 2 * Z.pos (Qden q) + 2)%Z) by lia.
  assert (Hback : (Z.of_nat (Z.to_nat (2 * Z.pos (Qden q) + 2))
                  * sif_d q (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 2)))
                  <= 2 * Z.pos (Qden q))%Z).
  { assert (HSN : Datatypes.S (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 2)))
                  = Z.to_nat (2 * Z.pos (Qden q) + 2)) by lia.
    pose proof (Hsucc (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 2)))) as HH.
    rewrite HSN in HH.
    destruct (Hall (Z.to_nat (2 * Z.pos (Qden q) + 2)) HN1
                   (Nat.le_refl _)) as [_ [Hub _]].
    lia. }
  assert (Hpd : (0 < sif_d q (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 2))))%Z)
    by (apply Hpos; [lia | lia]).
  (* 终局矛盾：d_{N-1} ≥ 1 ⟹ N·d_{N-1} ≥ N = 2b+2 > 2b ≥ N·d_{N-1} *)
  assert (Hd1 : (1 <= sif_d q (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 2))))%Z).
  { pose proof (Hpos (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 2)))
                  ltac:(lia) ltac:(lia)) as Hpp.
    lia. }
  assert (Hzc : (2 * Z.pos (Qden q) + 2
                  <= Z.of_nat (Z.to_nat (2 * Z.pos (Qden q) + 2))
                  * sif_d q (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 2))))%Z).
  { rewrite HzN. nia. }
  lia.
Qed.

(* Type 层有界枚举（n 从 1 起；判定件复用 sif_dec_pt） *)
Fixpoint lic_enum (q : Q) (K : nat) :
  (sigT (fun n : nat => sigT (fun _ : (1 <= n)%nat => sigT (fun _ : (n <= K)%nat =>
            QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))))))
  + (forall n : nat, (1 <= n)%nat -> (n <= K)%nat ->
       QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q)) -> Empty_set) :=
  match K with
  | O => inr (fun (n : nat) (_ : (1 <= n)%nat) (Hk : (n <= 0)%nat)
                 (_ : QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))) =>
               False_rect _ ltac:(lia))
  | Datatypes.S K' =>
      match lic_enum q K' with
      | inl w =>
          inl (match w with
               | existT _ n0 (existT _ H1 (existT _ Hk Hc)) =>
                   existT _ n0 (existT _ H1 (existT _ (Nat.le_le_succ_r _ _ Hk) Hc))
               end)
      | inr g =>
          match sif_dec_pt q (Datatypes.S K') with
          | inl c =>
              inl (existT _ (Datatypes.S K')
                     (existT _ (proj1 (Nat.succ_le_mono 0 K') (Nat.le_0_l K'))
                             (existT _ (Nat.le_refl (Datatypes.S K')) c)))
          | inr c =>
              inr (fun (n : nat) (H1 : (1 <= n)%nat) (Hn : (n <= Datatypes.S K')%nat)
                       (Hw : QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))) =>
                match Nat.eq_dec n (Datatypes.S K') with
                | left E => c (eq_rect n
                     (fun n1 : nat =>
                        QltT 1%Q (Qabs ((q_fact n1 * (q - exp_series n1 1)%Q)%Q)))
                     Hw (Datatypes.S K') E)
                | right E => g n H1 ltac:(lia) Hw
                end)
          end
      end
  end.

(* e 实例窗口供给：每个 q 有 n ≥ 1 使 1/n! < |q − s_n|。
   枚举失败支由平移窗 + 零点两步逃逸（复用 sif_zero_escape/sif_hit_of_dd/
   sif_abs_frac）导出矛盾——构造性 exfalso（Empty_set 消去）。 *)
Lemma lic_witness_e : lic_escape_window (fun n => exp_series n 1)
                                        (fun n => 1%Q / q_fact n).
Proof.
  intro q. destruct (lic_enum q (Z.to_nat (2 * Z.pos (Qden q) + 2) + 2))
    as [w | Hno].
  - destruct w as [n [Hn1 [HK Hw]]].
    exists n. split; [exact Hn1 | exact (lic_qwin_convert n q Hw)].
  - exfalso. apply (lic_window_shift q).
    intros k H1k HkK.
    assert (HkK2 : (k <= Z.to_nat (2 * Z.pos (Qden q) + 2) + 2)%nat) by lia.
    assert (Hnz : sif_d q k <> 0%Z).
    { intro Hz.
      assert (Hzc : (Z.pos (Qden q)
                       < Z.abs (sif_d q (Datatypes.S (Datatypes.S k))))%Z).
      { apply (proj1 (Z.ltb_lt (Z.pos (Qden q))
                 (Z.abs (sif_d q (Datatypes.S (Datatypes.S k)))))).
        destruct (sif_zero_escape q k Hz); reflexivity. }
      destruct (Hno (Datatypes.S (Datatypes.S k)) ltac:(lia) ltac:(lia)
                 (sif_hit_of_dd q (Datatypes.S (Datatypes.S k)) Hzc)). }
    split; [exact Hnz |].
    destruct (Qlt_bool 1%Q (Qabs ((q_fact k * (q - exp_series k 1)%Q)%Q)))
      eqn:Hqb.
    + exfalso. destruct (Hno k H1k HkK2 (sif_eq_id _ _ Hqb)).
    + assert (Hnb : ~ Qlt 1%Q (Qabs ((q_fact k * (q - exp_series k 1)%Q)%Q))).
      { intro Hlt.
        assert (Hct : Qcompare 1%Q (Qabs ((q_fact k * (q - exp_series k 1)%Q)%Q))
                      = Lt) by (apply (proj1 (Qlt_alt _ _)); exact Hlt).
        unfold Qlt_bool in Hqb. rewrite Hct in Hqb. discriminate. }
      rewrite (qeqT_imp_qeq _ _ (sif_abs_frac q k)) in Hnb.
      unfold Qlt in Hnb. cbn [Qnum Qden] in Hnb. lia.
Defined.

(* ============================================================ *)
(* S4：e 实例回验装配（真走母定理）+ 提取检验 + 公理面自审                 *)
(* ============================================================ *)

(* e 的无理性（判据形）：X := lim Σ_{j≤n} 1/j!，对任意有理数 q 存在
   Q 层正分离常数 c 使 real_const c < |X − q|。 *)
Theorem lic_e_irrational_criterion : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u)
                            (fun n => exp_series n 1)
                            (lic_seq_cauchy (fun n => exp_series n 1)
                                            (fun n => 1%Q / q_fact n)
                                            lic_tail_e lic_vanish_e))
       (real_const q)))).
Proof.
  intro q.
  exact (lic_irrational_criterion (fun n => exp_series n 1)                                  (fun n => 1%Q / q_fact n)                                  lic_tail_e lic_witness_e lic_vanish_e q).
Qed.

From Stdlib Require Import Extraction.
Separate Extraction lic_irrational_criterion lic_e_irrational_criterion
  lic_seq_cauchy lic_tail_e lic_vanish_e lic_witness_e lic_enum
  lic_window_shift lic_rsum lic_core.

Print Assumptions lic_irrational_criterion.
Print Assumptions lic_e_irrational_criterion.
