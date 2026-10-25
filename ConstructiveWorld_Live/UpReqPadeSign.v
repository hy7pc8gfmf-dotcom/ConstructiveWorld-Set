(* ConstructiveWorld-Set — sign lemmas for the signed Pade approximation. *)

(** * UpReqPadeSign: station values and sign propagation for the Pade chain..

    Mission.  Closed-form evaluations of the Pade numerator and denominator at the
 stations zero and one ([pds_den0_one], [pds_sum2], [pds_c10],
 [pds_c11], [pds_den1_expl]) and the sign propagation lemma
 [pds_qlt0_eq_r].

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Lia].
      Requires the base modules [S01_BaseRing] up to [S08_RealMainlineDPO]
      of this development.
      Requires [UpReqPadeQLeg] of this development.

    References.  This development, UpReqPadeSign.v, the baseline module in
 ConstructiveWorld-Main whose statement names are carried over here
 verbatim (statement-face Set-carrier completion: [==] equalities
 moved to [QeqT], the [Qlt] conclusion of [pds_qlt0_eq_r] to [QltT]).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqPadeSign.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)

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
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqPadeExp.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

Section PadeSignQ.

(* ===== S1 保底：n=0 具体例 ===== *)

(* n=0 分母恒一：sum_upto 1 只存 k=0 项，且 q_pow 递归于 nat 指标
   （不触 x），q_pow x 0 == 1 对变元 x 依指标归约——左端除 x 的
   指标位外全闭，vm_compute 端到端归一。 *)
Lemma pds_den0_one : forall x : Q, QeqT (pade_den 0 x) 1%Q.
Proof. intro x. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* S1 主张：Q_0(x) 恒正（Qlt_bool 闭式计算直绿，qltT_0_1 同款）。 *)
Lemma pds_den0_pos : forall x : Q, QltT 0 (pade_den 0 x).
Proof. intro x. unfold QltT. vm_compute. reflexivity. Qed.

(* ===== S2 保底主件：n=1 分母正性 ===== *)

(* 两项和分裂：sum_upto 2 f == f 0 + f 1（高位在后的左折叠，
   iota 两步 + Qplus_0_l；f 的指数位全 %nat 防 Q_scope 吞字面量）。 *)
Lemma pds_sum2 : forall f : nat -> Q,
  QeqT (sum_upto (Datatypes.S 1%nat) f) (f 0%nat + f 1%nat).
Proof.
  intro f. apply qeq_imp_qeqT. cbn [sum_upto]. cbv beta. ring.
Qed.

(* n=1 闭式系数锚（PC 锚件 pade_den_1_half 同款 vm_compute 口径：
   Nat.sub 截断坑或交错符号写反即红）。 *)
Lemma pds_c10 : QeqT (pade_coeff 1 0%nat) 1%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Lemma pds_c11 : QeqT (pade_coeff 1 1%nat) (1#2)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 显式形：Q_1(x) == 1 + (−1)·(1/2)·x——两项交错和的语义面。
   分裂 + q_pow 指标位 change + 系数锚改写 + ring 完成
   （Qopp 原子挂乘积结构，ring 直绿不触 判例）。 *)
Lemma pds_den1_expl : forall x : Q, QeqT (pade_den 1 x) (1%Q + (- (1#2)%Q) * x).
Proof.
  intro x. apply qeq_imp_qeqT. unfold pade_den.
  assert (Hs2 := pds_sum2 (fun k : nat => q_pow (- 1)%Q k * (pade_coeff 1 k * q_pow x k))).
  apply qeqT_imp_qeq in Hs2.
  setoid_rewrite Hs2. cbv beta.
  change (q_pow (- 1)%Q 0%nat) with 1%Q.
  change (q_pow (- 1)%Q 1%nat) with (-1)%Q.
  change (q_pow x 0%nat) with 1%Q.
  change (q_pow x 1%nat) with (x * 1)%Q.
  assert (Hc10 := pds_c10). apply qeqT_imp_qeq in Hc10.
  setoid_rewrite Hc10.
  assert (Hc11 := pds_c11). apply qeqT_imp_qeq in Hc11.
  setoid_rewrite Hc11.
  ring.
Qed.

(* Qeq 右换桥（本件最小传桥接引理）：a == b 时 0<a 传 0<b。
   AA12 肢化：语句面不变，证明体退化为自建 Q 单调肢一跳
   （UpReqPadeQLeg.pql_qlt0_eq_r，Z 乘法单调显式装配 + lia，
   根除 Psatz/micromega 环境闭包）。 *)
Lemma pds_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> QltT 0 b.
Proof.
  intros a b Hab Ha.
  exact (pql_qlt0_eq_r a b Hab Ha).
Qed.

(* 主件：0 < x < 2 ⟹ 0 < Q_1(x) = 1 − x/2。
   证法：传桥到显式乘积形 (1/2)·(2−x)——双正乘 Qmult_lt_0_compat，
   0<2−x 由 Qlt_minus_iff（p<q ↔ 0<q+−p，stdlib:1127 实名）从 x<2
*)
Lemma pds_den1_pos : forall x : Q,
  QltT 0 x -> QltT x (2#1) -> QltT 0 (pade_den 1 x).
Proof.
  intros x H0 H2.
  apply QltT_to_Qlt in H2.
  apply (pds_qlt0_eq_r ((1#2)%Q * (2 + - x)%Q) (pade_den 1 x)).
  - apply (Qeq_trans ((1#2)%Q * (2 + - x)%Q) (1%Q + (- (1#2)%Q) * x) (pade_den 1 x)).
    + ring.
    + apply Qeq_sym. exact (qeqT_imp_qeq _ _ (pds_den1_expl x)).
  - apply Qmult_lt_0_compat.
    + unfold Qlt. simpl. lia.
    + apply (proj1 (Qlt_minus_iff x (2#1))). exact H2.
Qed.

(* ===== S3 加分：锚交叉 ===== *)

(* Q_1(1/2) > 0：与 PC 锚 pade_den_1_half（Q_1(1/2) == 3/4）
   数值核对——Qlt_bool 0 (3/4) 闭式归 true，vm_compute 直绿。 *)
Lemma pds_den1_half : QltT 0 (pade_den 1 (1#2)).
Proof. unfold QltT. vm_compute. reflexivity. Qed.

(* ===== 显式假设登记（通用 n 版 den_pos，禁强造） =====
   通用 n 的 den_pos 实例化图（下一批，30 分钟预算内诚实显式假设）：
     den(x) := altsum (fun k => pade_coeff n k * q_pow x k) (n+1)
     （PC2 引擎出口，UpReqAltSumPos.v）；
   逐项非负（pade_coeff_pos）+ 相邻递减
     QleT (c_{k+1} x^{k+1}) (c_k x^k)（0<=x 段）
   喂 altsum_nonneg（QleT 假设面）/ altsum_nonneg_leT（QleT' 面）
   得 QleT' 0 (den x)；首对严格 + 项数 >= 2 时经 altsum_pos_strict
   升 QltT 0（本件 n=1 即其手工实例）；le_head 备 <= c_0 用。
   依赖缺口：相邻递减需 c_k x^k 单调面（x^k/x^{k+1} 比式 + 系数比
   (k+1)(2n-k)/(2(k+1)(n-k)) 型），库内尚无现成件，下一批建。
   本件三引理即 n=0/n=1 手工实例，可作通用件回来核对的锚。 *)

End PadeSignQ.

Print Assumptions pds_qlt0_eq_r.
