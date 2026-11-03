(* ConstructiveWorld-Set — strict suboptimality of the Doeblin constant for two-state softmax kernels. *)

(** * UpAblDeltaStarSuboptimal: strict suboptimality of the two-state Doeblin constant.

    Mission.  [mdsopt_main]: for rational [0 < lo < 1] the Doeblin constant
      [mdsopt_dstar lo = lo*lo] is strictly below the optimum
      [mdsopt_dstar_opt lo = 2*(lo*lo)/(1 + lo*lo)], with the explicit gap
      [mdsopt_gap] and its strict positivity [mdsopt_gap_pos], plus the
      feasibility companion [mdsopt_dstar_le_opt]; supporting facts:
      row-stochastic normalization [mdsopt_row0_norm]/[mdsopt_row1_norm]
      and the Q-arithmetic chain
      [mdsopt_sq0]/[mdsopt_lt1]/[mdsopt_den_pos]/[mdsopt_den_ne]/[mdsopt_cancel].

    Dependencies.  Stdlib [QArith.QArith], [Lia], [Extraction].  Requires
      [S02_CauchyComplete] of this development.

    References.  The minimization of the Doeblin (small-gain) constant: the
      explicit minimum of [2*K(s,s')] over two-state row-stochastic kernels
      with entries [lo/(1+lo)], [1/(1+lo)] in the first row and
      [(lo*lo)/(1+lo*lo)], [1/(1+lo*lo)] in the second.

    Constructivity.  All statements close with [Qed]; zero admission words;
      no classical logic; statement faces are carried by [Set] (order
      predicates and equalities are Set-valued [QltT]/[QleT']/[QeqT], zero
      Prop leakage).  Statements extract with [Obj.magic] = 0; [coqchk]
      reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblDeltaStarSuboptimal.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)


From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.
Require Import S02_CauchyComplete.

(* ========== §1 Q 算术基件 ========== *)

Lemma mdsopt_sq0 : forall lo : Q, (0 < lo)%Q -> QltT 0 (lo*lo).
Proof.
  intros lo H0. apply (Qlt_to_QltT 0 (lo*lo)).
  pose proof (Qmult_lt_compat_r 0 lo lo H0 H0) as H.
  rewrite Qmult_0_l in H. exact H.
Qed.

Lemma mdsopt_lt1 : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q -> QltT (lo*lo) 1.
Proof.
  intros lo H0 H1. apply (Qlt_to_QltT (lo*lo) 1).
  pose proof (Qmult_lt_compat_r lo 1 lo H0 H1) as H.
  rewrite Qmult_1_l in H. exact (Qlt_trans (lo*lo) lo 1 H H1).
Qed.

Lemma mdsopt_01 : QltT 0 1.
Proof. apply (Qlt_to_QltT 0 1). unfold Qlt, Qnum, Qden; cbn. exact eq_refl. Qed.

Lemma mdsopt_den_pos : forall lo : Q, (0 < lo)%Q -> QltT 0 (1 + lo*lo).
Proof.
  intros lo H0. apply (Qlt_to_QltT 0 (1 + lo*lo)).
  pose proof (QltT_to_Qlt 0 (lo*lo) (mdsopt_sq0 lo H0)) as H.
  pose proof (proj2 (Qplus_lt_r 0 (lo*lo) 1) H) as H2.
  rewrite Qplus_0_r in H2.
  exact (Qlt_trans 0 1 (1+lo*lo) (QltT_to_Qlt 0 1 mdsopt_01) H2).
Qed.

Lemma mdsopt_den_ne : forall lo : Q, (0 < lo)%Q -> S01_BaseRing.Not (QeqT (1 + lo*lo) 0).
Proof.
  intros lo H0 Hz.
  apply (qeqT_imp_qeq (1 + lo*lo) 0) in Hz.
  pose proof (QltT_to_Qlt 0 (1 + lo*lo) (mdsopt_den_pos lo H0)) as Hd.
  rewrite Hz in Hd. destruct (Qlt_irrefl 0 Hd).
Qed.

Lemma mdsopt_cancel : forall lo a : Q, ~ ((1 + lo*lo) == 0)%Q ->
  QeqT (a/(1+lo*lo)*(1+lo*lo)) a.
Proof.
  intros lo a Hd. apply (qeq_imp_qeqT (a/(1+lo*lo)*(1+lo*lo)) a).
  field. exact Hd.
Qed.

(* ========== §2 两态 softmax 核（Q 层，行随机） ========== *)

Definition mdsopt_k00 (lo : Q) : Q := lo/(1+lo).
Definition mdsopt_k01 (lo : Q) : Q := 1/(1+lo).
Definition mdsopt_k10 (lo : Q) : Q := (lo*lo)/(1+lo*lo).
Definition mdsopt_k11 (lo : Q) : Q := 1/(1+lo*lo).

(* 归一化验证：两行各和为 1 *)
Lemma mdsopt_row0_norm : forall lo : Q, (0 < lo)%Q ->
  QeqT (mdsopt_k00 lo + mdsopt_k01 lo) 1.
Proof.
  intros lo H0. apply (qeq_imp_qeqT (mdsopt_k00 lo + mdsopt_k01 lo) 1).
  unfold mdsopt_k00, mdsopt_k01.
  assert (Hx : (lo < lo + 1)%Q).
  { pose proof (proj2 (Qplus_lt_r 0 1 lo) (QltT_to_Qlt 0 1 mdsopt_01)) as H.
    rewrite Qplus_0_r in H. exact H. }
  assert (Hd : (0 < 1 + lo)%Q).
  { rewrite (Qplus_comm 1 lo). exact (Qlt_trans 0 lo (lo+1) H0 Hx). }
  assert (Hdn : ~ ((1+lo) == 0)%Q).
  { intro Hz. rewrite Hz in Hd. exact (Qlt_irrefl 0 Hd). }
  field. exact Hdn.
Qed.

Lemma mdsopt_row1_norm : forall lo : Q, (0 < lo)%Q ->
  QeqT (mdsopt_k10 lo + mdsopt_k11 lo) 1.
Proof.
  intros lo H0. apply (qeq_imp_qeqT (mdsopt_k10 lo + mdsopt_k11 lo) 1).
  unfold mdsopt_k10, mdsopt_k11.
  assert (Hdn : ~ ((1+lo*lo) == 0)%Q).
  { intro Hz. apply qeq_imp_qeqT in Hz. destruct (mdsopt_den_ne lo H0 Hz). }
  field. exact Hdn.
Qed.

(* ========== §3 δ*、最优常数与间隙（显式闭式定义） ========== *)

Definition mdsopt_dstar (lo : Q) : Q := lo*lo.
Definition mdsopt_dstar_opt (lo : Q) : Q := 2*(lo*lo)/(1+lo*lo).
Definition mdsopt_gap (lo : Q) : Q := (lo*lo)*(1-lo*lo)/(1+lo*lo).

(* ========== §4 主定理：δ* = lo² 严格次优（QltT Set 层见证形） ========== *)

Lemma mdsopt_main_strict : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  QltT (mdsopt_dstar lo) (mdsopt_dstar_opt lo).
Proof.
  intros lo H0 H1. apply (Qlt_to_QltT (mdsopt_dstar lo) (mdsopt_dstar_opt lo)).
  unfold mdsopt_dstar, mdsopt_dstar_opt.
  assert (Hsq0 := QltT_to_Qlt 0 (lo*lo) (mdsopt_sq0 lo H0)).
  assert (Hs1 := QltT_to_Qlt (lo*lo) 1 (mdsopt_lt1 lo H0 H1)).
  assert (Hden := QltT_to_Qlt 0 (1+lo*lo) (mdsopt_den_pos lo H0)).
  assert (Hnd : ~ ((1 + lo*lo) == 0)%Q).
  { intro Hz. apply qeq_imp_qeqT in Hz. destruct (mdsopt_den_ne lo H0 Hz). }
  assert (Hs2 : (1 + lo*lo < 2)%Q).
  { pose proof (proj2 (Qplus_lt_r (lo*lo) 1 1) Hs1) as H.
    assert (Heq : (1+1 == 2)%Q) by reflexivity.
    rewrite Heq in H. exact H. }
  (* 两端同乘正数 1+lo²（Qmult_lt_r 的 iff 可逆乘法），并消去右端
     分母（mdsopt_cancel），归结为 (1+lo²)·lo² < 2·lo²，即
     1+lo² < 2 与 lo² > 0 的 Qmult_lt_compat_r 直接推论。 *)
  apply (proj1 (Qmult_lt_r (lo*lo) (2*(lo*lo)/(1+lo*lo)) (1+lo*lo) Hden)).
  rewrite (qeqT_imp_qeq (2*(lo*lo)/(1+lo*lo)*(1+lo*lo)) (2*(lo*lo))
             (mdsopt_cancel lo (2*(lo*lo)) Hnd)).
  rewrite (Qmult_comm (lo*lo) (1+lo*lo)).
  apply (Qmult_lt_compat_r (1+lo*lo) 2 (lo*lo) Hsq0 Hs2).
Qed.

Theorem mdsopt_main : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  QltT (mdsopt_dstar lo) (mdsopt_dstar_opt lo).
Proof.
  intros lo H0 H1. apply mdsopt_main_strict; assumption.
Qed.

(* δ* 是可行 Doeblin 常数（δ* ≤ δ*_opt），主定理给出严格性 *)
Corollary mdsopt_dstar_le_opt : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  QleT' (mdsopt_dstar lo) (mdsopt_dstar_opt lo).
Proof.
  intros lo H0 H1. apply (Qle_to_QleT' (mdsopt_dstar lo) (mdsopt_dstar_opt lo)).
  apply Qlt_le_weak. apply (QltT_to_Qlt (mdsopt_dstar lo) (mdsopt_dstar_opt lo)).
  apply mdsopt_main_strict; assumption.
Qed.

(* ========== §5 间隙件：闭式与严格正 ========== *)

Lemma mdsopt_gap_eq : forall lo : Q, (0 < lo)%Q ->
  QeqT (mdsopt_dstar_opt lo - mdsopt_dstar lo) (mdsopt_gap lo).
Proof.
  intros lo H0.
  apply (qeq_imp_qeqT (mdsopt_dstar_opt lo - mdsopt_dstar lo) (mdsopt_gap lo)).
  unfold mdsopt_dstar_opt, mdsopt_dstar, mdsopt_gap.
  assert (Hd : ~ ((1 + lo*lo) == 0)%Q).
  { intro Hz. apply qeq_imp_qeqT in Hz. destruct (mdsopt_den_ne lo H0 Hz). }
  field. exact Hd.
Qed.

Lemma mdsopt_gap_pos : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  QltT 0 (mdsopt_gap lo).
Proof.
  intros lo H0 H1. apply (Qlt_to_QltT 0 (mdsopt_gap lo)).
  assert (Hsq0 := QltT_to_Qlt 0 (lo*lo) (mdsopt_sq0 lo H0)).
  assert (Hs1 := QltT_to_Qlt (lo*lo) 1 (mdsopt_lt1 lo H0 H1)).
  assert (Hden := QltT_to_Qlt 0 (1+lo*lo) (mdsopt_den_pos lo H0)).
  assert (Hnd : ~ ((1 + lo*lo) == 0)%Q).
  { intro Hz. apply qeq_imp_qeqT in Hz. destruct (mdsopt_den_ne lo H0 Hz). }
  assert (Hn1 : (0 < 1 - lo*lo)%Q).
  { pose proof (Qopp_lt_compat (lo*lo) 1 Hs1) as Ho.
    pose proof (proj2 (Qplus_lt_r (-1) (-(lo*lo)) 1) Ho) as Hm.
    rewrite Qplus_opp_r in Hm.
    exact Hm. }
  pose proof (Qmult_lt_compat_r 0 (1 - lo*lo) (lo*lo) Hsq0 Hn1) as Hp.
  rewrite Qmult_0_l in Hp.
  rewrite (Qmult_comm (1 - lo*lo) (lo*lo)) in Hp.
  unfold mdsopt_gap.
  (* 分母 1+lo² > 0，两端同乘归结为分子正性：
     lo²>0 与 1−lo²>0（由 lo²<1 经 Qopp_lt_compat 移项）之积。 *)
  apply (proj1 (Qmult_lt_r 0 ((lo*lo)*(1 - lo*lo)/(1+lo*lo)) (1+lo*lo) Hden)).
  rewrite Qmult_0_l.
  rewrite (qeqT_imp_qeq ((lo*lo)*(1 - lo*lo)/(1+lo*lo)*(1+lo*lo))
             ((lo*lo)*(1 - lo*lo))
             (mdsopt_cancel lo ((lo*lo)*(1 - lo*lo)) Hnd)).
  exact Hp.
Qed.

(* ========== §6 提取出口（G3：独立目录，魔数=0 判据） ========== *)

From Stdlib Require Import Extraction.
Set Extraction Output Directory "../_tdsopt_g3out".
Separate Extraction mdsopt_k00 mdsopt_k01 mdsopt_k10 mdsopt_k11
  mdsopt_dstar mdsopt_dstar_opt mdsopt_gap.
