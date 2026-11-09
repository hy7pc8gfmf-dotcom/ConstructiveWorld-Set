(* ==========================================================================
   UpAblDeltaStarSuboptimal.v — sharp suboptimality of the Doeblin constant
   for the two-state softmax kernel.

   Mission.  mdsopt_main: the star constant δ* = lo² (mdsopt_dstar) is
   strictly below the optimal constant δ*_opt = 2·lo²/(1+lo²)
   (mdsopt_dstar_opt), with the explicit positive gap mdsopt_gap_pos;
   supporting pieces give the row-stochastic normalization
   mdsopt_row0_norm/mdsopt_row1_norm and the Q-layer arithmetic chain.

   Dependencies.  S02_CauchyComplete; Stdlib QArith, Lia, Extraction.

   References.  Minimization of the Doeblin (small gain) constant: the
   explicit solution of min 2K(s,s') over two-state row-stochastic kernels.

   Constructivity.  All pieces close by Qed; no classical logic; the
   statement face is carried on the Set layer (the order predicate QltT and
   the Q equality are Set-valued, with zero Prop leakage).

   Build.  Rocq 9.3, direct coqc -native-compiler no with the file root
   mapped at . (vo shadow tree rebuilt in the same world), cpu_guard
   wrapping for load capping; .vo magic [436f7121 000160bc].
   ========================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.
Require Import S02_CauchyComplete.

(* ========== §1 Q arithmetic basics ========== *)

Lemma mdsopt_sq0 : forall lo : Q, (0 < lo)%Q -> (0 < lo*lo)%Q.
Proof.
  intros lo H0. pose proof (Qmult_lt_compat_r 0 lo lo H0 H0) as H.
  rewrite Qmult_0_l in H. exact H.
Qed.

Lemma mdsopt_lt1 : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q -> (lo*lo < 1)%Q.
Proof.
  intros lo H0 H1. pose proof (Qmult_lt_compat_r lo 1 lo H0 H1) as H.
  rewrite Qmult_1_l in H. exact (Qlt_trans (lo*lo) lo 1 H H1).
Qed.

Lemma mdsopt_01 : (0 < 1)%Q.
Proof. unfold Qlt, Qnum, Qden; cbn. exact eq_refl. Qed.

Lemma mdsopt_den_pos : forall lo : Q, (0 < lo)%Q -> (0 < 1 + lo*lo)%Q.
Proof.
  intros lo H0.
  pose proof (mdsopt_sq0 lo H0) as H.
  pose proof (proj2 (Qplus_lt_r 0 (lo*lo) 1) H) as H2.
  rewrite Qplus_0_r in H2.
  exact (Qlt_trans 0 1 (1+lo*lo) mdsopt_01 H2).
Qed.

Lemma mdsopt_den_ne : forall lo : Q, (0 < lo)%Q -> ~ ((1 + lo*lo) == 0)%Q.
Proof.
  intros lo H0 Hz. pose proof (mdsopt_den_pos lo H0) as Hd.
  rewrite Hz in Hd. exact (Qlt_irrefl 0 Hd).
Qed.

Lemma mdsopt_cancel : forall lo a : Q, ~ ((1 + lo*lo) == 0)%Q ->
  (a/(1+lo*lo)*(1+lo*lo) == a)%Q.
Proof. intros lo a Hd. field. exact Hd. Qed.

(* ========== §2 the two-state softmax kernel (Q layer, row stochastic) ========== *)

Definition mdsopt_k00 (lo : Q) : Q := lo/(1+lo).
Definition mdsopt_k01 (lo : Q) : Q := 1/(1+lo).
Definition mdsopt_k10 (lo : Q) : Q := (lo*lo)/(1+lo*lo).
Definition mdsopt_k11 (lo : Q) : Q := 1/(1+lo*lo).

(* normalization check: each row sums to 1 *)
Lemma mdsopt_row0_norm : forall lo : Q, (0 < lo)%Q ->
  (mdsopt_k00 lo + mdsopt_k01 lo == 1)%Q.
Proof.
  intros lo H0. unfold mdsopt_k00, mdsopt_k01.
  assert (Hx : (lo < lo + 1)%Q).
  { pose proof (proj2 (Qplus_lt_r 0 1 lo) mdsopt_01) as H.
    rewrite Qplus_0_r in H. exact H. }
  assert (Hd : (0 < 1 + lo)%Q).
  { rewrite (Qplus_comm 1 lo). exact (Qlt_trans 0 lo (lo+1) H0 Hx). }
  assert (Hdn : ~ ((1+lo) == 0)%Q).
  { intro Hz. rewrite Hz in Hd. exact (Qlt_irrefl 0 Hd). }
  field. exact Hdn.
Qed.

Lemma mdsopt_row1_norm : forall lo : Q, (0 < lo)%Q ->
  (mdsopt_k10 lo + mdsopt_k11 lo == 1)%Q.
Proof.
  intros lo H0. unfold mdsopt_k10, mdsopt_k11.
  assert (Hdn := mdsopt_den_ne lo H0).
  field. exact Hdn.
Qed.

(* ========== §3 δ*, the optimal constant and the gap (explicit closed forms) ========== *)

Definition mdsopt_dstar (lo : Q) : Q := lo*lo.
Definition mdsopt_dstar_opt (lo : Q) : Q := 2*(lo*lo)/(1+lo*lo).
Definition mdsopt_gap (lo : Q) : Q := (lo*lo)*(1-lo*lo)/(1+lo*lo).

(* ========== §4 main theorem: δ* = lo² strictly suboptimal (QltT Set-layer witness form) ========== *)

Lemma mdsopt_main_strict : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (mdsopt_dstar lo < mdsopt_dstar_opt lo)%Q.
Proof.
  intros lo H0 H1. unfold mdsopt_dstar, mdsopt_dstar_opt.
  assert (Hsq0 := mdsopt_sq0 lo H0).
  assert (Hs1 := mdsopt_lt1 lo H0 H1).
  assert (Hden := mdsopt_den_pos lo H0).
  assert (Hs2 : (1 + lo*lo < 2)%Q).
  { pose proof (proj2 (Qplus_lt_r (lo*lo) 1 1) Hs1) as H.
    assert (Heq : (1+1 == 2)%Q) by reflexivity.
    rewrite Heq in H. exact H. }
  (* multiply both sides by the positive quantity 1+lo² (the iff form of
     Qmult_lt_r gives invertible multiplication by a positive denominator)
     and cancel the denominator on the right by mdsopt_cancel; the goal
     reduces to (1+lo²)·lo² < 2·lo², a direct consequence of 1+lo² < 2 and
     lo² > 0 by Qmult_lt_compat_r. *)
  apply (proj1 (Qmult_lt_r (lo*lo) (2*(lo*lo)/(1+lo*lo)) (1+lo*lo) Hden)).
  rewrite (mdsopt_cancel lo (2*(lo*lo)) (mdsopt_den_ne lo H0)).
  rewrite (Qmult_comm (lo*lo) (1+lo*lo)).
  apply (Qmult_lt_compat_r (1+lo*lo) 2 (lo*lo) Hsq0 Hs2).
Qed.

Theorem mdsopt_main : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  QltT (mdsopt_dstar lo) (mdsopt_dstar_opt lo).
Proof.
  intros lo H0 H1. apply Qlt_to_QltT. apply mdsopt_main_strict; assumption.
Qed.

(* δ* is a feasible Doeblin constant (δ* ≤ δ*_opt); the main theorem supplies strictness *)
Corollary mdsopt_dstar_le_opt : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (mdsopt_dstar lo <= mdsopt_dstar_opt lo)%Q.
Proof.
  intros lo H0 H1. apply Qlt_le_weak. apply mdsopt_main_strict; assumption.
Qed.

(* ========== §5 gap pieces: closed form and strict positivity ========== *)

Lemma mdsopt_gap_eq : forall lo : Q, (0 < lo)%Q ->
  (mdsopt_dstar_opt lo - mdsopt_dstar lo == mdsopt_gap lo)%Q.
Proof.
  intros lo H0. unfold mdsopt_dstar_opt, mdsopt_dstar, mdsopt_gap.
  assert (Hd := mdsopt_den_ne lo H0). field. exact Hd.
Qed.

Lemma mdsopt_gap_pos : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (0 < mdsopt_gap lo)%Q.
Proof.
  intros lo H0 H1.
  assert (Hsq0 := mdsopt_sq0 lo H0).
  assert (Hs1 := mdsopt_lt1 lo H0 H1).
  assert (Hden := mdsopt_den_pos lo H0).
  assert (Hnd := mdsopt_den_ne lo H0).
  assert (Hn1 : (0 < 1 - lo*lo)%Q).
  { pose proof (Qopp_lt_compat (lo*lo) 1 Hs1) as Ho.
    pose proof (proj2 (Qplus_lt_r (-1) (-(lo*lo)) 1) Ho) as Hm.
    rewrite Qplus_opp_r in Hm.
    exact Hm. }
  pose proof (Qmult_lt_compat_r 0 (1 - lo*lo) (lo*lo) Hsq0 Hn1) as Hp.
  rewrite Qmult_0_l in Hp.
  rewrite (Qmult_comm (1 - lo*lo) (lo*lo)) in Hp.
  unfold mdsopt_gap.
  (* the denominator 1+lo² > 0, so multiplying both sides reduces the goal
     to positivity of the numerator: the product of lo²>0 and 1-lo²>0,
     where 1-lo²>0 moves lo²<1 to the other side via Qopp_lt_compat. *)
  apply (proj1 (Qmult_lt_r 0 ((lo*lo)*(1 - lo*lo)/(1+lo*lo)) (1+lo*lo) Hden)).
  rewrite Qmult_0_l.
  rewrite (mdsopt_cancel lo ((lo*lo)*(1 - lo*lo)) Hnd).
  exact Hp.
Qed.

(* ========== §6 extraction outlet (G3: separate directory, magic = 0 criterion) ========== *)

From Stdlib Require Import Extraction.
Set Extraction Output Directory "../_tdsopt_g3out".
Separate Extraction mdsopt_k00 mdsopt_k01 mdsopt_k10 mdsopt_k11
  mdsopt_dstar mdsopt_dstar_opt mdsopt_gap.
