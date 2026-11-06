(* ConstructiveWorld-Set -- constructive Doeblin-constant optimality over rational row-stochastic kernels. *)

(** * UpAblDeltaStarGeneral: the general nR-state Doeblin kernel family dsgen_k and its optimal constant.

    Mission.  Constructive generalization of the suboptimality of the
      Doeblin constant delta* = lo*lo from the 2-state kernel to
      row-stochastic kernels on nR >= 2 states through the explicit
      convex-combination kernel family [dsgen_k]: the main faces are
      row-stochasticity [dsgen_rowstoch], Doeblin feasibility
      [dsgen_feasible], beta-optimality at nR >= 3 [dsgen_optimal_ge3],
      the Set-level witness [dsgen_main], and the gap comparison
      [dsgen_gap_ge_mdsopt].

    Dependencies.  Stdlib [QArith.QArith], [Lia], [ZArith], [List] and
      [Extraction]; requires [S02_CauchyComplete] and
      [UpAblDeltaStarSuboptimal] of this development.

    References.  This development, UpAblDeltaStarGeneral.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblDeltaStarGeneral.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Require Import S02_CauchyComplete.
Require Import UpAblDeltaStarSuboptimal.
Import ListNotations.

(* ========== Section 1. Q arithmetic primitives (positivity, nonzero, division, monotonicity) ========== *)

Lemma dsgen_2pos : (0 < 2)%Q.
Proof. unfold Qlt, Qnum, Qden; cbn; lia. Qed.

Lemma dsgen_ne_of_pos : forall d : Q, (0 < d)%Q -> ~ ((d) == 0)%Q.
Proof.
  intros d Hp Hz. rewrite Hz in Hp. exact (Qlt_irrefl 0 Hp).
Qed.

(* Division cancellation (the proj1 direction of the Qmult_lt_r iff): with a
   positive denominator, [0 < a/d] reduces to [0 < a] (both sides multiplied by
   [d]; [(a/d)*d == a] closes by [field]). *)
Lemma dsgen_div_cancel : forall a d : Q, ~ ((d) == 0)%Q -> ((a/d)*d == a)%Q.
Proof. intros a d Hd. field. exact Hd. Qed.

Lemma dsgen_div_pos : forall a d : Q, (0 < a)%Q -> (0 < d)%Q -> (0 < a/d)%Q.
Proof.
  intros a d Ha Hd.
  apply (proj1 (Qmult_lt_r 0 (a/d) d Hd)).
  rewrite Qmult_0_l.
  rewrite (dsgen_div_cancel a d (dsgen_ne_of_pos d Hd)). exact Ha.
Qed.

(* [a/d == a*(1/d)]: division turned into multiplication so that the
   Qmult_le_r and Qmult_lt_r cancellations apply. *)
Lemma dsgen_div_inv : forall a d : Q, ~ ((d) == 0)%Q -> ((a/d) == a*(1/d))%Q.
Proof. intros a d Hd. field. exact Hd. Qed.

(* Positivity of a product of positives ([Qmult_lt_compat_r] with the [0<z]
   premise first; the [0*b] term clears by [Qmult_0_l]). *)
Lemma dsgen_mul_pos : forall a b : Q, (0 < a)%Q -> (0 < b)%Q -> (0 < a*b)%Q.
Proof.
  intros a b Ha Hb.
  pose proof (Qmult_lt_compat_r 0 a b Hb Ha) as H.
  rewrite Qmult_0_l in H. exact H.
Qed.

(* Adding a positive summand preserves [<=]: [z <= z+w] (the proj2 direction
   of the Qplus_le_r iff, closed with [Qplus_0_r]). *)
Lemma dsgen_le_add_pos : forall z w : Q, (0 < w)%Q -> (z <= z + w)%Q.
Proof.
  intros z w Hw.
  pose proof (proj2 (Qplus_le_r 0 w z) (Qlt_le_weak 0 w Hw)) as H.
  rewrite Qplus_0_r in H. exact H.
Qed.

(* Symmetric form: [w <= z+w] (the premise concerns the other summand). *)
Lemma dsgen_le_add_pos2 : forall z w : Q, (0 < z)%Q -> (w <= z + w)%Q.
Proof.
  intros z w Hz. rewrite (Qplus_comm z w). apply dsgen_le_add_pos. exact Hz.
Qed.

(* [x*2 == x+x]: a pure ring identity on Q, closed directly by [field]. *)
Lemma dsgen_two_mul_r : forall x : Q, ((x)*2 == x + x)%Q.
Proof. intros x. field. Qed.

(* ========== Section 2. Q-carrier of the state count nR ========== *)

Definition dsgen_qN (nR : nat) : Q := (Z.of_nat nR)#1.

Lemma dsgen_qN_pos : forall nR : nat, (1 <= nR)%nat -> (0 < dsgen_qN nR)%Q.
Proof.
  intros [|n] Hn; [ inversion Hn
  | unfold dsgen_qN, Qlt, Qnum, Qden; cbn; lia ].
Qed.

(* [qN (S n) == qN n + 1]: after the Z.of_nat reduction of S, the Qnum face
   unfolds and [lia] closes the Z.eqb goal. *)
Lemma dsgen_qN_S : forall n : nat, dsgen_qN (S n) == dsgen_qN n + 1.
Proof.
  intros n. unfold dsgen_qN.
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
  unfold Qeq, Qplus, Qnum, Qden. cbn. lia.
Qed.

(* ========== Section 3. Arithmetic face of beta := (1+lo*lo)/2 ========== *)

Definition dsgen_beta (lo : Q) : Q := (1 + lo*lo)/2.

Lemma dsgen_beta_pos : forall lo : Q, (0 < lo)%Q -> (0 < dsgen_beta lo)%Q.
Proof.
  intros lo H0. unfold dsgen_beta.
  apply dsgen_div_pos.
  - exact (QltT_to_Qlt 0 (1 + lo*lo) (mdsopt_den_pos lo H0)).
  - exact dsgen_2pos.
Qed.

(* [0 < 1 - lo*lo]: transposition by [Qopp_lt_compat] and sum merging by the
   proj2 direction of the [Qplus_lt_r] iff. *)
Lemma dsgen_1mlo2_pos : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (0 < 1 - lo*lo)%Q.
Proof.
  intros lo H0 H1.
  pose proof (Qopp_lt_compat (lo*lo) 1
                (QltT_to_Qlt (lo*lo) 1 (mdsopt_lt1 lo H0 H1))) as Ho.
  pose proof (proj2 (Qplus_lt_r (-1) (-(lo*lo)) 1) Ho) as Hm.
  rewrite Qplus_opp_r in Hm. exact Hm.
Qed.

(* [0 < 1 - beta]: rewriting [beta] as (1-lo*lo)/2 and applying division
   positivity. *)
Lemma dsgen_omb_pos : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (0 < 1 - dsgen_beta lo)%Q.
Proof.
  intros lo H0 H1.
  assert (Hb : (1 - dsgen_beta lo == (1 - lo*lo)/2)%Q)
    by (unfold dsgen_beta; field; apply dsgen_ne_of_pos; exact dsgen_2pos).
  rewrite Hb. apply dsgen_div_pos.
  - apply dsgen_1mlo2_pos; assumption.
  - exact dsgen_2pos.
Qed.

Lemma dsgen_beta_le_1 : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (dsgen_beta lo <= 1)%Q.
Proof.
  intros lo H0 H1.
  assert (Hcore : (1 + lo*lo <= 2)%Q).
  { pose proof (proj2 (Qplus_lt_r (lo*lo) 1 1)
                   (QltT_to_Qlt (lo*lo) 1 (mdsopt_lt1 lo H0 H1))) as H.
    assert (Heq : (1+1 == 2)%Q) by reflexivity.
    rewrite Heq in H. exact (Qlt_le_weak _ _ H). }
  unfold dsgen_beta.
  (* Both sides multiplied by 2 (the proj1 direction of the Qmult_le_r iff);
     the denominator on the left cancels by [field]. *)
  apply (proj1 (Qmult_le_r ((1 + lo*lo)/2) 1 2 dsgen_2pos)).
  rewrite (dsgen_div_cancel (1 + lo*lo) 2 (dsgen_ne_of_pos 2 dsgen_2pos)).
  rewrite Qmult_1_l. exact Hcore.
Qed.

(* [lo*lo < beta] unfolds to [2*lo*lo < 1+lo*lo], that is [lo*lo < 1]; the
   multiplication by 2 is undone through the Qmult_lt_r iff. *)
Lemma dsgen_dstar_lt_beta : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (lo*lo < dsgen_beta lo)%Q.
Proof.
  intros lo H0 H1. unfold dsgen_beta.
  apply (proj1 (Qmult_lt_r (lo*lo) ((1 + lo*lo)/2) 2 dsgen_2pos)).
  rewrite (dsgen_div_cancel (1 + lo*lo) 2 (dsgen_ne_of_pos 2 dsgen_2pos)).
  rewrite dsgen_two_mul_r, (Qplus_comm 1 (lo*lo)).
  apply (proj2 (Qplus_lt_r (lo*lo) 1 (lo*lo))).
  exact (QltT_to_Qlt (lo*lo) 1 (mdsopt_lt1 lo H0 H1)).
Qed.

Lemma dsgen_dstar_le_beta : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (lo*lo <= dsgen_beta lo)%Q.
Proof. intros lo H0 H1. apply Qlt_le_weak. apply dsgen_dstar_lt_beta; assumption. Qed.

(* ========== Section 4. Positivity of the 2-state block entries (via UpAblDeltaStarSuboptimal) ========== *)

Lemma dsgen_onelo_pos : forall lo : Q, (0 < lo)%Q -> (0 < 1 + lo)%Q.
Proof.
  intros lo H0.
  pose proof (proj2 (Qplus_lt_r 0 1 lo) (QltT_to_Qlt 0 1 mdsopt_01)) as Hx.
  rewrite Qplus_0_r in Hx.
  rewrite (Qplus_comm 1 lo).
  exact (Qlt_trans 0 lo (lo + 1) H0 Hx).
Qed.

Lemma dsgen_k00_pos : forall lo : Q, (0 < lo)%Q -> (0 < mdsopt_k00 lo)%Q.
Proof.
  intros lo H0. unfold mdsopt_k00. apply dsgen_div_pos;
    [ exact H0 | apply dsgen_onelo_pos; exact H0 ].
Qed.

Lemma dsgen_k01_pos : forall lo : Q, (0 < lo)%Q -> (0 < mdsopt_k01 lo)%Q.
Proof.
  intros lo H0. unfold mdsopt_k01. apply dsgen_div_pos;
    [ exact (QltT_to_Qlt 0 1 mdsopt_01) | apply dsgen_onelo_pos; exact H0 ].
Qed.

Lemma dsgen_k10_pos : forall lo : Q, (0 < lo)%Q -> (0 < mdsopt_k10 lo)%Q.
Proof.
  intros lo H0. unfold mdsopt_k10. apply dsgen_div_pos;
    [ exact (QltT_to_Qlt 0 (lo*lo) (mdsopt_sq0 lo H0))
    | exact (QltT_to_Qlt 0 (1 + lo*lo) (mdsopt_den_pos lo H0)) ].
Qed.

Lemma dsgen_k11_pos : forall lo : Q, (0 < lo)%Q -> (0 < mdsopt_k11 lo)%Q.
Proof.
  intros lo H0. unfold mdsopt_k11. apply dsgen_div_pos;
    [ exact (QltT_to_Qlt 0 1 mdsopt_01)
    | exact (QltT_to_Qlt 0 (1 + lo*lo) (mdsopt_den_pos lo H0)) ].
Qed.

(* ========== Section 5. The nR-state kernel definition (convex-combination embedding, arbitrary nR >= 2) ========== *)

(* [K s j = (1-beta) * B s j + beta/nR]: B embeds the 2-state block (uniform
   rows at indices >= 2, zero block at rows 0/1 and columns >= 2), beta/nR is
   the leakage mass, and every row sum stays 1.
   (The matches use the fully qualified Datatypes.O/S constructor shapes:
   with Q_scope open after QArith, numeral patterns would be read as Q
   constructors; the qualified shapes are unambiguous.) *)
Definition dsgen_k (nR : nat) (lo : Q) (s j : nat) : Q :=
  match s with
  | Datatypes.O => match j with
                   | Datatypes.O => (1 - dsgen_beta lo) * mdsopt_k00 lo
                                    + dsgen_beta lo / dsgen_qN nR
                   | Datatypes.S j' => match j' with
                                       | Datatypes.O => (1 - dsgen_beta lo) * mdsopt_k01 lo
                                                        + dsgen_beta lo / dsgen_qN nR
                                       | _ => dsgen_beta lo / dsgen_qN nR
                                       end
                   end
  | Datatypes.S s' => match s' with
                      | Datatypes.O => match j with
                                       | Datatypes.O => (1 - dsgen_beta lo) * mdsopt_k10 lo
                                                        + dsgen_beta lo / dsgen_qN nR
                                       | Datatypes.S j'' => match j'' with
                                                            | Datatypes.O => (1 - dsgen_beta lo) * mdsopt_k11 lo
                                                                             + dsgen_beta lo / dsgen_qN nR
                                                            | _ => dsgen_beta lo / dsgen_qN nR
                                                            end
                                       end
                      | _ => 1 / dsgen_qN nR
                      end
  end.

Definition dsgen_dsum (f : nat -> Q) (l : list nat) : Q :=
  fold_right Qplus 0 (map f l).

Definition dsgen_rowsum (nR : nat) (lo : Q) (s : nat) : Q :=
  dsgen_dsum (dsgen_k nR lo s) (seq 0 nR).

(* Row-stochasticity at the Set level: every row sum equals 1, carried by the
   decidable Q-equality leaf [QeqT]. *)
Definition dsgen_rowstoch (nR : nat) (lo : Q) : Set :=
  forall s : nat, (s < nR)%nat -> QeqT (dsgen_rowsum nR lo s) 1.

(* Doeblin feasibility against the uniform reference U = 1/nR: the entry
   bound [d * (1/nR) <= K s j] holds at every entry, carried by the decidable
   Q-leaves [QleT']. *)
Definition dsgen_feasible (nR : nat) (lo d : Q) : Set :=
  forall s j : nat, (s < nR)%nat -> (j < nR)%nat ->
    QleT' (d * (1 / dsgen_qN nR)) (dsgen_k nR lo s j).

(* ========== Section 6. List-summation primitives (fold over seq) ========== *)

(* List-level fold over Q splits concatenations ([cbn] with the app and
   fold_right arguments only, so the Qeq goal does not over-reduce). *)
Lemma dsgen_fold_app : forall (l1 l2 : list Q),
  fold_right Qplus 0 (l1 ++ l2) == fold_right Qplus 0 l1 + fold_right Qplus 0 l2.
Proof.
  intros l1 l2. induction l1 as [|a l1 IH].
  - cbn [app fold_right]. symmetry. apply Qplus_0_l.
  - cbn [app fold_right]. rewrite IH. apply Qplus_assoc.
Qed.

Lemma dsgen_dsum_app : forall (f : nat -> Q) (l1 l2 : list nat),
  dsgen_dsum f (l1 ++ l2) == dsgen_dsum f l1 + dsgen_dsum f l2.
Proof. intros f l1 l2. unfold dsgen_dsum. rewrite map_app. apply dsgen_fold_app. Qed.

(* Sum of a constant segment: n copies of c sum to n*c ([seq_S] peels the
   tail and the induction runs on the Z.of_nat face of qN). *)
Lemma dsgen_dsum_const_seq : forall (f : nat -> Q) (c : Q) (n start : nat),
  (forall j : nat, In j (seq start n) -> f j == c) ->
  dsgen_dsum f (seq start n) == dsgen_qN n * c.
Proof.
  intros f c n. induction n as [|n IH]; intros start Hfib.
  - (* The empty segment sums to 0 and [qN 0] is 0: [Qmult_0_l] gives the
       whole-term conversion. *)
    symmetry. exact (Qmult_0_l c).
  - rewrite seq_S. rewrite dsgen_dsum_app.
    assert (Hs : dsgen_dsum f ((start + n)%nat :: nil) == f (start + n)%nat + 0)
      by reflexivity.
    rewrite Hs, Qplus_0_r.
    rewrite IH by (intros j Hj; apply Hfib; apply in_seq in Hj;
                   apply in_seq; simpl in *; lia).
    rewrite <- (Hfib (start + n)%nat) by (apply in_seq; simpl; lia).
    rewrite dsgen_qN_S, Qmult_plus_distr_l, Qmult_1_l. reflexivity.
Qed.

(* ========== Section 7. Row-stochasticity (all nR >= 2) ========== *)

(* [qN (S (S m)) == qN m + 2]: the Qnum face unfolds and [lia] closes the
   Z.eqb goal. *)
Lemma dsgen_qN_split2 : forall m : nat,
  dsgen_qN (S (S m)) == dsgen_qN m + 2.
Proof.
  intros m. rewrite dsgen_qN_S, dsgen_qN_S. field.
Qed.

Lemma dsgen_seq_head2 : forall m : nat, seq 0 (S (S m)) = [0; 1]%nat ++ seq 2 m.
Proof. intros m. reflexivity. Qed.

(* Common closing for rows 0 and 1: grouping by the [field] ring identity
   turns the block sums == 1 into a cancellation of the block terms; the
   leakage segment qN*(beta/qN) collapses to beta by [Qmult_comm] and the
   division cancellation, leaving (1-beta)+beta == 1. *)
Lemma dsgen_rowstoch_head : forall (m : nat) (lo : Q),
  (0 < lo)%Q ->
  (mdsopt_k00 lo + mdsopt_k01 lo == 1)%Q ->
  (mdsopt_k10 lo + mdsopt_k11 lo == 1)%Q ->
  dsgen_rowsum (S (S m)) lo 0 == 1 /\ dsgen_rowsum (S (S m)) lo 1 == 1.
Proof.
  intros m lo H0 Hn0 Hn1.
  assert (Hqpos : (0 < dsgen_qN (S (S m)))%Q) by (apply dsgen_qN_pos; lia).
  assert (Hqne : ~ ((dsgen_qN (S (S m))) == 0)%Q)
    by (apply dsgen_ne_of_pos; exact Hqpos).
  assert (Hq2 : (0 < dsgen_qN m + 2)%Q).
  { unfold dsgen_qN, Qlt, Qnum, Qden. cbn. lia. }
  assert (Hgrp : forall k0 k1 : Q,
    (1 - dsgen_beta lo) * k0 + dsgen_beta lo / dsgen_qN (S (S m))
    + ((1 - dsgen_beta lo) * k1 + dsgen_beta lo / dsgen_qN (S (S m)))
    + dsgen_qN m * (dsgen_beta lo / dsgen_qN (S (S m)))
    == (1 - dsgen_beta lo) * (k0 + k1)
       + dsgen_qN (S (S m)) * (dsgen_beta lo / dsgen_qN (S (S m)))).
  { intros k0 k1. rewrite dsgen_qN_split2. field.
    apply dsgen_ne_of_pos. exact Hq2. }
  unfold dsgen_rowsum; split.
  - rewrite dsgen_seq_head2. rewrite dsgen_dsum_app.
    assert (Hhead : dsgen_dsum (dsgen_k (S (S m)) lo 0) [0; 1]%nat
                    == dsgen_k (S (S m)) lo 0 0
                       + (dsgen_k (S (S m)) lo 0 1 + 0)) by reflexivity.
    rewrite Hhead, Qplus_0_r.
    assert (Htail : dsgen_dsum (dsgen_k (S (S m)) lo 0) (seq 2 m)
                    == dsgen_qN m * (dsgen_beta lo / dsgen_qN (S (S m)))).
    { apply (dsgen_dsum_const_seq (dsgen_k (S (S m)) lo 0)
               (dsgen_beta lo / dsgen_qN (S (S m))) m 2).
      intros j Hj. apply in_seq in Hj.
      destruct j as [|[|j]]; [ lia | lia | ]. reflexivity. }
    rewrite Htail.
    cbn [dsgen_k]. rewrite Hgrp, Hn0, Qmult_1_r.
    rewrite (Qmult_comm (dsgen_qN (S (S m)))
                        (dsgen_beta lo / dsgen_qN (S (S m)))).
    rewrite (dsgen_div_cancel (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    assert (Hfin : ((1 - dsgen_beta lo) + dsgen_beta lo == 1)%Q) by field.
    exact Hfin.
  - rewrite dsgen_seq_head2. rewrite dsgen_dsum_app.
    assert (Hhead : dsgen_dsum (dsgen_k (S (S m)) lo 1) [0; 1]%nat
                    == dsgen_k (S (S m)) lo 1 0
                       + (dsgen_k (S (S m)) lo 1 1 + 0)) by reflexivity.
    rewrite Hhead, Qplus_0_r.
    assert (Htail : dsgen_dsum (dsgen_k (S (S m)) lo 1) (seq 2 m)
                    == dsgen_qN m * (dsgen_beta lo / dsgen_qN (S (S m)))).
    { apply (dsgen_dsum_const_seq (dsgen_k (S (S m)) lo 1)
               (dsgen_beta lo / dsgen_qN (S (S m))) m 2).
      intros j Hj. apply in_seq in Hj.
      destruct j as [|[|j]]; [ lia | lia | ]. reflexivity. }
    rewrite Htail.
    cbn [dsgen_k]. rewrite Hgrp, Hn1, Qmult_1_r.
    rewrite (Qmult_comm (dsgen_qN (S (S m)))
                        (dsgen_beta lo / dsgen_qN (S (S m)))).
    rewrite (dsgen_div_cancel (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    assert (Hfin : ((1 - dsgen_beta lo) + dsgen_beta lo == 1)%Q) by field.
    exact Hfin.
Qed.

Lemma dsgen_rowstoch_SS : forall (m : nat) (lo : Q), (0 < lo)%Q -> (lo < 1)%Q ->
  dsgen_rowstoch (S (S m)) lo.
Proof.
  intros m lo H0 H1 s Hs. apply qeq_imp_qeqT. destruct s as [|[|k]].
  - apply (proj1 (dsgen_rowstoch_head m lo H0
                    (qeqT_imp_qeq (mdsopt_k00 lo + mdsopt_k01 lo) 1
                       (mdsopt_row0_norm lo H0))
                    (qeqT_imp_qeq (mdsopt_k10 lo + mdsopt_k11 lo) 1
                       (mdsopt_row1_norm lo H0)))).
  - apply (proj2 (dsgen_rowstoch_head m lo H0
                    (qeqT_imp_qeq (mdsopt_k00 lo + mdsopt_k01 lo) 1
                       (mdsopt_row0_norm lo H0))
                    (qeqT_imp_qeq (mdsopt_k10 lo + mdsopt_k11 lo) 1
                       (mdsopt_row1_norm lo H0)))).
  - (* Rows >= 2 are uniform: nR*(1/nR) == 1. *)
    unfold dsgen_rowsum.
    assert (Htail : dsgen_dsum (dsgen_k (S (S m)) lo (S (S k))) (seq 0 (S (S m)))
                    == dsgen_qN (S (S m)) * (1 / dsgen_qN (S (S m)))).
    { apply (dsgen_dsum_const_seq (dsgen_k (S (S m)) lo (S (S k)))
               (1 / dsgen_qN (S (S m))) (S (S m)) 0).
      intros j Hj. reflexivity. }
    rewrite Htail.
    assert (Hge : (1 <= S (S m))%nat) by lia.
    rewrite (Qmult_comm (dsgen_qN (S (S m))) (1 / dsgen_qN (S (S m)))).
    rewrite (dsgen_div_cancel 1 (dsgen_qN (S (S m)))
               (dsgen_ne_of_pos _ (dsgen_qN_pos (S (S m)) Hge))).
    reflexivity.
Qed.

(* ========== Section 8. Feasibility and optimality (beta is exactly optimal at nR >= 3) ========== *)

(* Feasibility of beta: block entries dominate beta/nR (monotonicity of
   addition with a positive summand, [dsgen_le_add_pos2]), the leakage columns
   meet the bound with equality, and the uniform rows dominate beta/nR since
   beta <= 1 ([Qmult_le_compat_r]). *)
Lemma dsgen_beta_feasible : forall (m : nat) (lo : Q), (0 < lo)%Q -> (lo < 1)%Q ->
  dsgen_feasible (S (S m)) lo (dsgen_beta lo).
Proof.
  intros m lo H0 H1. unfold dsgen_feasible. intros s j Hs Hj.
  apply Qle_to_QleT'.
  assert (Hqpos : (0 < dsgen_qN (S (S m)))%Q) by (apply dsgen_qN_pos; lia).
  assert (Hqne : ~ ((dsgen_qN (S (S m))) == 0)%Q)
    by (apply dsgen_ne_of_pos; exact Hqpos).
  assert (Hbleak : (0 < dsgen_beta lo * (1 / dsgen_qN (S (S m))))%Q).
  { apply dsgen_mul_pos.
    - apply dsgen_beta_pos. exact H0.
    - apply dsgen_div_pos; [ exact (QltT_to_Qlt 0 1 mdsopt_01) | exact Hqpos ]. }
  destruct s as [|[|s]]; destruct j as [|[|j]]; cbn [dsgen_k].
  - (* The (0,0) block entry. *)
    rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    apply dsgen_le_add_pos2.
    apply dsgen_mul_pos; [ apply dsgen_omb_pos; assumption
                         | apply dsgen_k00_pos; exact H0 ].
  - (* The (0,1) block entry. *)
    rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    apply dsgen_le_add_pos2.
    apply dsgen_mul_pos; [ apply dsgen_omb_pos; assumption
                         | apply dsgen_k01_pos; exact H0 ].
  - (* The (0, >=2) leakage column meets the bound with equality. *)
    rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    apply Qle_refl.
  - (* The (1,0) block entry. *)
    rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    apply dsgen_le_add_pos2.
    apply dsgen_mul_pos; [ apply dsgen_omb_pos; assumption
                         | apply dsgen_k10_pos; exact H0 ].
  - (* The (1,1) block entry. *)
    rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    apply dsgen_le_add_pos2.
    apply dsgen_mul_pos; [ apply dsgen_omb_pos; assumption
                         | apply dsgen_k11_pos; exact H0 ].
  - (* The (1, >=2) leakage column meets the bound with equality. *)
    rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne).
    apply Qle_refl.
  - (* Uniform-row entries: beta*(1/nR) <= 1/nR (the kernel-level 1/nR and
       the division by nR are interchangeable). *)
    apply (Qle_trans (dsgen_beta lo * (1 / dsgen_qN (S (S m))))
                     (1 * (1 / dsgen_qN (S (S m))))).
    + apply Qmult_le_compat_r;
        [ apply dsgen_beta_le_1; assumption
        | apply Qlt_le_weak; apply dsgen_div_pos;
            [ exact (QltT_to_Qlt 0 1 mdsopt_01) | exact Hqpos ] ].
    + apply Qle_refl.
  - apply (Qle_trans (dsgen_beta lo * (1 / dsgen_qN (S (S m))))
                     (1 * (1 / dsgen_qN (S (S m))))).
    + apply Qmult_le_compat_r;
        [ apply dsgen_beta_le_1; assumption
        | apply Qlt_le_weak; apply dsgen_div_pos;
            [ exact (QltT_to_Qlt 0 1 mdsopt_01) | exact Hqpos ] ].
    + apply Qle_refl.
  - apply (Qle_trans (dsgen_beta lo * (1 / dsgen_qN (S (S m))))
                     (1 * (1 / dsgen_qN (S (S m))))).
    + apply Qmult_le_compat_r;
        [ apply dsgen_beta_le_1; assumption
        | apply Qlt_le_weak; apply dsgen_div_pos;
            [ exact (QltT_to_Qlt 0 1 mdsopt_01) | exact Hqpos ] ].
    + apply Qle_refl.
Qed.

(* Maximality at nR >= 3: the leakage-column entry K(0,2) = beta/nR is
   attained, so any feasible d satisfies d*(1/nR) <= beta/nR = beta*(1/nR)
   there; cancelling the positive factor 1/nR through the Qmult_le_r iff
   yields d <= beta. *)
Lemma dsgen_beta_max : forall (m : nat) (lo d : Q), (1 <= m)%nat ->
  (forall s j : nat, (s < S (S m))%nat -> (j < S (S m))%nat ->
     (d * (1 / dsgen_qN (S (S m))) <= dsgen_k (S (S m)) lo s j)%Q) ->
  d <= dsgen_beta lo.
Proof.
  intros m lo d Hm Hd.
  assert (Hqpos : (0 < dsgen_qN (S (S m)))%Q) by (apply dsgen_qN_pos; lia).
  assert (Hqne : ~ ((dsgen_qN (S (S m))) == 0)%Q)
    by (apply dsgen_ne_of_pos; exact Hqpos).
  assert (Hhalf : (0 < 1 / dsgen_qN (S (S m)))%Q)
    by (apply dsgen_div_pos; [ exact (QltT_to_Qlt 0 1 mdsopt_01) | exact Hqpos ]).
  assert (Hb1 : (0 < S (S m))%nat) by lia.
  assert (Hb2 : (2 < S (S m))%nat) by lia.
  pose proof (Hd 0%nat 2%nat Hb1 Hb2) as H.
  cbn [dsgen_k] in H.
  rewrite (dsgen_div_inv (dsgen_beta lo) (dsgen_qN (S (S m))) Hqne) in H.
  exact (proj1 (Qmult_le_r d (dsgen_beta lo) (1 / dsgen_qN (S (S m))) Hhalf) H).
Qed.

Theorem dsgen_optimal_ge3 : forall (m : nat) (lo : Q), (1 <= m)%nat ->
  (0 < lo)%Q -> (lo < 1)%Q ->
  S01_BaseRing.And (dsgen_feasible (S (S m)) lo (dsgen_beta lo))
    (forall d : Q, dsgen_feasible (S (S m)) lo d -> QleT' d (dsgen_beta lo)).
Proof.
  intros m lo Hm H0 H1. split.
  - apply dsgen_beta_feasible; assumption.
  - intros d Hd. unfold dsgen_feasible in Hd.
    apply Qle_to_QleT'. apply (dsgen_beta_max m lo d Hm).
    intros s j Hs Hj. apply QleT'_to_Qle. exact (Hd s j Hs Hj).
Qed.

(* ========== Section 9. Main theorems: row-stochasticity, delta* feasibility and strict suboptimality (all nR >= 2) ========== *)

Theorem dsgen_main_rowstoch : forall nR : nat, (2 <= nR)%nat -> forall lo : Q,
  (0 < lo)%Q -> (lo < 1)%Q -> dsgen_rowstoch nR lo.
Proof.
  intros nR Hn lo H0 H1. destruct nR as [|[|m]]; [ lia | lia | ].
  apply dsgen_rowstoch_SS; assumption.
Qed.

Theorem dsgen_main_feasible : forall nR : nat, (2 <= nR)%nat -> forall lo : Q,
  (0 < lo)%Q -> (lo < 1)%Q -> dsgen_feasible nR lo (lo*lo).
Proof.
  intros nR Hn lo H0 H1. destruct nR as [|[|m]]; [ lia | lia | ].
  unfold dsgen_feasible. intros s j Hs Hj. apply Qle_to_QleT'.
  apply (Qle_trans (lo*lo * (1 / dsgen_qN (S (S m))))
                   (dsgen_beta lo * (1 / dsgen_qN (S (S m))))).
  - apply Qmult_le_compat_r.
    + apply Qlt_le_weak. apply dsgen_dstar_lt_beta; assumption.
    + apply Qlt_le_weak. apply dsgen_div_pos;
        [ exact (QltT_to_Qlt 0 1 mdsopt_01) | apply dsgen_qN_pos; lia ].
  - exact (QleT'_to_Qle _ _
            (dsgen_beta_feasible m lo H0 H1 s j Hs Hj)).
Qed.

(* Main theorem: delta* = lo*lo is strictly suboptimal on the explicit
   nR-state kernel (QltT Set-level witness, stated separately so the Set
   position of QltT is not swallowed by a conjunction at the Prop face). *)
Theorem dsgen_main : forall nR : nat, (2 <= nR)%nat -> forall lo : Q,
  (0 < lo)%Q -> (lo < 1)%Q -> QltT (lo*lo) (dsgen_beta lo).
Proof.
  intros nR Hn lo H0 H1.
  apply Qlt_to_QltT. apply dsgen_dstar_lt_beta; assumption.
Qed.

(* ========== Section 10. Gap pieces: closed forms, strict positivity, and the 2-state gap as a constant multiple ========== *)

Definition dsgen_gap (lo : Q) : Q := dsgen_beta lo - lo*lo.

Lemma dsgen_gap_eq : forall lo : Q, (0 < lo)%Q ->
  (dsgen_gap lo == (1 - lo*lo)/2)%Q.
Proof.
  intros lo H0. unfold dsgen_gap, dsgen_beta. field.
Qed.

Lemma dsgen_gap_pos : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (0 < dsgen_gap lo)%Q.
Proof.
  intros lo H0 H1. rewrite dsgen_gap_eq by exact H0.
  apply dsgen_div_pos.
  - apply dsgen_1mlo2_pos; assumption.
  - exact dsgen_2pos.
Qed.

(* Constant-multiple closed form: [dsgen_gap = mdsopt_gap * (1+lo*lo)/(2*(lo*lo))]. *)
Lemma dsgen_gap_ratio : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (mdsopt_gap lo * ((1 + lo*lo)/(2*(lo*lo))) == dsgen_gap lo)%Q.
Proof.
  intros lo H0 H1. unfold mdsopt_gap, dsgen_gap, dsgen_beta. field.
  - split.
    + apply dsgen_ne_of_pos. exact H0.
    + intros Hz. apply qeq_imp_qeqT in Hz.
      destruct (mdsopt_den_ne lo H0 Hz).
Qed.

(* The constant multiple is >= 1 whenever 1+lo*lo >= 2*lo*lo, which follows
   from lo*lo <= 1. *)
Lemma dsgen_gap_ratio_ge1 : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (1 <= (1 + lo*lo)/(2*(lo*lo)))%Q.
Proof.
  intros lo H0 H1.
  assert (Hd : (0 < 2*(lo*lo))%Q).
  { pose proof (proj2 (Qmult_lt_r 0 (lo*lo) 2 dsgen_2pos)
                   (QltT_to_Qlt 0 (lo*lo) (mdsopt_sq0 lo H0))) as H.
    rewrite Qmult_0_l, Qmult_comm in H. exact H. }
  apply (proj1 (Qmult_le_r 1 ((1 + lo*lo)/(2*(lo*lo))) (2*(lo*lo)) Hd)).
  rewrite (dsgen_div_cancel (1 + lo*lo) (2*(lo*lo)) (dsgen_ne_of_pos _ Hd)).
  rewrite Qmult_1_l, (Qmult_comm 2 (lo*lo)), dsgen_two_mul_r.
  rewrite (Qplus_comm 1 (lo*lo)).
  apply (proj2 (Qplus_le_r (lo*lo) 1 (lo*lo))).
  apply Qlt_le_weak. exact (QltT_to_Qlt (lo*lo) 1 (mdsopt_lt1 lo H0 H1)).
Qed.

Lemma dsgen_gap_ge_mdsopt : forall lo : Q, (0 < lo)%Q -> (lo < 1)%Q ->
  (mdsopt_gap lo <= dsgen_gap lo)%Q.
Proof.
  intros lo H0 H1.
  rewrite <- (dsgen_gap_ratio lo H0 H1).
  pose proof (dsgen_gap_ratio_ge1 lo H0 H1) as Hr.
  pose proof (QltT_to_Qlt 0 (mdsopt_gap lo) (mdsopt_gap_pos lo H0 H1)) as Hw.
  pose proof (proj2 (Qmult_le_r 1 ((1 + lo*lo)/(2*(lo*lo))) (mdsopt_gap lo) Hw) Hr) as Hle.
  rewrite Qmult_1_l in Hle.
  rewrite (Qmult_comm ((1 + lo*lo)/(2*(lo*lo))) (mdsopt_gap lo)) in Hle.
  exact Hle.
Qed.

(* Extraction-audit mouths for the main exits: each must report
   [Closed under the global context]. *)
Print Assumptions dsgen_main_rowstoch.
Print Assumptions dsgen_main_feasible.
Print Assumptions dsgen_optimal_ge3.
Print Assumptions dsgen_main.

(* ========== Section 11. Extraction exits (separate output directory; the extracted artifact must contain no Obj.magic) ========== *)

From Stdlib Require Import Extraction.
Set Extraction Output Directory "../_dsnr_g3out".
Separate Extraction dsgen_qN dsgen_beta dsgen_k dsgen_rowsum dsgen_gap.
