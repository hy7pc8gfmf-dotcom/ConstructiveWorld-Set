(* ConstructiveWorld-Set — norm convergence and Cauchy criteria for series. *)

(** * UpReqNormConv: norm domination, Mertens theorem and Cauchy criteria.

    Mission.  Norm domination lemmas ([ncv_norm_sum_le], [ncv_norm_row_le],
 [ncv_norm_conv_le]), Mertens theorem for double series [ncv_mertens],
 the rectangular Cauchy criterion [ncv_conv_rect_cauchy] with diagonal
 corollary [ncv_conv_diag_cauchy], and the scalar lemmas
 [ncv_qmult_lt0], [ncv_qsum_scalar_l].

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Setoid], [Morphisms],
 [Lia]. Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
 [UpReqBanachExp] of this development.

    References.  This development, UpReqNormConv.v, the baseline module in
 ConstructiveWorld-Main whose statement names are carried over here
 verbatim (statement-face Set-carrier completion: [==] equalities
 moved to [QeqT], [Qlt] to [QltT]).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqNormConv.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Section 1. Definitions: Q-valued finite sums and tail sums, and   *)
(*   BA-valued row sums and rectangular partial sums of the product.  *)
(* ============================================================ *)

(* Q-valued finite sum: [ncv_qsum f n = sum_{k<n} f k]. *)
Fixpoint ncv_qsum (f : nat -> Q) (n : nat) : Q :=
  match n with
  | 0%nat => 0%Q
  | Datatypes.S m => (ncv_qsum f m + f m)%Q
  end.

(* Q-valued tail sum [ncv_qtail f m n = sum_{m<=k<n} f k], guarded by
   [Nat.leb] so an empty range (n < m) yields 0 without truncated
   nat subtraction. *)
Fixpoint ncv_qtail (f : nat -> Q) (m n : nat) : Q :=
  match n with
  | 0%nat => 0%Q
  | Datatypes.S n' => (ncv_qtail f m n' + (if Nat.leb m n' then f n' else 0%Q))%Q
  end.

(* BA-valued finite sum: [ncv_sum _ _ B x n = sum_{k<n} x k]. *)
Fixpoint ncv_sum (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x : nat -> BA) (n : nat) : BA :=
  match n with
  | 0%nat => @bzero _ _ B
  | Datatypes.S m => @bplus _ _ B (ncv_sum _ _ B x m) (x m)
  end.

(* Convolution row: [ncv_row _ _ B a b k n = sum_{j<n} (a k) * (b j)]. *)
Definition ncv_row (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : nat -> BA) (k n : nat) : BA :=
  ncv_sum _ _ B (fun j => @bmult _ _ B (a k) (b j)) n.

(* Rectangular partial sum: [C m n = sum_{k<m} sum_{j<n} (a k) * (b j)]. *)
Fixpoint ncv_conv (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : nat -> BA) (m n : nat) : BA :=
  match m with
  | 0%nat => @bzero _ _ B
  | Datatypes.S m' => @bplus _ _ B (ncv_conv _ _ B a b m' n) (ncv_row _ _ B a b m' n)
  end.

(* ============================================================ *)
(* Section 2a. The Q-side finite-sum engine: nonnegativity, pointwise *)
(*   monotonicity, scalar extraction, tail sums.                       *)
(* ============================================================ *)

Lemma ncv_qsum_nonneg : forall (f : nat -> Q) (n : nat),
  (forall k : nat, QleT' 0 (f k)) -> QleT' 0 (ncv_qsum f n).
Proof.
  intros f n Hf. induction n as [| m IH].
  - change (ncv_qsum f 0%nat) with 0%Q. apply qleT'_refl.
  - change (ncv_qsum f (Datatypes.S m)) with (ncv_qsum f m + f m)%Q.
    apply Qle_to_QleT'.
    apply (Qle_trans _ (0 + 0)%Q).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    + apply (Qplus_le_compat 0 (ncv_qsum f m) 0 (f m)).
      * apply QleT'_to_Qle. exact IH.
      * apply QleT'_to_Qle. exact (Hf m).
Qed.

Lemma ncv_qsum_le : forall (f g : nat -> Q) (n : nat),
  (forall k : nat, QleT' (f k) (g k)) -> QleT' (ncv_qsum f n) (ncv_qsum g n).
Proof.
  intros f g n Hle. induction n as [| m IH].
  - change (ncv_qsum f 0%nat) with 0%Q. change (ncv_qsum g 0%nat) with 0%Q.
    apply qleT'_refl.
  - change (ncv_qsum f (Datatypes.S m)) with (ncv_qsum f m + f m)%Q.
    change (ncv_qsum g (Datatypes.S m)) with (ncv_qsum g m + g m)%Q.
    apply (qleT'_plus_compat _ _ _ _).
    + exact IH.
    + exact (Hle m).
Qed.

Lemma ncv_qsum_scalar_l : forall (c : Q) (f : nat -> Q) (n : nat),
  QeqT (ncv_qsum (fun k => (c * f k)%Q) n) ((c * ncv_qsum f n)%Q).
Proof.
  intros c f n. apply qeq_imp_qeqT. induction n as [| m IH].
  - change (ncv_qsum (fun k => (c * f k)%Q) 0%nat) with 0%Q.
    change (ncv_qsum f 0%nat) with 0%Q.
    ring.
  - change (ncv_qsum (fun k => (c * f k)%Q) (Datatypes.S m))
      with (ncv_qsum (fun k => (c * f k)%Q) m + (c * f m)%Q)%Q.
    change (ncv_qsum f (Datatypes.S m)) with (ncv_qsum f m + f m)%Q.
    rewrite IH. ring.
Qed.

Lemma ncv_qtail_nonneg : forall (f : nat -> Q) (m n : nat),
  (forall k : nat, QleT' 0 (f k)) -> QleT' 0 (ncv_qtail f m n).
Proof.
  intros f m n Hf. induction n as [| n' IH].
  - change (ncv_qtail f m 0%nat) with 0%Q. apply qleT'_refl.
  - change (ncv_qtail f m (Datatypes.S n'))
      with (ncv_qtail f m n' + (if Nat.leb m n' then f n' else 0%Q))%Q.
    apply Qle_to_QleT'.
    apply (Qle_trans _ (0 + 0)%Q).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    + apply (Qplus_le_compat 0 (ncv_qtail f m n') 0 (if Nat.leb m n' then f n' else 0%Q)).
      * apply QleT'_to_Qle. exact IH.
      * apply QleT'_to_Qle. destruct (Nat.leb m n').
        -- exact (Hf n').
        -- apply qleT'_refl.
Qed.

Lemma ncv_qtail_le_m : forall (f : nat -> Q) (m n : nat),
  (n <= m)%nat -> QeqT (ncv_qtail f m n) 0%Q.
Proof.
  intros f m n Hn. apply qeq_imp_qeqT. induction n as [| n' IH].
  - reflexivity.
  - change (ncv_qtail f m (Datatypes.S n'))
      with (ncv_qtail f m n' + (if Nat.leb m n' then f n' else 0%Q))%Q.
    assert (Hle : Nat.leb m n' = false).
    { apply (proj2 (Nat.leb_gt m n')). lia. }
    assert (Hn'le : (n' <= m)%nat) by lia.
    rewrite Hle. rewrite (IH Hn'le). ring.
Qed.

(* A tail sum is bounded by the prefix sum over the same endpoints
   (pointwise nonnegativity; used by the Cauchy assembly). *)
Lemma ncv_qtail_le_qsum : forall (f : nat -> Q) (m n : nat),
  (forall k : nat, QleT' 0 (f k)) -> QleT' (ncv_qtail f m n) (ncv_qsum f n).
Proof.
  intros f m n Hf. induction n as [| n' IH].
  - change (ncv_qtail f m 0%nat) with 0%Q.
    change (ncv_qsum f 0%nat) with 0%Q.
    apply qleT'_refl.
  - change (ncv_qtail f m (Datatypes.S n'))
      with (ncv_qtail f m n' + (if Nat.leb m n' then f n' else 0%Q))%Q.
    change (ncv_qsum f (Datatypes.S n')) with (ncv_qsum f n' + f n')%Q.
    apply (qleT'_plus_compat _ _ _ _).
    + exact IH.
    + destruct (Nat.leb m n').
      * apply qleT'_refl.
      * exact (Hf n').
Qed.

(* ============================================================ *)
(* Section 2b. Norm triangle engine: the norm of a finite sum is     *)
(*   at most the sum of the norms (induction on the subadditivity     *)
(*   field).                                                          *)
(* ============================================================ *)

Lemma ncv_norm_sum_le : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x : nat -> BA) (n : nat),
  QleT' (@bnorm _ _ B (ncv_sum _ _ B x n)) (ncv_qsum (fun k => @bnorm _ _ B (x k)) n).
Proof.
  intros BA bae B x n. induction n as [| m IH].
  - change (ncv_sum _ _ B x 0%nat) with (@bzero _ _ B).
    rewrite (@bnorm_zero _ _ B).
    change (ncv_qsum (fun k => @bnorm _ _ B (x k)) 0%nat) with 0%Q.
    apply qleT'_refl.
  - change (ncv_sum _ _ B x (Datatypes.S m)) with (@bplus _ _ B (ncv_sum _ _ B x m) (x m)).
    change (ncv_qsum (fun k => @bnorm _ _ B (x k)) (Datatypes.S m))
      with (ncv_qsum (fun k => @bnorm _ _ B (x k)) m + @bnorm _ _ B (x m))%Q.
    eapply qleT'_trans.
    + exact (@bnorm_plus _ _ B (ncv_sum _ _ B x m) (x m)).
    + apply (qleT'_plus_compat _ _ _ _).
      * exact IH.
      * apply qleT'_refl.
Qed.

(* Row norm bound: the norm of row [k] is at most [norm (a k)] times
   the Q-sum of [norm (b j)] over [j < n]. *)
Lemma ncv_norm_row_le : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : nat -> BA) (k n : nat),
  QleT' (@bnorm _ _ B (ncv_row _ _ B a b k n))
        (@bnorm _ _ B (a k) * ncv_qsum (fun j => @bnorm _ _ B (b j)) n)%Q.
Proof.
  intros BA bae B a b k n. unfold ncv_row.
  eapply qleT'_trans.
  - exact (ncv_norm_sum_le _ _ B (fun j => @bmult _ _ B (a k) (b j)) n).
  - eapply qleT'_trans.
    + apply (ncv_qsum_le (fun j => @bnorm _ _ B (@bmult _ _ B (a k) (b j)))
                         (fun j => (@bnorm _ _ B (a k) * @bnorm _ _ B (b j))%Q) n).
      intros j. exact (@bnorm_mult _ _ B (a k) (b j)).
    + apply qeq_leT'.
      exact (ncv_qsum_scalar_l (@bnorm _ _ B (a k)) (fun j => @bnorm _ _ B (b j)) n).
Qed.

(* Anchor bound: [norm (C m n) <= (sum_{k<m} norm (a k)) * (sum_{j<n} norm (b j))]. *)
Lemma ncv_norm_conv_le : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : nat -> BA) (m n : nat),
  QleT' (@bnorm _ _ B (ncv_conv _ _ B a b m n))
        (ncv_qsum (fun k => @bnorm _ _ B (a k)) m * ncv_qsum (fun j => @bnorm _ _ B (b j)) n)%Q.
Proof.
  intros BA bae B a b m n. induction m as [| m' IH].
  - change (ncv_conv _ _ B a b 0%nat n) with (@bzero _ _ B).
    rewrite (@bnorm_zero _ _ B).
    change (ncv_qsum (fun k => @bnorm _ _ B (a k)) 0%nat) with 0%Q.
    apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - change (ncv_conv _ _ B a b (Datatypes.S m') n)
      with (@bplus _ _ B (ncv_conv _ _ B a b m' n) (ncv_row _ _ B a b m' n)).
    change (ncv_qsum (fun k => @bnorm _ _ B (a k)) (Datatypes.S m'))
      with (ncv_qsum (fun k => @bnorm _ _ B (a k)) m' + @bnorm _ _ B (a m'))%Q.
    eapply qleT'_trans.
    + exact (@bnorm_plus _ _ B (ncv_conv _ _ B a b m' n) (ncv_row _ _ B a b m' n)).
    + eapply qleT'_trans.
      * apply (qleT'_plus_compat _
                 (ncv_qsum (fun k => @bnorm _ _ B (a k)) m' * ncv_qsum (fun j => @bnorm _ _ B (b j)) n)%Q
                 _
                 ((@bnorm _ _ B (a m')) * ncv_qsum (fun j => @bnorm _ _ B (b j)) n)%Q).
        -- exact IH.
        -- exact (ncv_norm_row_le _ _ B a b m' n).
      * apply qeq_leT'. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* Section 3a. Rearrangement lemmas at the carrier-equality level.   *)
(* ============================================================ *)

(* The additive inverse is involutive: [bopp (bopp a) = a]. *)
Lemma ncv_bopp_bopp : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA),
  bae (@bopp _ _ B (@bopp _ _ B a)) a.
Proof.
  intros BA bae B a.
  apply (@bae_sym _ _ B a (@bopp _ _ B (@bopp _ _ B a))).
  apply (@bopp_unique BA bae B a (@bopp _ _ B a)).
  exact (@bplus_opp _ _ B a).
Qed.

(* The negative of a sum splits: [bopp (y + v) = (bopp y) + (bopp v)]. *)
Lemma ncv_bae_opp_plus : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (y v : BA),
  bae (@bopp _ _ B (@bplus _ _ B y v)) (@bplus _ _ B (@bopp _ _ B y) (@bopp _ _ B v)).
Proof.
  intros BA bae B y v.
  eapply bae_trans.
  { apply (@bopp_wd _ _ B (@bplus _ _ B y v) (@bplus _ _ B y (@bopp _ _ B (@bopp _ _ B v)))).
    apply (@bplus_wd_r BA bae B v (@bopp _ _ B (@bopp _ _ B v)) y).
    apply (@bae_sym _ _ B _ _ (ncv_bopp_bopp _ _ B v)). }
  { apply (@bae_sym _ _ B _ _ (@bplus_opp_swap BA bae B y (@bopp _ _ B v))). }
Qed.

(* Difference telescoping: [x - z = (x - y) + (y - z)] (inserting the
   intermediate point [y]). *)
Lemma ncv_bae_diff_join : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x y z : BA),
  bae (@bplus _ _ B (@bplus _ _ B x (@bopp _ _ B y)) (@bplus _ _ B y (@bopp _ _ B z)))
        (@bplus _ _ B x (@bopp _ _ B z)).
Proof.
  intros BA bae B x y z.
  eapply bae_trans.
  { exact (@bplus_assoc _ _ B (@bplus _ _ B x (@bopp _ _ B y)) y (@bopp _ _ B z)). }
  eapply bae_trans.
  { exact (@bplus_wd_l BA bae B (@bplus _ _ B (@bplus _ _ B x (@bopp _ _ B y)) y)
             (@bplus _ _ B x (@bplus _ _ B (@bopp _ _ B y) y)) (@bopp _ _ B z)
             (@bae_sym _ _ B _ _ (@bplus_assoc _ _ B x (@bopp _ _ B y) y))). }
  eapply bae_trans.
  { exact (@bplus_wd_l BA bae B (@bplus _ _ B x (@bplus _ _ B (@bopp _ _ B y) y))
             (@bplus _ _ B x (@bplus _ _ B y (@bopp _ _ B y))) (@bopp _ _ B z)
             (@bplus_wd_r BA bae B (@bplus _ _ B (@bopp _ _ B y) y) (@bplus _ _ B y (@bopp _ _ B y)) x
                (@bplus_comm _ _ B (@bopp _ _ B y) y))). }
  eapply bae_trans.
  { exact (@bplus_wd_l BA bae B (@bplus _ _ B x (@bplus _ _ B y (@bopp _ _ B y))) (@bplus _ _ B x (@bzero _ _ B))
             (@bopp _ _ B z)
             (@bplus_wd_r BA bae B (@bplus _ _ B y (@bopp _ _ B y)) (@bzero _ _ B) x (@bplus_opp _ _ B y))). }
  exact (@bplus_wd_l BA bae B (@bplus _ _ B x (@bzero _ _ B)) x (@bopp _ _ B z) (@bplus_zero _ _ B x)).
Qed.

(* Four-corner rearrangement: [(x + u) - (y + v) = (x - y) + (u - v)]. *)
Lemma ncv_bae_quad : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x y u v : BA),
  bae (@bplus _ _ B (@bplus _ _ B x u) (@bopp _ _ B (@bplus _ _ B y v)))
        (@bplus _ _ B (@bplus _ _ B x (@bopp _ _ B y)) (@bplus _ _ B u (@bopp _ _ B v))).
Proof.
  intros BA bae B x y u v.
  eapply bae_trans.
  { exact (@bplus_wd_r BA bae B (@bopp _ _ B (@bplus _ _ B y v)) (@bplus _ _ B (@bopp _ _ B y) (@bopp _ _ B v))
             (@bplus _ _ B x u) (ncv_bae_opp_plus _ _ B y v)). }
  eapply bae_trans.
  { exact (@bae_sym _ _ B _ _ (@bplus_assoc _ _ B x u (@bplus _ _ B (@bopp _ _ B y) (@bopp _ _ B v)))). }
  eapply bae_trans.
  { exact (@bplus_wd_r BA bae B (@bplus _ _ B u (@bplus _ _ B (@bopp _ _ B y) (@bopp _ _ B v)))
             (@bplus _ _ B (@bplus _ _ B (@bopp _ _ B y) u) (@bopp _ _ B v)) x
             (@bae_trans _ _ B _ _ _
                (@bplus_assoc _ _ B u (@bopp _ _ B y) (@bopp _ _ B v))
                (@bplus_wd_l BA bae B (@bplus _ _ B u (@bopp _ _ B y)) (@bplus _ _ B (@bopp _ _ B y) u)
                   (@bopp _ _ B v) (@bplus_comm _ _ B u (@bopp _ _ B y))))). }
  eapply bae_trans.
  { exact (@bplus_assoc _ _ B x (@bplus _ _ B (@bopp _ _ B y) u) (@bopp _ _ B v)). }
  eapply bae_trans.
  { exact (@bplus_wd_l BA bae B (@bplus _ _ B x (@bplus _ _ B (@bopp _ _ B y) u))
             (@bplus _ _ B (@bplus _ _ B x (@bopp _ _ B y)) u) (@bopp _ _ B v)
             (@bplus_assoc _ _ B x (@bopp _ _ B y) u)). }
  exact (@bae_sym _ _ B _ _ (@bplus_assoc _ _ B (@bplus _ _ B x (@bopp _ _ B y)) u (@bopp _ _ B v))).
Qed.

(* The norm difference is symmetric up to [QeqT]:
   [norm (x - y) = norm (y - x)]; the statement is carried in the
   [QeqT] face since the carrier equality is not a decidable identity. *)
Lemma ncv_norm_diff_sym : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x y : BA),
  QeqT (@bnorm _ _ B (@bplus _ _ B x (@bopp _ _ B y))) (@bnorm _ _ B (@bplus _ _ B y (@bopp _ _ B x))).
Proof.
  intros BA bae B x y.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (@bnorm _ _ B (@bplus _ _ B (@bopp _ _ B y) x))).
  - apply qeqT_imp_qeq. exact (@bnorm_wd _ _ B _ _ (@bplus_comm _ _ B x (@bopp _ _ B y))).
  - apply (Qeq_trans _ (@bnorm _ _ B (@bopp _ _ B (@bplus _ _ B y (@bopp _ _ B x))))).
    + apply qeqT_imp_qeq. exact (@bnorm_wd _ _ B _ _ (@bplus_opp_swap BA bae B y x)).
    + rewrite (@bnorm_opp _ _ B (@bplus _ _ B y (@bopp _ _ B x))). apply Qeq_refl.
Qed.

(* Interpolation triangle: [norm (x - z) <= norm (x - y) + norm (y - z)]. *)
Lemma ncv_norm_triangle_via : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x y z : BA),
  QleT' (@bnorm _ _ B (@bplus _ _ B x (@bopp _ _ B z)))
        (@bnorm _ _ B (@bplus _ _ B x (@bopp _ _ B y)) + @bnorm _ _ B (@bplus _ _ B y (@bopp _ _ B z)))%Q.
Proof.
  intros BA bae B x y z.
  eapply (QeqT_Qle_bool_cong _ _ _ (@bnorm_wd _ _ B _ _ (ncv_bae_diff_join _ _ B x y z))).
  exact (@bnorm_plus _ _ B (@bplus _ _ B x (@bopp _ _ B y)) (@bplus _ _ B y (@bopp _ _ B z))).
Qed.

(* Four-corner triangle: [norm ((x+u)-(y+v)) <= norm (x-y) + norm (u-v)]. *)
Lemma ncv_norm_quad_le : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x y u v : BA),
  QleT' (@bnorm _ _ B (@bplus _ _ B (@bplus _ _ B x u) (@bopp _ _ B (@bplus _ _ B y v))))
        (@bnorm _ _ B (@bplus _ _ B x (@bopp _ _ B y)) + @bnorm _ _ B (@bplus _ _ B u (@bopp _ _ B v)))%Q.
Proof.
  intros BA bae B x y u v.
  eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _ (ncv_bae_quad _ _ B x y u v)))).
  exact (@bnorm_plus _ _ B (@bplus _ _ B x (@bopp _ _ B y)) (@bplus _ _ B u (@bopp _ _ B v))).
Qed.

(* ============================================================ *)
(* Section 3b. Block norm-difference bounds (row difference, column   *)
(*   difference, row block) feeding the Mertens estimate.             *)
(* ============================================================ *)

(* Row difference: for [n1 <= n2],
   [norm (row k n2 - row k n1) <= norm (a k) * (tail of norms of b over [n1,n2))]. *)
Lemma ncv_norm_row_diff_le : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : nat -> BA) (k n1 n2 : nat),
  (n1 <= n2)%nat ->
  QleT' (@bnorm _ _ B (@bplus _ _ B (ncv_row _ _ B a b k n2) (@bopp _ _ B (ncv_row _ _ B a b k n1))))
        (@bnorm _ _ B (a k) * ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n2)%Q.
Proof.
  intros BA bae B a b k n1 n2. revert n2.
  induction n2 as [| n' IH]; intros Hn2.
  - assert (Hn10 : n1 = 0%nat) by lia. subst n1.
    change (ncv_row _ _ B a b k 0%nat) with (@bzero _ _ B).
    eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _ (@bplus_opp _ _ B (@bzero _ _ B))))).
    rewrite (@bnorm_zero _ _ B).
    change (ncv_qtail (fun j => @bnorm _ _ B (b j)) 0%nat 0%nat) with 0%Q.
    apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - destruct (Nat.leb n1 n') eqn:En.
    + assert (Hn1n' : (n1 <= n')%nat) by (apply Nat.leb_le; exact En).
      change (ncv_row _ _ B a b k (Datatypes.S n'))
        with (@bplus _ _ B (ncv_row _ _ B a b k n') (@bmult _ _ B (a k) (b n'))).
      eapply (QeqT_Qle_bool_cong _ _ _
        (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _
        (@bplus_middle_swap BA bae B (ncv_row _ _ B a b k n') (@bmult _ _ B (a k) (b n'))
                            (@bopp _ _ B (ncv_row _ _ B a b k n1)))))).
      eapply qleT'_trans.
      * exact (@bnorm_plus _ _ B (@bplus _ _ B (ncv_row _ _ B a b k n') (@bopp _ _ B (ncv_row _ _ B a b k n1)))
                            (@bmult _ _ B (a k) (b n'))).
      * change (ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 (Datatypes.S n'))
          with (ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n'
                + (if Nat.leb n1 n' then @bnorm _ _ B (b n') else 0%Q))%Q.
        rewrite En.
        eapply qleT'_trans.
        -- apply (qleT'_plus_compat _
                     (@bnorm _ _ B (a k) * ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n')%Q
                     _
                     (@bnorm _ _ B (a k) * @bnorm _ _ B (b n'))%Q).
           ++ exact (IH Hn1n').
           ++ exact (@bnorm_mult _ _ B (a k) (b n')).
        -- apply qeq_leT'. apply qeq_imp_qeqT. ring.
    + assert (Hn'1 : (n' < n1)%nat) by (apply (proj1 (Nat.leb_gt n1 n')); exact En).
      assert (Hn1S : n1 = Datatypes.S n') by lia. subst n1.
      change (ncv_row _ _ B a b k (Datatypes.S n'))
        with (@bplus _ _ B (ncv_row _ _ B a b k n') (@bmult _ _ B (a k) (b n'))).
      eapply (QeqT_Qle_bool_cong _ _ _
        (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _
        (@bplus_opp _ _ B (@bplus _ _ B (ncv_row _ _ B a b k n') (@bmult _ _ B (a k) (b n'))))))).
      rewrite (@bnorm_zero _ _ B).
      change (ncv_qtail (fun j => @bnorm _ _ B (b j)) (Datatypes.S n') (Datatypes.S n'))
        with (ncv_qtail (fun j => @bnorm _ _ B (b j)) (Datatypes.S n') n'
              + (if Nat.leb (Datatypes.S n') n' then @bnorm _ _ B (b n') else 0%Q))%Q.
      rewrite En.
      assert (Hq0 : (ncv_qtail (fun j => @bnorm _ _ B (b j)) (Datatypes.S n') n' + 0%Q)%Q == 0%Q).
      { assert (Ht : ncv_qtail (fun j => @bnorm _ _ B (b j)) (Datatypes.S n') n' == 0%Q)
          by (apply qeqT_imp_qeq; apply ncv_qtail_le_m; apply Nat.le_succ_diag_r).
        rewrite Ht. ring. }
      assert (Hfull : ((@bnorm _ _ B (a k))
                       * (ncv_qtail (fun j => @bnorm _ _ B (b j)) (Datatypes.S n') n' + 0%Q))%Q
                      == 0%Q).
      { rewrite Hq0. ring. }
      apply (qeq_imp_qle 0%Q
               (@bnorm _ _ B (a k)
                  * (ncv_qtail (fun j => @bnorm _ _ B (b j)) (Datatypes.S n') n' + 0%Q))%Q).
      apply qeq_imp_qeqT. symmetry. exact Hfull.
Qed.

(* Column difference: for [n1 <= n2],
   [norm (C M n2 - C M n1) <= (sum_{k<M} norm (a k)) * (tail of norms of b over [n1,n2))]. *)
Lemma ncv_norm_conv_coldiff_le : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : nat -> BA) (M n1 n2 : nat),
  (n1 <= n2)%nat ->
  QleT' (@bnorm _ _ B (@bplus _ _ B (ncv_conv _ _ B a b M n2) (@bopp _ _ B (ncv_conv _ _ B a b M n1))))
        (ncv_qsum (fun k => @bnorm _ _ B (a k)) M * ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n2)%Q.
Proof.
  intros BA bae B a b M. induction M as [| M' IH]; intros n1 n2 Hn.
  - change (ncv_conv _ _ B a b 0%nat n2) with (@bzero _ _ B).
    change (ncv_conv _ _ B a b 0%nat n1) with (@bzero _ _ B).
    eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _ (@bplus_opp _ _ B (@bzero _ _ B))))).
    rewrite (@bnorm_zero _ _ B).
    change (ncv_qsum (fun k => @bnorm _ _ B (a k)) 0%nat) with 0%Q.
    apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - change (ncv_conv _ _ B a b (Datatypes.S M') n2)
      with (@bplus _ _ B (ncv_conv _ _ B a b M' n2) (ncv_row _ _ B a b M' n2)).
    change (ncv_conv _ _ B a b (Datatypes.S M') n1)
      with (@bplus _ _ B (ncv_conv _ _ B a b M' n1) (ncv_row _ _ B a b M' n1)).
    eapply (QeqT_Qle_bool_cong _ _ _
      (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _ (ncv_bae_quad _ _ B (ncv_conv _ _ B a b M' n2) (ncv_conv _ _ B a b M' n1)
                                         (ncv_row _ _ B a b M' n2) (ncv_row _ _ B a b M' n1))))).
    eapply qleT'_trans.
    + exact (@bnorm_plus _ _ B (@bplus _ _ B (ncv_conv _ _ B a b M' n2) (@bopp _ _ B (ncv_conv _ _ B a b M' n1)))
                          (@bplus _ _ B (ncv_row _ _ B a b M' n2) (@bopp _ _ B (ncv_row _ _ B a b M' n1)))).
    + change (ncv_qsum (fun k => @bnorm _ _ B (a k)) (Datatypes.S M'))
        with (ncv_qsum (fun k => @bnorm _ _ B (a k)) M' + @bnorm _ _ B (a M'))%Q.
      eapply qleT'_trans.
      * apply (qleT'_plus_compat _
                 (ncv_qsum (fun k => @bnorm _ _ B (a k)) M' * ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n2)%Q
                 _
                 ((@bnorm _ _ B (a M')) * ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n2)%Q).
        -- exact (IH n1 n2 Hn).
        -- exact (ncv_norm_row_diff_le _ _ B a b M' n1 n2 Hn).
      * apply qeq_leT'. apply qeq_imp_qeqT. ring.
Qed.

(* Row-block difference: for [M1 <= M2],
   [norm (C M2 n - C M1 n) <= (tail of norms of a over [M1,M2)) * (sum_{j<n} norm (b j))]. *)
Lemma ncv_norm_conv_rowdiff_le : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : nat -> BA) (M1 M2 n : nat),
  (M1 <= M2)%nat ->
  QleT' (@bnorm _ _ B (@bplus _ _ B (ncv_conv _ _ B a b M2 n) (@bopp _ _ B (ncv_conv _ _ B a b M1 n))))
        (ncv_qtail (fun k => @bnorm _ _ B (a k)) M1 M2 * ncv_qsum (fun j => @bnorm _ _ B (b j)) n)%Q.
Proof.
  intros BA bae B a b M1 M2 n. revert M1.
  induction M2 as [| M2' IH]; intros M1 HM.
  - assert (HM10 : M1 = 0%nat) by lia. subst M1.
    change (ncv_conv _ _ B a b 0%nat n) with (@bzero _ _ B).
    eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _ (@bplus_opp _ _ B (@bzero _ _ B))))).
    rewrite (@bnorm_zero _ _ B).
    change (ncv_qtail (fun k => @bnorm _ _ B (a k)) 0%nat 0%nat) with 0%Q.
    apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - destruct (Nat.leb M1 M2') eqn:EM.
    + assert (HM1M2' : (M1 <= M2')%nat) by (apply Nat.leb_le; exact EM).
      change (ncv_conv _ _ B a b (Datatypes.S M2') n)
        with (@bplus _ _ B (ncv_conv _ _ B a b M2' n) (ncv_row _ _ B a b M2' n)).
      eapply (QeqT_Qle_bool_cong _ _ _
        (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _
        (@bplus_middle_swap BA bae B (ncv_conv _ _ B a b M2' n) (ncv_row _ _ B a b M2' n)
                            (@bopp _ _ B (ncv_conv _ _ B a b M1 n)))))).
      eapply qleT'_trans.
      * exact (@bnorm_plus _ _ B (@bplus _ _ B (ncv_conv _ _ B a b M2' n) (@bopp _ _ B (ncv_conv _ _ B a b M1 n)))
                            (ncv_row _ _ B a b M2' n)).
      * change (ncv_qtail (fun k => @bnorm _ _ B (a k)) M1 (Datatypes.S M2'))
          with (ncv_qtail (fun k => @bnorm _ _ B (a k)) M1 M2'
                + (if Nat.leb M1 M2' then @bnorm _ _ B (a M2') else 0%Q))%Q.
        rewrite EM.
        eapply qleT'_trans.
        -- apply (qleT'_plus_compat _
                     (ncv_qtail (fun k => @bnorm _ _ B (a k)) M1 M2' * ncv_qsum (fun j => @bnorm _ _ B (b j)) n)%Q
                     _
                     ((@bnorm _ _ B (a M2')) * ncv_qsum (fun j => @bnorm _ _ B (b j)) n)%Q).
           ++ exact (IH M1 HM1M2').
           ++ exact (ncv_norm_row_le _ _ B a b M2' n).
        -- apply qeq_leT'. apply qeq_imp_qeqT. ring.
    + assert (HM2'1 : (M2' < M1)%nat) by (apply (proj1 (Nat.leb_gt M1 M2')); exact EM).
      assert (HMEq : M1 = Datatypes.S M2') by lia. subst M1.
      change (ncv_conv _ _ B a b (Datatypes.S M2') n)
        with (@bplus _ _ B (ncv_conv _ _ B a b M2' n) (ncv_row _ _ B a b M2' n)).
      eapply (QeqT_Qle_bool_cong _ _ _
        (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _
        (@bplus_opp _ _ B (@bplus _ _ B (ncv_conv _ _ B a b M2' n) (ncv_row _ _ B a b M2' n)))))).
      rewrite (@bnorm_zero _ _ B).
      change (ncv_qtail (fun k => @bnorm _ _ B (a k)) (Datatypes.S M2') (Datatypes.S M2'))
        with (ncv_qtail (fun k => @bnorm _ _ B (a k)) (Datatypes.S M2') M2'
              + (if Nat.leb (Datatypes.S M2') M2' then @bnorm _ _ B (a M2') else 0%Q))%Q.
      rewrite EM.
      assert (Hq0 : (ncv_qtail (fun k => @bnorm _ _ B (a k)) (Datatypes.S M2') M2' + 0%Q)%Q == 0%Q).
      { assert (Ht : ncv_qtail (fun k => @bnorm _ _ B (a k)) (Datatypes.S M2') M2' == 0%Q)
          by (apply qeqT_imp_qeq; apply ncv_qtail_le_m; apply Nat.le_succ_diag_r).
        rewrite Ht. ring. }
      assert (Hfull : ((ncv_qtail (fun k => @bnorm _ _ B (a k)) (Datatypes.S M2') M2' + 0%Q)
                       * ncv_qsum (fun j => @bnorm _ _ B (b j)) n)%Q == 0%Q).
      { rewrite Hq0. ring. }
      apply (qeq_imp_qle 0%Q
               ((ncv_qtail (fun k => @bnorm _ _ B (a k)) (Datatypes.S M2') M2' + 0%Q)
                * ncv_qsum (fun j => @bnorm _ _ B (b j)) n)%Q).
      apply qeq_imp_qeqT. symmetry. exact Hfull.
Qed.

(* ============================================================ *)
(* Section 3, main statement: the Mertens core estimate with explicit *)
(*   bounds.  Prefix controls [sum norm a <= Ba] and [sum norm b <= Bb] *)
(*   give [norm (C m2 n2 - C m1 n1) <= Ba*(b tail n1..n2) + Bb*(a tail m1..m2)]. *)
(* ============================================================ *)

Lemma ncv_mertens : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : nat -> BA) (Ba Bb : Q),
  (forall K : nat, QleT' (ncv_qsum (fun k => @bnorm _ _ B (a k)) K) Ba) ->
  (forall K : nat, QleT' (ncv_qsum (fun j => @bnorm _ _ B (b j)) K) Bb) ->
  forall m1 m2 n1 n2 : nat,
  (m1 <= m2)%nat -> (n1 <= n2)%nat ->
  QleT' (@bnorm _ _ B (@bplus _ _ B (ncv_conv _ _ B a b m2 n2) (@bopp _ _ B (ncv_conv _ _ B a b m1 n1))))
        (Ba * ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n2
         + Bb * ncv_qtail (fun k => @bnorm _ _ B (a k)) m1 m2)%Q.
Proof.
  intros BA bae B a b Ba Bb Ha Hb m1 m2 n1 n2 Hm Hn.
  eapply (QeqT_Qle_bool_cong _ _ _
    (@bnorm_wd _ _ B _ _
    (ncv_bae_diff_join _ _ B (ncv_conv _ _ B a b m2 n2) (ncv_conv _ _ B a b m2 n1)
                        (ncv_conv _ _ B a b m1 n1)))).
  eapply qleT'_trans.
  - exact (@bnorm_plus _ _ B (@bplus _ _ B (ncv_conv _ _ B a b m2 n2) (@bopp _ _ B (ncv_conv _ _ B a b m2 n1)))
                        (@bplus _ _ B (ncv_conv _ _ B a b m2 n1) (@bopp _ _ B (ncv_conv _ _ B a b m1 n1)))).
  - apply (qleT'_trans
             (@bnorm _ _ B (@bplus _ _ B (ncv_conv _ _ B a b m2 n2) (@bopp _ _ B (ncv_conv _ _ B a b m2 n1)))
              + @bnorm _ _ B (@bplus _ _ B (ncv_conv _ _ B a b m2 n1) (@bopp _ _ B (ncv_conv _ _ B a b m1 n1))))%Q
             (ncv_qsum (fun k => @bnorm _ _ B (a k)) m2 * ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n2
              + ncv_qtail (fun k => @bnorm _ _ B (a k)) m1 m2
                 * ncv_qsum (fun j => @bnorm _ _ B (b j)) n1)%Q
             (Ba * ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n2
              + Bb * ncv_qtail (fun k => @bnorm _ _ B (a k)) m1 m2)%Q).
    + apply qleT'_plus_compat.
      * exact (ncv_norm_conv_coldiff_le _ _ B a b m2 n1 n2 Hn).
      * exact (ncv_norm_conv_rowdiff_le _ _ B a b m1 m2 n1 Hm).
    + apply (qleT'_trans
               (ncv_qsum (fun k => @bnorm _ _ B (a k)) m2
                  * ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n2
                + ncv_qtail (fun k => @bnorm _ _ B (a k)) m1 m2
                  * ncv_qsum (fun j => @bnorm _ _ B (b j)) n1)%Q
               (Ba * ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n2
                + ncv_qtail (fun k => @bnorm _ _ B (a k)) m1 m2 * Bb)%Q
               (Ba * ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n2
                + Bb * ncv_qtail (fun k => @bnorm _ _ B (a k)) m1 m2)%Q).
      * apply qleT'_plus_compat.
        -- exact (qleT'_mult_compat_r (ncv_qsum (fun k => @bnorm _ _ B (a k)) m2) Ba
                    (ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n2)
                    (ncv_qtail_nonneg (fun j => @bnorm _ _ B (b j)) n1 n2
                       (fun j => @bnorm_pos _ _ B (b j)))
                    (Ha m2)).
        -- exact (qleT'_mult_compat_l (ncv_qsum (fun j => @bnorm _ _ B (b j)) n1) Bb
                    (ncv_qtail (fun k => @bnorm _ _ B (a k)) m1 m2)
                    (ncv_qtail_nonneg (fun k => @bnorm _ _ B (a k)) m1 m2
                       (fun k => @bnorm_pos _ _ B (a k)))
                    (Hb n1)).
      * apply qeq_leT'. apply qeq_imp_qeqT. ring.
Qed.


(* ============================================================ *)
(* Section 4. Absolute convergence implies the convolution Cauchy     *)
(*   property.  The Q-side tail criterion (the tail sums of the two   *)
(*   norm prefixes arbitrarily small) with the explicit Mertens       *)
(*   estimate makes the rectangular family C(m,n) Cauchy in all four  *)
(*   indices, hence the diagonal sequence is Cauchy.  Scaling: with   *)
(*   E := (Ba+Bb)+2 and eps' := eps/E, (Ba+Bb)*eps' < E*eps' = eps.   *)
(* ============================================================ *)

(* A product of positive rationals is positive (strict multiplication
   compatibility, transported along [QeqT]). *)
Lemma ncv_qmult_lt0 : forall x y : Q, Qlt 0 x -> Qlt 0 y -> QltT 0 (x * y)%Q.
Proof.
  intros x y Hx Hy.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans 0 (0 * y)%Q (x * y)%Q).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - apply (Qmult_lt_compat_r 0 x y Hy Hx).
Qed.

Lemma ncv_norm_conv_diff_sym : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : nat -> BA)
                                         (p q r s : nat),
  QeqT (@bnorm _ _ B (@bplus _ _ B (ncv_conv _ _ B a b p q) (@bopp _ _ B (ncv_conv _ _ B a b r s))))
       (@bnorm _ _ B (@bplus _ _ B (ncv_conv _ _ B a b r s) (@bopp _ _ B (ncv_conv _ _ B a b p q)))).
Proof.
  intros BA bae B a b p q r s.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (@bnorm _ _ B (@bplus _ _ B (@bopp _ _ B (ncv_conv _ _ B a b r s))
                                         (ncv_conv _ _ B a b p q)))).
  - apply qeqT_imp_qeq.
    exact (@bnorm_wd _ _ B _ _ (@bplus_comm _ _ B (ncv_conv _ _ B a b p q)
                                          (@bopp _ _ B (ncv_conv _ _ B a b r s)))).
  - apply (Qeq_trans _ (@bnorm _ _ B (@bopp _ _ B (@bplus _ _ B (ncv_conv _ _ B a b r s)
                                                   (@bopp _ _ B (ncv_conv _ _ B a b p q)))))).
    + apply qeqT_imp_qeq.
      exact (@bnorm_wd _ _ B _ _ (@bplus_opp_swap BA bae B (ncv_conv _ _ B a b r s)
                                              (ncv_conv _ _ B a b p q))).
    + rewrite (@bnorm_opp _ _ B (@bplus _ _ B (ncv_conv _ _ B a b r s)
                                      (@bopp _ _ B (ncv_conv _ _ B a b p q)))).
      apply Qeq_refl.
Qed.

Lemma ncv_conv_rect_cauchy : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : nat -> BA)
                                              (Ba Bb : Q),
  (forall K : nat, QleT' (ncv_qsum (fun k => @bnorm _ _ B (a k)) K) Ba) ->
  (forall K : nat, QleT' (ncv_qsum (fun j => @bnorm _ _ B (b j)) K) Bb) ->
  (forall e : Q, QltT 0 e ->
    sigT (fun T : nat => forall u1 u2 : nat,
      NatLe T u1 -> NatLe T u2 -> QltT (ncv_qtail (fun k => @bnorm _ _ B (a k)) u1 u2) e)) ->
  (forall e : Q, QltT 0 e ->
    sigT (fun T : nat => forall v1 v2 : nat,
      NatLe T v1 -> NatLe T v2 -> QltT (ncv_qtail (fun j => @bnorm _ _ B (b j)) v1 v2) e)) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall m1 m2 n1 n2 : nat,
    NatLe N m1 -> NatLe N m2 -> NatLe N n1 -> NatLe N n2 ->
    QltT (@bnorm _ _ B (@bplus _ _ B (ncv_conv _ _ B a b m2 n2)
                            (@bopp _ _ B (ncv_conv _ _ B a b m1 n1)))) eps).
Proof.
  intros BA bae B a b Ba Bb Ha Hb Hta Htb eps Heps.
  assert (Ha0 : QleT' 0 Ba) by exact (Ha 0%nat).
  assert (Hb0 : QleT' 0 Bb) by exact (Hb 0%nat).
  assert (H0Ba : Qle 0 Ba) by (apply QleT'_to_Qle; exact Ha0).
  assert (H0Bb : Qle 0 Bb) by (apply QleT'_to_Qle; exact Hb0).
  assert (HtBB : Qle 0 (Ba + Bb)%Q).
  { apply (Qle_trans 0 (0 + 0)%Q (Ba + Bb)%Q).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    - apply (Qplus_le_compat 0 Ba 0 Bb); assumption. }
  (* E := (Ba+Bb) + 2 > 0 *)
  assert (HleE : Qle (1 + 1)%Q (((Ba + Bb)%Q + (1 + 1))%Q)).
  { apply (Qle_trans (1 + 1)%Q ((1 + 1)%Q + 0%Q)
                     ((Ba + Bb)%Q + (1 + 1))%Q).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    - apply (Qle_trans ((1 + 1)%Q + 0%Q) ((1 + 1)%Q + (Ba + Bb)%Q)
                       ((Ba + Bb)%Q + (1 + 1))%Q).
      + apply (Qplus_le_compat (1 + 1)%Q (1 + 1)%Q 0%Q (Ba + Bb)%Q).
        * apply Qle_refl.
        * exact HtBB.
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
  assert (H0E : Qlt 0 (((Ba + Bb)%Q + (1 + 1))%Q)).
  { apply (Qlt_le_trans 0 (1 + 1)%Q ((Ba + Bb)%Q + (1 + 1))%Q).
    - reflexivity.
    - exact HleE. }
  assert (H0Einv : Qlt 0 (/ ((Ba + Bb)%Q + (1 + 1))%Q)).
  { apply (Qinv_lt_0_compat _ H0E). }
  assert (Hlt0epsD : QltT 0 (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q).
  { apply (ncv_qmult_lt0 _ _ (QltT_to_Qlt 0 eps Heps) H0Einv). }
  assert (HltT0epsD : QltT 0 (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q).
  { exact Hlt0epsD. }
  assert (Hcan : (((Ba + Bb)%Q + (1 + 1))%Q
                  * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q) == eps)
    by (field; intro Hz; apply qeq_imp_qeqT in Hz;
        apply (q_neq_of_lt _ (Qlt_to_QltT _ _ H0E)) in Hz; destruct Hz).
  assert (HltBD : Qlt (Ba + Bb)%Q (((Ba + Bb)%Q + (1 + 1))%Q)).
  { apply (Qle_lt_trans (Ba + Bb)%Q ((Ba + Bb)%Q + 0%Q)
                        ((Ba + Bb)%Q + (1 + 1))%Q).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    - apply (proj2 (Qplus_lt_r 0 (1 + 1)%Q (Ba + Bb)%Q)). reflexivity. }
  destruct (Hta (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q HltT0epsD) as [Ta Htaf].
  destruct (Htb (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q HltT0epsD) as [Tb Htbf].
  (* Final tail step: [X <= Ba*eps' + Bb*eps'] gives [X < eps]. *)
  assert (Hfin : forall X : Q,
    QleT' X (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
             + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q ->
    QltT X eps).
  { intros X HX.
    assert (Hr1 : (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                   + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                  == ((Ba + Bb)%Q * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q) by ring.
    assert (Hs : ((Ba + Bb)%Q * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q < eps).
    { pose proof (Qmult_lt_compat_r (Ba + Bb)%Q
                    ((Ba + Bb)%Q + (1 + 1))%Q
                    (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q
                    (QltT_to_Qlt _ _ Hlt0epsD) HltBD) as Hs0.
      setoid_rewrite Hcan in Hs0. exact Hs0. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans X ((Ba + Bb)%Q * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q eps).
    - apply QleT'_to_Qle.
      exact (qleT'_trans X
               (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
               ((Ba + Bb)%Q * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
               HX
               (qeq_leT' (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                          + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                         ((Ba + Bb)%Q * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                         (qeq_imp_qeqT _ _ Hr1))).
    - exact Hs. }
  (* Column block scaling: [qs_a u * qtb v1 v2 <= Ba*eps'] once both
     [v1] and [v2] are at least [Tb]. *)
  assert (HscA : forall (u v1 v2 : nat),
    NatLe Tb v1 -> NatLe Tb v2 ->
    QleT' (ncv_qsum (fun k => @bnorm _ _ B (a k)) u
           * ncv_qtail (fun j => @bnorm _ _ B (b j)) v1 v2)%Q
          (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
  { intros u v1 v2 Hv1 Hv2.
    apply (qleT'_trans
             (ncv_qsum (fun k => @bnorm _ _ B (a k)) u
              * ncv_qtail (fun j => @bnorm _ _ B (b j)) v1 v2)%Q
             (Ba * ncv_qtail (fun j => @bnorm _ _ B (b j)) v1 v2)%Q
             (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
    - apply (qleT'_mult_compat_r (ncv_qsum (fun k => @bnorm _ _ B (a k)) u) Ba
               (ncv_qtail (fun j => @bnorm _ _ B (b j)) v1 v2)
               (ncv_qtail_nonneg (fun j => @bnorm _ _ B (b j)) v1 v2
                  (fun j => @bnorm_pos _ _ B (b j)))
               (Ha u)).
    - apply (qleT'_mult_compat_l (ncv_qtail (fun j => @bnorm _ _ B (b j)) v1 v2)
               (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q Ba Ha0).
      apply qltT_leT'. exact (Htbf v1 v2 Hv1 Hv2). }
  (* Row block scaling: [qta u1 u2 * qs_b v <= Bb*eps'] once both
     [u1] and [u2] are at least [Ta]. *)
  assert (HscB : forall (u1 u2 v : nat),
    NatLe Ta u1 -> NatLe Ta u2 ->
    QleT' (ncv_qtail (fun k => @bnorm _ _ B (a k)) u1 u2
           * ncv_qsum (fun j => @bnorm _ _ B (b j)) v)%Q
          (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
  { intros u1 u2 v Hu1 Hu2.
    apply (qleT'_trans
             (ncv_qtail (fun k => @bnorm _ _ B (a k)) u1 u2
              * ncv_qsum (fun j => @bnorm _ _ B (b j)) v)%Q
             ((ncv_qtail (fun k => @bnorm _ _ B (a k)) u1 u2) * Bb)%Q
             (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
    - apply (qleT'_mult_compat_l (ncv_qsum (fun j => @bnorm _ _ B (b j)) v) Bb
               (ncv_qtail (fun k => @bnorm _ _ B (a k)) u1 u2)
               (ncv_qtail_nonneg (fun k => @bnorm _ _ B (a k)) u1 u2
                  (fun k => @bnorm_pos _ _ B (a k)))
               (Hb v)).
    - apply (qleT'_trans
               ((ncv_qtail (fun k => @bnorm _ _ B (a k)) u1 u2) * Bb)%Q
               (Bb * ncv_qtail (fun k => @bnorm _ _ B (a k)) u1 u2)%Q
               (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
      + apply qeq_leT'. apply qeq_imp_qeqT. ring.
      + apply (qleT'_mult_compat_l (ncv_qtail (fun k => @bnorm _ _ B (a k)) u1 u2)
                 (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)%Q Bb Hb0).
        apply qltT_leT'. exact (Htaf u1 u2 Hu1 Hu2). }
  (* Assembly lemma: [norm (x - z)] via the interpolated point [y],
     combining the two block bounds ([gat]/[gbt] are the final bounds). *)
  assert (Hfin2 : forall (x y z : BA) (ga gb gat gbt : Q),
    QleT' (@bnorm _ _ B (@bplus _ _ B x (@bopp _ _ B y))) ga ->
    QleT' (@bnorm _ _ B (@bplus _ _ B y (@bopp _ _ B z))) gb ->
    QleT' ga gat ->
    QleT' gb gbt ->
    QleT' (@bnorm _ _ B (@bplus _ _ B x (@bopp _ _ B z))) (gat + gbt)%Q).
  { intros x y z ga gb gat gbt Hxy Hyz Hga Hgb.
    apply (qleT'_trans
             (@bnorm _ _ B (@bplus _ _ B x (@bopp _ _ B z)))
             (@bnorm _ _ B (@bplus _ _ B x (@bopp _ _ B y))
              + @bnorm _ _ B (@bplus _ _ B y (@bopp _ _ B z)))%Q
             (gat + gbt)%Q
             (ncv_norm_triangle_via _ _ B x y z)
             (qleT'_plus_compat
                (@bnorm _ _ B (@bplus _ _ B x (@bopp _ _ B y))) gat
                (@bnorm _ _ B (@bplus _ _ B y (@bopp _ _ B z))) gbt
                (qleT'_trans
                   (@bnorm _ _ B (@bplus _ _ B x (@bopp _ _ B y))) ga gat Hxy Hga)
                (qleT'_trans
                   (@bnorm _ _ B (@bplus _ _ B y (@bopp _ _ B z))) gb gbt Hyz Hgb))). }
  (* Sum-order swap for the mixed branches of the case analysis. *)
  assert (Hswap : forall X : Q,
    QleT' X (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
             + Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q ->
    QleT' X (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
             + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
  { intros X HX0.
    assert (Hr2 : (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                   + Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                  == (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                      + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q) by ring.
    exact (qleT'_trans X
             (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
              + Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
             (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
              + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
             HX0
              (qeq_leT' (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                         + Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                        (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q)
                         + Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                        (qeq_imp_qeqT _ _ Hr2))). }
  exists (Nat.max Ta Tb).
  intros m1 m2 n1 n2 Hm1 Hm2 Hn1 Hn2.
  assert (HPa1 : NatLe Ta m1).
  { apply NatLe_lift.
    exact (Nat.le_trans Ta (Nat.max Ta Tb) m1
             (Nat.le_max_l Ta Tb) (NatLe_drop _ _ Hm1)). }
  assert (HPa2 : NatLe Ta m2).
  { apply NatLe_lift.
    exact (Nat.le_trans Ta (Nat.max Ta Tb) m2
             (Nat.le_max_l Ta Tb) (NatLe_drop _ _ Hm2)). }
  assert (HPb1 : NatLe Tb n1).
  { apply NatLe_lift.
    exact (Nat.le_trans Tb (Nat.max Ta Tb) n1
             (Nat.le_max_r Ta Tb) (NatLe_drop _ _ Hn1)). }
  assert (HPb2 : NatLe Tb n2).
  { apply NatLe_lift.
    exact (Nat.le_trans Tb (Nat.max Ta Tb) n2
             (Nat.le_max_r Ta Tb) (NatLe_drop _ _ Hn2)). }
  destruct (Nat.leb m1 m2) eqn:Em; destruct (Nat.leb n1 n2) eqn:En.
  - (* Case m1<=m2, n1<=n2: interpolate at (m2,n1). *)
    apply Hfin.
    apply (Hfin2 (ncv_conv _ _ B a b m2 n2) (ncv_conv _ _ B a b m2 n1)
                 (ncv_conv _ _ B a b m1 n1)
                 (ncv_qsum (fun k => @bnorm _ _ B (a k)) m2
                  * ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n2)%Q
                 (ncv_qtail (fun k => @bnorm _ _ B (a k)) m1 m2
                  * ncv_qsum (fun j => @bnorm _ _ B (b j)) n1)%Q
                 (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                 (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
    + exact (ncv_norm_conv_coldiff_le _ _ B a b m2 n1 n2
               (proj1 (Nat.leb_le n1 n2) En)).
    + exact (ncv_norm_conv_rowdiff_le _ _ B a b m1 m2 n1
               (proj1 (Nat.leb_le m1 m2) Em)).
    + exact (HscA m2 n1 n2 HPb1 HPb2).
    + exact (HscB m1 m2 n1 HPa1 HPa2).
  - (* Case m1<=m2, n2<n1: interpolate at (m2,n1), column block reversed. *)
    apply Hfin.
    apply (Hfin2 (ncv_conv _ _ B a b m2 n2) (ncv_conv _ _ B a b m2 n1)
                 (ncv_conv _ _ B a b m1 n1)
                 (ncv_qsum (fun k => @bnorm _ _ B (a k)) m2
                  * ncv_qtail (fun j => @bnorm _ _ B (b j)) n2 n1)%Q
                 (ncv_qtail (fun k => @bnorm _ _ B (a k)) m1 m2
                  * ncv_qsum (fun j => @bnorm _ _ B (b j)) n1)%Q
                 (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                 (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
    + eapply (QeqT_Qle_bool_cong _ _ _
               (ncv_norm_diff_sym _ _ B (ncv_conv _ _ B a b m2 n1) (ncv_conv _ _ B a b m2 n2))).
      exact (ncv_norm_conv_coldiff_le _ _ B a b m2 n2 n1
               (Nat.lt_le_incl n2 n1 (proj1 (Nat.leb_gt n1 n2) En))).
    + exact (ncv_norm_conv_rowdiff_le _ _ B a b m1 m2 n1
               (proj1 (Nat.leb_le m1 m2) Em)).
    + exact (HscA m2 n2 n1 HPb2 HPb1).
    + exact (HscB m1 m2 n1 HPa1 HPa2).
  - (* Case m2<m1, n1<=n2: interpolate at (m1,n2). *)
    apply Hfin.
    apply Hswap.
    apply (Hfin2 (ncv_conv _ _ B a b m2 n2) (ncv_conv _ _ B a b m1 n2)
                 (ncv_conv _ _ B a b m1 n1)
                 (ncv_qtail (fun k => @bnorm _ _ B (a k)) m2 m1
                  * ncv_qsum (fun j => @bnorm _ _ B (b j)) n2)%Q
                 (ncv_qsum (fun k => @bnorm _ _ B (a k)) m1
                  * ncv_qtail (fun j => @bnorm _ _ B (b j)) n1 n2)%Q
                 (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                 (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
    + eapply (QeqT_Qle_bool_cong _ _ _
               (ncv_norm_diff_sym _ _ B (ncv_conv _ _ B a b m1 n2) (ncv_conv _ _ B a b m2 n2))).
      exact (ncv_norm_conv_rowdiff_le _ _ B a b m2 m1 n2
               (Nat.lt_le_incl m2 m1 (proj1 (Nat.leb_gt m1 m2) Em))).
    + exact (ncv_norm_conv_coldiff_le _ _ B a b m1 n1 n2
               (proj1 (Nat.leb_le n1 n2) En)).
    + exact (HscB m2 m1 n2 HPa2 HPa1).
    + exact (HscA m1 n1 n2 HPb1 HPb2).
  - (* Case m2<m1, n2<n1: swap corners symmetrically, interpolate at (m2,n1). *)
    eapply (QeqT_Qlt_bool_cong _ _ _
             (qeqT_sym_hw _ _ (ncv_norm_conv_diff_sym _ _ B a b m2 n2 m1 n1))).
    apply Hfin.
    apply Hswap.
    apply (Hfin2 (ncv_conv _ _ B a b m1 n1) (ncv_conv _ _ B a b m2 n1)
                 (ncv_conv _ _ B a b m2 n2)
                 (ncv_qtail (fun k => @bnorm _ _ B (a k)) m2 m1
                  * ncv_qsum (fun j => @bnorm _ _ B (b j)) n1)%Q
                 (ncv_qsum (fun k => @bnorm _ _ B (a k)) m2
                  * ncv_qtail (fun j => @bnorm _ _ B (b j)) n2 n1)%Q
                 (Bb * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q
                 (Ba * (eps * / ((Ba + Bb)%Q + (1 + 1))%Q))%Q).
    + exact (ncv_norm_conv_rowdiff_le _ _ B a b m2 m1 n1
               (Nat.lt_le_incl m2 m1 (proj1 (Nat.leb_gt m1 m2) Em))).
    + exact (ncv_norm_conv_coldiff_le _ _ B a b m2 n2 n1
               (Nat.lt_le_incl n2 n1 (proj1 (Nat.leb_gt n1 n2) En))).
    + exact (HscB m2 m1 n1 HPa2 HPa1).
    + exact (HscA m2 n2 n1 HPb2 HPb1).
Qed.

(* The diagonal partial-sum sequence [fun n => C n n] is Cauchy
   (single-sequence face of the Cauchy product). *)
Corollary ncv_conv_diag_cauchy : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : nat -> BA)
                                                  (Ba Bb : Q),
  (forall K : nat, QleT' (ncv_qsum (fun k => @bnorm _ _ B (a k)) K) Ba) ->
  (forall K : nat, QleT' (ncv_qsum (fun j => @bnorm _ _ B (b j)) K) Bb) ->
  (forall e : Q, QltT 0 e ->
    sigT (fun T : nat => forall u1 u2 : nat,
      NatLe T u1 -> NatLe T u2 -> QltT (ncv_qtail (fun k => @bnorm _ _ B (a k)) u1 u2) e)) ->
  (forall e : Q, QltT 0 e ->
    sigT (fun T : nat => forall v1 v2 : nat,
      NatLe T v1 -> NatLe T v2 -> QltT (ncv_qtail (fun j => @bnorm _ _ B (b j)) v1 v2) e)) ->
  bcauchy BA bae B (fun n => ncv_conv _ _ B a b n n).
Proof.
  intros BA bae B a b Ba Bb Ha Hb Hta Htb eps Heps.
  destruct (ncv_conv_rect_cauchy _ _ B a b Ba Bb Ha Hb Hta Htb eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  exact (HN n m n m Hn Hm Hn Hm).
Qed.

Print Assumptions ncv_bopp_bopp.
