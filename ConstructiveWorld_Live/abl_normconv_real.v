(* ======================================================================== *)
(* abl_normconv_real.v — the M-test (series convergence by comparison) on   *)
(* the Real face, as a transplanted construct: the tree has no Real-face    *)
(* series container, so rnv_sum (partial sums), rnv_seg (segment sums) and  *)
(* the predicates rnv_conv / rnv_tail_small / rnv_conv_partial live here.   *)
(* Mission. rnv_compare_cauchy: pointwise domination |a k| <=_R b k with    *)
(*   one-sided dominated-tail control implies the segment sums of a form a  *)
(*   Real-Cauchy family; rnv_compare_cauchy_partial: the partial-sum        *)
(*   difference form of the same kernel; rnv_m_test_geom: the M-test at     *)
(*   the geometric rate C*(1/2)^k (half-base engine arch_decay);            *)
(*   rnv_geom_series_conv: usage instance, the half geometric series.       *)
(* Dependencies. S01_BaseRing (NatLe family); S02_CauchyComplete (Real and  *)
(*   its ring/order structure, the Set comparison faces QltT/QleT'/QeqT     *)
(*   with conversion lemmas, the Real projections); S03_QExp (q_pow,        *)
(*   arch_decay, real_abs_opp, q_abs_abs_triangle); S07_RealSetoidExpLog    *)
(*   (real_const_pos, real_lt_plus_compat_lt_le, real_le_plus_compat,       *)
(*   real_abs_zero_req, real_abs_triangle_le_eps, RealSetoid); Stdlib       *)
(*   QArith/Qring/Arith/Lia, imported in full (short names are not          *)
(*   re-exported by the tree).                                              *)
(* References. Sibling of the norm-convergence family; half-base engine =   *)
(*   arch_decay; naming follows the Real-face integral precedent (abl_pint_realview). *)
(* Constructivity. Zero admission statements, zero classical logic, zero    *)
(*   unproved premise slots; every statement face is Set-carried (QltT /    *)
(*   QleT' / QeqT comparisons, NatLe for the nat order). Scope: the kernel  *)
(*   premise is the one-sided tail-control form rnv_tail_small, not the     *)
(*   two-sided absolute Cauchy form; the rate is fixed to the half base     *)
(*   C*(1/2)^k, the general 0<c<1 real base is future work.                 *)
(* Build. ulimit -s 65532 && rocq c -native-compiler no -q -Q . ""          *)
(*   abl_normconv_real.v (run inside the world directory).                  *)
(* ======================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Arith.Arith Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.

(* ============================================================ *)
(* Part 0: containers — partial sums, segment sums, convergence  *)
(* predicates                                                    *)
(* ============================================================ *)

(* Partial sums: s_n := sum of a k for k < n (nat fold with real_plus, *)
(* right-associated appending). *)
Fixpoint rnv_sum (a : nat -> Real) (n : nat) : Real :=
  match n with
  | O%nat => real_zero
  | Datatypes.S k => real_plus (rnv_sum a k) (a k)
  end.

(* Segment sums: rnv_seg a m d = sum of a k for m <= k < m + d (terms *)
(* taken left-to-right, d is the segment length; this shape lines up *)
(* pointwise with the geometric tail bound and the constant-segment  *)
(* projection below). *)
Fixpoint rnv_seg (a : nat -> Real) (m d : nat) : Real :=
  match d with
  | O%nat => real_zero
  | Datatypes.S d' => real_plus (a m) (rnv_seg a (Datatypes.S m) d')
  end.

(* Segment-sum Cauchy predicate: for every eps > 0 (Q) there is N such *)
(* that |seg a m d| < eps for all m >= N and all d. *)
Definition rnv_conv (a : nat -> Real) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall (m d : nat), NatLe N m ->
      real_lt (real_abs (rnv_seg a m d)) (real_const eps)).

(* Dominated-tail control in one-sided form: for every eps > 0 (Q) *)
(* there is N such that the segment sums of b beyond N are < eps.  *)
(* This is the premise face of the comparison kernel (see the      *)
(* scope note in the file header). *)
Definition rnv_tail_small (b : nat -> Real) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall (m d : nat), NatLe N m ->
      real_lt (rnv_seg b m d) (real_const eps)).

(* Partial-sum difference predicate: for every eps > 0 (Q) there is N *)
(* such that |s_m - s_n| < eps for all m, n >= N. *)
Definition rnv_conv_partial (a : nat -> Real) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
      real_lt (real_abs (real_plus (rnv_sum a m) (real_opp (rnv_sum a n))))
              (real_const eps)).

(* ============================================================ *)
(* Part 1: small Real ring/order lemmas (completing what the tree *)
(* lacks, self-contained)                                        *)
(* ============================================================ *)

(* Positivity of eps/2 (Qlt_shift_div_l recipe). *)
Lemma rnv_half_pos0 : forall eps : Q, QltT 0 eps -> QltT 0 (eps / 2)%Q.
Proof.
  intros eps Heps. apply Qlt_to_QltT. apply Qlt_shift_div_l.
  - change (Qlt 0 2). compute. reflexivity.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* eps/2 + eps/2 equals eps, closed at the Q budget level. *)
Lemma rnv_half2 : forall eps : Q, QeqT (eps / 2 + eps / 2)%Q eps.
Proof.
  intros eps. apply qeq_imp_qeqT.
  replace (eps / 2) with (eps * (1#2))%Q by reflexivity. ring.
Qed.

(* 0 + x is x (pointwise ring via real_eq_of_zero_diff). *)
Lemma rnv_plus_zero_l : forall x : Real, real_eq (real_plus real_zero x) x.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* x + 0 is x. *)
Lemma rnv_plus_zero_r : forall x : Real, real_eq (real_plus x real_zero) x.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* (x + y) + (-x) is y (sum-difference cancellation). *)
Lemma rnv_plus_opp_r : forall x y : Real,
  real_eq (real_plus (real_plus x y) (real_opp x)) y.
Proof.
  intros x y. destruct x as [u Hu]. destruct y as [v Hv].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* x - y is -(y - x) (negation of the difference). *)
Lemma rnv_opp_minus : forall x y : Real,
  real_eq (real_plus x (real_opp y)) (real_opp (real_plus y (real_opp x))).
Proof.
  intros x y. destruct x as [u Hu]. destruct y as [v Hv].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* Four-term rearrangement: (x + (y + z)) + w = (x + y) + (z + w) *)
(* (associativity and pointwise compatibility chain). *)
Lemma rnv_plus_shuffle : forall x y z w : Real,
  real_eq (real_plus (real_plus x (real_plus y z)) w)
          (real_plus (real_plus x y) (real_plus z w)).
Proof.
  intros x y z w.
  apply (real_eq_trans _ (real_plus x (real_plus (real_plus y z) w))).
  - exact (real_eq_sym _ _ (real_plus_assoc x (real_plus y z) w)).
  - apply (real_eq_trans _ (real_plus x (real_plus y (real_plus z w)))).
    + exact (RealSetoid.real_eq_plus_compat x (real_plus (real_plus y z) w) x
               (real_plus y (real_plus z w))
               (real_eq_refl x) (real_eq_sym _ _ (real_plus_assoc y z w))).
    + exact (real_plus_assoc x y (real_plus z w)).
Qed.

(* Transport of real_le along real_eq on both sides (two Or branches: *)
(* the strict branch via the eq_lt_lt chain, the equality branch via  *)
(* transitivity). *)
Lemma rnv_le_eq : forall x y x' y' : Real,
  real_le x y -> real_eq x x' -> real_eq y y' -> real_le x' y'.
Proof.
  intros x y x' y' Hxy Hxx' Hyy'.
  destruct Hxy as [Hlt | Heq].
  - exact (inl (real_lt_eq_lt x' y y'
                       (real_eq_lt_lt x' x y (real_eq_sym x x' Hxx') Hlt) Hyy')).
  - exact (inr (real_eq_trans x' x y' (real_eq_sym x x' Hxx')
                       (real_eq_trans x y y' Heq Hyy'))).
Qed.

(* real_abs commutes with real_eq (elimination of the abs forms: both *)
(* real_abs and real_const reduce transparently). *)
Lemma rnv_abs_eq_compat : forall x y : Real,
  real_eq x y -> real_eq (real_abs x) (real_abs y).
Proof.
  intros x y Hxy eps Heps.
  destruct (Hxy eps Heps) as [N HN].
  exists N. intros n Hn.
  destruct x as [u Hu]. destruct y as [v Hv]. cbn [projT1 real_abs].
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (Qabs (Qabs (u n) - Qabs (v n))) (Qabs (u n - v n)) eps).
  - exact (QleT'_to_Qle _ _ (q_abs_abs_triangle (u n) (v n))).
  - apply QltT_to_Qlt. exact (HN n Hn).
Qed.

(* Shared helper for lifting constants: QeqT c d implies real_eq     *)
(* (real_const c) (real_const d) (the recipe of the Real-face        *)
(* integral family's constant lemma, self-contained here). *)
Lemma rnv_const_qeqT : forall c d : Q, QeqT c d -> real_eq (real_const c) (real_const d).
Proof.
  intros c d Hcd eps Heps. exists 0%nat. intros n _.
  apply Qlt_to_QltT. apply (Qle_lt_trans _ 0).
  - pose proof (qeqT_imp_qeq c d Hcd) as Heq.
    pose proof (Qminus_comp c d Heq d d (Qeq_refl d)) as Hm.
    assert (Hdd : (d - d)%Q == 0) by ring.
    pose proof (Qeq_trans _ _ _ Hm Hdd) as Hm2.
    pose proof (Qabs_wd (c - d) 0 Hm2) as Habs1.
    pose proof (Qabs_pos 0 (Qle_refl 0)) as Habs2.
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    exact (Qeq_trans _ _ _ Habs1 Habs2).
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* |real_const c| is real_const |c| (constant case of the abs *)
(* change of face). *)
Lemma rnv_abs_const : forall c : Q, real_eq (real_abs (real_const c)) (real_const (Qabs c)).
Proof.
  intros c. apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT.
  cbn [projT1 real_abs real_const]. ring.
Qed.

(* ============================================================ *)
(* Part 2: sum algebra (the partial-sum / segment-sum join)       *)
(* ============================================================ *)

(* The join: s_(m+d) = s_m + seg a m d (induction on d, two steps of *)
(* compatibility and associativity). *)
Lemma rnv_sum_seg : forall (a : nat -> Real) (d m : nat),
  real_eq (rnv_sum a (m + d)) (real_plus (rnv_sum a m) (rnv_seg a m d)).
Proof.
  intros a d. induction d as [| d IH]; intro m.
  - rewrite Nat.add_0_r. exact (real_eq_sym _ _ (rnv_plus_zero_r (rnv_sum a m))).
  - rewrite Nat.add_succ_r. cbn [rnv_sum rnv_seg].
    pose proof (IH (Datatypes.S m)) as IHh.
    apply (real_eq_trans _ (real_plus (rnv_sum a (Datatypes.S m)) (rnv_seg a (Datatypes.S m) d))).
    + exact IHh.
    + exact (real_eq_sym _ _ (real_plus_assoc (rnv_sum a m) (a m) (rnv_seg a (Datatypes.S m) d))).
Qed.

(* Segment form of the partial-sum difference: s_(m+d) - s_m = seg a m d. *)
Lemma rnv_diff_seg : forall (a : nat -> Real) (d m : nat),
  real_eq (real_plus (rnv_sum a (m + d)) (real_opp (rnv_sum a m))) (rnv_seg a m d).
Proof.
  intros a d m.
  pose proof (rnv_sum_seg a d m) as Hs.
  apply (real_eq_trans
           (real_plus (rnv_sum a (m + d)) (real_opp (rnv_sum a m)))
           (real_plus (real_plus (rnv_sum a m) (rnv_seg a m d)) (real_opp (rnv_sum a m)))
           (rnv_seg a m d)).
  - exact (RealSetoid.real_eq_plus_compat (rnv_sum a (m + d)) (real_opp (rnv_sum a m))
             (real_plus (rnv_sum a m) (rnv_seg a m d)) (real_opp (rnv_sum a m))
             Hs (real_eq_refl _)).
  - exact (rnv_plus_opp_r (rnv_sum a m) (rnv_seg a m d)).
Qed.

(* ============================================================ *)
(* Part 3: the Q-level geometric ledger (half base: positivity,   *)
(* monotone decay, geometric segment bound)                       *)
(* ============================================================ *)

(* Two-sided transport of Qle along Qeq. *)
Lemma rnv_qle_eq : forall a b a' b' : Q,
  QleT' a b -> QeqT a a' -> QeqT b b' -> QleT' a' b'.
Proof.
  intros a b a' b' Hab Haa Hbb.
  apply Qle_to_QleT'.
  exact (Qle_trans a' a b'
           (QleT'_to_Qle a' a
              (qeq_le a' a (qeq_imp_qeqT a' a (Qeq_sym a a' (qeqT_imp_qeq a a' Haa)))))
           (Qle_trans a b b' (QleT'_to_Qle a b Hab)
              (QleT'_to_Qle b b' (qeq_le b b' Hbb)))).
Qed.

(* 0 <= 1/2. *)
Lemma rnv_qle_0_half : QleT' 0 (1#2)%Q.
Proof. exact id_refl. Qed.

(* (1/2)^d >= 0. *)
Lemma rnv_q_pow_half_pos : forall d : nat, QleT' 0 (q_pow (1#2)%Q d).
Proof.
  induction d as [| d IH].
  - apply Qle_to_QleT'. change (0 <= 1)%Q. apply Qlt_le_weak. compute. reflexivity.
  - cbn [q_pow].
    apply (rnv_qle_eq (0 * (1#2))%Q (q_pow (1#2)%Q d * (1#2))%Q 0%Q
             ((1#2) * q_pow (1#2)%Q d)%Q).
    + exact (Qle_to_QleT' _ _
               (Qmult_le_compat_r 0%Q (q_pow (1#2)%Q d) (1#2)%Q
                  (QleT'_to_Qle 0 (q_pow (1#2)%Q d) IH)
                  (QleT'_to_Qle 0 (1#2)%Q rnv_qle_0_half))).
    + apply qeq_imp_qeqT. ring.
    + apply qeq_imp_qeqT. ring.
Qed.

(* Monotone decay: (1/2)^(m+d) <= (1/2)^m. *)
Lemma rnv_q_pow_half_dec : forall (d m : nat),
  QleT' (q_pow (1#2)%Q (m + d)) (q_pow (1#2)%Q m).
Proof.
  intros d m. induction d as [| d IH].
  - replace (m + 0)%nat with m by lia. apply Qle_to_QleT'. apply Qle_refl.
  - replace (m + Datatypes.S d)%nat with (Datatypes.S (m + d))%nat by lia.
    cbn [q_pow].
    assert (Hr1 : (1%Q * q_pow (1#2)%Q (m + d))%Q == q_pow (1#2)%Q (m + d)) by ring.
    apply Qle_to_QleT'.
    apply (Qle_trans ((1#2) * q_pow (1#2)%Q (m + d))%Q
             (q_pow (1#2)%Q (m + d)) (q_pow (1#2)%Q m)).
    + exact (Qle_trans ((1#2) * q_pow (1#2)%Q (m + d))%Q
               (1%Q * q_pow (1#2)%Q (m + d))%Q
               (q_pow (1#2)%Q (m + d))
               (Qmult_le_compat_r (1#2)%Q 1%Q (q_pow (1#2)%Q (m + d))
                  (QleT'_to_Qle (1#2)%Q 1%Q id_refl)
                  (QleT'_to_Qle 0%Q (q_pow (1#2)%Q (m + d))
                     (rnv_q_pow_half_pos (m + d))))
               (QleT'_to_Qle _ _ (qeq_le _ _ (qeq_imp_qeqT _ _ Hr1)))).
    + exact (QleT'_to_Qle _ _ IH).
Qed.

(* Left-recursive Q-level segment sum (pointwise mirror of rnv_seg). *)
Fixpoint rnv_q_segL (f : nat -> Q) (m d : nat) : Q :=
  match d with
  | O%nat => 0%Q
  | Datatypes.S d' => f m + rnv_q_segL f (Datatypes.S m) d'
  end.

(* Geometric segment bound: segL(C*(1/2)^k) m d <= (1/2)^m * (C*2) *)
(* (induction on d with m shifted at each step). *)
Lemma rnv_q_segL_pow_bound : forall (C : Q) (d m : nat),
  QleT' 0 C ->
  QleT' (rnv_q_segL (fun k : nat => C * q_pow (1#2)%Q k) m d)
      (q_pow (1#2)%Q m * (C * 2))%Q.
Proof.
  intros C d. induction d as [| d IH]; intros m HC.
  - assert (Hzc : Qle 0 (C * 2)%Q)
      by exact (Qmult_le_compat_r 0%Q C 2%Q (QleT'_to_Qle 0%Q C HC)
                  (QleT'_to_Qle 0%Q 2%Q id_refl)).
    apply (rnv_qle_eq (0 * (C * 2))%Q (q_pow (1#2)%Q m * (C * 2))%Q 0%Q
             (q_pow (1#2)%Q m * (C * 2))%Q).
    + exact (Qle_to_QleT' _ _
               (Qmult_le_compat_r 0%Q (q_pow (1#2)%Q m) (C * 2)%Q
                  (QleT'_to_Qle 0%Q (q_pow (1#2)%Q m) (rnv_q_pow_half_pos m)) Hzc)).
    + apply qeq_imp_qeqT. ring.
    + apply qeq_imp_qeqT. apply Qeq_refl.
  - cbn [rnv_q_segL].
    pose proof (IH (Datatypes.S m) HC) as IHh.
    pose proof (Qplus_le_compat (C * q_pow (1#2)%Q m) (C * q_pow (1#2)%Q m)
                  (rnv_q_segL (fun k : nat => C * q_pow (1#2)%Q k) (Datatypes.S m) d)
                  (q_pow (1#2)%Q (Datatypes.S m) * (C * 2))%Q
                  (Qle_refl (C * q_pow (1#2)%Q m)) (QleT'_to_Qle _ _ IHh)) as H1.
    apply (rnv_qle_eq
             (C * q_pow (1#2)%Q m
              + rnv_q_segL (fun k : nat => C * q_pow (1#2)%Q k) (Datatypes.S m) d)%Q
             (C * q_pow (1#2)%Q m + q_pow (1#2)%Q (Datatypes.S m) * (C * 2))%Q
             (C * q_pow (1#2)%Q m
              + rnv_q_segL (fun k : nat => C * q_pow (1#2)%Q k) (Datatypes.S m) d)%Q
             (q_pow (1#2)%Q m * (C * 2))%Q).
    + exact (Qle_to_QleT' _ _ H1).
    + apply qeq_imp_qeqT. apply Qeq_refl.
    + apply qeq_imp_qeqT.
      replace (q_pow (1#2)%Q (Datatypes.S m)) with ((1#2) * q_pow (1#2)%Q m)%Q by reflexivity.
      ring.
Qed.

(* ============================================================ *)
(* Part 4: three segment-sum lemmas (triangle eps form, termwise  *)
(* domination monotonicity, constant-segment direct reading)      *)
(* ============================================================ *)

(* Segment triangle (eps form with the eps/2 budget threading):  *)
(* |seg a m d| <= seg|a| m d + eps. *)
Lemma rnv_seg_triangle_eps : forall (a : nat -> Real) (d m : nat) (eps : Q),
  QltT 0 eps ->
  real_le (real_abs (rnv_seg a m d))
          (real_plus (rnv_seg (fun k : nat => real_abs (a k)) m d) (real_const eps)).
Proof.
  intros a d. induction d as [| d IH]; intros m eps Heps.
  - cbn [rnv_seg].
    pose proof (real_lt_eq_lt real_zero (real_const eps)
                  (real_plus real_zero (real_const eps))
                  (real_const_pos eps Heps)
                  (real_eq_sym _ _ (rnv_plus_zero_l (real_const eps)))) as Hlt0.
    exact (inl (real_eq_lt_lt (real_abs real_zero) real_zero
                  (real_plus real_zero (real_const eps)) real_abs_zero_req Hlt0)).
  - cbn [rnv_seg].
    pose proof (rnv_half_pos0 eps Heps) as Hh.
    pose proof (real_abs_triangle_le_eps (a m) (rnv_seg a (Datatypes.S m) d)
                  (real_const (eps / 2)%Q) (real_const_pos (eps / 2)%Q Hh)) as Htri.
    pose proof (IH (Datatypes.S m) (eps / 2)%Q Hh) as IHh.
    (* (|a m| + |seg'|) + eps/2 <= (|a m| + (segabs' + eps/2)) + eps/2 *)
    pose proof (real_le_plus_compat (real_abs (a m)) (real_abs (a m))
                  (real_abs (rnv_seg a (Datatypes.S m) d))
                  (real_plus (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d)
                             (real_const (eps / 2)%Q))
                  (real_le_refl (real_abs (a m))) IHh) as H1.
    pose proof (real_le_plus_compat
                  (real_plus (real_abs (a m)) (real_abs (rnv_seg a (Datatypes.S m) d)))
                  (real_plus (real_abs (a m))
                             (real_plus (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d)
                                        (real_const (eps / 2)%Q)))
                  (real_const (eps / 2)%Q) (real_const (eps / 2)%Q)
                  H1 (real_le_refl (real_const (eps / 2)%Q))) as H2.
    (* Right-side transport: ((A + (B + c)) + c) = ((A + B) + eps) *)
    (* (rearrangement plus the constant budget c + c = eps). *)
    pose proof (rnv_le_eq
                  (real_plus (real_plus (real_abs (a m))
                               (real_abs (rnv_seg a (Datatypes.S m) d)))
                             (real_const (eps / 2)%Q))
                  (real_plus (real_plus (real_abs (a m))
                               (real_plus (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d)
                                          (real_const (eps / 2)%Q)))
                             (real_const (eps / 2)%Q))
                  (real_plus (real_plus (real_abs (a m))
                               (real_abs (rnv_seg a (Datatypes.S m) d)))
                             (real_const (eps / 2)%Q))
                  (real_plus (real_plus (real_abs (a m))
                               (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d))
                             (real_const eps))
                  H2 (real_eq_refl _)
                  (real_eq_trans
                     (real_plus (real_plus (real_abs (a m))
                                  (real_plus (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d)
                                             (real_const (eps / 2)%Q)))
                                (real_const (eps / 2)%Q))
                     (real_plus (real_plus (real_abs (a m))
                                  (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d))
                                (real_plus (real_const (eps / 2)%Q) (real_const (eps / 2)%Q)))
                     (real_plus (real_plus (real_abs (a m))
                                  (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d))
                                (real_const eps))
                     (rnv_plus_shuffle (real_abs (a m))
                        (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d)
                        (real_const (eps / 2)%Q) (real_const (eps / 2)%Q))
                     (RealSetoid.real_eq_plus_compat
                        (real_plus (real_abs (a m))
                                   (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d))
                        (real_plus (real_const (eps / 2)%Q) (real_const (eps / 2)%Q))
                        (real_plus (real_abs (a m))
                                   (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d))
                        (real_const eps)
                        (real_eq_refl _)
                        (rnv_const_qeqT (eps / 2 + eps / 2)%Q eps (rnv_half2 eps))))) as H2'.
    apply (real_le_trans _ (real_plus (real_plus (real_abs (a m))
                            (real_abs (rnv_seg a (Datatypes.S m) d)))
                          (real_const (eps / 2)%Q))).
    + exact Htri.
    + exact H2'.
Qed.

(* Termwise domination implies segment-sum domination (real_le_plus_compat *)
(* along the induction). *)
Lemma rnv_seg_le : forall (f g : nat -> Real) (d m : nat),
  (forall k : nat, real_le (f k) (g k)) -> real_le (rnv_seg f m d) (rnv_seg g m d).
Proof.
  intros f g d. induction d as [| d IH]; intros m H.
  - exact (inr (real_eq_refl real_zero)).
  - cbn [rnv_seg].
    exact (real_le_plus_compat (f m) (g m) (rnv_seg f (Datatypes.S m) d) (rnv_seg g (Datatypes.S m) d)
             (H m) (IH (Datatypes.S m) H)).
Qed.

(* Pointwise projection of a constant segment: projT1 (rnv_seg F m d) j *)
(* equals the Q-level segment sum (left-recursive alignment). *)
Lemma rnv_seg_const_proj : forall (f : nat -> Q) (F : nat -> Real) (d m j : nat),
  (forall k j0 : nat, QeqT (projT1 (F k) j0) (f k)) ->
  QeqT (projT1 (rnv_seg F m d) j) (rnv_q_segL f m d).
Proof.
  intros f F d. induction d as [| d IH]; intros m j H.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. cbn [rnv_seg rnv_q_segL].
    pose proof (qeqT_imp_qeq _ _
                  (real_plus_proj (F m) (rnv_seg F (Datatypes.S m) d) j)) as Hp.
    rewrite Hp.
    rewrite (qeqT_imp_qeq _ _ (IH (Datatypes.S m) j H)).
    rewrite (qeqT_imp_qeq _ _ (H m j)).
    reflexivity.
Qed.

(* Left transport of Qeq into Qlt (direct reading of the Qlt_compat *)
(* Proper instance). *)
Lemma rnv_qeq_qlt_l : forall a b c : Q, QeqT a b -> QltT b c -> QltT a c.
Proof.
  intros a b c Hab Hbc.
  apply Qlt_to_QltT.
  exact (proj1 (Qlt_compat b a (Qeq_sym a b (qeqT_imp_qeq a b Hab)) c c (Qeq_refl c))
               (QltT_to_Qlt b c Hbc)).
Qed.

(* Right shift of a Q sum: q + e0 < eps implies e0 < eps - q *)
(* (Qplus_lt_l with a Qlt_compat change of face). *)
Lemma rnv_qlt_shift : forall q e0 eps : Q, QltT (q + e0) eps -> QltT e0 (eps - q)%Q.
Proof.
  intros q e0 eps Hq.
  apply Qlt_to_QltT.
  apply (proj1 (Qplus_lt_l e0 (eps - q)%Q q)).
  assert (Hr1 : (e0 + q)%Q == (q + e0)%Q) by ring.
  assert (Hr2 : eps == ((eps - q)%Q + q)%Q) by ring.
  pose proof (Qlt_compat (q + e0)%Q (e0 + q)%Q (Qeq_sym _ _ Hr1)
                eps ((eps - q)%Q + q)%Q Hr2) as Hiff.
  exact (proj1 Hiff (QltT_to_Qlt (q + e0)%Q eps Hq)).
Qed.

(* Right transport of Qeq into Qlt (direct reading of the Qlt_compat *)
(* Proper instance). *)
Lemma rnv_qeq_qlt_r : forall a b c : Q, QeqT b c -> QltT a b -> QltT a c.
Proof.
  intros a b c Hbc Hab.
  apply Qlt_to_QltT.
  exact (proj1 (Qlt_compat a a (Qeq_refl a) b c (qeqT_imp_qeq b c Hbc))
               (QltT_to_Qlt a b Hab)).
Qed.

(* Direct strict Real bound from a Q value: constant-segment sum + e0 < eps *)
(* implies real_lt (rnv_seg F m d) (real_const eps). *)
Lemma rnv_seg_const_lt : forall (f : nat -> Q) (F : nat -> Real) (d m : nat) (eps e0 : Q),
  QltT 0 e0 ->
  (forall k j : nat, QeqT (projT1 (F k) j) (f k)) ->
  QltT (rnv_q_segL f m d + e0) eps ->
  real_lt (rnv_seg F m d) (real_const eps).
Proof.
  intros f F d m eps e0 He0 Hpt Hq. unfold real_lt.
  exists e0. split.
  - exact He0.
  - exists 0%nat. intros j _.
    pose proof (rnv_seg_const_proj f F d m j Hpt) as Hpr.
    pose proof (Qminus_comp eps eps (Qeq_refl eps)
                  (projT1 (rnv_seg F m d) j) (rnv_q_segL f m d)
                  (qeqT_imp_qeq _ _ Hpr)) as Hm.
    exact (rnv_qeq_qlt_r _ _ _ (qeq_imp_qeqT _ _ (Qeq_sym _ _ Hm))
             (rnv_qlt_shift _ _ _ Hq)).
Qed.

(* ============================================================ *)
(* Theorem 1: comparison-test kernel (domination plus dominated    *)
(* tail control implies segment-sum Cauchy)                        *)
(* ============================================================ *)

Theorem rnv_compare_cauchy : forall (a b : nat -> Real),
  (forall k : nat, real_le (real_abs (a k)) (b k)) ->
  rnv_tail_small b ->
  rnv_conv a.
Proof.
  intros a b Hab Hb eps Heps.
  pose proof (rnv_half_pos0 eps Heps) as Hh.
  destruct (Hb (eps / 2)%Q Hh) as [N HN].
  exists N. intros m d Hm.
  (* |sega| <= seg|a| + eps/2 <= segb + eps/2 < eps/2 + eps/2 = eps *)
  pose proof (rnv_seg_triangle_eps a d m (eps / 2)%Q Hh) as Htri.
  pose proof (rnv_seg_le (fun k : nat => real_abs (a k)) b d m Hab) as Hmono.
  pose proof (real_le_plus_compat
                (rnv_seg (fun k : nat => real_abs (a k)) m d) (rnv_seg b m d)
                (real_const (eps / 2)%Q) (real_const (eps / 2)%Q)
                Hmono (real_le_refl (real_const (eps / 2)%Q))) as H1.
  pose proof (real_le_trans (real_abs (rnv_seg a m d))
                (real_plus (rnv_seg (fun k : nat => real_abs (a k)) m d)
                           (real_const (eps / 2)%Q))
                (real_plus (rnv_seg b m d) (real_const (eps / 2)%Q)) Htri H1) as H2.
  pose proof (HN m d Hm) as H3.
  pose proof (real_lt_plus_compat_lt_le (rnv_seg b m d) (real_const (eps / 2)%Q)
                (real_const (eps / 2)%Q) (real_const (eps / 2)%Q)
                H3 (real_le_refl (real_const (eps / 2)%Q))) as H4.
  pose proof (real_lt_eq_lt (real_plus (rnv_seg b m d) (real_const (eps / 2)%Q))
                (real_plus (real_const (eps / 2)%Q) (real_const (eps / 2)%Q))
                (real_const eps) H4
                (rnv_const_qeqT (eps / 2 + eps / 2)%Q eps (rnv_half2 eps))) as H5.
  exact (real_le_lt_trans (real_abs (rnv_seg a m d))
           (real_plus (rnv_seg b m d) (real_const (eps / 2)%Q)) (real_const eps) H2 H5).
Qed.

(* Theorem 1': the partial-sum difference form (the transplanted *)
(* draft's original shape) — the kernel plus the algebra of Part 2. *)
Theorem rnv_compare_cauchy_partial : forall (a b : nat -> Real),
  (forall k : nat, real_le (real_abs (a k)) (b k)) ->
  rnv_tail_small b ->
  rnv_conv_partial a.
Proof.
  intros a b Hab Hb eps Heps.
  destruct (rnv_compare_cauchy a b Hab Hb eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  pose proof (NatLe_drop N m Hm) as Hdm.
  pose proof (NatLe_drop N n Hn) as Hdn.
  destruct (le_lt_dec m n) as [Hmn | Hnm].
  - (* m <= n: s_m - s_n = -(seg a m (n-m)); transport through |-x| = |x| *)
    (* and apply the kernel. *)
    replace n with (m + (n - m)%nat)%nat by lia.
    pose proof (rnv_diff_seg a (n - m)%nat m) as Hdf.
    pose proof (rnv_abs_eq_compat
                  (real_plus (rnv_sum a m) (real_opp (rnv_sum a (m + (n - m)%nat))))
                  (real_opp (real_plus (rnv_sum a (m + (n - m)%nat)) (real_opp (rnv_sum a m))))
                  (rnv_opp_minus (rnv_sum a m) (rnv_sum a (m + (n - m)%nat)))) as Heq1.
    pose proof (real_abs_opp
                  (real_plus (rnv_sum a (m + (n - m)%nat)) (real_opp (rnv_sum a m)))) as Heq2.
    pose proof (rnv_abs_eq_compat
                  (real_plus (rnv_sum a (m + (n - m)%nat)) (real_opp (rnv_sum a m)))
                  (rnv_seg a m (n - m)%nat) Hdf) as Heq3.
    pose proof (real_eq_trans
                  (real_abs (real_plus (rnv_sum a m) (real_opp (rnv_sum a (m + (n - m)%nat)))))
                  (real_abs (real_opp (real_plus (rnv_sum a (m + (n - m)%nat)) (real_opp (rnv_sum a m)))))
                  (real_abs (rnv_seg a m (n - m)%nat)) Heq1
                  (real_eq_trans
                     (real_abs (real_opp (real_plus (rnv_sum a (m + (n - m)%nat)) (real_opp (rnv_sum a m)))))
                     (real_abs (real_plus (rnv_sum a (m + (n - m)%nat)) (real_opp (rnv_sum a m))))
                     (real_abs (rnv_seg a m (n - m)%nat)) Heq2 Heq3)) as Hchain.
    pose proof (HN m (n - m)%nat (NatLe_lift N m Hdm)) as Hsmall.
    exact (real_eq_lt_lt
             (real_abs (real_plus (rnv_sum a m) (real_opp (rnv_sum a (m + (n - m)%nat)))))
             (real_abs (rnv_seg a m (n - m)%nat)) (real_const eps) Hchain Hsmall).
  - (* n < m: directly s_m - s_n = seg a n (m-n). *)
    replace m with (n + (m - n)%nat)%nat by lia.
    pose proof (rnv_diff_seg a (m - n)%nat n) as Hdf.
    pose proof (rnv_abs_eq_compat
                  (real_plus (rnv_sum a (n + (m - n)%nat)) (real_opp (rnv_sum a n)))
                  (rnv_seg a n (m - n)%nat) Hdf) as Hchain.
    exact (real_eq_lt_lt
             (real_abs (real_plus (rnv_sum a (n + (m - n)%nat)) (real_opp (rnv_sum a n))))
             (real_abs (rnv_seg a n (m - n)%nat)) (real_const eps) Hchain
             (HN n (m - n)%nat (NatLe_lift N n Hdn))).
Qed.

(* ============================================================ *)
(* Theorem 2: the M-test specialized to the geometric rate        *)
(* C*(1/2)^k (the tree's arch_decay shape)                        *)
(* ============================================================ *)

Theorem rnv_m_test_geom : forall (a : nat -> Real) (C : Q),
  QleT' 0 C ->
  (forall k : nat, real_le (real_abs (a k)) (real_const (C * q_pow (1#2)%Q k))) ->
  rnv_conv a.
Proof.
  intros a C HC Hab.
  apply (rnv_compare_cauchy a (fun k : nat => real_const (C * q_pow (1#2)%Q k)) Hab).
  (* Tail control for b := C*(1/2)^k: the Q geometric ledger plus the *)
  (* witness t selected by arch_decay. *)
  intros eps Heps.
  pose proof (rnv_half_pos0 eps Heps) as Hh.
  pose proof (QleT'_to_Qle 0 C HC) as HC0.
  pose proof (Qmult_le_compat_r 0%Q C 2%Q HC0 (QleT'_to_Qle 0%Q 2%Q id_refl)) as Hzc.
  pose proof (Qle_to_QleT' (0 * 4)%Q (C * 4)%Q
                (Qmult_le_compat_r 0%Q C 4%Q HC0 (QleT'_to_Qle 0%Q 4%Q id_refl))) as Hq4.
  destruct (arch_decay (C * 4)%Q (eps / 2)%Q Hq4 Hh) as [t Ht].
  exists t. intros m d Hm.
  pose proof (NatLe_drop t m Hm) as Hle.
  assert (Hmt : Qle (q_pow (1#2)%Q m) (q_pow (1#2)%Q t)).
  { replace m with (t + (m - t))%nat by lia.
    apply QleT'_to_Qle. apply rnv_q_pow_half_dec. }
  pose proof (rnv_q_segL_pow_bound C d m HC) as Hbound.
  pose proof (Qmult_le_compat_r (q_pow (1#2)%Q m) (q_pow (1#2)%Q t) (C * 2)%Q Hmt Hzc) as Hs1.
  assert (Hq2 : q_pow (1#2)%Q t * (C * 2)%Q
                == (C * 4)%Q * q_pow (1#2)%Q (Datatypes.S t)).
  { replace (q_pow (1#2)%Q (Datatypes.S t)) with ((1#2) * q_pow (1#2)%Q t)%Q by reflexivity.
    ring. }
  pose proof (Qle_trans _ _ _ Hs1
                (QleT'_to_Qle _ _ (qeq_le _ _ (qeq_imp_qeqT _ _ Hq2)))) as Hs2.
  pose proof (Qle_trans _ _ _ (QleT'_to_Qle _ _ Hbound) Hs2) as Hb2.
  apply (rnv_seg_const_lt (fun k : nat => C * q_pow (1#2)%Q k)
           (fun k : nat => real_const (C * q_pow (1#2)%Q k)) d m eps (eps / 2)%Q Hh).
  - intros k j. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (real_const_proj _ j)).
  - apply Qlt_to_QltT.
    apply (Qle_lt_trans _ ((C * 4)%Q * q_pow (1#2)%Q (Datatypes.S t) + (eps / 2)%Q) eps).
    + exact (Qplus_le_compat
               (rnv_q_segL (fun k : nat => C * q_pow (1#2)%Q k) m d)
               ((C * 4)%Q * q_pow (1#2)%Q (Datatypes.S t))
               (eps / 2)%Q (eps / 2)%Q Hb2 (Qle_refl (eps / 2)%Q)).
    + apply (Qlt_le_trans _ ((eps / 2 + eps / 2)%Q)).
      * exact (Qplus_lt_le_compat (C * 4 * q_pow (1#2)%Q (Datatypes.S t)) (eps / 2)%Q
                  (eps / 2)%Q (eps / 2)%Q (QltT_to_Qlt _ _ Ht)
                  (Qle_refl (eps / 2)%Q)).
      * exact (QleT'_to_Qle (eps / 2 + eps / 2)%Q eps
                 (qeq_le (eps / 2 + eps / 2)%Q eps (rnv_half2 eps))).
Qed.

(* Usage instance: the half geometric series converges (C := 1). *)
Theorem rnv_geom_series_conv : rnv_conv (fun k : nat => real_const (q_pow (1#2)%Q k)).
Proof.
  apply (rnv_m_test_geom (fun k : nat => real_const (q_pow (1#2)%Q k)) 1%Q id_refl).
  intros k.
  pose proof (rnv_q_pow_half_pos k) as Hpos.
  assert (Habs : Qabs (q_pow (1#2)%Q k) == q_pow (1#2)%Q k)
    by (apply Qabs_pos; exact (QleT'_to_Qle 0 (q_pow (1#2)%Q k) Hpos)).
  assert (Hq : q_pow (1#2)%Q k == 1 * q_pow (1#2)%Q k) by ring.
  exact (inr (real_eq_trans
           (real_abs (real_const (q_pow (1#2)%Q k)))
           (real_const (Qabs (q_pow (1#2)%Q k)))
           (real_const (1 * q_pow (1#2)%Q k))
           (rnv_abs_const (q_pow (1#2)%Q k))
           (rnv_const_qeqT (Qabs (q_pow (1#2)%Q k)) (1 * q_pow (1#2)%Q k)
              (qeq_imp_qeqT _ _
                 (Qeq_trans (Qabs (q_pow (1#2)%Q k)) (q_pow (1#2)%Q k)
                            (1 * q_pow (1#2)%Q k)
                            Habs
                            Hq))))).
Qed.

(* ============================================================ *)
(* Final face: Print Assumptions for the four theorems            *)
(* ============================================================ *)
Print Assumptions rnv_compare_cauchy.
Print Assumptions rnv_compare_cauchy_partial.
Print Assumptions rnv_m_test_geom.
Print Assumptions rnv_geom_series_conv.
