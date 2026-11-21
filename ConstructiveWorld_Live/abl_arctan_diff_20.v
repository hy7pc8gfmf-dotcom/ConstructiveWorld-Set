(* ConstructiveWorld-Set — arctan difference-formula continuation piece (slope identity and constant criterion). *)
(** * abl_arctan_diff_20: the slope-composition identity and the small-span constant criterion.

    Mission.  Continues [abl_arctan_diff_19] with the two certificates the
      phi assembly consumes.  [abl9_slope_id]: the exact Q-layer identity
      for the composite slope of [w(u) := (u-v)/(1+u*v)] — the [w]-increment
      at [u+s] scaled by [(1+u*v)^2/((1+u^2)(1+v^2))] differs from the
      substituted slope [s/(1+u^2)] by the explicit remainder
      [s*s*v/((1+(u+s)*v)(1+u^2))] (the algebraic core of [phi'(t) = 0]).
      [abl9_const_crit]: a uniform increment estimate forces
      [real_eq (phi (a+s)) (phi a)].  The remaining lemmas are the
      supporting pieces (Q transfer helpers, [Qabs] bridges, the path
      denominator, real-layer arctan well-definedness and alignment).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qround],
      [Lists.List], [Bool.Bool], [Arith.Arith], [Setoid], [Morphisms],
      [Lia], [QArith.Qminmax], [Structures.GenericMinMax], [Extraction];
      requires [S01_BaseRing] through [S11_TP3B5] and
      [abl_arctan_diff_19] of this development.

    References.  This development, abl_arctan_diff_20.v, the baseline module
      in ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All seventeen lemmas close constructively, stay
      transparent ([Defined]) and carry zero admitted statements; the
      conclusions use the Set-layer predicates, [Obj.magic] count 0.

    Build.  [coqc -q -Q ConstructiveWorld_Live "" abl_arctan_diff_20.v]
      compiles cleanly (exit 0); the artifact starts with [436f7121 00015ff4]. *)

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
Require Import abl_arctan_diff_19.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* Infrastructure for item 2: Qeq cannot be rewritten directly under    *)
(* QltT (the Id(Qlt_bool) carrier is not a setoid); the four transfer   *)
(* helpers below are shared across the whole piece (the QltT versions   *)
(* first, the Qlt versions reached through Qlt_to_QltT).                *)
(* ============================================================ *)
Lemma abl9_QltT_transfer_l : forall x y z : Q, x == y -> QltT x z -> QltT y z.
Proof.
  intros x y z Hxy Hlt.
  assert (Hx : Qlt x z) by (apply QltT_to_Qlt; exact Hlt).
  apply Qlt_to_QltT. apply (Qle_lt_trans y x z).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    apply Qeq_sym. exact Hxy.
  - exact Hx.
Defined.

Lemma abl9_QltT_transfer_r : forall x y z : Q, y == z -> QltT x y -> QltT x z.
Proof.
  intros x y z Hyz Hlt.
  apply Qlt_to_QltT. apply (Qlt_le_trans x y z).
  - apply QltT_to_Qlt. exact Hlt.
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact Hyz.
Defined.

Lemma abl9_Qlt_transfer_l : forall x y z : Q, x == y -> Qlt x z -> QltT y z.
Proof.
  intros x y z Hxy Hlt.
  apply Qlt_to_QltT. apply (Qle_lt_trans y x z).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    apply Qeq_sym. exact Hxy.
  - exact Hlt.
Defined.

Lemma abl9_Qlt_transfer_r : forall x y z : Q, y == z -> Qlt x y -> QltT x z.
Proof.
  intros x y z Hyz Hlt.
  apply Qlt_to_QltT. apply (Qlt_le_trans x y z).
  - exact Hlt.
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact Hyz.
Defined.

(* Well-definedness of Qabs under Qeq, lifted to the QeqT carrier. *)
Lemma abl9_Qabs_wd : forall x y : Q, x == y -> QeqT (Qabs x) (Qabs y).
Proof.
  intros x y H. apply qeq_imp_qeqT. apply (Qabs_wd x y). exact H.
Defined.

(* ============================================================ *)
(* Infrastructure for item 2: positivity of 1 + q^2 (the kernel reuses  *)
(* the S02 square-positivity lemma; the nonzero face is the Set-layer   *)
(* Not (QeqT ...) carrier).                                             *)
(* ============================================================ *)
Lemma abl9_q_pos_sq : forall q : Q, Not (QeqT (1 + q * q) 0).
Proof.
  intros q.
  assert (Hs : Qle 0 (q * q)) by (apply QleT'_to_Qle; apply Qsquare_nonneg).
  assert (H1 : QltT 0 (1 + q * q)).
  { apply Qlt_to_QltT. apply (Qlt_le_trans 0 1 (1 + q * q)).
    - unfold Qlt. simpl. lia.
    - apply (Qle_trans 1 (1 + 0) (1 + q * q)).
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      + apply Qplus_le_compat. apply Qle_refl. exact Hs. }
  exact (q_neq_of_lt (1 + q * q) H1).
Defined.

(* ============================================================ *)
(* Item 2: the exact slope-composition identity (division form — the    *)
(* algebraic core of phi'(t) = 0, with the O(s^2) remainder explicit).  *)
(* ============================================================ *)
Lemma abl9_slope_id : forall u v s : Q,
  ~ (1 + (u + s) * v == 0) -> ~ (1 + u * v == 0) ->
  QeqT
    (s / (1 + u * u)
    - ((u + s - v) / (1 + (u + s) * v) - (u - v) / (1 + u * v))
      * ((1 + u * v) * (1 + u * v) / ((1 + u * u) * (1 + v * v))))
    (s * s * v / ((1 + (u + s) * v) * (1 + u * u))).
Proof.
  intros u v s H1 H2.
  assert (Hu2 : ~ (1 + u * u == 0)).
  { intros Hz. apply qeq_imp_qeqT in Hz. apply (abl9_q_pos_sq u) in Hz.
    destruct Hz. }
  assert (Hv2 : ~ (1 + v * v == 0)).
  { intros Hz. apply qeq_imp_qeqT in Hz. apply (abl9_q_pos_sq v) in Hz.
    destruct Hz. }
  apply qeq_imp_qeqT.
  field. repeat split; assumption.
Defined.

(* ============================================================ *)
(* Item 3: the Q absolute-value shift triangle (|a| <= |a-b| + |b|).    *)
(* ============================================================ *)
Lemma abl9_abs_shift : forall a b : Q, QleT' (Qabs a) (Qabs (a - b) + Qabs b).
Proof.
  intros a b.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs a) (Qabs ((a - b) + b)) (Qabs (a - b) + Qabs b)).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply abl9_Qabs_wd. ring.
  - apply Qabs_triangle.
Defined.

(* ============================================================ *)
(* Item 3: |x| <= x for x >= 0 (Qabs_pos is directly usable here).      *)
(* ============================================================ *)
Lemma abl9_Qabs_le_self : forall x : Q, Qle 0 x -> QleT' (Qabs x) x.
Proof.
  intros x H. apply qeq_imp_qle. apply qeq_imp_qeqT.
  exact (Qabs_pos x H).
Defined.

(* ============================================================ *)
(* Item 3: a per-point eventual upper bound for a Cauchy real           *)
(* (constructive; a single cauchy call at eps = 1 plus the abs-shift    *)
(* triangle).                                                           *)
(* ============================================================ *)
Lemma abl9_real_tail_bnd : forall x : Real,
  sigT (fun B : Q => And (QltT 0 B)
    (sigT (fun N : nat => forall n : nat, NatLe N n ->
       QleT' (Qabs (projT1 x n)) B))).
Proof.
  intros x. destruct x as [u Hu].
  assert (H1 : QltT 0 1) by reflexivity.
  destruct (Hu 1 H1) as [N HN].
  exists (Qabs (u N) + 1).
  split.
  - apply Qlt_to_QltT.
    assert (H1le : Qle 1 (Qabs (u N) + 1)).
    { apply (Qle_trans 1 (1 + 0) (Qabs (u N) + 1)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      - apply (Qle_trans (1 + 0) (1 + Qabs (u N)) (Qabs (u N) + 1)).
        + apply Qplus_le_compat. apply Qle_refl. apply Qabs_nonneg.
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    apply (Qlt_le_trans 0 1 (Qabs (u N) + 1)).
    + unfold Qlt. simpl. lia.
    + exact H1le.
  - exists N. intros n Hn.
    apply Qle_to_QleT'.
    apply (Qle_trans (Qabs (u n)) (Qabs (u n - u N) + Qabs (u N))
                     (Qabs (u N) + 1)).
    + apply QleT'_to_Qle. apply (abl9_abs_shift (u n) (u N)).
    + apply (Qle_trans (Qabs (u n - u N) + Qabs (u N))
                       (1 + Qabs (u N)) (Qabs (u N) + 1)).
      * apply Qplus_le_compat.
        -- apply Qlt_le_weak. apply QltT_to_Qlt.
           apply (HN n N).
           ++ exact Hn.
           ++ apply NatLe_lift. apply Nat.le_refl.
        -- apply Qle_refl.
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Defined.

(* ============================================================ *)
(* Item 3: the small-span constant criterion — a uniform increment      *)
(* estimate forces real_eq.                                             *)
(* ============================================================ *)
Lemma abl9_const_crit :
  forall (phi : Real -> Real) (a s delta : Real),
  real_lt real_zero delta ->
  real_lt (real_abs s) delta ->
  (forall (eps eps' : Real), real_lt real_zero eps -> real_lt real_zero eps' ->
     real_le (real_abs (real_plus (phi (real_plus a s)) (real_opp (phi a))))
             (real_plus (real_mult eps (real_abs s)) eps')) ->
  real_eq (phi (real_plus a s)) (phi a).
Proof.
  intros phi a s delta Hdelta Hspan Hstep eps Heps.
  assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  destruct (abl9_real_tail_bnd s) as [B [HB0 [Nb HB]]].
  assert (HBQ : Qlt 0 B) by (apply QltT_to_Qlt; exact HB0).
  assert (HB1 : Qlt 0 (B + 1)).
  { apply (Qlt_le_trans 0 B (B + 1)).
    - exact HBQ.
    - apply (Qle_trans B (B + 0) (B + 1)).
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      + apply Qplus_le_compat. apply Qle_refl. unfold Qle. simpl. lia. }
  set (c := (eps / (8 * (B + 1)))%Q).
  assert (Hc0 : Qlt 0 c).
  { unfold c. unfold Qdiv. apply Qmult_lt_0_compat.
    - exact HepsQ.
    - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
      + unfold Qlt. simpl. lia.
      + exact HB1. }
  (* Budget: c*B <= eps/8. *)
  assert (HB1le : Qle B (B + 1)).
  { apply (Qle_trans B (B + 0) (B + 1)).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    - apply Qplus_le_compat. apply Qle_refl. unfold Qle. simpl. lia. }
  assert (Hden : ~ (B + 1 == 0)).
  { intros Hz.
    assert (H00 : Qlt 0 0)
      by (apply (Qlt_le_trans 0 (B + 1) 0); [exact HB1 | apply QleT'_to_Qle; apply qeq_imp_qle; apply qeq_imp_qeqT; exact Hz]).
    exact (Qlt_not_le 0 0 H00 (Qle_refl 0)). }
  assert (HcB : Qle (c * B) ((1 # 8) * eps)).
  { apply (Qle_trans (c * B) (c * (B + 1)) ((1 # 8) * eps)).
    - rewrite (Qmult_comm c B). rewrite (Qmult_comm c (B + 1)).
      apply Qmult_le_compat_r.
      + exact HB1le.
      + apply Qlt_le_weak. exact Hc0.
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
      unfold c. unfold Qdiv. field. assumption. }
  assert (Hc' : real_lt real_zero (real_const c))
    by (apply real_const_pos_f1; exact Hc0).
  assert (He2 : real_lt real_zero (real_const (eps / 2))).
  { apply real_const_pos_f1. apply Qlt_shift_div_l.
    - reflexivity.
    - simpl. apply QltT_to_Qlt. exact Heps. }
  assert (Hcsn : forall n : nat, NatLe Nb n ->
            Qle (c * Qabs (projT1 s n)) ((1 # 8) * eps)).
  { intros n Hn. apply (Qle_trans (c * Qabs (projT1 s n)) (c * B) ((1 # 8) * eps)).
    - rewrite (Qmult_comm c (Qabs (projT1 s n))). rewrite (Qmult_comm c B).
      apply Qmult_le_compat_r.
      + apply QleT'_to_Qle. apply (HB n). exact Hn.
      + apply Qlt_le_weak. exact Hc0.
    - exact HcB. }
  destruct (Hstep (real_const c) (real_const (eps / 2)) Hc' He2) as [Hr | Hr].
  - (* real_lt branch: there are q > 0 and M with q < bound_n - |diff_n| for all n >= M. *)
    destruct Hr as [q [Hq0 [M Hq]]].
    exists (Nat.max Nb M).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hnb : (Nb <= n)%nat) by lia.
    assert (Hm : (M <= n)%nat) by lia.
    assert (HnNb : NatLe Nb n) by (apply NatLe_lift; exact Hnb).
    set (dn := projT1 (phi (real_plus a s)) n).
    set (an := projT1 (phi a) n).
    assert (Hqn : Qlt q (c * Qabs (projT1 s n) + eps / 2 - Qabs (dn - an))).
    { apply (Qlt_le_trans q
        (projT1 (real_plus (real_mult (real_const c) (real_abs s))
                           (real_const (eps / 2))) n
         - projT1 (real_abs (real_plus (phi (real_plus a s))
                                        (real_opp (phi a)))) n)
        (c * Qabs (projT1 s n) + eps / 2 - Qabs (dn - an))).
      - apply QltT_to_Qlt. apply (Hq n). apply NatLe_lift. exact Hm.
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const c) (real_abs s))
                   (real_const (eps / 2)) n)).
        rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const c) (real_abs s) n)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj c n)).
        rewrite (qeqT_imp_qeq _ _ (real_abs_proj s n)).
        rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (phi (real_plus a s))
                                    (real_opp (phi a))) n)).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (phi (real_plus a s)) (real_opp (phi a)) n)).
        rewrite (qeqT_imp_qeq _ _ (real_opp_proj (phi a) n)).
        cbn [projT1 real_const real_zero].
        unfold dn, an. reflexivity. }
    assert (Hqn2 : Qlt 0 ((c * Qabs (projT1 s n) + eps / 2 - q) - Qabs (dn - an))).
    { apply QltT_to_Qlt.
      apply (abl9_Qlt_transfer_r 0
               ((c * Qabs (projT1 s n) + eps / 2) - Qabs (dn - an) - q)
               ((c * Qabs (projT1 s n) + eps / 2 - q) - Qabs (dn - an))).
      - field.
      - apply (proj1 (Qlt_minus_iff q
                   (c * Qabs (projT1 s n) + eps / 2 - Qabs (dn - an)))).
        exact Hqn. }
    assert (Hd1 : Qlt (Qabs (dn - an)) (c * Qabs (projT1 s n) + eps / 2)).
    { apply (Qlt_trans (Qabs (dn - an))
             (c * Qabs (projT1 s n) + eps / 2 - q)
             (c * Qabs (projT1 s n) + eps / 2)).
      - apply (proj2 (Qlt_minus_iff (Qabs (dn - an))
                 (c * Qabs (projT1 s n) + eps / 2 - q))). exact Hqn2.
      - apply (proj2 (Qlt_minus_iff (c * Qabs (projT1 s n) + eps / 2 - q)
                 (c * Qabs (projT1 s n) + eps / 2))).
        apply QltT_to_Qlt.
        apply (abl9_QltT_transfer_r 0 q
                 ((c * Qabs (projT1 s n) + eps / 2)
                  - (c * Qabs (projT1 s n) + eps / 2 - q))).
        + apply Qeq_sym.
          assert (Heqq : (c * Qabs (projT1 s n) + eps / 2)
                         - (c * Qabs (projT1 s n) + eps / 2 - q) == q) by ring.
          exact Heqq.
        + exact Hq0. }
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (Qabs (dn - an))
                        (c * Qabs (projT1 s n) + eps / 2) eps).
    + exact Hd1.
    + apply (Qle_trans (c * Qabs (projT1 s n) + eps / 2)
                       ((1 # 8) * eps + (1 # 2) * eps) eps).
      * apply Qplus_le_compat.
        -- apply (Hcsn n HnNb).
        -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. field.
      * apply (Qle_trans ((1 # 8) * eps + (1 # 2) * eps) (1 * eps)).
        -- apply (Qle_trans ((1 # 8) * eps + (1 # 2) * eps) ((5 # 8) * eps) (1 * eps)).
           ++ apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. field.
           ++ apply Qmult_le_compat_r.
              ** unfold Qle. simpl. lia.
              ** apply Qlt_le_weak. exact HepsQ.
        -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - (* real_eq branch: the pointwise gap of the two bounds is eventually below *)
    (* eps/8; the triangle chain plus the budget close the goal. *)
    assert (He8q : QltT 0 (eps / 8)).
    { apply Qlt_to_QltT. apply Qlt_shift_div_l.
      - reflexivity.
      - simpl. apply QltT_to_Qlt. exact Heps. }
    destruct (Hr (eps / 8) He8q) as [N2 H2].
    exists (Nat.max Nb N2).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hnb : (Nb <= n)%nat) by lia.
    assert (Hn2 : (N2 <= n)%nat) by lia.
    assert (HnNb : NatLe Nb n) by (apply NatLe_lift; exact Hnb).
    set (dn := projT1 (phi (real_plus a s)) n).
    set (an := projT1 (phi a) n).
    set (MID := (c * Qabs (projT1 s n) + eps / 2)%Q).
    set (AB := Qabs (Qabs (dn - an) - MID)%Q).
    assert (H2' : QltT AB (eps / 8)).
    { apply (abl9_QltT_transfer_l
        (Qabs (projT1 (real_abs (real_plus (phi (real_plus a s))
                          (real_opp (phi a)))) n
               - projT1 (real_plus (real_mult (real_const c) (real_abs s))
                                   (real_const (eps / 2))) n))).
      - rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus (phi (real_plus a s))
                                    (real_opp (phi a))) n)).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (phi (real_plus a s)) (real_opp (phi a)) n)).
        rewrite (qeqT_imp_qeq _ _ (real_opp_proj (phi a) n)).
        rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const c) (real_abs s))
                   (real_const (eps / 2)) n)).
        rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const c) (real_abs s) n)).
        rewrite (qeqT_imp_qeq _ _ (real_const_proj c n)).
        rewrite (qeqT_imp_qeq _ _ (real_abs_proj s n)).
        cbn [projT1 real_const real_zero].
        unfold AB, MID, dn, an. apply qeqT_imp_qeq. apply abl9_Qabs_wd. reflexivity.
      - exact (H2 n (NatLe_lift _ _ Hn2)). }
    assert (HY0 : Qle 0 MID).
    { apply (Qle_trans 0 (c * Qabs (projT1 s n)) MID).
      - apply (Qmult_le_0_compat c (Qabs (projT1 s n))).
        + apply Qlt_le_weak. exact Hc0.
        + apply Qabs_nonneg.
      - unfold MID. apply (Qle_plus_nonneg_r (c * Qabs (projT1 s n)) (eps / 2)).
        apply Qlt_le_weak. apply Qlt_shift_div_l.
        * reflexivity.
        * simpl. apply QltT_to_Qlt. exact Heps. }
    assert (Htri : Qle (Qabs (dn - an)) (AB + MID)).
    { (* |d| = Qabs(|d|) (Qabs is idempotent on nonnegative arguments) and *)
      (* |d| = |(|d|-MID)+MID| (ring identity) <= ||d|-MID| + |MID|       *)
      (* = AB + |MID| <= AB + MID. *)
      assert (Hid : Qabs (dn - an) == Qabs (Qabs (dn - an))).
      { apply Qeq_sym. exact (Qabs_pos (Qabs (dn - an)) (Qabs_nonneg (dn - an))). }
      apply (Qle_trans (Qabs (dn - an))
             (Qabs (Qabs (dn - an) - MID) + Qabs MID)
             (AB + MID)).
      - apply (Qle_trans (Qabs (dn - an))
               (Qabs (Qabs (dn - an)))
               (Qabs (Qabs (dn - an) - MID) + Qabs MID)).
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact Hid.
        + apply (Qle_trans (Qabs (Qabs (dn - an)))
                 (Qabs ((Qabs (dn - an) - MID) + MID))
                 (Qabs (Qabs (dn - an) - MID) + Qabs MID)).
          * apply QleT'_to_Qle. apply qeq_imp_qle. apply abl9_Qabs_wd. ring.
          * apply Qabs_triangle.
      - unfold AB. apply Qplus_le_compat.
        + apply Qle_refl.
        + apply QleT'_to_Qle. apply abl9_Qabs_le_self. exact HY0. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (dn - an)) (AB + MID) eps).
    + exact Htri.
    + (* AB + MID < eps/8 + MID (via the Qlt_minus_iff primitive), then the budget gives < eps. *)
      assert (Hstep1 : Qlt (AB + MID) (eps / 8 + MID)).
      { apply (proj2 (Qlt_minus_iff (AB + MID) (eps / 8 + MID))).
        apply QltT_to_Qlt.
        apply (abl9_Qlt_transfer_r 0 (eps / 8 - AB) ((eps / 8 + MID) - (AB + MID))).
        - field.
        - apply (proj1 (Qlt_minus_iff AB (eps / 8))).
          apply QltT_to_Qlt. exact H2'. }
      apply (Qlt_le_trans (AB + MID) (eps / 8 + MID) eps).
      * exact Hstep1.
      * apply (Qle_trans (eps / 8 + MID)
                         (eps / 8 + ((1 # 8) * eps + (1 # 2) * eps)) eps).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply Qplus_le_compat.
              ** unfold MID. apply (Hcsn n HnNb).
              ** apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. field.
        -- apply (Qle_trans (eps / 8 + ((1 # 8) * eps + (1 # 2) * eps))
                            ((3 # 4) * eps) eps).
           ++ apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
              assert (Heq : eps / 8 + ((1 # 8) * eps + (1 # 2) * eps)
                            == (3 # 4) * eps) by field.
              exact Heq.
           ++ apply (Qle_trans ((3 # 4) * eps) (1 * eps)).
              ** apply Qmult_le_compat_r.
                 --- unfold Qle. simpl. lia.
                 --- apply Qlt_le_weak. exact HepsQ.
              ** apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Defined.

(* ============================================================ *)
(* Six supply pieces for the phi assembly (the direct premises of the   *)
(* main theorem): two domain pieces in the pointwise Q form, and the    *)
(* well-definedness / alignment / zero pieces at the setoid layer.      *)
(* ============================================================ *)

(* Domain piece D0: the two-sided unpacking of |t| <= b (Qabs has no     *)
(* multiplicative distribution lemma, so the proof splits on the sign).  *)
Lemma abl9_q_abs_two_sided_le : forall t b : Q,
  Qle (Qabs t) b -> And (QleT' (- b) t) (QleT' t b).
Proof.
  intros t b Hab.
  assert (Hb0 : Qle 0 b)
    by (apply (Qle_trans 0 (Qabs t) b); [apply Qabs_nonneg | exact Hab]).
  destruct (Qlt_le_dec 0 t) as [Htp | Htn].
  - assert (Ht0 : Qle 0 t) by (apply Qlt_le_weak; exact Htp).
    assert (Habs : Qabs t == t) by exact (Qabs_pos t Ht0).
    split.
    + apply Qle_to_QleT'.
      apply (Qle_trans (- b) 0 t).
      * apply (Qle_trans (- b) (- 0) 0).
        -- apply (Qopp_le_compat 0 b). exact Hb0.
        -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      * exact Ht0.
    + apply Qle_to_QleT'.
      apply (Qle_trans t (Qabs t) b).
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
        apply Qeq_sym. exact Habs.
      * exact Hab.
  - assert (Ht0' : Qle t 0) by exact Htn.
    assert (Hnt0 : Qle 0 (- t)) by (apply (Qopp_le_compat t 0); exact Ht0').
    assert (Habs : Qabs t == - t).
    { apply (Qeq_trans (Qabs t) (Qabs (- t))).
      - apply Qeq_sym. apply Qabs_opp.
      - exact (Qabs_pos (- t) Hnt0). }
    split.
    + apply Qle_to_QleT'.
      apply (Qle_trans (- b) (- (- t)) t).
      * apply (Qopp_le_compat (- t) b).
        apply (Qle_trans (- t) (Qabs t) b).
        -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
           apply Qeq_sym. exact Habs.
        -- exact Hab.
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    + apply Qle_to_QleT'.
      apply (Qle_trans t 0 b).
      * exact Ht0'.
      * exact Hb0.
Defined.

(* Domain piece D1: the path-denominator bound — |a| <= 1, |t| <= 1/4    *)
(* gives 3/4 <= 1+(a+t)*a (the Q-layer arithmetic core of the pointwise  *)
(* bound 1+x(x+h) >= 3/4 along the path: a^2+ta >= -a/4 or a/4 depending *)
(* on the sign of a, with the square terms (a-1/8)^2 or (a+1/8)^2 >= 0). *)
Lemma abl9_q_path_den : forall a t : Q,
  Qle (Qabs a) 1 -> Qle (Qabs t) (1 # 4) ->
  QleT' (3 # 4) (1 + (a + t) * a).
Proof.
  intros a t Ha Ht.
  apply Qle_to_QleT'.
  destruct (abl9_q_abs_two_sided_le t (1 # 4) Ht) as [Htl Htu].
  destruct (abl9_q_abs_two_sided_le a 1 Ha) as [Hal Hau].
  destruct (Qlt_le_dec 0 a) as [Hap | Han].
  - (* a > 0: ta >= (-1/4)a; 1+a^2-a/4 = (a-1/8)^2 + 63/64 >= 63/64 >= 3/4 *)
    assert (Ha0 : Qle 0 a) by (apply Qlt_le_weak; exact Hap).
    assert (H34 : Qle (3 # 4) (63 # 64)) by (unfold Qle; simpl; lia).
    assert (Hta : Qle ((-1#4) * a) (t * a)).
    { apply (Qmult_le_compat_r (- (1#4)) t a).
      apply QleT'_to_Qle. exact Htl. exact Ha0. }
    apply (Qle_trans (3#4) (0 + (63#64)) (1 + (a + t) * a)).
    + apply (Qle_trans (3#4) (63#64) (0 + (63#64))).
      * exact H34.
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans (0 + (63#64))
                       ((a - (1#8)) * (a - (1#8)) + (63#64))
                       (1 + (a + t) * a)).
      * apply Qplus_le_compat.
        -- apply QleT'_to_Qle. apply Qsquare_nonneg.
        -- apply Qle_refl.
      * apply (Qle_trans ((a - (1#8)) * (a - (1#8)) + (63#64))
                       (1 + a * a + (-1#4) * a) (1 + (a + t) * a)).
        -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans (1 + a * a + (-1#4) * a)
                         (1 + a * a + t * a) (1 + (a + t) * a)).
           ++ apply Qplus_le_compat. apply Qle_refl. exact Hta.
           ++ apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - (* a <= 0: t <= 1/4 with a <= 0 flips the inequality to ta >= (1/4)a; *)
    (* 1+a^2+a/4 = (a+1/8)^2 + 63/64 *)
    assert (Ha0' : Qle a 0) by exact Han.
    assert (H34 : Qle (3 # 4) (63 # 64)) by (unfold Qle; simpl; lia).
    assert (Hta : Qle ((1#4) * a) (t * a)).
    { assert (E1 : t * a == (- t) * (- a)) by ring.
      assert (E2 : (1#4) * a == (- (1#4)) * (- a)) by ring.
      apply (Qle_trans ((1#4) * a) ((- (1#4)) * (- a)) (t * a)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact E2.
      - apply (Qle_trans ((- (1#4)) * (- a)) ((- t) * (- a)) (t * a)).
        + apply (Qmult_le_compat_r (- (1#4)) (- t) (- a)).
          * exact (Qopp_le_compat t (1#4) (QleT'_to_Qle _ _ Htu)).
          * apply (Qle_trans 0 (- 0) (- a)).
            -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
            -- apply (Qopp_le_compat a 0). exact Ha0'.
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          apply Qeq_sym. exact E1. }
    apply (Qle_trans (3#4) (0 + (63#64)) (1 + (a + t) * a)).
    + apply (Qle_trans (3#4) (63#64) (0 + (63#64))).
      * exact H34.
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans (0 + (63#64))
                       ((a + (1#8)) * (a + (1#8)) + (63#64))
                       (1 + (a + t) * a)).
      * apply Qplus_le_compat.
        -- apply QleT'_to_Qle. apply Qsquare_nonneg.
        -- apply Qle_refl.
      * apply (Qle_trans ((a + (1#8)) * (a + (1#8)) + (63#64))
                       (1 + a * a + (1#4) * a) (1 + (a + t) * a)).
        -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans (1 + a * a + (1#4) * a)
                         (1 + a * a + t * a) (1 + (a + t) * a)).
           ++ apply Qplus_le_compat. apply Qle_refl. exact Hta.
           ++ apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Defined.

(* Well-definedness piece A: cauchy_real_arctan lifts to the real layer  *)
(* (pointwise route: the arctan projection identities plus the pointwise *)
(* Q equality, lifted by real_eq_of_zero_diff — no approximation chain). *)
Lemma abl9_arctan_wd_real : forall (u v : Real)
  (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) 1)
  (Hv : forall n : nat, QleT' (Qabs (projT1 v n)) 1),
  (forall n : nat, projT1 u n == projT1 v n) ->
  real_eq (cauchy_real_arctan u Hu) (cauchy_real_arctan v Hv).
Proof.
  intros u v Hu Hv Hpt.
  apply real_eq_of_zero_diff.
  intros n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (arctan_real_proj u Hu n)).
  rewrite (qeqT_imp_qeq _ _ (arctan_real_proj v Hv n)).
  rewrite (qeqT_imp_qeq _ _ (b5c_arctan_partial_wd n (projT1 u n) (projT1 v n) (Hpt n))).
  ring.
Defined.

(* Zero piece C: arctan at the zero argument equals 0 (the w-side of the *)
(* endpoint value phi(0); via b5c_arctan_partial_wd and the zero point). *)
Lemma abl9_arctan_zero_pt : forall (u : Real)
  (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) 1),
  (forall n : nat, projT1 u n == 0) ->
  real_eq (cauchy_real_arctan u Hu) real_zero.
Proof.
  intros u Hu Hpt.
  apply real_eq_of_zero_diff.
  intros n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (arctan_real_proj u Hu n)).
  rewrite (qeqT_imp_qeq _ _ (b5c_arctan_partial_wd n (projT1 u n) 0 (Hpt n))).
  cbn [projT1 real_zero].
  rewrite (qeqT_imp_qeq _ _ (b5c_arctan_partial_zero n)).
  ring.
Defined.

(* Alignment piece B: the composite argument w(x) equals the intended    *)
(* right-hand-side argument (a real_mult commutativity/compatibility     *)
(* alignment chain; (x+h)+(-x) == h pointwise).                          *)
Lemma abl9_w_align : forall (x h : Real)
  (Hd : real_lt real_zero (real_plus real_one (real_mult (real_plus x h) x))),
  real_eq (real_mult (real_plus (real_plus x h) (real_opp x))
                     (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd))
          (real_mult (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd) h).
Proof.
  intros x h Hd.
  apply (real_eq_trans
          (real_mult (real_plus (real_plus x h) (real_opp x))
                     (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd))
          (real_mult h (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd))
          (real_mult (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd) h)).
  - apply (RealSetoid.real_eq_mult_compat
             (real_plus (real_plus x h) (real_opp x))
             (real_inv_pos (real_plus real_one (real_mult (real_plus x h) x)) Hd)
             h
             (real_inv_pos (real_plus real_one (real_mult (real_plus x h) x)) Hd)).
    + apply real_eq_of_zero_diff. intros n.
      apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus x h) (real_opp x) n)).
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj x h n)).
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)).
      cbn [projT1]. ring.
    + apply real_eq_refl.
  - exact (real_mult_comm h (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x h) x)) Hd)).
Defined.

(* Zero piece C2: w(x) == 0 (the w-side of the endpoint value phi(0);    *)
(* at t := real_zero the composite argument projects to 0 pointwise).    *)
Lemma abl9_wx_zero : forall (x : Real)
  (Hd : real_lt real_zero
          (real_plus real_one (real_mult (real_plus x real_zero) x))),
  real_eq (real_mult (real_plus (real_plus x real_zero) (real_opp x))
                     (real_inv_pos (real_plus real_one
                        (real_mult (real_plus x real_zero) x)) Hd))
          real_zero.
Proof.
  intros x Hd.
  apply real_eq_of_zero_diff.
  intros n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_plus (real_plus x real_zero) (real_opp x))
             (real_inv_pos (real_plus real_one
                (real_mult (real_plus x real_zero) x)) Hd) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus x real_zero) (real_opp x) n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj x real_zero n)).
  rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)).
  cbn [projT1 real_zero].
  ring.
Defined.

(* ============================================================ *)
(* Final checks: the assumption face and the extraction test.           *)
(*   Triple tally: the list of 17 lemma names = 17 closure commands     *)
(*   (Defined) = 17 Print Assumptions statements, with zero discrepancy.*)
(* ============================================================ *)
Print Assumptions abl9_QltT_transfer_l.
Print Assumptions abl9_QltT_transfer_r.
Print Assumptions abl9_Qlt_transfer_l.
Print Assumptions abl9_Qlt_transfer_r.
Print Assumptions abl9_Qabs_wd.
Print Assumptions abl9_q_pos_sq.
Print Assumptions abl9_slope_id.
Print Assumptions abl9_abs_shift.
Print Assumptions abl9_real_tail_bnd.
Print Assumptions abl9_const_crit.
Print Assumptions abl9_Qabs_le_self.
Print Assumptions abl9_q_abs_two_sided_le.
Print Assumptions abl9_q_path_den.
Print Assumptions abl9_arctan_wd_real.
Print Assumptions abl9_arctan_zero_pt.
Print Assumptions abl9_w_align.
Print Assumptions abl9_wx_zero.

(* Extraction test (criterion: the output has Obj.magic count 0). *)
Recursive Extraction abl9_q_pos_sq abl9_slope_id abl9_real_tail_bnd.
Recursive Extraction abl9_q_path_den abl9_arctan_wd_real abl9_arctan_zero_pt.
