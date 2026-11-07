(* ConstructiveWorld-Set — transport of pointwise separation across Cauchy-equal reals. *)

(** * LW2SepTransport: separation transport along Cauchy-equal reals.

    Mission.  If [X] and [Y] are Cauchy equal ([real_eq]) and [X] is pointwise separated from the rational point
      [q] with radius [c] ([real_lt (real_const c) (real_metric X (real_const q))]), then [Y] is separated from [q]
      with radius [c/2].  The general form [lw2t_sep_transport_k] carries the degeneracy factor [k] explicitly
      ([QleT 2 k], i.e. k >= 2): the separation radius shrinks to [c/k] and the equality modulus is instantiated at
      budget [c/(2k)]; [lw2t_sep_transport] is the compatibility specialization at [k := 2]; [lw2t_sep_transport_sym]
      transports in the reverse direction.  The witness is built per eps: the equality modulus [N1] and the separation
      modulus [N2] are combined by [Nat.max], reduced pointwise through two [lic_metric_proj] projections, and closed
      by the reverse triangle inequality [q_abs_abs_triangle]; the degeneracy kernel is the c-fold scaling of [2*(1/k) <= 1].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Arith.Arith], [Lia], [Lqa].  Requires [S01_BaseRing]
      (Set layer [Id]/[And]/[Or]/[NatLe]), [S02_CauchyComplete] ([Real], [real_eq], [real_lt], [QltT]/[QleT]/[QleT'],
      [real_const_proj], [real_eq_sym], [NatLe_lift]/[NatLe_drop], [qeq_le], [QltT_to_Qlt]/[Qlt_to_QltT]), [S03_QExp]
      ([real_metric], [q_abs_abs_triangle]), and [UpReqIrrationalCriterion] ([lic_metric_proj] pointwise projection reduction)
      of this development.

    References.  This development, LW2SepTransport.v, the baseline module in ConstructiveWorld-Main whose statement
      names are carried over here verbatim (statement-face Set-carrier completion).  Transitivity of pointwise separation
      (per-eps independence) along Cauchy equality after the constructive analysis treatment of separation; the explicit
      degeneracy factor keeps the separation radius monotone non-increasing under transport ([c/k] for k >= 2, no amplification).

    Constructivity.  The statement face is entirely Set-layer ([QltT]/[QleT]/[real_lt]/[sigT], identity taken as the S01
      Set layer [Id]); zero admission tokens, no classical logic, and the Require face introduces no axiom modules; linear
      decision of Q-layer inequalities uses [Lqa] throughout; the witness of [QleT] at [k := 2] is given explicitly as [inr id_refl].

    Build.  [coqc -native-compiler no -q -Q . "" LW2SepTransport.v] compiles cleanly (exit 0); the first eight bytes of the artifact are [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia Lqa.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqIrrationalCriterion.
Opaque Qred.

(* k >= 2 implies positivity of the reciprocal: 0 < 1/k (the Id branch
   closes by definitional reduction) *)
Lemma lw2t_qinv_pos : forall k : Q, QleT 2 k -> QltT 0 (Qinv k).
Proof.
  intros k Hk. destruct Hk as [Hlt | Hid].
  - apply Qlt_to_QltT. apply Qinv_lt_0_compat.
    apply QltT_to_Qlt in Hlt. lra.
  - destruct Hid. exact id_refl.
Qed.

(* k >= 2 implies 2*(1/k) <= 1: the arithmetic kernel of the
   degeneracy factor (both sides multiplied by the positive 1/k) *)
Lemma lw2t_k_inv2_le : forall k : Q, QleT 2 k -> QleT' (2 * Qinv k) 1.
Proof.
  intros k Hk. destruct Hk as [Hlt | Hid].
  - apply QltT_to_Qlt in Hlt.
    assert (Hk0 : (0 < k)%Q) by lra.
    assert (Hinvpos : (0 < Qinv k)%Q) by (apply Qinv_lt_0_compat; exact Hk0).
    apply Qle_to_QleT'.
    apply (Qle_trans _ (k * Qinv k)%Q).
    + apply Qmult_le_compat_r.
      * apply Qlt_le_weak. exact Hlt.
      * apply Qlt_le_weak. exact Hinvpos.
    + assert (Hne : ~ (k == 0)%Q).
      { intro Hz. rewrite Hz in Hk0. exact (Qlt_irrefl 0 Hk0). }
      rewrite (Qmult_inv_r k Hne). apply Qle_refl.
  - destruct Hid. exact id_refl.
Qed.

Theorem lw2t_sep_transport_k : forall (X Y : Real) (q c k : Q),
  QltT 0 c -> QleT 2 k -> real_eq X Y ->
  real_lt (real_const c) (real_metric X (real_const q)) ->
  real_lt (real_const (c / k)%Q) (real_metric Y (real_const q)).
Proof.
  intros X Y q c k Hc Hk Heq Hsep.
  pose proof (lw2t_qinv_pos k Hk) as Hkpos.
  pose proof (lw2t_k_inv2_le k Hk) as Hk2.
  apply QltT_to_Qlt in Hkpos. apply QltT_to_Qlt in Hc.
  destruct Hsep as [eps0 [Heps0 [N2 HN2]]].
  apply QltT_to_Qlt in Heps0.
  assert (Hbinv : (Qinv (2 * k) == (1#2) * Qinv k)%Q).
  { rewrite Qinv_mult_distr.
    assert (Hq2 : (Qinv 2 == (1#2))%Q) by reflexivity.
    rewrite Hq2. reflexivity. }
  assert (Hbud : QltT 0 (c * Qinv (2 * k))%Q).
  { apply Qlt_to_QltT. rewrite Hbinv. apply Qmult_lt_0_compat.
    - exact Hc.
    - apply Qmult_lt_0_compat.
      + lra.
      + exact Hkpos. }
  destruct (Heq (c * Qinv (2 * k))%Q Hbud) as [N1 HN1].
  exists (c * Qinv (2 * k))%Q. split.
  - exact Hbud.
  - exists (Nat.max N1 N2). intros n Hn.
    assert (Hn1 : NatLe N1 n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2);
      [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
    assert (Hn2 : NatLe N2 n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2);
      [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
    pose proof (HN2 n Hn2) as Hx.
    apply QltT_to_Qlt in Hx.
    rewrite (lic_metric_proj X q n) in Hx.
    rewrite (qeqT_imp_qeq _ _ (real_const_proj c n)) in Hx.
    pose proof (HN1 n Hn1) as Hy.
    apply QltT_to_Qlt in Hy.
    destruct X as [u Hu].
    cbn [projT1] in Hx.
    apply Qlt_to_QltT.
    rewrite (lic_metric_proj Y q n).
    rewrite (qeqT_imp_qeq _ _ (real_const_proj (c / k) n)).
    destruct Y as [v Hv].
    cbn [projT1] in Hy.
    cbn [projT1].
    assert (Hr : (v n - q == (u n - q) - (u n - v n))%Q) by ring.
    assert (Htri : Qle (Qabs (Qabs (u n - q) - Qabs (u n - v n))) (Qabs (v n - q))).
    { rewrite Hr. apply QleT'_to_Qle. apply q_abs_abs_triangle. }
    destruct (proj1 (Qabs_Qle_condition (Qabs (u n - q) - Qabs (u n - v n))
                                        (Qabs (v n - q))) Htri) as [_ HAB].
    assert (Hbm : Qle (2 * (c * Qinv (2 * k)) + c * Qinv k) c).
    { assert (Hring : (2 * (c * Qinv (2 * k)) + c * Qinv k == c * (2 * Qinv k))%Q).
      { rewrite Hbinv. ring. }
      rewrite Hring.
      apply (Qle_trans _ (c * 1)%Q).
      - apply (proj2 (Qmult_le_l (2 * Qinv k) 1 c Hc)). exact (QleT'_to_Qle _ _ Hk2).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qmult_1_r. }
    assert (Hchain : Qlt (c + eps0 - (c * Qinv (2 * k))) (Qabs (v n - q))) by lra.
    assert (Hmform : (c / k == c * Qinv k)%Q) by reflexivity.
    rewrite Hmform.
    lra.
Qed.

Theorem lw2t_sep_transport : forall (X Y : Real) (q c : Q),
  QltT 0 c -> real_eq X Y ->
  real_lt (real_const c) (real_metric X (real_const q)) ->
  real_lt (real_const (c / 2)%Q) (real_metric Y (real_const q)).
Proof.
  intros X Y q c Hc Heq Hsep.
  exact (lw2t_sep_transport_k X Y q c 2 Hc (inr id_refl) Heq Hsep).
Qed.

Theorem lw2t_sep_transport_sym : forall (X Y : Real) (q c : Q),
  QltT 0 c -> real_eq X Y ->
  real_lt (real_const c) (real_metric Y (real_const q)) ->
  real_lt (real_const (c / 2)%Q) (real_metric X (real_const q)).
Proof.
  intros X Y q c Hc Heq Hsep.
  exact (lw2t_sep_transport Y X q c Hc (real_eq_sym X Y Heq) Hsep).
Qed.

Print Assumptions lw2t_sep_transport_k.
Print Assumptions lw2t_sep_transport.
Print Assumptions lw2t_sep_transport_sym.
