(* Five-field pointer | Module: LW2MetricCompat.v.
   Mission. Metric losslessness along Cauchy equivalence (isometric compatibility):
   if reals X and Y are Cauchy equivalent (real_eq), then the distance of X to the
   rational point q, real_metric X (real_const q), and the distance of Y to q,
   real_metric Y (real_const q), are equal as reals (real_eq). Constructed per eps:
   take the modulus N1 of real_eq X Y at eps as the common modulus witness; per point
   lic_metric_proj reduces both distance projections to Qabs (projT1 X n - q) and
   Qabs (projT1 Y n - q); q_abs_abs_triangle gives ||X_n - q| - |Y_n - q|| <=
   |X_n - Y_n| (difference side rearranged by ring), closed against eps by
   Qle_lt_trans.
   Dependencies. S01_BaseRing (Set-level NatLe); S02_CauchyComplete (Real, real_eq,
   real_const, QltT, QltT_to_Qlt, Qlt_to_QltT, QleT'_to_Qle); S03_QExp (real_metric,
   q_abs_abs_triangle); UpReqIrrationalCriterion (lic_metric_proj per-point projection
   reduction).
   References. Bishop, constructive analysis: losslessness of the metric along Cauchy
   equivalence (distance reals equal per eps); the per-eps projection-reduction craft
   is shared with LW2SepTransport.v.
   Constructivity. Statement face fully Set-level (real_eq is a Set-valued per-eps
   datum; the identity is taken as real_eq). Zero classical logic; the Require face
   lists only the four in-tree dependency modules; the proof body uses
   only the triangle inequality and equation rearrangement. Tree-signature note:
   q_abs_abs_triangle is QleT'-faced (S03:6689), so its single consumption site is
   lowered to the Prop Qle face by the in-registry wrapped bridge QleT'_to_Qle
   (S02:103) in eta-expanded term form; the internal ring-chain equality assert stays
   on the Prop face, which is legal inside a proof body.
   Build. rocq c -native-compiler no -q -Q . "" LW2MetricCompat.v, working directory
   = the seat sandbox world (flat single level, empty logical prefix); COQLIB and
   ROCQLIB environment variables are unset for the born compile.
*)

From Stdlib Require Import QArith.QArith QArith.Qabs.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqIrrationalCriterion.
Opaque Qred.

(* Isometric compatibility: two Cauchy-equivalent reals have equal distances, as
   reals, to the same rational point. *)
Lemma lw2t_metric_compat : forall (X Y : Real) (q : Q),
  real_eq X Y ->
  real_eq (real_metric X (real_const q)) (real_metric Y (real_const q)).
Proof.
  intros X Y q Heq.
  unfold real_eq. intros eps Heps.
  destruct (Heq eps Heps) as [N1 HN1].
  exists N1. intros n Hn.
  apply Qlt_to_QltT.
  rewrite (lic_metric_proj X q n).
  rewrite (lic_metric_proj Y q n).
  pose proof (HN1 n Hn) as Hd.
  apply QltT_to_Qlt in Hd.
  apply (Qle_lt_trans _ (Qabs (projT1 X n - projT1 Y n))).
  - (* q_abs_abs_triangle is QleT'-faced in the tree (S03:6689); the wrapped bridge
       QleT'_to_Qle (S02:103) lowers it to this Prop Qle site (eta-expanded term). *)
    pose proof (QleT'_to_Qle _ _
      (q_abs_abs_triangle (projT1 X n - q)%Q (projT1 Y n - q)%Q)) as Htri.
    assert (Hring : ((projT1 X n - q) - (projT1 Y n - q) ==
                     projT1 X n - projT1 Y n)%Q) by ring.
    rewrite Hring in Htri. exact Htri.
  - exact Hd.
Qed.

Print Assumptions lw2t_metric_compat.
