(* ConstructiveWorld-Set — polynomial segment positivity versus integral sign. *)

(** * PintPosGrid: pointwise positivity on a segment does not imply a positive integral.

    Mission.  For linear functionals the claim is false.  The quadratic
      [pg_counterex] = [-x^2 + x - 11/64] = [1/64 + (3/4 - x)(x - 1/4)] is
      pointwise at least [1/64] on [1/4, 3/4] ([pg_counterex_seg_ge],
      strictly [pg_counterex_seg_pos]), yet its integral is negative
      ([pg_counterex_int_neg], exact value [-1/192]); both arms are packaged
      as [pg_P1b_counterexample], so the statement needs strengthening.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Lists.List],
      [Arith.Arith], [ZArith.ZArith], [Lia], [Extraction].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [PolyIntegral] of this
      development.

    References.  This development, [PolyIntegral].v, whose functionals
      [pint_eval] and [pint_integral] are consumed here.  Strengthened
      routes: coefficient-level decomposition f = g + h with h of
      non-negative coefficients, and Bernstein-coefficient conditions.

    Constructivity.  All named statements are carried by [Set]
      ([QleT']/[QltT] faces; the witness pair is a [Type] product); premises
      are [QleT'] segment endpoints only.  Proofs are structured Q-chains
      with numeric facts by [vm_compute].  Statements extract with
      [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" PintPosGrid.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)


From Stdlib Require Import Extraction.
From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Arith.Arith
               ZArith.ZArith Lia.
Import ListNotations.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import PolyIntegral.

(* ============================================================ *)
(* Section 1. Internal support lemmas (Q layer, proof-internal).     *)
(* ============================================================ *)

(* the product of nonnegative numbers is nonnegative (Qle layer;
   [Qle_trans] through 0·b plus [Qmult_le_compat_r], following the
   pattern of [pm_mult_r0_le] in PintMono) *)
Lemma pg_mult0 : forall a b : Q, Qle 0 a -> Qle 0 b -> QleT' 0 (a * b).
Proof.
  intros a b Ha Hb. apply (Qle_to_QleT' 0 (a * b)).
  apply (Qle_trans 0 (0 * b) (a * b)).
  - rewrite Qmult_0_l. apply Qle_refl.
  - apply (Qmult_le_compat_r 0 a b).
    + exact Ha.
    + exact Hb.
Qed.

(* reshaping the right-subtracted end: x <= y -> 0 <= y - x (the
   two-sided [Qplus_le_compat] paired with [Qplus_opp_r] folding the
   left end; the stdlib track here has no one-sided le_compat_r) *)
Lemma pg_qle_minus_r : forall x y : Q, Qle x y -> QleT' 0 (y - x).
Proof.
  intros x y H. apply (Qle_to_QleT' 0 (y - x)).
  apply (Qle_trans 0 (x + (- x)) (y + (- x))).
  - rewrite Qplus_opp_r. apply Qle_refl.
  - apply (Qplus_le_compat x y (- x) (- x)).
    + exact H.
    + apply Qle_refl.
Qed.

(* numeric fact: 0 < 1/64 (one [vm_compute] step; same shape as
   [qltT_0_1] in S02) *)
Lemma pg_lt_1_64 : QltT 0 (1 # 64).
Proof. apply (Qlt_to_QltT 0 (1 # 64)). vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* Section 2. Counterexample definition and the identity leg.        *)
(* ============================================================ *)

(* the counterexample polynomial (pint coefficient-list encoding, head
   = constant term):
   pg_counterex(x) = -11/64 + x·(1 + x·(-1)) = -x² + x - 11/64 *)
Definition pg_counterex : list Q := (- 11 # 64) :: (1 # 1) :: (- 1 # 1) :: nil.

(* identity leg: pg_counterex(x) == 1/64 + (3/4−x)·(x−1/4)
   (carrying form of the square decomposition
   1/16 − (x−1/2)² = (3/4−x)(x−1/4)) *)
Lemma pg_counterex_eval_eq : forall x : Q,
  QeqT (pint_eval pg_counterex x) ((1 # 64) + ((3 # 4) - x) * (x - (1 # 4))).
Proof.
  intros x. apply qeq_imp_qeqT. unfold pg_counterex. cbn [pint_eval]. ring.
Qed.

(* ============================================================ *)
(* Section 3. First leg: pointwise positivity on the segment (with   *)
(* the explicit positive lower bound 1/64, stronger than the         *)
(* original strict-positivity claim).                                *)
(* ============================================================ *)

(* main statement: x ∈ [1/4,3/4] -> pg_counterex(x) >= 1/64 (the
   QleT' Set face) *)
Theorem pg_counterex_seg_ge : forall x : Q,
  QleT' (1 # 4) x -> QleT' x (3 # 4) ->
  QleT' (1 # 64) (pint_eval pg_counterex x).
Proof.
  intros x Hlo Hhi.
  assert (HP : Qle 0 (((3 # 4) - x) * (x - (1 # 4)))).
  { apply (QleT'_to_Qle 0 (((3 # 4) - x) * (x - (1 # 4)))). apply pg_mult0.
    - apply (QleT'_to_Qle 0 ((3 # 4) - x)). apply pg_qle_minus_r.
      apply QleT'_to_Qle. exact Hhi.
    - apply (QleT'_to_Qle 0 (x - (1 # 4))). apply pg_qle_minus_r.
      apply QleT'_to_Qle. exact Hlo. }
  assert (HE : pint_eval pg_counterex x == (1 # 64) + ((3 # 4) - x) * (x - (1 # 4))).
  { apply qeqT_imp_qeq. apply pg_counterex_eval_eq. }
  apply Qle_to_QleT'.
  rewrite HE.
  apply (Qle_trans (1 # 64) ((1 # 64) + 0) ((1 # 64) + ((3 # 4) - x) * (x - (1 # 4)))).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply (Qplus_le_compat (1 # 64) (1 # 64) 0
                           (((3 # 4) - x) * (x - (1 # 4)))).
    + apply Qle_refl.
    + exact HP.
Qed.

(* statement in the shape of the original claim: x ∈ [1/4,3/4] ->
   pg_counterex(x) > 0 (the QltT Set face) *)
Theorem pg_counterex_seg_pos : forall x : Q,
  QleT' (1 # 4) x -> QleT' x (3 # 4) ->
  QltT 0 (pint_eval pg_counterex x).
Proof.
  intros x Hlo Hhi.
  assert (HE : pint_eval pg_counterex x == (1 # 64) + ((3 # 4) - x) * (x - (1 # 4))).
  { apply qeqT_imp_qeq. apply pg_counterex_eval_eq. }
  apply Qlt_to_QltT.
  rewrite HE.
  apply (Qplus_lt_le_compat 0 (1 # 64) 0 (((3 # 4) - x) * (x - (1 # 4)))).
  - apply (QltT_to_Qlt 0 (1 # 64)). apply pg_lt_1_64.
  - apply (QleT'_to_Qle 0 (((3 # 4) - x) * (x - (1 # 4)))). apply pg_mult0.
    + apply (QleT'_to_Qle 0 ((3 # 4) - x)). apply pg_qle_minus_r.
      apply QleT'_to_Qle. exact Hhi.
    + apply (QleT'_to_Qle 0 (x - (1 # 4))). apply pg_qle_minus_r.
      apply QleT'_to_Qle. exact Hlo.
Qed.

(* ============================================================ *)
(* Section 4. Second leg: negative integral (closed numeric          *)
(* computation: ∫ = −1/192 < 0).                                     *)
(* ============================================================ *)

Theorem pg_counterex_int_neg : QltT (pint_integral pg_counterex) 0.
Proof.
  unfold pg_counterex, pint_integral. vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* Section 5. Negative-witness packaging (a Set-face Type product:   *)
(* the two legs side by side certify the refutation of the original  *)
(* P1b claim).                                                       *)
(*                                                               *)
(*   The existence of [pg_P1b_counterexample] shows the original     *)
(*   claim "pointwise positive on a segment -> positive integral"    *)
(*   admits no full proof: any such machine applied to pg_counterex  *)
(*   contradicts the second leg.  P1b is thereby reclassified from   *)
(*   "missing grid machine" to "statement needs strengthening" (the  *)
(*   strengthening routes are described in the file header).         *)
(* ============================================================ *)

Definition pg_P1b_death_certificate : Set :=
  (forall x : Q, QleT' (1 # 4) x -> QleT' x (3 # 4) ->
     QltT 0 (pint_eval pg_counterex x))
  * QltT (pint_integral pg_counterex) 0.

Theorem pg_P1b_counterexample : pg_P1b_death_certificate.
Proof.
  exact (pair pg_counterex_seg_pos pg_counterex_int_neg).
Qed.

(* ============================================================ *)
(* Extraction check plus assumption audit (compile-time stdout,      *)
(* re-checked during verification).                                  *)
(* ============================================================ *)

Extraction "pintposgrid_extract.ml"
  pg_counterex pg_counterex_seg_ge pg_counterex_seg_pos
  pg_counterex_int_neg pg_P1b_counterexample.

Print Assumptions pg_counterex_seg_ge.
Print Assumptions pg_counterex_seg_pos.
Print Assumptions pg_counterex_int_neg.
Print Assumptions pg_P1b_counterexample.
