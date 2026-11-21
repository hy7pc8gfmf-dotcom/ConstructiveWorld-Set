(* ConstructiveWorld - DTPT_Entropy_b. *)
(** * DTPT_Entropy_b.

    Mission.  The multi-entropy evaluation suite over the discrete Q-domain:
      the [MultiEntropyEval] record packaging the four entropy quantities of
      DTPT_Entropy_a ([H_adj], [H_ms], [H_devsum], [H_cond]) behind the
      constructor [mkMEval], the boolean phase-side decision [phase_side] and
      low-entropy gate [gate_low_entropy], the [align_lambda] identity
      embedding, and two theorems: monotonicity of the lambda-interpolated
      mixed entropy [H_lam] in its interpolation weight, and nonnegativity
      of the deviation-sum entropy [H_devsum].
    Dependencies.  Stdlib QArith/Qabs/List/Arith/Lia/Permutation/Setoid/
      Morphisms; S01_BaseRing ([Id]/[And]/[Or]/[Not] carriers with
      [id_refl]/[id_sym]); S02_CauchyComplete ([QeqT]/[QleT']/[QltT]
      carriers with the [Qle_to_QleT']/[QleT'_to_Qle] bridges);
      DTPT_Entropy_a (entropy quantities and Q order toolbox).
    References.  Discrete Shannon entropy over rational frequency counts;
      lambda interpolation of two entropy quantities as a convex
      combination; insertion sort [P0] with its permutation theory as the
      sorting substrate.
    Constructivity.  Assumption-free, nothing left open, no classical
      logic.  Every statement is carried by Set: comparison premises are
      Set-faced [QleT'], the record and the decision functions are boolean
      data, and both theorems produce Set-faced [QleT'] conclusions.
      Definitions and constructive theorems are transparent ([Defined]).
    Build.  coqc -native-compiler no -q -Q <ConstructiveWorld_Live root> ""
      DTPT_Entropy_b.v, after S01_BaseRing, S02_CauchyComplete, and
      DTPT_Entropy_a.
 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Notation S := Datatypes.S.
From Stdlib Require Import Setoid Morphisms.

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Permutation.
Import ListNotations.
Open Scope Q_scope.

Require Import DTPT_Entropy_a.

(* ========== the multi-entropy evaluation suite ========== *)

Record MultiEntropyEval : Type := mkME {
  me_carrier : list Q;        (* the carrier being evaluated *)
  me_Hadj    : Q;             (* sequential entropy (adjacent differences) *)
  me_Hms     : Q;             (* multiset entropy (count of distinct values) *)
  me_Hsh     : Q;             (* Shannon entropy (frequency counting) *)
  me_Hcond   : Q              (* conditional entropy (context dependence) *)
}.

Definition mkMEval (l : list Q) (ctx : list Q) : MultiEntropyEval :=
  mkME l (H_adj l) (H_ms l) (H_devsum l) (H_cond l ctx).

(* ========== the operational heuristics, stated constructively ========== *)

(* phase evaluation: decide on which side of P0/Pinf the output lies *)
Definition phase_side (l : list Q) (s : nat) : nat :=
  (* 0 = closer to P0; 1 = closer to Pinf (comparing the sequential
     entropy against a threshold; the comparison result is boolean data) *)
  if Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s)) then 0 else 1.

(* a constructive rendering of zero-locus filtering: down-weight
   low-entropy phases *)
Definition gate_low_entropy (H : Q) (threshold : Q) : bool :=
  Qle_bool H threshold.

(* alignment: a lambda biased toward P0, for verifiable knowledge *)
(* the identity definition below keeps its historical name and signature;
   optimal lambda selection over the two entropies is not carried by this
   piece. *)
Definition align_lambda (lam : Q) : Q := lam.

(* ========== key theorems ========== *)

(* nonnegativity of a sum of nonnegative rationals *)
Lemma qadd_nonneg : forall a b : Q, QleT' 0 a -> QleT' 0 b -> QleT' 0 (a + b).
Proof.
  intros a b Ha Hb. apply (qadd_le 0 a 0 b).
  - exact Ha.
  - exact Hb.
Defined.

(* the mixed entropy is monotone in lambda: [H_lam] is a convex combination
   of the entropy over the sorted list and the entropy over the rotation *)
Theorem H_lam_mono : forall (l : list Q) (s : nat),
  QleT' (H_adj (Pinf l s)) (H_adj (P0 l)) ->
  forall lam1 lam2 : Q,
    QleT' lam1 lam2 -> QleT' (H_lam l s lam1) (H_lam l s lam2).
Proof.
  intros l s Hle lam1 lam2 Hlam. apply Qle_to_QleT'. unfold H_lam.
  assert (Hd : QleT' 0 (H_adj (P0 l) - H_adj (Pinf l s)))
    by exact (fst (Qle_0_sub' _ _) Hle).
  assert (E1 : lam1 * H_adj (P0 l) + (1 - lam1) * H_adj (Pinf l s)
             == H_adj (Pinf l s) + lam1 * (H_adj (P0 l) - H_adj (Pinf l s)))
    by ring.
  assert (E2 : lam2 * H_adj (P0 l) + (1 - lam2) * H_adj (Pinf l s)
             == H_adj (Pinf l s) + lam2 * (H_adj (P0 l) - H_adj (Pinf l s)))
    by ring.
  rewrite E1, E2.
  apply QleT'_to_Qle.
  apply qadd_le.
  - apply Qle_to_QleT'. apply Qle_refl.
  - apply qmul_le_r.
    + exact Hlam.
    + exact Hd.
Defined.

(* nonnegativity of the deviation-sum entropy (discrete Q version) *)
Theorem H_shannon_q_nonneg : forall l : list Q, QleT' 0 (H_devsum l).
Proof.
  intro l. induction l as [| x xs IH].
  - apply Qle_to_QleT'. simpl. apply Qle_refl.
  - simpl. apply qadd_nonneg.
    + exact (abs_nonneg (x - hd 0 (P0 (x :: xs)))).
    + exact IH.
Defined.
