(* ConstructiveWorld-Set — Q-carried multi-entropy family and multi-entropy evaluation suite. *)

(** * DTPT_Entropy: the multi-entropy family over Q and its evaluation suite.

    Mission.  Discrete Q-domain entropy variants: the frequency-count
      Shannon entropies [H_devsum] and [H_freq], the conditional entropy
      [H_cond], the lambda-interpolated mixed entropy [H_lam], and their
      nonnegativity/monotonicity/permutation theorem families; the
      evaluation suite ([MultiEntropyEval] with the certificate [me_cert]);
      cross-phase convolutions with numerical anchors.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith],
      [Lia], [Permutation]; and [S01_BaseRing], [S02_CauchyComplete] of
      this development.  The [xq_] toolbox is maintained in twin copies
      with [DTPT] (same names, same statements).

    References.  This development ([DTPT], the twin toolbox) and the
      ConstructiveWorld-Main baseline modules whose statement names are
      carried over verbatim; the multi-entropy family of the source
      specification with its evaluation suite.

    Constructivity.  Zero axioms, nothing admitted, no classical logic; all
      statements carried by [Set] ([IffT A B] := (A -> B) * (B -> A)); every
      proof closes with [Qed].  [H_shannon_q_perm_inv] is false ([H_devsum]
      takes a suffix minimum, which permutations change); it is replaced by
      the constructive counterexample [H_shannon_q_perm_inv_counterex].

    Build.  [coqc -native-compiler no -q -Q . "" DTPT_Entropy.v] after
      [S01_BaseRing]/[S02_CauchyComplete]; section banners index the
      content. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Notation S := Datatypes.S.
From Stdlib Require Import Setoid Morphisms.

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Permutation.
Import ListNotations.
Open Scope Q_scope.

(* ========== Set-carrier bridge twins (mirroring the [DTPT] toolbox)
   ========== *)
(* [Id]/[NatLe]/[QeqT]/[QleT']/[QltT] and their up/down bridges are supplied
   by [S01_BaseRing]/[S02_CauchyComplete]; *)
(* this section adds the eq -> Id bridge twins and the [IffT] carrier (not
   exported by [S01]; twin copies of the [DTPT] definitions). *)
(* zero Prop statement face and nothing admitted; [IffT A B] := (A -> B) *
   (B -> A) is the Set-carried if and only if. *)

Lemma eq_imp_id {A : Set} {x y : A} (H : x = y) : Id x y.
Proof. destruct H. apply id_refl. Qed.

Definition IffT (A B : Set) : Set := (A -> B) * (B -> A).
Fixpoint insert_q (x : Q) (l : list Q) : list Q :=
  match l with
  | [] => [x]
  | y :: ys => if Qle_bool x y then x :: y :: ys else y :: insert_q x ys
  end.

Fixpoint P0 (l : list Q) : list Q :=
  match l with
  | [] => []
  | x :: xs => insert_q x (P0 xs)
  end.

Definition rot (n : nat) (l : list Q) : list Q :=
  firstn n l ++ skipn n l.

Definition Pinf (l : list Q) (s : nat) : list Q :=
  rot (S s) l.

Lemma insert_q_perm_cons : forall (x : Q) (l : list Q),
  Permutation (x :: l) (insert_q x l).
Proof.
  intros x l. induction l as [| y ys IH]; simpl.
  - simpl. apply perm_skip. apply perm_nil.
  - destruct (Qle_bool x y) eqn:Hxy.
    + apply perm_skip. apply Permutation_refl.
    + etransitivity.
      * apply perm_swap.
      * apply perm_skip. exact IH.
Qed.

Theorem D5_P0_perm : forall l : list Q, Permutation l (P0 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply Permutation_refl.
  - etransitivity.
    + apply perm_skip. exact IH.
    + apply insert_q_perm_cons.
Qed.

(* Deprecation note: under the base module where [rot] satisfies the
   identity [rot = firstn ++ skipn], this statement is a direct consequence
   of that identity; the operational semantics are carried by [DTPT_ROTC],
   [DTPT_Cyc] and [DTPT_RotSpec]. *)

Theorem D5_Pinf_perm : forall (l : list Q) (s : nat), Permutation l (Pinf l s).
Proof.
  intros l s. unfold Pinf, rot.
  rewrite firstn_skipn.
  apply Permutation_refl.
Qed.

(* D5_Pmid_perm: general lam is false (firstn/skipn truncation not a permutation); covered by endpoint theorems. *)

Fixpoint dedup_aux (x : Q) (l : list Q) : list Q :=
  match l with
  | [] => []
  | y :: ys => if Qeq_bool x y then dedup_aux x ys else y :: dedup_aux x ys
  end.

Fixpoint dedup (l : list Q) : list Q :=
  match l with
  | [] => []
  | x :: xs => x :: dedup_aux x (dedup xs)
  end.

Definition H_ms (l : list Q) : Q := (Z.of_nat (length (dedup l)) # 1)%Q.

Fixpoint sum_adjdiff (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => 0
               | y :: _ => Qabs (y - x) + sum_adjdiff xs
               end
  end.

Definition H_adj (l : list Q) : Q := sum_adjdiff l.

(* ========== Q toolbox ([Lia] does not support [Q]; everything is decided
   by Z reflection) ========== *)

Lemma Qle_bool_false_le : forall x y : Q, Qle_bool x y = false -> QleT' (y) (x).
Proof.
  intros x y H. apply Qle_to_QleT'. unfold Qle_bool in H. unfold Qle.
  destruct (Z.leb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E.
  - discriminate.
  - apply Z.leb_gt in E. lia.
Qed.

Lemma Qle_dec' : forall x y : Q, Or (QleT' x y) (QleT' y x).
Proof.
  intros x y. destruct (Qle_bool x y) eqn:E.
  - left. apply Qle_to_QleT'. apply Qle_bool_iff in E. exact E.
  - right. apply Qle_bool_false_le. exact E.
Qed.

Lemma qadd_le : forall a b c d : Q, a <= b -> c <= d -> QleT' (a + c) (b + d).
Proof.
  intros [an ad] [bn bd] [cn cd] [dn dd] H H0.
  apply Qle_to_QleT'.
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos dd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos dd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  assert (H2 : ((cn * Zpos dd) * (Zpos ad * Zpos bd)
                <= (dn * Zpos cd) * (Zpos ad * Zpos bd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H0]).
  lia.
Qed.

Lemma qopp_le : forall a b : Q, a <= b -> QleT' (- b) (- a).
Proof.
  intros [an ad] [bn bd] H.
  apply Qle_to_QleT'.
  simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

Lemma qmul_le_r : forall n m p : Q, n <= m -> 0 <= p -> QleT' (n * p) (m * p).
Proof.
  intros [nn nd] [mn md] [pn pd] H H0.
  apply Qle_to_QleT'.
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((nn * Zpos md) * (pn * Zpos pd)
                <= (mn * Zpos nd) * (pn * Zpos pd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Qed.

Lemma Qle_0_sub' : forall x y : Q, IffT (QleT' x y) (QleT' 0 (y - x)).
Proof.
  intros [nx dx] [ny dy]; simpl; split; intros H.
  - apply Qle_to_QleT'.
    pose proof (QleT'_to_Qle _ _ H) as Hq.
    unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl; lia.
  - apply Qle_to_QleT'.
    pose proof (QleT'_to_Qle _ _ H) as Hq.
    unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl; lia.
Qed.

Lemma abs_eq : forall a : Q, 0 <= a -> QeqT (Qabs a) (a).
Proof.
  intros [n d] H. apply qeq_imp_qeqT. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - reflexivity.
  - exfalso. lia.
Qed.

Lemma abs_neg : forall a : Q, a <= 0 -> QeqT (Qabs a) (- a).
Proof.
  intros [n d] H. apply qeq_imp_qeqT. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - exfalso. lia.
  - reflexivity.
Qed.

Lemma abs_nonneg : forall a : Q, QleT' (0) (Qabs a).
Proof.
  intros [n d]. apply Qle_to_QleT'. unfold Qle. destruct n; simpl; lia.
Qed.

Lemma Qeqb_true_of : forall x y : Q, x == y -> Id (Qeq_bool x y) (true).
Proof.
  intros x y H. apply eq_imp_id. unfold Qeq in H. unfold Qeq_bool.
  destruct (Z.eqb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E; [reflexivity|].
  exfalso. apply Z.eqb_neq in E. lia.
Qed.

Lemma Qeqb_sym : forall x y : Q, Id (Qeq_bool x y) (Qeq_bool y x).
Proof.
  intros x y. apply eq_imp_id. destruct (Qeq_bool x y) eqn:E1, (Qeq_bool y x) eqn:E2; try reflexivity.
  - exfalso. apply Qeq_bool_eq in E1.
    assert (E1' : y == x) by (apply Qeq_sym; exact E1).
    assert (E1b : Id (Qeq_bool y x) true) by (apply Qeqb_true_of; exact E1').
    assert (E1c : Qeq_bool y x = true) by (destruct (id_sym E1b); reflexivity).
    congruence.
  - exfalso. apply Qeq_bool_eq in E2.
    assert (E2' : x == y) by (apply Qeq_sym; exact E2).
    assert (E2b : Id (Qeq_bool x y) true) by (apply Qeqb_true_of; exact E2').
    assert (E2c : Qeq_bool x y = true) by (destruct (id_sym E2b); reflexivity).
    congruence.
Qed.

Lemma Qeqb_trans : forall a b c : Q,
  Qeq_bool a b = true -> Qeq_bool b c = true -> Id (Qeq_bool a c) (true).
Proof.
  intros a b c H1 H2. apply Qeqb_true_of.
  apply Qeq_bool_eq in H1. apply Qeq_bool_eq in H2.
  transitivity b; assumption.
Qed.

(* ========== infrastructure for the [H_ms] permutation invariance lemmas
   ([Qeq] membership and the dedup characterization) ========== *)

Definition Qmem (a : Q) (l : list Q) : Set :=
  Id (existsb (fun y => Qeq_bool a y) l) true.

Lemma Qmem_cons : forall a x (l : list Q),
  IffT (Qmem a (x :: l))
       (Or (Id (Qeq_bool a x) true) (Qmem a l)).
Proof.
  intros a x l. split.
  - intro H. unfold Qmem in *. simpl in H.
    assert (Hb : (Qeq_bool a x || existsb (fun y => Qeq_bool a y) l)%bool = true)
      by (destruct (id_sym H); reflexivity).
    destruct (Qeq_bool a x) eqn:Ex.
    + left. apply eq_imp_id. reflexivity.
    + right. apply eq_imp_id. exact Hb.
  - intro H. destruct H as [E | Hl].
    + apply eq_imp_id. simpl. rewrite E. reflexivity.
    + apply eq_imp_id. simpl. destruct (id_sym Hl). apply orb_true_r.
Qed.

Lemma Qmem_refl_cons : forall x (l : list Q), Qmem x (x :: l).
Proof.
  intros x l. apply (snd (Qmem_cons x x l)). left.
  apply eq_imp_id. apply Qeq_bool_refl.
Qed.

Lemma Qmem_dedup_aux_keep : forall a x (l : list Q),
  Qmem a (dedup_aux x l) -> Qmem a l.
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H. inversion H.
  - intros H. destruct (Qeq_bool x y).
    + apply (snd (Qmem_cons _ _ _)). right. exact (IH H).
    + apply (fst (Qmem_cons _ _ _)) in H. destruct H as [H|H].
      * apply (snd (Qmem_cons _ _ _)). left. exact H.
      * apply (snd (Qmem_cons _ _ _)). right. exact (IH H).
Qed.

Lemma Qmem_dedup_aux_drop : forall a x (l : list Q),
  Qmem a l -> Qeq_bool a x = false -> Qmem a (dedup_aux x l).
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H _. inversion H.
  - intros H Hax. apply (fst (Qmem_cons _ _ _)) in H.
    destruct (Qeq_bool x y) eqn:Hxy.
    + destruct H as [H|H].
      * exfalso.
        assert (Hay : Qeq_bool a y = true) by (destruct (id_sym H); reflexivity).
        apply Qeq_bool_sym in Hay.
        assert (HxaI : Id (Qeq_bool x a) true)
          by (apply (Qeqb_trans x y a); assumption).
        assert (Hxa : Qeq_bool x a = true)
          by (destruct (id_sym HxaI); reflexivity).
        apply Qeq_bool_sym in Hxa. rewrite Hxa in Hax. discriminate.
      * exact (IH H Hax).
    + apply (snd (Qmem_cons _ _ _)). destruct H as [H|H].
      * left. exact H.
      * right. exact (IH H Hax).
Qed.

Lemma dedup_Qmem_l : forall (l : list Q) a, Qmem a (dedup l) -> Qmem a l.
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - intros H. inversion H.
  - intros H. apply (fst (Qmem_cons _ _ _)) in H. destruct H as [H|H].
    + apply (snd (Qmem_cons _ _ _)). left. exact H.
    + apply (snd (Qmem_cons _ _ _)). right. apply IH.
      exact (Qmem_dedup_aux_keep a x _ H).
Qed.

Lemma dedup_Qmem_r : forall (l : list Q) a, Qmem a l -> Qmem a (dedup l).
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - intros H. inversion H.
  - intros H. apply (snd (Qmem_cons _ _ _)).
    apply (fst (Qmem_cons _ _ _)) in H.
    destruct H as [H|H].
    + left. exact H.
    + destruct (Qeq_bool a x) eqn:Hax.
      * left. apply eq_imp_id. reflexivity.
      * right. apply Qmem_dedup_aux_drop.
        -- apply IH. exact H.
        -- exact Hax.
Qed.

Definition gate_pass (threshold H : Q) : bool :=
  if Qle_bool H threshold then true else false.

(* ============================================================
   The generalized sorting family for [H_adj]: the [C_gen] theorems.
   ============================================================ *)
(* ============================================================
   The [C_gen] family: minimality of the sorted sequence generalized from
   the identity permutation to the whole permutation class.
   Main theorem:
     [C_gen : forall (l p : list Q), Permutation l p -> H_adj (P0 l) <= H_adj p]
   Route: [H_adj (P0 l)] == lastq - hd by the telescoping identity
   ([xq_telescope]); endpoint membership is transported to p by
   [D5_P0_perm] and transitivity of Permutation; closed by
   [xq_pair_dist_le] (the span lower bound: the Qabs distance of any two
   elements is <= H_adj).
   Companions:
     [C_gen_sym_rev]  — reversal invariance: [H_adj (rev l) == H_adj l]
     [C_gen_attained] — the bound is attained at p := P0 l
     [C_gen_sorted]   — the sorted case re-derived (sanity specialization)
   Q-layer [lia] is unavailable; all inequalities go through the [xq_]
   bridges and [ring], with [Qabs]/[lastq]/[H_adj] as atoms.
   ============================================================ *)



(* ========== snoc-level helpers (for the reversal invariance) ========== *)

(* after appending one element at the end of the list, the tail element is
   that element (Leibniz form) *)


Module DTPT_Entropy.

(* ========== discrete Shannon entropy over Q (frequency counting; Shannon
   on Q-lists) ========== *)

Fixpoint count_val (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (count_val x ys) else count_val x ys
  end.

Fixpoint H_devsum (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => Qabs (x - hd 0 (P0 l)) + H_devsum xs
  end.

(* compatibility notation for the old name ([only parsing]); the semantics
   is unchanged *)
Notation H_shannon_q := H_devsum (only parsing).

Definition H_cond (l : list Q) (ctx : list Q) : Q :=
  H_devsum l - H_devsum ctx.

(* ========== lambda-interpolated mixed entropy (the entropy version of the
   P_mid interpolation) ========== *)
Definition H_lam (l : list Q) (s : nat) (lam : Q) : Q :=
  lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s).

(* ========== the multi-entropy evaluation suite (a constructive rendering
   of the operational heuristics) ========== *)

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

(* phase evaluation: decide on which side of P0/Pinf/Pmid the output lies *)
Definition phase_side (l : list Q) (s : nat) : nat :=
  (* 0 = closer to P0; 1 = closer to Pinf (comparing the sequential entropy
   against a threshold; the difference is data, not a Prop) *)
  if Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s)) then 0 else 1.

(* hallucination suppression: down-weight extreme phases (a constructive
   rendering of zero-locus filtering) *)
Definition gate_low_entropy (H : Q) (threshold : Q) : bool :=
  Qle_bool H threshold.

(* alignment: a lambda biased toward P0, for verifiable knowledge *)
(* the identity definition below keeps its historical name and signature;
   the real definition is [align_lambda_opt] at the end of the file (an
   optimal lambda chooser over the two entropies h0/h1, with the same
   semantics as the lambda optimizers of [DTPT_Rotation]). *)
Definition align_lambda (lam : Q) : Q := lam.

(* ========== key theorems ========== *)

(* the mixed entropy is monotone in lambda — continuity of the P_mid
   interpolation entropy *)
Lemma qadd_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> QleT' (0) (a + b).
Proof.
  intros [an ad] [bn bd] H H0.
  apply Qle_to_QleT'.
  simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

Theorem H_lam_mono : forall (l : list Q) (s : nat),
  H_adj (Pinf l s) <= H_adj (P0 l) ->
  forall lam1 lam2 : Q,
    (lam1 <= lam2)%Q -> QleT' (H_lam l s lam1) (H_lam l s lam2).
Proof.
  intros l s Hle lam1 lam2 Hlam. apply Qle_to_QleT'. unfold H_lam.
  change (1 - lam1) with (1 + - lam1)%Q.
  change (1 - lam2) with (1 + - lam2)%Q.
  assert (Hd : (0 <= H_adj (P0 l) + - H_adj (Pinf l s))%Q)
    by (apply QleT'_to_Qle; apply (fst (Qle_0_sub' _ _));
        exact (Qle_to_QleT' _ _ Hle)).
  assert (E1 : lam1 * H_adj (P0 l) + (1 + - lam1) * H_adj (Pinf l s)
             == H_adj (Pinf l s) + lam1 * (H_adj (P0 l) + - H_adj (Pinf l s)))
    by ring.
  assert (E2 : lam2 * H_adj (P0 l) + (1 + - lam2) * H_adj (Pinf l s)
             == H_adj (Pinf l s) + lam2 * (H_adj (P0 l) + - H_adj (Pinf l s)))
    by ring.
  rewrite E1, E2.
  apply QleT'_to_Qle.
  apply qadd_le;
    [ apply Qle_refl
    | apply QleT'_to_Qle; apply qmul_le_r; [exact Hlam | exact Hd] ].
Qed.

(* nonnegativity of the Shannon entropy (discrete Q version) *)
Theorem H_shannon_q_nonneg : forall l : list Q, QleT' (0) (H_devsum l).
Proof.
  intro l. apply Qle_to_QleT'.
  induction l as [| x xs IH]; simpl.
  - apply Qle_refl.
  - apply QleT'_to_Qle. apply qadd_nonneg.
    + apply QleT'_to_Qle. apply (abs_nonneg (x - hd 0 (P0 (x :: xs)))).
    + exact IH.
Qed.

(* [H_devsum] recursively takes a suffix minimum along the list
   (hd 0 (P0 l)), so a permutation changes the suffix structure.
   A constructive counterexample replaces the original claim below. *)
Theorem H_shannon_q_perm_inv_counterex :
  sigT (fun l : list Q => sigT (fun p : list Q =>
    And (Permutation l p) (Not (Id (H_devsum l) (H_devsum p))))).
Proof.
  apply (existT _ [3; 1; 2]). apply (existT _ [2; 1; 3]). split.
  - apply perm_trans with (l' := [1; 3; 2]).
    + apply perm_swap.
    + apply perm_trans with (l' := [1; 2; 3]).
      * apply perm_skip. apply perm_swap.
      * apply perm_swap.
  - intro Hc. vm_compute in Hc. inversion Hc.
Qed.

(* ============================================================
   Cross-phase entropy bridging theorems:
     (1) P0 minimizes the sequential entropy: [H_adj (P0 l) <= H_adj l]
         (pairing/telescoping route: a sorted list has entropy max - min,
         and any pairing has distance <= the sequential entropy)
     (2) cross-phase lower bound: [H_adj (P0 l) <= H_adj (Pinf l s)]
         (key fact: [rot = firstn ++ skipn], so [Pinf l s] = l)
     (3) lambda-interpolated mixed entropy sandwich:
         [H_adj (P0 l) <= H_lam l s lam <= H_adj (Pinf l s)],
         [0 <= lam <= 1]
     (4) vanishing of the Shannon deviation entropy at phase P0:
         [H_devsum (P0 l) == 0], and its minimality
     (5) permutation invariance of the frequency counts and cross-phase
         invariance of the spectrum (contrasting with the sequential
         entropy family)
     (6) conditional entropy: self-conditional zero, antisymmetry,
         guarded nonnegativity, and a negative example delimiting scope
   The local [xq_] lemmas of this block are auxiliary tools, depending only
   on [D5_P0_perm] / [D5_Pinf_perm] / [insert_q_perm_cons] / [qadd_le] /
   [Qle_bool_false_le].
   ============================================================ *)

(* ---------- local [xq] tools: Q order and absolute value ---------- *)

Lemma xq_Qle_bool_true : forall x y : Q, (x <= y)%Q -> Id (Qle_bool x y) (true).
Proof.
  intros [nx dx] [ny dy] H. apply eq_imp_id.
  unfold Qle in H. unfold Qle_bool; simpl. apply Z.leb_le. unfold Z.le.
  destruct (Z.compare (nx * Z.pos dy) (ny * Z.pos dx)) eqn:E.
  - discriminate.
  - discriminate.
  - exfalso. apply H. exact E.
Qed.

Lemma xq_Qle_bool_le : forall x y : Q, Qle_bool x y = true -> QleT' (x) (y).
Proof.
  intros [nx dx] [ny dy] H. apply Qle_to_QleT'.
  unfold Qle_bool; simpl. apply Z.leb_le. exact H.
Qed.

Lemma xq_Qle_antisym : forall x y : Q, (x <= y)%Q -> (y <= x)%Q -> QeqT x y.
Proof.
  intros [nx dx] [ny dy] H1 H2. apply qeq_imp_qeqT.
  unfold Qle in H1, H2; simpl in H1, H2.
  unfold Qeq; simpl. lia.
Qed.

(* [Qabs] in Rocq 9 is implemented via [Z.abs]: Qabs (n # d) = (Z.abs n # d) *)
Lemma xq_abs_id : forall x : Q, (0 <= x)%Q -> QeqT (Qabs x) (x).
Proof.
  intros [n d] Hx. apply qeq_imp_qeqT. unfold Qle in Hx; simpl in Hx.
  assert (Hn : (0 <= n)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite (Z.abs_eq n Hn). reflexivity.
Qed.

Lemma xq_abs_eq0 : forall x : Q, x == 0 -> QeqT (Qabs x) 0.
Proof.
  intros [n d] Hx. apply qeq_imp_qeqT.
  unfold Qeq in Hx; simpl in Hx.
  assert (Hn : (n = 0)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite Hn. reflexivity.
Qed.

Lemma xq_minus_self : forall x : Q, QeqT (x - x) 0.
Proof.
  intros [n d]. apply qeq_imp_qeqT.
  unfold Qminus, Qeq; simpl. lia.
Qed.

Lemma xq_abs_zero : forall x : Q, QeqT (Qabs (x - x)) 0.
Proof.
  intro x. apply xq_abs_eq0.
  apply qeqT_imp_qeq. apply xq_minus_self.
Qed.

Lemma xq_abs_eq : forall x y : Q, x == y -> QeqT (Qabs x) (Qabs y).
Proof.
  intros [n1 d1] [n2 d2] Hxy. apply qeq_imp_qeqT.
  unfold Qeq in Hxy; simpl in Hxy.
  unfold Qabs; simpl. unfold Qeq; simpl.
  pose proof (Z.abs_spec n1) as Ha1. pose proof (Z.abs_spec n2) as Ha2.
  destruct Ha1 as [[A1 B1] | [A1 B1]];
    destruct Ha2 as [[A2 B2] | [A2 B2]];
    try rewrite B1; try rewrite B2; lia.
Qed.

Lemma xq_abs_opp : forall x : Q, QeqT (Qabs (- x)) (Qabs x).
Proof.
  intros [n d]. apply qeq_imp_qeqT.
  unfold Qabs, Qopp; simpl. unfold Qeq; simpl.
  rewrite Z.abs_opp. reflexivity.
Qed.

Lemma xq_minus_opp : forall a b : Q, QeqT (b - a) (- (a - b)).
Proof.
  intros [na da] [nb db]. apply qeq_imp_qeqT.
  unfold Qminus, Qopp, Qeq; simpl.
  rewrite (Pos.mul_comm db da). ring.
Qed.

Lemma xq_abs_sub_comm : forall a b : Q, QeqT (Qabs (a - b)) (Qabs (b - a)).
Proof.
  intros a b. apply qeq_imp_qeqT.
  assert (H1 : Qabs (-(a - b)) == Qabs (a - b)) by (apply qeqT_imp_qeq; apply xq_abs_opp).
  rewrite <- H1.
  apply qeqT_imp_qeq. apply xq_abs_eq. symmetry. apply qeqT_imp_qeq. apply xq_minus_opp.
Qed.

Lemma xq_H_adj_nonneg : forall l : list Q, QleT' (0) (H_adj l).
Proof.
  intro l. apply Qle_to_QleT'. induction l as [| a rest IH].
  - apply Qle_refl.
  - destruct rest as [| b bs].
    + apply Qle_refl.
    + change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      apply QleT'_to_Qle. apply qadd_nonneg;
        [ apply QleT'_to_Qle; apply abs_nonneg | exact IH ].
Qed.

Lemma xq_le_add_abs : forall t h : Q, QleT' (h) (Qabs t + h).
Proof.
  intros t h.
  pose proof (qadd_le 0 (Qabs t) h h
    (QleT'_to_Qle _ _ (abs_nonneg t)) (Qle_refl h)) as HS.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ HS) as HS2.
  rewrite Qplus_0_l in HS2.
  exact HS2.
Qed.

(* ---------- local [xq] tools: the ascending predicate and the P0 normal
   form ---------- *)

Inductive SortedQ : list Q -> Set :=
| sortQ_nil : SortedQ []
| sortQ_cons : forall x xs,
    SortedQ xs -> Forall (fun z => (x <= z)%Q) xs -> SortedQ (x :: xs).

Lemma xq_sortQ_insert : forall (x : Q) (l : list Q),
  SortedQ l -> SortedQ (insert_q x l).
Proof.
  intros x l. revert x. induction l as [| y ys IH]; intros x HS.
  - simpl. apply sortQ_cons; [ apply sortQ_nil | apply Forall_nil ].
  - inversion HS as [| x0 xs0 HSys HFall]; subst.
    rewrite Forall_forall in HFall.
    simpl. destruct (Qle_bool x y) eqn:E.
    + apply sortQ_cons; [ exact HS | ].
      rewrite Forall_forall. intros z Hz. destruct Hz as [Heq | Hz].
      * subst. apply QleT'_to_Qle. apply xq_Qle_bool_le. exact E.
      * apply (Qle_trans x y z).
        -- apply QleT'_to_Qle. apply xq_Qle_bool_le. exact E.
        -- apply HFall. exact Hz.
    + apply sortQ_cons; [ apply IH; exact HSys | ].
      rewrite Forall_forall. intros z Hz.
      assert (Hin : In z (x :: ys)).
      { apply Permutation_in with (l := insert_q x ys).
        - apply Permutation_sym. apply insert_q_perm_cons.
        - exact Hz. }
      destruct Hin as [Heq | Hin].
      * subst. apply QleT'_to_Qle. apply Qle_bool_false_le. exact E.
      * apply HFall. exact Hin.
Qed.

Lemma xq_P0_sorted : forall l : list Q, SortedQ (P0 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply sortQ_nil.
  - apply xq_sortQ_insert. exact IH.
Qed.

(* [xq_insert_q_head_aux]: when the insertion point is >= the compared
   element, [insert_q] places the element at the head directly *)
Lemma xq_insert_q_head_aux : forall (a b : Q) (bs : list Q),
  (a <= b)%Q -> Id (insert_q a (b :: bs)) (a :: b :: bs).
Proof.
  intros a b bs H. apply eq_imp_id. simpl.
  destruct (id_sym (xq_Qle_bool_true _ _ H)). reflexivity.
Qed.

Lemma xq_sortQ_P0_id : forall l : list Q, SortedQ l -> Id (P0 l) (l).
Proof.
  intro l. induction l as [| a rest IH]; intro HS; apply eq_imp_id.
  - reflexivity.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    change (P0 (a :: rest)) with (insert_q a (P0 rest)).
    destruct (id_sym (IH HSr)). destruct rest as [| b bs].
    + reflexivity.
    + destruct (id_sym (xq_insert_q_head_aux a b bs
                   (HFa b (or_introl eq_refl)))).
      reflexivity.
Qed.

(* ---------- local [xq] tools: the [lastq] tail element and the telescoping
   equation ---------- *)

Fixpoint lastq (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => x
               | _ :: _ => lastq xs
               end
  end.

Lemma xq_lastq_In : forall m : list Q, m <> [] -> In (lastq m) m.
Proof.
  induction m as [| a rest IH]; intros Hne.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b bs].
    + simpl. left. reflexivity.
    + simpl. right. apply IH. simpl. discriminate.
Qed.

Lemma xq_hd_In_gen : forall m : list Q, m <> [] -> In (hd 0 m) m.
Proof.
  intros [| h t] H; [ exfalso; apply H; reflexivity | simpl; left; reflexivity ].
Qed.

Lemma xq_P0_cons_ne : forall (x : Q) (xs : list Q), P0 (x :: xs) <> [].
Proof.
  intros x xs. cbn [P0].
  destruct (P0 xs) as [| y ys]; cbn [insert_q].
  - discriminate.
  - destruct (Qle_bool x y); discriminate.
Qed.

Lemma xq_hd_le_lastq : forall l : list Q, SortedQ l -> QleT' (hd 0 l) (lastq l).
Proof.
  intro l. induction l as [| a rest IH]; intro HS; apply Qle_to_QleT'.
  - simpl. apply Qle_refl.
  - destruct rest as [| b bs].
    + simpl. apply Qle_refl.
    + inversion HS as [| x0 xs0 HSr HFa]; subst.
      rewrite Forall_forall in HFa.
      apply (Qle_trans a b).
      * apply HFa. left. reflexivity.
      * apply QleT'_to_Qle. apply IH. exact HSr.
Qed.

(* telescoping equation: the sum of adjacent differences of an ascending
   list equals the last element minus the first *)
Lemma xq_telescope : forall l : list Q, SortedQ l -> QeqT (H_adj l) (lastq l - hd 0 l).
Proof.
  induction l as [| a rest IH]; intro HS.
  - apply qeq_imp_qeqT. reflexivity.
  - destruct rest as [| b bs].
    + apply qeq_imp_qeqT.
      change (H_adj [a]) with 0%Q.
      change (lastq [a] - hd 0 [a]) with (a - a)%Q.
      symmetry. apply qeqT_imp_qeq. apply xq_minus_self.
    + apply qeq_imp_qeqT.
      inversion HS as [| x0 xs0 HSr HFa]; subst.
      rewrite Forall_forall in HFa.
      change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      assert (Hab : (0 <= b - a)%Q).
      { apply QleT'_to_Qle. apply (fst (Qle_0_sub' a b)).
        apply Qle_to_QleT'. apply HFa. left. reflexivity. }
      rewrite (qeqT_imp_qeq _ _ (xq_abs_id _ Hab)).
      rewrite (qeqT_imp_qeq _ _ (IH HSr)).
      change (lastq (a :: b :: bs)) with (lastq (b :: bs)).
      change (hd 0 (a :: b :: bs)) with a.
      change (hd 0 (b :: bs)) with b.
      ring.
Qed.

(* pairing distance bound: the Qabs distance of any two elements of the list
   is at most the sequential entropy *)
Lemma xq_pair_dist_le : forall (l : list Q) (x y : Q),
  In x l -> In y l -> QleT' (Qabs (x - y)) (H_adj l).
Proof.
  intro l. induction l as [| a rest IH]; intros x y Hx Hy; apply Qle_to_QleT'.
  - exfalso. exact Hx.
  - destruct rest as [| b bs].
    + destruct Hx as [Hx | []]; destruct Hy as [Hy | []]; subst.
      rewrite (qeqT_imp_qeq _ _ (xq_abs_zero _)). apply Qle_refl.
    + change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
      * rewrite (qeqT_imp_qeq _ _ (xq_abs_zero _)).
        apply QleT'_to_Qle. apply qadd_nonneg;
          [ apply QleT'_to_Qle; apply abs_nonneg
          | apply QleT'_to_Qle; apply xq_H_adj_nonneg ].
      * assert (Hr1 : a - y == (a - b) + (b - y)) by ring.
        rewrite Hr1.
        apply (Qle_trans _ (Qabs (a - b) + Qabs (b - y))).
        -- apply Qabs_triangle.
        -- rewrite (qeqT_imp_qeq _ _ (xq_abs_sub_comm a b)).
           apply QleT'_to_Qle. apply qadd_le; [ apply Qle_refl
                          | apply QleT'_to_Qle; apply IH;
                            [ left; reflexivity | exact Hy ] ].
      * assert (Hr2 : x - a == (x - b) + (b - a)) by ring.
        rewrite Hr2.
        apply (Qle_trans _ (Qabs (x - b) + Qabs (b - a))).
        -- apply Qabs_triangle.
        -- rewrite (Qplus_comm (Qabs (x - b)) (Qabs (b - a))).
           apply QleT'_to_Qle. apply qadd_le; [ apply Qle_refl
                          | apply QleT'_to_Qle; apply IH;
                            [ exact Hx | left; reflexivity ] ].
      * apply (Qle_trans _ (H_adj (b :: bs))).
        -- apply QleT'_to_Qle. apply IH; assumption.
        -- apply QleT'_to_Qle. apply xq_le_add_abs.
Qed.

(* ========== main theorem 1: P0 minimizes the sequential entropy
   ========== *)

Theorem H_adj_P0_min : forall l : list Q, QleT' (H_adj (P0 l)) (H_adj l).
Proof.
  intro l. apply Qle_to_QleT'. destruct l as [| a rest].
  - apply Qle_refl.
  - assert (HP : H_adj (P0 (a :: rest))
                 == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest)))
      by (apply qeqT_imp_qeq; apply xq_telescope; apply xq_P0_sorted).
    assert (HP2 : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest))).
    { rewrite (qeqT_imp_qeq _ _ (xq_abs_sub_comm (hd 0 (P0 (a :: rest))) (lastq (P0 (a :: rest))))).
      apply qeqT_imp_qeq. apply xq_abs_id.
      apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
      apply xq_hd_le_lastq. apply xq_P0_sorted. }
    rewrite HP. rewrite <- HP2.
    assert (Hm1 : In (hd 0 (P0 (a :: rest))) (a :: rest)).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - apply Permutation_sym. apply D5_P0_perm.
      - apply xq_hd_In_gen. apply xq_P0_cons_ne. }
    assert (Hm2 : In (lastq (P0 (a :: rest))) (a :: rest)).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - apply Permutation_sym. apply D5_P0_perm.
      - apply xq_lastq_In. apply xq_P0_cons_ne. }
    apply QleT'_to_Qle. apply xq_pair_dist_le; assumption.
Qed.

(* ========== main theorem 2: cross-phase lower bound (Pinf side)
   ========== *)

Corollary Pinf_eq_l : forall (l : list Q) (s : nat), Id (Pinf l s) (l).
Proof.
  intros l. induction l as [| a rest IH]; intros s; apply eq_imp_id.
  - reflexivity.
  - unfold Pinf, rot. destruct s as [| s'].
    + reflexivity.
    + change (firstn (S (S s')) (a :: rest) ++ skipn (S (S s')) (a :: rest) = a :: rest)
        with (a :: (firstn (S s') rest ++ skipn (S s') rest) = a :: rest).
      f_equal. change (firstn (S s') rest ++ skipn (S s') rest) with (Pinf rest s').
      destruct (id_sym (IH s')). reflexivity.
Qed.

Theorem H_adj_cross_phase_lb : forall (l : list Q) (s : nat), QleT' (H_adj (P0 l)) (H_adj (Pinf l s)).
Proof.
  intros l s. apply Qle_to_QleT'.
  destruct (id_sym (Pinf_eq_l l s)).
  apply QleT'_to_Qle. apply H_adj_P0_min.
Qed.

(* ========== main theorem 3: cross-phase sandwich for the
   lambda-interpolated mixed entropy ========== *)

Lemma xq_mul_nonneg : forall a b : Q, (0 <= a)%Q -> (0 <= b)%Q -> QleT' (0) (a * b).
Proof.
  intros [an ad] [bn bd] Ha Hb. apply Qle_to_QleT'. unfold Qle in Ha, Hb; simpl in Ha, Hb.
  unfold Qle, Qmult; simpl. lia.
Qed.

Theorem H_lam_cross_phase_bounds : forall (l : list Q) (s : nat) (lam : Q),
  (0 <= lam)%Q -> (lam <= 1)%Q ->
  And (QleT' (H_adj (P0 l)) (H_lam l s lam))
      (QleT' (H_lam l s lam) (H_adj (Pinf l s))).
Proof.
  intros l s lam Hlam0 Hlam1.
  assert (Hle : (H_adj (P0 l) <= H_adj (Pinf l s))%Q)
    by (apply QleT'_to_Qle; apply H_adj_cross_phase_lb).
  unfold H_lam.
  assert (Hlo : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - H_adj (P0 l))%Q).
  { assert (Er1 : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                  - H_adj (P0 l)
                  == (1 - lam) * (H_adj (Pinf l s) - H_adj (P0 l))) by ring.
    rewrite Er1.
    apply QleT'_to_Qle. apply xq_mul_nonneg.
    - apply QleT'_to_Qle. apply (fst (Qle_0_sub' lam 1)).
      apply Qle_to_QleT'. exact Hlam1.
    - apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
      apply Qle_to_QleT'. exact Hle. }
  assert (Hup : (0 <= H_adj (Pinf l s)
                 - (lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)))%Q).
  { assert (Er2 : H_adj (Pinf l s)
                  - (lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s))
                  == lam * (H_adj (Pinf l s) - H_adj (P0 l))) by ring.
    rewrite Er2.
    apply QleT'_to_Qle; apply xq_mul_nonneg;
      [ exact Hlam0
      | apply QleT'_to_Qle; apply (fst (Qle_0_sub' _ _));
        apply Qle_to_QleT'; exact Hle ]. }
  split.
  - apply (snd (Qle_0_sub' _ _)). apply Qle_to_QleT'. exact Hlo.
  - apply (snd (Qle_0_sub' _ _)). apply Qle_to_QleT'. exact Hup.
Qed.

(* ========== main theorem 4: vanishing of the Shannon deviation entropy at
   phase P0, and minimality ========== *)

Lemma xq_H_shannon_sortQ : forall l : list Q, SortedQ l -> QeqT (H_devsum l) (0).
Proof.
  intro l. induction l as [| a rest IH]; intro HS; apply qeq_imp_qeqT.
  - reflexivity.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    cbn [H_devsum].
    destruct (id_sym (xq_sortQ_P0_id (a :: rest) HS)).
    change (hd 0 (a :: rest)) with a.
    rewrite (qeqT_imp_qeq _ _ (IH HSr)).
    rewrite (qeqT_imp_qeq _ _ (xq_abs_zero _)). ring.
Qed.

Theorem H_shannon_q_P0_zero : forall l : list Q, QeqT (H_devsum (P0 l)) 0.
Proof.
  intro l. apply xq_H_shannon_sortQ. apply xq_P0_sorted.
Qed.

Theorem H_shannon_q_P0_min : forall l : list Q,
  QleT' (H_devsum (P0 l)) (H_devsum l).
Proof.
  intro l. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (H_shannon_q_P0_zero l)).
  apply QleT'_to_Qle. apply H_shannon_q_nonneg.
Qed.

(* ========== main theorem 5: permutation/cross-phase invariance of the
   frequency counts (in contrast with the sequential entropy)
   ========== *)

Theorem count_val_perm : forall (x : Q) (l p : list Q),
  Permutation l p -> Id (count_val x l) (count_val x p).
Proof.
  intros x l p H.
  apply eq_imp_id.
  induction H; simpl.
  - reflexivity.
  - match goal with
    | [ I : count_val x _ = count_val x _ |- _ ] => rewrite I
    end.
    reflexivity.
  - match goal with
    | [ |- context[Qeq_bool x ?u] ] => destruct (Qeq_bool x u) eqn:E1
    end;
    match goal with
    | [ |- context[Qeq_bool x ?u] ] => destruct (Qeq_bool x u) eqn:E2
    end;
    simpl; try match goal with
                  | [ I : count_val x _ = count_val x _ |- _ ] => rewrite I
                  end; reflexivity.
  - match goal with
    | [ I1 : count_val x ?u = count_val x ?v,
        I2 : count_val x ?v = count_val x ?w |- _ ] =>
        etransitivity; [ exact I1 | exact I2 ]
    end.
Qed.

Theorem count_val_phase_spectrum : forall (x : Q) (l : list Q) (s : nat),
  And (Id (count_val x (P0 l)) (count_val x l))
      (Id (count_val x (Pinf l s)) (count_val x l)).
Proof.
  intros x l s. split.
  - apply eq_imp_id.
    rewrite <- (count_val_perm x l (P0 l) (D5_P0_perm l)). reflexivity.
  - apply eq_imp_id.
    rewrite <- (count_val_perm x l (Pinf l s) (D5_Pinf_perm l s)). reflexivity.
Qed.

(* ========== main theorem 6: the conditional entropy quartet (guarded
   nonnegativity plus counterexamples delimiting scope) ========== *)

Theorem H_cond_self : forall l : list Q, QeqT (H_cond l l) 0.
Proof.
  intro l. apply qeq_imp_qeqT. unfold H_cond. ring.
Qed.

Theorem H_cond_antisym : forall (l ctx : list Q),
  QeqT (H_cond l ctx) (- H_cond ctx l).
Proof.
  intros l ctx. apply qeq_imp_qeqT. unfold H_cond. ring.
Qed.

Theorem H_cond_nonneg_guarded : forall (l ctx : list Q),
  (H_devsum ctx <= H_devsum l)%Q -> QleT' (0) (H_cond l ctx).
Proof.
  intros l ctx H. apply Qle_to_QleT'. unfold H_cond.
  apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
  apply Qle_to_QleT'. exact H.
Qed.

(* unconditional nonnegativity is false: conditioning an empty list on a
   high-entropy context gives H_cond = -2 < 0 *)
Theorem H_cond_neg_counterex :
  sigT (fun l : list Q => sigT (fun ctx : list Q => QltT (H_cond l ctx) 0)).
Proof.
  apply (existT _ []). apply (existT _ [5; 3]). apply Qlt_to_QltT.
  unfold H_cond. vm_compute. reflexivity.
Qed.

(* ============================================================
   Counting bounds, coherence of the evaluation record, endpoint degeneracy
   of [H_lam], and gating behavior:
     (1) counting upper bounds: [count_val <= length] (nat and Q forms),
         plus the [H_devsum] counting bound (each term |x - suffix minimum|
         is bounded by the pairing bound <= H_adj, so the sum is bounded by
         the length factor times H_adj, the factor reduced to S form)
     (2) coherence of [MultiEntropyEval]: the round trip of the [mkMEval]
         projections (eta form), and degeneracy [H_ms == 1] implies
         [H_devsum == 0] (dedup count -> all values equal -> sorted ->
         vanishing, a four-step bridge), with a constructive counterexample
         for the converse
     (3) endpoint degeneracy of [H_lam]: lam = 1 / lam = 0 recover the P0 /
         Pinf phase entropies
     (4) behavior of [gate_low_entropy] / [phase_side] (Qle_bool bridges in
         both directions)
   Reuses the toolbox proved in this file ([qmul_le_r], [Qle_bool_iff],
   [Qle_bool_false_le], [dedup_Qmem_r] and the [xq_] tools); no new
   premises.
   ============================================================ *)

(* ---------- local [xq] tools: the Q bridge for the length factor
   ---------- *)

Lemma xq_Zlen_nonneg : forall n : nat, QleT' (0) ((Z.of_nat n # 1)%Q).
Proof.
  intro n. apply Qle_to_QleT'. unfold Qle; simpl. lia.
Qed.

Lemma xq_Zlen_S : forall n : nat,
  QeqT (Z.of_nat (S n) # 1) (1 + (Z.of_nat n # 1))%Q.
Proof.
  intro n. apply qeq_imp_qeqT.
  assert (Hz : (Z.of_nat (S n) = 1 + Z.of_nat n)%Z) by lia.
  rewrite Hz. unfold Qeq, Qplus. cbn [Qnum Qden]. lia.
Qed.

Lemma xq_Zlen_inj1 : forall n : nat, ((Z.of_nat n # 1) == 1)%Q -> Id (n) (1%nat).
Proof.
  intros n H. apply eq_imp_id. unfold Qeq in H; simpl in H. lia.
Qed.

Lemma xq_Qeq_le : forall x y : Q, x == y -> QleT' (x) (y).
Proof.
  intros [nx dx] [ny dy] Hxy. apply Qle_to_QleT'. unfold Qeq in Hxy; simpl in Hxy.
  unfold Qle; simpl. lia.
Qed.

(* ---------- main theorem 1a: the length upper bound of the frequency
   counts (nat form) ---------- *)

Lemma count_val_le_length : forall (x : Q) (l : list Q), NatLe (count_val x l) ((length l)%nat).
Proof.
  intros x l. apply NatLe_lift. induction l as [| y ys IH]; simpl.
  - lia.
  - destruct (Qeq_bool x y); lia.
Qed.

(* main theorem 1b: the same upper bound in Q form (same length-factor
   convention) *)
Lemma count_val_Zle_length : forall (x : Q) (l : list Q),
  QleT' (Z.of_nat (count_val x l) # 1) (Z.of_nat (length l) # 1).
Proof.
  intros x l. apply Qle_to_QleT'.
  pose proof (count_val_le_length x l) as Hn.
  pose proof (NatLe_drop _ _ Hn) as Hn2.
  unfold Qle; simpl. lia.
Qed.

(* ---------- main theorem 1c: the [H_devsum] counting bound ----------
   Each term of [H_devsum] is |x - suffix minimum|: the pairing bound gives
   termwise <= H_adj, hence the sum <= length factor * H_adj.  Nontrivial
   points: suffix monotonicity (prepending only increases), reduction of
   the factor to S form, and unifying the order of the factors. ---------- *)

Lemma xq_H_adj_suffix_le : forall (a : Q) (l : list Q), QleT' (H_adj l) (H_adj (a :: l)).
Proof.
  intros a l. apply Qle_to_QleT'. destruct l as [| b bs].
  - cbn [H_adj sum_adjdiff]. apply Qle_refl.
  - change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
    apply QleT'_to_Qle. apply xq_le_add_abs.
Qed.

Lemma xq_head_term_le : forall (x : Q) (xs : list Q), QleT' (Qabs (x - hd 0 (P0 (x :: xs)))) (H_adj (x :: xs)).
Proof.
  intros x xs. apply Qle_to_QleT'. apply QleT'_to_Qle. apply xq_pair_dist_le.
  - left. reflexivity.
  - apply Permutation_in with (l := P0 (x :: xs)).
    + apply Permutation_sym. apply D5_P0_perm.
    + apply xq_hd_In_gen. apply xq_P0_cons_ne.
Qed.

Theorem H_shannon_q_count_ub : forall l : list Q, QleT' (H_devsum l) (H_adj l * (Z.of_nat (length l) # 1)).
Proof.
  intro l. induction l as [| x xs IH]; apply Qle_to_QleT'.
  - cbn [H_devsum]. apply QleT'_to_Qle. apply xq_mul_nonneg.
    + apply QleT'_to_Qle. apply xq_H_adj_nonneg.
    + apply QleT'_to_Qle. apply xq_Zlen_nonneg.
  - cbn [H_devsum].
    assert (Hs : (H_devsum xs
                  <= H_adj (x :: xs) * (Z.of_nat (length xs) # 1))%Q).
    { apply (Qle_trans _ (H_adj xs * (Z.of_nat (length xs) # 1))).
      - apply QleT'_to_Qle. exact IH.
      - apply QleT'_to_Qle. apply qmul_le_r.
        + apply QleT'_to_Qle. apply xq_H_adj_suffix_le.
        + apply QleT'_to_Qle. apply xq_Zlen_nonneg. }
    assert (Hh : (Qabs (x - hd 0 (P0 (x :: xs))) <= H_adj (x :: xs))%Q)
      by (apply QleT'_to_Qle; apply xq_head_term_le).
    assert (Hlen : ((Z.of_nat (length (x :: xs)) # 1)
                    == 1 + (Z.of_nat (length xs) # 1))%Q)
      by (cbn [length]; apply qeqT_imp_qeq; apply xq_Zlen_S).
    apply (Qle_trans _ (H_adj (x :: xs)
                        + H_adj (x :: xs) * (Z.of_nat (length xs) # 1))).
    + apply QleT'_to_Qle. apply qadd_le; [exact Hh | exact Hs].
    + rewrite Hlen.
      assert (Heq : H_adj (x :: xs) * (1 + (Z.of_nat (length xs) # 1))
                    == H_adj (x :: xs)
                       + H_adj (x :: xs) * (Z.of_nat (length xs) # 1))
        by ring.
      rewrite Heq. apply Qle_refl.
Qed.

(* ---------- coherence 2a: vanishing of [H_devsum] on an all-equal list
   ---------- *)

Lemma xq_insert_const_head : forall (a y : Q) (ys : list Q),
  y == a -> Id (insert_q a (y :: ys)) (a :: y :: ys).
Proof.
  intros a y ys Hya. apply eq_imp_id. cbn [insert_q].
  destruct (id_sym (xq_Qle_bool_true a y
              (QleT'_to_Qle _ _ (xq_Qeq_le a y (Qeq_sym y a Hya))))).
  reflexivity.
Qed.

Lemma xq_P0_const_id : forall (a : Q) (l : list Q),
  Forall (fun z => z == a) l -> Id (P0 l) (l).
Proof.
  intros a l. induction l as [| x xs IH]; intro Hfa; apply eq_imp_id.
  - reflexivity.
  - inversion Hfa as [| z zs Hzx Hfxs]; subst.
    cbn [P0]. destruct (id_sym (IH Hfxs)).
    destruct xs as [| y ys].
    + cbn [insert_q]. reflexivity.
    + destruct (id_sym (xq_insert_const_head x y ys
                   (Qeq_trans y a x (Forall_inv Hfxs) (Qeq_sym x a Hzx)))).
      reflexivity.
Qed.

Theorem H_shannon_q_const_zero : forall (a : Q) (l : list Q),
  Forall (fun z => z == a) l -> QeqT (H_devsum l) (0).
Proof.
  intros a l. revert a. induction l as [| x xs IH]; intros a Hfa;
    apply qeq_imp_qeqT.
  - reflexivity.
  - assert (Hfa' : Forall (fun z => z == a) (x :: xs)) by exact Hfa.
    inversion Hfa as [| z zs Hzx Hfxs]; subst.
    cbn [H_devsum].
    destruct (id_sym (xq_P0_const_id a (x :: xs) Hfa')).
    cbn [hd]. rewrite (qeqT_imp_qeq _ _ (xq_abs_zero _)).
    rewrite (qeqT_imp_qeq _ _ (IH a Hfxs)). ring.
Qed.

(* ---------- coherence 2b: multiset-entropy degeneracy implies vanishing
   of the Shannon deviation entropy ---------- *)

Lemma xq_len1_el : forall m : list Q,
  length m = 1%nat -> sigT (fun a : Q => Id m (a :: nil)).
Proof.
  intros [| b bs] H; cbn [length] in H.
  - discriminate H.
  - destruct bs as [| c cs].
    + apply (existT _ b). apply eq_imp_id. reflexivity.
    + discriminate H.
Qed.

Lemma xq_In_Qmem : forall (z : Q) (l : list Q), In z l -> Qmem z l.
Proof.
  intros z l. induction l as [| y ys IH]; intro Hind.
  - destruct Hind.
  - simpl in Hind. destruct (Qeq_bool z y) eqn:E.
    + apply (snd (Qmem_cons _ _ _)). left. apply eq_imp_id. exact E.
    + apply (snd (Qmem_cons _ _ _)). right. apply IH.
      destruct Hind as [Heq | Hind].
      * rewrite <- Heq in E. rewrite Qeq_bool_refl in E. discriminate E.
      * exact Hind.
Qed.

Lemma xq_dedup1_all_eq : forall (l : list Q) (a : Q),
  dedup l = a :: nil -> forall z : Q, In z l -> QeqT z a.
Proof.
  intros l a Hd z Hz.
  assert (Hm : Qmem z (dedup l)).
  { apply dedup_Qmem_r. apply xq_In_Qmem. exact Hz. }
  rewrite Hd in Hm.
  destruct (fst (Qmem_cons z a nil) Hm) as [Hm1 | Hm1].
  - assert (E : Qeq_bool z a = true)
      by (destruct (id_sym Hm1); reflexivity).
    apply qeq_imp_qeqT. apply Qeq_bool_eq. exact E.
  - simpl in Hm1. inversion Hm1.
Qed.

Theorem H_ms1_Hshannon0 : forall l : list Q,
  (H_ms l == 1)%Q -> QeqT (H_devsum l) 0.
Proof.
  intro l. unfold H_ms. intro H.
  assert (HI : Id (length (dedup l)) 1%nat)
    by (apply (xq_Zlen_inj1 (length (dedup l))); exact H).
  assert (Hlen : length (dedup l) = 1%nat)
    by (destruct (id_sym HI); reflexivity).
  destruct (xq_len1_el (dedup l) Hlen) as [b Hb].
  apply (H_shannon_q_const_zero b l).
  assert (Hbe : dedup l = [b]) by (destruct (id_sym Hb); reflexivity).
  apply Forall_forall. intros z Hz. apply qeqT_imp_qeq.
  apply (xq_dedup1_all_eq l b Hbe z Hz).
Qed.

(* the converse is false: the ascending list [1;2] has zero Shannon
   deviation but multiset entropy = 2 <> 1 *)
Theorem Hshannon0_not_Hms1_counterex :
  And (QeqT (H_devsum [1; 2]) 0) (Not (QeqT (H_ms [1; 2]) 1)).
Proof.
  split.
  - apply qeq_imp_qeqT. vm_compute. reflexivity.
  - intro Hc. apply (False_rect Empty_set). apply qeqT_imp_qeq in Hc.
    unfold H_ms in Hc. vm_compute in Hc. discriminate Hc.
Qed.

(* ---------- coherence 2c: the projections of [mkMEval] round-trip (eta
   form) ---------- *)

Theorem mkMEval_eta : forall (l ctx : list Q),
  And (Id (me_carrier (mkMEval l ctx)) l)
  (And (QeqT (me_Hadj (mkMEval l ctx)) (H_adj l))
  (And (QeqT (me_Hms (mkMEval l ctx)) (H_ms l))
  (And (QeqT (me_Hsh (mkMEval l ctx)) (H_devsum l))
       (QeqT (me_Hcond (mkMEval l ctx)) (H_cond l ctx))))).
Proof.
  intros l ctx. repeat split.
  - apply qeq_imp_qeqT. unfold Qeq. simpl. reflexivity.
  - apply qeq_imp_qeqT. unfold Qeq. simpl. reflexivity.
  - apply qeq_imp_qeqT. unfold Qeq. simpl. reflexivity.
  - apply qeq_imp_qeqT. unfold Qeq. simpl. reflexivity.
Qed.

Theorem mkMEval_Hms1_Hsh0 : forall (l ctx : list Q),
  (me_Hms (mkMEval l ctx) == 1)%Q -> QeqT (me_Hsh (mkMEval l ctx)) (0).
Proof.
  intros l ctx H. apply qeq_imp_qeqT. unfold mkMEval in H. simpl in H.
  unfold mkMEval. simpl. exact (qeqT_imp_qeq _ _ (H_ms1_Hshannon0 l H)).
Qed.

(* ---------- endpoint 3: degeneracy of [H_lam] at lambda = 1 /
   lambda = 0 ---------- *)

Theorem H_lam_lam1 : forall (l : list Q) (s : nat),
  QeqT (H_lam l s 1) (H_adj (P0 l)).
Proof.
  intros l s. apply qeq_imp_qeqT. unfold H_lam.
  replace (1 - 1)%Q with 0%Q by reflexivity.
  ring.
Qed.

Theorem H_lam_lam0 : forall (l : list Q) (s : nat),
  QeqT (H_lam l s 0) (H_adj (Pinf l s)).
Proof.
  intros l s. apply qeq_imp_qeqT. unfold H_lam.
  replace (1 - 0)%Q with 1%Q by reflexivity.
  ring.
Qed.

(* ---------- gating 4: behavior of [gate_low_entropy] / [phase_side]
   ---------- *)

Theorem gate_low_entropy_spec : forall H threshold : Q,
  IffT (Id (gate_low_entropy H threshold) true) (QleT' H threshold).
Proof.
  intros H threshold. split.
  - intro E. apply Qle_to_QleT'.
    assert (Eb : Qle_bool H threshold = true)
      by (unfold gate_low_entropy in E; destruct (id_sym E); reflexivity).
    apply (proj1 (Qle_bool_iff H threshold)). exact Eb.
  - intro Hle. apply eq_imp_id. unfold gate_low_entropy.
    apply (proj2 (Qle_bool_iff H threshold)).
    apply (QleT'_to_Qle _ _ Hle).
Qed.

Theorem gate_low_entropy_false_le : forall H threshold : Q,
  gate_low_entropy H threshold = false -> QleT' threshold H.
Proof.
  intros H threshold Hfalse.
  exact (Qle_bool_false_le _ _ Hfalse).
Qed.

Theorem gate_low_entropy_dec : forall H threshold : Q,
  Or (Id (gate_low_entropy H threshold) true)
     (Id (gate_low_entropy H threshold) false).
Proof.
  intros H threshold. unfold gate_low_entropy.
  destruct (Qle_bool H threshold).
  - left. apply eq_imp_id. reflexivity.
  - right. apply eq_imp_id. reflexivity.
Qed.

Theorem phase_side_spec : forall (l : list Q) (s : nat),
  IffT (Id (phase_side l s) 0%nat) (QleT' (H_adj (P0 l)) (H_adj (Pinf l s))).
Proof.
  intros l s. split.
  - intro E. assert (Eb : phase_side l s = 0%nat)
      by (destruct (id_sym E); reflexivity).
    unfold phase_side in Eb.
    destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))) eqn:Ex.
    + apply Qle_to_QleT'. apply (proj1 (Qle_bool_iff _ _)). exact Ex.
    + simpl in Eb. discriminate Eb.
  - intro Hle. apply eq_imp_id. unfold phase_side.
    destruct (id_sym (xq_Qle_bool_true _ _ (QleT'_to_Qle _ _ Hle))).
    reflexivity.
Qed.

Theorem phase_side_values : forall (l : list Q) (s : nat),
  Or (Id (phase_side l s) 0%nat) (Id (phase_side l s) 1%nat).
Proof.
  intros l s. unfold phase_side.
  destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))).
  - left. apply eq_imp_id. reflexivity.
  - right. apply eq_imp_id. reflexivity.
Qed.

(* ============================================================
   The true-frequency Shannon entropy ([H_freq]) theorem family and the
   data-processing inequality family.
   ============================================================ *)

(* ============================================================
   True-frequency Shannon entropy, permutation invariance, and the
   data-processing inequality.
   Content: the self-contained definition face of the true-frequency
   Shannon entropy (a rational surrogate over Q): [qn] (nat -> Q
   embedding), [freq_q] (frequency counting with Qeq_bool equality),
   [nsum] (general summation), [sqsum] (collision sum without dedup), and
   [H_freq] = 1 - sum_v p_v^2 with its theorem family (permutation
   invariance [H_freq_perm], nonnegativity, and a two-sided degeneracy
   characterization).  Background: [H_devsum] is a centroid-offset sum and
   is NOT permutation invariant (see the counterexample above); [H_freq]
   is its faithful replacement, lies in [0,1), and takes 0 on all-equal
   lists and lists of length <= 1.
   Data-processing inequality family: a coarse-grained observation
   ([map f]) does not increase [H_freq] — the counting form [freq_q_map],
   pointwise domination [freq_q_map_ge] (a Qeq-shape assumption enters
   here), collision-sum monotonicity [sqsum_map_ge], the complement sign
   flip [hfreq_core_anti], the main theorem [H_freq_dpi], endpoint
   examples, and the iterated no-decay chain.
   ============================================================ *)

(* ========== [qn]: the nat -> Q embedding (self-contained, no Z.of_nat
   dependency) ========== *)

Fixpoint qn (n : nat) : Q :=
  match n with
  | O => 0%Q
  | S k => (1 + qn k)%Q
  end.

Lemma qn_nonneg : forall n : nat, QleT' (0) (qn n).
Proof.
  intro n. induction n as [| k IH]; apply Qle_to_QleT'.
  - apply Qle_refl.
  - simpl. apply QleT'_to_Qle. apply qadd_nonneg.
    + apply (Qlt_le_weak 0 1). reflexivity.
    + apply QleT'_to_Qle. exact IH.
Qed.

Lemma qn_S_pos : forall k : nat, QltT (0) (qn (S k)).
Proof.
  intros k. apply Qlt_to_QltT. simpl. apply (Qlt_le_trans 0 1 (1 + qn k)%Q).
  - reflexivity.
  - pose proof (qadd_le 1 1 0 (qn k) (Qle_refl 1)
      (QleT'_to_Qle _ _ (qn_nonneg k))) as HH.
    simpl in HH. exact (QleT'_to_Qle _ _ HH).
Qed.

Lemma qn_pos : forall n : nat, (0 < n)%nat -> QltT (0) (qn n).
Proof.
  intros n Hn. apply Qlt_to_QltT. destruct n as [| m].
  - exfalso. lia.
  - apply QltT_to_Qlt. apply qn_S_pos.
Qed.

Lemma qn_add : forall a b : nat, QeqT (qn (a + b)%nat) (qn a + qn b).
Proof.
  intros a. induction a as [| a IH]; intros b; apply qeq_imp_qeqT.
  - rewrite Nat.add_0_l. cbn [qn]. rewrite Qplus_0_l. reflexivity.
  - cbn [qn Nat.add]. rewrite (qeqT_imp_qeq _ _ (IH b)). ring.
Qed.

Lemma qn_mul : forall a b : nat, QeqT (qn (a * b)%nat) (qn a * qn b).
Proof.
  intros a. induction a as [| a IH]; intros b; apply qeq_imp_qeqT.
  - simpl. symmetry. apply Qmult_0_l.
  - simpl. rewrite (qeqT_imp_qeq _ _ (qn_add b (a * b))).
    rewrite (qeqT_imp_qeq _ _ (IH b)). ring.
Qed.

Lemma qn_le : forall a b : nat, (a <= b)%nat -> QleT' (qn a) (qn b).
Proof.
  intros a. induction a as [| a IH]; intros b Hle; apply Qle_to_QleT'.
  - apply QleT'_to_Qle. apply qn_nonneg.
  - destruct b as [| b'].
    + exfalso. lia.
    + simpl. apply QleT'_to_Qle. apply (qadd_le 1 1 (qn a) (qn b')).
      * apply Qle_refl.
      * apply QleT'_to_Qle. apply IH. apply (le_S_n _ _ Hle).
Qed.

Lemma qn_inj : forall a b : nat, qn a == qn b -> Id (a) (b).
Proof.
  intros a. induction a as [| a IH]; intros b Heq; apply eq_imp_id.
  - destruct b as [| b'].
    + reflexivity.
    + simpl in Heq. pose proof (qn_S_pos b') as HP. simpl in HP.
      apply QltT_to_Qlt in HP. rewrite <- Heq in HP.
      exfalso. exact (Qlt_irrefl 0 HP).
  - destruct b as [| b'].
    + simpl in Heq. pose proof (qn_S_pos a) as HP. simpl in HP.
      apply QltT_to_Qlt in HP. rewrite Heq in HP.
      exfalso. exact (Qlt_irrefl 0 HP).
    + simpl in Heq.
      rewrite (Qplus_comm 1 (qn a)) in Heq.
      rewrite (Qplus_comm 1 (qn b')) in Heq.
      pose proof (proj1 (Qplus_inj_r (qn a) (qn b') 1) Heq) as H'.
      pose proof (IH b' H') as Hab. destruct (id_sym Hab). reflexivity.
Qed.

(* ========== Q division/subtraction tools (unfold Qminus, then ring; no
   division-premise gaps) ========== *)

Lemma qlt_neq0 : forall y : Q, 0 < y -> y <> 0.
Proof.
  intros y Hpy Heq. rewrite Heq in Hpy. exact (Qlt_irrefl 0 Hpy).
Qed.

Lemma qpos_neq0 : forall y : Q, 0 < y -> Not (QeqT y 0).
Proof.
  intros y Hpy Heq. apply qeqT_imp_qeq in Heq.
  apply (False_rect Empty_set). apply (Qlt_not_eq 0 y Hpy).
  apply (Qeq_sym y 0). exact Heq.
Qed.

(* on this platform the stdlib [Qmult_inv_r] has the shape x * /x == 1
   rather than a cancellation form; a cancellation lemma is built here (the
   field side condition is exactly the Qeq shape ~ (B == 0)) *)
Lemma qmult_inv_cancel_r : forall A B : Q, ~ (B == 0) -> QeqT (A * / B * B) (A).
Proof.
  intros A B HB. apply qeq_imp_qeqT. field. exact HB.
Qed.

Lemma qsub_eq0 : forall a b : Q, a - b == 0 -> QeqT (a) (b).
Proof.
  intros a b H.
  apply qeq_imp_qeqT.
  assert (Ha : a == (a - b) + b).
  { unfold Qminus. ring. }
  rewrite H in Ha. rewrite Qplus_0_l in Ha. exact Ha.
Qed.

(* a zero numerator (including the degenerate zero denominator) gives a
   zero quotient: the case 0/0 == 0 is covered as well *)
Lemma qdiv_zero_num : forall A B : Q, A == 0 -> QeqT (A / B) (0).
Proof.
  intros A B H. apply qeq_imp_qeqT. unfold Qdiv. rewrite H. apply Qmult_0_l.
Qed.

Lemma qdiv_eq0_num : forall A B : Q, 0 < B -> A / B == 0 -> QeqT A 0.
Proof.
  intros A B HB H. apply qeq_imp_qeqT. unfold Qdiv in H.
  assert (HBne : ~ (B == 0)).
  { intro Hb. destruct (qpos_neq0 B HB (qeq_imp_qeqT _ _ Hb)). }
  pose proof (qeqT_imp_qeq _ _ (qmult_inv_cancel_r A B HBne)) as Hcancel.
  rewrite H in Hcancel. rewrite Qmult_0_l in Hcancel.
  apply (Qeq_sym 0 A). exact Hcancel.
Qed.

Lemma qdiv_nonneg : forall A B : Q, 0 <= A -> 0 < B -> QleT' (0) (A / B).
Proof.
  intros A B HA HB. apply Qle_to_QleT'. unfold Qdiv. apply Qmult_le_0_compat.
  - exact HA.
  - apply Qlt_le_weak. apply (Qinv_lt_0_compat B HB).
Qed.

Lemma qnum_zero : forall n s : nat, qn (n * n) == qn s -> QeqT (qn n * qn n - qn s) (0).
Proof.
  intros n s H. apply qeq_imp_qeqT.
  rewrite <- (qeqT_imp_qeq _ _ (qn_mul n n)). rewrite <- H.
  unfold Qminus. apply Qplus_opp_r.
Qed.

Lemma qeqb_false_neq : forall x y : Q, Qeq_bool x y = false -> x <> y.
Proof.
  intros x y H Hxy.
  assert (Ht : Qeq_bool x y = true).
  { apply (proj2 (Qeq_bool_iff x y)). rewrite <- Hxy. apply Qeq_refl. }
  rewrite Ht in H. discriminate H.
Qed.

(* ========== [freq_q]: self-contained frequency counting (decidable by
   Qeq_bool) ========== *)

Fixpoint freq_q (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (freq_q x ys) else freq_q x ys
  end.

Lemma freq_q_le_length : forall (x : Q) (l : list Q), NatLe (freq_q x l) ((length l)%nat).
Proof.
  intros x l. apply NatLe_lift. induction l as [| y ys IH]; simpl.
  - lia.
  - simpl. destruct (Qeq_bool x y); lia.
Qed.

(* baseline: frequencies are additive under concatenation *)
Theorem freq_q_app : forall (x : Q) (l p : list Q), Id (freq_q x (l ++ p)) ((freq_q x l + freq_q x p)%nat).
Proof.
  intros x l p. apply eq_imp_id. induction l as [| a l IH].
  - reflexivity.
  - simpl. destruct (Qeq_bool x a); rewrite IH; lia.
Qed.

(* precondition of the main theorem: frequencies are permutation invariant
   (induction on the constructors of Permutation; in the perm_swap branch
   both sides count the same x0, so only the four branches need literal
   reordering, without Qeq_bool symmetry) *)
Theorem freq_q_perm : forall (x : Q) (l p : list Q),
  Permutation l p -> Id (freq_q x l) (freq_q x p).
Proof.
  intros x l p H.
  apply eq_imp_id.
  induction H as [ | y l' p' Hy IH | y z l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. destruct (Qeq_bool x y); rewrite IH; reflexivity.
  - simpl. destruct (Qeq_bool x y); destruct (Qeq_bool x z); reflexivity.
  - rewrite IH1. exact IH2.
Qed.

Lemma freq_q_eq_all : forall (x : Q) (l : list Q),
  (forall z, In z l -> z == x) -> Id (freq_q x l) (length l).
Proof.
  intros x l. induction l as [| y ys IH]; intros H; apply eq_imp_id.
  - reflexivity.
  - assert (Hy : Qeq_bool x y = true).
    { apply (proj2 (Qeq_bool_iff x y)). apply (Qeq_sym y x). apply H.
      left. reflexivity. }
    simpl. rewrite Hy. f_equal.
    destruct (id_sym (IH (fun z Hz => H z (or_intror Hz)))). reflexivity.
Qed.

Lemma freq_q_full_count : forall (x : Q) (l : list Q),
  freq_q x l = length l -> forall y, In y l -> QeqT (y) (x).
Proof.
  intros x l. induction l as [| a l IH]; intros Hcnt y0 Hy0.
  - destruct Hy0.
  - apply qeq_imp_qeqT. destruct Hy0 as [Hy0 | Hy0].
    + subst y0. destruct (Qeq_bool x a) eqn:Hyb.
      * apply (Qeq_sym x a). apply (proj1 (Qeq_bool_iff x a)). exact Hyb.
      * exfalso. simpl in Hcnt. rewrite Hyb in Hcnt.
        pose proof (NatLe_drop _ _ (freq_q_le_length x l)) as HL. lia.
    + apply qeqT_imp_qeq. apply IH.
      * destruct (Qeq_bool x a) eqn:Hyb.
        -- simpl in Hcnt. rewrite Hyb in Hcnt. lia.
        -- exfalso. simpl in Hcnt. rewrite Hyb in Hcnt.
           pose proof (NatLe_drop _ _ (freq_q_le_length x l)) as HL. lia.
      * exact Hy0.
Qed.

(* ========== [nsum]: general nat-indexed summation with Q values
   ========== *)

Fixpoint nsum (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => (f y + nsum f ys)%nat
  end.

Lemma nsum_ext_in : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> f x = g x) -> Id (nsum f l) (nsum g l).
Proof.
  intros f g l. induction l as [| y ys IH]; simpl; intros H; apply eq_imp_id.
  - reflexivity.
  - rewrite (H y (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

Lemma nsum_perm : forall (f : Q -> nat) (l p : list Q),
  Permutation l p -> Id (nsum f l) (nsum f p).
Proof.
  intros f l p H.
  apply eq_imp_id.
  induction H as [ | x l' p' Hx IH | x y l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. lia.
  - rewrite IH1. exact IH2.
Qed.

Lemma nsum_const : forall (n : nat) (l : list Q), Id (nsum (fun _ => n) l) ((length l * n)%nat).
Proof.
  intros n l. apply eq_imp_id. induction l as [| y ys IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma nsum_bound : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) -> NatLe (nsum f l) ((length l * B)%nat).
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (Hy : (f y <= B)%nat) by (apply H; left; reflexivity).
    assert (Hys : NatLe (nsum f ys) (length ys * B))
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ Hys). lia.
Qed.

Lemma nsum_bound_eq : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) ->
  nsum f l = (length l * B)%nat ->
  forall x, In x l -> Id (f x) (B).
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros Hsat Heq x0 Hx0;
    apply eq_imp_id.
  - destruct Hx0.
  - assert (Hy : (f y <= B)%nat) by (apply Hsat; left; reflexivity).
    assert (Hys : NatLe (nsum f ys) (length ys * B))
      by (apply (nsum_bound f ys B); intros x Hx; apply Hsat; right; exact Hx).
    pose proof (NatLe_drop _ _ Hys) as HysL.
    assert (Hfy : f y = B) by lia.
    assert (HysEq : nsum f ys = (length ys * B)%nat) by lia.
    destruct Hx0 as [Hx0 | Hx0].
    + subst x0. exact Hfy.
    + destruct (id_sym (IH (fun z Hz => Hsat z (or_intror Hz)) HysEq x0 Hx0)).
      reflexivity.
Qed.

(* ========== [sqsum]: sum_{x in l} freq_q x l = sum_v c_v^2 (dedup-free)
   ========== *)

Definition sqsum (l : list Q) : nat := nsum (fun x => freq_q x l) l.

Definition all_same (l : list Q) : Set :=
  forall a b, In a l -> In b l -> QeqT a b.

Theorem sqsum_perm : forall l p : list Q,
  Permutation l p -> Id (sqsum l) (sqsum p).
Proof.
  intros l p H. unfold sqsum.
  assert (Hex : forall x, In x l -> freq_q x l = freq_q x p).
  { intros x _. destruct (freq_q_perm x l p H). reflexivity. }
  destruct (id_sym (nsum_ext_in (fun x => freq_q x l) (fun x => freq_q x p) l Hex)).
  exact (nsum_perm (fun x => freq_q x p) l p H).
Qed.

Lemma sqsum_le : forall l : list Q, NatLe (sqsum l) ((length l * length l)%nat).
Proof.
  intros l. unfold sqsum.
  apply (nsum_bound (fun x => freq_q x l) l (length l)).
  intros x _. apply NatLe_drop. apply freq_q_le_length.
Qed.

Lemma freq_q_all_same : forall (x : Q) (l : list Q),
  In x l -> all_same l -> Id (freq_q x l) (length l).
Proof.
  intros x l Hin Hs. apply freq_q_eq_all. intros z Hz.
  unfold all_same in Hs. apply qeqT_imp_qeq. apply Hs.
  - exact Hz.
  - exact Hin.
Qed.

Lemma sqsum_all_same : forall l : list Q,
  all_same l -> Id (sqsum l) ((length l * length l)%nat).
Proof.
  intros l Hs. unfold sqsum.
  assert (Hex : forall x, In x l -> freq_q x l = length l).
  { intros x Hx. destruct (id_sym (freq_q_all_same x l Hx Hs)). reflexivity. }
  destruct (id_sym (nsum_ext_in (fun x => freq_q x l)
              (fun _ : Q => length l) l Hex)).
  apply nsum_const.
Qed.

Lemma sqsum_eq_all_same : forall l : list Q,
  sqsum l = (length l * length l)%nat -> all_same l.
Proof.
  intros l Heq. destruct l as [| x xs].
  - intros a b Ha Hb. destruct Ha.
  - unfold sqsum in Heq.
    pose proof (nsum_bound_eq (fun x0 => freq_q x0 (x :: xs)) (x :: xs)
                  (length (x :: xs))
                  (fun x0 _ => NatLe_drop _ _ (freq_q_le_length x0 (x :: xs)))
                  Heq x (or_introl eq_refl)) as Hfx.
    assert (HfxE : freq_q x (x :: xs) = length (x :: xs))
      by (destruct Hfx; reflexivity).
    pose proof (freq_q_full_count x (x :: xs) HfxE) as Hall.
    intros a b Ha Hb. apply qeq_imp_qeqT. apply (Qeq_trans a x b).
    + apply qeqT_imp_qeq. apply Hall. exact Ha.
    + apply (Qeq_sym b x). apply qeqT_imp_qeq. apply Hall. exact Hb.
Qed.

(* ========== [H_freq]: the rational surrogate of the true-frequency Shannon
   entropy and its main theorems ========== *)

(* [H_freq l = 1 - sum_v p_v^2 = (n^2 - sum_v c_v^2) / n^2] (over Q; the
   value is 0 when n = 0) *)
Definition H_freq (l : list Q) : Q :=
  (qn (length l) * qn (length l) - qn (sqsum l))
    / (qn (length l) * qn (length l)).

(* main theorem: permutation invariance — a theorem the centroid-offset
   shape of the old [H_devsum] could not express *)
Theorem H_freq_perm : forall l p : list Q,
  Permutation l p -> QeqT (H_freq l) (H_freq p).
Proof.
  intros l p Hp. apply qeq_imp_qeqT. unfold H_freq.
  destruct (id_sym (sqsum_perm l p Hp)).
  rewrite (Permutation_length Hp).
  reflexivity.
Qed.

(* nonnegativity (for the chosen shape: n^2 >= sum c_v^2, and division by a
   positive denominator preserves the sign; for the empty list numerator
   and denominator are both zero and the value is 0) *)
Theorem H_freq_nonneg : forall l : list Q, QleT' (0) (H_freq l).
Proof.
  intros l. apply Qle_to_QleT'. destruct l as [| x xs].
  - assert (Hz : H_freq [] == 0).
    { unfold H_freq. apply qeqT_imp_qeq. apply qdiv_zero_num.
      apply qeqT_imp_qeq. apply qnum_zero. reflexivity. }
    rewrite Hz. apply Qle_refl.
  - unfold H_freq. apply QleT'_to_Qle. apply qdiv_nonneg.
    + apply QleT'_to_Qle. apply (fst (Qle_0_sub' (qn (sqsum (x :: xs)))
                 (qn (length (x :: xs)) * qn (length (x :: xs))))).
      apply Qle_to_QleT'.
      rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs)) (length (x :: xs)))).
      apply QleT'_to_Qle. apply qn_le. apply NatLe_drop. apply sqsum_le.
    + rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs)) (length (x :: xs)))).
      apply QltT_to_Qlt. apply qn_pos. simpl. apply Nat.lt_0_succ.
Qed.

(* degeneracy characterization (forward): all values equal implies
   [H_freq] takes 0 *)
Theorem H_freq_all_same_zero : forall l : list Q,
  all_same l -> QeqT (H_freq l) (0).
Proof.
  intros l Hs. apply qeq_imp_qeqT. unfold H_freq.
  apply qeqT_imp_qeq. apply qdiv_zero_num.
  apply qeqT_imp_qeq. apply qnum_zero.
  destruct (id_sym (sqsum_all_same l Hs)). reflexivity.
Qed.

Theorem H_freq_len_le_1 : forall l : list Q,
  (length l <= 1)%nat -> QeqT (H_freq l) (0).
Proof.
  intros l Hl. destruct l as [| x xs].
  - apply H_freq_all_same_zero. intros a b Ha Hb. destruct Ha.
  - simpl in Hl. destruct xs as [| y ys].
    + apply H_freq_all_same_zero. intros a b Ha Hb.
      destruct (Qeq_bool a x) eqn:Ea.
      * apply qeq_imp_qeqT. apply (Qeq_trans a x b).
        -- apply (proj1 (Qeq_bool_iff a x)). exact Ea.
        -- destruct (Qeq_bool b x) eqn:Eb.
           ++ apply (Qeq_sym b x). apply (proj1 (Qeq_bool_iff b x)). exact Eb.
           ++ exfalso. destruct Hb as [Hb | Hb].
              ** rewrite <- Hb in Eb. rewrite Qeq_bool_refl in Eb.
                 discriminate Eb.
              ** exact Hb.
      * exfalso. destruct Ha as [Ha | Ha].
        -- rewrite <- Ha in Ea. rewrite Qeq_bool_refl in Ea. discriminate Ea.
        -- exact Ha.
    + simpl in Hl. exfalso. lia.
Qed.

(* degeneracy characterization (backward): [H_freq] takes 0 implies all
   values equal (two-sided closure) *)
Theorem H_freq_eq0_all_same : forall l : list Q,
  H_freq l == 0 -> all_same l.
Proof.
  intros l Heq. unfold H_freq in Heq. destruct l as [| x xs].
  - intros a b Ha Hb. destruct Ha.
  - assert (HB : 0 < qn (length (x :: xs)) * qn (length (x :: xs))).
    { rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs))
                     (length (x :: xs)))).
      apply QltT_to_Qlt. apply qn_pos. simpl. apply Nat.lt_0_succ. }
    assert (Hnum : qn (length (x :: xs)) * qn (length (x :: xs))
                   - qn (sqsum (x :: xs)) == 0)
      by (apply (qeqT_imp_qeq _ _ (qdiv_eq0_num _ _ HB Heq))).
    pose proof (qeqT_imp_qeq _ _
      (qsub_eq0 (qn (length (x :: xs)) * qn (length (x :: xs)))
                  (qn (sqsum (x :: xs))) Hnum)) as Hab.
    rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs))
                     (length (x :: xs)))) in Hab.
    pose proof (qn_inj (length (x :: xs) * length (x :: xs))
                  (sqsum (x :: xs)) Hab) as Heqnat.
    assert (HeqnatE : sqsum (x :: xs)
                      = (length (x :: xs) * length (x :: xs))%nat)
      by (destruct Heqnat; reflexivity).
    apply sqsum_eq_all_same. exact HeqnatE.
Qed.

(* ############################################################
   The data-processing inequality family for [H_freq].
   ############################################################ *)

(* ========== list/sum transfer tools ========== *)

(* [map] preserves length (built here, avoiding stdlib rename drift) *)
Lemma length_map_self : forall (f : Q -> Q) (l : list Q), Id (length (map f l)) (length l).
Proof.
  intros f l. induction l as [| a l IH]; simpl; apply eq_imp_id.
  - reflexivity.
  - destruct (id_sym IH). reflexivity.
Qed.

(* pointwise monotonicity of the general sum *)
Lemma nsum_le : forall (g h : Q -> nat) (l : list Q),
  (forall x, In x l -> (g x <= h x)%nat) -> NatLe (nsum g l) ((nsum h l)%nat).
Proof.
  intros g h l. induction l as [| a l IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (H1 : (g a <= h a)%nat) by (apply H; left; reflexivity).
    assert (H2 : NatLe (nsum g l) (nsum h l))
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ H2). lia.
Qed.

(* summing over map = summing the composition (the exchange bridge between
   [nsum] and [map]) *)
Lemma nsum_map : forall (g : Q -> nat) (f : Q -> Q) (l : list Q), Id (nsum g (map f l)) (nsum (fun x => g (f x)) l).
Proof.
  intros g f l. induction l as [| a l IH]; simpl; apply eq_imp_id.
  - reflexivity.
  - destruct (id_sym IH). reflexivity.
Qed.

(* ========== baseline: the pushforward counting lemma and pointwise
   domination ========== *)

(* baseline pushforward lemma, counting form: the frequency of y after
   [map] equals the number of votes of members x with f x == y in the
   original list *)
Theorem freq_q_map : forall (f : Q -> Q) (y : Q) (l : list Q), Id (freq_q y (map f l)) (nsum (fun x : Q => if Qeq_bool y (f x) then 1%nat else 0%nat) l).
Proof.
  intros f y l. induction l as [| a l IH]; simpl; apply eq_imp_id.
  - reflexivity.
  - destruct (Qeq_bool y (f a)); destruct (id_sym IH); reflexivity.
Qed.

(* Qeq-shape bridge, pointwise domination: the votes of x in the original
   list are <= the votes of f x in the image list.  A true vote (x == a)
   still hits under f (the shape assumption preserves hits), and the image
   list may merge additional votes (other values with the same image), so
   votes only grow — the micro-mechanism of the data-processing
   inequality. *)
Lemma freq_q_map_ge : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall (x : Q) (l : list Q), NatLe (freq_q x l) ((freq_q (f x) (map f l))%nat).
Proof.
  intros f Hf x l. induction l as [| a l IH]; simpl; apply NatLe_lift.
  - lia.
  - pose proof (NatLe_drop _ _ IH) as IHL.
    destruct (Qeq_bool x a) eqn:H1.
    + assert (H2 : Qeq_bool (f x) (f a) = true).
      { apply (proj2 (Qeq_bool_iff (f x) (f a))). apply Hf.
        apply (proj1 (Qeq_bool_iff x a)). exact H1. }
      rewrite H2. lia.
    + destruct (Qeq_bool (f x) (f a)); lia.
Qed.

(* mass-merging monotonicity, collision-sum form:
   [sqsum (map f l) >= sqsum l], by summing over map ([nsum_map]) and
   pointwise domination ([freq_q_map_ge]). *)
Theorem sqsum_map_ge : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall l : list Q, NatLe (sqsum l) ((sqsum (map f l))%nat).
Proof.
  intros f Hf l. unfold sqsum.
  destruct (id_sym (nsum_map (fun y => freq_q y (map f l)) f l)).
  apply nsum_le. intros x _. apply NatLe_drop. apply freq_q_map_ge. exact Hf.
Qed.

(* ========== Q division/subtraction monotonicity tools (the complement
   sign-flip machinery of the DPI) ========== *)

(* subtraction distributes over same-denominator quotients (unfold Qminus
   and Qdiv, then ring; [Qinv] stays atomic) *)
Lemma qdiv_sub_distr : forall A B D : Q, QeqT (A / D - B / D) ((A - B) / D).
Proof.
  intros A B D. apply qeq_imp_qeqT. unfold Qminus, Qdiv. ring.
Qed.

(* right monotonicity of subtraction: A <= B gives D - B <= D - A (the core
   of complement monotonicity with sign flip) *)
Lemma qsub_mono_r : forall D A B : Q, A <= B -> QleT' (D - B) (D - A).
Proof.
  intros D A B H. apply Qle_to_QleT'. unfold Qminus.
  apply QleT'_to_Qle. apply (qadd_le D D (- B) (- A)).
  - apply Qle_refl.
  - apply QleT'_to_Qle. apply qopp_le. exact H.
Qed.

(* core form: for N >= 1 the collision sum in [0, N^2] passes monotonically
   through the complement quotient with a sign flip ([qdiv_sub_distr]
   merges the quotient difference into a single quotient, [qdiv_nonneg]
   keeps the sign; for N = 0 both sides are literally A = B = 0). *)
Lemma hfreq_core_anti : forall (N A B : nat), (A <= B)%nat -> (B <= N * N)%nat -> QleT' ((qn N * qn N - qn B) / (qn N * qn N)) ((qn N * qn N - qn A) / (qn N * qn N)).
Proof.
  intros N A B HAB HBN.
  apply Qle_to_QleT'.
  destruct N as [| m].
  - assert (HA : A = 0%nat) by lia.
    assert (HB : B = 0%nat) by lia.
    subst. apply Qle_refl.
  - assert (HD : 0 < qn (S m) * qn (S m)).
    { rewrite <- (qeqT_imp_qeq _ _ (qn_mul (S m) (S m))).
      apply QltT_to_Qlt. apply qn_pos. simpl. apply Nat.lt_0_succ. }
    pose proof (qpos_neq0 (qn (S m) * qn (S m)) HD) as HDneq.
    apply QleT'_to_Qle. apply (snd (Qle_0_sub'
              ((qn (S m) * qn (S m) - qn B) / (qn (S m) * qn (S m)))
              ((qn (S m) * qn (S m) - qn A) / (qn (S m) * qn (S m))))).
    apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ (qdiv_sub_distr (qn (S m) * qn (S m) - qn A)
                            (qn (S m) * qn (S m) - qn B)
                            (qn (S m) * qn (S m)))).
    apply QleT'_to_Qle. apply qdiv_nonneg.
    + apply QleT'_to_Qle. apply (fst (Qle_0_sub' (qn (S m) * qn (S m) - qn B)
                               (qn (S m) * qn (S m) - qn A))).
      apply qsub_mono_r. apply QleT'_to_Qle. apply qn_le. exact HAB.
    + exact HD.
Qed.

(* ========== main theorem: the data-processing inequality (DPI) ========== *)

(* observation (coarse-graining that merges masses) does not increase
   [H_freq]: [H_freq (map f l) <= H_freq l].
   The shape assumption is the Qeq-honest conservation of the
   equivalence-class-merging semantics: for an arbitrary bare function f
   the claim is false — a bare function can observe the Record
   representation of Q (e.g. take the numerator); the counterexample
   l = [1/2; 2/4] has H_freq l = 0 but H_freq (map numerator l) = 1/2.
   Hence the main theorem carries the shape assumption
   (forall x y : Q, x == y -> f x == f y). *)
Theorem H_freq_dpi : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall l : list Q, QleT' (H_freq (map f l)) (H_freq l).
Proof.
  intros f Hf l.
  apply Qle_to_QleT'.
  assert (Hlen : length (map f l) = length l)
    by (destruct (length_map_self f l); reflexivity).
  destruct l as [| x xs].
  - replace (map f (@nil Q)) with (@nil Q) by reflexivity.
    apply Qle_refl.
  - unfold H_freq. rewrite Hlen.
    apply QleT'_to_Qle. apply (hfreq_core_anti (length (x :: xs))
                           (sqsum (x :: xs)) (sqsum (map f (x :: xs)))).
    + apply NatLe_drop. apply sqsum_map_ge. exact Hf.
    + pose proof (sqsum_le (map f (x :: xs))) as Hs.
      rewrite Hlen in Hs. exact (NatLe_drop _ _ Hs).
Qed.

(* ========== two endpoint examples: pinning the behavior at both ends of
   the DPI ========== *)

(* endpoint one, identity does not decay: the identity map (the finest
   observation) loses nothing — bridged directly by Leibniz equality of
   lists, no shape assumption needed. *)
Theorem H_freq_map_id : forall l : list Q, QeqT (H_freq (map (fun x : Q => x) l)) (H_freq l).
Proof.
  intros l.
  apply qeq_imp_qeqT.
  assert (Hid : map (fun x : Q => x) l = l).
  { induction l as [| a l IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity. }
  rewrite Hid. apply Qeq_refl.
Qed.

(* the image of a constant map is all-equal (Leibniz on lists) *)
Lemma in_map_const : forall (c : Q) (l : list Q) (a : Q),
  In a (map (fun _ : Q => c) l) -> QeqT (a) (c).
Proof.
  intros c l. induction l as [| b l IH]; simpl; intros a H; apply qeq_imp_qeqT.
  - destruct H.
  - destruct H as [H | H].
    + subst a. apply Qeq_refl.
    + apply qeqT_imp_qeq. apply IH. exact H.
Qed.

(* endpoint two, constant maps collapse everything: the coarsest observation
   (merging everything into one bucket) makes [H_freq] take 0 (degenerate
   form; true for the empty list too, whose [H_freq] is 0 anyway). *)
Theorem H_freq_map_const : forall (c : Q) (l : list Q), QeqT (H_freq (map (fun _ : Q => c) l)) (0).
Proof.
  intros c l. apply H_freq_all_same_zero.
  intros a b Ha Hb. apply qeq_imp_qeqT. apply (Qeq_trans a c b).
  - exact (qeqT_imp_qeq _ _ (in_map_const c l a Ha)).
  - apply (Qeq_sym b c). exact (qeqT_imp_qeq _ _ (in_map_const c l b Hb)).
Qed.

(* ========== bonus: the iterated no-decay chain ========== *)

(* two-step composition, directly: the second observation still does not
   increase (g must also respect the shape) *)
Theorem H_freq_map_twice : forall (f g : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  (forall x y : Q, x == y -> g x == g y) ->
  forall l : list Q, QleT' (H_freq (map g (map f l))) (H_freq (map f l)).
Proof.
  intros f g Hf Hg l. apply (H_freq_dpi g Hg (map f l)).
Qed.

(* chain: H_freq (map g (map f l)) <= H_freq (map f l) <= H_freq l *)
Theorem H_freq_map_chain : forall (f g : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  (forall x y : Q, x == y -> g x == g y) ->
  forall l : list Q, QleT' (H_freq (map g (map f l))) (H_freq l).
Proof.
  intros f g Hf Hg l.
  apply Qle_to_QleT'.
  apply (Qle_trans (H_freq (map g (map f l))) (H_freq (map f l)) (H_freq l)).
  - apply QleT'_to_Qle. apply (H_freq_dpi g Hg (map f l)).
  - apply QleT'_to_Qle. apply (H_freq_dpi f Hf l).
Qed.

(* ============================================================
   The three missing members of the multi-entropy family ([collide] /
   [maxfreq] / [H_min_q] and [H_max_q]) with the Renyi ladder order-chain
   main theorem [H_chain], plus the [H_freq] coherence bridge and the
   permutation-invariance closure.
   ============================================================ *)

(* ============================================================
   The three missing members of the multi-entropy family:
   [collide] (the Renyi-order-2 collision entropy core sum p_v^2),
   [maxfreq] (normalized maximum frequency), [H_max_q] = 1 - maxfreq and
   [H_min_q] = 1 - collide (the specified shapes).
   Main theorem, the Renyi ladder for nonempty l, all three members in one
   chain: [1 / qn n <= collide l <= maxfreq l <= 1]
   (sum p^2 >= 1/n is the discrete Cauchy-Schwarz; sum p^2 <=
   max p * sum p is proved by nat-side induction and bridged by Q
   division).
   Coherence: [H_freq l == 1 - collide l] for nonempty l ([H_freq] is the
   alias of 1 - collide).
   Convention note: Q has no logarithm, so the entropy complement 1 - x is
   the rational surrogate; it is decreasing in x exactly like -log x, so
   the order properties carry over faithfully.  For all-equal lists
   [maxfreq] takes 1 (the complement takes 0); empty lists take 0; the
   whole family is permutation invariant.
   ============================================================ *)

(* ========== Q order/division tools (built where the stdlib shapes
   differ) ========== *)

(* [Qeq] can be rewritten directly into [Qle] goals *)
Lemma qeq_le_l : forall x y : Q, x == y -> QleT' (x) (y).
Proof.
  intros x y H. apply Qle_to_QleT'. rewrite H. apply Qle_refl.
Qed.

(* qn n >= 1 (for n >= 1; via [qadd_le]) *)
Lemma qn_ge1 : forall n : nat, (1 <= n)%nat -> QleT' (1:Q) (qn n).
Proof.
  intros n Hn. apply Qle_to_QleT'. destruct n as [| k].
  - exfalso. lia.
  - simpl.
    pose proof (qadd_le 1 1 0 (qn k) (Qle_refl 1)
      (QleT'_to_Qle _ _ (qn_nonneg k))) as HH.
    simpl in HH. exact (QleT'_to_Qle _ _ HH).
Qed.

(* positivity of products of [qn] values (nat-side nonnegative
   multiplication plus monotonicity of [qn]) *)
Lemma qn_mul_pos : forall a b : nat, (0 < a)%nat -> (0 < b)%nat -> QltT (0) (qn a * qn b).
Proof.
  intros a b Ha Hb.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans 0 (qn a) (qn a * qn b)).
  - apply QltT_to_Qlt. apply qn_pos. exact Ha.
  - assert (Hab : (a <= a * b)%nat).
    { apply (Nat.le_trans a (a * 1) (a * b)).
      - lia.
      - apply Nat.mul_le_mono_l. lia. }
    rewrite <- (qeqT_imp_qeq _ _ (qn_mul a b)).
    apply QleT'_to_Qle. apply qn_le. exact Hab.
Qed.

(* length positivity of a nonempty list (pure nat side; [simpl] only on nat
   goals — on Q goals it would unfold Qlt into Qnum/Qden encodings and
   break the [apply]) *)
Lemma qlen_pos : forall (x : Q) (l : list Q), NatLe 1 (length (x :: l)).
Proof.
  intros x l. apply NatLe_lift.
  change (length (x :: l)) with (S (length l)). lia.
Qed.

(* positivity of products of embedded nonempty-list lengths (the unified Q
   entry of the order chain) *)
Lemma qlen_mul_pos : forall (x : Q) (l : list Q), QltT (0) (qn (length (x :: l)) * qn (length (x :: l))).
Proof.
  intros x l. apply qn_mul_pos;
    [ apply NatLe_drop, qlen_pos | apply NatLe_drop, qlen_pos ].
Qed.

(* same-denominator division is monotone in the numerator (positive
   denominator; positivity of the inverse via [Qinv_lt_0_compat], since the
   stdlib here has no left-compatible le form) *)
Lemma qdiv_ge_num : forall A C B : Q, 0 < B -> C <= A -> QleT' (C / B) (A / B).
Proof.
  intros A C B HB Hle. apply Qle_to_QleT'. unfold Qdiv.
  apply Qmult_le_compat_r.
  - exact Hle.
  - apply (Qlt_le_weak 0 (/ B)). apply (Qinv_lt_0_compat B HB).
Qed.

(* numerator <= denominator gives quotient <= 1 ([Qmult_inv_r] is the
   specialized multiply-out-to-1 form) *)
Lemma qdiv_le_1 : forall A B : Q, A <= B -> 0 < B -> QleT' (A / B) (1).
Proof.
  intros A B Hle HB. apply Qle_to_QleT'. unfold Qdiv.
  assert (Hpos : 0 <= / B)
    by (apply (Qlt_le_weak 0 (/ B)); apply (Qinv_lt_0_compat B HB)).
  assert (Hm : A * / B <= B * / B) by (apply Qmult_le_compat_r; assumption).
  apply (Qle_trans (A * / B) (B * / B) 1 Hm).
  apply QleT'_to_Qle. apply qeq_le_l. apply Qmult_inv_r.
  intro Hc. assert (Hc2 : B == 0) by (rewrite Hc; reflexivity).
  destruct (qpos_neq0 B HB (qeq_imp_qeqT _ _ Hc2)).
Qed.

(* normalization: 1 / P == P / (P * P) (the field side condition is a Qeq
   shape, discharged from the context assumption) *)
Lemma qdiv_norm : forall P : Q, ~ (P == 0) -> ~ (P * P == 0) -> QeqT (1 / P) (P / (P * P)).
Proof.
  intros P HP1 HP2. apply qeq_imp_qeqT. field; assumption.
Qed.

(* order-reversing subtraction (z fixed; unfold Qminus first, then
   [qadd_le], avoiding apply-unification trouble) *)
Lemma qsub_le : forall x y z : Q, x <= y -> QleT' (z - y) (z - x).
Proof.
  intros x y z H. apply Qle_to_QleT'. unfold Qminus.
  apply QleT'_to_Qle. apply (qadd_le z z (- y) (- x)).
  - apply Qle_refl.
  - exact (Qopp_le_compat x y H).
Qed.

(* ========== [nmax]: general nat-indexed maximum with Q values (the dual
   of [nsum]) ========== *)

Fixpoint nmax (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => Nat.max (f y) (nmax f ys)
  end.

Lemma nmax_bound : forall (f : Q -> nat) (l : list Q) (y : Q),
  In y l -> NatLe (f y) ((nmax f l)%nat).
Proof.
  intros f l y Hy. revert Hy.
  induction l as [| z zs IH]; simpl; intros Hy; apply NatLe_lift.
  - destruct Hy.
  - destruct Hy as [Hz | Hy].
    + subst z. apply Nat.le_max_l.
    + apply (Nat.le_trans (f y) (nmax f zs) (Nat.max (f z) (nmax f zs))).
      * apply NatLe_drop. apply IH. exact Hy.
      * apply Nat.le_max_r.
Qed.

Lemma nmax_le_bound : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) -> NatLe (nmax f l) ((B)%nat).
Proof.
  intros f l B. induction l as [| z zs IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (Hz : (f z <= B)%nat) by (apply H; left; reflexivity).
    assert (Hzs : NatLe (nmax f zs) B)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ Hzs). lia.
Qed.

Lemma nmax_ext_in : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> f x = g x) -> Id (nmax f l) (nmax g l).
Proof.
  intros f g l. induction l as [| y ys IH]; simpl; intros H; apply eq_imp_id.
  - reflexivity.
  - rewrite (H y (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

(* permutation invariance of the general maximum (perm_swap branch closed
   by commutativity of Nat.max) *)
Lemma nmax_perm : forall (f : Q -> nat) (l p : list Q),
  Permutation l p -> Id (nmax f l) (nmax f p).
Proof.
  intros f l p H.
  apply eq_imp_id.
  induction H as [ | x l' p' Hx IH | x y l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. lia.
  - rewrite IH1. exact IH2.
Qed.

(* ========== frequency complements (the nat-side baseline) ========== *)

(* every member has frequency >= 1 (the false branch of Qeq_bool is closed
   by the contradiction lemma [qeqb_false_neq]) *)
Lemma freq_q_ge1 : forall (x : Q) (l : list Q), In x l -> NatLe (1) ((freq_q x l)%nat).
Proof.
  intros x l Hin. revert Hin.
  induction l as [| y ys IH]; intros Hin; simpl; apply NatLe_lift.
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + subst y. destruct (Qeq_bool x x) eqn:Exx.
      * lia.
      * exfalso. apply (qeqb_false_neq x x Exx). reflexivity.
    + destruct (Qeq_bool x y) eqn:Exy.
      * lia.
      * apply NatLe_drop. apply IH. exact Hin.
Qed.

(* lower bound of the general sum (the dual of [nsum_bound]) *)
Lemma nsum_ge_const : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (B <= f x)%nat) -> NatLe (length l * B) ((nsum f l)%nat).
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (Hy : (B <= f y)%nat) by (apply H; left; reflexivity).
    assert (Hys : NatLe (length ys * B) (nsum f ys))
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ Hys). lia.
Qed.

(* nat-side baseline core: [sqsum >= length] (pointwise freq >= 1; the
   entry of the Cauchy-Schwarz lower bound) *)
Lemma sqsum_ge_length : forall l : list Q, NatLe (length l) ((sqsum l)%nat).
Proof.
  intros l. unfold sqsum.
  pose proof (nsum_ge_const (fun x => freq_q x l) l 1
                (fun x Hx => NatLe_drop _ _ (freq_q_ge1 x l Hx))) as Hge.
  rewrite Nat.mul_1_r in Hge. exact Hge.
Qed.

(* ========== [collide]: the Renyi-2 / collision-entropy core sum p^2 and
   its bounding theorems (baseline) ========== *)

(* collide l = sum_{x in l} (freq_q x l / n)² = qn (sqsum l) / (qn n * qn n) *)
Definition collide (l : list Q) : Q :=
  qn (sqsum l) / (qn (length l) * qn (length l)).

Lemma collide_zero : QeqT (collide []) (0).
Proof. apply qeq_imp_qeqT.
  assert (Hz : (qn (sqsum []) == 0)%Q).
  { change (qn (nsum (fun x => freq_q x []) []) == 0%Q).
    change (qn 0 == 0%Q).
    reflexivity. }
  unfold collide. unfold Qdiv. rewrite Hz. apply Qmult_0_l.
Qed.

(* upper bound: [collide <= 1] (whole list; [sqsum <= n^2]) *)
Theorem collide_upper : forall l : list Q, QleT' (collide l) (1).
Proof.
  intros l. destruct l as [| x xs].
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ collide_zero).
    apply (Qlt_le_weak 0 1). reflexivity.
  - unfold collide. apply qdiv_le_1.
    + assert (Hle : qn (sqsum (x :: xs))
                    <= qn (length (x :: xs)) * qn (length (x :: xs))).
      { rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs))
                         (length (x :: xs)))).
        apply QleT'_to_Qle. apply qn_le. apply NatLe_drop. apply sqsum_le. }
      exact Hle.
    + apply QltT_to_Qlt. apply qlen_mul_pos.
Qed.

(* lower bound: [1/n <= collide] (nonempty; 1/n == n/n^2 by normalization,
   numerator by [sqsum_ge_length]) *)
Theorem collide_lower : forall l : list Q,
  (0 < length l)%nat -> QleT' (1 / qn (length l)) (collide l).
Proof.
  intros l Hl. apply Qle_to_QleT'. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold collide.
    pose proof (QltT_to_Qlt _ _ (qlen_mul_pos x xs)) as HPP.
    assert (HP2 : ~ (qn (length (x :: xs)) * qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 _ HPP (qeq_imp_qeqT _ _ Hc)). }
    assert (HP1 : ~ (qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 (qn (length (x :: xs)))
        (QltT_to_Qlt 0 (qn (length (x :: xs)))
          (qn_pos (length (x :: xs)) (NatLe_drop 1 (length (x :: xs)) (qlen_pos x xs))))
        (qeq_imp_qeqT _ _ Hc)). }
    assert (Hge : (length (x :: xs) <= sqsum (x :: xs))%nat)
      by (apply NatLe_drop; apply sqsum_ge_length).
    assert (Hnum : qn (length (x :: xs)) <= qn (sqsum (x :: xs)))
      by (apply QleT'_to_Qle; apply qn_le; exact Hge).
    rewrite (qeqT_imp_qeq _ _
      (qdiv_norm (qn (length (x :: xs))) HP1 HP2)).
    apply QleT'_to_Qle. apply qdiv_ge_num.
    + exact HPP.
    + exact Hnum.
Qed.

(* permutation invariance (by [sqsum_perm] and [Permutation_length]) *)
Theorem collide_perm : forall l p : list Q,
  Permutation l p -> QeqT (collide l) (collide p).
Proof.
  intros l p H. apply qeq_imp_qeqT. unfold collide.
  destruct (id_sym (sqsum_perm l p H)).
  rewrite (Permutation_length H). reflexivity.
Qed.

(* ========== [maxfreq]: normalized maximum frequency, closing the order
   chain (main theorem) ========== *)

Definition maxcount (l : list Q) : nat := nmax (fun x => freq_q x l) l.

Definition maxfreq (l : list Q) : Q := qn (maxcount l) / qn (length l).

(* main theorem, the order chain [collide <= maxfreq]:
   nat side [sqsum <= n * maxcount] (pointwise, from the sum bound and
   [nmax_bound]), Q side same-denominator monotonicity plus in-context
   normalization (the field side condition discharged from the context) *)
Theorem collide_le_maxfreq : forall l : list Q, QleT' (collide l) (maxfreq l).
Proof.
  intros l. destruct l as [| x xs].
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ collide_zero).
    assert (Hz : maxfreq [] == 0)
      by (unfold maxfreq; apply qeqT_imp_qeq; apply qdiv_zero_num;
         reflexivity).
    rewrite Hz. apply Qle_refl.
  - unfold collide, maxfreq.
    pose proof (QltT_to_Qlt _ _ (qlen_mul_pos x xs)) as HPP.
    pose proof (qpos_neq0 _ HPP) as HP2.
    assert (HP1 : ~ (qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 (qn (length (x :: xs)))
        (QltT_to_Qlt 0 (qn (length (x :: xs)))
          (qn_pos (length (x :: xs)) (NatLe_drop 1 (length (x :: xs)) (qlen_pos x xs))))
        (qeq_imp_qeqT _ _ Hc)). }
    assert (Hnat : (sqsum (x :: xs)
                    <= length (x :: xs) * maxcount (x :: xs))%nat).
    { unfold sqsum, maxcount. apply NatLe_drop. apply nsum_bound.
      intros x0 Hx0. apply NatLe_drop.
      exact (nmax_bound (fun x0 => freq_q x0 (x :: xs)) (x :: xs) x0 Hx0). }
    assert (HQ : qn (sqsum (x :: xs))
                 <= qn (length (x :: xs)) * qn (maxcount (x :: xs))).
    { rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs))
                         (maxcount (x :: xs)))).
      apply QleT'_to_Qle. apply qn_le. exact Hnat. }
    assert (HA : qn (sqsum (x :: xs)) / (qn (length (x :: xs)) * qn (length (x :: xs)))
                 <= (qn (length (x :: xs)) * qn (maxcount (x :: xs)))
                    / (qn (length (x :: xs)) * qn (length (x :: xs)))).
    { apply QleT'_to_Qle. apply qdiv_ge_num.
      - exact HPP.
      - exact HQ. }
    assert (HB : (qn (length (x :: xs)) * qn (maxcount (x :: xs)))
                 / (qn (length (x :: xs)) * qn (length (x :: xs)))
                 == qn (maxcount (x :: xs)) / qn (length (x :: xs))).
    { field; assumption. }
    exact (Qle_to_QleT' _ _
      (Qle_trans _ _ _ HA (QleT'_to_Qle _ _ (qeq_le_l _ _ HB)))).
Qed.

(* lower bound: [1/n <= maxfreq] (nonempty; [maxcount >= 1] since every
   member has frequency >= 1) *)
Theorem maxfreq_lower : forall l : list Q,
  (0 < length l)%nat -> QleT' (1 / qn (length l)) (maxfreq l).
Proof.
  intros l Hl. apply Qle_to_QleT'. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold maxfreq.
    assert (Hge : (1 <= maxcount (x :: xs))%nat).
    { pose proof (NatLe_drop _ _
          (freq_q_ge1 x (x :: xs) (or_introl eq_refl))) as H1.
      assert (Hb : (freq_q x (x :: xs) <= maxcount (x :: xs))%nat).
      { unfold maxcount.
        exact (NatLe_drop _ _
                 (nmax_bound (fun x0 => freq_q x0 (x :: xs)) (x :: xs) x
                    (or_introl eq_refl))). }
      lia. }
    apply QleT'_to_Qle. apply qdiv_ge_num.
    + apply QltT_to_Qlt. apply qn_pos. apply NatLe_drop. apply qlen_pos.
    + assert (Hq1 : qn 1 == (1:Q)) by reflexivity.
      rewrite <- Hq1. exact (QleT'_to_Qle _ _ (qn_le 1 (maxcount (x :: xs)) Hge)).
Qed.

(* upper bound: [maxfreq <= 1] (whole list; [maxcount <= length] pointwise
   from [nmax_le_bound]) *)
Theorem maxfreq_upper : forall l : list Q, QleT' (maxfreq l) (1).
Proof.
  intros l. destruct l as [| x xs].
  - apply Qle_to_QleT'. assert (Hz : maxfreq [] == 0)
      by (unfold maxfreq; apply qeqT_imp_qeq; apply qdiv_zero_num; reflexivity).
    rewrite Hz. apply (Qlt_le_weak 0 1). reflexivity.
  - unfold maxfreq. apply qdiv_le_1.
    + assert (Hb : (maxcount (x :: xs) <= length (x :: xs))%nat).
      { unfold maxcount. apply NatLe_drop. apply nmax_le_bound.
        intros y Hy. apply NatLe_drop. apply freq_q_le_length. }
      apply (QleT'_to_Qle _ _ (qn_le (maxcount (x :: xs)) (length (x :: xs)) Hb)).
    + apply QltT_to_Qlt. apply qn_pos. apply NatLe_drop. apply qlen_pos.
Qed.

(* degenerate form: all values equal implies [maxfreq] takes 1
   ([maxcount == length], squeezed from both sides) *)
Theorem maxfreq_all_same_one : forall l : list Q,
  all_same l -> (0 < length l)%nat -> QeqT (maxfreq l) 1.
Proof.
  intros l Hs Hl. apply qeq_imp_qeqT. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold maxfreq.
    assert (Hmc : (maxcount (x :: xs) = length (x :: xs))%nat).
    { unfold maxcount. apply Nat.le_antisymm.
      - apply NatLe_drop. apply nmax_le_bound.
        intros y Hy. apply NatLe_drop. apply freq_q_le_length.
      - apply (Nat.le_trans (length (x :: xs)) (freq_q x (x :: xs))
                 (nmax (fun x0 => freq_q x0 (x :: xs)) (x :: xs))).
        + destruct (id_sym (freq_q_eq_all x (x :: xs)
                        (fun z Hz => qeqT_imp_qeq _ _
                           (Hs z x Hz (or_introl eq_refl))))).
          apply Nat.le_refl.
        + exact (NatLe_drop _ _
                   (nmax_bound (fun x0 => freq_q x0 (x :: xs)) (x :: xs) x
                      (or_introl eq_refl))). }
    rewrite Hmc.
    assert (HPne : ~ (qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 (qn (length (x :: xs)))
        (QltT_to_Qlt 0 (qn (length (x :: xs)))
          (qn_pos (length (x :: xs)) (NatLe_drop 1 (length (x :: xs)) (qlen_pos x xs))))
        (qeq_imp_qeqT _ _ Hc)). }
    field; assumption.
Qed.

(* [maxcount] is permutation invariant ([nmax_ext_in] pointwise bridge
   plus [nmax_perm]) *)
Theorem maxcount_perm : forall l p : list Q,
  Permutation l p -> Id (maxcount l) (maxcount p).
Proof.
  intros l p H. unfold maxcount.
  assert (Hex : forall x, In x l -> freq_q x l = freq_q x p).
  { intros x _. destruct (freq_q_perm x l p H). reflexivity. }
  destruct (id_sym (nmax_ext_in (fun x => freq_q x l)
              (fun x => freq_q x p) l Hex)).
  exact (nmax_perm (fun x => freq_q x p) l p H).
Qed.

(* [maxfreq] is permutation invariant *)
Theorem maxfreq_perm : forall l p : list Q,
  Permutation l p -> QeqT (maxfreq l) (maxfreq p).
Proof.
  intros l p H. apply qeq_imp_qeqT. unfold maxfreq.
  destruct (id_sym (maxcount_perm l p H)).
  rewrite (Permutation_length H). reflexivity.
Qed.

(* order chain read together: for nonempty l,
   [1/n <= collide <= maxfreq <= 1], all three members in one chain *)
Theorem H_chain : forall l : list Q, (0 < length l)%nat ->
  And (QleT' (1 / qn (length l)) (collide l))
      (And (QleT' (collide l) (maxfreq l)) (QleT' (maxfreq l) 1)).
Proof.
  intros l Hl. split.
  - apply collide_lower. exact Hl.
  - split.
    + apply collide_le_maxfreq.
    + apply maxfreq_upper.
Qed.

(* ========== [H_max_q] / [H_min_q]: the complement rational surrogates of
   the entropy family ========== *)

Definition H_max_q (l : list Q) : Q := 1 - maxfreq l.

Definition H_min_q (l : list Q) : Q := 1 - collide l.

(* monotonicity: the larger [maxfreq], the smaller [H_max_q] (via the
   order-reversing [qsub_le] bridge) *)
Theorem H_max_q_anti : forall l p : list Q,
  maxfreq l <= maxfreq p -> QleT' (H_max_q p) (H_max_q l).
Proof.
  intros l p H. unfold H_max_q. exact (qsub_le (maxfreq l) (maxfreq p) 1 H).
Qed.

Theorem H_max_q_nonneg : forall l : list Q, QleT' 0 (H_max_q l).
Proof.
  intros l. unfold H_max_q. exact (fst (Qle_0_sub' (maxfreq l) 1) (maxfreq_upper l)).
Qed.

Theorem H_max_q_le_one : forall l : list Q, QleT' (H_max_q l) 1.
Proof.
  intros l. apply Qle_to_QleT'. unfold H_max_q.
  assert (H0 : 0 <= maxfreq l).
  { destruct l as [| x xs].
    - assert (Hz : maxfreq [] == 0)
        by (unfold maxfreq; apply qeqT_imp_qeq; apply qdiv_zero_num;
           reflexivity).
      rewrite Hz. apply Qle_refl.
    - unfold maxfreq. apply QleT'_to_Qle. apply qdiv_nonneg.
      + apply QleT'_to_Qle. apply qn_nonneg.
      + apply QltT_to_Qlt. apply qn_pos. apply NatLe_drop. apply qlen_pos. }
  apply (Qle_trans (1 - maxfreq l) (1 - 0) 1).
  - apply QleT'_to_Qle. apply qsub_le. exact H0.
  - assert (Hz : (1:Q) - 0 == 1) by reflexivity.
    rewrite Hz. apply Qle_refl.
Qed.

(* coupling with the lower bound: [H_max_q l <= 1 - 1/n] (nonempty) *)
Theorem H_max_q_le_inv : forall l : list Q, (0 < length l)%nat ->
  QleT' (H_max_q l) (1 - 1 / qn (length l)).
Proof.
  intros l Hl. unfold H_max_q.
  exact (qsub_le (1 / qn (length l)) (maxfreq l) 1
    (QleT'_to_Qle _ _ (maxfreq_lower l Hl))).
Qed.

Theorem H_min_q_nonneg : forall l : list Q, QleT' 0 (H_min_q l).
Proof.
  intros l. unfold H_min_q. exact (fst (Qle_0_sub' (collide l) 1) (collide_upper l)).
Qed.

Theorem H_min_q_le_one : forall l : list Q, QleT' (H_min_q l) 1.
Proof.
  intros l. apply Qle_to_QleT'. unfold H_min_q.
  assert (Hc : 0 <= collide l).
  { destruct l as [| x xs].
    - rewrite (qeqT_imp_qeq _ _ collide_zero). apply Qle_refl.
    - unfold collide. apply QleT'_to_Qle. apply qdiv_nonneg.
      + apply QleT'_to_Qle. apply qn_nonneg.
      + apply QltT_to_Qlt. apply qlen_mul_pos. }
  apply (Qle_trans (1 - collide l) (1 - 0) 1).
  - apply QleT'_to_Qle. apply qsub_le. exact Hc.
  - assert (Hz : (1:Q) - 0 == 1) by reflexivity.
    rewrite Hz. apply Qle_refl.
Qed.

(* internal coherence bridge of the entropy family:
   [H_freq == 1 - collide] (nonempty; direct from the definitions, closed
   by field reasoning) *)
Theorem H_freq_eq_bridge : forall l : list Q,
  (0 < length l)%nat -> QeqT (H_freq l) (H_min_q l).
Proof.
  intros l Hl. apply qeq_imp_qeqT. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold H_freq, H_min_q, collide.
    assert (HP1 : ~ (qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 (qn (length (x :: xs)))
        (QltT_to_Qlt 0 (qn (length (x :: xs)))
          (qn_pos (length (x :: xs)) (NatLe_drop 1 (length (x :: xs)) (qlen_pos x xs))))
        (qeq_imp_qeqT _ _ Hc)). }
    pose proof (QltT_to_Qlt _ _ (qlen_mul_pos x xs)) as HPP.
    assert (HP2 : ~ (qn (length (x :: xs)) * qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 _ HPP (qeq_imp_qeqT _ _ Hc)). }
    field; assumption.
Qed.

(* degenerate form: all values equal implies [H_max_q] takes 0 (dual of the
   all-equal vanishing of [H_freq]) *)
Theorem H_max_q_all_same_zero : forall l : list Q,
  all_same l -> (0 < length l)%nat -> QeqT (H_max_q l) 0.
Proof.
  intros l Hs Hl. apply qeq_imp_qeqT. unfold H_max_q.
  assert (H1 : maxfreq l == 1) by (apply qeqT_imp_qeq; apply maxfreq_all_same_one; assumption).
  rewrite H1. reflexivity.
Qed.

(* ========== permutation-invariance closure (bonus) ========== *)

Theorem H_min_q_perm : forall l p : list Q,
  Permutation l p -> QeqT (H_min_q l) (H_min_q p).
Proof.
  intros l p H. apply qeq_imp_qeqT. unfold H_min_q.
  rewrite (qeqT_imp_qeq _ _ (collide_perm l p H)). reflexivity.
Qed.

Theorem H_max_q_perm : forall l p : list Q,
  Permutation l p -> QeqT (H_max_q l) (H_max_q p).
Proof.
  intros l p H. apply qeq_imp_qeqT. unfold H_max_q.
  rewrite (qeqT_imp_qeq _ _ (maxfreq_perm l p H)). reflexivity.
Qed.


(* ============================================================
   Coherence of the [MultiEntropyEval] record: local tools (abs triangle /
   aggregate weights / dedup counting), the five-field definitional
   equations, the joint coherence certificate [me_cert], suite-level lifts
   and cross-field bridges, and the [me_total] aggregate.
   ============================================================ *)

(* ============================================================
   The [MultiEntropyEval] coherence suite: from a data bundle to a
   self-certifying record.
   Basis (reused, no new premises): [mkMEval]/[mkMEval_eta],
   [H_shannon_q_nonneg], [xq_H_adj_nonneg], [H_shannon_q_count_ub],
   [H_adj_P0_min], [H_cond_nonneg_guarded], [mkMEval_Hms1_Hsh0],
   [xq_Zlen_nonneg], [xq_Qle_bool_le], [qadd_nonneg], [H_ms], [gate_pass],
   [Qle_dec'], [abs_eq], [abs_neg], [Qle_0_sub'], [qmul_le_r], [qadd_le],
   [qsub], and stdlib [Qle_trans]/[Qle_refl]/[ring]/[lia].
   Layered delivery:
   - baseline: the five field equations, one by one (composed from
     [mkMEval_eta], no re-proofs)
   - main theorem: [me_cert] — carrier agreement + the four entropy
     equalities + nonnegativity of Hadj/Hsh + the counting upper bound on
     Hsh + the triangle bound on Hcond, a nine-way joint coherence
     conjunction ([me_coherent], certified by the construction [mkMEval])
   - main piece: suite-level lifts, the contrapositive bridge
     [H_ms == 1 -> Hsh == 0], the triangle/counting certificate forms of
     |me_Hcond|, and the two-gate bridge ([H_cond_abs_bound] is not
     available here and is not used)
   - bonus: the equal-weight aggregate [me_total] with guarded
     nonnegativity and a twofold Shannon upper bound
   ============================================================ *)

(* ============================================================
   Local tools (abs triangle / aggregate weights / dedup counting)
   ============================================================ *)

(* abs triangle for nonnegative differences:
   0 <= a -> 0 <= b -> |a - b| <= a + b
   (case split by [Qle_dec'], then [abs_eq]/[abs_neg]; each branch
   rearranged by [Qle_0_sub']) *)
Lemma me2_abs_sub_triangle : forall a b : Q,
  (0 <= a)%Q -> (0 <= b)%Q -> QleT' (Qabs (a - b)) (a + b).
Proof.
  intros a b Ha Hb.
  apply Qle_to_QleT'.
  destruct (Qle_dec' a b) as [Hab | Hba].
  - (* branch a <= b: |a-b| = -(a-b) = b-a, via (a+b)-(b-a) = 2a >= 0 *)
    assert (Hneg : (a - b <= 0)%Q).
    { apply QleT'_to_Qle. apply (snd (Qle_0_sub' (a - b) 0)).
      apply Qle_to_QleT'.
      assert (Hr : (0 - (a - b))%Q == b - a) by ring.
      rewrite Hr. exact (QleT'_to_Qle _ _ (fst (Qle_0_sub' a b) Hab)). }
    rewrite (qeqT_imp_qeq _ _ (abs_neg (a - b) Hneg)).
    assert (Heq : (- (a - b))%Q == b - a) by ring.
    rewrite Heq.
    apply QleT'_to_Qle. apply (snd (Qle_0_sub' (b - a) (a + b))).
    apply Qle_to_QleT'.
    assert (Hr2 : ((a + b) - (b - a))%Q == a + a) by ring.
    rewrite Hr2. apply QleT'_to_Qle. apply qadd_nonneg; exact Ha.
  - (* branch b <= a: |a-b| = a-b, via (a+b)-(a-b) = 2b >= 0 *)
    assert (Hpos : (0 <= a - b)%Q).
    { apply QleT'_to_Qle. apply (fst (Qle_0_sub' b a)). exact Hba. }
    rewrite (qeqT_imp_qeq _ _ (abs_eq (a - b) Hpos)).
    apply QleT'_to_Qle. apply (snd (Qle_0_sub' (a - b) (a + b))).
    apply Qle_to_QleT'.
    assert (Hr3 : ((a + b) - (a - b))%Q == b + b) by ring.
    rewrite Hr3. apply QleT'_to_Qle. apply qadd_nonneg; exact Hb.
Qed.

(* the aggregate weight 1/4 is nonnegative (literal Qle_bool computation) *)
Lemma me2_weight_nonneg : QleT' (0) ((1 # 4)%Q).
Proof. apply Qle_to_QleT'.
  change (Z.le (0 * 4) (1 * 1))%Z.
  lia.
Qed.

(* the dedup count of a nonempty list is >= 1 *)
Lemma me2_dedup_len_ge1 : forall l : list Q,
  l <> [] -> NatLe (1) ((length (dedup l))%nat).
Proof.
  intros [| x xs] H.
  apply NatLe_lift.
  - exfalso. apply H. reflexivity.
  - cbn [dedup length]. reflexivity.
Qed.

(* ============================================================
   Baseline: the five field equations, one by one (reusing [mkMEval_eta],
   no re-proofs)
   ============================================================ *)

Theorem me2_carrier_eq : forall (l ctx : list Q), Id (me_carrier (mkMEval l ctx)) (l).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [Hc _]. exact Hc.
Qed.

Theorem me2_Hadj_eq : forall (l ctx : list Q), QeqT (me_Hadj (mkMEval l ctx)) (H_adj l).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [Ha _]]. exact Ha.
Qed.

Theorem me2_Hms_eq : forall (l ctx : list Q),
  QeqT (me_Hms (mkMEval l ctx)) (H_ms l).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [_ [Hm _]]]. exact Hm.
Qed.

Theorem me2_Hsh_eq : forall (l ctx : list Q), QeqT (me_Hsh (mkMEval l ctx)) (H_devsum l).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [_ [_ [Hs _]]]]. exact Hs.
Qed.

Theorem me2_Hcond_eq : forall (l ctx : list Q), QeqT (me_Hcond (mkMEval l ctx)) (H_cond l ctx).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [_ [_ [_ Hc]]]]. exact Hc.
Qed.

(* ============================================================
   Main theorem: [me_cert] — the self-certifying record of [mkMEval]
   (nine-way joint coherence conjunction: carrier agreement + the four
   entropy equalities + nonnegativity of Hadj/Hsh + the counting upper
   bound on Hsh + the triangle bound on Hcond)
   ============================================================ *)

Definition me_coherent (m : MultiEntropyEval) (l ctx : list Q) : Set :=
  And (Id (me_carrier m) l)
  (And (QeqT (me_Hadj m) (H_adj l))
  (And (QeqT (me_Hms m) (H_ms l))
  (And (QeqT (me_Hsh m) (H_devsum l))
  (And (QeqT (me_Hcond m) (H_cond l ctx))
  (And (QleT' 0 (me_Hadj m))
  (And (QleT' 0 (me_Hsh m))
  (And (QleT' (me_Hsh m) (me_Hadj m * (Z.of_nat (length (me_carrier m)) # 1)))
       (QleT' (Qabs (me_Hcond m)) (me_Hsh m + H_devsum ctx))))))))).

Theorem me_cert : forall (l ctx : list Q),
  me_coherent (mkMEval l ctx) l ctx.
Proof.
  intros l ctx.
  destruct (mkMEval_eta l ctx) as [Hc [Ha [Hm [Hs Hcond]]]].
  (* [repeat split] closes the first five definitional conjuncts (carrier
   equality + four Qeq; Z.eq is a Prop-level single constructor, solvable
   by eq_refl after projection delta reduction); the remaining four Qle
   coherence conjuncts reuse the baseline lemmas one by one *)
  unfold me_coherent, And. repeat split.
  - exact Ha.
  - exact Hm.
  - exact Hs.
  - exact Hcond.
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ Ha).
    apply QleT'_to_Qle. apply xq_H_adj_nonneg.
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ Hs).
    apply QleT'_to_Qle. apply H_shannon_q_nonneg.
  - apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ Hs), (qeqT_imp_qeq _ _ Ha).
    destruct (id_sym Hc).
    exact (QleT'_to_Qle _ _ (H_shannon_q_count_ub l)).
  - apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ Hcond), (qeqT_imp_qeq _ _ Hs).
    unfold H_cond.
    apply QleT'_to_Qle. apply me2_abs_sub_triangle;
      apply QleT'_to_Qle, H_shannon_q_nonneg.
Qed.

(* ============================================================
   Main piece: suite-level lifts and cross-field bridges (certificate
   forms)
   ============================================================ *)

(* lift of P0 minimality: [H_adj (P0 carrier)] <= [me_Hadj] *)
Theorem mkMEval_Hadj_min : forall (l ctx : list Q),
  QleT' (H_adj (P0 (me_carrier (mkMEval l ctx)))) (me_Hadj (mkMEval l ctx)).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [Hc [Ha _]].
  apply Qle_to_QleT'.
  destruct (id_sym Hc).
  rewrite (qeqT_imp_qeq _ _ Ha).
  exact (QleT'_to_Qle _ _ (H_adj_P0_min l)).
Qed.

(* nonnegativity of the Shannon field *)
Theorem mkMEval_Hsh_nonneg : forall (l ctx : list Q),
  QleT' 0 (me_Hsh (mkMEval l ctx)).
Proof.
  intros l ctx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hsh_eq l ctx)).
  exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l)).
Qed.

(* counting upper bound of the Shannon field ([H_adj] times the length
   factor) *)
Theorem mkMEval_Hsh_ub : forall (l ctx : list Q),
  QleT' (me_Hsh (mkMEval l ctx))
        (me_Hadj (mkMEval l ctx) * (Z.of_nat (length l) # 1)).
Proof.
  intros l ctx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hsh_eq l ctx)),
          (qeqT_imp_qeq _ _ (me2_Hadj_eq l ctx)).
  exact (QleT'_to_Qle _ _ (H_shannon_q_count_ub l)).
Qed.

(* nonempty lower bound of the multiset entropy: a nonempty carrier gives
   [1 <= me_Hms] (Z bridge) *)
Theorem mkMEval_Hms_ge1 : forall (l ctx : list Q),
  l <> [] -> QleT' 1 (me_Hms (mkMEval l ctx)).
Proof.
  intros l ctx Hl. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hms_eq l ctx)). unfold H_ms.
  assert (Hn : (1 <= length (dedup l))%nat)
    by (apply NatLe_drop; apply me2_dedup_len_ge1; exact Hl).
  assert (Hz : (1 <= Z.of_nat (length (dedup l)))%Z) by lia.
  unfold Qle. cbn [Qnum Qden]. lia.  (* the record field's true name is lowercase [Qden] *)
Qed.

(* negative-side bound of the conditional entropy:
   [-H_sh ctx <= me_Hcond] (rearranged [H_shannon_q_nonneg]) *)
Theorem mkMEval_Hcond_lb : forall (l ctx : list Q),
  QleT' (- H_devsum ctx) (me_Hcond (mkMEval l ctx)).
Proof.
  intros l ctx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hcond_eq l ctx)). unfold H_cond.
  apply QleT'_to_Qle. apply (snd (Qle_0_sub' (- H_devsum ctx)
                           (H_devsum l - H_devsum ctx))).
  apply Qle_to_QleT'.
  assert (Hr : (H_devsum l - H_devsum ctx) - (- H_devsum ctx)
               == H_devsum l) by ring.
  rewrite Hr. exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l)).
Qed.

(* both gates use the same Qle_bool: the low-entropy gate equals
   [gate_pass] (across the two definitions) *)
Theorem mkMEval_gate_bridge : forall (l ctx : list Q) (t : Q), Id (gate_low_entropy (me_Hsh (mkMEval l ctx)) t) (gate_pass t (H_devsum l)).
Proof.
  intros l ctx t. apply eq_imp_id. unfold gate_low_entropy, gate_pass, mkMEval.
  cbn [me_Hsh]. destruct (Qle_bool (H_devsum l) t); reflexivity.
Qed.

(* cross-field bridge, certificate form: the contrapositive of
   [H_ms == 1 -> Hsh == 0] (reusing [mkMEval_Hms1_Hsh0], no re-proof) *)
Theorem mkMEval_notHsh0_notHms1 : forall (l ctx : list Q),
  ~ (me_Hsh (mkMEval l ctx) == 0)%Q -> Not (QeqT (me_Hms (mkMEval l ctx)) 1).
Proof.
  intros l ctx H0 Hms1. apply qeqT_imp_qeq in Hms1.
  exact (False_rect Empty_set
    (H0 (qeqT_imp_qeq _ _ (mkMEval_Hms1_Hsh0 l ctx Hms1)))).
Qed.

(* triangle bound, certificate form:
   [|me_Hcond| <= me_Hsh + H_sh ctx] (composed from lemmas of this file;
   the abs-bound lemma of the zero-locus suite is not available here and
   is not used) *)
Theorem mkMEval_Hcond_abs_ub : forall (l ctx : list Q),
  QleT' (Qabs (me_Hcond (mkMEval l ctx)))
        (me_Hsh (mkMEval l ctx) + H_devsum ctx).
Proof.
  intros l ctx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hcond_eq l ctx)),
          (qeqT_imp_qeq _ _ (me2_Hsh_eq l ctx)). unfold H_cond.
  apply QleT'_to_Qle. apply me2_abs_sub_triangle;
    [ exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l))
    | exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg ctx)) ].
Qed.

(* counting bound, certificate form:
   [|me_Hcond| <= me_Hadj * n_l + H_adj ctx * n_ctx]
   (the triangle bound combined with [H_shannon_q_count_ub] on both arms) *)
Theorem mkMEval_Hcond_count_ub : forall (l ctx : list Q), QleT' (Qabs (me_Hcond (mkMEval l ctx))) (me_Hadj (mkMEval l ctx) * (Z.of_nat (length l) # 1)
       + H_adj ctx * (Z.of_nat (length ctx) # 1)).
Proof.
  intros l ctx. pose proof (mkMEval_eta l ctx) as Heta.
  destruct Heta as [Hc Hr1]. destruct Hr1 as [Ha Hr2].
  destruct Hr2 as [Hm Hr3]. destruct Hr3 as [Hs Hcond].
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ Hcond), (qeqT_imp_qeq _ _ Ha).
  unfold H_cond.
  apply (Qle_trans _ (H_devsum l + H_devsum ctx)%Q).
  - apply QleT'_to_Qle. apply me2_abs_sub_triangle;
      [ exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l))
      | exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg ctx)) ].
  - apply QleT'_to_Qle. apply qadd_le.
    + exact (QleT'_to_Qle _ _ (H_shannon_q_count_ub l)).
    + exact (QleT'_to_Qle _ _ (H_shannon_q_count_ub ctx)).
Qed.

(* ============================================================
   Bonus: the aggregate [me_total] (equal weights 1/4) with guarded
   nonnegativity and a twofold upper bound
   ============================================================ *)

Definition me_total (m : MultiEntropyEval) : Q :=
  (1 # 4)%Q * (me_Hadj m + me_Hms m + me_Hsh m + me_Hcond m)%Q.

(* the aggregate's defining equations (definitional projections of
   [mkMEval]) *)
Theorem me_total_eq : forall (l ctx : list Q), QeqT (me_total (mkMEval l ctx)) ((1 # 4)%Q * (H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q).
Proof.
  intros l ctx.
  apply qeq_imp_qeqT.
  change (me_total (mkMEval l ctx))
    with ((1 # 4)%Q * (me_Hadj (mkMEval l ctx) + me_Hms (mkMEval l ctx)
          + me_Hsh (mkMEval l ctx) + me_Hcond (mkMEval l ctx))%Q).
  change (me_Hadj (mkMEval l ctx)) with (H_adj l).
  change (me_Hms (mkMEval l ctx)) with (H_ms l).
  change (me_Hsh (mkMEval l ctx)) with (H_devsum l).
  change (me_Hcond (mkMEval l ctx)) with (H_cond l ctx).
  reflexivity.
Qed.

(* guarded nonnegativity: [H_sh ctx <= H_sh l -> 0 <= me_total]
   (under the guard all four entropies are nonnegative; a chain of
   [qadd_nonneg] and [qmul_le_r]) *)
Theorem me_total_nonneg_guarded : forall (l ctx : list Q),
  (H_devsum ctx <= H_devsum l)%Q ->
  QleT' 0 (me_total (mkMEval l ctx)).
Proof.
  intros l ctx Hle. apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ (me_total_eq l ctx)).
  assert (Hc : (0 <= H_cond l ctx)%Q)
    by (apply QleT'_to_Qle; apply H_cond_nonneg_guarded; exact Hle).
  assert (Hms : (0 <= H_ms l)%Q)
    by (unfold H_ms; apply QleT'_to_Qle; apply xq_Zlen_nonneg).
  assert (Hsum : (0 <= H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q).
  { apply QleT'_to_Qle. apply qadd_nonneg.
    - apply QleT'_to_Qle. apply qadd_nonneg.
      + apply QleT'_to_Qle. apply qadd_nonneg;
          [ apply QleT'_to_Qle; apply xq_H_adj_nonneg | exact Hms ].
      + exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l)).
    - exact Hc. }
  exact (QleT'_to_Qle _ _ (xq_mul_nonneg ((1 # 4)%Q)
    ((H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q)
    (QleT'_to_Qle _ _ me2_weight_nonneg) Hsum)).
Qed.

(* aggregate upper bound: [me_total <= (1/4) * (H_adj + H_ms + 2 * H_sh)]
   (the negative side is exactly absorbed by [H_cond <= H_sh l], since
   [-H_sh ctx <= 0]) *)
Theorem me_total_ub : forall (l ctx : list Q), QleT' (me_total (mkMEval l ctx)) ((1 # 4)%Q * (H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q).
Proof.
  intros l ctx. apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ (me_total_eq l ctx)).
  assert (Hcc : (H_cond l ctx <= H_devsum l)%Q).
  { unfold H_cond. apply QleT'_to_Qle. apply (snd (Qle_0_sub' _ _)).
    apply Qle_to_QleT'.
    assert (Hr : H_devsum l - (H_devsum l - H_devsum ctx)
                 == H_devsum ctx) by ring.
    rewrite Hr. apply QleT'_to_Qle. apply H_shannon_q_nonneg. }
  assert (Hsub : (H_devsum l + H_cond l ctx
                  <= (2 # 1)%Q * H_devsum l)%Q).
  { assert (Hr2 : (2 # 1)%Q * H_devsum l
                  == H_devsum l + H_devsum l) by ring.
    rewrite Hr2. apply QleT'_to_Qle. apply qadd_le.
    - apply Qle_refl.
    - exact Hcc. }
  assert (Hassoc : (H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q
                   == (H_adj l + H_ms l + (H_devsum l + H_cond l ctx))%Q)
    by ring.
  rewrite Hassoc.
  assert (Hinner : (H_adj l + H_ms l + (H_devsum l + H_cond l ctx)
                    <= H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q).
  { apply QleT'_to_Qle. apply qadd_le.
    - apply Qle_refl.
    - exact Hsub. }
  (* [qmul_le_r] multiplies on the right and requires a common multiplier:
   rearrange both weighted sides to the right by ring *)
  assert (Hsw1 : (1 # 4)%Q
                   * (H_adj l + H_ms l + (H_devsum l + H_cond l ctx))%Q
               == (H_adj l + H_ms l + (H_devsum l + H_cond l ctx))%Q
                    * (1 # 4)%Q) by ring.
  assert (Hsw2 : (1 # 4)%Q
                   * (H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q
               == (H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q
                    * (1 # 4)%Q) by ring.
  rewrite Hsw1, Hsw2. apply QleT'_to_Qle. apply qmul_le_r.
  - exact Hinner.
  - exact (QleT'_to_Qle _ _ me2_weight_nonneg).
Qed.

(* ============================================================
   Zero-locus characterization of the placeholder Shannon deviation
   entropy [H_devsum]: tools, the main theorem (zero locus iff ascending
   list), the all-equal characterization of [H_ms == 1], the [H_cond]
   family, and the restricted positive forms of the counterexamples.
   ============================================================ *)

(* ============================================================
   Zero-locus characterization of the placeholder centroid-offset Shannon
   deviation entropy [H_devsum] (the termwise |x - suffix P0 minimum| sum):
   the zero locus is exactly the ascending lists ([SortedQ]).
   Content grading:
   main theorem [H_shannon_q_zero_iff_sorted] (forward = the existing
     [xq_H_shannon_sortQ]; backward proved here: a vanishing sum with
     termwise nonnegativity forces each term to zero, so the head equals
     the suffix P0 minimum at every step — ascending cons, with the new
     head-minimality lemma [xqz_sorted_hd_min])
   piece A [H_ms1_all_eq] / [H_ms1_iff_const] (characterizing [H_ms == 1]
     as all members equal; honest convention: [H_ms []] == 0 while all
     members of the empty list are vacuously equal, so the right side of
     the iff carries the [l <> []] guard)
   piece B [H_cond_nonneg_iff] / [H_cond_abs_bound] / [H_cond_zero_iff]
     (absolute-value bound: |H_cond| <= H_devsum l + H_devsum ctx)
   bonus [H_shannon_q_perm_inv_if_sorted] (the restricted positive form of
     the permutation counterexample: invariance holds when both sides are
     ascending), [zero_locus_joint] (the positive twin: double zero locus
     iff a nonempty constant list), and
     [zero_locus_contrast_sorted_not_const] (the [1;2] contrast anchor)
   Contrast with the true-frequency entropy: the placeholder [H_devsum] can
   vanish on lists with distinct values ([1;2] is a zero locus but not
   constant), while the zero locus of the true-frequency [H_freq] is
   exactly the constant lists; new names carry the [xqz_] prefix.
   ============================================================ *)

(* ========== tools: absolute-value zero, subtraction zero, and splitting a
   vanishing sum of nonnegative terms ========== *)

(* Qabs x == 0 -> x == 0 (direct case analysis on the Qnum encoding; the
   stdlib has no ready-made Qeq form) *)
Lemma xqz_abs0_eq : forall x : Q, Qabs x == 0 -> QeqT x 0.
Proof.
  intros [n d] H. apply qeq_imp_qeqT. unfold Qeq. destruct n as [| p | p].
  - reflexivity.
  - unfold Qabs in H. simpl in H. discriminate H.
  - unfold Qabs in H. simpl in H. discriminate H.
Qed.

(* x - y == 0 -> x == y (both directions of [Qle_0_sub'] plus
   antisymmetry; no setoid rewriting) *)
Lemma xqz_sub_eq0 : forall x y : Q, (x - y == 0)%Q -> QeqT x y.
Proof.
  intros x y H. apply qeq_imp_qeqT.
  assert (Hyx : (y - x == 0)%Q).
  { assert (Hmo : y - x == - (x - y)) by (apply qeqT_imp_qeq; apply xq_minus_opp).
    rewrite Hmo, H. reflexivity. }
  apply qeqT_imp_qeq. apply (xq_Qle_antisym x y).
  - apply QleT'_to_Qle. apply (snd (Qle_0_sub' x y)).
    apply xq_Qeq_le. apply Qeq_sym. exact Hyx.
  - apply QleT'_to_Qle. apply (snd (Qle_0_sub' y x)).
    apply xq_Qeq_le. apply Qeq_sym. exact H.
Qed.

(* a vanishing sum of two nonnegative terms forces the first term to zero
   (squeezed between a <= a+b == 0 and 0 <= a) *)
Lemma xqz_plus_eq0_le : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> QeqT a 0.
Proof.
  intros a b Hab Ha Hb. apply qeq_imp_qeqT.
  assert (Hle : QleT' (a + 0) (a + b))
    by (apply qadd_le; [apply Qle_refl | exact Hb]).
  assert (Hle' : a <= 0).
  { apply QleT'_to_Qle in Hle. rewrite Hab in Hle.
    rewrite Qplus_0_r in Hle. exact Hle. }
  apply qeqT_imp_qeq. exact (xq_Qle_antisym a 0 Hle' Ha).
Qed.

(* a vanishing sum of two nonnegative terms forces both terms to zero
   (commute and reuse) *)
Lemma xqz_plus_eq0 : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> And (QeqT a 0) (QeqT b 0).
Proof.
  intros a b Hab Ha Hb. split.
  - exact (xqz_plus_eq0_le a b Hab Ha Hb).
  - rewrite Qplus_comm in Hab.
    exact (xqz_plus_eq0_le b a Hab Hb Ha).
Qed.

(* ========== main theorem: the zero locus of [H_devsum] = the ascending
   lists ========== *)

(* head minimality: the head of an ascending list does not exceed any
   member *)
Lemma xqz_sorted_hd_min : forall (l : list Q) (z : Q),
  SortedQ l -> In z l -> QleT' (hd 0 l) (z).
Proof.
  intros [| a rest] z HS Hin.
  - apply Qle_to_QleT'. destruct Hin.
  - apply Qle_to_QleT'.
    destruct HS as [| c1 c2 HSr HFa].
    * destruct Hin.
    * subst.
      rewrite Forall_forall in HFa.
      change (hd 0 (a :: rest)) with a.
      destruct Hin as [Heq | Hin].
      { subst. apply Qle_refl. }
      { apply HFa. exact Hin. }
Qed.

(* the head of the P0 normal form is a lower bound of the whole list
   (membership transported through the permutation) *)
Lemma xqz_P0_hd_min_all : forall (l : list Q) (z : Q),
  In z l -> QleT' (hd 0 (P0 l)) (z).
Proof.
  intros l z Hin.
  apply (xqz_sorted_hd_min (P0 l) z).
  - apply xq_P0_sorted.
  - apply Permutation_in with (l := l).
    + apply D5_P0_perm.
    + exact Hin.
Qed.

(* backward direction of the main theorem: a vanishing placeholder entropy
   implies ascending (peeling the |head difference| layer by layer, with
   induction) *)
Theorem H_shannon_q_zero_sorted : forall l : list Q,
  H_devsum l == 0 -> SortedQ l.
Proof.
  induction l as [| x xs IH]; intro H.
  - apply sortQ_nil.
  - cbn [H_devsum] in H.
    destruct (xqz_plus_eq0
                (Qabs (x - hd 0 (P0 (x :: xs)))) (H_devsum xs) H
                (QleT'_to_Qle _ _ (abs_nonneg (x - hd 0 (P0 (x :: xs)))))
                (QleT'_to_Qle _ _ (H_shannon_q_nonneg xs))) as [Ha Hs].
    assert (Hxm : x == hd 0 (P0 (x :: xs))).
    { apply qeqT_imp_qeq. apply xqz_sub_eq0. apply qeqT_imp_qeq.
      apply xqz_abs0_eq. apply qeqT_imp_qeq. exact Ha. }
    apply sortQ_cons.
    + apply IH. apply qeqT_imp_qeq. exact Hs.
    + rewrite Forall_forall. intros z Hz.
      apply (Qle_trans x (hd 0 (P0 (x :: xs))) z).
      * apply QleT'_to_Qle. apply xq_Qeq_le. exact Hxm.
      * apply QleT'_to_Qle. apply xqz_P0_hd_min_all. simpl. right. exact Hz.
Qed.

(* main theorem: the zero locus of the placeholder Shannon deviation
   entropy = the ascending lists (forward = the existing
   [xq_H_shannon_sortQ]; contrast: the zero locus of the true-frequency
   entropy = the constant lists) *)
Theorem H_shannon_q_zero_iff_sorted : forall l : list Q,
  And (QeqT (H_devsum l) 0 -> SortedQ l) (SortedQ l -> QeqT (H_devsum l) 0).
Proof.
  intro l. split.
  - intro H. apply qeqT_imp_qeq in H.
    apply H_shannon_q_zero_sorted. exact H.
  - intro Hs. apply xq_H_shannon_sortQ. exact Hs.
Qed.

(* executable contrast anchor: [1;2] is ascending and a zero locus of the
   placeholder entropy, yet not a constant list — a constructive witness
   that the zero loci of the two entropies differ *)
Theorem zero_locus_contrast_sorted_not_const :
  And (SortedQ [1; 2]) (And (QeqT (H_devsum [1; 2]) 0)
    (Not (sigT (fun a : Q => Forall (fun z => z == a) [1; 2])))).
Proof.
  split.
  - apply (sortQ_cons 1 [2]).
    + apply (sortQ_cons 2 []).
      * apply sortQ_nil.
      * apply Forall_nil.
    + apply Forall_cons; [ unfold Qle; simpl; lia | apply Forall_nil ].
  - split.
    + apply qeq_imp_qeqT. vm_compute. reflexivity.
    + intros [a Hfa]. apply (False_rect Empty_set).
      inversion Hfa as [| z1 zs1 Hz1 Hf1]; subst.
      inversion Hf1 as [| z2 zs2 Hz2 Hf2]; subst.
      assert (H12 : (1 == 2)%Q)
        by (apply (Qeq_trans 1 a 2 Hz1 (Qeq_sym 2 a Hz2))).
      vm_compute in H12. discriminate H12.
Qed.

(* ========== piece A: the all-equal characterization of [H_ms == 1]
   ========== *)

(* elimination by [dedup_aux]: when every member equals x, the dedup
   collapses to the empty list (the Qmem convention, not via [In]) *)
Lemma xqz_dedup_aux_nil : forall (x : Q) (m : list Q),
  (forall z : Q, Qmem z m -> x == z) -> Id (dedup_aux x m) ([]).
Proof.
  intros x m. induction m as [| y ys IH]; intro Hall; apply eq_imp_id.
  - reflexivity.
  - cbn [dedup_aux].
    assert (HxyI : Id (Qeq_bool x y) true).
    { apply Qeqb_true_of. apply Hall. apply Qmem_refl_cons. }
    assert (Hxy : Qeq_bool x y = true)
      by (destruct (id_sym HxyI); reflexivity).
    rewrite Hxy.
    assert (Hall' : forall z : Q, Qmem z ys -> x == z).
    { intros z Hz. apply Hall. apply (snd (Qmem_cons _ _ _)). right.
      exact Hz. }
    destruct (IH Hall'). reflexivity.
Qed.

(* all-equal characterization: [H_ms l == 1] implies any two members are
   Qeq equal (structure of the dedup of length 1 and [dedup_Qmem_r]; no
   dependency on [In]) *)
Theorem H_ms1_all_eq : forall l : list Q,
  (H_ms l == 1)%Q -> forall a b : Q, Qmem a l -> Qmem b l -> QeqT (a) (b).
Proof.
  intro l. intro H. unfold H_ms in H.
  assert (HI : Id (length (dedup l)) 1%nat)
    by (apply (xq_Zlen_inj1 (length (dedup l))); exact H).
  assert (Hlen : length (dedup l) = 1%nat)
    by (destruct (id_sym HI); reflexivity).
  destruct (xq_len1_el (dedup l) Hlen) as [c Hc].
  intros a b Ha Hb.
  assert (Qa : Qmem a (dedup l)) by (apply dedup_Qmem_r; exact Ha).
  assert (Qb : Qmem b (dedup l)) by (apply dedup_Qmem_r; exact Hb).
  revert Qb. revert Qa. destruct (id_sym Hc). intros Qa Qb.
  destruct (Qmem_cons a c nil) as [Qapc _].
  assert (Qa1 : Or (Id (Qeq_bool a c) true) (Qmem a nil))
    by (apply Qapc; exact Qa).
  destruct (Qmem_cons b c nil) as [Qbpc _].
  assert (Qb1 : Or (Id (Qeq_bool b c) true) (Qmem b nil))
    by (apply Qbpc; exact Qb).
  destruct Qa1 as [QaL | QaR];
    [ | unfold Qmem in QaR; simpl in QaR; inversion QaR ].
  destruct Qb1 as [QbL | QbR];
    [ | unfold Qmem in QbR; simpl in QbR; inversion QbR ].
  apply qeq_imp_qeqT. apply Qeq_bool_eq.
  assert (Ea : Qeq_bool a c = true) by (destruct (id_sym QaL); reflexivity).
  assert (Eb : Qeq_bool b c = true) by (destruct (id_sym QbL); reflexivity).
  assert (Eb' : Qeq_bool c b = true)
    by (destruct (Qeqb_sym b c); exact Eb).
  destruct (Qeqb_trans a c b Ea Eb'). reflexivity.
Qed.

(* piece A: [H_ms == 1] iff the list is nonempty with all members Qeq equal
   (exists-Forall form) *)
Theorem H_ms1_iff_const : forall l : list Q,
  IffT (QeqT (H_ms l) 1)
       (And (l <> []) (sigT (fun a : Q => Forall (fun z => z == a) l))).
Proof.
  intro l. split.
  - intro H.
    assert (HlenI : Id (length (dedup l)) 1%nat)
      by (unfold H_ms in H; apply xq_Zlen_inj1;
         apply qeqT_imp_qeq; exact H).
    assert (Hlen : length (dedup l) = 1%nat)
      by (destruct (id_sym HlenI); reflexivity).
    destruct (xq_len1_el (dedup l) Hlen) as [c Hc].
    split.
    + intro He. rewrite He in Hc. simpl in Hc. inversion Hc.
    + apply (existT _ c). apply Forall_forall. intros z Hz.
      assert (HcE : dedup l = [c]) by (destruct (id_sym Hc); reflexivity).
      apply qeqT_imp_qeq. apply (xq_dedup1_all_eq l c HcE z Hz).
  - intros [Hne [a Hfa]].
    destruct l as [| x xs]; [ exfalso; apply Hne; reflexivity | ].
    apply qeq_imp_qeqT. unfold H_ms.
    inversion Hfa as [| z0 zs Hzx Hfxs]; subst.
    assert (HdI : Id (dedup_aux x (dedup xs)) []).
    { rewrite Forall_forall in Hfxs.
      apply xqz_dedup_aux_nil. intros z Hz.
      assert (Qxs : Qmem z xs) by (apply (dedup_Qmem_l xs z); exact Hz).
      assert (QxsE : existsb (fun y => Qeq_bool z y) xs = true)
        by (destruct (id_sym Qxs); reflexivity).
      apply existsb_exists in QxsE.
      destruct QxsE as [w [Hw Hzw]].
      apply (Qeq_trans x a z Hzx).
      apply (Qeq_sym z a).
      apply (Qeq_trans z w a (Qeq_bool_eq z w Hzw) (Hfxs w Hw)). }
    assert (Hd : dedup_aux x (dedup xs) = [])
      by (destruct (id_sym HdI); reflexivity).
    unfold H_ms. cbn [dedup length]. rewrite Hd. reflexivity.
Qed.

(* ========== piece B: the [H_cond] family (nonnegativity iff + absolute
   value bound + zero locus iff) ========== *)

(* the exact iff form of the failed unconditional nonnegativity: the
   missing premise is exactly [H_devsum ctx <= H_devsum l] (a two-way
   strengthening of the guarded version) *)
Theorem H_cond_nonneg_iff : forall l ctx : list Q,
  IffT (QleT' 0 (H_cond l ctx)) (QleT' (H_devsum ctx) (H_devsum l)).
Proof.
  intros l ctx. unfold H_cond. split.
  - intro H. apply (snd (Qle_0_sub' (H_devsum ctx) (H_devsum l))).
    exact H.
  - intro H. apply (fst (Qle_0_sub' (H_devsum ctx) (H_devsum l))).
    exact H.
Qed.

(* absolute-value bound ([Qabs_triangle]):
   |H_cond l ctx| <= H_devsum l + H_devsum ctx
   (both entropies are nonnegative, so the triangle sum is the conservative
   upper bound; the shape follows the actual definition of [H_cond]) *)
Theorem H_cond_abs_bound : forall l ctx : list Q, QleT' (Qabs (H_cond l ctx)) ((H_devsum l + H_devsum ctx)%Q).
Proof.
  intros l ctx. apply Qle_to_QleT'. unfold H_cond, Qminus.
  apply (Qle_trans _ (Qabs (H_devsum l) + Qabs (- H_devsum ctx))).
  - apply Qabs_triangle.
  - rewrite (qeqT_imp_qeq _ _ (xq_abs_id (H_devsum l)
               (QleT'_to_Qle _ _ (H_shannon_q_nonneg l)))).
    rewrite (qeqT_imp_qeq _ _ (xq_abs_opp (H_devsum ctx))).
    rewrite (qeqT_imp_qeq _ _ (xq_abs_id (H_devsum ctx)
               (QleT'_to_Qle _ _ (H_shannon_q_nonneg ctx)))).
    apply Qle_refl.
Qed.

(* zero locus of the conditional entropy:
   [H_cond l ctx == 0] iff the two placeholder entropies are equal *)
Theorem H_cond_zero_iff : forall l ctx : list Q,
  IffT (QeqT (H_cond l ctx) 0) (QeqT (H_devsum l) (H_devsum ctx)).
Proof.
  intros l ctx. unfold H_cond. split.
  - intro H. apply qeq_imp_qeqT.
    apply (Qeq_trans (H_devsum l)
                     (H_devsum l - H_devsum ctx + H_devsum ctx) (H_devsum ctx)).
    + ring.
    + pose proof (qeqT_imp_qeq _ _ H) as Hm.
      rewrite Hm at 1. apply Qplus_0_l.
  - intro H. apply qeq_imp_qeqT.
    rewrite <- (qeqT_imp_qeq _ _ H).
    apply (qeqT_imp_qeq _ _ (xq_minus_self (H_devsum l))).
Qed.

(* ========== bonus: turning the counterexamples into positive forms
   ========== *)

(* the restricted positive form of the permutation counterexample:
   invariance holds exactly under the both-ascending premise (the failure
   of [3;1;2] vs [2;1;3] comes from the permutation destroying the
   ascending order) *)
Theorem H_shannon_q_perm_inv_if_sorted : forall l p : list Q,
  Permutation l p -> SortedQ l -> SortedQ p -> QeqT (H_devsum l) (H_devsum p).
Proof.
  intros l p _Hp Hl Hpp.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (xq_H_shannon_sortQ l Hl)).
  rewrite (qeqT_imp_qeq _ _ (xq_H_shannon_sortQ p Hpp)).
  reflexivity.
Qed.

(* the positive twin: double zero locus (placeholder entropy zero and
   multiset entropy 1) iff a nonempty constant list (assembled from
   [H_shannon_q_const_zero] and [H_ms1_iff_const]) *)
Theorem zero_locus_joint : forall l : list Q,
  IffT (And (QeqT (H_devsum l) 0) (QeqT (H_ms l) 1))
       (And (l <> []) (sigT (fun a : Q => Forall (fun z => z == a) l))).
Proof.
  intro l. split.
  - intros [Hh Hm]. exact (fst (H_ms1_iff_const l) Hm).
  - intros [Hne [a Hfa]]. split.
    + apply (H_shannon_q_const_zero a l Hfa).
    + apply (snd (H_ms1_iff_const l)). split.
      * exact Hne.
      * apply (existT _ a). exact Hfa.
Qed.

(* ============================================================
   Monotonicity of the collision mass under concatenation, composed from
   lemmas already in this file: [freq_q_app] (additivity of frequencies
   under concatenation) with the [nsum] / [sqsum] / [nmax] tools.
   Baseline: [sqsum_app_ge_l] / [sqsum_app_ge_r]:
     [sqsum (l1 ++ l2) >= sqsum l1] (and on the right) — concatenation
     increases pointwise frequencies and enlarges the support, so the
     collision mass only grows.
   Bonus: [sqsum_app_eq], the exact cross-term decomposition
     [sqsum (l1 ++ l2) = sqsum l1 + sqsum l2
      + sum_{x in l1} freq_q x l2 + sum_{x in l2} freq_q x l1].
   Companions: [sqsum_app_ge_sum] (mass form) and
   [maxcount_app_ge_l] / [maxcount_app_ge_r] (frequency extremes, the
   shared numerators of collide/maxfreq).
   Honest obstacle, pinned by counterexamples: monotonicity FAILS for the
   normalized quotients [H_freq]/[collide] — H_freq ([0] ++ [1]) = 1/2 > 0
   = H_freq [0], and collide [0] = 1 > 1/2 = collide ([0] ++ [1]).  The
   reason: while the collision sum (numerator) grows, the denominator n^2
   grows with it, so the normalized quotient has no direction; closed
   faithfully as [H_freq_app_mono_false] / [collide_app_mono_false].
   ============================================================ *)

(* ---------- core: additivity of [nsum] under concatenation, and pointwise
   additivity ---------- *)

Lemma nsum_app : forall (f : Q -> nat) (l p : list Q), Id (nsum f (l ++ p)) ((nsum f l + nsum f p)%nat).
Proof.
  intros f l p. apply eq_imp_id. induction l as [| a l IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma nsum_add : forall (f g : Q -> nat) (l : list Q), Id (nsum (fun x => (f x + g x)%nat) l) ((nsum f l + nsum g l)%nat).
Proof.
  intros f g l. apply eq_imp_id. induction l as [| a l IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

(* ---------- baseline: the two concatenation-monotonicity lemmas for
   [sqsum] ---------- *)

Theorem sqsum_app_ge_l : forall l1 l2 : list Q, NatLe (sqsum l1) ((sqsum (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. unfold sqsum. rewrite nsum_app.
  assert (H1 : (nsum (fun x => freq_q x l1) l1
                <= nsum (fun x => freq_q x (l1 ++ l2)) l1)%nat).
  { apply NatLe_drop. apply nsum_le. intros x _.
    destruct (id_sym (freq_q_app x l1 l2)). lia. }
  lia.
Qed.

Theorem sqsum_app_ge_r : forall l1 l2 : list Q, NatLe (sqsum l2) ((sqsum (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. unfold sqsum. rewrite nsum_app.
  assert (H2 : (nsum (fun x => freq_q x l2) l2
                <= nsum (fun x => freq_q x (l1 ++ l2)) l2)%nat).
  { apply NatLe_drop. apply nsum_le. intros x _.
    destruct (id_sym (freq_q_app x l1 l2)). lia. }
  lia.
Qed.

(* ---------- bonus: the exact cross-term decomposition of [sqsum] under
   concatenation ---------- *)

Theorem sqsum_app_eq : forall l1 l2 : list Q, Id (sqsum (l1 ++ l2)) ((sqsum l1 + sqsum l2
   + nsum (fun x => freq_q x l2) l1
   + nsum (fun x => freq_q x l1) l2)%nat).
Proof.
  intros l1 l2. apply eq_imp_id. unfold sqsum. rewrite nsum_app.
  assert (Hext1 : forall x : Q, In x l1 ->
    freq_q x (l1 ++ l2) = (freq_q x l1 + freq_q x l2)%nat).
  { intros x _. destruct (id_sym (freq_q_app x l1 l2)). reflexivity. }
  assert (Hext2 : forall x : Q, In x l2 ->
    freq_q x (l1 ++ l2) = (freq_q x l1 + freq_q x l2)%nat).
  { intros x _. destruct (id_sym (freq_q_app x l1 l2)). reflexivity. }
  rewrite (nsum_ext_in (fun x => freq_q x (l1 ++ l2))
                       (fun x => (freq_q x l1 + freq_q x l2)%nat) l1 Hext1).
  rewrite (nsum_ext_in (fun x => freq_q x (l1 ++ l2))
                       (fun x => (freq_q x l1 + freq_q x l2)%nat) l2 Hext2).
  rewrite (nsum_add (fun x => freq_q x l1) (fun x => freq_q x l2) l1),
          (nsum_add (fun x => freq_q x l1) (fun x => freq_q x l2) l2).
  lia.
Qed.

(* companion mass form: the sum of the two segment collision masses does
   not exceed the collision mass of the concatenation (cross terms are
   nonnegative) *)
Corollary sqsum_app_ge_sum : forall l1 l2 : list Q, NatLe (sqsum l1 + sqsum l2) ((sqsum (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. rewrite (sqsum_app_eq l1 l2). lia.
Qed.

(* ---------- companions: concatenation monotonicity of the [maxcount]
   extremes (numerator face) ---------- *)

Lemma nmax_app : forall (f : Q -> nat) (l p : list Q), Id (nmax f (l ++ p)) (Nat.max (nmax f l) (nmax f p)).
Proof.
  intros f l p. apply eq_imp_id. induction l as [| a l IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma nmax_le_app_l : forall (f : Q -> nat) (l p : list Q), NatLe (nmax f l) ((nmax f (l ++ p))%nat).
Proof.
  intros f l p. apply NatLe_lift. rewrite nmax_app. apply Nat.le_max_l.
Qed.

Lemma nmax_le_app_r : forall (f : Q -> nat) (l p : list Q), NatLe (nmax f l) ((nmax f (p ++ l))%nat).
Proof.
  intros f l p. apply NatLe_lift. rewrite nmax_app. apply Nat.le_max_r.
Qed.

Lemma nmax_mono : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> (f x <= g x)%nat) -> NatLe (nmax f l) ((nmax g l)%nat).
Proof.
  intros f g l. induction l as [| a t IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (H1 : (f a <= g a)%nat) by (apply H; left; reflexivity).
    assert (H2 : NatLe (nmax f t) (nmax g t))
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ H2). lia.
Qed.

Theorem maxcount_app_ge_l : forall l1 l2 : list Q, NatLe (maxcount l1) ((maxcount (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. unfold maxcount.
  apply (Nat.le_trans (nmax (fun x => freq_q x l1) l1)
                      (nmax (fun x => freq_q x (l1 ++ l2)) l1)
                      (nmax (fun x => freq_q x (l1 ++ l2)) (l1 ++ l2))).
  - apply NatLe_drop.
    apply (nmax_mono (fun x => freq_q x l1)
                     (fun x => freq_q x (l1 ++ l2)) l1).
    intros x _. destruct (id_sym (freq_q_app x l1 l2)). lia.
  - exact (NatLe_drop _ _ (nmax_le_app_l (fun x => freq_q x (l1 ++ l2)) l1 l2)).
Qed.

Theorem maxcount_app_ge_r : forall l1 l2 : list Q, NatLe (maxcount l2) ((maxcount (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. unfold maxcount.
  apply (Nat.le_trans (nmax (fun x => freq_q x l2) l2)
                      (nmax (fun x => freq_q x (l1 ++ l2)) l2)
                      (nmax (fun x => freq_q x (l1 ++ l2)) (l1 ++ l2))).
  - apply NatLe_drop.
    apply (nmax_mono (fun x => freq_q x l2)
                     (fun x => freq_q x (l1 ++ l2)) l2).
    intros x _. destruct (id_sym (freq_q_app x l1 l2)). lia.
  - exact (NatLe_drop _ _ (nmax_le_app_r (fun x => freq_q x (l1 ++ l2)) l2 l1)).
Qed.

(* ---------- honest obstacle: no direction for the normalized quotient
   under concatenation (pinned by counterexamples) ---------- *)

(* concrete value face (closed by [vm_compute]; used in the counterexample
   rewrites) *)
Lemma H_freq_01_val : QeqT (H_freq [0;1]) (1#2)%Q.
Proof. apply qeq_imp_qeqT. unfold H_freq. vm_compute. reflexivity. Qed.

Lemma H_freq_0_val : QeqT (H_freq [0]) 0%Q.
Proof. apply qeq_imp_qeqT. unfold H_freq. vm_compute. reflexivity. Qed.

Lemma collide_01_val : QeqT (collide [0;1]) (1#2)%Q.
Proof. apply qeq_imp_qeqT. unfold collide. vm_compute. reflexivity. Qed.

Lemma collide_0_val : QeqT (collide [0]) 1%Q.
Proof. apply qeq_imp_qeqT. unfold collide. vm_compute. reflexivity. Qed.

(* [H_freq] is not monotone under concatenation: adding one distinct
   element increases the entropy (0 < H_freq [0;1] = 1/2 collides with the
   assumed 1/2 <= 0) *)
Lemma H_freq_app_mono_false :
  Not (forall l1 l2 : list Q, QleT' (H_freq (l1 ++ l2)) (H_freq l1)).
Proof.
  intro H. specialize (H [0] [1]). apply QleT'_to_Qle in H.
  assert (Hn : H_freq ([0] ++ [1]) == H_freq [0;1]) by reflexivity.
  rewrite Hn in H. rewrite (qeqT_imp_qeq _ _ H_freq_01_val) in H.
  rewrite (qeqT_imp_qeq _ _ H_freq_0_val) in H.
  assert (Hgt : 0%Q < (1#2)%Q) by (unfold Qlt; simpl; lia).
  exact (False_rect Empty_set
    (Qlt_irrefl 0%Q (Qlt_le_trans 0%Q (1#2)%Q 0%Q Hgt H))).
Qed.

(* [collide] has no directed monotonicity under concatenation: adding a
   distinct element to an all-equal list decreases the collision entropy
   (the assumed 1 <= 1/2 collides with 1/2 < 1) *)
Lemma collide_app_mono_false :
  Not (forall l1 l2 : list Q, QleT' (collide l1) (collide (l1 ++ l2))).
Proof.
  intro H. specialize (H [0] [1]). apply QleT'_to_Qle in H.
  assert (Hn : collide ([0] ++ [1]) == collide [0;1]) by reflexivity.
  rewrite Hn in H. rewrite (qeqT_imp_qeq _ _ collide_01_val) in H.
  rewrite (qeqT_imp_qeq _ _ collide_0_val) in H.
  assert (Hlt : (1#2)%Q < 1%Q) by (unfold Qlt; simpl; lia).
  exact (False_rect Empty_set
    (Qlt_irrefl 1%Q (Qle_lt_trans 1%Q (1#2)%Q 1%Q H Hlt))).
Qed.

(* the identity [align_lambda] keeps its name and meaning unchanged; the
   real definition [align_lambda_opt] — the optimal lambda chooser over
   the two entropies h0/h1 (if Qle_bool h0 h1 then 1 else 0) — is added in
   this section.  Cross-file note: it has the same semantics as [lam_opt]
   of [DTPT_Rotation] (and its periodic alias [lam_opt_cyc]); this file
   cannot require that one back (the dependency runs the other way), so
   the same-semantics object is given here independently, with statements
   matching the shapes in use there. *)

Definition align_lambda_opt (h0 h1 : Q) : Q := if Qle_bool h0 h1 then 1 else 0.

(* values of the two branches: the endpoint chooser always takes the lambda
   value 1 or 0 (one constructor per branch). *)
Theorem align_lambda_opt_values : forall h0 h1 : Q,
  Or (Id (align_lambda_opt h0 h1) 1%Q) (Id (align_lambda_opt h0 h1) 0%Q).
Proof.
  intros h0 h1. unfold align_lambda_opt.
  destruct (Qle_bool h0 h1).
  - left. apply eq_imp_id. reflexivity.
  - right. apply eq_imp_id. reflexivity.
Qed.

(* range {0,1}: the chooser's image lies in [0,1] (from the values plus
   literal Qle assembly). *)
Theorem align_lambda_opt_range : forall h0 h1 : Q,
  And (QleT' 0 (align_lambda_opt h0 h1)) (QleT' (align_lambda_opt h0 h1) 1).
Proof.
  intros h0 h1. destruct (align_lambda_opt_values h0 h1) as [E | E].
  - destruct (id_sym E). split.
    + exact (xq_Qle_bool_le 0 1 eq_refl).
    + apply Qle_to_QleT'. apply Qle_refl.
  - destruct (id_sym E). split.
    + apply Qle_to_QleT'. apply Qle_refl.
    + exact (xq_Qle_bool_le 0 1 eq_refl).
Qed.

(* optimality (main piece): the mixed entropy at the endpoint chooser does
   not exceed the mixed entropy at any lambda in [0,1].  Each branch
   reduces to one assembly of nonnegative multiplication (affine difference
   route): for h0 <= h1 the choice lambda* = 1 gives the difference
   (1-lam) * (h1-h0); otherwise lambda* = 0 gives lam * (h0-h1). *)
Theorem align_lambda_opt_min : forall (l : list Q) (s : nat) (lam : Q),
  (0 <= lam <= 1)%Q -> QleT' (H_lam l s (align_lambda_opt (H_adj (P0 l)) (H_adj (Pinf l s)))) (H_lam l s lam).
Proof.
  intros l s lam H01. apply Qle_to_QleT'. destruct H01 as [Hlam0 Hlam1].
  unfold H_lam, align_lambda_opt.
  destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))) eqn:E.
  - (* h0 <= h1: lambda* = 1, optimal value = h0 *)
    assert (Hd : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                       - (1 * H_adj (P0 l) + (1 - 1) * H_adj (Pinf l s)))%Q).
    { assert (Er : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - (1 * H_adj (P0 l) + (1 - 1) * H_adj (Pinf l s))
                 == (1 - lam) * (H_adj (Pinf l s) - H_adj (P0 l))) by ring.
      rewrite Er. apply QleT'_to_Qle. apply xq_mul_nonneg.
      + apply QleT'_to_Qle. apply (fst (Qle_0_sub' lam 1)).
        apply Qle_to_QleT'. exact Hlam1.
      + apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
        apply xq_Qle_bool_le. exact E. }
    apply QleT'_to_Qle. apply (snd (Qle_0_sub' _ _)). apply Qle_to_QleT'. exact Hd.
  - (* h0 > h1: lambda* = 0, optimal value = h1 *)
    assert (Hge : (H_adj (Pinf l s) <= H_adj (P0 l))%Q)
      by (apply QleT'_to_Qle; apply Qle_bool_false_le; exact E).
    assert (Hd : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                       - (0 * H_adj (P0 l) + (1 - 0) * H_adj (Pinf l s)))%Q).
    { assert (Er : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - (0 * H_adj (P0 l) + (1 - 0) * H_adj (Pinf l s))
                 == lam * (H_adj (P0 l) - H_adj (Pinf l s))) by ring.
      rewrite Er. apply QleT'_to_Qle. apply xq_mul_nonneg.
      + exact Hlam0.
      + apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
        apply Qle_to_QleT'. exact Hge. }
    apply QleT'_to_Qle. apply (snd (Qle_0_sub' _ _)). apply Qle_to_QleT'. exact Hd.
Qed.

(* endpoint evaluation bridge (companion bonus): the mixed entropy at the
   chooser always takes the phase entropy of one of the endpoints (using
   the endpoint lemmas for lambda = 1 / lambda = 0). *)
Theorem align_lambda_opt_endpoint : forall (l : list Q) (s : nat),
  Or (QeqT (H_lam l s (align_lambda_opt (H_adj (P0 l)) (H_adj (Pinf l s))))
           (H_adj (P0 l)))
     (QeqT (H_lam l s (align_lambda_opt (H_adj (P0 l)) (H_adj (Pinf l s))))
           (H_adj (Pinf l s))).
Proof.
  intros l s.
  destruct (align_lambda_opt_values (H_adj (P0 l)) (H_adj (Pinf l s)))
    as [E | E].
  - left. destruct (id_sym E). apply H_lam_lam1.
  - right. destruct (id_sym E). apply H_lam_lam0.
Qed.

(* ============================================================
   The exact convolution identity of the entropy family under
   concatenation.
   Uses only lemmas already in this file: [freq_q_app], the [nsum] tools,
   [sqsum_app_eq] (the exact cross-term decomposition), the definitions of
   [collide] / [H_freq], and the bridge [H_freq_eq_bridge]
   ([H_freq == 1 - collide]).
   Every statement was first checked numerically by [vm_compute] before
   being committed; the check instances are kept permanently below.
   Honest boundary: the convolution identities carry the guard that n1, n2
   are both nonempty — the field route needs every quotient denominator
   nonzero.  In the degenerate n1 = 0 / n2 = 0 cases the quotient w = 0
   makes the identities still true, but normalization under concatenation
   has no direction (pinned by the counterexamples above); no statements
   beyond the guard are claimed here.
   ============================================================ *)

(* ---------- convolution algebra helpers ---------- *)

(* Q has no zero divisors (the field side condition): nonzero * nonzero <> 0 *)
Lemma qmul_neq0 : forall x y : Q,
  ~ (x == 0) -> ~ (y == 0) -> Not (QeqT (x * y) 0).
Proof.
  intros [xn xd] [yn yd] Hx Hy Hxy. apply qeqT_imp_qeq in Hxy.
  assert (Hxn : (xn <> 0)%Z).
  { intros Hz. apply Hx. unfold Qeq. simpl. rewrite Hz. reflexivity. }
  assert (Hyn : (yn <> 0)%Z).
  { intros Hz. apply Hy. unfold Qeq. simpl. rewrite Hz. reflexivity. }
  unfold Qeq, Qmult in Hxy. simpl in Hxy.
  rewrite ? Z.mul_1_r in Hxy.
  apply Z.mul_eq_0 in Hxy.
  exfalso. destruct Hxy as [E | E]; [exact (Hxn E) | exact (Hyn E)].
Qed.

(* summing the indicator = the frequency (the base-change bridge between
   [nsum] and [freq_q]) *)
Lemma nsum_freq_q_ind : forall (a : Q) (l : list Q), Id (nsum (fun x => if Qeq_bool x a then 1%nat else 0%nat) l) (freq_q a l).
Proof.
  intros a l. apply eq_imp_id. induction l as [| y ys IH].
  - reflexivity.
  - simpl. rewrite IH.
    destruct (Qeq_bool y a) eqn:E1; destruct (Qeq_bool a y) eqn:E2; try lia.
    + exfalso.
      assert (C : Qeq_bool a y = true).
      { apply (proj2 (Qeq_bool_iff a y)). apply Qeq_sym.
        apply (proj1 (Qeq_bool_iff y a)). exact E1. }
      rewrite C in E2. discriminate.
    + exfalso.
      assert (C : Qeq_bool y a = true).
      { apply (proj2 (Qeq_bool_iff y a)). apply Qeq_sym.
        apply (proj1 (Qeq_bool_iff a y)). exact E2. }
      rewrite C in E1. discriminate.
Qed.

(* ---------- baseline: the explicit cross-term form and the symmetric
   double sum ---------- *)

(* companion of [sqsum_app_eq] (the same shape, by expanding [freq_q_app]
   on both sides plus distribution of [nsum]); the body reuses that main
   theorem, no re-proof. *)
Theorem sqsum_app_cross : forall l1 l2 : list Q, Id (sqsum (l1 ++ l2)) ((sqsum l1 + sqsum l2
   + nsum (fun x => freq_q x l2) l1
   + nsum (fun x => freq_q x l1) l2)%nat).
Proof. intros l1 l2. apply eq_imp_id. destruct (sqsum_app_eq l1 l2). reflexivity. Qed.

(* symmetric double sum: the two cross terms are equal (the same counted
   pairing set {(p,q) in l1 x l2 : p == q}) — the load-bearing face of the
   normalized 2X form of the convolution identity. *)
Theorem sqsum_cross_sym : forall l1 l2 : list Q, Id (nsum (fun x => freq_q x l2) l1) ((nsum (fun x => freq_q x l1) l2)%nat).
Proof.
  intros l1. induction l1 as [| a t IH]; intros l2; apply eq_imp_id.
  - cbn [nsum]. symmetry.
    rewrite (nsum_ext_in (fun x : Q => freq_q x []) (fun _ : Q => 0%nat) l2
               (fun x _ => eq_refl)).
    pose proof (nsum_const 0%nat l2) as HC. rewrite HC. lia.
  - cbn [nsum].
    assert (Eext : forall x : Q,
      freq_q x (a :: t) = (freq_q x t + (if Qeq_bool x a then 1%nat else 0%nat))%nat).
    { intros x. simpl. destruct (Qeq_bool x a); lia. }
    rewrite (nsum_ext_in (fun x : Q => freq_q x (a :: t))
              (fun x : Q => (freq_q x t + (if Qeq_bool x a then 1%nat else 0%nat))%nat)
              l2 (fun x _ => Eext x)).
    rewrite nsum_add.
    rewrite (nsum_freq_q_ind a l2).
    rewrite IH. lia.
Qed.

(* normalized 2X form: the cross terms merge into the symmetric double sum
   ([sqsum_app_cross] and [cross_sym]) *)
Theorem sqsum_app_eq2 : forall l1 l2 : list Q, Id (sqsum (l1 ++ l2)) ((sqsum l1 + sqsum l2 + 2 * nsum (fun x => freq_q x l2) l1)%nat).
Proof.
  intros l1 l2. apply eq_imp_id. rewrite (sqsum_app_cross l1 l2).
  rewrite (sqsum_cross_sym l1 l2). lia.
Qed.

(* ---------- main theorem: the collision convolution under concatenation
   (weighted exact form) ---------- *)

(* collide (l1 ++ l2) = (n1/(n1+n2))^2 * collide l1
   + (n2/(n1+n2))^2 * collide l2
   + (sum_{x in l1} freq_q x l2 + sum_{x in l2} freq_q x l1) / (n1+n2)^2.
   A squared-weight combination plus a cross-correction term; nonempty
   guards n1, n2 (field route). *)
Theorem collide_app_eq : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat -> QeqT (collide (l1 ++ l2)) ((qn (length l1) / qn (length l1 + length l2)%nat)
      * (qn (length l1) / qn (length l1 + length l2)%nat) * collide l1
    + (qn (length l2) / qn (length l1 + length l2)%nat)
      * (qn (length l2) / qn (length l1 + length l2)%nat) * collide l2
    + (qn (nsum (fun x => freq_q x l2) l1)
       + qn (nsum (fun x => freq_q x l1) l2))
      / (qn (length l1 + length l2)%nat * qn (length l1 + length l2)%nat)).
Proof.
  intros l1 l2 H1 H2.
  apply qeq_imp_qeqT.
  unfold collide.
  rewrite length_app.
  rewrite (sqsum_app_eq l1 l2).
  assert (qn_addP : forall a b : nat, qn (a + b)%nat == qn a + qn b)
    by (intros a b; exact (qeqT_imp_qeq _ _ (qn_add a b))).
  rewrite ! qn_addP.
  assert (Hnn : (0 < length l1 + length l2)%nat) by lia.
  assert (HN : ~ (qn (length l1 + length l2)%nat == 0)).
  { intro Hc. destruct (qpos_neq0 (qn (length l1 + length l2)%nat)
      (QltT_to_Qlt 0 (qn (length l1 + length l2)%nat) (qn_pos _ Hnn))
      (qeq_imp_qeqT _ _ Hc)). }
  assert (Ha : ~ (qn (length l1) == 0)).
  { intro Hc. destruct (qpos_neq0 (qn (length l1))
      (QltT_to_Qlt 0 (qn (length l1)) (qn_pos _ H1))
      (qeq_imp_qeqT _ _ Hc)). }
  assert (Hb : ~ (qn (length l2) == 0)).
  { intro Hc. destruct (qpos_neq0 (qn (length l2))
      (QltT_to_Qlt 0 (qn (length l2)) (qn_pos _ H2))
      (qeq_imp_qeqT _ _ Hc)). }
  assert (HPP1 : ~ (qn (length l1) * qn (length l1) == 0)).
  { intro Hc. destruct (qmul_neq0 (qn (length l1)) (qn (length l1)) Ha Ha
         (qeq_imp_qeqT _ _ Hc)). }
  assert (HPP2 : ~ (qn (length l2) * qn (length l2) == 0)).
  { intro Hc. destruct (qmul_neq0 (qn (length l2)) (qn (length l2)) Hb Hb
         (qeq_imp_qeqT _ _ Hc)). }
  assert (HN2 : ~ (qn (length l1) + qn (length l2) == 0)).
  { intro Zc. apply HN.
    rewrite (qeqT_imp_qeq _ _ (qn_add (length l1) (length l2))). exact Zc. }
  assert (HNN2 : ~ ((qn (length l1) + qn (length l2))
                    * (qn (length l1) + qn (length l2)) == 0)).
  { intro Hc.
    destruct (qmul_neq0 (qn (length l1) + qn (length l2))
      (qn (length l1) + qn (length l2)) HN2 HN2
      (qeq_imp_qeqT _ _ Hc)). }
  field; repeat split; assumption.
Qed.

(* ---------- main piece: the [H_freq] convolution under concatenation
   (weighted, with the 2 w1 w2 cross-correction) ---------- *)

(* H_freq (l1 ++ l2) = w1^2 * H_freq l1 + w2^2 * H_freq l2 + 2 * w1 * w2
   - (sum_{x in l1} freq_q x l2 + sum_{x in l2} freq_q x l1) / (n1+n2)^2.
   From [collide_app_eq] and [H_freq_eq_bridge] (== 1 - collide); the
   cross-correction 2 * w1 * w2 - X / (n1+n2)^2 is nonnegative and bounded
   (2 * (n1*n2 - X) / (n1+n2)^2 >= 0, with X <= n1 * n2 pointwise by
   [freq_q_le_length]) — the full convolution identity of the entropy
   family. *)
Theorem H_freq_app_eq : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat -> QeqT (H_freq (l1 ++ l2)) ((qn (length l1) / qn (length l1 + length l2)%nat)
      * (qn (length l1) / qn (length l1 + length l2)%nat) * H_freq l1
    + (qn (length l2) / qn (length l1 + length l2)%nat)
      * (qn (length l2) / qn (length l1 + length l2)%nat) * H_freq l2
    + 2 * (qn (length l1) / qn (length l1 + length l2)%nat)
        * (qn (length l2) / qn (length l1 + length l2)%nat)
    - (qn (nsum (fun x => freq_q x l2) l1)
       + qn (nsum (fun x => freq_q x l1) l2))
      / (qn (length l1 + length l2)%nat * qn (length l1 + length l2)%nat)).
Proof.
  intros l1 l2 H1 H2.
  apply qeq_imp_qeqT.
  assert (Hnn : (0 < length (l1 ++ l2))%nat) by (rewrite length_app; lia).
  assert (Hnn2 : (0 < length l1 + length l2)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (H_freq_eq_bridge (l1 ++ l2) Hnn)). unfold H_min_q.
  rewrite (qeqT_imp_qeq _ _ (collide_app_eq l1 l2 H1 H2)).
  assert (B1 : collide l1 == 1 - H_freq l1).
  { pose proof (qeqT_imp_qeq _ _ (H_freq_eq_bridge l1 H1)) as T.
    unfold H_min_q in T. rewrite T. ring. }
  assert (B2 : collide l2 == 1 - H_freq l2).
  { pose proof (qeqT_imp_qeq _ _ (H_freq_eq_bridge l2 H2)) as T.
    unfold H_min_q in T. rewrite T. ring. }
  rewrite B1, B2.
  rewrite (qeqT_imp_qeq _ _ (qn_add (length l1) (length l2))).
  assert (HN2 : ~ (qn (length l1) + qn (length l2) == 0)).
  { intro Hc.
    rewrite <- (qeqT_imp_qeq _ _ (qn_add (length l1) (length l2))) in Hc.
    destruct (qpos_neq0 (qn (length l1 + length l2)%nat)
      (QltT_to_Qlt 0 (qn (length l1 + length l2)%nat) (qn_pos _ Hnn2))
      (qeq_imp_qeqT _ _ Hc)). }
  assert (HNN2 : ~ ((qn (length l1) + qn (length l2))
                    * (qn (length l1) + qn (length l2)) == 0)).
  { intro Hc.
    destruct (qmul_neq0 (qn (length l1) + qn (length l2))
      (qn (length l1) + qn (length l2)) HN2 HN2
      (qeq_imp_qeqT _ _ Hc)). }
  field; repeat split; assumption.
Qed.

(* ---------- bonus: associativity consistency of the convolution for
   three-way concatenation (value face) ---------- *)

(* (l1 ++ l2) ++ l3 and l1 ++ (l2 ++ l3) are the same list (definitionally,
   by [app_assoc]), so the three convolution quantities coincide pointwise
   under both groupings — the consistency closure of the convolution
   identity for three-way concatenation. *)
Theorem sqsum_app_assoc : forall (l1 l2 l3 : list Q), Id (sqsum ((l1 ++ l2) ++ l3)) (sqsum (l1 ++ (l2 ++ l3))).
Proof. intros l1 l2 l3. apply eq_imp_id. rewrite <- app_assoc. reflexivity. Qed.

Theorem collide_app_assoc : forall (l1 l2 l3 : list Q),
  QeqT (collide ((l1 ++ l2) ++ l3)) (collide (l1 ++ (l2 ++ l3))).
Proof. intros l1 l2 l3. apply qeq_imp_qeqT.
  rewrite <- app_assoc. reflexivity. Qed.

Theorem H_freq_app_assoc : forall (l1 l2 l3 : list Q),
  QeqT (H_freq ((l1 ++ l2) ++ l3)) (H_freq (l1 ++ (l2 ++ l3))).
Proof. intros l1 l2 l3. apply qeq_imp_qeqT.
  rewrite <- app_assoc. reflexivity. Qed.

(* ---------- numerical anchors ([vm_compute] check instances) ---------- *)

(* check instance: l1 = [0;1], l2 = [1;1] (with nontrivial cross terms
   X1 = X2 = 2).  Measured: sqsum (l1++l2) = 10, collide = 5/8,
   H_freq = 3/8; the weighted right-hand sides of both main theorems
   evaluate to the same values — the statements were verified to be true
   before being committed. *)
Lemma sqsum_app_cross_val : Id (sqsum ([0;1] ++ [1;1])) (10%nat).
Proof. apply eq_imp_id.
  change (sqsum [0; 1; 1; 1] = 10%nat).
  change (nsum (fun x => freq_q x [0; 1; 1; 1]) [0; 1; 1; 1] = 10%nat).
  change (Nat.add (freq_q 0 [0; 1; 1; 1])
            (Nat.add (freq_q 1 [0; 1; 1; 1])
               (Nat.add (freq_q 1 [0; 1; 1; 1])
                  (Nat.add (freq_q 1 [0; 1; 1; 1]) 0%nat))) = 10%nat).
  change ((1 + (3 + (3 + (3 + 0))))%nat = 10%nat).
  reflexivity.
Qed.

Lemma sqsum_cross_sym_val : Id (nsum (fun x => freq_q x [1;1]) [0;1]) (nsum (fun x => freq_q x [0;1]) [1;1]).
Proof. apply eq_imp_id.
  change (Nat.add (freq_q 0 [1; 1]) (freq_q 1 [1; 1])
          = Nat.add (freq_q 1 [0; 1]) (freq_q 1 [0; 1])).
  change ((0 + 2)%nat = (1 + 1)%nat).
  reflexivity.
Qed.

Lemma collide_app_eq_val : QeqT (collide ([0;1] ++ [1;1])) (5#8)%Q.
Proof. apply qeq_imp_qeqT. unfold collide. vm_compute. reflexivity. Qed.

Lemma collide_app_eq_rhs_val : QeqT ((qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat)
    * (qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat) * collide [0;1]
  + (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat)
    * (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat) * collide [1;1]
  + (qn (nsum (fun x => freq_q x [1;1]) [0;1])
     + qn (nsum (fun x => freq_q x [0;1]) [1;1]))
    / (qn (length [0;1] + length [1;1])%nat
       * qn (length [0;1] + length [1;1])%nat)) ((5#8)%Q).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Lemma H_freq_app_eq_val : QeqT (H_freq ([0;1] ++ [1;1])) (3#8)%Q.
Proof. apply qeq_imp_qeqT. unfold H_freq. vm_compute. reflexivity. Qed.

Lemma H_freq_app_eq_rhs_val : QeqT ((qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat)
    * (qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat) * H_freq [0;1]
  + (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat)
    * (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat) * H_freq [1;1]
  + 2 * (qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat)
      * (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat)
  - (qn (nsum (fun x => freq_q x [1;1]) [0;1])
     + qn (nsum (fun x => freq_q x [0;1]) [1;1]))
    / (qn (length [0;1] + length [1;1])%nat
       * qn (length [0;1] + length [1;1])%nat)) ((3#8)%Q).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

End DTPT_Entropy.

Import DTPT_Entropy.

(* ========== zero-axiom attestation of the merged sections ========== *)

Print Assumptions freq_q_app.
Print Assumptions freq_q_perm.
Print Assumptions H_freq_perm.
Print Assumptions H_freq_nonneg.
Print Assumptions H_freq_all_same_zero.
Print Assumptions H_freq_len_le_1.
Print Assumptions H_freq_eq0_all_same.
Print Assumptions freq_q_map.
Print Assumptions freq_q_map_ge.
Print Assumptions sqsum_map_ge.
Print Assumptions H_freq_dpi.
Print Assumptions H_freq_map_id.
Print Assumptions H_freq_map_const.
Print Assumptions H_freq_map_twice.
Print Assumptions H_freq_map_chain.

(* ========== zero-axiom attestation ========== *)

Print Assumptions collide_lower.
Print Assumptions collide_upper.
Print Assumptions collide_le_maxfreq.
Print Assumptions maxfreq_lower.
Print Assumptions maxfreq_upper.
Print Assumptions H_freq_eq_bridge.
Print Assumptions H_max_q_anti.
Print Assumptions H_chain.
Print Assumptions maxfreq_perm.
Print Assumptions collide_perm.
Print Assumptions H_max_q_perm.
Print Assumptions H_min_q_perm.

(* ========== zero-axiom attestation of the coherence / zero-locus sections
   ========== *)

Print Assumptions me_cert.
Print Assumptions mkMEval_gate_bridge.
Print Assumptions mkMEval_Hcond_count_ub.
Print Assumptions me_total_ub.
Print Assumptions H_shannon_q_zero_iff_sorted.
Print Assumptions H_ms1_iff_const.
Print Assumptions H_cond_abs_bound.
Print Assumptions zero_locus_joint.


Print Assumptions sqsum_app_ge_l.
Print Assumptions sqsum_app_ge_r.
Print Assumptions sqsum_app_eq.
Print Assumptions sqsum_app_ge_sum.
Print Assumptions maxcount_app_ge_l.
Print Assumptions maxcount_app_ge_r.
Print Assumptions H_freq_app_mono_false.
Print Assumptions collide_app_mono_false.


Print Assumptions align_lambda_opt_values.
Print Assumptions align_lambda_opt_range.
Print Assumptions align_lambda_opt_min.
Print Assumptions align_lambda_opt_endpoint.


Print Assumptions qmul_neq0.
Print Assumptions nsum_freq_q_ind.
Print Assumptions sqsum_app_cross.
Print Assumptions sqsum_cross_sym.
Print Assumptions sqsum_app_eq2.
Print Assumptions collide_app_eq.
Print Assumptions H_freq_app_eq.
Print Assumptions sqsum_app_assoc.
Print Assumptions collide_app_assoc.
Print Assumptions H_freq_app_assoc.
Print Assumptions sqsum_app_cross_val.
Print Assumptions sqsum_cross_sym_val.
Print Assumptions collide_app_eq_val.
Print Assumptions collide_app_eq_rhs_val.
Print Assumptions H_freq_app_eq_val.
Print Assumptions H_freq_app_eq_rhs_val.





Print Assumptions DTPT_Entropy.DTPT_Entropy.xq_Qle_bool_true.
Print Assumptions DTPT_Entropy.DTPT_Entropy.xq_Qle_bool_le.
Print Assumptions DTPT_Entropy.DTPT_Entropy.Pinf_eq_l.
Print Assumptions DTPT_Entropy.DTPT_Entropy.qlen_pos.
Print Assumptions DTPT_Entropy.DTPT_Entropy.collide_zero.
Print Assumptions DTPT_Entropy.DTPT_Entropy.me2_weight_nonneg.
Print Assumptions DTPT_Entropy.DTPT_Entropy.me_total_eq.
Print Assumptions DTPT_Entropy.DTPT_Entropy.sqsum_app_cross_val.
Print Assumptions DTPT_Entropy.DTPT_Entropy.sqsum_cross_sym_val.
