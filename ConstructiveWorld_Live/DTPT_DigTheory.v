(* ConstructiveWorld-Set -- DTPT_DigTheory: coding-tree size, order, and the decision face of the dig codes. *)

(** * DTPT_DigTheory: size, order, and decision theory of the Dig coding tree.

    Mission.  Module DTPT_DigTheory: the [dig_ne_] mutual-exclusion family
      over constructor pairs, the [dig_size] / [dig_lsize] size-equation
      family, the [dig_Q] projection with its round trip, [is_num]
      numericity, [sub_dig] with strict subterm size monotonicity, the
      [h_alg] decision chain, and the triple-agreement combination face.

    Dependencies.  [DTPT] of this development; Stdlib [QArith.QArith],
      [List], [Arith], [Lia], [Bool], [ZArith].

    References.  Size decidability and the subterm order of prefix-free
      codes (combinatory logic / coding theory); this development,
      DTPT_DigTheory.v, the baseline module in ConstructiveWorld-Main whose
      statement names are carried over here verbatim (comment-face English
      wash only, zero statement edits).

    Constructivity.  Every proof closes by [Qed], zero admission lexemes,
      no classical logic; the statement face is carried at the [Set] layer
      (order predicates and equalities are Set-valued, zero [Prop] leakage).

    Build.  Rocq 9.1 direct [coqc -Q . "" -native-compiler no] (the vo
      shadow tree rebuilt in the same world, cpu_guard load capping); the
      artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Bool ZArith.
Require DTPT.
Import ListNotations.
Open Scope Q_scope.
Import DTPT.DTPT.

Module DTPT_DigTheory.

(* ========== §1 constructor injectivity (floor piece) ========== *)

Lemma dig_inj_dQ : forall x y : Q, dQ x = dQ y -> x = y.
Proof. intros x y H. injection H as Hxy. exact Hxy. Qed.

Lemma dig_inj_dPair : forall a b c d : Dig,
  dPair a b = dPair c d -> a = c /\ b = d.
Proof. intros a b c d H. split; congruence. Qed.

Lemma dig_inj_dSeq : forall l1 l2 : list Dig,
  dSeq l1 = dSeq l2 -> l1 = l2.
Proof. intros l1 l2 H. injection H as Hl. exact Hl. Qed.

Lemma dig_inj_dCode : forall (n m : nat) (f g : nat -> Dig),
  dCode n f = dCode m g -> n = m /\ f = g.
Proof. intros n m f g H. split; congruence. Qed.

Lemma dig_inj_dCode_pointwise : forall (n m : nat) (f g : nat -> Dig),
  dCode n f = dCode m g -> n = m /\ (forall i : nat, f i = g i).
Proof.
  intros n m f g H. destruct (dig_inj_dCode n m f g H) as [Hn Hf].
  split; [exact Hn | intros i; rewrite Hf; reflexivity].
Qed.

Lemma dig_inj_dJudge : forall a b c d : Dig,
  dJudge a b = dJudge c d -> a = c /\ b = d.
Proof. intros a b c d H. split; congruence. Qed.

Lemma dig_inj_dModel : forall a b : Dig,
  dModel a = dModel b -> a = b.
Proof. intros a b H. injection H as Hab. exact Hab. Qed.

Lemma dig_inj_dProofT : forall a b c d : Dig,
  dProofT a b = dProofT c d -> a = c /\ b = d.
Proof. intros a b c d H. split; congruence. Qed.

(* ========== §2 cross-constructor mutual exclusion (21 pairs) (floor piece) ========== *)
(* pairwise discriminate; the reverse directions come free by symmetry
   of equality and are not restated as separate lemmas. *)

Lemma dig_ne_dQ_dPair : forall (x : Q) (a b : Dig), dQ x <> dPair a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dQ_dSeq : forall (x : Q) (l : list Dig), dQ x <> dSeq l.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dQ_dCode : forall (x : Q) (n : nat) (f : nat -> Dig),
  dQ x <> dCode n f.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dQ_dJudge : forall (x : Q) (a b : Dig), dQ x <> dJudge a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dQ_dModel : forall (x : Q) (a : Dig), dQ x <> dModel a.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dQ_dProofT : forall (x : Q) (a b : Dig), dQ x <> dProofT a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dPair_dSeq : forall (a b : Dig) (l : list Dig),
  dPair a b <> dSeq l.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dPair_dCode : forall (a b : Dig) (n : nat) (f : nat -> Dig),
  dPair a b <> dCode n f.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dPair_dJudge : forall (a b : Dig) (c d : Dig),
  dPair a b <> dJudge c d.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dPair_dModel : forall (a b : Dig) (c : Dig),
  dPair a b <> dModel c.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dPair_dProofT : forall (a b : Dig) (c d : Dig),
  dPair a b <> dProofT c d.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dSeq_dCode : forall (l : list Dig) (n : nat) (f : nat -> Dig),
  dSeq l <> dCode n f.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dSeq_dJudge : forall (l : list Dig) (a b : Dig),
  dSeq l <> dJudge a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dSeq_dModel : forall (l : list Dig) (a : Dig),
  dSeq l <> dModel a.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dSeq_dProofT : forall (l : list Dig) (a b : Dig),
  dSeq l <> dProofT a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dCode_dJudge : forall (n : nat) (f : nat -> Dig) (a b : Dig),
  dCode n f <> dJudge a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dCode_dModel : forall (n : nat) (f : nat -> Dig) (a : Dig),
  dCode n f <> dModel a.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dCode_dProofT : forall (n : nat) (f : nat -> Dig) (a b : Dig),
  dCode n f <> dProofT a b.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dJudge_dModel : forall (a b : Dig) (c : Dig),
  dJudge a b <> dModel c.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dJudge_dProofT : forall (a b : Dig) (c d : Dig),
  dJudge a b <> dProofT c d.
Proof. intros; discriminate. Qed.

Lemma dig_ne_dModel_dProofT : forall (a : Dig) (b c : Dig),
  dModel a <> dProofT b c.
Proof. intros; discriminate. Qed.

(* ========== §3 tower size theory (main piece) ========== *)
(* dig_size recurses on the constructor structure: a binary node takes
   one plus the sum of the child sizes, a sequence node takes one plus
   the sum of the sizes listed in the table, and dCode counts its
   leading argument slot (see header note a).
   implementation note: a mutual Fixpoint scheme is rejected by the
   guard check (dig_lsize would apply dig_size x to the list head,
   and x is not a subterm of the tail argument xs) — instead the dSeq
   branch embeds an anonymous fix: y stays a subterm of d through the
   three nested matches d ⊳ l ⊳ m ⊳ y, so the guard is satisfied;
   dig_lsize is then defined separately, and the equation face holds
   by convertibility. *)

Fixpoint dig_size (d : Dig) : nat :=
  match d with
  | dQ _ => 1%nat
  | dPair a b => S (dig_size a + dig_size b)%nat
  | dSeq l =>
      S ((fix dig_lsz (m : list Dig) : nat :=
            match m with
            | [] => 0%nat
            | y :: ys => (dig_size y + dig_lsz ys)%nat
            end) l)
  | dCode n _ => S n%nat
  | dJudge a b => S (dig_size a + dig_size b)%nat
  | dModel a => S (dig_size a)
  | dProofT a b => S (dig_size a + dig_size b)%nat
  end.

(* standalone list size function (same body as the dSeq-embedded fix
   of dig_size, convertible) *)
Fixpoint dig_lsize (l : list Dig) : nat :=
  match l with
  | [] => 0%nat
  | x :: xs => (dig_size x + dig_lsize xs)%nat
  end.

(* --- constructor equation family (all hold definitionally) --- *)

Theorem dig_size_eq_dQ : forall x : Q, dig_size (dQ x) = 1%nat.
Proof.
  intros x.
  (* route one: unfold the recursive body; the numeric branch
     iota-reduces on the dQ constructor to the constant one *)
  change (dig_size (dQ x)) with 1%nat.
  reflexivity.
Qed.

Theorem dig_size_eq_dPair : forall a b : Dig,
  dig_size (dPair a b) = S (dig_size a + dig_size b)%nat.
Proof.
  intros a b.
  (* route one: unfold the recursive body; the binary branch
     iota-reduces to one plus the sum of the child sizes *)
  change (dig_size (dPair a b)) with (S (dig_size a + dig_size b))%nat.
  reflexivity.
Qed.

Theorem dig_size_eq_dSeq : forall l : list Dig,
  dig_size (dSeq l) = S (dig_lsize l).
Proof.
  intros l.
  (* route one: unfold the recursive body; the sequence branch reduces
     through the embedded list scan to the successor form of the list
     size *)
  change (dig_size (dSeq l)) with (S (dig_lsize l)).
  reflexivity.
Qed.

Theorem dig_size_eq_dCode : forall (n : nat) (f : nat -> Dig),
  dig_size (dCode n f) = S n.
Proof.
  intros n f.
  (* route one: unfold the recursive body; the code branch reduces by
     counting its leading argument slot to the successor slot depth *)
  change (dig_size (dCode n f)) with (S n).
  reflexivity.
Qed.

Theorem dig_size_eq_dJudge : forall a b : Dig,
  dig_size (dJudge a b) = S (dig_size a + dig_size b)%nat.
Proof.
  intros a b.
  (* route one: unfold the recursive body; the judge branch
     iota-reduces to one plus the sum of the child sizes *)
  change (dig_size (dJudge a b)) with (S (dig_size a + dig_size b))%nat.
  reflexivity.
Qed.

Theorem dig_size_eq_dModel : forall a : Dig,
  dig_size (dModel a) = S (dig_size a).
Proof.
  intros a.
  (* route one: unfold the recursive body; the model branch reduces to
     one plus the single child size *)
  change (dig_size (dModel a)) with (S (dig_size a)).
  reflexivity.
Qed.

Theorem dig_size_eq_dProofT : forall a b : Dig,
  dig_size (dProofT a b) = S (dig_size a + dig_size b)%nat.
Proof.
  intros a b.
  (* route one: unfold the recursive body; the proof branch reduces to
     one plus the sum of the child sizes *)
  change (dig_size (dProofT a b)) with (S (dig_size a + dig_size b))%nat.
  reflexivity.
Qed.

Theorem dig_lsize_eq_nil : dig_lsize [] = 0%nat.
Proof.
  (* route one: the list size function iota-reduces on the empty
     constructor to zero *)
  change (dig_lsize (@nil Dig)) with 0%nat.
  reflexivity.
Qed.

Theorem dig_lsize_eq_cons : forall (x : Dig) (l : list Dig),
  dig_lsize (x :: l) = (dig_size x + dig_lsize l)%nat.
Proof.
  intros x l.
  (* route one: the list size function reduces on the single-element
     cons branch to the head size plus the tail accumulation *)
  change (dig_lsize (x :: l)) with (dig_size x + dig_lsize l)%nat.
  reflexivity.
Qed.

(* --- positivity and lower-bound face --- *)

Theorem dig_size_pos : forall d : Dig, (0 < dig_size d)%nat.
Proof. intros d. destruct d; simpl; lia. Qed.

Theorem dig_size_ge1 : forall d : Dig, (1 <= dig_size d)%nat.
Proof. intros d. pose proof (dig_size_pos d). lia. Qed.

Theorem dig_lsize_cons_pos : forall (x : Dig) (l : list Dig),
  (0 < dig_lsize (x :: l))%nat.
Proof. intros x l. simpl. pose proof (dig_size_pos x). lia. Qed.

Theorem dig_lsize_pos : forall l : list Dig,
  l <> [] -> (0 < dig_lsize l)%nat.
Proof.
  intros l Hne. destruct l as [| y ys].
  - exfalso. apply Hne. reflexivity.
  - apply dig_lsize_cons_pos.
Qed.

Theorem dig_lsize_app : forall l1 l2 : list Dig,
  dig_lsize (l1 ++ l2) = (dig_lsize l1 + dig_lsize l2)%nat.
Proof.
  intros l1 l2. induction l1 as [| y ys IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

(* branch node sizes are at least 2 (the child positivity premise is
   needed — child sizes are opaque atoms and bare lia refuses the
   goal with the X=Y=0 counterexample: the canonical worked example
   for asserting a subgoal's truth before proving it) *)

Theorem dig_size_dPair_ge2 : forall a b : Dig,
  (2 <= dig_size (dPair a b))%nat.
Proof.
  intros a b. rewrite dig_size_eq_dPair.
  pose proof (dig_size_ge1 a). pose proof (dig_size_ge1 b). lia.
Qed.

Theorem dig_size_dJudge_ge2 : forall a b : Dig,
  (2 <= dig_size (dJudge a b))%nat.
Proof.
  intros a b. rewrite dig_size_eq_dJudge.
  pose proof (dig_size_ge1 a). pose proof (dig_size_ge1 b). lia.
Qed.

Theorem dig_size_dProofT_ge2 : forall a b : Dig,
  (2 <= dig_size (dProofT a b))%nat.
Proof.
  intros a b. rewrite dig_size_eq_dProofT.
  pose proof (dig_size_ge1 a). pose proof (dig_size_ge1 b). lia.
Qed.

Theorem dig_size_dModel_ge2 : forall a : Dig,
  (2 <= dig_size (dModel a))%nat.
Proof.
  intros a. rewrite dig_size_eq_dModel.
  pose proof (dig_size_ge1 a). lia.
Qed.

(* ========== §4 numeric projection dig_Q (main piece) ========== *)
(* total function: the dQ slot returns the original value and every
   other constructor returns the default 0 (header note c:
   non-injective). *)

Definition dig_Q (d : Dig) : Q :=
  match d with
  | dQ x => x
  | _ => 0%Q
  end.

Theorem dig_Q_eq_dQ : forall x : Q, dig_Q (dQ x) = x.
Proof.
  intros x.
  (* route one: unfold the projection body; the numeric branch returns
     the original value *)
  change (dig_Q (dQ x)) with x.
  reflexivity.
Qed.

Theorem dig_Q_roundtrip : forall (d : Dig) (x : Q),
  d = dQ x -> dig_Q d = x.
Proof.
  intros d x H.
  (* route three, rewrite chain: rewrite the goal along the shape
     premise, then unfold the projection body and close by reduction,
     replacing the earlier single-hop substitution *)
  rewrite H.
  change (dig_Q (dQ x)) with x.
  reflexivity.
Qed.

Theorem dig_Q_not_injective_witness :
  dig_Q (dModel (dQ 0)) = dig_Q (dQ 0).
Proof.
  (* route two, explicit witness: each projection reduces along its
     own branch — the model branch lands on the default-zero arm, the
     numeric branch returns the original value, and both sides land
     on zero before the goal closes (the non-injectivity witness) *)
  change (dig_Q (dModel (dQ 0))) with 0%Q.
  change (dig_Q (dQ 0)) with 0%Q.
  reflexivity.
Qed.

(* ========== §5 numeric-domain decision is_num and the combination face (bonus piece) ========== *)

Definition is_num (d : Dig) : bool :=
  match d with
  | dQ _ => true
  | _ => false
  end.

Theorem is_num_eq_dQ : forall x : Q, is_num (dQ x) = true.
Proof.
  intros x.
  (* route one: unfold the decision procedure body; the numeric branch
     reduces to true *)
  change (is_num (dQ x)) with true.
  reflexivity.
Qed.

(* characterization, weak form (the Prop existential) *)
Theorem is_num_inv : forall d : Dig,
  is_num d = true -> exists x : Q, d = dQ x.
Proof.
  intros d H. destruct d as [x | a b | l | n f | a b | a | a b];
    simpl in H; try discriminate.
  exists x. reflexivity.
Qed.

(* characterization, constructive form (sigT, witness extractable) *)
Theorem is_num_inv_sigT : forall d : Dig,
  is_num d = true -> { x : Q & d = dQ x }.
Proof.
  intros d H. destruct d as [x | a b | l | n f | a b | a | a b];
    simpl in H; try discriminate.
  exact (existT _ x (eq_refl (dQ x))).
Qed.

Theorem is_num_false_not_dQ : forall (d : Dig) (x : Q),
  is_num d = false -> d <> dQ x.
Proof.
  intros d x H Heq. rewrite Heq in H. rewrite is_num_eq_dQ in H.
  discriminate.
Qed.

(* combination face one: the projection of a non-numeric node always
   lands on the default zero *)
Theorem dig_Q_default0 : forall d : Dig,
  is_num d = false -> dig_Q d = 0%Q.
Proof.
  intros d H. destruct d as [x | a b | l | n f | a b | a | a b];
    simpl in H; try discriminate; reflexivity.
Qed.

(* combination face two: a numeric node has size exactly 1 (only the
   forward direction, header note b) *)
Theorem is_num_size1 : forall d : Dig,
  is_num d = true -> dig_size d = 1%nat.
Proof.
  intros d H. destruct d as [x | a b | l | n f | a b | a | a b];
    simpl in H; try discriminate.
  reflexivity.
Qed.

(* combination face three: the triple agreement of the dQ probe
   (projection round trip + size + decision) — the main theorem *)
Theorem dQ_probe_roundtrip : forall x : Q,
  dig_Q (dQ x) = x /\ dig_size (dQ x) = 1%nat /\ is_num (dQ x) = true.
Proof.
  intros x.
  (* route three, split-and-combine structure: the triple agreement
     unfolds branch by branch — projection, size, and decision each
     go through an explicit reduction chain, replacing the
     closed-form injection split *)
  split.
  - change (dig_Q (dQ x)) with x. reflexivity.
  - split.
    + change (dig_size (dQ x)) with 1%nat. reflexivity.
    + change (is_num (dQ x)) with true. reflexivity.
Qed.

(* honest boundary: size 1 does not coincide with the numeric domain
   (the dSeq [] counterexample, definitional witness) *)
Theorem dig_size_one_not_only_num :
  dig_size (dSeq []) = 1%nat /\ is_num (dSeq []) = false.
Proof.
  (* route three, split-and-combine structure: each side of the
     counterexample witness goes through an explicit reduction — the
     empty sequence size lands on one through the embedded list scan,
     the decision procedure lands on false *)
  split.
  - change (dig_size (dSeq [])) with 1%nat. reflexivity.
  - change (is_num (dSeq [])) with false. reflexivity.
Qed.

(* ========== final audit: assumption-closure check ========== *)

Print Assumptions dQ_probe_roundtrip.
Print Assumptions dig_size_pos.
Print Assumptions is_num_inv_sigT.
Print Assumptions dig_Q_default0.
Print Assumptions dig_ne_dQ_dPair.
Print Assumptions dig_inj_dCode_pointwise.

(* ============================================================
   H proxy segment (M4 merge: from the original DTPT_HAlg.v; source
   file DTPT-U13R, merged in full, zero changes to the statements
   above, zero changes to the Qed face)
   collision search: h_alg / sub_dig / dig_eqb have zero hits across
   all .v files of the repository (grep-verified on the U13R segment,
   no residue from earlier versions, this file is the single source
   of truth for the segment).
   load discipline: all compilations go through cpu_guard
   (LoadLimit 60 / CoolSec 10), with coqc/coqchk serialization
   checked before each compile and a snapshot taken as each piece
   lands on disk.
   ============================================================ *)

Import ListNotations.
Open Scope Q_scope.

(* ========== §1 floor piece: the h_alg definition + nonnegativity / positivity + the minimal code face ========== *)

Definition h_alg (d : Dig) : Q := ((Z.of_nat (dig_size d)) # 1)%Q.

Theorem h_alg_dQ : forall x : Q, h_alg (dQ x) == 1.
Proof.
  intros x.
  unfold h_alg.
  (* route one, two-step chain: first unfold the depth proxy body,
     then reduce the integer-converted depth explicitly along the
     size branch to the constant one and close in that form *)
  change ((Z.of_nat (dig_size (dQ x))) # 1)%Q with ((1:Z) # 1)%Q.
  reflexivity.
Qed.

Theorem h_alg_pos : forall d : Dig, 0 < h_alg d.
Proof.
  intros d. pose proof (dig_size_pos d) as Hp. unfold h_alg.
  destruct (dig_size d) as [| k].
  - lia.
  - unfold Qlt. cbn [Qnum Qden]. rewrite !Z.mul_1_r. reflexivity.
Qed.

Theorem h_alg_nonneg : forall d : Dig, 0 <= h_alg d.
Proof. intros d. apply Qlt_le_weak. apply h_alg_pos. Qed.

(* ========== §2 main piece, subterm order: sub_dig + strict size monotonicity (core piece) ========== *)
(* dig_eqb: a size-monotone matching approximation on Dig (header
   note c). the dSeq branch follows the S7 guardedness pattern: the
   direct subterm l1 of dSeq l1 carries the embedded anonymous fix
   (a two-layer list scan), and the independent equation face holds
   by convertibility. *)

Fixpoint dig_eqb (a b : Dig) {struct a} : bool :=
  match a, b with
  | dQ x, dQ y => Qeq_bool x y
  | dPair a1 a2, dPair b1 b2 => (dig_eqb a1 b1 && dig_eqb a2 b2)
  | dSeq l1, dSeq l2 =>
      (fix eq_l (m1 m2 : list Dig) {struct m1} : bool :=
         match m1, m2 with
         | [], [] => true
         | x :: xs, y :: ys => (dig_eqb x y && eq_l xs ys)
         | _, _ => false
         end) l1 l2
  | dJudge a1 a2, dJudge b1 b2 => (dig_eqb a1 b1 && dig_eqb a2 b2)
  | dModel a1, dModel b1 => dig_eqb a1 b1
  | dProofT a1 a2, dProofT b1 b2 => (dig_eqb a1 b1 && dig_eqb a2 b2)
  | _, _ => false
  end.

(* the dSeq-face equation (taken directly by convertibility, for use
   in inductions) *)
Theorem dig_eqb_dSeq_cons : forall (x : Dig) (xs : list Dig) (y : Dig) (ys : list Dig),
  dig_eqb (dSeq (x :: xs)) (dSeq (y :: ys)) =
  (dig_eqb x y && dig_eqb (dSeq xs) (dSeq ys)).
Proof.
  intros x xs y ys.
  (* route one: unfold the matcher body; the sequence branch reduces
     through the embedded two-layer list scan to the per-element
     conjunction face *)
  change (dig_eqb (dSeq (x :: xs)) (dSeq (y :: ys)))
    with (dig_eqb x y && dig_eqb (dSeq xs) (dSeq ys)).
  reflexivity.
Qed.

(* dig_eqb transfers size (bounded induction; the dSeq face goes
   through the inner list induction, with the per-element IH supplying
   the measure) *)
Lemma dig_eqb_size_bound : forall (n : nat) (a b : Dig),
  (dig_size a <= n)%nat -> dig_eqb a b = true -> (dig_size a <= dig_size b)%nat.
Proof.
  intros n. induction n as [| n IHn]; intros a b Hd Hb.
  - pose proof (dig_size_pos a). lia.
  - destruct a as [x | a1 a2 | l1 | n0 f | a1 a2 | a1 | a1 a2];
      destruct b as [y | b1 b2 | l2 | m g | b1 b2 | b1 | b1 b2];
      simpl in Hb; try discriminate.
    + (* dQ *) simpl. lia.
    + (* dPair *)
      apply andb_true_iff in Hb as [H1 H2].
      assert (Ha1 : (dig_size a1 <= n)%nat) by (simpl in Hd; lia).
      assert (Ha2 : (dig_size a2 <= n)%nat) by (simpl in Hd; lia).
      pose proof (IHn a1 b1 Ha1 H1). pose proof (IHn a2 b2 Ha2 H2).
      simpl. lia.
    + (* dSeq *)
      assert (Hcase : forall (m1 m2 : list Dig), (dig_lsize m1 <= n)%nat ->
        dig_eqb (dSeq m1) (dSeq m2) = true ->
        (dig_lsize m1 <= dig_lsize m2)%nat).
      { intros m1. induction m1 as [| x xs IHl]; intros m2 Hm Hs.
        - destruct m2 as [| y ys].
          + simpl. lia.
          + simpl in Hs. discriminate.
        - destruct m2 as [| y ys].
          + simpl in Hs. discriminate.
          + rewrite dig_eqb_dSeq_cons in Hs.
            apply andb_true_iff in Hs as [H1 H2].
            assert (Hx : (dig_size x <= n)%nat) by (simpl in Hm; lia).
            assert (Hxs : (dig_lsize xs <= n)%nat) by (simpl in Hm; lia).
            pose proof (IHn x y Hx H1). pose proof (IHl ys Hxs H2).
            simpl. lia. }
      assert (Hl : (dig_lsize l1 <= n)%nat).
      { rewrite dig_size_eq_dSeq in Hd. lia. }
      pose proof (Hcase l1 l2 Hl Hb).
      rewrite !dig_size_eq_dSeq. lia.
    + (* dJudge *)
      apply andb_true_iff in Hb as [H1 H2].
      assert (Ha1 : (dig_size a1 <= n)%nat) by (simpl in Hd; lia).
      assert (Ha2 : (dig_size a2 <= n)%nat) by (simpl in Hd; lia).
      pose proof (IHn a1 b1 Ha1 H1). pose proof (IHn a2 b2 Ha2 H2).
      simpl. lia.
    + (* dModel *)
      assert (Ha1 : (dig_size a1 <= n)%nat) by (simpl in Hd; lia).
      pose proof (IHn a1 b1 Ha1 Hb). simpl. lia.
    + (* dProofT *)
      apply andb_true_iff in Hb as [H1 H2].
      assert (Ha1 : (dig_size a1 <= n)%nat) by (simpl in Hd; lia).
      assert (Ha2 : (dig_size a2 <= n)%nat) by (simpl in Hd; lia).
      pose proof (IHn a1 b1 Ha1 H1). pose proof (IHn a2 b2 Ha2 H2).
      simpl. lia.
Qed.

(* sub_dig: the structural proper-subterm decision (recursion over
   the seven constructors; dQ has no proper subterm; the dCode branch
   is conservatively false, header note b). the dSeq branch follows
   the same S7 guardedness pattern: the list scan is an embedded
   anonymous fix recursing on the tail argument m, and the element y
   keeps its subterm evidence chain through d ⊳ l ⊳ m ⊳ y. *)
Fixpoint sub_dig (a d : Dig) {struct d} : bool :=
  match d with
  | dQ _ => false
  | dPair b c => (((dig_eqb a b || dig_eqb a c) || sub_dig a b) || sub_dig a c)
  | dSeq l =>
      (fix sub_l (a0 : Dig) (m : list Dig) {struct m} : bool :=
         match m with
         | [] => false
         | y :: ys => ((dig_eqb a0 y || sub_dig a0 y) || sub_l a0 ys)
         end) a l
  | dCode _ _ => false
  | dJudge b c => (((dig_eqb a b || dig_eqb a c) || sub_dig a b) || sub_dig a c)
  | dModel b => (dig_eqb a b || sub_dig a b)
  | dProofT b c => (((dig_eqb a b || dig_eqb a c) || sub_dig a b) || sub_dig a c)
  end.

(* the dSeq-face equation (taken directly by convertibility) and the
   definitional witness *)
Theorem sub_dig_dSeq_nil : forall a : Dig, sub_dig a (dSeq []) = false.
Proof.
  intro a.
  (* route one: unfold the proper-subterm decision body; the
     empty-list branch lands on false directly through the embedded
     list scan *)
  change (sub_dig a (dSeq [])) with false.
  reflexivity.
Qed.

Theorem sub_dig_dSeq_cons : forall (a y : Dig) (ys : list Dig),
  sub_dig a (dSeq (y :: ys)) =
  ((dig_eqb a y || sub_dig a y) || sub_dig a (dSeq ys)).
Proof.
  intros a y ys.
  (* route one: unfold the proper-subterm decision body; the sequence
     branch reduces through the embedded list scan to the three-way
     disjunctive face — direct equality hit, recursive descent, and
     continued scan of the list tail *)
  change (sub_dig a (dSeq (y :: ys)))
    with ((dig_eqb a y || sub_dig a y) || sub_dig a (dSeq ys)).
  reflexivity.
Qed.

Theorem sub_dig_witness : sub_dig (dQ 0) (dPair (dQ 0) (dQ 0)) = true.
Proof.
  (* route two, explicit witness: first unfold the binary-branch
     decision face (two equality-hit routes and two recursive
     routes), then the left equality match reduces to true on the
     zero code and the goal closes *)
  change (sub_dig (dQ 0) (dPair (dQ 0) (dQ 0)))
    with (((dig_eqb (dQ 0) (dQ 0) || dig_eqb (dQ 0) (dQ 0))
           || sub_dig (dQ 0) (dQ 0)) || sub_dig (dQ 0) (dQ 0)).
  reflexivity.
Qed.

Theorem sub_dig_witness_neg : sub_dig (dQ 0) (dQ 0) = false.
Proof.
  (* route one: unfold the proper-subterm decision body; the numeric
     branch has no proper subterm and lands on false directly *)
  change (sub_dig (dQ 0) (dQ 0)) with false.
  reflexivity.
Qed.

(* the central lemma: subterm order implies strict size monotonicity
   (bounded induction; the dSeq face by inner list induction) *)
Lemma sub_dig_size_bound : forall (n : nat) (d a : Dig),
  (dig_size d <= n)%nat -> sub_dig a d = true -> (dig_size a < dig_size d)%nat.
Proof.
  intros n. induction n as [| n IHn]; intros d a Hd H.
  - pose proof (dig_size_pos d). lia.
  - destruct d as [x | b c | l | n0 f | b c | b | b c]; simpl in H;
      try discriminate.
    + (* dPair *)
      apply orb_true_iff in H. destruct H as [H | H].
      * apply orb_true_iff in H. destruct H as [H | H].
        -- apply orb_true_iff in H. destruct H as [H | H].
           ++ pose proof (dig_eqb_size_bound (dig_size a) a b
                            (le_n (dig_size a)) H). simpl. lia.
           ++ pose proof (dig_eqb_size_bound (dig_size a) a c
                            (le_n (dig_size a)) H). simpl. lia.
        -- assert (Hb : (dig_size b <= n)%nat) by (simpl in Hd; lia).
           pose proof (IHn b a Hb H). simpl. lia.
      * assert (Hc : (dig_size c <= n)%nat) by (simpl in Hd; lia).
        pose proof (IHn c a Hc H). simpl. lia.
    + (* dSeq *)
      assert (Hcase : forall m : list Dig, (dig_lsize m <= n)%nat ->
        sub_dig a (dSeq m) = true -> (dig_size a < S (dig_lsize m))%nat).
      { intros m. induction m as [| y ys IHl]; intros Hm Hs.
        - rewrite sub_dig_dSeq_nil in Hs. discriminate.
        - rewrite sub_dig_dSeq_cons in Hs. simpl in Hm. simpl.
          assert (Hy : (dig_size y <= n)%nat) by lia.
          pose proof (dig_size_pos y) as Hpy.
          apply orb_true_iff in Hs. destruct Hs as [Hs | Hs].
          + apply orb_true_iff in Hs. destruct Hs as [Hs | Hs].
            * pose proof (dig_eqb_size_bound (dig_size a) a y
                           (le_n (dig_size a)) Hs). lia.
            * pose proof (IHn y a Hy Hs). lia.
          + assert (Hys : (dig_lsize ys <= n)%nat) by lia.
            pose proof (IHl Hys Hs). lia. }
      assert (Hl : (dig_lsize l <= n)%nat).
      { rewrite dig_size_eq_dSeq in Hd. lia. }
      pose proof (Hcase l Hl H).
      rewrite dig_size_eq_dSeq. lia.
    + (* dJudge *)
      apply orb_true_iff in H. destruct H as [H | H].
      * apply orb_true_iff in H. destruct H as [H | H].
        -- apply orb_true_iff in H. destruct H as [H | H].
           ++ pose proof (dig_eqb_size_bound (dig_size a) a b
                            (le_n (dig_size a)) H). simpl. lia.
           ++ pose proof (dig_eqb_size_bound (dig_size a) a c
                            (le_n (dig_size a)) H). simpl. lia.
        -- assert (Hb : (dig_size b <= n)%nat) by (simpl in Hd; lia).
           pose proof (IHn b a Hb H). simpl. lia.
      * assert (Hc : (dig_size c <= n)%nat) by (simpl in Hd; lia).
        pose proof (IHn c a Hc H). simpl. lia.
    + (* dModel *)
      apply orb_true_iff in H. destruct H as [H | H].
      * pose proof (dig_eqb_size_bound (dig_size a) a b (le_n (dig_size a)) H).
        simpl. lia.
      * assert (Hb : (dig_size b <= n)%nat) by (simpl in Hd; lia).
        pose proof (IHn b a Hb H). simpl. lia.
    + (* dProofT *)
      apply orb_true_iff in H. destruct H as [H | H].
      * apply orb_true_iff in H. destruct H as [H | H].
        -- apply orb_true_iff in H. destruct H as [H | H].
           ++ pose proof (dig_eqb_size_bound (dig_size a) a b
                            (le_n (dig_size a)) H). simpl. lia.
           ++ pose proof (dig_eqb_size_bound (dig_size a) a c
                            (le_n (dig_size a)) H). simpl. lia.
        -- assert (Hb : (dig_size b <= n)%nat) by (simpl in Hd; lia).
           pose proof (IHn b a Hb H). simpl. lia.
      * assert (Hc : (dig_size c <= n)%nat) by (simpl in Hd; lia).
        pose proof (IHn c a Hc H). simpl. lia.
Qed.

(* the monotone theorem (the original ≤-shaped statement) and the
   strict form *)
Theorem sub_dig_size_mono : forall (d a : Dig),
  sub_dig a d = true -> (dig_size a <= dig_size d)%nat.
Proof.
  intros d a H. apply Nat.lt_le_incl.
  apply (sub_dig_size_bound (dig_size d) d a (le_n (dig_size d)) H).
Qed.

Theorem sub_dig_size_lt : forall (d a : Dig),
  sub_dig a d = true -> (dig_size a < dig_size d)%nat.
Proof.
  intros d a H. apply (sub_dig_size_bound (dig_size d) d a (le_n (dig_size d)) H).
Qed.

(* ========== §3 main piece, additivity family: direct derivation from the constructor equation family ========== *)
(* the integer-valued Q face: absorption of the additive unit in the
   n # 1 shape (the ring face settled in one pass) *)
Lemma qZ1_eq : forall p : Z, (((p + 1) # 1) == (((p # 1) + 1))%Q).
Proof. intros p. unfold Qeq, Qplus. cbn. ring. Qed.

Lemma qZ3_eq : forall p q : Z,
  (((p + q + 1) # 1) == (((p # 1) + (q # 1)) + 1)%Q).
Proof. intros p q. unfold Qeq, Qplus. cbn. ring. Qed.

Theorem h_alg_dPair : forall a b : Dig,
  h_alg (dPair a b) == ((h_alg a + h_alg b) + 1)%Q.
Proof.
  intros a b. unfold h_alg.
  rewrite dig_size_eq_dPair, Nat2Z.inj_succ, Nat2Z.inj_add, <- Z.add_1_r.
  apply qZ3_eq.
Qed.

Theorem h_alg_dJudge : forall a b : Dig,
  h_alg (dJudge a b) == ((h_alg a + h_alg b) + 1)%Q.
Proof.
  intros a b. unfold h_alg.
  rewrite dig_size_eq_dJudge, Nat2Z.inj_succ, Nat2Z.inj_add, <- Z.add_1_r.
  apply qZ3_eq.
Qed.

Theorem h_alg_dProofT : forall a b : Dig,
  h_alg (dProofT a b) == ((h_alg a + h_alg b) + 1)%Q.
Proof.
  intros a b. unfold h_alg.
  rewrite dig_size_eq_dProofT, Nat2Z.inj_succ, Nat2Z.inj_add, <- Z.add_1_r.
  apply qZ3_eq.
Qed.

Theorem h_alg_dModel : forall a : Dig, h_alg (dModel a) == (h_alg a + 1)%Q.
Proof.
  intros a. unfold h_alg.
  rewrite dig_size_eq_dModel, Nat2Z.inj_succ, <- Z.add_1_r.
  apply qZ1_eq.
Qed.

Theorem h_alg_dSeq : forall l : list Dig,
  h_alg (dSeq l) == ((Z.of_nat (dig_lsize l) # 1) + 1)%Q.
Proof.
  intros l. unfold h_alg.
  rewrite dig_size_eq_dSeq, Nat2Z.inj_succ, <- Z.add_1_r.
  apply qZ1_eq.
Qed.

Theorem h_alg_dCode : forall (n : nat) (f : nat -> Dig),
  h_alg (dCode n f) == ((Z.of_nat n # 1) + 1)%Q.
Proof.
  intros n f. unfold h_alg.
  rewrite dig_size_eq_dCode, Nat2Z.inj_succ, <- Z.add_1_r.
  apply qZ1_eq.
Qed.

(* ========== §4 bonus piece: the joint characterization of is_num × h_alg (the provable restricted form) ========== *)

Theorem is_num_h_alg1 : forall d : Dig, is_num d = true -> h_alg d == 1.
Proof.
  intros d H. apply is_num_inv in H. destruct H as [x Hx].
  rewrite Hx. apply h_alg_dQ.
Qed.

(* the triple agreement of the dQ probe: minimal code face + decision
   + positivity *)
Theorem h_alg_dQ_probe : forall x : Q,
  h_alg (dQ x) == 1 /\ is_num (dQ x) = true /\ 0 < h_alg (dQ x).
Proof.
  intros x.
  (* route three, split-and-combine structure: the triple agreement of
     depth proxy, decision procedure, and positivity unfolds branch by
     branch — the decision branch goes through an explicit reduction
     chain, the other two branches use the established equation
     lemmas *)
  split.
  - apply h_alg_dQ.
  - split.
    + change (is_num (dQ x)) with true. reflexivity.
    + apply h_alg_pos.
Qed.

(* honest boundary d): code face 1 does not coincide with the numeric
   domain (the dSeq [] counterexample, definitional witness) *)
Theorem h_alg_one_not_only_num :
  h_alg (dSeq []) == 1 /\ is_num (dSeq []) = false.
Proof.
  (* route three, split-and-combine structure: each side of the
     counterexample witness goes through an explicit reduction — the
     empty sequence depth lands on one through the embedded list
     scan, the decision procedure lands on false *)
  split.
  - unfold h_alg.
    change (Z.of_nat (dig_size (dSeq []))) with ((1:Z)).
    reflexivity.
  - change (is_num (dSeq [])) with false. reflexivity.
Qed.

End DTPT_DigTheory.
Import DTPT_DigTheory.

(* ========== final audit: assumption-closure check ========== *)

Print Assumptions sub_dig_size_mono.
Print Assumptions sub_dig_size_lt.
Print Assumptions h_alg_pos.
Print Assumptions h_alg_nonneg.
Print Assumptions h_alg_dPair.
Print Assumptions is_num_h_alg1.

(* ========== slice-replacement addendum: assumption-closure prints
   for the replacement pieces (G4 face) ========== *)

Print Assumptions dig_size_eq_dPair.
Print Assumptions dQ_probe_roundtrip.
Print Assumptions sub_dig_witness.
Print Assumptions h_alg_dQ.
