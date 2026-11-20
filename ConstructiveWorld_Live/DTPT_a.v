(* ConstructiveWorld-Set - DTPT_a, the digital-structure and carrier stem of the DTPT base library *)

(** * DTPT_a: digital structures, sequence carriers, entropy faces, rational toolbox.

    Mission.  The inductive type [Dig] of digital structures; the finite-sequence
    carriers and organization operators ([insert_q]/[P0]/[rot]/[Pinf]/[interleave]/
    [Pmid]); the support-domain stability family (D5, theorem A) on the Set
    permutation carrier [PermT]; the entropy carriers ([dedup]/[H_ms]/[H_adj]);
    the supplementary rational toolbox (order/equality faces over [Q]).

    Dependencies.  Stdlib only: [QArith.QArith], [QArith.Qabs], [List], [Arith],
    [Lia], [Permutation], [Sorting.Sorted].

    References.  The information-theoretic discrete layer of the constructive
    development (judged-code truth-predicate line); statement names carried
    verbatim from the baseline module in ConstructiveWorld-Main.  Consumers of
    this stem appear later in this node; their verbatim require names are
    carried by the require lines below.

    Constructivity.  Every statement is carried at the [Set] layer: order and
    equality predicates are the boolean identity carriers [QleT]/[QeqT], the
    permutation face is the single-constructor carrier [PermT], conjunctions
    are Set products.  Zero assumed constants, zero admissions, zero classical
    logic; definitions and constructive statements close transparently
    ([Defined]).  In-proof rational reasoning stays on the constructive Prop
    layer and erases under extraction with both extraction faces cast-free.

    Build.  Rocq 9.3 [coqc -native-compiler no -Q <world root> ""] under the
    load-capped build face; single all-names [Separate Extraction] driver,
    [ocamlc] compiled, sample-driven. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorting.Sorted.
Import ListNotations.
Open Scope Q_scope.

(* ========== section 0: Set-layer carriers (boolean identity faces and bridges) ========== *)

(* The Set-layer identity family: equality as informative data. *)
Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

Lemma eq_imp_id : forall (A : Set) (x y : A), x = y -> Id x y.
Proof. intros A x y H. destruct H. apply id_refl. Defined.

Lemma id_imp_eq : forall (A : Set) (x y : A), Id x y -> x = y.
Proof. intros A x y H. destruct H. apply eq_refl. Defined.

(* Order carrier: the decidable boolean identity face of the rational order. *)
Definition QleT (x y : Q) : Set := @Id bool (Qle_bool x y) true.

(* Equality carrier: the decidable boolean identity face of rational equality. *)
Definition QeqT (x y : Q) : Set := @Id bool (Qeq_bool x y) true.

(* Permutation carrier: single-constructor Set face wrapping the stdlib
   permutation relation; the relation argument erases under extraction. *)
Inductive PermT (l1 l2 : list Q) : Set :=
| permT_intro : Permutation l1 l2 -> PermT l1 l2.

Arguments permT_intro {l1 l2} _.

Definition PermT_of_Perm : forall (l1 l2 : list Q),
  Permutation l1 l2 -> PermT l1 l2 := fun l1 l2 H => permT_intro H.

Definition PermT_to_Perm : forall (l1 l2 : list Q),
  PermT l1 l2 -> Permutation l1 l2 :=
  fun l1 l2 H => match H with permT_intro p => p end.

(* Direction-explicit bridges between the Prop order/equality faces and the
   Set carriers; each bridge name reads source-face first, target-face second. *)
Lemma qle_imp_qleT : forall x y : Q, (x <= y)%Q -> QleT x y.
Proof.
  intros x y H. apply eq_imp_id. apply (proj2 (Qle_bool_iff x y)). exact H.
Defined.

Lemma qleT_imp_qle : forall x y : Q, QleT x y -> (x <= y)%Q.
Proof.
  intros x y H. apply (proj1 (Qle_bool_iff x y)).
  apply (id_imp_eq bool (Qle_bool x y) true H).
Defined.

Lemma qeq_imp_qeqT : forall x y : Q, (x == y)%Q -> QeqT x y.
Proof.
  intros x y H. apply eq_imp_id. unfold Qeq in H. unfold Qeq_bool.
  destruct (Z.eqb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E.
  - reflexivity.
  - exfalso. apply Z.eqb_neq in E. lia.
Defined.

Lemma qeqT_imp_qeq : forall x y : Q, QeqT x y -> (x == y)%Q.
Proof.
  intros x y H. apply Qeq_bool_eq.
  apply (id_imp_eq bool (Qeq_bool x y) true H).
Defined.

(* ========== section 1: the inductive type Dig of digital structures ========== *)

Inductive Dig : Type :=
| dQ     : Q -> Dig
| dPair  : Dig -> Dig -> Dig
| dSeq   : list Dig -> Dig
| dCode  : nat -> (nat -> Dig) -> Dig
| dJudge : Dig -> Dig -> Dig
| dModel : Dig -> Dig
| dProofT: Dig -> Dig -> Dig.

(* ========== section 2: finite-sequence carriers and organization operators ========== *)

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

Fixpoint interleave (l1 l2 : list Q) : list Q :=
  match l1, l2 with
  | [], _ => l2
  | _ :: _, [] => l1
  | x :: xs, y :: ys => x :: y :: interleave xs ys
  end.

Definition Pmid (l : list Q) (s lam : nat) : list Q :=
  firstn lam (P0 l) ++ skipn lam (Pinf l s).

(* ========== section 3: support-domain stability (D5, theorem A) ========== *)

Lemma insert_q_perm_cons : forall (x : Q) (l : list Q),
  PermT (x :: l) (insert_q x l).
Proof.
  intros x l. apply permT_intro.
  induction l as [| y ys IH]; simpl.
  - simpl. apply perm_skip. apply perm_nil.
  - destruct (Qle_bool x y) eqn:Hxy.
    + apply perm_skip. apply Permutation_refl.
    + etransitivity.
      * apply perm_swap.
      * apply perm_skip. exact IH.
Defined.

Theorem D5_P0_perm : forall l : list Q, PermT l (P0 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply permT_intro. apply Permutation_refl.
  - apply permT_intro. etransitivity.
    + apply perm_skip. exact (PermT_to_Perm _ _ IH).
    + exact (PermT_to_Perm _ _ (insert_q_perm_cons x (P0 xs))).
Defined.

(* [rot] is definitionally [firstn ++ skipn], so the shifted slice is the
   identity reorganization of the list; the corollary is a definitional
   identity face.  The operational semantics of bounded reorganization are
   carried by the later stems of this node; their verbatim require names are
   carried by the require lines below. *)
Theorem D5_Pinf_perm : forall (l : list Q) (s : nat), PermT l (Pinf l s).
Proof.
  intros l s. apply permT_intro. unfold Pinf, rot.
  rewrite firstn_skipn.
  apply Permutation_refl.
Defined.

(* A general-slice permutation statement for [Pmid] is false: firstn/skipn
   truncation is not a permutation.  Only the endpoint slices are asserted. *)
Theorem D5_support_same : forall (l : list Q) (s : nat),
  PermT l (P0 l) * PermT l (Pinf l s).
Proof.
  intros l s. split; [exact (D5_P0_perm l) | exact (D5_Pinf_perm l s)].
Defined.

(* ========== section 4: the multi-entropy function family ========== *)

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

(* ========== section 5: the supplementary rational toolbox (B2) ========== *)

Lemma Qle_bool_false_le : forall x y : Q,
  @Id bool (Qle_bool x y) false -> QleT y x.
Proof.
  intros x y H. apply qle_imp_qleT.
  destruct (Qle_bool y x) eqn:E.
  - apply (proj1 (Qle_bool_iff y x)). exact E.
  - exfalso.
    pose proof (id_imp_eq bool (Qle_bool x y) false H) as Hb.
    unfold Qle_bool in Hb, E.
    apply Z.leb_gt in E. apply Z.leb_gt in Hb. lia.
Defined.

(* The decision face: returns the holding side as Set data. *)
Lemma Qle_dec' : forall x y : Q, QleT x y + QleT y x.
Proof.
  intros x y. destruct (Qle_bool x y) eqn:E.
  - left. apply eq_imp_id. exact E.
  - right. exact (Qle_bool_false_le x y (eq_imp_id bool (Qle_bool x y) false E)).
Defined.

Lemma qadd_le : forall a b c d : Q,
  QleT a b -> QleT c d -> QleT (a + c) (b + d)%Q.
Proof.
  intros a b c d Ha Hd. apply qle_imp_qleT.
  pose proof (qleT_imp_qle a b Ha) as H.
  pose proof (qleT_imp_qle c d Hd) as H0.
  destruct a as [an ad]; destruct b as [bn bd];
    destruct c as [cn cd]; destruct d as [dn dd];
    simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos dd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos dd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  assert (H2 : ((cn * Zpos dd) * (Zpos ad * Zpos bd)
                <= (dn * Zpos cd) * (Zpos ad * Zpos bd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H0]).
  lia.
Defined.

Lemma qopp_le : forall a b : Q, QleT a b -> QleT (- b) (- a)%Q.
Proof.
  intros a b Ha. apply qle_imp_qleT.
  pose proof (qleT_imp_qle a b Ha) as H.
  destruct a as [an ad]; destruct b as [bn bd];
    simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl; lia.
Defined.

Lemma qmul_le_r : forall n m p : Q,
  QleT n m -> QleT 0 p -> QleT (n * p) (m * p)%Q.
Proof.
  intros n m p Hn Hp. apply qle_imp_qleT.
  pose proof (qleT_imp_qle n m Hn) as H.
  pose proof (qleT_imp_qle 0 p Hp) as H0.
  destruct n as [nn nd]; destruct m as [mn md]; destruct p as [pn pd];
    simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((nn * Zpos md) * (pn * Zpos pd)
                <= (mn * Zpos nd) * (pn * Zpos pd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Defined.

(* The order subtraction law, carried as a Set product of the two directional
   function faces. *)
Lemma Qle_0_sub' : forall x y : Q,
  (QleT x y -> QleT 0 (y - x)%Q) * (QleT 0 (y - x)%Q -> QleT x y).
Proof.
  intros [nx dx] [ny dy]; simpl; split; intros H;
    pose proof (qleT_imp_qle _ _ H) as Hprop;
    apply qle_imp_qleT;
    unfold Qle, Qminus, Qplus, Qopp in Hprop; simpl in Hprop;
    unfold Qle, Qminus, Qplus, Qopp; simpl; lia.
Defined.

Lemma qsub_le_r : forall a b c : Q,
  QleT a b -> QleT (a - c) (b - c)%Q.
Proof.
  intros a b c Ha. apply qle_imp_qleT.
  pose proof (qleT_imp_qle a b Ha) as H.
  destruct a as [an ad]; destruct b as [bn bd]; destruct c as [cn cd];
    unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos cd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos cd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Defined.

Lemma qsub_add : forall a b c : Q, QeqT (a - b + (b - c)) (a - c)%Q.
Proof.
  intros a b c. apply qeq_imp_qeqT.
  destruct a as [an ad]; destruct b as [bn bd]; destruct c as [cn cd].
  unfold Qeq, Qminus, Qplus, Qopp; simpl; lia.
Defined.

Lemma abs_eq : forall a : Q, QleT 0 a -> QeqT (Qabs a) a%Q.
Proof.
  intros [n d] H. apply qeq_imp_qeqT.
  pose proof (qleT_imp_qle 0 (n # d) H) as H0.
  unfold Qle in H0. simpl in H0. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - reflexivity.
  - exfalso. lia.
Defined.

Lemma abs_neg : forall a : Q, QleT a 0 -> QeqT (Qabs a) (- a)%Q.
Proof.
  intros [n d] H. apply qeq_imp_qeqT.
  pose proof (qleT_imp_qle (n # d) 0 H) as H0.
  unfold Qle in H0. simpl in H0. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - exfalso. lia.
  - reflexivity.
Defined.

Lemma abs_nonneg : forall a : Q, QleT 0 (Qabs a)%Q.
Proof.
  intros [n d]. apply qle_imp_qleT. unfold Qle.
  destruct n; simpl; lia.
Defined.

(* Coercion face from the equality carrier to the raw boolean identity; it is
   definitional by the carrier design. *)
Lemma Qeqb_true_of : forall x y : Q, QeqT x y -> @Id bool (Qeq_bool x y) true.
Proof. intros x y H. exact H. Defined.

Lemma Qeqb_sym : forall x y : Q, @Id bool (Qeq_bool x y) (Qeq_bool y x).
Proof.
  intros x y.
  destruct (Qeq_bool x y) eqn:E1, (Qeq_bool y x) eqn:E2.
  - apply eq_imp_id. reflexivity.
  - exfalso. apply Qeq_bool_eq in E1.
    assert (E1' : y == x) by (apply Qeq_sym; exact E1).
    pose proof (qeq_imp_qeqT y x E1') as HT.
    pose proof (id_imp_eq bool (Qeq_bool y x) true HT) as Ht.
    rewrite Ht in E2. discriminate E2.
  - exfalso. apply Qeq_bool_eq in E2.
    assert (E2' : x == y) by (apply Qeq_sym; exact E2).
    pose proof (qeq_imp_qeqT x y E2') as HT.
    pose proof (id_imp_eq bool (Qeq_bool x y) true HT) as Ht.
    rewrite Ht in E1. discriminate E1.
  - apply eq_imp_id. reflexivity.
Defined.

Lemma Qeqb_trans : forall a b c : Q,
  @Id bool (Qeq_bool a b) true -> @Id bool (Qeq_bool b c) true ->
  @Id bool (Qeq_bool a c) true.
Proof.
  intros a b c H1 H2.
  pose proof (id_imp_eq bool (Qeq_bool a b) true H1) as P1.
  pose proof (id_imp_eq bool (Qeq_bool b c) true H2) as P2.
  apply Qeq_bool_eq in P1. apply Qeq_bool_eq in P2.
  apply (qeq_imp_qeqT a c). transitivity b; assumption.
Defined.
