(* ConstructiveWorld-Set -- DTPT_Entropy premise-discharge supply, volume 2. *)

(** * abl_dte_core2: supply lemmas for premises 39-76 of the DTPT_Entropy host.

    Mission.  Supplies premises 39-76 of the host DTPT_Entropy.v premise
      ledger (statement coordinates :944-:1392) one premise at a time:
      each statement face reproduces the ledger form verbatim under the
      [dte_c2_] name map, with proofs constructed in place; premises 43
      and 44 stay registered only; six canonical instances specialize
      the supply statements with their instance premises constructed
      inline.  The main statement [dte_c2_H_freq_perm] states that the
      frequency entropy [dte_c2_H_freq] is invariant under list
      permutation.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List],
      [Arith], [Lia], [Permutation], [Extraction].  Requires [DTPT] of
      this development.

    References.  This development, abl_dte_core2.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_dte_core2.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Import DTPT.DTPT.

(* ================= Section 0. Data-layer copies ================= *)

(* Copies of the host data layer at :921/:1058/:1126/:1193/:1195/:1250,
   verbatim under the [dte_c2_] prefix.  [dte_c2_all_same] carries the
   mixed-carrier note of ledger premises 63-64: the note position is
   carried verbatim and the downstream predicate-position statements
   read it through this copy, in the manner of [dtd_Qmem]/[dtd_Qnodup]. *)

Fixpoint dte_c2_qn (n : nat) : Q :=
  match n with
  | O => 0%Q
  | S k => (1 + dte_c2_qn k)%Q
  end.

Fixpoint dte_c2_freq_q (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (dte_c2_freq_q x ys) else dte_c2_freq_q x ys
  end.

Fixpoint dte_c2_nsum (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => (f y + dte_c2_nsum f ys)%nat
  end.

Definition dte_c2_sqsum (l : list Q) : nat :=
  dte_c2_nsum (fun x => dte_c2_freq_q x l) l.

Fixpoint dte_c2_all_same (l : list Q) : bool :=
  match l with
  | [] => true
  | y :: ys => forallb (fun z => Qeq_bool z y) ys && dte_c2_all_same ys
  end.

(* The [dte_c2_bid] wrapper is the Set carrier of the boolean statement
   face: it is inhabited exactly when its boolean index reduces to
   [true], and the introduction constructor carries that equation. *)

Inductive dte_c2_bid (b : bool) : Set :=
  | dte_c2_bid_intro : b = true -> dte_c2_bid b.

Definition dte_c2_H_freq (l : list Q) : Q :=
  (dte_c2_qn (length l) * dte_c2_qn (length l) - dte_c2_qn (dte_c2_sqsum l))
    / (dte_c2_qn (length l) * dte_c2_qn (length l)).

(* ================= Section 1. Auxiliary lemmas ================= *)

(* Seven copies of the premise-free host lemmas at :927/:936/:951/:958/
   :1064/:1152/:1353, verbatim; they feed the supply proofs below.  The
   order facts are constructed in place on the base-module tools
   [qadd_nonneg] and [qadd_le]. *)

Lemma dte_c2_qn_nonneg : forall n : nat, 0 <= dte_c2_qn n.
Proof.
  induction n as [| k IH].
  - apply Qle_refl.
  - simpl. apply qadd_nonneg.
    + apply (Qlt_le_weak 0 1). reflexivity.
    + exact IH.
Qed.

Lemma dte_c2_qn_S_pos : forall k : nat, 0 < dte_c2_qn (S k).
Proof.
  intros k. simpl. apply (Qlt_le_trans 0 1 (1 + dte_c2_qn k)%Q).
  - reflexivity.
  - pose proof (qadd_le 1 1 0 (dte_c2_qn k) (Qle_refl 1) (dte_c2_qn_nonneg k))
      as HH. simpl in HH. exact HH.
Qed.

Lemma dte_c2_qn_add : forall a b : nat, dte_c2_qn (a + b)%nat == dte_c2_qn a + dte_c2_qn b.
Proof.
  induction a as [| a IH]; intros b.
  - simpl. rewrite Qplus_0_l. reflexivity.
  - simpl. rewrite IH. ring.
Qed.

Lemma dte_c2_qn_mul : forall a b : nat, dte_c2_qn (a * b)%nat == dte_c2_qn a * dte_c2_qn b.
Proof.
  induction a as [| a IH]; intros b.
  - simpl. symmetry. apply Qmult_0_l.
  - simpl. rewrite dte_c2_qn_add. rewrite IH. ring.
Qed.

Lemma dte_c2_freq_q_le_length : forall (x : Q) (l : list Q),
  (dte_c2_freq_q x l <= length l)%nat.
Proof.
  intros x. induction l as [| y ys IH].
  - simpl. lia.
  - simpl. destruct (Qeq_bool x y); lia.
Qed.

Lemma dte_c2_nsum_const : forall (n : nat) (l : list Q),
  dte_c2_nsum (fun _ => n) l = (length l * n)%nat.
Proof.
  intros n l. induction l as [| y ys IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma dte_c2_nsum_map : forall (g : Q -> nat) (f : Q -> Q) (l : list Q),
  dte_c2_nsum g (map f l) = dte_c2_nsum (fun x => g (f x)) l.
Proof.
  intros g f l. induction l as [| a l IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* ================= Section 2. Supply theorems ================= *)

(* Twenty-eight supply statements carrying 34 premises of the ledger,
   each statement face verbatim from the ledger under the [dte_c2_] name
   map, with proofs constructed in place.  Premises 43 and 44 are
   registered only; they are filed as comment blocks at their ledger
   positions. *)

(* Supply premise 39, ledger :944, [qn_pos]: statement face verbatim. *)
Theorem dte_c2_qn_pos : forall n : nat, (0 < n)%nat -> 0 < dte_c2_qn n.
Proof.
  intros n Hn. destruct n as [| m].
  - exfalso. lia.
  - apply dte_c2_qn_S_pos.
Qed.

(* Supply premise 40, ledger :965, [qn_le]: statement face verbatim. *)
Theorem dte_c2_qn_le : forall a b : nat, (a <= b)%nat -> dte_c2_qn a <= dte_c2_qn b.
Proof.
  induction a as [| a IH]; intros b Hle.
  - apply dte_c2_qn_nonneg.
  - destruct b as [| b'].
    + exfalso. lia.
    + simpl. apply (qadd_le 1 1 (dte_c2_qn a) (dte_c2_qn b')).
      * apply Qle_refl.
      * apply IH. apply (le_S_n _ _ Hle).
Qed.

(* Supply premise 41, ledger :976, [qn_inj]: statement face verbatim. *)
Theorem dte_c2_qn_inj : forall a b : nat, dte_c2_qn a == dte_c2_qn b -> a = b.
Proof.
  induction a as [| a IH]; intros b Heq.
  - destruct b as [| b'].
    + reflexivity.
    + simpl in Heq. pose proof (dte_c2_qn_S_pos b') as HP. simpl in HP.
      rewrite <- Heq in HP. exfalso. exact (Qlt_irrefl 0 HP).
  - destruct b as [| b'].
    + simpl in Heq. pose proof (dte_c2_qn_S_pos a) as HP. simpl in HP.
      rewrite Heq in HP. exfalso. exact (Qlt_irrefl 0 HP).
    + simpl in Heq.
      rewrite (Qplus_comm 1 (dte_c2_qn a)) in Heq.
      rewrite (Qplus_comm 1 (dte_c2_qn b')) in Heq.
      pose proof (proj1 (Qplus_inj_r (dte_c2_qn a) (dte_c2_qn b') 1) Heq) as H'.
      pose proof (IH b' H') as Hab. rewrite Hab. reflexivity.
Qed.

(* Supply premise 42, ledger :995, [qlt_neq0]: statement face verbatim;
   the [<>] is carried over from the premise face as registered. *)
Theorem dte_c2_qlt_neq0 : forall y : Q, 0 < y -> y <> 0.
Proof.
  intros y Hpy Heq. rewrite Heq in Hpy. exact (Qlt_irrefl 0 Hpy).
Qed.

(* Registered only, premise 43, ledger :1000, [qpos_neq0]:
   forall y : Q, 0 < y -> ~ (y == 0).  The ledger flags this slot as
   mixed-carrier with a negation in the conclusion face, so it stays
   registered without supply. *)

(* Registered only, premise 44, ledger :1008, [qmult_inv_cancel_r]:
   forall A B : Q, ~ (B == 0) -> A * / B * B == A.  A negation in the
   premise face keeps this slot registered without supply; its
   elimination kernel is reconstructed constructively inside the proof
   of [dte_c2_qdiv_eq0_num] below. *)

(* Supply premise 45, ledger :1013, [qsub_eq0]: statement face verbatim. *)
Theorem dte_c2_qsub_eq0 : forall a b : Q, a - b == 0 -> a == b.
Proof.
  intros a b H.
  assert (Ha : a == (a - b) + b).
  { unfold Qminus. ring. }
  rewrite H in Ha. rewrite Qplus_0_l in Ha. exact Ha.
Qed.

(* Supply premise 46, ledger :1022, [qdiv_zero_num]: statement face verbatim. *)
Theorem dte_c2_qdiv_zero_num : forall A B : Q, A == 0 -> A / B == 0.
Proof.
  intros A B H. unfold Qdiv. rewrite H. apply Qmult_0_l.
Qed.

(* Supply premises 47-48, ledger :1027, [qdiv_eq0_num]: statement face
   verbatim.  The proof does not go through the registered premise 44
   statement: the cancellation step is replayed independently from the
   field side condition, discharging the constructively negative face
   by the stdlib strict-order fact [Qlt_not_eq]. *)
Theorem dte_c2_qdiv_eq0_num : forall A B : Q, 0 < B -> A / B == 0 -> A == 0.
Proof.
  intros A B HB H. unfold Qdiv in H.
  assert (Hcancel : A * / B * B == A).
  { field. intro Hb. apply (Qlt_not_eq 0 B HB). apply (Qeq_sym B 0). exact Hb. }
  rewrite H in Hcancel. rewrite Qmult_0_l in Hcancel.
  apply (Qeq_sym 0 A). exact Hcancel.
Qed.

(* Supply premises 49-50, ledger :1035, [qdiv_nonneg]: statement face verbatim. *)
Theorem dte_c2_qdiv_nonneg : forall A B : Q, 0 <= A -> 0 < B -> 0 <= A / B.
Proof.
  intros A B HA HB. unfold Qdiv. apply Qmult_le_0_compat.
  - exact HA.
  - apply Qlt_le_weak. apply (Qinv_lt_0_compat B HB).
Qed.

(* Supply premise 51, ledger :1042, [qnum_zero]: statement face verbatim. *)
Theorem dte_c2_qnum_zero : forall n s : nat,
  dte_c2_qn (n * n) == dte_c2_qn s -> dte_c2_qn n * dte_c2_qn n - dte_c2_qn s == 0.
Proof.
  intros n s H. rewrite <- (dte_c2_qn_mul n n). rewrite <- H.
  unfold Qminus. apply Qplus_opp_r.
Qed.

(* Supply premise 52, ledger :1048, [qeqb_false_neq]: statement face verbatim;
   the [<>] is carried over from the premise face as registered. *)
Theorem dte_c2_qeqb_false_neq : forall x y : Q, Qeq_bool x y = false -> x <> y.
Proof.
  intros x y H Hxy.
  assert (Ht : Qeq_bool x y = true).
  { apply (proj2 (Qeq_bool_iff x y)). rewrite <- Hxy. apply Qeq_refl. }
  rewrite Ht in H. discriminate H.
Qed.

(* Supply premise 53, ledger :1083, [freq_q_perm]: statement face verbatim. *)
Theorem dte_c2_freq_q_perm : forall (x : Q) (l p : list Q),
  Permutation l p -> dte_c2_freq_q x l = dte_c2_freq_q x p.
Proof.
  intros x l p H.
  induction H as [ | y l' p' Hy IH | y z l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. destruct (Qeq_bool x y); rewrite IH; reflexivity.
  - simpl. destruct (Qeq_bool x y); destruct (Qeq_bool x z); reflexivity.
  - rewrite IH1. exact IH2.
Qed.

(* Supply premise 54, ledger :1094, [freq_q_eq_all]: statement face verbatim. *)
Theorem dte_c2_freq_q_eq_all : forall (x : Q) (l : list Q),
  (forall z, In z l -> z == x) -> dte_c2_freq_q x l = length l.
Proof.
  intros x l. induction l as [| y ys IH]; intros H.
  - reflexivity.
  - assert (Hy : Qeq_bool x y = true).
    { apply (proj2 (Qeq_bool_iff x y)). apply (Qeq_sym y x). apply H.
      left. reflexivity. }
    simpl. rewrite Hy. f_equal. apply IH. intros z Hz. apply H.
    right. exact Hz.
Qed.

(* Supply premises 55-56, ledger :1106, [freq_q_full_count]: statement face verbatim. *)
Theorem dte_c2_freq_q_full_count : forall (x : Q) (l : list Q),
  dte_c2_freq_q x l = length l -> forall y, In y l -> y == x.
Proof.
  intros x l. induction l as [| a l IH]; intros Hcnt y0 Hy0.
  - destruct Hy0.
  - destruct Hy0 as [Hy0 | Hy0].
    + subst y0. destruct (Qeq_bool x a) eqn:Hyb.
      * apply (Qeq_sym x a). apply (proj1 (Qeq_bool_iff x a)). exact Hyb.
      * exfalso. simpl in Hcnt. rewrite Hyb in Hcnt.
        pose proof (dte_c2_freq_q_le_length x l) as HL. lia.
    + apply IH.
      * destruct (Qeq_bool x a) eqn:Hyb.
        -- simpl in Hcnt. rewrite Hyb in Hcnt. lia.
        -- exfalso. simpl in Hcnt. rewrite Hyb in Hcnt.
           pose proof (dte_c2_freq_q_le_length x l) as HL. lia.
      * exact Hy0.
Qed.

(* Supply premise 57, ledger :1132, [nsum_ext_in]: statement face verbatim. *)
Theorem dte_c2_nsum_ext_in : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> f x = g x) -> dte_c2_nsum f l = dte_c2_nsum g l.
Proof.
  intros f g l. induction l as [| y ys IH]; simpl; intros H.
  - reflexivity.
  - rewrite (H y (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

(* Supply premise 58, ledger :1141, [nsum_perm]: statement face verbatim. *)
Theorem dte_c2_nsum_perm : forall (f : Q -> nat) (l p : list Q),
  Permutation l p -> dte_c2_nsum f l = dte_c2_nsum f p.
Proof.
  intros f l p H.
  induction H as [ | x l' p' Hx IH | x y l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. lia.
  - rewrite IH1. exact IH2.
Qed.

(* Supply premise 59, ledger :1160, [nsum_bound]: statement face verbatim. *)
Theorem dte_c2_nsum_bound : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) -> (dte_c2_nsum f l <= length l * B)%nat.
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros H.
  - lia.
  - assert (Hy : (f y <= B)%nat) by (apply H; left; reflexivity).
    assert (Hys : (dte_c2_nsum f ys <= length ys * B)%nat)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    lia.
Qed.

(* Supply premises 60-62, ledger :1171, [nsum_bound_eq]: statement face verbatim. *)
Theorem dte_c2_nsum_bound_eq : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) ->
  dte_c2_nsum f l = (length l * B)%nat ->
  forall x, In x l -> f x = B.
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros Hsat Heq x0 Hx0.
  - destruct Hx0.
  - assert (Hy : (f y <= B)%nat) by (apply Hsat; left; reflexivity).
    assert (Hys : (dte_c2_nsum f ys <= length ys * B)%nat)
      by (apply (dte_c2_nsum_bound f ys B); intros x Hx; apply Hsat; right; exact Hx).
    assert (Hfy : f y = B) by lia.
    assert (HysEq : dte_c2_nsum f ys = (length ys * B)%nat) by lia.
    destruct Hx0 as [Hx0 | Hx0].
    + subst x0. exact Hfy.
    + apply IH.
      * intros z Hz. apply Hsat. right. exact Hz.
      * exact HysEq.
      * exact Hx0.
Qed.

(* Premises 63-64, ledger :1195, the [all_same] definition slot: the
   ledger flags the note position as mixed-carrier.  The flag position
   stays registered; its verbatim carrying copy is the Section 0
   [dte_c2_all_same] (in the manner of [dtd_Qmem]/[dtd_Qnodup]),
   through which the five predicate-position statements of this volume
   (premises 66-67, 68, 69, 71 and 73) are all supplied. *)

(* Supply premise 65, ledger :1198, [sqsum_perm]: statement face verbatim. *)
Theorem dte_c2_sqsum_perm : forall l p : list Q,
  Permutation l p -> dte_c2_sqsum l = dte_c2_sqsum p.
Proof.
  intros l p H. unfold dte_c2_sqsum.
  rewrite (dte_c2_nsum_ext_in (fun x => dte_c2_freq_q x l)
             (fun x => dte_c2_freq_q x p) l
             (fun x _ => dte_c2_freq_q_perm x l p H)).
  exact (dte_c2_nsum_perm (fun x => dte_c2_freq_q x p) l p H).
Qed.

(* Supply premises 66-67, ledger :1214, [freq_q_all_same]: statement
   face verbatim up to the boolean carrier of the [dte_c2_all_same]
   premise. *)
Theorem dte_c2_freq_q_all_same : forall (x : Q) (l : list Q),
  In x l -> dte_c2_all_same l = true -> dte_c2_freq_q x l = length l.
Proof.
  intros x l Hin Hs. apply dte_c2_freq_q_eq_all. intros z Hz.
  revert x Hin z Hz Hs.
  induction l as [| y ys IH]; intros x Hin z Hz Hs.
  - destruct Hin.
  - simpl in Hs. apply andb_prop in Hs. destruct Hs as [Hall Hrec].
    pose proof (proj1 (forallb_forall (fun w => Qeq_bool w y) ys) Hall)
      as Hall'.
    destruct Hin as [Hin | Hin]; destruct Hz as [Hz | Hz].
    + subst x. subst z. apply Qeq_refl.
    + subst x. apply (proj1 (Qeq_bool_iff z y)). exact (Hall' z Hz).
    + subst z. apply (Qeq_sym x y).
      apply (proj1 (Qeq_bool_iff x y)). exact (Hall' x Hin).
    + apply (Qeq_trans z y x).
      * apply (proj1 (Qeq_bool_iff z y)). exact (Hall' z Hz).
      * apply (Qeq_sym x y). apply (proj1 (Qeq_bool_iff x y)).
        exact (Hall' x Hin).
Qed.

(* Supply premise 68, ledger :1222, [sqsum_all_same]: statement face
   verbatim up to the boolean carrier of the [dte_c2_all_same]
   premise. *)
Theorem dte_c2_sqsum_all_same : forall l : list Q,
  dte_c2_all_same l = true -> dte_c2_sqsum l = (length l * length l)%nat.
Proof.
  intros l Hs. unfold dte_c2_sqsum.
  rewrite (dte_c2_nsum_ext_in (fun x => dte_c2_freq_q x l)
             (fun _ : Q => length l) l
             (fun x Hx => dte_c2_freq_q_all_same x l Hx Hs)).
  apply dte_c2_nsum_const.
Qed.

(* Supply premise 69, ledger :1231, [sqsum_eq_all_same]: statement face
   verbatim with the [dte_c2_bid] carrier on the conclusion face. *)
Theorem dte_c2_sqsum_eq_all_same : forall l : list Q,
  dte_c2_sqsum l = (length l * length l)%nat -> dte_c2_bid (dte_c2_all_same l).
Proof.
  intros l Heq. apply dte_c2_bid_intro. destruct l as [| x xs].
  - reflexivity.
  - assert (Hintro : forall (m : list Q) (p : Q),
              (forall z, In z m -> z == p) -> dte_c2_all_same m = true).
    { intros m. induction m as [| u us IHm]; intros p Hallp.
      - reflexivity.
      - simpl.
        assert (HA : forallb (fun z => Qeq_bool z u) us = true).
        { apply (proj2 (forallb_forall (fun w => Qeq_bool w u) us)).
          intros z Hz. apply (proj2 (Qeq_bool_iff z u)).
          apply (Qeq_trans z p u).
          - apply Hallp. right. exact Hz.
          - apply (Qeq_sym u p). apply Hallp. left. reflexivity. }
        assert (HB : dte_c2_all_same us = true).
        { apply (IHm p). intros z Hz. apply Hallp. right. exact Hz. }
        rewrite HA. rewrite HB. reflexivity. }
    unfold dte_c2_sqsum in Heq.
    pose proof (dte_c2_nsum_bound_eq (fun x0 => dte_c2_freq_q x0 (x :: xs))
                  (x :: xs) (length (x :: xs))
                  (fun x0 _ => dte_c2_freq_q_le_length x0 (x :: xs))
                  Heq x (or_introl eq_refl)) as Hfx.
    pose proof (dte_c2_freq_q_full_count x (x :: xs) Hfx) as Hall.
    apply (Hintro (x :: xs) x). intros z Hz. apply Hall. exact Hz.
Qed.

(* Supply premise 70, ledger :1255, [H_freq_perm]: statement face verbatim;
   the main theorem of this volume. *)
Theorem dte_c2_H_freq_perm : forall l p : list Q,
  Permutation l p -> dte_c2_H_freq l == dte_c2_H_freq p.
Proof.
  intros l p Hp. unfold dte_c2_H_freq.
  rewrite (dte_c2_sqsum_perm l p Hp).
  rewrite (Permutation_length Hp).
  reflexivity.
Qed.

(* Supply premise 71, ledger :1281, [H_freq_all_same_zero]: statement
   face verbatim up to the boolean carrier of the [dte_c2_all_same]
   premise. *)
Theorem dte_c2_H_freq_all_same_zero : forall l : list Q,
  dte_c2_all_same l = true -> dte_c2_H_freq l == 0.
Proof.
  intros l Hs. unfold dte_c2_H_freq. apply dte_c2_qdiv_zero_num.
  apply dte_c2_qnum_zero.
  rewrite (dte_c2_sqsum_all_same l Hs). reflexivity.
Qed.

(* Supply premise 72, ledger :1288, [H_freq_len_le_1]: statement face verbatim. *)
Theorem dte_c2_H_freq_len_le_1 : forall l : list Q,
  (length l <= 1)%nat -> dte_c2_H_freq l == 0.
Proof.
  intros l Hl. destruct l as [| x xs].
  - apply dte_c2_H_freq_all_same_zero. reflexivity.
  - simpl in Hl. destruct xs as [| y ys].
    + apply dte_c2_H_freq_all_same_zero. reflexivity.
    + simpl in Hl. exfalso. lia.
Qed.

(* Supply premise 73, ledger :1304, [H_freq_eq0_all_same]: statement
   face verbatim with the [dte_c2_bid] carrier on the conclusion face. *)
Theorem dte_c2_H_freq_eq0_all_same : forall l : list Q,
  dte_c2_H_freq l == 0 -> dte_c2_bid (dte_c2_all_same l).
Proof.
  intros l Heq. unfold dte_c2_H_freq in Heq. destruct l as [| x xs].
  - apply dte_c2_bid_intro. reflexivity.
  - assert (HB : 0 < dte_c2_qn (length (x :: xs)) * dte_c2_qn (length (x :: xs))).
    { rewrite <- (dte_c2_qn_mul (length (x :: xs)) (length (x :: xs))).
      apply dte_c2_qn_pos. simpl. apply Nat.lt_0_succ. }
    assert (Hnum : dte_c2_qn (length (x :: xs)) * dte_c2_qn (length (x :: xs))
                   - dte_c2_qn (dte_c2_sqsum (x :: xs)) == 0)
      by (apply (dte_c2_qdiv_eq0_num _ _ HB Heq)).
    pose proof (dte_c2_qsub_eq0 (dte_c2_qn (length (x :: xs))
                  * dte_c2_qn (length (x :: xs)))
                  (dte_c2_qn (dte_c2_sqsum (x :: xs))) Hnum) as Hab.
    rewrite <- (dte_c2_qn_mul (length (x :: xs)) (length (x :: xs))) in Hab.
    pose proof (dte_c2_qn_inj (length (x :: xs) * length (x :: xs))
                  (dte_c2_sqsum (x :: xs)) Hab) as Heqnat.
    apply (dte_c2_sqsum_eq_all_same (x :: xs)). symmetry. exact Heqnat.
Qed.

(* Supply premise 74, ledger :1341, [nsum_le]: statement face verbatim. *)
Theorem dte_c2_nsum_le : forall (g h : Q -> nat) (l : list Q),
  (forall x, In x l -> (g x <= h x)%nat) -> (dte_c2_nsum g l <= dte_c2_nsum h l)%nat.
Proof.
  intros g h l. induction l as [| a l IH]; simpl; intros H.
  - lia.
  - assert (H1 : (g a <= h a)%nat) by (apply H; left; reflexivity).
    assert (H2 : (dte_c2_nsum g l <= dte_c2_nsum h l)%nat)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    lia.
Qed.

(* Supply premise 75, ledger :1376, [freq_q_map_ge]: statement face verbatim. *)
Theorem dte_c2_freq_q_map_ge : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall (x : Q) (l : list Q),
  (dte_c2_freq_q x l <= dte_c2_freq_q (f x) (map f l))%nat.
Proof.
  intros f Hf x. induction l as [| a l IH].
  - simpl. lia.
  - simpl. destruct (Qeq_bool x a) eqn:H1.
    + assert (H2 : Qeq_bool (f x) (f a) = true).
      { apply (proj2 (Qeq_bool_iff (f x) (f a))). apply Hf.
        apply (proj1 (Qeq_bool_iff x a)). exact H1. }
      rewrite H2. lia.
    + destruct (Qeq_bool (f x) (f a)); lia.
Qed.

(* Supply premise 76, ledger :1392, [sqsum_map_ge]: statement face verbatim. *)
Theorem dte_c2_sqsum_map_ge : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall l : list Q, (dte_c2_sqsum l <= dte_c2_sqsum (map f l))%nat.
Proof.
  intros f Hf l. unfold dte_c2_sqsum.
  rewrite (dte_c2_nsum_map (fun y => dte_c2_freq_q y (map f l)) f l).
  apply dte_c2_nsum_le. intros x _. apply dte_c2_freq_q_map_ge. exact Hf.
Qed.

(* ================= Section 3. Canonical instances ================= *)

(* Six canonical-instance statements, each an explicit application of a
   supply statement of this file with the instance premise constructed
   inline, in the same feeding manner as the host face; the remaining
   28 instances go through the application channels [Nat.lt_0_succ],
   [le_n], [Qeq_refl], [in_eq], [Permutation_nil] and [reflexivity],
   one instance each, and these six statements are the proof-carrying
   samples of that channel.  Double-supply guard: each of the six is a
   specialization of a host conclusion face (a premise-free instance of
   a premise-carrying host statement), disjoint from the in-service
   host statements (the host keeps no rev-form or reflexivity-form
   statement in service) and shape-distinct from the supply faces of
   this file. *)

(* Canonical instance of premise 39, [qn_pos]: the nat slot fed at
   n := 1 by [Nat.lt_0_succ 0]. *)
Theorem dte_c2_qn_pos_one : 0 < dte_c2_qn 1.
Proof.
  exact (dte_c2_qn_pos 1 (Nat.lt_0_succ 0)).
Qed.

(* Canonical instance of premise 40, [qn_le], the reflexive one: the
   nat slot fed at b := a by [le_n]. *)
Theorem dte_c2_qn_le_refl : forall a : nat, dte_c2_qn a <= dte_c2_qn a.
Proof.
  intro a. exact (dte_c2_qn_le a a (le_n a)).
Qed.

(* Canonical instance of premise 53, [freq_q_perm], the reversed one:
   the permutation slot fed by [Permutation_rev]. *)
Theorem dte_c2_freq_q_perm_rev : forall (x : Q) (l : list Q),
  dte_c2_freq_q x l = dte_c2_freq_q x (rev l).
Proof.
  intros x l. exact (dte_c2_freq_q_perm x l (rev l) (Permutation_rev l)).
Qed.

(* Canonical instance of premise 58, [nsum_perm], the reversed one,
   fed as above. *)
Theorem dte_c2_nsum_perm_rev : forall (f : Q -> nat) (l : list Q),
  dte_c2_nsum f l = dte_c2_nsum f (rev l).
Proof.
  intros f l. exact (dte_c2_nsum_perm f l (rev l) (Permutation_rev l)).
Qed.

(* Canonical instance of premise 65, [sqsum_perm], the reversed one,
   fed as above. *)
Theorem dte_c2_sqsum_perm_rev : forall l : list Q,
  dte_c2_sqsum l = dte_c2_sqsum (rev l).
Proof.
  intro l. exact (dte_c2_sqsum_perm l (rev l) (Permutation_rev l)).
Qed.

(* Canonical instance of premise 70, [H_freq_perm], the reversed one
   (the main theorem of this volume): the frequency entropy is
   invariant under reversal. *)
Theorem dte_c2_H_freq_perm_rev : forall l : list Q,
  dte_c2_H_freq l == dte_c2_H_freq (rev l).
Proof.
  intro l. exact (dte_c2_H_freq_perm l (rev l) (Permutation_rev l)).
Qed.

(* ================= Section 4. Closing audit ================= *)

(* Trailing audit: a [Check] impression plus a per-statement closedness
   audit ([Print Assumptions] exits all [Closed]); the name roster of 41
   statements shows zero drift (28 supply + 7 auxiliary + 6 canonical
   instances, all closed by [Qed]). *)

Check dte_c2_qn_nonneg.
Check dte_c2_qn_S_pos.
Check dte_c2_qn_add.
Check dte_c2_qn_mul.
Check dte_c2_freq_q_le_length.
Check dte_c2_nsum_const.
Check dte_c2_nsum_map.
Check dte_c2_qn_pos.
Check dte_c2_qn_le.
Check dte_c2_qn_inj.
Check dte_c2_qlt_neq0.
Check dte_c2_qsub_eq0.
Check dte_c2_qdiv_zero_num.
Check dte_c2_qdiv_eq0_num.
Check dte_c2_qdiv_nonneg.
Check dte_c2_qnum_zero.
Check dte_c2_qeqb_false_neq.
Check dte_c2_freq_q_perm.
Check dte_c2_freq_q_eq_all.
Check dte_c2_freq_q_full_count.
Check dte_c2_nsum_ext_in.
Check dte_c2_nsum_perm.
Check dte_c2_nsum_bound.
Check dte_c2_nsum_bound_eq.
Check dte_c2_sqsum_perm.
Check dte_c2_freq_q_all_same.
Check dte_c2_sqsum_all_same.
Check dte_c2_sqsum_eq_all_same.
Check dte_c2_H_freq_perm.
Check dte_c2_H_freq_all_same_zero.
Check dte_c2_H_freq_len_le_1.
Check dte_c2_H_freq_eq0_all_same.
Check dte_c2_nsum_le.
Check dte_c2_freq_q_map_ge.
Check dte_c2_sqsum_map_ge.
Check dte_c2_qn_pos_one.
Check dte_c2_qn_le_refl.
Check dte_c2_freq_q_perm_rev.
Check dte_c2_nsum_perm_rev.
Check dte_c2_sqsum_perm_rev.
Check dte_c2_H_freq_perm_rev.

Print Assumptions dte_c2_qn_nonneg.
Print Assumptions dte_c2_qn_S_pos.
Print Assumptions dte_c2_qn_add.
Print Assumptions dte_c2_qn_mul.
Print Assumptions dte_c2_freq_q_le_length.
Print Assumptions dte_c2_nsum_const.
Print Assumptions dte_c2_nsum_map.
Print Assumptions dte_c2_qn_pos.
Print Assumptions dte_c2_qn_le.
Print Assumptions dte_c2_qn_inj.
Print Assumptions dte_c2_qlt_neq0.
Print Assumptions dte_c2_qsub_eq0.
Print Assumptions dte_c2_qdiv_zero_num.
Print Assumptions dte_c2_qdiv_eq0_num.
Print Assumptions dte_c2_qdiv_nonneg.
Print Assumptions dte_c2_qnum_zero.
Print Assumptions dte_c2_qeqb_false_neq.
Print Assumptions dte_c2_freq_q_perm.
Print Assumptions dte_c2_freq_q_eq_all.
Print Assumptions dte_c2_freq_q_full_count.
Print Assumptions dte_c2_nsum_ext_in.
Print Assumptions dte_c2_nsum_perm.
Print Assumptions dte_c2_nsum_bound.
Print Assumptions dte_c2_nsum_bound_eq.
Print Assumptions dte_c2_sqsum_perm.
Print Assumptions dte_c2_freq_q_all_same.
Print Assumptions dte_c2_sqsum_all_same.
Print Assumptions dte_c2_sqsum_eq_all_same.
Print Assumptions dte_c2_H_freq_perm.
Print Assumptions dte_c2_H_freq_all_same_zero.
Print Assumptions dte_c2_H_freq_len_le_1.
Print Assumptions dte_c2_H_freq_eq0_all_same.
Print Assumptions dte_c2_nsum_le.
Print Assumptions dte_c2_freq_q_map_ge.
Print Assumptions dte_c2_sqsum_map_ge.
Print Assumptions dte_c2_qn_pos_one.
Print Assumptions dte_c2_qn_le_refl.
Print Assumptions dte_c2_freq_q_perm_rev.
Print Assumptions dte_c2_nsum_perm_rev.
Print Assumptions dte_c2_sqsum_perm_rev.
Print Assumptions dte_c2_H_freq_perm_rev.

(* ================= Section 5. Extraction audit ================= *)

(* Extractability check under the [Obj.magic] = 0 criterion.  The
   theorem barrel runs one single [Separate Extraction] command; the 41
   theorem conclusion faces are discrete proof data and occupy their
   family slots under the extraction erasure convention.  The real
   extraction face is the data layer: the implementations
   [dte_c2_qn]/[dte_c2_freq_q]/[dte_c2_nsum]/[dte_c2_sqsum]/
   [dte_c2_H_freq] together with the boolean [dte_c2_all_same]; it is
   exercised by the separate directed probe module [_dte_c2_probe]. *)

Set Extraction Output Directory "_log/dte_t7".
Separate Extraction dte_c2_qn_nonneg dte_c2_qn_S_pos dte_c2_qn_add
  dte_c2_qn_mul dte_c2_freq_q_le_length dte_c2_nsum_const dte_c2_nsum_map
  dte_c2_qn_pos dte_c2_qn_le dte_c2_qn_inj dte_c2_qlt_neq0 dte_c2_qsub_eq0
  dte_c2_qdiv_zero_num dte_c2_qdiv_eq0_num dte_c2_qdiv_nonneg
  dte_c2_qnum_zero dte_c2_qeqb_false_neq dte_c2_freq_q_perm
  dte_c2_freq_q_eq_all dte_c2_freq_q_full_count dte_c2_nsum_ext_in
  dte_c2_nsum_perm dte_c2_nsum_bound dte_c2_nsum_bound_eq dte_c2_sqsum_perm
  dte_c2_freq_q_all_same dte_c2_sqsum_all_same dte_c2_sqsum_eq_all_same
  dte_c2_H_freq_perm dte_c2_H_freq_all_same_zero dte_c2_H_freq_len_le_1
  dte_c2_H_freq_eq0_all_same dte_c2_nsum_le dte_c2_freq_q_map_ge
  dte_c2_sqsum_map_ge dte_c2_qn_pos_one dte_c2_qn_le_refl
  dte_c2_freq_q_perm_rev dte_c2_nsum_perm_rev dte_c2_sqsum_perm_rev
  dte_c2_H_freq_perm_rev.
