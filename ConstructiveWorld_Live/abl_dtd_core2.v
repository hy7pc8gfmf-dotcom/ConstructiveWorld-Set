(* ConstructiveWorld-Set -- constructive argument supply for the DTPT theorem faces. *)

(** * abl_dtd_core2: premise-free specializations of the DTPT theorems.

    Mission.  Constructive supply for the argument faces of the DTPT
      theorem family: each side condition of a host theorem is discharged
      by an explicit route lemma and the theorem is then applied at fully
      explicit arguments, yielding premise-free specializations of its
      conclusions.  The routes cover sortedness of the canonical form [P0]
      ([dtd_c2_sorted_P0]), nonemptiness of cons and reversal forms
      ([dtd_c2_cons_neq_nil], [dtd_c2_rev_cons_ne]), positivity guards
      ([dtd_c2_nat_lt_succ], [dtd_c2_Qlt_pos_num], [dtd_c2_Zpos_of_S]),
      permutation witnesses ([dtd_c2_perm_sym], [dtd_c2_perm_rev],
      [dtd_c2_n9_perm_max_wit]) and pairwise bounds ([dtd_c2_pair_spread]).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List],
      [Permutation], [Lia], [Extraction].  Requires [DTPT] of this
      development.

    References.  This development, abl_dtd_core2.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_dtd_core2.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Import DTPT.DTPT.

(* ================= Section 1. Certificate routes for the side conditions ================= *)

(* sortedness of the canonical form: [P0 l] is sorted for every list [l];
   the host module already carries this fact as [xq_P0_sorted], and this
   lemma forwards it verbatim as the shared sortedness route *)
Theorem dtd_c2_sorted_P0 : forall l : list Q, SortedQ (P0 l).
Proof.
  intro l. exact (xq_P0_sorted l).
Qed.

(* nonemptiness of cons forms: a list built by [cons] differs from the
   empty list, by discrimination on the head constructor; the disequality
   is verbatim the nonemptiness face of the host statements *)
Theorem dtd_c2_cons_neq_nil : forall (x : Q) (l : list Q), (x :: l) <> [].
Proof.
  intros x l H. discriminate H.
Qed.

(* strict positivity at the [nat] layer: every successor is greater than
   zero, so [0 < S k] holds for each [k] *)
Theorem dtd_c2_nat_lt_succ : forall k : nat, (0 < S k)%nat.
Proof.
  intro k. lia.
Qed.

(* strict order on the canonical family of positive fractions: [0 < 1 # p]
   holds definitionally after unfolding [Qlt] and reducing; linear
   arithmetic closes the remaining inequality (the standard library
   provides no boolean [Qlt] decision, so the computation itself is the
   route, the same unfolding recipe as the host [D8_sorted_frac_pos]) *)
Theorem dtd_c2_Qlt_pos_num : forall p : positive, (0 < (1 # p)%Q).
Proof.
  intro p. unfold Qlt. simpl. lia.
Qed.

(* symmetry of permutations: [Permutation p l] implies [Permutation l p],
   by the [Permutation_sym] constructor of the standard library *)
Theorem dtd_c2_perm_sym : forall l p : list Q,
  Permutation p l -> Permutation l p.
Proof.
  intros l p Hperm. exact (Permutation_sym Hperm).
Qed.

(* pairwise spread bound: any two elements of a table lie within
   [Qabs]-distance at most [spread m] of each other; this instantiates the
   host lemma [spread_pair_le] at the canonical bound [k := spread m] *)
Theorem dtd_c2_pair_spread : forall (m : list Q) (x y : Q),
  In x m -> In y m -> (Qabs (x - y) <= spread m)%Q.
Proof.
  intros m x y Hx Hy. exact (spread_pair_le m x y Hx Hy).
Qed.

(* a permutation inside the length-3 class: [Permutation [a; b; c]
   [a; c; b]] holds by the two constructor steps [perm_skip] and
   [perm_swap], the same construction chain as the host witness
   [n9_max_attained] *)
Theorem dtd_c2_perm3_swap : forall a b c : Q, Permutation [a; b; c] [a; c; b].
Proof.
  intros a b c. apply perm_skip. apply perm_swap.
Qed.

(* witness permutation for the n9 class: the witness list [n9_l0] permutes
   to [0; 2; 1], built by [perm_skip] and [perm_swap]; the host tightness
   witness [n9_max_attained] carries this permutation inside an existential
   conjunction, and this lemma supplies that component as a standalone
   datum *)
Theorem dtd_c2_n9_perm_max_wit : Permutation n9_l0 [0; 2; 1].
Proof.
  unfold n9_l0. apply perm_skip. apply perm_swap.
Qed.

(* reflexivity for the witness list: [Permutation n9_l0 n9_l0] by the
   [Permutation_refl] constructor; the minimum of the class is attained at
   the sorted form itself *)
Theorem dtd_c2_n9_perm_refl : Permutation n9_l0 n9_l0.
Proof.
  apply Permutation_refl.
Qed.

(* reversal permutation: [Permutation l (rev l)] for every list [l], by
   the standard-library constructor [Permutation_rev]; it supplies the
   permutation input of the reversal-shaped instances *)
Theorem dtd_c2_perm_rev : forall l : list Q, Permutation l (rev l).
Proof.
  intro l. apply Permutation_rev.
Qed.

(* nonemptiness of reversals: the reversal of a cons list is again
   nonempty, [rev (x :: xs) <> []]; this forwards the host lemma
   [cgen_rev_cons_ne] at all arguments, with the disequality verbatim the
   nonemptiness face of the host statements *)
Theorem dtd_c2_rev_cons_ne : forall (x : Q) (xs : list Q), rev (x :: xs) <> [].
Proof.
  intros x xs. exact (cgen_rev_cons_ne x xs).
Qed.

(* lower bound at the [nat] layer: zero is the least natural number, so
   [0 <= k] holds for each [k] *)
Theorem dtd_c2_nat_le_0 : forall k : nat, (0 <= k)%nat.
Proof.
  intro k. lia.
Qed.

(* positivity at the [Z] layer: the image of a successor under [Z.of_nat]
   is strictly positive; take the forward direction of [Znat.Nat2Z.inj_lt]
   from [nat] to [Z], closing the [nat] side by linear arithmetic first *)
Theorem dtd_c2_Zpos_of_S : forall n : nat, (0 < Z.of_nat (S n))%Z.
Proof.
  intro n. apply (proj1 (Znat.Nat2Z.inj_lt 0 (S n))). lia.
Qed.

(* factorial threshold: [4 <= S (S (S (S n)))] holds for each [n]; this is
   the host bound [(4 <= k)%nat] instantiated at the canonical index
   [k := S (S (S (S n)))] *)
Theorem dtd_c2_nat_ge4_S4 : forall n : nat, (4 <= S (S (S (S n))))%nat.
Proof.
  intro n. lia.
Qed.

(* ================= Section 2. Premise-free specializations =================

   Each theorem applies a host DTPT theorem at fully explicit arguments,
   with every side condition supplied by a Section 1 route or built inline
   by a membership or reflexivity constructor; each conclusion is the host
   conclusion face verbatim at the canonical instance. *)

(* insertion preserves the sort: apply the host [xq_sortQ_insert] with the
   sortedness side condition supplied by [dtd_c2_sorted_P0]; inserting one
   element into a sorted canonical form keeps it sorted *)
Theorem dtd_c2_xq_sortQ_insert_P0 : forall (x : Q) (l : list Q),
  SortedQ (insert_q x (P0 l)).
Proof.
  intros x l. exact (xq_sortQ_insert x (P0 l) (dtd_c2_sorted_P0 l)).
Qed.

(* last-element membership: apply the host [xq_lastq_In] with the
   nonemptiness side condition supplied by [dtd_c2_cons_neq_nil]; the last
   element of a cons list belongs to that list *)
Theorem dtd_c2_xq_lastq_In_cons : forall (x : Q) (l : list Q),
  In (lastq (x :: l)) (x :: l).
Proof.
  intros x l. exact (xq_lastq_In (x :: l) (dtd_c2_cons_neq_nil x l)).
Qed.

(* head-element membership: apply the host [xq_hd_In_gen] with the
   nonemptiness side condition supplied by [dtd_c2_cons_neq_nil]; the head
   of a cons list, read with default [0], belongs to that list *)
Theorem dtd_c2_xq_hd_In_gen_cons : forall (x : Q) (l : list Q),
  In (hd 0 (x :: l)) (x :: l).
Proof.
  intros x l. exact (xq_hd_In_gen (x :: l) (dtd_c2_cons_neq_nil x l)).
Qed.

(* head-tail order: apply the host [xq_hd_le_lastq] with the sortedness
   side condition supplied by [dtd_c2_sorted_P0]; in a sorted canonical
   form the head does not exceed the last element *)
Theorem dtd_c2_xq_hd_le_lastq_P0 : forall l : list Q,
  (hd 0 (P0 l) <= lastq (P0 l))%Q.
Proof.
  intro l. exact (xq_hd_le_lastq (P0 l) (dtd_c2_sorted_P0 l)).
Qed.

(* telescoping identity: apply the host [xq_telescope] with the sortedness
   side condition supplied by [dtd_c2_sorted_P0]; the sum of adjacent
   differences of a sorted canonical form equals the last element minus
   the head *)
Theorem dtd_c2_xq_telescope_P0 : forall l : list Q,
  H_adj (P0 l) == lastq (P0 l) - hd 0 (P0 l).
Proof.
  intro l. exact (xq_telescope (P0 l) (dtd_c2_sorted_P0 l)).
Qed.

(* pairwise distance bound: apply the host [xq_pair_dist_le] with both
   membership side conditions built inline by the [In]-cons constructors,
   [left] at the head position and [right; left] at the next position; the
   distance between the first two elements is at most the sum of adjacent
   differences *)
Theorem dtd_c2_xq_pair_dist_le_cons_cons : forall (x y : Q) (l : list Q),
  (Qabs (x - y) <= H_adj (x :: y :: l))%Q.
Proof.
  intros x y l.
  apply (xq_pair_dist_le (x :: y :: l) x y).
  - simpl. left. reflexivity.
  - simpl. right. left. reflexivity.
Qed.

(* reciprocal of a positive factorial is positive: apply the host
   [D8_sorted_frac_pos] with the positivity side condition supplied by
   [dtd_c2_nat_lt_succ] at the successor index *)
Theorem dtd_c2_D8_sorted_frac_pos_S : forall k : nat,
  0 < (1 / (q_fact (S k)))%Q.
Proof.
  intro k. exact (D8_sorted_frac_pos (S k) (dtd_c2_nat_lt_succ k)).
Qed.

(* snoc equation for the adjacent-difference sum: apply the host
   [cgen_H_adj_snoc] with the nonemptiness side condition supplied by
   [dtd_c2_cons_neq_nil]; appending one element increases the sum by
   exactly the distance to the previous last element *)
Theorem dtd_c2_cgen_H_adj_snoc_cons : forall (y x : Q) (l : list Q),
  H_adj ((y :: l) ++ [x]) == (H_adj (y :: l) + Qabs (x - lastq (y :: l)))%Q.
Proof.
  intros y x l.
  exact (cgen_H_adj_snoc (y :: l) x (dtd_c2_cons_neq_nil y l)).
Qed.

(* symmetry of the class bound: apply the host theorem [C_gen] with the
   permutation side condition reversed by [dtd_c2_perm_sym]; the entropy
   of the canonical form [P0 l] is a lower bound for the entropy of every
   permutation [p] of [l] *)
Theorem dtd_c2_C_gen_sym : forall l p : list Q,
  Permutation p l -> (H_adj (P0 l) <= H_adj p)%Q.
Proof.
  intros l p Hperm. exact (C_gen l p (dtd_c2_perm_sym l p Hperm)).
Qed.

(* head minimality: apply the host [sorted_hd_le_in] with the sortedness
   side condition from [xq_P0_sorted] and the membership side condition
   transported along the permutation equivalence [D5_P0_perm]; the head of
   the sorted canonical form is a lower bound for every element *)
Theorem dtd_c2_sorted_hd_le_in_min : forall (x : Q) (l : list Q),
  (hd 0 (P0 (x :: l)) <= x)%Q.
Proof.
  intros x l.
  apply (sorted_hd_le_in (P0 (x :: l)) x).
  - exact (xq_P0_sorted (x :: l)).
  - apply Permutation_in with (l := x :: l).
    + apply D5_P0_perm.
    + simpl. left. reflexivity.
Qed.

(* tail maximality: the mirror of the head-minimality construction; the
   last element of the sorted canonical form is an upper bound for every
   element *)
Theorem dtd_c2_sorted_in_le_last_max : forall (x : Q) (l : list Q),
  (x <= lastq (P0 (x :: l)))%Q.
Proof.
  intros x l.
  apply (sorted_in_le_last (P0 (x :: l)) x).
  - exact (xq_P0_sorted (x :: l)).
  - apply Permutation_in with (l := x :: l).
    + apply D5_P0_perm.
    + simpl. left. reflexivity.
Qed.

(* spread bound between two listed elements: apply the host
   [spread_pair_le] with both membership side conditions built inline at
   the head and next positions; the distance between the first two
   elements is at most the spread of the list *)
Theorem dtd_c2_spread_pair_le_cons_cons : forall (x y : Q) (l : list Q),
  (Qabs (x - y) <= spread (x :: y :: l))%Q.
Proof.
  intros x y l.
  apply (spread_pair_le (x :: y :: l) x y).
  - simpl. left. reflexivity.
  - simpl. right. left. reflexivity.
Qed.

(* amplification to the pairwise bound: apply the host
   [H_adj_pair_bound] with the nonemptiness side condition supplied by
   [dtd_c2_cons_neq_nil] and the pairwise bound supplied by
   [dtd_c2_pair_spread] at [k := spread]; the sum of adjacent differences
   is bounded by one less than the length times the spread *)
Theorem dtd_c2_H_adj_pair_bound_cons_spread : forall (x y : Q) (l : list Q),
  H_adj (x :: y :: l)
  <= ((Z.of_nat (length (x :: y :: l)) - 1)%Z # 1) * spread (x :: y :: l).
Proof.
  intros x y l.
  exact (H_adj_pair_bound (x :: y :: l) (spread (x :: y :: l))
           (dtd_c2_cons_neq_nil x (y :: l))
           (dtd_c2_pair_spread (x :: y :: l))).
Qed.

(* maximum of the n9 class at the witness list: apply the host [n9_max]
   with the permutation side condition supplied by
   [dtd_c2_n9_perm_max_wit]; the entropy of the permuted witness list is
   at most 3 *)
Theorem dtd_c2_n9_max_wit : (H_adj [0; 2; 1] <= 3)%Q.
Proof.
  exact (n9_max [0; 2; 1] dtd_c2_n9_perm_max_wit).
Qed.

(* minimum of the n9 class at the sorted form: apply the host
   [n9_min_is_sorted] with the reflexivity side condition supplied by
   [dtd_c2_n9_perm_refl]; the entropy of the witness list is at least 2 *)
Theorem dtd_c2_n9_min_is_sorted_refl : (2 <= H_adj n9_l0)%Q.
Proof.
  exact (n9_min_is_sorted n9_l0 dtd_c2_n9_perm_refl).
Qed.

(* naive upper bound, spread face, at the reversal instance: apply the
   host [n9_naive_bound] with the permutation side condition supplied by
   [dtd_c2_perm_rev] and the nonemptiness side condition supplied by
   [dtd_c2_rev_cons_ne]; the reversal instance keeps this conclusion
   distinct from the reflexive shape of the pairwise amplification above *)
Theorem dtd_c2_n9_naive_bound_rev : forall (a : Q) (t : list Q),
  H_adj (rev (a :: t))
  <= ((Z.of_nat (length (a :: t)) - 1)%Z # 1) * spread (a :: t).
Proof.
  intros a t.
  exact (n9_naive_bound (a :: t) (rev (a :: t))
           (dtd_c2_perm_rev (a :: t)) (dtd_c2_rev_cons_ne a t)).
Qed.

(* naive upper bound, entropy face, at the reversal instance: the same
   construction with the host [n9_naive_bound_Hadj]; the conclusion is the
   host conclusion verbatim at the canonical instance *)
Theorem dtd_c2_n9_naive_bound_Hadj_rev : forall (a : Q) (t : list Q),
  H_adj (rev (a :: t))
  <= ((Z.of_nat (length (a :: t)) - 1)%Z # 1) * H_adj (a :: t).
Proof.
  intros a t.
  exact (n9_naive_bound_Hadj (a :: t) (rev (a :: t))
           (dtd_c2_perm_rev (a :: t)) (dtd_c2_rev_cons_ne a t)).
Qed.

(* factorial monotonicity from zero: apply the host [nat_fact_mono] with
   the lower-bound side condition supplied by [dtd_c2_nat_le_0]; the
   factorial grows monotonically from the zeroth index *)
Theorem dtd_c2_nat_fact_mono_0 : forall k : nat,
  (nat_fact 0 <= nat_fact k)%nat.
Proof.
  intro k. exact (nat_fact_mono 0 k (dtd_c2_nat_le_0 k)).
Qed.

(* factorial monotonicity lifted to the integers: apply the host
   [nat_fact_le_Z] with the same lower-bound side condition; monotonicity
   reflects through [Z.of_nat] *)
Theorem dtd_c2_nat_fact_le_Z_0 : forall k : nat,
  (Z.of_nat (nat_fact 0) <= Z.of_nat (nat_fact k))%Z.
Proof.
  intro k. exact (nat_fact_le_Z 0 k (dtd_c2_nat_le_0 k)).
Qed.

(* reciprocal antitonicity from zero: apply the host [q_fact_recip_anti]
   with the lower-bound side condition supplied by [dtd_c2_nat_le_0]; the
   reciprocal of the factorial decreases as the index grows, starting from
   the value [1] at index zero *)
Theorem dtd_c2_q_fact_recip_anti_0 : forall k' : nat,
  (1 / q_fact k' <= 1 / q_fact 0)%Q.
Proof.
  intro k'. exact (q_fact_recip_anti 0 k' (dtd_c2_nat_le_0 k')).
Qed.

(* successive reciprocals do not increase: apply the host [D8_mono] at
   [K := S k] with the positivity side condition supplied by
   [dtd_c2_nat_lt_succ]; shifting the index by one does not increase the
   reciprocal *)
Theorem dtd_c2_D8_mono_S : forall k : nat,
  (1 / q_fact (S (S k)) <= 1 / q_fact (S k))%Q.
Proof.
  intro k. exact (D8_mono (S k) (dtd_c2_nat_lt_succ k)).
Qed.

(* core step at the doubled denominator: apply the host [q_recip_step_Z]
   with the positivity side condition supplied by [dtd_c2_Zpos_of_S] and
   the order side condition built inline by the reflexivity constructor
   [Z.le_refl] at the canonical instance [a := 2 * b]; doubling numerator
   and denominator leaves [2 / (2 * b) <= 1 / b] *)
Theorem dtd_c2_q_recip_step_Z_double : forall n : nat,
  (2 / ((2 * Z.of_nat (S n)) # 1) <= 1 / (Z.of_nat (S n) # 1))%Q.
Proof.
  intro n.
  apply (q_recip_step_Z (2 * Z.of_nat (S n)) (Z.of_nat (S n))).
  - exact (dtd_c2_Zpos_of_S n).
  - apply Z.le_refl.
Qed.

(* convergence rate at the factorial threshold: apply the host
   [q_fact_rate] with the threshold side condition supplied by
   [dtd_c2_nat_ge4_S4]; from four successors on, four times the reciprocal
   of the factorial is below 1 *)
Theorem dtd_c2_q_fact_rate_S4 : forall n : nat,
  (1 / q_fact (S (S (S (S n)))) * 4 < 1)%Q.
Proof.
  intro n.
  apply (q_fact_rate (S (S (S (S n))))).
  exact (dtd_c2_nat_ge4_S4 n).
Qed.

(* ================= Section 3. Audit block =================

   One [Check] and one [Print Assumptions] per named theorem, 37 in total:
   14 route lemmas and 23 premise-free specializations. *)

Check dtd_c2_sorted_P0.
Check dtd_c2_cons_neq_nil.
Check dtd_c2_nat_lt_succ.
Check dtd_c2_Qlt_pos_num.
Check dtd_c2_perm_sym.
Check dtd_c2_pair_spread.
Check dtd_c2_perm3_swap.
Check dtd_c2_n9_perm_max_wit.
Check dtd_c2_n9_perm_refl.
Check dtd_c2_perm_rev.
Check dtd_c2_rev_cons_ne.
Check dtd_c2_nat_le_0.
Check dtd_c2_Zpos_of_S.
Check dtd_c2_nat_ge4_S4.
Check dtd_c2_xq_sortQ_insert_P0.
Check dtd_c2_xq_lastq_In_cons.
Check dtd_c2_xq_hd_In_gen_cons.
Check dtd_c2_xq_hd_le_lastq_P0.
Check dtd_c2_xq_telescope_P0.
Check dtd_c2_xq_pair_dist_le_cons_cons.
Check dtd_c2_D8_sorted_frac_pos_S.
Check dtd_c2_cgen_H_adj_snoc_cons.
Check dtd_c2_C_gen_sym.
Check dtd_c2_sorted_hd_le_in_min.
Check dtd_c2_sorted_in_le_last_max.
Check dtd_c2_spread_pair_le_cons_cons.
Check dtd_c2_H_adj_pair_bound_cons_spread.
Check dtd_c2_n9_max_wit.
Check dtd_c2_n9_min_is_sorted_refl.
Check dtd_c2_n9_naive_bound_rev.
Check dtd_c2_n9_naive_bound_Hadj_rev.
Check dtd_c2_nat_fact_mono_0.
Check dtd_c2_nat_fact_le_Z_0.
Check dtd_c2_q_fact_recip_anti_0.
Check dtd_c2_D8_mono_S.
Check dtd_c2_q_recip_step_Z_double.
Check dtd_c2_q_fact_rate_S4.

Print Assumptions dtd_c2_sorted_P0.
Print Assumptions dtd_c2_cons_neq_nil.
Print Assumptions dtd_c2_nat_lt_succ.
Print Assumptions dtd_c2_Qlt_pos_num.
Print Assumptions dtd_c2_perm_sym.
Print Assumptions dtd_c2_pair_spread.
Print Assumptions dtd_c2_perm3_swap.
Print Assumptions dtd_c2_n9_perm_max_wit.
Print Assumptions dtd_c2_n9_perm_refl.
Print Assumptions dtd_c2_perm_rev.
Print Assumptions dtd_c2_rev_cons_ne.
Print Assumptions dtd_c2_nat_le_0.
Print Assumptions dtd_c2_Zpos_of_S.
Print Assumptions dtd_c2_nat_ge4_S4.
Print Assumptions dtd_c2_xq_sortQ_insert_P0.
Print Assumptions dtd_c2_xq_lastq_In_cons.
Print Assumptions dtd_c2_xq_hd_In_gen_cons.
Print Assumptions dtd_c2_xq_hd_le_lastq_P0.
Print Assumptions dtd_c2_xq_telescope_P0.
Print Assumptions dtd_c2_xq_pair_dist_le_cons_cons.
Print Assumptions dtd_c2_D8_sorted_frac_pos_S.
Print Assumptions dtd_c2_cgen_H_adj_snoc_cons.
Print Assumptions dtd_c2_C_gen_sym.
Print Assumptions dtd_c2_sorted_hd_le_in_min.
Print Assumptions dtd_c2_sorted_in_le_last_max.
Print Assumptions dtd_c2_spread_pair_le_cons_cons.
Print Assumptions dtd_c2_H_adj_pair_bound_cons_spread.
Print Assumptions dtd_c2_n9_max_wit.
Print Assumptions dtd_c2_n9_min_is_sorted_refl.
Print Assumptions dtd_c2_n9_naive_bound_rev.
Print Assumptions dtd_c2_n9_naive_bound_Hadj_rev.
Print Assumptions dtd_c2_nat_fact_mono_0.
Print Assumptions dtd_c2_nat_fact_le_Z_0.
Print Assumptions dtd_c2_q_fact_recip_anti_0.
Print Assumptions dtd_c2_D8_mono_S.
Print Assumptions dtd_c2_q_recip_step_Z_double.
Print Assumptions dtd_c2_q_fact_rate_S4.

(* Extraction audit: [Separate Extraction] emits one [\.ml] module per
   theorem; the audit checks that no [Obj.magic] remains in any emitted
   module. *)
Set Extraction Output Directory "_log/dtd_t3".
Separate Extraction dtd_c2_sorted_P0
  dtd_c2_cons_neq_nil dtd_c2_nat_lt_succ dtd_c2_Qlt_pos_num
  dtd_c2_perm_sym dtd_c2_pair_spread dtd_c2_perm3_swap
  dtd_c2_n9_perm_max_wit dtd_c2_n9_perm_refl dtd_c2_perm_rev
  dtd_c2_rev_cons_ne dtd_c2_nat_le_0 dtd_c2_Zpos_of_S
  dtd_c2_nat_ge4_S4 dtd_c2_xq_sortQ_insert_P0 dtd_c2_xq_lastq_In_cons
  dtd_c2_xq_hd_In_gen_cons dtd_c2_xq_hd_le_lastq_P0
  dtd_c2_xq_telescope_P0 dtd_c2_xq_pair_dist_le_cons_cons
  dtd_c2_D8_sorted_frac_pos_S dtd_c2_cgen_H_adj_snoc_cons
  dtd_c2_C_gen_sym dtd_c2_sorted_hd_le_in_min
  dtd_c2_sorted_in_le_last_max dtd_c2_spread_pair_le_cons_cons
  dtd_c2_H_adj_pair_bound_cons_spread dtd_c2_n9_max_wit
  dtd_c2_n9_min_is_sorted_refl dtd_c2_n9_naive_bound_rev
  dtd_c2_n9_naive_bound_Hadj_rev dtd_c2_nat_fact_mono_0
  dtd_c2_nat_fact_le_Z_0 dtd_c2_q_fact_recip_anti_0 dtd_c2_D8_mono_S
  dtd_c2_q_recip_step_Z_double dtd_c2_q_fact_rate_S4.
