(* ConstructiveWorld-Set -- decider-generic bounded separation search. *)

(** * NsepFindGeneric: generic bounded search over a decidable separation predicate.

    Mission.  The bounded linear search of [LW5SepComplexity] with its
      separation decider lifted to an explicit argument [dec]: the
      generic search [nsep_find] tests [dec] at successive indices and
      returns the budget endpoint when fuel runs out; upper bound
      [nsep_find_ub], hit characterization [nsep_find_hit], minimality
      [nsep_find_min], the budgeted run [nsep_first] with
      [nsep_first_bound], [nsep_first_hit], [nsep_first_least],
      [nsep_first_minimal], and the sqrt(2) Newton sequence instance
      [ir2_sep_dec] with [ir2_x], [ir2_delta], [ir2_e].  The three
      upper-bound statements conclude in nat order, as in the baseline.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
      [Arith.Arith], [Bool.Bool], [Lia], [Extraction].  Requires
      [LW0LeibWindow], [S01_BaseRing] of this development.

    References.  This development, NsepFindGeneric.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" NsepFindGeneric.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
From Stdlib Require Import Extraction.
Require Import LW0LeibWindow.
Require Import S01_BaseRing.

(* ================= Section 1. generic bounded linear search ================= *)

(* [nsep_find] tests the decider [dec] at successive indices from [n]
   and returns the first separating index; when the fuel is exhausted
   it returns the budget endpoint [n], and returning that endpoint
   makes no separating claim.  Every statement of this section holds
   for an arbitrary [dec : Q -> nat -> bool]. *)

Fixpoint nsep_find (dec : Q -> nat -> bool) (q : Q) (n fuel : nat) : nat :=
  match fuel with
  | 0%nat => n
  | Datatypes.S f =>
      if dec q n then n else nsep_find dec q (Datatypes.S n) f
  end.

(** search upper bound: [nsep_find] never exceeds the sum [n + fuel]
    of the start index and the fuel. *)
Lemma nsep_find_ub : forall (dec : Q -> nat -> bool) (q : Q) (fuel n : nat),
  (nsep_find dec q n fuel <= n + fuel)%nat.
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n.
  - simpl. lia.
  - simpl. destruct (dec q n).
    + lia.
    + specialize (IH (Datatypes.S n)). lia.
Qed.

(** hit characterization: if some index [n0] of the interval
    [n, n + fuel] satisfies [dec q n0 = true], then [nsep_find] stops
    at a separating index (first component) and does not step past
    [n0] (second component).  Both components are carried by [Set]:
    the boolean decision equality by [leiblw_Id], the conjunction by
    [And := prod] of [S01_BaseRing]. *)
Lemma nsep_find_hit : forall (dec : Q -> nat -> bool) (q : Q) (fuel n n0 : nat),
  (n <= n0)%nat -> (n0 <= n + fuel)%nat ->
  leiblw_Id (dec q n0) true ->
  And (leiblw_Id (dec q (nsep_find dec q n fuel)) true)
      (leiblw_Id (Nat.leb (nsep_find dec q n fuel) n0) true).
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n n0 Hn1 Hn2 Hhit.
  - assert (Heq : n = n0) by lia. subst n0. simpl.
    split; [exact Hhit|].
    apply leiblw_id_eq. apply Nat.leb_le. lia.
  - simpl. destruct (dec q n) eqn:E.
    + split.
      * rewrite E. apply leiblw_id_intro.
      * apply leiblw_id_eq. apply Nat.leb_le. lia.
    + apply (IH (Datatypes.S n) n0).
      * destruct (Nat.eq_dec n n0) as [Heq|Hne].
        -- subst n0. leiblw_id_inv_in Hhit. rewrite E in Hhit.
           discriminate Hhit.
        -- lia.
      * lia.
      * exact Hhit.
Qed.

(** minimality: every index [m] below the stopping point of
    [nsep_find] is non-separating, [dec q m = false], carried by the
    [Set]-face equality [leiblw_Id]. *)
Lemma nsep_find_min : forall (dec : Q -> nat -> bool) (q : Q) (fuel n m : nat),
  (n <= m)%nat -> (m < nsep_find dec q n fuel)%nat ->
  leiblw_Id (dec q m) false.
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n m Hn1 Hlt.
  - simpl in Hlt. lia.
  - simpl. destruct (dec q n) eqn:E.
    + simpl in Hlt. rewrite E in Hlt. cbn in Hlt. lia.
    + simpl in Hlt. rewrite E in Hlt. cbn in Hlt.
      destruct (Nat.eq_dec n m) as [Heq|Hne].
      * subst m. rewrite E. apply leiblw_id_intro.
      * apply (IH (Datatypes.S n) m); lia.
Qed.

(* ================= Section 2. budgeted run and its four corollaries ================= *)

(* [nsep_first dec b q] is [nsep_find] run from [0] with budget [b].
   The four corollaries match the four [lw5n_nsep] theorems of
   [LW5SepComplexity] statement for statement, with the budget [b]
   explicit: budget sufficiency, in the form of a separating witness
   inside the budget, is the obligation of the decider instance and
   is not claimed here. *)

Definition nsep_first (dec : Q -> nat -> bool) (b : nat) (q : Q) : nat :=
  nsep_find dec q 0 b.

(** run upper bound: [nsep_first] never exceeds the budget [b]. *)
Theorem nsep_first_bound : forall (dec : Q -> nat -> bool) (b : nat) (q : Q),
  (nsep_first dec b q <= b)%nat.
Proof.
  intros dec b q. unfold nsep_first.
  pose proof (nsep_find_ub dec q b 0) as H. lia.
Qed.

(** hit theorem: if a separating index exists within the budget,
    [nsep_first] stops at a separating index. *)
Theorem nsep_first_hit : forall (dec : Q -> nat -> bool) (b : nat) (q : Q)
    (n0 : nat),
  (n0 <= b)%nat ->
  leiblw_Id (dec q n0) true ->
  leiblw_Id (dec q (nsep_first dec b q)) true.
Proof.
  intros dec b q n0 Hb Hhit. unfold nsep_first.
  destruct (nsep_find_hit dec q b 0 n0 (Nat.le_0_l n0) Hb Hhit) as [H _].
  exact H.
Qed.

(** no-passing theorem: [nsep_first] does not step past any
    separating index within the budget. *)
Theorem nsep_first_least : forall (dec : Q -> nat -> bool) (b : nat) (q : Q)
    (n0 : nat),
  (n0 <= b)%nat ->
  leiblw_Id (dec q n0) true ->
  (nsep_first dec b q <= n0)%nat.
Proof.
  intros dec b q n0 Hb Hhit.
  apply Nat.leb_le.
  destruct (nsep_find_hit dec q b 0 n0 (Nat.le_0_l n0) Hb Hhit) as [_ H].
  leiblw_id_inv_in H. exact H.
Qed.

(** minimal characterization theorem: the least separating index
    within the budget is returned by [nsep_first] verbatim, as the
    [Set]-face [leiblw_Id] equality [nsep_first = n0], given a
    separating index [n0] with no separating index in [0, n0). *)
Theorem nsep_first_minimal : forall (dec : Q -> nat -> bool) (b : nat) (q : Q)
    (n0 : nat),
  (n0 <= b)%nat ->
  leiblw_Id (dec q n0) true ->
  (forall m : nat, (m < n0)%nat -> leiblw_Id (dec q m) false) ->
  leiblw_Id (nsep_first dec b q) n0.
Proof.
  intros dec b q n0 Hb Hn Hmin.
  assert (Hhit := nsep_first_hit dec b q n0 Hb Hn).
  assert (Hle := nsep_first_least dec b q n0 Hb Hn).
  destruct (Nat.eq_dec (nsep_first dec b q) n0) as [E|E].
  - rewrite E. apply leiblw_id_intro.
  - exfalso.
    assert (Hlt : (nsep_first dec b q < n0)%nat) by lia.
    specialize (Hmin _ Hlt).
    assert (Ht : dec q (nsep_first dec b q) = true)
      by (leiblw_id_inv_in Hhit; exact Hhit).
    rewrite Ht in Hmin. inversion Hmin.
Qed.

(* ================= Section 3. instance: the sqrt(2) Newton sequence decider ================= *)

(* the iteration starts at [x_0 = 2] and continues by
   [x_{n+1} = (x_n + 2 / x_n) * (1 / 2)]; the square error is
   [delta_n = x_n^2 - 2] and the window width is
   [e_n = (1 / 2) * delta_n].  At index [n] the decider [ir2_sep_dec]
   asks whether [|q - x_n|] has left the window [e_n], the negation
   of [Qle_bool], mirror-shaped to the leaving-window form of
   [lw5n_sep_dec] in [LW5SepComplexity]. *)

Fixpoint ir2_x (n : nat) : Q :=
  match n with
  | 0%nat => 2%Q
  | Datatypes.S m => (ir2_x m + 2%Q / ir2_x m) * (1 # 2)
  end.

Definition ir2_delta (n : nat) : Q := ir2_x n * ir2_x n - 2%Q.
Definition ir2_e (n : nat) : Q := (1 # 2) * ir2_delta n.

Definition ir2_sep_dec (q : Q) (n : nat) : bool :=
  negb (Qle_bool (Qabs ((q - ir2_x n)%Q)) (ir2_e n)).

(** instance type face: [ir2_sep_dec] fits the decider argument shape
    of [nsep_find]. *)
Check (ir2_sep_dec : Q -> nat -> bool).
Check (nsep_find ir2_sep_dec : Q -> nat -> nat -> nat).

(* ================= Section 4. computational spot checks, extraction, assumption audit ================= *)

(* sample [q = 3/2]: [x_0 = 2] and [e_0 = 1], so [|3/2 - 2| = 1/2]
   stays inside the window and [dec 0 = false]; at [x_2 = 17/12] with
   [e_2 = 1/288] we have [|3/2 - 17/12| = 1/12 > 1/288], so
   [dec 2 = true]; the least hitting index is [2]. *)

Eval vm_compute in (ir2_sep_dec (3 # 2) 0, ir2_sep_dec (3 # 2) 2).
Eval vm_compute in (ir2_sep_dec (3 # 2) 3).
Eval vm_compute in (nsep_find ir2_sep_dec (3 # 2) 0 10).

Separate Extraction nsep_find nsep_first ir2_sep_dec ir2_x ir2_e ir2_delta.

Print Assumptions nsep_find_ub.
Print Assumptions nsep_find_hit.
Print Assumptions nsep_find_min.
Print Assumptions nsep_first_bound.
Print Assumptions nsep_first_hit.
Print Assumptions nsep_first_least.
Print Assumptions nsep_first_minimal.
