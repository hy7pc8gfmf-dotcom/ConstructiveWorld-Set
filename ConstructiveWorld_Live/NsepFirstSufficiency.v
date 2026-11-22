(* ConstructiveWorld-Set -- general sufficiency theorem for the budgeted minimal separation index search: decider-parameterized, machine-checked. *)

(** * NsepFirstSufficiency: the two-sided output characterization of the budgeted minimal separation index search.

    Mission.  Beyond the four NsepFindGeneric corollaries (the sufficient-budget case: a hit order in
      [0, b]) this module completes the two-sided output characterization: exact stop (a first hit
      order r inside the window stops the search verbatim at r); sufficiency synthesis (a hit order
      within the budget makes the output a hit with every lower order a non-hit, so the output is
      exactly the first hit order); budget independence (any two sufficient budgets give verbatim
      equal outputs); non-sufficiency characterization (a non-hit output forces exhaustion: the output
      is the budget endpoint and the interval is hit-free throughout); and the pi-side instance
      interface (lw5n_find is functionally isomorphic to nsep_find under the fixed decider
      lw5n_sep_dec, the generic machine at budget lw5n_bnd q equals lw5n_nsep verbatim, and the
      synthesis specializes to the pi instance).  The sufficiency of lw5n_bnd itself (for every q a
      hit order at most lw5n_bnd q) is the instance side's duty, not claimed here; its closed proof is future work.

    Dependencies.  Stdlib [QArith.QArith], [ZArith.ZArith], [Arith.Arith], [Bool.Bool], [Lia],
      [Extraction].  Requires [LW0LeibWindow] (leiblw_Id, leiblw_id_eq, leiblw_id_inv_in), [S01_BaseRing]
      (the Set-face conjunction And := A * B), [NsepFindGeneric] (nsep_find, nsep_first, and their
      characterization theorems), [LW5SepComplexity] (the pi-side instance interface).

    References.  NsepFindGeneric.v nsep_find_hit/nsep_find_min/nsep_first_* (the sufficiency characterization joins them); LW5SepComplexity.v lw5n_find:416, lw5n_bnd/lw5n_nsep:427-429; the closed proof of the growth law is future work (its header).

    Constructivity.  Axiom-free, zero admissions, zero classical logic; the main conclusion face is
      entirely Set (leiblw_Id and And := prod), the nat order appears only in premises and at the
      endpoint equality position; proofs are structural induction plus bool case analysis; Obj.magic = 0
      on the extraction face; the closing Print Assumptions block reports Closed throughout.

    Build.  [coqc -native-compiler no -q -Q . "" -Q "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" "" NsepFirstSufficiency.v] compiles cleanly (exit 0), run thermal-guard wrapped with COQLIB/ROCQLIB exported to the 9.1 lib tree; the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith ZArith.ZArith.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
From Stdlib Require Import Extraction.
Require Import LW0LeibWindow.
Require Import S01_BaseRing.
Require Import NsepFindGeneric.
Require Import LW5SepComplexity.

(* ============================================================ *)
(* S0 identity-interface supplement: extraction of the false face of leiblw_Id *)
(*    and of the general equality face.  The library leiblw_id_eq and *)
(*    leiblw_id_inv cover only the = true face of bool; the premise of the *)
(*    non-sufficiency characterization theorem is carried by the leiblw_Id b false *)
(*    face, so the equality extraction is completed here from the induction *)
(*    definition of leiblw_Id (likewise the general extraction face at an *)
(*    arbitrary type). *)
(* ============================================================ *)

Lemma leiblw_id_eqv : forall (A : Type) (x y : A), leiblw_Id x y -> x = y.
Proof.
  intros A x y H. inversion H. reflexivity.
Qed.

Lemma leiblw_id_false_inv : forall b : bool, leiblw_Id b false -> b = false.
Proof.
  intros b H. destruct b as [|].
  - inversion H.
  - reflexivity.
Qed.

(* ============================================================ *)
(* S1 exact stop theorem: if the first hit order r lies inside the search window, *)
(*    the bounded search stops verbatim at r. *)
(* ============================================================ *)

Lemma nsep_find_exact :
  forall (dec : Q -> nat -> bool) (q : Q) (fuel n r : nat),
  (n <= r)%nat -> (r <= n + fuel)%nat ->
  leiblw_Id (dec q r) true ->
  (forall m : nat, (n <= m)%nat -> (m < r)%nat -> leiblw_Id (dec q m) false) ->
  leiblw_Id (nsep_find dec q n fuel) r.
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n r Hn1 Hn2 Hhit Hmin.
  - simpl. assert (Heq : r = n) by lia. subst r. apply leiblw_id_intro.
  - simpl. destruct (Nat.eq_dec n r) as [Heq|Hne].
    + subst r. destruct (dec q n) as [|] eqn:E.
      * apply leiblw_id_intro.
      * inversion Hhit.
    + destruct (dec q n) as [|] eqn:E.
      * assert (Hlt : (n < r)%nat) by lia.
        specialize (Hmin n (Nat.le_refl n) Hlt).
        simpl in Hmin. rewrite E in Hmin. inversion Hmin.
      * apply (IH (Datatypes.S n) r).
        -- lia.
        -- lia.
        -- exact Hhit.
        -- intros m Hm1 Hm2. apply Hmin; lia.
Qed.

(* ============================================================ *)
(* S2 under a sufficient budget the output equals verbatim the first hit order *)
(*    (the n = 0 specialization). *)
(* ============================================================ *)

Theorem nsep_first_exact :
  forall (dec : Q -> nat -> bool) (b : nat) (q : Q) (r : nat),
  (r <= b)%nat ->
  leiblw_Id (dec q r) true ->
  (forall m : nat, (m < r)%nat -> leiblw_Id (dec q m) false) ->
  leiblw_Id (nsep_first dec b q) r.
Proof.
  intros dec b q r Hb Hhit Hmin. unfold nsep_first.
  apply (nsep_find_exact dec q b 0 r).
  - apply Nat.le_0_l.
  - lia.
  - exact Hhit.
  - intros m Hm1 Hm2. apply Hmin. exact Hm2.
Qed.

(* ============================================================ *)
(* S3 sufficiency synthesis: a sufficient budget makes the output a hit with *)
(*    every order below the output a non-hit. *)
(* ============================================================ *)

Theorem nsep_first_sufficient :
  forall (dec : Q -> nat -> bool) (b : nat) (q : Q) (n0 : nat),
  (n0 <= b)%nat -> leiblw_Id (dec q n0) true ->
  And (leiblw_Id (dec q (nsep_first dec b q)) true)
      (forall m : nat, (m < nsep_first dec b q)%nat ->
                       leiblw_Id (dec q m) false).
Proof.
  intros dec b q n0 Hb Hhit. split.
  - exact (nsep_first_hit dec b q n0 Hb Hhit).
  - intros m Hlt. exact (nsep_find_min dec q b 0 m (Nat.le_0_l m) Hlt).
Qed.

(* ============================================================ *)
(* S4 budget independence of sufficiency: the first hit order does not depend on *)
(*    the particular value of a sufficient budget. *)
(* ============================================================ *)

Theorem nsep_first_budget_indep :
  forall (dec : Q -> nat -> bool) (q : Q) (b1 b2 : nat) (n0 : nat),
  (n0 <= b1)%nat -> (b1 <= b2)%nat ->
  leiblw_Id (dec q n0) true ->
  leiblw_Id (nsep_first dec b2 q) (nsep_first dec b1 q).
Proof.
  intros dec q b1 b2 n0 H1 H2 Hhit.
  apply (nsep_first_exact dec b2 q (nsep_first dec b1 q)).
  - pose proof (nsep_first_least dec b1 q n0 H1 Hhit) as Hle. lia.
  - exact (nsep_first_hit dec b1 q n0 H1 Hhit).
  - intros m Hlt. exact (nsep_find_min dec q b1 0 m (Nat.le_0_l m) Hlt).
Qed.

(* ============================================================ *)
(* S5 non-sufficiency characterization: a non-hit output forces exhaustion -- the *)
(*    output is the budget endpoint and the interval is hit-free throughout. *)
(*    Contrapositive: if the search stops short of the budget endpoint (a non- *)
(*    endpoint output) or some order in the interval is a hit, then the output is *)
(*    a hit order. *)
(* ============================================================ *)

Lemma nsep_find_false_stop :
  forall (dec : Q -> nat -> bool) (q : Q) (fuel n : nat),
  leiblw_Id (dec q (nsep_find dec q n fuel)) false ->
  leiblw_Id (nsep_find dec q n fuel) (n + fuel)%nat.
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n H.
  - simpl. replace (n + 0)%nat with n by lia. apply leiblw_id_intro.
  - simpl in H |- *. destruct (dec q n) as [|] eqn:E.
    + simpl in H. rewrite E in H. inversion H.
    + replace (n + Datatypes.S f)%nat with (Datatypes.S n + f)%nat by lia.
      apply (IH (Datatypes.S n)). exact H.
Qed.

Theorem nsep_first_exhausted :
  forall (dec : Q -> nat -> bool) (b : nat) (q : Q),
  leiblw_Id (dec q (nsep_first dec b q)) false ->
  And (leiblw_Id (nsep_first dec b q) b)
      (forall n0 : nat, (n0 <= b)%nat -> leiblw_Id (dec q n0) false).
Proof.
  intros dec b q H. unfold nsep_first in H |- *.
  assert (Hstop : leiblw_Id (nsep_find dec q 0 b) (0 + b)%nat)
    by (apply (nsep_find_false_stop dec q b 0); exact H).
  split.
  - apply (leiblw_id_eqv nat) in Hstop. rewrite Hstop.
    replace (0 + b)%nat with b by lia. apply leiblw_id_intro.
  - intros n0 Hn0. destruct (dec q n0) as [|] eqn:E.
    + exfalso.
      assert (Ht : leiblw_Id (dec q n0) true) by (apply leiblw_id_eq; exact E).
      pose proof (nsep_first_hit dec b q n0 Hn0 Ht) as HH.
      unfold nsep_first in HH.
      leiblw_id_inv_in HH. apply leiblw_id_false_inv in H.
      rewrite HH in H. discriminate H.
    + apply leiblw_id_intro.
Qed.

(* ============================================================ *)
(* S6 pi-side instance interface: the isomorphic passage and verbatim equality *)
(*    between the hardcoded machine and the generic machine, and the direct *)
(*    specialization of the sufficiency synthesis theorem to the pi instance. *)
(* ============================================================ *)

Lemma lw5n_find_nsep_find :
  forall (q : Q) (fuel n : nat),
  leiblw_Id (lw5n_find q n fuel) (nsep_find lw5n_sep_dec q n fuel).
Proof.
  intros q fuel. induction fuel as [|f IH]; intros n.
  - simpl. apply leiblw_id_intro.
  - simpl. destruct (lw5n_sep_dec q n) as [|] eqn:E.
    + apply leiblw_id_intro.
    + apply (IH (Datatypes.S n)).
Qed.

Theorem lw5n_nsep_generic_agree :
  forall q : Q,
  leiblw_Id (nsep_first lw5n_sep_dec (lw5n_bnd q) q) (lw5n_nsep q).
Proof.
  intros q. unfold nsep_first, lw5n_nsep.
  pose proof (lw5n_find_nsep_find q (lw5n_bnd q) 0) as H.
  apply (leiblw_id_eqv nat) in H. rewrite H. apply leiblw_id_intro.
Qed.

Theorem lw5n_first_sufficient :
  forall (q : Q) (b : nat) (n0 : nat),
  (n0 <= b)%nat -> leiblw_Id (lw5n_sep_dec q n0) true ->
  And (leiblw_Id (lw5n_sep_dec q (nsep_first lw5n_sep_dec b q)) true)
      (forall m : nat, (m < nsep_first lw5n_sep_dec b q)%nat ->
                       leiblw_Id (lw5n_sep_dec q m) false).
Proof.
  intros q b n0 Hb Hhit.
  exact (nsep_first_sufficient lw5n_sep_dec b q n0 Hb Hhit).
Qed.

(* ============================================================ *)
(* S7 computational spot checks on the sqrt(2) Newton instance (the decider of *)
(*    NsepFindGeneric S3), covering the three states: sufficient, non-sufficient, *)
(*    and budget-independent.  The first hit order of q = 3/2 is 2 (x_2 = 17/12, *)
(*    e_2 = 1/288, |3/2 - 17/12| = 1/12 > 1/288 leaves the window); budget 3 *)
(*    suffices and yields 2, budget 1 exhausts without a hit and yields the *)
(*    endpoint 1, and budget 10 agrees with budget 3 at 2. *)
(* ============================================================ *)

Eval vm_compute in (nsep_first ir2_sep_dec 3 (3 # 2)).
Eval vm_compute in (nsep_first ir2_sep_dec 1 (3 # 2)).
Eval vm_compute in (nsep_first ir2_sep_dec 10 (3 # 2)).

(* ============================================================ *)
(* S8 extraction check and the assumptions audit. *)
(* ============================================================ *)

Separate Extraction nsep_find nsep_first.

Print Assumptions leiblw_id_eqv.
Print Assumptions leiblw_id_false_inv.
Print Assumptions nsep_find_exact.
Print Assumptions nsep_first_exact.
Print Assumptions nsep_first_sufficient.
Print Assumptions nsep_first_budget_indep.
Print Assumptions nsep_find_false_stop.
Print Assumptions nsep_first_exhausted.
Print Assumptions lw5n_find_nsep_find.
Print Assumptions lw5n_nsep_generic_agree.
Print Assumptions lw5n_first_sufficient.
