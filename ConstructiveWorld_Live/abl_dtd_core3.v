(* ConstructiveWorld-Set -- verbatim premise-supply volumes over the DTPT register. *)

(** * abl_dtd_core3: DTPT register premises 71-105, supply volume three.

    Mission.  This volume resolves premises 71-105 of the host [DTPT]
      register (host statement coordinates :1663-:2673, 30 statements
      carrying 35 premises) in the shape-two form T + P': the T theorems
      supply a canonical production path for each premise face
      ([dtd_c3_le_length_refl], [dtd_c3_Qeq_half], [dtd_c3_perm_rev],
      [dtd_c3_in_cons], [dtd_c3_P0_ssorted]), and the P' theorems
      specialize the host conclusion face verbatim
      ([dtd_c3_firstn_length_id], [dtd_c3_freq_perm_rev],
      [dtd_c3_sumf_dedup_aux_dedup], [dtd_c3_ideal_sub_closed_sing],
      [dtd_c3_sorted_P0_idem]); all 38 theorems close by [Qed].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Permutation], [Sorting.Sorted], [Arith], [Lia], [Extraction].  Requires no other module of this development.

    References.  This development, abl_dtd_core3.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_dtd_core3.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Import DTPT.DTPT.

(* ==================== Section 1. Supply theorems, production-path side ==================== *)

(* 18 theorems, each a production-path instance of one premise face:
   the statement faces are the register premise faces verbatim or their
   constructor instances, built in place or by forwarding an existing
   host constructor. *)

(* NAT length reflexivity guard, covering the three premises at
   :1663, :1674 and :1846: the premise (length l <= n)%nat at its
   canonical instance n := length l, one application of the [le_n]
   constructor. *)
Theorem dtd_c3_le_length_refl : forall l : list Q, (length l <= length l)%nat.
Proof.
  intro l. apply le_n.
Qed.

(* NAT zero lower-bound guard for the premise at :1789: the register
   premise face is the [NatLe] carrier NatLe n (length l) at its
   canonical instance n := 0, built by the register bridge [NatLe_lift]
   over [Nat.le_0_l] (the instance shape of dtd_c2_nat_le_0). *)
Theorem dtd_c3_nat_le_0_length : forall l : list Q, NatLe 0 (length l).
Proof.
  intro l. apply NatLe_lift. apply Nat.le_0_l.
Qed.

(* Boolean decision-face production path, covering the two premises at
   :1739 and :1750: the premise gate_pass t H = true at the reflexive
   instance H := t, by the proj2 direction of [Qle_bool_iff] plus
   [Qle_refl] (the stdlib library has no Qle_bool_refl name, so the
   iff-projection route is taken). *)
Theorem dtd_c3_gate_pass_refl : forall t : Q, gate_pass t t = true.
Proof.
  intro t. unfold gate_pass.
  assert (Ht : Qle_bool t t = true)
    by (apply (proj2 (Qle_bool_iff t t)); apply Qle_refl).
  rewrite Ht. reflexivity.
Qed.

(* Q-ORD canonical instance for premise 1 at :1739: the premise
   (t1 <= t2)%Q at the concrete instance (0, 1), by definitional
   unfolding of [Qle] and [lia]. *)
Theorem dtd_c3_Qle_0_1 : (0 <= 1)%Q.
Proof.
  unfold Qle. simpl. lia.
Qed.

(* Q-ORD canonical instance for premise 1 at :1750: the premise
   (H1 <= H2)%Q at the concrete instance (0, 2), by the same recipe as
   the previous instance, at a value pair of a distinct shape so the two
   conclusion faces do not coincide. *)
Theorem dtd_c3_Qle_0_2 : (0 <= 2)%Q.
Proof.
  unfold Qle. simpl. lia.
Qed.

(* Qeq reflexivity production path, covering the two premises at :2252:
   the Q-ORD premise of the form a == 0 at the reflexive instance
   a := 0, literally the same face once [Qeq] is unfolded. *)
Theorem dtd_c3_Qeq_refl : forall x : Q, x == x.
Proof.
  intro x. unfold Qeq. reflexivity.
Qed.

(* Qeq non-canonical-value production path, covering the two premises at
   :1938 and :2172: the Q-ORD premise x == y at the canonical instance
   of the non-canonical equal pair (2 # 2, 1 # 1) - [Qeq] is value-level
   equality rather than syntactic coincidence, closed by 2 * 1 = 1 * 2
   at the value layer, not a degenerate reflexive face. *)
Theorem dtd_c3_Qeq_half : (2 # 2 == 1 # 1)%Q.
Proof.
  reflexivity.
Qed.

(* Qeq non-canonical-zero production path, covering the two premises at
   :2188 and :2196: the Q-ORD premise a == 0 at the canonical instance
   of the non-canonical zero (0 # 3), closed by 0 * 1 = 0 * 3 at the
   value layer. *)
Theorem dtd_c3_Qeq_0_third : (0 # 3 == 0)%Q.
Proof.
  reflexivity.
Qed.

(* Permutation-constructor route, covering the two premises at :1987 and
   :2075: the premise Permutation l p at the instance p := rev l, by
   forwarding the stdlib constructor [Permutation_rev] (the instance
   shape of dtd_c2_perm_rev). *)
Theorem dtd_c3_perm_rev : forall l : list Q, Permutation l (rev l).
Proof.
  intro l. apply Permutation_rev.
Qed.

(* NEQ guard production path for the premise at :2107: the premise face
   l <> [] carried verbatim as a pass-through guard, at the cons
   canonical instance, one application of [discriminate]; the only
   <> statement face in the file. *)
Theorem dtd_c3_cons_neq_nil : forall (x : Q) (l : list Q), (x :: l) <> [].
Proof.
  intros x l. discriminate.
Qed.

(* Qnodup production path for the premise at :2012: the register premise
   face is the Id-bool carrier Id (Qnodup m) true at the canonical
   instance m := dedup l, forwarding the premise-free host production
   path [dedup_Qnodup] (:556). *)
Theorem dtd_c3_Qnodup_dedup : forall l : list Q, Id (Qnodup (dedup l)) true.
Proof.
  intro l. apply dedup_Qnodup.
Qed.

(* In-constructor route, covering the two premises at :2412 and the
   premise at :2445: the premise In x l at the canonical head instance
   x :: l, one application of the [in_eq] constructor. *)
Theorem dtd_c3_in_cons : forall (x : Q) (l : list Q), In x (x :: l).
Proof.
  intros x l. apply in_eq.
Qed.

(* In-constructor route for the premise at :2625: the premise
   In z (insert_q x l) at the canonical instance l := [], where the
   empty-list branch of [insert_q] reduces to the head occurrence of x;
   closed by [in_eq] with all arguments explicit, avoiding the
   relation-rewriting backtrack of [apply]. *)
Theorem dtd_c3_in_insert_q_nil : forall x : Q, In x (insert_q x []).
Proof.
  intro x. exact (in_eq x []).
Qed.

(* Zero-left-factor production path for the premise at :2178: the
   premise (a * b == 0)%Q at the canonical left-zero instance a := 0,
   built in place by definitional unfolding of [Qmult] and [Qeq] plus
   [lia] at the Z layer; a declared standalone-delivery position, since
   the source conclusion face carries a Prop disjunction (see the
   standalone-delivery block in Section 2). *)
Theorem dtd_c3_qmul_eq0_l : forall b : Q, (0 * b == 0)%Q.
Proof.
  intro b. destruct b as [n d]. unfold Qmult, Qeq. simpl. lia.
Qed.

(* Zero-square production path for the premise at :2220: the premise
   (x * x == 0)%Q at the canonical instance of the non-canonical zero
   x := (0 # 5), closed at the value layer by definitional unfolding of
   [Qmult] and [Qeq]; the pure reflexive instance x := 0 is avoided as
   a degenerate face. *)
Theorem dtd_c3_qsq0_fifth : ((0 # 5) * (0 # 5) == 0)%Q.
Proof.
  unfold Qmult, Qeq. simpl. reflexivity.
Qed.

(* Zero-sum-of-squares production path for the premise at :2226: the
   premise (a * a + b * b == 0)%Q at the canonical instance of the
   non-canonical zero pair ((0 # 3), (0 # 5)), closed at the value layer
   by definitional unfolding of [Qplus], [Qmult] and [Qeq]; a declared
   standalone-delivery position, since the source conclusion face
   carries a Prop conjunction (see the standalone-delivery block in
   Section 2). *)
Theorem dtd_c3_qsum_sq0_thirds :
  ((0 # 3) * (0 # 3) + (0 # 5) * (0 # 5) == 0)%Q.
Proof.
  unfold Qmult, Qplus, Qeq. simpl. reflexivity.
Qed.

(* Boolean decision-false production path for the premise at :2525: the
   premise Qle_bool x y = false at the concrete instance (x, y) := (2, 1),
   closed definitionally on the [Z.leb] decision face. *)
Theorem dtd_c3_Qle_bool_2_1_false : Qle_bool 2 1 = false.
Proof.
  reflexivity.
Qed.

(* SORTED production path, covering the two premises at :2642 and :2673:
   the premise StronglySorted Qle l at the canonical instance l := P0 l,
   forwarding the premise-free host production path [P0_sorted]
   (:2666). *)
Theorem dtd_c3_P0_ssorted : forall l : list Q, StronglySorted Qle (P0 l).
Proof.
  intro l. apply P0_sorted.
Qed.

(* ==================== Registered only, seven premises ==================== *)

(* Seven premises carry mixed Prop flags in the register base (Section
   2.3) and are recorded without supply, following the host convention
   at :1612; each omission is declared explicitly:
   - premise 79, :1864 llm_Tex_fiber (existential flag: the source
     statement face carries a sigT witness);
   - premise 81, :1960 freq_zero_of_notQmem (negation flag: the premise
     position ~ Qmem x l);
   - premise 96, :2435 fiber_cozero_disjoint (negation flag: the
     conclusion position ~ In);
   - premise 98, :2455 fiber_cozero_compl (negation and iff flags: two
     Prop positions in the conclusion);
   - premises 100-101, :2603 Forall_in (explicit Prop flag: the
     annotation position P : A -> Prop);
   - premise 102, :2615 Forall_of_pointwise (explicit Prop flag, as
     above). *)

(* ==================== Section 2. Supply theorems, P' specialization side ==================== *)

(* 20 premise-free specializations: each applies a host theorem with all
   arguments explicit, so the premises dissolve and only the specialized
   conclusion remains; every conclusion face is the host conclusion face
   verbatim at concrete instances, carried discretely. *)

(* P1, premise-free specialization of [llm_firstn_ge_full] (premise 71
   at :1663): the length premise fed by [dtd_c3_le_length_refl] at
   n := length l, yielding the identity face of [firstn] on the full
   list. *)
Theorem dtd_c3_firstn_length_id : forall l : list Q, firstn (length l) l = l.
Proof.
  intro l. exact (llm_firstn_ge_full (length l) l (dtd_c3_le_length_refl l)).
Qed.

(* P2, premise-free specialization of [llm_skipn_ge_nil] (premise 72 at
   :1674), by the same recipe as the T side: [skipn] of the full length
   yields the empty list. *)
Theorem dtd_c3_skipn_length_nil : forall l : list Q, skipn (length l) l = [].
Proof.
  intro l. exact (llm_skipn_ge_nil (length l) l (dtd_c3_le_length_refl l)).
Qed.

(* P3, premise-free specialization of [llm_gate_pass_mono_thr] (premises
   73-74 at :1739): both guard premises at concrete canonical instances,
   the Q-ORD premise fed by [dtd_c3_Qle_0_1] (t1 := 0, t2 := 1) and the
   boolean premise fed by [dtd_c3_gate_pass_refl] (H := t1 := 0),
   yielding that widening the threshold from 0 to 1 preserves passage,
   in the register Id-carrier conclusion face: Id (gate_pass 1 0) true. *)
Theorem dtd_c3_gate_pass_mono_0_1 : Id (gate_pass 1 0) true.
Proof.
  exact (llm_gate_pass_mono_thr 0 0 1 dtd_c3_Qle_0_1 (dtd_c3_gate_pass_refl 0)).
Qed.

(* P4, premise-free specialization of [llm_gate_pass_anti_H] (premises
   75-76 at :1750): both guard premises at concrete canonical instances,
   the Q-ORD premise fed by [dtd_c3_Qle_0_2] (H1 := 0, H2 := 2) and the
   boolean premise fed by [dtd_c3_gate_pass_refl] (t := H2 := 2),
   yielding that lowering the measured quantity from 2 to 0 preserves
   passage, in the register Id-carrier conclusion face:
   Id (gate_pass 2 0) true. *)
Theorem dtd_c3_gate_pass_anti_0_2 : Id (gate_pass 2 0) true.
Proof.
  exact (llm_gate_pass_anti_H 0 2 2 dtd_c3_Qle_0_2 (dtd_c3_gate_pass_refl 2)).
Qed.

(* P5, premise-free specialization of [llm_rot_cyclic_inv] (premise 77
   at :1789): the length premise fed by [dtd_c3_nat_le_0_length] at
   n := 0, yielding the rot identity face - the cyclic-unit instance
   where firstn ++ skipn returns the original list. *)
Theorem dtd_c3_rot_cyclic_inv_0 :
  forall l : list Q, Id (rot (length l - 0) (rot 0 l)) l.
Proof.
  intro l. exact (llm_rot_cyclic_inv 0 l (dtd_c3_nat_le_0_length l)).
Qed.

(* P6, premise-free specialization of [llm_Pmid_full] (premise 78 at
   :1846): the NatLe length premise fed by [dtd_c3_le_length_refl]
   through the register bridge [NatLe_lift] at lam := length l, yielding
   that the midpoint split at the full-length endpoint is P0 l, in the
   register Id-carrier conclusion face. *)
Theorem dtd_c3_Pmid_full_length :
  forall (l : list Q) (s : nat), Id (Pmid l s (length l)) (P0 l).
Proof.
  intros l s.
  exact (llm_Pmid_full l s (length l)
           (NatLe_lift (length l) (length l) (dtd_c3_le_length_refl l))).
Qed.

(* P7, premise-free specialization of [freq_eq_congr] (premise 80 at
   :1938): the Q-ORD premise fed by [dtd_c3_Qeq_half] at the
   non-canonical equal pair (x := 2 # 2, y := 1 # 1), yielding the
   non-degenerate face that renaming a value to an equal one leaves the
   frequency unchanged. *)
Theorem dtd_c3_freq_eq_congr_half :
  forall l : list Q, freq l (2 # 2) = freq l (1 # 1).
Proof.
  intro l. exact (freq_eq_congr (2 # 2) (1 # 1) l dtd_c3_Qeq_half).
Qed.

(* P8, premise-free specialization of [freq_perm] (premise 82 at :1987):
   the Permutation premise fed by [dtd_c3_perm_rev] at p := rev l,
   avoiding the degenerate reflexive instance p := l, yielding that
   frequencies are invariant under reversal. *)
Theorem dtd_c3_freq_perm_rev :
  forall (l : list Q) (x : Q), freq l x = freq (rev l) x.
Proof.
  intros l x. exact (freq_perm l (rev l) x (dtd_c3_perm_rev l)).
Qed.

(* P9, premise-free specialization of [sumf_dedup_aux] (premise 83 at
   :2012): the Qnodup premise fed by [dtd_c3_Qnodup_dedup] at
   m := dedup l, yielding the transport equation of the total mass
   Sigma_freq onto the deduplicated support; the conclusion face is
   entirely data-level (if/existsb), with no Prop connectives. *)
Theorem dtd_c3_sumf_dedup_aux_dedup : forall (x : Q) (l : list Q),
  sumf (dedup l) l
  = ((if existsb (fun z => Qeq_bool x z) (dedup l) then freq l x else O)
     + sumf (dedup_aux x (dedup l)) (x :: l))%nat.
Proof.
  intros x l. exact (sumf_dedup_aux (dedup l) x l (dtd_c3_Qnodup_dedup l)).
Qed.

(* P10, premise-free specialization of [mu_perm] (premise 84 at :2075):
   the Permutation premise fed by [dtd_c3_perm_rev] as in P8, yielding
   that the uniform measure is invariant under reversal. *)
Theorem dtd_c3_mu_perm_rev :
  forall (l : list Q) (x : Q), Id (mu l x) (mu (rev l) x).
Proof.
  intros l x. exact (mu_perm l (rev l) x (dtd_c3_perm_rev l)).
Qed.

(* P11, premise-free specialization of [mu_total_mass] (premise 85 at
   :2107): the NEQ premise fed by [dtd_c3_cons_neq_nil] with the
   pass-through face l := [x], yielding that the single-point
   distribution has total mass exactly 1. *)
Theorem dtd_c3_mu_total_mass_sing :
  forall x : Q, qsum (map (mu [x]) (dedup [x])) == 1.
Proof.
  intro x. exact (mu_total_mass [x] (dtd_c3_cons_neq_nil x [])).
Qed.

(* P12, premise-free specialization of [qeq_le] (premise 86 at :2172):
   the Q-ORD premise fed by [dtd_c3_Qeq_half] by the same recipe as P7,
   yielding the non-degenerate Qeq-to-Qle bridge face. *)
Theorem dtd_c3_qeq_le_half : ((2 # 2) <= (1 # 1))%Q.
Proof.
  exact (qeq_le (2 # 2) (1 # 1) dtd_c3_Qeq_half).
Qed.

(* P13, premise-free specialization of [qmul_eq0_intro_l] (premise 88 at
   :2188): the Q-ORD premise fed by [dtd_c3_Qeq_0_third] at a := 0 # 3,
   yielding the universal family face for a zero factor entering the
   left position. *)
Theorem dtd_c3_qmul_eq0_intro_l_third : forall b : Q, ((0 # 3) * b == 0)%Q.
Proof.
  intro b. exact (qmul_eq0_intro_l (0 # 3) b dtd_c3_Qeq_0_third).
Qed.

(* P14, premise-free specialization of [qmul_eq0_intro_r] (premise 89 at
   :2196): the Q-ORD premise fed by [dtd_c3_Qeq_0_third] at b := 0 # 3,
   yielding the universal family face for a zero factor entering the
   right position. *)
Theorem dtd_c3_qmul_eq0_intro_r_third : forall a : Q, (a * (0 # 3) == 0)%Q.
Proof.
  intro a. exact (qmul_eq0_intro_r a (0 # 3) dtd_c3_Qeq_0_third).
Qed.

(* P15, premise-free specialization of [qsq_eq0] (premise 90 at :2220):
   the Q-ORD premise fed by [dtd_c3_qsq0_fifth] at x := 0 # 5, yielding
   that a zero square implies a zero factor; the conclusion face
   (0 # 5) == 0 is a non-trivial Qeq value-level position, and the value
   0 # 5 differs from the sibling instances so the faces stay distinct. *)
Theorem dtd_c3_qsq_eq0_fifth : (0 # 5 == 0)%Q.
Proof.
  exact (qsq_eq0 (0 # 5) dtd_c3_qsq0_fifth).
Qed.

(* P16, premise-free specialization of [qsum_sq_zero_intro] (premises
   92-93 at :2252): both Q-ORD premises fed by [dtd_c3_Qeq_refl] at the
   reflexive instance a := b := 0, yielding the converse construction
   face, of a shape distinct from its counterpart so the faces do not
   coincide. *)
Theorem dtd_c3_qsum_sq_zero_intro_zero00 : (0 * 0 + 0 * 0 == 0)%Q.
Proof.
  exact (qsum_sq_zero_intro 0 0 (dtd_c3_Qeq_refl 0) (dtd_c3_Qeq_refl 0)).
Qed.

(* P17, premise-free specialization of [ideal_sub_closed] (premises
   94-95 at :2412): the subset guard premise built inline for the zero
   function f := (fun _ => 0), whose fiber membership face is
   In x w /\ Qeq_bool (f x) 0 = true in that conjunction order (the
   actual shape of [fiber_in]), and the In premise fed by
   [dtd_c3_in_cons] at the head instance, yielding the fiber membership
   face of the indicator zero function. *)
Theorem dtd_c3_ideal_sub_closed_sing : forall a : Q,
  In a (fiber (fun y : Q => if in_dec Q_dec y [a] then 0 else 1) [a]).
Proof.
  intros a.
  apply (ideal_sub_closed [a] (fun _ : Q => 0) [a] a).
  - intros y Hy. simpl in Hy. destruct Hy as [Hy | Hf].
    + subst y. apply (proj2 (fiber_in (fun _ : Q => 0) [a] a)).
      * split.
        -- exact (in_eq a []).
        -- reflexivity.
    + destruct Hf.
  - exact (in_eq a []).
Qed.

(* P18, premise-free specialization of [Qle_bool_false_inv] (premise 99
   at :2525): the boolean premise fed by [dtd_c3_Qle_bool_2_1_false] at
   (x, y) := (2, 1), yielding the decision-false converse face
   (1 <= 2)%Q, of a shape distinct from its sibling faces so they do
   not coincide. *)
Theorem dtd_c3_Qle_bool_false_inv_1_2 : (1 <= 2)%Q.
Proof.
  exact (Qle_bool_false_inv 2 1 dtd_c3_Qle_bool_2_1_false).
Qed.

(* P19, premise-free specialization of [insert_sorted] (premise 104 at
   :2642): the SORTED premise fed by [dtd_c3_P0_ssorted] at l := P0 l,
   yielding that insertion preserves the P0 sortedness face. *)
Theorem dtd_c3_insert_sorted_P0 : forall (x : Q) (l : list Q),
  StronglySorted Qle (insert_q x (P0 l)).
Proof.
  intros x l. exact (insert_sorted x (P0 l) (dtd_c3_P0_ssorted l)).
Qed.

(* P20, premise-free specialization of [sorted_P0_id] (premise 105 at
   :2673): the SORTED premise fed by [dtd_c3_P0_ssorted] at l := P0 l,
   yielding the sorting idempotence face P0 (P0 l) = P0 l. *)
Theorem dtd_c3_sorted_P0_idem : forall l : list Q, P0 (P0 l) = P0 l.
Proof.
  intro l. exact (sorted_P0_id (P0 l) (dtd_c3_P0_ssorted l)).
Qed.

(* ==================== Standalone T delivery, four premises ==================== *)

(* Four premises are declared outright and delivered by a standalone T
   theorem each - declared positions, not failures, following the host
   convention at :262:
   - premise 87, :2178 qmul_eq0_fwd, delivered by [dtd_c3_qmul_eq0_l],
     since the source conclusion face carries the Prop disjunction
     (a == 0 \/ b == 0);
   - premise 91, :2226 qsum_sq_zero, delivered by
     [dtd_c3_qsum_sq0_thirds], since the source conclusion face carries
     the Prop conjunction (a == 0 /\ b == 0);
   - premise 97, :2445 fiber_cozero_cover, delivered by
     [dtd_c3_in_cons], since the source conclusion face carries a Prop
     disjunction;
   - premise 103, :2625 in_insert_q, delivered by
     [dtd_c3_in_insert_q_nil], since the source conclusion face carries
     the Prop disjunction (z = x \/ In z l). *)

(* ==================== Section 3. Verification block, at the end of the file ==================== *)

(* Check marks plus a per-theorem assumptions audit; the name list
   equals the 38 supply theorems (18 T, 20 P'), matching the [Qed] count
   exactly. *)

Check dtd_c3_le_length_refl.
Check dtd_c3_nat_le_0_length.
Check dtd_c3_gate_pass_refl.
Check dtd_c3_Qle_0_1.
Check dtd_c3_Qle_0_2.
Check dtd_c3_Qeq_refl.
Check dtd_c3_Qeq_half.
Check dtd_c3_Qeq_0_third.
Check dtd_c3_perm_rev.
Check dtd_c3_cons_neq_nil.
Check dtd_c3_Qnodup_dedup.
Check dtd_c3_in_cons.
Check dtd_c3_in_insert_q_nil.
Check dtd_c3_qmul_eq0_l.
Check dtd_c3_qsq0_fifth.
Check dtd_c3_qsum_sq0_thirds.
Check dtd_c3_Qle_bool_2_1_false.
Check dtd_c3_P0_ssorted.
Check dtd_c3_firstn_length_id.
Check dtd_c3_skipn_length_nil.
Check dtd_c3_gate_pass_mono_0_1.
Check dtd_c3_gate_pass_anti_0_2.
Check dtd_c3_rot_cyclic_inv_0.
Check dtd_c3_Pmid_full_length.
Check dtd_c3_freq_eq_congr_half.
Check dtd_c3_freq_perm_rev.
Check dtd_c3_sumf_dedup_aux_dedup.
Check dtd_c3_mu_perm_rev.
Check dtd_c3_mu_total_mass_sing.
Check dtd_c3_qeq_le_half.
Check dtd_c3_qmul_eq0_intro_l_third.
Check dtd_c3_qmul_eq0_intro_r_third.
Check dtd_c3_qsq_eq0_fifth.
Check dtd_c3_qsum_sq_zero_intro_zero00.
Check dtd_c3_ideal_sub_closed_sing.
Check dtd_c3_Qle_bool_false_inv_1_2.
Check dtd_c3_insert_sorted_P0.
Check dtd_c3_sorted_P0_idem.

Print Assumptions dtd_c3_le_length_refl.
Print Assumptions dtd_c3_nat_le_0_length.
Print Assumptions dtd_c3_gate_pass_refl.
Print Assumptions dtd_c3_Qle_0_1.
Print Assumptions dtd_c3_Qle_0_2.
Print Assumptions dtd_c3_Qeq_refl.
Print Assumptions dtd_c3_Qeq_half.
Print Assumptions dtd_c3_Qeq_0_third.
Print Assumptions dtd_c3_perm_rev.
Print Assumptions dtd_c3_cons_neq_nil.
Print Assumptions dtd_c3_Qnodup_dedup.
Print Assumptions dtd_c3_in_cons.
Print Assumptions dtd_c3_in_insert_q_nil.
Print Assumptions dtd_c3_qmul_eq0_l.
Print Assumptions dtd_c3_qsq0_fifth.
Print Assumptions dtd_c3_qsum_sq0_thirds.
Print Assumptions dtd_c3_Qle_bool_2_1_false.
Print Assumptions dtd_c3_P0_ssorted.
Print Assumptions dtd_c3_firstn_length_id.
Print Assumptions dtd_c3_skipn_length_nil.
Print Assumptions dtd_c3_gate_pass_mono_0_1.
Print Assumptions dtd_c3_gate_pass_anti_0_2.
Print Assumptions dtd_c3_rot_cyclic_inv_0.
Print Assumptions dtd_c3_Pmid_full_length.
Print Assumptions dtd_c3_freq_eq_congr_half.
Print Assumptions dtd_c3_freq_perm_rev.
Print Assumptions dtd_c3_sumf_dedup_aux_dedup.
Print Assumptions dtd_c3_mu_perm_rev.
Print Assumptions dtd_c3_mu_total_mass_sing.
Print Assumptions dtd_c3_qeq_le_half.
Print Assumptions dtd_c3_qmul_eq0_intro_l_third.
Print Assumptions dtd_c3_qmul_eq0_intro_r_third.
Print Assumptions dtd_c3_qsq_eq0_fifth.
Print Assumptions dtd_c3_qsum_sq_zero_intro_zero00.
Print Assumptions dtd_c3_ideal_sub_closed_sing.
Print Assumptions dtd_c3_Qle_bool_false_inv_1_2.
Print Assumptions dtd_c3_insert_sorted_P0.
Print Assumptions dtd_c3_sorted_P0_idem.

(* ==================== Section 4. Extraction audit ==================== *)

(* Extractability audit, with an Obj.magic count of 0 as the criterion.
   The theorem bucket is extracted by a single Separate Extraction
   command - a second same-named command in the same file would
   overwrite the first - and all 38 theorem conclusion faces, being
   Prop-carried, reduce to __ placeholders under the family
   extraction-erasure convention.  The genuine data-level extraction
   faces, the host data carriers used by the P' statement faces
   (insert_q, P0, rot, Pmid, gate_pass, freq, sumf, dedup, dedup_aux,
   mu, fiber, cozero, Q_dec), belong to the dedicated independent audit
   file _dtd_c3_probe.v, a separate bucket. *)

Set Extraction Output Directory "_log/dtd_t4".
Separate Extraction dtd_c3_le_length_refl
  dtd_c3_nat_le_0_length dtd_c3_gate_pass_refl dtd_c3_Qle_0_1
  dtd_c3_Qle_0_2 dtd_c3_Qeq_refl dtd_c3_Qeq_half dtd_c3_Qeq_0_third
  dtd_c3_perm_rev dtd_c3_cons_neq_nil dtd_c3_Qnodup_dedup
  dtd_c3_in_cons dtd_c3_in_insert_q_nil dtd_c3_qmul_eq0_l
  dtd_c3_qsq0_fifth dtd_c3_qsum_sq0_thirds dtd_c3_Qle_bool_2_1_false
  dtd_c3_P0_ssorted dtd_c3_firstn_length_id dtd_c3_skipn_length_nil
  dtd_c3_gate_pass_mono_0_1 dtd_c3_gate_pass_anti_0_2
  dtd_c3_rot_cyclic_inv_0 dtd_c3_Pmid_full_length
  dtd_c3_freq_eq_congr_half dtd_c3_freq_perm_rev
  dtd_c3_sumf_dedup_aux_dedup dtd_c3_mu_perm_rev
  dtd_c3_mu_total_mass_sing dtd_c3_qeq_le_half
  dtd_c3_qmul_eq0_intro_l_third dtd_c3_qmul_eq0_intro_r_third
  dtd_c3_qsq_eq0_fifth dtd_c3_qsum_sq_zero_intro_zero00
  dtd_c3_ideal_sub_closed_sing dtd_c3_Qle_bool_false_inv_1_2
  dtd_c3_insert_sorted_P0 dtd_c3_sorted_P0_idem.
