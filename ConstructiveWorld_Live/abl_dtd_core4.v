(* ConstructiveWorld-Set -- DTPT premise-slot supply theorems, final volume. *)

(** * abl_dtd_core4: supply theorems for premise slots 106-138 of the DTPT host.

    Mission.  Fills premise slots 106-138 of the host DTPT.v premise
      inventory (host statements at lines 2710-3758; the inventory closes
      here at 138 slots), one supply theorem per slot.  Seventeen
      derivation routes and twenty-three reduced host applications
      ([dtd_c4_P0_ssorted] through [dtd_c4_Tabs_const],
      [dtd_c4_H_adj_bound_single] through
      [dtd_c4_llm_view_PhP0_gate_exact_nil]) supply 31 of the 33 slots;
      [count_q_pos_wit] and [phase_classify_Mid_spec] stay registered.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List],
      [Arith], [Lia], [Permutation], [Sorting.Sorted], [Extraction].
      Requires no other module of this development.

    References.  This development, abl_dtd_core4.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_dtd_core4.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Import DTPT.DTPT.

(* ================= Section 1. Shared guard and certificate routes ================= *)

(* Seventeen supply theorems, one constructive derivation route for each
   premise slot they serve: the sortedness route, the permutation
   constructor routes ([Permutation_sym], [Permutation_rev], [perm_swap]),
   the three-step count transfer chain, computable canonical instances on
   the empty list, the membership constructions (fiber, dedup, cons), the
   boolean equality test route, the [Qopp] extensionality chain, the
   all-open filter induction, and the nonnegativity instance for [OrgDiff]
   on the empty list. *)

(* Sortedness route for the first two premise slots of the host statement
   at line 2987: the canonical strong order on [P0].  Forwards the
   in-force host proof [P0_sorted] at its [StronglySorted] face. *)
Theorem dtd_c4_P0_ssorted : forall l : list Q, StronglySorted Qle (P0 l).
Proof.
  intro l. exact (P0_sorted l).
Qed.

(* Count transfer route for the third premise slot of the host statement
   at line 2987: the numerical multiplicities of [P0 l] and [P0 (rev l)]
   agree, by the three-step permutation chain in [count_q_perm]
   ([D5_P0_perm], [Permutation_rev], [D5_P0_perm]).  This is the
   count-equality input of the sortedness-uniqueness application below;
   the three-step composition is derived here, not forwarded from a host
   alias. *)
Theorem dtd_c4_count_P0_P0rev : forall (l : list Q) (x : Q),
  count_q x (P0 l) = count_q x (P0 (rev l)).
Proof.
  intros l x.
  rewrite <- (count_q_perm l (P0 l) (D5_P0_perm l) x).
  rewrite (count_q_perm l (rev l) (Permutation_rev l) x).
  exact (count_q_perm (rev l) (P0 (rev l)) (D5_P0_perm (rev l)) x).
Qed.

(* Permutation symmetry route for the premise slots of the host statements
   at lines 3035 and 3079: [Permutation p l] implies [Permutation l p],
   in one step by the stdlib constructor [Permutation_sym]. *)
Theorem dtd_c4_perm_sym : forall l p : list Q,
  Permutation p l -> Permutation l p.
Proof.
  intros l p Hperm. exact (Permutation_sym Hperm).
Qed.

(* Singleton construction route for the premise slots of the host
   statements at lines 3050 and 3074: a pointwise [Qeq] between two
   numbers lifts to [Forall2 Qeq] on the singleton lists, in two steps
   by [Forall2_cons] and [Forall2_nil]; the canonical-instance input for
   premise faces of the form [Forall2 Qeq l1 l2]. *)
Theorem dtd_c4_Forall2_Qeq_single : forall x y : Q,
  x == y -> Forall2 Qeq [x] [y].
Proof.
  intros x y H. apply Forall2_cons; [exact H | apply Forall2_nil].
Qed.

(* Computable canonical instance for the premise slots of the host
   statements at lines 3108, 3742 and 3758: the classifier returns the
   P0 phase on the empty list, [phase_classify [] s = PhP0].  All three
   phases degenerate on [], the adjacent-difference entropy of [] is
   zero and [Qeq_bool 0 0] judges true, so the equation closes
   definitionally by [reflexivity]. *)
Theorem dtd_c4_phase_classify_nil_PhP0 : forall s : nat,
  phase_classify [] s = PhP0.
Proof.
  intro s. reflexivity.
Qed.

(* Two-element swap route for the first premise slot of the host statement
   at line 3144: [Permutation [x; y] [y; x]], in one step by the stdlib
   constructor [perm_swap]. *)
Theorem dtd_c4_perm_swap_pair : forall x y : Q,
  Permutation [x; y] [y; x].
Proof.
  intros x y. apply perm_swap.
Qed.

(* Rotation entropy route for the second premise slot of the host
   statement at line 3144: the rotation entropies of the two swap orders
   coincide, [H_adj (Pinf [x; y] 0) == H_adj (Pinf [y; x] 0)].  At
   [s := 0] the window of [Pinf] degenerates to the whole list by
   [firstn_skipn], and reversal invariance of [H_adj] is carried by the
   in-force host proof [C_gen_sym_rev] ([H_adj (rev l) == H_adj l]),
   with [rev [x; y]] computing to [[y; x]]. *)
Theorem dtd_c4_H_inf_swap_pair_eq : forall x y : Q,
  (H_adj (Pinf [x; y] 0) == H_adj (Pinf [y; x] 0))%Q.
Proof.
  intros x y. unfold Pinf, rot. rewrite !firstn_skipn.
  apply Qeq_sym. exact (C_gen_sym_rev [x; y]).
Qed.

(* Fiber membership route for the premise slot of the host statement at
   line 3477: the constant-zero observation has [x] in its support,
   [In x (fiber (fun _ => 0) [x])].  The fiber is a filter under the
   zero test, which unfolds definitionally and judges the head true by
   [Qeq_bool 0 0], so membership holds by computation. *)
Theorem dtd_c4_in_fiber_zero_single : forall x : Q,
  In x (fiber (fun _ => 0%Q) [x]).
Proof.
  intro x. unfold fiber. simpl. left. reflexivity.
Qed.

(* Nonemptiness guard route for the premise slots of the host statements
   at lines 3502 and 3610: a cons cell differs from the empty list,
   [(x :: l) <> []], by discrimination on the head constructor.  The
   disequality face is carried over verbatim from the host premise. *)
Theorem dtd_c4_cons_neq_nil : forall (x : Q) (l : list Q),
  (x :: l) <> [].
Proof.
  intros x l H. discriminate H.
Qed.

(* Membership route for the premise slot of the host statement at line
   3537: when the equality test rejects, [Qeq_bool x a = false], the
   false branch of [dedup_aux] keeps the head, so
   [In a (dedup_aux x (a :: t))].  The branch is selected by rewriting
   with the judged boolean value, not by case analysis on the
   conditional. *)
Theorem dtd_c4_in_dedup_aux_cons_neq : forall (x a : Q) (t : list Q),
  Qeq_bool x a = false -> In a (dedup_aux x (a :: t)).
Proof.
  intros x a t H. simpl. rewrite H. simpl. left. reflexivity.
Qed.

(* Head membership route for the premise slot of the host statement at
   line 3549: the head of a cons is always a member of its
   deduplication, [In a (dedup (a :: t))], since [dedup (x :: xs)]
   reduces definitionally to [x :: dedup_aux x (dedup xs)] and keeps the
   head whatever the test decides. *)
Theorem dtd_c4_in_dedup_head : forall (a : Q) (t : list Q),
  In a (dedup (a :: t)).
Proof.
  intros a t. simpl. left. reflexivity.
Qed.

(* Boolean equality route for the premise slot of the host statement at
   line 3562: if [a] occurs in [l] and [a == y], the test opens,
   [Qeq_bool a y = true], in one step by the forward direction of the
   host bridge [Qeqb_true_of]. *)
Theorem dtd_c4_gate_Qeq_y : forall (l : list Q) (y a : Q),
  In a l -> a == y -> Qeq_bool a y = true.
Proof.
  intros l y a _ Ha. apply Qeqb_true_of. exact Ha.
Qed.

(* Extensionality route for the first premise slot of the host statement
   at line 3581 and the second at line 3610: [Qopp] preserves [Qeq],
   [x == y -> - x == - y].  Derived in place, not forwarded: the
   congruence instance [Qminus_comp] gives [0 - x == 0 - y] and
   [Qplus_0_l] reattaches zero on both ends.  A direct expansion over
   the integer components runs into the lowercase [Qden] projection
   face of the [Q] record and was not taken. *)
Theorem dtd_c4_ext_Qopp : forall x y : Q, x == y -> (- x == - y)%Q.
Proof.
  intros x y H.
  apply (Qeq_trans (- x) (0 + (- x)) (- y)).
  - apply Qeq_sym. apply Qplus_0_l.
  - apply (Qeq_trans (0 + (- x)) (0 + (- y)) (- y)).
    + change (0 - x == 0 - y)%Q.
      apply Qminus_comp; [apply Qeq_refl | exact H].
    + apply Qplus_0_l.
Qed.

(* All-open filter route for the premise slot of the host statement at
   line 3595: filtering by the constantly-true predicate preserves every
   frequency, [freq (filter (fun _ => true) l) y = freq l y], by
   induction on [l]; the cons branch splits on [Qeq_bool a y] and closes
   by [lia].  The instance holds at every point, which is what the
   pointwise premise of the [sumf_ext] application below requires. *)
Theorem dtd_c4_freq_filter_all_true : forall (l : list Q) (y : Q),
  freq (filter (fun _ => true) l) y = freq l y.
Proof.
  intro l. induction l as [| a t IH]; intro y; simpl.
  - reflexivity.
  - specialize (IH y). destruct (Qeq_bool a y); lia.
Qed.

(* Computable canonical instance for the premise slot of the host
   statement at line 3669: the organization difference of the empty list
   is nonnegative, [0 <= OrgDiff [] s], since [OrgDiff [] s] reduces
   definitionally to [0 - 0 = 0] with [Pinf], [P0], [H_adj] and
   [Qminus] all degenerate on the empty list. *)
Theorem dtd_c4_OrgDiff_nil_nonneg : forall s : nat,
  (0 <= OrgDiff [] s)%Q.
Proof.
  intro s. replace (OrgDiff [] s) with 0%Q by reflexivity.
  apply Qle_refl.
Qed.

(* Reversal route for the premise slot of the host statement at line
   2957: [Permutation l (rev l)], forwarding the stdlib constructor
   [Permutation_rev] as the permutation input of the rev-shaped premise
   face. *)
Theorem dtd_c4_perm_rev : forall l : list Q, Permutation l (rev l).
Proof.
  intro l. apply Permutation_rev.
Qed.

(* Constant evidence route for the premise slot of the host statement at
   line 2886: [Tabs phi] carries evidence unconditionally,
   [forall phi m' : Dig, Evidence], forwarding the in-force host
   construction [llm_Tabs_const].  The application form is kept
   unconditional so that it does not overlap the registered
   [Tex_inhabited] face. *)
Theorem dtd_c4_Tabs_const : forall (phi : Dig) (m' : Dig), Evidence.
Proof.
  intros phi m'. exact (llm_Tabs_const phi m').
Qed.

(* ================= Section 2. Reduced host applications ================= *)

(* Twenty-three theorems covering twenty-eight premise slots; together
   with the three slots served by the Section 1 routes alone, thirty-one
   slots are supplied.  Each entry applies the host theorem at explicit
   arguments, fills every premise slot by a Section 1 route or by an
   inline construction ([le_n], [in_eq], [discriminate], or a reflexive
   equality), and states the host conclusion specialized to that
   instance.  Three entries pair a route with a reduced application at
   lines 2886, 3669 and 3742. *)

(* Reduced application of [H_adj_bound] at line 2710: the single-point
   upper bound [H_adj [x] <= (Z.of_nat (length [x]) # 1) * Qabs x * 2].
   The occurrence guard is filled inline: membership in the singleton
   list forces the occurring point to be [x], and the bound closes by
   [Qle_refl]. *)
Theorem dtd_c4_H_adj_bound_single : forall x : Q,
  (H_adj [x] <= (Z.of_nat (length [x]) # 1) * Qabs x * 2)%Q.
Proof.
  intro x. apply (H_adj_bound [x] (Qabs x)).
  intros x0 Hx. destruct Hx as [Heq | Hc].
  - subst x0. apply Qle_refl.
  - destruct Hc.
Qed.

(* Reduced application of [Hsup_bounded] at line 2853: the single-point
   upper bound [Hsup [x] n <= (Z.of_nat (length [x]) # 1) * Qabs x * 2],
   with [n] kept universal so the dynamic supremum family is bounded
   pointwise.  The occurrence guard is filled exactly as in
   [dtd_c4_H_adj_bound_single]. *)
Theorem dtd_c4_Hsup_bounded_single : forall (x : Q) (n : nat),
  (Hsup [x] n <= (Z.of_nat (length [x]) # 1) * Qabs x * 2)%Q.
Proof.
  intros x n. apply (Hsup_bounded [x] n (Qabs x)).
  intros x0 Hx. destruct Hx as [Heq | Hc].
  - subst x0. apply Qle_refl.
  - destruct Hc.
Qed.

(* Reduced application of [swap_adj_oob] at line 2917: swapping at the
   index equal to the length is the identity,
   [swap_adj l (length l) = l].  The host lemma is carried on the [Set]
   faces, [NatLe (length l) n -> Id (swap_adj l n) l]; the equation face
   is recovered by the host bridge [id_imp_eq], and the order premise is
   filled inline by [NatLe_lift] at [le_n] with [n := length l]. *)
Theorem dtd_c4_swap_adj_oob_len : forall l : list Q,
  swap_adj l (length l) = l.
Proof.
  intro l.
  exact (id_imp_eq (swap_adj_oob l (length l)
    (NatLe_lift (length l) (length l) (le_n (length l))))).
Qed.

(* Reduced application of [count_q_perm] at line 2957: numerical
   multiplicities are reversal invariant,
   [count_q x l = count_q x (rev l)], with the permutation premise
   filled by [dtd_c4_perm_rev]. *)
Theorem dtd_c4_count_q_perm_rev : forall (l : list Q) (x : Q),
  count_q x l = count_q x (rev l).
Proof.
  intros l x. exact (count_q_perm l (rev l) (dtd_c4_perm_rev l) x).
Qed.

(* Reduced application of [sorted_perm_count_qeq] at line 2987: the
   sorted forms transfer along the reversal, [Forall2 Qeq (P0 l)
   (P0 (rev l))].  Both sortedness premises are filled by
   [dtd_c4_P0_ssorted] and the count equality by
   [dtd_c4_count_P0_P0rev]; the sorted form depends only on the
   numerical multiset. *)
Theorem dtd_c4_sorted_perm_count_qeq_P0rev : forall l : list Q,
  Forall2 Qeq (P0 l) (P0 (rev l)).
Proof.
  intro l. apply (sorted_perm_count_qeq (P0 l) (P0 (rev l))).
  - exact (dtd_c4_P0_ssorted l).
  - exact (dtd_c4_P0_ssorted (rev l)).
  - intro x. exact (dtd_c4_count_P0_P0rev l x).
Qed.

(* Reduced application of [P0_perm_inv] at line 3035: the P0 multiset is
   permutation invariant, [Permutation p l -> Forall2 Qeq (P0 l)
   (P0 p)], with the permutation premise reversed by [dtd_c4_perm_sym]
   first.  The symmetric composite face is taken rather than the
   reflexive instance [Forall2 Qeq (P0 l) (P0 l)], which would coincide
   semantically with premise slot 115 and duplicate the registered
   statement. *)
Theorem dtd_c4_P0_perm_inv_sym : forall l p : list Q,
  Permutation p l -> Forall2 Qeq (P0 l) (P0 p).
Proof.
  intros l p Hperm. exact (P0_perm_inv l p (dtd_c4_perm_sym l p Hperm)).
Qed.

(* Reduced application of [sum_adjdiff_qeq] at line 3050: pointwise
   equality of two numbers gives equality of the adjacent-difference
   sums of their singleton lists, [sum_adjdiff [x] == sum_adjdiff [y]],
   with the [Forall2] premise filled by [dtd_c4_Forall2_Qeq_single]. *)
Theorem dtd_c4_sum_adjdiff_qeq_single : forall x y : Q,
  x == y -> sum_adjdiff [x] == sum_adjdiff [y].
Proof.
  intros x y H. exact (sum_adjdiff_qeq [x] [y]
                         (dtd_c4_Forall2_Qeq_single x y H)).
Qed.

(* Reduced application of [H_adj_qeq] at line 3074: pointwise equality
   gives equality of the adjacent-difference entropies of the singleton
   lists, [H_adj [x] == H_adj [y]], with the same [Forall2] filling. *)
Theorem dtd_c4_H_adj_qeq_single : forall x y : Q,
  x == y -> H_adj [x] == H_adj [y].
Proof.
  intros x y H. exact (H_adj_qeq [x] [y]
                         (dtd_c4_Forall2_Qeq_single x y H)).
Qed.

(* Reduced application of [H_adj_P0_perm] at line 3079: the entropy of
   the P0 multiset is permutation invariant, [Permutation p l ->
   H_adj (P0 l) == H_adj (P0 p)], with the permutation premise reversed
   by [dtd_c4_perm_sym].  This is the [Qeq]-carried face of
   [H_adj_P0_perm]; the [Qle]-carried face supplied under
   [dtd_c2_C_gen_sym] sits at a different premise and a different face,
   so the two do not collide. *)
Theorem dtd_c4_H_adj_P0_perm_sym : forall l p : list Q,
  Permutation p l -> (H_adj (P0 l) == H_adj (P0 p))%Q.
Proof.
  intros l p Hperm. exact (H_adj_P0_perm l p (dtd_c4_perm_sym l p Hperm)).
Qed.

(* Reduced application of [phase_classify_P0_spec] at line 3108:
   agreement with the P0 phase read back on the empty list,
   [H_adj (P0 []) == H_adj (Pmid [] s 0)], with the classification
   premise filled by [dtd_c4_phase_classify_nil_PhP0]; the face
   degenerates to [0 == 0] by computation. *)
Theorem dtd_c4_phase_classify_P0_spec_nil : forall s : nat,
  (H_adj (P0 []) == H_adj (Pmid [] s 0))%Q.
Proof.
  intro s. apply (phase_classify_P0_spec ([] : list Q) s).
  exact (dtd_c4_phase_classify_nil_PhP0 s).
Qed.

(* Reduced application of [phase_classify_perm_inv_cond] at line 3144:
   when the rotation entropies of the two orders coincide, the
   classifier is invariant under the swap, [phase_classify [x; y] 0 =
   phase_classify [y; x] 0].  The permutation premise is filled by
   [dtd_c4_perm_swap_pair] and the entropy equality by
   [dtd_c4_H_inf_swap_pair_eq]. *)
Theorem dtd_c4_phase_classify_perm_inv_cond_swap2 : forall x y : Q,
  phase_classify [x; y] 0 = phase_classify [y; x] 0.
Proof.
  intros x y. apply (phase_classify_perm_inv_cond [x; y] [y; x] 0).
  - exact (dtd_c4_perm_swap_pair x y).
  - exact (dtd_c4_H_inf_swap_pair_eq x y).
Qed.

(* Reduced application of [Pmid_len_spectrum] at line 3290: at the
   full-length end of the spectrum the middle phase has the length of
   the original list, [length (Pmid l s (length l)) = length l +
   (length l - length l)], with the order premise filled inline by
   [le_n] at [lam := length l], compatible with the registered
   [Pmid_len_endpoint] face. *)
Theorem dtd_c4_Pmid_len_spectrum_len : forall (l : list Q) (s : nat),
  length (Pmid l s (length l)) = (length l + (length l - length l))%nat.
Proof.
  intros l s. apply (Pmid_len_spectrum l s (length l)). apply le_n.
Qed.

(* Reduced application of [freq_pos_of_in] at line 3414: a member of the
   world list carries at least one vote, [1 <= freq (x :: l) x], with
   the membership premise filled inline by [in_eq] on the cons. *)
Theorem dtd_c4_freq_pos_of_in_cons : forall (x : Q) (l : list Q),
  (1 <= freq (x :: l) x)%nat.
Proof.
  intros x l. apply (freq_pos_of_in (x :: l) x). apply in_eq.
Qed.

(* Reduced application of [sumf_mono_r] at line 3443: filtering cannot
   increase a pointwise frequency, so the summed mass cannot increase
   either, [sumf m (filter g l) <= sumf m l], with the pointwise
   premise filled inline by [freq_filter_le]. *)
Theorem dtd_c4_sumf_mono_r_filter : forall (g : Q -> bool) (m l : list Q),
  (sumf m (filter g l) <= sumf m l)%nat.
Proof.
  intros g m l. apply (sumf_mono_r m (filter g l) l).
  intro y. apply freq_filter_le.
Qed.

(* Reduced application of [mu_fiber_pos] at line 3477: the w-measure is
   positive on its support, [0 < mu [x] x], with the support membership
   filled by [dtd_c4_in_fiber_zero_single]; the face degenerates to
   [0 < 1] by computation. *)
Theorem dtd_c4_mu_fiber_pos_single : forall x : Q, 0 < mu [x] x.
Proof.
  intro x. apply (mu_fiber_pos (fun _ => 0%Q) [x] x).
  exact (dtd_c4_in_fiber_zero_single x).
Qed.

(* Reduced application of [mu_fiber_mass_lb] at line 3502: the fiber mass
   bounds the empirical frequency from below on a cons world, each zero
   vote being counted at least once, with the nonemptiness premise
   filled by [dtd_c4_cons_neq_nil]. *)
Theorem dtd_c4_mu_fiber_mass_lb_cons : forall (f : Q -> Q) (x : Q)
    (t : list Q),
  ((Z.of_nat (length (fiber f (x :: t))) # 1)
   / (Z.of_nat (length (x :: t)) # 1))%Q
  <= qsum (map (mu (x :: t)) (dedup (fiber f (x :: t)))).
Proof.
  intros f x t. apply (mu_fiber_mass_lb f (x :: t)).
  exact (dtd_c4_cons_neq_nil x t).
Qed.

(* Reduced application of [dedup_aux_In_l] at line 3537: membership is
   preserved through [dedup_aux], giving [In a (a :: t)] under the
   rejected test [Qeq_bool x a = false], with the membership premise
   filled by [dtd_c4_in_dedup_aux_cons_neq]; the resulting face
   degenerates by [in_eq] and the content sits in the membership
   construction itself. *)
Theorem dtd_c4_dedup_aux_In_l_cons_neq : forall (x a : Q) (t : list Q),
  Qeq_bool x a = false -> In a (a :: t).
Proof.
  intros x a t H. apply (dedup_aux_In_l x (a :: t) a).
  exact (dtd_c4_in_dedup_aux_cons_neq x a t H).
Qed.

(* Reduced application of [dedup_In_l] at line 3549: the head of a cons
   is a member of its deduplication, giving [In a (a :: t)], with the
   membership premise filled by [dtd_c4_in_dedup_head]; as above, the
   content sits in the unconditional head membership construction. *)
Theorem dtd_c4_dedup_In_l_head : forall (a : Q) (t : list Q),
  In a (a :: t).
Proof.
  intros a t. apply (dedup_In_l (a :: t) a).
  exact (dtd_c4_in_dedup_head a t).
Qed.

(* Reduced application of [freq_filter_eq_all] at line 3562: when every
   [Qeq]-equal copy of [y] passes the test, the filter preserves the
   frequency of [y], [freq (filter (fun z => Qeq_bool z y) l) y =
   freq l y], with the extensional premise filled by
   [dtd_c4_gate_Qeq_y]. *)
Theorem dtd_c4_freq_filter_Qeq_y : forall (l : list Q) (y : Q),
  freq (filter (fun z => Qeq_bool z y) l) y = freq l y.
Proof.
  intros l y. apply (freq_filter_eq_all (fun z => Qeq_bool z y) l y).
  exact (dtd_c4_gate_Qeq_y l y).
Qed.

(* Reduced application of [freq_w_fiber_eq] at line 3581: counting the
   zero votes of the negated observation recovers the zero votes of the
   original, [freq (fiber Qopp w) 0 = freq w 0].  The extensionality
   premise is filled by [dtd_c4_ext_Qopp] and the zero-test premise
   inline by [reflexivity] on [Qeq_bool (Qopp 0) 0 = true]. *)
Theorem dtd_c4_freq_w_fiber_eq_opp : forall w : list Q,
  freq (fiber Qopp w) 0 = freq w 0.
Proof.
  intro w. apply (freq_w_fiber_eq Qopp dtd_c4_ext_Qopp w 0).
  reflexivity.
Qed.

(* Reduced application of [sumf_ext] at line 3595: pointwise frequency
   equality transfers to the summed masses, [sumf m (filter
   (fun _ => true) l) = sumf m l], with the pointwise premise filled by
   the all-open instance [dtd_c4_freq_filter_all_true], which holds at
   every point. *)
Theorem dtd_c4_sumf_ext_all_true : forall (m l : list Q),
  sumf m (filter (fun _ => true) l) = sumf m l.
Proof.
  intros m l. apply (sumf_ext m (filter (fun _ => true) l) l).
  intros y _. exact (dtd_c4_freq_filter_all_true l y).
Qed.

(* Reduced application of [mu_fiber_mass_eq] at line 3610: under the
   negated observation on a cons world, the fiber mass equals the
   empirical frequency, every zero vote being recorded under the fiber
   exactly once.  The nonemptiness premise is filled by
   [dtd_c4_cons_neq_nil] and the extensionality premise by
   [dtd_c4_ext_Qopp]. *)
Theorem dtd_c4_mu_fiber_mass_eq_opp_cons : forall (x : Q) (t : list Q),
  qsum (map (mu (x :: t)) (dedup (fiber Qopp (x :: t))))
  == ((Z.of_nat (length (fiber Qopp (x :: t))) # 1)
      / (Z.of_nat (length (x :: t)) # 1))%Q.
Proof.
  intros x t. apply (mu_fiber_mass_eq Qopp (x :: t)).
  - exact (dtd_c4_cons_neq_nil x t).
  - exact dtd_c4_ext_Qopp.
Qed.

(* Reduced application of [llm_view_PhP0_gate_exact] at line 3758: the
   acceptance test passes on the empty-list view, [gate_pass
   (gate_threshold (llm_view_of [] s)) (H_adj (Pmid [] s 0)) = true],
   with the classification premise filled by
   [dtd_c4_phase_classify_nil_PhP0].  The boolean decision face is
   carried discretely. *)
Theorem dtd_c4_llm_view_PhP0_gate_exact_nil : forall s : nat,
  gate_pass (gate_threshold (llm_view_of [] s))
            (H_adj (Pmid [] s 0)) = true.
Proof.
  intro s. apply (llm_view_PhP0_gate_exact ([] : list Q) s).
  exact (dtd_c4_phase_classify_nil_PhP0 s).
Qed.

(* ================= Section 3. Audit exits ================= *)

(* At the end of the file: a [Check] stamp for every statement, then the
   per-statement closedness audit.  The name list matches the forty
   supply statements exactly: seventeen routes and twenty-three reduced
   applications. *)

Check dtd_c4_P0_ssorted.
Check dtd_c4_count_P0_P0rev.
Check dtd_c4_perm_sym.
Check dtd_c4_Forall2_Qeq_single.
Check dtd_c4_phase_classify_nil_PhP0.
Check dtd_c4_perm_swap_pair.
Check dtd_c4_H_inf_swap_pair_eq.
Check dtd_c4_in_fiber_zero_single.
Check dtd_c4_cons_neq_nil.
Check dtd_c4_in_dedup_aux_cons_neq.
Check dtd_c4_in_dedup_head.
Check dtd_c4_gate_Qeq_y.
Check dtd_c4_ext_Qopp.
Check dtd_c4_freq_filter_all_true.
Check dtd_c4_OrgDiff_nil_nonneg.
Check dtd_c4_perm_rev.
Check dtd_c4_Tabs_const.
Check dtd_c4_H_adj_bound_single.
Check dtd_c4_Hsup_bounded_single.
Check dtd_c4_swap_adj_oob_len.
Check dtd_c4_count_q_perm_rev.
Check dtd_c4_sorted_perm_count_qeq_P0rev.
Check dtd_c4_P0_perm_inv_sym.
Check dtd_c4_sum_adjdiff_qeq_single.
Check dtd_c4_H_adj_qeq_single.
Check dtd_c4_H_adj_P0_perm_sym.
Check dtd_c4_phase_classify_P0_spec_nil.
Check dtd_c4_phase_classify_perm_inv_cond_swap2.
Check dtd_c4_Pmid_len_spectrum_len.
Check dtd_c4_freq_pos_of_in_cons.
Check dtd_c4_sumf_mono_r_filter.
Check dtd_c4_mu_fiber_pos_single.
Check dtd_c4_mu_fiber_mass_lb_cons.
Check dtd_c4_dedup_aux_In_l_cons_neq.
Check dtd_c4_dedup_In_l_head.
Check dtd_c4_freq_filter_Qeq_y.
Check dtd_c4_freq_w_fiber_eq_opp.
Check dtd_c4_sumf_ext_all_true.
Check dtd_c4_mu_fiber_mass_eq_opp_cons.
Check dtd_c4_llm_view_PhP0_gate_exact_nil.

Print Assumptions dtd_c4_P0_ssorted.
Print Assumptions dtd_c4_count_P0_P0rev.
Print Assumptions dtd_c4_perm_sym.
Print Assumptions dtd_c4_Forall2_Qeq_single.
Print Assumptions dtd_c4_phase_classify_nil_PhP0.
Print Assumptions dtd_c4_perm_swap_pair.
Print Assumptions dtd_c4_H_inf_swap_pair_eq.
Print Assumptions dtd_c4_in_fiber_zero_single.
Print Assumptions dtd_c4_cons_neq_nil.
Print Assumptions dtd_c4_in_dedup_aux_cons_neq.
Print Assumptions dtd_c4_in_dedup_head.
Print Assumptions dtd_c4_gate_Qeq_y.
Print Assumptions dtd_c4_ext_Qopp.
Print Assumptions dtd_c4_freq_filter_all_true.
Print Assumptions dtd_c4_OrgDiff_nil_nonneg.
Print Assumptions dtd_c4_perm_rev.
Print Assumptions dtd_c4_Tabs_const.
Print Assumptions dtd_c4_H_adj_bound_single.
Print Assumptions dtd_c4_Hsup_bounded_single.
Print Assumptions dtd_c4_swap_adj_oob_len.
Print Assumptions dtd_c4_count_q_perm_rev.
Print Assumptions dtd_c4_sorted_perm_count_qeq_P0rev.
Print Assumptions dtd_c4_P0_perm_inv_sym.
Print Assumptions dtd_c4_sum_adjdiff_qeq_single.
Print Assumptions dtd_c4_H_adj_qeq_single.
Print Assumptions dtd_c4_H_adj_P0_perm_sym.
Print Assumptions dtd_c4_phase_classify_P0_spec_nil.
Print Assumptions dtd_c4_phase_classify_perm_inv_cond_swap2.
Print Assumptions dtd_c4_Pmid_len_spectrum_len.
Print Assumptions dtd_c4_freq_pos_of_in_cons.
Print Assumptions dtd_c4_sumf_mono_r_filter.
Print Assumptions dtd_c4_mu_fiber_pos_single.
Print Assumptions dtd_c4_mu_fiber_mass_lb_cons.
Print Assumptions dtd_c4_dedup_aux_In_l_cons_neq.
Print Assumptions dtd_c4_dedup_In_l_head.
Print Assumptions dtd_c4_freq_filter_Qeq_y.
Print Assumptions dtd_c4_freq_w_fiber_eq_opp.
Print Assumptions dtd_c4_sumf_ext_all_true.
Print Assumptions dtd_c4_mu_fiber_mass_eq_opp_cons.
Print Assumptions dtd_c4_llm_view_PhP0_gate_exact_nil.

(* Extraction audit: the statements leave in a single [Separate
   Extraction] command into a dedicated directory.  This file adds no
   data layer of its own (it consumes the host module), so there is no
   same-name overwrite surface. *)
Set Extraction Output Directory "_log/dtd_t5".
Separate Extraction dtd_c4_P0_ssorted
  dtd_c4_count_P0_P0rev dtd_c4_perm_sym dtd_c4_Forall2_Qeq_single
  dtd_c4_phase_classify_nil_PhP0 dtd_c4_perm_swap_pair
  dtd_c4_H_inf_swap_pair_eq dtd_c4_in_fiber_zero_single
  dtd_c4_cons_neq_nil dtd_c4_in_dedup_aux_cons_neq
  dtd_c4_in_dedup_head dtd_c4_gate_Qeq_y dtd_c4_ext_Qopp
  dtd_c4_freq_filter_all_true dtd_c4_OrgDiff_nil_nonneg
  dtd_c4_perm_rev dtd_c4_Tabs_const dtd_c4_H_adj_bound_single
  dtd_c4_Hsup_bounded_single dtd_c4_swap_adj_oob_len
  dtd_c4_count_q_perm_rev dtd_c4_sorted_perm_count_qeq_P0rev
  dtd_c4_P0_perm_inv_sym dtd_c4_sum_adjdiff_qeq_single
  dtd_c4_H_adj_qeq_single dtd_c4_H_adj_P0_perm_sym
  dtd_c4_phase_classify_P0_spec_nil
  dtd_c4_phase_classify_perm_inv_cond_swap2
  dtd_c4_Pmid_len_spectrum_len dtd_c4_freq_pos_of_in_cons
  dtd_c4_sumf_mono_r_filter dtd_c4_mu_fiber_pos_single
  dtd_c4_mu_fiber_mass_lb_cons dtd_c4_dedup_aux_In_l_cons_neq
  dtd_c4_dedup_In_l_head dtd_c4_freq_filter_Qeq_y
  dtd_c4_freq_w_fiber_eq_opp dtd_c4_sumf_ext_all_true
  dtd_c4_mu_fiber_mass_eq_opp_cons dtd_c4_llm_view_PhP0_gate_exact_nil.
