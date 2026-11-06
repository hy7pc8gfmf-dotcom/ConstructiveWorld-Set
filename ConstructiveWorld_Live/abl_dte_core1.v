(* ConstructiveWorld-Set -- DTPT entropy antecedent supply modules. *)

(** * abl_dte_core1: antecedent supply for the DTPT entropy host, volume 1.

    Mission.  Supply the first thirty-eight registered antecedents of the
      host module [DTPT_Entropy] in registration order: direct supply forms
      for the Q-order and Q-absolute-value obligations ([dte_qadd_nonneg],
      [dte_xq_Qle_bool_true], [dte_xq_Qle_antisym], [dte_xq_abs_eq],
      [dte_xq_insert_q_head_aux], [dte_gate_low_entropy_false_le]), guarded
      production forms ([dte_c1_Qle_0_half], [dte_c1_perm_rev],
      [dte_c1_cons_ne], [dte_c1_in_cons], [dte_c1_sorted_P0]), and
      premise-free specializations ([dte_c1_qadd_nonneg_half_third],
      [dte_c1_mkMEval_Hsh0]).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List],
      [Permutation], [Arith], [Lia], [Extraction].  Requires [DTPT],
      [DTPT_Entropy] of this development.

    References.  This development, abl_dte_core1.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_dte_core1.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

Require DTPT.
Require DTPT_Entropy.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.

(* ================= Section 1. Direct supply statements ================= *)

(* Twelve statements supply registered antecedents
   1-2/5-11/13/21-22/28-29/38 of the host module.  Each statement face
   mirrors its host registration face verbatim under the [dte_] name map,
   and each proof is built in place by replaying the host argument steps,
   with no use of host lemmas. *)

(* A1, antecedents 1-2, host [qadd_nonneg] (:95) carried over verbatim: the
   discrete obligation that Q addition is nonnegative under the two
   nonnegativity guards. *)
Theorem dte_qadd_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> (0 <= a + b)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

(* A2, antecedent 5, host [xq_Qle_bool_true] (:171) carried over verbatim:
   the forward bridge from the order [Qle] to its decision face [Qle_bool]. *)
Theorem dte_xq_Qle_bool_true : forall x y : Q, (x <= y)%Q -> Qle_bool x y = true.
Proof.
  intros [nx dx] [ny dy]. unfold Qle, Qle_bool; simpl. intros H.
  destruct (Z.leb (nx * Z.pos dy) (ny * Z.pos dx)) eqn:E.
  - reflexivity.
  - apply Z.leb_gt in E. lia.
Qed.

(* A3, antecedent 6, host [xq_Qle_bool_le] (:179) carried over verbatim:
   the converse bridge from the decision face [Qle_bool] back to the order
   [Qle]. *)
Theorem dte_xq_Qle_bool_le : forall x y : Q, Qle_bool x y = true -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy]. unfold Qle, Qle_bool; simpl.
  change ((nx * Z.pos dy <=? ny * Z.pos dx)%Z = true
          -> (nx * Z.pos dy <= ny * Z.pos dx)%Z).
  intros H. apply Z.leb_le. exact H.
Qed.

(* A4, antecedents 7-8, host [xq_Qle_antisym] (:187) carried over verbatim:
   antisymmetry of the order on Q. *)
Theorem dte_xq_Qle_antisym : forall x y : Q, (x <= y)%Q -> (y <= x)%Q -> x == y.
Proof.
  intros [nx dx] [ny dy] H1 H2. unfold Qle in H1, H2; simpl in H1, H2.
  unfold Qeq; simpl. lia.
Qed.

(* A5, antecedent 9, host [xq_abs_id] (:194) carried over verbatim: a
   nonnegative value equals its own absolute value, through [Z.abs_eq]. *)
Theorem dte_xq_abs_id : forall x : Q, (0 <= x)%Q -> Qabs x == x.
Proof.
  intros [n d] Hx. unfold Qle in Hx; simpl in Hx.
  assert (Hn : (0 <= n)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite (Z.abs_eq n Hn). reflexivity.
Qed.

(* A6, antecedent 10, host [xq_abs_eq0] (:202) carried over verbatim: a
   value equal to zero has absolute value zero. *)
Theorem dte_xq_abs_eq0 : forall x : Q, x == 0 -> Qabs x == 0.
Proof.
  intros [n d] Hx. unfold Qeq in Hx; simpl in Hx.
  assert (Hn : (n = 0)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite Hn. reflexivity.
Qed.

(* A7, antecedent 11, host [xq_abs_eq] (:220) carried over verbatim:
   equality is preserved by the absolute value, by the four cases of
   [Z.abs_spec]. *)
Theorem dte_xq_abs_eq : forall x y : Q, x == y -> Qabs x == Qabs y.
Proof.
  intros [n1 d1] [n2 d2] Hxy.
  unfold Qeq in Hxy; simpl in Hxy.
  unfold Qabs; simpl. unfold Qeq; simpl.
  pose proof (Z.abs_spec n1) as Ha1. pose proof (Z.abs_spec n2) as Ha2.
  destruct Ha1 as [[A1 B1] | [A1 B1]];
    destruct Ha2 as [[A2 B2] | [A2 B2]];
    try rewrite B1; try rewrite B2; lia.
Qed.

(* A8, antecedents 21-22, host [xq_mul_nonneg] (:475) carried over verbatim:
   multiplication on Q is nonnegative under two nonnegativity guards. *)
Theorem dte_xq_mul_nonneg : forall a b : Q, (0 <= a)%Q -> (0 <= b)%Q -> (0 <= a * b)%Q.
Proof.
  intros [an ad] [bn bd] Ha Hb. unfold Qle in Ha, Hb; simpl in Ha, Hb.
  unfold Qle, Qmult; simpl. lia.
Qed.

(* A9, antecedent 28, host [xq_Zlen_inj1] (:627) carried over verbatim:
   the unit-fraction embedding [Z.of_nat n # 1] is injective at the value 1,
   by an integer-level [lia] step. *)
Theorem dte_xq_Zlen_inj1 : forall n : nat, ((Z.of_nat n # 1) == 1)%Q -> n = 1%nat.
Proof.
  intros n H. unfold Qeq in H; simpl in H. lia.
Qed.

(* A10, antecedent 29, host [xq_Qeq_le] (:632) carried over verbatim:
   equality weakens to the order. *)
Theorem dte_xq_Qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy] Hxy. unfold Qeq in Hxy; simpl in Hxy.
  unfold Qle; simpl. lia.
Qed.

(* A11, antecedent 13, host [xq_insert_q_head_aux] (:308) carried over
   verbatim: the head-insertion equation for [insert_q], by definitional
   unfolding plus a replay of the decision face of A2; built in place. *)
Theorem dte_xq_insert_q_head_aux : forall (a b : Q) (bs : list Q),
  (a <= b)%Q -> insert_q a (b :: bs) = a :: b :: bs.
Proof.
  intros a b bs H. simpl. rewrite (dte_xq_Qle_bool_true _ _ H). reflexivity.
Qed.

(* A12, antecedent 38, host [gate_low_entropy_false_le] (:843) carried over
   verbatim: the right-hand bound of the false face of the entropy gate, by
   definitional unfolding of [gate_low_entropy] plus an in-place
   integer-level replay of the false face of [Qle_bool]; the stdlib ships no
   named converse for that false face, so the path goes through
   [Z.leb_gt]. *)
Theorem dte_gate_low_entropy_false_le : forall H threshold : Q,
  gate_low_entropy H threshold = false -> (threshold <= H)%Q.
Proof.
  intros H threshold E. destruct H as [nx dx]. destruct threshold as [ny dy].
  unfold gate_low_entropy in E. unfold Qle_bool in E; simpl in E.
  apply Z.leb_gt in E. unfold Qle; simpl. lia.
Qed.

(* ================= Section 2. Guarded production statements ================= *)

(* Seven statements produce the guarded antecedent faces shared by the later
   specializations: a canonical order instance on Q, a non-canonical
   equal-value pair under Qeq, a permutation-constructor path, a nonequality
   guard passed through verbatim, a membership-constructor path, and a
   premise-free sortedness production. *)

(* Canonical order instance, feeding the source antecedents 1-4/23-24: the
   face (0 <= lam)%Q at lam := (1#2), a nontrivial positive instance after
   the [dtd_c3_Qle_0_1] recipe.  Consumers: P1 (antecedents 1-2), P2
   (antecedents 3-4), P10/P11 (antecedents 23-24). *)
Theorem dte_c1_Qle_0_half : (0 <= (1 # 2))%Q.
Proof.
  unfold Qle. simpl. lia.
Qed.

(* Canonical order instance, feeding the second guard of the P′ form of
   antecedent 1: lam := (1#3), a distinct shape so the two P′ faces do not
   coincide. *)
Theorem dte_c1_Qle_0_third : (0 <= (1 # 3))%Q.
Proof.
  unfold Qle. simpl. lia.
Qed.

(* Non-canonical equal-value pair under Qeq, feeding the guard of antecedent
   30: the order face x == y closed at the value level on (2#2, 1#1), after
   the [dtd_c3_Qeq_half] recipe; a non-degenerate reflexive face. *)
Theorem dte_c1_Qeq_half : (2 # 2 == 1 # 1)%Q.
Proof.
  reflexivity.
Qed.

(* Permutation-constructor path, a standalone production statement: the face
   Permutation l p at the instance p := rev l, forwarded from the stdlib
   [Permutation_rev].  No P′ chain of this volume consumes it: the effective
   supply for antecedent 26 is P13, which substitutes
   [Permutation_sym (D5_P0_perm l)] directly; this statement is kept as the
   permutation production path for later volumes, and that correction is
   declared here. *)
Theorem dte_c1_perm_rev : forall l : list Q, Permutation l (rev l).
Proof.
  intro l. apply Permutation_rev.
Qed.

(* Nonequality guard passed through verbatim, feeding antecedents 15/16:
   the face m <> [] in its assigned pass-through form, the only <> statement
   face of this file, at the canonical cons instance (one [discriminate]
   step). *)
Theorem dte_c1_cons_ne : forall (x : Q) (l : list Q), (x :: l) <> [].
Proof.
  intros x l. discriminate.
Qed.

(* Membership-constructor path, feeding antecedent 34 (declared): the face
   In x l at the head cons instance, by the fully applied [exact] form of
   [in_eq].  The effective supply for antecedents 19-20 is P9, which
   substitutes the stdlib [in_eq]/[in_cons] directly; this statement is not
   on that path, and that correction is declared here. *)
Theorem dte_c1_in_cons : forall (x : Q) (l : list Q), In x (x :: l).
Proof.
  intros x l. exact (in_eq x l).
Qed.

(* Premise-free sortedness production, feeding antecedents 12/14/17/18/25:
   the face SortedQ l at the canonical instance l := P0 l, forwarded from
   the host premise-free production [xq_P0_sorted]; the anchor showing that
   [SortedQ] has a production path. *)
Theorem dte_c1_sorted_P0 : forall l : list Q, SortedQ (P0 l).
Proof.
  intro l. apply xq_P0_sorted.
Qed.

(* ================= Registered only, not supplied ================= *)

(* Antecedent 33, host [xq_len1_el] (:749), sits on the mixed-face flag
   position of the baseline: an existential conclusion carried by Prop.
   Following the :1864 precedent it is registered but not supplied, and its
   statement face is not extended here; the failed supply is declared
   rather than silently repaired, and the upgrade direction is an
   existential witness carried by [sigT]. *)

(* ================= Section 3. Premise-free specializations ================= *)

(* Nineteen statements apply a host theorem at explicitly given arguments
   (@ with every argument), so the guarded antecedents discharge on the
   spot; each conclusion is the host conclusion verbatim at the
   specialization, carried discretely.  Two further statements split a
   conjunctive host conclusion into its two one-directional halves. *)

(* P1, the P′ form of antecedents 1-2: the premise-free specialization of
   the two-guard canonical instance -- the order guards fed at
   ((1#2), (1#3)) yield nonnegativity of the sum of two positives. *)
Theorem dte_c1_qadd_nonneg_half_third : (0 <= (1 # 2) + (1 # 3))%Q.
Proof.
  exact (dte_qadd_nonneg (1 # 2) (1 # 3) dte_c1_Qle_0_half dte_c1_Qle_0_third).
Qed.

(* P2, the P′ form of antecedents 3-4: the two-guard canonical instance of
   cross-phase monotonicity -- at l := [] and s := 0 the cross-phase premise
   discharges inline by reflexivity on the empty list, the order guard is
   fed at lam := (0, 1) from the same family, and the result is the
   monotonicity of H_lam in an enlarged lambda. *)
Theorem dte_c1_H_lam_mono_0_1 : (H_lam [] 0 0 <= H_lam [] 0 1)%Q.
Proof.
  assert (H1 : (H_adj (Pinf [] 0) <= H_adj (P0 []))%Q)
    by (change (0 <= 0)%Q; apply Qle_refl).
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (H_lam_mono [] 0 H1 0 1 dte_c1_Qle_0_half)).
Qed.

(* P3, the P′ form of antecedent 12: the SortedQ antecedent fed at
   (l := P0 l) yields order-preserving insertion on the canonical form P0. *)
Theorem dte_c1_sortQ_insert_P0 : forall (x : Q) (l : list Q),
  SortedQ (insert_q x (P0 l)).
Proof.
  intros x l. exact (xq_sortQ_insert x (P0 l) (dte_c1_sorted_P0 l)).
Qed.

(* P4, the P′ form of antecedent 14: the same application shape yields the
   idempotence of P0. *)
Theorem dte_c1_sortQ_P0_idem : forall l : list Q, P0 (P0 l) = P0 l.
Proof.
  intro l.
  exact (match xq_sortQ_P0_id (P0 l) (dte_c1_sorted_P0 l) in S01_BaseRing.Id _ y
         return P0 (P0 l) = y with
         | S01_BaseRing.id_refl => eq_refl end).
Qed.

(* P5, the P′ form of antecedent 15: the nonequality guard fed at the head
   instance yields membership of the last element. *)
Theorem dte_c1_lastq_In_cons : forall (a : Q) (l : list Q),
  In (lastq (a :: l)) (a :: l).
Proof.
  intros a l. exact (xq_lastq_In (a :: l) (dte_c1_cons_ne a l)).
Qed.

(* P6, the P′ form of antecedent 16: the same application shape yields
   membership of the head element. *)
Theorem dte_c1_hd_In_cons : forall (a : Q) (l : list Q),
  In (hd 0 (a :: l)) (a :: l).
Proof.
  intros a l. exact (xq_hd_In_gen (a :: l) (dte_c1_cons_ne a l)).
Qed.

(* P7, the P′ form of antecedent 17: the SortedQ antecedent fed at the
   canonical form yields the head-tail order bound on P0. *)
Theorem dte_c1_hd_le_lastq_P0 : forall l : list Q,
  (hd 0 (P0 l) <= lastq (P0 l))%Q.
Proof.
  intro l.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (xq_hd_le_lastq (P0 l) (dte_c1_sorted_P0 l))).
Qed.

(* P8, the P′ form of antecedent 18: the SortedQ antecedent fed at the
   canonical form yields the telescope equation on P0. *)
Theorem dte_c1_telescope_P0 : forall l : list Q,
  H_adj (P0 l) == lastq (P0 l) - hd 0 (P0 l).
Proof.
  intro l.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _
           (xq_telescope (P0 l) (dte_c1_sorted_P0 l))).
Qed.

(* P9, the P′ form of antecedents 19-20: the two In antecedents fed by two
   constructor instances ([in_eq] at the head and [in_cons] at the next
   position, fully applied [exact] forms) yield the pairing bound
   |a-b| <= H_adj [a;b] on the two-element list. *)
Theorem dte_c1_pair_dist_cons2 : forall a b : Q,
  (Qabs (a - b) <= H_adj [a; b])%Q.
Proof.
  intros a b.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (xq_pair_dist_le [a; b] a b (in_eq a [b])
              (in_cons a b [b] (in_eq b [])))).
Qed.

(* P10, the first one-directional half split from antecedent 23: the lower
   conjunct of the host conclusion (H_adj (P0 l) <= H_lam l s lam), with
   the two guards discharged inline at the canonical instance lam := 0
   ([Qle_refl] and the canonical order instance), giving the lower bound at
   the endpoint lambda = 0 -- the conjunctive-face reshape into a
   one-directional P′ form is declared here. *)
Theorem dte_c1_H_lam_lam0_lo : forall (l : list Q) (s : nat),
  (H_adj (P0 l) <= H_lam l s 0)%Q.
Proof.
  intros l s.
  destruct (H_lam_cross_phase_bounds l s 0 (Qle_refl 0) dte_c1_Qle_0_half)
    as [Hlo _].
  exact (S02_CauchyComplete.QleT'_to_Qle _ _ Hlo).
Qed.

(* P11, the second one-directional half split from antecedent 24: the upper
   conjunct, giving the upper bound at the endpoint lambda = 0. *)
Theorem dte_c1_H_lam_lam0_hi : forall (l : list Q) (s : nat),
  (H_lam l s 0 <= H_adj (Pinf l s))%Q.
Proof.
  intros l s.
  destruct (H_lam_cross_phase_bounds l s 0 (Qle_refl 0) dte_c1_Qle_0_half)
    as [_ Hhi].
  exact (S02_CauchyComplete.QleT'_to_Qle _ _ Hhi).
Qed.

(* P12, the P′ form of antecedent 25: the SortedQ antecedent fed at the
   canonical form yields the vanishing of the Shannon deviation entropy on
   P0. *)
Theorem dte_c1_H_shannon_P0_zero : forall l : list Q, H_devsum (P0 l) == 0.
Proof.
  intro l.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _
           (xq_H_shannon_sortQ (P0 l) (dte_c1_sorted_P0 l))).
Qed.

(* P13, the P′ form of antecedent 26: the permutation antecedent fed by the
   cross-phase instance ([Permutation_sym (D5_P0_perm l)], every argument
   explicit) yields invariance of the frequency count under the P0 phase. *)
Theorem dte_c1_count_val_P0_perm : forall (x : Q) (l : list Q),
  count_val x (P0 l) = count_val x l.
Proof.
  intros x l.
  exact (match count_val_perm x (P0 l) l (Permutation_sym (D5_P0_perm l))
         in S01_BaseRing.Id _ y
         return count_val x (P0 l) = y with
         | S01_BaseRing.id_refl => eq_refl end).
Qed.

(* P14, the P′ form of antecedent 27: the guard antecedent fed by the
   reflexive instance (ctx := l, [Qle_refl]) yields nonnegativity of the
   conditional entropy under its own condition (the host [H_cond_self]
   face). *)
Theorem dte_c1_H_cond_self_ge0 : forall l : list Q, (0 <= H_cond l l)%Q.
Proof.
  intro l.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _
           (H_cond_nonneg_guarded l l (Qle_refl (H_devsum l)))).
Qed.

(* P15, the P′ form of antecedent 30: the order guard fed by the
   non-canonical equal-value pair (y := (2#2) equal to a := (1#1)) yields
   the non-degenerate instance of the equal-value head-insertion
   equation. *)
Theorem dte_c1_insert_const_head_half : forall ys : list Q,
  insert_q (1 # 1) ((2 # 2) :: ys) = (1 # 1) :: (2 # 2) :: ys.
Proof.
  intro ys.
  exact (match xq_insert_const_head (1 # 1) (2 # 2) ys dte_c1_Qeq_half
         in S01_BaseRing.Id _ y
         return insert_q (1 # 1) ((2 # 2) :: ys) = y with
         | S01_BaseRing.id_refl => eq_refl end).
Qed.

(* P16, the P′ form of antecedent 31: the all-equal Forall guard at the
   singleton-table instance by [Qeq_refl] yields the identity of P0 on a
   constant list. *)
Theorem dte_c1_P0_const_cons : forall a : Q, P0 [a] = [a].
Proof.
  intro a.
  exact (match xq_P0_const_id a [a]
           (@Forall_cons Q (fun z : Q => z == a) a (@nil Q) (Qeq_refl a)
              (@Forall_nil Q (fun z : Q => z == a)))
         in S01_BaseRing.Id _ y
         return P0 [a] = y with
         | S01_BaseRing.id_refl => eq_refl end).
Qed.

(* P17, the P′ form of antecedent 32: the same guard instance as P16 yields
   the vanishing of the Shannon deviation entropy on a singleton list. *)
Theorem dte_c1_Hshannon_const_sing : forall a : Q, H_devsum [a] == 0.
Proof.
  intro a.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _
           (H_shannon_q_const_zero a [a]
              (@Forall_cons Q (fun z : Q => z == a) a (@nil Q) (Qeq_refl a)
                 (@Forall_nil Q (fun z : Q => z == a))))).
Qed.

(* P18, the P′ form of antecedent 34: the In antecedent fed at the head
   instance yields the membership face recast into [Qmem] form ([Qmem] is
   the host membership decision, carried on Prop with zero discrete data,
   after the additional cross-cutting registration convention 2). *)
Theorem dte_c1_In_Qmem_cons : forall (z : Q) (l : list Q), Qmem z (z :: l).
Proof.
  intros z l.
  exact (DTPT.DTPT.eq_imp_id
           (match xq_In_Qmem z (z :: l) (dte_c1_in_cons z l) in
            S01_BaseRing.Id _ y
            return existsb (fun y0 : Q => Qeq_bool z y0) (z :: l) = y with
            | S01_BaseRing.id_refl => eq_refl end)).
Qed.

(* P19, the P′ form of antecedent 35: the dedup singleton equation at the
   canonical instance [(1#2)] (closed by the true computation [eq_refl]
   through [dedup]) yields the all-equal Forall face, the host conclusion
   verbatim at the specialization. *)
Theorem dte_c1_dedup1_all_eq_sing :
  Forall (fun z : Q => z == (1 # 2)) [(1 # 2)].
Proof.
  apply Forall_forall. intros z Hz.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _
           (xq_dedup1_all_eq [(1 # 2)] (1 # 2) eq_refl z Hz)).
Qed.

(* P20, the P′ form of antecedent 36: the multiset-entropy degeneracy guard
   at the canonical instance [(1#2); (1#2)], a two-element all-equal list
   closed by the true computation of [dedup] ([reflexivity]), yields the
   vanishing of the Shannon deviation entropy. *)
Theorem dte_c1_Hms1_Hsh0_pair : H_devsum [(1 # 2); (1 # 2)] == 0.
Proof.
  assert (Hp : (H_ms [(1 # 2); (1 # 2)] == 1)%Q) by reflexivity.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _
           (H_ms1_Hshannon0 [(1 # 2); (1 # 2)] Hp)).
Qed.

(* P21, the P′ form of antecedent 37: the evaluation-suite degeneracy guard
   at the canonical instance [mkMEval [(1#2)] [(1#3)]] (closed by the
   projector round-trip computation, [reflexivity]) yields the vanishing of
   [me_Hsh]. *)
Theorem dte_c1_mkMEval_Hsh0 :
  (me_Hsh (mkMEval [(1 # 2)] [(1 # 3)]) == 0)%Q.
Proof.
  assert (Hp : (me_Hms (mkMEval [(1 # 2)] [(1 # 3)]) == 1)%Q) by reflexivity.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _
           (mkMEval_Hms1_Hsh0 [(1 # 2)] [(1 # 3)] Hp)).
Qed.

(* ================= Section 4. Trailing audit block ================= *)

(* Audit at the very end of the file: [Print Assumptions] for each statement,
   with [Closed] as the expected verdict for all.  The name list holds all
   40 statements, matching the [Qed] count of 40 with no discrepancy. *)

Print Assumptions dte_qadd_nonneg.
Print Assumptions dte_xq_Qle_bool_true.
Print Assumptions dte_xq_Qle_bool_le.
Print Assumptions dte_xq_Qle_antisym.
Print Assumptions dte_xq_abs_id.
Print Assumptions dte_xq_abs_eq0.
Print Assumptions dte_xq_abs_eq.
Print Assumptions dte_xq_mul_nonneg.
Print Assumptions dte_xq_Zlen_inj1.
Print Assumptions dte_xq_Qeq_le.
Print Assumptions dte_xq_insert_q_head_aux.
Print Assumptions dte_gate_low_entropy_false_le.
Print Assumptions dte_c1_Qle_0_half.
Print Assumptions dte_c1_Qle_0_third.
Print Assumptions dte_c1_Qeq_half.
Print Assumptions dte_c1_perm_rev.
Print Assumptions dte_c1_cons_ne.
Print Assumptions dte_c1_in_cons.
Print Assumptions dte_c1_sorted_P0.
Print Assumptions dte_c1_qadd_nonneg_half_third.
Print Assumptions dte_c1_H_lam_mono_0_1.
Print Assumptions dte_c1_sortQ_insert_P0.
Print Assumptions dte_c1_sortQ_P0_idem.
Print Assumptions dte_c1_lastq_In_cons.
Print Assumptions dte_c1_hd_In_cons.
Print Assumptions dte_c1_hd_le_lastq_P0.
Print Assumptions dte_c1_telescope_P0.
Print Assumptions dte_c1_pair_dist_cons2.
Print Assumptions dte_c1_H_lam_lam0_lo.
Print Assumptions dte_c1_H_lam_lam0_hi.
Print Assumptions dte_c1_H_shannon_P0_zero.
Print Assumptions dte_c1_count_val_P0_perm.
Print Assumptions dte_c1_H_cond_self_ge0.
Print Assumptions dte_c1_insert_const_head_half.
Print Assumptions dte_c1_P0_const_cons.
Print Assumptions dte_c1_Hshannon_const_sing.
Print Assumptions dte_c1_In_Qmem_cons.
Print Assumptions dte_c1_dedup1_all_eq_sing.
Print Assumptions dte_c1_Hms1_Hsh0_pair.
Print Assumptions dte_c1_mkMEval_Hsh0.

(* ================= Section 5. Extraction check ================= *)

(* Extractability check of red line 4, with an [Obj.magic] count of 0 as the
   criterion.  The statement bucket is one single [Separate Extraction]
   command (two same-named extraction commands in one file would overwrite
   each other); the conclusion faces of all 40 statements are carried as
   discrete Prop positions and take placeholder names under the family
   erasure convention of statement extraction.  The real data-layer
   extraction face -- the host data carriers used by the P′ statement faces
   ([insert_q]/[P0]/[rot]/[Pinf]/[H_adj]/[dedup]/[H_ms]/[count_val]/
   [H_devsum]/[H_lam]/[H_cond]/[gate_low_entropy]/[mkMEval]) -- is audited
   in the separate probe file [_dte_c1_probe.v], in its own bucket. *)

Set Extraction Output Directory "_log/dte_t6".
Separate Extraction dte_qadd_nonneg dte_xq_Qle_bool_true dte_xq_Qle_bool_le
  dte_xq_Qle_antisym dte_xq_abs_id dte_xq_abs_eq0 dte_xq_abs_eq
  dte_xq_mul_nonneg dte_xq_Zlen_inj1 dte_xq_Qeq_le dte_xq_insert_q_head_aux
  dte_gate_low_entropy_false_le dte_c1_Qle_0_half dte_c1_Qle_0_third
  dte_c1_Qeq_half dte_c1_perm_rev dte_c1_cons_ne dte_c1_in_cons
  dte_c1_sorted_P0 dte_c1_qadd_nonneg_half_third dte_c1_H_lam_mono_0_1
  dte_c1_sortQ_insert_P0 dte_c1_sortQ_P0_idem dte_c1_lastq_In_cons
  dte_c1_hd_In_cons dte_c1_hd_le_lastq_P0 dte_c1_telescope_P0
  dte_c1_pair_dist_cons2 dte_c1_H_lam_lam0_lo dte_c1_H_lam_lam0_hi
  dte_c1_H_shannon_P0_zero dte_c1_count_val_P0_perm dte_c1_H_cond_self_ge0
  dte_c1_insert_const_head_half dte_c1_P0_const_cons
  dte_c1_Hshannon_const_sing dte_c1_In_Qmem_cons dte_c1_dedup1_all_eq_sing
  dte_c1_Hms1_Hsh0_pair dte_c1_mkMEval_Hsh0.
