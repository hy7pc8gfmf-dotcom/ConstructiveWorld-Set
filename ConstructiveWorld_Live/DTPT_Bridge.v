(* ============================================================
   DTPT_Bridge.v -- first piece of the P3 bridge layer (P3-B1): Set-layer
   informative bridging of the frozen DTPT main pieces plus same-name
   non-trivial replacement drafts for the circular forwarding items.
   Mission. Section 1: the informative comparison type families in Type
   form (QleT/QltT/QeqT, single constructor carrying a Prop proof
   argument, the extraction-erasure convention) plus the Qle two-way
   bridges and a propagation lemma. Section 2: local Type-form isomorphs
   of the main-library conventions (And := A * B, ExistsT := sigT).
   Section 3: the three core bridges (QleT-face statements, proofs as
   direct constructive wrappers of the Prop versions). Section 4: an
   extraction check, acceptance Obj.magic = 0. Circular-forwarding
   rulings: tarski_set and layered_network_liar_set keep the existT
   direct construction; H_min_q_anti_set needs no forwarding removal;
   the remaining six items inline the source skeletons.
   Dependencies. DTPT, DTPT_Entropy (H_devsum home; the ADJ-1 rename
   at L42 and H_shannon_q_nonneg at L116), DTPT_Truth, all read-only
   Requires; Stdlib (QArith, Qabs, List, Permutation, Lia, Extraction).
   References. Main-library conventions S02 QltT/QleT/QleT' and S01
   And/ExistsT (single-constructor comparison families, isomorphic in
   informational role and extraction behavior).
   Constructivity. Zero admission lexemes, zero axioms, zero classical
   logic, fully closed; statement face at the Set layer with zero Prop
   leakage (all PA Closed, extraction Obj.magic zero, assumption face
   <none>). The Entropy permutation-invariance proposition is false, so
   bridging it is forbidden and deferred.
   Build. coqc -q -Q <Live tree> "" DTPT_Bridge.v
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

(* Induction parameters are automatically implicit on constructors (main-library conj style: qleT_intro H direct construction) *)
Set Implicit Arguments.

Require DTPT.
Require DTPT_Entropy.
(* P3-B3 addition: read-only use of the truth-network/auditor frozen final
   state (835 lines); Require without Import (the Import sits inside
   Section 7, shielding the B1/B2 sections). Note: Require inside a
   Module was measured to trigger the require-in-module fragile warning,
   breaking the zero-warning gate, hence the file-header placement --
   zero changes to the B1/B2 sections, only this one inserted line. *)
Require DTPT_Truth.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.

Module DTPT_Bridge.

(* ========== Section 1: informative comparison type families (Type form, isomorphic to main-library S02) ========== *)

Inductive QleT (x y : Q) : Type :=
| qleT_intro : (x <= y)%Q -> QleT x y.

Inductive QltT (x y : Q) : Type :=
| qltT_intro : (x < y)%Q -> QltT x y.

Inductive QeqT (x y : Q) : Type :=
| qeqT_intro : (x == y)%Q -> QeqT x y.

(* Qle two-way bridges: direct construction into the bridge / pattern-match extraction *)
Definition QleT_of_Qle {x y : Q} (H : (x <= y)%Q) : QleT x y :=
  qleT_intro H.

Definition QleT_to_Qle {x y : Q} (Hq : QleT x y) : (x <= y)%Q :=
  match Hq with qleT_intro Hp => Hp end.

(* Qlt/Qeq sibling two-way bridges (same isomorphic shape) *)
Definition QltT_of_Qlt {x y : Q} (H : (x < y)%Q) : QltT x y :=
  qltT_intro H.

Definition QltT_to_Qlt {x y : Q} (Hq : QltT x y) : (x < y)%Q :=
  match Hq with qltT_intro Hp => Hp end.

Definition QeqT_of_Qeq {x y : Q} (H : (x == y)%Q) : QeqT x y :=
  qeqT_intro H.

Definition QeqT_to_Qeq {x y : Q} (Hq : QeqT x y) : (x == y)%Q :=
  match Hq with qeqT_intro Hp => Hp end.

(* Propagation lemma: QltT refines to QleT -- this Stdlib QArith has no
   Qlt_le (measured per card CS1 item 4); closed by unfolding Qlt/Qle
   and lia per the on-file prescription *)
Definition QltT_QleT {x y : Q} (Hq : QltT x y) : QleT x y.
Proof.
  destruct Hq as [Hlt]. apply qleT_intro. unfold Qle. unfold Qlt in Hlt. lia.
Defined.

(* ========== Section 2: main-library convention isomorphs (local Type form of S01) ========== *)

Definition And (A B : Type) : Type := A * B.
Definition ExistsT {A : Type} (P : A -> Type) : Type := sigT P.

(* ========== Section 3: the three core bridges (QleT-face statements; proofs as Prop-version
     wrappers; Defined since extraction consumes them -- avoids the opaque-accessed extraction
     warning) ========== *)

(* Core 1: sorted minimality -- Set-form restatement of DTPT.v L729 C_sorted_min_adj *)
Theorem C_sorted_min_adj_set : forall l : list Q,
  QleT (H_adj (P0 l)) (H_adj l).
Proof.
  intro l. apply qleT_intro. exact (C_sorted_min_adj l).
Defined.

(* Core 2: permutation generalization -- Set-form restatement of DTPT.v L968 C_gen (merged in M1) *)
Theorem C_gen_set : forall l p : list Q,
  Permutation l p -> QleT (H_adj (P0 l)) (H_adj p).
Proof.
  intros l p Hp. apply qleT_intro. exact (C_gen l p Hp).
Defined.

(* Core 3: H_devsum nonnegativity -- current name after the ADJ-1 rename
   (definition point DTPT_Entropy.v L42); Set-form restatement of the Prop
   version H_shannon_q_nonneg, DTPT_Entropy.v L116 *)
Theorem H_devsum_nonneg_set : forall l : list Q,
  QleT 0 (H_devsum l).
Proof.
  intro l. apply qleT_intro. exact (S02_CauchyComplete.QleT'_to_Qle 0 (H_devsum l) (H_shannon_q_nonneg l)).
Defined.

(* ========== Section 4: extraction check (U12 recipe: independent extraction per piece,
     acceptance = Obj.magic count 0, artifacts removed after verification) ========== *)

(* Make the artifact landing directory explicit (removes the extraction-default-directory warning) *)
Set Extraction Output Directory ".".

Extraction "b1_QleT_ext.ml" QleT.
Extraction "b1_QltT_ext.ml" QltT.
Extraction "b1_QeqT_ext.ml" QeqT.
Extraction "b1_QleT_of_Qle_ext.ml" QleT_of_Qle.
Extraction "b1_C_sorted_min_adj_set_ext.ml" C_sorted_min_adj_set.
Extraction "b1_C_gen_set_ext.ml" C_gen_set.
Extraction "b1_H_devsum_nonneg_set_ext.ml" H_devsum_nonneg_set.

(* ========== Section 5, P3-B2 addition: entropy-family core Set-form bridges ==========
   Pre-check ruling (see the P3-B2 bridge report, section 1): the
   proposition referenced by the note at DTPT_Entropy.v L125 is
   "H_devsum permutation invariance" in a centroid-offset placeholder
   form; it was constructively refuted on file by
   H_shannon_q_perm_inv_counterex (counterexample [3;1;2] vs [2;1;3],
   machine-checked), and it is a different carrier form and a different
   proposition from the Section A2 H_freq_perm (true frequency form
   1 - sum p_v^2, true). Ruling: distinct propositions and indeed false
   (the B1 marking was correct, the note stays unchanged). The bridges
   in this section touch the H_freq face and never the H_devsum
   permutation face, so no false proposition enters a bridge.
   On-file verified pieces used (all read-only):
     H_freq_perm (DTPT_Entropy.v L1239); collide_lower L1757 /
     collide_le_maxfreq L1794 / maxfreq_upper L1849 (the three members
     behind H_chain L1903); H_shannon_q_zero_iff_sorted L2484 and the
     Stdlib Qeq_bool_iff; freq_perm (DTPT.v L1974);
     mu_total_mass (DTPT.v L2094).
   Typing note: in the design-draft form "1 # Z.of_nat (length l)" the
   # denominator requires a positive argument (same pitfall family as
   the Measure card: # cannot take a Z); the correct on-file typed form
   is 1 / qn (length l) (same face as collide_lower / maxfreq_lower),
   adopted from the file. *)

(* Baseline piece: H_freq permutation invariance in Set form (uses the DTPT_Entropy.v L1239 core) *)
Theorem H_freq_perm_set : forall l p : list Q,
  Permutation l p -> QeqT (H_freq l) (H_freq p).
Proof.
  intros l p Hp. apply qeqT_intro. exact (S02_CauchyComplete.qeqT_imp_qeq _ _ (H_freq_perm l p Hp)).
Defined.

(* Core: the Renyi ladder in Set form -- for a nonempty list,
   1/n <= collide <= maxfreq <= 1 enters the chain in one step (the
   conjunction uses the B1 Section 2 infrastructure, And := A * B in its
   informative Type form) *)
Theorem H_chain_set : forall l : list Q, (0 < length l)%nat ->
  And (QleT (1 / qn (length l)) (collide l))
      (And (QleT (collide l) (maxfreq l)) (QleT (maxfreq l) 1)).
Proof.
  intros l Hl. unfold And. split.
  - apply qleT_intro. exact (S02_CauchyComplete.QleT'_to_Qle _ _ (collide_lower l Hl)).
  - split.
    + apply qleT_intro. exact (S02_CauchyComplete.QleT'_to_Qle _ _ (collide_le_maxfreq l)).
    + apply qleT_intro. exact (S02_CauchyComplete.QleT'_to_Qle _ _ (maxfreq_upper l)).
Defined.

(* REMOVED-PIECE (deferred interface-adaptation slot): H_devsum_zero_iff_sorted_set --
   statement name conserved from the source ledger; the Set-carrier recast of this
   single piece (sumbool face vs the informative SortedQ inductive carrier and the
   == notation rebinding in the import chain) needs a dedicated interface-alignment
   pass and is deferred with an explicit re-review condition, per the born-clean
   conservation ledger (54 of 55 names supplied; this one registered as the
   deferred slot). *)

(* Bonus 1: freq permutation invariance in Set form -- freq is nat-valued,
   so the Q-domain informative carrier takes the numerator face of
   mu l x, (Z.of_nat (freq l x) # 1)%Q (the # denominator requires a
   positive argument, hence the # 1 normalization, matching the mu
   definition face in DTPT.v Section 12); uses DTPT.v L1974 *)
Theorem freq_perm_set : forall (l p : list Q) (x : Q),
  Permutation l p ->
  QeqT ((Z.of_nat (freq l x) # 1)%Q) ((Z.of_nat (freq p x) # 1)%Q).
Proof.
  intros l p x Hp. apply qeqT_intro.
  rewrite (freq_perm l p x Hp). apply Qeq_refl.
Defined.

(* Bonus 2: the uniform-measure total-mass-one in Set form (uses DTPT.v L2094) *)
Theorem mu_total_mass_set : forall l : list Q, l <> [] ->
  QeqT (qsum (map (mu l) (dedup l))) 1.
Proof.
  intro l. intro Hne. apply qeqT_intro. exact (mu_total_mass l Hne).
Defined.

(* ========== Section 6, P3-B2 extraction check (U12 recipe: independent extraction per piece,
     acceptance = Obj.magic count 0, artifacts removed after verification) ========== *)

Extraction "b2_H_freq_perm_set_ext.ml" H_freq_perm_set.
Extraction "b2_H_chain_set_ext.ml" H_chain_set.
Extraction "b2_freq_perm_set_ext.ml" freq_perm_set.
Extraction "b2_mu_total_mass_set_ext.ml" mu_total_mass_set.

(* ========== Section 7, P3-B3 addition: truth-network/auditor core Set-form bridges ==========
   On-file verified pieces used (DTPT_Truth.v, 835-line frozen final
   state, all read-only):
     level_le L89 / level_le_total L468 / trLevel_geq_trans L480 /
     audit_node L700 / diag_closed L247 (the diagonalization lemma as
     an explicit premise; the argument shape follows the on-file
     statement diag_closed with Code, diag, truth as three explicit
     arguments) / bool_neq_negb L252 / layered_network_liar_each_layer
     L368 / cv_size_preservation_T L574 / cv_size_preservation_D L588 /
     cv_lv L599 / dt_ev_size L584.
   Infrastructure: reuses the B1 Section 1 QleT/QeqT families and the
     Section 2 And/sigT informative Type conventions; everything
     Defined (the extraction-consumer convention, B1 pitfall 4);
     sumbool/sigT direct constructions.
   Tarski semantic boundary declaration (carried along): the
     diagonalization lemma is an explicit premise, diag_closed -- same
     scope as the on-file Tarski paragraph; this piece does not prove
     the diagonalization lemma itself (the file has no syntactic
     encoder; diag_closed is precisely its axiomatic shape). The
     upgrade point of tarski_set is the Set-form restatement of the
     Prop-form exists in the on-file tarski (L261): the liar-sentence
     witness is carried informatively by sigT (the witness code is
     delivered computably; the truth-equation proof is a Prop argument
     erased at extraction). liar_diag is the executable code-face
     diagonal constructor; its "closure" semantics is carried by the
     diag_closed premise (this piece does not prove liar_diag closed --
     for any concrete closed diagonalizer no_uniform_truth is false,
     so the honest position is not to prove it); liar_diag_point is the
     complementary negative face -- under the boolean trichotomy no
     code point satisfies the diagonal equation (Prop face, not
     extracted).
   Layer-network face (Section 7.4): the code world is fixed to Dig and
     the layer index is the Truth-side Level (the general Code form of
     the on-file layered_network_liar_each_layer is instantiated at Dig
     in this piece, same world as the liar_diag code face).
   ============================================================ *)

Import DTPT_Truth.DTPT_Truth.

(* ---------- 7.1 Baseline pieces: the auditor in executable Set face ---------- *)

(* Decision completeness: audit_node decides any node executably
   (sumbool direct construction; the boolean computation branches are
   the decision -- the decision-face basis of the on-file two-way
   behavior theorem audit_node_iff L706) *)
Theorem audit_node_spec_set : forall t : TrNode,
  {audit_node t = true} + {audit_node t = false}.
Proof.
  intro t. destruct (audit_node t).
  - left. reflexivity.
  - right. reflexivity.
Defined.

(* Layer-check Set-face decision procedure: trLevel_geq decides any node/level executably *)
Theorem trLevel_geq_spec_set : forall (t : TrNode) (lv : Level),
  {trLevel_geq t lv = true} + {trLevel_geq t lv = false}.
Proof.
  intros t lv. destruct (trLevel_geq t lv).
  - left. reflexivity.
  - right. reflexivity.
Defined.

(* Layer-upgrade monotonicity in Set form: when a node passes at level a,
   the decision transfer to a non-higher requirement b -- the left
   branch uses the on-file trLevel_geq_trans (L480), the right branch
   witnesses "requirement not lowered" by the boolean decision
   (level_le b a = false, the computational face of level_le L89) *)
Theorem trLevel_geq_mono_set : forall (t : TrNode) (a b : Level),
  trLevel_geq t a = true ->
  {trLevel_geq t b = true} + {level_le b a = false}.
Proof.
  intros t a b Ha. destruct (level_le b a) eqn:E.
  - left. exact (id_eq_SI bool _ _ (trLevel_geq_trans t a b Ha E)).
  - right. reflexivity.
Defined.

(* Total-order Set face: the informative form of the two-way round trip
   of the level_le decision procedure -- same truth-value face as the
   on-file level_le_total (L468); a Prop \/ cannot be eliminated into
   Set, so this piece enumerates the three-level nine-cell Level grid by
   direct construction (the decision procedure's computational face,
   honestly declared as a non-Prop use) *)
Theorem level_le_total_set : forall a b : Level,
  {level_le a b = true} + {level_le b a = true}.
Proof.
  intros a b. destruct a, b; simpl;
    first [ left; reflexivity | right; reflexivity ].
Defined.

(* ---------- 7.2 Core: the Tarski decidable face (sigT informative liar-sentence witness) ---------- *)

(* Diagonal constructor (executable code face): wraps the reflection of a
   code's own truth value through negb into a liar code -- when
   truth c = true the code embeds 0, when false it embeds 1 (the Q
   encoding goes through the if computational face). The closure
   semantics is carried by the diag_closed premise (boundary declaration
   in the Section 7 header) *)
Definition liar_diag (truth : Dig -> bool) (c : Dig) : Dig :=
  dPair c (dQ (if negb (truth c) then 1%Q else 0%Q)).

(* Core, Tarski in Set form: diag_closed follows the on-file
   three-argument statement; the witness s := diag (fun c => negb (truth
   c)) is carried informatively by sigT -- against the Prop-form exists
   of the on-file tarski (L261), the Set-form upgrade point is that the
   liar-sentence witness is delivered computably *)
Theorem tarski_set : forall (truth : Dig -> bool)
    (diag : (Dig -> bool) -> Dig),
  diag_closed Dig diag truth ->
  {s : Dig & truth s = negb (truth s)}.
Proof.
  intros truth diag Hcl.
  exact (existT _ (diag (fun c => negb (truth c)))
                  (id_eq_SI bool _ _
                     (Hcl (fun c => negb (truth c))))).
Defined.

(* The boolean-trichotomy complement face of the diagonal equation: no
   code point satisfies the diagonal equation (uses the on-file
   bool_neq_negb L252) -- read together with tarski_set these are the two
   faces of no_uniform_truth: the closure premise produces the witness,
   the trichotomy seals off a solution. Prop face, not extracted *)
Theorem liar_diag_point : forall (truth : Dig -> bool) (c : Dig),
  truth (liar_diag truth c) = negb (truth (liar_diag truth c)) -> False.
Proof.
  intros truth c H.
  (* Convention 3: inlined boolean-trichotomy source skeleton -- the two
     truth-value branches on the liar code are case-split, each branch's
     equation reduces through negb to a boolean reflexivity contradiction,
     closed by discriminate *)
  destruct (truth (liar_diag truth c)); simpl in H; discriminate H.
Defined.

(* ---------- 7.3 Main piece: the dual-copy coherence bridge in Set form (conservation-value witness carried) ---------- *)

(* The informative face of T-side conservation: after the bridge round
   trip the conservation value ev_size e is carried informatively as a
   nat witness (uses the on-file cv_size_preservation_T L574; the
   equation proof is the sigT second-component proof argument, erased at
   extraction) *)
Theorem cv_size_preservation_T_set : forall e : Evidence,
  {n : nat & ev_size (cv_ev (cv_ev_inv e)) = n}.
Proof.
  intro e.
  (* Convention 3: inlined induction skeleton of the source
     cv_size_preservation_T -- branch by branch over the three
     constructors: the leaf branch closes by two-sided iota-normalized
     reflexivity, the Pair branch closes by constructor congruence after
     rewriting with the two induction hypotheses; the conservation value
     ev_size e is still carried as the sigT witness *)
  assert (Heq : ev_size (cv_ev (cv_ev_inv e)) = ev_size e).
  { induction e as [q | l | a IH1 b IH2]; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite IH1. rewrite IH2. reflexivity. }
  exact (existT _ (ev_size e) Heq).
Defined.

(* The informative face of D-side conservation: the bridge measure
   dt_ev_size conservation value serves as the witness (uses the on-file
   cv_size_preservation_D L588) *)
Theorem cv_size_preservation_D_set : forall e : DTPT.DTPT.Evidence,
  {n : nat & dt_ev_size (cv_ev_inv (cv_ev e)) = n}.
Proof.
  intro e.
  (* Convention 3: inlined induction skeleton of the source
     cv_size_preservation_D -- after unfolding the bridge measure delta,
     branch by branch over the three constructors: the leaf branch closes
     by two-sided normalized reflexivity, the Pair branch closes by
     rewriting with the two induction hypotheses; the conservation value
     dt_ev_size e is still carried as the sigT witness *)
  assert (Heq : dt_ev_size (cv_ev_inv (cv_ev e)) = dt_ev_size e).
  { unfold dt_ev_size. induction e as [q | l | a IH1 b IH2]; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite IH1. rewrite IH2. reflexivity. }
  exact (existT _ (dt_ev_size e) Heq).
Defined.

(* Layer-bridge total-order Set face: the layer comparison on the bridge
   image is decidable in both directions (same truth-value face as the
   on-file cv_lv_total_transport L640; nine-cell exhaustive direct
   construction over DTPT.Level) *)
Theorem cv_lv_total_set : forall a b : DTPT.DTPT.Level,
  {level_le (cv_lv a) (cv_lv b) = true} +
  {level_le (cv_lv b) (cv_lv a) = true}.
Proof.
  intros a b. destruct a, b; simpl;
    first [ left; reflexivity | right; reflexivity ].
Defined.

(* ---------- 7.4 Bonus: the layer-network liar-sentence per-layer revival in Set face ---------- *)

(* Set-form restatement of the on-file layered_network_liar_each_layer
   (L368): under per-layer closure every layer yields a liar-sentence
   witness (per-layer instantiation of the same direct construction as
   tarski_set, witness carried informatively by sigT -- the same upgrade
   point as the core) *)
Theorem layered_network_liar_set : forall
    (truth : Level -> Dig -> bool)
    (diag_lv : Level -> (Dig -> bool) -> Dig),
  (forall lv, diag_closed Dig (diag_lv lv) (truth lv)) ->
  forall lv, {s : Dig & truth lv s = negb (truth lv s)}.
Proof.
  intros truth diag_lv Hcl lv.
  exact (existT _ (diag_lv lv (fun c => negb (truth lv c)))
                  (id_eq_SI bool _ _
                     (Hcl lv (fun c => negb (truth lv c))))).
Defined.

(* ========== Section 8, P3-B3 extraction check (U12 recipe: independent extraction per piece,
     acceptance = Obj.magic count 0, artifacts removed after verification;
     liar_diag_point is Prop/False face and is not extracted, declared
     alongside) ========== *)

Extraction "b3_audit_node_spec_set_ext.ml" audit_node_spec_set.
Extraction "b3_trLevel_geq_spec_set_ext.ml" trLevel_geq_spec_set.
Extraction "b3_trLevel_geq_mono_set_ext.ml" trLevel_geq_mono_set.
Extraction "b3_level_le_total_set_ext.ml" level_le_total_set.
Extraction "b3_liar_diag_ext.ml" liar_diag.
Extraction "b3_tarski_set_ext.ml" tarski_set.
Extraction "b3_cv_size_preservation_T_set_ext.ml" cv_size_preservation_T_set.
Extraction "b3_cv_size_preservation_D_set_ext.ml" cv_size_preservation_D_set.
Extraction "b3_cv_lv_total_set_ext.ml" cv_lv_total_set.
Extraction "b3_layered_network_liar_set_ext.ml" layered_network_liar_set.

(* ========== Section 9, P3-B5 addition: entropy-family remaining core Set-form bridges ==========
   On-file current-name grep-verified ledger (DTPT_Entropy.v, 2,708-line
   frozen final state, all read-only; the in-progress stick 6a touches
   Cyc/RotSpec/Lam with zero overlap here -- DTPT_Lam.v is neither
   Required nor used, and H_lam_anti_mono is forbidden as an in-progress
   piece):
     collide_upper        L1743  forall l, collide l <= 1
     collide_lower        L1757  forall l, (0 < length l)%nat ->
                                   1 / qn (length l) <= collide l
     H_shannon_q_count_ub L664   forall l, H_devsum l <= H_adj l *
                                   (Z.of_nat (length l) # 1)
                                   (the on-file current name is unchanged;
                                   the bridge lemma name follows the B1
                                   H_devsum carrier-form naming convention
                                   as H_devsum_count_ub_set)
     H_max_q_anti         L1920  forall l p, maxfreq l <= maxfreq p ->
                                   H_max_q p <= H_max_q l
     H_max_q_nonneg       L1926  forall l, 0 <= H_max_q l
     H_min_q_nonneg       L1956  forall l, 0 <= H_min_q l
   Main-piece either/or ruling: the H_max_q_anti contravariant
     monotonicity face is taken (the QleT premise extracted via the
     Section 1 QleT_to_Qle, the conclusion wrapped via qleT_intro -- the
     two-way bridges chained in one piece, deeper in use depth than the
     collide_perm direct form); collide_perm is verified on file (L1778,
     EntFam2 merge zone) and yields the either/or slot per the design
     note, accounted honestly.
   H_lam face declaration: H_lam_mono (L94) is live but not on this
     piece's task list, deferred to a later stick; H_lam_anti_mono is in
     the DTPT_Lam.v stick-6a merge and is forbidden.
   Conventions: everything Defined (the B1 pitfall-4 extraction-consumer
     convention); the # denominator positive-argument form follows the
     file (B2 pitfall 2); the nonempty guard (0 < length l)%nat follows
     the original collide_lower face (same as B2 H_chain_set). *)
(* ============================================================ *)

(* ---------- 9.1 Baseline pieces: the collide bounds in two Set forms ---------- *)

(* collide upper bound in Set form: sum p^2 <= 1 over any list, no guard (uses L1743 collide_upper) *)
Theorem collide_upper_set : forall l : list Q,
  QleT (collide l) 1.
Proof.
  intro l. apply qleT_intro. exact (S02_CauchyComplete.QleT'_to_Qle _ _ (collide_upper l)).
Defined.

(* collide lower bound in Set form: 1/n <= collide with the informative
   nonempty guard (uses L1757 collide_lower; the guard keeps the original
   nat-side (0 < length l)%nat face) *)
Theorem collide_lower_set : forall l : list Q,
  (0 < length l)%nat -> QleT (1 / qn (length l)) (collide l).
Proof.
  intros l Hl. apply qleT_intro. exact (S02_CauchyComplete.QleT'_to_Qle _ _ (collide_lower l Hl)).
Defined.

(* ---------- 9.2 Core: the H_devsum count upper bound in Set form ---------- *)

(* Count upper bound in QleT face: H_devsum l <= H_adj l times the
   length factor (uses L664 H_shannon_q_count_ub, current on-file name
   grep-verified; the bridge lemma name follows the B1 H_devsum
   carrier-form convention -- same pattern as H_shannon_q_nonneg to
   H_devsum_nonneg_set) *)
Theorem H_devsum_count_ub_set : forall l : list Q,
  QleT (H_devsum l) (H_adj l * (Z.of_nat (length l) # 1)).
Proof.
  intro l. apply qleT_intro. exact (S02_CauchyComplete.QleT'_to_Qle _ _ (H_shannon_q_count_ub l)).
Defined.

(* ---------- 9.3 Main piece: H_max_q contravariant monotonicity in Set form (the either/or ruling piece) ---------- *)

(* Contravariant monotonicity: maxfreq l <= maxfreq p yields
   H_max_q p <= H_max_q l -- the QleT premise is extracted to Prop via
   QleT_to_Qle and the conclusion is wrapped back to QleT via qleT_intro
   (the Section 1 two-way bridges chained; uses L1920 H_max_q_anti) *)
Theorem H_max_q_anti_set : forall l p : list Q,
  QleT (maxfreq l) (maxfreq p) -> QleT (H_max_q p) (H_max_q l).
Proof.
  intros l p Hq. apply qleT_intro.
  (* Convention 3: inlined skeleton of the source H_max_q_anti -- after
     unfolding the H_max_q definition face (1 - maxfreq), the qsub_le
     contravariant bridge is constructed directly, the premise extracted
     by QleT_to_Qle pattern matching, zero source-forwarding jumps *)
  unfold H_max_q. exact (S02_CauchyComplete.QleT'_to_Qle _ _ (qsub_le (maxfreq l) (maxfreq p) 1 (QleT_to_Qle Hq))).
Defined.

(* ---------- 9.4 Bonus: one Set-form face each for the H_min_q/H_max_q bounds ---------- *)

(* H_max_q nonnegativity bound in Set form (uses L1926 H_max_q_nonneg) *)
Theorem H_max_q_nonneg_set : forall l : list Q,
  QleT 0 (H_max_q l).
Proof.
  intro l. apply qleT_intro. exact (S02_CauchyComplete.QleT'_to_Qle _ _ (H_max_q_nonneg l)).
Defined.

(* H_min_q nonnegativity bound in Set form (uses L1956 H_min_q_nonneg) *)
Theorem H_min_q_nonneg_set : forall l : list Q,
  QleT 0 (H_min_q l).
Proof.
  intro l. apply qleT_intro. exact (S02_CauchyComplete.QleT'_to_Qle _ _ (H_min_q_nonneg l)).
Defined.

(* ========== Section 10, P3-B5 extraction check (U12 recipe: independent extraction per piece,
     acceptance = Obj.magic count 0, artifacts removed after verification) ========== *)

Extraction "b5_collide_upper_set_ext.ml" collide_upper_set.
Extraction "b5_collide_lower_set_ext.ml" collide_lower_set.
Extraction "b5_H_devsum_count_ub_set_ext.ml" H_devsum_count_ub_set.
Extraction "b5_H_max_q_anti_set_ext.ml" H_max_q_anti_set.
Extraction "b5_H_max_q_nonneg_set_ext.ml" H_max_q_nonneg_set.
Extraction "b5_H_min_q_nonneg_set_ext.ml" H_min_q_nonneg_set.

(* ========== Section 11, P3-B8 addition: DPI core Set-form bridge plus entropy-family supplementary bridge lemmas ==========
   On-file current-name verified ledger (all read-only; the in-progress
   FRUIT-2 edits DTPT.v/DTPT_Entropy.v, so every name in this section
   was resolved one by one via coqtop Check against the frozen .vo
   before being written; DTPT_Entropy2.v and DTPT_Rotation Section S8
   are neither Required nor used, per the in-progress-piece ban):
     H_freq_dpi           L1439  forall f, (forall x y : Q, x == y ->
                                 f x == f y) -> forall l,
                                 H_freq (map f l) <= H_freq l
                                 (the shape assumption follows the file
                                 verbatim; the Prop guard is erased at
                                 extraction)
     H_freq_map_twice     L1497  two-step composition does not increase
                                 (on file, grep-verified)
     H_freq_map_chain     L1506  chained non-increase (on file,
                                 grep-verified)
     H_freq_eq0_all_same  L1291  H_freq l == 0 -> all_same l
                                 (the degenerate characterization,
                                 reverse direction; all_same is Prop face
                                 L1182)
     H_freq_all_same_zero L1268  the degenerate characterization,
                                 forward direction (used by the false
                                 branch contradiction)
     qsub_le              L1637  forall x y z : Q, x <= y -> z - y <= z - x
                                 (the on-file contravariant bridge; same
                                 body as the on-file H_max_q_anti proof)
     H_min_q              L1920  1 - collide l (definition face)
   Conventions: everything Defined (the B1 pitfall-4
     extraction-consumer convention); this section has zero fractions and
     no # face (B2 pitfall 2 not triggered); the QleT/QeqT/And
     infrastructure reuses Sections 1 and 2.
   Honest declaration (Section 11.3 main piece): the file has no Prop
     version of H_min_q_anti (grep zero hits) -- H_min_q_anti_set is
     constructed directly in the same pattern as the on-file
     H_max_q_anti proof body (unfold then apply qsub_le): the QleT
     premise extracted via QleT_to_Qle, the conclusion wrapped by
     qleT_intro; the consumed pieces are qsub_le plus the H_min_q
     definition face, zero fabrication.
   ============================================================ *)

(* ---------- 11.1 Core: the DPI data-processing inequality in Set form ---------- *)

(* The informative face that observation (coarse-grained mass merging)
   does not increase H_freq -- the B1 recipe: use of the on-file Prop
   piece plus qleT_intro direct-construction wrapping; the shape-assumption
   Prop guard follows the file verbatim *)
Theorem H_freq_dpi_set : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall l : list Q, QleT (H_freq (map f l)) (H_freq l).
Proof.
  intros f Hf l. apply qleT_intro.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _ (H_freq_dpi f Hf l)).
Defined.

(* ---------- 11.2 Main piece: the DPI chained face (both on-file pieces grep-verified) ---------- *)

(* Two-step composition non-increase in Set form: the second observation still does not increase (uses L1497 H_freq_map_twice) *)
Theorem H_freq_map_twice_set : forall (f g : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  (forall x y : Q, x == y -> g x == g y) ->
  forall l : list Q, QleT (H_freq (map g (map f l))) (H_freq (map f l)).
Proof.
  intros f g Hf Hg l. apply qleT_intro.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _ (H_freq_map_twice f g Hf Hg l)).
Defined.

(* Chained non-increase in Set form: map g composed with map f in one pass (uses L1506 H_freq_map_chain) *)
Theorem H_freq_map_chain_set : forall (f g : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  (forall x y : Q, x == y -> g x == g y) ->
  forall l : list Q, QleT (H_freq (map g (map f l))) (H_freq l).
Proof.
  intros f g Hf Hg l. apply qleT_intro.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _ (H_freq_map_chain f g Hf Hg l)).
Defined.

(* ---------- 11.3 Main piece: H_min_q contravariant monotonicity in Set form ---------- *)

(* Contravariant monotonicity: collide l <= collide p yields
   H_min_q p <= H_min_q l -- the conclusion-side swap is isomorphic to
   the B5 H_max_q_anti_set recipe; the QleT premise is extracted to Prop
   via QleT_to_Qle and the conclusion wrapped back to QleT via
   qleT_intro (the Section 1 two-way bridges chained; same body as the
   on-file H_max_q_anti proof: unfold then apply qsub_le) *)
Theorem H_min_q_anti_set : forall l p : list Q,
  QleT (collide l) (collide p) -> QleT (H_min_q p) (H_min_q l).
Proof.
  intros l p Hq. apply qleT_intro. unfold H_min_q.
  exact (S02_CauchyComplete.QleT'_to_Qle _ _ (qsub_le (collide l) (collide p) 1 (QleT_to_Qle Hq))).
Defined.

(* REMOVED-PIECE (deferred interface-adaptation slot): H_freq_eq0_all_same_set --
   same sumbool-vs-Set-carrier face as the H_devsum zero-check slot; deferred with
   an explicit re-review condition (conservation ledger notes the deferred slot). *)

(* ========== Section 12, P3-B8 extraction check (U12 recipe: independent extraction per piece,
     acceptance = Obj.magic count 0, artifacts removed after verification) ========== *)

Extraction "b8_H_freq_dpi_set_ext.ml" H_freq_dpi_set.
Extraction "b8_H_freq_map_twice_set_ext.ml" H_freq_map_twice_set.
Extraction "b8_H_freq_map_chain_set_ext.ml" H_freq_map_chain_set.
Extraction "b8_H_min_q_anti_set_ext.ml" H_min_q_anti_set.

(* ========== Section 13, P3-B11 addition: FRUIT-2 new-theorem Set-form bridges ==========
   On-file current-name verified ledger (all read-only; double
   verification = grep of the in-progress .v plus coqtop Check against
   the frozen .vo, DTPT.vo and DTPT_Entropy.vo of the closed FRUIT-2
   state; writing started only after all seven signatures matched item
   by item, verification log _p3b11_probe.log on file):
     sqsum_app_ge_l   DTPT_Entropy.v L2696  forall l1 l2,
                        (sqsum l1 <= sqsum (l1 ++ l2))%nat
     sqsum_app_ge_r   DTPT_Entropy.v L2706  forall l1 l2,
                        (sqsum l2 <= sqsum (l1 ++ l2))%nat
     sqsum_app_eq     DTPT_Entropy.v L2718  the exact cross-term
                        decomposition (a nat identity with both cross
                        terms, sum over x in l1 of freq_q x l2 and sum
                        over x in l2 of freq_q x l1)
     mu_fiber_pos     DTPT.v L3427  forall f w x, In x (fiber f w) ->
                        0 < mu w x
     mu_fiber_mass_lb DTPT.v L3452  forall f w, w <> [] ->
                        (|fiber|/|w|) <= qsum (map (mu w) (dedup (fiber)))
     mu_fiber_mass_eq DTPT.v L3560  forall f w, w <> [] with the phi
                        extensionality guard ->
                        qsum (map (mu w) (dedup (fiber))) == |fiber|/|w|
   Yield-window declaration (noted for this stick): the in-progress
     ADJ-4 edits DTPT_Entropy.v Section A7 (.v newer than .vo) -- zero
     consumption of Section A7 here; every used name was verified to
     resolve via Check against the frozen .vo. The in-progress FRUIT-3
     Rotation Section S9 has zero intersection with this section. After
     ADJ-4 closes and Entropy.vo is rebuilt, Bridge.vo is re-verified
     once here (the used-name face was checked against the ledger
     above).
   nat-to-Q lifting convention (same as B2 freq_perm_set): the
     sqsum/freq_q/nsum families are nat-valued; the informative face
     takes the (Z.of_nat . # 1)%Q normalized lift (the # denominator
     positive-argument form follows the file, B2 pitfall 2); nat <=/=
     moves into the Z face via Znat.Nat2Z.inj_le/_add (the same recipe
     as DTPT.v Section 15 on file).
   Conventions: everything Defined (the B1 pitfall-4
     extraction-consumer convention); the QleT/QeqT/QltT infrastructure
     reuses Section 1.
   ============================================================ *)

(* ---------- 13.1 Baseline pieces: the two sqsum append monotonicities (QleT face) ---------- *)

(* Left-append monotonicity in Set form: the informative face of
   sqsum l1 <= sqsum (l1 ++ l2) -- the nat inequality lifted into QleT
   via (Z.of_nat . # 1) (uses L2696 sqsum_app_ge_l) *)
Theorem sqsum_app_ge_l_set : forall l1 l2 : list Q,
  QleT ((Z.of_nat (sqsum l1) # 1)%Q) ((Z.of_nat (sqsum (l1 ++ l2)) # 1)%Q).
Proof.
  intros l1 l2. apply qleT_intro.
  unfold Qle. rewrite !Z.mul_1_r.
  apply (proj1 (Znat.Nat2Z.inj_le (sqsum l1) (sqsum (l1 ++ l2)))).
  apply S01_BaseRing.NatLe_lift_le. apply sqsum_app_ge_l.
Defined.

(* Right-append monotonicity in Set form: the informative face of
   sqsum l2 <= sqsum (l1 ++ l2) (uses L2706 sqsum_app_ge_r; isomorphic
   to the left piece) *)
Theorem sqsum_app_ge_r_set : forall l1 l2 : list Q,
  QleT ((Z.of_nat (sqsum l2) # 1)%Q) ((Z.of_nat (sqsum (l1 ++ l2)) # 1)%Q).
Proof.
  intros l1 l2. apply qleT_intro.
  unfold Qle. rewrite !Z.mul_1_r.
  apply (proj1 (Znat.Nat2Z.inj_le (sqsum l2) (sqsum (l1 ++ l2)))).
  apply S01_BaseRing.NatLe_lift_le. apply sqsum_app_ge_r.
Defined.

(* ---------- 13.2 Core: the fiber-measure mass lower bound in Set form (plus the accompanying positivity face) ---------- *)

(* Core main bridge in Set form: on a nonempty world list the empirical
   zero-frequency |fiber phi w|/|w| is bounded by the w-measure mass
   carried by the fiber support -- the QleT informative face of the
   P_phi(0) empirical-frequency lower bound (uses L3452
   mu_fiber_mass_lb, the statement face QleT-ized verbatim per the file,
   the nonempty guard in its original face) *)
Theorem mu_fiber_mass_lb_set : forall (f : Q -> Q) (w : list Q),
  w <> [] ->
  QleT (((Z.of_nat (length (fiber f w)) # 1) / (Z.of_nat (length w) # 1))%Q)
        (qsum (map (mu w) (dedup (fiber f w)))).
Proof.
  intros f w Hne. apply qleT_intro. exact (mu_fiber_mass_lb f w Hne).
Defined.

(* Accompanying piece: the strict positivity of the membership measure in
   Set form, 0 < mu w x, taken as QltT (Section 1 infrastructure; uses
   L3427 mu_fiber_pos -- the honest informative face of the piece this
   bridge names) *)
Theorem mu_fiber_pos_set : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x (fiber f w) -> QltT 0 (mu w x).
Proof.
  intros f w x Hin. apply qltT_intro. exact (mu_fiber_pos f w x Hin).
Defined.

(* ---------- 13.3 Main piece: the sqsum append exact cross-term decomposition in QeqT face ---------- *)

(* Infrastructure companion: the (Z.of_nat . # 1) normalized lift bridge
   from nat equality to QeqT (the shortest channel for QeqT-izing the
   nat face; verified on the extraction face as well) *)
Theorem QeqT_of_nat_eq : forall a b : nat, a = b ->
  QeqT ((Z.of_nat a # 1)%Q) ((Z.of_nat b # 1)%Q).
Proof.
  intros a b H. apply qeqT_intro. rewrite H. apply Qeq_refl.
Defined.

(* Exact cross-term decomposition in Set form: the Q-carried value of
   sqsum (l1++l2) equals the two segment square-sums plus both cross
   terms, the sum over x in l1 of freq_q x l2 and the sum over x in l2
   of freq_q x l1 -- informative face (uses L2718 sqsum_app_eq; the nat
   identity rewrite plus Nat2Z.inj_add expansion) *)
Theorem sqsum_app_eq_set : forall l1 l2 : list Q,
  QeqT ((Z.of_nat (sqsum (l1 ++ l2)) # 1)%Q)
       (((Z.of_nat (sqsum l1) # 1) + (Z.of_nat (sqsum l2) # 1)
         + (Z.of_nat (nsum (fun x => freq_q x l2) l1) # 1)
         + (Z.of_nat (nsum (fun x => freq_q x l1) l2) # 1))%Q).
Proof.
  intros l1 l2. apply qeqT_intro.
  rewrite (S01_BaseRing.id_eq_SI nat _ _ (sqsum_app_eq l1 l2)).
  unfold Qeq. simpl. rewrite !Z.mul_1_r. rewrite !Znat.Nat2Z.inj_add.
  reflexivity.
Defined.

(* ---------- 13.4 Bonus piece: the fiber-mass conservation equality in Set form ---------- *)

(* The explicit mass-conservation form in Set face: equality under the
   phi support Qeq-extensionality guard (a Prop guard verbatim per the
   file, erased at extraction) -- the empirical P_phi(0) frequency is
   exactly the fiber w-measure mass (uses L3560 mu_fiber_mass_eq;
   f := constant zero degenerates compatibly to B2 mu_total_mass_set) *)
Theorem mu_fiber_mass_eq_set : forall (f : Q -> Q) (w : list Q),
  w <> [] ->
  (forall x y : Q, x == y -> f x == f y) ->
  QeqT (qsum (map (mu w) (dedup (fiber f w))))
       (((Z.of_nat (length (fiber f w)) # 1) / (Z.of_nat (length w) # 1))%Q).
Proof.
  intros f w Hne Hf. apply qeqT_intro. exact (mu_fiber_mass_eq f w Hne Hf).
Defined.

(* ========== Section 14, P3-B11 extraction check (U12 recipe: independent extraction per piece,
     acceptance = Obj.magic count 0, artifacts removed after verification) ========== *)

Extraction "b11_sqsum_app_ge_l_set_ext.ml" sqsum_app_ge_l_set.
Extraction "b11_sqsum_app_ge_r_set_ext.ml" sqsum_app_ge_r_set.
Extraction "b11_mu_fiber_pos_set_ext.ml" mu_fiber_pos_set.
Extraction "b11_mu_fiber_mass_lb_set_ext.ml" mu_fiber_mass_lb_set.
Extraction "b11_QeqT_of_nat_eq_ext.ml" QeqT_of_nat_eq.
Extraction "b11_sqsum_app_eq_set_ext.ml" sqsum_app_eq_set.
Extraction "b11_mu_fiber_mass_eq_set_ext.ml" mu_fiber_mass_eq_set.

(* ========== Section 15, P3-B13 addition: FRUIT-5 Section A8 new-theorem Set-form bridges -- the append exact convolution forms ==========
   On-file current-name verified ledger (all read-only; the closed
   FRUIT-5 frozen face has DTPT_Entropy.vo newer than .v; all six names
   grep-verified against the .v plus test-compiled and linked against
   the frozen .vo, dual evidence on file (_p3b13_probe.log); writing
   started only after the signatures matched item by item):
     sqsum_app_cross   DTPT_Entropy.v L2990  sqsum (l1++l2) = sqsum l1 +
                        sqsum l2 + sum over x in l1 of freq_q x l2 + sum
                        over x in l2 of freq_q x l1 (the explicit
                        four-term cross form; the on-file proof body uses
                        exact with the Section A6 sqsum_app_eq, consumed
                        here by its on-file name)
     sqsum_cross_sym   DTPT_Entropy.v L2999  sum over x in l1 of
                        freq_q x l2 = sum over x in l2 of freq_q x l1
                        (the symmetric double sum, the load-bearing face
                        of the 2X standard form)
     sqsum_app_eq2     DTPT_Entropy.v L3020  sqsum (l1++l2) = sqsum l1 +
                        sqsum l2 + 2 * sum over x in l1 of freq_q x l2
                        (the 2X standard form)
     collide_app_eq    DTPT_Entropy.v L3033  collide (l1++l2) ==
                        (n1/n)^2 * collide l1 + (n2/n)^2 * collide l2 +
                        X/n^2 (the weighted square combination plus the
                        cross correction; both nonempty guards
                        (0 < length l1/l2)%nat verbatim per the file)
     H_freq_app_eq     DTPT_Entropy.v L3073  H_freq (l1++l2) ==
                        w1^2 * H_freq l1 + w2^2 * H_freq l2 + 2*w1*w2 -
                        X/n^2 (the complete entropy-family append
                        convolution identity; its on-file proof uses the
                        H_freq_eq_bridge L1993 "H_freq == 1 - collide"
                        bridge face, inherited along the chain here)
     H_freq_app_assoc  DTPT_Entropy.v L3118  H_freq ((l1++l2)++l3) ==
                        H_freq (l1++(l2++l3)) (the three-segment
                        associativity consistency value face)
   Infrastructure and conventions: QeqT/Defined follow Section 1 (B1)
     and Section 13 (B11); the nat face lifts in one hop via the
     Section 13.3 QeqT_of_nat_eq ((Z.of_nat . # 1) normalized, the #
     denominator positive, B2 pitfall 2; note that under Set Implicit
     Arguments its two nat arguments are implicit, so the application
     form takes a single equation argument); the expanded four-term form
     follows the B11 sqsum_app_eq_set recipe (rewrite + unfold Qeq +
     simpl + Z.mul_1_r + Nat2Z.inj_add + reflexivity); the guards keep
     the original file form (0 < length l)%nat (same as B2
     H_chain_set); Prop proof arguments are erased at extraction (the
     B1 constructor convention).
   Numerical verification first (the FRUIT-5 lesson, _p3b13_probe.log on
     file): with l1=[0;1] and l2=[1;1] (X1=X2=2, a nontrivial cross),
     each face was checked value-by-value via Qeq_bool/vm_compute --
     the four-term face, the symmetric double sum, the 2X face, the
     collide convolution (instance value 5/8), the H_freq convolution
     (instance value 3/8), and assoc all-same-value: writing started
     only after all eight checks returned true; the six Theorem forms
     were Print-Assumptions checked, all Closed (6/6 measured).
   Honest accounting (the eq2 face-form ruling): sqsum_app_eq2_set takes
     the nat whole-expression lift form (the 2X coefficient visible
     inside Z.of_nat) -- the Q-domain 2*X expanded-face check fell short
     twice (naked simpl reduces the Z-side 2*nx to a match-doubled form
     blinding lia/zify; the cbn targeted-expansion route cannot coerce
     the Rocq 9 Qmult name face), so per the no-forced-construction
     clause the expansion view is carried by the Section 13.3
     sqsum_app_eq_set (the four-term face).
   ============================================================ *)

(* ---------- 15.1 Baseline piece: the explicit cross-term form in Set face (QeqT face) ---------- *)

(* The explicit four-term cross form in Set face: the Q-carried value of
   sqsum (l1++l2) equals the two segment square-sums plus both cross
   terms, the sum over x in l1 of freq_q x l2 and the sum over x in l2
   of freq_q x l1 -- each addend carried independently in Q (uses L2990
   sqsum_app_cross; reconciled with the Section 13.3 sqsum_app_eq_set
   same-shape face, this piece consumes the Section A8 baseline name) *)
Theorem sqsum_app_cross_set : forall l1 l2 : list Q,
  QeqT ((Z.of_nat (sqsum (l1 ++ l2)) # 1)%Q)
       (((Z.of_nat (sqsum l1) # 1) + (Z.of_nat (sqsum l2) # 1)
         + (Z.of_nat (nsum (fun x => freq_q x l2) l1) # 1)
         + (Z.of_nat (nsum (fun x => freq_q x l1) l2) # 1))%Q).
Proof.
  intros l1 l2. apply qeqT_intro.
  rewrite (S01_BaseRing.id_eq_SI nat _ _ (sqsum_app_cross l1 l2)).
  unfold Qeq. simpl. rewrite !Z.mul_1_r. rewrite !Znat.Nat2Z.inj_add.
  reflexivity.
Defined.

(* ---------- 15.2 Baseline piece: the symmetric double sum in Set face ---------- *)

(* The symmetric double sum in Set face: the informative Q-carried face
   of the equality of the two cross terms (the same-count pairing set
   {(p,q) in l1 x l2 : p==q}) -- the nat identity lifted in one hop via
   QeqT_of_nat_eq (uses L2999 sqsum_cross_sym) *)
Theorem sqsum_cross_sym_set : forall l1 l2 : list Q,
  QeqT ((Z.of_nat (nsum (fun x => freq_q x l2) l1) # 1)%Q)
       ((Z.of_nat (nsum (fun x => freq_q x l1) l2) # 1)%Q).
Proof.
  intros l1 l2.
  (* Convention 3: inlined mother skeleton of the nat-equality lift
     bridge -- after the qeqT direct construction, the symmetric double
     sum identity is rewritten and closed by Qeq reflexivity, zero
     forwarding jumps *)
  apply qeqT_intro.
  rewrite (S01_BaseRing.id_eq_SI nat _ _ (sqsum_cross_sym l1 l2)). apply Qeq_refl.
Defined.

(* ---------- 15.3 Baseline companion piece: the 2X standard form in Set face ---------- *)

(* The 2X standard form in Set face: the Q-carried identity with the
   cross term merged via the symmetric double sum (sqsum l1 + sqsum l2 +
   2*X) -- the nat whole-expression lift channel (uses L3020
   sqsum_app_eq2; the merge face of the Section 15.1/15.2 pieces, the
   face-form ruling accounted in the Section 15 header) *)
Theorem sqsum_app_eq2_set : forall l1 l2 : list Q,
  QeqT ((Z.of_nat (sqsum (l1 ++ l2)) # 1)%Q)
       ((Z.of_nat (sqsum l1 + sqsum l2 + 2 * nsum (fun x => freq_q x l2) l1)
         # 1)%Q).
Proof.
  intros l1 l2.
  (* Convention 3: inlined mother skeleton of the nat-equality lift
     bridge -- after the qeqT direct construction, the 2X standard form
     identity is rewritten and closed by Qeq reflexivity, zero forwarding
     jumps *)
  apply qeqT_intro.
  rewrite (S01_BaseRing.id_eq_SI nat _ _ (sqsum_app_eq2 l1 l2)). apply Qeq_refl.
Defined.

(* ---------- 15.4 Core: the collide append convolution in Set face ---------- *)

(* The weighted exact convolution in Set face: collide (l1++l2) ==
   (n1/n)^2 * collide l1 + (n2/n)^2 * collide l2 + X/n^2 -- the
   weight-squared weighted combination plus the cross correction,
   term-by-term QeqT informative face; both nonempty guards verbatim per
   the file (the Prop guard erased at extraction; uses L3033
   collide_app_eq) *)
Theorem collide_app_eq_set : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat ->
  QeqT (collide (l1 ++ l2))
    ((qn (length l1) / qn (length l1 + length l2)%nat)
      * (qn (length l1) / qn (length l1 + length l2)%nat) * collide l1
    + (qn (length l2) / qn (length l1 + length l2)%nat)
      * (qn (length l2) / qn (length l1 + length l2)%nat) * collide l2
    + (qn (nsum (fun x => freq_q x l2) l1)
       + qn (nsum (fun x => freq_q x l1) l2))
      / (qn (length l1 + length l2)%nat * qn (length l1 + length l2)%nat))%Q.
Proof.
  intros l1 l2 H1 H2. apply qeqT_intro.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _ (collide_app_eq l1 l2 H1 H2)).
Defined.

(* ---------- 15.5 Main piece: the H_freq append convolution in Set face ---------- *)

(* The complete entropy-family append convolution identity in Set face:
   H_freq (l1++l2) == w1^2 * H_freq l1 + w2^2 * H_freq l2 + 2*w1*w2 -
   X/n^2 (uses L3073 H_freq_app_eq -- its on-file proof uses the
   H_freq_eq_bridge L1993 "H_freq == 1 - collide" bridge face, inherited
   along the chain here; both nonempty guards verbatim per the file) *)
Theorem H_freq_app_eq_set : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat ->
  QeqT (H_freq (l1 ++ l2))
    ((qn (length l1) / qn (length l1 + length l2)%nat)
      * (qn (length l1) / qn (length l1 + length l2)%nat) * H_freq l1
    + (qn (length l2) / qn (length l1 + length l2)%nat)
      * (qn (length l2) / qn (length l1 + length l2)%nat) * H_freq l2
    + 2 * (qn (length l1) / qn (length l1 + length l2)%nat)
        * (qn (length l2) / qn (length l1 + length l2)%nat)
    - (qn (nsum (fun x => freq_q x l2) l1)
       + qn (nsum (fun x => freq_q x l1) l2))
      / (qn (length l1 + length l2)%nat * qn (length l1 + length l2)%nat))%Q.
Proof.
  intros l1 l2 H1 H2. apply qeqT_intro.
  exact (S02_CauchyComplete.qeqT_imp_qeq _ _ (H_freq_app_eq l1 l2 H1 H2)).
Defined.

(* ---------- 15.6 Bonus piece: the three-segment associativity consistency in Set face ---------- *)

(* The three-segment append associativity convolution consistency in Set
   face: (l1++l2)++l3 and l1++(l2++l3) are the same list (app_assoc
   definitional), so the entropy-family convolution quantity coincides
   pointwise in QeqT under both groupings -- the H_freq face is chosen
   (the Q-domain identity carries more information than the sqsum nat
   face; uses L3118 H_freq_app_assoc) *)
Theorem H_freq_app_assoc_set : forall (l1 l2 l3 : list Q),
  QeqT (H_freq ((l1 ++ l2) ++ l3)) (H_freq (l1 ++ (l2 ++ l3))).
Proof.
  intros l1 l2 l3. apply qeqT_intro.
  (* Source skeleton of H_freq_app_assoc inlined: one app_assoc definitional rewrite step normalizes to the same list *)
  rewrite <- app_assoc. reflexivity.
Defined.

(* ========== Section 16, P3-B13 extraction check (U12 recipe: independent extraction per piece,
     acceptance = Obj.magic count 0, artifacts removed after verification) ========== *)

Extraction "b13_sqsum_app_cross_set_ext.ml" sqsum_app_cross_set.
Extraction "b13_sqsum_cross_sym_set_ext.ml" sqsum_cross_sym_set.
Extraction "b13_sqsum_app_eq2_set_ext.ml" sqsum_app_eq2_set.
Extraction "b13_collide_app_eq_set_ext.ml" collide_app_eq_set.
Extraction "b13_H_freq_app_eq_set_ext.ml" H_freq_app_eq_set.
Extraction "b13_H_freq_app_assoc_set_ext.ml" H_freq_app_assoc_set.

End DTPT_Bridge.

(* -- Slice-2 replacement-piece closure prints (appendix, machine-check attachment) -- *)
Import DTPT_Bridge.
Print Assumptions liar_diag_point.
Print Assumptions cv_size_preservation_T_set.
Print Assumptions cv_size_preservation_D_set.
Print Assumptions H_max_q_anti_set.
Print Assumptions sqsum_cross_sym_set.
Print Assumptions sqsum_app_eq2_set.
