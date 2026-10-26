(* ConstructiveWorld-Main audit carrier v5: direct exercise of the S12
   engine-correctness main-theorem family. *)

(** * abl_audit_base_v5: correctness carriers for the S12 engine family.

    Mission.  Five carrier theorems that genuinely exercise the
      engine-correctness main theorems of [S12_B5RecycleSF]: the
      two-step gradient-descent instance, the two-stage consensus
      split, the consensus instance at [eps := real_one], the
      union-find self-union pairing, and the Viterbi/beam-search
      concrete exercises.

    Dependencies.  Stdlib [QArith], [List], [Arith], [Lia],
      [Extraction].  Requires [S01_BaseRing], [S02_CauchyComplete]
      and [S12_B5RecycleSF].

    References.  ConstructiveWorld-Main, module [abl_audit_base_v5]
      (statement names carried over verbatim).

    Constructivity.  No admits and no classical logic; conjunctions
      sit on [And], equalities on [Id], witnesses on [sigT], nat-order
      premises on [NatLe], comparisons on [real_le]/[real_lt]/
      [QleT']/[QId]; no [exists] or Prop connectives in statement
      faces; the auxiliary lemmas are stdlib-eq plumbing (the
      upstream iteration-length export is stated on stdlib [eq]).

    Build.  [coqc -native-compiler no -Q . "" abl_audit_base_v5.v];
      artifact magic [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S12_B5RecycleSF.
From Stdlib Require Import QArith.QArith QArith.Qabs
               Lists.List Arith.Arith.
Import ListNotations.
From Stdlib Require Import Lia.
Local Open Scope Q_scope.

(* Internal plumbing (stdlib-eq usage bridges; not carrier statements). *)

(* stdlib eq to Set-level Id bridge (the upstream iteration-length export is stated on stdlib eq). *)
Lemma abe_eq_id : forall (A : Set) (x y : A), x = y -> Id x y.
Proof.
  intros A x y H. destruct H. apply id_refl.
Qed.

(* Projections for [And] ([= A*B]) stated on the definition. *)
Definition abe_and_l (A B : Set) (p : And A B) : A :=
  match p with (a, _) => a end.
Definition abe_and_r (A B : Set) (p : And A B) : B :=
  match p with (_, b) => b end.

(* Consensus iteration splits: running [k1 + k2] stages equals running
   [k2] stages from the result of [k1] stages (kernel conversion along
   the [sf_consensus_iter] fixpoint; stdlib-eq plumbing). *)
Lemma abe_consensus_iter_add :
  forall (k1 : nat) (agents : list SFAgent) (k2 : nat),
    Id (sf_consensus_iter agents (k1 + k2))
       (sf_consensus_iter (sf_consensus_iter agents k1) k2).
Proof.
  intros k1. induction k1 as [| k1' IH]; intros agents k2.
  - apply id_refl.
  - cbn [Nat.add sf_consensus_iter].
    exact (IH (map (fun p => fst (sf_consensus_update (fst p) (snd p)))
                   (sf_pair_agents agents)) k2).
Qed.

(* Carrier 1 (gradient descent): the two-step instance of the
   convergence bound at step [1/2], pairing the convergence face
   ([QleT']) with the exact cost equality ([QId]). *)

Theorem abe_grad_half_two_step :
  forall (t x : Q),
    And (QleT' (sf_quad_cost t (sf_grad_descent sf_step_half t x 2))
               (qpow2 ((1 - sf_step_half) * (1 - sf_step_half)) 2
                * sf_quad_cost t x))
        (QId (sf_quad_cost t (sf_grad_descent sf_step_half t x 2))
             (qpow2 ((1 - sf_step_half) * (1 - sf_step_half)) 2
              * sf_quad_cost t x)).
Proof.
  intros t x. split.
  - (* Convergence face: the main theorem instantiated at [h := 1/2],
     [n := 2]; the premise slots consume the two wings of the standing
     [sf_step_half_bounds] conjunction. *)
    exact (@sf_grad_descent_convergence sf_step_half t x 2
             (abe_and_l _ _ sf_step_half_bounds)
             (abe_and_r _ _ sf_step_half_bounds)).
  - (* Exact equality face: the step-cost lemma instance, entered on the
     [QId] face via [qid_intro]. *)
    apply qid_intro.
    apply qeqT_imp_qeq.
    exact (sf_grad_descent_cost_eq sf_step_half t 2 x).
Qed.

(* Carrier 2 (consensus, part one): the two-stage split form, with the
   length-accounting lemma used on both stages; premise on [NatLe],
   conclusion on [Id]. *)

Theorem abe_consensus_iter_split :
  forall (agents : list SFAgent) (k1 k2 : nat),
    NatLe (k1 + k2) (length agents) ->
    Id ((length (sf_consensus_iter agents (k1 + k2)) + k1) + k2)%nat
       (length agents).
Proof.
  intros agents k1 k2 Hk.
  pose proof (NatLe_drop (k1 + k2) (length agents) Hk) as Hk'.
  assert (Hk1 : (k1 <= length agents)%nat).
  { apply (Nat.le_trans _ (k1 + k2) _ (Nat.le_add_r k1 k2)). exact Hk'. }
  pose proof (match sf_consensus_iter_len k1 agents Hk1 in Id _ z
              return ((length (sf_consensus_iter agents k1) + k1)%nat = z) with
              | id_refl => eq_refl end) as H1.
  assert (Hk2 : (k2 <= length (sf_consensus_iter agents k1))%nat) by lia.
  pose proof (match sf_consensus_iter_len k2 (sf_consensus_iter agents k1) Hk2
              in Id _ z
              return ((length (sf_consensus_iter (sf_consensus_iter agents k1)
                                k2) + k2)%nat = z) with
              | id_refl => eq_refl end) as H2.
  destruct (id_sym (abe_consensus_iter_add k1 agents k2)).
  apply abe_eq_id. lia.
Qed.

(* Carrier 3 (consensus, part two): the convergence theorem
   instantiated at [eps := real_one]; the sigT witness sits on Set and
   the [0 < 1] premise is kept explicitly on [real_lt]. *)

Theorem abe_consensus_bounded_one :
  forall (agents : list SFAgent),
    real_lt real_zero real_one ->
    sigT (fun k : nat =>
      forall x y : SFAgent,
        InT x (sf_consensus_iter agents k) ->
        InT y (sf_consensus_iter agents k) ->
        real_le (sf_dist_sq (sf_agent_coord x) (sf_agent_coord y)) real_one).
Proof.
  intros agents H01.
  exact (sf_consensus_converges agents real_one H01).
Qed.

(* Carrier 4 (union-find): the merge-idempotence theorem in general
   form (self-union is the identity) paired with the concrete table
   [(1,0) :: nil] instance. *)

Theorem abe_uf_self_union_and_pair :
  And (forall (uf : SFUnionFind) (x : nat), Id (sf_uf_union uf x x) uf)
      (Id (sf_uf_union ((1%nat, 0%nat) :: nil) 1%nat 0%nat)
          ((1%nat, 0%nat) :: nil)).
Proof.
  split.
  - (* General form: the theorem consumes the id_refl proof that the two
     roots agree definitionally. *)
    intros uf x. apply sf_uf_union_idempotent_same_root. apply id_refl.
  - (* Concrete instance: [find2] computes both roots to 0 on the concrete
     table, then the theorem applies. *)
    apply sf_uf_union_idempotent_same_root.
    cbn [sf_uf_find2 Nat.eqb]. apply id_refl.
Qed.

(* Carrier 5 (Viterbi): three concrete computations over the engine
   functions themselves ([sf_viterbi] with [sf_vec_hash]).  The
   matching theorem [sf_viterbi_matches] is stated as a premise-free
   triviality and is deliberately not used; the concrete instances
   below supply the real content: a hit yields the path, a miss yields
   the empty path, and a two-step run picks the hit state at each
   step. *)

Theorem abe_viterbi_concrete_matched :
  And (Id (sf_viterbi (nil :: nil) (sf_vec_hash nil :: nil)) (nil :: nil))
      (And (Id (sf_viterbi (nil :: nil) (1 :: nil)%nat) nil)
           (Id (sf_viterbi ((nil : SFVec) :: (real_zero :: nil) :: nil)
                           (0 :: 1 :: nil)%nat)
               ((nil : SFVec) :: (real_zero :: nil) :: nil))).
Proof.
  split.
  - (* Observation [[hash nil] = 0] hits the single state: the path is
     [[nil]]. *)
    exact id_refl.
  - split.
    + (* Observation [1] hits no state: the path is empty (the greedy
       skip branch). *)
      exact id_refl.
    + (* Observations [[0;1] against the two-state table (empty vector or
       single-zero vector): each step picks its hit state (the two
       branches of the greedy loop). *)
      exact id_refl.
Qed.

(* Carrier 6 (beam search): the optimality theorem and its auxiliary
   lemma used together - rechecking does not regress and optimality is
   preserved over candidates.  The comparison interface [cmp] is
   quantified explicitly over its exported argument face ([Or] on
   [A+B]); this module stays on that argument face and does not
   instantiate it. *)

Theorem abe_beam_rerun_no_regress :
  forall (cmp : forall p q : list SFVec,
            Or (real_le (sf_path_energy p) (sf_path_energy q))
               (real_lt (sf_path_energy q) (sf_path_energy p)))
         (cands : list (list SFVec)) (seed p : list SFVec),
    InT p cands ->
    And (real_le (sf_path_energy (sf_beam_search cmp cands
                    (sf_beam_search cmp cands seed)))
                 (sf_path_energy (sf_beam_search cmp cands seed)))
        (real_le (sf_path_energy (sf_beam_search cmp cands
                    (sf_beam_search cmp cands seed)))
                 (sf_path_energy p)).
Proof.
  intros cmp cands seed p Hin. split.
  - (* No regression: the auxiliary lemma instantiated with the first-round
     result as the new seed; the first wing gives the energy bound. *)
    exact (abe_and_l _ _ (sf_beam_aux_correct cmp cands
                   (sf_beam_search cmp cands seed))).
  - (* Optimality preserved: the main theorem instantiated with the
     first-round result as the seed; [InT p cands] slots in unchanged. *)
    exact (sf_beam_search_optimal cmp cands
             (sf_beam_search cmp cands seed) p Hin).
Qed.

(* Assumption audit: the S12 engine-correctness main theorems are
   audited across modules, followed by the six carriers of this
   module.  Every entry must report [Closed under the global context].
   The Require closure contains [Lqa] (the Q-domain decision supply);
   that environment face is accounted at the coqchk level and is not
   introduced by this module. *)

Print Assumptions S12_B5RecycleSF.sf_grad_descent_convergence.
Print Assumptions S12_B5RecycleSF.sf_grad_descent_cost_eq.
Print Assumptions S12_B5RecycleSF.sf_consensus_iter_len.
Print Assumptions S12_B5RecycleSF.sf_consensus_converges.
Print Assumptions S12_B5RecycleSF.sf_uf_union_idempotent_same_root.
Print Assumptions S12_B5RecycleSF.sf_beam_search_optimal.
Print Assumptions S12_B5RecycleSF.sf_beam_aux_correct.
Print Assumptions S12_B5RecycleSF.sf_viterbi_matches.
Print Assumptions abe_grad_half_two_step.
Print Assumptions abe_consensus_iter_split.
Print Assumptions abe_consensus_bounded_one.
Print Assumptions abe_uf_self_union_and_pair.
Print Assumptions abe_viterbi_concrete_matched.
Print Assumptions abe_beam_rerun_no_regress.

(* Extraction port: the carriers double as extraction targets (zero
   [Obj.magic] on the extracted face). *)

From Stdlib Require Import Extraction.
Separate Extraction abe_grad_half_two_step abe_consensus_iter_split
  abe_consensus_bounded_one abe_uf_self_union_and_pair
  abe_viterbi_concrete_matched abe_beam_rerun_no_regress.
