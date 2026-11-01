(** * abl_audit_base_v5b: direct-audit closure carriers for the S12
    residual-slot ore (the quota-boundary remainder of the CS audit v5
    report), closed in A-form.

    Mission.  Eight carrier theorems, sixteen genuine use points.  Main
      slot = sf_min_pick_spec (the min-action selection spec, cmp-carried):
      abj_minpick_two_stage (two stages; connectivity, seed and candidate
      faces twice each; And wings split by the v5 abe_and_l/abe_and_r
      fittings; cmp rides the exported Set-layer argument face, never
      instantiated) and abj_minpick_concrete_nohit (the greedy no-hit
      branch computed; cmp never exercised); plus the remainder carriers
      abj_grad_step_general_and_half, abj_consensus_pair_zero_both,
      abj_mp_iter_split_no_regress, abj_curriculum_two_stage, abj_qw2_triple
      and abj_qupdate_alpha0_pair (detail in the section banners below).
    Dependencies.  Stdlib QArith, List, Arith, Lia, Extraction; requires
      S01_BaseRing, S02_CauchyComplete, S12_B5RecycleSF and
      abl_audit_base_v5 (same-family chained predecessor; its
      abe_and_l/abe_and_r fittings consumed, its six carriers re-audited).
    References.  ConstructiveWorld-Main, module abl_audit_base_v5b
      (statement names carried over verbatim); the in-tree same-family
      variant abl_audit_base_v5.
    Constructivity.  Assumption-free, classical-logic-free, no Prop
      carriers: conjunctions on And (:= A*B), equalities on Id and QId/Id
      (the Qeq_bool face, Set layer), comparisons on real_le, real_lt,
      real_eq, QleT', QId, premise slots Set-typed Pi; proof bodies are
      exact/apply/cbn/id_refl handovers; the Prop face only at the
      mandatory qid_intro bridge (the v5 precedent).
    Build.  rocq c -native-compiler no -q -Q . "" abl_audit_base_v5b.v
      (world-directory co-located; the chained predecessor
      abl_audit_base_v5 born first; artifact magic 436f7121 00015ff4). *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S12_B5RecycleSF.
Require Import abl_audit_base_v5.
From Stdlib Require Import QArith.QArith QArith.Qabs
               Lists.List Arith.Arith.
Import ListNotations.
From Stdlib Require Import Lia.
Local Open Scope Q_scope.

(* Verification notes (carried from the source face, one for one):
   - Exit signatures as measured on this world's born chain:
     sf_min_pick_spec argument order is cmp start goal rest seed (rest
     before seed), while the engine sf_min_pick is cmp start goal seed
     rest; sf_curriculum_monotone exports M, step, loss and the section
     premise as four explicit slots; sf_message_passing_contractive
     carries its single-step premise as an explicit forall slot.
   - The abj_ prefix is grep-clean over the whole tree (collision
     vetting).
   - Bridges (measured on this world, wrapped accordingly): the upstream
     QeqT exits of sf_grad_cost_step_eq / sf_qw2_eq_qsub enter the Set
     layer via the standing qid_intro + qeqT_imp_qeq bridge (the v5
     precedent, same shape), and the no-hit branch lowers the Id-carried
     premise of sf_bool_id_true to its stdlib-eq assert by Id elimination
     (the stdlib-eq plumbing family of the v5 file) - the proof-body hunks
     against the source face.
   - sf_vec_hash: nil -> 0, non-empty -> 1; sf_path_connects matches the
     first and last hashes; the no-hit concrete instance closes by pure
     computation along this face.
   - sf_quad_cost t x = (1/2)*(x-t)^2 and sf_grad_step h t x =
     x - h*(x-t); the concrete wing at h=1/2, t=0, x=3 reduces to 9/8 on
     both sides (the Qeq_bool cross-multiplication criterion). *)

(* ===================================================================== *)
(* Section 0. Carrier 1 (main closure slot): the min-action selection     *)
(*    spec in two-stage composition (sf_min_pick_spec genuinely exercised *)
(*    twice; connectivity, seed and candidate faces twice each).          *)
(* ===================================================================== *)

Theorem abj_minpick_two_stage :
  forall (cmp : forall a b : Real, Or (real_le a b) (real_lt b a))
         (start goal : SFVec) (r1 r2 : list (list SFVec)) (seed : list SFVec),
    Id (sf_path_connects start goal seed) true ->
    And (Id (sf_path_connects start goal
               (sf_min_pick cmp start goal
                  (sf_min_pick cmp start goal seed r1) r2)) true)
        (And (real_le (sf_action (sf_min_pick cmp start goal
                                  (sf_min_pick cmp start goal seed r1) r2))
                      (sf_action seed))
             (And (forall x : list SFVec,
                     InT x r1 -> Id (sf_path_connects start goal x) true ->
                     real_le (sf_action (sf_min_pick cmp start goal
                                           (sf_min_pick cmp start goal seed r1) r2))
                             (sf_action x))
                  (forall x : list SFVec,
                     InT x r2 -> Id (sf_path_connects start goal x) true ->
                     real_le (sf_action (sf_min_pick cmp start goal
                                           (sf_min_pick cmp start goal seed r1) r2))
                             (sf_action x)))).
Proof.
  intros cmp start goal r1 r2 seed Hseed.
  (* Stage 1: the r1-stage selection (three faces); And wings split via *)
  (* the v5 file abe_and_l/abe_and_r fittings (chained use). *)
  destruct (sf_min_pick_spec cmp start goal r1 seed Hseed) as [Hc1 Hr1].
  pose proof (abe_and_l _ _ Hr1) as Hb1.
  pose proof (abe_and_r _ _ Hr1) as Hd1.
  (* Stage 2: the r2-stage selection seeded by the stage-1 result; the *)
  (* connectivity premise slot is fed by stage 1's connectivity face. *)
  destruct (sf_min_pick_spec cmp start goal r2
              (sf_min_pick cmp start goal seed r1) Hc1) as [Hc2 Hr2].
  pose proof (abe_and_l _ _ Hr2) as Hb2.
  pose proof (abe_and_r _ _ Hr2) as Hd2.
  split.
  - (* Connectivity face: the stage-2 connectivity face handed over directly. *)
    exact Hc2.
  - split.
    + (* Seed face: E(stage-2) <= E(stage-1) <= E(seed); the two stages' *)
      (* seed faces composed via trans. *)
      exact (real_le_trans _ _ _ Hb2 Hb1).
    + split.
      * (* r1 candidate face: E(stage-2) <= E(stage-1) <= E(x); stage 1's *)
        (* candidate face genuinely exercised. *)
        intros x Hx Hcx.
        exact (real_le_trans _ _ _ Hb2 (Hd1 x Hx Hcx)).
      * (* r2 candidate face: the stage-2 candidate face genuinely exercised. *)
        intros x Hx Hcx.
        exact (Hd2 x Hx Hcx).
Qed.

(* ===================================================================== *)
(* Section 1. Carrier 2: the min-action selection spec, concrete no-hit   *)
(*    instance (the greedy-skip branch computed).  cmp is quantified      *)
(*    throughout and never exercised (the no-hit branch does not call the *)
(*    comparison interface).                                              *)
(* ===================================================================== *)

Definition abj_vz : SFVec := real_zero :: nil.
Definition abj_seed_path : list SFVec := abj_vz :: nil.
Definition abj_miss_cands : list (list SFVec) := ((nil : SFVec) :: nil) :: nil.

Theorem abj_minpick_concrete_nohit :
  forall cmp : forall a b : Real, Or (real_le a b) (real_lt b a),
    And (Id (sf_path_connects abj_vz abj_vz
               (sf_min_pick cmp abj_vz abj_vz abj_seed_path abj_miss_cands)) true)
        (And (real_le (sf_action (sf_min_pick cmp abj_vz abj_vz
                                  abj_seed_path abj_miss_cands))
                      (sf_action abj_seed_path))
             (forall x : list SFVec,
                InT x abj_miss_cands ->
                Id (sf_path_connects abj_vz abj_vz x) true ->
                real_le (sf_action (sf_min_pick cmp abj_vz abj_vz
                                      abj_seed_path abj_miss_cands))
                        (sf_action x))).
Proof.
  intros cmp. split.
  - (* Candidate [empty vector] misses on the first-state hash 0<>1: the *)
    (* selection reduces to the seed [abj_vz]; the seed path starts and *)
    (* ends at abj_vz (hash 1) and is connected - fully computational. *)
    exact id_refl.
  - split.
    + (* Selection = seed: energy self-reflexive. *)
      apply real_le_refl.
    + intros x Hx Hcx.
      inversion Hx as [l0 | y l0 Hin]; subst.
      * (* The only candidate = [empty vector]: hash 0<>1 misses; the *)
        (* connectivity premise yields a false=true contradiction.  The *)
        (* measured tree exit of sf_bool_id_true is the Id carrier, so the *)
        (* premise is lowered to the assert's stdlib-eq face by Id *)
        (* elimination (the stdlib-eq plumbing family of the v5 file). *)
        assert (Hf : sf_path_connects abj_vz abj_vz ((nil : SFVec) :: nil) = true).
        { destruct (sf_bool_id_true _ Hcx). reflexivity. }
        unfold abj_vz in Hf.
        cbn [sf_path_connects sf_vec_hash sf_last Nat.eqb andb] in Hf.
        discriminate Hf.
      * (* InT x nil: the empty list has no members (Rocq 9 does not prune *)
        (* destruct on this family's index; per the S12 precedent, inversion *)
        (* with index injection pruning). *)
        inversion Hin.
Qed.

(* ===================================================================== *)
(* Section 2. Carrier 3: the gradient-descent single-step exact equality, *)
(*    the general form (QId equality face genuinely exercised) and the    *)
(*    concrete instance (h=1/2, t=0, x=3, both sides reduce to 9/8,       *)
(*    computational closure) carried together.                            *)
(* ===================================================================== *)

Theorem abj_grad_step_general_and_half :
  And (forall h t x : Q,
         QId (sf_quad_cost t (sf_grad_step h t x))
             ((1 - h) * (1 - h) * sf_quad_cost t x))
      (QId (sf_quad_cost 0 (sf_grad_step (1#2) 0 3))
           ((1 - (1#2)) * (1 - (1#2)) * sf_quad_cost 0 3)).
Proof.
  split.
  - (* General form: the measured tree exit of sf_grad_cost_step_eq is *)
    (* the QeqT carrier; enter the Set-layer QId via the standing *)
    (* qid_intro + qeqT_imp_qeq bridge (the v5 precedent, same shape). *)
    intros h t x. apply qid_intro.
    apply qeqT_imp_qeq.
    exact (sf_grad_cost_step_eq h t x).
  - (* Concrete instance: grad_step = 3/2, cost = 9/8; (1/2)^2 * (9/2) = 9/8 *)
    (* - Qeq_bool computation. *)
    exact id_refl.
Qed.

(* ===================================================================== *)
(* Section 3. Carrier 4: post-consensus two-body distance zero, the       *)
(*    forward and swapped pairings plus a concrete-agent instance, three  *)
(*    wings (sf_consensus_dist_zero exercised three times, on the         *)
(*    real_eq Set-layer face).                                            *)
(* ===================================================================== *)

Theorem abj_consensus_pair_zero_both :
  And (forall a b : SFAgent,
         real_eq (sf_dist_sq (sf_agent_coord (fst (sf_consensus_update a b)))
                             (sf_agent_coord (snd (sf_consensus_update a b))))
                 real_zero)
      (And (forall a b : SFAgent,
              real_eq (sf_dist_sq (sf_agent_coord (fst (sf_consensus_update b a)))
                                  (sf_agent_coord (snd (sf_consensus_update b a))))
                      real_zero)
           (real_eq (sf_dist_sq
                       (sf_agent_coord
                          (fst (sf_consensus_update
                                  (Build_SFAgent 0 (real_zero :: nil))
                                  (Build_SFAgent 1 (real_one :: nil)))))
                       (sf_agent_coord
                          (snd (sf_consensus_update
                                  (Build_SFAgent 0 (real_zero :: nil))
                                  (Build_SFAgent 1 (real_one :: nil))))))
                    real_zero)).
Proof.
  split.
  - (* Forward pairing: the main theorem handed over directly. *)
    intros a b. exact (sf_consensus_dist_zero a b).
  - split.
    + (* Swapped pairing: the main theorem transposed (the second wing of *)
      (* the two-fold exercise). *)
      intros a b. exact (sf_consensus_dist_zero b a).
    + (* Concrete instance: the agents (0,[0]) and (1,[1]) share *)
      (* coordinates after consensus. *)
      exact (sf_consensus_dist_zero (Build_SFAgent 0 (real_zero :: nil))
                                    (Build_SFAgent 1 (real_one :: nil))).
Qed.

(* ===================================================================== *)
(* Section 4. Carrier 5: message-passing contraction in iterative split   *)
(*    composition - m stages after n stages are no worse than the start   *)
(*    (the contraction main theorem genuinely exercised twice; the        *)
(*    single-step premise slot threaded unchanged, used along the         *)
(*    argument face).                                                     *)
(* ===================================================================== *)

Theorem abj_mp_iter_split_no_regress :
  forall (g : SFGraph)
         (Hstep : forall f : list SFVec,
                    real_le (sf_sq_sum (sf_mflatten (sf_message_passing g f)))
                            (sf_sq_sum (sf_mflatten f)))
         (feats : list SFVec) (n m : nat),
    real_le (sf_sq_sum (sf_mflatten (sf_iterate_mp g (sf_iterate_mp g feats n) m)))
            (sf_sq_sum (sf_mflatten feats)).
Proof.
  intros g Hstep feats n m.
  apply (real_le_trans
           (sf_sq_sum (sf_mflatten (sf_iterate_mp g (sf_iterate_mp g feats n) m)))
           (sf_sq_sum (sf_mflatten (sf_iterate_mp g feats n)))
           (sf_sq_sum (sf_mflatten feats))).
  - (* Later m stages: the main theorem instantiated with the n-stage *)
    (* result table as the start. *)
    exact (sf_message_passing_contractive g Hstep (sf_iterate_mp g feats n) m).
  - (* Earlier n stages: the main theorem instantiated in place. *)
    exact (sf_message_passing_contractive g Hstep feats n).
Qed.

(* ===================================================================== *)
(* Section 5. Carrier 6: curriculum-learning monotonicity (three section  *)
(*    slots exported explicitly) in two-stage curriculum composition -    *)
(*    the accumulated curriculum of s1 then s2 does not increase the loss *)
(*    (the main theorem genuinely exercised twice, composed per stage).   *)
(* ===================================================================== *)

Theorem abj_curriculum_two_stage :
  forall (M : Set) (step : M -> SFVec -> M) (loss : M -> Real)
         (Hok : forall (m : M) (smp : SFVec),
                  real_le (loss (step m smp)) (loss m))
         (s1 s2 : list SFVec) (m0 : M),
    real_le (loss (sf_curriculum_run M step s2 (sf_curriculum_run M step s1 m0)))
            (loss m0).
Proof.
  intros M step loss Hok s1 s2 m0.
  apply (real_le_trans
           (loss (sf_curriculum_run M step s2 (sf_curriculum_run M step s1 m0)))
           (loss (sf_curriculum_run M step s1 m0))
           (loss m0)).
  - (* Later stage s2: the main theorem instantiated with the s1-stage *)
    (* result model as the start. *)
    exact (sf_curriculum_monotone M step loss Hok s2 (sf_curriculum_run M step s1 m0)).
  - (* Earlier stage s1: the main theorem instantiated in place. *)
    exact (sf_curriculum_monotone M step loss Hok s1 m0).
Qed.

(* ===================================================================== *)
(* Section 6. Carrier 7: the Wasserstein block, three items - symmetry    *)
(*    (general form + concrete computation), same-distribution zero       *)
(*    (general form + concrete computation), and paired mean square =     *)
(*    pointwise squared-difference sum (QId face genuinely exercised).    *)
(* ===================================================================== *)

Theorem abj_qw2_triple :
  And (forall mu nu : list Q,
         Id (Qeq_bool (sf_qw2 mu nu) (sf_qw2 nu mu)) true)
      (And (forall mu : list Q,
              Id (Qeq_bool (sf_qw2 mu mu) 0) true)
           (And (forall mu nu : list Q,
                   QId (sf_qw2 mu nu)
                       (sf_qsum (map (fun d : Q => d * d) (sf_qsub mu nu))))
                (And (Id (Qeq_bool (sf_qw2 ((1#2) :: nil) ((1#3) :: nil))
                                 (sf_qw2 ((1#3) :: nil) ((1#2) :: nil))) true)
                     (Id (Qeq_bool (sf_qw2 ((1#2) :: nil) ((1#2) :: nil)) 0) true)))).
Proof.
  split.
  - (* Symmetry general form: the main theorem handed over directly. *)
    intros mu nu. exact (sf_qw2_sym mu nu).
  - split.
    + (* Same-distribution zero general form: the main theorem handed over *)
      (* directly. *)
      intros mu. exact (sf_qw2_same mu).
    + split.
      * (* Equality face: the measured tree exit of sf_qw2_eq_qsub is the *)
        (* QeqT carrier; enter the Set-layer QId via the standing *)
        (* qid_intro + qeqT_imp_qeq bridge (the v5 precedent, same shape). *)
        intros mu nu. apply qid_intro.
        apply qeqT_imp_qeq.
        exact (sf_qw2_eq_qsub mu nu).
      * split.
        -- (* Symmetry concrete instance: (1/2,1/3) reduces to (1/36)^2 in *)
           (* both directions - computational closure. *)
           exact id_refl.
        -- (* Same-distribution zero concrete instance: (1/2)-(1/2)=0, *)
           (* computational closure. *)
           exact id_refl.
Qed.

(* ===================================================================== *)
(* Section 7. Carrier 8: the Q-learning block - the alpha=0 table-value-  *)
(*    unchanged main theorem in general form genuinely exercised plus a   *)
(*    concrete table instance (q=[[5]]; the readback is unchanged after   *)
(*    the alpha=0 update; Qeq_bool computational closure).                *)
(* ===================================================================== *)

Theorem abj_qupdate_alpha0_pair :
  And (forall (q : SFQTable) (s a sp : nat) (r gamma : Q),
         Id (Qeq_bool (nth a (nth s (sf_q_update q s a sp r 0 gamma) nil) 0)
                      (nth a (nth s q nil) 0)) true)
      (Id (Qeq_bool (nth 0 (nth 0 (sf_q_update (((5#1) :: nil) :: nil) 0 0 0
                                    (3#1) 0 (1#2)) nil) 0)
                    (nth 0 (nth 0 (((5#1) :: nil) :: nil) nil) 0)) true).
Proof.
  split.
  - (* General form: the main theorem handed over directly. *)
    intros q s a sp r gamma. exact (sf_q_update_alpha0 q s a sp r gamma).
  - (* Concrete instance: at alpha=0 the new value = the old value = 5; the *)
    (* update is idempotent - Qeq_bool computational closure. *)
    exact id_refl.
Qed.

(* ===================================================================== *)
(* Section 8. Tail bay: assumption audit (the twelve true slots of the    *)
(*    S12 residual ore under direct audit + the two shell slots + the v5  *)
(*    six-carrier chained audit + this file's eight-carrier self-audit).  *)
(*    Reading criterion: all twenty-eight entries report Closed under the *)
(*    global context.  Note: the Require closure contains Lqa (the        *)
(*    Q-domain decision supply face); that environment face is accounted  *)
(*    at the coqchk level per the standing precedent and per-theorem PA   *)
(*    checks, and is not introduced by this file.                         *)
(* ===================================================================== *)

(* -- the twelve true slots of the S12 residual ore (the direct-audit *)
(*    body of this file) -- *)
Print Assumptions S12_B5RecycleSF.sf_min_pick_spec.
Print Assumptions S12_B5RecycleSF.sf_minimal_action_exists.
Print Assumptions S12_B5RecycleSF.sf_grad_cost_step_eq.
Print Assumptions S12_B5RecycleSF.sf_consensus_dist_zero.
Print Assumptions S12_B5RecycleSF.sf_message_passing_contractive.
Print Assumptions S12_B5RecycleSF.sf_curriculum_monotone.
Print Assumptions S12_B5RecycleSF.sf_qw2_sym.
Print Assumptions S12_B5RecycleSF.sf_qw2_same.
Print Assumptions S12_B5RecycleSF.sf_qw2_eq_qsub.
Print Assumptions S12_B5RecycleSF.sf_q_update_alpha0.
Print Assumptions S12_B5RecycleSF.sf_q_update_zero_core.
Print Assumptions S12_B5RecycleSF.sf_nth_update_same_qeq.
(* -- shell slots on file in the same module (registered, not used; *)
(*    closed true on the assumption face) -- *)
Print Assumptions S12_B5RecycleSF.sf_kmeans_nonincrease.
Print Assumptions S12_B5RecycleSF.sf_viterbi_matches.
(* -- the v5 predecessor file's six carriers, chained audit (chained- *)
(*    closure recheck) -- *)
Print Assumptions abe_grad_half_two_step.
Print Assumptions abe_consensus_iter_split.
Print Assumptions abe_consensus_bounded_one.
Print Assumptions abe_uf_self_union_and_pair.
Print Assumptions abe_viterbi_concrete_matched.
Print Assumptions abe_beam_rerun_no_regress.
(* -- this file's eight-carrier self-audit -- *)
Print Assumptions abj_minpick_two_stage.
Print Assumptions abj_minpick_concrete_nohit.
Print Assumptions abj_grad_step_general_and_half.
Print Assumptions abj_consensus_pair_zero_both.
Print Assumptions abj_mp_iter_split_no_regress.
Print Assumptions abj_curriculum_two_stage.
Print Assumptions abj_qw2_triple.
Print Assumptions abj_qupdate_alpha0_pair.

(* ===================================================================== *)
(* Section 9. Exit bay: the carriers double as extraction ports (zero     *)
(*    magic on the extracted face).                                       *)
(* ===================================================================== *)

From Stdlib Require Import Extraction.
Separate Extraction abj_minpick_two_stage abj_minpick_concrete_nohit
  abj_grad_step_general_and_half abj_consensus_pair_zero_both
  abj_mp_iter_split_no_regress abj_curriculum_two_stage
  abj_qw2_triple abj_qupdate_alpha0_pair.
