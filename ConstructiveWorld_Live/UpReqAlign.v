(* ==========================================================================
   UpReqAlign.v - alignment segment 1 (req_* family) on this world's
   argument-less interface Class: five sections (ReqAlignCore, ReqKLProjection,
   ReqNaturalGradient, ReqPPORatio, ReqSigmoidQuick).
   Mission. 使命: the theorem/lemma statement face of this file - the req
     forms of the alignment core (F_align / pi_star cluster), the KL
     projection items (rkl_* family, among them rkl_log_inv_one_inv), the
     natural-gradient items, the PPO ratio cluster, and the sigmoid quick
     cluster; every item fully proved, each station Qed-closed, the tail
     Print Assumptions probes report the closure face.
   Dependencies. 依赖清单: S01_BaseRing..S15_TailFEPUp, UpReqAlgebra of this
     development (-Set lineage world); the interface is the argument-less
     Class RealInterfaceEnhancedSetoid of S07_RealSetoidExpLog (module
     RealInterfaceEnhancedMod), fields resolved through the global Real
     instance.
   References. 对标: statement names carried over verbatim from the source
     piece; adaptation = pure binder removal + notation rebinding on this
     world's own precedent (the source five Context {R : Set}
     {RIS : RealInterfaceEnhancedSetoid R} binders were an alien argumented
     face raising "Illegal application (Non-functional construction)"):
     R := Real by notation (UpReqSumD.v L58; S10_KVQuantTrig.v L12417-12419),
     predicate face real_eq / real_lt / real_le (UpReqSumD.v L113-114 /
     L304-305), law fields as bare names through the global instance
     (UpReqSumD.v L68-72); no Obj.magic, no Prop-cast, statement names
     unchanged.
   Constructivity. 构造性注记: all Set-layer statements; the section premise
     slots are honest interface premises carried explicitly; zero new axioms.
   Build. 编译配方: rocq c -native-compiler no -Q . "" UpReqAlign.v inside the
     -Set lineage world (cpu_guard thermal wrapper, ulimit -s 65532).
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Import RealInterfaceEnhancedMod.

(* R := Real by notation: this world's RealInterfaceEnhancedSetoid is the
   argument-less Class, its fields resolve through the global Real instance
   (UpReqSumD.v L58 precedent; S10_KVQuantTrig.v L12417-12419 ruling). *)
Notation R := Real.

(* ============================================================ *)
(* ReqAlignCore: alignment-section real_eq infrastructure + RLHF/DPO core + main chain *)
(*   (Id original section: Alignment L18734-23272; section arguments aligned item-by-item)    *)
(* ============================================================ *)
Section ReqAlignCore.
Variable S : Set.

(* ---- real_eq-signature docking surface for SumOver (= the sum_req_over_S spec
        surface, counterpart of L66177; sum_le/sum_zero_nonneg are the real_eq
        counterparts of the Id sum_over_S_le/_zero_nonneg -- honest interface
        hypotheses; realizable for finite sums at the Real layer, as in the
        Z_align_pos precedent) ---- *)
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    real_eq (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    real_eq (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, real_le (f s) (g s)) -> real_le (sumf f) (sumf g).
Hypothesis sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, real_le zero (f s)) -> real_eq (sumf f) zero -> forall s : S, real_eq (f s) zero.

(* Interface-gap bridge (register 3; counterpart of UpReqAlgebra ReqLogBridge,
   T2(1)): satisfiable by the Real instance (Cauchy log continuity);
   instantiation deferred to the interface-extension batch. *)
Hypothesis log_req_compat :
  forall (x y : R) (Hx : real_lt zero x) (Hy : real_lt zero y),
    real_eq x y -> real_eq (log x Hx) (log y Hy).

(* ---- Section arguments (aligned to the Id system L18750-18768) ---- *)
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : real_lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, real_lt zero (pi_ref s).
Variable pi_ref_norm : real_eq (sumf pi_ref) one.

(* ---- real_eq-system in-section definitions ---- *)
Definition pos_dist (p : S -> R) : Set := forall s : S, real_lt zero (p s).
Definition norm_one (p : S -> R) : Set := real_eq (sumf p) one.

(* Partition function and closed-form optimal policy (same shapes as Id Z_align/pi_star L18769-18780) *)
Definition Z_align_req : R :=
  sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
(* Forward lemma (the former Variable replaced by a same-name Lemma, foundation-ablation wave T2 final verdict B39): derived from sum_pos+pi_ref_pos+mult_positive/exp_neg_pos; zero admitted items *)
Lemma Z_align_pos : real_lt zero Z_align_req.
Proof.
  unfold Z_align_req. apply sum_pos. intros s. apply mult_positive.
  exact (pi_ref_pos s). apply exp_neg_pos.
Qed.

Definition pi_star_req (s : S) : R :=
  mult (inv_pos Z_align_req Z_align_pos)
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
(* Relative entropy real_eq form (key subitem 3; Id relative_entropy L16535;
   log premise-ified: carries pointwise positivity -- register 1) *)
Definition relative_entropy_req (p q : S -> R) (Hp : pos_dist p) (Hq : pos_dist q) : R :=
  sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))).
(* Alignment energy / free energy / alignment objective (Id align_energy L18849
   / align_objective L18855; log premise-ified: F_align_req carries pointwise
   positivity) *)
Definition align_energy_req (s : S) : R :=
  req_minus (opp (reward s)) (mult beta (log (pi_ref s) (pi_ref_pos s))).
Definition F_align_req (p : S -> R) (Hp : pos_dist p) : R :=
  plus (sumf (fun s => mult (p s) (align_energy_req s)))
       (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition align_objective_req (p : S -> R) (Hp : pos_dist p) : R :=
  opp (F_align_req p Hp).
Definition dpo_loss_req (p : S -> R) (Hp : pos_dist p) : R :=
  opp (align_objective_req p Hp).

(* ============ Group A: genuine proofs (proofs inside real_eq, zero bridges) ============ *)

(* Negation converse (real_eq version of Id opp_eq L19170; destruct/eq_ind unavailable,
   so a two-step route via req_opp_compat + req_double_neg) *)
Lemma req_opp_eq : forall a b : R, real_eq (opp a) (opp b) -> real_eq a b.
Proof.
  intros a b Hab.
  apply (req_trans a (opp (opp a)) b).
  - apply (req_sym (opp (opp a)) a). apply req_double_neg.
  - apply (req_trans (opp (opp a)) (opp (opp b)) b).
    + apply (req_opp_compat (opp a) (opp b) Hab).
    + apply req_double_neg.
Qed.

(* pi* pointwise positivity (isomorphic to Id pi_star_pos L18783; pure assembly of interface fields) *)
Lemma req_pi_star_pos : pos_dist pi_star_req.
Proof.
  intro s.
  unfold pi_star_req.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply mult_positive.
    + apply pi_ref_pos.
    + apply exp_neg_pos.
Qed.

(* Alignment-energy exponential identity (real_eq version of Id align_energy_exp
   L18861, ~50-line genuine proof: req_mult_minus_distr_l + inv absorption +
   req_opp_minus reassembly + req_exp_neg_opp_plus (batch 1) +
   req_exp_neg_opp_log (batch 1)) *)
Lemma req_align_energy_exp :
  forall s : S,
    real_eq (exp_neg (mult (inv_pos beta beta_pos) (align_energy_req s)))
        (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Proof.
  intro s.
  set (iv := inv_pos beta beta_pos).
  set (lg := log (pi_ref s) (pi_ref_pos s)).
  (* H1 : iv*(-r - beta*lg) == (-(iv*r)) + (-lg) *)
  assert (H1 : real_eq (mult iv (align_energy_req s))
                   (plus (opp (mult iv (reward s))) (opp lg))).
  { unfold align_energy_req, req_minus.
    apply (req_trans (mult iv (plus (opp (reward s)) (opp (mult beta lg))))
                     (plus (mult iv (opp (reward s))) (opp (mult iv (mult beta lg)))))
      .
    - exact (req_mult_minus_distr_l iv (opp (reward s)) (mult beta lg)).
    - apply (req_plus_compat (mult iv (opp (reward s))) (opp (mult iv (reward s)))
                             (opp (mult iv (mult beta lg))) (opp lg)).
      + apply req_opp_mult_l.
      + apply (req_opp_compat (mult iv (mult beta lg)) lg).
        apply (req_trans (mult iv (mult beta lg)) (mult (mult iv beta) lg) lg).
        * apply mult_assoc.
        * apply (req_trans (mult (mult iv beta) lg) (mult one lg) lg).
          -- apply (req_mult_compat (mult iv beta) one lg lg
                                   (req_trans (mult iv beta) (mult beta iv) one
                                              (mult_comm iv beta)
                                              (inv_pos_correct beta beta_pos))
                                   (req_refl lg)).
          -- apply req_mult_one_l. }
  (* H3 : iv*E == -(iv*r + lg) *)
  assert (H3 : real_eq (mult iv (align_energy_req s))
                   (opp (plus (mult iv (reward s)) lg))).
  { apply (req_trans (mult iv (align_energy_req s))
                     (plus (opp (mult iv (reward s))) (opp lg))
                     (opp (plus (mult iv (reward s)) lg))).
    - exact H1.
    - apply (req_sym (opp (plus (mult iv (reward s)) lg))
                     (plus (opp (mult iv (reward s))) (opp lg))).
      apply req_opp_plus. }
  (* H4 : e^{iv*E} == e^{-(iv*r)} * e^{-lg} (batch-1 req_exp_neg_opp_plus) *)
  assert (H4 : real_eq (exp_neg (mult iv (align_energy_req s)))
                   (mult (exp_neg (opp (mult iv (reward s)))) (exp_neg (opp lg)))).
  { apply (req_trans (exp_neg (mult iv (align_energy_req s)))
                     (exp_neg (opp (plus (mult iv (reward s)) lg)))
                     (mult (exp_neg (opp (mult iv (reward s)))) (exp_neg (opp lg)))).
    - apply exp_neg_req_compat_setoid. exact H3.
    - exact (req_exp_neg_opp_plus (mult iv (reward s)) lg). }
  
  apply (req_trans (exp_neg (mult iv (align_energy_req s)))
                   (mult (exp_neg (opp (mult iv (reward s)))) (exp_neg (opp lg)))
                   (mult (pi_ref s) (exp_neg (opp (mult iv (reward s)))))).
  - exact H4.
  - apply (req_trans (mult (exp_neg (opp (mult iv (reward s)))) (exp_neg (opp lg)))
                     (mult (exp_neg (opp (mult iv (reward s)))) (pi_ref s))
                     (mult (pi_ref s) (exp_neg (opp (mult iv (reward s)))))).
    + apply (req_mult_compat (exp_neg (opp (mult iv (reward s))))
                             (exp_neg (opp (mult iv (reward s))))
                             (exp_neg (opp lg)) (pi_ref s)
                             (req_refl (exp_neg (opp (mult iv (reward s)))))
                             (req_exp_neg_opp_log (pi_ref s) (pi_ref_pos s))).
    + apply mult_comm.
Qed.

(* Partition condition (real_eq version of Id align_partition_condition L18944; genuine
   proof: sum_ext pointwise = the symmetric form of req_align_energy_exp) *)
Lemma req_align_partition_condition :
  real_eq Z_align_req
      (sumf (fun s => exp_neg (mult (inv_pos beta beta_pos) (align_energy_req s)))).
Proof.
  exact (sum_ext (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
                 (fun s => exp_neg (mult (inv_pos beta beta_pos) (align_energy_req s)))
                 (fun s => req_sym (exp_neg (mult (inv_pos beta beta_pos) (align_energy_req s)))
                                   (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
                                   (req_align_energy_exp s))).
Qed.

(* pi* normalization (real_eq version of Id pi_star_normalized L18790; genuine proof
   isomorphic to the pilot req_boltzmann_normalized: sum_linear + inv) *)
Lemma req_pi_star_normalized : real_eq (sumf pi_star_req) one.
Proof.
  apply (req_trans (sumf (fun s => mult (inv_pos Z_align_req Z_align_pos)
                                        (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))
                   (mult (inv_pos Z_align_req Z_align_pos)
                         (sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))
                   one).
  - exact (sum_linear (inv_pos Z_align_req Z_align_pos)
                      (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
  - apply (req_trans (mult (inv_pos Z_align_req Z_align_pos)
                           (sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))
                     (mult (inv_pos Z_align_req Z_align_pos) Z_align_req)
                     one).
    + apply (req_mult_compat (inv_pos Z_align_req Z_align_pos) (inv_pos Z_align_req Z_align_pos)
                             (sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))
                             Z_align_req).
      * apply req_refl.
      * apply (req_sym Z_align_req
                       (sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))).
        apply req_refl.
    + apply (req_trans (mult (inv_pos Z_align_req Z_align_pos) Z_align_req)
                       (mult Z_align_req (inv_pos Z_align_req Z_align_pos))
                       one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.

(* Free-energy extensionality (real_eq version of Id free_energy_ext L18951; genuine
   proof: double sum_ext + req_mult_compat; the log premise travels with
   pointwise positivity -- register 1) *)
Lemma req_free_energy_align_ext :
  forall (f g : S -> R) (Hf : pos_dist f) (Hg : pos_dist g),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (F_align_req f Hf) (F_align_req g Hg).
Proof.
  intros f g Hf Hg Hfg.
  unfold F_align_req.
  apply (req_plus_compat
           (sumf (fun s => mult (f s) (align_energy_req s)))
           (sumf (fun s => mult (g s) (align_energy_req s)))
           (mult beta (sumf (fun s => mult (f s) (log (f s) (Hf s)))))
           (mult beta (sumf (fun s => mult (g s) (log (g s) (Hg s)))))).
  - apply (sum_ext (fun s => mult (f s) (align_energy_req s))
                   (fun s => mult (g s) (align_energy_req s))).
    intro s.
    apply (req_mult_compat (f s) (g s) (align_energy_req s) (align_energy_req s)
                           (Hfg s) (req_refl (align_energy_req s))).
  - apply (req_mult_compat beta beta
                           (sumf (fun s => mult (f s) (log (f s) (Hf s))))
                           (sumf (fun s => mult (g s) (log (g s) (Hg s))))).
    + apply req_refl.
    + apply (sum_ext (fun s => mult (f s) (log (f s) (Hf s)))
                     (fun s => mult (g s) (log (g s) (Hg s)))).
      intro s.
      apply (req_mult_compat (f s) (g s) (log (f s) (Hf s)) (log (g s) (Hg s))
                             (Hfg s) (log_req_compat (f s) (g s) (Hf s) (Hg s) (Hfg s))).
Qed.

(* ============ Group B: RLHF/DPO core (T2(1) FEP bridges + genuine-proof assembly) ============ *)
(* real_eq-signature bridges for the FEP real_eq trio (carried by the real_eq counterparts
   of Id min_free_energy_is_boltzmann / free_energy_min_unique; demoted to
   dependents once the batch-2 UpReqFreeEnergy result lands.
   Counterpart-simplification note: on the Id side align_boltzmann_is_pi_star
   identifies boltzmann_dist pointwise with pi_star, so the real_eq-side bridge
   takes pi_star_req directly as the minimizer carrier -- equivalent and
   duplication-free -- register 3.) *)
Hypothesis bridge_min_free_energy :
  forall (p : S -> R) (Hn : norm_one p) (Hp : pos_dist p),
    real_le (F_align_req pi_star_req req_pi_star_pos) (F_align_req p Hp).
Hypothesis bridge_free_energy_min_unique :
  forall (p : S -> R) (Hn : norm_one p) (Hp : pos_dist p),
    real_eq (F_align_req p Hp) (F_align_req pi_star_req req_pi_star_pos) ->
    forall s : S, real_eq (p s) (pi_star_req s).

(* RLHF optimality (real_eq version of Id rlhf_optimal L19049; genuine-proof assembly:
   bridge + req_free_energy_align_ext (the pi* minimizer carrier needs no ext)
   + opp_le_compat) *)
Theorem req_rlhf_optimal :
  forall (p : S -> R) (Hn : norm_one p) (Hp : pos_dist p),
    real_le (align_objective_req p Hp) (align_objective_req pi_star_req req_pi_star_pos).
Proof.
  intros p Hn Hp. unfold align_objective_req.
  exact (opp_le_compat (F_align_req pi_star_req req_pi_star_pos) (F_align_req p Hp)
                       (bridge_min_free_energy p Hn Hp)).
Qed.

(* RLHF optimal-policy uniqueness (real_eq version of Id rlhf_optimal_unique
   L19180; req_opp_eq genuine proof + uniqueness-bridge assembly) *)
Theorem req_rlhf_optimal_unique :
  forall (p : S -> R) (Hn : norm_one p) (Hp : pos_dist p),
    real_eq (align_objective_req p Hp) (align_objective_req pi_star_req req_pi_star_pos) ->
    forall s : S, real_eq (p s) (pi_star_req s).
Proof.
  intros p Hn Hp Hj.
  exact (bridge_free_energy_min_unique p Hn Hp
           (req_opp_eq (F_align_req p Hp) (F_align_req pi_star_req req_pi_star_pos) Hj)).
Qed.

(* DPO optimality (real_eq version of Id dpo_optimal L19112; dpo_loss = -J genuine-proof assembly) *)
Theorem req_dpo_optimal :
  forall (p : S -> R) (Hn : norm_one p) (Hp : pos_dist p),
    real_le (dpo_loss_req pi_star_req req_pi_star_pos) (dpo_loss_req p Hp).
Proof.
  intros p Hn Hp. unfold dpo_loss_req.
  exact (opp_le_compat (align_objective_req p Hp) (align_objective_req pi_star_req req_pi_star_pos)
                       (req_rlhf_optimal p Hn Hp)).
Qed.

(* ============ Group C: policy-iteration main chain (real_eq-ified from Id L21237-23272) ============ *)
(* Section arguments (counterparts of Id L21238-21241; sum_pos already carries
   the Id Variable sum_over_S_pos @L21245 counterpart at the section head) *)
Variable eta : R.
Variable eta_pos : real_lt zero eta.
Variable eta_le_one : real_le eta one.

(* Definition family real_eq-ified (same shapes as Id advantage_aug/Z_rel/energy_t/
   pi_next; log premise-ified: carriers carry pointwise-positivity parameters --
   register 1) *)
Definition advantage_aug_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=
  req_minus (reward s)
            (mult beta (req_minus (log (pi_t s) (Hpi_t s)) (log (pi_ref s) (pi_ref_pos s)))).
Definition Z_rel_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) : R :=
  sumf (fun s => mult (pi_t s)
                      (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                          (advantage_aug_req pi_t Hpi_t s))))).
Definition energy_t_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=
  req_minus (opp (mult eta (advantage_aug_req pi_t Hpi_t s)))
            (mult beta (log (pi_t s) (Hpi_t s))).

(* Z_rel positivity (real_eq version of Id Z_rel_pos L21269; genuine proof: sum_pos + mult_positive) *)
Lemma req_Z_rel_pos :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t), real_lt zero (Z_rel_req pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t.
  unfold Z_rel_req.
  apply sum_pos.
  intro s.
  apply mult_positive.
  - apply Hpi_t.
  - apply exp_neg_pos.
Qed.

Definition pi_next_req (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (s : S) : R :=
  mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
       (mult (pi_t s)
             (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                 (advantage_aug_req pi_t Hpi_t s))))).

(* pi_next pointwise positivity (real_eq version of Id pi_next_pos L21789; genuine proof) *)
Lemma req_pi_next_pos :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t), pos_dist (pi_next_req pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t s.
  unfold pi_next_req.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply mult_positive.
    + apply Hpi_t.
    + apply exp_neg_pos.
Qed.

(* pi_next normalization (real_eq version of Id pi_next_normalized L21401; genuine
   proof: sum_linear + conversion on the Z_rel definition body + inv) *)
Lemma req_pi_next_normalized :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t),
    real_eq (sumf (pi_next_req pi_t Hpi_t)) one.
Proof.
  intros pi_t Hpi_t.
  apply (req_trans (sumf (pi_next_req pi_t Hpi_t))
                   (mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                         (sumf (fun s => mult (pi_t s)
                                              (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                                  (advantage_aug_req pi_t Hpi_t s)))))))
                   one).
  - exact (sum_linear (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                      (fun s => mult (pi_t s)
                                     (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                         (advantage_aug_req pi_t Hpi_t s)))))).
  - apply (req_trans (mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                           (sumf (fun s => mult (pi_t s)
                                                (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                                    (advantage_aug_req pi_t Hpi_t s)))))))
                     (mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                           (Z_rel_req pi_t Hpi_t))
                     one).
    + apply (req_mult_compat (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                             (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                             (sumf (fun s => mult (pi_t s)
                                                  (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                                      (advantage_aug_req pi_t Hpi_t s))))))
                             (Z_rel_req pi_t Hpi_t)).
      * apply req_refl.
      * exact (req_sym (Z_rel_req pi_t Hpi_t)
                       (sumf (fun s => mult (pi_t s)
                                            (exp_neg (opp (mult (mult eta (inv_pos beta beta_pos))
                                                                (advantage_aug_req pi_t Hpi_t s))))))
                       (req_refl (Z_rel_req pi_t Hpi_t))).
    + apply (req_trans (mult (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t))
                             (Z_rel_req pi_t Hpi_t))
                       (mult (Z_rel_req pi_t Hpi_t) (inv_pos (Z_rel_req pi_t Hpi_t) (req_Z_rel_pos pi_t Hpi_t)))
                       one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.

(* ---- B-class bridges (T2(1) premises positions kept, isomorphic item-by-item
   to the Id versions; register 3) ----
   req_step_kl_eta_bound <- Id Variable @L23114 (B-class; Real seeds
   real_step_kl_eta_bound_eps@L113142 / real_interp_Z_le_one_eps@L112890
   live at the root; instance resolution deferred to the real_eq-sum instance batch).
   req_backward_kl_identity <- Id theorem policy_iter_backward_kl_step @L22686
   (deep-chain t13 bridge; real_eq re-proof pending batch 3b -- see the end-of-file
   pending list).
   req_policy_improvement_mono <- Id @L22065 (deep chain t12, likewise pending). *)
Hypothesis req_step_kl_eta_bound :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t),
    real_le (relative_entropy_req pi_t (pi_next_req pi_t Hpi_t) Hpi_t (req_pi_next_pos pi_t Hpi_t))
       (mult eta (relative_entropy_req pi_t pi_star_req Hpi_t req_pi_star_pos)).
Hypothesis req_backward_kl_identity :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    real_eq (relative_entropy_req pi_star_req (pi_next_req pi_t Hpi_t)
             req_pi_star_pos (req_pi_next_pos pi_t Hpi_t))
        (plus (mult (req_minus one eta)
                    (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t))
              (plus (opp (mult eta (relative_entropy_req pi_t pi_star_req Hpi_t req_pi_star_pos)))
                    (relative_entropy_req pi_t (pi_next_req pi_t Hpi_t)
                         Hpi_t (req_pi_next_pos pi_t Hpi_t)))).

(* ---- Order-algebra auxiliaries (real_eq versions of Id
        plus_opp_le_zero/plusA_opp_cancel_le L23119/23130; genuine proofs:
        the real_le field + real_eq bridges) ---- *)
Lemma req_plus_opp_le_zero : forall B C : R, real_le C B -> real_le (plus (opp B) C) zero.
Proof.
  intros B C HCB.
  exact (le_id_r (plus (opp B) C) (plus (opp B) B) zero
                 (req_trans (plus (opp B) B) (plus B (opp B)) zero
                            (plus_comm (opp B) B) (plus_opp B))
                 (le_plus_compat (opp B) (opp B) C B (le_refl (opp B)) HCB)).
Qed.

Lemma req_plusA_opp_cancel_le :
  forall A B C : R, real_le C B -> real_le (plus A (plus (opp B) C)) A.
Proof.
  intros A B C HCB.
  exact (le_id_r (plus A (plus (opp B) C)) (plus A zero) A (plus_zero A)
                 (le_plus_compat A A (plus (opp B) C) zero (le_refl A)
                                 (req_plus_opp_le_zero B C HCB))).
Qed.

(* Single-step genuine geometric contraction (real_eq version of Id
   policy_iter_kl_geom_step L23146; three exact KL identities + the step bridge
   + order-algebra real_eq assembly -- main item) *)
Theorem req_policy_iter_kl_geom_step :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    real_le (relative_entropy_req pi_star_req (pi_next_req pi_t Hpi_t)
            req_pi_star_pos (req_pi_next_pos pi_t Hpi_t))
       (mult (req_minus one eta)
             (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t)).
Proof.
  intros pi_t Hpi_t Hnorm.
  apply (le_id_l
    (relative_entropy_req pi_star_req (pi_next_req pi_t Hpi_t)
         req_pi_star_pos (req_pi_next_pos pi_t Hpi_t))
    (plus (mult (req_minus one eta)
                (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t))
          (plus (opp (mult eta (relative_entropy_req pi_t pi_star_req Hpi_t req_pi_star_pos)))
                (relative_entropy_req pi_t (pi_next_req pi_t Hpi_t)
                     Hpi_t (req_pi_next_pos pi_t Hpi_t))))
    (mult (req_minus one eta)
          (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t))).
  - exact (req_backward_kl_identity pi_t Hpi_t Hnorm).
  - exact (req_plusA_opp_cancel_le
             (mult (req_minus one eta)
                   (relative_entropy_req pi_star_req pi_t req_pi_star_pos Hpi_t))
             (mult eta (relative_entropy_req pi_t pi_star_req Hpi_t req_pi_star_pos))
             (relative_entropy_req pi_t (pi_next_req pi_t Hpi_t)
                  Hpi_t (req_pi_next_pos pi_t Hpi_t))
             (req_step_kl_eta_bound pi_t Hpi_t)).
Qed.

(* Iteration Fixpoint real_eq-ified (isomorphic to Id policy_iterate L22879:
   distribution + positivity packaged as sigT, extractable; nat induction
   rebuilt at Set level -- register 4) *)
Fixpoint policy_iterate_req (t : nat) (pi : S -> R) (Hpi : pos_dist pi) :
  { pi' : S -> R & pos_dist pi' } :=
  match t with
  | 0%nat => existT _ pi Hpi
  | Datatypes.S m =>
      let p := policy_iterate_req m pi Hpi in
      existT _ (pi_next_req (projT1 p) (projT2 p)) (req_pi_next_pos (projT1 p) (projT2 p))
  end.

(* R-layer power real_eq-ified (nat induction, same shape as Id r_pow L14071; register 4) *)
Fixpoint req_r_pow (x : R) (n : nat) : R :=
  match n with
  | 0%nat => one
  | Datatypes.S m => mult x (req_r_pow x m)
  end.

(* Iteration preserves normalization (real_eq version of Id policy_iter_norm L22890; genuine proof by induction) *)
Lemma req_policy_iter_norm :
  forall (t : nat) (pi : S -> R) (Hpi : pos_dist pi),
    norm_one pi -> norm_one (projT1 (policy_iterate_req t pi Hpi)).
Proof.
  intros t pi Hpi Hnorm.
  induction t as [| m IH].
  - exact Hnorm.
  - exact (req_pi_next_normalized (projT1 (policy_iterate_req m pi Hpi))
                                  (projT2 (policy_iterate_req m pi Hpi))).
Qed.

(* Iterated geometric upper bound (real_eq version of Id policy_iter_kl_geom_iter
   L23181; (1-eta)^t genuine geometric rate, real_eq-dependent version -- genuine
   proof by induction) *)
Theorem req_policy_iter_kl_geom_iter :
  forall (t : nat) (pi : S -> R) (Hpi : pos_dist pi) (Hnorm : norm_one pi),
    real_le (relative_entropy_req pi_star_req (projT1 (policy_iterate_req t pi Hpi))
            req_pi_star_pos (projT2 (policy_iterate_req t pi Hpi)))
       (mult (req_r_pow (req_minus one eta) t)
             (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)).
Proof.
  intros t pi Hpi Hnorm.
  induction t as [| m IH].
  - (* t = 0: KL <= 1*KL *)
    apply (le_id_r
      (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)
      (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)
      (mult one (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))).
    + exact (req_sym (mult one (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))
                     (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)
                     (req_mult_one_l (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))).
    + apply le_refl.
  - (* t = S m: single-step contraction + induction + kappa^t reassociation (real_eq chain) *)
    assert (H1 : real_le (relative_entropy_req pi_star_req
                         (pi_next_req (projT1 (policy_iterate_req m pi Hpi))
                                      (projT2 (policy_iterate_req m pi Hpi)))
                         req_pi_star_pos
                         (req_pi_next_pos (projT1 (policy_iterate_req m pi Hpi))
                                          (projT2 (policy_iterate_req m pi Hpi))))
                    (mult (req_minus one eta)
                          (relative_entropy_req pi_star_req
                               (projT1 (policy_iterate_req m pi Hpi))
                               req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi))))).
    { exact (req_policy_iter_kl_geom_step (projT1 (policy_iterate_req m pi Hpi))
                                          (projT2 (policy_iterate_req m pi Hpi))
                                          (req_policy_iter_norm m pi Hpi Hnorm)). }
    assert (Hk : real_le zero (req_minus one eta)).
    { exact (req_le_minus_nonneg eta one eta_le_one). }
    assert (H4 : real_le (mult (req_minus one eta)
                          (relative_entropy_req pi_star_req
                               (projT1 (policy_iterate_req m pi Hpi))
                               req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi))))
                    (mult (req_minus one eta)
                          (mult (req_r_pow (req_minus one eta) m)
                                (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))).
    { apply (le_id_l
        (mult (req_minus one eta)
              (relative_entropy_req pi_star_req (projT1 (policy_iterate_req m pi Hpi))
                   req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi))))
        (mult (relative_entropy_req pi_star_req (projT1 (policy_iterate_req m pi Hpi))
                    req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi)))
              (req_minus one eta))
        (mult (req_minus one eta)
              (mult (req_r_pow (req_minus one eta) m)
                    (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))).
      - apply mult_comm.
      - apply (le_id_r
          (mult (relative_entropy_req pi_star_req (projT1 (policy_iterate_req m pi Hpi))
                     req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi)))
                (req_minus one eta))
          (mult (mult (req_r_pow (req_minus one eta) m)
                      (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))
                (req_minus one eta))
          (mult (req_minus one eta)
                (mult (req_r_pow (req_minus one eta) m)
                      (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))).
        + apply mult_comm.
        + apply (le_mult_compat_weak
            (relative_entropy_req pi_star_req (projT1 (policy_iterate_req m pi Hpi))
                 req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi)))
            (mult (req_r_pow (req_minus one eta) m)
                  (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))
            (req_minus one eta) Hk).
          exact IH. }
    apply (le_trans
      (relative_entropy_req pi_star_req (projT1 (policy_iterate_req (Datatypes.S m) pi Hpi))
           req_pi_star_pos (projT2 (policy_iterate_req (Datatypes.S m) pi Hpi)))
      (mult (req_minus one eta)
            (mult (req_r_pow (req_minus one eta) m)
                  (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))
      (mult (mult (req_minus one eta) (req_r_pow (req_minus one eta) m))
            (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))).
    + exact (le_trans
        (relative_entropy_req pi_star_req
             (projT1 (policy_iterate_req (Datatypes.S m) pi Hpi))
             req_pi_star_pos (projT2 (policy_iterate_req (Datatypes.S m) pi Hpi)))
        (mult (req_minus one eta)
              (relative_entropy_req pi_star_req (projT1 (policy_iterate_req m pi Hpi))
                   req_pi_star_pos (projT2 (policy_iterate_req m pi Hpi))))
        (mult (req_minus one eta)
              (mult (req_r_pow (req_minus one eta) m)
                    (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))
        H1 H4).
    + apply (le_id_r
        (mult (req_minus one eta)
              (mult (req_r_pow (req_minus one eta) m)
                    (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))
        (mult (req_minus one eta)
              (mult (req_r_pow (req_minus one eta) m)
                    (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)))
        (mult (mult (req_minus one eta) (req_r_pow (req_minus one eta) m))
              (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi))).
      * apply (mult_assoc (req_minus one eta) (req_r_pow (req_minus one eta) m)
                          (relative_entropy_req pi_star_req pi req_pi_star_pos Hpi)).
      * apply le_refl.
Qed.

(* ---- DPO loss along the policy-improvement orbit (real_eq versions of Id L23244/23256) ---- *)
Hypothesis req_policy_improvement_mono :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    real_le (align_objective_req pi_t Hpi_t)
       (align_objective_req (pi_next_req pi_t Hpi_t) (req_pi_next_pos pi_t Hpi_t)).

(* Single step: dpo_loss(pi_next) <= dpo_loss(pi_t) (genuine-proof assembly) *)
Theorem req_dpo_loss_iter_step_le :
  forall (pi_t : S -> R) (Hpi_t : pos_dist pi_t) (Hnorm : norm_one pi_t),
    real_le (dpo_loss_req (pi_next_req pi_t Hpi_t) (req_pi_next_pos pi_t Hpi_t))
       (dpo_loss_req pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t Hnorm.
  unfold dpo_loss_req.
  exact (opp_le_compat (align_objective_req pi_t Hpi_t)
                       (align_objective_req (pi_next_req pi_t Hpi_t) (req_pi_next_pos pi_t Hpi_t))
                       (req_policy_improvement_mono pi_t Hpi_t Hnorm)).
Qed.

(* Iteration: dpo_loss monotonically non-increasing along the policy_iterate_req orbit (genuine-proof assembly) *)
Theorem req_dpo_loss_iter_mono :
  forall (t : nat) (pi : S -> R) (Hpi : pos_dist pi) (Hnorm : norm_one pi),
    real_le (dpo_loss_req (projT1 (policy_iterate_req (Datatypes.S t) pi Hpi))
                     (projT2 (policy_iterate_req (Datatypes.S t) pi Hpi)))
       (dpo_loss_req (projT1 (policy_iterate_req t pi Hpi))
                     (projT2 (policy_iterate_req t pi Hpi))).
Proof.
  intros t pi Hpi Hnorm.
  apply (le_id_l
    (dpo_loss_req (projT1 (policy_iterate_req (Datatypes.S t) pi Hpi))
                  (projT2 (policy_iterate_req (Datatypes.S t) pi Hpi)))
    (dpo_loss_req (pi_next_req (projT1 (policy_iterate_req t pi Hpi))
                               (projT2 (policy_iterate_req t pi Hpi)))
                  (req_pi_next_pos (projT1 (policy_iterate_req t pi Hpi))
                                   (projT2 (policy_iterate_req t pi Hpi))))
    (dpo_loss_req (projT1 (policy_iterate_req t pi Hpi))
                  (projT2 (policy_iterate_req t pi Hpi)))).
  - apply req_refl.
  - exact (req_dpo_loss_iter_step_le (projT1 (policy_iterate_req t pi Hpi))
                                     (projT2 (policy_iterate_req t pi Hpi))
                                     (req_policy_iter_norm t pi Hpi Hnorm)).
Qed.

(* APPEND-POINT-B *)
End ReqAlignCore.

(* ============================================================ *)
(* ReqKLProjection: audit = KL projection (real_eq-ified from the Id original section L95420-95604) *)
(*   Signature difference (register 1): the real_eq log premise-ification makes the    *)
(*   log(0) term on the fail branch unstatable -- projected-KL is restated          *)



(*   in pointwise closed form; pass branch fully aligned (positive_dist + fail zero + normalization + HlogZ).          *)
(* ============================================================ *)
Section ReqKLProjection.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    real_eq (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    real_eq (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, real_le (f s) (g s)) -> real_le (sumf f) (sumf g).
Hypothesis log_req_compat :
  forall (x y : R) (Hx : real_lt zero x) (Hy : real_lt zero y),
    real_eq x y -> real_eq (log x Hx) (log y Hy).

Variable post_aud : S -> bool.
Variable p : S -> R.
Variable Hp_norm : real_eq (sumf p) one.
Variable Hp_pos : forall s : S, real_lt zero (p s).

(* Pass-set mass and projected distribution (same shapes as Id Z_aud/projected_distribution) *)
Definition Z_aud_req : R := sumf (fun s => if post_aud s then p s else zero).
Variable HZ : real_lt zero Z_aud_req.
Definition projected_distribution_req (s : S) : R :=
  if post_aud s then mult (p s) (inv_pos Z_aud_req HZ) else zero.


Definition kl_proj_closed (q : S -> R) (Hq : forall s : S, real_lt zero (q s)) (s : S) : R :=
  mult (q s)
       (req_minus (log (q s) (Hq s))
                  (plus (log (p s) (Hp_pos s))
                        (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).

(* Local auxiliary: req_minus left-argument compatibility (req_minus unfolds delta-transparently to plus compatibility) *)
Lemma rkl_minus_compat_l :
  forall a b c : R, real_eq a b -> real_eq (req_minus a c) (req_minus b c).
Proof.
  intros a b c H. unfold req_minus.
  exact (req_plus_compat a b (opp c) (opp c) H (req_refl (opp c))).
Qed.

(* Local auxiliary: opp zero == zero *)
Lemma rkl_opp_zero : real_eq (opp zero) zero.
Proof.
  exact (req_trans (opp zero) (plus zero (opp zero)) zero
                   (req_sym (plus zero (opp zero)) (opp zero) (req_plus_zero_l (opp zero)))
                   (plus_opp zero)).
Qed.

(* Projected distribution pass-branch shape (pass-branch counterpart of Id projected_pt) *)
Lemma req_projected_pass :
  forall (s : S) (E : post_aud s = true),
    real_eq (projected_distribution_req s) (mult (p s) (inv_pos Z_aud_req HZ)).
Proof.
  intros s E.
  destruct (post_aud s) eqn:Es.
  - unfold projected_distribution_req. rewrite Es. apply req_refl.
  - discriminate E.
Qed.

(* Projected distribution pass-branch positivity (needed by the real_eq log premise;
   the Id system's plain global positivity is only statable on the pass branch
   in the real_eq world -- signature-difference register 1) *)
Lemma req_projected_pass_pos :
  forall (s : S) (E : post_aud s = true), real_lt zero (projected_distribution_req s).
Proof.
  intros s E.
  destruct (post_aud s) eqn:Es.
  - unfold projected_distribution_req. rewrite Es.
    apply mult_positive.
    + apply Hp_pos.
    + apply inv_pos_pos.
  - discriminate E.
Qed.

(* real_eq version of Id if_p_le_p L95450 (bool branches + lt_le_iff; genuine proof) *)
Lemma req_if_p_le_p : forall s : S, real_le (if post_aud s then p s else zero) (p s).
Proof.
  intro s. destruct (post_aud s).
  - apply le_refl.
  - apply (lt_le_iff zero (p s)). left. apply Hp_pos.
Qed.

(* real_eq version of Id Z_aud_le_one L95459 (sum_le lifting; genuine proof) *)
Lemma req_Z_aud_le_one : real_le Z_aud_req (sumf p).
Proof.
  unfold Z_aud_req.
  exact (sum_le (fun s => if post_aud s then p s else zero) p
                req_if_p_le_p).
Qed.

(* real_eq version of Id projected_pt L95465 (genuine proof: comm / mult_zero branches) *)
Lemma req_projected_pt :
  forall s : S,
    real_eq (projected_distribution_req s)
        (mult (inv_pos Z_aud_req HZ) (if post_aud s then p s else zero)).
Proof.
  intro s. unfold projected_distribution_req. destruct (post_aud s).
  - apply mult_comm.
  - exact (req_sym (mult (inv_pos Z_aud_req HZ) zero) zero
                   (mult_zero (inv_pos Z_aud_req HZ))).
Qed.

(* real_eq version of Id projected_normalized L95476 (genuine proof: sum_ext + linear + inv) *)
Lemma req_projected_normalized : real_eq (sumf projected_distribution_req) one.
Proof.
  apply (req_trans (sumf projected_distribution_req)
                   (sumf (fun s => mult (inv_pos Z_aud_req HZ) (if post_aud s then p s else zero)))
                   one).
  - apply (sum_ext (fun s => projected_distribution_req s)
                   (fun s => mult (inv_pos Z_aud_req HZ) (if post_aud s then p s else zero))).
    apply req_projected_pt.
  - apply (req_trans (sumf (fun s => mult (inv_pos Z_aud_req HZ) (if post_aud s then p s else zero)))
                     (mult (inv_pos Z_aud_req HZ) (sumf (fun s => if post_aud s then p s else zero)))
                     one).
    + exact (sum_linear (inv_pos Z_aud_req HZ)
                        (fun s => if post_aud s then p s else zero)).
    + apply (req_trans (mult (inv_pos Z_aud_req HZ) (sumf (fun s => if post_aud s then p s else zero)))
                       (mult (inv_pos Z_aud_req HZ) Z_aud_req)
                       one).
      * apply (req_mult_compat (inv_pos Z_aud_req HZ) (inv_pos Z_aud_req HZ)
                               (sumf (fun s => if post_aud s then p s else zero))
                               Z_aud_req).
        -- apply req_refl.
        -- exact (req_sym Z_aud_req (sumf (fun s => if post_aud s then p s else zero))
                                 (req_refl Z_aud_req)).
      * apply (req_trans (mult (inv_pos Z_aud_req HZ) Z_aud_req)
                         (mult Z_aud_req (inv_pos Z_aud_req HZ))
                         one).
        -- apply mult_comm.
        -- apply inv_pos_correct.
Qed.

(* real_eq version of Id kl_minus_split L95498: a-c == (a-b)+(b-c) (req_minus carrier; genuine proof) *)
Lemma req_kl_minus_split :
  forall a b c : R, real_eq (req_minus a c) (plus (req_minus a b) (req_minus b c)).
Proof.
  intros a b c. unfold req_minus.
  apply (req_trans (plus a (opp c))
                   (plus a (plus (opp b) (plus b (opp c))))
                   (plus (plus a (opp b)) (plus b (opp c)))).
  - apply (req_plus_compat a a (opp c) (plus (opp b) (plus b (opp c)))
                           (req_refl a)).
    apply (req_trans (opp c) (plus (plus (opp b) b) (opp c))
                     (plus (opp b) (plus b (opp c)))).
    + apply (req_trans (opp c) (plus zero (opp c))
                       (plus (plus (opp b) b) (opp c))).
      * apply (req_sym (plus zero (opp c)) (opp c)). apply req_plus_zero_l.
      * apply (req_plus_compat zero (plus (opp b) b) (opp c) (opp c)
                               (req_sym (plus (opp b) b) zero (req_plus_opp_l b))
                               (req_refl (opp c))).
    + apply (req_sym (plus (opp b) (plus b (opp c)))
                     (plus (plus (opp b) b) (opp c))
                     (plus_assoc (opp b) b (opp c))).
  - apply plus_assoc.
Qed.

(* real_eq version of Id minus_plus_opp L95539: (x + (-L)) - x == -L (genuine proof) *)
Lemma req_minus_plus_opp : forall x L : R, real_eq (req_minus (plus x (opp L)) x) (opp L).
Proof.
  intros x L. unfold req_minus.
  apply (req_trans (plus (plus x (opp L)) (opp x))
                   (plus x (plus (opp L) (opp x)))
                   (opp L)).
  - apply (req_sym (plus x (plus (opp L) (opp x)))
                   (plus (plus x (opp L)) (opp x))).
    apply plus_assoc.
  - apply (req_trans (plus x (plus (opp L) (opp x)))
                     (plus x (plus (opp x) (opp L)))
                     (opp L)).
    + apply (req_plus_compat x x (plus (opp L) (opp x)) (plus (opp x) (opp L))
                             (req_refl x) (plus_comm (opp L) (opp x))).
    + apply (req_trans (plus x (plus (opp x) (opp L)))
                       (plus (plus x (opp x)) (opp L))
                       (opp L)).
      * apply plus_assoc.
      * apply (req_trans (plus (plus x (opp x)) (opp L))
                         (plus zero (opp L))
                         (opp L)).
        -- apply (req_plus_compat (plus x (opp x)) zero (opp L) (opp L)
                                  (plus_opp x) (req_refl (opp L))).
        -- apply (req_trans (plus zero (opp L)) (plus (opp L) zero) (opp L)
                            (plus_comm zero (opp L)) (plus_zero (opp L))).
Qed.

(* log(1/x) == -log x (rebuilt in this section, same pattern as UpReqAlgebra
   ReqLogBridge req_log_inv_one_inv -- depends on this section's
   log_req_compat bridge) *)
Lemma rkl_log_inv_one_inv :
  forall (x : R) (Hx : real_lt zero x),
    real_eq (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  assert (Hprod : real_eq (mult (inv_pos x Hx) x) one).
  { exact (req_trans (mult (inv_pos x Hx) x) (mult x (inv_pos x Hx)) one
                     (mult_comm (inv_pos x Hx) x) (inv_pos_correct x Hx)). }
  assert (Hl1 : real_eq (log (mult (inv_pos x Hx) x)
                         (mult_positive (inv_pos x Hx) x (inv_pos_pos x Hx) Hx))
                    zero).
  { apply (req_trans (log (mult (inv_pos x Hx) x)
                          (mult_positive (inv_pos x Hx) x (inv_pos_pos x Hx) Hx))
                     (log one one_pos) zero).
    - apply log_req_compat. exact Hprod.
    - exact (log_one one_pos). }
  apply (req_add_cancel_l (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx)
                          (opp (log x Hx))).
  apply (req_trans (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx))
                   zero
                   (plus (opp (log x Hx)) (log x Hx))).
  - apply (req_trans (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx))
                     (log (mult (inv_pos x Hx) x)
                          (mult_positive (inv_pos x Hx) x (inv_pos_pos x Hx) Hx))
                     zero).
    + apply (req_sym (log (mult (inv_pos x Hx) x)
                          (mult_positive (inv_pos x Hx) x (inv_pos_pos x Hx) Hx))
                     (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx))).
      apply log_mult.
    + exact Hl1.
  - apply (req_sym (plus (opp (log x Hx)) (log x Hx)) zero).
    apply (req_trans (plus (opp (log x Hx)) (log x Hx))
                     (plus (log x Hx) (opp (log x Hx))) zero).
    + apply plus_comm.
    + apply plus_opp.
Qed.

(* Pointwise projected-log decomposition (real_eq counterpart of Id
   kl_pointwise_split L95515): on the pass branch log pd == log p + log(1/Z)
   (genuine proof: pass shape + log bridge + log_mult) *)
Lemma req_log_proj_pass :
  forall (s : S) (E : post_aud s = true),
    real_eq (log (projected_distribution_req s) (req_projected_pass_pos s E))
        (plus (log (p s) (Hp_pos s))
              (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))).
Proof.
  intros s E.
  apply (req_trans (log (projected_distribution_req s) (req_projected_pass_pos s E))
                   (log (mult (p s) (inv_pos Z_aud_req HZ))
                        (mult_positive (p s) (inv_pos Z_aud_req HZ) (Hp_pos s)
                                                       (inv_pos_pos Z_aud_req HZ)))
                   (plus (log (p s) (Hp_pos s))
                         (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).
  - apply log_req_compat.
    exact (req_projected_pass s E).
  - exact (log_mult (p s) (inv_pos Z_aud_req HZ) (Hp_pos s) (inv_pos_pos Z_aud_req HZ)).
Qed.

(* Pointwise KL closed-form decomposition (pointwise kernel of Id
   kl_pointwise_split/kl_sum_split; genuine proof: req_kl_minus_split +
   req_minus_plus_cancel_r + distrib) *)
Lemma req_kl_closed_pt :
  forall (q : S -> R) (Hq : forall s : S, real_lt zero (q s)) (s : S),
    real_eq (mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))
        (plus (kl_proj_closed q Hq s)
              (mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).
Proof.
  intros q Hq s.
  assert (Hcancel : real_eq (req_minus (plus (log (p s) (Hp_pos s))
                                         (log (inv_pos Z_aud_req HZ)
                                              (inv_pos_pos Z_aud_req HZ)))
                                   (log (p s) (Hp_pos s)))
                        (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))
    by exact (req_minus_plus_cancel_r (log (p s) (Hp_pos s))
                                      (log (inv_pos Z_aud_req HZ)
                                           (inv_pos_pos Z_aud_req HZ))).
  assert (Hinner : real_eq (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))
                       (plus (req_minus (log (q s) (Hq s))
                                        (plus (log (p s) (Hp_pos s))
                                              (log (inv_pos Z_aud_req HZ)
                                                   (inv_pos_pos Z_aud_req HZ))))
                             (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).
  { apply (req_trans (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))
                     (plus (req_minus (log (q s) (Hq s))
                                      (plus (log (p s) (Hp_pos s))
                                            (log (inv_pos Z_aud_req HZ)
                                                 (inv_pos_pos Z_aud_req HZ))))
                           (req_minus (plus (log (p s) (Hp_pos s))
                                            (log (inv_pos Z_aud_req HZ)
                                                 (inv_pos_pos Z_aud_req HZ)))
                                      (log (p s) (Hp_pos s))))
                     (plus (req_minus (log (q s) (Hq s))
                                      (plus (log (p s) (Hp_pos s))
                                            (log (inv_pos Z_aud_req HZ)
                                                 (inv_pos_pos Z_aud_req HZ))))
                           (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).
    - exact (req_kl_minus_split (log (q s) (Hq s))
                                (plus (log (p s) (Hp_pos s))
                                      (log (inv_pos Z_aud_req HZ)
                                           (inv_pos_pos Z_aud_req HZ)))
                                (log (p s) (Hp_pos s))).
    - exact (req_plus_compat
               (req_minus (log (q s) (Hq s))
                          (plus (log (p s) (Hp_pos s))
                                (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))
               (req_minus (log (q s) (Hq s))
                          (plus (log (p s) (Hp_pos s))
                                (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))
               (req_minus (plus (log (p s) (Hp_pos s))
                                (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))
                          (log (p s) (Hp_pos s)))
               (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))
               (req_refl _)
               Hcancel). }
  apply (req_trans (mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))
                   (mult (q s)
                         (plus (req_minus (log (q s) (Hq s))
                                          (plus (log (p s) (Hp_pos s))
                                                (log (inv_pos Z_aud_req HZ)
                                                     (inv_pos_pos Z_aud_req HZ))))
                               (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))
                   (plus (mult (q s)
                               (req_minus (log (q s) (Hq s))
                                          (plus (log (p s) (Hp_pos s))
                                                (log (inv_pos Z_aud_req HZ)
                                                     (inv_pos_pos Z_aud_req HZ)))))
                         (mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))).
  - apply (req_mult_compat (q s) (q s)
          (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))
          (plus (req_minus (log (q s) (Hq s))
                           (plus (log (p s) (Hp_pos s))
                                 (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))
                (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))
          (req_refl (q s))
          Hinner).
  - exact (distrib (q s)
                   (req_minus (log (q s) (Hq s))
                              (plus (log (p s) (Hp_pos s))
                                    (log (inv_pos Z_aud_req HZ)
                                         (inv_pos_pos Z_aud_req HZ))))
                   (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))).
Qed.

(* Sum decomposition (real_eq version of Id kl_sum_split L95527; genuine proof: sum_ext + sum_add + linear) *)
Lemma req_kl_closed_sum_split :
  forall (q : S -> R) (Hq : forall s : S, real_lt zero (q s)),
    real_eq (sumf (fun s => mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))))
        (plus (sumf (fun s => kl_proj_closed q Hq s))
              (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))).
Proof.
  intros q Hq.
  apply (req_trans
    (sumf (fun s => mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))))
    (sumf (fun s => plus (kl_proj_closed q Hq s) (mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))))
    (plus (sumf (fun s => kl_proj_closed q Hq s)) (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q)))).
  - apply (sum_ext
      (fun s => mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))
      (fun s => plus (kl_proj_closed q Hq s) (mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))).
    intro s. exact (req_kl_closed_pt q Hq s).
  - apply (req_trans
      (sumf (fun s => plus (kl_proj_closed q Hq s) (mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))))
      (plus (sumf (fun s => kl_proj_closed q Hq s))
            (sumf (fun s => mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))))
      (plus (sumf (fun s => kl_proj_closed q Hq s)) (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q)))).
    + apply (sum_add (fun s => kl_proj_closed q Hq s)
                     (fun s => mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).
    + apply (req_plus_compat
               (sumf (fun s => kl_proj_closed q Hq s))
               (sumf (fun s => kl_proj_closed q Hq s))
               (sumf (fun s => mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))
               (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))
               (req_refl (sumf (fun s => kl_proj_closed q Hq s)))).
      apply (req_trans
        (sumf (fun s => mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))))
        (sumf (fun s => mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (q s)))
        (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))).
      * apply (sum_ext
                 (fun s => mult (q s) (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))
                 (fun s => mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (q s))).
        intro s. apply mult_comm.
      * exact (sum_linear (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) q).
Qed.

(* Tail-term evaluation (real_eq closed form of Id kl_tail_eval L95551; genuine proof:
   normalization + log(1/Z) == -log Z) *)
Lemma req_kl_closed_tail_eval :
  forall (q : S -> R) (Hq : forall s : S, real_lt zero (q s)) (Hqn : real_eq (sumf q) one),
    real_eq (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))
        (opp (log Z_aud_req HZ)).
Proof.
  intros q Hq Hqn.
  apply (req_trans (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))
                   (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))
                   (opp (log Z_aud_req HZ))).
  - exact (req_trans (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))
                     (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) one)
                     (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))
                     (req_mult_compat (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))
                                      (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ))
                                      (sumf q) one (req_refl _) Hqn)
                     (mult_one (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)))).
  - exact (rkl_log_inv_one_inv Z_aud_req HZ).
Qed.

(* Main theorem: audit = KL projection (real_eq version of Id
   projected_distribution_minimizes_kl L95587; genuine-proof assembly: split +
   one-sided chain on the nonnegative tail term) *)
Theorem req_projected_distribution_minimizes_kl :
  forall (q : S -> R) (Hq : forall s : S, real_lt zero (q s)) (Hqn : real_eq (sumf q) one)
         (Hqz : forall s : S, post_aud s = false -> real_eq (q s) zero)
         (HlogZ : real_le (log Z_aud_req HZ) zero),
    real_le (sumf (fun s => kl_proj_closed q Hq s))
       (sumf (fun s => mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))).
Proof.
  intros q Hq Hqn Hqz HlogZ.
  assert (Hsplit : real_eq (sumf (fun s => mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))))
                       (plus (sumf (fun s => kl_proj_closed q Hq s)) (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))))
    by exact (req_kl_closed_sum_split q Hq).
  assert (Htail : real_eq (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q)) (opp (log Z_aud_req HZ)))
    by exact (req_kl_closed_tail_eval q Hq Hqn).
  assert (Hge0 : real_le zero (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))).
  { apply (le_id_r zero (opp (log Z_aud_req HZ)) (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))
                   (req_sym (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q)) (opp (log Z_aud_req HZ)) Htail)).
    apply (le_id_l zero (opp zero) (opp (log Z_aud_req HZ)) (req_sym _ _ (rkl_opp_zero))).
    apply (opp_le_compat (log Z_aud_req HZ) zero). exact HlogZ. }
  exact (le_id_r (sumf (fun s => kl_proj_closed q Hq s))
                 (plus (sumf (fun s => kl_proj_closed q Hq s)) (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q)))
                 (sumf (fun s => mult (q s) (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s)))))
                 (req_sym (sumf (fun s => mult (q s)
                                                (req_minus (log (q s) (Hq s))
                                                           (log (p s) (Hp_pos s)))))
                          (plus (sumf (fun s => kl_proj_closed q Hq s))
                                (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q)))
                          Hsplit)
                 (req_le_plus_nonneg_r (sumf (fun s => kl_proj_closed q Hq s))
                                       (mult (log (inv_pos Z_aud_req HZ) (inv_pos_pos Z_aud_req HZ)) (sumf q))
                                       Hge0)).
Qed.

End ReqKLProjection.

(* ============================================================ *)
(* ReqNaturalGradient: natural gradient (real_eq-ified from the Id original section L24347-24460) *)
(*   B-class bridge real_eq counterpart (register 3): req_square_nonneg <- Id Variable     *)
(*   square_nonneg @L24393 (seed real_square_nonneg_eps@L44842 at the root); *)
(*   sum zero-split <- real_eq counterpart of sum_over_S_zero_nonneg (section-head premises).   *)
(* ============================================================ *)
Section ReqNaturalGradient.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, real_le zero (f s)) -> real_eq (sumf f) zero -> forall s : S, real_eq (f s) zero.
Hypothesis req_square_nonneg : forall a : R, real_le zero (mult a a).

Variable Theta : Set.
Variable p_theta : Theta -> S -> R.
Variable partial : (Theta -> R) -> Theta -> R.
Variable p_theta_pos : forall theta : Theta, forall s : S, real_lt zero (p_theta theta s).

(* Fisher information scalar (same shape as Id fisher_info_scalar L24360).
   The Id log has no premise; the setoid log carries a premise, so the real_eq
   version supplies p_theta_pos th s pointwise. *)
Definition fisher_info_scalar_req (theta : Theta) : R :=
  sumf (fun s =>
    mult (p_theta theta s)
         (mult (partial (fun th => log (p_theta th s) (p_theta_pos th s)) theta)
               (partial (fun th => log (p_theta th s) (p_theta_pos th s)) theta))).

(* Fisher zero-split (real_eq version of Id fisher_zero_implies_pointwise L24395;
   genuine proof: pointwise nonnegativity (req_square_nonneg bridge) + zero-sum
   splitting) *)
Theorem req_fisher_zero_implies_pointwise :
  forall theta : Theta,
    real_eq (fisher_info_scalar_req theta) zero ->
    forall s : S,
      real_eq (mult (p_theta theta s)
                (mult (partial (fun th => log (p_theta th s) (p_theta_pos th s)) theta)
                      (partial (fun th => log (p_theta th s) (p_theta_pos th s)) theta)))
          zero.
Proof.
  intros theta Hf0 s.
  assert (Hpt : forall s0 : S,
           real_le zero (mult (p_theta theta s0)
                         (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                               (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)))).
  { intro s0.
    assert (Hsq : real_le zero (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                                (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)))
      by exact (req_square_nonneg
                  (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)).
    exact (le_id_l zero (mult zero (p_theta theta s0))
                   (mult (p_theta theta s0)
                         (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                               (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)))
                   (req_sym (mult zero (p_theta theta s0)) zero
                            (req_trans (mult zero (p_theta theta s0))
                                            (mult (p_theta theta s0) zero) zero
                                            (mult_comm zero (p_theta theta s0))
                                            (mult_zero (p_theta theta s0))))
                   (le_id_r (mult zero (p_theta theta s0))
                            (mult (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                                       (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta))
                                  (p_theta theta s0))
                            (mult (p_theta theta s0)
                                  (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                                        (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)))
                            (mult_comm (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                                             (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta))
                                       (p_theta theta s0))
                            (le_mult_compat zero
                                            (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                                                  (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta))
                                            (p_theta theta s0)
                                            (p_theta_pos theta s0)
                                            Hsq))). }
  exact (sum_zero_nonneg
           (fun s0 => mult (p_theta theta s0)
                           (mult (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)
                                 (partial (fun th => log (p_theta th s0) (p_theta_pos th s0)) theta)))
           Hpt Hf0 s).
Qed.

End ReqNaturalGradient.

(* ============================================================ *)
(* ReqPPORatio: PPO decomposition family (the Id original section PPOClipDecomp L112330-112470   *)
(*   carries 3 migratable items real_eq-ified; the 2 min plain-real_le dependents are frozen -- see the end list) *)
(* ============================================================ *)
Section ReqPPORatio.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    real_eq (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).

Variable pi : S -> R.
Variable p_old : S -> R.
Variable eps : R.
Variable Hpos : forall s : S, real_lt zero (p_old s).

(* IS ratio / clipping / three objectives (same shapes as Id policy_ratio L19613 /
   ppo_clip L19607 / clip_error L112346 / ppo_surrogate L19590 /
   is_objective_of L19599; min/r_max are setoid-interface fields -- symbolic
   carriers only; this group does not depend on their real_le properties) *)
Definition ratio_req (s : S) : R := mult (pi s) (inv_pos (p_old s) (Hpos s)).
Definition ppo_clip_req (r low high : R) : R := min (r_max low r) high.
Definition ppo_surrogate_req (adv : S -> R) : R :=
  sumf (fun s : S =>
    mult (p_old s)
         (min (mult (ratio_req s) (adv s))
              (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                    (adv s)))).
Definition is_objective_req (adv : S -> R) : R :=
  sumf (fun s : S => mult (p_old s) (mult (ratio_req s) (adv s))).
Definition clip_error_req (adv : S -> R) : R :=
  sumf (fun s : S =>
    mult (p_old s)
         (req_minus (mult (ratio_req s) (adv s))
                    (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))).

(* Pointwise decomposition (real_eq version of Id ppo_pointwise_decomp L112363;
   genuine proof: req_minus_plus_cancel (batch 1) + distrib) *)
Lemma req_ppo_pointwise_decomp :
  forall (adv : S -> R) (s : S),
    real_eq (mult (p_old s) (mult (ratio_req s) (adv s)))
        (plus (mult (p_old s)
                    (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))
              (mult (p_old s)
                    (req_minus (mult (ratio_req s) (adv s))
                               (min (mult (ratio_req s) (adv s))
                                    (mult (ppo_clip_req (ratio_req s) (req_minus one eps)
                                                         (plus one eps))
                                          (adv s)))))).
Proof.
  intros adv s.
  assert (Hc : real_eq (mult (ratio_req s) (adv s)) (plus (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))) (req_minus (mult (ratio_req s) (adv s)) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))))
    by exact (req_sym (plus (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))) (req_minus (mult (ratio_req s) (adv s)) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))) (mult (ratio_req s) (adv s))
                      (req_minus_plus_cancel (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))) (mult (ratio_req s) (adv s)))).
  exact (req_trans (mult (p_old s) (mult (ratio_req s) (adv s)))
                   (mult (p_old s) (plus (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))) (req_minus (mult (ratio_req s) (adv s)) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))))
                   (plus (mult (p_old s) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))
                         (mult (p_old s) (req_minus (mult (ratio_req s) (adv s)) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))))))
                   (req_mult_compat (p_old s) (p_old s)
                                    (mult (ratio_req s) (adv s))
                                    (plus (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))) (req_minus (mult (ratio_req s) (adv s)) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s)))))
                                    (req_refl (p_old s)) Hc)
                   (distrib (p_old s) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s))) (req_minus (mult (ratio_req s) (adv s)) (min (mult (ratio_req s) (adv s))
                         (mult (ppo_clip_req (ratio_req s) (req_minus one eps) (plus one eps))
                               (adv s)))))).
Qed.

(* IS objective exact decomposition (real_eq version of Id ppo_is_decomp L112398; genuine-proof assembly) *)
Theorem req_ppo_is_decomp :
  forall adv : S -> R,
    real_eq (is_objective_req adv)
        (plus (ppo_surrogate_req adv) (clip_error_req adv)).
Proof.
  intro adv.
  apply (req_trans (is_objective_req adv)
                   (sumf (fun s : S =>
                            plus (mult (p_old s)
                                       (min (mult (ratio_req s) (adv s))
                                            (mult (ppo_clip_req (ratio_req s)
                                                                (req_minus one eps)
                                                                (plus one eps))
                                                  (adv s))))
                                 (mult (p_old s)
                                       (req_minus (mult (ratio_req s) (adv s))
                                                  (min (mult (ratio_req s) (adv s))
                                                       (mult (ppo_clip_req (ratio_req s)
                                                                            (req_minus one eps)
                                                                            (plus one eps))
                                                             (adv s)))))))
                   (plus (ppo_surrogate_req adv) (clip_error_req adv))).
  - apply (sum_ext (fun s : S => mult (p_old s) (mult (ratio_req s) (adv s)))
                   (fun s : S =>
                      plus (mult (p_old s)
                                 (min (mult (ratio_req s) (adv s))
                                      (mult (ppo_clip_req (ratio_req s) (req_minus one eps)
                                                           (plus one eps))
                                            (adv s))))
                           (mult (p_old s)
                                 (req_minus (mult (ratio_req s) (adv s))
                                            (min (mult (ratio_req s) (adv s))
                                                 (mult (ppo_clip_req (ratio_req s)
                                                                      (req_minus one eps)
                                                                      (plus one eps))
                                                       (adv s))))))).
    intro s. exact (req_ppo_pointwise_decomp adv s).
  - apply sum_add.
Qed.

(* a-b >= 0 implies b <= a (real_eq version of Id le_of_minus_nonneg L112430; genuine proof) *)
Lemma req_le_of_minus_nonneg :
  forall a b : R, real_le zero (req_minus a b) -> real_le b a.
Proof.
  intros a b H.
  exact (le_trans b (plus b (req_minus a b)) a
                   (req_le_plus_nonneg_r b (req_minus a b) H)
                   (le_id_r (plus b (req_minus a b))
                            (plus b (req_minus a b)) a
                            (req_minus_plus_cancel b a)
                            (le_refl (plus b (req_minus a b))))).
Qed.

End ReqPPORatio.

(* ============================================================ *)
(* ReqSigmoidQuick: sigmoid quick wins, 3 items (real_eq-ified from Id L20865-21053)     *)
(* ============================================================ *)
Section ReqSigmoidQuick.

(* Denominator positivity (real_eq version of Id sigmoid_denom_pos L20865; batch-1 req_plus_le_lt_pos) *)
Lemma req_sigmoid_denom_pos : forall x : R, real_lt zero (plus one (exp_neg x)).
Proof.
  intro x.
  exact (req_plus_le_lt_pos one (exp_neg x)
           (lt_le_iff zero one (inl one_pos)) (exp_neg_pos x)).
Qed.

(* Constructive sigmoid (same shape as Id sigmoid L20873) *)
Definition sigmoid_req (x : R) : R :=
  inv_pos (plus one (exp_neg x)) (req_sigmoid_denom_pos x).

(* Range positivity (real_eq version of Id sigmoid_pos L20876) *)
Lemma req_sigmoid_pos : forall x : R, real_lt zero (sigmoid_req x).
Proof. intro x. unfold sigmoid_req.
  exact (inv_pos_pos (plus one (exp_neg x)) (req_sigmoid_denom_pos x)). Qed.

(* sigma(0) = 1/2 (real_eq version of Id sigmoid_zero_half L21045; exp_neg_zero + inv_pos_ext) *)
Lemma req_sigmoid_zero_half :
  real_eq (sigmoid_req zero) (inv_pos (plus one one) (req_two_pos)).
Proof.
  unfold sigmoid_req.
  exact (inv_pos_ext (plus one (exp_neg zero)) (plus one one)
                     (req_sigmoid_denom_pos zero) (req_two_pos)
                     (req_plus_compat one one (exp_neg zero) one
                                      (req_refl one) (exp_neg_zero))).
Qed.

End ReqSigmoidQuick.

(* ============================================================ *)
(* ---- (d) Freeze list (planbook Sec. 3.4: dual-layer parallelism, per-item freeze reasons) ----   *)
(*                                                                *)
(* 1. ppo_conservative (Id @L19526) / std_ppo_conservative    *)
(*    (@L19559) / clip_lower (@L19521) / ppo_clip_upper (@L19648): *)
(*    depend on the plain-real_le forms of min_le_l / r_max_le_r (real_le (min a b) a); *)
(*    the setoid interface's min/r_max real_le outputs are eps-ified (min_le_l :          *)
(*    forall eps, real_lt zero eps -> real_le (min a b) (plus a eps)); the plain  *)
(*    form is not derivable from the eps form (no order elimination) -- with the        *)

(*    UpReqAlgebra frozen items: beyond the mechanical-translation boundary; frozen, batch-5 adjudication.                              *)
(* 2. clip_error_nonneg (Id @L112408) / ppo_clipped_improvement      *)
(*    (@L112439): same reason (min_le_l plain form + le_minus_nonneg(min)). *)
(* 3. fold_right_ext and the dpo_total_loss_at_star list-fold machinery     *)
(*    (Id around @L20160): nat/list-layer Id is independent of the number-system interface, reused as-is   *)
(*    (planbook Sec. 1.1 boundary 2); the real_eq companions of   *)
(*    dpo_total_loss(_monotone) follow the batch-4 outcome once the dpo_pair_loss family is real_eq-ified.                       *)
(* 4. GRPOCounterEx counterexample witness (not on the batch-3 list): dual-layer parallel (the verification evidence   *)
(*    cannot be Check-ed at the top level, Sec. 0.3).                                       *)
(*                                                                *)
(* ---- Deep-chain pending list (batches 3b/5; notes on the content carried by the T2(1) bridging lemmas) ----       *)
(* 1. req_backward_kl_identity (declared at this file's premises position; the Id theorem   *)
(*    policy_iter_backward_kl_step @L22686 is its counterpart): the Id proof ~100 lines, depending on   *)
(*    the t13 algebra chain (minus_distr_t13 and 9 more) +                        *)
(*    policy_iter_backward_kl_step_beta @L22575; the real_eq re-proof first needs the batch-1    *)
(*    foundation to add the t13 real_eq companions (mechanical items, est. 1-1.5 person-days); pending batch 3b.     *)
(* 2. req_policy_improvement_mono (declared at this file's premises position; the Id        *)
(*    counterpart @L22065): depends on the t12 deep chain (J_pi_t/J_pi_next/F_t_simpl_next_kl/  *)
(*    surrogate_diff_identity and ~11 more), pending batch 3b.                *)
(* 3. Once the two bridges above are discharged, this file's main items    *)
(*    (req_policy_iter_kl_geom_step/_iter/req_dpo_loss_iter_mono) close the whole chain as unconditional real_eq theorems --    *)
(*    this file has already genuinely proved all their real_eq-side transport and order-algebra content.                       *)
(* 4. The remaining Alignment Id items (of the alignment-identity family L19180-21240: the             *)
(*    align_objective_advantage_decomp / dpo_reward families / the t12 ring-algebra  *)
(*    duplicates, ~60 items): most real_eq counterparts are already covered by UpReqAlgebra (batch 1) and        *)
(*    UpReqDist (batch-2 reqd_ family); the remainder moves with batch 3b on this file's template      *)
(*    (mechanical translation); sigmoid_strict_inc (@L21028) needs the inv_pos_lt_contra bridge     *)
(*    (B-class premises real_eq counterpart, Sec. 1.5), following the B-bridge batch outcome.                    *)
(* ============================================================ *)

Print Assumptions req_align_partition_condition.
Print Assumptions req_rlhf_optimal.
Print Assumptions req_rlhf_optimal_unique.
Print Assumptions req_dpo_optimal.
Print Assumptions req_plus_opp_le_zero.
Print Assumptions req_plusA_opp_cancel_le.
Print Assumptions req_dpo_loss_iter_step_le.
Print Assumptions req_Z_aud_le_one.
Print Assumptions req_sigmoid_pos.
Print Assumptions req_sigmoid_zero_half.
