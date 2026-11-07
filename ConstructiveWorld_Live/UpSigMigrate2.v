(* ConstructiveWorld-Set — Signature migration part 2: exponential and logarithmic interfaces with the partition face of the RLHF chain. *)

(** * UpSigMigrate2: setoid-level [req] restatement of the §4 RLHF core chain
      of paper 1 (theorems 4.1–4.4) with two-state end-to-end theorems.

    Mission.  Part A restates the §4.1 free-energy interface: [req_exp_neg_ext],
      [req_log_inv_one_inv], the [boltzmann_dist_m2]/[free_energy_m2] family,
      the Boltzmann triple, and the decompositions [req_free_energy_boltzmann]/
      [req_free_energy_kl_decomp].  Part B restates the alignment layer
      ([a_rlhf_optimal], [a_rlhf_optimal_eps], [a_dpo_optimal],
      [a_rlhf_optimal_unique], [a_rlhf_suboptimality_gap],
      [a_rlhf_policy_improvement]); Part C the two-state end-to-end theorems.

    Dependencies.  Requires [S01_BaseRing]–[S15_TailFEPUp] of this development
      (notably [S07_RealSetoidExpLog] for [RealInterfaceEnhancedSetoid] and its
      instance [RealEnhancedReal]); the summation/logarithm fields and the Gibbs
      bridges are explicit Section premises (honest interface, no silent gaps).

    References.  This development; the baseline module of the same name in
      ConstructiveWorld-Main, whose statement names are carried over verbatim
      (statement-face Set-carrier completion), following its
      [FreeEnergyMinimization] and [Alignment] sections.

    Constructivity.  All named statements are carried by [Set]; the predicate
      notations bind to the global real face ([req] := [real_eq], [lt] :=
      [real_lt], [le] := [real_le]); proofs close by [Qed] along [req_trans]
      chains; extraction gives [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" UpSigMigrate2.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact are [436f7121 00015ff4]. *)

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
Import RealInterfaceEnhancedMod.

(* S07 lineage adaptation: [RealInterfaceEnhancedSetoid] in this world is a
   parameterless class ([S07_RealSetoidExpLog] [L8075]; every field is
   carried by the global [Real]; global instance [RealEnhancedReal] [L8740]).
   The parameterized binding face [Context {R : Set}
   {RIS : RealInterfaceEnhancedSetoid R}] belongs to the other tree and is
   dropped; the carrier set [R] is bound to the global [Real] by notation,
   in the same style as [UpAblT6_UpReqAlign2].  The predicate face binds the
   class fields directly to the global real face (the [req]/[lt]/[le] field
   types spell [real_eq]/[real_lt]/[real_le] verbatim), so statements use the
   real-face notation aligned with the field declarations and extraction
   needs no [Obj.magic] casts; the instance fields [req] := [real_eq],
   [lt] := [real_lt], [le] := [real_le] are inter-convertible with the class
   reading, as in [UpSigMigrate]. *)
Notation R := Real.
Notation req := real_eq.
Notation lt := real_lt.
Notation le := real_le.

(* ============================================================ *)
(* Part A. req-family restatement of the §4.1 general exit       *)
(*   Template: the [FreeEnergyMinimization] section of the       *)
(*   ConstructiveWorld-Main baseline, [L15759]-[L16440]          *)
(*   ([Context {RI : RealInterfaceEnhanced}]).                   *)
(* ============================================================ *)
Section ReqFECore.
Variable S : Set.

(* ---- req-signature interface of [SumOver]: the setoid dual of the Id-carried [SumOver] class ---- *)
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).

(* ---- Section parameters (mirroring the upstream [L15778]-[L15791]) ---- *)
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable Z : R.
Variable Z_pos : lt zero Z.
Hypothesis partition_condition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

(* ---- Honest gap bridges (fields genuinely missing from the setoid class; resolved for the [Real] instance in Part C) ---- *)
(* Cancellation of [log] ∘ [exp_neg]: the req form of the upstream lemma [log_exp_neg], proved in the ConstructiveWorld-Main baseline at [L592] *)
Hypothesis req_log_exp_neg :
  forall x : R, req (log (exp_neg x) (exp_neg_pos x)) (opp x).

Hypothesis req_log_compat :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    req a b -> req (log a Ha) (log b Hb).

(* ---- Section definitions (setoid convention; the [log] family carries positivity premises) ---- *)
Definition positive_dist_m2 (p : S -> R) : Set := forall s : S, lt zero (p s).
Definition normalized_m2 (p : S -> R) : Set := req (sumf p) one.
Definition rminus_m2 (a b : R) : R := plus a (opp b).
Definition boltzmann_dist_m2 : S -> R :=
  fun s => mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).
Definition free_energy_m2 (p : S -> R) (Hp : positive_dist_m2 p) : R :=
  plus (sumf (fun s => mult (p s) (base_loss s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).

(* ============================================================ *)
(* A0. req algebra preliminaries (proved in [UpSigMigrate.v]; only interface fields are used) *)
(* ============================================================ *)

Lemma req_plus_zero_r : forall a : R, req (plus zero a) a.
Proof.
  intro a.
  exact (req_trans (plus zero a) (plus a zero) a (plus_comm zero a) (plus_zero a)).
Qed.

Lemma req_mult_one_l : forall a : R, req (mult one a) a.
Proof.
  intro a.
  exact (req_trans (mult one a) (mult a one) a (mult_comm one a) (mult_one a)).
Qed.

Lemma req_add_cancel_l : forall (u v w : R),
  req (plus u v) (plus w v) -> req u w.
Proof.
  intros u v w H.
  apply (req_trans u (plus u zero) w).
  - apply (req_sym (plus u zero) u). apply plus_zero.
  - apply (req_trans (plus u zero) (plus u (plus v (opp v))) w).
    + apply (req_plus_compat u u zero (plus v (opp v))).
      * apply req_refl.
      * apply (req_sym (plus v (opp v)) zero). apply plus_opp.
    + apply (req_trans (plus u (plus v (opp v))) (plus (plus u v) (opp v)) w).
      * apply plus_assoc.
      * apply (req_trans (plus (plus u v) (opp v)) (plus (plus w v) (opp v)) w).
        -- apply (req_plus_compat (plus u v) (plus w v) (opp v) (opp v) H).
           apply req_refl.
        -- apply (req_trans (plus (plus w v) (opp v)) (plus w (plus v (opp v))) w).
           ++ apply (req_sym (plus w (plus v (opp v))) (plus (plus w v) (opp v))).
              apply plus_assoc.
           ++ apply (req_trans (plus w (plus v (opp v))) (plus w zero) w).
              ** apply (req_plus_compat w w (plus v (opp v)) zero).
                 --- apply req_refl.
                 --- apply plus_opp.
              ** apply plus_zero.
Qed.

Lemma req_double_neg : forall a : R, req (opp (opp a)) a.
Proof.
  intro a.
  apply (req_add_cancel_l (opp (opp a)) (opp a) a).
  apply (req_trans (plus (opp (opp a)) (opp a)) zero (plus a (opp a))).
  - apply (req_trans (plus (opp (opp a)) (opp a)) (plus (opp a) (opp (opp a))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus a (opp a)) zero). apply plus_opp.
Qed.

Lemma req_opp_plus : forall a b : R, req (opp (plus a b)) (plus (opp a) (opp b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (opp (plus a b)) (plus a b) (plus (opp a) (opp b))).
  apply (req_trans (plus (opp (plus a b)) (plus a b)) zero (plus (plus (opp a) (opp b)) (plus a b))).
  - apply (req_trans (plus (opp (plus a b)) (plus a b)) (plus (plus a b) (opp (plus a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus (plus (opp a) (opp b)) (plus a b)) zero).
    apply (req_trans (plus (plus (opp a) (opp b)) (plus a b))
                     (plus (opp a) (plus (opp b) (plus a b)))
                     zero).
    + apply (req_sym (plus (opp a) (plus (opp b) (plus a b)))
                     (plus (plus (opp a) (opp b)) (plus a b))).
      apply plus_assoc.
    + apply (req_trans (plus (opp a) (plus (opp b) (plus a b)))
                       (plus (opp a) (plus (plus (opp b) a) b))
                       zero).
      * apply (req_plus_compat (opp a) (opp a) (plus (opp b) (plus a b)) (plus (plus (opp b) a) b)).
        -- apply req_refl.
        -- apply plus_assoc.
      * apply (req_trans (plus (opp a) (plus (plus (opp b) a) b))
                         (plus (opp a) (plus (plus a (opp b)) b))
                         zero).
        -- apply (req_plus_compat (opp a) (opp a) (plus (plus (opp b) a) b) (plus (plus a (opp b)) b)).
           ++ apply req_refl.
           ++ apply (req_plus_compat (plus (opp b) a) (plus a (opp b)) b b).
              ** apply plus_comm.
              ** apply req_refl.
        -- apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                            (plus (plus (opp a) a) (plus (opp b) b))
                            zero).
           ++ apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                               (plus (opp a) (plus a (plus (opp b) b)))
                               (plus (plus (opp a) a) (plus (opp b) b))).
              ** apply (req_plus_compat (opp a) (opp a) (plus (plus a (opp b)) b) (plus a (plus (opp b) b))).
                 --- apply req_refl.
                 --- apply (req_sym (plus a (plus (opp b) b)) (plus (plus a (opp b)) b)). apply plus_assoc.
              ** apply plus_assoc.
           ++ apply (req_trans (plus (plus (opp a) a) (plus (opp b) b)) (plus zero zero) zero).
              ** apply (req_plus_compat (plus (opp a) a) zero (plus (opp b) b) zero).
                 --- apply (req_trans (plus (opp a) a) (plus a (opp a)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
                 --- apply (req_trans (plus (opp b) b) (plus b (opp b)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
              ** apply plus_zero.
Qed.

Lemma req_mult_opp_l : forall a b : R, req (mult a (opp b)) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (mult a (opp b)) (mult a b) (opp (mult a b))).
  apply (req_trans (plus (mult a (opp b)) (mult a b)) zero (plus (opp (mult a b)) (mult a b))).
  - apply (req_trans (plus (mult a (opp b)) (mult a b)) (plus (mult a b) (mult a (opp b))) zero).
    + apply plus_comm.
    + apply (req_trans (plus (mult a b) (mult a (opp b))) (mult a (plus b (opp b))) zero).
      * apply (req_sym (mult a (plus b (opp b))) (plus (mult a b) (mult a (opp b)))).
        apply distrib.
      * apply (req_trans (mult a (plus b (opp b))) (mult a zero) zero).
        -- apply (req_mult_compat a a (plus b (opp b)) zero).
           ++ apply req_refl.
           ++ apply plus_opp.
        -- apply mult_zero.
  - apply (req_sym (plus (opp (mult a b)) (mult a b)) zero).
    apply (req_trans (plus (opp (mult a b)) (mult a b)) (plus (mult a b) (opp (mult a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
Qed.

Lemma req_opp_mult_l : forall a b : R, req (mult (opp a) b) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_trans (mult (opp a) b) (mult b (opp a)) (opp (mult a b))).
  - apply mult_comm.
  - apply (req_trans (mult b (opp a)) (opp (mult b a)) (opp (mult a b))).
    + apply req_mult_opp_l.
    + apply (req_opp_compat (mult b a) (mult a b)). apply mult_comm.
Qed.

(* three-step commutation chain for products (the upstream mult-swap template): a·(b·c) == b·(a·c) *)
Lemma req_mult_swap : forall a b c : R, req (mult a (mult b c)) (mult b (mult a c)).
Proof.
  intros a b c.
  apply (req_trans (mult a (mult b c)) (mult (mult a b) c) (mult b (mult a c))).
  - apply mult_assoc.
  - apply (req_trans (mult (mult a b) c) (mult (mult b a) c) (mult b (mult a c))).
    + apply (req_mult_compat (mult a b) (mult b a) c c).
      * apply mult_comm.
      * apply req_refl.
    + apply (req_sym (mult b (mult a c)) (mult (mult b a) c)). apply mult_assoc.
Qed.

(* ============================================================ *)
(* A1. req compatibility of [exp_neg] (the upstream id_cong      *)
(*     exp_neg free lemma, derived from the [le_antisym] and     *)
(*     [exp_neg_le_decr] fields)                                 *)
(* ============================================================ *)
Lemma req_exp_neg_ext : forall x y : R, req x y -> req (exp_neg x) (exp_neg y).
Proof.
  intros x y Hxy.
  apply le_antisym.
  - apply exp_neg_le_decr. apply (lt_le_iff y x). apply (inr (req_sym x y Hxy)).
  - apply exp_neg_le_decr. apply (lt_le_iff x y). apply (inr Hxy).
Qed.

(* ============================================================ *)
(* A2. req form of [log_inv_one_inv] (free lemma upstream)       *)
(* ============================================================ *)
Lemma req_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x),
    req (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  assert (Hone : req (log (mult x (inv_pos x Hx)) (mult_positive x (inv_pos x Hx) Hx (inv_pos_pos x Hx))) zero).
  { apply (req_trans (log (mult x (inv_pos x Hx)) (mult_positive x (inv_pos x Hx) Hx (inv_pos_pos x Hx)))
                     (log one one_pos) zero).
    - apply (req_log_compat (mult x (inv_pos x Hx)) one
                            (mult_positive x (inv_pos x Hx) Hx (inv_pos_pos x Hx)) one_pos).
      apply inv_pos_correct.
    - apply log_one. }
  assert (Htot : req (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx))) zero)
    by exact (req_trans (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx)))
                        (log (mult x (inv_pos x Hx)) (mult_positive x (inv_pos x Hx) Hx (inv_pos_pos x Hx)))
                        zero
                        (req_sym (log (mult x (inv_pos x Hx)) (mult_positive x (inv_pos x Hx) Hx (inv_pos_pos x Hx)))
                                 (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx)))
                                 (log_mult x (inv_pos x Hx) Hx (inv_pos_pos x Hx)))
                        Hone).
  apply (req_trans (log (inv_pos x Hx) (inv_pos_pos x Hx))
                   (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) zero)
                   (opp (log x Hx))).
  - apply (req_sym (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) zero)
                   (log (inv_pos x Hx) (inv_pos_pos x Hx))). apply plus_zero.
  - apply (req_trans (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) zero)
                     (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (plus (log x Hx) (opp (log x Hx))))
                     (opp (log x Hx))).
    + apply (req_plus_compat (log (inv_pos x Hx) (inv_pos_pos x Hx))
                             (log (inv_pos x Hx) (inv_pos_pos x Hx))
                             zero (plus (log x Hx) (opp (log x Hx)))).
      * apply req_refl.
      * exact (req_sym (plus (log x Hx) (opp (log x Hx))) zero (plus_opp (log x Hx))).
    + apply (req_trans (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (plus (log x Hx) (opp (log x Hx))))
                       (plus (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx)) (opp (log x Hx)))
                       (opp (log x Hx))).
      * apply plus_assoc.
      * apply (req_trans (plus (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx)) (opp (log x Hx)))
                         (plus (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx))) (opp (log x Hx)))
                         (opp (log x Hx))).
        -- apply (req_plus_compat (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx))
                                  (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx)))
                                  (opp (log x Hx)) (opp (log x Hx))).
           ++ apply plus_comm.
           ++ apply req_refl.
        -- apply (req_trans (plus (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx))) (opp (log x Hx)))
                            (plus zero (opp (log x Hx)))
                            (opp (log x Hx))).
           ++ apply (req_plus_compat (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx))) zero
                                     (opp (log x Hx)) (opp (log x Hx)) Htot (req_refl (opp (log x Hx)))).
           ++ apply req_plus_zero_r.
Qed.

(* ============================================================ *)
(* A3. The Boltzmann triple: req forms of the upstream           *)
(*     boltzmann_pos/boltzmann_normalized/boltzmann_log_decomp;  *)
(*     the log_decomp step is proved internally here             *)
(* ============================================================ *)
Lemma req_boltzmann_positive : positive_dist_m2 boltzmann_dist_m2.
Proof.
  intro s.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

Lemma req_boltzmann_normalized : req (sumf boltzmann_dist_m2) one.
Proof.
  apply (req_trans (sumf boltzmann_dist_m2)
                   (mult (inv_pos Z Z_pos)
                         (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                   one).
  - exact (sum_linear (inv_pos Z Z_pos)
                      (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
  - apply (req_trans (mult (inv_pos Z Z_pos)
                           (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                     (mult (inv_pos Z Z_pos) Z)
                     one).
    + apply (req_mult_compat (inv_pos Z Z_pos) (inv_pos Z Z_pos)
                             (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
      * apply req_refl.
      * apply (req_sym Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))))).
        exact partition_condition.
    + apply (req_trans (mult (inv_pos Z Z_pos) Z) (mult Z (inv_pos Z Z_pos)) one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.


Lemma req_boltzmann_log_decomp :
  forall (s : S) (Hpb : lt zero (boltzmann_dist_m2 s)),
    req (log (boltzmann_dist_m2 s) Hpb)
        (plus (opp (log Z Z_pos))
              (opp (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  intros s Hpb.
  apply (req_trans (log (boltzmann_dist_m2 s) Hpb)
                   (plus (log (inv_pos Z Z_pos) (inv_pos_pos Z Z_pos))
                         (log (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))
                   (plus (opp (log Z Z_pos))
                         (opp (mult (inv_pos D D_pos) (base_loss s))))).
  - (* positivity-premise transport: the dependent evidence of [log] is transported by [req_log_compat] on a reflexive instance *)
    apply (req_trans (log (boltzmann_dist_m2 s) Hpb)
                     (log (mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))))
                          (mult_positive (inv_pos Z Z_pos)
                                         (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (inv_pos_pos Z Z_pos) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))
                     (plus (log (inv_pos Z Z_pos) (inv_pos_pos Z Z_pos))
                           (log (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))).
    + exact (req_sym (log (mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))))
                          (mult_positive (inv_pos Z Z_pos)
                                         (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (inv_pos_pos Z Z_pos) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))
                     (log (boltzmann_dist_m2 s) Hpb)
                     (req_log_compat (mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))))
                                     (boltzmann_dist_m2 s)
                                     (mult_positive (inv_pos Z Z_pos)
                                                    (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (inv_pos_pos Z Z_pos) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))))
                                     Hpb
                                     (req_refl (mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))))))).
    + exact (log_mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (inv_pos_pos Z Z_pos) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))).
  - apply (req_plus_compat (log (inv_pos Z Z_pos) (inv_pos_pos Z Z_pos))
                           (opp (log Z Z_pos))
                           (log (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))))
                           (opp (mult (inv_pos D D_pos) (base_loss s)))).
    + exact (req_log_inv_one_inv Z Z_pos).
    + exact (req_log_exp_neg (mult (inv_pos D D_pos) (base_loss s))).
Qed.

(* energy-log identity: E == opp(D·(log p_b + log Z)); internal req proof of the upstream statement at [L16116] *)
Lemma req_energy_in_log :
  forall (s : S) (Hpb : lt zero (boltzmann_dist_m2 s)),
    req (base_loss s)
        (opp (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos)))).
Proof.
  intros s Hpb.
  assert (Hld : req (log (boltzmann_dist_m2 s) Hpb)
                    (plus (opp (log Z Z_pos))
                          (opp (mult (inv_pos D D_pos) (base_loss s)))))
    by exact (req_boltzmann_log_decomp s Hpb).
  (* branch 1: lgb + lgZ == opp m, where m := E/D *)
  assert (H1 : req (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos))
                   (opp (mult (inv_pos D D_pos) (base_loss s)))).
  { apply (req_trans (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos))
                     (plus (plus (opp (log Z Z_pos))
                                 (opp (mult (inv_pos D D_pos) (base_loss s))))
                           (log Z Z_pos))
                     (opp (mult (inv_pos D D_pos) (base_loss s)))).
    - apply (req_plus_compat (log (boltzmann_dist_m2 s) Hpb)
                             (plus (opp (log Z Z_pos))
                                   (opp (mult (inv_pos D D_pos) (base_loss s))))
                             (log Z Z_pos) (log Z Z_pos) Hld (req_refl (log Z Z_pos))).
    - (* ring algebra: (opp lgZ + opp m) + lgZ == opp m *)
      apply (req_trans (plus (plus (opp (log Z Z_pos))
                                 (opp (mult (inv_pos D D_pos) (base_loss s))))
                           (log Z Z_pos))
                       (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                             (plus (opp (log Z Z_pos)) (log Z Z_pos)))
                       (opp (mult (inv_pos D D_pos) (base_loss s)))).
      + apply (req_trans (plus (plus (opp (log Z Z_pos))
                                     (opp (mult (inv_pos D D_pos) (base_loss s))))
                               (log Z Z_pos))
                         (plus (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                                     (opp (log Z Z_pos)))
                               (log Z Z_pos))
                         (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                               (plus (opp (log Z Z_pos)) (log Z Z_pos)))).
        * apply (req_plus_compat (plus (opp (log Z Z_pos))
                                       (opp (mult (inv_pos D D_pos) (base_loss s))))
                                 (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                                       (opp (log Z Z_pos)))
                                 (log Z Z_pos) (log Z Z_pos)).
          -- apply plus_comm.
          -- apply (req_refl (log Z Z_pos)).
        * apply (req_sym (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                               (plus (opp (log Z Z_pos)) (log Z Z_pos)))
                         (plus (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                                     (opp (log Z Z_pos)))
                               (log Z Z_pos))).
          apply plus_assoc.
      + apply (req_trans (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                               (plus (opp (log Z Z_pos)) (log Z Z_pos)))
                         (plus (opp (mult (inv_pos D D_pos) (base_loss s))) zero)
                         (opp (mult (inv_pos D D_pos) (base_loss s)))).
        * apply (req_plus_compat (opp (mult (inv_pos D D_pos) (base_loss s)))
                                 (opp (mult (inv_pos D D_pos) (base_loss s)))
                                 (plus (opp (log Z Z_pos)) (log Z Z_pos)) zero
                                 (req_refl (opp (mult (inv_pos D D_pos) (base_loss s))))
                                 (req_trans (plus (opp (log Z Z_pos)) (log Z Z_pos))
                                            (plus (log Z Z_pos) (opp (log Z Z_pos)))
                                            zero
                                            (plus_comm (opp (log Z Z_pos)) (log Z Z_pos))
                                            (plus_opp (log Z Z_pos)))).
        * apply plus_zero. }
  (* branches 2/3: D·(lgb + lgZ) == D·(opp m) == opp(D·m) == opp(loss) *)
  assert (Hchain : req (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos)))
                       (opp (base_loss s))).
  { apply (req_trans (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos)))
                     (opp (mult D (mult (inv_pos D D_pos) (base_loss s))))
                     (opp (base_loss s))).
    - apply (req_trans (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos)))
                       (mult D (opp (mult (inv_pos D D_pos) (base_loss s))))
                       (opp (mult D (mult (inv_pos D D_pos) (base_loss s))))).
      + apply (req_mult_compat D D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos))
                               (opp (mult (inv_pos D D_pos) (base_loss s))) (req_refl D) H1).
      + apply req_mult_opp_l.
    - apply (req_opp_compat (mult D (mult (inv_pos D D_pos) (base_loss s)))
                            (base_loss s)).
      apply (req_trans (mult D (mult (inv_pos D D_pos) (base_loss s)))
                       (mult (mult D (inv_pos D D_pos)) (base_loss s))
                       (base_loss s)).
      + apply mult_assoc.
      + apply (req_trans (mult (mult D (inv_pos D D_pos)) (base_loss s))
                         (mult one (base_loss s))
                         (base_loss s)).
        * apply (req_mult_compat (mult D (inv_pos D D_pos)) one (base_loss s) (base_loss s)
                                 (inv_pos_correct D D_pos) (req_refl (base_loss s))).
        * apply req_mult_one_l. }
  apply (req_trans (base_loss s)
                   (opp (opp (base_loss s)))
                   (opp (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos))))).
  - apply (req_sym (opp (opp (base_loss s))) (base_loss s)). apply req_double_neg.
  - apply (req_opp_compat (opp (base_loss s))
                          (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos)))).
    exact (req_sym (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos)))
                   (opp (base_loss s)) Hchain).
Qed.

(* ============================================================ *)
(* A4. summation layer: Σ opp f == opp Σ f (req version of the upstream [sum_opp] at [L15801]) *)
(* ============================================================ *)
Lemma req_sum_opp :
  forall f : S -> R, req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (sum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply (req_opp_compat (f s) (mult one (f s))).
      apply (req_sym (mult one (f s)) (f s)). apply req_mult_one_l.
    + apply (req_sym (mult (opp one) (f s)) (opp (mult one (f s)))).
      apply req_opp_mult_l.
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + apply (sum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f)) (opp (mult one (sumf f))) (opp (sumf f))).
      * apply req_opp_mult_l.
      * apply (req_opp_compat (mult one (sumf f)) (sumf f)). apply req_mult_one_l.
Qed.

(* Σ u·opp v == opp Σ u·v (direct appeal to the mult-opp summand identity) *)
Lemma req_sum_mult_opp :
  forall u v : S -> R,
    req (sumf (fun s => mult (u s) (opp (v s))))
        (opp (sumf (fun s => mult (u s) (v s)))).
Proof.
  intros u v.
  apply (req_trans (sumf (fun s => mult (u s) (opp (v s))))
                   (sumf (fun s => opp (mult (u s) (v s))))
                   (opp (sumf (fun s => mult (u s) (v s))))).
  - apply (sum_ext (fun s => mult (u s) (opp (v s)))
                   (fun s => opp (mult (u s) (v s)))).
    intro s. apply req_mult_opp_l.
  - apply req_sum_opp.
Qed.

(* ============================================================ *)

(*     (req version of the upstream [p_times_energy_decomp] at [L16198]; the   *)
(*      energy-log identity is proved internally here, where [UpSigMigrate]    *)
(*      carried it as a bridge premise — the upgrade point of this file)      *)
(* ============================================================ *)
Lemma req_p_times_energy_decomp :
  forall (p : S -> R) (s : S),
    (req (mult (p s) (base_loss s)) (plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
Proof.
  intros p s.
  assert (HlegA : (req (mult (p s) (base_loss s)) (opp (mult (p s) (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))))).
  { apply (req_trans (mult (p s) (base_loss s)) (mult (p s) (opp (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (mult (p s) (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))))).
    apply (req_mult_compat (p s) (p s) (base_loss s) (opp (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))).
      apply req_refl.
      exact (req_energy_in_log s (req_boltzmann_positive s)).
    apply req_mult_opp_l.
  }
  assert (Hswap : (req (mult (p s) (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))))).
  { exact (req_mult_swap (p s) D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))).
  }
  assert (Hdist2 : (req (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos)))))).
  { apply (req_trans (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (plus (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))).
    apply (req_mult_compat D D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))) (plus (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))).
      apply req_refl.
      apply distrib.
    apply distrib.
  }
  apply (req_trans (mult (p s) (base_loss s)) (opp (mult (p s) (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
  - exact HlegA.
  - apply (req_trans (opp (mult (p s) (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
    apply (req_opp_compat (mult (p s) (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))).
    exact Hswap.
    apply (req_trans (opp (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (plus (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
    apply (req_opp_compat (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))).
    exact Hdist2.
    apply req_opp_plus.
Qed.

(* Σ p_b·u == u for arbitrary u (direct consequence of normalization) *)
Lemma req_sum_pb_cancel :
  forall u : R,
    req (sumf (fun s => mult (boltzmann_dist_m2 s) u)) u.
Proof.
  intro u.
  apply (req_trans (sumf (fun s => (mult (boltzmann_dist_m2 s) u))) (mult u (sumf boltzmann_dist_m2)) u).
  - apply (req_trans (sumf (fun s => (mult (boltzmann_dist_m2 s) u))) (sumf (fun s => (mult u (boltzmann_dist_m2 s)))) (mult u (sumf boltzmann_dist_m2))).
      apply (sum_ext (fun s => (mult (boltzmann_dist_m2 s) u)) (fun s => (mult u (boltzmann_dist_m2 s)))).
        intro s0. apply mult_comm.
      apply (sum_linear u boltzmann_dist_m2).
  - apply (req_trans (mult u (sumf boltzmann_dist_m2)) (mult u one) u).
      apply (req_mult_compat u u (sumf boltzmann_dist_m2) one (req_refl u) req_boltzmann_normalized).
      apply mult_one.
Qed.

Lemma req_free_energy_boltzmann :
  req (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive)
      (opp (mult D (log Z Z_pos))).
Proof.
  unfold free_energy_m2.
  assert (Hsum1 : (req (sumf (fun s => (mult (boltzmann_dist_m2 s) (base_loss s)))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))))).
  { apply (req_trans (sumf (fun s => (mult (boltzmann_dist_m2 s) (base_loss s)))) (sumf (fun s => (plus (opp (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))))).
      apply (sum_ext (fun s => (mult (boltzmann_dist_m2 s) (base_loss s))) (fun s => (plus (opp (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))).
        intro s0. exact (req_p_times_energy_decomp boltzmann_dist_m2 s0).
      apply (req_trans (sumf (fun s => (plus (opp (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))) (plus (sumf (fun s => (opp (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (sumf (fun s => (opp (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))))).
        apply sum_add.
        apply (req_plus_compat (sumf (fun s => (opp (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (sumf (fun s => (opp (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))).
          apply (req_trans (sumf (fun s => (opp (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (sumf (fun s => (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
            apply req_sum_opp.
            apply (req_opp_compat (sumf (fun s => (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
              apply (sum_linear D (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))).
          apply (req_trans (sumf (fun s => (opp (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))) (opp (sumf (fun s => (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))).
            apply req_sum_opp.
            apply (req_opp_compat (sumf (fun s => (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))).
              apply (sum_linear D (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos)))).
  }
  assert (Hsum2 : (req (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))))).
  { apply (req_plus_compat (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))) (opp (mult D (log Z Z_pos)))).
      apply (req_refl (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
      apply (req_opp_compat (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos))))) (mult D (log Z Z_pos))).
        apply (req_mult_compat D D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos)))) (log Z Z_pos) (req_refl D) (req_sum_pb_cancel (log Z Z_pos))).
  }
  assert (Hsum : (req (sumf (fun s => (mult (boltzmann_dist_m2 s) (base_loss s)))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))))).
  { exact (req_trans (sumf (fun s => (mult (boltzmann_dist_m2 s) (base_loss s)))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))) Hsum1 Hsum2). }
  apply (req_trans (plus (sumf (fun s => (mult (boltzmann_dist_m2 s) (base_loss s)))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))).
  - apply (req_plus_compat (sumf (fun s => (mult (boltzmann_dist_m2 s) (base_loss s)))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
      exact Hsum.
      apply (req_refl (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
  - apply (req_trans (plus (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (opp (mult D (log Z Z_pos))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))) (opp (mult D (log Z Z_pos)))).
      apply (req_sym _ _ (plus_assoc (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
      apply (req_trans (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (opp (mult D (log Z Z_pos))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos))))) (opp (mult D (log Z Z_pos)))).
        apply (req_plus_compat (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (opp (mult D (log Z Z_pos))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos))))).
          apply (req_refl (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
          apply plus_comm.
        apply (req_trans (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos))))) (plus (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))) (opp (mult D (log Z Z_pos)))).
          apply plus_assoc.
          apply (req_trans (plus (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))) (plus zero (opp (mult D (log Z Z_pos)))) (opp (mult D (log Z Z_pos)))).
            apply (req_plus_compat (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) zero (opp (mult D (log Z Z_pos))) (opp (mult D (log Z Z_pos)))).
              apply (req_trans (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))) zero).
                apply plus_comm.
                apply plus_opp.
              apply (req_refl (opp (mult D (log Z Z_pos)))).
            apply req_plus_zero_r.
Qed.

Theorem req_free_energy_kl_decomp :
  forall (p : S -> R) (Hp : normalized_m2 p) (p0 : positive_dist_m2 p),
    req (free_energy_m2 p p0)
        (plus (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive)
              (mult D (sumf (fun s =>
                mult (p s) (rminus_m2 (log (p s) (p0 s))
                                   (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
Proof.
  intros p Hp p0.
  (* bridge: F[p_b] == mult (opp D) lgZ == opp (D·lgZ) (req form of upstream step 2) *)
  assert (Hfb' : req (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive)
                     (opp (mult D (log Z Z_pos)))).
  { exact req_free_energy_boltzmann. }
  (* step 1: Σ p·E == opp A + opp DlgZ (upstream [Hse]) *)
  assert (Hse : req (sumf (fun s => mult (p s) (base_loss s)))
                    (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                          (opp (mult D (log Z Z_pos))))).
  { apply (req_trans (sumf (fun s => mult (p s) (base_loss s)))
                     (sumf (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                                          (opp (mult D (mult (p s) (log Z Z_pos))))))
                     (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                           (opp (mult D (log Z Z_pos))))).
    - apply (sum_ext (fun s => mult (p s) (base_loss s))
                     (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                                    (opp (mult D (mult (p s) (log Z Z_pos)))))).
      { intro s. exact (req_p_times_energy_decomp p s). }
    - apply (req_trans (sumf (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                                            (opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (sumf (fun s => opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                             (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                             (opp (mult D (log Z Z_pos))))).
      { apply sum_add. }
      { apply (req_plus_compat (sumf (fun s => opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                               (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                               (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                               (opp (mult D (log Z Z_pos)))).
        - (* Σ opp(D·p·lgpb) == opp(D·Σ p·lgpb): req_sum_opp plus linearity in D *)
          apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                           (opp (sumf (fun s => mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
          { apply req_sum_opp. }
          { apply (req_opp_compat (sumf (fun s => mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                                  (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))).
            { apply (sum_linear D (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))). } }
        - (* Σ opp(D·p·lgZ) == opp(D·lgZ): req_sum_opp, linearity in D, and the normalization chain Σ p·lgZ = lgZ·Σ p = lgZ *)
          apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                           (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                           (opp (mult D (log Z Z_pos)))).
          { apply req_sum_opp. }
          { apply (req_trans (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                             (opp (mult D (sumf (fun s => mult (p s) (log Z Z_pos)))))
                             (opp (mult D (log Z Z_pos)))).
            { apply (req_opp_compat (sumf (fun s => mult D (mult (p s) (log Z Z_pos))))
                                    (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))).
              { apply (sum_linear D (fun s => mult (p s) (log Z Z_pos))). } }
            { apply (req_opp_compat (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))
                                    (mult D (log Z Z_pos))).
              { apply (req_mult_compat D D (sumf (fun s => mult (p s) (log Z Z_pos))) (log Z Z_pos)).
                { apply req_refl. }
                { apply (req_trans (sumf (fun s => mult (p s) (log Z Z_pos)))
                                   (sumf (fun s => mult (log Z Z_pos) (p s)))
                                   (log Z Z_pos)).
                  { apply (sum_ext (fun s => mult (p s) (log Z Z_pos)) (fun s => mult (log Z Z_pos) (p s))).
                    { intro s2. apply mult_comm. } }
                  { apply (req_trans (sumf (fun s => mult (log Z Z_pos) (p s)))
                                     (mult (log Z Z_pos) (sumf p))
                                     (log Z Z_pos)).
                    { apply (sum_linear (log Z Z_pos) p). }
                    { apply (req_trans (mult (log Z Z_pos) (sumf p))
                                       (mult (log Z Z_pos) one)
                                       (log Z Z_pos)).
                      { apply (req_mult_compat (log Z Z_pos) (log Z Z_pos) (sumf p) one).
                        { apply req_refl. }
                        { exact Hp. } }
                      { apply mult_one. } } } } } } }
  }
  }
  (* step 3: D·KL == B + opp A (upstream [Hkl]) *)
  assert (Hkl : req (mult D (sumf (fun s =>
                      mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                    (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                          (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
  { assert (Hpt2 : forall s : S,
        req (mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))
            (plus (mult (p s) (log (p s) (p0 s)))
                  (opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))).
    { intro s. unfold rminus_m2.
      apply (req_trans (mult (p s) (plus (log (p s) (p0 s)) (opp (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                       (plus (mult (p s) (log (p s) (p0 s))) (mult (p s) (opp (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                       (plus (mult (p s) (log (p s) (p0 s)))
                             (opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))).
      { apply distrib. }
      { apply (req_plus_compat (mult (p s) (log (p s) (p0 s))) (mult (p s) (log (p s) (p0 s)))
                               (mult (p s) (opp (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))
                               (opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))).
        { apply req_refl. }
        { apply req_mult_opp_l. } } }
    assert (Hinner : req (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                               (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
    { apply (req_trans (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                       (sumf (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                       (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                             (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
      { apply (sum_ext (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))
                       (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))).
        { exact Hpt2. } }
      { apply (req_trans (sumf (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s)))) (sumf (fun s => opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                               (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
        { apply sum_add. }
        { apply (req_plus_compat (sumf (fun s => mult (p s) (log (p s) (p0 s)))) (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                 (sumf (fun s => opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                                 (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))).
          { apply req_refl. }
          { apply req_sum_opp. } } } }
    apply (req_trans (mult D (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                     (mult D (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
    { apply (req_mult_compat D D
                             (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                             (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
      { apply req_refl. }
      { exact Hinner. } }
    apply (req_trans (mult D (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
    { apply distrib. }
    apply (req_plus_compat (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
    { apply req_refl. }
    { apply req_mult_opp_l. } }

  (* step 4: ring-algebra collapse (upstream [Hfin]: (opp A + opp DlgZ) + B -> opp DlgZ + (B + opp A)) *)
  assert (Hfin : req (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))
                     (plus (opp (mult D (log Z Z_pos))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))))).
  { set (A := (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))).
    set (DlgZ := (mult D (log Z Z_pos))).
    set (B := (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))).
    apply (req_trans (plus (plus (opp A) (opp DlgZ)) B)
                     (plus (opp A) (plus (opp DlgZ) B))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_sym (plus (opp A) (plus (opp DlgZ) B))
                     (plus (plus (opp A) (opp DlgZ)) B)).
      apply plus_assoc. }
    apply (req_trans (plus (opp A) (plus (opp DlgZ) B))
                     (plus (opp A) (plus B (opp DlgZ)))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_plus_compat (opp A) (opp A) (plus (opp DlgZ) B) (plus B (opp DlgZ))).
      { apply req_refl. }
      { apply plus_comm. } }
    apply (req_trans (plus (opp A) (plus B (opp DlgZ)))
                     (plus (plus (opp A) B) (opp DlgZ))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply plus_assoc. }
    apply (req_trans (plus (plus (opp A) B) (opp DlgZ))
                     (plus (plus B (opp A)) (opp DlgZ))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_plus_compat (plus (opp A) B) (plus B (opp A)) (opp DlgZ) (opp DlgZ)).
      { apply plus_comm. }
      { apply req_refl. } }
    apply plus_comm. }
  (* assembly: Hleg1 (conversion by unfolding the definition of [free_energy_m2 p], with [Hse] in the compat slot); Hleg2 ([Hfin] with [Hfb']/[Hkl] in the reverse closing slots) *)
  assert (Hleg1 : req (free_energy_m2 p p0) (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))).
  { unfold free_energy.
    apply (req_plus_compat (sumf (fun s => mult (p s) (base_loss s))) (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))).
    { exact Hse. }
    { apply req_refl. } }
  assert (Hleg2 : req (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))) (plus (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive) (mult D (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
  { apply (req_trans (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))
                      (plus (opp (mult D (log Z Z_pos))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))))
                      (plus (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive) (mult D (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
    { exact Hfin. }
    { apply (req_plus_compat (opp (mult D (log Z Z_pos))) (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
      { apply (req_sym (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive) (opp (mult D (log Z Z_pos)))). exact Hfb'. }
      { apply (req_sym (mult D (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))). exact Hkl. } } }
  exact (req_trans _ _ _ Hleg1 Hleg2).
Qed.

End ReqFECore.
(* ============================================================ *)
(* Part B. req-family restatement of the alignment layer             *)
(*   (template: the [Alignment] section of the ConstructiveWorld-     *)
(*   Main baseline, [L18734]-[L19158]).  Matrix correspondence:       *)
(*   4.1 rlhf_optimal <-> a_rlhf_optimal(_eps); 4.2 optimal_unique    *)
(*   <-> a_rlhf_optimal_unique; 4.3 rlhf_suboptimality_gap@L20554 <-> *)
(*   a_rlhf_suboptimality_gap; 4.4 rlhf_policy_improvement@L20591 <-> *)
(*   a_rlhf_policy_improvement; also dpo_optimal (theorem 5.2) and    *)
(*   a_fe_kl_decomp (the unified-view anchor rlhf_free_energy_kl@L20290). *)
(*   Honest bridges (req signatures of the upstream free lemmas):     *)
(*     b_gibbs_pos/b_gibbs_sum_eps (upstream gibbs_inequality L16629; *)
(*        resolved eps-wise by the Real-layer real_gibbs_inequality_eps L41704) *)
(*     b_log_exp_neg (resolved by [real_log_exp_neg]) / b_log_compat  *)
(*        (resolved by [real_log_wd]) / b_mult_cancel+b_gibbs_eq (the *)
(*        upstream field mult_cancel_l/log_eq_linear usage chain).    *)
(* ============================================================ *)
Section ReqAlignCore.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis asum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis asum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis asum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Hypothesis api_ref_pos : forall s : S, lt zero (pi_ref s).
Hypothesis api_ref_norm : req (sumf pi_ref) one.
Definition Z_align_a_sum : R :=
  sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Variable Z_align_a_pos : lt zero Z_align_a_sum.
Definition pdist_a (p : S -> R) : Set := forall s : S, lt zero (p s).
Definition nrm_a (p : S -> R) : Set := req (sumf p) one.
Definition rminus_a (a b : R) : R := plus a (opp b).
Definition align_energy_a (s : S) : R :=
  rminus_a (opp (reward s)) (mult beta (log (pi_ref s) (api_ref_pos s))).
Definition pi_star_a (s : S) : R :=
  mult (inv_pos Z_align_a_sum Z_align_a_pos)
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Definition kl_a (p q : S -> R) (Hp : pdist_a p) (Hq : pdist_a q) : R :=
  sumf (fun s => mult (p s) (rminus_a (log (p s) (Hp s)) (log (q s) (Hq s)))).
Definition fe_a (p : S -> R) (Hp : pdist_a p) : R :=
  plus (sumf (fun s => mult (p s) (align_energy_a s)))
       (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition J_a (p : S -> R) (Hp : pdist_a p) : R := opp (fe_a p Hp).

(* honest bridges *)
Hypothesis b_log_exp_neg :
  forall x : R, req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Hypothesis b_log_compat :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    req a b -> req (log a Ha) (log b Hb).
Hypothesis b_gibbs_pos :
  forall (p q : S -> R) (Hp : pdist_a p) (Hq : pdist_a q),
    nrm_a p -> nrm_a q -> le zero (kl_a p q Hp Hq).
Hypothesis b_gibbs_sum_eps :
  forall (p q : S -> R) (Hp : pdist_a p) (Hq : pdist_a q) (eps : R),
    lt zero eps -> le zero (plus (kl_a p q Hp Hq) eps).
Hypothesis b_mult_cancel :
  forall (a x : R), lt zero a -> req (mult a x) zero -> req x zero.
Hypothesis b_gibbs_eq :
  forall (p q : S -> R) (Hp : pdist_a p) (Hq : pdist_a q),
    req (kl_a p q Hp Hq) zero -> forall s : S, req (p s) (q s).

(* req compatibility of [exp_neg] (derived from [le_antisym] and [exp_neg_le_decr]) *)
Lemma a_exp_neg_ext : forall x y : R, req x y -> req (exp_neg x) (exp_neg y).
Proof.
  intros x y Hxy.
  apply le_antisym.
  - apply exp_neg_le_decr. apply (lt_le_iff y x). apply (inr (req_sym x y Hxy)).
  - apply exp_neg_le_decr. apply (lt_le_iff x y). apply (inr Hxy).
Qed.

(* alignment-energy closed-form exponential identity (req version of the upstream statement at [L18858]) *)
Lemma a_align_energy_exp :
  forall s : S, (req (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s))) (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Proof.
  intro s.
  unfold align_energy_a, rminus_a.
  assert (Hs1 : (req (mult (inv_pos beta beta_pos) (plus (opp (reward s)) (opp (mult beta (log (pi_ref s) (api_ref_pos s)))))) (plus (opp (mult (inv_pos beta beta_pos) (reward s))) (opp (log (pi_ref s) (api_ref_pos s)))))).
  { apply (req_trans (mult (inv_pos beta beta_pos) (plus (opp (reward s)) (opp (mult beta (log (pi_ref s) (api_ref_pos s)))))) (plus (mult (inv_pos beta beta_pos) (opp (reward s))) (mult (inv_pos beta beta_pos) (opp (mult beta (log (pi_ref s) (api_ref_pos s)))))) (plus (opp (mult (inv_pos beta beta_pos) (reward s))) (opp (log (pi_ref s) (api_ref_pos s))))).
      apply distrib.
      apply (req_plus_compat (mult (inv_pos beta beta_pos) (opp (reward s))) (opp (mult (inv_pos beta beta_pos) (reward s))) (mult (inv_pos beta beta_pos) (opp (mult beta (log (pi_ref s) (api_ref_pos s))))) (opp (log (pi_ref s) (api_ref_pos s)))).
        apply req_mult_opp_l.
        apply (req_trans (mult (inv_pos beta beta_pos) (opp (mult beta (log (pi_ref s) (api_ref_pos s))))) (opp (mult (inv_pos beta beta_pos) (mult beta (log (pi_ref s) (api_ref_pos s))))) (opp (log (pi_ref s) (api_ref_pos s)))).
          apply req_mult_opp_l.
          apply (req_opp_compat (mult (inv_pos beta beta_pos) (mult beta (log (pi_ref s) (api_ref_pos s)))) (log (pi_ref s) (api_ref_pos s))).
            apply (req_trans (mult (inv_pos beta beta_pos) (mult beta (log (pi_ref s) (api_ref_pos s)))) (mult (mult (inv_pos beta beta_pos) beta) (log (pi_ref s) (api_ref_pos s))) (log (pi_ref s) (api_ref_pos s))).
              apply mult_assoc.
              apply (req_trans (mult (mult (inv_pos beta beta_pos) beta) (log (pi_ref s) (api_ref_pos s))) (mult (mult beta (inv_pos beta beta_pos)) (log (pi_ref s) (api_ref_pos s))) (log (pi_ref s) (api_ref_pos s))).
                apply (req_mult_compat (mult (inv_pos beta beta_pos) beta) (mult beta (inv_pos beta beta_pos)) (log (pi_ref s) (api_ref_pos s)) (log (pi_ref s) (api_ref_pos s))).
                  apply mult_comm.
                  apply req_refl.
                apply (req_trans (mult (mult beta (inv_pos beta beta_pos)) (log (pi_ref s) (api_ref_pos s))) (mult one (log (pi_ref s) (api_ref_pos s))) (log (pi_ref s) (api_ref_pos s))).
                  apply (req_mult_compat (mult beta (inv_pos beta beta_pos)) one (log (pi_ref s) (api_ref_pos s)) (log (pi_ref s) (api_ref_pos s))).
                    apply inv_pos_correct.
                    apply req_refl.
                  apply req_mult_one_l.
  }
  apply (req_trans (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s))) (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (exp_neg (opp (log (pi_ref s) (api_ref_pos s))))) (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
    apply (req_trans (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s))) (exp_neg (plus (opp (mult (inv_pos beta beta_pos) (reward s))) (opp (log (pi_ref s) (api_ref_pos s))))) (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (exp_neg (opp (log (pi_ref s) (api_ref_pos s)))))).
      apply a_exp_neg_ext.
      exact Hs1.
      apply exp_neg_plus.
      assert (Hexpo : (req (exp_neg (opp (log (pi_ref s) (api_ref_pos s)))) (pi_ref s))).
      { apply (req_trans (exp_neg (opp (log (pi_ref s) (api_ref_pos s)))) (exp_neg (log_inv (pi_ref s) (api_ref_pos s))) (pi_ref s)).
          apply a_exp_neg_ext.
          apply (req_sym (log_inv (pi_ref s) (api_ref_pos s)) (opp (log (pi_ref s) (api_ref_pos s)))).
            apply log_inv_log.
          apply exp_neg_log_inv.
      }
      apply (req_trans (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (exp_neg (opp (log (pi_ref s) (api_ref_pos s))))) (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (pi_ref s)) (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
        exact (req_mult_compat (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (exp_neg (opp (log (pi_ref s) (api_ref_pos s)))) (pi_ref s) (req_refl (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))) Hexpo).
        apply mult_comm.
Qed.

(* ---- B2. alignment assembly (boltzmann assembly / partition / pi_star_pos / normalization) ---- *)
(* the alignment-frame Boltzmann assembly instantiates the Part A export [boltzmann_dist_m2]
   at the alignment parameters (the Part A section is closed by [End], so the export
   takes the explicit [S] argument) *)
Definition pb_a : S -> R :=
  boltzmann_dist_m2 S align_energy_a beta beta_pos Z_align_a_sum Z_align_a_pos.

(* transparent definition: taken directly from the Part A export [req_boltzmann_positive]
   (a conversion bridge between Qed-opaque terms — when a statement cites the Part A
   conclusion, the positivity proof slot must hold the delta-same term) *)
Definition a_pb_pos : pdist_a pb_a :=
  req_boltzmann_positive S align_energy_a beta beta_pos
                         Z_align_a_sum Z_align_a_pos.

Lemma a_partition : (req Z_align_a_sum (sumf (fun s => (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s)))))).
Proof.
  apply (asum_ext (fun s => (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))) (fun s => (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s))))).
    intro s. exact (req_sym (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s))) (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))) (a_align_energy_exp s)).
Qed.

Lemma a_pi_star_pos : forall s : S, lt zero (pi_star_a s).
Proof.
  intro s. unfold pi_star_a. apply mult_positive.
    apply inv_pos_pos.
    apply mult_positive.
      apply api_ref_pos.
      apply exp_neg_pos.
Qed.

Lemma a_boltzmann_is_pi_star : forall s : S, (req (pb_a s) (pi_star_a s)).
Proof.
  intro s. unfold pb_a, pi_star_a, boltzmann_dist_m2.
  apply (req_mult_compat (inv_pos Z_align_a_sum Z_align_a_pos) (inv_pos Z_align_a_sum Z_align_a_pos) (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s))) (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
    apply req_refl.
    exact (a_align_energy_exp s).
Qed.

Lemma a_pi_star_normalized : (req (sumf (fun s => (pi_star_a s))) one).
Proof.
  apply (req_trans (sumf (fun s => (pi_star_a s))) (mult (inv_pos Z_align_a_sum Z_align_a_pos) (sumf (fun s => (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))) one).
    apply (asum_linear (inv_pos Z_align_a_sum Z_align_a_pos) (fun s => (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))).
    apply (req_trans (mult (inv_pos Z_align_a_sum Z_align_a_pos) Z_align_a_sum) (mult Z_align_a_sum (inv_pos Z_align_a_sum Z_align_a_pos)) one).
      apply mult_comm.
      apply inv_pos_correct.
Qed.

Lemma a_pb_normalized : nrm_a pb_a.
Proof.
  apply (req_trans (sumf pb_a) (sumf (fun s => (pi_star_a s))) one).
    apply (asum_ext pb_a (fun s => (pi_star_a s))).
      intro s. exact (a_boltzmann_is_pi_star s).
    exact a_pi_star_normalized.
Qed.

(* ---- B3. extensionality of [fe_a] and of [kl_a] ---- *)
Lemma a_fe_ext :
  forall (f g : S -> R) (Hf : pdist_a f) (Hfg : forall s : S, req (f s) (g s)) (Hg : pdist_a g),
    req (fe_a f Hf) (fe_a g Hg).
Proof.
  intros f g Hf Hfg Hg.
  unfold fe_a.
  apply (req_plus_compat (sumf (fun s => (mult (f s) (align_energy_a s)))) (sumf (fun s => (mult (g s) (align_energy_a s)))) (mult beta (sumf (fun s => (mult (f s) (log (f s) (Hf s)))))) (mult beta (sumf (fun s => (mult (g s) (log (g s) (Hg s))))))).
    apply (asum_ext (fun s => (mult (f s) (align_energy_a s))) (fun s => (mult (g s) (align_energy_a s)))).
      intro s. exact (req_mult_compat (f s) (g s) (align_energy_a s) (align_energy_a s) (Hfg s) (req_refl (align_energy_a s))).
    apply (req_mult_compat beta beta (sumf (fun s => (mult (f s) (log (f s) (Hf s))))) (sumf (fun s => (mult (g s) (log (g s) (Hg s)))))).
      apply req_refl.
      apply (asum_ext (fun s => (mult (f s) (log (f s) (Hf s)))) (fun s => (mult (g s) (log (g s) (Hg s))))).
        intro s. exact (req_mult_compat (f s) (g s) (log (f s) (Hf s)) (log (g s) (Hg s)) (Hfg s)
                                        (b_log_compat (f s) (g s) (Hf s) (Hg s) (Hfg s))).
Qed.

Lemma a_KL_ext_r :
  forall (p q1 q2 : S -> R) (Hp : pdist_a p) (Hq1 : pdist_a q1) (Hq2 : pdist_a q2),
    (forall s : S, req (q1 s) (q2 s)) ->
    req (kl_a p q1 Hp Hq1) (kl_a p q2 Hp Hq2).
Proof.
  intros p q1 q2 Hp Hq1 Hq2 Hqq.
  apply (asum_ext (fun s => (mult (p s) (rminus_a (log (p s) (Hp s)) (log (q1 s) (Hq1 s)))))
                  (fun s => (mult (p s) (rminus_a (log (p s) (Hp s)) (log (q2 s) (Hq2 s)))))).
  intro s.
  apply (req_mult_compat (p s) (p s)
                         (rminus_a (log (p s) (Hp s)) (log (q1 s) (Hq1 s)))
                         (rminus_a (log (p s) (Hp s)) (log (q2 s) (Hq2 s)))).
    apply req_refl.
    apply (req_plus_compat (log (p s) (Hp s)) (log (p s) (Hp s))
                           (opp (log (q1 s) (Hq1 s))) (opp (log (q2 s) (Hq2 s)))).
      apply req_refl.
      apply (req_opp_compat (log (q1 s) (Hq1 s)) (log (q2 s) (Hq2 s))).
        apply b_log_compat.
        exact (Hqq s).
Qed.

(* fe_a(pb) == fe_a(pistar): the assembly bridge (shared by 4.2/4.3/4.4) *)
Lemma a_fe_boltzmann_pistar :
  req (fe_a pb_a a_pb_pos) (fe_a (fun s : S => pi_star_a s) a_pi_star_pos).
Proof.
  exact (a_fe_ext pb_a (fun s : S => pi_star_a s) a_pb_pos
           (fun s : S => a_boltzmann_is_pi_star s) a_pi_star_pos).
Qed.

(* ---- 4.1 alignment instance: F_a[p] == F_a[p_b] + beta·KL_a(p‖p_b) ---- *)
(* instantiates the Part A theorem [req_free_energy_kl_decomp] at the alignment
   parameters ([base_loss] := [align_energy_a], [D] := [beta], [Z] := [Z_align_a_sum]) *)
Lemma a_fe_kl_decomp :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p),
    req (fe_a p Hp)
        (plus (fe_a pb_a a_pb_pos)
              (mult beta (kl_a p pb_a Hp a_pb_pos))).
Proof.
  intros p Hn Hp.
  exact (req_free_energy_kl_decomp S sumf asum_ext asum_add asum_linear
           align_energy_a beta beta_pos Z_align_a_sum Z_align_a_pos
           a_partition b_log_exp_neg b_log_compat p Hn Hp).
Qed.

(* ---- 4.2 preliminary (eps-wise, F form): fe_a[p_b] <= fe_a[p] + beta·eps ---- *)
Lemma a_min_free_energy_eps :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p) (eps : R),
    lt zero eps ->
    le (fe_a pb_a a_pb_pos) (plus (fe_a p Hp) (mult beta eps)).
Proof.
  intros p Hn Hp eps Heps.
  assert (Hdec : (req (fe_a p Hp) (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))))
    by exact (a_fe_kl_decomp p Hn Hp).
  assert (Hg : (le zero (plus (kl_a p pb_a Hp a_pb_pos) eps)))
    by exact (b_gibbs_sum_eps p pb_a Hp a_pb_pos eps Heps).
  assert (Hd : (le zero (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps)))).
  { apply (le_trans zero (mult beta (plus (kl_a p pb_a Hp a_pb_pos) eps))
                     (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps))).
    - apply (le_id_r zero (mult (plus (kl_a p pb_a Hp a_pb_pos) eps) beta)
                     (mult beta (plus (kl_a p pb_a Hp a_pb_pos) eps))
                     (mult_comm (plus (kl_a p pb_a Hp a_pb_pos) eps) beta)
                     (le_id_l zero (mult zero beta)
                              (mult (plus (kl_a p pb_a Hp a_pb_pos) eps) beta)
                              (req_trans zero (mult beta zero) (mult zero beta)
                                         (req_sym (mult beta zero) zero (mult_zero beta))
                                         (mult_comm beta zero))
                              (le_mult_compat zero (plus (kl_a p pb_a Hp a_pb_pos) eps) beta beta_pos Hg))).
    - apply (lt_le_iff (mult beta (plus (kl_a p pb_a Hp a_pb_pos) eps))
                       (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps))).
      apply (inr (distrib beta (kl_a p pb_a Hp a_pb_pos) eps)). }
  assert (Hstart : (le (fe_a pb_a a_pb_pos) (plus (fe_a pb_a a_pb_pos) zero))).
  { apply (lt_le_iff (fe_a pb_a a_pb_pos) (plus (fe_a pb_a a_pb_pos) zero)).
    apply (inr (req_sym (plus (fe_a pb_a a_pb_pos) zero) (fe_a pb_a a_pb_pos)
                        (plus_zero (fe_a pb_a a_pb_pos)))). }
  apply (le_trans (fe_a pb_a a_pb_pos) (plus (fe_a pb_a a_pb_pos) zero)
                  (plus (fe_a p Hp) (mult beta eps))).
    exact Hstart.
    apply (le_trans (plus (fe_a pb_a a_pb_pos) zero)
                    (plus (fe_a pb_a a_pb_pos) (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps)))
                    (plus (fe_a p Hp) (mult beta eps))).
      apply (le_plus_compat (fe_a pb_a a_pb_pos) (fe_a pb_a a_pb_pos) zero
                            (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps))).
        apply le_refl.
        exact Hd.
      apply (lt_le_iff (plus (fe_a pb_a a_pb_pos) (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps)))
                       (plus (fe_a p Hp) (mult beta eps))).
        apply (inr (req_trans
                      (plus (fe_a pb_a a_pb_pos) (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps)))
                      (plus (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos))) (mult beta eps))
                      (plus (fe_a p Hp) (mult beta eps))
                      (plus_assoc (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps))
                      (req_plus_compat (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos))) (fe_a p Hp)
                                       (mult beta eps) (mult beta eps)
                                       (req_sym (fe_a p Hp)
                                                (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                                                Hdec)
                                       (req_refl (mult beta eps))))).
Qed.

(* ---- 4.2 main theorem (exact form; upstream rlhf_optimal@L19049): J(p) <= J(pistar) ---- *)
(* proof structure follows the upstream original: KL decomposition ⟹ F(pb) <= F(p) (KL>=0 bridge) ⟹ F(pb)==F(pistar)
   ⟹ substitution by [req_le_compat] ⟹ negation by [opp_le_compat]. *)
Theorem a_rlhf_optimal :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p),
    le (J_a p Hp) (J_a pi_star_a a_pi_star_pos).
Proof.
  intros p Hn Hp.
  unfold J_a.
  assert (Hkl0 : (le zero (kl_a p pb_a Hp a_pb_pos)))
    by exact (b_gibbs_pos p pb_a Hp a_pb_pos Hn a_pb_normalized).
  assert (Hklb : (le zero (mult beta (kl_a p pb_a Hp a_pb_pos)))).
  { apply (le_id_r zero (mult (kl_a p pb_a Hp a_pb_pos) beta)
                   (mult beta (kl_a p pb_a Hp a_pb_pos))
                   (mult_comm (kl_a p pb_a Hp a_pb_pos) beta)
                   (le_id_l zero (mult zero beta) (mult (kl_a p pb_a Hp a_pb_pos) beta)
                            (req_trans zero (mult beta zero) (mult zero beta)
                                       (req_sym (mult beta zero) zero (mult_zero beta))
                                       (mult_comm beta zero))
                            (le_mult_compat zero (kl_a p pb_a Hp a_pb_pos) beta beta_pos Hkl0))). }
  assert (Hmin : (le (fe_a pb_a a_pb_pos) (fe_a p Hp))).
  { apply (le_id_r (fe_a pb_a a_pb_pos)
                   (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                   (fe_a p Hp)
                   (req_sym (fe_a p Hp)
                            (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                            (a_fe_kl_decomp p Hn Hp))
                   (le_id_l (fe_a pb_a a_pb_pos) (plus (fe_a pb_a a_pb_pos) zero)
                            (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                            (req_sym (plus (fe_a pb_a a_pb_pos) zero) (fe_a pb_a a_pb_pos)
                                     (plus_zero (fe_a pb_a a_pb_pos)))
                            (le_plus_compat (fe_a pb_a a_pb_pos) (fe_a pb_a a_pb_pos) zero
                                            (mult beta (kl_a p pb_a Hp a_pb_pos))
                                            (le_refl (fe_a pb_a a_pb_pos)) Hklb))). }
  apply (opp_le_compat (fe_a (fun s : S => pi_star_a s) a_pi_star_pos) (fe_a p Hp)).
  apply (req_le_compat (fe_a pb_a a_pb_pos) (fe_a (fun s : S => pi_star_a s) a_pi_star_pos)
                       (fe_a p Hp) (fe_a p Hp)
                       a_fe_boltzmann_pistar (req_refl (fe_a p Hp)) Hmin).
Qed.

(* ---- 4.2 main theorem (Bishop eps-wise form; upstream real_rlhf_optimal_eps@L43804):
   J(p) <= J(pistar) + beta·eps ---------------------------------------------- *)
(* ring-closing identity: A + opp X <= B ⟹ A <= B + X (req version of the isomorphic Real-layer step) *)
Theorem a_rlhf_optimal_eps :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p) (eps : R),
    lt zero eps ->
    le (J_a p Hp) (plus (J_a pi_star_a a_pi_star_pos) (mult beta eps)).
Proof.
  intros p Hn Hp eps Heps.
  unfold J_a.
  assert (Hmin : (le (fe_a pb_a a_pb_pos) (plus (fe_a p Hp) (mult beta eps))))
    by exact (a_min_free_energy_eps p Hn Hp eps Heps).
  assert (Hopp : (le (opp (plus (fe_a p Hp) (mult beta eps))) (opp (fe_a pb_a a_pb_pos))))
    by exact (opp_le_compat (fe_a pb_a a_pb_pos) (plus (fe_a p Hp) (mult beta eps)) Hmin).
  assert (H3a : (le (plus (opp (fe_a p Hp)) (opp (mult beta eps))) (opp (fe_a pb_a a_pb_pos)))).
  { apply (le_id_l (plus (opp (fe_a p Hp)) (opp (mult beta eps)))
                   (opp (plus (fe_a p Hp) (mult beta eps)))
                   (opp (fe_a pb_a a_pb_pos))).
    - exact (req_sym (opp (plus (fe_a p Hp) (mult beta eps)))
                     (plus (opp (fe_a p Hp)) (opp (mult beta eps)))
                     (req_opp_plus (fe_a p Hp) (mult beta eps))).
    - exact Hopp. }
  assert (H3b : (le (plus (plus (opp (fe_a p Hp)) (opp (mult beta eps))) (mult beta eps))
                    (plus (opp (fe_a pb_a a_pb_pos)) (mult beta eps)))).
  { apply (le_plus_compat (plus (opp (fe_a p Hp)) (opp (mult beta eps)))
                          (opp (fe_a pb_a a_pb_pos))
                          (mult beta eps) (mult beta eps)).
    - exact H3a.
    - apply le_refl. }
  assert (H3c : (req (opp (fe_a p Hp)) (plus (plus (opp (fe_a p Hp)) (opp (mult beta eps))) (mult beta eps)))).
  { apply (req_trans (opp (fe_a p Hp)) (plus (opp (fe_a p Hp)) zero)
                     (plus (plus (opp (fe_a p Hp)) (opp (mult beta eps))) (mult beta eps))).
    - exact (req_sym (plus (opp (fe_a p Hp)) zero) (opp (fe_a p Hp)) (plus_zero (opp (fe_a p Hp)))).
    - apply (req_trans (plus (opp (fe_a p Hp)) zero)
                       (plus (opp (fe_a p Hp)) (plus (opp (mult beta eps)) (mult beta eps)))
                       (plus (plus (opp (fe_a p Hp)) (opp (mult beta eps))) (mult beta eps))).
      + apply (req_plus_compat (opp (fe_a p Hp)) (opp (fe_a p Hp)) zero (plus (opp (mult beta eps)) (mult beta eps))).
        * apply req_refl.
        * apply (req_sym (plus (opp (mult beta eps)) (mult beta eps)) zero).
          apply (req_trans (plus (opp (mult beta eps)) (mult beta eps)) (plus (mult beta eps) (opp (mult beta eps))) zero).
          -- apply plus_comm.
          -- apply plus_opp.
      + apply plus_assoc. }
  assert (Hs3 : (le (opp (fe_a p Hp)) (plus (opp (fe_a pb_a a_pb_pos)) (mult beta eps)))).
  { apply (le_id_l (opp (fe_a p Hp))
                   (plus (plus (opp (fe_a p Hp)) (opp (mult beta eps))) (mult beta eps))
                   (plus (opp (fe_a pb_a a_pb_pos)) (mult beta eps))).
    - exact H3c.
    - exact H3b. }
  apply (le_id_r (opp (fe_a p Hp))
                 (plus (opp (fe_a pb_a a_pb_pos)) (mult beta eps))
                 (plus (opp (fe_a (fun s : S => pi_star_a s) a_pi_star_pos)) (mult beta eps))).
    - apply (req_plus_compat (opp (fe_a pb_a a_pb_pos))
                             (opp (fe_a (fun s : S => pi_star_a s) a_pi_star_pos))
                             (mult beta eps) (mult beta eps)).
      + apply (req_opp_compat (fe_a pb_a a_pb_pos) (fe_a (fun s : S => pi_star_a s) a_pi_star_pos)).
        exact a_fe_boltzmann_pistar.
      + apply req_refl.
    - exact Hs3.
Qed.

(* ---- 4.3b DPO optimality (upstream dpo_optimal@L19096) ----
   DPO implicit-reward concretization: the DPO loss = -J(pi), a direct corollary of [a_rlhf_optimal]. *)
Definition dpo_loss_a (p : S -> R) (Hp : pdist_a p) : R := opp (J_a p Hp).

Theorem a_dpo_optimal :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p),
    le (dpo_loss_a pi_star_a a_pi_star_pos) (dpo_loss_a p Hp).
Proof.
  intros p Hn Hp. unfold dpo_loss_a.
  apply (opp_le_compat (J_a p Hp) (J_a pi_star_a a_pi_star_pos)).
    exact (a_rlhf_optimal p Hn Hp).
Qed.

(* ---- 4.4 uniqueness (upstream rlhf_optimal_unique@L19128) ----
   J(p) == J(pistar) ⟹ p == pistar (pointwise).
   Elimination chain: goal equality ⟹ F equality ⟹ beta·KL == 0 (additive cancellation) ⟹ KL == 0
   ([b_mult_cancel]) ⟹ pointwise ([b_gibbs_eq]) ⟹ substitution to [pi_star].  The req world has no
   destruct/eq_ind injective elimination; this chain mirrors the cancellation engine of Part C. *)
Lemma a_add_cancel_r : forall (u v w : R), req (plus u v) (plus u w) -> req v w.
Proof.
  intros u v w H.
  apply (req_add_cancel_l v u w).
  apply (req_trans (plus v u) (plus u v) (plus w u)).
    apply plus_comm.
    apply (req_trans (plus u v) (plus u w) (plus w u)).
      exact H.
      apply plus_comm.
Qed.

Theorem a_rlhf_optimal_unique :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p),
    req (J_a p Hp) (J_a pi_star_a a_pi_star_pos) ->
    forall s : S, req (p s) (pi_star_a s).
Proof.
  intros p Hn Hp HJ s.
  unfold J_a in HJ.
  assert (Hfe : (req (fe_a p Hp) (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos))).
  { exact (req_trans (fe_a p Hp) (opp (opp (fe_a p Hp)))
                     (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos)
                     (req_sym (opp (opp (fe_a p Hp))) (fe_a p Hp) (req_double_neg (fe_a p Hp)))
                     (req_trans (opp (opp (fe_a p Hp)))
                                (opp (opp (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos)))
                                (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos)
                                (req_opp_compat (opp (fe_a p Hp))
                                                (opp (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos))
                                                HJ)
                                (req_double_neg (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos)))). }
  assert (Hfe0 : (req (fe_a p Hp) (fe_a pb_a a_pb_pos)))
    by exact (req_trans (fe_a p Hp) (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos)
                        (fe_a pb_a a_pb_pos) Hfe
                        (req_sym (fe_a pb_a a_pb_pos)
                                 (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos)
                                 a_fe_boltzmann_pistar)).
  assert (Hdec : (req (fe_a p Hp) (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))))
    by exact (a_fe_kl_decomp p Hn Hp).
  assert (H1 : (req (fe_a pb_a a_pb_pos) (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))))
    by exact (req_trans (fe_a pb_a a_pb_pos) (fe_a p Hp)
                        (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                        (req_sym (fe_a p Hp) (fe_a pb_a a_pb_pos) Hfe0) Hdec).
  assert (H2 : (req (mult beta (kl_a p pb_a Hp a_pb_pos)) zero)).
  { apply (a_add_cancel_r (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)) zero).
    exact (req_trans (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                     (fe_a pb_a a_pb_pos)
                     (plus (fe_a pb_a a_pb_pos) zero)
                     (req_sym (fe_a pb_a a_pb_pos)
                              (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                              H1)
                     (req_sym (plus (fe_a pb_a a_pb_pos) zero) (fe_a pb_a a_pb_pos)
                              (plus_zero (fe_a pb_a a_pb_pos)))). }
  assert (H3 : (req (kl_a p pb_a Hp a_pb_pos) zero))
    by exact (b_mult_cancel beta (kl_a p pb_a Hp a_pb_pos) beta_pos H2).
  exact (req_trans (p s) (pb_a s) (pi_star_a s)
                   (b_gibbs_eq p pb_a Hp a_pb_pos H3 s)
                   (a_boltzmann_is_pi_star s)).
Qed.

(* ---- 4.3 suboptimality gap (upstream rlhf_suboptimality_gap@L20554) ----
   J(pistar) − J(p) == beta·KL(p‖pistar) (explicit forward KL value).
   Chain: the 4.1 alignment-instance KL decomposition ([a_fe_kl_decomp]) + the pb==pistar double
   substitution (left F argument via [a_fe_boltzmann_pistar], right KL argument via [a_KL_ext_r])
   + the double-negation elimination of J = −F ([req_double_neg]) + the ring closing
   A + opp(A+X) == X ([plus_assoc] with [plus_comm]/[plus_opp] cancellation).  A pure
   [req_trans] chain, no destruct. *)
Theorem a_rlhf_suboptimality_gap :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p),
    req (rminus_a (J_a pi_star_a a_pi_star_pos) (J_a p Hp))
        (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)).
Proof.
  intros p Hn Hp.
  assert (Hkl : (req (kl_a p pb_a Hp a_pb_pos)
                     (kl_a p pi_star_a Hp a_pi_star_pos)))
    by exact (a_KL_ext_r p pb_a pi_star_a Hp a_pb_pos a_pi_star_pos
                (fun s0 : S => a_boltzmann_is_pi_star s0)).
  assert (Hdec : (req (fe_a p Hp)
                      (plus (fe_a pi_star_a a_pi_star_pos)
                            (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))))
    by exact (req_trans (fe_a p Hp)
               (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
               (plus (fe_a pi_star_a a_pi_star_pos)
                     (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))
               (a_fe_kl_decomp p Hn Hp)
               (req_plus_compat (fe_a pb_a a_pb_pos)
                                (fe_a pi_star_a a_pi_star_pos)
                                (mult beta (kl_a p pb_a Hp a_pb_pos))
                                (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))
                                a_fe_boltzmann_pistar
                                (req_mult_compat beta beta
                                   (kl_a p pb_a Hp a_pb_pos)
                                   (kl_a p pi_star_a Hp a_pi_star_pos)
                                   (req_refl beta) Hkl))).
  (* fe-form gap: opp F* + Fp == beta·KL (ring closing A + opp(A+X) == X) *)
  assert (Hgapfe : (req (plus (opp (fe_a pi_star_a a_pi_star_pos)) (fe_a p Hp))
                        (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))).
  { apply (req_trans (plus (opp (fe_a pi_star_a a_pi_star_pos)) (fe_a p Hp))
                     (plus (opp (fe_a pi_star_a a_pi_star_pos))
                           (plus (fe_a pi_star_a a_pi_star_pos)
                                 (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))))
                     (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))).
    - apply (req_plus_compat (opp (fe_a pi_star_a a_pi_star_pos))
                             (opp (fe_a pi_star_a a_pi_star_pos))
                             (fe_a p Hp)
                             (plus (fe_a pi_star_a a_pi_star_pos)
                                   (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))).
      + apply req_refl.
      + exact Hdec.
    - apply (req_trans (plus (opp (fe_a pi_star_a a_pi_star_pos))
                             (plus (fe_a pi_star_a a_pi_star_pos)
                                   (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))))
                       (plus (plus (opp (fe_a pi_star_a a_pi_star_pos))
                                   (fe_a pi_star_a a_pi_star_pos))
                             (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))
                       (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))).
      + apply plus_assoc.
      + apply (req_trans (plus (plus (opp (fe_a pi_star_a a_pi_star_pos))
                                     (fe_a pi_star_a a_pi_star_pos))
                               (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))
                         (plus zero (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))
                         (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))).
        * apply (req_plus_compat (plus (opp (fe_a pi_star_a a_pi_star_pos))
                                       (fe_a pi_star_a a_pi_star_pos))
                                 zero
                                 (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))
                                 (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))).
          -- exact (req_trans (plus (opp (fe_a pi_star_a a_pi_star_pos))
                                    (fe_a pi_star_a a_pi_star_pos))
                              (plus (fe_a pi_star_a a_pi_star_pos)
                                    (opp (fe_a pi_star_a a_pi_star_pos)))
                              zero
                              (plus_comm (opp (fe_a pi_star_a a_pi_star_pos))
                                         (fe_a pi_star_a a_pi_star_pos))
                              (plus_opp (fe_a pi_star_a a_pi_star_pos))).
          -- apply req_refl.
        * apply (req_trans (plus zero (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))
                           (plus (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)) zero)
                           (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))).
          -- apply plus_comm.
          -- apply plus_zero. }
  (* J-form exit: rminus_a J* Jp == opp F* + opp (opp Fp) == opp F* + Fp (delta plus double negation) *)
  exact (req_trans (rminus_a (J_a pi_star_a a_pi_star_pos) (J_a p Hp))
                   (plus (opp (fe_a pi_star_a a_pi_star_pos))
                         (opp (opp (fe_a p Hp))))
                   (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))
                   (req_refl (rminus_a (J_a pi_star_a a_pi_star_pos) (J_a p Hp)))
                   (req_trans (plus (opp (fe_a pi_star_a a_pi_star_pos))
                                    (opp (opp (fe_a p Hp))))
                              (plus (opp (fe_a pi_star_a a_pi_star_pos)) (fe_a p Hp))
                              (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))
                              (req_plus_compat (opp (fe_a pi_star_a a_pi_star_pos))
                                               (opp (fe_a pi_star_a a_pi_star_pos))
                                               (opp (opp (fe_a p Hp))) (fe_a p Hp)
                                               (req_refl (opp (fe_a pi_star_a a_pi_star_pos)))
                                               (req_double_neg (fe_a p Hp)))
                              Hgapfe)).
Qed.

(* ---- 4.4 policy-improvement monotonicity (upstream rlhf_policy_improvement@L20591) ----
   KL(p_new‖pistar) <= KL(p_old‖pistar) ⟹ J(p_old) <= J(p_new).
   Chain: the 4.3 gap identity twice (J* − Jq == β·KLq) + order preservation under the
   multiplier β>0 ([le_mult_compat] with a [mult_comm] double rewrite into the left-multiplication
   position) + adding opp J* to both sides ([le_plus_compat])
   + the cancellation string opp J* + (J* + opp Jq) == opp Jq + finishing with the double negation of [opp_le_compat]. *)
Theorem a_rlhf_policy_improvement :
  forall (p_old p_new : S -> R)
         (Hn1 : nrm_a p_old) (Hp1 : pdist_a p_old)
         (Hn2 : nrm_a p_new) (Hp2 : pdist_a p_new),
    le (kl_a p_new pi_star_a Hp2 a_pi_star_pos)
       (kl_a p_old pi_star_a Hp1 a_pi_star_pos) ->
    le (J_a p_old Hp1) (J_a p_new Hp2).
Proof.
  intros p_old p_new Hn1 Hp1 Hn2 Hp2 Hkldec.
  assert (Hbeta : (le (mult beta (kl_a p_new pi_star_a Hp2 a_pi_star_pos))
                      (mult beta (kl_a p_old pi_star_a Hp1 a_pi_star_pos)))).
  { exact (le_id_r (mult beta (kl_a p_new pi_star_a Hp2 a_pi_star_pos))
                   (mult (kl_a p_old pi_star_a Hp1 a_pi_star_pos) beta)
                   (mult beta (kl_a p_old pi_star_a Hp1 a_pi_star_pos))
                   (mult_comm (kl_a p_old pi_star_a Hp1 a_pi_star_pos) beta)
                   (le_id_l (mult beta (kl_a p_new pi_star_a Hp2 a_pi_star_pos))
                            (mult (kl_a p_new pi_star_a Hp2 a_pi_star_pos) beta)
                            (mult (kl_a p_old pi_star_a Hp1 a_pi_star_pos) beta)
                            (mult_comm beta (kl_a p_new pi_star_a Hp2 a_pi_star_pos))
                            (le_mult_compat (kl_a p_new pi_star_a Hp2 a_pi_star_pos)
                                            (kl_a p_old pi_star_a Hp1 a_pi_star_pos)
                                            beta beta_pos Hkldec))). }
  (* cancellation string: opp J* + (J* + opp Jq) == opp Jq (the J-form of A+opp(A+X)==X) *)
  assert (Hsimpl : forall (q : S -> R) (Hq : pdist_a q),
    req (plus (opp (J_a pi_star_a a_pi_star_pos))
              (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a q Hq))))
        (opp (J_a q Hq))).
  { intros q Hq.
    apply (req_trans (plus (opp (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a q Hq))))
                     (plus (plus (opp (J_a pi_star_a a_pi_star_pos))
                                 (J_a pi_star_a a_pi_star_pos))
                           (opp (J_a q Hq)))
                     (opp (J_a q Hq))).
    - apply plus_assoc.
    - apply (req_trans (plus (plus (opp (J_a pi_star_a a_pi_star_pos))
                                   (J_a pi_star_a a_pi_star_pos))
                             (opp (J_a q Hq)))
                       (plus zero (opp (J_a q Hq)))
                       (opp (J_a q Hq))).
      + apply (req_plus_compat (plus (opp (J_a pi_star_a a_pi_star_pos))
                                     (J_a pi_star_a a_pi_star_pos))
                               zero
                               (opp (J_a q Hq)) (opp (J_a q Hq))).
        * exact (req_trans (plus (opp (J_a pi_star_a a_pi_star_pos))
                                 (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos)
                                 (opp (J_a pi_star_a a_pi_star_pos)))
                           zero
                           (plus_comm (opp (J_a pi_star_a a_pi_star_pos))
                                      (J_a pi_star_a a_pi_star_pos))
                           (plus_opp (J_a pi_star_a a_pi_star_pos))).
        * apply req_refl.
      + apply (req_trans (plus zero (opp (J_a q Hq)))
                         (plus (opp (J_a q Hq)) zero)
                         (opp (J_a q Hq))).
        * apply plus_comm.
        * apply plus_zero. }
  (* J* − J_new <= J* − J_old (the 4.3 identity substituted twice, with order preservation under β) *)
  assert (Hadd : (le (plus (opp (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_new Hp2))))
                     (plus (opp (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_old Hp1)))))).
  { apply (le_plus_compat (opp (J_a pi_star_a a_pi_star_pos))
                          (opp (J_a pi_star_a a_pi_star_pos))
                          (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_new Hp2)))
                          (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_old Hp1)))
                          (le_refl (opp (J_a pi_star_a a_pi_star_pos)))).
    apply (le_id_l (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_new Hp2)))
                   (mult beta (kl_a p_new pi_star_a Hp2 a_pi_star_pos))
                   (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_old Hp1)))).
    - exact (a_rlhf_suboptimality_gap p_new Hn2 Hp2).
    - apply (le_id_r (mult beta (kl_a p_new pi_star_a Hp2 a_pi_star_pos))
                     (mult beta (kl_a p_old pi_star_a Hp1 a_pi_star_pos))
                     (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_old Hp1)))
                     (req_sym (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_old Hp1)))
                              (mult beta (kl_a p_old pi_star_a Hp1 a_pi_star_pos))
                              (a_rlhf_suboptimality_gap p_old Hn1 Hp1))
                     Hbeta). }
  assert (Hopp : (le (opp (J_a p_new Hp2)) (opp (J_a p_old Hp1)))).
  { apply (le_id_l (opp (J_a p_new Hp2))
                   (plus (opp (J_a pi_star_a a_pi_star_pos))
                         (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_new Hp2))))
                   (opp (J_a p_old Hp1))).
    - exact (req_sym (plus (opp (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_new Hp2))))
                     (opp (J_a p_new Hp2))
                     (Hsimpl p_new Hp2)).
    - apply (le_id_r (plus (opp (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_new Hp2))))
                     (plus (opp (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_old Hp1))))
                     (opp (J_a p_old Hp1))
                     (Hsimpl p_old Hp1) Hadd). }
  exact (le_id_l (J_a p_old Hp1)
                 (opp (opp (J_a p_old Hp1)))
                 (J_a p_new Hp2)
                 (req_sym (opp (opp (J_a p_old Hp1))) (J_a p_old Hp1)
                          (req_double_neg (J_a p_old Hp1)))
                 (le_id_r (opp (opp (J_a p_old Hp1)))
                          (opp (opp (J_a p_new Hp2)))
                          (J_a p_new Hp2)
                          (req_double_neg (J_a p_new Hp2))
                          (opp_le_compat (opp (J_a p_new Hp2)) (opp (J_a p_old Hp1)) Hopp))).
Qed.

End ReqAlignCore.
(* ============================================================ *)
(* Part C. Two-state concrete instance assembly and end-to-end theorems *)
(*   [R] := [Real] (resolved by the instance [RealEnhancedReal];         *)
(*   [req] ≡ [real_eq]), [S] := [bool] (two states),                     *)
(*   [sumf] := [real_list_sum] over [true; false].                       *)
(*   Chain: concrete instance assembly -> use of the §4.1 core theorems  *)
(*   -> extraction check ([Obj.magic] = 0).                              *)
(* ============================================================ *)

Definition bsum (f : bool -> Real) : Real :=
  real_list_sum bool f (cons true (cons false nil)).

(* ---- instance assembly: resolving the three summation properties (from the base [real_list_sum] lemmas) ---- *)
Lemma c_sum_ext :
  forall f g : bool -> Real, (forall s : bool, req (f s) (g s)) -> req (bsum f) (bsum g).
Proof.
  intros f g H.
  exact (real_list_sum_ext bool f g (true :: false :: nil) H).
Qed.

Lemma c_sum_add :
  forall f g : bool -> Real,
    req (bsum (fun s : bool => real_plus (f s) (g s)))
        (real_plus (bsum f) (bsum g)).
Proof.
  intros f g.
  exact (real_list_sum_add bool f g (true :: false :: nil)).
Qed.

Lemma c_sum_linear :
  forall (a : Real) (f : bool -> Real),
    req (bsum (fun s : bool => real_mult a (f s))) (real_mult a (bsum f)).
Proof.
  intros a f.
  exact (real_list_sum_linear bool a f (true :: false :: nil)).
Qed.

(* ---- instance parameters: D := 1, Z := 2 (all concrete constructions) ---- *)
Definition two_state_loss : bool -> Real := fun _ : bool => real_zero.
Definition two_state_Z : Real := real_plus real_one real_one.
Definition two_state_Z_pos : lt zero two_state_Z :=
  real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one.

(* transparent definition: collects the instance-evar fragility that tactic-mode unification
   would otherwise meet (the conversion is settled at the kernel [Definition] layer) *)
Definition two_state_inv_one : Real := inv_pos real_one real_lt_zero_one.

Lemma c_exp_neg_zero :
  req (exp_neg (mult (two_state_inv_one) real_zero)) real_one.
Proof.
  exact (req_trans (exp_neg (mult (two_state_inv_one) real_zero))
                   (exp_neg real_zero) real_one
                   (req_exp_neg_ext (mult (two_state_inv_one) real_zero)
                                    real_zero
                                    (mult_zero (two_state_inv_one)))
                   exp_neg_zero).
Qed.

(* partition resolution: e^{-0}+e^{-0} == 1+1 == Z (pure instance algebra).
   Proof note: the chain is split into the two steps [H1]/[H2] because a monolithic term
   would unfold the parameterless class fields node by node through the global-instance
   projections at superlinear cost; the statement is unchanged, fully constructive, and no
   new premises are introduced. *)
Lemma c_partition :
  req two_state_Z
      (bsum (fun s : bool => exp_neg (mult (two_state_inv_one) real_zero))).
Proof.
  set (e := exp_neg (mult (two_state_inv_one) real_zero)).
  assert (H1 : req two_state_Z (real_plus e e)).
  { exact (req_plus_compat real_one e real_one e
             (req_sym e real_one c_exp_neg_zero)
             (req_sym e real_one c_exp_neg_zero)). }
  assert (H2 : req (real_plus e e)
                   (bsum (fun s : bool => exp_neg (mult (two_state_inv_one) real_zero)))).
  { exact (req_sym (real_plus e (real_plus e zero)) (real_plus e e)
             (req_plus_compat e e (real_plus e zero) e
                (req_refl e) (plus_zero e))). }
  exact (req_trans two_state_Z (real_plus e e)
                   (bsum (fun s : bool => exp_neg (mult (two_state_inv_one) real_zero)))
                   H1 H2).
Qed.

(* ---- assembly: the Boltzmann distribution and its positivity (instantiating the Part A exports) ---- *)
Definition two_state_boltz : bool -> Real :=
  boltzmann_dist_m2 bool two_state_loss real_one real_lt_zero_one
                    two_state_Z two_state_Z_pos.

Definition two_state_boltz_pos : forall s : bool, lt zero (two_state_boltz s) :=
  req_boltzmann_positive bool two_state_loss real_one real_lt_zero_one
                         two_state_Z two_state_Z_pos.

(* ============================================================ *)
(* End-to-end main theorem #1: use of the §4.1 core theorem [req_free_energy_boltzmann] *)

(* ============================================================ *)
Theorem two_state_free_energy_boltzmann :
  req (free_energy_m2 bool bsum two_state_loss real_one
           two_state_boltz two_state_boltz_pos)
      (opp (mult real_one (log two_state_Z two_state_Z_pos))).
Proof.
  exact (req_free_energy_boltzmann bool bsum c_sum_ext c_sum_add c_sum_linear
           two_state_loss real_one real_lt_zero_one two_state_Z two_state_Z_pos
           c_partition real_log_exp_neg real_log_wd).
Qed.

(* ---- the uniform policy p_u = (1/2, 1/2), its positivity and normalization ---- *)
Definition two_state_pu : bool -> Real :=
  fun _ : bool => inv_pos two_state_Z two_state_Z_pos.

Lemma two_state_pu_pos : forall s : bool, lt zero (two_state_pu s).
Proof.
  intro s. exact (inv_pos_pos two_state_Z two_state_Z_pos).
Qed.

(* left-multiplication cancellation engine (t > 0, req (t·x) (t·y) ⟹ req x y; the req world has
   no destruct injective elimination, so the engine is built as an [inv_pos_correct] ring chain) *)
Lemma c_mult_cancel_l :
  forall (t x y : Real), lt zero t -> req (mult t x) (mult t y) -> req x y.
Proof.
  intros t x y Ht H.
  assert (Hix1 : req (mult (inv_pos t Ht) t) one).
  { exact (req_trans (mult (inv_pos t Ht) t) (mult t (inv_pos t Ht)) one
                     (mult_comm (inv_pos t Ht) t) (inv_pos_correct t Ht)). }
  exact (req_trans x (mult (mult (inv_pos t Ht) t) x) y
           (req_trans x (mult one x) (mult (mult (inv_pos t Ht) t) x)
              (req_sym (mult one x) x (req_mult_one_l x))
              (req_mult_compat one (mult (inv_pos t Ht) t) x x
                 (req_sym (mult (inv_pos t Ht) t) one Hix1) (req_refl x)))
           (req_trans (mult (mult (inv_pos t Ht) t) x) (mult (inv_pos t Ht) (mult t x)) y
              (req_sym (mult (inv_pos t Ht) (mult t x)) (mult (mult (inv_pos t Ht) t) x)
                 (mult_assoc (inv_pos t Ht) t x))
              (req_trans (mult (inv_pos t Ht) (mult t x)) (mult (inv_pos t Ht) (mult t y)) y
                 (req_mult_compat (inv_pos t Ht) (inv_pos t Ht) (mult t x) (mult t y)
                    (req_refl (inv_pos t Ht)) H)
                 (req_trans (mult (inv_pos t Ht) (mult t y)) (mult (mult (inv_pos t Ht) t) y) y
                    (mult_assoc (inv_pos t Ht) t y)
                    (req_trans (mult (mult (inv_pos t Ht) t) y) (mult one y) y
                       (req_mult_compat (mult (inv_pos t Ht) t) one y y Hix1 (req_refl y))
                       (req_mult_one_l y)))))).
Qed.

(* normalization of p_u: 1/2 + 1/2 == 1 (the cancellation engine applied to 2·pair == 2·1).
   Proof note: the intermediate steps are written on the real face directly ([real_eq]/
   [real_plus]/[real_mult] via the S02 lemmas [real_eq_trans]/[real_eq_sym]/[real_eq_refl],
   [real_distrib], [real_plus_zero], [real_mult_one], the S03 [real_inv_pos_correct], and the
   S07 [RealSetoid.real_eq_plus_compat_adapt]), so record unfolding remains confined to a few
   boundary positions (the statement is unchanged, fully constructive, and no new premises
   are introduced). *)
Lemma c_pu_normalized : req (bsum two_state_pu) one.
Proof.
  set (u := real_inv_pos two_state_Z two_state_Z_pos).
  assert (Hd1 : real_eq (real_plus (real_mult two_state_Z u) (real_mult two_state_Z u))
                        (real_mult two_state_Z one)).
  { exact (real_eq_trans (real_plus (real_mult two_state_Z u) (real_mult two_state_Z u))
                         two_state_Z (real_mult two_state_Z one)
             (RealSetoid.real_eq_plus_compat_adapt (real_mult two_state_Z u) real_one
                              (real_mult two_state_Z u) real_one
                              (real_inv_pos_correct two_state_Z two_state_Z_pos)
                              (real_inv_pos_correct two_state_Z two_state_Z_pos))
             (real_eq_sym (real_mult two_state_Z one) two_state_Z
                          (real_mult_one two_state_Z))). }
  assert (Hd : real_eq (real_mult two_state_Z (real_plus u u))
                       (real_mult two_state_Z one)).
  { exact (real_eq_trans (real_mult two_state_Z (real_plus u u))
                         (real_plus (real_mult two_state_Z u) (real_mult two_state_Z u))
                         (real_mult two_state_Z one)
                         (real_distrib two_state_Z u u) Hd1). }
  assert (Hc : real_eq (real_plus u u) real_one).
  { exact (c_mult_cancel_l two_state_Z (real_plus u u) real_one two_state_Z_pos Hd). }
  assert (Hs : real_eq (bsum two_state_pu) (real_plus u u)).
  { exact (RealSetoid.real_eq_plus_compat_adapt u u (real_plus u real_zero) u
             (real_eq_refl u) (real_plus_zero u)). }
  exact (real_eq_trans (bsum two_state_pu) (real_plus u u) real_one Hs Hc).
Qed.

(* ============================================================ *)
(* End-to-end main theorem #2: use of the §4.1 core theorem [req_free_energy_kl_decomp] *)
(*   the free-energy-KL decomposition of the uniform policy p_u (extractable Set-level statement) *)
(* ============================================================ *)
Theorem two_state_free_energy_kl_flagship :
  req (free_energy_m2 bool bsum two_state_loss real_one
           two_state_pu two_state_pu_pos)
      (plus (free_energy_m2 bool bsum two_state_loss real_one
                  two_state_boltz two_state_boltz_pos)
            (mult real_one
                  (bsum (fun s : bool =>
                    mult (two_state_pu s)
                         (rminus_m2 (log (two_state_pu s) (two_state_pu_pos s))
                                    (log (two_state_boltz s) (two_state_boltz_pos s))))))).
Proof.
  exact (req_free_energy_kl_decomp bool bsum c_sum_ext c_sum_add c_sum_linear
           two_state_loss real_one real_lt_zero_one two_state_Z two_state_Z_pos
           c_partition real_log_exp_neg real_log_wd
           two_state_pu c_pu_normalized two_state_pu_pos).
Qed.
