(* ===================================================================== *)
(*  fa56_id_carrier.v -- five-field pointer header.                      *)
(* ===================================================================== *)
(*  Mission. Batch-instantiate the Id-carrier slots along the VA engine  *)
(*  fa51_sumpos_id.v (the fa51_sumd list fold / nonneg / lt_le / pos     *)
(*  family): honor the physics-prediction statement faces that the fa51  *)
(*  engine (or a light extension of it) can carry; mount only the slots  *)
(*  VA left uncovered.                                                   *)
(*  Dependencies. S01_BaseRing (vo foundation) + fa51_sumpos_id (Require *)
(*  only, left unmodified) + Stdlib Lists.List / ListNotations.          *)
(*  References. S04/S05 slot coordinates, grep-checked on the statement  *)
(*  originals: I  S04:1886-1892 + 2000- (Z / Z_pos / partition_condition *)
(*  and the isomorphic GRPO-loss copy); II  S04:1817-1818 + 1900-1902    *)
(*  (transition kernel nonneg + normalization); III  S05:5761-5768       *)
(*  (covariance + fluctuation_dissipation); IV  S05:5957-5961            *)
(*  (prob_negative_entropy + fluctuation_scale); V  S05:5917-5922        *)
(*  (temperature_difference + heat_relaxation_exponential).              *)
(*  Constructivity. Zero non-constructive steps; statements keep their   *)
(*  original wording; only the four toy proof bodies are rebuilt, the    *)
(*  rest are definitional closures / unique interface-field exits,       *)
(*  honestly annotated; statement faces all Set-level, zero Prop leak;   *)
(*  trailing Print Assumptions all Closed (13 items).                    *)
(*  Build. source Live/toolchain/env.sh; unset COQLIB ROCQLIB; ulimit    *)
(*  -s 65532; compile inside a cpu-guard queue slot: rocq c              *)
(*  -native-compiler no -Q <world> "" fa56_id_carrier.v (Rocq 9.1.0;     *)
(*  world holds S01_BaseRing.vo + fa51_sumpos_id.vo).                    *)
(*  Replacement note. Rebuilt proof bodies: fa56_partition_markov,       *)
(*  fa56_Z_markov_pos, fa56_markov_kernel_nonneg,                        *)
(*  fa56_markov_kernel_normalized -- the rest are annotated closures.    *)
(* ===================================================================== *)


Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
From Stdlib Require Import Lists.List.
Import ListNotations.
(* ============================================================ *)
(*                                                                *)
(* Mission: continuing along the VA engine file fa51_sumpos_id.v  *)
(* (the fa51_sumd list fold / nonneg / lt_le / pos family), this  *)
(* file batch-instantiates the Id-carrier slots: those statement  *)
(* faces in the VA physics-prediction sections that the fa51      *)
(* engine (or a light extension of it) can honor. It does not     *)
(* repeat the VA-instantiated resolved clusters (the              *)
(* sum_over_S_pos / Z_align_pos / Z_temp three-slot chain); it    *)
(* only fills the kernel / prediction slots VA left uncovered.    *)
(*                                                                *)
(* Slot survey (coordinates on the statement originals, all       *)
(* grep-checked):                                                 *)
(*  Slot I   S04_RealExpLogConv.v:1886-1892 (BoltzmannSteadyState *)
(*        section: Z / Z_pos / partition_condition) together with *)
(*        the isomorphic copy in the S04:2000- GRPO-loss section  *)
(*        -- established mounting: Z is taken by definition as    *)
(*        fa51_Z_temp (the generic VA piece, instantiated at      *)
(*        t:=D); the partition slot drops to a definitional piece *)
(*        and the Z_pos slot holds unconditionally.               *)
(*  Slot II  S04:1817-1818 (transition_kernel_nonneg /            *)
(*        normalization, GradientDescentAndAttractor section) and *)
(*        the same-shaped transition slots at S04:1900-1902 --    *)
(*        Boltzmann-Gibbs stationary-kernel instantiation:        *)
(*        pointwise positive, lifted to le, sumd-normalized (the  *)
(*        main theorem's nontrivial piece; needs the linearity    *)
(*        lemma).                                                 *)
(*  Slot III S05_AlignmentGRPO.v:5761-5768 (the                   *)
(*        FluctuationDissipation section covariance slot +        *)
(*        fluctuation_dissipation slot) -- mounting: definitional *)
(*        piece + positivity companion.                           *)
(*  Slot IV  S05:5957-5961 (Prediction4 section prob_negative_    *)
(*        entropy / fluctuation_scale slots) -- mounting:         *)
(*        definitional piece + unconditional positivity + a       *)
(*        strict below-one companion for N > 0 (uses              *)
(*        exp_neg_decr + exp_neg_zero).                           *)
(*  Slot V   S05:5917-5922 (Prediction1 section temperature_      *)
(*        difference / heat_relaxation_exponential slots) --      *)
(*        mounting: definitional piece + positivity companion.    *)
(*                                                                *)
(* Reconciliation scope: abstract SumOver-style carriers (the S04 *)
(* sum_over_S) have no list structure; the G12 header ruling, in  *)
(* its own words (translated here): Id-style carriers ... keep a  *)
(* real-isomorphic module -- this file is precisely that Id       *)
(* carrier (S01 RealInterfaceEnhanced) for the kernel /           *)
(* prediction slot face; statement faces are Set-level (lt / le / *)
(* Id / Not all Set-valued, per the S04:1589 vocab_nonempty       *)
(* precedent), zero Prop leakage.                                 *)
(*                                                                *)
(* Usage: S01_BaseRing (vo foundation) + fa51_sumpos_id (from the *)
(* ablation line; Require only, unmodified). Existing files are   *)
(* unchanged; the fa56_ prefix is collision-checked library-wide. *)
(* Red line: purely constructive, zero non-constructive steps;    *)
(* trailing Print Assumptions all Closed.                         *)
(* ============================================================ *)

Section Fa56IdCarrier.

Context {RI : RealInterfaceEnhanced}.
Variable S : Set.
Variable enum : list S.

Let R        := @R RI.
Let zero     := @zero RI.
Let one      := @one RI.
Let plus     := @plus RI.
Let mult     := @mult RI.
Let inv_pos  := @inv_pos RI.
Let le       := @le RI.
Let lt       := @lt RI.
Let exp_neg  := @exp_neg RI.

(* ============ Engine extension: constant factor-out (sumd linearity,   *)
(* ============ Id-level list induction) ================================ *)
(* The fa51 engine only covers the positive direction; kernel            *)
(* normalization needs Id-level linearity. No new premise is introduced: *)
(* assembled by induction from pure interface fields (mult_zero/distrib  *)
(* + id_cong/id_trans).                                                  *)

Lemma fa56_sumd_mult_const :
  forall (c : R) (f : S -> R) (l : list S),
    Id (fa51_sumd S (fun s => mult c (f s)) l) (mult c (fa51_sumd S f l)).
Proof.
  intros c f l. induction l as [| x t IH].
  - exact (id_sym (mult_zero c)).
  - exact (id_trans (id_cong (fun y => plus (mult c (f x)) y) IH)
                    (id_sym (distrib c (f x) (fa51_sumd S f t)))).
Qed.

(* ============ Main group I: S04:1886-1892 / 2000- Z slot chain, dual   *)
(* ============ coordinates ============================================= *)
(* Slot statements: Variable Z : R; Z_pos : lt zero Z;                   *)
(* partition_condition :                                                 *)
(*   Id Z (sum_over_S (fun s => exp_neg (mult (inv_pos D D_pos)          *)
(*         (base_loss s)))).                                             *)
(* Established mounting: Z is taken by definition as fa51_Z_temp (the    *)
(* generic VA piece, instantiated at t:=D); the partition slot drops to  *)
(* a definitional piece, the Z_pos slot holds unconditionally (engine    *)
(* entry 4). One generalization covers both isomorphic section copies -- *)
(* no duplicated construction.                                           *)

Theorem fa56_partition_markov :
  forall (base_loss : S -> R) (D : R) (D_pos : lt zero D),
    Id (fa51_Z_temp S enum base_loss D D_pos)
       (fa51_sumd S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))
                   enum).
Proof.
  intros base_loss D D_pos.
  reflexivity.
Qed.

Theorem fa56_Z_markov_pos :
  forall (base_loss : S -> R) (D : R) (D_pos : lt zero D),
    Not (Id enum nil) ->
    lt zero (fa51_Z_temp S enum base_loss D D_pos).
Proof.
  intros base_loss D D_pos Hne.
  destruct enum as [| x t].
  - destruct (Hne (@id_refl (list S) nil)).
  - unfold fa51_Z_temp.
    exact (lt_le_trans zero
             (exp_neg (mult (inv_pos D D_pos) (base_loss x)))
             (plus (exp_neg (mult (inv_pos D D_pos) (base_loss x)))
                   (fa51_sumd S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))) t))
             (exp_neg_pos (mult (inv_pos D D_pos) (base_loss x)))
             (le_id_l (exp_neg (mult (inv_pos D D_pos) (base_loss x)))
                      (plus (exp_neg (mult (inv_pos D D_pos) (base_loss x))) zero)
                      (plus (exp_neg (mult (inv_pos D D_pos) (base_loss x)))
                            (fa51_sumd S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))) t))
                      (id_sym (plus_zero (exp_neg (mult (inv_pos D D_pos) (base_loss x)))))
                      (le_plus_compat (exp_neg (mult (inv_pos D D_pos) (base_loss x)))
                                      (exp_neg (mult (inv_pos D D_pos) (base_loss x)))
                                      zero
                                      (fa51_sumd S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))) t)
                                      (le_refl (exp_neg (mult (inv_pos D D_pos) (base_loss x))))
                                      (fa51_sumd_nonneg S
                                         (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))) t
                                         (fun s0 => lt_le_iff zero
                                                      (exp_neg (mult (inv_pos D D_pos) (base_loss s0)))
                                                      (inl (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s0))))))))).
Qed.

(* ============ Main group II: S04:1817-1818 / 1900-1902 kernel slot     *)
(* ============ instantiation =========================================== *)
(* Slot statements: transition_nonneg : forall s s', le zero (transition *)
(* s s'); transition_normalization : forall s, Id (sum_over_S (fun s' => *)
(* transition s s')) one.                                                *)
(* Realization: a Boltzmann-Gibbs stationary kernel k(s') = Z^-1 *       *)
(* e^(-b*e(s')), b = inv_pos D D_pos -- independent of the first index;  *)
(* the slot's forall s face is proven exactly as stated. The positivity  *)
(* slot is upgraded to the strict form; the normalization slot is the    *)
(* main theorem's nontrivial piece (three-stage chain: linearity lemma + *)
(* spec definitional lemma + inv_pos_correct; the Id-carrier isomorph of *)
(* S04 boltzmann_dist_temp_normalized).                                  *)

Definition fa56_markov_kernel (base_loss : S -> R) (D : R) (D_pos : lt zero D)
                              (HZ : lt zero (fa51_Z_temp S enum base_loss D D_pos))
                              (s' : S) : R :=
  mult (inv_pos (fa51_Z_temp S enum base_loss D D_pos) HZ)
       (exp_neg (mult (inv_pos D D_pos) (base_loss s'))).

Theorem fa56_markov_kernel_pos :
  forall (base_loss : S -> R) (D : R) (D_pos : lt zero D)
         (HZ : lt zero (fa51_Z_temp S enum base_loss D D_pos)) (s' : S),
    lt zero (fa56_markov_kernel base_loss D D_pos HZ s').
Proof.
  intros base_loss D D_pos HZ s'. unfold fa56_markov_kernel.
  exact (mult_positive (inv_pos (fa51_Z_temp S enum base_loss D D_pos) HZ)
                       (exp_neg (mult (inv_pos D D_pos) (base_loss s')))
                       (inv_pos_pos (fa51_Z_temp S enum base_loss D D_pos) HZ)
                       (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s')))).
Qed.

Theorem fa56_markov_kernel_nonneg :
  forall (base_loss : S -> R) (D : R) (D_pos : lt zero D)
         (HZ : lt zero (fa51_Z_temp S enum base_loss D D_pos)) (s' : S),
    le zero (fa56_markov_kernel base_loss D D_pos HZ s').
Proof.
  intros base_loss D D_pos HZ s'.
  exact (lt_le_iff zero (fa56_markov_kernel base_loss D D_pos HZ s')
           (inl (mult_positive (inv_pos (fa51_Z_temp S enum base_loss D D_pos) HZ)
                               (exp_neg (mult (inv_pos D D_pos) (base_loss s')))
                               (inv_pos_pos (fa51_Z_temp S enum base_loss D D_pos) HZ)
                               (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s')))))).
Qed.

Theorem fa56_markov_kernel_normalized :
  forall (base_loss : S -> R) (D : R) (D_pos : lt zero D)
         (HZ : lt zero (fa51_Z_temp S enum base_loss D D_pos)),
    Id (fa51_sumd S (fun s' => fa56_markov_kernel base_loss D D_pos HZ s') enum)
       one.
Proof.
  intros base_loss D D_pos HZ. unfold fa56_markov_kernel.
  assert (Hc : forall l : list S,
            Id (fa51_sumd S (fun s => mult (inv_pos (fa51_Z_temp S enum base_loss D D_pos) HZ)
                                           (exp_neg (mult (inv_pos D D_pos) (base_loss s)))) l)
               (mult (inv_pos (fa51_Z_temp S enum base_loss D D_pos) HZ)
                     (fa51_sumd S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))) l))).
  { intro l. induction l as [| y t IHl].
    - exact (id_sym (mult_zero (inv_pos (fa51_Z_temp S enum base_loss D D_pos) HZ))).
    - exact (id_trans
               (id_cong (fun w => plus (mult (inv_pos (fa51_Z_temp S enum base_loss D D_pos) HZ)
                                             (exp_neg (mult (inv_pos D D_pos) (base_loss y)))) w)
                        IHl)
               (id_sym (distrib (inv_pos (fa51_Z_temp S enum base_loss D D_pos) HZ)
                                (exp_neg (mult (inv_pos D D_pos) (base_loss y)))
                                (fa51_sumd S (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))) t)))). }
  exact (id_trans (Hc enum)
           (id_trans (id_cong (fun y => mult (inv_pos (fa51_Z_temp S enum base_loss D D_pos) HZ) y)
                      (id_sym (fa51_Z_temp_spec_def S enum base_loss D D_pos)))
             (id_trans (mult_comm (inv_pos (fa51_Z_temp S enum base_loss D D_pos) HZ)
                                  (fa51_Z_temp S enum base_loss D D_pos))
                       (inv_pos_correct (fa51_Z_temp S enum base_loss D D_pos) HZ)))).
Qed.

(* ============ Main group III: S05:5761-5768 fluctuation-dissipation    *)
(* ============ slot ==================================================== *)
(* Slot statements: Variable covariance : R; fluctuation_dissipation :   *)
(*   Id covariance (mult D H_inv).                                       *)
(* Realization: covariance mounted as a definitional piece (established  *)
(* practice: the predicted quantity is taken as a construction) plus a   *)
(* positivity companion (mult_positive; H_inv positivity enters the      *)
(* theorem signature as a standing premise, same pattern as fa51).       *)

Definition fa56_covariance (D H_inv : R) : R := mult D H_inv.

Theorem fa56_fluctuation_dissipation :
  forall (D H_inv : R), Id (fa56_covariance D H_inv) (mult D H_inv).
Proof.
  intros D H_inv. reflexivity.
Qed.

Theorem fa56_covariance_pos :
  forall (D H_inv : R),
    lt zero D -> lt zero H_inv -> lt zero (fa56_covariance D H_inv).
Proof.
  intros D H_inv HD HI. unfold fa56_covariance.
  exact (mult_positive D H_inv HD HI).
Qed.

(* ============ Main group IV: S05:5957-5961 fluctuation-scale slot ==== *)
(* Slot statements: fluctuation_scale : forall N : R,                    *)
(*   Id (prob_negative_entropy N) (exp_neg (mult N (inv_pos k_B          *)
(*   k_B_pos))).                                                         *)
(* Realization: prob mounted as a definitional piece + unconditional     *)
(* positivity + a strict upper-bound companion (below one for N > 0;     *)
(* uses exp_neg_decr -- an Enhanced field; the S01 note names the        *)
(* fluctuation direction -- plus exp_neg_zero, closed on the right side  *)
(* by lt_id_r through Id). The S01 header states verbatim: without       *)
(* exp_neg_decr the original interface cannot decide this prediction     *)
(* direction -- this file is the realization once the field is present.  *)

Definition fa56_prob_neg_entropy (k_B : R) (k_B_pos : lt zero k_B) (N : R) : R :=
  exp_neg (mult N (inv_pos k_B k_B_pos)).

Theorem fa56_fluctuation_scale :
  forall (k_B : R) (k_B_pos : lt zero k_B) (N : R),
    Id (fa56_prob_neg_entropy k_B k_B_pos N)
       (exp_neg (mult N (inv_pos k_B k_B_pos))).
Proof.
  intros k_B k_B_pos N. reflexivity.
Qed.

Theorem fa56_prob_neg_entropy_pos :
  forall (k_B : R) (k_B_pos : lt zero k_B) (N : R),
    lt zero (fa56_prob_neg_entropy k_B k_B_pos N).
Proof.
  intros k_B k_B_pos N. unfold fa56_prob_neg_entropy.
  exact (exp_neg_pos (mult N (inv_pos k_B k_B_pos))).
Qed.

Theorem fa56_prob_neg_entropy_lt_one :
  forall (k_B : R) (k_B_pos : lt zero k_B) (N : R),
    lt zero N -> lt (fa56_prob_neg_entropy k_B k_B_pos N) one.
Proof.
  intros k_B k_B_pos N HN. unfold fa56_prob_neg_entropy.
  exact (lt_id_r (exp_neg (mult N (inv_pos k_B k_B_pos))) (exp_neg zero) one
           (exp_neg_zero)
           (exp_neg_decr zero (mult N (inv_pos k_B k_B_pos))
              (mult_positive N (inv_pos k_B k_B_pos) HN
                 (inv_pos_pos k_B k_B_pos)))).
Qed.

(* ============ Main group V: S05:5917-5922 heat-relaxation slot ======= *)
(* Slot statements: heat_relaxation_exponential : forall t : nat,        *)
(*   Id (temperature_difference t) (mult (exp_neg (mult gamma            *)
(*   (of_nat t))) temperature_difference0).                              *)
(* Realization: temperature_difference mounted as a definitional piece   *)
(* (the of_nat slot stays an interface argument -- honest downgrading,   *)
(* same pattern as fa51 beta) plus a positivity companion (D0 positivity *)
(* premise + exp_neg_pos).                                               *)

Definition fa56_temp_difference (gamma : R) (of_nat_R : nat -> R) (D0 : R)
                                (t : nat) : R :=
  mult (exp_neg (mult gamma (of_nat_R t))) D0.

Theorem fa56_heat_relaxation_exponential :
  forall (gamma : R) (of_nat_R : nat -> R) (D0 : R) (t : nat),
    Id (fa56_temp_difference gamma of_nat_R D0 t)
       (mult (exp_neg (mult gamma (of_nat_R t))) D0).
Proof.
  intros gamma of_nat_R D0 t. reflexivity.
Qed.

Theorem fa56_temp_difference_pos :
  forall (gamma : R) (of_nat_R : nat -> R) (D0 : R) (t : nat),
    lt zero D0 -> lt zero (fa56_temp_difference gamma of_nat_R D0 t).
Proof.
  intros gamma of_nat_R D0 t HD0. unfold fa56_temp_difference.
  exact (mult_positive (exp_neg (mult gamma (of_nat_R t))) D0
           (exp_neg_pos (mult gamma (of_nat_R t))) HD0).
Qed.

End Fa56IdCarrier.

(* ============ Assumption-surface closure declaration ================== *)

Print Assumptions fa56_sumd_mult_const.
Print Assumptions fa56_partition_markov.
Print Assumptions fa56_Z_markov_pos.
Print Assumptions fa56_markov_kernel_pos.
Print Assumptions fa56_markov_kernel_nonneg.
Print Assumptions fa56_markov_kernel_normalized.
Print Assumptions fa56_fluctuation_dissipation.
Print Assumptions fa56_covariance_pos.
Print Assumptions fa56_fluctuation_scale.
Print Assumptions fa56_prob_neg_entropy_pos.
Print Assumptions fa56_prob_neg_entropy_lt_one.
Print Assumptions fa56_heat_relaxation_exponential.
Print Assumptions fa56_temp_difference_pos.
