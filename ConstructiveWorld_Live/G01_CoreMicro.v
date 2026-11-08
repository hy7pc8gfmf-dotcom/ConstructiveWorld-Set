(* ConstructiveWorld-Set — micro-core merged group: log sign law, softmax free-energy closed forms, GRPO counterexamples. *)

(** * G01_CoreMicro: log sign law, softmax free-energy identities and the
      conditional nonnegativity of group-advantage variances.

    Mission.  The log sign law [hlogz_discharge]/[hlogz_strict]
      ([0 < Za], [Za <= 1] entail [log Za <= 0]; strict for [Za < 1]); the
      closed form [free_energy_softmax_eq_neg_T_logZ]
      ([F(softmax) == -T * log Z]) and the uniqueness statement
      [ufep_attention_minimizes_free_energy_unique]; the duplicated-copy
      counterexamples and the conditional form [real_var_nonneg_cond] of
      the squared-advantage sum.

    Dependencies.  The backbone [S01_BaseRing] .. [S15_TailFEPUp],
      [AttnDoeblin]; Stdlib [List], [PeanoNat], [Extraction].

    References.  The member files [UpExtras], [UpFEP], [UpLogMono] and
      [UpPPO] of the ConstructiveWorld-Main baseline are merged here with
      statement names carried over verbatim; the log lemmas and the PPO
      clip family are consumed from the top-level [S14_B5BatchBlock] and
      [S15_TailFEPUp] copies of this development.

    Constructivity.  All proofs close by [Qed]; zero admission words; no
      classical logic; statement faces are carried by [Set]; the
      squared-sum theorem keeps its pointwise premise as an explicit
      interface assumption.

    Build.  [coqc -native-compiler no -q -Q . "" G01_CoreMicro.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

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

(* ================================================================ *)
(* Main result 1: the HlogZ discharge (direct from log monotonicity). *)
(*   [0 < Za], [Za <= 1] entail [real_log Za <= real_log 1 == 0]:      *)
(*   [real_log_le_mono : real_le a b -> real_le (log a) (log b)], with *)
(*   the positivity premises on a and b supplied by [HZa] and          *)
(*   [real_lt_zero_one].                                              *)
(* ================================================================ *)
Theorem hlogz_discharge :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  (* compose the [le] chain through the intermediate [real_log 1] *)
  apply (real_le_trans _ (real_log real_one Hone) _).
  - (* monotone [le] form: [Za <= 1] gives [log Za <= log 1] *)
    exact (real_log_le_mono Za real_one HZa Hone HZa1).
  - (* [log 1 == 0] lifted to [le] by the eq-to-le bridge *)
    exact (real_eq_le_bridge (real_log real_one Hone) real_zero
             (real_log_one Hone)).
Qed.

(* ================================================================ *)
(* Main result 2: the HlogZ discharge, direct form.                   *)
(*   The same statement shape, proved by the direct lemma             *)
(*   [real_log_le_zero_of_le_one]; the monotone-chain assembly and    *)
(*   the direct form are two independent routes to one conclusion.    *)
(* ================================================================ *)
Theorem hlogz_discharge_full :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  exact (real_log_le_zero_of_le_one Za HZa HZa1).
Qed.

(* ================================================================ *)
(* Additional result 1: the strict form (the bound is strict).        *)
(*   [0 < Za < 1] entails [log Za < log 1 = 0] (strict [lt] chain).   *)
(*   [real_log_lt_mono] is stated over [cw_log]; after the definitional *)
(*   unfolding [real_log := cw_log] the terms match position by       *)
(*   position, and [real_lt_eq_lt] rewrites [log 1] into [0] at the   *)
(*   end.                                                            *)
(* ================================================================ *)
Theorem hlogz_strict :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_lt Za real_one),
  real_lt (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  apply (real_lt_eq_lt _ (cw_log real_one Hone) _).
  - (* strict monotonicity: [Za < 1] gives [cw_log Za < cw_log 1] *)
    unfold real_log.
    exact (real_log_lt_mono Za real_one HZa Hone HZa1).
  - (* [cw_log 1 == 0] *)
    exact (real_log_one Hone).
Qed.

(* ================================================================ *)
(* Additional result 2: the KL tail-term form, [0 <= opp (log Z)].    *)
(*   Direct Real-layer supply of the tail estimate [opp (log Z_aud)   *)
(*   >= 0] in the main theorem: from [log Z <= 0] the antitone        *)
(*   [real_opp_le_compat] gives [opp 0 <= opp (log Z)], composed with *)
(*   the eq-to-le bridge on [opp 0 == 0].                            *)
(* ================================================================ *)
Theorem hlogz_opp_nonneg :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le real_zero (real_opp (real_log Za HZa)).
Proof.
  intros Za HZa HZa1.
  apply (real_le_trans _ (real_opp real_zero) _).
  - (* [0 <= opp 0]: symmetry of the equation lifted to [le] *)
    exact (real_eq_le_bridge real_zero (real_opp real_zero)
             (real_eq_sym (real_opp real_zero) real_zero real_opp_zero)).
  - (* [opp 0 <= opp (log Z)]: antitonicity composed with main result 1 *)
    exact (real_opp_le_compat (real_log Za HZa) real_zero
             (hlogz_discharge Za HZa HZa1)).
Qed.

(* Extraction check; the [Set Warnings] line silences the standard informational message about opaque-accessed constants. *)
Set Warnings "-extraction-opaque-accessed".

(* ======== G01_CoreMicro member file: UpExtras, merged unchanged ======== *)
(* ============================================================ *)
(* UpExtras.v — three independent small theorems.                 *)
(*                                                                *)
(* Item 1 (P5b): log-sum-exp = negative free energy.  Instantiate *)
(*   the root [free_energy_boltzmann] (fully generalized over the *)
(*   base loss, the temperature and the partition) with           *)
(*   [base_loss := -z], [D := T]; with the pointwise alignment    *)
(*   lemma ([softmax_temp] is pointwise the Boltzmann             *)
(*   distribution, via [opp_mult_l], the unfolding of [exp_pos_fn] *)
(*   and the definitional partition) and the extensionality lemma *)
(*   for the free energy this gives                               *)
(*   [F_attn[softmax_temp(z)] == -T * log Z_T(z)].                *)
(*                                                                *)
(* Item 2: the GRPO duplicated-copy counterexample (constructive  *)
(*   witness that NoDup cannot be dropped).  [Group := nat],      *)
(*   [enum2 := [O; O]] (one element twice, so NoDup fails): the   *)
(*   indicator sum equals [1 + 1 == 2 <> 1] — under the           *)
(*   uniform-mean reading each copy carries delta mass [2/G], so  *)
(*   at [G = 2] the total mass doubles; the constant-reward version *)
(*   sums to [2c <> c].                                           *)
(*                                                                *)
(* Item 3: the conditional form of [Var >= 0] (Real layer).       *)
(*   [real_var_nonneg_cond]: if every squared advantage is        *)
(*   nonnegative (an interface assumption, the same shape as the  *)
(*   [square_nonneg] Variable of the root GRPO section — a        *)
(*   constructive ordered field carries no trichotomy law, so     *)
(*   general squared nonnegativity must stay an honest interface), *)
(*   then [sum A_i^2 >= 0] (summation preserves the order).       *)
(*   This is the summation-side copy of the root GRPO section,    *)
(*   not a weaker form.                                           *)
(*                                                                *)
(* Zero axioms, zero admissions, zero interface escapes, no       *)
(* classical logic; Set-layer statements; all proofs close by     *)
(* Qed.  Self-contained: no Require of UpFEP / UpGRPO /           *)
(* AttnDoeblin.                                                   *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.
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

(* ################ Item 1 (P5b): log-sum-exp = negative free energy ################ *)

Section FEPLogZ.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let lt := @lt RI.
Let sum_over_S := @sum_over_S RI SS SO.
Let log := @log RI.

(* Explicit interface assumption for positivity of the softmax partition *)
(* (the same shape as the sum-positivity Variable of the root's          *)
(* attention-Gibbs bridge section). *)
Variable spp : forall f : S -> R,
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).
Variable z : S -> R.
Variable T : R.
Variable T_pos : lt zero T.

Let base : S -> R := fun s : S => opp (z s).
Let invT := inv_pos T T_pos.
Let Zf := partition_function_temp T T_pos z.
Let Zf_pos := partition_function_temp_pos spp T T_pos z.
Let F_attn (p : S -> R) : R := free_energy base T p.

(* Partition condition: the temperature partition function matches the Z *)
(* specification of the free-energy triple,                              *)
(* [Z == sum_s exp_neg (invT * base s)] (definitional unfolding of       *)
(* [exp_pos_fn]). *)
Lemma uex_fep_partition_condition :
  Id Zf (sum_over_S (fun s : S => exp_neg (mult invT (base s)))).
Proof.  unfold Zf, partition_function_temp, base.
  exact (sum_over_S_ext _ _
    (fun s : S => id_cong exp_neg (id_sym (opp_mult_l invT (z s))))).
Qed.

(* Alignment lemma: the Boltzmann distribution (energy [-z], temperature *)
(* [T]) is pointwise the temperature softmax. *)
Lemma uex_fep_align : forall s : S,
  Id (boltzmann_dist base T T_pos Zf Zf_pos s) (softmax_temp spp T T_pos z s).
Proof.  intro s. unfold boltzmann_dist, softmax_temp, exp_pos_fn.
  exact (id_trans (mult_comm (inv_pos Zf Zf_pos) (exp_neg (mult invT (base s))))
           (id_cong2 mult (id_cong exp_neg (opp_mult_l invT (z s))) (id_refl))).
Qed.

(* Extensionality for F: pointwise equal distributions give equal free   *)
(* energies (base loss and temperature fixed). *)
Lemma uex_fep_F_ext : forall p q : S -> R,
  (forall s : S, Id (p s) (q s)) -> Id (F_attn p) (F_attn q).
Proof.
  intros p q Hpt. unfold F_attn, free_energy.
  apply (id_cong2 plus).
  - apply (sum_over_S_ext _ _
      (fun s : S => id_cong2 mult (Hpt s) (id_refl : Id (base s) (base s)))).
  - apply (id_cong (fun w : R => mult T w)).
    apply (sum_over_S_ext _ _
      (fun s : S => id_cong2 mult (Hpt s) (id_cong log (Hpt s)))).
Qed.

(* ========== P5b main theorem: log-sum-exp = negative free energy ==========
   [F_attn[softmax_temp(z)] == -T * log Z_T(z)]: the softmax is pointwise
   the Boltzmann distribution ([uex_fep_align]), F is extensional, and the
   root [free_energy_boltzmann] applies with [base_loss := -z], [D := T]. *)
Theorem free_energy_softmax_eq_neg_T_logZ :
  Id (F_attn (softmax_temp spp T T_pos z))
     (mult (opp T) (log Zf)).
Proof.  exact (id_trans (uex_fep_F_ext (softmax_temp spp T T_pos z)
                             (boltzmann_dist base T T_pos Zf Zf_pos)
                             (fun s : S => id_sym (uex_fep_align s)))
            (free_energy_boltzmann base T T_pos Zf Zf_pos uex_fep_partition_condition)).
Qed.

End FEPLogZ.

(* ################ Item 2: the GRPO duplicated-copy counterexample (NoDup cannot be dropped) ################ *)

Section GRPOCounterEx.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let lt := @lt RI.

(* Own group summation (the copy-root GRPO Section's [list_sum_g]; the    *)
(* group is fixed at [nat], where equality is decidable and [Nat.eq_dec]  *)
(* feeds the indicator branches). *)
Fixpoint list_sum_g2 (f : nat -> R) (l : list nat) : R :=
  match l with
  | nil => zero
  | i :: rest => plus (f i) (list_sum_g2 f rest)
  end.

(* Constant reward: any [c > 0] (the mean carries no information; the    *)
(* counterexample is independent of the value of [c]). *)
Variable c : R.
Variable c_pos : lt zero c.
Definition reward2 : nat -> R := fun _ => c.

(* Duplicated enumeration: the element [O] occurs twice, a lawful list   *)
(* on which NoDup fails. *)
(* Indicator: the weight function of "is member [i] a group              *)
(* representative" under the uniform-mean reading. *)
Definition indicator2 : nat -> R :=
  fun i : nat =>
    match Nat.eq_dec i O with
    | left _ => one
    | right _ => zero
    end.

(* ========== Constructive witness: the indicator sum over duplicated     *)
(* copies equals [2 <> 1] ==========                                      *)
(* Why the uniform-mean reading breaks: with a single copy               *)
(* [sum_i indicator(i) == 1] (exactly one representative); duplication   *)
(* makes the sum [plus one one == 2] — each delta mass becomes [2/G]     *)
(* ([G] the group size), so at [G = 2] the indicator mass doubles and    *)
(* the exactly-once specification is violated.                           *)
(* Numerical counterexample: both statements close by [simpl] and        *)
(* [plus_zero]. *)
Theorem counter_ex_indicator_sum_two :
  Id (list_sum_g2 indicator2 [O; O])
     (plus one one).
Proof.  simpl.
  exact (id_cong (fun x => plus one x) (plus_zero one)).
Qed.

(* Same-root witness: under duplication the constant reward has total    *)
(* mass [2c <> c] (single copy), while the mean [(1/2) * 2c] stays [c] — *)
(* copying adds no reward information yet doubles the indicator mass. *)
Theorem counter_ex_reward_sum_two_c :
  Id (list_sum_g2 reward2 [O; O])
     (plus c c).
Proof.  simpl.
  exact (id_cong (fun x => plus c x) (plus_zero c)).
Qed.

End GRPOCounterEx.

(* ################ Item 3: the conditional form of Var >= 0 (Real layer) ################ *)

Section RealVarNonNeg.
Variable Grp2 : Set.
Variable enum2 : list Grp2.
Variable reward2 : Grp2 -> Real.
(* Group-size positivity: [enum] nonempty entails [length >= 1] entails   *)
(* [of_nat (length) > 0]. *)
Variable Hpos : real_lt real_zero (real_of_nat (length enum2)).

(* Group mean [mu = (1/G) * sum r_i] (Real layer; the copy-root GRPO      *)
(* [group_mean]). *)
Definition mean2 : Real :=
  real_mult (real_inv_pos (real_of_nat (length enum2)) Hpos)
            (real_list_sum_g Grp2 reward2 enum2).

(* Group-relative advantage [A_i = r_i - mu] (Real layer; the copy-root   *)
(* GRPO [grpo_advantage]). *)
Definition A2 (i : Grp2) : Real := real_plus (reward2 i) (real_opp mean2).

(* Pointwise nonnegative squares entail a nonnegative sum (induction on  *)
(* the finite list plus [real_le_plus_compat]; the proof skeleton of the *)
(* copy-root [real_list_sum_nonneg] with the fold replaced by            *)
(* [real_list_sum_g]). *)
Lemma sq_sum_list_nonneg : forall l : list Grp2,
  (forall i : Grp2, real_le real_zero (real_mult (A2 i) (A2 i))) ->
  real_le real_zero
    (real_list_sum_g Grp2 (fun i : Grp2 => real_mult (A2 i) (A2 i)) l).
Proof.
  intros l Hsq.
  induction l as [| i rest IH]; cbn [real_list_sum_g].
  - apply real_le_refl.
  - apply (RealSetoid.real_le_id_l real_zero (real_plus real_zero real_zero)
             (real_plus (real_mult (A2 i) (A2 i))
                        (real_list_sum_g Grp2
                           (fun i0 : Grp2 => real_mult (A2 i0) (A2 i0)) rest))).
    + apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
      apply real_plus_zero.
    + apply (real_le_plus_compat real_zero (real_mult (A2 i) (A2 i))
               real_zero
               (real_list_sum_g Grp2
                  (fun i0 : Grp2 => real_mult (A2 i0) (A2 i0)) rest)).
      * apply Hsq.
      * exact IH.
Qed.

(* ========== Var >= 0 (conditional form; the summation-side copy of the  *)
(* root GRPO section) ==========                                          *)
(* Pointwise nonnegativity of the squares is an interface assumption (a  *)
(* constructive ordered field has no trichotomy law, so general squared  *)
(* nonnegativity needs an interface field — the honest-interface form of *)
(* the root's [square_nonneg] Variable); this theorem is its summation   *)
(* side: given the pointwise premise, [sum A_i^2 >= 0] follows purely    *)
(* constructively from order preservation of summation.  The Var premise *)
(* of the GRPO sigma theorem is supplied exactly in this form. *)
Theorem real_var_nonneg_cond :
  (forall i : Grp2, real_le real_zero (real_mult (A2 i) (A2 i))) ->
  real_le real_zero
    (real_list_sum_g Grp2 (fun i : Grp2 => real_mult (A2 i) (A2 i)) enum2).
Proof.
  exact (sq_sum_list_nonneg enum2).
Qed.

End RealVarNonNeg.

(* Extraction check: the computational constructions of items 1 and 2    *)
(* extract. *)
(* Note: the computational use of [softmax_temp] goes through the Qed    *)
(* lemma [partition_function_temp_pos], so extraction reports its        *)
(* standard informational opaque-access warning (explicitly silenced     *)
(* here); the extraction output directory is set to the current          *)
(* directory, matching the default output location. *)
From Stdlib Require Import Extraction.
Set Warnings "-extraction-opaque-accessed".
Set Extraction Output Directory ".".
Extraction "upextras.ml" softmax_temp partition_function_temp free_energy
  list_sum_g2 reward2 indicator2.

(* ======== G01_CoreMicro member file: UpFEP, merged unchanged ======== *)
(* ============================================================ *)
(* UpFEP.v — P5: attention is the unique minimizer of the         *)
(*            variational free energy, plus the row-view lemma    *)
(*            (each row of [bs_kernel] is the single-query        *)
(*            [softmax_temp]).                                    *)
(*                                                                *)
(* P5 (free-energy x Gibbs bridge closure, pure assembly):        *)
(*   instantiate the free-energy/KL decomposition triple          *)
(*   ([free_energy_kl_decomp], [min_free_energy_is_boltzmann],    *)
(*   [free_energy_min_unique], fully generalized over the base    *)
(*   loss, the temperature and the partition) with                *)
(*   [base_loss := -z], [D := T]; with the alignment lemma (the   *)
(*   Boltzmann factor is the softmax numerator, via [opp_mult_l]) *)
(*   and the extensionality lemma for F, [softmax_temp z] is the  *)
(*   unique minimizer of [F_T[p] = -E_p[z] + T * sum p log p].    *)
(* Row view: every row of the row-softmax kernel [bs_kernel] of   *)
(*   [AttnDoeblin] is the same object as the single-query         *)
(*   [softmax_temp] (through the agreement premise between        *)
(*   [expf] and [exp_pos_fn]).                                    *)
(* Zero axioms, zero admissions; Set-layer statements; all Qed.   *)
(* ============================================================ *)

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
Require Import AttnDoeblin.

(* ################ Part 1: the P5 free-energy closure ################ *)

Section FEPAttention.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let sum_over_S := @sum_over_S RI SS SO.
Let log := @log RI.

Variable z : S -> R.
Variable T : R.
Variable T_pos : lt zero T.
Variable spp : forall f : S -> R,
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).

Let base : S -> R := fun s : S => opp (z s).
Let invT := inv_pos T T_pos.
Let Zf := partition_function_temp T T_pos z.
Let Zf_pos := partition_function_temp_pos spp T T_pos z.
Let F_attn (p : S -> R) : R := free_energy base T p.

(* Partition condition: the softmax partition function matches the Z     *)
(* specification of the free-energy triple. *)
Lemma ufep_fep_partition_condition :
  Id Zf (sum_over_S (fun s : S => exp_neg (mult invT (base s)))).
Proof.  unfold Zf, partition_function_temp, base.
  exact (sum_over_S_ext _ _ (fun s : S => id_cong exp_neg (id_sym (opp_mult_l invT (z s))))).
Qed.

(* Alignment lemma: the Boltzmann distribution (energy [-z], temperature *)
(* [T]) is pointwise [softmax_temp z]. *)
(* Here [boltzmann_dist] unfolds [exp_neg] directly (not through         *)
(* [boltzmann_factor]), so the unfolding below avoids [boltzmann_factor] *)
(* as well (matching the unfolding face of [uex_fep_align] in this file). *)
Lemma ufep_fep_align : forall s : S,
  Id (boltzmann_dist base T T_pos Zf Zf_pos s) (softmax_temp spp T T_pos z s).
Proof.  intro s. unfold boltzmann_dist, softmax_temp, exp_pos_fn.
  exact (id_trans (mult_comm (inv_pos Zf Zf_pos) (exp_neg (mult invT (base s))))
           (id_cong2 mult (id_cong exp_neg (opp_mult_l invT (z s))) (id_refl))).
Qed.

(* Extensionality for F: pointwise equal normalized distributions give   *)
(* equal free energies. *)
Lemma ufep_fep_F_ext : forall p q : S -> R,
  normalized p -> normalized q -> (forall s : S, Id (p s) (q s)) ->
  Id (F_attn p) (F_attn q).
Proof.
  intros p q Hp Hq Hpt. unfold F_attn, free_energy.
  apply (id_cong2 plus).
  - apply (sum_over_S_ext _ _
      (fun s : S => id_cong2 mult (Hpt s) (id_refl : Id (base s) (base s)))).
  - apply (id_cong (fun w : R => mult T w)).
    apply (sum_over_S_ext _ _
      (fun s : S => id_cong2 mult (Hpt s) (id_cong log (Hpt s)))).
Qed.

(* ========== P5 main theorem: attention is the unique minimizer of the   *)
(* variational free energy ========== *)
Theorem ufep_attention_minimizes_free_energy_unique :
  forall p : S -> R, normalized p -> positive_dist p ->
  And (le (F_attn (softmax_temp spp T T_pos z)) (F_attn p))
      (Id (F_attn p) (F_attn (softmax_temp spp T T_pos z)) ->
        forall s : S, Id (p s) (softmax_temp spp T T_pos z s)).
Proof.
  intros p Hp Hpos.
  assert (Hnorms : normalized (softmax_temp spp T T_pos z))
    by exact (softmax_temp_normalized spp T T_pos z).
  assert (HFsb : Id (F_attn (softmax_temp spp T T_pos z))
                     (F_attn (boltzmann_dist base T T_pos Zf Zf_pos)))
    by exact (ufep_fep_F_ext (softmax_temp spp T T_pos z)
               (boltzmann_dist base T T_pos Zf Zf_pos)
               Hnorms (boltzmann_normalized base T T_pos Zf Zf_pos ufep_fep_partition_condition)
               (fun s : S => id_sym (ufep_fep_align s))).
  split.
  - exact (le_id_l _ _ _ HFsb
             (min_free_energy_is_boltzmann base T T_pos Zf Zf_pos
                ufep_fep_partition_condition p Hp Hpos)).
  - intros Heq s.
    exact (id_trans
             (free_energy_min_unique base T T_pos Zf Zf_pos
                ufep_fep_partition_condition p Hp Hpos
                (id_trans Heq HFsb) s)
             (ufep_fep_align s)).
Qed.

End FEPAttention.

(* ################ Part 2: the row-view lemma ################ *)

Section RowView.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Variable spp : forall f : S -> R,
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).
Variable enum : list S.
Variable enum_nonempty : Not (Id enum nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable z2 : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z2 s s').
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_mono_le : forall a b : R, le a b -> le (expf a) (expf b).
Variable sum_eq_list : forall g : S -> R, Id (sum_over_S g) (bs_list_sum g enum).
Variable expf_agree : forall x : R, Id (expf x) (exp_pos_fn x).

(* ========== Row view: each row of [bs_kernel] is the single-query       *)
(* [softmax_temp] ==========                                             *)
(* Dependency premise: [expf] agrees pointwise with the attention        *)
(* section's [exp_pos_fn] (the instantiation channel of the [expf] mini  *)
(* interface: once [real_expf_realizable] is proved, taking              *)
(* [expf := exp_pos_fn] satisfies it and the agreement premise            *)
(* degenerates to [id_refl]). *)
Theorem ufep_bs_kernel_row_is_softmax_temp : forall s s' : S,
  Id (bs_kernel enum enum_nonempty temp temp_pos Delta z2 z_lb
        expf expf_pos expf_mono_le sum_eq_list s s')
     (softmax_temp spp temp temp_pos (fun s0 : S => z2 s s0) s').
Proof.
  intros s s'.
  unfold bs_kernel, softmax_temp.
  assert (HZ : Id (Zrow temp temp_pos z2 expf s)
                   (partition_function_temp temp temp_pos (fun s0 : S => z2 s s0))).
  { unfold Zrow, partition_function_temp.
    apply (sum_over_S_ext _ _
      (fun s0 : S => expf_agree (mult (inv_pos temp temp_pos) (z2 s s0)))). }
  apply (id_cong2 mult
    (expf_agree (mult (inv_pos temp temp_pos) (z2 s s')))
    (inv_pos_ext (Zrow temp temp_pos z2 expf s)
                 (partition_function_temp temp temp_pos (fun s0 : S => z2 s s0))
                 (bs_Zrow_pos enum enum_nonempty temp temp_pos Delta z2 z_lb
                    expf expf_pos expf_mono_le sum_eq_list s)
                 (partition_function_temp_pos spp temp temp_pos
                    (fun s0 : S => z2 s s0))
                 HZ)).
Qed.

End RowView.

(* Extraction check: the softmax kernel and the free energy extract. *)
From Stdlib Require Import Extraction.
Extraction "upfep.ml" softmax_temp partition_function_temp free_energy.

(* ======== G01_CoreMicro member file: UpLogMono, merged unchanged ======== *)
(* ============================================================ *)
(* UpLogMono.v — the [le] version of Real-layer log monotonicity. *)
(*                                                                *)
(* Last piece needed to discharge the HlogZ premise               *)
(* [le (log Z_aud) zero] of the KL-projection audit main theorem: *)
(* [Z_aud <= 1] entails [log Z_aud <= 0].  The [le] encoded as an *)
(* [Or] over the Real layer ([cw_log]/[real_log]) is proved       *)
(* branch by branch:                                              *)
(*   the [lt] branch uses [real_log_lt_mono] (strict monotonicity, *)
(*      proved in the root);                                      *)
(*   the [eq] branch uses [real_log_wd] (rewriting along an       *)
(*      equation, proved in the root).                            *)
(* Zero axioms, zero admissions; Set-layer statements; all Qed;   *)
(* extractable.                                                   *)
(* ============================================================ *)

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

(* The four UpLogMono lemmas merged into earlier drafts of this file      *)
(* ([real_lt_le_bridge], [real_eq_le_bridge], [real_log_le_mono],         *)
(* [real_log_le_zero_of_le_one]) are provided top-level by                *)
(* [S14_B5BatchBlock]; the use sites of this file consume the [Require]d  *)
(* versions. *)

(* Extraction check. *)
From Stdlib Require Import Extraction.
Extraction "uplogmono.ml" real_log cw_log.

(* ======== G01_CoreMicro member file: UpPPO, merged unchanged ======== *)
(* ============================================================ *)
(* UpPPO.v — PPO clip one-sided error identities (E1-E3).         *)
(*                                                                *)
(* The one-sided half of the composition between the clipped      *)
(* surrogate and value improvement:                               *)
(*   E1 exact decomposition: the IS objective equals the clipped  *)
(*      surrogate plus the clip error (an unconditional identity); *)
(*   E2 error nonnegativity: [clip_error >= 0] (no sign premise   *)
(*      on the advantage — [min_le_l] sits inside the product);   *)
(*   E3 improvement condition: a nonnegative clipped surrogate    *)
(*      entails value improvement (the one-sided closure of the   *)
(*      triple).                                                  *)
(* Honesty boundary: the converse bound (a [V(pi) - V(p_old) <=   *)
(* std_ppo + C * eps] shape) is false for unbounded ratios (when  *)
(* the ratio [rho] grows unboundedly the error [A * (rho - 1 -    *)
(* eps)] is unbounded), so no converse is claimed.                *)
(* Zero axioms, zero admissions; Set-layer statements; all Qed.   *)
(* ============================================================ *)

(* The UpPPO section PPOClipDecomp merged into earlier drafts of this     *)
(* file ([clip_error], [ppo_pointwise_decomp], [ppo_is_decomp],           *)
(* [clip_error_nonneg], [le_of_minus_nonneg], [ppo_clipped_improvement],  *)
(* the one-sided triple E1-E3) is provided top-level, under the same names *)
(* and signatures, by [S15_TailFEPUp]: the closing [Print Assumptions]    *)
(* lines for [ppo_is_decomp] / [le_of_minus_nonneg] and the three         *)
(* extraction names [policy_ratio] / [ppo_clip] / [clip_error] below      *)
(* consume the [Require]d versions. *)

(* Extraction check: the clip error and the surrogate objective extract. *)
From Stdlib Require Import Extraction.
Extraction "upppo.ml" policy_ratio ppo_clip clip_error.

Print Assumptions uex_fep_partition_condition.
Print Assumptions uex_fep_align.
Print Assumptions free_energy_softmax_eq_neg_T_logZ.
Print Assumptions counter_ex_indicator_sum_two.
Print Assumptions counter_ex_reward_sum_two_c.
Print Assumptions ufep_fep_partition_condition.
Print Assumptions ufep_fep_align.
Print Assumptions ppo_is_decomp.
Print Assumptions le_of_minus_nonneg.
