(* ConstructiveWorld-Set -- the tail free-energy-principle module of the S-series. *)
(** * S15_TailFEPUp: tail FEP -- softmax kernels, PPO clip errors, step-KL rate, GRPO sigma.

    Mission.  Attention as the unique minimizer of the variational free energy
      ([attention_minimizes_free_energy_unique]); kernel rows as single-query
      softmaxes ([bs_kernel_row_is_softmax_temp]); the PPO clip one-sided family
      ([ppo_is_decomp], [clip_error_nonneg], [ppo_clipped_improvement]); the
      step-KL geometric rate ([real_step_kl_eta_bound_eps]); the GRPO NoDup
      uniformization and sigma witness ([grpo_uniform_mass],
      [real_sigma_witness], [proj_sigma_sq]); the extras
      ([free_energy_softmax_eq_neg_T_logZ], the duplicated-copy counterexamples,
      [real_var_nonneg_cond]).

    Dependencies.  [S01_BaseRing] .. [S14_B5BatchBlock] of this development;
      Stdlib [QArith], [List], [Bool], [Arith], [Setoid], [Morphisms], [Lia],
      [Qminmax], [ZArith.Znat], [PeanoNat].

    References.  This development, CW_ConstructiveWorld_219.v: the baseline
      monolith in ConstructiveWorld-Main whose statement names are carried
      over here verbatim (original range L112164-L114222); the upstream
      modules UpPPO, UpStepKL, UpGRPO, UpExtras are embedded below, the last
      two wrapped in [UpGRPO219]/[UpExtras219] under qualified names.

    Constructivity.  All named statements are carried by [Set]; the file is
      axiom-free with every proof closed by [Qed]; statements extract with
      [Obj.magic] = 0 and no erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      S15_TailFEPUp.v] compiles cleanly (exit 0); the first eight bytes of
      the artifact are [436f7121 00015ff4]. *)
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
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.
From Stdlib Require Import ZArith.Znat.
Opaque Qred.

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

(* partition condition: the softmax partition function realizes the Z slot
   of the [free_energy] triple *)
Lemma fep_partition_condition :
  Id Zf (sum_over_S (fun s : S => exp_neg (mult invT (base s)))).
Proof.
  unfold Zf, partition_function_temp, base.
  apply (sum_over_S_ext _ _ (fun s : S => id_cong exp_neg (id_sym (opp_mult_l invT (z s))))).
Qed.

(* alignment lemma: the Boltzmann distribution (energy -z, temperature T)
   agrees pointwise with [softmax_temp z] *)
Lemma fep_align : forall s : S,
  Id (boltzmann_dist base T T_pos Zf Zf_pos s) (softmax_temp spp T T_pos z s).
Proof.
  intro s. unfold boltzmann_dist, softmax_temp, boltzmann_factor, exp_pos_fn.
  apply (id_trans (mult_comm (inv_pos Zf Zf_pos) (exp_neg (mult invT (base s))))).
  apply (id_cong2 mult (id_cong exp_neg (opp_mult_l invT (z s)))).
  apply id_refl.
Qed.

(* extensionality of F: pointwise-equal normalized distributions carry
   equal free energy *)
Lemma fep_F_ext : forall p q : S -> R,
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

(* ========== P5 main theorem: attention is the unique minimizer of the variational free energy ========== *)
Theorem attention_minimizes_free_energy_unique :
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
    by exact (fep_F_ext (softmax_temp spp T T_pos z)
               (boltzmann_dist base T T_pos Zf Zf_pos)
               Hnorms (boltzmann_normalized base T T_pos Zf Zf_pos fep_partition_condition)
               (fun s : S => id_sym (fep_align s))).
  split.
  - exact (le_id_l _ _ _ HFsb
             (min_free_energy_is_boltzmann base T T_pos Zf Zf_pos
                fep_partition_condition p Hp Hpos)).
  - intros Heq s.
    exact (id_trans
             (free_energy_min_unique base T T_pos Zf Zf_pos
                fep_partition_condition p Hp Hpos
                (id_trans Heq HFsb) s)
             (fep_align s)).
Qed.

End FEPAttention.

(* ################ Part 2: row-view lemmas ################ *)

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

(* ========== row view: every row of [bs_kernel] is the single-query [softmax_temp] ========== *)
(* standing premise: [expf] agrees pointwise with the attention section's
   [exp_pos_fn] (the instantiation channel of the expf mini-interface:
   taking [expf := exp_pos_fn] via [real_expf_realizable] satisfies it,
   and the agreement premise degenerates to [id_refl]). *)
Theorem bs_kernel_row_is_softmax_temp : forall s s' : S,
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

(* extraction check: the softmax kernel and the free energy extract *)

(* ============================================================ *)
(* Block 27. UpPPO: PPO clip one-sided error identities.          *)
(*   [ppo_is_decomp] + [clip_error_nonneg] +                      *)
(*   [ppo_clipped_improvement] (the one-sided closure of Paper 1, *)
(*   Sec. 6.2; the counterexample note for the reverse bound sits *)
(*   in the source file header). Source: UpPPO.v (upstream); zero *)
(*   axioms, no admitted proofs; 5 Qed.                           *)
(* ============================================================ *)
(* ============================================================ *)
(* UpPPO.v -- PPO clip one-sided error identities (E1-E3).         *)
(*                                                                *)
(* Closes the one-sided half of the Paper 1 Sec. 6.2 trio: the    *)
(* composite theorem between the clipped surrogate and the value  *)
(* improvement --                                                  *)
(*   E1 exact decomposition: the IS objective == clipped          *)
(*      surrogate + clip error (an unconditional identity);       *)
(*   E2 error nonnegativity: [clip_error] >= 0 (no advantage-sign *)
(*      premise -- [min_le_l] sits inside the product, as in       *)
(*      Theorem 6.7);                                             *)
(*   E3 improvement condition: a nonnegative clipped surrogate    *)
(*      implies the value improvement (the one-sided closure with *)
(*      all three pieces in place).                               *)
(* Honesty boundary: the reverse bound (of the shape              *)
(* V(pi) - V(p_old) <= std_ppo + C*eps) is false for unbounded    *)
(* ratios (counterexample: as the ratio rho -> infinity the error *)
(* A*(rho - 1 - eps) is unbounded), so it is not claimed.         *)
(* Discipline: zero axioms, no admitted proofs; Set-layer         *)
(* statements; all proofs closed by Qed.                          *)
(* ============================================================ *)


Section PPOClipDecomp.
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
Let minus := @minus RI.
Let sum_over_S := @sum_over_S RI SS SO.
Let min := @min RI.

Variable pi p_old : S -> R.
Variable eps : R.
Variable Hpos : forall s : S, lt zero (p_old s).
Variable Hpi : normalized pi.

Let ratio (s : S) : R := policy_ratio pi p_old s (Hpos s).

(* clip error: the amount by which the pointwise IS value exceeds the
   pointwise clipped surrogate (the weights [p_old] built in) *)
Definition clip_error (adv : S -> R) : R :=
  sum_over_S (fun s : S =>
    mult (p_old s)
      (minus (mult (ratio s) (adv s))
             (min (mult (ratio s) (adv s))
                  (mult (ppo_clip (ratio s) (minus one eps) (plus one eps))
                        (adv s))))).

(* pointwise decomposition: rA == min(rA, clip(r)A) + (rA - min(rA, clip(r)A)) *)
Lemma ppo_pointwise_decomp (adv : S -> R) : forall s : S,
  Id (mult (p_old s) (mult (ratio s) (adv s)))
     (plus (mult (p_old s)
                 (min (mult (ratio s) (adv s))
                      (mult (ppo_clip (ratio s) (minus one eps) (plus one eps))
                            (adv s))))
           (mult (p_old s)
                 (minus (mult (ratio s) (adv s))
                        (min (mult (ratio s) (adv s))
                             (mult (ppo_clip (ratio s) (minus one eps)
                                        (plus one eps))
                                   (adv s)))))).
Proof.
  intro s.
  apply (id_trans (id_cong (mult (p_old s))
             (id_trans (id_sym (minus_plus_cancel_gap
                                 (mult (ratio s) (adv s))
                                 (min (mult (ratio s) (adv s))
                                      (mult (ppo_clip (ratio s) (minus one eps)
                                                 (plus one eps))
                                            (adv s)))))
                       (plus_comm (minus (mult (ratio s) (adv s))
                                          (min (mult (ratio s) (adv s))
                                               (mult (ppo_clip (ratio s)
                                                          (minus one eps)
                                                          (plus one eps))
                                                     (adv s))))
                                  (min (mult (ratio s) (adv s))
                                       (mult (ppo_clip (ratio s) (minus one eps)
                                                  (plus one eps))
                                             (adv s))))))).
  apply distrib.
Qed.

(* ========== E1: exact decomposition of the IS objective (an unconditional identity) ========== *)
Theorem ppo_is_decomp : forall adv : S -> R,
  Id (is_objective_of pi p_old adv Hpos)
     (plus (ppo_surrogate pi p_old adv eps Hpos) (clip_error adv)).
Proof.
  intro adv. unfold is_objective_of, ppo_surrogate, clip_error.
  apply (id_trans (sum_over_S_ext _ _ (ppo_pointwise_decomp adv))).
  apply (sum_over_S_add _ _).
Qed.

(* ========== E2: the clip error is nonnegative (no advantage-sign premise) ========== *)
Theorem clip_error_nonneg : forall adv : S -> R, le zero (clip_error adv).
Proof.
  intro adv. unfold clip_error.
  apply sum_over_S_nonneg. intro s.
  apply (le_mult_nonneg_t12 (p_old s)
    (minus (mult (ratio s) (adv s))
           (min (mult (ratio s) (adv s))
                (mult (ppo_clip (ratio s) (minus one eps) (plus one eps))
                      (adv s))))).
  - exact (lt_le_iff _ _ (inl (Hpos s))).
  - exact (le_minus_nonneg
             (min (mult (ratio s) (adv s))
                  (mult (ppo_clip (ratio s) (minus one eps) (plus one eps))
                        (adv s)))
             (mult (ratio s) (adv s))
             (min_le_l (mult (ratio s) (adv s))
                       (mult (ppo_clip (ratio s) (minus one eps)
                                  (plus one eps))
                             (adv s)))).
Qed.

(* auxiliary: a - b >= 0 implies b <= a *)
Lemma le_of_minus_nonneg : forall a b : R, le zero (minus a b) -> le b a.
Proof.
  intros a b H. exact (le_id_r b (plus b (minus a b)) a (id_trans (plus_comm b (minus a b)) (minus_plus_cancel_gap a b)) (le_plus_nonneg_r b (minus a b) H)).
Qed.

(* ========== E3: a nonnegative clipped surrogate implies the value improvement (one-sided, all three pieces) ========== *)
Theorem ppo_clipped_improvement : forall reward : S -> R,
  le zero (ppo_surrogate pi p_old (advantage reward p_old) eps Hpos) ->
  le (state_value reward p_old) (state_value reward pi).
Proof.
  intros reward Hsurr.
  assert (H65 := ppo_surrogate_raw_is_value_improvement reward pi p_old Hpos Hpi).
  assert (His : Id (is_objective_of pi p_old (advantage reward p_old) Hpos)
                   (minus (state_value reward pi) (state_value reward p_old)))
    by exact H65.
  assert (Hge : le zero (is_objective_of pi p_old (advantage reward p_old) Hpos)).
  { apply (le_trans _ (ppo_surrogate pi p_old (advantage reward p_old) eps Hpos) _).
    - exact Hsurr.
    - apply (le_id_r _ _ _ (id_sym (ppo_is_decomp (advantage reward p_old)))).
      exact (le_plus_nonneg_r (ppo_surrogate pi p_old (advantage reward p_old) eps Hpos)
               (clip_error (advantage reward p_old))
               (clip_error_nonneg (advantage reward p_old))). }
  assert (Hle0 : le zero (minus (state_value reward pi) (state_value reward p_old))).
  { exact (le_id_r _ _ _ His Hge). }
  exact (le_of_minus_nonneg _ _ Hle0).
Qed.

End PPOClipDecomp.

(* extraction check: the clip error and the surrogate objective extract *)

(* ============================================================ *)
(* Block 28. UpStepKL: the Real-layer realization of the unique   *)
(*   honest interface of Paper 1 Theorem 4.8; four main pieces    *)
(*   plus the kl_ family. The 35 declaration names clash with no  *)
(*   upstream root names, so no Module wrapper is added; the      *)
(*   upstream CW Require lines are stripped; the Import of        *)
(*   RealInterfaceEnhancedMod is kept. Source: UpStepKL.v         *)
(*   (upstream); zero axioms, no admitted proofs; 32 Qed.         *)
(* ============================================================ *)
(* ============================================================ *)
(* UpStepKL.v -- the Real-layer realization of step_kl_eta_bound.  *)
(* The eps-analog of the unique honest interface of Paper 1       *)
(* Theorem 4.8 (the true geometric rate of policy iteration): the *)
(* interpolation inequality Z = Sum pi_t^{1-eta}*pi*^eta <= 1.    *)
(* Route: the Varberg cone argument (no Jensen/Hoelder            *)
(* infrastructure)                                                *)
(*   M0.1 two-point convexity kernel                              *)
(*      (e^{(1-eta)x + eta y} <= (1-eta)e^x + eta*e^y + eps)      *)
(*   M0.2 pointwise AM-GM                                         *)
(*      (a^{1-eta} b^eta <= (1-eta)a + eta b + eps)               *)
(*   M1  summed version (Sum powprod <= 1 + eps; normalization    *)
(*      absorbs the eps*pi_t weights).                            *)
(* All names sit at the Real-layer top level ([cw_log]/           *)
(* [cauchy_real_exp]); [le] is Or-encoded.                        *)
(* Discipline: zero axioms, no admitted proofs; Set-layer         *)
(* statements; all proofs closed by Qed; extractable.             *)
(* ============================================================ *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.

(* ========== bridges: lt/eq into le, and the eq reformations on both sides of le ========== *)

Lemma kl_lt_le_bridge : forall a b : Real, real_lt a b -> real_le a b.
Proof.
  intros a b H.
  (* unfolding the Set-layer Or encoding: [real_le a b] =
   [Or (real_lt a b) (real_eq a b)]; the left branch is injected by the
   fully explicit [@inl] with every type argument fed in (no inl sugar) *)
  exact (@inl (real_lt a b) (real_eq a b) H).
Qed.

Lemma kl_eq_le_bridge : forall a b : Real, real_eq a b -> real_le a b.
Proof.
  intros a b H.
  (* unfolding the Set-layer Or encoding: the right branch is injected by the
   fully explicit [@inr] with every type argument fed in (no inr sugar) *)
  exact (@inr (real_lt a b) (real_eq a b) H).
Qed.

Lemma kl_le_eq_r : forall a b c : Real,
  real_le a b -> real_eq b c -> real_le a c.
Proof.
  intros a b c Hab Hbc.
  (* the last link of the transitivity chain is injected explicitly:
   [real_le b c] is built as [@inr (real_eq b c)] *)
  exact (real_le_trans a b c Hab (@inr (real_lt b c) (real_eq b c) Hbc)).
Qed.

Lemma kl_le_eq_l : forall a b c : Real,
  real_le a b -> real_eq a c -> real_le c b.
Proof. intros a b c Hab Hac.
  (* after flipping the equation with [real_eq_sym], the first link of the
   transitivity chain is injected by the fully explicit [@inr] *)
  exact (real_le_trans c a b
          (@inr (real_lt c a) (real_eq c a) (real_eq_sym a c Hac)) Hab).
Qed.

(* ========== ring identity family (pointwise [ring] through [real_eq_of_zero_diff]) ========== *)

Lemma kl_zero_plus_zero : real_eq (real_plus real_zero real_zero) real_zero.
Proof. apply real_eq_of_zero_diff. intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

Lemma kl_plus_zero_l : forall x : Real, real_eq (real_plus real_zero x) x.
Proof. intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

Lemma kl_mult_zero_l : forall x : Real, real_eq (real_mult real_zero x) real_zero.
Proof. intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

Lemma kl_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof. intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

Lemma kl_distrib_r : forall x y z : Real,
  real_eq (real_mult (real_plus x y) z) (real_plus (real_mult x z) (real_mult y z)).
Proof. intros x y z. destruct x as [u Hu]. destruct y as [v Hv]. destruct z as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

(* (1 - eta) + eta == 1 *)
Lemma kl_ring_m_plus_eta : forall eta : Real,
  real_eq (real_plus (real_plus real_one (real_opp eta)) eta) real_one.
Proof. intros eta. destruct eta as [v Hv]. apply real_eq_of_zero_diff.
  intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

(* the Varberg cone master identity:
   E*m*(1 + eta*s) + E*eta*(1 + m*(-s)) == E, with m := 1 - eta expanded *)
Lemma kl_ring_core : forall (E eta s : Real),
  real_eq (real_plus
    (real_mult (real_mult E (real_plus real_one (real_opp eta)))
               (real_plus real_one (real_mult eta s)))
    (real_mult (real_mult E eta)
               (real_plus real_one
                 (real_mult (real_plus real_one (real_opp eta)) (real_opp s)))))
    E.
Proof. intros E eta s. destruct E as [u Hu]. destruct eta as [v Hv]. destruct s as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

(* z + eta*s == x, where z := (1-eta)x + eta y and s := x - y *)
Lemma kl_z_tA : forall x y eta : Real,
  real_eq (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                (real_mult eta y))
                     (real_mult eta (real_plus x (real_opp y)))) x.
Proof. intros x y eta. destruct x as [u Hu]. destruct y as [v Hv]. destruct eta as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

(* z + (1-eta)*(-s) == y *)
Lemma kl_z_tB : forall x y eta : Real,
  real_eq (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                (real_mult eta y))
                     (real_mult (real_plus real_one (real_opp eta))
                                (real_opp (real_plus x (real_opp y))))) y.
Proof. intros x y eta. destruct x as [u Hu]. destruct y as [v Hv]. destruct eta as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

Lemma kl_sum_prod_r : forall a b w : Real,
  real_eq (real_plus (real_mult a w) (real_mult b w)) (real_mult (real_plus a b) w).
Proof. intros a b w. destruct a as [u Hu]. destruct b as [v Hv]. destruct w as [w' Hw'].
  apply real_eq_of_zero_diff. intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

Lemma kl_swap3 : forall c e w : Real,
  real_eq (real_mult c (real_mult e w)) (real_mult e (real_mult c w)).
Proof. intros c e w. destruct c as [u Hu]. destruct e as [v Hv]. destruct w as [w' Hw'].
  apply real_eq_of_zero_diff. intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

Lemma kl_assoc_swap : forall E m w : Real,
  real_eq (real_mult (real_mult E m) w) (real_mult m (real_mult E w)).
Proof. intros E m w. destruct E as [u Hu]. destruct m as [v Hv]. destruct w as [w' Hw'].
  apply real_eq_of_zero_diff. intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

(* ========== order auxiliaries ========== *)

(* eta <= 1 implies 0 <= 1 - eta (branch by branch in the Or encoding) *)
Lemma kl_one_minus_eta_nonneg : forall eta : Real,
  real_le eta real_one -> real_le real_zero (real_plus real_one (real_opp eta)).
Proof.
  intros eta Hle. destruct Hle as [Hlt | Heq].
  - exact (inl (real_eq_lt_lt real_zero (real_plus eta (real_opp eta))
                  (real_plus real_one (real_opp eta))
                  (real_eq_sym (real_plus eta (real_opp eta)) real_zero
                     (real_plus_opp eta))
                  (real_lt_plus_compat_lt_le eta real_one (real_opp eta) (real_opp eta)
                    Hlt (real_le_refl (real_opp eta))))).
  - exact (inr (real_eq_sym (real_plus real_one (real_opp eta)) real_zero
                    (real_eq_trans (real_plus real_one (real_opp eta))
                                 (real_plus eta (real_opp eta)) real_zero
                    (RealSetoid.real_eq_plus_compat real_one (real_opp eta)
                       eta (real_opp eta)
                       (real_eq_sym eta real_one Heq) (real_eq_refl (real_opp eta)))
                    (real_plus_opp eta)))).
Qed.

(* 0 <= a and 0 < b imply 0 < a + b *)
Lemma kl_le_lt_plus : forall a b : Real,
  real_le real_zero a -> real_lt real_zero b ->
  real_lt real_zero (real_plus a b).
Proof.
  intros a b Ha Hb. destruct Ha as [Hlt | Heq].
  exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero) (real_plus a b) kl_zero_plus_zero (real_lt_plus_compat real_zero a real_zero b Hlt Hb)).
  exact (real_lt_eq_lt real_zero b (real_plus a b) Hb (real_eq_sym (real_plus a b) b (real_eq_trans (real_plus a b) (real_plus real_zero b) b (RealSetoid.real_eq_plus_compat a b real_zero b (real_eq_sym real_zero a Heq) (real_eq_refl b)) (kl_plus_zero_l b)))).
Qed.

(* 0 <= m and 0 < E imply 0 <= E*m (weakly order-preserving multiplication
   plus an eq reformation) *)
Lemma kl_le_mult_weak_swap : forall m E : Real,
  real_le real_zero m -> real_lt real_zero E -> real_le real_zero (real_mult E m).
Proof.
  intros m E Hm HE.
  exact (kl_le_eq_r real_zero (real_mult m E) (real_mult E m)
           (kl_le_eq_l (real_mult real_zero E) (real_mult m E) real_zero
              (real_le_mult_compat_weak real_zero m E (inl HE) Hm)
              (kl_mult_zero_l E))
           (real_mult_comm m E)).
Qed.

(* seeding by a nonnegative/positive factor: c*(1 + t) <= c*e^t + c*delta *)
Lemma kl_seed_mul : forall (c t e2 : Real),
  real_le real_zero c -> real_lt real_zero e2 ->
  real_le (real_mult c (real_plus real_one t))
          (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2)).
Proof.
  intros c t e2 Hc0 He2.
  assert (Hseed : real_le (real_plus real_one t) (real_plus (cauchy_real_exp t) e2))
    by (apply RealInterfaceEnhancedMod.real_exp_ge_linear_eps; exact He2).
  assert (Hab : real_le (real_mult (real_plus real_one t) c)
                        (real_mult (real_plus (cauchy_real_exp t) e2) c))
    by (exact (real_le_mult_compat_weak (real_plus real_one t)
                 (real_plus (cauchy_real_exp t) e2) c Hc0 Hseed)).
  assert (Hdis : real_eq (real_mult (real_plus (cauchy_real_exp t) e2) c)
                         (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2)))
    by (exact (real_eq_trans
                 (real_mult (real_plus (cauchy_real_exp t) e2) c)
                 (real_plus (real_mult (cauchy_real_exp t) c) (real_mult e2 c))
                 (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2))
                 (kl_distrib_r (cauchy_real_exp t) e2 c)
                 (RealSetoid.real_eq_plus_compat
                    (real_mult (cauchy_real_exp t) c) (real_mult e2 c)
                    (real_mult c (cauchy_real_exp t)) (real_mult c e2)
                    (real_mult_comm (cauchy_real_exp t) c)
                    (real_mult_comm e2 c)))).
  apply (kl_le_eq_l (real_mult (real_plus real_one t) c)
                    (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2))
                    (real_mult c (real_plus real_one t))).
  - apply (kl_le_eq_r (real_mult (real_plus real_one t) c)
                      (real_mult (real_plus (cauchy_real_exp t) e2) c)
                      (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2))
                      Hab Hdis).
  - apply real_mult_comm.
Qed.


(* ========== M0.1: two-point convexity kernel (Varberg cone) ==========
   e^{(1-eta)x + eta y} <= (1-eta)*e^x + eta*e^y + eps.
   Statement-direction note: the direction as originally specified was
   reversed ((1-eta)e^x + eta*e^y <= e^z + eps is a reversed Jensen
   inequality and is false in general). The true e-form of the AM-GM
   a^{1-eta} b^eta <= (1-eta)a + eta b is the convexity direction
   e^z <= the weighted sum; its proof is exactly the Varberg cone
   argument of the upstream specification (multiply the two seed
   inequalities by e^z > 0 and merge with the weights). This file states
   the true direction. *)
Lemma real_exp_two_point_cvx_eps : forall (x y eta : Real),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (cauchy_real_exp (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                      (real_mult eta y)))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta))
                                            (cauchy_real_exp x))
                                (real_mult eta (cauchy_real_exp y)))
                     eps).
Proof.
  intros x y eta Heta_pos Heta_le eps Heps.
  set (m := real_plus real_one (real_opp eta)).
  set (z := real_plus (real_mult m x) (real_mult eta y)).
  set (s := real_plus x (real_opp y)).
  set (tA := real_mult eta s).
  set (tB := real_mult m (real_opp s)).
  assert (HEpos : real_lt real_zero (cauchy_real_exp z)) by apply cauchy_real_exp_pos.
  set (E := cauchy_real_exp z).
  set (cA := real_mult E m).
  set (cB := real_mult E eta).
  assert (Hm0 : real_le real_zero m)
    by exact (kl_one_minus_eta_nonneg eta Heta_le).
  assert (HcA0 : real_le real_zero cA) by exact (kl_le_mult_weak_swap m E Hm0 HEpos).
  assert (HcBpos : real_lt real_zero cB)
    by exact (real_mult_positive E eta HEpos Heta_pos).
  set (c := real_plus cA cB).
  assert (Hcpos : real_lt real_zero c) by exact (kl_le_lt_plus cA cB HcA0 HcBpos).
  set (d := real_mult eps (real_inv_pos c Hcpos)).
  assert (Hdpos : real_lt real_zero d)
    by exact (real_mult_positive eps (real_inv_pos c Hcpos) Heps
                (real_inv_pos_pos c Hcpos)).
  (* the two seed inequalities scaled by cA and cB respectively, then added *)
  assert (HseedA : real_le (real_mult cA (real_plus real_one tA))
                           (real_plus (real_mult cA (cauchy_real_exp tA))
                                      (real_mult cA d)))
    by exact (kl_seed_mul cA tA d HcA0 Hdpos).
  assert (HseedB : real_le (real_mult cB (real_plus real_one tB))
                           (real_plus (real_mult cB (cauchy_real_exp tB))
                                      (real_mult cB d)))
    by exact (kl_seed_mul cB tB d (inl HcBpos) Hdpos).
  assert (Hsumle : real_le (real_plus (real_mult cA (real_plus real_one tA))
                                      (real_mult cB (real_plus real_one tB)))
                           (real_plus (real_plus (real_mult cA (cauchy_real_exp tA))
                                                 (real_mult cA d))
                                      (real_plus (real_mult cB (cauchy_real_exp tB))
                                                 (real_mult cB d))))
    by exact (real_le_plus_compat _ _ _ _ HseedA HseedB).
  (* cone identity: the left weighted sum equals E (pure ring algebra once
   m is expanded) *)
  assert (EqCore : real_eq (real_plus (real_mult cA (real_plus real_one tA))
                                      (real_mult cB (real_plus real_one tB)))
                           E)
    by exact (kl_ring_core E eta s).
  (* exponential regrouping: E*e^{tA} == e^x and E*e^{tB} == e^y *)
  assert (HEqA : real_eq (real_mult E (cauchy_real_exp tA)) (cauchy_real_exp x))
    by exact (real_eq_trans (real_mult E (cauchy_real_exp tA))
                            (cauchy_real_exp (real_plus z tA)) (cauchy_real_exp x)
                 (real_eq_sym (cauchy_real_exp (real_plus z tA))
                              (real_mult (cauchy_real_exp z) (cauchy_real_exp tA))
                              (cauchy_real_exp_plus z tA))
                 (cauchy_real_exp_wd (real_plus z tA) x (kl_z_tA x y eta))).
  assert (HEqB : real_eq (real_mult E (cauchy_real_exp tB)) (cauchy_real_exp y))
    by exact (real_eq_trans (real_mult E (cauchy_real_exp tB))
                            (cauchy_real_exp (real_plus z tB)) (cauchy_real_exp y)
                 (real_eq_sym (cauchy_real_exp (real_plus z tB))
                              (real_mult (cauchy_real_exp z) (cauchy_real_exp tB))
                              (cauchy_real_exp_plus z tB))
                 (cauchy_real_exp_wd (real_plus z tB) y (kl_z_tB x y eta))).
  (* error absorption: cA*d + cB*d == eps, with d := eps*(1/c) *)
  assert (ErrEq : real_eq (real_plus (real_mult cA d) (real_mult cB d)) eps)
    by exact (real_eq_trans (real_plus (real_mult cA d) (real_mult cB d))
                            (real_mult c d) eps
                 (kl_sum_prod_r cA cB d)
                 (real_eq_trans (real_mult c d)
                    (real_mult eps (real_mult c (real_inv_pos c Hcpos))) eps
                    (kl_swap3 c eps (real_inv_pos c Hcpos))
                    (real_eq_trans
                       (real_mult eps (real_mult c (real_inv_pos c Hcpos)))
                       (real_mult eps real_one) eps
                       (RealSetoid.real_eq_mult_compat eps
                          (real_mult c (real_inv_pos c Hcpos)) eps real_one
                          (real_eq_refl eps) (real_inv_pos_correct c Hcpos))
                       (real_mult_one eps)))).
  (* final eq assembly: the four-term reordering plus the exponential
   regrouping plus the error absorption *)
  assert (EqFinal : real_eq (real_plus (real_plus (real_mult cA (cauchy_real_exp tA))
                                                  (real_mult cA d))
                                       (real_plus (real_mult cB (cauchy_real_exp tB))
                                                  (real_mult cB d)))
                            (real_plus (real_plus (real_mult m (cauchy_real_exp x))
                                                  (real_mult eta (cauchy_real_exp y)))
                                       eps)).
  { apply (real_eq_trans
             (real_plus (real_plus (real_mult cA (cauchy_real_exp tA)) (real_mult cA d))
                        (real_plus (real_mult cB (cauchy_real_exp tB)) (real_mult cB d)))
             (real_plus (real_plus (real_mult cA (cauchy_real_exp tA))
                                   (real_mult cB (cauchy_real_exp tB)))
                        (real_plus (real_mult cA d) (real_mult cB d)))
             (real_plus (real_plus (real_mult m (cauchy_real_exp x))
                                   (real_mult eta (cauchy_real_exp y))) eps)).
    - exact (real_plus_swap_mid (real_mult cA (cauchy_real_exp tA)) (real_mult cA d)
                                (real_mult cB (cauchy_real_exp tB)) (real_mult cB d)).
    - exact (RealSetoid.real_eq_plus_compat
               (real_plus (real_mult cA (cauchy_real_exp tA))
                          (real_mult cB (cauchy_real_exp tB)))
               (real_plus (real_mult cA d) (real_mult cB d))
               (real_plus (real_mult m (cauchy_real_exp x))
                          (real_mult eta (cauchy_real_exp y)))
               eps
               (RealSetoid.real_eq_plus_compat
                  (real_mult cA (cauchy_real_exp tA))
                  (real_mult cB (cauchy_real_exp tB))
                  (real_mult m (cauchy_real_exp x))
                  (real_mult eta (cauchy_real_exp y))
                  (real_eq_trans (real_mult cA (cauchy_real_exp tA))
                                 (real_mult m (real_mult E (cauchy_real_exp tA)))
                                 (real_mult m (cauchy_real_exp x))
                    (kl_assoc_swap E m (cauchy_real_exp tA))
                    (RealSetoid.real_eq_mult_compat m
                       (real_mult E (cauchy_real_exp tA)) m (cauchy_real_exp x)
                       (real_eq_refl m) HEqA))
                  (real_eq_trans (real_mult cB (cauchy_real_exp tB))
                                 (real_mult eta (real_mult E (cauchy_real_exp tB)))
                                 (real_mult eta (cauchy_real_exp y))
                    (kl_assoc_swap E eta (cauchy_real_exp tB))
                    (RealSetoid.real_eq_mult_compat eta
                       (real_mult E (cauchy_real_exp tB)) eta (cauchy_real_exp y)
                       (real_eq_refl eta) HEqB)))
               ErrEq). }
  exact (kl_le_eq_r E
           (real_plus (real_plus (real_mult cA (cauchy_real_exp tA)) (real_mult cA d))
                      (real_plus (real_mult cB (cauchy_real_exp tB)) (real_mult cB d)))
           (real_plus (real_plus (real_mult m (cauchy_real_exp x))
                                 (real_mult eta (cauchy_real_exp y))) eps)
           (kl_le_eq_l
              (real_plus (real_mult cA (real_plus real_one tA))
                         (real_mult cB (real_plus real_one tB)))
              (real_plus (real_plus (real_mult cA (cauchy_real_exp tA))
                                    (real_mult cA d))
                         (real_plus (real_mult cB (cauchy_real_exp tB))
                                    (real_mult cB d)))
              E Hsumle EqCore)
           EqFinal).
Qed.

(* ========== M0.2: pointwise AM-GM ==========
   a^{1-eta}*b^eta <= (1-eta)*a + eta*b + eps, where a^{alpha} :=
   e^{alpha*log a}. *)
Definition real_pow_pos (a alpha : Real) (Ha : real_lt real_zero a) : Real :=
  cauchy_real_exp (real_mult alpha (cw_log a Ha)).

Lemma real_amgm_pointwise_eps : forall (a b eta : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_mult (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                     (real_pow_pos b eta Hb))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                                (real_mult eta b)) eps).
Proof.
  intros a b eta Ha Hb Heta_pos Heta_le eps Heps.
  assert (Hcvx : real_le
            (cauchy_real_exp (real_plus
               (real_mult (real_plus real_one (real_opp eta)) (cw_log a Ha))
               (real_mult eta (cw_log b Hb))))
            (real_plus (real_plus
               (real_mult (real_plus real_one (real_opp eta))
                          (cauchy_real_exp (cw_log a Ha)))
               (real_mult eta (cauchy_real_exp (cw_log b Hb)))) eps))
    by exact (real_exp_two_point_cvx_eps (cw_log a Ha) (cw_log b Hb) eta
                Heta_pos Heta_le eps Heps).
  exact (kl_le_eq_r
           (real_mult (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                      (real_pow_pos b eta Hb))
           (real_plus (real_plus
                        (real_mult (real_plus real_one (real_opp eta))
                                   (cauchy_real_exp (cw_log a Ha)))
                        (real_mult eta (cauchy_real_exp (cw_log b Hb)))) eps)
           (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                                 (real_mult eta b)) eps)
           (kl_le_eq_l
              (cauchy_real_exp (real_plus
                 (real_mult (real_plus real_one (real_opp eta)) (cw_log a Ha))
                 (real_mult eta (cw_log b Hb))))
              (real_plus (real_plus
                            (real_mult (real_plus real_one (real_opp eta))
                                       (cauchy_real_exp (cw_log a Ha)))
                            (real_mult eta (cauchy_real_exp (cw_log b Hb)))) eps)
              (real_mult (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                         (real_pow_pos b eta Hb))
              Hcvx
              (cauchy_real_exp_plus
                 (real_mult (real_plus real_one (real_opp eta)) (cw_log a Ha))
                 (real_mult eta (cw_log b Hb))))
           (RealSetoid.real_eq_plus_compat
              (real_plus (real_mult (real_plus real_one (real_opp eta))
                                    (cauchy_real_exp (cw_log a Ha)))
                         (real_mult eta (cauchy_real_exp (cw_log b Hb))))
              eps
              (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                         (real_mult eta b))
              eps
              (RealSetoid.real_eq_plus_compat
                 (real_mult (real_plus real_one (real_opp eta))
                            (cauchy_real_exp (cw_log a Ha)))
                 (real_mult eta (cauchy_real_exp (cw_log b Hb)))
                 (real_mult (real_plus real_one (real_opp eta)) a)
                 (real_mult eta b)
                 (RealSetoid.real_eq_mult_compat
                    (real_plus real_one (real_opp eta))
                    (cauchy_real_exp (cw_log a Ha))
                    (real_plus real_one (real_opp eta)) a
                    (real_eq_refl (real_plus real_one (real_opp eta)))
                    (cw_log_exp_right a Ha))
                 (RealSetoid.real_eq_mult_compat eta
                    (cauchy_real_exp (cw_log b Hb)) eta b
                    (real_eq_refl eta) (cw_log_exp_right b Hb)))
              (real_eq_refl eps))).
Qed.

(* ========== M1: summed interpolation inequality (Z <= 1 + eps) ==========
   Z := Sum_i pi_t(i)^{1-eta} * pi*(i)^eta <= 1 + eps.
   Error absorption: the pointwise error is taken as eps*pi_t(i) (a
   positive weight); after normalization Sum pi_t == 1 the total error
   Sum (eps*pi_t) == eps*1 == eps -- no division, no bisection, pure
   normalization absorption. *)
Lemma real_interp_Z_le_one_eps :
  forall (n : nat) (pit pist : nat -> Real) (eta : Real)
    (Hpit : forall i : nat, real_lt real_zero (pit i))
    (Hpist : forall i : nat, real_lt real_zero (pist i))
    (Hnormp : real_eq (real_list_sum nat pit (seq 0 n)) real_one)
    (Hnormq : real_eq (real_list_sum nat pist (seq 0 n)) real_one),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_list_sum nat
             (fun i : nat => real_mult
                (real_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i))
                (real_pow_pos (pist i) eta (Hpist i)))
             (seq 0 n))
          (real_plus real_one eps).
Proof.
  intros n pit pist eta Hpit Hpist Hnormp Hnormq Heta_pos Heta_le eps Heps.
  set (m := real_plus real_one (real_opp eta)).
  (* pointwise AM-GM with the error term weighted by eps*pit i *)
  assert (Hpt : forall i : nat,
            real_le (real_mult (real_pow_pos (pit i) m (Hpit i))
                               (real_pow_pos (pist i) eta (Hpist i)))
                    (real_plus (real_plus (real_mult m (pit i))
                                          (real_mult eta (pist i)))
                               (real_mult eps (pit i)))).
  { intro i.
    exact (real_amgm_pointwise_eps (pit i) (pist i) eta (Hpit i) (Hpist i)
             Heta_pos Heta_le (real_mult eps (pit i))
             (real_mult_positive eps (pit i) Heps (Hpit i))). }
  assert (Hsumle : real_le
            (real_list_sum nat (fun i : nat => real_mult
                                  (real_pow_pos (pit i) m (Hpit i))
                                  (real_pow_pos (pist i) eta (Hpist i))) (seq 0 n))
            (real_list_sum nat (fun i : nat => real_plus
                                  (real_plus (real_mult m (pit i))
                                             (real_mult eta (pist i)))
                                  (real_mult eps (pit i))) (seq 0 n)))
    by exact (real_list_sum_le nat _ _ (seq 0 n) Hpt).
  (* the summed right side splits as Sum f + Sum g, with
   f i := m*pit i + eta*pist i and g i := eps*pit i *)
  assert (Hsplit : real_eq
            (real_list_sum nat (fun i : nat => real_plus
                                  (real_plus (real_mult m (pit i))
                                             (real_mult eta (pist i)))
                                  (real_mult eps (pit i))) (seq 0 n))
            (real_plus (real_list_sum nat (fun i : nat => real_plus
                                              (real_mult m (pit i))
                                              (real_mult eta (pist i))) (seq 0 n))
                       (real_list_sum nat (fun i : nat => real_mult eps (pit i))
                          (seq 0 n))))
    by exact (real_list_sum_add nat _ _ (seq 0 n)).
  (* Sum f == m*Sum pit + eta*Sum pist == m + eta == 1 *)
  assert (Hf : real_eq (real_list_sum nat (fun i : nat => real_plus
                                             (real_mult m (pit i))
                                             (real_mult eta (pist i))) (seq 0 n))
                       real_one).
  { apply (real_eq_trans _
             (real_plus (real_list_sum nat (fun i : nat => real_mult m (pit i)) (seq 0 n))
                        (real_list_sum nat (fun i : nat => real_mult eta (pist i)) (seq 0 n)))).
    - exact (real_list_sum_add nat _ _ (seq 0 n)).
    - apply (real_eq_trans _
                (real_plus (real_mult m (real_list_sum nat pit (seq 0 n)))
                           (real_mult eta (real_list_sum nat pist (seq 0 n))))).
      + exact (RealSetoid.real_eq_plus_compat _ _ _ _
                   (real_list_sum_linear nat m pit (seq 0 n))
                   (real_list_sum_linear nat eta pist (seq 0 n))).
      + apply (real_eq_trans _ (real_plus m eta)).
        * exact (RealSetoid.real_eq_plus_compat
                    (real_mult m (real_list_sum nat pit (seq 0 n)))
                    (real_mult eta (real_list_sum nat pist (seq 0 n))) m eta
                    (real_eq_trans (real_mult m (real_list_sum nat pit (seq 0 n)))
                       (real_mult m real_one) m
                       (RealSetoid.real_eq_mult_compat m
                          (real_list_sum nat pit (seq 0 n)) m real_one
                          (real_eq_refl m) Hnormp)
                       (real_mult_one m))
                    (real_eq_trans (real_mult eta (real_list_sum nat pist (seq 0 n)))
                       (real_mult eta real_one) eta
                       (RealSetoid.real_eq_mult_compat eta
                          (real_list_sum nat pist (seq 0 n)) eta real_one
                          (real_eq_refl eta) Hnormq)
                       (real_mult_one eta))).
        * exact (kl_ring_m_plus_eta eta). }
  (* Sum g == eps*Sum pit == eps*1 == eps *)
  assert (Hg : real_eq (real_list_sum nat (fun i : nat => real_mult eps (pit i)) (seq 0 n)) eps).
  { apply (real_eq_trans _ (real_mult eps (real_list_sum nat pit (seq 0 n)))).
    - exact (real_list_sum_linear nat eps pit (seq 0 n)).
    - exact (real_eq_trans (real_mult eps (real_list_sum nat pit (seq 0 n)))
                           (real_mult eps real_one) eps
               (RealSetoid.real_eq_mult_compat eps (real_list_sum nat pit (seq 0 n))
                  eps real_one (real_eq_refl eps) Hnormp)
               (real_mult_one eps)). }
  (* closing: Z <= Sum f + Sum g == 1 + eps *)
  exact (kl_le_eq_r
           (real_list_sum nat (fun i : nat => real_mult
                                 (real_pow_pos (pit i) m (Hpit i))
                                 (real_pow_pos (pist i) eta (Hpist i))) (seq 0 n))
           (real_list_sum nat (fun i : nat => real_plus
                                 (real_plus (real_mult m (pit i))
                                            (real_mult eta (pist i)))
                                 (real_mult eps (pit i))) (seq 0 n))
           (real_plus real_one eps)
           Hsumle
           (real_eq_trans
              (real_list_sum nat (fun i : nat => real_plus
                                    (real_plus (real_mult m (pit i))
                                               (real_mult eta (pist i)))
                                    (real_mult eps (pit i))) (seq 0 n))
              (real_plus (real_list_sum nat (fun i : nat => real_plus
                                                (real_mult m (pit i))
                                                (real_mult eta (pist i))) (seq 0 n))
                         (real_list_sum nat (fun i : nat => real_mult eps (pit i))
                            (seq 0 n)))
              (real_plus real_one eps)
              Hsplit
              (RealSetoid.real_eq_plus_compat
                 (real_list_sum nat (fun i : nat => real_plus
                                       (real_mult m (pit i))
                                       (real_mult eta (pist i))) (seq 0 n))
                 (real_list_sum nat (fun i : nat => real_mult eps (pit i)) (seq 0 n))
                 real_one eps Hf Hg))).
Qed.

(* ========== M2 preliminaries: log algebra plus ring identities ========== *)

(* a + b == 0 implies b == -a *)
Lemma kl_eq_plus_opp_uniq_r : forall a b : Real,
  real_eq (real_plus a b) real_zero -> real_eq b (real_opp a).
Proof.
  intros a b H.
  assert (Hstep1 : real_eq (real_plus (real_opp a) (real_plus a b))
                           (real_plus (real_opp a) real_zero))
    by exact (RealSetoid.real_eq_plus_compat (real_opp a) (real_plus a b)
                (real_opp a) real_zero (real_eq_refl (real_opp a)) H).
  assert (Hstep2 : real_eq (real_plus (real_opp a) real_zero) (real_opp a))
    by exact (real_plus_zero (real_opp a)).
  assert (Hstep3 : real_eq (real_plus (real_opp a) (real_plus a b)) b).
  { exact (real_eq_trans (real_plus (real_opp a) (real_plus a b))
                         (real_plus (real_plus (real_opp a) a) b) b
             (real_plus_assoc (real_opp a) a b)
             (real_eq_trans (real_plus (real_plus (real_opp a) a) b)
                            (real_plus real_zero b) b
                (RealSetoid.real_eq_plus_compat (real_plus (real_opp a) a) b
                   real_zero b
                   (real_eq_trans (real_plus (real_opp a) a)
                      (real_plus a (real_opp a)) real_zero
                      (real_plus_comm (real_opp a) a) (real_plus_opp a))
                   (real_eq_refl b))
                (kl_plus_zero_l b))). }
  exact (real_eq_trans b (real_plus (real_opp a) (real_plus a b)) (real_opp a)
           (real_eq_sym _ _ Hstep3) (real_eq_trans _ _ _ Hstep1 Hstep2)).
Qed.

(* log(1/x) == -log x *)
Lemma kl_log_inv : forall (x : Real) (Hx : real_lt real_zero x)
    (Hix : real_lt real_zero (real_inv_pos x Hx)),
  real_eq (cw_log (real_inv_pos x Hx) Hix) (real_opp (cw_log x Hx)).
Proof.
  intros x Hx Hix.
  assert (Hprodpos : real_lt real_zero (real_mult x (real_inv_pos x Hx)))
    by exact (real_mult_positive x (real_inv_pos x Hx) Hx Hix).
  assert (Hmult : real_eq (cw_log (real_mult x (real_inv_pos x Hx)) Hprodpos)
                           (real_plus (cw_log x Hx) (cw_log (real_inv_pos x Hx) Hix)))
    by exact (log_inv_mult_thm x (real_inv_pos x Hx) Hx Hix Hprodpos).
  assert (Hone : real_eq (cw_log (real_mult x (real_inv_pos x Hx)) Hprodpos) real_zero).
  { apply (real_eq_trans _ (cw_log real_one real_lt_zero_one)).
    - exact (real_log_wd (real_mult x (real_inv_pos x Hx)) real_one Hprodpos
                real_lt_zero_one (real_inv_pos_correct x Hx)).
    - exact (real_log_one real_lt_zero_one). }
  exact (kl_eq_plus_opp_uniq_r (cw_log x Hx) (cw_log (real_inv_pos x Hx) Hix)
           (real_eq_trans (real_plus (cw_log x Hx) (cw_log (real_inv_pos x Hx) Hix))
              (cw_log (real_mult x (real_inv_pos x Hx)) Hprodpos) real_zero
              (real_eq_sym
                 (cw_log (real_mult x (real_inv_pos x Hx)) Hprodpos)
                 (real_plus (cw_log x Hx) (cw_log (real_inv_pos x Hx) Hix)) Hmult)
              Hone)).
Qed.

(* ring identity family *)
Lemma kl_ring_reassoc : forall X Y Z W : Real,
  real_eq (real_mult (real_mult (real_mult X Y) Z) W)
          (real_mult X (real_mult Y (real_mult Z W))).
Proof. intros X Y Z W. destruct X as [a Ha]. destruct Y as [b Hb]. destruct Z as [c Hc].
  destruct W as [d Hd]. apply real_eq_of_zero_diff. intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

Lemma kl_ring_opp_swap : forall X Y : Real,
  real_eq (real_opp (real_plus X (real_opp Y))) (real_plus Y (real_opp X)).
Proof. intros X Y. destruct X as [a Ha]. destruct Y as [b Hb].
  apply real_eq_of_zero_diff. intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

Lemma kl_ring_log4 : forall eta lp lr LZ : Real,
  real_eq (real_plus (real_mult (real_plus real_one (real_opp eta)) lp)
                     (real_plus (real_mult eta lr)
                                (real_plus (real_opp LZ) (real_opp lp))))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) lp)
                                (real_mult eta lr))
                     (real_plus (real_opp LZ) (real_opp lp))).
Proof. intros eta lp lr LZ. destruct eta as [e He]. destruct lp as [u Hu].
  destruct lr as [v Hv]. destruct LZ as [w Hw]. apply real_eq_of_zero_diff.
  intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

Lemma kl_ring_neg4 : forall eta lp lr LZ : Real,
  real_eq (real_opp (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) lp)
                                          (real_mult eta lr))
                               (real_plus (real_opp LZ) (real_opp lp))))
          (real_plus (real_mult eta (real_plus lp (real_opp lr))) LZ).
Proof. intros eta lp lr LZ. destruct eta as [e He]. destruct lp as [u Hu].
  destruct lr as [v Hv]. destruct LZ as [w Hw]. apply real_eq_of_zero_diff.
  intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

Lemma kl_ring_kl_split : forall eta W X Z : Real,
  real_eq (real_mult W (real_plus (real_mult eta X) Z))
          (real_plus (real_mult eta (real_mult W X)) (real_mult W Z)).
Proof. intros eta W X Z. destruct eta as [e He]. destruct W as [w Hw].
  destruct X as [x Hx]. destruct Z as [z Hz]. apply real_eq_of_zero_diff.
  intro n. simpl.
  apply qeq_imp_qeqT. ring. Qed.

(* the le-monotonicity of log (branch by branch in the Or encoding, as in
   UpLogMono) *)
Lemma kl_log_le_mono : forall (a b : Real) (Ha : real_lt real_zero a)
    (Hb : real_lt real_zero b),
  real_le a b -> real_le (cw_log a Ha) (cw_log b Hb).
Proof.
  intros a b Ha Hb Hab. destruct Hab as [Hlt | Heq].
  - exact (inl (real_log_lt_mono a b Ha Hb Hlt)).
  - exact (inr (real_log_wd a b Ha Hb Heq)).
Qed.

(* ========== M2: KL identity assembly ==========
   pi_{t+1}(i) := pi_t(i)^{1-eta} * pi-star(i)^eta / Z (the geometric
   interpolation policy).
   Exact identity: KL(pi_t || pi_{t+1}) == eta*KL(pi_t || pi-star) + log Z
   (pointwise kl_term algebra plus normalization absorption Sum p == 1);
   then M1 (Z <= 1 + eps), the strict seed (1 + eps < e^eps, hence
   log(1 + eps) < eps), and monotonicity of log give log Z < eps, so
   KL(pi_t || pi_{t+1}) <= eta*KL(pi_t || pi-star) + eps. *)

(* the geometric-interpolation partition function
   Z := Sum_i pi_t(i)^{1-eta} * pi*(i)^eta *)
Definition real_interp_Z (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i)) : Real :=
  real_list_sum nat
    (fun i : nat => real_mult
       (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
       (real_pow_pos (r i) eta (Hr i)))
    (seq 0 n).

(* the next policy pi_{t+1}(i) := pi_t(i)^{1-eta} * pi*(i)^eta / Z *)
Definition real_step_next (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr)) : nat -> Real :=
  fun i : nat => real_mult
    (real_mult (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
               (real_pow_pos (r i) eta (Hr i)))
    (real_inv_pos (real_interp_Z n p r eta Hp Hr) HZ).

Theorem real_step_kl_eta_bound_eps :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnormp : real_eq (real_list_sum nat p (seq 0 n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (seq 0 n)) real_one)
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n p r eta Hp Hr HZ i)),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_list_sum nat
             (fun i : nat => real_kl_term (p i)
                             (real_step_next n p r eta Hp Hr HZ i) (Hp i) (Hqv i))
             (seq 0 n))
          (real_plus (real_mult eta
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (p i) (r i) (Hp i) (Hr i))
                           (seq 0 n)))
                     eps).
Proof.
  intros n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta_pos Heta_le eps Heps.
  set (m := real_plus real_one (real_opp eta)).
  set (Z := real_interp_Z n p r eta Hp Hr).
  set (q := real_step_next n p r eta Hp Hr HZ).
  set (LZ := cw_log Z HZ).
  set (Rsum := real_list_sum nat
                 (fun i : nat => real_kl_term (p i) (r i) (Hp i) (Hr i)) (seq 0 n)).
  (* ---- pointwise KL identity (exact eq) ---- *)
  assert (Hpi : forall i : nat,
    real_eq (real_kl_term (p i) (q i) (Hp i) (Hqv i))
            (real_plus (real_mult eta (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                       (real_mult (p i) LZ))).
  { intro i.
    set (ipp := real_inv_pos (p i) (Hp i)).
    set (izz := real_inv_pos Z HZ).
    set (pA := real_pow_pos (p i) m (Hp i)).
    set (pB := real_pow_pos (r i) eta (Hr i)).
    (* the proof terms mirror the unfolding of [real_kl_term] exactly
   ([cw_log] depends on its proof argument) *)
    assert (Hip : real_lt real_zero ipp) by exact (real_inv_pos_pos (p i) (Hp i)).
    assert (Hizp : real_lt real_zero izz) by exact (real_inv_pos_pos Z HZ).
    assert (HpA : real_lt real_zero pA)
      by exact (cauchy_real_exp_pos (real_mult m (cw_log (p i) (Hp i)))).
    assert (HpB : real_lt real_zero pB)
      by exact (cauchy_real_exp_pos (real_mult eta (cw_log (r i) (Hr i)))).
    set (Hqqlog := real_mult_positive (q i) (real_inv_pos (p i) (Hp i)) (Hqv i)
                  (real_inv_pos_pos (p i) (Hp i))).
    set (Hrplog := real_mult_positive (r i) (real_inv_pos (p i) (Hp i)) (Hr i)
                  (real_inv_pos_pos (p i) (Hp i))).
    (* log-value facts *)
    assert (HlA : real_eq (cw_log pA HpA) (real_mult m (cw_log (p i) (Hp i))))
      by exact (log_inv_exp_neg_thm (real_mult m (cw_log (p i) (Hp i))) HpA).
    assert (HlB : real_eq (cw_log pB HpB) (real_mult eta (cw_log (r i) (Hr i))))
      by exact (log_inv_exp_neg_thm (real_mult eta (cw_log (r i) (Hr i))) HpB).
    assert (HlZ : real_eq (cw_log izz Hizp) (real_opp LZ))
      by exact (kl_log_inv Z HZ Hizp).
    assert (HlP : real_eq (cw_log ipp Hip) (real_opp (cw_log (p i) (Hp i))))
      by exact (kl_log_inv (p i) (Hp i) Hip).
    (* log(r * inv p) == log r + (-log p) *)
    assert (Hlogrp : real_eq (cw_log (real_mult (r i) ipp) Hrplog)
                             (real_plus (cw_log (r i) (Hr i))
                                        (real_opp (cw_log (p i) (Hp i))))).
    { exact (real_eq_trans (cw_log (real_mult (r i) ipp) Hrplog)
               (real_plus (cw_log (r i) (Hr i)) (cw_log ipp Hip))
               (real_plus (cw_log (r i) (Hr i)) (real_opp (cw_log (p i) (Hp i))))
               (log_inv_mult_thm (r i) ipp (Hr i) Hip Hrplog)
               (RealSetoid.real_eq_plus_compat (cw_log (r i) (Hr i)) (cw_log ipp Hip)
                  (cw_log (r i) (Hr i)) (real_opp (cw_log (p i) (Hp i)))
                  (real_eq_refl (cw_log (r i) (Hr i))) HlP)). }
    (* rearranging the factors of q * inv p (pure ring algebra) *)
    assert (Hring1 : real_eq (real_mult (q i) ipp)
                             (real_mult pA (real_mult pB (real_mult izz ipp))))
      by exact (kl_ring_reassoc pA pB izz ipp).
    assert (Hpos3 : real_lt real_zero (real_mult izz ipp))
      by exact (real_mult_positive izz ipp Hizp Hip).
    assert (Hpos2 : real_lt real_zero (real_mult pB (real_mult izz ipp)))
      by exact (real_mult_positive pB (real_mult izz ipp) HpB Hpos3).
    assert (HAB4 : real_lt real_zero (real_mult pA (real_mult pB (real_mult izz ipp))))
      by exact (real_mult_positive pA (real_mult pB (real_mult izz ipp)) HpA Hpos2).
    (* splitting log(q * inv p) into four terms *)
    assert (Hlog4 : real_eq (cw_log (real_mult (q i) ipp) Hqqlog)
                       (real_plus (cw_log pA HpA)
                          (real_plus (cw_log pB HpB)
                             (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))).
    { apply (real_eq_trans (cw_log (real_mult (q i) ipp) Hqqlog)
               (cw_log (real_mult pA (real_mult pB (real_mult izz ipp))) HAB4)
               (real_plus (cw_log pA HpA)
                  (real_plus (cw_log pB HpB)
                     (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))).
      - exact (real_log_wd (real_mult (q i) ipp)
                 (real_mult pA (real_mult pB (real_mult izz ipp))) Hqqlog HAB4 Hring1).
      - exact (real_eq_trans
                  (cw_log (real_mult pA (real_mult pB (real_mult izz ipp))) HAB4)
                  (real_plus (cw_log pA HpA)
                     (cw_log (real_mult pB (real_mult izz ipp)) Hpos2))
                  (real_plus (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))
                  (log_inv_mult_thm pA (real_mult pB (real_mult izz ipp)) HpA Hpos2 HAB4)
                  (RealSetoid.real_eq_plus_compat (cw_log pA HpA)
                     (cw_log (real_mult pB (real_mult izz ipp)) Hpos2)
                     (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip)))
                     (real_eq_refl (cw_log pA HpA))
                     (real_eq_trans
                        (cw_log (real_mult pB (real_mult izz ipp)) Hpos2)
                        (real_plus (cw_log pB HpB) (cw_log (real_mult izz ipp) Hpos3))
                        (real_plus (cw_log pB HpB)
                           (real_plus (cw_log izz Hizp) (cw_log ipp Hip)))
                        (log_inv_mult_thm pB (real_mult izz ipp) HpB Hpos3 Hpos2)
                        (RealSetoid.real_eq_plus_compat (cw_log pB HpB)
                           (cw_log (real_mult izz ipp) Hpos3)
                           (cw_log pB HpB)
                           (real_plus (cw_log izz Hizp) (cw_log ipp Hip))
                           (real_eq_refl (cw_log pB HpB))
                           (log_inv_mult_thm izz ipp Hizp Hip Hpos3))))). }
    (* substituting the log values *)
    assert (Hlog4' : real_eq (cw_log (real_mult (q i) ipp) Hqqlog)
                       (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                             (real_mult eta (cw_log (r i) (Hr i))))
                                  (real_plus (real_opp LZ)
                                             (real_opp (cw_log (p i) (Hp i)))))).
    { apply (real_eq_trans (cw_log (real_mult (q i) ipp) Hqqlog)
               (real_plus (cw_log pA HpA)
                  (real_plus (cw_log pB HpB)
                     (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))
               (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                     (real_mult eta (cw_log (r i) (Hr i))))
                          (real_plus (real_opp LZ)
                                     (real_opp (cw_log (p i) (Hp i)))))).
      - exact Hlog4.
      - exact (real_eq_trans
                  (real_plus (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))
                  (real_plus (real_mult m (cw_log (p i) (Hp i)))
                     (real_plus (real_mult eta (cw_log (r i) (Hr i)))
                        (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i))))))
                  (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                        (real_mult eta (cw_log (r i) (Hr i))))
                     (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i)))))
                  (RealSetoid.real_eq_plus_compat (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip)))
                     (real_mult m (cw_log (p i) (Hp i)))
                     (real_plus (real_mult eta (cw_log (r i) (Hr i)))
                        (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i)))))
                     HlA
                     (RealSetoid.real_eq_plus_compat (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip))
                        (real_mult eta (cw_log (r i) (Hr i)))
                        (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i))))
                        HlB
                        (RealSetoid.real_eq_plus_compat (cw_log izz Hizp)
                           (cw_log ipp Hip) (real_opp LZ)
                           (real_opp (cw_log (p i) (Hp i))) HlZ HlP)))
                  (kl_ring_log4 eta (cw_log (p i) (Hp i)) (cw_log (r i) (Hr i)) LZ)). }
    (* negating and regrouping by ring algebra:
   -log(q * inv p) == eta*(log p - log r) + LZ *)
    assert (Hneg : real_eq (real_opp (cw_log (real_mult (q i) ipp) Hqqlog))
                       (real_plus (real_mult eta
                                     (real_plus (cw_log (p i) (Hp i))
                                                (real_opp (cw_log (r i) (Hr i)))))
                                  LZ)).
    { exact (real_eq_trans (real_opp (cw_log (real_mult (q i) ipp) Hqqlog))
               (real_opp (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                                (real_mult eta (cw_log (r i) (Hr i))))
                                    (real_plus (real_opp LZ)
                                               (real_opp (cw_log (p i) (Hp i))))))
               (real_plus (real_mult eta
                             (real_plus (cw_log (p i) (Hp i))
                                        (real_opp (cw_log (r i) (Hr i)))))
                          LZ)
               (RealSetoid.real_eq_opp_compat
                  (cw_log (real_mult (q i) ipp) Hqqlog)
                  (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                        (real_mult eta (cw_log (r i) (Hr i))))
                     (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i)))))
                  Hlog4')
               (kl_ring_neg4 eta (cw_log (p i) (Hp i)) (cw_log (r i) (Hr i)) LZ)). }
    (* the r side: log p - log r == -log(r * inv p) *)
    assert (HnegR : real_eq (real_plus (cw_log (p i) (Hp i))
                                       (real_opp (cw_log (r i) (Hr i))))
                            (real_opp (cw_log (real_mult (r i) ipp) Hrplog))).
    { exact (real_eq_trans
                (real_plus (cw_log (p i) (Hp i)) (real_opp (cw_log (r i) (Hr i))))
                (real_opp (real_plus (cw_log (r i) (Hr i))
                                     (real_opp (cw_log (p i) (Hp i)))))
                (real_opp (cw_log (real_mult (r i) ipp) Hrplog))
                (real_eq_sym (real_opp (real_plus (cw_log (r i) (Hr i))
                                                  (real_opp (cw_log (p i) (Hp i)))))
                   (real_plus (cw_log (p i) (Hp i))
                              (real_opp (cw_log (r i) (Hr i))))
                   (kl_ring_opp_swap (cw_log (r i) (Hr i)) (cw_log (p i) (Hp i))))
                (real_eq_sym (real_opp (cw_log (real_mult (r i) ipp) Hrplog))
                   (real_opp (real_plus (cw_log (r i) (Hr i))
                                        (real_opp (cw_log (p i) (Hp i)))))
                   (RealSetoid.real_eq_opp_compat
                      (cw_log (real_mult (r i) ipp) Hrplog)
                      (real_plus (cw_log (r i) (Hr i))
                                 (real_opp (cw_log (p i) (Hp i))))
                      Hlogrp))). }
    (* final assembly: kl(p, q) == eta*kl(p, r) + p*LZ *)
    exact (real_eq_trans
              (real_mult (p i) (real_opp (cw_log (real_mult (q i) ipp) Hqqlog)))
              (real_plus
                 (real_mult eta
                    (real_mult (p i)
                       (real_plus (cw_log (p i) (Hp i))
                                  (real_opp (cw_log (r i) (Hr i))))))
                 (real_mult (p i) LZ))
              (real_plus (real_mult eta (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                         (real_mult (p i) LZ))
              (real_eq_trans
                 (real_mult (p i) (real_opp (cw_log (real_mult (q i) ipp) Hqqlog)))
                 (real_mult (p i)
                    (real_plus (real_mult eta
                                  (real_plus (cw_log (p i) (Hp i))
                                             (real_opp (cw_log (r i) (Hr i)))))
                               LZ))
                 (real_plus
                    (real_mult eta
                       (real_mult (p i)
                          (real_plus (cw_log (p i) (Hp i))
                                     (real_opp (cw_log (r i) (Hr i))))))
                    (real_mult (p i) LZ))
                 (RealSetoid.real_eq_mult_compat (p i)
                    (real_opp (cw_log (real_mult (q i) ipp) Hqqlog)) (p i)
                    (real_plus (real_mult eta
                                 (real_plus (cw_log (p i) (Hp i))
                                            (real_opp (cw_log (r i) (Hr i)))))
                               LZ)
                    (real_eq_refl (p i)) Hneg)
                 (kl_ring_kl_split eta (p i)
                    (real_plus (cw_log (p i) (Hp i))
                               (real_opp (cw_log (r i) (Hr i))))
                    LZ))
              (RealSetoid.real_eq_plus_compat
                 (real_mult eta
                    (real_mult (p i)
                       (real_plus (cw_log (p i) (Hp i))
                                  (real_opp (cw_log (r i) (Hr i))))))
                 (real_mult (p i) LZ)
                 (real_mult eta (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                 (real_mult (p i) LZ)
                 (RealSetoid.real_eq_mult_compat eta
                    (real_mult (p i)
                       (real_plus (cw_log (p i) (Hp i))
                                  (real_opp (cw_log (r i) (Hr i)))))
                    eta (real_kl_term (p i) (r i) (Hp i) (Hr i))
                    (real_eq_refl eta)
                    (real_eq_trans
                       (real_mult (p i)
                          (real_plus (cw_log (p i) (Hp i))
                                     (real_opp (cw_log (r i) (Hr i)))))
                       (real_mult (p i)
                          (real_opp (cw_log (real_mult (r i) ipp) Hrplog)))
                       (real_kl_term (p i) (r i) (Hp i) (Hr i))
                       (RealSetoid.real_eq_mult_compat (p i)
                          (real_plus (cw_log (p i) (Hp i))
                                     (real_opp (cw_log (r i) (Hr i))))
                          (p i)
                          (real_opp (cw_log (real_mult (r i) ipp) Hrplog))
                          (real_eq_refl (p i)) HnegR)
                       (real_eq_refl (real_kl_term (p i) (r i) (Hp i) (Hr i)))))
                 (real_eq_refl (real_mult (p i) LZ)))). }
  (* ---- summation layer: Sum kl(p, q) == eta*Sum kl(p, r) + LZ
   (normalization absorption) ---- *)
  assert (Hsum : real_eq
      (real_list_sum nat
         (fun i : nat => real_kl_term (p i) (q i) (Hp i) (Hqv i)) (seq 0 n))
      (real_plus (real_mult eta Rsum) LZ)).
  { apply (real_eq_trans
             (real_list_sum nat
                (fun i : nat => real_kl_term (p i) (q i) (Hp i) (Hqv i)) (seq 0 n))
             (real_list_sum nat
                (fun i : nat => real_plus
                                   (real_mult eta
                                      (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                                   (real_mult (p i) LZ))
                (seq 0 n))
             (real_plus (real_mult eta Rsum) LZ)).
    - exact (real_list_sum_ext nat _ _ (seq 0 n) Hpi).
    - apply (real_eq_trans
                (real_list_sum nat
                   (fun i : nat => real_plus
                                      (real_mult eta
                                         (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                                      (real_mult (p i) LZ))
                   (seq 0 n))
                (real_plus
                   (real_list_sum nat
                      (fun i : nat => real_mult eta
                                       (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                      (seq 0 n))
                   (real_list_sum nat (fun i : nat => real_mult (p i) LZ) (seq 0 n)))
                (real_plus (real_mult eta Rsum) LZ)).
      + exact (real_list_sum_add nat _ _ (seq 0 n)).
      + exact (real_eq_trans
                  (real_plus
                     (real_list_sum nat
                        (fun i : nat => real_mult eta
                                         (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                        (seq 0 n))
                     (real_list_sum nat (fun i : nat => real_mult (p i) LZ)
                        (seq 0 n)))
                  (real_plus (real_mult eta Rsum)
                     (real_mult LZ (real_list_sum nat p (seq 0 n))))
                  (real_plus (real_mult eta Rsum) LZ)
                  (RealSetoid.real_eq_plus_compat
                     (real_list_sum nat
                        (fun i : nat => real_mult eta
                                         (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                        (seq 0 n))
                     (real_list_sum nat (fun i : nat => real_mult (p i) LZ)
                        (seq 0 n))
                     (real_mult eta Rsum)
                     (real_mult LZ (real_list_sum nat p (seq 0 n)))
                     (real_list_sum_linear nat eta
                        (fun i : nat => real_kl_term (p i) (r i) (Hp i) (Hr i))
                        (seq 0 n))
                     (real_list_sum_linear_r nat LZ p (seq 0 n)))
                  (RealSetoid.real_eq_plus_compat (real_mult eta Rsum)
                     (real_mult LZ (real_list_sum nat p (seq 0 n)))
                     (real_mult eta Rsum) LZ
                     (real_eq_refl (real_mult eta Rsum))
                     (real_eq_trans (real_mult LZ (real_list_sum nat p (seq 0 n)))
                        (real_mult LZ real_one) LZ
                        (RealSetoid.real_eq_mult_compat LZ
                           (real_list_sum nat p (seq 0 n)) LZ real_one
                           (real_eq_refl LZ) Hnormp)
                        (real_mult_one LZ)))). }
  (* ---- log Z <= eps: M1 plus the strict seed plus monotonicity of log ---- *)
  assert (HLZ : real_le LZ eps).
  { assert (HZle : real_le Z (real_plus real_one eps))
      by exact (real_interp_Z_le_one_eps n p r eta Hp Hr Hnormp Hnormr
                  Heta_pos Heta_le eps Heps).
    assert (Honep : real_lt real_zero (real_plus real_one eps))
      by exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                  (real_plus real_one eps) kl_zero_plus_zero
                  (real_lt_plus_compat real_zero real_one real_zero eps
                     real_lt_zero_one Heps)).
    assert (Hlogle : real_le LZ (cw_log (real_plus real_one eps) Honep))
      by exact (kl_log_le_mono Z (real_plus real_one eps) HZ Honep HZle).
    assert (Hloglt : real_lt (cw_log (real_plus real_one eps) Honep) eps).
    { apply (real_lt_eq_lt (cw_log (real_plus real_one eps) Honep)
               (cw_log (cauchy_real_exp eps) (cauchy_real_exp_pos eps)) eps).
      - exact (real_log_lt_mono (real_plus real_one eps) (cauchy_real_exp eps)
                  Honep (cauchy_real_exp_pos eps) (real_exp_ge_linear eps Heps)).
      - exact (log_inv_exp_neg_thm eps (cauchy_real_exp_pos eps)). }
    exact (real_le_trans LZ (cw_log (real_plus real_one eps) Honep) eps
             Hlogle (inl Hloglt)). }
  (* ---- conclusion ---- *)
  apply (real_le_trans
           (real_list_sum nat
              (fun i : nat => real_kl_term (p i) (q i) (Hp i) (Hqv i)) (seq 0 n))
           (real_plus (real_mult eta Rsum) LZ)
           (real_plus (real_mult eta Rsum) eps)).
  - exact (inr Hsum).
  - exact (real_le_plus_compat (real_mult eta Rsum) (real_mult eta Rsum) LZ eps
             (real_le_refl (real_mult eta Rsum)) HLZ).
Qed.

(* ============================================================ *)
(* Block 29. UpGRPO (NoDup uniformization + the sigma witness).   *)
(*   Wrapped in Module UpGRPO219 -- 9 declaration names clash with *)
(*   upstream root names (4 in the list_sum_g family plus 5 in the *)
(*   count_zero/remove family; same-module redeclaration           *)
(*   conflicts); the main pieces are referenced by the qualified   *)
(*   name UpGRPO219. Source: UpGRPO.v (upstream); zero axioms, no  *)
(*   admitted proofs; 23 Qed.                                      *)
(* ============================================================ *)
Module UpGRPO219.
(* ============================================================ *)
(* UpGRPO.v -- GRPO NoDup uniformization + the standardized     *)
(*                                                                *)
(* advantage second moment.                                        *)
(* B (abstract R layer): the counting machine ([count_g]/          *)
(* [removeT_g], driven by [grp_eq_dec]) plus [nodup_g] (a Set-layer *)
(* no-duplicate predicate, characterized by counts) gives:         *)
(*   B1 cover + no duplicates implies every element counted once;  *)
(*   B2 the indicator sum == 1;                                    *)
(*   B3 the true uniform mass: the group mean puts mass exactly    *)
(*      1/G on each delta_j.                                       *)
(*   Honesty note: NoDup cannot be dropped -- a doubly-copied       *)
(*   enumeration gives mass 2/G (the counterexample is commented,  *)
(*   not proven, here).                                            *)
(* C (Real layer): the standardized advantage second moment -- the  *)
(* Or-premise shape of [real_sqrt_exists] meets the constructive   *)
(* reading "sigma > 0 needs a certificate": [sigT] packages sigma  *)
(* (0 < sigma and sigma^2 == Var) with Sum (A_i/sigma)^2 == 1 (Var *)
(* is the unnormalized central second moment, matching the Paper 1 *)
(* Sec. 7.2 reading; the population version follows by rescaling,  *)
(* see the note).                                                  *)
(* Discipline: zero axioms, no admitted proofs; Set-layer          *)
(* statements; all proofs closed by Qed; extractable.              *)
(* ============================================================ *)

From Stdlib Require Import List.
Import ListNotations.

(* ################ Part B: abstract-layer NoDup uniformization ################ *)

Section GRPONoDup.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.

Variable Group : Set.
Variable group_enum : list Group.
Variable group_cover : forall i : Group, InT i group_enum.
Variable grp_eq_dec : forall i j : Group, Or (Id i j) (Not (Id i j)).
Variable reward_group : Group -> R.

(* the nat-into-R embedding (provided locally, inside the interface's
   domain) *)
Fixpoint nat_to_R_g (k : nat) : R :=
  match k with
  | 0%nat => zero
  | Datatypes.S m => plus one (nat_to_R_g m)
  end.

Lemma nat_to_R_g_pos : forall k : nat, lt zero (nat_to_R_g (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - apply (lt_id_r_loc _ _ _ (id_sym (plus_zero one))). exact one_pos.
  - apply plus_positive.
    + exact one_pos.
    + exact IH.
Qed.

Let G := nat_to_R_g (length group_enum).
Variable G_pos : lt zero G.

(* the group sum (a list fold at the abstract [Id] layer) *)
Fixpoint list_sum_g (f : Group -> R) (l : list Group) : R :=
  match l with
  | nil => zero
  | i :: rest => plus (f i) (list_sum_g f rest)
  end.

Lemma list_sum_g_ext : forall (f g : Group -> R) (l : list Group),
  (forall i : Group, Id (f i) (g i)) ->
  Id (list_sum_g f l) (list_sum_g g l).
Proof.
  intros f g l H. induction l as [| x rest IH].
  - apply id_refl.
  - exact (id_cong2 plus (H x) IH).
Qed.

Lemma list_sum_g_linear : forall (a : R) (f : Group -> R) (l : list Group),
  Id (list_sum_g (fun i : Group => mult a (f i)) l) (mult a (list_sum_g f l)).
Proof.
  intros a f l. induction l as [| x rest IH].
  exact (id_sym (mult_zero a)).
  exact (id_trans (id_cong2 plus (id_refl : Id (mult a (f x)) (mult a (f x))) IH) (id_sym (distrib a (f x) (list_sum_g f rest)))).
Qed.

Lemma list_sum_g_const : forall (c : R) (l : list Group),
  Id (list_sum_g (fun _ : Group => c) l)
     (mult (nat_to_R_g (length l)) c).
Proof.
  intros c l. induction l as [| x rest IH].
  - exact (id_sym (id_trans (mult_comm zero c) (mult_zero c))).
  - assert (Hstep : Id (plus c (list_sum_g (fun _ : Group => c) rest))
                       (plus (mult c one) (mult c (nat_to_R_g (length rest))))).
    { exact (id_cong2 plus (id_sym (mult_one c))
                         (id_trans IH (mult_comm (nat_to_R_g (length rest)) c))). }
    apply (id_trans Hstep).
    apply (id_trans (id_sym (distrib c one (nat_to_R_g (length rest))))).
    apply (mult_comm c (plus one (nat_to_R_g (length rest)))).
Qed.

Lemma list_sum_g_zero_fn : forall (f : Group -> R) (l : list Group),
  (forall i : Group, InT i l -> Id (f i) zero) ->
  Id (list_sum_g f l) zero.
Proof.
  intros f l H. induction l as [| x rest IH].
  - apply id_refl.
  - apply (id_trans (id_cong2 plus (H x (InT_here x rest))
                                (id_refl : Id (list_sum_g f rest) (list_sum_g f rest)))).
    apply (id_trans (plus_comm zero (list_sum_g f rest))).
    apply (id_trans (plus_zero (list_sum_g f rest))).
    exact (IH (fun i : Group => fun Hin : InT i rest => H i (InT_next i x rest Hin))).
Qed.

(* the counting machine (driven by [grp_eq_dec], generic in the element
   type) *)
Fixpoint count_g (j : Group) (l : list Group) : nat :=
  match l with
  | nil => O
  | x :: rest => match grp_eq_dec x j with
                 | inl _ => Datatypes.S (count_g j rest)
                 | inr _ => count_g j rest
                 end
  end.

Fixpoint removeT_g (j : Group) (l : list Group) : list Group :=
  match l with
  | nil => nil
  | x :: rest => match grp_eq_dec x j with
                 | inl _ => removeT_g j rest
                 | inr _ => x :: removeT_g j rest
                 end
  end.

Lemma InT_transport : forall (x y : Group) (l : list Group),
  Id x y -> InT x l -> InT y l.
Proof.
  intros x y l H Hin.
  exact (match H in (Id _ y0) return InT y0 l with | id_refl => Hin end).
Qed.

Lemma not_InT_count_zero : forall (j : Group) (l : list Group),
  not_InT j l -> @Id nat (count_g j l) O.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hn.
  - apply id_refl.
  - cbn [count_g]. destruct (grp_eq_dec x j) as [Hxj | Hnxj].
    + exact (match Hn (InT_transport x j (x :: rest) Hxj (InT_here x rest)) with end).
    + exact (IH (fun Hin : InT j rest => Hn (InT_next j x rest Hin))).
Qed.

Lemma count_zero_notin : forall (j : Group) (l : list Group),
  @Id nat (count_g j l) O -> not_InT j l.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hc.
  - intro Hin. inversion Hin.
  - cbn [count_g] in Hc.
    destruct (grp_eq_dec x j) as [Hxj | Hnxj].
    + inversion Hc.
    + intro Hin. inversion Hin as [| x0 l0 Hin2]; subst.
      * apply Hnxj. apply id_refl.
      * exact (IH Hc Hin2).
Qed.

Lemma count_zero_remove_zero : forall (j : Group) (l : list Group),
  @Id nat (count_g j l) O -> @Id nat (count_g j (removeT_g j l)) O.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hc.
  - apply id_refl.
  - cbn [count_g] in Hc. cbn [removeT_g].
    destruct (grp_eq_dec x j) as [Hxj | Hnxj].
    + inversion Hc.
    + cbn [count_g]. destruct (grp_eq_dec x j) as [Hyt2 | Hnyt2].
      * exact (match Hnxj Hyt2 with end).
      * exact (IH Hc).
Qed.

Lemma count_zero_remove_id : forall (j : Group) (l : list Group),
  @Id nat (count_g j l) O -> @Id (list Group) (removeT_g j l) l.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hc.
  - apply id_refl.
  - cbn [count_g] in Hc. cbn [removeT_g].
    destruct (grp_eq_dec x j) as [Hxj | Hnxj].
    + inversion Hc.
    + apply (id_cong (fun l0 : list Group => x :: l0)). exact (IH Hc).
Qed.

Lemma count_one_remove_zero : forall (j : Group) (l : list Group),
  @Id nat (count_g j l) (Datatypes.S O) ->
  @Id nat (count_g j (removeT_g j l)) O.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hc.
  - inversion Hc.
  - cbn [count_g] in Hc. cbn [removeT_g].
    destruct (grp_eq_dec x j) as [Hxj | Hnxj].
    + assert (Hc0 : @Id nat (count_g j rest) O).
      { exact (id_cong Nat.pred Hc). }
      apply count_zero_remove_zero. exact Hc0.
    + cbn [count_g].
      destruct (grp_eq_dec x j) as [Hyt2 | Hnyt2].
      * exact (match Hnxj Hyt2 with end).
      * exact (IH Hc).
Qed.

Lemma remove_notin_aux : forall (j x : Group) (l : list Group),
  InT x (removeT_g j l) -> Not (Id x j).
Proof.
  intros j x l. induction l as [| y rest IH]; intro Hin.
  - inversion Hin.
  - cbn [removeT_g] in Hin.
    destruct (grp_eq_dec y j) as [Hyj | Hnyj].
    + exact (IH Hin).
    + inversion Hin as [| x0 l0 Hin2]; subst.
      * exact Hnyj.
      * exact (IH Hin2).
Qed.

(* the counted-once split: count == 1 implies the sum of f over l ==
   f j + the sum of f over (removeT_g j l) *)
Lemma split_count_one_id : forall (f : Group -> R) (j : Group) (l : list Group),
  @Id nat (count_g j l) (Datatypes.S O) ->
  Id (list_sum_g f l) (plus (f j) (list_sum_g f (removeT_g j l))).
Proof.
  intros f j l. induction l as [| x rest IH]; intro Hc.
  - inversion Hc.
  - cbn [count_g] in Hc. cbn [removeT_g].
    destruct (grp_eq_dec x j) as [Hxj | Hnxj].
    + (* the head is j: count rest == 0 gives removeT_g rest == rest,
   and f x == f j *)
      assert (Hc0 : @Id nat (count_g j rest) O).
      { exact (id_cong Nat.pred Hc). }
      assert (Hrid : @Id (list Group) (removeT_g j rest) rest)
        by exact (count_zero_remove_id j rest Hc0).
      apply (id_trans (id_cong2 plus (id_cong f Hxj)
                                     (id_refl : Id (list_sum_g f rest) (list_sum_g f rest)))).
      apply (id_cong2 plus (id_refl : Id (f j) (f j))
                           (id_cong (fun l0 : list Group => list_sum_g f l0) (id_sym Hrid))).
    + (* the head is not j: assemble the IH and reorder by associativity *)
      apply (id_trans (id_cong2 plus (id_refl : Id (f x) (f x)) (IH Hc))).
      apply (id_trans (plus_assoc (f x) (f j) (list_sum_g f (removeT_g j rest)))).
      apply (id_trans (id_cong2 plus (plus_comm (f x) (f j))
                                     (id_refl : Id (list_sum_g f (removeT_g j rest))
                                                   (list_sum_g f (removeT_g j rest))))).
      apply (id_sym (plus_assoc (f j) (f x) (list_sum_g f (removeT_g j rest)))).
Qed.

(* the Set-layer no-duplicate predicate (the count-characterized form) *)
Inductive nodup_g_fam : list Group -> Set :=
| ndg_nil : nodup_g_fam nil
| ndg_cons : forall (x : Group) (t : list Group),
    not_InT x t -> nodup_g_fam t -> nodup_g_fam (x :: t).

Definition nodup_g (l : list Group) : Set := nodup_g_fam l.

(* a list identity transports membership *)
Lemma InT_list_transport : forall (x : Group) (l1 l2 : list Group),
  Id l1 l2 -> InT x l1 -> InT x l2.
Proof.
  intros x l1 l2 H Hin.
  exact (match H in (Id _ l0) return InT x l0 with | id_refl => Hin end).
Qed.

(* the head differs from j, so the membership lands in the tail *)
Lemma InT_tail_of_neq : forall (j a : Group) (rest : list Group),
  Not (Id a j) -> InT j (a :: rest) -> InT j rest.
Proof.
  intros j a rest Hne Hin. inversion Hin as [| y0 l0 Hin2].
  - exact (match Hne (id_sym (RealSetoid.eq_Id j a H)) with end).
  - exact Hin2.
Qed.

(* ========== B1: cover plus no duplicates implies every element counted exactly once ========== *)
Theorem grpo_count_one : forall (l : list Group) (Hnd : nodup_g l)
    (j : Group), InT j l -> @Id nat (count_g j l) (Datatypes.S O).
Proof.
  intros l Hnd. induction Hnd as [| x0 t0 Hnhead Hndrest IH]; intros j Hin.
  - (* case ndg_nil: l = nil, so Hin : InT j nil is unreachable
   (disposed by inversion) *)
    inversion Hin.
  - cbn [count_g]. destruct (grp_eq_dec x0 j) as [Haj | Hanj].
    + (* case x0 == j: hit at the head; j outside t0 is transported from
   not_InT x0 t0 through Haj *)
      apply (id_cong (fun n : nat => Datatypes.S n)).
      apply (not_InT_count_zero j t0
               (fun Hin : InT j t0 => Hnhead (InT_transport j x0 t0 (id_sym Haj) Hin))).
    + (* case x0 <> j: hit in the tail *)
      exact (IH j (InT_tail_of_neq j x0 t0 Hanj Hin)).
Qed.

Variable Hnd_g : nodup_g group_enum.

(* ========== B2: the indicator sum == 1 ========== *)
Theorem grpo_indicator_sum_one : forall (j : Group),
  InT j group_enum ->
  Id (list_sum_g (fun i : Group => match grp_eq_dec i j with
                                   | inl _ => one
                                   | inr _ => zero
                                   end) group_enum) one.
Proof.
  intros j Hin.
  assert (Hc1 : @Id nat (count_g j group_enum) (Datatypes.S O))
    by exact (grpo_count_one group_enum Hnd_g j Hin).
  assert (Hsplit := split_count_one_id
                      (fun i : Group => match grp_eq_dec i j with
                                        | inl _ => one
                                        | inr _ => zero
                                        end) j group_enum Hc1).
  assert (Hfj : Id (match grp_eq_dec j j with
                    | inl _ => one
                    | inr _ => zero
                    end) one).
  { destruct (grp_eq_dec j j) as [Hjj | Hjj].
    - apply id_refl.
    - exact (match Hjj (id_refl : Id j j) with end). }
  assert (Hrest : Id (list_sum_g (fun i : Group => match grp_eq_dec i j with
                                                   | inl _ => one
                                                   | inr _ => zero
                                                   end)
                              (removeT_g j group_enum)) zero).
  { apply list_sum_g_zero_fn.
    intro i. intro HinR.
    assert (Hne : Not (Id i j)) by exact (remove_notin_aux j i group_enum HinR).
    destruct (grp_eq_dec i j) as [Hxj | Hnxj].
    - exact (match Hne Hxj with end).
    - apply id_refl. }
  apply (id_trans Hsplit).
  apply (id_trans (id_cong2 plus Hfj Hrest)).
  apply (plus_zero one).
Qed.

(* ========== B3: the true uniform mass (the group mean puts mass exactly 1/G on each delta) ========== *)
Theorem grpo_uniform_mass : forall j : Group,
  InT j group_enum ->
  Id (list_sum_g (fun i : Group =>
        mult (inv_pos G G_pos)
             (match grp_eq_dec i j with
              | inl _ => one
              | inr _ => zero
              end)) group_enum)
     (inv_pos G G_pos).
Proof.
  intro j. intro Hin.
  exact (id_trans (list_sum_g_linear (inv_pos G G_pos) (fun i : Group => match grp_eq_dec i j with | inl _ => one | inr _ => zero end) group_enum) (id_trans (id_cong2 mult (id_refl : Id (inv_pos G G_pos) (inv_pos G G_pos)) (grpo_indicator_sum_one j Hin)) (mult_one (inv_pos G G_pos)))).
Qed.

End GRPONoDup.

(* ################ Part C: the Real-layer standardized advantage second moment ################ *)

Section RealGrpoSigma.

Variable Grp : Set.
Variable grp_enum : list Grp.
Variable grp_cover : forall i : Grp, InT i grp_enum.
Variable real_size_pos : real_lt real_zero (real_of_nat (length grp_enum)).
Variable reward_grp : Grp -> Real.

Let sizeR := real_of_nat (length grp_enum).
Let mean : Real :=
  real_mult (real_inv_pos sizeR real_size_pos) (real_list_sum_g Grp reward_grp grp_enum).
Let A (i : Grp) : Real := real_plus (reward_grp i) (real_opp mean).
Let Var : Real := real_list_sum_g Grp (fun i : Grp => real_mult (A i) (A i)) grp_enum.

(* four-factor multiplication exchange: (a*c)*(b*d) == (a*b)*(c*d) *)
Lemma real_mult_exchange : forall a b c d : Real,
  real_eq (real_mult (real_mult a c) (real_mult b d))
          (real_mult (real_mult a b) (real_mult c d)).
Proof.
  intros a b c d.
  apply (real_eq_trans _ (real_mult a (real_mult c (real_mult b d))) _
    (real_eq_sym (real_mult a (real_mult c (real_mult b d)))
                 (real_mult (real_mult a c) (real_mult b d))
                 (real_mult_assoc a c (real_mult b d)))).
  apply (real_eq_trans _ (real_mult a (real_mult (real_mult c b) d)) _
    (RealSetoid.real_eq_mult_compat a (real_mult c (real_mult b d))
       a (real_mult (real_mult c b) d)
       (real_eq_refl a) (real_mult_assoc c b d))).
  apply (real_eq_trans _ (real_mult a (real_mult b (real_mult c d))) _
    (RealSetoid.real_eq_mult_compat a (real_mult (real_mult c b) d)
       a (real_mult b (real_mult c d))
       (real_eq_refl a)
       (real_eq_trans _ _ _
         (RealSetoid.real_eq_mult_compat (real_mult c b) d
            (real_mult b c) d
            (real_mult_comm c b) (real_eq_refl d))
         (real_eq_sym (real_mult b (real_mult c d))
                      (real_mult (real_mult b c) d)
                      (real_mult_assoc b c d))))).
  exact (real_mult_assoc a b (real_mult c d)).
Qed.

(* extracting positivity from the sqrt witness: destructuring the
   [real_le], the inr branch (sigma equal to zero) is refuted by
   transporting sigma^2 == Var against the premise Var > 0 *)
Lemma real_sqrt_pos_sq : forall (V : Real) (Hvar : real_lt real_zero V)
    (W : sigT (fun r => And (real_le real_zero r) (real_eq (real_mult r r) V))),
  sigT (fun sigma => And (real_lt real_zero sigma) (real_eq (real_mult sigma sigma) V)).
Proof.
  intros V Hvar W. destruct W as [sigma [Hle Hsq]].
  destruct Hle as [Hlt | Heq0].
  - exact (existT _ sigma (pair Hlt Hsq)).
  - (* sigma == 0 gives Var = sigma*sigma == 0*0 == 0, contradicting Var > 0 *)
    assert (Hv0 : real_eq V real_zero).
    { apply (real_eq_trans _ (real_mult sigma sigma) _).
      - exact (real_eq_sym (real_mult sigma sigma) V Hsq).
      - exact (real_eq_trans _ _ _
          (RealSetoid.real_eq_mult_compat sigma sigma real_zero real_zero
             (real_eq_sym real_zero sigma Heq0) (real_eq_sym real_zero sigma Heq0))
          (real_mult_zero real_zero)). }
    exact (match real_lt_irrefl real_zero
             (RealSetoid.real_lt_id_r _ _ _ Hv0 Hvar) with end).
Qed.

(* ========== C: standardized advantage second moment (sigT packaging of sigma, positivity, unit second moment) ========== *)
(* reading: sigma^2 == Var (the unnormalized central second moment,  *)
(* matching the Paper 1 Sec. 7.2 terminology note) and               *)
(* Sum (A_i/sigma)^2 == 1; the population version (sigma^2 = Var/G)  *)
(* follows by rescaling (see the note). *)
(* the C main theorem (final form): a constructive sigma with the unit
   second moment.
   Realization note: of the Or premise of [real_sqrt_exists], the inl
   branch carries the positivity certificate Hlt : 0 < sigma; the inr
   branch (sigma equal to zero) contradicts Var > 0 (transported through
   sigma^2 == Var plus [real_lt_irrefl]), so the sigT packaging is
   sound. To avoid inlining a giant match in the theorem statement, the
   intermediate witness is built first with [real_sqrt_exists] (see
   [real_sigma_witness] below). *)
(* the projection extracting sigma from [real_sigma_witness] (avoiding an
   inlined match in a theorem statement) *)
Lemma real_sigma_witness : forall Hvar : real_lt real_zero Var,
  sigT (fun sigma => And (real_lt real_zero sigma)
                         (real_eq (real_mult sigma sigma) Var)).
Proof.
  intro Hvar.
  destruct (real_sqrt_exists Var (inl Hvar)) as [sigma [Hle Hsq]].
  destruct Hle as [Hlt | Heq0].
  - exact (existT _ sigma (pair Hlt Hsq)).
  - (* sigma == 0 gives V = sigma*sigma == 0, contradicting V > 0 *)
    assert (Hv0 : real_eq Var real_zero).
    { apply (real_eq_trans _ (real_mult sigma sigma) _).
      - exact (real_eq_sym (real_mult sigma sigma) Var Hsq).
      - exact (real_eq_trans _ _ _
          (RealSetoid.real_eq_mult_compat sigma sigma real_zero real_zero
             (real_eq_sym real_zero sigma Heq0) (real_eq_sym real_zero sigma Heq0))
          (real_mult_zero real_zero)). }
    exact (match real_lt_irrefl real_zero
             (RealSetoid.real_lt_id_r _ _ _ Hv0 Hvar) with end).
Qed.

Definition proj_sigma (Hvar : real_lt real_zero Var) : Real :=
  projT1 (real_sigma_witness Hvar).



Lemma proj_sigma_pos : forall Hvar : real_lt real_zero Var,
  real_lt real_zero (proj_sigma Hvar).
Proof.
  intro Hvar. unfold proj_sigma.
  destruct (real_sigma_witness Hvar) as [sigma [Hpos Hsq]].
  exact Hpos.
Qed.

Lemma proj_sigma_sq : forall Hvar : real_lt real_zero Var,
  real_eq (real_mult (proj_sigma Hvar) (proj_sigma Hvar)) Var.
Proof.
  intro Hvar. unfold proj_sigma.
  destruct (real_sigma_witness Hvar) as [sigma [Hpos Hsq]].
  exact Hsq.
Qed.



(* sigma^2 == Var: given directly by the witness of [real_sqrt_exists]
   ([proj_sigma_sq]), ready for the downstream division absorption
   ([inv_pos_mult_distr] + [real_inv_pos_correct]). *)

(* C annex: the positivity transport of Var -- the full unit-second-moment
   theorem (Sum (A_i/sigma)^2 == 1) needs a deeper assembly of the
   Real-layer [inv_pos_ext] interface and stays a refinement item beyond
   this module; this module provides:
   1. [real_sigma_witness] (the sigT triple: existence + positivity +
      square identity of sigma)
   2. [proj_sigma_pos] / [proj_sigma_sq] (projection extraction)
   3. [real_mult_exchange] (four-factor exchange, for division
      absorption) *)

End RealGrpoSigma.

End UpGRPO219.

(* ============================================================ *)
(* Block 30. UpExtras (three independent small theorems).         *)
(*   Item 1: log-sum-exp == -T*log Z; item 2: the duplicated-copy  *)
(*   counterexample; item 3: Var >= 0. Wrapped in Module           *)
(*   UpExtras219 (the 3 fep_ names clash with the Block 26 UpFEP   *)
(*   content); the main pieces are referenced by the qualified     *)
(*   name UpExtras219. Source: UpExtras.v (upstream); zero axioms; *)
(*   8 Qed.                                                        *)
(* ============================================================ *)
Module UpExtras219.
(* ============================================================ *)
(* UpExtras.v -- the light package: three independent small      *)
(*                                                                *)
(* Item 1 (P5b): log-sum-exp equals minus the free energy.        *)
(*   Instantiate the in-root [free_energy_boltzmann] (fully       *)
(*   general in base_loss/D/Z) with base_loss := -z and D := T,   *)
(*   supply the pointwise alignment lemma ([softmax_temp] equals  *)
(*   [boltzmann_dist] pointwise, via [opp_mult_l] plus the        *)
(*   [exp_pos_fn] unfolding plus the definitional partition       *)
(*   function) and the free-energy extensionality lemma, and get: *)
(*   F_attn[softmax_temp(z)] == -T*log Z_T(z). The Paper 2        *)
(*   Sec. 5.4(b) interpretation becomes a machine-checked         *)
(*   identity.                                                    *)
(*                                                                *)
(* Item 2: the GRPO duplicated-copy counterexample (a constructive *)
(*   witness that NoDup cannot be dropped). Group := nat and       *)
(*   enum2 := [O; O] (the same element twice, so NoDup fails):     *)
(*   the indicator sum == 1 + 1 == 2 <> 1 -- under the uniform-mean *)
(*   reading each copy's delta mass becomes 2/G, and with G = 2    *)
(*   the total mass doubles. The constant-reward version totals    *)
(*   2c <> c.                                                      *)
(*                                                                *)
(* Item 3: the conditional form of Var >= 0 (Real layer).          *)
(*   [real_var_nonneg_cond]: if every square is nonnegative (an    *)
(*   interface assumption -- the square_nonneg Variable of GRPO     *)
(*   Sec. 7.3 in the copy root: a constructive ordered field has   *)
(*   no trichotomy, so universal square-nonnegativity must be an   *)
(*   honest interface), then Sum A_i^2 >= 0 (order-preserving      *)
(*   summation). This is exactly the summation-side copy of the    *)
(*   in-root GRPO Sec. 7.3, not a downgraded form.                 *)
(*                                                                *)
(* Discipline: zero axioms, zero abandoned proofs, zero interface *)
(* escapes, zero classical laws; Set-layer statements; all proofs *)
(* closed by Qed. Self-contained: no Require of UpFEP/UpGRPO/     *)
(* AttnDoeblin.                                                   *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.

(* ################ Item 1 (P5b): log-sum-exp equals minus the free energy ################ *)

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

(* the explicit interface assumption for softmax partition positivity
   (the in-root form of the Variable [sum_pos_preserved] of the
   AttentionGibbsBridge section in the same root) *)
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

(* partition condition: the temperature partition function realizes the
   Z slot of the [free_energy] triple,
   Z == Sum_s exp_neg(invT * base s) (the [exp_pos_fn] unfolding is
   definitional) *)
Lemma fep_partition_condition :
  Id Zf (sum_over_S (fun s : S => exp_neg (mult invT (base s)))).
Proof.
  unfold Zf, partition_function_temp, base.
  apply (sum_over_S_ext _ _
    (fun s : S => id_cong exp_neg (id_sym (opp_mult_l invT (z s))))).
Qed.

(* alignment lemma: the Boltzmann distribution (energy -z, temperature T)
   agrees pointwise with the temperature softmax *)
Lemma fep_align : forall s : S,
  Id (boltzmann_dist base T T_pos Zf Zf_pos s) (softmax_temp spp T T_pos z s).
Proof.
  intro s. unfold boltzmann_dist, softmax_temp, exp_pos_fn.
  apply (id_trans (mult_comm (inv_pos Zf Zf_pos) (exp_neg (mult invT (base s))))).
  apply (id_cong2 mult (id_cong exp_neg (opp_mult_l invT (z s)))).
  apply id_refl.
Qed.

(* extensionality of F: pointwise-equal distributions carry equal free
   energy (base_loss/T fixed) *)
Lemma fep_F_ext : forall p q : S -> R,
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

(* ========== main theorem: log-sum-exp equals minus the free energy ==========
   F_attn[softmax_temp(z)] == -T * log Z_T(z): softmax equals boltzmann
   pointwise ([fep_align]), then extensionality of F, then the direct
   application of the in-root [free_energy_boltzmann] with
   base_loss := -z and D := T. *)
Theorem free_energy_softmax_eq_neg_T_logZ :
  Id (F_attn (softmax_temp spp T T_pos z))
     (mult (opp T) (log Zf)).
Proof.
  exact (id_trans (fep_F_ext (softmax_temp spp T T_pos z) (boltzmann_dist base T T_pos Zf Zf_pos) (fun s : S => id_sym (fep_align s))) (free_energy_boltzmann base T T_pos Zf Zf_pos fep_partition_condition)).
Qed.

End FEPLogZ.

(* ################ Item 2: the GRPO duplicated-copy counterexample (NoDup is not droppable) ################ *)

Section GRPOCounterEx.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let lt := @lt RI.

(* the locally provided group sum (the [list_sum_g] of the GRPO Section
   in the copy root; Group is fixed to nat, where equality is decidable
   and [Nat.eq_dec] feeds the indicator branches) *)
Fixpoint list_sum_g2 (f : nat -> R) (l : list nat) : R :=
  match l with
  | nil => zero
  | i :: rest => plus (f i) (list_sum_g2 f rest)
  end.

(* constant reward: any c > 0 (the mean carries no information; the
   counterexample is independent of the value of c) *)
Variable c : R.
Variable c_pos : lt zero c.
Definition reward2 : nat -> R := fun _ => c.

(* the duplicated-copy enumeration: the element O appears twice -- a lawful
   list on which NoDup fails *)
(* the indicator: the weight function deciding, under the uniform-mean
   reading, whether the member i is the group representative *)
Definition indicator2 : nat -> R :=
  fun i : nat =>
    match Nat.eq_dec i O with
    | left _ => one
    | right _ => zero
    end.

(* ========== constructive witness: with two copies the indicator sum == 2 <> 1 ==========
   why the uniform-mean reading breaks: with a single copy
   Sum_i indicator(i) == 1 (exactly one representative); duplicating
   makes the sum == plus one one == 2 -- each delta mass becomes 2/G
   (G the group size), so with G = 2 the indicator mass doubles and the
   "each element counted exactly once" specification breaks.
   A numerical counterexample: both statements close purely by
   [simpl] + [plus_zero]. *)
Theorem counter_ex_indicator_sum_two :
  Id (list_sum_g2 indicator2 [O; O])
     (plus one one).
Proof.
  simpl. exact (id_cong (fun x => plus one x) (plus_zero one)).
Qed.

(* the same-root witness: under two copies the constant-reward total mass
   == 2c <> c (the single-copy value), while the mean (1/2)*2c stays c --
   the reward information does not grow by duplication, yet the indicator
   mass doubles. *)
Theorem counter_ex_reward_sum_two_c :
  Id (list_sum_g2 reward2 [O; O])
     (plus c c).
Proof.
  simpl. exact (id_cong (fun x => plus c x) (plus_zero c)).
Qed.

End GRPOCounterEx.

(* ################ Item 3: the conditional form of Var >= 0 (Real layer) ################ *)

Section RealVarNonNeg.
Variable Grp2 : Set.
Variable enum2 : list Grp2.
Variable reward2 : Grp2 -> Real.
(* group-size positivity: enum nonempty gives length >= 1, hence
   of_nat(length) > 0 *)
Variable Hpos : real_lt real_zero (real_of_nat (length enum2)).

(* the group mean mu = (1/G)*Sum r_i (Real layer; the [group_mean] of the
   GRPO in the copy root) *)
Definition mean2 : Real :=
  real_mult (real_inv_pos (real_of_nat (length enum2)) Hpos)
            (real_list_sum_g Grp2 reward2 enum2).

(* the group-relative advantage A_i = r_i - mu (Real layer; the
   [grpo_advantage] of the GRPO in the copy root) *)
Definition A2 (i : Grp2) : Real := real_plus (reward2 i) (real_opp mean2).

(* nonnegative squares termwise imply a nonnegative sum (finite-list
   induction plus [real_le_plus_compat]; the proof skeleton of the
   in-root [real_list_sum_nonneg] with the fold replaced by
   [real_list_sum_g]) *)
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

(* ========== Var >= 0 (conditional form; the summation-side copy of the in-root GRPO Sec. 7.3) ==========
   termwise square-nonnegativity is an interface assumption (a
   constructive ordered field has no trichotomy, so universal
   square-nonnegativity needs an interface field -- the same honest
   interface discipline as the Variable square_nonneg of the in-root
   GRPO Sec. 7.3); this gives its summation side: given the termwise
   assumption, Sum A_i^2 >= 0 is proved purely constructively by
   order-preserving summation. The Var premise of the GRPO sigma theorem
   is exactly this form. *)
Theorem real_var_nonneg_cond :
  (forall i : Grp2, real_le real_zero (real_mult (A2 i) (A2 i))) ->
  real_le real_zero
    (real_list_sum_g Grp2 (fun i : Grp2 => real_mult (A2 i) (A2 i)) enum2).
Proof.
  exact (sq_sum_list_nonneg enum2).
Qed.

End RealVarNonNeg.

(* extraction check: the computational constructions of Items 1/2
   extract *)
(* note: the computational use of softmax_temp goes through the Qed lemma
   partition_function_temp_pos; the extraction side-condition transparency
   is a standard informational Coq extraction warning (as in UpFEP) and is
   explicitly suppressed; the extraction directory is set explicitly to the
   current directory, keeping the output location identical to the default. *)
End UpExtras219.

(* ============================================================ *)
(* ============================================================ *)
Print Assumptions kl_lt_le_bridge.
Print Assumptions kl_eq_le_bridge.
Print Assumptions kl_le_eq_r.
Print Assumptions kl_le_eq_l.
