(* ConstructiveWorld-Set -- Real-layer definition file for the FEP temperature family. *)
(** * UpReqTempDefs: temperature-family definitions and laws.

    Mission.  The Real-layer FEP temperature family: Boltzmann factor
      [real_boltzmann_factor_temp], partition function [real_Z_temp],
      Boltzmann distribution [real_boltzmann_dist_temp], energy
      expectation [real_energy_exp_temp], distribution entropy
      [real_entropy_dist], their positivity/normalization laws, the
      entropy identity [real_entropy_temp_explicit], and the
      sum-interface certificates.

    Dependencies.  [S01_BaseRing]..[S15_TailFEPUp], [UpReqConcSoftmax],
      [ConcMixSelFeed]; Stdlib [List].

    References.  The Id-layer originals ([partition_function_temp],
      [Z_temp_spec], [boltzmann_dist_temp], [energy_exp_temp],
      [entropy_dist], [Z_temp_pos], [boltzmann_dist_temp_normalized];
      line positions in the section comments below); [UpReqRealFEP]
      ([rfep_boltzmann_normalized_real]); [G02_Debt]
      ([RealScaleDual]/[RealAttnGibbsTemp]); mathlib's
      measure-theoretic Boltzmann distribution; Stdlib [Coq.Reals]; the
      same-name ConstructiveWorld-Main baseline.

    Constructivity.  Purely constructive: no admission statements, no
      classical real axioms; Set-layer carriers, zero Prop leakage;
      the [T_pos] premise mirrors the Id layer's [Variable] form; all [Qed].

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      UpReqTempDefs.v] compiles cleanly (exit 0); the first eight bytes
      of the artifact are [436f7121 00015ff4]. *)

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

(* ================= Instance-layer supply segment (assumption discharge: certificate positions become proved theorems, signature-preserving) ================= *)
(*   Statement face = the original assumed propositions with the carrier swapped to the supplied instance [csm_sumf S0 en]; *)
(*   proofs = the supply theorems of [ConcMixSelFeed] ([cms_sum_*]) applied with all arguments explicit. *)
From Stdlib Require Import List.
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.

(* Sum extensionality: pointwise [real_eq] gives [real_eq] of the sums (the original assumed proposition, instantiated at [csm_sumf]). *)
Theorem w3p_tempdef_sum_ext_sup :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    (forall s : S0, real_eq (f s) (g s)) ->
    real_eq (csm_sumf S0 en f) (csm_sumf S0 en g).
Proof.
  intros S0 en f g H.
  exact (cms_sum_ext S0 en f g H).
Qed.

(* Sum linearity: constant factors pull out (the original assumed proposition, instantiated at [csm_sumf]). *)
Theorem w3p_tempdef_sum_linear_sup :
  forall (S0 : Set) (en : list S0) (a : Real) (f : S0 -> Real),
    real_eq (csm_sumf S0 en (fun s : S0 => real_mult a (f s)))
            (real_mult a (csm_sumf S0 en f)).
Proof.
  intros S0 en a f.
  exact (cms_sum_linear S0 en a f).
Qed.

(* Sum additivity: splitting the sum of a two-term summand (the original assumed proposition, instantiated at [csm_sumf]). *)
Theorem w3p_tempdef_sum_add_sup :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    real_eq (csm_sumf S0 en (fun s : S0 => real_plus (f s) (g s)))
            (real_plus (csm_sumf S0 en f) (csm_sumf S0 en g)).
Proof.
  intros S0 en f g.
  exact (cms_sum_add S0 en f g).
Qed.

(* ================= Section RealTempDefs: Real-layer definitions of the temperature family (abstract [sumf] carrier) ================= *)
Section RealTempDefs.

(* Abstract state space and sum interface (same shape as the [G02_Debt] [RealAttnGibbsTemp] precedent) *)
Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s => real_mult a (f s))) (real_mult a (real_sum_over_S f)).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).

(* Temperature (premise position mirroring the Id layer's [Variable] form, S06 L3338) and energy *)
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable energy : S -> Real.

(* ---------------------------------------------------------- *)
(* Definition 0 (numerator helper): the Boltzmann factor      *)
(*   [bf(s) := e^{-e(s)/T}]                                   *)
(*   Counterpart: the Id-layer inner [exp_neg (mult (inv_pos t Ht) E_s)], S04 L3421. *)
(* ---------------------------------------------------------- *)
Definition real_boltzmann_factor_temp (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos T T_pos) (energy s)).

(* Positivity of the Boltzmann factor ([exp] is always positive; counterpart: the Id-layer [exp_neg_pos] argument position) *)
Lemma real_boltzmann_factor_temp_pos :
  forall s : S, real_lt real_zero (real_boltzmann_factor_temp s).
Proof.
  intro s.
  unfold real_boltzmann_factor_temp.
  apply real_exp_neg_pos.
Qed.

(* ---------------------------------------------------------- *)
(* Definition 1: the temperature-scaled partition function          *)
(*   [Z_T := Sum_s e^{-e(s)/T}]                                     *)
(*   Counterpart: the Id-layer [partition_function_temp] (the S06 L3339 [Variable] form) *)
(*   / the S04 [Z_temp_spec] expansion; the sum itself is the partition, *)
(*   so the spec identity reduces to definitional equality.          *)
(* ---------------------------------------------------------- *)
Definition real_Z_temp : Real :=
  real_sum_over_S real_boltzmann_factor_temp.

(* Basic lemma 1 (positivity): [Z_T > 0] ([exp] positivity times sum positivity; counterpart: *)
(* the Id-layer [Z_temp_pos], S04 L3416). *)
Theorem real_Z_temp_pos : real_lt real_zero real_Z_temp.
Proof.
  unfold real_Z_temp.
  apply real_sum_pos_preserved.
  intro s.
  apply real_boltzmann_factor_temp_pos.
Qed.

(* ---------------------------------------------------------- *)
(* Definition 2: the temperature-scaled Boltzmann distribution ([inv_pos] normalization, *)
(* i.e. the temperature-scaled softmax) *)
(*   [p_T(s) := inv(Z_T) * e^{-e(s)/T}]                             *)
(*   Counterpart: the Id-layer [boltzmann_dist_temp] (S04 L3421), with the factor order *)
(*   preserved field by field ([inv] first, [exp] second).           *)
(* ---------------------------------------------------------- *)
Definition real_boltzmann_dist_temp (s : S) : Real :=
  real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
            (real_boltzmann_factor_temp s).

(* Pointwise positivity of the distribution ([inv] positive times factor positive; counterpart: the Id-layer [boltzmann_dist_temp_pos]) *)
Lemma real_boltzmann_dist_temp_pos :
  forall s : S, real_lt real_zero (real_boltzmann_dist_temp s).
Proof.
  intro s.
  unfold real_boltzmann_dist_temp.
  apply (real_mult_pos_compat
           (real_inv_pos real_Z_temp real_Z_temp_pos)
           (real_boltzmann_factor_temp s)).
  - apply real_inv_pos_pos.
  - apply real_boltzmann_factor_temp_pos.
Qed.

(* Basic lemma 2 (normalization): [Sum_s p_T(s) == 1]               *)
(*   Counterpart: the Id-layer [boltzmann_dist_temp_normalized] (S04 L3433); a two-step chain: *)
(*   per-[s] factor swap ([sum_ext]) -> linear extraction ([sum_linear]) -> *)
(*   [inv(Z_T) * Z_T == 1] ([inv_pos_correct]).  The established recipe takes exactly these two steps, *)
(*   the same shape as [rfep_boltzmann_normalized_real] ([UpReqRealFEP] Part 3). *)
Theorem real_boltzmann_dist_temp_normalized :
  real_eq (real_sum_over_S real_boltzmann_dist_temp) real_one.
Proof.
  apply (real_eq_trans
           (real_sum_over_S real_boltzmann_dist_temp)
           (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)
           real_one).
  - (* Step 1: [Sum p_T == inv(Z_T) * Z_T] (swap + linearity + definitional convergence to the partition) *)
    apply (real_eq_trans
             (real_sum_over_S real_boltzmann_dist_temp)
             (real_sum_over_S
                (fun s : S => real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                                        (real_boltzmann_factor_temp s)))
             (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)).
    + apply (real_sum_over_S_ext real_boltzmann_dist_temp
               (fun s : S => real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                                       (real_boltzmann_factor_temp s))).
      intro s. apply real_eq_refl.
    + apply (real_eq_trans
               (real_sum_over_S
                  (fun s : S => real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                                          (real_boltzmann_factor_temp s)))
               (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                          (real_sum_over_S real_boltzmann_factor_temp))
               (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)).
      * apply real_sum_over_S_linear.
      * apply (RealSetoid.real_eq_mult_compat_adapt
                 (real_inv_pos real_Z_temp real_Z_temp_pos)
                 (real_inv_pos real_Z_temp real_Z_temp_pos)
                 (real_sum_over_S real_boltzmann_factor_temp)
                 real_Z_temp
                 (real_eq_refl (real_inv_pos real_Z_temp real_Z_temp_pos))
                 (real_eq_refl real_Z_temp)).
  - (* Step 2: [inv(Z_T) * Z_T == 1] (swap + [inv_pos_correct]) *)
    apply (real_eq_trans
             (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)
             (real_mult real_Z_temp (real_inv_pos real_Z_temp real_Z_temp_pos))
             real_one).
    + apply real_mult_comm.
    + apply real_inv_pos_correct.
Qed.

(* ---------------------------------------------------------- *)
(* Definition 3: the temperature-scaled energy expectation          *)
(*   [E_T := Sum_s p_T(s) * e(s)]                                   *)
(*   Counterpart: the Id-layer [energy_exp_temp] (S04 L3424), field by field. *)
(* ---------------------------------------------------------- *)
Definition real_energy_exp_temp : Real :=
  real_sum_over_S (fun s : S => real_mult (real_boltzmann_dist_temp s) (energy s)).

(* ---------------------------------------------------------- *)
(* Definition 4: the distribution entropy (information entropy, distribution version) *)

(*   Counterpart: the Id-layer [entropy_dist] (S04 L3150), field by field; the one premise-position *)
(*   difference: the Id [log] is total while the Real [real_log] carries a positivity witness *)
(*   (the req-layer precedent [reqd_entropy_dist] holds the same position). *)
(* ---------------------------------------------------------- *)
Definition real_entropy_dist
  (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)) : Real :=
  real_sum_over_S (fun s : S => real_mult (p s) (real_opp (real_log (p s) (Hp s)))).

(* ============================================================ *)
(* Added piece: [real_entropy_temp_explicit] (a Real-layer isomorphic copy *)
(*   of the Id-layer [entropy_temp_explicit] at L17271; the req-layer *)
(*   precedent [req_entropy_temp_explicit], statement 1/5 of [UpReqTempEntropy], *)
(*   sits at the same statement caliber): *)



(*   -> [sum_add] splits the sum -> [beta] linear extraction + [logZ] constant extraction (normalization completes). *)
(* ============================================================ *)


(* ...the [real_log_wd] + [real_inv_pos_correct] + [real_log_one] + [real_plus] group. *)
Lemma real_log_inv_Z_aux :
  real_eq (real_log (real_inv_pos real_Z_temp real_Z_temp_pos)
                    (real_inv_pos_pos real_Z_temp real_Z_temp_pos))
          (real_opp (real_log real_Z_temp real_Z_temp_pos)).
Proof.
  set (X := real_log (real_inv_pos real_Z_temp real_Z_temp_pos)
                     (real_inv_pos_pos real_Z_temp real_Z_temp_pos)).
  set (LZ := real_log real_Z_temp real_Z_temp_pos).
  assert (Hsum : real_eq (real_plus X LZ) real_zero).
  { apply (real_eq_trans (real_plus X LZ)
             (real_log (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)
                       (real_mult_positive (real_inv_pos real_Z_temp real_Z_temp_pos)
                          real_Z_temp (real_inv_pos_pos real_Z_temp real_Z_temp_pos)
                          real_Z_temp_pos))
             real_zero).
    - apply real_eq_sym.
      exact (real_log_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp
              (real_inv_pos_pos real_Z_temp real_Z_temp_pos) real_Z_temp_pos).
    - apply (real_eq_trans
               (real_log (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)
                         (real_mult_positive (real_inv_pos real_Z_temp real_Z_temp_pos)
                            real_Z_temp (real_inv_pos_pos real_Z_temp real_Z_temp_pos)
                            real_Z_temp_pos))
               (real_log real_one real_lt_zero_one)
               real_zero).
      + apply (real_log_wd
                 (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)
                 real_one
                 (real_mult_positive (real_inv_pos real_Z_temp real_Z_temp_pos)
                    real_Z_temp (real_inv_pos_pos real_Z_temp real_Z_temp_pos)
                    real_Z_temp_pos)
                 real_lt_zero_one).
        apply (real_eq_trans
                 (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)
                 (real_mult real_Z_temp (real_inv_pos real_Z_temp real_Z_temp_pos))
                 real_one).
        * exact (real_mult_comm (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp).
        * exact (real_inv_pos_correct real_Z_temp real_Z_temp_pos).
      + exact (real_log_one real_lt_zero_one). }
  apply (real_eq_trans X (real_plus X real_zero) (real_opp LZ)).
  - apply real_eq_sym. exact (real_plus_zero X).
  - apply (real_eq_trans
             (real_plus X real_zero)
             (real_plus X (real_plus LZ (real_opp LZ)))
             (real_opp LZ)).
    + apply (RealSetoid.real_eq_plus_compat_adapt X X real_zero
               (real_plus LZ (real_opp LZ)) (real_eq_refl X)).
      apply real_eq_sym. exact (real_plus_opp LZ).
    + apply (real_eq_trans
             (real_plus X (real_plus LZ (real_opp LZ)))
             (real_plus (real_plus X LZ) (real_opp LZ))
             (real_opp LZ)).
      * exact (real_plus_assoc X LZ (real_opp LZ)).
      * apply (real_eq_trans
                 (real_plus (real_plus X LZ) (real_opp LZ))
                 (real_plus real_zero (real_opp LZ))
                 (real_opp LZ)).
        -- apply (RealSetoid.real_eq_plus_compat_adapt
                    (real_plus X LZ) real_zero (real_opp LZ) (real_opp LZ)
                    Hsum (real_eq_refl (real_opp LZ))).
        -- apply (real_eq_trans
                    (real_plus real_zero (real_opp LZ))
                    (real_plus (real_opp LZ) real_zero)
                    (real_opp LZ)).
           ++ exact (real_plus_comm real_zero (real_opp LZ)).
           ++ exact (real_plus_zero (real_opp LZ)).
Qed.


Lemma real_neg_log_boltzmann_point :
  forall s : S,
    real_eq (real_opp (real_log (real_boltzmann_dist_temp s)
                                (real_boltzmann_dist_temp_pos s)))
            (real_plus (real_mult (real_inv_pos T T_pos) (energy s))
                       (real_log real_Z_temp real_Z_temp_pos)).
Proof.
  intro s.
  set (bta := real_inv_pos T T_pos).
  set (Hi := real_inv_pos_pos real_Z_temp real_Z_temp_pos).
  set (LZ := real_log real_Z_temp real_Z_temp_pos).
  apply (real_eq_trans
           (real_opp (real_log (real_boltzmann_dist_temp s)
                               (real_boltzmann_dist_temp_pos s)))
           (real_opp (real_opp (real_plus LZ (real_mult bta (energy s)))))
           (real_plus (real_mult bta (energy s)) LZ)).
  - apply (RealSetoid.real_eq_opp_compat
             (real_log (real_boltzmann_dist_temp s) (real_boltzmann_dist_temp_pos s))
             (real_opp (real_plus LZ (real_mult bta (energy s))))).
    apply (real_eq_trans
             (real_log (real_boltzmann_dist_temp s) (real_boltzmann_dist_temp_pos s))
             (real_plus (real_log (real_inv_pos real_Z_temp real_Z_temp_pos) Hi)
                        (real_log (real_exp_neg (real_mult bta (energy s)))
                                  (real_exp_neg_pos (real_mult bta (energy s)))))
             (real_opp (real_plus LZ (real_mult bta (energy s))))).
    + apply (real_eq_trans
               (real_log (real_boltzmann_dist_temp s) (real_boltzmann_dist_temp_pos s))
               (real_log (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                                    (real_exp_neg (real_mult bta (energy s))))
                         (real_mult_positive (real_inv_pos real_Z_temp real_Z_temp_pos)
                            (real_exp_neg (real_mult bta (energy s))) Hi
                            (real_exp_neg_pos (real_mult bta (energy s)))))
               (real_plus (real_log (real_inv_pos real_Z_temp real_Z_temp_pos) Hi)
                          (real_log (real_exp_neg (real_mult bta (energy s)))
                                    (real_exp_neg_pos (real_mult bta (energy s)))))).
      * exact (real_log_wd
                 (real_boltzmann_dist_temp s)
                 (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                            (real_exp_neg (real_mult bta (energy s))))
                 (real_boltzmann_dist_temp_pos s)
                 (real_mult_positive (real_inv_pos real_Z_temp real_Z_temp_pos)
                    (real_exp_neg (real_mult bta (energy s))) Hi
                    (real_exp_neg_pos (real_mult bta (energy s))))
                 (real_eq_refl (real_boltzmann_dist_temp s))).
      * exact (real_log_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                 (real_exp_neg (real_mult bta (energy s))) Hi
                 (real_exp_neg_pos (real_mult bta (energy s)))).
    + apply (real_eq_trans
               (real_plus (real_log (real_inv_pos real_Z_temp real_Z_temp_pos) Hi)
                          (real_log (real_exp_neg (real_mult bta (energy s)))
                                    (real_exp_neg_pos (real_mult bta (energy s)))))
               (real_plus (real_opp LZ) (real_opp (real_mult bta (energy s))))
               (real_opp (real_plus LZ (real_mult bta (energy s))))).
      * apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_log (real_inv_pos real_Z_temp real_Z_temp_pos) Hi)
                 (real_opp LZ)
                 (real_log (real_exp_neg (real_mult bta (energy s)))
                           (real_exp_neg_pos (real_mult bta (energy s))))
                 (real_opp (real_mult bta (energy s)))
                 real_log_inv_Z_aux
                 (real_log_exp_neg (real_mult bta (energy s)))).
      * apply real_eq_sym.
        exact (real_opp_plus LZ (real_mult bta (energy s))).
  - apply (real_eq_trans
             (real_opp (real_opp (real_plus LZ (real_mult bta (energy s)))))
             (real_plus LZ (real_mult bta (energy s)))
             (real_plus (real_mult bta (energy s)) LZ)).
    + exact (real_opp_opp (real_plus LZ (real_mult bta (energy s)))).
    + apply real_plus_comm.
Qed.


Theorem real_entropy_temp_explicit :
  real_eq (real_entropy_dist real_boltzmann_dist_temp real_boltzmann_dist_temp_pos)
          (real_plus (real_mult (real_inv_pos T T_pos) real_energy_exp_temp)
                     (real_log real_Z_temp real_Z_temp_pos)).
Proof.
  unfold real_entropy_dist.
  set (bta := real_inv_pos T T_pos).
  set (p := real_boltzmann_dist_temp).
  set (Hp := real_boltzmann_dist_temp_pos).
  set (LZ := real_log real_Z_temp real_Z_temp_pos).
  apply (real_eq_trans
           (real_sum_over_S (fun s : S => real_mult (p s) (real_opp (real_log (p s) (Hp s)))))
           (real_sum_over_S (fun s : S => real_mult (p s)
                              (real_plus (real_mult bta (energy s)) LZ)))
           (real_plus (real_mult bta real_energy_exp_temp) LZ)).
  - (* Step 1: pointwise reshaping (the point lemma applied explicitly) *)
    apply real_sum_over_S_ext.
    intro s.
    apply (RealSetoid.real_eq_mult_compat_adapt (p s) (p s)
             (real_opp (real_log (p s) (Hp s)))
             (real_plus (real_mult bta (energy s)) LZ)
             (real_eq_refl (p s))
             (real_neg_log_boltzmann_point s)).
  - (* Steps 2-4: pointwise distributivity splits the summand -> [add] splits the sum -> beta extraction + logZ extraction *)
    apply (real_eq_trans
             (real_sum_over_S (fun s : S => real_mult (p s)
                                (real_plus (real_mult bta (energy s)) LZ)))
             (real_plus
                (real_sum_over_S (fun s : S => real_mult (p s) (real_mult bta (energy s))))
                (real_sum_over_S (fun s : S => real_mult (p s) LZ)))
             (real_plus (real_mult bta real_energy_exp_temp) LZ)).
    + apply (real_eq_trans
               (real_sum_over_S (fun s : S => real_mult (p s)
                                  (real_plus (real_mult bta (energy s)) LZ)))
               (real_sum_over_S (fun s : S =>
                  real_plus (real_mult (p s) (real_mult bta (energy s)))
                            (real_mult (p s) LZ)))
               (real_plus
                  (real_sum_over_S (fun s : S => real_mult (p s) (real_mult bta (energy s))))
                  (real_sum_over_S (fun s : S => real_mult (p s) LZ)))).
      * apply real_sum_over_S_ext.
        intro s. apply real_distrib.
      * apply (real_sum_over_S_add
                 (fun s : S => real_mult (p s) (real_mult bta (energy s)))
                 (fun s : S => real_mult (p s) LZ)).
    + (* beta extraction + logZ extraction (the two branches) *)
      apply (RealSetoid.real_eq_plus_compat_adapt
               (real_sum_over_S (fun s : S => real_mult (p s) (real_mult bta (energy s))))
               (real_mult bta real_energy_exp_temp)
               (real_sum_over_S (fun s : S => real_mult (p s) LZ))
               LZ).
      * (* beta branch: [Sum p*(beta*e) == beta*E_T] (pointwise reassociation -> linear extraction -> definitional convergence) *)
        apply (real_eq_trans
                 (real_sum_over_S (fun s : S => real_mult (p s) (real_mult bta (energy s))))
                 (real_mult bta (real_sum_over_S (fun s : S => real_mult (p s) (energy s))))
                 (real_mult bta real_energy_exp_temp)).
        -- apply (real_eq_trans
                    (real_sum_over_S (fun s : S => real_mult (p s) (real_mult bta (energy s))))
                    (real_sum_over_S (fun s : S => real_mult bta (real_mult (p s) (energy s))))
                    (real_mult bta (real_sum_over_S (fun s : S => real_mult (p s) (energy s))))).
           ++ apply real_sum_over_S_ext.
              intro s.
              apply (real_eq_trans
                       (real_mult (p s) (real_mult bta (energy s)))
                       (real_mult (real_mult (p s) bta) (energy s))
                       (real_mult bta (real_mult (p s) (energy s)))).
              ** exact (real_mult_assoc (p s) bta (energy s)).
              ** apply (real_eq_trans
                          (real_mult (real_mult (p s) bta) (energy s))
                          (real_mult (real_mult bta (p s)) (energy s))
                          (real_mult bta (real_mult (p s) (energy s)))).
                 --- apply (RealSetoid.real_eq_mult_compat_adapt
                              (real_mult (p s) bta) (real_mult bta (p s))
                              (energy s) (energy s)
                              (real_mult_comm (p s) bta) (real_eq_refl (energy s))).
                 --- apply real_eq_sym.
                     exact (real_mult_assoc bta (p s) (energy s)).
           ++ apply (real_sum_over_S_linear bta
                       (fun s : S => real_mult (p s) (energy s))).
        -- exact (real_eq_refl (real_mult bta real_energy_exp_temp)).
      * (* logZ branch: [Sum p*LZ == LZ * Sum p == LZ * 1 == LZ] *)
        apply (real_eq_trans
                 (real_sum_over_S (fun s : S => real_mult (p s) LZ))
                 (real_mult LZ (real_sum_over_S p))
                 LZ).
        -- apply (real_eq_trans
                    (real_sum_over_S (fun s : S => real_mult (p s) LZ))
                    (real_sum_over_S (fun s : S => real_mult LZ (p s)))
                    (real_mult LZ (real_sum_over_S p))).
           ++ apply real_sum_over_S_ext.
              intro s. apply real_mult_comm.
           ++ apply (real_sum_over_S_linear LZ p).
        -- apply (real_eq_trans
                    (real_mult LZ (real_sum_over_S p))
                    (real_mult LZ real_one)
                    LZ).
           ++ apply (RealSetoid.real_eq_mult_compat_adapt LZ LZ
                       (real_sum_over_S p) real_one
                       (real_eq_refl LZ) real_boltzmann_dist_temp_normalized).
           ++ exact (real_mult_one LZ).
Qed.

End RealTempDefs.
