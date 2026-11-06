(* ConstructiveWorld-Set -- Real-layer instance packs for finite two-point tables. *)

(** * UpAblT7b_real_two_point_pack: Real-layer two-point instance pack.

    Mission.  Assemble the concrete Real-layer two-point instance pack:
      half is positive ([uab7b_half_pos]), two halves normalize to one
      ([uab7b_half_plus_half]), and [uab7b_two_point_pack] realizes the
      uniform two-point statement over [bool]; supporting families give
      bounds, sum positivity, index witnesses, and contradiction elimination.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Lists.List].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp] of this development.

    References.  This development, UpAblT7b_real_two_point_pack.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblT7b_real_two_point_pack.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List.
Import ListNotations.

(* ============ Section 0. The Real-layer two-point constructions (half/two with positivity anchors) ============ *)
(* The half route: [uab7b_half := real_const (1/2)%Q] is a constant
   Cauchy sequence, and its positivity is substituted directly from
   [real_half_pos].  The alternative route through [real_inv_pos] stays
   available to consumers; the constant route taken here needs no
   inversion, and the normalization chain runs through the pointwise
   zero-difference core. *)

Definition uab7b_half : Real := real_const (1 / 2)%Q.
Definition uab7b_two : Real := real_plus real_one real_one.

Theorem uab7b_half_pos : real_lt real_zero uab7b_half.
Proof.
  exact real_half_pos.
Qed.

Theorem uab7b_two_pos : real_lt real_zero uab7b_two.
Proof.
  exact real_two_pos_local.
Qed.

(* The normalization canal: half + half == one, proved pointwise by the
   zero-difference core [real_eq_of_zero_diff] together with the
   pointwise projections [real_plus_proj] and [real_const_proj]. *)
Theorem uab7b_half_plus_half : real_eq (real_plus uab7b_half uab7b_half) real_one.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj uab7b_half uab7b_half n)).
  unfold uab7b_half.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 / 2)%Q n)).
  assert (Ho : projT1 real_one n == 1%Q).
  { unfold real_one. cbn [projT1]. reflexivity. }
  setoid_rewrite Ho.
  field.
Qed.

(* ============ Section 1. The package body: the Real-layer three-leg And package ============ *)
(* Leg one, normalization: the two-point table sums to one, by unfolding
   [real_list_sum] and reusing the additive identity canal of Section 0. *)
Theorem uab7b_pack_norm_leg :
  real_eq (real_list_sum bool (fun _ : bool => uab7b_half) [true; false]) real_one.
Proof.
  cbn [real_list_sum].
  apply (real_eq_trans _ (real_plus uab7b_half uab7b_half) _).
  - exact (RealSetoid.real_eq_plus_compat uab7b_half uab7b_half
             (real_plus uab7b_half real_zero) uab7b_half
             (real_eq_refl uab7b_half) (real_plus_zero uab7b_half)).
  - exact uab7b_half_plus_half.
Qed.

(* The statement restates fa57_W2p_uniform_two_realized at the Real
   layer, reading the sum as [real_list_sum], the equality as [real_eq],
   and the order as [real_lt] (world survey in the header). *)
Theorem uab7b_two_point_pack :
  And (real_eq (real_list_sum bool (fun _ : bool => uab7b_half) [true; false]) real_one)
      (And (forall i : bool, real_lt real_zero ((fun _ : bool => uab7b_half) i))
           (sigT (fun i : bool =>
                    And (Id ((fun _ : bool => true) i) true)
                        (InT i [true; false])))).
Proof.
  split.
  - exact uab7b_pack_norm_leg.
  - split.
    + exact (fun _ => uab7b_half_pos).
    + exact (existT (fun i : bool =>
                       And (Id ((fun _ : bool => true) i) true)
                           (InT i [true; false]))
                    true (id_refl, @InT_here bool true [false])).
Qed.

(* ============ Section 2. The positivity certificate family (scalar and pointwise forms) ============ *)
(* The slot duality.  Scalar slots: [beta_pos], [D_pos], [T_pos],
   [Z_align_pos], [gamma_pos], [mu_pos], [eta_pos], and
   [sf_fisher_nonneg] (its [real_le] form reached by the left
   injection).  Pointwise slots: [pi_ref_pos], [real_pi_old_pos],
   [real_advantage_pos], [tf_pos], [p_pos], [Omega_A_pos],
   [Omega_B_pos], and [uab_temp_factor_pos].
   Each slot is realized by loading half (scalar) or the constant-half
   function (pointwise) and moving the endpoint with
   [RealSetoid.real_lt_id_r]. *)

Theorem uab7b_pos_transfer_any :
  forall x : Real, real_eq x uab7b_half -> real_lt real_zero x.
Proof.
  intros x Hx.
  exact (RealSetoid.real_lt_id_r real_zero (real_plus uab7b_half real_zero) x
           (real_eq_trans _ _ _ (real_plus_zero uab7b_half) (real_eq_sym _ _ Hx))
           (RealSetoid.real_lt_id_r real_zero uab7b_half (real_plus uab7b_half real_zero)
              (real_eq_sym _ _ (real_plus_zero uab7b_half)) uab7b_half_pos)).
Qed.

Theorem uab7b_pos_transfer_pointwise :
  forall (T : Type) (g : T -> Real),
    (forall t : T, real_eq (g t) uab7b_half) ->
    forall t : T, real_lt real_zero (g t).
Proof.
  intros T g Hg t.
  exact (RealSetoid.real_lt_id_r real_zero uab7b_half (g t) (real_eq_sym _ _ (Hg t))
           uab7b_half_pos).
Qed.

(* ============ Section 3. The bound family (half < one and half <= one) ============ *)
(* The slot duality: [ratio_le_one] with the ratio loaded by half.
   The strict bound is assembled here: zero + half < half + half by the
   mixed strict-plus compatibility lemma [real_lt_plus_compat_lt_le]
   with [real_le_refl]; the endpoint then moves twice, to
   half < half + half and to half < one. *)
Theorem uab7b_half_lt_one : real_lt uab7b_half real_one.
Proof.
  apply (RealSetoid.real_lt_id_r uab7b_half (real_plus uab7b_half uab7b_half) real_one
           uab7b_half_plus_half).
  apply (RealSetoid.real_lt_id_l uab7b_half (real_plus real_zero uab7b_half)
           (real_plus uab7b_half uab7b_half)
           (real_eq_sym _ _ (real_plus_zero uab7b_half))).
  exact (real_lt_plus_compat_lt_le real_zero uab7b_half uab7b_half uab7b_half
           uab7b_half_pos (real_le_refl uab7b_half)).
Qed.

Theorem uab7b_half_le_one : real_le uab7b_half real_one.
Proof.
  exact (inl uab7b_half_lt_one).
Qed.

(* Multiplying by one with the endpoint moved (slot duality:
   [eta_lt_inv_L] with L loaded by one and eta by half, giving
   one * half < one). *)
Theorem uab7b_mult_one_half_lt_one : real_lt (real_mult real_one uab7b_half) real_one.
Proof.
  apply (RealSetoid.real_lt_id_l (real_mult real_one uab7b_half) uab7b_half real_one).
  - exact (real_eq_trans _ _ _ (real_mult_comm real_one uab7b_half)
             (real_mult_one uab7b_half)).
  - exact uab7b_half_lt_one.
Qed.

(* ============ Section 4. The sum positivity family (singleton-table truncated mass and partition loading forms) ============ *)
(* The slot duality: [real_minp_temp_sum_pos], [uab_temp_sum_pos],
   [uab_Z_full_pos], and [temp_sum_pos].  The realization loads the
   token table by a singleton, keeps the retention decision constant
   (the [unit] carrier with the [inl] decision), and loads the factor by
   the constant-half function: the truncated sum reduces by definition
   to half + zero, and its positivity follows from the
   endpoint-transfer chain. *)
Theorem uab7b_minp_temp_sum_singleton_pos :
  forall (T : Set) (t0 : T) (prefix : list T),
    real_lt real_zero
      (real_minp_temp_sum T (cons t0 (@nil T)) (fun _ : T => uab7b_half)
         (fun _ _ => unit) (fun _ _ => inl tt) prefix).
Proof.
  intros T t0 prefix.
  cbn [real_minp_temp_sum real_list_sum].
  exact (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
           (real_plus uab7b_half real_zero)
           (real_eq_sym _ _ (real_plus_zero real_zero))
           (real_lt_plus_compat_lt_le real_zero uab7b_half real_zero real_zero
              uab7b_half_pos (real_le_refl real_zero))).
Qed.

Theorem uab7b_list_sum_singleton_pos :
  forall (T : Set) (t0 : T),
    real_lt real_zero
      (real_list_sum T (fun _ : T => uab7b_half) (cons t0 (@nil T))).
Proof.
  intros T t0.
  cbn [real_list_sum].
  exact (RealSetoid.real_lt_id_r real_zero uab7b_half (real_plus uab7b_half real_zero)
           (real_eq_sym _ _ (real_plus_zero uab7b_half)) uab7b_half_pos).
Qed.

(* The two-point table version (the two-point loading form for partitions and truncated mass). *)
Theorem uab7b_list_sum_two_point_pos :
  real_lt real_zero
    (real_list_sum bool (fun _ : bool => uab7b_half) [true; false]).
Proof.
  cbn [real_list_sum].
  apply (RealSetoid.real_lt_id_r real_zero (real_plus uab7b_half uab7b_half)
           (real_plus uab7b_half (real_plus uab7b_half real_zero))
           (RealSetoid.real_eq_plus_compat uab7b_half uab7b_half uab7b_half
              (real_plus uab7b_half real_zero)
              (real_eq_refl uab7b_half)
              (real_eq_sym _ _ (real_plus_zero uab7b_half)))).
  apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
           (real_plus uab7b_half uab7b_half)
           (real_eq_sym _ _ (real_plus_zero real_zero))).
  exact (real_lt_plus_compat_lt_le real_zero uab7b_half real_zero uab7b_half
           uab7b_half_pos (inl uab7b_half_pos)).
Qed.

(* The normalized two-point form of the singleton-table scheme (slot
   duality: [tokens_sum] with tokens loaded by [half; half] and the
   summand loaded by the identity function): the sum of two halves is
   one. *)
Theorem uab7b_list_sum_two_half_norm :
  real_eq
    (real_list_sum Real (fun x : Real => x)
       (cons uab7b_half (cons uab7b_half (@nil Real))))
    real_one.
Proof.
  cbn [real_list_sum].
  apply (real_eq_trans _ (real_plus uab7b_half uab7b_half) _).
  - exact (RealSetoid.real_eq_plus_compat uab7b_half uab7b_half
             (real_plus uab7b_half real_zero) uab7b_half
             (real_eq_refl uab7b_half) (real_plus_zero uab7b_half)).
  - exact uab7b_half_plus_half.
Qed.

(* ============ Section 5. The cardinality positivity family (of_nat lengths, two-point enumeration loading) ============ *)
(* The slot duality: [real_group_size_pos], [real_size_pos], and [Hpos].
   The realization loads the enumeration slot by the two-point table,
   with the cover component built element by element through [InT] in
   the shape of [uab7b_cover_two_point]; the cardinality positivity
   chain is reproved from scratch for the two-point specialization, in
   the shape of [tw_list_len_pos], with no extra requires and no empty
   matches. *)
Theorem uab7b_of_nat_one_pos_aux : real_lt real_zero (real_plus real_one real_zero).
Proof.
  exact (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
           (real_plus real_one real_zero)
           (real_eq_sym _ _ (real_plus_zero real_zero))
           (real_lt_plus_compat_lt_le real_zero real_one real_zero real_zero
              real_lt_zero_one (real_le_refl real_zero))).
Qed.

Theorem uab7b_of_nat_nonneg : forall n : nat, real_le real_zero (real_of_nat n).
Proof.
  intro n.
  induction n as [| n IH].
  - exact (real_le_refl real_zero).
  - cbn [real_of_nat].
    exact (inl (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                  (real_plus real_one (real_of_nat n))
                  (real_eq_sym _ _ (real_plus_zero real_zero))
                  (real_lt_plus_compat_lt_le real_zero real_one real_zero
                     (real_of_nat n) real_lt_zero_one IH))).
Qed.

Theorem uab7b_group_size_two_pos :
  real_lt real_zero (real_of_nat (Datatypes.length [true; false])).
Proof.
  cbn [Datatypes.length real_of_nat].
  apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
           (real_plus real_one (real_plus real_one real_zero))).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_lt_plus_compat_lt_le.
    + exact real_lt_zero_one.
    + exact (inl uab7b_of_nat_one_pos_aux).
Qed.

(* ============ Section 6. The index bound witness family (reflection level) ============ *)
(* The slot duality: [tokens_ne] =
   [sigT (fun i => NatLt i (Datatypes.length tokens))].  The realization
   loads tokens by a singleton table and builds the bound at reflection
   level: the [NatLt] carrier is a boolean identity holding [Nat.ltb i j]
   against [true], [Nat.ltb 0 1] reduces by definition to [true], and
   [id_refl] substitutes directly. *)
Theorem uab7b_tokens_ne_singleton :
  forall (T : Set) (t0 : T),
    sigT (fun i : nat => NatLt i (Datatypes.length (cons t0 (@nil T)))).
Proof.
  intros T t0.
  exact (existT _ O id_refl).
Qed.

(* ============ Section 7. The contradiction elimination family (counting loading form) ============ *)
(* The slot duality: [real_count_heavier_succ_le] with the factor loaded
   by the constant half and the count by the constant zero.  The premise
   [real_lt uab7b_half uab7b_half] is contradictory, and
   [real_lt_not_eq] eliminates it against the reflexivity of [real_eq];
   the conclusion [Empty_set] keeps the statement a [Set]-level function. *)
Theorem uab7b_half_lt_half_contra : real_lt uab7b_half uab7b_half -> Empty_set.
Proof.
  intro H.
  exact (real_lt_not_eq uab7b_half uab7b_half H (real_eq_refl uab7b_half)).
Qed.

(* ============ Section 8. The row-error loading family (zero-core loading form) ============ *)
(* The slot duality: [Hrow] with the core loaded by the constant zero,
   the retention decision constantly excluding, and the error constant
   loaded by zero: the row-error sum reduces by definition to
   |zero - zero| + zero = zero, and the resulting [real_le] is
   substituted by the equality branch.  This file supplies the
   normalization core whose row sums vanish, pointwise a zero
   difference. *)
Theorem uab7b_row_err_singleton_norm :
  forall (T : Set) (t0 : T),
    real_eq
      (real_list_sum T
         (fun _ : T => real_abs (real_minus_r real_zero real_zero))
         (cons t0 (@nil T)))
      real_zero.
Proof.
  intros T t0.
  apply real_eq_of_zero_diff.
  intro n.
  cbn [real_list_sum].
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ n)).
  assert (Hz : projT1 real_zero n == 0%Q).
  { unfold real_zero. cbn [projT1]. reflexivity. }
  setoid_rewrite Hz.
  assert (Ha : projT1 (real_abs (real_minus_r real_zero real_zero)) n
                 == Qabs (0 + - 0)%Q).
  { unfold real_abs, real_minus_r, real_zero. cbn. reflexivity. }
  rewrite Ha.
  reflexivity.
Qed.

(* ============ Section 9. The geometric bound family (the additive inverse of the zero anchor) ============ *)
(* The slot duality: [real_energy_lower] with the maximal energy loaded
   by zero and the energy by the constant zero.  The bound
   [real_le (real_opp real_zero) real_zero] is substituted by the
   equality branch through [inr]. *)
Theorem uab7b_opp_zero_le : real_le (real_opp real_zero) real_zero.
Proof.
  apply (RealSetoid.real_eq_le (real_opp real_zero) real_zero).
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj real_zero n)).
  assert (Hz : projT1 real_zero n == 0%Q).
  { unfold real_zero. cbn [projT1]. reflexivity. }
  setoid_rewrite Hz.
  reflexivity.
Qed.

(* ============ Closing section: each main statement audited closed ============ *)
Print Assumptions uab7b_half_pos.
Print Assumptions uab7b_two_pos.
Print Assumptions uab7b_half_plus_half.
Print Assumptions uab7b_pack_norm_leg.
Print Assumptions uab7b_two_point_pack.
Print Assumptions uab7b_pos_transfer_any.
Print Assumptions uab7b_pos_transfer_pointwise.
Print Assumptions uab7b_half_lt_one.
Print Assumptions uab7b_half_le_one.
Print Assumptions uab7b_mult_one_half_lt_one.
Print Assumptions uab7b_minp_temp_sum_singleton_pos.
Print Assumptions uab7b_list_sum_singleton_pos.
Print Assumptions uab7b_list_sum_two_point_pos.
Print Assumptions uab7b_list_sum_two_half_norm.
Print Assumptions uab7b_of_nat_one_pos_aux.
Print Assumptions uab7b_of_nat_nonneg.
Print Assumptions uab7b_group_size_two_pos.
Print Assumptions uab7b_tokens_ne_singleton.
Print Assumptions uab7b_half_lt_half_contra.
Print Assumptions uab7b_row_err_singleton_norm.
Print Assumptions uab7b_opp_zero_le.
