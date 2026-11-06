(* ConstructiveWorld-Set -- finite-merge group of real-layer debt-clearing members. *)

(** * G02_Debt: square-root witnesses, softmax scaling and Gibbs duality.

    Mission.  square-root witnesses, softmax scaling and Gibbs duality: a
      constructive square root of any nonnegative real under the abstract
      identity interface ([sqrt_witness_exists_abstract], premise bridge
      [sqrt_premise_le_intro]); the scaled and the temperature-indexed
      softmax families coincide by the scale-temperature duality
      ([real_scale_temp_duality]); softmax equals the Boltzmann
      distribution at any temperature ([real_attention_is_gibbs_temp]).

    Dependencies.  No direct Stdlib requires.  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp] of this development.

    References.  This development, G02_Debt.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  Main theorems [sqrt_witness_exists_abstract],
      [real_scale_temp_duality] and [real_attention_is_gibbs_temp] (with the
      premise bridge [sqrt_premise_le_intro] and all support lemmas) are carried
      by [Set] ([Set]-sorted [Id]/[lt]/[le] and [real_eq]/[real_lt]; existence in
      [sigT]); no named statement of this module has a Stdlib-[Prop] face.

    Build.  [coqc -native-compiler no -q -Q . "" G02_Debt.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
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

Section SqrtAbstract.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* square witness, mirroring the root-module sqrt_witness: r*r == d *)
Definition dsq_sqrt_witness (d r : R) : Set := Id (mult r r) d.

(* two := 1+1 (the literal 2); two > 0 follows by assembling plus_positive with one_pos *)
Definition two_abs : R := plus one one.
Lemma two_abs_pos : lt zero two_abs.
Proof.
  exact (plus_positive one one one_pos one_pos).
Qed.

(* half := inv(two), and half + half == one.
   Chain: half*two == one (inv_pos_correct, via mult_comm), and
   half*two == half*(1+1) == half*1 + half*1 == half + half
   (distrib with mult_one applied twice). *)
Definition half_abs : R := inv_pos two_abs two_abs_pos.
Lemma half_plus_half : Id (plus half_abs half_abs) one.
Proof.
  assert (Hd : Id (mult half_abs two_abs) one)
    by exact (id_trans (mult_comm half_abs two_abs)
                       (inv_pos_correct two_abs two_abs_pos)).
  assert (Hsplit : Id (mult half_abs two_abs) (plus half_abs half_abs))
    by exact (id_trans (distrib half_abs one one)
                       (id_cong2 (fun a b => plus a b)
                                 (mult_one half_abs) (mult_one half_abs))).
  exact (id_trans (id_sym Hsplit) Hd).
Qed.

(* the Or premise carries exactly the constructive content of le
   (a record of the one-way interface bridge lt_le_iff) *)
Lemma sqrt_premise_le_intro : forall d : R, Or (lt zero d) (Id zero d) -> le zero d.
Proof.
  intros d H. exact (lt_le_iff zero d H).
Qed.

(* ---- main theorem (member 3): a square-root witness for any nonnegative
   d at the abstract Id level ----
   left branch (d > 0, the positive-gap certificate): r := exp_neg(half*log_inv d).
     r*r == d: exp(h)*exp(h) == exp(h+h) (exp_neg_plus read backwards)
       == exp(log_inv d) (h+h == half*L+half*L == half*(L+L)
       == one*L == L, using half+half == one)
       == d (exp_neg_log_inv as the right inverse).
     r > 0: exp_neg_pos followed by lt_le_iff.
   right branch (d == 0 in the Id sense, the identity certificate): r := zero;
     0 <= 0 (le_refl) and 0*0 == 0 (mult_zero) == d (Hdeq). *)
Theorem sqrt_witness_exists_abstract :
  forall d : R, Or (lt zero d) (Id zero d) ->
  sigT (fun r : R => And (le zero r) (Id (mult r r) d)).
Proof.
  intros d Hd.
  destruct Hd as [Hdlt | Hdeq].
  - (* case 1: d > 0, take r := exp(half*log d). *)
    exists (exp_neg (mult half_abs (log_inv d))).
    split.
    + (* r > 0: exp is strictly positive (the le left summand is lt, via lt_le_iff) *)
      exact (lt_le_iff zero (exp_neg (mult half_abs (log_inv d)))
                        (inl (exp_neg_pos (mult half_abs (log_inv d))))).
    + (* r*r == d: the three-link chain exp(h)*exp(h) == exp(h+h) == exp(log d) == d *)
      assert (Hinner : Id (plus (mult half_abs (log_inv d))
                                (mult half_abs (log_inv d)))
                          (log_inv d)).
      { exact (id_trans
                (id_trans
                  (id_cong2 (fun a b => plus a b)
                            (mult_comm half_abs (log_inv d))
                            (mult_comm half_abs (log_inv d)))
                  (id_trans (id_sym (distrib (log_inv d) half_abs half_abs))
                            (mult_comm (log_inv d) (plus half_abs half_abs))))
                (id_trans
                  (id_cong (fun x => mult x (log_inv d)) half_plus_half)
                  (id_trans (mult_comm one (log_inv d))
                            (mult_one (log_inv d))))). }
      exact (id_trans
              (id_sym (exp_neg_plus (mult half_abs (log_inv d))
                                    (mult half_abs (log_inv d))))
              (id_trans (id_cong (fun x => exp_neg x) Hinner)
                        (exp_neg_log_inv d))).
  - (* case 2: d == 0 in the Id sense, take r := zero. *)
    exists zero.
    split.
    + (* 0 <= 0 by reflexivity *)
      apply le_refl.
    + (* 0*0 == 0 == d *)
      exact (id_trans (mult_zero zero) Hdeq).
Qed.

(* restatement in witness form (the dsq_sqrt_witness named presentation) *)
Lemma sqrt_witness_exists_abstract_witness :
  forall d : R, Or (lt zero d) (Id zero d) ->
  sigT (fun r : R => And (le zero r) (dsq_sqrt_witness d r)).
Proof.
  intros d H.
  exact (sqrt_witness_exists_abstract d H).
Qed.

(* instance (a machine-checkable sanity statement): the abstract square root
   of one is constructible, r := exp(half*log_inv 1) with r >= 0 and
   r*r == 1 (the root-module real_sqrt_one copy). *)
Lemma sqrt_one_abstract :
  sigT (fun r : R => And (le zero r) (Id (mult r r) one)).
Proof.
  exact (sqrt_witness_exists_abstract one (inl one_pos)).
Qed.

End SqrtAbstract.

(* ======== G02_Debt member module: UpDebtDual (merged verbatim, carries its own Require face) ======== *)
(* ============================================================ *)
(* UpDebtDual.v -- debt-clearing packaging module (member 2).        *)
(*   The scale-temperature duality family at the Real level: a copy  *)
(*   of the abstract-level scale_temp_duality of the baseline        *)
(*   ConstructiveWorld-Main module, together with its companion      *)
(*   scaled family.                                                  *)
(*                                                                   *)
(*   Defining family:                                                *)
(*     real_softmax_scaled c z s       := e^{c*z_s}/sum e^{c*z}      *)
(*     real_softmax_temp_param T0 z s  := e^{z/T0}/sum e^{z/T0}      *)
(*   Main statement:                                                 *)
(*     real_scale_temp_duality: for c > 0,                           *)
(*       real_softmax_scaled (1/c) == real_softmax_temp_param c      *)
(*   Companions: positivity and normalization of the scaled family,  *)
(*   and real_scale_inv_T_eq_softmax_temp: the 1/T-scaled family     *)
(*   equals the temperature-form softmax of the baseline, by the     *)
(*   definitional equality of the partition functions through        *)
(*   real_inv_pos_ext, a pure identity chain.                        *)
(*                                                                   *)
(*   All statements live at the Set level (real_lt/real_eq/sigT/     *)
(*   And) and all proofs close with Qed.                             *)
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

Section RealScaleDual.

(* abstract state space, declared by this Real-level Section itself
   (the RealAttnMain pattern) *)
Variable S : Type.

(* honest interface: summation over the abstract S (instantiable at the
   Real level; zero axioms) *)
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s => real_mult a (f s))) (real_mult a (real_sum_over_S f)).

(* ---- scaled family: real_softmax_scaled ---- *)

(* scaled partition function: Z_c(z) := sum_s e^{c*z_s} (c an arbitrary real) *)
Definition real_partition_function_scaled (c : Real) (z : S -> Real) : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult c (z s))).

(* positivity of the scaled partition: exp is strictly positive, combined
   with sum_pos_preserved *)
Lemma real_partition_function_scaled_pos :
  forall (c : Real) (z : S -> Real), real_lt real_zero (real_partition_function_scaled c z).
Proof.
  intros c z.
  exact (real_sum_pos_preserved
           (fun s : S => real_exp_neg (real_opp (real_mult c (z s))))
           (fun s : S => real_exp_neg_pos (real_opp (real_mult c (z s))))).
Qed.

(* scaled softmax: sc(z; c)_s := e^{c*z_s}*inv(Z_c(z)) (c an arbitrary real) *)
Definition real_softmax_scaled (c : Real) (z : S -> Real) (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult c (z s)))
            (real_inv_pos (real_partition_function_scaled c z)
                          (real_partition_function_scaled_pos c z)).

(* probability law of the scaled family, positivity: exp is strictly
   positive and inv preserves it *)
Theorem real_softmax_scaled_pos :
  forall (c : Real) (z : S -> Real) (s : S), real_lt real_zero (real_softmax_scaled c z s).
Proof.
  intros c z s.
  unfold real_softmax_scaled, real_exp_pos_fn.
  apply real_mult_pos_compat.
  - apply real_exp_neg_pos.
  - apply real_inv_pos_pos.
Qed.

(* probability law of the scaled family, normalization: sum_s sc(z;c)_s == 1.
   Chain: swap the factors termwise (sum_ext + real_mult_comm), pull the
   scalar out by linearity (sum_linear), then inv(Z_c)*Z_c == 1
   (real_inv_pos_correct). *)
Theorem real_softmax_scaled_normalized :
  forall (c : Real) (z : S -> Real),
    real_eq (real_sum_over_S (fun s => real_softmax_scaled c z s)) real_one.
Proof.
  intros c z.
  unfold real_softmax_scaled.
  apply (real_eq_trans
          (real_sum_over_S (fun s => real_mult
                             (real_exp_pos_fn (real_mult c (z s)))
                             (real_inv_pos (real_partition_function_scaled c z)
                                           (real_partition_function_scaled_pos c z))))
          (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                   (real_partition_function_scaled_pos c z))
                     (real_sum_over_S (fun s => real_exp_pos_fn (real_mult c (z s)))))
          real_one).
  - (* 1. factor swap, then extraction by linearity *)
    apply (real_eq_trans
            (real_sum_over_S (fun s => real_mult
                               (real_exp_pos_fn (real_mult c (z s)))
                               (real_inv_pos (real_partition_function_scaled c z)
                                             (real_partition_function_scaled_pos c z))))
            (real_sum_over_S (fun s => real_mult
                               (real_inv_pos (real_partition_function_scaled c z)
                                             (real_partition_function_scaled_pos c z))
                               (real_exp_pos_fn (real_mult c (z s)))))
            _).
    + apply real_sum_over_S_ext.
      intro s. apply real_mult_comm.
    + apply real_sum_over_S_linear.
  - (* 2. inv(Z_c)*Z_c == 1 *)
    apply (real_eq_trans
            (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                     (real_partition_function_scaled_pos c z))
                       (real_sum_over_S (fun s => real_exp_pos_fn (real_mult c (z s)))))
            (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                     (real_partition_function_scaled_pos c z))
                       (real_partition_function_scaled c z))
            real_one).
    + apply real_eq_refl.
    + apply (real_eq_trans
              (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                       (real_partition_function_scaled_pos c z))
                         (real_partition_function_scaled c z))
              (real_mult (real_partition_function_scaled c z)
                         (real_inv_pos (real_partition_function_scaled c z)
                                       (real_partition_function_scaled_pos c z)))
              real_one).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* ---- temperature-indexed family: the explicit (T0, HT0) form ---- *)

(* temperature-indexed partition function: Z_T0(z) := sum_s e^{z_s/T0} *)
Definition real_partition_function_temp_param
  (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real) : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s))).

(* positivity of the temperature-indexed partition function *)
Lemma real_partition_function_temp_param_pos :
  forall (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real),
    real_lt real_zero (real_partition_function_temp_param T0 HT0 z).
Proof.
  intros T0 HT0 z.
  exact (real_sum_pos_preserved
           (fun s : S => real_exp_neg (real_opp (real_mult (real_inv_pos T0 HT0) (z s))))
           (fun s : S =>
              real_exp_neg_pos (real_opp (real_mult (real_inv_pos T0 HT0) (z s))))).
Qed.

(* temperature-indexed softmax: e^{z_s/T0}*inv(Z_T0(z)) *)
Definition real_softmax_temp_param
  (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real) (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))
            (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                          (real_partition_function_temp_param_pos T0 HT0 z)).

(* positivity of the temperature-indexed family (companion) *)
Theorem real_softmax_temp_param_pos :
  forall (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real) (s : S),
    real_lt real_zero (real_softmax_temp_param T0 HT0 z s).
Proof.
  intros T0 HT0 z s.
  unfold real_softmax_temp_param, real_exp_pos_fn.
  apply real_mult_pos_compat.
  - apply real_exp_neg_pos.
  - apply real_inv_pos_pos.
Qed.

(* normalization of the temperature-indexed family (companion) *)
Theorem real_softmax_temp_param_normalized :
  forall (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real),
    real_eq (real_sum_over_S (fun s => real_softmax_temp_param T0 HT0 z s)) real_one.
Proof.
  intros T0 HT0 z.
  unfold real_softmax_temp_param.
  apply (real_eq_trans
          (real_sum_over_S (fun s => real_mult
                             (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))
                             (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                           (real_partition_function_temp_param_pos T0 HT0 z))))
          (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                   (real_partition_function_temp_param_pos T0 HT0 z))
                     (real_sum_over_S (fun s =>
                       real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))))
          real_one).
  - apply (real_eq_trans
            (real_sum_over_S (fun s => real_mult
                               (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))
                               (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                             (real_partition_function_temp_param_pos T0 HT0 z))))
            (real_sum_over_S (fun s => real_mult
                               (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                             (real_partition_function_temp_param_pos T0 HT0 z))
                               (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))))
            _).
    + apply real_sum_over_S_ext.
      intro s. apply real_mult_comm.
    + apply real_sum_over_S_linear.
  - apply (real_eq_trans
            (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                     (real_partition_function_temp_param_pos T0 HT0 z))
                       (real_sum_over_S (fun s =>
                         real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))))
            (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                     (real_partition_function_temp_param_pos T0 HT0 z))
                       (real_partition_function_temp_param T0 HT0 z))
            real_one).
    + apply real_eq_refl.
    + apply (real_eq_trans
              (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                       (real_partition_function_temp_param_pos T0 HT0 z))
                         (real_partition_function_temp_param T0 HT0 z))
              (real_mult (real_partition_function_temp_param T0 HT0 z)
                         (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                       (real_partition_function_temp_param_pos T0 HT0 z)))
              real_one).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* ---- main statement (member 2 core): the scale-temperature duality ----
   for c > 0, softmax with logits scaled by 1/c equals the softmax at
   temperature c.  After unfolding, the first factors of both sides (the
   numerators e^{(1/c)*z_s}) agree verbatim and are closed by mult_compat
   with refl; the partition functions are definitionally equal (both sides
   unfold to the same sum), so real_inv_pos_ext with real_eq_refl closes
   the rest.  A pure identity chain with no new axioms. *)
Theorem real_scale_temp_duality :
  forall (c : Real) (Hc : real_lt real_zero c) (z : S -> Real) (s : S),
    real_eq (real_softmax_scaled (real_inv_pos c Hc) z s)
            (real_softmax_temp_param c Hc z s).
Proof.
  intros c Hc z s.
  unfold real_softmax_scaled, real_softmax_temp_param.
  apply (RealSetoid.real_eq_mult_compat_adapt
          (real_exp_pos_fn (real_mult (real_inv_pos c Hc) (z s)))
          (real_exp_pos_fn (real_mult (real_inv_pos c Hc) (z s)))
          (real_inv_pos (real_partition_function_scaled (real_inv_pos c Hc) z)
                        (real_partition_function_scaled_pos (real_inv_pos c Hc) z))
          (real_inv_pos (real_partition_function_temp_param c Hc z)
                        (real_partition_function_temp_param_pos c Hc z))
          (real_eq_refl _)
          (real_inv_pos_ext
            (real_partition_function_scaled (real_inv_pos c Hc) z)
            (real_partition_function_temp_param c Hc z)
            (real_partition_function_scaled_pos (real_inv_pos c Hc) z)
            (real_partition_function_temp_param_pos c Hc z)
            (real_eq_refl _))).
Qed.

(* the symmetric direction: softmax at temperature c equals the 1/c-scaled
   softmax (real_eq_sym) *)
Lemma real_temp_is_scale_duality :
  forall (c : Real) (Hc : real_lt real_zero c) (z : S -> Real) (s : S),
    real_eq (real_softmax_temp_param c Hc z s)
            (real_softmax_scaled (real_inv_pos c Hc) z s).
Proof.
  intros c Hc z s.
  exact (real_eq_sym (real_softmax_scaled (real_inv_pos c Hc) z s)
                     (real_softmax_temp_param c Hc z s)
                     (real_scale_temp_duality c Hc z s)).
Qed.

(* ---- Section-level temperature bridge: the 1/T-scaled family equals the
   baseline temperature-form softmax ----
   in the baseline softmax_temp shape, the temperature T and the partition
   Z_T are plain Section variables (rather than an indexed family carrying
   a positivity premise); this Section rebuilds that shape and bridges the
   two forms by real_inv_pos_ext with real_eq_refl (definitional equality
   of the partition functions). *)
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable z_logits : S -> Real.

(* the baseline temperature-form partition (Section-level temperature shape) *)
Definition real_partition_function_temp : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s))).

Lemma real_partition_function_temp_pos : real_lt real_zero real_partition_function_temp.
Proof.
  exact (real_sum_pos_preserved
           (fun s : S => real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
           (fun s : S =>
              real_exp_neg_pos (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))).
Qed.

(* the baseline temperature-form softmax (Section-level temperature shape) *)
Definition real_softmax_temp (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
            (real_inv_pos real_partition_function_temp real_partition_function_temp_pos).

(* the bridge (the duality lemma instantiated at c := T, plus the
   definitional equality of the partition functions) *)
Lemma real_scale_inv_T_eq_softmax_temp :
  forall s : S,
    real_eq (real_softmax_scaled (real_inv_pos T T_pos) z_logits s)
            (real_softmax_temp s).
Proof.
  intro s.
  unfold real_softmax_scaled, real_softmax_temp.
  apply (RealSetoid.real_eq_mult_compat_adapt
          (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
          (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
          (real_inv_pos (real_partition_function_scaled (real_inv_pos T T_pos) z_logits)
                        (real_partition_function_scaled_pos (real_inv_pos T T_pos) z_logits))
          (real_inv_pos real_partition_function_temp real_partition_function_temp_pos)
          (real_eq_refl _)
          (real_inv_pos_ext
            (real_partition_function_scaled (real_inv_pos T T_pos) z_logits)
            real_partition_function_temp
            (real_partition_function_scaled_pos (real_inv_pos T T_pos) z_logits)
            real_partition_function_temp_pos
            (real_eq_refl _))).
Qed.

End RealScaleDual.

(* ======== G02_Debt member module: UpDebtGibbsT (merged verbatim, carries its own Require face) ======== *)
(* ============================================================ *)
(* UpDebtGibbsT.v -- debt-clearing packaging module (member 1).      *)
(*   The Real-level restatement of attention_is_gibbs_temp: softmax  *)
(*   equals Boltzmann at any temperature.                            *)
(*                                                                   *)
(*   Template: a verbatim translation of the unit-temperature        *)
(*   real_attention_is_gibbs of the baseline ConstructiveWorld-Main: *)
(*     the temperature-equality premise real_eq (inv T) (inv D),     *)
(*     plus energy == -logits pointwise and equality of the two      *)
(*     partition functions,                                          *)
(*     yield pointwise real_eq (real_softmax_temp s)                 *)
(*     (real_boltzmann_dist_attn s).                                 *)
(*                                                                   *)
(*   The Real level had no temperature-form softmax or partition     *)
(*   definition, so both are built here first:                       *)
(*     gibbst_real_partition_function_temp := sum e^{z/T},           *)
(*     gibbst_real_softmax_temp s := e^{z_s/T}*inv(Z_T),             *)
(*   with companion positivity and normalization lemmas.  Proof      *)
(*   core: real_inv algebra + cauchy_real_exp_wd + real_inv_pos_ext  *)
(*   + real_mult_comm; every step of the unit-temperature version    *)
(*   has a counterpart here.                                         *)
(*                                                                   *)
(*   The world choice follows the baseline real_attention_is_gibbs   *)
(*   in carrying its statements at the Real level of this            *)
(*   development.                                                    *)
(*                                                                   *)
(*   All statements live at the Set level (real_lt/real_eq/sigT/     *)
(*   the development's And) and all proofs close with Qed.           *)
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

Section RealAttnGibbsTemp.

(* abstract state space, declared by this Real-level Section itself
   (the RealAttnMain pattern) *)
Variable S : Type.

(* honest interface: summation over the abstract S (instantiable at the
   Real level; zero axioms) *)
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s => real_mult a (f s))) (real_mult a (real_sum_over_S f)).

(* the temperatures (inference-side T and thermodynamic-side D), the energy
   and the logits (Real level) *)
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable energy : S -> Real.
Variable z_logits : S -> Real.

(* ---- basic helper: real_eq extensionality of real_exp_neg ---- *)
(* (the real_exp_neg form of cauchy_real_exp_wd; real_exp_neg x is      *)
(*  definitionally cauchy_real_exp (-x))                                *)
Lemma real_exp_neg_wd : forall a b : Real,
  real_eq a b -> real_eq (real_exp_neg a) (real_exp_neg b).
Proof.
  intros a b H.
  exact (cauchy_real_exp_wd (real_opp a) (real_opp b)
           (RealSetoid.real_eq_opp_compat a b H)).
Qed.

(* ---- temperature-form partition function (Real level): Z_T := sum_s e^{z_s/T} ---- *)
Definition gibbst_real_partition_function_temp : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s))).

Lemma gibbst_real_partition_function_temp_pos : real_lt real_zero gibbst_real_partition_function_temp.
Proof.
  exact (real_sum_pos_preserved
           (fun s : S => real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
           (fun s : S =>
              real_exp_neg_pos (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))).
Qed.

(* ---- temperature-form softmax (Real level): e^{z_s/T}*inv(Z_T) ---- *)
Definition gibbst_real_softmax_temp (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
            (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos).

(* companion positivity: exp is strictly positive and inv preserves it
   (real_mult_pos_compat) *)
Theorem real_softmax_temp_pos : forall s : S, real_lt real_zero (gibbst_real_softmax_temp s).
Proof.
  intro s. unfold gibbst_real_softmax_temp, real_exp_pos_fn.
  apply real_mult_pos_compat.
  - apply real_exp_neg_pos.
  - apply real_inv_pos_pos.
Qed.

(* companion normalization: sum_s softmax_temp(s) == 1.
   Chain: swap the factors termwise (sum_ext + real_mult_comm), pull the
   scalar out by linearity (sum_linear), then inv(Z_T)*Z_T == 1
   (real_inv_pos_correct). *)
Theorem real_softmax_temp_normalized :
  real_eq (real_sum_over_S (fun s => gibbst_real_softmax_temp s)) real_one.
Proof.
  unfold gibbst_real_softmax_temp.
  apply (real_eq_trans
          (real_sum_over_S (fun s => real_mult
                             (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
                             (real_inv_pos gibbst_real_partition_function_temp
                                           gibbst_real_partition_function_temp_pos)))
          (real_mult (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos)
                     (real_sum_over_S (fun s =>
                       real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))))
          real_one).
  - (* 1. factor swap, then extraction by linearity *)
    apply (real_eq_trans
            (real_sum_over_S (fun s => real_mult
                               (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
                               (real_inv_pos gibbst_real_partition_function_temp
                                             gibbst_real_partition_function_temp_pos)))
            (real_sum_over_S (fun s => real_mult
                               (real_inv_pos gibbst_real_partition_function_temp
                                             gibbst_real_partition_function_temp_pos)
                               (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))))
            _).
    + apply real_sum_over_S_ext.
      intro s. apply real_mult_comm.
    + apply real_sum_over_S_linear.
  - (* 2. inv(Z_T)*Z_T == 1 *)
    apply (real_eq_trans
            (real_mult (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos)
                       (real_sum_over_S (fun s =>
                         real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))))
            (real_mult (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos)
                       gibbst_real_partition_function_temp)
            real_one).
    + apply real_eq_refl.
    + apply (real_eq_trans
              (real_mult (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos)
                         gibbst_real_partition_function_temp)
              (real_mult gibbst_real_partition_function_temp
                         (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos))
              real_one).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* ---- the Boltzmann side (same structure as the unit-temperature version) ---- *)
(* the Boltzmann factor (Real level): e^{-e(s)/D} *)
Definition gibbst_real_boltzmann_factor (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)).

(* the thermodynamic partition (Real level): sum_s boltzmann_factor *)
Definition gibbst_real_Z_thermo : Real := real_sum_over_S gibbst_real_boltzmann_factor.

Variable real_Z_thermo_pos : real_lt real_zero gibbst_real_Z_thermo.

(* the Boltzmann distribution (Real level): inv(Z_thermo)*factor *)
Definition gibbst_real_boltzmann_dist_attn (s : S) : Real :=
  real_mult (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos) (gibbst_real_boltzmann_factor s).

(* ---- main statement (member 1): softmax equals Boltzmann at any
   temperature ----
   premises: (i) 1/T == 1/D (the temperatures unify, pointwise equality of
   the real_inv_pos values); (ii) energy == -logits pointwise in s;
   (iii) Z_thermo == Z_T (equal partition functions).
   conclusion: for every s, gibbst_real_softmax_temp s ==
   gibbst_real_boltzmann_dist_attn s.
   proof core (mirroring the unit-temperature version step by step):
   the factor bridge (real_opp_mult + temperature unification + the energy
   replacement + exp extensionality), then unification of the inverses
   (HZ + real_inv_pos_ext), then the assembly (mult commutation + the
   four-slot pointwise mult_compat). *)
Theorem real_attention_is_gibbs_temp :
  (real_eq (real_inv_pos T T_pos) (real_inv_pos D D_pos)) ->
  (forall s : S, real_eq (energy s) (real_opp (z_logits s))) ->
  real_eq gibbst_real_Z_thermo gibbst_real_partition_function_temp ->
  forall s : S, real_eq (gibbst_real_softmax_temp s) (gibbst_real_boltzmann_dist_attn s).
Proof.
  intros HDT Henergy HZ s.
  unfold gibbst_real_softmax_temp, gibbst_real_boltzmann_dist_attn, gibbst_real_boltzmann_factor, real_exp_pos_fn.
  (* 1. factor bridge: e^{-(-z(s)/T)} == e^{-e(s)/D} *)
  assert (Hf : real_eq (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                       (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))).
  {
    apply real_exp_neg_wd.
    apply (real_eq_trans _ (real_mult (real_inv_pos D D_pos) (real_opp (z_logits s))) _).
    - apply (real_eq_trans _ (real_mult (real_inv_pos T T_pos) (real_opp (z_logits s))) _).
      + (* -(z/T) == (1/T)*(-z), by real_opp_mult *)
        apply real_opp_mult.
      + (* (1/T)*(-z) == (1/D)*(-z), by the temperature unification HDT *)
        apply (RealSetoid.real_eq_mult_compat_adapt
                (real_inv_pos T T_pos) (real_inv_pos D D_pos)
                (real_opp (z_logits s)) (real_opp (z_logits s))
                HDT (real_eq_refl _)).
    - (* (1/D)*(-z) == (1/D)*e, by energy == -logits read symmetrically *)
      apply (RealSetoid.real_eq_mult_compat_adapt
              (real_inv_pos D D_pos) (real_inv_pos D D_pos)
              (real_opp (z_logits s)) (energy s)
              (real_eq_refl _) (real_eq_sym _ _ (Henergy s))).
  }
  (* 2. unification of the inverses: inv(Z_thermo) == inv(Z_T), by
     HZ + real_inv_pos_ext *)
  assert (Hie : real_eq (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos)
                        (real_inv_pos gibbst_real_partition_function_temp
                                      gibbst_real_partition_function_temp_pos)).
  { apply (real_inv_pos_ext gibbst_real_Z_thermo gibbst_real_partition_function_temp
                            real_Z_thermo_pos gibbst_real_partition_function_temp_pos).
    exact HZ. }
  (* 3. assembly (step 3 of the unit-temperature copy) *)
  apply (real_eq_trans _ (real_mult (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                                    (real_inv_pos gibbst_real_partition_function_temp
                                                  gibbst_real_partition_function_temp_pos)) _).
  - apply real_eq_refl.
  - apply (real_eq_trans _ (real_mult (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                                      (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos)) _).
    + apply (RealSetoid.real_eq_mult_compat_adapt
              (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
              (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
              (real_inv_pos gibbst_real_partition_function_temp gibbst_real_partition_function_temp_pos)
              (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos)
              (real_eq_refl _) (real_eq_sym _ _ Hie)).
    + apply (real_eq_trans _ (real_mult (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos)
                                        (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))) _).
      * apply real_mult_comm.
      * apply (RealSetoid.real_eq_mult_compat_adapt
                (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos)
                (real_inv_pos gibbst_real_Z_thermo real_Z_thermo_pos)
                (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))
                (real_eq_refl _) Hf).
Qed.

End RealAttnGibbsTemp.
Print Assumptions sqrt_premise_le_intro.
Print Assumptions real_partition_function_scaled_pos.
Print Assumptions real_partition_function_temp_param_pos.
Print Assumptions real_partition_function_temp_pos.
Print Assumptions gibbst_real_partition_function_temp_pos.
Print Assumptions real_temp_is_scale_duality.
Print Assumptions real_exp_neg_wd.
