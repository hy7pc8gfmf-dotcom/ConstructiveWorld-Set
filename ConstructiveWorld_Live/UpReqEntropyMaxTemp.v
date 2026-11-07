(* ConstructiveWorld-Set — temperature characterization of the
   maximum-entropy distribution at fixed energy. *)

(** * UpReqEntropyMaxTemp: at fixed energy the maximum-entropy distribution
      is the Boltzmann distribution, up to additive [eps] slack.

    Mission.  Over an abstract normalized sum interface on a state type
      [S]: every normalized pointwise-positive [p] with the same energy
      expectation as the temperature-[T] Boltzmann distribution obeys
      [S[p] <= S[p_T] + eps] ([real_max_entropy_is_boltzmann_temp_eps]);
      supported by [real_sum_le_list_carrier_instance],
      [real_le_plus_nonneg_r], and [real_plus_neg_cancel_shift_eps].

    Dependencies.  Requires [S01_BaseRing] through [S15_TailFEPUp],
      [UpReqTempDefs], [UpReqEntropyDeficitTemp] of this development.

    References.  This development, the ConstructiveWorld-Main baseline
      module of the same name whose statement names are carried over
      verbatim (statement-face Set-carrier completion); the maximum
      entropy principle, classical in statistical mechanics.

    Constructivity.  Every statement closes with [Qed]; no proof is left
      open and no classical reasoning is used; statements are carried by
      the [Set] layer — [real_le] and [real_eq] are [Set]-valued with no
      [Prop] leakage on the statement face.

    Build.  [coqc -native-compiler no -q -Q . "" UpReqEntropyMaxTemp.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 000160bc]. *)

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
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.

(* ------------------------------------------------------------ *)
(* Inhabitant of the extended sum interface: the pointwise-to-   *)
(*   sum monotone lift for the concrete [real_list_sum] carrier  *)
(*   is already in the library ([S08_RealMainlineDPO]); this     *)
(*   corollary packages it as the concrete-carrier instance      *)
(*   satisfying the abstract interface slot.                     *)
(* ------------------------------------------------------------ *)
Corollary real_sum_le_list_carrier_instance :
  forall (X : Type) (f g : X -> Real) (l : list X),
    (forall w : X, real_le (f w) (g w)) ->
    real_le (real_list_sum X f l) (real_list_sum X g l).
Proof.
  exact (fun (X : Type) (f g : X -> Real) (l : list X)           (H : forall w : X, real_le (f w) (g w)) =>           real_list_sum_le X f g l H).
Qed.

(* ------------------------------------------------------------ *)
(* Auxiliary lemma A: [0 <= b] implies [a <= a + b] — the        *)
(*   [Real]-face counterpart of [le_plus_nonneg_r] on the [Id]   *)
(*   carrier, proved from [real_le_plus_compat] together with    *)
(*   [real_plus_zero] (the right-zero form [x + 0 == x]).        *)
(* ------------------------------------------------------------ *)
Lemma real_le_plus_nonneg_r :
  forall a b : Real,
    real_le real_zero b -> real_le a (real_plus a b).
Proof.
  intros a b Hb.
  apply (RealSetoid.real_le_id_l a (real_plus a real_zero) (real_plus a b)           (real_eq_sym (real_plus a real_zero) a (real_plus_zero a))).
  exact (real_le_plus_compat a a real_zero b (real_le_refl a) Hb).
Qed.

(* ------------------------------------------------------------ *)
(* Auxiliary lemma B: [a + ((b + (-a)) + eps) == b + eps], the   *)
(*   [eps]-shifted form of the cancellation behind               *)
(*   [minus_plus_cancel]; the rewrite chain runs associativity   *)
(*   (outer, inner), commutativity, associativity backwards,     *)
(*   [real_plus_opp], then [real_plus_zero].                     *)
(* ------------------------------------------------------------ *)
Lemma real_plus_neg_cancel_shift_eps :
  forall (a b eps : Real),
    real_eq (real_plus a (real_plus (real_plus b (real_opp a)) eps))
            (real_plus b eps).
Proof.
  intros a b eps.
  apply (real_eq_trans
           (real_plus a (real_plus (real_plus b (real_opp a)) eps))
           (real_plus (real_plus b real_zero) eps)
           (real_plus b eps)).
  - (* branch 1a: five rewrites reduce the left summand to [(b + 0) + eps]. *)
    apply (real_eq_trans
             (real_plus a (real_plus (real_plus b (real_opp a)) eps))
             (real_plus (real_plus a (real_plus b (real_opp a))) eps)
             (real_plus (real_plus b real_zero) eps)).
    + exact (real_plus_assoc a (real_plus b (real_opp a)) eps).
    + apply (real_eq_trans
               (real_plus (real_plus a (real_plus b (real_opp a))) eps)
               (real_plus (real_plus (real_plus a b) (real_opp a)) eps)
               (real_plus (real_plus b real_zero) eps)).
      * apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_plus a (real_plus b (real_opp a)))
                 (real_plus (real_plus a b) (real_opp a))
                 eps eps
                 (real_plus_assoc a b (real_opp a))
                 (real_eq_refl eps)).
      * apply (real_eq_trans
                 (real_plus (real_plus (real_plus a b) (real_opp a)) eps)
                 (real_plus (real_plus b (real_plus a (real_opp a))) eps)
                 (real_plus (real_plus b real_zero) eps)).
        -- apply (real_eq_trans
                    (real_plus (real_plus (real_plus a b) (real_opp a)) eps)
                    (real_plus (real_plus (real_plus b a) (real_opp a)) eps)
                    (real_plus (real_plus b (real_plus a (real_opp a))) eps)).
           ++ apply (RealSetoid.real_eq_plus_compat_adapt
                       (real_plus (real_plus a b) (real_opp a))
                       (real_plus (real_plus b a) (real_opp a))
                       eps eps
                       (RealSetoid.real_eq_plus_compat_adapt
                          (real_plus a b) (real_plus b a)
                          (real_opp a) (real_opp a)
                          (real_plus_comm a b)
                          (real_eq_refl (real_opp a)))
                       (real_eq_refl eps)).
           ++ apply (RealSetoid.real_eq_plus_compat_adapt
                       (real_plus (real_plus b a) (real_opp a))
                       (real_plus b (real_plus a (real_opp a)))
                       eps eps
                       (real_eq_sym (real_plus b (real_plus a (real_opp a)))
                                    (real_plus (real_plus b a) (real_opp a))
                                    (real_plus_assoc b a (real_opp a)))
                       (real_eq_refl eps)).
        -- apply (RealSetoid.real_eq_plus_compat_adapt
                    (real_plus b (real_plus a (real_opp a)))
                    (real_plus b real_zero)
                    eps eps
                    (RealSetoid.real_eq_plus_compat_adapt
                       b b
                       (real_plus a (real_opp a)) real_zero
                       (real_eq_refl b)
                       (real_plus_opp a))
                    (real_eq_refl eps)).
  - (* branch 1b: [(b + 0) + eps == b + eps] by the right-zero form [real_plus_zero]. *)
    apply (RealSetoid.real_eq_plus_compat_adapt
             (real_plus b real_zero) b
             eps eps
             (real_plus_zero b)
             (real_eq_refl eps)).
Qed.

(* ============================================================ *)
(* Section [RealEntropyMaxTemp]: the summation face, temperature,  *)
(*   and the energy field follow [UpReqTempDefs] with the same    *)
(*   names and order; the extension slot adds [real_sum_over_S_le] *)
(*   (declared right after [real_sum_over_S_ext], the interface    *)
(*   monotonicity position).                                       *)
(* ============================================================ *)
Section RealEntropyMaxTemp.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
(* Extended interface slot (the monotonicity position of the sum     *)
(*   interface); same-shape precedents exist in [G06_BForm] and      *)
(*   [UpRealLeB]; the concrete-carrier inhabitant is                 *)
(*   [real_list_sum_le] in [S08_RealMainlineDPO], packaged above.    *)
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable energy : S -> Real.

(* ------------------------------------------------------------ *)
(* Statement 1: KL divergence nonnegative up to [eps] — the       *)
(*   temperature-specialized [Real]-face counterpart of the       *)
(*   [Id]-carrier [gibbs_inequality]: for normalized, pointwise   *)
(*   positive [p] and [eps > 0], [0 <= KL(p || p_T) + eps].       *)
(*   Chain: the characterization lemma [real_KL_temp_kl_term_bridge],  *)
(*   the pointwise core [real_gibbs_core_eps], the lift to the    *)
(*   sum face through the extended interface, the left-hand-side  *)
(*   reduction ([sum(p - p_T) == 1 - 1 == 0]), and the error      *)
(*   reduction ([sum(p * eps) == eps]).                           *)
(* ------------------------------------------------------------ *)
Theorem real_KL_temp_ge_zero_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
           eps).
Proof.
  intros p Hp Hnp eps Hepspos.
  set (pT := real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy).
  set (HpT := real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                T T_pos energy).
  (* step 0, the bridge: [KL == sum(real_kl_term)], applied with all nine arguments explicit. *)
  assert (Hbridge : real_eq
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
           (real_sum_over_S (fun s : S =>
              real_kl_term (p s) (pT s) (Hp s) (HpT s)))).
  { exact (real_KL_temp_kl_term_bridge S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext T T_pos energy p Hp). }
  (* step 1, the pointwise core: [p - p_T <= real_kl_term + p * eps],     *)
  (*   applied explicitly; [real_kl_term] agrees definitionally with the  *)
  (*   first summand of the [real_gibbs_core_eps] right-hand side, as in  *)
  (*   [S08_RealMainlineDPO].                                             *)
  assert (Hpt : forall s : S,
           real_le (real_plus (p s) (real_opp (pT s)))
                   (real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                              (real_mult (p s) eps))).
  { intro s.
    exact (real_gibbs_core_eps (p s) (pT s) (Hp s) (HpT s) eps Hepspos). }
  (* step 2: the lift to the sum face through the extended interface slot. *)
  assert (Hsum : real_le
           (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
           (real_sum_over_S (fun s : S =>
              real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                        (real_mult (p s) eps)))).
  { exact (real_sum_over_S_le
             (fun s : S => real_plus (p s) (real_opp (pT s)))
             (fun s : S => real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                                     (real_mult (p s) eps))
             Hpt). }
  (* step 3, the left-hand side: [sum(p - p_T) == sum p + -(sum p_T) == 1 + (-1) == 0]. *)
  assert (HnormT : real_eq (real_sum_over_S pT) real_one).
  { exact (real_boltzmann_dist_temp_normalized S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext real_sum_over_S_linear T T_pos energy). }
  assert (Hzero : real_eq
           (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
           real_zero).
  { apply (real_eq_trans
             (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
             (real_plus (real_sum_over_S p)
                        (real_sum_over_S (fun s : S => real_opp (pT s))))
             real_zero).
    - exact (real_sum_over_S_add p (fun s : S => real_opp (pT s))).
    - apply (real_eq_trans
               (real_plus (real_sum_over_S p)
                          (real_sum_over_S (fun s : S => real_opp (pT s))))
               (real_plus real_one (real_opp real_one))
               real_zero).
      + apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_sum_over_S p) real_one
                 (real_sum_over_S (fun s : S => real_opp (pT s)))
                 (real_opp real_one)
                 Hnp
                 (real_eq_trans
                    (real_sum_over_S (fun s : S => real_opp (pT s)))
                    (real_opp (real_sum_over_S pT))
                    (real_opp real_one)
                    (real_sum_over_S_opp S real_sum_over_S real_sum_over_S_ext
                       real_sum_over_S_linear pT)
                    (RealSetoid.real_eq_opp_compat
                       (real_sum_over_S pT) real_one HnormT))).
      + exact (real_plus_opp real_one).
  }
  (* step 4, the error term: [sum(p * eps) == sum(eps * p) == eps * sum p == eps * 1 == eps]. *)
  assert (Heps : real_eq (real_sum_over_S (fun s : S => real_mult (p s) eps)) eps).
  { apply (real_eq_trans
             (real_sum_over_S (fun s : S => real_mult (p s) eps))
             (real_sum_over_S (fun s : S => real_mult eps (p s)))
             eps).
    - apply real_sum_over_S_ext.
      intro s. exact (real_mult_comm (p s) eps).
    - apply (real_eq_trans
               (real_sum_over_S (fun s : S => real_mult eps (p s)))
               (real_mult eps (real_sum_over_S p))
               eps).
      + exact (real_sum_over_S_linear eps p).
      + apply (real_eq_trans
                 (real_mult eps (real_sum_over_S p))
                 (real_mult eps real_one)
                 eps).
        * apply (RealSetoid.real_eq_mult_compat_adapt eps eps
                   (real_sum_over_S p) real_one
                   (real_eq_refl eps) Hnp).
        * exact (real_mult_one eps).
  }
  (* step 5, the right-hand side: [sum(kl + p * eps) == sum kl + eps]. *)
  assert (Hrhs : real_eq
           (real_sum_over_S (fun s : S =>
              real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                        (real_mult (p s) eps)))
           (real_plus
              (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
              eps)).
  { apply (real_eq_trans
             (real_sum_over_S (fun s : S =>
                real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                          (real_mult (p s) eps)))
             (real_plus
                (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
                (real_sum_over_S (fun s : S => real_mult (p s) eps)))
             (real_plus
                (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
                eps)).
    - exact (real_sum_over_S_add
               (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s))
               (fun s : S => real_mult (p s) eps)).
    - apply (RealSetoid.real_eq_plus_compat_adapt
               (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
               (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
               (real_sum_over_S (fun s : S => real_mult (p s) eps)) eps
               (real_eq_refl
                  (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s))))
               Heps).
  }
  (* step 6, the assembly: [0 <= sum(kl + p * eps)] gives [0 <= sum kl + eps] *)
  (*   and then [0 <= KL + eps], two setoid rewrite hops.                     *)
  exact (RealSetoid.real_le_id_r real_zero
           (real_plus
              (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
              eps)
           (real_plus
              (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
              eps)
           (RealSetoid.real_eq_plus_compat_adapt
              (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
              (real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp)
              eps eps
              (real_eq_sym _ _ Hbridge)
              (real_eq_refl eps))
           (RealSetoid.real_le_id_r real_zero
              (real_sum_over_S (fun s : S =>
                 real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                           (real_mult (p s) eps)))
              (real_plus
                 (real_sum_over_S (fun s : S => real_kl_term (p s) (pT s) (Hp s) (HpT s)))
                 eps)
              Hrhs
              (RealSetoid.real_le_id_l real_zero
                 (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
                 (real_sum_over_S (fun s : S =>
                    real_plus (real_kl_term (p s) (pT s) (Hp s) (HpT s))
                              (real_mult (p s) eps)))
                 (real_eq_sym
                    (real_sum_over_S (fun s : S => real_plus (p s) (real_opp (pT s))))
                    real_zero
                    Hzero)
                 Hsum))).
Qed.

(* ------------------------------------------------------------ *)
(* Statement 2 (the main statement): the per-[eps] form of        *)
(*   Theorem 4.6b — the argument-position counterpart of the     *)
(*   [Id]-carrier [max_entropy_is_boltzmann_temp] in              *)
(*   [S04_RealExpLogConv]: equal constrained energy               *)
(*   [E(p) == E_T] implies [S[p] <= S[p_T] + eps].  Chain: the    *)
(*   temperature form of the entropy deficit, then the per-[eps]  *)
(*   nonnegativity of KL (statement 1), closed by the [le] chain. *)
(* ------------------------------------------------------------ *)
Theorem real_max_entropy_is_boltzmann_temp_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    real_eq (real_sum_over_S (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
               T T_pos energy) ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (real_entropy_dist S real_sum_over_S p Hp)
              (real_plus
                 (real_entropy_dist S real_sum_over_S
                    (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                       T T_pos energy)
                    (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                       T T_pos energy))
                 eps).
Proof.
  intros p Hp Hnp Henergy eps Hepspos.
  set (Sp := real_entropy_dist S real_sum_over_S p Hp).
  set (Spt := real_entropy_dist S real_sum_over_S
                (real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved
                   T T_pos energy)
                (real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved
                   T T_pos energy)).
  set (KL := real_KL_temp S real_sum_over_S real_sum_pos_preserved T T_pos energy p Hp).
  (* step 1, the temperature form of the entropy deficit, applied with    *)
  (*   all thirteen arguments explicit; [real_minus_r] unfolds to         *)
  (*   [real_plus Spt (real_opp Sp)] definitionally.                      *)
  assert (Hdef : real_eq (real_plus Spt (real_opp Sp)) KL).
  { exact (real_entropy_deficit_kl_temp S real_sum_over_S real_sum_pos_preserved
             real_sum_over_S_ext real_sum_over_S_linear real_sum_over_S_add
             T T_pos energy p Hp Hnp Henergy). }
  (* step 2: per-[eps] nonnegativity of KL (statement 1). *)
  assert (Hkl : real_le real_zero (real_plus KL eps)).
  { exact (real_KL_temp_ge_zero_eps p Hp Hnp eps Hepspos). }
  (* step 3: transfer to the [Spt] summand via [real_le_id_r] with an equality compatibility limb. *)
  assert (Hstep : real_le real_zero (real_plus (real_plus Spt (real_opp Sp)) eps)).
  { apply (RealSetoid.real_le_id_r real_zero (real_plus KL eps)
             (real_plus (real_plus Spt (real_opp Sp)) eps)
             (RealSetoid.real_eq_plus_compat_adapt KL (real_plus Spt (real_opp Sp))
                eps eps
                (real_eq_sym (real_plus Spt (real_opp Sp)) KL Hdef)
                (real_eq_refl eps))).
    exact Hkl. }
  (* step 4: adding a nonnegative summand (auxiliary lemma A). *)
  assert (H1 : real_le Sp (real_plus Sp (real_plus (real_plus Spt (real_opp Sp)) eps))).
  { exact (real_le_plus_nonneg_r Sp (real_plus (real_plus Spt (real_opp Sp)) eps)
             Hstep). }
  (* step 5: finish with the equality limb of auxiliary lemma B and [real_le_id_r]. *)
  exact (RealSetoid.real_le_id_r Sp
           (real_plus Sp (real_plus (real_plus Spt (real_opp Sp)) eps))
           (real_plus Spt eps)
           (real_plus_neg_cancel_shift_eps Sp Spt eps)
           H1).
Qed.

End RealEntropyMaxTemp.
