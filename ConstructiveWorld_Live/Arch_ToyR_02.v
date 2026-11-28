(* ========================================================================= *)
(* Module   : Arch_ToyR_02                                                  *)
(* Mission. Six constructive families over the Set carrier Real of this     *)
(*  development: (1) the two-point strict-gap token world pa6ul: decidable  *)
(*  equality, nonemptiness and membership witnesses, the gap supply         *)
(*  z(x)+1 <= z(m) off the representative, closed uniform-window instance;  *)
(*  (2) list-length positivity and separation, closing a group mean; (3)    *)
(*  rate-layer contraction: delta <= 1 from minorization, iterated          *)
(*  contraction, strict branch, power-rate equality, Bishop decay; (4)      *)
(*  temperature-scaled Gibbs/Jeffreys bounds; (5) list-fold restatements    *)
(*  of summation slots; (6) realizations, order transport, realizer.        *)
(* Dependencies. S01_BaseRing through S15_TailFEPUp, AttnHardLimit218,      *)
(*  UpReqAttnUniformLimit, UpRealLeB, UpRealLeB2, UpRealLeB3, G07_KLWall,   *)
(*  KLWallClosed, UpTVDoeblin, UpReqKLStrictB, GibbsFamilyExt, UpReqSumD,   *)
(*  AttnDoeblin, IdSlotTranslate, fa51_sumpos_id, fa53_compat_abs,          *)
(*  fa56_id_carrier, fa56b_ext; Stdlib List, Arith.                         *)
(* References. S01_BaseRing (Set-layer Id and InT; real interface);         *)
(*  S02_CauchyComplete (Real a Set of regular Cauchy sequences, with        *)
(*  Set-valued lt/le/eq); UpReqAttnUniformLimit, KLWallClosed,              *)
(*  GibbsFamilyExt, UpRealLeB, UpRealLeB3, UpTVDoeblin (bound faces);       *)
(*  IdSlotTranslate and fa51/fa53/fa56 modules (slot realizers).            *)
(* Constructivity. All statement faces are Set-carried: identities in the   *)
(*  Set inductive Id; real_lt/real_le/real_eq/real_le_b Set-valued;         *)
(*  embedded existentials sigT over Set data only, so conclusions extract   *)
(*  with zero Prop faces. Lemma faces close with Qed (opaque proof terms);  *)
(*  all definitions and data faces are Defined. Proof bodies are            *)
(*  constructive; no classical logic anywhere.                              *)
(* Build. coqc -native-compiler no -q -Q <development root> ""              *)
(*  Arch_ToyR_02.v (workdir = this directory).                              *)
(* ========================================================================= *)

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
Require Import AttnHardLimit218.
Require Import UpReqAttnUniformLimit.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import G07_KLWall.
Require Import KLWallClosed.
Require Import UpTVDoeblin.
Require Import UpRealLeB3.
Require Import UpReqKLStrictB.
Require Import GibbsFamilyExt.
Require UpReqSumD.
Require Import AttnDoeblin.
Require Import IdSlotTranslate.
Require Import fa51_sumpos_id.
Require Import fa53_compat_abs.
Require Import fa56_id_carrier.
Require Import fa56b_ext.
From Stdlib Require Import List Arith.
Import ListNotations.

(* ================= Section 1. The pa6ul family ================= *)
(* A minimal two-valued token world with a genuine strict gap. *)

(* The vocabulary: the two-point list [true; false]. *)
Definition pa6ul_vocab : list bool := true :: false :: nil.

(* The two-branch logit map: branch real_one on the representative side,
   real_zero elsewhere (a genuinely gapped, nonconstant carrier map). *)
Definition pa6ul_z (x : bool) : Real :=
  match x with
  | true => real_one
  | false => real_zero
  end.

(* The strict-gap constant: gamma := real_one. *)
Definition pa6ul_gamma : Real := real_one.

(* Decidable equality on the two-point vocabulary: a four-way case split
   with the two cross cases discharged by constructor mismatch. *)
Definition pa6ul_eq_dec (a b : bool) : Or (Id a b) (Not (Id a b)).
Proof.
  destruct a as [ | ]; destruct b as [ | ].
  - exact (@inl _ _ (@id_refl bool true)).
  - exact (@inr (Id true false) (Not (Id true false))
             (fun H : Id true false =>
                match H in Id _ y
                  return (match y with false => Empty_set | _ => unit end) with
                | id_refl => tt
                end)).
  - exact (@inr (Id false true) (Not (Id false true))
             (fun H : Id false true =>
                match H in Id _ y
                  return (match y with true => Empty_set | _ => unit end) with
                | id_refl => tt
                end)).
  - exact (@inl _ _ (@id_refl bool false)).
Defined.

(* Nonemptiness certificate: [true; false] differs from the empty list. *)
Definition pa6ul_vocab_ne : Not (Id pa6ul_vocab nil) :=
  fun H : Id pa6ul_vocab nil =>
    match H in Id _ y
      return (match y with nil => Empty_set | _ => unit end) with
    | id_refl => tt
    end.

(* The representative m := true lies in the vocabulary. *)
Definition pa6ul_m_in : InT true pa6ul_vocab :=
  @InT_here bool true (false :: nil).

(* Gap supply: for every token off the representative,
   z(x) + gamma <= z(m). Case x = true contradicts the premise by
   constructor mismatch; case x = false gives 0 + 1 = 1, transported to
   the weak order by the equality-to-order face. *)
Lemma pa6ul_gap_le_supply : forall x : bool, Not (Id x true) ->
  real_le (real_plus (pa6ul_z x) pa6ul_gamma) (pa6ul_z true).
Proof.
  intros x Hx. destruct x as [ | ].
  - (* x = true contradicts Not (Id true true). *)
    exact (match Hx (@id_refl bool true) with end).
  - (* x = false: 0 + 1 == 1 + 0 == 1, then eq gives le. *)
    exact (RealSetoid.real_eq_le
             (real_plus (pa6ul_z false) pa6ul_gamma) (pa6ul_z true)
             (real_eq_trans (real_plus (pa6ul_z false) pa6ul_gamma)
                (real_plus real_one real_zero) real_one
                (real_plus_comm (pa6ul_z false) real_one)
                (real_plus_zero real_one))).
Qed.

(* Direct supply: gamma = 1 > 0. *)
Lemma pa6ul_gamma_pos_supply : real_lt real_zero pa6ul_gamma.
Proof.
  exact real_lt_zero_one.
Qed.

(* Strict-gap first cut: the uniform-window conclusion holds verbatim in
   this world, with both premises of the general theorem discharged by
   the two supply lemmas above. *)
Corollary pa6ul_strict_first_cut :
  forall eps : Real,
    real_lt real_zero eps ->
    sigT (fun T0 =>
      And (real_lt real_zero T0)
        (forall (T : Real) (Ht : real_lt real_zero T),
          real_lt T T0 ->
          real_le
            (real_list_sum bool
               (fun x : bool =>
                  real_abs (real_minus_r
                    (alm_uniform bool pa6ul_vocab pa6ul_eq_dec true
                       pa6ul_m_in x)
                    (S13_NLiveAudit.w_T bool pa6ul_vocab pa6ul_vocab_ne
                       pa6ul_z T Ht x)))
               pa6ul_vocab)
            eps)).
Proof.
  intros eps Heps.
  exact (alm_uniform_limit bool pa6ul_vocab pa6ul_vocab_ne pa6ul_eq_dec
           pa6ul_z true pa6ul_m_in pa6ul_gamma pa6ul_gamma_pos_supply
           pa6ul_gap_le_supply eps Heps).
Qed.

(* ================= Section 2. The nlp family ================= *)
(* Positivity and separation certificates for list lengths, through the
   nat-to-real embedding, over an arbitrary carrier. *)
Section NatLenPos.

(* Support 1: the nat embedding is nonnegative (induction on k). *)
Lemma nlp_ofnat_nonneg : forall k : nat,
  real_le real_zero (real_of_nat k).
Proof.
  intro k. induction k as [| k IH].
  - apply real_le_refl.
  - cbn [real_of_nat].
    apply (RealSetoid.real_le_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus real_one (real_of_nat k))).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_le_plus_compat.
      * apply real_le_from_lt_aux. apply real_lt_zero_one.
      * exact IH.
Qed.

(* Support 2: the successor case is strictly positive: 0 < 1 <= 1 + k. *)
Lemma nlp_ofnat_S_pos : forall k : nat,
  real_lt real_zero (real_of_nat (Datatypes.S k)).
Proof.
  intro k.
  cbn [real_of_nat].
  apply (real_lt_le_trans real_zero real_one
           (real_plus real_one (real_of_nat k)) real_lt_zero_one).
  apply real_le_plus_nonneg_r_aux.
  apply nlp_ofnat_nonneg.
Qed.

(* Main face: full coverage of an enumeration forces its length to be a
   strictly positive real. The induction runs on the membership
   derivation itself; both constructors are cons-shaped, so no nil
   branch enters the proof term. *)
Theorem nlp_len_pos_cover :
  forall (G : Set) (enum : list G),
    (forall i : G, InT i enum) ->
    forall g0 : G,
      real_lt real_zero (real_of_nat (Datatypes.length enum)).
Proof.
  intros G enum cover g0.
  induction (cover g0) as [l0 | y l0 Hin IH].
  - exact (nlp_ofnat_S_pos (Datatypes.length l0)).
  - exact (nlp_ofnat_S_pos (Datatypes.length l0)).
Qed.

(* Nonzero separation: a strictly positive real differs from zero (Set-
   layered negation). *)
Theorem nlp_len_nonzero :
  forall (G : Set) (enum : list G),
    real_lt real_zero (real_of_nat (Datatypes.length enum)) ->
    Not (real_eq real_zero (real_of_nat (Datatypes.length enum))).
Proof.
  intros G enum Hpos H0.
  exact (real_lt_irrefl real_zero
           (real_lt_eq_lt real_zero
              (real_of_nat (Datatypes.length enum)) real_zero Hpos
              (real_eq_sym real_zero
                 (real_of_nat (Datatypes.length enum)) H0))).
Qed.

(* Interface-determined group mean: inv(|G|) * sum r, with the positivity
   premise supplied by the coverage witness, so the assembly is fully
   closed. *)
Definition nlp_g01_mean2 (Grp2 : Set) (enum2 : list Grp2)
  (reward2 : Grp2 -> Real) (cover : forall i : Grp2, InT i enum2)
  (g0 : Grp2) : Real :=
  real_mult (real_inv_pos (real_of_nat (Datatypes.length enum2))
               (nlp_len_pos_cover Grp2 enum2 cover g0))
            (real_list_sum_g Grp2 reward2 enum2).

End NatLenPos.

(* ================= Section 3. The rta family ================= *)
(* Rate-layer contraction on the discrete-state machine whose state type
   is list Real. *)
Import ListNotations.

(* Part 1: a pointwise minorization plus two one-sided normalizations
   imply delta <= 1; the row-normalization premise is redundant at the
   interface level. *)
Theorem rta_delta_le_one_of_minorization :
  forall (states : list (list Real)) (K : list Real -> list Real -> Real)
         (u : list Real -> Real) (delta : Real),
  (forall i : list Real,
     real_eq (real_list_sum (list Real) (K i) states) real_one) ->
  real_eq (real_list_sum (list Real) u states) real_one ->
  (forall i j : list Real, real_le (real_mult delta (u j)) (K i j)) ->
  real_le delta real_one.
Proof.
  intros states K u delta HKrow Hunorm Hmin.
  (* Pointwise minorization (at i := nil; both premises hold for all i). *)
  pose proof (HKrow nil) as Hrow0.
  assert (Hpt : forall j : list Real,
           real_le (real_mult delta (u j)) (K nil j))
    by (intro j; apply Hmin).
  (* Sum monotonicity: sum (delta * u) <= sum (K nil). *)
  assert (Hle : real_le
                  (real_list_sum (list Real)
                     (fun j : list Real => real_mult delta (u j)) states)
                  (real_list_sum (list Real) (K nil) states)).
  { exact (@real_list_sum_le (list Real)
             (fun j : list Real => real_mult delta (u j))
             (K nil) states Hpt). }
  (* Left side: sum (delta * u) == delta * sum u == delta * 1 == delta. *)
  assert (Hlhs : real_eq
                   (real_list_sum (list Real)
                      (fun j : list Real => real_mult delta (u j)) states)
                   delta).
  { apply (real_eq_trans _
             (real_mult delta (real_list_sum (list Real) u states)) _).
    - exact (@real_list_sum_linear (list Real) delta u states).
    - apply (real_eq_trans _ (real_mult delta real_one) _).
      + apply (RealSetoid.real_eq_mult_compat delta
                 (real_list_sum (list Real) u states)
                 delta real_one (real_eq_refl delta) Hunorm).
      + exact (real_mult_one delta). }
  (* Assembly: delta <= sum (delta * u) <= sum (K nil) == 1. *)
  apply (real_le_trans delta
           (real_list_sum (list Real)
              (fun j : list Real => real_mult delta (u j)) states)
           real_one).
  - apply (RealSetoid.real_eq_le _ _).
    exact (real_eq_sym _ _ Hlhs).
  - apply (real_le_trans _
             (real_list_sum (list Real) (K nil) states) _).
    + exact Hle.
    + apply (RealSetoid.real_eq_le _ _). exact Hrow0.
Qed.

(* Part 2: the iterated contraction without the delta <= 1 premise: the
   n-step iterate shrinks by the residual-rate power, with delta <= 1
   derived in Part 1 from the minorization. *)
Theorem rta_iter_contraction_wo_le_one :
  forall (states : list (list Real)) (K : list Real -> list Real -> Real)
         (u : list Real -> Real) (delta : Real),
  (forall i : list Real,
     real_eq (real_list_sum (list Real) (K i) states) real_one) ->
  real_eq (real_list_sum (list Real) u states) real_one ->
  (forall i j : list Real, real_le (real_mult delta (u j)) (K i j)) ->
  (forall f : list Real -> Real,
     real_le (real_abs (real_list_sum (list Real) f states))
             (real_list_sum (list Real)
                (fun w : list Real => real_abs (f w)) states)) ->
  forall (n : nat) (mu nu : list Real -> Real),
  real_eq (real_list_sum (list Real) mu states) real_one ->
  real_eq (real_list_sum (list Real) nu states) real_one ->
  real_le (tv_doeblin states
             (tv_titer states K n mu) (tv_titer states K n nu))
          (real_mult (tv_rpow (tv_omd delta) n)
                     (tv_doeblin states mu nu)).
Proof.
  intros states K u delta HKrow Hunorm Hmin Labs n mu nu Hmu Hnu.
  exact (tv_doeblin_iter states K HKrow u Hunorm delta
           (rta_delta_le_one_of_minorization states K u delta
              HKrow Hunorm Hmin)
           Hmin Labs n mu nu Hmu Hnu).
Qed.

(* Part 3: the Real-carrier branch of the strict-shrink face: from
   0 <= eta < 1 one gets the positivity certificate 1 - eta > 0 (by the
   strict-shift chain) together with the Bishop contraction of the
   powers of 1 - eta. *)
Theorem rta_strict_branch_real : forall (eta : Real) (t t1 : nat),
  real_le real_zero eta -> real_lt eta real_one -> NatLe t t1 ->
  prod (real_lt real_zero (real_plus real_one (real_opp eta)))
       (real_le_b (powb_pow (real_plus real_one (real_opp eta)) t1)
                  (powb_pow (real_plus real_one (real_opp eta)) t)).
Proof.
  intros eta t t1 H0 Hlt Hle. split.
  - (* 0 < 1 - eta: shift eta < 1 and fold eta + (-eta) == 0. *)
    apply (RealSetoid.real_lt_id_l real_zero
             (real_plus eta (real_opp eta))
             (real_plus real_one (real_opp eta))).
    + exact (real_eq_sym (real_plus eta (real_opp eta)) real_zero
               (real_plus_opp eta)).
    + exact (real_lt_plus_compat_lt_le eta real_one (real_opp eta)
               (real_opp eta) Hlt (real_le_refl (real_opp eta))).
  - (* Bishop contraction of the powers, under 0 <= eta <= 1. *)
    exact (klc_closed_powb_mono eta t t1 H0
             (real_le_from_lt_aux eta real_one Hlt) Hle).
Qed.

(* Part 4: rate-layer bridge: the two power machines tv_rpow and
   powb_pow agree pointwise (equality of two structurally identical
   folds). *)
Lemma rta_rpow_powb_eq : forall (a : Real) (n : nat),
  real_eq (tv_rpow a n) (powb_pow a n).
Proof.
  intros a n. induction n as [| n IH].
  - cbn [tv_rpow powb_pow]. apply real_eq_refl.
  - cbn [tv_rpow powb_pow].
    apply (RealSetoid.real_eq_mult_compat a (tv_rpow a n)
             a (powb_pow a n) (real_eq_refl a) IH).
Qed.

(* Part 5: Bishop-monotone decay of the residual-rate powers: from
   0 <= delta <= 1 the rate (1 - delta)^m is bounded by (1 - delta)^n
   for n <= m, carried through the Part 4 bridge. *)
Theorem rta_omd_powb_mono_b : forall (delta : Real) (n m : nat),
  real_le real_zero delta -> real_le delta real_one -> NatLe n m ->
  real_le_b (tv_rpow (tv_omd delta) m) (tv_rpow (tv_omd delta) n).
Proof.
  intros delta n m H0 H1 Hle.
  pose proof (klc_closed_powb_mono delta n m H0 H1 Hle) as Hklc.
  unfold real_le_b in *. intros eps Heps.
  apply (RealSetoid.real_lt_compat
           (powb_pow (real_plus real_one (real_opp delta)) m)
           (tv_rpow (tv_omd delta) m)
           (real_plus (powb_pow (real_plus real_one (real_opp delta)) n) eps)
           (real_plus (tv_rpow (tv_omd delta) n) eps)).
  - apply real_eq_sym.
    exact (rta_rpow_powb_eq (real_plus real_one (real_opp delta)) m).
  - apply (RealSetoid.real_eq_plus_compat
             (powb_pow (real_plus real_one (real_opp delta)) n) eps
             (tv_rpow (tv_omd delta) n) eps
             (real_eq_sym (tv_rpow (tv_omd delta) n)
                (powb_pow (real_plus real_one (real_opp delta)) n)
                (rta_rpow_powb_eq (real_plus real_one (real_opp delta)) n))
             (real_eq_refl eps)).
  - exact (Hklc eps Heps).
Qed.

(* ================= Section 4. The uagfe family ================= *)
(* Temperature-scaled Gibbs and Jeffreys bounds in Bishop form. *)
Import ListNotations.

(* Part 1: unit temperature beta = 1: pointwise Bishop upper bound. *)
Lemma uagfe_gibbs_temp_one_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_le_b (real_mult real_one (real_plus p (real_opp q)))
            (real_mult real_one (real_kl_term p q Hp Hq)).
Proof.
  intros p q Hp Hq.
  exact (gfe_gibbs_core_temp_B p q real_one Hp Hq real_lt_zero_one).
Qed.

(* Part 2: doubled temperature beta = 2: the pointwise eps-form. *)
Lemma uagfe_gibbs_temp_two_eps : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (eps : Real) (Heps : real_lt real_zero eps),
  real_le (real_mult (real_plus real_one real_one) (real_plus p (real_opp q)))
          (real_plus
             (real_mult (real_plus real_one real_one)
                        (real_kl_term p q Hp Hq))
             (real_mult (real_plus real_one real_one) (real_mult p eps))).
Proof.
  intros p q Hp Hq eps Heps.
  exact (gfe_gibbs_core_temp_eps p q (real_plus real_one real_one) Hp Hq
           (gfe_le_of_lt (real_plus real_one real_one)
              (real_plus_positive real_one real_one
                 real_lt_zero_one real_lt_zero_one))
           eps Heps).
Qed.

(* Part 3: composite two-level temperature flat form: positive scaling
   preserves Bishop bounds. *)
Lemma uagfe_le_b_mult_pos_two_temp_flat :
  forall (x y b1 b2 : Real),
  real_lt real_zero b1 -> real_lt real_zero b2 ->
  real_le_b x y ->
  real_le_b (real_mult (real_mult b1 b2) x)
            (real_mult (real_mult b1 b2) y).
Proof.
  intros x y b1 b2 Hb1 Hb2 Hxy.
  apply (gfe_le_b_eq_r (real_mult (real_mult b1 b2) x)
           (real_mult b1 (real_mult b2 y))
           (real_mult (real_mult b1 b2) y)).
  - apply (leb3_le_b_eq_l (real_mult b1 (real_mult b2 x))
             (real_mult (real_mult b1 b2) x)
             (real_mult b1 (real_mult b2 y))).
    + exact (real_mult_assoc b1 b2 x).
    + exact (gfe_le_b_mult_pos (real_mult b2 x) (real_mult b2 y) b1 Hb1
               (gfe_le_b_mult_pos x y b2 Hb2 Hxy)).
  - exact (real_mult_assoc b1 b2 y).
Qed.

(* Part 4: symmetric Jeffreys bound at pointwise temperature:
   0 <=_B b * (kl(p,q) + kl(q,p)). *)
Theorem uagfe_jeffreys_sym_temp_B : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_plus (real_kl_term p q Hp Hq)
                            (real_kl_term q p Hq Hp))).
Proof.
  intros p q b Hp Hq Hb.
  apply (leb3_le_b_eq_l (real_mult b real_zero) real_zero
           (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                   (real_kl_term q p Hq Hp)))).
  - exact (real_mult_zero b).
  - exact (gfe_le_b_mult_pos real_zero
             (real_plus (real_kl_term p q Hp Hq)
                        (real_kl_term q p Hq Hp))
             b Hb (gfe_jeffreys_sym_B p q Hp Hq)).
Qed.

(* Part 5: symmetric Jeffreys bound over finite sums:
   0 <=_B b * sum_s (kl(p s,q s) + kl(q s,p s)). *)
Theorem uagfe_jeffreys_sym_list_temp_B :
  forall (X : Type) (l : list X) (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (b : Real) (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_list_sum X
        (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                (real_kl_term (q s) (p s) (Hq s) (Hp s))) l)).
Proof.
  intros X l p q Hp Hq b Hb.
  apply (leb3_le_b_eq_l (real_mult b real_zero) real_zero
           (real_mult b (real_list_sum X
              (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                      (real_kl_term (q s) (p s) (Hq s) (Hp s)))
              l))).
  - exact (real_mult_zero b).
  - exact (gfe_le_b_mult_pos real_zero
             (real_list_sum X
                (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                        (real_kl_term (q s) (p s) (Hq s) (Hp s)))
                l)
             b Hb (gfe_jeffreys_sym_list_B X l p q Hp Hq)).
Qed.

(* ================= Section 5. The sef family ================= *)
(* List-fold restatements of the abstract summation slots on an enhanced
   real interface with a state space and a summation structure. *)
Import ListNotations.
Section SumEqListFeed.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Let le := @le RI.

(* Part 1: restated row bounds, attention machine. The abstract slot
   sum_eq_list is instantiated by the list-fold witness: the lower bound
   transports by right identity substitution, the upper bound by left
   identity substitution, and the normalized uniform row by transitivity
   through the slot. *)
Lemma sef_attn_zrow_ge : forall (en : list S) (g : S -> R) (a : R),
  le a (AttnDoeblin.bs_list_sum g en) -> le a (idt_sumf en g).
Proof.
  intros en g a Hle.
  exact (le_id_r a (AttnDoeblin.bs_list_sum g en) (idt_sumf en g)
           (id_sym (idt_slot_attdoeblin en g)) Hle).
Qed.

Lemma sef_attn_zrow_le : forall (en : list S) (g : S -> R) (b : R),
  le (AttnDoeblin.bs_list_sum g en) b -> le (idt_sumf en g) b.
Proof.
  intros en g b Hle.
  exact (le_id_l (idt_sumf en g) (AttnDoeblin.bs_list_sum g en) b
           (idt_slot_attdoeblin en g) Hle).
Qed.

Lemma sef_attn_unif_norm : forall (en : list S) (g : S -> R) (b : R),
  Id (AttnDoeblin.bs_list_sum g en) b -> Id (idt_sumf en g) b.
Proof.
  intros en g b Hid.
  exact (id_trans (idt_slot_attdoeblin en g) Hid).
Qed.

(* Part 2: the same three restatements for the audit machine, whose fold
   has the same cons shape. *)
Lemma sef_s13_zrow_ge : forall (en : list S) (g : S -> R) (a : R),
  le a (S13_NLiveAudit.bs_list_sum g en) -> le a (idt_sumf en g).
Proof.
  intros en g a Hle.
  exact (le_id_r a (S13_NLiveAudit.bs_list_sum g en) (idt_sumf en g)
           (id_sym (idt_slot_s13 en g)) Hle).
Qed.

Lemma sef_s13_zrow_le : forall (en : list S) (g : S -> R) (b : R),
  le (S13_NLiveAudit.bs_list_sum g en) b -> le (idt_sumf en g) b.
Proof.
  intros en g b Hle.
  exact (le_id_l (idt_sumf en g) (S13_NLiveAudit.bs_list_sum g en) b
           (idt_slot_s13 en g) Hle).
Qed.

Lemma sef_s13_unif_norm : forall (en : list S) (g : S -> R) (b : R),
  Id (S13_NLiveAudit.bs_list_sum g en) b -> Id (idt_sumf en g) b.
Proof.
  intros en g b Hid.
  exact (id_trans (idt_slot_s13 en g) Hid).
Qed.

(* Part 3: the slot statements as explicit arguments of the general
   forms, definitional constructions filling the two argument positions. *)
Definition sef_g01_slot_arg (en : list S)
  : forall g : S -> R, Id (idt_sumf en g) (AttnDoeblin.bs_list_sum g en) :=
  idt_slot_g01 en.

Definition sef_s15_slot_arg (en : list S)
  : forall g : S -> R, Id (idt_sumf en g) (S13_NLiveAudit.bs_list_sum g en) :=
  idt_slot_s15 en.

(* Pointwise agreement of the filler with the restated machines (eta
   level). *)
Lemma sef_g01_slot_arg_pt : forall (en : list S) (g : S -> R),
  Id (idt_sumf en g) (AttnDoeblin.bs_list_sum g en).
Proof.
  intros en g.
  exact (sef_g01_slot_arg en g).
Qed.

Lemma sef_s15_slot_arg_pt : forall (en : list S) (g : S -> R),
  Id (idt_sumf en g) (S13_NLiveAudit.bs_list_sum g en).
Proof.
  intros en g.
  exact (sef_s15_slot_arg en g).
Qed.

End SumEqListFeed.

(* ================= Section 6. The fa57 family ================= *)
(* Finite-sum carrier realizations over the interface record with a
   decidable order extension. *)
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Fa57Ext.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
(* The one-sided strict-shift family needs the decidable-order
   extension; it enters only the two transport lemmas below. *)
Context {DO : DecidableOrder RI}.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.

(* Main realization: on any nonempty enumeration the list fold is
   positivity-preserving, congruent pointwise, and linear in constant
   left factors. *)
Theorem fa57_sum_carrier_realizes :
  forall (X : Set) (enum : list X),
    Not (Id enum nil) ->
    sigT (fun sumf : (X -> R) -> R =>
            And (forall f : X -> R,
                   (forall x : X, lt zero (f x)) -> lt zero (sumf f))
                (And (forall f g : X -> R,
                        (forall x : X, Id (f x) (g x)) -> Id (sumf f) (sumf g))
                     (forall (a : R) (f : X -> R),
                        Id (sumf (fun x => mult a (f x)))
                           (mult a (sumf f))))).
Proof.
  intros X enum Hne.
  exact (existT _
                (fun f => fa51_sumd X f enum)
                ((fun f Hf => fa51_sumd_nonnil_pos X f enum Hne Hf),
                 ((fun f g Hpt => fa56b_sumd_cong X f g enum Hpt),
                  (fun a f => fa56_sumd_mult_const X a f enum)))).
Qed.

(* Right-factor linearity (the (fun x => mult (f x) a) variant): swap,
   constant factor, and commutativity chained through transitivity. *)
Lemma fa57_sumd_mult_const_r :
  forall (X : Set) (a : R) (f : X -> R) (l : list X),
    Id (fa51_sumd X (fun x => mult (f x) a) l)
       (mult (fa51_sumd X f l) a).
Proof.
  intros X a f l.
  exact (id_trans (fa56b_sumd_cong X (fun x => mult (f x) a)
                                    (fun x => mult a (f x)) l
                                    (fun x => mult_comm (f x) a))
                  (id_trans (fa56_sumd_mult_const X a f l)
                            (mult_comm a (fa51_sumd X f l)))).
Qed.

(* Slot statement: lt a b implies lt zero (minus b a), where minus is
   definitional addition of the opposite. Forward direction: relocate
   a + (-a) == 0 and apply the one-sided strict shift. *)
Lemma fa57_lt_minus_nonneg :
  forall a b : R, lt a b -> lt zero (minus b a).
Proof.
  intros a b Hab.
  exact (lt_id_l zero (plus a (opp a)) (plus b (opp a))
           (id_sym (plus_opp a))
           (@fa53_lt_plus_translate_r RI DO a b (opp a) Hab)).
Qed.

(* Converse direction: shift zero back and fold the associativity,
   opposite and zero identities. *)
Lemma fa57_minus_lt_strict :
  forall a b : R, lt zero (minus b a) -> lt a b.
Proof.
  intros a b H.
  apply (lt_id_l a (plus zero a) b
           (id_trans (id_sym (plus_zero a)) (id_sym (plus_comm zero a)))).
  apply (lt_id_r (plus zero a) (plus (plus b (opp a)) a) b).
  - exact (id_trans (id_sym (plus_assoc b (opp a) a))
                    (id_trans (id_cong (fun w => plus b w)
                                       (id_trans (plus_comm (opp a) a)
                                                 (plus_opp a)))
                              (plus_zero b))).
  - exact (@fa53_lt_plus_translate_r RI DO zero (plus b (opp a)) a H).
Qed.

(* The nat embedding of the interface record: recursion on plus one, with
   positivity at successors by the interface positivity fields. *)
Fixpoint fa57_nat_to_R (k : nat) : R :=
  match k with
  | O => zero
  | Datatypes.S m => plus one (fa57_nat_to_R m)
  end.

Lemma fa57_nat_to_R_pos :
  forall k : nat, lt zero (fa57_nat_to_R (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - exact (lt_id_r zero one (plus one zero) (id_sym (plus_zero one)) one_pos).
  - exact (plus_positive one (fa57_nat_to_R (Datatypes.S k)) one_pos IH).
Qed.

(* Coverage forces a positive group size, for the interface embedding:
   the induction runs on the membership derivation; both constructors
   are cons-shaped, so no nil branch enters the proof term. *)
Theorem fa57_grpo_G_pos :
  forall (Group : Set) (group_enum : list Group),
    (forall i : Group, InT i group_enum) ->
    forall g0 : Group,
      lt zero (fa57_nat_to_R (Datatypes.length group_enum)).
Proof.
  intros Group group_enum cover g0.
  induction (cover g0) as [l0 | y l0 Hin IH].
  - exact (fa57_nat_to_R_pos (Datatypes.length l0)).
  - exact (fa57_nat_to_R_pos (Datatypes.length l0)).
Qed.

(* The two-point uniform projection family: carrier I := bool, index
   [true; false], constant half mass, full witness. The halving chain:
   half + half == half * 1 + half * 1 == half * two == one, by the
   distributive, multiplicative-unit and inverse four-step chain. *)

Definition fa57_two : R := plus one one.

Lemma fa57_two_pos : lt zero fa57_two.
Proof.
  exact (plus_positive one one one_pos one_pos).
Qed.

Definition fa57_half : R := inv_pos fa57_two fa57_two_pos.

Lemma fa57_half_pos : lt zero fa57_half.
Proof.
  exact (inv_pos_pos fa57_two fa57_two_pos).
Qed.

Lemma fa57_half_plus_half : Id (plus fa57_half fa57_half) one.
Proof.
  exact (id_trans (id_cong2 plus (id_sym (mult_one fa57_half))
                                (id_sym (mult_one fa57_half)))
                  (id_trans (id_sym (distrib fa57_half one one))
                            (id_trans (mult_comm fa57_half fa57_two)
                                      (inv_pos_correct fa57_two
                                         fa57_two_pos)))).
Qed.

(* The seven-slot realization package for the two-point uniform family:
   normalization, pointwise positivity, and the witness triple; the
   structural slots are discharged by the type face itself. *)
Theorem fa57_W2p_uniform_two_realized :
  And (Id (fa51_sumd bool (fun _ : bool => fa57_half) [true; false]) one)
      (And (forall i : bool, lt zero ((fun _ : bool => fa57_half) i))
           (sigT (fun i : bool =>
                    And (Id ((fun _ : bool => true) i) true)
                        (InT i [true; false])))).
Proof.
  split.
  - exact (id_trans (id_cong (fun w : R => plus fa57_half w)
                             (plus_zero fa57_half))
                    fa57_half_plus_half).
  - split.
    + exact (fun _ => fa57_half_pos).
    + exact (existT (fun i : bool =>
                       And (Id ((fun _ : bool => true) i) true)
                           (InT i [true; false]))
                    true (id_refl, @InT_here bool true [false])).
Qed.

(* The alignment partition function as an honest realizer: the argument
   Z together with its positivity certificate, both supplied by the
   finite-sum realizer, with the reference-positivity and nonemptiness
   premises explicit. *)
Definition fa57_dpolip_Z_realizer :
  forall (X : Set) (enum : list X) (reward : X -> R) (beta : R)
         (beta_pos : lt zero beta) (pi_ref : X -> R),
    (forall s : X, lt zero (pi_ref s)) ->
    Not (Id enum nil) ->
    sigT (fun Z : R => And (Id Z (fa51_Z_align X enum reward beta beta_pos pi_ref))
                           (lt zero Z)).
Proof.
  intros X enum reward beta beta_pos pi_ref Href Hne.
  exact (existT _
                (fa51_Z_align X enum reward beta beta_pos pi_ref)
                (id_refl,
                 fa51_Z_align_pos X enum reward beta beta_pos pi_ref Href Hne)).
Qed.

End Fa57Ext.

(* ================= Assumption audit ================= *)
(* One Print Assumptions line per theorem of this piece, in order of
   appearance. *)

Print Assumptions pa6ul_gap_le_supply.
Print Assumptions pa6ul_gamma_pos_supply.
Print Assumptions pa6ul_strict_first_cut.
Print Assumptions nlp_ofnat_nonneg.
Print Assumptions nlp_ofnat_S_pos.
Print Assumptions nlp_len_pos_cover.
Print Assumptions nlp_len_nonzero.
Print Assumptions nlp_g01_mean2.
Print Assumptions rta_delta_le_one_of_minorization.
Print Assumptions rta_iter_contraction_wo_le_one.
Print Assumptions rta_strict_branch_real.
Print Assumptions rta_rpow_powb_eq.
Print Assumptions rta_omd_powb_mono_b.
Print Assumptions uagfe_gibbs_temp_one_B.
Print Assumptions uagfe_gibbs_temp_two_eps.
Print Assumptions uagfe_le_b_mult_pos_two_temp_flat.
Print Assumptions uagfe_jeffreys_sym_temp_B.
Print Assumptions uagfe_jeffreys_sym_list_temp_B.
Print Assumptions sef_attn_zrow_ge.
Print Assumptions sef_attn_zrow_le.
Print Assumptions sef_attn_unif_norm.
Print Assumptions sef_s13_zrow_ge.
Print Assumptions sef_s13_zrow_le.
Print Assumptions sef_s13_unif_norm.
Print Assumptions sef_g01_slot_arg.
Print Assumptions sef_g01_slot_arg_pt.
Print Assumptions sef_s15_slot_arg.
Print Assumptions sef_s15_slot_arg_pt.
Print Assumptions fa57_sum_carrier_realizes.
Print Assumptions fa57_sumd_mult_const_r.
Print Assumptions fa57_lt_minus_nonneg.
Print Assumptions fa57_minus_lt_strict.
Print Assumptions fa57_nat_to_R_pos.
Print Assumptions fa57_grpo_G_pos.
Print Assumptions fa57_two_pos.
Print Assumptions fa57_half_pos.
Print Assumptions fa57_half_plus_half.
Print Assumptions fa57_W2p_uniform_two_realized.
Print Assumptions fa57_dpolip_Z_realizer.
