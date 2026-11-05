(* ConstructiveWorld-Set -- Real-layer top-K total-variation chain over the Boltzmann partition interface. *)

(** * UpReqTopKTVChain: Theorem 7.6 [topk_tv_identity_strict] on Set carriers.

    Mission.  Formalizes the top-K total-variation identity for a Boltzmann
      distribution against its top-K renormalization: the kept and tail
      partition masses [rtk_kept_partition] and [rtk_tail_mass], their
      conservation [rtk_kept_plus_tail_full], the sign auxiliary family
      [rtk_inv_one_cc], [rtk_opp_zero_cc], [rtk_lt_minus_cc], [rtk_abs_neg_cc],
      [rtk_minus_zero_cc], the pointwise and sum stages [rtk_tv_pointwise],
      [rtk_sum_decomp], [rtk_sum_collapse], and the main statement
      [rtk_tv_identity_strict] (the distance equals tail mass over Z).

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp] of this development.

    References.  This development, UpReqTopKTVChain.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqTopKTVChain.v] compiles cleanly
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

(* ============================================================ *)
(* Section RealTopKTVChain: mirrors the Id module AttentionGibbsBridge (top-K part) *)
(* ============================================================ *)
Section RealTopKTVChain.

(* world: the state type (a copy of the Context slot; the Id layer takes S *)
(*   through RealInterface, *)
(*   the Real layer takes the Type slot directly -- the three summation *)
(*   carriers stay abstract in the same way). *)
Variable S : Type.


Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) ->
  real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) ->
  real_le (real_sum_over_S f) (real_sum_over_S g).

(* ---- Boltzmann carriers (a faithful copy of the Id block at 3843; the *)
(*   same shape as the req side, lines 537-541) ---- *)
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable energy : S -> Real.

Definition rtk_boltzmann_factor (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)).

Definition rtk_Z_thermo : Real := real_sum_over_S rtk_boltzmann_factor.

Variable rtk_Z_thermo_pos : real_lt real_zero rtk_Z_thermo.

(* ---- defining carriers (family copy of the Id block at 5541; the same *)
(*   axis as the req-side tail_mass_of_r) -- *)
(* top-K tail mass (the Id topk_tail_mass: the mass of the evicted states) *)
Definition rtk_tail_mass
  (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : Real :=
  real_sum_over_S (fun s : S => if kd s then real_zero else rtk_boltzmann_factor s).

(* top-K kept mass (the Id topk_kept_partition: the renormalization denominator) *)
Definition rtk_kept_partition
  (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : Real :=
  real_sum_over_S (fun s : S => if kd s then rtk_boltzmann_factor s else real_zero).

(* ---- item 1: positivity of the Boltzmann factor at a single state ---- *)
(* the Id proof quotes exp_neg_pos directly; the Real layer has the same *)
(*   shape: real_exp_neg_pos provides the step. *)
Lemma rtk_boltzmann_factor_pos_attn :
  forall s : S, real_lt real_zero (rtk_boltzmann_factor s).
Proof.
  intro s.
  unfold rtk_boltzmann_factor.
  apply real_exp_neg_pos.
Qed.

(* ---- item 2: the if-kept summand is nonnegative (> 0 when kept, == 0 *)
(*   otherwise) ---- *)
Lemma rtk_kept_term_nonneg :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s : S),
    real_le real_zero (if kd s then rtk_boltzmann_factor s else real_zero).
Proof.
  intros k kd s. destruct (kd s) as [Hk | Hnk].
  - apply (RealSetoid.real_lt_le_iff_req real_zero (rtk_boltzmann_factor s)).
    left. apply rtk_boltzmann_factor_pos_attn.
  - apply real_le_refl.
Qed.

(* ---- item 3: the if-kept summand is at most the factor (reflexive when *)
(*   kept, 0 < b otherwise) ---- *)
Lemma rtk_kept_term_le_factor :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s : S),
    real_le (if kd s then rtk_boltzmann_factor s else real_zero)
            (rtk_boltzmann_factor s).
Proof.
  intros k kd s. destruct (kd s) as [Hk | Hnk].
  - apply real_le_refl.
  - apply (RealSetoid.real_lt_le_iff_req real_zero (rtk_boltzmann_factor s)).
    left. apply rtk_boltzmann_factor_pos_attn.
Qed.

(* ---- item 4: conservation kept + tail == Z_thermo ---- *)
(* Id proof chain: pointwise plus cancellation (plus_zero in both directions), *)
(*   then sum extensionality, then additivity of the sum; *)
(*   the Real layer replays the same chain (a real_eq_trans chain with the *)
(*   extensionality and additivity legs). *)
Lemma rtk_kept_plus_tail_full :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))),
    real_eq (real_plus (rtk_kept_partition k kd) (rtk_tail_mass k kd))
            rtk_Z_thermo.
Proof.
  intros k kd.
  unfold rtk_kept_partition, rtk_tail_mass, rtk_Z_thermo.
  (* pointwise: kept term + tail term == the factor (kept: b + 0 == b; *)
  (*   evicted: 0 + b == b) *)
  assert (Hpt : forall s : S,
           real_eq (real_plus (if kd s then rtk_boltzmann_factor s else real_zero)
                              (if kd s then real_zero else rtk_boltzmann_factor s))
                   (rtk_boltzmann_factor s)).
  { intro s. destruct (kd s) as [Hk | Hnk].
    - exact (real_plus_zero (rtk_boltzmann_factor s)).
    - exact (real_eq_trans _ _ _
                (real_plus_comm real_zero (rtk_boltzmann_factor s))
                (real_plus_zero (rtk_boltzmann_factor s))). }
  assert (Hext : real_eq
                   (real_sum_over_S (fun s : S =>
                      real_plus (if kd s then rtk_boltzmann_factor s else real_zero)
                                (if kd s then real_zero else rtk_boltzmann_factor s)))
                   (real_sum_over_S (fun s : S => rtk_boltzmann_factor s)))
    by exact (real_sum_over_S_ext _ _ Hpt).
  assert (Hadd : real_eq
                   (real_sum_over_S (fun s : S =>
                      real_plus (if kd s then rtk_boltzmann_factor s else real_zero)
                                (if kd s then real_zero else rtk_boltzmann_factor s)))
                   (real_plus (real_sum_over_S (fun s : S =>
                                  if kd s then rtk_boltzmann_factor s else real_zero))
                              (real_sum_over_S (fun s : S =>
                                  if kd s then real_zero else rtk_boltzmann_factor s))))
    by exact (real_sum_over_S_add _ _).
  exact (real_eq_trans _ _ _ (real_eq_sym _ _ Hadd) Hext).
Qed.

(* ---- item 5: kept <= Z_thermo (a sub-sum is at most the full sum) ---- *)
Lemma rtk_kept_le_Zthermo :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))),
    real_le (rtk_kept_partition k kd) rtk_Z_thermo.
Proof.
  intros k kd.
  unfold rtk_kept_partition, rtk_Z_thermo.
  apply real_sum_over_S_le.
  intro s.
  apply rtk_kept_term_le_factor.
Qed.

(* ---- item 6: inversion reverses the order, kept <= Z implies 1/Z <= 1/kept ---- *)
(* key fact: real_inv_pos_le_compat (S07 line 6775; the same slot as the Id *)
(*   inv_pos_le_compat). *)
Lemma rtk_inv_Z_le_inv_kept :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : real_lt real_zero (rtk_kept_partition k kd)),
    real_le (real_inv_pos rtk_Z_thermo rtk_Z_thermo_pos)
            (real_inv_pos (rtk_kept_partition k kd) Hkpos).
Proof.
  intros k kd Hkpos.
  exact (real_inv_pos_le_compat (rtk_kept_partition k kd) rtk_Z_thermo
           Hkpos rtk_Z_thermo_pos (rtk_kept_le_Zthermo k kd)).
Qed.

(* ============================================================ *)
(* the _cc sign auxiliary items (Id block at 5647; decoupled from the top-K *)
(*   carriers, pure Real algebra) *)
(* ============================================================ *)

(* ---- item 7: inv one == one ---- *)
(* the Id proof goes through mult_one symmetry, then commutativity, then *)
(*   inv_pos_correct; the Real layer replays the same chain. *)
Lemma rtk_inv_one_cc :
  real_eq (real_inv_pos real_one real_lt_zero_one) real_one.
Proof.
  apply (real_eq_trans (real_inv_pos real_one real_lt_zero_one)
                       (real_mult (real_inv_pos real_one real_lt_zero_one) real_one)
                       real_one).
  - exact (real_eq_sym _ _ (real_mult_one (real_inv_pos real_one real_lt_zero_one))).
  - apply (real_eq_trans (real_mult (real_inv_pos real_one real_lt_zero_one) real_one)
                         (real_mult real_one (real_inv_pos real_one real_lt_zero_one))
                         real_one).
    + exact (real_mult_comm (real_inv_pos real_one real_lt_zero_one) real_one).
    + exact (real_inv_pos_correct real_one real_lt_zero_one).
Qed.

(* ---- item 8: opp zero == zero ---- *)
(* the Id layer proves this inside its own section to avoid a forward reference; *)
(*   the Real base fact real_opp_zero (S08 line 386) is already on disk, *)
(*   so we quote it directly (verified reference, no rebuilding; the audit is *)
(*   Closed). *)
Lemma rtk_opp_zero_cc : real_eq (real_opp real_zero) real_zero.
Proof.
  exact real_opp_zero.
Qed.

(* ---- item 9: a < b implies a - b < 0 ---- *)
(* Id chain: unfold minus, then lt_id_r (b + opp b == 0), then mixed plus *)
(*   compatibility; *)
(*   the Real layer unfolds real_minus_r, then uses real_lt_id_r with the *)
(*   real_plus_opp leg *)
(*   and the mixed compatibility real_lt_plus_compat_lt_le (S07 line 6109): *)
(*   the req side carries it as an explicit premise *)
(*   req_lt_plus_compat_lt_le_h because the req interface has no mixed field; *)
(*   the Real layer uses the fact directly, so that premise dissolves *)
(*   naturally. *)
Lemma rtk_lt_minus_cc :
  forall a b : Real, real_lt a b -> real_lt (real_minus_r a b) real_zero.
Proof.
  intros a b Hab.
  unfold real_minus_r.
  apply (RealSetoid.real_lt_id_r (real_plus a (real_opp b))                                 (real_plus b (real_opp b)) real_zero                                 (real_plus_opp b)).
  exact (real_lt_plus_compat_lt_le a b (real_opp b) (real_opp b)             Hab (real_le_refl (real_opp b))).
Qed.

(* ---- item 10: a < 0 implies |a| == -a ---- *)
(* Id chain: symmetry by abs_opp, then abs_pos (the negative branch), then *)
(*   order reversal under opp; *)
(*   the Real layer uses the symmetry leg real_abs_opp, then real_abs_pos_req *)
(*   (the negative-sign elimination, *)
(*   applied to -a), then real_opp_lt_compat to reverse *)
(*   (a < 0 gives 0 < -a, *)
(*   rewriting through real_opp_zero in real_lt_id_r). *)
Lemma rtk_abs_neg_cc :
  forall a : Real, real_lt a real_zero -> real_eq (real_abs a) (real_opp a).
Proof.
  intros a Ha.
  apply (real_eq_trans (real_abs a) (real_abs (real_opp a)) (real_opp a)).
  - exact (real_eq_sym _ _ (real_abs_opp a)).
  - apply real_abs_pos_req.
    exact (real_eq_lt_lt real_zero (real_opp real_zero) (real_opp a)
               (real_eq_sym _ _ real_opp_zero)
               (real_opp_lt_compat a real_zero Ha)).
Qed.

(* ---- item 11 (closing the _cc family): x - 0 == x ---- *)
(* Id chain: unfold minus, rewrite opp zero == zero, then plus_zero; the Real *)
(*   layer unfolds real_minus_r, rewrites the right summand with *)
(*   RealSetoid.real_eq_plus_compat (opp 0 = 0), then real_plus_zero closes. *)
(*   So the five _cc sign *)
(*   auxiliary items are all carried over; the pointwise TV chain resumes at *)
(*   the Id topk_tv_pointwise_keep (@5667). *)
Lemma rtk_minus_zero_cc :
  forall x : Real, real_eq (real_minus_r x real_zero) x.
Proof.
  intro x. unfold real_minus_r.
  apply (real_eq_trans _ (real_plus x real_zero)).
  - apply (RealSetoid.real_eq_plus_compat x (real_opp real_zero) x real_zero).
    + apply real_eq_refl.
    + exact real_opp_zero.
  - exact (real_plus_zero x).
Qed.

End RealTopKTVChain.

(* ============================================================ *)
(* first-half inventory: 11 lemma items + 5 defining carriers in this file; *)
(*   the compliance audit appears in the closing note. *)
(*   rtk_boltzmann_factor_pos_attn<-5554  rtk_kept_term_nonneg<-5560    *)
(*   rtk_kept_term_le_factor<-5569        rtk_kept_plus_tail_full<-5578 *)
(*   rtk_kept_le_Zthermo<-5603            rtk_inv_Z_le_inv_kept<-5611   *)
(*   rtk_inv_one_cc<-5620                 rtk_opp_zero_cc<-5628         *)
(*   rtk_lt_minus_cc<-5637                rtk_abs_neg_cc<-5647          *)
(*   rtk_minus_zero_cc<-5658                                            *)
(*   defining carriers: rtk_boltzmann_factor <- 3840, rtk_Z_thermo <- 3843 *)
(*   rtk_tail_mass<-5537                  rtk_kept_partition<-5541      *)
(*   (topk_renorm <- 5548 belongs to the second half of the TV chain and *)
(*   moves with items 12-19). *)
(* remaining second-half list (through the Id block at 5886, 8 items): *)
(*   topk_tv_pointwise_keep<-5667 / topk_tv_pointwise_evict<-5725 /      *)
(*   topk_if_split<-5742 / eviction_if_linear_else<-5753 /               *)
(*   topk_tv_pointwise<-5764 / topk_sum_decomp<-5780 /                   *)
(*   topk_sum_collapse <- 5840 / topk_tv_identity_strict <- 5886 (the main statement). *)
(*   used interface: the three summation fields of this section plus a *)
(*   linearity field (the pointwise and decomposition stages of the TV chain *)
(*   need real_sum_over_S_linear, the same field as the Id sum_over_S_linear, *)
(*   added on the req side as well); *)
(*   items 9-11 rtk_lt_minus_cc / rtk_abs_neg_cc / rtk_minus_zero_cc *)
(*   serve as the sign legs of the pointwise difference decomposition. *)

(*   Print Assumptions reports all eleven items Closed; Recursive Extraction *)
(*   reports Obj.magic = 0 at the top-level names. *)

(* ============================================================ *)

(* ============================================================ *)
(* UpReqTopKTVChain.v -- Theorem 7.6 topk_tv_identity (second half) *)
(*   Real-layer translation, second half complete (the 8 pointwise TV items *)
(*   plus the closing main statement) *)
(* ------------------------------------------------------------------ *)

(*   item 12 rtk_tv_pointwise_keep       <- S06 5667 (kept-branch sign identity) *)
(*   item 13 rtk_tv_pointwise_evict      <- S06 5725 (evicted |x - 0| == x) *)
(*   item 14 rtk_if_split                <- S06 5742 (pointwise if additive decomposition) *)
(*   item 15 rtk_eviction_if_linear_else <- S06 5753 (else-branch linearity, dual) *)
(*   item 16 rtk_tv_pointwise            <- S06 5764 (full pointwise identity, conditioned) *)
(*   item 17 rtk_sum_decomp              <- S06 5780 (sum decomposition) *)
(*   item 18 rtk_sum_collapse            <- S06 5840 (collapse to 2 * invZ * T) *)
(*   item 19 rtk_tv_identity_strict      <- S06 5886 (main statement TV == tail/Z) *)
(* ------------------------------------------------------------------ *)
(* new carriers: the rtk2_* wrappers quote the raised names directly, nothing *)
(*   rebuilt; the matching Id anchors appear at the line ends *)
(*   rtk2_bfactor<- rtk_boltzmann_factor  rtk2_Z<-rtk_Z_thermo      *)
(*   rtk2_kept<-rtk_kept_partition @5541  rtk2_tail<-rtk_tail_mass @5537 *)
(*   rtk2_topk_renorm<-S06 5548  rtk2_boltzmann_dist_attn<-S06 3847    *)
(*   rtk2_tv_dist <- S06 4033 (inv2 := 1/(1+1), real_two_pos S08 593) *)

(*   S01 line 1402; the field reserved by the header note is filled here, *)
(*   used by item 17). Two auxiliary items (in use): *)
(*   rtk_minus_plus_cancel_r_cc (copy of the Id minus_plus_cancel_r, used by item 18) *)
(*   rtk_eviction_if_linear <- S06 4653 (kept-branch linearity, used by item 17). *)
(* quoted uses: items 9-11 lt_minus_cc / abs_neg_cc / minus_zero_cc *)
(*   (the sign legs) plus the base facts: real_distrib S02 2375 / real_distrib_r S09 *)
(*   111 / real_mult_opp_l S08 49 / real_opp_plus S07 7786 /            *)
(*   real_opp_opp S08 95 / real_plus_assoc S02 2333 / real_plus_opp     *)
(*   S02 2345 / real_abs_mult_req S07 7268 / real_abs_eq_compat S08     *)
(*   5112 / real_abs_pos_req S07 7280 / real_mult_positive S07 6960 /   *)
(*   real_inv_pos_pos S03 6771 / real_inv_pos_correct S03 6722. *)
(* discipline: purely constructive; zero Prop leakage at the Set layer; real_eq *)
(*   is never rewritten outside the Id rules -- the whole chain gives *)
(*   real_eq_trans explicit endpoints (the family items take x and y as explicit *)
(*   leading arguments); *)
(*   every item closes with Qed. *)
(* ============================================================ *)

Section RealTopKTVFinish.


Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) ->
  real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).

(* ---- thermodynamic carriers (bitwise match to the Id block at 3843; the *)
(*   same shape as the first section) ---- *)
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable energy : S -> Real.

(* ---- Boltzmann carrier instantiation (direct quotes of the raised names) ---- *)
Definition rtk2_bfactor (s : S) : Real :=
  rtk_boltzmann_factor S D D_pos energy s.

Definition rtk2_Z : Real := rtk_Z_thermo S real_sum_over_S D D_pos energy.

Variable rtk2_Zpos : real_lt real_zero rtk2_Z.

Definition rtk2_invZ : Real := real_inv_pos rtk2_Z rtk2_Zpos.

Definition rtk2_kept (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : Real :=
  rtk_kept_partition S real_sum_over_S D D_pos energy k kd.

Definition rtk2_tail (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : Real :=
  rtk_tail_mass S real_sum_over_S D D_pos energy k kd.

Definition rtk2_invK (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
  (Hkpos : real_lt real_zero (rtk2_kept k kd)) : Real :=
  real_inv_pos (rtk2_kept k kd) Hkpos.

(* top-K renormalized distribution <- S06 5548 *)
Definition rtk2_topk_renorm (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
  (Hkpos : real_lt real_zero (rtk2_kept k kd)) (s : S) : Real :=
  if kd s then real_mult (rtk2_invK k kd Hkpos) (rtk2_bfactor s) else real_zero.

(* Boltzmann distribution <- S06 3847 *)
Definition rtk2_boltzmann_dist_attn (s : S) : Real :=
  real_mult rtk2_invZ (rtk2_bfactor s).

(* total-variation distance <- S06 4033 (inv2 := 1/(1+1)) *)
Definition rtk2_tv_dist (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
  (Hkpos : real_lt real_zero (rtk2_kept k kd)) : Real :=
  real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos)
            (real_sum_over_S (fun s : S =>
               real_abs (real_minus_r (rtk2_boltzmann_dist_attn s)
                                      (rtk2_topk_renorm k kd Hkpos s)))).

(* ============================================================ *)
(* auxiliary A1: x + y - x == y (copy of the Id minus_plus_cancel_r; used by item 18) *)
(* ============================================================ *)
Lemma rtk_minus_plus_cancel_r_cc :
  forall m x : Real,
    real_eq (real_minus_r (real_plus m x) m) x.
Proof.
  intros m x.
  apply (real_eq_trans _ (real_plus x real_zero) _).
  - apply (real_eq_trans _ (real_plus x (real_plus m (real_opp m))) _).
    + apply (real_eq_trans _ (real_plus (real_plus x m) (real_opp m)) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_plus m x) (real_opp m)
                 (real_plus x m) (real_opp m)
                 (real_plus_comm m x) (real_eq_refl (real_opp m))).
      * exact (real_eq_sym _ _ (real_plus_assoc x m (real_opp m))).
    + apply (RealSetoid.real_eq_plus_compat
               x (real_plus m (real_opp m)) x real_zero
               (real_eq_refl x) (real_plus_opp m)).
  - exact (real_plus_zero x).
Qed.

(* ---- item 14: pointwise if additive decomposition ---- *)
Lemma rtk_if_split :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (X Y : Real) (s : S),
    real_eq (if kd s then X else Y)
            (real_plus (if kd s then X else real_zero)
                       (if kd s then real_zero else Y)).
Proof.
  intros k kd X Y s. destruct (kd s) as [Hk | Hnk].
  - exact (real_eq_sym _ _ (real_plus_zero X)).
  - exact (real_eq_trans _ _ _ (real_eq_sym _ _ (real_plus_zero Y))
             (real_eq_sym _ _ (real_plus_comm real_zero Y))).
Qed.

(* ---- auxiliary A2: kept-branch linearity (used by item 17) ---- *)
Lemma rtk_eviction_if_linear :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (a : Real) (f : S -> Real) (s : S),
    real_eq (if kd s then real_mult a (f s) else real_zero)
            (real_mult a (if kd s then f s else real_zero)).
Proof.
  intros k kd a f s. destruct (kd s) as [Hk | Hnk].
  - apply real_eq_refl.
  - exact (real_eq_sym _ _ (real_mult_zero a)).
Qed.

(* ---- item 15: else-branch linearity (dual of A2) ---- *)
Lemma rtk_eviction_if_linear_else :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (a : Real) (f : S -> Real) (s : S),
    real_eq (if kd s then real_zero else real_mult a (f s))
            (real_mult a (if kd s then real_zero else f s)).
Proof.
  intros k kd a f s. destruct (kd s) as [Hk | Hnk].
  - exact (real_eq_sym _ _ (real_mult_zero a)).
  - apply real_eq_refl.
Qed.

(* ============================================================ *)
(* item 12: kept-branch pointwise sign identity *)
(*   |b*invZ - invK*b| == b*(invK - invZ), under invZ < invK (strict eviction, *)
(*   instantiated on the Real layer from T > 0); the sign legs are the *)
(*   item 9 + item 10 steps. *)
(* ============================================================ *)
Lemma rtk_tv_pointwise_keep :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s : S)
         (Hk : k s)
         (Hkpos : real_lt real_zero (rtk2_kept k kd))
         (Hst : real_lt (real_inv_pos rtk2_Z rtk2_Zpos)
                        (real_inv_pos (rtk2_kept k kd) Hkpos)),
    real_eq (real_abs (real_minus_r
              (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
              (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos) (rtk2_bfactor s))))
            (real_mult (rtk2_bfactor s)
                       (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                     (real_inv_pos rtk2_Z rtk2_Zpos))).
Proof.
  intros k kd s Hk Hkpos Hst.
  (* leg 1 (factor out the common term; the reverse copy of the Id mult_minus_distr_r) *)
  assert (Hfac : real_eq
           (real_minus_r (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                         (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos) (rtk2_bfactor s)))
           (real_mult (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                    (real_inv_pos (rtk2_kept k kd) Hkpos))
                      (rtk2_bfactor s))).
  { apply (real_eq_trans _ (real_plus (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                        (real_opp (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos)
                                             (rtk2_bfactor s)))) _).
    - apply real_eq_refl.
    - apply (real_eq_trans _ (real_plus (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                          (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos)
                                     (real_opp (rtk2_bfactor s)))) _).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                 (real_opp (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos)
                                      (rtk2_bfactor s)))
                 (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                 (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos)
                            (real_opp (rtk2_bfactor s)))
                 (real_eq_refl (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))
                 (real_eq_sym _ _
                    (real_mult_opp_l (real_inv_pos (rtk2_kept k kd) Hkpos)
                                     (rtk2_bfactor s)))).
      + apply (real_eq_trans _ (real_plus (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                            (real_mult (rtk2_bfactor s)
                                       (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))) _).
        * apply (RealSetoid.real_eq_plus_compat
                   (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                   (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos)
                              (real_opp (rtk2_bfactor s)))
                   (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                   (real_mult (rtk2_bfactor s)
                              (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))
                   (real_eq_refl (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))
                   (real_eq_trans _ _ _
                      (real_mult_opp_l (real_inv_pos (rtk2_kept k kd) Hkpos)
                                       (rtk2_bfactor s))
                      (real_eq_trans _ _ _
                         (RealSetoid.real_eq_opp_compat
                            (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos)
                                       (rtk2_bfactor s))
                            (real_mult (rtk2_bfactor s)
                                       (real_inv_pos (rtk2_kept k kd) Hkpos))
                            (real_mult_comm (real_inv_pos (rtk2_kept k kd) Hkpos)
                                            (rtk2_bfactor s)))
                         (real_eq_sym _ _
                            (real_mult_opp_l (rtk2_bfactor s)
                                             (real_inv_pos (rtk2_kept k kd) Hkpos)))))).
        * apply (real_eq_trans _ (real_mult (rtk2_bfactor s)
                              (real_plus (real_inv_pos rtk2_Z rtk2_Zpos)
                                         (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))) _).
          -- apply (real_eq_trans _
                      (real_plus (real_mult (rtk2_bfactor s)
                                            (real_inv_pos rtk2_Z rtk2_Zpos))
                                 (real_mult (rtk2_bfactor s)
                                            (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))) _).
            ++ apply (RealSetoid.real_eq_plus_compat
                        (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                        (real_mult (rtk2_bfactor s)
                                   (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))
                        (real_mult (rtk2_bfactor s) (real_inv_pos rtk2_Z rtk2_Zpos))
                        (real_mult (rtk2_bfactor s)
                                   (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))
                        (real_mult_comm (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                        (real_eq_refl
                           (real_mult (rtk2_bfactor s)
                                      (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos))))).
            ++ exact (real_eq_sym _ _
                         (real_distrib (rtk2_bfactor s) (real_inv_pos rtk2_Z rtk2_Zpos)
                                       (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))).
          -- exact (real_mult_comm (rtk2_bfactor s)
                       (real_plus (real_inv_pos rtk2_Z rtk2_Zpos)
                                  (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))). }
  (* leg 2 (|D'*b| == b*|D'|): real_abs_mult_req + commutativity + |b| == b *)
  assert (Habs : real_eq
           (real_abs (real_mult (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                              (real_inv_pos (rtk2_kept k kd) Hkpos))
                                (rtk2_bfactor s)))
           (real_mult (rtk2_bfactor s)
                      (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                              (real_inv_pos (rtk2_kept k kd) Hkpos))))).
  { apply (real_eq_trans _ (real_mult (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                                (real_inv_pos (rtk2_kept k kd) Hkpos)))
                        (real_abs (rtk2_bfactor s))) _).
    - exact (real_abs_mult_req
               (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                             (real_inv_pos (rtk2_kept k kd) Hkpos))
               (rtk2_bfactor s)).
    - apply (real_eq_trans _ (real_mult (real_abs (rtk2_bfactor s))
                          (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                                  (real_inv_pos (rtk2_kept k kd) Hkpos)))) _).
      + exact (real_mult_comm
                 (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                         (real_inv_pos (rtk2_kept k kd) Hkpos)))
                 (real_abs (rtk2_bfactor s))).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_abs (rtk2_bfactor s))
                 (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                         (real_inv_pos (rtk2_kept k kd) Hkpos)))
                 (rtk2_bfactor s)
                 (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                         (real_inv_pos (rtk2_kept k kd) Hkpos)))
                 (real_abs_pos_req (rtk2_bfactor s)
                    (rtk_boltzmann_factor_pos_attn S D D_pos energy s))
                 (real_eq_refl
                    (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                            (real_inv_pos (rtk2_kept k kd) Hkpos))))). }
  (* leg 3 (the sign, under the premise invZ < invK): the item 9 + item 10 steps *)
  assert (Hsign : real_eq
           (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                   (real_inv_pos (rtk2_kept k kd) Hkpos)))
           (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                         (real_inv_pos rtk2_Z rtk2_Zpos))).
  { apply (real_eq_trans _ (real_opp (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                     (real_inv_pos (rtk2_kept k kd) Hkpos))) _).
    - exact (rtk_abs_neg_cc
               (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                             (real_inv_pos (rtk2_kept k kd) Hkpos))
               (rtk_lt_minus_cc (real_inv_pos rtk2_Z rtk2_Zpos)
                                (real_inv_pos (rtk2_kept k kd) Hkpos) Hst)).
    - apply (real_eq_trans _ (real_plus (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))
                          (real_opp (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))) _).
      + exact (real_opp_plus (real_inv_pos rtk2_Z rtk2_Zpos)
                 (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos))).
      + apply (real_eq_trans _ (real_plus (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))
                            (real_inv_pos (rtk2_kept k kd) Hkpos)) _).
        * apply (RealSetoid.real_eq_plus_compat
                   (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))
                   (real_opp (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))
                   (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))
                   (real_inv_pos (rtk2_kept k kd) Hkpos)
                   (real_eq_refl (real_opp (real_inv_pos rtk2_Z rtk2_Zpos)))
                   (real_opp_opp (real_inv_pos (rtk2_kept k kd) Hkpos))).
        * exact (real_plus_comm (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))
                                (real_inv_pos (rtk2_kept k kd) Hkpos)). }
  (* assembly: |b*invZ - invK*b| == b*(invK - invZ) *)
  apply (real_eq_trans _ (real_abs (real_mult (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                              (real_inv_pos (rtk2_kept k kd) Hkpos))
                                (rtk2_bfactor s))) _).
  - apply real_abs_eq_compat. exact Hfac.
  - apply (real_eq_trans _ (real_mult (rtk2_bfactor s)
                        (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                                (real_inv_pos (rtk2_kept k kd) Hkpos)))) _).
    + exact Habs.
    + apply (RealSetoid.real_eq_mult_compat
               (rtk2_bfactor s)
               (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                       (real_inv_pos (rtk2_kept k kd) Hkpos)))
               (rtk2_bfactor s)
               (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                             (real_inv_pos rtk2_Z rtk2_Zpos))
               (real_eq_refl (rtk2_bfactor s)) Hsign).
Qed.

(* ---- item 13: evicted branch |b*invZ - 0| == b*invZ ---- *)
Lemma rtk_tv_pointwise_evict :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s : S)
         (Hnk : Not (k s)),
    real_eq (real_abs (real_minus_r
              (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)) real_zero))
            (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)).
Proof.
  intros k kd s Hnk.
  apply (real_eq_trans _ (real_abs (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))) _).
  - apply real_abs_eq_compat.
    exact (rtk_minus_zero_cc
             (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))).
  - apply real_abs_pos_req.
    apply (real_mult_positive (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)).
    + apply (real_inv_pos_pos rtk2_Z rtk2_Zpos).
    + exact (rtk_boltzmann_factor_pos_attn S D D_pos energy s).
Qed.

(* ---- item 16: the full pointwise identity (conditioned) ---- *)
Lemma rtk_tv_pointwise :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : real_lt real_zero (rtk2_kept k kd)) (s : S)
         (Hst : real_lt (real_inv_pos rtk2_Z rtk2_Zpos)
                        (real_inv_pos (rtk2_kept k kd) Hkpos)),
    real_eq (real_abs (real_minus_r
              (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
              (rtk2_topk_renorm k kd Hkpos s)))
            (if kd s
             then real_mult (rtk2_bfactor s)
                            (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                          (real_inv_pos rtk2_Z rtk2_Zpos))
             else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)).
Proof.
  intros k kd Hkpos s Hst. unfold rtk2_topk_renorm.
  destruct (kd s) as [Hk | Hnk].
  - exact (rtk_tv_pointwise_keep k kd s Hk Hkpos Hst).
  - exact (rtk_tv_pointwise_evict k kd s Hnk).
Qed.

(* ============================================================ *)
(* item 17: sum decomposition *)
(*   sum(if keep then b*D' else invZ*b) == kept*D' + invZ*T *)
(*   Σ(if keep then b·D' else invZ·b) == kept·D' + invZ·T               *)
(*   chain: the if additive decomposition (item 14), then additivity of the sum, *)
(*   then the two linearity legs (the linearity field plus A2/item 15), *)
(*   and the kept/tail endpoints close definitionally. *)
(* ============================================================ *)
Lemma rtk_sum_decomp :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : real_lt real_zero (rtk2_kept k kd))
         (Hst : real_lt (real_inv_pos rtk2_Z rtk2_Zpos)
                        (real_inv_pos (rtk2_kept k kd) Hkpos)),
    real_eq (real_sum_over_S (fun s : S =>
               if kd s
               then real_mult (rtk2_bfactor s)
                              (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                            (real_inv_pos rtk2_Z rtk2_Zpos))
               else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))
            (real_plus (real_mult (rtk2_kept k kd)
                                  (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                                (real_inv_pos rtk2_Z rtk2_Zpos)))
                       (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
Proof.
  intros k kd Hkpos Hst.
  apply (real_eq_trans _ (real_plus
              (real_sum_over_S (fun s : S =>
                 if kd s
                 then real_mult (rtk2_bfactor s)
                                (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                              (real_inv_pos rtk2_Z rtk2_Zpos))
                 else real_zero))
              (real_sum_over_S (fun s : S =>
                 if kd s then real_zero
                 else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))) _).
  - (* pointwise if decomposition (item 14), then additivity of the sum *)
    apply (real_eq_trans _ (real_sum_over_S (fun s : S =>
                real_plus (if kd s
                           then real_mult (rtk2_bfactor s)
                                          (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                                        (real_inv_pos rtk2_Z rtk2_Zpos))
                           else real_zero)
                          (if kd s then real_zero
                           else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))) _).
    + apply real_sum_over_S_ext. intro s.
      exact (rtk_if_split k kd
               (real_mult (rtk2_bfactor s)
                          (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                        (real_inv_pos rtk2_Z rtk2_Zpos)))
               (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)) s).
    + exact (real_sum_over_S_add
               (fun s : S =>
                  if kd s
                  then real_mult (rtk2_bfactor s)
                                 (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                               (real_inv_pos rtk2_Z rtk2_Zpos))
                  else real_zero)
               (fun s : S =>
                  if kd s then real_zero
                  else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))).
  - (* the two linearity legs *)
    apply (RealSetoid.real_eq_plus_compat
             (real_sum_over_S (fun s : S =>
                if kd s
                then real_mult (rtk2_bfactor s)
                               (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                             (real_inv_pos rtk2_Z rtk2_Zpos))
                else real_zero))
             (real_sum_over_S (fun s : S =>
                if kd s then real_zero
                else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))
             (real_mult (rtk2_kept k kd)
                        (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                      (real_inv_pos rtk2_Z rtk2_Zpos)))
             (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
    + (* LEFT: sum(if k then b*D' else 0) == (sum if-kept)*D' *)
      apply (real_eq_trans _ (real_sum_over_S (fun s : S =>
                  real_mult (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                          (real_inv_pos rtk2_Z rtk2_Zpos))
                            (if kd s then rtk2_bfactor s else real_zero))) _).
      * apply real_sum_over_S_ext. intro s.
        apply (real_eq_trans _ (if kd s
                  then real_mult (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                                (real_inv_pos rtk2_Z rtk2_Zpos))
                                 (rtk2_bfactor s)
                  else real_zero) _).
        -- destruct (kd s) as [Hks | Hnks].
           ++ exact (real_mult_comm (rtk2_bfactor s)
                       (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                     (real_inv_pos rtk2_Z rtk2_Zpos))).
           ++ apply real_eq_refl.
        -- exact (rtk_eviction_if_linear k kd
                    (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                  (real_inv_pos rtk2_Z rtk2_Zpos))
                    rtk2_bfactor s).
      * apply (real_eq_trans _ (real_mult (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                          (real_inv_pos rtk2_Z rtk2_Zpos))
                            (real_sum_over_S (fun s : S =>
                               if kd s then rtk2_bfactor s else real_zero))) _).
        -- exact (real_sum_over_S_linear
                    (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                  (real_inv_pos rtk2_Z rtk2_Zpos))
                    (fun s : S => if kd s then rtk2_bfactor s else real_zero)).
        -- exact (real_mult_comm
                    (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                  (real_inv_pos rtk2_Z rtk2_Zpos))
                    (real_sum_over_S (fun s : S =>
                       if kd s then rtk2_bfactor s else real_zero))).
    + (* right: sum(if k then 0 else invZ*b) == invZ * (sum if-tail) (item 15) *)
      apply (real_eq_trans _ (real_sum_over_S (fun s : S =>
                  real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                            (if kd s then real_zero else rtk2_bfactor s))) _).
      * apply real_sum_over_S_ext. intro s.
        exact (rtk_eviction_if_linear_else k kd
                 (real_inv_pos rtk2_Z rtk2_Zpos) rtk2_bfactor s).
      * exact (real_sum_over_S_linear (real_inv_pos rtk2_Z rtk2_Zpos)
                  (fun s : S => if kd s then real_zero else rtk2_bfactor s)).
Qed.

(* ============================================================ *)
(* item 18: finishing algebra kept*D' + invZ*T == (1+1)*(invZ*T) *)
(* ============================================================ *)
Lemma rtk_sum_collapse :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : real_lt real_zero (rtk2_kept k kd)),
    real_eq (real_plus (real_mult (rtk2_kept k kd)
                                  (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                                (real_inv_pos rtk2_Z rtk2_Zpos)))
                       (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
            (real_mult (real_plus real_one real_one)
                       (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
Proof.
  intros k kd Hkpos.
  (* kept*invK == 1 (direct quote of real_inv_pos_correct) *)
  assert (Hkept1 : real_eq
             (real_mult (rtk2_kept k kd) (real_inv_pos (rtk2_kept k kd) Hkpos))
             real_one)
    by exact (real_inv_pos_correct (rtk2_kept k kd) Hkpos).
  (* Hk1: kept*(invK - invZ) == 1 - kept*invZ *)
  assert (Hk1 : real_eq
           (real_mult (rtk2_kept k kd)
                      (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                    (real_inv_pos rtk2_Z rtk2_Zpos)))
           (real_minus_r real_one
                         (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))).
  { unfold real_minus_r.
    apply (real_eq_trans _ (real_plus real_one
                          (real_opp (real_mult (rtk2_kept k kd)
                                               (real_inv_pos rtk2_Z rtk2_Zpos)))) _).
    - apply (real_eq_trans _ (real_plus (real_mult (rtk2_kept k kd)
                                                       (real_inv_pos (rtk2_kept k kd) Hkpos))
                          (real_mult (rtk2_kept k kd)
                                     (real_opp (real_inv_pos rtk2_Z rtk2_Zpos)))) _).
      + apply (real_eq_trans _ (real_plus (real_mult (rtk2_kept k kd)
                                                       (real_inv_pos (rtk2_kept k kd) Hkpos))
                            (real_mult (rtk2_kept k kd)
                                       (real_opp (real_inv_pos rtk2_Z rtk2_Zpos)))) _).
        * exact (real_distrib (rtk2_kept k kd) (real_inv_pos (rtk2_kept k kd) Hkpos)
                              (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))).
        * exact (real_eq_refl
                   (real_plus (real_mult (rtk2_kept k kd)
                                          (real_inv_pos (rtk2_kept k kd) Hkpos))
                              (real_mult (rtk2_kept k kd)
                                         (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))))).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_mult (rtk2_kept k kd) (real_inv_pos (rtk2_kept k kd) Hkpos))
                 (real_mult (rtk2_kept k kd) (real_opp (real_inv_pos rtk2_Z rtk2_Zpos)))
                 real_one
                 (real_opp (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
                 Hkept1
                 (real_mult_opp_l (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))).
    - apply real_eq_refl. }
  (* Hk2: kept*invZ + invZ*T == 1 (conservation + inv_pos_correct) *)
  assert (Hk2 : real_eq
           (real_plus (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
                      (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
           real_one).
  { apply (real_eq_trans _ (real_plus (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
                        (real_mult (rtk2_tail k kd) (real_inv_pos rtk2_Z rtk2_Zpos))) _).
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
               (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
               (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
               (real_mult (rtk2_tail k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
               (real_eq_refl
                  (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
               (real_mult_comm (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
    - apply (real_eq_trans _ (real_mult rtk2_Z (real_inv_pos rtk2_Z rtk2_Zpos)) _).
      + apply (real_eq_trans _
                  (real_mult (real_plus (rtk2_kept k kd) (rtk2_tail k kd))
                             (real_inv_pos rtk2_Z rtk2_Zpos)) _).
        * exact (real_distrib_r (rtk2_kept k kd) (rtk2_tail k kd)
                                (real_inv_pos rtk2_Z rtk2_Zpos)).
        * apply (RealSetoid.real_eq_mult_compat
                   (real_plus (rtk2_kept k kd) (rtk2_tail k kd))
                   (real_inv_pos rtk2_Z rtk2_Zpos)
                   rtk2_Z
                   (real_inv_pos rtk2_Z rtk2_Zpos)
                   (rtk_kept_plus_tail_full S real_sum_over_S real_sum_over_S_ext
                      real_sum_over_S_add D D_pos energy k kd)
                   (real_eq_refl (real_inv_pos rtk2_Z rtk2_Zpos))).
      + exact (real_inv_pos_correct rtk2_Z rtk2_Zpos). }
  (* Hk3: 1 - kept*invZ == invZ*T (closed by A1) *)
  assert (Hk3 : real_eq
           (real_minus_r real_one
                         (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
           (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
  { apply (real_eq_trans _ (real_minus_r
                (real_plus (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
                           (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
                (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))) _).
    - apply (RealSetoid.real_eq_plus_compat real_one
               (real_opp (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
               (real_plus (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
                          (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
               (real_opp (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
               (real_eq_sym _ _ Hk2)
               (real_eq_refl
                  (real_opp (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))))).
    - exact (rtk_minus_plus_cancel_r_cc
               (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
               (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))). }
  (* assembly: kept*D' + invZ*T == (1 - kept*invZ) + invZ*T == X + X == (1+1)*X *)
  apply (real_eq_trans _ (real_plus (real_minus_r real_one
                                   (real_mult (rtk2_kept k kd)
                                              (real_inv_pos rtk2_Z rtk2_Zpos)))
                      (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))) _).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (rtk2_kept k kd)
                        (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                      (real_inv_pos rtk2_Z rtk2_Zpos)))
             (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
             (real_minus_r real_one
                           (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
             (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
             Hk1 (real_eq_refl (real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                          (rtk2_tail k kd)))).
  - apply (real_eq_trans _ (real_plus (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
                        (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))) _).
    + apply (RealSetoid.real_eq_plus_compat
               (real_minus_r real_one
                             (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
               (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
               (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
               (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
               Hk3 (real_eq_refl (real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                            (rtk2_tail k kd)))).
    + apply (real_eq_trans _ (real_plus (real_mult real_one
                                     (real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                                (rtk2_tail k kd)))
                          (real_mult real_one
                                     (real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                                (rtk2_tail k kd)))) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
                 (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
                 (real_mult real_one
                            (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
                 (real_mult real_one
                            (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
                 (real_eq_trans _ _ _
                    (real_eq_sym _ _
                       (real_mult_one
                          (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))))
                    (real_eq_sym _ _
                       (real_mult_comm real_one
                          (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))))
                 (real_eq_trans _ _ _
                    (real_eq_sym _ _
                       (real_mult_one
                          (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))))
                    (real_eq_sym _ _
                       (real_mult_comm real_one
                          (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))))).
      * exact (real_distrib_r real_one real_one
                 (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
Qed.

(* ============================================================ *)
(* item 19 (the main statement): strict eviction implies TV(boltzmann, topk) == tail/Z *)
(* ============================================================ *)
Theorem rtk_tv_identity_strict :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : real_lt real_zero (rtk2_kept k kd))
         (Hst : real_lt (real_inv_pos rtk2_Z rtk2_Zpos)
                        (real_inv_pos (rtk2_kept k kd) Hkpos)),
    real_eq (rtk2_tv_dist k kd Hkpos)
            (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)).
Proof.
  intros k kd Hkpos Hst.
  (* pointwise substitution (item 16) *)
  assert (Hpt : real_eq
           (real_sum_over_S (fun s : S =>
              real_abs (real_minus_r
                          (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                          (rtk2_topk_renorm k kd Hkpos s))))
           (real_sum_over_S (fun s : S =>
              if kd s
              then real_mult (rtk2_bfactor s)
                             (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                           (real_inv_pos rtk2_Z rtk2_Zpos))
              else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))).
  { apply real_sum_over_S_ext. intro s.
    exact (rtk_tv_pointwise k kd Hkpos s Hst). }
  apply (real_eq_trans _ (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos)
                      (real_sum_over_S (fun s : S =>
                         if kd s
                         then real_mult (rtk2_bfactor s)
                                        (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                                      (real_inv_pos rtk2_Z rtk2_Zpos))
                         else real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                        (rtk2_bfactor s)))) _).
  - (* inv2 * sum(|.|) == inv2 * sum(if.): both endpoints close definitionally *)
  (*   once rtk2_tv_dist is unfolded *)
    apply (RealSetoid.real_eq_mult_compat
             (real_inv_pos (real_plus real_one real_one) real_two_pos)
             (real_sum_over_S (fun s : S =>
                real_abs (real_minus_r
                            (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                            (rtk2_topk_renorm k kd Hkpos s))))
             (real_inv_pos (real_plus real_one real_one) real_two_pos)
             (real_sum_over_S (fun s : S =>
                if kd s
                then real_mult (rtk2_bfactor s)
                               (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                             (real_inv_pos rtk2_Z rtk2_Zpos))
                else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))
             (real_eq_refl (real_inv_pos (real_plus real_one real_one) real_two_pos))
             Hpt).
  - apply (real_eq_trans _ (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos)
                        (real_plus
                           (real_mult (rtk2_kept k kd)
                                      (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                                    (real_inv_pos rtk2_Z rtk2_Zpos)))
                           (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))) _).
    + (* item 17: sum decomposition *)
      apply (RealSetoid.real_eq_mult_compat
               (real_inv_pos (real_plus real_one real_one) real_two_pos)
               (real_sum_over_S (fun s : S =>
                  if kd s
                  then real_mult (rtk2_bfactor s)
                                 (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                               (real_inv_pos rtk2_Z rtk2_Zpos))
                  else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))
               (real_inv_pos (real_plus real_one real_one) real_two_pos)
               (real_plus
                  (real_mult (rtk2_kept k kd)
                             (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                           (real_inv_pos rtk2_Z rtk2_Zpos)))
                  (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
               (real_eq_refl (real_inv_pos (real_plus real_one real_one) real_two_pos))
               (rtk_sum_decomp k kd Hkpos Hst)).
    + apply (real_eq_trans _ (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos)
                          (real_mult (real_plus real_one real_one)
                                     (real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                                (rtk2_tail k kd)))) _).
      * (* item 18: finishing algebra *)
        apply (RealSetoid.real_eq_mult_compat
                 (real_inv_pos (real_plus real_one real_one) real_two_pos)
                 (real_plus
                    (real_mult (rtk2_kept k kd)
                               (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                             (real_inv_pos rtk2_Z rtk2_Zpos)))
                    (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
                 (real_inv_pos (real_plus real_one real_one) real_two_pos)
                 (real_mult (real_plus real_one real_one)
                            (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
                 (real_eq_refl (real_inv_pos (real_plus real_one real_one) real_two_pos))
                 (rtk_sum_collapse k kd Hkpos)).
      * (* inv2*((1+1)*X) == X: assoc + inv_pos_correct + one *)
        apply (real_eq_trans _ (real_mult
                    (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos)
                               (real_plus real_one real_one))
                    (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))) _).
        -- exact (real_mult_assoc
                     (real_inv_pos (real_plus real_one real_one) real_two_pos)
                     (real_plus real_one real_one)
                     (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
        -- apply (real_eq_trans _ (real_mult real_one
                                (real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                           (rtk2_tail k kd))) _).
           ++ apply (RealSetoid.real_eq_mult_compat
                       (real_mult
                          (real_inv_pos (real_plus real_one real_one) real_two_pos)
                          (real_plus real_one real_one))
                       (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
                       real_one
                       (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
              ** exact (real_eq_trans _ _ _
                            (real_mult_comm
                               (real_inv_pos (real_plus real_one real_one) real_two_pos)
                               (real_plus real_one real_one))
                            (real_inv_pos_correct
                               (real_plus real_one real_one) real_two_pos)).
              ** apply real_eq_refl.
           ++ exact (real_eq_trans _ _ _
                        (real_mult_comm real_one
                           (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
                        (real_mult_one
                           (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))).
Qed.

End RealTopKTVFinish.

(* ============================================================ *)
(* second-half inventory: 8 lemma items + 2 auxiliary items + 6 defining *)
(*   carriers + 1 filled interface field in this file. *)
(*   item 12 rtk_tv_pointwise_keep <- 5667   item 13 rtk_tv_pointwise_evict <- 5725 *)
(*   item 14 rtk_if_split <- 5742            item 15 rtk_eviction_if_linear_else *)
(*   item 16 rtk_tv_pointwise <- 5764        item 17 rtk_sum_decomp <- 5780 *)
(*   item 18 rtk_sum_collapse <- 5840        item 19 rtk_tv_identity_strict <- 5886 *)
(*   (the main statement closes: TV(boltzmann, topk renormalization) == tail/Z, *)
(*   an exact identity) *)
(*   auxiliary: rtk_minus_plus_cancel_r_cc (copy of the Id minus_plus_cancel_r) *)
(*   rtk_eviction_if_linear <- 4653; carriers: rtk2_bfactor / rtk2_Z / rtk2_invZ *)
(*   rtk2_kept/rtk2_tail/rtk2_invK/rtk2_topk_renorm/rtk2_boltzmann_dist_ *)
(*   attn/rtk2_tv_dist (all 8 carriers of the top-K family carried over). *)
(*   filled field: real_sum_over_S_linear (the same field as the Id SumOver, *)
(*   reserved by the header note). *)

(*   Print Assumptions reports every item Closed under the global context *)
(*   (full mode). *)

(* ============================================================ *)

(* Print Assumptions audit block: one line per named statement of this file *)
(*   (34 statements). Every line must report [Closed under the global *)
(*   context]. *)
Print Assumptions rtk_boltzmann_factor.
Print Assumptions rtk_Z_thermo.
Print Assumptions rtk_tail_mass.
Print Assumptions rtk_kept_partition.
Print Assumptions rtk_boltzmann_factor_pos_attn.
Print Assumptions rtk_kept_term_nonneg.
Print Assumptions rtk_kept_term_le_factor.
Print Assumptions rtk_kept_plus_tail_full.
Print Assumptions rtk_kept_le_Zthermo.
Print Assumptions rtk_inv_Z_le_inv_kept.
Print Assumptions rtk_inv_one_cc.
Print Assumptions rtk_opp_zero_cc.
Print Assumptions rtk_lt_minus_cc.
Print Assumptions rtk_abs_neg_cc.
Print Assumptions rtk_minus_zero_cc.
Print Assumptions rtk2_bfactor.
Print Assumptions rtk2_Z.
Print Assumptions rtk2_invZ.
Print Assumptions rtk2_kept.
Print Assumptions rtk2_tail.
Print Assumptions rtk2_invK.
Print Assumptions rtk2_topk_renorm.
Print Assumptions rtk2_boltzmann_dist_attn.
Print Assumptions rtk2_tv_dist.
Print Assumptions rtk_minus_plus_cancel_r_cc.
Print Assumptions rtk_if_split.
Print Assumptions rtk_eviction_if_linear.
Print Assumptions rtk_eviction_if_linear_else.
Print Assumptions rtk_tv_pointwise_keep.
Print Assumptions rtk_tv_pointwise_evict.
Print Assumptions rtk_tv_pointwise.
Print Assumptions rtk_sum_decomp.
Print Assumptions rtk_sum_collapse.
Print Assumptions rtk_tv_identity_strict.

(* ============================================================ *)
