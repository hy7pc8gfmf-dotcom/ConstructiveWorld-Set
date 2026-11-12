(* ============================================================
   EntropyMonoSplitInst.v - loader of the three certificate slots
   of UpReqEntropyMonoSplit (source Section EmsEntropyMonoSplit).
   Mission.  each of the three slot conclusions (interface slots of
     the source section, rootless across the library) receives one
     loading theorem: slot 1 Hpinned:137, the slice energy pin
     E(p_u) == E_{t*}, loads inst_pinned; slot 2 Hkl_right:146, the
     right-of-peak KL growth certificate in eps form, loads
     inst_kl_right; slot 3 Hkl_left:153, the left-of-peak KL decay
     certificate, loads inst_kl_left; an isomorphic exact-transfer
     twin and a zero-premise loading at the peak temperature
     complete the set.
   Dependencies.  CW219 / UpReqTempDefs / UpReqEntropyDeficitTemp /
     UpReqEntropyMaxTemp / GibbsAssembly (existing library modules,
     read-only).
   References.  UpReqEntropyMonoSplit.v, the three slot statement
     faces (verbatim same shape).
   Constructivity.  fully constructive with zero assumptions; all
     statement faces sit in Set through the sigT-Or forms of
     real_eq / real_lt / real_le; interface slots are Variables and
     supplies enter as explicit premises; a trailing Print
     Assumptions block audits every exit.
   Build.  coqc -native-compiler no -q -Q . "" ; .vo magic
     [436f7121 000160bc].
   ============================================================ *)

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
Require Import UpReqEntropyMaxTemp.

(* ============================================================ *)
(* Section EntropyMonoSplitInst: the interface face mirrors Section     *)
(*   EmsEntropyMonoSplit of the source module with the same names in    *)
(*   the same order (seven summation slots + peak temperature T_star    *)
(*   + energy); the certificate slots stay Variables, since this module *)
(*   exists to load the certificates and supplies enter as explicit     *)
(*   premises.                                                          *)
(* ============================================================ *)
Section EntropyMonoSplitInst.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable T_star : Real.
Variable T_star_pos : real_lt real_zero T_star.
Variable energy : S -> Real.

(* ---- shorthand (renamed from the source Let ems_bt / ems_bt_pos /    *)
(*   ems_kl_peak with identical shapes, so the slot statements transfer *)
(*   verbatim; the KL direction red line is inherited from the source:  *)
(*   in KL(p_u || p_{t*}) the distribution p_u sits in the first slot   *)
(*   and p_{t*} is the reference, never swapped) ---- *)
Let emsi_bt (u : Real) (Hu : real_lt real_zero u) : S -> Real :=
  real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let emsi_bt_pos (u : Real) (Hu : real_lt real_zero u) :
  forall s : S, real_lt real_zero (emsi_bt u Hu s) :=
  real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let emsi_kl (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_KL_temp S real_sum_over_S real_sum_pos_preserved T_star T_star_pos energy
               (emsi_bt u Hu) (emsi_bt_pos u Hu).

(* ---------------------------------------------------------- *)
(* bridge lemma one (slot 1 bridge, the registered energy-expectation   *)
(*   face in its self-pin form): the per-temperature energy expectation *)
(*   pins itself. the definition face of real_energy_exp_temp is        *)
(*   Sigma p_T · e (UpReqTempDefs.v:199); after the left side is        *)
(*   renamed through emsi_bt the two sides unify definitionally, and    *)
(*   real_eq_refl closes the proof. the shape is verbatim the Henergy   *)
(*   slot of theorem 4.6b (UpReqEntropyMaxTemp.v:364-366) at an         *)
(*   arbitrary positive temperature T := u.                             *)
(* ---------------------------------------------------------- *)
Lemma emsi_energy_pin_self :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (real_sum_over_S (fun s : S => real_mult (emsi_bt u Hu s) (energy s)))
      (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
         u Hu energy).
Proof.
  intros u Hu.
  exact (real_eq_refl           (real_sum_over_S              (fun s : S => real_mult (emsi_bt u Hu s) (energy s)))).
Qed.

(* ---------------------------------------------------------- *)
(* bridge lemma two (order algebra, the difference form): a ≤ b gives   *)
(*   0 ≤ b − a. the registered raw Real face only carries the opposite  *)
(*   direction real_le_plus_nonneg_r (0 ≤ b gives a ≤ a + b,            *)
(*   UpReqEntropyMaxTemp.v:79); this lemma supplies the difference      *)
(*   direction: real_le_plus_compat adds −a to both sides, then         *)
(*   RealSetoid.real_le_id_l rewrites the left side through             *)
(*   (a + −a) ≡ 0. the proof is a pure term witness.                    *)
(* ---------------------------------------------------------- *)
Lemma emsi_le_diff_ge_zero :
  forall a b : Real,
    real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab.
  apply (RealSetoid.real_le_id_l real_zero           (real_plus a (real_opp a))           (real_plus b (real_opp a))           (real_eq_sym (real_plus a (real_opp a)) real_zero              (real_plus_opp a))).
  exact (real_le_plus_compat a b (real_opp a) (real_opp a) Hab           (real_le_refl (real_opp a))).
Qed.

(* ---------------------------------------------------------- *)
(* bridge lemma three (the eps relaxation lift): 0 ≤ X and 0 < eps give *)
(*   0 ≤ X + eps. this is the order-algebra core of the registered      *)
(*   family of shapes "0 ≤ KL + eps": compat adds eps to both sides     *)
(*   and the left side converts through (0+0) ≡ 0.                      *)
(* ---------------------------------------------------------- *)
Lemma emsi_le_plus_eps :
  forall X eps : Real,
    real_le real_zero X -> real_lt real_zero eps ->
    real_le real_zero (real_plus X eps).
Proof.
  intros X eps HX Heps.
  apply (RealSetoid.real_le_id_l real_zero           (real_plus real_zero real_zero)           (real_plus X eps)           (real_eq_sym (real_plus real_zero real_zero) real_zero              (real_plus_zero real_zero))).
  exact (real_le_plus_compat real_zero X real_zero eps HX           (real_le_from_lt_aux real_zero eps Heps)).
Qed.

(* ---------------------------------------------------------- *)
(* exact-transfer twin of the registered sibling corollary (the seed of *)
(*   the slot 2/3 statements): the registered sibling corollary         *)
(*   real_KL_temp_ge_zero_eps (UpReqEntropyMaxTemp.v:197, the only      *)
(*   registration site in the library) is applied with all 16 arguments *)
(*   explicit and the temperature slot converted at T := t*.            *)
(*   - slot coordinates: the source header at :142-144 records that the *)
(*     sibling corollary is already registered;                         *)
(*   - original meaning: 0 ≤ KL(p || p_{t*}) + eps (normalization +     *)
(*     pointwise positivity + eps positive);                            *)
(*   - loading path: out of the section the sibling corollary is        *)
(*     applied with 16 explicit arguments, the 10 interface slots       *)
(*     converted under this section's same names in the same order;     *)
(*   - theorem cited: real_KL_temp_ge_zero_eps                          *)
(*     (UpReqEntropyMaxTemp.v:197).                                     *)
(* ---------------------------------------------------------- *)
Corollary emsi_kl_ge_zero_eps_mirror :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved
              T_star T_star_pos energy p Hp)
           eps).
Proof.
  intros p Hp Hnp eps Heps.
  exact (real_KL_temp_ge_zero_eps           S real_sum_over_S real_sum_pos_preserved           real_sum_over_S_ext real_sum_over_S_le real_sum_over_S_linear           real_sum_over_S_add           T_star T_star_pos energy p Hp Hnp eps Heps).
Qed.

(* ---------------------------------------------------------- *)
(* loading theorem one (slot 1 Hpinned, conclusion shape verbatim from  *)
(*   the source :137-140).                                              *)
(*   - slot coordinates: UpReqEntropyMonoSplit.v:137 (the Hpinned       *)
(*     energy pin);                                                     *)
(*   - original meaning: the slice constraint E(p_u) == E_{t*} for      *)
(*     every positive temperature u (the theorem carrier of the C5      *)
(*     "constraint appears" variable);                                  *)
(*   - loading path: the GibbsAssembly interface face falls short (the  *)
(*     req2 enhanced layer carries no energy pin and the source-layer   *)
(*     red line forbids mixed citation), so the bridge runs over the    *)
(*     registered raw Real face: emsi_energy_pin_self (self-pin,        *)
(*     definitional) composed through real_eq_trans with the slice      *)
(*     transport (E_u == E_{t*}); the constraint content stays          *)
(*     explicit, with no hidden premises;                               *)
(*   - theorem cited: real_energy_exp_temp (definition face at          *)
(*     UpReqTempDefs.v:199; the matching Henergy slot shape at          *)
(*     UpReqEntropyMaxTemp.v:364).                                      *)
(* ---------------------------------------------------------- *)
Theorem inst_pinned :
  (forall (u : Real) (Hu : real_lt real_zero u),
     real_eq
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          u Hu energy)
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          T_star T_star_pos energy)) ->
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (real_sum_over_S (fun s : S => real_mult (emsi_bt u Hu s) (energy s)))
      (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
         T_star T_star_pos energy).
Proof.
  intros Hslice u Hu.
  exact (real_eq_trans           (real_sum_over_S              (fun s : S => real_mult (emsi_bt u Hu s) (energy s)))           (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved              u Hu energy)           (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved              T_star T_star_pos energy)           (emsi_energy_pin_self u Hu)           (Hslice u Hu)).
Qed.

(* ---------------------------------------------------------- *)
(* twin of loading theorem one (zero-premise closed loading at the peak *)
(*   temperature): at u := t* the slice transport degenerates to        *)
(*   reflexivity and the slot face coincides with the self-pin face, a  *)
(*   genuine proof with zero supplies (the closedness witness of the    *)
(*   loading carrier).                                                  *)
(* ---------------------------------------------------------- *)
Theorem inst_pinned_at_peak :
  real_eq
    (real_sum_over_S
       (fun s : S => real_mult (emsi_bt T_star T_star_pos s) (energy s)))
    (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
       T_star T_star_pos energy).
Proof.
  exact (emsi_energy_pin_self T_star T_star_pos).
Qed.

(* ---------------------------------------------------------- *)
(* loading theorem two (slot 2 Hkl_right, conclusion shape verbatim     *)
(*   from the source :146-152).                                         *)
(*   - slot coordinates: UpReqEntropyMonoSplit.v:146 (the Hkl_right     *)
(*     branch right of the peak);                                       *)
(*   - original meaning: 0 ≤ KL_v − KL_u + eps for t* ≤ u ≤ v (the      *)
(*     "KL grows with temperature" reading; KL_v comes first and KL_u   *)
(*     enters through real_opp, never swapped);                         *)
(*   - loading path: the supply is typed plain growth (the literal      *)
(*     right-branch reading real_le KL_u KL_v of the KL-V shape) →      *)
(*     the difference conversion emsi_le_diff_ge_zero → the eps         *)
(*     relaxation lift emsi_le_plus_eps; the statement face is on       *)
(*     record through the sibling-corollary transfer twin (the eps      *)
(*     form is isomorphic);                                             *)
(*   - theorem cited: real_KL_temp_ge_zero_eps (used at the sibling     *)
(*     twin emsi_kl_ge_zero_eps_mirror) plus the two-stage emsi         *)
(*     conversion.                                                      *)
(* ---------------------------------------------------------- *)
Theorem inst_kl_right :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le T_star u -> real_le u v ->
     real_le (emsi_kl u Hu) (emsi_kl v Hv)) ->
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (emsi_kl v Hv) (real_opp (emsi_kl u Hu))) eps).
Proof.
  intros Hgrowth u v Hu Hv Htu Huv eps Heps.
  exact (emsi_le_plus_eps           (real_plus (emsi_kl v Hv) (real_opp (emsi_kl u Hu))) eps           (emsi_le_diff_ge_zero (emsi_kl u Hu) (emsi_kl v Hv)              (Hgrowth u v Hu Hv Htu Huv))           Heps).
Qed.

(* ---------------------------------------------------------- *)
(* loading theorem three (slot 3 Hkl_left, conclusion shape verbatim    *)
(*   from the source :153-159).                                         *)
(*   - slot coordinates: UpReqEntropyMonoSplit.v:153 (the Hkl_left      *)
(*     branch left of the peak);                                        *)
(*   - original meaning: 0 ≤ KL_u − KL_v + eps for u ≤ v ≤ t* (the      *)
(*     "KL decays toward the peak" reading, right branch of the sibling *)
(*     corollary, never swapped);                                       *)
(*   - loading path: the supply is typed plain decay, real_le KL_v KL_u *)
(*     under the order premises u ≤ v ≤ t* → the same difference        *)
(*     bridge plus the eps relaxation bridge in two conversions;        *)
(*   - theorem cited: as in slot 2 (the sibling twin plus the emsi      *)
(*     conversion bridge).                                              *)
(* ---------------------------------------------------------- *)
Theorem inst_kl_left :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le u v -> real_le v T_star ->
     real_le (emsi_kl v Hv) (emsi_kl u Hu)) ->
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (emsi_kl u Hu) (real_opp (emsi_kl v Hv))) eps).
Proof.
  intros Hdecay u v Hu Hv Huv Hvt eps Heps.
  exact (emsi_le_plus_eps           (real_plus (emsi_kl u Hu) (real_opp (emsi_kl v Hv))) eps           (emsi_le_diff_ge_zero (emsi_kl v Hv) (emsi_kl u Hu)              (Hdecay u v Hu Hv Huv Hvt))           Heps).
Qed.

End EntropyMonoSplitInst.

(* ---- embedded audit block (explicit Print Assumptions statements in  *)
(*   file, required ahead of the four checks) ---- *)
Print Assumptions emsi_energy_pin_self.
Print Assumptions emsi_le_diff_ge_zero.
Print Assumptions emsi_le_plus_eps.
Print Assumptions emsi_kl_ge_zero_eps_mirror.
Print Assumptions inst_pinned.
Print Assumptions inst_pinned_at_peak.
Print Assumptions inst_kl_right.
Print Assumptions inst_kl_left.
