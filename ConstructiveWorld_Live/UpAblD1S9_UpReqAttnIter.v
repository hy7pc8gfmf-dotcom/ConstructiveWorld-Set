(* ConstructiveWorld-Set -- instance-supply record completion for the UpReqAttnIter ReqAttnIter section family. *)

(** * UpAblD1S9_UpReqAttnIter: a 22-slot instance-supply record with one-point feeding.

    Mission.  This file formalizes the instance supply for the ReqAttnIter
      section statement face: the record [uabd1s9_ait_pack22] carries the 22
      slot statements verbatim, the feeding lemmas [uabd1s9_ait_one_lt_two],
      [uabd1s9_ait_delta_lt_one_feed] and [uabd1s9_ait_minor_feed] build the
      arithmetic kernel, and [uabd1s9_ait_pack22_supplied] supplies 21 slots
      on the one-point instance world, [abs_nonneg_h] carried as a premise.

    Dependencies.  Stdlib [List], [QArith.QArith], [QArith.Qabs],
      [QArith.Qround].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqAlgebra],
      [UpReqAlign], [CW220_Extensions] of this development.

    References.  This development, UpAblD1S9_UpReqAttnIter.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblD1S9_UpReqAttnIter.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
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
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import CW220_Extensions.
Import RealInterfaceEnhancedMod.

(* ============ helper 0: 1 < 1+1, the premise ingredient for delta_lt_one ============ *)

Lemma uabd1s9_ait_one_lt_two : real_lt real_one (real_plus real_one real_one).
Proof.
  exists (Qmake 1 2).
  split.
  - apply Qlt_to_QltT. vm_compute. first [exact I | exact eq_refl].
  - exists 0%nat. intros n _.
    apply Qlt_to_QltT.
    unfold real_plus, real_one; cbn [projT1]; simpl.
    vm_compute. first [exact I | exact eq_refl].
Qed.

(* ============ helper 1: half < 1, the feeding lemma for the delta_lt_one slot ============ *)
(*   ingredients: real_inv_pos_lt_contra (the inverse is antitone) and               *)
(*   real_inv_one_local (transport of inv 1 = 1), as in the chain of CW220_Extensions. *)

Lemma uabd1s9_ait_delta_lt_one_feed :
  real_lt (real_inv_pos (real_plus real_one real_one) real_two_pos) real_one.
Proof.
  apply (real_lt_eq_lt (real_inv_pos (real_plus real_one real_one) real_two_pos)
                       (real_inv_pos real_one real_lt_zero_one) real_one).
  - exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one)
             real_lt_zero_one real_two_pos uabd1s9_ait_one_lt_two).
  - exact real_inv_one_local.
Qed.

(* ============ helper 2: the ratio normalization chain, feeding lemma for the minorization slot ============ *)
(*   delta * (1/E * E) <= 1: the inner product 1/E * E equals one by real_mult_comm    *)
(*   and real_inv_pos_correct; real_eq_mult_compat with mult_one collapses the outer   *)
(*   product to delta, and real_le_compat carries the premise at the left injection.   *)

Lemma uabd1s9_ait_minor_feed :
  forall (delta E : Real)
         (Hd1 : real_lt delta real_one) (HE : real_lt real_zero E),
    real_le (real_mult delta (real_mult (real_inv_pos E HE) E)) real_one.
Proof.
  intros delta E Hd1 HE.
  assert (h_inner : real_eq (real_mult (real_inv_pos E HE) E) real_one).
  { apply (real_eq_trans _ (real_mult E (real_inv_pos E HE))).
    - apply real_mult_comm.
    - exact (real_inv_pos_correct E HE). }
  assert (he1 : real_eq (real_mult delta (real_mult (real_inv_pos E HE) E)) delta).
  { apply (real_eq_trans _ (real_mult delta real_one)).
    - exact (RealSetoid.real_eq_mult_compat delta
               (real_mult (real_inv_pos E HE) E) delta real_one
               (real_eq_refl delta) h_inner).
    - apply real_mult_one. }
  exact (RealSetoid.real_le_compat delta
           (real_mult delta (real_mult (real_inv_pos E HE) E))
           real_one real_one (real_eq_sym _ _ he1) (real_eq_refl real_one)
           (inl Hd1)).
Qed.

(* ============ record-style pack: the 22 slot statements carried verbatim ============ *)
(*   slot order follows the declaration order of the source section; Z_thermo_i and    *)
(*   boltzmann_dist_i are inlined at their defining bodies in that section.            *)
(*   Carrier-ization registered (family E3, M34b canon): the one-point carrier [unit]  *)
(*   and the instance carriers [real_eq/real_le/real_lt] are specialized once here so  *)
(*   the extraction face carries no [Obj.magic]; the open slot abs_nonneg_h alone      *)
(*   stays at the interface face [le], type-exact with the supply theorem's premise.   *)

Inductive uabd1s9_ait_pack22 : Type :=
| uabd1s9_ait_pack22_intro :
    forall sumf : (unit -> Real) -> Real,
        (* L100 sum_ext *)
        (forall f g : unit -> Real,
            (forall s : unit, real_eq (f s) (g s)) ->
            real_eq (sumf f) (sumf g)) ->
        (* L102 sum_linear *)
        (forall (a : Real) (f : unit -> Real),
            real_eq (sumf (fun s : unit => mult a (f s)))
                    (mult a (sumf f))) ->
        (* L105 sum_add *)
        (forall f g : unit -> Real,
            real_eq (sumf (fun s : unit => plus (f s) (g s)))
                    (plus (sumf f) (sumf g))) ->
        (* L108 sum_le *)
        (forall f g : unit -> Real,
            (forall s : unit, real_le (f s) (g s)) ->
            real_le (sumf f) (sumf g)) ->
        (* L111 sum_nonneg_h *)
        (forall f : unit -> Real,
            (forall s : unit, real_le zero (f s)) ->
            real_le zero (sumf f)) ->
        (* L114 abs_sum_le_h *)
        (forall f : unit -> Real,
            real_le (abs (sumf f)) (sumf (fun s : unit => abs (f s)))) ->
        (* slot abs_nonneg_h: the genuinely open slot, kept as stated *)
        (forall a : Real, le zero (abs a)) ->
        (* L121 D *)
        forall D : Real,
          (* L122 D_pos *)
          forall D_pos : real_lt zero D,
          (* L123 energy *)
          forall energy : unit -> Real,
          (* slot Z_thermo_i_pos: Z_thermo_i inlined as the sumf of the boltzmann factor *)
          forall Z_thermo_i_pos : real_lt zero (sumf (fun s : unit =>
                    exp_neg (mult (inv_pos D D_pos) (energy s)))),
          (* L136 transition *)
          forall transition : unit -> unit -> Real,
          (* L138 transition_row_i *)
          (forall s : unit,
              real_eq (sumf (fun s' : unit => transition s s')) one) ->
          (* L140 delta *)
          forall delta : Real,
            (* L141 delta_pos *)
            real_lt zero delta ->
            (* L142 delta_lt_one *)
            real_lt delta one ->
            (* slot minorization: boltzmann_dist_i inlined as inv Z times the boltzmann factor *)
            (forall s s' : unit,
                real_le (mult delta
                       (mult (inv_pos (sumf (fun s0 : unit =>
                                 exp_neg (mult (inv_pos D D_pos) (energy s0)))) Z_thermo_i_pos)
                             (exp_neg (mult (inv_pos D D_pos) (energy s')))))
                   (transition s s')) ->
            (* slot p_steady_i: the same inlining applied at both positions *)
            (forall s' : unit,
                real_eq (sumf (fun s : unit =>
                        mult (mult (inv_pos (sumf (fun s0 : unit =>
                                  exp_neg (mult (inv_pos D D_pos) (energy s0)))) Z_thermo_i_pos)
                                (exp_neg (mult (inv_pos D D_pos) (energy s))))
                             (transition s s')))
                    (mult (inv_pos (sumf (fun s0 : unit =>
                              exp_neg (mult (inv_pos D D_pos) (energy s0)))) Z_thermo_i_pos)
                          (exp_neg (mult (inv_pos D D_pos) (energy s'))))) ->
            (* slot arch_pow_i: req_r_pow and req_minus are module-level definitions, quoted verbatim *)
            (forall (a : Real), real_lt zero a ->
                forall eps : Real, real_lt zero eps ->
                  sigT (fun N : nat =>
                    real_lt (mult a (req_r_pow (req_minus one delta) N)) eps)) ->
            uabd1s9_ait_pack22.

(* ============ feeding theorem: the one-point instance supplies 21 slots at once, the remaining open slot carried as an explicit premise ============ *)

Theorem uabd1s9_ait_pack22_supplied :
  forall (Habnn : forall a : Real, le zero (abs a)),
    uabd1s9_ait_pack22.
Proof.
  intro Habnn.
  exact (uabd1s9_ait_pack22_intro           (fun (f : unit -> Real) => f tt)           (fun (f g : unit -> Real)              (H : forall s : unit, real_eq (f s) (g s)) => H tt)           (fun (a : Real) (f : unit -> Real) =>              req_refl (mult a (f tt)))           (fun (f g : unit -> Real) =>              req_refl (plus (f tt) (g tt)))           (fun (f g : unit -> Real)              (H : forall s : unit, real_le (f s) (g s)) => H tt)           (fun (f : unit -> Real)              (H : forall s : unit, real_le zero (f s)) => H tt)           (fun (f : unit -> Real) => le_refl (abs (f tt)))           Habnn           real_one real_lt_zero_one           (fun _ : unit => real_zero)           (exp_neg_pos (mult (inv_pos real_one real_lt_zero_one) real_zero))           (fun _ _ : unit => real_one)           (fun _ : unit => req_refl real_one)           (inv_pos (plus one one) real_two_pos)           (inv_pos_pos (plus one one) real_two_pos)           uabd1s9_ait_delta_lt_one_feed           (fun _ _ : unit =>              uabd1s9_ait_minor_feed                (inv_pos (plus one one) real_two_pos)                (exp_neg (mult (inv_pos real_one real_lt_zero_one) real_zero))                uabd1s9_ait_delta_lt_one_feed                (exp_neg_pos                   (mult (inv_pos real_one real_lt_zero_one) real_zero)))           (fun _ : unit => mult_one _)           (fun (a : Real) (Ha : real_lt zero a) (eps : Real) (Heps : real_lt zero eps) =>              r_arch_pow_attn_real                (inv_pos (plus one one) real_two_pos)                (inv_pos_pos (plus one one) real_two_pos)                uabd1s9_ait_delta_lt_one_feed a Ha eps Heps)).
Qed.

(* ============ assumption audit for the supply theorem ============ *)

Print Assumptions uabd1s9_ait_pack22_supplied.
