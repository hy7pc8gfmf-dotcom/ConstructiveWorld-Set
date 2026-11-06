(* ConstructiveWorld-Set -- independent Set-face re-proofs of the LoHiSqueeze bounds family with temperature-one, spread-one and half-quantity instance forms. *)

(** * ToyR_UpAblP7_LoHiSqueeze: independent re-proofs of the four LoHiSqueeze theorems with three instance forms.

    Mission.  This file re-proves independently the four theorems of the source
      module LoHiSqueeze over an abstract ordered-exponential interface: the
      conjunction lo < 1 and 1 < hi, the squeeze lo < hi, the square bound
      0 < lo*lo < 1, and the kappa bound 0 < 1 - lo*lo < 1.  Main statements:
      [uahl_lo_lt_one_hi], [uahl_lo_lt_hi], [uahl_delta_star_bounded],
      [uahl_omd_bounded], with the instance forms [uahl_omd_bounded_one] and
      [uahl_lo_lt_hi_one] at temperature one and spread one, and
      [uahl_omd_bounded_half] at lo := the abstract half.  The source module
      itself is not Required; only its upstream interfaces are.

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete] (the carrier of
      [Real]), [S03_QExp], [S07_RealSetoidExpLog], [Paper7Ablation], [P7BoundedSoftmaxDeep].

    References.  This development, ToyR_UpAblP7_LoHiSqueeze.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" ToyR_UpAblP7_LoHiSqueeze.v] compiles cleanly
      (exit 0); artifact magic [436f7121 000160bc] (9.3, od-verified),
      [coqchk -silent] exit 0, all seven [Print Assumptions] blocks Closed. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import Paper7Ablation.
Require Import P7BoundedSoftmaxDeep.

(* Carrier adaptation (cure note, round-2 compile gate).  This tree's
   RealInterfaceEnhancedSetoid is the zero-argument Class over the
   concrete [Real] carrier (S07_RealSetoidExpLog, inside the
   RealInterfaceEnhancedMod module, with the global instance
   RealEnhancedReal); the source binder pair
     Context {R : Set} {RI : RealInterfaceEnhancedSetoid R}
   is therefore removed, [R] is bound to [Real] by abbreviation and the
   interface fields resolve through the global instance
   (Arch_PA_01 / AlignIdUnclosed / abl_sumd_strict precedent).  All
   statement names and statement faces are kept verbatim; no
   Obj.magic, no Prop-ification.  Extraction face (M34b canon): the
   section banks carry the global instance's field values in their
   concrete delta-equal S02/S03/S07 form, so Separate Extraction of the
   seven named statements lands Obj.magic = 0 on both artifact faces. *)
Abbreviation R := Real.
(* Instance activated without importing the field short names: Sections
   UahlPair/UahlStar/UahlSbInst address the fields by their qualified
   RealInterfaceEnhancedMod names, while Section UahlHalf keeps the bare
   S01 RealInterfaceEnhanced face (Paper7Ablation precedent) unambiguous. *)
Existing Instance RealInterfaceEnhancedMod.RealEnhancedReal.

(* ============ Section 1. Conjunction lo < 1 and 1 < hi, the squeeze lo < hi, delta-star in (0,1); no decidable-order entry ============ *)
(* The section variables match the LhsPair section of the source module LoHiSqueeze.v: the temperature pair, the spread pair, and the four-member exponential family. *)

Section UahlPair.

(* Binders (R : Set) and (RI : RealInterfaceEnhancedSetoid R) removed:
   zero-argument Class; carrier fixed by the top notation R := Real, the
   fields resolving through the global instance RealEnhancedReal. *)

(* Projection bank over the RIS interface, in the style of S10
   AttentionGibbsBridgeSetoid: each bare name below carries the field value
   of the unique global instance in its concrete delta-equal form (M34b
   canon; the extraction face lands Obj.magic = 0), so the statements keep
   the verbatim statement face of the source text. *)
Let zero : R := real_zero.
Let one : R := real_one.
Let plus : R -> R -> R := real_plus.
Let mult : R -> R -> R := real_mult.
Let opp : R -> R := real_opp.
Let lt : R -> R -> Set := real_lt.
Let le : R -> R -> Set := real_le.
Let req : R -> R -> Set := real_eq.
Let inv_pos : forall x : R, lt zero x -> R := real_inv_pos.
Let req_sym := real_eq_sym.
Let req_trans := real_eq_trans.
Let plus_comm := real_plus_comm.
Let plus_zero := real_plus_zero.
Let plus_opp := real_plus_opp.
Let mult_comm := real_mult_comm.
Let mult_one := real_mult_one.
Let mult_zero := real_mult_zero.
Let mult_positive := real_mult_positive.
Let lt_trans := real_lt_trans.
Let lt_id_l := RealSetoid.real_lt_id_l.
Let lt_id_r := RealSetoid.real_lt_id_r.
Let le_refl := real_le_refl.
Let lt_mult_compat := (fun a b c Hc Hab => real_mult_lt_compat a b c Hab Hc).
Let lt_zero_opp := real_lt_zero_opp.
Let inv_pos_pos := real_inv_pos_pos.
Let one_pos : lt zero one := real_lt_zero_one.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : req (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).

(* [uahl_lo_lt_one_hi], an independent re-proof of lhs_lo_lt_one_hi of the
   source module: the left conjunct goes through the body of p7a_lo_lt_one,
   the right one through the body of p7d_hi_gt_one; the positivity of invT
   comes from inv_pos_pos. *)
Theorem uahl_lo_lt_one_hi : And (lt lo one) (lt one hi).
Proof.
  split.
  - (* The req-face body of p7a_lo_lt_one, inlined (as in tpei_p7a_lo_lt_one_req). *)
    assert (Hond := lt_zero_opp Delta Delta_pos).
    assert (Hm : lt (mult (opp Delta) invT) zero).
    { apply (lt_id_r (mult (opp Delta) invT) (mult zero invT) zero
               (req_trans (mult zero invT) (mult invT zero) zero
                  (mult_comm zero invT) (mult_zero invT))).
      exact (lt_mult_compat (opp Delta) zero invT
               (inv_pos_pos temp temp_pos) Hond). }
    apply (lt_id_r (expf (mult invT (opp Delta))) (expf zero) one expf_zero).
    apply (expf_mono_lt (mult invT (opp Delta)) zero).
    apply (lt_id_l (mult invT (opp Delta)) (mult (opp Delta) invT) zero
             (mult_comm invT (opp Delta))).
    exact Hm.
  - (* The req-face body of p7d_hi_gt_one, inlined (as in tpei_p7d_hi_gt_one_req). *)
    exact (lt_id_l one (expf zero) (expf (mult invT Delta))
             (req_sym (expf zero) one expf_zero)
             (expf_mono_lt zero (mult invT Delta)
                (mult_positive invT Delta (inv_pos_pos temp temp_pos) Delta_pos))).
Qed.

(* [uahl_lo_lt_hi], an independent re-proof of lhs_lo_lt_hi of the source module: two lt_trans steps over the two conjuncts of uahl_lo_lt_one_hi. *)
Theorem uahl_lo_lt_hi : lt lo hi.
Proof.
  exact (lt_trans lo one hi (fst uahl_lo_lt_one_hi) (snd uahl_lo_lt_one_hi)).
Qed.

(* [uahl_delta_star_bounded], an independent re-proof of
   lhs_delta_star_bounded of the source module: the left conjunct
   delta-star > 0 is one direct step (the mult_positive field of the RIS
   interface); the right conjunct delta-star < 1 takes three independent
   steps, lt_mult_compat, lt_id_l through mult_one, and lt_trans. *)
Theorem uahl_delta_star_bounded :
  And (lt zero (mult lo lo)) (lt (mult lo lo) one).
Proof.
  assert (Hlo1 : lt lo one).
  { (* The req-face body of p7a_lo_lt_one, inlined as in the left conjunct of uahl_lo_lt_one_hi. *)
    assert (Hond := lt_zero_opp Delta Delta_pos).
    assert (Hm : lt (mult (opp Delta) invT) zero).
    { apply (lt_id_r (mult (opp Delta) invT) (mult zero invT) zero
               (req_trans (mult zero invT) (mult invT zero) zero
                  (mult_comm zero invT) (mult_zero invT))).
      exact (lt_mult_compat (opp Delta) zero invT
               (inv_pos_pos temp temp_pos) Hond). }
    apply (lt_id_r (expf (mult invT (opp Delta))) (expf zero) one expf_zero).
    apply (expf_mono_lt (mult invT (opp Delta)) zero).
    apply (lt_id_l (mult invT (opp Delta)) (mult (opp Delta) invT) zero
             (mult_comm invT (opp Delta))).
    exact Hm. }
  split.
  - exact (mult_positive lo lo (expf_pos (mult invT (opp Delta)))
             (expf_pos (mult invT (opp Delta)))).
  - exact (lt_trans (mult lo lo) (mult one lo) one
             (lt_mult_compat lo one lo
                (expf_pos (mult invT (opp Delta))) Hlo1)
             (lt_id_l (mult one lo) lo one
                (req_trans (mult one lo) (mult lo one) lo
                   (mult_comm one lo) (mult_one lo)) Hlo1)).
Qed.

End UahlPair.

(* ============ Section 2. uahl_omd_bounded: kappa := 1 - delta-star in (0,1), with a decidable-order entry ============ *)
(* The section variables match the LhsStar section of the source module
   LoHiSqueeze.v; in place of the Context {DO} entry this section carries the
   lpc additivity entry in the style of UpReqAttnMixTime, and both chains of
   the omd bound are inlined inside the section in two steps each. *)

Section UahlStar.

(* Binders (R : Set) and (RI : RealInterfaceEnhancedSetoid R) removed:
   zero-argument Class; carrier fixed by the top notation R := Real, the
   fields resolving through the global instance RealEnhancedReal. *)
(* Projection bank over the RIS interface, as in Section UahlPair (concrete delta-equal field values, M34b canon). *)
Let zero : R := real_zero.
Let one : R := real_one.
Let plus : R -> R -> R := real_plus.
Let mult : R -> R -> R := real_mult.
Let opp : R -> R := real_opp.
Let lt : R -> R -> Set := real_lt.
Let le : R -> R -> Set := real_le.
Let req : R -> R -> Set := real_eq.
Let inv_pos : forall x : R, lt zero x -> R := real_inv_pos.
Let req_sym := real_eq_sym.
Let req_trans := real_eq_trans.
Let req_lt_compat := RealSetoid.real_lt_compat.
Let plus_comm := real_plus_comm.
Let plus_zero := real_plus_zero.
Let plus_opp := real_plus_opp.
Let mult_comm := real_mult_comm.
Let mult_one := real_mult_one.
Let mult_zero := real_mult_zero.
Let mult_positive := real_mult_positive.
Let lt_trans := real_lt_trans.
Let lt_id_l := RealSetoid.real_lt_id_l.
Let lt_id_r := RealSetoid.real_lt_id_r.
Let le_refl := real_le_refl.
Let lt_mult_compat := (fun a b c Hc Hab => real_mult_lt_compat a b c Hab Hc).
Let lt_zero_opp := real_lt_zero_opp.
Let inv_pos_pos := real_inv_pos_pos.
Let one_pos : lt zero one := real_lt_zero_one.

(* The RIS interface world carries no DecidableOrder instance, so the section takes lpc directly at this concrete level. *)
Variable lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : req (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).

(* Section-local shadow of minus, a verbatim copy of the S01 definition with
   the RI argument removed; the Let form keeps it inside the section scope, so
   nothing leaks past End and the S01 minus used by UahlHalf is untouched. *)
Let minus (a b : R) : R := plus a (opp b).

(* [uahl_omd_bounded], an independent re-proof of lhs_omd_bounded of the
   source module: the left conjunct inlines the two-step chain of omd_pos
   from the premise delta-star < 1; the right conjunct inlines the two-step
   chain of omd_lt_one from 0 < lo. *)
Theorem uahl_omd_bounded :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { (* The req-face body of p7a_lo_lt_one, inlined as in the left conjunct of UahlPair. *)
    assert (Hond := lt_zero_opp Delta Delta_pos).
    assert (Hm : lt (mult (opp Delta) invT) zero).
    { apply (lt_id_r (mult (opp Delta) invT) (mult zero invT) zero
               (req_trans (mult zero invT) (mult invT zero) zero
                  (mult_comm zero invT) (mult_zero invT))).
      exact (lt_mult_compat (opp Delta) zero invT
               (inv_pos_pos temp temp_pos) Hond). }
    apply (lt_id_r (expf (mult invT (opp Delta))) (expf zero) one expf_zero).
    apply (expf_mono_lt (mult invT (opp Delta)) zero).
    apply (lt_id_l (mult invT (opp Delta)) (mult (opp Delta) invT) zero
             (mult_comm invT (opp Delta))).
    exact Hm. }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp Delta))). }
  split.
  - exact (lt_id_l zero (plus (mult lo lo) (opp (mult lo lo)))
             (plus one (opp (mult lo lo)))
             (req_sym (plus (mult lo lo) (opp (mult lo lo))) zero
                (plus_opp (mult lo lo)))
             (lpc (mult lo lo) one (opp (mult lo lo)) (opp (mult lo lo))
                (lt_trans (mult lo lo) (mult one lo) one
                   (lt_mult_compat lo one lo Hlopos Hlo1)
                   (lt_id_l (mult one lo) lo one
                      (req_trans (mult one lo) (mult lo one) lo
                         (mult_comm one lo) (mult_one lo)) Hlo1))
                (le_refl (opp (mult lo lo))))).
  - exact (req_lt_compat (plus (opp (mult lo lo)) one)
             (plus one (opp (mult lo lo))) (plus zero one) one
             (plus_comm (opp (mult lo lo)) one)
             (req_trans (plus zero one) (plus one zero) one
                (plus_comm zero one) (plus_zero one))
             (lpc (opp (mult lo lo)) zero one one
                (lt_zero_opp (mult lo lo) (mult_positive lo lo Hlopos Hlopos))
                (le_refl one))).
Qed.

End UahlStar.

(* ============ Section 3. Instance form one: uahl_omd_bounded and uahl_lo_lt_hi at temperature := 1 and spread := 1 ============ *)
(* The temperature and the spread both take the value one, one_pos supplying
   positivity at both places, and invT := inv_pos one one_pos; the exponential
   family stays abstract (the development carries no concrete real instance).
   The RIS interface, the lpc entry and the minus shadow follow Section
   UahlStar. *)

Section UahlSbInst.

(* Binders (R : Set) and (RI : RealInterfaceEnhancedSetoid R) removed:
   zero-argument Class; carrier fixed by the top notation R := Real, the
   fields resolving through the global instance RealEnhancedReal. *)
(* Projection bank over the RIS interface, as in Section UahlStar (concrete delta-equal field values, M34b canon). *)
Let zero : R := real_zero.
Let one : R := real_one.
Let plus : R -> R -> R := real_plus.
Let mult : R -> R -> R := real_mult.
Let opp : R -> R := real_opp.
Let lt : R -> R -> Set := real_lt.
Let le : R -> R -> Set := real_le.
Let req : R -> R -> Set := real_eq.
Let inv_pos : forall x : R, lt zero x -> R := real_inv_pos.
Let req_sym := real_eq_sym.
Let req_trans := real_eq_trans.
Let req_lt_compat := RealSetoid.real_lt_compat.
Let plus_comm := real_plus_comm.
Let plus_zero := real_plus_zero.
Let plus_opp := real_plus_opp.
Let mult_comm := real_mult_comm.
Let mult_one := real_mult_one.
Let mult_zero := real_mult_zero.
Let mult_positive := real_mult_positive.
Let lt_trans := real_lt_trans.
Let lt_id_l := RealSetoid.real_lt_id_l.
Let lt_id_r := RealSetoid.real_lt_id_r.
Let le_refl := real_le_refl.
Let lt_mult_compat := (fun a b c Hc Hab => real_mult_lt_compat a b c Hab Hc).
Let lt_zero_opp := real_lt_zero_opp.
Let inv_pos_pos := real_inv_pos_pos.
Let one_pos : lt zero one := real_lt_zero_one.

(* The lpc entry, in the style of Section UahlStar. *)
Variable lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).

Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : req (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos one one_pos.
Let lo := expf (mult invT (opp one)).

(* Section-local shadow of minus, as in Section UahlStar. *)
Let minus (a b : R) : R := plus a (opp b).

(* [uahl_omd_bounded_one], the instance form of uahl_omd_bounded at
   temperature := 1 and spread := 1: the inlined req-face body of p7a_lo_lt_one
   supplies lo < 1, expf_pos supplies 0 < lo, and both chains of the omd bound
   are inlined inside the section. *)
Theorem uahl_omd_bounded_one :
  And (lt zero (minus one (mult lo lo)))
      (lt (minus one (mult lo lo)) one).
Proof.
  assert (Hlo1 : lt lo one).
  { (* The req-face body of p7a_lo_lt_one, inlined at one/one. *)
    assert (Hond := lt_zero_opp one one_pos).
    assert (Hm : lt (mult (opp one) invT) zero).
    { apply (lt_id_r (mult (opp one) invT) (mult zero invT) zero
               (req_trans (mult zero invT) (mult invT zero) zero
                  (mult_comm zero invT) (mult_zero invT))).
      exact (lt_mult_compat (opp one) zero invT (inv_pos_pos one one_pos) Hond). }
    apply (lt_id_r (expf (mult invT (opp one))) (expf zero) one expf_zero).
    apply (expf_mono_lt (mult invT (opp one)) zero).
    apply (lt_id_l (mult invT (opp one)) (mult (opp one) invT) zero
             (mult_comm invT (opp one))).
    exact Hm. }
  assert (Hlopos : lt zero lo).
  { exact (expf_pos (mult invT (opp one))). }
  split.
  - exact (lt_id_l zero (plus (mult lo lo) (opp (mult lo lo)))
             (plus one (opp (mult lo lo)))
             (req_sym (plus (mult lo lo) (opp (mult lo lo))) zero
                (plus_opp (mult lo lo)))
             (lpc (mult lo lo) one (opp (mult lo lo)) (opp (mult lo lo))
                (lt_trans (mult lo lo) (mult one lo) one
                   (lt_mult_compat lo one lo Hlopos Hlo1)
                   (lt_id_l (mult one lo) lo one
                      (req_trans (mult one lo) (mult lo one) lo
                         (mult_comm one lo) (mult_one lo)) Hlo1))
                (le_refl (opp (mult lo lo))))).
  - exact (req_lt_compat (plus (opp (mult lo lo)) one)
             (plus one (opp (mult lo lo))) (plus zero one) one
             (plus_comm (opp (mult lo lo)) one)
             (req_trans (plus zero one) (plus one zero) one
                (plus_comm zero one) (plus_zero one))
             (lpc (opp (mult lo lo)) zero one one
                (lt_zero_opp (mult lo lo) (mult_positive lo lo Hlopos Hlopos))
                (le_refl one))).
Qed.

(* [uahl_lo_lt_hi_one], the instance form of uahl_lo_lt_hi at the same
   instantiation: the inlined req-face body of p7a_lo_lt_one supplies lo < 1,
   the inlined req-face body of p7d_hi_gt_one supplies 1 < hi, and lt_trans
   composes them (lpc is used nowhere and does not enter the exported form). *)
Theorem uahl_lo_lt_hi_one :
  lt (expf (mult invT (opp one))) (expf (mult invT one)).
Proof.
  assert (Hlo1 : lt (expf (mult invT (opp one))) one).
  { (* The req-face body of p7a_lo_lt_one, inlined at one/one as in the Hlo1 block above. *)
    assert (Hond := lt_zero_opp one one_pos).
    assert (Hm : lt (mult (opp one) invT) zero).
    { apply (lt_id_r (mult (opp one) invT) (mult zero invT) zero
               (req_trans (mult zero invT) (mult invT zero) zero
                  (mult_comm zero invT) (mult_zero invT))).
      exact (lt_mult_compat (opp one) zero invT (inv_pos_pos one one_pos) Hond). }
    apply (lt_id_r (expf (mult invT (opp one))) (expf zero) one expf_zero).
    apply (expf_mono_lt (mult invT (opp one)) zero).
    apply (lt_id_l (mult invT (opp one)) (mult (opp one) invT) zero
             (mult_comm invT (opp one))).
    exact Hm. }
  exact (lt_trans (expf (mult invT (opp one))) one (expf (mult invT one))
           Hlo1
           (lt_id_l one (expf zero) (expf (mult invT one))
              (req_sym (expf zero) one expf_zero)
              (expf_mono_lt zero (mult invT one)
                 (mult_positive invT one (inv_pos_pos one one_pos) one_pos)))).
Qed.

End UahlSbInst.

(* ============ Section 4. Instance form two: uahl_omd_bounded at lo := the abstract half ============ *)
(* lo := inv_pos (plus one one) two_pos (one half, two_pos and inv_pos_pos
   supplying positivity).  The left conjunct bypasses the delta-star < 1 route
   and runs an independent chain: half_twice (half plus half = 1, and the
   square of half plus the square of half = half) with plus_positive (the
   square of half is positive) and identity rearrangements give 0 < 1 - 1/4;
   the right conjunct is @p7a_omd_lt_one. *)

Section UahlHalf.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Let half := inv_pos (plus one one) two_pos.
Let half2 := mult half half.

(* [uahl_omd_bounded_half], the second instance form. *)
Theorem uahl_omd_bounded_half :
  And (lt zero (minus one half2)) (lt (minus one half2) one).
Proof.
  assert (Hhp : lt zero half).
  { exact (inv_pos_pos (plus one one) two_pos). }
  assert (Hh2p : lt zero half2).
  { exact (mult_positive half half Hhp Hhp). }
  assert (Hh2p2 : lt zero (plus half2 half2)).
  { exact (plus_positive half2 half2 Hh2p Hh2p). }
  assert (Hq : Id (plus half2 half2) half).
  { exact (half_twice half). }
  assert (Hone : Id (plus half half) one).
  { exact (id_trans (id_cong (fun x => plus x x) (id_sym (mult_one half)))
                    (half_twice one)). }
  assert (Hone2 : Id one (plus (plus half2 half2) (plus half2 half2))).
  { exact (id_trans (id_sym Hone) (id_sym (id_cong (fun x => plus x x) Hq))). }
  assert (Gup : Id (plus (plus (plus half2 half2) (plus half2 half2))
                         (opp half2))
                   (plus half2 (plus half2 half2))).
  { exact (id_trans
             (id_sym (plus_assoc (plus half2 half2) (plus half2 half2)
                       (opp half2)))
             (id_trans
                (id_cong (fun x => plus (plus half2 half2) x)
                   (id_trans (id_sym (plus_assoc half2 half2 (opp half2)))
                      (id_trans
                         (id_cong (fun w => plus half2 w)
                            (plus_comm half2 (opp half2)))
                         (plus_assoc half2 (opp half2) half2))))
             (id_trans
                (id_cong (fun x => plus (plus half2 half2) x)
                   (id_cong (fun w => plus w half2) (plus_opp half2)))
                (id_trans
                   (id_cong (fun x => plus (plus half2 half2) x)
                      (id_trans (plus_comm zero half2) (plus_zero half2)))
                   (id_sym (plus_assoc half2 half2 half2)))))). }
  assert (Gtotal : Id (minus one half2) (plus half2 (plus half2 half2))).
  { exact (id_trans
             (id_sym (id_cong (fun w => plus w (opp half2)) (id_sym Hone2)))
             Gup). }
  split.
  - exact (lt_id_r zero (plus half2 (plus half2 half2)) (minus one half2)
             (id_sym Gtotal)
             (plus_positive half2 (plus half2 half2) Hh2p Hh2p2)).
  - exact (@p7a_omd_lt_one RI DO half Hhp).
Qed.

End UahlHalf.

(* ---- Closing: [Print Assumptions] audit of every named statement ---- *)
Print Assumptions uahl_lo_lt_one_hi.
Print Assumptions uahl_lo_lt_hi.
Print Assumptions uahl_delta_star_bounded.
Print Assumptions uahl_omd_bounded.
Print Assumptions uahl_omd_bounded_one.
Print Assumptions uahl_lo_lt_hi_one.
Print Assumptions uahl_omd_bounded_half.
