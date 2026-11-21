(* ==========================================================================
   abl_c1_lohi
   Mission. A named witness family for the five section-variable
     packages of the lo/hi squeeze development UpAblP7_LoHiSqueeze:
     the exponential witness expf := fun x => exp_neg (opp x) with
     its three certificates (strict positivity, the zero identity,
     strict monotonicity by contravariant composition); the instance
     data temp := Delta := one (invT := inv_pos one one_pos,
     lo := expf(invT * (-1)), hi := expf(invT * 1)); and the ten host
     statements closed at the fully-applied form, one anchor per
     slot (five/five/five/five/three).
   Dependencies. S01_BaseRing (Set carriers Id/And, the class
     RealInterfaceEnhanced with the exp_neg field family,
     opp_lt_compat, one_pos, inv_pos, plus_inv_unique, the identity
     combinators id_trans/id_cong); UpAblP7_LoHiSqueeze (the host
     statement families lhs_*/uahl_*, consumed fully applied).
   References. UpAblP7_LoHiSqueeze.v (sections LhsPair, LhsStar,
     UahlPair, UahlStar, UahlSbInst); UpAblD1_expf_pack.v
     (uabd1x_expf_zero, the real_eq-face variant of the same
     witness construction); S01_BaseRing.v (exp_neg field family).
   Constructivity. Statement faces Set-carried (interface lt, the Id
     inductive, the And product; no Prop component in statements or
     binders); proofs are term-mode assemblies of class fields and
     host lemmas; no admits, no classical logic; every theorem
     transparent (Defined); Print Assumptions checks all 37 names;
     Separate Extraction carries Obj.magic = 0 as the build gate.
   Build. coqc -Q ConstructiveWorld_Live "" abl_c1_lohi.v (Rocq 9.3
     toolchain, thermal-guard wrapped; dependencies loaded read-only
     from the ConstructiveWorld_Live .vo pool).
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import UpAblP7_LoHiSqueeze.

Existing Instance RI_base.

(* ============================================================ *)
(* Part 1. The witness core: expf := exp_neg composed with opp.     *)
(*   This is the generic Id-face exponential witness over an        *)
(*   arbitrary RealInterfaceEnhanced carrier (the real_eq-face      *)
(*   precedent uabd1x_expf does not fit the Id-face slots).         *)
(*   Four transparent proofs.                                       *)
(* ============================================================ *)

Definition c1_expf (RI : RealInterfaceEnhanced) : R -> R :=
  fun x => exp_neg (opp x).

(* Negation maps zero to zero: the three-step plus_inv_unique chain
   (same assembly as the in-library precedent at S01_BaseRing), a
   purely class-field construction. *)
Lemma c1_opp_zero : forall RI : RealInterfaceEnhanced, Id (opp zero) zero.
Proof.
  intros RI.
  apply (plus_inv_unique zero (opp zero) zero).
  - exact (plus_opp zero).
  - exact (plus_zero zero).
Defined.

(* The witness identity: Id (c1_expf zero) one -- c1_opp_zero, then
   congruence under exp_neg via id_cong, closed by the class field
   exp_neg_zero. *)
Theorem c1_expf_zero : forall RI : RealInterfaceEnhanced,
  Id (c1_expf RI zero) one.
Proof.
  intros RI.
  apply (id_trans (id_cong exp_neg (c1_opp_zero RI))).
  exact exp_neg_zero.
Defined.

(* Certificate A: strict positivity of expf at every point --
   exp_neg_pos applied at the negated argument, universally given. *)
Theorem c1_expf_pos : forall (RI : RealInterfaceEnhanced) (x : R),
  lt zero (c1_expf RI x).
Proof. intros RI x. exact (exp_neg_pos (opp x)). Defined.

(* Certificate B: strict monotonicity of expf -- opp_lt_compat is
   contravariant in opp and exp_neg_decr is contravariant in exp_neg;
   two contravariances compose to a covariant map. *)
Theorem c1_expf_mono_lt : forall (RI : RealInterfaceEnhanced) (a b : R),
  lt a b -> lt (c1_expf RI a) (c1_expf RI b).
Proof.
  intros RI a b H.
  exact (exp_neg_decr (opp b) (opp a) (opp_lt_compat a b H)).
Defined.

(* ============================================================ *)
(* Part 2. The instance data: temp := Delta := one (the applied     *)
(*   form of the host sectionLets, in named form).  one_pos         *)
(*   discharges both positivity slots; lo/hi match the host section *)
(*   let-shapes literally.                                          *)
(* ============================================================ *)

Definition c1_invT (RI : RealInterfaceEnhanced) : R := inv_pos one one_pos.
Definition c1_lo (RI : RealInterfaceEnhanced) : R :=
  c1_expf RI (mult (c1_invT RI) (opp one)).
Definition c1_hi (RI : RealInterfaceEnhanced) : R :=
  c1_expf RI (mult (c1_invT RI) one).

(* ============================================================ *)
(* Part 3. Witness anchors for the five slot packages of the host   *)
(*   sections (one named closed witness per section slot).          *)
(* ============================================================ *)

(* ---- Package 1: the LhsPair slots (temp_pos, Delta_pos,
        expf_pos, expf_zero, expf_mono_lt at the applied form
        temp := Delta := one, expf := c1_expf) ---- *)

Theorem c1_lhsp_temp_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Defined.

Theorem c1_lhsp_Delta_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Defined.

Theorem c1_lhsp_expf_pos : forall (RI : RealInterfaceEnhanced) (x : R),
  lt zero (c1_expf RI x).
Proof. intros RI x. exact (c1_expf_pos RI x). Defined.

Theorem c1_lhsp_expf_zero : forall RI : RealInterfaceEnhanced,
  Id (c1_expf RI zero) one.
Proof. intros RI. exact (c1_expf_zero RI). Defined.

Theorem c1_lhsp_expf_mono_lt : forall (RI : RealInterfaceEnhanced) (a b : R),
  lt a b -> lt (c1_expf RI a) (c1_expf RI b).
Proof. intros RI a b H. exact (c1_expf_mono_lt RI a b H). Defined.

(* ---- Package 2: the LhsStar slots (the same five slots) ---- *)

Theorem c1_lhss_temp_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Defined.

Theorem c1_lhss_Delta_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Defined.

Theorem c1_lhss_expf_pos : forall (RI : RealInterfaceEnhanced) (x : R),
  lt zero (c1_expf RI x).
Proof. intros RI x. exact (c1_expf_pos RI x). Defined.

Theorem c1_lhss_expf_zero : forall RI : RealInterfaceEnhanced,
  Id (c1_expf RI zero) one.
Proof. intros RI. exact (c1_expf_zero RI). Defined.

Theorem c1_lhss_expf_mono_lt : forall (RI : RealInterfaceEnhanced) (a b : R),
  lt a b -> lt (c1_expf RI a) (c1_expf RI b).
Proof. intros RI a b H. exact (c1_expf_mono_lt RI a b H). Defined.

(* ---- Package 3: the UahlPair slots (the same five slots) ---- *)

Theorem c1_uahp_temp_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Defined.

Theorem c1_uahp_Delta_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Defined.

Theorem c1_uahp_expf_pos : forall (RI : RealInterfaceEnhanced) (x : R),
  lt zero (c1_expf RI x).
Proof. intros RI x. exact (c1_expf_pos RI x). Defined.

Theorem c1_uahp_expf_zero : forall RI : RealInterfaceEnhanced,
  Id (c1_expf RI zero) one.
Proof. intros RI. exact (c1_expf_zero RI). Defined.

Theorem c1_uahp_expf_mono_lt : forall (RI : RealInterfaceEnhanced) (a b : R),
  lt a b -> lt (c1_expf RI a) (c1_expf RI b).
Proof. intros RI a b H. exact (c1_expf_mono_lt RI a b H). Defined.

(* ---- Package 4: the UahlStar slots (the same five slots) ---- *)

Theorem c1_uahs_temp_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Defined.

Theorem c1_uahs_Delta_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Defined.

Theorem c1_uahs_expf_pos : forall (RI : RealInterfaceEnhanced) (x : R),
  lt zero (c1_expf RI x).
Proof. intros RI x. exact (c1_expf_pos RI x). Defined.

Theorem c1_uahs_expf_zero : forall RI : RealInterfaceEnhanced,
  Id (c1_expf RI zero) one.
Proof. intros RI. exact (c1_expf_zero RI). Defined.

Theorem c1_uahs_expf_mono_lt : forall (RI : RealInterfaceEnhanced) (a b : R),
  lt a b -> lt (c1_expf RI a) (c1_expf RI b).
Proof. intros RI a b H. exact (c1_expf_mono_lt RI a b H). Defined.

(* ---- Package 5: the UahlSbInst slots (the three exponential
        slots; the instance form fixes temp := Delta := one) ---- *)

Theorem c1_uasi_expf_pos : forall (RI : RealInterfaceEnhanced) (x : R),
  lt zero (c1_expf RI x).
Proof. intros RI x. exact (c1_expf_pos RI x). Defined.

Theorem c1_uasi_expf_zero : forall RI : RealInterfaceEnhanced,
  Id (c1_expf RI zero) one.
Proof. intros RI. exact (c1_expf_zero RI). Defined.

Theorem c1_uasi_expf_mono_lt : forall (RI : RealInterfaceEnhanced) (a b : R),
  lt a b -> lt (c1_expf RI a) (c1_expf RI b).
Proof. intros RI a b H. exact (c1_expf_mono_lt RI a b H). Defined.

(* ============================================================ *)
(* Part 4. The ten host statements closed at the fully-applied      *)
(*   form: with the witness family in place, every host statement   *)
(*   holds for c1_expf at the instance data temp := Delta := one.   *)
(*   The DecidableOrder premise is carried explicitly in the        *)
(*   closures whose host lemma requires it; the host instance form  *)
(*   at lo := one half lies outside the scope of this family.       *)
(* ============================================================ *)

(* ---- The LhsPair closures (no DecidableOrder premise) ---- *)

Theorem c1_lhs_lo_lt_one_hi_closed :
  forall RI : RealInterfaceEnhanced, And (lt (c1_lo RI) one) (lt one (c1_hi RI)).
Proof.
  intros RI.
  exact (@lhs_lo_lt_one_hi RI one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Defined.

Theorem c1_lhs_lo_lt_hi_closed :
  forall RI : RealInterfaceEnhanced, lt (c1_lo RI) (c1_hi RI).
Proof.
  intros RI.
  exact (@lhs_lo_lt_hi RI one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Defined.

Theorem c1_lhs_delta_star_bounded_closed :
  forall RI : RealInterfaceEnhanced,
    And (lt zero (mult (c1_lo RI) (c1_lo RI)))
        (lt (mult (c1_lo RI) (c1_lo RI)) one).
Proof.
  intros RI.
  exact (@lhs_delta_star_bounded RI one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Defined.

(* ---- The LhsStar closure (carries the DecidableOrder premise) ---- *)

Theorem c1_lhs_omd_bounded_closed :
  forall (RI : RealInterfaceEnhanced) (DO : DecidableOrder RI),
    And (lt zero (minus one (mult (c1_lo RI) (c1_lo RI))))
        (lt (minus one (mult (c1_lo RI) (c1_lo RI))) one).
Proof.
  intros RI DO.
  exact (@lhs_omd_bounded RI DO one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Defined.

(* ---- The UahlPair closures (no DecidableOrder premise) ---- *)

Theorem c1_uahp_lo_lt_one_hi_closed :
  forall RI : RealInterfaceEnhanced, And (lt (c1_lo RI) one) (lt one (c1_hi RI)).
Proof.
  intros RI.
  exact (@uahl_lo_lt_one_hi RI one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Defined.

Theorem c1_uahp_lo_lt_hi_closed :
  forall RI : RealInterfaceEnhanced, lt (c1_lo RI) (c1_hi RI).
Proof.
  intros RI.
  exact (@uahl_lo_lt_hi RI one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Defined.

Theorem c1_uahp_delta_star_bounded_closed :
  forall RI : RealInterfaceEnhanced,
    And (lt zero (mult (c1_lo RI) (c1_lo RI)))
        (lt (mult (c1_lo RI) (c1_lo RI)) one).
Proof.
  intros RI.
  exact (@uahl_delta_star_bounded RI one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Defined.

(* ---- The UahlStar closure (carries the DecidableOrder premise) ---- *)

Theorem c1_uahs_omd_bounded_closed :
  forall (RI : RealInterfaceEnhanced) (DO : DecidableOrder RI),
    And (lt zero (minus one (mult (c1_lo RI) (c1_lo RI))))
        (lt (minus one (mult (c1_lo RI) (c1_lo RI))) one).
Proof.
  intros RI DO.
  exact (@uahl_omd_bounded RI DO one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Defined.

(* ---- The UahlSbInst closures: uahl_omd_bounded_one carries the
        DecidableOrder premise (its host proof applies p7a_omd_pos
        with DO); uahl_lo_lt_hi_one does not (its host proof stays
        inside the section without DO).  One closure per actual
        post-section signature. ---- *)

Theorem c1_uasi_omd_bounded_one_closed :
  forall (RI : RealInterfaceEnhanced) (DO : DecidableOrder RI),
    And (lt zero (minus one (mult (c1_lo RI) (c1_lo RI))))
        (lt (minus one (mult (c1_lo RI) (c1_lo RI))) one).
Proof.
  intros RI DO.
  exact (@uahl_omd_bounded_one RI DO (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Defined.

Theorem c1_uasi_lo_lt_hi_one_closed :
  forall RI : RealInterfaceEnhanced, lt (c1_lo RI) (c1_hi RI).
Proof.
  intros RI.
  exact (@uahl_lo_lt_hi_one RI (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Defined.

(* ============================================================ *)
(* Part 5. Self-check, first gate: Print Assumptions over all 37    *)
(*   names (every display must read Closed under the global         *)
(*   context).                                                      *)
(* ============================================================ *)
Print Assumptions c1_opp_zero.
Print Assumptions c1_expf_zero.
Print Assumptions c1_expf_pos.
Print Assumptions c1_expf_mono_lt.
Print Assumptions c1_lhsp_temp_pos.
Print Assumptions c1_lhsp_Delta_pos.
Print Assumptions c1_lhsp_expf_pos.
Print Assumptions c1_lhsp_expf_zero.
Print Assumptions c1_lhsp_expf_mono_lt.
Print Assumptions c1_lhss_temp_pos.
Print Assumptions c1_lhss_Delta_pos.
Print Assumptions c1_lhss_expf_pos.
Print Assumptions c1_lhss_expf_zero.
Print Assumptions c1_lhss_expf_mono_lt.
Print Assumptions c1_uahp_temp_pos.
Print Assumptions c1_uahp_Delta_pos.
Print Assumptions c1_uahp_expf_pos.
Print Assumptions c1_uahp_expf_zero.
Print Assumptions c1_uahp_expf_mono_lt.
Print Assumptions c1_uahs_temp_pos.
Print Assumptions c1_uahs_Delta_pos.
Print Assumptions c1_uahs_expf_pos.
Print Assumptions c1_uahs_expf_zero.
Print Assumptions c1_uahs_expf_mono_lt.
Print Assumptions c1_uasi_expf_pos.
Print Assumptions c1_uasi_expf_zero.
Print Assumptions c1_uasi_expf_mono_lt.
Print Assumptions c1_lhs_lo_lt_one_hi_closed.
Print Assumptions c1_lhs_lo_lt_hi_closed.
Print Assumptions c1_lhs_delta_star_bounded_closed.
Print Assumptions c1_lhs_omd_bounded_closed.
Print Assumptions c1_uahp_lo_lt_one_hi_closed.
Print Assumptions c1_uahp_lo_lt_hi_closed.
Print Assumptions c1_uahp_delta_star_bounded_closed.
Print Assumptions c1_uahs_omd_bounded_closed.
Print Assumptions c1_uasi_omd_bounded_one_closed.
Print Assumptions c1_uasi_lo_lt_hi_one_closed.

(* ============================================================ *)
(* Part 6. Self-check, second gate: the extraction discharge.  A    *)
(*   single Separate Extraction command covering the witness core   *)
(*   and all 23 slot anchors; Obj.magic must stay absent from       *)
(*   both extraction products.                                      *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Separate Extraction c1_expf c1_opp_zero c1_expf_zero c1_expf_pos
  c1_expf_mono_lt c1_lhsp_temp_pos c1_lhsp_Delta_pos c1_lhsp_expf_pos
  c1_lhsp_expf_zero c1_lhsp_expf_mono_lt c1_lhss_temp_pos c1_lhss_Delta_pos
  c1_lhss_expf_pos c1_lhss_expf_zero c1_lhss_expf_mono_lt c1_uahp_temp_pos
  c1_uahp_Delta_pos c1_uahp_expf_pos c1_uahp_expf_zero c1_uahp_expf_mono_lt
  c1_uahs_temp_pos c1_uahs_Delta_pos c1_uahs_expf_pos c1_uahs_expf_zero
  c1_uahs_expf_mono_lt c1_uasi_expf_pos c1_uasi_expf_zero c1_uasi_expf_mono_lt.
