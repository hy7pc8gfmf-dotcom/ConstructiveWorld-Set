(* ========================================================================= *)
(* Module   : LW3ExclusionCalc                                              *)
(* Mission. Exclusion-witness calculator for rational approximation of pi:  *)
(*   for q : Q and a separation constant c with 0 < c strictly below the    *)
(*   pointwise distance d(pi, q), assemble the self-contained seal          *)
(*   lw3x_seal = (c, 0 < c, the separation fact, Leibniz envelope endpoints *)
(*   [lo, hi] around pi (rational-envelope formulas), decider bit b, and a  *)
(*   branch bit carrying QltT hi q or QltT q lo);                           *)
(*   lw3x_band_excl forces hi < q from band width hi - lo < c and lo <= q;  *)
(*   lw3x_pi_geom_seal_slot transports separation from the geometric pi     *)
(*   representation to the Leibniz-series one at halved radius;             *)
(*   lw3x_env_supply exposes the endpoint pair for any eps > 0.            *)
(* Dependencies. Stdlib QArith/Qabs/Arith/Lia/Lqa; LW0LeibWindow            *)
(*   (leiblw_Qltb), S01_BaseRing, S02_CauchyComplete (Real/real_lt/QltT/    *)
(*   QleT'/QeqT, cauchy_real_pi_leibniz), S03_QExp, S10_KVQuantTrig         *)
(*   (real_pi_geom), UpReqIrrationalCriterion (lic_metric_proj),            *)
(*   PiEnvelope (pi_rational_envelope), LW2SepTransport                     *)
(*   (lw2t_sep_transport), S11_TP3B5 (channel_f1, a3_h4_value_bridge,       *)
(*   b5b_hsc_theorem), S14_B5BatchBlock (b5dS_E_zero_on_unit).             *)
(* References. Endpoint formulas follow PiEnvelope's pi_rational_envelope;  *)
(*   transport is lw2t_sep_transport at c/2; channel input S14 b5dS.       *)
(* Constructivity. Statement faces are Set-carried (sigT/And/real_lt/QltT/  *)
(*   QleT'/QeqT/bool); the seal's decision branch is a bool-indexed QltT    *)
(*   pair, so the Set carrier embeds zero Prop components. All bodies are   *)
(*   Defined-transparent with no Qed (no pure-Prop bridge to justify one);  *)
(*   Prop derivations (QltT_to_Qlt, Lqa on Q, lia on Z) stay in proofs;     *)
(*   zero axioms, zero admits, zero classical principles, no vm_compute.   *)
(* Build. coqc -native-compiler no -q -Q <Live tree root> ""                *)
(*   LW3ExclusionCalc.v (workdir = the piece directory).                   *)
(* ========================================================================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia Lqa.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import UpReqIrrationalCriterion.
Require Import PiEnvelope.
Require Import LW0LeibWindow.
Require Import LW2SepTransport.
Require Import S11_TP3B5.
Require Import S14_B5BatchBlock.

(* ============================================================ *)
(* Section 1. computation core: the outer-side decider bit and  *)
(* the envelope endpoint selectors (all Defined, extractable)   *)
(* ============================================================ *)

(* outer-side decider bit: true exactly when q < lo. The boolean
   comparator is leiblw_Qltb (LW0LeibWindow), whose body coincides with
   the Qlt_bool comparator of S02_CauchyComplete. *)
Definition lw3x_sideb (q lo : Q) : bool := leiblw_Qltb q lo.

(* envelope endpoint selectors, literally the witness formulas of
   pi_rational_envelope (lo := 4*pi_partial(2*pi_modulus(eps/2)+2) - eps/4,
   hi := 4*pi_partial(2*pi_modulus(eps/2)+1) + eps/4); the upstream
   pie_partial/pie_modulus are transparent, so the chain is extractable. *)
Definition lw3x_env_lo (eps : Q) : Q :=
  4 * pie_partial (2 * pie_modulus (eps / 2) + 2) - eps / 4.
Definition lw3x_env_hi (eps : Q) : Q :=
  4 * pie_partial (2 * pie_modulus (eps / 2) + 1) + eps / 4.

(* decider reflection law: a true bit carries QltT q lo. *)
Lemma lw3x_sideb_spec : forall q lo : Q, lw3x_sideb q lo = true -> QltT q lo.
Proof.
  intros q lo H. unfold QltT.
  change (Qlt_bool q lo = true) in H.
  rewrite H. apply id_refl.
Defined.

(* Branch witness for the exclusion seal: a two-constructor Set   *)
(* carrier carrying the pointwise face of the active side. A      *)
(* dependent match over the branch bit inside the seal type would *)
(* cast at the extraction face, so the two arms are proper        *)
(* constructors instead.                                          *)
Inductive lw3x_branch (q lo hi : Q) : Set :=
| lw3x_lo_side : QltT q lo -> lw3x_branch q lo hi
| lw3x_hi_side : QltT hi q -> lw3x_branch q lo hi.

(* ============================================================ *)
(* Section 2. the exclusion seal: a Set-layer existential package *)
(* (constant c with its positivity, the separation fact, the     *)
(* envelope endpoints, the decider bit, and the branch witness;  *)
(* the branch is the two-constructor lw3x_branch carrier,        *)
(* keeping the seal free of Prop components and of dependent     *)
(* matches)                                                      *)
(* ============================================================ *)

Definition lw3x_seal (q c : Q) : Set :=
  sigT (fun c' : Q =>
    sigT (fun _ : QltT 0 c' =>
      sigT (fun _ : real_lt (real_const c')
                       (real_metric cauchy_real_pi_leibniz (real_const q)) =>
        sigT (fun lo : Q =>
          sigT (fun hi : Q =>
            sigT (fun b : bool =>
              And (real_lt (real_const lo) cauchy_real_pi_leibniz)
                  (And (real_lt cauchy_real_pi_leibniz (real_const hi))
                       (lw3x_branch q lo hi)))))))).

(* ============================================================ *)
(* Section 3. band-incompatibility lemma: if the endpoint band   *)
(* width is strictly below the separation radius and lo <= q,    *)
(* the pointwise sandwich and the separation lower bound are     *)
(* incompatible, forcing hi < q.                                 *)
(* ============================================================ *)

Theorem lw3x_band_excl : forall (q c lo hi : Q),
  QltT 0 c ->
  real_lt (real_const c) (real_metric cauchy_real_pi_leibniz (real_const q)) ->
  real_lt (real_const lo) cauchy_real_pi_leibniz ->
  real_lt cauchy_real_pi_leibniz (real_const hi) ->
  QltT' (hi - lo) c ->
  QleT' lo q ->
  QltT hi q.
Proof.
  intros q c lo hi Hc Hsep Hlo Hhi Hw Hqlo.
  apply Qlt_to_QltT.
  pose proof (QltT_to_Qlt 0 c Hc) as HcQ.
  pose proof (QltT_to_Qlt (hi - lo) c (QltT'_to_Qlt (hi - lo) c Hw)) as HwQ.
  pose proof (QleT'_to_Qle lo q Hqlo) as HqloQ.
  destruct Hlo as [eps1 [Hpos1 [N1 HN1]]].
  destruct Hhi as [eps2 [Hpos2 [N2 HN2]]].
  destruct Hsep as [eps0 [Heps0 [N3 HN3]]].
  pose proof (QltT_to_Qlt 0 eps1 Hpos1) as Hp1pos.
  pose proof (QltT_to_Qlt 0 eps2 Hpos2) as Hp2pos.
  pose proof (QltT_to_Qlt 0 eps0 Heps0) as Hp0pos.
  pose (m := Nat.max (Nat.max N1 N2) N3).
  assert (Hn1 : NatLe N1 m).
  { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2).
    - apply Nat.le_max_l.
    - apply Nat.le_max_l. }
  assert (Hn2 : NatLe N2 m).
  { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2).
    - apply Nat.le_max_r.
    - apply Nat.le_max_l. }
  assert (Hn3 : NatLe N3 m).
  { apply NatLe_lift. apply Nat.le_max_r. }
  pose proof (HN1 m Hn1) as Hp1.
  pose proof (HN2 m Hn2) as Hp2.
  pose proof (HN3 m Hn3) as Hp3.
  apply QltT_to_Qlt in Hp1.
  apply QltT_to_Qlt in Hp2.
  apply QltT_to_Qlt in Hp3.
  rewrite (lic_metric_proj cauchy_real_pi_leibniz q m) in Hp3.
  rewrite (qeqT_imp_qeq _ _ (real_const_proj c m)) in Hp3.
  rewrite (qeqT_imp_qeq _ _ (real_const_proj lo m)) in Hp1.
  rewrite (qeqT_imp_qeq _ _ (real_const_proj hi m)) in Hp2.
  (* pointwise layer: pi_m sits within eps1/eps2 of lo/hi and the
     separation lower bound c + eps0 acts on |pi_m - q|; the absolute
     value splits by the sign of pi_m - q. Non-negative branch: the
     sandwich forces hi - lo > c + eps0 + eps2, contradicting the width
     bound; negative branch: q > pi_m + c + eps0 > lo + c + eps1 + eps0
     > hi. *)
  destruct (Qlt_le_dec (projT1 cauchy_real_pi_leibniz m - q)%Q 0)
    as [Hsign | Hsign].
  - assert (Hle0 : Qle (projT1 cauchy_real_pi_leibniz m - q)%Q 0)
      by (apply Qlt_le_weak; exact Hsign).
    rewrite (Qabs_neg (projT1 cauchy_real_pi_leibniz m - q)%Q Hle0) in Hp3.
    lra.
  - rewrite (Qabs_pos (projT1 cauchy_real_pi_leibniz m - q)%Q Hsign) in Hp3.
    lra.
Defined.

(* ============================================================ *)
(* Section 4. main statement: q in, exclusion seal out (the      *)
(* separation premise sits in premise position, since inside     *)
(* the envelope band both branches fail without it)              *)
(* ============================================================ *)

Theorem lw3x_calc : forall (q c : Q),
  QltT 0 c ->
  real_lt (real_const c) (real_metric cauchy_real_pi_leibniz (real_const q)) ->
  lw3x_seal q c.
Proof.
  intros q c Hc Hsep.
  destruct (pi_rational_envelope c (Qlt_to_QltT' 0 c (QltT_to_Qlt 0 c Hc)))
    as [lo [hi [Hlo [Hhi Hw]]]].
  exists c.
  exists Hc.
  exists Hsep.
  exists lo.
  exists hi.
  exists (lw3x_sideb q lo).
  split.
  - exact Hlo.
  - split.
    + exact Hhi.
    + destruct (lw3x_sideb q lo) eqn:Eb.
      * (* decider true: q < lo, the lo-side branch carries QltT q lo *)
        exact (lw3x_lo_side q lo hi (lw3x_sideb_spec q lo Eb)).
      * (* decider false: lo <= q, band incompatibility forces QltT hi q *)
        destruct (Qlt_le_dec q lo) as [Hlt | Hge].
        -- exfalso.
           assert (HbT : leiblw_Qltb q lo = true).
           { destruct (leiblw_Qltb_true q lo Hlt); reflexivity. }
           unfold lw3x_sideb in Eb. rewrite HbT in Eb. discriminate.
        -- exact (lw3x_hi_side q lo hi
                    (lw3x_band_excl q c lo hi Hc Hsep Hlo Hhi Hw
                       (Qle_to_QleT' lo q Hge))).
Defined.

(* ============================================================ *)
(* Section 5. the two-representation channel and the separation  *)
(* theorem under the geometric representation                    *)
(* ============================================================ *)

(* closed form of the two-representation equality channel: the
   channel_f1 instance assembled from the value bridge 4*arctan(1) == pi_L
   and the sin(arctan 1) == cos(arctan 1) face instantiated by
   b5b_hsc_theorem from the E(1) == 0 supply b5dS_E_zero_on_unit. *)
Definition lw3x_channel_f1_closed : real_eq real_pi_geom cauchy_real_pi_leibniz :=
  channel_f1 a3_h4_value_bridge (b5b_hsc_theorem b5dS_E_zero_on_unit).

(* positivity of c/2: Q division arithmetic, same pattern as the
   eps/4 positivity segment of the rational envelope. *)
Lemma lw3x_c2_pos : forall c : Q, QltT 0 c -> QltT 0 (c / 2)%Q.
Proof.
  intros c Hc. apply Qlt_to_QltT. unfold Qdiv.
  apply (Qmult_lt_0_compat c (/ (2 # 1))).
  - apply QltT_to_Qlt. exact Hc.
  - apply Qinv_lt_0_compat. unfold Qlt; simpl; lia.
Defined.

(* transport and packaging: given 0 < c and the pointwise separation of
   the geometric representation real_pi_geom from the rational point a/b,
   the transport theorem lw2t_sep_transport through the channel above
   halves the radius to c/2 for the Leibniz-series representation, and
   the main theorem then produces the exclusion seal. *)
Theorem lw3x_pi_geom_seal_slot :
  forall (a b c : Q),
    QltT 0 c ->
    real_lt (real_const c) (real_metric real_pi_geom (real_const (a / b))) ->
    lw3x_seal (a / b) (c / 2)%Q.
Proof.
  intros a b c Hc Hsep.
  apply (lw3x_calc (a / b) (c / 2)%Q).
  - exact (lw3x_c2_pos c Hc).
  - exact (lw2t_sep_transport real_pi_geom cauchy_real_pi_leibniz
             (a / b) c Hc lw3x_channel_f1_closed Hsep).
Defined.

(* ============================================================ *)
(* Section 6. transparent supply theorem for the Leibniz         *)
(* endpoint envelope                                             *)
(* ============================================================ *)

(* envelope supply: for any positive eps the endpoint pair
   (lw3x_env_lo eps, lw3x_env_hi eps) satisfies lo < pi < hi with band
   width hi - lo < eps; a transparent restatement of the same assembly
   as pi_rational_envelope, with the endpoint data face fully explicit
   (Defined) for downstream statements that consume the endpoints. *)
Definition lw3x_env_supply (eps : Q) (Heps : QltT' 0 eps) :
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_lt (real_const lo) cauchy_real_pi_leibniz)
        (And (real_lt cauchy_real_pi_leibniz (real_const hi))
             (QltT' (hi - lo) eps)))).
Proof.
  assert (HepsQ : Qlt 0 eps)
    by (apply (QltT_to_Qlt 0 eps (QltT'_to_Qlt 0 eps Heps))).
  assert (Hc4 : Qlt 0 (eps / 4)).
  { unfold Qdiv. apply (Qmult_lt_0_compat eps (/ (4 # 1))).
    - exact HepsQ.
    - apply Qinv_lt_0_compat. unfold Qlt; simpl; lia. }
  assert (Hc2 : Qlt 0 (eps / 2)).
  { unfold Qdiv. apply (Qmult_lt_0_compat eps (/ (2 # 1))).
    - exact HepsQ.
    - apply Qinv_lt_0_compat. unfold Qlt; simpl; lia. }
  assert (Hb : Qlt (4 * pie_mag (2 * pie_modulus (eps / 2) + 1)) (eps / 2)).
  { apply (Qle_lt_trans _ (4 * pie_mag (pie_modulus (eps / 2))) _).
    - apply (QleT'_to_Qle _ _). apply pie_mult4_le.
      apply (QleT'_to_Qle _ _). apply pie_mag_antitone. lia.
    - exact (QltT_to_Qlt _ _ (pie_modulus_bound (eps / 2) Hc2)). }
  exists (lw3x_env_lo eps).
  exists (lw3x_env_hi eps).
  unfold lw3x_env_lo, lw3x_env_hi.
  split.
  - apply (pie_real_lower_gen (pie_modulus (eps / 2)) (eps / 4)
            (4 * pie_partial (2 * pie_modulus (eps / 2) + 2) - eps / 4)).
    + exact Hc4.
    + apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT. ring.
  - split.
    + apply (pie_real_upper_gen (pie_modulus (eps / 2)) (eps / 4)
              (4 * pie_partial (2 * pie_modulus (eps / 2) + 1) + eps / 4)).
      * exact Hc4.
      * apply Qle_refl.
    + apply Qlt_to_QltT'.
      replace (2 * pie_modulus (eps / 2) + 2)%nat
        with (Datatypes.S (2 * pie_modulus (eps / 2) + 1))%nat by lia.
      assert (Hgap : 4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
                     - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1))
                     == 4 * pie_mag (2 * pie_modulus (eps / 2) + 1)).
      { assert (Hg := pie_gap1 (2 * pie_modulus (eps / 2) + 1)).
        assert (Hs : pie_term (2 * pie_modulus (eps / 2) + 1)
                     == - pie_mag (2 * pie_modulus (eps / 2) + 1)).
        { unfold pie_term, pie_mag, Qdiv.
          rewrite (qeqT_imp_qeq _ _ (atan_sign_odd (pie_modulus (eps / 2)))). ring. }
        setoid_replace (4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
                        - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1)))
          with (- (4 * (pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1))
                     - pie_partial (2 * pie_modulus (eps / 2) + 1))))
          by ring.
        rewrite (qeqT_imp_qeq _ _ Hg). rewrite Hs. ring. }
      setoid_replace ((4 * pie_partial (2 * pie_modulus (eps / 2) + 1) + eps / 4)
                      - (4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1))
                         - eps / 4))
        with ((4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
               - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1)))
              + (eps / 4 + eps / 4)) by ring.
      setoid_replace (4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
                      - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1)))
        with (4 * pie_mag (2 * pie_modulus (eps / 2) + 1)) by exact Hgap.
      setoid_replace (eps / 4 + eps / 4) with (eps / 2)
        by apply (qeqT_imp_qeq _ _ (pie_q_add_halves eps)).
      apply (proj2 (Qlt_minus_iff (4 * pie_mag (2 * pie_modulus (eps / 2) + 1)
                                   + eps / 2) eps)).
      setoid_replace (eps - (4 * pie_mag (2 * pie_modulus (eps / 2) + 1) + eps / 2))
        with ((eps - eps / 2) - 4 * pie_mag (2 * pie_modulus (eps / 2) + 1))
        by ring.
      setoid_replace (eps - eps / 2) with (eps / 2)
        by (unfold Qdiv; field).
      apply (proj1 (Qlt_minus_iff (4 * pie_mag (2 * pie_modulus (eps / 2) + 1))
                                  (eps / 2))).
      exact Hb.
Defined.

(* ============================================================ *)
(* Section 7. assumption audit (one line per theorem)            *)
(* ============================================================ *)

Print Assumptions lw3x_sideb_spec.
Print Assumptions lw3x_seal.
Print Assumptions lw3x_band_excl.
Print Assumptions lw3x_calc.
Print Assumptions lw3x_channel_f1_closed.
Print Assumptions lw3x_c2_pos.
Print Assumptions lw3x_pi_geom_seal_slot.
Print Assumptions lw3x_env_supply.
