(* ==========================================================================
   uabda_g13_evict_discharge.v -- discharge-form cross-check piece for the
   interface-assumption faces of the G13_EvictFam eviction family.
   Mission.  give instance-world discharge forms for the four interface
   assumptions of G13_EvictFam.v: id layer :57 Z_thermo_pos and :83
   evicted_partition_pos, req layer :474 Z_thermo_pos and :503
   evicted_partition_pos.  the id layer is a single-point world using the
   supply-library pieces at lines :130/:141; the req layer is a two-point world
   using the supply-library piece at line :285.  the req-layer evicted
   partition positivity is a new unconditionally closed construction: the
   library holds only one conditional form with demand and positivity
   premises, plus the id-layer piece at line :141, and lacks this world form.
   Dependencies.  S01_BaseRing, G13_EvictFam, G13 companion library pieces
   (all read-only).
   References.  G13_EvictFam.v:57/:83/:474/:503; the supply-library
   discharge pieces (:130/:141/:285); the isomorphic template
   S06_DiffSamplingGibbs.v:3826 Z_thermo_pos (pointwise exp_neg_pos plus
   sum-positivity interface instantiation).  interface-generation alignment
   per the UpReqMisc5B precedent (binder-shell removal + Id-layer import
   restore, in-world compiled precedent verified, statement names verbatim).
   Constructivity.  every proof closes by Qed; nothing is declared without
   proof and no classical logic is used; the statement face stays on the Set
   layer with zero Prop leakage; the proof body of uabda_g13_evpart_req is an
   explicit two-point positive-sum construction (plus_positive plus two uses
   of exp_neg_pos), not a forwarding piece.
   Build.  coqc -q -native-compiler no -Q <main vo tree> "" -Q . "" this
   file, wrapped by cpu_guard -TempLimit 98 with COQLIB/ROCQLIB exported
   verbatim; .vo magic [436f7121 000160bc].
   ========================================================================== *)
Require Import S01_BaseRing.
Require Import S07_RealSetoidExpLog.
Require Import G13_EvictFam.
Require Import UpAblT13c_G13.
(* interface-generation alignment, Id layer: the req segments of G13_EvictFam
   and its companion modules export the abbreviation R := Real, which shadows
   the S01_BaseRing carrier projection R used by the Id-layer statement face;
   this re-import restores the projection resolution for the Id layer. *)
Require Import S01_BaseRing.

(* ---- i. id layer: discharge form of the :57 interface assumption (single-point world, where the sum degenerates to a single factor) ---- *)

Theorem uabda_g13_zpos_id :
  forall {RI : RealInterfaceEnhanced}
         (D : @R RI) (D_pos : @lt RI (@zero RI) D)
         (energy : @S RI uab_ssUnit -> @R RI),
    @lt RI (@zero RI)
      (@evict_Z_thermo RI uab_ssUnit uab_soUnit D D_pos energy).
Proof.
  intros RI D D_pos energy.
  exact (uabT13c_evict61 D D_pos energy).
Qed.

(* ---- ii. id layer: discharge form of the :83 interface assumption (single-point world, with the keep-all decision supplied) ---- *)

Theorem uabda_g13_evpart_id :
  forall {RI : RealInterfaceEnhanced}
         (D : @R RI) (D_pos : @lt RI (@zero RI) D)
         (energy : @S RI uab_ssUnit -> @R RI),
    @lt RI (@zero RI)
      (@evict_evicted_partition RI uab_ssUnit uab_soUnit D D_pos energy
         (fun _ : @S RI uab_ssUnit => unit)
         (fun _ : @S RI uab_ssUnit => inl tt : Or unit (Not unit))).
Proof.
  intros RI D D_pos energy.
  exact (uabT13c_evict87 D D_pos energy).
Qed.

Import RealInterfaceEnhancedMod.

(* ---- iii. req layer: the two-point world, the carrier R fixed to the
   concrete Real face by the registered tree notation (interface-generation
   alignment per the UpReqMisc5B precedent: this tree's
   RealInterfaceEnhancedSetoid is an unparameterized class, so the
   source-world binder shells, the Let resolution block, and the leading
   R RIS of the evq applications are removed; the mathematical content of
   every statement is unchanged) ---- *)

Require Import G13_EvictFam.

Section UabdaG13Req.

(* discharge form of the :474 interface assumption, two-point world (uab_t2sum); uses the companion library piece at line :285 *)
Theorem uabda_g13_zpos_req (D : R) (D_pos : lt zero D) (energy : bool -> R) :
  lt zero (@evq_Z_thermo bool uab_t2sum D D_pos energy).
Proof.
  exact (uabT13c_evq_Zpos2 D D_pos energy).
Qed.

(* discharge form of the :503 interface assumption, two-point world,
   keep-all decision, unconditionally closed (explicit two-point
   positive-sum construction): once the keep decision always takes the left
   branch, pointwise positivity is given by exp_neg_pos, and the positivity
   of the two-term sum is composed by plus_positive; isomorphic to the S06
   Z_thermo_pos template (pointwise positivity plus sum-positivity
   instantiation, carried here on the two-point carrier). *)
Theorem uabda_g13_evpart_req (D : R) (D_pos : lt zero D) (energy : bool -> R) :
  lt zero (@evq_evicted_partition bool uab_t2sum D D_pos energy
             (fun _ : bool => unit)
             (fun _ : bool => inl tt : Or unit (Not unit))).
Proof.
  unfold evq_evicted_partition, uab_t2sum, evq_boltzmann_factor.
  exact (plus_positive
           (exp_neg (mult (inv_pos D D_pos) (energy true)))
           (exp_neg (mult (inv_pos D D_pos) (energy false)))
           (exp_neg_pos (mult (inv_pos D D_pos) (energy true)))
           (exp_neg_pos (mult (inv_pos D D_pos) (energy false)))).
Qed.

End UabdaG13Req.

(* ---- per-item premise-face audit (the Closed criterion) ---- *)

Print Assumptions uabda_g13_zpos_id.
Print Assumptions uabda_g13_evpart_id.
Print Assumptions uabda_g13_zpos_req.
Print Assumptions uabda_g13_evpart_req.
