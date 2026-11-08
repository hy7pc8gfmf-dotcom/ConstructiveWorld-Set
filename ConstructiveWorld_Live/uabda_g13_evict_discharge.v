(* ConstructiveWorld-Set -- instance-world discharge forms for the G13 eviction family interface faces. *)

(** * uabda_g13_evict_discharge: instance-world discharge of the interface positivity faces of the G13 eviction family.

    Mission.  Discharges the four interface faces of the [G13_EvictFam] eviction
      family, [Z_thermo_pos] and [evicted_partition_pos] at the [Id] layer and at
      the request layer, as instance-world closure theorems.  On the single-point
      world [uab_ssUnit] the sum reduces to a factor row and
      [uabda_g13_zpos_id]/[uabda_g13_evpart_id] forward to the companion supply
      theorems; on the two-point world [uab_t2sum], [uabda_g13_zpos_req] forwards
      likewise while [uabda_g13_evpart_req] is a new unconditional closure: the
      retention decision takes the left branch, pointwise positivity is given by
      [exp_neg_pos] on both branches and the two-term sum closes by
      [plus_positive], isomorphic to the diff-sampling [Z_thermo_pos] discharge.

    Dependencies.  Requires [S01_BaseRing], [S07_RealSetoidExpLog],
      [G13_EvictFam], and the [G13] companion module of this development.

    References.  This development, uabda_g13_evict_discharge.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" uabda_g13_evict_discharge.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import S01_BaseRing.
Require Import S07_RealSetoidExpLog.
Require Import G13_EvictFam.
Require Import UpAblT13c_G13.

Import RealInterfaceEnhancedMod.

(* ---- request layer: the two-point world, with the carrier [R] fixed to the
   global Cauchy real [Real], whose fields resolve through the global instance
   [RealEnhancedReal].  Interface-face adaptation registered per the tree
   precedent (the interface-face note of G13_EvictFam's EvictIdReq segment):
   this tree's [RealInterfaceEnhancedSetoid] is an unparameterized class, so
   the source-world parameterized binder shells ([Context {R : Set}],
   [Context {RIS : RealInterfaceEnhancedSetoid R}], the [Let ... := @... R RIS]
   resolution block, and the leading [R RIS] of the [@evq_*] applications) are
   carrier-ized to the concrete [Real] face; the mathematical content of every
   statement is unchanged.  Idiom per the [G13] companion module's part-two
   request segment: the re-import replays the G13_EvictFam EvictIdReq concrete-carrier notation
   take ([R := Real]; [req]/[lt]/[le] := [real_eq]/[real_lt]/[real_le]) over
   the module's concrete-instance faces, so every statement face names the
   concrete carrier explicitly (extraction-face fix, fa56b plan B discipline:
   the extractor sees one concrete carrier on both sides of every use site). ---- *)

Require Import G13_EvictFam.

Section UabdaG13Req.

(* ---- Id layer, [Z_thermo_pos] face on the single-point world (carrier unit,
   sum uab_unit_sum): forwards to the companion module's concrete face. ---- *)

Theorem uabda_g13_zpos_id (D : R) (D_pos : lt zero D) (energy : unit -> R) :
  lt zero (@evq_Z_thermo unit uab_unit_sum D D_pos energy).
Proof.
  exact (uabT13c_evict61 D D_pos energy).
Qed.

(* ---- Id layer, [evicted_partition_pos] face on the single-point world, with
   the retention decision supplied as all-keep. ---- *)

Theorem uabda_g13_evpart_id (D : R) (D_pos : lt zero D) (energy : unit -> R) :
  lt zero (@evq_evicted_partition unit uab_unit_sum D D_pos energy
             (fun _ : unit => unit)
             (fun _ : unit => inl tt : Or unit (Not unit))).
Proof.
  exact (uabT13c_evict87 D D_pos energy).
Qed.

(* request-layer [Z_thermo_pos] face on the two-point world [uab_t2sum]:
   forwards to the in-development companion supply theorem. *)
Theorem uabda_g13_zpos_req (D : R) (D_pos : lt zero D) (energy : bool -> R) :
  lt zero (@evq_Z_thermo bool uab_t2sum D D_pos energy).
Proof.
  exact (uabT13c_evq_Zpos2 D D_pos energy).
Qed.

(* request-layer [evicted_partition_pos] face on the two-point world, closed
   unconditionally: the retention decision always takes the left branch, so
   pointwise positivity is given by [exp_neg_pos] on both branches and the
   positivity of the two-term sum is composed by [plus_positive].  Isomorphic
   to the diff-sampling [Z_thermo_pos] discharge: pointwise positivity plus
   positivity-preserving summation, instantiated here on the two-point
   carrier. *)
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

(* ---- per-statement closure audit by [Print Assumptions]. ---- *)

Print Assumptions uabda_g13_zpos_id.
Print Assumptions uabda_g13_evpart_id.
Print Assumptions uabda_g13_zpos_req.
Print Assumptions uabda_g13_evpart_req.
