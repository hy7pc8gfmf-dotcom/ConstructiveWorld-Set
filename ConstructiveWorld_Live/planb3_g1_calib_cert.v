(* ConstructiveWorld-Main - planb3_g1_calib numeric-certainty companion: the sigma=17 tension face and the b-channel nonzero census. *)

(** * planb3_g1_calib_cert: numeric spot faces for the G1 calibration.

    Mission.  The vm_compute-verified numeric faces split out of
      planb3_g1_calib: the calibration A-channel sigma=17 growth-slot
      tension at n=5 (the KB41m 5.5 registered open item) and the
      b-channel nonzero census across the whole domain 1..40.

    Dependencies.  planb3_g1_calib of this development; stdlib
      ZArith, QArith.

    References.  planb3_g1_calib.v (the calibration tables these
      faces audit).

    Constructivity.  All proofs close by vm_compute; admission-free
      and postulate-free throughout.

    Build.  coqc -native-compiler no -q -Q . "" planb3_g1_calib_cert.v
      (Rocq 9.3.0, single lane under cpu_guard_v3). *)

From Stdlib Require Import QArith ZArith.
Require Import planb3_g1_calib.

(* the calibration A-channel does NOT satisfy the sigma=17 growth *)
(* slot at n=5 (the registered open item). *)
Example planb3_g1_A5_hcoef17_tension : (2 ^ 85 < Z.abs (planb3_g1_A 5))%Z.
Proof. vm_compute; reflexivity. Qed.

(* Hcoef@17 B-side fit at n=5: |B 5| <= 2^85 (the B-side mapping fits *)
(* the sigma=17 slot at the calibration witness).                     *)
Example planb3_g1_B5_hcoef17_fit : (Z.abs (planb3_g1_B 5) <= 2 ^ 85)%Z.
Proof. vm_compute; intro Hc; discriminate Hc. Qed.

(* the b-channel nonzero census holds across the whole domain 1..40. *)
Example planb3_g1_b_nonzero_dom : planb3_g1_allb_nz 40 = true.
Proof. vm_compute; reflexivity. Qed.

(* assumption audit *)
Print Assumptions planb3_g1_A5_hcoef17_tension.
Print Assumptions planb3_g1_B5_hcoef17_fit.
Print Assumptions planb3_g1_b_nonzero_dom.
