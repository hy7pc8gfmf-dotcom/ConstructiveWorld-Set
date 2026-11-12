(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: the A/B definition face     *)
(* (total nat -> Z assembly over the born window n = 1..6).              *)
(* ===================================================================== *)

(** * planb4_g1_ab_def: the A/B assembly definition face.

    Mission.  The total informative functions [planb4_g1_A] and
      [planb4_g1_B : nat -> Z]: the assembly [A(n) = 2^(-floor(5n/2)
      +2) L_n (-1)^(n+1) r_n], [B(n)] the s-channel twin, carried
      in Q, [Qred]-canonicalized, projected by [Qnum]; [L_n] via
      the witness lcm/Pn-window quotient, r/s via the certified
      endpoint bridge.  Born window n = 1..6 anchors: L/Phi window
      bites, Qnum integrality, frozen A/B table bites.  Domain
      honesty: no forall-n claim; out-of-table inputs compute.

    Dependencies.  planb4_g1_witness (scale/L/Phi/LZn);
      planb4_g1_rs_channel (planb4_rs, planb4_ss); planb3_g1_calib
      (frozen n = 1..40 tables); stdlib Qcanon (Qred).

    References.  ZZ2020 Prop 1 (2^(-5n/2+2) L_n I_n integer
      assembly); zzm1b_linform_bridge 143-224 (certified r/s).

    Constructivity.  Transparent informative Definitions over Q/Z;
      each anchor one vm_compute step; admission-free throughout.

    Build.  coqc -native-compiler no -q -Q . "" planb4_g1_ab_def.v
      (Rocq 9.3.0, single lane under cpu_guard_v3). *)

From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qcanon.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Require Import planb4_g1_witness.
Require Import planb4_g1_rs_channel.
Require Import planb3_g1_calib.

(* ================================================================== *)
(* Section 1. The A/B assembly faces (total, informative).            *)
(* ================================================================== *)

(* the scale factor 2^(-floor(5n/2)+2): the witness scale             *)
(* 2^(-floor(5n/2)+1) doubled; the +2 exponent is pinned by the       *)
(* frozen tables (n=1: 2^0 * 12 * 5636/3 = 22544, n=2: 2^-3 * 840 *   *)
(* (-1) * (-3078046528/105) = 3078046528; the +1 form fails both).    *)
Definition planb4_ab_exp (n : nat) : Q := (planb4_scale n * 2)%Q.

(* (-1)^(n+1): +1 on odd n, -1 on even n. *)
Definition planb4_ab_sign (n : nat) : Z :=
  if Nat.even n then (-1)%Z else 1%Z.

(* the ZZ2020 clearing integer L_n = lcm(1..4n) / Phi_n. *)
Definition planb4_ab_L (n : nat) : Z := planb4_LZn n.

(* the r-channel assembly: 2^(-floor(5n/2)+2) L_n (-1)^(n+1) r_n.    *)
(* Qred: the base-Q ring ops multiply denominators without gcd       *)
(* reduction, so the Qnum projection is the lowest-terms numerator   *)
(* only after canonicalization (same face as planb4_g1_laur_extract). *)
Definition planb4_abqA (n : nat) : Q :=
  Qred (planb4_ab_exp n * inject_Z (planb4_ab_L n)
        * inject_Z (planb4_ab_sign n) * planb4_rs n).

(* the s-channel twin: 2^(-floor(5n/2)+2) L_n (-1)^(n+1) s_n. *)
Definition planb4_abqB (n : nat) : Q :=
  Qred (planb4_ab_exp n * inject_Z (planb4_ab_L n)
        * inject_Z (planb4_ab_sign n) * planb4_ss n).

(* the total A/B functions: Q projection to the numerator; the born   *)
(* window n = 1..6 carries integer-valued rationals, so Qnum recovers *)
(* the frozen calibration integers there. *)
Definition planb4_g1_A : nat -> Z := fun n => Qnum (planb4_abqA n).

Definition planb4_g1_B : nat -> Z := fun n => Qnum (planb4_abqB n).

(* ================================================================== *)
(* Section 2. Born window n = 1..6, group (a): the L/Phi window pair  *)
(* bites the frozen calib channels (lcm/Phi arithmetic only).         *)
(* ================================================================== *)

Example planb4_ab_Lwin_1 : Z.eqb (planb4_LZn 1) (planb3_g1_L 1) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Lwin_2 : Z.eqb (planb4_LZn 2) (planb3_g1_L 2) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Lwin_3 : Z.eqb (planb4_LZn 3) (planb3_g1_L 3) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Lwin_4 : Z.eqb (planb4_LZn 4) (planb3_g1_L 4) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Lwin_5 : Z.eqb (planb4_LZn 5) (planb3_g1_L 5) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Lwin_6 : Z.eqb (planb4_LZn 6) (planb3_g1_L 6) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Phiwin_1 : Z.eqb (planb4_Phi 1) (planb3_g1_Phi 1) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Phiwin_2 : Z.eqb (planb4_Phi 2) (planb3_g1_Phi 2) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Phiwin_3 : Z.eqb (planb4_Phi 3) (planb3_g1_Phi 3) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Phiwin_4 : Z.eqb (planb4_Phi 4) (planb3_g1_Phi 4) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Phiwin_5 : Z.eqb (planb4_Phi 5) (planb3_g1_Phi 5) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Phiwin_6 : Z.eqb (planb4_Phi 6) (planb3_g1_Phi 6) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 3. Born window n = 1..6, group (b): both assembled         *)
(* channels are integer-valued rationals there (Q representation      *)
(* free: Qeq_bool through the Qnum/inject_Z round trip).              *)
(* ================================================================== *)

Example planb4_abqA_int_1 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 1))) (planb4_abqA 1) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_abqA_int_2 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 2))) (planb4_abqA 2) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_abqA_int_3 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 3))) (planb4_abqA 3) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_abqA_int_4 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 4))) (planb4_abqA 4) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_abqA_int_5 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 5))) (planb4_abqA 5) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_abqA_int_6 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 6))) (planb4_abqA 6) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_1 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 1))) (planb4_abqB 1) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_abqB_int_2 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 2))) (planb4_abqB 2) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_abqB_int_3 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 3))) (planb4_abqB 3) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_abqB_int_4 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 4))) (planb4_abqB 4) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_abqB_int_5 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 5))) (planb4_abqB 5) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_abqB_int_6 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 6))) (planb4_abqB 6) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 4. Born window n = 1..6, group (c): the assembled Qnum     *)
(* values bite the frozen calibration tables (the exact machine       *)
(* verification of the assembly formula on the born window).          *)
(* ================================================================== *)

Example planb4_ab_Acal_1 : Z.eqb (Qnum (planb4_abqA 1)) (planb3_g1_A 1) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Acal_2 : Z.eqb (Qnum (planb4_abqA 2)) (planb3_g1_A 2) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Acal_3 : Z.eqb (Qnum (planb4_abqA 3)) (planb3_g1_A 3) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Acal_4 : Z.eqb (Qnum (planb4_abqA 4)) (planb3_g1_A 4) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Acal_5 : Z.eqb (Qnum (planb4_abqA 5)) (planb3_g1_A 5) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Acal_6 : Z.eqb (Qnum (planb4_abqA 6)) (planb3_g1_A 6) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_1 : Z.eqb (Qnum (planb4_abqB 1)) (planb3_g1_B 1) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Bcal_2 : Z.eqb (Qnum (planb4_abqB 2)) (planb3_g1_B 2) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Bcal_3 : Z.eqb (Qnum (planb4_abqB 3)) (planb3_g1_B 3) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Bcal_4 : Z.eqb (Qnum (planb4_abqB 4)) (planb3_g1_B 4) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Bcal_5 : Z.eqb (Qnum (planb4_abqB 5)) (planb3_g1_B 5) = true.
Proof. vm_compute. reflexivity. Qed.
Example planb4_ab_Bcal_6 : Z.eqb (Qnum (planb4_abqB 6)) (planb3_g1_B 6) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 5. Assumption audit.                                       *)
(* ================================================================== *)

Print Assumptions planb4_ab_exp.
Print Assumptions planb4_ab_sign.
Print Assumptions planb4_ab_L.
Print Assumptions planb4_abqA.
Print Assumptions planb4_abqB.
Print Assumptions planb4_g1_A.
Print Assumptions planb4_g1_B.
Print Assumptions planb4_ab_Lwin_1.
Print Assumptions planb4_ab_Lwin_2.
Print Assumptions planb4_ab_Lwin_3.
Print Assumptions planb4_ab_Lwin_4.
Print Assumptions planb4_ab_Lwin_5.
Print Assumptions planb4_ab_Lwin_6.
Print Assumptions planb4_ab_Phiwin_1.
Print Assumptions planb4_ab_Phiwin_2.
Print Assumptions planb4_ab_Phiwin_3.
Print Assumptions planb4_ab_Phiwin_4.
Print Assumptions planb4_ab_Phiwin_5.
Print Assumptions planb4_ab_Phiwin_6.
Print Assumptions planb4_abqA_int_1.
Print Assumptions planb4_abqA_int_2.
Print Assumptions planb4_abqA_int_3.
Print Assumptions planb4_abqA_int_4.
Print Assumptions planb4_abqA_int_5.
Print Assumptions planb4_abqA_int_6.
Print Assumptions planb4_abqB_int_1.
Print Assumptions planb4_abqB_int_2.
Print Assumptions planb4_abqB_int_3.
Print Assumptions planb4_abqB_int_4.
Print Assumptions planb4_abqB_int_5.
Print Assumptions planb4_abqB_int_6.
Print Assumptions planb4_ab_Acal_1.
Print Assumptions planb4_ab_Acal_2.
Print Assumptions planb4_ab_Acal_3.
Print Assumptions planb4_ab_Acal_4.
Print Assumptions planb4_ab_Acal_5.
Print Assumptions planb4_ab_Acal_6.
Print Assumptions planb4_ab_Bcal_1.
Print Assumptions planb4_ab_Bcal_2.
Print Assumptions planb4_ab_Bcal_3.
Print Assumptions planb4_ab_Bcal_4.
Print Assumptions planb4_ab_Bcal_5.
Print Assumptions planb4_ab_Bcal_6.
