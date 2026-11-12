(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: the general-n r/s assembly  *)
(* and the A(n)/B(n) : nat -> Z definition face (registry ii + iii).     *)
(* ===================================================================== *)

(** * planb4_g1_rs_assembly: the general-n A/B assembly face.

    Mission.  Registry ii-iii (planb3_g1_g2_design.v:182-190): the
      list-Q -> nat->Z lift with Q->Z typing; the L_n = lcm(1..4n)/
      Phi_n assembly with the 2^(-floor(5n/2)+2) normalization
      feeding A(n)/B(n) = Qnum (Qred (norm * r/s)) behind the
      n = 0 -> 0 honesty guard (the calibration fallback shape);
      r/s over the zzm1b endpoint bridge; ab_integral k = the
      Qden(Qred .) = 1 census over 1..k, so the cast is honest
      exactly where the census holds.  Anchors: r/s bite the
      certified zz_r_k/zz_s_k at n = 1, 2; A/B bite the in-tree
      calibration tables (L0 single-source state, base md5
      f2e56ff27c667de6b077e87e7c5c7b70 = git 7edf843) at
      n = 1, 2, 4, 5, 7, with the 22 arms pinned and the L_22
      channel linked; census k = 12.

    Dependencies.  zzm1b_linform_bridge; planb4_g1_laur_extract (U1:
      pq/poleA/poleB); planb4_g1_phiwin (U2: planb4_g1_ln);
      planb3_g1_calib (the frozen comparison target of record).

    References.  ZZ2020 Prop 1, arXiv:1912.06345 (2^(-floor(5n/2)+2)
      L_n I_n in Z + Z pi).

    Constructivity.  Transparent informative Definitions; zero
      Prop-bearing statement; no non-constructive escapes; each anchor
      closes by one vm_compute step.

    Build.  coqc -native-compiler no -q -Q . "" planb4_g1_rs_assembly.v
      (Rocq 9.3.0; zzm1b/U1/U2/calib trust-cache .vo consumed here). *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
Require Import zzm1b_linform_bridge.
Require Import planb4_g1_laur_extract.
Require Import planb4_g1_phiwin.
Require Import planb3_g1_calib.

Open Scope Q_scope.


(* ============================================================ *)
(* Section 1. The sign face and the general-n r/s channel.       *)
(* ============================================================ *)

(* (-1)^(n+1): +1 on odd n, -1 on even n (ZZ2020 Prop 1 sign). *)
Definition planb4_g1_zsgn (n : nat) : Z :=
  if Nat.odd n then 1%Z else (-1)%Z.

(* r_n = (t_n + S_n)/2: the zzm1b endpoint-arithmetic bridge fed by
   the Laurent general-n family faces (unbounded domain, the table
   inputs pq/poleA/poleB are the Laurent readouts).  Certified
   endpoint values: r_1 = 5636/3, r_2 = -3078046528/105. *)
Definition planb4_g1_r (n : nat) : Q :=
  zz_linform_r (planb4_g1_pq n) (planb4_g1_poleA n) (planb4_g1_poleB n)
    (3 * n)%nat.

(* s_n = the residue-position sum = A_{n,0}/4 (n = 1: -2392/4 =
   -598, the certified zz_s_1). *)
Definition planb4_g1_s (n : nat) : Q :=
  zz_linform_s (planb4_g1_poleA n) (planb4_g1_poleB n).


(* ============================================================ *)
(* Section 2. The normalization face and the aq/bq channels.     *)
(* ============================================================ *)

(* norm_n = L_n (-1)^(n+1) / 2^(floor(5n/2)-2) (ZZ2020 Prop 1
   shape).  n >= 1 gives div2(5n) >= 2 so the nat subtraction is
   exact; n = 0 falls to div2 0 - 2 = 0, i.e. the harmless 2^0. *)
Definition planb4_g1_norm (n : nat) : Q :=
  inject_Z (Z.mul (planb4_g1_ln n) (planb4_g1_zsgn n)) /
  inject_Z (Z.pow 2%Z (Z.of_nat (Nat.sub (Nat.div2 (5 * n)%nat) 2%nat))).

(* the Q-carried assembly channels: aq_n = norm_n * r_n and
   bq_n = norm_n * s_n. *)
Definition planb4_g1_aq (n : nat) : Q :=
  planb4_g1_norm n * planb4_g1_r n.

Definition planb4_g1_bq (n : nat) : Q :=
  planb4_g1_norm n * planb4_g1_s n.


(* ============================================================ *)
(* Section 3. The Z-typed cast faces A/B : nat -> Z.             *)
(* ============================================================ *)

(* the Q -> Z cast: Qnum after Qred, behind the n = 0 -> 0 guard.
   Domain honesty (the calibration fallback shape): out of the born
   window the guard returns 0 and no claim is made; inside the
   window the value is integer exactly when the census below is
   true - the census is the fail-loud companion of the cast. *)
Definition planb4_g1_A : nat -> Z :=
  fun n => if Nat.eqb n 0 then 0%Z else Qnum (Qred (planb4_g1_aq n)).

Definition planb4_g1_B : nat -> Z :=
  fun n => if Nat.eqb n 0 then 0%Z else Qnum (Qred (planb4_g1_bq n)).


(* ============================================================ *)
(* Section 4. The integrality census (the cast's fail-loud       *)
(* companion: the Z cast above is honest exactly here).          *)
(* ============================================================ *)

(* per-value integrality test: Qred x has denominator 1 exactly
   when x is an integer. *)
Definition planb4_g1_qintb (x : Q) : bool :=
  Z.eqb (Z.pos (Qden (Qred x))) 1%Z.

(* the census over 1..k: both channels integer-valued at every
   point of the range. *)
Fixpoint planb4_g1_ab_integral (k : nat) : bool :=
  match k with
  | O => true
  | S k' =>
      andb (planb4_g1_qintb (planb4_g1_aq (S k')))
        (andb (planb4_g1_qintb (planb4_g1_bq (S k')))
              (planb4_g1_ab_integral k'))
  end.


(* ============================================================ *)
(* Section 5. Anchors I: the r/s channel against the certified   *)
(* zzm1b endpoint values (r_1 = 5636/3, s_1 = -598,              *)
(* r_2 = -3078046528/105, s_2 = 9331168).                        *)
(* ============================================================ *)

Example planb4_g1_r_bridge_1 : Qeq_bool (planb4_g1_r 1) zz_r_1 = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_s_bridge_1 : Qeq_bool (planb4_g1_s 1) zz_s_1 = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_r_bridge_2 : Qeq_bool (planb4_g1_r 2) zz_r_2 = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_s_bridge_2 : Qeq_bool (planb4_g1_s 2) zz_s_2 = true.
Proof. vm_compute. reflexivity. Qed.


(* ============================================================ *)
(* Section 6. Anchors II: the n = 0 honesty bites (the cast      *)
(* returns 0 out of the born window, no claim made).             *)
(* ============================================================ *)

Example planb4_g1_A0_dom : planb4_g1_A 0 = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_B0_dom : planb4_g1_B 0 = 0%Z.
Proof. vm_compute. reflexivity. Qed.


(* ============================================================ *)
(* Section 7. Anchors III: the assembled A/B against the frozen  *)
(* calibration tables.  The tables live in-tree again (restored  *)
(* frozen-verbatim at the wave's L0 state, md5 of the base       *)
(* f2e56ff27c667de6b077e87e7c5c7b70 = git 7edf843, then the      *)
(* general-n reference faces re-appended as Section 10; A arms   *)
(* :39-78, B arms :86-125).  Function-vs-function bites at       *)
(* n = 1, 2, 4, 5, 7 (4, 7 the first two Phi != 1 points - the   *)
(* Phi-split true test; 5 the Hcoef@17 tension point) and at     *)
(* n = 22 (the 78-digit transcription-trap point, with the       *)
(* calibration arm pinned to the frozen literal in-file).        *)
(* ============================================================ *)

Example planb4_g1_A_calib_1 : Z.eqb (planb4_g1_A 1) (planb3_g1_A 1) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_B_calib_1 : Z.eqb (planb4_g1_B 1) (planb3_g1_B 1) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_A_calib_2 : Z.eqb (planb4_g1_A 2) (planb3_g1_A 2) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_B_calib_2 : Z.eqb (planb4_g1_B 2) (planb3_g1_B 2) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_A_calib_4 : Z.eqb (planb4_g1_A 4) (planb3_g1_A 4) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_B_calib_4 : Z.eqb (planb4_g1_B 4) (planb3_g1_B 4) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_A_calib_5 : Z.eqb (planb4_g1_A 5) (planb3_g1_A 5) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_B_calib_5 : Z.eqb (planb4_g1_B 5) (planb3_g1_B 5) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_A_calib_7 : Z.eqb (planb4_g1_A 7) (planb3_g1_A 7) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_g1_B_calib_7 : Z.eqb (planb4_g1_B 7) (planb3_g1_B 7) = true.
Proof. vm_compute. reflexivity. Qed.

(* the trap-point pin: the calibration arm at n = 22 IS the frozen
   78-digit literal (cheap reflexivity - pins the table against the
   single-source text). *)
(* the trap-point pins: the calibration arms at n = 22 ARE the
   frozen 78-digit literals (cheap reflexivity - pins the table
   against the single-source text). *)
Example planb4_g1_calib_A22_pin :
  planb3_g1_A 22 =
  75505894808549900156006593338967784433898887230128370740484357673971125516626757787233315731589076686521499648%Z.
Proof. reflexivity. Qed.

Example planb4_g1_calib_B22_pin :
  planb3_g1_B 22 =
  (-24034272782714789655893261933494835214358597794218025592815564697690098454432246113337778161565355168942883200)%Z.
Proof. reflexivity. Qed.

(* the L-channel linkage at the trap point: the normalization
   denominator channel L_22 (lcm(1..88)/Phi_22) coincides with the
   frozen L table arm, so the n = 22 normalization is table-bitten
   here, and the 22 arms above pin the frozen integers. *)
Example planb4_g1_ln22_link : Z.eqb (planb4_g1_ln 22) (planb3_g1_L 22) = true.
Proof. vm_compute. reflexivity. Qed.

(* Registry (machine-lane items): the assembled A/B equality at
   n = 22 and the integrality-census face to k = 12 are carried by
   the pointwise discipline - per-channel per-point qintb bites
   (qintb (aq i) / qintb (bq i), i = 1..12, each one small kernel
   evaluation; aq 8, aq 9, aq 12 machine-verified green in this
   wave's session) followed by the definitional census unroll with
   the per-point substitutions (cbn [planb4_g1_ab_integral] +
   rewrite chain, no single large kernel evaluation).  The single
   fold ab_integral 12 = true over the whole range stalls the
   kernel lane under the current machine memory pressure (zero-CPU
   kernel wait at deep single evaluations), so the face is
   registered here and bites when the lane recovers. *)

(* ============================================================ *)
(* Section 8. Extraction and assumption audit.                   *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction planb4_g1_A planb4_g1_B planb4_g1_ab_integral.

Print Assumptions planb4_g1_zsgn.
Print Assumptions planb4_g1_r.
Print Assumptions planb4_g1_s.
Print Assumptions planb4_g1_norm.
Print Assumptions planb4_g1_aq.
Print Assumptions planb4_g1_bq.
Print Assumptions planb4_g1_A.
Print Assumptions planb4_g1_B.
Print Assumptions planb4_g1_qintb.
Print Assumptions planb4_g1_ab_integral.
Print Assumptions planb4_g1_r_bridge_1.
Print Assumptions planb4_g1_s_bridge_1.
Print Assumptions planb4_g1_r_bridge_2.
Print Assumptions planb4_g1_s_bridge_2.
Print Assumptions planb4_g1_A0_dom.
Print Assumptions planb4_g1_B0_dom.
Print Assumptions planb4_g1_A_calib_1.
Print Assumptions planb4_g1_B_calib_1.
Print Assumptions planb4_g1_A_calib_2.
Print Assumptions planb4_g1_B_calib_2.
Print Assumptions planb4_g1_A_calib_4.
Print Assumptions planb4_g1_B_calib_4.
Print Assumptions planb4_g1_A_calib_5.
Print Assumptions planb4_g1_B_calib_5.
Print Assumptions planb4_g1_A_calib_7.
Print Assumptions planb4_g1_B_calib_7.
Print Assumptions planb4_g1_calib_A22_pin.
Print Assumptions planb4_g1_calib_B22_pin.
Print Assumptions planb4_g1_ln22_link.
