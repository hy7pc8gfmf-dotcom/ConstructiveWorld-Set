(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: the general-n r/s channel   *)
(* face composing the zzm1b endpoint bridge with the Laurent faces.      *)
(* ===================================================================== *)

(** * planb4_g1_rs_channel: the composite r/s linear-form channel.

    Mission.  [planb4_rs n] := [zz_linform_r (pq n) (poleA n) (poleB n)
      (3n)] and [planb4_ss n] := [zz_linform_s (poleA n) (poleB n)]:
      the zzm1b endpoint-arithmetic bridge (unbounded domain, table
      inputs) fed by the Laurent general-n family faces of
      planb4_g1_laur_extract.  The n = 1..6 anchors bite the certified
      [zz_r_k]/[zz_s_k] literals; composed with the U1 anchor
      poleA = zz_as, this machine-bites the Laurent route against the
      certified r/s domain for n <= 6.

    Dependencies.  zzm1b_linform_bridge (zz_linform_r/s, the certified
      zz_r_k/zz_s_k tables, zzId); planb4_g1_laur_extract (pq/poleA/
      poleB); zzm1_gauss (zzId).

    References.  ZZ2020 Lemma 1 (the A_j pole readout); the zzm1b
      certified-table supply note (r/s values, n = 1..6).

    Constructivity.  Two transparent Q-valued Definitions over the
      Set-borne bridge; every statement zzId-borne (zero Prop
      statement); no non-constructive escapes; each anchor closes by
      one vm_compute step.

    Build.  coqc -native-compiler no -q -Q . "" planb4_g1_rs_channel.v
      (Rocq 9.3.0; the zzm1b/Laurent trust-cache .vo consumed here). *)

From Stdlib Require Import QArith.QArith ZArith.ZArith List.
Require Import zzm1_gauss.
Require Import zzm1b_linform_bridge.
Require Import planb4_g1_laur_extract.

Open Scope Q_scope.


(* ============================================================ *)
(* §1 The composite r/s channel definitions (transparent)        *)
(* ============================================================ *)

(* r channel: polynomial part + double principal part, the Laurent
   family tables feeding the certified endpoint bridge. *)
Definition planb4_rs (n : nat) : Q :=
  zz_linform_r (planb4_g1_pq n) (planb4_g1_poleA n) (planb4_g1_poleB n) (3 * n)%nat.

(* s channel: the residue-position sum over the same family. *)
Definition planb4_ss (n : nat) : Q :=
  zz_linform_s (planb4_g1_poleA n) (planb4_g1_poleB n).


(* ============================================================ *)
(* §2 Anchors n = 1..6: each an independent vm_compute bite of   *)
(*    the Laurent-fed channel against the certified zz_r_k /     *)
(*    zz_s_k literals (zzm1b_linform_bridge 143-224).            *)
(* ============================================================ *)

Example zz4_rs_1 : zzId (Qeq_bool (planb4_rs 1) zz_r_1) true.
Proof. vm_compute. reflexivity. Qed.
Example zz4_ss_1 : zzId (Qeq_bool (planb4_ss 1) zz_s_1) true.
Proof. vm_compute. reflexivity. Qed.

Example zz4_rs_2 : zzId (Qeq_bool (planb4_rs 2) zz_r_2) true.
Proof. vm_compute. reflexivity. Qed.
Example zz4_ss_2 : zzId (Qeq_bool (planb4_ss 2) zz_s_2) true.
Proof. vm_compute. reflexivity. Qed.

Example zz4_rs_3 : zzId (Qeq_bool (planb4_rs 3) zz_r_3) true.
Proof. vm_compute. reflexivity. Qed.
Example zz4_ss_3 : zzId (Qeq_bool (planb4_ss 3) zz_s_3) true.
Proof. vm_compute. reflexivity. Qed.

Example zz4_rs_4 : zzId (Qeq_bool (planb4_rs 4) zz_r_4) true.
Proof. vm_compute. reflexivity. Qed.
Example zz4_ss_4 : zzId (Qeq_bool (planb4_ss 4) zz_s_4) true.
Proof. vm_compute. reflexivity. Qed.

Example zz4_rs_5 : zzId (Qeq_bool (planb4_rs 5) zz_r_5) true.
Proof. vm_compute. reflexivity. Qed.
Example zz4_ss_5 : zzId (Qeq_bool (planb4_ss 5) zz_s_5) true.
Proof. vm_compute. reflexivity. Qed.

Example zz4_rs_6 : zzId (Qeq_bool (planb4_rs 6) zz_r_6) true.
Proof. vm_compute. reflexivity. Qed.
Example zz4_ss_6 : zzId (Qeq_bool (planb4_ss 6) zz_s_6) true.
Proof. vm_compute. reflexivity. Qed.


(* ============================================================ *)
(* §3 Extraction and assumption audit                            *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction planb4_rs planb4_ss.

Print Assumptions planb4_rs.
Print Assumptions planb4_ss.
Print Assumptions zz4_rs_1.
Print Assumptions zz4_ss_1.
Print Assumptions zz4_rs_2.
Print Assumptions zz4_ss_2.
Print Assumptions zz4_rs_3.
Print Assumptions zz4_ss_3.
Print Assumptions zz4_rs_4.
Print Assumptions zz4_ss_4.
Print Assumptions zz4_rs_5.
Print Assumptions zz4_ss_5.
Print Assumptions zz4_rs_6.
Print Assumptions zz4_ss_6.
