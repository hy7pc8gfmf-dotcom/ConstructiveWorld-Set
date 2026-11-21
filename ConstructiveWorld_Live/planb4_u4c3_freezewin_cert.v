(** * planb4_u4c3_freezewin_cert: the full-window census certificate
      (U4-C3: the frozen-window n = 1..40 face plus the kernel-sum
      cross route).

    Mission.  The fold censuses over the declared frozen window:
      [awin]/[bwin] (the pipeline [planb4_g1_A]/[planb4_g1_B] bites
      the frozen [planb3_g1_A]/[planb3_g1_B] arm at every n <= k),
      [symwin] (antipodal Laurent readouts agree entrywise via
      [zz_lqeqb]) and [allb_nz] (the assembled-B nonzero mirror of
      the calibration census); the kernel-sum cross pins
      [nth j (planb4_g1_poleA 1) 0] = [piu_zz_Aj 1 j] (j = 0..3) and
      [nth 0 (planb4_g1_poleA 2)] = [piu_zz_Aj 2 0] (disjoint routes
      over one face); the sigma = 17 tension face at n = 5 stays an
      honest registered tension; each census is anchored at its k.
    Dependencies.  planb3_g1_calib (the frozen comparison target of
      record); zzm1b_linform_bridge ([zz_lqeqb]);
      planb4_g1_laur_extract ([planb4_g1_poleA]/[planb4_g1_poleB]);
      planb4_g1_rs_assembly (the general-n A/B lift);
      piu_zz_kernel_sum ([piu_zz_Aj], the cross route).
    References.  ZZ2020 Prop 1; zzm1b zz_r_1 = 5636/3, zz_s_1 = -598,
      zz_r_2 = -3078046528/105, zz_s_2 = 9331168; kernel-sum
      A_{1,0} = -2392, A_{1,3} = 8000; n1_linform A_{1,1} = 6880,
      A_{1,2} = -11200, A_{2,0} = 37324672.
    Constructivity.  Transparent Fixpoint censuses over bool; the
      census-intro lemmas close by induction and end Defined; the
      numeric anchors close by vm_compute; admission-free and
      postulate-free throughout.
    Build.  coqc -native-compiler no -q -Q . "" planb4_u4c3_freezewin_cert.v
      (Rocq 9.3.0, single lane under cpu_guard_v3). *)
From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Require Import planb3_g1_calib.
Require Import zzm1b_linform_bridge.
Require Import planb4_g1_laur_extract.
Require Import planb4_g1_rs_assembly.
Require Import piu_zz_kernel_sum.

(* ============================================================ *)
(* Section 1. The census Fixpoints over the declared window.     *)
(* ============================================================ *)

(* the A-channel table bite census: at every n <= k the assembled  *)
(* pipeline channel equals the frozen table arm. *)
Fixpoint planb4_g1_awin (k : nat) : bool :=
  match k with
  | O => true
  | S k' => andb (Z.eqb (planb4_g1_A (S k')) (planb3_g1_A (S k')))
                 (planb4_g1_awin k')
  end.

(* the B-channel twin census. *)
Fixpoint planb4_g1_bwin (k : nat) : bool :=
  match k with
  | O => true
  | S k' => andb (Z.eqb (planb4_g1_B (S k')) (planb3_g1_B (S k')))
                 (planb4_g1_bwin k')
  end.

(* the pole-symmetry census: the antipodal Laurent readouts agree  *)
(* entry by entry at every n <= k (the 5 vs -5 numerator swap).    *)
Fixpoint planb4_g1_symwin (k : nat) : bool :=
  match k with
  | O => true
  | S k' =>
      andb (zz_lqeqb (planb4_g1_poleA (S k')) (planb4_g1_poleB (S k')))
           (planb4_g1_symwin k')
  end.

(* the assembled-B nonzero census mirror of planb3_g1_allb_nz      *)
(* (planb3_g1_calib.v:228-232) over the pipeline B channel. *)
Fixpoint planb4_g1_allb_nz (k : nat) : bool :=
  match k with
  | O => true
  | S k' => andb (negb (Z.eqb (planb4_g1_B (S k')) 0))
                 (planb4_g1_allb_nz k')
  end.

(* census transfer: a table bite census plus a nonzero table       *)
(* census carry the assembled nonzero census, point-free over the  *)
(* whole range (no recomputation of the B pipeline is needed). *)
Lemma planb4_g1_allb_nz_mono : forall k : nat,
  planb4_g1_bwin k = true -> planb3_g1_allb_nz k = true ->
  planb4_g1_allb_nz k = true.
Proof. induction k as [|k' IH]; intros Hw Hc.
  - reflexivity.
  - cbn [planb4_g1_allb_nz planb4_g1_bwin planb3_g1_allb_nz] in Hw, Hc |- *.
    apply andb_true_intro. split.
    + apply andb_true_iff in Hw. destruct Hw as [Heq _].
      apply andb_true_iff in Hc. destruct Hc as [Hnz _].
      apply Z.eqb_eq in Heq. rewrite Heq. exact Hnz.
    + apply IH.
      * apply andb_true_iff in Hw. destruct Hw as [_ Ht]. exact Ht.
      * apply andb_true_iff in Hc. destruct Hc as [_ Ht]. exact Ht.
Defined.

(* ============================================================ *)
(* Section 2. The frozen-table nonzero census at k = 40.          *)
(* ============================================================ *)

(* cheap table fold; the same face is carried by
   planb3_g1_calib_cert.v:36 as planb3_g1_b_nonzero_dom, restated
   here so this unit's require closure stays on planb3_g1_calib. *)
Example planb4_u4c3_calib_allb_nz_40 : planb3_g1_allb_nz 40%nat = true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* Section 3. The kernel-sum cross: the Laurent pole readout vs   *)
(* the Gaussian-series A_j (two disjoint routes over one face).   *)
(* ============================================================ *)

(* Route law.  planb4_g1_poleA n reads A_{n,j} off the Laurent
   chain (pdivmod -> pshift -> Laurent, planb4_g1_laur_extract:101);
   piu_zz_Aj n j sums the Gaussian pair series (piu_zz_kernel_sum.v
   :632).  The certified overlap window is n <= 2: the kernel route
   series zz_Mj n 0 already spans 114795 terms at n = 8
   (piu_zz_n1_linform zz_len_sample_8_0), so beyond n = 2 the
   kernel route leaves the declared computable domain (the
   registered OOM bound).  Certified in-tree sample points:
   A_{1,j} = [-2392; 6880; -11200; 8000] and A_{2,0} = 37324672. *)

Example planb4_u4c3_ksA_1_0 :
  Qeq_bool (nth 0%nat (planb4_g1_poleA 1%nat) 0%Q) (piu_zz_Aj 1%nat 0%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_ksA_1_1 :
  Qeq_bool (nth 1%nat (planb4_g1_poleA 1%nat) 0%Q) (piu_zz_Aj 1%nat 1%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_ksA_1_2 :
  Qeq_bool (nth 2%nat (planb4_g1_poleA 1%nat) 0%Q) (piu_zz_Aj 1%nat 2%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_ksA_1_3 :
  Qeq_bool (nth 3%nat (planb4_g1_poleA 1%nat) 0%Q) (piu_zz_Aj 1%nat 3%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_ksA_2_0 :
  Qeq_bool (nth 0%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 0%nat) = true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* Section 4. The sigma=17 tension face on the pipeline channel.  *)
(* ============================================================ *)

(* The honest non-claim: the assembled pipeline channel at n = 5
   reproduces the registered calibration tension
   (planb3_g1_calib_cert.v:27, 2^85 < |A 5|), so the pipeline is
   faithful AND the tension is inherited on the general-n face.
   This is explicitly NOT a supply of the planb3_g1_hcoef17_face
   design statement (planb3_g1_g2_design.v:175-179): the A-side
   slot fails at the n = 5 witness, and that failure stays
   registered here as an honest tension, not repaired. *)
Example planb4_u4c3_tension_A5 :
  Z.ltb (2 ^ 85)%Z (Z.abs (planb4_g1_A 5%nat)) = true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* Section 5. Census introduction: pointwise bites give the fold. *)
(* ============================================================ *)

(* The k = 40 fold anchors are carried by the companion segment
   files planb4_u4c3_freezewin_s1..s5 (per-point vm_compute bites,
   the pointwise discipline registered at planb4_g1_rs_assembly.v
   :226-236) and assembled by planb4_u4c3_freezewin_40.v.
   The intro lemmas here are the general induction glue. *)

Lemma planb4_g1_awin_intro : forall k : nat,
  (forall n : nat, (1 <= n)%nat -> (n <= k)%nat ->
     Z.eqb (planb4_g1_A n) (planb3_g1_A n) = true) ->
  planb4_g1_awin k = true.
Proof. induction k as [|k' IH]; intros H.
  - reflexivity.
  - cbn [planb4_g1_awin]. apply andb_true_intro. split.
    + apply H; lia.
    + apply IH. intros n H1 H2. apply H; lia.
Defined.

Lemma planb4_g1_bwin_intro : forall k : nat,
  (forall n : nat, (1 <= n)%nat -> (n <= k)%nat ->
     Z.eqb (planb4_g1_B n) (planb3_g1_B n) = true) ->
  planb4_g1_bwin k = true.
Proof. induction k as [|k' IH]; intros H.
  - reflexivity.
  - cbn [planb4_g1_bwin]. apply andb_true_intro. split.
    + apply H; lia.
    + apply IH. intros n H1 H2. apply H; lia.
Defined.

Lemma planb4_g1_symwin_intro : forall k : nat,
  (forall n : nat, (1 <= n)%nat -> (n <= k)%nat ->
     zz_lqeqb (planb4_g1_poleA n) (planb4_g1_poleB n) = true) ->
  planb4_g1_symwin k = true.
Proof. induction k as [|k' IH]; intros H.
  - reflexivity.
  - cbn [planb4_g1_symwin]. apply andb_true_intro. split.
    + apply H; lia.
    + apply IH. intros n H1 H2. apply H; lia.
Defined.

(* ============================================================ *)
(* Section 6. Extraction differential and assumption audit.       *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction planb4_g1_awin planb4_g1_bwin planb4_g1_symwin
  planb4_g1_allb_nz.

Print Assumptions planb4_g1_awin.
Print Assumptions planb4_g1_bwin.
Print Assumptions planb4_g1_symwin.
Print Assumptions planb4_g1_allb_nz.
Print Assumptions planb4_g1_allb_nz_mono.
Print Assumptions planb4_u4c3_calib_allb_nz_40.
Print Assumptions planb4_u4c3_ksA_1_0.
Print Assumptions planb4_u4c3_ksA_1_1.
Print Assumptions planb4_u4c3_ksA_1_2.
Print Assumptions planb4_u4c3_ksA_1_3.
Print Assumptions planb4_u4c3_ksA_2_0.
Print Assumptions planb4_u4c3_tension_A5.
Print Assumptions planb4_g1_awin_intro.
Print Assumptions planb4_g1_bwin_intro.
Print Assumptions planb4_g1_symwin_intro.
