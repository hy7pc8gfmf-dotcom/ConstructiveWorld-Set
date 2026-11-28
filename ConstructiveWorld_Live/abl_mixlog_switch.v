(* ======================================================================== *)
(* Module   : abl_mixlog_switch                                             *)
(* Mission. The generic switch-tier calculator over the mixing-log numeric  *)
(*            tier: accept-station calculator msw_min_station = igr_k_enum  *)
(*            (generic least-passing-index enumeration) x msw_mix_test      *)
(*            (the (1-w)^k * tv0 < b0 truth test as a bool decider); the    *)
(*            sound/minimal/none correctness ledger, the Q-layer monotone   *)
(*            step-switch face (all-pass above the returned station), the   *)
(*            family-shape total piece msw_switch_tier, and the 91/22       *)
(*            instance back-core with the affine closed-form tier 91 as    *)
(*            the enum window (mixe_cf_select supplies H).                  *)
(* Dependencies. UpReqIterGeomRate (igr_k_enum, sound/none/min),            *)
(*            UpReqMixLogE (mixe_qlt_bool/mixe_qpow/mixe_qle_01/            *)
(*            mixe_cf_select, Q-order transport kit), S01_BaseRing (Id,     *)
(*            And, NatLe, id_eq_SI), S02_CauchyComplete (QltT/QleT'/QeqT);  *)
(*            Stdlib QArith/ZArith/Arith/PeanoNat/Lia/Extraction.           *)
(* References. UpReqIterGeomRate :1534/:1557/:1576/:1599 (igr_k_enum and    *)
(*            its sound/none/min ledger); UpReqMixLogE :41/:333/:685        *)
(*            (mixe_qlt_bool/mixe_qpow/mixe_cf_select);                     *)
(*            S02_CauchyComplete :150/:201/:227; S01_BaseRing :41/:88/:149. *)
(* Constructivity. Zero Prop statements: conclusions and premises sit on    *)
(*            the decidable Set carriers (Id bool equations, QltT/QleT'/    *)
(*            QeqT, NatLe, local msw_nat_lt); no Set carrier embeds a Prop  *)
(*            component. Prop derivation stays inside proof bodies only;    *)
(*            every closure is Defined, zero Qed (no pure-Prop bridge       *)
(*            lemma is stated); zero axioms, zero admits, no classical      *)
(*            logic; vm_compute confined to the concrete numeric pins.      *)
(* Build. coqc -native-compiler no -q -Q <Set Live root> ""                 *)
(*            abl_mixlog_switch.v (single shot, this directory as workdir). *)
(* ======================================================================== *)
From Stdlib Require Import QArith.QArith ZArith.ZArith.
From Stdlib Require Import PeanoNat Lia.

Require Import UpReqIterGeomRate.
Require Import UpReqMixLogE.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Section 1. The calculator. The generic enumerator eats any    *)
(* nat -> bool test; the test here is the Q-layer truth test     *)
(* (1-w)^k * tv0 < b0 decided as a bool. Both are Defined and    *)
(* extractable. The local Set carrier msw_nat_lt is the strict   *)
(* nat order on the boolean identity face.                       *)
(* ============================================================ *)

Definition msw_mix_test (w tv0 b0 : Q) (k : nat) : bool :=
  mixe_qlt_bool (mixe_qpow (1 - w) k * tv0) b0.

Definition msw_min_station (w tv0 b0 : Q) (H : nat) : option nat :=
  igr_k_enum (msw_mix_test w tv0 b0) H.

Definition msw_nat_lt (j k : nat) : Set := Id (Nat.ltb j k) true.

(* ============================================================ *)
(* Section 2. The three-limb correctness ledger of the station:  *)
(* a returned station passes the test; every index below it      *)
(* fails; None means every index in the window fails. All faces  *)
(* are boolean identity values on Set.                           *)
(* ============================================================ *)

Theorem msw_station_sound : forall (w tv0 b0 : Q) (H k : nat),
  Id (msw_min_station w tv0 b0 H) (Some k) ->
  Id (msw_mix_test w tv0 b0 k) true.
Proof.
  intros w tv0 b0 H k Hsel.
  apply id_eq_SI in Hsel.
  rewrite (igr_k_enum_sound (msw_mix_test w tv0 b0) H k Hsel).
  exact id_refl.
Defined.

Theorem msw_station_min : forall (w tv0 b0 : Q) (H k j : nat),
  Id (msw_min_station w tv0 b0 H) (Some k) -> msw_nat_lt j k ->
  Id (msw_mix_test w tv0 b0 j) false.
Proof.
  intros w tv0 b0 H k j Hsel Hjk.
  apply id_eq_SI in Hsel.
  assert (Hjk' : (j < k)%nat).
  { apply (proj1 (Nat.ltb_lt j k)). exact (id_eq_SI _ _ _ Hjk). }
  rewrite (igr_k_enum_min (msw_mix_test w tv0 b0) H k Hsel j Hjk').
  exact id_refl.
Defined.

Theorem msw_station_none : forall (w tv0 b0 : Q) (H j : nat),
  Id (msw_min_station w tv0 b0 H) None -> NatLe j H ->
  Id (msw_mix_test w tv0 b0 j) false.
Proof.
  intros w tv0 b0 H j Hnone Hj.
  apply id_eq_SI in Hnone.
  assert (Hj' : (j <= H)%nat) by exact (NatLe_drop j H Hj).
  rewrite (igr_k_enum_none (msw_mix_test w tv0 b0) H Hnone j Hj').
  exact id_refl.
Defined.

(* ============================================================ *)
(* Section 3. The bool ledger to the Q-order faces: a true test  *)
(* bit carries the strict order as a QltT value, a false bit     *)
(* carries the lower bound as a QleT' value.                     *)
(* ============================================================ *)

Theorem msw_test_true_lt : forall (w tv0 b0 : Q) (k : nat),
  Id (msw_mix_test w tv0 b0 k) true ->
  QltT (mixe_qpow (1 - w) k * tv0) b0.
Proof.
  intros w tv0 b0 k Hk.
  exact (mixe_qlt_bool_of_true _ _ (id_eq_SI _ _ _ Hk)).
Defined.

Theorem msw_test_false_ge : forall (w tv0 b0 : Q) (j : nat),
  Id (msw_mix_test w tv0 b0 j) false ->
  QleT' b0 (mixe_qpow (1 - w) j * tv0).
Proof.
  intros w tv0 b0 j Hj.
  apply id_eq_SI in Hj.
  unfold msw_mix_test, mixe_qlt_bool in Hj.
  destruct (Qlt_le_dec (mixe_qpow (1 - w) j * tv0) b0) as [Hd | Hd].
  - discriminate Hj.
  - exact (Qle_to_QleT' _ _ Hd).
Defined.

(* ============================================================ *)
(* Section 4. Monotone stepping and the switch face: above the   *)
(* returned station the test passes for every k without bound.   *)
(* ============================================================ *)

Theorem msw_qpow_step_le : forall (w tv0 : Q) (k : nat),
  QleT' 0 w -> QleT' w 1 -> QleT' 0 tv0 ->
  QleT' (mixe_qpow (1 - w) (Datatypes.S k) * tv0)
        (mixe_qpow (1 - w) k * tv0).
Proof.
  intros w tv0 k Hw0 Hw1 Htv0.
  assert (Hbase : QleT' 0 (1 - w))
    by exact (mixe_sub_nonneg w (QleT'_to_Qle _ _ Hw1)).
  assert (Hlow : QleT' (1 - w) 1)
    by exact (mixe_le_sub 1 w (QleT'_to_Qle _ _ Hw0)).
  assert (HP : QleT' 0 (mixe_qpow (1 - w) k))
    by exact (mixe_qpow_nonneg (1 - w) k (QleT'_to_Qle _ _ Hbase)).
  cbn [mixe_qpow].
  apply (mixe_qle_eq_r ((1 - w) * mixe_qpow (1 - w) k * tv0)
           (1 * mixe_qpow (1 - w) k * tv0)
           (mixe_qpow (1 - w) k * tv0)).
  - apply (Qmult_le_compat_r ((1 - w) * mixe_qpow (1 - w) k)
             (1 * mixe_qpow (1 - w) k) tv0).
    + exact (Qmult_le_compat_r (1 - w) 1 (mixe_qpow (1 - w) k)
               (QleT'_to_Qle _ _ Hlow) (QleT'_to_Qle _ _ HP)).
    + exact (QleT'_to_Qle _ _ Htv0).
  - rewrite (Qmult_1_l (mixe_qpow (1 - w) k)). reflexivity.
Defined.

Theorem msw_test_step : forall (w tv0 b0 : Q) (k : nat),
  QleT' 0 w -> QleT' w 1 -> QleT' 0 tv0 ->
  Id (msw_mix_test w tv0 b0 k) true ->
  Id (msw_mix_test w tv0 b0 (Datatypes.S k)) true.
Proof.
  intros w tv0 b0 k Hw0 Hw1 Htv0 Hk.
  unfold msw_mix_test.
  apply mixe_qlt_bool_true.
  apply (Qle_lt_trans (mixe_qpow (1 - w) (Datatypes.S k) * tv0)
           (mixe_qpow (1 - w) k * tv0) b0).
  - exact (QleT'_to_Qle _ _ (msw_qpow_step_le w tv0 k Hw0 Hw1 Htv0)).
  - exact (QltT_to_Qlt _ _ (msw_test_true_lt w tv0 b0 k Hk)).
Defined.

Theorem msw_test_add_d : forall (w tv0 b0 : Q) (d k : nat),
  QleT' 0 w -> QleT' w 1 -> QleT' 0 tv0 ->
  Id (msw_mix_test w tv0 b0 k) true ->
  Id (msw_mix_test w tv0 b0 (k + d)%nat) true.
Proof.
  intros w tv0 b0 d.
  induction d as [| d IH]; intros k Hw0 Hw1 Htv0 Hk.
  - rewrite (Nat.add_0_r k). exact Hk.
  - replace ((k + Datatypes.S d)%nat) with ((Datatypes.S (k + d))%nat) by lia.
    exact (msw_test_step w tv0 b0 (k + d)%nat Hw0 Hw1 Htv0
             (IH k Hw0 Hw1 Htv0 Hk)).
Defined.

Theorem msw_station_switch : forall (w tv0 b0 : Q) (H k j : nat),
  QleT' 0 w -> QleT' w 1 -> QleT' 0 tv0 ->
  Id (msw_min_station w tv0 b0 H) (Some k) -> NatLe k j ->
  Id (msw_mix_test w tv0 b0 j) true.
Proof.
  intros w tv0 b0 H k j Hw0 Hw1 Htv0 Hsel Hkj.
  assert (Hkj' : (k <= j)%nat) by exact (NatLe_drop k j Hkj).
  replace j with ((k + (j - k))%nat) by lia.
  exact (msw_test_add_d w tv0 b0 (j - k)%nat k Hw0 Hw1 Htv0
           (msw_station_sound w tv0 b0 H k Hsel)).
Defined.

Theorem msw_switch_tier : forall (w tv0 b0 : Q) (H : nat),
  QleT' 0 w -> QleT' w 1 -> QleT' 0 tv0 ->
  match msw_min_station w tv0 b0 H with
  | Some k =>
      And (Id (msw_mix_test w tv0 b0 k) true)
          (And (forall j : nat, msw_nat_lt j k ->
                 Id (msw_mix_test w tv0 b0 j) false)
               (forall j : nat, NatLe k j ->
                 Id (msw_mix_test w tv0 b0 j) true))
  | None => forall j : nat, NatLe j H -> Id (msw_mix_test w tv0 b0 j) false
  end.
Proof.
  intros w tv0 b0 H Hw0 Hw1 Htv0.
  destruct (msw_min_station w tv0 b0 H) as [k |] eqn:E.
  - assert (Hsel : Id (msw_min_station w tv0 b0 H) (Some k)).
    { rewrite E. exact id_refl. }
    split.
    + exact (msw_station_sound w tv0 b0 H k Hsel).
    + split.
      * intros j Hjk.
        exact (msw_station_min w tv0 b0 H k j Hsel Hjk).
      * intros j Hkj.
        exact (msw_station_switch w tv0 b0 H k j Hw0 Hw1 Htv0 Hsel Hkj).
  - assert (Hsel : Id (msw_min_station w tv0 b0 H) None).
    { rewrite E. exact id_refl. }
    intros j Hj. exact (msw_station_none w tv0 b0 H j Hsel Hj).
Defined.

(* ============================================================ *)
(* Section 5. The enumeration window only bounds the search: it  *)
(* never changes the first passing station.                      *)
(* ============================================================ *)

Theorem msw_enum_succ_some : forall (test : nat -> bool) (t k : nat),
  Id (igr_k_enum test t) (Some k) ->
  Id (igr_k_enum test (Datatypes.S t)) (Some k).
Proof.
  intros test t k H.
  apply id_eq_SI in H.
  cbn [igr_k_enum]. rewrite H. exact id_refl.
Defined.

Theorem msw_enum_window_mono : forall (test : nat -> bool) (d t k : nat),
  Id (igr_k_enum test t) (Some k) ->
  Id (igr_k_enum test (t + d)%nat) (Some k).
Proof.
  intros test d.
  induction d as [| d IH]; intros t k H.
  - rewrite (Nat.add_0_r t). exact H.
  - replace ((t + Datatypes.S d)%nat) with ((Datatypes.S (t + d))%nat) by lia.
    exact (msw_enum_succ_some test (t + d)%nat k (IH t k H)).
Defined.

(* ============================================================ *)
(* Section 6. Instance pins at w = 1/10, tv0 = 1, b0 = 1/10,     *)
(* all vm_compute on concrete numerals only.                     *)
(* ============================================================ *)

Theorem msw_qle_tenth_pos : QleT' 0 (1 # 10).
Proof. vm_compute. exact id_refl. Defined.

Theorem msw_qle_tenth_le_one : QleT' (1 # 10) 1.
Proof. vm_compute. exact id_refl. Defined.

Theorem msw_nat_lt_21_22 : msw_nat_lt 21 22.
Proof. unfold msw_nat_lt. vm_compute. exact id_refl. Defined.

Example msw_smoke_station_in_affine_window :
  Id (msw_min_station (1 # 10) 1 (1 # 10) (mixe_cf_select (1 # 10) (1 # 10) 1))
     (Some 22%nat).
Proof. vm_compute. exact id_refl. Defined.

Example msw_smoke_station_tight_22 :
  Id (msw_min_station (1 # 10) 1 (1 # 10) 22) (Some 22%nat).
Proof. vm_compute. exact id_refl. Defined.

Example msw_smoke_window_21_none :
  Id (msw_min_station (1 # 10) 1 (1 # 10) 21) None.
Proof. vm_compute. exact id_refl. Defined.

(* Any window H at least 22 returns the true minimal station 22. *)
Theorem msw_station_22_any_window : forall H : nat,
  NatLe 22 H -> Id (msw_min_station (1 # 10) 1 (1 # 10) H) (Some 22%nat).
Proof.
  intros H Hge.
  assert (Hge' : (22 <= H)%nat) by exact (NatLe_drop 22 H Hge).
  unfold msw_min_station.
  replace H with ((22 + (H - 22))%nat) by lia.
  exact (msw_enum_window_mono (msw_mix_test (1 # 10) 1 (1 # 10))
           (H - 22)%nat 22 22 msw_smoke_station_tight_22).
Defined.

(* ============================================================ *)
(* Section 7. The 91/22 back-core. The three concrete bridges    *)
(* identify (1 - 1/10)^k * 1 with (9/10)^k * 1 (k = 21,22,91);   *)
(* the 22 tier is re-proved through the generic interface, the   *)
(* 21 tier carries the lower bound, and the 91 accept face is    *)
(* derived from the 22 tier plus the switch face.                *)
(* ============================================================ *)

Theorem msw_eq_21 :
  QeqT (mixe_qpow (9 # 10) 21 * 1) (mixe_qpow (1 - (1 # 10)) 21 * 1).
Proof. vm_compute. exact id_refl. Defined.

Theorem msw_eq_22 :
  QeqT (mixe_qpow (9 # 10) 22 * 1) (mixe_qpow (1 - (1 # 10)) 22 * 1).
Proof. vm_compute. exact id_refl. Defined.

Theorem msw_eq_91 :
  QeqT (mixe_qpow (9 # 10) 91 * 1) (mixe_qpow (1 - (1 # 10)) 91 * 1).
Proof. vm_compute. exact id_refl. Defined.

Theorem msw_true_min_22 : QltT (mixe_qpow (9 # 10) 22 * 1) (1 # 10).
Proof.
  apply (mixe_qlt_eq_l (mixe_qpow (9 # 10) 22 * 1)
           (mixe_qpow (1 - (1 # 10)) 22 * 1) (1 # 10)).
  - exact (qeqT_imp_qeq _ _ msw_eq_22).
  - apply QltT_to_Qlt.
    apply (msw_test_true_lt (1 # 10) 1 (1 # 10) 22).
    exact (msw_station_sound (1 # 10) 1 (1 # 10)
             (mixe_cf_select (1 # 10) (1 # 10) 1) 22
             msw_smoke_station_in_affine_window).
Defined.

Theorem msw_below_21_not_accept : QleT' (1 # 10) (mixe_qpow (9 # 10) 21 * 1).
Proof.
  apply (mixe_qle_eq_r (1 # 10) (mixe_qpow (1 - (1 # 10)) 21 * 1)
           (mixe_qpow (9 # 10) 21 * 1)).
  - exact (QleT'_to_Qle _ _
            (msw_test_false_ge (1 # 10) 1 (1 # 10) 21
               (msw_station_min (1 # 10) 1 (1 # 10)
                  (mixe_cf_select (1 # 10) (1 # 10) 1) 22 21
                  msw_smoke_station_in_affine_window
                  msw_nat_lt_21_22))).
  - exact (Qeq_sym _ _ (qeqT_imp_qeq _ _ msw_eq_21)).
Defined.

Theorem msw_below_21_all_fail : forall j : nat,
  NatLe j 21 -> Id (msw_mix_test (1 # 10) 1 (1 # 10) j) false.
Proof.
  intros j Hj.
  exact (msw_station_none (1 # 10) 1 (1 # 10) 21 j
           msw_smoke_window_21_none Hj).
Defined.

Theorem msw_affine_cert_91 : QltT (mixe_qpow (9 # 10) 91 * 1) (1 # 10).
Proof.
  apply (mixe_qlt_eq_l (mixe_qpow (9 # 10) 91 * 1)
           (mixe_qpow (1 - (1 # 10)) 91 * 1) (1 # 10)).
  - exact (qeqT_imp_qeq _ _ msw_eq_91).
  - apply QltT_to_Qlt.
    apply (msw_test_true_lt (1 # 10) 1 (1 # 10) 91).
    apply (msw_station_switch (1 # 10) 1 (1 # 10)
             (mixe_cf_select (1 # 10) (1 # 10) 1) 22 91
             msw_qle_tenth_pos msw_qle_tenth_le_one mixe_qle_01
             msw_smoke_station_in_affine_window).
    apply NatLe_lift. lia.
Defined.

Example msw_select_cert_91_bool_switched :
  Id (mixe_qlt_bool (mixe_qpow (9 # 10) 91 * 1) (1 # 10)) true.
Proof.
  apply mixe_qlt_bool_true.
  exact (QltT_to_Qlt _ _ msw_affine_cert_91).
Defined.

(* ============================================================ *)
(* Assumption audit: one Print Assumptions per statement face.   *)
(* ============================================================ *)
Print Assumptions msw_station_sound.
Print Assumptions msw_station_min.
Print Assumptions msw_station_none.
Print Assumptions msw_test_true_lt.
Print Assumptions msw_test_false_ge.
Print Assumptions msw_qpow_step_le.
Print Assumptions msw_test_step.
Print Assumptions msw_test_add_d.
Print Assumptions msw_station_switch.
Print Assumptions msw_switch_tier.
Print Assumptions msw_enum_succ_some.
Print Assumptions msw_enum_window_mono.
Print Assumptions msw_qle_tenth_pos.
Print Assumptions msw_qle_tenth_le_one.
Print Assumptions msw_nat_lt_21_22.
Print Assumptions msw_smoke_station_in_affine_window.
Print Assumptions msw_smoke_station_tight_22.
Print Assumptions msw_smoke_window_21_none.
Print Assumptions msw_station_22_any_window.
Print Assumptions msw_eq_21.
Print Assumptions msw_eq_22.
Print Assumptions msw_eq_91.
Print Assumptions msw_true_min_22.
Print Assumptions msw_below_21_not_accept.
Print Assumptions msw_below_21_all_fail.
Print Assumptions msw_affine_cert_91.
Print Assumptions msw_select_cert_91_bool_switched.

(* ============================================================ *)
(* Extraction spot: the calculator body itself is Set-carried    *)
(* and extracts; the generic enumerator feeds it as a value.     *)
(* ============================================================ *)
From Stdlib Require Extraction.
Separate Extraction msw_min_station.
