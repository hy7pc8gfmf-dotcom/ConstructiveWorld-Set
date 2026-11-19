(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 SL4: statement faces and the    *)
(* pending-debt ledger of the Delta_n <> 0 witness-newness supply line.  *)
(* ===================================================================== *)

(** * planb4_sl4_skeleton: SL4 statement faces and pending-debt ledger.

    Mission.  Statement faces of the [Delta_n <> 0] supply line:
      the determinant face on the ab_def carrier, the born forall-n
      nonzero body, two growth-account targets, the ZZ2020
      proportionality half, and the twin Delta-slot premise faces.
      Every proof-shaped item is a registered debt; none claimed.

    Dependencies.  Stdlib QArith, ZArith; planb3_g1_calib (frozen
      n = 1..40 tables, fallback 0 above the domain); planb4_g1_ab_def
      (total A/B : nat -> Z carrier; legal for forall-n faces: tables
      read 0 above n = 40, planb_b_nlo q > 40 for q >= 2^79).

    References.  hesc18:111-163/:1587-1643; rs_channel:44-54;
      laur_extract:144-189 (n = 1..6 only); u5_carrier_align
      :58-65/:127-129/:279-280; g2_design:170-180; ZZ2020 MJCT 9
      (2020) 407-419; fourslots:101-116.

    Constructivity.  Every named face is Set-carried through
      decidable Id-of-boolean predicates, sigT existence over Q and
      Set products; no assumption commands; all definitions
      transparent.

    Build.  coqc -Q <live-tree-root> "" planb4_sl4_skeleton.v
      (Rocq 9.3.0, single lane under cpu_guard_v3). *)

From Stdlib Require Import QArith.QArith ZArith.ZArith.
Require Import planb3_g1_calib.
Require Import planb4_g1_ab_def.

(* ================================================================== *)
(* Section 0. Decidable Set carriers: the Id-of-boolean recast of     *)
(*            the QltT/QeqT family at the Z, nat and Q faces.         *)
(* ================================================================== *)

(* the truth-carrying identity type over Set. *)
Inductive sl4_Id {A : Set} (x : A) : A -> Set :=
| sl4_id_refl : sl4_Id x x.

Arguments sl4_id_refl {A} {x}.

(* Z-face equality / disequality / order; Q-face equality; nat order. *)
Definition sl4_ZeqT (a b : Z) : Set := sl4_Id (Z.eqb a b) true.
Definition sl4_ZneT (a b : Z) : Set := sl4_Id (Z.eqb a b) false.
Definition sl4_ZleT (a b : Z) : Set := sl4_Id (Z.leb a b) true.
Definition sl4_QeqT (a b : Q) : Set := sl4_Id (Qeq_bool a b) true.
Definition sl4_NatLeT (a b : nat) : Set := sl4_Id (Nat.leb a b) true.

(* ================================================================== *)
(* Section 1. The named determinant face (closed definition; the      *)
(*            carrier is the TOTAL ab_def pair, per survey 1.2-1).    *)
(* ================================================================== *)

(* Delta n is the dodge determinant of the consecutive witness pair:  *)
(* A n * B (S n) - A (S n) * B n, the verbatim shape consumed by the  *)
(* dodge chain (hesc18:109/:1592/:1625-1627), now named and bound to  *)
(* the total carrier planb4_g1_A/planb4_g1_B instead of the frozen    *)
(* n = 1..40 table.  A definition, not a claim.                       *)
Definition planb4_sl4_delta (n : nat) : Z :=
  (planb4_g1_A n * planb4_g1_B (S n)
   - planb4_g1_A (S n) * planb4_g1_B n)%Z.

(* ================================================================== *)
(* Section 2. The born forall-n nonzero body (the SL4 breakthrough    *)
(*            target; born statement, honestly unproven / NOT         *)
(*            claimed).                                               *)
(* ================================================================== *)

(* Survey section 5, the breakthrough row: the missing piece is one   *)
(* constructive Rocq carrier of strict linear-form decay times       *)
(* reduced-denominator growth.  This statement is its landing shape,  *)
(* with nonzero-ness carried by the decidable Z disequality face.     *)
Definition planb4_sl4_delta_nz : Set :=
  forall n : nat, sl4_ZneT (planb4_sl4_delta n) 0%Z.

(* ================================================================== *)
(* Section 3. Route B, half 1: the B-side growth account (born        *)
(*            statement, honestly unproven / NOT claimed).            *)
(* ================================================================== *)

(* Machine survey (survey section 3, exact Z over the frozen table):  *)
(* |B| monotone with zero violations on n = 1..39, per-step bit       *)
(* growth min 6 max 32, |B_1| at 13 bits.  The constant 6 below is    *)
(* the conservative table-extrapolated pin; the forall-n face is the  *)
(* debt (Laurent product structure, general-n face = P6 debt).        *)
(* The order side is the decidable nat/Z pair sl4_NatLeT/sl4_ZleT.    *)
Definition planb4_sl4_bgrowth : Set :=
  forall n : nat, sl4_NatLeT 1 n ->
    sl4_ZleT (2 ^ Z.of_nat ((6 * (n - 1))%nat)) (Z.abs (planb4_g1_B n)).

(* ================================================================== *)
(* Section 4. Route B, half 2: the reduced-denominator gcd bound      *)
(*            (born statement, honestly unproven / NOT claimed).      *)
(* ================================================================== *)

(* d_n := |B n| / gcd(|A n|, |B n|) - the reduced denominator of the  *)
(* witness fraction.  Survey section 3: the criterion holds on        *)
(* n = 1..40 with huge margin (n = 40: d_n at 632 bits vs threshold   *)
(* 100 bits).  Threshold form 2^((5n-1)/2) = 2^(ceil(5n/2)-1), the    *)
(* M1:329 criterion (i) pin (survey section 2, skeleton C).  The      *)
(* forall-n face is the N2c-chain debt (g2_design:170-180).           *)
Definition planb4_sl4_denom_reduced (n : nat) : Z :=
  (Z.abs (planb4_g1_B n)
   / Z.gcd (Z.abs (planb4_g1_A n)) (Z.abs (planb4_g1_B n)))%Z.

Definition planb4_sl4_denom_bound : Set :=
  forall n : nat, sl4_NatLeT 1 n ->
    sl4_ZleT (2 ^ ((Z.of_nat n * 5 - 1) / 2)) (planb4_sl4_denom_reduced n).

(* ================================================================== *)
(* Section 5. Route ZZ, algebraic half: proportionality on zero       *)
(*            determinant (born statement, honestly unproven / NOT    *)
(*            claimed).                                               *)
(* ================================================================== *)

(* ZZ2020 nonzeroness-automatic-since-I_n-to-0 recast (survey         *)
(* section 2, skeleton A): if Delta n = 0 the two coefficient pairs   *)
(* are proportional over Q, so I_(S n) = lambda * I_n with            *)
(* |lambda| = |B (S n)| / |B n| >= 1 under monotone growth - blocking *)
(* any strict decay.  THIS statement is the pure-Z/Q algebraic half   *)
(* (rank-1 proportionality of a 2x2 pair with zero determinant over   *)
(* the fraction field); the decay half needs the |I_n| carrier l2_dv  *)
(* and is NOT stated in this file - it is debt D-SL4-6, registered on *)
(* the joint SL2 carrier face (fourslots:112-116).                    *)
(* The witness half is Set-carried: sigT over Q, the conjunctive pair *)
(* the Set product, each proportionality conjunct the decidable Q     *)
(* equality face sl4_QeqT (Qeq_bool reflects the fraction-field       *)
(* equality of the original face verbatim).                           *)
Definition planb4_sl4_proportional_on_zero : Set :=
  forall n : nat, sl4_ZeqT (planb4_sl4_delta n) 0%Z ->
    sigT (fun l : Q =>
      prod (sl4_QeqT (inject_Z (planb4_g1_A (S n)))
                     (Qmult l (inject_Z (planb4_g1_A n))))
           (sl4_QeqT (inject_Z (planb4_g1_B (S n)))
                     (Qmult l (inject_Z (planb4_g1_B n))))).

(* ================================================================== *)
(* Section 6. The twin Delta-slot premise faces (consumption shapes;  *)
(*            born statements, honestly unproven / NOT claimed).      *)
(* ================================================================== *)

(* The current consumption premise of window_route/global is stated   *)
(* at the FROZEN carrier, verbatim hesc18:1592-1594/:1625-1627, with  *)
(* the concrete picker planb_b_nlo (planb1:215-217).  The picker      *)
(* enters here as a generic function argument (postulate-free: a      *)
(* plain function argument of each face); a consuming module          *)
(* instantiates it at planb_b_nlo or at a repaired picker.            *)

(* The frozen-carrier face - the carrier the tree consumes today.     *)
(* Domain honesty: this premise is literally false for q >= 2^79      *)
(* (the picker lands above the table, both slots read 0, the          *)
(* subtracted determinant is 0), which is exactly why the swap debt   *)
(* D-SL4-2 exists (survey section 1.2; calib:79/:261).                *)
Definition planb4_sl4_window_slot_frozen (nlo : nat -> nat) : Set :=
  forall q : nat, sl4_NatLeT 1 q ->
    sl4_ZneT (planb3_g1_A (nlo q) * planb3_g1_B (S (nlo q))
              - planb3_g1_A (S (nlo q)) * planb3_g1_B (nlo q)) 0%Z.

(* The ab_def-carrier twin - the swap target; identical shape, total  *)
(* carrier.  Literally the instance planb4_sl4_delta (nlo q) <> 0.    *)
Definition planb4_sl4_window_slot_abdef (nlo : nat -> nat) : Set :=
  forall q : nat, sl4_NatLeT 1 q ->
    sl4_ZneT (planb4_sl4_delta (nlo q)) 0%Z.

(* ================================================================== *)
(* Section 7. Pending-debt ledger (comments only; mirror of the       *)
(*            appended survey-volume section; each row is             *)
(*            independently actionable; estimates are EXTRAPOLATED,   *)
(*            UNCALIBRATED; nothing in this ledger is claimed,        *)
(*            proven, or priced beyond the survey volume's own        *)
(*            no-pricing-before-survey law).                          *)
(* ================================================================== *)

(* D-SL4-1  table-domain anchor blank. *)
(*   target statement : planb4_sl4_delta (Section 1) plus vm_compute  *)
(*     readings n = 1..39, 39/39 true (the survey's exact-Z           *)
(*     readings, survey section 3, recast as born Examples in a       *)
(*     build file).                                                   *)
(*   dependencies     : planb4_g1_ab_def (in tree); survey section 3. *)
(*   estimate         : about 0.5-1 work units (extrapolated,         *)
(*     uncalibrated; the survey slice S-1 share).                      *)
(*   review condition : any carrier or table change re-anchors.       *)

(* D-SL4-2  carrier swap above the forced band. *)
(*   target statement : planb4_sl4_window_slot_abdef (Section 6)      *)
(*     assembled as the twin of window_route/global for q >= 2^79     *)
(*     addresses; the frozen face (Section 6) stays as the in-domain  *)
(*     twin; signature of hesc18 untouched (stability law).           *)
(*   dependencies     : D-SL4-1; hesc18:1587-1643 consumption faces.  *)
(*   estimate         : about 1-3 work units (extrapolated,           *)
(*     uncalibrated; the survey slice S-2 share; S-1 + S-2 within     *)
(*     the survey's 2-4 total).                                       *)
(*   review condition : any hesc18 signature change re-prices.        *)

(* D-SL4-3  B-side growth account (breakthrough half 1). *)
(*   target statement : planb4_sl4_bgrowth (Section 3).               *)
(*   dependencies     : Laurent product structure general-n; the      *)
(*     poleA well-definedness face is the P6 debt (M1:437); r/s       *)
(*     channel table-certified n = 1..6 only (laur_extract:144-189,   *)
(*     rs_channel:59-88); survey section 3 readings.                  *)
(*   estimate         : about 4-10 work units (extrapolated,          *)
(*     uncalibrated).                                                 *)
(*   review condition : P6 progress, N2c landing, or SL2 slotting     *)
(*     forces re-estimate (M1:319(a) reverse-isomorphic gate).        *)

(* D-SL4-4  reduced-denominator gcd bound (breakthrough half 2). *)
(*   target statement : planb4_sl4_denom_bound (Section 4).           *)
(*   dependencies     : D-SL4-3; the G4/N2c chain                     *)
(*     (g2_design:170-180 registration; M1:329 upstream list).        *)
(*   estimate         : about 4-10 work units (extrapolated,          *)
(*     uncalibrated).                                                 *)
(*   review condition : any gcd upper-bound lemma landing in tree     *)
(*     forces re-estimate.                                            *)

(* D-SL4-5  proportionality half, ZZ algebraic limb. *)
(*   target statement : planb4_sl4_proportional_on_zero (Section 5).  *)
(*   dependencies     : none upstream - pure Z/Q algebra over the     *)
(*     Section 1 face; the smallest startable piece of the ledger.    *)
(*   estimate         : about 1-2 work units (extrapolated,           *)
(*     uncalibrated; classical rank-1 fact, constructive carrier).    *)
(*   review condition : none external; lands and waits for the        *)
(*     decay half to consume it.                                      *)

(* D-SL4-6  decay half, SL2 joint face (NOT stated in this file). *)
(*   target statement : strict decay of |l2_dv (A n) (B n)| forall n  *)
(*     on the hcage-slot carrier (fourslots:112-116); to be minted    *)
(*     on the joint SL2 carrier line, not by this skeleton.           *)
(*   dependencies     : SL2 slotting; ZZ2020 v2 source verbatim       *)
(*     survey (G3 disk src_v2/pimeas_v2.tex, 34,929 B, unread per     *)
(*     survey section 8); S02/LW1PiMeasure dependency closure.        *)
(*   estimate         : about 6-12 work units (extrapolated,          *)
(*     uncalibrated).                                                 *)
(*   review condition : any SL2 |I_n| certificate forces immediate    *)
(*     re-estimate (survey section 5, review condition 3).            *)

(* D-SL4-7  forall-n body confluence and consumption wiring. *)
(*   target statement : planb4_sl4_delta_nz (Section 2) plus the      *)
(*   instance planb4_sl4_window_slot_abdef planb_b_nlo feeding the    *)
(*   q >= 2^79 band of the escape face.                               *)
(*   dependencies     : (D-SL4-3 AND D-SL4-4 AND D-SL4-5, by the      *)
(*   growth-route contradiction) OR (D-SL4-5 AND D-SL4-6, by the      *)
(*   ZZ-route contradiction); D-SL4-2 for wiring.                     *)
(*   estimate         : about 2-5 work units (extrapolated,           *)
(*   uncalibrated; confluence only - the mathematical content lives   *)
(*   upstream).                                                       *)
(*   review condition : any upstream limb landing forces re-estimate. *)

(* D-SL4-8  depth-warning remainder (review-driven only). *)
(*   target statement : witness pdiv retirement note face; Laurent    *)
(*   multi-sum bite advanced past n = 2 (u5:58-65 OOM register).      *)
(*   dependencies     : u5_carrier_align:127-129/:279-280;            *)
(*   piu_zz_kernel_sum.                                               *)
(*   estimate         : about 2-6 work units (extrapolated,          *)
(*   uncalibrated).                                                   *)
(*   review condition : dispatched only if skeleton D (recurrence)    *)
(*   is re-priced; it is the sole re-evaluation channel of the        *)
(*   pure-algebraic route (rs_channel:44-54, no recurrence face).     *)

(* ================================================================== *)
(* Section 8. Assumption audit.                                       *)
(* ================================================================== *)

Print Assumptions planb4_sl4_delta.
Print Assumptions planb4_sl4_denom_reduced.
Print Assumptions planb4_sl4_delta_nz.
Print Assumptions planb4_sl4_bgrowth.
Print Assumptions planb4_sl4_denom_bound.
Print Assumptions planb4_sl4_proportional_on_zero.
Print Assumptions planb4_sl4_window_slot_frozen.
Print Assumptions planb4_sl4_window_slot_abdef.

(* ================= end of statement faces and ledger ============== *)
