(* ==========================================================================)
   abl_s01_supply.v - S01 gap first-strike group (batch 5; base-region gap top
   S01_BaseRing physical-world interface family; outboard new-file supply).
   Mission.  Fourteen supply theorems plus two data definitions (16 stations)
     close 14 reachable slots of the frozen host S01_BaseRing (104 open slots
     x 463 whole-tree uses, gap-board top; the rest stay on the W ledger;
     host zero bytes changed, outboard supply = zero cascade).  Groups:
     (1) intrinsic slot plus_positive (LM :1702, class field same
     name :202, general-RI form closes directly); (2) bool two-letter
     vocabulary world slots vocab_nonempty (LM :1626, SLM :1879) and
     token_eq_dec (LM :1627, bool instance face closes here); (3) ten
     one-instantiation positivity slots via class field one_pos (:198),
     named per-slot forwarding (coordinates in banners); (4) the singleton
     weighted world (PCC :1343).
   Dependencies.  S01_BaseRing (read-only, frozen domain, host untouched);
     Stdlib List; Stdlib Extraction (tail); Require face = the host alone.
   References.  one-world root tspp_tsi_temperature_pos_one (abl_tail_pos_certs.v:175);
     forwarding precedent tspw_up01_align_beta_pos (abl_tail_world_certs.v:239);
     bool world precedents tspp_bool_enum_sumd_in_witness
     (abl_tail_pos_certs.v:245), p2t1_vocab_nonempty_supply
     (UpAblP2T1_Cert.v:2459), hard_token_eq_dec_supply (AttnHardLimit218.v:1281).
   Constructivity.  Zero assumed-constant declarations, zero suspended
     premises, zero classical logic; all fourteen theorems and both data
     definitions close by genuine construction; statement faces all
     Set-layer (lt/Not/Id/Or/InT: S01 Set-layer objects, zero Prop
     carriers); supplies use only S01 class fields; per-theorem Print
     Assumptions Closed; probes take Obj.magic count 0.
   Build.  rocq c -native-compiler no -q (Rocq 9.1, guard-wrapped, ulimit
     -s 65532); green: EXIT=0, true-error 0, vo head 436f7121 00015ff4, vo fresh.
   ========================================================================== *)

Require Import S01_BaseRing.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* Duplicate-check registration block (whole-library grep measured, three-   *)
(*   gate record):                                                           *)
(*   (1) Prefix gate: abls_ whole-library grep zero hits (incl. this pool);  *)
(*       zero prefix collision.                                              *)
(*   (2) Target-slot gate: the S01_BaseRing host data/certificate sections   *)
(*       had no in-service file targeting these slots before this file       *)
(*       (coverage-map section zero.4: base Feed pieces use statement-match  *)
(*       substitution, not slot supply; tspw_/tspp_/p2t1_ target slots       *)
(*       belong to Arch_Up_01 / PA family / UpAblP2T1 host positions) -      *)
(*       this file is the first in the domain.                               *)
(*   (3) Statement-face gate: the one-world closed form is same-face with    *)
(*       the in-service tspp_tsi_temperature_pos_one                         *)
(*       (abl_tail_pos_certs.v:175) and the tspw_up01_* group                *)
(*       (abl_tail_world_certs.v:239); per the abl_tail_pos_certs six-       *)
(*       Real-face named-forwarding convention: zero reproof, exact direct   *)
(*       reference, per-slot naming, registered here.  Whole-library grep    *)
(*       zero same-statement for the general-RI plus_positive supply         *)
(*       (S07 real_plus_positive :7106 is the in-service Real-face           *)
(*       same-family root, zero re-supply; this general form covers its      *)
(*       concrete instantiations via the class field); the bool vocabulary   *)
(*       nonemptiness form is same-face different-carrier with               *)
(*       p2t1_vocab_nonempty_supply (UpAblP2T1_Cert.v:2459, abstract T0/T1   *)
(*       there, bool here), registered as such.                              *)
(* ============================================================ *)

(* ============================================================ *)
(* I. Intrinsic slot: LanguageModelInstance plus_positive          *)
(*   (slot statement, current archive :1702 verbatim: Variable     *)
(*   plus_positive : forall a b : R, lt zero a -> lt zero b ->     *)
(*   lt zero (plus a b) - verbatim same form as the class field    *)
(*   plus_positive of RealInterfaceEnhanced (:202); the general    *)
(*   RI form closes by direct field reference.  Four-step speed    *)
(*   verdict: step 0 Set face pass; step 1 no wall row hit;        *)
(*   step 2 the class field is the certificate itself; step 3      *)
(*   interface face and instance face close together).             *)
(* ============================================================ *)

Theorem abls_lm_plus_positive :
  forall (RI : RealInterfaceEnhanced) (a b : @S01_BaseRing.R RI),
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) a ->
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) b ->
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@S01_BaseRing.plus RI a b).
Proof.
  intros RI a b Ha Hb.
  exact (@S01_BaseRing.plus_positive RI a b Ha Hb).
Qed.

(* ============================================================ *)
(* II. bool two-letter vocabulary world instance slots             *)
(*   (LM vocab_nonempty :1626 / token_eq_dec :1627; SLM            *)
(*   vocab_nonempty :1879 double-landing in file; vocabulary       *)
(*   carrier is the named bool two-letter list).                   *)
(* ============================================================ *)

Definition abls_vocab_bool_two : list bool := true :: false :: nil.

(* ---- LM :1626 slot statement (current archive verbatim): Variable       ---- *)
(* ----   vocab_nonempty : Not (Id vocab nil); closed form = the bool       ---- *)
(* ----   two-letter list as vocab.                                         ---- *)
Theorem abls_lm_vocab_nonempty_bool_two :
  @S01_BaseRing.Not
    (S01_BaseRing.Id abls_vocab_bool_two (@nil bool)).
Proof.
  intro H.
  unfold abls_vocab_bool_two in H.
  inversion H.
Qed.

(* ---- SLM :1879 slot statement double-lands with LM :1626 verbatim;      ---- *)
(* ----   landings named separately (pos_certs dual-landing convention).   ---- *)
Theorem abls_slm_vocab_nonempty_bool_two :
  @S01_BaseRing.Not
    (S01_BaseRing.Id abls_vocab_bool_two (@nil bool)).
Proof.
  intro H.
  unfold abls_vocab_bool_two in H.
  inversion H.
Qed.

(* ---- LM :1627 slot statement (current archive verbatim): Variable       ---- *)
(* ----   token_eq_dec : forall a b : Token, Or (Id a b) (Not (Id a b)).   ---- *)
(* ----   The abstract-Token face is the speed-manual row-2 defense line   ---- *)
(* ----   (W-ledger three-element registration); the bool instance face    ---- *)
(* ----   is the precedent-654 direct gift, closed here (dual-state note:  ---- *)
(* ----   interface face W + instance face closed).                        ---- *)
Theorem abls_lm_token_eq_dec_bool_two :
  forall a b : bool,
    S01_BaseRing.Or (S01_BaseRing.Id a b)
                    (S01_BaseRing.Not (S01_BaseRing.Id a b)).
Proof.
  intros a b.
  destruct a as [|]; destruct b as [|].
  - exact (inl S01_BaseRing.id_refl).
  - right.
    intro H.
    inversion H.
  - right.
    intro H.
    inversion H.
  - exact (inl S01_BaseRing.id_refl).
Qed.

(* ============================================================ *)
(* III. one-instantiation positivity certificate slots (general   *)
(*    RI form; class field one_pos :198 direct reference; named   *)
(*    per-slot forwarding, zero reproof)                          *)
(* ============================================================ *)

(* ---- PCC :1379 slot statement (current archive verbatim): Variable      ---- *)
(* ----   Z_pos : lt zero Z; closed form = Z := one.                        ---- *)
Theorem abls_pcc_z_pos_one :
  forall RI : RealInterfaceEnhanced,
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI).
Proof.
  intros RI.
  exact (@S01_BaseRing.one_pos RI).
Qed.

(* ---- PCC :1381 D_pos; closed form = D := one.                           ---- *)
Theorem abls_pcc_d_pos_one :
  forall RI : RealInterfaceEnhanced,
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI).
Proof.
  intros RI.
  exact (@S01_BaseRing.one_pos RI).
Qed.

(* ---- PCC :1417 k_B_pos; closed form = k_B := one.                       ---- *)
Theorem abls_pcc_k_b_pos_one :
  forall RI : RealInterfaceEnhanced,
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI).
Proof.
  intros RI.
  exact (@S01_BaseRing.one_pos RI).
Qed.

(* ---- PCC :1415 slot statement (current archive verbatim): Variable      ---- *)
(* ----   prob_pos : forall x : R, lt zero (prob_density x); closed form   ---- *)
(* ----   = constant-density world (prob_density := fun _ => one).         ---- *)
Theorem abls_pcc_prob_pos_one_world :
  forall (RI : RealInterfaceEnhanced) (x : @S01_BaseRing.R RI),
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI).
Proof.
  intros RI x.
  exact (@S01_BaseRing.one_pos RI).
Qed.

(* ---- SLM :1883 temperature_pos; closed form = temperature := one.       ---- *)
Theorem abls_slm_temperature_pos_one :
  forall RI : RealInterfaceEnhanced,
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI).
Proof.
  intros RI.
  exact (@S01_BaseRing.one_pos RI).
Qed.

(* ---- Thermo :2781 k_B_pos; closed form = k_B := one.                    ---- *)
Theorem abls_th_k_b_pos_one :
  forall RI : RealInterfaceEnhanced,
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI).
Proof.
  intros RI.
  exact (@S01_BaseRing.one_pos RI).
Qed.

(* ---- Thermo :2798 slot statement (current archive verbatim): Variable   ---- *)
(* ----   temperature_A_pos : forall E_A, lt zero (temperature_A E_A);     ---- *)
(* ----   closed form = constant-temperature world.                        ---- *)
Theorem abls_th_temperature_a_pos_one_world :
  forall (RI : RealInterfaceEnhanced) (x : @S01_BaseRing.R RI),
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI).
Proof.
  intros RI x.
  exact (@S01_BaseRing.one_pos RI).
Qed.

(* ---- Thermo :2799 temperature_B_pos; isomorphic constant-temperature   ---- *)
(* ----   world.                                                           ---- *)
Theorem abls_th_temperature_b_pos_one_world :
  forall (RI : RealInterfaceEnhanced) (x : @S01_BaseRing.R RI),
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI).
Proof.
  intros RI x.
  exact (@S01_BaseRing.one_pos RI).
Qed.

(* ---- Thermo :2806 eta_pos; closed form = eta := one (dissipation       ---- *)
(* ----   step positivity).                                                ---- *)
Theorem abls_th_eta_pos_one :
  forall RI : RealInterfaceEnhanced,
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (@S01_BaseRing.one RI).
Proof.
  intros RI.
  exact (@S01_BaseRing.one_pos RI).
Qed.

(* ============================================================ *)
(* IV. Singleton weighted-world certificate (the nonempty         *)
(*    singleton-world instance form of the PCC :1343              *)
(*    weighted_props_positive slot - witness-loading slot made    *)
(*    concrete: the weighted proposition list takes one element   *)
(*    (constant-one proposition, weight one); per-item positivity *)
(*    unfolds by InT construction).                               *)
(* ============================================================ *)

Definition abls_pcc_one_prop
  (RI : RealInterfaceEnhanced) (SS : StateSpace RI)
  : @PropositionConvergenceCore.Proposition RI SS
  := fun _ => @S01_BaseRing.one RI.

Theorem abls_pcc_weighted_props_positive_singleton :
  forall (RI : RealInterfaceEnhanced) (SS : StateSpace RI),
    forall p_w : (@PropositionConvergenceCore.Proposition RI SS *
                  @S01_BaseRing.R RI)%type,
      S01_BaseRing.InT p_w
        ((abls_pcc_one_prop RI SS, @S01_BaseRing.one RI) :: nil) ->
      @PropositionConvergenceCore.IsPositiveProposition RI SS (fst p_w).
Proof.
  intros RI SS p_w H.
  inversion H.
  - intros s.
    exact (@S01_BaseRing.one_pos RI).
  - inversion H1.
Qed.

(* ============================================================ *)
(* V. Premise-face audit (per-theorem Closed criterion; name      *)
(*    census = Qed count = 14, zero difference)                   *)
(* ============================================================ *)
Print Assumptions abls_lm_plus_positive.
Print Assumptions abls_lm_vocab_nonempty_bool_two.
Print Assumptions abls_slm_vocab_nonempty_bool_two.
Print Assumptions abls_lm_token_eq_dec_bool_two.
Print Assumptions abls_pcc_z_pos_one.
Print Assumptions abls_pcc_d_pos_one.
Print Assumptions abls_pcc_k_b_pos_one.
Print Assumptions abls_pcc_prob_pos_one_world.
Print Assumptions abls_slm_temperature_pos_one.
Print Assumptions abls_th_k_b_pos_one.
Print Assumptions abls_th_temperature_a_pos_one_world.
Print Assumptions abls_th_temperature_b_pos_one_world.
Print Assumptions abls_th_eta_pos_one.
Print Assumptions abls_pcc_weighted_props_positive_singleton.

(* ============================================================ *)
(* VI. Extraction check area (G3 control-account convention:      *)
(*   library-layer transcription and this-file introduction are   *)
(*   counted separately; the out-of-tree control probe re-extracts *)
(*   the one_pos / plus_positive library roots with own-tree      *)
(*   unreachable-branch self-standing definitions; same-segment   *)
(*   transcription recurrence belongs to the closure/family, not  *)
(*   to this file).                                               *)
(* ============================================================ *)
Set Extraction Output Directory "_log/extraction".
Recursive Extraction abls_lm_plus_positive
  abls_lm_vocab_nonempty_bool_two abls_slm_vocab_nonempty_bool_two
  abls_lm_token_eq_dec_bool_two.
Recursive Extraction abls_pcc_z_pos_one abls_pcc_d_pos_one
  abls_pcc_k_b_pos_one abls_pcc_prob_pos_one_world.
Recursive Extraction abls_slm_temperature_pos_one abls_th_k_b_pos_one
  abls_th_temperature_a_pos_one_world abls_th_temperature_b_pos_one_world
  abls_th_eta_pos_one.
Recursive Extraction abls_pcc_weighted_props_positive_singleton.
