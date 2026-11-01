(* ==========================================================================
   Arch_PA_01.v - the uabT1 ssum / uabd1s4 two-half / idt slot / uabd2
   abs-id / uabd1s3 FEP / tmw temperature-mono families, Set-borne.
   Cure note.
     The source binder forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R}
     meets this world's zero-argument Class (S07 L8075); fix = binder
     removal with Notation R := Real and the real_eq / real_le / real_lt
     dependency faces; the absent UpReqRealFEP re-anchors on the
     landed UpReqFEPAttn. No Obj.magic, no Prop-ification.
   Mission.
     The uabT1_fw_ssum five slots, the uabd1s4 two-half chain and pack,
     the idt list-sum bridges, the uabd2 abs-id family, the uabd1s3 FEP
     instance family with extraction, the tmw temperature-mono family.
   Dependencies.
     S01..S15 chain, UpReqSumD, AttnDoeblin, S13_NLiveAudit,
     fa53_compat_abs, AbsLeId, UpReqFEPAttn, UpReqAlgebra, UpReqDist,
     UpReqTempEntropy, UpFirewallReq, Stdlib List / Extraction.
   References.
     sumd slots UpReqSumD L113-305; real_two_pos / real_list_sum S08
     L610 / L294; Id family S01 L41-73; ali_real_abs_ge_zero_id;
     fa53_abs_ge_zero_id_dec; real_le := Or (real_lt) (real_eq) S02
     L484; exp_neg_req_compat_setoid S10 L12502; UpReqTempEntropy
     L59-93 / L986 / L1452 / L652; UpFirewallReq L110-120.
   Constructivity.
     Statement faces all Set-layer; the bare premise Not (enum = nil)
     is the lawful premise-slot keep of the sum_pos interface; zero
     axioms; all stations Qed-closed with Print Assumptions blocks.
   Build.
     rocq c -native-compiler no -Q /tmp/nw10world "" Arch_PA_01.v (Rocq 9.1.0, cpu_guard, ulimit -s 65532).
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqSumD.
From Stdlib Require Import List.
Require Import AttnDoeblin.
Require Import fa53_compat_abs.
Require Import AbsLeId.
Require Import UpReqFEPAttn.
From Stdlib Require Import Extraction.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.

(* R := Real: this world's RealInterfaceEnhancedSetoid is the
   zero-argument Class; its fields resolve through the global instance
   RealEnhancedReal, so the family statements bind the carrier by
   notation (UpReqSumD L58 precedent). *)
Notation R := Real.

(* ================= Section 1: the uabT1_fw_ssum family ================= *)
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* G1 <- ssum_ext: pointwise real_eq lifts to the enumerated sum. *)
Theorem uabT1_fw_ssum_ext :
  forall (S : Set) (enum : list S) (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* G2 <- ssum_add: the sum of the pointwise sum is the sum of the sums. *)
Theorem uabT1_fw_ssum_add :
  forall (S : Set) (enum : list S) (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
            (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* G3 <- ssum_linear: constant factor pulls out of the enumerated sum. *)
Theorem uabT1_fw_ssum_linear :
  forall (S : Set) (enum : list S) (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s)))
            (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* G4 <- ssum_le: pointwise real_le lifts to the enumerated sum. *)
Theorem uabT1_fw_ssum_le :
  forall (S : Set) (enum : list S) (f g : S -> R),
    (forall s : S, real_le (f s) (g s)) ->
    real_le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* G5 <- ssum_pos: strictly positive pointwise data with a non-empty
   enumeration gives a strictly positive sum (explicit non-emptiness
   premise, the sumd_sum_pos interface shape). *)
Theorem uabT1_fw_ssum_pos :
  forall (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, real_lt zero (f s)) -> real_lt zero (sumd_sumf S enum f).
Proof.
  intros S enum Hne f H.
  exact (sumd_sum_pos S enum f Hne H).
Qed.

(* ============ PA closing block: per-item Closed adjudication ============ *)
Print Assumptions uabT1_fw_ssum_ext.
Print Assumptions uabT1_fw_ssum_add.
Print Assumptions uabT1_fw_ssum_linear.
Print Assumptions uabT1_fw_ssum_le.
Print Assumptions uabT1_fw_ssum_pos.

Print Assumptions uabT1_fw_ssum_pos.
Print Assumptions uabT1_fw_ssum_le.
Print Assumptions uabT1_fw_ssum_linear.
Print Assumptions uabT1_fw_ssum_add.
Print Assumptions uabT1_fw_ssum_ext.

(* ================= Section 2: the uabd1s4 two-half family ================= *)

(* The point-two constant and its strict positivity (S08 L610 face). *)
Definition uabd1s4_two : Real := real_plus real_one real_one.

Lemma uabd1s4_two_pos : real_lt real_zero uabd1s4_two.
Proof.
  exact real_two_pos.
Qed.

(* The half constant as the constructive inverse of two. *)
Definition uabd1s4_half : Real := real_inv_pos uabd1s4_two uabd1s4_two_pos.

Lemma uabd1s4_half_pos : real_lt real_zero uabd1s4_half.
Proof.
  exact (real_inv_pos_pos uabd1s4_two uabd1s4_two_pos).
Qed.

(* Normalization core: half + half == one, by the distrib / mult_comm /
   inv_pos_correct chain. *)
Lemma uabd1s4_half_plus_half : real_eq (real_plus uabd1s4_half uabd1s4_half) real_one.
Proof.
  exact (real_eq_trans
           (real_plus uabd1s4_half uabd1s4_half)
           (real_mult uabd1s4_half uabd1s4_two)
           real_one
           (real_eq_trans
              (real_plus uabd1s4_half uabd1s4_half)
              (real_plus (real_mult uabd1s4_half real_one)
                         (real_mult uabd1s4_half real_one))
              (real_mult uabd1s4_half uabd1s4_two)
              (RealSetoid.real_eq_plus_compat uabd1s4_half uabd1s4_half
                                   (real_mult uabd1s4_half real_one)
                                   (real_mult uabd1s4_half real_one)
                                   (real_eq_sym (real_mult uabd1s4_half real_one)
                                                uabd1s4_half
                                                (real_mult_one uabd1s4_half))
                                   (real_eq_sym (real_mult uabd1s4_half real_one)
                                                uabd1s4_half
                                                (real_mult_one uabd1s4_half)))
              (real_eq_sym
                 (real_mult uabd1s4_half uabd1s4_two)
                 (real_plus (real_mult uabd1s4_half real_one)
                            (real_mult uabd1s4_half real_one))
                 (real_distrib uabd1s4_half real_one real_one)))
           (real_eq_trans
              (real_mult uabd1s4_half uabd1s4_two)
              (real_mult uabd1s4_two uabd1s4_half)
              real_one
              (real_mult_comm uabd1s4_half uabd1s4_two)
              (real_inv_pos_correct uabd1s4_two uabd1s4_two_pos))).
Qed.

(* Uniform two-state supply: the two-element list sum of half equals one
   (cons fold of real_list_sum over seq 0 2). *)
Lemma uabd1s4_half_sum_two :
  real_eq (real_list_sum nat (fun _ : nat => uabd1s4_half) (List.seq 0 2)) real_one.
Proof.
  exact (real_eq_trans
           (real_list_sum nat (fun _ : nat => uabd1s4_half) (List.seq 0 2))
           (real_plus uabd1s4_half uabd1s4_half)
           real_one
           (RealSetoid.real_eq_plus_compat uabd1s4_half
                                (real_plus uabd1s4_half real_zero)
                                uabd1s4_half uabd1s4_half
                                (real_eq_refl uabd1s4_half)
                                (real_plus_zero uabd1s4_half))
           uabd1s4_half_plus_half).
Qed.

(* The twelve-slot pack: a finite Markov data pack with positive
   temperature, positive eta bounded by one, positive pit and piref
   families and a normalized pit sum. *)
Inductive uabd1s4_ske_pack12 : Set :=
| uabd1s4_ske_pack12_intro :
    forall k : nat,
      forall beta : Real,
        real_lt real_zero beta ->
        forall r : nat -> Real,
          forall eta : Real,
            real_lt real_zero eta ->
            real_le eta real_one ->
            forall pit : nat -> Real,
              (forall i : nat, real_lt real_zero (pit i)) ->
              real_eq (real_list_sum nat pit (List.seq 0 (Datatypes.S k))) real_one ->
              forall piref : nat -> Real,
                (forall i : nat, real_lt real_zero (piref i)) ->
                uabd1s4_ske_pack12.

(* The pack is inhabited: the half-function instance fills all twelve
   slots at k := 1. *)
Theorem uabd1s4_ske_pack12_supplied : uabd1s4_ske_pack12.
Proof.
  exact (uabd1s4_ske_pack12_intro 1%nat
          real_one real_lt_zero_one
          (fun _ : nat => real_zero)
          real_one real_lt_zero_one (real_le_refl real_one)
          (fun _ : nat => uabd1s4_half)
          (fun _ : nat => uabd1s4_half_pos)
          uabd1s4_half_sum_two
          (fun _ : nat => uabd1s4_half)
          (fun _ : nat => uabd1s4_half_pos)).
Qed.

(* ============ Assumption-face adjudication block ============ *)
Print Assumptions uabd1s4_two_pos.
Print Assumptions uabd1s4_half_pos.
Print Assumptions uabd1s4_half_plus_half.
Print Assumptions uabd1s4_half_sum_two.
Print Assumptions uabd1s4_ske_pack12_supplied.

(* PA follow-up adjudication block. *)
Print Assumptions uabd1s4_ske_pack12_supplied.
Print Assumptions uabd1s4_half_sum_two.
Print Assumptions uabd1s4_half_plus_half.
Print Assumptions uabd1s4_half_pos.
Print Assumptions uabd1s4_two_pos.

(* ================= Section 3: the idt_list_sum bridge family ================= *)
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* Section with the host context: bare S is the StateSpace projection
   resolved through the section instances (AttnDoeblin BoundedSoftmax
   preamble face); the abstract carrier is bound as Rc because the
   exported UpReqSumD abbreviation names R for the concrete Real. *)
Section IdSlotTranslate.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Local Existing Instance RI_base.
Let Rc := @S01_BaseRing.R RI.

(* Bridge 1: the interface-carried list fold, with the ring fields taken
   explicitly from RI. *)
Fixpoint idt_list_sum (f : S -> Rc) (l : list S) : Rc :=
  match l with
  | nil => @S01_BaseRing.zero RI
  | x :: t => @S01_BaseRing.plus RI (f x) (idt_list_sum f t)
  end.

(* The sum_over_S interface slot at the definitionally-resolved
   instance: idt_sumf unfolds to idt_list_sum. *)
Definition idt_sumf (enum : list S) (f : S -> Rc) : Rc :=
  idt_list_sum f enum.

(* Bridge 1 body: the Id-key; idt_sumf collapses definitionally into
   idt_list_sum, discharged by id_refl (no induction, no rewrite). *)
Lemma idt_sum_eq_list :
  forall (enum : list S) (g : S -> Rc),
    Id (idt_sumf enum g) (idt_list_sum g enum).
Proof.
  intros enum g.
  exact id_refl.
Qed.

(* Bridge 2: agreement with each host list-sum machine. On the cons
   shape both sides reduce by delta/iota and id_cong2 lifts the tail
   agreement; on nil both sides are the zero of RI (conversion, no
   neutral-argument trust). *)
Lemma idt_bs_list_sum_attn_agree :
  forall (f : S -> Rc) (l : list S),
    Id (idt_list_sum f l) (AttnDoeblin.bs_list_sum f l).
Proof.
  intros f l. induction l as [| x t IH].
  - exact id_refl.
  - exact (id_cong2 (@S01_BaseRing.plus RI) id_refl IH).
Qed.

Lemma idt_bs_list_sum_s13_agree :
  forall (f : S -> Rc) (l : list S),
    Id (idt_list_sum f l) (S13_NLiveAudit.bs_list_sum f l).
Proof.
  intros f l. induction l as [| x t IH].
  - exact id_refl.
  - exact (id_cong2 (@S01_BaseRing.plus RI) id_refl IH).
Qed.

(* ============ Four host verification slots ============ *)
(* Each slot states the sum_over_S := idt_sumf instance face against one
   host machine; the enumeration is universally quantified explicitly. *)

Theorem idt_slot_attdoeblin :
  forall (enum : list S) (g : S -> Rc),
    Id (idt_sumf enum g) (AttnDoeblin.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_attn_agree g enum).
Qed.

Theorem idt_slot_g01 :
  forall (enum : list S) (g : S -> Rc),
    Id (idt_sumf enum g) (AttnDoeblin.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_attn_agree g enum).
Qed.

Theorem idt_slot_s13 :
  forall (enum : list S) (g : S -> Rc),
    Id (idt_sumf enum g) (S13_NLiveAudit.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_s13_agree g enum).
Qed.

Theorem idt_slot_s15 :
  forall (enum : list S) (g : S -> Rc),
    Id (idt_sumf enum g) (S13_NLiveAudit.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_s13_agree g enum).
Qed.

(* ============ G4 evidence: seven items all Closed ============ *)
Print Assumptions idt_sum_eq_list.
Print Assumptions idt_bs_list_sum_attn_agree.
Print Assumptions idt_bs_list_sum_s13_agree.
Print Assumptions idt_slot_attdoeblin.
Print Assumptions idt_slot_g01.
Print Assumptions idt_slot_s13.
Print Assumptions idt_slot_s15.

End IdSlotTranslate.

Print Assumptions idt_slot_s15.
Print Assumptions idt_slot_s13.
Print Assumptions idt_slot_g01.
Print Assumptions idt_slot_attdoeblin.
Print Assumptions idt_sum_eq_list.

(* ================= Section 4: the uabd2 abs-id family ================= *)
(* Section context as in AbsLeId L35-46: the RI_base instance resolves
   the interface projections; after the section the pair form carries
   RI0 / DO0 as explicit leading arguments. *)
Section UabD2PairWorld.

Context {RI0 : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO0 : DecidableOrder RI0}.

Let Rc := @S01_BaseRing.R RI0.
Let le := @S01_BaseRing.le RI0.
Let zero := @S01_BaseRing.zero RI0.
Let abs := @S01_BaseRing.abs RI0.

Theorem uabd2_ali_abs_ge_zero_id_pair :
  forall a : Rc, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI0 DO0 a Ha).
Qed.

End UabD2PairWorld.

(* Post-section shape evidence: the section arguments are gone from the
   explicit head. *)
Check uabd2_ali_abs_ge_zero_id_pair.

(* The fully explicit form, all arguments on the head. *)
Theorem uabd2_ali_abs_ge_zero_id_explicit :
  forall (RI1 : RealInterfaceEnhanced) (DO1 : DecidableOrder RI1)
         (a : @S01_BaseRing.R RI1),
    @S01_BaseRing.le RI1 (@S01_BaseRing.zero RI1) a ->
    @S01_BaseRing.Id (@S01_BaseRing.R RI1) (@S01_BaseRing.abs RI1 a) a.
Proof.
  intros RI1 DO1 a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI1 DO1 a Ha).
Qed.

(* ---- Slot 1, real face: the concrete-Real abs-id (AbsLeId face). ---- *)
Theorem uabd2_ri_real_abs_ge_zero_id :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  exact ali_real_abs_ge_zero_id.
Qed.

(* ---- Slot 2, req face: the same statement through the interface
   projections of the global instance (le / zero / abs / req fields,
   delta-convertible with the real_* face). ---- *)
Theorem uabd2_ri_reqface_abs_ge_zero_id :
  forall a : Real,
    @RealInterfaceEnhancedMod.le RealInterfaceEnhancedMod.RealEnhancedReal
      (@RealInterfaceEnhancedMod.zero
         RealInterfaceEnhancedMod.RealEnhancedReal) a ->
    @RealInterfaceEnhancedMod.req RealInterfaceEnhancedMod.RealEnhancedReal
      (@RealInterfaceEnhancedMod.abs
         RealInterfaceEnhancedMod.RealEnhancedReal a) a.
Proof.
  exact ali_real_abs_ge_zero_id.
Qed.

(* ---- Slot 3, decidable-order face: the transparent unfold of
   real_le as Or (real_lt) (real_eq) (S02 L484). ---- *)
Theorem uabd2_do_ltle_iffdec_real :
  forall a b : Real,
    S01_BaseRing.Or (real_lt a b) (real_eq a b) -> real_le a b.
Proof.
  intros a b H.
  exact H.
Qed.

(* ============ PA self-adjudication block ============ *)
Print Assumptions uabd2_ali_abs_ge_zero_id_pair.
Print Assumptions uabd2_ali_abs_ge_zero_id_explicit.
Print Assumptions uabd2_ri_real_abs_ge_zero_id.
Print Assumptions uabd2_ri_reqface_abs_ge_zero_id.
Print Assumptions uabd2_do_ltle_iffdec_real.

Print Assumptions uabd2_do_ltle_iffdec_real.
Print Assumptions uabd2_ri_reqface_abs_ge_zero_id.
Print Assumptions uabd2_ri_real_abs_ge_zero_id.
Print Assumptions uabd2_ali_abs_ge_zero_id_explicit.
Print Assumptions uabd2_ali_abs_ge_zero_id_pair.

(* ================= Section 5: the uabd1s3 FEP instance family ================= *)
Import RealInterfaceEnhancedMod.

(* ---- Z: the Boltzmann non-normalized sum at the sumd instance. ---- *)
Definition uabd1s3_fep_st_Z (S0 : Set) (enum0 : list S0)
  (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D) : Real :=
  sumd_sumf S0 enum0
    (fun s : S0 => real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s))).

Lemma uabd1s3_fep_st_Z_pos :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D),
    real_lt real_zero (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos).
Proof.
  intros S0 enum0 Hne base_loss D D_pos.
  exact (sumd_sum_pos S0 enum0
          (fun s : S0 => real_exp_neg
                          (real_mult (real_inv_pos D D_pos) (base_loss s)))
          Hne
          (fun s : S0 => real_exp_neg_pos
                          (real_mult (real_inv_pos D D_pos) (base_loss s)))).
Qed.

(* ---- dist: the Boltzmann distribution inv(Z) . exp(- e(s) / D)
   (S08 L2491 shape, carried on the sumd instance). ---- *)
Definition uabd1s3_fep_st_dist (S0 : Set) (enum0 : list S0)
  (Hne : Not (enum0 = nil)) (base_loss : S0 -> Real) (D : Real)
  (D_pos : real_lt real_zero D) (s : S0) : Real :=
  real_mult
    (real_inv_pos (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
                  (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos))
    (real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s))).

(* ---- kernel: the independent proposal k(s, s') := dist(s'). ---- *)
Definition uabd1s3_fep_st_kernel (S0 : Set) (enum0 : list S0)
  (Hne : Not (enum0 = nil)) (base_loss : S0 -> Real) (D : Real)
  (D_pos : real_lt real_zero D) : S0 -> S0 -> Real :=
  fun _ s' => uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s'.

(* ---- Slot 1: the partition face as the opp-rewrite bridge: the sum of
   exp(- beta . (- z)) equals the sum of exp(- (beta . z)); the pointwise
   step is real_opp_mult lifted by exp_neg_req_compat_setoid (S10
   L12502). ---- *)
Theorem uabd1s3_fep_st_real_partition_condition :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (z0 : S0 -> Real) (T0 : Real) (HT0 : real_lt real_zero T0),
    real_eq (sumd_sumf S0 enum0
              (fun s : S0 => real_exp_neg
                              (real_mult (real_inv_pos T0 HT0)
                                         (real_opp (z0 s)))))
            (sumd_sumf S0 enum0
              (fun s : S0 => real_exp_neg
                              (real_opp
                                 (real_mult (real_inv_pos T0 HT0) (z0 s))))).
Proof.
  intros S0 enum0 Hne z0 T0 HT0.
  exact (sumd_sum_ext S0 enum0
          (fun s : S0 => real_exp_neg
                          (real_mult (real_inv_pos T0 HT0) (real_opp (z0 s))))
          (fun s : S0 => real_exp_neg
                          (real_opp (real_mult (real_inv_pos T0 HT0) (z0 s))))
          (fun s : S0 => exp_neg_req_compat_setoid _ _
                          (real_eq_sym _ _
                             (real_opp_mult (real_inv_pos T0 HT0) (z0 s))))).
Qed.

(* ---- Slot 2: transition non-negativity, strict form lifted to the
   non-strict face by real_lt_le_iff. ---- *)
Theorem uabd1s3_fep_st_real_transition_nonneg :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D)
         (s s' : S0),
    real_le real_zero (uabd1s3_fep_st_kernel S0 enum0 Hne base_loss D D_pos s s').
Proof.
  intros S0 enum0 Hne base_loss D D_pos s s'.
  apply real_lt_le_iff.
  left.
  exact (real_mult_positive
          (real_inv_pos (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
                        (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos))
          (real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s')))
          (real_inv_pos_pos (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
                            (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos))
          (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (base_loss s')))).
Qed.

(* ---- Slot 3: normalization: the kernel row sums to one; the partition
   premise holds definitionally since Z is that very sum. ---- *)
Theorem uabd1s3_fep_st_real_transition_normalization :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D)
         (s : S0),
    real_eq (sumd_sumf S0 enum0
              (fun s' : S0 => uabd1s3_fep_st_kernel S0 enum0 Hne base_loss D D_pos s s'))
            real_one.
Proof.
  intros S0 enum0 Hne base_loss D D_pos s.
  exact (real_eq_trans
          (sumd_sumf S0 enum0
             (fun s' : S0 =>
                uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s'))
          (real_mult
             (real_inv_pos (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
                           (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos))
             (sumd_sumf S0 enum0
                (fun s' : S0 => real_exp_neg
                                (real_mult (real_inv_pos D D_pos) (base_loss s')))))
          real_one
          (sumd_sum_linear S0 enum0
             (real_inv_pos (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
                           (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos))
             (fun s' : S0 => real_exp_neg
                             (real_mult (real_inv_pos D D_pos) (base_loss s'))))
          (real_eq_trans
             (real_mult
                (real_inv_pos (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
                              (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos))
                (sumd_sumf S0 enum0
                   (fun s' : S0 => real_exp_neg
                                   (real_mult (real_inv_pos D D_pos) (base_loss s')))))
             (real_mult
                (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
                (real_inv_pos (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
                              (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos)))
             real_one
             (real_mult_comm
                (real_inv_pos (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
                              (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos))
                (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos))
             (real_inv_pos_correct (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
                                   (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos)))).
Qed.

(* ---- Slot 4: detailed balance for the independent proposal kernel:
   dist(s) . k(s, s') == dist(s') . k(s', s) reduces to mult_comm. ---- *)
Theorem uabd1s3_fep_st_real_detailed_balance :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D)
         (s s' : S0),
    real_eq (real_mult (uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s)
                       (uabd1s3_fep_st_kernel S0 enum0 Hne base_loss D D_pos s s'))
            (real_mult (uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s')
                       (uabd1s3_fep_st_kernel S0 enum0 Hne base_loss D D_pos s' s)).
Proof.
  intros S0 enum0 Hne base_loss D D_pos s s'.
  exact (real_mult_comm (uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s)
                        (uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s')).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_fep_st_Z.ml" uabd1s3_fep_st_Z.

Print Assumptions uabd1s3_fep_st_Z_pos.
Print Assumptions uabd1s3_fep_st_real_partition_condition.
Print Assumptions uabd1s3_fep_st_real_transition_nonneg.
Print Assumptions uabd1s3_fep_st_real_transition_normalization.
Print Assumptions uabd1s3_fep_st_real_detailed_balance.

Print Assumptions uabd1s3_fep_st_real_detailed_balance.
Print Assumptions uabd1s3_fep_st_real_transition_normalization.
Print Assumptions uabd1s3_fep_st_real_transition_nonneg.
Print Assumptions uabd1s3_fep_st_real_partition_condition.
Print Assumptions uabd1s3_fep_st_Z_pos.

(* ================= Section 6: the tmw temperature-mono family ================= *)
Import RealInterfaceEnhancedMod.

(* Section TmwMonoW2: the premise block mirrors the
   UpReqTempEntropy ReqTempEntropy section slot by slot (L59-93), so the
   closed-form temperature theorems consume the section premises in
   declaration order. *)
Section TmwMonoW2.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- Summation face ---- *)
Hypothesis tmw_sum_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis tmw_sum_add :
  forall f g : S -> R,
    real_eq (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis tmw_sum_linear :
  forall (a : R) (f : S -> R),
    real_eq (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis tmw_sum_pos :
  forall f : S -> R, (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f).
Hypothesis tmw_sum_le :
  forall f g : S -> R, (forall s : S, real_le (f s) (g s)) -> real_le (sumf f) (sumf g).
Hypothesis tmw_sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, real_le zero (f s)) -> real_eq (sumf f) zero ->
    forall s : S, real_eq (f s) zero.

Variable base_loss : S -> R.

(* ---- Distribution log face ---- *)
Hypothesis tmw_dist_log_inv_one_inv :
  forall (x : R) (Hx : real_lt zero x) (Hi : real_lt zero (inv_pos x Hx)),
    real_eq (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis tmw_dist_log_exp_neg :
  forall u : R, real_eq (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis tmw_dist_log_le_linear :
  forall (x : R) (Hx : real_lt zero x), real_le (log x Hx) (req_minus x one).
Hypothesis tmw_dist_log_eq_linear :
  forall (x : R) (Hx : real_lt zero x),
    real_eq (log x Hx) (req_minus x one) -> real_eq x one.

(* ---- Z_temp interface ---- *)
Variable Z_temp : R -> R.
Hypothesis tmw_Z_temp_spec : forall (t : R) (Ht : real_lt zero t),
  real_eq (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

Theorem tmw_req_energy_exp_temp_mono_cond :
  forall (t1 t2 : R) (Ht1 : real_lt zero t1) (Ht2 : real_lt zero t2),
  real_lt t1 t2 ->
  real_lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
  real_le (@UpFirewallReq.fw_et S sumf tmw_sum_pos base_loss
                                Z_temp tmw_Z_temp_spec t1 Ht1)
          (@UpFirewallReq.fw_et S sumf tmw_sum_pos base_loss
                                Z_temp tmw_Z_temp_spec t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hbd.
  exact (UpReqTempEntropy.req_energy_exp_temp_mono
          S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos
          tmw_sum_le
          base_loss
          tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg
          tmw_dist_log_le_linear
          Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hbd).
Qed.

Theorem tmw_req_energy_exp_temp_strict_mono_cond :
  forall (t1 t2 : R) (Ht1 : real_lt zero t1) (Ht2 : real_lt zero t2),
  real_lt t1 t2 ->
  real_lt zero (req_relative_entropy S sumf
             (@UpFirewallReq.fw_bt S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t1 Ht1)
             (@UpFirewallReq.fw_bt_pos S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt_pos S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t1 Ht1)) ->
  real_lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
  real_lt zero (req_minus (@UpFirewallReq.fw_et S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                          (@UpFirewallReq.fw_et S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hkl Hbd.
  exact (UpReqTempEntropy.req_energy_exp_temp_strict_mono
          S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos
          tmw_sum_le
          base_loss
          tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg
          tmw_dist_log_le_linear
          Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl Hbd).
Qed.

Theorem tmw_req_energy_exp_temp_mono_full :
  (forall a b : R, real_lt a b -> real_lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : real_lt zero t1) (Ht2 : real_lt zero t2),
  real_lt t1 t2 ->
  real_le (@UpFirewallReq.fw_et S sumf tmw_sum_pos base_loss
                                Z_temp tmw_Z_temp_spec t1 Ht1)
          (@UpFirewallReq.fw_et S sumf tmw_sum_pos base_loss
                                Z_temp tmw_Z_temp_spec t2 Ht2).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt.
  exact (UpReqTempEntropy.req_energy_exp_temp_mono
          S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos
          tmw_sum_le
          base_loss
          tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg
          tmw_dist_log_le_linear
          Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt
          (Hlmn (inv_pos t2 Ht2) (inv_pos t1 Ht1)
                (UpReqTempEntropy.req_inv_pos_lt_contra t1 t2 Ht1 Ht2 Hlt))).
Qed.

Theorem tmw_req_energy_exp_temp_strict_mono_full :
  (forall a b : R, real_lt a b -> real_lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : real_lt zero t1) (Ht2 : real_lt zero t2),
  real_lt t1 t2 ->
  real_lt zero (req_relative_entropy S sumf
             (@UpFirewallReq.fw_bt S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t1 Ht1)
             (@UpFirewallReq.fw_bt_pos S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt_pos S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t1 Ht1)) ->
  real_lt zero (req_minus (@UpFirewallReq.fw_et S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                          (@UpFirewallReq.fw_et S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt Hkl.
  exact (UpReqTempEntropy.req_energy_exp_temp_strict_mono
          S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos
          tmw_sum_le
          base_loss
          tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg
          tmw_dist_log_le_linear
          Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl
          (Hlmn (inv_pos t2 Ht2) (inv_pos t1 Ht1)
                (UpReqTempEntropy.req_inv_pos_lt_contra t1 t2 Ht1 Ht2 Hlt))).
Qed.

(* The non-strict energy gap face, discharged by the full monotonicity
   witness and req_le_minus_nonneg (UpReqAlgebra L770). *)
Theorem tmw_le_minus_nonneg_fw_et :
  (forall a b : R, real_lt a b -> real_lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : real_lt zero t1) (Ht2 : real_lt zero t2),
  real_lt t1 t2 ->
  real_le zero (req_minus (@UpFirewallReq.fw_et S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                          (@UpFirewallReq.fw_et S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt.
  exact (req_le_minus_nonneg
          (@UpFirewallReq.fw_et S sumf tmw_sum_pos base_loss
                                Z_temp tmw_Z_temp_spec t1 Ht1)
          (@UpFirewallReq.fw_et S sumf tmw_sum_pos base_loss
                                Z_temp tmw_Z_temp_spec t2 Ht2)
          (tmw_req_energy_exp_temp_mono_full Hlmn t1 t2 Ht1 Ht2 Hlt)).
Qed.

End TmwMonoW2.

(* Print Assumptions adjudication block (five items, both directions). *)
Print Assumptions tmw_req_energy_exp_temp_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_mono_full.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_full.
Print Assumptions tmw_le_minus_nonneg_fw_et.

Print Assumptions tmw_le_minus_nonneg_fw_et.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_full.
Print Assumptions tmw_req_energy_exp_temp_mono_full.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_mono_cond.
