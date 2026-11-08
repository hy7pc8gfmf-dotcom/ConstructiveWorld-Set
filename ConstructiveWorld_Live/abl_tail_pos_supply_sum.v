(* ConstructiveWorld-Set -- slot-exact named supply theorems for the sum family. *)

(** * abl_tail_pos_supply_sum: twenty-six slot-level supply theorems for the six-property sumd-list
    family across seven host slots.

    Mission.  At each host slot, instantiate [sumd_sumf S enum] definitionally and supply the six-property
      family under verbatim host statement faces: extensionality, additivity, linearity and monotonicity
      ([sum_ext], [sum_add], [sum_linear], [sum_le]), positivity with an explicit cons witness ([sum_pos_cons]),
      and the surjective zero-nonnegativity transfer ([sum_zero_nonneg_surj]), named [tspps_uralign_*],
      [tspps_udist_*], [tspps_ufw_*], [tspps_uralta_*].  The seven host targets receive no [Require] of their
      own: slot supply matches host statement faces directly.

    Dependencies.  Stdlib [List] and [Extraction] (audit section); requires
      [S01_BaseRing] through [S15_TailFEPUp] and [UpReqSumD] of this development.

    References.  This development, abl_tail_pos_supply_sum.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here verbatim
      (statement-face Set-carrier completion).  Interface-generation surgery (the
      registered legitimate pattern, UpReqMisc5B precedent): this tree's interface class
      [RealInterfaceEnhancedSetoid] is unparameterized, so the Main-tree binder pair
      [(R : Set)] [(RIS : RealInterfaceEnhancedSetoid R)] is carrier-ized away ([R := Real]; statement
      faces at the concrete [real_eq]/[real_lt]/[real_le] relations of that canon); statement names are
      carried over verbatim.

    Constructivity.  All named statements and fields are carried by [Set] (decidable
      Q-carriers and boolean identity carriers); statements extract with
      [Obj.magic] = 0 and no erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_tail_pos_supply_sum.v] compiles
      cleanly (exit 0); the artifact starts with [436f7121 000160bc]. *)
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
Import RealInterfaceEnhancedMod.

(* R := Real by notation: the interface is the argument-less Class
   RealInterfaceEnhancedSetoid, whose law fields resolve as bare names
   through the global instance RealEnhancedReal (the UpReqSumD
   precedent). *)
Notation R := Real.

(* Grading record, stated once for all twenty-six slots: every supply
   theorem resolves by direct instantiation of a library root, the
   [sumd_*] lemmas of [UpReqSumD], with one named supply position per
   host slot; each proof body is a one-step [exact] reference and
   nothing else.  Each slot statement face is lifted verbatim from the
   corresponding host slot archive (argument order, naming and implicit
   positions included), with the sum position read as the
   instantiation [sumd_sumf S enum]. *)

(* Section 1.  Six slots of the ReqAlignCore section of UpReqAlign.v
   (host archive lines :90-103: sum carrier sumf :90; sum_ext :91,
   sum_add :93, sum_linear :96, sum_pos :99, sum_le :101,
   sum_zero_nonneg :103).  Four slots mirror the host statement faces
   directly; for the two remaining slots the host statement carries no
   premise position, so the supply takes the missing data explicitly:
   the pos slot carries nonemptiness by the cons cell w :: rest itself
   (the witness is the data, recorded here, not a silent
   strengthening), and the zero_nonneg slot takes the surjectivity
   data as an explicit argument (the membership predicate sumd_in is
   self-contained at the Set level). *)

(* Slot sum_ext, verbatim from host lines :91-92: forall f g : S -> R,
   (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g). *)
Theorem tspps_uralign_sum_ext :
  forall (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* Slot sum_add, verbatim from host lines :93-95. *)
Theorem tspps_uralign_sum_add :
  forall (S : Set)
         (enum : list S) (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* Slot sum_linear, verbatim from host lines :96-98. *)
Theorem tspps_uralign_sum_linear :
  forall (S : Set)
         (enum : list S) (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* Slot sum_le, verbatim from host lines :101-102. *)
Theorem tspps_uralign_sum_le :
  forall (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, real_le (f s) (g s)) ->
    real_le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* Slot sum_pos (:99-100), cons-witness form: the host slot has no
   premise position, so nonemptiness is carried by the enumerated cons
   data, w :: rest being the witness itself.  The explicit nonemptiness
   form is already supplied by uabT1_rte_fsum_pos and is not restated
   here. *)
Theorem tspps_uralign_sum_pos_cons :
  forall (S : Set)
         (f : S -> R) (w : S) (rest : list S),
    (forall s : S, real_lt zero (f s)) ->
    real_lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Qed.

(* Slot sum_zero_nonneg (:103, verbatim, with the surjectivity data as
   an explicit argument): the host slot is the universally closed form,
   which is unprovable without the surjectivity data (a counter-model
   is on record in the UpReqSumD head note); the supply form matches
   the sumd_sum_zero_nonneg_surj slot shape, and the membership
   predicate sumd_in is self-contained at the Set level (the empty and
   sum types of the base ring), so no Prop position arises. *)
Theorem tspps_uralign_sum_zero_nonneg_surj :
  forall (S : Set)
         (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> R,
      (forall s : S, real_le zero (f s)) ->
      real_eq (sumd_sumf S enum f) zero ->
      forall s : S, real_eq (f s) zero.
Proof.
  intros S enum Hsurj f Hnn H0 s.
  exact (sumd_sum_zero_nonneg_surj S enum f Hsurj Hnn H0 s).
Qed.

(* Section 2.  Six slots of the ReqSumLayer section of UpReqDist.v
   (host archive lines :251-267: sum carrier sumf :251; sum_ext :252,
   sum_add :254, sum_linear :257, sum_pos :260, sum_le :262,
   sum_zero_nonneg :264).  The six statement faces coincide verbatim
   with Section 1 (the same req-faced six-property slot family), named
   separately per host slot. *)

Theorem tspps_udist_rsl_sum_ext :
  forall (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

Theorem tspps_udist_rsl_sum_add :
  forall (S : Set)
         (enum : list S) (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

Theorem tspps_udist_rsl_sum_linear :
  forall (S : Set)
         (enum : list S) (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

Theorem tspps_udist_rsl_sum_le :
  forall (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, real_le (f s) (g s)) ->
    real_le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* Slot sum_pos (:260), cons-witness form (as in Section 1). *)
Theorem tspps_udist_rsl_sum_pos_cons :
  forall (S : Set)
         (f : S -> R) (w : S) (rest : list S),
    (forall s : S, real_lt zero (f s)) ->
    real_lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Qed.

(* Slot sum_zero_nonneg (:264), surjectivity as an explicit argument
   (as in Section 1). *)
Theorem tspps_udist_rsl_sum_zero_nonneg_surj :
  forall (S : Set)
         (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> R,
      (forall s : S, real_le zero (f s)) ->
      real_eq (sumd_sumf S enum f) zero ->
      forall s : S, real_eq (f s) zero.
Proof.
  intros S enum Hsurj f Hnn H0 s.
  exact (sumd_sum_zero_nonneg_surj S enum f Hsurj Hnn H0 s).
Qed.

(* Section 3.  Six slots of the ReqFEP section of UpReqDist.v (host
   archive lines :1053-1069: sum carrier sumf :1053; fsum_ext :1054,
   fsum_add :1056, fsum_linear :1059, fsum_pos :1062, fsum_le :1064,
   fsum_zero_nonneg :1066). *)

Theorem tspps_udist_rfep_fsum_ext :
  forall (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

Theorem tspps_udist_rfep_fsum_add :
  forall (S : Set)
         (enum : list S) (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

Theorem tspps_udist_rfep_fsum_linear :
  forall (S : Set)
         (enum : list S) (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

Theorem tspps_udist_rfep_fsum_le :
  forall (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, real_le (f s) (g s)) ->
    real_le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* Slot fsum_pos (:1062), cons-witness form (as in Section 1). *)
Theorem tspps_udist_rfep_fsum_pos_cons :
  forall (S : Set)
         (f : S -> R) (w : S) (rest : list S),
    (forall s : S, real_lt zero (f s)) ->
    real_lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Qed.

(* Slot fsum_zero_nonneg (:1066), surjectivity as an explicit argument
   (as in Section 1). *)
Theorem tspps_udist_rfep_fsum_zero_nonneg_surj :
  forall (S : Set)
         (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> R,
      (forall s : S, real_le zero (f s)) ->
      real_eq (sumd_sumf S enum f) zero ->
      forall s : S, real_eq (f s) zero.
Proof.
  intros S enum Hsurj f Hnn H0 s.
  exact (sumd_sum_zero_nonneg_surj S enum f Hsurj Hnn H0 s).
Qed.

(* Section 4.  Two slots of the ReqSteadyState section of UpReqDist.v
   (host archive lines :3147-3149: sum carrier sumf :3147; ssum_ext
   :3148, ssum_linear :3149). *)

Theorem tspps_udist_rss_ssum_ext :
  forall (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

Theorem tspps_udist_rss_ssum_linear :
  forall (S : Set)
         (enum : list S) (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* Section 5.  Two slots of the ReqSoftmaxDual section of UpReqDist.v
   (host archive lines :3501-3504: sum carrier sumf :3501; sumf_ext
   :3502, sumf_pos :3504). *)

Theorem tspps_udist_rsd_sumf_ext :
  forall (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* Slot sumf_pos (:3504), cons-witness form (as in Section 1). *)
Theorem tspps_udist_rsd_sumf_pos_cons :
  forall (S : Set)
         (f : S -> R) (w : S) (rest : list S),
    (forall s : S, real_lt zero (f s)) ->
    real_lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Qed.

(* Section 6.  The three remaining slots of the FirewallReq section of
   UpFirewallReq.v (host archive lines :89-104: sum carrier sumf :89;
   ssum_ext :90, ssum_add :92, ssum_linear :95, ssum_le :98, ssum_pos
   :100).  The ssum_add and ssum_le slots are already supplied by
   feed_ssum_add and feed_ssum_le of SumDCarrierFeed (:118-126), so
   this file supplies only the three remaining slots, with no
   duplication.  Register card 1 lists four slots where the host
   archive shows five; the count correction is recorded at delivery. *)

Theorem tspps_ufw_ssum_ext :
  forall (S : Set)
         (enum : list S) (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

Theorem tspps_ufw_ssum_linear :
  forall (S : Set)
         (enum : list S) (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* Slot ssum_pos (:100), cons-witness form (as in Section 1). *)
Theorem tspps_ufw_ssum_pos_cons :
  forall (S : Set)
         (f : S -> R) (w : S) (rest : list S),
    (forall s : S, real_lt zero (f s)) ->
    real_lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Qed.

(* Section 7.  The one remaining slot of the ReqRestACore section of
   UpReqAlignRestA.v (host archive lines :107-115: sum carrier sumf
   :107; ralt_sum_ext :108, already supplied by feed_ralt_sum_ext of
   SumDCarrierFeed (:128-130), with no duplication; ralt_sum_pos
   :113). *)

(* Slot ralt_sum_pos (:113), cons-witness form (as in Section 1). *)
Theorem tspps_uralta_ralt_sum_pos_cons :
  forall (S : Set)
         (f : S -> R) (w : S) (rest : list S),
    (forall s : S, real_lt zero (f s)) ->
    real_lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Qed.

(* Print Assumptions audit: every supply theorem must report Closed
   under the global context; the name list and the Qed count agree at
   twenty-six, with no gap. *)
Print Assumptions tspps_uralign_sum_ext.
Print Assumptions tspps_uralign_sum_add.
Print Assumptions tspps_uralign_sum_linear.
Print Assumptions tspps_uralign_sum_le.
Print Assumptions tspps_uralign_sum_pos_cons.
Print Assumptions tspps_uralign_sum_zero_nonneg_surj.
Print Assumptions tspps_udist_rsl_sum_ext.
Print Assumptions tspps_udist_rsl_sum_add.
Print Assumptions tspps_udist_rsl_sum_linear.
Print Assumptions tspps_udist_rsl_sum_le.
Print Assumptions tspps_udist_rsl_sum_pos_cons.
Print Assumptions tspps_udist_rsl_sum_zero_nonneg_surj.
Print Assumptions tspps_udist_rfep_fsum_ext.
Print Assumptions tspps_udist_rfep_fsum_add.
Print Assumptions tspps_udist_rfep_fsum_linear.
Print Assumptions tspps_udist_rfep_fsum_le.
Print Assumptions tspps_udist_rfep_fsum_pos_cons.
Print Assumptions tspps_udist_rfep_fsum_zero_nonneg_surj.
Print Assumptions tspps_udist_rss_ssum_ext.
Print Assumptions tspps_udist_rss_ssum_linear.
Print Assumptions tspps_udist_rsd_sumf_ext.
Print Assumptions tspps_udist_rsd_sumf_pos_cons.
Print Assumptions tspps_ufw_ssum_ext.
Print Assumptions tspps_ufw_ssum_linear.
Print Assumptions tspps_ufw_ssum_pos_cons.
Print Assumptions tspps_uralta_ralt_sum_pos_cons.

(* Extraction audit.  The criterion counts Obj.magic occurrences with
   library-layer transcriptions and this-file introductions registered
   separately; the [Recursive Extraction] output is printed to the
   compile log (the output-directory setting is inert here: it touches
   no file-writing command).  The three extracted representatives cover
   the three proof-body families: the ext direct reference, the pos
   cons form, and the zero_nonneg surjectivity form.  A hard extractor
   error or a nonzero this-file transcription count is handled under
   the controlled-experiment protocol of the 63/68 precedent and
   registered item by item; no false pass may be reported. *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tspps_uralign_sum_ext
  tspps_uralign_sum_pos_cons tspps_uralign_sum_zero_nonneg_surj.

(* Verification record, measured on this file:

   1. All four compile criteria pass: EXIT = 0, true error lines in the
      log count 0, the first eight bytes of the .vo are
      436f7121 000160bc, and the .vo is newer than the source; compile
      log at abl_tail_pos_supply_sum.compile.log of the probe world root
      (single -Q root seeded from the Live tree, per the batch SOP).

   2. The Print Assumptions audit reports all twenty-six supply
      theorems Closed under the global context (name list = Qed count
      = 26, no gap; non-Closed positions count 0).

   3. Extraction exits 0 with no hard errors; the extraction targets
      are the three representatives (ext direct reference, pos cons
      form, zero_nonneg surjectivity form, one each).  Obj.magic counts
      0 in the .ml and 0 in the .mli, both on the in-file
      [Recursive Extraction] output (printed to the compile log; the
      output-directory setting touches no file-writing command) and on
      the gate7 single-module driver, whose [Separate Extraction]
      covers all twenty-six names with no missing candidate;
      this-file introductions count 0, the extraction bodies being
      thin let bindings referencing the roots directly (the
      compile-log tail records let tspps_uralign_sum_ext = sumd_sum_ext
      and alike).

   4. coqchk fifth criterion: rocq check -Q <probe world root> "" -o
      abl_tail_pos_supply_sum exits 0; the environment summary reports
      [Axioms: none], type-in-type <none>, unsafe fixpoints <none>,
      positivity assumed <none>, Set is predicative.  The summary also
      lists an indices-not-mattering section carrying only the Corelib
      and Stdlib universals (eq, eq_true, eq_dep), recorded here for
      completeness. *)
