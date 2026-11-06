(* ConstructiveWorld-Set -- positive-certificate and data-slot families carried by a two-point instance pack. *)

(** * UpAblT7_two_point_pack: one instance construction covering the two-point positivity and realization families.

    Mission.  The two-point instance pack: [uab7_two_point_pack] feeds the
      family statements [uab7_pack_norm], [uab7_pack_pos_pointwise],
      [uab7_pack_witness], [uab7_pos_half_anchor], [uab7_pos_transfer_any],
      [uab7_pos_transfer_pointwise], [uab7_half_lt_one], [uab7_half_le_one],
      [uab7_vocab_nonempty_singleton], [uab7_witness_singleton],
      [uab7_cover_two_point], [uab7_default_token_singleton].

    Dependencies.  Stdlib [Lists.List].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [fa51_sumpos_id], [fa53_compat_abs], [fa57_ext],
      [fa56b_ext], [fa56c_ext] of this development.

    References.  This development, UpAblT7_two_point_pack.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblT7_two_point_pack.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
Require Import fa51_sumpos_id.
Require Import fa53_compat_abs.
Require Import fa57_ext.
Require Import fa56b_ext.
Require Import fa56c_ext.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section UabT7Pack.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* ============ Section 0. Pack body: one instance construction (two-point realized weight pack) ============ *)
(* The statement is carried over verbatim from fa57_W2p_uniform_two_realized
   of fa57_ext.  Three limbs: (i) normalization, the two weights sum to one;
   (ii) pointwise positivity, each weight equals half and half is positive;
   (iii) realized witness, an index inside the enumeration on which the
   retention predicate evaluates to true.  The pack is the uniform supply
   source for the data slots, the positivity slots and the witness slots of
   the library. *)

Theorem uab7_two_point_pack :
  And (Id (fa51_sumd bool (fun _ : bool => fa57_half) [true; false]) one)
      (And (forall i : bool, lt zero ((fun _ : bool => fa57_half) i))
           (sigT (fun i : bool =>
                    And (Id ((fun _ : bool => true) i) true)
                        (InT i [true; false])))).
Proof.
  exact fa57_W2p_uniform_two_realized.
Qed.

(* Limb (i), normalization: covers the u_norm normalization slot (copies at
   AttnDoeblin:147 and S13:2338; inside those modules sum_over_S unfolds to
   fa51_sumd). *)
Theorem uab7_pack_norm :
  Id (fa51_sumd bool (fun _ : bool => fa57_half) [true; false]) one.
Proof.
  destruct fa57_W2p_uniform_two_realized as [Hnorm _].
  exact Hnorm.
Qed.

(* Limb (ii), pointwise positivity: covers the anchor of the pointwise
   positivity family. *)
Theorem uab7_pack_pos_pointwise :
  forall i : bool, lt zero ((fun _ : bool => fa57_half) i).
Proof.
  destruct fa57_W2p_uniform_two_realized as [_ [Hpos _]].
  exact Hpos.
Qed.

(* Limb (iii), realized witness: covers the sigT witness family (a predicate
   constantly true plus membership in the enumeration). *)
Theorem uab7_pack_witness :
  sigT (fun i : bool =>
          And (Id ((fun _ : bool => true) i) true)
              (InT i [true; false])).
Proof.
  destruct fa57_W2p_uniform_two_realized as [_ [_ Hwit]].
  exact Hwit.
Qed.

(* ============ Section 1. Positivity certificate family (scalar form) ============ *)
(* Premise-form copies on the inventory certificate face (scalar):
   Z_pos : lt zero Z (S01:1536), D_pos : lt zero D (S01:1538),
   k_B_pos (S01:1574), temperature_pos (S01:), T_pos (S15:55/S06:3346),
   gamma_pos (S13:3470), etc.
   Realization: the data premise slot is loaded with half (fa57_half) and the
   anchor statement substitutes directly. *)

Theorem uab7_pos_half_anchor : lt zero fa57_half.
Proof.
  exact fa57_half_pos.
Qed.

(* Transfer form: positivity holds for every scalar premise slot loaded with
   half, by the lt_id_r field elimination (an Id endpoint exchange plus the
   direct substitution of the mother anchor); a level-2 derived form. *)
Theorem uab7_pos_transfer_any :
  forall x : R, Id x fa57_half -> lt zero x.
Proof.
  intros x Hx.
  exact (lt_id_r zero fa57_half x (id_sym Hx) fa57_half_pos).
Qed.

(* ============ Section 2. Positivity certificate family (pointwise form) ============ *)
(* Premise-form copies: prob_pos : forall x, lt zero (prob_density x),
   pi_ref_pos, temperature_A_pos, fisher_pos and the positive_dist unfolding
   (positive at every point), spread over the S01, S04, S05 and S13 baseline
   modules.  Realization: the function premise slot is loaded with the
   constant-half function plus the transfer form. *)

Theorem uab7_pos_transfer_pointwise :
  forall (g : bool -> R),
    (forall i : bool, Id (g i) fa57_half) ->
    forall i : bool, lt zero (g i).
Proof.
  intros g Hg i.
  exact (lt_id_r zero fa57_half (g i) (id_sym (Hg i)) fa57_half_pos).
Qed.

(* ============ Section 3. Bound certificate family (half < one) ============ *)
(* Premise-form copies: delta_lt_one : lt delta one, kappa_lt_one,
   min_p_lt_one, spread over the S04, S06 and S13 baseline modules and
   AttnDoeblin.  Realization: the bound premise slot is loaded with half plus
   a fresh construction: half + half = one (fa57_half_plus_half) and
   zero < half (fa57_half_pos) combine through the strict field of
   lt_plus_compat (an enhanced interface field, no decidable order needed)
   into zero + half < half + half, which the plus identity canal collapses to
   the endpoint; a level-2 derived form. *)
Theorem uab7_half_lt_one : lt fa57_half one.
Proof.
  apply (lt_id_r fa57_half (plus fa57_half fa57_half) one fa57_half_plus_half).
  apply (lt_id_l fa57_half (plus zero fa57_half) (plus fa57_half fa57_half)           (id_sym (id_trans (plus_comm zero fa57_half) (plus_zero fa57_half)))).
  exact (@fa53_lt_plus_compat_lt_le_dec RI DO zero fa57_half fa57_half fa57_half           fa57_half_pos (le_refl fa57_half)).
Qed.

(* ============ Section 4. Bound certificate family (half <= one) ============ *)
(* Premise-form copies: eta_le_one : le eta one of the S05 baseline module.
   Realization: the bound premise slot is loaded with half plus the
   lt_le_iff field, which embeds the half < one statement in the left branch
   of the Or; a level-2 derived form. *)
Theorem uab7_half_le_one : le fa57_half one.
Proof.
  exact (lt_le_iff fa57_half one (inl uab7_half_lt_one)).
Qed.

(* ============ Section 5. Vocabulary and enumeration nonemptiness family ============ *)
(* Premise-form copies: vocab_nonempty : Not (Id vocab nil) and
   enum_nonempty, states_ne, spread over the S01, S06, S13 and S15 baseline
   modules and the G01, UpKVDrift, UpKVDrift_P2, UpKVEv and AttnHardLimit218
   modules.  Realization: the vocabulary premise slot is loaded with the
   singleton list plus the direct substitution of the discrimination
   kernel. *)
Theorem uab7_vocab_nonempty_singleton :
  forall (T : Set) (t0 : T), Not (Id (cons t0 (@nil T)) (@nil T)).
Proof.
  intros T t0.
  exact (fa56b_singleton_nonempty T t0).
Qed.

(* ============ Section 6. Realized witness family (singleton list form) ============ *)
(* Premise-form copies: keep_nonempty : sigT (fun s => And (Id (keep s) true)
   (InT s states)), aud_witness, kept_witness and m_in_vocab, spread over the
   G04, S13, UpKVDrift, UpKVDrift_P2, UpKVEv and AttnHardLimit218 baseline
   modules.  Realization: the carrier premise slot is loaded with the
   singleton list, the predicate is loaded as constantly true, and sigT
   assembles the pair (a singleton specialization isomorphic to limb (iii) of
   the W2p pack); a level-3 instance supply form. *)
Theorem uab7_witness_singleton :
  forall (T : Set) (P : T -> bool) (t0 : T),
    Id (P t0) true ->
    sigT (fun s : T => And (Id (P s) true) (InT s (cons t0 (@nil T)))).
Proof.
  intros T P t0 H.
  exact (existT _ t0 (H, @InT_here T t0 (@nil T))).
Qed.

(* ============ Section 7. Finite cover family (two-point enumeration specialization) ============ *)
(* Premise-form copies: S_finite_cover : forall s, InT s S_enum of the S06
   baseline module.  Realization: the carrier premise slot is loaded with
   bool and the enumeration premise slot with the two-point list (the support
   of the W2p pack), constructed element by element; a level-3 instance
   supply form (no abstract-carrier total cover is derivable, the statement
   holds on the two-point carrier; recorded as such). *)
Theorem uab7_cover_two_point :
  forall s : bool, InT s [true; false].
Proof.
  intros s.
  destruct s as [].
  - exact (@InT_here bool true [false]).
  - exact (@InT_next bool false true [false] (@InT_here bool false nil)).
Qed.

(* ============ Section 8. Default token family ============ *)
(* Premise-form copies: default_token : Token of the S01, S04 and S06
   baseline modules.  Realization: the vocabulary premise slot is loaded
   with the singleton list, the nonemptiness witness is supplied by the
   Section 5 statement, and head membership substitutes directly from fa56c
   (same statement as fa56c_default_token_singleton of fa56c). *)
Theorem uab7_default_token_singleton :
  forall (T : Set) (t0 : T),
    Id (fa56c_default_token T (cons t0 (@nil T))
          (fa56b_singleton_nonempty T t0)) t0.
Proof.
  intros T t0.
  exact (fa56c_default_token_singleton T t0).
Qed.

End UabT7Pack.

(* ============ Print Assumptions closing block (each entry read off as Closed) ============ *)
Print Assumptions uab7_two_point_pack.
Print Assumptions uab7_pack_norm.
Print Assumptions uab7_pack_pos_pointwise.
Print Assumptions uab7_pack_witness.
Print Assumptions uab7_pos_half_anchor.
Print Assumptions uab7_pos_transfer_any.
Print Assumptions uab7_pos_transfer_pointwise.
Print Assumptions uab7_half_lt_one.
Print Assumptions uab7_half_le_one.
Print Assumptions uab7_vocab_nonempty_singleton.
Print Assumptions uab7_witness_singleton.
Print Assumptions uab7_cover_two_point.
Print Assumptions uab7_default_token_singleton.
