(* ========================================================================= *)
(*  NatLenPos.v - positivity of the natural-to-Real embedding behind the     *)
(*  GRPO group size (ablation-50 CYC9 piece, group E-STAGING-CYC9).          *)
(*  Mission. Close the positivity slot real_lt real_zero (real_of_nat        *)
(*  (length enum2)) of G01_CoreMicro.v:284 (Section RealVarNonNeg): the      *)
(*  non-zero identity carried by the natural-to-Real conversion inside the   *)
(*  group mean mean2 = inv(|G|) . sum r; slot family S08:1741, S15:1734,     *)
(*  GibbsAttractor:63 n_pos, S11 vocab_len_pos. Stations: nlp_ofnat_nonneg   *)
(*  (embedding non-negative, induction on k); nlp_ofnat_S_pos (S k strictly  *)
(*  positive: 0 < 1 <= 1 + of_nat k); nlp_len_pos_cover (induction on the    *)
(*  InT derivation itself: both constructors cons-shaped, the Nil branch     *)
(*  never enters the proof term, dodging the empty-match extraction magic);  *)
(*  nlp_len_nonzero (positivity implies Not (real_eq 0 |G|), Set-level Not,  *)
(*  real_lt_eq_lt + real_eq_sym vs real_lt_irrefl); Definition               *)
(*  nlp_g01_mean2 (group mean closed under the cover witness, G01:287-289).  *)
(*  Dependencies. Require face S01_BaseRing .. S15_TailFEPUp in full, plus   *)
(*  Stdlib Lists.List; consumed short names: S01 InT/Not/NatLe; S02 Real,    *)
(*  real_lt/le/eq, real_lt_le_trans, real_lt_eq_lt, real_lt_irrefl; S03      *)
(*  real_inv_pos; S07 real_le_id_l, real_le_plus_compat, real_lt_zero_one;   *)
(*  S08 real_of_nat, real_list_sum_g; S13 real_le_from_lt_aux,               *)
(*  real_le_plus_nonneg_r_aux.                                               *)
(*  References. CYB7 fa57_grpo_G_pos (InT-derivation induction paradigm);    *)
(*  UpKVDrift kv_ofnat family (nonneg support restated locally).             *)
(*  Constructivity. Statement face carried entirely by Set: real_lt,         *)
(*  real_le, real_eq are Set-valued (S02), InT and Not are S01 Set-level;    *)
(*  all proofs end in Qed as genuine constructions, no classical logic;      *)
(*  the tail runs Print Assumptions per statement, Closed the criterion.     *)
(*  Build. rocq c -native-compiler no -q -Q . "" NatLenPos.v, seat world     *)
(*  as flat single-level root, empty logical prefix; COQLIB/ROCQLIB unset.   *)
(* ========================================================================= *)

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
From Stdlib Require Import Lists.List.
Import ListNotations.

Section NatLenPos.

(* ---- Support 1: the natural-to-Real embedding is non-negative (dual of
        UpKVDrift.kv_ofnat_nonneg; restated locally to avoid cross-piece
        section dependencies) ---- *)
Lemma nlp_ofnat_nonneg : forall k : nat,
  real_le real_zero (real_of_nat k).
Proof.
  intro k. induction k as [| k IH].
  - apply real_le_refl.
  - cbn [real_of_nat].
    apply (RealSetoid.real_le_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus real_one (real_of_nat k))).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_le_plus_compat.
      * apply real_le_from_lt_aux. apply real_lt_zero_one.
      * exact IH.
Qed.

(* ---- Support 2: the S k case is strictly positive (0 < 1 <= 1 + of_nat k) ---- *)
Lemma nlp_ofnat_S_pos : forall k : nat,
  real_lt real_zero (real_of_nat (Datatypes.S k)).
Proof.
  intro k. cbn [real_of_nat].
  exact (real_lt_le_trans real_zero real_one
           (real_plus real_one (real_of_nat k)) real_lt_zero_one
           (real_le_plus_nonneg_r_aux real_one (real_of_nat k)
              (nlp_ofnat_nonneg k))).
Qed.

(* ---- Main piece: the enumeration-length positivity slot (closed
        cover-witness form of the G01:284 Hpos slot) ----
   Induction on the InT derivation itself: both constructors are cons-shaped
   and the Nil branch never enters the proof term (fa57_grpo_G_pos method;
   avoids the empty-match extraction magic wrapper). *)
Theorem nlp_len_pos_cover :
  forall (G : Set) (enum : list G),
    (forall i : G, InT i enum) ->
    forall g0 : G,
      real_lt real_zero (real_of_nat (Datatypes.length enum)).
Proof.
  intros G enum cover g0.
  induction (cover g0) as [l0 | y l0 Hin IH].
  - exact (nlp_ofnat_S_pos (Datatypes.length l0)).
  - exact (nlp_ofnat_S_pos (Datatypes.length l0)).
Qed.

(* ---- Non-zero identity piece: positivity implies |G| is not zero
        (Set-level Not) ---- *)
Theorem nlp_len_nonzero :
  forall (G : Set) (enum : list G),
    real_lt real_zero (real_of_nat (Datatypes.length enum)) ->
    Not (real_eq real_zero (real_of_nat (Datatypes.length enum))).
Proof.
  intros G enum Hpos H0.
  exact (real_lt_irrefl real_zero
           (real_lt_eq_lt real_zero
                          (real_of_nat (Datatypes.length enum))
                          real_zero Hpos
                          (real_eq_sym real_zero
                             (real_of_nat (Datatypes.length enum)) H0))).
Qed.

(* ---- G01:284 interface form with all arguments determined: the closed
        assembly of the group mean (isomorphic to G01:287-289:
        inv(|G|) . sum r, Hpos supplied by the cover witness, zero residual
        premises - the slot consumption shown fully closed) ---- *)
Definition nlp_g01_mean2 (Grp2 : Set) (enum2 : list Grp2)
  (reward2 : Grp2 -> Real) (cover : forall i : Grp2, InT i enum2)
  (g0 : Grp2) : Real :=
  real_mult (real_inv_pos (real_of_nat (Datatypes.length enum2))
               (nlp_len_pos_cover Grp2 enum2 cover g0))
            (real_list_sum_g Grp2 reward2 enum2).

End NatLenPos.

(* ---- In-file self-check tail (Print Assumptions run per station) ---- *)
Print Assumptions nlp_ofnat_nonneg.
Print Assumptions nlp_ofnat_S_pos.
Print Assumptions nlp_len_pos_cover.
Print Assumptions nlp_len_nonzero.
Print Assumptions nlp_g01_mean2.
