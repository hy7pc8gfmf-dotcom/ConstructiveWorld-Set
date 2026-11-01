(* Ablation pack, Real-carrier line: the UpRealLeB2 positive-sum           *)
(* assumption slot (source section lines 482-483).                         *)
(* Mission. Discharge real_evicted_partition_pos (UpRealLeB2.v lines       *)
(*   482-483: real_lt real_zero (real_evicted_partition S keep keep_dec    *)
(*   real_energy D D_pos real_sum_over_S)) at the concrete finite-sum      *)
(*   instance real_sum_over_S := the enumerated list sum over enum: the    *)
(*   premise thins to pure data slots (an enum list plus a kept-element    *)
(*   certificate) and the assumption slot is eliminated. Honesty notes,    *)
(*   both carried: (1) the ablated section declares S : Type while the     *)
(*   stock sumd_list_sum machinery is pinned at S : Set, so the isomorphic *)
(*   machinery is rebuilt here at S : Type (zero downgrading; the chain    *)
(*   re-enacts sumd_list_sum_pos_cons limb by limb); (2) the ablated       *)
(*   function takes real_zero off the kept elements, so the pos face adds  *)
(*   a kept-element certificate slot (kept strictly positive, dropped      *)
(*   nonnegative; recast r3 to the sumd_in_fam family shape, name stable). *)
(* Dependencies. Stdlib List; the declared Require face S01_BaseRing       *)
(*   through S15_TailFEPUp plus UpReqSumD, all in-tree, read-only use      *)
(*   (S07 real_exp_neg_pos; S10 real_evicted_partition and                 *)
(*   real_kv_boltzmann_factor via the Export chain; UpReqSumD sumd_lt_le). *)
(* References. The read-only source section UpRealLeB2 (lines 464-616,     *)
(*   statement face verbatim from 482-483); kin sumd_list_sum_pos@UpReqSumD. *)
(* Constructivity. Set-layer statement face; zero assumption slots; the    *)
(*   theorem closes by an explicit structural-induction term ending in     *)
(*   Qed; the tail Print Assumptions reports Closed under the global       *)
(*   context; no classical reasoning anywhere. Bridges (r0 probe, measured *)
(*   tree signature): R and the statement-face predicates rail onto the    *)
(*   tree's global-Real exits and unparameterized interface, UpReqSumD     *)
(*   in-tree form.                                                         *)
(* Build. rocq c -native-compiler no -q -Q . "" (every compile wrapped     *)
(*   by the thermal-guard protocol of the CI).                             *)

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
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============ Positive-sum machinery (S : Type layer, sumd-isomorphic self-carried) ============ *)
(* Isomorphic to the sumd_list_sum/sumd_in pair of the UpReqSumD SumDischarge    *)
(* section, lifted to S : Type (the ablated section's S : Type verbatim);        *)
(* interface fields assembled plainly; zero assumption slots added.              *)
Section UabT12RListPos.

(* Bridge (r0 pristine probe, measured tree signature): the tree's         *)
(* RealInterfaceEnhancedSetoid is the unparameterized global-Real class    *)
(* (S07 RealInterfaceEnhancedMod, canonical instance registered), so the   *)
(* R-carried face rails onto it exactly as UpReqSumD SumDischarge does:    *)
(* R := Real (definitional, eta-neutral), interface fields resolve through *)
(* the global instance; the statement-face predicates rail onto the tree's *)
(* global exit faces (the certified statement-face convention of UpReqSumD:*)
(* real_le/real_lt named, zero/plus bare data).                            *)
Notation R := Real.
Notation le := real_le.
Notation lt := real_lt.
Variable S : Type.
Variable keep : S -> Set.

(* List-sum machine (sumd_list_sum isomorph, Type layer) *)
Fixpoint uabT12_rsum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => zero
  | y :: t => plus (f y) (uabT12_rsum f t)
  end.

(* Kept-element certificate (recast r3, extraction gate round 1: the source  *)
(* [keep]-sum fixpoint erases to __ under extraction and casts at every      *)
(* consumer; recast to the sumd_in_fam certified shape -- an inductive       *)
(* derivation family, empty at nil, head-witness/tail at cons -- with the    *)
(* named synonym keeping the statement names stable, contract unchanged:     *)
(* the certificate is the kept element itself. The family sits at Type (the  *)
(* section's S : Type verbatim: the constructor data lives at Type), not a   *)
(* downgrading of the Set-sort slot shape. *)
Inductive uabT12_kept_fam : list S -> Type :=
| uabT12_kept_head : forall (x : S) (t : list S), keep x -> uabT12_kept_fam (x :: t)
| uabT12_kept_tail : forall (x : S) (t : list S), uabT12_kept_fam t -> uabT12_kept_fam (x :: t).

Definition uabT12_find_kept (l : list S) : Type := uabT12_kept_fam l.

(* Nonnegative limb (sumd_list_sum_nonneg isomorph) *)
Lemma uabT12_rsum_nonneg : forall (f : S -> R) (l : list S),
  (forall s : S, le zero (f s)) -> le zero (uabT12_rsum f l).
Proof.
  intros f l Hnn. induction l as [| y t IH].
  - exact (le_refl zero).
  - exact (le_id_l zero (plus zero zero) (plus (f y) (uabT12_rsum f t))
             (req_sym (plus zero zero) zero (plus_zero zero))
             (le_plus_compat zero (f y) zero (uabT12_rsum f t)
                (Hnn y) IH)).
Qed.

(* Positive limb (kept-element certificate form; induction chain limb by limb  *)
(* after the sumd_list_sum_pos_cons pattern) *)
Lemma uabT12_rsum_pos : forall (f : S -> R) (l : list S),
  (forall s : S, le zero (f s)) ->
  (forall s : S, keep s -> lt zero (f s)) ->
  uabT12_find_kept l ->
  lt zero (uabT12_rsum f l).
Proof.
  intros f l Hnn Hpos Hw. induction Hw as [x t Hx | x t Hwt IH].
  - (* Head kept: the head constructor hands (x :: t) directly; f x > 0 lifts *)
    (* the whole sum (pos_cons isomorph) *)
    exact (lt_le_trans zero (f x) (plus (f x) (uabT12_rsum f t)) (Hpos x Hx)
             (le_id_l (f x) (plus (f x) zero) (plus (f x) (uabT12_rsum f t))
                (req_sym (plus (f x) zero) (f x) (plus_zero (f x)))
                (le_plus_compat (f x) (f x) zero (uabT12_rsum f t)
                   (le_refl (f x))
                   (uabT12_rsum_nonneg f t Hnn)))).
  - (* Tail carries the certificate: the IH gives tail sum > 0, head term       *)
    (* nonnegative lifts the whole sum (comm re-rail then pos_cons isomorph;    *)
    (* interface plus_zero is the right-zero form, the left-zero form re-rails  *)
    (* via plus_comm and req_lt_compat) *)
    exact (req_lt_compat zero zero
             (plus (uabT12_rsum f t) (f x)) (plus (f x) (uabT12_rsum f t))
             (req_refl zero) (plus_comm (uabT12_rsum f t) (f x))
             (lt_le_trans zero (uabT12_rsum f t)
                (plus (uabT12_rsum f t) (f x))
                IH
                (le_id_l (uabT12_rsum f t) (plus (uabT12_rsum f t) zero)
                   (plus (uabT12_rsum f t) (f x))
                   (req_sym (plus (uabT12_rsum f t) zero) (uabT12_rsum f t)
                      (plus_zero (uabT12_rsum f t)))
                   (le_plus_compat (uabT12_rsum f t) (uabT12_rsum f t) zero (f x)
                      (le_refl (uabT12_rsum f t)) (Hnn x))))).
Qed.

End UabT12RListPos.

(* ============ A1 <- UpRealLeB2.v L482-483 (verbatim statement face, instance site restated) ============ *)
(* Original site: Variable real_evicted_partition_pos : real_lt real_zero
   (real_evicted_partition S keep keep_dec real_energy D D_pos real_sum_over_S).
   This file: real_sum_over_S replaced by the concrete instance
   fun g => the enumerated list sum over enum, the assumption slot replaced by data slots
   (enum + kept-element certificate). *)
Theorem uabT12_rl2_evicted_partition_pos :
  forall (S : Type) (keep : S -> Set)
    (keep_dec : forall s : S, Or (keep s) (Not (keep s)))
    (real_energy : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (enum : list S) (Hkept : uabT12_find_kept S keep enum),
    real_lt real_zero
      (real_evicted_partition S keep keep_dec real_energy D D_pos
         (fun g : S -> Real => uabT12_rsum S g enum)).
Proof.
  intros S keep keep_dec real_energy D D_pos enum Hkept.
  assert (Hnn : forall s : S,
    le real_zero
      (if keep_dec s then real_kv_boltzmann_factor S real_energy D D_pos s
                     else real_zero)).
  { intro s. destruct (keep_dec s) as [Hk | Hc].
    - exact (sumd_lt_le (real_kv_boltzmann_factor S real_energy D D_pos s)
               (real_exp_neg_pos
                  (real_mult (real_inv_pos D D_pos) (real_energy s)))).
    - exact (le_refl real_zero). }
  assert (Hpos : forall s : S, keep s ->
    lt real_zero
      (if keep_dec s then real_kv_boltzmann_factor S real_energy D D_pos s
                     else real_zero)).
  { intros s Hk. destruct (keep_dec s) as [Hk' | Hc].
    - exact (real_exp_neg_pos
               (real_mult (real_inv_pos D D_pos) (real_energy s))).
    - destruct (Hc Hk). }
  unfold real_evicted_partition.
  exact (uabT12_rsum_pos S keep
           (fun s : S => if keep_dec s then real_kv_boltzmann_factor S real_energy D D_pos s
                                     else real_zero)
           enum Hnn Hpos Hkept).
Qed.

(* ============ Assumption audit tail (per-piece Closed reading) ============ *)
Print Assumptions uabT12_rl2_evicted_partition_pos.
