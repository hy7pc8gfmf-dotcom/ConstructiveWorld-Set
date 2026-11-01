(* ==========================================================================
   UpReqBranchPos.v -- branch-wise positivity engine piece.
   Mission. A condition-agnostic branch-sum positivity engine over the
   constructive enumeration membership InT: brp_sum_pos with the witness
   head/tail dispatcher brp_mem_split, the bool face brp_branch_pos_bool,
   the Or face brp_branch_pos_or, and four source-slot discharges B1..B4
   (UpReqAlign audited-Z, G13_EvictFam evicted partition, UpReqAttnGibbs
   Gibbs-face copy, UpReqAlignRestB two-form KV eviction partition).
   Dependencies. The pieces on the in-piece Require declaration faces
   (all read-only, zero original-tree edits): the S01_BaseRing ..
   S15_TailFEPUp chain, UpReqAlgebra, UpReqSumD; Stdlib List.
   References. Branch-wise positivity by witness-carrying enumeration
   membership; the non-trivial proof content lives in brp_sum_pos
   (in-piece) over sumd_list_sum_nonneg / sumd_lt_le @UpReqSumD; the
   B1..B4 statements carry the slot faces of the four source positions
   on sumd_sumf S enum (InT face: S01_BaseRing.v:77).
   Alignment. Aligned to the world's unparameterized interface class (the
   UpReqSumD.v L58 / S10_KVQuantTrig.v L12417 precedents): the binder face
   forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} mismatches the
   zero-argument Class of this -Set-lineage world; aligned by dropping the
   binders, Notation R := Real, and the real_lt / real_le / real_eq faces
   (zero shims); brp_mem_split eliminates InT by explicit dependent match.
   The conditional keep-marks are Id-carrier (Id (c a) true, the QeqT
   form) or the bare kp a witness carrier, and the strict premises are
   unconditional real_lt, so every extracted branch value shares one
   carrier and extraction carries zero Obj.magic.
   Constructivity. All items close with Qed; zero admission literals; no
   classical logic; the statement face is Set-layered (order predicates
   and equalities Set-valued, zero Prop leakage); ends with Print
   Assumptions.
   Build. Rocq 9.1 direct invocation, rocq c -Q . "" -native-compiler no,
   cpu_guard wrapped load caps.
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
Require Import UpReqAlgebra.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.
Notation R := Real.

(* ============================================================ *)
(* Section BrpEngine: condition-agnostic generic branch-sum       *)
(* positivity engine.                                            *)
(* ============================================================ *)
Section BrpEngine.
Context {A : Set}.

(* Self-contained head/tail dispatcher on the membership witness        *)
(* (explicit match-return term, index refinement, no case replay):      *)
(* the witness head position yields the head positivity, the tail       *)
(* position yields the tail membership, at Or in the Set layer.         *)
Definition brp_mem_split (b : A -> R) (a : A) (x : A) (t : list A)
           (hpos : real_lt zero (b a)) (pin : InT a (x :: t)) :
  Or (real_lt zero (b x)) (InT a t) :=
  match pin as i0 in InT _ L
        return (match L with
                | nil => Empty_set
                | x' :: t' => Or (real_lt zero (b x')) (InT a t')
                end)
  with
  | InT_here _ l0 => inl hpos
  | InT_next _ y0 l0 i1 => inr i1
  end.

(* Main engine (condition-agnostic): the integrand is pointwise          *)
(* nonnegative and a sigT witness locates a strictly positive term       *)
(* inside the enumeration; then the list sum is strictly positive.       *)
Lemma brp_sum_pos : forall (b : A -> R) (l : list A),
  (forall a : A, real_le zero (b a)) ->
  sigT (fun a : A => sigT (fun _ : InT a l => real_lt zero (b a))) ->
  real_lt zero (sumd_list_sum A b l).
Proof.
  intros b l Hnn. induction l as [| x t IH]; intro Hw.
  - (* nil case: the nonempty premise is contradictory (InT has no nil    *)
    (* constructor; inversion filters the index contradiction).           *)
    destruct Hw as [a w]. destruct w as [pin hpos]. inversion pin.
  - destruct Hw as [a w]. destruct w as [pin hpos].
    destruct (brp_mem_split b a x t hpos pin) as [hhead | pint].
    + (* witness at the head position: head term positive + tail sum       *)
      (* nonnegative.                                                     *)
      exact (lt_le_trans zero (b x)
               (plus (b x) (sumd_list_sum A b t))
               hhead
               (le_id_l (b x) (plus (b x) zero)
                  (plus (b x) (sumd_list_sum A b t))
                  (req_sym (plus (b x) zero) (b x) (plus_zero (b x)))
                  (le_plus_compat (b x) (b x) zero
                     (sumd_list_sum A b t)
                     (le_refl (b x))
                     (sumd_list_sum_nonneg A b t Hnn)))).
    + (* witness at the tail position: head term nonnegative + tail sum    *)
      (* positive implies the sum positive (zero-conditional branch).     *)
      exact (lt_le_trans zero (sumd_list_sum A b t)
               (plus (b x) (sumd_list_sum A b t))
               (IH (existT
                      (fun a0 : A =>
                         sigT (fun _ : InT a0 t => real_lt zero (b a0)))
                      a (existT (fun _ : InT a t => real_lt zero (b a))
                           pint hpos)))
               (le_id_l (sumd_list_sum A b t)
                  (plus zero (sumd_list_sum A b t))
                  (plus (b x) (sumd_list_sum A b t))
                  (req_sym (plus zero (sumd_list_sum A b t))
                     (sumd_list_sum A b t)
                     (req_plus_zero_l (sumd_list_sum A b t)))
                  (le_plus_compat zero (b x) (sumd_list_sum A b t)
                     (sumd_list_sum A b t)
                     (Hnn x)
                     (le_refl (sumd_list_sum A b t))))).
Qed.

End BrpEngine.

(* ============================================================ *)
(* Section BrpEngineBool: the engine over the bool conditional    *)
(* face (B1 hookup).                                             *)
(*   Slot-form double premise taken directly: the keep-mark       *)
(*   witness (sigT + InT + Id mark) and pointwise positivity of   *)
(*   the kept terms (unconditional real_lt premise). The keep-    *)
(*   mark is the Id-carrier Id (c a) true (the QeqT form: the     *)
(*   Set-layer equality carrier, inhabited exactly when the       *)
(*   bool flag holds), so no branch-typed premise survives        *)
(*   extraction; the conditional dispatch is a plain body-level   *)
(*   match whose branch values share one carrier.                *)
(* ============================================================ *)
Section BrpEngineBool.
Context {A : Set}.

Variable c : A -> bool.
Variable f : A -> R.

(* Zero-branch nonneg dispatcher: the branch integrand is pointwise     *)
(* nonnegative (true branch lifts strict positivity, false branch is    *)
(* reflexive).                                                          *)
Definition brp_bool_nonneg_of (a : A)
           (Hs : real_lt zero (f a)) :
  real_le zero (if c a then f a else zero) :=
  match c a as cx
        return real_le zero (if cx then f a else zero)
  with
  | true => sumd_lt_le (f a) Hs
  | false => le_refl zero
  end.

(* Strict-positivity dispatcher: a strict positivity premise plus the   *)
(* Id-carrier keep mark (QeqT form, inhabited iff c a = true) implies   *)
(* the branch term strictly positive. The false branch discharges the   *)
(* uninhabited mark through an empty match (extraction renders it as    *)
(* the canonical absurd case, not a cast).                              *)
Definition brp_bool_pos_of (a : A)
           (Hs : real_lt zero (f a))
           (mk : Id (c a) true) :
  real_lt zero (if c a then f a else zero) :=
  match c a as cx
        return Id cx true -> real_lt zero (if cx then f a else zero)
  with
  | true => fun _ => Hs
  | false => fun mk0 =>
      False_rect (real_lt zero zero)
        (match mk0 in Id _ x
                return (match x with true => False | false => True end)
         with
         | id_refl => I
         end)
  end mk.

Lemma brp_branch_pos_bool : forall (l : list A),
  sigT (fun a : A => prod (InT a l) (Id (c a) true)) ->
  (forall a : A, real_lt zero (f a)) ->
  real_lt zero (sumd_list_sum A (fun a : A => if c a then f a else zero) l).
Proof.
  intros l Hw Hstrict.
  destruct Hw as [a [pin mark]].
  exact (brp_sum_pos
           (fun a0 : A => if c a0 then f a0 else zero) l
           (fun a0 : A => brp_bool_nonneg_of a0 (Hstrict a0))
           (existT
              (fun a0 : A =>
                 sigT (fun _ : InT a0 l =>
                          real_lt zero (if c a0 then f a0 else zero)))
              a
              (existT
                 (fun _ : InT a l =>
                    real_lt zero (if c a then f a else zero))
                 pin (brp_bool_pos_of a (Hstrict a) mark)))).
Qed.

End BrpEngineBool.

(* ============================================================ *)
(* Section BrpEngineOr: the engine over the Or conditional face   *)
(* (B2-B4 hookup; the keep_dec slot has the pointwise form        *)
(* forall a, Or (kp a) (Not (kp a)), with the Set-layer Or and    *)
(* Not).                                                          *)
(* ============================================================ *)
Section BrpEngineOr.
Context {A : Set}.

Variable kp : A -> Set.
Variable kd : forall a : A, Or (kp a) (Not (kp a)).
Variable f : A -> R.

(* Zero-branch nonneg dispatcher: the branch integrand is pointwise     *)
(* nonnegative (left branch lifts strict positivity, right branch is    *)
(* reflexive).                                                          *)
Definition brp_or_nonneg_of (a : A)
           (Hs : real_lt zero (f a)) :
  real_le zero (if kd a then f a else zero) :=
  match kd a as k0
        return real_le zero (if k0 then f a else zero)
  with
  | inl _ => sumd_lt_le (f a) Hs
  | inr _ => le_refl zero
  end.

(* Strict-positivity dispatcher: a strict positivity premise plus the   *)
(* bare keep-carrier witness (kp a, inhabited exactly when the Or       *)
(* decider picked the left branch) implies the branch term strictly     *)
(* positive. The right branch discharges the contradiction (the Not     *)
(* witness applied to the keep witness) through an empty match.         *)
Definition brp_or_pos_of (a : A)
           (mk : kp a)
           (Hs : real_lt zero (f a)) :
  real_lt zero (if kd a then f a else zero) :=
  match kd a as k0
        return real_lt zero (if k0 then f a else zero)
  with
  | inl _ => Hs
  | inr n0 => match n0 mk with end
  end.

Lemma brp_branch_pos_or : forall (l : list A),
  sigT (fun a : A => prod (InT a l) (kp a)) ->
  (forall a : A, real_lt zero (f a)) ->
  real_lt zero (sumd_list_sum A (fun a : A => if kd a then f a else zero) l).
Proof.
  intros l Hw Hstrict.
  destruct Hw as [a [pin mark]].
  exact (brp_sum_pos
           (fun a0 : A => if kd a0 then f a0 else zero) l
           (fun a0 : A => brp_or_nonneg_of a0 (Hstrict a0))
           (existT
              (fun a0 : A =>
                 sigT (fun _ : InT a0 l =>
                          real_lt zero (if kd a0 then f a0 else zero)))
              a
              (existT
                 (fun _ : InT a l =>
                    real_lt zero (if kd a then f a else zero))
                 pin (brp_or_pos_of a mark (Hstrict a))))).
Qed.

End BrpEngineOr.

(* ============================================================ *)
(* Section BrpDischargeB1: the UpReqAlign audited-Z slot,         *)
(* instance form over the bool conditional face.                  *)
(*   Slot face: Z_aud_req = sumf (fun s => if post_aud s then     *)
(*   p s else zero); the sum face is instantiated to              *)
(*   sumd_sumf S enum; the nonemptiness position is the sigT      *)
(*   witness (Id keep-mark inside the enumeration).               *)
(*   The normalization premise is not needed on the witness route *)
(*   (honest strengthening: the conclusion does not depend on     *)
(*   normalization).                                              *)
(* ============================================================ *)
Section BrpDischargeB1.
Variable S : Set.
Variable enum : list S.
Variable post_aud : S -> bool.
Variable p : S -> R.

(* Slot-form branch sum: the concrete instance face of Z_aud_req        *)
(* (transparent, for downstream direct connection).                     *)
Definition brp_Z_aud_req : R :=
  sumd_sumf S enum (fun s : S => if post_aud s then p s else zero).

Lemma brp_b1_Z_aud_pos :
  (forall s : S, real_lt zero (p s)) ->
  sigT (fun s : S => prod (InT s enum) (Id (post_aud s) true)) ->
  real_lt zero brp_Z_aud_req.
Proof.
  intros Hp Hw.
  unfold brp_Z_aud_req.
  exact (brp_branch_pos_bool post_aud p enum Hw Hp).
Qed.

End BrpDischargeB1.

(* ============================================================ *)
(* Section BrpDischargeB2: the G13_EvictFam evicted_partition_pos *)
(* slot.                                                          *)
(*   Slot face: evicted_partition = sumf (fun s => if keep_dec s  *)
(*   then boltzmann_factor s else zero); the source face is a     *)
(*   Variable position. Pointwise positivity of the kept terms    *)
(*   = exp_neg_pos (the enhanced interface field).                *)
(* ============================================================ *)
Section BrpDischargeB2.
Variable S : Set.
Variable enum : list S.
Variable D : R.
Variable D_pos : real_lt zero D.
Variable energy : S -> R.
Variable keep : S -> Set.
Variable keep_dec : forall s : S, Or (keep s) (Not (keep s)).

(* Slot-form Boltzmann factor (G13_EvictFam face). *)
Definition brp_boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

(* Slot-form branch sum: the concrete instance face of the evicted      *)
(* partition.                                                           *)
Definition brp_evicted_partition : R :=
  sumd_sumf S enum
    (fun s : S => if keep_dec s then brp_boltzmann_factor s else zero).

Lemma brp_b2_evicted_partition_pos :
  sigT (fun s : S => prod (InT s enum) (keep s)) ->
  real_lt zero brp_evicted_partition.
Proof.
  intro Hw.
  unfold brp_evicted_partition.
  exact (brp_branch_pos_or keep keep_dec brp_boltzmann_factor enum Hw
           (fun s : S =>
              exp_neg_pos (mult (inv_pos D D_pos) (energy s)))).
Qed.

End BrpDischargeB2.

(* ============================================================ *)
(* Section BrpDischargeB3: the UpReqAttnGibbs                     *)
(* evicted_partition_r_pos slot.                                  *)
(*   Slot face: evicted_partition_r = sumf (fun s => if keep_dec  *)
(*   s then boltzmann_factor_r s else zero); an isomorphic copy   *)
(*   of B2 under the Gibbs-face _r names.                         *)
(* ============================================================ *)
Section BrpDischargeB3.
Variable S : Set.
Variable enum : list S.
Variable D : R.
Variable D_pos : real_lt zero D.
Variable energy : S -> R.
Variable keep : S -> Set.
Variable keep_dec : forall s : S, Or (keep s) (Not (keep s)).

(* Slot-form Boltzmann factor (UpReqAttnGibbs boltzmann_factor_r face). *)
Definition brp_boltzmann_factor_r (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

(* Slot-form branch sum: the concrete instance face of                  *)
(* evicted_partition_r.                                                 *)
Definition brp_evicted_partition_r : R :=
  sumd_sumf S enum
    (fun s : S => if keep_dec s then brp_boltzmann_factor_r s else zero).

Lemma brp_b3_evicted_partition_r_pos :
  sigT (fun s : S => prod (InT s enum) (keep s)) ->
  real_lt zero brp_evicted_partition_r.
Proof.
  intro Hw.
  unfold brp_evicted_partition_r.
  exact (brp_branch_pos_or keep keep_dec brp_boltzmann_factor_r enum Hw
           (fun s : S =>
              exp_neg_pos (mult (inv_pos D D_pos) (energy s)))).
Qed.

End BrpDischargeB3.

(* ============================================================ *)
(* Section BrpDischargeB4: the UpReqAlignRestB                    *)
(* req_evicted_partition_pos slot.                                *)
(*   Slot face: req_evicted_partition = sum_over_S (fun s =>      *)
(*   match keep_dec s with inl _ => req_kv_boltzmann_factor s |   *)
(*   inr _ => zero end); the sum carrier is a bare Variable       *)
(*   (no enumeration, no fields). Two result forms: piece 1 is    *)
(*   the sumd concrete instance form (the existing mounting);     *)
(*   piece 2 is the bare-carrier reconnection form (canonical     *)
(*   condition + the lt_id_r face re-track, same method as        *)
(*   zposd_Z_pos_of_partition; the RestB side supplies the        *)
(*   canonical slot and mounts directly).                         *)
(* ============================================================ *)
Section BrpDischargeB4.
Variable S : Set.
Variable enum : list S.
Variable D : R.
Variable D_pos : real_lt zero D.
Variable energy : S -> R.
Variable keep : S -> Set.
Variable keep_dec : forall s : S, Or (keep s) (Not (keep s)).

(* Slot-form KV Boltzmann factor (req_kv_boltzmann_factor face). *)
Definition brp_kv_boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

(* Slot-form branch sum: the explicit match form (pointwise             *)
(* isomorphic to the RestB source slot).                                *)
Definition brp_req_evicted_partition_sumd : R :=
  sumd_sumf S enum
    (fun s : S => match keep_dec s with
                  | inl _ => brp_kv_boltzmann_factor s
                  | inr _ => zero
                  end).

(* Piece 1: the sumd concrete instance form discharge. *)
Lemma brp_b4_evicted_partition_pos :
  sigT (fun s : S => prod (InT s enum) (keep s)) ->
  real_lt zero brp_req_evicted_partition_sumd.
Proof.
  intro Hw.
  unfold brp_req_evicted_partition_sumd.
  exact (brp_branch_pos_or keep keep_dec brp_kv_boltzmann_factor enum Hw
           (fun s : S =>
              exp_neg_pos (mult (inv_pos D D_pos) (energy s)))).
Qed.

(* Piece 2: the bare-carrier reconnection form -- for any sum operator  *)
(* sov carrying the canonical condition (real_eq (sov g) (sumd_sumf g), *)
(* the RestB-side mounting face, the partition_condition position), the *)
(* positivity of the source-slot original form (the sov carrier)        *)
(* follows directly.                                                    *)
Lemma brp_b4_of_carrier : forall (sov : (S -> R) -> R),
  (forall g : S -> R, real_eq (sov g) (sumd_sumf S enum g)) ->
  sigT (fun s : S => prod (InT s enum) (keep s)) ->
  real_lt zero (sov (fun s : S => match keep_dec s with
                                  | inl _ => brp_kv_boltzmann_factor s
                                  | inr _ => zero
                                  end)).
Proof.
  intros sov Hspec Hw.
  exact (lt_id_r zero
           (sumd_sumf S enum
              (fun s : S => match keep_dec s with
                            | inl _ => brp_kv_boltzmann_factor s
                            | inr _ => zero
                            end))
           (sov (fun s : S => match keep_dec s with
                              | inl _ => brp_kv_boltzmann_factor s
                              | inr _ => zero
                              end))
           (req_sym
              (sov (fun s : S => match keep_dec s with
                                 | inl _ => brp_kv_boltzmann_factor s
                                 | inr _ => zero
                                 end))
              (sumd_sumf S enum
                 (fun s : S => match keep_dec s with
                               | inl _ => brp_kv_boltzmann_factor s
                               | inr _ => zero
                               end))
              (Hspec (fun s : S => match keep_dec s with
                                   | inl _ => brp_kv_boltzmann_factor s
                                   | inr _ => zero
                                   end)))
           (brp_b4_evicted_partition_pos Hw)).
Qed.

End BrpDischargeB4.

(* ============ G3 evidence: the new pieces carry zero external      *)
(* ============ unproved assumptions (all Closed).                   ============ *)
Print Assumptions brp_sum_pos.
Print Assumptions brp_branch_pos_bool.
Print Assumptions brp_branch_pos_or.
Print Assumptions brp_b1_Z_aud_pos.
Print Assumptions brp_b2_evicted_partition_pos.
Print Assumptions brp_b3_evicted_partition_r_pos.
Print Assumptions brp_b4_evicted_partition_pos.
Print Assumptions brp_b4_of_carrier.
