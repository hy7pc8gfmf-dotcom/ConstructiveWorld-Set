(* ConstructiveWorld-Set -- certified real-level mixing-time assemblies. *)

(** * UpReqConcB1: the unconditional B1 mixing-time assembly.

    Mission.  The generic sum-swap fold lemmas [cb1_list_sum_zero] and
      [cb1_swap_lists] and the absolute-value bound [cb1_bs_abs]; then the
      one-element world ([unit], [[tt]]) delegates its slots to the [csm_]
      family while [cb1_arch] and [cb1_tv0] fill the remaining slots, giving
      [csm_b1_unconditional_mixing_time] with only mass and budget premises.

    Dependencies.  Stdlib [List], [QArith.QArith], [QArith.Qabs], [Lia].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqAlgebra], [UpReqSumD], [UpReqConcSoftmax],
      [UpReqSampling], [UpReqConcMixSel], [AttnDoeblin] of this development.

    References.  This development, UpReqConcB1.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements extract
      with [Obj.magic] = 0 and no erasure; [coqchk] reports [Axioms: none].
      Disclosed exceptions: [b1_enum_ne] is a [Not]-face (Prop) certificate fed
      directly to [k_titer] with no elimination site; [cb1_arch] keeps only the
      [real_lt] branch of [real_arch].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqConcB1.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
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
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
Require Import AttnDoeblin.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ============================================================ *)
(* Section 1.  The generic [bs_swap] double fold over [sumd_list_sum]. *)
(* ============================================================ *)

Notation R := Real.

Section Cb1Swap.
(* Interface fields resolve through the global instance of the
   unparameterized class [RealInterfaceEnhancedSetoid]; the 9.1-style
   [Context {RIS : RealInterfaceEnhancedSetoid R}] header is illegal in
   9.3 since the class takes no arguments (fields all use the global
   [Real]).  Cure follows the UpReqSumD precedent. *)

(* Zero-sum branch: a pointwise-zero function has zero list sum; this is the
   a = nil case of the swap. *)
Lemma cb1_list_sum_zero : forall (S : Set) (g : S -> R) (l : list S),
  (forall x : S, real_eq (g x) zero) -> real_eq (sumd_list_sum S g l) zero.
Proof.
  intros S g l H. induction l as [| x t IH].
  - exact (req_refl zero).
  - exact (req_trans _ _ _
             (req_plus_compat (g x) zero (sumd_list_sum S g t) zero (H x) IH)
             (plus_zero zero)).
Defined.

(* Main double-fold lemma: the sum over a of the sum over b of f equals the
   transposed iterated sum (the generic [bs_swap] piece). *)
Lemma cb1_swap_lists : forall (S : Set) (f : S -> S -> R) (a b : list S),
  real_eq (sumd_list_sum S (fun x : S => sumd_list_sum S (fun y : S => f x y) b) a)
      (sumd_list_sum S (fun y : S => sumd_list_sum S (fun x : S => f x y) a) b).
Proof.
  intros S f a. induction a as [| x a' IH]; intro b.
  - (* a = nil: the left side is zero; the right side folds pointwise to zero
       and is pulled back. *)
    apply req_sym.
    exact (cb1_list_sum_zero S
             (fun y : S => sumd_list_sum S (fun x : S => f x y) nil) b
             (fun y : S => req_refl zero)).
  - (* a = x :: a': split the inner sum by [sumd_list_sum_add] and stitch the
       tail with the induction premise; the chain runs from the right side
       to the left, hence the outer [req_sym]. *)
    exact (req_sym _ _
             (req_trans _ _ _
             (sumd_list_sum_add S (fun y : S => f x y)
                (fun y : S => sumd_list_sum S (fun x0 : S => f x0 y) a') b)
             (req_plus_compat
                (sumd_list_sum S (fun y : S => f x y) b)
                (sumd_list_sum S (fun y : S => f x y) b)
                (sumd_list_sum S (fun y : S => sumd_list_sum S (fun x0 : S => f x0 y) a') b)
                (sumd_list_sum S (fun x0 : S => sumd_list_sum S (fun y : S => f x0 y) b) a')
                (req_refl _)
                (req_sym _ _ (IH b))))).
Defined.

End Cb1Swap.

(* ============================================================ *)
(* Section 2.  The [bs_abs] bound at the concrete [Real] layer.  The [le]   *)
(*   field is a projection rather than an inductive carrier, so the Or      *)
(*   disjunct elimination must unfold [real_le] (the unfold discipline of   *)
(*   CW219); the generic interface layer has no such elimination site,      *)
(*   which is why UpReqSampling freezes the corresponding premise -- this   *)
(*   module supplies its concrete resolution. *)
(* ============================================================ *)

Lemma cb1_bs_abs : forall a : Real,
  real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a H. unfold real_le in H. destruct H as [Hlt | Heq].
  - exact (real_abs_pos_req a Hlt).
  - exact (real_eq_trans _ _ _
             (real_eq_trans _ _ _
                (real_abs_eq_compat a real_zero (real_eq_sym real_zero a Heq))
                real_abs_zero_req)
             Heq).
Defined.

(* ============================================================ *)
(* Section 3.  The concrete B1 assembly: one-element world [S := unit],     *)
(*   enumeration [[tt]]. *)
(* ============================================================ *)

(* ---- World data and the summation functional ---- *)

Definition b1_sumf (f : unit -> Real) : Real := @csm_sumf unit [tt] f.

Definition b1_inv_two : Real := inv_pos (plus one one) req_two_pos.

Definition b1_enum_ne : Not ([tt] = (@nil unit)).
Proof. intro H. discriminate H. Qed.

(* The abs_sum_le_h slot as a plain one-element bound: [abs (b1_sumf f)] =
   [abs (f tt + 0)] and hence [abs (f tt)], while
   [b1_sumf (fun s : unit => abs (f s))] is [abs (f tt) + 0] and hence
   [abs (f tt)]; [le_refl] concludes after the [req] rewrites on both sides. *)
Lemma cb1_abs_sum_le : forall f : unit -> Real,
  real_le (abs (b1_sumf f)) (b1_sumf (fun s : unit => abs (f s))).
Proof.
  intro f.
  exact (le_id_r _ _ _
           (req_sym _ _ (plus_zero (abs (f tt))))
           (le_id_l _ _ _
              (req_abs_compat (plus (f tt) zero) (f tt) (plus_zero (f tt)))
              (le_refl (abs (f tt))))).
Defined.

(* The sum_eq_list slot: the two folding machines agree definitionally on
   the one-element list, witnessed by [req_refl]; the tuple is a concrete
   constructor, so the fixpoint reduces by iota. *)
Lemma cb1_sum_eq_list : forall g : unit -> Real,
  real_eq (b1_sumf g) (rsq_bs_list_sum unit g [tt]).
Proof. intro g. exact (req_refl (rsq_bs_list_sum unit g [tt])). Defined.

(* Bounds of the noise function: [z] is constantly zero and [Delta] is one. *)
Lemma cb1_z_lb : forall s s' : unit, real_le (opp one) zero.
Proof.
  intros s s'.
  exact (lt_le_iff (opp one) zero (inl (lt_zero_opp one one_pos))).
Defined.

Lemma cb1_z_ub : forall s s' : unit, real_le zero one.
Proof. intros s s'. exact (lt_le_iff zero one (inl one_pos)). Defined.

(* ---- The [real_const] reshaping machines underlying the [Arch] bridge ---- *)

(* Pointwise packing: extensionality of [real_const] under [Qeq]. *)
Lemma cb1_real_const_ext : forall q1 q2 : Q,
  Qeq q1 q2 -> real_eq (real_const q1) (real_const q2).
Proof.
  intros q1 q2 H. apply real_eq_of_zero_diff. intro k.
  apply qeq_imp_qeqT.
  setoid_rewrite <- H.
  unfold Qminus. apply Qplus_opp_r.
Defined.

(* [real_const] is an additive homomorphism (pointwise projection packing). *)
Lemma cb1_real_const_plus : forall q1 q2 : Q,
  real_eq (real_const (Qplus q1 q2)) (real_plus (real_const q1) (real_const q2)).
Proof.
  intros q1 q2. apply real_eq_of_zero_diff. intro k.
  apply qeq_imp_qeqT.
  change ((q1 + q2)%Q - (q1 + q2)%Q == 0).
  apply Qplus_opp_r.
Defined.

(* Two rational-layer identities: the successor on nat, and the splitting of
   1 + z. *)
Lemma cb1_qeq_nat1 : forall n : nat,
  Qeq (Qmake (Z.of_nat (Datatypes.S n)) 1) (Qmake (1 + Z.of_nat n) 1).
Proof.
  intro n.
  assert (Hz : Z.of_nat (Datatypes.S n) = (1 + Z.of_nat n)%Z) by lia.
  unfold Qeq. rewrite Hz. reflexivity.
Qed.

Lemma cb1_qeq_Zplus1 : forall z : Z,
  Qeq (Qmake (1 + z) 1) (Qplus (Qmake 1%Z 1) (Qmake z 1)).
Proof.
  intro z.
  assert (Hzm : (z * 1 = z)%Z) by ring.
  unfold Qeq. simpl. rewrite Hzm. reflexivity.
Qed.

(* [real_const 1#1] equals [real_one]; when feeding slots this conversion
   coincides with the field [one]. *)
Lemma cb1_one_const : real_eq (real_const (Qmake 1%Z 1)) real_one.
Proof.
  apply real_eq_of_zero_diff. intro k.
  apply qeq_imp_qeqT.
  change ((1 - 1)%Q == 0).
  apply Qplus_opp_r.
Defined.

(* Main bridge: [cmk_scale n one], the interface unit chain, equals [n#1],
   the [real_const] constant chain. *)
Lemma cb1_scale_const : forall n : nat,
  real_eq (real_const (Qmake (Z.of_nat n) 1)) (cmk_scale n one).
Proof.
  intro n. induction n as [| n IH].
  - (* n = 0: [real_const 0#1] equals zero by pointwise zero-difference
       packing. *)
    change (cmk_scale Datatypes.O one) with real_zero.
    apply real_eq_of_zero_diff. intro k.
    apply qeq_imp_qeqT.
    change ((0 - 0)%Q == 0).
    apply Qplus_opp_r.
  - (* n = S m: [real_const ((m+1)#1)] equals [1#1 + real_const (m#1)] and
       hence [one + cmk_scale m one]. *)
    change (cmk_scale (Datatypes.S n) one) with (plus one (cmk_scale n one)).
    exact (req_trans _ _ _
             (cb1_real_const_ext _ _ (cb1_qeq_nat1 n))
             (req_trans _ _ _
                (req_trans _ _ _
                   (cb1_real_const_ext _ _ (cb1_qeq_Zplus1 (Z.of_nat n)))
                   (cb1_real_const_plus (Qmake 1%Z 1) (Qmake (Z.of_nat n) 1)))
                (req_plus_compat (real_const (Qmake 1%Z 1)) one
                   (real_const (Qmake (Z.of_nat n) 1)) (cmk_scale n one)
                   cb1_one_const IH))).
Defined.

(* ---- The [Arch] resolution piece, reshaping [real_arch]: the [2 <= n]
   branch of the conjunction is discarded and never enters a slot ---- *)

Lemma cb1_arch : forall x : Real, real_le zero x ->
  sigT (fun N : nat => real_lt x (cmk_scale (Datatypes.S N) one)).
Proof.
  intros x _. destruct (real_arch x) as [n [Hn2 Hlt]].
  exists n.
  apply (@lt_le_trans RealEnhancedReal x
           (real_const (Qmake (Z.of_nat n) 1))
           (cmk_scale (Datatypes.S n) one) Hlt).
  change (cmk_scale (Datatypes.S n) one) with (plus one (cmk_scale n one)).
  apply (le_trans _ (cmk_scale n one)).
  - exact (le_id_l _ _ _ (cb1_scale_const n) (le_refl (cmk_scale n one))).
  - exact (le_id_r _ _ _ (plus_comm (cmk_scale n one) one)
             (cmk_le_plus_r (cmk_scale n one) one
                (lt_le_iff zero one (inl one_pos)))).
Defined.

(* ---- The total-variation resolution piece, one-element case: the mass
   premises force the difference to be zero, so the bound holds without a
   disjunction ---- *)

Definition b1_tv (mu nu : unit -> Real) : Real :=
  mult b1_inv_two (b1_sumf (fun s : unit => abs (req_minus (mu s) (nu s)))).

Lemma cb1_tv0 : forall mu nu : unit -> Real,
  real_eq (b1_sumf mu) one -> real_eq (b1_sumf nu) one -> real_le zero (b1_tv mu nu).
Proof.
  intros mu nu Hmu Hnu.
  assert (Hmu0 : real_eq (mu tt) one).
  { exact (req_trans _ _ _ (req_sym _ _ (plus_zero (mu tt))) Hmu). }
  assert (Hnu0 : real_eq (nu tt) one).
  { exact (req_trans _ _ _ (req_sym _ _ (plus_zero (nu tt))) Hnu). }
  assert (Hw0 : real_eq (req_minus (mu tt) (nu tt)) zero).
  { exact (req_trans _ _ _
             (req_plus_compat (mu tt) one (opp (nu tt)) (opp one)
                Hmu0 (req_opp_compat (nu tt) one Hnu0))
             (plus_opp one)). }
  assert (Habs : real_le zero (abs (req_minus (mu tt) (nu tt)))).
  { exact (le_id_r _ _ _
             (req_sym _ _ (req_abs_compat (req_minus (mu tt) (nu tt)) zero Hw0))
             (le_id_r zero zero (abs zero)
                (req_sym _ _ abs_zero) (le_refl zero))). }
  assert (Hprod : real_le zero (mult (abs (req_minus (mu tt) (nu tt))) b1_inv_two)).
  { exact (le_id_l _ _ _
             (req_sym _ _
                (req_trans _ _ _ (mult_comm zero b1_inv_two)
                   (mult_zero b1_inv_two)))
             (le_mult_compat_weak zero (abs (req_minus (mu tt) (nu tt))) b1_inv_two
                (lt_le_iff zero b1_inv_two
                   (inl (inv_pos_pos (plus one one) req_two_pos)))
                Habs)). }
  assert (Hsw : real_le zero (mult b1_inv_two (abs (req_minus (mu tt) (nu tt))))).
  { exact (le_id_r _ _ _ (mult_comm (abs (req_minus (mu tt) (nu tt))) b1_inv_two)
             Hprod). }
  unfold b1_tv.
  exact (le_id_r _ _ _
           (req_mult_compat b1_inv_two b1_inv_two
              (abs (req_minus (mu tt) (nu tt)))
              (plus (abs (req_minus (mu tt) (nu tt))) zero)
              (req_refl b1_inv_two)
              (req_sym _ _ (plus_zero (abs (req_minus (mu tt) (nu tt))))))
           Hsw).
Defined.

(* ---- The iterator wrapper: [k_titer] in its exported form, fed the whole
   B1 data ---- *)

Definition b1_titer (n : nat) (mu : unit -> Real) : unit -> Real :=
  k_titer unit b1_sumf [tt] b1_enum_ne one one_pos one
          (fun _ _ : unit => zero) cb1_z_lb cb1_sum_eq_list n mu.

(* ---- The closing certificate: every argument of [cmk_attention_mixing_time]
   supplied explicitly ---- *)

Definition cb1_mixing_cert :=
  cmk_attention_mixing_time
    real_lt_plus_compat_lt_le          (* the lt_plus_compat_lt_le slot,
                                          filled by the Real-layer lemma directly *)
    unit b1_sumf
    (csm_sum_ext unit [tt])
    (csm_sum_linear unit [tt])
    (csm_sum_add unit [tt])
    (csm_sum_le unit [tt])
    cb1_abs_sum_le                     (* the abs_sum_le_h slot as a plain
                                          one-element bound *)
    [tt] b1_enum_ne
    one one_pos                        (* temp := one *)
    one one_pos                        (* Delta := one *)
    (fun _ _ : unit => zero) cb1_z_lb cb1_z_ub
    (fun f : unit -> unit -> Real => cb1_swap_lists unit f [tt] [tt])  (* bs_swap *)
    cb1_bs_abs                         (* bs_abs *)
    real_lt_plus_compat_lt_le          (* the bs_lpc slot: the same lemma in
                                          the same shape *)
    cb1_sum_eq_list.

(* ============ The terminal theorem: B1 closes unconditionally, with no
   interface, Arch, or initial-variation premises ============ *)

Theorem csm_b1_unconditional_mixing_time :
  forall mu nu : unit -> Real,
  real_eq (b1_sumf mu) one -> real_eq (b1_sumf nu) one ->
  forall budget : Real, real_lt zero budget ->
  sigT (fun k : nat =>
    real_lt (b1_tv (b1_titer k mu) (b1_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget.
  exact (cb1_mixing_cert mu nu Hmu Hnu budget Hbudget
           cb1_arch (cb1_tv0 mu nu Hmu Hnu)).
Defined.

(* The weak variant: the same certificate chain fed to
   [cmk_attention_mixing_time_le], weakening the strict conclusion to its
   weak form. *)
Theorem csm_b1_unconditional_mixing_time_le :
  forall mu nu : unit -> Real,
  real_eq (b1_sumf mu) one -> real_eq (b1_sumf nu) one ->
  forall budget : Real, real_lt zero budget ->
  sigT (fun k : nat =>
    real_le (b1_tv (b1_titer k mu) (b1_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget.
  apply (cmk_attention_mixing_time_le
           real_lt_plus_compat_lt_le unit b1_sumf
           (csm_sum_ext unit [tt]) (csm_sum_linear unit [tt])
           (csm_sum_add unit [tt]) (csm_sum_le unit [tt])
           cb1_abs_sum_le [tt] b1_enum_ne
           one one_pos one one_pos
           (fun _ _ : unit => zero) cb1_z_lb cb1_z_ub
           (fun f : unit -> unit -> Real => cb1_swap_lists unit f [tt] [tt])
           cb1_bs_abs real_lt_plus_compat_lt_le
           cb1_sum_eq_list mu nu Hmu Hnu budget Hbudget
           cb1_arch (cb1_tv0 mu nu Hmu Hnu)).
Defined.

(* ============ Machine evidence: the terminal statements and the main exits
   close under the global context ============ *)
Print Assumptions csm_b1_unconditional_mixing_time.
Print Assumptions csm_b1_unconditional_mixing_time_le.
Print Assumptions cb1_arch.
Print Assumptions cb1_scale_const.
Print Assumptions cb1_swap_lists.
Print Assumptions cb1_bs_abs.
Print Assumptions cb1_tv0.
Print Assumptions cb1_abs_sum_le.
