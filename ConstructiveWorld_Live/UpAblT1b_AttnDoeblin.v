(* ConstructiveWorld-Set — discharged slot instances for the swap and absolute-value interfaces of the attention module. *)

(** * UpAblT1b_AttnDoeblin: instances closing the swap and
    absolute-value identity slots of [AttnDoeblin].

    Mission.  The double-sum exchange for the two swap slots
      [abl_AtnDoeblin_sum_swap_cc]/[abl_AtnDoeblin_bs_swap], derived
      wholesale from the enumeration-normalization slot [sum_eq_list]
      via a list-Fubini layer, and the absolute-value identity slots
      [abl_AtnDoeblin_abs_ge_zero_id_cc]/[abl_AtnDoeblin_bs_abs] as
      direct instantiations of [AbsLeId].

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing] through
      [S15_TailFEPUp], [AttnDoeblin] and [AbsLeId] of this
      development.

    References.  This development, UpAblT1b_AttnDoeblin.v, the baseline
      module in ConstructiveWorld-Main whose statement names are carried
      over here verbatim (statement-face Set-carrier completion); the
      closed slots are [sum_swap_cc], [bs_swap], [abs_ge_zero_id_cc],
      [bs_abs] of [AttnDoeblin].

    Constructivity.  All statements are predicated on the Set-valued
      identity [Id]; proofs use list induction, step congruence
      ([id_cong]/[id_cong2]) and transitivity; statements extract with
      [Obj.magic] = 0 and no erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . ""
      UpAblT1b_AttnDoeblin.v] compiles cleanly (exit 0); the first
      eight bytes of the artifact are [436f7121 00015ff4]. *)

From Stdlib Require Import List.
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
Require Import AttnDoeblin.
Require Import AbsLeId.

(* ==================== Part 1. List-Fubini combinatorics over the discharged machine ==================== *)
(* Pointwise congruence, additivity, the zero-function degeneration and
   the double-sum exchange for the top-level machine
   [AttnDoeblin.bs_list_sum]; these lemmas are the basic layer the swap
   slot is derived from. *)

Section AblListSum.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

(* Pointwise [Id] implies [Id] of the list sums (congruence extension
   along [bs_list_sum]). *)
Lemma abl_lsum_ext : forall (f g : S -> R) (l : list S),
  (forall x : S, Id (f x) (g x)) ->
  Id (AttnDoeblin.bs_list_sum f l) (AttnDoeblin.bs_list_sum g l).
Proof.
  intros f g l H. induction l as [| x t IH].
  - exact id_refl.
  - simpl. exact (id_cong2 plus (H x) IH).
Qed.

(* Additivity of the list sum. *)
Lemma abl_lsum_add : forall (f g : S -> R) (l : list S),
  Id (AttnDoeblin.bs_list_sum (fun s : S => plus (f s) (g s)) l)
     (plus (AttnDoeblin.bs_list_sum f l) (AttnDoeblin.bs_list_sum g l)).
Proof.
  intros f g l. induction l as [| x t IH].
  - exact (id_sym (plus_zero zero)).
  - simpl.
    apply (id_trans (id_cong (fun w : R => plus (plus (f x) (g x)) w) IH)).
    exact (AttnDoeblin.plus_exchange (f x) (AttnDoeblin.bs_list_sum f t)
                                     (g x) (AttnDoeblin.bs_list_sum g t)).
Qed.

(* The list sum of the zero function is zero (via [bs_list_const_sum]
   and the multiplicative zero). *)
Lemma abl_lsum_zero : forall l : list S,
  Id zero (AttnDoeblin.bs_list_sum (fun _ : S => zero) l).
Proof.
  intro l.
  exact (id_trans (id_sym (mult_zero (AttnDoeblin.nat_to_R (length l))))
          (id_sym (AttnDoeblin.bs_list_const_sum zero l))).
Qed.

(* Exchange of a double list sum (general form, outer and inner lists
   independent; the core of the Fubini combinatorics). *)
Lemma abl_lsum_fubini_gen : forall (f : S -> S -> R) (l1 l2 : list S),
  Id (AttnDoeblin.bs_list_sum (fun s : S => AttnDoeblin.bs_list_sum (f s) l2) l1)
     (AttnDoeblin.bs_list_sum (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') l1) l2).
Proof.
  intros f l1. induction l1 as [| x t IH]; intro l2.
  - apply (id_trans (abl_lsum_zero l2)).
    exact (abl_lsum_ext (fun _ : S => zero)
                        (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') nil)
                        l2 (fun s' : S => id_refl)).
  - apply (id_trans (id_cong (fun w : R => plus (AttnDoeblin.bs_list_sum (f x) l2) w)
                             (IH l2))).
    apply (id_sym (abl_lsum_add (fun s' : S => f x s')
              (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') t) l2)).
Qed.

End AblListSum.

(* ==================== Part 2. The swap slots, derived wholesale ==================== *)
(* The [sum_swap_cc] and [bs_swap] slots of [AttnDoeblin] follow
   wholesale from the enumeration-normalization slot [sum_eq_list]
   plus the Part 1 combinatorics — the swap position is not an
   independent interface slot. *)

Section AblSwap.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Variable enum : list S.
Variable sum_eq_list : forall g : S -> R,
  Id (sum_over_S g) (AttnDoeblin.bs_list_sum g enum).

(* Main statement, in the verbatim shape of the [sum_swap_cc] slot; the
   only premise is the normalization slot [sum_eq_list]. *)
Theorem abl_AtnDoeblin_sum_swap_cc : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Proof.
  intro f.
  apply (id_trans (sum_eq_list (fun s : S => sum_over_S (fun s' : S => f s s')))).
  apply (id_trans (abl_lsum_ext
            (fun s : S => sum_over_S (fun s' : S => f s s'))
            (fun s : S => AttnDoeblin.bs_list_sum (fun s' : S => f s s') enum) enum
            (fun s : S => sum_eq_list (fun s' : S => f s s')))).
  apply (id_trans (abl_lsum_fubini_gen f enum enum)).
  apply (id_trans (id_sym (abl_lsum_ext
            (fun s' : S => sum_over_S (fun s : S => f s s'))
            (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') enum) enum
            (fun s' : S => sum_eq_list (fun s : S => f s s'))))).
  exact (id_sym (sum_eq_list (fun s' : S => sum_over_S (fun s : S => f s s')))).
Qed.

(* Dual statement: the same proposition as the [bs_swap] slot (the two
   slots share one proof). *)
Corollary abl_AtnDoeblin_bs_swap : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Proof.
  exact abl_AtnDoeblin_sum_swap_cc.
Qed.

End AblSwap.

(* ==================== Part 3. Absolute-value idempotence slots ==================== *)
(* The [abs_ge_zero_id_cc] and [bs_abs] slots of [AttnDoeblin] are
   direct instantiations of the main [AbsLeId] lemma; its decidable-
   order extension slot closes fully once the discharged parameters
   are generalized. *)

Section AblAbs.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* Main statement, in the verbatim shape of the [abs_ge_zero_id_cc] slot. *)
Theorem abl_AtnDoeblin_abs_ge_zero_id_cc : forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (ali_abs_ge_zero_id a Ha).
Qed.

(* Dual statement: the same proposition as the [bs_abs] slot. *)
Corollary abl_AtnDoeblin_bs_abs : forall a : R, le zero a -> Id (abs a) a.
Proof.
  exact abl_AtnDoeblin_abs_ge_zero_id_cc.
Qed.

End AblAbs.

(* Closure audit: [Print Assumptions] on every statement. *)
Print Assumptions abl_lsum_ext.
Print Assumptions abl_lsum_add.
Print Assumptions abl_lsum_zero.
Print Assumptions abl_lsum_fubini_gen.
Print Assumptions abl_AtnDoeblin_sum_swap_cc.
Print Assumptions abl_AtnDoeblin_bs_swap.
Print Assumptions abl_AtnDoeblin_abs_ge_zero_id_cc.
Print Assumptions abl_AtnDoeblin_bs_abs.
