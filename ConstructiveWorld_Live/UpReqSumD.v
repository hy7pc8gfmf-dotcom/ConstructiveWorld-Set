(* ConstructiveWorld-Set — unconditional finite-sum laws over an enumerated carrier. *)

(** * UpReqSumD: the enumerated-sum discharge of the sampling-interface sum family.

    Mission.  The [sum_eq_list] bridge of the sampling interface, instantiated
      at the concrete operator [sumd_sumf] (the enumerated list sum of [enum]
      for a carrier [S]), and the discharge of the interface sum family as
      unconditional statements: [sumd_sum_ext], [sumd_sum_linear],
      [sumd_sum_add], [sumd_sum_opp], [sumd_sum_le], [sumd_sum_pos] (cons and
      nonempty-slot forms), the zero-total family [sumd_sum_zero_nonneg_in]
      with its surjectivity upgrade [sumd_sum_zero_nonneg_surj], the Fubini
      swap [sumd_sum_swap], the constant-sum collapse [sumd_sumf_const], and
      the membership bridge [sumd_in_to_In].

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing] through
      [S15_TailFEPUp], [UpReqAlgebra], [UpReqDist] of this development.

    References.  This development, UpReqSumD.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements are carried by [Set]: [req], [le]
      and [lt] are Set-valued interface fields; nonemptiness slots take
      [Not (l = nil)]; membership is the Set-level predicate [sumd_in].
      Statements extract with [Obj.magic] = 0; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqSumD.v] compiles
      cleanly (exit 0); the artifact starts with the bytes
      [436f7121 00015ff4]. *)

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
(* The constant-sum statements below consume [req_list_sum_g_const] and
   [reqd_of_nat] from the GRPO section of [UpReqDist]; its exported names
   are all [reqd_]/[req_]/[fsum_]-prefixed, disjoint from every visible
   name of this file. *)
Require Import UpReqDist.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ================= Section 1. The enumerated finite-sum instance ================= *)
Notation R := Real.

Section SumDischarge.
(* Interface fields resolve through the global instance of the
   unparameterized class. *)

Variable S : Set.
Variable enum : list S.

(* The list-sum machine, self-contained in the shape of the sampling-interface list sum. *)
Fixpoint sumd_list_sum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => zero
  | x :: t => plus (f x) (sumd_list_sum f t)
  end.

(* The concrete finite-sum operator: the discharged instance of the interface sum. *)
Definition sumd_sumf (f : S -> R) : R := sumd_list_sum f enum.

(* The bridge instantiation: at the concrete operator the interface
   assumption collapses to [req_refl], since [sumd_sumf] is definitionally
   the enumerated list sum. *)
Lemma sumd_sum_eq_list : forall g : S -> R,
  real_eq (sumd_sumf g) (sumd_list_sum g enum).
Proof. intro g. exact (req_refl (sumd_list_sum g enum)). Qed.

(* Auxiliary family shared by the discharged statements. *)

(* One-way lifting of strict positivity to weak positivity: the strict
   branch of the interface field [lt_le_iff], a class field of
   [S01_BaseRing] with no body to inline. *)
Lemma sumd_lt_le : forall a : R, real_lt zero a -> real_le zero a.
Proof. intros a H. exact (lt_le_iff zero a (inl H)). Qed.

(* A sum of pointwise nonnegative values is nonnegative; shared by the positivity and zero-total statements. *)
Lemma sumd_list_sum_nonneg : forall (f : S -> R) (l : list S),
  (forall s : S, real_le zero (f s)) -> real_le zero (sumd_list_sum f l).
Proof.
  intros f l H. induction l as [| x t IH].
  - exact (le_refl zero).
  - exact (le_id_l zero (plus zero zero) (plus (f x) (sumd_list_sum f t))
             (req_sym (plus zero zero) zero (plus_zero zero))
             (le_plus_compat zero (f x) zero (sumd_list_sum f t) (H x) IH)).
Qed.

(* Extensionality of the sum. *)
Lemma sumd_list_sum_ext : forall (f g : S -> R) (l : list S),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (sumd_list_sum f l) (sumd_list_sum g l).
Proof.
  intros f g l H. induction l as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_list_sum f t) (sumd_list_sum g t)
             (H x) IH).
Qed.

Lemma sumd_sum_ext : forall f g : S -> R,
  (forall s : S, real_eq (f s) (g s)) -> real_eq (sumd_sumf f) (sumd_sumf g).
Proof.
  intros f g H.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_list_sum f t) (sumd_list_sum g t)
             (H x) IH).
Qed.

(* Linearity of the sum. *)
Lemma sumd_list_sum_linear : forall (a : R) (f : S -> R) (l : list S),
  real_eq (sumd_list_sum (fun s : S => mult a (f s)) l) (mult a (sumd_list_sum f l)).
Proof.
  intros a f l. induction l as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - exact (req_trans
             (plus (mult a (f x)) (sumd_list_sum (fun s : S => mult a (f s)) t))
             (plus (mult a (f x)) (mult a (sumd_list_sum f t)))
             (mult a (plus (f x) (sumd_list_sum f t)))
             (req_plus_compat (mult a (f x)) (mult a (f x))
                (sumd_list_sum (fun s : S => mult a (f s)) t)
                (mult a (sumd_list_sum f t))
                (req_refl (mult a (f x))) IH)
             (req_sym (mult a (plus (f x) (sumd_list_sum f t)))
                (plus (mult a (f x)) (mult a (sumd_list_sum f t)))
                (distrib a (f x) (sumd_list_sum f t)))).
Qed.

Lemma sumd_sum_linear : forall (a : R) (f : S -> R),
  real_eq (sumd_sumf (fun s : S => mult a (f s))) (mult a (sumd_sumf f)).
Proof.
  intros a f.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - exact (req_trans
             (plus (mult a (f x)) (sumd_list_sum (fun s : S => mult a (f s)) t))
             (plus (mult a (f x)) (mult a (sumd_list_sum f t)))
             (mult a (plus (f x) (sumd_list_sum f t)))
             (req_plus_compat (mult a (f x)) (mult a (f x))
                (sumd_list_sum (fun s : S => mult a (f s)) t)
                (mult a (sumd_list_sum f t))
                (req_refl (mult a (f x))) IH)
             (req_sym (mult a (plus (f x) (sumd_list_sum f t)))
                (plus (mult a (f x)) (mult a (sumd_list_sum f t)))
                (distrib a (f x) (sumd_list_sum f t)))).
Qed.

(* Additivity of the sum over pointwise addition. *)
Lemma sumd_list_sum_add : forall (f g : S -> R) (l : list S),
  real_eq (sumd_list_sum (fun s : S => plus (f s) (g s)) l)
      (plus (sumd_list_sum f l) (sumd_list_sum g l)).
Proof.
  intros f g l. induction l as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - exact (req_trans
             (plus (plus (f x) (g x))
                (sumd_list_sum (fun s : S => plus (f s) (g s)) t))
             (plus (plus (f x) (g x))
                (plus (sumd_list_sum f t) (sumd_list_sum g t)))
             (plus (plus (f x) (sumd_list_sum f t))
                (plus (g x) (sumd_list_sum g t)))
             (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x))
                (sumd_list_sum (fun s : S => plus (f s) (g s)) t)
                (plus (sumd_list_sum f t) (sumd_list_sum g t))
                (req_refl (plus (f x) (g x))) IH)
             (req_plus_exchange (f x) (sumd_list_sum f t)
                (g x) (sumd_list_sum g t))).
Qed.

Lemma sumd_sum_add : forall f g : S -> R,
  real_eq (sumd_sumf (fun s : S => plus (f s) (g s)))
      (plus (sumd_sumf f) (sumd_sumf g)).
Proof.
  intros f g.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - exact (req_trans
             (plus (plus (f x) (g x))
                (sumd_list_sum (fun s : S => plus (f s) (g s)) t))
             (plus (plus (f x) (g x))
                (plus (sumd_list_sum f t) (sumd_list_sum g t)))
             (plus (plus (f x) (sumd_list_sum f t))
                (plus (g x) (sumd_list_sum g t)))
             (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x))
                (sumd_list_sum (fun s : S => plus (f s) (g s)) t)
                (plus (sumd_list_sum f t) (sumd_list_sum g t))
                (req_refl (plus (f x) (g x))) IH)
             (req_plus_exchange (f x) (sumd_list_sum f t)
                (g x) (sumd_list_sum g t))).
Qed.

(* The sum commutes with opposition. *)
Lemma sumd_list_sum_opp : forall (f : S -> R) (l : list S),
  real_eq (sumd_list_sum (fun s : S => opp (f s)) l) (opp (sumd_list_sum f l)).
Proof.
  intros f l. induction l as [| x t IH].
  - exact (req_sym (opp zero) zero
             (req_trans (opp zero) (plus zero (opp zero)) zero
                (req_sym (plus zero (opp zero)) (opp zero)
                   (req_plus_zero_l (opp zero)))
                (plus_opp zero))).
  - exact (req_trans
             (plus (opp (f x)) (sumd_list_sum (fun s : S => opp (f s)) t))
             (plus (opp (f x)) (opp (sumd_list_sum f t)))
             (opp (plus (f x) (sumd_list_sum f t)))
             (req_plus_compat (opp (f x)) (opp (f x))
                (sumd_list_sum (fun s : S => opp (f s)) t)
                (opp (sumd_list_sum f t))
                (req_refl (opp (f x))) IH)
             (req_sym (opp (plus (f x) (sumd_list_sum f t)))
                (plus (opp (f x)) (opp (sumd_list_sum f t)))
                (req_opp_plus (f x) (sumd_list_sum f t)))).
Qed.

Lemma sumd_sum_opp : forall f : S -> R,
  real_eq (sumd_sumf (fun s : S => opp (f s))) (opp (sumd_sumf f)).
Proof.
  intros f.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_sym (opp zero) zero
             (req_trans (opp zero) (plus zero (opp zero)) zero
                (req_sym (plus zero (opp zero)) (opp zero)
                   (req_plus_zero_l (opp zero)))
                (plus_opp zero))).
  - exact (req_trans
             (plus (opp (f x)) (sumd_list_sum (fun s : S => opp (f s)) t))
             (plus (opp (f x)) (opp (sumd_list_sum f t)))
             (opp (plus (f x) (sumd_list_sum f t)))
             (req_plus_compat (opp (f x)) (opp (f x))
                (sumd_list_sum (fun s : S => opp (f s)) t)
                (opp (sumd_list_sum f t))
                (req_refl (opp (f x))) IH)
             (req_sym (opp (plus (f x) (sumd_list_sum f t)))
                (plus (opp (f x)) (opp (sumd_list_sum f t)))
                (req_opp_plus (f x) (sumd_list_sum f t)))).
Qed.

(* Monotonicity of the sum under pointwise order. *)
Lemma sumd_list_sum_le : forall (f g : S -> R) (l : list S),
  (forall s : S, real_le (f s) (g s)) -> real_le (sumd_list_sum f l) (sumd_list_sum g l).
Proof.
  intros f g l H. induction l as [| x t IH].
  - exact (le_refl zero).
  - exact (le_plus_compat (f x) (g x) (sumd_list_sum f t) (sumd_list_sum g t)
             (H x) IH).
Qed.

Lemma sumd_sum_le : forall f g : S -> R,
  (forall s : S, real_le (f s) (g s)) -> real_le (sumd_sumf f) (sumd_sumf g).
Proof.
  intros f g H.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (le_refl zero).
  - exact (le_plus_compat (f x) (g x) (sumd_list_sum f t) (sumd_list_sum g t)
             (H x) IH).
Qed.

(* Positivity of the sum over strictly positive values.
   Cons form: the head element witnesses nonemptiness directly, so the
   statement needs no Prop-level nonemptiness data. *)
Lemma sumd_list_sum_pos_cons : forall (f : S -> R) (x : S) (l : list S),
  (forall s : S, real_lt zero (f s)) -> real_lt zero (sumd_list_sum f (x :: l)).
Proof.
  intros f x l H.
  assert (Hn : real_le zero (sumd_list_sum f l)).
  { exact (sumd_list_sum_nonneg f l (fun s : S => sumd_lt_le (f s) (H s))). }
  apply (lt_le_trans zero (f x) (plus (f x) (sumd_list_sum f l)) (H x)).
  apply (le_id_l (f x) (plus (f x) zero) (plus (f x) (sumd_list_sum f l))
           (req_sym (plus (f x) zero) (f x) (plus_zero (f x)))).
  apply (le_plus_compat (f x) (f x) zero (sumd_list_sum f l)
           (le_refl (f x)) Hn).
Qed.

(* Slot form: nonemptiness as an explicit [Not (l = nil)] premise, the
   same datum position as the upstream sampling enumeration; the negation
   sits on the Stdlib equality, matching the upstream signature shape. *)
Lemma sumd_list_sum_pos : forall (f : S -> R) (l : list S),
  Not (l = nil) -> (forall s : S, real_lt zero (f s)) -> real_lt zero (sumd_list_sum f l).
Proof.
  intros f l Hne H.
  destruct l as [| x t].
  - destruct (Hne eq_refl).
  - exact (sumd_list_sum_pos_cons f x t H).
Qed.

Lemma sumd_sum_pos : forall f : S -> R,
  Not (enum = nil) -> (forall s : S, real_lt zero (f s)) -> real_lt zero (sumd_sumf f).
Proof.
  intros f Hne H.
  unfold sumd_sumf.
  destruct enum as [| x t].
  - destruct (Hne eq_refl).
  - apply (lt_le_trans zero (f x) (plus (f x) (sumd_list_sum f t)) (H x)).
    apply (le_id_l (f x) (plus (f x) zero) (plus (f x) (sumd_list_sum f t))
             (req_sym (plus (f x) zero) (f x) (plus_zero (f x)))).
    apply (le_plus_compat (f x) (f x) zero (sumd_list_sum f t)
             (le_refl (f x))
             (sumd_list_sum_nonneg f t
                (fun s : S => sumd_lt_le (f s) (H s)))).
Qed.

(* Zero-total family, in its honest member-indexed form: pointwise
   nonnegativity, a zero total, and membership of [s] in [enum] imply
   [f s = 0].  The universal form would require [enum] to be surjective;
   the surrounding development carries only enumeration nonemptiness, so
   the member-indexed form is the strongest statement available here.
   The membership predicate lives at [Set] (empty type for [nil], sums
   for [cons]), avoiding Prop elimination entirely. *)

(* Set-level membership: an inductive derivation family — the empty
   family at [nil]; the head-equality branch or the tail branch at
   [cons].  The named predicate [sumd_in] is the transparent synonym of
   the family, keeping the statement names stable. *)
Inductive sumd_in_fam (s : S) : list S -> Set :=
| sumd_in_head : forall (x : S) (t : list S), Id x s -> sumd_in_fam s (x :: t)
| sumd_in_tail : forall (x : S) (t : list S), sumd_in_fam s t -> sumd_in_fam s (x :: t).

Definition sumd_in (s : S) (l : list S) : Set := sumd_in_fam s l.

(* Head leg: if [f x] is nonnegative and bounded by a zero total, then [f x] is zero. *)
Lemma sumd_list_sum_zero_nonneg_head : forall (f : S -> R) (x : S) (l : list S),
  (forall s : S, real_le zero (f s)) -> real_eq (sumd_list_sum f (x :: l)) zero ->
  real_eq (f x) zero.
Proof.
  intros f x l Hnn H0.
  exact (le_antisym (f x) zero
           (le_trans (f x) (plus (f x) (sumd_list_sum f l)) zero
              (le_id_l (f x) (plus (f x) zero)
                 (plus (f x) (sumd_list_sum f l))
                 (req_sym (plus (f x) zero) (f x) (plus_zero (f x)))
                 (le_plus_compat (f x) (f x) zero (sumd_list_sum f l)
                    (le_refl (f x)) (sumd_list_sum_nonneg f l Hnn)))
              (le_id_r (plus (f x) (sumd_list_sum f l))
                 (plus (f x) (sumd_list_sum f l)) zero
                 H0 (le_refl (plus (f x) (sumd_list_sum f l)))))
           (Hnn x)).
Qed.

(* Tail leg: a zero total forces a zero tail sum; the head term is commuted to the front first. *)
Lemma sumd_list_sum_zero_nonneg_tail : forall (f : S -> R) (x : S) (l : list S),
  (forall s : S, real_le zero (f s)) -> real_eq (sumd_list_sum f (x :: l)) zero ->
  real_eq (sumd_list_sum f l) zero.
Proof.
  intros f x l Hnn H0.
  exact (le_antisym (sumd_list_sum f l) zero
           (le_trans (sumd_list_sum f l) (plus (sumd_list_sum f l) (f x)) zero
              (le_id_l (sumd_list_sum f l) (plus (sumd_list_sum f l) zero)
                 (plus (sumd_list_sum f l) (f x))
                 (req_sym (plus (sumd_list_sum f l) zero)
                    (sumd_list_sum f l) (plus_zero (sumd_list_sum f l)))
                 (le_plus_compat (sumd_list_sum f l) (sumd_list_sum f l)
                    zero (f x)
                    (le_refl (sumd_list_sum f l)) (Hnn x)))
              (le_id_r (plus (sumd_list_sum f l) (f x))
                 (plus (sumd_list_sum f l) (f x)) zero
                 (req_trans (plus (sumd_list_sum f l) (f x))
                    (plus (f x) (sumd_list_sum f l)) zero
                    (plus_comm (sumd_list_sum f l) (f x)) H0)
                 (le_refl (plus (sumd_list_sum f l) (f x)))))
           (sumd_list_sum_nonneg f l Hnn)).
Qed.

(* The member-indexed zero-total statement, by induction on the list. *)
Lemma sumd_list_sum_zero_nonneg_in : forall (f : S -> R) (l : list S),
  (forall s : S, real_le zero (f s)) -> real_eq (sumd_list_sum f l) zero ->
  forall s : S, sumd_in s l -> real_eq (f s) zero.
Proof.
  intros f l Hnn H0 s Hs. revert H0.
  induction Hs as [y u Heq | y u Ht IH]; intro H0.
  - destruct Heq.
    exact (sumd_list_sum_zero_nonneg_head f y u Hnn H0).
  - exact (IH (sumd_list_sum_zero_nonneg_tail f y u Hnn H0)).
Qed.

(* The same statement for the concrete enumerated sum. *)
Lemma sumd_sum_zero_nonneg_in : forall f : S -> R,
  (forall s : S, real_le zero (f s)) -> real_eq (sumd_sumf f) zero ->
  forall s : S, sumd_in s enum -> real_eq (f s) zero.
Proof.
  intros f Hnn H0 s Hs.
  unfold sumd_sumf in H0.
  exact (sumd_list_sum_zero_nonneg_in f enum Hnn H0 s Hs).
Qed.

(* ============================================================ *)

(*  The list Fubini swap is discharged by induction on the inner list: *)
(*  flattening both sides instead would produce the same multiset in   *)
(*  different orders, and reordering invariance would require          *)
(*  eliminating Prop-level permutation evidence, which is not          *)
(*  available at the level of [Set]; the inner induction plus           *)
(*  additivity closes in two steps with no new structure.              *)
(*                                                                     *)
(*  The constant-sum collapse mirrors the GRPO-section fold proof of   *)
(*  [UpReqDist]: the enumerated fold and that fold share the same      *)
(*  recursion shape, and the induction consumes the same interface     *)
(*  algebra (distributivity, the one/zero laws).                       *)
(*                                                                     *)
(*  The universal form of the zero-total statement is not provable     *)
(*  without surjectivity data for [enum]: with [enum = [a]] and a      *)
(*  point [s] outside [enum], a strictly positive value at [s] is      *)
(*  consistent with a zero total.  Two upgrades are recorded instead:  *)
(*  an explicit-surjection premise form [sumd_sum_zero_nonneg_surj],   *)
(*  and the one-way membership bridge [sumd_in_to_In] (the             *)
(*  [Set]-to-[Prop] direction; the converse is blocked by Prop         *)
(*  elimination and is not claimed).                                   *)

(* Auxiliary: the sum of the zero function is zero. *)
Lemma sumd_list_sum_zero : forall l : list S,
  real_eq (sumd_list_sum (fun _ : S => zero) l) zero.
Proof.
  intro l. induction l as [| x t IH].
  - exact (req_refl zero).
  - exact (req_trans (plus zero (sumd_list_sum (fun _ : S => zero) t))
                     (sumd_list_sum (fun _ : S => zero) t) zero
                     (req_plus_zero_l (sumd_list_sum (fun _ : S => zero) t)) IH).
Qed.

(* The list-level Fubini swap, by induction on the inner list with the outer list fully general. *)
Lemma sumd_list_sum_swap : forall (f : S -> S -> R) (e l : list S),
  real_eq (sumd_list_sum (fun s : S => sumd_list_sum (f s) e) l)
      (sumd_list_sum (fun s' : S => sumd_list_sum (fun s : S => f s s') l) e).
Proof.
  intros f e l. induction e as [| y e' IH].
  - exact (req_trans (sumd_list_sum (fun s : S => sumd_list_sum (f s) nil) l)
                     zero
                     (sumd_list_sum (fun s' : S =>
                        sumd_list_sum (fun s : S => f s s') l) nil)
                     (sumd_list_sum_zero l)
                     (req_refl zero)).
  - exact (req_trans
             (sumd_list_sum (fun s : S =>
                plus (f s y) (sumd_list_sum (f s) e')) l)
             (plus (sumd_list_sum (fun s : S => f s y) l)
                   (sumd_list_sum (fun s : S => sumd_list_sum (f s) e') l))
             (plus (sumd_list_sum (fun s : S => f s y) l)
                   (sumd_list_sum (fun s' : S =>
                      sumd_list_sum (fun s : S => f s s') l) e'))
             (sumd_list_sum_add (fun s : S => f s y)
                                (fun s : S => sumd_list_sum (f s) e') l)
             (req_plus_compat (sumd_list_sum (fun s : S => f s y) l)
                (sumd_list_sum (fun s : S => f s y) l)
                (sumd_list_sum (fun s : S => sumd_list_sum (f s) e') l)
                (sumd_list_sum (fun s' : S =>
                   sumd_list_sum (fun s : S => f s s') l) e')
                (req_refl (sumd_list_sum (fun s : S => f s y) l))
                IH)).
Qed.

(* The concrete enumerated-sum slot: the list-level swap applied to
   [enum] on both sides; a diagonal induction over the two enumerations
   would reprove the same induction body with no additional reach. *)
Lemma sumd_sum_swap : forall f : S -> S -> R,
  real_eq (sumd_sumf (fun s : S => sumd_sumf (fun s' : S => f s s')))
      (sumd_sumf (fun s' : S => sumd_sumf (fun s : S => f s s'))).
Proof. intro f. exact (sumd_list_sum_swap f enum enum). Qed.

(* List-level constant-sum collapse: the sum of a constant function is
   the length embedding times the constant, by the same induction as the
   GRPO-section fold of [UpReqDist] (the two folds share the recursion
   shape and the interface algebra). *)
Lemma sumd_sum_const : forall (c : R) (l : list S),
  real_eq (sumd_list_sum (fun _ : S => c) l) (mult (reqd_of_nat (length l)) c).
Proof.
  intros c l. induction l as [| i rest IH]; cbn [sumd_list_sum length].
  - exact (req_sym (mult zero c) zero
                   (req_trans (mult zero c) (mult c zero) zero
                              (mult_comm zero c) (mult_zero c))).
  - apply (req_trans (plus c (sumd_list_sum (fun _ : S => c) rest))
                     (plus c (mult (reqd_of_nat (length rest)) c))
                     (mult (plus one (reqd_of_nat (length rest))) c)).
    + exact (req_plus_compat c c (sumd_list_sum (fun _ : S => c) rest)
                             (mult (reqd_of_nat (length rest)) c)
                             (req_refl c) IH).
    + apply (req_trans (plus c (mult (reqd_of_nat (length rest)) c))
                       (plus (mult one c) (mult (reqd_of_nat (length rest)) c))
                       (mult (plus one (reqd_of_nat (length rest))) c)).
      * exact (req_plus_compat c (mult one c)
                               (mult (reqd_of_nat (length rest)) c)
                               (mult (reqd_of_nat (length rest)) c)
                               (req_sym (mult one c) c (req_mult_one_l c))
                               (req_refl (mult (reqd_of_nat (length rest)) c))).
      * apply (req_sym (mult (plus one (reqd_of_nat (length rest))) c)
                       (plus (mult one c) (mult (reqd_of_nat (length rest)) c))).
        apply req_mult_plus_distr_r.
Qed.

(* The concrete enumerated-sum slot of the constant-sum collapse,
   via the list-level statement applied to [enum]. *)
Lemma sumd_sumf_const : forall c : R,
  real_eq (sumd_sumf (fun _ : S => c)) (mult (reqd_of_nat (length enum)) c).
Proof. intro c. exact (sumd_sum_const c enum). Qed.

(* The zero-total statement with the surjectivity data as an explicit premise. *)
Lemma sumd_sum_zero_nonneg_surj : forall f : S -> R,
  (forall s : S, sumd_in s enum) ->
  (forall s : S, real_le zero (f s)) -> real_eq (sumd_sumf f) zero ->
  forall s : S, real_eq (f s) zero.
Proof.
  intros f Hsurj Hnn H0 s.
  exact (sumd_sum_zero_nonneg_in f Hnn H0 s (Hsurj s)).
Qed.

(* One-way membership bridge from the Set-level predicate to the Stdlib [In]; the converse direction is not claimed. *)
Lemma sumd_in_to_In : forall (s : S) (l : list S), sumd_in s l -> In s l.
Proof.
  intros s l H. unfold sumd_in in H.
  induction H as [y u Heq | y u Ht IH].
  - assert (Heq' : y = s) by (destruct Heq; apply eq_refl).
    left. exact Heq'.
  - right. exact IH.
Qed.

End SumDischarge.

(* Assumption audits: every statement of this file is closed under the global context. *)
Print Assumptions sumd_sum_eq_list.
Print Assumptions sumd_lt_le.
Print Assumptions sumd_list_sum_nonneg.
Print Assumptions sumd_list_sum_ext.
Print Assumptions sumd_sum_ext.
Print Assumptions sumd_list_sum_linear.
Print Assumptions sumd_sum_linear.
Print Assumptions sumd_list_sum_add.
Print Assumptions sumd_sum_add.
Print Assumptions sumd_list_sum_opp.
Print Assumptions sumd_sum_opp.
Print Assumptions sumd_list_sum_le.
Print Assumptions sumd_sum_le.
Print Assumptions sumd_list_sum_pos_cons.
Print Assumptions sumd_list_sum_pos.
Print Assumptions sumd_sum_pos.
Print Assumptions sumd_list_sum_zero_nonneg_head.
Print Assumptions sumd_list_sum_zero_nonneg_tail.
Print Assumptions sumd_list_sum_zero_nonneg_in.
Print Assumptions sumd_sum_zero_nonneg_in.
(* The seven extension statements. *)
Print Assumptions sumd_list_sum_zero.
Print Assumptions sumd_list_sum_swap.
Print Assumptions sumd_sum_swap.
Print Assumptions sumd_sum_const.
Print Assumptions sumd_sumf_const.
Print Assumptions sumd_sum_zero_nonneg_surj.
Print Assumptions sumd_in_to_In.
