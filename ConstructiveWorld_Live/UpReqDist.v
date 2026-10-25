(* ConstructiveWorld-Set — real_eq-faced distribution, free-energy and GRPO theory. *)

(** * UpReqDist: real_eq-faced distribution, free-energy and GRPO clusters.

    Mission.  real_eq-faced restatement of the distribution, free-energy and
      GRPO families: Boltzmann normalization and its log decomposition, the
      free-energy and training-inference closures [req_free_energy_boltzmann],
      [req_free_energy_kl_decomp], Gibbs inequality [req_gibbs_inequality]
      with its equality case, the entropy-temperature and ELBO layers,
      cross-entropy training equivalence [req_training_equivalence], and the
      GRPO cluster and the nat embedding [reqd_nat_to_R].

    Dependencies.  Stdlib [QArith.QArith], [List].  Requires [S01_BaseRing]
      through [S15_TailFEPUp] and [UpReqAlgebra] of this development.  The
      interface class [RealInterfaceEnhancedSetoid] is unparameterized over
      the global Cauchy real [Real]; statements use [real_eq]/[real_lt]/
      [real_le].

    References.  This development, UpReqDist.v of ConstructiveWorld-Main,
      whose statement names are carried over here verbatim (statement-face
      Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set];
      proofs are pure term-mode chains over the interface fields; extraction
      gives [Obj.magic] = 0; [coqchk] reports [Axioms: none].  Honest
      disclosures: the positivity premise [positive_dist] and the explicit
      dynamics premise of [req_second_law_irreversible].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqDist.v]; exit 0; the
      first eight bytes of the artifact are [436f7121 00015ff4]. *)

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
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the global Real. *)
Notation R := Real.

(* ============================================================ *)
(* ReqDistCommon: shared machinery of this file; the reqd_ prefix avoids name clashes with UpReqAlgebra. *)
(* ============================================================ *)
Section ReqDistCommon.


(* real_eq implies real_le: the right branch of [lt_le_iff]. *)
Lemma reqd_le_of_req : forall a b : R, real_eq a b -> real_le a b.
Proof.  intros a b H. exact (lt_le_iff a b (inr H)).
Qed.

(* Two-argument compatibility of [req_minus], the minus companion of [req_plus_compat]. *)
Lemma reqd_minus_compat : forall a b c d : R,
  real_eq a b -> real_eq c d -> real_eq (req_minus a c) (req_minus b d).
Proof.  intros a b c d Hab Hcd. unfold req_minus.
  exact (req_trans (plus a (opp c)) (plus b (opp c)) (plus b (opp d))
           (req_plus_compat a b (opp c) (opp c) Hab (req_refl (opp c)))
           (req_plus_compat b b (opp c) (opp d) (req_refl b)
              (req_opp_compat c d Hcd))).
Qed.

(* Injectivity of [inv_pos]: via [inv_pos_correct] and left cancellation [req_mult_cancel_l]. *)
Lemma reqd_inv_pos_cancel : forall (a b : R) (Ha : real_lt zero a) (Hb : real_lt zero b),
  real_eq (inv_pos a Ha) (inv_pos b Hb) -> real_eq a b.
Proof.
  intros a b Ha Hb Hinv.
  assert (Hm : real_eq (mult (inv_pos b Hb) a) (mult (inv_pos b Hb) b)).
  { apply (req_trans (mult (inv_pos b Hb) a) (mult a (inv_pos b Hb))
                     (mult (inv_pos b Hb) b)).
    - apply mult_comm.
    - apply (req_trans (mult a (inv_pos b Hb)) (mult a (inv_pos a Ha))
                       (mult (inv_pos b Hb) b)).
      + exact (req_mult_compat a a (inv_pos b Hb) (inv_pos a Ha)
                               (req_refl a)
                               (req_sym (inv_pos a Ha) (inv_pos b Hb) Hinv)).
      + apply (req_trans (mult a (inv_pos a Ha)) one (mult (inv_pos b Hb) b)).
        * apply inv_pos_correct.
        * apply (req_trans one (mult b (inv_pos b Hb)) (mult (inv_pos b Hb) b)).
          -- apply (req_sym (mult b (inv_pos b Hb)) one). apply inv_pos_correct.
          -- apply mult_comm. }
  exact (req_mult_cancel_l (inv_pos b Hb) a b (inv_pos_pos b Hb) Hm).
Qed.

(* Injectivity of log: via [req_exp_neg_opp_log]. The interface exports no exp injectivity, so this detour makes the lemma unconditional. *)
Lemma reqd_log_cancel : forall (a b : R) (Ha : real_lt zero a) (Hb : real_lt zero b),
  real_eq (log a Ha) (log b Hb) -> real_eq a b.
Proof.
  intros a b Ha Hb Hlog.
  apply (req_trans a (exp_neg (opp (log a Ha))) b).
  - apply (req_sym (exp_neg (opp (log a Ha))) a). apply req_exp_neg_opp_log.
  - apply (req_trans (exp_neg (opp (log a Ha))) (exp_neg (opp (log b Hb))) b).
    + apply exp_neg_req_compat_setoid.
      exact (req_opp_compat (log a Ha) (log b Hb) Hlog).
    + apply req_exp_neg_opp_log.
Qed.

(* Nonnegativity of products, via [le_mult_compat_weak] transported by [mult_zero]. *)
Lemma reqd_le_mult_nonneg_t12 : forall a b : R,
  real_le zero a -> real_le zero b -> real_le zero (mult a b).
Proof.
  intros a b Ha Hb.
  apply (le_id_l zero (mult zero b) (mult a b)).
  - exact (req_sym (mult zero b) zero
                   (req_trans (mult zero b) (mult b zero) zero
                              (mult_comm zero b) (mult_zero b))).
  - exact (le_mult_compat_weak zero a b Hb Ha).
Qed.

(* Strict cancellation by a positive factor: c > 0 and a*c > 0 imply a > 0, using a == (a*c)*inv c. *)
Lemma reqd_lt_mult_pos_cancel : forall a c : R,
  real_lt zero c -> real_lt zero (mult a c) -> real_lt zero a.
Proof.
  intros a c Hc Hac.
  apply (lt_id_r zero (mult (mult a c) (inv_pos c Hc)) a).
  - apply (req_trans (mult (mult a c) (inv_pos c Hc))
                     (mult a (mult c (inv_pos c Hc))) a).
    + apply (req_sym (mult a (mult c (inv_pos c Hc)))
                     (mult (mult a c) (inv_pos c Hc))). apply mult_assoc.
    + apply (req_trans (mult a (mult c (inv_pos c Hc))) (mult a one) a).
      * exact (req_mult_compat a a (mult c (inv_pos c Hc)) one
                               (req_refl a) (inv_pos_correct c Hc)).
      * apply mult_one.
  - apply mult_positive.
    + exact Hac.
    + apply inv_pos_pos.
Qed.

(* Three-term rotation: (a+b)+c == (a+c)+b. *)
Lemma reqd_plus_rot : forall a b c : R,
  real_eq (plus (plus a b) c) (plus (plus a c) b).
Proof.
  intros a b c.
  apply (req_trans (plus (plus a b) c) (plus (plus a b) (plus c zero))
                   (plus (plus a c) b)).
  - apply (req_sym (plus (plus a b) (plus c zero)) (plus (plus a b) c)).
    exact (req_plus_compat (plus a b) (plus a b) (plus c zero) c
                           (req_refl (plus a b)) (plus_zero c)).
  - apply (req_trans (plus (plus a b) (plus c zero))
                     (plus (plus a c) (plus b zero)) (plus (plus a c) b)).
    + apply req_plus_swap_mid.
    + exact (req_plus_compat (plus a c) (plus a c) (plus b zero) b
                             (req_refl (plus a c)) (plus_zero b)).
Qed.

(* opp zero == zero. *)
Lemma reqd_opp_zero : real_eq (opp zero) zero.
Proof.  exact (req_trans (opp zero) (plus zero (opp zero)) zero
           (req_sym (plus zero (opp zero)) (opp zero)
              (UpReqAlgebra.req_plus_zero_l (opp zero)))
           (plus_opp zero)).
Qed.

(* a - 0 == a: right zero of [req_minus]. *)
Lemma reqd_minus_zero_r : forall a : R, real_eq (req_minus a zero) a.
Proof.
  intro a. unfold req_minus.
  apply (req_trans (plus a (opp zero)) (plus a zero) a).
  - exact (req_plus_compat a a (opp zero) zero (req_refl a) reqd_opp_zero).
  - apply plus_zero.
Qed.
End ReqDistCommon.

(* ============================================================ *)
(* Section ReqSumLayer: the setoid summation interface — extension, linearity, positivity. *)
(* ============================================================ *)
Section ReqSumLayer.

Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    real_eq (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    real_eq (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, real_le (f s) (g s)) -> real_le (sumf f) (sumf g).
Hypothesis sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, real_le zero (f s)) -> real_eq (sumf f) zero ->
    forall s : S, real_eq (f s) zero.

(* Sum of the pointwise opposite equals the opposite of the sum. *)
Lemma reqd_sum_opp :
  forall f : S -> R, real_eq (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (sum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply (req_opp_compat (f s) (mult one (f s))).
      exact (req_sym (mult one (f s)) (f s) (req_mult_one_l (f s))).
    + apply (req_sym (mult (opp one) (f s)) (opp (mult one (f s)))).
      apply req_opp_mult_r.
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + apply (sum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f)) (opp (mult one (sumf f)))
                       (opp (sumf f))).
      * apply req_opp_mult_r.
      * apply (req_opp_compat (mult one (sumf f)) (sumf f)).
        apply req_mult_one_l.
Qed.

(* Sums split under pointwise subtraction. *)
Lemma reqd_sum_minus :
  forall f g : S -> R,
    real_eq (sumf (fun s => req_minus (f s) (g s))) (req_minus (sumf f) (sumf g)).
Proof.
  intros f g. unfold req_minus.
  apply (req_trans (sumf (fun s => plus (f s) (opp (g s))))
                   (plus (sumf f) (sumf (fun s => opp (g s))))
                   (plus (sumf f) (opp (sumf g)))).
  - apply sum_add.
  - apply (req_plus_compat (sumf f) (sumf f)
                           (sumf (fun s => opp (g s))) (opp (sumf g))
                           (req_refl (sumf f))).
    apply reqd_sum_opp.
Qed.

(* The zero function sums to zero, via extensionality and linearity. *)
Lemma reqd_sum_zero : real_eq (sumf (fun _ : S => zero)) zero.
Proof.
  apply (req_trans (sumf (fun _ : S => zero))
                   (sumf (fun _ : S => mult zero zero)) zero).
  - apply (sum_ext (fun _ : S => zero) (fun _ : S => mult zero zero)).
    intro s. apply (req_sym (mult zero zero) zero). apply mult_zero.
  - apply (req_trans (sumf (fun _ : S => mult zero zero))
                     (mult zero (sumf (fun _ : S => zero))) zero).
    + apply (sum_linear zero (fun _ : S => zero)).
    + apply (req_trans (mult zero (sumf (fun _ : S => zero))) zero zero).
      * exact (req_trans (mult zero (sumf (fun _ : S => zero)))
                         (mult (sumf (fun _ : S => zero)) zero) zero
                         (mult_comm zero (sumf (fun _ : S => zero)))
                         (mult_zero (sumf (fun _ : S => zero)))).
      * apply req_refl.
Qed.

End ReqSumLayer.

(* ============================================================ *)
(* Section ReqGRPO: the GRPO cluster over real_eq; the group enumeration machinery is nat/list-level and reused as is. *)
(* [reqd_of_nat] and [reqd_list_sum_g] rebuild the nat embedding and the list fold over the setoid operations. *)
(* ============================================================ *)
Section ReqGRPO.


(* The embedding of nat into R: 0 maps to zero and S n to one plus the embedding of n. *)
Fixpoint reqd_of_nat (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S n' => plus one (reqd_of_nat n')
  end.

Variable Group : Set.
Variable group_enum : list Group.
Definition reqd_group_size : nat := length group_enum.
Variable group_size_pos : real_lt zero (reqd_of_nat reqd_group_size).
Variable reward_group : Group -> R.

(* Group sum: fold over the list. *)
Fixpoint reqd_list_sum_g (f : Group -> R) (l : list Group) : R :=
  match l with
  | nil => zero
  | i :: rest => plus (f i) (reqd_list_sum_g f rest)
  end.

(* Id list_sum_g_linear @23828 *)
Lemma req_list_sum_g_linear : forall (a : R) (f : Group -> R) (l : list Group),
  real_eq (reqd_list_sum_g (fun i => mult a (f i)) l)
      (mult a (reqd_list_sum_g f l)).
Proof.
  intros a f l. induction l as [| i rest IH]; cbn [reqd_list_sum_g].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - apply (req_trans (plus (mult a (f i)) (reqd_list_sum_g (fun i => mult a (f i)) rest))
                     (plus (mult a (f i)) (mult a (reqd_list_sum_g f rest)))
                     (mult a (plus (f i) (reqd_list_sum_g f rest)))).
    + exact (req_plus_compat (mult a (f i)) (mult a (f i))
                             (reqd_list_sum_g (fun i => mult a (f i)) rest)
                             (mult a (reqd_list_sum_g f rest))
                             (req_refl (mult a (f i))) IH).
    + apply (req_sym (mult a (plus (f i) (reqd_list_sum_g f rest)))
                     (plus (mult a (f i)) (mult a (reqd_list_sum_g f rest)))).
      apply distrib.
Qed.

(* Id list_sum_g_add @23836 *)
Lemma req_list_sum_g_add : forall f g : Group -> R, forall l : list Group,
  real_eq (reqd_list_sum_g (fun i => plus (f i) (g i)) l)
      (plus (reqd_list_sum_g f l) (reqd_list_sum_g g l)).
Proof.
  intros f g l. induction l as [| i rest IH]; cbn [reqd_list_sum_g].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - apply (req_trans (plus (plus (f i) (g i))
                          (reqd_list_sum_g (fun i => plus (f i) (g i)) rest))
                     (plus (plus (f i) (g i))
                           (plus (reqd_list_sum_g f rest) (reqd_list_sum_g g rest)))
                     (plus (plus (f i) (reqd_list_sum_g f rest))
                           (plus (g i) (reqd_list_sum_g g rest)))).
    + exact (req_plus_compat (plus (f i) (g i)) (plus (f i) (g i))
                             (reqd_list_sum_g (fun i => plus (f i) (g i)) rest)
                             (plus (reqd_list_sum_g f rest) (reqd_list_sum_g g rest))
                             (req_refl (plus (f i) (g i))) IH).
    + apply req_plus_swap_mid.
Qed.

(* Id list_sum_g_ext @23844 *)
Lemma req_list_sum_g_ext : forall f g : Group -> R, forall l : list Group,
  (forall i : Group, real_eq (f i) (g i)) ->
  real_eq (reqd_list_sum_g f l) (reqd_list_sum_g g l).
Proof.
  intros f g l Hfg. induction l as [| i rest IH]; cbn [reqd_list_sum_g].
  - apply req_refl.
  - apply (req_trans (plus (f i) (reqd_list_sum_g f rest))
                     (plus (f i) (reqd_list_sum_g g rest))
                     (plus (g i) (reqd_list_sum_g g rest))).
    + exact (req_plus_compat (f i) (f i) (reqd_list_sum_g f rest)
                             (reqd_list_sum_g g rest) (req_refl (f i)) IH).
    + exact (req_plus_compat (f i) (g i) (reqd_list_sum_g g rest)
                             (reqd_list_sum_g g rest) (Hfg i) (req_refl (reqd_list_sum_g g rest))).
Qed.

(* Sum of a constant function: sum a == of_nat (length l) * a. *)
Lemma req_list_sum_g_const : forall (a : R) (l : list Group),
  real_eq (reqd_list_sum_g (fun _ => a) l) (mult (reqd_of_nat (length l)) a).
Proof.
  intros a l. induction l as [| i rest IH]; cbn [reqd_list_sum_g].
  - exact (req_sym (mult zero a) zero
                   (req_trans (mult zero a) (mult a zero) zero
                              (mult_comm zero a) (mult_zero a))).
  - apply (req_trans (plus a (reqd_list_sum_g (fun _ => a) rest))
                     (plus a (mult (reqd_of_nat (length rest)) a))
                     (mult (plus one (reqd_of_nat (length rest))) a)).
    + exact (req_plus_compat a a (reqd_list_sum_g (fun _ => a) rest)
                             (mult (reqd_of_nat (length rest)) a)
                             (req_refl a) IH).
    + apply (req_trans (plus a (mult (reqd_of_nat (length rest)) a))
                       (plus (mult one a) (mult (reqd_of_nat (length rest)) a))
                       (mult (plus one (reqd_of_nat (length rest))) a)).
      * exact (req_plus_compat a (mult one a)
                               (mult (reqd_of_nat (length rest)) a)
                               (mult (reqd_of_nat (length rest)) a)
                               (req_sym (mult one a) a (req_mult_one_l a))
                               (req_refl (mult (reqd_of_nat (length rest)) a))).
      * apply (req_sym (mult (plus one (reqd_of_nat (length rest))) a)
                       (plus (mult one a) (mult (reqd_of_nat (length rest)) a))).
        apply req_mult_plus_distr_r.
Qed.

(* Sum of the pointwise opposite: sum (-f) == - sum f. *)
Lemma req_list_sum_g_opp : forall f : Group -> R, forall l : list Group,
  real_eq (reqd_list_sum_g (fun i => opp (f i)) l) (opp (reqd_list_sum_g f l)).
Proof.
  intros f l. induction l as [| i rest IH]; cbn [reqd_list_sum_g].
  - exact (req_sym (opp zero) zero reqd_opp_zero).
  - apply (req_trans (plus (opp (f i)) (reqd_list_sum_g (fun i => opp (f i)) rest))
                     (plus (opp (f i)) (opp (reqd_list_sum_g f rest)))
                     (opp (plus (f i) (reqd_list_sum_g f rest)))).
    + exact (req_plus_compat (opp (f i)) (opp (f i))
                             (reqd_list_sum_g (fun i => opp (f i)) rest)
                             (opp (reqd_list_sum_g f rest))
                             (req_refl (opp (f i))) IH).
    + apply (req_sym (opp (plus (f i) (reqd_list_sum_g f rest)))
                     (plus (opp (f i)) (opp (reqd_list_sum_g f rest)))).
      apply req_opp_plus.
Qed.

(* Sums split under pointwise subtraction: sum (f - g) == sum f - sum g. *)
Lemma req_list_sum_g_minus : forall f g : Group -> R, forall l : list Group,
  real_eq (reqd_list_sum_g (fun i => req_minus (f i) (g i)) l)
      (req_minus (reqd_list_sum_g f l) (reqd_list_sum_g g l)).
Proof.
  intros f g l. unfold req_minus.
  apply (req_trans (reqd_list_sum_g (fun i => plus (f i) (opp (g i))) l)
                   (plus (reqd_list_sum_g f l)
                         (reqd_list_sum_g (fun i => opp (g i)) l))
                   (plus (reqd_list_sum_g f l) (opp (reqd_list_sum_g g l)))).
  - apply req_list_sum_g_add.
  - exact (req_plus_compat (reqd_list_sum_g f l) (reqd_list_sum_g f l)
                           (reqd_list_sum_g (fun i => opp (g i)) l)
                           (opp (reqd_list_sum_g g l))
                           (req_refl (reqd_list_sum_g f l))
                           (req_list_sum_g_opp g l)).
Qed.

(* Group mean: mu = (1/G) * sum r_i. *)
Definition req_group_mean : R :=
  mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
       (reqd_list_sum_g reward_group group_enum).

(* Group-relative advantage: A_i = r_i - mu. *)
Definition req_grpo_advantage (i : Group) : R :=
  req_minus (reward_group i) req_group_mean.

(* Defining identity of the mean: G*mu == sum r. *)
Lemma req_group_mean_def :
  real_eq (mult (reqd_of_nat reqd_group_size) req_group_mean)
      (reqd_list_sum_g reward_group group_enum).
Proof.
  unfold req_group_mean.
  apply (req_trans (mult (reqd_of_nat reqd_group_size)
                         (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                               (reqd_list_sum_g reward_group group_enum)))
                   (mult (mult (reqd_of_nat reqd_group_size)
                               (inv_pos (reqd_of_nat reqd_group_size) group_size_pos))
                         (reqd_list_sum_g reward_group group_enum))
                   (reqd_list_sum_g reward_group group_enum)).
  - apply mult_assoc.
  - apply (req_trans (mult (mult (reqd_of_nat reqd_group_size)
                                (inv_pos (reqd_of_nat reqd_group_size) group_size_pos))
                           (reqd_list_sum_g reward_group group_enum))
                     (mult one (reqd_list_sum_g reward_group group_enum))
                     (reqd_list_sum_g reward_group group_enum)).
    + exact (req_mult_compat (mult (reqd_of_nat reqd_group_size)
                                   (inv_pos (reqd_of_nat reqd_group_size) group_size_pos))
                             one
                             (reqd_list_sum_g reward_group group_enum)
                             (reqd_list_sum_g reward_group group_enum)
                             (inv_pos_correct (reqd_of_nat reqd_group_size) group_size_pos)
                             (req_refl (reqd_list_sum_g reward_group group_enum))).
    + apply (req_trans (mult one (reqd_list_sum_g reward_group group_enum))
                       (mult (reqd_list_sum_g reward_group group_enum) one)
                       (reqd_list_sum_g reward_group group_enum)).
      * apply mult_comm.
      * apply mult_one.
Qed.

(* Weighted advantages sum to zero: sum A_i*c == 0 for any c. *)
Theorem req_grpo_advantage_zero_mean :
  forall c : R,
    real_eq (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) c) group_enum) zero.
Proof.
  intros c.
  assert (Hext : real_eq (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) c) group_enum)
                     (reqd_list_sum_g (fun i => mult c (req_grpo_advantage i)) group_enum)).
  { apply req_list_sum_g_ext. intro i. apply mult_comm. }
  assert (Hlin : real_eq (reqd_list_sum_g (fun i => mult c (req_grpo_advantage i)) group_enum)
                     (mult c (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum))).
  { exact (req_list_sum_g_linear c (fun i => req_minus (reward_group i) req_group_mean) group_enum). }
  assert (Hcancel : real_eq (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum) zero).
  { assert (Hmin : real_eq (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum)
                       (req_minus (reqd_list_sum_g reward_group group_enum)
                                  (reqd_list_sum_g (fun _ => req_group_mean) group_enum)))
      by exact (req_list_sum_g_minus reward_group (fun _ => req_group_mean) group_enum).
    assert (Hconst : real_eq (reqd_list_sum_g (fun _ => req_group_mean) group_enum)
                         (mult (reqd_of_nat reqd_group_size) req_group_mean))
      by exact (req_list_sum_g_const req_group_mean group_enum).
    assert (Hcc := req_group_mean_def).
    apply (req_trans (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum)
                     (req_minus (reqd_list_sum_g reward_group group_enum)
                                (mult (reqd_of_nat reqd_group_size) req_group_mean))
                     zero).
    - apply (req_trans (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum)
                       (req_minus (reqd_list_sum_g reward_group group_enum)
                                  (reqd_list_sum_g (fun _ => req_group_mean) group_enum))
                       (req_minus (reqd_list_sum_g reward_group group_enum)
                                  (mult (reqd_of_nat reqd_group_size) req_group_mean))).
      + exact Hmin.
      + exact (reqd_minus_compat (reqd_list_sum_g reward_group group_enum)
                                 (reqd_list_sum_g reward_group group_enum)
                                 (reqd_list_sum_g (fun _ => req_group_mean) group_enum)
                                 (mult (reqd_of_nat reqd_group_size) req_group_mean)
                                 (req_refl (reqd_list_sum_g reward_group group_enum)) Hconst).
    - apply (req_trans (req_minus (reqd_list_sum_g reward_group group_enum)
                                  (mult (reqd_of_nat reqd_group_size) req_group_mean))
                       (req_minus (reqd_list_sum_g reward_group group_enum)
                                  (reqd_list_sum_g reward_group group_enum))
                       zero).
      + exact (reqd_minus_compat (reqd_list_sum_g reward_group group_enum)
                                 (reqd_list_sum_g reward_group group_enum)
                                 (mult (reqd_of_nat reqd_group_size) req_group_mean)
                                 (reqd_list_sum_g reward_group group_enum)
                                 (req_refl (reqd_list_sum_g reward_group group_enum)) Hcc).
      + apply req_minus_self_zero. apply req_refl. }
  apply (req_trans (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) c) group_enum)
                   (mult c (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum))
                   zero).
  - exact (req_trans _ _ _ Hext Hlin).
  - apply (req_trans (mult c (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum))
                     (mult c zero) zero).
    + exact (req_mult_compat c c
                             (reqd_list_sum_g (fun i => req_minus (reward_group i) req_group_mean) group_enum)
                             zero (req_refl c) Hcancel).
    + apply mult_zero.
Qed.

(* Group second moment / centered second moment. *)
Definition req_group_raw_second_moment : R :=
  reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum.
Definition req_group_centered_second_moment : R :=
  reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum.

(* Square expansion: (r-mu)^2 == r^2 - 2*r*mu + mu^2. *)
Lemma req_grpo_square_expand : forall i : Group,
  real_eq (mult (req_grpo_advantage i) (req_grpo_advantage i))
      (plus (mult (reward_group i) (reward_group i))
            (plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                  (mult req_group_mean req_group_mean))).
Proof.
  intro i. unfold req_grpo_advantage, req_minus.
  set (r := reward_group i). set (m := req_group_mean).
  (* Square expansion, first helper. *)
  (* Left half: r*(r + opp mu) == r^2 + opp (r*mu). *)
  assert (H2 : real_eq (mult r (plus r (opp m)))
                   (plus (mult r r) (opp (mult r m)))).
  { apply (req_trans (mult r (plus r (opp m)))
                     (plus (mult r r) (mult r (opp m)))
                     (plus (mult r r) (opp (mult r m)))).
    - apply distrib.
    - exact (req_plus_compat (mult r r) (mult r r) (mult r (opp m)) (opp (mult r m))
                             (req_refl (mult r r)) (req_opp_mult_l r m)). }
  (* Right half: opp mu*(r + opp mu) == opp (mu*r) + mu*mu. *)
  assert (H6 : real_eq (mult (opp m) (opp m)) (mult m m)).
  { apply (req_trans (mult (opp m) (opp m)) (opp (mult m (opp m)))
                     (mult m m)).
    - apply req_opp_mult_r.
    - apply (req_trans (opp (mult m (opp m))) (opp (opp (mult m m))) (mult m m)).
      + exact (req_opp_compat (mult m (opp m)) (opp (mult m m)) (req_opp_mult_l m m)).
      + apply req_double_neg. }
  assert (H4 : real_eq (mult (opp m) (plus r (opp m)))
                   (plus (opp (mult m r)) (mult m m))).
  { apply (req_trans (mult (opp m) (plus r (opp m)))
                     (plus (mult (opp m) r) (mult (opp m) (opp m)))
                     (plus (opp (mult m r)) (mult m m))).
    - apply distrib.
    - exact (req_plus_compat (mult (opp m) r) (opp (mult m r))
                             (mult (opp m) (opp m)) (mult m m)
                             (req_opp_mult_r m r) H6). }
  (* Cross-term merge: r^2 + opp (r*mu) + opp (mu*r) + mu^2 reduces to r^2 + opp (2*r*mu) + mu^2. *)
  assert (Hm2 : real_eq (plus (opp (mult m r)) (opp (mult r m)))
                    (opp (mult (mult (plus one one) r) m))).
  { assert (H2b : real_eq (plus (mult m r) (mult r m)) (mult (mult (plus one one) r) m)).
    { apply (req_trans (plus (mult m r) (mult r m))
                       (plus (mult r m) (mult r m))
                       (mult (mult (plus one one) r) m)).
      - exact (req_plus_compat (mult m r) (mult r m) (mult r m) (mult r m)
                               (mult_comm m r) (req_refl (mult r m))).
      - apply (req_trans (plus (mult r m) (mult r m)) (mult (plus r r) m)
                         (mult (mult (plus one one) r) m)).
        + apply (req_sym (mult (plus r r) m) (plus (mult r m) (mult r m))).
          apply (req_mult_plus_distr_r r r m).
        + apply (req_sym (mult (mult (plus one one) r) m) (mult (plus r r) m)).
          exact (req_mult_compat (mult (plus one one) r) (plus r r) m m
                                 (req_two_mult r) (req_refl m)). }
    apply (req_trans (plus (opp (mult m r)) (opp (mult r m)))
                     (opp (plus (mult m r) (mult r m)))
                     (opp (mult (mult (plus one one) r) m))).
    - apply (req_sym (opp (plus (mult m r) (mult r m)))
                     (plus (opp (mult m r)) (opp (mult r m)))).
      apply (req_opp_plus (mult m r) (mult r m)).
    - exact (req_opp_compat (plus (mult m r) (mult r m))
                            (mult (mult (plus one one) r) m) H2b). }
  assert (H7 : real_eq (plus (plus (mult r r) (opp (mult r m)))
                         (plus (opp (mult m r)) (mult m m)))
                   (plus (mult r r)
                         (plus (opp (mult (mult (plus one one) r) m))
                               (mult m m)))).
  { apply (req_trans (plus (plus (mult r r) (opp (mult r m)))
                           (plus (opp (mult m r)) (mult m m)))
                     (plus (mult r r)
                           (plus (opp (mult m r)) (plus (opp (mult r m)) (mult m m))))
                     (plus (mult r r)
                           (plus (opp (mult (mult (plus one one) r) m))
                                 (mult m m)))).
    - apply (req_trans (plus (plus (mult r r) (opp (mult r m)))
                             (plus (opp (mult m r)) (mult m m)))
                       (plus (plus (mult r r) (opp (mult m r)))
                             (plus (opp (mult r m)) (mult m m)))
                       (plus (mult r r)
                             (plus (opp (mult m r)) (plus (opp (mult r m)) (mult m m))))).
      + apply req_plus_swap_mid.
      + apply (req_sym (plus (mult r r)
                             (plus (opp (mult m r)) (plus (opp (mult r m)) (mult m m))))
                       (plus (plus (mult r r) (opp (mult m r)))
                             (plus (opp (mult r m)) (mult m m)))).
        apply (plus_assoc (mult r r) (opp (mult m r)) (plus (opp (mult r m)) (mult m m))).
    - exact (req_plus_compat (mult r r) (mult r r)
                             (plus (opp (mult m r)) (plus (opp (mult r m)) (mult m m)))
                             (plus (opp (mult (mult (plus one one) r) m)) (mult m m))
                             (req_refl (mult r r))
                             (req_trans (plus (opp (mult m r)) (plus (opp (mult r m)) (mult m m)))
                                        (plus (plus (opp (mult m r)) (opp (mult r m))) (mult m m))
                                        (plus (opp (mult (mult (plus one one) r) m)) (mult m m))
                                        (plus_assoc (opp (mult m r)) (opp (mult r m)) (mult m m))
                                        (req_plus_compat (plus (opp (mult m r)) (opp (mult r m)))
                                                         (opp (mult (mult (plus one one) r) m))
                                                         (mult m m) (mult m m)
                                                         Hm2 (req_refl (mult m m))))).
  }
  (* Assembly: the square (r + opp mu)*(r + opp mu) splits into the two halves, then the cross terms merge. *)
  apply (req_trans (mult (plus r (opp m)) (plus r (opp m)))
                   (plus (mult r (plus r (opp m))) (mult (opp m) (plus r (opp m))))
                   (plus (mult r r)
                         (plus (opp (mult (mult (plus one one) r) m))
                               (mult m m)))).
  - apply req_mult_plus_distr_r.
  - apply (req_trans (plus (mult r (plus r (opp m))) (mult (opp m) (plus r (opp m))))
                     (plus (plus (mult r r) (opp (mult r m)))
                           (plus (opp (mult m r)) (mult m m)))
                     (plus (mult r r)
                           (plus (opp (mult (mult (plus one one) r) m))
                                 (mult m m)))).
    + exact (req_plus_compat _ _ _ _ H2 H4).
    + exact H7.
Qed.

(* Variance identity: sum (r-mu)^2 == sum r^2 - G*mu^2. *)
Theorem req_grpo_variance_identity :
  real_eq req_group_centered_second_moment
      (req_minus req_group_raw_second_moment
                 (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean))).
Proof.
  unfold req_group_centered_second_moment, req_group_raw_second_moment.
  (* Pointwise expansion. *)
  assert (Hext : real_eq (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                     (reqd_list_sum_g (fun i =>
                        plus (mult (reward_group i) (reward_group i))
                             (plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                                   (mult req_group_mean req_group_mean))) group_enum))
    by (apply req_list_sum_g_ext; intro i; exact (req_grpo_square_expand i)).
  (* Linearity of the sum, applied twice. *)
  assert (Hadd1 : real_eq (reqd_list_sum_g (fun i =>
                   plus (mult (reward_group i) (reward_group i))
                        (plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                              (mult req_group_mean req_group_mean))) group_enum)
                  (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                        (reqd_list_sum_g (fun i =>
                          plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                               (mult req_group_mean req_group_mean)) group_enum)))
    by (apply req_list_sum_g_add).
  assert (Hadd2 : real_eq (reqd_list_sum_g (fun i =>
                   plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                        (mult req_group_mean req_group_mean)) group_enum)
                  (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                        (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))
    by (apply req_list_sum_g_add).
  (* Σ opp(2 r μ) == opp(2 Σr μ) *)
  assert (Hopp : real_eq (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                     (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))).
  { assert (Hlin : real_eq (reqd_list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) req_group_mean) group_enum)
                       (mult req_group_mean (reqd_list_sum_g (fun i => mult (plus one one) (reward_group i)) group_enum))).
    { apply (req_trans (reqd_list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) req_group_mean) group_enum)
                       (reqd_list_sum_g (fun i => mult req_group_mean (mult (plus one one) (reward_group i))) group_enum)
                       (mult req_group_mean (reqd_list_sum_g (fun i => mult (plus one one) (reward_group i)) group_enum))).
      - apply req_list_sum_g_ext. intro i. apply mult_comm.
      - apply req_list_sum_g_linear. }
    assert (Hlin2 : real_eq (reqd_list_sum_g (fun i => mult (plus one one) (reward_group i)) group_enum)
                        (mult (plus one one) (reqd_list_sum_g reward_group group_enum)))
      by exact (req_list_sum_g_linear (plus one one) reward_group group_enum).
    assert (HA : real_eq (reqd_list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) req_group_mean) group_enum)
                     (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean)).
    { assert (Hsw : real_eq (reqd_list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) req_group_mean) group_enum)
                        (reqd_list_sum_g (fun i => mult req_group_mean (mult (plus one one) (reward_group i))) group_enum))
        by (apply req_list_sum_g_ext; intro i; apply mult_comm).
      assert (Hmid : real_eq (reqd_list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) req_group_mean) group_enum)
                         (mult req_group_mean (mult (plus one one) (reqd_list_sum_g reward_group group_enum))))
        by exact (req_trans _ _ _ Hsw
                             (req_trans _ _ _
                              (req_list_sum_g_linear req_group_mean
                                                     (fun i => mult (plus one one) (reward_group i))
                                                     group_enum)
                              (req_mult_compat req_group_mean req_group_mean
                                               (reqd_list_sum_g (fun i => mult (plus one one) (reward_group i)) group_enum)
                                               (mult (plus one one) (reqd_list_sum_g reward_group group_enum))
                                               (req_refl req_group_mean) Hlin2))).
      exact (req_trans _ _ _ Hmid
                           (mult_comm req_group_mean
                                      (mult (plus one one) (reqd_list_sum_g reward_group group_enum)))). }
    apply (req_trans (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                     (opp (reqd_list_sum_g (fun i => mult (mult (plus one one) (reward_group i)) req_group_mean) group_enum))
                     (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))).
    - apply req_list_sum_g_opp.
    - exact (req_opp_compat _ _ HA). }
  (* sum mu^2 == G*mu^2 and sum r == G*mu. *)
  assert (Hconst : real_eq (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)
                       (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)))
    by exact (req_list_sum_g_const (mult req_group_mean req_group_mean) group_enum).
  assert (Hmu : real_eq (reqd_list_sum_g reward_group group_enum)
                    (mult (reqd_of_nat reqd_group_size) req_group_mean))
    by exact (req_sym (mult (reqd_of_nat reqd_group_size) req_group_mean)
                      (reqd_list_sum_g reward_group group_enum) req_group_mean_def).
  assert (Hcross : real_eq (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                       (opp (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean)))
    by (apply (req_opp_compat _ _ (req_mult_compat (mult (plus one one) (reqd_list_sum_g reward_group group_enum))
                                                   (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean))
                                                   req_group_mean req_group_mean
                                                   (req_mult_compat (plus one one) (plus one one)
                                                                    (reqd_list_sum_g reward_group group_enum)
                                                                    (mult (reqd_of_nat reqd_group_size) req_group_mean)
                                                                    (req_refl (plus one one)) Hmu)
                                                   (req_refl req_group_mean)))).
  (* 2x - x == -x with x := G*mu^2. *)
  assert (Hcancel2 : real_eq (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean))
                               (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)))
                         (opp (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)))).
  { assert (H2a : real_eq (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean)
                      (mult (plus one one) (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)))).
    { apply (req_trans (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean)
                       (mult (plus one one) (mult (mult (reqd_of_nat reqd_group_size) req_group_mean) req_group_mean))
                       (mult (plus one one) (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)))).
      - apply (req_sym (mult (plus one one) (mult (mult (reqd_of_nat reqd_group_size) req_group_mean) req_group_mean))
                       (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean)).
        apply mult_assoc.
      - exact (req_mult_compat (plus one one) (plus one one)
                               (mult (mult (reqd_of_nat reqd_group_size) req_group_mean) req_group_mean)
                               (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean))
                               (req_refl (plus one one))
                               (req_sym (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean))
                                        (mult (mult (reqd_of_nat reqd_group_size) req_group_mean) req_group_mean)
                                        (mult_assoc (reqd_of_nat reqd_group_size) req_group_mean req_group_mean))). }
    set (x := mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)).
    assert (H2c : real_eq (plus (opp (mult (plus one one) x)) x) (opp x)).
    { apply (req_trans (plus (opp (mult (plus one one) x)) x)
                       (plus (opp (plus x x)) x) (opp x)).
      - exact (req_plus_compat (opp (mult (plus one one) x)) (opp (plus x x)) x x
                               (req_opp_compat (mult (plus one one) x) (plus x x) (req_two_mult x))
                               (req_refl x)).
      - apply (req_trans (plus (opp (plus x x)) x) (plus (plus (opp x) (opp x)) x) (opp x)).
        + exact (req_plus_compat (opp (plus x x)) (plus (opp x) (opp x)) x x
                                 (req_opp_plus x x)
                                 (req_refl x)).
        + apply (req_trans (plus (plus (opp x) (opp x)) x) (plus (opp x) (plus (opp x) x)) (opp x)).
          * apply (req_sym (plus (opp x) (plus (opp x) x)) (plus (plus (opp x) (opp x)) x)).
            apply plus_assoc.
          * apply (req_trans (plus (opp x) (plus (opp x) x)) (plus (opp x) zero) (opp x)).
            -- exact (req_plus_compat (opp x) (opp x) (plus (opp x) x) zero (req_refl (opp x))
                                      (req_trans (plus (opp x) x) (plus x (opp x)) zero
                                                 (plus_comm (opp x) x) (plus_opp x))).
            -- apply (req_trans (plus (opp x) zero) (opp x) (opp x)
                                (plus_zero (opp x)) (req_refl (opp x))). }
    exact (req_trans (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean))
                           (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)))
                     (plus (opp (mult (plus one one) x)) x) (opp x)
                     (req_plus_compat (opp (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean))
                                      (opp (mult (plus one one) x))
                                      (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)) x
                                      (req_opp_compat _ _ H2a) (req_refl x))
                     H2c). }
  (* Assembly: the second-moment sum reduces to sum r^2 - G*mu^2 after cancellation. *)
  assert (Hl1 : real_eq (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                    (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                          (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))).
  { apply (req_trans (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                     (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (reqd_list_sum_g (fun i =>
                              plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                                   (mult req_group_mean req_group_mean)) group_enum))
                     (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                 (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))).
    - exact (req_trans _ _ _ Hext Hadd1).
    - exact (req_plus_compat (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                            (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                            (reqd_list_sum_g (fun i =>
                               plus (opp (mult (mult (plus one one) (reward_group i)) req_group_mean))
                                    (mult req_group_mean req_group_mean)) group_enum)
                            (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                  (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum))
                            (req_refl (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum))
                            Hadd2).
  }
  assert (Hl2 : real_eq (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                    (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                          (plus (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))).
  { apply (req_trans (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                     (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                 (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))
                     (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (plus (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                 (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))).
    - exact Hl1.
    - exact (req_plus_compat (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                             (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                             (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                   (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum))
                             (plus (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                   (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum))
                             (req_refl (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum))
                             (req_plus_compat (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                              (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                              (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)
                                              (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)
                                              Hopp
                                              (req_refl (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))).
  }
  assert (Hl3 : real_eq (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                    (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                          (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean))
                                (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean))))).
  { apply (req_trans (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                     (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                 (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))
                     (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                           (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean))
                                 (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean))))).
    - exact Hl1.
    - exact (req_plus_compat (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                             (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                             (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                   (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum))
                             (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean))
                                   (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)))
                             (req_refl (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum))
                             (req_trans (plus (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                                  (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum))
                                            (plus (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                                  (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum))
                                            (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean))
                                                  (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)))
                                   (req_plus_compat (reqd_list_sum_g (fun i => opp (mult (mult (plus one one) (reward_group i)) req_group_mean)) group_enum)
                                                    (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                                    (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)
                                                    (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)
                                                    Hopp
                                                    (req_refl (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)))
                                   (req_plus_compat (opp (mult (mult (plus one one) (reqd_list_sum_g reward_group group_enum)) req_group_mean))
                                                    (opp (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean))
                                                    (reqd_list_sum_g (fun _ => mult req_group_mean req_group_mean) group_enum)
                                                    (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean))
                                                    Hcross
                                                    Hconst))).
  }
  unfold req_minus.
  exact (req_trans (reqd_list_sum_g (fun i => mult (req_grpo_advantage i) (req_grpo_advantage i)) group_enum)
                   (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                         (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean))
                               (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean))))
                   (plus (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                         (opp (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean))))
           Hl3
           (req_plus_compat (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                            (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum)
                            (plus (opp (mult (mult (plus one one) (mult (reqd_of_nat reqd_group_size) req_group_mean)) req_group_mean))
                                  (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)))
                            (opp (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)))
                            (req_refl (reqd_list_sum_g (fun i => mult (reward_group i) (reward_group i)) group_enum))
                            Hcancel2)).
Qed.

(* Group variance. *)
Definition req_group_variance : R :=
  mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
       req_group_centered_second_moment.

(* inv(G)*(G*x) == x. *)
Lemma req_inv_G_absorb : forall (G : R) (Hg : real_lt zero G) (x : R),
  real_eq (mult (inv_pos G Hg) (mult G x)) x.
Proof.
  intros G Hg x.
  apply (req_trans (mult (inv_pos G Hg) (mult G x))
                   (mult (mult (inv_pos G Hg) G) x) x).
  - apply mult_assoc.
  - apply (req_trans (mult (mult (inv_pos G Hg) G) x) (mult one x) x).
    + exact (req_mult_compat (mult (inv_pos G Hg) G) one x x
                             (req_trans (mult (inv_pos G Hg) G) (mult G (inv_pos G Hg)) one
                                        (mult_comm (inv_pos G Hg) G) (inv_pos_correct G Hg))
                             (req_refl x)).
    + apply (req_trans (mult one x) (mult x one) x (mult_comm one x) (mult_one x)).
Qed.

(* Variance: Var == (1/G)*sum r^2 - mu^2. *)
Theorem req_group_variance_identity :
  real_eq req_group_variance
      (req_minus (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                       req_group_raw_second_moment)
                 (mult req_group_mean req_group_mean)).
Proof.
  unfold req_group_variance.
  apply (req_trans (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                         req_group_centered_second_moment)
                   (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                         (req_minus req_group_raw_second_moment
                                    (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean))))
                   (req_minus (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                                    req_group_raw_second_moment)
                              (mult req_group_mean req_group_mean))).
  - exact (req_mult_compat (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                           (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                           req_group_centered_second_moment
                           (req_minus req_group_raw_second_moment
                                      (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)))
                           (req_refl (inv_pos (reqd_of_nat reqd_group_size) group_size_pos))
                           req_grpo_variance_identity).
  - apply (req_trans (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                           (req_minus req_group_raw_second_moment
                                      (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean))))
                     (req_minus (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                                      req_group_raw_second_moment)
                                (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                                      (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean))))
                     (req_minus (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                                      req_group_raw_second_moment)
                                (mult req_group_mean req_group_mean))).
    + apply req_mult_minus_distr_l.
    + exact (reqd_minus_compat (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                                     req_group_raw_second_moment)
                               (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                                     req_group_raw_second_moment)
                               (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                                     (mult (reqd_of_nat reqd_group_size) (mult req_group_mean req_group_mean)))
                               (mult req_group_mean req_group_mean)
                               (req_refl (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                                               req_group_raw_second_moment))
                               (req_inv_G_absorb (reqd_of_nat reqd_group_size) group_size_pos
                                                 (mult req_group_mean req_group_mean))).
Qed.

(* If 0 <= b then a - b <= a. *)
Lemma req_grpo_le_minus : forall a b : R, real_le zero b -> real_le (req_minus a b) a.
Proof.
  intros a b Hb. unfold req_minus.
  apply (le_id_r (plus a (opp b)) (plus a zero) a).
  - apply plus_zero.
  - apply (le_plus_compat a a (opp b) zero).
    + apply le_refl.
    + apply (le_id_r (opp b) (opp zero) zero).
      * exact reqd_opp_zero.
      * apply (opp_le_compat zero b). exact Hb.
Qed.

(* Var <= (1/G)*sum r^2; [square_nonneg] stays an explicit premise (a constructive ordered field has no trichotomy). *)
Theorem req_group_variance_le_raw_second_moment :
  (forall a : R, real_le zero (mult a a)) ->
  real_le req_group_variance
     (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
           req_group_raw_second_moment).
Proof.
  intros square_nonneg.
  apply (le_id_l req_group_variance
                 (req_minus (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                                  req_group_raw_second_moment)
                            (mult req_group_mean req_group_mean))
                 (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                       req_group_raw_second_moment)).
  - exact req_group_variance_identity.
  - apply (req_grpo_le_minus (mult (inv_pos (reqd_of_nat reqd_group_size) group_size_pos)
                                   req_group_raw_second_moment)
                             (mult req_group_mean req_group_mean)).
    apply square_nonneg.
Qed.

End ReqGRPO.

(* ============================================================ *)
(* Section ReqFEP: free-energy minimization over the setoid summation interface. *)
(* ============================================================ *)
Section ReqFEP.

Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis fsum_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis fsum_add :
  forall f g : S -> R,
    real_eq (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis fsum_linear :
  forall (a : R) (f : S -> R),
    real_eq (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis fsum_pos :
  forall f : S -> R, (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f).
Hypothesis fsum_le :
  forall f g : S -> R, (forall s : S, real_le (f s) (g s)) -> real_le (sumf f) (sumf g).
Hypothesis fsum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, real_le zero (f s)) -> real_eq (sumf f) zero ->
    forall s : S, real_eq (f s) zero.

Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : real_lt zero D.
Variable Z : R.
Hypothesis partition_condition :
  real_eq Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
(* partition_condition, derived from [fsum_pos], pointwise positivity of [exp_neg] and [lt_id_r]; no extra assumptions. *)
Lemma Z_pos : real_lt zero Z.
Proof.
  exact (lt_id_r zero
         (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z
         (req_sym Z (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s))))
                  partition_condition)
         (fsum_pos (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))
                   (fun s : S => exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))))).
Qed.


(* Honest interface bridges: the log tangency statements below are declared as explicit section hypotheses. *)
Hypothesis dist_log_inv_one_inv :
  forall (x : R) (Hx : real_lt zero x) (Hi : real_lt zero (inv_pos x Hx)),
    real_eq (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis dist_log_exp_neg :
  forall u : R, real_eq (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis dist_log_le_linear :
  forall (x : R) (Hx : real_lt zero x), real_le (log x Hx) (req_minus x one).
Hypothesis dist_log_eq_linear :
  forall (x : R) (Hx : real_lt zero x),
    real_eq (log x Hx) (req_minus x one) -> real_eq x one.

(* Section-local definitions; log-carrying definitions take the positivity premise [positive_dist]. *)
Definition reqd_positive_dist (p : S -> R) : Set := forall s : S, real_lt zero (p s).
Definition reqd_normalized (p : S -> R) : Set := real_eq (sumf p) one.
Definition reqd_boltzmann_dist : S -> R :=
  fun s => mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).
Definition reqd_free_energy (p : S -> R) (Hp : reqd_positive_dist p) : R :=
  plus (sumf (fun s => mult (p s) (base_loss s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition req_relative_entropy (p q : S -> R) (Hp : reqd_positive_dist p) (Hq : reqd_positive_dist q) : R :=
  sumf (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))).
Definition reqd_entropy_dist (p : S -> R) (Hp : reqd_positive_dist p) : R :=
  sumf (fun s => mult (p s) (opp (log (p s) (Hp s)))).
Definition reqd_energy_expectation (p : S -> R) : R :=
  sumf (fun s => mult (p s) (base_loss s)).
Definition reqd_cross_entropy (p q : S -> R) (Hq : reqd_positive_dist q) : R :=
  sumf (fun s => mult (p s) (opp (log (q s) (Hq s)))).
Definition reqd_elbo (q : S -> R) (Hq : reqd_positive_dist q) : R := opp (reqd_free_energy q Hq).

Lemma req_boltzmann_positive : forall s : S, real_lt zero (reqd_boltzmann_dist s).
Proof.
  intro s. unfold reqd_boltzmann_dist.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Defined.

Definition reqd_evidence : R := opp (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive).

(* Section-local helper: sum of the pointwise opposite equals the opposite of the sum. *)
Lemma fsum_opp :
  forall f : S -> R, real_eq (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (fsum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply (req_opp_compat (f s) (mult one (f s))).
      exact (req_sym (mult one (f s)) (f s) (req_mult_one_l (f s))).
    + apply (req_sym (mult (opp one) (f s)) (opp (mult one (f s)))).
      apply req_opp_mult_r.
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f)) (opp (sumf f))).
    + apply (fsum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f)) (opp (mult one (sumf f))) (opp (sumf f))).
      * apply req_opp_mult_r.
      * apply (req_opp_compat (mult one (sumf f)) (sumf f)).
        apply req_mult_one_l.
Qed.

(* Section-local helper: sums split under pointwise subtraction. *)
Lemma fsum_minus :
  forall f g : S -> R,
    real_eq (sumf (fun s => req_minus (f s) (g s))) (req_minus (sumf f) (sumf g)).
Proof.
  intros f g. unfold req_minus.
  apply (req_trans (sumf (fun s => plus (f s) (opp (g s))))
                   (plus (sumf f) (sumf (fun s => opp (g s))))
                   (plus (sumf f) (opp (sumf g)))).
  - apply fsum_add.
  - exact (req_plus_compat (sumf f) (sumf f)
                           (sumf (fun s => opp (g s))) (opp (sumf g))
                           (req_refl (sumf f)) (fsum_opp g)).
Qed.

(* Boltzmann normalization over a finite type. *)
Theorem req_boltzmann_normalized : reqd_normalized reqd_boltzmann_dist.
Proof.
  apply (req_trans (sumf reqd_boltzmann_dist)
                   (mult (inv_pos Z Z_pos)
                         (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                   one).
  - exact (fsum_linear (inv_pos Z Z_pos)
                       (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
  - apply (req_trans (mult (inv_pos Z Z_pos)
                           (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                     (mult (inv_pos Z Z_pos) Z) one).
    + apply (req_mult_compat (inv_pos Z Z_pos) (inv_pos Z Z_pos)
                             (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
      * apply req_refl.
      * exact (req_sym Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))))
                        partition_condition).
    + apply (req_trans (mult (inv_pos Z Z_pos) Z) (mult Z (inv_pos Z Z_pos)) one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.

(* Normalization of the convex combination alpha*p + (1-alpha)*q. *)
Theorem req_boltzmann_mix_normalized :
  forall (p q : S -> R) (alpha : R) (Halpha : real_lt zero alpha)
         (Halpha1 : real_lt zero (req_minus one alpha)),
    reqd_normalized p -> reqd_normalized q ->
    real_eq (sumf (fun s => plus (mult alpha (p s)) (mult (req_minus one alpha) (q s)))) one.
Proof.
  intros p q alpha Halpha Halpha1 Hp Hq.
  apply (req_trans (sumf (fun s => plus (mult alpha (p s)) (mult (req_minus one alpha) (q s))))
                   (plus (sumf (fun s => mult alpha (p s)))
                         (sumf (fun s => mult (req_minus one alpha) (q s))))
                   one).
  - apply fsum_add.
  - apply (req_trans (plus (sumf (fun s => mult alpha (p s)))
                           (sumf (fun s => mult (req_minus one alpha) (q s))))
                     (plus (mult alpha (sumf p)) (mult (req_minus one alpha) (sumf q)))
                     one).
    + exact (req_plus_compat _ _ _ _ (fsum_linear alpha p)
                                     (fsum_linear (req_minus one alpha) q)).
    + apply (req_trans (plus (mult alpha (sumf p)) (mult (req_minus one alpha) (sumf q)))
                       (plus (mult alpha one) (mult (req_minus one alpha) one))
                       one).
      * exact (req_plus_compat _ _ _ _
                               (req_mult_compat alpha alpha (sumf p) one
                                                (req_refl alpha) Hp)
                               (req_mult_compat (req_minus one alpha) (req_minus one alpha)
                                                (sumf q) one (req_refl (req_minus one alpha)) Hq)).
      * apply (req_trans (plus (mult alpha one) (mult (req_minus one alpha) one))
                         (plus alpha (req_minus one alpha)) one).
        -- exact (req_plus_compat (mult alpha one) alpha
                                  (mult (req_minus one alpha) one) (req_minus one alpha)
                                  (mult_one alpha)
                                  (mult_one (req_minus one alpha))).
        -- apply (req_trans (plus alpha (req_minus one alpha)) (plus one (plus alpha (opp alpha))) one).
           apply (req_trans (plus alpha (plus one (opp alpha)))
                            (plus (plus alpha one) (opp alpha))
                            (plus one (plus alpha (opp alpha)))).
           ++ apply plus_assoc.
           ++ apply (req_trans (plus (plus alpha one) (opp alpha))
                               (plus (plus one alpha) (opp alpha))
                               (plus one (plus alpha (opp alpha)))).
              ** exact (req_plus_compat (plus alpha one) (plus one alpha) (opp alpha) (opp alpha)
                                        (plus_comm alpha one) (req_refl (opp alpha))).
              ** apply (req_sym (plus one (plus alpha (opp alpha)))
                                (plus (plus one alpha) (opp alpha))).
                 apply plus_assoc.
           ++ apply (req_trans (plus one (plus alpha (opp alpha))) (plus one zero) one).
              ** exact (req_plus_compat one one (plus alpha (opp alpha)) zero
                                        (req_refl one) (plus_opp alpha)).
              ** apply (req_trans (plus one zero) one one
                                  (plus_zero one) (req_refl one)).
Qed.


Theorem req_boltzmann_log_decomp :
  forall s : S,
    real_eq (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))
        (plus (opp (log Z Z_pos)) (opp (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  intro s. unfold reqd_boltzmann_dist, req_boltzmann_positive.
  assert (Hlm : real_eq (log (mult (inv_pos Z Z_pos)
                              (exp_neg (mult (inv_pos D D_pos) (base_loss s))))
                        (mult_positive (inv_pos Z Z_pos)
                                       (exp_neg (mult (inv_pos D D_pos) (base_loss s)))
                                       (inv_pos_pos Z Z_pos)
                                       (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))
                    (plus (log (inv_pos Z Z_pos) (inv_pos_pos Z Z_pos))
                          (log (exp_neg (mult (inv_pos D D_pos) (base_loss s)))
                               (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))).
  { apply log_mult. }
  apply (req_trans _ _ _ Hlm (req_plus_compat (log (inv_pos Z Z_pos) (inv_pos_pos Z Z_pos))
                                              (opp (log Z Z_pos))
                                              (log (exp_neg (mult (inv_pos D D_pos) (base_loss s)))
                                                   (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))))
                                              (opp (mult (inv_pos D D_pos) (base_loss s)))
                                              (dist_log_inv_one_inv Z Z_pos (inv_pos_pos Z Z_pos))
                                              (dist_log_exp_neg (mult (inv_pos D D_pos) (base_loss s))))).
Qed.


Lemma reqd_log_div :
  forall (a b : R) (Ha : real_lt zero a) (Hb : real_lt zero b),
    real_eq (log (mult a (inv_pos b Hb))
              (mult_positive a (inv_pos b Hb) Ha (inv_pos_pos b Hb)))
        (plus (log a Ha) (opp (log b Hb))).
Proof.
  intros a b Ha Hb.
  apply (req_trans (log (mult a (inv_pos b Hb))
                        (mult_positive a (inv_pos b Hb) Ha (inv_pos_pos b Hb)))
                   (plus (log a Ha) (log (inv_pos b Hb) (inv_pos_pos b Hb)))
                   (plus (log a Ha) (opp (log b Hb)))).
  - apply log_mult.
  - exact (req_plus_compat (log a Ha) (log a Ha)
                           (log (inv_pos b Hb) (inv_pos_pos b Hb)) (opp (log b Hb))
                           (req_refl (log a Ha))
                           (dist_log_inv_one_inv b Hb (inv_pos_pos b Hb))).
Qed.


Lemma req_energy_in_log_boltzmann :
  forall s : S,
    real_eq (base_loss s)
        (opp (mult D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))
                           (log Z Z_pos)))).
Proof.
  intro s.
  assert (H2 : real_eq (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))
                   (opp (mult (inv_pos D D_pos) (base_loss s)))).
  { apply (req_trans (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))
                     (plus (plus (opp (log Z Z_pos))
                                 (opp (mult (inv_pos D D_pos) (base_loss s))))
                           (log Z Z_pos))
                     (opp (mult (inv_pos D D_pos) (base_loss s)))).
    - exact (req_plus_compat (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))
                             (plus (opp (log Z Z_pos))
                                   (opp (mult (inv_pos D D_pos) (base_loss s))))
                             (log Z Z_pos) (log Z Z_pos)
                             (req_boltzmann_log_decomp s) (req_refl (log Z Z_pos))).
    - apply (req_trans (plus (plus (opp (log Z Z_pos))
                                   (opp (mult (inv_pos D D_pos) (base_loss s))))
                             (log Z Z_pos))
                       (plus (plus (opp (log Z Z_pos)) (log Z Z_pos))
                             (opp (mult (inv_pos D D_pos) (base_loss s))))
                       (opp (mult (inv_pos D D_pos) (base_loss s)))).
      + apply reqd_plus_rot.
      + apply (req_trans (plus (plus (opp (log Z Z_pos)) (log Z Z_pos))
                               (opp (mult (inv_pos D D_pos) (base_loss s))))
                         (plus zero (opp (mult (inv_pos D D_pos) (base_loss s))))
                         (opp (mult (inv_pos D D_pos) (base_loss s)))).
        * exact (req_plus_compat (plus (opp (log Z Z_pos)) (log Z Z_pos)) zero
                                 (opp (mult (inv_pos D D_pos) (base_loss s)))
                                 (opp (mult (inv_pos D D_pos) (base_loss s)))
                                 (req_trans (plus (opp (log Z Z_pos)) (log Z Z_pos))
                                            (plus (log Z Z_pos) (opp (log Z Z_pos)))
                                            zero
                                            (plus_comm (opp (log Z Z_pos)) (log Z Z_pos))
                                            (plus_opp (log Z Z_pos)))
                                 (req_refl (opp (mult (inv_pos D D_pos) (base_loss s))))).
        * apply req_plus_zero_l. }
  assert (H3 : real_eq (mult D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))
                                 (log Z Z_pos)))
                   (opp (base_loss s))).
  { apply (req_trans (mult D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))
                                   (log Z Z_pos)))
                     (mult D (opp (mult (inv_pos D D_pos) (base_loss s))))
                     (opp (base_loss s))).
    - exact (req_mult_compat D D
                             (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))
                                   (log Z Z_pos))
                             (opp (mult (inv_pos D D_pos) (base_loss s)))
                             (req_refl D) H2).
    - apply (req_trans (mult D (opp (mult (inv_pos D D_pos) (base_loss s))))
                       (opp (mult D (mult (inv_pos D D_pos) (base_loss s))))
                       (opp (base_loss s))).
      + apply req_opp_mult_l.
      + apply (req_opp_compat (mult D (mult (inv_pos D D_pos) (base_loss s))) (base_loss s)).
        exact (req_trans (mult D (mult (inv_pos D D_pos) (base_loss s)))
                         (mult (mult D (inv_pos D D_pos)) (base_loss s))
                         (base_loss s)
                         (mult_assoc D (inv_pos D D_pos) (base_loss s))
                         (req_trans (mult (mult D (inv_pos D D_pos)) (base_loss s))
                                    (mult one (base_loss s))
                                    (base_loss s)
                                    (req_mult_compat (mult D (inv_pos D D_pos)) one
                                                     (base_loss s) (base_loss s)
                                                     (inv_pos_correct D D_pos)
                                                     (req_refl (base_loss s)))
                                    (req_trans (mult one (base_loss s))
                                               (mult (base_loss s) one)
                                               (base_loss s)
                                               (mult_comm one (base_loss s))
                                               (mult_one (base_loss s))))).
  }
  apply (req_trans (base_loss s) (opp (opp (base_loss s)))
                   (opp (mult D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))
                                      (log Z Z_pos))))).
  - apply (req_sym (opp (opp (base_loss s))) (base_loss s)). apply req_double_neg.
  - exact (req_opp_compat (opp (base_loss s))
                          (mult D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))
                                        (log Z Z_pos)))
                          (req_sym _ _ H3)).
Qed.


Lemma fsum_pb_logZ :
  real_eq (sumf (fun s => mult (reqd_boltzmann_dist s) (log Z Z_pos))) (log Z Z_pos).
Proof.
  apply (req_trans (sumf (fun s => mult (reqd_boltzmann_dist s) (log Z Z_pos)))
                   (sumf (fun s => mult (log Z Z_pos) (reqd_boltzmann_dist s)))
                   (log Z Z_pos)).
  - apply (fsum_ext (fun s => mult (reqd_boltzmann_dist s) (log Z Z_pos))
                    (fun s => mult (log Z Z_pos) (reqd_boltzmann_dist s))).
    intro s. apply mult_comm.
  - apply (req_trans (sumf (fun s => mult (log Z Z_pos) (reqd_boltzmann_dist s)))
                     (mult (log Z Z_pos) (sumf reqd_boltzmann_dist)) (log Z Z_pos)).
    + exact (fsum_linear (log Z Z_pos) reqd_boltzmann_dist).
    + apply (req_trans (mult (log Z Z_pos) (sumf reqd_boltzmann_dist))
                       (mult (log Z Z_pos) one) (log Z Z_pos)).
      * exact (req_mult_compat (log Z Z_pos) (log Z Z_pos) (sumf reqd_boltzmann_dist) one
                             (req_refl (log Z Z_pos)) req_boltzmann_normalized).
      * apply (req_trans (mult (log Z Z_pos) one) (mult one (log Z Z_pos)) (log Z Z_pos)
                       (mult_comm (log Z Z_pos) one) (req_mult_one_l (log Z Z_pos))).
Qed.

(* The zero function sums to zero (section-local copy; a cross-section use would need eight explicit parameters). *)
Lemma fsum_zero : real_eq (sumf (fun _ : S => zero)) zero.
Proof.
  apply (req_trans (sumf (fun _ : S => zero))
                   (sumf (fun _ : S => mult zero zero)) zero).
  - apply (fsum_ext (fun _ : S => zero) (fun _ : S => mult zero zero)).
    intro s. apply (req_sym (mult zero zero) zero). apply mult_zero.
  - apply (req_trans (sumf (fun _ : S => mult zero zero))
                     (mult zero (sumf (fun _ : S => zero))) zero).
    + apply (fsum_linear zero (fun _ : S => zero)).
    + exact (req_trans (mult zero (sumf (fun _ : S => zero)))
                       (mult (sumf (fun _ : S => zero)) zero) zero
                       (mult_comm zero (sumf (fun _ : S => zero)))
                       (mult_zero (sumf (fun _ : S => zero)))).
Qed.

(* Normalized-fold general form: sum p*c == c for any constant c. *)
Lemma fsum_norm_const :
  forall (p : S -> R) (c : R), reqd_normalized p ->
    real_eq (sumf (fun s => mult (p s) c)) c.
Proof.
  intros p c Hnp.
  apply (req_trans (sumf (fun s => mult (p s) c))
                   (sumf (fun s => mult c (p s))) c).
  - apply (fsum_ext (fun s => mult (p s) c) (fun s => mult c (p s))).
    intro s. apply mult_comm.
  - apply (req_trans (sumf (fun s => mult c (p s)))
                     (mult c (sumf p)) c).
    + exact (fsum_linear c p).
    + apply (req_trans (mult c (sumf p)) (mult c one) c).
      * exact (req_mult_compat c c (sumf p) one (req_refl c) Hnp).
      * apply (req_trans (mult c one) (mult one c) c
                         (mult_comm c one) (req_mult_one_l c)).
Qed.

(* Free energy of the Boltzmann distribution: F[p_b] == opp (D * log Z). *)
Theorem req_free_energy_boltzmann :
  real_eq (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive)
      (mult (opp D) (log Z Z_pos)).
Proof.
  unfold reqd_free_energy.
  set (Eavg := sumf (fun s => mult (reqd_boltzmann_dist s) (base_loss s))).
  set (A := sumf (fun s => mult (reqd_boltzmann_dist s)
                                (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))).
  
  assert (Hpoint :
    forall s : S,
      real_eq (mult (reqd_boltzmann_dist s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))
          (plus (mult (reqd_boltzmann_dist s) (opp (log Z Z_pos)))
                (opp (mult (inv_pos D D_pos) (mult (reqd_boltzmann_dist s) (base_loss s)))))).
  {
    intro s.
    assert (H1 : real_eq (mult (reqd_boltzmann_dist s)
                           (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))
                     (mult (reqd_boltzmann_dist s)
                           (plus (opp (log Z Z_pos))
                                 (opp (mult (inv_pos D D_pos) (base_loss s))))))
      by exact (req_mult_compat (reqd_boltzmann_dist s) (reqd_boltzmann_dist s)
                                (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))
                                (plus (opp (log Z Z_pos))
                                      (opp (mult (inv_pos D D_pos) (base_loss s))))
                                (req_refl (reqd_boltzmann_dist s))
                                (req_boltzmann_log_decomp s)).
    apply (req_trans _ _ _ H1).
    apply (req_trans (mult (reqd_boltzmann_dist s)
                           (plus (opp (log Z Z_pos))
                                 (opp (mult (inv_pos D D_pos) (base_loss s)))))
                     (plus (mult (reqd_boltzmann_dist s) (opp (log Z Z_pos)))
                           (mult (reqd_boltzmann_dist s)
                                 (opp (mult (inv_pos D D_pos) (base_loss s)))))
                     (plus (mult (reqd_boltzmann_dist s) (opp (log Z Z_pos)))
                           (opp (mult (inv_pos D D_pos)
                                      (mult (reqd_boltzmann_dist s) (base_loss s)))))).
    - apply distrib.
    - apply req_plus_compat.
      + apply req_refl.
      + (* p_b * opp ((1/D)*E) == opp ((1/D)*(p_b*E)): opposite multiplier and regrouping. *)
        apply (req_trans (mult (reqd_boltzmann_dist s)
                               (opp (mult (inv_pos D D_pos) (base_loss s))))
                         (opp (mult (reqd_boltzmann_dist s)
                                    (mult (inv_pos D D_pos) (base_loss s))))
                         (opp (mult (inv_pos D D_pos)
                                    (mult (reqd_boltzmann_dist s) (base_loss s))))).
        * apply req_opp_mult_l.
        * apply (req_opp_compat (mult (reqd_boltzmann_dist s)
                                      (mult (inv_pos D D_pos) (base_loss s)))
                                (mult (inv_pos D D_pos)
                                      (mult (reqd_boltzmann_dist s) (base_loss s)))).
          exact (req_trans (mult (reqd_boltzmann_dist s)
                                 (mult (inv_pos D D_pos) (base_loss s)))
                           (mult (mult (reqd_boltzmann_dist s) (inv_pos D D_pos))
                                 (base_loss s))
                           (mult (inv_pos D D_pos)
                                 (mult (reqd_boltzmann_dist s) (base_loss s)))
                           (mult_assoc (reqd_boltzmann_dist s) (inv_pos D D_pos) (base_loss s))
                           (req_trans (mult (mult (reqd_boltzmann_dist s) (inv_pos D D_pos))
                                            (base_loss s))
                                      (mult (mult (inv_pos D D_pos) (reqd_boltzmann_dist s))
                                            (base_loss s))
                                      (mult (inv_pos D D_pos)
                                            (mult (reqd_boltzmann_dist s) (base_loss s)))
                                      (req_mult_compat (mult (reqd_boltzmann_dist s) (inv_pos D D_pos))
                                                       (mult (inv_pos D D_pos) (reqd_boltzmann_dist s))
                                                       (base_loss s) (base_loss s)
                                                       (mult_comm (reqd_boltzmann_dist s) (inv_pos D D_pos))
                                                       (req_refl (base_loss s)))
                                      (req_sym (mult (inv_pos D D_pos)
                                                     (mult (reqd_boltzmann_dist s) (base_loss s)))
                                               (mult (mult (inv_pos D D_pos) (reqd_boltzmann_dist s))
                                                     (base_loss s))
                                               (mult_assoc (inv_pos D D_pos)
                                                           (reqd_boltzmann_dist s) (base_loss s))))).
  }
  
  assert (Hsum :
    real_eq A (plus (opp (log Z Z_pos)) (opp (mult (inv_pos D D_pos) Eavg)))).
  {
    apply (req_trans A
      (sumf (fun s => plus (mult (reqd_boltzmann_dist s) (opp (log Z Z_pos)))
                           (opp (mult (inv_pos D D_pos)
                                      (mult (reqd_boltzmann_dist s) (base_loss s))))))
      (plus (opp (log Z Z_pos)) (opp (mult (inv_pos D D_pos) Eavg)))).
    - apply (fsum_ext (fun s => mult (reqd_boltzmann_dist s)
                                     (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))
                      (fun s => plus (mult (reqd_boltzmann_dist s) (opp (log Z Z_pos)))
                                     (opp (mult (inv_pos D D_pos)
                                                (mult (reqd_boltzmann_dist s) (base_loss s)))))).
      exact Hpoint.
    - apply (req_trans (sumf (fun s => plus (mult (reqd_boltzmann_dist s) (opp (log Z Z_pos)))
                                            (opp (mult (inv_pos D D_pos)
                                                       (mult (reqd_boltzmann_dist s) (base_loss s))))))
                       (plus (sumf (fun s => mult (reqd_boltzmann_dist s) (opp (log Z Z_pos))))
                             (sumf (fun s => opp (mult (inv_pos D D_pos)
                                                       (mult (reqd_boltzmann_dist s) (base_loss s))))))
                       (plus (opp (log Z Z_pos)) (opp (mult (inv_pos D D_pos) Eavg)))).
      + apply fsum_add.
      + apply req_plus_compat.
        * 
          apply (req_trans (sumf (fun s => mult (reqd_boltzmann_dist s) (opp (log Z Z_pos))))
                           (sumf (fun s => mult (opp (log Z Z_pos)) (reqd_boltzmann_dist s)))
                           (opp (log Z Z_pos))).
          -- apply (fsum_ext (fun s => mult (reqd_boltzmann_dist s) (opp (log Z Z_pos)))
                             (fun s => mult (opp (log Z Z_pos)) (reqd_boltzmann_dist s))).
             intro s. apply mult_comm.
          -- apply (req_trans (sumf (fun s => mult (opp (log Z Z_pos)) (reqd_boltzmann_dist s)))
                              (mult (opp (log Z Z_pos)) (sumf reqd_boltzmann_dist))
                              (opp (log Z Z_pos))).
             ++ apply (fsum_linear (opp (log Z Z_pos)) reqd_boltzmann_dist).
             ++ apply (req_trans (mult (opp (log Z Z_pos)) (sumf reqd_boltzmann_dist))
                                 (mult (opp (log Z Z_pos)) one)
                                 (opp (log Z Z_pos))).
                ** exact (req_mult_compat (opp (log Z Z_pos)) (opp (log Z Z_pos))
                                          (sumf reqd_boltzmann_dist) one
                                          (req_refl (opp (log Z Z_pos)))
                                          req_boltzmann_normalized).
                ** apply (req_trans (mult (opp (log Z Z_pos)) one)
                                    (mult one (opp (log Z Z_pos)))
                                    (opp (log Z Z_pos))
                                    (mult_comm (opp (log Z Z_pos)) one)
                                    (req_mult_one_l (opp (log Z Z_pos)))).
        * (* Σ opp((1/D)·p_b·E) == opp((1/D)·⟨E⟩) *)
          apply (req_trans (sumf (fun s => opp (mult (inv_pos D D_pos)
                                                     (mult (reqd_boltzmann_dist s) (base_loss s)))))
                           (opp (sumf (fun s => mult (inv_pos D D_pos)
                                                      (mult (reqd_boltzmann_dist s) (base_loss s)))))
                           (opp (mult (inv_pos D D_pos) Eavg))).
          -- apply fsum_opp.
          -- exact (req_opp_compat (sumf (fun s => mult (inv_pos D D_pos)
                                                        (mult (reqd_boltzmann_dist s) (base_loss s))))
                                   (mult (inv_pos D D_pos) Eavg)
                                   (fsum_linear (inv_pos D D_pos)
                                                (fun s => mult (reqd_boltzmann_dist s) (base_loss s)))).
  }
  
  assert (Hmd : real_eq (mult D (plus (opp (log Z Z_pos))
                                  (opp (mult (inv_pos D D_pos) Eavg))))
                    (plus (opp (mult D (log Z Z_pos))) (opp Eavg))).
  {
    apply (req_trans (mult D (plus (opp (log Z Z_pos))
                                   (opp (mult (inv_pos D D_pos) Eavg))))
                     (plus (mult D (opp (log Z Z_pos)))
                           (mult D (opp (mult (inv_pos D D_pos) Eavg))))
                     (plus (opp (mult D (log Z Z_pos))) (opp Eavg))).
    - apply distrib.
    - apply req_plus_compat.
      + apply req_opp_mult_l.
      + apply (req_trans (mult D (opp (mult (inv_pos D D_pos) Eavg)))
                         (opp (mult D (mult (inv_pos D D_pos) Eavg))) (opp Eavg)).
        * apply req_opp_mult_l.
        * apply (req_opp_compat (mult D (mult (inv_pos D D_pos) Eavg)) Eavg).
          exact (req_trans (mult D (mult (inv_pos D D_pos) Eavg))
                           (mult (mult D (inv_pos D D_pos)) Eavg) Eavg
                           (mult_assoc D (inv_pos D D_pos) Eavg)
                           (req_trans (mult (mult D (inv_pos D D_pos)) Eavg)
                                      (mult one Eavg) Eavg
                                      (req_mult_compat (mult D (inv_pos D D_pos)) one
                                                       Eavg Eavg
                                                       (inv_pos_correct D D_pos)
                                                       (req_refl Eavg))
                                      (req_trans (mult one Eavg) (mult Eavg one) Eavg
                                                 (mult_comm one Eavg) (mult_one Eavg)))).
  }
  
  assert (Hfin : real_eq (plus Eavg (plus (opp (mult D (log Z Z_pos))) (opp Eavg)))
                    (opp (mult D (log Z Z_pos)))).
  {
    apply (req_trans (plus Eavg (plus (opp (mult D (log Z Z_pos))) (opp Eavg)))
                     (plus (plus Eavg (opp (mult D (log Z Z_pos)))) (opp Eavg))
                     (opp (mult D (log Z Z_pos)))).
    - exact (plus_assoc Eavg (opp (mult D (log Z Z_pos))) (opp Eavg)).
    - apply (req_trans (plus (plus Eavg (opp (mult D (log Z Z_pos)))) (opp Eavg))
                       (plus (plus (opp (mult D (log Z Z_pos))) Eavg) (opp Eavg))
                       (opp (mult D (log Z Z_pos)))).
      + exact (req_plus_compat (plus Eavg (opp (mult D (log Z Z_pos))))
                               (plus (opp (mult D (log Z Z_pos))) Eavg)
                               (opp Eavg) (opp Eavg)
                               (plus_comm Eavg (opp (mult D (log Z Z_pos))))
                               (req_refl (opp Eavg))).
      + apply (req_trans (plus (plus (opp (mult D (log Z Z_pos))) Eavg) (opp Eavg))
                         (plus (opp (mult D (log Z Z_pos))) (plus Eavg (opp Eavg)))
                         (opp (mult D (log Z Z_pos)))).
        * apply (req_sym (plus (opp (mult D (log Z Z_pos))) (plus Eavg (opp Eavg)))
                         (plus (plus (opp (mult D (log Z Z_pos))) Eavg) (opp Eavg))).
          apply plus_assoc.
        * apply (req_trans (plus (opp (mult D (log Z Z_pos))) (plus Eavg (opp Eavg)))
                           (plus (opp (mult D (log Z Z_pos))) zero)
                           (opp (mult D (log Z Z_pos)))).
          -- exact (req_plus_compat (opp (mult D (log Z Z_pos)))
                                    (opp (mult D (log Z Z_pos)))
                                    (plus Eavg (opp Eavg)) zero
                                    (req_refl (opp (mult D (log Z Z_pos))))
                                    (plus_opp Eavg)).
          -- apply plus_zero.
  }
  (* Assembly: substitute the energy average, regroup, and collapse the ring. *)
  apply (req_trans (plus Eavg (mult D A))
                   (plus Eavg (plus (opp (mult D (log Z Z_pos))) (opp Eavg)))
                   (mult (opp D) (log Z Z_pos))).
  - apply (req_trans (plus Eavg (mult D A))
                     (plus Eavg (mult D (plus (opp (log Z Z_pos))
                                              (opp (mult (inv_pos D D_pos) Eavg)))))
                     (plus Eavg (plus (opp (mult D (log Z Z_pos))) (opp Eavg)))).
    + exact (req_plus_compat Eavg Eavg (mult D A)
                             (mult D (plus (opp (log Z Z_pos))
                                           (opp (mult (inv_pos D D_pos) Eavg))))
                             (req_refl Eavg)
                             (req_mult_compat D D A
                                              (plus (opp (log Z Z_pos))
                                                    (opp (mult (inv_pos D D_pos) Eavg)))
                                              (req_refl D) Hsum)).
    + exact (req_plus_compat Eavg Eavg
                             (mult D (plus (opp (log Z Z_pos))
                                           (opp (mult (inv_pos D D_pos) Eavg))))
                             (plus (opp (mult D (log Z Z_pos))) (opp Eavg))
                             (req_refl Eavg) Hmd).
  - exact (req_trans _ _ _ Hfin
                     (req_sym (mult (opp D) (log Z Z_pos))
                              (opp (mult D (log Z Z_pos)))
                              (req_opp_mult_r D (log Z Z_pos)))).
Qed.

(* Pointwise energy decomposition: p*E == opp (D*p*log p_b) - D*p*log Z; first step of the KL decomposition. *)
Lemma req_p_times_energy_decomp :
  forall (p : S -> R) (s : S),
    real_eq (mult (p s) (base_loss s))
        (plus (opp (mult D (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))
              (opp (mult D (mult (p s) (log Z Z_pos))))).
Proof.
  intros p s.
  set (Lp := log (reqd_boltzmann_dist s) (req_boltzmann_positive s)).
  set (Lz := log Z Z_pos).
  set (E := base_loss s).
  set (ps := p s).
  assert (He : real_eq E (opp (mult D (plus Lp Lz))))
    by exact (req_energy_in_log_boltzmann s).
  (* Associativity-commutativity rearrangement of the scaling factors. *)
  assert (Hsw : real_eq (mult ps (mult D (plus Lp Lz)))
                    (mult D (mult ps (plus Lp Lz)))).
  { apply (req_trans (mult ps (mult D (plus Lp Lz)))
                     (mult (mult ps D) (plus Lp Lz))
                     (mult D (mult ps (plus Lp Lz)))).
    - apply mult_assoc.
    - apply (req_trans (mult (mult ps D) (plus Lp Lz))
                       (mult (mult D ps) (plus Lp Lz))
                       (mult D (mult ps (plus Lp Lz)))).
      + exact (req_mult_compat (mult ps D) (mult D ps) (plus Lp Lz) (plus Lp Lz)
                               (mult_comm ps D) (req_refl (plus Lp Lz))).
      + apply (req_sym (mult D (mult ps (plus Lp Lz)))
                       (mult (mult D ps) (plus Lp Lz))). apply mult_assoc. }
  (* Right distributivity of D over the pointwise log sum. *)
  assert (Hdi : real_eq (mult D (mult ps (plus Lp Lz)))
                    (plus (mult D (mult ps Lp)) (mult D (mult ps Lz)))).
  { exact (req_trans _ _ _ (req_mult_compat D D (mult ps (plus Lp Lz))
                                            (plus (mult ps Lp) (mult ps Lz))
                                            (req_refl D) (distrib ps Lp Lz))
                           (distrib D (mult ps Lp) (mult ps Lz))). }
  (* Hop : opp(ps·(D·(Lp+Lz))) == opp(D·(ps·Lp)) + opp(D·(ps·Lz)) *)
  assert (Hop : real_eq (opp (mult ps (mult D (plus Lp Lz))))
                    (plus (opp (mult D (mult ps Lp))) (opp (mult D (mult ps Lz))))).
  { apply (req_trans (opp (mult ps (mult D (plus Lp Lz))))
                     (opp (plus (mult D (mult ps Lp)) (mult D (mult ps Lz))))
                     (plus (opp (mult D (mult ps Lp))) (opp (mult D (mult ps Lz))))).
    - apply (req_opp_compat (mult ps (mult D (plus Lp Lz)))
                            (plus (mult D (mult ps Lp)) (mult D (mult ps Lz)))).
      exact (req_trans _ _ _ Hsw Hdi).
    - apply req_opp_plus. }
  (* Assembly of the energy-side chain. *)
  apply (req_trans (mult ps E)
                   (opp (mult ps (mult D (plus Lp Lz))))
                   (plus (opp (mult D (mult ps Lp))) (opp (mult D (mult ps Lz))))).
  - apply (req_trans (mult ps E)
                     (mult ps (opp (mult D (plus Lp Lz))))
                     (opp (mult ps (mult D (plus Lp Lz))))).
    + exact (req_mult_compat ps ps E (opp (mult D (plus Lp Lz))) (req_refl ps) He).
    + apply req_opp_mult_l.
  - exact Hop.
Qed.

(* ============================================================ *)
(* Training-inference closure: F[p] == F[p_b] + D * KL(p || p_b). *)
(* ============================================================ *)
Theorem req_free_energy_kl_decomp :
  forall (p : S -> R) (Hp : reqd_positive_dist p), reqd_normalized p ->
    real_eq (reqd_free_energy p Hp)
        (plus (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive)
              (mult D (sumf (fun s => mult (p s)
                                           (req_minus (log (p s) (Hp s))
                                                      (log (reqd_boltzmann_dist s)
                                                             (req_boltzmann_positive s))))))).
Proof.
  intros p Hp Hnp.
  unfold reqd_free_energy.
  set (Eavg := sumf (fun s => mult (p s) (base_loss s))).
  set (A := sumf (fun s => mult (p s) (log (p s) (Hp s)))).
  set (B := sumf (fun s => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))).
  set (KL := sumf (fun s => mult (p s)
                                 (req_minus (log (p s) (Hp s))
                                            (log (reqd_boltzmann_dist s)
                                                   (req_boltzmann_positive s))))).
  
  assert (Hse : real_eq Eavg (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))).
  {
    apply (req_trans Eavg
      (sumf (fun s => plus (opp (mult D (mult (p s) (log (reqd_boltzmann_dist s)
                                                            (req_boltzmann_positive s)))))
                           (opp (mult D (mult (p s) (log Z Z_pos))))))
      (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))).
    - apply (fsum_ext (fun s => mult (p s) (base_loss s))
                      (fun s => plus (opp (mult D (mult (p s) (log (reqd_boltzmann_dist s)
                                                                        (req_boltzmann_positive s)))))
                                     (opp (mult D (mult (p s) (log Z Z_pos)))))).
      intro s. exact (req_p_times_energy_decomp p s).
    - apply (req_trans (sumf (fun s => plus (opp (mult D (mult (p s) (log (reqd_boltzmann_dist s)
                                                                        (req_boltzmann_positive s)))))
                                            (opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (sumf (fun s => opp (mult D (mult (p s)
                                                               (log (reqd_boltzmann_dist s)
                                                                       (req_boltzmann_positive s))))))
                             (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))).
      + apply fsum_add.
      + apply req_plus_compat.
        * apply (req_trans (sumf (fun s => opp (mult D (mult (p s)
                                                             (log (reqd_boltzmann_dist s)
                                                                     (req_boltzmann_positive s))))))
                           (opp (sumf (fun s => mult D (mult (p s)
                                                             (log (reqd_boltzmann_dist s)
                                                                     (req_boltzmann_positive s))))))
                           (opp (mult D B))).
          -- apply fsum_opp.
          -- exact (req_opp_compat (sumf (fun s => mult D (mult (p s)
                                                                (log (reqd_boltzmann_dist s)
                                                                        (req_boltzmann_positive s)))))
                                   (mult D B)
                                   (fsum_linear D (fun s => mult (p s)
                                                                 (log (reqd_boltzmann_dist s)
                                                                         (req_boltzmann_positive s))))).
        * apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                           (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                           (opp (mult D (log Z Z_pos)))).
          -- apply fsum_opp.
          -- apply (req_trans (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                              (opp (mult D (sumf (fun s => mult (p s) (log Z Z_pos)))))
                              (opp (mult D (log Z Z_pos)))).
             ++ exact (req_opp_compat (sumf (fun s => mult D (mult (p s) (log Z Z_pos))))
                                      (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))
                                      (fsum_linear D (fun s => mult (p s) (log Z Z_pos)))).
             ++ exact (req_opp_compat (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))
                                      (mult D (log Z Z_pos))
                                      (req_mult_compat D D
                                                       (sumf (fun s => mult (p s) (log Z Z_pos)))
                                                       (log Z Z_pos) (req_refl D)
                                                       (fsum_norm_const p (log Z Z_pos) Hnp))).
  }
  (* Step 2: KL == A - B, via pointwise distribution of multiplication over subtraction and sum extensionality. *)
  assert (Hkl : real_eq KL (req_minus A B)).
  {
    apply (req_trans KL
                     (sumf (fun s => req_minus (mult (p s) (log (p s) (Hp s)))
                                               (mult (p s) (log (reqd_boltzmann_dist s)
                                                                (req_boltzmann_positive s)))))
                     (req_minus A B)).
    - apply (fsum_ext (fun s => mult (p s)
                                     (req_minus (log (p s) (Hp s))
                                                (log (reqd_boltzmann_dist s)
                                                       (req_boltzmann_positive s))))
                      (fun s => req_minus (mult (p s) (log (p s) (Hp s)))
                                          (mult (p s) (log (reqd_boltzmann_dist s)
                                                           (req_boltzmann_positive s))))).
      intro s. exact (req_mult_minus_distr_l (p s) (log (p s) (Hp s))
                                             (log (reqd_boltzmann_dist s)
                                                    (req_boltzmann_positive s))).
    - exact (fsum_minus (fun s => mult (p s) (log (p s) (Hp s)))
                        (fun s => mult (p s) (log (reqd_boltzmann_dist s)
                                                 (req_boltzmann_positive s)))).
  }
  (* Step 3: regroup Eavg + D*A into opp (D*logZ) + D*KL, aligning with the right-hand side plus F_b (D*KL). *)
  assert (HDkl : real_eq (mult D KL)
                     (plus (mult D A) (opp (mult D B)))).
  { exact (req_trans _ _ _
           (req_mult_compat D D KL (req_minus A B) (req_refl D) Hkl)
           (req_mult_minus_distr_l D A B)). }
  assert (Hmain : real_eq (plus Eavg (mult D A))
                      (plus (mult (opp D) (log Z Z_pos)) (mult D KL))).
  {
    apply (req_trans (plus Eavg (mult D A))
                     (plus (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))
                           (mult D A))
                     (plus (mult (opp D) (log Z Z_pos)) (mult D KL))).
    - exact (req_plus_compat Eavg (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))
                             (mult D A) (mult D A) Hse (req_refl (mult D A))).
    - (* (x + y) + z == y + (z + x) with x := -D*B, y := -D*logZ, z := D*A. *)
      apply (req_trans (plus (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))
                             (mult D A))
                       (plus (opp (mult D (log Z Z_pos)))
                             (plus (mult D A) (opp (mult D B))))
                       (plus (mult (opp D) (log Z Z_pos)) (mult D KL))).
      + apply (req_trans (plus (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))
                               (mult D A))
                         (plus (plus (opp (mult D (log Z Z_pos))) (opp (mult D B)))
                               (mult D A))
                         (plus (opp (mult D (log Z Z_pos)))
                               (plus (mult D A) (opp (mult D B))))).
        * exact (req_plus_compat (plus (opp (mult D B)) (opp (mult D (log Z Z_pos))))
                                 (plus (opp (mult D (log Z Z_pos))) (opp (mult D B)))
                                 (mult D A) (mult D A)
                                 (plus_comm (opp (mult D B)) (opp (mult D (log Z Z_pos))))
                                 (req_refl (mult D A))).
        * apply (req_trans (plus (plus (opp (mult D (log Z Z_pos))) (opp (mult D B)))
                                 (mult D A))
                           (plus (opp (mult D (log Z Z_pos)))
                                 (plus (opp (mult D B)) (mult D A)))
                           (plus (opp (mult D (log Z Z_pos)))
                                 (plus (mult D A) (opp (mult D B))))).
          -- apply (req_sym (plus (opp (mult D (log Z Z_pos)))
                                  (plus (opp (mult D B)) (mult D A)))
                            (plus (plus (opp (mult D (log Z Z_pos))) (opp (mult D B)))
                                  (mult D A))).
             apply plus_assoc.
          -- exact (req_plus_compat (opp (mult D (log Z Z_pos)))
                                    (opp (mult D (log Z Z_pos)))
                                    (plus (opp (mult D B)) (mult D A))
                                    (plus (mult D A) (opp (mult D B)))
                                    (req_refl (opp (mult D (log Z Z_pos))))
                                    (plus_comm (opp (mult D B)) (mult D A))).
      + exact (req_plus_compat (opp (mult D (log Z Z_pos)))
                               (mult (opp D) (log Z Z_pos))
                               (plus (mult D A) (opp (mult D B))) (mult D KL)
                               (req_sym (mult (opp D) (log Z Z_pos))
                                        (opp (mult D (log Z Z_pos)))
                                        (req_opp_mult_r D (log Z Z_pos)))
                               (req_sym _ _ HDkl)).
  }
  exact (req_trans _ _ _ Hmain
           (req_plus_compat (mult (opp D) (log Z Z_pos))
                            (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive)
                            (mult D KL) (mult D KL)
                            (req_sym (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive)
                                     (mult (opp D) (log Z Z_pos))
                                     req_free_energy_boltzmann)
                            (req_refl (mult D KL)))).
Qed.
(* Difference form: F[p] - F[p_b] == D * KL(p || p_b). *)
Theorem req_free_energy_kl_diff :
  forall (p : S -> R) (Hp : reqd_positive_dist p), reqd_normalized p ->
    real_eq (req_minus (reqd_free_energy p Hp)
                   (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive))
        (mult D (sumf (fun s => mult (p s)
                                     (req_minus (log (p s) (Hp s))
                                                (log (reqd_boltzmann_dist s)
                                                       (req_boltzmann_positive s)))))).
Proof.
  intros p Hp Hnp. unfold req_minus.
  assert (Hdec := req_free_energy_kl_decomp p Hp Hnp).
  apply (req_trans (plus (reqd_free_energy p Hp)
                         (opp (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive)))
                   (plus (plus (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive)
                               (mult D (sumf (fun s => mult (p s)
                                                            (req_minus (log (p s) (Hp s))
                                                                       (log (reqd_boltzmann_dist s)
                                                                              (req_boltzmann_positive s)))))))
                         (opp (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive)))
                   (mult D (sumf (fun s => mult (p s)
                                                (req_minus (log (p s) (Hp s))
                                                           (log (reqd_boltzmann_dist s)
                                                                  (req_boltzmann_positive s))))))).
  - exact (req_plus_compat (reqd_free_energy p Hp)
                           (plus (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive)
                                 (mult D (sumf (fun s => mult (p s)
                                                              (req_minus (log (p s) (Hp s))
                                                                         (log (reqd_boltzmann_dist s)
                                                                                (req_boltzmann_positive s)))))))
                           (opp (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive))
                           (opp (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive))
                           Hdec (req_refl (opp (reqd_free_energy reqd_boltzmann_dist
                                                            req_boltzmann_positive)))).
  - set (Fb := reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive).
    set (KL := sumf (fun s => mult (p s)
                                   (req_minus (log (p s) (Hp s))
                                              (log (reqd_boltzmann_dist s)
                                                     (req_boltzmann_positive s))))).
    apply (req_trans (plus (plus Fb (mult D KL)) (opp Fb))
                     (plus Fb (plus (mult D KL) (opp Fb))) (mult D KL)).
    + apply (req_sym (plus Fb (plus (mult D KL) (opp Fb)))
                     (plus (plus Fb (mult D KL)) (opp Fb))).
      apply plus_assoc.
    + apply (req_trans (plus Fb (plus (mult D KL) (opp Fb)))
                       (plus (plus Fb (opp Fb)) (mult D KL))
                       (mult D KL)).
      * apply (req_trans (plus Fb (plus (mult D KL) (opp Fb)))
                         (plus Fb (plus (opp Fb) (mult D KL)))
                         (plus (plus Fb (opp Fb)) (mult D KL))).
        -- exact (req_plus_compat Fb Fb (plus (mult D KL) (opp Fb))
                                  (plus (opp Fb) (mult D KL))
                                  (req_refl Fb) (plus_comm (mult D KL) (opp Fb))).
        -- apply plus_assoc.
      * apply (req_trans (plus (plus Fb (opp Fb)) (mult D KL))
                         (plus zero (mult D KL)) (mult D KL)).
        -- exact (req_plus_compat (plus Fb (opp Fb)) zero (mult D KL) (mult D KL)
                                  (plus_opp Fb) (req_refl (mult D KL))).
        -- exact (req_trans (plus zero (mult D KL)) (plus (mult D KL) zero) (mult D KL)
                            (plus_comm zero (mult D KL)) (plus_zero (mult D KL))).
Qed.

(* Difference form: F[p] - F[q] == D*(KL(p||p_b) - KL(q||p_b)). *)
Theorem req_free_energy_diff_kl :
  forall (p q : S -> R) (Hp : reqd_positive_dist p) (Hq : reqd_positive_dist q),
    reqd_normalized p -> reqd_normalized q ->
    real_eq (req_minus (reqd_free_energy p Hp) (reqd_free_energy q Hq))
        (mult D (req_minus
                   (sumf (fun s => mult (p s)
                                        (req_minus (log (p s) (Hp s))
                                                   (log (reqd_boltzmann_dist s)
                                                          (req_boltzmann_positive s)))))
                   (sumf (fun s => mult (q s)
                                        (req_minus (log (q s) (Hq s))
                                                   (log (reqd_boltzmann_dist s)
                                                          (req_boltzmann_positive s))))))).
Proof.
  intros p q Hp Hq Hnp Hnq.
  set (Fb := reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive).
  set (KLp := sumf (fun s => mult (p s)
                                  (req_minus (log (p s) (Hp s))
                                             (log (reqd_boltzmann_dist s)
                                                    (req_boltzmann_positive s))))).
  set (KLq := sumf (fun s => mult (q s)
                                  (req_minus (log (q s) (Hq s))
                                             (log (reqd_boltzmann_dist s)
                                                    (req_boltzmann_positive s))))).
  apply (req_trans (req_minus (reqd_free_energy p Hp) (reqd_free_energy q Hq))
                   (req_minus (plus Fb (mult D KLp)) (plus Fb (mult D KLq)))
                   (mult D (req_minus KLp KLq))).
  - exact (reqd_minus_compat (reqd_free_energy p Hp) (plus Fb (mult D KLp))
                             (reqd_free_energy q Hq) (plus Fb (mult D KLq))
                             (req_free_energy_kl_decomp p Hp Hnp)
                             (req_free_energy_kl_decomp q Hq Hnq)).
  - apply (req_trans (req_minus (plus Fb (mult D KLp)) (plus Fb (mult D KLq)))
                     (req_minus (mult D KLp) (mult D KLq))
                     (mult D (req_minus KLp KLq))).
    + exact (req_minus_plus_congr_l Fb (mult D KLp) (mult D KLq)).
    + exact (req_sym _ _ (req_mult_minus_distr_l D KLp KLq)).
Qed.

(* Self-relative entropy vanishes: KL(p||p) == 0; no assumptions beyond the section interface. *)
Lemma req_relative_entropy_self_zero :
  forall (p : S -> R) (Hp : reqd_positive_dist p),
    real_eq (req_relative_entropy p p Hp Hp) zero.
Proof.
  intros p Hp. unfold req_relative_entropy.
  apply (req_trans (sumf (fun s => mult (p s)
                                        (req_minus (log (p s) (Hp s)) (log (p s) (Hp s)))))
                   (sumf (fun _ : S => zero)) zero).
  - apply (fsum_ext (fun s => mult (p s)
                                   (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))))
                    (fun _ : S => zero)).
    intro s.
    apply (req_trans (mult (p s) (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))))
                     (mult (p s) zero) zero).
    + exact (req_mult_compat (p s) (p s)
                             (req_minus (log (p s) (Hp s)) (log (p s) (Hp s))) zero
                             (req_refl (p s))
                             (req_minus_self_zero (log (p s) (Hp s)) (log (p s) (Hp s))
                                                  (req_refl (log (p s) (Hp s))))).
    + apply mult_zero.
  - exact fsum_zero.
Qed.


Lemma req_entropy_neg_sum :
  forall (p : S -> R) (Hp : reqd_positive_dist p),
    real_eq (sumf (fun s => mult (p s) (log (p s) (Hp s))))
        (opp (reqd_entropy_dist p Hp)).
Proof.
  intros p Hp. unfold reqd_entropy_dist.
  apply (req_trans (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                   (sumf (fun s => opp (mult (p s) (opp (log (p s) (Hp s))))))
                   (opp (sumf (fun s => mult (p s) (opp (log (p s) (Hp s))))))).
  - apply (fsum_ext (fun s => mult (p s) (log (p s) (Hp s)))
                    (fun s => opp (mult (p s) (opp (log (p s) (Hp s)))))).
    intro s.
    apply (req_trans (mult (p s) (log (p s) (Hp s)))
                     (opp (opp (mult (p s) (log (p s) (Hp s)))))
                     (opp (mult (p s) (opp (log (p s) (Hp s)))))).
    + apply (req_sym (opp (opp (mult (p s) (log (p s) (Hp s)))))
                     (mult (p s) (log (p s) (Hp s)))).
      apply req_double_neg.
    + apply (req_opp_compat (opp (mult (p s) (log (p s) (Hp s))))
                            (mult (p s) (opp (log (p s) (Hp s))))).
      exact (req_sym (mult (p s) (opp (log (p s) (Hp s))))
                     (opp (mult (p s) (log (p s) (Hp s))))
                     (req_opp_mult_l (p s) (log (p s) (Hp s)))).
  - apply fsum_opp.
Qed.

(* Free energy versus entropy: F[p] == <E>_p - D * S[p]; unconditional. *)
Lemma req_free_energy_entropy :
  forall (p : S -> R) (Hp : reqd_positive_dist p),
    real_eq (reqd_free_energy p Hp)
        (plus (reqd_energy_expectation p) (mult D (opp (reqd_entropy_dist p Hp)))).
Proof.
  intros p Hp.
  unfold reqd_free_energy, reqd_energy_expectation.
  exact (req_plus_compat (sumf (fun s => mult (p s) (base_loss s)))
                         (sumf (fun s => mult (p s) (base_loss s)))
                         (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                         (mult D (opp (reqd_entropy_dist p Hp)))
                         (req_refl (sumf (fun s => mult (p s) (base_loss s))))
                         (req_mult_compat D D
                                          (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                                          (opp (reqd_entropy_dist p Hp))
                                          (req_refl D) (req_entropy_neg_sum p Hp))).
Qed.
(* Gibbs-cluster algebra helpers, exported for the equality case. *)

(* Fractional cancellation: x*(y*inv x) == y. *)
Lemma reqd_p_times_ratio :
  forall (x y : R) (Hx : real_lt zero x), real_eq (mult x (mult y (inv_pos x Hx))) y.
Proof.
  intros x y Hx.
  apply (req_trans (mult x (mult y (inv_pos x Hx)))
                   (mult y (mult x (inv_pos x Hx)))
                   y).
  - apply (req_trans (mult x (mult y (inv_pos x Hx)))
                     (mult (mult x y) (inv_pos x Hx))
                     (mult y (mult x (inv_pos x Hx)))).
    + exact (mult_assoc x y (inv_pos x Hx)).
    + apply (req_trans (mult (mult x y) (inv_pos x Hx))
                       (mult (mult y x) (inv_pos x Hx))
                       (mult y (mult x (inv_pos x Hx)))).
      * exact (req_mult_compat (mult x y) (mult y x)
                               (inv_pos x Hx) (inv_pos x Hx)
                               (mult_comm x y) (req_refl (inv_pos x Hx))).
      * exact (req_sym (mult y (mult x (inv_pos x Hx)))
                       (mult (mult y x) (inv_pos x Hx))
                       (mult_assoc y x (inv_pos x Hx))).
  - exact (req_trans (mult y (mult x (inv_pos x Hx)))
                     (mult y one) y
                     (req_mult_compat y y (mult x (inv_pos x Hx)) one
                                      (req_refl y) (inv_pos_correct x Hx))
                     (mult_one y)).
Qed.

(* x*(1 - y/x) == x - y. *)
Lemma reqd_p_minus_ratio :
  forall (x y : R) (Hx : real_lt zero x),
    real_eq (mult x (req_minus one (mult y (inv_pos x Hx)))) (req_minus x y).
Proof.
  intros x y Hx.
  apply (req_trans (mult x (req_minus one (mult y (inv_pos x Hx))))
                   (plus (mult x one) (mult x (opp (mult y (inv_pos x Hx)))))
                   (req_minus x y)).
  - exact (distrib x one (opp (mult y (inv_pos x Hx)))).
  - apply (req_trans (plus (mult x one) (mult x (opp (mult y (inv_pos x Hx)))))
                     (plus x (opp (mult x (mult y (inv_pos x Hx)))))
                     (req_minus x y)).
    + exact (req_plus_compat (mult x one) x
                             (mult x (opp (mult y (inv_pos x Hx))))
                             (opp (mult x (mult y (inv_pos x Hx))))
                             (mult_one x)
                             (req_opp_mult_l x (mult y (inv_pos x Hx)))).
    + apply (req_trans (plus x (opp (mult x (mult y (inv_pos x Hx)))))
                       (plus x (opp y))
                       (req_minus x y)).
      * exact (req_plus_compat x x
                               (opp (mult x (mult y (inv_pos x Hx))))
                               (opp y)
                               (req_refl x)
                               (req_opp_compat (mult x (mult y (inv_pos x Hx))) y
                                               (reqd_p_times_ratio x y Hx))).
      * apply req_refl.
Qed.

(* 1 - R == opp (R - 1): reshaping at the tangent equality point. *)
Lemma reqd_minus_one_flip :
  forall a : R, real_eq (req_minus one a) (opp (req_minus a one)).
Proof.
  intro a.
  apply (req_trans (req_minus one a)
                   (plus (opp a) one)
                   (opp (req_minus a one))).
  - exact (req_trans (req_minus one a) (plus one (opp a)) (plus (opp a) one)
                     (req_refl (plus one (opp a))) (plus_comm one (opp a))).
  - exact (req_sym _ _ (req_opp_minus a one)).
Qed.

(* Pointwise Gibbs bound: p - q <= p*(log p - log q). *)
Lemma req_gibbs_pointwise :
  forall (p q : S -> R) (s : S) (Hps : real_lt zero (p s)) (Hqs : real_lt zero (q s)),
    real_le (req_minus (p s) (q s))
       (mult (p s) (req_minus (log (p s) (Hps)) (log (q s) (Hqs)))).
Proof.
  intros p q s Hps Hqs.
  set (Rqp := mult (q s) (inv_pos (p s) Hps)).
  set (Hr := mult_positive (q s) (inv_pos (p s) Hps) Hqs (inv_pos_pos (p s) Hps)).
  assert (Hlin : real_le (log Rqp Hr) (req_minus Rqp one))
    by exact (dist_log_le_linear Rqp Hr).
  assert (Hopp : real_le (opp (req_minus Rqp one)) (opp (log Rqp Hr)))
    by exact (opp_le_compat (log Rqp Hr) (req_minus Rqp one) Hlin).
  
  assert (Hjoin : real_eq (req_minus (log (p s) Hps) (log (q s) Hqs))
                      (opp (log Rqp Hr))).
  { apply (req_trans (req_minus (log (p s) Hps) (log (q s) Hqs))
                     (opp (plus (log (q s) Hqs) (opp (log (p s) Hps))))
                     (opp (log Rqp Hr))).
    - apply (req_trans (req_minus (log (p s) Hps) (log (q s) Hqs))
                       (plus (opp (log (q s) Hqs)) (log (p s) Hps))
                       (opp (plus (log (q s) Hqs) (opp (log (p s) Hps))))).
      + apply (req_trans (req_minus (log (p s) Hps) (log (q s) Hqs))
                         (plus (log (p s) Hps) (opp (log (q s) Hqs)))
                         (plus (opp (log (q s) Hqs)) (log (p s) Hps))).
        * exact (req_refl (plus (log (p s) Hps) (opp (log (q s) Hqs)))).
        * apply plus_comm.
      + exact (req_sym _ _ (req_opp_minus (log (q s) Hqs) (log (p s) Hps))).
    - exact (req_opp_compat (plus (log (q s) Hqs) (opp (log (p s) Hps)))
                            (log Rqp Hr)
                            (req_sym _ _ (reqd_log_div (q s) (p s) Hqs Hps))). }
  assert (Hlhsform : real_eq (mult (p s) (req_minus one Rqp)) (req_minus (p s) (q s)))
    by exact (reqd_p_minus_ratio (p s) (q s) Hps).
  (* Left multiplication by p > 0 preserves the order. *)
  assert (Hml : real_le (mult (p s) (req_minus one Rqp)) (mult (p s) (opp (log Rqp Hr)))).
  { apply (le_id_l (mult (p s) (req_minus one Rqp))
                   (mult (p s) (opp (req_minus Rqp one)))
                   (mult (p s) (opp (log Rqp Hr)))).
    - exact (req_mult_compat (p s) (p s) (req_minus one Rqp) (opp (req_minus Rqp one))
                             (req_refl (p s)) (reqd_minus_one_flip Rqp)).
    - exact (req_le_mult_compat_r (p s) (opp (req_minus Rqp one)) (opp (log Rqp Hr))
                                  (lt_le_iff zero (p s) (inl Hps)) Hopp). }
  exact (le_id_l (req_minus (p s) (q s))
                 (mult (p s) (req_minus one Rqp))
                 (mult (p s) (req_minus (log (p s) Hps) (log (q s) Hqs)))
                 (req_sym _ _ Hlhsform)
                 (le_id_r (mult (p s) (req_minus one Rqp))
                          (mult (p s) (opp (log Rqp Hr)))
                          (mult (p s) (req_minus (log (p s) Hps) (log (q s) Hqs)))
                          (req_sym _ _ (req_mult_compat (p s) (p s)
                                                        (req_minus (log (p s) Hps) (log (q s) Hqs))
                                                        (opp (log Rqp Hr))
                                                        (req_refl (p s)) Hjoin))
                          Hml)).
Qed.

(* Gibbs inequality: the KL of a normalized positive distribution is nonnegative. *)
Theorem req_gibbs_inequality :
  forall (p q : S -> R) (Hp : reqd_positive_dist p) (Hq : reqd_positive_dist q),
    reqd_normalized p -> reqd_normalized q ->
    real_le zero (req_relative_entropy p q Hp Hq).
Proof.
  intros p q Hp Hq Hnp Hnq. unfold req_relative_entropy.
  assert (Hpt : forall s : S,
                  real_le (req_minus (p s) (q s))
                     (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
    by (intro s; exact (req_gibbs_pointwise p q s (Hp s) (Hq s))).
  assert (Hle : real_le (sumf (fun s => req_minus (p s) (q s)))
                   (sumf (fun s => mult (p s)
                                        (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))))
    by exact (fsum_le _ _ Hpt).
  assert (Hsum0 : real_eq (sumf (fun s => req_minus (p s) (q s))) zero).
  { exact (req_trans _ _ _ (fsum_minus p q)
                           (req_minus_self_zero (sumf p) (sumf q)
                                                (req_trans _ _ _ Hnp (req_sym _ _ Hnq)))). }
  exact (le_id_l zero (sumf (fun s => req_minus (p s) (q s)))
                    (sumf (fun s => mult (p s)
                                         (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
                    (req_sym _ _ Hsum0) Hle).
Qed.

(* Equality case: KL(p||q) == 0 implies p == q pointwise, via the log tangency uniqueness bridge. *)
Theorem req_gibbs_equality :
  forall (p q : S -> R) (Hp : reqd_positive_dist p) (Hq : reqd_positive_dist q),
    reqd_normalized p -> reqd_normalized q ->
    real_eq (req_relative_entropy p q Hp Hq) zero ->
    forall s : S, real_eq (p s) (q s).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl0 s0.
  unfold req_relative_entropy in Hkl0.
  set (KLsum := sumf (fun s => mult (p s)
                                    (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))).
  set (S2 := sumf (fun s => req_minus (p s) (q s))).
  assert (Hpq0 : real_eq S2 zero).
  { exact (req_trans _ _ _ (fsum_minus p q)
                           (req_minus_self_zero (sumf p) (sumf q)
                                                (req_trans _ _ _ Hnp (req_sym _ _ Hnq)))). }
  (* Pointwise nonnegativity of d(s). *)
  assert (Hd_nonneg : forall s : S,
            real_le zero (req_minus (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
                               (req_minus (p s) (q s)))).
  { intro s. apply req_le_minus_nonneg.
    exact (req_gibbs_pointwise p q s (Hp s) (Hq s)). }
  (* 2) Σ d == 0 *)
  assert (Hd_sum : real_eq (sumf (fun s => req_minus
                                        (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
                                        (req_minus (p s) (q s)))) zero).
  { apply (req_trans (sumf (fun s => req_minus
                                        (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
                                        (req_minus (p s) (q s))))
                     (req_minus KLsum S2)
                     zero).
    - apply fsum_minus.
    - apply (req_trans (req_minus KLsum S2) (req_minus KLsum zero) zero).
      + exact (reqd_minus_compat KLsum KLsum S2 zero (req_refl KLsum) Hpq0).
      + exact (req_trans _ _ _ (reqd_minus_zero_r KLsum) Hkl0). }
  (* Vanishing: d(s) == 0 pointwise. *)
  assert (Hd0 : forall s : S,
            real_eq (req_minus (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
                           (req_minus (p s) (q s))) zero)
    by exact (fsum_zero_nonneg _ Hd_nonneg Hd_sum).
  
  assert (Hceq : forall s : S,
            real_eq (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
                (req_minus (p s) (q s)))
    by (intro s; exact (req_minus_eq_cancel _ _ (Hd0 s))).
  
  set (Hr := mult_positive (q s0) (inv_pos (p s0) (Hp s0)) (Hq s0)
                           (inv_pos_pos (p s0) (Hp s0))).
  assert (Hcancel_p : real_eq (mult (p s0) (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0))))
                          (mult (p s0) (req_minus one (mult (q s0) (inv_pos (p s0) (Hp s0))))))
    by exact (req_trans _ _ _ (Hceq s0)
                             (req_sym _ _ (reqd_p_minus_ratio (p s0) (q s0) (Hp s0)))).
  assert (Hlm : real_eq (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0)))
                    (req_minus one (mult (q s0) (inv_pos (p s0) (Hp s0)))))
    by exact (req_mult_cancel_l (p s0)
                                (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0)))
                                (req_minus one (mult (q s0) (inv_pos (p s0) (Hp s0))))
                                (Hp s0) Hcancel_p).
  assert (Hlmflip : real_eq (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0)))
                        (opp (req_minus (mult (q s0) (inv_pos (p s0) (Hp s0))) one)))
    by exact (req_trans _ _ _ Hlm
                        (reqd_minus_one_flip (mult (q s0) (inv_pos (p s0) (Hp s0))))).
  
  assert (Hlog_opplm : real_eq (log (mult (q s0) (inv_pos (p s0) (Hp s0))) Hr)
                           (opp (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0))))).
  { apply (req_trans (log (mult (q s0) (inv_pos (p s0) (Hp s0))) Hr)
                     (req_minus (log (q s0) (Hq s0)) (log (p s0) (Hp s0)))
                     (opp (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0))))).
    - exact (reqd_log_div (q s0) (p s0) (Hq s0) (Hp s0)).
    - apply (req_trans (req_minus (log (q s0) (Hq s0)) (log (p s0) (Hp s0)))
                       (plus (log (q s0) (Hq s0)) (opp (log (p s0) (Hp s0))))
                       (opp (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0))))).
      + exact (req_refl (plus (log (q s0) (Hq s0)) (opp (log (p s0) (Hp s0))))).
      + exact (req_trans _ _ _
                         (plus_comm (log (q s0) (Hq s0)) (opp (log (p s0) (Hp s0))))
                         (req_sym _ _ (req_opp_minus (log (p s0) (Hp s0))
                                                     (log (q s0) (Hq s0))))). }
  
  assert (Hlog_eq : real_eq (log (mult (q s0) (inv_pos (p s0) (Hp s0))) Hr)
                        (req_minus (mult (q s0) (inv_pos (p s0) (Hp s0))) one)).
  { apply (req_trans (log (mult (q s0) (inv_pos (p s0) (Hp s0))) Hr)
                     (opp (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0))))
                     (req_minus (mult (q s0) (inv_pos (p s0) (Hp s0))) one)).
    - exact Hlog_opplm.
    - apply (req_trans (opp (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0))))
                       (opp (opp (req_minus (mult (q s0) (inv_pos (p s0) (Hp s0))) one)))
                       (req_minus (mult (q s0) (inv_pos (p s0) (Hp s0))) one)).
      + exact (req_opp_compat (req_minus (log (p s0) (Hp s0)) (log (q s0) (Hq s0)))
                              (opp (req_minus (mult (q s0) (inv_pos (p s0) (Hp s0))) one))
                              Hlmflip).
      + apply req_double_neg. }
  assert (Hratio_one : real_eq (mult (q s0) (inv_pos (p s0) (Hp s0))) one)
    by exact (dist_log_eq_linear (mult (q s0) (inv_pos (p s0) (Hp s0))) Hr Hlog_eq).
  (* q*inv p == p*inv p implies q == p, cancelling the positive factor inv p. *)
  exact (req_sym _ _
           (req_mult_cancel_r (inv_pos (p s0) (Hp s0)) (q s0) (p s0)
                              (inv_pos_pos (p s0) (Hp s0))
                              (req_trans _ _ _ Hratio_one
                                         (req_sym _ _ (inv_pos_correct (p s0) (Hp s0)))))).
Qed.

(* Positivity of the Boltzmann distribution. *)
Lemma req_boltzmann_dist_pos : forall s : S, real_lt zero (reqd_boltzmann_dist s).
Proof.
  intro s. unfold reqd_boltzmann_dist.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

(* ============================================================ *)
(* Free-energy minimization, uniqueness, and the entropy-temperature layer. *)
(*            free_energy_min_unique@16888                    *)
(*            entropy_deficit_kl@16993 max_entropy@17069      *)
(*            entropy_max_unique@17653 cross_entropy_decomp@18094 *)
(* ============================================================ *)

(* The minimum of free energy is attained at the Boltzmann distribution: F[p_b] <= F[p]; unconditional. *)
Theorem req_min_free_energy_is_boltzmann :
  forall (p : S -> R) (Hp : reqd_positive_dist p), reqd_normalized p ->
    real_le (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive) (reqd_free_energy p Hp).
Proof.
  intros p Hp Hnp.
  set (K := req_relative_entropy p reqd_boltzmann_dist Hp req_boltzmann_positive).
  set (FB := reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive).
  (* F[p] == F[p_b] + D*KL: the decomposition identity at the sum level. *)
  assert (Hdecomp : real_eq (reqd_free_energy p Hp) (plus FB (mult D K)))
    by exact (req_free_energy_kl_decomp p Hp Hnp).
  (* KL >= 0 by [req_gibbs_inequality]. *)
  assert (Hkl : real_le zero K)
    by exact (req_gibbs_inequality p reqd_boltzmann_dist Hp req_boltzmann_positive
                                Hnp req_boltzmann_normalized).
  (* 3. D > 0 ⟹ 0 ≤ D·KL *)
  assert (Hdkl : real_le zero (mult D K)).
  { apply (le_id_l zero (mult D zero) (mult D K)).
    - exact (req_sym _ _ (req_mult_zero_r D)).
    - apply (req_le_mult_compat_r D zero K).
      + exact (lt_le_iff zero D (inl D_pos)).
      + exact Hkl. }
  (* [le_plus_compat] preserves the left side; the zero term is normalized over real_eq. *)
  assert (Hfin : real_le FB (plus FB (mult D K))).
  { apply (le_id_l FB (plus FB zero) (plus FB (mult D K))).
    - exact (req_sym _ _ (req_plus_zero_r FB)).
    - apply (le_plus_compat FB FB zero (mult D K)).
      + apply le_refl.
      + exact Hdkl. }
  (* Reshape the right side back to F[p]. *)
  exact (le_id_r FB (plus FB (mult D K)) (reqd_free_energy p Hp)
                   (req_sym _ _ Hdecomp) Hfin).
Qed.

(* Uniqueness: F[p] == F[p_b] implies p == p_b pointwise: cancel the sum, cancel the positive factor D, then apply the Gibbs equality case. *)
Theorem req_free_energy_min_unique :
  forall (p : S -> R) (Hp : reqd_positive_dist p), reqd_normalized p ->
    real_eq (reqd_free_energy p Hp) (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive) ->
    forall s : S, real_eq (p s) (reqd_boltzmann_dist s).
Proof.
  intros p Hp Hnp Hfeq s.
  set (K := req_relative_entropy p reqd_boltzmann_dist Hp req_boltzmann_positive).
  set (FB := reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive).
  (* 1. F[p] == F[p_b] + D·KL *)
  assert (Hdecomp : real_eq (reqd_free_energy p Hp) (plus FB (mult D K)))
    by exact (req_free_energy_kl_decomp p Hp Hnp).
  (* 2. F[p_b] + D·KL == F[p_b] ⟹ D·KL == 0 *)
  assert (Hplus : real_eq (plus FB (mult D K)) FB)
    by exact (req_trans _ _ _ (req_sym _ _ Hdecomp) Hfeq).
  assert (Hdkl0 : real_eq (mult D K) zero)
    by exact (req_plus_cancel_zero FB (mult D K) Hplus).
  (* 3. D > 0 ⟹ KL == 0 *)
  assert (Hkl0 : real_eq K zero).
  { apply (req_mult_cancel_l D K zero D_pos).
    exact (req_trans _ _ _ Hdkl0 (req_sym _ _ (req_mult_zero_r D))). }
  (* The Gibbs equality case closes the chain. *)
  exact (req_gibbs_equality p reqd_boltzmann_dist Hp req_boltzmann_positive
                            Hnp req_boltzmann_normalized Hkl0 s).
Qed.

(* Entropy deficit under the same energy constraint: S[p_b] - S[p] == KL(p||p_b). *)
Theorem req_entropy_deficit_kl :
  forall (p : S -> R) (Hp : reqd_positive_dist p), reqd_normalized p ->
    real_eq (reqd_energy_expectation p) (reqd_energy_expectation reqd_boltzmann_dist) ->
    real_eq (req_minus (reqd_entropy_dist reqd_boltzmann_dist req_boltzmann_positive)
                   (reqd_entropy_dist p Hp))
       (req_relative_entropy p reqd_boltzmann_dist Hp req_boltzmann_positive).
Proof.
  intros p Hp Hnp Henergy.
  set (Sp := reqd_entropy_dist p Hp).
  set (Sb := reqd_entropy_dist reqd_boltzmann_dist req_boltzmann_positive).
  set (K := req_relative_entropy p reqd_boltzmann_dist Hp req_boltzmann_positive).
  set (Ep := reqd_energy_expectation p).
  set (Eb := reqd_energy_expectation reqd_boltzmann_dist).
  set (FB0 := reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive).
  (* The three free-energy identities. *)
  assert (Hdecomp : real_eq (reqd_free_energy p Hp) (plus FB0 (mult D K)))
    by exact (req_free_energy_kl_decomp p Hp Hnp).
  assert (Hfe_p : real_eq (reqd_free_energy p Hp) (plus Ep (mult D (opp Sp))))
    by exact (req_free_energy_entropy p Hp).
  assert (Hfe_b : real_eq FB0 (plus Eb (mult D (opp Sb))))
    by exact (req_free_energy_entropy reqd_boltzmann_dist req_boltzmann_positive).
  (* 2. ⟨E⟩_p − D·S[p] == (⟨E⟩_b − D·S[p_b]) + D·KL *)
  assert (Htot : real_eq (plus Ep (mult D (opp Sp)))
                     (plus (plus Eb (mult D (opp Sb))) (mult D K))).
  { exact (req_trans (plus Ep (mult D (opp Sp)))
                     (plus FB0 (mult D K))
                     (plus (plus Eb (mult D (opp Sb))) (mult D K))
                     (req_trans _ _ _ (req_sym _ _ Hfe_p) Hdecomp)
                     (req_plus_compat FB0 (plus Eb (mult D (opp Sb))) (mult D K) (mult D K)
                        Hfe_b (req_refl (mult D K)))). }
  (* Substitute the energy average and cancel on the left. *)
  assert (Hcancel : real_eq (mult D (opp Sp))
                        (plus (mult D (opp Sb)) (mult D K))).
  { apply (req_plus_cancel_l Eb (mult D (opp Sp)) (plus (mult D (opp Sb)) (mult D K))).
    apply (req_trans (plus Eb (mult D (opp Sp)))
                     (plus Ep (mult D (opp Sp)))
                     (plus Eb (plus (mult D (opp Sb)) (mult D K)))).
    - exact (req_plus_compat Eb Ep (mult D (opp Sp)) (mult D (opp Sp))
                             (req_sym _ _ Henergy) (req_refl (mult D (opp Sp)))).
    - exact (req_trans (plus Ep (mult D (opp Sp)))
                       (plus (plus Eb (mult D (opp Sb))) (mult D K))
                       (plus Eb (plus (mult D (opp Sb)) (mult D K)))
                       Htot
                       (req_sym _ _ (plus_assoc Eb (mult D (opp Sb)) (mult D K)))). }
  (* Ring cancellation with D > 0. *)
  exact (req_ring_d_cancel D Sp Sb K D_pos Hcancel).
Qed.

(* Maximum entropy under the same energy constraint: S[p] <= S[p_b]. *)
Theorem req_max_entropy_is_boltzmann :
  forall (p : S -> R) (Hp : reqd_positive_dist p), reqd_normalized p ->
    real_eq (reqd_energy_expectation p) (reqd_energy_expectation reqd_boltzmann_dist) ->
    real_le (reqd_entropy_dist p Hp) (reqd_entropy_dist reqd_boltzmann_dist req_boltzmann_positive).
Proof.
  intros p Hp Hnp Henergy.
  assert (Hdef : real_eq (req_minus (reqd_entropy_dist reqd_boltzmann_dist req_boltzmann_positive)
                                (reqd_entropy_dist p Hp))
                     (req_relative_entropy p reqd_boltzmann_dist Hp req_boltzmann_positive))
    by exact (req_entropy_deficit_kl p Hp Hnp Henergy).
  assert (Hkl : real_le zero (req_relative_entropy p reqd_boltzmann_dist Hp req_boltzmann_positive))
    by exact (req_gibbs_inequality p reqd_boltzmann_dist Hp req_boltzmann_positive
                                   Hnp req_boltzmann_normalized).
  assert (Hnonneg : real_le zero (req_minus (reqd_entropy_dist reqd_boltzmann_dist req_boltzmann_positive)
                                       (reqd_entropy_dist p Hp)))
    by exact (le_id_r zero (req_relative_entropy p reqd_boltzmann_dist Hp req_boltzmann_positive)
                       (req_minus (reqd_entropy_dist reqd_boltzmann_dist req_boltzmann_positive)
                                  (reqd_entropy_dist p Hp))
                       (req_sym _ _ Hdef) Hkl).
  apply (le_id_r (reqd_entropy_dist p Hp)
                 (plus (reqd_entropy_dist p Hp)
                       (req_minus (reqd_entropy_dist reqd_boltzmann_dist req_boltzmann_positive)
                                  (reqd_entropy_dist p Hp)))
                 (reqd_entropy_dist reqd_boltzmann_dist req_boltzmann_positive)).
  - exact (req_minus_plus_cancel (reqd_entropy_dist p Hp)
                                 (reqd_entropy_dist reqd_boltzmann_dist req_boltzmann_positive)).
  - exact (req_le_plus_nonneg_r (reqd_entropy_dist p Hp)
                                (req_minus (reqd_entropy_dist reqd_boltzmann_dist req_boltzmann_positive)
                                           (reqd_entropy_dist p Hp))
                                Hnonneg).
Qed.

(* Entropy uniqueness: same energy and same entropy imply p == p_b pointwise. *)
Theorem req_entropy_max_unique :
  forall (p : S -> R) (Hp : reqd_positive_dist p), reqd_normalized p ->
    real_eq (reqd_energy_expectation p) (reqd_energy_expectation reqd_boltzmann_dist) ->
    real_eq (reqd_entropy_dist p Hp) (reqd_entropy_dist reqd_boltzmann_dist req_boltzmann_positive) ->
    forall s : S, real_eq (p s) (reqd_boltzmann_dist s).
Proof.
  intros p Hp Hnp Henergy Hent s.
  assert (Hdef : real_eq (req_minus (reqd_entropy_dist reqd_boltzmann_dist req_boltzmann_positive)
                                (reqd_entropy_dist p Hp))
                     (req_relative_entropy p reqd_boltzmann_dist Hp req_boltzmann_positive))
    by exact (req_entropy_deficit_kl p Hp Hnp Henergy).
  assert (Hkl0 : real_eq (req_relative_entropy p reqd_boltzmann_dist Hp req_boltzmann_positive) zero).
  { exact (req_trans _ _ _ (req_sym _ _ Hdef)
                           (req_minus_self_zero (reqd_entropy_dist reqd_boltzmann_dist req_boltzmann_positive)
                                                (reqd_entropy_dist p Hp)
                                                (req_sym _ _ Hent))). }
  exact (req_gibbs_equality p reqd_boltzmann_dist Hp req_boltzmann_positive
                            Hnp req_boltzmann_normalized Hkl0 s).
Qed.

(* Cross-entropy decomposition: H(p,q) == S[p] + KL(p||q). *)
Theorem req_cross_entropy_decomp :
  forall (p q : S -> R) (Hp : reqd_positive_dist p) (Hq : reqd_positive_dist q),
    real_eq (reqd_cross_entropy p q Hq)
        (plus (reqd_entropy_dist p Hp) (req_relative_entropy p q Hp Hq)).
Proof.
  intros p q Hp Hq. unfold reqd_cross_entropy, reqd_entropy_dist, req_relative_entropy.
  assert (Hpt : forall s : S,
            real_eq (mult (p s) (opp (log (q s) (Hq s))))
                (plus (mult (p s) (opp (log (p s) (Hp s))))
                      (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))).
  { intro s.
    assert (Hz : real_eq (plus (mult (p s) (opp (log (p s) (Hp s))))
                           (mult (p s) (log (p s) (Hp s)))) zero)
      by exact (req_trans _ _ _
                  (req_plus_compat (mult (p s) (opp (log (p s) (Hp s))))
                                   (opp (mult (p s) (log (p s) (Hp s))))
                                   (mult (p s) (log (p s) (Hp s)))
                                   (mult (p s) (log (p s) (Hp s)))
                                   (req_opp_mult_l (p s) (log (p s) (Hp s)))
                                   (req_refl (mult (p s) (log (p s) (Hp s)))))
                  (req_trans _ _ _
                    (plus_comm (opp (mult (p s) (log (p s) (Hp s))))
                               (mult (p s) (log (p s) (Hp s))))
                    (plus_opp (mult (p s) (log (p s) (Hp s)))))).
    apply (req_sym (plus (mult (p s) (opp (log (p s) (Hp s))))
                         (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
                   (mult (p s) (opp (log (q s) (Hq s))))).
    apply (req_trans (plus (mult (p s) (opp (log (p s) (Hp s))))
                           (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))))
                     (plus (mult (p s) (opp (log (p s) (Hp s))))
                           (plus (mult (p s) (log (p s) (Hp s)))
                                 (mult (p s) (opp (log (q s) (Hq s))))))
                     (mult (p s) (opp (log (q s) (Hq s))))).
    - exact (req_plus_compat (mult (p s) (opp (log (p s) (Hp s))))
                             (mult (p s) (opp (log (p s) (Hp s))))
                             (mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
                             (plus (mult (p s) (log (p s) (Hp s)))
                                   (mult (p s) (opp (log (q s) (Hq s)))))
                             (req_refl (mult (p s) (opp (log (p s) (Hp s)))))
                             (distrib (p s) (log (p s) (Hp s)) (opp (log (q s) (Hq s))))).
    - apply (req_trans (plus (mult (p s) (opp (log (p s) (Hp s))))
                             (plus (mult (p s) (log (p s) (Hp s)))
                                   (mult (p s) (opp (log (q s) (Hq s))))))
                       (plus (plus (mult (p s) (opp (log (p s) (Hp s))))
                                   (mult (p s) (log (p s) (Hp s))))
                             (mult (p s) (opp (log (q s) (Hq s)))))
                       (mult (p s) (opp (log (q s) (Hq s))))).
      + exact (plus_assoc (mult (p s) (opp (log (p s) (Hp s))))
                          (mult (p s) (log (p s) (Hp s)))
                          (mult (p s) (opp (log (q s) (Hq s))))).
      + apply (req_trans (plus (plus (mult (p s) (opp (log (p s) (Hp s))))
                                     (mult (p s) (log (p s) (Hp s))))
                               (mult (p s) (opp (log (q s) (Hq s)))))
                         (plus zero (mult (p s) (opp (log (q s) (Hq s)))))
                         (mult (p s) (opp (log (q s) (Hq s))))).
        * exact (req_plus_compat (plus (mult (p s) (opp (log (p s) (Hp s))))
                                       (mult (p s) (log (p s) (Hp s))))
                                 zero
                                 (mult (p s) (opp (log (q s) (Hq s))))
                                 (mult (p s) (opp (log (q s) (Hq s))))
                                 Hz
                                 (req_refl (mult (p s) (opp (log (q s) (Hq s)))))).
        * exact (req_trans (plus zero (mult (p s) (opp (log (q s) (Hq s)))))
                           (plus (mult (p s) (opp (log (q s) (Hq s)))) zero)
                           (mult (p s) (opp (log (q s) (Hq s))))
                           (plus_comm zero (mult (p s) (opp (log (q s) (Hq s)))))
                           (plus_zero (mult (p s) (opp (log (q s) (Hq s)))))).
  }
  apply (req_trans (sumf (fun s => mult (p s) (opp (log (q s) (Hq s)))))
                   (sumf (fun s => plus (mult (p s) (opp (log (p s) (Hp s))))
                                        (mult (p s) (req_minus (log (p s) (Hp s))
                                                               (log (q s) (Hq s))))))
                   (plus (sumf (fun s => mult (p s) (opp (log (p s) (Hp s)))))
                         (sumf (fun s => mult (p s)
                                              (req_minus (log (p s) (Hp s))
                                                         (log (q s) (Hq s))))))).
  - exact (fsum_ext _ _ Hpt).
  - exact (fsum_add _ _).
Qed.

(* Local helper: cancelling the common summand, minus (A+B) (A+C) == minus B C. *)
Lemma req_minus_plus_common_local : forall A B C : R,
  real_eq (req_minus (plus A B) (plus A C)) (req_minus B C).
Proof.
  intros A B C. unfold req_minus.
  apply (req_trans (plus (plus A B) (opp (plus A C)))
                   (plus (plus A B) (plus (opp A) (opp C)))
                   (plus B (opp C))).
  - exact (req_plus_compat (plus A B) (plus A B)
                           (opp (plus A C)) (plus (opp A) (opp C))
                           (req_refl (plus A B)) (req_opp_plus A C)).
  - apply (req_trans (plus (plus A B) (plus (opp A) (opp C)))
                     (plus (plus A (opp A)) (plus B (opp C)))
                     (plus B (opp C))).
    + exact (req_plus_swap_mid A B (opp A) (opp C)).
    + apply (req_trans (plus (plus A (opp A)) (plus B (opp C)))
                       (plus zero (plus B (opp C)))
                       (plus B (opp C))).
      * exact (req_plus_compat (plus A (opp A)) zero
                               (plus B (opp C)) (plus B (opp C))
                               (plus_opp A) (req_refl (plus B (opp C)))).
      * exact (req_trans (plus zero (plus B (opp C)))
                         (plus (plus B (opp C)) zero)
                         (plus B (opp C))
                         (plus_comm zero (plus B (opp C)))
                         (req_plus_zero_r (plus B (opp C)))).
Qed.

(* H(p,q) - H(p,p) == KL(p||q): the core of the training-objective equivalence. *)
Theorem req_cross_entropy_minus_self :
  forall (p q : S -> R) (Hp : reqd_positive_dist p) (Hq : reqd_positive_dist q),
    real_eq (req_minus (reqd_cross_entropy p q Hq) (reqd_cross_entropy p p Hp))
       (req_relative_entropy p q Hp Hq).
Proof.
  intros p q Hp Hq.
  assert (H1 : real_eq (reqd_cross_entropy p q Hq)
                   (plus (reqd_entropy_dist p Hp) (req_relative_entropy p q Hp Hq)))
    by exact (req_cross_entropy_decomp p q Hp Hq).
  assert (H2 : real_eq (reqd_cross_entropy p p Hp) (reqd_entropy_dist p Hp)).
  { apply (req_trans (reqd_cross_entropy p p Hp)
                     (plus (reqd_entropy_dist p Hp) (req_relative_entropy p p Hp Hp))
                     (reqd_entropy_dist p Hp)).
    - exact (req_cross_entropy_decomp p p Hp Hp).
    - apply (req_trans (plus (reqd_entropy_dist p Hp) (req_relative_entropy p p Hp Hp))
                       (plus (reqd_entropy_dist p Hp) zero)
                       (reqd_entropy_dist p Hp)).
      + exact (req_plus_compat _ _ _ _ (req_refl (reqd_entropy_dist p Hp))
                                      (req_relative_entropy_self_zero p Hp)).
      + exact (req_plus_zero_r (reqd_entropy_dist p Hp)). }
  apply (req_trans (req_minus (reqd_cross_entropy p q Hq) (reqd_cross_entropy p p Hp))
                   (req_minus (plus (reqd_entropy_dist p Hp)
                                    (req_relative_entropy p q Hp Hq))
                              (reqd_entropy_dist p Hp))
                   (req_relative_entropy p q Hp Hq)).
  - exact (reqd_minus_compat (reqd_cross_entropy p q Hq)
                             (plus (reqd_entropy_dist p Hp)
                                   (req_relative_entropy p q Hp Hq))
                             (reqd_cross_entropy p p Hp)
                             (reqd_entropy_dist p Hp)
                             H1 H2).
  - exact (req_minus_plus_cancel_r (reqd_entropy_dist p Hp)
                                   (req_relative_entropy p q Hp Hq)).
Qed.

(* Training equivalence: decreasing cross-entropy decreases KL, for a fixed target p; unconditional. *)
Theorem req_training_equivalence :
  forall (p q1 q2 : S -> R) (Hp : reqd_positive_dist p)
         (Hq1 : reqd_positive_dist q1) (Hq2 : reqd_positive_dist q2),
    real_le (reqd_cross_entropy p q2 Hq2) (reqd_cross_entropy p q1 Hq1) ->
    real_le (req_relative_entropy p q2 Hp Hq2) (req_relative_entropy p q1 Hp Hq1).
Proof.
  intros p q1 q2 Hp Hq1 Hq2 Hce.
  assert (H1d : real_eq (reqd_cross_entropy p q1 Hq1)
                    (plus (reqd_entropy_dist p Hp) (req_relative_entropy p q1 Hp Hq1)))
    by exact (req_cross_entropy_decomp p q1 Hp Hq1).
  assert (H2d : real_eq (reqd_cross_entropy p q2 Hq2)
                    (plus (reqd_entropy_dist p Hp) (req_relative_entropy p q2 Hp Hq2)))
    by exact (req_cross_entropy_decomp p q2 Hp Hq2).
  (* Difference identity: H2 - H1 == KL2 - KL1. *)
  assert (Hdiff : real_eq (req_minus (reqd_cross_entropy p q2 Hq2) (reqd_cross_entropy p q1 Hq1))
                      (req_minus (req_relative_entropy p q2 Hp Hq2)
                                 (req_relative_entropy p q1 Hp Hq1))).
  { apply (req_trans (req_minus (reqd_cross_entropy p q2 Hq2) (reqd_cross_entropy p q1 Hq1))
                     (req_minus (plus (reqd_entropy_dist p Hp) (req_relative_entropy p q2 Hp Hq2))
                                (plus (reqd_entropy_dist p Hp) (req_relative_entropy p q1 Hp Hq1)))
                     (req_minus (req_relative_entropy p q2 Hp Hq2)
                                (req_relative_entropy p q1 Hp Hq1))).
    - exact (reqd_minus_compat _ _ _ _ H2d H1d).
    - exact (req_minus_plus_common_local (reqd_entropy_dist p Hp)
                                         (req_relative_entropy p q2 Hp Hq2)
                                         (req_relative_entropy p q1 Hp Hq1)). }
  (* Symmetric form: H1 - H2 == KL1 - KL2. *)
  assert (Hdiff' : real_eq (req_minus (reqd_cross_entropy p q1 Hq1) (reqd_cross_entropy p q2 Hq2))
                       (req_minus (req_relative_entropy p q1 Hp Hq1)
                                  (req_relative_entropy p q2 Hp Hq2))).
  { apply (req_trans (req_minus (reqd_cross_entropy p q1 Hq1) (reqd_cross_entropy p q2 Hq2))
                     (req_minus (plus (reqd_entropy_dist p Hp) (req_relative_entropy p q1 Hp Hq1))
                                (plus (reqd_entropy_dist p Hp) (req_relative_entropy p q2 Hp Hq2)))
                     (req_minus (req_relative_entropy p q1 Hp Hq1)
                                (req_relative_entropy p q2 Hp Hq2))).
    - exact (reqd_minus_compat _ _ _ _ H1d H2d).
    - exact (req_minus_plus_common_local (reqd_entropy_dist p Hp)
                                         (req_relative_entropy p q1 Hp Hq1)
                                         (req_relative_entropy p q2 Hp Hq2)). }
  assert (Hd : real_le zero (req_minus (reqd_cross_entropy p q1 Hq1) (reqd_cross_entropy p q2 Hq2)))
    by exact (req_le_minus_nonneg (reqd_cross_entropy p q2 Hq2) (reqd_cross_entropy p q1 Hq1) Hce).
  assert (Hd' : real_le zero (req_minus (req_relative_entropy p q1 Hp Hq1)
                                   (req_relative_entropy p q2 Hp Hq2)))
    by exact (le_id_r zero (req_minus (reqd_cross_entropy p q1 Hq1) (reqd_cross_entropy p q2 Hq2))
                       (req_minus (req_relative_entropy p q1 Hp Hq1)
                                  (req_relative_entropy p q2 Hp Hq2))
                       Hdiff' Hd).
  apply (le_id_r (req_relative_entropy p q2 Hp Hq2)
                 (plus (req_relative_entropy p q2 Hp Hq2)
                       (req_minus (req_relative_entropy p q1 Hp Hq1)
                                  (req_relative_entropy p q2 Hp Hq2)))
                 (req_relative_entropy p q1 Hp Hq1)).
  - exact (req_minus_plus_cancel (req_relative_entropy p q2 Hp Hq2)
                                 (req_relative_entropy p q1 Hp Hq1)).
  - exact (req_le_plus_nonneg_r (req_relative_entropy p q2 Hp Hq2)
                                (req_minus (req_relative_entropy p q1 Hp Hq1)
                                           (req_relative_entropy p q2 Hp Hq2))
                                Hd').
Qed.

(* ============================================================ *)
(* The ELBO family. *)
(*          elbo_explicit@18428 elbo_tight@18520               *)
(* ============================================================ *)

(* ELBO lower bound: ELBO(q) <= evidence. *)
Theorem req_elbo_lower_bound :
  forall (q : S -> R) (Hq : reqd_positive_dist q), reqd_normalized q ->
    real_le (reqd_elbo q Hq) reqd_evidence.
Proof.
  intros q Hq Hnq. unfold reqd_elbo, reqd_evidence.
  apply (opp_le_compat (reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive)
                       (reqd_free_energy q Hq)).
  exact (req_min_free_energy_is_boltzmann q Hq Hnq).
Qed.

(* Evidence decomposition: evidence == ELBO(q) + D * KL(q||p_b). *)
Theorem req_evidence_kl_decomp :
  forall (q : S -> R) (Hq : reqd_positive_dist q), reqd_normalized q ->
    real_eq reqd_evidence
        (plus (reqd_elbo q Hq)
              (mult D (req_relative_entropy q reqd_boltzmann_dist Hq req_boltzmann_positive))).
Proof.
  intros q Hq Hnq.
  set (K := req_relative_entropy q reqd_boltzmann_dist Hq req_boltzmann_positive).
  set (Fq := reqd_free_energy q Hq).
  set (FB := reqd_free_energy reqd_boltzmann_dist req_boltzmann_positive).
  unfold reqd_evidence, reqd_elbo.
  assert (Hdecomp : real_eq Fq (plus FB (mult D K)))
    by exact (req_free_energy_kl_decomp q Hq Hnq).
  apply (req_sym (plus (opp Fq) (mult D K)) (opp FB)).
  apply (req_trans (plus (opp Fq) (mult D K))
                   (plus (opp (plus FB (mult D K))) (mult D K))
                   (opp FB)).
  - exact (req_plus_compat (opp Fq) (opp (plus FB (mult D K)))
                           (mult D K) (mult D K)
                           (req_opp_compat Fq (plus FB (mult D K)) Hdecomp)
                           (req_refl (mult D K))).
  - apply (req_trans (plus (opp (plus FB (mult D K))) (mult D K))
                     (plus (plus (opp FB) (opp (mult D K))) (mult D K))
                     (opp FB)).
    + exact (req_plus_compat _ _ _ _ (req_opp_plus FB (mult D K)) (req_refl (mult D K))).
    + apply (req_trans (plus (plus (opp FB) (opp (mult D K))) (mult D K))
                       (plus (opp FB) (plus (opp (mult D K)) (mult D K)))
                       (opp FB)).
      * exact (req_sym _ _ (plus_assoc (opp FB) (opp (mult D K)) (mult D K))).
      * apply (req_trans (plus (opp FB) (plus (opp (mult D K)) (mult D K)))
                         (plus (opp FB) zero)
                         (opp FB)).
        -- exact (req_plus_compat (opp FB) (opp FB)
                                 (plus (opp (mult D K)) (mult D K)) zero
                                 (req_refl (opp FB))
                                 (req_trans (plus (opp (mult D K)) (mult D K))
                                            (plus (mult D K) (opp (mult D K)))
                                            zero
                                            (plus_comm (opp (mult D K)) (mult D K))
                                            (plus_opp (mult D K)))).
        -- exact (req_plus_zero_r (opp FB)).
Qed.

(* Explicit form: -F[q] == -<E>_q + D*S[q]. *)
Theorem req_elbo_explicit :
  forall (q : S -> R) (Hq : reqd_positive_dist q),
    real_eq (reqd_elbo q Hq)
        (plus (opp (reqd_energy_expectation q)) (mult D (reqd_entropy_dist q Hq))).
Proof.
  intro q. intro Hq. unfold reqd_elbo, reqd_free_energy, reqd_energy_expectation.
  assert (Hml : real_eq (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))
                    (opp (mult D (reqd_entropy_dist q Hq)))).
  { apply (req_trans (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))
                     (mult D (opp (reqd_entropy_dist q Hq)))
                     (opp (mult D (reqd_entropy_dist q Hq)))).
    - exact (req_mult_compat D D (sumf (fun s => mult (q s) (log (q s) (Hq s))))
                             (opp (reqd_entropy_dist q Hq))
                             (req_refl D) (req_entropy_neg_sum q Hq)).
    - exact (req_opp_mult_l D (reqd_entropy_dist q Hq)). }
  apply (req_trans (opp (plus (sumf (fun s => mult (q s) (base_loss s)))
                              (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))))
                   (plus (opp (sumf (fun s => mult (q s) (base_loss s))))
                         (opp (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))))
                   (plus (opp (sumf (fun s => mult (q s) (base_loss s))))
                         (mult D (reqd_entropy_dist q Hq)))).
  - exact (req_opp_plus (sumf (fun s => mult (q s) (base_loss s)))
                        (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))).
  - exact (req_plus_compat (opp (sumf (fun s => mult (q s) (base_loss s)))) (opp (sumf (fun s => mult (q s) (base_loss s)))) (opp (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))) (mult D (reqd_entropy_dist q Hq))
                            (req_refl (opp (sumf (fun s => mult (q s) (base_loss s)))))
                            (req_trans (opp (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))) (opp (opp (mult D (reqd_entropy_dist q Hq)))) (mult D (reqd_entropy_dist q Hq))
                                       (req_trans (opp (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s)))))) (opp (mult D (opp (reqd_entropy_dist q Hq)))) (opp (opp (mult D (reqd_entropy_dist q Hq))))
                                                  (req_opp_compat (mult D (sumf (fun s => mult (q s) (log (q s) (Hq s))))) (mult D (opp (reqd_entropy_dist q Hq)))
                                                                  (req_mult_compat D D (sumf (fun s => mult (q s) (log (q s) (Hq s)))) (opp (reqd_entropy_dist q Hq)) (req_refl D)
                                                                                   (req_entropy_neg_sum q Hq)))
                                                  (req_opp_compat (mult D (opp (reqd_entropy_dist q Hq))) (opp (mult D (reqd_entropy_dist q Hq))) (req_opp_mult_l D (reqd_entropy_dist q Hq))))
                                       (req_double_neg (mult D (reqd_entropy_dist q Hq))))).
Qed.

(* Tightness: ELBO[p_b] == evidence (zero gap). *)
Theorem req_elbo_tight :
  real_eq (reqd_elbo reqd_boltzmann_dist req_boltzmann_positive) reqd_evidence.
Proof.
  unfold reqd_elbo, reqd_evidence. apply req_refl.
Qed.
(* Variational gap: evidence - ELBO(q) == D * KL(q||p_b). *)
Theorem req_evidence_gap_kl :
  forall (q : S -> R) (Hq : reqd_positive_dist q), reqd_normalized q ->
    real_eq (req_minus reqd_evidence (reqd_elbo q Hq))
       (mult D (req_relative_entropy q reqd_boltzmann_dist Hq req_boltzmann_positive)).
Proof.
  intros q Hq Hnq.
  apply (req_trans (req_minus reqd_evidence (reqd_elbo q Hq))
                   (req_minus (plus (reqd_elbo q Hq)
                                    (mult D (req_relative_entropy q reqd_boltzmann_dist Hq
                                                                  req_boltzmann_positive)))
                              (reqd_elbo q Hq))
                   (mult D (req_relative_entropy q reqd_boltzmann_dist Hq req_boltzmann_positive))).
  - exact (reqd_minus_compat _ _ _ _
             (req_evidence_kl_decomp q Hq Hnq) (req_refl (reqd_elbo q Hq))).
  - exact (req_minus_plus_cancel_r (reqd_elbo q Hq)
                                   (mult D (req_relative_entropy q reqd_boltzmann_dist Hq
                                                                req_boltzmann_positive))).
Qed.


(* ============================================================ *)
(* Section ReqKLDiv: KL divergence specialized to a fixed reference distribution q. *)
(* ============================================================ *)
Section ReqKLDiv.
Variable qk : S -> R.
Hypothesis qk_pos : forall s : S, real_lt zero (qk s).
Hypothesis qk_norm : reqd_normalized qk.
Definition req_kl_divergence (p : S -> R) (Hp : reqd_positive_dist p) : R :=
  req_relative_entropy p qk Hp qk_pos.

(* Id kl_nonneg @24982 *)
Theorem req_kl_nonneg :
  forall (p : S -> R) (Hp : reqd_positive_dist p), reqd_normalized p ->
    real_le zero (req_kl_divergence p Hp).
Proof.
  intros p Hp Hnp. unfold req_kl_divergence.
  exact (req_gibbs_inequality p qk Hp qk_pos Hnp qk_norm).
Qed.

(* Id kl_zero_iff_eq @24992 *)
Theorem req_kl_zero_iff_eq :
  forall (p : S -> R) (Hp : reqd_positive_dist p), reqd_normalized p ->
    real_eq (req_kl_divergence p Hp) zero -> forall s : S, real_eq (p s) (qk s).
Proof.
  intros p Hp Hnp Hkl0 s. unfold req_kl_divergence in Hkl0.
  exact (req_gibbs_equality p qk Hp qk_pos Hnp qk_norm Hkl0 s).
Qed.
End ReqKLDiv.

(* ============================================================ *)
(* Section ReqTemp: the entropy deficit and maximum-entropy statements in the temperature parametrization. *)

(*   entropy_temp_explicit / relative_entropy_temp_decomp +     *)
(* ============================================================ *)
Section ReqTemp.
Variable Z_temp : R -> R.
Hypothesis Z_temp_spec : forall (t : R) (Ht : real_lt zero t),
  real_eq (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

Lemma req_Z_temp_pos : forall (t : R) (Ht : real_lt zero t), real_lt zero (Z_temp t).
Proof.
  intros t Ht.
  apply (lt_id_r zero (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))) (Z_temp t)
                    (req_sym _ _ (Z_temp_spec t Ht))).
  exact (fsum_pos (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))
                  (fun s => exp_neg_pos (mult (inv_pos t Ht) (base_loss s)))).
Qed.

Definition reqd_boltzmann_dist_temp (t : R) (Ht : real_lt zero t) : S -> R :=
  fun s => mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                (exp_neg (mult (inv_pos t Ht) (base_loss s))).

Definition reqd_energy_exp_temp (t : R) (Ht : real_lt zero t) : R :=
  sumf (fun s => mult (reqd_boltzmann_dist_temp t Ht s) (base_loss s)).

Theorem reqd_boltzmann_dist_temp_normalized :
  forall (t : R) (Ht : real_lt zero t), reqd_normalized (reqd_boltzmann_dist_temp t Ht).
Proof.
  intros t Ht.
  apply (req_trans (sumf (fun s => mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                                        (exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                   (mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                         (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                   one).
  - exact (fsum_linear (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                       (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).
  - apply (req_trans (mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                           (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))))
                     (mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht)) (Z_temp t))
                     one).
    + exact (req_mult_compat (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                             (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                             (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s))))
                             (Z_temp t)
                             (req_refl (inv_pos (Z_temp t) (req_Z_temp_pos t Ht)))
                             (req_sym _ _ (Z_temp_spec t Ht))).
    + apply (req_trans (mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht)) (Z_temp t))
                       (mult (Z_temp t) (inv_pos (Z_temp t) (req_Z_temp_pos t Ht)))
                       one).
      * exact (mult_comm (inv_pos (Z_temp t) (req_Z_temp_pos t Ht)) (Z_temp t)).
      * exact (inv_pos_correct (Z_temp t) (req_Z_temp_pos t Ht)).
Qed.

Lemma reqd_boltzmann_dist_temp_pos :
  forall (t : R) (Ht : real_lt zero t) (s : S), real_lt zero (reqd_boltzmann_dist_temp t Ht s).
Proof.
  intros t Ht s. unfold reqd_boltzmann_dist_temp.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Defined.

(* Boltzmann log at temperature: log p_t(s) == opp (log Z_t) - beta * e_s, via the log-inverse and exp-neg interface bridges. *)
Theorem reqd_boltzmann_log_temp_decomp :
  forall (t : R) (Ht : real_lt zero t) (s : S),
    real_eq (log (reqd_boltzmann_dist_temp t Ht s) (reqd_boltzmann_dist_temp_pos t Ht s))
        (plus (opp (log (Z_temp t) (req_Z_temp_pos t Ht)))
              (opp (mult (inv_pos t Ht) (base_loss s)))).
Proof.
  intros t Ht s.
  unfold reqd_boltzmann_dist_temp, reqd_boltzmann_dist_temp_pos.
  assert (Hlm : real_eq (log (mult (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                               (exp_neg (mult (inv_pos t Ht) (base_loss s))))
                        (mult_positive (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                                       (exp_neg (mult (inv_pos t Ht) (base_loss s)))
                                       (inv_pos_pos (Z_temp t) (req_Z_temp_pos t Ht))
                                       (exp_neg_pos (mult (inv_pos t Ht) (base_loss s)))))
                    (plus (log (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                               (inv_pos_pos (Z_temp t) (req_Z_temp_pos t Ht)))
                          (log (exp_neg (mult (inv_pos t Ht) (base_loss s)))
                               (exp_neg_pos (mult (inv_pos t Ht) (base_loss s)))))).
  { apply log_mult. }
  apply (req_trans _ _ _ Hlm
         (req_plus_compat (log (inv_pos (Z_temp t) (req_Z_temp_pos t Ht))
                               (inv_pos_pos (Z_temp t) (req_Z_temp_pos t Ht)))
                          (opp (log (Z_temp t) (req_Z_temp_pos t Ht)))
                          (log (exp_neg (mult (inv_pos t Ht) (base_loss s)))
                               (exp_neg_pos (mult (inv_pos t Ht) (base_loss s))))
                          (opp (mult (inv_pos t Ht) (base_loss s)))
                          (dist_log_inv_one_inv (Z_temp t) (req_Z_temp_pos t Ht)
                                                (inv_pos_pos (Z_temp t) (req_Z_temp_pos t Ht)))
                          (dist_log_exp_neg (mult (inv_pos t Ht) (base_loss s))))).
Qed.

End ReqTemp.

(* ============================================================ *)
(* Energy-cross-entropy identity. *)


(* ============================================================ *)
Theorem req_energy_cross_entropy :
  forall p : S -> R,
    reqd_normalized p ->
    real_eq (reqd_energy_expectation p)
        (plus (mult D (reqd_cross_entropy p reqd_boltzmann_dist req_boltzmann_positive))
              (opp (mult D (log Z Z_pos)))).
Proof.
  intros p Hnp.
  unfold reqd_energy_expectation, reqd_cross_entropy.
  
  assert (Hpt : forall s : S,
    real_eq (mult (p s) (base_loss s))
        (opp (mult D (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))
                           (mult (p s) (log Z Z_pos)))))).
  { intro s.
    apply (req_trans (mult (p s) (base_loss s))
                     (mult (p s) (opp (mult D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))
                     (opp (mult D (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))).
    - exact (req_mult_compat (p s) (p s) (base_loss s)
               (opp (mult D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))
               (req_refl (p s)) (req_energy_in_log_boltzmann s)).
    - apply (req_trans (mult (p s) (opp (mult D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))
                       (opp (mult (p s) (mult D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))
                       (opp (mult D (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))).
      + exact (req_opp_mult_l (p s) (mult D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))).
      + apply (req_opp_compat (mult (p s) (mult D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))
                              (mult D (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))).
        apply (req_trans (mult (p s) (mult D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))
                         (mult (mult D (p s)) (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))
                         (mult D (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))).
        * apply (req_trans (mult (p s) (mult D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))
                           (mult (mult (p s) D) (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))
                           (mult (mult D (p s)) (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))).
          -- exact (mult_assoc (p s) D (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))).
          -- exact (req_mult_compat (mult (p s) D) (mult D (p s))
                       (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))
                       (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))
                       (mult_comm (p s) D) (req_refl (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))).
        * exact (req_trans (mult (mult D (p s)) (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))
                           (mult D (mult (p s) (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))
                           (mult D (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))
                           (req_sym _ _ (mult_assoc D (p s) (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))
                           (req_mult_compat D D
                              (mult (p s) (plus (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))
                              (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))
                              (req_refl D) (distrib (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))). }
  
  assert (Hsum : real_eq (sumf (fun s : S => mult (p s) (base_loss s)))
                     (opp (mult D (plus (sumf (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))
                                        (sumf (fun s : S => mult (p s) (log Z Z_pos))))))).
  { apply (req_trans (sumf (fun s : S => mult (p s) (base_loss s)))
                     (sumf (fun s : S => opp (mult D (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))))
                     (opp (mult D (plus (sumf (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos))))))).
    - apply (fsum_ext (fun s : S => mult (p s) (base_loss s))
                      (fun s : S => opp (mult D (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))).
      exact Hpt.
    - exact (req_trans (sumf (fun s : S => opp (mult D (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))))
                       (opp (sumf (fun s : S => mult D (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))))
                       (opp (mult D (plus (sumf (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos))))))
                       (fsum_opp (fun s : S => mult D (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))
                       (req_opp_compat (sumf (fun s : S => mult D (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))
                                       (mult D (plus (sumf (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos)))))
                                       (req_trans (sumf (fun s : S => mult D (plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))
                                                  (mult D (sumf (fun s : S => plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))))
                                                  (mult D (plus (sumf (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos)))))
                                                  (fsum_linear D (fun s : S => plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))
                                                  (req_mult_compat D D
                                                     (sumf (fun s : S => plus (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos))))
                                                     (plus (sumf (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos))))
                                                     (req_refl D)
                                                     (fsum_add (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))
                                                              (fun s : S => mult (p s) (log Z Z_pos))))))). }
  
  assert (HA : real_eq (sumf (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))
                   (opp (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))).
  { apply (req_trans (sumf (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))
                     (sumf (fun s : S => opp (mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))
                     (opp (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))).
    - apply (fsum_ext (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))
                      (fun s : S => opp (mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))).
      intro s.
      apply (req_trans (mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))
                       (mult (p s) (opp (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))
                       (opp (mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))).
      + exact (req_mult_compat (p s) (p s)
                 (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))
                 (opp (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))
                 (req_refl (p s))
                 (req_sym _ _ (req_double_neg (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))).
      + exact (req_opp_mult_l (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))).
    - exact (fsum_opp (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))). }
  (* Constant extraction: sum p*logZ == logZ. *)
  assert (HC : real_eq (sumf (fun s : S => mult (p s) (log Z Z_pos))) (log Z Z_pos)).
  { apply (req_trans (sumf (fun s : S => mult (p s) (log Z Z_pos)))
                     (sumf (fun s : S => mult (log Z Z_pos) (p s)))
                     (log Z Z_pos)).
    - apply (fsum_ext (fun s : S => mult (p s) (log Z Z_pos))
                      (fun s : S => mult (log Z Z_pos) (p s))).
      intro s. exact (mult_comm (p s) (log Z Z_pos)).
    - apply (req_trans (sumf (fun s : S => mult (log Z Z_pos) (p s)))
                       (mult (log Z Z_pos) (sumf p))
                       (log Z Z_pos)).
      + exact (fsum_linear (log Z Z_pos) p).
      + apply (req_trans (mult (log Z Z_pos) (sumf p))
                         (mult (log Z Z_pos) one)
                         (log Z Z_pos)).
        * exact (req_mult_compat (log Z Z_pos) (log Z Z_pos) (sumf p) one
                   (req_refl (log Z Z_pos)) Hnp).
        * exact (mult_one (log Z Z_pos)). }
  (* Closing regrouping: opp (D*(opp CE + logZ)) == D*CE + opp (D*logZ). *)
  apply (req_trans (sumf (fun s : S => mult (p s) (base_loss s)))
                   (opp (mult D (plus (opp (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))
                                      (log Z Z_pos))))
                   (plus (mult D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))
                         (opp (mult D (log Z Z_pos))))).
  - exact (req_trans (sumf (fun s : S => mult (p s) (base_loss s)))
                     (opp (mult D (plus (sumf (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos))))))
                     (opp (mult D (plus (opp (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))) (log Z Z_pos))))
                     Hsum
                     (req_opp_compat (mult D (plus (sumf (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos)))))
                                     (mult D (plus (opp (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))) (log Z Z_pos)))
                                     (req_mult_compat D D
                                        (plus (sumf (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))) (sumf (fun s : S => mult (p s) (log Z Z_pos))))
                                        (plus (opp (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))) (log Z Z_pos))
                                        (req_refl D)
                                        (req_plus_compat (sumf (fun s : S => mult (p s) (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))
                                                         (opp (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))
                                                         (sumf (fun s : S => mult (p s) (log Z Z_pos)))
                                                         (log Z Z_pos)
                                                         HA
                                                         HC)))).
  - apply (req_trans (opp (mult D (plus (opp (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))
                                        (log Z Z_pos))))
                     (opp (plus (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))))
                                (mult D (log Z Z_pos))))
                     (plus (mult D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (log Z Z_pos))))).
    + exact (req_opp_compat (mult D (plus (opp (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))) (log Z Z_pos)))
                            (plus (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))))
                                  (mult D (log Z Z_pos)))
                            (req_trans (mult D (plus (opp (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))) (log Z Z_pos)))
                                       (plus (mult D (opp (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))) (mult D (log Z Z_pos)))
                                       (plus (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))) (mult D (log Z Z_pos)))
                                       (distrib D (opp (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))) (log Z Z_pos))
                                       (req_plus_compat (mult D (opp (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))))
                                                        (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))))
                                                        (mult D (log Z Z_pos))
                                                        (mult D (log Z Z_pos))
                                                        (req_opp_mult_l D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))
                                                        (req_refl (mult D (log Z Z_pos)))))).
    + exact (req_trans (opp (plus (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))))
                                  (mult D (log Z Z_pos))))
                       (plus (opp (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))))
                             (opp (mult D (log Z Z_pos))))
                       (plus (mult D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))
                             (opp (mult D (log Z Z_pos))))
                       (req_opp_plus (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))))
                                     (mult D (log Z Z_pos)))
                       (req_plus_compat (opp (opp (mult D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))))
                                        (mult D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s))))))
                                        (opp (mult D (log Z Z_pos)))
                                        (opp (mult D (log Z Z_pos)))
                                        (req_double_neg (mult D (sumf (fun s : S => mult (p s) (opp (log (reqd_boltzmann_dist s) (req_boltzmann_positive s)))))))
                                        (req_refl (opp (mult D (log Z Z_pos)))))).
Qed.

End ReqFEP.

(* ============================================================ *)
(* Standalone sections: Boltzmann steady state, probability distributions, the second law, U2 helpers, square witnesses. *)
(* ============================================================ *)

(* Boltzmann steady state. *)
Section ReqSteadyState.

Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis ssum_ext : forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis ssum_linear : forall (a : R) (f : S -> R), real_eq (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : real_lt zero D.
Variable Z : R.
Variable Z_pos : real_lt zero Z.
Variable transition : S -> S -> R.
Hypothesis transition_normalization : forall s : S, real_eq (sumf (fun s' => transition s s')) one.

Definition reqd_boltzmann_prob (s : S) : R :=
  mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).

Hypothesis detailed_balance :
  forall s s' : S,
    real_eq (mult (reqd_boltzmann_prob s') (transition s' s))
        (mult (reqd_boltzmann_prob s) (transition s s')).

(* Detailed balance implies stationarity. *)
Theorem req_steady_state_boltzmann :
  forall s : S,
    real_eq (sumf (fun s' => mult (reqd_boltzmann_prob s') (transition s' s)))
        (reqd_boltzmann_prob s).
Proof.
  intro s.
  apply (req_trans (sumf (fun s' => mult (reqd_boltzmann_prob s') (transition s' s)))
                   (sumf (fun s' => mult (reqd_boltzmann_prob s) (transition s s')))
                   (reqd_boltzmann_prob s)).
  - exact (ssum_ext (fun s' => mult (reqd_boltzmann_prob s') (transition s' s))
                    (fun s' => mult (reqd_boltzmann_prob s) (transition s s'))
                    (fun s' => detailed_balance s s')).
  - apply (req_trans (sumf (fun s' => mult (reqd_boltzmann_prob s) (transition s s')))
                     (mult (reqd_boltzmann_prob s) (sumf (fun s' => transition s s')))
                     (reqd_boltzmann_prob s)).
    + exact (ssum_linear (reqd_boltzmann_prob s) (fun s' => transition s s')).
    + apply (req_trans (mult (reqd_boltzmann_prob s) (sumf (fun s' => transition s s')))
                       (mult (reqd_boltzmann_prob s) one)
                       (reqd_boltzmann_prob s)).
      * exact (req_mult_compat (reqd_boltzmann_prob s) (reqd_boltzmann_prob s)
                               (sumf (fun s' => transition s s')) one
                               (req_refl (reqd_boltzmann_prob s)) (transition_normalization s)).
      * exact (req_mult_one_r (reqd_boltzmann_prob s)).
Qed.
End ReqSteadyState.

(* Probability distribution properties. *)
Section ReqProbDist.

Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis psum_linear : forall (a : R) (f : S -> R), real_eq (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis psum_add : forall f g : S -> R, real_eq (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).

Definition reqd_is_prob_dist (p : S -> R) : Set :=
  And (forall s : S, real_le zero (p s)) (real_eq (sumf p) one).

(* Id prob_dist_sum_linear @24896 *)
Lemma req_prob_dist_sum_linear :
  forall (p : S -> R), reqd_is_prob_dist p ->
    forall a : R, real_eq (sumf (fun s => mult a (p s))) a.
Proof.
  intros p Hp a. destruct Hp as [Hp_nonneg Hp_norm].
  apply (req_trans (sumf (fun s => mult a (p s))) (mult a (sumf p)) a).
  - exact (psum_linear a p).
  - exact (req_trans _ _ _ (req_mult_compat a a (sumf p) one (req_refl a) Hp_norm)
                           (req_mult_one_r a)).
Qed.

(* The pointwise mixture of two normalized distributions sums to two; the correct mixture is the normalized mean inv_2*(p+q). *)
Theorem req_prob_dist_mix :
  forall p q : S -> R, reqd_is_prob_dist p -> reqd_is_prob_dist q ->
    reqd_is_prob_dist (fun s => mult (inv_pos (plus one one) req_two_pos) (plus (p s) (q s))).
Proof.
  intros p q [Hp_nonneg Hp_norm] [Hq_nonneg Hq_norm]. unfold reqd_is_prob_dist.
  split.
  - intro s.
    assert (Hx : real_le zero (plus (p s) (q s))).
    { apply (le_id_l zero (plus zero zero) (plus (p s) (q s))).
      - exact (req_sym _ _ (req_plus_zero_r zero)).
      - exact (le_plus_compat zero (p s) zero (q s) (Hp_nonneg s) (Hq_nonneg s)). }
    apply (le_trans zero (mult zero (plus (p s) (q s)))
                        (mult (inv_pos (plus one one) req_two_pos) (plus (p s) (q s)))).
    + apply (le_id_l zero (mult zero (plus (p s) (q s))) (mult zero (plus (p s) (q s)))).
      * exact (req_sym _ _ (req_trans _ _ _ (mult_comm zero (plus (p s) (q s)))
                                               (mult_zero (plus (p s) (q s))))).
      * apply le_refl.
    + apply (le_mult_compat_weak zero (inv_pos (plus one one) req_two_pos) (plus (p s) (q s))).
      * exact Hx.
      * exact (lt_le_iff zero (inv_pos (plus one one) req_two_pos)
                             (inl (inv_pos_pos (plus one one) req_two_pos))).
  - apply (req_trans (sumf (fun s => mult (inv_pos (plus one one) req_two_pos) (plus (p s) (q s))))
                     (mult (inv_pos (plus one one) req_two_pos) (sumf (fun s => plus (p s) (q s))))
                     one).
    + exact (psum_linear (inv_pos (plus one one) req_two_pos) (fun s => plus (p s) (q s))).
    + apply (req_trans (mult (inv_pos (plus one one) req_two_pos) (sumf (fun s => plus (p s) (q s))))
                       (mult (inv_pos (plus one one) req_two_pos) (plus (sumf p) (sumf q)))
                       one).
      * exact (req_mult_compat (inv_pos (plus one one) req_two_pos)
                               (inv_pos (plus one one) req_two_pos)
                               (sumf (fun s => plus (p s) (q s))) (plus (sumf p) (sumf q))
                               (req_refl (inv_pos (plus one one) req_two_pos)) (psum_add p q)).
      * apply (req_trans (mult (inv_pos (plus one one) req_two_pos) (plus (sumf p) (sumf q)))
                         (mult (inv_pos (plus one one) req_two_pos) (plus one one))
                         one).
        -- exact (req_mult_compat (inv_pos (plus one one) req_two_pos)
                                 (inv_pos (plus one one) req_two_pos)
                                 (plus (sumf p) (sumf q)) (plus one one)
                                 (req_refl (inv_pos (plus one one) req_two_pos))
                                 (req_plus_compat (sumf p) one (sumf q) one Hp_norm Hq_norm)).
        -- exact (req_trans _ _ _ (mult_comm (inv_pos (plus one one) req_two_pos) (plus one one))
                                  (inv_pos_correct (plus one one) req_two_pos)).
Qed.
End ReqProbDist.

(* Second-law section; the statement carries the postulate in Not (real_eq ..) form. *)
Section ReqSecondLaw.

Variable entropy : R -> R.
Variable dynamics : R -> R.
Definition reqd_entropy_increases : Set :=
  forall x, real_le (entropy x) (entropy (dynamics x)).
(* The irreversibility statement is an honest model assumption: the abstract dynamics and entropy fields have no interface characterization, so Not (real_eq (dynamics x) x) is declared as an explicit premise rather than derived. *)
Variable strict_entropy_increase :
  forall x, Not (real_eq (dynamics x) x) -> real_lt (entropy x) (entropy (dynamics x)).
Theorem req_second_law_irreversible :
  forall x, Not (real_eq (dynamics x) x) -> real_lt (entropy x) (entropy (dynamics x)).
Proof.
  intros x Hneq. apply strict_entropy_increase. exact Hneq.
Qed.
End ReqSecondLaw.

(* U2 fixed-point helpers. *)
Section ReqU2Aux.

(* Helper A: two nonnegative summands with zero sum are each zero. *)
Lemma req_u2_nonneg_sum_zero : forall a b : R,
  real_le zero a -> real_le zero b -> real_eq (plus a b) zero -> real_eq a zero.
Proof.
  intros a b Ha Hb Habs.
  assert (H1 : real_le a (plus a b)) by exact (req_le_plus_nonneg_r a b Hb).
  assert (H2 : real_le a zero) by exact (le_id_r a (plus a b) zero Habs H1).
  exact (req_sym _ _ (le_antisym zero a Ha H2)).
Qed.

(* Helper C: (a - b) - a == opp b. *)
Lemma req_u2_minus_minus : forall a b : R,
  real_eq (req_minus (req_minus a b) a) (opp b).
Proof.
  intros a b. unfold req_minus.
  apply (req_trans (plus (plus a (opp b)) (opp a))
                   (plus a (plus (opp b) (opp a)))
                   (opp b)).
  - exact (req_sym _ _ (plus_assoc a (opp b) (opp a))).
  - apply (req_trans (plus a (plus (opp b) (opp a)))
                     (plus a (plus (opp a) (opp b)))
                     (opp b)).
    + exact (req_plus_compat a a (plus (opp b) (opp a)) (plus (opp a) (opp b))
                             (req_refl a) (plus_comm (opp b) (opp a))).
    + apply (req_trans (plus a (plus (opp a) (opp b)))
                       (plus (plus a (opp a)) (opp b))
                       (opp b)).
      * exact (plus_assoc a (opp a) (opp b)).
      * apply (req_trans (plus (plus a (opp a)) (opp b))
                         (plus zero (opp b))
                         (opp b)).
        -- exact (req_plus_compat (plus a (opp a)) zero (opp b) (opp b)
                                  (plus_opp a) (req_refl (opp b))).
        -- exact (req_trans _ _ _ (plus_comm zero (opp b)) (plus_zero (opp b))).
Qed.
End ReqU2Aux.

(* Square witness, general form: the nat embedding built over the setoid operations. *)
Section ReqSqrtWitness.

Fixpoint reqd_nat_to_R (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S n' => plus one (reqd_nat_to_R n')
  end.

(* Additive homomorphism. *)
Lemma reqd_nat_to_R_plus_hom : forall m n : nat,
  real_eq (reqd_nat_to_R (m + n)%nat) (plus (reqd_nat_to_R m) (reqd_nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - cbn [reqd_nat_to_R Nat.add Nat.mul]. exact (req_sym _ _ (req_trans _ _ _ (plus_comm zero (reqd_nat_to_R n))
                                               (plus_zero (reqd_nat_to_R n)))).
  - cbn [reqd_nat_to_R Nat.add Nat.mul]. exact (req_trans _ _ _ (req_plus_compat one one (reqd_nat_to_R (m + n)%nat)
                                                          (plus (reqd_nat_to_R m) (reqd_nat_to_R n))
                                                          (req_refl one) IH)
                                  (plus_assoc one (reqd_nat_to_R m) (reqd_nat_to_R n))).
Qed.

(* Multiplicative homomorphism. *)
Lemma reqd_nat_to_R_mult_hom : forall m n : nat,
  real_eq (reqd_nat_to_R (m * n)%nat) (mult (reqd_nat_to_R m) (reqd_nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - cbn [reqd_nat_to_R Nat.add Nat.mul]. exact (req_sym _ _ (req_trans _ _ _ (mult_comm zero (reqd_nat_to_R n))
                                               (mult_zero (reqd_nat_to_R n)))).
  - cbn [reqd_nat_to_R Nat.add Nat.mul].
    exact (req_trans _ _ _ (reqd_nat_to_R_plus_hom n (m * n)%nat)
           (req_trans _ _ _ (req_plus_compat (reqd_nat_to_R n) (reqd_nat_to_R n)
                                             (reqd_nat_to_R (m * n)%nat)
                                             (mult (reqd_nat_to_R m) (reqd_nat_to_R n))
                                             (req_refl (reqd_nat_to_R n)) IH)
           (req_trans _ _ _ (req_plus_compat (reqd_nat_to_R n) (mult (reqd_nat_to_R n) one)
                                             (mult (reqd_nat_to_R m) (reqd_nat_to_R n))
                                             (mult (reqd_nat_to_R n) (reqd_nat_to_R m))
                                             (req_sym _ _ (req_mult_one_r (reqd_nat_to_R n)))
                                             (mult_comm (reqd_nat_to_R m) (reqd_nat_to_R n)))
           (req_trans _ _ _ (req_sym _ _ (distrib (reqd_nat_to_R n) one (reqd_nat_to_R m)))
                            (mult_comm (reqd_nat_to_R n) (plus one (reqd_nat_to_R m))))))).
Qed.

(* Strict positivity: k >= 1 implies 0 < nat embedding. *)
Lemma reqd_nat_to_R_pos : forall k : nat, real_lt zero (reqd_nat_to_R (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - cbn [reqd_nat_to_R Nat.add Nat.mul]. exact (lt_id_r zero one (plus one zero) (req_sym _ _ (req_plus_zero_r one)) one_pos).
  - cbn [reqd_nat_to_R Nat.add Nat.mul]. exact (plus_positive one (reqd_nat_to_R (Datatypes.S k)) one_pos IH).
Qed.

Definition reqd_sqrt_witness (d r : R) : Set := real_eq (mult r r) d.

(* Literal witness: d := r*r. *)
Lemma reqd_sqrt_witness_sq : forall k : nat,
  reqd_sqrt_witness (mult (reqd_nat_to_R k) (reqd_nat_to_R k)) (reqd_nat_to_R k).
Proof. intro k. unfold reqd_sqrt_witness. apply req_refl. Qed.

(* Nontrivial witness: d := nat (k*k), via the multiplicative homomorphism. *)
Lemma reqd_sqrt_witness_nat_sq : forall k : nat,
  reqd_sqrt_witness (reqd_nat_to_R (k * k)%nat) (reqd_nat_to_R k).
Proof. intro k. unfold reqd_sqrt_witness. exact (req_sym _ _ (reqd_nat_to_R_mult_hom k k)). Qed.
End ReqSqrtWitness.


(* ============================================================ *)
(* Section ReqAlgBridge2: order-cancellation laws and the softmax scaling-temperature duality. *)
(* ============================================================ *)
Section ReqAlgBridge2.


(* Right additive cancellation for real_le. *)
Lemma req_le_plus_cancel_l : forall a b c : R,
  real_le (plus a c) (plus b c) -> real_le a b.
Proof.
  intros a b c H.
  (* Identity: x == (x+c) + opp c. *)
  assert (Hdec : forall x : R, real_eq x (plus (plus x c) (opp c))).
  { intro x.
    apply (req_trans x (plus x zero) (plus (plus x c) (opp c))).
    - exact (req_sym _ _ (req_plus_zero_r x)).
    - apply (req_trans (plus x zero) (plus x (plus c (opp c)))
                       (plus (plus x c) (opp c))).
      + exact (req_plus_compat x x zero (plus c (opp c)) (req_refl x)
                               (req_sym _ _ (plus_opp c))).
      + exact (plus_assoc x c (opp c)). }
  apply (le_id_l a (plus (plus a c) (opp c)) b (Hdec a)).
  apply (le_id_r (plus (plus a c) (opp c)) (plus (plus b c) (opp c)) b).
  - exact (req_sym _ _ (Hdec b)).
  - exact (le_plus_compat (plus a c) (plus b c) (opp c) (opp c) H
                          (le_refl (opp c))).
Qed.

(* Converse of subtraction nonnegativity. *)
Lemma req_le_minus_nonneg_rev : forall a b : R,
  real_le (req_minus a b) zero -> real_le a b.
Proof.
  intros a b H.
  (* a == (a-b) + b. *)
  assert (Ha : real_eq a (plus (req_minus a b) b)).
  { apply (req_trans a (plus a zero) (plus (req_minus a b) b)).
    - exact (req_sym _ _ (req_plus_zero_r a)).
    - apply (req_trans (plus a zero) (plus a (plus (opp b) b))
                       (plus (req_minus a b) b)).
      + exact (req_plus_compat a a zero (plus (opp b) b) (req_refl a)
                               (req_sym _ _ (req_plus_opp_l b))).
      + exact (plus_assoc a (opp b) b). }
  apply (le_id_l a (plus (req_minus a b) b) b Ha).
  apply (le_id_r (plus (req_minus a b) b) (plus zero b) b).
  - exact (req_trans (plus zero b) (plus b zero) b (plus_comm zero b)
                     (req_plus_zero_r b)).
  - exact (le_plus_compat (req_minus a b) zero b b H (le_refl b)).
Qed.

(* Cancellation by a positive factor for real_le. *)
Lemma req_le_mult_pos_cancel : forall a c : R,
  real_lt zero c -> real_le (mult a c) zero -> real_le a zero.
Proof.
  intros a c Hc H.
  assert (Hic : real_le zero (inv_pos c Hc)).
  { apply (lt_le_iff zero (inv_pos c Hc)). left. exact (inv_pos_pos c Hc). }
  apply (le_id_l a (mult (mult a c) (inv_pos c Hc)) zero).
  - apply (req_trans a (mult a one) (mult (mult a c) (inv_pos c Hc))).
    + exact (req_sym _ _ (req_mult_one_r a)).
    + apply (req_trans (mult a one) (mult a (mult c (inv_pos c Hc)))
                       (mult (mult a c) (inv_pos c Hc))).
      * exact (req_mult_compat a a one (mult c (inv_pos c Hc)) (req_refl a)
                 (req_sym _ _ (inv_pos_correct c Hc))).
      * exact (mult_assoc a c (inv_pos c Hc)).
  - apply (le_id_r (mult (mult a c) (inv_pos c Hc))
                   (mult zero (inv_pos c Hc)) zero).
    + exact (req_trans (mult zero (inv_pos c Hc))
                       (mult (inv_pos c Hc) zero) zero
                       (mult_comm zero (inv_pos c Hc))
                       (mult_zero (inv_pos c Hc))).
    + exact (le_mult_compat_weak (mult a c) zero (inv_pos c Hc) Hic H).
Qed.

(* Right distributivity of multiplication over subtraction. *)
Lemma req_mult_minus_distr_r : forall a b c : R,
  real_eq (mult (req_minus a b) c) (req_minus (mult a c) (mult b c)).
Proof.
  intros a b c.
  unfold req_minus.
  apply (req_trans (mult (plus a (opp b)) c)
                   (mult c (plus a (opp b)))
                   (plus (mult a c) (opp (mult b c)))).
  - exact (mult_comm (plus a (opp b)) c).
  - apply (req_trans (mult c (plus a (opp b)))
                     (plus (mult c a) (mult c (opp b)))
                     (plus (mult a c) (opp (mult b c)))).
    + exact (distrib c a (opp b)).
    + apply (req_trans (plus (mult c a) (mult c (opp b)))
                       (plus (mult a c) (mult c (opp b)))
                       (plus (mult a c) (opp (mult b c)))).
      * exact (req_plus_compat (mult c a) (mult a c) (mult c (opp b))
                 (mult c (opp b)) (mult_comm c a) (req_refl (mult c (opp b)))).
      * exact (req_plus_compat (mult a c) (mult a c) (mult c (opp b))
                 (opp (mult b c)) (req_refl (mult a c))
                 (req_trans (mult c (opp b)) (opp (mult c b)) (opp (mult b c))
                            (req_opp_mult_l c b)
                            (req_opp_compat (mult c b) (mult b c)
                                            (mult_comm c b)))).
Qed.

(* Softmax scaling-temperature duality over real_eq; the softmax family and its partition are defined with positivity witnesses inlined. *)
Section ReqSoftmaxDual.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sumf_ext :
  forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sumf_pos :
  forall f : S -> R, (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f).

Definition reqd_softmax_scaled (c : R) (z : S -> R) (s : S) : R :=
  mult (exp_neg (mult c (z s)))
       (inv_pos (sumf (fun s0 : S => exp_neg (mult c (z s0))))
                (sumf_pos (fun s0 : S => exp_neg (mult c (z s0)))
                          (fun s0 : S => exp_neg_pos (mult c (z s0))))).

Definition reqd_softmax_temp_param (t : R) (Ht : real_lt zero t) (z : S -> R) (s : S) : R :=
  mult (exp_neg (mult (inv_pos t Ht) (z s)))
       (inv_pos (sumf (fun s0 : S => exp_neg (mult (inv_pos t Ht) (z s0))))
                (sumf_pos (fun s0 : S => exp_neg (mult (inv_pos t Ht) (z s0)))
                          (fun s0 : S => exp_neg_pos (mult (inv_pos t Ht) (z s0))))).

(* Scaling-temperature duality: the softmax of 1/t-scaled logits equals the temperature-t softmax; under real_eq semantics the two sides agree definitionally. *)
Theorem reqd_scale_temp_duality :
  forall (t : R) (Ht : real_lt zero t) (z : S -> R) (s : S),
    real_eq (reqd_softmax_scaled (inv_pos t Ht) z s)
        (reqd_softmax_temp_param t Ht z s).
Proof.
  intros t Ht z s. unfold reqd_softmax_scaled, reqd_softmax_temp_param.
  apply req_refl.
Qed.

(* First instance: the square witness d := r*r. *)
Theorem reqd_scale_dual_sq_k :
  forall (k : nat) (z : S -> R) (s : S),
    reqd_sqrt_witness
      (mult (reqd_nat_to_R (Datatypes.S k)) (reqd_nat_to_R (Datatypes.S k)))
      (reqd_nat_to_R (Datatypes.S k)) ->
    real_eq (reqd_softmax_scaled (inv_pos (reqd_nat_to_R (Datatypes.S k))
                                      (reqd_nat_to_R_pos k)) z s)
        (reqd_softmax_temp_param (reqd_nat_to_R (Datatypes.S k))
                                 (reqd_nat_to_R_pos k) z s).
Proof.
  intros k z s Hw.
  exact (reqd_scale_temp_duality (reqd_nat_to_R (Datatypes.S k))
                                 (reqd_nat_to_R_pos k) z s).
Qed.

(* Second instance: the nontrivial witness d := nat (k*k), discharged by the multiplicative homomorphism. *)
Theorem reqd_scale_dual_nat_sq_k :
  forall (k : nat) (z : S -> R) (s : S),
    reqd_sqrt_witness (reqd_nat_to_R (k * k)%nat) (reqd_nat_to_R k) ->
    real_eq (reqd_softmax_scaled (inv_pos (reqd_nat_to_R (Datatypes.S k))
                                      (reqd_nat_to_R_pos k)) z s)
        (reqd_softmax_temp_param (reqd_nat_to_R (Datatypes.S k))
                                 (reqd_nat_to_R_pos k) z s).
Proof.
  intros k z s Hw.
  assert (Hwok : reqd_sqrt_witness (reqd_nat_to_R (k * k)%nat)
                                   (reqd_nat_to_R k))
    by exact (reqd_sqrt_witness_nat_sq k).
  exact (reqd_scale_temp_duality (reqd_nat_to_R (Datatypes.S k))
                                 (reqd_nat_to_R_pos k) z s).
Qed.

End ReqSoftmaxDual.
End ReqAlgBridge2.


(* ============================================================ *)
(* -------------------------------------------------------------- *)
(*   reqd_log_cancel reqd_le_mult_nonneg_t12 reqd_lt_mult_pos_cancel       *)
(*   reqd_plus_rot reqd_opp_zero reqd_minus_zero_r reqd_sum_opp            *)
(*   reqd_sum_minus reqd_sum_zero                                    [12]  *)
(*   req_group_mean_def req_grpo_advantage_zero_mean req_grpo_square_expand*)
(*   req_grpo_variance_identity req_inv_G_absorb req_group_variance        *)
(*   req_group_variance_identity req_grpo_le_minus                         *)
(*   req_group_variance_le_raw_second_moment                          [15] *)
(*   req_boltzmann_normalized req_boltzmann_mix_normalized                 *)
(*   req_boltzmann_log_decomp reqd_log_div req_energy_in_log_boltzmann     *)
(*   fsum_pb_logZ fsum_zero fsum_norm_const req_free_energy_boltzmann      *)
(*   req_p_times_energy_decomp req_free_energy_kl_decomp                   *)
(*   req_free_energy_kl_diff req_free_energy_diff_kl                       *)
(*   req_relative_entropy_self_zero req_entropy_neg_sum                    *)
(*   req_free_energy_entropy reqd_p_times_ratio reqd_p_minus_ratio         *)
(*   reqd_minus_one_flip req_gibbs_pointwise req_gibbs_inequality          *)
(*   req_gibbs_equality req_boltzmann_dist_pos                        [26] *)
(*   req_max_entropy_is_boltzmann req_entropy_max_unique                   *)
(*   req_cross_entropy_decomp req_minus_plus_common_local                  *)
(*   req_cross_entropy_minus_self req_training_equivalence                 *)
(*   req_elbo_lower_bound req_evidence_kl_decomp req_elbo_explicit         *)
(*   reqd_boltzmann_dist_temp_pos(Defined) reqd_boltzmann_log_temp_decomp  *)
(*                                                                    [1]  *)
(*   reqd_sqrt_witness_sq reqd_sqrt_witness_nat_sq                    [5]  *)
(* -------------------------------------------------------------- *)

(*   req_le_minus_nonneg_rev<- req_le_mult_pos_cancel<-  *)
(*   reqd_scale_dual_sq_k<- reqd_scale_dual_nat_sq_k<-   *)
(* -------------------------------------------------------------- *)
(*     (@17521) temp_strict_A_chain2(@17825) temp_strict_ident2(@17879)    *)
(*     energy_exp_temp_strict_mono(@18019) temp_energy_dual_closed(@17788  *)

(* -------------------------------------------------------------- *)

(* Assumption audit: every statement below reports Closed under the global context. *)
Print Assumptions reqd_le_of_req.
Print Assumptions reqd_minus_compat.
Print Assumptions reqd_opp_zero.
Print Assumptions req_boltzmann_dist_pos.
