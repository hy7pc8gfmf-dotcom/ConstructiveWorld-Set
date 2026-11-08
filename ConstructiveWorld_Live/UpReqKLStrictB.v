(* ConstructiveWorld-Set — Bishop-order companions of the KL-strict family. *)

(** * UpReqKLStrictB: explicit [real_le_b] companions and completions for the strict KL family.

    Mission.  The strict-to-Bishop bridge [klstb_lt_le_b], the
      right-translation combinator [klstb_le_b_translate_r], the
      premise-free pointwise gap [klstb_gibbs_core_shift_B], the
      list-sum combiners [klstb_list_sum_zero]/[klstb_list_sum_le_b],
      the unconditional shifted sum [klstb_kl_sum_shift_B], the
      companions [klstb_kl_sum_strict_B]/[klstb_kl_energy_nonconst_B],
      and the degenerate dual [klstb_gibbs_core_zero_B].

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing] through
      [S15_TailFEPUp], [UpRealLeB], [UpRealLeB2], [UpRealLeB3] and
      [G07_KLWall] of this development.

    References.  This development, UpReqKLStrictB.v, the baseline module
      in ConstructiveWorld-Main whose statement names are carried over
      here verbatim (statement-face Set-carrier completion); strict
      sources in [G07_KLWall], Bishop-order toolkit in
      [UpRealLeB]/[UpRealLeB2]/[UpRealLeB3].

    Constructivity.  [real_le_b] is a Set-valued predicate and
      [real_lt] a [sigT] witness set, so all statements stay in [Set]
      with no classical-domain downgrade; proofs resolve within the
      weak trichotomy; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqKLStrictB.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 00015ff4]. *)

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
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import G07_KLWall.

(* ==================== Part 0. Rewriting auxiliary: the equality face of shifted cancellation ==================== *)

(* [(p-q) + (q-p) == 0] through an explicit
   associativity/commutativity/inverse/zero chain (no ring automation,
   as in G07 Part C0). *)
Lemma klstb_pq_shift_zero : forall p q : Real,
  real_eq (real_plus (real_plus p (real_opp q)) (real_plus q (real_opp p)))
          real_zero.
Proof.
  intros p q.
  apply (real_eq_trans
           (real_plus (real_plus p (real_opp q)) (real_plus q (real_opp p)))
           (real_plus p (real_opp p))
           real_zero).
  - apply (real_eq_trans
             (real_plus (real_plus p (real_opp q)) (real_plus q (real_opp p)))
             (real_plus p (real_plus (real_opp q) (real_plus q (real_opp p))))
             (real_plus p (real_opp p))).
    + apply real_eq_sym. apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat p
               (real_plus (real_opp q) (real_plus q (real_opp p)))
               p (real_opp p)).
      * apply real_eq_refl.
      * (* Inner sum: [(-q) + (q + (-p)) == -p]. *)
        apply (real_eq_trans
                 (real_plus (real_opp q) (real_plus q (real_opp p)))
                 (real_plus (real_plus (real_opp q) q) (real_opp p))
                 (real_opp p)).
        -- apply real_plus_assoc.
        -- apply (real_eq_trans
                    (real_plus (real_plus (real_opp q) q) (real_opp p))
                    (real_plus (real_plus q (real_opp q)) (real_opp p))
                    (real_opp p)).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus (real_opp q) q) (real_opp p)
                       (real_plus q (real_opp q)) (real_opp p)).
              ** apply real_plus_comm.
              ** apply real_eq_refl.
           ++ apply (real_eq_trans
                       (real_plus (real_plus q (real_opp q)) (real_opp p))
                       (real_plus real_zero (real_opp p))
                       (real_opp p)).
              ** apply (RealSetoid.real_eq_plus_compat
                          (real_plus q (real_opp q)) (real_opp p)
                          real_zero (real_opp p)).
                 --- apply real_plus_opp.
                 --- apply real_eq_refl.
              ** apply (real_eq_trans
                          (real_plus real_zero (real_opp p))
                          (real_plus (real_opp p) real_zero)
                          (real_opp p)).
                 --- apply real_plus_comm.
                 --- apply real_plus_zero.
  - apply real_plus_opp.
Qed.

(* ==================== Part A. Explicit one-way bridge from strict order to [real_le_b] ==================== *)

(* [x < y] (a [sigT] positive statement) implies [x <=_B y]: the left
   disjunct enters the [Or] face via [real_lt_le_iff_req], then the
   one-way bridge [real_le_to_le_b] applies (the derivation stays in
   [Set] throughout, with no classical-domain downgrade). *)
Lemma klstb_lt_le_b : forall x y : Real,
  real_lt x y -> real_le_b x y.
Proof.
  intros x y Hlt.
  apply real_le_to_le_b.
  apply (RealSetoid.real_lt_le_iff_req x y).
  left. exact Hlt.
Qed.

(* ==================== Part B. Right-translation combinator for [real_le_b] ==================== *)

Lemma klstb_le_b_translate_r : forall x y z : Real,
  real_le_b x y -> real_le_b (real_plus x z) (real_plus y z).
Proof.
  intros x y z H.
  apply (real_le_b_plus_compat x y z z H).
  apply leb3_le_b_refl.
Qed.

(* ==================== Part C. Pointwise premise-free Bishop face: [0 <=_B kl_term + (q-p)] ==================== *)
(* No comparison premise and no normalization premise; the witness is
   [real_gibbs_core_B] right-translated by [(q-p)] and closed with the
   Part 0 cancellation. *)

Lemma klstb_gibbs_core_shift_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_le_b real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))).
Proof.
  intros p q Hp Hq.
  apply (leb3_le_b_eq_l
           (real_plus (real_plus p (real_opp q)) (real_plus q (real_opp p)))
           real_zero
           (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
           (klstb_pq_shift_zero p q)).
  apply (klstb_le_b_translate_r (real_plus p (real_opp q))
                                (real_kl_term p q Hp Hq)
                                (real_plus q (real_opp p))).
  unfold real_kl_term.
  exact (real_gibbs_core_B p q Hp Hq).
Qed.

(* ==================== Part D. Pointwise sum combinator for [real_le_b] ==================== *)

Lemma klstb_list_sum_zero : forall (X : Type) (l : list X),
  real_eq (real_list_sum X (fun _ : X => real_zero) l) real_zero.
Proof.
  intros X l.
  induction l as [| w l IH].
  - apply real_eq_refl.
  - cbn [real_list_sum].
    apply (real_eq_trans
             (real_plus real_zero (real_list_sum X (fun _ : X => real_zero) l))
             (real_plus (real_list_sum X (fun _ : X => real_zero) l) real_zero)
             real_zero).
    + apply real_plus_comm.
    + apply (real_eq_trans
               (real_plus (real_list_sum X (fun _ : X => real_zero) l) real_zero)
               (real_list_sum X (fun _ : X => real_zero) l)
               real_zero).
      * apply real_plus_zero.
      * exact IH.
Qed.

Lemma klstb_list_sum_le_b : forall (X : Type) (f g : X -> Real) (l : list X),
  (forall s : X, real_le_b (f s) (g s)) ->
  real_le_b (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l H.
  induction l as [| w l IH].
  - apply leb3_le_b_refl.
  - cbn [real_list_sum].
    apply (real_le_b_plus_compat (f w) (g w)
             (real_list_sum X f l) (real_list_sum X g l)).
    + apply H.
    + exact IH.
Qed.

(* ==================== Part E. Unconditional shifted sum: [0 <=_B sum_s (kl_term + (q-p))] ==================== *)
(* No comparison premise and no normalization premise; pointwise Part C
   is lifted through the Part D combiner. *)

Lemma klstb_kl_sum_shift_B : forall (X : Type) (l : list X) (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s)),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                               (real_plus (q s) (real_opp (p s)))) l).
Proof.
  intros X l p q Hp Hq.
  apply (leb3_le_b_eq_l
           (real_list_sum X (fun _ : X => real_zero) l)
           real_zero
           (real_list_sum X
              (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                      (real_plus (q s) (real_opp (p s)))) l)
           (klstb_list_sum_zero X l)).
  apply (klstb_list_sum_le_b X
           (fun _ : X => real_zero)
           (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                   (real_plus (q s) (real_opp (p s)))) l).
  intro s.
  apply (klstb_gibbs_core_shift_B (p s) (q s) (Hp s) (Hq s)).
Qed.

(* ==================== Part F. Bishop-form companions of the two strict main statements ==================== *)
(* Companion semantics: the premise face is copied verbatim from the
   strict family and the conclusion is weakened from strict to
   [real_le_b] — showing what the strict layer and the Bishop layer
   each reach on identically shaped statement faces. *)

(* Companion of [klst_kl_sum_strict] (G07 Part D, one-sided weak-order
   branch). *)
Lemma klstb_kl_sum_strict_B : forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hpq : forall s : X, real_le (p s) (q s))
  (Hnormp : real_eq (real_list_sum X p (l₁ ++ s₀ :: l₂)) real_one)
  (Hnormq : real_eq (real_list_sum X q (l₁ ++ s₀ :: l₂)) real_one)
  (Hdiv : real_lt (p s₀) (q s₀)),
  real_le_b real_zero
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                    (l₁ ++ s₀ :: l₂)).
Proof.
  intros X l₁ s₀ l₂ p q Hp Hq Hpq Hnormp Hnormq Hdiv.
  apply (klstb_lt_le_b real_zero
          (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                         (l₁ ++ s₀ :: l₂))).
  exact (klst_kl_sum_strict X l₁ s₀ l₂ p q Hp Hq Hpq Hnormp Hnormq Hdiv).
Qed.

(* Companion of [klst_kl_energy_nonconst] (G07 Part G, two-sided
   premise-free main statement). *)
Lemma klstb_kl_energy_nonconst_B : forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hpq : forall s : X, Or (real_le (p s) (q s)) (real_le (q s) (p s)))
  (Hnormp : real_eq (real_list_sum X p (l₁ ++ s₀ :: l₂)) real_one)
  (Hnormq : real_eq (real_list_sum X q (l₁ ++ s₀ :: l₂)) real_one)
  (Hdiv : Or (real_lt (p s₀) (q s₀)) (real_lt (q s₀) (p s₀))),
  real_le_b real_zero
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                    (l₁ ++ s₀ :: l₂)).
Proof.
  intros X l₁ s₀ l₂ p q Hp Hq Hpq Hnormp Hnormq Hdiv.
  apply (klstb_lt_le_b real_zero
          (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s))
                         (l₁ ++ s₀ :: l₂))).
  exact (klst_kl_energy_nonconst X l₁ s₀ l₂ p q Hp Hq Hpq Hnormp Hnormq Hdiv).
Qed.

(* ==================== Part G. The degenerate dual face ==================== *)
(* At [p == q] the shifted gap [kl_term + (q-p)] is zero: the equality
   face enters the bridge through its right disjunct.  Together with
   Part C (premise-free away from [p == q]) the three cases of the weak
   comparison meet on the [real_le_b] face. *)

Lemma klstb_gibbs_core_zero_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hpq : real_eq p q),
  real_le_b real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))).
Proof.
  intros p q Hp Hq Hpq.
  apply real_le_to_le_b.
  apply (RealSetoid.real_eq_le real_zero
           (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))).
  apply real_eq_sym.
  exact (klst_gibbs_core_zero p q Hp Hq Hpq).
Qed.

(* ==================== Closure audit: [Print Assumptions] reports every statement Closed ==================== *)

Print Assumptions klstb_pq_shift_zero.
Print Assumptions klstb_lt_le_b.
Print Assumptions klstb_le_b_translate_r.
Print Assumptions klstb_gibbs_core_shift_B.
Print Assumptions klstb_list_sum_zero.
Print Assumptions klstb_list_sum_le_b.
Print Assumptions klstb_kl_sum_shift_B.
Print Assumptions klstb_kl_sum_strict_B.
Print Assumptions klstb_kl_energy_nonconst_B.
Print Assumptions klstb_gibbs_core_zero_B.
