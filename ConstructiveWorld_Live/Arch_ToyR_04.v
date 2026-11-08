(* ConstructiveWorld-Set — statement-family cluster: temperature-weighted Gibbs inequalities, Beukers series terms, ln2 integralization, q-tilde integrality. *)

(** * Arch_ToyR_04: statement families with their witness carriers.

    Mission.  The [gfe_le_of_lt] Gibbs family: pointwise and finite-sum
      eps/Bishop forms of the temperature-weighted KL inequality and the
      symmetric Jeffreys forms [gfe_jeffreys_sym_B],
      [gfe_jeffreys_sym_list_B]; the [bv_term] Beukers series family:
      term values and positivity, truncation carriers, [bv_sum_mono],
      [bv_sum_pos], the discrete core [bv_delannoy_eq_qtilde] and the
      numerator closed form [bv_p]; the [pi_ptilde] integralization
      family: [pi_Pn_int], [pi_Qn_le_8pow], [pi_x_n_frac],
      [pi_den_divide]; the nat-layer binomial scaffolding [bkC] with the
      integrality witnesses [bk_Qn_int], [bk_Qn_ge_3pow].

    Dependencies.  The library files listed in the Require face below;
      Stdlib [List], [QArith], [ZArith], [Arith], [Lia].

    References.  Statement families carried over from the
      ConstructiveWorld-Main baseline; the nine second-law statements
      around [slc_minus_r_plus_cancel] are not carried here
      ([SecondLawQuantified] is outside this world) — [SecondLawConsume.v]
      hosts them.

    Constructivity.  All proofs close by [Qed]; zero admission words; no
      classical logic; statement faces are carried by the [Set] layer.

    Build.  [coqc -native-compiler no -q -Q . "" Arch_ToyR_04.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
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
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
From Stdlib Require Import List.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import UpReqKLStrictB.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral.
Require Import PadeErrorIntegral BeukersLists PintMono.
Require Import BeukersLists HansonLcm.

(* ================= Section 2. The gfe_le_of_lt family ================= *)
Import ListNotations.

(* Part 0: order-algebraic support lemmas (four). *)

(* 0.1 Bridge from strict positivity to weak nonnegativity (temperature  *)
(* premise downgrade: the [b > 0] exit feeds a [b >= 0] entry).  [real_le] *)
(* is Or-encoded, so the [lt] branch is the [inl] injection directly; no *)
(* intermediate lemma is needed. *)
Lemma gfe_le_of_lt : forall b : Real,
  real_lt real_zero b -> real_le real_zero b.
Proof.
  intros b Hb.
  exact (inl Hb).
Qed.

(* 0.2 [(q - p) + (p - q) == 0]: the asymmetric cancellation core (an    *)
(* associativity chain with no dependence on an opp-distribution law;    *)
(* the cancellation engine of the symmetric Jeffreys form). *)
Lemma gfe_pq_shift_zero : forall p q : Real,
  real_eq (real_plus (real_plus q (real_opp p)) (real_plus p (real_opp q)))
          real_zero.
Proof.
  intros p q.
  assert (Hopp0 : real_eq (real_plus (real_opp p) p) real_zero).
  { exact (real_eq_trans (real_plus (real_opp p) p)
                         (real_plus p (real_opp p)) real_zero
             (real_plus_comm (real_opp p) p) (real_plus_opp p)). }
  (* step 1: two associativity hops fold the [p] arm into the [q] arm *)
  assert (Hs1 : real_eq (real_plus (real_plus q (real_opp p))
                                   (real_plus p (real_opp q)))
                        (real_plus (real_plus q (real_plus (real_opp p) p))
                                   (real_opp q))).
  { apply (real_eq_trans
             (real_plus (real_plus q (real_opp p)) (real_plus p (real_opp q)))
             (real_plus (real_plus (real_plus q (real_opp p)) p) (real_opp q))
             (real_plus (real_plus q (real_plus (real_opp p) p)) (real_opp q))).
    - exact (real_plus_assoc (real_plus q (real_opp p)) p (real_opp q)).
    - apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_plus q (real_opp p)) p)
               (real_opp q)
               (real_plus q (real_plus (real_opp p) p))
               (real_opp q)).
      + apply (real_eq_sym (real_plus q (real_plus (real_opp p) p))
                           (real_plus (real_plus q (real_opp p)) p)).
        exact (real_plus_assoc q (real_opp p) p).
      + apply real_eq_refl. }
  (* step 2: the inner [(- p) + p] cancels to [0] *)
  assert (Hs2 : real_eq (real_plus (real_plus q (real_plus (real_opp p) p))
                                   (real_opp q))
                        (real_plus (real_plus q real_zero) (real_opp q))).
  { apply (RealSetoid.real_eq_plus_compat
             (real_plus q (real_plus (real_opp p) p))
             (real_opp q)
             (real_plus q real_zero)
             (real_opp q)).
    - apply (RealSetoid.real_eq_plus_compat q
               (real_plus (real_opp p) p) q real_zero).
      + apply real_eq_refl.
      + exact Hopp0.
    - apply real_eq_refl. }
  (* steps 3-4: reassociate [(q + 0) + (- q)] and close by [real_plus_opp] *)
  assert (Hs3 : real_eq (real_plus (real_plus q real_zero) (real_opp q))
                        real_zero).
  { apply (real_eq_trans
             (real_plus (real_plus q real_zero) (real_opp q))
             (real_plus q (real_opp q))
             real_zero).
    - apply (RealSetoid.real_eq_plus_compat (real_plus q real_zero)
               (real_opp q) q (real_opp q)).
      + exact (real_plus_zero q).
      + apply real_eq_refl.
    - exact (real_plus_opp q). }
  exact (real_eq_trans
           (real_plus (real_plus q (real_opp p)) (real_plus p (real_opp q)))
           (real_plus (real_plus q (real_plus (real_opp p) p)) (real_opp q))
           real_zero
           Hs1
           (real_eq_trans
              (real_plus (real_plus q (real_plus (real_opp p) p)) (real_opp q))
              (real_plus (real_plus q real_zero) (real_opp q))
              real_zero Hs2 Hs3)).
Qed.

(* 0.3 Translation-cancellation identity: [(a + s) + (d + t) == a + d]   *)
(* whenever [s + t == 0]; closes in one hop by [real_plus_swap_mid] —    *)
(* the engine of the symmetric Jeffreys main identity. *)
Lemma gfe_sym_sum_eq : forall (a d s t : Real),
  real_eq (real_plus s t) real_zero ->
  real_eq (real_plus (real_plus a s) (real_plus d t)) (real_plus a d).
Proof.
  intros a d s t Hst.
  apply (real_eq_trans
           (real_plus (real_plus a s) (real_plus d t))
           (real_plus (real_plus a d) (real_plus s t))
           (real_plus a d)).
  - exact (real_plus_swap_mid a s d t).
  - apply (real_eq_trans
             (real_plus (real_plus a d) (real_plus s t))
             (real_plus (real_plus a d) real_zero)
             (real_plus a d)).
    + apply (RealSetoid.real_eq_plus_compat (real_plus a d) (real_plus s t)
               (real_plus a d) real_zero).
      * apply real_eq_refl.
      * exact Hst.
    + exact (real_plus_zero (real_plus a d)).
Qed.

(* 0.4 Bishop-form right-operand transporter (a family-level combiner:   *)
(* [le_b x y] with [y == z] gives [le_b x z]; the dual of the            *)
(* left-operand transporter [leb3_le_b_eq_l], which [UpRealLeB3] lacks). *)
Lemma gfe_le_b_eq_r : forall (x y z : Real),
  real_le_b x y -> real_eq y z -> real_le_b x z.
Proof.
  intros x y z Hxy Heq. unfold real_le_b in Hxy. unfold real_le_b.
  intros eps Heps.
  apply (RealSetoid.real_lt_compat x x
           (real_plus y eps) (real_plus z eps)).
  - apply real_eq_refl.
  - apply (RealSetoid.real_eq_plus_compat y eps z eps).
    + exact Heq.
    + apply real_eq_refl.
  - exact (Hxy eps Heps).
Qed.

(* Part A: temperature-parameterized forms (variant face A; five members *)
(* of the beta-weighted Gibbs family). *)

(* A1 temperature-parameterized pointwise core, eps form (weak premise   *)
(* [b >= 0], admitting the zero-temperature degeneration):               *)
(* [b*(p-q) <= b*kl(p|q) + b*p*eps].                                     *)
(* Certificate chain: [real_gibbs_core_eps], then order preservation of  *)
(* left multiplication [real_le_mult_compat_r], then the distributive    *)
(* reassociation (three-step assembly; the coefficient is tracked        *)
(* explicitly throughout). *)
Lemma gfe_gibbs_core_temp_eps : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_le real_zero b) (eps : Real) (Heps : real_lt real_zero eps),
  real_le (real_mult b (real_plus p (real_opp q)))
          (real_plus (real_mult b (real_kl_term p q Hp Hq))
                     (real_mult b (real_mult p eps))).
Proof.
  intros p q b Hp Hq Hb eps Heps.
  apply (RealSetoid.real_le_id_r
           (real_mult b (real_plus p (real_opp q)))
           (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                   (real_mult p eps)))
           (real_plus (real_mult b (real_kl_term p q Hp Hq))
                      (real_mult b (real_mult p eps)))).
  - exact (real_distrib b (real_kl_term p q Hp Hq) (real_mult p eps)).
  - exact (real_le_mult_compat_r b (real_plus p (real_opp q))
             (real_plus (real_kl_term p q Hp Hq) (real_mult p eps)) Hb
             (real_gibbs_core_eps p q Hp Hq eps Heps)).
Qed.

(* A2 temperature-parameterized pointwise core, Bishop form (strict      *)
(* premise [b > 0]): [b*(p-q) <=_B b*kl(p|q)].                           *)
(* Closer: [real_le_closure_b] with [D := b*p] (positivity certificate   *)
(* [real_mult_positive]); the per-eps margin [(b*p)*eps] is supplied by  *)
(* A1 reassociated through [real_mult_assoc].                            *)
(* Note: at [b = 0] no certificate for D can be supplied — the Bishop    *)
(* premise is strictly stronger than the eps premise, which is the       *)
(* constructive bifurcation of the form choice under temperature         *)
(* parameterization. *)
Theorem gfe_gibbs_core_temp_B : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_lt real_zero b),
  real_le_b (real_mult b (real_plus p (real_opp q)))
            (real_mult b (real_kl_term p q Hp Hq)).
Proof.
  intros p q b Hp Hq Hb.
  apply (real_le_closure_b
           (real_mult b (real_plus p (real_opp q)))
           (real_mult b (real_kl_term p q Hp Hq))
           (real_mult b p) (real_mult_positive b p Hb Hp)).
  intros eps Heps.
  apply (RealSetoid.real_le_id_r
           (real_mult b (real_plus p (real_opp q)))
           (real_plus (real_mult b (real_kl_term p q Hp Hq))
                      (real_mult b (real_mult p eps)))
           (real_plus (real_mult b (real_kl_term p q Hp Hq))
                      (real_mult (real_mult b p) eps))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult b (real_kl_term p q Hp Hq))
             (real_mult b (real_mult p eps))
             (real_mult b (real_kl_term p q Hp Hq))
             (real_mult (real_mult b p) eps)).
    + apply real_eq_refl.
    + exact (real_mult_assoc b p eps).
  - exact (gfe_gibbs_core_temp_eps p q b Hp Hq (gfe_le_of_lt b Hb) eps Heps).
Qed.

(* A3 temperature-parameterized finite-sum eps form (weak premise        *)
(* [b >= 0]): [0 <= b*sum_s kl(p s|q s) + b*eps].                        *)
(* Certificate chain: [real_gibbs_inequality_eps], order preservation of *)
(* left multiplication, distributive reassociation; the left end         *)
(* [b*0 == 0] is reassociated by [real_mult_zero] (normalization        *)
(* cancellation survives temperature scaling). *)
Lemma gfe_gibbs_inequality_temp_eps : forall (X : Type) (l : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hnormp : real_eq (real_list_sum X p l) real_one)
  (Hnormq : real_eq (real_list_sum X q l) real_one)
  (b : Real) (Hb : real_le real_zero b) (eps : Real)
  (Heps : real_lt real_zero eps),
  real_le real_zero
    (real_plus (real_mult b (real_list_sum X
                  (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))
               (real_mult b eps)).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq b Hb eps Heps.
  apply (RealSetoid.real_le_id_l real_zero (real_mult b real_zero)
           (real_plus
              (real_mult b (real_list_sum X
                  (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))
              (real_mult b eps))).
  - exact (real_eq_sym (real_mult b real_zero) real_zero (real_mult_zero b)).
  - apply (RealSetoid.real_le_id_r (real_mult b real_zero)
             (real_mult b (real_plus (real_list_sum X
                  (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
                  eps))
             (real_plus
                (real_mult b (real_list_sum X
                   (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))
                (real_mult b eps))).
    + exact (real_distrib b (real_list_sum X
                 (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
                 eps).
    + exact (real_le_mult_compat_r b real_zero
                (real_plus (real_list_sum X
                    (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
                  eps) Hb
                (real_gibbs_inequality_eps X l p q Hp Hq Hnormp Hnormq
                   eps Heps)).
Qed.

(* A4 temperature-parameterized finite-sum Bishop form (strict premise   *)
(* [b > 0]): [0 <=_B b*sum_s kl(p s|q s)].                               *)
(* Closer: [real_le_closure_b] with [D := b]; the A3 exit margin         *)
(* [(b*sum kl) + b*eps] matches the closure supply shape [y + D*eps]     *)
(* verbatim, so it plugs in directly. *)
Theorem gfe_gibbs_inequality_temp_B : forall (X : Type) (l : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hnormp : real_eq (real_list_sum X p l) real_one)
  (Hnormq : real_eq (real_list_sum X q l) real_one)
  (b : Real) (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_list_sum X
        (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq b Hb.
  apply (real_le_closure_b real_zero           (real_mult b (real_list_sum X               (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))           b Hb).
  intros eps Heps.
  exact (gfe_gibbs_inequality_temp_eps X l p q Hp Hq Hnormp Hnormq b           (gfe_le_of_lt b Hb) eps Heps).
Qed.

(* A5 family-level combiner: order preservation of multiplication by a   *)
(* positive in Bishop form (the library has no multiplicative [<=_B]     *)
(* exit): [x <=_B y] with [0 < b] entails [b*x <=_B b*y].                *)
(* Certificate chain: unfold [le_b] eps by eps, lift to [le], apply the  *)
(* order preservation of left multiplication, reassociate                *)
(* distributively, and re-close by [real_le_closure_b] with [D := b]. *)
Lemma gfe_le_b_mult_pos : forall (x y b : Real),
  real_lt real_zero b -> real_le_b x y -> real_le_b (real_mult b x) (real_mult b y).
Proof.
  intros x y b Hb Hxy.
  apply (real_le_closure_b (real_mult b x) (real_mult b y) b Hb).
  intros eps Heps.
  apply (RealSetoid.real_le_id_r (real_mult b x)
           (real_mult b (real_plus y eps))
           (real_plus (real_mult b y) (real_mult b eps))).
  - exact (real_distrib b y eps).
  - apply (real_le_mult_compat_r b x (real_plus y eps) (gfe_le_of_lt b Hb)).
    exact (inl (Hxy eps Heps)).
Qed.

(* A6 temperature-parameterized unconditional gap Bishop form ([b > 0]): *)
(* [0 <=_B b*(kl(p|q) + (q-p))].                                         *)
(* Certificate chain: the premise-free gap Bishop form                   *)
(* [klstb_gibbs_core_shift_B] lifted once through the A5 combiner — the  *)
(* second-law reading is invariant under temperature scaling. *)
Theorem gfe_gibbs_temp_gap_B : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_plus (real_kl_term p q Hp Hq)
                            (real_plus q (real_opp p)))).
Proof.
  intros p q b Hp Hq Hb.
  apply (leb3_le_b_eq_l (real_mult b real_zero) real_zero
           (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                   (real_plus q (real_opp p))))).
  - exact (real_mult_zero b).
  - exact (gfe_le_b_mult_pos real_zero
             (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
             b Hb (klstb_gibbs_core_shift_B p q Hp Hq)).
Qed.

(* A6b flattened corollary: [0 <=_B b*kl(p|q) + b*(q-p)] (distributive   *)
(* reassociation face). *)
Lemma gfe_gibbs_temp_gap_B_flat : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_plus (real_mult b (real_kl_term p q Hp Hq))
               (real_mult b (real_plus q (real_opp p)))).
Proof.
  intros p q b Hp Hq Hb.
  apply (gfe_le_b_eq_r real_zero
           (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                   (real_plus q (real_opp p))))
           (real_plus (real_mult b (real_kl_term p q Hp Hq))
                      (real_mult b (real_plus q (real_opp p))))).
  - exact (gfe_gibbs_temp_gap_B p q b Hp Hq Hb).
  - exact (real_distrib b (real_kl_term p q Hp Hq)
             (real_plus q (real_opp p))).
Qed.

(* Part B: the symmetric Jeffreys forms (variant face B; two members     *)
(* complementing the asymmetric face). *)

(* B1 symmetric Jeffreys pointwise Bishop form (the complementary        *)
(* closure of the asymmetric form): [0 <=_B kl(p|q) + kl(q|p)].          *)
(* Certificate chain: the two klstb shift forms are each [>=_B 0], added *)
(* by [real_le_b_plus_compat]; the translation-cancellation term         *)
(* [(q-p) + (p-q)] is then peeled off the sum by [gfe_sym_sum_eq] (the   *)
(* [swap_mid] engine). *)
Theorem gfe_jeffreys_sym_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_le_b real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_kl_term q p Hq Hp)).
Proof.
  intros p q Hp Hq.
  apply (gfe_le_b_eq_r real_zero
           (real_plus (real_plus (real_kl_term p q Hp Hq)
                                 (real_plus q (real_opp p)))
                      (real_plus (real_kl_term q p Hq Hp)
                                 (real_plus p (real_opp q))))
           (real_plus (real_kl_term p q Hp Hq) (real_kl_term q p Hq Hp))).
  - apply (leb3_le_b_eq_l (real_plus real_zero real_zero) real_zero _
             (real_plus_zero real_zero)
             (real_le_b_plus_compat real_zero
                (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
                real_zero
                (real_plus (real_kl_term q p Hq Hp) (real_plus p (real_opp q)))
                (klstb_gibbs_core_shift_B p q Hp Hq)
                (klstb_gibbs_core_shift_B q p Hq Hp))).
  - exact (gfe_sym_sum_eq (real_kl_term p q Hp Hq) (real_kl_term q p Hq Hp)
             (real_plus q (real_opp p)) (real_plus p (real_opp q))
             (gfe_pq_shift_zero p q)).
Qed.

(* B2 symmetric Jeffreys finite-sum Bishop form:                         *)
(* [0 <=_B sum_s (kl(p s|q s) + kl(q s|p s))].                           *)
(* Certificate chain: [klstb_list_sum_le_b] feeds B1 pointwise, and the  *)
(* zero-constant sum is reassociated by [klstb_list_sum_zero] (the       *)
(* symmetric family closes at the summation layer). *)
Theorem gfe_jeffreys_sym_list_B : forall (X : Type) (l : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s)),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                               (real_kl_term (q s) (p s) (Hq s) (Hp s))) l).
Proof.
  intros X l p q Hp Hq.
  apply (leb3_le_b_eq_l
           (real_list_sum X (fun _ : X => real_zero) l)
           real_zero
           (real_list_sum X
              (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                      (real_kl_term (q s) (p s) (Hq s) (Hp s)))
              l)).
  - exact (klstb_list_sum_zero X l).
  - apply (klstb_list_sum_le_b X (fun _ : X => real_zero)
             (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                     (real_kl_term (q s) (p s) (Hq s) (Hp s)))
             l).
    intro s. exact (gfe_jeffreys_sym_B (p s) (q s) (Hp s) (Hq s)).
Qed.

(* Closure audit: the Print Assumptions outputs below should all report  *)
(* Closed. *)

Print Assumptions gfe_le_of_lt.
Print Assumptions gfe_pq_shift_zero.
Print Assumptions gfe_sym_sum_eq.
Print Assumptions gfe_le_b_eq_r.
Print Assumptions gfe_gibbs_core_temp_eps.
Print Assumptions gfe_gibbs_core_temp_B.
Print Assumptions gfe_gibbs_inequality_temp_eps.
Print Assumptions gfe_gibbs_inequality_temp_B.
Print Assumptions gfe_le_b_mult_pos.
Print Assumptions gfe_gibbs_temp_gap_B.
Print Assumptions gfe_gibbs_temp_gap_B_flat.
Print Assumptions gfe_jeffreys_sym_B.
Print Assumptions gfe_jeffreys_sym_list_B.
(* ================= Section 3. The bv_term family ================= *)
From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.

Open Scope nat_scope.

(* Section A. Series definition: the term [bv_term = C(n+m,n) *          *)
(* B(n+2m+1, 2n+1)] and its positivity. *)

Definition bv_term (n m : nat) : Q :=
  ((Z.of_nat (bkC (n + m) n) # 1) *
     (q_fact (n + 2 * m) * q_fact (2 * n + 1) / q_fact (3 * n + 2 * m + 2)))%Q.

(* [bv_term n m == C(n+m,n) * integral_0^1 t^{n+2m} (1-t)^{2n+1} dt],    *)
(* reduced to [pint_integral] by [pei_beta_value]. *)
Lemma bv_term_value : forall n m : nat,
  bv_term n m ==
  ((Z.of_nat (bkC (n + m) n) # 1) * pint_integral (pei_list (n + 2 * m) (2 * n + 1)))%Q.
Proof.
  intros n m. unfold bv_term.
  rewrite (qeqT_imp_qeq _ _ (pei_beta_value (n + 2 * m) (2 * n + 1))).
  replace ((n + 2 * m) + (2 * n + 1) + 1)%nat with (3 * n + 2 * m + 2)%nat by lia.
  reflexivity.
Qed.

(** bv_term_pos: the series term is strictly positive — [bkC >= 1]        *)
(** multiplied by the positivity of [q_fact]. *)
Theorem bv_term_pos : forall n m : nat, QltT 0 (bv_term n m).
Proof.
  intros n m. apply Qlt_to_QltT. unfold bv_term. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - assert (Hb : NatLe 1 (bkC (n + m) n)) by (apply bkC_pos; apply NatLe_lift; lia).
    pose proof (NatLe_drop _ _ Hb) as HbP.
    assert (Hz : (0 <= Z.of_nat (bkC (n + m) n))%Z) by apply Nat2Z.is_nonneg.
    unfold Qlt. cbn [Qnum Qden Qmult Pos.mul]. lia.
  - apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos.
    + apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* Section B. Truncation carriers: [bv_pad] (appends two zero            *)
(* coefficients) and [bv_carrier] (same shape as [pei_eb_list]). *)

Definition bv_pad (p : list Q) : list Q := pei_ztail (pei_ztail p).

Lemma bv_pad_eval : forall (p : list Q) (x : Q),
  pint_eval (bv_pad p) x == pint_eval p x.
Proof.
  intros p x. unfold bv_pad.
  rewrite (qeqT_imp_qeq _ _ (pei_eval_ztail (pei_ztail p) x)),
          (qeqT_imp_qeq _ _ (pei_eval_ztail p x)).
  reflexivity.
Qed.

Lemma bv_pad_int : forall p : list Q,
  pint_integral (bv_pad p) == pint_integral p.
Proof.
  intro p. unfold bv_pad.
  rewrite (qeqT_imp_qeq _ _ (pei_integral_ztail (pei_ztail p))),
          (qeqT_imp_qeq _ _ (pei_integral_ztail p)).
  reflexivity.
Qed.

Lemma bv_pad_length : forall p : list Q, length (bv_pad p) = (length p + 2)%nat.
Proof.
  intro p. unfold bv_pad, pei_ztail.
  rewrite app_length, app_length. cbn [length]. lia.
Qed.

(* [bv_carrier n M]: the coefficient table of the partial sum            *)
(* [sum_{m<=M} C(n+m,n) * t^{n+2m} (1-t)^{2n+1}] (same shape as           *)
(* [pei_eb_list]). *)
Fixpoint bv_carrier (n M : nat) : list Q :=
  match M with
  | 0 => pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                    (pei_list (n + 2 * 0) (2 * n + 1))
  | Datatypes.S m =>
      pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                           (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
               (bv_pad (bv_carrier n m))
  end.

Lemma bv_carrier_length : forall n M : nat,
  length (bv_carrier n M) = (3 * n + 2 * M + 2)%nat.
Proof.
  intros n M. induction M as [| m IH].
  - change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    rewrite (RealSetoid.Id_eq _ _
              (pei_scale_length ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                                (pei_list (n + 2 * 0) (2 * n + 1)))),
            (RealSetoid.Id_eq _ _
              (pei_list_length (n + 2 * 0) (2 * n + 1))).
    lia.
  - change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                    (bv_pad (bv_carrier n m))).
    assert (HL : Id (length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                        (pei_list (n + 2 * Datatypes.S m) (2 * n + 1))))
                    (length (bv_pad (bv_carrier n m)))).
    { apply RealSetoid.eq_Id.
      rewrite (RealSetoid.Id_eq _ _
                (pei_scale_length ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                  (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))),
              (RealSetoid.Id_eq _ _
                (pei_list_length (n + 2 * Datatypes.S m) (2 * n + 1))),
              bv_pad_length, IH. lia. }
    rewrite (RealSetoid.Id_eq _ _ (pei_add_length
              (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                          (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
              (bv_pad (bv_carrier n m)) HL)),
            (RealSetoid.Id_eq _ _
              (pei_scale_length ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))),
            (RealSetoid.Id_eq _ _
              (pei_list_length (n + 2 * Datatypes.S m) (2 * n + 1))).
    lia.
Qed.

(** bv_carrier_eval: the pointwise value equals                          *)
(** [t^n (1-t)^{2n+1} * sum_{m<=M} C(n+m,n) (t^2)^m] (a                  *)
(** negative-binomial-type truncation). *)
Theorem bv_carrier_eval : forall (n M : nat) (t : Q),
  pint_eval (bv_carrier n M) t ==
  q_pow t n * q_pow (1 - t)%Q (2 * n + 1) *
    bk_psQ (fun m : nat => (Z.of_nat (bkC (n + m) n) # 1)%Q)
           (Datatypes.S M) (t * t)%Q.
Proof.
  intros n M. induction M as [| m IH]; intro t.
  - change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    change (bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                   (Datatypes.S 0) (t * t)%Q)
      with (0 + (Z.of_nat (bkC (n + 0) n) # 1) * 1)%Q.
    rewrite (qeqT_imp_qeq _ _
              (pei_eval_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                              (pei_list (n + 2 * 0) (2 * n + 1)) t)).
    rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + 2 * 0) (2 * n + 1) t)).
    replace (n + 2 * 0)%nat with n%nat by lia.
    ring.
  - change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                    (bv_pad (bv_carrier n m))).
    rewrite (qeqT_imp_qeq _ _
              (pei_eval_add
                 (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                             (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                 (bv_pad (bv_carrier n m)) t)).
    rewrite (qeqT_imp_qeq _ _
              (pei_eval_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                              (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)) t)).
    rewrite (qeqT_imp_qeq _ _
              (pei_beta_eval (n + 2 * Datatypes.S m) (2 * n + 1) t)).
    rewrite (bv_pad_eval (bv_carrier n m) t).
    rewrite (IH t).
    assert (HpsQ : bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                          (Datatypes.S (Datatypes.S m)) (t * t)%Q
                   == bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                          (Datatypes.S m) (t * t)%Q
                      + (Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q
                          * q_pow (t * t)%Q (Datatypes.S m))
      by reflexivity.
    rewrite HpsQ.
    rewrite (qeqT_imp_qeq _ _ (q_pow_add t n (2 * Datatypes.S m))).
    replace (2 * Datatypes.S m)%nat with (Datatypes.S m + Datatypes.S m)%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (q_pow_add t (Datatypes.S m) (Datatypes.S m))).
    rewrite <- (qeqT_imp_qeq _ _ (bk_q_pow_mul t t (Datatypes.S m))).
    ring.
Qed.

(* Section C. Truncated integrals: the exact value [bv_carrier_value],   *)
(* monotonicity [bv_sum_mono], positivity [bv_sum_pos]. *)

Fixpoint bv_zeros (L : nat) : list Q :=
  match L with
  | 0 => nil
  | Datatypes.S m => 0%Q :: bv_zeros m
  end.

Lemma bv_zeros_length : forall L : nat, length (bv_zeros L) = L.
Proof.
  induction L as [| l IH].
  - reflexivity.
  - cbn [bv_zeros length]. rewrite IH. reflexivity.
Qed.

Lemma bv_zeros_int : forall (L k : nat), pint_integral_from (bv_zeros L) k == 0%Q.
Proof.
  induction L as [| l IH]; intros k.
  - reflexivity.
  - cbn [bv_zeros pint_integral_from]. unfold pint_monomial_int.
    rewrite (qeqT_imp_qeq _ _ (pint_zero_div (Z.of_nat (Datatypes.S k) # 1))),
            Qplus_0_l. apply IH.
Qed.

Theorem bv_zeros_int0 : forall L : nat, pint_integral (bv_zeros L) == 0%Q.
Proof. intro L. unfold pint_integral. apply bv_zeros_int. Qed.

Lemma bv_c_pos_le : forall n m : nat, QleT' 0 ((Z.of_nat (bkC (n + m) n) # 1)%Q).
Proof.
  intros n m. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
  assert (Hb : NatLe 1 (bkC (n + m) n)) by (apply bkC_pos; apply NatLe_lift; lia).
  pose proof (NatLe_drop _ _ Hb) as HbP.
  assert (Hz : (0 <= Z.of_nat (bkC (n + m) n))%Z) by apply Nat2Z.is_nonneg.
  lia.
Qed.

Lemma bv_pos_cint : forall n m : nat,
  QleT' 0 (pint_integral (pei_list (n + 2 * m) (2 * n + 1))).
Proof.
  intros n m.
  exact (Qle_to_QleT' 0
    (pint_integral (pei_list (n + 2 * m) (2 * n + 1)))
    (Qlt_le_weak 0 (pint_integral (pei_list (n + 2 * m) (2 * n + 1)))
       (QltT_to_Qlt 0 (pint_integral (pei_list (n + 2 * m) (2 * n + 1)))
          (pei_beta_pos (n + 2 * m) (2 * n + 1))))).
Qed.

(** bv_carrier_value: the truncated integral equals the series partial    *)
(** sum [sum_{m<=M} bv_term n m] (exact [QeqT]). *)
Theorem bv_carrier_value : forall n M : nat,
  pint_integral (bv_carrier n M) == sum_upto (Datatypes.S M) (fun m : nat => bv_term n m).
Proof.
  intros n M. induction M as [| m IH].
  - change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    change (sum_upto (Datatypes.S 0) (fun m0 : nat => bv_term n m0))
      with (0 + bv_term n 0)%Q.
    rewrite (qeqT_imp_qeq _ _
              (pint_integral_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                                   (pei_list (n + 2 * 0) (2 * n + 1)))).
    rewrite (qeqT_imp_qeq _ _ (pei_beta_value (n + 2 * 0) (2 * n + 1))).
    unfold bv_term.
    replace (n + 2 * 0)%nat with n%nat by lia.
    replace (3 * n + 2 * 0 + 2)%nat with (n + (2 * n + 1) + 1)%nat by lia.
    ring.
  - change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                    (bv_pad (bv_carrier n m))).
    change (sum_upto (Datatypes.S (Datatypes.S m)) (fun m0 : nat => bv_term n m0))
      with (sum_upto (Datatypes.S m) (fun m0 : nat => bv_term n m0)
              + bv_term n (Datatypes.S m))%Q.
    assert (HL : length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                    (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                 = length (bv_pad (bv_carrier n m))).
    { rewrite (RealSetoid.Id_eq _ _
                (pei_scale_length ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                  (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))),
              (RealSetoid.Id_eq _ _
                (pei_list_length (n + 2 * Datatypes.S m) (2 * n + 1))),
              bv_pad_length, bv_carrier_length. lia. }
    rewrite (qeqT_imp_qeq _ _ (pint_integral_add _ _ HL)).
    rewrite (bv_pad_int (bv_carrier n m)).
    rewrite (qeqT_imp_qeq _ _
              (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                   (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))).
    rewrite (qeqT_imp_qeq _ _
              (pei_beta_value (n + 2 * Datatypes.S m) (2 * n + 1))),
            IH. unfold bv_term.
    replace ((n + 2 * Datatypes.S m) + (2 * n + 1) + 1)%nat
      with (3 * n + 2 * Datatypes.S m + 2)%nat by lia.
    ring.
Qed.

(** bv_sum_mono: the truncated integral is monotone in M ([QleT']);       *)
(** assembled from [PintMono]'s [pm_scale_mono] and [pm_add_mono] with    *)
(** the same-value substitutions [pm_qle_wd_l] and [pm_qle_wd_r]. *)
Theorem bv_sum_mono : forall n M : nat,
  QleT' (pint_integral (bv_carrier n M))
        (pint_integral (bv_carrier n (Datatypes.S M))).
Proof.
  intros n M.
  change (pint_integral (bv_carrier n (Datatypes.S M)))
    with (pint_integral (pint_add
             (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                         (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
             (bv_pad (bv_carrier n M)))).
  assert (Hlen : length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                    (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
                 = length (bv_pad (bv_carrier n M))).
  { rewrite pei_scale_length, pei_list_length, bv_pad_length, bv_carrier_length. lia. }
  assert (HId1 : Id (length (bv_zeros (3 * n + 2 * M + 2 + 2)))
                    (length (bv_pad (bv_carrier n M)))).
  { rewrite bv_zeros_length, bv_pad_length, bv_carrier_length. reflexivity. }
  assert (HId2 : Id (length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                        (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
                    (length (bv_pad (bv_carrier n M)))).
  { rewrite <- Hlen. reflexivity. }
  (* intermediate assertion HleX: [0 <= C(n+M,n) * integral              *)
  (* t^{n+2M} (1-t)^{2n+1}], via [bv_c_pos_le], [bv_pos_cint] and         *)
  (* [pm_scale_mono]. *)
  assert (HleX : QleT' 0 (pint_integral
                    (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))).
  { apply (pm_qle_wd_r
             (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
               pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)
             (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                        (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
             0%Q).
    - apply Qeq_sym. apply qeqT_imp_qeq.
      apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
    - apply (pm_qle_wd_l
               (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                          (bv_zeros (3 * n + 2 * M + 2 + 2))))
               0%Q
               (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                 pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)).
      + transitivity (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                       pint_integral (bv_zeros (3 * n + 2 * M + 2 + 2)))%Q).
        * apply qeqT_imp_qeq.
          apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                     (bv_zeros (3 * n + 2 * M + 2 + 2))).
        * rewrite bv_zeros_int0. apply Qmult_0_r.
      + apply (pm_qle_wd_r
                 (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                            (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
                 (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                   pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)
                 (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                            (bv_zeros (3 * n + 2 * M + 2 + 2))))).
        * apply qeqT_imp_qeq.
          apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                     (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
        * apply (pm_scale_mono ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                   (bv_zeros (3 * n + 2 * M + 2 + 2))
                   (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
          -- apply bv_c_pos_le.
          -- apply (pm_qle_wd_l 0%Q _ _).
             ++ apply Qeq_sym. apply bv_zeros_int0.
             ++ apply bv_pos_cint. }
  (* intermediate assertion Hmove: the integral of [bv_zeros] plus       *)
  (* [bv_pad (bv_carrier n M)] equals [pint_integral (bv_carrier n M)]. *)
  assert (Hmove : pint_integral (pint_add (bv_zeros (3 * n + 2 * M + 2 + 2))
                                          (bv_pad (bv_carrier n M)))
                 == pint_integral (bv_carrier n M)).
  { assert (HLz : length (bv_zeros (3 * n + 2 * M + 2 + 2))
                  = length (bv_pad (bv_carrier n M)))
      by (rewrite bv_zeros_length, bv_pad_length, bv_carrier_length; reflexivity).
    rewrite (qeqT_imp_qeq _ _ (pint_integral_add _ _ HLz)).
    rewrite bv_zeros_int0, bv_pad_int. ring. }
  apply (pm_qle_wd_l
           (pint_integral (pint_add (bv_zeros (3 * n + 2 * M + 2 + 2))
                                    (bv_pad (bv_carrier n M))))
           (pint_integral (bv_carrier n M))
           (pint_integral (pint_add
                (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                            (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
                (bv_pad (bv_carrier n M))))).
  - exact Hmove.
  - apply (pm_add_mono (bv_zeros (3 * n + 2 * M + 2 + 2))
             (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                         (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
             (bv_pad (bv_carrier n M)) (bv_pad (bv_carrier n M))).
    + exact HId1.
    + exact HId2.
    + apply (pm_qle_wd_l 0%Q _ _).
      * apply Qeq_sym. apply bv_zeros_int0.
      * exact HleX.
    + apply qleT'_refl.
Qed.

(* bv_sum_upto_pos: the partial sum is strictly positive (induction on M; *)
(* from [bv_term_pos] and [pei_lt_le_plus]). *)
Lemma bv_sum_upto_pos : forall n M : nat,
  QltT 0 (sum_upto (Datatypes.S M) (fun m : nat => bv_term n m)).
Proof.
  intros n. induction M as [| m IH].
  - change (sum_upto (Datatypes.S 0) (fun m0 : nat => bv_term n m0))
      with (0 + bv_term n 0)%Q.
    apply (pei_qeq_lt (bv_term n 0) (0 + bv_term n 0)%Q 0%Q).
    + apply qeq_imp_qeqT. ring.
    + exact (bv_term_pos n 0).
  - change (sum_upto (Datatypes.S (Datatypes.S m)) (fun m0 : nat => bv_term n m0))
      with (sum_upto (Datatypes.S m) (fun m0 : nat => bv_term n m0)
              + bv_term n (Datatypes.S m))%Q.
    apply pei_lt_le_plus.
    + exact IH.
    + apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt. apply bv_term_pos.
Qed.

(** bv_sum_pos: the truncated integral is strictly positive — rewrite to  *)
(** the partial sum by [bv_carrier_value], then apply [bv_sum_upto_pos]. *)
Theorem bv_sum_pos : forall n M : nat,
  QltT 0 (pint_integral (bv_carrier n M)).
Proof.
  intros n M.
  apply (pei_qeq_lt (sum_upto (Datatypes.S M) (fun m : nat => bv_term n m))
                    (pint_integral (bv_carrier n M)) 0%Q).
  - apply qeq_imp_qeqT. apply Qeq_sym.
    exact (bv_carrier_value n M).
  - exact (bv_sum_upto_pos n M).
Qed.

(* Section D. Discrete core of the ln2 coefficients:                     *)
(* [bv_delannoy_eq_qtilde] (the ascending-power Delannoy sum equals      *)
(* [q~_n]).  [bv_D_asc n == sum_{a<=n} C(n,a)^2 * 2^a] (reordered via    *)
(* [bk_psd_ext] and [bk_Qn_sym]); coefficient identity:                  *)
(* [u^n](u-1)^n(2-u)^n = sum_{a+b=n} C(n,a) C(n,b) 2^{n-b} (-1)^{n-a+b}; *)
(* at [b = n-a] the sign is [(-1)^{2n-2a} = 1], hence the sum is         *)
(* [sum_a C(n,a)^2 2^a = D_n = q~_n]. *)

Definition bv_D_asc (n : nat) : nat :=
  bk_psd (fun k => bkC n (n - k) * bkC n (n - k)) (Datatypes.S n).

Theorem bv_delannoy_eq_qtilde : forall n : nat,
  QeqT ((Z.of_nat (bv_D_asc n) # 1)%Q) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n. apply qeq_imp_qeqT. unfold bv_D_asc.
  assert (H : Id (bk_psd (fun k => bkC n (n - k) * bkC n (n - k)) (Datatypes.S n))
                 (bk_psd (fun k => bkC n k * bkC n k) (Datatypes.S n))).
  { apply bk_psd_ext. intros k Hk.
    assert (Hle : k <= n) by (pose proof (NatLe_drop _ _ Hk); lia).
    pose proof (RealSetoid.Id_eq _ _ (bk_Qn_sym n k (NatLe_lift _ _ Hle))) as Hq.
    rewrite <- Hq. reflexivity. }
  pose proof (RealSetoid.Id_eq _ _ H) as Hp.
  rewrite Hp. reflexivity.
Qed.

(* Section E. The numerator closed form [bv_p] (signed sum of Laurent    *)
(* coefficients) and the numerical anchor group:                         *)
(* [p_n = - sum_{j <> n, j <= 2n} c_j * (2^{j-n} - 1)/(j - n)]           *)
(* (anchor values of p: 0, 2, 9, 131/3). *)

Fixpoint bv_negpow (k : nat) : Q :=
  match k with
  | 0 => 1%Q
  | Datatypes.S k' => (- bv_negpow k')%Q
  end.

(* signed powers of 2 (exponent in Z). *)
Definition bv_q2 (k : Z) : Q :=
  match Z.leb 0 k with
  | true => q_pow (2 # 1)%Q (Z.to_nat k)
  | false => 1%Q / q_pow (2 # 1)%Q (Z.to_nat (Z.opp k))
  end.

(* Laurent coefficient [c_j = (-1)^{n+j} * sum_{a<=j, a<=n, j-a<=n}      *)
(* C(n,a) C(n,j-a) 2^{n-(j-a)}]. *)
Definition bv_c (n j : nat) : Q :=
  bv_negpow (n + j) *
  bk_psQ (fun a : nat =>
            if andb (Nat.leb a n) (Nat.leb (j - a) n)
            then ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) *
                  q_pow (2 # 1)%Q (n - (j - a)))%Q
            else 0%Q)
         (Datatypes.S j) 1%Q.

(* bv_p: the numerator closed form (see Section E; signed sum of Laurent *)
(* coefficients). *)
Definition bv_p (n : nat) : Q :=
  (- bk_psQ (fun j : nat =>
               if Nat.eqb j n then 0%Q
               else (bv_c n j *
                     ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                      ((Z.of_nat j - Z.of_nat n)%Z # 1))%Q))
            (Datatypes.S (2 * n)) 1%Q)%Q.

(* the genuinely normalized approximant [x_n := p_n / q~_n] (canonical   *)
(* form: no power of 2). *)
Definition bv_x (n : nat) : Q := bv_p n / (Z.of_nat (bk_Qn_qtilde n) # 1)%Q.

(* bv_x2pow: the power-of-2 normalized form [x''_n := p_n / (2^n *       *)
(* q~_n)], not equivalent to the genuinely normalized form (see           *)
(* [bv_x2pow_sep1]). *)
Definition bv_x2pow (n : nat) : Q :=
  bv_p n / (q_pow (2 # 1)%Q n * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q.

(* ---- numerical anchor group (each anchor decided exactly by           *)
(* vm_compute) ---- *)

Theorem bv_q1_anchor : QeqT ((Z.of_nat (bk_Qn_qtilde 1) # 1)%Q) (3 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c11_anchor : QeqT (bv_c 1 1) (3 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c22_anchor : QeqT (bv_c 2 2) (13 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c33_anchor : QeqT (bv_c 3 3) (63 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p0_anchor : QeqT (bv_p 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p1_anchor : QeqT (bv_p 1) (2 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p2_anchor : QeqT (bv_p 2) (9 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p3_anchor : QeqT (bv_p 3) (131 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x0_anchor : QeqT (bv_x 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x1_anchor : QeqT (bv_x 1) (2 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x2_anchor : QeqT (bv_x 2) (9 # 13)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* cross-variant check: [bv_p 2 == 9], consistent with the               *)
(* original-variant relation [r_2 == 2^3 * p_2 == 72]. *)
Theorem bv_cross2_anchor : QeqT ((bv_p 2 * (Z.of_nat 8 # 1))%Q) (72 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(** bv_x2pow_sep1: the separating witness — [bv_x2pow 1 == 1/3 < 2/3 ==   *)
(** bv_x 1] ([QltT], Set layer). *)
Theorem bv_x2pow_sep1 : QltT (bv_x2pow 1) (bv_x 1).
Proof. vm_compute. reflexivity. Qed.

(* Assumption audit: the Print Assumptions outputs below should report   *)
(* zero dependencies (admission re-check). *)

Print Assumptions bv_delannoy_eq_qtilde.
Print Assumptions bv_term_pos.
Print Assumptions bv_carrier_eval.
Print Assumptions bv_carrier_value.
Print Assumptions bv_sum_mono.
Print Assumptions bv_sum_pos.
Print Assumptions bv_p3_anchor.
Print Assumptions bv_x2pow_sep1.
(* ================= Section 4. The pi_pow3_ge1 family ================= *)
From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia Lists.List.

Open Scope nat_scope.

(* Section A. Power and positivity lemmas (nat layer). *)

Lemma pi_pow3_ge1 : forall n : nat, 1 <= 3 ^ n.
Proof.
  induction n as [| n IH].
  - cbn [Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma pi_pow4b : forall n : nat, 4 ^ n = 2 ^ n * 2 ^ n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite !Nat.pow_succ_r'. rewrite IH. ring.
Qed.

Lemma pi_pow8 : forall n : nat, 8 ^ n = 4 ^ n * 2 ^ n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite !Nat.pow_succ_r'. rewrite IH. ring.
Qed.

(* closed form of [bk_psd] with a constant coefficient: [sum_{k<N}       *)
(* c * 2^{N-1-k} = c * (2^N - 1)]. *)
Lemma pi_psd_const : forall (N c : nat),
  bk_psd (fun _ : nat => c) N = c * (2 ^ N - 1).
Proof.
  induction N as [| N IH]; intro c.
  - cbn [bk_psd Nat.pow]. lia.
  - cbn [bk_psd]. rewrite IH. rewrite Nat.pow_succ_r'.
    pose proof (hl_le_t_to_le 1 (2 ^ N) (hl_pow2_ge1 N)). nia.
Qed.

(* Section B. The dual-Pascal bridge [bkC <-> hl_binom]: [pi_bkC_hl]. *)

Lemma pi_bkC_hl : forall n k : nat, bkC n k = hl_binom n k.
Proof.
  induction n as [| n IH]; intro k.
  - destruct k as [| k'].
    + reflexivity.
    + reflexivity.
  - destruct k as [| k'].
    + reflexivity.
    + cbn [bkC]. rewrite (IH k'). rewrite (IH (Datatypes.S k')).
      symmetry. apply hl_id_eq. exact (hl_binom_S n k').
Qed.

(* Section C. Q-layer multiplication/division micro-lemmas (field laws of *)
(* the Q domain; all nonzero premises explicit). *)

(* fraction times integer with a positive denominator: the denominators  *)
(* merge without unfolding the [Qinv] component. *)
Lemma pi_Qden_cancel : forall (u : Z) (p : positive),
  ((u # p) * ((Z.pos p) # 1))%Q == (u # 1)%Q.
Proof.
  intros u p. unfold Qeq. cbn [Qnum Qden Qmult]. rewrite Pos.mul_1_r. ring.
Qed.

Lemma pi_Qneq0_Zpos : forall p : positive, ~ (((Z.pos p) # 1) == 0)%Q.
Proof.
  intros p Hc. unfold Qeq in Hc. vm_compute in Hc. discriminate Hc.
Qed.

Lemma pi_Qneq0_nat : forall m : nat, 1 <= m -> ~ ((Z.of_nat m # 1) == 0)%Q.
Proof.
  intros m Hm Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc. lia.
Qed.

(* pi_Qmul_cancel_r_to: right cancellation in the Q domain (from the     *)
(* stdlib [Qmult_inv_r]). *)
Lemma pi_Qmul_cancel_r_to : forall a b c : Q,
  ~ (c == 0)%Q -> a * c == b * c -> a == b.
Proof.
  intros a b c Hc H.
  assert (Hc1 : (c * (/ c))%Q == 1%Q) by (apply Qmult_inv_r; exact Hc).
  transitivity (((a * c) * (/ c)))%Q.
  - rewrite <- Qmult_assoc, Hc1. symmetry. apply Qmult_1_r.
  - rewrite H. rewrite <- Qmult_assoc, Hc1. apply Qmult_1_r.
Qed.

(* one-sided introduction of a division equation: [y <> 0] with          *)
(* [x == b*y] entails [x/y == b]. *)
Lemma pi_Qdiv_eq_intro : forall x y b : Q,
  ~ (y == 0)%Q -> x == b * y -> x / y == b.
Proof.
  intros x y b Hy Hxy. unfold Qdiv. rewrite Hxy.
  assert (Hy1 : (y * (/ y))%Q == 1%Q) by (apply Qmult_inv_r; exact Hy).
  rewrite <- Qmult_assoc, Hy1. apply Qmult_1_r.
Qed.

(* pi_Qmul_inv_r_eq: the division cross-equivalence (a field law of the  *)
(* Q domain). *)
Lemma pi_Qmul_inv_r_eq : forall x y z : Q,
  ~ (y == 0)%Q -> ((x * (/ y)) == z <-> x == z * y).
Proof.
  intros x y z Hy. split; intro H.
  - assert (Hy1 : (y * (/ y))%Q == 1%Q) by (apply Qmult_inv_r; exact Hy).
    transitivity (((x * (/ y)) * y))%Q.
    + rewrite <- Qmult_assoc. rewrite (Qmult_comm (/ y) y). rewrite Hy1.
      symmetry. apply Qmult_1_r.
    + rewrite H. reflexivity.
  - assert (Hy1 : (y * (/ y))%Q == 1%Q) by (apply Qmult_inv_r; exact Hy).
    rewrite H. rewrite <- Qmult_assoc, Hy1. apply Qmult_1_r.
Qed.

(* Section D. Divisibility quotient transport and the H_k integralization *)
(* main bridge: [pi_div_Qeq], [pi_hsum_spec]. *)

(* pi_div_Qeq: [j | D] entails [Q#D * (1/Q#j) == Q#(D/j)] (from           *)
(* [Nat.div_mul]). *)
Lemma pi_div_Qeq : forall (D j : nat), 1 <= j -> Nat.divide j D ->
  ((Z.of_nat D # 1) * ((1 # 1) / (Z.of_nat j # 1)))%Q
  == (Z.of_nat (D / j) # 1)%Q.
Proof.
  intros D j Hj Hd. destruct Hd as [c Hc].
  assert (Hj0 : ~ ((Z.of_nat j # 1) == 0)%Q) by (apply pi_Qneq0_nat; exact Hj).
  assert (Hdq : D / j = c).
  { rewrite Hc. apply Nat.div_mul. lia. }
  rewrite Hdq. unfold Qdiv.
  transitivity ((((Z.of_nat D # 1) * (1 # 1)) * (/ (Z.of_nat j # 1))))%Q.
  - ring.
  - apply (proj2 (pi_Qmul_inv_r_eq _ _ _ Hj0)).
    rewrite Qmult_1_r.
    rewrite Hc.
    rewrite (qeqT_imp_qeq _ _ (bk_Qmul_nat c j)).
    reflexivity.
Qed.

(* integralization-sum carrier: [pi_hsum D k = sum_{j=1}^{k} D/j] (D      *)
(* fixed, the quotient sum taken over a varying index). *)
Fixpoint pi_hsum (D k : nat) : nat :=
  match k with
  | 0 => 0
  | Datatypes.S m => pi_hsum D m + D / Datatypes.S m
  end.

(* pi_hsum_spec: [D_n * H_k == Q#(sum_{j<=k} D_n/j)]; induction on k,     *)
(* each term via [hl_lcm_divide_all] and [pi_div_Qeq]. *)
Lemma pi_hsum_spec : forall (n k : nat), k <= n ->
  ((Z.of_nat (hl_lcm_upto n) # 1) * bk_H k)%Q
  == (Z.of_nat (pi_hsum (hl_lcm_upto n) k) # 1)%Q.
Proof.
  intros n k. induction k as [| k IH]; intro Hk.
  - cbn [bk_H pi_hsum]. ring.
  - assert (Hle : k <= n) by lia.
    specialize (IH Hle).
    cbn [bk_H pi_hsum].
    rewrite Qmult_plus_distr_r.
    rewrite IH.
    assert (H1 : 1 <= Datatypes.S k) by lia.
    assert (Hd := hl_lcm_divide_all n (Datatypes.S k) H1 Hk).
    assert (Hdv := pi_div_Qeq (hl_lcm_upto n) (Datatypes.S k) H1 Hd).
    rewrite Hdv.
    exact (qeqT_imp_qeq _ _
            (bk_Qadd_nat (pi_hsum (hl_lcm_upto n) k)
                         (hl_lcm_upto n / Datatypes.S k))).
Qed.

(* Section E. Pointwise extensionality and constant extraction for       *)
(* [bk_psQ]: [pi_psQ_ext], [pi_psQ_mul]. *)

Lemma pi_psQ_ext : forall (N : nat) (f g : nat -> Q) (z : Q),
  (forall k : nat, k < N -> f k == g k) -> bk_psQ f N z == bk_psQ g N z.
Proof.
  induction N as [| N IH]; intros f g z H.
  - reflexivity.
  - cbn [bk_psQ].
    rewrite (IH f g z) by (intros k Hk; apply H; lia).
    rewrite (H N) by lia.
    reflexivity.
Qed.

Lemma pi_psQ_mul : forall (N : nat) (c : Q) (f : nat -> Q) (z : Q),
  bk_psQ (fun k => (c * f k)%Q) N z == (c * bk_psQ f N z)%Q.
Proof.
  induction N as [| N IH]; intros c f z.
  - cbn [bk_psQ]. ring.
  - cbn [bk_psQ]. rewrite IH. ring.
Qed.

(* Section F. The p-tilde integralization main theorem [pi_Pn_int]       *)
(* (coefficients taken as [C^2 * D_n]). *)

(* coefficient integralization (pointwise): [(Z#(C^2 * D_n)) * H_k ==    *)
(* Z#(C^2 * S_k)] with [S_k := pi_hsum D_n k]. *)
Lemma pi_coeff_Zeq : forall (n k : nat), k <= n ->
  ((Z.of_nat (bkC n k * bkC n k * hl_lcm_upto n) # 1) * bk_H k)%Q
  == (Z.of_nat (bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k) # 1)%Q.
Proof.
  intros n k Hk.
  rewrite <- (qeqT_imp_qeq _ _
               (bk_Qmul_nat (bkC n k * bkC n k) (hl_lcm_upto n))).
  transitivity ((Z.of_nat (bkC n k * bkC n k) # 1)
                  * ((Z.of_nat (hl_lcm_upto n) # 1) * bk_H k))%Q.
  - ring.
  - rewrite (pi_hsum_spec n k Hk).
    exact (qeqT_imp_qeq _ _
            (bk_Qmul_nat (bkC n k * bkC n k)
                         (pi_hsum (hl_lcm_upto n) k))).
Qed.

(* pi_ptilde: [p~_n := sum_{k<=n} C(n,k)^2 * S_k] with [S_k := pi_hsum    *)
(* D_n k]. *)
Definition pi_ptilde (n : nat) : nat :=
  bk_psd (fun k => bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k)
         (Datatypes.S n).

(* pi_Pn_eval_eq: the Qeq form of [bk_Pn_eval] (converted through        *)
(* [qeqT_imp_qeq], for rewriting == goals). *)
Lemma pi_Pn_eval_eq : forall (n : nat) (z : Q),
  bkQ (bk_Pn_list n) z
  == bk_psQ (fun k : nat => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
          (Datatypes.S n) z.
Proof.
  intros n z.
  apply qeqT_imp_qeq.
  apply bk_Pn_eval.
Qed.

(* half-integer closed form: [D_n * 2^n * P_n(1/2) == Q#p~_n] (with       *)
(* [p~_n] carried by nat). *)
Lemma pi_Pn_half : forall n : nat,
  ((Z.of_nat (hl_lcm_upto n) # 1)
     * (q_pow (2 # 1)%Q n * bkQ (bk_Pn_list n) (1 # 2)%Q))%Q
  == (Z.of_nat (pi_ptilde n) # 1)%Q.
Proof.
  intro n. unfold pi_ptilde.
  rewrite (pi_Pn_eval_eq n (1 # 2)%Q).
  assert (Hmul := pi_psQ_mul (Datatypes.S n)
                    (Z.of_nat (hl_lcm_upto n) # 1)%Q
                    (fun k : nat => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
                    (1 # 2)%Q).
  transitivity ((q_pow (2 # 1)%Q n
    * ((Z.of_nat (hl_lcm_upto n) # 1)
         * bk_psQ (fun k : nat => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
               (Datatypes.S n) (1 # 2)%Q))%Q).
  - ring.
  - rewrite <- Hmul.
    assert (Hpt : forall k : nat, k < Datatypes.S n ->
        (((Z.of_nat (hl_lcm_upto n) # 1)
            * ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k))%Q)
        == ((Z.of_nat (bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k) # 1))%Q).
    { intro k. intro Hk. assert (Hle : k <= n) by lia.
      transitivity ((Z.of_nat (bkC n k * bkC n k) # 1)
                      * ((Z.of_nat (hl_lcm_upto n) # 1) * bk_H k))%Q.
      - ring.
      - rewrite (pi_hsum_spec n k Hle).
        exact (qeqT_imp_qeq _ _
                (bk_Qmul_nat (bkC n k * bkC n k)
                             (pi_hsum (hl_lcm_upto n) k))). }
    rewrite (pi_psQ_ext (Datatypes.S n) _ _ _ Hpt).
    exact (qeqT_imp_qeq _ _
            (bk_half_psd n
               (fun k : nat => bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k))).
Qed.

(* pi_Pn_int: the sigT integrality witness of [p~_n in Z] (Set face). *)

Theorem pi_Pn_int : forall n : nat,
  sigT (fun z : Z =>
    QeqT (q_pow (2 # 1)%Q n
            * ((Z.of_nat (hl_lcm_upto n) # 1) * bkQ (bk_Pn_list n) (1 # 2)%Q)%Q)
         ((z # 1)%Q)).
Proof.
  intro n. exists (Z.of_nat (pi_ptilde n)). apply qeq_imp_qeqT.
  transitivity ((Z.of_nat (hl_lcm_upto n) # 1)
                  * (q_pow (2 # 1)%Q n * bkQ (bk_Pn_list n) (1 # 2)%Q))%Q.
  - ring.
  - apply pi_Pn_half.
Qed.

(* Section G. [q~_n <= (n+1) * 8^n]: [pi_Qn_le_8pow] ([QleT'] Set face). *)

Theorem pi_Qn_le_8pow : forall n : nat,
  QleT' ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q)
        ((Z.of_nat (Datatypes.S n * 8 ^ n) # 1)%Q).
Proof.
  intro n. apply bk_Qle_nat. apply NatLe_lift.
  unfold bk_Qn_qtilde.
  assert (Hpt : forall k : nat, k < Datatypes.S n ->
      bkC n k * bkC n k <= 4 ^ n).
  { intro k. intro Hk.
    pose proof (hl_le_t_to_le (hl_binom n k) (2 ^ n)
                  (hl_binom_le_pow2 n k)) as Hb.
    rewrite <- (pi_bkC_hl n k) in Hb.
    rewrite (pi_pow4b n).
    nia. }
  pose proof (bk_psd_mono (Datatypes.S n)
               (fun k => bkC n k * bkC n k)
               (fun _ : nat => 4 ^ n)
               (fun k Hk => NatLe_lift _ _ (Hpt k (NatLe_drop _ _ Hk)))) as Hmono.
  rewrite pi_psd_const in Hmono.
  rewrite Nat.pow_succ_r' in Hmono.
  destruct n as [| n'].
  - cbn [bk_psd bkC Nat.pow] in *. lia.
  - assert (Hs1 : 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n' - 1)
                  <= 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n'))
      by (apply Nat.mul_le_mono_l; lia).
    assert (Hs2 : 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n')
                  = 2 * (4 ^ Datatypes.S n' * 2 ^ Datatypes.S n')) by ring.
    assert (Hs3 : 2 * (4 ^ Datatypes.S n' * 2 ^ Datatypes.S n')
                  <= Datatypes.S (Datatypes.S n') * (4 ^ Datatypes.S n' * 2 ^ Datatypes.S n')).
    { apply Nat.mul_le_mono_r. lia. }
    rewrite (pi_pow8 (Datatypes.S n')).
    apply Nat.le_trans with
      (m := 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n' - 1)).
    + pose proof (NatLe_drop _ _ Hmono) as HmonoL. exact HmonoL.
    + apply Nat.le_trans with
        (m := 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n')).
      * exact Hs1.
      * rewrite Hs2. exact Hs3.
Qed.

(* Section H. The explicit denominator of [x'_n]: [pi_x_n_frac] and the  *)
(* sigT weak face [pi_den_divide]. *)

Lemma pi_lcm_pos : forall a b : nat, 1 <= a -> 1 <= b -> 1 <= Nat.lcm a b.
Proof.
  intros a b Ha Hb. unfold Nat.lcm.
  destruct (Nat.gcd a b) as [| g] eqn:Eg.
  - exfalso.
    destruct (Nat.gcd_divide_r a b) as [q Hq].
    rewrite Eg, Nat.mul_0_r in Hq. lia.
  - assert (Hbg : 0 < b / Datatypes.S g).
    { apply Nat.div_str_pos.
      destruct (Nat.gcd_divide_r a b) as [q Hq]. rewrite Eg in Hq.
      destruct q as [| q'].
      - lia.
      - split.
        + lia.
        + assert (Hg1 : Datatypes.S g * 1 <= Datatypes.S g * Datatypes.S q')
            by (apply Nat.mul_le_mono_l; lia).
          rewrite Nat.mul_1_r in Hg1.
          rewrite Hq, Nat.mul_comm. exact Hg1. }
    nia.
Qed.

Lemma pi_lcm_upto_pos : forall n : nat, 1 <= hl_lcm_upto n.
Proof.
  induction n as [| n IH].
  - cbn [hl_lcm_upto]. lia.
  - cbn [hl_lcm_upto]. apply pi_lcm_pos.
    + exact IH.
    + lia.
Qed.

Lemma pi_qtilde_pos : forall n : nat, 1 <= bk_Qn_qtilde n.
Proof.
  intro n. pose proof (NatLe_drop _ _ (bk_Qn_ge_3pow_nat n)).
    pose proof (pi_pow3_ge1 n). lia.
Qed.

(* pi_Qn_nz: [2 * Q_n(1/2)] is nonzero (from [bk_Qn_half_closed] and     *)
(* [q~_n >= 3^n > 0]). *)
Lemma pi_Qn_nz : forall n : nat,
  ~ (((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q) == 0)%Q.
Proof.
  intro n. intro H0.
  assert (HQ : bkQ (bk_Qn_list n) (1 # 2)%Q == 0%Q).
  { apply (pi_Qmul_cancel_r_to (bkQ (bk_Qn_list n) (1 # 2)%Q) 0%Q (2 # 1)%Q).
    - apply pi_Qneq0_Zpos.
    - rewrite (Qmult_comm (bkQ (bk_Qn_list n) (1 # 2)%Q) (2 # 1)%Q).
      rewrite Qmult_0_l. exact H0. }
  assert (Hh := qeqT_imp_qeq _ _ (bk_Qn_half_closed n)).
  rewrite HQ in Hh. rewrite Qmult_0_r in Hh.
  pose proof (NatLe_drop _ _ (bk_Qn_ge_3pow_nat n)).
  unfold Qeq in Hh. cbn [Qnum Qden] in Hh.
  rewrite !Z.mul_1_r in Hh.
  replace 0%Z with (Z.of_nat 0) in Hh by reflexivity.
  apply Znat.Nat2Z.inj in Hh.
  pose proof (pi_pow3_ge1 n).
  lia.
Qed.

(* cross identity: [P_n(1/2) * (2 * D_n * q~_n) == p~_n * (2 *           *)
(* Q_n(1/2))] (pure ring reasoning in the Q domain). *)
Lemma pi_x_cross : forall n : nat,
  (bkQ (bk_Pn_list n) (1 # 2)%Q
     * (Z.of_nat (2 * hl_lcm_upto n * bk_Qn_qtilde n) # 1))%Q
  == ((Z.of_nat (pi_ptilde n) # 1)
        * ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q.
Proof.
  intro n.
  replace (2 # 1)%Q with ((Z.of_nat 2 # 1)%Q) by reflexivity.
  rewrite <- (qeqT_imp_qeq _ _
               (bk_Qmul_nat (2 * hl_lcm_upto n) (bk_Qn_qtilde n))).
  rewrite <- (qeqT_imp_qeq _ _ (bk_Qmul_nat 2 (hl_lcm_upto n))).
  rewrite <- (qeqT_imp_qeq _ _ (bk_Qn_half_closed n)).
  rewrite <- (pi_Pn_half n).
  ring.
Qed.

(* pi_x_n_frac: [x'_n == p~_n / (2 * D_n * q~_n)] with the denominator   *)
(* constructed explicitly.                                               *)
(* Pitfall note: [Z.pos (Pos.of_nat M)] evaluates to [M+1] (no zero      *)
(* offset), so stating with it would give a false statement;             *)
(* [Pos.of_succ_nat (Nat.pred M)] evaluates to exactly [M] (definitional *)
(* conversion). *)
Theorem pi_x_n_frac : forall n : nat,
  QeqT (bkQ (bk_Pn_list n) (1 # 2)%Q
          / ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q
       ((Z.of_nat (pi_ptilde n)
           # Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))%Q).
Proof.
  intro n. apply qeq_imp_qeqT.
  assert (Hm1 : 1 <= 2 * hl_lcm_upto n * bk_Qn_qtilde n)
    by (pose proof (pi_lcm_upto_pos n); pose proof (pi_qtilde_pos n); lia).
  assert (Hpm : Z.pos (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))
              = Z.of_nat (2 * hl_lcm_upto n * bk_Qn_qtilde n)).
  { assert (Hs : Datatypes.S (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n))
               = 2 * hl_lcm_upto n * bk_Qn_qtilde n) by lia.
    transitivity (Z.of_nat (Datatypes.S (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))).
    - reflexivity.
    - rewrite Hs. reflexivity. }
  apply pi_Qdiv_eq_intro.
  - apply pi_Qn_nz.
  - apply (pi_Qmul_cancel_r_to (bkQ (bk_Pn_list n) (1 # 2)%Q)
             (((Z.of_nat (pi_ptilde n)
                  # Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))
                 * ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q)
             ((Z.pos (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n))) # 1)%Q)).
    + apply pi_Qneq0_Zpos.
    + rewrite Hpm.
      transitivity ((Z.of_nat (pi_ptilde n) # 1)
                      * ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q.
      * exact (pi_x_cross n).
      * rewrite <- (pi_Qden_cancel (Z.of_nat (pi_ptilde n))
                          (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))).
        rewrite Hpm.
        ring.
Qed.

(* pi_den_divide: there is a positive denominator [p] with [x'_n ==       *)
(* p~_n / p] (sigT weak face). *)
Theorem pi_den_divide : forall n : nat,
  sigT (fun p : positive =>
    QeqT (bkQ (bk_Pn_list n) (1 # 2)%Q
            / ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q
         ((Z.of_nat (pi_ptilde n) # p)%Q)).
Proof.
  intro n.
  exists (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n))).
  apply pi_x_n_frac.
Qed.

(* Assumption audit: the Print Assumptions outputs below should report   *)
(* zero dependencies (admission re-check). *)

Print Assumptions pi_bkC_hl.
Print Assumptions pi_div_Qeq.
Print Assumptions pi_hsum_spec.
Print Assumptions pi_psQ_ext.
Print Assumptions pi_Pn_int.
Print Assumptions pi_Qn_le_8pow.
Print Assumptions pi_x_n_frac.
Print Assumptions pi_den_divide.
(* ================= Section 5. The bkC family ================= *)
From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.

(* QArith leaks Q_scope (bare numerals would be read as Q constructors); *)
(* restore nat_scope priority. *)
Open Scope nat_scope.

(* Section A. The nat-layer binomial coefficient (Pascal recursion) and  *)
(* the symmetry lemma. *)

(* Pascal-recursive binomial coefficient [C(n,k)] (the name [bkC] avoids *)
(* a shadowing clash with C). *)
Fixpoint bkC (n k : nat) : nat :=
  match n with
  | 0 => match k with
         | 0 => 1
         | Datatypes.S _ => 0
         end
  | Datatypes.S n' =>
      match k with
      | 0 => 1
      | Datatypes.S k' => bkC n' k' + bkC n' (Datatypes.S k')
      end
  end.

(* out-of-range lemma: [C(n,k) = 0] when [k > n]. *)
Lemma bkC_out : forall n k : nat, n < k -> bkC n k = 0.
Proof.
  induction n as [| n IH]; intros k Hk.
  - destruct k as [| k'].
    + lia.
    + reflexivity.
  - destruct k as [| k'].
    + lia.
    + cbn [bkC].
      rewrite (IH k') by lia.
      rewrite (IH (Datatypes.S k')) by lia.
      reflexivity.
Qed.

(* diagonal lemma: [C(n,n) = 1]. *)
Lemma bkC_diag : forall n : nat, bkC n n = 1.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [bkC].
    rewrite IH.
    rewrite (bkC_out n (Datatypes.S n)) by lia.
    reflexivity.
Qed.

(* positivity lemma: [C(n,k) >= 1] when [k <= n]. *)
Lemma bkC_pos : forall n k : nat, k <= n -> 1 <= bkC n k.
Proof.
  induction n as [| n IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. cbn [bkC]. lia.
  - destruct k as [| k'].
    + cbn [bkC]. lia.
    + cbn [bkC].
      destruct (le_lt_dec (Datatypes.S k') n) as [Hle | Hlt].
      * assert (H1 : 1 <= bkC n k') by (apply IH; lia).
        assert (H2 : 1 <= bkC n (Datatypes.S k')) by (apply IH; lia).
        lia.
      * assert (Hk' : k' = n) by lia. subst k'.
        rewrite (bkC_out n (Datatypes.S n)) by lia.
        assert (H1 : 1 <= bkC n n) by (apply IH; lia).
        lia.
Qed.

(* pointwise Pascal identity: [shift(C n)(k) + C(n,k) = C(S n,k)] (all k *)
(* branches definitional). *)
Lemma bkC_pascal_shift : forall n k : nat,
  (match k with
   | 0 => 0
   | Datatypes.S j => bkC n j
   end) + bkC n k = bkC (Datatypes.S n) k.
Proof.
  intros n k. destruct k as [| j].
  - destruct n as [| n']; reflexivity.
  - cbn [bkC]. reflexivity.
Qed.

(* symmetry lemma: [C(n,k) = C(n,n-k)] (consumed by the later identity   *)
(* inductions). *)
Lemma bk_Qn_sym : forall n k : nat, k <= n -> bkC n k = bkC n (n - k).
Proof.
  induction n as [| n IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. reflexivity.
  - destruct k as [| k'].
    + replace (Datatypes.S n - 0) with (Datatypes.S n) by lia.
      rewrite (bkC_diag (Datatypes.S n)). reflexivity.
    + replace (Datatypes.S n - Datatypes.S k') with (n - k') by lia.
      destruct (le_lt_dec (Datatypes.S k') n) as [Hle | Hlt].
      * assert (H1 : bkC n k' = bkC n (n - k')) by (apply IH; lia).
        assert (H2 : bkC n (Datatypes.S k') = bkC n (n - Datatypes.S k'))
          by (apply IH; lia).
        assert (Hn1 : n - k' = Datatypes.S (n - Datatypes.S k')) by lia.
        rewrite Hn1 in H1.
        rewrite Hn1.
        cbn [bkC]. lia.
      * assert (Hk' : k' = n) by lia. subst k'.
        replace (n - n) with 0 by lia.
        rewrite (bkC_diag (Datatypes.S n)).
        reflexivity.
Qed.

(* Section B. The nat-layer descending-power weighted sum [bk_psd] and   *)
(* the binomial theorem for [(1+2)^n].                                   *)
(*   [bk_psd f n = sum_{k<n} f(k) * 2^{n-1-k}]; the recursion            *)
(*   [bk_psd f (S m) = 2 * bk_psd f m + f m] (the descending-power step  *)
(*   is exactly a doubling). *)

Fixpoint bk_psd (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => 0
  | Datatypes.S m => 2 * bk_psd f m + f m
  end.

Lemma bk_psd_ext : forall (N : nat) (f g : nat -> nat),
  (forall k : nat, k < N -> f k = g k) -> bk_psd f N = bk_psd g N.
Proof.
  induction N as [| N IH]; intros f g H.
  - reflexivity.
  - cbn [bk_psd].
    rewrite (IH f g) by (intro k; intro Hk; apply H; lia).
    rewrite (H N) by lia.
    reflexivity.
Qed.

Lemma bk_psd_add : forall (N : nat) (f g : nat -> nat),
  bk_psd (fun k => f k + g k) N = bk_psd f N + bk_psd g N.
Proof.
  induction N as [| N IH]; intros f g.
  - reflexivity.
  - cbn [bk_psd]. rewrite IH. lia.
Qed.

(* shift lemma: shifting the coefficient row one place right (zero-padded *)
(* head) makes the sum equal the original sum one level down. *)
Lemma bk_psd_shift : forall (m : nat) (g : nat -> nat),
  bk_psd (fun k => match k with
                   | 0 => 0
                   | Datatypes.S j => g j
                   end) (Datatypes.S m) = bk_psd g m.
Proof.
  induction m as [| m IH]; intros g.
  - reflexivity.
  - assert (Hunf : bk_psd (fun k => match k with
                                    | 0 => 0
                                    | Datatypes.S j => g j
                                    end) (Datatypes.S (Datatypes.S m))
                 = 2 * bk_psd (fun k => match k with
                                        | 0 => 0
                                        | Datatypes.S j => g j
                                        end) (Datatypes.S m)
                   + g m)
      by reflexivity.
    rewrite Hunf, IH. reflexivity.
Qed.

(* descending-power binomial theorem: [sum_{k<=n} C(n,k) * 2^{n-k} =     *)
(* (1+2)^n = 3^n] (self-built; the stdlib carries no binomial theorem at  *)
(* this layer). *)
Lemma bk_psd_binom : forall n : nat,
  bk_psd (fun k => bkC n k) (Datatypes.S n) = 3 ^ n.
Proof.
  induction n as [| n IH].
  - cbn [bk_psd]. replace (2 * 0)%nat with 0%nat by lia. reflexivity.
  - replace (bk_psd (fun k => bkC (Datatypes.S n) k) (Datatypes.S (Datatypes.S n)))
      with (bk_psd (fun k => (match k with
                             | 0 => 0
                             | Datatypes.S j => bkC n j
                             end) + bkC n k) (Datatypes.S (Datatypes.S n)))
      by (apply bk_psd_ext; intro k; intro Hk; apply bkC_pascal_shift).
    rewrite bk_psd_add.
    assert (IH' : bk_psd (bkC n) (Datatypes.S n) = 3 ^ n) by exact IH.
    assert (Hsh : bk_psd (fun k => match k with
                                   | 0 => 0
                                   | Datatypes.S j => bkC n j
                                   end) (Datatypes.S (Datatypes.S n))
                = bk_psd (bkC n) (Datatypes.S n))
      by (apply (bk_psd_shift (Datatypes.S n) (bkC n))).
    assert (Hunf : bk_psd (bkC n) (Datatypes.S (Datatypes.S n))
                 = 2 * bk_psd (bkC n) (Datatypes.S n)
                   + bkC n (Datatypes.S n))
      by reflexivity.
    rewrite Hsh, Hunf, IH'.
    rewrite (bkC_out n (Datatypes.S n)) by lia.
    rewrite Nat.pow_succ_r'.
    lia.
Qed.

(* monotonicity lemma: pointwise [<=] entails [<=] of the sums. *)
Lemma bk_psd_mono : forall (N : nat) (f h : nat -> nat),
  (forall k : nat, k < N -> f k <= h k) -> bk_psd f N <= bk_psd h N.
Proof.
  induction N as [| N IH]; intros f h H.
  - reflexivity.
  - cbn [bk_psd].
    assert (H1 : bk_psd f N <= bk_psd h N)
      by (apply IH; intro k; intro Hk; apply H; lia).
    assert (H2 : f N <= h N) by (apply H; lia).
    lia.
Qed.

(* Section C. The nat-layer [q~_n] and its [3^n] lower bound (nat        *)
(* scaffolding face). *)

(* [q~_n := sum_{k<=n} C(n,k)^2 * 2^{n-k}] (the nat carrier of           *)
(* [2^n * Q_n(1/2)]). *)
Definition bk_Qn_qtilde (n : nat) : nat :=
  bk_psd (fun k => bkC n k * bkC n k) (Datatypes.S n).

Lemma bk_Qn_ge_3pow_nat : forall n : nat, 3 ^ n <= bk_Qn_qtilde n.
Proof.
  intro n.
  unfold bk_Qn_qtilde.
  assert (Hpt : forall k : nat, k < Datatypes.S n -> bkC n k <= bkC n k * bkC n k).
  { intro k. intro Hk.
    assert (Hk' : k <= n) by lia.
    assert (Hpos : NatLe 1 (bkC n k)) by (apply BeukersLists.bkC_pos; apply NatLe_lift; exact Hk').
    pose proof (NatLe_drop _ _ Hpos) as HposP.
    assert (H1 : bkC n k * 1 <= bkC n k * bkC n k)
      by (apply Nat.mul_le_mono_l; exact HposP).
    rewrite Nat.mul_1_r in H1. exact H1. }
  assert (Hmono := bk_psd_mono (Datatypes.S n)
                     (fun k => bkC n k)
                     (fun k => bkC n k * bkC n k) Hpt).
  rewrite <- (bk_psd_binom n).
  exact Hmono.
Qed.

(* nat-to-Q bridge: the nat image of [Qle]. *)
Lemma bk_Qle_nat : forall a b : nat, (a <= b)%nat -> Qle (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b H.
  unfold Qle. cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  apply Nat2Z.inj_le.
  exact H.
Qed.

(* Section D. The Q layer: the [Q_n] coefficient list, evaluation faces  *)
(* and the integrality witnesses. *)

(* Horner-fold evaluation (the head is the constant term). *)
Fixpoint bkQ (p : list Q) (z : Q) : Q :=
  match p with
  | nil => 0%Q
  | c :: p' => c + z * bkQ p' z
  end.

(* index-list core: [bk_idx N = [0;1;...;N-1]] (carried by a list        *)
(* Fixpoint). *)
Fixpoint bk_idx (N : nat) : list nat :=
  match N with
  | 0 => nil
  | Datatypes.S m => bk_idx m ++ (m :: nil)
  end.

Lemma bk_idx_seq : forall N : nat, bk_idx N = seq 0 N.
Proof.
  induction N as [| N IH].
  - reflexivity.
  - cbn [bk_idx]. rewrite IH.
    rewrite (seq_S N 0). reflexivity.
Qed.

(* the [Q_n] coefficient list: term [k] is [C(n,k)^2] (the Q image of    *)
(* the squared [bkC]), [k = 0..n]. *)
Definition bk_Qn_list (n : nat) : list Q :=
  map (fun k => (Z.of_nat (bkC n k * bkC n k) # 1)%Q) (bk_idx (Datatypes.S n)).

(* the evaluation function (list-fold face). *)
Definition bk_Qn_eval (n : nat) (z : Q) : Q := bkQ (bk_Qn_list n) z.

(* the Q-layer indexed-sum core: [bk_psQ f N z = sum_{k<N} f(k) * z^k]. *)
Fixpoint bk_psQ (f : nat -> Q) (N : nat) (z : Q) : Q :=
  match N with
  | 0 => 0%Q
  | Datatypes.S m => bk_psQ f m z + f m * q_pow z m
  end.

Lemma bkQ_app : forall (p q : list Q) (z : Q),
  bkQ (p ++ q) z == bkQ p z + q_pow z (length p) * bkQ q z.
Proof.
  induction p as [| a p' IH]; intros q z.
  - cbn [app length bkQ q_pow]. ring.
  - cbn [app length bkQ].
    rewrite IH.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ z (length p'))).
    ring.
Qed.

(* list vs indexed sum: [bkQ (map f (seq 0 (S N))) z == sum_{k<S N}       *)
(* f(k) * z^k]. *)
Lemma bkQ_seq_map : forall (N : nat) (f : nat -> Q) (z : Q),
  bkQ (map f (seq 0 (Datatypes.S N))) z == bk_psQ f (Datatypes.S N) z.
Proof.
  induction N as [| N IH]; intros f z.
  - cbn [seq map bkQ bk_psQ q_pow]. ring.
  - replace (seq 0 (Datatypes.S (Datatypes.S N)))
      with (seq 0 (Datatypes.S N) ++ (Datatypes.S N :: nil))
      by (rewrite (seq_S (Datatypes.S N) 0); reflexivity).
    rewrite map_app.
    rewrite bkQ_app.
    rewrite map_length, seq_length.
    cbn [map bkQ].
    rewrite IH.
    assert (Hunf : bk_psQ f (Datatypes.S (Datatypes.S N)) z
                 = (bk_psQ f (Datatypes.S N) z
                    + f (Datatypes.S N) * q_pow z (Datatypes.S N))%Q)
      by reflexivity.
    rewrite Hunf.
    ring.
Qed.

(* pointwise image: with [k] out-of-range excluded, the [k]-th term of   *)
(* [map] over [seq] equals [f k]. *)
Lemma bk_nth_map_lt : forall (f : nat -> Q) (l : list nat) (k : nat) (d : Q),
  k < length l -> nth k (map f l) d == f (nth k l 0).
Proof.
  intros f l. induction l as [| a l' IH]; intros k d Hk.
  - exfalso. cbn [length] in Hk. lia.
  - destruct k as [| k'].
    + cbn [map nth]. apply Qeq_refl.
    + cbn [map nth]. apply IH. cbn [length] in Hk. lia.
Qed.

Lemma bk_nth_map_seq : forall (f : nat -> Q) (N k : nat) (d : Q),
  k < Datatypes.S N -> nth k (map f (seq 0 (Datatypes.S N))) d == f k.
Proof.
  intros f N k d Hk.
  replace (f k) with (f (nth k (seq 0 (Datatypes.S N)) 0)).
  - apply (bk_nth_map_lt f (seq 0 (Datatypes.S N)) k d).
    rewrite seq_length. lia.
  - apply f_equal. rewrite seq_nth by lia. reflexivity.
Qed.

(* term-by-term characterization of the coefficients: term [k] equals    *)
(* the Q image of [C(n,k)^2]. *)
Lemma bk_Qn_list_nth : forall n k : nat, k <= n ->
  nth k (bk_Qn_list n) 0%Q == (Z.of_nat (bkC n k * bkC n k) # 1)%Q.
Proof.
  intros n k Hk.
  unfold bk_Qn_list. rewrite bk_idx_seq.
  apply bk_nth_map_seq. lia.
Qed.

(* Section D2. The base-change core and the integrality witnesses (the   *)
(* nontrivial main statements of this file). *)

Lemma bk_q_pow_mul : forall (x y : Q) (k : nat),
  q_pow (x * y) k == q_pow x k * q_pow y k.
Proof.
  intros x y k. induction k as [| k IH].
  - cbn [q_pow]. ring.
  - cbn [q_pow]. rewrite IH. ring.
Qed.

Lemma bk_q_pow_one : forall k : nat, q_pow 1%Q k == 1%Q.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. reflexivity.
Qed.

Lemma bk_Qmul_nat : forall a b : nat,
  ((Z.of_nat a # 1) * (Z.of_nat b # 1))%Q == (Z.of_nat (a * b) # 1)%Q.
Proof.
  intros a b. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
  rewrite !Z.mul_1_r, !Nat2Z.inj_mul. reflexivity.
Qed.

Lemma bk_Qadd_nat : forall a b : nat,
  ((Z.of_nat a # 1) + (Z.of_nat b # 1))%Q == (Z.of_nat (a + b) # 1)%Q.
Proof.
  intros a b. unfold Qeq. cbn [Qnum Qden Qplus Pos.mul].
  rewrite !Z.mul_1_r, !Nat2Z.inj_add. reflexivity.
Qed.

(* the base-change core (nontrivial main lemma):                         *)
(* [2^n * sum_{k<S n} Q#f(k) * (1/2)^k == Q# sum_{k<S n} f(k) 2^{n-k}],  *)
(* carried by the descending-power nat sum [bk_psd]; plain arithmetic    *)
(* induction, no symmetric reordering needed. *)
Lemma bk_half_psd : forall (n : nat) (g : nat -> nat),
  q_pow (2 # 1)%Q n
    * bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q) (Datatypes.S n) (1 # 2)%Q
  == (Z.of_nat (bk_psd g (Datatypes.S n)) # 1)%Q.
Proof.
  intros n g. induction n as [| n IH].
  - cbn [q_pow bk_psQ bk_psd].
    replace (2 * 0)%nat with 0%nat by lia.
    cbn [Nat.add]. ring.
  - assert (Hhalf : (2 # 1)%Q * (1 # 2)%Q == 1%Q)
      by (compute; reflexivity).
    assert (Hunf : bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                     (Datatypes.S (Datatypes.S n)) (1 # 2)%Q
                 = (bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                     (Datatypes.S n) (1 # 2)%Q
                   + ((Z.of_nat (g (Datatypes.S n)) # 1)
                        * q_pow (1 # 2)%Q (Datatypes.S n))%Q)%Q)
      by reflexivity.
    rewrite Hunf.
    rewrite Qmult_plus_distr_r.
    assert (EA : q_pow (2 # 1)%Q (Datatypes.S n)
                   * bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                       (Datatypes.S n) (1 # 2)%Q
                 == (Z.of_nat (2 * bk_psd g (Datatypes.S n)) # 1)%Q).
    { rewrite (qeqT_imp_qeq _ _ (q_pow_succ (2 # 1)%Q n)).
      rewrite <- (Qmult_assoc (2 # 1)%Q (q_pow (2 # 1)%Q n)
                    (bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                        (Datatypes.S n) (1 # 2)%Q)).
      rewrite IH.
      replace (2 # 1)%Q with (Z.of_nat 2 # 1)%Q by reflexivity.
      apply bk_Qmul_nat. }
    assert (EB : q_pow (2 # 1)%Q (Datatypes.S n)
                   * ((Z.of_nat (g (Datatypes.S n)) # 1)
                        * q_pow (1 # 2)%Q (Datatypes.S n))
                 == (Z.of_nat (g (Datatypes.S n)) # 1) * 1%Q).
    { transitivity ((Z.of_nat (g (Datatypes.S n)) # 1)
                      * (q_pow (2 # 1)%Q (Datatypes.S n)
                           * q_pow (1 # 2)%Q (Datatypes.S n)))%Q.
      - ring.
      - rewrite <- (bk_q_pow_mul (2 # 1)%Q (1 # 2)%Q (Datatypes.S n)).
        rewrite Hhalf. rewrite bk_q_pow_one. reflexivity. }
    rewrite EA, EB, Qmult_1_r.
    apply bk_Qadd_nat.
Qed.

(* half-integer closed form: the [2^n] rescale of [bkQ (bk_Qn_list n)    *)
(* (1/2)] equals [Q#q~_n]. *)
Lemma bk_Qn_half_closed : forall n : nat,
  q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2)%Q
  == (Z.of_nat (bk_Qn_qtilde n) # 1)%Q.
Proof.
  intro n.
  unfold bk_Qn_list.
  rewrite bk_idx_seq.
  rewrite bkQ_seq_map.
  apply bk_half_psd.
Qed.

(* main statement 2: the integrality witness [q~_n = 2^n * Q_n(1/2) in Z] *)
(* (sigT + QeqT, Set face). *)
Theorem bk_Qn_int : forall n : nat,
  sigT (fun z : Z =>
    QeqT ((q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q) ((z # 1)%Q)).
Proof.
  intro n.
  exists (Z.of_nat (bk_Qn_qtilde n)).
  apply qeq_imp_qeqT.
  apply bk_Qn_half_closed.
Qed.

(* main statement 3: [q~_n >= 3^n] ([QleT'] Set face). *)
Theorem bk_Qn_ge_3pow : forall n : nat,
  QleT' ((Z.of_nat (3 ^ n) # 1)%Q) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n.
  apply Qle_to_QleT'.
  apply bk_Qle_nat.
  apply bk_Qn_ge_3pow_nat.
Qed.

(* evaluation-face semantics: [bk_Qn_eval n z == sum_{k<=n} C(n,k)^2 *    *)
(* z^k] ([QeqT] Set face). *)
Theorem bk_Qn_eval_sem : forall (n : nat) (z : Q),
  QeqT (bk_Qn_eval n z)
       (bk_psQ (fun k => (Z.of_nat (bkC n k * bkC n k) # 1)%Q) (Datatypes.S n) z).
Proof.
  intros n z. unfold bk_Qn_eval, bk_Qn_list.
  rewrite bk_idx_seq.
  apply qeq_imp_qeqT.
  apply bkQ_seq_map.
Qed.


(* the harmonic number [H_k = sum_{j=1}^{k} 1/j] (a Q-layer Fixpoint). *)
Fixpoint bk_H (k : nat) : Q :=
  match k with
  | 0 => 0%Q
  | Datatypes.S k' => bk_H k' + (1%Q / (Z.of_nat (Datatypes.S k') # 1))%Q
  end.

(* the [P_n] coefficient list: term [k] is [C(n,k)^2 * H_k]. *)
Definition bk_Pn_list (n : nat) : list Q :=
  map (fun k => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
      (bk_idx (Datatypes.S n)).

(* evaluation face: [bkQ (bk_Pn_list n) z == sum_{k<=n} C(n,k)^2 * H_k *  *)
(* z^k] ([QeqT] Set face). *)
Theorem bk_Pn_eval : forall (n : nat) (z : Q),
  QeqT (bkQ (bk_Pn_list n) z)
       (bk_psQ (fun k => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
               (Datatypes.S n) z).
Proof.
  intros n z. unfold bk_Pn_list.
  rewrite bk_idx_seq.
  apply qeq_imp_qeqT.
  apply bkQ_seq_map.
Qed.

(* term-by-term characterization of the [P_n] coefficients. *)
Lemma bk_Pn_list_nth : forall n k : nat, k <= n ->
  nth k (bk_Pn_list n) 0%Q == ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q.
Proof.
  intros n k Hk.
  unfold bk_Pn_list. rewrite bk_idx_seq.
  apply bk_nth_map_seq. lia.
Qed.

(* Assumption audit record: the Print Assumptions lines below. *)

Print Assumptions bk_Qn_sym.
Print Assumptions bk_psd_binom.
Print Assumptions bk_Qn_ge_3pow_nat.
Print Assumptions bk_Qn_int.
Print Assumptions bk_Qn_ge_3pow.
Print Assumptions bk_Qn_eval_sem.
Print Assumptions bk_Qn_list_nth.
Print Assumptions bk_Pn_eval.
Print Assumptions bk_Pn_list_nth.
