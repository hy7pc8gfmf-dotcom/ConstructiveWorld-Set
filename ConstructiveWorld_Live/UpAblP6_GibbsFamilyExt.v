(* ConstructiveWorld-Set -- temperature-scaled KL/Jeffreys bounds, Gibbs family extension. *)

(** * UpAblP6_GibbsFamilyExt: temperature scaling of KL and symmetric Jeffreys divergence.

    Mission.  Five pointwise / finite-sum upper bounds for the positive-temperature
      scaling (β) of KL and symmetric Jeffreys divergence over the Bishop reals:
      ① [uagfe_gibbs_temp_one_B], the β=1 Bishop instance from [gfe_gibbs_core_temp_B];
      ② [uagfe_gibbs_temp_two_eps], the β=2 eps instance from [gfe_gibbs_core_temp_eps],
      premise lowered to non-strict by [gfe_le_of_lt]; ③ [uagfe_le_b_mult_pos_two_temp_flat],
      (b1·b2)·x ≤_B (b1·b2)·y, two composed levels of [gfe_le_b_mult_pos];
      ④ [uagfe_jeffreys_sym_temp_B], 0 ≤_B β·(kl(p‖q)+kl(q‖p)) pointwise, the
      Jeffreys-sum temperature face new here; ⑤ [uagfe_jeffreys_sym_list_temp_B],
      its finite-sum analog via [gfe_jeffreys_sym_list_B], scaled as ④.

    Dependencies.  Stdlib [List] ([ListNotations]); [S02_CauchyComplete];
      [S08_RealMainlineDPO]; [UpRealLeB]/[UpRealLeB2]/[UpRealLeB3];
      [UpReqKLStrictB]; [GibbsFamilyExt]; premises [real_lt_zero_one]/[real_plus_positive].

    References.  No direct counterpart (a Bishop-constructive version of
      KL/Jeffreys-type inequalities). Provenance: by-name replacement draft of
      the same-named Live-tree file, verbatim except the toy-proof bodies of
      [uagfe_gibbs_temp_one_B] (orig L52) and [uagfe_gibbs_temp_two_eps] (orig L65);
      statement and citation faces unchanged, zero new Requires.

    Constructivity.  All conclusions Set-layer carried (self-built Or encoding;
      [real_le]/[real_lt]/[real_le_b]/[real_eq] Set-valued); zero axioms, zero
      admission-style statements; end-of-file Print Assumptions Closed on all five.

    Build.  [coqc 9.1 direct call with cpu_guard, -o to a temp directory, zero
      in-tree writes] compiles cleanly; the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import List.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Import ListNotations.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import UpReqKLStrictB.
Require Import GibbsFamilyExt.

(* ============================================================ *)
(* §1 uagfe_gibbs_temp_one_B: the unit-temperature β=1 pointwise Bishop
   upper-bound instance *)
(* ============================================================ *)

Lemma uagfe_gibbs_temp_one_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_le_b (real_mult real_one (real_plus p (real_opp q)))
            (real_mult real_one (real_kl_term p q Hp Hq)).
Proof.
  intros p q Hp Hq.
  exact (gfe_gibbs_core_temp_B p q real_one Hp Hq real_lt_zero_one).
Qed.

(* ============================================================ *)
(* §2 uagfe_gibbs_temp_two_eps: the doubled-temperature β=2 pointwise eps
   instance form *)
(* ============================================================ *)

Lemma uagfe_gibbs_temp_two_eps : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (eps : Real) (Heps : real_lt real_zero eps),
  real_le (real_mult (real_plus real_one real_one) (real_plus p (real_opp q)))
          (real_plus
             (real_mult (real_plus real_one real_one)
                        (real_kl_term p q Hp Hq))
             (real_mult (real_plus real_one real_one) (real_mult p eps))).
Proof.
  intros p q Hp Hq eps Heps.
  exact (gfe_gibbs_core_temp_eps p q (real_plus real_one real_one) Hp Hq           (gfe_le_of_lt (real_plus real_one real_one)              (real_plus_positive real_one real_one                 real_lt_zero_one real_lt_zero_one))           eps Heps).
Qed.

(* ============================================================ *)
(* §3 uagfe_le_b_mult_pos_two_temp_flat: the two-level temperature
   composition, flat form *)
(* ============================================================ *)

Lemma uagfe_le_b_mult_pos_two_temp_flat :
  forall (x y b1 b2 : Real),
  real_lt real_zero b1 -> real_lt real_zero b2 ->
  real_le_b x y ->
  real_le_b (real_mult (real_mult b1 b2) x)
            (real_mult (real_mult b1 b2) y).
Proof.
  intros x y b1 b2 Hb1 Hb2 Hxy.
  apply (gfe_le_b_eq_r (real_mult (real_mult b1 b2) x)
           (real_mult b1 (real_mult b2 y))
           (real_mult (real_mult b1 b2) y)).
  - apply (leb3_le_b_eq_l (real_mult b1 (real_mult b2 x))
             (real_mult (real_mult b1 b2) x)
             (real_mult b1 (real_mult b2 y))).
    + exact (real_mult_assoc b1 b2 x).
    + exact (gfe_le_b_mult_pos (real_mult b2 x) (real_mult b2 y) b1 Hb1
               (gfe_le_b_mult_pos x y b2 Hb2 Hxy)).
  - exact (real_mult_assoc b1 b2 y).
Qed.

(* ============================================================ *)
(* §4 uagfe_jeffreys_sym_temp_B: 0 ≤_B β·(kl(p‖q)+kl(q‖p)) (pointwise) *)
(* ============================================================ *)

Theorem uagfe_jeffreys_sym_temp_B : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_plus (real_kl_term p q Hp Hq)
                            (real_kl_term q p Hq Hp))).
Proof.
  intros p q b Hp Hq Hb.
  apply (leb3_le_b_eq_l (real_mult b real_zero) real_zero
           (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                   (real_kl_term q p Hq Hp)))).
  - exact (real_mult_zero b).
  - exact (gfe_le_b_mult_pos real_zero
             (real_plus (real_kl_term p q Hp Hq)
                        (real_kl_term q p Hq Hp))
             b Hb (gfe_jeffreys_sym_B p q Hp Hq)).
Qed.

(* ============================================================ *)
(* §5 uagfe_jeffreys_sym_list_temp_B (symmetric Jeffreys temperature face,
   finite sum): *)
(*   0 ≤_B β·Σ_s (kl(p s‖q s)+kl(q s‖p s)) *)
(* ============================================================ *)

Theorem uagfe_jeffreys_sym_list_temp_B :
  forall (X : Type) (l : list X) (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (b : Real) (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_list_sum X
        (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                (real_kl_term (q s) (p s) (Hq s) (Hp s))) l)).
Proof.
  intros X l p q Hp Hq b Hb.
  apply (leb3_le_b_eq_l (real_mult b real_zero) real_zero
           (real_mult b (real_list_sum X
              (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                      (real_kl_term (q s) (p s) (Hq s) (Hp s)))
              l))).
  - exact (real_mult_zero b).
  - exact (gfe_le_b_mult_pos real_zero
             (real_list_sum X
                (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                        (real_kl_term (q s) (p s) (Hq s) (Hp s)))
                l)
             b Hb (gfe_jeffreys_sym_list_B X l p q Hp Hq)).
Qed.

(* ============================================================ *)
(* closing check: Print Assumptions prints Closed for all five theorems
   (empty assumption context) *)
(* ============================================================ *)

Print Assumptions uagfe_gibbs_temp_one_B.
Print Assumptions uagfe_gibbs_temp_two_eps.
Print Assumptions uagfe_le_b_mult_pos_two_temp_flat.
Print Assumptions uagfe_jeffreys_sym_temp_B.
Print Assumptions uagfe_jeffreys_sym_list_temp_B.
