(** * u5c_zeta2_gapB (ConstructiveWorld-Set): the Hanson closure chain, the supply side of the zeta(2) gap.

    Mission.  The Hanson (1972) bound [hl_lcm_upto n <= 3^n] is the supply position of
      premise I of the integrality separation face [zb2_dc_sep_small].  This file
      proves the supply side: the C-chain equation, the stepping of the Sylvester
      denominator product, the reinjection identity at [z2d_sylv_P k], and the
      closure chain from divisibility and the upper-bound premise to [hl_le_t
      (hl_lcm_upto n) (3^n)], with the Q-layer acceptance statement
      [z2d_lcm_le_3pow].  The core certificate, the nat form of the Sylvester
      entropy inequality [sum (ln a_i) / a_i < ln 3], is not cast here: the chain
      carries [z2v_C n <= 3^n] as an explicit premise position rather than an
      axiom, and [Print Assumptions] stays empty; gap piece A (premise II) is untouched here.

    Dependencies.  Stdlib [QArith.QArith], [ZArith.ZArith], [Arith.Arith],
      [Arith.Factorial], [Lia]; requires [HansonLcm], [Hanson3Pow],
      [S02_CauchyComplete] (the [QleT'] supply position), [abl_z2_dub3], [abl_z2_valbridge].

    References.  Hanson, Canad. Math. Bull. 15 (1972), 33-37, Lemma 3;
      C(n) := n! / prod_i floor(n / a_i)! over the Sylvester sequence 2, 3,
      7, 43, ...; carriers follow [abl_z2_dub3] and [abl_z2_valbridge];
      statement names carried over verbatim from the same-named baseline module. interface-generation alignment per UpReqMisc5B precedent (hl_le_t bridge family).

    Constructivity.  All proofs close by Qed; no axioms are declared and no
      classical logic is used; [hl_le_t] and [QleT'] are Set-level, the
      supporting lemmas are nat-level Prop statements, [z2gb_G] is a
      computable Fixpoint, and the closing [Print Assumptions] block re-checks every named statement.

    Build.  [coqc -native-compiler no -q -Q . ""] on this module compiles
      cleanly (exit 0); the artifact starts with [436f7121 000160bc]; the
      dependency .vo files map to the source root by -Q (abl_tmine04_pool/zeta2 pool). *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith.
From Stdlib Require Import Arith.Factorial Lia.
Require Import HansonLcm.
Require Import Hanson3Pow.
Require Import S02_CauchyComplete.
Require Import abl_z2_dub3.
Require Import abl_z2_valbridge.

(* importing QArith opens Q_scope globally and its notation then shadows the nat face —
   the scope is closed in place, and every Q-layer statement is annotated locally with %Q
   (the face of z2d_lcm_le_3pow is already annotated) *)
Close Scope Q_scope.

(* ===================================================================== *)
(* §0 the Q-layer embedding bridge and the basic face                                                  *)
(* ===================================================================== *)

(* nonnegative numeric face: 0 ≤ (n)#1 for any nat *)
Lemma zb2gb_natQ_ge0 : forall n : nat, (0 <= Z.of_nat n # 1)%Q.
Proof.
  intro n. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* same-denominator order reflection on the Q layer: a ≤ b (nat) implies (a#1) ≤ (b#1) (carried by the Set-level QleT') *)
Lemma zb2gb_Qnat_le : forall a b : nat,
  (a <= b)%nat -> QleT' ((Z.of_nat a # 1)%Q) ((Z.of_nat b # 1)%Q).
Proof.
  intros a b Hab. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* positivity of powers: 1 ≤ 3^n for any nat exponent *)
Lemma zb2gb_3pow_pos : forall n : nat, (1 <= 3 ^ n)%nat.
Proof.
  intro n. assert (Hne : (3 ^ n <> 0)%nat) by (apply Nat.pow_nonzero; lia).
  lia.
Qed.

(* ===================================================================== *)
(* §1 the C-chain equation and positivity                                                     *)
(* ===================================================================== *)

(* the C-chain equation (exact): 1 ≤ n gives fact n = z2v_den n n · z2v_C n.
   (z2v_den n n divides fact n by the valbridge lemma z2v_den_dvd; the division is read back through its defining equation.) *)
Lemma zb2gb_C_fact_eq : forall n : nat,
  (1 <= n)%nat -> fact n = z2v_den n n * z2v_C n.
Proof.
  intros n Hn. unfold z2v_C.
  destruct (z2v_den_dvd n Hn) as [t Ht].
  pose proof (hl_le_t_to_le _ _ (z2v_den_pos n n)) as Hdp.
  rewrite Ht.
  rewrite Nat.div_mul by lia.
  ring.
Qed.

(* positivity of C: 1 ≤ z2v_C n for every n (at n = 0 the case computes directly, z2v_C 0 = 1) *)
Lemma zb2gb_C_pos : forall n : nat, (1 <= z2v_C n)%nat.
Proof.
  intro n. destruct n as [| m].
  - vm_compute. lia.
  - destruct (z2v_C (S m)) eqn:EC.
    + exfalso. pose proof (zb2gb_C_fact_eq (S m) ltac:(lia)) as Heq.
      rewrite EC in Heq.
      rewrite Nat.mul_0_r in Heq.
      pose proof (hl_le_t_to_le _ _ (h3_fact_pos (S m))). lia.
    + lia.
Qed.

(* divisibility implies ≤, three-premise form (without positivity of the dividend, a | 0 is already a counterexample) *)
Lemma zb2gb_dvd_le : forall a b : nat,
  Nat.divide a b -> (1 <= a)%nat -> (1 <= b)%nat -> (a <= b)%nat.
Proof.
  intros a b Hd Ha Hb. destruct Hd as [p Hp].
  assert (Hp1 : (1 <= p)%nat).
  { destruct p as [| p']; [rewrite Nat.mul_0_l in Hp; lia | lia]. }
  rewrite Hp, (Nat.mul_comm p a).
  rewrite <- (Nat.mul_1_r a) at 1.
  apply Nat.mul_le_mono_l. exact Hp1.
Qed.

(* ===================================================================== *)
(* §2 the Sylvester increment product z2gb_G and the denominator-product stepper                              *)
(* ===================================================================== *)

(* the increment-product carrier: z2gb_G k n := ∏_{j<k} f_j with f_j = n/a_{j+1} when a_{j+1} ∣ n,
   and 1 otherwise. this is the exact ratio product of the denominator product fact(⌊n/a⌋) as n grows by one. *)
Fixpoint z2gb_G (k n : nat) : nat :=
  match k with
  | O => 1
  | S k' =>
      z2gb_G k' n *
      (if Nat.eqb (n mod z2d_sylv_a k') 0 then n / z2d_sylv_a k' else 1)
  end.

(* the tiered-quotient step of the factorial (the ratio kernel at each tier): 1 ≤ a gives
   fact(S m/a) = fact(m/a)·[S m/a when a ∣ S m, and 1 otherwise].
   (z2v_inc: the tiered quotient jumps by exactly one at the tiers where a ∣ S m.) *)
Lemma zb2gb_fact_step : forall m a : nat,
  (1 <= a)%nat ->
  fact (S m / a) =
  fact (m / a) * (if Nat.eqb (S m mod a) 0 then S m / a else 1).
Proof.
  intros m a Ha.
  pose proof (hl_id_eq _ _ _ (z2v_inc m a Ha)) as Hinc.
  destruct (Nat.eq_dec (S m mod a) 0) as [Hz | Hnz].
  - rewrite Hz in Hinc.
    rewrite Nat.eqb_refl in Hinc.
    change (if true then 1 else 0) with 1 in Hinc.
    rewrite Hz.
    rewrite Nat.eqb_refl.
    change (if true then S m / a else 1) with (S m / a).
    rewrite Hinc.
    rewrite Nat.add_1_r.
    cbn [fact]. ring.
  - apply Nat.eqb_neq in Hnz.
    rewrite Hnz in Hinc.
    change (if false then 1 else 0) with 0 in Hinc.
    rewrite Hnz.
    change (if false then S m / a else 1) with 1.
    assert (Hzero : (S m / a = m / a)%nat) by lia.
    rewrite Hzero. ring.
Qed.

(* positivity of the increment product: 1 ≤ n gives 1 ≤ z2gb_G k n for every k *)
Lemma zb2gb_G_ge1 : forall k n : nat, (1 <= n)%nat -> (1 <= z2gb_G k n)%nat.
Proof.
  induction k as [| k IH]; intros n Hn.
  - cbn [z2gb_G]. lia.
  - cbn [z2gb_G].
    destruct (Nat.eq_dec (n mod z2d_sylv_a k) 0) as [Hm0 | Hm0].
    + rewrite Hm0.
      rewrite Nat.eqb_refl.
      change (if true then n / z2d_sylv_a k else 1)
        with (n / z2d_sylv_a k).
      destruct (n / z2d_sylv_a k) as [| q'] eqn:Ed.
      * exfalso.
        pose proof (Nat.div_mod_eq n (z2d_sylv_a k)) as Hdm.
        rewrite Ed in Hdm.
        rewrite Hm0 in Hdm.
        lia.
      * pose proof (IH n Hn).
        change (1 * 1 <= z2gb_G k n * S q')%nat.
        apply Nat.mul_le_mono; lia.
    + rewrite (proj2 (Nat.eqb_neq (n mod z2d_sylv_a k) 0) Hm0).
      change (if false then n / z2d_sylv_a k else 1) with 1.
      pose proof (IH n Hn). lia.
Qed.

(* P ≥ 2^k: the lower exponential anchor of the Sylvester running product (P_0 = 1 = 2^0, each step doubles) *)
Lemma zb2gb_sylvP_ge_pow2 : forall k : nat, (2 ^ k <= z2d_sylv_P k)%nat.
Proof.
  induction k as [| k IH].
  - cbn [z2d_sylv_P Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'. cbn [z2d_sylv_P].
    apply Nat.le_trans with (m := 2 * z2d_sylv_P k).
    + apply Nat.mul_le_mono_l. exact IH.
    + pose proof (S01_BaseRing.NatLe_drop _ _ (z2d_sylv_P_pos k)) as Hp.
      rewrite (Nat.mul_comm 2 (z2d_sylv_P k)).
      apply Nat.mul_le_mono_l. lia.
Qed.

(* tiered-bound invariance of the denominator product: m < a_k leaves the product unchanged when one more tier folds in (a_k > m gives ⌊m/a_k⌋ = 0) *)
Lemma zb2gb_den_tail1 : forall k m : nat,
  (m < z2d_sylv_a k)%nat -> z2v_den (S k) m = z2v_den k m.
Proof.
  intros k m Hlt. cbn [z2v_den].
  rewrite (Nat.div_small m (z2d_sylv_a k) Hlt).
  cbn [fact]. lia.
Qed.

(* the denominator-product stepper (core engine one of this file): 1 ≤ n gives
   z2v_den k n = z2v_den k (n−1) · z2gb_G k n.
   at each tier: when a ∣ n, fact(n/a) = fact((n−1)/a)·(n/a) (the tiered quotient jumps by exactly one);
   when a ∤ n the quotient is unchanged and the factor is 1, tier by tier this is exactly zb2gb_fact_step. *)
Lemma zb2gb_den_G : forall k n : nat,
  (1 <= n)%nat -> z2v_den k n = z2v_den k (n - 1) * z2gb_G k n.
Proof.
  intros k n Hn. destruct n as [| m]; [lia |].
  induction k as [| k IH].
  - cbn [z2v_den z2gb_G]. lia.
  - cbn [z2v_den z2gb_G].
    replace (S m - 1) with m by lia.
    pose proof (z2d_sylv_a_neq0 k) as Hak.
    assert (Hone : (1 <= z2d_sylv_a k)%nat) by lia.
    remember ((if Nat.eqb (S m mod z2d_sylv_a k) 0
               then S m / z2d_sylv_a k else 1)) as F eqn:EF.
    rewrite (zb2gb_fact_step m (z2d_sylv_a k) Hone).
    rewrite <- EF.
    replace (S m - 1) with m in IH by lia.
    rewrite IH. ring.
Qed.

(* ===================================================================== *)
(* §3 engine identity one: the exact stepping recursion of C                                      *)
(* ===================================================================== *)

(* the C stepping identity (unconditional, full strength): m ≥ 1 gives
   z2v_C (S m) · z2gb_G (S m) (S m) = S m · z2v_C m.
   chain order: the two exact expressions for fact (S m) (one from the C-chain equation at each end) are
   reconciled through the denominator-product stepper (§2, with the tiered-bound invariance at a_m > m
   closing the last tier) and cancel. *)
Lemma zb2gb_C_step : forall m : nat,
  (1 <= m)%nat -> z2v_C (S m) * z2gb_G (S m) (S m) = S m * z2v_C m.
Proof.
  intros m Hm.
  pose proof (zb2gb_C_fact_eq (S m) ltac:(lia)) as Etop.
  pose proof (zb2gb_C_fact_eq m Hm) as Ebot.
  pose proof (zb2gb_den_G (S m) (S m) ltac:(lia)) as EG1.
  replace (S m - 1) with m in EG1 by lia.
  assert (Ham : (m < z2d_sylv_a m)%nat).
  { unfold z2d_sylv_a.
    pose proof (zb2gb_sylvP_ge_pow2 m) as Hp2.
    pose proof (Nat.pow_gt_lin_r 2 m ltac:(lia)) as Hgt. lia. }
  pose proof (zb2gb_den_tail1 m m Ham) as Et.
  pose proof (hl_le_t_to_le _ _ (z2v_den_pos m m)) as Hdp.
  assert (Hdnz : (z2v_den m m <> 0)%nat) by lia.
  assert (E2 : fact (S m) = (z2v_C (S m) * z2gb_G (S m) (S m)) * z2v_den m m).
  { rewrite Etop. rewrite EG1. rewrite Et. ring. }
  assert (E1 : fact (S m) = (S m * z2v_C m) * z2v_den m m).
  { cbn [fact]. rewrite Ebot. ring. }
  pose proof (proj1 (Nat.mul_cancel_r (z2v_C (S m) * z2gb_G (S m) (S m))
                       (S m * z2v_C m) (z2v_den m m) Hdnz)
               (eq_trans (eq_sym E2) E1)) as Ef.
  exact Ef.
Qed.

(* numeric anchor (direct computation on a small instance): z2gb_G 6 6 = 6 (2·3 divides 6, the remaining tiers contribute factor 1);
   combined with the C stepping identity at n = 6 this closes by direct computation as 60·6 = 6·60. *)
Lemma zb2gb_G_smoke_6 : z2gb_G 6 6 = 6.
Proof. reflexivity. Qed.

Lemma zb2gb_C_step_smoke : z2v_C 6 * z2gb_G 6 6 = 6 * z2v_C 5.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(* §4 engine identity two: full-tier reinjection of the increment product (the ledger refill position at P_k)               *)
(* ===================================================================== *)

(* the scaling identity of the increment product: when every a_j (j < k) divides X,
   z2gb_G k (c·X) = z2gb_G k X · c^k
   (each tier contributes the factor c·X/a_j = c·(X/a_j), and the k tiers compose to c^k, of the same shape as z2d_sylv_sum_mul). *)
Lemma zb2gb_G_scale : forall k c X : nat,
  (forall j : nat, (j < k)%nat -> Nat.divide (z2d_sylv_a j) X) ->
  z2gb_G k (c * X) = z2gb_G k X * (c ^ k)%nat.
Proof.
  induction k as [| k IH]; intros c X Hd.
  - reflexivity.
  - cbn [z2gb_G].
    destruct (Hd k (Nat.lt_succ_diag_r k)) as [q Hq].
    pose proof (z2d_sylv_a_neq0 k) as Ha0.
    assert (Hmod1 : (X mod z2d_sylv_a k = 0)%nat).
    { rewrite Hq. rewrite Nat.Div0.mod_mul. lia. }
    assert (Hmodx : Nat.eqb (X mod z2d_sylv_a k) 0 = true)
      by (apply Nat.eqb_eq; exact Hmod1).
    assert (Hdiv1 : X / z2d_sylv_a k = q)
      by (rewrite Hq at 1; apply Nat.div_mul; exact Ha0).
    assert (Hmodc : Nat.eqb ((c * X) mod z2d_sylv_a k) 0 = true).
    { apply Nat.eqb_eq. rewrite Hq at 1.
      rewrite Nat.mul_assoc. rewrite Nat.Div0.mod_mul. lia. }
    assert (Hdivc : (c * X) / z2d_sylv_a k = c * (X / z2d_sylv_a k)).
    { rewrite Hq at 1. rewrite Nat.mul_assoc.
      rewrite Nat.div_mul by exact Ha0.
      rewrite Hdiv1. reflexivity. }
    rewrite Hmodx.
    change (if true then X / z2d_sylv_a k else 1) with (X / z2d_sylv_a k).
    rewrite Hdiv1.
    rewrite Hmodc.
    change (if true then c * (X / z2d_sylv_a k) else 1)
      with (c * (X / z2d_sylv_a k)).
    rewrite Hdivc.
    rewrite Hdiv1.
    rewrite (IH c X) by (intros j Hj; apply Hd; lia).
    rewrite Nat.pow_succ_r'. ring.
Qed.

(* the full-tier reinjection identity (unconditional, full strength):
   z2gb_G k (z2d_sylv_P k) · z2d_sylv_P k = (z2d_sylv_P k)^k.
   at P_k every a_j (j < k) divides (z2d_sylv_dvd), so the increment product runs at full tiers; the step closes
   with P_{k+1} = a_{k+1}·P_k and the scaling identity. this is the refill engine of the C stepping ledger
   at the Sylvester anchors. *)
Lemma zb2gb_G_sylv : forall k : nat,
  z2gb_G k (z2d_sylv_P k) * z2d_sylv_P k = ((z2d_sylv_P k) ^ k)%nat.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - assert (Hdvd : forall j : nat, (j < k)%nat -> Nat.divide (z2d_sylv_a j) (z2d_sylv_P k))
      by (intros j Hj; apply z2d_sylv_dvd; exact Hj).
    cbn [z2gb_G].
    assert (Hmodstep : Nat.eqb (z2d_sylv_P (S k) mod z2d_sylv_a k) 0 = true).
    { apply Nat.eqb_eq. unfold z2d_sylv_a, z2d_sylv_P.
      rewrite Nat.Div0.mod_mul. lia. }
    rewrite Hmodstep.
    change (if true then z2d_sylv_P (S k) / z2d_sylv_a k else 1)
      with (z2d_sylv_P (S k) / z2d_sylv_a k).
    assert (Hdivstep : z2d_sylv_P (S k) / z2d_sylv_a k = z2d_sylv_P k).
    { unfold z2d_sylv_a, z2d_sylv_P. apply Nat.div_mul.
      pose proof (S01_BaseRing.NatLe_drop _ _ (z2d_sylv_P_pos k)). lia. }
    rewrite Hdivstep.
    assert (Hfold : z2d_sylv_P (S k) = z2d_sylv_a k * z2d_sylv_P k).
    { unfold z2d_sylv_a, z2d_sylv_P. rewrite Nat.mul_comm. reflexivity. }
    rewrite Hfold.
    rewrite (zb2gb_G_scale k (z2d_sylv_a k) (z2d_sylv_P k) Hdvd).
    rewrite Nat.pow_succ_r'.
    rewrite Nat.pow_mul_l.
    rewrite <- IH. ring.
Qed.

(* numeric anchor: z2gb_G 3 (z2d_sylv_P 3) · 42 = 42^3
   (P_3 = 42 = 2·3·7, the increment product is 21·14·6, and 21·14·6·42 = 74088 = 42^3) *)
Lemma zb2gb_G_sylv_smoke_3 :
  z2gb_G 3 (z2d_sylv_P 3) * z2d_sylv_P 3 = ((z2d_sylv_P 3) ^ 3)%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(* §5 the M3′ closure chain (divisibility + positivity + upper bound give the 3^n bound)                          *)
(* ===================================================================== *)

(* the M3′ closure main chain (Set face, carried by hl_id): an upper bound on C gives lcm ≤ 3^n.
   chain order: z2v_lcm_dvd_C (the valbridge divisibility at full strength) gives lcm ≤ C (three-premise form),
   hence lcm ≤ 3^n. *)
Theorem zb2gb_lcm_le_3pow_cond : forall n : nat,
  (1 <= n)%nat -> (z2v_C n <= 3 ^ n)%nat ->
  hl_le_t (hl_lcm_upto n) (3 ^ n)%nat.
Proof.
  intros n Hn HC. apply hl_le_to_le_t.
  pose proof (z2v_lcm_dvd_C n) as Hdd.
  pose proof (hl_le_t_to_le _ _ (h3_lcm_pos n)) as Hlp.
  pose proof (zb2gb_C_pos n) as Hcp.
  pose proof (zb2gb_3pow_pos n) as H3p.
  pose proof (zb2gb_dvd_le (hl_lcm_upto n) (z2v_C n) Hdd Hlp Hcp) as Hle.
  lia.
Qed.

(* ===================================================================== *)
(* §6 the acceptance statement (acceptance-criterion name from survey shape §3, Q-layer Set face, explicit premise position)                *)
(* ===================================================================== *)

(* the acceptance statement (registered loudly: the premise z2v_C n ≤ 3^n is exactly the interface position of the still-uncast core piece M2′,
   once that piece lands this statement becomes unconditional; the premise is carried in the statement itself, not an axiom, nothing admitted). *)
Theorem z2d_lcm_le_3pow : forall n : nat,
  (1 <= n)%nat -> (z2v_C n <= 3 ^ n)%nat ->
  QleT' ((Z.of_nat (hl_lcm_upto n) # 1)%Q) ((Z.of_nat (3 ^ n) # 1)%Q).
Proof.
  intros n Hn HC. apply zb2gb_Qnat_le.
  pose proof (hl_le_t_to_le (hl_lcm_upto n) (3 ^ n)%nat
                (zb2gb_lcm_le_3pow_cond n Hn HC)) as Hle. exact Hle.
Qed.

(* numeric smoke check (executable on the Set face): the full chain computed directly at the instance n = 6
   (lcm(1..6) = 60 ≤ 3^6 = 729; the premise C(6) = 60 ≤ 729 is computed directly) *)
Lemma zb2gb_smoke_6 : hl_le_t (hl_lcm_upto 6) (3 ^ 6)%nat.
Proof.
  apply (zb2gb_lcm_le_3pow_cond 6).
  - lia.
  - vm_compute. lia.
Qed.

(* ===================================================================== *)
(* §7 tail section: self-check of the axiom face of the main statements                                              *)
(* ===================================================================== *)

Print Assumptions zb2gb_natQ_ge0.
Print Assumptions zb2gb_Qnat_le.
Print Assumptions zb2gb_3pow_pos.
Print Assumptions zb2gb_C_fact_eq.
Print Assumptions zb2gb_C_pos.
Print Assumptions zb2gb_dvd_le.
Print Assumptions zb2gb_fact_step.
Print Assumptions zb2gb_G_ge1.
Print Assumptions zb2gb_sylvP_ge_pow2.
Print Assumptions zb2gb_den_tail1.
Print Assumptions zb2gb_den_G.
Print Assumptions zb2gb_C_step.
Print Assumptions zb2gb_G_smoke_6.
Print Assumptions zb2gb_C_step_smoke.
Print Assumptions zb2gb_G_scale.
Print Assumptions zb2gb_G_sylv.
Print Assumptions zb2gb_G_sylv_smoke_3.
Print Assumptions zb2gb_lcm_le_3pow_cond.
Print Assumptions z2d_lcm_le_3pow.
Print Assumptions zb2gb_smoke_6.
