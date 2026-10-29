(* ConstructiveWorld-Set -- Hanson route foundation: the Sylvester floor-sum density inequality toward d_n = lcm(1..n) <= 3^n. *)
(** * abl_z2_dub3: the Sylvester density inequality (core of Hanson's Lemma 1).

    Mission.  The exponential control d_n = lcm(1..n) <= 3^n (Hanson 1972)
    is the hard prerequisite on record for the final assembly of the
    zeta(2) tower integrality face d_n^2 * I_n.  This file delivers the
    foundation segment of the Hanson route: the Sylvester sequence
    a_1 = 2, a_{k+1} = a_1*...*a_k + 1 (write P_k = a_1*...*a_k), and on
    it the density inequality 1 + SUM_{j<k} floor(s/a_{j+1}) <= s (1 <= s).

    Dependencies.  Stdlib (Arith.Arith, Lia) plus HansonLcm (the Set-face
    comparator hl_le_t) plus S01_BaseRing (Id, id_refl, id_cong,
    id_cong2, id_trans, NatLe, NatLe_lift, NatLe_drop).

    References.  A. E. Hanson, lcm(1..n) < 3^n, Canad. Math. Bull. 15
    (1972), 33-37: lcm(1..n) = PROD_{p^a <= n} p < 3^n via the quotient
    C(n) = n! / PROD_i floor(n/a_i)!, whose per-prime valuations lean on
    the density inequality proved here and whose ceiling is the entropy
    bound SUM_i (ln a_i)/a_i < ln 3.

    Constructivity.  Closes by Qed throughout; Axioms: none; no classical
    logic.  The main statement face hl_le_t : Set is carried by HansonLcm
    on the Id type; the supporting lemmas live on the nat-layer Prop face
    and serve inference only; z2d_sylv_P and z2d_sylv_sum are executable
    Fixpoints; a closing Print Assumptions sweep rechecks every statement.

    Build.  rocq c -native-compiler no -q -Q world6 "" abl_z2_dub3.v
    (Rocq 9.1.0) against the same-world dependency .vo tree, under the
    cpu_guard load wrapper. *)

From Stdlib Require Import Arith.Arith Lia.
Require Import HansonLcm.
Require Import S01_BaseRing (Id, id_refl, id_cong, id_cong2, id_trans, NatLe, NatLe_lift, NatLe_drop).

(* ================================================================== *)
(* Part A.  The Sylvester sequence and the finite-sum carrier.        *)
(* ================================================================== *)

(* P_k = a_1*...*a_k: P_0 = 1 (empty product), P_{k+1} = P_k*(P_k + 1);
   a_{k+1} := P_k + 1, i.e. a_1 = 2, a_2 = 3, a_3 = 7, a_4 = 43, ... *)
Fixpoint z2d_sylv_P (k : nat) : nat :=
  match k with
  | O => 1
  | S k' => z2d_sylv_P k' * (z2d_sylv_P k' + 1)
  end.

Definition z2d_sylv_a (k : nat) : nat := z2d_sylv_P k + 1.

(* SUM_{j<k} floor(Y/a_{j+1}): the finite-sum carrier (terms with
   a_{j+1} > Y contribute zero of themselves). *)
Fixpoint z2d_sylv_sum (k Y : nat) : nat :=
  match k with
  | O => 0
  | S k' => z2d_sylv_sum k' Y + Y / z2d_sylv_a k'
  end.

Lemma z2d_sylv_P_pos : forall k : nat, NatLe 1 (z2d_sylv_P k).
Proof.
  intros k. apply NatLe_lift.
  induction k as [| k IH]; cbn [z2d_sylv_P]; lia.
Qed.

Lemma z2d_sylv_a_neq0 : forall k : nat, z2d_sylv_a k <> 0.
Proof.
  intro k. unfold z2d_sylv_a.
  pose proof (NatLe_drop _ _ (z2d_sylv_P_pos k)). lia.
Qed.

(* Numeric anchor: P_3 = 2*3*7 = 42 (small instance, direct computation). *)
Lemma z2d_sylv_P_3 : Id (z2d_sylv_P 3) 42.
Proof. apply id_refl. Qed.

(* Numeric anchor: SUM_{j<3} floor(10/a_{j+1})
   = floor(10/2) + floor(10/3) + floor(10/7) = 5 + 3 + 1 = 9. *)
Lemma z2d_sylv_sum_3_10 : Id (z2d_sylv_sum 3 10) 9.
Proof. apply id_refl. Qed.

(* ================================================================== *)
(* Part B.  Divisibility along the sequence and scalar pull-out       *)
(*     for the sum.                                                   *)
(* ================================================================== *)

(* Factor closure of P_k: j < k entails a_{j+1} divides P_k
   (the root of the two-by-two coprimality of the Sylvester sequence). *)
Lemma z2d_sylv_dvd : forall j k : nat,
  j < k -> Nat.divide (z2d_sylv_a j) (z2d_sylv_P k).
Proof.
  intros j k. induction k as [| k IH]; intros Hj.
  - lia.
  - destruct (Nat.eq_dec j k) as [E|NE].
    + rewrite E. unfold z2d_sylv_a. cbn [z2d_sylv_P].
      exists (z2d_sylv_P k). ring.
    + assert (Hjk : j < k) by lia.
      destruct (IH Hjk) as [q Hq].
      cbn [z2d_sylv_P].
      exists (q * (z2d_sylv_P k + 1)).
      rewrite Hq. ring.
Qed.

(* Multiply-divide exchange inequality: if a divides d, then
   d*floor(s/a) <= (d/a)*s.
   (Pointwise: a*floor(s/a) <= s together with d = (d/a)*a.) *)
Lemma z2d_div_mul_le : forall d a s : nat,
  a <> 0 -> Nat.divide a d -> NatLe (d * (s / a)) ((d / a) * s).
Proof.
  intros d a s Ha Hd. apply NatLe_lift. destruct Hd as [q Hq].
  assert (Eda : d / a = q) by (rewrite Hq; apply Nat.div_mul; exact Ha).
  pose proof (Nat.div_mod_eq s a) as Hdm.
  rewrite Eda, Hq.
  rewrite <- Nat.mul_assoc. apply Nat.mul_le_mono_l. lia.
Qed.

(* Scalar pull-out for the sum: if every a_{j+1} divides X, then
   SUM_j floor(c*X/a_{j+1}) = c * SUM_j floor(X/a_{j+1}). *)
Lemma z2d_sylv_sum_mul : forall k c X : nat,
  (forall j : nat, j < k -> Nat.divide (z2d_sylv_a j) X) ->
  Id (z2d_sylv_sum k (c * X)) (c * z2d_sylv_sum k X).
Proof.
  induction k as [| k IH]; intros c X H.
  - cbn [z2d_sylv_sum]. rewrite Nat.mul_0_r. apply id_refl.
  - cbn [z2d_sylv_sum].
    rewrite Nat.mul_add_distr_l.
    apply (id_cong2 (fun u v : nat => u + v)).
    + assert (IHk : Id (z2d_sylv_sum k (c * X)) (c * z2d_sylv_sum k X)).
      { apply (IH c X). intros j Hj. apply H. lia. }
      exact IHk.
    + pose proof (z2d_sylv_a_neq0 k) as Ha.
      assert (E1 : (c * X) / z2d_sylv_a k = c * (X / z2d_sylv_a k)).
      { destruct (H k (Nat.lt_succ_diag_r k)) as [q Hq].
        rewrite Hq. rewrite Nat.mul_assoc.
        rewrite Nat.div_mul by exact Ha.
        rewrite Nat.div_mul by exact Ha.
        reflexivity. }
      rewrite E1. apply id_refl.
Qed.

(* Derivative identity: SUM_{j<k} floor(P_k/a_{j+1}) + 1 = P_k
   (the proper divisors of P_k fall one short of P_k in sum -- the
   general shape of P_3 = 42 = 21 + 14 + 6 + 1). *)
Lemma z2d_sylv_deriv : forall k : nat,
  Id (z2d_sylv_sum k (z2d_sylv_P k) + 1) (z2d_sylv_P k).
Proof.
  induction k as [| k IH].
  - apply id_refl.
  - cbn [z2d_sylv_P z2d_sylv_sum].
    rewrite (Nat.mul_comm (z2d_sylv_P k) (z2d_sylv_P k + 1)).
    pose proof (z2d_sylv_a_neq0 k) as Ha.
    pose proof (z2d_sylv_sum_mul k (z2d_sylv_P k + 1) (z2d_sylv_P k)
                  (fun j Hj => z2d_sylv_dvd j k Hj)) as Hsm.
    assert (E1 : (z2d_sylv_P k + 1) * z2d_sylv_P k / z2d_sylv_a k
                 = z2d_sylv_P k).
    { unfold z2d_sylv_a. rewrite Nat.mul_comm. apply Nat.div_mul. exact Ha. }
    assert (Eshape : (z2d_sylv_P k + 1) * (z2d_sylv_sum k (z2d_sylv_P k) + 1)
                     = (z2d_sylv_P k + 1) * z2d_sylv_sum k (z2d_sylv_P k)
                       + z2d_sylv_P k + 1) by ring.
    rewrite E1.
    apply (id_trans (id_cong (fun t : nat => t + z2d_sylv_P k + 1) Hsm)).
    rewrite <- Eshape.
    exact (id_cong (fun t : nat => (z2d_sylv_P k + 1) * t) IH).
Qed.

(* ================================================================== *)
(* Part C.  The density inequality (core of Hanson's Lemma 1).        *)
(* ================================================================== *)

(* Density inequality: P_k * SUM_{j<k} floor(s/a_{j+1}) + s <= s * P_k.
   Argument: after the split P_{k+1} = P_k*(P_k+1), each term is scaled
   up through the multiply-divide exchange with a_{k+1} a divisor; the
   tail closes linearly from the induction premise P_k*SUM + s <= s*P_k
   multiplied by (P_k+1), together with
   (P_k+1)*floor(s/(P_k+1)) <= s (div_mod). *)
Lemma z2d_sylv_sum_density : forall k s : nat,
  NatLe (z2d_sylv_P k * z2d_sylv_sum k s + s) (s * z2d_sylv_P k).
Proof.
  intros k s. apply NatLe_lift. induction k as [| k IH].
  - cbn [z2d_sylv_P z2d_sylv_sum]. lia.
  - pose proof (Nat.div_mod_eq s (z2d_sylv_a k)) as Hdm.
    assert (Hd : z2d_sylv_a k * (s / z2d_sylv_a k) <= s) by lia.
    pose proof (Nat.mul_le_mono_l (z2d_sylv_P k * z2d_sylv_sum k s + s)
                  (s * z2d_sylv_P k) (z2d_sylv_a k) IH) as HIH.
    unfold z2d_sylv_a in *.
    cbn [z2d_sylv_P z2d_sylv_sum].
    unfold z2d_sylv_a.
    assert (H41 : (z2d_sylv_P k + 1) * (z2d_sylv_P k * z2d_sylv_sum k s)
                  + z2d_sylv_P k * s + s
                  = (z2d_sylv_P k + 1) * (z2d_sylv_P k * z2d_sylv_sum k s + s))
      by ring.
    assert (H42 : (z2d_sylv_P k + 1) * (s * z2d_sylv_P k)
                  = s * (z2d_sylv_P k * (z2d_sylv_P k + 1))) by ring.
    assert (H43 : z2d_sylv_P k * (z2d_sylv_P k + 1)
                    * (z2d_sylv_sum k s + s / (z2d_sylv_P k + 1)) + s
                  = (z2d_sylv_P k + 1) * (z2d_sylv_P k * z2d_sylv_sum k s)
                    + z2d_sylv_P k * ((z2d_sylv_P k + 1) * (s / (z2d_sylv_P k + 1)))
                    + s) by ring.
    assert (H44 : z2d_sylv_P k * ((z2d_sylv_P k + 1) * (s / (z2d_sylv_P k + 1)))
                  <= z2d_sylv_P k * s)
      by (apply Nat.mul_le_mono_l; exact Hd).
    rewrite H43.
    apply Nat.le_trans with
      (m := (z2d_sylv_P k + 1) * (z2d_sylv_P k * z2d_sylv_sum k s)
            + z2d_sylv_P k * s + s).
    + apply Nat.add_le_mono_r. apply Nat.add_le_mono_l. exact H44.
    + rewrite H41, <- H42. exact HIH.
Qed.

(* Density inequality (quotient form): 1 <= s entails
   SUM_{j<k} floor(s/a_{j+1}) < s. *)
Lemma z2d_sylv_sum_lt : forall k s : nat,
  1 <= s -> NatLe (S (z2d_sylv_sum k s)) s.
Proof.
  intros k s Hs. apply NatLe_lift.
  pose proof (NatLe_drop _ _ (z2d_sylv_sum_density k s)) as HD.
  destruct (Nat.lt_ge_cases (z2d_sylv_sum k s) s) as [Hlt|Hge]; [exact Hlt|].
  exfalso.
  pose proof (Nat.mul_le_mono_r s (z2d_sylv_sum k s) (z2d_sylv_P k) Hge) as Hm.
  lia.
Qed.

(* ================================================================== *)
(* Part D.  Main theorem (Set-face carrier) and the honest scope.     *)
(* ================================================================== *)

(* Main theorem (the Sylvester density inequality, Set face): for all k
   and 1 <= s, 1 + SUM_{j<k} floor(s/a_{j+1}) <= s.
   Core of Hanson's 1972 Lemma 1: for a prime p and j <= floor(log_p n)
   take s = floor(n/p^j) >= 1, giving
   floor(n/p^j) - SUM_i floor(n/(a_{i+1}*p^j)) >= 1; summing over levels
   yields floor(log_p n) <= v_p(n! / PROD_i floor(n/a_{i+1})!), hence
   lcm(1..n) divides n! / PROD_i floor(n/a_{i+1})!. *)
Theorem z2d_sylv_floor_t : forall k s : nat,
  1 <= s -> hl_le_t (z2d_sylv_sum k s + 1) s.
Proof.
  intros k s Hs. apply hl_le_to_le_t.
  pose proof (NatLe_drop _ _ (z2d_sylv_sum_lt k s Hs)). lia.
Qed.

(* Honest scope (no overclaim): the main theorem of this file is the
   foundation segment of the Hanson 1972 route.  The three remaining
   segments toward the z2d target statement (hl_lcm_upto n <= 3^n) are
   future files, not yet in the stack:
   first, the Legendre sum identity v_p(m!) = SUM_j floor(m/p^j), both
   directions;
   second, the valuation bridge floor(log_p n) <= v_p(n! / PROD_i
   floor(n/a_{i+1})!) -- level by level take s = floor(n/p^j) and apply
   the main theorem of this file, together with the nested division
   floor(floor(n/p^j)/a) = floor(n/(a*p^j));
   third, the upper tier n! / PROD_i floor(n/a_{i+1})! <= 3^n (a nat
   rendering of the Sylvester entropy inequality
   SUM_i (ln a_i)/a_i < ln 3, including the small-n check).
   None of the three is claimed in finished form within this file. *)

(* Assumption audit: the Print Assumptions output below should report
   Axioms: none (recheck against this list).
   (The Print Assumptions log does not echo theorem names; the evidence
   is collated in the order of this list.) *)
Print Assumptions z2d_sylv_P_pos.
Print Assumptions z2d_sylv_a_neq0.
Print Assumptions z2d_sylv_P_3.
Print Assumptions z2d_sylv_sum_3_10.
Print Assumptions z2d_sylv_dvd.
Print Assumptions z2d_div_mul_le.
Print Assumptions z2d_sylv_sum_mul.
Print Assumptions z2d_sylv_deriv.
Print Assumptions z2d_sylv_sum_density.
Print Assumptions z2d_sylv_sum_lt.
Print Assumptions z2d_sylv_floor_t.
