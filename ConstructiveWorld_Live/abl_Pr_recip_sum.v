(* ============================================================ *)
(* Mission. prs_harm_diverge : forall K : nat, { m : nat &       *)
(*   NatLe (K * 2 ^ (2 * m)) (prs_hsum (2 ^ m) (2 ^ (2 * m))) }: *)
(*   a constructive divergence certificate for the harmonic     *)
(*   series (witness m = 2 * K, computable and extractable);     *)
(*   core limb prs_harm_dyad gives at n = 2 ^ m the log-free nat *)
(*   bound 2 * H_n >= (m + 1) * 2 ^ (2 * m) by dyadic block      *)
(*   gains, second limb prs_geo_euler is the single-prime Euler  *)
(*   factor identity (p - 1) * (1 + p + ... + p ^ e) + 1 =       *)
(*   p ^ (e + 1) on the Set-level hl_id carrier; the full Euler  *)
(*   product and weak Mertens form stay out of scope (Section 8  *)
(*   register block).                                            *)
(* Dependencies. Stdlib (Arith.Arith, List, Bool, Lia);          *)
(*   HansonLcm (hl_id, hl_idrefl); S01_BaseRing (Id, id_refl,    *)
(*   NatLe, NatLe_lift, NatLe_drop).                             *)
(* References. the 26 in-file stations in file order, plus       *)
(*   NatLe_lift, NatLe_drop, hl_idrefl, Nat.pow_add_r,           *)
(*   Nat.pow_succ_r, Nat.div_mul, Nat.div_mod, Nat.le_trans.     *)
(* Constructivity. Set-level carriers: bare nat equations carry  *)
(*   Id, nat orderings carry NatLe (an Id over Nat.leb), the     *)
(*   divergence statement is a sigT witness, the Euler factor    *)
(*   identity is an hl_id equation; proofs drop to the Prop face *)
(*   only through NatLe_lift / NatLe_drop and close by id_refl / *)
(*   hl_idrefl; nonlinear steps are explicit mul monotonicity,   *)
(*   lia covers linear cores, closed numerics run vm_compute;    *)
(*   refutations use -> False only. Axioms: none (Section 9      *)
(*   audit).                                                     *)
(* Build. Rocq 9.1.0: rocq c -native-compiler no -Q . "" with     *)
(*   the S01_BaseRing and HansonLcm pool in the work directory.  *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import HansonLcm.
Require Import S01_BaseRing (Id, id_refl, NatLe, NatLe_lift, NatLe_drop).

(* ---- Section 1. Linear support for powers and division (nat only, no negation notation) ---- *)

Fixpoint prs_hsum (N C : nat) : nat :=
  match N with
  | 0 => 0
  | S N' => C / S N' + prs_hsum N' C
  end.

Lemma prs_hsum_S : forall N C : nat,
  Id (prs_hsum (S N) C) (C / S N + prs_hsum N C).
Proof. intros N C. apply id_refl. Qed.

Lemma prs_pow_succ : forall j : nat, Id (2 ^ (S j)) (2 * 2 ^ j).
Proof. intros j. apply id_refl. Qed.

Lemma prs_pow2_pos : forall b : nat, NatLe 1 (2 ^ b).
Proof.
  intros b. apply NatLe_lift. induction b as [|b IH].
  - simpl. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma prs_pow2_double : forall j : nat, Id (2 ^ j + 2 ^ j) (2 ^ (S j)).
Proof.
  intros j.
  assert (Hfull : (2 ^ j + 2 ^ j = 2 ^ (S j))%nat)
    by (rewrite Nat.pow_succ_r'; lia).
  rewrite Hfull. apply id_refl.
Qed.

Lemma prs_pow2_sq : forall m : nat, Id (2 ^ m * 2 ^ m) (2 ^ (2 * m)).
Proof.
  intros m.
  assert (Hfull : (2 ^ m * 2 ^ m = 2 ^ (2 * m))%nat).
  { replace (2 * m) with (m + m) by lia.
    symmetry. apply Nat.pow_add_r. }
  rewrite Hfull. apply id_refl.
Qed.

Lemma prs_pow_div : forall a b : nat, NatLe b a -> Id (2 ^ a / 2 ^ b) (2 ^ (a - b)).
Proof.
  intros a b H. apply NatLe_drop in H.
  assert (Hfull : (2 ^ a / 2 ^ b = 2 ^ (a - b))%nat).
  { assert (Hm : (2 ^ b * 2 ^ (a - b) = 2 ^ a)%nat).
    { rewrite <- Nat.pow_add_r. f_equal. lia. }
    assert (Hz : 2 ^ b <> 0).
    { intro H0. pose proof (prs_pow2_pos b) as Hp. apply NatLe_drop in Hp. lia. }
    rewrite <- Hm.
    rewrite (Nat.mul_comm (2 ^ b) (2 ^ (a - b))).
    apply Nat.div_mul. exact Hz. }
  rewrite Hfull. apply id_refl.
Qed.

(* Multiplicative re-association (the host stdlib has no mul_swap; *)
(* built from assoc + comm). *)
Lemma prs_mul_swap : forall a b c : nat, Id (a * (b * c)) (b * (a * c)).
Proof.
  intros a b c.
  assert (Hfull : (a * (b * c) = b * (a * c))%nat)
    by (rewrite Nat.mul_assoc, (Nat.mul_comm a b), <- Nat.mul_assoc; reflexivity).
  rewrite Hfull. apply id_refl.
Qed.

(* Lower division bound: d * (C / d) <= C (assembled from Nat.div_mod, linear core). *)
Lemma prs_mul_div_le : forall d C : nat, NatLe 1 d -> NatLe (d * (C / d)) C.
Proof.
  intros d C Hd. apply NatLe_lift.
  apply NatLe_drop in Hd. destruct d as [|d'].
  - exfalso. lia.
  - assert (Hz : S d' = 0 -> False) by discriminate.
    assert (Hdm : C = S d' * (C / S d') + C mod S d')
      by (apply Nat.div_mod; exact Hz).
    lia.
Qed.

(* Quotient lower bound: k * q <= C with 1 <= k gives q <= C / k (the *)
(* multiplication step is an explicit mul_le_mono, the rest is linear -- *)
(* no unsupported nonlinear step). *)
Lemma prs_div_lower : forall C k q : nat,
  NatLe 1 k -> NatLe (k * q) C -> NatLe q (C / k).
Proof.
  intros C k q Hk Hpq. apply NatLe_lift.
  apply NatLe_drop in Hk. apply NatLe_drop in Hpq.
  destruct k as [|k'].
  - exfalso. lia.
  - assert (Hz : S k' = 0 -> False) by discriminate.
    assert (Hmod : C mod S k' < S k') by (apply Nat.mod_upper_bound; exact Hz).
    assert (Hdm : C = S k' * (C / S k') + C mod S k')
      by (apply Nat.div_mod; exact Hz).
    destruct (le_lt_dec q (C / S k')) as [Hle | Hlt].
    + exact Hle.
    + exfalso.
      assert (Hq1 : C / S k' + 1 <= q) by lia.
      assert (Hmul : S k' * (C / S k' + 1) <= S k' * q)
        by (apply Nat.mul_le_mono_l; exact Hq1).
      assert (Hex : S k' * (C / S k' + 1) = S k' * (C / S k') + S k').
      { rewrite Nat.mul_add_distr_l. lia. }
      lia.
Qed.

(* ---- Section 2. Block gain (splitting the sum over dyadic blocks -- the *)
(*    divergence engine). When every term of the tail (N, N + M] satisfies *)
(*    C / k >= q, the whole sum gains at least M * q. *)

Lemma prs_hsum_block : forall M N C q : nat,
  (forall k : nat, NatLe (S N) k -> NatLe k (N + M) -> NatLe q (C / k)) ->
  NatLe (prs_hsum N C + M * q) (prs_hsum (N + M) C).
Proof.
  intros M. induction M as [|M IH]; intros N C q Hall.
  - replace (N + 0) with N by lia. apply NatLe_lift. lia.
  - replace (N + S M) with (S (N + M)) by lia.
    change (prs_hsum (S (N + M)) C)
      with (C / S (N + M) + prs_hsum (N + M) C).
    apply NatLe_lift.
    assert (IH' : (prs_hsum N C + M * q <= prs_hsum (N + M) C)%nat).
    { apply NatLe_drop. apply IH. intros k H1 H2. apply Hall;
        [exact H1 | apply NatLe_lift; apply NatLe_drop in H2; lia]. }
    assert (Hq : (q <= C / S (N + M))%nat).
    { apply NatLe_drop. apply Hall;
        [apply NatLe_lift; lia | apply NatLe_lift; lia]. }
    rewrite Nat.mul_succ_l. lia.
Qed.

(* ---- Section 3. Scale doubling (C to 2C preserves the term order; the *)
(*    harmonic scale doubles block by block). *)

Lemma prs_hsum_scale2 : forall N C : nat,
  NatLe (2 * prs_hsum N C) (prs_hsum N (2 * C)).
Proof.
  intros N C. apply NatLe_lift. induction N as [|N IH].
  - simpl. lia.
  - change (prs_hsum (S N) C) with (C / S N + prs_hsum N C).
    change (prs_hsum (S N) (2 * C)) with (2 * C / S N + prs_hsum N (2 * C)).
    assert (Hd : (2 * (C / S N) <= 2 * C / S N)%nat).
    { apply NatLe_drop. apply prs_div_lower.
      - apply NatLe_lift. lia.
      - apply NatLe_lift.
        assert (H1 : (S N * (C / S N) <= C)%nat)
          by (apply NatLe_drop; apply prs_mul_div_le; apply NatLe_lift; lia).
        assert (H2 : S N * (2 * (C / S N)) = 2 * (S N * (C / S N)))
          by exact (match prs_mul_swap (S N) 2 (C / S N) in (Id _ y)
                    return (S N * (2 * (C / S N)) = y) with
                    | id_refl => eq_refl end).
        rewrite H2. apply Nat.mul_le_mono_l. exact H1. }
    lia.
Qed.

(* ---- Section 4. Main lemma (the divergence core closes): H >= (m + 1) / 2 *)
(*    at dyadic points -- 2 * sum over k <= 2 ^ m of 2 ^ (2 m) / k >= *)
(*    (m + 1) * 2 ^ (2 m); each block (2 ^ j, 2 ^ (j + 1)] gains exactly *)
(*    2 ^ (2 m - 1) (floor loss-free path). *)

Lemma prs_harm_dyad : forall m : nat,
  NatLe (S m * 2 ^ (2 * m)) (2 * prs_hsum (2 ^ m) (2 ^ (2 * m))).
Proof.
  intros m. apply NatLe_lift. induction m as [|m IH].
  - vm_compute. lia.
  - replace (2 * S m) with (S (S (2 * m))) by lia.
    change (2 ^ S (S (2 * m))) with (2 * 2 ^ S (2 * m)).
    change (2 ^ S (2 * m)) with (2 * 2 ^ (2 * m)).
    assert (Hdb : (2 ^ m + 2 ^ m = 2 ^ S m)%nat)
      by (rewrite Nat.pow_succ_r'; lia).
    rewrite <- Hdb.
    (* Scale doubling: the large sum at scale 2C ties to the small sum at scale C. *)
    assert (Hs_small : 2 * prs_hsum (2 ^ m) (2 ^ (2 * m))
                       <= prs_hsum (2 ^ m) (2 * 2 ^ (2 * m)))
      by (apply NatLe_drop; apply prs_hsum_scale2).
    assert (Hs_big1 : 2 * prs_hsum (2 ^ m + 2 ^ m) (2 ^ (2 * m))
                      <= prs_hsum (2 ^ m + 2 ^ m) (2 * 2 ^ (2 * m)))
      by (apply NatLe_drop; apply prs_hsum_scale2).
    assert (Hs_big2 : 2 * prs_hsum (2 ^ m + 2 ^ m) (2 * 2 ^ (2 * m))
                      <= prs_hsum (2 ^ m + 2 ^ m) (2 * (2 * 2 ^ (2 * m))))
      by (apply NatLe_drop; apply prs_hsum_scale2).
    (* Block gain at scale 2C: the gain is exactly 2 ^ (2 m). *)
    assert (Hsq : (2 ^ m * 2 ^ m = 2 ^ (2 * m))%nat).
    { replace (2 * m) with (m + m) by lia.
      symmetry. apply Nat.pow_add_r. }
    assert (Hval : 2 * 2 ^ (2 * m) / (2 ^ m + 2 ^ m) = 2 ^ m).
    { replace (2 * 2 ^ (2 * m)) with (2 ^ S (2 * m)) by reflexivity.
      rewrite Hdb.
      replace (2 ^ m) with (2 ^ (S (2 * m) - S m)) by (f_equal; lia).
      assert (Hle : NatLe (S m) (S (2 * m))) by (apply NatLe_lift; lia).
      exact (match prs_pow_div (S (2 * m)) (S m) Hle in (Id _ y)
             return (2 ^ S (2 * m) / 2 ^ S m = y) with
             | id_refl => eq_refl end). }
    assert (HX : 2 ^ m * (2 * 2 ^ (2 * m) / (2 ^ m + 2 ^ m)) = 2 ^ (2 * m)).
    { rewrite Hval.
      replace (2 * m) with (m + m) by lia.
      symmetry. apply Nat.pow_add_r. }
    assert (Hb : prs_hsum (2 ^ m) (2 * 2 ^ (2 * m))
                 + 2 ^ m * (2 * 2 ^ (2 * m) / (2 ^ m + 2 ^ m))
                 <= prs_hsum (2 ^ m + 2 ^ m) (2 * 2 ^ (2 * m))).
    { apply NatLe_drop. apply prs_hsum_block. intros k H1 H2.
      apply prs_div_lower;
        [apply NatLe_lift; apply NatLe_drop in H1; lia |].
      apply NatLe_lift. rewrite Hval.
      apply (Nat.le_trans _ ((2 ^ m + 2 ^ m) * 2 ^ m)).
      - apply Nat.mul_le_mono_r. apply NatLe_drop; exact H2.
      - rewrite Nat.mul_add_distr_r, Hsq. lia. }
    (* Close: explicit multiplication steps, linear core to lia. *)
    assert (Hstep : S (S m) * (2 * (2 * 2 ^ (2 * m)))
                    <= 2 * prs_hsum (2 ^ m + 2 ^ m) (2 * (2 * 2 ^ (2 * m)))).
    { rewrite Nat.mul_succ_l.
      assert (Hsw : S m * (2 * (2 * 2 ^ (2 * m)))
                    = 2 * (S m * (2 * 2 ^ (2 * m))))
        by exact (match prs_mul_swap (S m) 2 (2 * 2 ^ (2 * m)) in (Id _ y)
                  return (S m * (2 * (2 * 2 ^ (2 * m))) = y) with
                  | id_refl => eq_refl end).
      rewrite Hsw.
      assert (Hsw2 : S m * (2 * 2 ^ (2 * m)) = 2 * (S m * 2 ^ (2 * m)))
        by exact (match prs_mul_swap (S m) 2 (2 ^ (2 * m)) in (Id _ y)
                  return (S m * (2 * 2 ^ (2 * m)) = y) with
                  | id_refl => eq_refl end).
      assert (H1 : S m * (2 * 2 ^ (2 * m))
                   <= 2 * (2 * prs_hsum (2 ^ m) (2 ^ (2 * m)))).
      { rewrite Hsw2.
        apply Nat.mul_le_mono_l. exact IH. }
      assert (H2 : 2 * (S m * (2 * 2 ^ (2 * m)))
                   <= 2 * (2 * (2 * prs_hsum (2 ^ m) (2 ^ (2 * m))))).
      { apply Nat.mul_le_mono_l. exact H1. }
      assert (H3 : 2 * prs_hsum (2 ^ m + 2 ^ m) (2 * (2 * 2 ^ (2 * m)))
                   >= 2 * (2 * (2 * prs_hsum (2 ^ m) (2 ^ (2 * m))))
                      + 2 * 2 ^ (2 * m)).
      { lia. }
      lia. }
    lia.
Qed.

(* ---- Section 5. Set-level main statement (sigT divergence certificate, transparent) ---- *)

Theorem prs_harm_diverge : forall K : nat,
  { m : nat & NatLe (K * 2 ^ (2 * m)) (prs_hsum (2 ^ m) (2 ^ (2 * m))) }.
Proof.
  intros K. exists (2 * K). apply NatLe_lift.
  pose proof (prs_harm_dyad (2 * K)) as Hd. apply NatLe_drop in Hd.
  assert (Hsplit : S (2 * K) * 2 ^ (2 * (2 * K))
                   = 2 * (K * 2 ^ (2 * (2 * K))) + 2 ^ (2 * (2 * K))).
  { rewrite Nat.mul_succ_l.
    rewrite (Nat.mul_assoc 2 K (2 ^ (2 * (2 * K)))). lia. }
  rewrite Hsplit in Hd.
  lia.
Defined.

(* ---- Section 6. Layer-2 brick: single-prime Euler factor identity *)
(*    (Set-level hl_id carrier). Finite Euler factor: (p - 1) * *)
(*    (1 + p + ... + p ^ e) + 1 = p ^ (e + 1), the finite geometric *)
(*    expansion factor of (1 - 1/p) ^ -1. *)

Fixpoint prs_geo (p e : nat) : nat :=
  match e with
  | 0 => 1
  | S e' => 1 + p * prs_geo p e'
  end.

Lemma prs_geo_S : forall p e : nat,
  Id (prs_geo p (S e)) (1 + p * prs_geo p e).
Proof. intros p e. apply id_refl. Qed.

(* Prop-face scaffold (equation induction). *)
Lemma prs_geo_euler_eq : forall p e : nat,
  NatLe 1 p -> Id (1 + (p - 1) * prs_geo p e) (p ^ (S e)).
Proof.
  intros p e Hp. apply NatLe_drop in Hp.
  assert (Heq : (1 + (p - 1) * prs_geo p e = p ^ (S e))%nat).
  { induction e as [|e IH].
    - simpl. rewrite Nat.mul_1_r. lia.
    - change (prs_geo p (S e)) with (1 + p * prs_geo p e).
      replace (p ^ (S (S e))) with (p * p ^ (S e))
        by (apply Nat.pow_succ_r; lia).
      replace (p * p ^ (S e)) with (p * (1 + (p - 1) * prs_geo p e))
        by (f_equal; exact IH).
      rewrite (Nat.mul_add_distr_l p 1 ((p - 1) * prs_geo p e)).
      rewrite Nat.mul_1_r.
      rewrite Nat.mul_add_distr_l.
      rewrite Nat.mul_1_r.
      lia. }
  rewrite Heq. apply id_refl.
Qed.

(* Set-level main carrier: hl_id equation (HansonLcm carrier, after the *)
(* lcm_eq precedent). *)
Theorem prs_geo_euler : forall p e : nat,
  NatLe 1 p -> hl_id (1 + (p - 1) * prs_geo p e) (p ^ (S e)).
Proof.
  intros p e Hp.
  assert (Heq : 1 + (p - 1) * prs_geo p e = p ^ (S e))
    by exact (match prs_geo_euler_eq p e Hp in (Id _ y)
              return (1 + (p - 1) * prs_geo p e = y) with
              | id_refl => eq_refl end).
  rewrite Heq. apply hl_idrefl.
Defined.

(* ---- Section 7. Numeric smoke checks (small instances, vm_compute, no postulates) ---- *)

Lemma prs_hsum_4_16 : Id (prs_hsum 4 16) 33.
Proof. vm_compute. apply id_refl. Qed.

Lemma prs_hsum_8_64 : Id (prs_hsum 8 64) 172.
Proof. vm_compute. apply id_refl. Qed.

Lemma prs_hsum_16_256 : Id (prs_hsum 16 256) 861.
Proof. vm_compute. apply id_refl. Qed.

Lemma prs_dyad_smoke_2 : NatLe (S 2 * 2 ^ (2 * 2)) (2 * prs_hsum (2 ^ 2) (2 ^ (2 * 2))).
Proof. apply NatLe_lift. vm_compute. lia. Qed.

Lemma prs_dyad_smoke_3 : NatLe (S 3 * 2 ^ (2 * 3)) (2 * prs_hsum (2 ^ 3) (2 ^ (2 * 3))).
Proof. apply NatLe_lift. vm_compute. lia. Qed.

Lemma prs_diverge_smoke_3 : NatLe (3 * 2 ^ (2 * 6)) (prs_hsum (2 ^ 6) (2 ^ (2 * 6))).
Proof. apply NatLe_lift. vm_compute. lia. Qed.

Lemma prs_geo_2_4 : Id (prs_geo 2 4) 31.
Proof. vm_compute. apply id_refl. Qed.

Lemma prs_geo_euler_smoke : hl_id (1 + (2 - 1) * prs_geo 2 4) (2 ^ 5).
Proof. vm_compute. apply hl_idrefl. Qed.

(* ---- Section 8. Obstruction register (fail-loud: the full layer-2 and *)
(*    layer-3 goals are out of reach here and explicitly registered).    *)
(*    O1, layer 2 full form (finite Euler product): target nat form      *)
(*    sigma(L) * prod over p <= n of (p - 1) <= L * prod over p <= n of p *)
(*    with L = hl_lcm_upto n and sigma(L) = sum of divisors of L. The    *)
(*    lower half is in place in this file: sum over k <= n of L / k <=   *)
(*    sigma(L) needs only hl_lcm_divide_all (k <= n implies k divides L, *)
(*    ready in the cache root) plus the divisor-enumeration sum; the     *)
(*    single-prime factor identity prs_geo_euler is closed (Section 6).  *)
(*    Gap (not closed in this slice): sigma(L) <= product over p <= n of *)
(*    prs_geo p (plm_v p L) needs (a) injectivity of the exponent vector *)
(*    (unique decomposition of the prime-power fold of one nat value:    *)
(*    p ^ a divides the product of q ^ b_q and p divides none of the     *)
(*    others implies a <= b_p -- rebuildable by two-stage induction with *)
(*    plm_dvd_mul_coprime / plm_gcd_pow, roughly a hundred lines) and    *)
(*    (b) the sum decomposition of the divisor-enumeration machine       *)
(*    (fold-product distributivity of sigma over prime powers). The      *)
(*    combined size exceeds this slice's budget.                         *)
(*    O2, layer 3 (weak Mertens): sum over p <= n of 1/p >= log log(n+1) *)
(*    needs a Q-level log; the cache root Q face has rational powers and *)
(*    QleT' but no log. The dyadic core of Section 4 is the log-free     *)
(*    stand-in: H_n >= (m + 1) / 2 at n = 2 ^ m (prs_harm_dyad); once    *)
(*    layer 2 closes, the transfer through product over p <= n of        *)
(*    (1 - 1/p) ^ -1 >= H_n yields unboundedness of the prime reciprocal *)
(*    sum; the log log form stays with a successor file.                 *)
(*    Consumer guide (successor files): the six prime files, the         *)
(*    Bertrand file, the fact-growth bridge, and HansonLcm's hl_lcm_upto *)
(*    are all consumed at the two O1 gaps only; this file consumes none  *)
(*    of them (minimal dependency face). *)

(* ---- Section 9. Assumption audit (Print Assumptions evidence) ---- *)

Print Assumptions prs_mul_div_le.
Print Assumptions prs_div_lower.
Print Assumptions prs_hsum_block.
Print Assumptions prs_hsum_scale2.
Print Assumptions prs_harm_dyad.
Print Assumptions prs_harm_diverge.
Print Assumptions prs_geo_euler_eq.
Print Assumptions prs_geo_euler.
