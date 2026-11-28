(* ========================================================================= *)
(* Module   : abl_Pr_erdos_theta                                             *)
(* Mission. A constructive Chebyshev-type linear bound for the prime         *)
(*            counting function theta: with pec_prim N the primorial of N    *)
(*            (the folded table of primes in (1, N]), the classical bound    *)
(*            theta(N) <= 4 ln 2 * N takes the nat carrier form              *)
(*            pec_prim N <= 4^(2N), proved by the Erdos binomial-window      *)
(*            dyadic telescope: window tables split over half intervals,     *)
(*            the primorial doubles by pec_prim(2^(j+1)) = pec_prim(2^j) *   *)
(*            prod_{2^j < p <= 2^(j+1)} p with prod_{n < p <= 2n} p <=       *)
(*            C(2n,n) <= 4^n, and a computable halving witness K with        *)
(*            2^K <= N < 2^(K+1) closes the telescope at 4^(2^(K+1)-1)       *)
(*            <= 4^(2N).                                                     *)
(* Dependencies. HansonLcm (hl_id, hl_le_t, hl_le_to_le_t, hl_le_t_to_le),   *)
(*            abl_Pr_core_01 (pr_prime, pr_prime_bool), abl_Pr_erdos_core    *)
(*            (pec_win, pec_winprod, pec_mid, pec_erdos_skeleton,            *)
(*            pec_skeleton_lt, pec_win_in); Stdlib Arith/Bool/List/Lia.      *)
(* References. The Erdos binomial-window proof of the Bertrand postulate     *)
(*            (central binomial coefficient C(2n,n) < 4^n plus the window    *)
(*            telescope); Set-carrier conventions follow HansonLcm.          *)
(* Constructivity. Every statement is Set-sorted: conclusions and premises   *)
(*            ride hl_id/hl_le_t (the Nat.leb-equality identity in Set), the *)
(*            halving witness pec_log2_ex is a sigT with purely Set payload, *)
(*            and Prop occurs only inside proof bodies. Qed is confined to   *)
(*            proof-scaffold lemmas outside the extraction face (reason:     *)
(*            reasoning bridges, not data); carrier Definitions and the      *)
(*            witness lemma are Defined; vm_compute hits five numeric pins.  *)
(* Build. rocq c -native-compiler no -q -Q <Set Live root> ""                *)
(*            abl_Pr_erdos_theta.v (this directory as workdir).              *)
(* ========================================================================= *)

From Stdlib Require Import Arith.Arith Bool Lia List.
Require Import HansonLcm.
Require Import abl_Pr_core_01.
Require Import abl_Pr_erdos_core.

(* ============================================================ *)
(* Section 1: window-table splitting and product algebra        *)
(* ============================================================ *)

(* The window table splits over a half interval: the primes of        *)
(* (a, a + k + k'] listed descending are the high half followed by    *)
(* the low half, carried by the Set-level identity [hl_id].           *)
Lemma pec_win_app : forall a k k' : nat,
  hl_id (pec_win a (k + k')) (pec_win (a + k) k' ++ pec_win a k).
Proof.
  intros a k. induction k' as [|k' IH].
  - replace (k + 0) with k by lia.
    cbn [pec_win app]. apply hl_idrefl.
  - replace (k + S k') with (S (k + k')) by lia.
    cbn [pec_win app].
    replace (a + S (k + k')) with (a + k + S k') by lia.
    destruct (pr_prime_bool (a + k + S k')).
    + rewrite (hl_id_eq _ _ _ IH). rewrite app_comm_cons. apply hl_idrefl.
    + exact IH.
Qed.

(* The folded product turns concatenation into multiplication. *)
Lemma pec_prod_app : forall l1 l2 : list nat,
  hl_id (fold_right Nat.mul 1 (l1 ++ l2))
        (fold_right Nat.mul 1 l1 * fold_right Nat.mul 1 l2).
Proof.
  induction l1 as [|q l1 IH]; intro l2.
  - cbn [fold_right app]. rewrite Nat.mul_1_l. apply hl_idrefl.
  - cbn [fold_right app]. rewrite (hl_id_eq _ _ _ (IH l2)).
    rewrite Nat.mul_assoc. apply hl_idrefl.
Qed.

(* A window table folds to at least 1, since every entry is at least 1. *)
Lemma pec_winprod_ge1 : forall a k : nat,
  hl_le_t 1 (fold_right Nat.mul 1 (pec_win a k)).
Proof.
  intro a. induction k as [|k IH].
  - cbn [pec_win fold_right]. apply hl_le_to_le_t. lia.
  - cbn [pec_win fold_right]. destruct (pr_prime_bool (a + S k)).
    + cbn [fold_right]. apply hl_le_to_le_t. apply Nat.le_trans with (1 * 1).
      * lia.
      * apply Nat.mul_le_mono; [lia | apply hl_le_t_to_le; exact IH].
    + cbn [fold_right]. exact IH.
Qed.

(* ============================================================ *)
(* Section 2: primorial definition and the window-product bound  *)
(* ============================================================ *)

(* The primorial of N: the folded table of primes in (1, N]. *)
Definition pec_prim (n : nat) : nat := fold_right Nat.mul 1 (pec_win 1 (n - 1)).

(* Window product bound: prod_{n < p <= 2n} p <= C(2n,n) <= 4^n *)
(* (both halves of the Erdos skeleton of abl_Pr_erdos_core).    *)
Lemma pec_winprod_le : forall n : nat, hl_le_t (pec_winprod n) (4 ^ n).
Proof.
  intro n. destruct (pec_erdos_skeleton n) as [_ [H1 H2]].
  apply hl_le_to_le_t. apply Nat.le_trans with (pec_mid n).
  - apply hl_le_t_to_le. exact H1.
  - apply hl_le_t_to_le. exact H2.
Qed.

(* Strict form: n >= 1 gives prod_{n < p <= 2n} p + 2 <= 4^n *)
(* (the middle term coexists with the two row-end ones).     *)
Lemma pec_winprod_lt : forall n : nat,
  hl_le_t 1 n -> hl_le_t (pec_winprod n + 2) (4 ^ n).
Proof.
  intros n Hn. apply hl_le_t_to_le in Hn.
  apply hl_le_to_le_t. apply Nat.le_trans with (pec_mid n + 2).
  - apply Nat.add_le_mono.
    + apply hl_le_t_to_le. destruct (pec_erdos_skeleton n) as [_ [H1 _]]. exact H1.
    + lia.
  - apply hl_le_t_to_le. apply pec_skeleton_lt. exact Hn.
Qed.

(* ============================================================ *)
(* Section 3: doubling identity and the dyadic ladder           *)
(* ============================================================ *)

(* Doubling identity: pec_prim(2^(j+1)) = pec_prim(2^j) *         *)
(* prod_{2^j < p <= 2^(j+1)} p (the half-open table (1, 2^(j+1)]  *)
(* splits at 2^j).                                                *)
Lemma pec_prim_step : forall j : nat,
  hl_id (pec_prim (2 ^ S j)) (pec_prim (2 ^ j) * pec_winprod (2 ^ j)).
Proof.
  intro j. unfold pec_prim.
  rewrite Nat.pow_succ_r'.
  replace (2 * 2 ^ j - 1) with (2 ^ j - 1 + 2 ^ j) by lia.
  rewrite (hl_id_eq _ _ _ (pec_win_app 1 (2 ^ j - 1) (2 ^ j))).
  rewrite (hl_id_eq _ _ _
             (pec_prod_app (pec_win (1 + (2 ^ j - 1)) (2 ^ j)) (pec_win 1 (2 ^ j - 1)))).
  assert (Hjp : 1 <= 2 ^ j).
  { assert (H0 : 2 ^ j <> 0) by (apply Nat.pow_nonzero; lia). lia. }
  replace (1 + (2 ^ j - 1)) with (2 ^ j) by lia.
  rewrite Nat.mul_comm. apply hl_idrefl.
Qed.

(* Dyadic rung: pec_prim(2^j) <= 4^(2^j - 1); each step up multiplies *)
(* by a window product at most 4^(2^j) and the exponent adds up.      *)
Lemma pec_prim_dyad_le : forall j : nat,
  hl_le_t (pec_prim (2 ^ j)) (4 ^ (2 ^ j - 1)).
Proof.
  induction j as [|j IH].
  - cbn [pec_prim pec_win fold_right Nat.pow Nat.sub].
    apply hl_le_to_le_t. lia.
  - rewrite (hl_id_eq _ _ _ (pec_prim_step j)).
    apply hl_le_to_le_t. apply Nat.le_trans with (4 ^ (2 ^ j - 1) * 4 ^ (2 ^ j)).
    + apply Nat.mul_le_mono;
        [apply hl_le_t_to_le; exact IH | apply hl_le_t_to_le; apply pec_winprod_le].
    + replace (2 ^ S j - 1) with (2 ^ j - 1 + 2 ^ j) by (rewrite Nat.pow_succ_r'; lia).
      rewrite Nat.pow_add_r. apply Nat.le_refl.
Qed.

(* ============================================================ *)
(* Section 4: computable halving witness and primorial monotone  *)
(* ============================================================ *)

(* Halving witness: for N >= 1 a computable K satisfies              *)
(* 2^K <= N < 2^(K+1); the sigT payload is purely Set-carried.       *)
Lemma pec_log2_ex : forall N : nat,
  hl_le_t 1 N -> { K : nat & hl_le_t (2 ^ K) N * hl_le_t (S N) (2 ^ S K) }.
Proof.
  intro N. induction N as [|N IH]; intro HN.
  - exfalso. apply hl_le_t_to_le in HN. lia.
  - destruct N as [|N'].
    + exists 0. split; cbn [Nat.pow].
      * apply hl_le_to_le_t. lia.
      * apply hl_le_to_le_t. lia.
    + assert (H1 : hl_le_t 1 (S N')) by exact (hl_idrefl true).
      destruct (IH H1) as [K [Hlo Hhi]].
      apply hl_le_t_to_le in Hlo. apply hl_le_t_to_le in Hhi.
      destruct (le_lt_dec (2 ^ S K) (S (S N'))) as [Hle | Hgt].
      * exists (S K). split.
        -- apply hl_le_to_le_t. exact Hle.
        -- apply hl_le_to_le_t. rewrite Nat.pow_succ_r'. lia.
      * exists K. split.
        -- apply hl_le_to_le_t. lia.
        -- apply hl_le_to_le_t. lia.
Defined.

(* Primorial monotonicity: 1 <= N <= M gives pec_prim N <= pec_prim M *)
(* (the long table is a prefix plus the (N, M] segment, whose product *)
(* is at least 1).                                                    *)
Lemma pec_prim_monotone : forall N M : nat,
  hl_le_t 1 N -> hl_le_t N M -> hl_le_t (pec_prim N) (pec_prim M).
Proof.
  intros N M HN HM. apply hl_le_t_to_le in HN. apply hl_le_t_to_le in HM.
  unfold pec_prim.
  replace (M - 1) with (N - 1 + (M - N)) by lia.
  rewrite (hl_id_eq _ _ _ (pec_win_app 1 (N - 1) (M - N))).
  rewrite (hl_id_eq _ _ _
             (pec_prod_app (pec_win (1 + (N - 1)) (M - N)) (pec_win 1 (N - 1)))).
  replace (1 + (N - 1)) with N by lia.
  rewrite Nat.mul_comm.
  apply hl_le_to_le_t. apply Nat.le_trans with (fold_right Nat.mul 1 (pec_win 1 (N - 1)) * 1).
  + rewrite Nat.mul_1_r. apply Nat.le_refl.
  + apply Nat.mul_le_mono_l. apply hl_le_t_to_le. apply pec_winprod_ge1.
Qed.

(* ============================================================ *)
(* Section 5: the main bound, theta(N) <= 4 ln 2 * N in nat form *)
(* ============================================================ *)

(* Main theorem: pec_prim N <= 4^(2N). Telescope: N in [2^K, 2^(K+1)) *)
(* gives pec_prim N <= pec_prim(2^(K+1)) <= 4^(2^(K+1)-1) <= 4^(2N),  *)
(* the last step using 2^(K+1) = 2 * 2^K <= 2N.                       *)
Theorem pec_theta_bound : forall N : nat,
  hl_le_t 1 N -> hl_le_t (pec_prim N) (4 ^ (2 * N))%nat.
Proof.
  intros N HN. apply hl_le_to_le_t.
  destruct (pec_log2_ex N HN) as [K [Hlo Hhi]].
  apply hl_le_t_to_le in Hhi.
  apply Nat.le_trans with (pec_prim (2 ^ S K)).
  - apply hl_le_t_to_le. apply pec_prim_monotone; [exact HN | apply hl_le_to_le_t; lia].
  - apply Nat.le_trans with (4 ^ (2 ^ S K - 1)).
    + apply hl_le_t_to_le. apply pec_prim_dyad_le.
    + apply (Nat.pow_le_mono_r 4 (2 ^ S K - 1) (2 * N)).
      * lia.
      * apply hl_le_t_to_le in Hlo. rewrite Nat.pow_succ_r'. lia.
Qed.

(* Decidable check carrier: the bound as a boolean test on N,     *)
(* specialized to the concrete primorial carrier.                 *)
Definition pec_theta_check (N : nat) : bool := Nat.leb (pec_prim N) (4 ^ (2 * N)).

Theorem pec_theta_check_true : forall N : nat,
  hl_le_t 1 N -> hl_id (pec_theta_check N) true.
Proof. intros N HN. exact (pec_theta_bound N HN). Qed.

(* ============================================================ *)
(* Section 6: numeric pins (vm_compute confined to these)        *)
(* ============================================================ *)

Lemma pec_smoke_prim1 : hl_id (pec_prim 1) 1.
Proof. vm_compute. apply hl_idrefl. Qed.

Lemma pec_smoke_win19 : hl_id (pec_win 1 9) (7 :: 5 :: 3 :: 2 :: nil)%list.
Proof. vm_compute. apply hl_idrefl. Qed.

Lemma pec_smoke_prim10 : hl_id (pec_prim 10) 210.
Proof. vm_compute. apply hl_idrefl. Qed.

Lemma pec_smoke_win49 : hl_id (pec_win 4 9) (13 :: 11 :: 7 :: 5 :: nil)%list.
Proof. vm_compute. apply hl_idrefl. Qed.

Lemma pec_smoke_theta6 : hl_le_t (pec_prim 6) (4 ^ 6)%nat.
Proof. vm_compute. apply hl_idrefl. Qed.

(* ============================================================ *)
(* Section 7: assumption audit and extraction check              *)
(* ============================================================ *)

Print Assumptions pec_win_app.
Print Assumptions pec_prod_app.
Print Assumptions pec_winprod_ge1.
Print Assumptions pec_winprod_le.
Print Assumptions pec_winprod_lt.
Print Assumptions pec_prim_step.
Print Assumptions pec_prim_dyad_le.
Print Assumptions pec_log2_ex.
Print Assumptions pec_prim_monotone.
Print Assumptions pec_theta_bound.
Print Assumptions pec_theta_check_true.
Print Assumptions pec_smoke_prim1.
Print Assumptions pec_smoke_win19.
Print Assumptions pec_smoke_prim10.
Print Assumptions pec_smoke_win49.
Print Assumptions pec_smoke_theta6.

From Stdlib Require Import Extraction.
Separate Extraction pec_prim pec_win pec_winprod pec_theta_check.
