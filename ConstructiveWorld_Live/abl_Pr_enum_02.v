(* ============================================================ *)
(* abl_Pr_enum_02.v -- prime-domain enumeration file (prime suite 3).  *)
(* Mission. Four nat-level prime enumeration faces: (1) the counting   *)
(*   machine pen_count_upto / pen_count_seg with additive split and     *)
(*   the no-prime/unique-prime window lemmas ("the k-th prime"); (2)    *)
(*   the next-prime search pen_next_prime with its four-part spec; (3)  *)
(*   the k-th prime enumerator pen_nth_prime with a two-part spec and   *)
(*   the sigT witness form pen_nth_prime_exists (Defined); (4) the      *)
(*   prime list pen_primes_upto with its In characterisation, the       *)
(*   primorial pen_primorial, the primorial-successor coprimality and   *)
(*   pen_euclid_new_prime (Euclid structure, enumeration side), plus    *)
(*   pen_prime_unbounded and pen_coprime_of_neq.                        *)
(* Dependencies. Stdlib (Arith.Arith, List, Bool, Lia); abl_Pr_core_01  *)
(*   (pr_prime, pr_prime_bool both ways, pr_min_factor_exists);         *)
(*   S01_BaseRing (Id, id_refl, id_sym, And, NatLe, NatLe_lift,         *)
(*   NatLe_drop). No other project files.                               *)
(* References. pr_prime, pr_prime_bool_true, pr_prime_bool_false,       *)
(*   pr_min_factor_exists, NatLe_lift, NatLe_drop, id_refl, id_sym.     *)
(* Constructivity. Set-level carriers: m1 statement faces are washed    *)
(*   into Id / NatLe / sigT; premises keep their Prop faces. The In     *)
(*   station pen_in_primes_upto keeps its stdlib In conclusion          *)
(*   (CAPTURE pool, pending adjudication). Witness forms are sigT       *)
(*   (Defined); negation is self-carried as P -> False only.            *)
(*   Axioms: none (assumption audit in Section 6). Computational parts  *)
(*   are first-order nat/bool/list Fixpoints, extractable; fuel         *)
(*   adequacy stays an explicit window premise; smoke instances <= 10.  *)
(* Build. Rocq 9.1.0. Compile abl_Pr_core_01.v first, then              *)
(*   rocq c -native-compiler no -Q <vo_world> "" -Q . ""                *)
(*   abl_Pr_enum_02.v (item 1 is required from the pool path).          *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import abl_Pr_core_01.
Require Import S01_BaseRing (Id, id_refl, id_sym, And, NatLe, NatLe_lift, NatLe_drop).

(* ---- Section 1. The prime counting machine (computable carrier for
   "the k-th prime") ----
   pen_count_upto n = number of primes in [2, n];
   pen_count_seg m d = number of primes in (m, m + d]. *)

Fixpoint pen_count_upto (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => pen_count_upto m + (if pr_prime_bool (S m) then 1 else 0)
  end.

Fixpoint pen_count_seg (m d : nat) : nat :=
  match d with
  | 0 => 0
  | S d' => pen_count_seg m d' + (if pr_prime_bool (m + S d') then 1 else 0)
  end.

(* Definitional unfolding lemmas (structural equations, shielding the
   simpl behaviour of the deciders). *)
Lemma pen_count_upto_S : forall m : nat,
  Id (pen_count_upto (S m))
     (pen_count_upto m + (if pr_prime_bool (S m) then 1 else 0)).
Proof. reflexivity. Qed.

Lemma pen_count_seg_S : forall m d : nat,
  Id (pen_count_seg m (S d))
     (pen_count_seg m d + (if pr_prime_bool (m + S d) then 1 else 0)).
Proof. reflexivity. Qed.

(* Additivity of the count: primes in [2, n+d] = primes in [2, n]
   plus primes in (n, n+d]. *)
Lemma pen_count_split : forall n d : nat,
  Id (pen_count_upto (n + d)) (pen_count_upto n + pen_count_seg n d).
Proof.
  intros n d. induction d as [|d IH].
  - rewrite Nat.add_0_r. change (pen_count_seg n 0) with 0.
    rewrite Nat.add_0_r. reflexivity.
  - assert (IHp : pen_count_upto (n + d) = pen_count_upto n + pen_count_seg n d).
    { destruct IH. reflexivity. }
    assert (Hcore : pen_count_upto (n + S d) =
                    pen_count_upto n + pen_count_seg n (S d)).
    { assert (Hs : n + S d = S (n + d)) by apply Nat.add_succ_r.
      rewrite Hs. destruct (id_sym (pen_count_upto_S (n + d))).
      destruct (id_sym (pen_count_seg_S n d)).
      rewrite <- Hs. rewrite IHp. symmetry. apply Nat.add_assoc. }
    destruct Hcore. reflexivity.
Qed.

(* An empty window counts zero (backward: no prime in the window gives
   a zero count). *)
Lemma pen_count_seg_none : forall d m : nat,
  (forall q : nat, pr_prime q -> m < q -> q <= m + d -> False) ->
  Id (pen_count_seg m d) 0.
Proof.
  intros d. induction d as [|d IH]; intros m Hnone.
  - reflexivity.
  - destruct (id_sym (pen_count_seg_S m d)).
    assert (Hb0 : pr_prime_bool (m + S d) = false).
    { destruct (pr_prime_bool (m + S d)) eqn:Eb; [|reflexivity].
      exfalso. apply (Hnone (m + S d)).
      - apply pr_prime_bool_true. exact Eb.
      - lia.
      - lia. }
    rewrite Hb0. change (if false then 1 else 0) with 0.
    rewrite Nat.add_0_r. apply IH.
    intros q Hq Hmq Hqle.
    destruct (Nat.eq_dec q (m + S d)) as [Hqe|Hqne].
    + exfalso. rewrite Hqe in Hq.
      assert (Hbt : pr_prime_bool (m + S d) = true).
      { exact (match pr_prime_bool_false (m + S d) Hq
               in (Id _ z) return (pr_prime_bool (m + S d) = z)
               with id_refl => eq_refl end). }
      rewrite Hbt in Hb0. discriminate.
    + apply (Hnone q Hq Hmq). lia.
Qed.

(* A window holding exactly one prime (a unique prime p in the window)
   counts one. *)
Lemma pen_count_seg_one : forall d m p : nat, pr_prime p -> m < p -> p <= m + d ->
  (forall q : nat, pr_prime q -> m < q -> q <= m + d -> q = p) ->
  Id (pen_count_seg m d) 1.
Proof.
  intros d. induction d as [|d IH]; intros m p Hp Hmp Hple Huniq.
  - exfalso. lia.
  - destruct (id_sym (pen_count_seg_S m d)).
    destruct (le_lt_dec p (m + d)) as [Hpd|Hplt].
    + (* p inside the inner window: the outer endpoint m + S d is not
         prime, delta = 0, IH closes. *)
      assert (Hb0 : pr_prime_bool (m + S d) = false).
      { destruct (pr_prime_bool (m + S d)) eqn:Eb; [|reflexivity].
        exfalso.
        assert (Hpmd : pr_prime (m + S d)) by (apply pr_prime_bool_true; exact Eb).
        assert (Heq : m + S d = p) by (apply (Huniq (m + S d) Hpmd); lia).
        lia. }
      rewrite Hb0. change (if false then 1 else 0) with 0.
      rewrite Nat.add_0_r. apply (IH m p Hp Hmp Hpd).
      intros q Hq Hmq Hqle. apply (Huniq q Hq); [exact Hmq | lia].
    + (* p = m + S d: the inner window has no prime (else uniqueness
         breaks), delta = 1. *)
      assert (Heq : p = m + S d) by lia.
      assert (Hb : pr_prime_bool (m + S d) = true).
      { assert (Hpmd : pr_prime (m + S d)) by (rewrite <- Heq; exact Hp).
        exact (match pr_prime_bool_false (m + S d) Hpmd
               in (Id _ z) return (pr_prime_bool (m + S d) = z)
               with id_refl => eq_refl end). }
      assert (Hseg0 : pen_count_seg m d = 0).
      { assert (Hi : Id (pen_count_seg m d) 0).
        { apply pen_count_seg_none. intros q Hq Hmq Hqle.
          assert (Hqe : q = p) by (apply (Huniq q Hq); [exact Hmq | lia]).
          lia. }
        destruct Hi. reflexivity. }
      rewrite Hb. change (if true then 1 else 0) with 1.
      rewrite Hseg0. reflexivity.
Qed.

(* Basic counting facts: reading at 1, the prime step, monotonicity,
   largest-prime extraction, strict monotonicity and injectivity on
   primes. *)
Lemma pen_count_upto_1 : Id (pen_count_upto 1) 0.
Proof. reflexivity. Qed.

Lemma pen_count_upto_step : forall n : nat, 1 <= n -> pr_prime n ->
  Id (pen_count_upto n) (pen_count_upto (n - 1) + 1).
Proof.
  intros n Hn Hp. destruct n as [|m]; [exfalso; lia|].
  assert (Hcore : pen_count_upto (S m) = pen_count_upto (S m - 1) + 1).
  { destruct (id_sym (pen_count_upto_S m)).
    assert (Hb : pr_prime_bool (S m) = true).
    { exact (match pr_prime_bool_false (S m) Hp
             in (Id _ z) return (pr_prime_bool (S m) = z)
             with id_refl => eq_refl end). }
    rewrite Hb. change (if true then 1 else 0) with 1.
    assert (Hsm : S m - 1 = m) by lia. rewrite Hsm. reflexivity. }
  destruct Hcore. reflexivity.
Qed.

Lemma pen_count_mono : forall a b : nat, a <= b -> NatLe (pen_count_upto a) (pen_count_upto b).
Proof.
  intros a b. induction b as [|m IH]; intros Hab.
  - assert (Ha0 : a = 0) by lia. subst a. apply NatLe_lift. apply Nat.le_refl.
  - destruct (Nat.eq_dec a (S m)) as [Hae|Hane].
    + rewrite Hae. apply NatLe_lift. apply Nat.le_refl.
    + assert (Ham : a <= m) by lia.
      specialize (IH Ham).
      destruct (id_sym (pen_count_upto_S m)).
      apply NatLe_lift. pose proof (NatLe_drop _ _ IH). lia.
Qed.

(* A nonzero count yields a largest prime r <= n keeping the reading. *)
Lemma pen_count_upto_largest : forall n : nat, 1 <= pen_count_upto n ->
  sigT (fun r : nat => And (pr_prime r)
                            (And (NatLe r n)
                                 (Id (pen_count_upto r) (pen_count_upto n)))).
Proof.
  intros n. induction n as [|m IH]; intros Hpos.
  - exfalso. simpl in Hpos. lia.
  - destruct (pr_prime_bool (S m)) eqn:Hb.
    + exists (S m). split.
      * apply pr_prime_bool_true. exact Hb.
      * split; [apply NatLe_lift; lia | apply id_refl].
    + assert (Hcount : pen_count_upto (S m) = pen_count_upto m).
      { destruct (id_sym (pen_count_upto_S m)).
        rewrite Hb. change (if false then 1 else 0) with 0.
        rewrite Nat.add_0_r. reflexivity. }
      assert (Hpos' : 1 <= pen_count_upto m) by (rewrite Hcount in Hpos; exact Hpos).
      destruct (IH Hpos') as [r Hrp].
      pose proof (fst Hrp) as Hr.
      pose proof (fst (snd Hrp)) as Hrle.
      pose proof (snd (snd Hrp)) as Hrc.
      exists r. split; [exact Hr |]. split.
      * apply NatLe_lift. pose proof (NatLe_drop _ _ Hrle). lia.
      * rewrite Hcount. exact Hrc.
Qed.

(* Strict monotonicity on primes: p and r both prime with p < r gives
   a strictly smaller reading at p. *)
Lemma pen_count_lt_prime : forall p r : nat, pr_prime p -> pr_prime r -> p < r ->
  NatLe (S (pen_count_upto p)) (pen_count_upto r).
Proof.
  intros p r Hp Hr Hlt.
  pose proof (fst Hr) as Hr2.
  pose proof (snd Hr) as Hrd.
  assert (Hstep : Id (pen_count_upto r) (pen_count_upto (r - 1) + 1)).
  { apply (pen_count_upto_step r); [lia | split; [exact Hr2 | exact Hrd]]. }
  assert (Hmono : pen_count_upto p <= pen_count_upto (r - 1)).
  { assert (Hpre : p <= r - 1) by lia.
    exact (NatLe_drop _ _ (pen_count_mono p (r - 1) Hpre)). }
  apply NatLe_lift.
  destruct (id_sym Hstep).
  lia.
Qed.

(* Injectivity of the count on primes: two primes with equal readings
   are equal. *)
Lemma pen_count_inj : forall p r : nat, pr_prime p -> pr_prime r ->
  pen_count_upto p = pen_count_upto r -> Id p r.
Proof.
  intros p r Hp Hr Heq.
  destruct (lt_eq_lt_dec p r) as [[Hlt|Heqr]|Hgt].
  - exfalso.
    assert (Hltc : pen_count_upto p < pen_count_upto r)
      by (pose proof (NatLe_drop _ _ (pen_count_lt_prime p r Hp Hr Hlt)); lia).
    lia.
  - rewrite Heqr. reflexivity.
  - exfalso.
    assert (Hgtc : pen_count_upto r < pen_count_upto p)
      by (pose proof (NatLe_drop _ _ (pen_count_lt_prime r p Hr Hp Hgt)); lia).
    lia.
Qed.

(* ---- Section 2. The next-prime search (fuel f descending, scan start
   m ascending, decided by pr_prime_bool) ----
   pen_next_prime f m scans [m, m + f) upward for the first prime;
   exhausted fuel falls back to 0. *)

Fixpoint pen_next_prime (f m : nat) : nat :=
  match f with
  | 0 => 0
  | S f' => if pr_prime_bool m then m else pen_next_prime f' (S m)
  end.

Lemma pen_next_prime_S : forall f m : nat,
  Id (pen_next_prime (S f) m)
     (if pr_prime_bool m then m else pen_next_prime f (S m)).
Proof. reflexivity. Qed.

(* Four-part correctness: if the window truly holds a prime, the result
   is prime, respects the start, falls inside the window, and is the
   smallest prime in the window. *)
Theorem pen_next_prime_spec : forall f m : nat,
  (exists q : nat, pr_prime_bool q = true /\ m <= q /\ q < m + f) ->
  And (Id (pr_prime_bool (pen_next_prime f m)) true)
      (And (NatLe m (pen_next_prime f m))
           (And (NatLe (S (pen_next_prime f m)) (m + f))
                (forall q : nat, pr_prime q -> NatLe m q ->
                                 NatLe (pen_next_prime f m) q))).
Proof.
  intros f. induction f as [|f IH]; intros m Hget.
  - exfalso. destruct Hget as [q [Hq [Hq1 Hq2]]]. lia.
  - destruct (id_sym (pen_next_prime_S f m)).
    destruct (pr_prime_bool m) eqn:Hb.
    + change (if true then m else pen_next_prime f (S m)) with m.
      split; [|split; [|split]].
      * rewrite Hb. reflexivity.
      * apply NatLe_lift. lia.
      * apply NatLe_lift. lia.
      * intros q0 Hq0 Hmq0. exact Hmq0.
    + change (if false then m else pen_next_prime f (S m)) with (pen_next_prime f (S m)).
      assert (Hmnp : pr_prime m -> False).
      { intros Hpm.
        assert (Hbt : pr_prime_bool m = true).
        { exact (match pr_prime_bool_false m Hpm
                 in (Id _ z) return (pr_prime_bool m = z)
                 with id_refl => eq_refl end). }
        rewrite Hbt in Hb. discriminate. }
      assert (Hwin : exists q0 : nat, pr_prime_bool q0 = true /\ S m <= q0 /\ q0 < S m + f).
      { destruct Hget as [q [Hq [Hq1 Hq2]]].
        assert (Hqm : S m <= q).
        { destruct (Nat.eq_dec q m) as [Hqe|Hqne].
          - exfalso. rewrite Hqe in Hq. exact (Hmnp (pr_prime_bool_true m Hq)).
          - lia. }
        exists q. split; [exact Hq | split; [exact Hqm | lia]]. }
      destruct (IH (S m) Hwin) as [Hp [Hp1 [Hp2 Hp4]]].
      split; [|split; [|split]].
      * exact Hp.
      * apply NatLe_lift. pose proof (NatLe_drop _ _ Hp1). lia.
      * apply NatLe_lift. pose proof (NatLe_drop _ _ Hp2). lia.
      * intros q0 Hq0 Hmq0.
        destruct (Nat.eq_dec q0 m) as [Hqe|Hqne].
        -- exfalso. apply Hmnp. rewrite <- Hqe. exact Hq0.
        -- apply Hp4; [exact Hq0 | apply NatLe_lift; pose proof (NatLe_drop _ _ Hmq0); lia].
Qed.

(* Reading fact: the search result is exactly the prime that pushes the
   count to "reading before the start, plus one". *)
Lemma pen_count_next_prime : forall f m : nat, 1 <= m ->
  (exists q : nat, pr_prime_bool q = true /\ m <= q /\ q < m + f) ->
  Id (pen_count_upto (pen_next_prime f m)) (pen_count_upto (m - 1) + 1).
Proof.
  intros f m Hm Hget.
  destruct (pen_next_prime_spec f m Hget) as [Hp [Hmle [Hplt Hmin]]].
  pose proof (NatLe_drop _ _ Hmle) as Hmlep.
  pose proof (NatLe_drop _ _ Hplt) as Hpltp.
  assert (Hsplit : pen_next_prime f m = (m - 1) + (pen_next_prime f m - (m - 1))) by lia.
  rewrite Hsplit.
  destruct (id_sym (pen_count_split (m - 1) (pen_next_prime f m - (m - 1)))).
  assert (HsegI : Id (pen_count_seg (m - 1) (pen_next_prime f m - (m - 1))) 1).
  { apply (pen_count_seg_one (pen_next_prime f m - (m - 1)) (m - 1) (pen_next_prime f m)).
    - apply (pr_prime_bool_true (pen_next_prime f m)). destruct Hp. reflexivity.
    - lia.
    - lia.
    - intros q Hq Hmq Hqle.
      assert (Hmq2 : m <= q) by lia.
      pose proof (NatLe_drop _ _
                    (Hmin q Hq (NatLe_lift _ _ Hmq2))). lia. }
  destruct (id_sym HsegI).
  reflexivity.
Qed.

(* ---- Section 3. The k-th prime enumerator (structural recursion on
   the slot k; slot 0 falls back to 1, the spec covers S k only) ---- *)

Fixpoint pen_nth_prime (f k : nat) : nat :=
  match k with
  | 0 => 1
  | S k' => pen_next_prime f (S (pen_nth_prime f k'))
  end.

(* Enumerator core spec: if the window [2, 2+f) holds an S k-th prime
   (counting reading), then pen_nth_prime f (S k) returns a prime whose
   reading is exactly S k (prime, and the S k-th one). *)
Theorem pen_nth_prime_spec : forall k f : nat,
  (exists q : nat, pr_prime_bool q = true /\ pen_count_upto q = S k /\ q < 2 + f) ->
  And (Id (pr_prime_bool (pen_nth_prime f (S k))) true)
      (Id (pen_count_upto (pen_nth_prime f (S k))) (S k)).
Proof.
  intros k. induction k as [|k IH]; intros f Hget.
  - (* The 1st prime: start 2, the window prime q self-certifies. *)
    assert (Hwin : exists q0 : nat, pr_prime_bool q0 = true /\ 2 <= q0 /\ q0 < 2 + f).
    { destruct Hget as [q [Hq [Hcq Hqlt]]].
      pose proof Hq as Hq'.
      apply andb_prop in Hq'.
      destruct Hq' as [Hl _].
      apply (proj1 (Nat.leb_le 2 q)) in Hl.
      exists q. split; [exact Hq | split; [exact Hl | exact Hqlt]]. }
    assert (Hstep : pen_nth_prime f 1 = pen_next_prime f 2) by reflexivity.
    rewrite Hstep.
    destruct (pen_next_prime_spec f 2 Hwin) as [Hp [Hp1 [Hp2s Hp4]]].
    split; [exact Hp|].
    assert (Hm2 : 1 <= 2) by lia.
    destruct (id_sym (pen_count_next_prime f 2 Hm2 Hwin)).
    assert (Hc1 : pen_count_upto (2 - 1) = 0) by reflexivity.
    rewrite Hc1. reflexivity.
  - (* The S (S k)-th prime: take the predecessor prime r (the S k-th
       prime), scan upward right after it. All witness reasoning on the
       premise stays under Prop-side assertions. *)
    assert (Hrwin : exists r0 : nat, pr_prime_bool r0 = true /\ pen_count_upto r0 = S k /\ r0 < 2 + f).
    { destruct Hget as [q [Hq [Hcq Hqlt]]].
      pose proof Hq as Hq'.
      apply andb_prop in Hq'.
      destruct Hq' as [Hl _].
      apply (proj1 (Nat.leb_le 2 q)) in Hl.
      assert (Hstepq : pen_count_upto q = pen_count_upto (q - 1) + 1).
      { assert (Hi : Id (pen_count_upto q) (pen_count_upto (q - 1) + 1)).
        { apply (pen_count_upto_step q); [lia | apply pr_prime_bool_true; exact Hq]. }
        destruct Hi. reflexivity. }
      assert (Hcq1 : pen_count_upto (q - 1) = S k) by lia.
      assert (HprevL : 1 <= pen_count_upto (q - 1)) by lia.
      destruct (pen_count_upto_largest (q - 1) HprevL) as [r Hrp].
      pose proof (fst Hrp) as Hr.
      pose proof (fst (snd Hrp)) as Hrle.
      pose proof (NatLe_drop _ _ Hrle).
      pose proof (snd (snd Hrp)) as HrcI.
      assert (Hrc : pen_count_upto r = pen_count_upto (q - 1)).
      { exact (match HrcI in (Id _ z) return (pen_count_upto r = z)
               with id_refl => eq_refl end). }
      exists r.
      split;
        [exact (match pr_prime_bool_false r Hr
                in (Id _ z) return (pr_prime_bool r = z)
                with id_refl => eq_refl end)
        | split; [lia | lia]]. }
    destruct (IH f Hrwin) as [Hp Hpc].
    (* The IH value and the predecessor prime r coincide by injectivity
       of the count. *)
    assert (Hwin : exists q0 : nat, pr_prime_bool q0 = true /\
                                   S (pen_nth_prime f (S k)) <= q0 /\
                                   q0 < S (pen_nth_prime f (S k)) + f).
    { destruct Hget as [q [Hq [Hcq Hqlt]]].
      pose proof Hq as Hq'.
      apply andb_prop in Hq'.
      destruct Hq' as [Hl _].
      apply (proj1 (Nat.leb_le 2 q)) in Hl.
      assert (Hstepq : pen_count_upto q = pen_count_upto (q - 1) + 1).
      { assert (Hi : Id (pen_count_upto q) (pen_count_upto (q - 1) + 1)).
        { apply (pen_count_upto_step q); [lia | apply pr_prime_bool_true; exact Hq]. }
        destruct Hi. reflexivity. }
      assert (Hcq1 : pen_count_upto (q - 1) = S k) by lia.
      assert (HprevL : 1 <= pen_count_upto (q - 1)) by lia.
      destruct (pen_count_upto_largest (q - 1) HprevL) as [r Hrp].
      pose proof (fst Hrp) as Hr.
      pose proof (NatLe_drop _ _ (fst Hr)).
      pose proof (fst (snd Hrp)) as Hrle.
      pose proof (NatLe_drop _ _ Hrle).
      pose proof (snd (snd Hrp)) as HrcI.
      assert (Hrc : pen_count_upto r = pen_count_upto (q - 1)).
      { exact (match HrcI in (Id _ z) return (pen_count_upto r = z)
               with id_refl => eq_refl end). }
      assert (Hpr : pen_nth_prime f (S k) = r).
      { assert (Hipp : pr_prime (pen_nth_prime f (S k))).
        { apply pr_prime_bool_true. destruct Hp. reflexivity. }
        assert (Hi : Id (pen_nth_prime f (S k)) r).
        { apply (pen_count_inj (pen_nth_prime f (S k)) r Hipp Hr).
          destruct (id_sym Hpc). rewrite Hrc. symmetry. exact Hcq1. }
        destruct Hi. reflexivity. }
      exists q. split; [exact Hq | split; [lia | lia]]. }
    assert (Hstep2 : pen_nth_prime f (S (S k)) =
                     pen_next_prime f (S (pen_nth_prime f (S k)))) by reflexivity.
    rewrite Hstep2.
    destruct (pen_next_prime_spec f (S (pen_nth_prime f (S k))) Hwin) as [Hpp2 [Hpm [Hplt Hmin]]].
    split; [exact Hpp2|].
    assert (Hm1 : 1 <= S (pen_nth_prime f (S k))) by lia.
    destruct (id_sym (pen_count_next_prime f (S (pen_nth_prime f (S k))) Hm1 Hwin)).
    assert (Hsub : pen_count_upto (S (pen_nth_prime f (S k)) - 1) =
                   pen_count_upto (pen_nth_prime f (S k))).
    { assert (Hz : S (pen_nth_prime f (S k)) - 1 = pen_nth_prime f (S k)) by lia.
      rewrite Hz. reflexivity. }
    rewrite Hsub.
    destruct (id_sym Hpc).
    assert (Hc : S k + 1 = S (S k)) by lia.
    destruct Hc. reflexivity.
Qed.

(* sigT witness form: the result is prime with reading S k (the S k-th
   prime), and is the computed enumerator value. *)
Theorem pen_nth_prime_exists : forall k f : nat,
  (exists q : nat, pr_prime_bool q = true /\ pen_count_upto q = S k /\ q < 2 + f) ->
  { p : nat & And (pr_prime p)
                   (And (Id (pen_count_upto p) (S k))
                        (Id (pen_nth_prime f (S k)) p)) }.
Proof.
  intros k f Hget.
  exists (pen_nth_prime f (S k)).
  destruct (pen_nth_prime_spec k f Hget) as [Hp Hc].
  split.
  - apply pr_prime_bool_true. destruct Hp. reflexivity.
  - split; [exact Hc | apply id_refl].
Defined.

(* ---- Section 4. The prime list, the primorial and the coprimality
   face (the enumeration-side shape of the Euclid structure) ---- *)

Fixpoint pen_primes_upto (n : nat) : list nat :=
  match n with
  | 0 => nil
  | S m => pen_primes_upto m ++ (if pr_prime_bool (S m) then S m :: nil else nil)
  end.

Lemma pen_primes_upto_S : forall n : nat,
  Id (pen_primes_upto (S n))
     (pen_primes_upto n ++ (if pr_prime_bool (S n) then S n :: nil else nil)).
Proof. reflexivity. Qed.

(* In characterisation: in the list iff prime and <= n. *)
Theorem pen_in_primes_upto : forall p n : nat,
  And (In p (pen_primes_upto n) -> And (pr_prime p) (NatLe p n))
      (And (pr_prime p) (NatLe p n) -> In p (pen_primes_upto n)).
Proof.
  intros p n. induction n as [|m IH].
  - split.
    + intros Hin.
      assert (Hf : False) by (destruct Hin).
      destruct Hf.
    + intros Hpair. exfalso.
      pose proof (NatLe_drop _ _ (fst (fst Hpair))).
      pose proof (NatLe_drop _ _ (snd Hpair)). lia.
  - destruct (id_sym (pen_primes_upto_S m)). split.
    + intros Hin. destruct (pr_prime_bool (S m)) eqn:Hb.
      * change (if true then S m :: nil else nil) with (S m :: nil) in Hin.
        destruct (Nat.eq_dec p (S m)) as [Hps | Hps].
        -- subst p. split.
           ++ apply pr_prime_bool_true. exact Hb.
           ++ apply NatLe_lift; lia.
        -- assert (Hin' : In p (pen_primes_upto m)).
           { apply in_app_or in Hin. destruct Hin as [Hin' | Hh].
             - exact Hin'.
             - simpl in Hh. destruct Hh as [Heq | Hf].
               + exfalso. apply Hps. symmetry. exact Heq.
               + destruct Hf. }
           destruct IH as [IHf IHb]. apply IHf in Hin'.
           pose proof (fst Hin') as Hp. pose proof (snd Hin') as Hle.
           split; [exact Hp | apply NatLe_lift; pose proof (NatLe_drop _ _ Hle); lia].
      * change (if false then S m :: nil else nil) with (@nil nat) in Hin.
        rewrite app_nil_r in Hin.
        destruct IH as [IHf IHb]. apply IHf in Hin.
        pose proof (fst Hin) as Hp. pose proof (snd Hin) as Hle.
        split; [exact Hp | apply NatLe_lift; pose proof (NatLe_drop _ _ Hle); lia].
    + intros Hpair. destruct (le_lt_dec p m) as [Hpm|Hpgt].
      * apply in_or_app. left. destruct IH as [IHf IHb]. apply IHb.
        split; [exact (fst Hpair)
               | apply NatLe_lift; pose proof (NatLe_drop _ _ (snd Hpair)); lia].
      * assert (Hpe : p = S m) by (pose proof (NatLe_drop _ _ (snd Hpair)); lia).
        assert (Hb : pr_prime_bool (S m) = true).
        { assert (HpS : pr_prime (S m)) by (rewrite <- Hpe; exact (fst Hpair)).
          exact (match pr_prime_bool_false (S m) HpS
                 in (Id _ z) return (pr_prime_bool (S m) = z)
                 with id_refl => eq_refl end). }
        rewrite Hb. change (if true then S m :: nil else nil) with (S m :: nil).
        apply in_or_app. right. simpl. left. lia.
Qed.

(* All list entries >= 1 gives a folded product >= 1. *)
Lemma pen_fold_mul_pos : forall l : list nat,
  (forall x : nat, In x l -> 1 <= x) -> NatLe 1 (fold_right Nat.mul 1 l).
Proof.
  intros l. induction l as [|a l IH]; intros Hall.
  - apply NatLe_lift. simpl. lia.
  - apply NatLe_lift. simpl.
    assert (H1 : 1 <= a) by (apply Hall; left; reflexivity).
    assert (H2 : 1 <= fold_right Nat.mul 1 l).
    { assert (Hpre : forall x : nat, In x l -> 1 <= x)
        by (intros x Hx; apply Hall; right; exact Hx).
      exact (NatLe_drop _ _ (IH Hpre)). }
    assert (Hstep : a * 1 <= a * fold_right Nat.mul 1 l)
      by (apply (Nat.mul_le_mono_l 1 (fold_right Nat.mul 1 l) a); exact H2).
    rewrite Nat.mul_1_r in Hstep. lia.
Qed.

(* The primorial: the product of the primes up to n (at n = the k-th
   prime this is the product of the first k primes). *)
Definition pen_primorial (n : nat) : nat :=
  fold_right Nat.mul 1 (pen_primes_upto n).

Lemma pen_primorial_pos : forall n : nat, NatLe 1 (pen_primorial n).
Proof.
  intros n. apply pen_fold_mul_pos. intros x Hx.
  pose proof (fst (fst (pen_in_primes_upto x n) Hx)) as Hp.
  pose proof (NatLe_drop _ _ (fst Hp)). lia.
Qed.

(* A list member divides the folded product. *)
Lemma pen_fold_in_divide : forall (x : nat) (l : list nat),
  In x l -> Nat.divide x (fold_right Nat.mul 1 l).
Proof.
  intros x l. induction l as [|a l IH]; intros Hin.
  - destruct Hin.
  - simpl. destruct Hin as [Heq|Hin].
    + subst a. exists (fold_right Nat.mul 1 l). apply Nat.mul_comm.
    + destruct (IH Hin) as [c Hc].
      exists (a * c). rewrite Hc.
      rewrite <- (Nat.mul_assoc a c x). reflexivity.
Qed.

(* A prime p <= n divides the primorial of n. *)
Lemma pen_primorial_divide : forall p n : nat, pr_prime p -> p <= n ->
  Nat.divide p (pen_primorial n).
Proof.
  intros p n Hp Hle. unfold pen_primorial.
  apply (pen_fold_in_divide p).
  apply (snd (pen_in_primes_upto p n)). split; [exact Hp | apply NatLe_lift; exact Hle].
Qed.

(* The constructive coprimality of a primorial and its successor: any d
   dividing both the primorial of n and its successor is one. *)
Theorem pen_primorial_coprime_succ : forall n : nat,
  forall d : nat, Nat.divide d (pen_primorial n) ->
                  Nat.divide d (S (pen_primorial n)) -> Id d 1.
Proof.
  intros n d Hd1 Hd2.
  assert (Hs : S (pen_primorial n) - pen_primorial n = 1) by lia.
  assert (Hd3 : Nat.divide d 1).
  { rewrite <- Hs.
    apply (Nat.divide_sub_r d (S (pen_primorial n)) (pen_primorial n));
      [exact Hd2 | exact Hd1]. }
  apply Nat.divide_1_r in Hd3. rewrite Hd3. reflexivity.
Qed.

(* The enumeration-side constructive Euclid form: the least prime factor
   of primorial n + 1 is above n -- for each n one explicit new prime
   outside the table (parallel to the n!+1 line). *)
Theorem pen_euclid_new_prime : forall n : nat,
  { p : nat & And (pr_prime p)
                   (And (Nat.divide p (S (pen_primorial n))) (NatLe (S n) p)) }.
Proof.
  intros n.
  assert (HP2 : 2 <= S (pen_primorial n)).
  { assert (H1 : 1 <= pen_primorial n) by exact (NatLe_drop _ _ (pen_primorial_pos n)). lia. }
  destruct (pr_min_factor_exists (S (pen_primorial n)) HP2) as [p Hpf].
  pose proof (fst Hpf) as Hpn.
  pose proof (snd Hpf) as Hpp.
  exists p. split; [exact Hpp |]. split; [exact Hpn |].
  destruct (le_lt_dec p n) as [Hpn2|Hpgt]; [|apply NatLe_lift; exact Hpgt].
  exfalso.
  pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  assert (Hdv : Nat.divide p (pen_primorial n))
    by (apply (pen_primorial_divide p n Hpp Hpn2)).
  assert (Hs : S (pen_primorial n) - pen_primorial n = 1) by lia.
  assert (Hd1 : Nat.divide p 1).
  { rewrite <- Hs.
    apply (Nat.divide_sub_r p (S (pen_primorial n)) (pen_primorial n));
      [exact Hpn | exact Hdv]. }
  assert (Hp1 : p = 1) by (apply Nat.divide_1_r; exact Hd1).
  lia.
Defined.

(* Primes are unbounded (constructive): for each n a prime above n. *)
Theorem pen_prime_unbounded : forall n : nat,
  { p : nat & And (pr_prime p) (NatLe (S n) p) }.
Proof.
  intros n. destruct (pen_euclid_new_prime n) as [p Hpair].
  pose proof (fst Hpair) as Hpp.
  pose proof (snd Hpair) as Hpair2.
  exists p. split; [exact Hpp | exact (snd Hpair2)].
Defined.

(* Coprimality of distinct primes: the greatest common divisor of two
   distinct primes is one. *)
Theorem pen_coprime_of_neq : forall p q : nat,
  pr_prime p -> pr_prime q -> (p = q -> False) -> Id (Nat.gcd p q) 1.
Proof.
  intros p q Hp Hq Hpq.
  pose proof (NatLe_drop _ _ (fst Hp)) as Hp2.
  pose proof (NatLe_drop _ _ (fst Hq)) as Hq2.
  pose proof (snd Hp) as Hpd.
  pose proof (snd Hq) as Hqd.
  assert (Hgp : Nat.divide (Nat.gcd p q) p) by apply Nat.gcd_divide_l.
  assert (Hgq : Nat.divide (Nat.gcd p q) q) by apply Nat.gcd_divide_r.
  destruct (le_lt_dec 2 (Nat.gcd p q)) as [Hg2|Hg1].
  - (* A common factor reaching 2: it must equal p, hence divide q,
       hence p = q, contradicting distinctness. *)
    exfalso.
    assert (Hgle : Nat.gcd p q <= p).
    { destruct Hgp as [c Hc]. destruct c as [|c'].
      - rewrite Nat.mul_0_l in Hc. exfalso. lia.
      - assert (Hstep : 1 * Nat.gcd p q <= S c' * Nat.gcd p q)
          by (apply (Nat.mul_le_mono_r 1 (S c') (Nat.gcd p q)); lia).
        rewrite Nat.mul_1_l in Hstep. lia. }
    assert (Hgeqp : Nat.gcd p q = p).
    { destruct (Nat.eq_dec (Nat.gcd p q) p) as [H|H]; [exact H|].
      exfalso.
      destruct (le_lt_dec (Nat.gcd p q) p) as [Hle|Hlt].
      - assert (Hglt : Nat.gcd p q < p) by lia.
        assert (Hgf : Id (Nat.eqb (p mod (Nat.gcd p q)) 0) false).
        { apply (Hpd (Nat.gcd p q)); [apply NatLe_lift; lia | apply NatLe_lift; lia]. }
        assert (Hg1 : 1 <= Nat.gcd p q) by lia.
        pose proof (pr_dvd_mod0 (Nat.gcd p q) p Hg1 Hgp) as Hmod0.
        assert (Hgfe : Nat.eqb (p mod (Nat.gcd p q)) 0 = false)
          by (exact (match Hgf in (Id _ z)
                     return (Nat.eqb (p mod (Nat.gcd p q)) 0 = z)
                     with id_refl => eq_refl end)).
        assert (Hmode : p mod (Nat.gcd p q) = 0)
          by (exact (match Hmod0 in (Id _ z) return (p mod (Nat.gcd p q) = z)
                     with id_refl => eq_refl end)).
        rewrite Hmode in Hgfe. simpl in Hgfe. discriminate.
      - lia. }
    rewrite Hgeqp in Hgq.
    assert (Hple : p <= q).
    { destruct Hgq as [c Hc]. destruct c as [|c'].
      - rewrite Nat.mul_0_l in Hc. exfalso. lia.
      - assert (Hstep : 1 * p <= S c' * p)
          by (apply (Nat.mul_le_mono_r 1 (S c') p); lia).
        rewrite Nat.mul_1_l in Hstep. lia. }
    destruct (Nat.eq_dec p q) as [H|H].
    + apply Hpq. exact H.
    + assert (Hqf : Id (Nat.eqb (q mod p) 0) false).
      { apply (Hqd p (fst Hp)); [apply NatLe_lift; lia]. }
      assert (Hqfe : Nat.eqb (q mod p) 0 = false)
        by (exact (match Hqf in (Id _ z) return (Nat.eqb (q mod p) 0 = z)
                   with id_refl => eq_refl end)).
      assert (Hp1 : 1 <= p) by lia.
      pose proof (pr_dvd_mod0 p q Hp1 Hgq) as Hmod0.
      assert (Hqe : q mod p = 0)
        by (exact (match Hmod0 in (Id _ z) return (q mod p = z)
                   with id_refl => eq_refl end)).
      rewrite Hqe in Hqfe. simpl in Hqfe. discriminate.
  - (* A common factor below 2 that is not zero (zero divides p only if
       p is zero, contradicting primality): hence it is one. *)
    assert (Hg0 : Nat.gcd p q = 0 -> False).
    { intros H0. rewrite H0 in Hgp.
      apply (Nat.divide_0_l p) in Hgp.
      lia. }
    assert (Hgpos : 1 <= Nat.gcd p q).
    { destruct (le_lt_dec 1 (Nat.gcd p q)) as [Hge|Hlt1].
      - exact Hge.
      - exfalso. apply Hg0. lia. }
    assert (Hgf : Nat.gcd p q = 1) by lia.
    rewrite Hgf. reflexivity.
Qed.

(* ---- Section 5. Numeric smoke tests (small instances <= 10,
   vm_compute direct evaluation, no postulates) ---- *)

Lemma pen_nth_1 : Id (pen_nth_prime 8 1) 2.
Proof. vm_compute. reflexivity. Qed.

Lemma pen_nth_2 : Id (pen_nth_prime 8 2) 3.
Proof. vm_compute. reflexivity. Qed.

Lemma pen_nth_3 : Id (pen_nth_prime 8 3) 5.
Proof. vm_compute. reflexivity. Qed.

Lemma pen_nth_4 : Id (pen_nth_prime 8 4) 7.
Proof. vm_compute. reflexivity. Qed.

Lemma pen_count_10 : Id (pen_count_upto 10) 4.
Proof. vm_compute. reflexivity. Qed.

Lemma pen_list_10 : Id (pen_primes_upto 10) (2 :: 3 :: 5 :: 7 :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma pen_primorial_5 : Id (pen_primorial 5) 30.
Proof. vm_compute. reflexivity. Qed.

Lemma pen_primorial_10 : Id (pen_primorial 10) 210.
Proof. vm_compute. reflexivity. Qed.

(* ---- Section 6. Assumption audit (Print Assumptions evidence block) ---- *)

Print Assumptions pen_count_split.
Print Assumptions pen_count_seg_none.
Print Assumptions pen_count_seg_one.
Print Assumptions pen_count_upto_step.
Print Assumptions pen_count_mono.
Print Assumptions pen_count_upto_largest.
Print Assumptions pen_count_lt_prime.
Print Assumptions pen_count_inj.
Print Assumptions pen_next_prime_spec.
Print Assumptions pen_count_next_prime.
Print Assumptions pen_nth_prime_spec.
Print Assumptions pen_nth_prime_exists.
Print Assumptions pen_in_primes_upto.
Print Assumptions pen_fold_mul_pos.
Print Assumptions pen_primorial_pos.
Print Assumptions pen_fold_in_divide.
Print Assumptions pen_primorial_divide.
Print Assumptions pen_primorial_coprime_succ.
Print Assumptions pen_euclid_new_prime.
Print Assumptions pen_prime_unbounded.
Print Assumptions pen_coprime_of_neq.
