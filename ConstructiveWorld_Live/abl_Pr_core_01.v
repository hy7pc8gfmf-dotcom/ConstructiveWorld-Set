(* ConstructiveWorld-Set -- prime-field domain formation series, piece 1 *)
(** * abl_Pr_core_01: trial-division primality, least prime factor, and
    prime factorization existence, all on nat.

    Mission.  (1) The primality statement pr_prime (2 <= n, no divisor
    in [2,n), Set-carried per Sec.0 below) and its boolean decider
    pr_prime_bool with a two-way spec.  (2) The least prime factor
    pr_min_factor, a fuel-decreasing Fixpoint (fuel k counts down; the
    tested divisor d = n-k sweeps upward from 2), with soundness, the
    least-divisor-is-prime lemma, and the sigT-witnessed existence form
    pr_min_factor_exists.  (3) Factorization existence pr_factor_exists:
    every n >= 2 has a list of prime factors whose fold_right product
    equals n (well-founded strong induction).

    Dependencies.  Stdlib (Arith.Arith, List, Bool, Lia); S01_BaseRing
    (Id, id_refl, NatLe, NatLe_lift, NatLe_drop, And).

    References.  Design basis: item 1 of the prime-field
    domain-formation series (the domain foundation).

    Constructivity.  All statements are Set-carried: pr_prime itself,
    and both existence theorems as sigT-witnessed records.  Negation is
    held as P -> False only in reasoning premises.  Axioms: none.  The
    computational pieces pr_trial, pr_min_factor and pr_prime_bool are
    first-order bool/nat Fixpoints, hence extractable; numeric smoke
    tests run on small instances (at most n = 49).

    Build.  rocq c -native-compiler no -q -Q <world> "" abl_Pr_core_01.v
    (Rocq 9.1.0; stack ulimit -s 65532; thermal-guard wrapped; the
    dependency .vo reused read-only from the source seat's world). *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import S01_BaseRing (Id, id_refl, NatLe, NatLe_lift, NatLe_drop, And).

(* ---- Sec.0  The primality statement (Set-carried: the NatLe
   least-factor bound conjoined with the per-divisor non-divisibility
   face, the latter held as the boolean mod decider
   Id (Nat.eqb (n mod d) 0) false) ---- *)

Definition pr_prime (n : nat) : Set :=
  And (NatLe 2 n)
      (forall d : nat, NatLe 2 d -> NatLe (S d) n ->
        Id (Nat.eqb (n mod d) 0) false).

(* ---- Sec.1  The bridge between mod and divide (divisor >= 1, both
   directions) ---- *)

Lemma pr_dvd_mod0 : forall d n : nat,
  1 <= d -> Nat.divide d n -> Id (n mod d) 0.
Proof.
  intros d n Hd Hdvd.
  assert (Hcore : n mod d = 0).
  { destruct Hdvd as [z Hz].
    destruct (Nat.Div0.mod_divides n d) as [_ Hbwd].
    apply Hbwd. exists z. rewrite Hz. apply Nat.mul_comm. }
  destruct Hcore. apply id_refl.
Qed.

Lemma pr_mod0_dvd : forall d n : nat,
  1 <= d -> n mod d = 0 -> Nat.divide d n.
Proof.
  intros d n Hd Hm.
  destruct (Nat.Div0.mod_divides n d) as [Hfwd _].
  apply Hfwd in Hm. destruct Hm as [c Hc].
  exists c. rewrite Hc. apply Nat.mul_comm.
Qed.

(* ---- Sec.2  The fuel-decreasing boolean trial machine (fuel k counts
   down; the divisor d = n-k sweeps the interval [n-k, n)) ---- *)

Fixpoint pr_trial (k n : nat) : bool :=
  match k with
  | 0 => true
  | S k' => if Nat.eqb (n mod (n - S k')) 0 then false else pr_trial k' n
  end.

(* true direction: pr_trial k n = true implies that no divisor of n
   lies in [n-k, n) *)
Lemma pr_trial_true : forall n k : nat, 1 <= n ->
  pr_trial k n = true ->
  forall d : nat, n - k <= d -> d < n -> Nat.divide d n -> False.
Proof.
  intros n k. induction k as [|k IH]; intros Hn Htrue d Hd Hlt Hdvd.
  - lia.
  - simpl in Htrue. destruct (Nat.eqb (n mod (n - S k)) 0) eqn:Em.
    + discriminate.
    + destruct (Nat.eq_dec d (n - S k)) as [Hde|Hdne].
      * subst d. destruct (le_lt_dec 1 (n - S k)) as [H1|H1].
        -- exfalso. apply (proj1 (Nat.eqb_neq (n mod (n - S k)) 0)) in Em.
           apply (pr_dvd_mod0 (n - S k) n H1) in Hdvd.
           apply Em. destruct Hdvd. reflexivity.
        -- exfalso. assert (Hz : n - S k = 0) by lia.
           rewrite Hz in Hdvd. apply Nat.divide_0_l in Hdvd. lia.
      * apply (IH Hn Htrue d); try lia. exact Hdvd.
Qed.

(* false direction: no divisor of n in [n-k, n) implies
   pr_trial k n = true *)
Lemma pr_trial_false : forall n k : nat, 1 <= n ->
  (forall d : nat, n - k <= d -> d < n -> Nat.divide d n -> False) ->
  Id (pr_trial k n) true.
Proof.
  intros n k. induction k as [|k IH]; intros Hn Hall.
  - apply id_refl.
  - simpl. destruct (Nat.eqb (n mod (n - S k)) 0) eqn:Em.
    + exfalso. apply Nat.eqb_eq in Em.
      destruct (le_lt_dec 1 (n - S k)) as [H1|H1].
      * apply (Hall (n - S k)); try lia.
        apply (pr_mod0_dvd (n - S k) n H1 Em).
      * assert (Hz : n - S k = 0) by lia.
        rewrite Hz in Em. rewrite Nat.mod_0_r in Em. lia.
    + apply IH; [lia|].
      intros d Hd Hlt Hdvd.
      destruct (Nat.eq_dec d (n - S k)) as [Hde|Hdne].
      * subst d. exfalso.
        destruct (le_lt_dec 1 (n - S k)) as [H1|H0].
        -- apply (proj1 (Nat.eqb_neq (n mod (n - S k)) 0)) in Em.
           apply (pr_dvd_mod0 (n - S k) n H1) in Hdvd.
           apply Em. destruct Hdvd. reflexivity.
        -- assert (Hz : n - S k = 0) by lia.
           rewrite Hz in Hdvd. apply Nat.divide_0_l in Hdvd. lia.
      * apply (Hall d); [lia | lia | exact Hdvd].
Qed.

(* The trial machine spec (two-way iff) *)
Theorem pr_trial_spec : forall n k : nat, 1 <= n ->
  pr_trial k n = true <->
  (forall d : nat, n - k <= d -> d < n -> Nat.divide d n -> False).
Proof.
  intros n k Hn. split.
  - apply pr_trial_true; assumption.
  - intro Hall. assert (Hid : Id (pr_trial k n) true).
    { apply (pr_trial_false n k); assumption. }
    destruct Hid. reflexivity.
Qed.

(* ---- Sec.3  The decider pr_prime_bool (boolean exit + two-way spec) ---- *)

Definition pr_prime_bool (n : nat) : bool :=
  andb (Nat.leb 2 n) (pr_trial (n - 2) n).

Theorem pr_prime_bool_true : forall n : nat,
  pr_prime_bool n = true -> pr_prime n.
Proof.
  intros n H. unfold pr_prime. unfold pr_prime_bool in H.
  apply andb_prop in H. destruct H as [Hleb Htr].
  apply (proj1 (Nat.leb_le 2 n)) in Hleb. split.
  - apply NatLe_lift. exact Hleb.
  - intros d Hd2 Hdlt.
    pose proof (NatLe_drop _ _ Hd2).
    pose proof (NatLe_drop _ _ Hdlt).
    assert (H1 : 1 <= n) by lia.
    assert (Hd1 : 1 <= d) by lia.
    destruct (Nat.eqb (n mod d) 0) eqn:Em.
    + exfalso. apply Nat.eqb_eq in Em.
      apply (pr_trial_true n (n - 2) H1 Htr d); try lia.
      exact (pr_mod0_dvd d n Hd1 Em).
    + apply id_refl.
Qed.

Theorem pr_prime_bool_false : forall n : nat,
  pr_prime n -> Id (pr_prime_bool n) true.
Proof.
  intros n Hpp. destruct Hpp as [H2 Hall].
  assert (H2' : 2 <= n) by (apply (NatLe_drop _ _ H2)).
  assert (H1 : 1 <= n) by lia.
  assert (Hl : Nat.leb 2 n = true) by (apply (proj2 (Nat.leb_le 2 n)); exact H2').
  unfold pr_prime_bool. rewrite Hl.
  change (Id (pr_trial (n - 2) n) true).
  apply (pr_trial_false n (n - 2)); [exact H1|].
    intros d Hd Hlt Hdvd.
    assert (Hd2 : 2 <= d) by lia.
    assert (Hdlt2 : S d <= n) by lia.
    assert (Hd1 : 1 <= d) by lia.
    pose proof (Hall d (NatLe_lift _ _ Hd2) (NatLe_lift _ _ Hdlt2)) as Hne.
    pose proof (pr_dvd_mod0 d n Hd1 Hdvd) as Hm0.
    assert (Heq0 : n mod d = 0).
    { exact (match Hm0 in (Id _ z0) return (n mod d = z0)
             with id_refl => eq_refl end). }
    assert (Hne' : Nat.eqb (n mod d) 0 = false).
    { exact (match Hne in (Id _ z0) return (Nat.eqb (n mod d) 0 = z0)
             with id_refl => eq_refl end). }
    rewrite Heq0 in Hne'. simpl in Hne'. discriminate.
Qed.

Theorem pr_prime_bool_spec : forall n : nat,
  And (pr_prime_bool n = true -> pr_prime n)
      (pr_prime n -> Id (pr_prime_bool n) true).
Proof.
  intros n. split.
  - apply pr_prime_bool_true.
  - apply pr_prime_bool_false.
Qed.

(* ---- Sec.4  The least prime factor (fuel-decreasing Fixpoint +
   soundness + sigT-witnessed existence form).  pr_min_factor k n: the
   remaining fuel k counts down and the tested divisor d = n-k sweeps
   upward from 2; if no divisor is found the value falls back to n
   (for n >= 2, n itself is a divisor, so the fallback is
   legitimate). ---- *)

Fixpoint pr_min_factor (k n : nat) : nat :=
  match k with
  | 0 => n
  | S k' => if Nat.eqb (n mod (n - S k')) 0 then n - S k' else pr_min_factor k' n
  end.

Lemma pr_min_factor_sound : forall n k : nat, 2 <= n -> k <= n - 2 ->
  (forall e : nat, 2 <= e -> e < n - k -> Nat.divide e n -> False) ->
  And (Nat.divide (pr_min_factor k n) n)
    (And (NatLe 2 (pr_min_factor k n))
      (And (NatLe (pr_min_factor k n) n)
        (forall e : nat, NatLe 2 e -> NatLe (S e) (pr_min_factor k n) ->
           Nat.divide e n -> False))).
Proof.
  intros n k. induction k as [|k IH]; intros Hn Hk Hall.
  - simpl. repeat split.
    + apply Nat.divide_refl.
    + apply NatLe_lift. lia.
    + apply NatLe_lift. lia.
    + intros e He Hlt Hdvd. apply NatLe_drop in He. apply NatLe_drop in Hlt.
      apply (Hall e); try lia. exact Hdvd.
  - simpl.
    assert (Hk2 : k <= n - 2) by lia.
    assert (Hd2 : 2 <= n - S k) by lia.
    destruct (Nat.eqb (n mod (n - S k)) 0) eqn:Em.
    + apply Nat.eqb_eq in Em.
      repeat split.
      * apply (pr_mod0_dvd (n - S k) n); [lia | exact Em].
      * apply NatLe_lift. lia.
      * apply NatLe_lift. lia.
      * intros e He Hlt Hdvd. apply NatLe_drop in He. apply NatLe_drop in Hlt.
        apply (Hall e); try lia. exact Hdvd.
    + apply IH; try lia.
      intros e He Hlt Hdvd.
      assert (Hsplit : e <= n - S k) by lia.
      destruct (Nat.eq_dec e (n - S k)) as [Hde|Hdne].
      * subst e.
        assert (Hm : Id (n mod (n - S k)) 0).
        { apply (pr_dvd_mod0 (n - S k) n); [lia | exact Hdvd]. }
        apply (proj1 (Nat.eqb_neq (n mod (n - S k)) 0)) in Em.
        apply Em. destruct Hm. reflexivity.
      * apply (Hall e); [lia | lia | exact Hdvd].
Qed.

(* Correctness lemma: the least d > 1 found is prime (trial-division
   pr_prime) *)
Theorem pr_min_factor_prime : forall n : nat,
  2 <= n -> pr_prime (pr_min_factor (n - 2) n).
Proof.
  intros n Hn. unfold pr_prime.
  assert (Hkvac : n - 2 <= n - 2) by apply Nat.le_refl.
  assert (Hvac : forall e : nat, 2 <= e -> e < n - (n - 2) -> Nat.divide e n -> False).
  { intros e He Hlt _. lia. }
  destruct (pr_min_factor_sound n (n - 2) Hn Hkvac Hvac) as [Hpn [Hp2 [Hpn' Hmin]]].
  split; [exact Hp2|].
  intros d Hd2 Hdlt.
  assert (Hd1 : 1 <= d) by (pose proof (NatLe_drop _ _ Hd2); lia).
  destruct (Nat.eqb (pr_min_factor (n - 2) n mod d) 0) eqn:Em.
  + exfalso. apply Nat.eqb_eq in Em.
    pose proof (pr_mod0_dvd d (pr_min_factor (n - 2) n) Hd1 Em) as Hdm.
    apply (Hmin d Hd2 Hdlt).
    exact (Nat.divide_trans d (pr_min_factor (n - 2) n) n Hdm Hpn).
  + apply id_refl.
Qed.

(* sigT-witnessed existence: n >= 2 yields a witness p that divides n
   and is prime *)
Theorem pr_min_factor_exists : forall n : nat, 2 <= n ->
  { p : nat & And (Nat.divide p n) (pr_prime p) }.
Proof.
  intros n Hn. exists (pr_min_factor (n - 2) n). split.
  - assert (Hvac : forall e : nat, 2 <= e -> e < n - (n - 2) -> Nat.divide e n -> False).
    { intros e He Hlt _. lia. }
    destruct (pr_min_factor_sound n (n - 2) Hn (Nat.le_refl (n - 2)) Hvac) as [Hpn _].
    exact Hpn.
  - apply (pr_min_factor_prime n Hn).
Defined.

(* ---- Sec.5  The factorization existence form (sigT witness: a list of
   prime factors whose fold_right product equals n) ---- *)

Theorem pr_factor_exists : forall n : nat, 2 <= n ->
  { l : list nat & And (forall p : nat, In p l -> pr_prime p)
                       (Id (fold_right Nat.mul 1 l) n) }.
Proof.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun m : nat => 2 <= m ->
      { l : list nat & And (forall p : nat, In p l -> pr_prime p)
                           (Id (fold_right Nat.mul 1 l) m) })).
  intros n IH Hn.
  destruct (pr_min_factor_exists n Hn) as [p Hpf].
  pose proof (fst Hpf) as Hpn.
  pose proof (snd Hpf) as Hpp.
  pose proof (fst Hpp) as Hp2.
  pose proof (NatLe_drop _ _ Hp2) as Hp2'.
  assert (Hpn0 : p = 0 -> False) by lia.
  assert (Hmod0 : n mod p = 0).
  { destruct Hpn as [z Hz].
    destruct (Nat.Div0.mod_divides n p) as [_ Hbwd].
    apply Hbwd. exists z. rewrite Hz. apply Nat.mul_comm. }
  assert (Hdm : n = p * (n / p)).
  { assert (Hdm0 : n = p * (n / p) + n mod p) by (apply Nat.div_mod; exact Hpn0).
    rewrite Hmod0 in Hdm0. rewrite Nat.add_0_r in Hdm0. exact Hdm0. }
  destruct (Nat.eq_dec p n) as [Hpe|Hpne].
  - (* n itself is prime: the list is [n] *)
    exists (p :: nil). split.
    + intros q Hin.
      destruct (Nat.eq_dec q p) as [Hqp | Hqp].
      * subst q. exact Hpp.
      * exfalso.
        assert (Heq : p = q)
          by (simpl in Hin; destruct Hin as [Heq'|Hf];
              [exact Heq' | destruct Hf]).
        apply Hqp. symmetry. exact Heq.
    + simpl. rewrite Nat.mul_1_r.
      destruct Hpe. apply id_refl.
  - (* p < n: recurse on the computable quotient n / p; the list is
     p :: lq *)
    assert (Hz1 : 1 <= n / p).
    { destruct (n / p) as [|z'] eqn:E.
      - rewrite Nat.mul_0_r in Hdm. lia.
      - lia. }
    assert (Hz2 : 2 <= n / p).
    { destruct (n / p) as [|z'] eqn:E.
      - rewrite Nat.mul_0_r in Hdm. lia.
      - destruct z' as [|z''].
        + exfalso. rewrite Nat.mul_1_r in Hdm.
          apply Hpne. symmetry. exact Hdm.
        + lia. }
    assert (Hq0 : 0 < n / p) by lia.
    assert (Hzltn : n / p < n).
    { assert (Hstep : (n / p) * 1 < (n / p) * p).
      { apply (proj1 (Nat.mul_lt_mono_pos_l (n / p) 1 p Hq0)). lia. }
      rewrite Nat.mul_1_r in Hstep.
      rewrite (Nat.mul_comm (n / p) p) in Hstep.
      rewrite <- Hdm in Hstep. exact Hstep. }
    assert (Hp0 : 0 < p) by lia.
    assert (Hpltn : p < n).
    { assert (Hstep2 : p * 1 < p * (n / p)).
      { apply (proj1 (Nat.mul_lt_mono_pos_l p 1 (n / p) Hp0)). lia. }
      rewrite Nat.mul_1_r in Hstep2. rewrite <- Hdm in Hstep2. exact Hstep2. }
    destruct (IH (n / p) Hzltn Hz2) as [lq [Hallq Hfoldq]].
    exists (p :: lq). split.
    + intros q Hin.
      destruct (Nat.eq_dec q p) as [Hqp | Hqp].
      * subst q. exact Hpp.
      * assert (Htail : In q lq).
        { simpl in Hin. destruct Hin as [Heq' | Ht].
          - exfalso. apply Hqp. symmetry. exact Heq'.
          - exact Ht. }
        apply Hallq. exact Htail.
    + assert (Hfoldq' : fold_right Nat.mul 1 lq = n / p).
      { exact (match Hfoldq in (Id _ z) return (fold_right Nat.mul 1 lq = z)
               with id_refl => eq_refl end). }
      simpl. rewrite Hfoldq'. rewrite <- Hdm. apply id_refl.
Defined.

(* ---- Sec.6  Numeric smoke tests (small instances, at most n = 49, by
   vm_compute with no postulates) ---- *)

Lemma pr_prime_bool_2 : Id (pr_prime_bool 2) true.
Proof. vm_compute. apply id_refl. Qed.

Lemma pr_prime_bool_3 : Id (pr_prime_bool 3) true.
Proof. vm_compute. apply id_refl. Qed.

Lemma pr_prime_bool_4 : Id (pr_prime_bool 4) false.
Proof. vm_compute. apply id_refl. Qed.

Lemma pr_prime_bool_5 : Id (pr_prime_bool 5) true.
Proof. vm_compute. apply id_refl. Qed.

Lemma pr_prime_bool_9 : Id (pr_prime_bool 9) false.
Proof. vm_compute. apply id_refl. Qed.

Lemma pr_prime_bool_11 : Id (pr_prime_bool 11) true.
Proof. vm_compute. apply id_refl. Qed.

Lemma pr_prime_bool_12 : Id (pr_prime_bool 12) false.
Proof. vm_compute. apply id_refl. Qed.

Lemma pr_min_factor_35 : Id (pr_min_factor 33 35) 5.
Proof. vm_compute. apply id_refl. Qed.

Lemma pr_min_factor_49 : Id (pr_min_factor 47 49) 7.
Proof. vm_compute. apply id_refl. Qed.

Lemma pr_trial_12 : Id (pr_trial 10 12) false.
Proof. vm_compute. apply id_refl. Qed.

(* ---- Sec.7  Assumption audit via Print Assumptions ---- *)

Print Assumptions pr_dvd_mod0.
Print Assumptions pr_mod0_dvd.
Print Assumptions pr_trial_spec.
Print Assumptions pr_prime_bool_spec.
Print Assumptions pr_min_factor_sound.
Print Assumptions pr_min_factor_prime.
Print Assumptions pr_min_factor_exists.
Print Assumptions pr_factor_exists.
