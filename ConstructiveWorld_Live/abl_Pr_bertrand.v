(* ConstructiveWorld-Set -- constructive witness forms for Bertrand's postulate in the prime-domain family. *)

(** * abl_Pr_bertrand: constructive witness forms for Bertrand's postulate.

    Mission.  Three constructive witness families for Bertrand's postulate
      (n < p <= 2n): an ascending scan machine ([pbr_scan], [pbr_search])
      with unconditional spec lemmas [pbr_scan_some] and [pbr_scan_hit] and
      the conditional main statement [pbr_bertrand_cond]; a segment-table
      engine over [2,512] ([pbr_runs], [pbr_runs_ok], [pbr_runs_good]) giving
      the table-domain main statements [pbr_bertrand_table] and
      [pbr_search_cert]; and monotone lifting with extension to [2,520]
      ([pbr_lift], [pbr_bertrand_ext]) plus unbounded good points
      ([pbr_bertrand_infinite]).

    Dependencies.  Stdlib [Arith.Arith], [List], [Bool], [Lia].
      Requires [abl_Pr_core_01], [abl_Pr_enum_02], [S01_BaseRing] of this development.

    References.  This development, abl_Pr_bertrand.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  The witness statements and their fields are carried
      by [Set] (decidable boolean carriers, [NatLe]/[And]/[Id] Set-face
      equations and [sigT] witness carriers); auxiliary definitional and
      smoke lemmas keep the Prop equation face; statements extract with
      [Obj.magic] = 0 and no name erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_Pr_bertrand.v] compiles
      cleanly (exit 0); the artifact starts with [436f7121 000160bc]. *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import abl_Pr_core_01.
Require Import abl_Pr_enum_02.
Require Import S01_BaseRing (Id, id_refl, And, NatLe, NatLe_lift, NatLe_drop).

(* ---- Section 0. Table-domain constants and segment-table data ----
   A segment (n0, p, len) records that for every i < len the Bertrand
   witness of n = n0 + i is the same prime p.
   The table covers the 511 points of [2,512] in 97 segments; consecutive
   segment starts differ by the segment length, and the first segment
   starts at 2. *)

Definition pbr_N : nat := 512.

Definition pbr_runs : list (nat * nat * nat) :=
  (2,3,1) :: (3,5,2) :: (5,7,2) :: (7,11,4) :: (11,13,2) :: (13,17,4) ::
  (17,19,2) :: (19,23,4) :: (23,29,6) :: (29,31,2) :: (31,37,6) :: (37,41,4) ::
  (41,43,2) :: (43,47,4) :: (47,53,6) :: (53,59,6) :: (59,61,2) :: (61,67,6) ::
  (67,71,4) :: (71,73,2) :: (73,79,6) :: (79,83,4) :: (83,89,6) :: (89,97,8) ::
  (97,101,4) :: (101,103,2) :: (103,107,4) :: (107,109,2) :: (109,113,4) :: (113,127,14) ::
  (127,131,4) :: (131,137,6) :: (137,139,2) :: (139,149,10) :: (149,151,2) :: (151,157,6) ::
  (157,163,6) :: (163,167,4) :: (167,173,6) :: (173,179,6) :: (179,181,2) :: (181,191,10) ::
  (191,193,2) :: (193,197,4) :: (197,199,2) :: (199,211,12) :: (211,223,12) :: (223,227,4) ::
  (227,229,2) :: (229,233,4) :: (233,239,6) :: (239,241,2) :: (241,251,10) :: (251,257,6) ::
  (257,263,6) :: (263,269,6) :: (269,271,2) :: (271,277,6) :: (277,281,4) :: (281,283,2) ::
  (283,293,10) :: (293,307,14) :: (307,311,4) :: (311,313,2) :: (313,317,4) :: (317,331,14) ::
  (331,337,6) :: (337,347,10) :: (347,349,2) :: (349,353,4) :: (353,359,6) :: (359,367,8) ::
  (367,373,6) :: (373,379,6) :: (379,383,4) :: (383,389,6) :: (389,397,8) :: (397,401,4) ::
  (401,409,8) :: (409,419,10) :: (419,421,2) :: (421,431,10) :: (431,433,2) :: (433,439,6) ::
  (439,443,4) :: (443,449,6) :: (449,457,8) :: (457,461,4) :: (461,463,2) :: (463,467,4) ::
  (467,479,12) :: (479,487,8) :: (487,491,4) :: (491,499,8) :: (499,503,4) :: (503,509,6) ::
  (509,521,4) :: nil.

(* ---- Section 1. Ascending scan machine (option exit; 0 is never returned, the fuel is the window width) ---- *)

Fixpoint pbr_scan (n k : nat) : option nat :=
  match k with
  | 0 => None
  | S k' => if pr_prime_bool (S n) then Some (S n) else pbr_scan (S n) k'
  end.

Definition pbr_search (n : nat) : option nat := pbr_scan n n.

Definition pbr_opt_witness (n : nat) : nat :=
  match pbr_search n with
  | Some p => p
  | None => 0
  end.

Lemma pbr_scan_S : forall n k : nat,
  pbr_scan n (S k) =
  (if pr_prime_bool (S n) then Some (S n) else pbr_scan (S n) k).
Proof. reflexivity. Qed.

(* Soundness: any value the search returns is a prime inside the window (unconditional, general form). *)
Lemma pbr_scan_some : forall k n p : nat,
  pbr_scan n k = Some p ->
  And (NatLe (S n) p) (And (NatLe p (n + k)) (pr_prime p)).
Proof.
  intros k. induction k as [|k IH]; intros n p H.
  - discriminate.
  - rewrite pbr_scan_S in H. destruct (pr_prime_bool (S n)) eqn:Eb.
    + injection H as Hp. subst p.
      split; [apply NatLe_lift; lia |].
      split; [apply NatLe_lift; lia | apply pr_prime_bool_true; exact Eb].
    + apply IH in H. destruct H as [H1 [H2 H3]].
      pose proof (NatLe_drop _ _ H1). pose proof (NatLe_drop _ _ H2).
      split; [apply NatLe_lift; lia |].
      split; [apply NatLe_lift; lia | exact H3].
Qed.

(* Completeness: if the window contains a prime then the search hits it
   (unconditional, general form).  Termination is immediate from the fuel
   being the window width; the hit argument needs no extra lemma. *)
Lemma pbr_scan_hit : forall k n q : nat,
  n < q -> q <= n + k -> pr_prime q ->
  exists p : nat, pbr_scan n k = Some p.
Proof.
  intros k. induction k as [|k IH]; intros n q Hnq Hqk Hq.
  - exfalso. lia.
  - rewrite pbr_scan_S. destruct (pr_prime_bool (S n)) eqn:Eb.
    + exists (S n). reflexivity.
    + assert (Hq2 : S n < q).
      { destruct (Nat.eq_dec q (S n)) as [Heq|Hne].
        - exfalso.
          assert (Hb1 : pr_prime_bool (S n) = true).
          { rewrite <- Heq.
            exact (match pr_prime_bool_false q Hq in Id _ z
                   return pr_prime_bool q = z with id_refl => eq_refl end). }
          rewrite Hb1 in Eb. discriminate.
        - lia. }
      apply (IH (S n) q); [exact Hq2 | lia | exact Hq].
Qed.

Lemma pbr_search_some : forall n p : nat,
  pbr_search n = Some p ->
  And (NatLe (S n) p) (And (NatLe p (2 * n)) (pr_prime p)).
Proof.
  intros n p H. unfold pbr_search in H.
  apply (pbr_scan_some n n p) in H. destruct H as [H1 [H2 H3]].
  pose proof (NatLe_drop _ _ H2).
  split; [exact H1 | split; [apply NatLe_lift; lia | exact H3]].
Qed.

Lemma pbr_search_hit : forall n q : nat,
  n < q -> q <= 2 * n -> pr_prime q ->
  exists p : nat, pbr_search n = Some p.
Proof.
  intros n q Hnq Hqn Hq. unfold pbr_search.
  apply (pbr_scan_hit n n q); [exact Hnq | lia | exact Hq].
Qed.

(* Computable witness readout of the search exit (the None branch is excluded by the premise). *)
Lemma pbr_opt_witness_eq : forall n : nat,
  (pbr_search n = None -> False) ->
  pbr_search n = Some (pbr_opt_witness n).
Proof.
  intros n Hne. revert Hne.
  destruct (pbr_search n) as [p|] eqn:E.
  - intros _. unfold pbr_opt_witness. rewrite E. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
Qed.

(* ---- Section 2. Segment-table checkers and verification lemmas ---- *)

Fixpoint pbr_run_ok (k p len : nat) : bool :=
  match len with
  | 0 => true
  | S len' => andb (andb (Nat.ltb k p) (Nat.leb p (2 * k))) (pbr_run_ok (S k) p len')
  end.

Fixpoint pbr_runs_ok (k : nat) (l : list (nat * nat * nat)) : bool :=
  match l with
  | nil => Nat.ltb pbr_N k
  | (n0, p, len) :: l' =>
      andb (Nat.eqb k n0)
           (andb (pr_prime_bool p)
                 (andb (pbr_run_ok k p len) (pbr_runs_ok (k + len) l')))
  end.

Fixpoint pbr_runs_len (l : list (nat * nat * nat)) : nat :=
  match l with
  | nil => 0
  | (n0, p, len) :: l' => len + pbr_runs_len l'
  end.

Fixpoint pbr_pick (n : nat) (l : list (nat * nat * nat)) : nat :=
  match l with
  | nil => 0
  | (n0, p, len) :: l' => if Nat.ltb n (n0 + len) then p else pbr_pick n l'
  end.

Lemma pbr_run_ok_S : forall k p len : nat,
  pbr_run_ok k p (S len) =
  andb (andb (Nat.ltb k p) (Nat.leb p (2 * k))) (pbr_run_ok (S k) p len).
Proof. reflexivity. Qed.

Lemma pbr_runs_ok_cons : forall k n0 p len l,
  pbr_runs_ok k ((n0, p, len) :: l) =
  andb (Nat.eqb k n0)
       (andb (pr_prime_bool p)
             (andb (pbr_run_ok k p len) (pbr_runs_ok (k + len) l))).
Proof. reflexivity. Qed.

Lemma pbr_runs_len_cons : forall n0 p len l,
  pbr_runs_len ((n0, p, len) :: l) = len + pbr_runs_len l.
Proof. reflexivity. Qed.

Lemma pbr_pick_cons : forall n n0 p len l,
  pbr_pick n ((n0, p, len) :: l) =
  (if Nat.ltb n (n0 + len) then p else pbr_pick n l).
Proof. reflexivity. Qed.

(* Pointwise window inside a segment: on a segment of length len every point k+i satisfies k+i < p <= 2 * (k+i). *)
Lemma pbr_run_ok_spec : forall len k p : nat,
  pbr_run_ok k p len = true ->
  forall i : nat, i < len -> k + i < p /\ p <= 2 * (k + i).
Proof.
  intros len. induction len as [|len IH]; intros k p Hok i Hi.
  - exfalso. lia.
  - rewrite pbr_run_ok_S in Hok.
    apply andb_true_iff in Hok. destruct Hok as [H1 Hok].
    apply andb_true_iff in H1. destruct H1 as [Hlt Hle].
    apply Nat.ltb_lt in Hlt. apply Nat.leb_le in Hle.
    destruct i as [|i'].
    + rewrite Nat.add_0_r. split; [exact Hlt | exact Hle].
    + assert (Hih : i' < len) by lia.
      destruct (IH (S k) p Hok i' Hih) as [Ha Hb].
      split; lia.
Qed.

(* Main verification lemma: once the checker passes, the pick function
   pbr_pick gives, pointwise on the table domain, the three-fold witness
   strictly inside the window, prime, and within the window upper bound
   (coverage and picking are carried by one induction). *)
Lemma pbr_runs_ok_pick : forall (l : list (nat * nat * nat)) (k n : nat),
  pbr_runs_ok k l = true -> k <= n -> n < k + pbr_runs_len l ->
  And (NatLe (S n) (pbr_pick n l))
      (And (pr_prime (pbr_pick n l)) (NatLe (pbr_pick n l) (2 * n))).
Proof.
  intros l. induction l as [| [[n0 p] len] l IH]; intros k n Hok Hkn Hlt.
  - exfalso. simpl in Hlt. lia.
  - rewrite pbr_runs_len_cons in Hlt.
    rewrite pbr_runs_ok_cons in Hok.
    apply andb_true_iff in Hok. destruct Hok as [Hke Hok].
    apply andb_true_iff in Hok. destruct Hok as [Hpb Hok].
    apply andb_true_iff in Hok. destruct Hok as [Hrun Hrest].
    apply Nat.eqb_eq in Hke. subst n0.
    assert (Hpp : pr_prime p) by (apply pr_prime_bool_true; exact Hpb).
    rewrite pbr_pick_cons.
    destruct (Nat.ltb n (k + len)) eqn:Hdec.
    + change (if true then p else pbr_pick n l) with p.
      apply Nat.ltb_lt in Hdec.
      assert (Hi : n - k < len) by lia.
      destruct (pbr_run_ok_spec len k p Hrun (n - k) Hi) as [Ha Hb].
      assert (Hk : k + (n - k) = n) by lia.
      rewrite Hk in Ha, Hb.
      split; [apply NatLe_lift; exact Ha |].
      split; [exact Hpp | apply NatLe_lift; exact Hb].
    + change (if false then p else pbr_pick n l) with (pbr_pick n l).
      apply Nat.ltb_ge in Hdec.
      apply (IH (k + len) n); [exact Hrest | lia | lia].
Qed.

(* ---- Section 3. Segment-table verification points (mechanical vm_compute checks) ---- *)

Lemma pbr_runs_len_val : pbr_runs_len pbr_runs = 511.
Proof. vm_compute. reflexivity. Qed.

Lemma pbr_runs_good : pbr_runs_ok 2 pbr_runs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pbr_pick_512_val : pbr_pick 512 pbr_runs = 521.
Proof. vm_compute. reflexivity. Qed.

(* ---- Section 4. Table-domain main statements (sigT witness form; the witness term is a computable function) ---- *)

Theorem pbr_bertrand_table : forall n : nat, 2 <= n -> n <= pbr_N ->
  { p : nat & And (NatLe (S n) p) (And (pr_prime p) (NatLe p (2 * n))) }.
Proof.
  intros n H2 Hn. unfold pbr_N in Hn.
  assert (Hlt : n < 2 + pbr_runs_len pbr_runs) by (rewrite pbr_runs_len_val; lia).
  destruct (pbr_runs_ok_pick pbr_runs 2 n pbr_runs_good H2 Hlt) as [Ha [Hb Hc]].
  exists (pbr_pick n pbr_runs). split; [exact Ha | split; [exact Hb | exact Hc]].
Defined.

Theorem pbr_search_cert : forall n : nat, 2 <= n -> n <= pbr_N ->
  { p : nat & And (NatLe (S n) p)
                  (And (pr_prime p)
                       (And (NatLe p (2 * n)) (Id (pbr_search n) (Some p)))) }.
Proof.
  intros n H2 Hn. unfold pbr_N in Hn.
  assert (Htab : And (NatLe (S n) (pbr_pick n pbr_runs))
                     (And (pr_prime (pbr_pick n pbr_runs))
                          (NatLe (pbr_pick n pbr_runs) (2 * n)))).
  { assert (Hlt : n < 2 + pbr_runs_len pbr_runs) by (rewrite pbr_runs_len_val; lia).
    exact (pbr_runs_ok_pick pbr_runs 2 n pbr_runs_good H2 Hlt). }
  destruct Htab as [Ht1 [Ht2 Ht3]].
  pose proof (NatLe_drop _ _ Ht1) as Ht1p.
  pose proof (NatLe_drop _ _ Ht3) as Ht3p.
  assert (Hhit : exists p0 : nat, pbr_search n = Some p0).
  { exact (pbr_search_hit n (pbr_pick n pbr_runs) Ht1p Ht3p Ht2). }
  assert (Hne : pbr_search n = None -> False).
  { intros Hnone. destruct Hhit as [p0 Hp0]. rewrite Hnone in Hp0. discriminate. }
  assert (Heq : pbr_search n = Some (pbr_opt_witness n)) by (apply pbr_opt_witness_eq; exact Hne).
  assert (Hid : Id (pbr_search n) (Some (pbr_opt_witness n)))
    by (rewrite Heq; apply id_refl).
  unfold pbr_search in Heq.
  destruct (pbr_scan_some n n (pbr_opt_witness n) Heq) as [Hs1 [Hs2 Hs3]].
  pose proof (NatLe_drop _ _ Hs2).
  exists (pbr_opt_witness n).
  split; [exact Hs1 |].
  split; [exact Hs3 |].
  split; [apply NatLe_lift; lia | exact Hid].
Defined.

(* ---- Section 5. Monotone lifting, table-domain extension, and unbounded good points ---- *)

(* Interval-wise monotone lifting: a witness p at n lifts to every m with
   n < m < p (m > n gives 2 * m > 2 * n >= p, and m < p is a premise). *)
Lemma pbr_lift : forall n m q : nat,
  n < m -> m < q -> q <= 2 * n -> pr_prime q ->
  And (NatLe (S m) q) (And (NatLe q (2 * m)) (pr_prime q)).
Proof.
  intros n m q Hnm Hmq Hqn Hq.
  split; [apply NatLe_lift; exact Hmq |].
  split; [apply NatLe_lift; lia | exact Hq].
Qed.

(* Table-domain extension: the last segment's witness 521 covers (512,521), extending the unconditional coverage to [2,520]. *)
Theorem pbr_bertrand_ext : forall n : nat, 2 <= n -> n <= 520 ->
  { p : nat & And (NatLe (S n) p) (And (pr_prime p) (NatLe p (2 * n))) }.
Proof.
  intros n H2 Hn.
  destruct (le_gt_dec n pbr_N) as [Hle | Hgt].
  - exact (pbr_bertrand_table n H2 Hle).
  - assert (Hcov : And (NatLe (S 512) (pbr_pick 512 pbr_runs))
                       (And (pr_prime (pbr_pick 512 pbr_runs))
                            (NatLe (pbr_pick 512 pbr_runs) (2 * 512)))).
    { apply (pbr_runs_ok_pick pbr_runs 2 512 pbr_runs_good).
      - lia.
      - rewrite pbr_runs_len_val. lia. }
    rewrite pbr_pick_512_val in Hcov.
    destruct Hcov as [Ha [Hb Hc]].
    pose proof (NatLe_drop _ _ Hc) as Hcp.
    assert (Hn521 : n < 521) by lia.
    destruct (pbr_lift 512 n 521 Hgt Hn521 Hcp Hb) as [H1 [H2' H3]].
    exists 521. split; [exact H1 | split; [exact H3 | exact H2']].
Defined.

(* Unbounded good points: for every n some m >= n carries a prime in (m, 2m];
   take a prime p above n, then m = p - 1 is a good point (m < p and
   p <= 2 * m amount to p >= 2), so the Bertrand good points are unbounded. *)
Theorem pbr_bertrand_infinite : forall n : nat,
  { m : nat & (NatLe n m) *
              { p : nat & And (pr_prime p) (And (NatLe (S m) p) (NatLe p (2 * m))) } }.
Proof.
  intros n.
  pose proof (pen_prime_unbounded n) as Hpu.
  destruct Hpu as [q Hq].
  pose proof (fst Hq) as Hpr.
  pose proof (NatLe_drop _ _ (snd Hq)) as Hn0.
  pose proof (NatLe_drop _ _ (fst Hpr)) as Hq2.
  exists (q - 1). split; [apply NatLe_lift; lia | ].
  exists q.
  split; [exact Hpr |].
  pose proof (NatLe_drop _ _ (fst Hpr)).
  split; apply NatLe_lift; lia.
Defined.

(* ---- Section 6. Conditional general main statement (the conditionalized full-strength Bertrand postulate) ---- *)

Theorem pbr_bertrand_cond : forall n : nat,
  { q : nat & And (pr_prime q) (And (NatLe (S n) q) (NatLe q (2 * n))) } ->
  { p : nat & And (NatLe (S n) p)
                  (And (pr_prime p)
                       (And (NatLe p (2 * n)) (Id (pbr_search n) (Some p)))) }.
Proof.
  intros n Hget.
  assert (Hne : pbr_search n = None -> False).
  { intros Hnone.
    assert (Hhit : exists p0 : nat, pbr_search n = Some p0).
    { destruct Hget as [q [Hq [Hnq Hqn]]].
      pose proof (NatLe_drop _ _ Hnq) as Hnqp.
      pose proof (NatLe_drop _ _ Hqn) as Hqnp.
      exact (pbr_search_hit n q Hnqp Hqnp Hq). }
    destruct Hhit as [p0 Hp0]. rewrite Hnone in Hp0. discriminate. }
  assert (Heq : pbr_search n = Some (pbr_opt_witness n)) by (apply pbr_opt_witness_eq; exact Hne).
  assert (Hid : Id (pbr_search n) (Some (pbr_opt_witness n)))
    by (rewrite Heq; apply id_refl).
  unfold pbr_search in Heq.
  destruct (pbr_scan_some n n (pbr_opt_witness n) Heq) as [Hs1 [Hs2 Hs3]].
  pose proof (NatLe_drop _ _ Hs2).
  exists (pbr_opt_witness n).
  split; [exact Hs1 |].
  split; [exact Hs3 |].
  split; [apply NatLe_lift; lia | exact Hid].
Defined.

(* ---- Section 7. Numerical checks (small instances by vm_compute; n <= 12 and pure table walks) ---- *)

Lemma pbr_search_10 : pbr_search 10 = Some 11.
Proof. vm_compute. reflexivity. Qed.

Lemma pbr_search_12 : pbr_search 12 = Some 13.
Proof. vm_compute. reflexivity. Qed.

Lemma pbr_opt_4 : pbr_opt_witness 4 = 5.
Proof. vm_compute. reflexivity. Qed.

Lemma pbr_pick_100 : pbr_pick 100 pbr_runs = 101.
Proof. vm_compute. reflexivity. Qed.

(* ---- Section 8. Assumption audit ([Print Assumptions] reports [Axioms: none] on every exit) ---- *)

Print Assumptions pbr_scan_some.
Print Assumptions pbr_scan_hit.
Print Assumptions pbr_search_some.
Print Assumptions pbr_search_hit.
Print Assumptions pbr_run_ok_spec.
Print Assumptions pbr_runs_ok_pick.
Print Assumptions pbr_bertrand_table.
Print Assumptions pbr_search_cert.
Print Assumptions pbr_lift.
Print Assumptions pbr_bertrand_ext.
Print Assumptions pbr_bertrand_infinite.
Print Assumptions pbr_bertrand_cond.
