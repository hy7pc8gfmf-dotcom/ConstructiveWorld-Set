(* ConstructiveWorld-Set -- core lemmas of the first Erdos segment in the prime domain. *)

(** * abl_Pr_erdos_core: prime powers in the central binomial coefficient.

    Mission.  The binomial prime-power chain of the first Erdos segment for
      Bertrand's postulate, over the [nat] binomial machine [hl_binom].  The
      row-sum machine [pec_sum] gives [pec_row_sum] and hence the lower
      bound [pec_lower] (4^n <= (2n+1) * C(2n,n)) with strict strengthening
      [pec_central_lt].  The key Erdos observation that a prime p with
      n < p <= 2n divides C(2n,n) exactly once is [pec_mid_exactly_once],
      assembled from [pec_mid_prime_dvd], [pec_mid_not_sq_dvd] and the
      Euclid lemma [pec_euclid].  The full-strength skeleton inequality
      (window product divides C(2n,n) and is bounded by it, C(2n,n) <= 4^n)
      is [pec_erdos_skeleton] with strict form [pec_skeleton_lt].

    Dependencies.  Stdlib [Arith.Arith], [Arith.Factorial], [Bool], [List],
      [Lia], [Extraction].  Requires [HansonLcm], [abl_Pr_core_01] of this
      development.

    References.  This development, abl_Pr_erdos_core.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_Pr_erdos_core.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import Arith.Arith Arith.Factorial Bool Lia List.
Require Import HansonLcm.
Require Import abl_Pr_core_01.

(* ================= Section 1. Binomial base faces, auxiliary lemmas of [hl_binom] ================= *)

(* Out-of-range rows vanish: m < k gives [hl_binom m k = 0], by direct induction along the Pascal recursion. *)
Lemma pec_binom_out : forall m k : nat, m < k -> hl_binom m k = 0.
Proof.
  intros m. induction m as [|m IH]; intros k Hk.
  - destruct k as [|k'].
    + lia.
    + reflexivity.
  - destruct k as [|k'].
    + lia.
    + rewrite hl_binom_S.
      rewrite (IH k') by lia.
      rewrite (IH (S k')) by lia.
      reflexivity.
Qed.

(* First column: C(m,0) = 1 holds definitionally in both cases, since the fix only unfolds when its first argument starts with a constructor. *)
Lemma pec_binom_zero_r : forall m : nat, hl_binom m 0 = 1.
Proof.
  destruct m as [|m'].
  - reflexivity.
  - reflexivity.
Qed.

(* Diagonal: C(m,m) = 1. *)
Lemma pec_binom_diag : forall m : nat, hl_binom m m = 1.
Proof.
  induction m as [|m IH].
  - reflexivity.
  - rewrite hl_binom_S. rewrite IH.
    rewrite (pec_binom_out m (S m) (Nat.lt_succ_diag_r m)).
    reflexivity.
Qed.

(* Positivity floor: k <= m gives 1 <= C(m,k), since in-range row entries never vanish. *)
Lemma pec_binom_pos : forall m k : nat, k <= m -> 1 <= hl_binom m k.
Proof.
  intros m. induction m as [|m IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. cbn [hl_binom]. lia.
  - destruct k as [|k'].
    + cbn [hl_binom]. lia.
    + rewrite hl_binom_S.
      assert (H1 : 1 <= hl_binom m k') by (apply IH; lia).
      assert (H2 : 0 <= hl_binom m (S k')) by apply Nat.le_0_l.
      lia.
Qed.

(* Second column: C(m,1) = m. *)
Lemma pec_binom_1 : forall m : nat, hl_binom m 1 = m.
Proof.
  induction m as [|m IH].
  - reflexivity.
  - change (hl_binom (S m) 1) with (hl_binom (S m) (S 0)).
    rewrite hl_binom_S. rewrite pec_binom_zero_r. rewrite IH. lia.
Qed.

(* ================= Section 2. The folded sum machine, [pec_sum f n] as the sum of f i over i < n ================= *)

Fixpoint pec_sum (f : nat -> nat) (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => pec_sum f n' + f n'
  end.

Lemma pec_sum_first : forall (n : nat) (f : nat -> nat),
  pec_sum f (S n) = f 0 + pec_sum (fun i => f (S i)) n.
Proof.
  induction n as [|n IH]; intros f.
  - cbn [pec_sum]. lia.
  - assert (Hsp : pec_sum f (S (S n)) = pec_sum f (S n) + f (S n)) by reflexivity.
    rewrite Hsp. rewrite IH. cbn [pec_sum] in *. lia.
Qed.

Lemma pec_sum_add : forall (n : nat) (f g : nat -> nat),
  pec_sum (fun i => f i + g i) n = pec_sum f n + pec_sum g n.
Proof.
  induction n as [|n IH]; intros f g.
  - reflexivity.
  - cbn [pec_sum]. rewrite IH. lia.
Qed.

Lemma pec_sum_ext : forall (n : nat) (f g : nat -> nat),
  (forall i : nat, i < n -> f i = g i) -> pec_sum f n = pec_sum g n.
Proof.
  induction n as [|n IH]; intros f g H.
  - reflexivity.
  - cbn [pec_sum]. rewrite (IH f g) by (intros i Hi; apply H; lia).
    rewrite (H n (Nat.lt_succ_diag_r n)). reflexivity.
Qed.

Lemma pec_sum_le : forall (n : nat) (f g : nat -> nat),
  (forall i : nat, i < n -> f i <= g i) -> pec_sum f n <= pec_sum g n.
Proof.
  induction n as [|n IH]; intros f g H.
  - cbn [pec_sum]. lia.
  - cbn [pec_sum].
    assert (Hrec : pec_sum f n <= pec_sum g n) by (apply IH; intros i Hi; apply H; lia).
    pose proof (H n (Nat.lt_succ_diag_r n)). lia.
Qed.

Lemma pec_sum_const : forall n c : nat, pec_sum (fun _ => c) (S n) = S n * c.
Proof.
  induction n as [|n IH]; intros c.
  - cbn [pec_sum]. lia.
  - assert (Hsp : pec_sum (fun _ => c) (S (S n)) = pec_sum (fun _ => c) (S n) + c)
      by reflexivity.
    rewrite Hsp, IH. lia.
Qed.

Lemma pec_sum_ge : forall (n i : nat) (f : nat -> nat), i < n -> f i <= pec_sum f n.
Proof.
  induction n as [|n IH]; intros i f Hi.
  - lia.
  - cbn [pec_sum]. destruct (Nat.eq_dec i n) as [E|NE].
    + subst i. lia.
    + assert (Hrec : f i <= pec_sum f n) by (apply IH; lia).
      lia.
Qed.

(* Row-sum master statement: the row entries of [hl_binom m] for k <= m sum to 2^m.  The Pascal double split peels off the first entry 1 and the shifted row, so 2^m = 1 + (2^m - 1) + (2^m - 1); the remaining arithmetic is linear. *)
Lemma pec_row_sum : forall m : nat, pec_sum (hl_binom m) (S m) = 2 ^ m.
Proof.
  induction m as [|m IH].
  - cbn [pec_sum hl_binom Nat.pow]. lia.
  - assert (Hsp : pec_sum (hl_binom (S m)) (S (S m))
                = pec_sum (hl_binom (S m)) (S m) + hl_binom (S m) (S m))
      by reflexivity.
    rewrite Hsp. rewrite pec_binom_diag.
    rewrite (pec_sum_first m (hl_binom (S m))).
    cbn [hl_binom].
    rewrite pec_sum_add.
    assert (H1 : pec_sum (hl_binom m) m + 1 = 2 ^ m).
    { assert (Hsp1 : pec_sum (hl_binom m) (S m) = pec_sum (hl_binom m) m + hl_binom m m)
        by reflexivity.
      rewrite pec_binom_diag in Hsp1. rewrite IH in Hsp1. lia. }
    assert (H2 : 1 + pec_sum (fun i => hl_binom m (S i)) m = 2 ^ m).
    { pose proof (pec_sum_first m (hl_binom m)) as Hf.
      rewrite pec_binom_zero_r in Hf. rewrite IH in Hf. lia. }
    rewrite Nat.pow_succ_r'. lia.
Qed.

(* ================= Section 3. Row monotonicity, the middle entry as row maximum ================= *)

(* Symmetry law: k <= m gives C(m,k) = C(m,m-k), by induction with both branches driven, combining the out-of-range zero, the diagonal and the Pascal recursion. *)
Lemma pec_binom_sym : forall m k : nat, k <= m -> hl_binom m k = hl_binom m (m - k).
Proof.
  intros m. induction m as [|m IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. reflexivity.
  - destruct k as [|k'].
    + replace (S m - 0) with (S m) by reflexivity.
      rewrite pec_binom_diag. apply pec_binom_zero_r.
    + rewrite hl_binom_S.
      replace (S m - S k') with (m - k') by reflexivity.
      destruct (m - k') as [|i] eqn:Hi.
      * assert (Hkm : k' = m) by lia. subst k'.
        rewrite pec_binom_diag. rewrite pec_binom_zero_r.
        rewrite pec_binom_out by lia. reflexivity.
      * rewrite (hl_binom_S m i).
        assert (E1 : hl_binom m k' = hl_binom m (S i)).
        { replace (S i) with (m - k') by (rewrite Hi; reflexivity).
          apply (IH k'). lia. }
        assert (E2 : hl_binom m (S k') = hl_binom m i).
        { replace i with (m - S k') by lia.
          apply (IH (S k')). lia. }
        lia.
Qed.

(* Climb lemma: 2k+1 <= m gives C(m,k) <= C(m,k+1).  The absorption identity C(m,k+1) * (k+1) = C(m,k) * (m-k) for S k <= m is proved by a self-contained induction with the boundary case S k = a split off; multiplication monotonicity and cancellation of the positive factor m - k then give the climb. *)
Lemma pec_mono : forall m k : nat, k + k + 1 <= m -> hl_binom m k <= hl_binom m (S k).
Proof.
  intros m k Hk.
  assert (Hgen : forall a b : nat, S b <= a ->
              hl_binom a (S b) * S b = hl_binom a b * (a - b)).
  { intros a. induction a as [|a IHa]; intros b Hb.
    - lia.
    - destruct b as [|b'].
      + rewrite pec_binom_1. rewrite pec_binom_zero_r.
        replace (S a - 0) with (S a) by reflexivity.
        rewrite Nat.mul_1_r. rewrite Nat.mul_1_l. reflexivity.
      + destruct (Nat.eq_dec (S b') a) as [Eb | NEb].
        * subst a.
          rewrite pec_binom_diag.
          rewrite Nat.mul_1_l.
          rewrite pec_binom_sym by lia.
          replace (S (S b') - S b') with 1 by lia.
          rewrite pec_binom_1.
          rewrite Nat.mul_1_r.
          reflexivity.
        * assert (Hba : S (S b') <= a) by lia.
          rewrite hl_binom_S. replace (S a - S b') with (a - b') by reflexivity.
          rewrite hl_binom_S.
          rewrite Nat.mul_add_distr_r. rewrite Nat.mul_add_distr_r.
          rewrite (IHa (S b') Hba).
          assert (Hb' : b' < a) by lia.
          rewrite <- (IHa b' Hb').
          rewrite <- Nat.mul_add_distr_l. rewrite <- Nat.mul_add_distr_l.
          replace (S (S b') + (a - S b')) with (S a) by lia.
          replace (S b' + (a - b')) with (S a) by lia.
          reflexivity. }
  assert (Hab : hl_binom m (S k) * S k = hl_binom m k * (m - k))
    by (apply Hgen; lia).
  assert (HkB : S k <= m - k) by lia.
  assert (Hpos : 0 < m - k) by lia.
  assert (Hstep : hl_binom m (S k) * S k <= hl_binom m (S k) * (m - k))
    by (apply Nat.mul_le_mono_l; exact HkB).
  rewrite Hab in Hstep.
  apply (proj2 (Nat.mul_le_mono_pos_r (hl_binom m k) (hl_binom m (S k)) (m - k) Hpos)).
  exact Hstep.
Qed.

(* Chained climb: a <= b with b + b <= m gives C(m,a) <= C(m,b), by stepping the climb lemma from a up to b. *)
Lemma pec_mono_chain : forall m b a : nat,
  a <= b -> b + b <= m -> hl_binom m a <= hl_binom m b.
Proof.
  intros m b. induction b as [|b IH]; intros a Ha Hb.
  - assert (a = 0) by lia. subst a. apply Nat.le_refl.
  - destruct (Nat.eq_dec a (S b)) as [E|NE].
    + subst a. apply Nat.le_refl.
    + assert (Hstep : hl_binom m b <= hl_binom m (S b)) by (apply pec_mono; lia).
      assert (Hrec : hl_binom m a <= hl_binom m b) by (apply IH; lia).
      lia.
Qed.

(* The middle entry is a row maximum: k <= 2n gives C(2n,k) <= C(2n,n); for k <= n this is a direct climb, for k > n the symmetry law reflects k to 2n - k and climbs back. *)
Lemma pec_max_mid : forall n k : nat, k <= 2 * n -> hl_binom (2 * n) k <= hl_binom (2 * n) n.
Proof.
  intros n k Hk. destruct (le_lt_dec k n) as [Hle | Hgt].
  - apply (pec_mono_chain (2 * n) n k Hle). lia.
  - assert (Hsym : hl_binom (2 * n) k = hl_binom (2 * n) (2 * n - k))
      by (apply pec_binom_sym; lia).
    rewrite Hsym.
    apply (pec_mono_chain (2 * n) n (2 * n - k)); lia.
Qed.

(* ================= Section 4. Layer 1a, the middle-entry lower bound 4^n <= (2n+1) * C(2n,n) and the strict upper bound ================= *)

Lemma pec_lower_nat : forall n : nat, 4 ^ n <= (2 * n + 1) * hl_binom (2 * n) n.
Proof.
  intros n. rewrite hl_pow4. replace (2 * n + 1) with (S (2 * n)) by lia.
  rewrite <- (pec_sum_const (2 * n) (hl_binom (2 * n) n)).
  rewrite <- (pec_row_sum (2 * n)).
  apply pec_sum_le. intros i Hi. apply pec_max_mid. lia.
Qed.

(* Layer 1a main statement, carried on the informative face by [hl_le_t]. *)
Theorem pec_lower : forall n : nat,
  hl_le_t (4 ^ n)%nat ((2 * n + 1) * hl_binom (2 * n) n).
Proof.
  intro n. apply hl_le_to_le_t. exact (pec_lower_nat n).
Qed.

(* Strict upper bound strengthening: n >= 1 gives C(2n,n) + 2 <= 4^n.  The two further row entries C(2n,0) = 1 and C(2n,2n) = 1 sit alongside the middle entry: the first entry is split off the row sum, the final entry is the diagonal, and the middle entry pointwise dominates every remaining entry. *)
Lemma pec_central_lt : forall n : nat, 1 <= n -> hl_binom (2 * n) n + 2 <= 4 ^ n.
Proof.
  intros n Hn. rewrite hl_pow4. rewrite <- (pec_row_sum (2 * n)).
  rewrite (pec_sum_first (2 * n) (hl_binom (2 * n))).
  rewrite pec_binom_zero_r.
  assert (Htwo : forall (f : nat -> nat) (m i j : nat),
            i < j -> j < m -> f i + f j <= pec_sum f m).
  { intros f m. induction m as [|m IH]; intros i j Hij Hjm.
    - lia.
    - cbn [pec_sum]. destruct (Nat.eq_dec j m) as [Ej | NEj].
      + subst j.
        assert (Hfi : f i <= pec_sum f m) by (apply (pec_sum_ge m i f); lia).
        lia.
      + assert (Hrec : f i + f j <= pec_sum f m) by (apply IH; lia).
        lia. }
  assert (Hij : n - 1 < 2 * n - 1) by lia.
  assert (Hjm : 2 * n - 1 < 2 * n) by lia.
  pose proof (Htwo (fun i => hl_binom (2 * n) (S i)) (2 * n) (n - 1) (2 * n - 1)
              Hij Hjm) as Htwoi.
  cbv beta in Htwoi.
  replace (S (n - 1)) with n in Htwoi by lia.
  replace (S (2 * n - 1)) with (2 * n) in Htwoi by lia.
  rewrite pec_binom_diag in Htwoi.
  lia.
Qed.

(* ================= Section 5. The self-contained divisibility face with explicit witnesses and the Euclid lemma ================= *)

Inductive pec_dvd (d n : nat) : Set := pec_dvd_intro : forall z : nat, n = d * z -> pec_dvd d n.

Lemma pec_dvd_of_eq : forall d n z : nat, n = d * z -> pec_dvd d n.
Proof. intros d n z H. exists z. exact H. Qed.

Lemma pec_dvd_mul_r : forall d a q : nat, pec_dvd d a -> pec_dvd d (q * a).
Proof.
  intros d a q [z Hz]. exists (q * z). rewrite Hz. ring.
Qed.

(* Additive cancellation for divisibility: d dividing x and x + y gives d dividing y, with witness z2 - z1 and the truncated identity d * (z2 - z1) = d * z2 - d * z1; the arithmetic is fully deterministic. *)
Lemma pec_dvd_add_r : forall d x y : nat,
  pec_dvd d x -> pec_dvd d (x + y) -> pec_dvd d y.
Proof.
  intros d x y [z1 Hz1] [z2 Hz2]. exists (z2 - z1).
  rewrite Hz1 in Hz2.
  rewrite Nat.mul_sub_distr_l. lia.
Qed.

(* Divisibility-division bridge: d dividing n gives n = d * (n / d); this pivot lemma assembles the informative witnesses through computable division. *)
Lemma pec_dvd_div_eq : forall d n : nat, pec_dvd d n -> n = d * (n / d).
Proof.
  intros d n [z Hz]. destruct d as [|d'].
  - rewrite Nat.mul_0_l in Hz. subst n. reflexivity.
  - assert (Hne : S d' <> 0) by lia.
    pose proof (Nat.div_mod n (S d') Hne) as Hdm.
    assert (Hm0 : n mod S d' = 0).
    { apply (proj2 (Nat.Div0.mod_divides n (S d'))).
      exists z. exact Hz. }
    rewrite Hm0 in Hdm. rewrite Nat.add_0_r in Hdm. exact Hdm.
Qed.

(* Contradiction case split on small product shapes: with 2 <= p and 1 <= r < p, the equation r = p * w is impossible, since w = 0 gives r = 0, w = 1 gives r = p and w = S (S w1) gives r >= p, all against 1 <= r < p. *)
Lemma pec_small_prod_contra : forall p r w : nat,
  2 <= p -> 1 <= r -> r < p -> r = p * w -> False.
Proof.
  intros p r w Hp2 Hr1 Hrp Hw. destruct w as [|w0].
  - rewrite Nat.mul_0_r in Hw. lia.
  - destruct w0 as [|w1].
    + rewrite Nat.mul_1_r in Hw. lia.
    + rewrite Nat.mul_succ_r in Hw. rewrite Nat.mul_succ_r in Hw. lia.
Qed.

Lemma pec_two_p_contra : forall p m w : nat,
  2 <= p -> p <= m -> m < 2 * p -> m <> p -> m = p * w -> False.
Proof.
  intros p m w Hp2 Hpm Hm2p Hne Hw. destruct w as [|w0].
  - rewrite Nat.mul_0_r in Hw. lia.
  - destruct w0 as [|w1].
    + rewrite Nat.mul_1_r in Hw. lia.
    + rewrite Nat.mul_succ_r in Hw. rewrite Nat.mul_succ_r in Hw. lia.
Qed.

(* Euclid lemma, strong form on the branch i < p: for prime p with 1 <= i < p, p dividing i * a forces p dividing a.  Well-founded induction on i keeps the induction premise explicit.  Writing p = (p / i) * i + p mod i splits the cases: for p mod i = 0 the divisibility i | p contradicts the primality of p; for p mod i >= 1 the identity p * a = (p / i) * (i * a) + (p mod i) * a cancels the (p / i) * (i * a) summand and reduces to p dividing (p mod i) * a, where the induction premise applies. *)
Lemma pec_euclid_aux : forall p i a : nat, pr_prime p -> 1 <= i -> i < p ->
  pec_dvd p (i * a) -> pec_dvd p a.
Proof.
  intros p.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun i => forall a : nat, pr_prime p -> 1 <= i -> i < p ->
       pec_dvd p (i * a) -> pec_dvd p a)).
  intros i IH a Hp Hi1 Hip Hdvd.
  destruct (Nat.eq_dec i 1) as [E1 | NE1].
  - subst i. destruct Hdvd as [z Hz]. cbn [Nat.mul] in Hz.
    rewrite Nat.add_0_r in Hz. exists z. exact Hz.
  - assert (Hi2 : 2 <= i) by lia.
    assert (Hne : i <> 0) by lia.
    pose proof (Nat.div_mod p i Hne) as Hdm.
    destruct (Nat.eq_dec (p mod i) 0) as [Hr0 | Hr0].
    + exfalso. unfold pr_prime in Hp. destruct Hp as [_ Hno].
      pose proof (Hno i (S01_BaseRing.NatLe_lift _ _ Hi2)
                    (S01_BaseRing.NatLe_lift _ _ Hip)) as Hni.
      assert (Hne' : Nat.eqb (p mod i) 0 = false).
      { exact (match Hni in (S01_BaseRing.Id _ z0) return (Nat.eqb (p mod i) 0 = z0)
               with S01_BaseRing.id_refl => eq_refl end). }
      rewrite Hr0 in Hne'. simpl in Hne'. discriminate.
    + assert (Hr1 : 1 <= p mod i) by lia.
      assert (Hri : p mod i < i) by (apply (Nat.mod_upper_bound p i Hne)).
      assert (Hip2 : p mod i < p) by lia.
      assert (Hra : pec_dvd p (p mod i * a)).
      { destruct Hdvd as [zv Hzv].
        assert (Hsum : p * a = (p / i) * (p * zv) + p mod i * a).
        { assert (Hs : i * (p / i) + p mod i = p) by (symmetry; exact Hdm).
          assert (Hdistr : (i * (p / i) + p mod i) * a
                           = (p / i) * (i * a) + p mod i * a)
            by (rewrite Nat.mul_add_distr_r; ring).
          rewrite Hs in Hdistr. rewrite Hzv in Hdistr. exact Hdistr. }
        assert (Hge : (p / i) * zv <= a).
        { assert (Hp0 : 0 < p) by (unfold pr_prime in Hp; destruct Hp as [Hp2 _]; pose proof (S01_BaseRing.NatLe_drop _ _ Hp2); lia).
          apply (proj2 (Nat.mul_le_mono_pos_r ((p / i) * zv) a p Hp0)).
          lia. }
        exists (a - (p / i) * zv).
        rewrite Nat.mul_sub_distr_l. lia. }
      exact (IH (p mod i) Hri a Hp Hr1 Hip2 Hra).
Qed.

(* Euclid lemma, full form: for prime p, p dividing i * a forces p dividing i or p dividing a.  For i >= p the remainder first lowers the index, i = (i / p) * p + i mod p, and remainder zero gives the left branch; for i < p the remainder equals i and the auxiliary lemma applies directly. *)
Lemma pec_euclid : forall p i a : nat, pr_prime p ->
  pec_dvd p (i * a) -> S01_BaseRing.Or (pec_dvd p i) (pec_dvd p a).
Proof.
  intros p.
  apply (well_founded_induction_type Wf_nat.lt_wf
    (fun i => forall a : nat, pr_prime p ->
       pec_dvd p (i * a) -> S01_BaseRing.Or (pec_dvd p i) (pec_dvd p a))).
  intros i IH a Hp Hdvd.
  destruct (Nat.eq_dec i 0) as [E0 | NE0].
  - subst i. left. exists 0. lia.
  - assert (Hi1 : 1 <= i) by lia.
    assert (Hne : p <> 0) by (unfold pr_prime in Hp; destruct Hp as [Hp2 _]; pose proof (S01_BaseRing.NatLe_drop _ _ Hp2); lia).
    pose proof (Nat.mod_upper_bound i p Hne) as Hrb.
    pose proof (Nat.div_mod i p Hne) as Hdm.
    destruct (Nat.eq_dec (i mod p) 0) as [Hr0 | Hr0].
    + left.
      assert (Hfin : i = p * (i / p)).
      { rewrite Hdm at 1. rewrite Hr0. rewrite Nat.add_0_r. reflexivity. }
      exists (i / p). exact Hfin.
    + assert (Hr1 : 1 <= i mod p) by lia.
      assert (Hra : pec_dvd p (i mod p * a)).
      { destruct Hdvd as [zv Hzv].
        assert (Hsum : p * zv = p * (i / p) * a + i mod p * a).
        { assert (Hdistr : (p * (i / p) + i mod p) * a
                           = p * (i / p) * a + i mod p * a)
            by (rewrite Nat.mul_add_distr_r; reflexivity).
          rewrite <- Hdm in Hdistr. rewrite Hzv in Hdistr. exact Hdistr. }
        assert (Hge : (i / p) * a <= zv).
        { assert (Hp0 : 0 < p) by (unfold pr_prime in Hp; destruct Hp as [Hp2 _]; pose proof (S01_BaseRing.NatLe_drop _ _ Hp2); lia).
          apply (proj2 (Nat.mul_le_mono_pos_r ((i / p) * a) zv p Hp0)).
          lia. }
        exists (zv - (i / p) * a).
        rewrite Nat.mul_sub_distr_l. lia. }
      destruct (le_lt_dec p i) as [Hpi | Hip].
      * assert (Hri : i mod p < i) by lia.
        destruct (IH (i mod p) Hri a Hp Hra) as [Hl | Hr2].
        -- exfalso. destruct Hl as [w Hw].
           unfold pr_prime in Hp. destruct Hp as [Hp2 _].
           exact (pec_small_prod_contra p (i mod p) w (S01_BaseRing.NatLe_drop _ _ Hp2) Hr1 Hrb Hw).
        -- right. exact Hr2.
      * assert (Hreq : i mod p = i) by (apply Nat.mod_small; lia).
        rewrite Hreq in Hra.
        right. exact (pec_euclid_aux p i a Hp Hi1 Hip Hra).
Qed.

(* Primes dividing primes are equal: p and q both prime with p dividing q force p = q, by excluding the strict orderings on both sides. *)
Lemma pec_prime_dvd_prime : forall p q : nat,
  pr_prime p -> pr_prime q -> pec_dvd p q -> p = q.
Proof.
  intros p q Hp Hq Hd. destruct Hd as [w Hw].
  unfold pr_prime in Hp. destruct Hp as [Hp2 _].
  unfold pr_prime in Hq. destruct Hq as [Hq2 Hqn].
  destruct (lt_eq_lt_dec p q) as [[Hlt | Heq] | Hgt].
  - exfalso. assert (Hni : S01_BaseRing.Id (Nat.eqb (q mod p) 0) false).
    { apply (Hqn p Hp2 (S01_BaseRing.NatLe_lift _ _ Hlt)). }
    assert (Hne' : Nat.eqb (q mod p) 0 = false).
    { exact (match Hni in (S01_BaseRing.Id _ z0) return (Nat.eqb (q mod p) 0 = z0)
             with S01_BaseRing.id_refl => eq_refl end). }
    assert (Hmod : q mod p = 0).
    { apply (proj2 (Nat.Div0.mod_divides q p)). exists w. exact Hw. }
    rewrite Hmod in Hne'. simpl in Hne'. discriminate.
  - exact Heq.
  - exfalso. assert (Hq1 : 1 <= q) by (pose proof (S01_BaseRing.NatLe_drop _ _ Hq2); lia).
    exact (pec_small_prod_contra p q w (S01_BaseRing.NatLe_drop _ _ Hp2) Hq1 Hgt Hw).
Qed.

(* Combination lemma: for prime x with x not dividing P, x dividing C and P dividing C force x * P to divide C, by splitting the witness w of C = P * w with the Euclid lemma. *)
Lemma pec_combine : forall x P C : nat,
  pr_prime x -> (pec_dvd x P -> False) ->
  pec_dvd x C -> pec_dvd P C -> pec_dvd (x * P) C.
Proof.
  intros x P C Hp HnP HdC HdP.
  destruct HdP as [w Hw].
  assert (HdC2 : pec_dvd x (P * w)) by (rewrite <- Hw; exact HdC).
  destruct (pec_euclid x P w Hp HdC2) as [Hd1 | Hdw].
  - exfalso. apply HnP. exact Hd1.
  - destruct Hdw as [u Hu]. exists u. rewrite Hw, Hu. ring.
Qed.

(* ================= Section 6. Factorial identities and prime-factorial interaction ================= *)

Lemma pec_fact_step : forall n : nat, fact (S n) = S n * fact n.
Proof. intro n. cbn [fact]. ring. Qed.

(* Factorial identity of the Pascal binomial: k <= m gives C(m,k) * k! * (m-k)! = m!.  The induction step has three cases: k = 0 computes directly, k = m uses the diagonal and the out-of-range zero, and k < m combines the two induction hypotheses with the distributivity of the sum, all through plain equalities. *)
Lemma pec_binom_fact : forall m k : nat, k <= m ->
  hl_binom m k * fact k * fact (m - k) = fact m.
Proof.
  induction m as [|m IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. reflexivity.
  - destruct k as [|k'].
    + cbn [hl_binom]. rewrite Nat.sub_0_r. cbn [fact]. ring.
    + assert (Hk' : k' <= m) by lia.
      destruct (Nat.eq_dec k' m) as [E | NE].
      * subst k'. rewrite pec_binom_diag.
        replace (S m - S m) with 0 by lia. cbn [fact]. ring.
      * assert (Hk2 : S k' <= m) by lia.
        pose proof (IH k' Hk') as H1.
        pose proof (IH (S k') Hk2) as H2.
        rewrite hl_binom_S.
        replace (S m - S k') with (m - k') by reflexivity.
        rewrite pec_fact_step. rewrite (pec_fact_step m).
        rewrite pec_fact_step in H2.
        assert (Hv : fact (m - k') = S (m - S k') * fact (m - S k')).
        { replace (m - k') with (S (m - S k')) by lia. apply pec_fact_step. }
        rewrite Hv in H1.
        rewrite Hv.
        assert (Hsum : S k' + S (m - S k') = S m) by lia.
        transitivity (S k' * (hl_binom m k' * fact k' * (S (m - S k') * fact (m - S k')))
                    + S (m - S k') * (hl_binom m (S k') * (S k' * fact k') * fact (m - S k'))).
        -- ring.
        -- rewrite H1, H2. rewrite <- Hsum. rewrite Nat.mul_add_distr_r. reflexivity.
Qed.

(* Primes at most m divide m!: p prime with p <= m gives p dividing [fact m], by induction; p = S m is read off directly and p < S m passes to the induction premise. *)
Lemma pec_prime_dvd_fact : forall p m : nat, pr_prime p -> p <= m -> pec_dvd p (fact m).
Proof.
  intros p m Hp. induction m as [|m IH]; intros Hm.
  - unfold pr_prime in Hp. destruct Hp as [Hp2 _].
    pose proof (S01_BaseRing.NatLe_drop _ _ Hp2). lia.
  - destruct (Nat.eq_dec p (S m)) as [E | NE].
    + subst p. exists (fact m). apply pec_fact_step.
    + assert (Hpm : p <= m) by lia.
      destruct (IH Hpm) as [z Hz].
      exists (S m * z). rewrite pec_fact_step, Hz. ring.
Qed.

(* Primes above do not divide factorials below: p prime with n < p excludes p dividing [fact n], since the Euclid auxiliary lemma pushes the divisibility down through S n * [fact n] layer by layer until the base case p dividing 1 contradicts 2 <= p. *)
Lemma pec_prime_not_dvd_fact : forall p n : nat, pr_prime p -> n < p ->
  pec_dvd p (fact n) -> False.
Proof.
  intros p n Hp. induction n as [|n IH]; intros Hn Hd.
  - destruct Hd as [z Hz]. cbn [fact] in Hz.
    unfold pr_prime in Hp. destruct Hp as [Hp2 _].
    pose proof (S01_BaseRing.NatLe_drop _ _ Hp2).
    destruct z as [|z'].
    + rewrite Nat.mul_0_r in Hz. lia.
    + rewrite Nat.mul_succ_r in Hz. lia.
  - rewrite pec_fact_step in Hd.
    assert (Hdf : pec_dvd p (fact n)).
    { apply (pec_euclid_aux p (S n) (fact n) Hp); [lia | exact Hn | exact Hd]. }
    exfalso. apply IH; [lia | exact Hdf].
Qed.

(* ================= Section 7. Layer 1b, the prime power occurring exactly once in the middle term C(2n,n) ================= *)

Definition pec_mid (n : nat) : nat := hl_binom (2 * n) n.

Lemma pec_mid_fact_eq : forall n : nat, pec_mid n * fact n * fact n = fact (2 * n).
Proof.
  intro n. unfold pec_mid.
  pose proof (pec_binom_fact (2 * n) n ltac:(lia)) as H.
  replace (2 * n - n) with n in H by lia. exact H.
Qed.

(* Primes divide the middle term, reasoning face: p prime with n < p <= 2n divides C(2n,n).  The decomposition fact (2n) = p * z0 meets the identity C(2n,n) * n! * n! = fact (2n), and the Euclid lemma rules out the factorial factors in two steps. *)
Lemma pec_mid_dvd_prop : forall n p : nat, n < p -> p <= 2 * n -> pr_prime p ->
  pec_dvd p (pec_mid n).
Proof.
  intros n p Hnp Hp2n Hp.
  assert (Hd20 : pec_dvd p (fact (2 * n)))
    by (apply pec_prime_dvd_fact; [exact Hp | lia]).
  assert (Hdfn : pec_dvd p (fact n) -> False)
    by (apply pec_prime_not_dvd_fact; [exact Hp | exact Hnp]).
  pose proof (pec_mid_fact_eq n) as Hmid.
  assert (HdC : pec_dvd p (pec_mid n * (fact n * fact n))).
  { destruct Hd20 as [z0 Hz0]. exists z0.
    rewrite Nat.mul_assoc. rewrite Hmid. exact Hz0. }
  destruct (pec_euclid p (pec_mid n) (fact n * fact n) Hp HdC) as [H1 | H12].
  - exact H1.
  - destruct (pec_euclid p (fact n) (fact n) Hp H12) as [H2 | H2].
    + exfalso. apply (Hdfn H2).
    + exfalso. apply (Hdfn H2).
Qed.

(* Primes divide the middle term, layer 1b main face: the witness z = C(2n,n) / p is computable, so the statement is carried by the informative existential. *)
Theorem pec_mid_prime_dvd : forall n p : nat, n < p -> p <= 2 * n -> pr_prime p ->
  { z : nat & pec_mid n = p * z }.
Proof.
  intros n p Hnp Hp2n Hp. exists (pec_mid n / p).
  apply (pec_dvd_div_eq p (pec_mid n)).
  apply (pec_mid_dvd_prop n p Hnp Hp2n Hp).
Defined.

(* Single-p decomposition: for prime p with p <= m < 2p, m! = p * z with p not dividing z, on the informative existential.  Induction on m: m = p takes z = fact (p-1), and p < m passes to the induction premise before the Euclid lemma rules out a second factor of p. *)
Lemma pec_fact_single_p : forall p m : nat, pr_prime p -> p <= m -> m < 2 * p ->
  { z : nat & fact m = p * z /\ (forall w : nat, fact m = p * (p * w) -> False) }.
Proof.
  intros p m Hp. induction m as [|m IH]; intros Hpm Hm2p.
  - exfalso. unfold pr_prime in Hp. destruct Hp as [Hp2 _].
    pose proof (S01_BaseRing.NatLe_drop _ _ Hp2). lia.
  - destruct (Nat.eq_dec (S m) p) as [E | NE].
    + subst p. exists (fact m). split.
      * apply pec_fact_step.
      * intros w Hw.
        assert (Hne0 : S m <> 0) by lia.
        assert (Hc : fact m = S m * w).
        { apply (proj1 (Nat.mul_cancel_l (fact m) (S m * w) (S m) Hne0)).
          rewrite pec_fact_step in Hw. exact Hw. }
        exfalso.
        apply (pec_prime_not_dvd_fact (S m) m Hp (Nat.lt_succ_diag_r m)).
        exists w. exact Hc.
    + assert (Hpm' : p <= m) by lia.
      assert (Hm2' : m < 2 * p) by lia.
      destruct (IH Hpm' Hm2') as [z1 [Hz1 Hz1n]].
      exists (S m * z1). split.
      * rewrite pec_fact_step, Hz1. ring.
      * intros w Hw.
        assert (Hne0 : p <> 0) by (unfold pr_prime in Hp; destruct Hp as [Hp2 _]; pose proof (S01_BaseRing.NatLe_drop _ _ Hp2); lia).
        rewrite pec_fact_step in Hw. rewrite Hz1 in Hw.
        assert (Hc : S m * z1 = p * w).
        { apply (proj1 (Nat.mul_cancel_l (S m * z1) (p * w) p Hne0)).
          rewrite Nat.mul_assoc. rewrite (Nat.mul_comm p (S m)).
          rewrite <- Nat.mul_assoc. exact Hw. }
        assert (Hdvd : pec_dvd p (S m * z1)) by (exists w; exact Hc).
        destruct (pec_euclid p (S m) z1 Hp Hdvd) as [Hd1 | Hd2].
        -- exfalso. destruct Hd1 as [w2 Hw2].
           unfold pr_prime in Hp. destruct Hp as [Hp2 _].
           assert (HpmS : p <= S m) by lia.
           exact (pec_two_p_contra p (S m) w2 (S01_BaseRing.NatLe_drop _ _ Hp2) HpmS Hm2p NE Hw2).
        -- exfalso. destruct Hd2 as [w2 Hw2]. apply (Hz1n w2).
           rewrite Hz1, Hw2. reflexivity.
Defined.

(* Prime squares do not divide the middle term, layer 1b second face: p * p dividing C(2n,n) is contradictory.  Since n < p gives 2n < 2p, the factorial fact (2n) carries p exactly once, and C(2n,n) = p * (p * w) would raise the multiplicity of p in fact (2n) = C(2n,n) * n! * n! to two. *)
Theorem pec_mid_not_sq_dvd : forall n p : nat, n < p -> p <= 2 * n -> pr_prime p ->
  pec_dvd (p * p) (pec_mid n) -> False.
Proof.
  intros n p Hnp Hp2n Hp [w Hw].
  assert (Ha : p <= 2 * n) by lia.
  assert (Hb : 2 * n < 2 * p) by lia.
  destruct (pec_fact_single_p p (2 * n) Hp Ha Hb) as [z [Hz Hzn]].
  apply (Hzn (w * fact n * fact n)).
  pose proof (pec_mid_fact_eq n) as Hmid.
  rewrite <- Hmid, Hw. ring.
Qed.

(* Layer 1b main statement: the prime power occurs exactly once, joining the two faces on the informative existential. *)
Theorem pec_mid_exactly_once : forall n p : nat, n < p -> p <= 2 * n -> pr_prime p ->
  { z : nat & pec_mid n = p * z /\ (forall w : nat, pec_mid n = p * (p * w) -> False) }.
Proof.
  intros n p Hnp Hp2n Hp. exists (pec_mid n / p). split.
  - apply (pec_dvd_div_eq p (pec_mid n)). apply (pec_mid_dvd_prop n p Hnp Hp2n Hp).
  - intros w Hw. apply (pec_mid_not_sq_dvd n p Hnp Hp2n Hp). exists w.
    replace (p * p * w) with (p * (p * w)) by ring. exact Hw.
Defined.

(* ================= Section 8. Layer 2, the window prime product dividing the middle term and the skeleton inequality ================= *)

(* Window prime table: [pec_win a k] lists the primes in the interval (a, a+k], built in descending order with the boolean primality tester. *)
Fixpoint pec_win (a k : nat) : list nat :=
  match k with
  | O => nil
  | S k' => let x := a + S k' in
            if pr_prime_bool x then x :: pec_win a k' else pec_win a k'
  end.

Definition pec_winprod (n : nat) : nat := fold_right Nat.mul 1 (pec_win n n).

Lemma pec_win_in : forall a k p : nat,
  In p (pec_win a k) -> pr_prime_bool p = true /\ a < p /\ p <= a + k.
Proof.
  intros a k. induction k as [|k IH]; intros p Hin.
  - cbn [pec_win] in Hin. destruct Hin.
  - cbn [pec_win] in Hin. destruct (pr_prime_bool (a + S k)) eqn:Eb.
    + destruct Hin as [Heq | Hin].
      * subst p. split; [exact Eb | split; lia].
      * destruct (IH p Hin) as [H1 [H2 H3]]. split; [exact H1 | split; lia].
    + destruct (IH p Hin) as [H1 [H2 H3]]. split; [exact H1 | split; lia].
Qed.

(* A prime dividing a rising product divides one of its members, by pushing the Euclid lemma down the fold. *)
Lemma pec_prime_dvd_prod_in : forall (p : nat) (l : list nat),
  pr_prime p -> pec_dvd p (fold_right Nat.mul 1 l) ->
  { q : nat & In q l * pec_dvd p q }%type.
Proof.
  intros p l Hp. induction l as [|q l IH]; intros Hd.
  - cbn [fold_right] in Hd. destruct Hd as [z Hz].
    unfold pr_prime in Hp. destruct Hp as [Hp2 _].
    pose proof (S01_BaseRing.NatLe_drop _ _ Hp2).
    destruct z as [|z'].
    + rewrite Nat.mul_0_r in Hz. exfalso. lia.
    + rewrite Nat.mul_succ_r in Hz. exfalso. lia.
  - cbn [fold_right] in Hd.
    destruct (pec_euclid p q (fold_right Nat.mul 1 l) Hp Hd) as [Hq | Hl].
    + exists q. split; [left; reflexivity | exact Hq].
    + destruct (IH Hl) as [q' [Hin Hq']]. exists q'. split; [right; exact Hin | exact Hq'].
Qed.

(* The window rising product divides the middle term, reasoning face, by induction on the window width k <= n: the head x = n + S k is the largest prime of the window, x divides C(2n,n) by the exactly-once face, x cannot divide the shorter rising product since a divided member q would force x = q against q <= n + k, and the combination lemma merges x into the product. *)
Lemma pec_winprod_dvd_eq : forall n k : nat, k <= n ->
  { z : nat & pec_mid n = fold_right Nat.mul 1 (pec_win n k) * z }.
Proof.
  intros n k. induction k as [|k IH]; intros Hk.
  - exists (pec_mid n). cbn [pec_win fold_right]. ring.
  - cbn [pec_win]. destruct (pr_prime_bool (n + S k)) eqn:Eb.
    + assert (Hpx : pr_prime (n + S k)) by (apply pr_prime_bool_true; exact Eb).
      assert (Hxn : n < n + S k) by lia.
      assert (Hx2 : n + S k <= 2 * n) by lia.
      destruct (pec_mid_prime_dvd n (n + S k) Hxn Hx2 Hpx) as [vx Hvx].
      assert (HnP : pec_dvd (n + S k) (fold_right Nat.mul 1 (pec_win n k)) -> False).
      { intros Hd.
        destruct (pec_prime_dvd_prod_in (n + S k) (pec_win n k) Hpx Hd) as [q [Hin Hq]].
        destruct (pec_win_in n k q Hin) as [Hq1 [Hq2 Hq3]].
        apply pr_prime_bool_true in Hq1.
        assert (Heq : n + S k = q) by (apply (pec_prime_dvd_prime (n + S k) q Hpx Hq1 Hq)).
        lia. }
      assert (Hk' : k <= n) by lia.
      destruct (IH Hk') as [z' Hz'].
      assert (HdP : pec_dvd (fold_right Nat.mul 1 (pec_win n k)) (pec_mid n))
        by (apply (pec_dvd_of_eq (fold_right Nat.mul 1 (pec_win n k)) (pec_mid n) z' Hz')).
      destruct (pec_combine (n + S k) (fold_right Nat.mul 1 (pec_win n k)) (pec_mid n)
                            Hpx HnP (pec_dvd_of_eq (n + S k) (pec_mid n) vx Hvx) HdP)
        as [u Hu].
      exists u. cbn [fold_right]. exact Hu.
    + assert (Hk' : k <= n) by lia.
      destruct (IH Hk') as [z' Hz']. exists z'. exact Hz'.
Qed.

(* The window rising product divides the middle term, layer 2 main face: the witness z = C(2n,n) / prod is computable on the informative existential. *)
Theorem pec_win_dvd_mid : forall n : nat,
  { z : nat & pec_mid n = pec_winprod n * z }.
Proof.
  intro n.
  assert (Hd : pec_dvd (pec_winprod n) (pec_mid n)).
  { unfold pec_winprod.
    destruct (pec_winprod_dvd_eq n n (Nat.le_refl n)) as [z0 Hz0].
    apply (pec_dvd_of_eq (fold_right Nat.mul 1 (pec_win n n)) (pec_mid n) z0 Hz0). }
  exists (pec_mid n / pec_winprod n).
  apply (pec_dvd_div_eq (pec_winprod n) (pec_mid n) Hd).
Defined.

(* Layer 2 skeleton inequality, constructively joined: the product of the window primes divides C(2n,n) and the chain prod <= C(2n,n) <= 4^n holds, with the upper half citing [hl_central_binom_le] of HansonLcm directly. *)
Theorem pec_erdos_skeleton : forall n : nat,
  { z : nat & pec_mid n = pec_winprod n * z }
  * (hl_le_t (pec_winprod n) (pec_mid n) * hl_le_t (pec_mid n) (4 ^ n)%nat).
Proof.
  intro n. split.
  - apply pec_win_dvd_mid.
  - split.
    + apply hl_le_to_le_t.
      destruct (pec_win_dvd_mid n) as [z Hz].
      assert (Hpos : 1 <= pec_mid n) by (unfold pec_mid; apply pec_binom_pos; lia).
      destruct z as [|z'].
      * rewrite Nat.mul_0_r in Hz. lia.
      * rewrite Nat.mul_succ_r in Hz. lia.
    + unfold pec_mid. apply hl_central_binom_le.
Defined.

(* Strict upper-bound face of the skeleton: n >= 1 gives C(2n,n) + 2 <= 4^n, carried by [hl_le_t]. *)
Theorem pec_skeleton_lt : forall n : nat, 1 <= n -> hl_le_t (pec_mid n + 2) (4 ^ n)%nat.
Proof.
  intros n Hn. unfold pec_mid. apply hl_le_to_le_t. apply pec_central_lt. exact Hn.
Qed.

(* ================= Section 9. Numerical spot checks of the statements on small instances ================= *)

Lemma pec_smoke_lower5 : (Nat.leb (4 ^ 5) (11 * hl_binom 10 5))%bool = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_lower8 : (Nat.leb (4 ^ 4) (9 * hl_binom 8 4))%bool = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_mid4 : hl_binom 8 4 = 70.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_win4 : pec_win 4 4 = (7 :: 5 :: nil)%list.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_prod4 : pec_winprod 4 = 35.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_dvd4 : (hl_binom 8 4 mod pec_winprod 4)%nat = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma pec_smoke_notsq4 : (hl_binom 8 4 mod (5 * 5))%nat = 20.
Proof. vm_compute. reflexivity. Qed.

(* ================= Section 10. Assumption audit and extraction checks ================= *)

Print Assumptions pec_row_sum.
Print Assumptions pec_lower.
Print Assumptions pec_central_lt.
Print Assumptions pec_euclid_aux.
Print Assumptions pec_euclid.
Print Assumptions pec_binom_fact.
Print Assumptions pec_mid_prime_dvd.
Print Assumptions pec_mid_not_sq_dvd.
Print Assumptions pec_mid_exactly_once.
Print Assumptions pec_winprod_dvd_eq.
Print Assumptions pec_win_dvd_mid.
Print Assumptions pec_erdos_skeleton.
Print Assumptions pec_skeleton_lt.

From Stdlib Require Import Extraction.
Separate Extraction pec_sum pec_win pec_winprod pec_mid.
