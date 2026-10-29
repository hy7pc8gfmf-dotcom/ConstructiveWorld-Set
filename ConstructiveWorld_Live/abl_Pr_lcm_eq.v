(* ============================================================ *)
(* Mission. pr_lcm_eq_decomp : forall n : nat, hl_id            *)
(*   (hl_lcm_upto n) (fold_right Nat.mul 1 (map (fun p : nat => *)
(*   p ^ plm_v p (hl_lcm_upto n)) (pen_primes_upto n))): the     *)
(*   lcm of 1..n equals the product of prime powers p ^ e_p,    *)
(*   e_p = plm_v p (hl_lcm_upto n) the lcm's own valuation      *)
(*   (p ^ e divides L(n) iff p ^ e <= n). An earlier draft      *)
(*   used the valuation of n as the exponent, failing at        *)
(*   n = 6 (30 vs L(6) = 60); corrected here, the rest of the   *)
(*   statement kept verbatim.                                   *)
(* Dependencies. Stdlib (Arith, List, Bool, Lia); HansonLcm;    *)
(*   Hanson3Pow; abl_Pr_core_01; abl_Pr_enum_02;                *)
(*   abl_Pr_lcmdecomp_04; S01_BaseRing.                         *)
(* References. pr_prime, pr_mod0_dvd, pr_dvd_mod0,              *)
(*   pr_min_factor_exists, pen_primes_upto, pen_primes_upto_S,  *)
(*   pen_in_primes_upto, pen_fold_in_divide, pen_fold_mul_pos,  *)
(*   plm_v, plm_v_dvd, plm_v_max, plm_gcd_pow, plm_prime_gcd_1, *)
(*   plm_gcd_prod_1, plm_dvd_mul_coprime, hl_idrefl,            *)
(*   hl_lcm_divide_all, h3_lcm_fold_divide, NatLe_lift,         *)
(*   NatLe_drop.                                                *)
(* Constructivity. Set-level carrier: the statement is an       *)
(*   hl_id equation between two closed nat terms, closed by     *)
(*   hl_idrefl. Proof skeleton: two divisibility limbs -- the   *)
(*   product divides L(n), and L(n) divides the product --      *)
(*   combined by antisymmetry (Sections 2-4). All computation   *)
(*   sits in the existing extractable Fixpoints plm_v /         *)
(*   pen_primes_upto / hl_lcm_upto; refutations use the         *)
(*   -> False form only. Axioms: none (Section 6 audit).        *)
(* Build. Rocq 9.1.0: rocq c -native-compiler no -Q world6 ""    *)
(*   abl_Pr_lcm_eq.v (work directory holds world6/ deps tree).   *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import HansonLcm.
Require Import Hanson3Pow.
Require Import abl_Pr_core_01.
Require Import abl_Pr_enum_02.
Require Import abl_Pr_lcmdecomp_04.
Require Import S01_BaseRing (Id, id_refl, NatLe, NatLe_lift, NatLe_drop).

(* ---- Section 0. Auxiliary lemmas ---- *)

(* Power divisibility: w <= v implies p ^ w divides p ^ v. *)
Lemma plq_pow_le_dvd : forall p w v : nat,
  w <= v -> Nat.divide (p ^ w) (p ^ v).
Proof.
  intros p w v Hw. exists (p ^ (v - w)).
  rewrite <- Nat.pow_add_r. f_equal. lia.
Qed.

(* Positivity of the lcm: 1 <= L(n) (L(0) = 1; at the step, the lcm is *)
(* a * (b / g) with g dividing b, which gives b / g >= 1). *)
Lemma plq_lcm_pos : forall n : nat, NatLe 1 (hl_lcm_upto n).
Proof.
  intros n. apply NatLe_lift. induction n as [| n IH].
  - cbn [hl_lcm_upto]. lia.
  - cbn [hl_lcm_upto]. unfold Nat.lcm.
    assert (Hgd : Nat.divide (Nat.gcd (hl_lcm_upto n) (S n)) (S n))
      by apply Nat.gcd_divide_r.
    assert (Hg0 : Nat.gcd (hl_lcm_upto n) (S n) = 0 -> False).
    { intro Hz.
      assert (Hdv : Nat.divide (Nat.gcd (hl_lcm_upto n) (S n)) (S n))
        by apply Nat.gcd_divide_r.
      rewrite Hz in Hdv. apply Nat.divide_0_l in Hdv. lia. }
    pose proof (Nat.div_mod (S n) (Nat.gcd (hl_lcm_upto n) (S n)) Hg0) as Hdm.
    assert (Hmod : S n mod Nat.gcd (hl_lcm_upto n) (S n) = 0)
      by (apply (pr_dvd_mod0 _ (S n)); [lia | exact Hgd]).
    rewrite Hmod, Nat.add_0_r in Hdm.
    destruct (S n / Nat.gcd (hl_lcm_upto n) (S n)) as [| q] eqn:Eq.
    + exfalso. rewrite Nat.mul_0_r in Hdm. lia.
    + apply Nat.le_trans with (1 * 1).
      * lia.
      * apply Nat.mul_le_mono; lia.
Qed.

(* Positivity of the folded product: elementwise >= 1 implies fold >= 1 *)
(* (reuse pen_fold_mul_pos from the enumeration module; no new lemma). *)

(* A prime p not dividing m forces gcd p m = 1 (divisor trichotomy: *)
(* g divides a prime p only as g = 1 or g = p). *)
Lemma plq_gcd_1_of_nondvd : forall p m : nat,
  pr_prime p -> 1 <= m -> (Nat.divide p m -> False) -> Id (Nat.gcd p m) 1.
Proof.
  intros p m [Hp2 Hpdiv] Hm Hnd.
  destruct (Nat.eq_dec (Nat.gcd p m) 1) as [E1 | NE1].
  - rewrite E1. apply id_refl.
  - exfalso.
    assert (Hgp : Nat.divide (Nat.gcd p m) p) by apply Nat.gcd_divide_l.
    assert (Hgm : Nat.divide (Nat.gcd p m) m) by apply Nat.gcd_divide_r.
    assert (Hle : Nat.gcd p m <= p)
      by (apply Nat.divide_pos_le; [lia | exact Hgp]).
    remember (Nat.gcd p m) as g eqn:Eg.
    destruct g as [| [| g']].
    + apply Nat.divide_0_l in Hgp. lia.
    + apply NE1. reflexivity.
    + rewrite Eg in Hgp. rewrite Eg in Hgm.
      assert (Hg2 : Nat.gcd p m = p).
      { destruct (Nat.eq_dec (Nat.gcd p m) p) as [Eg2 | NEg2].
        - exact Eg2.
        - exfalso. apply (Hpdiv (Nat.gcd p m)); [lia | lia | exact Hgp]. }
      rewrite Hg2 in Hgm. apply Hnd. exact Hgm.
Qed.

(* NoDup is preserved by concatenation (self-built: this shape is *)
(* missing from the stdlib; case split via in_app_or). *)
Lemma plq_nodup_app : forall l1 l2 : list nat,
  NoDup l1 -> NoDup l2 ->
  (forall x : nat, In x l1 -> In x l2 -> False) ->
  NoDup (l1 ++ l2).
Proof.
  induction l1 as [| a t IH]; intros l2 H1 H2 Hdisj.
  - simpl. exact H2.
  - simpl. apply NoDup_cons.
    + intro Hin. apply in_app_or in Hin. destruct Hin as [Hit | Hin2].
      * inversion H1 as [| a0 t0 Hnin Hnd0 Heq]; subst.
        apply Hnin. exact Hit.
      * apply (Hdisj a). apply in_eq. exact Hin2.
    + apply IH.
      * inversion H1 as [| a0 t0 Hnin Hnd0 Heq]; subst. exact Hnd0.
      * exact H2.
      * intros x Hx1 Hx2. apply (Hdisj x); [apply in_cons; exact Hx1 | exact Hx2].
Qed.

(* The prime enumeration is duplicate-free: NoDup (pen_primes_upto n) *)
(* (membership of S n in the shorter list is refuted through the In *)
(* characterization pen_in_primes_upto, which would force S n <= n). *)
Lemma plq_pen_nodup : forall n : nat, NoDup (pen_primes_upto n).
Proof.
  induction n as [| n IH].
  - apply NoDup_nil.
  - rewrite pen_primes_upto_S. destruct (pr_prime_bool (S n)) eqn:Eb.
    + apply plq_nodup_app.
      * exact IH.
      * apply NoDup_cons.
        -- intros Hc. destruct Hc.
        -- apply NoDup_nil.
      * intros x Hx1 Hx2. destruct Hx2 as [Ex | Hc].
        -- subst x.
           destruct (proj1 (pen_in_primes_upto (S n) n) Hx1) as [_ Hle].
           lia.
        -- destruct Hc.
    + change (if false then S n :: nil else nil) with (@nil nat).
      rewrite app_nil_r. exact IH.
Qed.

(* ---- Section 1. Strengthening the valuation layer: the lower-exponent *)
(* divisibility clause and monotonicity of plm_v ---- *)

(* Climbing valuation, full downward divisibility: w <= plm_vmax p k e *)
(* implies p ^ w divides k. *)
Lemma plq_vmax_dvd_le : forall p k e w : nat,
  w <= plm_vmax p k e -> Nat.divide (p ^ w) k.
Proof.
  intros p k e. induction e as [| e' IH]; intros w Hw.
  - simpl in Hw. assert (E : w = 0) by lia. subst w.
    rewrite Nat.pow_0_r. apply Nat.divide_1_l.
  - change (plm_vmax p k (S e'))
      with (if Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0
            then S (plm_vmax p k e')
            else plm_vmax p k e') in Hw.
    destruct (Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0) eqn:Em.
    + simpl in Hw.
      apply Nat.eqb_eq in Em.
      destruct (Nat.eq_dec w (S (plm_vmax p k e'))) as [Ew | NEw].
      * subst w.
        destruct (Nat.eq_dec p 0) as [Ep0 | Ep0].
        -- rewrite Ep0 in Em |- *.
           change (0 ^ S (plm_vmax 0 k e')) with 0 in Em.
           rewrite Nat.mod_0_r in Em. rewrite Em.
           change (0 ^ S (plm_vmax 0 k e')) with 0.
           apply Nat.divide_0_r.
        -- assert (Hpos : 1 <= p ^ S (plm_vmax p k e')).
           { pose proof (Nat.pow_nonzero p (S (plm_vmax p k e')) Ep0). lia. }
           exact (pr_mod0_dvd (p ^ S (plm_vmax p k e')) k Hpos Em).
      * apply IH. lia.
    + simpl in Hw. exact (IH w Hw).
Qed.

(* Lower-exponent divisibility for plm_v (a third clause beyond the two *)
(* spec clauses of abl_Pr_lcmdecomp_04, supplied here). *)
Lemma plq_v_dvd_le : forall p k w : nat,
  w <= plm_v p k -> Nat.divide (p ^ w) k.
Proof.
  intros p k w Hw. unfold plm_v.
  exact (plq_vmax_dvd_le p k k w Hw).
Qed.

(* Monotonicity of the valuation: x divides y and 1 <= y and 1 < p imply *)
(* plm_v p x <= plm_v p y (by contradiction: the reverse order would *)
(* make p ^ S (plm_v p y) divide x divide y, contradicting the *)
(* maximality of plm_v p y). *)
Lemma plq_v_mono : forall p x y : nat,
  1 < p -> 1 <= y -> Nat.divide x y -> NatLe (plm_v p x) (plm_v p y).
Proof.
  intros p x y Hp Hy Hdvd.
  destruct (le_lt_dec (plm_v p x) (plm_v p y)) as [Hle | Hlt].
  - apply NatLe_lift. exact Hle.
  - exfalso.
    assert (Hd1 : Nat.divide (p ^ S (plm_v p y)) x)
      by (apply plq_v_dvd_le; lia).
    apply (plm_v_max p y Hp Hy).
    apply (Nat.divide_trans (p ^ S (plm_v p y)) x y); assumption.
Qed.

(* ---- Section 2. First limb: the product of prime powers divides L(n) *)
(* (the coprime-at-distinct-positions product divisibility, rebuilt) ---- *)

(* Coprime-product divisibility at distinct positions: for a NoDup list *)
(* l, if f p divides c for every p in l, and gcd (f p) (f q) = 1 for *)
(* every pair of distinct elements p q in l, then fold_right Nat.mul 1 *)
(* (map f l) divides c (head/tail split: the head factor is coprime to *)
(* the whole tail product, via plm_gcd_prod_1). *)
(* Rebuild note: the all-pairs premise plm_pairwise_coprime (which also *)
(* covers x = y) is unsatisfiable on a list of primes (gcd p p = p), so *)
(* the lemma is rebuilt here in distinct-pair form plus NoDup. *)
Lemma plq_powprod_dvd : forall (l : list nat) (f : nat -> nat) (c : nat),
  NoDup l ->
  (forall p : nat, In p l -> Nat.divide (f p) c) ->
  (forall p q : nat, In p l -> In q l ->
    (p = q -> False) -> Nat.gcd (f p) (f q) = 1) ->
  Nat.divide (fold_right Nat.mul 1 (map f l)) c.
Proof.
  intros l f c. induction l as [| x t IH]; intros Hnd Hdiv Hcop.
  - simpl. apply Nat.divide_1_l.
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnin Hnd0].
    simpl. apply plm_dvd_mul_coprime.
    + apply Hdiv. apply in_eq.
    + apply IH.
      * exact Hnd0.
      * intros p Hp. apply Hdiv. apply in_cons. exact Hp.
      * intros p q Hp Hq Hpq. apply Hcop.
        -- apply in_cons. exact Hp.
        -- apply in_cons. exact Hq.
        -- exact Hpq.
    + apply (plm_gcd_prod_1 (map f t) (f x)).
      intros y Hy. apply in_map_iff in Hy. destruct Hy as [p [Hfp Hpt]].
      rewrite <- Hfp. apply Hcop.
      * apply in_eq.
      * apply in_cons. exact Hpt.
      * intro Hxp. subst p. apply Hnin. exact Hpt.
Qed.

(* Main lemma of the first limb: the fold of the power table *)
(* p ^ plm_v p (hl_lcm_upto n) over the prime list (primes <= n) *)
(* divides L(n). *)
Theorem plq_powprod_dvd_lcm : forall n : nat,
  Nat.divide
    (fold_right Nat.mul 1
       (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
            (pen_primes_upto n)))
    (hl_lcm_upto n).
Proof.
  intro n.
  apply (plq_powprod_dvd _ (fun p : nat => p ^ plm_v p (hl_lcm_upto n))).
  - apply plq_pen_nodup.
  - intros p Hp. exact (plm_v_dvd p (hl_lcm_upto n)).
  - intros p q Hp Hq Hpq. apply plm_gcd_pow.
    destruct (proj1 (pen_in_primes_upto p n) Hp) as [Hpp _].
    destruct (proj1 (pen_in_primes_upto q n) Hq) as [Hqq _].
    exact (plm_prime_gcd_1 p q Hpp Hqq Hpq).
Qed.

(* ---- Section 3. Second limb: L(n) divides the product of prime powers *)
(* (strong induction, stripping one prime power per number) ---- *)

(* Per-number divisibility: 1 <= m <= n implies m divides the fold of *)
(* the power table p ^ plm_v p (hl_lcm_upto n) over the primes <= n. *)
(* Strong induction on fuel bounded by n, with m descending to a proper *)
(* divisor m'': if m is prime it already appears in the table; otherwise *)
(* take the least prime factor p, strip the full power m = p ^ w * m'' *)
(* (p does not divide m''), get divisibility for m'' from the *)
(* strong-induction instance, and push the exponent w into the table via *)
(* valuation monotonicity (m divides L(n)); the coprime-product lemma *)
(* closes the fold. *)
Lemma plq_num_dvd_powprod : forall fuel m : nat, m <= fuel -> 1 <= m ->
  forall n : nat, m <= n ->
  Nat.divide m
    (fold_right Nat.mul 1
       (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
            (pen_primes_upto n))).
Proof.
  intro fuel. induction fuel as [| f IH]; intros m Hmf Hm n Hmn.
  - exfalso. lia.
  - destruct (Nat.eq_dec m 1) as [E1 | NE1].
    + rewrite E1. apply Nat.divide_1_l.
    + assert (Hm2 : 2 <= m) by lia.
      destruct (pr_min_factor_exists m Hm2) as [p Hpf].
      destruct Hpf as [Hpd Hpp]. destruct Hpp as [Hp2 Hpdiv].
      assert (Hpm : p <= m)
        by (apply Nat.divide_pos_le; [lia | exact Hpd]).
      assert (Hw1 : 1 <= plm_v p m).
      { destruct (plm_v p m) as [| w'] eqn:Ew; [ | lia].
        exfalso. apply (plm_v_max p m); [lia | exact Hm |].
        rewrite Ew, Nat.pow_1_r. exact Hpd. }
      assert (Hpw : Nat.divide (p ^ plm_v p m) m) by apply plm_v_dvd.
      assert (Hpw0 : p ^ plm_v p m = 0 -> False)
        by (apply Nat.pow_nonzero; lia).
      assert (Hsplit : p ^ plm_v p m * (m / p ^ plm_v p m) = m).
      { pose proof (Nat.div_mod m (p ^ plm_v p m) Hpw0) as Hdm.
        assert (Hmod : m mod p ^ plm_v p m = 0)
          by (apply (pr_dvd_mod0 (p ^ plm_v p m) m); [lia | exact Hpw]).
        rewrite Hmod, Nat.add_0_r in Hdm. symmetry. exact Hdm. }
      assert (Hm2p : 1 <= m / p ^ plm_v p m).
      { destruct (m / p ^ plm_v p m) as [| q] eqn:Eq; [ | lia].
        exfalso. rewrite Nat.mul_0_r in Hsplit. lia. }
      assert (H2pw : 2 <= p ^ plm_v p m).
      { apply Nat.le_trans with (p ^ 1).
        - rewrite Nat.pow_1_r. lia.
        - apply Nat.pow_le_mono_r; lia. }
      assert (Hm2lt : m / p ^ plm_v p m < m).
      { assert (Hstep : 2 * (m / p ^ plm_v p m)
                        <= p ^ plm_v p m * (m / p ^ plm_v p m))
          by (apply Nat.mul_le_mono_r; exact H2pw).
        lia. }
      assert (Hm2f : m / p ^ plm_v p m <= f) by lia.
      assert (Hm2n : m / p ^ plm_v p m <= n) by lia.
      specialize (IH (m / p ^ plm_v p m) Hm2f Hm2p n Hm2n) as IHm2.
      assert (Hpnd : Nat.divide p (m / p ^ plm_v p m) -> False).
      { intros [t Ht].
        apply (plm_v_max p m); [lia | exact Hm |].
        exists t. rewrite Nat.pow_succ_r'.
        rewrite Nat.mul_assoc.
        rewrite <- Ht.
        symmetry.
        rewrite (Nat.mul_comm (m / p ^ plm_v p m) (p ^ plm_v p m)).
        exact Hsplit. }
      assert (Hg1 : Id (Nat.gcd p (m / p ^ plm_v p m)) 1)
        by (apply plq_gcd_1_of_nondvd; [split; [lia | exact Hpdiv] | lia | exact Hpnd]).
      assert (Hgw : Nat.gcd (p ^ plm_v p m) (m / p ^ plm_v p m) = 1).
      { rewrite <- (Nat.pow_1_r (m / p ^ plm_v p m)).
        apply plm_gcd_pow. destruct Hg1. reflexivity. }
      assert (Hpwn : plm_v p m <= plm_v p (hl_lcm_upto n)).
      { apply NatLe_drop. apply (plq_v_mono p m (hl_lcm_upto n));
          [lia | exact (NatLe_drop _ _ (plq_lcm_pos n)) |].
        apply (hl_lcm_divide_all n m Hm Hmn). }
      rewrite <- Hsplit. apply plm_dvd_mul_coprime.
      { apply (Nat.divide_trans (p ^ plm_v p m)
                 (p ^ plm_v p (hl_lcm_upto n))).
        { apply plq_pow_le_dvd. exact Hpwn. }
        { apply (pen_fold_in_divide (p ^ plm_v p (hl_lcm_upto n))).
          apply (in_map (fun p0 : nat => p0 ^ plm_v p0 (hl_lcm_upto n))).
          apply (proj2 (pen_in_primes_upto p n)). split.
          - split; [lia | exact Hpdiv].
          - lia. } }
      { exact IHm2. }
      { exact Hgw. }
Qed.

(* Main theorem of the second limb: L(n) divides the product of prime *)
(* powers (closed off the shelf by h3_lcm_fold_divide: if every number *)
(* in 1..n divides D, then L(n) divides D). *)
Theorem plq_lcm_dvd_powprod : forall n : nat,
  Nat.divide (hl_lcm_upto n)
    (fold_right Nat.mul 1
       (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
            (pen_primes_upto n))).
Proof.
  intro n. apply (h3_lcm_fold_divide n). intros m Hm Hmn.
  apply (plq_num_dvd_powprod n m Hmn Hm n Hmn).
Qed.

(* ---- Section 4. Main theorem: the full identity, carried by hl_id at *)
(* the Set level ---- *)

Theorem pr_lcm_eq_decomp : forall n : nat,
  hl_id (hl_lcm_upto n)
    (fold_right Nat.mul 1
       (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
            (pen_primes_upto n))).
Proof.
  intro n.
  assert (Hsup : Nat.divide
    (fold_right Nat.mul 1
       (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
            (pen_primes_upto n)))
    (hl_lcm_upto n)) by apply plq_powprod_dvd_lcm.
  assert (Hsub : Nat.divide (hl_lcm_upto n)
    (fold_right Nat.mul 1
       (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
            (pen_primes_upto n)))) by apply plq_lcm_dvd_powprod.
  assert (HP : 1 <= fold_right Nat.mul 1
    (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
         (pen_primes_upto n))).
  { apply pen_fold_mul_pos. intros x Hx.
    apply in_map_iff in Hx. destruct Hx as [p [Hpv Hpt]].
    rewrite <- Hpv.
    destruct (proj1 (pen_in_primes_upto p n) Hpt) as [Hpp _].
    destruct Hpp as [Hp2 _].
    pose proof (Nat.pow_nonzero p (plm_v p (hl_lcm_upto n))).
    lia. }
  assert (HL : 1 <= hl_lcm_upto n) by exact (NatLe_drop _ _ (plq_lcm_pos n)).
  assert (E : hl_lcm_upto n = fold_right Nat.mul 1
    (map (fun p : nat => p ^ plm_v p (hl_lcm_upto n))
         (pen_primes_upto n))).
  { apply Nat.le_antisymm.
    - apply Nat.divide_pos_le; [lia | exact Hsub].
    - apply Nat.divide_pos_le; [lia | exact Hsup]. }
  rewrite <- E. apply hl_idrefl.
Qed.

(* ---- Section 5. Numerical smoke tests (small instances computed directly *)
(* by vm_compute: the two closed nat terms agree pointwise) ---- *)

Lemma plq_smoke_0 : Id (hl_lcm_upto 0)
  (fold_right Nat.mul 1
    (map (fun p : nat => p ^ plm_v p (hl_lcm_upto 0))
         (pen_primes_upto 0))).
Proof. vm_compute. apply id_refl. Qed.

Lemma plq_smoke_1 : Id (hl_lcm_upto 1)
  (fold_right Nat.mul 1
    (map (fun p : nat => p ^ plm_v p (hl_lcm_upto 1))
         (pen_primes_upto 1))).
Proof. vm_compute. apply id_refl. Qed.

Lemma plq_smoke_2 : Id (hl_lcm_upto 2)
  (fold_right Nat.mul 1
    (map (fun p : nat => p ^ plm_v p (hl_lcm_upto 2))
         (pen_primes_upto 2))).
Proof. vm_compute. apply id_refl. Qed.

Lemma plq_smoke_4 : Id (hl_lcm_upto 4)
  (fold_right Nat.mul 1
    (map (fun p : nat => p ^ plm_v p (hl_lcm_upto 4))
         (pen_primes_upto 4))).
Proof. vm_compute. apply id_refl. Qed.

(* Upper bound on instances: the three recursive calls in the body of *)
(* plm_vmax share no subcomputations, so vm_compute doubles the work at *)
(* every level -- cost exponential in the fuel k (measured: plm_v 2 60 *)
(* ran past 25 s under a timeout, while plm_v 2 12 is instantaneous). *)
(* The smoke tests therefore stop at n <= 4 (L(4) = 12, so the deepest *)
(* exponent tree has 2 ^ 12 leaves); from n = 6 upward, L(6) = 60 *)
(* exceeds any reasonable evaluation budget. The main theorem holds for *)
(* every n through the proof alone (no computation inside proofs); *)
(* large instances belong to the extraction side. *)

(* ---- Section 6. Assumption audit (Print Assumptions evidence) ---- *)

Print Assumptions plq_pow_le_dvd.
Print Assumptions plq_lcm_pos.
Print Assumptions plq_gcd_1_of_nondvd.
Print Assumptions plq_nodup_app.
Print Assumptions plq_pen_nodup.
Print Assumptions plq_vmax_dvd_le.
Print Assumptions plq_v_dvd_le.
Print Assumptions plq_v_mono.
Print Assumptions plq_powprod_dvd.
Print Assumptions plq_powprod_dvd_lcm.
Print Assumptions plq_num_dvd_powprod.
Print Assumptions plq_lcm_dvd_powprod.
Print Assumptions pr_lcm_eq_decomp.
