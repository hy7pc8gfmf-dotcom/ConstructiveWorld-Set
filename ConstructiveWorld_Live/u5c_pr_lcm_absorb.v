(* ConstructiveWorld-Set -- Hanson lcm valuation faces with the per-prime-power annulus absorption step. *)

(** * u5c_pr_lcm_absorb: p-adic valuations of lcm(1..n) and the annulus absorption step.

    Mission.  Hanson route groundwork: the p-adic valuation characterization
      of the lcm [L n = hl_lcm_upto n] and the per-prime-power absorption
      step for the half splitting of [L (2 * m)]; Piece A carries
      [plw_v_lcm_upto_id] with the pointwise spec [plw_pow_dvd_lcm_iff],
      Piece B carries [plw_annulus_pow_dvd] and [plw_lcm2m_v_le_carry].

    Dependencies.  Stdlib [Arith.Arith], [Arith.Factorial], [Lia];
      requires [Hanson3Pow], [HansonLcm], [abl_Pr_core_01],
      [abl_Pr_euclid_03], [abl_Pr_lcmdecomp_04], plus the [S01_BaseRing]
      carrier names [Id], [id_refl], [NatLe], [NatLe_lift], [NatLe_drop],
      [And] (the [pr_prime] premise face).

    References.  This development, u5c_pr_lcm_absorb.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  Per-item carrier disclosure: [plw_maxpow] is a nat-valued
      [Fixpoint] (Set face) and [plw_v_lcm_upto_id] is carried by the Set-level
      [hl_id] of HansonLcm, so both extract with no [Obj.magic] and no erasure;
      the remaining named statements (divisibility and valuation faces,
      support lemmas, smoke equations) are Prop faces for reasoning only;
      [Print Assumptions] reports all thirteen audited names [Closed under
      the global context] and [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" u5c_pr_lcm_absorb.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import Arith.Arith Arith.Factorial Lia.
Require Import S01_BaseRing (Id, id_refl, NatLe, NatLe_lift, NatLe_drop, And).
Require Import HansonLcm.
Require Import Hanson3Pow.
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.

(* ================= Section 0. Assorted lemmas ================= *)

(* Powers divide along exponents: e <= f gives p ^ e divides p ^ f for 1 <= p. *)
Lemma plw_pow_le_dvd : forall p e f : nat,
  1 <= p -> e <= f -> Nat.divide (p ^ e) (p ^ f).
Proof.
  intros p e f Hp Hef. exists (p ^ (f - e)).
  rewrite <- Nat.pow_add_r. f_equal. lia.
Qed.

(* Divisibility is multiplicative in both factors: a divides b and c divides d give a * c divides b * d. *)
Lemma plw_dvd_mul_mono : forall a b c d : nat,
  Nat.divide a b -> Nat.divide c d -> Nat.divide (a * c) (b * d).
Proof.
  intros a b c d [q Hq] [r Hr]. exists (q * r).
  rewrite Hq, Hr. ring.
Qed.

(* Left cancellation for multiplication, packaged from the Stdlib iff [Nat.mul_cancel_l]. *)
Lemma plw_mul_cancel_l : forall a x y : nat,
  a <> 0 -> a * x = a * y -> x = y.
Proof. intros a x y Ha H. exact (proj1 (Nat.mul_cancel_l x y a Ha) H). Qed.

(* Powers of a positive base stay positive: 1 <= p gives 1 <= p ^ e. *)
Lemma plw_pow_pos : forall p e : nat,
  1 <= p -> 1 <= p ^ e.
Proof.
  intros p e Hp.
  apply Nat.neq_0_lt_0. intro Hz.
  assert (Hpnz : p <> 0) by lia.
  pose proof (Nat.pow_nonzero p e Hpnz).
  lia.
Qed.

(* Strict monotonicity of powers: e < f gives p ^ e < p ^ f for 2 <= p, closed
   by stepping through [Nat.pow_le_mono_r] rather than quoting the
   [pow_lt_mono_r] signature. *)
Lemma plw_pow_lt_mono : forall p e f : nat,
  2 <= p -> e < f -> p ^ e < p ^ f.
Proof.
  intros p e f Hp Hlt.
  assert (Hs : S e <= f) by lia.
  assert (Hle : p ^ S e <= p ^ f)
    by (apply Nat.pow_le_mono_r; lia).
  rewrite Nat.pow_succ_r' in Hle.
  assert (H1 : 1 <= p ^ e) by (apply plw_pow_pos; lia).
  assert (Hstep : 2 * p ^ e <= p * p ^ e)
    by (apply Nat.mul_le_mono_r; lia).
  lia.
Qed.

(* ================= Section 1. Valuation characterization core for [plm_v] ================= *)

(* Upper arm: e <= plm_v p k gives p ^ e divides k, by trimming the exponent
   in [plm_v_dvd]. *)
Lemma plw_v_dvd_le : forall p k e : nat,
  1 <= p ->
  Nat.divide (p ^ plm_v p k) k -> e <= plm_v p k ->
  Nat.divide (p ^ e) k.
Proof.
  intros p k e Hp Hd Hle.
  apply (Nat.divide_trans (p ^ e) (p ^ plm_v p k) k).
  - apply plw_pow_le_dvd; lia.
  - exact Hd.
Qed.

(* Lower arm: p ^ e divides k with 1 <= k and 1 < p gives e <= plm_v p k,
   since an overshooting power p ^ (S v) dividing k would break maximality
   of [plm_v]. *)
Lemma plw_v_le_dvd : forall p k e : nat,
  1 < p -> 1 <= k -> Nat.divide (p ^ e) k -> e <= plm_v p k.
Proof.
  intros p k e Hp Hk Hd.
  destruct (le_lt_dec e (plm_v p k)) as [Hle | Hlt].
  - exact Hle.
  - exfalso.
    apply (plm_v_max p k Hp Hk).
    apply (Nat.divide_trans (p ^ S (plm_v p k)) (p ^ e) k).
    + apply plw_pow_le_dvd; lia.
    + exact Hd.
Qed.

(* The full characterization for 1 <= k: p ^ e divides k iff e <= plm_v p k. *)
Lemma plw_v_char : forall p k e : nat,
  1 < p -> 1 <= k ->
  Nat.divide (p ^ e) k <-> e <= plm_v p k.
Proof.
  intros p k e Hp Hk. split.
  - intro Hd. exact (plw_v_le_dvd p k e Hp Hk Hd).
  - intro Hle. apply (plw_v_dvd_le p k e).
    + lia.
    + apply plm_v_dvd.
    + exact Hle.
Qed.

(* Valuation fixed point on prime powers: plm_v p (p ^ e) = e for 1 < p.
   The <= arm reads p ^ v dividing p ^ e as p ^ v <= p ^ e hence v <= e;
   for the >= arm, v < e would let p ^ (S v) divide p ^ e and break
   maximality. *)
Lemma plw_pow_v_eq : forall p e : nat,
  1 < p -> plm_v p (p ^ e) = e.
Proof.
  intros p e Hp.
  assert (Hk : 1 <= p ^ e) by (apply plw_pow_pos; lia).
  apply Nat.le_antisymm.
  - assert (Hdvd : Nat.divide (p ^ plm_v p (p ^ e)) (p ^ e))
      by apply plm_v_dvd.
    assert (Hle : p ^ plm_v p (p ^ e) <= p ^ e)
      by (apply Nat.divide_pos_le; [lia | exact Hdvd]).
    destruct (le_lt_dec (plm_v p (p ^ e)) e) as [| Hlt].
    + lia.
    + exfalso.
      assert (Hlt2 : p ^ e < p ^ plm_v p (p ^ e))
        by (apply (plw_pow_lt_mono p e (plm_v p (p ^ e))); [lia | lia]).
      lia.
  - destruct (le_lt_dec e (plm_v p (p ^ e))) as [| Hlt].
    + lia.
    + exfalso.
      apply (plm_v_max p (p ^ e) Hp Hk).
      apply (plw_pow_le_dvd p (S (plm_v p (p ^ e))) e); lia.
Qed.

(* ================= Section 2. Valuation calculus for products, gcds and lcms over primes ================= *)

(* The tail factor escapes p: a = p ^ v * a' with p ^ (S v) not dividing a
   gives p not dividing a'. *)
Lemma plw_tail_nop : forall p v a t : nat,
  1 < p -> a = p ^ v * t ->
  (Nat.divide (p ^ S v) a -> False) ->
  (Nat.divide p t -> False).
Proof.
  intros p v a t Hp Ha Hceil [u Hu].
  apply Hceil. exists u. rewrite Ha, Hu.
  rewrite Nat.pow_succ_r'. ring.
Qed.

(* Valuations add over products: plm_v p (a * b) = plm_v p a + plm_v p b
   for p prime and a, b >= 1. *)
Lemma plw_v_mul : forall p a b : nat,
  pr_prime p -> 1 <= a -> 1 <= b ->
  plm_v p (a * b) = plm_v p a + plm_v p b.
Proof.
  intros p a b Hpp Ha Hb.
  pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  pose proof (snd Hpp) as Hpd.
  assert (Hp1 : 1 < p) by lia.
  assert (Hab : 1 <= a * b) by (apply (Nat.mul_le_mono 1 a 1 b); lia).
  apply Nat.le_antisymm.
  - (* The <= direction: p ^ v_ab divides a * b; after peeling
       p ^ va * p ^ vb the remainder carries no factor p, and an excess
       v_ab would put p into that remainder, breaking maximality on a or
       b through the primality split. *)
    assert (Hd : Nat.divide (p ^ plm_v p (a * b)) (a * b))
      by apply plm_v_dvd.
    destruct Hd as [q Hq].
    destruct (plm_v_dvd p a) as [a' Ha'].
    destruct (plm_v_dvd p b) as [b' Hb'].
    assert (Ha'f : a = p ^ plm_v p a * a') by (rewrite Ha' at 1; ring).
    assert (Hb'f : b = p ^ plm_v p b * b') by (rewrite Hb' at 1; ring).
    assert (Hta : Nat.divide p a' -> False).
    { apply (plw_tail_nop p (plm_v p a) a a'); [lia | exact Ha'f |].
      intro Hd2. exact (plm_v_max p a Hp1 Ha Hd2). }
    assert (Htb : Nat.divide p b' -> False).
    { apply (plw_tail_nop p (plm_v p b) b b'); [lia | exact Hb'f |].
      intro Hd2. exact (plm_v_max p b Hp1 Hb Hd2). }
    destruct (le_lt_dec (plm_v p (a * b))
                (plm_v p a + plm_v p b)) as [| Hlt].
    + lia.
    + exfalso.
      (* p ^ (S (va + vb)) divides a * b, transferred from
         v_ab >= S (va + vb). *)
      assert (Hdd : Nat.divide (p ^ S (plm_v p a + plm_v p b)) (a * b)).
      { apply (Nat.divide_trans (p ^ S (plm_v p a + plm_v p b))
                  (p ^ plm_v p (a * b)) (a * b)).
        - apply plw_pow_le_dvd; lia.
        - apply plm_v_dvd. }
      destruct Hdd as [u Hu].
      (* Peeling equation: p ^ (va + vb) * (a' * b')
         = p ^ (S (va + vb)) * u; cancelling leaves p dividing a' * b'. *)
      assert (Hab2 : a * b
                     = p ^ (plm_v p a + plm_v p b) * (a' * b')).
      { rewrite Ha' at 1. rewrite Hb' at 1. rewrite Nat.pow_add_r. ring. }
      assert (Hq2 : p ^ (plm_v p a + plm_v p b) * (a' * b')
                    = p ^ (plm_v p a + plm_v p b) * (p * u)).
      { rewrite <- Hab2, Hu, Nat.pow_succ_r'. ring. }
      assert (Hcancel : a' * b' = p * u).
      { apply (plw_mul_cancel_l (p ^ (plm_v p a + plm_v p b))
                 (a' * b') (p * u)).
        - pose proof (plw_pow_pos p (plm_v p a + plm_v p b) ltac:(lia)).
          lia.
        - exact Hq2. }
      assert (Hdv : Nat.divide p (a' * b')).
      { exists u. rewrite Hcancel. ring. }
      destruct (plm_prime_dvd_mul p a' b' Hpp Hdv)
        as [Hda | Hdb].
      * exact (Hta Hda).
      * exact (Htb Hdb).
  - (* The >= direction: p ^ va divides a and p ^ vb divides b give
       p ^ (va + vb) dividing a * b. *)
    apply (plw_v_le_dvd p (a * b) (plm_v p a + plm_v p b) Hp1 Hab).
    rewrite Nat.pow_add_r.
    apply (plw_dvd_mul_mono (p ^ plm_v p a) a (p ^ plm_v p b) b).
    + apply plm_v_dvd.
    + apply plm_v_dvd.
Qed.

(* Valuation of the gcd: plm_v p (Nat.gcd a b) = min for p prime and
   a, b >= 1. *)
Lemma plw_v_gcd : forall p a b : nat,
  pr_prime p -> 1 <= a -> 1 <= b ->
  plm_v p (Nat.gcd a b) = Nat.min (plm_v p a) (plm_v p b).
Proof.
  intros p a b Hpp Ha Hb.
  pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  assert (Hp1 : 1 < p) by lia.
  assert (Hga : 1 <= Nat.gcd a b).
  { apply Nat.neq_0_lt_0. intro Hz.
    assert (Hd : Nat.divide (Nat.gcd a b) a) by apply Nat.gcd_divide_l.
    rewrite Hz in Hd. apply Nat.divide_0_l in Hd. lia. }
  apply Nat.le_antisymm.
  - assert (H1 : plm_v p (Nat.gcd a b) <= plm_v p a).
    { apply (plw_v_le_dvd p a (plm_v p (Nat.gcd a b)) Hp1 Ha).
      apply (Nat.divide_trans (p ^ plm_v p (Nat.gcd a b))
                (Nat.gcd a b) a).
      + apply plm_v_dvd.
      + apply Nat.gcd_divide_l. }
    assert (H2 : plm_v p (Nat.gcd a b) <= plm_v p b).
    { apply (plw_v_le_dvd p b (plm_v p (Nat.gcd a b)) Hp1 Hb).
      apply (Nat.divide_trans (p ^ plm_v p (Nat.gcd a b))
                (Nat.gcd a b) b).
      + apply plm_v_dvd.
      + apply Nat.gcd_divide_r. }
    lia.
  - apply (plw_v_le_dvd p (Nat.gcd a b)
             (Nat.min (plm_v p a) (plm_v p b)) Hp1 Hga).
    apply Nat.gcd_greatest.
    + apply (plw_v_dvd_le p a (Nat.min (plm_v p a) (plm_v p b))).
      * lia.
      * apply plm_v_dvd.
      * apply Nat.le_min_l.
    + apply (plw_v_dvd_le p b (Nat.min (plm_v p a) (plm_v p b))).
      * lia.
      * apply plm_v_dvd.
      * apply Nat.le_min_r.
Qed.

(* lcm * gcd = a * b, computed directly on the Stdlib unfolding
   lcm a b = a * (b / gcd a b), zero edges included. *)
Lemma plw_lcm_gcd_mul : forall a b : nat,
  Nat.lcm a b * Nat.gcd a b = a * b.
Proof.
  intros a b.
  unfold Nat.lcm.
  destruct (Nat.eq_dec (Nat.gcd a b) 0) as [Ez | Nz].
  - assert (Ha : a = 0).
    { assert (Hd : Nat.divide (Nat.gcd a b) a) by apply Nat.gcd_divide_l.
      rewrite Ez in Hd. apply Nat.divide_0_l in Hd. exact Hd. }
    assert (Hb : b = 0).
    { assert (Hd : Nat.divide (Nat.gcd a b) b) by apply Nat.gcd_divide_r.
      rewrite Ez in Hd. apply Nat.divide_0_l in Hd. exact Hd. }
    rewrite Ez, Ha, Hb. reflexivity.
  - assert (Hb0 : b = Nat.gcd a b * (b / Nat.gcd a b)).
    { pose proof (Nat.div_mod_eq b (Nat.gcd a b)) as Hdm.
      assert (Hm0 : b mod Nat.gcd a b = 0).
      { apply (proj2 (Nat.mod_divide b (Nat.gcd a b) Nz)).
        apply Nat.gcd_divide_r. }
      rewrite Hm0, Nat.add_0_r in Hdm. exact Hdm. }
    rewrite <- (Nat.mul_assoc a (b / Nat.gcd a b) (Nat.gcd a b)).
    rewrite (Nat.mul_comm (b / Nat.gcd a b) (Nat.gcd a b)).
    rewrite <- Hb0. reflexivity.
Qed.

(* Positivity of the lcm for 1 <= a and 1 <= b, by contradiction through
   lcm * gcd = a * b. *)
Lemma plw_lcm_pos_gen : forall a b : nat,
  1 <= a -> 1 <= b -> 1 <= Nat.lcm a b.
Proof.
  intros a b Ha Hb.
  assert (Hab : 1 <= a * b) by (apply (Nat.mul_le_mono 1 a 1 b); lia).
  apply Nat.neq_0_lt_0. intro Hz.
  pose proof (plw_lcm_gcd_mul a b) as Hmul.
  rewrite Hz, Nat.mul_0_l in Hmul.
  lia.
Qed.

(* Valuation of the lcm: plm_v p (Nat.lcm a b) = max for p prime and
   a, b >= 1.  The equation lcm * gcd = a * b gives
   v(lcm) + v(gcd) = v(a) + v(b), and v(gcd) = min forces v(lcm) = max. *)
Lemma plw_v_lcm : forall p a b : nat,
  pr_prime p -> 1 <= a -> 1 <= b ->
  plm_v p (Nat.lcm a b) = Nat.max (plm_v p a) (plm_v p b).
Proof.
  intros p a b Hpp Ha Hb.
  pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  pose proof (snd Hpp) as Hpd.
  assert (Hp1 : 1 < p) by lia.
  assert (Hg1 : 1 <= Nat.gcd a b).
  { apply Nat.neq_0_lt_0. intro Hz.
    assert (Hd : Nat.divide (Nat.gcd a b) a) by apply Nat.gcd_divide_l.
    rewrite Hz in Hd. apply Nat.divide_0_l in Hd. lia. }
  assert (Hl1 : 1 <= Nat.lcm a b)
    by (apply plw_lcm_pos_gen; assumption).
  assert (Hvl : plm_v p (Nat.lcm a b) + plm_v p (Nat.gcd a b)
                = plm_v p a + plm_v p b).
  { rewrite <- (plw_v_mul p (Nat.lcm a b) (Nat.gcd a b) Hpp Hl1 Hg1).
    rewrite (plw_lcm_gcd_mul a b).
    apply (plw_v_mul p a b Hpp Ha Hb). }
  rewrite (plw_v_gcd p a b Hpp Ha Hb) in Hvl.
  lia.
Qed.

(* ================= Section 3. Piece A: the p-adic valuation characterization of L(n), the Hanson decomposition valuation face ================= *)

(* Positivity of the folded lcm: 1 <= L n, by induction on the unfolding
   lcm a b = a * (b / gcd a b). *)
Lemma plw_lcm_pos : forall n : nat, 1 <= hl_lcm_upto n.
Proof.
  induction n as [| n IH].
  - cbn [hl_lcm_upto]. lia.
  - cbn [hl_lcm_upto].
    apply plw_lcm_pos_gen; [exact IH | lia].
Qed.

(* Valuation of the folding step: v_p (L (S n)) = max (v_p (L n)) (v_p (S n))
   for p prime. *)
Lemma plw_v_lcm_upto_S : forall p n : nat,
  pr_prime p ->
  plm_v p (hl_lcm_upto (S n))
  = Nat.max (plm_v p (hl_lcm_upto n)) (plm_v p (S n)).
Proof.
  intros p n Hpp. cbn [hl_lcm_upto].
  apply (plw_v_lcm p (hl_lcm_upto n) (S n) Hpp).
  - apply plw_lcm_pos.
  - lia.
Qed.

(* Piece A', the divisibility characterization of L: p ^ w divides L n iff
   p ^ w <= n, for p prime and 1 <= n.  The if arm is [hl_lcm_divide_all],
   since p ^ w is itself a member of 1..n; the only-if arm goes by
   induction, splitting at the step w <= max (v (L m)) (v (S m)):
   w <= v (L m) returns to the induction premise, and w <= v (S m)
   comes out directly. *)
Lemma plw_pow_dvd_lcm_iff : forall p n w : nat,
  pr_prime p -> 1 <= n ->
  Nat.divide (p ^ w) (hl_lcm_upto n) <-> p ^ w <= n.
Proof.
  intros p n. induction n as [| m IH]; intros w Hpp Hn.
  - exfalso. lia.
  - pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
    pose proof (snd Hpp) as Hpd.
    assert (Hp1 : 1 < p) by lia.
    assert (Hpw : 1 <= p ^ w) by (apply plw_pow_pos; lia).
    split.
    + intro Hd.
      apply (plw_v_le_dvd p (hl_lcm_upto (S m)) w Hp1
               (plw_lcm_pos (S m))) in Hd.
      assert (Hdmax : w <= Nat.max (plm_v p (hl_lcm_upto m))
                        (plm_v p (S m))).
      { rewrite <- (plw_v_lcm_upto_S p m Hpp). exact Hd. }
      destruct (le_lt_dec w (plm_v p (hl_lcm_upto m))) as [Hc | Hc].
      * (* w <= v (L m): back to the induction premise. *)
        assert (Hdm : Nat.divide (p ^ w) (hl_lcm_upto m))
          by (apply (plw_v_dvd_le p (hl_lcm_upto m) w);
              [lia | apply plm_v_dvd | exact Hc]).
        destruct m as [| m'].
        -- simpl in Hdm.
           apply Nat.divide_1_r in Hdm.
           rewrite Hdm. lia.
        -- pose proof (proj1 (IH w Hpp ltac:(lia)) Hdm) as Hle.
           lia.
      * (* w <= v (S m): p ^ w divides S m directly. *)
        assert (Hds : Nat.divide (p ^ w) (S m))
          by (apply (plw_v_dvd_le p (S m) w);
              [lia | apply plm_v_dvd | lia]).
        apply Nat.divide_pos_le; [lia | exact Hds].
    + intro Hle.
      apply (hl_lcm_divide_all (S m) (p ^ w)); [exact Hpw | exact Hle].
Qed.

(* The climbing machine: plw_maxpow p n is the largest exponent w with
   p ^ w <= n, as a first-order nat [Fixpoint].  The bound n is safe
   because p ^ w <= n forces w <= n; the shape mirrors [plm_vmax]. *)
Fixpoint plw_maxpow (p n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => if Nat.leb (p ^ S (plw_maxpow p m)) (S m)
           then S (plw_maxpow p m)
           else plw_maxpow p m
  end.

(* First arm of the climb: p ^ (plw_maxpow p n) <= n unless n = 0. *)
Lemma plw_maxpow_dvd_upto : forall p n : nat,
  p ^ plw_maxpow p n <= n \/ n = 0.
Proof.
  intros p n. induction n as [| m IH].
  - right. reflexivity.
  - change (plw_maxpow p (S m))
      with (if Nat.leb (p ^ S (plw_maxpow p m)) (S m)
            then S (plw_maxpow p m) else plw_maxpow p m).
    destruct (Nat.leb (p ^ S (plw_maxpow p m)) (S m)) eqn:Eb.
    + left. apply Nat.leb_le in Eb. exact Eb.
    + apply Nat.leb_gt in Eb.
      destruct IH as [Hle | Hm0].
      * change (if false then S (plw_maxpow p m)
                else plw_maxpow p m)
          with (plw_maxpow p m).
        left. lia.
      * subst m. change (plw_maxpow p 0) with 0.
        change (if false then S 0 else 0) with 0.
        rewrite Nat.pow_0_r. left. lia.
Qed.

(* Second arm of the climb: n < p ^ (S (plw_maxpow p n)) for 1 < p, so the
   climb never overshoots. *)
Lemma plw_maxpow_ceil : forall p n : nat,
  1 < p -> n < p ^ S (plw_maxpow p n).
Proof.
  intros p n Hp. induction n as [| m IH].
  - cbn [plw_maxpow]. rewrite Nat.pow_succ_r', Nat.pow_0_r. lia.
  - change (plw_maxpow p (S m))
      with (if Nat.leb (p ^ S (plw_maxpow p m)) (S m)
            then S (plw_maxpow p m) else plw_maxpow p m).
    destruct (Nat.leb (p ^ S (plw_maxpow p m)) (S m)) eqn:Eb.
    + apply Nat.leb_le in Eb.
      change (if true then S (plw_maxpow p m) else plw_maxpow p m)
        with (S (plw_maxpow p m)).
      assert (Hsm : m < p ^ S (plw_maxpow p m)) by exact IH.
      assert (Hge : p ^ S (plw_maxpow p m) * 2
                    <= p ^ S (plw_maxpow p m) * p)
        by (apply Nat.mul_le_mono_l; lia).
      assert (Hstep : p ^ S (S (plw_maxpow p m))
                      = p ^ S (plw_maxpow p m) * p)
        by (rewrite Nat.pow_succ_r'; ring).
      rewrite Hstep. lia.
    + apply Nat.leb_gt in Eb. exact Eb.
Qed.

(* Assembling the characterization: v_p (L n) = plw_maxpow p n for p prime.
   At n = 0 both sides are zero; for n >= 1 the two antisymmetry arms
   squeeze the values together through the iff uniqueness and the strict
   monotonicity of powers. *)
Lemma plw_v_lcm_upto : forall p n : nat,
  pr_prime p -> plm_v p (hl_lcm_upto n) = plw_maxpow p n.
Proof.
  intros p n Hpp.
  pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  pose proof (snd Hpp) as Hpd.
  assert (Hp1 : 1 < p) by lia.
  assert (Hpos : 1 <= hl_lcm_upto n) by apply plw_lcm_pos.
  destruct n as [| m].
  - cbn [hl_lcm_upto plw_maxpow].
    assert (Hv : plm_v p 1 = 0).
    { destruct (plm_v p 1) as [| v'] eqn:Ev.
      - reflexivity.
      - exfalso.
        destruct (plm_v_dvd p 1) as [t Ht].
        rewrite Ev in Ht.
        assert (Hge : 2 <= p ^ S v')
          by (apply Nat.le_trans with (p ^ 1);
              [rewrite Nat.pow_1_r; lia | apply Nat.pow_le_mono_r; lia]).
        assert (Hle : p ^ S v' <= 1)
          by (apply Nat.divide_pos_le;
              [lia | exact (ex_intro _ t Ht)]).
        lia. }
    rewrite Hv. reflexivity.
  - assert (Hn : 1 <= S m) by lia.
    pose proof (plw_maxpow_dvd_upto p (S m)) as Hdu.
    destruct Hdu as [Hdu | Hm0].
    2:{ exfalso. lia. }
    pose proof (plw_maxpow_ceil p (S m) Hp1) as Hcl.
    assert (Hvd : p ^ plm_v p (hl_lcm_upto (S m)) <= S m).
    { apply (proj1 (plw_pow_dvd_lcm_iff p (S m)
                    (plm_v p (hl_lcm_upto (S m))) Hpp Hn)).
      apply plm_v_dvd. }
    assert (Hvc : p ^ S (plm_v p (hl_lcm_upto (S m))) <= S m -> False).
    { intro Hle2.
      apply (plm_v_max p (hl_lcm_upto (S m)) Hp1 Hpos).
      exact (proj2 (plw_pow_dvd_lcm_iff p (S m)
              (S (plm_v p (hl_lcm_upto (S m)))) Hpp Hn) Hle2). }
    apply Nat.le_antisymm.
    + destruct (le_lt_dec (plm_v p (hl_lcm_upto (S m)))
                  (plw_maxpow p (S m))) as [Hle3 | Hgt].
      * exact Hle3.
      * exfalso.
        assert (Hmono : p ^ S (plw_maxpow p (S m))
                        <= p ^ plm_v p (hl_lcm_upto (S m)))
          by (apply Nat.pow_le_mono_r; lia).
        lia.
    + destruct (le_lt_dec (plw_maxpow p (S m))
                  (plm_v p (hl_lcm_upto (S m)))) as [Hle3 | Hgt].
      * exact Hle3.
      * exfalso.
        assert (Hmono : p ^ S (plm_v p (hl_lcm_upto (S m)))
                        <= p ^ plw_maxpow p (S m))
          by (apply Nat.pow_le_mono_r; lia).
        apply Hvc. lia.
Qed.

(* Piece A on the Set face: the p-adic valuation of L n equals
   plw_maxpow p n, carried as an [hl_id] equation: the valuation face of
   the Hanson decomposition L(n) = product over p <= n of
   p ^ max {w : p ^ w <= n}, with the exponent slot lifted to the explicit
   [plw_maxpow] form after the host statement [pr_lcm_eq_decomp]. *)
Theorem plw_v_lcm_upto_id : forall p n : nat,
  pr_prime p -> hl_id (plm_v p (hl_lcm_upto n)) (plw_maxpow p n).
Proof.
  intros p n Hpp.
  rewrite (plw_v_lcm_upto p n Hpp). apply hl_idrefl.
Qed.

(* ================= Section 4. Piece B: the per-prime-power annulus absorption step ================= *)

(* A prime above m does not divide fact m: p prime and m < p give p not
   dividing fact m, since p dividing the factorial would put p into some
   factor <= m < p against primality; the induction step splits along the
   product rule for prime divisors. *)
Lemma plw_nodvd_fact : forall m p : nat,
  pr_prime p -> m < p -> (Nat.divide p (fact m) -> False).
Proof.
  intros m p Hpp.
  pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  induction m as [| m IH]; intros Hlt Hd.
  - cbn [fact] in Hd. apply Nat.divide_1_r in Hd. lia.
  - cbn [fact] in Hd. rewrite Nat.mul_comm in Hd.
    destruct (plm_prime_dvd_mul p (fact m) (S m) Hpp Hd) as [H1 | H2].
    + exact (IH ltac:(lia) H1).
    + assert (Hle : p <= S m)
        by (apply Nat.divide_pos_le; [lia | exact H2]).
      lia.
Qed.

(* Coprimality from non-divisibility: p prime and p not dividing x give
   Nat.gcd p x = 1, via the size trichotomy on the gcd. *)
Lemma plw_gcd_1_of_nodvd : forall p x : nat,
  pr_prime p -> (Nat.divide p x -> False) -> Nat.gcd p x = 1.
Proof.
  intros p x Hpp Hnd.
  pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  pose proof (snd Hpp) as Hpd.
  destruct (Nat.eq_dec (Nat.gcd p x) 1) as [E1 | NE1].
  - exact E1.
  - exfalso.
    assert (Hgp : Nat.divide (Nat.gcd p x) p) by apply Nat.gcd_divide_l.
    assert (Hgm : Nat.divide (Nat.gcd p x) x) by apply Nat.gcd_divide_r.
    assert (Hgp0 : 1 <= Nat.gcd p x).
    { apply Nat.neq_0_lt_0. intro Hz.
      rewrite Hz in Hgp.
      apply Nat.divide_0_l in Hgp. lia. }
    assert (Hle : Nat.gcd p x <= p)
      by (apply Nat.divide_pos_le; [lia | exact Hgp]).
    remember (Nat.gcd p x) as g eqn:Eg.
    destruct g as [| [| g']].
    + apply Nat.divide_0_l in Hgp. lia.
    + apply NE1. reflexivity.
    + assert (Hg2 : Nat.gcd p x = p).
      { destruct (Nat.eq_dec (Nat.gcd p x) p) as [Eg2 | NEg2].
        - exact Eg2.
        - exfalso.
          assert (Hlt2 : S (S g') < p).
          { destruct (le_lt_dec p (S (S g'))) as [Hge | Hlt2].
            - exfalso. apply NEg2. apply Nat.le_antisymm;
                [rewrite <- Eg; exact Hle | rewrite <- Eg; exact Hge].
            - exact Hlt2. }
          assert (Hgf : Id (Nat.eqb (p mod (S (S g'))) 0) false)
            by (apply (Hpd (S (S g')));
                [apply NatLe_lift; lia | apply NatLe_lift; lia]).
          assert (Hgfe : Nat.eqb (p mod (S (S g'))) 0 = false)
            by (exact (match Hgf in (Id _ z)
                       return (Nat.eqb (p mod (S (S g'))) 0 = z)
                       with id_refl => eq_refl end)).
          assert (Hg1 : 1 <= S (S g')) by lia.
          pose proof (pr_dvd_mod0 (S (S g')) p Hg1 Hgp) as Hmod0.
          assert (Hmode : p mod (S (S g')) = 0)
            by (exact (match Hmod0 in (Id _ z)
                       return (p mod (S (S g')) = z)
                       with id_refl => eq_refl end)).
          rewrite Hmode in Hgfe. simpl in Hgfe. discriminate. }
      rewrite Eg, Hg2 in Hgm. apply Hnd. exact Hgm.
Qed.

(* Annulus absorption at the prime slot w = 1: a prime m < p <= 2m divides
   C(2m, m).  No Legendre counting is needed: p is a literal factor of the
   product over m+1..2m by [h3_prod_divide], p > m gives p not dividing
   fact m by [plw_nodvd_fact], and [plm_gauss] absorbs the coprime
   factorial into the binomial. *)
Lemma plw_annulus_prime_dvd_binom : forall m p : nat,
  pr_prime p -> m < p -> p <= 2 * m ->
  Nat.divide p (hl_binom (2 * m) m).
Proof.
  intros m p Hpp Hlt Hle.
  replace (2 * m) with (m + m) by lia.
  assert (Hprod : Nat.divide p (h3_prod_from (S m) m)).
  { apply (h3_prod_divide m (S m) p); lia. }
  rewrite (h3_prod_binom_fact m m) in Hprod.
  apply (plm_gauss p (fact m)).
  - apply (plw_gcd_1_of_nodvd p (fact m) Hpp).
    intro Hd. exact (plw_nodvd_fact m p Hpp Hlt Hd).
  - rewrite Nat.mul_comm. exact Hprod.
Qed.

(* Piece B, the per-prime-power annulus absorption step: a prime power
   p ^ w in the annulus (m, 2m] divides C(2m, m) * L m * p.  The case
   w = 0 is the unit; the case w = 1 is the prime slot of the annulus by
   [plw_annulus_prime_dvd_binom]; for w >= 2 the budget p ^ (w-1) <= m,
   from p ^ (w-1) * 2 <= p ^ (w-1) * p = p ^ w <= 2m, places p ^ (w-1)
   into L m by [hl_lcm_divide_all], and the factor p divides p joins by
   multiplicativity. *)
Theorem plw_annulus_pow_dvd : forall p m w : nat,
  pr_prime p -> m < p ^ w -> p ^ w <= 2 * m ->
  Nat.divide (p ^ w) (hl_binom (2 * m) m * hl_lcm_upto m * p).
Proof.
  intros p m w Hpp Hlt Hle.
  pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  pose proof (snd Hpp) as Hpd.
  assert (Hp1 : 1 < p) by lia.
  destruct w as [| w'].
  - rewrite Nat.pow_0_r. apply Nat.divide_1_l.
  - destruct w' as [| w''].
    + (* The case w = 1: the prime slot of the annulus. *)
      rewrite Nat.pow_1_r in Hlt, Hle.
      rewrite Nat.pow_1_r.
      destruct (plw_annulus_prime_dvd_binom m p Hpp Hlt Hle)
        as [q Hq].
      exists (q * (hl_lcm_upto m * p)). rewrite Hq. ring.
    + (* The case w >= 2: the budget p ^ (S w'') absorbs into L m, with
         the factor p dividing p joined alongside. *)
      assert (Heq : p ^ S (S w'') = p ^ S w'' * p)
        by (rewrite Nat.pow_succ_r'; ring).
      rewrite Heq in Hle. rewrite Heq.
      replace (hl_binom (2 * m) m * hl_lcm_upto m * p)
        with (hl_lcm_upto m * (hl_binom (2 * m) m * p)) by ring.
      apply (plw_dvd_mul_mono (p ^ S w'') (hl_lcm_upto m) p
               (hl_binom (2 * m) m * p)).
      * apply (hl_lcm_divide_all m (p ^ S w'')).
        -- assert (Hnz : 0 < p ^ S w'').
           { apply Nat.neq_0_lt_0.
             pose proof (Nat.pow_nonzero p (S w'')). lia. }
           lia.
        -- assert (Hm2 : p ^ S w'' * 2 <= p ^ S w'' * p)
             by (apply Nat.mul_le_mono_l; lia).
           lia.
      * exists (hl_binom (2 * m) m). ring.
Qed.

(* Positivity of binomial coefficients: k <= n gives 1 <= C(n, k), by
   induction along the folding recursion. *)
Lemma plw_binom_pos : forall n k : nat,
  k <= n -> 1 <= hl_binom n k.
Proof.
  intros n. induction n as [| n IH]; intros k Hk.
  - assert (Hk0 : k = 0) by lia. subst k. cbn [hl_binom]. lia.
  - destruct k as [| k'].
    + cbn [hl_binom]. lia.
    + cbn [hl_binom].
      assert (H1 : 1 <= hl_binom n k') by (apply IH; lia).
      lia.
Qed.

(* The pointwise per-prime form of the Hanson half step, assembled directly
   from piece A' and piece B: for each prime p the p-valuation of L(2m)
   does not exceed the p-valuation of C(2m, m) * L m * p, the exact
   pointwise upper bound reachable on the p-adic route.  Merging across
   distinct primes into a single divisibility statement would need
   pairwise coprimality of distinct prime powers and is left open here. *)
Theorem plw_lcm2m_v_le_carry : forall p m : nat,
  pr_prime p -> 1 <= m ->
  plm_v p (hl_lcm_upto (2 * m))
  <= plm_v p (hl_binom (2 * m) m * hl_lcm_upto m * p).
Proof.
  intros p m Hpp Hm.
  pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  pose proof (snd Hpp) as Hpd.
  assert (Hp1 : 1 < p) by lia.
  assert (Hm2 : 1 <= 2 * m) by lia.
  assert (HL : 1 <= hl_lcm_upto m) by apply plw_lcm_pos.
  assert (Hb : 1 <= hl_binom (2 * m) m) by (apply plw_binom_pos; lia).
  assert (HX : 1 <= hl_binom (2 * m) m * hl_lcm_upto m)
    by (apply (Nat.mul_le_mono 1 (hl_binom (2 * m) m) 1
                (hl_lcm_upto m)); lia).
  assert (HY : 1 * p <= hl_binom (2 * m) m * hl_lcm_upto m * p)
    by (apply Nat.mul_le_mono_r; lia).
  assert (Hpos : 1 <= hl_binom (2 * m) m * hl_lcm_upto m * p) by lia.
  assert (HdL : Nat.divide (hl_lcm_upto m)
                  (hl_binom (2 * m) m * hl_lcm_upto m * p)).
  { exists (hl_binom (2 * m) m * p). ring. }
  assert (Hd2 : Nat.divide (p ^ plm_v p (hl_lcm_upto (2 * m)))
                  (hl_lcm_upto (2 * m))) by apply plm_v_dvd.
  pose proof (proj1 (plw_pow_dvd_lcm_iff p (2 * m)
              (plm_v p (hl_lcm_upto (2 * m))) Hpp Hm2)
              Hd2) as Hle2.
  destruct (le_lt_dec (p ^ plm_v p (hl_lcm_upto (2 * m))) m)
    as [Hcase | Hcase].
  - (* p ^ v <= m: the budget absorbs into L m. *)
    assert (HdmL : Nat.divide (p ^ plm_v p (hl_lcm_upto (2 * m)))
                    (hl_lcm_upto m)).
    { apply (proj2 (plw_pow_dvd_lcm_iff p m
              (plm_v p (hl_lcm_upto (2 * m))) Hpp Hm)).
      exact Hcase. }
    apply (plw_v_le_dvd p
            (hl_binom (2 * m) m * hl_lcm_upto m * p));
      [lia | exact Hpos |].
    apply (Nat.divide_trans (p ^ plm_v p (hl_lcm_upto (2 * m)))
              (hl_lcm_upto m)
              (hl_binom (2 * m) m * hl_lcm_upto m * p)).
    + exact HdmL.
    + exact HdL.
  - (* m < p ^ v <= 2m: annulus absorption, piece B. *)
    apply (plw_v_le_dvd p
            (hl_binom (2 * m) m * hl_lcm_upto m * p));
      [lia | exact Hpos |].
    exact (plw_annulus_pow_dvd p m (plm_v p (hl_lcm_upto (2 * m)))
             Hpp Hcase Hle2).
Qed.

(* ================= Section 5. Closed numeric instances (small [plw_maxpow] cases by [vm_compute] with no postulates; large [plm_v] cases are slow and stay off the certification path) ================= *)

Lemma plw_maxpow_smoke_2_6 : plw_maxpow 2 6 = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma plw_maxpow_smoke_2_8 : plw_maxpow 2 8 = 3.
Proof. vm_compute. reflexivity. Qed.

Lemma plw_maxpow_smoke_3_9 : plw_maxpow 3 9 = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma plw_maxpow_smoke_2_1 : plw_maxpow 2 1 = 0.
Proof. vm_compute. reflexivity. Qed.

(* Annulus instance: p = 3, m = 2, so 3 lies in (2, 4] and 3 divides
   C(4, 2) * L 2 * 3 = 6 * 2 * 3. *)
Lemma plw_annulus_smoke_3_2 :
  Nat.eqb ((hl_binom (2 * 2) 2 * hl_lcm_upto 2 * 3) mod 3) 0 = true.
Proof. vm_compute. reflexivity. Qed.

(* ================= Section 6. Closedness audit (the [Print Assumptions] evidence face) ================= *)

Print Assumptions plw_v_char.
Print Assumptions plw_pow_v_eq.
Print Assumptions plw_v_mul.
Print Assumptions plw_v_gcd.
Print Assumptions plw_v_lcm.
Print Assumptions plw_pow_dvd_lcm_iff.
Print Assumptions plw_v_lcm_upto.
Print Assumptions plw_v_lcm_upto_id.
Print Assumptions plw_annulus_prime_dvd_binom.
Print Assumptions plw_annulus_pow_dvd.
Print Assumptions plw_binom_pos.
Print Assumptions plw_lcm2m_v_le_carry.
Print Assumptions plw_maxpow_smoke_2_6.

(* ================= Section 7. Extraction check ([Separate Extraction] of the executable core [plw_maxpow]) ================= *)

From Stdlib Require Import Extraction.
Separate Extraction plw_maxpow.
