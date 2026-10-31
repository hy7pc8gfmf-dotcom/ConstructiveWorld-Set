(* ============================================================ *)
(* abl_Pr_lcmdecomp_04.v - prime-domain lcm decomposition, piece 4 *)
(* Mission. Washed carrier of the piece-4 statement set: the       *)
(*   coprime-product divisibility core (Gauss/Bezout kernel, gcd=1 *)
(*   lemmas, pairwise coprimality, product-divides theorem), the   *)
(*   prime coprimality face, the p-adic valuation face (plm_vmax / *)
(*   plm_v with both spec limbs), prime-factor tools, three Hanson *)
(*   bridges into L(n), and the Euclid new-prime closure           *)
(*   plm_peu_next_outside_lcm. Conclusions are carried by Set      *)
(*   types: equations by Id, order by NatLe, Prop disjunctions by  *)
(*   sumbool braces, conjunctions by the Set-level And, the        *)
(*   valuation spec by a sigT pair; premises keep Prop hypotheses  *)
(*   and negative faces keep the -> False form.                    *)
(* Dependencies. Stdlib (Arith.Arith, List, Bool, Lia);            *)
(*   S01_BaseRing (Id, id_refl, NatLe, NatLe_lift, NatLe_drop,     *)
(*   And); HansonLcm; abl_Pr_core_01; abl_Pr_euclid_03.            *)
(* References. Nat.gcd_unique_alt, Nat.divide_1_r, Nat.gcd_comm,   *)
(*   Nat.gcd_greatest, Nat.divide_trans, Nat.divide_pos_le,        *)
(*   Nat.pow_nonzero, Nat.pow_gt_lin_r, Nat.eqb_eq, Nat.eq_dec,    *)
(*   le_lt_dec, Nat.Div0.mod_divides, in_map_iff, id_refl,         *)
(*   NatLe_lift, NatLe_drop.                                       *)
(* Constructivity. plm_vmax / plm_v / plm_hit_find are first-order *)
(*   nat Fixpoints, directly extractable; smoke lemmas close by    *)
(*   vm_compute on small instances; all proofs end in Qed;         *)
(*   Axioms: none (Print Assumptions block at the file end).       *)
(* Build. Rocq 9.1.0: env.sh; unset COQLIB ROCQLIB; ulimit -s      *)
(*   65532; in a directory holding prebuilt S01_BaseRing.vo /      *)
(*   HansonLcm.vo / abl_Pr_core_01.vo / abl_Pr_euclid_03.vo run:   *)
(*   rocq c -native-compiler no -Q . "" abl_Pr_lcmdecomp_04.v      *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import S01_BaseRing (Id, id_refl, NatLe, NatLe_lift, NatLe_drop, And).
Require Import HansonLcm.
Require Import abl_Pr_core_01.
Require Import abl_Pr_euclid_03.

(* ---- Section 0. gcd unit lemmas (Nat.gcd_unique_alt closure) ---- *)

Lemma plm_gcd_1_r : forall n : nat, Id (Nat.gcd n 1) 1.
Proof.
  intros n.
  assert (H : Nat.gcd n 1 = 1).
  { apply Nat.gcd_unique_alt.
    intros q. split.
    - intros Hq. apply Nat.divide_1_r in Hq. subst q. split.
      + apply Nat.divide_1_l.
      + apply Nat.divide_refl.
    - intros [H1 H2]. exact H2. }
  rewrite H. apply id_refl.
Qed.

Lemma plm_gcd_1_l : forall n : nat, Id (Nat.gcd 1 n) 1.
Proof.
  intros n. rewrite Nat.gcd_comm. apply plm_gcd_1_r.
Qed.

(* ---- Section 1. Coprime-product divisibility core ---- *)

(* Kernel 1 (Gauss/Bezout): gcd b a = 1 and b divides a * c
   imply b divides c; both Bezout orientations are unfolded. *)
Lemma plm_gauss : forall b a c : nat,
  Nat.gcd b a = 1 -> Nat.divide b (a * c) -> Nat.divide b c.
Proof.
  intros b a c Hg Hd.
  destruct (Nat.gcd_bezout b a) as [Hbez | Hbez].
  - (* Bezout on (b, a): u * b = gcd b a + v * a *)
    destruct Hbez as [u [v Hu]]. rewrite Hg in Hu.
    destruct Hd as [q Hq].
    assert (H3 : u * c * b = c + v * q * b).
    { replace (u * c * b) with (u * b * c) by ring.
      rewrite Hu, Nat.mul_add_distr_r, Nat.mul_1_l.
      rewrite <- Nat.mul_assoc, Hq, Nat.mul_assoc. reflexivity. }
    exists (u * c - v * q).
    rewrite Nat.mul_sub_distr_r.
    assert (H4 : u * c * b - v * q * b = c) by lia.
    lia.
  - (* Bezout on (a, b): u * a = gcd b a + v * b *)
    destruct Hbez as [u [v Hu]]. rewrite Hg in Hu.
    destruct Hd as [q Hq].
    assert (H3 : u * q * b = c + v * c * b).
    { rewrite <- Nat.mul_assoc, <- Hq, Nat.mul_assoc, Hu.
      rewrite Nat.mul_add_distr_r, Nat.mul_1_l. ring. }
    exists (u * q - v * c).
    rewrite Nat.mul_sub_distr_r.
    assert (H4 : u * q * b - v * c * b = c) by lia.
    lia.
Qed.

(* Kernel 2: a divides c, b divides c, gcd a b = 1 imply a * b divides c. *)
Lemma plm_dvd_mul_coprime : forall a b c : nat,
  Nat.divide a c -> Nat.divide b c -> Nat.gcd a b = 1 ->
  Nat.divide (a * b) c.
Proof.
  intros a b c Hac Hbc Hg.
  destruct Hac as [c1 Hc1].
  assert (Hba : Nat.gcd b a = 1) by (rewrite Nat.gcd_comm; exact Hg).
  assert (Hb : Nat.divide b (a * c1)).
  { rewrite Nat.mul_comm, <- Hc1. exact Hbc. }
  destruct Hbc as [c2 Hc2].
  destruct (plm_gauss b a c1 Hba Hb) as [c3 Hc3].
  exists c3. rewrite Hc1, Hc3. ring.
Qed.

(* Kernel 3: gcd x y = 1 and gcd x z = 1 imply gcd x (y * z) = 1. *)
Lemma plm_coprime_mul : forall x y z : nat,
  Nat.gcd x y = 1 -> Nat.gcd x z = 1 -> Id (Nat.gcd x (y * z)) 1.
Proof.
  intros x y z Hxy Hxz.
  assert (H : Nat.gcd x (y * z) = 1).
  { apply Nat.divide_1_r.
    apply (Nat.divide_trans (Nat.gcd x (y * z)) (Nat.gcd x z) 1).
    - apply (Nat.gcd_greatest x z (Nat.gcd x (y * z))).
      + apply Nat.gcd_divide_l.
      + apply (plm_gauss (Nat.gcd x (y * z)) y z).
        * apply Nat.divide_1_r.
          apply (Nat.divide_trans
            (Nat.gcd (Nat.gcd x (y * z)) y) (Nat.gcd x y) 1).
          -- apply (Nat.gcd_greatest x y (Nat.gcd (Nat.gcd x (y * z)) y)).
             ++ apply (Nat.divide_trans
                  (Nat.gcd (Nat.gcd x (y * z)) y) (Nat.gcd x (y * z)) x).
                ** apply Nat.gcd_divide_l.
                ** apply Nat.gcd_divide_l.
             ++ apply Nat.gcd_divide_r.
          -- rewrite Hxy. apply Nat.divide_1_l.
        * apply Nat.gcd_divide_r.
    - rewrite Hxz. apply Nat.divide_1_l. }
  rewrite H. apply id_refl.
Qed.

(* Kernel 4: x coprime to every element implies x coprime to the
   list product (fold_right induction). *)
Lemma plm_gcd_prod_1 : forall (t : list nat) (x : nat),
  (forall y : nat, In y t -> Nat.gcd x y = 1) ->
  Id (Nat.gcd x (fold_right Nat.mul 1 t)) 1.
Proof.
  induction t as [| y t' IH]; intros x Hall.
  - exact (plm_gcd_1_r x).
  - change (fold_right Nat.mul 1 (y :: t'))
      with (Nat.mul y (fold_right Nat.mul 1 t')).
    apply plm_coprime_mul.
    + apply Hall. apply in_eq.
    + assert (Hid : Id (Nat.gcd x (fold_right Nat.mul 1 t')) 1).
      { apply IH. intros y' Hy'. apply Hall. apply in_cons. exact Hy'. }
      exact (match Hid in Id _ z
             return (Nat.gcd x (fold_right Nat.mul 1 t') = z) with
             | id_refl => eq_refl end).
Qed.

(* Pairwise coprimality of a list: every pair is coprime; repeated
   elements are excluded since gcd x x = x. Set-carried definition. *)
Definition plm_pairwise_coprime (l : list nat) : Set :=
  forall x y : nat, In x l -> In y l -> Id (Nat.gcd x y) 1.

(* Main theorem: elementwise divisibility plus pairwise coprimality
   imply the list product divides c (structural induction). *)
Theorem plm_coprime_prod_dvd : forall (l : list nat) (c : nat),
  (forall x : nat, In x l -> Nat.divide x c) ->
  plm_pairwise_coprime l ->
  Nat.divide (fold_right Nat.mul 1 l) c.
Proof.
  induction l as [| x t IH]; intros c Hdiv Hpw.
  - apply Nat.divide_1_l.
  - apply plm_dvd_mul_coprime.
    + apply Hdiv. apply in_eq.
    + apply IH.
      * intros y Hy. apply Hdiv. apply in_cons. exact Hy.
      * intros x' y' Hx' Hy'. apply Hpw.
        -- apply in_cons. exact Hx'.
        -- apply in_cons. exact Hy'.
    + assert (Hid : Id (Nat.gcd x (fold_right Nat.mul 1 t)) 1).
      { apply plm_gcd_prod_1. intros y Hy.
        assert (Hxy : Id (Nat.gcd x y) 1)
          by (apply Hpw; [apply in_eq | apply in_cons; exact Hy]).
        destruct Hxy; reflexivity. }
      exact (match Hid in Id _ z
             return (Nat.gcd x (fold_right Nat.mul 1 t) = z) with
             | id_refl => eq_refl end).
Qed.

(* ---- Section 2. Prime coprimality face ---- *)

(* Distinct primes are coprime (three-way case analysis on the gcd). *)
Lemma plm_prime_gcd_1 : forall p q : nat,
  pr_prime p -> pr_prime q -> (p = q -> False) -> Id (Nat.gcd p q) 1.
Proof.
  intros p q Hpp Hqq Hne.
  pose proof (fst Hpp) as Hp2. pose proof (snd Hpp) as Hpd.
  pose proof (fst Hqq) as Hq2. pose proof (snd Hqq) as Hqd.
  pose proof (NatLe_drop _ _ Hp2) as Hp2'.
  pose proof (NatLe_drop _ _ Hq2) as Hq2'.
  assert (Hgp : Nat.divide (Nat.gcd p q) p) by apply Nat.gcd_divide_l.
  assert (Hgq : Nat.divide (Nat.gcd p q) q) by apply Nat.gcd_divide_r.
  assert (Hlep : Nat.gcd p q <= p) by (apply Nat.divide_pos_le; [lia | exact Hgp]).
  assert (Hleq : Nat.gcd p q <= q) by (apply Nat.divide_pos_le; [lia | exact Hgq]).
  remember (Nat.gcd p q) as g eqn:Eg.
  destruct g as [| [| g'']].
  - exfalso. apply Nat.divide_0_l in Hgp. lia.
  - apply id_refl.
  - exfalso.
    destruct (Nat.eq_dec p q) as [Epq|Npq].
    + apply Hne. exact Epq.
    + destruct (Nat.eq_dec (S (S g'')) p) as [Egp|Ngp].
      * rewrite Egp in Hgq.
        assert (Hpq_lt : p < q).
        { destruct (le_lt_dec q p) as [Hqle|Hlt2].
          - exfalso. apply Npq. lia.
          - exact Hlt2. }
        exfalso.
        assert (Hqf : Id (Nat.eqb (q mod p) 0) false)
          by (apply (Hqd p Hp2); [apply NatLe_lift; exact Hpq_lt]).
        assert (Hqfe : Nat.eqb (q mod p) 0 = false)
          by (exact (match Hqf in (Id _ z) return (Nat.eqb (q mod p) 0 = z)
                     with id_refl => eq_refl end)).
        assert (Hp1 : 1 <= p) by lia.
        pose proof (pr_dvd_mod0 p q Hp1 Hgq) as Hmod0.
        assert (Hqe : q mod p = 0)
          by (exact (match Hmod0 in (Id _ z) return (q mod p = z)
                     with id_refl => eq_refl end)).
        rewrite Hqe in Hqfe. simpl in Hqfe. discriminate.
      * exfalso.
        assert (Hgf : Id (Nat.eqb (p mod (S (S g''))) 0) false)
          by (apply (Hpd (S (S g''))); [apply NatLe_lift; lia | apply NatLe_lift; lia]).
        assert (Hgfe : Nat.eqb (p mod (S (S g''))) 0 = false)
          by (exact (match Hgf in (Id _ z) return (Nat.eqb (p mod (S (S g''))) 0 = z)
                     with id_refl => eq_refl end)).
        assert (Hg1 : 1 <= S (S g'')) by lia.
        pose proof (pr_dvd_mod0 (S (S g'')) p Hg1 Hgp) as Hmod0.
        assert (Hmode : p mod (S (S g'')) = 0)
          by (exact (match Hmod0 in (Id _ z) return (p mod (S (S g'')) = z)
                     with id_refl => eq_refl end)).
        rewrite Hmode in Hgfe. simpl in Hgfe. discriminate.
Qed.

(* Single-base power lifting: gcd x y = 1 implies gcd x (y ^ b) = 1. *)
Lemma plm_coprime_pow1 : forall x y b : nat,
  Nat.gcd x y = 1 -> Id (Nat.gcd x (y ^ b)) 1.
Proof.
  intros x y b Hxy. induction b as [| b' IH].
  - rewrite Nat.pow_0_r. apply plm_gcd_1_r.
  - rewrite Nat.pow_succ_r'. apply plm_coprime_mul.
    + exact Hxy.
    + destruct IH; reflexivity.
Qed.

(* Full power lifting: gcd p q = 1 implies gcd (p ^ a) (q ^ b) = 1. *)
Lemma plm_gcd_pow : forall p q a b : nat,
  Nat.gcd p q = 1 -> Id (Nat.gcd (p ^ a) (q ^ b)) 1.
Proof.
  intros p q a b Hpq. induction a as [| a' IH].
  - rewrite Nat.pow_0_r. apply plm_gcd_1_l.
  - rewrite Nat.pow_succ_r'.
    rewrite (Nat.gcd_comm (p * p ^ a') (q ^ b)).
    apply plm_coprime_mul.
    + rewrite (Nat.gcd_comm (q ^ b) p).
      destruct (plm_coprime_pow1 p q b Hpq); reflexivity.
    + rewrite (Nat.gcd_comm (q ^ b) (p ^ a')).
      destruct IH; reflexivity.
Qed.

(* ---- Section 3. p-adic valuation face (e-structured recursion) ---- *)

(* Climb from 0 to e: v(e+1) = v(e) + 1 if p^(v(e)+1) divides k,
   else v(e); the bound e keeps the recursion structural. *)
Fixpoint plm_vmax (p k e : nat) : nat :=
  match e with
  | 0 => 0
  | S e' =>
      if Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0
      then S (plm_vmax p k e')
      else plm_vmax p k e'
  end.

Definition plm_v (p k : nat) : nat := plm_vmax p k k.

(* Limb one: the climbed value always divides (p = 0 branch explicit). *)
Lemma plm_vmax_dvd : forall p k e : nat, Nat.divide (p ^ plm_vmax p k e) k.
Proof.
  intros p k e. induction e as [| e' IH].
  - rewrite Nat.pow_0_r. apply Nat.divide_1_l.
  - change (plm_vmax p k (S e'))
      with (if Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0
            then S (plm_vmax p k e')
            else plm_vmax p k e').
    destruct (Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0) eqn:Em.
    + apply Nat.eqb_eq in Em.
      destruct (Nat.eq_dec p 0) as [Ep0|Ep0].
      * rewrite Ep0 in Em |- *.
        change (0 ^ S (plm_vmax 0 k e')) with 0 in Em.
        rewrite Nat.mod_0_r in Em.
        rewrite Em. apply Nat.divide_0_r.
      * assert (Hpos : 1 <= p ^ S (plm_vmax p k e')).
        { pose proof (Nat.pow_nonzero p (S (plm_vmax p k e')) Ep0). lia. }
        exact (pr_mod0_dvd (p ^ S (plm_vmax p k e')) k Hpos Em).
    + exact IH.
Qed.

(* Limb two: the value equals the bound e, or the next power divides
   and the climb continues (refutation form, kept verbatim). *)
Lemma plm_vmax_ceil : forall p k e : nat,
  {plm_vmax p k e = e} +
  {Nat.divide (p ^ S (plm_vmax p k e)) k -> False}.
Proof.
  intros p k e. induction e as [| e' IH].
  - left. reflexivity.
  - change (plm_vmax p k (S e'))
      with (if Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0
            then S (plm_vmax p k e')
            else plm_vmax p k e').
    destruct (Nat.eqb (k mod p ^ S (plm_vmax p k e')) 0) eqn:Em.
    + (* climbed: p ^ S v' divides k, so the failure limb is void *)
      assert (Hclimb : Nat.divide (p ^ S (plm_vmax p k e')) k).
      { apply Nat.eqb_eq in Em.
        destruct (Nat.eq_dec p 0) as [Ep0|Ep0].
        - rewrite Ep0 in Em |- *.
          change (0 ^ S (plm_vmax 0 k e')) with 0 in Em.
          rewrite Nat.mod_0_r in Em.
          rewrite Em. apply Nat.divide_0_r.
        - assert (Hpos : 1 <= p ^ S (plm_vmax p k e')).
          { pose proof (Nat.pow_nonzero p (S (plm_vmax p k e')) Ep0). lia. }
          exact (pr_mod0_dvd (p ^ S (plm_vmax p k e')) k Hpos Em). }
      destruct IH as [Heq | Hfail].
      * left. rewrite Heq. reflexivity.
      * exfalso. apply Hfail. exact Hclimb.
    + right. intros Hd.
      apply Nat.eqb_neq in Em.
      destruct (Nat.eq_dec p 0) as [Ep0|Ep0].
      * rewrite Ep0 in Hd, Em.
        change (0 ^ S (plm_vmax 0 k e')) with 0 in Hd, Em.
        rewrite Nat.mod_0_r in Em.
        apply Nat.divide_0_l in Hd. lia.
      * assert (Hpos : 1 <= p ^ S (plm_vmax p k e')).
        { pose proof (Nat.pow_nonzero p (S (plm_vmax p k e')) Ep0). lia. }
        apply Em.
        exact (match pr_dvd_mod0 (p ^ S (plm_vmax p k e')) k Hpos Hd in Id _ z
               return (k mod p ^ S (plm_vmax p k e') = z) with
               | id_refl => eq_refl end).
Qed.

Theorem plm_v_dvd : forall p k : nat, Nat.divide (p ^ plm_v p k) k.
Proof. intros p k. apply plm_vmax_dvd. Qed.

Theorem plm_v_max : forall p k : nat,
  1 < p -> 1 <= k -> Nat.divide (p ^ S (plm_v p k)) k -> False.
Proof.
  intros p k Hp Hk Hd.
  destruct (plm_vmax_ceil p k k) as [Heq | Hfail].
  - exfalso. unfold plm_v in Hd. rewrite Heq in Hd.
    assert (Hdle : p ^ S k <= k)
      by (apply Nat.divide_pos_le; [exact Hk | exact Hd]).
    pose proof (Nat.pow_gt_lin_r p (S k) Hp). lia.
  - exact (Hfail Hd).
Qed.

(* Valuation spec, both limbs (Set-carried pair; the negative limb
   keeps its -> False form verbatim). *)
Theorem plm_v_spec : forall p k : nat, 1 < p -> 1 <= k ->
  sigT (fun _ : Id (Nat.eqb (k mod p ^ plm_v p k) 0) true =>
        Nat.divide (p ^ S (plm_v p k)) k -> False).
Proof.
  intros p k Hp Hk.
  assert (Hd1 : Nat.divide (p ^ plm_v p k) k) by apply plm_v_dvd.
  assert (Hp0 : p <> 0) by lia.
  assert (Hpos : 0 < p ^ plm_v p k).
  { pose proof (Nat.pow_nonzero p (plm_v p k) Hp0). lia. }
  pose proof (match pr_dvd_mod0 (p ^ plm_v p k) k Hpos Hd1 in Id _ z
              return (k mod p ^ plm_v p k = z) with
              | id_refl => eq_refl end) as Hm.
  assert (Hl1 : Id (Nat.eqb (k mod p ^ plm_v p k) 0) true).
  { rewrite Hm. apply id_refl. }
  exists Hl1.
  intros Hd. apply (plm_v_max p k Hp Hk Hd).
Qed.

(* ---- Section 4. Prime factor tools ---- *)

(* A prime dividing a product divides one factor (gcd three-way split). *)
Lemma plm_prime_dvd_mul : forall p x y : nat,
  pr_prime p -> Nat.divide p (x * y) ->
  {Nat.divide p x} + {Nat.divide p y}.
Proof.
  intros p x y Hpp Hdvd.
  pose proof (fst Hpp) as Hp2. pose proof (snd Hpp) as Hpd.
  pose proof (NatLe_drop _ _ Hp2) as Hp2'.
  destruct (Nat.eq_dec (Nat.gcd p x) 1) as [E1|N1].
  - right. apply (plm_gauss p x y E1 Hdvd).
  - destruct (Nat.eq_dec (Nat.gcd p x) p) as [Ep|Np].
    + left. rewrite <- Ep. apply Nat.gcd_divide_r.
    + exfalso.
      assert (Hgp : Nat.divide (Nat.gcd p x) p) by apply Nat.gcd_divide_l.
      assert (Hle : Nat.gcd p x <= p)
        by (apply Nat.divide_pos_le; [lia | exact Hgp]).
      remember (Nat.gcd p x) as g eqn:Eg.
      destruct g as [| [| g']].
      * exfalso. apply Nat.divide_0_l in Hgp. lia.
      * apply N1. reflexivity.
      * exfalso.
        assert (Hgf : Id (Nat.eqb (p mod (S (S g'))) 0) false)
          by (apply (Hpd (S (S g'))); [apply NatLe_lift; lia | apply NatLe_lift; lia]).
        assert (Hgfe : Nat.eqb (p mod (S (S g'))) 0 = false)
          by (exact (match Hgf in (Id _ z) return (Nat.eqb (p mod (S (S g'))) 0 = z)
                     with id_refl => eq_refl end)).
        assert (Hg1 : 1 <= S (S g')) by lia.
        pose proof (pr_dvd_mod0 (S (S g')) p Hg1 Hgp) as Hmod0.
        assert (Hmode : p mod (S (S g')) = 0)
          by (exact (match Hmod0 in (Id _ z) return (p mod (S (S g')) = z)
                     with id_refl => eq_refl end)).
        rewrite Hmode in Hgfe. simpl in Hgfe. discriminate.
Qed.

(* A prime dividing the lcm divides one argument (Nat.lcm unfold). *)
Lemma plm_lcm_split : forall p a b : nat,
  pr_prime p -> Nat.divide p (Nat.lcm a b) ->
  {Nat.divide p a} + {Nat.divide p b}.
Proof.
  intros p a b Hpp Hd. unfold Nat.lcm in Hd.
  destruct (plm_prime_dvd_mul p a (b / Nat.gcd a b) Hpp Hd) as [H1|H2].
  - left. exact H1.
  - right.
    destruct (Nat.eq_dec (Nat.gcd a b) 0) as [E0|N0].
    + assert (Hgb : Nat.divide (Nat.gcd a b) b) by apply Nat.gcd_divide_r.
      rewrite E0 in Hgb. apply Nat.divide_0_l in Hgb.
      rewrite Hgb. apply Nat.divide_0_r.
    + assert (Hgb : Nat.divide (Nat.gcd a b) b) by apply Nat.gcd_divide_r.
      assert (Hg1 : 1 <= Nat.gcd a b) by lia.
      assert (Hb : b = Nat.gcd a b * (b / Nat.gcd a b)).
      { pose proof (Nat.div_mod b (Nat.gcd a b) N0) as Hdm.
        assert (Hm0 : b mod Nat.gcd a b = 0).
        { exact (match pr_dvd_mod0 (Nat.gcd a b) b Hg1 Hgb in Id _ z
                 return (b mod Nat.gcd a b = z) with
                 | id_refl => eq_refl end). }
        rewrite Hm0 in Hdm. rewrite Nat.add_0_r in Hdm. exact Hdm. }
      rewrite Hb. apply Nat.divide_mul_r. exact H2.
Qed.

(* Divisibility witness scanner (descending fuel: take S f when
   p divides S f, else drop the fuel). *)
Fixpoint plm_hit_find (p fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f => if Nat.eqb (S f mod p) 0 then S f else plm_hit_find p f
  end.

(* Scanner spec: p prime dividing L(fuel) yields a hit within bounds
   (Set-carried conjunction; mod form for the divisibility limb). *)
Lemma plm_hit_find_spec : forall p fuel : nat, pr_prime p ->
  Nat.divide p (hl_lcm_upto fuel) ->
  And (NatLe 1 (plm_hit_find p fuel))
      (And (NatLe (plm_hit_find p fuel) fuel)
           (Id (Nat.eqb (plm_hit_find p fuel mod p) 0) true)).
Proof.
  intros p fuel Hpp.
  pose proof (fst Hpp) as Hp2. pose proof (snd Hpp) as Hpd.
  pose proof (NatLe_drop _ _ Hp2) as Hp2'.
  induction fuel as [| f IH]; intros HL.
  - exfalso. simpl in HL.
    apply Nat.divide_1_r in HL. lia.
  - change (plm_hit_find p (S f))
      with (if Nat.eqb (S f mod p) 0 then S f else plm_hit_find p f).
    destruct (Nat.eqb (S f mod p) 0) eqn:Em.
    * apply Nat.eqb_eq in Em.
      assert (HpS : Nat.divide p (S f))
        by (apply (pr_mod0_dvd p (S f)); [lia | exact Em]).
      split.
      { apply NatLe_lift. lia. }
      split.
      { apply NatLe_lift. lia. }
      { change (Id (Nat.eqb (S f mod p) 0) true).
        rewrite Em. apply id_refl. }
    * apply Nat.eqb_neq in Em.
      change (hl_lcm_upto (S f)) with (Nat.lcm (hl_lcm_upto f) (S f)).
      destruct (plm_lcm_split p (hl_lcm_upto f) (S f) Hpp HL)
        as [HLf | HLf].
      -- destruct (IH HLf) as [H1 [H2 H3]].
         split.
         { exact H1. }
         split.
         { apply NatLe_lift. pose proof (NatLe_drop _ _ H2). lia. }
         { exact H3. }
      -- exfalso. apply Em.
         assert (Hp1 : 1 <= p) by lia.
         exact (match pr_dvd_mod0 p (S f) Hp1 HLf in Id _ z
                return (S f mod p = z) with
                | id_refl => eq_refl end).
Qed.

(* ---- Section 5. Hanson bridges + piece-3 closure ---- *)

(* Bridge one: the prime power enters the lcm list. *)
Theorem plm_lcm_dvd_pow : forall p n : nat,
  1 < p -> 1 <= n -> Nat.divide (p ^ plm_v p n) (hl_lcm_upto n).
Proof.
  intros p n Hp Hn.
  assert (Hdvd : Nat.divide (p ^ plm_v p n) n) by apply plm_v_dvd.
  assert (Hpos : 1 <= p ^ plm_v p n).
  { destruct (p ^ plm_v p n) as [| q'] eqn:Ep.
    - exfalso. apply Nat.divide_0_l in Hdvd. lia.
    - lia. }
  assert (Hle : p ^ plm_v p n <= n)
    by (apply Nat.divide_pos_le; [exact Hn | exact Hdvd]).
  apply (hl_lcm_divide_all n (p ^ plm_v p n)); [exact Hpos | exact Hle].
Qed.

(* Bridge two: the product of per-prime valuation powers over a list
   of distinct primes divides L(n) (coprime-product core at work). *)
Theorem plm_lcm_pow_prod_dvd : forall (l : list nat) (n : nat),
  1 <= n ->
  (forall p : nat, In p l -> pr_prime p) ->
  plm_pairwise_coprime l ->
  Nat.divide
    (fold_right Nat.mul 1 (map (fun p => p ^ plm_v p n) l))
    (hl_lcm_upto n).
Proof.
  intros l n Hn Hall Hpw.
  apply plm_coprime_prod_dvd.
  - intros q Hq. apply in_map_iff in Hq. destruct Hq as [p [Hp Hin]].
    rewrite <- Hp.
    apply (plm_lcm_dvd_pow p n);
      [pose proof (NatLe_drop _ _ (fst (Hall p Hin))); lia | exact Hn].
  - intros x y Hx Hy.
    (* ex extraction is staged in Prop; the Set goal is reached by rewrite *)
    assert (Hg0 : Nat.gcd x y = 1).
    { apply in_map_iff in Hx. apply in_map_iff in Hy.
      destruct Hx as [p [Hpx Hinp]]. destruct Hy as [q [Hqy Hinq]].
      rewrite <- Hpx, <- Hqy.
      assert (Hg1 : Nat.gcd p q = 1).
      { destruct (Hpw p q Hinp Hinq); reflexivity. }
      destruct (plm_gcd_pow p q (plm_v p n) (plm_v q n) Hg1); reflexivity. }
    rewrite Hg0. apply id_refl.
Qed.

(* Bridge three: a factor decomposition's product divides L(n). *)
Theorem plm_fact_dvd_lcm : forall (l : list nat) (m n : nat),
  fold_right Nat.mul 1 l = m -> 1 <= m -> m <= n ->
  Nat.divide (fold_right Nat.mul 1 l) (hl_lcm_upto n).
Proof.
  intros l m n Hfold Hm Hn. rewrite Hfold.
  apply hl_lcm_divide_all; assumption.
Qed.

Theorem plm_fact_exists_dvd_lcm : forall (m n : nat) (Hm : 2 <= m),
  m <= n ->
  Nat.divide
    (fold_right Nat.mul 1 (projT1 (pr_factor_exists m Hm)))
    (hl_lcm_upto n).
Proof.
  intros m n Hm Hn.
  pose proof (snd (projT2 (pr_factor_exists m Hm))) as HfoldI.
  assert (Hfold : fold_right Nat.mul 1 (projT1 (pr_factor_exists m Hm)) = m).
  { exact (match HfoldI in (Id _ z)
           return (fold_right Nat.mul 1 (projT1 (pr_factor_exists m Hm)) = z)
           with id_refl => eq_refl end). }
  apply (plm_fact_dvd_lcm _ m n); [exact Hfold | lia | exact Hn].
Qed.

(* Piece-3 closure: the new prime peu_next n does not divide L(n):
   the Euclid prime is outside the prime basis of lcm(1..n). *)
Theorem plm_peu_next_outside_lcm : forall n : nat,
  Nat.divide (peu_next n) (hl_lcm_upto n) -> False.
Proof.
  intros n Hd.
  destruct (plm_hit_find_spec (peu_next n) n (peu_next_prime n) Hd)
    as [H1 [H2 H3]].
  pose proof (NatLe_drop _ _ (fst (peu_next_prime n))) as Hp2.
  assert (Heq0 : Nat.eqb (plm_hit_find (peu_next n) n mod peu_next n) 0 = true).
  { exact (match H3 in Id _ z
           return (Nat.eqb (plm_hit_find (peu_next n) n mod peu_next n) 0 = z) with
           | id_refl => eq_refl end). }
  apply Nat.eqb_eq in Heq0.
  assert (Hdv : Nat.divide (peu_next n) (plm_hit_find (peu_next n) n)).
  { apply (pr_mod0_dvd (peu_next n) (plm_hit_find (peu_next n) n));
      [lia | exact Heq0]. }
  assert (Hpos : 0 < plm_hit_find (peu_next n) n).
  { pose proof (NatLe_drop _ _ H1). lia. }
  assert (Hle : peu_next n <= plm_hit_find (peu_next n) n)
    by (apply Nat.divide_pos_le; [exact Hpos | exact Hdv]).
  assert (Hle2 : plm_hit_find (peu_next n) n <= n)
    by (apply NatLe_drop; exact H2).
  pose proof (NatLe_drop _ _ (peu_next_gt n)). lia.
Qed.

(* ---- Section 6. Numeric smoke closures (small instances) ---- *)

Lemma plm_v_smoke_2_12 : Id (plm_v 2 12) 2.
Proof. vm_compute. apply id_refl. Qed.

Lemma plm_v_smoke_3_12 : Id (plm_v 3 12) 1.
Proof. vm_compute. apply id_refl. Qed.

Lemma plm_v_smoke_5_12 : Id (plm_v 5 12) 0.
Proof. vm_compute. apply id_refl. Qed.

Lemma plm_v_smoke_2_8 : Id (plm_v 2 8) 3.
Proof. vm_compute. apply id_refl. Qed.

Lemma plm_v_smoke_3_6 : Id (plm_v 3 6) 1.
Proof. vm_compute. apply id_refl. Qed.

Lemma plm_hit_smoke_5_6 : Id (plm_hit_find 5 6) 5.
Proof. vm_compute. apply id_refl. Qed.

Lemma plm_hit_smoke_7_6 : Id (plm_hit_find 7 6) 0.
Proof. vm_compute. apply id_refl. Qed.

Lemma plm_lcm_smoke_6 : Id (hl_lcm_upto 6) 60.
Proof. vm_compute. apply id_refl. Qed.

(* Power-image instance: p-adic exponents of 6 multiply back to 6. *)
Lemma plm_powprod_smoke_6 :
  Id (fold_right Nat.mul 1 (map (fun p => p ^ plm_v p 6) (2 :: 3 :: 5 :: nil)))
     6.
Proof. vm_compute. apply id_refl. Qed.

Lemma plm_bridge_smoke_6 :
  Id (Nat.eqb (hl_lcm_upto 6 mod 30) 0) true.
Proof. vm_compute. apply id_refl. Qed.

Lemma plm_gcd_pow_smoke : Id (Nat.gcd 4 9) 1.
Proof. vm_compute. apply id_refl. Qed.

(* ---- Section 7. Assumption audit (Print Assumptions block) ---- *)

Print Assumptions plm_gauss.
Print Assumptions plm_dvd_mul_coprime.
Print Assumptions plm_coprime_mul.
Print Assumptions plm_gcd_prod_1.
Print Assumptions plm_coprime_prod_dvd.
Print Assumptions plm_prime_gcd_1.
Print Assumptions plm_gcd_pow.
Print Assumptions plm_vmax_dvd.
Print Assumptions plm_vmax_ceil.
Print Assumptions plm_v_spec.
Print Assumptions plm_lcm_dvd_pow.
Print Assumptions plm_lcm_pow_prod_dvd.
Print Assumptions plm_fact_exists_dvd_lcm.
Print Assumptions plm_peu_next_outside_lcm.
