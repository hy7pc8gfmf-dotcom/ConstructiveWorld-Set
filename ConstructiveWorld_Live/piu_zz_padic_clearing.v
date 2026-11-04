(* ConstructiveWorld-Set -- p-adic clearing modules of the ZZ 2020 pi family. *)

(** * piu_zz_padic_clearing: discrete p-adic clearing for the pi-family ZZ chain.

    Mission.  Formalizes the p-adic clearing family for the ZZ 2020 pi chain
      (Zeilberger-Zudilin arXiv:1912.06345, Lemmas 1-3 in discrete form): the
      Set-carried identity core [Bid], [BidT], [Bdiv]; the Gaussian-integer
      split [zz_gauss_split] and [zz_L1_gauss_integral] with the 2-adic
      exponent bound [zz_L1_exponent]; the P_n window [zz_in_Pn],
      [zz_Pn_window_spec], [zz_Pn_floor_two], [zz_Pn_floor_three],
      [zz_Pn_bounded]; the lcm propagation [zz_j_div_lcm]; the product
      divisibility [zz_prodf_divides]; the integral quotient [zz_L_integral];
      and the clearing kernel [zz_clearing_propagation].

    Dependencies.  Stdlib [ZArith], [NArith], [QArith], [Znumtheory], [Lia].
      Requires no other module of this development.

    References.  This development, piu_zz_padic_clearing.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" piu_zz_padic_clearing.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import QArith.
From Stdlib Require Import Znumtheory.
(* Dependency note: the declared dependency surface is stdlib only --
   no in-tree requires.  [Lia] belongs to the stdlib micromega family
   and carries no in-tree dependency; since [ZArith] no longer re-exports
   [lia] by default, this import is the minimal stdlib-scope extension. *)
From Stdlib Require Import Lia.

Open Scope Z_scope.

(* ==================================================================== *)
(* Section 0. Set-carried core: [Bid] (a self-contained identity form),
   [BidT], [Bdiv]                  *)
(* ==================================================================== *)

Inductive Bid (A : Type) (a : A) : A -> Set := BidRefl : Bid A a a.

Definition BidT (x : bool) : Set := Bid bool x true.

Definition Bdiv (a b : Z) : Set := sigT (fun z : Z => Bid Z (a * z) b).

Lemma Bid_elim : forall (A : Type) (a b : A), Bid A a b -> a = b.
Proof. intros A a b H. destruct H. reflexivity. Qed.

Lemma Bid_intro : forall (A : Type) (a b : A), a = b -> Bid A a b.
Proof. intros A a b H. rewrite H. apply BidRefl. Qed.

Lemma BidT_intro : forall x : bool, x = true -> BidT x.
Proof. intros x H. apply Bid_intro. exact H. Qed.

Lemma BidT_elim : forall x : bool, BidT x -> x = true.
Proof. intros x H. apply Bid_elim. exact H. Qed.

Lemma BidT_and : forall x y : bool, BidT x -> BidT y -> BidT (x && y).
Proof.
  intros x y Hx Hy. apply BidT_elim in Hx. apply BidT_elim in Hy.
  apply BidT_intro. rewrite Hx, Hy. reflexivity.
Qed.

(* Boolean exit of [Bdiv]: from a*z = b witnessed by [Bid], the decidable
   divisibility test [Z.eqb (b mod a) 0] holds true.  (The former
   [Bdiv_to_divide] conclusion face carried [Z.divide] as a Prop and is
   retired; the Set-carried divisibility is [Bdiv] itself, and the Prop
   form is only derived inside consumer proofs via exists and
   [Bid_elim].) *)
Lemma Bdiv_eqb : forall a b : Z, Bdiv a b -> Z.eqb (b mod a) 0 = true.
Proof.
  intros a b [z H]. apply Bid_elim in H.
  destruct (Z.eq_dec a 0) as [Ha0 | Hane].
  - subst a. rewrite <- H. reflexivity.
  - apply (proj2 (Z.eqb_eq _ _)).
    apply (proj2 (Z.mod_divide b a Hane)).
    exists z. rewrite Z.mul_comm. symmetry. exact H.
Qed.

(* Lawful Set packaging of Prop divisibility: the witness is the data
   [Z.div], and mod = 0 appears only as a Prop step inside the proof.
   (The direct Prop-to-Set tear-off divide_to_Bdiv is unlawful and is
   not used.) *)
Lemma Bdiv_of_mod : forall a b : Z, a <> 0 -> b mod a = 0 -> Bdiv a b.
Proof.
  intros a b H0 Hm. exists (b / a). apply Bid_intro.
  pose proof (Z.div_mod b a H0) as Hdm. rewrite Hm in Hdm.
  symmetry. lia.
Qed.

(* ==================================================================== *)
(* Section 1. Discrete halving arithmetic on [Z]                                                    *)
(* ==================================================================== *)

Lemma zz_half_split : forall x : Z, 0 <= x -> (x + 1) / 2 + x / 2 = x.
Proof.
  intros x Hx.
  assert (H2 : 0 < 2) by lia.
  assert (H2ne : 2 <> 0) by lia.
  pose proof (Z.div_mod x 2 H2ne) as Hdmx.
  pose proof (Z.mod_pos_bound x 2 H2) as Hmb.
  destruct (Z.eq_dec (x mod 2) 0) as [Hr | Hr].
  - remember (x / 2) as q eqn:Hq.
    assert (Hc : x = 2 * q) by lia.
    assert (Hu : (x + 1) / 2 = q).
    { assert (Hmod : (x + 1) mod 2 = 1).
      { replace (x + 1) with (1 + q * 2) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      pose proof (Z.div_mod (x + 1) 2 H2ne) as Hd2.
      rewrite Hmod in Hd2. lia. }
    rewrite Hu, Hc. lia.
  - remember (x / 2) as q eqn:Hq.
    assert (Hc : x = 2 * q + 1) by lia.
    assert (Hu : (x + 1) / 2 = q + 1).
    { assert (Hmod : (x + 1) mod 2 = 0).
      { replace (x + 1) with (0 + (q + 1) * 2) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      pose proof (Z.div_mod (x + 1) 2 H2ne) as Hd2.
      rewrite Hmod in Hd2. lia. }
    rewrite Hu, Hc. lia.
Qed.

Lemma zz_half_floor_mono : forall a b : Z, a <= b -> Z.leb (a / 2) (b / 2) = true.
Proof. intros a b H. apply (proj2 (Z.leb_le _ _)). apply Z.div_le_mono; lia. Qed.

Lemma zz_half_ceil_mono : forall a b : Z,
  a <= b -> Z.leb ((a + 1) / 2) ((b + 1) / 2) = true.
Proof. intros a b H. apply (proj2 (Z.leb_le _ _)). apply Z.div_le_mono; lia. Qed.

Lemma zz_pow_shift : forall e1 e2 s c : Z,
  0 <= e1 -> 0 <= e2 -> 0 <= s -> s <= e1 + e2 ->
  Z.pow 2 e1 * (Z.pow 2 e2 * c) = Z.pow 2 s * (Z.pow 2 (e1 + e2 - s) * c).
Proof.
  intros e1 e2 s c H1 H2 H3 H4.
  assert (H12 : Z.pow 2 e1 * Z.pow 2 e2 = Z.pow 2 (e1 + e2)).
  { rewrite <- Z.pow_add_r by lia. reflexivity. }
  assert (He : e1 + e2 = s + (e1 + e2 - s)) by lia.
  assert (Hs2 : Z.pow 2 (e1 + e2) = Z.pow 2 s * Z.pow 2 (e1 + e2 - s)).
  { rewrite He at 1. rewrite Z.pow_add_r by lia. reflexivity. }
  replace (Z.pow 2 e1 * (Z.pow 2 e2 * c))
    with ((Z.pow 2 e1 * Z.pow 2 e2) * c) by lia.
  rewrite H12, Hs2. ring.
Qed.

(* ==================================================================== *)
(* Section 2. Gaussian integer Z^2 carriers (the (1±i) integrality core of Lemma 1)                        *)
(* ==================================================================== *)

Definition gmul (u v : Z * Z) : Z * Z :=
  (fst u * fst v - snd u * snd v, fst u * snd v + snd u * fst v).

Fixpoint gpow (u : Z * Z) (s : nat) : Z * Z :=
  match s with
  | O => (1, 0)
  | S s' => gmul u (gpow u s')
  end.

Lemma gmul_pairL : forall p q1 q2 : Z, gmul (p, 0) (q1, q2) = (p * q1, p * q2).
Proof. intros p q1 q2. unfold gmul. cbn [fst snd]. f_equal; ring. Qed.

Lemma gmul_11_11 : forall a b : Z,
  gmul (1, 1) (gmul (1, 1) (a, b)) = (- 2 * b, 2 * a).
Proof. intros a b. unfold gmul. cbn [fst snd]. f_equal; ring. Qed.

(* Computable unit factor: the Gaussian representation of
   u_s = (1+i)^s / 2^{floor(s/2)}, rotating by a quarter turn every two
   steps. *)
Fixpoint zz_gp (s : nat) : Z * Z :=
  match s with
  | O => (1, 0)
  | S O => (1, 1)
  | S (S s') => (- snd (zz_gp s'), fst (zz_gp s'))
  end.

Lemma zz_gsplit_eq : forall s : nat,
  gpow (1, 1) s =
    (Z.pow 2 (Z.of_nat s / 2) * fst (zz_gp s),
     Z.pow 2 (Z.of_nat s / 2) * snd (zz_gp s)).
Proof.
  intro s.
  assert (HQ : forall s : nat,
            gpow (1, 1) s =
              (Z.pow 2 (Z.of_nat s / 2) * fst (zz_gp s),
               Z.pow 2 (Z.of_nat s / 2) * snd (zz_gp s))
            /\
            gpow (1, 1) (S s) =
              (Z.pow 2 (Z.of_nat (S s) / 2) * fst (zz_gp (S s)),
               Z.pow 2 (Z.of_nat (S s) / 2) * snd (zz_gp (S s)))).
  { intro s0. induction s0 as [|s0 [IH1 IH2]].
    - split; reflexivity.
    - split.
      + exact IH2.
      + assert (Hq0 : 0 <= Z.of_nat s0 / 2) by (apply Z.div_pos; lia).
        cbn [gpow]. rewrite IH1, gmul_11_11.
        cbn [zz_gp fst snd].
        assert (HZ : Z.of_nat (S (S s0)) = Z.of_nat s0 + 2)
          by (rewrite Nat2Z.inj_succ; rewrite Nat2Z.inj_succ; lia).
        rewrite HZ.
        assert (Hdiv : (Z.of_nat s0 + 2) / 2 = Z.of_nat s0 / 2 + 1).
        { replace (Z.of_nat s0 + 2) with (1 * 2 + Z.of_nat s0) by lia.
          rewrite Z.div_add_l by lia. lia. }
        rewrite Hdiv, Z.pow_add_r by lia.
        replace (Z.pow 2 1) with 2 by reflexivity.
        f_equal; ring. }
  apply (proj1 (HQ s)).
Qed.

(* Theorem B1 (the discrete Z[i] integrality core of Lemma 1):
   (1+i)^s = 2^{floor(s/2)} * (c, d), witnessed by the computable
   function [zz_gp s] through a [sigT] existence package.  Literature
   anchor, the proof of Lemma 1: "(1±i)^2 = ±2i; hence 2^{ceil((3n-j)/2)}
   * (1-i)^{-m4} (1+i)^{-m5} ∈ Z[i]". *)
Theorem zz_gauss_split : forall s : nat,
  sigT (fun c : Z =>
        sigT (fun d : Z =>
              Bid (Z * Z) (gpow (1, 1) s)
                (Z.pow 2 (Z.of_nat s / 2) * c,
                 Z.pow 2 (Z.of_nat s / 2) * d))).
Proof.
  intro s. exists (fst (zz_gp s)), (snd (zz_gp s)).
  apply Bid_intro. apply zz_gsplit_eq.
Qed.

(* Theorem B2 (the pooled (1±i) integrality form of Lemma 1; the
   multiplication crossing avoids inverses): for s <= t,
   2^{ceil(t/2)} * (1+i)^s = 2^s * (c, d) for some Gaussian integer.
   The instantiation t = 3n-j, s = m4+m5 gives
   2^{ceil((3n-j)/2)} (1-i)^{-m4} (1+i)^{-m5} ∈ Z[i]; the (1-i) side
   follows by conjugate symmetry and is left as a continuation note. *)
Theorem zz_L1_gauss_integral : forall t s : nat, BidT (Nat.leb s t) ->
  sigT (fun c : Z =>
        sigT (fun d : Z =>
              Bid (Z * Z)
                (gmul (Z.pow 2 ((Z.of_nat t + 1) / 2), 0) (gpow (1, 1) s))
                (Z.pow 2 (Z.of_nat s) * c, Z.pow 2 (Z.of_nat s) * d))).
Proof.
  intros t s Hst. apply BidT_elim in Hst.
  apply (proj1 (Nat.leb_le s t)) in Hst.
  destruct (zz_gauss_split s) as [c0 [d0 Hsplit]].
  apply Bid_elim in Hsplit.
  assert (Hs0 : 0 <= Z.of_nat s) by apply Nat2Z.is_nonneg.
  assert (Hk0 : 0 <= Z.of_nat s / 2) by (apply Z.div_pos; lia).
  assert (Hh20 : 0 <= (Z.of_nat t + 1) / 2) by (apply Z.div_pos; lia).
  assert (Hhs : (Z.of_nat s + 1) / 2 + Z.of_nat s / 2 = Z.of_nat s)
    by (apply zz_half_split; lia).
  assert (Hmono : (Z.of_nat s + 1) / 2 <= (Z.of_nat t + 1) / 2).
  { apply (proj1 (Z.leb_le _ _)). apply zz_half_ceil_mono. lia. }
  assert (Hkf : Z.of_nat s / 2 <= (Z.of_nat s + 1) / 2).
  { apply (proj1 (Z.leb_le _ _)). apply zz_half_floor_mono. lia. }
  exists (Z.pow 2 ((Z.of_nat t + 1) / 2 + Z.of_nat s / 2 - Z.of_nat s) * c0),
         (Z.pow 2 ((Z.of_nat t + 1) / 2 + Z.of_nat s / 2 - Z.of_nat s) * d0).
  apply Bid_intro.
  rewrite Hsplit, gmul_pairL. f_equal.
  - apply (zz_pow_shift ((Z.of_nat t + 1) / 2) (Z.of_nat s / 2) (Z.of_nat s) c0); lia.
  - apply (zz_pow_shift ((Z.of_nat t + 1) / 2) (Z.of_nat s / 2) (Z.of_nat s) d0); lia.
Qed.

(* Theorem B3 (the discrete nat/Z form of the 2-adic exponent inequality
   behind display (5) of Lemma 1): for j <= 3n,
   floor((5n+3j)/2) <= 4n + j + ceil((3n-j)/2).  Literature anchor: in
   the proof of (5), the exponent flow from
   2^{-floor((5n+3j)/2)+1} * 2^{4n-1+j+m1} * 2^{ceil((3n-j)/2)} (1∓i)^{-m}
   ∈ Z[i], with m1 >= 0 already absorbed. *)
Theorem zz_L1_exponent : forall n j : nat,
  BidT (Z.leb (Z.of_nat j) (3 * Z.of_nat n)) ->
  BidT (Z.leb ((Z.of_nat n * 5 + Z.of_nat j * 3) / 2)
              (Z.of_nat n * 4 + Z.of_nat j +
               (Z.of_nat n * 3 - Z.of_nat j + 1) / 2)).
Proof.
  intros n j Hj. apply BidT_elim in Hj.
  apply (proj1 (Z.leb_le _ _)) in Hj.
  apply BidT_intro. apply (proj2 (Z.leb_le _ _)).
  transitivity ((Z.of_nat n * 5 + Z.of_nat j * 3 + 1) / 2).
  - apply (proj1 (Z.leb_le _ _)). apply zz_half_floor_mono. lia.
  - transitivity ((Z.of_nat n * 8 + Z.of_nat j * 2 +
                   (Z.of_nat n * 3 - Z.of_nat j + 1)) / 2).
    + apply (proj1 (Z.leb_le _ _)). apply zz_half_floor_mono. lia.
    + replace (Z.of_nat n * 8 + Z.of_nat j * 2)
        with ((Z.of_nat n * 4 + Z.of_nat j) * 2) by lia.
      rewrite Z.div_add_l by lia. lia.
Qed.

(* ==================================================================== *)
(* Section 3. [zz_primeb]: trial-division primality as bool (the P_n
   primality component, constructively extractable)              *)
(* ==================================================================== *)

Fixpoint zz_nodiv_upto (k : Z) (d : nat) : bool :=
  match d with
  | O => true
  | S d' =>
      if Z.ltb (Z.of_nat (S d')) 2 then true
      else if Z.eqb (k mod Z.of_nat (S d')) 0 then false
      else zz_nodiv_upto k d'
  end.

Definition zz_primeb (k : nat) : bool :=
  andb (Nat.ltb 1 k) (zz_nodiv_upto (Z.of_nat k) (k - 1)%nat).

Lemma zz_nodiv_upto_spec : forall k d, zz_nodiv_upto k d = true ->
  forall e : nat, (2 <= e)%nat -> (e <= d)%nat ->
  Z.eqb (k mod Z.of_nat e) 0 = false.
Proof.
  intros k d. induction d as [|d IH]; intros H e H2 H3.
  - exfalso. lia.
  - destruct (Nat.eq_dec e (S d)) as [He | Hne].
    + subst e. unfold zz_nodiv_upto in H.
      destruct (Z.ltb (Z.of_nat (S d)) 2) eqn:Hlt.
      * apply Z.ltb_lt in Hlt. exfalso. lia.
      * destruct (Z.eqb (k mod Z.of_nat (S d)) 0) eqn:Heq.
        -- discriminate H.
        -- reflexivity.
    + unfold zz_nodiv_upto in H.
      destruct (Z.ltb (Z.of_nat (S d)) 2) eqn:Hlt.
      * apply Z.ltb_lt in Hlt. exfalso. lia.
      * destruct (Z.eqb (k mod Z.of_nat (S d)) 0) eqn:Heq.
        -- discriminate H.
        -- apply IH; [exact H | lia | lia].
Qed.

Lemma zz_primeb_prime : forall k : nat, zz_primeb k = true -> Nat.ltb 1 k = true.
Proof.
  intros k H. apply Bool.andb_true_iff in H. destruct H as [H1 _]. exact H1.
Qed.

(* bool-carried form of the Z-side primality measure: for
   0 <= m < [Z.of_nat k] with m <> 1, the decidable test
   [Z.of_nat k mod m =? 0] is false.  (The former conclusion face carried
   [Z.prime] and is retired; consumers rebuild [Z.prime] inside their
   proofs: 1 < k comes from [zz_primeb_prime], and the no-divisor
   property is given directly here.) *)
Lemma zz_primeb_spec : forall k : nat, zz_primeb k = true ->
  forall m : Z, (0 <= m)%Z -> (m < Z.of_nat k)%Z -> m <> 1 ->
  Z.eqb (Z.of_nat k mod m) 0 = false.
Proof.
  intros k H m Hm0 Hmk Hm1.
  assert (Hnod : zz_nodiv_upto (Z.of_nat k) (k - 1)%nat = true).
  { apply Bool.andb_true_iff in H. destruct H as [_ H2]. exact H2. }
  pose proof (Z2Nat.id m Hm0) as Hzm.
  destruct (Z.eq_dec m 0) as [Hmz | Hmnz].
  - subst m. replace (Z.of_nat k mod 0) with (Z.of_nat k)
      by (destruct (Z.of_nat k); reflexivity).
    apply Z.eqb_neq. lia.
  - assert (He2 : (2 <= Z.to_nat m)%nat) by lia.
    assert (He3 : (Z.to_nat m <= k - 1)%nat) by lia.
    pose proof (zz_nodiv_upto_spec (Z.of_nat k) (k - 1)%nat Hnod
                  (Z.to_nat m) He2 He3) as Hne.
    rewrite Hzm in Hne. exact Hne.
Qed.

(* ==================================================================== *)
(* Section 4. Constructive definition of P_n (discrete statement-face reading
   of ZZ 2020 v2, Lemma 2)              *)
(*   P_n = {p prime : p > max{5, sqrt(3n)} : 1/2 <= {n/p} < 2/3}, where              *)
(*   {n/p} = (n mod p)/p;  1/2 <= {n/p} iff 2*(n mod p) >= p;          *)
(*   {n/p} < 2/3 iff 3*(n mod p) < 2p;  p > sqrt(3n) iff p^2 > 3n.                    *)
(* ==================================================================== *)

Definition zz_in_Pn (n p : nat) : bool :=
  andb (zz_primeb p)
  (andb (Nat.ltb 5%nat p)
  (andb (Nat.ltb (3 * n)%nat (p * p)%nat)
  (andb (Nat.leb p (2 * (n mod p))%nat)
        (Nat.ltb (3 * (n mod p))%nat (2 * p)%nat)))).

(* Window spec (the Prop-to-Set resolved form): the three-way Prop
   conjunction of the former zz_Pn_window_Prop is resolved into a bool
   equality carried by [Set], with [andb] components mirroring
   [zz_in_Pn] -- the three components are the Set forms of the three
   inequalities: [zz_primeb p] (so 1 < p), [Nat.leb p (2 * (n mod p))],
   [Nat.ltb (3 * (n mod p)) (2 * p)].  The Z-side inequalities follow
   inside consumer proofs via [Nat.leb_le], [Nat.ltb_lt] and [Nat2Z]
   (constructive Prop derivations inside proofs are lawful).  Name map:
   zz_Pn_window_Prop -> zz_Pn_window_spec. *)
Lemma zz_Pn_window_spec : forall n p : nat, BidT (zz_in_Pn n p) ->
  (zz_primeb p &&
   (Nat.leb p (2 * (n mod p))%nat &&
    Nat.ltb (3 * (n mod p))%nat (2 * p)%nat)) = true.
Proof.
  intros n p H. apply BidT_elim in H.
  unfold zz_in_Pn in H.
  apply Bool.andb_true_iff in H. destruct H as [Hp Hrest].
  apply Bool.andb_true_iff in Hrest. destruct Hrest as [_ Hrest].
  apply Bool.andb_true_iff in Hrest. destruct Hrest as [_ Hrest].
  apply Bool.andb_true_iff in Hrest. destruct Hrest as [Hw1 Hw2].
  apply Bool.andb_true_iff. split; [exact Hp |].
  apply Bool.andb_true_iff. split; [exact Hw1 | exact Hw2].
Qed.

(* Theorem B4 (the first discrete floor form in the proof of display (7)
   of Lemma 2): p ∈ P_n implies floor(2n/p) = 2*floor(n/p) + 1 (the
   discrete omega = {n/p} ∈ [1/2, 2/3) gives floor(2*omega) = 1). *)
Theorem zz_Pn_floor_two : forall n p : nat, BidT (zz_in_Pn n p) ->
  Bid Z (2 * Z.of_nat n / Z.of_nat p) (2 * (Z.of_nat n / Z.of_nat p) + 1).
Proof.
  intros n p H.
  pose proof (zz_Pn_window_spec n p H) as Hw.
  apply Bool.andb_true_iff in Hw. destruct Hw as [Hp Hwb].
  apply Bool.andb_true_iff in Hwb. destruct Hwb as [Hw1 Hw2].
  pose proof (zz_primeb_prime p Hp) as Hp1.
  apply (proj1 (Nat.ltb_lt 1 p)) in Hp1.
  assert (Hp2 : (Z.of_nat p <= 2 * Z.of_nat (n mod p))%Z).
  { apply (proj1 (Nat.leb_le p (2 * (n mod p)))) in Hw1.
    replace (2 * Z.of_nat (n mod p)) with (Z.of_nat (2 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    apply (proj1 (Nat2Z.inj_le p (2 * (n mod p)))). exact Hw1. }
  assert (Hp3 : (3 * Z.of_nat (n mod p) < 2 * Z.of_nat p)%Z).
  { apply (proj1 (Nat.ltb_lt (3 * (n mod p)) (2 * p))) in Hw2.
    replace (2 * Z.of_nat (n mod p)) with (Z.of_nat (2 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    replace (3 * Z.of_nat (n mod p)) with (Z.of_nat (3 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    replace (2 * Z.of_nat p) with (Z.of_nat (2 * p))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    apply (proj1 (Nat2Z.inj_lt (3 * (n mod p)) (2 * p))). exact Hw2. }
  assert (Zpne : Z.of_nat p <> 0) by lia.
  assert (Zp0 : 0 < Z.of_nat p) by lia.
  pose proof (Z.div_mod (Z.of_nat n) (Z.of_nat p) Zpne) as Hdm.
  pose proof (Z.mod_pos_bound (Z.of_nat n) (Z.of_nat p) Zp0) as Hmb.
  rewrite Nat2Z.inj_mod in Hp2, Hp3.
  remember (Z.of_nat n / Z.of_nat p) as q eqn:Hq.
  remember (Z.of_nat n mod Z.of_nat p) as r eqn:Hr.
  replace (2 * Z.of_nat n)
    with ((2 * q + 1) * Z.of_nat p + (2 * r - Z.of_nat p)) by lia.
  rewrite Z.div_add_l by exact Zpne.
  rewrite Z.div_small by lia.
  apply Bid_intro. lia.
Qed.

(* Theorem B5 (the third form, same proof shape): p ∈ P_n implies
   floor(3n/p) = 3*floor(n/p) + 1 (discretely floor(3*omega) = 1). *)
Theorem zz_Pn_floor_three : forall n p : nat, BidT (zz_in_Pn n p) ->
  Bid Z (3 * Z.of_nat n / Z.of_nat p) (3 * (Z.of_nat n / Z.of_nat p) + 1).
Proof.
  intros n p H.
  pose proof (zz_Pn_window_spec n p H) as Hw.
  apply Bool.andb_true_iff in Hw. destruct Hw as [Hp Hwb].
  apply Bool.andb_true_iff in Hwb. destruct Hwb as [Hw1 Hw2].
  pose proof (zz_primeb_prime p Hp) as Hp1.
  apply (proj1 (Nat.ltb_lt 1 p)) in Hp1.
  assert (Hp2 : (Z.of_nat p <= 2 * Z.of_nat (n mod p))%Z).
  { apply (proj1 (Nat.leb_le p (2 * (n mod p)))) in Hw1.
    replace (2 * Z.of_nat (n mod p)) with (Z.of_nat (2 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    apply (proj1 (Nat2Z.inj_le p (2 * (n mod p)))). exact Hw1. }
  assert (Hp3 : (3 * Z.of_nat (n mod p) < 2 * Z.of_nat p)%Z).
  { apply (proj1 (Nat.ltb_lt (3 * (n mod p)) (2 * p))) in Hw2.
    replace (2 * Z.of_nat (n mod p)) with (Z.of_nat (2 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    replace (3 * Z.of_nat (n mod p)) with (Z.of_nat (3 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    replace (2 * Z.of_nat p) with (Z.of_nat (2 * p))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    apply (proj1 (Nat2Z.inj_lt (3 * (n mod p)) (2 * p))). exact Hw2. }
  assert (Zpne : Z.of_nat p <> 0) by lia.
  assert (Zp0 : 0 < Z.of_nat p) by lia.
  pose proof (Z.div_mod (Z.of_nat n) (Z.of_nat p) Zpne) as Hdm.
  pose proof (Z.mod_pos_bound (Z.of_nat n) (Z.of_nat p) Zp0) as Hmb.
  rewrite Nat2Z.inj_mod in Hp2, Hp3.
  remember (Z.of_nat n / Z.of_nat p) as q eqn:Hq.
  remember (Z.of_nat n mod Z.of_nat p) as r eqn:Hr.
  replace (3 * Z.of_nat n)
    with ((3 * q + 1) * Z.of_nat p + (3 * r - Z.of_nat p)) by lia.
  rewrite Z.div_add_l by exact Zpne.
  rewrite Z.div_small by lia. apply Bid_intro. lia.
Qed.

(* Theorem B6 (boundedness from the window's lower bound): p ∈ P_n
   implies p <= 2n.  ({n/p} >= 1/2 gives p <= 2*(n mod p) <= 2n, so
   P_n ⊆ [7, 2n] and Φ_n is finite.)  Registered note: nonemptiness of
   P_n is not a pure Z-side statement (really empty at n = 1, 2) and is
   not carried here. *)
Theorem zz_Pn_bounded : forall n p : nat, BidT (zz_in_Pn n p) ->
  BidT (Nat.leb p (2 * n)%nat).
Proof.
  intros n p H.
  pose proof (zz_Pn_window_spec n p H) as Hw.
  apply Bool.andb_true_iff in Hw. destruct Hw as [Hp Hwb].
  apply Bool.andb_true_iff in Hwb. destruct Hwb as [Hw1 Hw2].
  pose proof (zz_primeb_prime p Hp) as Hp1.
  apply (proj1 (Nat.ltb_lt 1 p)) in Hp1.
  assert (Hp2 : (Z.of_nat p <= 2 * Z.of_nat (n mod p))%Z).
  { apply (proj1 (Nat.leb_le p (2 * (n mod p)))) in Hw1.
    replace (2 * Z.of_nat (n mod p)) with (Z.of_nat (2 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    apply (proj1 (Nat2Z.inj_le p (2 * (n mod p)))). exact Hw1. }
  assert (Hp3 : (3 * Z.of_nat (n mod p) < 2 * Z.of_nat p)%Z).
  { apply (proj1 (Nat.ltb_lt (3 * (n mod p)) (2 * p))) in Hw2.
    replace (2 * Z.of_nat (n mod p)) with (Z.of_nat (2 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    replace (3 * Z.of_nat (n mod p)) with (Z.of_nat (3 * (n mod p)))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    replace (2 * Z.of_nat p) with (Z.of_nat (2 * p))
      by (rewrite Nat2Z.inj_mul; reflexivity).
    apply (proj1 (Nat2Z.inj_lt (3 * (n mod p)) (2 * p))). exact Hw2. }
  assert (Zpne : Z.of_nat p <> 0) by lia.
  assert (Zp0 : 0 < Z.of_nat p) by lia.
  pose proof (Z.div_mod (Z.of_nat n) (Z.of_nat p) Zpne) as Hdm.
  pose proof (Z.mod_pos_bound (Z.of_nat n) (Z.of_nat p) Zp0) as Hmb.
  rewrite Nat2Z.inj_mod in Hp2.
  remember (Z.of_nat n / Z.of_nat p) as q eqn:Hq.
  remember (Z.of_nat n mod Z.of_nat p) as r eqn:Hr.
  assert (Hq0 : 0 <= q).
  { rewrite Hq. apply Z.div_pos; lia. }
  assert (Ht : 0 <= Z.of_nat p * q).
  { rewrite Hq, <- (Nat2Z.inj_div n p), <- (Nat2Z.inj_mul p (n / p)%nat).
    apply Nat2Z.is_nonneg. }
  assert (Hrn : r <= Z.of_nat n) by lia.
  apply BidT_intro. apply (proj2 (Nat.leb_le p (2 * n)%nat)).
  lia.
Qed.

(* ==================================================================== *)
(* Section 5. lcm(1..K) and divisibility propagation (Lemma 3, display (11))                  *)
(* ==================================================================== *)

Fixpoint zz_lcm_range (K : nat) : Z :=
  match K with
  | O => 1
  | S K' => Z.lcm (zz_lcm_range K') (Z.of_nat (S K'))
  end.

(* Theorem B7 (the constructive divisibility form of the opening step of
   the Lemma 3 proof, lcm(1..4n) * (1/j) ∈ Z): 1 <= j <= K implies
   j ∣ lcm(1..K), the quotient witness carried by [sigT] (Prop core plus
   the lawful [Bdiv_of_mod] packaging). *)
Lemma zz_j_div_lcm_P : forall K j : nat,
  (1 <= j)%nat -> (j <= K)%nat -> Bdiv (Z.of_nat j) (zz_lcm_range K).
Proof.
  intros K j H1 H2.
  assert (Hd : (Z.of_nat j | zz_lcm_range K)%Z).
  { revert H2. induction K as [|K IH]; intros H2.
    - exfalso. lia.
    - destruct (Nat.eq_dec j (S K)) as [Hej | Hlt].
      + subst j. apply Z.divide_lcm_r.
      + apply (Z.divide_trans (Z.of_nat j) (zz_lcm_range K) (zz_lcm_range (S K))).
        * apply IH. lia.
        * apply Z.divide_lcm_l. }
  apply Bdiv_of_mod; [lia |].
  apply (proj2 (Z.mod_divide (zz_lcm_range K) (Z.of_nat j) ltac:(lia))).
  exact Hd.
Qed.

Theorem zz_j_div_lcm : forall K j : nat,
  BidT (Nat.ltb 0 j && Nat.leb j K) ->
  Bdiv (Z.of_nat j) (zz_lcm_range K).
Proof.
  intros K j H. apply BidT_elim in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply (proj1 (Nat.ltb_lt 0 j)) in H1.
  apply (proj1 (Nat.leb_le j K)) in H2.
  apply zz_j_div_lcm_P; assumption.
Qed.

(* ==================================================================== *)
(* Section 6. Φ_n = ∏_{p∈P_n} p and Φ_n ∣ lcm(1..4n) (L_n ∈ Z)         *)
(* ==================================================================== *)

Fixpoint zz_prodf (n K : nat) : Z :=
  match K with
  | O => 1
  | S K' =>
      if zz_in_Pn n (S K') then zz_prodf n K' * Z.of_nat (S K')
      else zz_prodf n K'
  end.

Definition zz_Phi (n : nat) : Z := zz_prodf n (2 * n)%nat.

Definition zz_L (n : nat) : Z :=
  Z.div (zz_lcm_range (4 * n)%nat) ((zz_Phi n)).

Lemma zz_prodf_nonneg : forall n K : nat, Z.leb 0 (zz_prodf n K) = true.
Proof.
  intros n K. induction K as [|K IH].
  - cbn [zz_prodf]. reflexivity.
  - cbn [zz_prodf]. destruct (zz_in_Pn n (S K)) eqn:E.
    + apply (proj2 (Z.leb_le _ _)).
      apply (proj1 (Z.leb_le 0 (zz_prodf n K))) in IH.
      nia.
    + exact IH.
Qed.

Lemma zz_prodf_pos : forall n K : nat, Z.ltb 0 (zz_prodf n K) = true.
Proof.
  intros n K. induction K as [|K IH].
  - cbn [zz_prodf]. reflexivity.
  - cbn [zz_prodf]. destruct (zz_in_Pn n (S K)) eqn:E.
    + apply (proj2 (Z.ltb_lt _ _)).
      apply (proj1 (Z.ltb_lt 0 (zz_prodf n K))) in IH.
      assert (H1 : 1 <= zz_prodf n K) by lia.
      assert (H2 : 1 <= Z.of_nat (S K)) by lia.
      assert (Hle : 1 * 1 <= zz_prodf n K * Z.of_nat (S K)).
      { apply (Z.mul_le_mono_nonneg 1 (zz_prodf n K) 1 (Z.of_nat (S K))); lia. }
      lia.
    + exact IH.
Qed.

Lemma zz_coprime_sym : forall a b : Z,
  Z.eqb (Z.gcd a b) 1 = true -> Z.eqb (Z.gcd b a) 1 = true.
Proof.
  intros a b H. apply Z.eqb_eq in H.
  apply (proj2 (Z.eqb_eq _ _)). rewrite Z.gcd_comm. exact H.
Qed.

Lemma zz_lcm_prod : forall a b : Z,
  Z.gcd a b = 1 -> 0 <= a -> 0 <= b -> Z.lcm a b = a * b.
Proof.
  intros a b Hcop Ha Hb. unfold Z.lcm.
  rewrite Hcop. rewrite Z.div_1_r.
  rewrite Z.abs_eq by nia.
  reflexivity.
Qed.

Lemma zz_prodf_coprime : forall n K q,
  (forall k : nat, BidT (Nat.leb k K) -> BidT (zz_in_Pn n k) ->
     Z.eqb (Z.gcd (Z.of_nat k) q) 1 = true) ->
  Z.eqb (Z.gcd (zz_prodf n K) q) 1 = true.
Proof.
  intros n K q. induction K as [|K IH]; intros Hh.
  - cbn [zz_prodf]. rewrite Z.gcd_1_l. apply Z.eqb_refl.
  - cbn [zz_prodf]. destruct (zz_in_Pn n (S K)) eqn:E.
    + apply (proj2 (Z.eqb_eq _ _)).
      assert (Hrest : Z.gcd (zz_prodf n K) q = 1).
      { apply (proj1 (Z.eqb_eq _ _)). apply IH.
        intros k Hk Hinp. apply Hh.
        -- apply BidT_intro. apply (proj2 (Nat.leb_le k (S K))).
           apply BidT_elim in Hk. apply (proj1 (Nat.leb_le k K)) in Hk. lia.
        -- exact Hinp. }
      assert (Hsk : Z.gcd (Z.of_nat (S K)) q = 1).
      { apply (proj1 (Z.eqb_eq _ _)). apply Hh.
        -- apply BidT_intro. apply (proj2 (Nat.leb_le (S K) (S K))). lia.
        -- apply BidT_intro. exact E. }
      apply (proj2 (Zgcd_1_rel_prime _ _)). apply rel_prime_sym.
      apply (rel_prime_mult q).
      -- apply rel_prime_sym. apply (proj1 (Zgcd_1_rel_prime _ _)). exact Hrest.
      -- apply rel_prime_sym. apply (proj1 (Zgcd_1_rel_prime _ _)). exact Hsk.
    + apply IH. intros k Hk Hinp. apply Hh.
      * apply BidT_intro. apply (proj2 (Nat.leb_le k (S K))).
        apply BidT_elim in Hk. apply (proj1 (Nat.leb_le k K)) in Hk. lia.
      * exact Hinp.
Qed.

(* Theorem B8 (product propagation of divisibility under pairwise
   coprimality): if each member of P_n divides M -- coprimality being
   automatic from primality plus distinctness -- then
   ∏_{p∈P_n, p<=K} p ∣ M.  (Prop core plus the [Bdiv_of_mod] packaging.) *)
Lemma zz_prodf_divides_P : forall (n K : nat) (M : Z),
  (forall k : nat, BidT (Nat.leb k K) -> BidT (zz_in_Pn n k) ->
     Bdiv (Z.of_nat k) M) ->
  Bdiv (zz_prodf n K) M.
Proof.
  intros n K. induction K as [|K IH]; intros M Hhyp.
  - cbn [zz_prodf]. apply Bdiv_of_mod; [lia |].
    apply (proj2 (Z.mod_divide M 1 ltac:(lia))).
    apply Z.divide_1_l.
  - cbn [zz_prodf]. destruct (zz_in_Pn n (S K)) eqn:E.
    + assert (HrestM : Bdiv (zz_prodf n K) M).
      { apply IH. intros k Hk Hinp. apply Hhyp.
        - apply BidT_intro. apply (proj2 (Nat.leb_le k (S K))).
          apply BidT_elim in Hk. apply (proj1 (Nat.leb_le k K)) in Hk. lia.
        - exact Hinp. }
      assert (HpM : Bdiv (Z.of_nat (S K)) M).
      { apply Hhyp.
        - apply BidT_intro. apply (proj2 (Nat.leb_le (S K) (S K))). lia.
        - apply BidT_intro. exact E. }
      assert (Hpb : zz_primeb (S K) = true).
      { unfold zz_in_Pn in E. apply Bool.andb_true_iff in E.
        destruct E as [Epb _]. exact Epb. }
      assert (Hpk : prime (Z.of_nat (S K))).
      { pose proof (zz_primeb_prime (S K) Hpb) as Hltb.
        apply (proj1 (Nat.ltb_lt 1 (S K))) in Hltb.
        apply prime_intro.
        - lia.
        - intros m Hm.
        apply (proj1 (Zgcd_1_rel_prime _ _)).
          destruct (Z.eq_dec (Z.gcd m (Z.of_nat (S K))) 1) as [Hg | Hgne].
          + exact Hg.
          + exfalso.
            pose proof (Z.gcd_divide_l m (Z.of_nat (S K))) as Hgd1.
            pose proof (Z.gcd_divide_r m (Z.of_nat (S K))) as Hgd2.
            pose proof (Z.gcd_nonneg m (Z.of_nat (S K))) as Hgn.
            assert (Hgz : Z.gcd m (Z.of_nat (S K)) <> 0).
            { intro H0. rewrite H0 in Hgd1.
              destruct Hgd1 as [q Hq]. rewrite Z.mul_0_r in Hq. lia. }
            assert (Hg2 : (2 <= Z.gcd m (Z.of_nat (S K)))%Z) by lia.
            assert (Hgle : (Z.gcd m (Z.of_nat (S K)) <= m)%Z)
              by (apply (Z.divide_pos_le _ m); [lia | exact Hgd1]).
            assert (Hglt : (Z.gcd m (Z.of_nat (S K)) < Z.of_nat (S K))%Z) by lia.
            pose proof (zz_primeb_spec (S K) Hpb (Z.gcd m (Z.of_nat (S K))) Hgn Hglt Hgne) as Hb.
            rewrite (proj2 (Z.mod_divide (Z.of_nat (S K)) (Z.gcd m (Z.of_nat (S K))) Hgz) Hgd2) in Hb.
            discriminate Hb. }
      assert (Hcop : Z.eqb (Z.gcd (zz_prodf n K) (Z.of_nat (S K))) 1 = true).
      { apply zz_prodf_coprime.
        intros k Hk Hinp. apply BidT_elim in Hk.
        apply (proj1 (Nat.leb_le k K)) in Hk.
        apply (proj2 (Z.eqb_eq _ _)).
        assert (Hcp : Z.gcd (Z.of_nat (S K)) (Z.of_nat k) = 1).
        { apply (proj2 (Zgcd_1_rel_prime _ _)).
          apply (prime_rel_prime (Z.of_nat (S K)) Hpk (Z.of_nat k)).
          - intro Hd.
            assert (Hpbk : zz_primeb k = true).
            { apply BidT_elim in Hinp. unfold zz_in_Pn in Hinp.
              apply Bool.andb_true_iff in Hinp. destruct Hinp as [Hpbin _].
              exact Hpbin. }
            assert (Hqk : prime (Z.of_nat k)).
            { pose proof (zz_primeb_prime k Hpbk) as Hltb.
              apply (proj1 (Nat.ltb_lt 1 k)) in Hltb.
              apply prime_intro.
              - lia.
              - intros m Hm.
              apply (proj1 (Zgcd_1_rel_prime _ _)).
                destruct (Z.eq_dec (Z.gcd m (Z.of_nat k)) 1) as [Hg | Hgne].
                + exact Hg.
                + exfalso.
                  pose proof (Z.gcd_divide_l m (Z.of_nat k)) as Hgd1.
                  pose proof (Z.gcd_divide_r m (Z.of_nat k)) as Hgd2.
                  pose proof (Z.gcd_nonneg m (Z.of_nat k)) as Hgn.
                  assert (Hgz : Z.gcd m (Z.of_nat k) <> 0).
                  { intro H0. rewrite H0 in Hgd1.
                    destruct Hgd1 as [q Hq]. rewrite Z.mul_0_r in Hq. lia. }
                  assert (Hg2 : (2 <= Z.gcd m (Z.of_nat k))%Z) by lia.
                  assert (Hgle : (Z.gcd m (Z.of_nat k) <= m)%Z)
                    by (apply (Z.divide_pos_le _ m); [lia | exact Hgd1]).
                  assert (Hglt : (Z.gcd m (Z.of_nat k) < Z.of_nat k)%Z) by lia.
                  pose proof (zz_primeb_spec k Hpbk (Z.gcd m (Z.of_nat k)) Hgn Hglt Hgne) as Hb.
                  rewrite (proj2 (Z.mod_divide (Z.of_nat k) (Z.gcd m (Z.of_nat k)) Hgz) Hgd2) in Hb.
                  discriminate Hb. }
            pose proof (prime_div_prime (Z.of_nat (S K)) (Z.of_nat k)
                          Hpk Hqk Hd) as Heq.
            apply Nat2Z.inj in Heq. lia. }
        rewrite Z.gcd_comm. exact Hcp. }
      assert (Hlcm : Z.lcm (zz_prodf n K) (Z.of_nat (S K)) =
                     zz_prodf n K * Z.of_nat (S K)).
      { apply zz_lcm_prod.
        - apply (proj1 (Z.eqb_eq _ _)). exact Hcop.
        - apply (proj1 (Z.leb_le 0 (zz_prodf n K))). apply zz_prodf_nonneg.
        - apply Nat2Z.is_nonneg. }
      assert (Hp : (0 < zz_prodf n K)%Z).
      { apply (proj1 (Z.ltb_lt 0 (zz_prodf n K))). apply zz_prodf_pos. }
      apply Bdiv_of_mod.
      * lia.
      * apply (proj2 (Z.mod_divide M (zz_prodf n K * Z.of_nat (S K)) ltac:(lia))).
        rewrite <- Hlcm. apply Z.lcm_divide_iff. split.
        -- destruct HrestM as [z Hz]. apply Bid_elim in Hz.
           exists z. rewrite Z.mul_comm. symmetry. exact Hz.
        -- destruct HpM as [z Hz]. apply Bid_elim in Hz.
           exists z. rewrite Z.mul_comm. symmetry. exact Hz.
    + apply IH. intros k Hk Hinp. apply Hhyp.
      * apply BidT_intro. apply (proj2 (Nat.leb_le k (S K))).
        apply BidT_elim in Hk. apply (proj1 (Nat.leb_le k K)) in Hk. lia.
      * exact Hinp.
Qed.

Theorem zz_prodf_divides : forall (n K : nat) (M : Z),
  (forall k : nat, BidT (Nat.leb k K) -> BidT (zz_in_Pn n k) ->
     Bdiv (Z.of_nat k) M) ->
  Bdiv (zz_prodf n K) M.
Proof.
  intros n K M Hhyp.
  apply zz_prodf_divides_P. exact Hhyp.
Qed.

(* Theorem B9 (the L_n ∈ Z form of Lemma 3): there exists L (namely
   [zz_L n], the exact quotient lcm(1..4n)/Φ_n) with Φ_n * L =
   lcm(1..4n). *)
Theorem zz_L_integral : forall n : nat,
  sigT (fun L : Z => Bid Z ((zz_Phi n) * L) (zz_lcm_range (4 * n)%nat)).
Proof.
  intro n.
  assert (Hpos : (0 < (zz_Phi n))%Z).
  { unfold zz_Phi. apply (proj1 (Z.ltb_lt 0 (zz_prodf n (2 * n)%nat))).
    apply zz_prodf_pos. }
  assert (HdP : Bdiv (zz_Phi n) (zz_lcm_range (4 * n)%nat)).
  { apply (zz_prodf_divides_P n (2 * n)%nat).
    intros k Hk Hinp. apply zz_j_div_lcm_P.
    - pose proof (zz_Pn_window_spec n k Hinp) as Hw.
      apply Bool.andb_true_iff in Hw. destruct Hw as [Hpk _].
      pose proof (zz_primeb_prime k Hpk) as Hk1.
      apply (proj1 (Nat.ltb_lt 1 k)) in Hk1. lia.
    - assert (Hb : BidT (Nat.leb k (2 * n)%nat))
        by (apply zz_Pn_bounded; exact Hinp).
      apply BidT_elim in Hb. apply (proj1 (Nat.leb_le k (2 * n)%nat)) in Hb.
      lia. }
  assert (HL : (zz_Phi n) * Z.div (zz_lcm_range (4 * n)%nat) ((zz_Phi n))
             = zz_lcm_range (4 * n)%nat).
  { destruct HdP as [e He]. apply Bid_elim in He.
    replace (zz_lcm_range (4 * n)%nat) with (e * (zz_Phi n))
      by (rewrite Z.mul_comm; exact He).
    rewrite Z.div_mul by lia. apply Z.mul_comm. }
  exists (Z.div (zz_lcm_range (4 * n)%nat) ((zz_Phi n))).
  apply Bid_intro. exact HL.
Qed.

(* ==================================================================== *)
(* Section 7. Theorem B10: the combined kernel of Lemma 3 (the A_j side
   abstracted as f : nat -> Z)                  *)
(*   Literature: display (11), lcm * (1/j) ∈ Z, together with display      *)
(*   (12) -- for p ∈ P_n, p ∣ j implies p ∣ 10^{-j} A_j, the Lemma 2 v2   *)
(*   conclusion taken here as a premise -- so L_n * 10^{-j} A_j / j ∈ Z.  *)
(*   Carried form: 1 <= j <= 4n plus a per-prime clearing premise (p ∣ j  *)
(*   represented by the Set-carried boolean form [Z.eqb (j mod p) 0])     *)
(*   imply j ∣ L_n * f(j), witnessed by [sigT]. *)
(* ==================================================================== *)

Theorem zz_clearing_propagation : forall (n j : nat) (f : nat -> Z),
  BidT (Nat.ltb 0 j && Nat.leb j (4 * n)%nat) ->
  (forall p : nat, BidT (zz_in_Pn n p) ->
     BidT (Z.eqb (Z.of_nat j mod Z.of_nat p) 0) ->
     Bdiv (Z.of_nat p) (f j)) ->
  Bdiv (Z.of_nat j) (zz_L n * f j).
Proof.
  intros n j f Hj Hclear.
  assert (Hpos : (0 < (zz_Phi n))%Z).
  { unfold zz_Phi. apply (proj1 (Z.ltb_lt 0 (zz_prodf n (2 * n)%nat))).
    apply zz_prodf_pos. }
  apply BidT_elim in Hj. apply Bool.andb_true_iff in Hj.
  destruct Hj as [Hj1 Hj2].
  apply (proj1 (Nat.ltb_lt 0 j)) in Hj1.
  apply (proj1 (Nat.leb_le j (4 * n)%nat)) in Hj2.
  assert (Hjpos : (0 < j)%nat) by lia.
  assert (HjLcm : (Z.of_nat j | zz_lcm_range (4 * n)%nat)%Z).
  { destruct (zz_j_div_lcm_P (4 * n)%nat j ltac:(lia) ltac:(lia)) as [z Hz].
    apply Bid_elim in Hz.
    exists z. rewrite Z.mul_comm. symmetry. exact Hz. }
  set (w := Z.div (zz_lcm_range (4 * n)%nat) (Z.of_nat j)).
  assert (Hjw : zz_lcm_range (4 * n)%nat = Z.of_nat j * w).
  { unfold w.
    apply (proj2 (Z.div_exact (zz_lcm_range (4 * n)%nat) (Z.of_nat j) ltac:(lia))).
    apply (proj2 (Z.mod_divide (zz_lcm_range (4 * n)%nat) (Z.of_nat j) ltac:(lia))).
    exact HjLcm. }
  assert (Hwf : Bdiv (zz_Phi n) (w * f j)).
  { apply (zz_prodf_divides_P n (2 * n)%nat).
    intros k Hk Hinp.
    pose proof (zz_Pn_window_spec n k Hinp) as Hw.
    apply Bool.andb_true_iff in Hw. destruct Hw as [Hpk _].
    pose proof (zz_primeb_prime k Hpk) as Hwpos.
    apply (proj1 (Nat.ltb_lt 1 k)) in Hwpos.
    clear Hpk.
    assert (Hpbk : zz_primeb k = true).
    { apply BidT_elim in Hinp. unfold zz_in_Pn in Hinp.
      apply Bool.andb_true_iff in Hinp. destruct Hinp as [Hpb _].
      exact Hpb. }
    assert (Hprime : prime (Z.of_nat k)).
    { pose proof (zz_primeb_prime k Hpbk) as Hltb.
      apply (proj1 (Nat.ltb_lt 1 k)) in Hltb.
      apply prime_intro.
      - lia.
      - intros m Hm.
      apply (proj1 (Zgcd_1_rel_prime _ _)).
        destruct (Z.eq_dec (Z.gcd m (Z.of_nat k)) 1) as [Hg | Hgne].
        + exact Hg.
        + exfalso.
          pose proof (Z.gcd_divide_l m (Z.of_nat k)) as Hgd1.
          pose proof (Z.gcd_divide_r m (Z.of_nat k)) as Hgd2.
          pose proof (Z.gcd_nonneg m (Z.of_nat k)) as Hgn.
          assert (Hgz : Z.gcd m (Z.of_nat k) <> 0).
          { intro H0. rewrite H0 in Hgd1.
            destruct Hgd1 as [q Hq]. rewrite Z.mul_0_r in Hq. lia. }
          assert (Hg2 : (2 <= Z.gcd m (Z.of_nat k))%Z) by lia.
          assert (Hgle : (Z.gcd m (Z.of_nat k) <= m)%Z)
            by (apply (Z.divide_pos_le _ m); [lia | exact Hgd1]).
          assert (Hglt : (Z.gcd m (Z.of_nat k) < Z.of_nat k)%Z) by lia.
          pose proof (zz_primeb_spec k Hpbk (Z.gcd m (Z.of_nat k)) Hgn Hglt Hgne) as Hb.
          rewrite (proj2 (Z.mod_divide (Z.of_nat k) (Z.gcd m (Z.of_nat k)) Hgz) Hgd2) in Hb.
          discriminate Hb. }
    assert (HkL : (Z.of_nat k | zz_lcm_range (4 * n)%nat)%Z).
    { assert (Hk1 : (1 <= k)%nat) by lia.
      assert (Hk2 : (k <= 4 * n)%nat).
      { assert (Hb : BidT (Nat.leb k (2 * n)%nat))
          by (apply zz_Pn_bounded; exact Hinp).
        apply BidT_elim in Hb. apply (proj1 (Nat.leb_le k (2 * n)%nat)) in Hb.
        lia. }
      destruct (zz_j_div_lcm_P (4 * n)%nat k Hk1 Hk2) as [z Hz].
      apply Bid_elim in Hz.
      exists z. rewrite Z.mul_comm. symmetry. exact Hz. }
    destruct (Z.eqb (Z.of_nat j mod Z.of_nat k) 0) eqn:Hjeq.
    - (* k ∣ j: the clearing premise gives k ∣ f j directly; w times that
      is k ∣ w * f j *)
      assert (HjeqbB : BidT (Z.eqb (Z.of_nat j mod Z.of_nat k) 0)).
      { apply BidT_intro. exact Hjeq. }
      destruct (Hclear k Hinp HjeqbB) as [zp Hbp].
      apply Bid_elim in Hbp.
      exists (w * zp). apply Bid_intro. rewrite <- Hbp. ring.
    - (* k ∤ j: from k ∣ lcm = j * w plus primality, [Z.gauss] gives k ∣ w;
      multiply by f j afterwards *)
      assert (Hnkdj : ~ (Z.of_nat k | Z.of_nat j)).
      { intro Hd.
        pose proof (proj2 (Z.mod_divide (Z.of_nat j) (Z.of_nat k) ltac:(lia)) Hd)
          as Hmod0.
        rewrite Hmod0 in Hjeq. discriminate Hjeq. }
      assert (Hcop : Z.gcd (Z.of_nat k) (Z.of_nat j) = 1).
      { apply (proj2 (Zgcd_1_rel_prime _ _)).
        apply prime_rel_prime.
        - exact Hprime.
        - exact Hnkdj. }
      assert (Hkw : (Z.of_nat k | w)%Z).
      { apply (Z.gauss (Z.of_nat k) (Z.of_nat j) w).
        + rewrite <- Hjw. exact HkL.
        + exact Hcop. }
      assert (Hkne : Z.of_nat k <> 0) by lia.
      assert (Hmodw : w mod Z.of_nat k = 0).
      { apply (proj2 (Z.mod_divide w (Z.of_nat k) Hkne)). exact Hkw. }
      pose proof (Z.div_mod w (Z.of_nat k) Hkne) as Hdm.
      set (q := w / Z.of_nat k) in Hdm.
      rewrite Hmodw in Hdm.
      exists (q * f j). apply Bid_intro.
      rewrite Hdm. ring. }
  assert (HdP2 : Bdiv (zz_Phi n) (zz_lcm_range (4 * n)%nat)).
  { apply (zz_prodf_divides_P n (2 * n)%nat).
    intros k Hk Hinp. apply zz_j_div_lcm_P.
    - pose proof (zz_Pn_window_spec n k Hinp) as Hw.
      apply Bool.andb_true_iff in Hw. destruct Hw as [Hpk _].
      pose proof (zz_primeb_prime k Hpk) as Hk1.
      apply (proj1 (Nat.ltb_lt 1 k)) in Hk1. lia.
    - assert (Hb : BidT (Nat.leb k (2 * n)%nat))
        by (apply zz_Pn_bounded; exact Hinp).
      apply BidT_elim in Hb. apply (proj1 (Nat.leb_le k (2 * n)%nat)) in Hb.
      lia. }
  assert (HΦL : (zz_Phi n) * zz_L n = zz_lcm_range (4 * n)%nat).
  { unfold zz_L.
    destruct HdP2 as [e He]. apply Bid_elim in He.
    replace (zz_lcm_range (4 * n)%nat) with (e * (zz_Phi n))
      by (rewrite Z.mul_comm; exact He).
    rewrite Z.div_mul by lia. apply Z.mul_comm. }
  (* Prop core: j ∣ L_n * f j with witness z0; the lawful [Bdiv_of_mod]
     packaging lifts it to Set *)
  apply Bdiv_of_mod.
  - lia.
  - apply (proj2 (Z.mod_divide (zz_L n * f j) (Z.of_nat j) ltac:(lia))).
    destruct Hwf as [z0 Hz0]. apply Bid_elim in Hz0.
    assert (Heq : (zz_Phi n) * (zz_L n * f j)
                = (zz_Phi n) * (Z.of_nat j * z0)).
    { rewrite Z.mul_assoc, HΦL, Hjw, <- Z.mul_assoc, <- Hz0. ring. }
    exists z0.
    apply (proj1 (Z.mul_cancel_l (zz_L n * f j) (z0 * Z.of_nat j)
                    ((zz_Phi n)) ltac:(lia))).
    rewrite Heq. ring.
Qed.

(* ==================================================================== *)
(* Section 8. Audit exits: Print Assumptions on every delivered theorem             *)
(* ==================================================================== *)

Print Assumptions zz_gauss_split.
Print Assumptions zz_L1_gauss_integral.
Print Assumptions zz_L1_exponent.
Print Assumptions zz_Pn_floor_two.
Print Assumptions zz_Pn_floor_three.
Print Assumptions zz_Pn_bounded.
Print Assumptions zz_j_div_lcm.
Print Assumptions zz_prodf_divides.
Print Assumptions zz_L_integral.
Print Assumptions zz_clearing_propagation.
