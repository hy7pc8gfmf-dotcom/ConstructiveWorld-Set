(* ConstructiveWorld-Set -- finite Euler product formula for the prime reciprocal-sum register. *)

(** * abl_Pr_euler_prod: the finite Euler product formula, prime reciprocal-sum endpoint.

    Mission.  With L = [hl_lcm_upto n] (least common multiple of 1..n) and
      [pze_sigma] the nat-carried divisor sum, [pze_O1] proves
      sigma(L) * product of (p - 1) over primes p <= n at most
      L * product of p, and [pze_euler_harm] transfers the control to the
      harmonic sum [prs_hsum n L] (endpoint form of product (1 - 1/p)^(-1) >=
      H_n, the harmonic sum carried by the divisor sum through [pze_lower]);
      [pze_euler_gap] supplies the computable [sigT] gap witness with its
      [hl_id] equation.

    Dependencies.  Stdlib [Arith.Arith], [List], [Bool], [Lia].  Requires
      [Hanson3Pow], [HansonLcm], [abl_Pr_core_01], [abl_Pr_enum_02],
      [abl_Pr_euclid_03], [abl_Pr_lcmdecomp_04], [abl_Pr_lcm_eq],
      [abl_Pr_recip_sum] of this development.

    References.  This development, abl_Pr_euler_prod.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_Pr_euler_prod.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import HansonLcm.
Require Import abl_Pr_core_01.
Require Import abl_Pr_enum_02.
Require Import abl_Pr_lcmdecomp_04.
Require Import abl_Pr_lcm_eq.
Require Import abl_Pr_recip_sum.

(* ---- Sec.0  computable carriers: the divisibility indicator, finite sums, list sums, products ---- *)

(* divisibility indicator: 1 when k divides N, 0 otherwise *)
Definition pze_dvdind (k N : nat) : nat :=
  if Nat.eqb (N mod k) 0 then 1 else 0.

(* lower bound for products *)
Lemma pze_mul_pos : forall a b : nat, 1 <= a -> 1 <= b -> 1 <= a * b.
Proof.
  intros a b Ha Hb. apply Nat.le_trans with (1 * 1).
  - lia.
  - apply Nat.mul_le_mono; assumption.
Qed.

(* finite sum Σ_{k=1}^{B} f k *)
Fixpoint pze_sumf (f : nat -> nat) (B : nat) : nat :=
  match B with
  | 0 => 0
  | S B' => f (S B') + pze_sumf f B'
  end.

Lemma pze_sumf_ext : forall (f g : nat -> nat) (B : nat),
  (forall k : nat, f k = g k) -> pze_sumf f B = pze_sumf g B.
Proof.
  intros f g B H. induction B as [|B IH].
  - reflexivity.
  - simpl. rewrite (H (S B)), IH. reflexivity.
Qed.

Lemma pze_sumf_le : forall (f g : nat -> nat) (B : nat),
  (forall k : nat, f k <= g k) -> pze_sumf f B <= pze_sumf g B.
Proof.
  intros f g B H. induction B as [|B IH].
  - simpl. lia.
  - simpl. apply Nat.add_le_mono.
    + apply H.
    + exact IH.
Qed.

Lemma pze_sumf_add : forall (f g : nat -> nat) (B : nat),
  pze_sumf (fun k => f k + g k) B = pze_sumf f B + pze_sumf g B.
Proof.
  intros f g B. induction B as [|B IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma pze_sumf_mul_l : forall (c : nat) (f : nat -> nat) (B : nat),
  pze_sumf (fun k => c * f k) B = c * pze_sumf f B.
Proof.
  intros c f B. induction B as [|B IH].
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

(* truncation of the tail: a genuine extension contributes nothing *)
Lemma pze_sumf_trunc : forall (f : nat -> nat) (B1 B2 : nat),
  B1 <= B2 ->
  (forall k : nat, B1 < k -> k <= B2 -> f k = 0) ->
  pze_sumf f B2 = pze_sumf f B1.
Proof.
  intros f B1 B2. induction B2 as [|B2 IH]; intros Hle H0.
  - replace B1 with 0 by lia. reflexivity.
  - destruct (Nat.eq_dec B1 (S B2)) as [E | NE].
    + rewrite E. reflexivity.
    + assert (Hlt : B1 <= B2) by lia.
      simpl.
      rewrite (IH Hlt) by (intros k Hk1 Hk2; apply H0; lia).
      assert (Hp1 : B1 < S B2) by lia.
      assert (Hp2 : S B2 <= S B2) by lia.
      rewrite (H0 (S B2) Hp1 Hp2). lia.
Qed.

(* list sum Σ_{x∈l} F x *)
Definition pze_lsum (F : nat -> nat) (l : list nat) : nat :=
  fold_right (fun x acc => F x + acc) 0 l.

Lemma pze_lsum_app : forall F : nat -> nat, forall a b : list nat,
  pze_lsum F (a ++ b) = pze_lsum F a + pze_lsum F b.
Proof.
  intros F a. induction a as [|x a IH]; intro b.
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma pze_lsum_map : forall (F f : nat -> nat) (l : list nat),
  pze_lsum F (map f l) = pze_lsum (fun x => F (f x)) l.
Proof.
  intros F f l. induction l as [|a t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma pze_lsum_ext_in : forall F G : nat -> nat, forall l : list nat,
  (forall x : nat, In x l -> F x = G x) -> pze_lsum F l = pze_lsum G l.
Proof.
  intros F G l. induction l as [|a t IH]; intros H.
  - reflexivity.
  - simpl. rewrite (H a (or_introl eq_refl)).
    rewrite IH by (intros x Hx; apply H; right; exact Hx).
    reflexivity.
Qed.

(* base change between the list sum over [seq 1 len] and the finite sum (the start 1 aligns with the finite-sum index) *)
Lemma pze_lsum_seq1 : forall (f : nat -> nat) (len : nat),
  pze_lsum f (seq 1 len) = pze_sumf f len.
Proof.
  intros f len. induction len as [|len IH].
  - reflexivity.
  - rewrite seq_S, pze_lsum_app. simpl. rewrite IH.
    replace (1 + len) with (S len) by lia. lia.
Qed.

(* the harmonic carrier [prs_hsum] coincides definitionally with the finite sum *)
Lemma pze_hsum_sumf : forall n C : nat,
  prs_hsum n C = pze_sumf (fun k => C / k) n.
Proof.
  intros n C. induction n as [|n IH].
  - reflexivity.
  - rewrite prs_hsum_S. cbn [pze_sumf]. rewrite IH. reflexivity.
Qed.

(* product ∏_{x∈l} f x *)
Definition pze_prod (f : nat -> nat) (l : list nat) : nat :=
  fold_right Nat.mul 1 (map f l).

Lemma pze_prod_nil : forall f : nat -> nat, pze_prod f nil = 1.
Proof. reflexivity. Qed.

Lemma pze_prod_cons : forall (f : nat -> nat) (a : nat) (l : list nat),
  pze_prod f (a :: l) = f a * pze_prod f l.
Proof. reflexivity. Qed.

Lemma pze_prod_pos : forall f : nat -> nat, forall l : list nat,
  (forall x : nat, In x l -> 1 <= f x) -> 1 <= pze_prod f l.
Proof.
  intros f l. induction l as [|a t IH]; intros H.
  - rewrite pze_prod_nil. lia.
  - rewrite pze_prod_cons. apply Nat.le_trans with (1 * 1).
    + lia.
    + apply Nat.mul_le_mono.
      * apply H. left. reflexivity.
      * apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma pze_prod_hom : forall f g : nat -> nat, forall l : list nat,
  pze_prod (fun x => f x * g x) l = pze_prod f l * pze_prod g l.
Proof.
  intros f g l. induction l as [|a t IH].
  - rewrite pze_prod_nil, pze_prod_nil. reflexivity.
  - rewrite pze_prod_cons, pze_prod_cons, pze_prod_cons, IH. ring.
Qed.

Lemma pze_prod_mono : forall f g : nat -> nat, forall l : list nat,
  (forall x : nat, In x l -> f x <= g x) -> pze_prod f l <= pze_prod g l.
Proof.
  intros f g l. induction l as [|a t IH]; intros H.
  - rewrite pze_prod_nil, pze_prod_nil. lia.
  - rewrite pze_prod_cons, pze_prod_cons. apply Nat.mul_le_mono.
    + apply H. left. reflexivity.
    + apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

(* divisor sum σ(N) = Σ_{d=1}^{N} d·[d∣N], the nat carrier of Σ_{d∣N} d *)
Definition pze_sigma (N : nat) : nat :=
  pze_sumf (fun d => d * pze_dvdind d N) N.

Lemma pze_sigma_1 : pze_sigma 1 = 1.
Proof. reflexivity. Qed.

(* NoDup map over a list *)
Lemma pze_nodup_map : forall (f : nat -> nat) (l : list nat),
  NoDup l ->
  (forall x y : nat, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup (map f l).
Proof.
  intros f l. induction l as [|a t IH]; intros Hnd Hinj.
  - simpl. apply NoDup_nil.
  - simpl. apply NoDup_cons_iff. apply NoDup_cons_iff in Hnd.
    destruct Hnd as [Hna Hndt]. split.
    + intros Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hyt]].
      apply Hna.
      assert (Hay : a = y).
      { apply Hinj.
        - left. reflexivity.
        - right. exact Hyt.
        - rewrite Hy. reflexivity. }
      rewrite Hay. exact Hyt.
    + apply IH.
      * exact Hndt.
      * intros x y Hx Hy Hf.
        apply Hinj; [right; exact Hx | right; exact Hy | exact Hf].
Qed.

(* ---- Sec.G1  image-sum bound under injection: the list sum over a NoDup list stays under the full-interval finite sum ---- *)

Lemma pze_nodup_split : forall x : nat, forall l1 l2 : list nat,
  NoDup (l1 ++ x :: l2) -> NoDup (l1 ++ l2) /\
  (forall y : nat, In y (l1 ++ l2) -> y <> x).
Proof.
  intros x l1. induction l1 as [|a t IH]; intros l2 Hnd.
  - simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnin Hnd0].
    split.
    + exact Hnd0.
    + intros y Hy Hxy. subst y. apply Hnin. exact Hy.
  - simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnin Hnd0].
    destruct (IH l2 Hnd0) as [Hnd2 Hnx2]. split.
    + simpl. apply NoDup_cons_iff. split.
      * intros Hin. apply in_app_or in Hin. destruct Hin as [Ht | Hl2].
        -- apply Hnin. apply in_or_app. left. exact Ht.
        -- apply Hnin. apply in_or_app. right. right. exact Hl2.
      * exact Hnd2.
    + intros y Hy. simpl in Hy. destruct Hy as [Eya | Hy2].
      * subst y. intros Eax. apply Hnin. apply in_or_app. right. left.
        symmetry. exact Eax.
      * apply Hnx2. exact Hy2.
Qed.

Lemma pze_inj_lsum_le : forall B : nat, forall F : nat -> nat, forall l : list nat,
  NoDup l ->
  (forall x : nat, In x l -> 1 <= x /\ x <= B) ->
  pze_lsum F l <= pze_sumf F B.
Proof.
  intros B F. induction B as [|B IH]; intros l Hnd Hb.
  - assert (Hnil : l = nil).
    { destruct l as [|a t]. reflexivity. exfalso.
      destruct (Hb a (or_introl eq_refl)) as [H1 H2]. lia. }
    rewrite Hnil. simpl. lia.
  - destruct (in_dec Nat.eq_dec (S B) l) as [Hin | Hnin].
    + destruct (in_split (S B) l Hin) as [l1 [l2 Hsp]]. subst l.
      destruct (pze_nodup_split (S B) l1 l2 Hnd) as [Hnd2 Hnx].
      assert (Hb2 : forall x : nat, In x (l1 ++ l2) -> 1 <= x /\ x <= B).
      { intros x Hx2.
        assert (Hxl : In x (l1 ++ S B :: l2)).
        { apply in_app_or in Hx2. apply in_or_app.
          destruct Hx2 as [H1 | H2].
          - left. exact H1.
          - right. right. exact H2. }
        destruct (Hb x Hxl) as [Hx1 Hx3]. split.
        - exact Hx1.
        - destruct (Nat.eq_dec x (S B)) as [Ex | NEx].
          + exfalso. apply (Hnx x Hx2 Ex).
          + lia. }
      assert (Hfold : pze_lsum F (l1 ++ S B :: l2)
                    = pze_lsum F l1 + F (S B) + pze_lsum F l2).
      { rewrite (pze_lsum_app F l1 (S B :: l2)). simpl. lia. }
      rewrite Hfold.
      assert (Hrest : pze_lsum F l1 + pze_lsum F l2 <= pze_sumf F B).
      { rewrite <- (pze_lsum_app F l1 l2). apply IH.
        - exact Hnd2.
        - exact Hb2. }
      cbn [pze_sumf]. lia.
    + assert (Hb2 : forall x : nat, In x l -> 1 <= x /\ x <= B).
      { intros x Hx. destruct (Hb x Hx) as [H1 H2]. split.
        - exact H1.
        - destruct (Nat.eq_dec x (S B)) as [Ex | NEx].
          + exfalso. apply Hnin. rewrite <- Ex. exact Hx.
          + lia. }
      apply Nat.le_trans with (pze_sumf F B).
      * apply IH.
        -- exact Hnd.
        -- exact Hb2.
      * simpl. lia.
Qed.

(* ---- Sec.G2  quotient reindexing: the terms divisible by p regroup by their quotients ---- *)

(* distributivity of truncated subtraction over multiplication (holds unconditionally, by case analysis on b) *)
Lemma pze_mul_sub_aux : forall a b : nat, a * (b - 1) = a * b - a.
Proof.
  intros a b. destruct b as [|b'].
  - replace (0 - 1) with 0 by lia. rewrite !Nat.mul_0_r. lia.
  - replace (S b' - 1) with b' by lia.
    rewrite Nat.mul_succ_r. lia.
Qed.

Lemma pze_div_S_dvd : forall p B : nat,
  1 <= p -> (S B) mod p = 0 -> S B / p = S (B / p).
Proof.
  intros p B Hp Hm. assert (Hp0 : p <> 0) by lia.
  pose proof (Nat.div_mod (S B) p Hp0) as Hd. rewrite Hm in Hd.
  assert (Hq1 : S B / p >= 1).
  { destruct (S B / p) as [|q] eqn:Eq.
    - exfalso. simpl in Hd. lia.
    - lia. }
  assert (Hple : p <= S B).
  { assert (Hdvd : Nat.divide p (S B)) by (exists (S B / p); lia).
    pose proof (Nat.divide_pos_le p (S B) (Nat.lt_0_succ B) Hdvd). lia. }
  assert (HBp : B / p = S B / p - 1).
  { set (q := S B / p).
    pose proof (pze_mul_sub_aux p q) as Hx.
    assert (HB : B = p * (q - 1) + (p - 1)) by lia.
    rewrite HB.
    rewrite (Nat.mul_comm p (q - 1)).
    rewrite Nat.div_add_l by exact Hp0.
    rewrite Nat.div_small by lia.
    lia. }
  lia.
Qed.

Lemma pze_div_S_ndvd : forall p B : nat,
  1 <= p -> (S B) mod p <> 0 -> S B / p = B / p.
Proof.
  intros p B Hp Hm. assert (Hp0 : p <> 0) by lia.
  pose proof (Nat.div_mod (S B) p Hp0) as Hd.
  pose proof (Nat.mod_upper_bound (S B) p Hp0) as Hlt.
  assert (HBp : S B / p = B / p).
  { set (q := S B / p).
    assert (HB : B = p * q + (S B mod p - 1)) by lia.
    rewrite HB.
    rewrite (Nat.mul_comm p q).
    rewrite Nat.div_add_l by exact Hp0.
    rewrite Nat.div_small by lia.
    lia. }
  exact HBp.
Qed.

Lemma pze_reindex_raw : forall p B : nat, forall g : nat -> nat,
  1 <= p ->
  pze_sumf (fun k => g (k / p) * (if Nat.eqb (k mod p) 0 then 1 else 0)) B
  = pze_sumf g (B / p).
Proof.
  intros p B g Hp. assert (Hp0 : p <> 0) by lia.
  induction B as [|B IH].
  - rewrite Nat.Div0.div_0_l. reflexivity.
  - cbn [pze_sumf]. destruct (Nat.eqb (S B mod p) 0) eqn:Em.
    + change (if true then 1 else 0) with 1.
      rewrite Nat.mul_1_r, IH,
        (pze_div_S_dvd p B Hp (proj1 (Nat.eqb_eq (S B mod p) 0) Em)).
      reflexivity.
    + change (if false then 1 else 0) with 0.
      rewrite Nat.mul_0_r, Nat.add_0_l, IH.
      rewrite (pze_div_S_ndvd p B Hp
                 (proj1 (Nat.eqb_neq (S B mod p) 0) Em)).
      reflexivity.
Qed.

Lemma pze_reindex : forall p B : nat, forall g : nat -> nat,
  1 <= p ->
  pze_sumf (fun k => g (k / p) * pze_dvdind p k) B = pze_sumf g (B / p).
Proof.
  intros p B g Hp. unfold pze_dvdind. apply pze_reindex_raw. exact Hp.
Qed.

(* ---- Sec.1  cancellation bridge for the divisor indicator and coprimality with prime powers ---- *)

Lemma pze_dvd_div_cancel : forall p X j : nat,
  1 <= p -> 1 <= X ->
  Nat.divide (p * j) (p * X) <-> Nat.divide j X.
Proof.
  intros p X j Hp HX. split.
  - intros [c Hc]. destruct j as [|j'].
    + exfalso.
      assert (HpX : 1 <= p * X).
      { apply Nat.le_trans with (1 * 1); [lia | apply Nat.mul_le_mono; lia]. }
      lia.
    + exists c. assert (Hp0 : p <> 0) by lia.
      apply (proj1 (Nat.mul_cancel_l X (c * S j') p Hp0)).
      rewrite <- (prs_mul_swap c p (S j')). exact Hc.
  - intros [c Hc]. exists c. rewrite Hc.
    symmetry. exact (match prs_mul_swap c p j in (S01_BaseRing.Id _ y)
                     return (c * (p * j) = y) with
                     | S01_BaseRing.id_refl => eq_refl end).
Qed.

Lemma pze_dvdind_mul_cancel : forall p X j : nat,
  1 <= p -> 1 <= X ->
  pze_dvdind (p * j) (p * X) = pze_dvdind j X.
Proof.
  intros p X j Hp HX. unfold pze_dvdind.
  destruct (Nat.eqb ((p * X) mod (p * j)) 0) eqn:E1;
    destruct (Nat.eqb (X mod j) 0) eqn:E2; try reflexivity.
  - exfalso.
    assert (Hj1 : 1 <= j).
    { destruct j as [|j'].
      - exfalso.
        rewrite Nat.mul_0_r in E1.
        assert (Hz : (p * X) mod 0 = p * X) by (apply Nat.mod_0_r).
        rewrite Hz in E1.
        assert (Hz2 : p * X = 0) by exact (proj1 (Nat.eqb_eq _ _) E1).
        assert (HpX : 1 <= p * X) by (apply pze_mul_pos; lia).
        lia.
      - lia. }
    assert (Hmod1 : (p * X) mod (p * j) = 0)
      by exact (proj1 (Nat.eqb_eq ((p * X) mod (p * j)) 0) E1).
    assert (Hd1 : Nat.divide (p * j) (p * X))
      by (apply (pr_mod0_dvd (p * j) (p * X));
          [apply pze_mul_pos; [exact Hp | exact Hj1] | exact Hmod1]).
    assert (Hd2 : Nat.divide j X).
    { destruct (pze_dvd_div_cancel p X j Hp HX) as [Hf _].
      apply Hf. exact Hd1. }
    assert (Hmod2 : X mod j = 0).
    { assert (Hid : S01_BaseRing.Id (X mod j) 0)
        by (apply (pr_dvd_mod0 j X); [exact Hj1 | exact Hd2]).
      exact (match Hid in (S01_BaseRing.Id _ y) return (X mod j = y) with
             | S01_BaseRing.id_refl => eq_refl end). }
    rewrite Hmod2 in E2. simpl in E2. discriminate E2.
  - exfalso.
    assert (Hmod2 : X mod j = 0)
      by exact (proj1 (Nat.eqb_eq (X mod j) 0) E2).
    assert (Hj1 : 1 <= j).
    { destruct j as [|j'].
      - exfalso. rewrite Nat.mod_0_r in Hmod2. lia.
      - lia. }
    assert (Hd2 : Nat.divide j X)
      by (apply (pr_mod0_dvd j X); [exact Hj1 | exact Hmod2]).
    assert (Hd1 : Nat.divide (p * j) (p * X)).
    { destruct (pze_dvd_div_cancel p X j Hp HX) as [_ Hb].
      apply Hb. exact Hd2. }
    assert (Hmod1 : (p * X) mod (p * j) = 0).
    { assert (Hid : S01_BaseRing.Id ((p * X) mod (p * j)) 0)
        by (apply (pr_dvd_mod0 (p * j) (p * X));
            [apply pze_mul_pos; lia | exact Hd1]).
      exact (match Hid in (S01_BaseRing.Id _ y)
             return ((p * X) mod (p * j) = y) with
             | S01_BaseRing.id_refl => eq_refl end). }
    rewrite Hmod1 in E1. simpl in E1. discriminate E1.
Qed.

(* coprimality with prime powers: if p is prime and p does not divide k, then k is coprime to every power of p *)
Lemma pze_gcd_pow_prime : forall p e k : nat,
  pr_prime p -> 1 <= k -> (Nat.divide p k -> False) ->
  Nat.gcd k (p ^ e) = 1.
Proof.
  intros p e k Hp Hk Hnp. destruct Hp as [Hp2 Hpdiv].
  assert (Hp2le : 2 <= p) by exact (S01_BaseRing.NatLe_drop 2 p Hp2).
  assert (Hp1 : 1 <= p) by lia.
  assert (Hg1 : 1 <= Nat.gcd k (p ^ e)).
  { destruct (Nat.gcd k (p ^ e)) as [|g] eqn:Eg.
    - exfalso.
      pose proof (Nat.gcd_divide_l k (p ^ e)) as Hd. rewrite Eg in Hd.
      apply Nat.divide_0_l in Hd. lia.
    - lia. }
  destruct (le_lt_dec (Nat.gcd k (p ^ e)) 1) as [Hle | Hlt].
  - lia.
  - exfalso.
    destruct (pr_min_factor_exists (Nat.gcd k (p ^ e)) Hlt) as [q Hqf].
    destruct Hqf as [Hqd Hqp]. destruct Hqp as [Hq2 Hqdiv].
    assert (Hqpe : Nat.divide q (p ^ e)).
    { apply (Nat.divide_trans q (Nat.gcd k (p ^ e)) (p ^ e)).
      - exact Hqd.
      - apply Nat.gcd_divide_r. }
    assert (Haux : forall f : nat, Nat.divide q (p ^ f) -> Nat.divide q p).
    { intros f. induction f as [|f IHf]; intros Hf.
      - rewrite Nat.pow_0_r in Hf. exfalso.
        assert (Hq2le : 2 <= q) by exact (S01_BaseRing.NatLe_drop 2 q Hq2).
        assert (Hq11 : q <= 1)
          by (apply Nat.divide_pos_le; [lia | exact Hf]).
        lia.
      - rewrite Nat.pow_succ_r in Hf by lia.
        destruct (plm_prime_dvd_mul q p (p ^ f) (pair Hq2 Hqdiv) Hf)
          as [H1 | H2].
        + exact H1.
        + apply IHf. exact H2. }
    assert (Hqp2 : Nat.divide q p) by (exact (Haux e Hqpe)).
    assert (Hqlep : q <= p)
      by (apply Nat.divide_pos_le; [lia | exact Hqp2]).
    assert (Hqp3 : q = p).
    { destruct (Nat.eq_dec q p) as [E | NE].
      - exact E.
      - exfalso.
        assert (Hid : S01_BaseRing.Id (Nat.eqb (p mod q) 0) false).
        { apply (Hpdiv q).
          + exact Hq2.
          + apply S01_BaseRing.NatLe_lift. lia. }
        assert (Hid1 : S01_BaseRing.Id (p mod q) 0).
        { apply (pr_dvd_mod0 q p).
          + apply Nat.le_trans with 2. lia. exact (S01_BaseRing.NatLe_drop 2 q Hq2).
          + exact Hqp2. }
        assert (Hb0 : Nat.eqb (p mod q) 0 = false).
        { exact (match Hid in (S01_BaseRing.Id _ y)
                 return (Nat.eqb (p mod q) 0 = y) with
                 | S01_BaseRing.id_refl => eq_refl end). }
        assert (Hb1 : Nat.eqb (p mod q) 0 = true).
        { apply (proj2 (Nat.eqb_eq (p mod q) 0)).
          exact (match Hid1 in (S01_BaseRing.Id _ y) return (p mod q = y) with
                 | S01_BaseRing.id_refl => eq_refl end). }
        rewrite Hb1 in Hb0. discriminate Hb0. }
    assert (Hqk : Nat.divide q k).
    { apply (Nat.divide_trans q (Nat.gcd k (p ^ e)) k).
      - exact Hqd.
      - apply Nat.gcd_divide_l. }
    apply Hnp. rewrite <- Hqp3. exact Hqk.
Qed.

(* ---- Sec.S1  splitting step: σ(p^{e+1}·N) ≤ σ(N) + p·σ(p^e·N) ---- *)

Lemma pze_sigma_split_le : forall p e N : nat,
  pr_prime p -> 1 <= N ->
  pze_sigma (p ^ S e * N) <= pze_sigma N + p * pze_sigma (p ^ e * N).
Proof.
  intros p e N Hp HN. destruct Hp as [Hp2 Hpdiv].
  assert (Hp2le : 2 <= p) by exact (S01_BaseRing.NatLe_drop 2 p Hp2).
  assert (Hp0 : p <> 0) by lia.
  assert (Hp1 : 1 <= p) by lia.
  assert (HPe : p ^ S e * N = p * (p ^ e * N)).
  { rewrite Nat.pow_succ_r by lia. rewrite Nat.mul_assoc. reflexivity. }
  rewrite HPe. unfold pze_sigma.
  (* two-class split of the summands: the multiples of p and the nonmultiples *)
  assert (Hsplit :
    pze_sumf (fun k => k * pze_dvdind k (p * (p ^ e * N))) (p * (p ^ e * N))
    = pze_sumf
        (fun k => (k * pze_dvdind k (p * (p ^ e * N)) * pze_dvdind p k)
                + (k * pze_dvdind k (p * (p ^ e * N))
                   * (1 - pze_dvdind p k)))
        (p * (p ^ e * N))).
  { apply pze_sumf_ext. intro k. unfold pze_dvdind.
    destruct (Nat.eqb (k mod p) 0); lia. }
  rewrite Hsplit, pze_sumf_add.
  assert (Hpe1 : 1 <= p ^ e).
  { assert (Hnz : p ^ e <> 0) by (apply Nat.pow_nonzero; lia). lia. }
  assert (HM : 1 <= p ^ e * N).
  { apply Nat.le_trans with (1 * 1); [lia | apply Nat.mul_le_mono; lia]. }
  (* the divisible class regroups by quotients into p·σ(p^e·N) *)
  assert (Hpt : forall k : nat,
    k * pze_dvdind k (p * (p ^ e * N)) * pze_dvdind p k
    = (fun j => p * j * pze_dvdind (p * j) (p * (p ^ e * N))) (k / p)
      * pze_dvdind p k).
  { intro k. destruct (Nat.eqb (k mod p) 0) eqn:Ek.
    - assert (Hi1 : pze_dvdind p k = 1)
        by (unfold pze_dvdind; rewrite Ek; reflexivity).
      rewrite Hi1, !Nat.mul_1_r. cbv beta.
      assert (Hk : k = p * (k / p)).
      { pose proof (Nat.div_mod k p Hp0) as Hd.
        pose proof (proj1 (Nat.eqb_eq (k mod p) 0) Ek) as E0. lia. }
      rewrite <- Hk. reflexivity.
    - assert (Hi0 : pze_dvdind p k = 0)
        by (unfold pze_dvdind; rewrite Ek; reflexivity).
      rewrite Hi0, !Nat.mul_0_r. reflexivity. }
  assert (H1 :
    pze_sumf (fun k => k * pze_dvdind k (p * (p ^ e * N)) * pze_dvdind p k)
        (p * (p ^ e * N))
    = p * pze_sumf (fun k => k * pze_dvdind k (p ^ e * N)) (p ^ e * N)).
  { rewrite (pze_sumf_ext
        (fun k => k * pze_dvdind k (p * (p ^ e * N)) * pze_dvdind p k)
        (fun k => (fun j => p * j * pze_dvdind (p * j) (p * (p ^ e * N)))
                    (k / p) * pze_dvdind p k)
        (p * (p ^ e * N)) Hpt).
    rewrite (pze_reindex p (p * (p ^ e * N))
               (fun j => p * j * pze_dvdind (p * j) (p * (p ^ e * N))) Hp1).
    assert (Hdiv : p * (p ^ e * N) / p = p ^ e * N).
    { rewrite Nat.mul_comm. apply Nat.div_mul. exact Hp0. }
    rewrite Hdiv.
    rewrite (pze_sumf_ext
        (fun j => p * j * pze_dvdind (p * j) (p * (p ^ e * N)))
        (fun k => p * (k * pze_dvdind k (p ^ e * N)))
        (p ^ e * N)).
    + rewrite pze_sumf_mul_l. reflexivity.
    + intro j.
      rewrite (pze_dvdind_mul_cancel p (p ^ e * N) j Hp1 HM).
      symmetry. apply Nat.mul_assoc. }
  (* the nondivisible class folds into σ(N) by the Gauss cancellation *)
  assert (Hle3 : N <= p * (p ^ e * N)).
  { apply Nat.le_trans with (p ^ e * N).
    - apply Nat.le_trans with (1 * N).
      + lia.
      + exact (Nat.mul_le_mono_r 1 (p ^ e) N Hpe1).
    - apply Nat.le_trans with (1 * (p ^ e * N)).
      + lia.
      + apply Nat.mul_le_mono; [exact Hp1 | apply Nat.le_refl]. }
  assert (H0z : forall k : nat, N < k -> k <= p * (p ^ e * N) ->
    k * pze_dvdind k N = 0).
  { intros k Hk1 Hk2. unfold pze_dvdind.
    destruct (Nat.eqb (N mod k) 0) eqn:EN.
    - exfalso.
      assert (Hdv : Nat.divide k N)
        by (apply (pr_mod0_dvd k N);
            [lia | exact (proj1 (Nat.eqb_eq (N mod k) 0) EN)]).
      pose proof (Nat.divide_pos_le k N HN Hdv) as HkN2. lia.
    - apply Nat.mul_0_r. }
  assert (H2 :
    pze_sumf (fun k => k * pze_dvdind k (p * (p ^ e * N)) * (1 - pze_dvdind p k))
        (p * (p ^ e * N))
    <= pze_sumf (fun k => k * pze_dvdind k N) N).
  { rewrite <- (pze_sumf_trunc (fun k => k * pze_dvdind k N)
                  N (p * (p ^ e * N)) Hle3 H0z).
    apply (pze_sumf_le
             (fun k => k * pze_dvdind k (p * (p ^ e * N)) * (1 - pze_dvdind p k))
             (fun k => k * pze_dvdind k N) (p * (p ^ e * N))).
    - intros k. unfold pze_dvdind.
      destruct (Nat.eqb ((p * (p ^ e * N)) mod k) 0) eqn:EB;
        destruct (Nat.eqb (k mod p) 0) eqn:Ep;
        destruct (Nat.eqb (N mod k) 0) eqn:EN; simpl; try lia.
      (* remaining case: k divides p·(p^e·N) and p does not divide k, so k divides N by coprimality, contradicting the indicator bit *)
      exfalso.
      assert (Hk1 : 1 <= k).
      { destruct k as [|k'].
        - exfalso.
          assert (Hz : (p * (p ^ e * N)) mod 0 = p * (p ^ e * N))
            by (apply Nat.mod_0_r).
          rewrite Hz in EB.
          assert (Hz2 : p * (p ^ e * N) = 0)
            by exact (proj1 (Nat.eqb_eq _ _) EB).
          assert (HpeX : 1 <= p * (p ^ e * N))
            by (apply pze_mul_pos; lia).
          lia.
        - lia. }
      assert (Hdv : Nat.divide k (p ^ S e * N)).
      { rewrite Nat.pow_succ_r by lia. rewrite <- Nat.mul_assoc.
        apply (pr_mod0_dvd k (p * (p ^ e * N)));
          [exact Hk1 | exact (proj1 (Nat.eqb_eq _ _) EB)]. }
      assert (Hnp : Nat.divide p k -> False).
      { intros [c Hc].
        assert (Hid : S01_BaseRing.Id (k mod p) 0)
          by (apply (pr_dvd_mod0 p k); [lia | exists c; exact Hc]).
        assert (Hm0 : k mod p = 0).
        { exact (match Hid in (S01_BaseRing.Id _ y) return (k mod p = y) with
                 | S01_BaseRing.id_refl => eq_refl end). }
        pose proof (proj1 (Nat.eqb_neq (k mod p) 0) Ep) as Hne.
        rewrite Hm0 in Hne. lia. }
      assert (Hgcd : Nat.gcd k (p ^ S e) = 1)
        by (apply pze_gcd_pow_prime;
              [exact (pair Hp2 Hpdiv) | exact Hk1 | exact Hnp]).
      assert (HkN : Nat.divide k N).
      { apply (plm_gauss k (p ^ S e) N Hgcd). exact Hdv. }
      assert (HidN : S01_BaseRing.Id (N mod k) 0)
        by (apply (pr_dvd_mod0 k N); [lia | exact HkN]).
      assert (HmodN : N mod k = 0).
      { exact (match HidN in (S01_BaseRing.Id _ y) return (N mod k = y) with
               | S01_BaseRing.id_refl => eq_refl end). }
      rewrite HmodN in EN. simpl in EN. discriminate EN. }
  rewrite H1. lia.
Qed.

(* ---- Sec.S2  geometric completion step: σ(p^e·N) ≤ prs_geo p e·σ(N) ---- *)

Lemma pze_step_geo : forall p e N : nat,
  pr_prime p -> 1 <= N ->
  pze_sigma (p ^ e * N) <= prs_geo p e * pze_sigma N.
Proof.
  intros p e N [Hp2 Hpdiv] HN.
  assert (Hp2le : 2 <= p) by exact (S01_BaseRing.NatLe_drop 2 p Hp2).
  induction e as [|e IH].
  - rewrite Nat.pow_0_r, Nat.mul_1_l.
    replace (prs_geo p 0) with 1 by reflexivity. lia.
  - pose proof (pze_sigma_split_le p e N (pair Hp2 Hpdiv) HN) as H1.
    change (prs_geo p (S e)) with (1 + p * prs_geo p e).
    assert (Hpe1 : 1 <= p ^ e).
    { assert (Hnz : p ^ e <> 0) by (apply Nat.pow_nonzero; lia). lia. }
    assert (HM1 : p * pze_sigma (p ^ e * N) <= p * (prs_geo p e * pze_sigma N))
      by (apply Nat.mul_le_mono_l; exact IH).
    assert (Halg : pze_sigma N + p * (prs_geo p e * pze_sigma N)
                 = (1 + p * prs_geo p e) * pze_sigma N).
    { rewrite Nat.mul_add_distr_r, Nat.mul_1_l, <- Nat.mul_assoc. reflexivity. }
    lia.
Qed.

(* ---- Sec.S3  folding step: over a list of primes, σ(∏p^{e_p}) ≤ ∏ prs_geo p e_p ---- *)

Lemma pze_fold_geo : forall (l : list nat) (e : nat -> nat),
  (forall p : nat, In p l -> pr_prime p) ->
  pze_sigma (pze_prod (fun p => p ^ e p) l)
  <= pze_prod (fun p => prs_geo p (e p)) l.
Proof.
  intros l e. induction l as [|a t IH]; intros Hpp.
  - rewrite pze_prod_nil, pze_sigma_1, pze_prod_nil. lia.
  - assert (Hpa : pr_prime a) by (apply Hpp; left; reflexivity).
    assert (HN : 1 <= pze_prod (fun p => p ^ e p) t).
    { apply pze_prod_pos. intros x Hx.
      assert (Hx2 : 2 <= x).
      { destruct (Hpp x (or_intror Hx)) as [Hx2n _].
        exact (S01_BaseRing.NatLe_drop 2 x Hx2n). }
      assert (Hnz : x ^ e x <> 0) by (apply Nat.pow_nonzero; lia).
      lia. }
    rewrite pze_prod_cons, pze_prod_cons.
    apply Nat.le_trans with
      (prs_geo a (e a) * pze_sigma (pze_prod (fun p => p ^ e p) t)).
    + apply pze_step_geo.
      * exact Hpa.
      * exact HN.
    + apply Nat.mul_le_mono_l. apply IH. intros p Hp.
      apply Hpp. right. exact Hp.
Qed.

(* ---- Sec.2  the main chain: the O1 full bound and the Euler-Harm transfer ---- *)

(* the exact equation: the product of prime powers equals L(n), supplied by [pr_lcm_eq_decomp] of [abl_Pr_lcm_eq] *)
Theorem pze_runprod_eq : forall n : nat,
  pze_prod (fun p => p ^ plm_v p (hl_lcm_upto n)) (pen_primes_upto n)
  = hl_lcm_upto n.
Proof.
  intro n. unfold pze_prod. symmetry. apply hl_id_eq.
  apply pr_lcm_eq_decomp.
Qed.

(* upper bound: σ(L) ≤ ∏_{p≤n} prs_geo p (plm_v p L) *)
Theorem pze_sigma_upper : forall n : nat,
  pze_sigma (hl_lcm_upto n)
  <= pze_prod (fun p => prs_geo p (plm_v p (hl_lcm_upto n)))
       (pen_primes_upto n).
Proof.
  intro n.
  apply Nat.le_trans with
    (pze_sigma
       (pze_prod (fun p => p ^ plm_v p (hl_lcm_upto n)) (pen_primes_upto n))).
  - rewrite pze_runprod_eq. apply Nat.le_refl.
  - apply pze_fold_geo. intros p Hp.
    exact (fst (fst (pen_in_primes_upto p n) Hp)).
Qed.

(* quotient injection: k ↦ L/k is injective on the divisor set *)
Lemma pze_codiv_inj : forall n k1 k2 : nat,
  1 <= k1 -> 1 <= k2 ->
  Nat.divide k1 (hl_lcm_upto n) -> Nat.divide k2 (hl_lcm_upto n) ->
  hl_lcm_upto n / k1 = hl_lcm_upto n / k2 -> k1 = k2.
Proof.
  intros n k1 k2 H1 H2 D1 D2 E.
  assert (HL1 : 1 <= hl_lcm_upto n) by exact (S01_BaseRing.NatLe_drop _ _ (plq_lcm_pos n)).
  assert (Hk10 : k1 <> 0) by lia.
  assert (Hk20 : k2 <> 0) by lia.
  assert (Hid1 : S01_BaseRing.Id (hl_lcm_upto n mod k1) 0)
    by (apply (pr_dvd_mod0 k1 (hl_lcm_upto n)); [lia | exact D1]).
  assert (Hm1 : hl_lcm_upto n mod k1 = 0).
  { exact (match Hid1 in (S01_BaseRing.Id _ y)
           return (hl_lcm_upto n mod k1 = y) with
           | S01_BaseRing.id_refl => eq_refl end). }
  assert (Hid2 : S01_BaseRing.Id (hl_lcm_upto n mod k2) 0)
    by (apply (pr_dvd_mod0 k2 (hl_lcm_upto n)); [lia | exact D2]).
  assert (Hm2 : hl_lcm_upto n mod k2 = 0).
  { exact (match Hid2 in (S01_BaseRing.Id _ y)
           return (hl_lcm_upto n mod k2 = y) with
           | S01_BaseRing.id_refl => eq_refl end). }
  pose proof (Nat.div_mod (hl_lcm_upto n) k1 Hk10) as Hd1.
  pose proof (Nat.div_mod (hl_lcm_upto n) k2 Hk20) as Hd2.
  rewrite Hm1 in Hd1. rewrite Hm2 in Hd2.
  assert (Hq1 : 1 <= hl_lcm_upto n / k1).
  { destruct (hl_lcm_upto n / k1) eqn:Eq; [| lia].
    exfalso. simpl in Hd1. lia. }
  rewrite <- E in Hd2.
  assert (Ha : k1 * (hl_lcm_upto n / k1) = k2 * (hl_lcm_upto n / k1)) by lia.
  assert (Hq0 : hl_lcm_upto n / k1 <> 0) by lia.
  apply (proj1 (Nat.mul_cancel_r k1 k2 (hl_lcm_upto n / k1) Hq0)).
  lia.
Qed.

(* lower transfer: Σ_{k≤n} L/k ≤ σ(L) *)
Theorem pze_lower : forall n : nat,
  prs_hsum n (hl_lcm_upto n) <= pze_sigma (hl_lcm_upto n).
Proof.
  intro n.
  rewrite (pze_hsum_sumf n (hl_lcm_upto n)).
  rewrite <- (pze_lsum_seq1 (fun k => hl_lcm_upto n / k) n).
  unfold pze_sigma.
  assert (Hbridge :
    pze_lsum (fun k => hl_lcm_upto n / k) (seq 1 n)
    = pze_lsum (fun d => d * pze_dvdind d (hl_lcm_upto n))
        (map (fun k => hl_lcm_upto n / k) (seq 1 n))).
  { rewrite pze_lsum_map. apply pze_lsum_ext_in.
    intros x Hx. apply in_seq in Hx. destruct Hx as [Hx1 Hx2].
    assert (HL1 : 1 <= hl_lcm_upto n) by exact (S01_BaseRing.NatLe_drop _ _ (plq_lcm_pos n)).
    assert (Hx0 : x <> 0) by lia.
    assert (Hdvd : Nat.divide x (hl_lcm_upto n))
      by (apply (hl_lcm_divide_all n x); lia).
    pose proof (Nat.div_mod (hl_lcm_upto n) x Hx0) as Hdm.
    assert (Hidx : S01_BaseRing.Id (hl_lcm_upto n mod x) 0)
      by (apply (pr_dvd_mod0 x (hl_lcm_upto n)); [lia | exact Hdvd]).
    assert (Hm0 : hl_lcm_upto n mod x = 0).
    { exact (match Hidx in (S01_BaseRing.Id _ y)
             return (hl_lcm_upto n mod x = y) with
             | S01_BaseRing.id_refl => eq_refl end). }
    rewrite Hm0 in Hdm.
    assert (Hdm2 : hl_lcm_upto n = x * (hl_lcm_upto n / x)) by lia.
    assert (HLx1 : 1 <= hl_lcm_upto n / x).
    { destruct (hl_lcm_upto n / x) eqn:Eq; [| lia].
      exfalso. simpl in Hdm2. lia. }
    assert (Hdv2 : Nat.divide (hl_lcm_upto n / x) (hl_lcm_upto n)).
    { exists x. exact Hdm2. }
    assert (Hind : pze_dvdind (hl_lcm_upto n / x) (hl_lcm_upto n) = 1).
    { unfold pze_dvdind.
      destruct (Nat.eqb (hl_lcm_upto n mod (hl_lcm_upto n / x)) 0) eqn:E.
      - reflexivity.
      - exfalso.
        assert (Hidm : S01_BaseRing.Id
                         (hl_lcm_upto n mod (hl_lcm_upto n / x)) 0)
          by (apply (pr_dvd_mod0 (hl_lcm_upto n / x) (hl_lcm_upto n));
              [lia | exact Hdv2]).
        assert (Hm2 : hl_lcm_upto n mod (hl_lcm_upto n / x) = 0).
        { exact (match Hidm in (S01_BaseRing.Id _ y)
                 return (hl_lcm_upto n mod (hl_lcm_upto n / x) = y) with
                 | S01_BaseRing.id_refl => eq_refl end). }
        rewrite Hm2 in E. simpl in E. discriminate E. }
    rewrite Hind. lia. }
  rewrite Hbridge.
  apply (pze_inj_lsum_le (hl_lcm_upto n)
           (fun d => d * pze_dvdind d (hl_lcm_upto n))
           (map (fun k => hl_lcm_upto n / k) (seq 1 n))).
  - apply pze_nodup_map.
    + apply seq_NoDup.
    + intros x y Hx Hy Hf.
      apply in_seq in Hx. apply in_seq in Hy.
      destruct Hx as [Hx1 Hx2]. destruct Hy as [Hy1 Hy2].
      apply (pze_codiv_inj n); try lia.
      * apply (hl_lcm_divide_all n x); lia.
      * apply (hl_lcm_divide_all n y); lia.
  - intros x Hx. apply in_map_iff in Hx. destruct Hx as [k [Hxk Hkt]].
    subst x. apply in_seq in Hkt. destruct Hkt as [Hk1 Hk2].
    assert (HL1 : 1 <= hl_lcm_upto n) by exact (S01_BaseRing.NatLe_drop _ _ (plq_lcm_pos n)).
    assert (Hk0 : k <> 0) by lia.
    assert (Hdvd : Nat.divide k (hl_lcm_upto n))
      by (apply (hl_lcm_divide_all n k); lia).
    pose proof (Nat.div_mod (hl_lcm_upto n) k Hk0) as Hdm.
    assert (Hidk : S01_BaseRing.Id (hl_lcm_upto n mod k) 0)
      by (apply (pr_dvd_mod0 k (hl_lcm_upto n)); [lia | exact Hdvd]).
    assert (Hm0 : hl_lcm_upto n mod k = 0).
    { exact (match Hidk in (S01_BaseRing.Id _ y)
             return (hl_lcm_upto n mod k = y) with
             | S01_BaseRing.id_refl => eq_refl end). }
    rewrite Hm0 in Hdm.
    assert (Hdm2 : hl_lcm_upto n = k * (hl_lcm_upto n / k)) by lia.
    assert (HLk1 : 1 <= hl_lcm_upto n / k).
    { destruct (hl_lcm_upto n / k) eqn:Eq; [| lia].
      exfalso. simpl in Hdm2. lia. }
    split.
    + exact HLk1.
    + apply Nat.div_le_upper_bound.
      * lia.
      * apply Nat.le_trans with (1 * hl_lcm_upto n).
        -- lia.
        -- apply Nat.mul_le_mono_r. lia.
Qed.

(* per-prime-factor terminal inequality: prs_geo p e·(p−1) ≤ p^e·p, read off prs_geo_euler_eq *)
Lemma pze_termwise : forall n p : nat,
  In p (pen_primes_upto n) ->
  prs_geo p (plm_v p (hl_lcm_upto n)) * (p - 1)
  <= p ^ plm_v p (hl_lcm_upto n) * p.
Proof.
  intros n p Hp.
  destruct (fst (pen_in_primes_upto p n) Hp) as [Hpp _].
  destruct Hpp as [Hp2 Hpdiv].
  assert (Hp2le : 2 <= p) by exact (S01_BaseRing.NatLe_drop 2 p Hp2).
  assert (Hp1 : 1 <= p) by lia.
  assert (Heq : 1 + (p - 1) * prs_geo p (plm_v p (hl_lcm_upto n))
                = p ^ S (plm_v p (hl_lcm_upto n))).
  { exact (match prs_geo_euler_eq p (plm_v p (hl_lcm_upto n))
                (S01_BaseRing.NatLe_lift 1 p Hp1) in (S01_BaseRing.Id _ y)
           return (1 + (p - 1) * prs_geo p (plm_v p (hl_lcm_upto n)) = y) with
           | S01_BaseRing.id_refl => eq_refl end). }
  rewrite Nat.pow_succ_r in Heq by lia.
  lia.
Qed.

(* O1 full bound: σ(L)·∏(p−1) ≤ L·∏p *)
Theorem pze_O1 : forall n : nat,
  pze_sigma (hl_lcm_upto n) * pze_prod (fun p => p - 1) (pen_primes_upto n)
  <= hl_lcm_upto n * pze_prod (fun p => p) (pen_primes_upto n).
Proof.
  intro n.
  pose proof (pze_sigma_upper n) as Hup.
  assert (Hhom :
    pze_prod (fun p => prs_geo p (plm_v p (hl_lcm_upto n))) (pen_primes_upto n)
    * pze_prod (fun p => p - 1) (pen_primes_upto n)
    = pze_prod
        (fun p => prs_geo p (plm_v p (hl_lcm_upto n)) * (p - 1))
        (pen_primes_upto n))
    by (symmetry; apply pze_prod_hom).
  assert (Hmono :
    pze_prod
        (fun p => prs_geo p (plm_v p (hl_lcm_upto n)) * (p - 1))
        (pen_primes_upto n)
    <= pze_prod
        (fun p => p ^ plm_v p (hl_lcm_upto n) * p)
        (pen_primes_upto n)).
  { apply pze_prod_mono. intros x Hx. apply pze_termwise. exact Hx. }
  assert (Hhom2 :
    pze_prod (fun p => p ^ plm_v p (hl_lcm_upto n) * p) (pen_primes_upto n)
    = pze_prod (fun p => p ^ plm_v p (hl_lcm_upto n)) (pen_primes_upto n)
      * pze_prod (fun p => p) (pen_primes_upto n))
    by apply pze_prod_hom.
  pose proof (pze_runprod_eq n) as Hrun.
  apply Nat.le_trans with
    (pze_prod (fun p => prs_geo p (plm_v p (hl_lcm_upto n)))
       (pen_primes_upto n)
     * pze_prod (fun p => p - 1) (pen_primes_upto n)).
  - apply Nat.mul_le_mono_r. exact Hup.
  - rewrite Hhom.
    apply Nat.le_trans with
      (pze_prod (fun p => p ^ plm_v p (hl_lcm_upto n) * p)
         (pen_primes_upto n)).
    + exact Hmono.
    + rewrite Hhom2, Hrun. apply Nat.le_refl.
Qed.

(* Euler-Harm transfer: ∏(p−1)·H_n ≤ ∏p, the harmonic series held under the prime product *)
Theorem pze_euler_harm : forall n : nat,
  pze_prod (fun p => p - 1) (pen_primes_upto n) * prs_hsum n (hl_lcm_upto n)
  <= hl_lcm_upto n * pze_prod (fun p => p) (pen_primes_upto n).
Proof.
  intro n.
  pose proof (pze_lower n) as Hlo.
  pose proof (pze_O1 n) as H1.
  apply Nat.le_trans with
    (pze_prod (fun p => p - 1) (pen_primes_upto n)
     * pze_sigma (hl_lcm_upto n)).
  - apply Nat.mul_le_mono_l. exact Hlo.
  - rewrite (Nat.mul_comm
        (pze_prod (fun p => p - 1) (pen_primes_upto n))
        (pze_sigma (hl_lcm_upto n))).
    exact H1.
Qed.

(* Set-face carrier: the sigT witness of the gap and its hl_id equation (transparent Defined) *)
Theorem pze_euler_gap : forall n : nat,
  { d : nat & hl_id
      (pze_prod (fun p => p - 1) (pen_primes_upto n)
       * prs_hsum n (hl_lcm_upto n) + d)
      (hl_lcm_upto n * pze_prod (fun p => p) (pen_primes_upto n)) }.
Proof.
  intro n.
  pose proof (pze_euler_harm n) as H.
  exists (hl_lcm_upto n * pze_prod (fun p => p) (pen_primes_upto n)
          - pze_prod (fun p => p - 1) (pen_primes_upto n)
            * prs_hsum n (hl_lcm_upto n)).
  rewrite Nat.add_comm.
  rewrite Nat.sub_add by exact H.
  apply hl_idrefl.
Defined.

(* boolean checker (extractable and machine-runnable) *)
Definition pze_harm_check (n : nat) : bool :=
  Nat.leb (pze_prod (fun p => p - 1) (pen_primes_upto n)
            * prs_hsum n (hl_lcm_upto n))
          (hl_lcm_upto n * pze_prod (fun p => p) (pen_primes_upto n)).

(* ---- Sec.3  numeric smoke tests (small instances by vm_compute, no postulates) ---- *)

Lemma pze_sigma_smoke_6 : pze_sigma 6 = 12.
Proof. vm_compute. reflexivity. Qed.

Lemma pze_sigma_smoke_12 : pze_sigma 12 = 28.
Proof. vm_compute. reflexivity. Qed.

Lemma pze_O1_smoke_6 :
  pze_sigma (hl_lcm_upto 6) * pze_prod (fun p => p - 1) (pen_primes_upto 6)
  <= hl_lcm_upto 6 * pze_prod (fun p => p) (pen_primes_upto 6).
Proof. vm_compute. lia. Qed.

Lemma pze_harm_smoke_1 :
  pze_prod (fun p => p - 1) (pen_primes_upto 1) * prs_hsum 1 (hl_lcm_upto 1)
  <= hl_lcm_upto 1 * pze_prod (fun p => p) (pen_primes_upto 1).
Proof. vm_compute. lia. Qed.

Lemma pze_harm_smoke_4 :
  pze_prod (fun p => p - 1) (pen_primes_upto 4) * prs_hsum 4 (hl_lcm_upto 4)
  <= hl_lcm_upto 4 * pze_prod (fun p => p) (pen_primes_upto 4).
Proof. vm_compute. lia. Qed.

Lemma pze_harm_smoke_6 :
  pze_prod (fun p => p - 1) (pen_primes_upto 6) * prs_hsum 6 (hl_lcm_upto 6)
  <= hl_lcm_upto 6 * pze_prod (fun p => p) (pen_primes_upto 6).
Proof. vm_compute. lia. Qed.

Lemma pze_harm_check_6 : pze_harm_check 6 = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- Sec.4  assumption audit (Print Assumptions evidence face) ---- *)

Print Assumptions pze_inj_lsum_le.
Print Assumptions pze_reindex.
Print Assumptions pze_dvdind_mul_cancel.
Print Assumptions pze_gcd_pow_prime.
Print Assumptions pze_sigma_split_le.
Print Assumptions pze_step_geo.
Print Assumptions pze_fold_geo.
Print Assumptions pze_runprod_eq.
Print Assumptions pze_sigma_upper.
Print Assumptions pze_lower.
Print Assumptions pze_termwise.
Print Assumptions pze_O1.
Print Assumptions pze_euler_harm.
Print Assumptions pze_euler_gap.
Print Assumptions pze_harm_check.
