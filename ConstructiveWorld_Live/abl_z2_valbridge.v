(* ConstructiveWorld-Set -- zeta-2 tower Hanson chain: the valuation
   bridge [B(n) | C(n)]. *)

(** * abl_z2_valbridge: the valuation bridge [B(n) | C(n)].

    Mission.  For [C(n) := n! / prod_i floor(n/a_i)!] ([a_i] the
      Sylvester sequence of [abl_z2_dub3]), prove [B(n) :=
      hl_lcm_upto n] divides [C(n)] (Hanson 1972, Lemma 2): the
      Legendre identity [v_p(m!) = sum_j floor(m/p^j)] (arbiter
      [plm_v], fuel-bounded [z2v_leg]); nested division
      [floor(floor(n/p^j)/a) = floor(n/(a*p^j))]; layer-wise
      comparison through the Sylvester dense inequality
      [z2d_sylv_floor_t], giving [floor(log_p n) <= v_p(C(n))];
      closing via [h3_lcm_fold_divide] and a prime-factor split.

    Dependencies.  Stdlib [Arith.Arith], [Arith.Factorial], [Lia];
      requires [HansonLcm], [Hanson3Pow], [abl_z2_dub3],
      [abl_Pr_core_01], [abl_Pr_lcmdecomp_04], [S01_BaseRing].

    References.  ConstructiveWorld-Main, module [abl_z2_valbridge]
      (statement names carried over verbatim).

    Constructivity.  Whole file [Qed]-closed, no axioms, no admits,
      no classical logic; the main statement face [z2v_dvd_t : Set]
      ([hl_id] carrier, mod-zero criterion); supporting predicate
      slots on [hl_id]/[hl_le_t]; the five [z2v_*] Fixpoints are
      executable; tail [Print Assumptions] re-audits all statements.

    Build.  [coqc -native-compiler no -q -Q . "" abl_z2_valbridge.v]
      compiles cleanly (exit 0); artifact magic [436f7121 00015ff4]. *)

From Stdlib Require Import Arith.Arith Arith.Factorial List Lia.
Require Import HansonLcm.
Require Import Hanson3Pow.
Require Import abl_z2_dub3.
Require Import S01_BaseRing (Id, id_refl, NatLe, NatLe_drop).
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.

(* ============================================================ *)
(* Section 0 - carrier definitions                                 *)
(* ============================================================ *)

(* sum_{i<K} floor(m / p^{i+1}): the fuel-bounded Legendre sum      *)
(* (terms with p^{i+1} > m vanish naturally).                       *)
Fixpoint z2v_leg (p K m : nat) : nat :=
  match K with
  | O => 0
  | S K' => z2v_leg p K' m + m / p ^ (S K')
  end.

(* #{i < K : p^{i+1} divides t}: layer-wise divisibility counting   *)
(* (the incremental form of the Legendre sum).                      *)
Fixpoint z2v_cnt (p K t : nat) : nat :=
  match K with
  | O => 0
  | S K' => z2v_cnt p K' t + (if Nat.eqb (t mod p ^ (S K')) 0 then 1 else 0)
  end.

(* #{i < K : p^{i+1} <= n}: the layer count (fuel-bounded carrier   *)
(* of floor(log_p n)).                                              *)
Fixpoint z2v_pc (p K n : nat) : nat :=
  match K with
  | O => 0
  | S K' => z2v_pc p K' n + (if Nat.leb 1 (n / p ^ (S K')) then 1 else 0)
  end.

(* prod_{j<k} floor(n/a_{j+1})!: the denominator product of C(n)    *)
(* (factors with a_{j+1} > n contribute 0! = 1).                    *)
Fixpoint z2v_den (k n : nat) : nat :=
  match k with
  | O => 1
  | S k' => z2v_den k' n * fact (n / z2d_sylv_a k')
  end.

(* sum_{i<K} z2d_sylv_sum k floor(n/p^{i+1}): the layer-wise sum of *)
(* the per-layer Sylvester sums.                                    *)
Fixpoint z2v_lsum (p K k n : nat) : nat :=
  match K with
  | O => 0
  | S K' => z2v_lsum p K' k n + z2d_sylv_sum k (n / p ^ (S K'))
  end.

(* C(n) := n! / prod_i floor(n/a_i)! (the denominator product at    *)
(* the canonical layer bound k = n).                                *)
Definition z2v_C (n : nat) : nat := fact n / z2v_den n n.

(* Set-face divisibility criterion: [b mod a = 0] carried by        *)
(* [hl_id].                                                         *)
Definition z2v_dvd_t (a b : nat) : Set := hl_id (Nat.modulo b a) 0.

(* Power-split witness type: the explicit [: Set] annotation pins   *)
(* the sort of the sigT-body [*] notation.                          *)
Definition z2v_split_t (p c x y c1 c2 : nat) : Set :=
  (hl_id (c1 + c2) c) *
  (z2v_dvd_t (p ^ c1) x * z2v_dvd_t (p ^ c2) y).

(* Elimination bridge from the S01 [Id] carrier to a Prop equation  *)
(* (the J eliminator, shaped as the [id_sym] family).               *)
Lemma z2v_idS_eq : forall (A : Set) (x y : A), Id x y -> x = y.
Proof.
  intros A x y H.
  exact (match H in Id _ z return x = z with id_refl => eq_refl end).
Qed.

(* Transport bridge from a Prop equation to the [hl_id] carrier     *)
(* (the dual direction of [hl_id_eq]).                              *)
Lemma z2v_id_of_eq : forall (A : Set) (x y : A), x = y -> hl_id x y.
Proof.
  intros A x y E. induction E. apply hl_idrefl.
Qed.

(* ============================================================ *)
(* Section 1 - small tools for powers and sums                     *)
(* ============================================================ *)

(* Monotone divisibility of powers: [a <= b] gives [p^a | p^b].     *)
Lemma z2v_pow_dvd : forall p a b : nat,
  a <= b -> Nat.divide (p ^ a) (p ^ b).
Proof.
  intros p a b Hle.
  replace b with (a + (b - a)) by lia.
  rewrite Nat.pow_add_r.
  exists (p ^ (b - a)). apply Nat.mul_comm.
Qed.

(* Power positivity: [1 <= p] gives [1 <= p^e].                     *)
Lemma z2v_pow_pos : forall p e : nat, 1 <= p -> hl_le_t 1 (p ^ e).
Proof.
  intros p e Hp. apply hl_le_to_le_t. assert (Hp0 : p <> 0) by lia.
  pose proof (Nat.pow_nonzero p e Hp0). lia.
Qed.

(* Zero base of the Sylvester sum: [z2d_sylv_sum k 0 = 0].          *)
Lemma z2v_sylv_sum_0 : forall k : nat, hl_id (z2d_sylv_sum k 0) 0.
Proof.
  intros k. apply z2v_id_of_eq.
  induction k as [| k IH]; [reflexivity |].
  cbn [z2d_sylv_sum]. rewrite IH, Nat.Div0.div_0_l. lia.
Qed.

(* Zero base of the Legendre sum: [z2v_leg p K 0 = 0].              *)
Lemma z2v_leg_0 : forall p K : nat, hl_id (z2v_leg p K 0) 0.
Proof.
  intros p K. apply z2v_id_of_eq.
  induction K as [| K IH]; [reflexivity |].
  cbn [z2v_leg]. rewrite IH, Nat.Div0.div_0_l. lia.
Qed.

(* Denominator-product positivity: [1 <= z2v_den k n].              *)
Lemma z2v_den_pos : forall k n : nat, hl_le_t 1 (z2v_den k n).
Proof.
  induction k as [| k IH]; intro n.
  - cbn [z2v_den]. apply hl_le_to_le_t. lia.
  - cbn [z2v_den]. apply hl_le_to_le_t.
    pose proof (hl_le_t_to_le _ _ (IH n)) as IHp.
    pose proof (hl_le_t_to_le _ _ (h3_fact_pos (n / z2d_sylv_a k))) as Hfp.
    lia.
Qed.

(* ============================================================ *)
(* Section 2 - the valuation face: additivity of [plm_v] and the   *)
(*   power split                                                   *)
(* ============================================================ *)

(* [plm_v p 1 = 0] for [1 < p].                                     *)
Lemma z2v_v_1 : forall p : nat, 1 < p -> hl_id (plm_v p 1) 0.
Proof.
  intros p Hp. apply z2v_id_of_eq. unfold plm_v. cbn [plm_vmax Nat.pow].
  rewrite Nat.mul_1_r.
  rewrite (Nat.mod_small 1 p) by lia.
  reflexivity.
Qed.

(* Power split: if [p^c | x*y], there are [c1 + c2 = c] with the    *)
(* two-way divisibility split (a prime dividing a product divides   *)
(* one factor; recurse by cancelling p layer by layer).             *)
Lemma z2v_pow_split : forall p c x y : nat,
  pr_prime p -> Nat.divide (p ^ c) (x * y) ->
  sigT (fun c1 : nat => sigT (fun c2 : nat =>
    z2v_split_t p c x y c1 c2)).
Proof.
  intros p c. induction c as [| c IH]; intros x y Hpp Hd.
  - exists 0, 0. split; [apply z2v_id_of_eq; reflexivity | split].
    + unfold z2v_dvd_t. cbn [Nat.pow]. rewrite Nat.mod_1_r. apply hl_idrefl.
    + unfold z2v_dvd_t. cbn [Nat.pow]. rewrite Nat.mod_1_r. apply hl_idrefl.
  - assert (Hp0 : p <> 0) by (pose proof (NatLe_drop _ _ (fst Hpp)); lia).
    assert (Hp1 : Nat.divide p (x * y)).
    { apply (hl_div_trans p (p ^ S c) (x * y)); [| exact Hd].
      exists (p ^ c). rewrite Nat.pow_succ_r'. apply Nat.mul_comm. }
    destruct (plm_prime_dvd_mul p x y Hpp Hp1) as [Hdx | Hdy].
    + assert (Hxm : x mod p = 0).
      { exact (z2v_idS_eq _ _ _ (pr_dvd_mod0 p x ltac:(lia) Hdx)). }
      assert (Hxq : x = p * (x / p))
        by (pose proof (Nat.div_mod_eq x p) as Hdm;
            rewrite Hxm in Hdm; rewrite Nat.add_0_r in Hdm; exact Hdm).
      assert (Hdc : Nat.divide (p ^ c) ((x / p) * y)).
      { destruct Hd as [t Ht]. exists t.
        pose proof (Nat.pow_succ_r' p c) as HpS. rewrite HpS in Ht.
        rewrite Hxq in Ht.
        apply (proj1 (Nat.mul_cancel_r ((x / p) * y) (t * p ^ c) p Hp0)).
        replace ((x / p) * y * p) with (p * (x / p) * y) by ring.
        rewrite Ht. ring. }
      destruct (IH (x / p) y Hpp Hdc) as [c1 [c2 [Heq [Hd1 Hd2]]]].
      pose proof (hl_id_eq _ _ _ Heq) as HeqP.
      exists (S c1), c2. split; [apply z2v_id_of_eq; lia | split].
      * unfold z2v_dvd_t. apply z2v_id_of_eq.
        assert (Hxt : Nat.divide (p ^ S c1) x).
        { rewrite Hxq.
          destruct (pr_mod0_dvd (p ^ c1) (x / p)
                      ltac:(pose proof (Nat.pow_nonzero p c1 Hp0); lia)
                      (hl_id_eq _ _ _ Hd1)) as [q Hq].
          exists q. rewrite Hq, Nat.pow_succ_r'. ring. }
        exact (z2v_idS_eq _ _ _
                 (pr_dvd_mod0 (p ^ S c1) x
                    ltac:(pose proof (Nat.pow_nonzero p (S c1) Hp0); lia)
                    Hxt)).
      * exact Hd2.
    + assert (Hym : y mod p = 0).
      { exact (z2v_idS_eq _ _ _ (pr_dvd_mod0 p y ltac:(lia) Hdy)). }
      assert (Hyq : y = p * (y / p))
        by (pose proof (Nat.div_mod_eq y p) as Hdm;
            rewrite Hym in Hdm; rewrite Nat.add_0_r in Hdm; exact Hdm).
      assert (Hdc : Nat.divide (p ^ c) (x * (y / p))).
      { destruct Hd as [t Ht]. exists t.
        pose proof (Nat.pow_succ_r' p c) as HpS. rewrite HpS in Ht.
        rewrite Hyq in Ht.
        apply (proj1 (Nat.mul_cancel_r (x * (y / p)) (t * p ^ c) p Hp0)).
        replace (x * (y / p) * p) with (x * (p * (y / p))) by ring.
        rewrite Ht. ring. }
      destruct (IH x (y / p) Hpp Hdc) as [c1 [c2 [Heq [Hd1 Hd2]]]].
      pose proof (hl_id_eq _ _ _ Heq) as HeqP.
      exists c1, (S c2). split; [apply z2v_id_of_eq; lia | split].
      * exact Hd1.
      * unfold z2v_dvd_t. apply z2v_id_of_eq.
        assert (Hyt : Nat.divide (p ^ S c2) y).
        { rewrite Hyq.
          destruct (pr_mod0_dvd (p ^ c2) (y / p)
                      ltac:(pose proof (Nat.pow_nonzero p c2 Hp0); lia)
                      (hl_id_eq _ _ _ Hd2)) as [q Hq].
          exists q. rewrite Hq, Nat.pow_succ_r'. ring. }
        exact (z2v_idS_eq _ _ _
                 (pr_dvd_mod0 (p ^ S c2) y
                    ltac:(pose proof (Nat.pow_nonzero p (S c2) Hp0); lia)
                    Hyt)).
Qed.

(* Valuation additivity: [v_p(x*y) = v_p(x) + v_p(y)] for [x, y >= 1],
   [p] prime.  Lower side: [p^{a+b} | x*y] while [p^{v+1} ∤ x*y]
   squeezes; upper side: [p^{S(a+b)} | x*y] and the power split give *)
(* [p^{S a} | x] or [p^{S b} | y], contradicting maximality.        *)
Lemma z2v_v_add : forall p x y : nat,
  pr_prime p -> 1 <= x -> 1 <= y ->
  hl_id (plm_v p (x * y)) (plm_v p x + plm_v p y).
Proof.
  intros p x y Hpp Hx Hy. apply z2v_id_of_eq.
  pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2. assert (Hp1lt : 1 < p) by lia.
  assert (Hp0 : p <> 0) by lia.
  assert (Hxy1 : 1 <= x * y) by lia.
  pose proof (plm_v_dvd p (x * y)) as Hdxy.
  pose proof (plm_v_max p (x * y) Hp1lt Hxy1) as Hndxy.
  pose proof (plm_v_dvd p x) as Hdx.
  pose proof (plm_v_max p x Hp1lt Hx) as Hndx.
  pose proof (plm_v_dvd p y) as Hdy.
  pose proof (plm_v_max p y Hp1lt Hy) as Hndy.
  assert (Hge : plm_v p x + plm_v p y <= plm_v p (x * y)).
  { destruct (Nat.le_gt_cases (plm_v p x + plm_v p y) (plm_v p (x * y))) as [H|H];
      [exact H |].
    exfalso. apply Hndxy.
    apply (hl_div_trans (p ^ S (plm_v p (x * y)))
             (p ^ (plm_v p x + plm_v p y)) (x * y)).
    - apply z2v_pow_dvd. lia.
    - rewrite Nat.pow_add_r.
      destruct Hdx as [w1 Hw1]. destruct Hdy as [w2 Hw2].
      exists (w1 * w2).
      rewrite Hw1 at 1. rewrite Hw2 at 1. ring. }
  assert (Hle : plm_v p (x * y) <= plm_v p x + plm_v p y).
  { destruct (Nat.le_gt_cases (plm_v p (x * y)) (plm_v p x + plm_v p y)) as [H|H];
      [exact H |].
    exfalso.
    assert (Hd2 : Nat.divide (p ^ S (plm_v p x + plm_v p y)) (x * y)).
    { apply (hl_div_trans (p ^ S (plm_v p x + plm_v p y))
               (p ^ plm_v p (x * y)) (x * y)).
      - apply z2v_pow_dvd. lia.
      - exact Hdxy. }
    destruct (z2v_pow_split p (S (plm_v p x + plm_v p y)) x y Hpp Hd2)
      as [c1 [c2 [Hc [Hc1 Hc2]]]].
    pose proof (hl_id_eq _ _ _ Hc) as HcP.
    assert (Hc1a : c1 <= plm_v p x).
    { destruct (Nat.le_gt_cases c1 (plm_v p x)) as [Hk1|Hgt]; [exact Hk1 |].
      exfalso. apply Hndx.
      apply (hl_div_trans (p ^ S (plm_v p x)) (p ^ c1) x).
      - apply z2v_pow_dvd. lia.
      - apply (pr_mod0_dvd (p ^ c1) x).
        + pose proof (Nat.pow_nonzero p c1 Hp0). lia.
        + exact (hl_id_eq _ _ _ Hc1). }
    assert (Hc2b : c2 <= plm_v p y).
    { destruct (Nat.le_gt_cases c2 (plm_v p y)) as [Hk2|Hgt]; [exact Hk2 |].
      exfalso. apply Hndy.
      apply (hl_div_trans (p ^ S (plm_v p y)) (p ^ c2) y).
      - apply z2v_pow_dvd. lia.
      - apply (pr_mod0_dvd (p ^ c2) y).
        + pose proof (Nat.pow_nonzero p c2 Hp0). lia.
        + exact (hl_id_eq _ _ _ Hc2). }
    lia. }
  lia.
Qed.

(* ============================================================ *)
(* Section 3 - the Legendre identity (exact:                       *)
(*   [plm_v p (fact m) = z2v_leg p K m])                           *)
(* ============================================================ *)

(* Layer increment: [S m / d = m / d + [d divides S m]] - the       *)
(* quotient jumps at a layer boundary exactly by the indicator.     *)
Lemma z2v_inc : forall m d : nat,
  1 <= d ->
  hl_id (S m / d) (m / d + (if Nat.eqb (S m mod d) 0 then 1 else 0)).
Proof.
  intros m d Hd. apply z2v_id_of_eq. destruct d as [| d'].
  - lia.
  - pose proof (Nat.div_mod_eq m (S d')) as Hdm.
    pose proof (Nat.mod_upper_bound m (S d') ltac:(lia)) as Hlt.
    destruct (Nat.eq_dec (m mod S d' + 1) (S d')) as [Ecase|Ecase].
    + (* full-layer case: [r + 1 = d], so [d] divides [S m]. *)
      assert (HSm : S m = S d' * S (m / S d')).
      { rewrite Hdm at 1. rewrite <- Nat.add_1_r, <- Nat.add_assoc, Ecase.
        rewrite (Nat.mul_succ_r (S d') (m / S d')). reflexivity. }
      rewrite HSm. rewrite (Nat.mul_comm (S d') (S (m / S d'))).
      rewrite Nat.div_mul by lia. rewrite Nat.mod_mul by lia.
      rewrite Nat.eqb_refl. change (if true then 1 else 0) with 1. lia.
    + (* partial-layer case: [r + 1 < d], the quotient is unchanged   *)
      (* and the remainder is nonzero.                                *)
      assert (Hne : m mod S d' + 1 <> 0) by lia.
      assert (HSm : S m = S d' * (m / S d') + (m mod S d' + 1)).
      { rewrite Hdm at 1. rewrite <- Nat.add_1_r. lia. }
      rewrite HSm.
      rewrite (Nat.add_comm (S d' * (m / S d')) (m mod S d' + 1)).
      rewrite (Nat.mul_comm (S d') (m / S d')).
      rewrite (Nat.div_add (m mod S d' + 1) (m / S d') (S d')) by lia.
      rewrite (Nat.mod_add (m mod S d' + 1) (m / S d') (S d')) by lia.
      rewrite (Nat.div_small (m mod S d' + 1) (S d')) by lia.
      rewrite (Nat.mod_small (m mod S d' + 1) (S d')) by lia.
      pose proof (proj2 (Nat.eqb_neq (m mod S d' + 1) 0) Hne) as Eeqb.
      rewrite Eeqb. change (if false then 1 else 0) with 0. lia.
Qed.

(* Incremental form of the Legendre sum: [z2v_leg p K (S m) =       *)
(* z2v_leg p K m + the layer count].                                *)
Lemma z2v_leg_cnt : forall p K m : nat,
  1 <= p ->
  hl_id (z2v_leg p K (S m)) (z2v_leg p K m + z2v_cnt p K (S m)).
Proof.
  intros p K m Hp. apply z2v_id_of_eq. induction K as [| K IH].
  - reflexivity.
  - cbn [z2v_leg z2v_cnt]. rewrite IH.
    assert (HleK : 1 <= p ^ S K)
      by (exact (hl_le_t_to_le _ _ (z2v_pow_pos p (S K) Hp))).
    pose proof (hl_id_eq _ _ _ (z2v_inc m (p ^ S K) HleK)) as Hinc.
    rewrite Hinc. lia.
Qed.

(* Minimum form of the layer count: [z2v_cnt p K t = min K          *)
(* (plm_v p t)].  Cases: if [p^{S K} | t] then [S K <= v] and all K *)
(* layers count; otherwise [v < S K] and exactly v layers count.    *)
Lemma z2v_cnt_min : forall p K t : nat,
  pr_prime p -> 1 <= t -> hl_id (z2v_cnt p K t) (Nat.min K (plm_v p t)).
Proof.
  intros p K t Hpp Ht. apply z2v_id_of_eq. pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  assert (Hp1lt : 1 < p) by lia.
  induction K as [| K IH].
  - reflexivity.
  - cbn [z2v_cnt]. rewrite IH.
    destruct (Nat.eqb (t mod p ^ S K) 0) eqn:Em.
    + apply Nat.eqb_eq in Em.
      assert (Hdv : Nat.divide (p ^ S K) t)
        by (apply (pr_mod0_dvd (p ^ S K) t);
            [pose proof (hl_le_t_to_le _ _ (z2v_pow_pos p (S K) ltac:(lia))); lia
            | exact Em]).
      assert (HKv : S K <= plm_v p t).
      { destruct (Nat.le_gt_cases (S K) (plm_v p t)) as [H|H]; [exact H|].
        exfalso. apply (plm_v_max p t Hp1lt Ht).
        apply (hl_div_trans (p ^ S (plm_v p t)) (p ^ S K) t).
        - apply z2v_pow_dvd. lia.
        - exact Hdv. }
      rewrite (Nat.min_l K (plm_v p t)) by lia.
      rewrite (Nat.min_l (S K) (plm_v p t)) by lia.
      change (if true then 1 else 0) with 1. lia.
    + apply Nat.eqb_neq in Em.
      assert (Hndv : Nat.divide (p ^ S K) t -> False).
      { intro Hdv. apply Em.
        exact (z2v_idS_eq _ _ _ (pr_dvd_mod0 (p ^ S K) t
                   ltac:(pose proof (hl_le_t_to_le _ _
                           (z2v_pow_pos p (S K) ltac:(lia))); lia)
                   Hdv)). }
      assert (HKv : plm_v p t <= K).
      { destruct (Nat.le_gt_cases (plm_v p t) K) as [H|H]; [exact H|].
        exfalso. apply Hndv.
        apply (hl_div_trans (p ^ S K) (p ^ plm_v p t) t).
        - apply z2v_pow_dvd. lia.
        - apply (plm_v_dvd p t). }
      rewrite (Nat.min_r K (plm_v p t)) by lia.
      rewrite (Nat.min_r (S K) (plm_v p t)) by lia.
      change (if false then 1 else 0) with 0. lia.
Qed.

(* The exact Legendre identity: [p^K > m] gives [v_p(m!) =           *)
(* sum_{i<K} floor(m/p^{i+1})].  Induction on [m]: [v_p((S m)!) =     *)
(* v_p(S m) + v_p(m!)] by additivity, and the layer-sum increment    *)
(* equals the layer count [min(K, v_p(S m)) = v_p(S m)] (since       *)
(* [v_p(S m) < K] follows from [p^K > S m]).                         *)
Lemma z2v_fact_ex : forall p m K : nat,
  pr_prime p -> p ^ K > m -> hl_id (plm_v p (fact m)) (z2v_leg p K m).
Proof.
  intros p m K Hpp. revert K.
  induction m as [| m IH]; intros K HK; apply z2v_id_of_eq.
  - cbn [fact]. assert (Hp1lt : 1 < p) by (pose proof (NatLe_drop _ _ (fst Hpp)); lia).
    pose proof (hl_id_eq _ _ _ (z2v_v_1 p Hp1lt)) as Hv1.
    pose proof (hl_id_eq _ _ _ (z2v_leg_0 p K)) as Hl0.
    rewrite Hv1, Hl0. reflexivity.
  - pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
    assert (HKm : p ^ K > m) by lia.
    assert (HvK : plm_v p (S m) < K).
    { destruct (Nat.le_gt_cases K (plm_v p (S m))) as [Hle|Hgt].
      - exfalso.
        pose proof (plm_v_dvd p (S m)) as Hdv.
        pose proof (Nat.divide_pos_le (p ^ plm_v p (S m)) (S m)
                      ltac:(lia) Hdv) as Hle1.
        pose proof (Nat.pow_le_mono_r p K (plm_v p (S m))
                      ltac:(lia) Hle) as Hpw.
        lia.
      - exact Hgt. }
    cbn [fact].
    pose proof (hl_id_eq _ _ _ (z2v_v_add p (S m) (fact m) Hpp ltac:(lia)
                  (hl_le_t_to_le _ _ (h3_fact_pos m)))) as Hvadd.
    rewrite Hvadd.
    rewrite (IH K HKm).
    pose proof (hl_id_eq _ _ _ (z2v_leg_cnt p K m
                  ltac:(pose proof (NatLe_drop _ _ (fst Hpp)); lia))) as Hlc.
    rewrite Hlc.
    pose proof (hl_id_eq _ _ _ (z2v_cnt_min p K (S m) Hpp ltac:(lia))) as Hcm.
    rewrite Hcm.
    rewrite (Nat.min_r K (plm_v p (S m))) by lia.
    lia.
Qed.

(* ============================================================ *)
(* Section 4 - the denominator product's layer bound (nested       *)
(*   division) and the divisibility face                           *)
(* ============================================================ *)

(* Layer-shift identity of the layer sum: advancing [k] by one      *)
(* increments the layer sum exactly by the Legendre sum of the new  *)
(* denominator factor - applying nested division                    *)
(* [floor(floor(n/p^j)/a) = floor(n/(a*p^j)) =                      *)
(* floor(floor(n/a)/p^j)] layer by layer.                           *)
Lemma z2v_lsum_S_k : forall p K k n : nat,
  1 <= p ->
  hl_id (z2v_lsum p K (S k) n)
        (z2v_lsum p K k n + z2v_leg p K (n / z2d_sylv_a k)).
Proof.
  intros p K k n Hp. apply z2v_id_of_eq. induction K as [| K IH].
  - reflexivity.
  - cbn [z2v_lsum z2v_leg]. rewrite IH. cbn [z2d_sylv_sum].
    assert (Hpk : p ^ S K <> 0)
      by (pose proof (Nat.pow_nonzero p (S K) ltac:(lia)); lia).
    assert (E : (n / p ^ S K) / z2d_sylv_a k = (n / z2d_sylv_a k) / p ^ S K).
    { rewrite (Nat.div_div n (z2d_sylv_a k) (p ^ S K))
        by (first [apply z2d_sylv_a_neq0 | exact Hpk]).
      rewrite (Nat.div_div n (p ^ S K) (z2d_sylv_a k))
        by (first [exact Hpk | apply z2d_sylv_a_neq0]).
      rewrite (Nat.mul_comm (p ^ S K) (z2d_sylv_a k)). reflexivity. }
    lia.
Qed.

(* Valuation upper bound for the denominator product:               *)
(* [v_p(prod_{j<k} floor(n/a_{j+1})!) <=                            *)
(* sum_{i<K} z2d_sylv_sum k floor(n/p^{i+1})] - each denominator    *)
(* factor's exact Legendre sum is folded layer-wise into the        *)
(* Sylvester sums by the layer-shift identity.                      *)
Lemma z2v_den_val : forall p k n K : nat,
  pr_prime p -> p ^ K > n ->
  hl_le_t (plm_v p (z2v_den k n)) (z2v_lsum p K k n).
Proof.
  intros p k. induction k as [| k IH]; intros n K Hpp HK.
  - apply hl_le_to_le_t. cbn [z2v_den z2v_lsum].
    assert (Hp1lt : 1 < p) by (pose proof (NatLe_drop _ _ (fst Hpp)); lia).
    pose proof (hl_id_eq _ _ _ (z2v_v_1 p Hp1lt)) as Hv1. rewrite Hv1. lia.
  - apply hl_le_to_le_t.
    assert (Ha0 : z2d_sylv_a k <> 0) by apply z2d_sylv_a_neq0.
    assert (Ha1 : 1 <= z2d_sylv_a k) by lia.
    assert (Hle : n / z2d_sylv_a k <= n).
    { apply Nat.div_le_upper_bound; [exact Ha0 |].
      pose proof (Nat.mul_le_mono_r 1 (z2d_sylv_a k) n Ha1) as Hm.
      rewrite Nat.mul_1_l in Hm. exact Hm. }
    assert (HKm : p ^ K > n / z2d_sylv_a k) by lia.
    pose proof (hl_id_eq _ _ _ (z2v_lsum_S_k p K k n
                  ltac:(pose proof (NatLe_drop _ _ (fst Hpp)); lia))) as Hls.
    rewrite Hls.
    pose proof (hl_id_eq _ _ _ (z2v_v_add p (z2v_den k n)
                  (fact (n / z2d_sylv_a k)) Hpp
                  (hl_le_t_to_le _ _ (z2v_den_pos k n))
                  (hl_le_t_to_le _ _ (h3_fact_pos (n / z2d_sylv_a k))))) as Vadd.
    pose proof (hl_le_t_to_le _ _ (IH n K Hpp HK)) as VIH.
    pose proof (hl_id_eq _ _ _ (z2v_fact_ex p (n / z2d_sylv_a k) K Hpp HKm)) as Vex.
    cbn [z2v_den]. lia.
Qed.

(* Layer-wise pointwise Sylvester inequality: the layer indicator   *)
(* plus the layer Sylvester sum does not exceed the layer quotient  *)
(* (full strength of [z2d_sylv_floor_t] at [s >= 1]; at [s = 0]     *)
(* both sides vanish).                                              *)
Lemma z2v_pointwise : forall k s : nat,
  hl_le_t ((if Nat.leb 1 s then 1 else 0) + z2d_sylv_sum k s) s.
Proof.
  intros k s. apply hl_le_to_le_t. destruct (Nat.leb 1 s) eqn:E.
  - apply Nat.leb_le in E. change (if true then 1 else 0) with 1.
    pose proof (hl_le_t_to_le (z2d_sylv_sum k s + 1) s
                  (z2d_sylv_floor_t k s E)). lia.
  - apply Nat.leb_nle in E. change (if false then 1 else 0) with 0.
    assert (Hs0 : s = 0) by lia. subst s.
    rewrite z2v_sylv_sum_0. lia.
Qed.

(* Layer-sum closure: [sum_{i<K} [floor(n/p^{i+1}) >= 1] +          *)
(* sum_{i<K} z2d_sylv_sum k floor(n/p^{i+1}) <=                     *)
(* sum_{i<K} floor(n/p^{i+1})] - the pointwise inequality summed    *)
(* over layers.                                                     *)
Lemma z2v_layersum_bound : forall p K k n : nat,
  hl_le_t (z2v_lsum p K k n + z2v_pc p K n) (z2v_leg p K n).
Proof.
  intros p K k n. apply hl_le_to_le_t. induction K as [| K IH].
  - cbn [z2v_lsum z2v_pc z2v_leg]. lia.
  - cbn [z2v_lsum z2v_pc z2v_leg].
    pose proof (hl_le_t_to_le _ _ (z2v_pointwise k (n / p ^ S K))). lia.
Qed.

(* Lower bound for the layer count: [p^e <= n] and [e <= K] give    *)
(* [e <= #{i < K : p^{i+1} <= n}].                                  *)
Lemma z2v_pc_ge : forall p K e n : nat,
  1 < p -> p ^ e <= n -> e <= K -> hl_le_t e (z2v_pc p K n).
Proof.
  intros p K. induction K as [| K IH]; intros e n Hp He HKe;
    apply hl_le_to_le_t.
  - lia.
  - assert (Hp0 : p <> 0) by lia.
    destruct (Nat.eq_dec e (S K)) as [E|NE].
    + subst e. cbn [z2v_pc].
      assert (H1 : 1 <= n / p ^ S K).
      { destruct (n / p ^ S K) eqn:Eq.
        - exfalso.
          pose proof (Nat.div_mod_eq n (p ^ S K)) as Hdm. rewrite Eq in Hdm.
          pose proof (Nat.mod_upper_bound n (p ^ S K)
                        (Nat.pow_nonzero p (S K) Hp0)) as Hmb.
          lia.
        - lia. }
      pose proof (proj2 (Nat.leb_le 1 (n / p ^ S K)) H1) as Elb.
      rewrite Elb. change (if true then 1 else 0) with 1.
      assert (HpK : p ^ K <= n).
      { pose proof (Nat.pow_le_mono_r p K (S K) Hp0 (Nat.le_succ_diag_r K)).
        lia. }
      pose proof (hl_le_t_to_le _ _ (IH K n Hp HpK (Nat.le_refl K))). lia.
    + cbn [z2v_pc].
      pose proof (hl_le_t_to_le _ _ (IH e n Hp He ltac:(lia))). lia.
Qed.

(* Two-factor factorial split: [fact (a + b) = fact b *             *)
(* h3_prod_from (S b) a] - the stepping identity on the interval    *)
(* product ([h3_prod_binom_fact] gives the binomial-coefficient     *)
(* form).                                                           *)
Lemma z2v_fact_split : forall a b : nat,
  hl_id (fact (a + b)) (fact b * h3_prod_from (S b) a).
Proof.
  intros a b. apply z2v_id_of_eq. induction a as [| a IH].
  - rewrite Nat.mul_1_r. reflexivity.
  - replace (S a + b) with (S (a + b)) by lia.
    cbn [fact h3_prod_from]. rewrite IH.
    replace (S b + a) with (S (b + a)) by lia. ring.
Qed.

(* Denominator-product divisibility (general form): if              *)
(* [sum_{j<k} floor(n/a_{j+1}) + s <= n], then                      *)
(* [prod_{j<k} floor(n/a_{j+1})! * s! divides (s + sum)!] -         *)
(* telescoping factor by factor with binomial coefficients as       *)
(* witnesses (induction invariant: the denominator product times    *)
(* the residual factorial divides the total factorial).             *)
Lemma z2v_den_dvd_gen : forall k n s : nat,
  s + z2d_sylv_sum k n <= n ->
  Nat.divide (z2v_den k n * fact s) (fact (s + z2d_sylv_sum k n)).
Proof.
  induction k as [| k IH]; intros n s Hs.
  - cbn [z2v_den z2d_sylv_sum]. rewrite Nat.add_0_r.
    exists 1. rewrite Nat.mul_1_l. ring.
  - cbn [z2v_den z2d_sylv_sum]. cbn [z2d_sylv_sum] in Hs.
    assert (Hstep : Nat.divide
              (fact (n / z2d_sylv_a k) * fact s)
              (fact (s + n / z2d_sylv_a k))).
    { pose proof (z2v_fact_split (n / z2d_sylv_a k) s) as Hfs.
      rewrite (Nat.add_comm (n / z2d_sylv_a k) s) in Hfs.
      pose proof (hl_id_eq _ _ _
                    (h3_prod_binom_fact s (n / z2d_sylv_a k))) as Hpb.
      rewrite Hpb in Hfs.
      exists (hl_binom (s + n / z2d_sylv_a k) (n / z2d_sylv_a k)).
      rewrite Hfs. ring. }
    assert (Hcomb : Nat.divide
              ((z2v_den k n * fact (n / z2d_sylv_a k)) * fact s)
              (z2v_den k n * fact (s + n / z2d_sylv_a k))).
    { destruct Hstep as [w Hw]. exists w.
      rewrite Hw. ring. }
    assert (HIH : Nat.divide
              (z2v_den k n * fact (s + n / z2d_sylv_a k))
              (fact ((s + n / z2d_sylv_a k) + z2d_sylv_sum k n))).
    { apply IH. lia. }
    rewrite <- Nat.add_assoc in HIH.
    rewrite (Nat.add_comm (n / z2d_sylv_a k) (z2d_sylv_sum k n)) in HIH.
    apply (hl_div_trans
             ((z2v_den k n * fact (n / z2d_sylv_a k)) * fact s)
             (z2v_den k n * fact (s + n / z2d_sylv_a k))
             (fact (s + (z2d_sylv_sum k n + n / z2d_sylv_a k)))).
    + exact Hcomb.
    + exact HIH.
Qed.

(* Denominator-product divisibility (main form): [1 <= n] gives     *)
(* [prod_{j<=n} floor(n/a_{j+1})! | n!] - take [s = n - sum] (the   *)
(* Sylvester dense inequality gives [sum + 1 <= n], hence           *)
(* [s + sum = n]).                                                  *)
Lemma z2v_den_dvd : forall n : nat,
  1 <= n -> Nat.divide (z2v_den n n) (fact n).
Proof.
  intros n Hn.
  pose proof (hl_le_t_to_le (z2d_sylv_sum n n + 1) n
                (z2d_sylv_floor_t n n Hn)) as Hfl.
  pose proof (z2v_den_dvd_gen n n (n - z2d_sylv_sum n n) ltac:(lia)) as Hd.
  rewrite (Nat.sub_add (z2d_sylv_sum n n) n ltac:(lia)) in Hd.
  destruct Hd as [t Ht].
  exists (t * fact (n - z2d_sylv_sum n n)). rewrite Ht. ring.
Qed.

(* ============================================================ *)
(* Section 5 - the per-prime theorem: the layer count is at most   *)
(*   [v_p(C(n))] (layer-wise comparison closing up)                *)
(* ============================================================ *)

(* Per-prime main chain: [z2v_pc p (S n) n <= plm_v p (C n)].       *)
(* Chain order: [fact n = C n * den] (the exact equation of the     *)
(* denominator-divisibility face), so [v_p(fact n) = v_p(den) +     *)
(* v_p(C n)] by additivity; [v_p(fact n) = z2v_leg p (S n) n] (the  *)
(* exact Legendre identity); [v_p(den) <= z2v_lsum] (the            *)
(* denominator layer bound); [z2v_lsum + z2v_pc <= z2v_leg] (the    *)
(* layer-wise comparison closure).                                  *)
Theorem z2v_v_C_ge : forall p n : nat,
  pr_prime p -> 1 <= n -> hl_le_t (z2v_pc p (S n) n) (plm_v p (z2v_C n)).
Proof.
  intros p n Hpp Hn. apply hl_le_to_le_t. pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  pose proof (z2v_den_dvd n Hn) as Hdd.
  pose proof (hl_le_t_to_le _ _ (z2v_den_pos n n)) as Hdenpos.
  assert (Heq : fact n = z2v_den n n * z2v_C n).
  { unfold z2v_C.
    pose proof (z2v_idS_eq _ _ _
                  (pr_dvd_mod0 (z2v_den n n) (fact n) Hdenpos Hdd)) as Hm0.
    pose proof (Nat.div_mod_eq (fact n) (z2v_den n n)) as Hdm.
    rewrite Hm0, Nat.add_0_r in Hdm. exact Hdm. }
  assert (HCpos : 1 <= z2v_C n).
  { destruct (z2v_C n) eqn:EC.
    - exfalso. rewrite Nat.mul_0_r in Heq.
      pose proof (hl_le_t_to_le _ _ (h3_fact_pos n)). lia.
    - lia. }
  assert (Hgt : p ^ S n > n).
  { pose proof (Nat.pow_gt_lin_r p n Hp2) as H1.
    pose proof (Nat.pow_le_mono_r p n (S n)
                  ltac:(lia) (Nat.le_succ_diag_r n)) as H2. lia. }
  pose proof (hl_id_eq _ _ _
                (z2v_v_add p (z2v_den n n) (z2v_C n) Hpp Hdenpos HCpos)) as V1.
  rewrite <- Heq in V1.
  pose proof (hl_id_eq _ _ _ (z2v_fact_ex p n (S n) Hpp Hgt)) as V2.
  pose proof (hl_le_t_to_le _ _ (z2v_den_val p n n (S n) Hpp Hgt)) as V3.
  pose proof (hl_le_t_to_le _ _ (z2v_layersum_bound p (S n) n n)) as V4.
  lia.
Qed.

(* Prime powers divide C(n): [p^e <= n] gives [p^e | C(n)] - the    *)
(* usable form of Hanson's Lemma 2 ([e <= floor(log_p n) = the      *)
(* layer count <= v_p(C n)], transported by power monotonicity).    *)
Theorem z2v_ppow_dvd_C : forall p e n : nat,
  pr_prime p -> p ^ e <= n -> Nat.divide (p ^ e) (z2v_C n).
Proof.
  intros p e n Hpp He. pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2.
  assert (Hp1lt : 1 < p) by lia.
  assert (Hen : e <= S n) by (pose proof (Nat.pow_gt_lin_r p e Hp1lt); lia).
  assert (Hn1 : 1 <= n)
    by (pose proof (hl_le_t_to_le _ _ (z2v_pow_pos p e ltac:(lia))); lia).
  pose proof (hl_le_t_to_le _ _ (z2v_pc_ge p (S n) e n Hp1lt He Hen)) as Hpc.
  pose proof (hl_le_t_to_le _ _ (z2v_v_C_ge p n Hpp Hn1)) as V.
  apply (hl_div_trans (p ^ e) (p ^ plm_v p (z2v_C n)) (z2v_C n)).
  - apply z2v_pow_dvd. lia.
  - apply (plm_v_dvd p (z2v_C n)).
Qed.

(* ============================================================ *)
(* Section 6 - whole-number divisibility and the main theorem:     *)
(*   [B(n) = hl_lcm_upto n] divides [C(n)]                         *)
(* ============================================================ *)

(* Two-way factor split for prime powers: [d | p^e] gives [d = 1]   *)
(* or [p | d] (cancelling the prime layer by layer).                *)
Lemma z2v_dvd_pow_split : forall p e d : nat,
  pr_prime p -> hl_id ((p ^ e) mod d) 0 -> hl_id d 1 + z2v_dvd_t p d.
Proof.
  intros p e. induction e as [| e IH]; intros d Hpp Hd.
  - cbn [Nat.pow] in Hd.
    destruct d as [| d'].
    + right. unfold z2v_dvd_t. rewrite Nat.Div0.mod_0_l. apply hl_idrefl.
    + pose proof (hl_id_eq _ _ _ Hd) as Hm0.
      assert (Hd1 : S d' = 1).
      { pose proof (pr_mod0_dvd (S d') 1 ltac:(lia) Hm0) as Hdiv.
        destruct Hdiv as [z Hz].
        pose proof (proj1 (Nat.mul_eq_1 z (S d')) (eq_sym Hz)) as [Hz1 Hz2].
        exact Hz2. }
      left. apply z2v_id_of_eq. exact Hd1.
  - assert (Hp0 : p <> 0) by (pose proof (NatLe_drop _ _ (fst Hpp)); lia).
    assert (Hdpos : 1 <= d).
    { destruct d as [| d'].
      - exfalso. pose proof (hl_id_eq _ _ _ Hd) as Hmz.
        rewrite Nat.mod_0_r in Hmz.
        pose proof (Nat.pow_nonzero p (S e) Hp0). lia.
      - lia. }
    pose proof (hl_id_eq _ _ _ Hd) as Hm0.
    pose proof (pr_mod0_dvd d (p ^ S e) ltac:(exact Hdpos) Hm0) as Hdd.
    assert (Hzeq : p ^ S e = (p ^ S e / d) * d)
      by (pose proof (Nat.div_mod_eq (p ^ S e) d) as Hdm;
          rewrite Hm0, Nat.add_0_r in Hdm;
          rewrite (Nat.mul_comm d (p ^ S e / d)) in Hdm; exact Hdm).
    assert (Hpzd : Nat.divide p ((p ^ S e / d) * d)).
    { exists (p ^ e). rewrite <- Hzeq, Nat.pow_succ_r'. ring. }
    destruct (plm_prime_dvd_mul p (p ^ S e / d) d Hpp Hpzd) as [Hdz | Hdd2].
    + assert (Hd' : Nat.divide d (p ^ e)).
      { destruct Hdz as [w Hw].
        exists w.
        apply (proj1 (Nat.mul_cancel_r (p ^ e) (w * d) p Hp0)).
        rewrite (Nat.mul_comm (p ^ e) p).
        change (p * p ^ e) with (p ^ S e).
        rewrite Hzeq, Hw. ring. }
      assert (Hin : hl_id ((p ^ e) mod d) 0).
      { apply z2v_id_of_eq.
        exact (z2v_idS_eq _ _ _ (pr_dvd_mod0 d (p ^ e) Hdpos Hd')). }
      destruct (IH d Hpp Hin) as [Hi | Hid].
      * left. exact Hi.
      * right. exact Hid.
    + right. unfold z2v_dvd_t. apply z2v_id_of_eq.
      exact (z2v_idS_eq _ _ _ (pr_dvd_mod0 p d ltac:(lia) Hdd2)).
Qed.

(* Coprimality of a prime power with [u]: [p] prime and [p] not     *)
(* dividing [u] give [gcd(p^e, u) = 1].                             *)
Lemma z2v_gcd_pow_prime : forall p e u : nat,
  pr_prime p -> (Nat.divide p u -> False) ->
  hl_id (Nat.gcd (p ^ e) u) 1.
Proof.
  intros p e u Hpp Hu.
  assert (Hp0 : p <> 0) by (pose proof (NatLe_drop _ _ (fst Hpp)); lia).
  pose proof (Nat.gcd_divide_l (p ^ e) u) as Hgl.
  assert (Hgcd : 1 <= Nat.gcd (p ^ e) u).
  { destruct (Nat.eq_dec (Nat.gcd (p ^ e) u) 0) as [Ez | NEz]; [| lia].
    exfalso.
    destruct Hgl as [z Hz]. rewrite Ez in Hz.
    pose proof (Nat.pow_nonzero p e Hp0). lia. }
  assert (Hin : hl_id ((p ^ e) mod Nat.gcd (p ^ e) u) 0).
  { apply z2v_id_of_eq.
    exact (z2v_idS_eq _ _ _ (pr_dvd_mod0 (Nat.gcd (p ^ e) u) (p ^ e)
               Hgcd Hgl)). }
  destruct (z2v_dvd_pow_split p e (Nat.gcd (p ^ e) u) Hpp Hin) as [H1 | Hpd].
  - exact H1.
  - exfalso. apply Hu.
    apply (hl_div_trans p (Nat.gcd (p ^ e) u) u).
    + apply (pr_mod0_dvd p (Nat.gcd (p ^ e) u));
        [pose proof (NatLe_drop _ _ (fst Hpp)); lia
        | exact (hl_id_eq _ _ _ Hpd)].
    + apply Nat.gcd_divide_r.
Qed.

(* Whole-number divisibility (strong induction): [1 <= m <= n]      *)
(* gives [m | C(n)].  Induction step: the factorization witness     *)
(* yields a prime [p] with [m = p^e * u] ([e = v_p(m)] the full     *)
(* power, [u] coprime to [p]); [u | C(n)] by induction and          *)
(* [p^e | C(n)] by the prime-power theorem, combined through        *)
(* multiplicative divisibility at [gcd = 1]; [m = 1] is immediate.  *)
Theorem z2v_m_dvd_C : forall m n : nat,
  1 <= m -> m <= n -> Nat.divide m (z2v_C n).
Proof.
  intro m. induction m as [m IH] using (well_founded_induction_type Wf_nat.lt_wf).
  intros n Hm1 Hmn. destruct m as [| m'].
  - lia.
  - destruct (Nat.eq_dec (S m') 1) as [E1|NE1].
    + rewrite E1. apply Nat.divide_1_l.
    + assert (Hm2 : 2 <= S m') by lia.
      destruct (pr_factor_exists (S m') Hm2) as [l [Hprim Hfold]].
      destruct l as [| p rest].
      * cbn [fold_right] in Hfold.
        pose proof (z2v_idS_eq _ _ _ Hfold) as HfoldP. lia.
      * pose proof (Hprim p (or_introl eq_refl)) as Hpp.
        pose proof (NatLe_drop _ _ (fst Hpp)) as Hp2. assert (Hp1lt : 1 < p) by lia.
        cbn [fold_right] in Hfold.
        set (m0 := fold_right Nat.mul 1 rest) in Hfold.
        pose proof (z2v_idS_eq _ _ _ Hfold) as HfoldP.
        pose proof (plm_v_dvd p (S m')) as Hpe0.
        destruct Hpe0 as [u Hu].
        assert (Hdivp : Nat.divide p (S m')).
        { exists m0. rewrite <- HfoldP. apply Nat.mul_comm. }
        assert (He1 : 1 <= plm_v p (S m')).
        { destruct (Nat.eq_dec (plm_v p (S m')) 0) as [E0|Hne0]; [| lia].
          exfalso. apply (plm_v_max p (S m') Hp1lt ltac:(lia)).
          rewrite E0. cbn [Nat.pow]. rewrite Nat.mul_1_r. exact Hdivp. }
        assert (Hnpu : Nat.divide p u -> False).
        { intro Hpu. destruct Hpu as [w Hw].
          apply (plm_v_max p (S m') Hp1lt ltac:(lia)).
          exists w. rewrite Hu at 1. rewrite Nat.pow_succ_r', Hw. ring. }
        pose proof (hl_id_eq _ _ _
                      (z2v_gcd_pow_prime p (plm_v p (S m')) u Hpp Hnpu)) as Hgc.
        assert (Hu1 : 1 <= u).
        { destruct u as [| u'']; [rewrite Nat.mul_0_l in Hu; lia | lia]. }
        assert (HpE2 : 2 <= p ^ plm_v p (S m')).
        { pose proof (Nat.pow_le_mono_r p 1 (plm_v p (S m')) ltac:(lia) He1) as H1.
          cbn [Nat.pow] in H1. lia. }
        assert (Hult : u < S m').
        { pose proof (Nat.mul_le_mono_l 2 (p ^ plm_v p (S m')) u HpE2). lia. }
        assert (HpeC : Nat.divide (p ^ plm_v p (S m')) (z2v_C n)).
        { apply (z2v_ppow_dvd_C p (plm_v p (S m')) n Hpp).
          pose proof (Nat.divide_pos_le (p ^ plm_v p (S m')) (S m')
                        ltac:(lia) (plm_v_dvd p (S m'))) as Hle1.
          lia. }
        assert (HuC : Nat.divide u (z2v_C n)).
        { apply IH; [lia | exact Hu1 |].
          apply (Nat.le_trans u (S m') n);
            [exact (Nat.lt_le_incl _ _ Hult) | exact Hmn]. }
        pose proof (plm_dvd_mul_coprime (p ^ plm_v p (S m')) u (z2v_C n)
                      HpeC HuC Hgc) as Hcomb.
        rewrite Hu, (Nat.mul_comm u (p ^ plm_v p (S m'))). exact Hcomb.
Qed.

(* Main theorem (Prop face): [B(n) = hl_lcm_upto n] divides         *)
(* [C(n)] - [h3_lcm_fold_divide] folds under the whole-number       *)
(* divisibility premises.                                           *)
Theorem z2v_lcm_dvd_C : forall n : nat, Nat.divide (hl_lcm_upto n) (z2v_C n).
Proof.
  intro n. apply (h3_lcm_fold_divide n (z2v_C n)).
  intros m Hm1 Hm2. apply (z2v_m_dvd_C m n Hm1 Hm2).
Qed.

(* Main theorem (Set face): the mod-zero criterion form of          *)
(* [B(n) | C(n)].                                                   *)
Theorem z2v_lcm_dvd_C_t : forall n : nat, z2v_dvd_t (hl_lcm_upto n) (z2v_C n).
Proof.
  intro n. unfold z2v_dvd_t. apply z2v_id_of_eq.
  exact (z2v_idS_eq _ _ _
    (pr_dvd_mod0 (hl_lcm_upto n) (z2v_C n)
       (hl_le_t_to_le _ _ (h3_lcm_pos n)) (z2v_lcm_dvd_C n))).
Qed.

(* Numeric anchor: [C(6) = 6!/(3!*2!*0!*...) = 720/12 = 60 =        *)
(* lcm(1..6)].                                                      *)
Lemma z2v_C_6 : hl_id (z2v_C 6) 60.
Proof. apply z2v_id_of_eq. reflexivity. Qed.

(* Numeric anchor (executable on the Set face): direct computation  *)
(* of the mod-zero criterion for [B(6) | C(6)].                     *)
Lemma z2v_dvd_t_smoke_6 : z2v_dvd_t (hl_lcm_upto 6) (z2v_C 6).
Proof. reflexivity. Qed.

(* Assumption audit: the following [Print Assumptions] outputs      *)
(* should report no assumptions (rechecking a clean global          *)
(* context).  The log does not echo statement names, so the         *)
(* evidence is checked against this list in order.                  *)
Print Assumptions z2v_pow_dvd.
Print Assumptions z2v_pow_pos.
Print Assumptions z2v_sylv_sum_0.
Print Assumptions z2v_leg_0.
Print Assumptions z2v_den_pos.
Print Assumptions z2v_v_1.
Print Assumptions z2v_pow_split.
Print Assumptions z2v_v_add.
Print Assumptions z2v_inc.
Print Assumptions z2v_leg_cnt.
Print Assumptions z2v_cnt_min.
Print Assumptions z2v_fact_ex.
Print Assumptions z2v_lsum_S_k.
Print Assumptions z2v_den_val.
Print Assumptions z2v_pointwise.
Print Assumptions z2v_layersum_bound.
Print Assumptions z2v_pc_ge.
Print Assumptions z2v_fact_split.
Print Assumptions z2v_den_dvd_gen.
Print Assumptions z2v_den_dvd.
Print Assumptions z2v_v_C_ge.
Print Assumptions z2v_ppow_dvd_C.
Print Assumptions z2v_dvd_pow_split.
Print Assumptions z2v_gcd_pow_prime.
Print Assumptions z2v_m_dvd_C.
Print Assumptions z2v_lcm_dvd_C.
Print Assumptions z2v_lcm_dvd_C_t.
Print Assumptions z2v_C_6.
Print Assumptions z2v_dvd_t_smoke_6.
