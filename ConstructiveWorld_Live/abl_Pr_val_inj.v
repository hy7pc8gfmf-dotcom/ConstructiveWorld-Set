(* ConstructiveWorld-Set -- prime-power valuations of folded prime-power products. *)

(** * abl_Pr_val_inj: uniqueness of prime-power data in a folded product of prime powers.

    Mission.  For a prime [p], a list [l] of pairwise distinct primes and a
      positive exponent assignment [b], the folded product
      [fold_right Nat.mul 1 (map (fun q => q ^ b q) l)] carries [p]-power
      data uniquely: [p ^ a] divides the product iff [p] occurs in [l] with
      [a <= b p].  Main statements: [pzb_pow_dvd_prod_le],
      [pzb_pow_nodvd_prod], [pzb_prime_dvd_pow].

    Dependencies.  Stdlib [Arith.Arith], [List], [Bool], [Lia]; of this
      development [S01_BaseRing], [HansonLcm], [abl_Pr_core_01],
      [abl_Pr_euclid_03], [abl_Pr_lcmdecomp_04].

    References.  This development, abl_Pr_val_inj.v; statement names carried
      over verbatim from the baseline module, statement faces unchanged
      (standard-library Prop faces; full per-item list in Section 5).

    Constructivity.  Per-item carrier accounting; no blanket Set claim.  The
      Set-carried decision data live in the dependency chain: [S01_BaseRing]
      supplies the Set carriers [Id]/[NatLe]/[And] with the order bridges
      [NatLe_drop]/[NatLe_lift], and [abl_Pr_core_01] defines
      [pr_prime : nat -> Set].  Every statement named in this file is
      [Prop]-carried on standard-library faces ([le], [Nat.divide], [eq],
      [In], [NoDup], [ex], [/\], [\/]) -- the reasoning face over those Set
      inputs; it carries no computational data and erases at extraction.

    Build.  [coqc -native-compiler no -q -Q . "" abl_Pr_val_inj.v] compiles
      cleanly (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import S01_BaseRing (Id, id_refl, NatLe, NatLe_lift, NatLe_drop, And).
Require Import abl_Pr_core_01.
Require Import abl_Pr_lcmdecomp_04.

(* ---- Section 0. elementary facts on powers and divisibility ---- *)

Lemma pzb_pow_pos : forall p m : nat,
  1 <= p -> 1 <= p ^ m.
Proof.
  intros p m Hp. induction m as [| m' IH].
  - reflexivity.
  - rewrite Nat.pow_succ_r'. apply (Nat.mul_le_mono 1 p 1 (p ^ m')); lia.
Qed.

Lemma pzb_dvd_pow_succ : forall p k : nat,
  1 <= k -> Nat.divide p (p ^ k).
Proof.
  intros p k Hk. destruct k as [| k']; [lia |].
  rewrite Nat.pow_succ_r'. exists (p ^ k').
  apply Nat.mul_comm.
Qed.

Lemma pzb_dvd_cancel_mul : forall x u v : nat,
  x <> 0 -> Nat.divide (x * u) (x * v) -> Nat.divide u v.
Proof.
  intros x u v Hx Hdvd. destruct Hdvd as [z Hz].
  exists z.
  apply (proj1 (Nat.mul_cancel_l v (z * u) x Hx)).
  rewrite Hz. ring.
Qed.

Lemma pzb_dvd_pow_dvd_base : forall p a W : nat,
  1 <= a -> Nat.divide (p ^ a) W -> Nat.divide p W.
Proof.
  intros p a W Ha Hdvd. destruct a as [| a']; [lia |].
  rewrite Nat.pow_succ_r' in Hdvd.
  destruct Hdvd as [z Hz].
  exists (z * p ^ a'). rewrite Hz. ring.
Qed.

(* exponent bound when a positive power divides a product: with [p] absent from the cofactor, the exponent [a] cannot exceed [m] *)
Lemma pzb_pow_le_of_dvd_mul : forall p a m W : nat,
  pr_prime p -> 1 <= a -> (Nat.divide p W -> False) ->
  Nat.divide (p ^ a) (p ^ m * W) -> a <= m.
Proof.
  intros p a m W Hp Ha Hnp Hdvd.
  destruct Hp as [Hp2 _].
  destruct (le_lt_dec a m) as [Hle | Hlt]; [exact Hle |].
  exfalso.
  assert (Hsplit : exists k, a = m + k /\ 1 <= k)
    by (exists (a - m); split; lia).
  destruct Hsplit as [k [Hk Hk1]].
  rewrite Hk, Nat.pow_add_r in Hdvd.
  assert (Hpm : p ^ m <> 0).
  { assert (Hpos : 1 <= p ^ m) by (apply pzb_pow_pos; pose proof (NatLe_drop _ _ Hp2); lia).
    lia. }
  assert (Hdk : Nat.divide (p ^ k) W)
    by (apply (pzb_dvd_cancel_mul (p ^ m) (p ^ k) W Hpm Hdvd)).
  apply Hnp.
  apply (Nat.divide_trans p (p ^ k) W).
  - apply pzb_dvd_pow_succ. exact Hk1.
  - exact Hdk.
Qed.

(* ---- Section 1. the prime coincidence bridge ---- *)

Theorem pzb_prime_dvd_pow : forall p q e : nat,
  pr_prime p -> pr_prime q -> 1 <= e -> Nat.divide q (p ^ e) -> q = p.
Proof.
  intros p q e Hp Hq He Hdvd.
  destruct (Nat.eq_dec q p) as [Eq | Neq]; [exact Eq |].
  exfalso.
  assert (Hg : Nat.gcd q p = 1).
  { exact (match plm_prime_gcd_1 q p Hq Hp Neq in Id _ z
           return (Nat.gcd q p = z) with
           | id_refl => eq_refl end). }
  destruct Hq as [Hq2 _].
  assert (Hg1 : Nat.gcd (q ^ 1) (p ^ e) = 1).
  { exact (match plm_gcd_pow q p 1 e Hg in Id _ z
           return (Nat.gcd (q ^ 1) (p ^ e) = z) with
           | id_refl => eq_refl end). }
  rewrite Nat.pow_1_r in Hg1.
  assert (Hgd : Nat.divide q (Nat.gcd q (p ^ e)))
    by (apply Nat.gcd_greatest; [apply Nat.divide_refl | exact Hdvd]).
  rewrite Hg1 in Hgd.
  assert (Hle : q <= 1) by (apply (Nat.divide_pos_le q 1); [lia | exact Hgd]).
  pose proof (NatLe_drop _ _ Hq2); lia.
Qed.

(* ---- Section 2. companions of the folded product: tail rejection and list membership ---- *)

(* when [p] is absent from the list, [p] does not divide the folded product, by head splitting along the list induction *)
Lemma pzb_nodvd_fold : forall (p : nat) (l : list nat) (b : nat -> nat),
  pr_prime p ->
  (forall q, In q l -> pr_prime q) ->
  (forall q, In q l -> q <> p) ->
  (forall q, In q l -> 1 <= b q) ->
  Nat.divide p (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) -> False.
Proof.
  intros p l b Hpp Hpr Hne Hb.
  revert Hpr Hne Hb.
  induction l as [| q rest IH]; intros Hpr Hne Hb Hdvd.
  - cbn [map fold_right] in Hdvd.
    destruct Hpp as [Hp2 _].
    assert (Hle : p <= 1)
      by (apply (Nat.divide_pos_le p 1); [lia | exact Hdvd]).
    pose proof (NatLe_drop _ _ Hp2); lia.
  - cbn [map fold_right] in Hdvd.
    destruct (plm_prime_dvd_mul p (q ^ b q)
                (fold_right Nat.mul 1 (map (fun q => q ^ b q) rest))
                Hpp Hdvd) as [Hdq | Hdvr].
    + assert (Hqp : p = q)
        by (apply (pzb_prime_dvd_pow q p (b q));
            [apply Hpr; apply in_eq | exact Hpp
            | apply Hb; apply in_eq | exact Hdq]).
      apply (Hne q (in_eq q rest)). symmetry. exact Hqp.
    + apply IH.
      * intros r Hr. apply Hpr. apply in_cons. exact Hr.
      * intros r Hr. apply Hne. apply in_cons. exact Hr.
      * intros r Hr. apply Hb. apply in_cons. exact Hr.
      * exact Hdvr.
Qed.

(* if [p] divides the folded product then [p] occurs in the list, in the weak form that needs no distinctness *)
Lemma pzb_in_of_dvd : forall (p : nat) (l : list nat) (b : nat -> nat),
  pr_prime p ->
  (forall q, In q l -> pr_prime q) ->
  (forall q, In q l -> 1 <= b q) ->
  Nat.divide p (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) ->
  In p l.
Proof.
  intros p l b Hpp Hpr Hb Hdvd.
  revert Hpr Hb Hdvd.
  induction l as [| q rest IH]; intros Hpr Hb Hdvd.
  - cbn [map fold_right] in Hdvd.
    destruct Hpp as [Hp2 _].
    assert (Hle : p <= 1)
      by (apply (Nat.divide_pos_le p 1); [lia | exact Hdvd]).
    pose proof (NatLe_drop _ _ Hp2); lia.
  - cbn [map fold_right] in Hdvd.
    destruct (plm_prime_dvd_mul p (q ^ b q)
                (fold_right Nat.mul 1 (map (fun q => q ^ b q) rest))
                Hpp Hdvd) as [Hdq | Hdvr].
    + left. symmetry.
      apply (pzb_prime_dvd_pow q p (b q));
        [apply Hpr; apply in_eq | exact Hpp
        | apply Hb; apply in_eq | exact Hdq].
    + right. apply IH.
      * intros r Hr. apply Hpr. apply in_cons. exact Hr.
      * intros r Hr. apply Hb. apply in_cons. exact Hr.
      * exact Hdvr.
Qed.

(* ---- Section 3. the strong core and the two main statements ---- *)

(* exponent bound once [p] is located in the list: a head factor distinct from [p] is peeled off by coprime Gaussian cancellation *)
Lemma pzb_le_of_in_dvd : forall (p a : nat) (l : list nat) (b : nat -> nat),
  pr_prime p -> 1 <= a ->
  In p l -> NoDup l ->
  (forall q, In q l -> pr_prime q) ->
  (forall q, In q l -> 1 <= b q) ->
  Nat.divide (p ^ a) (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) ->
  a <= b p.
Proof.
  intros p a l b Hpp Ha Hin Hnd Hpr Hb Hdvd.
  revert Hin Hnd Hpr Hb Hdvd.
  induction l as [| q rest IH]; intros Hin Hnd Hpr Hb Hdvd.
  - destruct Hin.
  - cbn [map fold_right] in Hdvd.
    simpl in Hin.
    destruct Hin as [Heq | HinR].
    + subst q.
      assert (Hnin : ~ In p rest) by (inversion Hnd; assumption).
      assert (HneR : forall r, In r rest -> r <> p).
      { intros r Hr Hep. apply Hnin. rewrite <- Hep. exact Hr. }
      assert (Hnp : Nat.divide p
                (fold_right Nat.mul 1 (map (fun q => q ^ b q) rest)) -> False).
      { intros Hd.
        apply (pzb_nodvd_fold p rest b Hpp).
        - intros r Hr. apply Hpr. apply in_cons. exact Hr.
        - exact HneR.
        - intros r Hr. apply Hb. apply in_cons. exact Hr.
        - exact Hd. }
      exact (pzb_pow_le_of_dvd_mul p a (b p)
               (fold_right Nat.mul 1 (map (fun q => q ^ b q) rest))
               Hpp Ha Hnp Hdvd).
    + assert (Hnin : ~ In q rest) by (inversion Hnd; assumption).
      assert (Hqp : q <> p).
      { intro Heq. apply Hnin. rewrite Heq. exact HinR. }
      assert (Hndr : NoDup rest) by (inversion Hnd; assumption).
      assert (Hg : Nat.gcd p q = 1).
      { exact (match plm_prime_gcd_1 p q Hpp (Hpr q (in_eq q rest))
                       (fun Heq2 => Hqp (eq_sym Heq2)) in Id _ z
               return (Nat.gcd p q = z) with
               | id_refl => eq_refl end). }
      assert (Hgc : Nat.gcd (p ^ a) (q ^ b q) = 1).
      { exact (match plm_gcd_pow p q a (b q) Hg in Id _ z
               return (Nat.gcd (p ^ a) (q ^ b q) = z) with
               | id_refl => eq_refl end). }
      assert (Hdvr : Nat.divide (p ^ a)
                (fold_right Nat.mul 1 (map (fun q => q ^ b q) rest)))
        by (apply (plm_gauss (p ^ a) (q ^ b q)
                   (fold_right Nat.mul 1 (map (fun q => q ^ b q) rest))
                   Hgc Hdvd)).
      apply IH.
      * exact HinR.
      * exact Hndr.
      * intros r Hr. apply Hpr. apply in_cons. exact Hr.
      * intros r Hr. apply Hb. apply in_cons. exact Hr.
      * exact Hdvr.
Qed.

Theorem pzb_pow_dvd_prod_le : forall p a (l : list nat) (b : nat -> nat),
  pr_prime p -> NoDup l ->
  (forall q, In q l -> pr_prime q) ->
  (forall q, In q l -> 1 <= b q) ->
  1 <= a ->
  Nat.divide (p ^ a) (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) ->
  exists q, In q l /\ q = p /\ a <= b q.
Proof.
  intros p a l b Hpp Hnd Hpr Hb Ha Hdvd.
  assert (Hin : In p l).
  { apply (pzb_in_of_dvd p l b Hpp Hpr Hb).
    exact (pzb_dvd_pow_dvd_base p a
             (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) Ha Hdvd). }
  assert (Hle : a <= b p)
    by (apply (pzb_le_of_in_dvd p a l b Hpp Ha Hin Hnd Hpr Hb Hdvd)).
  exists p. split; [exact Hin | split; [reflexivity | exact Hle]].
Qed.

Theorem pzb_pow_nodvd_prod : forall p a (l : list nat) (b : nat -> nat),
  pr_prime p -> NoDup l ->
  (forall q, In q l -> pr_prime q) ->
  (forall q, In q l -> q <> p) ->
  (forall q, In q l -> 1 <= b q) ->
  1 <= a ->
  (Nat.divide (p ^ a) (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) -> False) \/
  (exists q, In q l /\ q = p).
Proof.
  intros p a l b Hpp Hnd Hpr Hne Hb Ha.
  destruct (In_dec Nat.eq_dec p l) as [Hin | Hnin].
  - right. exists p. split; [exact Hin | reflexivity].
  - left. intros Hdvd.
    apply (pzb_nodvd_fold p l b Hpp Hpr Hne Hb).
    exact (pzb_dvd_pow_dvd_base p a
             (fold_right Nat.mul 1 (map (fun q => q ^ b q) l)) Ha Hdvd).
Qed.

(* ---- Section 4. numerical checks ---- *)

Example pzb_smoke_fold : fold_right Nat.mul 1 (map (fun q => q ^ 3) (cons 2 (cons 3 nil))) = 216.
Proof. vm_compute. reflexivity. Qed.

Example pzb_smoke_dvd : Nat.eqb ((2 ^ 3 * 3 ^ 2) mod (2 ^ 3)) 0 = true.
Proof. vm_compute. reflexivity. Qed.

Example pzb_smoke_nodvd : Nat.eqb ((2 ^ 3 * 3 ^ 2) mod (5 ^ 1)) 0 = false.
Proof. vm_compute. reflexivity. Qed.

(* ---- Section 5. constructivity audit of the statements ----

   Per-item carrier disclosure (referred to by the Constructivity header
   field).  Set-carried decision data: none in this file -- the Set carriers
   ([Id], [NatLe], [And] with the bridges [NatLe_drop]/[NatLe_lift], and
   [pr_prime : nat -> Set]) are supplied by [S01_BaseRing] and
   [abl_Pr_core_01].  Every statement named in this file is [Prop]-carried
   on standard-library faces and erases at extraction, item by item:
   - support lemmas (Prop): [pzb_pow_pos], [pzb_dvd_pow_succ],
     [pzb_dvd_cancel_mul], [pzb_dvd_pow_dvd_base], [pzb_pow_le_of_dvd_mul],
     [pzb_nodvd_fold], [pzb_in_of_dvd], [pzb_le_of_in_dvd];
   - main statements (Prop): [pzb_prime_dvd_pow], [pzb_pow_dvd_prod_le],
     [pzb_pow_nodvd_prod];
   - smoke examples (Prop): [pzb_smoke_fold], [pzb_smoke_dvd],
     [pzb_smoke_nodvd].
   Assumption audit: each [Print Assumptions] below reports Closed under
   the global context; [coqchk] on the compiled module reports
   [Axioms: none].  Extraction face, measured: a [Separate Extraction] of
   all fourteen names emits [abl_Pr_val_inj.ml]/[abl_Pr_val_inj.mli] with
   every name present as an opaque [Obj.t] slot ([type __ = Obj.t]) and
   [Obj.magic] literal count 0 on both faces. *)

Print Assumptions pzb_pow_pos.
Print Assumptions pzb_dvd_pow_succ.
Print Assumptions pzb_dvd_cancel_mul.
Print Assumptions pzb_dvd_pow_dvd_base.
Print Assumptions pzb_pow_le_of_dvd_mul.
Print Assumptions pzb_prime_dvd_pow.
Print Assumptions pzb_nodvd_fold.
Print Assumptions pzb_in_of_dvd.
Print Assumptions pzb_le_of_in_dvd.
Print Assumptions pzb_pow_dvd_prod_le.
Print Assumptions pzb_pow_nodvd_prod.
