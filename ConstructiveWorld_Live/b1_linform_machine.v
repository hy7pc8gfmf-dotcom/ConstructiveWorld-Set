(* ConstructiveWorld-Set — integer-valued linear-form machine on the Z layer. *)

(** * b1_linform_machine: the Euler arctan continued-fraction machine.

    Mission.  Convergents [(p_n, q_n)] of the Euler continued fraction for
    [arctan(1) = pi/4] = [1/(1 + 1^2/(3 + 2^2/(5 + 3^2/(7 + ...))))], generated
    by the three-term recurrence carried as a one-step dual state [(P_n,
    P_{n-1})].  Closed faces: the determinant identity [b1cf_detT n = (-1)^n
    (n!)^2] (one-step fold, two-step induction); denominator positivity
    [q_n >= 1], monotonicity [q_n <= q_{S n}] (QltT Set bridge), the growth
    limb [q_{S n} <= (S n)^2 * q_n] and the telescope [q_n <= (n!)^2];
    numerical anchors (independently recomputed).  The Beukers-type identity
    [|q_n pi/4 - p_n| = D_n I_n] needs real integral semantics; it lives in
    the named supply slot of the competing-judgement file.

    Dependencies.  S01_BaseRing (QeqT/QltT/Id), S02_CauchyComplete,
    b1_kernel_pointwise; Stdlib ZArith/Arith/Factorial/Lia, Setoid,
    Morphisms, Qfield.

    References.  The witness-precedence file family; machine-shape transfer
    of the four transferable properties.

    Constructivity.  Statement faces all [Set] (QeqT/QltT); Z-layer proof
    bodies are propositional reasoning carriers (in-body constructive Prop
    derivation is legal), Set faces completed by explicit bridge citations
    of Z facts; Z-ring identities via micromega linearization (the local
    Z-ring tactic is broken on record).  Axioms: none; no classical logic.

    Build.  Source Live/toolchain/env.sh, then inside the cpu_guard wrapper
    run [rocq c -native-compiler no -q -Q . "" b1_linform_machine.v]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith Arith.Arith
  Arith.Factorial Lia.
From Stdlib Require Import Setoid Morphisms Qfield.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import b1_kernel_pointwise.

Open Scope Z_scope.
Open Scope Q_scope.

(* ========== Section 0. Preliminaries: the Id <-> eq and Z-order Set-bridge kit (in-file local bridge kit, canonical form) ========== *)

Definition Id_eq {A : Set} (x y : A) (H : Id x y) : x = y.
Proof. destruct H. apply eq_refl. Defined.

Definition eq_Id {A : Set} (x y : A) (H : x = y) : Id x y.
Proof. destruct H. apply id_refl. Defined.

Definition ZLeT (a b : Z) : Set := Id (Z.leb a b) true.

Lemma ZLeT_drop : forall a b : Z, ZLeT a b -> (a <= b)%Z.
Proof. intros a b H. apply Z.leb_le. exact (Id_eq _ _ H). Defined.

Lemma ZLeT_lift : forall a b : Z, (a <= b)%Z -> ZLeT a b.
Proof. intros a b H. exact (eq_Id _ _ (proj2 (Z.leb_le a b) H)). Defined.

(* ========== Section 0. The Z->Q Set bridge and arithmetic certificates ========== *)

(* Z equality -> QeqT (the #1 embedding) *)
Lemma b1_zeq_qeqT1 : forall a b : Z, (a = b)%Z -> QeqT (a # 1) (b # 1).
Proof.
  intros a b Hab.
  assert (Hq : (a # 1)%Q == (b # 1)%Q).
  { unfold Qeq. cbn [Qnum Qden].
    rewrite Z.mul_1_r, Z.mul_1_r, Hab. reflexivity. }
  exact (qeq_imp_qeqT ((a # 1)%Q) ((b # 1)%Q) Hq).
Qed.

(* Z order 1 <= z -> QltT 0 (z#1) (strict tier) *)
Lemma b1_zle1_qltT0 : forall z : Z, (1 <= z)%Z -> QltT 0 (z # 1).
Proof.
  intros z Hz. unfold QltT, Qlt_bool, Qcompare, Qle. cbn [Qnum Qden].
  rewrite Z.mul_0_l, Z.mul_1_r.
  destruct (0 ?= z)%Z eqn:Ez.
  - exfalso. apply (proj1 (Z.compare_eq_iff 0 z)) in Ez. lia.
  - reflexivity.
  - exfalso. apply (proj1 (Z.compare_gt_iff 0 z)) in Ez. lia.
Qed.

(* 2k+3 <= (k+2)^2 (perfect-square fold: (k+2)^2 = (k+1)^2 + (2k+3), and (k+1)^2 >= 0) *)
Lemma b1_sq_ge_2k3 : forall k : Z, ZLeT (2 * k + 3)%Z ((k + 2) * (k + 2))%Z.
Proof.
  intro k.
  apply ZLeT_lift.
  assert (Hp : (0 <= (k + 1) * (k + 1))%Z)
    by (exact (ZLeT_drop _ _ (b1_zsq_nonneg (k + 1)%Z))).
  replace ((k + 2) * (k + 2))%Z
    with ((k + 1) * (k + 1) + (2 * k + 3))%Z by lia.
  apply (Z.le_trans (2 * k + 3) (0 + (2 * k + 3))%Z
                    ((k + 1) * (k + 1) + (2 * k + 3))%Z).
  - rewrite Z.add_0_l. apply Z.le_refl.
  - apply (Zplus_le_compat_r 0 ((k + 1) * (k + 1)) (2 * k + 3)). exact Hp.
Qed.

(* 1 <= S n (nat-layer local lemma) *)
Lemma b1_1leS : forall n : nat, NatLe 1 (Datatypes.S n).
Proof.
  intro n. apply NatLe_lift. apply (proj1 (Nat.succ_le_mono 0 n)).
  apply Nat.le_0_l.
Qed.

(* 1 <= z -> Z.pos (Z.to_pos z) = z (positive read-back form) *)
Lemma b1_zpos_of : forall z : Z, (1 <= z)%Z -> Id (Z.pos (Z.to_pos z)) z.
Proof.
  intros z Hz. destruct z as [| p | p]; cbn [Z.to_pos];
    [ exfalso; lia | apply id_refl | exfalso; lia ].
Qed.

(* ========== Section 1. Continued-fraction convergents (one-step dual-state recursion, guard-safe form) ========== *)

Fixpoint b1cfP (n : nat) : Z * Z :=
  match n with
  | O => (0%Z, 0%Z)
  | Datatypes.S n0 =>
      match n0 with
      | O => (1%Z, 0%Z)
      | Datatypes.S k =>
          let (p1, p2) := b1cfP n0 in
          ((Z.of_nat ((2 * Datatypes.S k + 1)%nat) * p1
            + Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k) * p2)%Z,
           p1)
      end
  end.

Fixpoint b1cfQ (n : nat) : Z * Z :=
  match n with
  | O => (1%Z, 1%Z)
  | Datatypes.S n0 =>
      match n0 with
      | O => (1%Z, 1%Z)
      | Datatypes.S k =>
          let (q1, q2) := b1cfQ n0 in
          ((Z.of_nat ((2 * Datatypes.S k + 1)%nat) * q1
            + Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k) * q2)%Z,
           q1)
      end
  end.

Definition b1cf_p (n : nat) : Z := fst (b1cfP n).
Definition b1cf_q (n : nat) : Z := fst (b1cfQ n).

Lemma b1cf_p0 : Id (b1cf_p 0) 0%Z. Proof. apply id_refl. Qed.
Lemma b1cf_p1 : Id (b1cf_p 1) 1%Z. Proof. apply id_refl. Qed.
Lemma b1cf_q0 : Id (b1cf_q 0) 1%Z. Proof. apply id_refl. Qed.
Lemma b1cf_q1 : Id (b1cf_q 1) 1%Z. Proof. apply id_refl. Qed.

(* Two-step unfolding (definitional; full iota reduction) *)
Lemma b1cfP_stepS : forall k : nat,
  Id (b1cfP (Datatypes.S (Datatypes.S k)))
     (let (p1, p2) := b1cfP (Datatypes.S k) in
      ((Z.of_nat ((2 * Datatypes.S k + 1)%nat) * p1
        + Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k) * p2)%Z, p1)).
Proof. intros k. apply id_refl. Qed.

Lemma b1cfQ_stepS : forall k : nat,
  Id (b1cfQ (Datatypes.S (Datatypes.S k)))
     (let (q1, q2) := b1cfQ (Datatypes.S k) in
      ((Z.of_nat ((2 * Datatypes.S k + 1)%nat) * q1
        + Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k) * q2)%Z, q1)).
Proof. intros k. apply id_refl. Qed.

(* One-step recursive unfolding (dual state; domain n >= 1, the base case excluded by the premise) *)
Lemma b1cf_p_unfold1 : forall n : nat, (1 <= n)%nat ->
  Id (b1cf_p (Datatypes.S n))
     ((Z.of_nat ((2 * n + 1)%nat) * fst (b1cfP n)
       + Z.of_nat n * Z.of_nat n * snd (b1cfP n))%Z).
Proof.
  intros n Hn. destruct n as [| k].
  - exfalso. lia.
  - unfold b1cf_p.
    rewrite (Id_eq _ _ (b1cfP_stepS k)).
    destruct (b1cfP (Datatypes.S k)) as [a b].
    apply id_refl.
Qed.

Lemma b1cf_q_unfold1 : forall n : nat, (1 <= n)%nat ->
  Id (b1cf_q (Datatypes.S n))
     ((Z.of_nat ((2 * n + 1)%nat) * fst (b1cfQ n)
       + Z.of_nat n * Z.of_nat n * snd (b1cfQ n))%Z).
Proof.
  intros n Hn. destruct n as [| k].
  - exfalso. lia.
  - unfold b1cf_q.
    rewrite (Id_eq _ _ (b1cfQ_stepS k)).
    destruct (b1cfQ (Datatypes.S k)) as [a b].
    apply id_refl.
Qed.

(* Dual-state second component (fst form): snd (b1cfP (S n)) = P_n and snd (b1cfQ (S n)) = Q_n *)
Lemma b1cf_p_snd_f : forall n : nat,
  Id (snd (b1cfP (Datatypes.S n))) (fst (b1cfP n)).
Proof.
  intros n. destruct n as [| k].
  - apply id_refl.
  - rewrite (Id_eq _ _ (b1cfP_stepS k)).
    destruct (b1cfP (Datatypes.S k)) as [a b].
    apply id_refl.
Qed.

Lemma b1cf_q_snd_f : forall n : nat,
  Id (snd (b1cfQ (Datatypes.S n))) (fst (b1cfQ n)).
Proof.
  intros n. destruct n as [| k].
  - apply id_refl.
  - rewrite (Id_eq _ _ (b1cfQ_stepS k)).
    destruct (b1cfQ (Datatypes.S k)) as [a b].
    apply id_refl.
Qed.

(* ========== Section 2. The determinant identity (the main load-bearing statement) ========== *)

(* D_n := p_{S n} * q_n - p_n * q_{S n} *)
Definition b1cf_detT (n : nat) : Z :=
  (b1cf_p (Datatypes.S n) * b1cf_q n - b1cf_p n * b1cf_q (Datatypes.S n))%Z.

(* Linear-form elimination core: (t*a + v*b)*c - a*(t*c + v*d) = -v*(a*d - b*c)
   (an all-integer-variable identity; pure distributivity and cancellation) *)
Lemma b1_z_lform_core : forall a b c d t v : Z,
  Id (((t * a + v * b) * c - a * (t * c + v * d))%Z)
     (((-(v)) * (a * d - b * c))%Z).
Proof. intros a b c d t v. apply eq_Id. lia. Qed.

(* Determinant step core: -(x^2)*(p f^2) = (-p)*(x f)*(x f) (an all-integer-variable identity) *)
Lemma b1_z_det_core : forall x f p : Z,
  Id (((-(x * x)) * (p * f * f))%Z)
     (((Z.opp 1 * p) * (x * f) * (x * f))%Z).
Proof. intros x f p. apply eq_Id. lia. Qed.

(* One-step fold: D_{S n} = -(S n)^2 * D_n (two-step recursive unfolding + the linear-form elimination core) *)
Lemma b1cf_det_step : forall n : nat,
  Id (b1cf_detT (Datatypes.S n))
     ((-(Z.of_nat (Datatypes.S n) * Z.of_nat (Datatypes.S n))
       * b1cf_detT n)%Z).
Proof.
  intro n.
  unfold b1cf_detT.
  rewrite (Id_eq _ _ (b1cf_p_unfold1 (Datatypes.S n)
                       (NatLe_drop 1 (Datatypes.S n) (b1_1leS n)))).
  rewrite (Id_eq _ _ (b1cf_q_unfold1 (Datatypes.S n)
                       (NatLe_drop 1 (Datatypes.S n) (b1_1leS n)))).
  rewrite (Id_eq _ _ (b1cf_p_snd_f n)).
  rewrite (Id_eq _ _ (b1cf_q_snd_f n)).
  unfold b1cf_p, b1cf_q.
  apply (b1_z_lform_core
          (fst (b1cfP (Datatypes.S n))) (fst (b1cfP n))
          (fst (b1cfQ (Datatypes.S n))) (fst (b1cfQ n))
          (Z.of_nat ((2 * Datatypes.S n + 1)%nat))
          (Z.of_nat (Datatypes.S n) * Z.of_nat (Datatypes.S n))).
Qed.

(* The determinant identity (Z core): D_n = (-1)^n * (n!)^2 *)
Theorem b1cf_det_eq : forall n : nat,
  Id (b1cf_detT n)
     ((Z.pow (Z.opp 1) (Z.of_nat n) * Z.of_nat (fact n) * Z.of_nat (fact n))%Z).
Proof.
  induction n as [| n IH].
  - unfold b1cf_detT. cbn [fact]. apply id_refl.
  - rewrite (Id_eq _ _ (b1cf_det_step n)). rewrite (Id_eq _ _ IH).
    (* This stdlib lacks Nat.fact_succ / Z.pow_succ_r' (established by probe):
       fact (S n) takes the definitional detour (cbn [fact] iota + inj_mul) and
       Z.pow_succ_r (premise tier 0 <= m, m = Z.of_nat n via Nat2Z.is_nonneg). *)
    replace (Z.of_nat (fact (Datatypes.S n)))
      with ((Z.of_nat (Datatypes.S n) * Z.of_nat (fact n))%Z)
      by (cbn [fact]; rewrite Nat2Z.inj_mul; reflexivity).
    replace (Z.of_nat (Datatypes.S n)) with (Z.succ (Z.of_nat n))
      by (rewrite Nat2Z.inj_succ; reflexivity).
    replace (Z.pow (Z.opp 1) (Z.succ (Z.of_nat n)))
      with ((Z.opp 1 * Z.pow (Z.opp 1) (Z.of_nat n))%Z)
      by (symmetry; apply Z.pow_succ_r; apply Nat2Z.is_nonneg).
    apply (b1_z_det_core (Z.succ (Z.of_nat n)) (Z.of_nat (fact n))
                         (Z.pow (Z.opp 1) (Z.of_nat n))).
Qed.

(* The determinant identity (Set certificate form) *)
Theorem b1cf_det : forall n : nat,
  QeqT ((b1cf_detT n) # 1)
       ((Z.pow (Z.opp 1) (Z.of_nat n) * Z.of_nat (fact n) * Z.of_nat (fact n)) # 1).
Proof.
  intros n. apply b1_zeq_qeqT1. exact (Id_eq _ _ (b1cf_det_eq n)).
Qed.

(* ========== Section 3. Denominator positivity, monotonicity and growth (Z core + Set bridge) ========== *)

(* q >= 1 (Z core; a two-base pairing drives the induction, all chains linear) *)
Lemma b1cf_q_ge1 : forall n : nat, ZLeT 1 (b1cf_q n).
Proof.
  intro n.
  assert (Hpair : forall k : nat,
            (1 <= b1cf_q k)%Z /\ (1 <= b1cf_q (Datatypes.S k))%Z).
  { induction k as [| k IHk].
    - split; [rewrite (Id_eq _ _ b1cf_q0) | rewrite (Id_eq _ _ b1cf_q1)];
        apply Z.le_refl.
    - destruct IHk as [H0 H1].
      split.
      + exact H1.
      + rewrite (Id_eq _ _ (b1cf_q_unfold1 (Datatypes.S k)
                             (NatLe_drop 1 (Datatypes.S k) (b1_1leS k)))).
        (* This stdlib lacks Z.mul_le_mono_l / Z.le_add_r (established by probe):
           premise tier 0 <= p via Z.mul_le_mono_nonneg_l/r, plus a Y >= 0 certificate closed by lia. *)
        assert (Hq2 : (1 <= snd (b1cfQ (Datatypes.S k)))%Z).
        { rewrite (Id_eq _ _ (b1cf_q_snd_f k)). exact H0. }
        assert (Hx : (0 <= Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k)
                            * snd (b1cfQ (Datatypes.S k)))%Z).
        { assert (Hs0 : (0 <= snd (b1cfQ (Datatypes.S k)))%Z) by lia.
          pose proof (Z.mul_le_mono_nonneg_r 0
            (Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k))
            (snd (b1cfQ (Datatypes.S k))) Hs0
            (ZLeT_drop _ _
              (b1_zsq_nonneg (Z.of_nat (Datatypes.S k))))) as HH.
          rewrite Z.mul_0_l in HH. exact HH. }
        apply (Z.le_trans 1
                 (Z.of_nat ((2 * Datatypes.S k + 1)%nat)
                  * fst (b1cfQ (Datatypes.S k)))%Z _).
        * apply (Z.le_trans 1
                   (Z.of_nat ((2 * Datatypes.S k + 1)%nat) * 1)%Z _).
          -- rewrite Z.mul_1_r. lia.
          -- apply Z.mul_le_mono_nonneg_l.
             ++ apply Nat2Z.is_nonneg.
             ++ exact H1.
        * lia. }
  apply ZLeT_lift. exact (proj1 (Hpair n)).
Qed.

(* Denominator positivity (Set certificate form, strict tier) *)
Theorem b1cf_q_pos : forall n : nat, QltT 0 ((b1cf_q n) # 1).
Proof.
  intros n. apply b1_zle1_qltT0. exact (ZLeT_drop _ _ (b1cf_q_ge1 n)).
Qed.

(* Monotonicity: q_n <= q_{S n} (Z core; two base cases + the step case by additive domination) *)
Theorem b1cf_q_mono : forall n : nat,
  ZLeT (b1cf_q n) (b1cf_q (Datatypes.S n)).
Proof.
  intro n.
  assert (Hpair : forall k : nat,
            (b1cf_q k <= b1cf_q (Datatypes.S k))%Z
            /\ (b1cf_q (Datatypes.S k)
                <= b1cf_q (Datatypes.S (Datatypes.S k)))%Z).
  { induction k as [| k IHk].
    - split.
      + rewrite (Id_eq _ _ b1cf_q0), (Id_eq _ _ b1cf_q1). apply Z.le_refl.
      + rewrite (Id_eq _ _ (b1cf_q_unfold1 1 (Nat.le_refl 1))).
        change (b1cf_q 1) with 1%Z.
        change (Z.of_nat ((2 * Datatypes.S 0 + 1)%nat)) with 3%Z.
        change (Z.of_nat (Datatypes.S 0)) with 1%Z.
        change (fst (b1cfQ (Datatypes.S 0))) with 1%Z.
        change (snd (b1cfQ (Datatypes.S 0))) with 1%Z.
        lia.
    - destruct IHk as [H0 H1].
      split.
      + exact H1.
      + rewrite (Id_eq _ _ (b1cf_q_unfold1 (Datatypes.S (Datatypes.S k))
                             (NatLe_drop 1 (Datatypes.S (Datatypes.S k))
                                          (b1_1leS (Datatypes.S k))))).
        unfold b1cf_q. rewrite (Id_eq _ _ (b1cf_q_snd_f (Datatypes.S k))).
        (* This stdlib lacks Z.le_add_l (established by probe): B <= c*B via the
           multiplier chain (1 <= B, 1 <= c) plus a T2 >= 0 certificate, closed by lia. *)
        assert (H1B : (1 <= fst (b1cfQ (Datatypes.S (Datatypes.S k))))%Z)
          by exact (ZLeT_drop _ _
                      (b1cf_q_ge1 (Datatypes.S (Datatypes.S k)))).
        assert (HB : (fst (b1cfQ (Datatypes.S (Datatypes.S k)))
                    <= Z.of_nat ((2 * Datatypes.S (Datatypes.S k) + 1)%nat)
                      * fst (b1cfQ (Datatypes.S (Datatypes.S k))))%Z).
        { assert (H0B : (0 <= fst (b1cfQ (Datatypes.S (Datatypes.S k))))%Z) by lia.
          assert (Hc1 : (1 <= Z.of_nat ((2 * Datatypes.S (Datatypes.S k) + 1)%nat))%Z)
            by lia.
          pose proof (Z.mul_le_mono_nonneg_r 1
            (Z.of_nat ((2 * Datatypes.S (Datatypes.S k) + 1)%nat))
            (fst (b1cfQ (Datatypes.S (Datatypes.S k)))) H0B Hc1) as HH.
          rewrite Z.mul_1_l in HH. exact HH. }
        assert (HT2 : (0 <= Z.of_nat (Datatypes.S (Datatypes.S k))
                             * Z.of_nat (Datatypes.S (Datatypes.S k))
                             * fst (b1cfQ (Datatypes.S k)))%Z).
        { assert (H1A2 : (1 <= fst (b1cfQ (Datatypes.S k)))%Z)
            by exact (ZLeT_drop _ _ (b1cf_q_ge1 (Datatypes.S k))).
          assert (H0A2 : (0 <= fst (b1cfQ (Datatypes.S k)))%Z) by lia.
          pose proof (Z.mul_le_mono_nonneg_r 0
            (Z.of_nat (Datatypes.S (Datatypes.S k)) * Z.of_nat (Datatypes.S (Datatypes.S k)))
            (fst (b1cfQ (Datatypes.S k))) H0A2
            (ZLeT_drop _ _
              (b1_zsq_nonneg (Z.of_nat (Datatypes.S (Datatypes.S k)))))) as HH.
          rewrite Z.mul_0_l in HH. exact HH. }
        lia. }
  apply ZLeT_lift. exact (proj1 (Hpair n)).
Qed.

(* Square-shift identity: (2k+3) + (k+1)^2 = (k+2)^2 (Z reading) *)
Lemma b1_z_sq_shift : forall k : nat,
  Id ((Z.of_nat ((2 * Datatypes.S k + 1)%nat)
       + Z.of_nat (Datatypes.S k) * Z.of_nat (Datatypes.S k))%Z)
     ((Z.of_nat (Datatypes.S (Datatypes.S k))
       * Z.of_nat (Datatypes.S (Datatypes.S k)))%Z).
Proof. intro k. apply eq_Id. lia. Qed.

(* Growth step: q_{S n} <= (S n)^2 * q_n (monotonicity limb + the square shift) *)
Theorem b1cf_q_growth : forall n : nat,
  ZLeT (b1cf_q (Datatypes.S n))
       ((Z.of_nat (Datatypes.S n) * Z.of_nat (Datatypes.S n) * b1cf_q n)%Z).
Proof.
  induction n as [| n IHn].
  - rewrite (Id_eq _ _ b1cf_q1), (Id_eq _ _ b1cf_q0).
    change (Z.of_nat (Datatypes.S 0)) with 1%Z.
    apply id_refl.
  - apply ZLeT_lift.
    rewrite (Id_eq _ _ (b1cf_q_unfold1 (Datatypes.S n)
                         (NatLe_drop 1 (Datatypes.S n) (b1_1leS n)))).
    apply (Z.le_trans _ ((Z.of_nat (2 * Datatypes.S n + 1)%nat
                          + Z.of_nat (Datatypes.S n) * Z.of_nat (Datatypes.S n))
                         * b1cf_q (Datatypes.S n))%Z _).
    + rewrite Z.mul_add_distr_r.
      apply Zplus_le_compat.
      * apply Z.le_refl.
      * apply Z.mul_le_mono_nonneg_l.
        -- exact (ZLeT_drop _ _ (b1_zsq_nonneg _)).
        -- rewrite (Id_eq _ _ (b1cf_q_snd_f n)).
           exact (ZLeT_drop _ _ (b1cf_q_mono n)).
    + rewrite <- (Id_eq _ _ (b1_z_sq_shift n)). apply Z.le_refl.
Qed.

(* Square-product regrouping: (a^2)*(f^2) = (a f)^2 (Z identity) *)
Lemma b1_z_sq_mul_sq : forall a f : Z,
  Id (((a * a) * (f * f))%Z) (((a * f) * (a * f))%Z).
Proof. intros a f. apply eq_Id. lia. Qed.

(* Telescope: q_n <= (n!)^2 *)
Theorem b1cf_q_le_fact_sq : forall n : nat,
  ZLeT (b1cf_q n) ((Z.of_nat (fact n) * Z.of_nat (fact n))%Z).
Proof.
  induction n as [| n IH].
  - rewrite (Id_eq _ _ b1cf_q0). cbn [fact].
    change (Z.of_nat 1) with 1%Z. apply id_refl.
  - apply ZLeT_lift.
    apply (Z.le_trans _ (Z.of_nat (Datatypes.S n) * Z.of_nat (Datatypes.S n)
                         * (Z.of_nat (fact n) * Z.of_nat (fact n)))%Z _).
    + apply (Z.le_trans _ (Z.of_nat (Datatypes.S n) * Z.of_nat (Datatypes.S n)
                           * b1cf_q n)%Z _).
      * exact (ZLeT_drop _ _ (b1cf_q_growth n)).
      * apply Z.mul_le_mono_nonneg_l.
        -- exact (ZLeT_drop _ _ (b1_zsq_nonneg _)).
        -- exact (ZLeT_drop _ _ IH).
    + replace (Z.of_nat (fact (Datatypes.S n)))
        with ((Z.of_nat (Datatypes.S n) * Z.of_nat (fact n))%Z)
        by (cbn [fact]; rewrite Nat2Z.inj_mul; reflexivity).
      rewrite (Id_eq _ _ (b1_z_sq_mul_sq (Z.of_nat (Datatypes.S n))
                              (Z.of_nat (fact n)))).
      apply Z.le_refl.
Qed.

(* ========== Section 4. Numerical anchors (independently recomputed comparison points) ========== *)

(* Anchor 1: p_3 = 19 (numerator of the convergent 19/24) *)
Lemma b1cf_p_anchor3 : Id (b1cf_p 3) (19%Z).
Proof. reflexivity. Qed.

(* Anchor 2: q_3 = 24 (the denominator) *)
Lemma b1cf_q_anchor3 : Id (b1cf_q 3) (24%Z).
Proof. reflexivity. Qed.

(* Anchor 3: p_4 = 160, q_4 = 204 (the unreduced form of 40/51) *)
Lemma b1cf_p_anchor4 : Id (b1cf_p 4) (160%Z).
Proof. reflexivity. Qed.

Lemma b1cf_q_anchor4 : Id (b1cf_q 4) (204%Z).
Proof. reflexivity. Qed.

(* Anchor 4: determinant D_3 = p_4 q_3 - p_3 q_4 = 3840 - 3876 = -36 = (-1)^3 * (3!)^2 *)
Lemma b1cf_det_anchor3 : Id (b1cf_detT 3) ((-36)%Z).
Proof. reflexivity. Qed.

(* Anchor 5: D_2 = p_3 q_2 - p_2 q_3 = 76 - 72 = 4 = (-1)^2 * (2!)^2 *)
Lemma b1cf_det_anchor2 : Id (b1cf_detT 2) (4%Z).
Proof. reflexivity. Qed.

(* ========== Section 5. In-file checks and the assumption audit ========== *)

Check b1cf_det.
Check b1cf_det_eq.
Check b1cf_q_pos.
Check b1cf_q_mono.
Check b1cf_q_growth.
Check b1cf_q_le_fact_sq.

Print Assumptions b1cf_det.
Print Assumptions b1cf_det_eq.
Print Assumptions b1cf_q_pos.
Print Assumptions b1cf_q_mono.
Print Assumptions b1cf_q_growth.
Print Assumptions b1cf_q_le_fact_sq.
