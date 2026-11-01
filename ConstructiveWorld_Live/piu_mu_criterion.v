(* =========================================================================
   Module: piu_mu_criterion. Irrationality-measure criterion for integer
   linear forms with Set-carried statement faces.
   Mission. Let A, B : nat -> Z with |A(n)|, |B(n)| <= 2^(sigma*n) and
   dval(A(n), B(n)) * 2^(tau*n) <= 1. If every rational point p/q (q >= 1)
   carries an escape index n with 2*q <= 2^(tau*n),
   2^(sigma*n*tau) <= kappa^tau * q^(sigma+tau) and |A(n)*q + B(n)*p| >= 1,
   then (1/2)^tau <= kappa^tau * |q*x - p|^tau * q^(sigma+tau) for all
   q >= 1. For tau >= 1 this is order-equivalent (both sides to the
   tau-th power) to |x - p/q| >= c0/q^(1 + sigma/tau), c0 = 1/(2*kappa):
   the q^(-mu) lower-bound form of mu(x) <= 1 + sigma/tau. The value
   |a + b*x| is carried by an abstract map dval : Z -> Z -> Q; its
   positivity and triangle consistency (identity
   a*q + b*p = q*(a + b*x) - b*(q*x - p)) are explicit premises Hp, Htri.
   Exponential scales are discretized to powers of two: e^(sigma*n) as
   2^(sigma*n), e^(-tau*n) as 2^(-tau*n); powers are order-preserving on
   the positive domain, so measure semantics is kept.
   Dependencies. Stdlib only: QArith, Qring, ZArith, Arith, Lia, Lqa,
   Qpower. Lia/Lqa serve bridge lemmas and auxiliary conversions only;
   the main theorem closes with an explicit inequality-chain synthesis.
   References. Irrationality measure via linear-form criteria: the
   tau-power restatement of |x - p/q| >= c0/q^(1 + sigma/tau), c0 = 1/(2*kappa).
   Constructivity. Statements and premise positions are Set-carried
   (piu_mu_QleT, piu_mu_QltT, piu_mu_QeqT, piu_mu_ZleT, piu_mu_NleT,
   piu_mu_and2, piu_mu_and3, sigT); Prop reasoning stays inside proofs;
   definitions are transparent; undecidable premises (Hp, Hcoef, Hval,
   Htri, Hesc) are disclosed as explicit Set-shaped section premises;
   Print Assumptions: Closed under the global context for all seven exports.
   Build. rocq c -native-compiler no -q -Q . "" piu_mu_criterion.v
   ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Qring.
From Stdlib Require Import ZArith Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import Qpower.

Inductive piu_mu_QleT (x y : Q) : Set :=
  piu_mu_QleT_i : x <= y -> piu_mu_QleT x y.

Inductive piu_mu_QltT (x y : Q) : Set :=
  piu_mu_QltT_i : x < y -> piu_mu_QltT x y.

Inductive piu_mu_QeqT (x y : Q) : Set :=
  piu_mu_QeqT_i : x == y -> piu_mu_QeqT x y.

Inductive piu_mu_ZleT (x y : Z) : Set :=
  piu_mu_ZleT_i : (x <= y)%Z -> piu_mu_ZleT x y.

Inductive piu_mu_NleT (x y : nat) : Set :=
  piu_mu_NleT_i : (x <= y)%nat -> piu_mu_NleT x y.

Inductive piu_mu_and2 (S1 S2 : Set) : Set :=
  piu_mu_and2_i : S1 -> S2 -> piu_mu_and2 S1 S2.

Inductive piu_mu_and3 (S1 S2 S3 : Set) : Set :=
  piu_mu_and3_i : S1 -> S2 -> S3 -> piu_mu_and3 S1 S2 S3.

Lemma piu_mu_Zle_Qle : forall x y : Z, (x <= y)%Z -> piu_mu_QleT (inject_Z x) (inject_Z y).
Proof.
  intros x y H. apply piu_mu_QleT_i. unfold Qle, inject_Z.
  destruct x as [|px|px]; destruct y as [|py|py]; cbn; lia.
Qed.

Lemma piu_mu_Zlt_Qlt : forall z : Z, (0 < z)%Z -> piu_mu_QltT 0 (inject_Z z).
Proof.
  intros z H. apply piu_mu_QltT_i. unfold Qlt, inject_Z.
  destruct z as [|pz|pz]; cbn in H; cbn; lia.
Qed.

Lemma piu_mu_double :
  forall z : Z, piu_mu_QeqT (inject_Z (2 * z)) ((2 # 1) * inject_Z z).
Proof.
  intros z. apply piu_mu_QeqT_i. unfold Qeq, inject_Z, Qmult.
  destruct z as [|pz|pz]; cbn; lia.
Qed.

Lemma piu_mu_Qinv_nonneg : forall y : Q, (0 < y)%Q -> piu_mu_QleT 0 (/ y).
Proof.
  intros y Hy. apply piu_mu_QleT_i.
  destruct (Qlt_le_dec 0 (/ y)) as [H | H].
  - exact (Qlt_le_weak _ _ H).
  - exfalso.
    assert (Hyy : (y * / y == 1)%Q) by (apply Qmult_inv_r; lra).
    pose proof (Qmult_le_compat_r (/ y) 0 y H (Qlt_le_weak 0 y Hy)) as Hle2.
    lra.
Qed.

Lemma piu_mu_mult_le_r_inv :
  forall x y z : Q, (0 < z)%Q -> (x * z <= y * z)%Q -> piu_mu_QleT x y.
Proof.
  intros x y z Hz H. apply piu_mu_QleT_i.
  destruct (Qlt_le_dec y x) as [Hyx | Hyx].
  - exfalso.
    pose proof (Qmult_lt_compat_r y x z Hz Hyx) as Hlt.
    pose proof (Qlt_le_weak _ _ Hlt) as Hle1.
    pose proof (Qle_antisym _ _ H Hle1) as Heq.
    rewrite Heq in Hlt.
    lra.
  - exact Hyx.
Qed.

Lemma piu_mu_pow_ge :
  forall (x y : Q) (t : Z), (0 < y)%Q -> (y <= x)%Q -> (1 <= t)%Z ->
    piu_mu_QleT (Qpower y t) (Qpower x t).
Proof.
  intros x y t Hy Hle Ht. apply piu_mu_QleT_i.
  assert (Hyy : (y * / y == 1)%Q) by (apply Qmult_inv_r; lra).
  assert (Hr1 : (1 <= x * / y)%Q).
  { rewrite <- Hyy.
    apply (Qmult_le_compat_r y x (/ y)).
    - exact Hle.
    - destruct (piu_mu_Qinv_nonneg y Hy) as [Hnn]. exact Hnn. }
  assert (Ht0 : (0 <= t)%Z) by lia.
  assert (Hrp : (1 <= Qpower x t * Qpower (/ y) t)%Q).
  { pose proof (Qpower_1_le (x * / y) t Hr1 Ht0) as H0.
    rewrite Qmult_power in H0. exact H0. }
  assert (Hpinv : (Qpower (/ y) t * Qpower y t == 1)%Q).
  { rewrite <- (Qmult_power (/ y) y t).
    rewrite (Qmult_comm (/ y) y), Hyy.
    apply Qpower_1. }
  assert (Hone : (0 < (1 # 1))%Q) by lra.
  assert (Hmul : (Qpower y t * (1 # 1) <= Qpower x t * (1 # 1))%Q).
  { pose proof (Qmult_le_compat_r (1 # 1) (Qpower x t * Qpower (/ y) t)
    (Qpower y t) Hrp (Qpower_0_le y t (Qlt_le_weak 0 y Hy))) as Hm.
  rewrite <- (Qmult_assoc (Qpower x t) (Qpower (/ y) t) (Qpower y t)) in Hm.
  rewrite Hpinv in Hm.
  rewrite Qmult_1_l, Qmult_1_r in Hm.
  rewrite !Qmult_1_r.
  exact Hm. }
  destruct (piu_mu_mult_le_r_inv (Qpower y t) (Qpower x t) (1 # 1) Hone Hmul)
    as [Hfin].
  exact Hfin.
Qed.

Section PiuMuCriterion.

Variable sigma tau : nat.
Variable dval : Z -> Z -> Q.
Variable A B : nat -> Z.
Variable kappa : Q.

(* Exponential scale: the powers 2^k carried in Q *)
Definition piu_mu_epos (k : nat) : Q := inject_Z (2 ^ Z.of_nat k).

(* Root-form measure constant c0 = 1/(2*kappa): the tau-th-power form of
   the statement is order-equivalent to it on the positive domain
   (see the file header). *)
Definition piu_mu_c0 : Q := (1 # 1) / (2 * kappa)%Q.

(* q^(-mu) approximation lower-bound face (tau-th-power form): for all
   q >= 1, cnum^tau <= kappa^tau * |q*x-p|^tau * q^(sigma+tau) *)
Definition piu_mu_MuBound (cnum : Q) : Set :=
  forall (p : Z) (q : nat), (1 <= q)%nat ->
    piu_mu_QleT (Qpower cnum (Z.of_nat tau))
      ((Qpower kappa (Z.of_nat tau)
        * Qpower (dval (Z.of_nat q) (- p)) (Z.of_nat tau)
        * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (sigma + tau)))%Q).

Hypothesis Htau : piu_mu_NleT 1 tau.
Hypothesis Hkap : piu_mu_QltT 0 kappa.
Hypothesis Hp : forall a b : Z, piu_mu_QleT 0 (dval a b).
Hypothesis Hcoef : forall n : nat,
  piu_mu_and2
    (piu_mu_ZleT (Z.abs (A n)) (2 ^ Z.of_nat (sigma * n))%Z)
    (piu_mu_ZleT (Z.abs (B n)) (2 ^ Z.of_nat (sigma * n))%Z).
Hypothesis Hval : forall n : nat,
  piu_mu_QleT (dval (A n) (B n) * piu_mu_epos (tau * n)) (1 # 1).
Hypothesis Htri : forall (a b p : Z) (q : nat), (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
    ((inject_Z (Z.of_nat q) * dval a b
      + inject_Z (Z.abs b) * dval (Z.of_nat q) (- p))%Q).
Hypothesis Hesc : forall (p : Z) (q : nat), (1 <= q)%nat ->
  sigT (fun n : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (tau * n)))
    (piu_mu_ZleT 1 (Z.abs (A n * Z.of_nat q + B n * p)))
    (piu_mu_QleT (Qpower (piu_mu_epos (sigma * n)) (Z.of_nat tau))
      (Qpower kappa (Z.of_nat tau)
       * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (sigma + tau)))%Q)).

(* Core estimate: the measure lower bound at a single escape index
   (2q <= 2^(tau*n) together with |A(n)*q+B(n)*p| >= 1 yields
    |q*x-p| * 2^(sigma*n) >= 1/2) *)
Theorem piu_mu_core : forall (p : Z) (q : nat) (n : nat), (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (tau * n)) ->
  piu_mu_ZleT 1 (Z.abs (A n * Z.of_nat q + B n * p)) ->
  piu_mu_QleT ((1 # 2)%Q)
    (dval (Z.of_nat q) (- p) * piu_mu_epos (sigma * n)).
Proof.
  intros p q n Hq E1 E2.
  destruct E2 as [Hnz].
  destruct (Hcoef n) as [_ HB]. destruct HB as [HB].
  destruct (Hval n) as [Hv].
  destruct (Htri (A n) (B n) p q Hq) as [Htr].
  destruct E1 as [He1].
  destruct (Hp (Z.of_nat q) (- p)) as [Hwpos].
  destruct (Hp (A n) (B n)) as [Hdvpos].
  destruct (piu_mu_Zle_Qle _ _ HB) as [HBQ].
  destruct (piu_mu_Zle_Qle _ _ Hnz) as [HnzQ].
  assert (Hz2 : (Z.of_nat (2 * q) = 2 * Z.of_nat q)%Z) by lia.
  assert (He1' : (inject_Z (2 * Z.of_nat q) <= piu_mu_epos (tau * n))%Q).
  { rewrite <- Hz2. exact He1. }
  destruct (piu_mu_double (Z.of_nat q)) as [Hdbl].
  rewrite Hdbl in He1'.
  change (inject_Z 1) with (1 # 1) in HnzQ.
  set (qQ := inject_Z (Z.of_nat q)) in *.
  set (dv := dval (A n) (B n)) in *.
  set (w := dval (Z.of_nat q) (- p)) in *.
  set (bQ := inject_Z (Z.abs (B n))) in *.
  set (tv := piu_mu_epos (tau * n)) in *.
  set (s := piu_mu_epos (sigma * n)) in *.
  (* Step 1: 2*qQ*dv <= 1 *)
  assert (Hs1 : ((2 # 1) * qQ * dv <= 1)%Q).
  { apply (Qle_trans _ (dv * tv) 1).
    - rewrite (Qmult_comm dv tv).
      apply (Qmult_le_compat_r ((2 # 1) * qQ) tv dv).
      + exact He1'.
      + exact Hdvpos.
    - exact Hv. }
  (* Step 2: bQ*w >= 1/2 (from Htri, HnzQ, Hs1) *)
  assert (Hbw : ((1 # 2) <= bQ * w)%Q) by lra.
  (* Step 3: w*s >= 1/2 (from bQ <= s and w >= 0) *)
  assert (Hws : ((1 # 2) <= w * s)%Q).
  { apply (Qle_trans _ (w * bQ) (w * s)).
    - lra.
    - rewrite (Qmult_comm w bQ), (Qmult_comm w s).
      apply (Qmult_le_compat_r bQ s w).
      + exact HBQ.
      + exact Hwpos. }
  apply piu_mu_QleT_i. exact Hws.
Qed.

(* Main theorem: the q^(-mu) approximation lower-bound form of the
   linear-form criterion (tau-th power) *)
Theorem piu_mu_criterion : piu_mu_MuBound (1 # 2).
Proof.
  intros p q Hq.
  destruct (Hesc p q Hq) as [n [E1q E2z E3q]].
  destruct E3q as [E3q].
  destruct Htau as [Htd].
  pose proof (piu_mu_core p q n Hq E1q E2z) as Hcore.
  destruct Hcore as [Hcore].
  destruct (Hp (Z.of_nat q) (- p)) as [Hwpos].
  destruct Hkap as [Hk0].
  set (w := dval (Z.of_nat q) (- p)) in *.
  set (s := piu_mu_epos (sigma * n)) in *.
  (* Step 1: (1/2)^tau <= w^tau * s^tau *)
  assert (Hstep1 : (Qpower (1 # 2) (Z.of_nat tau)
              <= Qpower w (Z.of_nat tau) * Qpower s (Z.of_nat tau))%Q).
  { rewrite <- (Qmult_power w s (Z.of_nat tau)).
    assert (Hc0 : (0 < (1 # 2))%Q) by lra.
    assert (Htz : (1 <= Z.of_nat tau)%Z).
    { pose proof (proj1 (Nat2Z.inj_le 1 tau) Htd) as Hz.
      change (Z.of_nat 1) with 1%Z in Hz. exact Hz. }
    destruct (piu_mu_pow_ge (w * s) (1 # 2) (Z.of_nat tau) Hc0 Hcore Htz)
      as [HP].
    exact HP. }
  (* Step 2: s^tau * w^tau <= (kappa^tau * q^(sigma+tau)) * w^tau *)
  assert (Hstep2 : (Qpower s (Z.of_nat tau) * Qpower w (Z.of_nat tau)
              <= Qpower kappa (Z.of_nat tau)
                 * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (sigma + tau))
                 * Qpower w (Z.of_nat tau))%Q).
  { apply (Qmult_le_compat_r (Qpower s (Z.of_nat tau))
             (Qpower kappa (Z.of_nat tau)
              * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (sigma + tau)))
             (Qpower w (Z.of_nat tau))).
    - exact E3q.
    - apply (Qpower_0_le w (Z.of_nat tau)). exact Hwpos. }
  (* Step 3: finishes with the linear atom chain *)
  apply piu_mu_QleT_i.
  lra.
Qed.

End PiuMuCriterion.

Print Assumptions piu_mu_core.
Print Assumptions piu_mu_criterion.
Print Assumptions piu_mu_Zle_Qle.
Print Assumptions piu_mu_Zlt_Qlt.
Print Assumptions piu_mu_double.
Print Assumptions piu_mu_mult_le_r_inv.
Print Assumptions piu_mu_pow_ge.
