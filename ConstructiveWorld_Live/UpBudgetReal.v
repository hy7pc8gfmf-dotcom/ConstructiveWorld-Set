(* ConstructiveWorld-Set -- the Real-layer explicit iteration budget theorem for geometric breakdown. *)
(** * UpBudgetReal: the Real-layer construction of paper 4's (gradient
    dynamics convergence) "explicit iteration budget" over the concrete
    Cauchy reals, closing the gap in the ConvergenceCauchy section's
    [r_arch_pow] interface premises.

    Mission.  [r_arch_pow_real]: for κ a eps with 0<κ<1, 0<a, 0<eps, an
      explicit nat witness N with a·κ^N < eps.  Route: i := 1/κ > 1,
      c := i − 1 > 0; Bernoulli i^N ≥ 1 + (N#1)·c bounds the power below;
      the budget real y := (a/eps)/c is solved for N by [real_arch]; the
      reciprocal contravariance ([real_inv_pos_lt_contra]) and the pow·inv
      identity return a·κ^N < eps.  [budget_cond_sufficient]: sufficiency
      of the budget condition (log power identity + strictly monotone exp
      inversion).  [geo_tail_budget]/[budget_min_tail]: the min tail bound
      and its budget combination (pure order algebra).  The power operation
      existed previously only as an interface assumption; this module is the pure Real-layer route.

    Dependencies.  [S01_BaseRing] .. [S15_TailFEPUp] (the full Require face);
      Stdlib [QArith], [Lia], [Extraction]; [hlogz_strict] self-contained
      (the in-root G01 piece is absent here; born-clean re-proved from
      [real_log_lt_mono] + [real_log_one]).

    References.  Paper 4 Theorem 4.10 (tail bound a·κ^{min m n}); the same-name ConstructiveWorld-Main baseline.

    Constructivity.  Purely constructive; Set-layer statements
      ([real_lt]/[real_le]/[real_eq]/[sigT]/[NatLe]); Qed-closed; nat-order
      premises uniformly Set-layer NatLe ([NatLe_drop] bridging to lia);
      in-root proven machinery reused without re-proving.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" UpBudgetReal.v] (direct call, cpu_guard wrapped). *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.

Local Open Scope Q_scope.

(* ============ 0. the concrete real-layer power (the Real-layer r_pow) ============ *)

Fixpoint real_pow (x : Real) (n : nat) : Real :=
  match n with
  | O => real_one
  | Datatypes.S m => real_mult x (real_pow x m)
  end.

(* The same-name interface from the task specification: r_pow kappa N is
   real_pow kappa N *)
Notation r_pow := real_pow (only parsing).

(* Compatibility of the power with real_eq *)
Lemma real_pow_eq_compat : forall (x y : Real) (n : nat),
  real_eq x y -> real_eq (real_pow x n) (real_pow y n).
Proof.
  intros x y n Hxy. induction n as [| m IH].
  - apply real_eq_refl.
  - cbn [real_pow].
    apply (RealSetoid.real_eq_mult_compat x (real_pow x m) y (real_pow y m)).
    + exact Hxy.
    + exact IH.
Qed.

(* Power positivity: 0 < x implies 0 < x^n *)
Lemma bud_real_pow_pos : forall (x : Real) (n : nat),
  real_lt real_zero x -> real_lt real_zero (real_pow x n).
Proof.
  intros x n Hx. induction n as [| m IH].
  - exact real_lt_zero_one.
  - cbn [real_pow]. exact (real_mult_pos_compat x (real_pow x m) Hx IH).
Qed.

(* ============ 1. basic algebra utilities (filling the gaps absent from the 217 root) ============ *)

(* 0#1 == 0 (the nat-embedded zero) *)
Lemma real_const_zero_thm : real_eq (real_const (Z.of_nat 0 # 1)) real_zero.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  change (projT1 (real_const (Z.of_nat 0 # 1)) n) with 0%Q.
  change (projT1 real_zero n) with 0%Q.
  apply qeq_imp_qeqT.
  ring.
Qed.

(* 1·x == x (the in-root real_mult_one has the x·1 shape) *)
Lemma real_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans _ (real_mult x real_one)).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* 0·x == 0 (the in-root real_mult_zero has the x·0 shape) *)
Lemma real_mult_zero_l : forall x : Real, real_eq (real_mult real_zero x) real_zero.
Proof.
  intro x.
  apply (real_eq_trans _ (real_mult x real_zero)).
  - apply real_mult_comm.
  - apply real_mult_zero.
Qed.

(* Successor step of the nat-embedded multiplication:
   (S n)#1·x == (n#1)·x + x *)
Lemma real_nat_mult_succ : forall (n : nat) (x : Real),
  real_eq (real_mult (real_const (Z.of_nat (Datatypes.S n) # 1)) x)
          (real_plus (real_mult (real_const (Z.of_nat n # 1)) x) x).
Proof.
  intros n x.
  apply (real_eq_trans _ (real_mult (real_plus (real_const (Z.of_nat n # 1)) real_one) x)).
  - apply (RealSetoid.real_eq_mult_compat (real_const (Z.of_nat (Datatypes.S n) # 1)) x
                                          (real_plus (real_const (Z.of_nat n # 1)) real_one) x).
    + apply b4_lift_succ.
    + apply real_eq_refl.
  - apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat n # 1)) x)
                                      (real_mult real_one x))).
    + apply (real_eq_sym _ _ (real_distrib_r_local (real_const (Z.of_nat n # 1)) real_one x)).
    + apply (RealSetoid.real_eq_plus_compat (real_mult (real_const (Z.of_nat n # 1)) x)
                                            (real_mult real_one x)
                                            (real_mult (real_const (Z.of_nat n # 1)) x) x).
      * apply real_eq_refl.
      * apply real_mult_one_l.
Qed.

(* A supplement on reciprocal uniqueness: inv 1 == 1 (the in-root
   real_inv_one_local already provides it; used directly) *)
(* (not re-proved here; see real_inv_one_local) *)

(* Dedicated to reciprocal positivity: the bridge to 1 < 1/κ
   ([real_inv_pos_lt_contra] + inv 1 == 1) *)

(* ============ 2. the power·reciprocal identity (κ^N · (1/κ)^N == 1) ============ *)

Lemma real_pow_inv_pair : forall (k : Real) (Hk : real_lt real_zero k) (n : nat),
  real_eq (real_mult (real_pow k n) (real_pow (real_inv_pos k Hk) n)) real_one.
Proof.
  intros k Hk n. induction n as [| m IH].
  - cbn [real_pow]. apply real_mult_one.
  - cbn [real_pow].
    (* (k·k^m)·(i·i^m) == 1，i := 1/κ *)
    apply (real_eq_trans _ (real_mult (real_mult (real_pow k m) k)
                                      (real_mult (real_inv_pos k Hk)
                                                 (real_pow (real_inv_pos k Hk) m)))).
    + apply (RealSetoid.real_eq_mult_compat
               (real_mult k (real_pow k m))
               (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m))
               (real_mult (real_pow k m) k)
               (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m))).
      * apply real_mult_comm.
      * apply real_eq_refl.
    + apply (real_eq_trans _ (real_mult (real_pow k m)
                                        (real_mult k (real_mult (real_inv_pos k Hk)
                                                                (real_pow (real_inv_pos k Hk) m))))).
      * apply (real_eq_sym _ _ (real_mult_assoc (real_pow k m) k
                         (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m)))).
      * apply (real_eq_trans _ (real_mult (real_pow k m)
                                          (real_mult (real_mult k (real_inv_pos k Hk))
                                                     (real_pow (real_inv_pos k Hk) m)))).
        -- apply (RealSetoid.real_eq_mult_compat (real_pow k m)
                   (real_mult k (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m)))
                   (real_pow k m)
                   (real_mult (real_mult k (real_inv_pos k Hk)) (real_pow (real_inv_pos k Hk) m))).
           ++ apply real_eq_refl.
           ++ apply (real_mult_assoc k (real_inv_pos k Hk)
                                        (real_pow (real_inv_pos k Hk) m)).
        -- apply (real_eq_trans _ (real_mult (real_pow k m)
                                             (real_mult real_one (real_pow (real_inv_pos k Hk) m)))).
           ++ apply (RealSetoid.real_eq_mult_compat (real_pow k m)
                      (real_mult (real_mult k (real_inv_pos k Hk)) (real_pow (real_inv_pos k Hk) m))
                      (real_pow k m)
                      (real_mult real_one (real_pow (real_inv_pos k Hk) m))).
              ** apply real_eq_refl.
              ** apply (RealSetoid.real_eq_mult_compat (real_mult k (real_inv_pos k Hk))
                          (real_pow (real_inv_pos k Hk) m) real_one (real_pow (real_inv_pos k Hk) m)).
                 --- exact (real_inv_pos_correct k Hk).
                 --- apply real_eq_refl.
           ++ apply (real_eq_trans _ (real_mult (real_pow k m)
                                                (real_pow (real_inv_pos k Hk) m))).
              ** apply (RealSetoid.real_eq_mult_compat (real_pow k m)
                          (real_mult real_one (real_pow (real_inv_pos k Hk) m))
                          (real_pow k m) (real_pow (real_inv_pos k Hk) m)).
                 --- apply real_eq_refl.
                 --- apply real_mult_one_l.
              ** exact IH.
Qed.

(* ============ 3. le/lt auxiliaries (1 ≤ 1+x, 0 ≤ (n#1)·x, y < 1+y) ============ *)

Lemma bud_real_le_one_plus : forall x : Real,
  real_le real_zero x -> real_le real_one (real_plus real_one x).
Proof.
  intros x Hx.
  apply (real_le_trans _ (real_plus real_one real_zero)).
  - apply real_eq_le_bridge.
    apply (real_eq_sym _ _ (real_plus_zero real_one)).
  - exact (real_le_plus_compat real_one real_one real_zero x (real_le_refl real_one) Hx).
Qed.

Lemma real_lt_plus_one : forall y : Real, real_lt y (real_plus real_one y).
Proof.
  intro y.
  apply (real_eq_lt_lt y (real_plus real_zero y) (real_plus real_one y)).
  - exact (real_eq_sym (real_plus real_zero y) y (sf_real_plus_zero_l y)).
  - exact (real_lt_plus_compat_lt_le real_zero real_one y y real_lt_zero_one (real_le_refl y)).
Qed.

(* (n#1)·x is nonnegative: 0 < x implies 0 ≤ (n#1)·x (a nat-embedded
   multiple is nonnegative) *)
Lemma real_nat_mult_nonneg : forall (n : nat) (x : Real),
  real_lt real_zero x -> real_le real_zero (real_mult (real_const (Z.of_nat n # 1)) x).
Proof.
  intros n x Hx. induction n as [| m IH].
  - apply real_eq_le_bridge.
    apply (real_eq_trans _ (real_mult real_zero x)).
    + apply (real_eq_sym _ _ (real_mult_zero_l x)).
    + apply (RealSetoid.real_eq_mult_compat real_zero x (real_const (Z.of_nat 0 # 1)) x).
      * apply (real_eq_sym _ _ real_const_zero_thm).
      * apply real_eq_refl.
  - apply real_lt_le_bridge.
    apply (real_lt_eq_lt _ (real_plus (real_mult (real_const (Z.of_nat m # 1)) x) x)).
    + apply (real_lt_eq_lt _ (real_plus x (real_mult (real_const (Z.of_nat m # 1)) x))).
      * apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)).
        -- exact (real_eq_sym _ _ (real_plus_zero real_zero)).
        -- exact (real_lt_plus_compat_lt_le real_zero x real_zero
                    (real_mult (real_const (Z.of_nat m # 1)) x) Hx IH).
      * apply real_plus_comm.
    + apply (real_eq_sym _ _ (real_nat_mult_succ m x)).
Qed.

(* ============ 4. the Bernoulli power lower bound: (1+c)^n ≥ 1 + (n#1)·c (c > 0) ============ *)

Lemma bernoulli_pow : forall (c : Real) (Hc : real_lt real_zero c) (n : nat),
  real_le (real_plus real_one (real_mult (real_const (Z.of_nat n # 1)) c))
          (real_pow (real_plus real_one c) n).
Proof.
  intros c Hc n. induction n as [| m IH].
  - cbn [real_pow].
    apply (real_le_trans _ real_one).
    + apply real_eq_le_bridge.
      apply (real_eq_trans _ (real_plus real_one real_zero)).
      * apply (RealSetoid.real_eq_plus_compat real_one
                 (real_mult (real_const (Z.of_nat 0 # 1)) c) real_one real_zero).
        -- apply real_eq_refl.
        -- apply (real_eq_trans _ (real_mult real_zero c)).
           ++ apply (RealSetoid.real_eq_mult_compat (real_const (Z.of_nat 0 # 1)) c
                       real_zero c).
              ** exact real_const_zero_thm.
              ** apply real_eq_refl.
           ++ apply (real_mult_zero_l c).
      * exact (real_plus_zero real_one).
    + apply real_le_refl.
  - cbn [real_pow].
    apply (real_le_trans _ (real_plus (real_plus real_one (real_mult (real_const (Z.of_nat m # 1)) c)) c)).
    + (* 1 + (S m)#1·c == (1 + m#1·c) + c *)
      apply real_eq_le_bridge.
      apply (real_eq_trans _ (real_plus real_one (real_plus (real_mult (real_const (Z.of_nat m # 1)) c) c))).
      * apply (RealSetoid.real_eq_plus_compat real_one
                 (real_mult (real_const (Z.of_nat (Datatypes.S m) # 1)) c)
                 real_one
                 (real_plus (real_mult (real_const (Z.of_nat m # 1)) c) c)).
        -- apply real_eq_refl.
        -- apply (real_nat_mult_succ m c).
      * apply real_plus_assoc.
    + (* (1 + m#1·c) + c ≤ (1+c)·(1+c)^m *)
      apply (real_le_trans _ (real_plus (real_pow (real_plus real_one c) m)
                                        (real_mult c (real_pow (real_plus real_one c) m)))).
      * assert (Hx0 : real_le real_zero (real_mult (real_const (Z.of_nat m # 1)) c))
          by exact (real_nat_mult_nonneg m c Hc).
        assert (H1P : real_le real_one (real_pow (real_plus real_one c) m)).
        { apply (real_le_trans _ (real_plus real_one (real_mult (real_const (Z.of_nat m # 1)) c))).
          - exact (bud_real_le_one_plus _ Hx0).
          - exact IH. }
        apply (real_le_plus_compat _ _ _ _ IH).
        (* c ≤ c·(1+c)^m *)
        apply (real_le_trans _ (real_mult c real_one)).
        -- apply real_eq_le_bridge.
           apply (real_eq_sym _ _ (real_mult_one c)).
        -- apply (real_le_trans _ (real_mult real_one c)).
           ++ apply real_eq_le_bridge.
              exact (real_mult_comm c real_one).
           ++ apply (real_le_trans _ (real_mult (real_pow (real_plus real_one c) m) c)).
              ** exact (real_le_mult_compat real_one (real_pow (real_plus real_one c) m) c Hc H1P).
              ** apply real_eq_le_bridge.
                 exact (real_mult_comm (real_pow (real_plus real_one c) m) c).
      * (* P + c·P == (1+c)·P *)
        apply real_eq_le_bridge.
        apply (real_eq_trans _ (real_plus (real_mult real_one (real_pow (real_plus real_one c) m))
                                          (real_mult c (real_pow (real_plus real_one c) m)))).
        -- apply (RealSetoid.real_eq_plus_compat (real_pow (real_plus real_one c) m)
                    (real_mult c (real_pow (real_plus real_one c) m))
                    (real_mult real_one (real_pow (real_plus real_one c) m))
                    (real_mult c (real_pow (real_plus real_one c) m))).
           ++ apply (real_eq_sym _ _ (real_mult_one_l (real_pow (real_plus real_one c) m))).
           ++ apply real_eq_refl.
        -- exact (real_distrib_r_local real_one c (real_pow (real_plus real_one c) m)).
Qed.


(* ============ 5. piece-2 main theorem: the Real-layer explicit nat budget for geometric breakdown ============ *)
(*   The explicit shape of N: the nat solved by real_arch on the budget real
    y := (a/eps)/(1/κ − 1). *)

Theorem r_arch_pow_real :
  forall (kappa : Real) (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (a : Real) (Ha : real_lt real_zero a) (eps : Real) (Heps : real_lt real_zero eps),
  sigT (fun N : nat => real_lt (real_mult a (r_pow kappa N)) eps).
Proof.
  intros kappa Hk1 Hk2 a Ha eps Heps.
  assert (Hinvpos : real_lt real_zero (real_inv_pos kappa Hk1))
    by exact (real_inv_pos_pos kappa Hk1).
  assert (HoneLtInv : real_lt real_one (real_inv_pos kappa Hk1)).
  { apply (real_eq_lt_lt real_one (real_inv_pos real_one real_lt_zero_one)
                         (real_inv_pos kappa Hk1)).
    - apply (real_eq_sym _ _ real_inv_one_local).
    - exact (real_inv_pos_lt_contra kappa real_one Hk1 real_lt_zero_one Hk2). }
  assert (Hc : real_lt real_zero (real_plus (real_inv_pos kappa Hk1) (real_opp real_one)))
    by exact (real_lt_opp_plus real_one (real_inv_pos kappa Hk1) HoneLtInv).
  assert (Hax : real_lt real_zero (real_mult a (real_inv_pos eps Heps)))
    by exact (real_mult_pos_compat a (real_inv_pos eps Heps) Ha (real_inv_pos_pos eps Heps)).
  set (c := real_plus (real_inv_pos kappa Hk1) (real_opp real_one)) in Hc |- *.
  set (x := real_mult a (real_inv_pos eps Heps)) in Hax |- *.
  assert (Hyc : real_lt real_zero (real_mult x (real_inv_pos c Hc)))
    by exact (real_mult_pos_compat x (real_inv_pos c Hc) Hax (real_inv_pos_pos c Hc)).
  destruct (real_arch (real_mult x (real_inv_pos c Hc))) as [N [HN2 HN]].
  (* x < (N#1)·c: (x·(1/c))·c == x (the reshaping by real_mult_div), then
   multiplying by c preserves the order *)
  assert (Hxc_lt : real_lt x (real_mult (real_const (Z.of_nat N # 1)) c)).
  { apply (real_eq_lt_lt x (real_mult (real_mult x (real_inv_pos c Hc)) c)).
    - apply (real_eq_trans _ (real_mult c (real_mult x (real_inv_pos c Hc)))).
      + apply (real_eq_sym _ _ (real_mult_div c x Hc)).
      + apply real_mult_comm.
    - exact (real_mult_lt_compat (real_mult x (real_inv_pos c Hc))
               (real_const (Z.of_nat N # 1)) c HN Hc). }
  (* 1 + c == 1/κ *)
  assert (Honec : real_eq (real_plus real_one c) (real_inv_pos kappa Hk1)).
  { unfold c. apply (real_eq_trans _ (real_plus (real_plus real_one (real_inv_pos kappa Hk1))
                                                (real_opp real_one))).
    - apply real_plus_assoc.
    - apply (real_eq_trans _ (real_plus (real_plus (real_inv_pos kappa Hk1) real_one)
                                        (real_opp real_one))).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_plus real_one (real_inv_pos kappa Hk1)) (real_opp real_one)
                 (real_plus (real_inv_pos kappa Hk1) real_one) (real_opp real_one)).
        * apply real_plus_comm.
        * apply real_eq_refl.
      + apply (real_eq_trans _ (real_plus (real_inv_pos kappa Hk1)
                                          (real_plus real_one (real_opp real_one)))).
        * apply (real_eq_sym _ _ (real_plus_assoc (real_inv_pos kappa Hk1) real_one
                                                    (real_opp real_one))).
        * apply (real_eq_trans _ (real_plus (real_inv_pos kappa Hk1) real_zero)).
          -- apply (RealSetoid.real_eq_plus_compat (real_inv_pos kappa Hk1)
                      (real_plus real_one (real_opp real_one))
                      (real_inv_pos kappa Hk1) real_zero).
             ++ apply real_eq_refl.
             ++ apply real_plus_opp.
          -- apply (real_plus_zero (real_inv_pos kappa Hk1)). }
  (* x < 1 + (N#1)·c ≤ (1+c)^N == (1/κ)^N (Bernoulli le + strict on the first
   segment) *)
  assert (Hkey : real_lt x (real_pow (real_inv_pos kappa Hk1) N)).
  { apply (real_lt_eq_lt _ (real_pow (real_plus real_one c) N)).
    - apply (real_lt_le_trans _ (real_plus real_one (real_mult (real_const (Z.of_nat N # 1)) c))).
      + apply (real_lt_trans _ (real_mult (real_const (Z.of_nat N # 1)) c)).
        * exact Hxc_lt.
        * exact (real_lt_plus_one _).
      + exact (bernoulli_pow c Hc N).
    - apply (real_pow_eq_compat _ _ N Honec). }
  (* κ^N == 1/(1/κ)^N (the pow·inv identity + reciprocal uniqueness) *)
  assert (HposN : real_lt real_zero (real_pow (real_inv_pos kappa Hk1) N))
    by exact (bud_real_pow_pos _ N Hinvpos).
  assert (Hpowinv : real_eq (real_pow kappa N)
                            (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)).
  { apply (real_inv_unique (real_pow (real_inv_pos kappa Hk1) N) (real_pow kappa N)
                           (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)).
    - apply (real_eq_trans _ (real_mult (real_pow kappa N)
                                        (real_pow (real_inv_pos kappa Hk1) N))).
      + apply real_mult_comm.
      + exact (real_pow_inv_pair kappa Hk1 N).
    - exact (real_inv_pos_correct (real_pow (real_inv_pos kappa Hk1) N) HposN). }
  (* 1/x == eps·(1/a) (real_inv_unique applied at x·(eps·(1/a)) == 1) *)
  assert (Hinva : real_eq (real_inv_pos x Hax) (real_mult eps (real_inv_pos a Ha))).
  { apply (real_inv_unique x (real_inv_pos x Hax) (real_mult eps (real_inv_pos a Ha))).
    - exact (real_inv_pos_correct x Hax).
    - apply (real_eq_trans _ (real_mult a
                 (real_mult (real_inv_pos eps Heps) (real_mult eps (real_inv_pos a Ha))))).
      + apply (real_eq_sym _ _ (real_mult_assoc a (real_inv_pos eps Heps)
                                  (real_mult eps (real_inv_pos a Ha)))).
      + apply (real_eq_trans _ (real_mult a
                 (real_mult (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha)))).
        * apply (RealSetoid.real_eq_mult_compat a
                    (real_mult (real_inv_pos eps Heps) (real_mult eps (real_inv_pos a Ha)))
                    a
                    (real_mult (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha))).
          -- apply real_eq_refl.
          -- apply (real_mult_assoc (real_inv_pos eps Heps) eps
                                                       (real_inv_pos a Ha)).
        * apply (real_eq_trans _ (real_mult a (real_mult real_one (real_inv_pos a Ha)))).
          -- apply (RealSetoid.real_eq_mult_compat a
                      (real_mult (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha))
                      a
                      (real_mult real_one (real_inv_pos a Ha))).
             ++ apply real_eq_refl.
             ++ apply (RealSetoid.real_eq_mult_compat
                          (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha)
                          real_one (real_inv_pos a Ha)).
                ** apply (real_eq_trans _ (real_mult eps (real_inv_pos eps Heps))).
                   --- apply real_mult_comm.
                   --- exact (real_inv_pos_correct eps Heps).
                ** apply real_eq_refl.
          -- apply (real_eq_trans _ (real_mult a (real_inv_pos a Ha))).
             ++ apply (RealSetoid.real_eq_mult_compat a
                         (real_mult real_one (real_inv_pos a Ha)) a (real_inv_pos a Ha)).
                ** apply real_eq_refl.
                ** apply real_mult_one_l.
             ++ exact (real_inv_pos_correct a Ha). }
  assert (Hinvlt : real_lt (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)
                           (real_inv_pos x Hax)).
  { exact (real_inv_pos_lt_contra x (real_pow (real_inv_pos kappa Hk1) N) Hax HposN Hkey). }
  (* κ^N < eps·(1/a) *)
  assert (Hklt : real_lt (real_pow kappa N) (real_mult eps (real_inv_pos a Ha))).
  { apply (real_eq_lt_lt _ (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)).
    - exact Hpowinv.
    - exact (real_lt_eq_lt _ _ _ Hinvlt Hinva). }
  exists N.
  apply (real_lt_eq_lt (real_mult a (real_pow kappa N))
                       (real_mult a (real_mult eps (real_inv_pos a Ha)))).
  - exact (real_mult_lt_compat_l (real_pow kappa N)
             (real_mult eps (real_inv_pos a Ha)) a Hklt Ha).
  - exact (real_mult_div a eps Ha).
Qed.




(* The strict-negativity bridge for log: 0 < κ < 1 implies log κ < 0 (the
   born-clean form prepared in-module: real_log_lt_mono strict monotonicity
   plus real_log_one for the endpoint swap to 0; both are already proven at
   the S07 top level) *)
Lemma hlogz_strict :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_lt Za real_one),
  real_lt (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  apply (real_lt_eq_lt _ (cw_log real_one Hone) _).
  - unfold real_log.
    exact (real_log_lt_mono Za real_one HZa Hone HZa1).
  - exact (real_log_one Hone).
Qed.

Lemma log_kappa_neg : forall (kappa : Real)
                         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one),
  real_lt real_zero (real_opp (real_log kappa Hk1)).
Proof.
  intros kappa Hk1 Hk2.
  assert (Hneg : real_lt (real_log kappa Hk1) real_zero)
    by exact (hlogz_strict kappa Hk1 Hk2).
  apply (real_eq_lt_lt real_zero (real_opp real_zero) (real_opp (real_log kappa Hk1))).
  - apply (real_eq_sym _ _ real_opp_zero).
  - exact (real_opp_lt_compat (real_log kappa Hk1) real_zero Hneg).
Qed.

(* The log power identity: log(κ^N) == (N#1)·log κ (induction by
   real_log_mult) *)
Lemma real_pow_log_form : forall (k : Real) (Hk : real_lt real_zero k) (n : nat),
  real_eq (real_log (real_pow k n) (bud_real_pow_pos k n Hk))
          (real_mult (real_const (Z.of_nat n # 1)) (real_log k Hk)).
Proof.
  intros k Hk n. induction n as [| m IH].
  - apply (real_eq_trans _ real_zero).
    + apply real_log_one.
    + exact (real_eq_sym (real_mult (real_const (Z.of_nat 0 # 1)) (real_log k Hk)) real_zero
               (real_eq_trans (real_mult (real_const (Z.of_nat 0 # 1)) (real_log k Hk))
                              (real_mult real_zero (real_log k Hk)) real_zero
                              (RealSetoid.real_eq_mult_compat
                                 (real_const (Z.of_nat 0 # 1)) (real_log k Hk)
                                 real_zero (real_log k Hk)
                                 real_const_zero_thm (real_eq_refl (real_log k Hk)))
                              (real_mult_zero_l (real_log k Hk)))).
  - cbn [real_pow].
    apply (real_eq_trans _ (real_plus (real_log k Hk)
                                      (real_log (real_pow k m) (bud_real_pow_pos k m Hk)))).
    + exact (log_inv_mult_thm k (real_pow k m) Hk (bud_real_pow_pos k m Hk)
               (bud_real_pow_pos k (Datatypes.S m) Hk)).
    + apply (real_eq_trans _ (real_plus (real_log k Hk)
                   (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk)))).
      * apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _) IH).
      * apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat m # 1))
                                                        (real_log k Hk))
                                            (real_log k Hk))).
        -- apply (real_plus_comm (real_log k Hk)
                    (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk))).
        -- apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat m # 1))
                                                        (real_log k Hk))
                                             (real_log k Hk))).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk))
                       (real_log k Hk)
                       (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk))
                       (real_log k Hk)).
              ** apply real_eq_refl.
              ** apply real_eq_refl.
           ++ apply (real_eq_sym _ _ (real_nat_mult_succ m (real_log k Hk))).
Qed.

(* Piece-1 main piece: sufficiency of the budget condition
   (via the log polynomial identity + cauchy_real_exp_mono strict
   monotonicity + cw_log_exp_right inversion) *)
Theorem budget_cond_sufficient :
  forall (kappa a eps : Real)
         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps) (N : nat),
  real_lt (real_plus (real_log a Ha) (real_opp (real_log eps Heps)))
          (real_mult (real_const (Z.of_nat N # 1)) (real_opp (real_log kappa Hk1))) ->
  real_lt (real_mult a (real_pow kappa N)) eps.
Proof.
  intros kappa a eps Hk1 Hk2 Ha Heps N Hcond.

  
  assert (Hlogpow : real_eq (real_log (real_mult a (real_pow kappa N))
                                      (real_mult_positive a (real_pow kappa N) Ha (bud_real_pow_pos kappa N Hk1)))
                            (real_plus (real_log a Ha)
                                       (real_mult (real_const (Z.of_nat N # 1))
                                                  (real_log kappa Hk1)))).
  { apply (real_eq_trans _ (real_plus (real_log a Ha)
                                      (real_log (real_pow kappa N) (bud_real_pow_pos kappa N Hk1)))).
    - exact (real_log_mult a (real_pow kappa N) Ha (bud_real_pow_pos kappa N Hk1)).
    - apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)
               (real_pow_log_form kappa Hk1 N)). }
  (* N#1·logκ == −(N#1·(−logκ)) *)
  assert (Hnegm : real_eq (real_mult (real_const (Z.of_nat N # 1)) (real_log kappa Hk1))
                          (real_opp (real_mult (real_const (Z.of_nat N # 1))
                                               (real_opp (real_log kappa Hk1))))).
  { apply (real_eq_trans _ (real_mult (real_const (Z.of_nat N # 1))
                                      (real_opp (real_opp (real_log kappa Hk1))))).
    - apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)
               (real_eq_sym _ _ (real_opp_opp (real_log kappa Hk1)))).
    - apply real_mult_opp_l. }
  (* Condition reshaping: log a < N#1·(−logκ) + log eps
     (adding log eps to both sides of Hcond: La + −Le < W implies
     (La + −Le) + Le < W + Le) *)
  assert (Hmid : real_lt (real_log a Ha)
                         (real_plus (real_mult (real_const (Z.of_nat N # 1))
                                               (real_opp (real_log kappa Hk1)))
                                    (real_log eps Heps))).
  { apply (real_eq_lt_lt (real_log a Ha)
            (real_plus (real_plus (real_log a Ha) (real_opp (real_log eps Heps)))
                       (real_log eps Heps))).
    - apply (real_eq_trans _ (real_plus (real_log a Ha)
                   (real_plus (real_opp (real_log eps Heps)) (real_log eps Heps)))).
      + apply (real_eq_sym _ _).
        apply (real_eq_trans _ (real_plus (real_log a Ha) real_zero)).
        * apply (RealSetoid.real_eq_plus_compat (real_log a Ha)
                   (real_plus (real_opp (real_log eps Heps)) (real_log eps Heps))
                   (real_log a Ha) real_zero).
          -- apply real_eq_refl.
          -- exact (real_eq_trans _ _ _
                     (real_plus_comm (real_opp (real_log eps Heps)) (real_log eps Heps))
                     (real_plus_opp (real_log eps Heps))).
        * apply (real_plus_zero (real_log a Ha)).
      + apply (real_plus_assoc (real_log a Ha) (real_opp (real_log eps Heps))
                                 (real_log eps Heps)).
    - exact (real_lt_plus_compat_lt_le _ _ _ _ Hcond (real_le_refl (real_log eps Heps))). }
  (* Additive cancellation: x == La − W and La < W + Le imply x < Le (a pure
   addition lemma dedicated to piece 1) *)
  assert (Hshift : forall (x La Le W : Real),
            real_eq x (real_plus La (real_opp W)) ->
            real_lt La (real_plus W Le) ->
            real_lt x Le).
  { intros x0 La0 Le0 W0 H1 H2.
    apply (real_eq_lt_lt x0 (real_plus La0 (real_opp W0))).
    - exact H1.
    - apply (real_lt_eq_lt _ (real_plus (real_plus W0 Le0) (real_opp W0))).
      + exact (real_lt_plus_compat_lt_le _ _ _ _ H2 (real_le_refl _)).
      + exact (real_eq_trans
                 (real_plus (real_plus W0 Le0) (real_opp W0))
                 (real_plus W0 (real_plus Le0 (real_opp W0)))
                 Le0
                 (real_eq_sym _ _ (real_plus_assoc W0 Le0 (real_opp W0)))
                 (real_eq_trans
                    (real_plus W0 (real_plus Le0 (real_opp W0)))
                    (real_plus (real_plus W0 (real_opp W0)) Le0)
                    Le0
                    (real_eq_trans
                       (real_plus W0 (real_plus Le0 (real_opp W0)))
                       (real_plus W0 (real_plus (real_opp W0) Le0))
                       (real_plus (real_plus W0 (real_opp W0)) Le0)
                       (RealSetoid.real_eq_plus_compat W0 (real_plus Le0 (real_opp W0)) W0
                          (real_plus (real_opp W0) Le0)
                          (real_eq_refl W0)
                          (real_plus_comm Le0 (real_opp W0)))
                       (real_plus_assoc W0 (real_opp W0) Le0))
                    (real_eq_trans
                       (real_plus (real_plus W0 (real_opp W0)) Le0)
                       (real_plus real_zero Le0)
                       Le0
                       (RealSetoid.real_eq_plus_compat (real_plus W0 (real_opp W0)) Le0
                          real_zero Le0
                          (real_plus_opp W0)
                          (real_eq_refl Le0))
                       (sf_real_plus_zero_l Le0)))). }
  
  assert (Hlt : real_lt (real_log (real_mult a (real_pow kappa N))
                                  (real_mult_positive a (real_pow kappa N) Ha (bud_real_pow_pos kappa N Hk1)))
                        (real_log eps Heps)).
  { apply (Hshift _ (real_log a Ha) (real_log eps Heps)
             (real_mult (real_const (Z.of_nat N # 1)) (real_opp (real_log kappa Hk1)))).
    - apply (real_eq_trans _ (real_plus (real_log a Ha)
                   (real_mult (real_const (Z.of_nat N # 1)) (real_log kappa Hk1)))).
      + exact Hlogpow.
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _) Hnegm).
    - exact Hmid. }
  
  apply (real_eq_lt_lt (real_mult a (real_pow kappa N))
           (cauchy_real_exp (real_log (real_mult a (real_pow kappa N))
              (real_mult_positive a (real_pow kappa N) Ha (bud_real_pow_pos kappa N Hk1))))
           eps).
  - apply (real_eq_sym _ _ (cw_log_exp_right (real_mult a (real_pow kappa N))
              (real_mult_positive a (real_pow kappa N) Ha (bud_real_pow_pos kappa N Hk1)))).
  - apply (real_lt_eq_lt _ (cauchy_real_exp (real_log eps Heps))).
    + exact (cauchy_real_exp_mono _ _ Hlt).
    + exact (cw_log_exp_right eps Heps).
Qed.

(* ============ 7. piece 3: the tail-bound shape of paper 4's Theorem 4.10 (pure order algebra) ============ *)

(* Power addition: κ^(p+j) == κ^p · κ^j *)
Lemma real_pow_add_thm : forall (k : Real) (p j : nat),
  real_eq (real_pow k (p + j)%nat) (real_mult (real_pow k p) (real_pow k j)).
Proof.
  intros k p j. induction p as [| p IH].
  - change (real_pow k (0 + j)%nat) with (real_pow k j).
    change (real_pow k 0) with real_one.
    apply (real_eq_sym _ _ (real_mult_one_l (real_pow k j))).
  - replace (Datatypes.S p + j)%nat with (Datatypes.S (p + j))%nat by lia.
    change (real_pow k (Datatypes.S (p + j))) with
           (real_mult k (real_pow k (p + j))).
    apply (real_eq_trans _ (real_mult k (real_mult (real_pow k p) (real_pow k j)))).
    + apply (RealSetoid.real_eq_mult_compat k (real_pow k (p + j)%nat) k
               (real_mult (real_pow k p) (real_pow k j))).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_eq_trans _ (real_mult (real_mult k (real_pow k p)) (real_pow k j))).
      * exact (real_mult_assoc k (real_pow k p) (real_pow k j)).
      * apply real_eq_refl.
Qed.

(* κ ≤ 1 ⟹ κ^j ≤ 1 *)
Lemma real_pow_le_one : forall (k : Real) (Hk1 : real_lt real_zero k)
                          (Hk2 : real_le k real_one) (j : nat),
  real_le (real_pow k j) real_one.
Proof.
  intros k Hk1 Hk2 j. induction j as [| j IH].
  - apply real_le_refl.
  - cbn [real_pow].
    apply (real_le_trans _ (real_mult k real_one)).
    + apply (real_le_trans _ (real_mult (real_pow k j) k)).
      * apply real_eq_le_bridge. exact (real_mult_comm k (real_pow k j)).
      * apply (real_le_trans _ (real_mult real_one k)).
        -- exact (real_le_mult_compat (real_pow k j) real_one k Hk1 IH).
        -- apply real_eq_le_bridge.
           apply (real_eq_trans _ k).
           ++ exact (real_mult_one_l k).
           ++ apply (real_eq_sym _ _ (real_mult_one k)).
      + apply (real_le_trans _ k).
        * apply real_eq_le_bridge. exact (real_mult_one k).
        * exact Hk2.
Qed.

(* Power antitonicity: 0 < κ ≤ 1 and p ≤ q imply κ^q ≤ κ^p *)
Lemma real_pow_anti_mono : forall (k : Real) (Hk1 : real_lt real_zero k)
                              (Hk2 : real_le k real_one) (p q : nat),
  NatLe p q -> real_le (real_pow k q) (real_pow k p).
Proof.
  intros k Hk1 Hk2 p q Hle.
  pose proof (NatLe_drop p q Hle) as HleP.
  assert (Hcore : forall j : nat,
            real_le (real_pow k (p + j)%nat) (real_pow k p)).
  { intros j.
    assert (Heq : real_eq (real_pow k (p + j)%nat)
                          (real_mult (real_pow k p) (real_pow k j)))
      by exact (real_pow_add_thm k p j).
    apply (real_le_trans _ (real_mult (real_pow k p) (real_pow k j))).
    - apply real_eq_le_bridge. exact Heq.
    - apply (real_le_trans _ (real_mult (real_pow k j) (real_pow k p))).
      + apply real_eq_le_bridge. exact (real_mult_comm (real_pow k p) (real_pow k j)).
      + apply (real_le_trans _ (real_mult real_one (real_pow k p))).
        * exact (real_le_mult_compat (real_pow k j) real_one (real_pow k p)
                   (bud_real_pow_pos k p Hk1) (real_pow_le_one k Hk1 Hk2 j)).
        * apply real_eq_le_bridge. exact (real_mult_one_l (real_pow k p)). }
  assert (Hq : q = (p + (q - p))%nat) by lia.
  rewrite Hq. apply Hcore.
Qed.

(* Budget descent: N ≤ min m n and a·κ^N < eps imply a·κ^{min m n} < eps
   (the budget discharge of paper 4's Theorem 4.10 tail bound
   a·κ^{min m n}, pure order algebra) *)
Theorem geo_tail_budget :
  forall (kappa a eps : Real)
         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps) (m n N : nat),
  NatLe N (Nat.min m n) ->
  real_lt (real_mult a (real_pow kappa N)) eps ->
  real_lt (real_mult a (real_pow kappa (Nat.min m n))) eps.
Proof.
  intros kappa a eps Hk1 Hk2 Ha Heps m n N Hmin Hbudget.
  assert (Hk2le : real_le kappa real_one)
    by exact (real_lt_le_bridge kappa real_one Hk2).
  apply (real_le_lt_trans _ (real_mult a (real_pow kappa N))).
  - apply (real_le_trans _ (real_mult (real_pow kappa (Nat.min m n)) a)).
    + apply real_eq_le_bridge.
      exact (real_mult_comm a (real_pow kappa (Nat.min m n))).
    + apply (real_le_trans _ (real_mult (real_pow kappa N) a)).
      * exact (real_le_mult_compat (real_pow kappa (Nat.min m n))
                  (real_pow kappa N) a Ha
                  (real_pow_anti_mono kappa Hk1 Hk2le N (Nat.min m n) Hmin)).
      * apply real_eq_le_bridge.
        exact (real_mult_comm (real_pow kappa N) a).
  - exact Hbudget.
Qed.

(* The combined form: given the explicit budget N, the min tail bound
   discharges accordingly (the Real-layer assembly of Theorem 4.10) *)
Theorem budget_min_tail :
  forall (kappa a eps : Real)
         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps),
  sigT (fun N : nat => forall (p q : nat),
    NatLe N (Nat.min p q) ->
    real_lt (real_mult a (real_pow kappa (Nat.min p q))) eps).
Proof.
  intros kappa a eps Hk1 Hk2 Ha Heps.
  destruct (r_arch_pow_real kappa Hk1 Hk2 a Ha eps Heps) as [N HN].
  exists N.
  intros p q Hpq.
  exact (geo_tail_budget kappa a eps Hk1 Hk2 Ha Heps p q N Hpq HN).
Qed.

(* ============ 8. extraction check (executable OCaml, the G3 gate) ============ *)
From Stdlib Require Import Extraction.
Set Warnings "-extraction-opaque-accessed".
Set Extraction Output Directory ".".
Extraction "upbudgetreal.ml" r_arch_pow_real budget_cond_sufficient geo_tail_budget budget_min_tail.
