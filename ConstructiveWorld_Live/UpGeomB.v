(* ConstructiveWorld-Set -- unconditional Bishop-form policy-iteration geometric contraction (Theorem 4.8 counterpart). *)
(*
   Mission.  Under the Or-coded Set-valued order (real_le/real_lt) the
   exact "log Z <= 0" single-step form is not provable (its eq branch
   needs excluded middle), so this file proves the Bishop form: a
   per-eps strict surplus replaces the exact inequality, a strict lt
   witness replaces the eq branch, and the Or-form premise real_le is
   consumed constructively (both branches carry a witness route;
   cf. UpRealLeB.real_le_to_le_b).  Main results:
     geod_b_policy_iter_step  KL(pi*||pi_{t+1}) <=_B (1-eta)*KL(pi*||pi_t)
       (one step; margin lemma over kl(r,q) == (1-eta)*kl(r,p) + r*log Z);
     geod_b_policy_iter_iter  KL(pi*||pi_t) <=_B (1-eta)^t*KL(pi*||pi_0)
       (main theorem; le_b induction; eps by half h+(1-eta)h < 2h == eps).

   Dependencies.  S01_BaseRing .. S15_TailFEPUp, UpRealLeB
   (real_step_kl_eta_bound_B, real_le_to_le_b, real_le_closure_b_one),
   UpReqGeomD (geod_lsum, geod_kappa_pos, geod_eta_plus_kappa);
   Stdlib QArith.Qring, Lia, List.

   References.  Prefix geod_b_ clash-free in the tree; geod_b_pow
   mirrors klcx_r_pow/req_r_pow; strict twin of geod_kappa_le_one.

   Constructivity.  Set-layer statements (real_le_b/real_lt
   Set-valued; the nat-layer 0 < n premise is Prop, per
   real_list_sum_pos); all proofs close by Qed; Axioms: none; pure
   term-mode assembly (real_eq is not Id, no rewriting on the main
   chain); closing Print Assumptions sweep rechecks all statements.

   Build.  rocq c -native-compiler no -q -Q world "" UpGeomB.v
   (Rocq 9.1.0), same-world dependency .vo tree, cpu_guard wrapper. *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
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
Require Import UpRealLeB.
Require Import UpReqGeomD.

(* ============================================================ *)
(* P-A order/ring auxiliary lemmas *)
(* ============================================================ *)

(* le + lt splicing: x <= y < z implies x < z (each branch of the Or-coded premise takes its witness route) *)
Lemma geod_b_le_lt_trans : forall x y z : Real,
  real_le x y -> real_lt y z -> real_lt x z.
Proof.
  intros x y z Hle Hlt. unfold real_le in Hle.
  destruct Hle as [Hlt' | Heq].
  - exact (real_lt_trans x y z Hlt' Hlt).
  - exact (real_eq_lt_lt x y z Heq Hlt).
Qed.

(* eta > 0 implies 1-eta < 1 (strict; the strict twin of geod_kappa_le_one) *)
Lemma geod_b_kappa_lt_one : forall eta : Real,
  real_lt real_zero eta ->
  real_lt (real_plus real_one (real_opp eta)) real_one.
Proof.
  intros eta Hpos.
(* m == m+0 < m+eta == eta+m == 1 *)
  apply (real_eq_lt_lt (real_plus real_one (real_opp eta))
           (real_plus (real_plus real_one (real_opp eta)) real_zero) real_one).
  - exact (real_eq_sym _ _
             (real_plus_zero (real_plus real_one (real_opp eta)))).
  - apply (real_lt_eq_lt
             (real_plus (real_plus real_one (real_opp eta)) real_zero)
             (real_plus (real_plus real_one (real_opp eta)) eta) real_one).
    + exact (real_lt_plus_translate (real_plus real_one (real_opp eta))
                real_zero eta Hpos).
    + exact (real_eq_trans
               (real_plus (real_plus real_one (real_opp eta)) eta)
               (real_plus eta (real_plus real_one (real_opp eta))) real_one
               (real_plus_comm (real_plus real_one (real_opp eta)) eta)
               (geod_eta_plus_kappa eta)).
Qed.

(* Ring auxiliary: the mirrored dual of kl_ring_neg4 (m := 1-eta inlined):
   -((m*lp + eta*lr) + (-LZ + -lr)) == m*(lr - lp) + LZ *)
Lemma geod_b_ring_neg4_b : forall eta lp lr LZ : Real,
  real_eq (real_opp (real_plus
                       (real_plus (real_mult (real_plus real_one (real_opp eta)) lp)
                                  (real_mult eta lr))
                       (real_plus (real_opp LZ) (real_opp lr))))
          (real_plus (real_mult (real_plus real_one (real_opp eta))
                                (real_plus lr (real_opp lp))) LZ).
Proof.
  intros eta lp lr LZ. destruct eta as [e He]. destruct lp as [u Hu].
  destruct lr as [v Hv]. destruct LZ as [w Hw]. apply real_eq_of_zero_diff.
  intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* Ring auxiliary: reassociation (mirrored dual; kk arbitrary real --
   the endpoint is -lr, not -lp):
   kk*lp + (eta*lr + (-LZ + -lr)) == (kk*lp + eta*lr) + (-LZ + -lr) *)
Lemma geod_b_ring_log4_b : forall kk eta lp lr LZ : Real,
  real_eq (real_plus (real_mult kk lp)
                     (real_plus (real_mult eta lr)
                                (real_plus (real_opp LZ) (real_opp lr))))
          (real_plus (real_plus (real_mult kk lp) (real_mult eta lr))
                     (real_plus (real_opp LZ) (real_opp lr))).
Proof.
  intros kk eta lp lr LZ. destruct kk as [a Ha]. destruct eta as [e He].
  destruct lp as [u Hu]. destruct lr as [v Hv]. destruct LZ as [w Hw].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* Ring auxiliary: product reshuffle i*(e*X) == X*(i*e) (no named lemma needed, pointwise ring) *)
Lemma geod_b_ring_mlcr : forall i e X : Real,
  real_eq (real_mult i (real_mult e X)) (real_mult X (real_mult i e)).
Proof.
  intros i e X. destruct i as [fi Hi]. destruct e as [fe He].
  destruct X as [fx Hx]. apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* Ring auxiliary: one-step scaling reshape m*(X*KL + h) == (m*X)*KL + m*h *)
Lemma geod_b_scale_reshape : forall m X KL0 h : Real,
  real_eq (real_mult m (real_plus (real_mult X KL0) h))
          (real_plus (real_mult (real_mult m X) KL0) (real_mult m h)).
Proof.
  intros m X KL0 h. destruct m as [fm Hm]. destruct X as [fx Hx].
  destruct KL0 as [fk Hk]. destruct h as [fh Hh].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* Half-quantity engine: (1+1)*i == 1 implies e*i + e*i == e (the ring core of
   the per-eps half split; real_inv_pos is a Cauchy reciprocal, not a pointwise
   identity, so this goes through a real-eq algebra chain, not pointwise) *)
Lemma geod_b_half_double : forall e i : Real,
  real_eq (real_mult (real_plus real_one real_one) i) real_one ->
  real_eq (real_plus (real_mult e i) (real_mult e i)) e.
Proof.
  intros e i H.
  apply (real_eq_trans
           (real_plus (real_mult e i) (real_mult e i))
           (real_mult i (real_plus e e)) e).
  - apply (real_eq_trans
             (real_plus (real_mult e i) (real_mult e i))
             (real_plus (real_mult i e) (real_mult i e))
             (real_mult i (real_plus e e))).
    + exact (RealSetoid.real_eq_plus_compat (real_mult e i) (real_mult e i)
               (real_mult i e) (real_mult i e)
               (real_mult_comm e i) (real_mult_comm e i)).
    + exact (real_eq_sym _ _ (real_distrib i e e)).
  - apply (real_eq_trans
             (real_mult i (real_plus e e))
             (real_mult i (real_mult e (real_plus real_one real_one))) e).
    + exact (RealSetoid.real_eq_mult_compat i (real_plus e e) i
               (real_mult e (real_plus real_one real_one))
               (real_eq_refl i)
               (real_eq_trans (real_plus e e)
                  (real_plus (real_mult e real_one) (real_mult e real_one))
                  (real_mult e (real_plus real_one real_one))
                  (RealSetoid.real_eq_plus_compat e e
                     (real_mult e real_one) (real_mult e real_one)
                     (real_eq_sym _ _ (real_mult_one e))
                     (real_eq_sym _ _ (real_mult_one e)))
                  (real_eq_sym _ _ (real_distrib e real_one real_one)))).
    + apply (real_eq_trans
               (real_mult i (real_mult e (real_plus real_one real_one)))
               (real_mult (real_plus real_one real_one) (real_mult i e)) e).
      * exact (geod_b_ring_mlcr i e (real_plus real_one real_one)).
      * apply (real_eq_trans
                 (real_mult (real_plus real_one real_one) (real_mult i e))
                 (real_mult (real_mult (real_plus real_one real_one) i) e) e).
      -- exact (real_mult_assoc (real_plus real_one real_one) i e).
      -- apply (real_eq_trans
                   (real_mult (real_mult (real_plus real_one real_one) i) e)
                   (real_mult real_one e) e).
         ++ exact (RealSetoid.real_eq_mult_compat
                     (real_mult (real_plus real_one real_one) i)
                     e real_one e H (real_eq_refl e)).
         ++ exact (real_eq_trans (real_mult real_one e)
                     (real_mult e real_one) e
                     (real_mult_comm real_one e) (real_mult_one e)).
Qed.

(* ============================================================ *)
(* P-B main theorem family: geod_b_eta_pow -- powers (1-eta)^t in the Bishop order *)
(* ============================================================ *)

(* Power carrier: x^t := x*x^{t-1} (Fixpoint structurally identical to klcx_r_pow/req_r_pow) *)
Fixpoint geod_b_pow (x : Real) (t : nat) : Real :=
  match t with
  | Datatypes.O => real_one
  | Datatypes.S k => real_mult x (geod_b_pow x k)
  end.

(* Positivity preservation: 0 < x implies 0 < x^t *)
Lemma geod_b_pow_pos : forall (x : Real) (t : nat),
  real_lt real_zero x -> real_lt real_zero (geod_b_pow x t).
Proof.
  intros x t Hx. induction t as [| k IH].
  - exact real_lt_zero_one.
  - exact (real_mult_positive x (geod_b_pow x k) Hx IH).
Qed.

(* Monotone decrease (Bishop-order form): 0 < x <= 1 implies x^{t+1} <=_B x^t.
   Route: x*x^t <= 1*x^t (right multiplication by a positive factor preserves
   order, Or form -- the premise slot is an Or premise, consumed constructively)
   + the reshape 1*x^t == x^t, closed by the one-way bridge real_le_to_le_b. *)
Lemma geod_b_pow_mono_decr : forall (x : Real) (t : nat),
  real_lt real_zero x -> real_le x real_one ->
  real_le_b (geod_b_pow x (Datatypes.S t)) (geod_b_pow x t).
Proof.
  intros x t Hx Hx1. apply real_le_to_le_b.
  apply (real_le_trans (real_mult x (geod_b_pow x t))
           (real_mult real_one (geod_b_pow x t)) (geod_b_pow x t)).
  - exact (real_le_mult_compat x real_one (geod_b_pow x t)
             (geod_b_pow_pos x t Hx) Hx1).
  - apply (RealSetoid.real_eq_le _ _).
    exact (real_eq_trans (real_mult real_one (geod_b_pow x t))
             (real_mult (geod_b_pow x t) real_one) (geod_b_pow x t)
             (real_mult_comm real_one (geod_b_pow x t))
             (real_mult_one (geod_b_pow x t))).
Qed.

(* ============================================================ *)
(* P-C semantic pieces: KL sum carrier + next-policy certificates + iterate orbit *)
(* ============================================================ *)

(* KL sum carrier: Sum_i kl(a_i||b_i) (explicit certificate arguments -- carried directly by the dependently typed real_kl_term) *)
Definition geod_b_kl_sum (n : nat) (a b : nat -> Real)
  (Ha : forall i : nat, real_lt real_zero (a i))
  (Hb : forall i : nat, real_lt real_zero (b i)) : Real :=
  real_list_sum nat
    (fun i : nat => real_kl_term (a i) (b i) (Ha i) (Hb i))
    (List.seq 0 n).

(* Interpolation partition Z := Sum p^{1-eta}*r^eta > 0 (n nonempty + pointwise
   positivity; exp is positive everywhere, no eta premise -- supplied free by
   cauchy_real_exp_pos) *)
Lemma geod_b_interp_Z_pos : forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hn : (0 < n)%nat)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i)),
  real_lt real_zero (real_interp_Z n p r eta Hp Hr).
Proof.
  intros n p r eta Hn Hp Hr. unfold real_interp_Z.
  apply (real_list_sum_pos nat
           (fun i : nat => real_mult
              (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
              (real_pow_pos (r i) eta (Hr i)))
           (List.seq 0 n)).
  - intro i.
    exact (real_mult_positive
             (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
             (real_pow_pos (r i) eta (Hr i))
             (cauchy_real_exp_pos
                (real_mult (real_plus real_one (real_opp eta))
                           (cw_log (p i) (Hp i))))
             (cauchy_real_exp_pos (real_mult eta (cw_log (r i) (Hr i))))).
  - intro Heq. destruct n as [| k].
    + lia.
    + discriminate Heq.
Qed.

(* Next policy pointwise positive: q_i = p_i^{1-eta}*r_i^eta/Z > 0 *)
Lemma geod_b_step_next_pos : forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr)) (i : nat),
  real_lt real_zero (real_step_next n p r eta Hp Hr HZ i).
Proof.
  intros n p r eta Hp Hr HZ i. unfold real_step_next.
  exact (real_mult_positive
           (real_mult
              (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
              (real_pow_pos (r i) eta (Hr i)))
           (real_inv_pos (real_interp_Z n p r eta Hp Hr) HZ)
           (real_mult_positive
              (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
              (real_pow_pos (r i) eta (Hr i))
              (cauchy_real_exp_pos
                 (real_mult (real_plus real_one (real_opp eta))
                            (cw_log (p i) (Hp i))))
              (cauchy_real_exp_pos (real_mult eta (cw_log (r i) (Hr i)))))
           (real_inv_pos_pos (real_interp_Z n p r eta Hp Hr) HZ)).
Qed.

(* Next policy preserves normalization: Sum q == (Sum p^{1-eta}r^eta)/Z == Z/Z == 1
   (linearity law + inverse absorption; no premises -- Z is by definition that sum) *)
Lemma geod_b_step_next_norm : forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr)),
  real_eq (geod_lsum n (real_step_next n p r eta Hp Hr HZ)) real_one.
Proof.
  intros n p r eta Hp Hr HZ.
  unfold geod_lsum, real_step_next.
  set (Z := real_interp_Z n p r eta Hp Hr).
  apply (real_eq_trans
           (real_list_sum nat
              (fun i : nat => real_mult
                 (real_mult
                    (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
                    (real_pow_pos (r i) eta (Hr i)))
                 (real_inv_pos Z HZ))
              (List.seq 0 n))
           (real_mult (real_inv_pos Z HZ)
                      (real_list_sum nat
                         (fun i : nat => real_mult
                            (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
                            (real_pow_pos (r i) eta (Hr i)))
                         (List.seq 0 n)))
           real_one).
  - exact (real_list_sum_linear_r nat (real_inv_pos Z HZ)
             (fun i : nat => real_mult
                (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
                (real_pow_pos (r i) eta (Hr i)))
             (List.seq 0 n)).
  - exact (real_eq_trans (real_mult (real_inv_pos Z HZ) Z)
             (real_mult Z (real_inv_pos Z HZ)) real_one
             (real_mult_comm (real_inv_pos Z HZ) Z)
             (real_inv_pos_correct Z HZ)).
Qed.

(* Iterate orbit: pi_{t+1} := real_step_next(pi_t, r) (sigT packaging of pointwise
   positivity + normalization; isomorphic to policy_iterate, positivity and
   normalization carried internally, self-supplied -- no new premises) *)
Fixpoint geod_b_iterate (n : nat) (Hn : (0 < n)%nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) (eta : Real) (t : nat)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormp : real_eq (geod_lsum n p) real_one)
    {struct t}
  : { q : nat -> Real &
      prod (forall i : nat, real_lt real_zero (q i))
           (real_eq (geod_lsum n q) real_one) } :=
  match t with
  | Datatypes.O => existT _ p (Hp, Hnormp)
  | Datatypes.S k =>
      let q := projT1 (geod_b_iterate n Hn r Hr eta k p Hp Hnormp) in
      let Hqp := fst (projT2 (geod_b_iterate n Hn r Hr eta k p Hp Hnormp)) in
      let Hqn := snd (projT2 (geod_b_iterate n Hn r Hr eta k p Hp Hnormp)) in
      let HZq := geod_b_interp_Z_pos n q r eta Hn Hqp Hr in
      existT _ (real_step_next n q r eta Hqp Hr HZq)
               (geod_b_step_next_pos n q r eta Hqp Hr HZq,
                geod_b_step_next_norm n q r eta Hqp Hr HZq)
  end.

(* ============================================================ *)
(* P-D floor piece: one-step KL contraction, Bishop form (Requires the UpRealLeB engine) *)
(* ============================================================ *)

(* KL(pi_t||pi_{t+1}) <=_B eta*KL(pi_t||pi_star):
   fed in one stroke by real_step_kl_eta_bound_B (UpRealLeB D.5, verified on disk). *)
Theorem geod_b_step_kl_eps :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n p r eta Hp Hr HZ i))
    (Heta : real_lt real_zero eta) (Hetale : real_le eta real_one),
  real_le_b (geod_b_kl_sum n p (real_step_next n p r eta Hp Hr HZ) Hp Hqv)
            (real_mult eta (geod_b_kl_sum n p r Hp Hr)).
Proof.
  intros n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta Hetale.
  exact (real_step_kl_eta_bound_B n p r eta Hp Hr Hnormp Hnormr HZ Hqv
           Heta Hetale).
Qed.

(* ============================================================ *)
(* P-E main piece 1: the one-step genuine geometric contraction, Bishop form
   (the le_b form of the three-KL identity).  Auxiliary lemma: the per-eps
   strict surplus KL(r||q) < (1-eta)*KL(r||p) + eps -- pointwise identity
   kl(r_i,q_i) == (1-eta)*kl(r_i,p_i) + r_i*log Z (M2 dual). *)

(* ============================================================ *)

Theorem geod_b_policy_iter_step_margin :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n p r eta Hp Hr HZ i))
    (Heta : real_lt real_zero eta) (Hetale : real_le eta real_one),
  forall eps : Real, real_lt real_zero eps ->
  real_lt (geod_b_kl_sum n r (real_step_next n p r eta Hp Hr HZ) Hr Hqv)
          (real_plus (real_mult (real_plus real_one (real_opp eta))
                        (geod_b_kl_sum n r p Hr Hp))
                     eps).
Proof.
  intros n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta Hetale eps Heps.
  unfold geod_b_kl_sum.
  set (m := real_plus real_one (real_opp eta)).
  set (Z := real_interp_Z n p r eta Hp Hr).
  set (q := real_step_next n p r eta Hp Hr HZ).
  set (LZ := cw_log Z HZ).
  set (Rsum := real_list_sum nat
                 (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                 (List.seq 0 n)).
(* ---- Pointwise KL identity (exact eq): kl(r_i,q_i) == m*kl(r_i,p_i) + r_i*LZ ---- *)
  assert (Hpi : forall i : nat,
    real_eq (real_kl_term (r i) (q i) (Hr i) (Hqv i))
            (real_plus (real_mult m (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                       (real_mult (r i) LZ))).
  { intro i.
    set (irr := real_inv_pos (r i) (Hr i)).
    set (izz := real_inv_pos Z HZ).
    set (pA := real_pow_pos (p i) m (Hp i)).
    set (pB := real_pow_pos (r i) eta (Hr i)).
    set (lr := cw_log (r i) (Hr i)).
    set (lp := cw_log (p i) (Hp i)).
    assert (HIR : real_lt real_zero irr) by exact (real_inv_pos_pos (r i) (Hr i)).
    assert (HIZ : real_lt real_zero izz) by exact (real_inv_pos_pos Z HZ).
    assert (HpA : real_lt real_zero pA)
      by exact (cauchy_real_exp_pos (real_mult m (cw_log (p i) (Hp i)))).
    assert (HpB : real_lt real_zero pB)
      by exact (cauchy_real_exp_pos (real_mult eta (cw_log (r i) (Hr i)))).
    set (Hrqlog := real_mult_positive (q i) (real_inv_pos (r i) (Hr i)) (Hqv i)
                     (real_inv_pos_pos (r i) (Hr i))).
    set (Hprlog := real_mult_positive (p i) (real_inv_pos (r i) (Hr i)) (Hp i)
                     (real_inv_pos_pos (r i) (Hr i))).
    
    assert (HlA : real_eq (cw_log pA HpA) (real_mult m lp))
      by exact (log_inv_exp_neg_thm (real_mult m (cw_log (p i) (Hp i))) HpA).
    assert (HlB : real_eq (cw_log pB HpB) (real_mult eta lr))
      by exact (log_inv_exp_neg_thm (real_mult eta (cw_log (r i) (Hr i))) HpB).
    assert (HlZ : real_eq (cw_log izz HIZ) (real_opp LZ))
      by exact (kl_log_inv Z HZ HIZ).
    assert (HlR : real_eq (cw_log irr HIR) (real_opp lr))
      by exact (kl_log_inv (r i) (Hr i) HIR).
    
    assert (Hlogpr : real_eq (cw_log (real_mult (p i) irr) Hprlog)
                             (real_plus lp (real_opp lr))).
    { exact (real_eq_trans (cw_log (real_mult (p i) irr) Hprlog)
               (real_plus (cw_log (p i) (Hp i)) (cw_log irr HIR))
               (real_plus lp (real_opp lr))
               (log_inv_mult_thm (p i) irr (Hp i) HIR Hprlog)
               (RealSetoid.real_eq_plus_compat (cw_log (p i) (Hp i))
                  (cw_log irr HIR) (cw_log (p i) (Hp i)) (real_opp lr)
                  (real_eq_refl (cw_log (p i) (Hp i))) HlR)). }
(* q*inv r ring reshuffle (pure ring) *)
    assert (Hring1 : real_eq (real_mult (q i) irr)
                             (real_mult pA (real_mult pB (real_mult izz irr))))
      by exact (kl_ring_reassoc pA pB izz irr).
    assert (Hpos3 : real_lt real_zero (real_mult izz irr))
      by exact (real_mult_positive izz irr HIZ HIR).
    assert (Hpos2 : real_lt real_zero (real_mult pB (real_mult izz irr)))
      by exact (real_mult_positive pB (real_mult izz irr) HpB Hpos3).
    assert (HAB4 : real_lt real_zero (real_mult pA (real_mult pB (real_mult izz irr))))
      by exact (real_mult_positive pA (real_mult pB (real_mult izz irr)) HpA Hpos2).
    
    assert (Hlog4 : real_eq (cw_log (real_mult (q i) irr) Hrqlog)
                       (real_plus (cw_log pA HpA)
                          (real_plus (cw_log pB HpB)
                             (real_plus (cw_log izz HIZ) (cw_log irr HIR))))).
    { apply (real_eq_trans (cw_log (real_mult (q i) irr) Hrqlog)
               (cw_log (real_mult pA (real_mult pB (real_mult izz irr))) HAB4)
               (real_plus (cw_log pA HpA)
                  (real_plus (cw_log pB HpB)
                     (real_plus (cw_log izz HIZ) (cw_log irr HIR))))).
      - exact (real_log_wd (real_mult (q i) irr)
                 (real_mult pA (real_mult pB (real_mult izz irr))) Hrqlog HAB4 Hring1).
      - exact (real_eq_trans
                  (cw_log (real_mult pA (real_mult pB (real_mult izz irr))) HAB4)
                  (real_plus (cw_log pA HpA)
                     (cw_log (real_mult pB (real_mult izz irr)) Hpos2))
                  (real_plus (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz HIZ) (cw_log irr HIR))))
                  (log_inv_mult_thm pA (real_mult pB (real_mult izz irr)) HpA Hpos2 HAB4)
                  (RealSetoid.real_eq_plus_compat (cw_log pA HpA)
                     (cw_log (real_mult pB (real_mult izz irr)) Hpos2)
                     (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz HIZ) (cw_log irr HIR)))
                     (real_eq_refl (cw_log pA HpA))
                     (real_eq_trans
                        (cw_log (real_mult pB (real_mult izz irr)) Hpos2)
                        (real_plus (cw_log pB HpB) (cw_log (real_mult izz irr) Hpos3))
                        (real_plus (cw_log pB HpB)
                           (real_plus (cw_log izz HIZ) (cw_log irr HIR)))
                        (log_inv_mult_thm pB (real_mult izz irr) HpB Hpos3 Hpos2)
                        (RealSetoid.real_eq_plus_compat (cw_log pB HpB)
                           (cw_log (real_mult izz irr) Hpos3)
                           (cw_log pB HpB)
                           (real_plus (cw_log izz HIZ) (cw_log irr HIR))
                           (real_eq_refl (cw_log pB HpB))
                           (log_inv_mult_thm izz irr HIZ HIR Hpos3))))). }
    
    assert (Hlog4' : real_eq (cw_log (real_mult (q i) irr) Hrqlog)
                       (real_plus (real_plus (real_mult m lp) (real_mult eta lr))
                                  (real_plus (real_opp LZ) (real_opp lr)))).
    { apply (real_eq_trans (cw_log (real_mult (q i) irr) Hrqlog)
               (real_plus (cw_log pA HpA)
                  (real_plus (cw_log pB HpB)
                     (real_plus (cw_log izz HIZ) (cw_log irr HIR))))
               (real_plus (real_plus (real_mult m lp) (real_mult eta lr))
                          (real_plus (real_opp LZ) (real_opp lr)))).
      - exact Hlog4.
      - exact (real_eq_trans
                  (real_plus (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz HIZ) (cw_log irr HIR))))
                  (real_plus (real_mult m lp)
                     (real_plus (real_mult eta lr)
                        (real_plus (real_opp LZ) (real_opp lr))))
                  (real_plus (real_plus (real_mult m lp) (real_mult eta lr))
                             (real_plus (real_opp LZ) (real_opp lr)))
                  (RealSetoid.real_eq_plus_compat (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz HIZ) (cw_log irr HIR)))
                     (real_mult m lp)
                     (real_plus (real_mult eta lr)
                        (real_plus (real_opp LZ) (real_opp lr)))
                     HlA
                     (RealSetoid.real_eq_plus_compat (cw_log pB HpB)
                        (real_plus (cw_log izz HIZ) (cw_log irr HIR))
                        (real_mult eta lr)
                        (real_plus (real_opp LZ) (real_opp lr))
                        HlB
                        (RealSetoid.real_eq_plus_compat (cw_log izz HIZ)
                           (cw_log irr HIR) (real_opp LZ) (real_opp lr)
                           HlZ HlR)))
                  (geod_b_ring_log4_b m eta lp lr LZ)). }
    
    assert (Hneg : real_eq (real_opp (cw_log (real_mult (q i) irr) Hrqlog))
                       (real_plus (real_mult m (real_plus lr (real_opp lp))) LZ)).
    { exact (real_eq_trans
               (real_opp (cw_log (real_mult (q i) irr) Hrqlog))
               (real_opp (real_plus (real_plus (real_mult m lp) (real_mult eta lr))
                                    (real_plus (real_opp LZ) (real_opp lr))))
               (real_plus (real_mult m (real_plus lr (real_opp lp))) LZ)
               (RealSetoid.real_eq_opp_compat
                  (cw_log (real_mult (q i) irr) Hrqlog)
                  (real_plus (real_plus (real_mult m lp) (real_mult eta lr))
                             (real_plus (real_opp LZ) (real_opp lr)))
                  Hlog4')
               (geod_b_ring_neg4_b eta lp lr LZ)). }
    
    assert (HnegP : real_eq (real_plus lr (real_opp lp))
                            (real_opp (cw_log (real_mult (p i) irr) Hprlog))).
    { exact (real_eq_trans (real_plus lr (real_opp lp))
               (real_opp (real_plus lp (real_opp lr)))
               (real_opp (cw_log (real_mult (p i) irr) Hprlog))
               (real_eq_sym
                  (real_opp (real_plus lp (real_opp lr)))
                  (real_plus lr (real_opp lp))
                  (kl_ring_opp_swap lp lr))
               (real_eq_sym
                  (real_opp (cw_log (real_mult (p i) irr) Hprlog))
                  (real_opp (real_plus lp (real_opp lr)))
                  (RealSetoid.real_eq_opp_compat
                     (cw_log (real_mult (p i) irr) Hprlog)
                     (real_plus lp (real_opp lr)) Hlogpr))). }
(* Final assembly: kl(r,q) == m*kl(r,p) + r*LZ *)
    exact (real_eq_trans
              (real_mult (r i) (real_opp (cw_log (real_mult (q i) irr) Hrqlog)))
              (real_plus
                 (real_mult m (real_mult (r i) (real_plus lr (real_opp lp))))
                 (real_mult (r i) LZ))
              (real_plus (real_mult m (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                         (real_mult (r i) LZ))
              (real_eq_trans
                 (real_mult (r i) (real_opp (cw_log (real_mult (q i) irr) Hrqlog)))
                 (real_mult (r i)
                    (real_plus (real_mult m (real_plus lr (real_opp lp))) LZ))
                 (real_plus
                    (real_mult m (real_mult (r i) (real_plus lr (real_opp lp))))
                    (real_mult (r i) LZ))
                 (RealSetoid.real_eq_mult_compat (r i)
                    (real_opp (cw_log (real_mult (q i) irr) Hrqlog)) (r i)
                    (real_plus (real_mult m (real_plus lr (real_opp lp))) LZ)
                    (real_eq_refl (r i)) Hneg)
                 (kl_ring_kl_split m (r i) (real_plus lr (real_opp lp)) LZ))
              (RealSetoid.real_eq_plus_compat
                 (real_mult m (real_mult (r i) (real_plus lr (real_opp lp))))
                 (real_mult (r i) LZ)
                 (real_mult m (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                 (real_mult (r i) LZ)
                 (RealSetoid.real_eq_mult_compat m
                    (real_mult (r i) (real_plus lr (real_opp lp)))
                    m (real_kl_term (r i) (p i) (Hr i) (Hp i))
                    (real_eq_refl m)
                    (real_eq_trans
                       (real_mult (r i) (real_plus lr (real_opp lp)))
                       (real_mult (r i)
                          (real_opp (cw_log (real_mult (p i) irr) Hprlog)))
                       (real_kl_term (r i) (p i) (Hr i) (Hp i))
                       (RealSetoid.real_eq_mult_compat (r i)
                          (real_plus lr (real_opp lp)) (r i)
                          (real_opp (cw_log (real_mult (p i) irr) Hprlog))
                          (real_eq_refl (r i)) HnegP)
                       (real_eq_refl (real_kl_term (r i) (p i) (Hr i) (Hp i)))))
                 (real_eq_refl (real_mult (r i) LZ)))). }
(* ---- Summation layer: Sum kl(r,q) == m*Sum kl(r,p) + LZ (normalization absorbs Sum r == 1) ---- *)
  assert (Hsum : real_eq
      (real_list_sum nat
         (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hqv i)) (List.seq 0 n))
      (real_plus (real_mult m Rsum) LZ)).
  { apply (real_eq_trans
             (real_list_sum nat
                (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hqv i))
                (List.seq 0 n))
             (real_list_sum nat
                (fun i : nat => real_plus
                                   (real_mult m
                                      (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                                   (real_mult (r i) LZ))
                (List.seq 0 n))
             (real_plus (real_mult m Rsum) LZ)).
    - exact (real_list_sum_ext nat _ _ (List.seq 0 n) Hpi).
    - apply (real_eq_trans
                (real_list_sum nat
                   (fun i : nat => real_plus
                                      (real_mult m
                                         (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                                      (real_mult (r i) LZ))
                   (List.seq 0 n))
                (real_plus
                   (real_list_sum nat
                      (fun i : nat => real_mult m
                                       (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                      (List.seq 0 n))
                   (real_list_sum nat (fun i : nat => real_mult (r i) LZ)
                      (List.seq 0 n)))
                (real_plus (real_mult m Rsum) LZ)).
      + exact (real_list_sum_add nat _ _ (List.seq 0 n)).
      + exact (real_eq_trans
                  (real_plus
                     (real_list_sum nat
                        (fun i : nat => real_mult m
                                         (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                        (List.seq 0 n))
                     (real_list_sum nat (fun i : nat => real_mult (r i) LZ)
                        (List.seq 0 n)))
                  (real_plus (real_mult m Rsum)
                     (real_mult LZ (real_list_sum nat r (List.seq 0 n))))
                  (real_plus (real_mult m Rsum) LZ)
                  (RealSetoid.real_eq_plus_compat
                     (real_list_sum nat
                        (fun i : nat => real_mult m
                                         (real_kl_term (r i) (p i) (Hr i) (Hp i)))
                        (List.seq 0 n))
                     (real_list_sum nat (fun i : nat => real_mult (r i) LZ)
                        (List.seq 0 n))
                     (real_mult m Rsum)
                     (real_mult LZ (real_list_sum nat r (List.seq 0 n)))
                     (real_list_sum_linear nat m
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n))
                     (real_list_sum_linear_r nat LZ r (List.seq 0 n)))
                  (RealSetoid.real_eq_plus_compat (real_mult m Rsum)
                     (real_mult LZ (real_list_sum nat r (List.seq 0 n)))
                     (real_mult m Rsum) LZ
                     (real_eq_refl (real_mult m Rsum))
                     (real_eq_trans (real_mult LZ (real_list_sum nat r (List.seq 0 n)))
                        (real_mult LZ real_one) LZ
                        (RealSetoid.real_eq_mult_compat LZ
                           (real_list_sum nat r (List.seq 0 n)) LZ real_one
                           (real_eq_refl LZ) Hnormr)
                        (real_mult_one LZ)))). }
  
  assert (HLZ : real_lt LZ eps).
  { assert (HZle : real_le Z (real_plus real_one eps))
      by exact (real_interp_Z_le_one_eps n p r eta Hp Hr Hnormp Hnormr
                  Heta Hetale eps Heps).
    assert (Honep : real_lt real_zero (real_plus real_one eps))
      by exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                  (real_plus real_one eps) kl_zero_plus_zero
                  (real_lt_plus_compat real_zero real_one real_zero eps
                     real_lt_zero_one Heps)).
    assert (Hlogle : real_le LZ (cw_log (real_plus real_one eps) Honep))
      by exact (kl_log_le_mono Z (real_plus real_one eps) HZ Honep HZle).
    assert (Hloglt : real_lt (cw_log (real_plus real_one eps) Honep) eps).
    { apply (real_lt_eq_lt (cw_log (real_plus real_one eps) Honep)
               (cw_log (cauchy_real_exp eps) (cauchy_real_exp_pos eps)) eps).
      - exact (real_log_lt_mono (real_plus real_one eps) (cauchy_real_exp eps)
                  Honep (cauchy_real_exp_pos eps) (real_exp_ge_linear eps Heps)).
      - exact (log_inv_exp_neg_thm eps (cauchy_real_exp_pos eps)). }
    exact (geod_b_le_lt_trans LZ (cw_log (real_plus real_one eps) Honep) eps
             Hlogle Hloglt). }
(* ---- Endgame: KL(r,q) == m*KL(r,p) + LZ < m*KL(r,p) + eps ---- *)
  exact (real_eq_lt_lt
           (real_list_sum nat
              (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hqv i))
              (List.seq 0 n))
           (real_plus (real_mult m Rsum) LZ)
           (real_plus (real_mult m Rsum) eps)
           Hsum
           (real_lt_eq_lt
              (real_plus (real_mult m Rsum) LZ)
              (real_plus eps (real_mult m Rsum))
              (real_plus (real_mult m Rsum) eps)
              (real_eq_lt_lt
                 (real_plus (real_mult m Rsum) LZ)
                 (real_plus LZ (real_mult m Rsum))
                 (real_plus eps (real_mult m Rsum))
                 (real_plus_comm (real_mult m Rsum) LZ)
                 (real_lt_plus_compat_lt_le LZ eps (real_mult m Rsum)
                    (real_mult m Rsum) HLZ
                    (real_le_refl (real_mult m Rsum))))
              (real_plus_comm eps (real_mult m Rsum)))).
Qed.

(* Main piece 1 (Bishop completion): KL(pi*||pi_{t+1}) <=_B (1-eta)*KL(pi*||pi_t).
   Certificate chain: geod_b_policy_iter_step_margin (strict surplus for any eps)
   + real_le_closure_b_one closes in one step (the certificate real_lt_zero_one
   already exists). *)
Theorem geod_b_policy_iter_step :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n p r eta Hp Hr HZ i))
    (Heta : real_lt real_zero eta) (Hetale : real_le eta real_one),
  real_le_b (geod_b_kl_sum n r (real_step_next n p r eta Hp Hr HZ) Hr Hqv)
            (real_mult (real_plus real_one (real_opp eta))
                       (geod_b_kl_sum n r p Hr Hp)).
Proof.
  intros n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta Hetale.
  apply real_le_closure_b_one. intros eps Heps.
  exact (inl (geod_b_policy_iter_step_margin n p r eta Hp Hr Hnormp Hnormr
                  HZ Hqv Heta Hetale eps Heps)).
Qed.

(* ============================================================ *)
(* P-F main piece 2 (main theorem): t-step geometric contraction, Bishop form
   KL(pi*||pi_t) <=_B (1-eta)^t * KL(pi*||pi_0) -- le_b induction; the eps
   accumulation is a per-eps half split (each step takes h := eps/2, with
   (1-eta)*h < h, summing to 2*h == eps; no 1/n splitting -- same as the
   UpReqSumD precedent). *)
(* ============================================================ *)

Theorem geod_b_policy_iter_iter :
  forall (n : nat) (Hn : (0 < n)%nat) (r p : nat -> Real) (eta : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one) (t : nat),
  real_le_b
    (geod_b_kl_sum n r
       (projT1 (geod_b_iterate n Hn r Hr eta t p Hp Hnormp))
       Hr
       (fst (projT2 (geod_b_iterate n Hn r Hr eta t p Hp Hnormp))))
    (real_mult (geod_b_pow (real_plus real_one (real_opp eta)) t)
               (geod_b_kl_sum n r p Hr Hp)).
Proof.
  intros n Hn r p eta Hr Hp Hnormr Hnormp Heta Hlt1 t.
  unfold real_le_b.
  set (m := real_plus real_one (real_opp eta)).
  set (KL0 := geod_b_kl_sum n r p Hr Hp).
  assert (Hmpos : real_lt real_zero m) by exact (geod_kappa_pos eta Hlt1).
  assert (Hmlt1 : real_lt m real_one) by exact (geod_b_kappa_lt_one eta Heta).
  assert (Hetale : real_le eta real_one) by exact (inl Hlt1).
  induction t as [| k IH].
  - (* t = 0: KL(pi*||pi_0) < 1*KL(pi*||pi_0) + eps (the reshape 1*KL0 == KL0) *)
    intros eps Heps.
    apply (real_lt_eq_lt KL0 (real_plus KL0 eps)
             (real_plus (real_mult (geod_b_pow m 0) KL0) eps)).
    + exact (real_lt_plus_r_zero KL0 eps Heps).
    + apply (RealSetoid.real_eq_plus_compat KL0 eps
               (real_mult (geod_b_pow m 0) KL0) eps).
      * exact (real_eq_sym _ _ (real_eq_trans (real_mult (geod_b_pow m 0) KL0)
                 (real_mult real_one KL0) KL0
                 (RealSetoid.real_eq_mult_compat (geod_b_pow m 0) KL0
                    real_one KL0
                    (real_eq_refl real_one) (real_eq_refl KL0))
                 (real_eq_trans (real_mult real_one KL0)
                    (real_mult KL0 real_one) KL0
                    (real_mult_comm real_one KL0) (real_mult_one KL0)))).
      * exact (real_eq_refl eps).
  - (* t = S k: strict one-step contraction + induction + scaling + half-quantity eps split *)
    intros eps Heps.
    set (Pk := projT1 (geod_b_iterate n Hn r Hr eta k p Hp Hnormp)) in *.
    set (Pkp := fst (projT2 (geod_b_iterate n Hn r Hr eta k p Hp Hnormp))) in *.
    set (Hkn := snd (projT2 (geod_b_iterate n Hn r Hr eta k p Hp Hnormp))) in *.
    set (HZk := geod_b_interp_Z_pos n Pk r eta Hn Pkp Hr).
    set (PSk := real_step_next n Pk r eta Pkp Hr HZk).
    set (HPSkpos := geod_b_step_next_pos n Pk r eta Pkp Hr HZk).
(* Half quantity h := eps/2 *)
    set (inv2 := real_inv_pos (real_plus real_one real_one)
                   (real_plus_positive real_one real_one
                      real_lt_zero_one real_lt_zero_one)).
    set (h := real_mult eps inv2).
    assert (Hh : real_lt real_zero h)
      by exact (real_mult_positive eps inv2 Heps
                  (real_inv_pos_pos (real_plus real_one real_one)
                     (real_plus_positive real_one real_one
                        real_lt_zero_one real_lt_zero_one))).
    assert (Hhh : real_eq (real_plus h h) eps)
      by exact (geod_b_half_double eps inv2
                  (real_inv_pos_correct (real_plus real_one real_one)
                     (real_plus_positive real_one real_one
                        real_lt_zero_one real_lt_zero_one))).
(* The induction premise specializes to h *)
    specialize (IH h Hh).
(* Strict one-step contraction (main piece 1 margin) *)
    assert (Hstep : real_lt (geod_b_kl_sum n r PSk Hr HPSkpos)
                            (real_plus (real_mult m (geod_b_kl_sum n r Pk Hr Pkp)) h))
      by exact (geod_b_policy_iter_step_margin n Pk r eta Pkp Hr Hkn Hnormr
                  HZk HPSkpos Heta Hetale h Hh).
(* Positive scaling of the induction premise: m*KL_k < m*(kappa^k*KL0 + h) ==
   kappa^{S k}*KL0 + m*h *)
    assert (Hscale : real_lt (real_mult m (geod_b_kl_sum n r Pk Hr Pkp))
                             (real_mult m (real_plus (real_mult (geod_b_pow m k) KL0) h)))
      by exact (real_mult_lt_compat_l (geod_b_kl_sum n r Pk Hr Pkp)
                  (real_plus (real_mult (geod_b_pow m k) KL0) h) m IH Hmpos).
    assert (Hresh : real_eq (real_mult m (real_plus (real_mult (geod_b_pow m k) KL0) h))
                            (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                       (real_mult m h)))
      by exact (geod_b_scale_reshape m (geod_b_pow m k) KL0 h).
    assert (HA : real_lt (real_mult m (geod_b_kl_sum n r Pk Hr Pkp))
                         (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                    (real_mult m h)))
      by exact (real_lt_eq_lt (real_mult m (geod_b_kl_sum n r Pk Hr Pkp))
                  (real_mult m (real_plus (real_mult (geod_b_pow m k) KL0) h))
                  (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                             (real_mult m h))
                  Hscale Hresh).
(* m*h < h (m < 1, strict) *)
    assert (Hmh : real_lt (real_mult m h) h)
      by exact (real_eq_lt_lt (real_mult m h) (real_mult h m) h
                  (real_mult_comm m h)
                  (real_lt_eq_lt (real_mult h m) (real_mult h real_one) h
                     (real_mult_lt_compat_l m real_one h Hmlt1 Hh)
                     (real_mult_one h))).
(* Closing: KL_{S k} <= m*KL_k + h < (kappa^{S k}KL0 + m*h) + h <
   kappa^{S k}KL0 + 2*h == kappa^{S k}KL0 + eps *)
    assert (Hmerge : real_lt (real_plus (real_mult m (geod_b_kl_sum n r Pk Hr Pkp)) h)
                             (real_plus
                                (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                           (real_mult m h))
                                h))
      by exact (real_lt_plus_compat_lt_le
                  (real_mult m (geod_b_kl_sum n r Pk Hr Pkp))
                  (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                             (real_mult m h))
                  h h HA (real_le_refl h)).
    assert (Hstep2 : real_lt (geod_b_kl_sum n r PSk Hr HPSkpos)
                             (real_plus
                                (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                           (real_mult m h))
                                h))
      by exact (geod_b_le_lt_trans (geod_b_kl_sum n r PSk Hr HPSkpos)
                  (real_plus (real_mult m (geod_b_kl_sum n r Pk Hr Pkp)) h)
                  (real_plus
                     (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                (real_mult m h))
                     h)
                  (inl Hstep) Hmerge).
    assert (Hassoc : real_lt (geod_b_kl_sum n r PSk Hr HPSkpos)
                             (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                        (real_plus (real_mult m h) h)))
      by exact (real_lt_eq_lt (geod_b_kl_sum n r PSk Hr HPSkpos)
                  (real_plus
                     (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                (real_mult m h))
                     h)
                  (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                             (real_plus (real_mult m h) h))
                  Hstep2
                  (real_eq_sym
                     (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                (real_plus (real_mult m h) h))
                     (real_plus
                        (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                                   (real_mult m h))
                        h)
                     (real_plus_assoc (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                        (real_mult m h) h))).
    assert (Hinner : real_lt (real_plus (real_mult m h) h) (real_plus h h))
      by exact (real_lt_plus_compat_lt_le (real_mult m h) h h h Hmh
                  (real_le_refl h)).
    assert (Hfin : real_lt (geod_b_kl_sum n r PSk Hr HPSkpos) (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0) (real_plus h h)))
      by exact (real_lt_eq_lt
                  (geod_b_kl_sum n r PSk Hr HPSkpos)
                  (real_plus (real_plus h h) (real_mult (geod_b_pow m (Datatypes.S k)) KL0))
                  (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0) (real_plus h h))
                  (real_lt_trans (geod_b_kl_sum n r PSk Hr HPSkpos) (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0) (real_plus (real_mult m h) h)) (real_plus (real_plus h h) (real_mult (geod_b_pow m (Datatypes.S k)) KL0)) Hassoc (real_eq_lt_lt
                      (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0) (real_plus (real_mult m h) h))
                      (real_plus (real_plus (real_mult m h) h) (real_mult (geod_b_pow m (Datatypes.S k)) KL0))
                      (real_plus (real_plus h h) (real_mult (geod_b_pow m (Datatypes.S k)) KL0))
                      (real_plus_comm (real_mult (geod_b_pow m (Datatypes.S k)) KL0) (real_plus (real_mult m h) h))
                      (real_lt_plus_compat_lt_le (real_plus (real_mult m h) h) (real_plus h h) (real_mult (geod_b_pow m (Datatypes.S k)) KL0) (real_mult (geod_b_pow m (Datatypes.S k)) KL0) Hinner (real_le_refl (real_mult (geod_b_pow m (Datatypes.S k)) KL0)))))
                  (real_plus_comm (real_plus h h) (real_mult (geod_b_pow m (Datatypes.S k)) KL0))).
    exact (real_lt_eq_lt (geod_b_kl_sum n r PSk Hr HPSkpos)
             (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                        (real_plus h h))
             (real_plus (real_mult (geod_b_pow m (Datatypes.S k)) KL0) eps)
             Hfin
             (RealSetoid.real_eq_plus_compat
                (real_mult (geod_b_pow m (Datatypes.S k)) KL0)
                (real_plus h h)
                (real_mult (geod_b_pow m (Datatypes.S k)) KL0) eps
                (real_eq_refl (real_mult (geod_b_pow m (Datatypes.S k)) KL0))
                Hhh)).
Qed.

(* ============================================================ *)

(* ============================================================ *)

Print Assumptions geod_b_le_lt_trans.
Print Assumptions geod_b_kappa_lt_one.
Print Assumptions geod_b_half_double.
Print Assumptions geod_b_pow_pos.
Print Assumptions geod_b_pow_mono_decr.
Print Assumptions geod_b_interp_Z_pos.
Print Assumptions geod_b_step_next_pos.
Print Assumptions geod_b_step_next_norm.
Print Assumptions geod_b_iterate.
Print Assumptions geod_b_step_kl_eps.
Print Assumptions geod_b_policy_iter_step_margin.
Print Assumptions geod_b_policy_iter_step.
Print Assumptions geod_b_policy_iter_iter.
