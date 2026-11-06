(* ConstructiveWorld-Set -- constructive geometric convergence-rate accounts for iterated KL contraction. *)

(** * UpReqIterGeomRate: sharp geometric-sum and simplified step-weighted error accounts for iterated KL contraction.

    Mission.  Single-step and iterated geometric contraction rates for KL
      divergence along the [geodi_iterate] orbit: [igr_geom_step_eps],
      [igr_geom_step_discharged_B], [igr_iter_geom_rate_tight_eps],
      [igr_iter_geom_rate_tight], [igr_iter_geom_rate_eps],
      [igr_iter_geom_rate], [igr_iter_geom_rate_witness],
      [igr_iter_geom_rate_witness_one], and [igr_k_select].

    Dependencies.  Stdlib [List], [PeanoNat], [QArith.Qring], [QArith.QArith].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp], [UpRealLeB], [G07_KLWall],
      [UpReqGeomD], [UpReqGeomIter] of this development.

    References.  This development, UpReqIterGeomRate.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqIterGeomRate.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.QArith.
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
Require Import G07_KLWall.
Require Import UpReqGeomD.
Require Import UpReqGeomIter.
Import RealInterfaceEnhancedMod.
Local Open Scope nat_scope.

(* ========== carrier definitions ========== *)

(* the geometric rate base: kappa := 1 - eta *)
Definition igr_kappa (eta : Real) : Real := real_plus real_one (real_opp eta).

(* the sharp error account: G_t = sum_{i<t} kappa^i, with the recursion
   G_O = 0 and G_{S m} = 1 + kappa·G_m (equal to the term-by-term sum
   1 + k + ... + k^{t-1}, up to the order of association). *)
Fixpoint igr_gsum (k : Real) (t : nat) : Real :=
  match t with
  | Datatypes.O => real_zero
  | Datatypes.S m => real_plus real_one (real_mult k (igr_gsum k m))
  end.

(* t·x, by repeated addition in nat (the accumulated step-weighted error
   of the simplified account) *)
Fixpoint igr_nmul (t : nat) (x : Real) : Real :=
  match t with
  | Datatypes.O => real_zero
  | Datatypes.S m => real_plus x (igr_nmul m x)
  end.

(* ========== ring and order auxiliaries (destruct + ring style, following UpStepKLM3) ========== *)

(* 0·x == 0 *)
Lemma igr_mult_zero_r : forall x : Real, real_eq (real_mult real_zero x) real_zero.
Proof. intros x. destruct x as [v Hv]. apply real_eq_of_zero_diff.
  intro n. apply qeq_imp_qeqT. simpl. ring. Qed.

(* left distributivity: a·(b+c) == a·b + a·c *)
Lemma igr_distrib_l : forall a b c : Real,
  real_eq (real_mult a (real_plus b c)) (real_plus (real_mult a b) (real_mult a c)).
Proof. intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring. Qed.

(* right distributivity: (a+b)·c == a·c + b·c *)
Lemma igr_distrib_r : forall a b c : Real,
  real_eq (real_mult (real_plus a b) c) (real_plus (real_mult a c) (real_mult b c)).
Proof. intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring. Qed.

(* reassociation: a·(b·c) == (a·b)·c *)
Lemma igr_ring_reassoc : forall a b c : Real,
  real_eq (real_mult a (real_mult b c)) (real_mult (real_mult a b) c).
Proof. intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring. Qed.

(* atomic ring identity A: k·(X+Y) + e == k·X + (k·Y + e) *)
Lemma igr_ring_step_a : forall k X Y e : Real,
  real_eq (real_plus (real_mult k (real_plus X Y)) e)
          (real_plus (real_mult k X) (real_plus (real_mult k Y) e)).
Proof. intros k X Y e.
  destruct k as [a Ha]. destruct X as [b Hb]. destruct Y as [c Hc]. destruct e as [f Hf].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring. Qed.

(* atomic ring identity B: (1 + k·G)·e == e + k·(G·e) *)
Lemma igr_ring_step_b : forall k G e : Real,
  real_eq (real_mult (real_plus real_one (real_mult k G)) e)
          (real_plus e (real_mult k (real_mult G e))).
Proof. intros k G e.
  destruct k as [a Ha]. destruct G as [b Hb]. destruct e as [f Hf].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring. Qed.

(* the combined inductive-step identity of the sharp account (assembled
   from the atoms; powb_pow/igr_gsum pass through unchanged):
   kappa·(kappa^m·KL0 + G_m·eps) + eps
     == (kappa·kappa^m)·KL0 + (1 + kappa·G_m)·eps. *)
Lemma igr_ring_step : forall (k KL0 G e : Real) (m : nat),
  real_eq
    (real_plus (real_mult k (real_plus (real_mult (powb_pow k m) KL0)
                                        (real_mult G e)))
               e)
    (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
               (real_mult (real_plus real_one (real_mult k G)) e)).
Proof.
  intros k KL0 G e m.
  pose proof (igr_ring_step_a k (real_mult (powb_pow k m) KL0)
                (real_mult G e) e) as H1.
  pose proof (igr_ring_reassoc k (powb_pow k m) KL0) as H2.
  pose proof (real_plus_comm (real_mult k (real_mult G e)) e) as H3.
  pose proof (igr_ring_step_b k G e) as H4.
  apply (real_eq_trans
           (real_plus (real_mult k (real_plus (real_mult (powb_pow k m) KL0)
                                              (real_mult G e)))
                      e)
           (real_plus (real_mult k (real_mult (powb_pow k m) KL0))
                      (real_plus (real_mult k (real_mult G e)) e))
           (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
                      (real_mult (real_plus real_one (real_mult k G)) e))).
  - exact H1.
  - apply (real_eq_trans
             (real_plus (real_mult k (real_mult (powb_pow k m) KL0))
                        (real_plus (real_mult k (real_mult G e)) e))
             (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
                        (real_plus (real_mult k (real_mult G e)) e))
             (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
                        (real_mult (real_plus real_one (real_mult k G)) e))).
    + exact (RealSetoid.real_eq_plus_compat
                (real_mult k (real_mult (powb_pow k m) KL0))
                (real_plus (real_mult k (real_mult G e)) e)
                (real_mult (real_mult k (powb_pow k m)) KL0)
                (real_plus (real_mult k (real_mult G e)) e)
                H2
                (real_eq_refl (real_plus (real_mult k (real_mult G e)) e))).
    + apply (real_eq_trans
               (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
                          (real_plus (real_mult k (real_mult G e)) e))
               (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
                          (real_plus e (real_mult k (real_mult G e))))
               (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
                          (real_mult (real_plus real_one (real_mult k G)) e))).
      * exact (RealSetoid.real_eq_plus_compat
                  (real_mult (real_mult k (powb_pow k m)) KL0)
                  (real_plus (real_mult k (real_mult G e)) e)
                  (real_mult (real_mult k (powb_pow k m)) KL0)
                  (real_plus e (real_mult k (real_mult G e)))
                  (real_eq_refl (real_mult (real_mult k (powb_pow k m)) KL0))
                  H3).
      * exact (RealSetoid.real_eq_plus_compat
                  (real_mult (real_mult k (powb_pow k m)) KL0)
                  (real_plus e (real_mult k (real_mult G e)))
                  (real_mult (real_mult k (powb_pow k m)) KL0)
                  (real_mult (real_plus real_one (real_mult k G)) e)
                  (real_eq_refl (real_mult (real_mult k (powb_pow k m)) KL0))
                  (real_eq_sym (real_mult (real_plus real_one (real_mult k G)) e)
                               (real_plus e (real_mult k (real_mult G e))) H4)).
Qed.

(* 0 < d implies x < x + d (a rewriting chain through zero, on already
   proved base lemmas) *)
Lemma igr_lt_plus_r : forall (x d : Real),
  real_lt real_zero d -> real_lt x (real_plus x d).
Proof.
  intros x d Hd.
  pose proof (real_lt_plus_compat_lt_le real_zero d x x Hd (real_le_refl x)) as H0.
  pose proof (real_eq_lt_lt x (real_plus real_zero x) (real_plus d x)
                (real_eq_sym (real_plus real_zero x) x (kl_plus_zero_l x)) H0) as H1.
  exact (real_lt_eq_lt x (real_plus d x) (real_plus x d) H1
           (real_plus_comm d x)).
Qed.

(* 0 < d ⟹ x <= x + d *)
Lemma igr_le_plus_r : forall (x d : Real),
  real_lt real_zero d -> real_le x (real_plus x d).
Proof.
  intros x d Hd.
  exact (kl_le_eq_l (real_plus x real_zero) (real_plus x d) x           (real_le_plus_compat x x real_zero d (real_le_refl x)              (kl_lt_le_bridge real_zero d Hd))           (real_plus_zero x)).
Qed.

(* ========== the assumption-free single-step contraction (the instance lemma closed along the orbit) ========== *)

(* KL(pi*||pi_{t+1}) <= kappa·KL(pi*||pi_t) + eps, in real_le form.
   The Real-layer eps-graded counterpart of the S05 abstract-layer
   policy_iter_kl_geom_step (S05_AlignmentGRPO.v:4436): the two carrier
   argument slots of the interface step_kl_eta_bound are supplied by the
   orbit itself, with the HZ slot := geodi_zpos (the Set-level encoding of
   the non-trivial premise NatLt 0 n, on the id_false_true ex-falso
   precedent of UpReqGeomIter.v:119) and the Hqv slot := geodi_next_pos
   (baked from the same literal terms as the HZ slot). *)
Theorem igr_geom_step_eps :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S t) i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S t) i)))
    (real_plus
       (real_mult (igr_kappa eta)
          (geod_lsum n (fun i : nat =>
             real_kl_term (r i)
               (geodi_iterate n r Hr eta p Hp Hn t i)
               (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i))))
       eps).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t eps Heps.
  unfold geod_lsum in *.
  unfold geodi_iterate, geodi_iterate_pos.
  cbn [geodi_seq].
  destruct (geodi_seq n r Hr (real_plus real_one (real_opp eta)) p Hp Hn t) as [q Hq] eqn:Em.
  pose proof (geodi_seq_norm_pair n r Hr (real_plus real_one (real_opp eta)) p Hp Hn Hnormp t q Hq Em)
    as HnormQ.
  unfold geod_lsum in HnormQ.
  (* the S15 native instance with the KL arguments swapped: the p-slot :=
     r (the reference pi-star), the r-slot := q (pi_t), the
     eta-slot := kappa; after the swap,
     KL(pi*||next) <= kappa·KL(pi*||pi_t) + eta·eps. *)
  pose proof (real_step_kl_eta_bound_eps n r q (igr_kappa eta) Hr Hq
                Hnormr HnormQ
                (geodi_zpos n r q (igr_kappa eta) Hr Hq Hn)
                (geodi_next_pos n r q (igr_kappa eta) Hr Hq Hn)
                (geod_kappa_pos eta Hlt1) (geod_kappa_le_one eta Heta)
                (real_mult eta eps)
                (real_mult_positive eta eps Heta Heps)) as Hstep.
  (* eta·eps <= eps, by order preservation of multiplication under
     eta <= 1 plus the rewriting 1·eps == eps *)
  pose proof (kl_le_eq_r (real_mult eta eps) (real_mult real_one eps) eps
                (real_le_mult_compat_weak eta real_one eps
                   (kl_lt_le_bridge real_zero eps Heps)
                   (kl_lt_le_bridge eta real_one Hlt1))
                (kl_mult_one_l eps)) as Hscale.
  pose proof (real_le_plus_compat
                (real_mult (igr_kappa eta)
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))
                      (List.seq 0 n)))
                (real_mult (igr_kappa eta)
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))
                      (List.seq 0 n)))
                (real_mult eta eps) eps
                (real_le_refl
                   (real_mult (igr_kappa eta)
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))
                         (List.seq 0 n)))) Hscale) as Hle2.
  exact (real_le_trans _ _ _ Hstep Hle2).
Qed.

(* the Bishop form (sharp): KL(pi*||pi_{t+1}) <=_B kappa·KL(pi*||pi_t).
   Closed in one step by real_le_closure_b_one (UpRealLeB.v:381), feeding
   igr_geom_step_eps at each budget d (the eps slot of the instance lemma
   takes any positive budget). *)
Theorem igr_geom_step_discharged_B :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat),
  real_le_b
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S t) i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S t) i)))
    (real_mult (igr_kappa eta)
       (geod_lsum n (fun i : nat =>
          real_kl_term (r i)
            (geodi_iterate n r Hr eta p Hp Hn t i)
            (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t.
  exact (real_le_closure_b_one _ _
    (fun d Hd => igr_geom_step_eps n r Hr eta Heta Hlt1 p Hp
                   Hnormr Hnormp Hn t d Hd)).
Qed.

(* ========== order properties of the error account ========== *)

(* G_m >= 0, preserved along the recursion under the premise kappa >= 0 *)
Lemma igr_gsum_nonneg : forall (eta : Real) (Heta : real_lt real_zero eta)
    (Hlt1 : real_lt eta real_one) (m : nat),
  real_le real_zero (igr_gsum (igr_kappa eta) m).
Proof.
  intros eta Heta Hlt1 m. induction m as [| m IH].
  - exact (real_le_refl real_zero).
  - pose proof (kl_lt_le_bridge real_zero (igr_kappa eta)
                  (geod_kappa_pos eta Hlt1)) as Hkle.
    pose proof (real_le_mult_compat_weak real_zero (igr_kappa eta)
                  (igr_gsum (igr_kappa eta) m) IH Hkle) as Hm0.
    pose proof (kl_le_eq_l (real_mult real_zero (igr_gsum (igr_kappa eta) m))
                  (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m))
                  real_zero Hm0 (igr_mult_zero_r (igr_gsum (igr_kappa eta) m))) as HkG.
    exact (kl_le_eq_l (real_plus real_zero real_zero)
             (real_plus real_one (real_mult (igr_kappa eta)
                               (igr_gsum (igr_kappa eta) m)))
             real_zero
             (real_le_plus_compat real_zero real_one real_zero
                (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m))
                (kl_lt_le_bridge real_zero real_one real_lt_zero_one) HkG)
             kl_zero_plus_zero).
Qed.

(* G_{S m} > 0 (the positivity certificate of the D slot in the Bishop
   completer; the strict term 1 > 0 plus kappa·G_m >= 0) *)
Lemma igr_gsum_S_pos : forall (eta : Real) (Heta : real_lt real_zero eta)
    (Hlt1 : real_lt eta real_one) (m : nat),
  real_lt real_zero (igr_gsum (igr_kappa eta) (Datatypes.S m)).
Proof.
  intros eta Heta Hlt1 m.
  pose proof (kl_lt_le_bridge real_zero (igr_kappa eta)
                (geod_kappa_pos eta Hlt1)) as Hkle.
  pose proof (igr_gsum_nonneg eta Heta Hlt1 m) as Hg0.
  pose proof (real_le_mult_compat_weak real_zero (igr_kappa eta)
                (igr_gsum (igr_kappa eta) m) Hg0 Hkle) as Hm0.
  pose proof (kl_le_eq_l (real_mult real_zero (igr_gsum (igr_kappa eta) m))
                (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m))
                real_zero Hm0 (igr_mult_zero_r (igr_gsum (igr_kappa eta) m))) as HkG.
  exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
           (real_plus real_one (real_mult (igr_kappa eta)
                             (igr_gsum (igr_kappa eta) m)))
           (real_eq_sym (real_plus real_zero real_zero) real_zero
              kl_zero_plus_zero)
           (real_lt_plus_compat_lt_le real_zero real_one real_zero
              (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m))
              real_lt_zero_one HkG)).
Qed.

(* G_t <= t·1 (the bridge to the simplified account: the discount
   kappa <= 1 never inflates the account) *)
Lemma igr_gsum_le_nmul : forall (eta : Real) (Heta : real_lt real_zero eta)
    (Hlt1 : real_lt eta real_one) (t : nat),
  real_le (igr_gsum (igr_kappa eta) t) (igr_nmul t real_one).
Proof.
  intros eta Heta Hlt1 t. induction t as [| m IH].
  - exact (real_le_refl real_zero).
  - pose proof (geod_kappa_le_one eta Heta) as Hkle.
    pose proof (real_le_mult_compat_weak (igr_kappa eta) real_one
                  (igr_gsum (igr_kappa eta) m)
                  (igr_gsum_nonneg eta Heta Hlt1 m) Hkle) as Hdisc.
    pose proof (kl_le_eq_r (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m))
                  (real_mult real_one (igr_gsum (igr_kappa eta) m))
                  (igr_gsum (igr_kappa eta) m) Hdisc
                  (kl_mult_one_l (igr_gsum (igr_kappa eta) m))) as Hdisc2.
    pose proof (real_le_trans _ _ _ Hdisc2 IH) as Hstep2.
    exact (real_le_plus_compat real_one real_one
             (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m))
             (igr_nmul m real_one) (real_le_refl real_one) Hstep2).
Qed.

(* (t·1)·eps == t·eps (the distribution identity of igr_nmul over a one
   coefficient) *)
Lemma igr_nmul_mult_one : forall (t : nat) (eps : Real),
  real_eq (real_mult (igr_nmul t real_one) eps) (igr_nmul t eps).
Proof.
  intros t eps. induction t as [| m IH].
  - exact (igr_mult_zero_r eps).
  - cbn [igr_nmul].
    exact (real_eq_trans
             (real_mult (real_plus real_one (igr_nmul m real_one)) eps)
             (real_plus (real_mult real_one eps) (real_mult (igr_nmul m real_one) eps))
             (real_plus eps (igr_nmul m eps))
             (igr_distrib_r real_one (igr_nmul m real_one) eps)
             (RealSetoid.real_eq_plus_compat
                (real_mult real_one eps) (real_mult (igr_nmul m real_one) eps)
                eps (igr_nmul m eps)
                (kl_mult_one_l eps)
                IH)).
Qed.

(* ========== the iterated geometric rate, main statements ========== *)

(* the sharp geometric-sum account, in real_le form:
   KL(pi*||pi_t) <= (1-eta)^t·KL(pi*||pi_0) + (sum_{i<t}(1-eta)^i)·eps.
   The inductive step is fed the full eps, and the identity igr_ring_step
   closes it as one lemma (no geometric-sum identity needed). *)
Theorem igr_iter_geom_rate_tight_eps :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn t i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_mult (powb_pow (igr_kappa eta) t)
          (geod_lsum n (fun i : nat =>
             real_kl_term (r i) (p i) (Hr i) (Hp i))))
       (real_mult (igr_gsum (igr_kappa eta) t) eps)).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t eps Heps.
  unfold geod_lsum in *.
  induction t as [| m IH].
  - (* t = 0: KL_0 <= 1·KL_0 + 0·eps (the eq side rests on the identity
         0·eps == 0) *)
    apply (RealSetoid.real_le_id_l
             (real_list_sum nat
                (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                (List.seq 0 n))
             (real_mult real_one
                (real_list_sum nat
                   (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                   (List.seq 0 n)))
             (real_plus
                (real_mult real_one
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                      (List.seq 0 n)))
                (real_mult real_zero eps))).
    + exact (real_eq_sym
                (real_mult real_one
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                      (List.seq 0 n)))
                (real_list_sum nat
                   (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                   (List.seq 0 n))
                (kl_mult_one_l
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                      (List.seq 0 n)))).
    + exact (inr
                (real_eq_trans
                   (real_mult real_one
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_plus
                      (real_mult real_one
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      real_zero)
                   (real_plus
                      (real_mult real_one
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      (real_mult real_zero eps))
                   (real_eq_sym
                      (real_plus
                         (real_mult real_one
                            (real_list_sum nat
                               (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                               (List.seq 0 n)))
                         real_zero)
                      (real_mult real_one
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      (real_plus_zero
                         (real_mult real_one
                            (real_list_sum nat
                               (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                               (List.seq 0 n)))))
                   (RealSetoid.real_eq_plus_compat
                      (real_mult real_one
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      real_zero
                      (real_mult real_one
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      (real_mult real_zero eps)
                      (real_eq_refl
                         (real_mult real_one
                            (real_list_sum nat
                               (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                               (List.seq 0 n))))
                      (real_eq_sym (real_mult real_zero eps) real_zero
                         (igr_mult_zero_r eps))))).
  - (* t = S m: the sigT pair decomposition, the instance lemma fed the
       full eps, the kappa-weighted inductive premise (IH), and the
       combined identity *)
    cbn [powb_pow igr_gsum].
    unfold geodi_iterate, geodi_iterate_pos in IH.
    unfold geodi_iterate, geodi_iterate_pos.
    revert IH.
    cbn [geodi_seq].
    destruct (geodi_seq n r Hr (real_plus real_one (real_opp eta)) p Hp Hn m) as [q Hq] eqn:Em.
    intro IH.
    pose proof (geodi_seq_norm_pair n r Hr (real_plus real_one (real_opp eta)) p Hp Hn Hnormp m q Hq Em)
      as HnormQ.
    unfold geod_lsum in HnormQ.
    (* the S15 native instance with swapped KL arguments (as above, fed
       the full eps) *)
    pose proof (real_step_kl_eta_bound_eps n r q (igr_kappa eta) Hr Hq
                  Hnormr HnormQ
                  (geodi_zpos n r q (igr_kappa eta) Hr Hq Hn)
                  (geodi_next_pos n r q (igr_kappa eta) Hr Hq Hn)
                  (geod_kappa_pos eta Hlt1) (geod_kappa_le_one eta Heta)
                  eps Heps) as Hstep.
    (* the kappa weighting of the inductive premise IH (strictly positive
       left factor, after UpReqGeomIter.v:330) *)
    pose proof (geodi_mult_le_compat_l (igr_kappa eta)
                  (real_list_sum nat
                     (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))
                     (List.seq 0 n))
                  (real_plus
                     (real_mult (powb_pow (igr_kappa eta) m)
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                           (List.seq 0 n)))
                     (real_mult (igr_gsum (igr_kappa eta) m) eps))
                  (geod_kappa_pos eta Hlt1) IH) as Hmul.
    pose proof (real_le_plus_compat
                  (real_mult (igr_kappa eta)
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))
                        (List.seq 0 n)))
                  (real_mult (igr_kappa eta)
                     (real_plus
                        (real_mult (powb_pow (igr_kappa eta) m)
                           (real_list_sum nat
                              (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                              (List.seq 0 n)))
                        (real_mult (igr_gsum (igr_kappa eta) m) eps)))
                  eps eps
                  Hmul (real_le_refl eps)) as Hmid.
    pose proof (real_le_trans
                  (real_list_sum nat
                     (fun i : nat =>
                        real_kl_term (r i)
                          (real_step_next n r q (igr_kappa eta) Hr Hq
                             (geodi_zpos n r q (igr_kappa eta) Hr Hq Hn) i)
                          (Hr i)
                          (geodi_next_pos n r q (igr_kappa eta) Hr Hq Hn i))
                     (List.seq 0 n))
                  (real_plus
                     (real_mult (igr_kappa eta)
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))
                           (List.seq 0 n)))
                     eps)
                  (real_plus
                     (real_mult (igr_kappa eta)
                        (real_plus
                           (real_mult (powb_pow (igr_kappa eta) m)
                              (real_list_sum nat
                                 (fun i : nat =>
                                    real_kl_term (r i) (p i) (Hr i) (Hp i))
                                 (List.seq 0 n)))
                           (real_mult (igr_gsum (igr_kappa eta) m) eps)))
                     eps)
                  Hstep Hmid) as Hchain.
    exact (kl_le_eq_r
             (real_list_sum nat
                (fun i : nat =>
                   real_kl_term (r i)
                     (real_step_next n r q (igr_kappa eta) Hr Hq
                        (geodi_zpos n r q (igr_kappa eta) Hr Hq Hn) i)
                     (Hr i)
                     (geodi_next_pos n r q (igr_kappa eta) Hr Hq Hn i))
                (List.seq 0 n))
             (real_plus
                (real_mult (igr_kappa eta)
                   (real_plus
                      (real_mult (powb_pow (igr_kappa eta) m)
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      (real_mult (igr_gsum (igr_kappa eta) m) eps)))
                eps)
             (real_plus
                (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                      (List.seq 0 n)))
                (real_mult
                   (real_plus real_one
                      (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m)))
                   eps))
             Hchain
             (igr_ring_step (igr_kappa eta)
                (real_list_sum nat
                   (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                   (List.seq 0 n))
                (igr_gsum (igr_kappa eta) m) eps m)).
Qed.

(* shared t = 0 closure of the Bishop forms: KL_0 <=_B 1·KL_0 + z, for
   any error term z with z == 0 *)
Lemma igr_B_zero : forall (KL0 z : Real),
  real_eq z real_zero ->
  real_le_b KL0 (real_plus (real_mult real_one KL0) z).
Proof.
  intros KL0 z Hz. unfold real_le_b. intros d Hd.
  pose proof (igr_lt_plus_r KL0 d Hd) as Hlt.
  pose proof (real_eq_sym
                (real_plus (real_mult real_one KL0) (real_plus z d))
                (real_plus (real_plus (real_mult real_one KL0) z) d)
                (real_plus_assoc (real_mult real_one KL0) z d)) as Heq1.
  pose proof (real_eq_trans
                (real_plus (real_plus (real_mult real_one KL0) z) d)
                (real_plus (real_mult real_one KL0) (real_plus z d))
                (real_plus KL0 d)
                Heq1
                (RealSetoid.real_eq_plus_compat
                   (real_mult real_one KL0)
                   (real_plus z d)
                   KL0 d
                   (kl_mult_one_l KL0)
                   (real_eq_trans (real_plus z d) (real_plus real_zero d) d
                      (RealSetoid.real_eq_plus_compat z d real_zero d
                         Hz (real_eq_refl d))
                      (kl_plus_zero_l d)))) as Heq.
  exact (real_lt_eq_lt KL0 (real_plus KL0 d)
           (real_plus (real_plus (real_mult real_one KL0) z) d)
           Hlt (real_eq_sym _ _ Heq)).
Qed.

(* the sharp geometric-sum account, in Bishop form:
   KL(pi*||pi_t) <=_B (1-eta)^t·KL(pi*||pi_0) + (sum_{i<t}(1-eta)^i)·eps.
   The t >= 1 branch closes in one step by real_le_closure_b
   (D := G_t, with the positivity certificate igr_gsum_S_pos); the t = 0
   branch is a ring rewriting (igr_B_zero). *)
Theorem igr_iter_geom_rate_tight :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le_b
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn t i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_mult (powb_pow (igr_kappa eta) t)
          (geod_lsum n (fun i : nat =>
             real_kl_term (r i) (p i) (Hr i) (Hp i))))
       (real_mult (igr_gsum (igr_kappa eta) t) eps)).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t eps Heps.
  unfold geod_lsum in *.
  destruct t as [| m].
  - exact (igr_B_zero
             (real_list_sum nat
                (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                (List.seq 0 n)) (real_mult real_zero eps)
             (igr_mult_zero_r eps)).
  - apply (real_le_closure_b
             (real_list_sum nat
                (fun i : nat =>
                   real_kl_term (r i)
                     (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m) i)
                     (Hr i)
                     (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S m) i))
                (List.seq 0 n))
             (real_plus
                (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                      (List.seq 0 n)))
                (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
             (igr_gsum (igr_kappa eta) (Datatypes.S m))
             (igr_gsum_S_pos eta Heta Hlt1 m)).
    intros e He.
    pose proof (real_lt_plus_compat real_zero eps real_zero e Heps He) as Hpe0.
    pose proof (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                  (real_plus eps e)
                  (real_eq_sym (real_plus real_zero real_zero) real_zero
                     kl_zero_plus_zero) Hpe0) as Hpe.
    pose proof (igr_iter_geom_rate_tight_eps n r Hr eta Heta Hlt1 p Hp
                  Hnormr Hnormp Hn (Datatypes.S m) (real_plus eps e) Hpe) as Ht.
    pose proof (igr_distrib_l (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps e)
      as Hd1.
    pose proof (kl_eq_le_bridge
                  (real_plus
                     (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                           (List.seq 0 n)))
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                        (real_plus eps e)))
                  (real_plus
                     (real_plus
                        (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                           (real_list_sum nat
                              (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                              (List.seq 0 n)))
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) e))
                  (real_eq_trans
                (real_plus
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                      (real_plus eps e)))
                (real_plus
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_plus
                      (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                      (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) e)))
                (real_plus
                   (real_plus
                      (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) e))
                (RealSetoid.real_eq_plus_compat
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                      (real_plus eps e))
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_plus
                      (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                      (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) e))
                   (real_eq_refl
                      (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n))))
                   Hd1)
                (real_plus_assoc
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) e)))) as Hbridge.
    exact (real_le_trans
             (real_list_sum nat
                (fun i : nat =>
                   real_kl_term (r i)
                     (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m) i)
                     (Hr i)
                     (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S m) i))
                (List.seq 0 n))
             (real_plus
                (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                      (List.seq 0 n)))
                (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                   (real_plus eps e)))
             (real_plus
                (real_plus
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
             (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) e))
             Ht Hbridge).
Qed.

(* the simplified t·eps account, in real_le form: obtained from the
   sharp account by the scaling G_t <= t·1. *)
Theorem igr_iter_geom_rate_eps :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn t i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_mult (powb_pow (igr_kappa eta) t)
          (geod_lsum n (fun i : nat =>
             real_kl_term (r i) (p i) (Hr i) (Hp i))))
       (igr_nmul t eps)).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t eps Heps.
  unfold geod_lsum in *.
  pose proof (igr_iter_geom_rate_tight_eps n r Hr eta Heta Hlt1 p Hp
                Hnormr Hnormp Hn t eps Heps) as Htight.
  (* G_t·eps <= (t·1)·eps == t·eps *)
  pose proof (real_le_mult_compat_weak (igr_gsum (igr_kappa eta) t)
                (igr_nmul t real_one) eps
                (kl_lt_le_bridge real_zero eps Heps)
                (igr_gsum_le_nmul eta Heta Hlt1 t)) as Hsc.
  pose proof (kl_le_eq_r (real_mult (igr_gsum (igr_kappa eta) t) eps)
                (real_mult (igr_nmul t real_one) eps) (igr_nmul t eps)
                Hsc (igr_nmul_mult_one t eps)) as Hsc2.
  exact (real_le_trans _ _ _ Htight
           (real_le_plus_compat
              (real_mult (powb_pow (igr_kappa eta) t)
                 (real_list_sum nat
                    (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                    (List.seq 0 n)))
              (real_mult (powb_pow (igr_kappa eta) t)
                 (real_list_sum nat
                    (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                    (List.seq 0 n)))
              (real_mult (igr_gsum (igr_kappa eta) t) eps) (igr_nmul t eps)
              (real_le_refl
                 (real_mult (powb_pow (igr_kappa eta) t)
                    (real_list_sum nat
                       (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                       (List.seq 0 n))))
              Hsc2)).
Qed.

(* the simplified t·eps account, in Bishop form: the t >= 1 branch goes
   through the sharp account and the inverse-funded budget rewriting
   G_{S m}·(eps + d·inv G_{S m}) == G_{S m}·eps + d; the t = 0 branch is
   a ring rewriting. *)
Theorem igr_iter_geom_rate :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le_b
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn t i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_mult (powb_pow (igr_kappa eta) t)
          (geod_lsum n (fun i : nat =>
             real_kl_term (r i) (p i) (Hr i) (Hp i))))
       (igr_nmul t eps)).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t eps Heps.
  unfold geod_lsum in *.
  destruct t as [| m].
  - unfold geodi_iterate, geodi_iterate_pos.
    cbn [geodi_seq projT1 projT2 powb_pow igr_nmul].
    exact (igr_B_zero
             (real_list_sum nat
                (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                (List.seq 0 n)) real_zero (real_eq_refl real_zero)).
  - (* the S m branch: G_{S m} > 0, with the inner budget
       e := eps + d·inv(G_{S m}) *)
    pose proof (igr_gsum_S_pos eta Heta Hlt1 m) as HgG.
    apply real_le_closure_b_one. intros d Hd.
    pose proof
      (real_mult_positive d
         (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)
         Hd (real_inv_pos_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)) as Hdi.
    pose proof (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                  (real_plus eps
                     (real_mult d
                        (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))
                  (real_eq_sym (real_plus real_zero real_zero) real_zero
                     kl_zero_plus_zero)
                  (real_lt_plus_compat_lt_le real_zero eps real_zero
                     (real_mult d
                        (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))
                     Heps
                     (kl_lt_le_bridge real_zero
                        (real_mult d
                           (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))
                        Hdi))) as Hbudget.
    pose proof (igr_iter_geom_rate_tight_eps n r Hr eta Heta Hlt1 p Hp
                  Hnormr Hnormp Hn (Datatypes.S m)
                  (real_plus eps
                     (real_mult d
                        (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))
                  Hbudget) as Htight.
    (* the rewriting: G·(eps + d·invG) == G·eps + d *)
    pose proof (igr_distrib_l (igr_gsum (igr_kappa eta) (Datatypes.S m))
                  eps (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))) as Hd1.
    pose proof (RealSetoid.real_eq_mult_compat
                  (igr_gsum (igr_kappa eta) (Datatypes.S m)) (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))
                  (igr_gsum (igr_kappa eta) (Datatypes.S m)) (real_mult (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG) d)
                  (real_eq_refl (igr_gsum (igr_kappa eta) (Datatypes.S m)))
                  (real_mult_comm d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))) as Hd2.
    pose proof (igr_ring_reassoc (igr_gsum (igr_kappa eta) (Datatypes.S m))
                  (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG) d) as Hd3.
    pose proof (RealSetoid.real_eq_mult_compat
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)) d
                  real_one d
                  (real_inv_pos_correct (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)
                  (real_eq_refl d)) as Hd4.
    pose proof (kl_mult_one_l d) as Hd5.
    pose proof (real_eq_trans
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                     (real_plus eps (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))))
                  (real_plus
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                        (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))))
                  (real_plus
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                     d)
                  Hd1
                  (RealSetoid.real_eq_plus_compat
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                        (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                     d
                     (real_eq_refl
                        (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                     (real_eq_trans
                        (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                           (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))
                        (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                           (real_mult (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG) d))
                        d
                        Hd2
                        (real_eq_trans
                           (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                              (real_mult (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG) d))
                           (real_mult
                              (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                                 (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)) d)
                           d
                           Hd3
                           (real_eq_trans
                              (real_mult
                                 (real_mult
                                    (igr_gsum (igr_kappa eta) (Datatypes.S m)) (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)) d)
                              (real_mult real_one d)
                              d
                              Hd4
                              Hd5))))) as Hsc.
    (* the chain: KL <= A + G·(eps + d·invG) == (A + G·eps) + d
       <= (A + t·eps) + d *)
    pose proof (RealSetoid.real_eq_plus_compat
                  (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n)))
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                     (real_plus eps (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))))
                  (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n)))
                  (real_plus
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                     d)
                  (real_eq_refl
                     (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                           (List.seq 0 n))))
                  Hsc) as HeqA.
    pose proof (real_plus_assoc
                  (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n)))
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                  d) as HeqB.
    pose proof (real_le_trans
                  (real_list_sum nat
                     (fun i : nat =>
                        real_kl_term (r i)
                          (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m) i)
                          (Hr i)
                          (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S m) i))
                     (List.seq 0 n))
                  (real_plus
                     (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                           (List.seq 0 n)))
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                        (real_plus eps (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))))
                  (real_plus
                     (real_plus
                        (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                           (real_list_sum nat
                              (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                              (List.seq 0 n)))
                        (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                     d)
                  Htight
                  (kl_eq_le_bridge _ _
                     (real_eq_trans
                        (real_plus
                           (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                              (real_list_sum nat
                                 (fun i : nat =>
                                    real_kl_term (r i) (p i) (Hr i) (Hp i))
                                 (List.seq 0 n)))
                           (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                              (real_plus eps (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))))
                        (real_plus
                           (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                              (real_list_sum nat
                                 (fun i : nat =>
                                    real_kl_term (r i) (p i) (Hr i) (Hp i))
                                 (List.seq 0 n)))
                           (real_plus
                              (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                              d))
                        (real_plus
                           (real_plus
                              (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                                 (real_list_sum nat
                                    (fun i : nat =>
                                       real_kl_term (r i) (p i) (Hr i) (Hp i))
                                    (List.seq 0 n)))
                              (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                           d)
                        HeqA HeqB))) as Hch1.
    pose proof (real_le_mult_compat_weak (igr_gsum (igr_kappa eta) (Datatypes.S m))
                  (igr_nmul (Datatypes.S m) real_one) eps
                  (kl_lt_le_bridge real_zero eps Heps)
                  (igr_gsum_le_nmul eta Heta Hlt1 (Datatypes.S m))) as Hsc2.
    pose proof (kl_le_eq_r
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                  (real_mult (igr_nmul (Datatypes.S m) real_one) eps)
                  (igr_nmul (Datatypes.S m) eps)
                  Hsc2 (igr_nmul_mult_one (Datatypes.S m) eps)) as Hsc3.
    exact (real_le_trans _ _ _ Hch1
             (real_le_plus_compat
                (real_plus
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                (real_plus
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (igr_nmul (Datatypes.S m) eps))
                d d
                (real_le_plus_compat
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                   (igr_nmul (Datatypes.S m) eps)
                   (real_le_refl
                      (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n))))
                   Hsc3)
                (real_le_refl d))).
Qed.

(* ============================================================ *)
(* Bishop-order preservation under a strictly positive left factor:                *)
(*   a <=_B b and 0 < c imply c·a <=_B c·b. The budget e·inv(c) appears            *)
(*   literally; the non-strict right-factor form would need an exact  *)
(*   non-negativity account of KL_0, which the library does not carry; *)
(*   so this strictly positive variant avoids it: division by c is     *)
(*   feasible. New mathematical content; no same-shaped lemma in the   *)
(*   library.                      *)
(* ============================================================ *)
Lemma igr_le_b_mult_l : forall (a b c : Real),
  real_le_b a b -> real_lt real_zero c -> real_le_b (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hab Hc. unfold real_le_b. intros e He.
  pose proof (real_mult_positive e (real_inv_pos c Hc) He
                 (real_inv_pos_pos c Hc)) as Hdic.
  pose proof (Hab (real_mult e (real_inv_pos c Hc)) Hdic) as Hlt.
  pose proof (real_mult_lt_compat_l a
                 (real_plus b (real_mult e (real_inv_pos c Hc))) c Hlt Hc) as Hlt2.
  pose proof (real_eq_trans
                 (real_mult c (real_mult e (real_inv_pos c Hc)))
                 (real_mult c (real_mult (real_inv_pos c Hc) e))
                 e
                 (RealSetoid.real_eq_mult_compat c (real_mult e (real_inv_pos c Hc)) c
                    (real_mult (real_inv_pos c Hc) e) (real_eq_refl c)
                    (real_mult_comm e (real_inv_pos c Hc)))
                 (real_eq_trans
                    (real_mult c (real_mult (real_inv_pos c Hc) e))
                    (real_mult (real_mult c (real_inv_pos c Hc)) e)
                    e
                    (igr_ring_reassoc c (real_inv_pos c Hc) e)
                    (real_eq_trans
                       (real_mult (real_mult c (real_inv_pos c Hc)) e)
                       (real_mult real_one e)
                       e
                       (RealSetoid.real_eq_mult_compat
                          (real_mult c (real_inv_pos c Hc)) e real_one e
                          (real_inv_pos_correct c Hc) (real_eq_refl e))
                       (kl_mult_one_l e)))) as Hring.
  pose proof (igr_distrib_l c b (real_mult e (real_inv_pos c Hc))) as Hdd.
  pose proof (real_lt_eq_lt (real_mult c a)
                (real_mult c (real_plus b (real_mult e (real_inv_pos c Hc))))
                (real_plus (real_mult c b) (real_mult c (real_mult e (real_inv_pos c Hc))))
                Hlt2 Hdd) as Hlt3.
  exact (real_lt_eq_lt (real_mult c a)
           (real_plus (real_mult c b) (real_mult c (real_mult e (real_inv_pos c Hc))))
           (real_plus (real_mult c b) e)
           Hlt3
           (RealSetoid.real_eq_plus_compat (real_mult c b)
              (real_mult c (real_mult e (real_inv_pos c Hc)))
              (real_mult c b) e
              (real_eq_refl (real_mult c b)) Hring)).
Qed.

(* ============================================================ *)
(* exact power upper bounds, dependences of the multiplication lemma   *)
(* and of the witnesses; the library PowB layer provides only Bishop            *)
(* ============================================================ *)
Lemma igr_powb_nonneg : forall (eta : Real) (Heta : real_lt real_zero eta)
    (Hlt1 : real_lt eta real_one) (t : nat),
  real_le real_zero (powb_pow (igr_kappa eta) t).
Proof.
  intros eta Heta Hlt1 t. induction t as [| m IH].
  - exact (kl_lt_le_bridge real_zero real_one real_lt_zero_one).
  - pose proof (kl_lt_le_bridge real_zero (igr_kappa eta)
                  (geod_kappa_pos eta Hlt1)) as Hk0.
    pose proof (real_le_mult_compat_weak real_zero (igr_kappa eta)
                  (powb_pow (igr_kappa eta) m) IH Hk0) as Hstep.
    exact (kl_le_eq_l (real_mult real_zero (powb_pow (igr_kappa eta) m))
             (real_mult (igr_kappa eta) (powb_pow (igr_kappa eta) m))
             real_zero Hstep
             (igr_mult_zero_r (powb_pow (igr_kappa eta) m))).
Qed.

Lemma igr_powb_le_one : forall (eta : Real) (Heta : real_lt real_zero eta)
    (Hlt1 : real_lt eta real_one) (t : nat),
  real_le (powb_pow (igr_kappa eta) t) real_one.
Proof.
  intros eta Heta Hlt1 t. induction t as [| m IH].
  - cbn [powb_pow]. exact (real_le_refl real_one).
  - pose proof (real_le_mult_compat_weak (igr_kappa eta) real_one
                  (powb_pow (igr_kappa eta) m)
                  (igr_powb_nonneg eta Heta Hlt1 m)
                  (geod_kappa_le_one eta Heta)) as Hdisc.
    pose proof (kl_le_eq_r (real_mult (igr_kappa eta) (powb_pow (igr_kappa eta) m))
                  (real_mult real_one (powb_pow (igr_kappa eta) m))
                  (powb_pow (igr_kappa eta) m)
                  Hdisc (kl_mult_one_l (powb_pow (igr_kappa eta) m))) as Hdisc2.
    exact (real_le_trans _ _ _ Hdisc2 IH).
Qed.

(* ============================================================ *)
(* the four-layer sigT witness construction (the S-branch split route)                  *)
(*                                                              *)
(*   layer 1, igr_ring_scale_inv: the budget-rewriting ring identity as          *)
(*     a standalone single-goal lemma: G·(e + d·invG) == G·e + d, with *)
(*     the invG positivity certificate carried along.                 *)
(*   layer 2, igr_iter_budget_witness_S: the per-budget real_le chain            *)
(*     at the step S m, a standalone single-goal lemma specialized to  *)
(*     t = S m (t case-splits are always factored into lemmas).       *)
(*   layer 3, igr_iter_geom_rate_witness: a Defined term-level match on       *)
(*     t (destruct is unavailable at the term level, so match is used),              *)
(*     producing the Bishop witness of "KL_t <=_B kappa^t·KL_0 +    *)
(*     G_t·eps": unfolding real_le_b gives the per-budget witness map f           *)
(*     for all d > 0, and real_lt is a sigT, so the extraction face is *)
(*     the computable map eps -> (gap, N).                                      *)
(*   layer 4, igr_iter_geom_rate_witness_one: the budget d := 1            *)
(*     instance, a concrete real_lt sigT value (the end product of the *)
(*     extraction face).                    *)
(*                                                              *)
(* no new premises are introduced: the witness and its concrete          *)
(* instance are Defined (genuinely computable, not sealed by Qed); the  *)
(* auxiliary lemmas ring_scale_inv / budget_witness_S close by Qed.    *)
(* extraction-face organization: interface bridging lemmas stay out of
   the extraction face, and the witness statements use plain
   geod_*/real_* names (the organization that extracts the six
   pieces at 0 magic).     *)
(* ============================================================ *)

(* layer 1: the budget-rewriting ring identity. For G strictly positive
   (with the inverse-positivity certificate carried along),
   G·(e + d·invG) == G·e + d, so the inverse-funded budget d cancels
   exactly. *)
Lemma igr_ring_scale_inv : forall (G : Real) (HG : real_lt real_zero G)
    (e d : Real),
  real_eq
    (real_mult G (real_plus e (real_mult d (real_inv_pos G HG))))
    (real_plus (real_mult G e) d).
Proof.
  intros G HG e d.
  pose proof (igr_distrib_l G e (real_mult d (real_inv_pos G HG))) as Hd1.
  pose proof (RealSetoid.real_eq_mult_compat G
                 (real_mult d (real_inv_pos G HG)) G
                 (real_mult (real_inv_pos G HG) d)
                 (real_eq_refl G)
                 (real_mult_comm d (real_inv_pos G HG))) as Hd2.
  pose proof (igr_ring_reassoc G (real_inv_pos G HG) d) as Hd3.
  pose proof (RealSetoid.real_eq_mult_compat
                 (real_mult G (real_inv_pos G HG)) d real_one d
                 (real_inv_pos_correct G HG) (real_eq_refl d)) as Hd4.
  pose proof (kl_mult_one_l d) as Hd5.
  exact (real_eq_trans
           (real_mult G (real_plus e (real_mult d (real_inv_pos G HG))))
           (real_plus (real_mult G e)
              (real_mult G (real_mult d (real_inv_pos G HG))))
           (real_plus (real_mult G e) d)
           Hd1
           (RealSetoid.real_eq_plus_compat
              (real_mult G e)
              (real_mult G (real_mult d (real_inv_pos G HG)))
              (real_mult G e) d
              (real_eq_refl (real_mult G e))
              (real_eq_trans
                 (real_mult G (real_mult d (real_inv_pos G HG)))
                 (real_mult G (real_mult (real_inv_pos G HG) d))
                 d
                 Hd2
                 (real_eq_trans
                    (real_mult G (real_mult (real_inv_pos G HG) d))
                    (real_mult (real_mult G (real_inv_pos G HG)) d)
                    d
                    Hd3
                    (real_eq_trans
                       (real_mult (real_mult G (real_inv_pos G HG)) d)
                       (real_mult real_one d)
                       d
                       Hd4
                       Hd5))))).
Qed.

(* layer 2: the per-budget real_le chain at the step S m (single goal,
   with t specialized to S m by the split discipline):
   KL_{S m} <= (kappa^{S m}·KL_0 + G_{S m}·eps) + d, where the inner
   budget e := eps + d·invG feeds the sharp account and the ring
   identity cancels the funding. *)
Lemma igr_iter_budget_witness_S :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n) (m : nat) (eps : Real) (Heps : real_lt real_zero eps)
    (d : Real) (Hd : real_lt real_zero d),
  real_le
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m) i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S m) i)))
    (real_plus
       (real_plus
          (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
             (geod_lsum n (fun i : nat =>
                real_kl_term (r i) (p i) (Hr i) (Hp i))))
          (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
       d).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn m eps Heps d Hd.
  unfold geod_lsum in *.
  pose proof (igr_gsum_S_pos eta Heta Hlt1 m) as HgG.
  pose proof (real_mult_positive d
                 (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)
                 Hd
                 (real_inv_pos_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)) as Hdi.
  pose proof (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                 (real_plus eps
                    (real_mult d
                       (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))
                 (real_eq_sym (real_plus real_zero real_zero) real_zero
                    kl_zero_plus_zero)
                 (real_lt_plus_compat_lt_le real_zero eps real_zero
                    (real_mult d
                       (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))
                    Heps
                    (kl_lt_le_bridge real_zero
                       (real_mult d
                          (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))
                       Hdi))) as Hbudget.
  pose proof (igr_iter_geom_rate_tight_eps n r Hr eta Heta Hlt1 p Hp
                 Hnormr Hnormp Hn (Datatypes.S m)
                 (real_plus eps
                    (real_mult d
                       (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))
                 Hbudget) as Htight.
  pose proof (igr_ring_scale_inv
                 (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG eps d) as Hsc.
  pose proof (RealSetoid.real_eq_plus_compat
                  (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n)))
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                     (real_plus eps
                        (real_mult d
                           (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))))
                  (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n)))
                  (real_plus
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                     d)
                  (real_eq_refl
                     (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                           (List.seq 0 n))))
                  Hsc) as HeqA.
  pose proof (real_plus_assoc
                  (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n)))
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                  d) as HeqB.
  exact (real_le_trans
           (real_list_sum nat
              (fun i : nat =>
                 real_kl_term (r i)
                   (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m) i)
                   (Hr i)
                   (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S m) i))
              (List.seq 0 n))
           (real_plus
              (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                 (real_list_sum nat
                    (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                    (List.seq 0 n)))
              (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                 (real_plus eps
                    (real_mult d
                       (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))))
           (real_plus
              (real_plus
                 (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                    (real_list_sum nat
                       (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                       (List.seq 0 n)))
                 (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
              d)
           Htight
           (kl_eq_le_bridge _ _
              (real_eq_trans
                 (real_plus
                    (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                       (real_list_sum nat
                          (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                          (List.seq 0 n)))
                    (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                       (real_plus eps
                          (real_mult d
                             (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))))
                 (real_plus
                    (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                       (real_list_sum nat
                          (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                          (List.seq 0 n)))
                    (real_plus
                       (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                       d))
                 (real_plus
                    (real_plus
                       (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                          (real_list_sum nat
                             (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                             (List.seq 0 n)))
                       (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                    d)
                 HeqA HeqB))).
Qed.

(* layer 3: the witness itself (a Defined term-level match on t; the
   branches already live in standalone lemmas, so this piece carries no
   proof and is a pure term-level assembly). *)
Definition igr_iter_geom_rate_witness :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le_b
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn t i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_mult (powb_pow (igr_kappa eta) t)
          (geod_lsum n (fun i : nat =>
             real_kl_term (r i) (p i) (Hr i) (Hp i))))
       (real_mult (igr_gsum (igr_kappa eta) t) eps)) :=
  fun (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n) (t : nat) (eps : Real)
    (Heps : real_lt real_zero eps) =>
  match t as t0 return
    real_le_b
      (geod_lsum n (fun i : nat =>
         real_kl_term (r i)
           (geodi_iterate n r Hr eta p Hp Hn t0 i)
           (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t0 i)))
      (real_plus
         (real_mult (powb_pow (igr_kappa eta) t0)
            (geod_lsum n (fun i : nat =>
               real_kl_term (r i) (p i) (Hr i) (Hp i))))
         (real_mult (igr_gsum (igr_kappa eta) t0) eps))
    with
  | Datatypes.O =>
      igr_B_zero
        (geod_lsum n (fun i : nat =>
           real_kl_term (r i) (p i) (Hr i) (Hp i)))
        (real_mult real_zero eps)
        (igr_mult_zero_r eps)
  | Datatypes.S m =>
      real_le_closure_b_one
        (geod_lsum n (fun i : nat =>
           real_kl_term (r i)
             (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m) i)
             (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S m) i)))
        (real_plus
           (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
              (geod_lsum n (fun i : nat =>
                 real_kl_term (r i) (p i) (Hr i) (Hp i))))
           (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
        (igr_iter_budget_witness_S n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn
           m eps Heps)
  end.

(* layer 4: the d := 1 instance, the budget taken as the literal 1 (with
   the existing certificate real_lt_zero_one): a concrete real_lt sigT
   value, the end product of the extraction face, with the map
   eps -> (gap, N) made explicit. *)
Definition igr_iter_geom_rate_witness_one :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_lt
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn t i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_plus
          (real_mult (powb_pow (igr_kappa eta) t)
             (geod_lsum n (fun i : nat =>
                real_kl_term (r i) (p i) (Hr i) (Hp i))))
          (real_mult (igr_gsum (igr_kappa eta) t) eps))
       real_one) :=
  fun (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n) (t : nat) (eps : Real)
    (Heps : real_lt real_zero eps) =>
  igr_iter_geom_rate_witness n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn
    t eps Heps real_one real_lt_zero_one.

(* ============================================================ *)
(* the k-selector, Q-certificate side, the igr_ side of this file.                                                    *)
(*                                                              *)
(* the Real-layer real_le is an Or encoding (constructively      *)
(* undecidable), so the least-t search is made decidable on the      *)
(* Q-certificate side: the caller supplies Q-layer certificates for       *)
(* kappa, KL_0, eps and target, and the test is exact in Q; igr_k_select
   enumerates the window [0,H] and returns the first (= least) passing
   index, with None := no solution inside the window.                                 *)
(* interface symmetry note: same shape as the C10 mix_k_select
   (eps -> least t, as a nat enumeration).  *)
(* ============================================================ *)

Fixpoint igr_qpow (q : Q) (t : nat) : Q :=
  match t with
  | Datatypes.O => 1%Q
  | Datatypes.S m => Qmult q (igr_qpow q m)
  end.

(* window enumeration: returns the least passing index in [0,t]
   (None := none). *)
Fixpoint igr_k_enum (test : nat -> bool) (t : nat) : option nat :=
  match t with
  | Datatypes.O => if test Datatypes.O then Some Datatypes.O else None
  | Datatypes.S m =>
      match igr_k_enum test m with
      | Some k => Some k
      | None => if test (Datatypes.S m) then Some (Datatypes.S m) else None
      end
  end.

(* the Q-layer test: kappa^t·KL_0 + t·eps <= target (Q-certificate side,
   exactly decidable). *)
Definition igr_k_test (kq KL0q epsq targetq : Q) (t : nat) : bool :=
  Qle_bool (Qplus (Qmult (igr_qpow kq t) KL0q)
                  (Qmult (Qmake (Z.of_nat t) 1) epsq))
           targetq.

(* the k-selector: given the Q certificates and the search window H, a
   Defined function returns the least passing index. *)
Definition igr_k_select (kq KL0q epsq targetq : Q) (H : nat) : option nat :=
 igr_k_enum (igr_k_test kq KL0q epsq targetq) H.

(* enumeration soundness: a returned index always passes the test. *)
Lemma igr_k_enum_sound : forall (test : nat -> bool) (t k : nat),
  igr_k_enum test t = Some k -> test k = true.
Proof.
  intros test t. induction t as [| m IH]; intros k Hk.
  - cbn [igr_k_enum] in Hk. destruct (test Datatypes.O) eqn:Ht0.
    + injection Hk. intros Hkk. rewrite <- Hkk. exact Ht0.
    + discriminate Hk.
  - cbn [igr_k_enum] in Hk.
    destruct (igr_k_enum test m) eqn:Em.
    + (* the inner window already decided: destruct-eqn has resolved
         IH/Hk to Some n form, substituted directly in the same shape *)
      apply IH. exact Hk.
    + destruct (test (Datatypes.S m)) eqn:Ht.
      * injection Hk. intros Hkk. rewrite <- Hkk. exact Ht.
      * discriminate Hk.
Qed.

(* the no-solution account of the enumeration: None implies every index
   in the window fails. *)
Lemma igr_k_enum_none : forall (test : nat -> bool) (t : nat),
  igr_k_enum test t = None -> forall j : nat, j <= t -> test j = false.
Proof.
  intros test t. induction t as [| m IH]; intros Heq j Hj.
  - cbn [igr_k_enum] in Heq. destruct (test Datatypes.O) eqn:Ht0.
    + discriminate Heq.
    + apply (proj1 (Nat.lt_eq_cases j 0)) in Hj.
      destruct Hj as [Hlt0 | Heqj0].
      * exfalso. exact (Nat.nlt_0_r j Hlt0).
      * rewrite Heqj0. exact Ht0.
  - cbn [igr_k_enum] in Heq.
    destruct (igr_k_enum test m) eqn:Em.
    + discriminate Heq.
    + destruct (test (Datatypes.S m)) eqn:HtS.
      * discriminate Heq.
      * apply (proj1 (Nat.lt_eq_cases j (Datatypes.S m))) in Hj.
        destruct Hj as [Hlt | Heqj].
        -- exact (IH eq_refl j (proj1 (Nat.lt_succ_r j m) Hlt)).
        -- rewrite Heqj. exact HtS.
Qed.

(* minimality: Some k implies k passes and every index below k fails
   (a genuine least index). *)
Lemma igr_k_enum_min : forall (test : nat -> bool) (t k : nat),
  igr_k_enum test t = Some k ->
  forall j : nat, j < k -> test j = false.
Proof.
  intros test t. induction t as [| m IH]; intros k Hk j Hj.
  - cbn [igr_k_enum] in Hk. destruct (test Datatypes.O) eqn:Ht0.
    + injection Hk. intros Hkk. rewrite <- Hkk in Hj.
      exfalso. exact (Nat.nlt_0_r j Hj).
    + discriminate Hk.
  - cbn [igr_k_enum] in Hk.
    destruct (igr_k_enum test m) eqn:Em.
    + (* the inner window already decided: destruct-eqn has resolved IH
         to Some n form, inheriting minimality directly *)
      exact (IH k Hk j Hj).
    + destruct (test (Datatypes.S m)) eqn:Ht.
      * (* the k = S m case: j < S m gives j <= m, hence the no-solution
           account *)
        injection Hk. intros Hkk. rewrite <- Hkk in Hj.
        apply (proj1 (Nat.lt_succ_r j m)) in Hj.
        exact (igr_k_enum_none test m Em j Hj).
      * discriminate Hk.
Qed.

(* the k-selector main account: Some k implies k passes and every index
   below k fails (a single-goal conjunction). *)
Lemma igr_k_select_min : forall (kq KL0q epsq targetq : Q) (H k : nat),
  igr_k_select kq KL0q epsq targetq H = Some k ->
  igr_k_test kq KL0q epsq targetq k = true /\
  (forall j : nat, j < k -> igr_k_test kq KL0q epsq targetq j = false).
Proof.
  intros kq KL0q epsq targetq H k Hsel.
  unfold igr_k_select in Hsel. split.
  - exact (igr_k_enum_sound _ _ _ Hsel).
  - exact (igr_k_enum_min _ _ _ Hsel).
Qed.

(* ============================================================ *)
(* registry of scope notes                                                    *)
(*                                                              *)
(* layer declaration: every statement of this file lives in the        *)
(* Real-ized discrete-distribution layer (the folded sums geod_lsum /    *)
(* real_kl_term), on the same layer as the instance lemma (S15:1014);
   the S05 abstract layer is separate territory, with no waiting on it
   and no overlap with it.                                *)
(*                                                              *)
(* sharp-account exemption: the geometric-sum identity *)
(* eta·G_t == 1 - kappa^t is neither built nor used: with the error
   account recursion G_{S m} := 1 + kappa·G_m, the inductive step closes
   by pure ring reasoning. If a downstream consumer needs the closed form     *)
(* (1-kappa^t)/eta, it can be recovered from igr_gsum of this file.     *)
(*                                                              *)
(* gap 4 of the tail note (UpReqGeomIter.v:869-877) is verified absent
   here: the le_b multiplication closure      *)
(* a <=_B b /\ 0 <=_B c => a·c <=_B b·c is not built in this file, since   *)
(* its non-strict right-factor case needs an exact non-negativity of
   KL_0 (Gibbs in real_le form) and the library carries only the eps form  *)
(* (real_gibbs_inequality_eps); the layered-floor discipline keeps it     *)
(* unbuilt, and the original registry stands. The sharp geometric-sum
   account delivered here does not pass through that gap.        *)
(*                                                              *)
(* witness account: igr_iter_geom_rate_witness is a Defined term-level   *)
(* match on t (destruct is not available at the term level); the S
   branch is split into the single-goal lemma             *)
(* igr_iter_budget_witness_S plus the ring identity igr_ring_scale_inv.   *)
(* The witness measures the sharp account G_t·eps (not the simplified
   t·eps); the layer-4 _one piece is the budget d := 1 instance (the        *)
(* end product of the extraction face). The least-t search of the
   k-selector igr_k_select is made decidable on the Q-certificate side        *)
(* (the Real-layer Or encoding is constructively undecidable).          *)
(*                                                              *)
(* per-statement Assumptions audits appear at the end of the file.                                       *)
(* ============================================================ *)

Print Assumptions igr_geom_step_eps.
Print Assumptions igr_geom_step_discharged_B.
Print Assumptions igr_iter_geom_rate_tight_eps.
Print Assumptions igr_iter_geom_rate_tight.
Print Assumptions igr_iter_geom_rate_eps.
Print Assumptions igr_iter_geom_rate.
Print Assumptions igr_le_b_mult_l.
Print Assumptions igr_powb_le_one.
Print Assumptions igr_ring_scale_inv.
Print Assumptions igr_iter_budget_witness_S.
Print Assumptions igr_iter_geom_rate_witness.
Print Assumptions igr_iter_geom_rate_witness_one.
Print Assumptions igr_k_select_min.
