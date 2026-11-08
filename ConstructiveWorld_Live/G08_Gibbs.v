(* ConstructiveWorld-Set — finite merge group: Gibbs inequality and log bounds. *)

(** * G08_Gibbs: merged statement family for the Gibbs inequality, the
      cross-entropy decomposition, and the log-nonpositivity dischargers.

    Mission.  A finite merge group (members merged verbatim) carrying
      ([gibbsd_] / [hzlogd_] / [gibbe2_] prefixes): the Gibbs inequality
      chain over the Bishop order [real_le_b] ([gibbsd_gibbs_pointwise_B],
      [gibbsd_gibbs_inequality], [gibbsd_cross_entropy_decomp]), the
      log-nonpositivity discharge family ([gibbsd_two_pos],
      [hzlogd_discharge_real], [hzlogd_proj_min_kl_hlogzfree],
      [hzlogd_proj_min_kl_bool]), and the finite-list sum-zero extraction
      side ([gibbe2_le_b_id_r], [gibbe2_list_sum_zero_extract_bool]).

    Dependencies.  The library files listed in the Require face below.

    References.  Gibbs' inequality and the entropy decomposition
      H(p,q) = S[p] + KL(p||q) over constructive reals.

    Constructivity.  All proofs close by [Qed]; zero admission words; no
      classical axioms; the statement face is carried by the [Set] layer
      ([real_le_b]/[real_eq]/[real_lt] all [Set]-valued, zero Prop
      leakage).

    Build.  [coqc -native-compiler no -q -Q . "" G08_Gibbs.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

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
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part A. Bishop-order algebra primitives (opp / scalar                        *)
(* multiplication / transport over [real_le_b])                                 *)
(* ============================================================ *)

(* A1: translating the right end of [lt] from −eps to +eps (the foundation of the opp-reversal lemma) *)
Lemma gibbsd_lt_add_opp_r : forall x y e : Real,
  real_lt real_zero e ->
  real_lt (real_plus x (real_opp e)) y ->
  real_lt x (real_plus y e).
Proof.
  intros x y e Heps Hlt.
  apply (RealSetoid.real_lt_compat
           (real_plus e (real_plus x (real_opp e))) x
           (real_plus e y) (real_plus y e)).
  - apply real_eq_sym.
    apply (real_eq_trans x (real_plus x (real_plus (real_opp e) e))
                         (real_plus e (real_plus x (real_opp e)))).
    + apply (real_eq_trans x (real_plus x real_zero)
                           (real_plus x (real_plus (real_opp e) e))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (RealSetoid.real_eq_plus_compat x real_zero x
                 (real_plus (real_opp e) e)).
        -- apply real_eq_refl.
        -- apply (real_eq_trans real_zero (real_plus e (real_opp e))
                     (real_plus (real_opp e) e)).
           ++ apply real_eq_sym. apply real_plus_opp.
           ++ apply real_plus_comm.
    + apply (real_eq_trans (real_plus x (real_plus (real_opp e) e))
                           (real_plus (real_plus x (real_opp e)) e)
                           (real_plus e (real_plus x (real_opp e)))).
      * apply real_plus_assoc.
      * apply real_plus_comm.
  - apply real_plus_comm.
  - exact (real_lt_plus_translate e (real_plus x (real_opp e)) y Hlt).
Qed.

(* A2: opp reverses the Bishop order (the le_b counterpart of the req layer's [opp_le_compat]) *)
Lemma gibbsd_le_b_opp : forall a b : Real,
  real_le_b a b -> real_le_b (real_opp b) (real_opp a).
Proof.
  intros a b H eps Heps. unfold real_le_b in H.
  apply gibbsd_lt_add_opp_r.
  - exact Heps.
  - apply (RealSetoid.real_lt_compat
             (real_opp (real_plus b eps))
             (real_plus (real_opp b) (real_opp eps))
             (real_opp a) (real_opp a)).
    + exact (real_opp_plus b eps).
    + apply real_eq_refl.
    + exact (real_opp_lt_compat a (real_plus b eps) (H eps Heps)).
Qed.

(* A3: real_eq transport of the left end in the Bishop order (the le_b counterpart of the req layer's [le_id_l]) *)
Lemma gibbsd_le_b_id_l : forall a b c : Real,
  real_eq a b -> real_le_b b c -> real_le_b a c.
Proof.
  intros a b c Hab H eps Heps. unfold real_le_b in H.
  exact (RealSetoid.real_lt_compat b a (real_plus c eps) (real_plus c eps)
           (real_eq_sym a b Hab) (real_eq_refl (real_plus c eps))
           (H eps Heps)).
Qed.

(* A5: the minus-flip identity −(a−b) == b−a (counterpart of the req layer's reqd_minus_one_flip) *)
Lemma gibbsd_minus_flip : forall a b : Real,
  real_eq (real_opp (real_plus a (real_opp b)))
          (real_plus b (real_opp a)).
Proof.
  intros a b.
  apply (real_eq_trans (real_opp (real_plus a (real_opp b)))
                       (real_plus (real_opp a) (real_opp (real_opp b)))
                       (real_plus b (real_opp a))).
  - exact (real_opp_plus a (real_opp b)).
  - apply (real_eq_trans (real_plus (real_opp a) (real_opp (real_opp b)))
             (real_plus (real_opp (real_opp b)) (real_opp a))
             (real_plus b (real_opp a))).
    + apply real_plus_comm.
    + apply (RealSetoid.real_eq_plus_compat
               (real_opp (real_opp b)) (real_opp a)
               b (real_opp a)
               (real_opp_opp b) (real_eq_refl (real_opp a))).
Qed.

(* A4: right multiplication by a positive preserves the Bishop order (the le_b counterpart of the req layer's req_le_mult_compat_r) *)
Lemma gibbsd_le_b_mult_pos_r : forall c a b : Real,
  real_lt real_zero c -> real_le_b a b ->
  real_le_b (real_mult c a) (real_mult c b).
Proof.
  intros c a b Hc H eps Heps. unfold real_le_b in H.
  set (e0 := real_mult eps (real_inv_pos c Hc)).
  assert (Hpos0 : real_lt real_zero e0).
  { exact (real_mult_positive eps (real_inv_pos c Hc) Heps
             (real_inv_pos_pos c Hc)). }
  apply (RealSetoid.real_lt_compat
           (real_mult c a) (real_mult c a)
           (real_mult c (real_plus b e0))
           (real_plus (real_mult c b) eps)).
  - apply real_eq_refl.
  - apply (real_eq_trans
             (real_mult c (real_plus b e0))
             (real_plus (real_mult c b) (real_mult c e0))
             (real_plus (real_mult c b) eps)).
    + exact (real_distrib c b e0).
    + exact (RealSetoid.real_eq_plus_compat (real_mult c b) (real_mult c e0)
               (real_mult c b) eps
               (real_eq_refl (real_mult c b))
               (real_eq_trans
                  (real_mult c e0)
                  (real_mult eps (real_mult c (real_inv_pos c Hc))) eps
                  (real_eq_trans
                     (real_mult c e0)
                     (real_mult (real_mult eps c) (real_inv_pos c Hc))
                     (real_mult eps (real_mult c (real_inv_pos c Hc)))
                     (real_eq_trans
                        (real_mult c e0)
                        (real_mult (real_mult c eps) (real_inv_pos c Hc))
                        (real_mult (real_mult eps c) (real_inv_pos c Hc))
                        (real_mult_assoc c eps (real_inv_pos c Hc))
                        (RealSetoid.real_eq_mult_compat
                           (real_mult c eps) (real_inv_pos c Hc)
                           (real_mult eps c) (real_inv_pos c Hc)
                           (real_mult_comm c eps)
                           (real_eq_refl (real_inv_pos c Hc))))
                     (real_eq_sym
                        (real_mult eps (real_mult c (real_inv_pos c Hc)))
                        (real_mult (real_mult eps c) (real_inv_pos c Hc))
                        (real_mult_assoc eps c (real_inv_pos c Hc))))
                  (real_eq_trans
                     (real_mult eps (real_mult c (real_inv_pos c Hc)))
                     (real_mult eps real_one) eps
                     (RealSetoid.real_eq_mult_compat eps
                        (real_mult c (real_inv_pos c Hc)) eps real_one
                        (real_eq_refl eps) (real_inv_pos_correct c Hc))
                     (real_mult_one eps)))).
  - exact (real_mult_lt_compat_l a (real_plus b e0) c (H e0 Hpos0) Hc).
Qed.

(* ============================================================ *)
(* Part B. Pointwise slot-proof preliminaries (eq-layer identities)             *)
(* ============================================================ *)

(* B0: p·(q/p) == q (fraction cancellation; an assoc / comm / inv_correct chain) *)
Lemma gibbsd_p_mult_ratio : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_mult q (real_inv_pos p Hp))) q.
Proof.
  intros p q Hp.
  apply (real_eq_trans
           (real_mult p (real_mult q (real_inv_pos p Hp)))
           (real_mult q (real_mult p (real_inv_pos p Hp))) q).
  - apply (real_eq_trans
             (real_mult p (real_mult q (real_inv_pos p Hp)))
             (real_mult (real_mult p q) (real_inv_pos p Hp))
             (real_mult q (real_mult p (real_inv_pos p Hp)))).
    + exact (real_mult_assoc p q (real_inv_pos p Hp)).
    + apply (real_eq_trans
               (real_mult (real_mult p q) (real_inv_pos p Hp))
               (real_mult (real_mult q p) (real_inv_pos p Hp))
               (real_mult q (real_mult p (real_inv_pos p Hp)))).
      * apply (RealSetoid.real_eq_mult_compat (real_mult p q)
                 (real_inv_pos p Hp) (real_mult q p) (real_inv_pos p Hp)
                 (real_mult_comm p q) (real_eq_refl (real_inv_pos p Hp))).
      * apply real_eq_sym.
        exact (real_mult_assoc q p (real_inv_pos p Hp)).
  - apply (real_eq_trans
             (real_mult q (real_mult p (real_inv_pos p Hp)))
             (real_mult q real_one) q).
    + apply (RealSetoid.real_eq_mult_compat q
               (real_mult p (real_inv_pos p Hp)) q real_one
               (real_eq_refl q) (real_inv_pos_correct p Hp)).
    + exact (real_mult_one q).
Qed.

(* B1: p·(1 − q/p) == p − q (the Real counterpart of the req layer's reqd_p_minus_ratio) *)
Lemma gibbsd_p_minus_ratio : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_plus real_one
                         (real_opp (real_mult q (real_inv_pos p Hp)))))
          (real_plus p (real_opp q)).
Proof.
  intros p q Hp.
  apply (real_eq_trans
           (real_mult p (real_plus real_one
                      (real_opp (real_mult q (real_inv_pos p Hp)))))
           (real_plus (real_mult p real_one)
                      (real_mult p (real_opp (real_mult q (real_inv_pos p Hp)))))
           (real_plus p (real_opp q))).
  - exact (real_distrib p real_one
             (real_opp (real_mult q (real_inv_pos p Hp)))).
  - apply (RealSetoid.real_eq_plus_compat (real_mult p real_one)
             (real_mult p (real_opp (real_mult q (real_inv_pos p Hp))))
             p (real_opp q)).
    + exact (real_mult_one p).
    + apply (real_eq_trans
               (real_mult p (real_opp (real_mult q (real_inv_pos p Hp))))
               (real_opp (real_mult p (real_mult q (real_inv_pos p Hp))))
               (real_opp q)).
      * apply real_eq_sym.
        exact (real_opp_mult p (real_mult q (real_inv_pos p Hp))).
      * apply (RealSetoid.real_eq_opp_compat
                 (real_mult p (real_mult q (real_inv_pos p Hp))) q
                 (gibbsd_p_mult_ratio p q Hp)).
Qed.

(* ============================================================ *)
(* Part C. The Bishop summation layer (lifting pointwise facts to sums          *)
(* over [real_list_sum])                                                        *)
(* ============================================================ *)

Lemma gibbsd_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
           (real_plus real_one real_one)
           (real_eq_sym _ _ (real_plus_zero real_zero))
           (real_lt_plus_compat_lt_le real_zero real_one real_zero real_one
              real_lt_zero_one (inl real_lt_zero_one))).
Qed.

Definition gibbsd_half : Real :=
  real_inv_pos (real_plus real_one real_one) gibbsd_two_pos.

Lemma gibbsd_half_pos : real_lt real_zero gibbsd_half.
Proof.
  exact (real_inv_pos_pos (real_plus real_one real_one) gibbsd_two_pos).
Qed.

(* half-distribution: e·h + e·h == e (the identity behind halving the eps budget) *)
Lemma gibbsd_half_sum : forall e : Real,
  real_eq (real_plus (real_mult e gibbsd_half) (real_mult e gibbsd_half)) e.
Proof.
  intro e.
  apply (real_eq_trans
           (real_plus (real_mult e gibbsd_half) (real_mult e gibbsd_half))
           (real_mult e (real_plus gibbsd_half gibbsd_half)) e).
  - apply real_eq_sym.
    exact (real_distrib e gibbsd_half gibbsd_half).
  - apply (real_eq_trans
             (real_mult e (real_plus gibbsd_half gibbsd_half))
             (real_mult e real_one) e).
    + apply (RealSetoid.real_eq_mult_compat e
               (real_plus gibbsd_half gibbsd_half) e real_one).
      * apply real_eq_refl.
      * apply (real_eq_trans (real_plus gibbsd_half gibbsd_half)
                 (real_mult (real_plus real_one real_one) gibbsd_half)
                 real_one).
        -- apply real_eq_sym.
           apply (real_eq_trans
                    (real_mult (real_plus real_one real_one) gibbsd_half)
                    (real_plus (real_mult real_one gibbsd_half)
                               (real_mult real_one gibbsd_half))
                    (real_plus gibbsd_half gibbsd_half)).
           ++ exact (real_eq_sym
                       (real_plus (real_mult real_one gibbsd_half)
                                  (real_mult real_one gibbsd_half))
                       (real_mult (real_plus real_one real_one) gibbsd_half)
                       (real_distrib_r_local real_one real_one gibbsd_half)).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_mult real_one gibbsd_half)
                       (real_mult real_one gibbsd_half)
                       gibbsd_half gibbsd_half).
              ** exact (real_eq_trans (real_mult real_one gibbsd_half)
                          (real_mult gibbsd_half real_one) gibbsd_half
                          (real_mult_comm real_one gibbsd_half)
                          (real_mult_one gibbsd_half)).
              ** exact (real_eq_trans (real_mult real_one gibbsd_half)
                          (real_mult gibbsd_half real_one) gibbsd_half
                          (real_mult_comm real_one gibbsd_half)
                          (real_mult_one gibbsd_half)).
        -- exact (real_inv_pos_correct (real_plus real_one real_one)
                    gibbsd_two_pos).
    + exact (real_mult_one e).
Qed.

(* C3: pointwise le_b ⟹ summed le_b (the Bishop counterpart of the req layer's   *)
(*   fsum_le; induction with the budget halved: eps is split as e/2 + e/2, and   *)
(*   the nil remainder goes through [real_lt_plus_r_zero])                       *)
Lemma gibbsd_list_sum_le_b : forall (X : Type) (f g : X -> Real) (l : list X),
  (forall s : X, real_le_b (f s) (g s)) ->
  real_le_b (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l Hpt.
  unfold real_le_b.
  induction l as [| w l IH].
  - intros eps Heps. simpl.
    exact (real_lt_plus_r_zero real_zero eps Heps).
  - intros eps Heps. simpl.
    assert (Hpos : real_lt real_zero (real_mult eps gibbsd_half)).
    { exact (real_mult_positive eps gibbsd_half Heps gibbsd_half_pos). }
    assert (Ha : real_lt (f w)
                   (real_plus (g w) (real_mult eps gibbsd_half))).
    { exact (Hpt w (real_mult eps gibbsd_half) Hpos). }
    assert (Ht : real_lt (real_list_sum X f l)
                   (real_plus (real_list_sum X g l)
                              (real_mult eps gibbsd_half))).
    { exact (IH (real_mult eps gibbsd_half) Hpos). }
    apply (RealSetoid.real_lt_compat
             (real_plus (f w) (real_list_sum X f l))
             (real_plus (f w) (real_list_sum X f l))
             (real_plus (real_plus (g w) (real_mult eps gibbsd_half))
                        (real_plus (real_list_sum X g l)
                                   (real_mult eps gibbsd_half)))
             (real_plus (real_plus (g w) (real_list_sum X g l)) eps)).
    + apply real_eq_refl.
    + exact (real_eq_trans
               (real_plus (real_plus (g w) (real_mult eps gibbsd_half))
                          (real_plus (real_list_sum X g l)
                                     (real_mult eps gibbsd_half)))
               (real_plus (real_plus (g w) (real_list_sum X g l))
                          (real_plus (real_mult eps gibbsd_half)
                                     (real_mult eps gibbsd_half)))
               (real_plus (real_plus (g w) (real_list_sum X g l)) eps)
               (real_plus_swap_mid (g w) (real_mult eps gibbsd_half)
                                   (real_list_sum X g l)
                                   (real_mult eps gibbsd_half))
               (RealSetoid.real_eq_plus_compat
                  (real_plus (g w) (real_list_sum X g l))
                  (real_plus (real_mult eps gibbsd_half)
                             (real_mult eps gibbsd_half))
                  (real_plus (g w) (real_list_sum X g l))
                  eps
                  (real_eq_refl (real_plus (g w) (real_list_sum X g l)))
                  (gibbsd_half_sum eps))).
    + exact (real_lt_plus_compat _ _ _ _ Ha Ht).
Qed.

(* C4: Σ(p−q) == Σp − Σq (the Real counterpart of the req layer's fsum_minus) *)
Lemma gibbsd_list_sum_minus : forall (X : Type) (p q : X -> Real) (l : list X),
  real_eq (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
          (real_plus (real_list_sum X p l)
                     (real_opp (real_list_sum X q l))).
Proof.
  intros X p q l.
  apply (real_eq_trans
           (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
           (real_plus (real_list_sum X p l)
                      (real_list_sum X (fun s => real_opp (q s)) l))
           (real_plus (real_list_sum X p l)
                      (real_opp (real_list_sum X q l)))).
  - exact (real_list_sum_add X p (fun s => real_opp (q s)) l).
  - apply (RealSetoid.real_eq_plus_compat (real_list_sum X p l)
             (real_list_sum X (fun s => real_opp (q s)) l)
             (real_list_sum X p l)
             (real_opp (real_list_sum X q l))).
    + apply real_eq_refl.
    + exact (real_list_sum_opp X q l).
Qed.

(* ============================================================ *)
(* Part D. The deliverable proof main body                                      *)
(* ============================================================ *)

(* D0 [slot-proof position]: the pointwise Gibbs tangent p−q ≤_B p·(−log(q/p)).
   Logically colocated with req_gibbs_pointwise (UpReqDist:2066) — there the
   Hypothesis dist_log_le_linear is consumed (a slot with 10 downstream
   consumers); here [real_log_le_linear_B] (UpRealLeB:535) is supplied
   directly, closing it once and unconditionally.
   Chain: the slot log(q/p) ≤_B q/p−1 -> reversal by opp -> transport to
   1−q/p -> order-preserving left multiplication by p -> closed by the
   transport p·(1−q/p)==p−q. *)
Lemma gibbsd_gibbs_pointwise_B : forall (X : Type) (p q : X -> Real) (s : X)
  (Hps : real_lt real_zero (p s)) (Hqs : real_lt real_zero (q s)),
  real_le_b (real_plus (p s) (real_opp (q s)))
            (real_kl_term (p s) (q s) Hps Hqs).
Proof.
  intros X p q s Hps Hqs.
  unfold real_kl_term, real_le_b. intros eps Heps.
  set (Rqp := real_mult (q s) (real_inv_pos (p s) Hps)).
  set (Hr := real_mult_positive (q s) (real_inv_pos (p s) Hps) Hqs
               (real_inv_pos_pos (p s) Hps)).
  (* slot-proof position: this is where the req layer consumes dist_log_le_linear; the Bishop-order form supplies it directly *)
  assert (Hlin : real_le_b (real_log Rqp Hr)
                           (real_plus Rqp (real_opp real_one))).
  { exact (real_log_le_linear_B Rqp Hr). }
  assert (Hstep2 : real_le_b (real_plus real_one (real_opp Rqp))
                             (real_opp (real_log Rqp Hr))).
  { exact (gibbsd_le_b_id_l _ _ _
             (real_eq_sym _ _ (gibbsd_minus_flip Rqp real_one))
             (gibbsd_le_b_opp _ _ Hlin)). }
  assert (Hstep3 : real_le_b
                     (real_mult (p s)
                        (real_plus real_one (real_opp Rqp)))
                     (real_mult (p s) (real_opp (real_log Rqp Hr)))).
  { exact (gibbsd_le_b_mult_pos_r (p s) _ _ Hps Hstep2). }
  exact (gibbsd_le_b_id_l _ _ _
           (real_eq_sym _ _ (gibbsd_p_minus_ratio (p s) (q s) Hps))
           Hstep3 eps Heps).
Qed.

(* D1 [main deliverable]: the Real instantiation of the Gibbs inequality — 0 ≤_B Σ_s KL(p s‖q s).
   A Real-instantiation proof of req_gibbs_inequality (UpReqDist:2122,
   dist_log_le_linear with 10 downstream consumers): the normalization premises
   are copied from the req layer (in real_eq form), the summation layer is the
   [real_list_sum] machinery, the order is [real_le_b], and the argument
   positions are filled by the pointwise lemma D0.
   The statement has the same shape as E.13 real_gibbs_inequality_B: E.13 closes
   along the real_gibbs_inequality_eps route, this lemma along the log-tangent
   slot-proof route — the two routes corroborate each other. *)
Theorem gibbsd_gibbs_inequality :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormq : real_eq (real_list_sum X q l) real_one),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq.
  assert (Hle : real_le_b
                  (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
                  (real_list_sum X
                     (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
  { apply gibbsd_list_sum_le_b.
    intro s. exact (gibbsd_gibbs_pointwise_B X p q s (Hp s) (Hq s)). }
  assert (Hz : real_eq
                 (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
                 real_zero).
  { apply (real_eq_trans
             (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
             (real_plus (real_list_sum X p l)
                        (real_opp (real_list_sum X q l)))
             real_zero).
    - exact (gibbsd_list_sum_minus X p q l).
    - apply (real_eq_trans
               (real_plus (real_list_sum X p l)
                          (real_opp (real_list_sum X q l)))
               (real_plus real_one (real_opp real_one))
               real_zero).
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum X p l)
                 (real_opp (real_list_sum X q l)) real_one
                 (real_opp real_one)).
        * exact Hnormp.
        * apply (RealSetoid.real_eq_opp_compat (real_list_sum X q l) real_one
                   Hnormq).
      + exact (real_plus_opp real_one).
  }
  exact (gibbsd_le_b_id_l real_zero
           (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
           (real_list_sum X
              (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
           (real_eq_sym _ _ Hz) Hle).
Qed.

(* ============================================================ *)
(* Part E. The main lemma — cross_entropy_decomp, the first cascade layer,      *)
(*   proved the same way (the Real-instantiation counterpart of                 *)
(*   req_cross_entropy_decomp@UpReqDist:2431; the pointwise identity closes     *)
(*   toward q == p·(q/p) via the multiplicative log decomposition, with no      *)
(*   log-inverse cancellation)                                                  *)
(* ============================================================ *)

Theorem gibbsd_cross_entropy_decomp :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq
    (real_list_sum X
       (fun s : X => real_mult (p s) (real_opp (real_log (q s) (Hq s)))) l)
    (real_plus
       (real_list_sum X
          (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
       (real_list_sum X
          (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
Proof.
  intros X l p q Hp Hq.
  apply (real_eq_trans
           (real_list_sum X
              (fun s : X => real_mult (p s) (real_opp (real_log (q s) (Hq s)))) l)
           (real_list_sum X
              (fun s : X => real_plus
                            (real_mult (p s) (real_opp (real_log (p s) (Hp s))))
                            (real_kl_term (p s) (q s) (Hp s) (Hq s))) l)
           (real_plus
              (real_list_sum X
                 (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
              (real_list_sum X
                 (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))).
  - apply real_list_sum_ext. intro s0.
    unfold real_kl_term.
    set (Rqp := real_mult (q s0) (real_inv_pos (p s0) (Hp s0))).
    set (Hr := real_mult_positive (q s0) (real_inv_pos (p s0) (Hp s0)) (Hq s0)
                 (real_inv_pos_pos (p s0) (Hp s0))).
    set (Hpm := real_mult_positive (p s0) Rqp (Hp s0) Hr).
    assert (Hlogsplit : real_eq (real_log (q s0) (Hq s0))
                          (real_plus (real_log (p s0) (Hp s0))
                                     (real_log Rqp Hr))).
    { apply (real_eq_trans (real_log (q s0) (Hq s0))
                           (real_log (real_mult (p s0) Rqp) Hpm)
                           (real_plus (real_log (p s0) (Hp s0))
                                      (real_log Rqp Hr))).
      - exact (real_log_wd (q s0) (real_mult (p s0) Rqp) (Hq s0) Hpm
                  (real_eq_sym _ _
                     (gibbsd_p_mult_ratio (p s0) (q s0) (Hp s0)))).
      - exact (real_log_mult (p s0) Rqp (Hp s0) Hr).
    }
    apply (real_eq_trans
             (real_mult (p s0) (real_opp (real_log (q s0) (Hq s0))))
             (real_mult (p s0)
                (real_plus (real_opp (real_log (p s0) (Hp s0)))
                           (real_opp (real_log Rqp Hr))))
             (real_plus (real_mult (p s0) (real_opp (real_log (p s0) (Hp s0))))
                        (real_mult (p s0) (real_opp (real_log Rqp Hr))))).
    + apply (RealSetoid.real_eq_mult_compat (p s0)
               (real_opp (real_log (q s0) (Hq s0))) (p s0)
               (real_plus (real_opp (real_log (p s0) (Hp s0)))
                          (real_opp (real_log Rqp Hr)))).
      * apply real_eq_refl.
      * apply (real_eq_trans
                 (real_opp (real_log (q s0) (Hq s0)))
                 (real_opp (real_plus (real_log (p s0) (Hp s0))
                                      (real_log Rqp Hr)))
                 (real_plus (real_opp (real_log (p s0) (Hp s0)))
                            (real_opp (real_log Rqp Hr)))).
        -- exact (RealSetoid.real_eq_opp_compat (real_log (q s0) (Hq s0))
                     (real_plus (real_log (p s0) (Hp s0)) (real_log Rqp Hr))
                     Hlogsplit).
        -- exact (real_opp_plus (real_log (p s0) (Hp s0)) (real_log Rqp Hr)).
    + exact (real_distrib (p s0) (real_opp (real_log (p s0) (Hp s0)))
               (real_opp (real_log Rqp Hr))).
  - exact (real_list_sum_add X
             (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s))))
             (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).
Qed.

(* ============================================================ *)
(* Inventory (results of premise-slot proof series #1):                      *)
(*   gibbsd_lt_add_opp_r / gibbsd_le_b_opp / gibbsd_le_b_id_l /                 *)
(*   gibbsd_minus_flip / gibbsd_le_b_mult_pos_r — the five Bishop-order         *)
(*   algebra primitives (le_b counterparts of the req layer's                   *)
(*   opp_le_compat / le_id_l / req_le_mult_compat_r; the req layer has no       *)
(*   such forms — gap pieces supplied directly by the Bishop-order engine).     *)
(*   gibbsd_p_mult_ratio / gibbsd_p_minus_ratio — two eq-layer identities.      *)
(*   gibbsd_two_pos / gibbsd_half / gibbsd_half_pos / gibbsd_half_sum           *)
(*   + gibbsd_list_sum_le_b / gibbsd_list_sum_minus — six summation-layer       *)
(*   pieces (Bishop counterparts of fsum_le / fsum_minus; by the halved-budget  *)
(*   induction).                                                                *)
(*   gibbsd_gibbs_pointwise_B — the slot-proof position (dist_log_le_linear     *)
(*   supplied directly).                                                        *)
(*   gibbsd_gibbs_inequality — the main deliverable (the four-checkpoint goal). *)
(*   gibbsd_cross_entropy_decomp — the main lemma of the first cascade layer.   *)
(* Notes:                                                                       *)
(*   Note 1: the Bishop-order engine proves what the req layer carries as       *)
(*   Hypothesis slots; the order-direction mismatch prevents direct provision,  *)
(*   so the registered fallback route (Real-instantiation theorems) is executed *)
(*   here in full chain; the gap pieces are the five Bishop-order algebra       *)
(*   primitives plus the Bishop sum monotonicity (this file's Part A/C are      *)
(*   reusable across modules: the log_le_linear/log_lt_mono family has          *)
(*   isomorphic slot-proof gaps).                                               *)
(*   Note 2: the log-inverse cancellation (log(inv p) == −log p) is not         *)
(*   available in the upstream baseline —                                       *)
(*   the kl_term normal form routes around it (the multiplicative log           *)
(*   decomposition closes toward q == p·(q/p) with no cancellation);            *)
(*   bridging the literal p·(log p−log q) form of req_relative_entropy awaits   *)
(*   that cancellation lemma.                                                   *)
(* ============================================================ *)

(* ======== G08_Gibbs member: UpReqHlogZD (merged verbatim, with its own Requires) ======== *)
(* ============================================================ *)
(* UpReqHlogZD.v — premise-slot proof series #4: a constructive proof of the HlogZ slot (the KL projection main theorem) *)
(*                                                              *)
(* Target main theorem: UpReqAlign.req_projected_distribution_minimizes_kl     *)
(*   (the req version of the KL projection; the ReqKLProjection section is      *)
(*   closed; the post-Section export signature was verified against a Check     *)
(*   table in _hzlogd_probe.v).                                                 *)
(*                                                              *)
(* Measured shape of the HlogZ slot (key calibration point):                    *)
(*   le (log (Z_aud_req S sumf post_aud p) HZ) zero                             *)
(*   — this is the upper-bound form of log Z (log Z ≤ 0), not the lower-bound   *)
(*   form lt zero (log Z), and not the per-eps form.  The proof route is        *)
(*   therefore fixed as:                                                        *)
(*   Z_aud ≤ sumf p ([req_Z_aud_le_one]: the pass-set mass is at most the       *)
(*     total mass) == one (normalization [Hp_norm]) ⟹ log Z_aud ≤ log one == 0  *)
(*     (direct from the monotone le form of log; the Id-side proof precedents   *)
(*     are G01_CoreMicro.hlogz_*, and the Real-layer seeds are the upstream     *)
(*     real_log_le_mono / real_log_le_zero_of_le_one).                          *)
(* The original task sketch "Z ≥ max p_i ⟹ a lower bound of log Z" describes a  *)
(*   lower-bound slot route; the measured slot has no such shape: max           *)
(*   extraction does not enter the implementation; the pointwise positivity     *)
(*   witness in the two-state instance is given by hzlogd_HZ_bool (proving the  *)
(*   HZ slot along the way); see the technical report for calibration details.  *)
(*                                                              *)
(* Result inventory (the hzlogd_ prefix is exclusive; grep re-checked zero name *)
(* clashes before writing):                                                     *)
(*   [deliverable] hzlogd_log_le_zero_of_le_one — Z positive + Z ≤ 1 ⟹ log Z ≤ 0 *)
(*           abstract proof (the monotone le slot of log at an explicit         *)
(*           position; Set layer, zero Prop);                                   *)
(*   [T2(2)] hzlogd_discharge_real — the abstract monotone slot supplied        *)
(*           directly by the upstream seed real_log_le_mono: the concrete Real  *)
(*           proof (unconditional closure);                                     *)
(*           hzlogd_discharge_real_direct — the direct-use twin via             *)
(*           real_log_le_zero_of_le_one (the two forms coexist, same goal);     *)
(*   [main 1] hzlogd_proj_min_kl_hlogzfree — abstract HlogZ-free instantiation  *)
(*           of the main theorem: the HlogZ slot is filled by the deliverable;  *)
(*           the honest premise shift = the new sum_le/Hp_norm (the             *)
(*           mathematical source of the Z ≤ 1 route; absent from the main       *)
(*           theorem's original signature);                                     *)
(*   [main 2] hzlogd_proj_min_kl_bool — the bool/Real concrete instance of the  *)
(*           main theorem (S := bool two-state audit, post_aud := id; the HZ    *)
(*           slot is proved along the way by hzlogd_HZ_bool; only the p/q       *)
(*           distribution premises remain, all on the Set layer).               *)
(*                                                              *)
(* Constraints: zero axiom-class tokens; all proofs close by Qed; Set-layer     *)
(* statements (req/lt/le all Set-valued; the post_aud s = false slot of Hqz     *)
(* inherits the main theorem's position); existing files untouched;             *)
(* the two forms coexist.                                                       *)
(* ============================================================ *)

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
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the
   global Real, and the field names below are bound to the global constants. *)
Notation R := Real.
Notation req := real_eq.
Notation req_refl := real_eq_refl.
Notation req_sym := real_eq_sym.
Notation req_trans := real_eq_trans.
Notation zero := real_zero.
Notation one := real_one.
Notation plus := real_plus.
Notation mult := real_mult.
Notation opp := real_opp.
Notation lt := real_lt.
Notation le := real_le.
Notation req_plus_compat := RealSetoid.real_eq_plus_compat_adapt.
Notation req_lt_compat := RealSetoid.real_lt_compat.
Notation plus_assoc := real_plus_assoc.
Notation plus_comm := real_plus_comm.
Notation plus_zero := real_plus_zero.
Notation distrib := real_distrib.
Notation le_id_l := RealSetoid.real_le_id_l.
Notation le_id_r := RealSetoid.real_le_id_r.
Notation one_pos := real_lt_zero_one.
Notation le_plus_compat := real_le_plus_compat.
Notation opp_le_compat := real_opp_le_compat.
Notation log := real_log.
Notation log_one := real_log_one.

(* ============================================================ *)
(* Deliverable: the abstract proof (the monotone le slot of log at an explicit  *)
(*   position; the first link of the main chain)                                *)
(*   Argument: Z ≤ 1 ⟹ log Z ≤ log one (monotone slot) ⟹ log Z ≤ 0             *)
(*   ([log_one] is an interface field: req (log one H) zero, with the right end *)
(*   transported by [le_id_r]).                                                 *)
(* ============================================================ *)
Lemma hzlogd_log_le_zero_of_le_one :
  
    (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
       le x y -> le (log x Hx) (log y Hy)) ->
    forall (Z : R) (HZ : lt zero Z), le Z one -> le (log Z HZ) zero.
Proof.
  intros Hmono Z HZ HZ1.
  apply (le_id_r (log Z HZ) (log one one_pos) zero).
  - exact (log_one one_pos).
  - exact (Hmono Z one HZ one_pos HZ1).
Qed.

(* ============================================================ *)
(*  Template (2): the concrete Real proof (the abstract monotone slot supplied  *)
(*   directly by the upstream seed).                                            *)
(*   [real_log_le_mono] (upstream baseline [L112104] region; dual of            *)
(*   G01_CoreMicro) feeds the single-premise slot;                              *)
(*   the statement-level lt/le/log are delta-equal to real_* via the            *)
(*   [RealEnhancedReal] instance.                                               *)
(* ============================================================ *)
Lemma hzlogd_discharge_real :
  forall (Z : Real) (HZ : lt zero Z), le Z one -> le (log Z HZ) zero.
Proof.
  intros Z HZ HZ1.
  exact (le_id_r (log Z HZ) (log one one_pos) zero
           (log_one one_pos)
           (real_log_le_mono Z one HZ one_pos HZ1)).
Qed.

(* twin form: the direct-use form [real_log_le_zero_of_le_one] (as in          *)
(* G01_CoreMicro) is taken directly, coinciding in result with the lemma above  *)
(* (the same statement proved by two routes, as G01_CoreMicro does).            *)
Lemma hzlogd_discharge_real_direct :
  forall (Z : Real) (HZ : lt zero Z), le Z one -> le (log Z HZ) zero.
Proof.
  intros Z HZ HZ1.
  exact (real_log_le_zero_of_le_one Z HZ HZ1).
Qed.

(* ============================================================ *)
(* Main 1: abstract HlogZ-free instantiation of the main theorem                *)
(*   The post-Section signature of the main theorem (verified table) =          *)
(*   S sumf + sum_ext/add/linear + log_req_compat + post_aud p Hp_pos HZ +      *)
(*   q Hq Hqn Hqz + HlogZ.                                                      *)
(*   This lemma: the HlogZ slot is filled by the deliverable; the new entries   *)
(*   sum_le/Hp_norm are added (the source of the Z ≤ 1 route:                   *)
(*   [req_Z_aud_le_one] needs sum_le; transporting the right end needs          *)
(*   Hp_norm) — an honest premise shift; the main theorem's original signature  *)
(*   contains neither.                                                          *)
(* ============================================================ *)
Lemma hzlogd_proj_min_kl_hlogzfree :
  forall  (S : Set)
         (sumf : (S -> R) -> R)
         (sum_ext : forall f g : S -> R,
            (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (sum_add : forall f g : S -> R,
            req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (sum_linear : forall (a : R) (f : S -> R),
            req (sumf (fun s => mult a (f s))) (mult a (sumf f)))
         (sum_le : forall f g : S -> R,
            (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
         (log_req_compat : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
            req x y -> req (log x Hx) (log y Hy))
         (post_aud : S -> bool) (p : S -> R)
         (Hp_norm : req (sumf p) one)
         (Hp_pos : forall s : S, lt zero (p s))
         (HZ : lt zero (Z_aud_req S sumf post_aud p))
         (Hmono : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
            le x y -> le (log x Hx) (log y Hy))
         (q : S -> R) (Hq : forall s : S, lt zero (q s))
         (Hqn : req (sumf q) one)
         (Hqz : forall s : S, post_aud s = false -> req (q s) zero),
    le (sumf (fun s =>
           kl_proj_closed S sumf post_aud p Hp_pos HZ q Hq s))
       (sumf (fun s =>
           mult (q s)
                (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))).
Proof.
  intros S sumf sum_ext sum_add sum_linear sum_le log_req_compat
         post_aud p Hp_norm Hp_pos HZ Hmono q Hq Hqn Hqz.
  apply (req_projected_distribution_minimizes_kl S sumf sum_ext sum_add
           sum_linear log_req_compat post_aud p Hp_pos HZ q Hq Hqn Hqz).
  (* HlogZ slot assembled in place: the intermediate stop [log one] of *)
  (* @[le_id_r] + the right end transported by [log_one] + the monotone leg *)
  (* [Hmono], with the Z_aud ≤ one tail leg inlined into the fifth argument of *)
  (* the monotone leg (no detour through the deliverable lemma) *)
  apply (le_id_r (log (Z_aud_req S sumf post_aud p) HZ)
           (log one one_pos) zero).
  - exact (log_one one_pos).
  - exact (Hmono (Z_aud_req S sumf post_aud p) one HZ one_pos
             (le_id_r (Z_aud_req S sumf post_aud p) (sumf p) one
                Hp_norm
                (req_Z_aud_le_one S sumf sum_le post_aud p Hp_pos))).
Qed.

(* ============================================================ *)
(* Foundation of Main 2: the bool/Real two-state finite sum (the S := bool      *)
(*   two-state audit instance).                                                 *)
(*   sumf := plus (f true) (f false); the four sum premises + [log_req_compat]  *)
(*   are all proved inside this file (closed on the Real layer, zero new        *)
(*   premises).                                                                 *)
(* ============================================================ *)
Definition hzlogd_aud_sum (f : bool -> Real) : Real := plus (f true) (f false).

Lemma hzlogd_sum2_ext :
  forall f g : bool -> Real,
    (forall s : bool, req (f s) (g s)) ->
    req (hzlogd_aud_sum f) (hzlogd_aud_sum g).
Proof.
  intros f g H. unfold hzlogd_aud_sum.
  exact (req_plus_compat (f true) (g true) (f false) (g false)
           (H true) (H false)).
Qed.

Lemma hzlogd_sum2_add :
  forall f g : bool -> Real,
    req (hzlogd_aud_sum (fun s => plus (f s) (g s)))
        (plus (hzlogd_aud_sum f) (hzlogd_aud_sum g)).
Proof.
  intros f g. unfold hzlogd_aud_sum.
  apply (req_trans (plus (plus (f true) (g true)) (plus (f false) (g false)))
                   (plus (f true) (plus (g true) (plus (f false) (g false))))
                   (plus (plus (f true) (f false)) (plus (g true) (g false)))).
  - (* step 1: (a+b)+(c+d) -> a+(b+(c+d)) (assoc, reversed) *)
    apply (req_sym (plus (f true) (plus (g true) (plus (f false) (g false))))
                   (plus (plus (f true) (g true)) (plus (f false) (g false)))
                   (plus_assoc (f true) (g true) (plus (f false) (g false)))).
  - apply (req_trans (plus (f true) (plus (g true) (plus (f false) (g false))))
                     (plus (f true) (plus (plus (g true) (f false)) (g false)))
                     (plus (plus (f true) (f false)) (plus (g true) (g false)))).
    + (* step 2: b+(c+d) -> (b+c)+d (assoc, forward) *)
      apply (req_plus_compat (f true) (f true)
               (plus (g true) (plus (f false) (g false)))
               (plus (plus (g true) (f false)) (g false))).
      * apply req_refl.
      * apply plus_assoc.
    + apply (req_trans (plus (f true) (plus (plus (g true) (f false)) (g false)))
                       (plus (f true) (plus (plus (f false) (g true)) (g false)))
                       (plus (plus (f true) (f false)) (plus (g true) (g false)))).
      * (* step 3: (b+c)+d -> (c+b)+d (comm on the middle pair) *)
        apply (req_plus_compat (f true) (f true)
                 (plus (plus (g true) (f false)) (g false))
                 (plus (plus (f false) (g true)) (g false))).
        -- apply req_refl.
        -- apply (req_plus_compat (plus (g true) (f false))
                     (plus (f false) (g true)) (g false) (g false)).
           ++ apply plus_comm.
           ++ apply req_refl.
      * apply (req_trans (plus (f true) (plus (plus (f false) (g true)) (g false)))
                         (plus (f true) (plus (f false) (plus (g true) (g false))))
                         (plus (plus (f true) (f false)) (plus (g true) (g false)))).
        -- (* step 4: (c+b)+d -> c+(b+d) (assoc, reversed) *)
           apply (req_plus_compat (f true) (f true)
                    (plus (plus (f false) (g true)) (g false))
                    (plus (f false) (plus (g true) (g false)))).
           ++ apply req_refl.
           ++ apply (req_sym (plus (f false) (plus (g true) (g false)))
                             (plus (plus (f false) (g true)) (g false))
                             (plus_assoc (f false) (g true) (g false))).
        -- (* step 5: a+(c+(b+d)) -> (a+c)+(b+d) (assoc, forward, closing) *)
           apply plus_assoc.
Qed.

Lemma hzlogd_sum2_linear :
  forall (a : Real) (f : bool -> Real),
    req (hzlogd_aud_sum (fun s => mult a (f s))) (mult a (hzlogd_aud_sum f)).
Proof.
  intros a f. unfold hzlogd_aud_sum.
  apply (req_sym (mult a (plus (f true) (f false)))
                 (plus (mult a (f true)) (mult a (f false)))).
  apply distrib.
Qed.

Lemma hzlogd_sum2_le :
  forall f g : bool -> Real,
    (forall s : bool, le (f s) (g s)) ->
    le (hzlogd_aud_sum f) (hzlogd_aud_sum g).
Proof.
  intros f g H. unfold hzlogd_aud_sum.
  exact (le_plus_compat (f true) (g true) (f false) (g false)
           (H true) (H false)).
Qed.

(* instance of the log compatibility face (direct use of [real_log_wd]; the same-position closing lemma as in [UpReqU2]) *)
Lemma hzlogd_log_req_compat_real :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (real_log_wd x y Hx Hy Hxy).
Qed.

(* ============================================================ *)
(* Proof of the HZ slot (the two-state pointwise-witness provider): at the      *)
(* pass point true, p positive ⟹                                               *)
(* Z_aud = plus (p true) zero > 0 (iota reduction + transport by [plus_zero]).  *)
(* In the two-state space the max term is the pass point itself; no max         *)
(* selector is needed.                                                          *)
(* ============================================================ *)
Lemma hzlogd_HZ_bool :
  forall p : bool -> Real,
    lt zero (p true) ->
    lt zero (Z_aud_req bool hzlogd_aud_sum
               (fun b : bool => b) p).
Proof.
  intros p Hp.
  apply (req_lt_compat zero zero (p true)
           (Z_aud_req bool hzlogd_aud_sum
              (fun b : bool => b) p)).
  - apply req_refl.
  - exact (req_sym (Z_aud_req bool hzlogd_aud_sum
                      (fun b : bool => b) p)
                   (p true)
                   (req_trans (Z_aud_req bool
                                 hzlogd_aud_sum (fun b : bool => b) p)
                              (plus (p true) zero) (p true)
                              (req_refl (Z_aud_req bool
                                           hzlogd_aud_sum
                                           (fun b : bool => b) p))
                              (plus_zero (p true)))).
  - exact Hp.
Qed.

(* ============================================================ *)
(* Main 2: the bool/Real concrete instance of the main theorem (the HlogZ slot  *)
(*   filled by the Template-(2) proof lemma).                                   *)
(*   post_aud := fun b => b (the audit set is {true}); all four sum premises    *)
(*   proved;                                                                    *)
(*   the HZ slot proved by [hzlogd_HZ_bool] (the statement is inlined rather    *)
(*   than introduced by an opaque assert);                                      *)
(*   the HlogZ slot proved by [hzlogd_discharge_real] (Z_aud ≤ one via          *)
(*   [req_Z_aud_le_one] + [Hp_norm], the same route);                           *)
(*   the remaining premises are only the p/q distribution shapes (Set layer:    *)
(*   real_eq/real_lt carriers).                                                 *)
(* ============================================================ *)
Theorem hzlogd_proj_min_kl_bool :
  forall (p : bool -> Real)
         (Hp_norm : req (hzlogd_aud_sum p) one)
         (Hp_pos : forall s : bool, lt zero (p s))
         (q : bool -> Real) (Hq : forall s : bool, lt zero (q s))
         (Hqn : req (hzlogd_aud_sum q) one)
         (Hqz : forall s : bool,
            (fun b : bool => b) s = false -> req (q s) zero),
    le (hzlogd_aud_sum (fun s =>
          kl_proj_closed bool hzlogd_aud_sum
              (fun b : bool => b) p Hp_pos
              (hzlogd_HZ_bool p (Hp_pos true)) q Hq s))
       (hzlogd_aud_sum (fun s =>
          mult (q s)
               (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))).
Proof.
  intros p Hp_norm Hp_pos q Hq Hqn Hqz.
  apply (req_projected_distribution_minimizes_kl bool
           hzlogd_aud_sum hzlogd_sum2_ext hzlogd_sum2_add hzlogd_sum2_linear
           hzlogd_log_req_compat_real (fun b : bool => b) p Hp_pos
           (hzlogd_HZ_bool p (Hp_pos true)) q Hq Hqn Hqz).
  (* HlogZ slot assembled in place: the intermediate stop [log one] of *)
  (* @[le_id_r] + [log_one] + the monotone leg [real_log_le_mono], with the *)
  (* Z_aud ≤ one tail leg inlined into the fifth argument of the monotone leg *)
  (* (no detour through the discharge lemma) *)
  apply (le_id_r
           (log (Z_aud_req bool hzlogd_aud_sum
                  (fun b : bool => b) p)
               (hzlogd_HZ_bool p (Hp_pos true)))
           (log one one_pos) zero).
  - exact (log_one one_pos).
  - exact (real_log_le_mono
             (Z_aud_req bool hzlogd_aud_sum
                (fun b : bool => b) p)
             one (hzlogd_HZ_bool p (Hp_pos true)) one_pos
             (le_id_r
                 (Z_aud_req bool hzlogd_aud_sum
                    (fun b : bool => b) p)
                 (hzlogd_aud_sum p) one Hp_norm
                 (req_Z_aud_le_one bool hzlogd_aud_sum
                    hzlogd_sum2_le (fun b : bool => b) p Hp_pos))).
Qed.

(* ============================================================ *)
(* Extraction check + Print Assumptions (closure verification of the new        *)
(* statements)                                                                  *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Warnings "-extraction-opaque-accessed".
Set Extraction Output Directory ".".
Extraction "upreqhlogzd_core.ml" hzlogd_log_le_zero_of_le_one
  hzlogd_proj_min_kl_hlogzfree.
Extraction "upreqhlogzd_real.ml" hzlogd_discharge_real
  hzlogd_discharge_real_direct hzlogd_HZ_bool hzlogd_proj_min_kl_bool.

Print Assumptions hzlogd_log_le_zero_of_le_one.
Print Assumptions hzlogd_discharge_real.
Print Assumptions hzlogd_discharge_real_direct.
Print Assumptions hzlogd_proj_min_kl_hlogzfree.
Print Assumptions hzlogd_HZ_bool.
Print Assumptions hzlogd_proj_min_kl_bool.

(* ============================================================ *)
(* Closure record (appended after the build):                                   *)
(*   Qed count: 11 = deliverable 1 + the two discharge forms 2 + main 1 +       *)
(*   the four sum foundations + log compatibility 1 +                           *)
(*   the HZ proof 1 + main 2.                                                   *)
(*   Zero banned tokens; both extraction tracks (core/real) succeed with all    *)
(*   PA outputs Closed;                                                         *)
(*   [coqchk] reports "Modules were successfully checked".                      *)
(* ============================================================ *)

(* ======== G08_Gibbs member: UpReqGibbsE2 (merged verbatim, with its own Requires) ======== *)
(* ============================================================ *)
(* UpReqGibbsE2.v — relocated module of premise-slot proof series #2: the    *)
(*   finite concrete route for gibbs_equality                                   *)
(*   (the upstream draft UpReqGibbsE.v with the abstract Or shape was blocked   *)
(*   at verdict; this file does not touch that draft;                           *)
(*   the gibbe2_ prefix is unique library-wide against name clashes; grep       *)
(*   measured zero hits before writing).                                        *)
(* ------------------------------------------------------------------ *)
(* Reconnaissance conclusions (from direct reading):                            *)
(*   1. per-item clamping to zero is feasible: real_eq/real_lt are Set-valued   *)
(*      per-eps forms (upstream baseline:3448/3517),                            *)
(*      and real_list_sum_pos (root [L41660] region) backs the direction "each  *)
(*      item positive ⟹ sum positive";                                          *)
(*      the converse "sum zero ⟹ each item zero" goes through the antisymmetry  *)
(*      of le_b (missing in the baseline) and is closed inside this file.       *)
(*   2. the log engine: real_log_le_mono (G01_CoreMicro L24; the lt branch      *)
(*      real_log_lt_mono is proved in the baseline — strict monotonicity is in  *)
(*      the library); a log injectivity/eq-linear bridge module is missing —    *)
(*      the upstream baseline [L41224] states the honest boundary explicitly:   *)
(*      "log_eq_linear needs strong trichotomy/LPO and is not provable          *)
(*      constructively".  Measured: the main lemma's closure does need that     *)
(*      bridge.                                                                 *)
(*   3. the swap derivation at the two cut points is rejected: per-item         *)
(*      clamping gives log u_s == u_s − 1 for each s,                           *)
(*      but the reciprocity u_1·u_2 == 1 fails for general distributions        *)
(*      (normalization does not create reciprocity),                            *)
(*      and a finite concrete carrier cannot bypass the eq-linear bridge        *)
(*      either — the adjacency question remains an open item of this series.    *)
(* ------------------------------------------------------------------ *)
(* Deliverables (graded):                                                       *)
(*   [deliverable 1 · per-item clamp family] gibbe2_le_b_antisym (the core new  *)
(*     lemma, built per n, zero Or closure, zero LPO, zero trichotomy);         *)
(*     gibbe2_clamp_head / _r;                                                  *)
(*     gibbe2_list_sum_zero_extract_bool (extraction over the finite concrete   *)
(*     carrier [true;false]).                                                   *)
(*   [deliverable 2 · log relation lemmas] gibbe2_kl_eq_of_w_zero +             *)
(*     gibbe2_tangent_eq + gibbe2_kl_zero_tangent_eq: KL==0 ⟹ pointwise        *)
(*     tangent equality log(q_s/p_s) == q_s/p_s − 1 (unconditional on the Real  *)
(*     layer — the first such lemma in the library).                            *)
(*   [main · bridge-injected proof lemma] gibbe2_gibbs_equality_bool: KL==0 ⟹  *)
(*     pointwise tangent equality ⟹ (eq-linear bridge injected explicitly) ⟹   *)
(*     pointwise p==q.  The bridge is unprovable unconditionally (the           *)
(*     [L41224] verdict; the upstream exp-copy draft belongs to the blocked     *)
(*     zone and is untouched here), so it is proved with an explicit premise    *)
(*     by the fallback plan — the Real-instantiation gap of the req-layer       *)
(*     dist_log_eq_linear (UpReqDist:1031 Hypothesis) is reported as is.        *)
(* Constraints: Set layer with zero Prop (statement order/equality all          *)
(*   Set-valued real_eq/real_lt/real_le_b; zero Or closure, zero trichotomy,    *)
(*   zero LPO); all proofs close by Qed; zero axioms; existing files untouched; *)
(*   the old UpReqGibbsE.v untouched (no .vo, cannot be Required, unused).      *)
(* ============================================================ *)

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

From Stdlib Require Import List QArith.QArith QArith.Qabs QArith.Qround
               Arith.Arith.
From Stdlib Require Import Lia.
Import ListNotations.

(* ============================================================ *)
(* Part A. Q-layer halving helpers                                              *)
(* ============================================================ *)

Lemma gibbe2_Q_half_pos : forall eps : Q, QltT 0 eps -> QltT 0 (eps * (1#2))%Q.
Proof.
  intros eps Heps. apply Qlt_to_QltT. apply (Qmult_lt_0_compat eps (1#2)).
  - apply QltT_to_Qlt. exact Heps.
  - reflexivity.
Qed.

Lemma gibbe2_Q_half_lt : forall eps : Q, QltT 0 eps -> QltT (eps * (1#2))%Q eps.
Proof.
  intros eps Heps.
  assert (H1 : Qlt ((1#2) * eps) (1 * eps)).
  { apply (Qmult_lt_compat_r (1#2) 1 eps).
    - apply QltT_to_Qlt. exact Heps.
    - reflexivity. }
  rewrite Qmult_1_l in H1.
  rewrite (Qmult_comm (1#2) eps) in H1.
  apply Qlt_to_QltT. exact H1.
Qed.

(* ============================================================ *)
(* Part B. The complementary le_b order machinery                               *)
(* ============================================================ *)

(* B1: real_eq transport of the right end of le_b *)
Lemma gibbe2_le_b_id_r : forall a b c : Real,
  real_le_b a b -> real_eq b c -> real_le_b a c.
Proof.
  intros a b c H Hbc eps Heps. unfold real_le_b in H.
  exact (real_lt_eq_lt a (real_plus b eps) (real_plus c eps) (H eps Heps)
           (RealSetoid.real_eq_plus_compat b eps c eps Hbc (real_eq_refl eps))).
Qed.

(* B2: right-addition translation for le_b *)
Lemma gibbe2_le_b_translate_r : forall x y z : Real,
  real_le_b x y -> real_le_b (real_plus x z) (real_plus y z).
Proof.
  intros x y z H eps Heps. unfold real_le_b in H.
  apply (RealSetoid.real_lt_compat (real_plus z x) (real_plus x z)
           (real_plus z (real_plus y eps)) (real_plus (real_plus y z) eps)).
  - apply real_plus_comm.
  - apply (real_eq_trans _ (real_plus (real_plus z y) eps) _).
    + apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat (real_plus z y) eps
               (real_plus y z) eps
               (real_plus_comm z y) (real_eq_refl eps)).
  - exact (real_lt_plus_translate z x (real_plus y eps) (H eps Heps)).
Qed.

(* B3: le_b a b ⟹ le_b 0 (b−a) *)
Lemma gibbe2_le_b_nonneg_diff : forall a b : Real,
  real_le_b a b -> real_le_b real_zero (real_plus b (real_opp a)).
Proof.
  intros a b H eps Heps. unfold real_le_b in H.
  apply (RealSetoid.real_lt_compat (real_plus (real_opp a) a)
           real_zero
           (real_plus (real_opp a) (real_plus b eps))
           (real_plus (real_plus b (real_opp a)) eps)).
  - apply (real_eq_trans _ (real_plus a (real_opp a)) _).
    + apply real_plus_comm.
    + exact (real_plus_opp a).
  - apply (real_eq_trans _ (real_plus (real_plus (real_opp a) b) eps) _).
    + apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp a) b) eps
               (real_plus b (real_opp a)) eps
               (real_plus_comm (real_opp a) b) (real_eq_refl eps)).
  - exact (real_lt_plus_translate (real_opp a) a (real_plus b eps) (H eps Heps)).
Qed.

(* B4 [core new lemma]: antisymmetry of the Bishop order le_b (built per n;    *)
(* zero Or closure, zero LPO) *)
Lemma gibbe2_le_b_antisym : forall a b : Real,
  real_le_b a b -> real_le_b b a -> real_eq a b.
Proof.
  intros a b H1 H2 eps Heps.
  assert (He2pos : real_lt real_zero (real_const (eps * (1#2))%Q))
    by (apply real_const_pos; apply gibbe2_Q_half_pos; exact Heps).
  assert (Hhe : Qlt (eps * (1#2))%Q eps)
    by (apply QltT_to_Qlt; apply gibbe2_Q_half_lt; exact Heps).
  destruct (H1 _ He2pos) as [g1 [Hg1pos [N1 HN1]]].
  destruct (H2 _ He2pos) as [g2 [Hg2pos [N2 HN2]]].
  exists (max N1 N2).
  intros n Hn.
  assert (Hn1 : NatLe N1 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
  assert (Hn2 : NatLe N2 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
  specialize (HN1 n Hn1). specialize (HN2 n Hn2).
  apply QltT_to_Qlt in HN1. apply QltT_to_Qlt in HN2.
  assert (Hp1 : forall k : nat,
           projT1 (real_plus b (real_const (eps * (1#2))%Q)) k
           == projT1 b k + projT1 (real_const (eps * (1#2))%Q) k)
    by (intro k; apply qeqT_imp_qeq; apply real_plus_proj).
  assert (Hp2 : forall k : nat,
           projT1 (real_plus a (real_const (eps * (1#2))%Q)) k
           == projT1 a k + projT1 (real_const (eps * (1#2))%Q) k)
    by (intro k; apply qeqT_imp_qeq; apply real_plus_proj).
  assert (Hcst : forall (c : Q) (k : nat), projT1 (real_const c) k == c)
    by (intros c k; apply qeqT_imp_qeq; apply real_const_proj).
  rewrite (Hp1 n) in HN1. rewrite (Hcst (eps * (1#2))%Q n) in HN1.
  rewrite (Hp2 n) in HN2. rewrite (Hcst (eps * (1#2))%Q n) in HN2.
  set (x := projT1 a n - projT1 b n).
  set (h := (eps * (1#2))%Q).
  assert (Hg1q : 0 < g1) by (apply QltT_to_Qlt; exact Hg1pos).
  assert (Hg2q : 0 < g2) by (apply QltT_to_Qlt; exact Hg2pos).
  (* Upper side: x < h where x is a n - b n (ring normalization plus lia). *)
  assert (Hstep1 : projT1 a n - projT1 b n + g1
                   < projT1 a n - projT1 b n
                     + (projT1 b n + eps * (1#2) - projT1 a n)).
  { exact (proj2 (Qplus_lt_r g1 (projT1 b n + eps * (1#2) - projT1 a n)
                   (projT1 a n - projT1 b n)) HN1). }
  assert (Hring1 : projT1 a n - projT1 b n
                   + (projT1 b n + eps * (1#2) - projT1 a n)
                   == eps * (1#2)) by ring.
  rewrite Hring1 in Hstep1.
  assert (Hub : projT1 a n - projT1 b n < eps * (1#2)).
  { apply (Qle_lt_trans _ (projT1 a n - projT1 b n + g1) _).
    - rewrite <- (Qplus_0_r (projT1 a n - projT1 b n)) at 1.
      apply (proj2 (Qplus_le_r 0 g1 (projT1 a n - projT1 b n))).
      exact (QleT'_to_Qle _ _ (b5dH_q_pos_le g1 Hg1pos)).
    - exact Hstep1. }
  (* Lower side: -x < h. *)
  assert (Hstep2 : - (projT1 a n - projT1 b n) + g2
                   < - (projT1 a n - projT1 b n)
                     + (projT1 a n + eps * (1#2) - projT1 b n)).
  { exact (proj2 (Qplus_lt_r g2 (projT1 a n + eps * (1#2) - projT1 b n)
                   (- (projT1 a n - projT1 b n))%Q) HN2). }
  assert (Hring2 : - (projT1 a n - projT1 b n)
                   + (projT1 a n + eps * (1#2) - projT1 b n)
                   == eps * (1#2)) by ring.
  rewrite Hring2 in Hstep2.
  assert (Hdn : (- (projT1 a n - projT1 b n))%Q < eps * (1#2)).
  { apply (Qle_lt_trans _ ((- (projT1 a n - projT1 b n))%Q + g2) _).
    - rewrite <- (Qplus_0_r (- (projT1 a n - projT1 b n))%Q) at 1.
      apply (proj2 (Qplus_le_r 0 g2 (- (projT1 a n - projT1 b n))%Q)).
      exact (QleT'_to_Qle _ _ (b5dH_q_pos_le g2 Hg2pos)).
    - exact Hstep2. }
  (* Final step: the absolute value of x is below eps (two sign cases, decidable over Q, no trichotomy). *)
  unfold x, h.
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec 0 (projT1 a n - projT1 b n)) as [Hsx | Hsx].
  - rewrite (Qabs_pos (projT1 a n - projT1 b n) (Qlt_le_weak _ _ Hsx)).
    apply (Qlt_le_trans _ (eps * (1#2)) eps Hub).
    exact (Qlt_le_weak _ _ Hhe).
  - rewrite (Qabs_neg (projT1 a n - projT1 b n) Hsx).
    apply (Qlt_le_trans (- (projT1 a n - projT1 b n))%Q (eps * (1#2)) eps Hdn).
    exact (Qlt_le_weak _ _ Hhe).
Qed.

(* ============================================================ *)
(* Part C. Deliverable 1: the per-item clamp family                             *)
(* ============================================================ *)

(* C1: a two-term zero sum ⟹ the first term is zero *)
Lemma gibbe2_clamp_head : forall a b : Real,
  real_le_b real_zero a -> real_le_b real_zero b ->
  real_eq (real_plus a b) real_zero -> real_eq real_zero a.
Proof.
  intros a b Ha Hb Hsum.
  apply (gibbe2_le_b_antisym real_zero a Ha).
  apply (gibbe2_le_b_id_r a (real_plus b a) real_zero).
  - apply (gibbsd_le_b_id_l a (real_plus real_zero a) (real_plus b a)
             (real_eq_trans a (real_plus a real_zero) (real_plus real_zero a)
                (real_eq_sym _ _ (real_plus_zero a)) (real_plus_comm a real_zero))
             (gibbe2_le_b_translate_r real_zero b a Hb)).
  - apply (real_eq_trans (real_plus b a) (real_plus a b) real_zero
             (real_plus_comm b a) Hsum).
Qed.

(* C2: a two-term zero sum ⟹ the second term is zero (comm dual) *)
Lemma gibbe2_clamp_head_r : forall a b : Real,
  real_le_b real_zero a -> real_le_b real_zero b ->
  real_eq (real_plus a b) real_zero -> real_eq real_zero b.
Proof.
  intros a b Ha Hb Hsum.
  apply (gibbe2_clamp_head b a Hb Ha).
  apply (real_eq_trans _ (real_plus a b) _).
  - apply real_plus_comm.
  - exact Hsum.
Qed.

(* C3 [Deliverable 1 main lemma]: per-item extraction from a zero sum over the finite concrete carrier [true;false] *)
Lemma gibbe2_list_sum_zero_extract_bool :
  forall (f : bool -> Real),
    (forall s : bool, real_le_b real_zero (f s)) ->
    real_eq (real_list_sum bool f [true; false]) real_zero ->
    forall s : bool, real_eq real_zero (f s).
Proof.
  intros f Hpt Hsum s. destruct s; simpl in Hsum.
  - exact (gibbe2_clamp_head (f true) (real_plus (f false) real_zero)
             (Hpt true)
             (gibbe2_le_b_id_r real_zero (f false)
                (real_plus (f false) real_zero)
                (Hpt false) (real_eq_sym _ _ (real_plus_zero (f false))))
             Hsum).
  - apply (real_eq_trans real_zero (real_plus (f false) real_zero) (f false)).
    + exact (gibbe2_clamp_head_r (f true) (real_plus (f false) real_zero)
               (Hpt true)
               (gibbe2_le_b_id_r real_zero (f false)
                  (real_plus (f false) real_zero)
                  (Hpt false) (real_eq_sym _ _ (real_plus_zero (f false))))
               Hsum).
    + exact (real_plus_zero (f false)).
Qed.

(* ============================================================ *)
(* Part D. Deliverable 2: log relation lemmas (KL==0 ⟹ pointwise tangent       *)
(* equality)                                                                    *)
(* ============================================================ *)

(* D0: a zero sum ⟹ term identity *)
Lemma gibbe2_kl_eq_of_w_zero : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_plus (real_kl_term p q Hp Hq)
                     (real_opp (real_plus p (real_opp q)))) real_zero ->
  real_eq (real_kl_term p q Hp Hq) (real_plus p (real_opp q)).
Proof.
  intros p q Hp Hq H.
  set (X := real_plus p (real_opp q)).
  set (K := real_kl_term p q Hp Hq).
  set (NX := real_opp X).
  (* kl == (kl + −X) + X *)
  apply (real_eq_trans K (real_plus (real_plus K NX) X) X).
  - apply (real_eq_trans K (real_plus K real_zero) (real_plus (real_plus K NX) X)).
    + exact (real_eq_sym (real_plus K real_zero) K (real_plus_zero K)).
    + apply (real_eq_trans (real_plus K real_zero)
               (real_plus K (real_plus NX X))
               (real_plus (real_plus K NX) X)).
      * apply (RealSetoid.real_eq_plus_compat K real_zero K
                 (real_plus NX X)
                 (real_eq_refl K)
                 (real_eq_trans real_zero (real_plus X NX) (real_plus NX X)
                    (real_eq_sym (real_plus X NX) real_zero (real_plus_opp X))
                    (real_plus_comm X NX))).
      * exact (real_plus_assoc K NX X).
  - (* (kl + −X) + X == 0 + X == X *)
    apply (real_eq_trans (real_plus (real_plus K NX) X)
             (real_plus real_zero X) X).
    + exact (RealSetoid.real_eq_plus_compat (real_plus K NX) X real_zero X
               H (real_eq_refl X)).
    + apply (real_eq_trans (real_plus real_zero X)
               (real_plus X real_zero) X
               (real_plus_comm real_zero X)
               (real_plus_zero X)).
Qed.

(* D1: tangent-equality shape: kl == p−q ⟹ log(q/p) == q/p − 1 *)
Lemma gibbe2_tangent_eq : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_kl_term p q Hp Hq) (real_plus p (real_opp q)) ->
  real_eq (real_log (real_mult q (real_inv_pos p Hp))
                    (real_mult_positive q (real_inv_pos p Hp) Hq
                       (real_inv_pos_pos p Hp)))
          (real_plus (real_mult q (real_inv_pos p Hp))
                     (real_opp real_one)).
Proof.
  intros p q Hp Hq H.
  set (u := real_mult q (real_inv_pos p Hp)).
  set (Hu := real_mult_positive q (real_inv_pos p Hp) Hq
               (real_inv_pos_pos p Hp)).
  set (L := real_log u Hu).
  (* H : p·(−L) == p + −q *)
  (* step 1: p·L == q + −p (opp on both sides) *)
  assert (Hs1 : real_eq (real_mult p L) (real_plus q (real_opp p))).
  { apply (real_eq_trans (real_mult p L)
             (real_opp (real_mult p (real_opp L)))
             (real_plus q (real_opp p))).
    - apply (real_eq_sym (real_opp (real_mult p (real_opp L)))
               (real_mult p L)
               (real_eq_trans (real_opp (real_mult p (real_opp L)))
                  (real_mult p (real_opp (real_opp L)))
                  (real_mult p L)
                  (real_opp_mult p (real_opp L))
                  (RealSetoid.real_eq_mult_compat p
                     (real_opp (real_opp L)) p L
                     (real_eq_refl p) (real_opp_opp L)))).
    - apply (real_eq_trans (real_opp (real_mult p (real_opp L)))
               (real_opp (real_plus p (real_opp q)))
               (real_plus q (real_opp p))
               (RealSetoid.real_eq_opp_compat (real_mult p (real_opp L))
                  (real_plus p (real_opp q)) H)
               (gibbsd_minus_flip p q)).
  }
  (* step 2: L == (q−p)·inv p *)
  assert (Hs2 : real_eq L (real_mult (real_plus q (real_opp p))
                                        (real_inv_pos p Hp))).
  { apply (real_eq_trans L
             (real_mult (real_mult p L) (real_inv_pos p Hp))
             (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))).
    - apply (real_eq_trans L (real_mult L real_one)
               (real_mult (real_mult p L) (real_inv_pos p Hp))).
      + apply (real_eq_sym (real_mult L real_one) L (real_mult_one L)).
      + apply (real_eq_trans (real_mult L real_one)
                 (real_mult L (real_mult p (real_inv_pos p Hp)))
                 (real_mult (real_mult p L) (real_inv_pos p Hp))).
        * apply (RealSetoid.real_eq_mult_compat L real_one
                   L (real_mult p (real_inv_pos p Hp))
                   (real_eq_refl L)
                   (real_eq_sym (real_mult p (real_inv_pos p Hp)) real_one
                      (real_inv_pos_correct p Hp))).
        * apply (real_eq_trans
                   (real_mult L (real_mult p (real_inv_pos p Hp)))
                   (real_mult (real_mult L p) (real_inv_pos p Hp))
                   (real_mult (real_mult p L) (real_inv_pos p Hp))).
          -- exact (real_mult_assoc L p (real_inv_pos p Hp)).
          -- apply (RealSetoid.real_eq_mult_compat (real_mult L p)
                     (real_inv_pos p Hp) (real_mult p L) (real_inv_pos p Hp)
                     (real_mult_comm L p) (real_eq_refl _)).
    - apply (RealSetoid.real_eq_mult_compat (real_mult p L)
               (real_inv_pos p Hp) (real_plus q (real_opp p))
               (real_inv_pos p Hp) Hs1 (real_eq_refl _)).
  }
  (* step 3: (q−p)·inv p == q·inv p + −1 == u + −1 *)
  assert (Hs3 : real_eq (real_mult (real_plus q (real_opp p))
                                   (real_inv_pos p Hp))
                        (real_plus u (real_opp real_one))).
  { apply (real_eq_trans
             (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))
             (real_plus (real_mult (real_inv_pos p Hp) q)
                        (real_mult (real_inv_pos p Hp) (real_opp p)))
             (real_plus u (real_opp real_one))).
    - apply (real_eq_trans
               (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))
               (real_mult (real_inv_pos p Hp) (real_plus q (real_opp p)))
               (real_plus (real_mult (real_inv_pos p Hp) q)
                          (real_mult (real_inv_pos p Hp) (real_opp p)))).
      + apply (real_mult_comm (real_plus q (real_opp p)) (real_inv_pos p Hp)).
      + exact (real_distrib (real_inv_pos p Hp) q (real_opp p)).
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult (real_inv_pos p Hp) q)
               (real_mult (real_inv_pos p Hp) (real_opp p))
               (real_mult q (real_inv_pos p Hp)) (real_opp real_one)).
      + apply (real_mult_comm (real_inv_pos p Hp) q).
      + apply (real_eq_trans (real_mult (real_inv_pos p Hp) (real_opp p))
                   (real_opp (real_mult (real_inv_pos p Hp) p))
                   (real_opp real_one)).
        * apply (real_eq_sym _ _ (real_opp_mult (real_inv_pos p Hp) p)).
        * apply (RealSetoid.real_eq_opp_compat
                   (real_mult (real_inv_pos p Hp) p) real_one).
          apply (real_eq_trans (real_mult (real_inv_pos p Hp) p)
                     (real_mult p (real_inv_pos p Hp)) real_one).
          -- apply (real_mult_comm (real_inv_pos p Hp) p).
          -- exact (real_inv_pos_correct p Hp).
  }
  exact (real_eq_trans L _ _ Hs2 Hs3).
Qed.

(* D2 [Deliverable 2 main lemma]: KL==0 ⟹ the pointwise tangent equality      *)
(* log(q_s/p_s) == q_s/p_s − 1 *)
Lemma gibbe2_kl_zero_tangent_eq :
  forall (p q : bool -> Real)
    (Hp : forall s : bool, real_lt real_zero (p s))
    (Hq : forall s : bool, real_lt real_zero (q s))
    (Hnp : real_eq (real_list_sum bool p [true; false]) real_one)
    (Hnq : real_eq (real_list_sum bool q [true; false]) real_one),
  real_eq (real_list_sum bool
             (fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s))
             [true; false])
          real_zero ->
  forall s : bool,
    real_eq (real_log (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                      (real_mult_positive (q s) (real_inv_pos (p s) (Hp s))
                         (Hq s) (real_inv_pos_pos (p s) (Hp s))))
            (real_plus (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                       (real_opp real_one)).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl.
  set (K := fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s)).
  set (G := fun s : bool => real_plus (p s) (real_opp (q s))).
  set (D := fun s : bool => real_plus (K s) (real_opp (G s))).
  (* 1. Σ(p−q) == 0 *)
  assert (HsumG0 : real_eq (real_list_sum bool G [true; false]) real_zero).
  { apply (real_eq_trans
             (real_list_sum bool G [true; false])
             (real_plus (real_list_sum bool p [true; false])
                        (real_opp (real_list_sum bool q [true; false])))
             real_zero).
    - exact (gibbsd_list_sum_minus bool p q [true; false]).
    - apply (real_eq_trans
               (real_plus (real_list_sum bool p [true; false])
                          (real_opp (real_list_sum bool q [true; false])))
               (real_plus real_one (real_opp real_one)) real_zero).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool p [true; false])
                 (real_opp (real_list_sum bool q [true; false]))
                 real_one (real_opp real_one) Hnp
                 (RealSetoid.real_eq_opp_compat
                    (real_list_sum bool q [true; false]) real_one Hnq)).
      + exact (real_plus_opp real_one).
  }
  (* 2. ΣD == 0 *)
  assert (HsumD : real_eq (real_list_sum bool D [true; false]) real_zero).
  { unfold D.
    apply (real_eq_trans
             (real_list_sum bool
                (fun s : bool => real_plus (K s) (real_opp (G s))) [true; false])
             (real_plus (real_list_sum bool K [true; false])
                        (real_opp (real_list_sum bool G [true; false])))
             real_zero).
    - apply (real_eq_trans
               (real_list_sum bool
                  (fun s : bool => real_plus (K s) (real_opp (G s))) [true; false])
               (real_plus (real_list_sum bool K [true; false])
                          (real_list_sum bool
                             (fun s : bool => real_opp (G s)) [true; false]))
               (real_plus (real_list_sum bool K [true; false])
                          (real_opp (real_list_sum bool G [true; false])))).
      + exact (real_list_sum_add bool K (fun s : bool => real_opp (G s))
                   [true; false]).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool K [true; false])
                 (real_list_sum bool (fun s : bool => real_opp (G s)) [true; false])
                 (real_list_sum bool K [true; false])
                 (real_opp (real_list_sum bool G [true; false]))
                 (real_eq_refl _)
                 (real_list_sum_opp bool G [true; false])).
    - apply (real_eq_trans
               (real_plus (real_list_sum bool K [true; false])
                          (real_opp (real_list_sum bool G [true; false])))
               (real_plus real_zero (real_opp real_zero)) real_zero).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool K [true; false])
                 (real_opp (real_list_sum bool G [true; false]))
                 real_zero (real_opp real_zero) Hkl
                 (RealSetoid.real_eq_opp_compat
                    (real_list_sum bool G [true; false]) real_zero HsumG0)).
      + apply (real_eq_trans
                 (real_plus real_zero (real_opp real_zero))
                 (real_plus real_zero real_zero) real_zero).
        * apply (RealSetoid.real_eq_plus_compat real_zero (real_opp real_zero)
                   real_zero real_zero (real_eq_refl _) (real_opp_zero)).
        * exact (real_plus_zero real_zero).
  }
  (* 3. per-item clamping: D s == 0 *)
  assert (Hclamp : forall s : bool, real_eq (D s) real_zero).
  { intro s. apply (real_eq_sym _ _).
    apply (gibbe2_list_sum_zero_extract_bool D).
    - intro s0. exact (gibbe2_le_b_nonneg_diff _ _
                         (gibbsd_gibbs_pointwise_B bool p q s0 (Hp s0) (Hq s0))).
    - exact HsumD. }
  (* 4. pointwise: K s == G s ⟹ the tangent equality *)
  intro s. apply gibbe2_tangent_eq.
  apply gibbe2_kl_eq_of_w_zero.
  exact (Hclamp s).
Qed.

(* ============================================================ *)
(* Part E. Main lemma: the bridge-injected proof                                *)
(* ============================================================ *)

Theorem gibbe2_gibbs_equality_bool :
  forall (p q : bool -> Real)
    (Hp : forall s : bool, real_lt real_zero (p s))
    (Hq : forall s : bool, real_lt real_zero (q s))
    (Hnp : real_eq (real_list_sum bool p [true; false]) real_one)
    (Hnq : real_eq (real_list_sum bool q [true; false]) real_one),
  real_eq (real_list_sum bool
             (fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s))
             [true; false])
          real_zero ->
  (forall (u : Real) (Hu : real_lt real_zero u),
     real_eq (real_log u Hu) (real_plus u (real_opp real_one)) ->
     real_eq u real_one) ->
  forall s : bool, real_eq (p s) (q s).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl Heqlin s.
  assert (Htan := gibbe2_kl_zero_tangent_eq p q Hp Hq Hnp Hnq Hkl s).
  assert (Hu1 : real_eq (real_mult (q s) (real_inv_pos (p s) (Hp s))) real_one).
  { apply (Heqlin (real_mult (q s) (real_inv_pos (p s) (Hp s)))
             (real_mult_positive (q s) (real_inv_pos (p s) (Hp s))
                (Hq s) (real_inv_pos_pos (p s) (Hp s)))).
    exact Htan. }
  apply (real_eq_trans (p s)
           (real_mult (p s) (real_mult (q s) (real_inv_pos (p s) (Hp s))))
           (q s)).
  - apply (real_eq_trans (p s) (real_mult (p s) real_one)
             (real_mult (p s) (real_mult (q s) (real_inv_pos (p s) (Hp s))))).
    + apply (real_eq_sym (real_mult (p s) real_one) (p s)
               (real_mult_one (p s))).
    + apply (RealSetoid.real_eq_mult_compat (p s) real_one (p s)
               (real_mult (q s) (real_inv_pos (p s) (Hp s)))
               (real_eq_refl (p s))
               (real_eq_sym (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                  real_one Hu1)).
  - exact (gibbsd_p_mult_ratio (p s) (q s) (Hp s)).
Qed.

(* ============================================================ *)
(* Tail check: Print Assumptions (the zero-axiom witness)                       *)
(* ============================================================ *)

Print Assumptions gibbe2_le_b_antisym.
Print Assumptions gibbe2_clamp_head.
Print Assumptions gibbe2_list_sum_zero_extract_bool.
Print Assumptions gibbe2_kl_zero_tangent_eq.
Print Assumptions gibbe2_gibbs_equality_bool.
