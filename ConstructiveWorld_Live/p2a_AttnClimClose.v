(* ConstructiveWorld-Set -- real-layer convergence and Q-budget companions for the attention contraction family. *)

(** * p2a_AttnClimClose: real-layer decay chain, limit and Q-budget companions for the attention contraction family.

    Mission.  The order lemmas [one_minus_delta_pos_real] and [one_minus_delta_lt_one_real]
      provide the interface premises for the budget witness [r_arch_pow_attn_real];
      the decay chain [tv_iter_decay_real] assembles the explicit-budget
      convergence statement [attention_iterate_converges_real]; [p2a_geo_iter_le]
      bounds the geometric iterate, [p2a_attn_clim_zero] and
      [p2a_attn_tv_seq_clim_zero] prove the clim limit to zero, and
      [p2a_attn_clim_budget] carries the one-sided Q-budget form.

    Dependencies.  Stdlib [QArith.QArith] and [Extraction].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5],
      [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp],
      [UpBudgetReal] of this development.

    References.  This development, p2a_AttnClimClose.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" p2a_AttnClimClose.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
Require Import UpBudgetReal.
From Stdlib Require Import Extraction.

(* ================= Section 1. The one_minus_delta_pos_real family ================= *)
From Stdlib Require Import QArith.QArith.

Local Open Scope Q_scope.

(* ============ 1. the real-layer order lemma for 1−δ (κ := 1−δ well formed) ============ *)

(* real-layer copy of the baseline statement [one_minus_kappa_pos]: δ < 1 gives 0 < 1−δ *)
Lemma one_minus_delta_pos_real : forall delta : Real,
  real_lt delta real_one ->
  real_lt real_zero (real_plus real_one (real_opp delta)).
Proof.
  intros delta Hd.
  exact (real_lt_opp_plus delta real_one Hd).
Qed.

(* real-layer copy of the symmetric half of the baseline attention premise:
   0 < δ gives 1−δ < 1 (the pointwise difference vanishes; [real_lt_eq_lt]
   applies once 1−(1−δ) == δ holds by pointwise ring computation) *)
Lemma one_minus_delta_lt_one_real : forall delta : Real,
  real_lt real_zero delta ->
  real_lt (real_plus real_one (real_opp delta)) real_one.
Proof.
  intros delta Hd.
  apply (real_lt_zero_minus (real_plus real_one (real_opp delta)) real_one).
  apply (real_lt_eq_lt real_zero delta).
  - exact Hd.
  - apply real_eq_sym.
    apply real_eq_of_zero_diff.
    intro n.
    (* 1 − (1−δ) agrees with δ at every index: a Q ring identity per point. *)
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _
               (real_plus_proj real_one
                  (real_opp (real_plus real_one (real_opp delta))) n)).
    rewrite (qeqT_imp_qeq _ _
               (real_opp_proj (real_plus real_one (real_opp delta)) n)).
    rewrite (qeqT_imp_qeq _ _
               (real_plus_proj real_one (real_opp delta) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj delta n)).
    ring.
Qed.

(* ============ 2. the main witness: real-layer instancing of the interface premise ============ *)

Theorem r_arch_pow_attn_real :
  forall delta : Real, real_lt real_zero delta -> real_lt delta real_one ->
  forall a : Real, real_lt real_zero a ->
  forall eps : Real, real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_lt (real_mult a
              (real_pow (real_plus real_one (real_opp delta)) N)) eps).
Proof.
  intros delta Hd1 Hd2 a Ha eps Heps.
  exact (r_arch_pow_real (real_plus real_one (real_opp delta))           (one_minus_delta_pos_real delta Hd2)           (one_minus_delta_lt_one_real delta Hd1)           a Ha eps Heps).
Qed.

(* ============ 3. the TV geometric decay chain (real-layer copy) ============ *)

(* real-layer copy of the conclusion chain of the baseline statement
   [attention_tv_iter_contraction]: each step gives tv_{n+1} ≤ (1−δ)·tv_n,
   hence tv_n ≤ (1−δ)^n·tv₀.
   (the antitone power bound is the real-layer copy
   [UpBudgetReal.real_pow_anti_mono]; [attention_iterate_converges_real] reuses
   it directly without a second proof.) *)
Lemma tv_iter_decay_real :
  forall (delta : Real)
         (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
         (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  forall n : nat,
    real_le (tv_seq n)
            (real_mult (real_pow (real_plus real_one (real_opp delta)) n)
                       (tv_seq Datatypes.O)).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep n.
  assert (Hk1 : real_lt real_zero (real_plus real_one (real_opp delta)))
    by exact (one_minus_delta_pos_real delta Hd2).
  set (kappa := real_plus real_one (real_opp delta)) in *.
  induction n as [| n IH].
  - (* κ^0 is one: 1·tv₀ == tv₀ *)
    apply real_eq_le_bridge.
    apply real_eq_sym.
    exact (real_mult_one_l (tv_seq Datatypes.O)).
  - (* tv_{n+1} ≤ κ·tv_n ≤ κ·(κ^n·tv₀) == κ^{n+1}·tv₀ *)
    apply (real_le_trans _ (real_mult kappa (tv_seq n))).
    + exact (Hstep n).
    + apply (real_le_trans _ (real_mult (tv_seq n) kappa)).
      * apply real_eq_le_bridge.
        exact (real_mult_comm kappa (tv_seq n)).
      * apply (real_le_trans _
                 (real_mult (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                            kappa)).
        -- exact (real_le_mult_compat (tv_seq n)
                    (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                    kappa Hk1 IH).
        -- apply real_eq_le_bridge.
           exact (real_eq_trans
                    (real_mult (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                               kappa)
                    (real_mult kappa
                               (real_mult (real_pow kappa n) (tv_seq Datatypes.O)))
                    (real_mult (real_mult kappa (real_pow kappa n))
                               (tv_seq Datatypes.O))
                    (real_mult_comm (real_mult (real_pow kappa n)
                                        (tv_seq Datatypes.O))
                                    kappa)
                    (real_mult_assoc kappa (real_pow kappa n)
                                     (tv_seq Datatypes.O))).
Qed.

(* ============ 4. the main convergence statement: explicit sigT budget witness ============ *)

(* real-layer assembly of the baseline statement [attention_iterate_converges]:
   the budget N comes from [r_arch_pow_attn_real]; the tail bound n ≥ N combines
   the tv decay chain above, the antitone power bound [real_pow_anti_mono], and
   the endpoint a·κ^N < eps of [r_arch_pow_attn_real].
   Scope note: tv_seq carries the real-layer content of the semantic object
   n ↦ TV(iterate attention_step n μ₀, boltzmann_dist_attn), and the per-step
   contraction premise Hstep mirrors the conclusion shape of the baseline
   [attention_tv_contraction]. A full real-layer instancing of the abstract
   Section would resolve the interface premises [detailed_balance],
   [minorization], [sum_swap_cc], [abs_ge_zero_id_cc] and [lt_plus_compat] as a whole,
   a development of its own that lies outside this file; [r_arch_pow_attn_real]
   is unaffected. *)
Theorem attention_iterate_converges_real :
  forall (delta : Real)
         (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
         (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  forall eps : Real, real_lt real_zero eps ->
  real_lt real_zero (tv_seq Datatypes.O) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (tv_seq n) eps).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  destruct (r_arch_pow_attn_real delta Hd1 Hd2
             (tv_seq Datatypes.O) Htv0 eps Heps) as [N HN].
  exists N.
  intros n Hn.
  set (kappa := real_plus real_one (real_opp delta)) in *.
  apply (real_le_lt_trans _
           (real_mult (real_pow kappa n) (tv_seq Datatypes.O))).
  - exact (tv_iter_decay_real delta Hd1 Hd2 tv_seq Hstep n).
  - apply (real_le_lt_trans _
             (real_mult (real_pow kappa N) (tv_seq Datatypes.O))).
    + assert (Hk1 : real_lt real_zero kappa)
        by exact (one_minus_delta_pos_real delta Hd2).
      assert (Hk2le : real_le kappa real_one)
        by exact (real_lt_le_bridge kappa real_one
                    (one_minus_delta_lt_one_real delta Hd1)).
      assert (Hanti : real_le (real_pow kappa n) (real_pow kappa N))
        by exact (real_pow_anti_mono kappa Hk1 Hk2le N n (NatLe_lift N n Hn)).
      exact (real_le_mult_compat (real_pow kappa n) (real_pow kappa N)
               (tv_seq Datatypes.O) Htv0 Hanti).
    + exact (real_eq_lt_lt (real_mult (real_pow kappa N) (tv_seq Datatypes.O))
               (real_mult (tv_seq Datatypes.O) (real_pow kappa N)) eps
               (real_mult_comm (real_pow kappa N) (tv_seq Datatypes.O)) HN).
Qed.

(* ============ 5. extraction check: zero [Obj.magic] ============ *)
(* ================= Section 2. The p2a_geo_iter_le family ================= *)
From Stdlib Require Import QArith.QArith.

(* ============ geometric iterate bound: u n ≤ κ^n·u 0 ============ *)

Theorem p2a_geo_iter_le : forall (u : nat -> Real) (kappa : Real),
  real_lt real_zero kappa ->
  (forall n : nat, real_le (u (Datatypes.S n)) (real_mult kappa (u n))) ->
  forall n : nat, real_le (u n) (real_mult (real_pow kappa n) (u 0%nat)).
Proof.
  intros u kappa Hk1 Hstep n.
  induction n as [| n IH].
  - apply real_eq_le_bridge. apply real_eq_sym. apply real_mult_one_l.
  - apply (real_le_trans _ (real_mult kappa (u n))).
    + apply Hstep.
    + apply (real_le_trans _
               (real_mult kappa (real_mult (real_pow kappa n) (u 0%nat)))).
      * apply real_le_mult_compat_r.
        -- exact (real_lt_le_bridge real_zero kappa Hk1).
        -- exact IH.
      * apply real_eq_le_bridge. apply real_mult_assoc.
Qed.

(* ============ the central argument: clim convergence of geometrically contracting sequences (limit zero) ============ *)

Theorem p2a_attn_clim_zero : forall (u : nat -> Real) (kappa : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  (forall n : nat, real_le (u (Datatypes.S n)) (real_mult kappa (u n))) ->
  (forall n : nat, real_le real_zero (u n)) ->
  real_lt real_zero (u 0%nat) ->
  real_lim u real_zero.
Proof.
  intros u kappa Hk1 Hk2 Hstep Hnonneg Hu0 eps Heps.
  destruct (r_arch_pow_real kappa Hk1 Hk2 (u 0%nat) Hu0 (real_const eps)
              (real_const_pos eps Heps)) as [N HN].
  exists N. intros n Hn.
  split.
  - (* upper side: u n ≤ κ^n·u0 ≤ κ^N·u0 < eps, restated in the 0+eps form *)
    apply (real_lt_eq_lt (u n) (real_const eps)
             (real_plus real_zero (real_const eps))).
    + apply (real_le_lt_trans (u n)
               (real_mult (real_pow kappa N) (u 0%nat))).
      * apply (real_le_trans _
                 (real_mult (real_pow kappa n) (u 0%nat))).
        -- exact (p2a_geo_iter_le u kappa Hk1 Hstep n).
        -- apply real_le_mult_compat.
           ++ exact Hu0.
           ++ exact (real_pow_anti_mono kappa Hk1
                       (real_lt_le_bridge kappa real_one Hk2) N n
                       (NatLe_lift N n Hn)).
      * apply (real_eq_lt_lt
                 (real_mult (real_pow kappa N) (u 0%nat))
                 (real_mult (u 0%nat) (real_pow kappa N))).
        -- apply real_mult_comm.
        -- exact HN.
    + apply real_eq_sym.
      apply (real_eq_trans (real_plus real_zero (real_const eps))
                           (real_plus (real_const eps) real_zero)).
      * apply real_plus_comm.
      * apply real_plus_zero.
  - (* lower side: 0 − eps < u n rests on the nonnegativity premise alone *)
    apply (real_lt_le_trans (real_plus real_zero (real_opp (real_const eps))) real_zero).
    + apply (real_eq_lt_lt
               (real_plus real_zero (real_opp (real_const eps)))
               (real_opp (real_const eps)) real_zero).
      * apply (real_eq_trans
                 (real_plus real_zero (real_opp (real_const eps)))
                 (real_plus (real_opp (real_const eps)) real_zero)).
        -- apply real_plus_comm.
        -- apply real_plus_zero.
      * exact (real_lt_zero_opp (real_const eps) (real_const_pos eps Heps)).
    + exact (Hnonneg n).
Qed.

(* ============ the attention specialization: κ := 1−δ (paper 2, §5.5/§9.4) ============ *)
(*   the per-step contraction premise Hstep mirrors the real-layer dual of
    [attention_tv_contraction]: the instance of the geometric rate (1−δ) in
    [S06_DiffSamplingGibbs] keeps the explicit-premise discipline of the
    [UpArchAttn] piece 2 form, while a whole-world instancing of the abstract
    Section TV/iterate objects is a development of its own and lies outside
    this file. *)

Theorem p2a_attn_tv_seq_clim_zero :
  forall (tv_seq : nat -> Real) (delta : Real),
  real_lt real_zero delta -> real_lt delta real_one ->
  (forall n : nat,
     real_le (tv_seq (Datatypes.S n))
             (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  (forall n : nat, real_le real_zero (tv_seq n)) ->
  real_lt real_zero (tv_seq 0%nat) ->
  real_lim tv_seq real_zero.
Proof.
  intros tv_seq delta Hd0 Hd1 Hstep Hnonneg Hu0.
  exact (p2a_attn_clim_zero tv_seq (real_plus real_one (real_opp delta))           (one_minus_delta_pos_real delta Hd1)           (one_minus_delta_lt_one_real delta Hd0)           Hstep Hnonneg Hu0).
Qed.

(* ============ the budget companion: one-sided Q-eps budget form of the clim limit ============ *)

Theorem p2a_attn_clim_budget : forall (u : nat -> Real) (kappa : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  (forall n : nat, real_le (u (Datatypes.S n)) (real_mult kappa (u n))) ->
  (forall n : nat, real_le real_zero (u n)) ->
  real_lt real_zero (u 0%nat) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (u n) (real_plus real_zero (real_const eps))).
Proof.
  intros u kappa Hk1 Hk2 Hstep Hnonneg Hu0 eps Heps.
  destruct (p2a_attn_clim_zero u kappa Hk1 Hk2 Hstep Hnonneg Hu0 eps Heps)
    as [N HN].
  exists N. intros n Hn.
  destruct (HN n Hn) as [Hup _].
  exact Hup.
Qed.

(* ---- audit companions: Print Assumptions audits and the extraction check ---- *)

Print Assumptions p2a_geo_iter_le.
Print Assumptions p2a_attn_clim_zero.
Print Assumptions p2a_attn_tv_seq_clim_zero.
Print Assumptions p2a_attn_clim_budget.

Set Extraction Output Directory ".".
Extraction "p2a_attnclimclose.ml" p2a_geo_iter_le p2a_attn_clim_budget.
