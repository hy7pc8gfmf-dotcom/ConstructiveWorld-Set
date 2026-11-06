(* ConstructiveWorld-Set -- upstream-requirement completion modules over the constructive setoid real line. *)

(** * UpReqStepKLEtaInst: premise-free single-step KL contraction of the eta-interpolated policy update.

    Mission.  One-step KL contraction of the eta-interpolated policy update over
      the setoid real line: ring cores [ske_r_za_cancel], [ske_r_step], [ske_r_klpi];
      log-law assembly [ske_logM], [ske_log_step], [ske_log_pist]; identities
      [ske_pt_eq], [ske_Zrel_eq]; contraction [ske_geom_step_discharged] with
      companions [ske_geom_step_discharged_B]; step KL bounds
      [ske_step_kl_eta_bound_inst], [ske_step_kl_eta_bound_inst_B].

    Dependencies.  Stdlib [QArith.Qring].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5],
      [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], and [UpRealLeB].

    References.  This development, UpReqStepKLEtaInst.v, the baseline module in
      ConstructiveWorld-Main (statement names carried over verbatim).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements extract
      with [Obj.magic] = 0 and no erasure; [coqchk] reports [Axioms: none].
      [ske_nonnil] carries a toy-proof replacement body (head discrimination).
      [ske_pow_pos] carries a toy-proof replacement body (witness [cauchy_real_exp_pos]).
      [ske_log_pow] carries a toy-proof replacement body (law [log_inv_exp_neg_thm]).
      [ske_geom_step_discharged_B] carries a toy-proof replacement body via [real_le_closure_b_one].
      [ske_step_kl_eta_bound_inst_B] carries a toy-proof replacement body via [real_le_closure_b_one].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqStepKLEtaInst.v] compiles
      cleanly (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.Qring.
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

(* ============================================================ *)
(* Part 0: basic instruments (premise-free generic ring lemmas + the value-level resubstituter) *)
(* ============================================================ *)

Lemma ske_opp_opp : forall x : Real,
  real_eq (real_opp (real_opp x)) x.
Proof.
  intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

Lemma ske_r_opp_split : forall u v : Real,
  real_eq (real_opp (real_plus u v)) (real_plus (real_opp u) (real_opp v)).
Proof.
  intros u v. destruct u as [a Ha]. destruct v as [b Hb].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* R-advA: e*(u + opp v) == e*u + opp(e*v) *)
Lemma ske_r_advA : forall e u v : Real,
  real_eq (real_mult e (real_plus u (real_opp v)))
          (real_plus (real_mult e u) (real_opp (real_mult e v))).
Proof.
  intros e u v. destruct e as [x Hx]. destruct u as [y Hy].
  destruct v as [z Hz]. apply real_eq_of_zero_diff.
  intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* R-assoc2: (e*f)*(g*X) == e*((f*g)*X) *)
Lemma ske_r_assoc2 : forall e f g X : Real,
  real_eq (real_mult (real_mult e f) (real_mult g X))
          (real_mult e (real_mult (real_mult f g) X)).
Proof.
  intros e f g X. destruct e as [x Hx]. destruct f as [y Hy].
  destruct g as [z Hz]. destruct X as [w Hw].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* R-mult-one-l: e*(1*X) == e*X *)
Lemma ske_r_mult_one_l : forall e X : Real,
  real_eq (real_mult e (real_mult real_one X)) (real_mult e X).
Proof.
  intros e X. destruct e as [x Hx]. destruct X as [w Hw].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* R3: the nontrivial ring core behind the two assembly trees of ske_pt_eq (cancellation of the eta * Za factor) *)
Lemma ske_r_za_cancel :
  forall (lp lza lqr ri e f : Real),
  real_eq (real_plus lp
             (real_plus (real_mult (real_mult e f) ri)
                        (real_plus (real_opp (real_mult e lp))
                                   (real_mult e lqr))))
          (real_plus (real_mult e lza)
                     (real_plus (real_mult (real_plus real_one (real_opp e)) lp)
                                (real_mult e
                                   (real_plus (real_opp lza)
                                              (real_plus lqr (real_mult f ri)))))).
Proof.
  intros lp lza lqr ri e f.
  destruct lp as [a Ha]. destruct lza as [b Hb]. destruct lqr as [c Hc].
  destruct ri as [d Hd]. destruct e as [x Hx]. destruct f as [y Hy].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* R4: the nontrivial ring core behind the two assembly trees of ske_pnext_pt *)
Lemma ske_r_step :
  forall (lp lza lz lqr ri e f : Real),
  real_eq (real_plus (real_opp (real_plus (real_mult e lza) lz))
                      (real_plus lp
                                 (real_plus (real_mult (real_mult e f) ri)
                                            (real_plus (real_opp (real_mult e lp))
                                                       (real_mult e lqr)))))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp e)) lp)
                                (real_mult e
                                   (real_plus (real_opp lza)
                                              (real_plus lqr (real_mult f ri)))))
                     (real_opp lz)).
Proof.
  intros lp lza lz lqr ri e f.
  destruct lp as [a Ha]. destruct lza as [b Hb]. destruct lz as [c Hc].
  destruct lqr as [d Hd]. destruct ri as [g Hg].
  destruct e as [x Hx]. destruct f as [y Hy].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* R5: the nontrivial ring core behind the two assembly trees of the W5
   pointwise identity (the tree shapes kept unflattened).
   math core: LHS = pv*(FORM-F1), RHS = m*pv*(FORM-lp) + pv*lz; both sides
   == pv*(-m*lza + m*lqr + m*f*ri - m*lp + lz) *)
Lemma ske_r_klpi :
  forall (pv lp lza lz lqr ri e f : Real),
  real_eq (real_mult pv
             (real_opp (real_plus
                (real_plus (real_opp (real_plus (real_mult e lza) lz))
                           (real_plus lp
                                      (real_plus (real_mult (real_mult e f) ri)
                                                 (real_plus (real_opp (real_mult e lp))
                                                            (real_mult e lqr)))))
                (real_opp (real_plus (real_opp lza)
                                     (real_plus lqr (real_mult f ri)))))))
          (real_plus (real_mult (real_plus real_one (real_opp e))
                                (real_mult pv
                                   (real_plus (real_opp lp)
                                              (real_plus (real_opp lza)
                                                         (real_plus lqr (real_mult f ri))))))
                     (real_mult pv lz)).
Proof.
  intros pv lp lza lz lqr ri e f.
  destruct pv as [p Hp]. destruct lp as [a Ha]. destruct lza as [b Hb].
  destruct lz as [c Hc]. destruct lqr as [d Hd]. destruct ri as [g Hg].
  destruct e as [x Hx]. destruct f as [y Hy].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* value-level resubstituter: equal cw_log values with both arguments positive imply equal values *)
Lemma ske_eq_of_log : forall (a b : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq (cw_log a Ha) (cw_log b Hb) -> real_eq a b.
Proof.
  intros a b Ha Hb H.
  apply (real_eq_trans _ (real_exp_neg (real_log_inv a Ha))).
  - exact (real_eq_sym _ _ (real_exp_neg_log_inv a Ha)).
  - apply (real_eq_trans _ (real_exp_neg (real_log_inv b Hb))).
    + apply cauchy_real_exp_wd. unfold real_log_inv.
      apply (real_eq_trans _ (cw_log a Ha)).
      * apply ske_opp_opp.
      * apply (real_eq_trans _ (cw_log b Hb)).
        -- exact H.
        -- exact (real_eq_sym _ _ (ske_opp_opp (cw_log b Hb))).
    + exact (real_exp_neg_log_inv b Hb).
Qed.

(* extensionality of the KL term in its second slot *)
Lemma ske_kl_term_ext : forall (p q1 q2 : Real)
    (Hp : real_lt real_zero p) (Hq1 : real_lt real_zero q1)
    (Hq2 : real_lt real_zero q2),
  real_eq q1 q2 ->
  real_eq (real_kl_term p q1 Hp Hq1) (real_kl_term p q2 Hp Hq2).
Proof.
  intros p q1 q2 Hp Hq1 Hq2 Hq. unfold real_kl_term.
  apply RealSetoid.real_eq_mult_compat.
  - apply real_eq_refl.
  - apply RealSetoid.real_eq_opp_compat.
    apply real_log_wd.
    apply RealSetoid.real_eq_mult_compat.
    + exact Hq.
    + apply real_eq_refl.
Qed.

(* R-mult-opp: e*opp(X) == opp(e*X) *)
Lemma ske_r_mult_opp : forall e X : Real,
  real_eq (real_mult e (real_opp X)) (real_opp (real_mult e X)).
Proof.
  intros e X. destruct e as [x Hx]. destruct X as [w Hw].
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* the state table is nonempty (a Set-level supply for the nonemptiness premise of real_list_sum_pos, stated generically outside the section) *)
Lemma ske_nonnil : forall k : nat, (List.seq 0 (Datatypes.S k)) <> (@nil nat).
Proof.
  intros k Hc.
  simpl in Hc.
  discriminate Hc.
Qed.

(* ============================================================ *)
(* Section: the Real-level form of the S05 Alignment shapes (definition-by-definition duality) *)
(*   state carrier: the initial segment seq 0 (S k) of nat (k makes the  *)
(*   nonemptiness face honest); reward/beta/pi_ref/eta/pit are all       *)
(*   section variables (Set-valued premises).                            *)
(* ============================================================ *)

Section SkeInst.

Variable k : nat.
Let n := Datatypes.S k.

Variable beta : Real.
Variable Hbeta : real_lt real_zero beta.
Variable r : nat -> Real.
Variable eta : Real.
Variable Heta : real_lt real_zero eta.
Variable Hetale : real_le eta real_one.
Variable pit : nat -> Real.
Variable Hpit : forall i : nat, real_lt real_zero (pit i).
Variable Hpitn : real_eq (real_list_sum nat pit (List.seq 0 n)) real_one.
Variable piref : nat -> Real.
Variable Hpref : forall i : nat, real_lt real_zero (piref i).

(* the state table is nonempty (a Set-level supply for the nonemptiness premise of real_list_sum_pos) *)
(* ---------- S05 definition duality ---------- *)
(* ib := beta^-1; ske_e1(i) := exp(-beta^-1 * r(i))                *)
(* ske_Za := sum piref*e1   (S05 Z_align)                          *)
(* ske_pist(i) := Za^-1 * piref(i)*e1(i)   (S05 pi_star closed form) *)
(* ske_adv(i) := r(i) - beta*(log pit(i) - log piref(i))           *)
(*               (S05 advantage_aug)                               *)
(* ske_Zrel := sum pit*exp(-eta*beta^-1*adv)   (S05 Z_rel)          *)
(* ske_pnext(i) := Zrel^-1 * pit(i)*exp(-eta*beta^-1*adv(i))        *)
(*               (S05 pi_next)                                     *)

Let ib := real_inv_pos beta Hbeta.

Definition ske_e1 (i : nat) : Real :=
  real_exp_neg (real_opp (real_mult ib (r i))).

Definition ske_Za : Real :=
  real_list_sum nat (fun i => real_mult (piref i) (ske_e1 i)) (List.seq 0 n).

Lemma ske_HZa : real_lt real_zero ske_Za.
Proof.
  unfold ske_Za.
  apply (real_list_sum_pos nat _ (List.seq 0 n)).
  - intro i. apply real_mult_positive.
    + apply Hpref.
    + apply real_exp_neg_pos.
  - exact (ske_nonnil k).
Qed.

Definition ske_pist (i : nat) : Real :=
  real_mult (real_inv_pos ske_Za ske_HZa)
            (real_mult (piref i) (ske_e1 i)).

Lemma ske_Hpist : forall i : nat, real_lt real_zero (ske_pist i).
Proof.
  intro i. unfold ske_pist. apply real_mult_positive.
  - apply real_inv_pos_pos.
  - apply real_mult_positive.
    + apply Hpref.
    + apply real_exp_neg_pos.
Qed.

Definition ske_adv (i : nat) : Real :=
  real_plus (r i) (real_opp (real_mult beta
    (real_plus (cw_log (pit i) (Hpit i))
               (real_opp (cw_log (piref i) (Hpref i)))))).

Definition ske_Zrel : Real :=
  real_list_sum nat
    (fun i => real_mult (pit i)
                        (real_exp_neg
                           (real_opp (real_mult (real_mult eta ib) (ske_adv i)))))
    (List.seq 0 n).

Lemma ske_HZrel : real_lt real_zero ske_Zrel.
Proof.
  unfold ske_Zrel.
  apply (real_list_sum_pos nat _ (List.seq 0 n)).
  - intro i. apply real_mult_positive.
    + apply Hpit.
    + apply real_exp_neg_pos.
  - exact (ske_nonnil k).
Qed.

Definition ske_pnext (i : nat) : Real :=
  real_mult (real_inv_pos ske_Zrel ske_HZrel)
            (real_mult (pit i)
                       (real_exp_neg
                          (real_opp (real_mult (real_mult eta ib) (ske_adv i))))).

Lemma ske_Hpnext : forall i : nat, real_lt real_zero (ske_pnext i).
Proof.
  intro i. unfold ske_pnext. apply real_mult_positive.
  - apply real_inv_pos_pos.
  - apply real_mult_positive.
    + apply Hpit.
    + apply real_exp_neg_pos.
Qed.

(* ---------- engine-face positivity pieces (the W5 half: HZ and Hqv proved constructively) ---------- *)

Lemma ske_pow_pos : forall (a al : Real) (Ha : real_lt real_zero a),
  real_lt real_zero (real_pow_pos a al Ha).
Proof.
  intros a al Ha.
  unfold real_pow_pos.
  apply cauchy_real_exp_pos.
Qed.

Lemma ske_HZ : real_lt real_zero
  (real_interp_Z n pit ske_pist eta Hpit ske_Hpist).
Proof.
  unfold real_interp_Z.
  apply (real_list_sum_pos nat _ (List.seq 0 n)).
  - intro i. apply real_mult_positive.
    + apply ske_pow_pos.
    + apply ske_pow_pos.
  - exact (ske_nonnil k).
Qed.

Lemma ske_Hqv : forall i : nat,
  real_lt real_zero
    (real_step_next n pit ske_pist eta Hpit ske_Hpist ske_HZ i).
Proof.
  intro i. unfold real_step_next. apply real_mult_positive.
  - apply real_mult_positive.
    + apply ske_pow_pos.
    + apply ske_pow_pos.
  - apply real_inv_pos_pos.
Qed.

(* ---------- the log-law assembly layer ---------- *)

(* the log of e1 == beta^-1 * r(i) *)
Lemma ske_log_e1 : forall i : nat,
  real_eq (cw_log (ske_e1 i) (real_exp_neg_pos (real_opp (real_mult ib (r i)))))
          (real_mult ib (r i)).
Proof.
  intro i. unfold ske_e1.
  apply (real_eq_trans _ (real_opp (real_opp (real_mult ib (r i))))).
  - exact (log_inv_exp_neg_thm
             (real_opp (real_opp (real_mult ib (r i))))
             (real_exp_neg_pos (real_opp (real_mult ib (r i))))).
  - apply ske_opp_opp.
Qed.

(* the log of a power == alpha*log a (the witness shape fixed) *)
Lemma ske_log_pow : forall (a al : Real) (Ha : real_lt real_zero a),
  real_eq (cw_log (real_pow_pos a al Ha)
                  (cauchy_real_exp_pos (real_mult al (cw_log a Ha))))
          (real_mult al (cw_log a Ha)).
Proof.
  intros a al Ha.
  unfold real_pow_pos.
  exact (log_inv_exp_neg_thm (real_mult al (cw_log a Ha))           (cauchy_real_exp_pos (real_mult al (cw_log a Ha)))).
Qed.

(* log expansion of pi_star: log pist == -log Za + (log piref + beta^-1*r) *)
Lemma ske_log_pist : forall i : nat,
  real_eq (cw_log (ske_pist i) (ske_Hpist i))
          (real_plus (real_opp (cw_log ske_Za ske_HZa))
                     (real_plus (cw_log (piref i) (Hpref i))
                                (real_mult ib (r i)))).
Proof.
  intro i.
  assert (HP : real_lt real_zero
                 (real_mult (piref i) (ske_e1 i)))
    by (apply real_mult_positive; [apply Hpref | apply real_exp_neg_pos]).
  assert (HP2 : real_lt real_zero
                  (real_mult (real_inv_pos ske_Za ske_HZa)
                             (real_mult (piref i) (ske_e1 i))))
    by (apply real_mult_positive;
          [apply real_inv_pos_pos | exact HP]).
  pose proof
    (log_inv_mult_thm (real_inv_pos ske_Za ske_HZa)
       (real_mult (piref i) (ske_e1 i))
       (real_inv_pos_pos ske_Za ske_HZa) HP HP2) as H1.
  pose proof (kl_log_inv ske_Za ske_HZa (real_inv_pos_pos ske_Za ske_HZa)) as H2.
  assert (H3 : real_eq (cw_log (real_mult (piref i) (ske_e1 i)) HP)
                       (real_plus (cw_log (piref i) (Hpref i))
                                  (real_mult ib (r i)))).
  { apply (real_eq_trans _
             (real_plus (cw_log (piref i) (Hpref i))
                        (cw_log (ske_e1 i)
                           (real_exp_neg_pos (real_opp (real_mult ib (r i))))))).
    - exact (log_inv_mult_thm (piref i) (ske_e1 i) (Hpref i)
               (real_exp_neg_pos (real_opp (real_mult ib (r i)))) HP).
    - apply RealSetoid.real_eq_plus_compat.
      + apply real_eq_refl.
      + exact (ske_log_e1 i). }
  apply (real_eq_trans _ (real_plus
             (cw_log (real_inv_pos ske_Za ske_HZa)
                     (real_inv_pos_pos ske_Za ske_HZa))
             (cw_log (real_mult (piref i) (ske_e1 i)) HP))).
  - apply (real_eq_trans _
             (cw_log (real_mult (real_inv_pos ske_Za ske_HZa)
                                (real_mult (piref i) (ske_e1 i))) HP2)).
    + exact (real_log_wd (ske_pist i)
               (real_mult (real_inv_pos ske_Za ske_HZa)
                          (real_mult (piref i) (ske_e1 i)))
               (ske_Hpist i) HP2 (real_eq_refl _)).
    + exact H1.
  - apply RealSetoid.real_eq_plus_compat.
    + exact H2.
    + exact H3.
Qed.


(* opp(e*(u + opp v)) == opp(e*u) + e*v (the flattening core of W5/logM) *)
Lemma ske_opp_mult_plus : forall e u v : Real,
  real_eq (real_opp (real_mult e (real_plus u (real_opp v))))
          (real_plus (real_opp (real_mult e u)) (real_mult e v)).
Proof.
  intros e u v.
  apply (real_eq_trans _
           (real_plus (real_opp (real_mult e u))
                      (real_opp (real_opp (real_mult e v))))).
  - apply (real_eq_trans _
             (real_opp (real_plus (real_mult e u) (real_opp (real_mult e v))))).
    + apply RealSetoid.real_eq_opp_compat. exact (ske_r_advA e u v).
    + apply ske_r_opp_split.
  - apply RealSetoid.real_eq_plus_compat.
    + apply real_eq_refl.
    + exact (ske_opp_opp (real_mult e v)).
Qed.

(* exponential ring identity for the advantage: eta*beta^-1*adv == eta*beta^-1*r - eta*(lp-lqr) *)
Lemma ske_adv_exp : forall i : nat,
  real_eq (real_mult (real_mult eta ib) (ske_adv i))
          (real_plus (real_mult (real_mult eta ib) (r i))
                     (real_opp (real_mult eta
                                  (real_plus (cw_log (pit i) (Hpit i))
                                             (real_opp (cw_log (piref i) (Hpref i))))))).
Proof.
  intro i. unfold ske_adv.
  pose (X := real_plus (cw_log (pit i) (Hpit i))
                       (real_opp (cw_log (piref i) (Hpref i)))).
  (* leaf replacement: (eta*ib)*(beta*X) == eta*X (ib*beta == 1 via three named compat steps) *)
  assert (H2p : real_eq (real_mult ib beta) real_one).
  { apply (real_eq_trans _ (real_mult beta ib)).
    - apply real_mult_comm.
    - exact (real_inv_pos_correct beta Hbeta). }
  (* leaf: (eta*ib)*(beta*X) == eta*X (absorbing ib*beta == 1) *)
  assert (Hleaf : real_eq (real_mult (real_mult eta ib) (real_mult beta X))
                          (real_mult eta X)).
  { apply (real_eq_trans _
             (real_mult eta (real_mult (real_mult ib beta) X))).
    - exact (ske_r_assoc2 eta ib beta X).
    - apply (real_eq_trans _ (real_mult eta (real_mult real_one X))).
      + exact (RealSetoid.real_eq_mult_compat eta
                 (real_mult (real_mult ib beta) X) eta (real_mult real_one X)
                 (real_eq_refl eta)
                 (RealSetoid.real_eq_mult_compat (real_mult ib beta) X
                    real_one X H2p (real_eq_refl X))).
      + exact (ske_r_mult_one_l eta X). }
  (* assembly: (eta*ib)*(r + opp(beta*X)) == eta*ib*r + opp((eta*ib)*(beta*X))
              == eta*ib*r + opp(eta*X) *)
  apply (real_eq_trans _
           (real_plus (real_mult (real_mult eta ib) (r i))
                      (real_opp (real_mult (real_mult eta ib)
                                           (real_mult beta X))))).
  - exact (ske_r_advA (real_mult eta ib) (r i) (real_mult beta X)).
  - apply RealSetoid.real_eq_plus_compat.
    + apply real_eq_refl.
    + apply RealSetoid.real_eq_opp_compat. exact Hleaf.
Qed.

(* ============================================================ *)
(* Part 2: the log-level assembly layer                          *)
(* ============================================================ *)

(* log(pit*E) == lp + (eta*ib*r + (opp(eta*lp) + eta*lqr))
   (E := exp_neg(opp(eta*ib*adv)), the input of ske_adv_exp) *)
Lemma ske_logM : forall i : nat,
  real_eq (cw_log
             (real_mult (pit i)
                        (real_exp_neg
                           (real_opp (real_mult (real_mult eta ib) (ske_adv i)))))
             (real_mult_positive (pit i)
                (real_exp_neg (real_opp (real_mult (real_mult eta ib) (ske_adv i))))
                (Hpit i)
                (real_exp_neg_pos (real_opp (real_mult (real_mult eta ib) (ske_adv i))))))
          (real_plus (cw_log (pit i) (Hpit i))
                     (real_plus (real_mult (real_mult eta ib) (r i))
                                (real_plus (real_opp (real_mult eta (cw_log (pit i) (Hpit i))))
                                           (real_mult eta (cw_log (piref i) (Hpref i)))))).
Proof.
  intro i.
  apply (real_eq_trans _
           (real_plus (cw_log (pit i) (Hpit i))
                      (cw_log (real_exp_neg (real_opp (real_mult (real_mult eta ib) (ske_adv i))))
                              (real_exp_neg_pos (real_opp (real_mult (real_mult eta ib) (ske_adv i))))))).
  - exact (log_inv_mult_thm (pit i)
              (real_exp_neg (real_opp (real_mult (real_mult eta ib) (ske_adv i))))
              (Hpit i)
              (real_exp_neg_pos (real_opp (real_mult (real_mult eta ib) (ske_adv i))))
              (real_mult_positive (pit i)
                 (real_exp_neg (real_opp (real_mult (real_mult eta ib) (ske_adv i))))
                 (Hpit i)
                 (real_exp_neg_pos (real_opp (real_mult (real_mult eta ib) (ske_adv i)))))).
  - apply RealSetoid.real_eq_plus_compat.
    + apply real_eq_refl.
    + apply (real_eq_trans _
               (real_opp (real_opp (real_mult (real_mult eta ib) (ske_adv i))))).
      * exact (log_inv_exp_neg_thm
                 (real_opp (real_opp (real_mult (real_mult eta ib) (ske_adv i))))
                 (real_exp_neg_pos (real_opp (real_mult (real_mult eta ib) (ske_adv i))))).
      * apply (real_eq_trans _ (real_mult (real_mult eta ib) (ske_adv i))).
        -- exact (ske_opp_opp (real_mult (real_mult eta ib) (ske_adv i))).
        -- apply (real_eq_trans _
                    (real_plus (real_mult (real_mult eta ib) (r i))
                               (real_opp (real_mult eta
                                                  (real_plus (cw_log (pit i) (Hpit i))
                                                             (real_opp (cw_log (piref i) (Hpref i)))))))).
           ++ exact (ske_adv_exp i).
           ++ apply RealSetoid.real_eq_plus_compat.
              ** apply real_eq_refl.
              ** exact (ske_opp_mult_plus eta (cw_log (pit i) (Hpit i))
                           (cw_log (piref i) (Hpref i))).
Qed.



(* pointwise identity (the bridge core): pit*E == Za^eta * (pit^(1-eta) * pist^eta)
   log level: lp + (eta*ib*r - eta*lp + eta*lqr)
        == eta*lZa + ((1-eta)*lp + eta*(-lZa + lqr + ib*r))
   ring core = ske_r_za_cancel (cancellation of the Za^eta factor) *)
Lemma ske_pt_eq : forall i : nat,
  real_eq (real_mult (pit i)
             (real_exp_neg (real_opp (real_mult (real_mult eta ib) (ske_adv i)))))
          (real_mult (real_pow_pos ske_Za eta ske_HZa)
                     (real_mult (real_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i))
                                (real_pow_pos (ske_pist i) eta (ske_Hpist i)))).
Proof.
  intro i.
  pose (PZ := real_pow_pos ske_Za eta ske_HZa).
  pose (PM := real_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i)).
  pose (PP := real_pow_pos (ske_pist i) eta (ske_Hpist i)).
  pose (HPZ := cauchy_real_exp_pos (real_mult eta (cw_log ske_Za ske_HZa))).
  pose (HPM := cauchy_real_exp_pos
                 (real_mult (real_plus real_one (real_opp eta)) (cw_log (pit i) (Hpit i)))).
  pose (HPP := cauchy_real_exp_pos (real_mult eta (cw_log (ske_pist i) (ske_Hpist i)))).
  pose (HPG := real_mult_positive PM PP HPM HPP).
  pose (HG := real_mult_positive PZ (real_mult PM PP) HPZ HPG).
  pose proof (log_inv_mult_thm PZ (real_mult PM PP) HPZ HPG HG) as HR1.
  pose proof (log_inv_mult_thm PM PP HPM HPP HPG) as HR2.
  pose proof (ske_log_pow ske_Za eta ske_HZa) as HZl.
  pose proof (ske_log_pow (pit i) (real_plus real_one (real_opp eta)) (Hpit i)) as HPl.
  pose proof (ske_log_pow (ske_pist i) eta (ske_Hpist i)) as HPp.
  assert (HR : real_eq (cw_log (real_mult PZ (real_mult PM PP)) HG)
                       (real_plus (real_mult eta (cw_log ske_Za ske_HZa))
                                  (real_plus (real_mult (real_plus real_one (real_opp eta))
                                                        (cw_log (pit i) (Hpit i)))
                                             (real_mult eta
                                                        (real_plus (real_opp (cw_log ske_Za ske_HZa))
                                                                   (real_plus (cw_log (piref i) (Hpref i))
                                                                              (real_mult ib (r i)))))))).
  { apply (real_eq_trans _ (real_plus (cw_log PZ HPZ) (cw_log (real_mult PM PP) HPG))).
    - exact HR1.
    - apply RealSetoid.real_eq_plus_compat.
      + exact HZl.
      + apply (real_eq_trans _ (real_plus (cw_log PM HPM) (cw_log PP HPP))).
        * exact HR2.
        * apply RealSetoid.real_eq_plus_compat.
          -- exact HPl.
          -- apply (real_eq_trans _ (real_mult eta (cw_log (ske_pist i) (ske_Hpist i)))).
             ++ exact HPp.
             ++ apply RealSetoid.real_eq_mult_compat.
                ** apply real_eq_refl.
                ** exact (ske_log_pist i). }
  apply (ske_eq_of_log
           (real_mult (pit i)
                      (real_exp_neg (real_opp (real_mult (real_mult eta ib) (ske_adv i)))))
           (real_mult PZ (real_mult PM PP))
           (real_mult_positive (pit i)
              (real_exp_neg (real_opp (real_mult (real_mult eta ib) (ske_adv i))))
              (Hpit i)
              (real_exp_neg_pos (real_opp (real_mult (real_mult eta ib) (ske_adv i)))))
           HG).
  apply (real_eq_trans _
           (real_plus (cw_log (pit i) (Hpit i))
                      (real_plus (real_mult (real_mult eta ib) (r i))
                                 (real_plus (real_opp (real_mult eta (cw_log (pit i) (Hpit i))))
                                            (real_mult eta (cw_log (piref i) (Hpref i))))))).
  - exact (ske_logM i).
  - apply (real_eq_trans _
             (real_plus (real_mult eta (cw_log ske_Za ske_HZa))
                        (real_plus (real_mult (real_plus real_one (real_opp eta))
                                              (cw_log (pit i) (Hpit i)))
                                   (real_mult eta
                                              (real_plus (real_opp (cw_log ske_Za ske_HZa))
                                                         (real_plus (cw_log (piref i) (Hpref i))
                                                                    (real_mult ib (r i)))))))).
    + exact (ske_r_za_cancel (cw_log (pit i) (Hpit i)) (cw_log ske_Za ske_HZa)
               (cw_log (piref i) (Hpref i)) (r i) eta ib).
    + exact (real_eq_sym _ _ HR).
Qed.

(* Z level: Zrel == Za^eta * Z_int (pointwise identity ske_pt_eq + linearity) *)
Lemma ske_Zrel_eq : real_eq ske_Zrel
  (real_mult (real_pow_pos ske_Za eta ske_HZa)
             (real_interp_Z n pit ske_pist eta Hpit ske_Hpist)).
Proof.
  unfold ske_Zrel, real_interp_Z.
  apply (real_eq_trans _
           (real_list_sum nat
              (fun i => real_mult (real_pow_pos ske_Za eta ske_HZa)
                                  (real_mult
                                     (real_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i))
                                     (real_pow_pos (ske_pist i) eta (ske_Hpist i))))
              (List.seq 0 n))).
  - apply real_list_sum_ext. intro i. exact (ske_pt_eq i).
  - exact (real_list_sum_linear nat (real_pow_pos ske_Za eta ske_HZa) _
             (List.seq 0 n)).
Qed.

(* log(pi_next) == opp(eta*lZa + lz) + (lp + the ske_adv_exp shape) *)
Lemma ske_log_step : forall i : nat,
  real_eq (cw_log (ske_pnext i) (ske_Hpnext i))
          (real_plus (real_opp (real_plus (real_mult eta (cw_log ske_Za ske_HZa))
                                          (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)))
                     (real_plus (cw_log (pit i) (Hpit i))
                                (real_plus (real_mult (real_mult eta ib) (r i))
                                           (real_plus (real_opp (real_mult eta (cw_log (pit i) (Hpit i))))
                                                      (real_mult eta (cw_log (piref i) (Hpref i))))))).
Proof.
  intro i.
  pose (PZ := real_pow_pos ske_Za eta ske_HZa).
  pose (HPZ := cauchy_real_exp_pos (real_mult eta (cw_log ske_Za ske_HZa))).
  pose (HZY := real_mult_positive PZ (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) HPZ ske_HZ).
  assert (HLZeq : real_eq (cw_log ske_Zrel ske_HZrel)
                          (real_plus (real_mult eta (cw_log ske_Za ske_HZa))
                                     (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ))).
  { apply (real_eq_trans _
             (cw_log (real_mult PZ (real_interp_Z n pit ske_pist eta Hpit ske_Hpist)) HZY)).
    - apply real_log_wd.
      exact (ske_Zrel_eq).
    - apply (real_eq_trans _
               (real_plus (cw_log PZ HPZ)
                          (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ))).
      + exact (log_inv_mult_thm PZ (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) HPZ ske_HZ HZY).
      + apply RealSetoid.real_eq_plus_compat.
        * exact (ske_log_pow ske_Za eta ske_HZa).
        * apply real_eq_refl. }
  pose proof (log_inv_mult_thm (real_inv_pos ske_Zrel ske_HZrel)
                 (real_mult (pit i)
                            (real_exp_neg (real_opp (real_mult (real_mult eta ib) (ske_adv i)))))
                 (real_inv_pos_pos ske_Zrel ske_HZrel)
                 (real_mult_positive (pit i)
                    (real_exp_neg (real_opp (real_mult (real_mult eta ib) (ske_adv i))))
                    (Hpit i)
                    (real_exp_neg_pos (real_opp (real_mult (real_mult eta ib) (ske_adv i)))))
                 (ske_Hpnext i)) as H1.
  pose proof (kl_log_inv ske_Zrel ske_HZrel (real_inv_pos_pos ske_Zrel ske_HZrel)) as H2.
  apply (real_eq_trans _
           (real_plus (cw_log (real_inv_pos ske_Zrel ske_HZrel) (real_inv_pos_pos ske_Zrel ske_HZrel))
                      (cw_log (real_mult (pit i)
                                         (real_exp_neg (real_opp (real_mult (real_mult eta ib) (ske_adv i)))))
                              (real_mult_positive (pit i)
                                 (real_exp_neg (real_opp (real_mult (real_mult eta ib) (ske_adv i))))
                                 (Hpit i)
                                 (real_exp_neg_pos (real_opp (real_mult (real_mult eta ib) (ske_adv i)))))))).
  - exact H1.
  - apply RealSetoid.real_eq_plus_compat.
    + apply (real_eq_trans _ (real_opp (cw_log ske_Zrel ske_HZrel))).
      * exact H2.
      * apply RealSetoid.real_eq_opp_compat. exact HLZeq.
    + exact (ske_logM i).
Qed.

(* bridge: ske_pnext(i) == real_step_next(i) (the S15 geometric interpolation strategy) *)
Lemma ske_pnext_pt : forall i : nat,
  real_eq (ske_pnext i)
          (real_step_next n pit ske_pist eta Hpit ske_Hpist ske_HZ i).
Proof.
  intro i.
  pose (PM := real_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i)).
  pose (PP := real_pow_pos (ske_pist i) eta (ske_Hpist i)).
  pose (HPM := cauchy_real_exp_pos
                 (real_mult (real_plus real_one (real_opp eta)) (cw_log (pit i) (Hpit i)))).
  pose (HPP := cauchy_real_exp_pos (real_mult eta (cw_log (ske_pist i) (ske_Hpist i)))).
  pose (HPG := real_mult_positive PM PP HPM HPP).
  pose (HIZ := real_inv_pos_pos (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ).
  pose (HST := real_mult_positive (real_mult PM PP)
                 (real_inv_pos (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ) HPG HIZ).
  pose proof (log_inv_mult_thm (real_mult PM PP)
                 (real_inv_pos (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ) HPG HIZ HST) as HR1.
  pose proof (log_inv_mult_thm PM PP HPM HPP HPG) as HR2.
  pose proof (ske_log_pow (pit i) (real_plus real_one (real_opp eta)) (Hpit i)) as HPl.
  pose proof (ske_log_pow (ske_pist i) eta (ske_Hpist i)) as HPp.
  pose proof (kl_log_inv (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ HIZ) as Hlz.
  assert (HR : real_eq (cw_log (real_step_next n pit ske_pist eta Hpit ske_Hpist ske_HZ i) HST)
                       (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta))
                                                        (cw_log (pit i) (Hpit i)))
                                             (real_mult eta
                                                        (real_plus (real_opp (cw_log ske_Za ske_HZa))
                                                                   (real_plus (cw_log (piref i) (Hpref i))
                                                                              (real_mult ib (r i))))))
                                  (real_opp (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)))).
  { apply (real_eq_trans _
             (real_plus (cw_log (real_mult PM PP) HPG)
                        (cw_log (real_inv_pos (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ) HIZ))).
    - exact HR1.
    - apply RealSetoid.real_eq_plus_compat.
      + apply (real_eq_trans _ (real_plus (cw_log PM HPM) (cw_log PP HPP))).
        * exact HR2.
        * apply RealSetoid.real_eq_plus_compat.
          -- exact HPl.
          -- apply (real_eq_trans _ (real_mult eta (cw_log (ske_pist i) (ske_Hpist i)))).
             ++ exact (ske_log_pow (ske_pist i) eta (ske_Hpist i)).
             ++ apply RealSetoid.real_eq_mult_compat.
                ** apply real_eq_refl.
                ** exact (ske_log_pist i).
      + exact Hlz. }
  apply (ske_eq_of_log (ske_pnext i)
           (real_step_next n pit ske_pist eta Hpit ske_Hpist ske_HZ i)
           (ske_Hpnext i) HST).
  apply (real_eq_trans _
           (real_plus (real_opp (real_plus (real_mult eta (cw_log ske_Za ske_HZa))
                                           (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)))
                      (real_plus (cw_log (pit i) (Hpit i))
                                 (real_plus (real_mult (real_mult eta ib) (r i))
                                            (real_plus (real_opp (real_mult eta (cw_log (pit i) (Hpit i))))
                                                       (real_mult eta (cw_log (piref i) (Hpref i)))))))).
  - exact (ske_log_step i).
  - apply (real_eq_trans _
             (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) (cw_log (pit i) (Hpit i)))
                                   (real_mult eta
                                              (real_plus (real_opp (cw_log ske_Za ske_HZa))
                                                         (real_plus (cw_log (piref i) (Hpref i))
                                                                    (real_mult ib (r i))))))
                        (real_opp (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)))).
    + exact (ske_r_step (cw_log (pit i) (Hpit i)) (cw_log ske_Za ske_HZa)
               (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)
               (cw_log (piref i) (Hpref i)) (r i) eta ib).
    + exact (real_eq_sym _ _ HR).
Qed.

(* pi_star normalization: sum pist == 1 (the Real-level form of S05 pi_star_normalized) *)
Lemma ske_pistn : real_eq (real_list_sum nat ske_pist (List.seq 0 n)) real_one.
Proof.
  apply (real_eq_trans _
           (real_mult (real_inv_pos ske_Za ske_HZa)
                      (real_list_sum nat (fun i => real_mult (piref i) (ske_e1 i))
                                      (List.seq 0 n)))).
  - exact (real_list_sum_linear nat (real_inv_pos ske_Za ske_HZa)
             (fun i => real_mult (piref i) (ske_e1 i)) (List.seq 0 n)).
  - apply (real_eq_trans _ (real_mult (real_inv_pos ske_Za ske_HZa) ske_Za)).
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * apply real_eq_refl.
    + apply (real_eq_trans _ (real_mult ske_Za (real_inv_pos ske_Za ske_HZa))).
      * apply real_mult_comm.
      * exact (real_inv_pos_correct ske_Za ske_HZa).
Qed.

(* interpolation-piece interface: lz <= eps (S15 M1 + strict seed + the log monotonicity chain) *)
Lemma ske_lz_le_eps : forall eps : Real, real_lt real_zero eps ->
  real_le (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ) eps.
Proof.
  intros eps Heps.
  assert (HZle : real_le (real_interp_Z n pit ske_pist eta Hpit ske_Hpist)
                         (real_plus real_one eps))
    by exact (real_interp_Z_le_one_eps n pit ske_pist eta Hpit ske_Hpist
                Hpitn ske_pistn Heta Hetale eps Heps).
  assert (Honep : real_lt real_zero (real_plus real_one eps))
    by exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                (real_plus real_one eps) kl_zero_plus_zero
                (real_lt_plus_compat real_zero real_one real_zero eps
                   real_lt_zero_one Heps)).
  apply (real_le_trans _
           (cw_log (real_plus real_one eps) Honep)).
  - exact (kl_log_le_mono (real_interp_Z n pit ske_pist eta Hpit ske_Hpist)
             (real_plus real_one eps) ske_HZ Honep HZle).
  - exact (inl (real_lt_eq_lt (cw_log (real_plus real_one eps) Honep)
                  (cw_log (cauchy_real_exp eps) (cauchy_real_exp_pos eps)) eps
                  (real_log_lt_mono (real_plus real_one eps) (cauchy_real_exp eps)
                     Honep (cauchy_real_exp_pos eps) (real_exp_ge_linear eps Heps))
                  (log_inv_exp_neg_thm eps (cauchy_real_exp_pos eps)))).
Qed.

(* ============================================================ *)
(* Part 3: W5 -- the premise-free single-step contraction (the Real-level form of the three-KL composition) *)
(* ============================================================ *)

(* W5 pointwise identity: kl(pist,pnext) == (1-eta)*kl(pist,pit) + pist*logZ *)
Lemma ske_kl_pist_pnext : forall i : nat,
  real_eq (real_kl_term (ske_pist i) (ske_pnext i) (ske_Hpist i) (ske_Hpnext i))
          (real_plus (real_mult (real_plus real_one (real_opp eta))
                                (real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i)))
                     (real_mult (ske_pist i)
                                (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ))).
Proof.
  intro i.
  pose (HIvp := real_inv_pos_pos (ske_pist i) (ske_Hpist i)).
  pose (HJ := real_mult_positive (ske_pnext i)
                 (real_inv_pos (ske_pist i) (ske_Hpist i))
                 (ske_Hpnext i) HIvp).
  pose (HJ2 := real_mult_positive (pit i)
                  (real_inv_pos (ske_pist i) (ske_Hpist i))
                  (Hpit i) HIvp).
  pose proof (log_inv_mult_thm (ske_pnext i)
                 (real_inv_pos (ske_pist i) (ske_Hpist i))
                 (ske_Hpnext i) HIvp HJ) as HA.
  pose proof (log_inv_mult_thm (pit i)
                 (real_inv_pos (ske_pist i) (ske_Hpist i))
                 (Hpit i) HIvp HJ2) as HE.
  pose proof (kl_log_inv (ske_pist i) (ske_Hpist i) HIvp) as HB.
  pose proof (ske_log_step i) as HC.
  pose proof (ske_log_pist i) as HD.
  assert (HBF : real_eq (cw_log (real_inv_pos (ske_pist i) (ske_Hpist i)) HIvp)
                        (real_opp (real_plus (real_opp (cw_log ske_Za ske_HZa))
                                             (real_plus (cw_log (piref i) (Hpref i))
                                                        (real_mult ib (r i)))))).
  { apply (real_eq_trans _ (real_opp (cw_log (ske_pist i) (ske_Hpist i)))).
    - exact HB.
    - apply RealSetoid.real_eq_opp_compat. exact HD. }
  assert (HXL : real_eq
             (real_kl_term (ske_pist i) (ske_pnext i) (ske_Hpist i) (ske_Hpnext i))
             (real_mult (ske_pist i)
                        (real_opp
                           (real_plus
                              (real_plus (real_opp (real_plus (real_mult eta (cw_log ske_Za ske_HZa))
                                                              (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)))
                                         (real_plus (cw_log (pit i) (Hpit i))
                                                    (real_plus (real_mult (real_mult eta ib) (r i))
                                                               (real_plus (real_opp (real_mult eta (cw_log (pit i) (Hpit i))))
                                                                          (real_mult eta (cw_log (piref i) (Hpref i)))))))
                              (real_opp (real_plus (real_opp (cw_log ske_Za ske_HZa))
                                                   (real_plus (cw_log (piref i) (Hpref i))
                                                              (real_mult ib (r i))))))))).
  { unfold real_kl_term.
    apply RealSetoid.real_eq_mult_compat.
    + apply real_eq_refl.
    + apply RealSetoid.real_eq_opp_compat.
      apply (real_eq_trans _
               (real_plus (cw_log (ske_pnext i) (ske_Hpnext i))
                          (cw_log (real_inv_pos (ske_pist i) (ske_Hpist i)) HIvp))).
      - exact HA.
      - apply RealSetoid.real_eq_plus_compat.
        * exact HC.
        * exact HBF. }
  assert (HXR : real_eq
             (real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i))
             (real_mult (ske_pist i)
                        (real_plus (real_opp (cw_log (pit i) (Hpit i)))
                                   (real_plus (real_opp (cw_log ske_Za ske_HZa))
                                              (real_plus (cw_log (piref i) (Hpref i))
                                                         (real_mult ib (r i))))))).
  { unfold real_kl_term.
    apply RealSetoid.real_eq_mult_compat.
    + apply real_eq_refl.
    + apply (real_eq_trans _
               (real_opp (real_plus (cw_log (pit i) (Hpit i))
                                    (real_opp (real_plus (real_opp (cw_log ske_Za ske_HZa))
                                                         (real_plus (cw_log (piref i) (Hpref i)) (real_mult ib (r i)))))))).
      * apply RealSetoid.real_eq_opp_compat.
        unfold real_log.
        exact (real_eq_trans _ _ _ HE
                 (RealSetoid.real_eq_plus_compat
                    (cw_log (pit i) (Hpit i))
                    (cw_log (real_inv_pos (ske_pist i) (ske_Hpist i)) HIvp)
                    (cw_log (pit i) (Hpit i))
                    (real_opp (real_plus (real_opp (cw_log ske_Za ske_HZa))
                               (real_plus (cw_log (piref i) (Hpref i)) (real_mult ib (r i)))))
                    (real_eq_refl (cw_log (pit i) (Hpit i))) HBF)).
      * apply (real_eq_trans _
                 (real_plus (real_opp (cw_log (pit i) (Hpit i)))
                            (real_opp (real_opp (real_plus (real_opp (cw_log ske_Za ske_HZa))
                                                       (real_plus (cw_log (piref i) (Hpref i)) (real_mult ib (r i)))))))).
        -- apply ske_r_opp_split.
        -- apply RealSetoid.real_eq_plus_compat.
           ++ apply real_eq_refl.
           ++ exact (ske_opp_opp (real_plus (real_opp (cw_log ske_Za ske_HZa))
                                                                (real_plus (cw_log (piref i) (Hpref i))
                                                                           (real_mult ib (r i))))). }

  apply (real_eq_trans _
           (real_mult (ske_pist i)
                      (real_opp
                         (real_plus
                            (real_plus (real_opp (real_plus (real_mult eta (cw_log ske_Za ske_HZa))
                                                            (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)))
                                       (real_plus (cw_log (pit i) (Hpit i))
                                                  (real_plus (real_mult (real_mult eta ib) (r i))
                                                             (real_plus (real_opp (real_mult eta (cw_log (pit i) (Hpit i))))
                                                                        (real_mult eta (cw_log (piref i) (Hpref i)))))))
                            (real_opp (real_plus (real_opp (cw_log ske_Za ske_HZa))
                                                 (real_plus (cw_log (piref i) (Hpref i)) (real_mult ib (r i))))))))).
  - exact HXL.
  - apply (real_eq_trans _
             (real_plus (real_mult (real_plus real_one (real_opp eta))
                                   (real_mult (ske_pist i)
                                              (real_plus (real_opp (cw_log (pit i) (Hpit i)))
                                                         (real_plus (real_opp (cw_log ske_Za ske_HZa))
                                                                    (real_plus (cw_log (piref i) (Hpref i)) (real_mult ib (r i)))))))
                        (real_mult (ske_pist i)
                                   (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)))).
    + exact (ske_r_klpi (ske_pist i) (cw_log (pit i) (Hpit i)) (cw_log ske_Za ske_HZa)
               (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)
               (cw_log (piref i) (Hpref i)) (r i) eta ib).
    + apply RealSetoid.real_eq_plus_compat.
      * apply RealSetoid.real_eq_mult_compat.
        -- apply real_eq_refl.
        -- exact (real_eq_sym _ _ HXR).
      * apply real_eq_refl.
Qed.

(* W5 main piece (eps form): KL(pist|pnext) <= (1-eta)*KL(pist|pit) + eps *)
Theorem ske_geom_step_discharged : forall eps : Real,
  real_lt real_zero eps ->
  real_le (real_list_sum nat
             (fun i => real_kl_term (ske_pist i) (ske_pnext i) (ske_Hpist i) (ske_Hpnext i))
             (List.seq 0 n))
          (real_plus (real_mult (real_plus real_one (real_opp eta))
                                (real_list_sum nat
                                   (fun i => real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i))
                                   (List.seq 0 n)))
                     eps).
Proof.
  intros eps Heps.
  assert (Hext : real_eq
             (real_list_sum nat
                (fun i => real_kl_term (ske_pist i) (ske_pnext i) (ske_Hpist i) (ske_Hpnext i))
                (List.seq 0 n))
             (real_list_sum nat
                (fun i => real_plus (real_mult (real_plus real_one (real_opp eta))
                                                (real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i)))
                                    (real_mult (ske_pist i)
                                               (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)))
                (List.seq 0 n))).
  { apply real_list_sum_ext. intro i. exact (ske_kl_pist_pnext i). }
  assert (Hadd : real_eq
             (real_list_sum nat
                (fun i => real_plus (real_mult (real_plus real_one (real_opp eta))
                                                (real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i)))
                                    (real_mult (ske_pist i)
                                               (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)))
                (List.seq 0 n))
             (real_plus (real_list_sum nat
                            (fun i => real_mult (real_plus real_one (real_opp eta))
                                                (real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i)))
                            (List.seq 0 n))
                        (real_list_sum nat
                           (fun i => real_mult (ske_pist i)
                                               (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ))
                           (List.seq 0 n)))).
  { exact (real_list_sum_add nat _ _ (List.seq 0 n)). }
  assert (Hlin1 : real_eq
             (real_list_sum nat
                (fun i => real_mult (real_plus real_one (real_opp eta))
                                    (real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i)))
                (List.seq 0 n))
             (real_mult (real_plus real_one (real_opp eta))
                        (real_list_sum nat
                           (fun i => real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i))
                           (List.seq 0 n)))).
  { exact (real_list_sum_linear nat (real_plus real_one (real_opp eta))
             (fun i => real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i))
             (List.seq 0 n)). }
  assert (Hswap : real_eq
             (real_list_sum nat
                (fun i => real_mult (ske_pist i)
                                    (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ))
                (List.seq 0 n))
             (real_list_sum nat
                (fun i => real_mult (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)
                                    (ske_pist i))
                (List.seq 0 n))).
  { apply real_list_sum_ext. intro i. apply real_mult_comm. }
  assert (Hlin2 : real_eq
             (real_list_sum nat
                (fun i => real_mult (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)
                                    (ske_pist i))
                (List.seq 0 n))
             (real_mult (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)
                        (real_list_sum nat ske_pist (List.seq 0 n)))).
  { exact (real_list_sum_linear nat
               (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)
               ske_pist (List.seq 0 n)). }
  assert (Hnorm : real_eq
             (real_mult (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)
                        (real_list_sum nat ske_pist (List.seq 0 n)))
             (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)).
  { apply (real_eq_trans _ (real_mult
         (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ) real_one)).
    - apply RealSetoid.real_eq_mult_compat.
      + apply real_eq_refl.
      + exact ske_pistn.
    - apply real_mult_one. }
  assert (Hsum : real_eq
             (real_list_sum nat
                (fun i => real_kl_term (ske_pist i) (ske_pnext i) (ske_Hpist i) (ske_Hpnext i))
                (List.seq 0 n))
             (real_plus (real_mult (real_plus real_one (real_opp eta))
                                   (real_list_sum nat
                                      (fun i => real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i))
                                      (List.seq 0 n)))
                        (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ))).
  { exact (real_eq_trans _ _ _ Hext (real_eq_trans _ _ _ Hadd
      (RealSetoid.real_eq_plus_compat
         (real_list_sum nat
            (fun i => real_mult (real_plus real_one (real_opp eta))
                                (real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i)))
            (List.seq 0 n))
         (real_list_sum nat
            (fun i => real_mult (ske_pist i)
                                (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ))
            (List.seq 0 n))
         (real_mult (real_plus real_one (real_opp eta))
                    (real_list_sum nat
                       (fun i => real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i))
                       (List.seq 0 n)))
         (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ)
         Hlin1 (real_eq_trans _ _ _ Hswap (real_eq_trans _ _ _ Hlin2 Hnorm))))). }
  apply (real_le_trans _
           (real_plus (real_mult (real_plus real_one (real_opp eta))
                                 (real_list_sum nat
                                    (fun i => real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i))
                                    (List.seq 0 n)))
                      (cw_log (real_interp_Z n pit ske_pist eta Hpit ske_Hpist) ske_HZ))).
  - exact (inr Hsum).
  - apply real_le_plus_compat.
    + apply real_le_refl.
    + exact (ske_lz_le_eps eps Heps).
Qed.


(* W5 B form (the Bishop non-strict order, closed by the UpRealLeB closer) *)
Theorem ske_geom_step_discharged_B :
  real_le_b (real_list_sum nat
               (fun i => real_kl_term (ske_pist i) (ske_pnext i) (ske_Hpist i) (ske_Hpnext i))
               (List.seq 0 n))
            (real_mult (real_plus real_one (real_opp eta))
                       (real_list_sum nat
                          (fun i => real_kl_term (ske_pist i) (pit i) (ske_Hpist i) (Hpit i))
                          (List.seq 0 n))).
Proof.
  exact (real_le_closure_b_one _ _
    (fun eps Heps => ske_geom_step_discharged eps Heps)).
Qed.


(* ============================================================ *)
(* Part 4: W3 -- instantiation discharge of the S05 premise slots (the backstop main piece) *)
(* ============================================================ *)

(* W3 main piece (eps form): KL(pit|pi_next pit) <= eta*KL(pit|pi_star) + eps
   -- the premise-free Real-level form of the S05:4404 Variable
   step_kl_eta_bound; the certificate chain = the bridge ske_pnext_pt plus one
   feeding of the engine real_step_kl_eta_bound_eps *)
Theorem ske_step_kl_eta_bound_inst : forall eps : Real,
  real_lt real_zero eps ->
  real_le (real_list_sum nat
             (fun i => real_kl_term (pit i) (ske_pnext i) (Hpit i) (ske_Hpnext i))
             (List.seq 0 n))
          (real_plus (real_mult eta
                                (real_list_sum nat
                                   (fun i => real_kl_term (pit i) (ske_pist i) (Hpit i) (ske_Hpist i))
                                   (List.seq 0 n)))
                     eps).
Proof.
  intros eps Heps.
  apply (RealSetoid.real_le_id_l
           (real_list_sum nat
              (fun i => real_kl_term (pit i) (ske_pnext i) (Hpit i) (ske_Hpnext i))
              (List.seq 0 n))
           (real_list_sum nat
              (fun i => real_kl_term (pit i)
                         (real_step_next n pit ske_pist eta Hpit ske_Hpist ske_HZ i)
                         (Hpit i) (ske_Hqv i))
              (List.seq 0 n))
           (real_plus (real_mult eta
                                   (real_list_sum nat
                                      (fun i => real_kl_term (pit i) (ske_pist i) (Hpit i) (ske_Hpist i))
                                      (List.seq 0 n)))
                      eps)).
  - apply real_list_sum_ext. intro i.
    apply ske_kl_term_ext. exact (ske_pnext_pt i).
  - exact (real_step_kl_eta_bound_eps n pit ske_pist eta Hpit ske_Hpist
             Hpitn ske_pistn ske_HZ ske_Hqv Heta Hetale eps Heps).
Qed.

(* W3 B form (the Bishop non-strict order) *)
Theorem ske_step_kl_eta_bound_inst_B :
  real_le_b (real_list_sum nat
               (fun i => real_kl_term (pit i) (ske_pnext i) (Hpit i) (ske_Hpnext i))
               (List.seq 0 n))
            (real_mult eta
                       (real_list_sum nat
                          (fun i => real_kl_term (pit i) (ske_pist i) (Hpit i) (ske_Hpist i))
                          (List.seq 0 n))).
Proof.
  exact (real_le_closure_b_one _ _
    (fun eps Heps => ske_step_kl_eta_bound_inst eps Heps)).
Qed.


End SkeInst.

(* ============================================================ *)
(* PA audit (self-check that no new logical axiom face is added) *)
(* ============================================================ *)
Print Assumptions ske_step_kl_eta_bound_inst.
Print Assumptions ske_step_kl_eta_bound_inst_B.
Print Assumptions ske_geom_step_discharged.
Print Assumptions ske_geom_step_discharged_B.