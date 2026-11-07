(* ConstructiveWorld-Set -- LMCarrierExt: continued LM carrier slot supplies
   for the S04 language-model and thermodynamics sections. *)

(** * LMCarrierExt: engine-continued carrier slot supplies.

    Mission.  Four slot families on the engine exports
      [fa51_sumd]/[fa56_markov_kernel]/[fa56b_nonempty]: the softmax
      partition (Boltzmann [neg_log_prob], the isomorphic [sum_exp]
      fold with positivity, the denominator = temperature-partition
      bridge, normalization); the [total_loss] finite sum with
      prefix-extension monotonicity on the new engine piece
      [lmc_sumd_app]; the noise/[sigma] sampling slot on the R
      carrier (zero-noise inhabitant, [sigT] assembly, unit step);
      and the autoregressive sequence loss collapsing to the finite
      sum for prefix-independent (unigram) [nll].

    Dependencies.  Stdlib [Lists.List]; requires [S01_BaseRing],
      [fa51_sumpos_id], [fa56_id_carrier], [fa56b_ext].

    References.  ConstructiveWorld-Main, module [LMCarrierExt]
      (statement names carried over verbatim).

    Constructivity.  Statement faces are Set-level ([lt]/[le]/[Id]/
      [Not]/[sigT] are the S01 Set definitions); purely constructive,
      no admits; tail [Print Assumptions] covers every statement.

    Build.  [coqc -native-compiler no -q -Q . "" LMCarrierExt.v]
      compiles cleanly (exit 0). *)

Require Import S01_BaseRing.
Require Import fa51_sumpos_id.
Require Import fa56_id_carrier.
Require Import fa56b_ext.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section LmcCarrierExt.

Context {RI : RealInterfaceEnhanced}.

Let R        := @R RI.
Let zero     := @zero RI.
Let one      := @one RI.
Let plus     := @plus RI.
Let mult     := @mult RI.
Let opp      := @opp RI.
Let inv_pos  := @inv_pos RI.
Let le       := @le RI.
Let lt       := @lt RI.
Let exp_neg  := @exp_neg RI.

(* ============ New engine piece: sum-over-append decomposition   *)
(*   (the list-carrier isomorph of sum_over_S_add) ============   *)

Lemma lmc_sumd_app :
  forall (S : Set) (f : S -> R) (l l' : list S),
    Id (fa51_sumd S f (l ++ l')) (plus (fa51_sumd S f l) (fa51_sumd S f l')).
Proof.
  intros S f l l'. induction l as [| x t IH].
  - exact (id_trans (id_sym (plus_zero (fa51_sumd S f l')))
                    (id_sym (plus_comm zero (fa51_sumd S f l')))).
  - exact (id_trans (id_cong (fun y => plus (f x) y) IH)
                    (plus_assoc (f x) (fa51_sumd S f t) (fa51_sumd S f l'))).
Qed.

(* ============ Slot A: the S04:1470/1472/1478 softmax partition  *)
(*   slot (LM section) ============                               *)
(* Slot statement: [Variable neg_log_prob : list Token -> Token -> *)
(* R]; [Fixpoint sum_exp prefix l = sum_w exp_neg (neg_log_prob    *)
(* prefix w)].  Realization: [neg_log_prob] taken as the Boltzmann *)
(* negative log-likelihood [beta*E(w)] (unigram degenerate,        *)
(* prefix-independent); an isomorphic [sum_exp] fold plus the      *)
(* list-carrier positivity isomorph (of S04:1478                   *)
(* sum_exp_positive).                                              *)

Definition lmc_neg_log_prob (Token : Set) (loss : Token -> R) (D : R)
                            (D_pos : lt zero D) (prefix : list Token) (w : Token) : R :=
  mult (inv_pos D D_pos) (loss w).

Fixpoint lmc_sum_exp (Token : Set) (nll : list Token -> Token -> R)
                     (prefix : list Token) (l : list Token) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (exp_neg (nll prefix w)) (lmc_sum_exp Token nll prefix rest)
  end.

(* Mirror piece: the [sum_exp] fold is the [fa51_sumd] finite sum  *)
(* (the engine interface piece).                                   *)
Theorem lmc_sum_exp_eq :
  forall (Token : Set) (nll : list Token -> Token -> R) (l prefix : list Token),
    Id (lmc_sum_exp Token nll prefix l)
       (fa51_sumd Token (fun w => exp_neg (nll prefix w)) l).
Proof.
  intros Token nll l. induction l as [| w rest IH]; intros prefix.
  - exact (@id_refl R zero).
  - exact (id_cong (fun y => plus (exp_neg (nll prefix w)) y) (IH prefix)).
Qed.

(* Positivity isomorph (the list-carrier form of S04:1478): the    *)
(* softmax denominator of a nonempty sequence is strictly          *)
(* positive.                                                       *)
Theorem lmc_sum_exp_pos :
  forall (Token : Set) (nll : list Token -> Token -> R) (prefix l : list Token),
    Not (Id l (@nil Token)) -> lt zero (lmc_sum_exp Token nll prefix l).
Proof.
  intros Token nll prefix l Hne.
  exact (fa56b_lt_transport
           (fa51_sumd Token (fun w => exp_neg (nll prefix w)) l)
           (lmc_sum_exp Token nll prefix l)
           (id_sym (lmc_sum_exp_eq Token nll l prefix))
           (fa51_sumd_nonnil_pos Token (fun w => exp_neg (nll prefix w)) l Hne
              (fun w => exp_neg_pos (nll prefix w)))).
Qed.

(* Softmax-denominator = temperature-partition bridge: with        *)
(* [nll := beta*E] the vocabulary softmax denominator is the fa51  *)
(* temperature partition function (Boltzmann and softmax share     *)
(* one denominator).                                               *)
Theorem lmc_softmax_Z_bridge :
  forall (Token : Set) (vocab : list Token) (loss : Token -> R)
         (D : R) (D_pos : lt zero D) (prefix : list Token),
    Id (lmc_sum_exp Token (lmc_neg_log_prob Token loss D D_pos) prefix vocab)
       (fa51_Z_temp Token vocab loss D D_pos).
Proof.
  intros Token vocab loss D D_pos prefix.
  exact (lmc_sum_exp_eq Token (lmc_neg_log_prob Token loss D D_pos) vocab prefix).
Qed.

(* Prefix-independence of the denominator (the explicit unigram    *)
(* degenerate form): assembled both ways through the bridge piece. *)
Theorem lmc_softmax_Z_prefix_inv :
  forall (Token : Set) (vocab : list Token) (loss : Token -> R)
         (D : R) (D_pos : lt zero D) (prefix : list Token),
    Id (lmc_sum_exp Token (lmc_neg_log_prob Token loss D D_pos) prefix vocab)
       (lmc_sum_exp Token (lmc_neg_log_prob Token loss D D_pos) nil vocab).
Proof.
  intros Token vocab loss D D_pos prefix.
  exact (id_trans (lmc_softmax_Z_bridge Token vocab loss D D_pos prefix)
                  (id_sym (lmc_softmax_Z_bridge Token vocab loss D D_pos nil))).
Qed.

(* Softmax probability assembly: [Z^{-1} * e^{-nll(w)}] (the       *)
(* fa56_markov_kernel term).                                       *)
Definition lmc_softmax_prob (Token : Set) (vocab : list Token) (loss : Token -> R)
                            (D : R) (D_pos : lt zero D)
                            (HZ : lt zero (fa51_Z_temp Token vocab loss D D_pos))
                            (w : Token) : R :=
  mult (inv_pos (fa51_Z_temp Token vocab loss D D_pos) HZ)
       (exp_neg (mult (inv_pos D D_pos) (loss w))).

(* Normalization specialization (the Token/vocab coordinates of    *)
(* fa56_markov_kernel_normalized): [sum_{w in vocab} softmax(w) =  *)
(* one].                                                           *)
Theorem lmc_softmax_normalized :
  forall (Token : Set) (vocab : list Token) (loss : Token -> R)
         (D : R) (D_pos : lt zero D)
         (HZ : lt zero (fa51_Z_temp Token vocab loss D D_pos)),
    Id (fa51_sumd Token (fun w => lmc_softmax_prob Token vocab loss D D_pos HZ w) vocab)
       one.
Proof.
  intros Token vocab loss D D_pos HZ.
  exact (fa56_markov_kernel_normalized Token vocab loss D D_pos HZ).
Qed.

(* ============ Slot B: the S04:1512 total_loss slot (the         *)
(*   ArgminCorrectness section) ============                      *)
(* Slot statement: [Variable total_loss : list Token -> R].       *)
(* Realization: a per-token finite-sum assembly; the main theorem *)
(* piece is prefix-extension monotonicity (the [lmc_sumd_app]     *)
(* decomposition plus an [le] chain).                             *)

Definition lmc_total_loss (Token : Set) (tok_loss : Token -> R) (l : list Token) : R :=
  fa51_sumd Token tok_loss l.

Theorem lmc_total_loss_mirror :
  forall (Token : Set) (tok_loss : Token -> R) (l : list Token),
    Id (lmc_total_loss Token tok_loss l) (fa51_sumd Token tok_loss l).
Proof. intros Token tok_loss l. reflexivity. Qed.

(* Main theorem piece: nonnegative per-token losses give a         *)
(* nondecreasing total loss under extension (the greedy-extension  *)
(* monotonicity face).                                             *)
Theorem lmc_total_loss_ext_mono :
  forall (Token : Set) (tok_loss : Token -> R) (l : list Token) (w : Token),
    (forall v : Token, le zero (tok_loss v)) ->
    le (lmc_total_loss Token tok_loss l)
       (lmc_total_loss Token tok_loss (l ++ w :: nil)).
Proof.
  intros Token tok_loss l w Hf.
  exact (le_id_r
           (fa51_sumd Token tok_loss l)
           (plus (plus (tok_loss w) zero) (fa51_sumd Token tok_loss l))
           (fa51_sumd Token tok_loss (l ++ w :: nil))
           (id_trans (plus_comm (plus (tok_loss w) zero)
                                (fa51_sumd Token tok_loss l))
                     (id_sym (lmc_sumd_app Token tok_loss l (w :: nil))))
           (le_id_r
              (fa51_sumd Token tok_loss l)
              (plus (fa51_sumd Token tok_loss l) (plus (tok_loss w) zero))
              (plus (plus (tok_loss w) zero) (fa51_sumd Token tok_loss l))
              (plus_comm (fa51_sumd Token tok_loss l)
                         (plus (tok_loss w) zero))
              (le_id_l
                 (fa51_sumd Token tok_loss l)
                 (plus (fa51_sumd Token tok_loss l) zero)
                 (plus (fa51_sumd Token tok_loss l) (plus (tok_loss w) zero))
                 (id_sym (plus_zero (fa51_sumd Token tok_loss l)))
                 (le_plus_compat
                    (fa51_sumd Token tok_loss l) (fa51_sumd Token tok_loss l)
                    zero (plus (tok_loss w) zero)
                    (le_refl (fa51_sumd Token tok_loss l))
                    (le_id_r zero (tok_loss w) (plus (tok_loss w) zero)
                       (id_sym (plus_zero (tok_loss w))) (Hf w)))))).
Qed.

(* ============ Slot C: the S04:1799-1800 noise/sigma sampling    *)
(*   slot ============                                            *)
(* R-carrier instance (the R instance of the StateSpace fields;    *)
(* [splus]/[smult]/[sopp] are [plus]/[mult]/[opp] on the R         *)
(* carrier).  Isomorphic to the S04:1802 [sgd_step] decomposition  *)
(* shape.                                                          *)

Definition lmc_sgd_step (gradv noisev sigma : R) : R :=
  plus (mult sigma (opp gradv)) (mult sigma noisev).

Theorem lmc_sgd_step_mirror :
  forall gradv noisev sigma : R,
    Id (lmc_sgd_step gradv noisev sigma)
       (plus (mult sigma (opp gradv)) (mult sigma noisev)).
Proof. intros gradv noisev sigma. reflexivity. Qed.

(* Zero-noise degenerate piece: with [noise := zero] the step      *)
(* displacement is [sigma * force] (a [mult_zero] and [plus_zero]  *)
(* chain).                                                         *)
Theorem lmc_sgd_zero_noise :
  forall gradv sigma : R,
    Id (lmc_sgd_step gradv zero sigma) (mult sigma (opp gradv)).
Proof.
  intros gradv sigma.
  exact (id_trans (plus_comm (mult sigma (opp gradv)) (mult sigma zero))
           (id_trans (id_cong (fun y => plus y (mult sigma (opp gradv)))
                              (mult_zero sigma))
                     (id_trans (plus_comm zero (mult sigma (opp gradv)))
                               (plus_zero (mult sigma (opp gradv)))))).
Qed.

(* Slot-assembly main theorem: the noise slot is instantiable -    *)
(* the zero-noise inhabitant provides the [sigT] witness (one-step *)
(* assembly).                                                      *)
Theorem lmc_sgd_noise_slot :
  forall gradv sigma : R,
    sigT (fun noisev : R => Id (lmc_sgd_step gradv noisev sigma)
                               (mult sigma (opp gradv))).
Proof.
  intros gradv sigma.
  exact (existT _ zero (lmc_sgd_zero_noise gradv sigma)).
Qed.

(* Unit-step specialization: at [sigma := one] the deterministic   *)
(* update is [force + noise] (two [mult_one] rewrites).            *)
Theorem lmc_sgd_one_sigma :
  forall gradv noisev : R,
    Id (lmc_sgd_step gradv noisev one) (plus (opp gradv) noisev).
Proof.
  intros gradv noisev.
  exact (id_trans
           (id_cong (fun y => plus y (mult one noisev))
                    (id_trans (mult_comm one (opp gradv))
                              (mult_one (opp gradv))))
           (id_cong (fun y => plus (opp gradv) y)
                    (id_trans (mult_comm one noisev) (mult_one noisev)))).
Qed.

(* ============ Slot D: the S04:1639/1641 AR-LM sequence-loss     *)
(*   slot ============                                            *)
(* Slot statement: [Variable neg_log_prob]; the [Fixpoint          *)
(* sequence_loss_prefix] updates the prefix each step              *)
(* ([prefix ++ [w]]).  Realization: the isomorphic fold plus the   *)
(* nil/single definition pieces and the unigram-collapse main      *)
(* theorem (with prefix-independent [nll] the sequence loss is the *)
(* finite sum; the induction changes the prefix, a nontrivial      *)
(* step).                                                          *)

Fixpoint lmc_seq_loss (Token : Set) (nll : list Token -> Token -> R)
                      (prefix s : list Token) : R :=
  match s with
  | nil => zero
  | w :: rest => plus (nll prefix w) (lmc_seq_loss Token nll (prefix ++ [w]) rest)
  end.

Theorem lmc_seq_loss_nil :
  forall (Token : Set) (nll : list Token -> Token -> R) (prefix : list Token),
    Id (lmc_seq_loss Token nll prefix nil) zero.
Proof. intros Token nll prefix. exact (@id_refl R zero). Qed.

Theorem lmc_seq_loss_single :
  forall (Token : Set) (nll : list Token -> Token -> R) (prefix : list Token)
         (w : Token),
    Id (lmc_seq_loss Token nll prefix (w :: nil)) (nll prefix w).
Proof.
  intros Token nll prefix w.
  exact (id_trans (id_cong (fun y => plus (nll prefix w) y)
                           (lmc_seq_loss_nil Token nll (prefix ++ w :: nil)))
                  (plus_zero (nll prefix w))).
Qed.

(* Main theorem piece: when [nll] is prefix-independent (unigram), *)
(* the autoregressive sequence loss collapses to the finite sum.   *)
Theorem lmc_seq_loss_unigram_sumd :
  forall (Token : Set) (nll : list Token -> Token -> R),
    (forall (p : list Token) (w : Token), Id (nll p w) (nll nil w)) ->
    forall (s prefix : list Token),
      Id (lmc_seq_loss Token nll prefix s)
         (fa51_sumd Token (fun w => nll nil w) s).
Proof.
  intros Token nll Hpfx s. induction s as [| w rest IH]; intros prefix.
  - exact (@id_refl R zero).
  - exact (id_trans
             (id_cong (fun y => plus (nll prefix w) y) (IH (prefix ++ [w])))
             (id_cong (fun z => plus z (fa51_sumd Token (fun v => nll nil v) rest))
                      (Hpfx prefix w))).
Qed.

End LmcCarrierExt.

(* ============ Assumption-face closure report ============ *)

Print Assumptions lmc_sumd_app.
Print Assumptions lmc_sum_exp_eq.
Print Assumptions lmc_sum_exp_pos.
Print Assumptions lmc_softmax_Z_bridge.
Print Assumptions lmc_softmax_Z_prefix_inv.
Print Assumptions lmc_softmax_normalized.
Print Assumptions lmc_total_loss_mirror.
Print Assumptions lmc_total_loss_ext_mono.
Print Assumptions lmc_sgd_step_mirror.
Print Assumptions lmc_sgd_zero_noise.
Print Assumptions lmc_sgd_noise_slot.
Print Assumptions lmc_sgd_one_sigma.
Print Assumptions lmc_seq_loss_nil.
Print Assumptions lmc_seq_loss_single.
Print Assumptions lmc_seq_loss_unigram_sumd.
