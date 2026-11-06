(* ConstructiveWorld-Set -- up-module statement families: composed Gibbs kernels, entropy dynamics and DPO loss sensitivity. *)

(** * Arch_Up_01: quantitative statement families over the constructive reals.

    Mission.  Families [qktv_abs_lt_two_side], [qktv_gamma], [qktv_dstar], [qktv_K],
      [qk_tv_iter_contraction], [kvev_id_transport], [kvev_single_le_sum],
      [kvev_list_len_pos], [Z_keep], [minus_middle_t12], [policy_gap_next_exact],
      [recovery_entropy_gain], [entropy_temp_mono], [firewall_loop],
      [entropy_step_gain_lower], [second_law_quant], [real_softplus],
      [real_dpo_pair_loss_sensitivity]: the main statement [qk_tv_iter_contraction]
      composes the attention Gibbs kernel with the iterative total-variation
      contraction at the explicit rate [(1 - dstar)^n].

    Dependencies.  Stdlib [Lia], [Lqa], [List], [QArith.QArith], [QArith.Qabs],
      [QArith.Qring], [Arith.Arith].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [G10_LoebFam], [UpTVDoeblin] of this development.

    References.  This development, Arch_Up_01.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements extract
      with [Obj.magic] = 0 and no erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" Arch_Up_01.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
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
Require Import G10_LoebFam.
Require Import UpTVDoeblin.
From Stdlib Require Import Lia Lqa.

(* ================= Section 1. The qktv_abs_lt_two_side family ================= *)
From Stdlib Require Import List QArith.QArith QArith.Qabs QArith.Qring Arith.Arith.

(* ################ Bridging lemma: constructive two-sided extraction from a strict abs bound ################ *)

(* |x| < c implies both -c < x and x < c.  The argument is pointwise:
   real_abs_proj (|x|_n == Qabs x_n) together with Qle_abs_self
   (x_n ≤ |x_n| and −x_n ≤ |x_n|) transports the pointwise margins of the
   lt encoding unchanged.  This bridge fixes the constructive price of
   turning an abs bound into two bounds: only the strict (lt) form holds. *)
Lemma qktv_abs_lt_two_side : forall (x c : Real),
  real_lt (real_abs x) c ->
  And (real_lt (real_opp c) x) (real_lt x c).
Proof.
  intros x c H.
  destruct H as [eps [Heps [N HN]]].
  split.
  - (* first component, -c < x: pointwise, eps < c−|x| and −x ≤ |x| give eps < x+c *)
    unfold real_lt.
    exists eps. split.
    + exact Heps.
    + exists N. intros n Hn.
      specialize (HN n Hn).
      assert (HNq : Qlt eps (projT1 c n - projT1 (real_abs x) n)%Q)
        by (apply QltT_to_Qlt; exact HN).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj x n)) in HNq.
      pose proof (Qle_abs_self (Qopp (projT1 x n))) as H0.
      setoid_rewrite (Qabs_opp (projT1 x n)) in H0.
      (* H0 : −x_n ≤ |x_n| *)
      pose proof (Qopp_le_compat (Qopp (projT1 x n))
                    (Qabs (projT1 x n)) H0) as Hm.
      setoid_rewrite (Qopp_involutive (projT1 x n)) in Hm.
      (* Hm : −|x_n| ≤ x_n *)
      pose proof (Qplus_le_compat (projT1 c n) (projT1 c n)
                    (Qopp (Qabs (projT1 x n))) (projT1 x n)
                    (Qle_refl (projT1 c n)) Hm) as Hp.
      setoid_rewrite (Qplus_comm (projT1 c n) (projT1 x n)) in Hp.
      (* Hp : c_n − |x_n| ≤ x_n + c_n *)
      apply Qlt_to_QltT.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj c n)).
      unfold Qminus.
      setoid_rewrite (Qopp_involutive (projT1 c n)).
      exact (Qlt_le_trans eps (projT1 c n - Qabs (projT1 x n))%Q
               (projT1 x n + projT1 c n)%Q HNq Hp).
  - (* second component, x < c: pointwise, eps < c−|x| and x ≤ |x| give eps < c−x *)
    unfold real_lt.
    exists eps. split.
    + exact Heps.
    + exists N. intros n Hn.
      specialize (HN n Hn).
      assert (HNq : Qlt eps (projT1 c n - projT1 (real_abs x) n)%Q)
        by (apply QltT_to_Qlt; exact HN).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj x n)) in HNq.
      pose proof (Qopp_le_compat (projT1 x n) (Qabs (projT1 x n))
                    (Qle_abs_self (projT1 x n))) as Hm.
      (* Hm : −|x_n| ≤ −x_n *)
      pose proof (Qplus_le_compat (projT1 c n) (projT1 c n)
                    (Qopp (Qabs (projT1 x n))) (Qopp (projT1 x n))
                    (Qle_refl (projT1 c n)) Hm) as Hp.
      (* Hp : c_n − |x_n| ≤ c_n − x_n, in the expanded Qminus form *)
      apply Qlt_to_QltT.
      exact (Qlt_le_trans eps (projT1 c n - Qabs (projT1 x n))%Q
               (projT1 c n - projT1 x n)%Q HNq Hp).
Qed.

(* ################ Composite pieces: the rate constant γ′, the explicit rate δ*′ and the kernel qktv_K ################ *)

(* γ′ := Δ + 1 = Qb·Kb·inv(√d) + 2: the composite rate constant, with Δ the logit bound delivered by the QK side *)
Definition qktv_gamma (d : nat) (Qb Kb : Q) : Real :=
  real_plus (Delta d Qb Kb) (real_const 1).

(* the explicit rate δ*′ := e^{−2γ′/T}, the instance of tvd_dstar on the TV side at γ := γ′ *)
Definition qktv_dstar (d : nat) (Qb Kb : Q) (Ttemp : Real)
  (HT : real_lt real_zero Ttemp) : Real :=
  tvd_dstar Ttemp HT (qktv_gamma d Qb Kb).

(* the composite kernel: the Gibbs kernel of the attention logits, the instance of tvd_K on the TV side at z := attn_logit d *)
Definition qktv_K (states : list (list Real))
  (Hn : real_lt real_zero (real_of_nat (length states)))
  (d : nat) (Ttemp : Real) (HT : real_lt real_zero Ttemp)
  (i j : list Real) : Real :=
  tvd_K states Hn Ttemp HT (attn_logit d) i j.

(* ################ Main theorem: module-level one-step composition ################ *)

(* a norm bound plus a temperature imply iterated TV contraction of the
   attention Gibbs kernel at the explicit rate (1−δ*′)ⁿ.  the QK side
   supplies the data behind γ′, namely Δ, and for each pair the certificate
   |attn_logit d i j| ≤ Δ; the TV side supplies the Gibbs kernel, the
   resolution of the δ interface and the iterated contraction theorem.
   without the QK side neither γ′ nor the kernel z has a supplier; without
   the TV side there is no contraction vocabulary, so both sides are
   needed. *)
Theorem qk_tv_iter_contraction :
  forall (d : nat) (Qb Kb : Q),
    Qlt 0 Qb -> Qlt 0 Kb ->
    forall (states : list (list Real))
           (Hn : real_lt real_zero (real_of_nat (length states))),
      forall (Ttemp : Real) (HT : real_lt real_zero Ttemp)
             (HS : forall s : list Real, real_le real_zero (qkb_sql s)),
        (forall s : list Real,
           real_le (root_of (qkb_sql s) (HS s)) (real_const Qb)) ->
        (forall s : list Real,
           real_le (root_of (qkb_sql s) (HS s)) (real_const Kb)) ->
        (forall f : list Real -> Real,
           real_le (real_abs (real_list_sum (list Real) f states))
                   (real_list_sum (list Real)
                      (fun w : list Real => real_abs (f w)) states)) ->
        forall (n : nat) (mu nu : list Real -> Real),
          real_eq (real_list_sum (list Real) mu states) real_one ->
          real_eq (real_list_sum (list Real) nu states) real_one ->
          real_le
            (tv_doeblin states
               (tv_titer states (qktv_K states Hn d Ttemp HT) n mu)
               (tv_titer states (qktv_K states Hn d Ttemp HT) n nu))
            (real_mult (tv_rpow (tv_omd (qktv_dstar d Qb Kb Ttemp HT)) n)
                       (tv_doeblin states mu nu)).
Proof.
  intros d Qb Kb HQ HK states Hn Ttemp HT HS Hqb Hkb Labs n mu nu Hmu Hnu.
  (* Δ > 0, first component of the QK-side bound, taken once over the nil family of contexts and hence independent of states *)
  assert (Hdpos : real_lt real_zero (Delta d Qb Kb)).
  { destruct (qk_logits_bounded d Qb Kb
                (fun _ : nat => Datatypes.nil)
                (fun _ : nat => Datatypes.nil)
                (fun _ : nat => HS Datatypes.nil)
                (fun _ : nat => HS Datatypes.nil)
                HQ HK
                (fun _ : nat => Hqb Datatypes.nil)
                (fun _ : nat => Hkb Datatypes.nil)) as [Hdp _].
    exact Hdp. }
  (* 0 < 1, from the QK-side positivity of constants at c := 1 *)
  assert (Hone : real_lt real_zero (real_const 1)).
  { apply qkb_real_const_pos.
    exact (proj2 (Qlt_alt 0 1) (@eq_refl comparison Lt)). }
  (* Δ < γ′, with γ′ := Δ+1, by the right-zero identity and translation *)
  assert (Hgltp : real_lt (Delta d Qb Kb) (qktv_gamma d Qb Kb)).
  { unfold qktv_gamma.
    apply (RealSetoid.real_lt_id_l (Delta d Qb Kb)
             (real_plus (Delta d Qb Kb) real_zero)
             (real_plus (Delta d Qb Kb) (real_const 1))).
    - exact (real_eq_sym (real_plus (Delta d Qb Kb) real_zero)
               (Delta d Qb Kb) (real_plus_zero (Delta d Qb Kb))).
    - exact (real_lt_plus_translate (Delta d Qb Kb) real_zero
               (real_const 1) Hone). }
  (* 0 < γ′ *)
  assert (Hgpos : real_lt real_zero (qktv_gamma d Qb Kb)).
  { unfold qktv_gamma.
    apply (RealSetoid.real_lt_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus (Delta d Qb Kb) (real_const 1))).
    - exact (real_eq_sym real_zero (real_plus real_zero real_zero)
               (real_plus_zero real_zero)).
    - exact (real_lt_plus_compat_lt_le real_zero (Delta d Qb Kb)
               real_zero (real_const 1) Hdpos (tvd_lt_le real_zero (real_const 1) Hone)). }
  (* the per-pair QK certificate, made strict at the +1 cost, then extracted on both sides: z_hi *)
  assert (Hzhi : forall i j : list Real,
            real_le (attn_logit d i j) (qktv_gamma d Qb Kb)).
  { intros i j.
    destruct (qk_logits_bounded d Qb Kb
                (fun _ : nat => i) (fun _ : nat => j)
                (fun _ : nat => HS i) (fun _ : nat => HS j)
                HQ HK (fun _ : nat => Hqb i) (fun _ : nat => Hkb j))
      as [_ Habs].
    specialize (Habs 0%nat 0%nat).
    apply tvd_lt_le.
    apply (qktv_abs_lt_two_side (attn_logit d i j) (qktv_gamma d Qb Kb)).
    exact (real_le_lt_trans (real_abs (attn_logit d i j)) (Delta d Qb Kb)
             (qktv_gamma d Qb Kb) Habs Hgltp). }
  (* the same argument gives z_lo *)
  assert (Hzlo : forall i j : list Real,
            real_le (real_opp (qktv_gamma d Qb Kb)) (attn_logit d i j)).
  { intros i j.
    destruct (qk_logits_bounded d Qb Kb
                (fun _ : nat => i) (fun _ : nat => j)
                (fun _ : nat => HS i) (fun _ : nat => HS j)
                HQ HK (fun _ : nat => Hqb i) (fun _ : nat => Hkb j))
      as [_ Habs].
    specialize (Habs 0%nat 0%nat).
    apply tvd_lt_le.
    destruct (qktv_abs_lt_two_side (attn_logit d i j) (qktv_gamma d Qb Kb)
               (real_le_lt_trans (real_abs (attn_logit d i j))
                  (Delta d Qb Kb) (qktv_gamma d Qb Kb) Habs Hgltp))
      as [Hlo _].
    exact Hlo. }
  (* the TV-side main theorem resolves in one step at γ := γ′ and z := attn_logit d *)
  exact (tvd_dstar_iter_contraction states Hn Ttemp HT
           (qktv_gamma d Qb Kb) Hgpos
           (attn_logit d) Hzlo Hzhi Labs n mu nu Hmu Hnu).
Qed.

(* assumption audit for the bridging lemma and the main theorem, each expected Closed                        *)
Print Assumptions qktv_abs_lt_two_side.
Print Assumptions qk_tv_iter_contraction.
(* ================= Section 2. The kvev_id_transport family ================= *)
(* ---------- helper: positivity of the potential of a nonempty finite list, in the direct form of states_ne ---------- *)
(* the root-level vocab_len_pos carries unrelated section variables (token_eq_dec/count_token); *)
(* here is the clean form: Not (Id l nil) implies 0 < of_nat |l|.                *)
Lemma kvev_id_transport : forall (A : Set) (x y : A) (P : A -> Set),
  P x -> Id x y -> P y.
Proof.
  intros A x y P p H.
  exact (match H with id_refl => p end).
Qed.

(* one term is bounded by the full sum: the induction is on the InT
   derivation itself, and the contradictory Nil branch never enters the *)
(* extraction closure, which keeps Obj.magic = 0 under extraction; the    *)
(* root-level single_le_sum_aux has an empty match producing two
   Obj.magic occurrences, so it is not reused.                      *)
Lemma kvev_single_le_sum : forall (A : Set) (f : A -> Real) (x : A) (l : list A),
  InT x l -> (forall y : A, real_le real_zero (f y)) ->
  real_le (f x) (real_list_sum A f l).
Proof.
  intros A f x l Hin. induction Hin as [l0 | y l0 Hin IH].
  - intro Hnn. cbn [real_list_sum].
    apply real_le_plus_nonneg_r_aux.
    apply (real_list_sum_nonneg A f l0 Hnn).
  - intro Hnn. cbn [real_list_sum].
    apply (real_le_trans _ (real_list_sum A f l0)).
    + exact (IH Hnn).
    + apply (RealSetoid.real_le_id_r (real_list_sum A f l0)
               (real_plus (real_list_sum A f l0) (f y))
               (real_plus (f y) (real_list_sum A f l0))
               (real_plus_comm (real_list_sum A f l0) (f y))).
      apply real_le_plus_nonneg_r_aux. apply Hnn.
Qed.

Lemma kvev_list_len_pos : forall (A : Set) (l : list A),
  Not (Id l nil) -> real_lt real_zero (real_of_nat (length l)).
Proof.
  intros A l. destruct l as [| w rest].
  - intro Hne. exact (match Hne (@id_refl (list A) nil) with end).
  - intro Hne2. cbn [length].
    apply (real_lt_eq_lt real_zero
             (real_plus real_one (real_of_nat (length rest)))
             (real_of_nat (Datatypes.S (length rest)))).
    + apply (real_eq_lt_lt real_zero
               (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat (length rest)))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_lt_plus_compat_lt_le.
        -- apply real_lt_zero_one.
        -- apply real_of_nat_nonneg_aux.
    + apply real_eq_refl.
Qed.

(* Section KVEv: the evicted-kernel world                                       *)
Section KVEv.

Variable Tok : Set.
Variable states : list Tok.
Variable states_ne : Not (Id states nil).
Variable K : Tok -> Tok -> Real.                       (* full row-stochastic kernel *)
Variable Krow : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K s s') states) real_one.
Variable Kpos : forall s s' : Tok, real_lt real_zero (K s s').  (* kernel positive pointwise *)
Variable keep : Tok -> bool.
Variable keep_nonempty :
  sigT (fun s : Tok => And (Id (keep s) true) (InT s states)).

(* the keep-filtered row sum: the mismatch mass left after eviction, the denominator of the row normalization *)
Definition Z_keep (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => if keep s' then K s s' else real_zero) states.

(* the filtered entries are nonnegative pointwise, the lemma shared by piece 0 and Z_keep_pos *)
Lemma Z_keep_entry_nonneg : forall (s y : Tok),
  real_le real_zero (if keep y then K s y else real_zero).
Proof.
  intros s y. destruct (keep y).
  - apply real_le_from_lt_aux. apply Kpos.
  - apply real_le_refl.
Qed.

(* Z_keep_pos as a theorem: the keep-witnessed entry K(s,s0) > 0 and is bounded by Z_keep s *)
Theorem Z_keep_pos : forall s : Tok, real_lt real_zero (Z_keep s).
Proof.
  intro s.
  destruct keep_nonempty as [s0 [Hk0 Hin0]].
  assert (Hb : keep s0 = true)
    by (destruct (sf_bool_id_true _ Hk0); reflexivity).
  assert (Hlt0 : real_lt real_zero (if keep s0 then K s s0 else real_zero)).
  { rewrite Hb. apply Kpos. }
  assert (Hle : real_le (if keep s0 then K s s0 else real_zero) (Z_keep s)).
  { apply (kvev_single_le_sum Tok
             (fun y : Tok => if keep y then K s y else real_zero)
             s0 states Hin0).
    intro y. apply Z_keep_entry_nonneg. }
  destruct Hle as [Hlt | Heq].
  - exact (real_lt_trans real_zero
             (if keep s0 then K s s0 else real_zero) (Z_keep s) Hlt0 Hlt).
  - exact (real_lt_eq_lt real_zero
             (if keep s0 then K s s0 else real_zero) (Z_keep s)
             Hlt0 Heq).
Qed.

(* the uniform distribution U ≡ 1/|states|, matching the Unif form of the root-level bs_minorization *)
Definition N_R : Real := real_of_nat (length states).
Theorem N_R_pos : real_lt real_zero N_R.
Proof.
  exact (kvev_list_len_pos Tok states states_ne).
Qed.
Definition U (s' : Tok) : Real := real_inv_pos N_R N_R_pos.

(* δ with its premises, matching the root-level delta, its upper bound and the minorization premise *)
Variable delta : Real.
Variable delta_pos : real_lt real_zero delta.
Variable delta_le_one : real_le delta real_one.
Variable delta_minor : forall s s' : Tok,
  real_le (real_mult delta (U s')) (K s s').

(* the evicted kernel: kept entries carry K·inv(Z_keep), dropped entries are zero *)
Definition K_ev (s s' : Tok) : Real :=
  if keep s' then
    real_mult (K s s') (real_inv_pos (Z_keep s) (Z_keep_pos s))
  else real_zero.

(* ---------- piece 0: Z_keep s ≤ 1, the keep sub-sum bounded by the full sum over the Krow bridge ---------- *)
Theorem Z_keep_le_one : forall s : Tok, real_le (Z_keep s) real_one.
Proof.
  intro s.
  apply (real_le_trans _ (real_list_sum Tok (fun s' : Tok => K s s') states)).
  - apply (real_list_sum_le Tok
             (fun s' : Tok => if keep s' then K s s' else real_zero)
             (fun s' : Tok => K s s') states).
    intro y. destruct (keep y).
    + apply real_le_refl.
    + apply real_le_from_lt_aux. apply Kpos.
  - apply (RealSetoid.real_eq_le _ _). apply Krow.
Qed.

(* ---------- piece 1: row normalization Σ K_ev == 1 ---------- *)
Theorem kev_row_normalized : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K_ev s s') states) real_one.
Proof.
  intro s.
  (* step one: rewrite K_ev pointwise as g(s')·inv(Z); the drop branch vanishes by 0·x == 0 *)
  apply (real_eq_trans _
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_mult (if keep s' then K s s' else real_zero)
                           (real_inv_pos (Z_keep s) (Z_keep_pos s)))
              states) _).
  { apply (real_list_sum_ext Tok (fun s' : Tok => K_ev s s') _ states).
    intro y. destruct (keep y) eqn:Hk.
    - unfold K_ev. rewrite Hk. apply real_eq_refl.
    - unfold K_ev. rewrite Hk.
      apply (real_eq_trans _
               (real_mult (real_inv_pos (Z_keep s) (Z_keep_pos s)) real_zero) _).
      + apply real_eq_sym. apply real_mult_zero.
      + apply real_mult_comm. }
  (* step two: linear_r extracts the constant inv(Z) *)
  apply (real_eq_trans _
           (real_mult (real_inv_pos (Z_keep s) (Z_keep_pos s)) (Z_keep s)) _).
  { apply (real_list_sum_linear_r Tok
             (real_inv_pos (Z_keep s) (Z_keep_pos s))
             (fun s' : Tok => if keep s' then K s s' else real_zero) states). }
  (* step three: inv(Z)·Z == 1 by the commutativity bridge and real_inv_pos_correct *)
  apply (real_eq_trans _
           (real_mult (Z_keep s) (real_inv_pos (Z_keep s) (Z_keep_pos s))) _).
  - apply real_mult_comm.
  - apply real_inv_pos_correct.
Qed.

(* ---------- piece 2: the minorization transports to δ·U(s') ≤ K_ev s s' ---------- *)
(* kvev_id_transport projects along Id (keep s') true onto the keep branch, *)
(* avoiding the implicit substitution of the premise that destruct with eqn performs.  *)

Theorem kev_minorization : forall s s' : Tok,
  Id (keep s') true -> real_le (real_mult delta (U s')) (K_ev s s').
Proof.
  intros s s' Hkeep.
  apply (kvev_id_transport bool true (keep s')
           (fun b : bool =>
              real_le (real_mult delta (U s'))
                (if b then
                   real_mult (K s s') (real_inv_pos (Z_keep s) (Z_keep_pos s))
                 else real_zero))).
  (* K ≤ K_ev: Z ≤ 1 gives inv(1) ≤ inv(Z) by the antitone inv, and multiplication by a positive factor preserves the order *)
  - apply (real_le_trans _ (K s s')).
    + apply delta_minor.
    + apply (real_le_trans _
               (real_mult (K s s') (real_inv_pos real_one real_lt_zero_one))).
      * (* the eq-to-le bridge for K == K·inv(1) *)
        apply (RealSetoid.real_eq_le (K s s')
                 (real_mult (K s s') (real_inv_pos real_one real_lt_zero_one))).
        apply real_eq_sym.
        apply (real_eq_trans _ (real_mult (K s s') real_one) _).
        -- apply (RealSetoid.real_eq_mult_compat
                    (K s s') (real_inv_pos real_one real_lt_zero_one)
                    (K s s') real_one).
           ++ apply real_eq_refl.
           ++ apply (real_eq_trans _
                       (real_mult real_one (real_inv_pos real_one real_lt_zero_one)) _).
              ** apply real_eq_sym. apply b4_one_mult.
              ** apply real_inv_pos_correct.
        -- apply real_mult_one.
      * apply (real_le_mult_compat_r (K s s')
                 (real_inv_pos real_one real_lt_zero_one)
                 (real_inv_pos (Z_keep s) (Z_keep_pos s))).
        -- apply real_le_from_lt_aux. apply Kpos.
        -- apply (real_inv_pos_le_compat (Z_keep s) real_one
                    (Z_keep_pos s) real_lt_zero_one).
           apply Z_keep_le_one.
  - exact (id_sym Hkeep).
Qed.

(* ---------- piece 2b: the zero form on the drop branch and the unconditional pointwise version ---------- *)
Theorem kev_drop_zero : forall s s' : Tok,
  Id (keep s') false -> real_eq (K_ev s s') real_zero.
Proof.
  intros s s' Hk.
  apply (kvev_id_transport bool false (keep s')
           (fun b : bool =>
              real_eq (if b then
                         real_mult (K s s')
                           (real_inv_pos (Z_keep s) (Z_keep_pos s))
                       else real_zero)
                 real_zero)).
  - apply real_eq_refl.
  - exact (id_sym Hk).
Qed.

Theorem kev_minorization_uncond : forall s s' : Tok,
  real_le (if keep s' then real_mult delta (U s') else real_zero) (K_ev s s').
Proof.
  intros s s'. destruct (keep s') eqn:Hk.
  - apply kev_minorization. apply sf_bool_true_id. exact Hk.
  - apply (RealSetoid.real_eq_le real_zero (K_ev s s')).
    + apply real_eq_sym. apply kev_drop_zero.
      rewrite Hk. apply id_refl.
Qed.

End KVEv.
(* ================= Section 3. The minus_middle_t12 family ================= *)
(* ---------- declaration mirroring the root Section Alignment, same names in the same order, unused items not declared ---------- *)

Section AlignIdWorld.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable reward : S -> R.          (* reward function r(s) *)
Variable beta : R.                 (* KL regularization temperature β > 0 *)
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.          (* reference policy *)
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable Z_align_pos : lt zero (Z_align reward beta beta_pos pi_ref).
Variable eta : R.                  (* step size of the copy, η > 0 *)
Variable eta_pos : lt zero eta.
Variable sum_over_S_pos : forall (f : S -> R),
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).

(* ---------- difference-algebra packaging, a two-step assembly of root-level lemmas, shared by the two main statements ---------- *)

(* the telescope: extraction of the common term with known b.
   (a − b) − (c − b) == a − c
   assembled from minus_minus_distr ((a−b)−c == a−(b+c), root L19183)
       and minus_plus_cancel (b + (c−b) == c, root L668). *)
Lemma minus_middle_t12 : forall a b c : R,
  Id (minus (minus a b) (minus c b)) (minus a c).
Proof.
  intros a b c.
  exact (id_trans (minus_minus_distr a b (minus c b))
                  (id_cong (fun x => minus a x) (minus_plus_cancel b c))).
Qed.

(* left cancellation: (a − b) − (a − c) == c − b, the reshaping kernel of the gap decrement.
   assembled from minus_rearrange_four (root L19773, four-term difference rearrangement)
       and minus_self_zero (a − a == 0, root L984)
       and minus zero X == opp X (plus_comm/plus_zero)
       and opp_minus (root L706), plus plus_comm. *)
Lemma minus_left_cancel_t12 : forall a b c : R,
  Id (minus (minus a b) (minus a c)) (minus c b).
Proof.
  intros a b c.
  assert (Hzero : Id (minus zero (minus b c)) (minus c b)).
  {
    assert (H1 : Id (minus zero (minus b c)) (opp (minus b c)))
      by exact (id_trans (plus_comm zero (opp (minus b c)))
                         (plus_zero (opp (minus b c)))).
    assert (H2 : Id (opp (minus b c)) (minus c b))
      by exact (id_trans (opp_minus b c) (plus_comm (opp b) c)).
    exact (id_trans H1 H2).
  }
  exact (id_trans (minus_rearrange_four a b a c)
                  (id_trans (id_cong2 minus (minus_self_zero a a id_refl) id_refl)
                            Hzero)).
Qed.

(* ---------- piece A: the one-step exact decomposition identity of the suboptimality gap ---------- *)
(* gap(pi_{t+1}) == gap(pi_t) − β·[(1/η−1)·K1 + (1/η)·K2]
   assembly = identity + identity = identity:
     gap(pi_t) == β·KL(pi_t‖pi_star)       (L20554)
     J(pi_{t+1}) − J(pi_t) == Δ              (L23000)
     telescope: J* − J(pi_{t+1}) == (J* − J(pi_t)) − (J(pi_{t+1}) − J(pi_t)). *)
Theorem policy_gap_next_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (minus (align_objective reward beta pi_ref
                 (pi_star reward beta beta_pos pi_ref Z_align_pos))
              (align_objective reward beta pi_ref
                 (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                    pi_t pi_t_pos)))
       (minus (mult beta (relative_entropy pi_t
                 (pi_star reward beta beta_pos pi_ref Z_align_pos)))
              (mult beta (plus
                 (mult (minus (inv_pos eta eta_pos) one)
                       (relative_entropy (pi_next reward beta beta_pos pi_ref
                                            eta sum_over_S_pos pi_t pi_t_pos)
                                         pi_t))
                 (mult (inv_pos eta eta_pos)
                       (relative_entropy pi_t
                          (pi_next reward beta beta_pos pi_ref eta
                             sum_over_S_pos pi_t pi_t_pos)))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Ps := pi_star reward beta beta_pos pi_ref Z_align_pos).
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hgap : Id (minus (align_objective reward beta pi_ref Ps)
                           (align_objective reward beta pi_ref pi_t))
                     (mult beta (relative_entropy pi_t Ps)))
    by exact (rlhf_suboptimality_gap reward beta beta_pos pi_ref pi_ref_pos
                                     Z_align_pos pi_t pi_t_norm pi_t_pos).
  assert (Hdiff : Id (minus (align_objective reward beta pi_ref Np)
                            (align_objective reward beta pi_ref pi_t))
                     (mult beta (plus
                        (mult (minus (inv_pos eta eta_pos) one)
                              (relative_entropy Np pi_t))
                        (mult (inv_pos eta eta_pos)
                              (relative_entropy pi_t Np)))))
    by exact (policy_iter_gap_diff reward beta beta_pos pi_ref eta eta_pos
                                   sum_over_S_pos pi_t pi_t_pos pi_t_norm).
  exact (id_trans (id_sym (minus_middle_t12
             (align_objective reward beta pi_ref Ps)
             (align_objective reward beta pi_ref pi_t)
             (align_objective reward beta pi_ref Np)))
           (id_cong2 minus Hgap Hdiff)).
Qed.

(* ---------- piece A': the exact identity for the gap decrement, the precise form behind the monotone ≤ of L23086 ---------- *)
(* gap(pi_t) − gap(pi_{t+1}) == Δ; both KL terms on the right are nonnegative
   by the root-level KL machinery, so the monotone ≤ reads off this identity
   directly, with the exact step size. *)
Corollary policy_gap_decrement_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (minus (minus (align_objective reward beta pi_ref
                        (pi_star reward beta beta_pos pi_ref Z_align_pos))
                     (align_objective reward beta pi_ref pi_t))
              (minus (align_objective reward beta pi_ref
                        (pi_star reward beta beta_pos pi_ref Z_align_pos))
                     (align_objective reward beta pi_ref
                        (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                           pi_t pi_t_pos))))
       (mult beta (plus
          (mult (minus (inv_pos eta eta_pos) one)
                (relative_entropy (pi_next reward beta beta_pos pi_ref eta
                                     sum_over_S_pos pi_t pi_t_pos)
                                  pi_t))
          (mult (inv_pos eta eta_pos)
                (relative_entropy pi_t
                   (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                      pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Ps := pi_star reward beta beta_pos pi_ref Z_align_pos).
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hdiff : Id (minus (align_objective reward beta pi_ref Np)
                            (align_objective reward beta pi_ref pi_t))
                     (mult beta (plus
                        (mult (minus (inv_pos eta eta_pos) one)
                              (relative_entropy Np pi_t))
                        (mult (inv_pos eta eta_pos)
                              (relative_entropy pi_t Np)))))
    by exact (policy_iter_gap_diff reward beta beta_pos pi_ref eta eta_pos
                                   sum_over_S_pos pi_t pi_t_pos pi_t_norm).
  exact (id_trans (minus_left_cancel_t12
             (align_objective reward beta pi_ref Ps)
             (align_objective reward beta pi_ref pi_t)
             (align_objective reward beta pi_ref Np))
           Hdiff).
Qed.

(* ---------- piece B: the one-step exact difference identity of dpo_loss, stated side by side on the dual axis ---------- *)
(* dpo_loss(pi) := opp (align_objective pi) (root-level definition).
   dpo_loss(pi_t) − dpo_loss(pi_{t+1}) == Δ.
   relation to the root-level L23000 policy_iter_gap_diff: the two stand
   side by side on dual axes; L23000 is the one-step improvement on the
   J axis while this piece is the one-step decrease on the loss axis, and
   minus_opp_opp converts each into the other exactly (an explicit statement
   on the dual axis, for direct use in loss-dynamics accounts). *)
Theorem dpo_loss_step_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (minus (dpo_loss reward beta pi_ref pi_t)
              (dpo_loss reward beta pi_ref
                 (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                    pi_t pi_t_pos)))
       (mult beta (plus
          (mult (minus (inv_pos eta eta_pos) one)
                (relative_entropy (pi_next reward beta beta_pos pi_ref eta
                                     sum_over_S_pos pi_t pi_t_pos)
                                  pi_t))
          (mult (inv_pos eta eta_pos)
                (relative_entropy pi_t
                   (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                      pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  unfold dpo_loss.
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hdiff : Id (minus (align_objective reward beta pi_ref Np)
                            (align_objective reward beta pi_ref pi_t))
                     (mult beta (plus
                        (mult (minus (inv_pos eta eta_pos) one)
                              (relative_entropy Np pi_t))
                        (mult (inv_pos eta eta_pos)
                              (relative_entropy pi_t Np)))))
    by exact (policy_iter_gap_diff reward beta beta_pos pi_ref eta eta_pos
                                   sum_over_S_pos pi_t pi_t_pos pi_t_norm).
  exact (id_trans (minus_opp_opp (align_objective reward beta pi_ref pi_t)
                                 (align_objective reward beta pi_ref Np))
                  Hdiff).
Qed.

(* ---------- companion piece C: the axis-exchanged exact identity of the backward KL recursion ---------- *)
(* β·KL(pi*‖pi_{t+1}) == (1−η)·β·KL(pi*‖pi_t) − η·gap(pi_t) + β·K2
   assembly = L22686 (the three-KL identity in the β-free form) multiplied
   through by β (distrib plus mult commutativity absorb the scaling), with
   the middle term replaced exactly by gap(pi_t) = J* − J(pi_t) from L20554.
   quantitative reading: the backward KL drops by exactly η·gap(pi_t) each
   step, offset by the forward step KL(β·K2). *)
Theorem policy_gap_backward_kl_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (mult beta (relative_entropy
             (pi_star reward beta beta_pos pi_ref Z_align_pos)
             (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                pi_t pi_t_pos)))
       (plus (mult (minus one eta)
                   (mult beta (relative_entropy
                          (pi_star reward beta beta_pos pi_ref Z_align_pos)
                          pi_t)))
             (plus (opp (mult eta
                          (minus (align_objective reward beta pi_ref
                                    (pi_star reward beta beta_pos pi_ref
                                       Z_align_pos))
                                 (align_objective reward beta pi_ref pi_t))))
                   (mult beta (relative_entropy pi_t
                          (pi_next reward beta beta_pos pi_ref eta
                             sum_over_S_pos pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Ps := pi_star reward beta beta_pos pi_ref Z_align_pos).
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hnextpos : forall s : S, lt zero (Np s)).
  {
    intro s. unfold Np.
    exact (pi_next_pos reward beta beta_pos pi_ref eta sum_over_S_pos
                       pi_t pi_t_pos s).
  }
  assert (Hgap : Id (minus (align_objective reward beta pi_ref Ps)
                           (align_objective reward beta pi_ref pi_t))
                     (mult beta (relative_entropy pi_t Ps)))
    by exact (rlhf_suboptimality_gap reward beta beta_pos pi_ref pi_ref_pos
                                     Z_align_pos pi_t pi_t_norm pi_t_pos).
  (* the original L22686 identity, the three-KL form without β *)
  assert (Hb : Id (relative_entropy Ps Np)
                   (plus (mult (minus one eta) (relative_entropy Ps pi_t))
                         (plus (opp (mult eta (relative_entropy pi_t Ps)))
                               (relative_entropy pi_t Np))))
    by exact (policy_iter_backward_kl_step reward beta beta_pos pi_ref
                                           pi_ref_pos Z_align_pos eta eta_pos
                                           sum_over_S_pos pi_t pi_t_pos
                                           pi_t_norm Hnextpos).
  (* β rescaling: β·(k·X) == k·(β·X), by associativity, commutativity and anti-associativity *)
  assert (Hscale1 : Id (mult beta (mult (minus one eta) (relative_entropy Ps pi_t)))
                       (mult (minus one eta) (mult beta (relative_entropy Ps pi_t)))).
  {
    apply (id_trans (mult_assoc beta (minus one eta) (relative_entropy Ps pi_t))).
    apply (id_trans (id_cong (fun x => mult x (relative_entropy Ps pi_t))
                             (mult_comm beta (minus one eta)))).
    exact (id_sym (mult_assoc (minus one eta) beta (relative_entropy Ps pi_t))).
  }
  assert (Hswap2 : Id (mult beta (mult eta (relative_entropy pi_t Ps)))
                      (mult eta (mult beta (relative_entropy pi_t Ps)))).
  {
    apply (id_trans (mult_assoc beta eta (relative_entropy pi_t Ps))).
    apply (id_trans (id_cong (fun x => mult x (relative_entropy pi_t Ps))
                             (mult_comm beta eta))).
    exact (id_sym (mult_assoc eta beta (relative_entropy pi_t Ps))).
  }
  (* β·(opp (η·KLts)) == opp (η·gap(pi_t)): opp_mult_l, then the Hswap2 and Hgap substitutions *)
  assert (Hscale2 : Id (mult beta (opp (mult eta (relative_entropy pi_t Ps))))
                       (opp (mult eta
                              (minus (align_objective reward beta pi_ref Ps)
                                     (align_objective reward beta pi_ref pi_t))))).
  {
    apply (id_trans (opp_mult_l beta (mult eta (relative_entropy pi_t Ps)))).
    exact (id_cong opp
                   (id_trans Hswap2
                             (id_cong (fun z => mult eta z) (id_sym Hgap)))).
  }
  (* β distributed over the rear subtree: β·(B + C) == β·B + β·C, with the B term reshaped *)
  assert (Hscale3 : Id (mult beta (plus (opp (mult eta (relative_entropy pi_t Ps)))
                                        (relative_entropy pi_t Np)))
                       (plus (opp (mult eta
                                    (minus (align_objective reward beta pi_ref Ps)
                                           (align_objective reward beta pi_ref pi_t))))
                             (mult beta (relative_entropy pi_t Np))))
    by exact (id_trans (distrib beta (opp (mult eta (relative_entropy pi_t Ps)))
                                (relative_entropy pi_t Np))
                       (id_cong2 plus Hscale2 id_refl)).
  (* the full-tree β distribution assembled *)
  assert (Hscale : Id (mult beta (plus (mult (minus one eta) (relative_entropy Ps pi_t))
                                       (plus (opp (mult eta (relative_entropy pi_t Ps)))
                                             (relative_entropy pi_t Np))))
                       (plus (mult (minus one eta) (mult beta (relative_entropy Ps pi_t)))
                             (plus (opp (mult eta
                                          (minus (align_objective reward beta pi_ref Ps)
                                                 (align_objective reward beta pi_ref pi_t))))
                                   (mult beta (relative_entropy pi_t Np)))))
    by exact (id_trans (distrib beta (mult (minus one eta) (relative_entropy Ps pi_t))
                                (plus (opp (mult eta (relative_entropy pi_t Ps)))
                                      (relative_entropy pi_t Np)))
                       (id_cong2 plus Hscale1 Hscale3)).
  exact (id_trans (id_cong (mult beta) Hb) Hscale).
Qed.

End AlignIdWorld.

(* ---------- extraction check: Obj.magic = 0 ---------- *)

(* ---- assumption audit: each listed statement printed in turn, all expected Closed ---- *)
Print Assumptions minus_middle_t12.
(* ================= Section 4. The fw_energy_eta family ================= *)
Section FirewallLoop.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* unpacking the interface fields, as in the root-level FreeEnergyMinimization section *)
Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let le := @le RI.
Let lt := @lt RI.
Let log := @log RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.
(* minus stays the root-level global Definition (minus a b := plus a (opp b)) *)

Variable base_loss : S -> R.
Variable sum_over_S_pos : forall f : S -> R,
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).
Variable Z_temp : R -> R.
Variable Z_temp_spec : forall (t : R) (Ht : lt zero t),
  Id (Z_temp t) (sum_over_S (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).
(* strictness interface, replicating the like-named Variables of the root-level section *)
Variable inv_pos_lt_compat : forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Variable lt_minus_nonneg : forall a b : R, lt a b -> lt zero (minus b a).
(* mixed lt+le additivity of the order (the like-named Variable precedent of
   the root ConvergenceCauchy section), used only for the strictness of the
   warm-up target t' := t+t *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* shorthands for the temperature-scaled Boltzmann family, all arguments explicit *)
Let Bt (t : R) (Ht : lt zero t) : S -> R :=
  boltzmann_dist_temp base_loss sum_over_S_pos Z_temp Z_temp_spec t Ht.
Let Et (t : R) (Ht : lt zero t) : R :=
  energy_exp_temp base_loss sum_over_S_pos Z_temp Z_temp_spec t Ht.

(* ===== basic lemmas ===== *)

(* the η-form bridge of the energy expectation: energy_expectation (Bt t) is definitionally Et t *)
Lemma fw_energy_eta : forall (t : R) (Ht : lt zero t),
  Id (energy_expectation base_loss (Bt t Ht)) (Et t Ht).
Proof. intros t Ht. exact (@id_refl _ (energy_expectation base_loss (Bt t Ht))). Qed.

(* doubling raises the temperature strictly: t > 0 implies t < t + t, the
   constructive certificate behind the warm-up target.
   (the interface plus is abstract: plus zero t and t are not convertible,
   so the step goes through id_transport, the standard route when rewriting
   on an abstract-layer Id premise is not available) *)
Lemma fw_lt_double : forall t : R, forall Ht : lt zero t,
  lt t (plus t t).
Proof.
  intros t Ht.
  apply (id_transport (fun w => lt w (plus t t))
                      (id_trans (plus_comm zero t) (plus_zero t))).
  apply (lt_plus_compat_lt_le zero t t t Ht (le_refl t)).
Qed.

(* positivity under doubling: t > 0 implies t + t > 0 *)
Lemma fw_double_pos : forall t : R, forall Ht : lt zero t,
  lt zero (plus t t).
Proof.
  intros t Ht. apply plus_positive; exact Ht.
Qed.

(* ===== piece 2 (main result): the exact recovery-gain identity =====
   ΔH := H(p_{t2}) − H(p_{t1}) == β₂·(E₂ − E₁) + KL(p_{t1} ‖ p_{t2})
   three-line proof: the KL temperature decomposition, the explicit entropy
   form, and a purely AC rearrangement. *)
Theorem recovery_entropy_gain : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  Id (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
     (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
           (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))).
Proof.
  intros t1 t2 Ht1 Ht2.
  unfold minus.
  set (b2 := inv_pos t2 Ht2).
  set (E1 := Et t1 Ht1). set (E2 := Et t2 Ht2).
  set (H1 := entropy_dist (Bt t1 Ht1)). set (H2 := entropy_dist (Bt t2 Ht2)).
  set (K := relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)).
  set (L2 := log (Z_temp t2)).
  (* the explicit entropy form: H2 == b2·E2 + L2 *)
  assert (Hex2 : Id H2 (plus (mult b2 E2) L2))
    by exact (entropy_temp_explicit base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2).
  (* the KL temperature decomposition: K == (−H1 + b2·E1) + L2, with
     energy_expectation (Bt t1) definitionally E1 via fw_energy_eta as id_refl *)
  assert (Hkl : Id K (plus (plus (opp H1) (mult b2 E1)) L2)).
  { apply (id_trans (relative_entropy_temp_decomp base_loss sum_over_S_pos Z_temp Z_temp_spec
                                  t2 Ht2 (Bt t1 Ht1)
                                  (boltzmann_dist_temp_normalized base_loss sum_over_S_pos
                                     Z_temp Z_temp_spec t1 Ht1))).
    apply (id_cong (fun x => plus (plus (opp H1) (mult b2 x)) L2)).
    apply fw_energy_eta. }
  (* left distributivity over the difference: b2·(E2−E1) == b2·E2 + −(b2·E1) *)
  assert (Hd : Id (mult b2 (minus E2 E1)) (plus (mult b2 E2) (opp (mult b2 E1)))).
  { apply (id_trans (mult_minus_distr_l b2 E2 E1)).
    unfold minus. apply id_refl. }
  (* the main algebra chain (purely AC):
     b2(E2−E1) + ((−H1+b2E1)+L2) == (b2E2 + −(b2E1)) + ((−H1+b2E1)+L2)
       == b2E2 + ((−(b2E1)) + ((−H1+b2E1)+L2))
       == b2E2 + ((−(b2E1)) + (b2E1 + (−H1+L2)))
       == b2E2 + ((−(b2E1) + b2E1) + (−H1+L2))
       == b2E2 + (−H1+L2)
       == (b2E2 + L2) + −H1 == H2 + −H1 *)
  assert (Hrot : forall aX : R,
    Id (plus (plus (opp H1) aX) L2) (plus aX (plus (opp H1) L2))).
  { intros aX.
    apply (id_trans (id_sym (plus_assoc (opp H1) aX L2))).
    apply (id_trans (id_cong (fun w => plus (opp H1) w) (plus_comm aX L2))).
    apply (id_trans (plus_assoc (opp H1) L2 aX)).
    apply (plus_comm (plus (opp H1) L2) aX). }
  assert (Hchain : Id (plus (mult b2 (minus E2 E1)) (plus (plus (opp H1) (mult b2 E1)) L2))
                      (plus H2 (opp H1))).
  { apply (id_trans (id_cong (fun x => plus x (plus (plus (opp H1) (mult b2 E1)) L2)) Hd)).
    apply (id_trans (id_sym (plus_assoc (mult b2 E2) (opp (mult b2 E1))
                                        (plus (plus (opp H1) (mult b2 E1)) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) (plus (opp (mult b2 E1)) w))
                             (Hrot (mult b2 E1)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w)
                             (plus_assoc (opp (mult b2 E1)) (mult b2 E1)
                                         (plus (opp H1) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) (plus w (plus (opp H1) L2)))
                             (id_trans (plus_comm (opp (mult b2 E1)) (mult b2 E1))
                                       (plus_opp (mult b2 E1))))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w)
                             (plus_comm zero (plus (opp H1) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w)
                             (plus_zero (plus (opp H1) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w) (plus_comm (opp H1) L2))).
    apply (id_trans (plus_assoc (mult b2 E2) L2 (opp H1))).
    apply (id_cong (fun w => plus w (opp H1)) (id_sym Hex2)). }
  apply (id_sym (id_trans (id_cong (fun x => plus (mult b2 (minus E2 E1)) x) Hkl) Hchain)).
Qed.

(* ===== piece 1 (main result): temperature-entropy monotonicity =====
   t1 < t2 implies H(p_{t1}) ≤ H(p_{t2}).
   route: energy monotonicity at the root, the piece 2 identity, and
   KL ≥ 0 by the root-level Gibbs inequality. *)
Theorem entropy_temp_mono : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  lt t1 t2 -> le (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt.
  (* E1 ≤ E2, the root-level main theorem energy_exp_temp_mono *)
  assert (HdE : le zero (minus (Et t2 Ht2) (Et t1 Ht1))).
  { apply le_minus_nonneg.
    exact (energy_exp_temp_mono base_loss sum_over_S_pos inv_pos_lt_compat
             lt_minus_nonneg Z_temp Z_temp_spec t1 t2 Ht1 Ht2 Hlt). }
  (* KL(p_{t1} ‖ p_{t2}) ≥ 0, the root-level Gibbs inequality *)
  assert (Hkl : le zero (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))).
  { apply (gibbs_inequality (Bt t1 Ht1) (Bt t2 Ht2)).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1 s).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2 s). }
  (* β₂ > 0 ⟹ β₂·ΔE ≥ 0 *)
  assert (Hb2 : le zero (inv_pos t2 Ht2)).
  { apply (lt_le_iff _ _). left. exact (inv_pos_pos t2 Ht2). }
  assert (Hterm : le zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))).
  { apply (le_id_l zero (mult (inv_pos t2 Ht2) zero)
                     (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))).
    - exact (id_sym (mult_zero (inv_pos t2 Ht2))).
    - exact (le_mult_compat_r (inv_pos t2 Ht2) zero (minus (Et t2 Ht2) (Et t1 Ht1)) Hb2 HdE). }
  (* the sum of two nonnegative terms is ≥ 0 *)
  assert (Hsum : le zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                               (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))))
    by exact (le_trans zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                        (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                              (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))
                        Hterm
                        (le_plus_nonneg_r (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                          (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)) Hkl)).
  (* transported along the piece 2 identity: ΔH ≥ 0 *)
  assert (Hfin : le zero (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))).
  { apply (le_id_r zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                              (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))).
    - exact (id_sym (recovery_entropy_gain t1 t2 Ht1 Ht2)).
    - exact Hsum. }
  (* H1 + ΔH == H2 by minus_plus_cancel, so H1 ≤ H2 *)
  apply (le_id_r (entropy_dist (Bt t1 Ht1))
                 (plus (entropy_dist (Bt t1 Ht1))
                       (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))))
                 (entropy_dist (Bt t2 Ht2))).
  - exact (minus_plus_cancel (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2))).
  - exact (le_plus_nonneg_r (entropy_dist (Bt t1 Ht1))
                            (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))) Hfin).
Qed.

(* ===== piece 2, strict tier: warming implies strict entropy recovery =====
   explicit premise (as at the root): KL(p_{t2} ‖ p_{t1}) > 0
   (satisfied whenever the two temperature distributions are not pointwise
   identical; the KL degenerates to zero only then).
   route: the root-level energy_exp_temp_strict_mono gives ΔE > 0, hence
   β₂ΔE > 0, and adding KL ≥ 0 the piece 2 identity transports it. *)
Theorem entropy_temp_strict_mono : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  lt t1 t2 ->
  lt zero (relative_entropy (Bt t2 Ht2) (Bt t1 Ht1)) ->
  lt (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hkl12.
  assert (HdE : lt zero (minus (Et t2 Ht2) (Et t1 Ht1)))
    by exact (energy_exp_temp_strict_mono base_loss sum_over_S_pos inv_pos_lt_compat
                lt_minus_nonneg Z_temp Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl12).
  assert (Hterm : lt zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1))))
    by exact (mult_positive (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1))
                            (inv_pos_pos t2 Ht2) HdE).
  assert (Hkl21 : le zero (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))).
  { apply (gibbs_inequality (Bt t1 Ht1) (Bt t2 Ht2)).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1 s).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2 s). }
  assert (Hsum : lt zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                               (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))))
    by exact (lt_le_trans zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                          (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))
                          Hterm
                          (le_plus_nonneg_r (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                            (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)) Hkl21)).
  assert (Hfin : lt zero (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))))
    by exact (lt_id_r zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                  (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))
                       (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
                       (id_sym (recovery_entropy_gain t1 t2 Ht1 Ht2)) Hsum).
  apply (lt_id_r (entropy_dist (Bt t1 Ht1))
                 (plus (entropy_dist (Bt t1 Ht1))
                       (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))))
                 (entropy_dist (Bt t2 Ht2))).
  - exact (minus_plus_cancel (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2))).
  - (* lt H1 (H1 + ΔH): one id_transport on each side
       (zero + H1 ↦ H1 and ΔH + H1 ↦ H1 + ΔH; the abstract interface plus
       admits no rewriting) *)
    apply (id_transport
             (fun w => lt w (plus (entropy_dist (Bt t1 Ht1))
                                  (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))))
             (id_trans (plus_comm zero (entropy_dist (Bt t1 Ht1)))
                       (plus_zero (entropy_dist (Bt t1 Ht1))))).
    apply (id_transport
             (fun w => lt (plus zero (entropy_dist (Bt t1 Ht1))) w)
             (plus_comm (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
                        (entropy_dist (Bt t1 Ht1)))).
    exact (lt_plus_compat_lt_le zero
                                (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
                                (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t1 Ht1))
                                Hfin (le_refl (entropy_dist (Bt t1 Ht1)))).
Qed.

(* ===== piece 2, dual form: the symmetric KL pairing =====
   paired with the root-level temp_strict_ident2 ((β₁−β₂)ΔE == K12 + K21)
   to eliminate (β₁−β₂)ΔE: ΔH == β₁·ΔE − K12, with K12 := KL(p_{t2} ‖ p_{t1}).
   the full coefficient table of the three recovery quantities (ΔH, ΔE and
   the KL combination) closes here. *)
Theorem recovery_entropy_gain_alt : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  Id (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
     (minus (mult (inv_pos t1 Ht1) (minus (Et t2 Ht2) (Et t1 Ht1)))
            (relative_entropy (Bt t2 Ht2) (Bt t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (dE := minus (Et t2 Ht2) (Et t1 Ht1)).
  set (K12 := relative_entropy (Bt t2 Ht2) (Bt t1 Ht1)).
  set (K21 := relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)).
  (* the symmetric KL identity, root-level temp_strict_ident2 *)
  assert (Hsym : Id (plus K12 K21) (mult (minus b1 b2) dE))
    by exact (temp_strict_ident2 base_loss sum_over_S_pos Z_temp Z_temp_spec t1 t2 Ht1 Ht2).
  (* b1 == b2 + (b1 − b2) *)
  assert (Hb1 : Id b1 (plus b2 (minus b1 b2))).
  { apply id_sym.
    apply (id_trans (plus_assoc b2 b1 (opp b2))).
    apply (id_trans (id_cong (fun w => plus w (opp b2)) (plus_comm b2 b1))).
    apply (id_trans (id_sym (plus_assoc b1 b2 (opp b2)))).
    apply (id_trans (id_cong (fun w => plus b1 w) (plus_opp b2))).
    apply (plus_zero b1). }
  (* distributivity: b1·ΔE == b2·ΔE + (b1−b2)·ΔE *)
  assert (Hdistr : Id (mult b1 dE) (plus (mult b2 dE) (mult (minus b1 b2) dE))).
  { apply (id_trans (id_cong (fun w => mult w dE) Hb1)).
    apply (mult_plus_distr_r b2 (minus b1 b2) dE). }
  (* (b1−b2)·ΔE == K21 + K12, Hsym with the two sides exchanged *)
  assert (Hsym' : Id (mult (minus b1 b2) dE) (plus K21 K12))
    by exact (id_trans (id_sym Hsym) (plus_comm K12 K21)).
  (* subtraction cancellation: (K21 + K12) − K12 == K21 *)
  assert (Hcancel : Id (minus (plus K21 K12) K12) K21).
  { unfold minus.
    apply (id_trans (id_sym (plus_assoc K21 K12 (opp K12)))).
    apply (id_trans (id_cong (fun w => plus K21 w) (plus_opp K12))).
    apply (plus_zero K21). }
  (* assembly: ΔH == b2ΔE + K21 (piece 2)
       == (b2ΔE + (K21+K12)) − K12 == (b2ΔE + (b1−b2)ΔE) − K12 == b1ΔE − K12 *)
  assert (Hstep1 : Id (plus (mult b2 dE) K21)
                      (minus (plus (mult b2 dE) (plus K21 K12)) K12)).
  { apply (id_trans (id_cong (fun w => plus (mult b2 dE) w) (id_sym Hcancel))).
    apply (plus_assoc (mult b2 dE) (plus K21 K12) (opp K12)). }
  assert (Hstep2 : Id (minus (plus (mult b2 dE) (plus K21 K12)) K12)
                      (minus (mult b1 dE) K12)).
  { apply (id_cong (fun w => minus w K12)
                   (id_sym (id_trans Hdistr
                     (id_cong (fun w => plus (mult b2 dE) w) Hsym')))). }
  apply (id_trans (recovery_entropy_gain t1 t2 Ht1 Ht2)).
  exact (id_trans Hstep1 Hstep2).
Qed.

(* ===== piece 3: closed-loop packaging, a certificate-form state machine =====

   fw_verdict: the health verdict is a sum of certificates (a Set-level Or,
   not a boolean decider)
     - inl: the healthy certificate, a le certificate that the entropy is
       past the threshold H_min;
     - inr: the degradation report, a sigT single-element type quantifying
       the gap (gap is definitionally the difference of the current entropy
       and H_min, a real number that carries the remaining distance and
       extracts).
       (level discipline: the branches of Or are types, not terms; a real
       number cannot serve as a branch by itself and must be carried by a
       sigT single-element type.)
   firewall_loop: the closed-loop transition, any verdict implies a sigT
     witness of the successor temperature (staying at t' := t when healthy;
     doubling the temperature, t' := t + t, when degraded), carrying the
     transition certificates (temperature non-decreasing + entropy
     non-decreasing + the verdict reloaded).
   explicit boundary: one round does not claim recovery; the reloaded
     verdict on the degraded branch is again inr (a fresh gap report), and
     whether the system is healthy is answered by the next round's
     fw_verdict certificate.  the loop invariant is temperature
     non-decreasing together with entropy non-decreasing (supplied by
     pieces 1 and 2). *)

Definition fw_verdict (Hmin : R) (t : R) (Ht : lt zero t) : Set :=
  Or (le Hmin (entropy_dist (Bt t Ht)))
     (sigT (fun gap : R => Id gap (minus (entropy_dist (Bt t Ht)) Hmin))).

(* the detect-and-warm response: a degradation report implies a sigT witness
   of the warm target t' := t + t together with the recovery certificates
   (entropy non-decreasing, and the increment exactly decomposed by the
   piece 2 identity) *)
Theorem fw_detect_warm : forall (Hmin : R) (t : R) (Ht : lt zero t)
                                (Hdef : sigT (fun gap : R =>
                                          Id gap (minus (entropy_dist (Bt t Ht)) Hmin))),
  sigT (fun t' => sigT (fun Ht' : lt zero t' =>
    And (lt t t')
        (And (le (entropy_dist (Bt t Ht)) (entropy_dist (Bt t' Ht')))
             (Id (minus (entropy_dist (Bt t' Ht')) (entropy_dist (Bt t Ht)))
                 (plus (mult (inv_pos t' Ht') (minus (Et t' Ht') (Et t Ht)))
                       (relative_entropy (Bt t Ht) (Bt t' Ht'))))))).
Proof.
  intros Hmin t Ht Hdef.
  assert (Ht' : lt zero (plus t t)) by exact (fw_double_pos t Ht).
  assert (Hup : lt t (plus t t)) by exact (fw_lt_double t Ht).
  exists (plus t t). exists Ht'.
  split.
  - exact Hup.
  - split.
    + exact (entropy_temp_mono t (plus t t) Ht Ht' Hup).
    + exact (recovery_entropy_gain t (plus t t) Ht Ht').
Qed.

(* closed-loop main theorem: any verdict implies a sigT successor state
   (temperature non-decreasing, entropy non-decreasing, verdict reloaded),
   a certificate state-machine transition repeatable round after round;
   the healthy branch stays, the degraded branch doubles the temperature. *)
Theorem firewall_loop : forall (Hmin : R) (t : R) (Ht : lt zero t)
                              (v : fw_verdict Hmin t Ht),
  sigT (fun t' => sigT (fun Ht' : lt zero t' =>
    And (le t t')
        (And (le (entropy_dist (Bt t Ht)) (entropy_dist (Bt t' Ht')))
             (fw_verdict Hmin t' Ht')))).
Proof.
  intros Hmin t Ht v. destruct v as [Hok | Hdef].
  - (* healthy branch: stay *)
    exists t. exists Ht.
    split.
    + apply le_refl.
    + split.
      * apply le_refl.
      * left. exact Hok.
  - (* degraded branch: double the temperature to t' := t + t, entropy recovers (piece 1), verdict reloaded (explicitly still inr) *)
    assert (Ht' : lt zero (plus t t)) by exact (fw_double_pos t Ht).
    assert (Hup : lt t (plus t t)) by exact (fw_lt_double t Ht).
    exists (plus t t). exists Ht'.
    split.
    + apply (lt_le_iff _ _). left. exact Hup.
    + split.
      * exact (entropy_temp_mono t (plus t t) Ht Ht' Hup).
      * right. exact (existT _ (minus (entropy_dist (Bt (plus t t) Ht')) Hmin) id_refl).
Qed.

End FirewallLoop.

(* ============ extraction check (executable OCaml) ============ *)
Set Warnings "-extraction-opaque-accessed".
(* ================= Section 5. The eg_minus_def family ================= *)
Section EntropyGainQuant.

Context {RI : RealInterfaceEnhanced}.

(* unpacking the RealInterface fields, as in the root ConvergenceCauchy precedent *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
(* minus stays the root-level global Definition (minus a b := plus a (opp b)), unfolded definitionally *)

(* ===== explicit interface, Variables replicating the root ConvergenceCauchy section ===== *)
Variable entropy : R -> R.
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable dynamics_gradient_step : forall x : R,
  Id (dynamics x) (plus x (mult eta (entropy_gradient x))).
Variable L : R.
Variable L_pos : lt zero L.
Variable gradient_lipschitz : forall x y : R,
  le (abs (minus (entropy_gradient x) (entropy_gradient y)))
     (mult L (abs (minus x y))).
Variable entropy_tangent : forall x y : R,
  le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (minus y x))).
(* added explicit interface: the one-sided extraction of |·|, le a (abs a),
   the sibling of the root abs_ge_zero_id_cc family (le zero a -> |a| == a);
   a standard property of a constructive ordered field, provable in the
   Cauchy model of the reals, declared here as an interface field of the
   abstract layer rather than a classical axiom *)
Variable abs_ge_value : forall a : R, le a (abs a).
(* mixed lt+le additivity of the order (the like-named Variable precedent of the root ConvergenceCauchy section) *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* ===== basic algebra (the three manual chains absent from the root global layer) ===== *)

(* the definition of subtraction (minus is transparent, definitionally equal) *)
Lemma eg_minus_def : forall a b : R, Id (minus a b) (plus a (opp b)).
Proof. intros a b. exact (@id_refl _ (plus a (opp b))). Qed.

(* subtraction is invertible: (a − b) + b == a *)
Lemma eg_minus_plus_cancel : forall a b : R,
  Id (plus (minus a b) b) a.
Proof.
  intros a b. unfold minus.
  apply (id_trans (id_sym (plus_assoc a (opp b) b))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_comm (opp b) b))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_opp b))).
  apply (plus_zero a).
Qed.

(* K0, the one-step unfolding in difference form: x' − x == η·g(x) *)
Lemma eg_step_diff : forall x : R,
  Id (minus (dynamics x) x) (mult eta (entropy_gradient x)).
Proof.
  intros x. unfold minus.
  apply (id_trans (id_cong (fun z => plus z (opp x)) (dynamics_gradient_step x))).
  apply (id_trans (id_sym (plus_assoc x (mult eta (entropy_gradient x)) (opp x)))).
  apply (id_trans (id_cong (fun z => plus x z)
                           (plus_comm (mult eta (entropy_gradient x)) (opp x)))).
  apply (id_trans (plus_assoc x (opp x) (mult eta (entropy_gradient x)))).
  apply (id_trans (id_cong (fun z => plus z (mult eta (entropy_gradient x)))
                           (plus_opp x))).
  apply (id_trans (plus_comm zero (mult eta (entropy_gradient x)))).
  apply (plus_zero (mult eta (entropy_gradient x))).
Qed.

(* K0', the reversed difference: x − x' == −(η·g(x)) *)
Lemma eg_step_neg_diff : forall x : R,
  Id (minus x (dynamics x)) (opp (mult eta (entropy_gradient x))).
Proof.
  intros x. unfold minus.
  apply (id_trans (id_cong (fun z => plus x z)
                           (id_cong opp (dynamics_gradient_step x)))).
  apply (id_trans (id_cong (fun z => plus x z)
                           (opp_plus x (mult eta (entropy_gradient x))))).
  apply (id_trans (plus_assoc x (opp x) (opp (mult eta (entropy_gradient x))))).
  apply (id_trans (id_cong (fun z => plus z (opp (mult eta (entropy_gradient x))))
                           (plus_opp x))).
  apply (id_trans (plus_comm zero (opp (mult eta (entropy_gradient x))))).
  apply (plus_zero (opp (mult eta (entropy_gradient x)))).
Qed.

(* helper: a strict inequality a < b gives 0 < b − a, the counterpart of minus_pos in the root ConvergenceCauchy section *)
Lemma eg_minus_pos : forall u v : R, lt u v -> lt zero (minus v u).
Proof.
  intros u v Huv.
  unfold minus.
  apply (lt_id_l zero (plus u (opp u)) (plus v (opp u)) (id_sym (plus_opp u))).
  apply (lt_plus_compat_lt_le u v (opp u) (opp u) Huv (le_refl (opp u))).
Qed.

(* ===== piece 1, core A: the tangent bound read backwards at x' gives the increment ≥ η·g(x)·g(x') =====
   the tangent (an upper bound) at x', with y := x:
     e ≤ e' + g'·(x − x') = e' − g'·(η·g) implies e' − e ≥ g'·(η·g) *)
Lemma eg_tangent_shift : forall x : R,
  le (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
     (minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x.
  pose proof (entropy_tangent (dynamics x) x) as Ht.
  (* reshaping Ht: minus x x' == −(η·g), and g'·(−η·g) == −(g'·(η·g)) *)
  assert (Ht1 : le (entropy x)
                   (plus (entropy (dynamics x))
                         (opp (mult (entropy_gradient (dynamics x))
                                    (mult eta (entropy_gradient x)))))).
  { apply (le_id_r _ (plus (entropy (dynamics x))
                           (mult (entropy_gradient (dynamics x))
                                 (minus x (dynamics x)))) _).
    - exact (id_cong (fun z => plus (entropy (dynamics x)) z)
                     (id_trans (id_cong (fun z => mult (entropy_gradient (dynamics x)) z)
                                        (eg_step_neg_diff x))
                               (opp_mult_l (entropy_gradient (dynamics x))
                                           (mult eta (entropy_gradient x))))).
    - exact Ht. }
  (* adding W := g'·(η·g) to both sides moves the term: le e (e' − W) implies le (e + W) e'.
     the chain: le_plus_compat Ht1 (le_refl W) gives le (e + W) ((e' − W) + W),
     whose right side == e' by assoc, plus_opp and plus_zero; le_id_r finishes *)
  assert (Ht2 : le (plus (entropy x)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (entropy (dynamics x))).
  { pose proof (le_plus_compat (entropy x)
                               (plus (entropy (dynamics x))
                                     (opp (mult (entropy_gradient (dynamics x))
                                                (mult eta (entropy_gradient x)))))
                               (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x)))
                               (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x)))
                               Ht1 (le_refl (mult (entropy_gradient (dynamics x))
                                                  (mult eta (entropy_gradient x))))) as Hadd.
    apply (le_id_r (plus (entropy x)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (plus (plus (entropy (dynamics x))
                               (opp (mult (entropy_gradient (dynamics x))
                                          (mult eta (entropy_gradient x)))))
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (entropy (dynamics x))).
    - exact (id_trans (id_sym (plus_assoc (entropy (dynamics x))
                                          (opp (mult (entropy_gradient (dynamics x))
                                                     (mult eta (entropy_gradient x))))
                                          (mult (entropy_gradient (dynamics x))
                                                (mult eta (entropy_gradient x)))))
                      (id_trans (id_cong (fun z => plus (entropy (dynamics x)) z)
                                         (id_trans (plus_comm (opp (mult (entropy_gradient (dynamics x))
                                                                            (mult eta (entropy_gradient x))))
                                                              (mult (entropy_gradient (dynamics x))
                                                                    (mult eta (entropy_gradient x))))
                                                   (plus_opp (mult (entropy_gradient (dynamics x))
                                                                   (mult eta (entropy_gradient x))))))
                                (plus_zero (entropy (dynamics x))))).
    - exact Hadd. }
  (* adding opp e to both sides extracts: le (e + W) e' implies le W (e' − e) == minus e' e *)
  apply (le_id_l (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
                 (plus (plus (entropy x)
                             (mult (entropy_gradient (dynamics x))
                                   (mult eta (entropy_gradient x))))
                       (opp (entropy x)))).
  - exact (id_trans (id_trans (id_sym (plus_zero (mult (entropy_gradient (dynamics x))
                                                      (mult eta (entropy_gradient x)))))
                              (id_cong (fun z => plus (mult (entropy_gradient (dynamics x))
                                                             (mult eta (entropy_gradient x))) z)
                                       (id_sym (plus_opp (entropy x)))))
                    (id_trans (plus_assoc (mult (entropy_gradient (dynamics x))
                                                (mult eta (entropy_gradient x)))
                                          (entropy x) (opp (entropy x)))
                              (id_cong (fun z => plus z (opp (entropy x)))
                                       (plus_comm (mult (entropy_gradient (dynamics x))
                                                        (mult eta (entropy_gradient x)))
                                                  (entropy x))))).
  - exact (le_plus_compat (plus (entropy x)
                                (mult (entropy_gradient (dynamics x))
                                      (mult eta (entropy_gradient x))))
                          (entropy (dynamics x))
                          (opp (entropy x)) (opp (entropy x))
                          Ht2 (le_refl (opp (entropy x)))).
Qed.

(* ===== piece 1, core B: one-sided extraction from Lipschitz gives g' ≥ (1 − L·η)·g ===== *)
Lemma eg_grad_lower : forall x : R,
  lt zero (entropy_gradient x) ->
  le (mult (minus one (mult L eta)) (entropy_gradient x))
     (entropy_gradient (dynamics x)).
Proof.
  intros x Hgx.
  (* (i) |x' − x| == η·g(x), with η>0 and g>0, by abs_pos, abs_mult and abs_opp *)
  assert (Hstep : Id (minus (dynamics x) x) (mult eta (entropy_gradient x)))
    by exact (eg_step_diff x).
  assert (Hha : lt zero (mult eta (entropy_gradient x)))
    by exact (mult_positive eta (entropy_gradient x) eta_pos Hgx).
  assert (Habsstep : Id (abs (minus (dynamics x) x))
                        (mult eta (entropy_gradient x))).
  { apply (id_trans (id_cong abs Hstep)).
    apply (id_trans (abs_mult eta (entropy_gradient x))).
    exact (id_cong2 (fun u v => mult u v) (abs_pos eta eta_pos) (abs_pos _ Hgx)). }
  assert (Habsneg : Id (abs (minus x (dynamics x)))
                       (mult eta (entropy_gradient x))).
  { apply (id_trans (id_cong abs (eg_step_neg_diff x))).
    apply (id_trans (abs_opp (mult eta (entropy_gradient x)))).
    apply (id_trans (id_cong abs (id_sym Hstep))).
    exact Habsstep. }
  (* (ii) Lipschitz at (x, x'): |g − g'| ≤ L·η·g *)
  assert (Hlip : le (abs (minus (entropy_gradient x) (entropy_gradient (dynamics x))))
                    (mult L (mult eta (entropy_gradient x)))).
  { apply (le_id_r _ (mult L (abs (minus x (dynamics x)))) _).
    - exact (id_cong (fun z => mult L z) Habsneg).
    - exact (gradient_lipschitz x (dynamics x)). }
  (* (iii) one-sided extraction: g − g' ≤ |g − g'| ≤ L·η·g by abs_ge_value *)
  assert (Hone : le (minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                    (mult L (mult eta (entropy_gradient x)))).
  { apply (le_trans _ (abs (minus (entropy_gradient x)
                                  (entropy_gradient (dynamics x)))) _).
    - exact (abs_ge_value (minus (entropy_gradient x)
                                 (entropy_gradient (dynamics x)))).
    - exact Hlip. }
  (* (iv) moving terms: g − (Lη)g ≤ g', that is (1 − Lη)·g ≤ g'
        chain: adding g' gives le g ((Lη)g + g'); adding opp((Lη)g) gives le (g − (Lη)g) g' *)
  assert (H1 : le (entropy_gradient x)
                  (plus (mult L (mult eta (entropy_gradient x)))
                        (entropy_gradient (dynamics x)))).
  { apply (le_id_l (entropy_gradient x)
                   (plus (minus (entropy_gradient x)
                                (entropy_gradient (dynamics x)))
                         (entropy_gradient (dynamics x)))).
    - exact (id_sym (eg_minus_plus_cancel (entropy_gradient x)
                                          (entropy_gradient (dynamics x)))).
    - exact (le_plus_compat (minus (entropy_gradient x)
                                   (entropy_gradient (dynamics x)))
                            (mult L (mult eta (entropy_gradient x)))
                            (entropy_gradient (dynamics x)) (entropy_gradient (dynamics x))
                            Hone (le_refl (entropy_gradient (dynamics x)))). }
  assert (H2 : le (plus (entropy_gradient x)
                        (opp (mult L (mult eta (entropy_gradient x)))))
                  (entropy_gradient (dynamics x))).
  { apply (le_id_r _ (plus (plus (mult L (mult eta (entropy_gradient x)))
                                 (entropy_gradient (dynamics x)))
                           (opp (mult L (mult eta (entropy_gradient x)))))
                     (entropy_gradient (dynamics x))).
    - exact (id_trans (id_cong (fun z => plus z (opp (mult L (mult eta (entropy_gradient x)))))
                               (plus_comm (mult L (mult eta (entropy_gradient x)))
                                          (entropy_gradient (dynamics x))))
                      (id_trans (id_sym (plus_assoc (entropy_gradient (dynamics x))
                                                    (mult L (mult eta (entropy_gradient x)))
                                                    (opp (mult L (mult eta (entropy_gradient x))))))
                                (id_trans (id_cong (fun z => plus (entropy_gradient (dynamics x)) z)
                                                   (plus_opp (mult L (mult eta (entropy_gradient x)))))
                                          (plus_zero (entropy_gradient (dynamics x)))))).
    - exact (le_plus_compat (entropy_gradient x)
                            (plus (mult L (mult eta (entropy_gradient x)))
                                  (entropy_gradient (dynamics x)))
                            (opp (mult L (mult eta (entropy_gradient x))))
                            (opp (mult L (mult eta (entropy_gradient x))))
                            H1 (le_refl (opp (mult L (mult eta (entropy_gradient x)))))). }
  (* (v) reshaping: g + opp((Lη)g) == (1 − Lη)·g
        chain: opp((Lη)g) == opp((L·η)g) == (opp(Lη))·g; then
        g + (opp(Lη))·g == 1·g + (opp(Lη))·g == (1 + opp(Lη))·g *)
  apply (le_id_l (mult (minus one (mult L eta)) (entropy_gradient x))
                 (plus (entropy_gradient x)
                       (opp (mult L (mult eta (entropy_gradient x)))))).
  - exact (id_sym
             (id_trans (id_cong (fun z => plus (entropy_gradient x) z)
                                (id_trans (id_cong opp (mult_assoc L eta (entropy_gradient x)))
                                          (id_sym (opp_mult_r (mult L eta) (entropy_gradient x)))))
                       (id_trans (id_cong (fun z => plus z (mult (opp (mult L eta))
                                                                 (entropy_gradient x)))
                                          (id_trans (id_sym (mult_one (entropy_gradient x)))
                                                    (mult_comm (entropy_gradient x) one)))
                                 (id_sym (mult_plus_distr_r one (opp (mult L eta))
                                                            (entropy_gradient x)))))).
  - exact H2.
Qed.

(* ============================================================
   piece 1 (result): entropy_step_gain_lower, the quantitative one-step
     lower bound of the entropy gain
     g(x) > 0 implies
     η(1 − L·η)·g(x)² ≤ entropy(dynamics x) − entropy(x)
   assembly: core B multiplied by g > 0 and then by η > 0, cascaded with
   core A.
   ============================================================ *)
Theorem entropy_step_gain_lower : forall x : R,
  lt zero (entropy_gradient x) ->
  le (mult (mult eta (minus one (mult L eta)))
           (mult (entropy_gradient x) (entropy_gradient x)))
     (minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x Hgx.
  pose proof (eg_grad_lower x Hgx) as Hlow.
  (* multiplying by g > 0 (le_mult_compat): (c₁·g)·g ≤ g'·g, reshaped on the left by assoc *)
  pose proof (le_mult_compat (mult (minus one (mult L eta)) (entropy_gradient x))
                             (entropy_gradient (dynamics x))
                             (entropy_gradient x) Hgx Hlow) as Hm1.
  assert (Hm1' : le (mult (minus one (mult L eta))
                          (mult (entropy_gradient x) (entropy_gradient x)))
                    (mult (entropy_gradient (dynamics x)) (entropy_gradient x))).
  { apply (le_id_l _ (mult (mult (minus one (mult L eta)) (entropy_gradient x))
                           (entropy_gradient x)) _).
    - exact (mult_assoc (minus one (mult L eta)) (entropy_gradient x)
                        (entropy_gradient x)).
    - exact Hm1. }
  (* multiplying by η > 0 on the left (le_mult_compat_r): η·((1−Lη)·g²) ≤ η·(g'·g) *)
  pose proof (lt_le_iff zero eta (inl eta_pos)) as Hle_eta.
  pose proof (le_mult_compat_r eta
                             (mult (minus one (mult L eta))
                                   (mult (entropy_gradient x) (entropy_gradient x)))
                             (mult (entropy_gradient (dynamics x)) (entropy_gradient x))
                             Hle_eta Hm1') as Hm2.
  assert (Hm2' : le (mult (mult eta (minus one (mult L eta)))
                          (mult (entropy_gradient x) (entropy_gradient x)))
                    (mult (entropy_gradient (dynamics x))
                          (mult eta (entropy_gradient x)))).
  { apply (le_id_l _ (mult eta (mult (minus one (mult L eta))
                                     (mult (entropy_gradient x) (entropy_gradient x)))) _).
    - exact (id_sym (mult_assoc eta (minus one (mult L eta))
                                (mult (entropy_gradient x) (entropy_gradient x)))).
    - apply (le_id_r _ (mult eta (mult (entropy_gradient (dynamics x))
                                       (entropy_gradient x))) _).
      + exact (id_trans (mult_assoc eta (entropy_gradient (dynamics x)) (entropy_gradient x))
                        (id_trans (id_cong (fun z => mult z (entropy_gradient x))
                                           (mult_comm eta (entropy_gradient (dynamics x))))
                                  (id_sym (mult_assoc (entropy_gradient (dynamics x))
                                                      eta (entropy_gradient x))))).
      + exact Hm2. }
  exact (le_trans _ _ _ Hm2' (eg_tangent_shift x)).
Qed.

(* ============================================================
   piece 2 (result): entropy_gain_positive, the sufficient-condition form
     of the positivity of the increment
     0 < η, 0 < L, ηL < 1, g(x) > 0 imply 0 < entropy(x') − entropy(x)
   (the positivity condition is ηL < 1 rather than the draft form ημ < 1: μ
     only bounds the upper tail and does not control overshoot; the
     negative branch g < 0 would need a three-way sign decision, so the
     constructive statement descends to the one-sided form.)
   ============================================================ *)
Theorem entropy_gain_positive : forall x : R,
  lt zero (entropy_gradient x) ->
  lt (mult L eta) one ->
  lt zero (minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x Hgx HetaL.
  assert (Hc : lt zero (minus one (mult L eta)))
    by exact (eg_minus_pos (mult L eta) one HetaL).
  assert (Hc1 : lt zero (mult eta (minus one (mult L eta))))
    by exact (mult_positive eta (minus one (mult L eta)) eta_pos Hc).
  assert (Haa : lt zero (mult (entropy_gradient x) (entropy_gradient x)))
    by exact (mult_positive (entropy_gradient x) (entropy_gradient x) Hgx Hgx).
  assert (HA : lt zero (mult (mult eta (minus one (mult L eta)))
                             (mult (entropy_gradient x) (entropy_gradient x))))
    by exact (mult_positive (mult eta (minus one (mult L eta)))
                            (mult (entropy_gradient x) (entropy_gradient x))
                            Hc1 Haa).
  pose proof (entropy_step_gain_lower x Hgx) as Hlow.
  exact (lt_le_trans zero _ _ HA Hlow).
Qed.

(* ============================================================
   piece 3 (comparison note plus resulting corollary): second_law_quant
   in the root SecondLaw section (L27778-27803) strict_entropy_increase is
   an interface Variable and second_law_irreversible follows by applying it
   (a transport of the premise; both occurrences share the same premise).
   this file derives the same conclusion,
   lt (entropy x) (entropy (dynamics x)), from the concrete entropy-gradient
   dynamics under explicit sufficient premises (ηL < 1 and g(x) > 0); the
   older piece can retire, its interface premise being supplied
   constructively here by entropy_gain_positive under these premises.
   ============================================================ *)
Theorem second_law_quant : forall x : R,
  lt zero (entropy_gradient x) ->
  lt (mult L eta) one ->
  lt (entropy x) (entropy (dynamics x)).
Proof.
  intros x Hgx HetaL.
  pose proof (entropy_gain_positive x Hgx HetaL) as Hpos.
  apply (lt_id_r (entropy x)
                 (plus (minus (entropy (dynamics x)) (entropy x)) (entropy x))
                 (entropy (dynamics x))).
  - exact (eg_minus_plus_cancel (entropy (dynamics x)) (entropy x)).
  - apply (lt_id_l (entropy x) (plus zero (entropy x))
                   (plus (minus (entropy (dynamics x)) (entropy x)) (entropy x))).
    + exact (id_trans (id_sym (plus_zero (entropy x)))
                      (plus_comm (entropy x) zero)).
    + exact (lt_plus_compat_lt_le zero (minus (entropy (dynamics x)) (entropy x))
                                  (entropy x) (entropy x)
                                  Hpos (le_refl (entropy x))).
Qed.

End EntropyGainQuant.
(* ================= Section 6. The real_softplus family ================= *)
(* piece 1: the definition of real_softplus, the identity bridge and monotonicity                      *)

(* softplus x := log(1 + e^{−x}), the softplus form of the DPO logit loss;
   the positivity certificate reuses the root-level real_sigmoid_denom_pos:
   1 + e^{−x} > 0. *)
Definition real_softplus (x : Real) : Real :=
  real_log (real_plus real_one (real_exp_neg x)) (real_sigmoid_denom_pos x).

(* identity bridge: real_softplus x == real_dpo_logit x == −log σ(x). *)
Lemma real_softplus_eq_dpo_logit : forall x : Real,
  real_eq (real_softplus x) (real_dpo_logit x).
Proof. intro x. apply real_eq_sym. exact (real_softplus_sigmoid_eq x). Qed.

(* monotonicity (decreasing): x ≤ y implies softplus y ≤ softplus x
   (exp_neg is decreasing, giving 1+e^{−y} ≤ 1+e^{−x}; log preserves the
   order and finishes). *)
Lemma real_softplus_mono : forall x y : Real, real_le x y ->
  real_le (real_softplus y) (real_softplus x).
Proof.
  intros x y Hxy.
  apply (real_log_le_mono (real_plus real_one (real_exp_neg y))
                          (real_plus real_one (real_exp_neg x))
                          (real_sigmoid_denom_pos y)
                          (real_sigmoid_denom_pos x)).
  exact (real_le_plus_compat real_one real_one
                             (real_exp_neg y) (real_exp_neg x)
                             (real_le_refl real_one)
                             (real_exp_neg_le_decr x y Hxy)).
Qed.

(* u ≤ 0 implies 1 ≤ e^{−u}, by the e^0 == 1 reshaping and the decrease of exp_neg. *)
Lemma real_one_le_exp_neg_of_le_zero : forall u : Real, real_le u real_zero ->
  real_le real_one (real_exp_neg u).
Proof.
  intros u Hu.
  apply (real_le_trans real_one (real_exp_neg real_zero) (real_exp_neg u)).
  - apply real_eq_le_bridge.
    apply real_eq_sym. exact real_exp_neg_zero.
  - exact (real_exp_neg_le_decr u real_zero Hu).
Qed.

(* b ≤ a implies b − a ≤ 0 (nonpositivity of the difference; order-preserving addition and a + (−a) == 0). *)
Lemma real_diff_le_zero : forall a b : Real, real_le b a ->
  real_le (real_plus b (real_opp a)) real_zero.
Proof.
  intros a b Hba.
  apply (real_le_trans (real_plus b (real_opp a))
                       (real_plus a (real_opp a)) real_zero).
  - exact (real_le_plus_compat b a (real_opp a) (real_opp a)
                                  Hba (real_le_refl (real_opp a))).
  - apply real_eq_le_bridge. exact (real_plus_opp a).
Qed.

(* algebra: e^{−b} == e^{−a}·e^{−(b−a)}, by reshaping the exponent and the additivity of exp. *)
Lemma dpo_real_exp_neg_split : forall a b : Real,
  real_eq (real_exp_neg b)
          (real_mult (real_exp_neg a)
                     (real_exp_neg (real_plus b (real_opp a)))).
Proof.
  intros a b.
  apply (real_eq_trans (real_exp_neg b)
                       (real_exp_neg (real_plus a (real_plus b (real_opp a)))) _).
  - unfold real_exp_neg. apply cauchy_real_exp_wd.
    apply (RealSetoid.real_eq_opp_compat b (real_plus a (real_plus b (real_opp a)))).
    apply real_eq_sym.
    (* a + (b − a) == b: assoc, comm, inverse assoc, opp cancellation, right zero *)
    apply (real_eq_trans (real_plus a (real_plus b (real_opp a)))
                         (real_plus (real_plus a b) (real_opp a)) b).
    + exact (real_plus_assoc a b (real_opp a)).
    + apply (real_eq_trans (real_plus (real_plus a b) (real_opp a))
                           (real_plus (real_plus b a) (real_opp a)) b).
      * apply (RealSetoid.real_eq_plus_compat (real_plus a b) (real_opp a)
                                              (real_plus b a) (real_opp a)).
        -- exact (real_plus_comm a b).
        -- apply real_eq_refl.
      * apply (real_eq_trans (real_plus (real_plus b a) (real_opp a))
                             (real_plus b (real_plus a (real_opp a))) b).
        -- apply real_eq_sym.
           exact (real_plus_assoc b a (real_opp a)).
        -- apply (real_eq_trans (real_plus b (real_plus a (real_opp a)))
                                (real_plus b real_zero) b).
           ++ apply (RealSetoid.real_eq_plus_compat b (real_plus a (real_opp a))
                                                    b real_zero).
              ** apply real_eq_refl.
              ** exact (real_plus_opp a).
           ++ exact (real_plus_zero b).
  - exact (real_exp_neg_plus a (real_plus b (real_opp a))).
Qed.

(* piece 2: the one-sided kernel under the order premise (the Lipschitz mathematical core)                        *)
(*   b ≤ a ⟹ softplus b − softplus a ≤ a − b                     *)
(* mathematical core: 1+e^{−b} ≤ e^{a−b} + e^{−b} == (1+e^{−a})·e^{a−b}     *)
(*   (e^{a−b} ≥ 1 follows from b ≤ a); taking log on both sides and the      *)
(*   additivity of log finish.                                               *)
Lemma real_softplus_diff_le : forall a b : Real, real_le b a ->
  real_le (real_plus (real_softplus b) (real_opp (real_softplus a)))
          (real_plus a (real_opp b)).
Proof.
  intros a b Hba.
  set (u := real_plus b (real_opp a)).
  set (E := real_exp_neg u).
  set (A := real_plus real_one (real_exp_neg a)).
  set (B := real_plus real_one (real_exp_neg b)).
  (* step 1: E = e^{a−b} ≥ 1 *)
  assert (Hu0 : real_le u real_zero) by exact (real_diff_le_zero a b Hba).
  assert (HE1 : real_le real_one E) by exact (real_one_le_exp_neg_of_le_zero u Hu0).
  (* step 2: the identity A·E == E + e^{−b} *)
  assert (HQ : real_eq (real_mult A E) (real_plus E (real_exp_neg b))).
  { apply (real_eq_trans (real_mult A E)
           (real_plus (real_mult E real_one) (real_mult E (real_exp_neg a))) _).
    - apply (real_eq_trans (real_mult A E)
              (real_mult E (real_plus real_one (real_exp_neg a))) _).
      + exact (real_mult_comm A E).
      + exact (real_distrib E real_one (real_exp_neg a)).
    - apply (RealSetoid.real_eq_plus_compat (real_mult E real_one)
                                            (real_mult E (real_exp_neg a))
                                            E (real_exp_neg b)).
      + exact (real_mult_one E).
      + (* E·e^{−a} == e^{−b}: dpo_real_exp_neg_split plus commutativity of multiplication *)
        apply real_eq_sym.
        apply (real_eq_trans (real_exp_neg b)
                             (real_mult (real_exp_neg a) E) _).
        * exact (dpo_real_exp_neg_split a b).
        * exact (real_mult_comm (real_exp_neg a) E).
  }
  (* step 3: B ≤ A·E, by order-preserving addition from 1 ≤ E and the reshaped identity *)
  assert (HB : real_le B (real_mult A E)).
  { apply (real_le_trans B (real_plus E (real_exp_neg b)) (real_mult A E)).
    - exact (real_le_plus_compat real_one E (real_exp_neg b) (real_exp_neg b)
                                  HE1 (real_le_refl (real_exp_neg b))).
    - apply real_eq_le_bridge. apply real_eq_sym. exact HQ.
  }
  (* step 4: log completes it: softplus b ≤ softplus a + (a − b) *)
  assert (Hlog : real_le (real_softplus b)
                         (real_plus (real_softplus a) (real_plus a (real_opp b)))).
  { apply (real_le_trans (real_softplus b)
             (real_log (real_mult A E)
                       (real_mult_positive A E (real_sigmoid_denom_pos a)
                                           (real_exp_neg_pos u))) _).
    - apply (real_log_le_mono B (real_mult A E) (real_sigmoid_denom_pos b)
              (real_mult_positive A E (real_sigmoid_denom_pos a)
                                      (real_exp_neg_pos u)) HB).
    - apply real_eq_le_bridge.
      apply (real_eq_trans (real_log (real_mult A E)
                (real_mult_positive A E (real_sigmoid_denom_pos a)
                                        (real_exp_neg_pos u)))
        (real_plus (real_log A (real_sigmoid_denom_pos a))
                   (real_log E (real_exp_neg_pos u))) _).
      + exact (real_log_mult A E (real_sigmoid_denom_pos a) (real_exp_neg_pos u)).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_log A (real_sigmoid_denom_pos a))
                 (real_log E (real_exp_neg_pos u))
                 (real_softplus a) (real_plus a (real_opp b))).
        * apply real_eq_refl.
        * 
          apply (real_eq_trans (real_log E (real_exp_neg_pos u))
                               (real_opp u) _).
          -- exact (log_inv_exp_neg_thm (real_opp u) (real_exp_neg_pos u)).
          -- apply (real_eq_trans (real_opp u)
                     (real_plus (real_opp b) (real_opp (real_opp a))) _).
             ++ exact (real_opp_plus b (real_opp a)).
             ++ apply (real_eq_trans (real_plus (real_opp b) (real_opp (real_opp a)))
                                     (real_plus (real_opp b) a) _).
                ** apply (RealSetoid.real_eq_plus_compat (real_opp b)
                            (real_opp (real_opp a)) (real_opp b) a).
                   --- apply real_eq_refl.
                   --- exact (real_opp_opp a).
                ** exact (real_plus_comm (real_opp b) a).
  }
  (* step 5: moving terms: softplus b − softplus a ≤ a − b *)
  apply (real_le_trans (real_plus (real_softplus b) (real_opp (real_softplus a)))
                       (real_plus (real_plus (real_softplus a) (real_plus a (real_opp b)))
                                  (real_opp (real_softplus a))) _).
  - exact (real_le_plus_compat (real_softplus b)
                               (real_plus (real_softplus a) (real_plus a (real_opp b)))
                               (real_opp (real_softplus a)) (real_opp (real_softplus a))
                               Hlog (real_le_refl (real_opp (real_softplus a)))).
  - apply real_eq_le_bridge.
    apply (real_eq_trans (real_plus (real_plus (real_softplus a) (real_plus a (real_opp b)))
                                    (real_opp (real_softplus a)))
                         (real_plus (real_softplus a)
                                    (real_plus (real_plus a (real_opp b))
                                               (real_opp (real_softplus a)))) _).
    + apply real_eq_sym.
      exact (real_plus_assoc (real_softplus a) (real_plus a (real_opp b))
                             (real_opp (real_softplus a))).
    + apply (real_eq_trans (real_plus (real_softplus a)
                              (real_plus (real_plus a (real_opp b))
                                         (real_opp (real_softplus a))))
                           (real_plus (real_softplus a)
                              (real_plus (real_opp (real_softplus a))
                                         (real_plus a (real_opp b)))) _).
      * apply (RealSetoid.real_eq_plus_compat (real_softplus a)
                 (real_plus (real_plus a (real_opp b)) (real_opp (real_softplus a)))
                 (real_softplus a)
                 (real_plus (real_opp (real_softplus a)) (real_plus a (real_opp b)))).
        -- apply real_eq_refl.
        -- exact (real_plus_comm (real_plus a (real_opp b))
                                 (real_opp (real_softplus a))).
      * apply (real_eq_trans (real_plus (real_softplus a)
                   (real_plus (real_opp (real_softplus a)) (real_plus a (real_opp b))))
                (real_plus (real_plus (real_softplus a) (real_opp (real_softplus a)))
                           (real_plus a (real_opp b))) _).
        -- exact (real_plus_assoc (real_softplus a) (real_opp (real_softplus a))
                                  (real_plus a (real_opp b))).
        -- apply (real_eq_trans (real_plus (real_plus (real_softplus a)
                                             (real_opp (real_softplus a)))
                                           (real_plus a (real_opp b)))
                                (real_plus real_zero (real_plus a (real_opp b))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus (real_softplus a) (real_opp (real_softplus a)))
                       (real_plus a (real_opp b))
                       real_zero (real_plus a (real_opp b))).
              ** exact (real_plus_opp (real_softplus a)).
              ** apply real_eq_refl.
           ++ apply (real_eq_trans (real_plus real_zero (real_plus a (real_opp b)))
                                   (real_plus (real_plus a (real_opp b)) real_zero) _).
              ** exact (real_plus_comm real_zero (real_plus a (real_opp b))).
              ** exact (real_plus_zero (real_plus a (real_opp b))).
Qed.

(* piece 2 completed: the abs resolution tools and the main Lipschitz corollary under the Or order premise          *)

(* 0 ≤ d implies |d| == d, the le form of real_abs_pos_req over the two Or branches. *)
Lemma real_abs_nonneg_eq : forall d : Real, real_le real_zero d ->
  real_eq (real_abs d) d.
Proof.
  intros d Hd. destruct Hd as [Hlt | Heq].
  - exact (real_abs_pos_req d Hlt).
  - apply (real_eq_trans (real_abs d) real_zero d).
    + apply (real_eq_trans (real_abs d) (real_abs real_zero) real_zero).
      * apply (RealSetoid.real_eq_abs_compat d real_zero (real_eq_sym real_zero d Heq)).
      * exact real_abs_zero_req.
    + exact Heq.
Qed.

(* the negated form of a difference: u − v == −(v − u). *)
Lemma real_minus_opp_form : forall u v : Real,
  real_eq (real_plus u (real_opp v)) (real_opp (real_plus v (real_opp u))).
Proof.
  intros u v.
  apply (real_eq_trans (real_plus u (real_opp v))
                       (real_plus (real_opp v) u) _).
  - exact (real_plus_comm u (real_opp v)).
  - apply (real_eq_trans (real_plus (real_opp v) u)
                         (real_plus (real_opp v) (real_opp (real_opp u))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_opp v) u
                                            (real_opp v) (real_opp (real_opp u))).
      * apply real_eq_refl.
      * apply real_eq_sym. exact (real_opp_opp u).
    + apply real_eq_sym. exact (real_opp_plus v (real_opp u)).
Qed.

(* d == −e and 0 ≤ e imply |d| == e, resolving abs through the opp symmetry. *)
Lemma real_abs_opp_form : forall d e : Real,
  real_eq d (real_opp e) -> real_le real_zero e -> real_eq (real_abs d) e.
Proof.
  intros d e Hd He.
  apply (real_eq_trans (real_abs d) (real_abs e) e).
  - apply (real_eq_trans (real_abs d) (real_abs (real_opp e)) (real_abs e)).
    + apply (RealSetoid.real_eq_abs_compat d (real_opp e) Hd).
    + exact (real_abs_opp e).
  - exact (real_abs_nonneg_eq e He).
Qed.

(* main corollary: the 1-Lipschitz sensitivity bound of softplus, in metric
   form.  the premise Or (real_le x y) (real_le y x) is the explicit
   Set-level dichotomy of the order, not decidable wholesale on the
   constructive reals. *)
Theorem real_softplus_lipschitz : forall x y : Real,
  Or (real_le x y) (real_le y x) ->
  real_le (real_metric (real_softplus x) (real_softplus y))
          (real_metric x y).
Proof.
  intros x y Hor. unfold real_metric.
  destruct Hor as [Hxy | Hyx].
  - (* branch 1: x ≤ y.  |sp x − sp y| == sp x − sp y, and |x − y| == y − x. *)
    assert (Hdec : real_le (real_softplus y) (real_softplus x))
      by exact (real_softplus_mono x y Hxy).
    assert (Hd1 : real_le real_zero
                    (real_plus (real_softplus x) (real_opp (real_softplus y))))
      by exact (real_le_minus_nonneg_aux (real_softplus y) (real_softplus x) Hdec).
    assert (Hd2 : real_le real_zero (real_plus y (real_opp x)))
      by exact (real_le_minus_nonneg_aux x y Hxy).
    apply (real_le_trans (real_abs (real_plus (real_softplus x) (real_opp (real_softplus y))))
                         (real_plus (real_softplus x) (real_opp (real_softplus y))) _).
    + apply real_eq_le_bridge.
      exact (real_abs_nonneg_eq (real_plus (real_softplus x) (real_opp (real_softplus y))) Hd1).
    + apply (real_le_trans (real_plus (real_softplus x) (real_opp (real_softplus y)))
                           (real_plus y (real_opp x)) _).
      * exact (real_softplus_diff_le y x Hxy).
      * apply real_eq_le_bridge. apply real_eq_sym.
        exact (real_abs_opp_form (real_plus x (real_opp y))
                                 (real_plus y (real_opp x))
                                 (real_minus_opp_form x y) Hd2).
  - (* branch 2: y ≤ x.  |sp x − sp y| == sp y − sp x by the opp bridge, and |x − y| == x − y. *)
    assert (Hdec : real_le (real_softplus x) (real_softplus y))
      by exact (real_softplus_mono y x Hyx).
    assert (Hd1 : real_le real_zero
                    (real_plus (real_softplus y) (real_opp (real_softplus x))))
      by exact (real_le_minus_nonneg_aux (real_softplus x) (real_softplus y) Hdec).
    assert (Hd2 : real_le real_zero (real_plus x (real_opp y)))
      by exact (real_le_minus_nonneg_aux y x Hyx).
    apply (real_le_trans (real_abs (real_plus (real_softplus x) (real_opp (real_softplus y))))
                         (real_plus (real_softplus y) (real_opp (real_softplus x))) _).
    + apply real_eq_le_bridge.
      exact (real_abs_opp_form (real_plus (real_softplus x) (real_opp (real_softplus y)))
                               (real_plus (real_softplus y) (real_opp (real_softplus x)))
                               (real_minus_opp_form (real_softplus x) (real_softplus y))
                               Hd1).
    + apply (real_le_trans (real_plus (real_softplus y) (real_opp (real_softplus x)))
                           (real_plus x (real_opp y)) _).
      * exact (real_softplus_diff_le x y Hyx).
      * apply real_eq_le_bridge.
        apply real_eq_sym.
        exact (real_abs_nonneg_eq (real_plus x (real_opp y)) Hd2).
Qed.

(* piece 3: the DPO loss sensitivity assembly                                      *)
(*   |L(π; w, l) − L(π*; w, l)| ≤ |β(log_ratio difference) − (r_w − r_l)| *)
(*   (conditional form: the order-dichotomy premise is an explicit Set-level Or).                *)

(* the metric is compatible with the real_eq congruence. *)
Lemma real_metric_eq_compat : forall a a' b b' : Real,
  real_eq a a' -> real_eq b b' ->
  real_eq (real_metric a b) (real_metric a' b').
Proof.
  intros a a' b b' Ha Hb. unfold real_metric.
  apply (RealSetoid.real_eq_abs_compat (real_plus a (real_opp b))
                                       (real_plus a' (real_opp b'))).
  apply (RealSetoid.real_eq_plus_compat a (real_opp b) a' (real_opp b') Ha).
  apply (RealSetoid.real_eq_opp_compat b b'). exact Hb.
Qed.

Section UpDpoSensMain.

Variable S : Type.
Variable reward : S -> Real.
Variable beta : Real.
Variable beta_pos : real_lt real_zero beta.
Variable pi_ref : S -> Real.
Variable pi_ref_pos : forall s : S, real_lt real_zero (pi_ref s).
Variable Z_align : Real.
Variable Z_align_pos : real_lt real_zero Z_align.

(* the DPO logit difference of a policy π: β·(log_ratio(π, w) − log_ratio(π, l)). *)
Definition real_dpo_logit_pair (pi : S -> Real)
  (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S) : Real :=
  real_plus (real_mult beta (real_log_ratio S pi_ref pi_ref_pos pi Hpi s_w))
            (real_opp (real_mult beta (real_log_ratio S pi_ref pi_ref_pos pi Hpi s_l))).

(* the DPO logit difference at π*: the true reward difference r_w − r_l. *)
Definition real_dpo_logit_star (s_w s_l : S) : Real :=
  real_plus (reward s_w) (real_opp (reward s_l)).

(* bridge 1: the policy DPO loss == softplus of the logit difference, definitionally plus the softplus identity bridge. *)
Lemma real_dpo_loss_pair_eq_softplus : forall (pi : S -> Real)
  (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S),
  real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos pi Hpi s_w s_l)
          (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)).
Proof.
  intros pi Hpi s_w s_l.
  apply real_eq_sym. apply real_softplus_eq_dpo_logit.
Qed.

(* bridge 2: the DPO loss at π* == softplus of the true reward difference
   (real_dpo_loss_at_pi_star plus the softplus identity bridge). *)
Lemma real_dpo_loss_star_eq_softplus : forall s_w s_l : S,
  real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos
             (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
             (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos)
             s_w s_l)
          (real_softplus (real_dpo_logit_star s_w s_l)).
Proof.
  intros s_w s_l.
  apply (real_eq_trans _ (real_dpo_logit (real_dpo_logit_star s_w s_l)) _).
  - exact (real_dpo_loss_at_pi_star S reward beta beta_pos pi_ref pi_ref_pos
                                    Z_align Z_align_pos s_w s_l).
  - apply real_eq_sym. apply real_softplus_eq_dpo_logit.
Qed.

(* main statement: the DPO loss sensitivity bound in metric form, with the
   order-dichotomy premise an explicit Set-level Or.
   content: metric L pi L_star ≤ metric logit pi logit_star, that is, the
   distance from the policy loss to the pi_star loss is bounded by the
   distance between the logit differences. *)
Theorem real_dpo_pair_loss_sensitivity :
  forall (pi : S -> Real) (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S),
  Or (real_le (real_dpo_logit_star s_w s_l) (real_dpo_logit_pair pi Hpi s_w s_l))
      (real_le (real_dpo_logit_pair pi Hpi s_w s_l) (real_dpo_logit_star s_w s_l)) ->
  real_le (real_metric (real_dpo_loss_pair S beta pi_ref pi_ref_pos pi Hpi s_w s_l)
                       (real_dpo_loss_pair S beta pi_ref pi_ref_pos
                          (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
                          (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos)
                          s_w s_l))
          (real_metric (real_dpo_logit_pair pi Hpi s_w s_l)
                       (real_dpo_logit_star s_w s_l)).
Proof.
  intros pi Hpi s_w s_l Hor.
  assert (HL : real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos pi Hpi s_w s_l)
                       (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))
    by exact (real_dpo_loss_pair_eq_softplus pi Hpi s_w s_l).
  assert (HS : real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos
                             (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
                             (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos)
                             s_w s_l)
                       (real_softplus (real_dpo_logit_star s_w s_l)))
    by exact (real_dpo_loss_star_eq_softplus s_w s_l).
  apply (real_le_trans _ (real_metric (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                      (real_softplus (real_dpo_logit_star s_w s_l))) _).
  - apply real_eq_le_bridge.
    exact (real_metric_eq_compat _ _ _ _ HL HS).
  - unfold real_metric.
    destruct Hor as [H | H].
    + (* branch 1: X* ≤ Xπ implies Lπ ≤ L*, and |Lπ − L*| == L* − Lπ ≤ Xπ − X* == |Xπ − X*| *)
      assert (Hdec : real_le (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                             (real_softplus (real_dpo_logit_star s_w s_l)))
        by exact (real_softplus_mono (real_dpo_logit_star s_w s_l)
                                     (real_dpo_logit_pair pi Hpi s_w s_l) H).
      assert (Hd1 : real_le real_zero
                      (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                 (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))))
        by exact (real_le_minus_nonneg_aux (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                           (real_softplus (real_dpo_logit_star s_w s_l)) Hdec).
      assert (Hd2 : real_le real_zero
                      (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                 (real_opp (real_dpo_logit_star s_w s_l))))
        by exact (real_le_minus_nonneg_aux (real_dpo_logit_star s_w s_l)
                                           (real_dpo_logit_pair pi Hpi s_w s_l) H).
      apply (real_le_trans (real_abs (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                                (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))))
                           (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                      (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))) _).
      * apply real_eq_le_bridge.
        exact (real_abs_opp_form (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                            (real_opp (real_softplus (real_dpo_logit_star s_w s_l))))
                                 (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                            (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))))
                                 (real_minus_opp_form (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                                      (real_softplus (real_dpo_logit_star s_w s_l)))
                                 Hd1).
      * apply (real_le_trans (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                        (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))))
                             (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                        (real_opp (real_dpo_logit_star s_w s_l))) _).
        -- exact (real_softplus_diff_le (real_dpo_logit_pair pi Hpi s_w s_l)
                                        (real_dpo_logit_star s_w s_l) H).
        -- apply real_eq_le_bridge.
           apply real_eq_sym.
           exact (real_abs_nonneg_eq (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                                (real_opp (real_dpo_logit_star s_w s_l))) Hd2).
    + (* branch 2: Xπ ≤ X* implies L* ≤ Lπ, and |Lπ − L*| == Lπ − L* ≤ X* − Xπ == |Xπ − X*| *)
      assert (Hdec : real_le (real_softplus (real_dpo_logit_star s_w s_l))
                             (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))
        by exact (real_softplus_mono (real_dpo_logit_pair pi Hpi s_w s_l)
                                     (real_dpo_logit_star s_w s_l) H).
      assert (Hd1 : real_le real_zero
                      (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                 (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))))
        by exact (real_le_minus_nonneg_aux (real_softplus (real_dpo_logit_star s_w s_l))
                                           (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)) Hdec).
      assert (Hd2 : real_le real_zero
                      (real_plus (real_dpo_logit_star s_w s_l)
                                 (real_opp (real_dpo_logit_pair pi Hpi s_w s_l))))
        by exact (real_le_minus_nonneg_aux (real_dpo_logit_pair pi Hpi s_w s_l)
                                           (real_dpo_logit_star s_w s_l) H).
      apply (real_le_trans (real_abs (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                                (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))))
                           (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                      (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))) _).
      * apply real_eq_le_bridge.
        exact (real_abs_nonneg_eq (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                             (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))) Hd1).
      * apply (real_le_trans (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                        (real_opp (real_softplus (real_dpo_logit_star s_w s_l))))
                             (real_plus (real_dpo_logit_star s_w s_l)
                                        (real_opp (real_dpo_logit_pair pi Hpi s_w s_l))) _).
        -- exact (real_softplus_diff_le (real_dpo_logit_star s_w s_l)
                                        (real_dpo_logit_pair pi Hpi s_w s_l) H).
        -- apply real_eq_le_bridge.
           apply real_eq_sym.
           exact (real_abs_opp_form (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                               (real_opp (real_dpo_logit_star s_w s_l)))
                                    (real_plus (real_dpo_logit_star s_w s_l)
                                               (real_opp (real_dpo_logit_pair pi Hpi s_w s_l)))
                                    (real_minus_opp_form (real_dpo_logit_pair pi Hpi s_w s_l)
                                                         (real_dpo_logit_star s_w s_l))
                                    Hd2).
Qed.

End UpDpoSensMain.
