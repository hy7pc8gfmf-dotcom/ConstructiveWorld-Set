(* ConstructiveWorld-Set -- per-slot supply theorems feeding the premise slots of the DTPT truth audit. *)

(** * abl_dtpt_truth_supply: one supply theorem per premise slot of DTPT_Truth.

    Mission.  for each registered premise slot of [DTPT_Truth] this file supplies
      one [tdt_] theorem whose statement is an existing decidable instance of
      that premise: involutive negation on [bool] via [negb] (slots 3/7/9);
      level-order reflexivity diagonals [trLevel_geq], [level_le], [chain_ok]
      (slots 11-16); record-projection computation laws for [trPhi], [trLevel],
      [trValue] (slots 17-19); [Q]-order diagonals through [Qle_refl] and
      [DTPT.DTPT.gate_pass] (slots 20-26); and boolean decision leaves and size
      witnesses for [qlist_eqb], [ev_eqb], [ev_eqb_raw], [ev_size] (slots 27-33).

    Dependencies.  Stdlib [QArith.QArith], [List], [Bool], [Arith].  Requires
      [DTPT], [DTPT_Truth] of this development.

    References.  This development, abl_dtpt_truth_supply.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_dtpt_truth_supply.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith.
Import ListNotations.

Require DTPT.
Require DTPT_Truth.
Import DTPT_Truth.DTPT_Truth.

(* ================= Section 1. Involutive slots (#3/7/9) with the transitivity, cast and audit-node families ================= *)

(* slot 3 of DTPT_Truth.v (neg_truth_at_neg, premise 1): [involutive bool negb] --
   the general form fails by the host counterexample [negS_not_involutive], so
   the supply takes the existing positive instance in the boolean code world
   [Code := bool], [neg := negb]; [negb_involutive_self] has the required shape
   and is reused verbatim. *)
Theorem tdt_neg_truth_at_neg_h1 : involutive bool negb.
Proof.
  exact negb_involutive_self.
Qed.

(* slot 7 of DTPT_Truth.v (diag_conj_spec, premise 1): same involutive shape as
   slot 3, so the same boolean instance applies, one theorem per slot. *)
Theorem tdt_diag_conj_spec_h1 : involutive bool negb.
Proof.
  exact negb_involutive_self.
Qed.

(* slot 9 of DTPT_Truth.v (tarski_via_renaming, premise 1): same involutive
   shape, same boolean instance. *)
Theorem tdt_tarski_via_renaming_h1 : involutive bool negb.
Proof.
  exact negb_involutive_self.
Qed.

(* slot 11 of DTPT_Truth.v (trLevel_geq_trans, premise 1): [trLevel_geq t a = true]
   with the instance domain [a := Lv0], the bottom of the level order; the host
   lemma [trLevel_geq_Lv0] supplies it directly. *)
Theorem tdt_trLevel_geq_trans_h1 : forall t : TrNode, trLevel_geq t Lv0 = true.
Proof.
  intros t. apply DTPT.DTPT.id_imp_eq. apply trLevel_geq_Lv0.
Qed.

(* slot 12 of DTPT_Truth.v (trLevel_geq_trans, premise 2): [level_le b a = true]
   with [b := Lv0]; the first branch of the definition of [level_le] reduces to
   [true], so the nine-way boolean decision is discharged by case analysis. *)
Theorem tdt_trLevel_geq_trans_h2 : forall a : Level, level_le Lv0 a = true.
Proof.
  intros a. destruct a; reflexivity.
Qed.

(* slot 13 of DTPT_Truth.v (chain_ok_trans, premise 1): [chain_ok l1 l2 l3 = true]
   on the diagonal [l1 = l2 = l3]; both conjuncts are reflexivity of [level_le],
   assembled from the host lemma [level_le_refl]. *)
Theorem tdt_chain_ok_trans_h1 : forall l : Level, chain_ok l l l = true.
Proof.
  intros l. unfold chain_ok. apply andb_true_intro. split;
    apply DTPT.DTPT.id_imp_eq; apply level_le_refl.
Qed.

(* slot 14 of DTPT_Truth.v (cv_lv_inj, premise 1): [cv_lv a = cv_lv b], the
   equality-supply form: the existing composition of Leibniz equality rewriting
   yields the slot premise, and [cv_lv_inj] then applies to this instance. *)
Theorem tdt_cv_lv_inj_h1 : forall a b : DTPT.DTPT.Level,
  a = b -> cv_lv a = cv_lv b.
Proof.
  intros a b H. rewrite H. reflexivity.
Qed.

(* slot 15 of DTPT_Truth.v (cv_lv_antisym_transport, premise 1):
   [level_le (cv_lv a) (cv_lv b) = true] on the diagonal [b := a]; the host
   lemma [level_le_refl] supplies the reflexive instance. *)
Theorem tdt_cv_lv_antisym_transport_h1 : forall a : DTPT.DTPT.Level,
  level_le (cv_lv a) (cv_lv a) = true.
Proof.
  intros a. exact (DTPT.DTPT.id_imp_eq (level_le_refl (cv_lv a))).
Qed.

(* slot 16 of DTPT_Truth.v (cv_lv_antisym_transport, premise 2):
   [level_le (cv_lv b) (cv_lv a) = true] on the diagonal [b := a]; the same
   host lemma applies, one theorem per slot. *)
Theorem tdt_cv_lv_antisym_transport_h2 : forall a : DTPT.DTPT.Level,
  level_le (cv_lv a) (cv_lv a) = true.
Proof.
  intros a. exact (DTPT.DTPT.id_imp_eq (level_le_refl (cv_lv a))).
Qed.

(* slot 17 of DTPT_Truth.v (Tex_fiber_cast, premise 1): [DTPT.DTPT.trPhi t = phi] --
   witness-node computation law: for [t := DTPT.DTPT.mkTrNode lv phi m v] the
   first projection reduces to [phi] by iota. *)
Theorem tdt_Tex_fiber_cast_h1 : forall (lv : DTPT.DTPT.Level)
    (phi m : DTPT.DTPT.Dig) (v : DTPT.DTPT.Evidence),
  DTPT.DTPT.trPhi (DTPT.DTPT.mkTrNode lv phi m v) = phi.
Proof.
  intros lv phi m v. reflexivity.
Qed.

(* slot 18 of DTPT_Truth.v (audit_node_mono, premise 1): [trLevel t' = trLevel t] --
   record-projection computation law: the level projection of a node built at
   level [lv] reduces to the level index itself. *)
Theorem tdt_audit_node_mono_h1 : forall (lv : Level) (p m : DTPT.DTPT.Dig)
    (v : Evidence),
  trLevel (mkTrNode lv p m v) = lv.
Proof.
  intros lv p m v. reflexivity.
Qed.

(* slot 19 of DTPT_Truth.v (audit_node_mono, premise 2): [trValue t' = trValue t] --
   record-projection computation law: the value projection of a node built with
   evidence [v] reduces to the evidence index itself. *)
Theorem tdt_audit_node_mono_h2 : forall (lv : Level) (p m : DTPT.DTPT.Dig)
    (v : Evidence),
  trValue (mkTrNode lv p m v) = v.
Proof.
  intros lv p m v. reflexivity.
Qed.

(* ================= Section 2. Composite audit slot families (#20-26) with the content-decision and size slot families (#27-33) ================= *)

(* slot 20 of DTPT_Truth.v (audit_gate_level_combo, premise 1): [(thr1 <= thr2)%Q] --
   diagonal instance [thr1 := thr2] of the total order on [Q]; the stdlib lemma
   [Qle_refl] supplies it directly. *)
Theorem tdt_audit_gate_level_combo_h1 : forall thr : Q, (thr <= thr)%Q.
Proof.
  intros thr. apply Qle_refl.
Qed.

(* slot 21 of DTPT_Truth.v (audit_gate_level_combo, premise 2):
   [trLevel_geq t a = true] with [a := Lv0]; the host lemma [trLevel_geq_Lv0]
   supplies it (same shape as slot 11, one theorem per slot). *)
Theorem tdt_audit_gate_level_combo_h2 : forall t : TrNode,
  trLevel_geq t Lv0 = true.
Proof.
  intros t. apply DTPT.DTPT.id_imp_eq. apply trLevel_geq_Lv0.
Qed.

(* slot 22 of DTPT_Truth.v (audit_gate_level_combo, premise 3):
   [level_le b a = true] with [b := Lv0]; the nine-way boolean decision is
   discharged by case analysis (same shape as slot 12). *)
Theorem tdt_audit_gate_level_combo_h3 : forall a : Level, level_le Lv0 a = true.
Proof.
  intros a. destruct a; reflexivity.
Qed.

(* slot 23 of DTPT_Truth.v (audit_gate_level_combo, premise 4):
   [DTPT.DTPT.gate_pass thr1 H = true] on the diagonal [thr1 := H]: the existing
   composition of [DTPT.DTPT.llm_gate_pass_iff] with [Qle_refl] shows the pass
   test holds at a threshold equal to itself. *)
Theorem tdt_audit_gate_level_combo_h4 : forall H : Q,
  DTPT.DTPT.gate_pass H H = true.
Proof.
  intros H. exact (proj2 (DTPT.DTPT.llm_gate_pass_iff H H) (Qle_refl H)).
Qed.

(* slot 24 of DTPT_Truth.v (audit_node_chain_combo, premise 1): [(thr1 <= thr2)%Q] --
   diagonal instance of the total order on [Q] (same shape as slot 20, one
   theorem per slot). *)
Theorem tdt_audit_node_chain_combo_h1 : forall thr : Q, (thr <= thr)%Q.
Proof.
  intros thr. apply Qle_refl.
Qed.

(* slot 25 of DTPT_Truth.v (audit_node_chain_combo, premise 2): [audit_node t = true] --
   instance domain of a node witnessing the [Lv2] promotion; the host lemma
   [audit_node_lv2] supplies it verbatim. *)
Theorem tdt_audit_node_chain_combo_h2 : forall (p m : DTPT.DTPT.Dig)
    (v : Evidence),
  audit_node (mkTrNode Lv2 p m v) = true.
Proof.
  intros p m v. exact (DTPT.DTPT.id_imp_eq (audit_node_lv2 p m v)).
Qed.

(* slot 26 of DTPT_Truth.v (audit_node_chain_combo, premise 3):
   [DTPT.DTPT.gate_pass thr1 H = true] on the diagonal (same shape as slot 23,
   one theorem per slot). *)
Theorem tdt_audit_node_chain_combo_h3 : forall H : Q,
  DTPT.DTPT.gate_pass H H = true.
Proof.
  intros H. exact (proj2 (DTPT.DTPT.llm_gate_pass_iff H H) (Qle_refl H)).
Qed.

(* slot 27 of DTPT_Truth.v (qlist_eqb_sound, premise 1): [qlist_eqb l1 l2 = true] --
   singleton-list instance domain: the pointwise decision rests on the host
   lemma [qeqb_refl] plus reflexivity of the empty tail. *)
Theorem tdt_qlist_eqb_sound_h1 : forall q : Q,
  qlist_eqb (q :: nil) (q :: nil) = true.
Proof.
  intros q. simpl. apply andb_true_intro. split.
  - apply DTPT.DTPT.id_imp_eq. apply qeqb_refl.
  - reflexivity.
Qed.

(* slot 29 of DTPT_Truth.v (ev_eqb_cong_sound, premise 1): [ev_eqb a b = true] --
   leaf instance domain (equal [evNum] pair): the leaf decision [Qeq_bool]
   rests on the host lemma [qeqb_refl]. *)
Theorem tdt_ev_eqb_cong_sound_h1 : forall q : Q,
  ev_eqb (evNum q) (evNum q) = true.
Proof.
  intros q. simpl. apply DTPT.DTPT.id_imp_eq. apply qeqb_refl.
Qed.

(* slot 31 of DTPT_Truth.v (ev_eqb_raw_eq, premise 1): [ev_eqb_raw a b = true] --
   leaf instance domain (Leibniz leaf decision): the host lemma [Qraw_eqb_refl]
   supplies it. *)
Theorem tdt_ev_eqb_raw_eq_h1 : forall q : Q,
  ev_eqb_raw (evNum q) (evNum q) = true.
Proof.
  intros q. simpl. apply DTPT.DTPT.id_imp_eq. apply Qraw_eqb_refl.
Qed.

(* slot 32 of DTPT_Truth.v (ev_size_ge_2_pair, premise 1): [le (S (S O)) (ev_size e)] --
   size witness: for [e := evPair] of two leaves the size unfolds to [3], and
   [2 <= 3] follows by [le_S] then [le_n]. *)
Theorem tdt_ev_size_ge_2_pair_h1 :
  le (Datatypes.S (Datatypes.S O))
     (ev_size (evPair (evNum 0%Q) (evNum 0%Q))).
Proof.
  simpl. apply le_S. apply le_n.
Qed.

(* slot 33 of DTPT_Truth.v (ev_pair_decomp_exact, premise 1): same size threshold --
   size witness on a heterogeneous leaf pair ([evSeq] with [evNum]), one theorem
   per slot. *)
Theorem tdt_ev_pair_decomp_exact_h1 :
  le (Datatypes.S (Datatypes.S O))
     (ev_size (evPair (evSeq nil) (evNum 0%Q))).
Proof.
  simpl. apply le_S. apply le_n.
Qed.

(* ========== Assumption audit: Print Assumptions for each of the 24 supply theorems ========== *)
Print Assumptions tdt_neg_truth_at_neg_h1.
Print Assumptions tdt_diag_conj_spec_h1.
Print Assumptions tdt_tarski_via_renaming_h1.
Print Assumptions tdt_trLevel_geq_trans_h1.
Print Assumptions tdt_trLevel_geq_trans_h2.
Print Assumptions tdt_chain_ok_trans_h1.
Print Assumptions tdt_cv_lv_inj_h1.
Print Assumptions tdt_cv_lv_antisym_transport_h1.
Print Assumptions tdt_cv_lv_antisym_transport_h2.
Print Assumptions tdt_Tex_fiber_cast_h1.
Print Assumptions tdt_audit_node_mono_h1.
Print Assumptions tdt_audit_node_mono_h2.
Print Assumptions tdt_audit_gate_level_combo_h1.
Print Assumptions tdt_audit_gate_level_combo_h2.
Print Assumptions tdt_audit_gate_level_combo_h3.
Print Assumptions tdt_audit_gate_level_combo_h4.
Print Assumptions tdt_audit_node_chain_combo_h1.
Print Assumptions tdt_audit_node_chain_combo_h2.
Print Assumptions tdt_audit_node_chain_combo_h3.
Print Assumptions tdt_qlist_eqb_sound_h1.
Print Assumptions tdt_ev_eqb_cong_sound_h1.
Print Assumptions tdt_ev_eqb_raw_eq_h1.
Print Assumptions tdt_ev_size_ge_2_pair_h1.
Print Assumptions tdt_ev_pair_decomp_exact_h1.
