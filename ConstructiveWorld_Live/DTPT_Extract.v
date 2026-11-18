(** * DTPT_Extract: the extraction-gate suite over the DTPT core (X2-5 newly built face).

    Mission.  The extraction gate suite.  §1 extraction checks: each core
      piece extracted to its own [_ext.ml] artifact, acceptance metric
      [Obj.magic] = 0, artifacts removed after acceptance.  §2 behaviour
      pinned at [vm_compute] precision, the gold-standard regression anchor:
      any base change turning these red is a drift alarm.  §3 the executable
      review chain [gate_chain] (no [Prop] premises, all-boolean face) with
      the booleanized phase equivalence; §4 the [mu] regression and the
      degenerate [phase_side]; new names use the [u12_] prefix.

    Dependencies.  DTPT / DTPT_Measure / DTPT_LLM (the three task-sheet base
      components, all stable); DTPT_Entropy / DTPT_Truth (both settled:
      [phase_side] in Entropy, [level_le] / [ev_size] / [trLevel_geq] in
      Truth; task-sheet-named (Require-gated), in-progress pieces (D8Ext etc.) untouched; Truth-side
      references fully qualified, DTPT and DTPT_Truth defining same-named Level/Evidence inductions);
      QArith (QArith/Qabs), List, Arith, Permutation, Extraction.

    References.  Magic-free extraction of decision pieces and vm_compute
      regression anchors; this development, DTPT_Extract.v, the baseline
      ConstructiveWorld-Main module (statement names carried over verbatim;
      four name-binding sites adapted by qualification to the DTPT_Entropy
      generation, first-hand Locate/Print evidence).

    Constructivity.  Purely constructive, machine-checked, all proofs closed
      by [Qed], zero admission lexemes and zero axioms; [nat] literals all
      explicit [%nat]; [Q] a record, behaviour theorems close by [vm_compute].

    Build.  Rocq 9.1 direct [coqc -q -Q D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo ""] DTPT_Extract.v;
      the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Permutation.
From Stdlib Require Import Extraction.
Import ListNotations.
Require DTPT.
Require DTPT_Entropy.
Require DTPT_Truth.
Open Scope Q_scope.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.
Import DTPT_Truth.DTPT_Truth.

Module DTPT_Extract.

(* ========== §1 extraction checks (the guaranteed baseline face) ========== *)

(* Each piece is extracted on its own to a [name_ext.ml] artifact so the
   artifact names cannot collide; the artifacts are removed after acceptance.
   Extracting piece by piece keeps the Obj.magic count localizable to one
   concrete computational piece. *)

Set Extraction Output Directory ".".
Extraction "gate_pass_ext.ml" gate_pass.
Extraction "H_adj_ext.ml" H_adj.
Extraction "freq_ext.ml" freq.
Extraction "mu_ext.ml" mu.
Extraction "level_le_ext.ml" DTPT_Truth.DTPT_Truth.level_le.
Extraction "ev_size_ext.ml" DTPT_Truth.DTPT_Truth.ev_size.
Extraction "trLevel_geq_ext.ml" DTPT_Truth.DTPT_Truth.trLevel_geq.
Extraction "phase_side_ext.ml" phase_side.

(* ========== §2 computational behaviour pinned down (core, gold-standard regression face) ========== *)

(* The gate_pass sample table: the truth values of the three inputs 0/1/2
   under the thresholds 1/2, six cells pinned one by one.  Note the argument
   order of gate_pass is (threshold H): the threshold comes first. *)
Theorem u12_gate_pass_t1_h0 : gate_pass 1 0 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_pass_t1_h1 : gate_pass 1 1 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_pass_t1_h2 : gate_pass 1 2 = false.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_pass_t2_h0 : gate_pass 2 0 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_pass_t2_h1 : gate_pass 2 1 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_pass_t2_h2 : gate_pass 2 2 = true.
Proof. vm_compute. reflexivity. Qed.

(* A concrete freq column count: in [1;2;2;3] the value 2 occurs twice *)
Theorem u12_freq_1223_2 : freq [1;2;2;3] 2 = 2%nat.
Proof. vm_compute. reflexivity. Qed.

(* A concrete ev_size evidence-tree size: evPair(evNum 1)(evSeq [1;2]) = 1+1+1 = 3 *)
Theorem u12_ev_size_pair_num_seq :
  DTPT_Truth.DTPT_Truth.ev_size (DTPT_Truth.DTPT_Truth.evPair (DTPT_Truth.DTPT_Truth.evNum 1)
                                       (DTPT_Truth.DTPT_Truth.evSeq [1;2])) = 3%nat.
Proof. vm_compute. reflexivity. Qed.

(* level_le samples of the total-order decider: Lv1<=Lv2 true, Lv2<=Lv1 false *)
Theorem u12_level_le_12 : DTPT_Truth.DTPT_Truth.level_le DTPT_Truth.DTPT_Truth.Lv1 DTPT_Truth.DTPT_Truth.Lv2 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_level_le_21 : DTPT_Truth.DTPT_Truth.level_le DTPT_Truth.DTPT_Truth.Lv2 DTPT_Truth.DTPT_Truth.Lv1 = false.
Proof. vm_compute. reflexivity. Qed.

(* Concrete trLevel_geq node decisions: the Lv1 node passes the Lv0 gate (true) and fails the Lv2 gate (false) *)
Definition u12_trn1 : DTPT_Truth.DTPT_Truth.TrNode :=
  DTPT_Truth.DTPT_Truth.mkTrNode DTPT_Truth.DTPT_Truth.Lv1 (dQ 1) (dQ 1) (DTPT_Truth.DTPT_Truth.evNum 1).

Theorem u12_trLevel_geq_lv0 : DTPT_Truth.DTPT_Truth.trLevel_geq u12_trn1 DTPT_Truth.DTPT_Truth.Lv0 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_trLevel_geq_lv2 : DTPT_Truth.DTPT_Truth.trLevel_geq u12_trn1 DTPT_Truth.DTPT_Truth.Lv2 = false.
Proof. vm_compute. reflexivity. Qed.

(* Concrete phase_side list decisions (the X2-1 degenerate evidence made
   executable: the base rot is the identity degeneration, Pinf = l, so the
   phase decision always lands on the 0 side; three instances pinned) *)
Theorem u12_phase_side_301_s0 : phase_side [3;0;1] 0 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_phase_side_301_s2 : phase_side [3;0;1] 2 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_phase_side_nil : phase_side [] 0 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(* Concrete H_adj list values: 4 for the unsorted [3;0;1], 3 for the sorted [0;1;3] (on the Qeq face) *)
Theorem u12_H_adj_301 : H_adj [3;0;1] == 4%Q.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_H_adj_013 : H_adj [0;1;3] == 3%Q.
Proof. vm_compute. reflexivity. Qed.

(* ========== §3 the executable review chain (main piece) ========== *)

(* The booleanized phase decision: the same Qle_bool criterion as phase_side, zero Prop premises *)
Definition u12_phase_side_bool (l : list Q) (s : nat) : bool :=
  Qle_bool (DTPT_Entropy.H_adj (DTPT_Entropy.P0 l)) (DTPT_Entropy.H_adj (DTPT_Entropy.Pinf l s)).

(* The pointwise equivalence bridge between the booleanized piece and the original nat-valued decider *)
Theorem u12_phase_side_bool_spec : forall (l : list Q) (s : nat),
  phase_side l s = if u12_phase_side_bool l s then 0%nat else 1%nat.
Proof.
  intros l s. unfold phase_side, u12_phase_side_bool.
  destruct (Qle_bool (DTPT_Entropy.H_adj (DTPT_Entropy.P0 l)) (DTPT_Entropy.H_adj (DTPT_Entropy.Pinf l s))); reflexivity.
Qed.

(* The extractable review chain: the gate passes the H_adj threshold test and the phase lands on the P0 side (sampled at s = 0) *)
Definition u12_gate_chain (l : list Q) (threshold : Q) : bool :=
  gate_pass threshold (H_adj l) && u12_phase_side_bool l 0%nat.

(* The new definitions on the chain are extractable too (the same chain as the base pieces, the Obj.magic face accepted together) *)
Extraction "gate_chain_ext.ml" u12_gate_chain u12_phase_side_bool.

(* Two behaviour theorems: one rejection (the threshold gate blocks) and one passage (both gates open) *)
Theorem u12_gate_chain_301_t1 : u12_gate_chain [3;0;1] 1 = false.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_chain_301_t5 : u12_gate_chain [3;0;1] 5 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_chain_013_t3 : u12_gate_chain [0;1;3] 3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_gate_chain_nil_t0 : u12_gate_chain [] 0 = true.
Proof. vm_compute. reflexivity. Qed.

(* ========== §4 the extra pieces ========== *)

(* The numeric regression for the uniform measure mu: mu [1;1;2] 1 = 2/3, pinned on both the Qeq face and the bool face *)
Theorem u12_mu_112_1 : mu [1;1;2] 1 == (2 # 3)%Q.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_mu_112_1_bool : Qeq_bool (mu [1;1;2] 1) (2 # 3)%Q = true.
Proof. vm_compute. reflexivity. Qed.

(* The freq regressions for the empty list and for a value of zero frequency *)
Theorem u12_freq_nil : freq [] 1 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem u12_freq_1223_5 : freq [1;2;2;3] 5 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(* The executable universal form of the degenerate phase_side evidence: the
   base rot = firstn ++ skipn is the identity, Pinf l s = l, and the decision
   reduces to C_sorted_min_adj (the P0-side H_adj never increases).  This
   piece is a Prop-face documentation theorem, not part of the extraction
   chain; its concrete-value behaviour is already pinned by the three §2
   instances. *)
(* Deprecation note: under the rot = firstn ++ skipn identity base this theorem is a disguised identity corollary; the operational semantics follow the realized layers DTPT_ROTC / DTPT_Cyc / DTPT_RotSpec. *)
Theorem u12_phase_side_always_zero : forall (l : list Q) (s : nat),
  phase_side l s = 0%nat.
Proof.
  intros l s. unfold phase_side, DTPT_Entropy.Pinf, DTPT_Entropy.rot.
  rewrite firstn_skipn.
  rewrite (xq_Qle_bool_true (DTPT_Entropy.H_adj (DTPT_Entropy.P0 l))
                            (DTPT_Entropy.H_adj l) (C_sorted_min_adj l)).
  reflexivity.
Qed.

End DTPT_Extract.

(* ========== closing note ==========
   Extraction artifact list (removed after the Obj.magic = 0 acceptance, the
   counts of this report stored in the upgrade report):
     gate_pass_ext.ml / H_adj_ext.ml / freq_ext.ml / mu_ext.ml /
     level_le_ext.ml / ev_size_ext.ml / trLevel_geq_ext.ml /
     phase_side_ext.ml / gate_chain_ext.ml
   The gold-standard regression face = all the closed vm_compute theorems of
   §2 + §3: any change to the base that turns one of these theorems red is a
   behaviour drift alarm. *)
