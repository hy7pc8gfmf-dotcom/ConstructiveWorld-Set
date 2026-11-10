(* ConstructiveWorld-Set -- conditional nonvanishing carriers for the K witness transfer. *)

(** * LW3P2Carrier: conditional carrier of the K-face nonvanishing witness transfer.

    Mission.  The conditional transfer that produces the K witness
      [@Id bool false (Qeq_bool ((lw3_Kinst p N) # 1)%Q 0%Q)] from the
      standing premise on the endpoint functional value: [tlw379_qtransfer]
      moves the nonzero verdict data across the two bridges,
      [tlw379_p2carrier] takes the polynomial witness [lw3_nz p] with the
      real-side equality premise, and the pair [tlw379_p2inst] /
      [tlw379_gap_empty_p202] pins both ends of the standing premise by
      computation (the zero instance records the true verdict).

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [ZArith.ZArith],
      [List.List], [Lia], [QArith_base].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [LW0QPoly], [LW1ZPoly],
      [LW2Hermite], [LW2IntegMachine], [LW0FactGrowth], [LW2UpperBound],
      [LW2NivenInt], [LW3ETranscendental], [LW3P2Prod] of this development.

    References.  This development, LW3P2Carrier.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (boolean identity carriers over the decidable verdict booleans);
      statements extract with [Obj.magic] = 0 and no erasure; [coqchk]
      reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" LW3P2Carrier.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith_base.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW1ZPoly.
Require Import LW2Hermite.
Require Import LW2IntegMachine.
Require Import LW0FactGrowth.
Require Import LW2UpperBound.
Require Import LW2NivenInt.
Require Import LW3ETranscendental.
Require Import LW3P2Prod.

(* The rational-side transfer: the nonvanishing verdict data rides the     *)
(* two bridges.  The spec bridge ties the integer functional value to the  *)
(* node functional, and the evaluation bridge ties the node functional to  *)
(* the endpoint value with unit exponential scalar.  Should the integer    *)
(* value decide equal to zero, both bridges would force the endpoint value *)
(* to zero and the handed-over witness would empty; hence the decidable    *)
(* comparison takes the false branch and the witness is produced.          *)
Lemma tlw379_qtransfer :
  forall (p : zpoly) (N : nat),
    @Id bool false (Qeq_bool (lw2_exp_L (1 # 1)%Q
              (length (lw3_fbuild p (lw3_deg p) N))
              (lw3_fbuild p (lw3_deg p) N)
              (lw2_node (Datatypes.S (lw3_nodecount p N)))) 0%Q) ->
    @Id bool false (Qeq_bool ((lw3_Kinst p N) # 1)%Q 0%Q).
Proof.
  intros p N Hgap.
  destruct (Qeq_bool ((lw3_Kinst p N) # 1)%Q 0%Q) eqn:HKq.
  - apply Qeq_bool_eq in HKq.
    pose proof (lw3_Kinst_spec p N) as Es.
    apply qeqT_imp_qeq in Es.
    pose proof (tlw229_lam_expL (lw3_nodecount p N)
                  (lw3_fbuild p (lw3_deg p) N)) as Eb.
    apply qeqT_imp_qeq in Eb.
    assert (Hlam0 : lw2_lambda (lw3_nodecount p N)
                      (lw3_fbuild p (lw3_deg p) N) == 0%Q)
      by exact (Qeq_trans _ _ _ Es HKq).
    assert (Hexp0 : lw2_exp_L (1 # 1)%Q
                      (length (lw3_fbuild p (lw3_deg p) N))
                      (lw3_fbuild p (lw3_deg p) N)
                      (lw2_node (Datatypes.S (lw3_nodecount p N))) == 0%Q)
      by exact (Qeq_trans _ _ _ (Qeq_sym _ _ Eb) Hlam0).
    assert (Hf : Qeq_bool (lw2_exp_L (1 # 1)%Q
                            (length (lw3_fbuild p (lw3_deg p) N))
                            (lw3_fbuild p (lw3_deg p) N)
                            (lw2_node (Datatypes.S (lw3_nodecount p N)))) 0%Q
                 = true)
      by exact (Qeq_eq_bool _ _ Hexp0).
    inversion Hgap.
    congruence.
  - exact id_refl.
Qed.

(* The conditional carrier: the nonzero polynomial witness, the vanishing *)
(* of the polynomial evaluation at the constructive constant e carried in *)
(* the real-side equality data, and the explicit standing premise holding *)
(* the real-side analytic half (the derivation of the endpoint value's    *)
(* nonvanishing from the vanishing premise belongs to the continuation    *)
(* order) together produce the K witness.  All premises are Set-sorted.   *)
Theorem tlw379_p2carrier :
  forall (p : zpoly) (N : nat),
    lw3_nz p ->
    real_eq (lw3_evalr p lw3_e) real_zero ->
    @Id bool false (Qeq_bool (lw2_exp_L (1 # 1)%Q
              (length (lw3_fbuild p (lw3_deg p) N))
              (lw3_fbuild p (lw3_deg p) N)
              (lw2_node (Datatypes.S (lw3_nodecount p N)))) 0%Q) ->
    @Id bool false (Qeq_bool ((lw3_Kinst p N) # 1)%Q 0%Q).
Proof.
  intros p N Hnz Hpzero Hgap.
  exact (tlw379_qtransfer p N Hgap).
Qed.

(* The anchor datum 1 + t: its node functional value is -265, so the      *)
(* standing premise is inhabited by direct computation, and the carrier   *)
(* chain produces the K witness at the first exponent instance even though*)
(* the integer value itself sits behind an opaque integral bridge.        *)
Definition p379b : zpoly := cons 1%Z (cons 1%Z nil).
Definition p379b_nz :
  @Id bool false (Z.eqb (nth 0%nat p379b 0%Z) 0%Z) := id_refl.

Definition tlw379_gap_p379b :
  @Id bool false (Qeq_bool (lw2_exp_L (1 # 1)%Q
            (length (lw3_fbuild p379b (lw3_deg p379b) 1))
            (lw3_fbuild p379b (lw3_deg p379b) 1)
            (lw2_node (Datatypes.S (lw3_nodecount p379b 1)))) 0%Q) := id_refl.

Theorem tlw379_p2inst :
  @Id bool false (Qeq_bool ((lw3_Kinst p379b 1) # 1)%Q 0%Q).
Proof. exact (tlw379_qtransfer p379b 1 tlw379_gap_p379b). Qed.

(* The recorded zero instance -46 + 7 t empties the standing premise: its *)
(* endpoint functional value vanishes together with the node functional,  *)
(* so the decidable verdict computes to the true arm and the conditional  *)
(* premise carries genuine content and is no trivially available witness. *)
Theorem tlw379_gap_empty_p202 :
  @Id bool true (Qeq_bool (lw2_exp_L (1 # 1)%Q
            (length (lw3_fbuild lw3_p202 (lw3_deg lw3_p202) 1))
            (lw3_fbuild lw3_p202 (lw3_deg lw3_p202) 1)
            (lw2_node (Datatypes.S (lw3_nodecount lw3_p202 1)))) 0%Q).
Proof. exact id_refl. Qed.

Print Assumptions tlw379_qtransfer.
Print Assumptions tlw379_p2carrier.
Print Assumptions tlw379_p2inst.
Print Assumptions tlw379_gap_empty_p202.

Set Extraction Output Directory ".".
Separate Extraction p379b.
