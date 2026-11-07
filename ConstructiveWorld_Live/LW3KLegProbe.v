(* ConstructiveWorld-Set — the general form of the K-nonzero criterion probed at a zero instance. *)

(** * LW3KLegProbe: the K-nonzero criterion in general form, refuted at a zero instance.

    Mission.  The zero-instance polynomial [p377] = -46 + 7 t voids the
      K-face witness type at the first exponent instance: the node
      functional vanishes ([lam377_zero]), so [kleg377_empty] derives
      [Empty_set] from the K witness (unconditional K-witness
      production from [p377_nz] admits no construction); [lam377b_div]
      pins the divisibility of the anchor value -265 by node shift 5.

    Dependencies.  Stdlib [QArith], [Lia], [Arith], [ZArith], [List],
      [QArith_base]; requires [S02_CauchyComplete], [S03_QExp], the
      LW0/LW1/LW2 modules and [LW3ETranscendental] of this development
      (read-only).

    References.  This development, [LW3ETranscendental].v; the baseline
      module of the same name in ConstructiveWorld-Main, whose statement
      names are carried over here verbatim.

    Constructivity.  All statements carried by [Set]: the voiding
      theorem [kleg377_empty] targets [Empty_set], [p377_nz] is a [sigT]
      inhabitation, value pins ride [match] over [Qeq_bool]/[Z.eqb];
      zero admission words; no classical axioms; extraction names data
      only ([p377], [p377b]), with generic library-lemma parameters
      surfacing as [Obj.magic] (disclosed per the extraction census).

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      LW3KLegProbe.v] compiles cleanly (exit 0); the first eight bytes of
      the artifact are [436f7121 00015ff4]. *)
Require Import QArith Lia Arith ZArith List.
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

(* The zero instance: the polynomial -46 + 7 t, whose node functional    *)
(* vanishes at the first exponent instance, so the K witness type is     *)
(* empty there although the polynomial witness is inhabited.             *)
Definition p377 : zpoly := cons (-46)%Z (cons 7%Z nil).

(* The master nonzero witness on this datum: the coefficient at index    *)
(* zero compares nonzero in the decidable integer order, recorded as the *)
(* uniform Id verdict data (the decidable content of lw3_nz p377).       *)
Definition p377_nz :
  @Id bool false (Z.eqb (nth 0 p377 0%Z) 0%Z) := id_refl.

(* The node functional of the built integrand vanishes: the boolean      *)
(* decision against zero takes the true branch on the transparent path,  *)
(* recorded in the uniform Id carrier for the match-typed witness face.  *)
Definition lam377_zero :
  @Id bool true (Qeq_bool (lw2_lambda (lw3_nodecount p377 1)
                                       (lw3_fbuild p377 (lw3_deg p377) 1))
                          (0 # 1)%Q) := id_refl.

(* Collapse face: the K witness type is uninhabited at this instance,    *)
(* since the integer value rides the vanishing functional through the    *)
(* lambda bridge.  Together with p377_nz this certifies that the         *)
(* unconditional production of the K witness from the polynomial witness *)
(* admits no construction.                                               *)
Theorem kleg377_empty :
  lw3_qnz ((lw3_Kinst p377 1) # 1)%Q -> Empty_set.
Proof.
  intro Hk.
  assert (HzK : lw3_Kinst p377 1 = 0%Z).
  { assert (Eb : Qeq_bool (lw2_lambda (lw3_nodecount p377 1)
                                      (lw3_fbuild p377 (lw3_deg p377) 1))
                          0%Q = true)
      by (vm_compute; reflexivity).
    pose proof (qeqT_imp_qeq _ _ (lw3_Kinst_spec p377 1)) as Es.
    apply Qeq_bool_eq in Eb.
    unfold Qeq in Eb, Es.
    cbn [Qnum Qden] in Eb, Es.
    rewrite Z.mul_1_r in Eb, Es.
    rewrite Z.mul_0_l in Eb.
    rewrite Eb in Es.
    symmetry in Es.
    apply Z.mul_eq_0 in Es.
    destruct Es as [Hz | Hd].
    - exact Hz.
    - discriminate Hd. }
  (* Discharged inside a Prop-level False, which the extraction face      *)
  (* erases; False_rect then finishes the Set-sorted Empty_set            *)
  (* conclusion, so the extracted body renders without magic.             *)
  assert (HC : False).
  { unfold lw3_qnz in Hk.
    destruct (Qeq_bool ((lw3_Kinst p377 1) # 1)%Q 0%Q) eqn:Eb.
    - destruct Hk.
    - assert (Et : Qeq_bool ((lw3_Kinst p377 1) # 1)%Q 0%Q = true).
      { rewrite HzK. apply Qeq_bool_refl. }
      rewrite Et in Eb. discriminate Eb. }
  exact (False_rect Empty_set HC).
Qed.

(* Divisibility face on the recorded anchor: the functional value -265   *)
(* leaves no remainder under the node shift 5, the trace of the termwise *)
(* congruence of each derivative value against its coefficient factorial.*)
Definition p377b : zpoly := cons 1%Z (cons 1%Z nil).
(* The divisibility pin in the uniform Id carrier: the boolean decision  *)
(* "no remainder" holds on the transparent computation path.             *)
Definition lam377b_div :
  @Id bool true (Z.eqb (Z.modulo
                          (Qnum (lw2_lambda (lw3_nodecount p377b 1)
                                            (lw3_fbuild p377b (lw3_deg p377b) 1)))
                          5%Z)
                       0%Z) := id_refl.

Print Assumptions p377_nz.
Print Assumptions kleg377_empty.
Print Assumptions lam377b_div.

Separate Extraction p377 p377b.
