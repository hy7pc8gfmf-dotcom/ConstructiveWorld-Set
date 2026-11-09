(* ConstructiveWorld-Set -- the loop-6 kills lemma of the convergence chain. *)

(** * LW3Kills: the loop-6 kills lemma and the interface discharge at its witness.

    Mission.  The loop-6 kills lemma [tlw398_kills]: for [QltT 0 eps] it
      exhibits the threshold [M] with [2 * Qabs X <= M + 1] and the bound
      [QltT (tlw383_geom_bound X M) eps] as sigT data over a Set-level
      conjunction; [tlw398_kills_M] makes [M] an explicit computable
      function of [X] and [eps]; [tlw398_carrier_discharge] fills the second
      premise slot of [tlw383_eslot_carrier], and [tlw398_anchor_discharge]
      anchors the interface at the anchor instance eps = 1.

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [ZArith.ZArith],
      [List.List], [Lia], [QArith_base], [QArith.Qabs], [Extraction].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [LW0QPoly], [LW0FactGrowth], [LW2Hermite], [LW3ESlot] of this
      development.

    References.  This development, LW3Kills.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" LW3Kills.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith_base.
From Stdlib Require Import QArith.Qabs.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW0FactGrowth.
Require Import LW2Hermite.
Require Import LW3ESlot.

(* ================= Section 0. visibility of the chain lemmas in scope ================= *)

Check q_arch_geom.
Check arch_decay.
Check exp_tail_arch.
Check q_pow_fact2_nonneg.
Check qabs_nonnegT.
Check QleT'_to_Qle.
Check Qle_to_QleT'.
Check QltT_to_Qlt.
Check qleT'_trans.
Check qeq_leT'.
Check NatLe_lift.
Check tlw383_geom_bound.
Check tlw383_eslot_carrier.
Print lw0_q_of_nat.

(* ================= Section 1. the kills lemma: eps-instantiation closing the loop-6 gap ================= *)

(* the explicit threshold datum: take [N0] from the archimedean ceiling slot
   witness [q_arch_geom (Qabs X)], [t] from the geometric eps-instance
   witness [arch_decay front eps], and [M := N0 + S t].  the three segments:
   (a) the [N0 <= M+1] segment: [2*|X| <= (u+1)#1] holds for every [u >= N0]
       by the projection of [q_arch_geom], and taking [u := M] gives
       [2*|X| <= M+1] (the ring identity [(1+1)*A = 2*A] folds the shape);
   (b) the front constant: [front := (|X|^N0 / N0!) * 2 >= 0] by
       [q_pow_fact2_nonneg];
   (c) the tail: [t] realizes [front * (1/2)^(S t) < eps] by [arch_decay],
       and at [b := M >= N0 + S t] the ratio-product decomposition of
       [exp_tail_arch] along [pow_fact_decay] presses the bound
       [B_M < eps]. *)
Theorem tlw398_kills : forall (X eps : Q),
  QltT 0 eps ->
  sigT (fun M : nat =>
    And (QleT' (2 * Qabs X) (lw0_q_of_nat (M + 1)))
        (QltT (tlw383_geom_bound X M) eps)).
Proof.
  intros X eps Heps0.
  destruct (q_arch_geom (Qabs X)) as [N0 Hgeom].
  assert (HA : QleT' 0 (Qabs X)).
  { apply qabs_nonnegT. }
  assert (Hgq : forall u : nat, NatLe N0 u ->
           QleT' (Qmult (1 + 1)%Q (Qabs X)) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply Hgeom. exact Hu. }
  assert (Hf0 : QleT' 0 ((q_pow (Qabs X) N0 / q_fact N0) * (1 + 1)%Q)).
  { apply (q_pow_fact2_nonneg (Qabs X) N0 HA). }
  destruct (arch_decay ((q_pow (Qabs X) N0 / q_fact N0) * (1 + 1)%Q) eps
             Hf0 Heps0) as [t Hdec].
  exists ((N0 + Datatypes.S t)%nat). split.
  - apply (qleT'_trans (2 * Qabs X) (Qmult (1 + 1)%Q (Qabs X))
             (lw0_q_of_nat (((N0 + Datatypes.S t) + 1)%nat))).
    + apply qeq_leT'. apply qeq_imp_qeqT. ring.
    + unfold lw0_q_of_nat. apply Hgeom.
      apply NatLe_lift. lia.
  - unfold tlw383_geom_bound.
    apply (exp_tail_arch (Qabs X) N0 t ((N0 + Datatypes.S t)%nat) eps HA Hgq).
    + exact Heps0.
    + exact Hdec.
    + lia.
Qed.

(* the witness-extraction datum: the threshold M as an explicit computable function of X and eps into [nat] *)
Definition tlw398_kills_M (X eps : Q) (Heps0 : QltT 0 eps) : nat :=
  projT1 (tlw398_kills X eps Heps0).

(* ================= Section 2. interface check: the kills witness fills the open premise slot of [tlw383_eslot_carrier] ================= *)

(* one premise slot fewer: the upstream carrier takes the two premises
   ([QltT 0 eps] and the kills shape) to the [real_lt]-face conclusion,
   and this file derives the same conclusion from the single premise
   [QltT 0 eps] alone by instantiating the kills shape with
   [tlw398_kills]; the upstream carrier is used unchanged, and the second
   premise face matches its statement verbatim. *)
Theorem tlw398_carrier_discharge : forall (X eps : Q),
  QltT 0 eps ->
  sigT (fun M : nat =>
    real_lt (real_metric (cauchy_real_exp (real_const X))
                          (real_const (tlw383_EQ X M)))
            (real_const eps)).
Proof.
  intros X eps Heps0.
  exact (tlw383_eslot_carrier X eps Heps0 (tlw398_kills X eps Heps0)).
Qed.

(* ================= Section 3. anchored instance: at X := -node 2 (|X| = 2) and eps := 1 the kills shape yields the real distance < 1 ================= *)

(* the same use position as [tlw383_eslot_anchor]: the kills shape is not
   vacuous at the anchor, and the single premise 0 < 1 alone produces the
   M witness together with the real distance < 1, the instantiation form
   of the interface statement above. *)
Theorem tlw398_anchor_discharge :
  sigT (fun M : nat =>
    real_lt (real_metric
               (cauchy_real_exp
                  (real_const (- lw2_node (Datatypes.S (Datatypes.S O)))))
               (real_const (tlw383_EQ
                  (- lw2_node (Datatypes.S (Datatypes.S O))) M)))
            (real_const (1 # 1)%Q)).
Proof.
  apply (tlw398_carrier_discharge
          (- lw2_node (Datatypes.S (Datatypes.S O))) (1 # 1)%Q).
  unfold QltT, Qlt_bool. vm_compute. reflexivity.
Qed.

(* ================= Section 4. extraction audit: the threshold-M computable function ================= *)

(* The closedness audit of the named exit pieces, printed at build time. *)
Print Assumptions tlw398_kills.
Print Assumptions tlw398_kills_M.
Print Assumptions tlw398_carrier_discharge.
Print Assumptions tlw398_anchor_discharge.

From Stdlib Require Import Extraction.

(* The audit extraction reads the dependency lemmas through Qed opacity
   by construction and writes beside the working directory; the two
   extraction notices carry no substantive content here. *)
Set Warnings "-extraction-opaque-accessed".
Set Extraction Output Directory ".".
Separate Extraction tlw398_kills_M.
