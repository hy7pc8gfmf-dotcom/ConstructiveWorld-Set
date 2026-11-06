(* ConstructiveWorld-Set -- premise-2 production pieces bridging lambda evaluation forms to the integration machine. *)

(** * LW3P2Prod: evaluation-form bridges to the integration machine endpoint functional.

    Mission.  This file formalizes the Q-layer half of the evaluation-form
      bridge on the premise-2 production side: lambda evaluation forms of the
      shape [F (0) - F (Datatypes.S n)] agree value by value with the
      integration machine endpoint functional [lw2_exp_L].  Main statements:
      the general bridge [tlw229_lam_expL] carried by [QeqT], the Niven
      anchor datum [tlw229_niven] with the kernel-computed instance pin
      [tlw229_lam_expL_niven] carried by [Id], and the zero-instance datum
      [lw3_p202] with the instance pin [tlw229_lam_expL_p202] carried by [Id].

    Dependencies.  Stdlib [QArith], [Arith], [ZArith], [List], and
      [QArith_base].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [LW0QPoly], [LW2Hermite], [LW2IntegMachine],
      [LW2NivenInt], and [LW3ETranscendental] of this development.

    References.  This development, LW3P2Prod.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" LW3P2Prod.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import QArith Arith ZArith List.
From Stdlib Require Import QArith_base.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW2Hermite.
Require Import LW2IntegMachine.
Require Import LW2NivenInt.
Require Import LW3ETranscendental.

(* (i) The general bridge: the lambda evaluation form and the integration
   machine endpoint functional agree value by value.  This is the Q-layer
   half of evaluation forms of the shape F(0) - F(Datatypes.S n): the
   endpoint table unfolds by [lw2_eps_eval_sum], a telescoping on the node
   [S (Datatypes.S n)] leaves only the first and last summands, and the
   coefficient table does not depend on k. *)
Theorem tlw229_lam_expL : forall (n : nat) (f : QPoly),
  QeqT (lw2_lambda n f)
       (lw2_exp_L (1 # 1)%Q (length f) f (lw2_node (Datatypes.S n))).
Proof.
  intros n f. apply qeq_imp_qeqT.
  unfold lw2_lambda, lw2_exp_L.
  rewrite (qeqT_imp_qeq _ _ (lw2_eps_eval_sum (length f) f 0%Q)).
  rewrite (qeqT_imp_qeq _ _ (lw2_eps_eval_sum (length f) f
             (lw2_node (Datatypes.S n)))).
  transitivity
    (lw2_qsum0 (fun j : nat =>
       (lw2_lambda_coef n j 0 # 1)%Q *
       lw2_qsum0 (fun k : nat =>
         qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f))
       (Datatypes.S (Datatypes.S n)))%Q.
  - apply (qeqT_imp_qeq _ _). apply lw2_qsum0_ext. intros j Hj.
    apply (qeq_imp_qeqT _ _).
    transitivity
      (lw2_qsum0 (fun k : nat =>
         (lw2_lambda_coef n j 0 # 1)%Q *
         qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f))%Q.
    + apply (qeqT_imp_qeq _ _). apply lw2_qsum0_ext. intros k Hk.
      apply (qeq_imp_qeqT _ _). reflexivity.
    + apply (qeqT_imp_qeq _ _). apply lw2_qsum0_scale.
  - transitivity
      ((lw2_qsum0 (fun j : nat =>
          (lw2_lambda_coef n j 0 # 1)%Q *
          lw2_qsum0 (fun k : nat =>
            qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f))
          (Datatypes.S n) +
        (lw2_lambda_coef n (Datatypes.S n) 0 # 1)%Q *
        lw2_qsum0 (fun k : nat =>
          qpoly_eval (qpoly_deriv_iter k f) (lw2_node (Datatypes.S n)))
          (length f))%Q).
    + reflexivity.
    + assert (Hd0 : (1 <= Datatypes.S n)%nat)
        by (apply le_n_S; apply Nat.le_0_l).
      assert (Hd1 : forall j : nat, (1 <= j)%nat -> (j < Datatypes.S n)%nat ->
                QeqT ((lw2_lambda_coef n j 0 # 1)%Q *
                  lw2_qsum0 (fun k : nat =>
                    qpoly_eval (qpoly_deriv_iter k f) (lw2_node j))
                  (length f)) 0%Q).
      { intros j Hj1 Hj2. apply (qeq_imp_qeqT _ _).
        destruct (Nat.eqb_spec j 0) as [Hj0 | Hj0].
        - rewrite Hj0 in Hj1. inversion Hj1.
        - destruct (Nat.eqb_spec j (Datatypes.S n)) as [Hjn | Hjn].
          ++ rewrite Hjn in Hj2.
             destruct (Nat.lt_irrefl (Datatypes.S n) Hj2).
          ++ unfold lw2_lambda_coef.
             rewrite (proj2 (Nat.eqb_neq j 0) Hj0).
             rewrite (proj2 (Nat.eqb_neq j (Datatypes.S n)) Hjn).
             cbn [Nat.eqb Z.add]. ring. }
      rewrite (qeqT_imp_qeq _ _ (lw2_qsum0_dirac (Datatypes.S n)
        (fun j : nat => (lw2_lambda_coef n j 0 # 1)%Q *
          lw2_qsum0 (fun k : nat =>
            qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)) (length f))
        Hd0 Hd1)).
      cbv beta.
      unfold lw2_lambda_coef. rewrite !Nat.eqb_refl.
      cbn [Nat.eqb Z.add].
      change (lw2_node (0 % nat)) with (0 # 1)%Q. ring.
Qed.

(* The anchor datum: the Niven source polynomial with a = 1, b = 1, n = 2,
   i.e. t^2 (1 - t)^2 with coefficient list [0;0;1;-2;1], given in closed
   form by [lw2_niven_int_f] as pure [Set] data. *)
Definition tlw229_niven : QPoly := lw2_niven_int_f 1%Z 1%Z 2%nat.

(* (ii) The Niven anchor instance pin, carried by [Id] and closed by kernel
   computation: both sides reduce to the same rational literal -240,
   consistent with the endpoint values F(0) = 14 and F(3) = 254. *)
Theorem tlw229_lam_expL_niven :
  Id (lw2_exp_L (1 # 1)%Q (length tlw229_niven) tlw229_niven (lw2_node 3))
     (lw2_lambda 2 tlw229_niven).
Proof. vm_compute. apply id_refl. Qed.

(* The recorded zero-instance datum of the case (iii) pin below:      *)
(* p202 = [-46;7], i.e. -46 + 7 t, at exponent N = 1 with Kinst = 0.  *)
Definition lw3_p202 := cons (-46)%Z (cons 7%Z nil).

(* (iii) The p202 case instance pin, carried by [Id]: the bridge also holds
   on the Kinst = 0 instance of the case p202 = [-46;7] at N = 1.  The bridge
   holds unconditionally and does not certify nonvanishing on the production
   side. *)
Theorem tlw229_lam_expL_p202 :
  Id (lw2_exp_L (1 # 1)%Q
        (length (lw3_fbuild lw3_p202 (lw3_deg lw3_p202) 1))
        (lw3_fbuild lw3_p202 (lw3_deg lw3_p202) 1)
        (lw2_node (Datatypes.S (lw3_nodecount lw3_p202 1))))
     (lw2_lambda (lw3_nodecount lw3_p202 1)
                 (lw3_fbuild lw3_p202 (lw3_deg lw3_p202) 1)).
Proof. vm_compute. apply id_refl. Qed.

Print Assumptions tlw229_lam_expL.
Print Assumptions tlw229_lam_expL_niven.
Print Assumptions tlw229_lam_expL_p202.
