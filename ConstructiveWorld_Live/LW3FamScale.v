(* ========================================================================= *)
(* Module   : LW3FamScale                                                    *)
(* Mission. Factorial-reciprocal scaling of the Hermite family: the built    *)
(*   integrand under the scale 1/7!, coefficient- and derivative-level       *)
(*   linearity of the scalar operator, the scaled instances at scales one    *)
(*   and zero, the node functional with endpoint and pointwise floors and    *)
(*   weighted total pinned at both scales, eight strict reversals (all       *)
(*   pinned totals strictly below one), the scale-structure bridge pins,     *)
(*   and the per-node bound-family carrier with its joint bearing form.      *)
(* Dependencies. Stdlib QArith/Lia/Arith/ZArith/List/Extraction; S01_BaseRing*)
(*   (Id, Set-level And, NatLe), S02_CauchyComplete (QeqT/QltT/QleT',        *)
(*   qeq_imp_qeqT), S03_QExp (q_fact), LW0QPoly, LW1ZPoly, LW2Hermite,       *)
(*   LW2IntegMachine, LW0FactGrowth, LW2UpperBound, LW2NivenInt,             *)
(*   LW3ETranscendental (lw3_fbuild, lw3_deg, lw3_nodecount).                *)
(* References. Hermite's 1873 family with its 1/(N-1)!-type factorial        *)
(*   scaling; in-tree conventions per NsepBudgetVerify.v and the             *)
(*   LW0LeibWindow bridge family.                                            *)
(* Constructivity. Statement face all-Set: value pins are bool-match data,   *)
(*   reversals QltT, linearity QeqT, bound-family conclusions QleT' with     *)
(*   the Prop nat-order premises of the baseline face lifted to the          *)
(*   decidable Set face NatLe (Id of Nat.leb); the QltT embed inside sigT    *)
(*   pairs through the Set-level And (A * B). Linearity proofs route        *)
(*   through qeq_imp_qeqT (constructive Q-equality, proof-internal only,     *)
(*   Qeq decidable, no excluded-middle step); every constant is Defined so   *)
(*   conclusion faces extract; vm_compute only on concrete numeric pins.     *)
(* Build. rocq c -native-compiler no -q -Q <ConstructiveWorld-Set Live> ""   *)
(*   LW3FamScale.v, in this directory (r237_compile.py driver).              *)
(* ========================================================================= *)

From Stdlib Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith_base.
From Stdlib Require Import QArith.Qabs.
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

(* The anchor source polynomial one plus t. *)
Definition p381 : zpoly := cons 1%Z (cons 1%Z nil).

(* The two explicit scales of the joint accounting: one and zero. *)
Definition N1_381 : nat := 1.
Definition N0_381 : nat := 0.

(* The rank of the factorial-reciprocal scale constant. *)
Definition m381 : nat := 7.

(* The factorial-reciprocal scale constant at rank m. *)
Definition lw381_scale_const (m : nat) : Q := / (q_fact m)%Q.

(* The scaled family face: the built integrand under the factorial-       *)
(* reciprocal scalar. The scalar operator maps cons to cons, so the       *)
(* derivative-order count of the family is unchanged.                     *)
Definition lw381_fbuild_scaled (p : zpoly) (sg N m : nat) : QPoly :=
  qpoly_scalar (lw381_scale_const m) (lw3_fbuild p sg N).

(* The node counts at both scales. *)
Definition n1_381 : nat := lw3_nodecount p381 N1_381.
Definition n0_381 : nat := lw3_nodecount p381 N0_381.

(* The scaled family instances at both scales. *)
Definition f1_381 : QPoly := lw381_fbuild_scaled p381 (lw3_deg p381) N1_381 m381.
Definition f0_381 : QPoly := lw381_fbuild_scaled p381 (lw3_deg p381) N0_381 m381.

(* Scalar linearity at the coefficient level: every coefficient of the    *)
(* scaled polynomial is the scale constant times the base coefficient.    *)
Lemma lw381_coef_scalar : forall (a : Q) (f : QPoly) (j : nat),
  QeqT (lw0_coef j (qpoly_scalar a f)) ((a * lw0_coef j f)%Q).
Proof.
  intros a f. induction f as [|b f IH]; intro j.
  - cbn [qpoly_scalar lw0_coef]. apply qeq_imp_qeqT. ring.
  - destruct j as [|j].
    + cbn [qpoly_scalar lw0_coef]. apply qeq_imp_qeqT. ring.
    + cbn [qpoly_scalar lw0_coef]. apply IH.
Defined.

(* First-order dual face: differentiation passes through the scalar at    *)
(* every evaluation point, so each first derivative of the scaled family  *)
(* equals the scale constant times the unscaled one.                      *)
Lemma lw381_eval_deriv1_scalar : forall (a : Q) (g : QPoly) (x : Q),
  QeqT (qpoly_eval (qpoly_deriv (qpoly_scalar a g)) x)
       ((a * qpoly_eval (qpoly_deriv g) x)%Q).
Proof.
  intros a g x. apply qeq_imp_qeqT. destruct g as [|b g'].
  - cbn [qpoly_scalar qpoly_deriv qpoly_eval]. ring.
  - cbn [qpoly_scalar qpoly_deriv].
    rewrite qpoly_eval_add.
    rewrite qpoly_eval_add.
    cbn [qpoly_eval].
    rewrite qpoly_eval_scalar.
    rewrite qpoly_eval_deriv_scalar.
    rewrite qpoly_eval_scalar.
    cbn [qpoly_eval].
    ring.
Defined.

(* The pointwise floor on the scaled family: the sum of absolute          *)
(* derivative values over the full node and order grid.                   *)
Definition lw381_pwsum (n : nat) (f : QPoly) : Q :=
  lw2_qsum0 (fun j => lw2_qsum0 (fun k =>
      Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))
      (length f))
    (Datatypes.S (Datatypes.S n)).

(* The endpoint floor on the scaled family: the two endpoint absolute     *)
(* sums that any sound accounting of the node functional value covers.    *)
Definition lw381_rfsum (n : nat) (f : QPoly) : Q :=
  lw2_qsum0 (fun k => Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node 0)))
            (length f) +
  lw2_qsum0 (fun k =>
      Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node (Datatypes.S n))))
            (length f).

(* The per-node full sum, serving as the bound-family entry at each node. *)
Definition lw381_nodewsum (f : QPoly) (j : nat) : Q :=
  lw2_qsum0 (fun k => Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))
            (length f).

(* The bound-family entries at both scales, on the scaled instances. *)
Definition Ef1_381 : nat -> Q := lw381_nodewsum f1_381.
Definition Ef0_381 : nat -> Q := lw381_nodewsum f0_381.

(* Reversal value pins at scale one: functional value, endpoint floor and *)
(* pointwise floor of the scaled family, all over the rank-seven          *)
(* factorial denominator.                                                 *)
Definition lw381_lam1s_val :
  match Qeq_bool (lw2_lambda n1_381 f1_381) ((-265) # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw381_rf1s_val :
  match Qeq_bool (lw381_rfsum n1_381 f1_381) (281 # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw381_pw1s_val :
  match Qeq_bool (lw381_pwsum n1_381 f1_381) (613 # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

(* Reversal value pins at scale zero. *)
Definition lw381_lam0s_val :
  match Qeq_bool (lw2_lambda n0_381 f0_381) ((-15) # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw381_rf0s_val :
  match Qeq_bool (lw381_rfsum n0_381 f0_381) (19 # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw381_pw0s_val :
  match Qeq_bool (lw381_pwsum n0_381 f0_381) (34 # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

(* Structure bridge pins: multiplying the scaled functional value by the  *)
(* rank-seven factorial restores the unscaled functional value, so the    *)
(* congruence structure of the integer functional transfers through the   *)
(* scale in scaled-back form.                                             *)
Definition lw381_bridge1_val :
  match Qeq_bool ((q_fact m381)%Q * lw2_lambda n1_381 f1_381)
                  ((-265) # 1)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw381_bridge0_val :
  match Qeq_bool ((q_fact m381)%Q * lw2_lambda n0_381 f0_381)
                  ((-15) # 1)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

(* Weighted total of the bound family over the scaled instance: the       *)
(* derivative-order count times the family entries, summed over the       *)
(* node grid.                                                             *)
Definition lw381_wsum (p : zpoly) (N m : nat) (Ef : nat -> Q) : Q :=
  lw0_q_of_nat (length (lw381_fbuild_scaled p (lw3_deg p) N m)) *
  lw2_qsum0 Ef (Datatypes.S (Datatypes.S (lw3_nodecount p N))).

(* Weighted-total reversal value pins at both scales. *)
Definition lw381_wsum1s_val :
  match Qeq_bool (lw381_wsum p381 N1_381 m381 Ef1_381) (2452 # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

Definition lw381_wsum0s_val :
  match Qeq_bool (lw381_wsum p381 N0_381 m381 Ef0_381) (102 # 5040)%Q with
  | true => unit
  | false => Empty_set
  end := tt.

(* Strict reversal at scale one: the node functional value of the scaled  *)
(* family lies strictly below one in absolute value. *)
Theorem lw381_rev_lam1 :
  QltT (Qabs (lw2_lambda n1_381 f1_381)) (1 # 1)%Q.
Proof. vm_compute. constructor. Defined.

(* Strict reversal at scale one, endpoint floor. *)
Theorem lw381_rev_rf1 :
  QltT (lw381_rfsum n1_381 f1_381) (1 # 1)%Q.
Proof. vm_compute. constructor. Defined.

(* Strict reversal at scale one, pointwise floor. *)
Theorem lw381_rev_pw1 :
  QltT (lw381_pwsum n1_381 f1_381) (1 # 1)%Q.
Proof. vm_compute. constructor. Defined.

(* Strict reversal at scale one, weighted total. *)
Theorem lw381_rev_wsum1 :
  QltT (lw381_wsum p381 N1_381 m381 Ef1_381) (1 # 1)%Q.
Proof. vm_compute. constructor. Defined.

(* The four strict reversals at scale zero. *)
Theorem lw381_rev_lam0 :
  QltT (Qabs (lw2_lambda n0_381 f0_381)) (1 # 1)%Q.
Proof. vm_compute. constructor. Defined.

Theorem lw381_rev_rf0 :
  QltT (lw381_rfsum n0_381 f0_381) (1 # 1)%Q.
Proof. vm_compute. constructor. Defined.

Theorem lw381_rev_pw0 :
  QltT (lw381_pwsum n0_381 f0_381) (1 # 1)%Q.
Proof. vm_compute. constructor. Defined.

Theorem lw381_rev_wsum0 :
  QltT (lw381_wsum p381 N0_381 m381 Ef0_381) (1 # 1)%Q.
Proof. vm_compute. constructor. Defined.

(* The per-node bound-family premise in data form, reposed over the       *)
(* scaled family: every derivative value at every node of the grid is     *)
(* bounded by the family entry at that node. The grid bounds carry the    *)
(* decidable Set face NatLe (Id of Nat.leb) in place of the Prop nat      *)
(* order, so the carrier holds no proposition. *)
Definition lw381_pnode_fam (p : zpoly) (N m : nat) (Ef : nat -> Q) : Set :=
  forall (j k : nat),
    NatLe j (Datatypes.S (lw3_nodecount p N)) ->
    NatLe (Datatypes.S k) (length (lw381_fbuild_scaled p (lw3_deg p) N m)) ->
    QleT' (Qabs (qpoly_eval
                   (qpoly_deriv_iter k (lw381_fbuild_scaled p (lw3_deg p) N m))
                   (lw2_node j)))
          (Ef j).

(* The joint bearing form of the two-boundary production face, reposed    *)
(* over the scaled family at explicit scale rank: a bound family covering *)
(* every node value, whose weighted total stays below one.                *)
Definition lw381_joint_target (p : zpoly) (N m : nat) : Set :=
  sigT (fun Ef : nat -> Q =>
    And (lw381_pnode_fam p N m Ef)
        (QltT (lw381_wsum p N m Ef) (1 # 1)%Q)).

Print Assumptions lw381_coef_scalar.
Print Assumptions lw381_eval_deriv1_scalar.
Print Assumptions lw381_lam1s_val.
Print Assumptions lw381_rf1s_val.
Print Assumptions lw381_pw1s_val.
Print Assumptions lw381_lam0s_val.
Print Assumptions lw381_rf0s_val.
Print Assumptions lw381_pw0s_val.
Print Assumptions lw381_bridge1_val.
Print Assumptions lw381_bridge0_val.
Print Assumptions lw381_wsum1s_val.
Print Assumptions lw381_wsum0s_val.
Print Assumptions lw381_rev_lam1.
Print Assumptions lw381_rev_rf1.
Print Assumptions lw381_rev_pw1.
Print Assumptions lw381_rev_wsum1.
Print Assumptions lw381_rev_lam0.
Print Assumptions lw381_rev_rf0.
Print Assumptions lw381_rev_pw0.
Print Assumptions lw381_rev_wsum0.
Print Assumptions lw381_joint_target.

From Stdlib Require Import Extraction.
Separate Extraction p381 m381 n1_381 n0_381.
