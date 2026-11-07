(* ConstructiveWorld-Set — numeric instantiation of the count-times-E strict premise. *)

(** * LW3CountEBound: the count-times-E premise instantiated at the anchor polynomial.

    Mission.  On the anchor [p374] = 1 + t at scale one ([N374]), the
      master premise "node-count factor times decay scalar below one" is
      witnessed at the explicit pair ([N374], [E374]): [lw3_countE374]
      packages the decay positivity (via [lw3_decay_E_posT]) and the
      strict [QltT] comparison; the boundary data [lw3_p3viol374],
      [lw3_f5374_val] and kin, [lw3_joint374] delimit the per-node bound
      grid at the top node.

    Dependencies.  Stdlib [QArith], [Lia], [Arith], [ZArith], [List],
      [QArith_base], [QArith.Qabs]; requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], the LW0/LW1/LW2 modules and
      [LW3ETranscendental] (read-only) of this development.

    References.  This development, [LW3ETranscendental].v; the baseline
      module of the same name in ConstructiveWorld-Main, whose statement
      names are carried over here verbatim.

    Constructivity.  All named statements are carried by [Set]
      ([sigT] witnesses, [And] products and [QltT] strict forms); zero
      admission words; no classical axioms; extraction names data only
      ([p374], [N374], [m374], [count374], [E374]), with generic lemma
      parameters surfacing as [Obj.magic] (disclosed per the census).

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      LW3CountEBound.v] compiles cleanly (exit 0); the first eight bytes
      of the artifact are [436f7121 00015ff4]. *)
Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith.Qabs.
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

(* Anchor instance: the source polynomial one plus t, scale one.         *)
Definition p374 : zpoly := cons 1%Z (cons 1%Z nil).

(* Explicit instantiation data: the scale of the built integrand and the *)
(* derivative-order index of the registered decay form, whose value is   *)
(* the reciprocal of six factorial.                                      *)
Definition N374 : nat := 1.
Definition m374 : nat := 3.
Definition E374 : Q := lw3_decay_E m374.

(* The node-count factor of the master statement on the anchor instance. *)
Definition count374 : nat :=
  Datatypes.S (Datatypes.S (lw3_nodecount p374 N374)) *
  length (lw3_fbuild p374 (lw3_deg p374) N374).

(* Main brick: the count-times-E strict premise of the master statement  *)
(* is witnessed at the explicit pair, with positivity of the decay scale *)
(* supplied by the library production lemma and the strict comparison    *)
(* decided on the transparent computation path.                          *)
Theorem lw3_countE374 :
  sigT (fun N : nat => sigT (fun E : Q =>
    And (QltT 0%Q E)
        (QltT (lw0_q_of_nat (Datatypes.S (Datatypes.S (lw3_nodecount p374 N)) *
                            length (lw3_fbuild p374 (lw3_deg p374) N)) * E)
              (1 # 1)%Q))).
Proof.
  exists N374. exists E374. split.
  - exact (lw3_decay_E_posT m374).
  - vm_compute. constructor.
Qed.

(* Machine pin: the node-count factor equals twenty-four.                *)
Definition lw3_count374_val :
  @Id bool true (Qeq_bool (lw0_q_of_nat count374) (24 # 1)%Q) := id_refl.

(* Machine pin: the decay scalar equals the reciprocal of seven hundred  *)
(* twenty.                                                               *)
Definition lw3_e374_val :
  @Id bool true (Qeq_bool E374 (1 # 720)%Q) := id_refl.

(* Boundary datum: the decay scalar is strictly below the anchor value   *)
(* of the second derivative at the endpoint node five, so the decay      *)
(* scalar cannot serve the per-node bound premise at scale one.          *)
Theorem lw3_p3viol374 :
  QltT E374 (Qabs (qpoly_eval
    (qpoly_deriv_iter 2 (lw3_fbuild p374 (lw3_deg p374) N374))
    (lw2_node 5))).
Proof. vm_compute. constructor. Qed.

(* Boundary datum: the four endpoint values of the per-node grid at the  *)
(* top node five, machine-pinned; every derivative of the anchor         *)
(* integrand has nonnegative coefficients, so each grid value is bounded *)
(* by its endpoint value.                                                *)
Definition lw3_f5374_val :
  @Id bool true (Qeq_bool (qpoly_eval (lw3_fbuild p374 (lw3_deg p374) N374)
                             (lw2_node 5)) (150 # 1)%Q) := id_refl.

Definition lw3_f15_374_val :
  @Id bool true (Qeq_bool (qpoly_eval (qpoly_deriv_iter 1 (lw3_fbuild p374 (lw3_deg p374) N374))
                             (lw2_node 5)) (85 # 1)%Q) := id_refl.

Definition lw3_f25_374_val :
  @Id bool true (Qeq_bool (qpoly_eval (qpoly_deriv_iter 2 (lw3_fbuild p374 (lw3_deg p374) N374))
                             (lw2_node 5)) (32 # 1)%Q) := id_refl.

Definition lw3_f35_374_val :
  @Id bool true (Qeq_bool (qpoly_eval (qpoly_deriv_iter 3 (lw3_fbuild p374 (lw3_deg p374) N374))
                             (lw2_node 5)) (6 # 1)%Q) := id_refl.

(* Boundary datum: the node-count factor times the endpoint maximum      *)
(* value exceeds one, so at scale one the strict count premise forces a  *)
(* scalar strictly below the reciprocal of the node-count factor, while  *)
(* the per-node premise forces at least the endpoint maximum.            *)
Theorem lw3_joint374 :
  QltT (1 # 1)%Q (lw0_q_of_nat count374 * (150 # 1)%Q).
Proof. vm_compute. constructor. Qed.

Print Assumptions lw3_countE374.
Print Assumptions lw3_count374_val.
Print Assumptions lw3_e374_val.
Print Assumptions lw3_p3viol374.
Print Assumptions lw3_f5374_val.
Print Assumptions lw3_f15_374_val.
Print Assumptions lw3_f25_374_val.
Print Assumptions lw3_f35_374_val.
Print Assumptions lw3_joint374.

From Stdlib Require Import Extraction.
Separate Extraction p374 N374 m374 count374 E374.
