(* ========================================================================= *)
(* Module   : LW3CarrierFull                                                 *)
(* Mission. Zero-premise exponential carrier: for every rational X an        *)
(*          explicit index M exists with the real distance between e^X and   *)
(*          its partial-sum approximation [tlw383_EQ X M] below eps(X) :=    *)
(*          (positive rational lower bound of e^X)/2.  The kills premise is  *)
(*          discharged upstream (LW3Kills); picking eps(X) automatically     *)
(*          removes the remaining premise.  The polynomial-in-e variant      *)
(*          keeps p(e) = 0 as an honest conditional premise (unused by      *)
(*          the carrier production; kept for downstream irrationality); an   *)
(*          anchor instance pins X = -2.                                     *)
(* Dependencies. Stdlib QArith/QArith_base/Extraction; S02_CauchyComplete    *)
(*          (QltT, real faces, qltT_0_2, qltT_div_pos), S03_QExp (exp,       *)
(*          exp_pos, real_metric), LW3ESlot (tlw383_EQ), LW3Kills            *)
(*          (tlw398_carrier_discharge), LW3ETranscendental (lw3_e,           *)
(*          lw3_evalr, lw3_nodecount), LW2Hermite (lw2_node), LW1ZPoly       *)
(*          (zpoly).                                                         *)
(* References. S01_BaseRing :46 [And A B := A * B], the Set-face product     *)
(*          inside real_lt; the landed NsepBudgetVerify.v for the header     *)
(*          convention and the tail assumption audit.                        *)
(* Constructivity. Statement faces are all Set: QltT is the decidable        *)
(*          identity [Id (Qlt_bool x y) true]; real_lt/real_eq are Set       *)
(*          witnesses over QltT, And is the Set product, so sigT carriers    *)
(*          embed zero Prop components; Prop reasoning stays inside proof    *)
(*          bodies via constructive library lemmas.  Everything ends         *)
(*          [Defined]: no pure-Prop bridge, hence no [Qed] and no waiver;    *)
(*          zero axioms, zero admits; extraction consumes [exp_carrier_M].   *)
(* Build. coqc -native-compiler no -q -Q <Set Live root> ""                  *)
(*          LW3CarrierFull.v (single shot, this directory as workdir).       *)
(* ========================================================================= *)

Require Import QArith.
From Stdlib Require Import QArith_base.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW1ZPoly.
Require Import LW2Hermite.
Require Import LW3ETranscendental.
Require Import LW3ESlot.
Require Import LW3Kills.

(* LW1ZPoly opens Z_scope at file level and that opening leaks through the   *)
(* Require chain; reopen the rational scope so the bare numerals of this     *)
(* file denote rationals.  Nat constructors below carry the explicit         *)
(* Datatypes prefix, so no scope reading depends on the leak.                *)
Local Open Scope Q_scope.

(* ================= Section 1: the tolerance, an explicit positive rational = *)

(* The exponential [cauchy_real_exp_pos] witnesses strict positivity of e^X  *)
(* as a [real_lt] sigT structure; its first component is an explicit         *)
(* positive rational lower bound of e^X.  Halving it keeps a strict margin   *)
(* for the downstream transport.                                             *)
Definition exp_tol (X : Q) : Q :=
  projT1 (cauchy_real_exp_pos (real_const X)) / 2.

Lemma exp_tol_pos : forall X : Q, QltT 0 (exp_tol X).
Proof.
  intros X. unfold exp_tol.
  apply (qltT_div_pos (projT1 (cauchy_real_exp_pos (real_const X))) 2).
  - exact (fst (projT2 (cauchy_real_exp_pos (real_const X)))).
  - exact qltT_0_2.
Defined.

(* ================= Section 2: the carrier at zero non-conditional premises = *)

(* The upstream discharge [tlw398_carrier_discharge] takes the kills premise *)
(* away from the slot carrier; instantiating its tolerance argument at the   *)
(* automatic [exp_tol X] removes the last premise, so the assembled          *)
(* statement carries no premise at all.                                      *)
Theorem exp_carrier : forall X : Q,
  sigT (fun M : nat =>
    real_lt (real_metric (cauchy_real_exp (real_const X))
                          (real_const (tlw383_EQ X M)))
            (real_const (exp_tol X))).
Proof.
  intros X.
  exact (tlw398_carrier_discharge X (exp_tol X) (exp_tol_pos X)).
Defined.

(* The threshold index as an explicit computable function of X: the first    *)
(* component of the carrier witness.                                         *)
Definition exp_carrier_M (X : Q) : nat :=
  projT1 (exp_carrier X).

(* ================ Section 3: the polynomial-in-e variant, conditional face = *)

(* The evaluation side-condition p(e) = 0 is carried verbatim as the         *)
(* antecedent [real_eq (lw3_evalr p lw3_e) real_zero].  The carrier          *)
(* production at the exponent node X = -(S (nodecount p N)) does not use     *)
(* it: the premise exists for the downstream nonzero-transport steps.        *)
Theorem exp_carrier_poly_e : forall (p : zpoly) (Nn : nat),
  real_eq (lw3_evalr p lw3_e) real_zero ->
  sigT (fun M : nat =>
    real_lt (real_metric
               (cauchy_real_exp
                  (real_const (- lw2_node (Datatypes.S (lw3_nodecount p Nn)))))
               (real_const (tlw383_EQ
                  (- lw2_node (Datatypes.S (lw3_nodecount p Nn))) M)))
            (real_const (exp_tol
               (- lw2_node (Datatypes.S (lw3_nodecount p Nn)))))).
Proof.
  intros p Nn Hpzero.
  exact (exp_carrier (- lw2_node (Datatypes.S (lw3_nodecount p Nn)))).
Defined.

(* =================================== Section 4: the anchor instance ======== *)

(* At X = -2 the carrier produces its witness with no premise and no         *)
(* computation side-condition, against the automatically picked tolerance.   *)
Theorem exp_carrier_anchor :
  sigT (fun M : nat =>
    real_lt (real_metric
               (cauchy_real_exp
                  (real_const (- lw2_node (Datatypes.S (Datatypes.S O)))))
               (real_const (tlw383_EQ
                  (- lw2_node (Datatypes.S (Datatypes.S O))) M)))
            (real_const (exp_tol
               (- lw2_node (Datatypes.S (Datatypes.S O)))))).
Proof.
  exact (exp_carrier (- lw2_node (Datatypes.S (Datatypes.S O)))).
Defined.

(* ===================== Section 5: assumption audit and the extraction face = *)

Print Assumptions exp_tol_pos.
Print Assumptions exp_carrier.
Print Assumptions exp_carrier_poly_e.
Print Assumptions exp_carrier_anchor.

From Stdlib Require Import Extraction.
Separate Extraction exp_carrier_M.
