(* Five-field pointer | Module: LW0PiTrigValues.v.
   Mission.  The values of sine and cosine at the geometric constant
   real_pi_geom (pi := 2 * cos_pi_half, the unique zero of the cosine on
   the interval (3/2, 5/3), see S10): the endpoint pair cos(pi) = -1 and
   sin(pi) = 0, the boundary inputs consumed by the Niven-type integral
   mechanism (constructive irrationality of pi).  Value-face wrapper
   piece: the value core is already Closed in the library module
   S12_B5RecycleSF (the b5p family); this piece restates the required
   statement faces via a Set-level And bridge and a real_const (-1)
   representation bridge.
   Dependencies.  S01_BaseRing, S02_CauchyComplete (constructive real ring
   core: real_eq, real_eq_trans, real_eq_of_zero_diff, qeq_imp_qeqT),
   S10_KVQuantTrig (cauchy_real_sin, cauchy_real_cos, cos_pi_half,
   real_pi_geom), S12_B5RecycleSF (b5p_sin_pi_geom_zero,
   b5p_cos_pi_geom_neg_one, b5p_pi_trig_signature); the Import of
   PropositionConvergenceCore resolves to the in-tree Module of that name
   inside S01_BaseRing.  Stdlib: QArith, Qabs, Qround, List, Bool, Arith,
   Setoid, Morphisms, Lia, Qminmax, Lqa.
   References.  I. Niven, A simple proof that pi is irrational, Bulletin
   of the American Mathematical Society 53 (1947), 509 - this piece
   supplies the endpoint values cos pi = -1 and sin pi = 0; the value
   core lives in the b5p family of S12_B5RecycleSF (pi trigonometric
   signature section).
   Constructivity.  All statement faces are Set-level (real_eq :
   Real -> Real -> Set; And is the Set-level product; none lives in Prop).
   Each proof cites a library b5p piece plus one Q-level pointwise identity
   closed by ring; every lemma prints [Closed under the global context].
   Build.  rocq c -native-compiler no -q -Q . "" LW0PiTrigValues.v, run in
   the flat world directory holding the born-in-place tree modules.
*)

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
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.
From Stdlib Require Import Lqa.
Opaque Qred.

(* ---- Representation bridge: real_opp real_one == real_const (-1)
   (a Q-level pointwise identity). ---- *)
Lemma lw0_real_opp_one_const : real_eq (real_opp real_one) (real_const (-1)%Q).
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  apply qeq_imp_qeqT.
  simpl.
  ring.
Qed.

(* ---- Main statement 1: cos(pi) == -1 ----
   b5p_cos_pi_geom_neg_one gives cos(pi) == real_opp real_one;
   lw0_real_opp_one_const re-expresses it as real_const (-1). *)
Lemma pi_geom_cos_pi_neg_one :
  real_eq (cauchy_real_cos real_pi_geom) (real_const (-1)%Q).
Proof.
  apply (real_eq_trans
    (cauchy_real_cos real_pi_geom)
    (real_opp real_one)
    (real_const (-1)%Q)).
  - exact b5p_cos_pi_geom_neg_one.
  - exact lw0_real_opp_one_const.
Qed.

(* ---- Main statement 2: sin(pi) == 0 ----
   Literally the statement face of b5p_sin_pi_geom_zero; cited directly. *)
Lemma pi_geom_sin_pi_zero :
  real_eq (cauchy_real_sin real_pi_geom) real_zero.
Proof.
  exact b5p_sin_pi_geom_zero.
Qed.

(* ---- Set-level product wrapper: the And certificate of the two
   endpoint values. ---- *)
Lemma pi_geom_trig_values :
  And (real_eq (cauchy_real_sin real_pi_geom) real_zero)
      (real_eq (cauchy_real_cos real_pi_geom) (real_const (-1)%Q)).
Proof.
  exact (pi_geom_sin_pi_zero, pi_geom_cos_pi_neg_one).
Qed.

Print Assumptions lw0_real_opp_one_const.
Print Assumptions pi_geom_cos_pi_neg_one.
Print Assumptions pi_geom_sin_pi_zero.
Print Assumptions pi_geom_trig_values.
