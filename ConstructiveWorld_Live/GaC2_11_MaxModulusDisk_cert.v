(* ConstructiveWorld, GaC2_11_MaxModulusDisk_cert (node C2-11,
   segment C2, slot W2, certificate piece): the rational sample
   certificates of the maximum-modulus growth closed forms.
   Mission.  The rational-level mirrors of the growth-lemma closed
     forms and their sample points: cert_tau (the gain-scale
     tau = s0 s1 / (s0 + (R/4) s1)), cert_theta (the adaptive
     theta factor tau / (4 sqT r4)), cert_rho (the adaptive radius
     (theta / (1 + theta)) scaled by R/4), and cert_gain (the gain
     increment (1/2) rho tau).  Sample lemmas at the unit instance
     s0 = s1 = sqT = R = 1: tau = 4/5, theta = 4/5, rho = 1/9, the
     gain increment 2/45 (the total gain factor 47/45), the radius
     modulus face rho^2 = 1/81, and the radius bound rho < 1/2.
     The chain-walk step-count certificate belongs to the chain
     interface premise of the node statement piece and is not
     carried here.
   Dependencies.  Stdlib QArith.QArith.  Requires S01_BaseRing (the
     Set-level identity type Id) and S02_CauchyComplete (QeqT, QltT)
     of this development.
   References.  drafts_C2.md C2.11 certificate note (the gain
     constant and step-bound samples); the closed forms are the
     rational mirrors of the statement-piece growth direction.
   Constructivity.  All statements are Set-sorted rational decisions
     (QeqT, QltT).  Every definition is transparent; each sample
     lemma closes with the explicit boolean witness term id_refl on
     true, the rational comparison of the two sides reducing to the
     Eq (respectively Lt) verdict by kernel conversion; zero
     assumed constants.
   Build.  coqc -native-compiler no -q -Q <certified vo tree> ""
     -o <sandbox>/GaC2_11_MaxModulusDisk_cert.vo
     <sandbox>/GaC2_11_MaxModulusDisk_cert.v, thermal guard wrapper. *)

From Stdlib Require Import QArith.QArith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.

(* Rational mirror of tau = s0 s1 / (s0 + (R/4) s1). *)
Definition cert_tau (s0 s1 r : Q) : Q := (s0 * s1) / (s0 + ((1#4) * r) * s1).

(* Rational mirror of theta = tau / (4 sqT r4). *)
Definition cert_theta (tau sqT r4 : Q) : Q := tau / ((4#1) * (sqT * r4)).

(* Rational mirror of rho = (R/4) * theta / (1 + theta). *)
Definition cert_rho (r tau sqT : Q) : Q :=
  ((1#4) * r) * (cert_theta tau sqT ((1#4) * r))
    / (1 + cert_theta tau sqT ((1#4) * r)).

(* Rational mirror of the gain increment (1/2) rho tau. *)
Definition cert_gain (tau rho : Q) : Q := (1#2) * (rho * tau).

(* Sample certificates at the unit instance s0 = s1 = sqT = R = 1.
   Each lemma is a definitional closure: the boolean reflection of
   the rational comparison reduces to the identity type on true,
   and the explicit witness term id_refl inhabits it. *)

(* Sample: the gain scale at the unit instance. *)
Lemma cert_tau_sample : QeqT (cert_tau 1 1 1) (4#5)%Q.
Proof. exact (@id_refl _ true). Defined.

(* Sample: the theta factor at the unit instance. *)
Lemma cert_theta_sample : QeqT (cert_theta (4#5)%Q 1 ((1#4)%Q)) (4#5)%Q.
Proof. exact (@id_refl _ true). Defined.

(* Sample: the adaptive radius at the unit instance. *)
Lemma cert_rho_sample : QeqT (cert_rho 1 (4#5)%Q 1) (1#9)%Q.
Proof. exact (@id_refl _ true). Defined.

(* Sample: the radius modulus face at the unit instance. *)
Lemma cert_rho_sq_sample :
  QeqT ((cert_rho 1 (4#5)%Q 1) * (cert_rho 1 (4#5)%Q 1)) (1#81)%Q.
Proof. exact (@id_refl _ true). Defined.

(* Sample: the gain increment at the unit instance. *)
Lemma cert_gain_sample : QeqT (cert_gain (4#5)%Q (1#9)%Q) (2#45)%Q.
Proof. exact (@id_refl _ true). Defined.

(* Sample: the radius stays below the half-radius cap. *)
Lemma cert_rho_bound_sample : QltT (cert_rho 1 (4#5)%Q 1) (1#2)%Q.
Proof. exact (@id_refl _ true). Defined.
