(* ========================================================================= *)
(* Module   : abl_tail_world_certs                                          *)
(* Mission. Constructive certificates for a minimal two-point uniform-     *)
(*   kernel world over the Q-Cauchy Real carrier of S02 (states            *)
(*   true::false::nil, keep := constant true, delta := real_one, uniform   *)
(*   kernel K := inv(1+1) pointwise): row normalization tspw_kvev_Krow,    *)
(*   keep_nonempty witness load, delta_pos, delta_le_one, the chain lemma  *)
(*   tspw_kvev_two_inv_sum (c+(c+0) == (1+1)*c == 1), and eight            *)
(*   interface-face certificates lt zero one (beta / pi_ref / eta / L /    *)
(*   temp / Delta at one) for any RealInterfaceEnhanced carrier.         *)
(* Dependencies. S01_BaseRing (classes, Id/And/InT), S02_CauchyComplete    *)
(*   (Real, real_eq/real_lt/real_le, ring laws), S03_QExp (real_inv_pos,   *)
(*   real_inv_pos_correct), S07_RealSetoidExpLog (RealSetoid.              *)
(*   real_eq_plus_compat, real_lt_zero_one, real_plus_positive),           *)
(*   S08_RealMainlineDPO (real_list_sum); Stdlib List/Extraction.        *)
(* References. Format follows NsepBudgetVerify.v; S01_BaseRing.v:41/:46/   *)
(*   :77/:184/:268/:1080; S02_CauchyComplete.v:150/:227/:511/:513/:582/    *)
(*   :586/:2481/:2528/:2552/:2564/:2597; S03_QExp.v:6968/:7036;            *)
(*   S07_RealSetoidExpLog.v:248/:7625/:7642; S08_RealMainlineDPO.v:317.   *)
(* Constructivity. All thirteen statement faces are Set-carried, zero Prop:*)
(*   real_eq/real_lt/real_le are S02 Set values over the decidable Q-order *)
(*   (QltT :150 = Id (Qlt_bool x y) true, QeqT :227); every Qlt-embedded   *)
(*   sigT mirrors the landed S02 shape verbatim (declared here); the       *)
(*   interface predicate is the class's Set-valued field lt (S01:184).     *)
(*   All bodies Defined (no Qed: every face is a Set value and Set-valued  *)
(*   proofs must extract to real code); zero axioms, zero admits.        *)
(* Build. python3 -I r237_compile.py abl_tail_world_certs.v (rocq c        *)
(*   -native-compiler no -q -Q <Set Live root> "" here); green = exit 0,   *)
(*   no Error, one Closed per Print Assumptions, fresh Rocq 9.3 .vo magic.*)
(* ========================================================================= *)

From Stdlib Require Import List Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.

(* ============================================================ *)
(* Section 1. The minimal two-point uniform-kernel world (data).  *)
(*   Carrier: the two-point enumeration over bool. The state      *)
(*   count |states| = 2 is carried by N_R = 1 + 1 (constructive   *)
(*   positivity witness below); the kernel is pointwise constant  *)
(*   K s s' = inv N_R; the retention predicate is constantly      *)
(*   true; the step is delta := one.                             *)
(* ============================================================ *)

Definition tspw_kvev_tok : Set := bool.

Definition tspw_kvev_states : list tspw_kvev_tok := true :: false :: nil.

Definition tspw_kvev_keep : tspw_kvev_tok -> bool := fun _ => true.

Definition tspw_kvev_delta : Real := real_one.

Definition tspw_kvev_N_R : Real := real_plus real_one real_one.

Definition tspw_kvev_N_R_pos : real_lt real_zero tspw_kvev_N_R :=
  real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one.

Definition tspw_kvev_K (s s' : tspw_kvev_tok) : Real :=
  real_inv_pos tspw_kvev_N_R tspw_kvev_N_R_pos.

(* Concrete-carrier specialization of the generic reciprocal lemma
   real_inv_pos_correct at N_R; consumed verbatim by the row
   normalization theorem below. *)
Definition tspw_kvev_N_R_inv_correct :
  real_eq (real_mult tspw_kvev_N_R
             (real_inv_pos tspw_kvev_N_R tspw_kvev_N_R_pos)) real_one :=
  real_inv_pos_correct tspw_kvev_N_R tspw_kvev_N_R_pos.

(* ---- Arithmetic chain lemma --------------------------------- *)
(* For any c with N_R * c == 1:  c + (c + 0) == c + c ==         *)
(* (c*1) + (c*1) == c*(1+1) == N_R*c == 1.  Every step is a      *)
(* real_eq equality step over the concrete Real carrier.         *)
Lemma tspw_kvev_two_inv_sum : forall (c : Real)
  (Hc : real_eq (real_mult tspw_kvev_N_R c) real_one),
  real_eq (real_plus c (real_plus c real_zero)) real_one.
Proof.
  intros c Hc.
  exact (real_eq_trans
          (real_plus c (real_plus c real_zero))
          (real_plus c c)
          real_one
          (RealSetoid.real_eq_plus_compat c (real_plus c real_zero) c c
             (real_eq_refl c) (real_plus_zero c))
          (real_eq_trans
             (real_plus c c)
             (real_mult tspw_kvev_N_R c)
             real_one
             (real_eq_trans
                (real_plus c c)
                (real_plus (real_mult c real_one) (real_mult c real_one))
                (real_mult tspw_kvev_N_R c)
                (RealSetoid.real_eq_plus_compat c c
                   (real_mult c real_one) (real_mult c real_one)
                   (real_eq_sym (real_mult c real_one) c (real_mult_one c))
                   (real_eq_sym (real_mult c real_one) c (real_mult_one c)))
                (real_eq_trans
                   (real_plus (real_mult c real_one) (real_mult c real_one))
                   (real_mult c (real_plus real_one real_one))
                   (real_mult tspw_kvev_N_R c)
                   (real_eq_sym
                      (real_mult c (real_plus real_one real_one))
                      (real_plus (real_mult c real_one) (real_mult c real_one))
                      (real_distrib c real_one real_one))
                   (real_mult_comm c tspw_kvev_N_R)))
             Hc)).
Defined.

(* ---- Row normalization -------------------------------------- *)
(* The kernel is pointwise constant, so the two-point fold is    *)
(* c + (c + 0) with c := inv N_R; the chain lemma closes it.     *)
Theorem tspw_kvev_Krow : forall s : tspw_kvev_tok,
  real_eq (real_list_sum tspw_kvev_tok
             (fun s' : tspw_kvev_tok => tspw_kvev_K s s') tspw_kvev_states)
          real_one.
Proof.
  intro s.
  exact (tspw_kvev_two_inv_sum (tspw_kvev_K s true) tspw_kvev_N_R_inv_correct).
Defined.

(* ---- Retention witness load --------------------------------- *)
(* keep is constantly true, so the state true itself witnesses    *)
(* the nonempty load: Id true true by id_refl, and true is the    *)
(* head of the enumeration by InT_here.                           *)
Theorem tspw_kvev_keep_nonempty :
  sigT (fun s : tspw_kvev_tok =>
    S01_BaseRing.And (S01_BaseRing.Id (tspw_kvev_keep s) true)
                     (InT s tspw_kvev_states)).
Proof.
  exists true.
  split.
  - exact S01_BaseRing.id_refl.
  - exact (S01_BaseRing.InT_here true (false :: nil)).
Defined.

(* ---- Step positivity and upper bound ------------------------- *)
(* delta := one, so 0 < one and one <= one close both faces.      *)
Theorem tspw_kvev_delta_pos : real_lt real_zero tspw_kvev_delta.
Proof. exact real_lt_zero_one. Defined.

Theorem tspw_kvev_delta_le_one : real_le tspw_kvev_delta real_one.
Proof. exact (real_le_refl real_one). Defined.

(* ============================================================ *)
(* Section 2. Interface-face certificates, alignment shape.       *)
(*   Each certificate instantiates its argument at one and is     *)
(*   discharged by the carrier's own positivity field one_pos.    *)
(*   The intermediate Definition carries the explicit type        *)
(*   annotation for the record-field consumption.                 *)
(* ============================================================ *)
Section TspwUp01AlignFace.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Definition tspw_ri_one_pos : lt zero one := @S01_BaseRing.one_pos RI.

Theorem tspw_up01_align_beta_pos : lt zero one.
Proof. exact tspw_ri_one_pos. Defined.

(* Reference-policy face: the domain type S comes from the state  *)
(* space of the same carrier.                                     *)
Section TspwUp01AlignPiRef.
Context {SS : StateSpace RI}.
Theorem tspw_up01_align_pi_ref_pos : forall s : S, lt zero one.
Proof. intro s. exact tspw_ri_one_pos. Defined.
End TspwUp01AlignPiRef.

Theorem tspw_up01_align_eta_pos : lt zero one.
Proof. exact tspw_ri_one_pos. Defined.

End TspwUp01AlignFace.

(* ============================================================ *)
(* Section 3. Interface-face certificates, entropy shape: the     *)
(*   copy step eta and the Lipschitz constant L, both one.        *)
(* ============================================================ *)
Section TspwUp01EntropyFace.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Definition tspw_ri_one_pos_e : lt zero one := @S01_BaseRing.one_pos RI.

Theorem tspw_up01_entropy_eta_pos : lt zero one.
Proof. exact tspw_ri_one_pos_e. Defined.

Theorem tspw_up01_entropy_L_pos : lt zero one.
Proof. exact tspw_ri_one_pos_e. Defined.

End TspwUp01EntropyFace.

(* ============================================================ *)
(* Section 4. Interface-face certificates, temperature shape:     *)
(*   the softmax temperatures temp and Delta, both one.           *)
(* ============================================================ *)
Section TspwP7DFace.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Definition tspw_ri_one_pos_p7d : lt zero one := @S01_BaseRing.one_pos RI.

Theorem tspw_p7d3_temp_pos : lt zero one.
Proof. exact tspw_ri_one_pos_p7d. Defined.

Theorem tspw_p7d3_Delta_pos : lt zero one.
Proof. exact tspw_ri_one_pos_p7d. Defined.

Theorem tspw_p7d7_temp_pos : lt zero one.
Proof. exact tspw_ri_one_pos_p7d. Defined.

End TspwP7DFace.

(* ============================================================ *)
(* Section 5. Assumption audit: one line per theorem; every      *)
(*   verdict must read Closed under the global context.          *)
(* ============================================================ *)
Print Assumptions tspw_kvev_Krow.
Print Assumptions tspw_kvev_keep_nonempty.
Print Assumptions tspw_kvev_delta_pos.
Print Assumptions tspw_kvev_delta_le_one.
Print Assumptions tspw_kvev_two_inv_sum.
Print Assumptions tspw_up01_align_beta_pos.
Print Assumptions tspw_up01_align_pi_ref_pos.
Print Assumptions tspw_up01_align_eta_pos.
Print Assumptions tspw_up01_entropy_eta_pos.
Print Assumptions tspw_up01_entropy_L_pos.
Print Assumptions tspw_p7d3_temp_pos.
Print Assumptions tspw_p7d3_Delta_pos.
Print Assumptions tspw_p7d7_temp_pos.

(* ============================================================ *)
(* Section 6. Extraction spot-check of the conclusion faces      *)
(*   (stdout; judgement: the printed OCaml holds no Obj.magic,   *)
(*   i.e. every face is a genuine Set-carried program).          *)
(* ============================================================ *)
Recursive Extraction tspw_kvev_Krow tspw_kvev_keep_nonempty.
Recursive Extraction tspw_kvev_delta_pos tspw_kvev_delta_le_one.
Recursive Extraction tspw_up01_align_beta_pos tspw_up01_align_pi_ref_pos.
Recursive Extraction tspw_p7d3_temp_pos.
