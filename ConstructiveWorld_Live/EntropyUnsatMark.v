(* ========================================================================== *)
(*  EntropyUnsatMark.v - unsatisfiability certificates for the entropy       *)
(*  section of the constructive real library                                 *)
(* ========================================================================== *)
(*   Mission. fa52_EDP_E_B_pos_unsat refutes any witness that every positive *)
(*   difference E_total - E is again positive, by instantiating it at        *)
(*   E = 1 and at E = E_total (the latter forces 0 < E_total - E_total == 0); *)
(*   fa52_EntropyDiffReal_premises_unsat lifts the refutation to the full    *)
(*   ten-slot EntropyDiffReal premise set; eum_E_B_pos_slot_unsat_ref and    *)
(*   eum_premises_unsat_ref forward the two certificates unchanged;          *)
(*   eum_EntropyDiffReal_section_vacuous converts the vacuous truth of the   *)
(*   whole premise set into an arbitrary conclusion P via False_ind.         *)
(*   Dependencies. S02_CauchyComplete, S07_RealSetoidExpLog,                 *)
(*   S08_RealMainlineDPO, S09_EntropyReal: the constructive Cauchy reals     *)
(*   (Real, real_plus/real_opp, real_zero/real_one, the Set-valued order     *)
(*   and equality witnesses real_lt/real_le/real_eq, RealDifferentiable).    *)
(*   No further Require.                                                     *)
(*   References. Baseline module EntropyUnsatMark.v of ConstructiveWorld_Live *)
(*   (statement names carried over verbatim; census 5=5 ordered identity).   *)
(*   Constructivity. Premises are Set-layer objects (Real and                *)
(*   RealDifferentiable are Set-sorted; real_lt/real_eq are Set-valued       *)
(*   witnesses); the conclusions are False or an arbitrary P : Prop. Every   *)
(*   proof is a Qed-closed forwarding or a two-point instantiation; the      *)
(*   module is axiom-free and uses no classical logic. Empty_set (the        *)
(*   conclusion carrier of S01_BaseRing.Not) has no constructor, so the      *)
(*   contradiction exits by destruct; the arbitrary-conclusion exit          *)
(*   eliminates through False_ind; extraction yields no Obj.magic.           *)
(*   Build. rocq c -native-compiler no -q -Q . "" EntropyUnsatMark.v         *)
(*   (Rocq 9.1 toolchain; single -Q root with an empty logical prefix).      *)

Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.

(* ================= Section 1: the fa52_EDP_E_B_pos_unsat family ================= *)
(* ---------- Core: single-slot unsatisfiability of the E_B_pos witness ---------- *)
Theorem fa52_EDP_E_B_pos_unsat :
  forall E_total : Real,
    (forall E : Real, real_lt real_zero E ->
       real_lt real_zero (real_plus E_total (real_opp E))) -> False.
Proof.
  intros E_total eB.
  (* Step 1: instantiate eB at E := real_one : 0 < E_total - 1 *)
  pose proof (eB real_one real_lt_zero_one) as H1.
  (* Step 2: mixed addition preserves strict order: 0+1 < (E_total-1)+1 *)
  assert (Hstep : real_lt (real_plus real_zero real_one)
                          (real_plus (real_plus E_total (real_opp real_one)) real_one)).
  { exact (real_lt_plus_compat_lt_le real_zero
             (real_plus E_total (real_opp real_one)) real_one real_one H1
             (real_le_refl real_one)). }
  (* 0 + 1 == 1 *)
  assert (HL : real_eq (real_plus real_zero real_one) real_one).
  { apply (real_eq_trans _ (real_plus real_one real_zero)).
    - apply (real_plus_comm real_zero real_one).
    - apply (real_plus_zero real_one). }
  (* (E_total-1)+1 == E_total *)
  assert (HR : real_eq (real_plus (real_plus E_total (real_opp real_one)) real_one)
                       E_total).
  { apply (real_eq_trans _ (real_plus E_total (real_plus (real_opp real_one) real_one))).
    - apply real_eq_sym.
      apply (real_plus_assoc E_total (real_opp real_one) real_one).
    - apply (real_eq_trans _ (real_plus E_total real_zero)).
      + apply (RealSetoid.real_eq_plus_compat E_total
                 (real_plus (real_opp real_one) real_one) E_total real_zero).
        * apply (real_eq_refl E_total).
        * apply (real_eq_trans _ (real_plus real_one (real_opp real_one))).
          -- apply (real_plus_comm (real_opp real_one) real_one).
          -- apply (real_plus_opp real_one).
      + apply (real_plus_zero E_total). }
  (* Hence 1 < E_total; step down to 0 < E_total *)
  assert (H1ET : real_lt real_one E_total).
  { exact (real_eq_lt_lt _ _ _ (real_eq_sym _ _ HL) (real_lt_eq_lt _ _ _ Hstep HR)). }
  assert (H2 : real_lt real_zero E_total).
  { exact (real_lt_le_trans real_zero real_one E_total real_lt_zero_one (inl H1ET)). }
  (* Step 3: instantiate eB at E_total : 0 < E_total - E_total == 0, contradiction *)
  pose proof (real_lt_eq_lt real_zero (real_plus E_total (real_opp E_total)) real_zero
                (eB E_total H2) (real_plus_opp E_total)) as Hcon.
  (* Empty_set (the conclusion carrier of S01_BaseRing.Not) has no constructor; destruct on it clears any goal *)
  destruct (real_lt_irrefl real_zero Hcon).
Qed.

(* ---------- Packaging: vacuous truth of the full ten-slot EntropyDiffReal premise set ---------- *)
Theorem fa52_EntropyDiffReal_premises_unsat :
  forall (Omega_A : forall E_A : Real, real_lt real_zero E_A -> Real)
         (Omega_B : forall E_B : Real, real_lt real_zero E_B -> Real)
         (dA : RealDifferentiable Omega_A)
         (dB : RealDifferentiable Omega_B)
         (pA : forall (E_A : Real) (H : real_lt real_zero E_A),
                real_lt real_zero (Omega_A E_A H))
         (pB : forall (E_B : Real) (H : real_lt real_zero E_B),
                real_lt real_zero (Omega_B E_B H))
         (wdB : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
                real_eq a b -> real_eq (Omega_B a Ha) (Omega_B b Hb))
         (E_total k_B : Real)
         (eB : forall (E_A : Real) (H : real_lt real_zero E_A),
                real_lt real_zero (real_plus E_total (real_opp E_A))),
    False.
Proof.
  intros Omega_A Omega_B dA dB pA pB wdB E_total k_B eB.
  exact (fa52_EDP_E_B_pos_unsat E_total eB).
Qed.

Print Assumptions fa52_EDP_E_B_pos_unsat.
Print Assumptions fa52_EntropyDiffReal_premises_unsat.
(* ================= Section 2: the eum_E_B_pos_slot_unsat_ref family ================= *)
(* ---------- Exit 1: slot-10 single-slot diagnostic forwarding (zero new proof) ---------- *)
Theorem eum_E_B_pos_slot_unsat_ref :
  forall E_total : Real,
    (forall E : Real, real_lt real_zero E ->
       real_lt real_zero (real_plus E_total (real_opp E))) -> False.
Proof.
  exact fa52_EDP_E_B_pos_unsat.
Qed.

(* ---------- Exit 2: forwarding of the vacuous truth of the full ten-slot premise set (zero new proof; the main theorem of this module) ---------- *)
Theorem eum_premises_unsat_ref :
  forall (Omega_A : forall (E_A : Real), real_lt real_zero E_A -> Real)
         (Omega_B : forall (E_B : Real), real_lt real_zero E_B -> Real)
         (dOmega_A : RealDifferentiable Omega_A)
         (dOmega_B : RealDifferentiable Omega_B)
         (Omega_A_pos : forall (E_A : Real) (H : real_lt real_zero E_A),
                real_lt real_zero (Omega_A E_A H))
         (Omega_B_pos : forall (E_B : Real) (H : real_lt real_zero E_B),
                real_lt real_zero (Omega_B E_B H))
         (Omega_B_wd : forall (a b : Real) (Ha : real_lt real_zero a)
                                         (Hb : real_lt real_zero b),
                real_eq a b -> real_eq (Omega_B a Ha) (Omega_B b Hb))
         (E_total k_B : Real)
         (E_B_pos : forall (E_A : Real) (H : real_lt real_zero E_A),
                real_lt real_zero (real_plus E_total (real_opp E_A))),
    False.
Proof.
  exact fa52_EntropyDiffReal_premises_unsat.
Qed.

(* ---------- Exit 3: whole-section vacuous-truth conclusion piece (arbitrary Prop conclusion, constructive False_ind) ---------- *)
Theorem eum_EntropyDiffReal_section_vacuous :
  forall (Omega_A : forall (E_A : Real), real_lt real_zero E_A -> Real)
         (Omega_B : forall (E_B : Real), real_lt real_zero E_B -> Real)
         (dOmega_A : RealDifferentiable Omega_A)
         (dOmega_B : RealDifferentiable Omega_B)
         (Omega_A_pos : forall (E_A : Real) (H : real_lt real_zero E_A),
                real_lt real_zero (Omega_A E_A H))
         (Omega_B_pos : forall (E_B : Real) (H : real_lt real_zero E_B),
                real_lt real_zero (Omega_B E_B H))
         (Omega_B_wd : forall (a b : Real) (Ha : real_lt real_zero a)
                                         (Hb : real_lt real_zero b),
                real_eq a b -> real_eq (Omega_B a Ha) (Omega_B b Hb))
         (E_total k_B : Real)
         (E_B_pos : forall (E_A : Real) (H : real_lt real_zero E_A),
                real_lt real_zero (real_plus E_total (real_opp E_A)))
         (P : Prop),
    P.
Proof.
  intros Omega_A Omega_B dOmega_A dOmega_B Omega_A_pos Omega_B_pos
         Omega_B_wd E_total k_B E_B_pos P.
  exact (False_ind P
    (eum_premises_unsat_ref Omega_A Omega_B dOmega_A dOmega_B
       Omega_A_pos Omega_B_pos Omega_B_wd E_total k_B E_B_pos)).
Qed.

(* ========== 4. Registration of the whole-section vacuous-truth conclusion + usage-impact assessment ========== *)
(* Five section products of S09_EntropyReal (kinds and slot usage as recorded):
   real_E_B_ent                definition (consumes slot 8 E_total / slot 10 E_B_pos as premises)
   real_Omega_total_ent        definition (consumes slots 1/2/10)
   real_Omega_total_pos        lemma (consumes slots 5/6/10)
   real_entropy_ent            definition (consumes slot 9 k_B; via real_log and real_Omega_total_pos)
   real_entropy_differentiable lemma (consumes slots 3/4/7/8/10)
   All five are vacuously true: every argument position is supplied by the
   vacuously-true premise set (without a slot-10 witness the family has no
   closed instance). *)
(* Out-of-section usage (full-library grep of the baseline tree): the
   real_entropy_ent / real_entropy_differentiable / real_Omega_total_ent
   family has zero definition-level consumers; its only mentions are comment
   citations in UpReqAlignRestB.v (no declaration-level use). Hence the
   realization of this section carries no downstream coupling and no
   re-derivation surface; realization is the terminal state. *)
(* Constructivity self-audit: pure constructive forwarding (zero new proofs;
   the main piece's two-point instantiation is a non-trivial, fully traceable
   construction). Statement faces are Set-layer objects (Real /
   RealDifferentiable : Set); the exit pieces with False/Prop-sorted
   conclusions eliminate constructively through False_ind, with no Set-layer
   leakage. The extraction-level Obj.magic inspection is carried out outside
   this module. *)

Print Assumptions eum_E_B_pos_slot_unsat_ref.
Print Assumptions eum_premises_unsat_ref.
Print Assumptions eum_EntropyDiffReal_section_vacuous.
