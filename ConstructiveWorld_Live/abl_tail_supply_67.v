(* ConstructiveWorld-Set -- Real-face closed-form supply bundle for the F4 exponential-family slots. *)
(** * abl_tail_supply_67: Real-face verbatim supply for the F4 expf slots.

    Mission.  Seventeen F4 expf slots: P7BoundedSoftmaxDeep P7DNoSwap
      :169-174 (six) + P7DKernelBand :381-383 (three);
      UpAblP7_WallEpsChain_B P7aKappaPackage :890-894 (five) +
      P7aSbInst :994-996 (three).  Five [Id]-pinned slots ([expf_zero]
      P7B:171/WallEps:892/:995; [expf_plus] P7B:172/WallEps:893) carry
      the non-canonical-representation obligation (no input here); the
      eight real slots and zero/addition [real_eq] readings are
      transcribed from [real_expf_realizable] (AttnDoeblin) via
      [UpAblD1_expf_pack]: one instance, five projections, four
      bundles -- nine [Qed] theorems.

    Dependencies.  [S01_BaseRing], [S02_CauchyComplete], [UpAblD1_expf_pack];
      Stdlib [Extraction]; all references read-only (consumers untouched).

    References.  [UpAblD1_expf_pack] ([uabd1x_expf] :28; unpacked theorems
      :48/:52/:56/:61/:67; [uabd1x_pack_fields] :31); AttnDoeblin
      [real_expf_realizable] :771; [uabl_attn_full_instance] Part A;
      same-name ConstructiveWorld-Main baseline (statements verbatim).

    Constructivity.  All nine conclusions close by genuine [Qed]
      constructions: no admissions, no classical logic; carriers all
      Set-valued ([real_eq]/[real_lt]/[real_le]/[And]), no Prop leakage;
      [Print Assumptions] [Closed] on all nine; probes take [Obj.magic] = 0.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      abl_tail_supply_67.v] compiles cleanly (exit 0); the first eight
      bytes of the artifact are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpAblD1_expf_pack.
From Stdlib Require Import Extraction.

(* ================= Section 1. Exponential instance and five projection transcriptions (verbatim Real-face, no reproofs) ================= *)

(* The function instance is a signature projection of the composite: a
   definitional transcription of [uabd1x_expf@UpAblD1_expf_pack:28],
   underlying [cauchy_real_exp@AttnDoeblin] projected by [projT1] out of
   the [sigT] composite [real_expf_realizable:771].  All five proof
   paths are direct [exact] citations of the unpacked theorems
   (:48/:52/:56/:61/:67).  The zero and addition transcriptions take
   the [real_eq] reading because their [Id]-face slot shapes
   (P7B:171/:172, WallEps:892/:893/:995) carry the non-canonical
   representation obligation and receive no input here; the
   [real_eq]-reading transcription is the established re-face supply
   route in this development (the in-use precedent
   [uabl_attn_full_instance] Part A). *)

Definition tsp_expf_spec_fn : Real -> Real := uabd1x_expf.

(* ---- Transcription one: pointwise strict positivity (the [pos] slot,  ---- *)
(* ----      Real-specialized closed form; the [lt]-face slot readings   ---- *)
(* ----      at P7B:170/:382 and WallEps:891).                           ---- *)
Theorem tsp_expf_spec_pos : forall x : Real, real_lt real_zero (tsp_expf_spec_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ---- Transcription two: unit equality at zero (the [zero] slot, [real_eq] reading). ---- *)
Theorem tsp_expf_spec_zero_req : real_eq (tsp_expf_spec_fn real_zero) real_one.
Proof. exact uabd1x_expf_zero. Qed.

(* ---- Transcription three: multiplicativity over addition (the [plus] slot, [real_eq] reading). ---- *)
Theorem tsp_expf_spec_plus_req : forall a b : Real,
  real_eq (tsp_expf_spec_fn (real_plus a b))
          (real_mult (tsp_expf_spec_fn a) (tsp_expf_spec_fn b)).
Proof. exact uabd1x_expf_plus. Qed.

(* ---- Transcription four: strict monotonicity (the [mono_lt] slot,     ---- *)
(* ----      Real-specialized closed form; the [lt]-face slot readings   ---- *)
(* ----      at P7B:173 and WallEps:894/:996).                           ---- *)
Theorem tsp_expf_spec_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tsp_expf_spec_fn a) (tsp_expf_spec_fn b).
Proof. exact uabd1x_expf_mono_lt. Qed.

(* ---- Transcription five: order preservation (the [mono_le] slot,      ---- *)
(* ----      Real-specialized closed form; the [le]-face slot readings   ---- *)
(* ----      at P7B:174/:383; the two [Or] disjuncts are discharged      ---- *)
(* ----      branch by branch inside the composite).                     ---- *)
Theorem tsp_expf_spec_mono_le : forall a b : Real,
  real_le a b -> real_le (tsp_expf_spec_fn a) (tsp_expf_spec_fn b).
Proof. exact uabd1x_expf_mono_le. Qed.

(* ================= Section 2. Four per-section bundles (Set-layer [And] bundles, members in each section's slot order) ================= *)

(* Each bundle is the certificate covering every exponential property
   slot of the corresponding consuming section, in the Real/[req]
   readings.  Member notes: the [pos]/[mono_lt]/[mono_le] members feed
   the Real-specialized forms of the [lt]/[le]-face slots; the
   [zero_req]/[plus_req] members are re-face transcriptions of the
   [Id]-face slots under the [real_eq] reading (the established re-face
   supply route, not a statement-face resolution of the [Id] slots
   themselves). *)

(* ---- Bundle one: P7BoundedSoftmaxDeep, third block (section           ---- *)
(* ----      P7DNoSwap, :169-174).  All five property slots covered:     ---- *)
(* ----      pos:170, zero:171 ([req] reading), plus:172 ([req]          ---- *)
(* ----      reading), mono_lt:173, mono_le:174; the expf carrier at     ---- *)
(* ----      :169 is an argument slot and is not part of the bundle.     ---- *)
Theorem tsp_p7d_noswap_expf_certs :
  And (forall x : Real, real_lt real_zero (tsp_expf_spec_fn x))
      (And (real_eq (tsp_expf_spec_fn real_zero) real_one)
      (And (forall a b : Real,
            real_eq (tsp_expf_spec_fn (real_plus a b))
                    (real_mult (tsp_expf_spec_fn a) (tsp_expf_spec_fn b)))
      (And (forall a b : Real,
            real_lt a b -> real_lt (tsp_expf_spec_fn a) (tsp_expf_spec_fn b))
           (forall a b : Real,
            real_le a b -> real_le (tsp_expf_spec_fn a) (tsp_expf_spec_fn b))))).
Proof.
  exact (pair tsp_expf_spec_pos
           (pair tsp_expf_spec_zero_req
           (pair tsp_expf_spec_plus_req
           (pair tsp_expf_spec_mono_lt tsp_expf_spec_mono_le)))).
Qed.

(* ---- Bundle two: P7BoundedSoftmaxDeep, seventh block (section         ---- *)
(* ----      P7DKernelBand, :381-383).  Two property slots: pos:382 and  ---- *)
(* ----      mono_le:383; the expf carrier at :381 is an argument slot.  ---- *)
Theorem tsp_p7d_kernelband_expf_certs :
  And (forall x : Real, real_lt real_zero (tsp_expf_spec_fn x))
      (forall a b : Real,
       real_le a b -> real_le (tsp_expf_spec_fn a) (tsp_expf_spec_fn b)).
Proof.
  exact (pair tsp_expf_spec_pos tsp_expf_spec_mono_le).
Qed.

(* ---- Bundle three: UpAblP7_WallEpsChain_B, second section             ---- *)
(* ----      (P7aKappaPackage, :890-894).  All four property slots       ---- *)
(* ----      covered: pos:891, zero:892 ([req] reading), plus:893        ---- *)
(* ----      ([req] reading), mono_lt:894; the expf carrier at :890 is   ---- *)
(* ----      an argument slot.                                           ---- *)
Theorem tsp_walleps_kappa_expf_certs :
  And (forall x : Real, real_lt real_zero (tsp_expf_spec_fn x))
      (And (real_eq (tsp_expf_spec_fn real_zero) real_one)
      (And (forall a b : Real,
            real_eq (tsp_expf_spec_fn (real_plus a b))
                    (real_mult (tsp_expf_spec_fn a) (tsp_expf_spec_fn b)))
           (forall a b : Real,
            real_lt a b -> real_lt (tsp_expf_spec_fn a) (tsp_expf_spec_fn b)))).
Proof.
  exact (pair tsp_expf_spec_pos
           (pair tsp_expf_spec_zero_req
           (pair tsp_expf_spec_plus_req tsp_expf_spec_mono_lt))).
Qed.

(* ---- Bundle four: UpAblP7_WallEpsChain_B, third section               ---- *)
(* ----      (P7aSbInst, :994-996).  Two property slots: zero:995        ---- *)
(* ----      ([req] reading) and mono_lt:996; the expf carrier at :994   ---- *)
(* ----      is an argument slot.                                        ---- *)
Theorem tsp_walleps_sb_expf_certs :
  And (real_eq (tsp_expf_spec_fn real_zero) real_one)
      (forall a b : Real,
       real_lt a b -> real_lt (tsp_expf_spec_fn a) (tsp_expf_spec_fn b)).
Proof.
  exact (pair tsp_expf_spec_zero_req tsp_expf_spec_mono_lt).
Qed.

(* ================= Section 3. Audit: premise audit of all nine theorems (name count = [Qed] count = [Print Assumptions] count, no discrepancy) ================= *)
Print Assumptions tsp_expf_spec_pos.
Print Assumptions tsp_expf_spec_zero_req.
Print Assumptions tsp_expf_spec_plus_req.
Print Assumptions tsp_expf_spec_mono_lt.
Print Assumptions tsp_expf_spec_mono_le.
Print Assumptions tsp_p7d_noswap_expf_certs.
Print Assumptions tsp_p7d_kernelband_expf_certs.
Print Assumptions tsp_walleps_kappa_expf_certs.
Print Assumptions tsp_walleps_sb_expf_certs.

(* ================= Section 4. Extraction checks: criterion carrier, the nine theorems, and the comparison command ================= *)

(* Command A extracts the criterion carrier [tsp_expf_spec_fn] alone (a
   purely computational carrier; the criterion is [Obj.magic] = 0, with
   the same-source extraction precedent AttnDoeblin:792).  Command B
   extracts all nine theorems.  Command C is the comparison (the five
   unpacked originals plus the carrier function itself); comparing the
   B and C counts gives the zero-new-increment account for this file. *)
Recursive Extraction tsp_expf_spec_fn.
Recursive Extraction tsp_expf_spec_pos tsp_expf_spec_zero_req
  tsp_expf_spec_plus_req tsp_expf_spec_mono_lt tsp_expf_spec_mono_le
  tsp_p7d_noswap_expf_certs tsp_p7d_kernelband_expf_certs
  tsp_walleps_kappa_expf_certs tsp_walleps_sb_expf_certs.
Recursive Extraction uabd1x_expf uabd1x_expf_pos uabd1x_expf_zero
  uabd1x_expf_plus uabd1x_expf_mono_lt uabd1x_expf_mono_le.

(* Verification outcomes: compilation exits 0 with zero error lines in
   the log; all nine [Print Assumptions] report [Closed] (count 9,
   matching the [Qed] count); the full log contains zero [Obj.magic] --
   the criterion-carrier extraction, the nine-theorem extraction, and
   the comparison extraction (the five unpacked originals plus the
   carrier function) all report zero [Obj.magic], so the strong
   extraction criterion is met (same-source precedent
   AttnDoeblin:791-792); [coqchk] exits 0 with an environment summary
   reporting [Axioms: none].
   The extractor accesses proved theorem bodies inside the dependency
   closure under the bypass-opaque setting (the standard warning
   extraction-opaque-accessed); this is a warning face only, not an
   admission face. *)
