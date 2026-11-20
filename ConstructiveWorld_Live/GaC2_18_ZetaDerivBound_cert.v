(** * GaC2_18_ZetaDerivBound_cert: certificate face of node C2-18.

    Mission.  Certificate face of node C2-18: the literal corridor
      of the derivative-bound constant and the decidable sample
      bands (the band inventory in the Notes block below).  Honest
      scope: these bands certify the rational corridor forms and the
      decidable skeleton only; the Real-line bound faces live on the
      statement face with the premise family, and the binding of C2
      to the certified vertical-bound constant lands at mother-chain
      integration (the C2-16/17 faces own the certified C2 value).

    Dependencies.  Stdlib [QArith.QArith] only (the face is
      base-standalone: the proof-to-cert direction stays one-way, no
      statement-face require).

    References.  drafts_C2.md C2.18 certificate line (the constant
      and radius sample bands); gamma_module_spec.md section 4.2 the
      certificate-face shape.

    Constructivity.  Set-sorted rational identities and boolean
      skeletons; every statement face is carried by the Set-sorted
      identity family defined below, so the certificate terms stay
      information-bearing and extractable; zero assumed constants,
      zero abandoned proofs; the bands close by explicit computation
      under the global context, all proof terms transparent.

    Build.  [coqc -Q . "" GaC2_18_ZetaDerivBound_cert.v]; the face
      is base-standalone (Stdlib only). *)

From Stdlib Require Import QArith.QArith.
(** Notes.  Band inventory.

    (1) The constant corridor [GaC2_18_c3_form]: the explicit
    C3 = 4 * C2 / c binding form over the rational inputs (C2 the
    vertical-bound constant, c the consumer-domain constant),
    division-free (multiplication by the rational unit 1/c), sampled
    at C2 = 2, c = 1 closing at 8.
    (2) The radius lower-bound corridor [GaC2_18_r_lb]: the half
    vertical-gap form (sigma - 1) / 2 on the unit-vertical zero-set
    line, sampled at sigma = 3/2 closing at 1/4 and sigma = 5/4
    closing at 1/8.
    (3) The decidable skeleton of the two-sided imaginary bound
    [GaC2_18_t_le_cap] at the cap samples 10 and 100 with the point
    t = 5 and t = 0. *)

Local Open Scope Q_scope.

(* ---- Set-sorted statement carrier ---- *)

(* The certificate statements are carried by this Set-sorted identity    *)
(* family instead of the Prop-sorted equality, so each statement face    *)
(* stays information-bearing and extractable.                            *)
Inductive GaC2_18_id (A : Type) (x : A) : A -> Set :=
  GaC2_18_id_refl : GaC2_18_id A x x.

(* ---- Band 1: the constant corridor form ---- *)

(* The C3 binding corridor: C3 = 4 * C2 / c, the division-free form     *)
(* (multiplication by the rational unit 1/c).                            *)
Definition GaC2_18_c3_form (c2 c : Q) : Q := 4 * c2 * Qinv c.

Lemma GaC2_18_cert_c3_sample : GaC2_18_id bool (Qeq_bool (GaC2_18_c3_form 2 1) 8) true.
Proof. vm_compute; exact (GaC2_18_id_refl bool true). Defined.

(* ---- Band 2: the radius lower-bound corridor ---- *)

(* The radius lower-bound corridor on the unit-vertical zero-set line:  *)
(* r >= (sigma - 1) / 2, the division-free half form.                    *)
Definition GaC2_18_r_lb (sigma : Q) : Q := (sigma - 1) * (1 # 2).

Lemma GaC2_18_cert_r_lb_sample1 : GaC2_18_id bool (Qeq_bool (GaC2_18_r_lb (3 # 2)) (1 # 4)) true.
Proof. vm_compute; exact (GaC2_18_id_refl bool true). Defined.

Lemma GaC2_18_cert_r_lb_sample2 : GaC2_18_id bool (Qeq_bool (GaC2_18_r_lb (5 # 4)) (1 # 8)) true.
Proof. vm_compute; exact (GaC2_18_id_refl bool true). Defined.

(* ---- Band 3: the decidable two-sided imaginary skeleton ---- *)

(* The two-sided imaginary bound skeleton: -cap <= t <= cap as the       *)
(* boolean pair.                                                         *)
Definition GaC2_18_t_le_cap (t cap : Q) : bool :=
  andb (Qle_bool (Qopp cap) t) (Qle_bool t cap).

Lemma GaC2_18_cert_t_le_cap_sample1 : GaC2_18_id bool (GaC2_18_t_le_cap 5 10) true.
Proof. vm_compute; exact (GaC2_18_id_refl bool true). Defined.

Lemma GaC2_18_cert_t_le_cap_sample2 : GaC2_18_id bool (GaC2_18_t_le_cap 0 100) true.
Proof. vm_compute; exact (GaC2_18_id_refl bool true). Defined.
