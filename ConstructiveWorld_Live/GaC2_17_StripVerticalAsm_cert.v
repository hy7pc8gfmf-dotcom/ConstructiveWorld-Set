(** * GaC2_17_StripVerticalAsm_cert: certificate face of node C2-17.

    Mission.  The delta sample points of the draft certificate line
      (delta in {1/10, 1/4}) and the decidable skeletons the strip face
      feeds on (band inventory in the Notes block).  Each claim is the
      boolean verdict of a decidable skeleton at one sample point: the
      corridor form closes at 32 and 16 at the two lower-bound literals,
      both literals are positive, and the band skeleton admits
      sigma = 1/2 at delta = 1/4 while rejecting sigma = 7/8.  Honest
      scope: these bands certify the rational corridor forms and the
      decidable skeletons only; the Real-line corridor inequality and
      the uniform bound live on the statement face of the wider
      development.

    Dependencies.  Stdlib [QArith.QArith] only (base-standalone: the
      proof-to-cert direction stays one-way, no statement-face require).

    References.  drafts_C2.md C2.17 certificate line (the delta sample
      points and the literal lower bounds); cards_C2.md C2.17 the
      computable face row; gamma_module_spec.md section 4.2 the
      certificate-face shape.

    Constructivity.  Every statement face is Set-carried (no
      statement-level Prop): truth claims ride the boolean identity
      [GaC2_17_id], and each certificate closes by one [vm_compute] step
      at the identity constructor, so every statement extracts as Set
      data with no erasure.

    Build.  coqc -native-compiler no -q -Q <world-root> ""
      GaC2_17_StripVerticalAsm_cert.v; the face is base-standalone. *)

From Stdlib Require Import QArith.QArith.

(** Notes.  Band inventory.

    (1) The lower-bound literals [GaC2_17_lb_delta1] = 1/16 and
    [GaC2_17_lb_delta2] = 1/8 claimed for the corridor 2^delta - 1
    at the two sample deltas (both claims true on the real line:
    2^{1/10} - 1 > 1/16 and 2^{1/4} - 1 > 1/8; their Real-line
    verification faces belong to the wider development).
    (2) The uniform-bound corridor form [GaC2_17_ub_corridor] =
    2 * inverse lb (the division-free form of the card bound
    2 / (2^delta - 1)), sampled at the two literals and closing at
    32 and 16.
    (3) The literal positivity skeletons of the two bounds.
    (4) The decidable band skeleton [GaC2_17_sigma_band] =
    0 <= sigma <= 1 - delta of the (a) band membership, sampled
    one-in one-out (sigma = 1/2 in at delta = 1/4; sigma = 7/8
    out). *)

Local Open Scope Q_scope.

(* The Set-level identity of this certificate face.  [GaC2_17_id x y]  *)
(* is witnessed by the single constructor [GaC2_17_idr] exactly when   *)
(* x and y are the same element of the Set [A]; a term of              *)
(* [GaC2_17_id b v] is the identity evidence that the boolean verdict  *)
(* [b] agrees with the expected boolean [v].  Every band claim below   *)
(* is stated in this form, so all statement faces live in [Set]: no    *)
(* statement of this module is a Prop.                                 *)
Inductive GaC2_17_id {A : Set} (x : A) : A -> Set :=
| GaC2_17_idr : GaC2_17_id x x.

Arguments GaC2_17_idr {A} {x}.

(* ---- Band 1: the lower-bound literals ---- *)

(* The claimed lower-bound literals for 2^delta - 1 at the sample      *)
(* deltas (delta = 1/10 and delta = 1/4).                              *)
Definition GaC2_17_lb_delta1 : Q := (1#16).
Definition GaC2_17_lb_delta2 : Q := (1#8).

(* ---- Band 2: the uniform-bound corridor form ---- *)

(* The card bound 2 / (2^delta - 1) in the division-free form          *)
(* 2 * inverse lb over the lower-bound literal.                        *)
Definition GaC2_17_ub_corridor (lb : Q) : Q := 2 * Qinv lb.

(* The corridor form at the first literal closes at 32. *)
Lemma GaC2_17_cert_ub_sample1 :
  GaC2_17_id (Qeq_bool (GaC2_17_ub_corridor GaC2_17_lb_delta1) 32) true.
Proof. vm_compute. exact GaC2_17_idr. Defined.

(* The corridor form at the second literal closes at 16. *)
Lemma GaC2_17_cert_ub_sample2 :
  GaC2_17_id (Qeq_bool (GaC2_17_ub_corridor GaC2_17_lb_delta2) 16) true.
Proof. vm_compute. exact GaC2_17_idr. Defined.

(* ---- Band 3: the literal positivity skeletons ---- *)

(* Strict positivity as the decidable pair: non-negative and nonzero   *)
(* (the stdlib QArith of this tree carries no boolean strict-order     *)
(* face; the pair form is the honest decidable substitute).            *)
Definition GaC2_17_lb_pos (lb : Q) : bool :=
  andb (Qle_bool 0 lb) (negb (Qeq_bool lb 0)).

Lemma GaC2_17_cert_lb_pos1 : GaC2_17_id (GaC2_17_lb_pos GaC2_17_lb_delta1) true.
Proof. vm_compute. exact GaC2_17_idr. Defined.

Lemma GaC2_17_cert_lb_pos2 : GaC2_17_id (GaC2_17_lb_pos GaC2_17_lb_delta2) true.
Proof. vm_compute. exact GaC2_17_idr. Defined.

(* ---- Band 4: the decidable band skeleton ---- *)

(* The (a) band membership skeleton: 0 <= sigma <= 1 - delta as the    *)
(* boolean pair.                                                       *)
Definition GaC2_17_sigma_band (sigma delta : Q) : bool :=
  andb (Qle_bool 0 sigma) (Qle_bool sigma (1 - delta)).

(* sigma = 1/2 lies in the band at delta = 1/4. *)
Lemma GaC2_17_cert_band_in : GaC2_17_id (GaC2_17_sigma_band (1#2) (1#4)) true.
Proof. vm_compute. exact GaC2_17_idr. Defined.

(* sigma = 7/8 lies outside the band at delta = 1/4 (7/8 > 3/4). *)
Lemma GaC2_17_cert_band_out : GaC2_17_id (GaC2_17_sigma_band (7#8) (1#4)) false.
Proof. vm_compute. exact GaC2_17_idr. Defined.

(* ---- Assumption audit over the six certificates. ---- *)

Print Assumptions GaC2_17_cert_ub_sample1.
Print Assumptions GaC2_17_cert_ub_sample2.
Print Assumptions GaC2_17_cert_lb_pos1.
Print Assumptions GaC2_17_cert_lb_pos2.
Print Assumptions GaC2_17_cert_band_in.
Print Assumptions GaC2_17_cert_band_out.
