(* ConstructiveWorld-Main - certificate face of the eta continuation node. *)
(** * GaC2_10_EtaContinuation_cert: certificate face of node C2-10.

    Mission.  The decidable rational sample bands of the L13 obligation row
    (drafts_C2.md C2.10, the certificate row sigma0 in {1/2, 1}).  Band 1: the
    eta uniform-modulus weight corridor at the sigma0 = 1 and sigma0 = 1/2
    slots.  Band 2: the denominator lower-bound sample band on the real axis
    (the L13 local-constant registration), the s = 1/2 and s = 3/2 samples.
    The sample arithmetic and the scope statement sit in the Notes block.

    Dependencies.  Stdlib [QArith.QArith] only (base-standalone: no requires
    from the project statement tree); the Set-layer identity type [Id] used
    as the statement carrier is defined locally in this file.

    References.  drafts_C2.md C2.10 certificate line (the denominator
    lower-bound sample band, the sigma0 in {1/2, 1} two samples); the card
    C2.10 row (c) (the weight corridor 1 + 2 * 2^{-sigma0});
    gamma_module_spec.md section 4.2 (literal certificates, the
    compute-closed verification lemmas).

    Constructivity.  Every statement lives in [Set]: each verdict is carried
    by [Id] applied to a boolean verdict, and the weight form
    [GaC2_10_w1_form] is rational-valued.  Zero assumed constants, zero
    abandoned proofs; each certificate closes by virtual-machine computation
    followed by the identity constructor, and all statements are transparent
    ([Defined]) so the verdicts extract as data.

    Build.  [coqc -native-compiler no -q -Q . "" GaC2_10_EtaContinuation_cert.v]
    from the flat build directory (base-standalone, Stdlib only). *)

From Stdlib Require Import QArith.QArith.

Local Open Scope Q_scope.

(* The Set-layer identity type over a decidable verdict: [Id x y] is        *)
(* inhabited exactly when [x] and [y] are convertible elements of the       *)
(* Set [A].  Each certificate below states its boolean verdict as the data  *)
(* [Id verdict true] rather than as a proposition, so the verdicts extract  *)
(* as computable content.                                                   *)
Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

(** Notes.  Band 1 samples: the sigma0 = 1 slot closes exactly at 2 (the
    rational two-power 2^{-1} = 1/2); the sigma0 = 1/2 slot closes at the
    rational corridor 5/2 (the irrational 2^{-1/2} enters through its rational
    upper face 3/4, underpinned by the square band 2 >= (4/3)^2 = 16/9).
    Band 2 samples: the s = 1/2 sample ([GaC2_10_cert_lb_s1_2]:
    sqrt(2) > 7/5 gives |1 - 2^(1/2)| > 2/5; [GaC2_10_cert_lb_sq_s1_2]: the
    squared form 3 - 2 sqrt(2) > 1/6 from sqrt(2) < 17/12), and the s = 3/2
    sample ([GaC2_10_cert_lb_sq_s3_2]: the squared form 3/2 - sqrt(2) > 1/12
    from the same square band).

    Scope boundary, stated explicitly: these bands certify the rational
    corridor forms and the decidable skeleton only; the Real-line bound faces
    live on the statement side with the premise family, the s = 1 point is a
    denominator zero (the zero-set face of C2-09) so no sample is claimed
    there, and the irrationals enter only through their rational square-band
    certificates. *)


(* ---- Band 1: the eta weight corridor at the two sigma0 samples ---- *)

(* The weight corridor form: 1 + 2 * q, q the rational slot of the     *)
(* two-power face 2^{-sigma0}.                                          *)
Definition GaC2_10_w1_form (q : Q) : Q := 1 + 2 * q.

(* The sigma0 = 1 sample: 2^{-1} = 1/2 rational, the corridor closes    *)
(* exactly at 2.                                                        *)
Lemma GaC2_10_cert_w1_sigma_one : Id (Qeq_bool (GaC2_10_w1_form (1#2)) 2) true.
Proof. vm_compute. exact (@id_refl bool true). Defined.

(* The underpinning square band for the sigma0 = 1/2 slot: 2 >= 16/9,   *)
(* i.e. 2^{-1/2} <= 3/4.                                                *)
Lemma GaC2_10_cert_two_ge_16_9 : Id (Qle_bool (16#9) 2) true.
Proof. vm_compute. exact (@id_refl bool true). Defined.

(* The sigma0 = 1/2 sample: the corridor closes at the rational         *)
(* corridor 1 + 2 * (3/4) = 5/2.                                        *)
Lemma GaC2_10_cert_w1_sigma_half : Id (Qle_bool (GaC2_10_w1_form (3#4)) (5#2)) true.
Proof. vm_compute. exact (@id_refl bool true). Defined.

(* ---- Band 2: the denominator lower-bound samples on the real axis -- *)

(* The s = 1/2 sample, linear form: sqrt(2) > 7/5 strictly, i.e.        *)
(* |1 - 2^(1/2)| = sqrt(2) - 1 > 2/5 (the strict face as the negated    *)
(* weak order: 2 <= 7/5^2 is false).                                    *)
Lemma GaC2_10_cert_lb_s1_2 : Id (negb (Qle_bool 2 (49#25))) true.
Proof. vm_compute. exact (@id_refl bool true). Defined.

(* The s = 1/2 sample, squared form: |1 - 2^(1/2)|^2 = 3 - 2 sqrt(2)    *)
(* > 1/6 strictly, from sqrt(2) < 17/12 (the square band (17/12)^2 =    *)
(* 289/36 > 8, the strict face as the negated weak order).              *)
Lemma GaC2_10_cert_lb_sq_s1_2 : Id (negb (Qle_bool (289#36) 8)) true.
Proof. vm_compute. exact (@id_refl bool true). Defined.

(* The s = 3/2 sample, squared form: |1 - 2^(-1/2)|^2 = 3/2 - sqrt(2)   *)
(* > 1/12 strictly, from the same square band 2 < (17/12)^2 = 289/144.  *)
Lemma GaC2_10_cert_lb_sq_s3_2 : Id (negb (Qle_bool (289#144) 2)) true.
Proof. vm_compute. exact (@id_refl bool true). Defined.
