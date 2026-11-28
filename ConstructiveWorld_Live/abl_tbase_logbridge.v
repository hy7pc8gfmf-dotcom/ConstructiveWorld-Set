(* ======================================================================== *)
(* Module   : abl_tbase_logbridge                                           *)
(* Mission. Twenty named instances of the four elementary logarithm         *)
(*            identities over the constructive Cauchy real line:            *)
(*            (A) req (log (inv_pos x Hx) Hi) (opp (log x Hx));             *)
(*            (B) req (log (exp_neg u) (exp_neg_pos u)) (opp u);            *)
(*            (C) req x y -> req (log x Hx) (log y Hy);                     *)
(*            (D) req (log_inv (exp_neg x) (exp_neg_pos x)) x.              *)
(*            Each instance is delivered under its own name for its own     *)
(*            consumption site; every conclusion is a Set-carried value.    *)
(* Dependencies. S02_CauchyComplete (the Real carrier and its Set-valued    *)
(*            predicates real_eq/real_lt), G05_LogSmall (the logd_ Real-    *)
(*            layer roots and the req/lt/log notation face); Stdlib none.   *)
(* References. G05_LogSmall :317 (log compatibility under req), :341        *)
(*            (log of the exponential), :352 (log of the reciprocal),       *)
(*            :274 (the log_inv/exp_neg mutual reduction fed by the :341    *)
(*            root); the carrier and its predicates at                      *)
(*            S02_CauchyComplete :511/:513/:582.                            *)
(* Constructivity. Zero Prop statements: every conclusion and every         *)
(*            positivity premise sits on the decidable Set predicates       *)
(*            real_eq/real_lt (the QltT/QeqT Id-plus-bool family of         *)
(*            S02:150/:227); the sigT-embedded order data inside real_lt    *)
(*            is the existing library mirror form, imported as-is.          *)
(*            Every closure is Defined (transparent): no conclusion face    *)
(*            is a pure Prop bridge, so no Qed closure appears anywhere;    *)
(*            zero axioms, zero admits, no classical logic.                 *)
(* Build. coqc -native-compiler no -q -Q <tree root> ""                     *)
(*            abl_tbase_logbridge.v (single shot, this directory as         *)
(*            workdir).                                                     *)
(* ======================================================================== *)

Require Import S02_CauchyComplete.
Require Import G05_LogSmall.

(* ============================================================ *)
(* Section 1. The reciprocal-log identity log(1/x) = -log x:     *)
(* two named instances of the same identity.                     *)
(* ============================================================ *)

Theorem tblb_udist_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Defined.

Theorem tblb_udist_log_exp_neg :
  forall u : Real, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Defined.

(* ============================================================ *)
(* Section 2. The exponential-log identity log(e^{-x}) = -x:     *)
(* two named instances.                                          *)
(* ============================================================ *)

Theorem tblb_ute_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Defined.

Theorem tblb_ute_log_exp_neg :
  forall u : Real, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Defined.

(* ============================================================ *)
(* Section 3. Two reciprocal-log instances, two exponential-log  *)
(* instances, and the compatibility of log under req             *)
(* (x = y implies log x = log y for positive arguments):         *)
(* five named instances.                                         *)
(* ============================================================ *)

Theorem tblb_ufepa1_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Defined.

Theorem tblb_ufepa1_log_exp_neg :
  forall u : Real, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Defined.

Theorem tblb_ufepa2_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Defined.

Theorem tblb_ufepa2_log_exp_neg :
  forall u : Real, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Defined.

Theorem tblb_ufepa2_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Defined.

(* ============================================================ *)
(* Section 4. Two exponential-log instances and two compatibility *)
(* instances (bound names a/b/Ha/Hb kept from the slot shape):    *)
(* four named instances.                                          *)
(* ============================================================ *)

Theorem tblb_usigm_req_log_exp_neg :
  forall x : Real, req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  exact (logd_log_exp_neg_real x).
Defined.

Theorem tblb_usigm_req_log_compat :
  forall (a b : Real) (Ha : lt zero a) (Hb : lt zero b),
    req a b -> req (log a Ha) (log b Hb).
Proof.
  intros a b Ha Hb Hab.
  exact (logd_log_compat_real a b Ha Hb Hab).
Defined.

Theorem tblb_usigm_b_log_exp_neg :
  forall x : Real, req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  exact (logd_log_exp_neg_real x).
Defined.

Theorem tblb_usigm_b_log_compat :
  forall (a b : Real) (Ha : lt zero a) (Hb : lt zero b),
    req a b -> req (log a Ha) (log b Hb).
Proof.
  intros a b Ha Hb Hab.
  exact (logd_log_compat_real a b Ha Hb Hab).
Defined.

(* ============================================================ *)
(* Section 5. The compatibility instance and the exponential-log *)
(* instance, first family: two named instances.                  *)
(* ============================================================ *)

Theorem tblb_bbd_sup_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Defined.

Theorem tblb_bbd_sup_log_exp_neg : forall u : Real,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Defined.

(* ============================================================ *)
(* Section 6. The same pair, second family: two named instances. *)
(* ============================================================ *)

Theorem tblb_boltz_sup_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Defined.

Theorem tblb_boltz_sup_log_exp_neg : forall u : Real,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Defined.

(* ============================================================ *)
(* Section 7. The same pair, third family: two named instances.  *)
(* ============================================================ *)

Theorem tblb_ulogcompd_sup_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Defined.

Theorem tblb_ulogcompd_sup_log_exp_neg : forall u : Real,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Defined.

(* ============================================================ *)
(* Section 8. log_inv after exp_neg is the identity: obtained    *)
(* from the exponential-log identity through the mutual          *)
(* reduction of the two slots (G05_LogSmall :274 fed by :341).    *)
(* ============================================================ *)

Theorem tblb_ualgebra_log_inv_exp_neg_req :
  forall x : Real, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  exact (logd_log_inv_exp_neg_of_log_exp_neg logd_log_exp_neg_real x).
Defined.

(* ============================================================ *)
(* Assumption audit: one Print Assumptions per theorem.          *)
(* ============================================================ *)
Print Assumptions tblb_udist_log_inv_one_inv.
Print Assumptions tblb_udist_log_exp_neg.
Print Assumptions tblb_ute_log_inv_one_inv.
Print Assumptions tblb_ute_log_exp_neg.
Print Assumptions tblb_ufepa1_log_inv_one_inv.
Print Assumptions tblb_ufepa1_log_exp_neg.
Print Assumptions tblb_ufepa2_log_inv_one_inv.
Print Assumptions tblb_ufepa2_log_exp_neg.
Print Assumptions tblb_ufepa2_log_req_compat.
Print Assumptions tblb_usigm_req_log_exp_neg.
Print Assumptions tblb_usigm_req_log_compat.
Print Assumptions tblb_usigm_b_log_exp_neg.
Print Assumptions tblb_usigm_b_log_compat.
Print Assumptions tblb_bbd_sup_compat.
Print Assumptions tblb_bbd_sup_log_exp_neg.
Print Assumptions tblb_boltz_sup_compat.
Print Assumptions tblb_boltz_sup_log_exp_neg.
Print Assumptions tblb_ulogcompd_sup_compat.
Print Assumptions tblb_ulogcompd_sup_log_exp_neg.
Print Assumptions tblb_ualgebra_log_inv_exp_neg_req.
