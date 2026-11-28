(* ========================================================================= *)
(* Module   : abl_tbase_klcx_rppo_sum                                       *)
(* Mission. Supply theorems for finite enumeration sums over the           *)
(*             constructive real carrier: extensionality, additivity,       *)
(*             linearity, weak monotonicity, strict positivity from a       *)
(*             cons-head witness, the zero-total collapse under explicit    *)
(*             enumeration-surjection data, and compatibility of the        *)
(*             constructive logarithm under pointwise equality; all eleven  *)
(*             conclusions are Set-valued interface predicates (req/le/lt). *)
(* Dependencies. UpReqSumD (sumd_sumf, sumd_sum_ext, sumd_sum_add,          *)
(*             sumd_sum_linear, sumd_sum_le, sumd_list_sum_pos_cons,        *)
(*             sumd_sum_zero_nonneg_surj, sumd_in); G05_LogSmall            *)
(*             (logd_log_compat_real, and the field-name notations          *)
(*             req/lt/le/zero/plus/mult/log binding the concrete global     *)
(*             interface instance); Stdlib List.                            *)
(* References. Statement families mirror the discharged signatures of       *)
(*             UpReqSumD (:113/:143/:185/:265/:279/:513) and the log        *)
(*             compatibility lemma of G05_LogSmall (:317); the two          *)
(*             statement groups coincide on the four shared sum statements  *)
(*             and are kept as separately named faces.                      *)
(* Constructivity. Zero axioms, zero assumptions, zero classical logic;     *)
(*             no opaque proof closure anywhere; every statement face is    *)
(*             Set-valued (req/le/lt are Real -> Real -> Set; sumd_in :     *)
(*             Set), so no Prop statement occurs; every proof is closed     *)
(*             transparently with Defined (sufficient since no pure-Prop    *)
(*             proof bridge is present). The interface class is             *)
(*             unparameterized with one global instance, so the carrier is  *)
(*             the concrete Real throughout.                                *)
(* Build. rocq c -native-compiler no -q -Q <Set Live world root> ""  abl_tbase_klcx_rppo_sum.v *)
(* ========================================================================= *)

From Stdlib Require Import List.
Import ListNotations.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import UpReqSumD.
Require Import G05_LogSmall.

(* ============================================================ *)
(* Group one: the enumerated-sum six-statement family. Each     *)
(* conclusion is a Set-valued interface predicate on the finite *)
(* enumeration sum of the constructive reals.                   *)
(* ============================================================ *)

Theorem tbkx_klcx_sum_ext :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    (forall s : S, req (f s) (g s)) ->
    req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Defined.

Theorem tbkx_klcx_sum_add :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  exact (sumd_sum_add S enum f g).
Defined.

Theorem tbkx_klcx_sum_linear :
  forall (S : Set) (enum : list S) (a : Real) (f : S -> Real),
    req (sumd_sumf S enum (fun s : S => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Defined.

Theorem tbkx_klcx_sum_le :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    (forall s : S, le (f s) (g s)) ->
    le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_le S enum f g H).
Defined.

(* The non-emptiness witness is carried as data: the cons head w of the *)
(* enumeration is itself the witness, so the statement keeps a purely   *)
(* Set-shaped face with no added premise beyond the enumeration.        *)
Theorem tbkx_klcx_sum_pos_cons :
  forall (S : Set) (f : S -> Real) (w : S) (rest : list S),
    (forall s : S, lt zero (f s)) ->
    lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Defined.

(* The zero-total collapse needs the enumeration to be exhaustive; the *)
(* surjection data is an explicit Set-valued premise (sumd_in : Set).  *)
Theorem tbkx_klcx_sum_zero_nonneg_surj :
  forall (S : Set) (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> Real,
      (forall s : S, le zero (f s)) ->
      req (sumd_sumf S enum f) zero ->
      forall s : S, req (f s) zero.
Proof.
  intros S enum Hsurj f Hnn H0 s.
  exact (sumd_sum_zero_nonneg_surj S enum f Hsurj Hnn H0 s).
Defined.

(* ============================================================ *)
(* Group two: the advantage-section five-statement family. The  *)
(* four sum statements are the Real-carrier reading of the same *)
(* signatures as group one and are kept under their own names;  *)
(* the fifth states compatibility of the constructive log.      *)
(* ============================================================ *)

Theorem tbkx_arch10_sum_ext :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    (forall s : S, req (f s) (g s)) ->
    req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Defined.

Theorem tbkx_arch10_sum_add :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  exact (sumd_sum_add S enum f g).
Defined.

Theorem tbkx_arch10_sum_linear :
  forall (S : Set) (enum : list S) (a : Real) (f : S -> Real),
    req (sumd_sumf S enum (fun s : S => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Defined.

Theorem tbkx_arch10_sum_pos_cons :
  forall (S : Set) (f : S -> Real) (w : S) (rest : list S),
    (forall s : S, lt zero (f s)) ->
    lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros S f w rest H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Defined.

Theorem tbkx_arch10_rppo_log_compat :
  forall (a b : Real) (Ha : lt zero a) (Hb : lt zero b),
    req a b -> req (log a Ha) (log b Hb).
Proof.
  intros a b Ha Hb Hab.
  exact (logd_log_compat_real a b Ha Hb Hab).
Defined.

(* ============================================================ *)
(* Assumption audit: one Print Assumptions per theorem.         *)
(* ============================================================ *)

Print Assumptions tbkx_klcx_sum_ext.
Print Assumptions tbkx_klcx_sum_add.
Print Assumptions tbkx_klcx_sum_linear.
Print Assumptions tbkx_klcx_sum_le.
Print Assumptions tbkx_klcx_sum_pos_cons.
Print Assumptions tbkx_klcx_sum_zero_nonneg_surj.
Print Assumptions tbkx_arch10_sum_ext.
Print Assumptions tbkx_arch10_sum_add.
Print Assumptions tbkx_arch10_sum_linear.
Print Assumptions tbkx_arch10_sum_pos_cons.
Print Assumptions tbkx_arch10_rppo_log_compat.
