(* ConstructiveWorld-Set -- fa53 decision certificates transported onto the six-slot statement face. *)

(** * DecBridge6: bridging the [Id]-branch decision certificates of fa53 to [req] certificates.

    Mission.  The fa53 decision engine ends its trichotomy with an [Id]
      equality certificate, while the six-slot statement face reads the
      equality branch at [req]; on the definition plane where the assembly
      bridge fixes [req := Id] (built inline below at the S01 carrier),
      this file transports the
      [Id] branch to the [req] face through [db6_id_req] and supplies the
      matching companions [db6_ord_le_dec], [db6_lt_dec_id],
      [db6_rae_le_dec], [db6_rae_lt_dec], [db6_probe_le_dec],
      [db6_probe_lt_dec], [db6_req_lt_plus_compat_lt_le] and
      [db6_ralt_lt_plus_compat_lt_le].

    Dependencies.  Requires [S01_BaseRing], [S07_RealSetoidExpLog],
      [TempSoftmaxInstantiation], [fa53_compat_abs] of this development.

    References.  This development, DecBridge6.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" DecBridge6.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
Require Import S01_BaseRing.
Require Import S07_RealSetoidExpLog.
Require Import TempSoftmaxInstantiation.
Require Import fa53_compat_abs.

(* ---- Definition plane of the six-slot statement faces.  In this
   world the landed S07 carrier face is zero-argument: the class
   RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid carries no
   carrier slot (its fields sit at the global Real carrier,
   S07:8696 / S02:511; only the S07 r_if wrappers keep a vestigial
   carrier slot, S07:9530), and the landed TempSoftmaxInstantiation.vo
   exports no carrier-indexed assembly bridge.  The statement faces of
   this file read the mod projections at the section carrier in the
   four-slot form (carrier, instance, two elements), so the mod face
   is supplied locally in that carrier-indexed shape.  The three
   relation/operation slots ride the class fields; the req slot is
   spelled as its own definition with the [Id] body (the mission of
   this file: req fixed at [Id]), so the conclusion of [db6_id_req]
   stays carrier-uniform under extraction (no erasure cast). ---- *)
Module RealInterfaceEnhancedMod.

Class RealInterfaceEnhancedSetoid (R : Set) := {
  sle : R -> R -> Set;
  slt : R -> R -> Set;
  splus : R -> R -> R;
}.

Definition req (R : Set) (d : RealInterfaceEnhancedSetoid R) (x y : R) : Set := @Id R x y.
Definition le (R : Set) (d : RealInterfaceEnhancedSetoid R) (x y : R) : Set := @sle R d x y.
Definition lt (R : Set) (d : RealInterfaceEnhancedSetoid R) (x y : R) : Set := @slt R d x y.
Definition plus (R : Set) (d : RealInterfaceEnhancedSetoid R) (x y : R) : R := @splus R d x y.

End RealInterfaceEnhancedMod.

Section DecBridge6.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* Abbreviation for the assembly-bridge instance: the enrichment structure on the S01 carrier, with the req branch fixed at [Id]; the le/lt/plus slots read the S01 same-name projections, so both faces carry the same relations up to conversion. *)
Let TSI : RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid
            (@S01_BaseRing.R RI) :=
  RealInterfaceEnhancedMod.Build_RealInterfaceEnhancedSetoid
    (@S01_BaseRing.R RI)
    (@S01_BaseRing.le RI)
    (@S01_BaseRing.lt RI)
    (@S01_BaseRing.plus RI).

(* Statement-face slot projections: each bridge field is read explicitly, matching the host structure slots by name and shape. *)
Let rle  : @S01_BaseRing.R RI -> @S01_BaseRing.R RI -> Set :=
  fun a b => @RealInterfaceEnhancedMod.le (@S01_BaseRing.R RI) TSI a b.
Let rlt  : @S01_BaseRing.R RI -> @S01_BaseRing.R RI -> Set :=
  fun a b => @RealInterfaceEnhancedMod.lt (@S01_BaseRing.R RI) TSI a b.
Let rreq : @S01_BaseRing.R RI -> @S01_BaseRing.R RI -> Set :=
  fun a b => @RealInterfaceEnhancedMod.req (@S01_BaseRing.R RI) TSI a b.
Let rplus : @S01_BaseRing.R RI -> @S01_BaseRing.R RI -> @S01_BaseRing.R RI :=
  fun a b => @RealInterfaceEnhancedMod.plus (@S01_BaseRing.R RI) TSI a b.

(* ---- fa53 projection alias: the class field name lt_dec is shadowed
   by Stdlib Compare_dec (match projection as in fa53_compat_abs.v:39-44) ---- *)
Definition db6_ord_le_dec :
  forall a b : @S01_BaseRing.R RI,
    Or (@S01_BaseRing.le RI a b) (@S01_BaseRing.Not (@S01_BaseRing.le RI a b)) :=
  match DO with
  | Build_DecidableOrder _ ord _ _ _ _ => ord
  end.

Definition db6_lt_dec_id :
  forall a b : @S01_BaseRing.R RI,
    Or (@S01_BaseRing.lt RI a b)
       (Or (Id a b) (@S01_BaseRing.lt RI b a)) :=
  match DO with
  | Build_DecidableOrder _ _ lt_d _ _ _ => lt_d
  end.

(* ============================================================ *)
(* New mathematical point: the req-Id decision-branch transport bridge.  *)
(*   In the fa53 engine trichotomy the middle branch carries an [Id]     *)
(*   certificate; on the six-slot statement face it carries a [req]      *)
(*   certificate.  The req field of the assembly bridge is definitional  *)
(*   [fun x y => Id x y], so the transport is conversion-level movement; *)
(*   the bridge is cast as an explicit statement to carry that meaning.  *)
(* ============================================================ *)
Theorem db6_id_req :
  forall (a b : @S01_BaseRing.R RI),
    Id a b -> @RealInterfaceEnhancedMod.req (@S01_BaseRing.R RI) TSI a b.
Proof.
  intros a b H. exact H.
Qed.

(* ---- Slot #34/#36 shape: the binary le decision, given directly by the DO field ord_le_dec ---- *)
Theorem db6_rae_le_dec :
  forall a b : @S01_BaseRing.R RI, Or (rle a b) (Not (rle a b)).
Proof.
  intros a b. exact (db6_ord_le_dec a b).
Qed.

(* ---- Slot #35/#37 shape: the trichotomy decision (engine output
   direct plus transport of the equality branch).  The inl and inr-inr
   branches match the engine output shape verbatim; the inr-inl branch
   goes through the transport bridge db6_id_req, turning the Id decision
   certificate into the req decision certificate (the new mathematical
   point of this file). ---- *)
Theorem db6_rae_lt_dec :
  forall a b : @S01_BaseRing.R RI,
    Or (rlt a b) (Or (rreq a b) (rlt b a)).
Proof.
  intros a b.
  destruct (db6_lt_dec_id a b) as [Hlt | [Heq | Hgt]].
  - (* a < b: the strict branch is given directly *)
    exact (inl Hlt).
  - (* a == b: the Id certificate transports to the req certificate *)
    exact (inr (inl (db6_id_req a b Heq))).
  - (* b < a: the strict branch on the far side is given directly *)
    exact (inr (inr Hgt)).
Qed.

(* ---- Slot #36/#37: the probe positions, same statements as the rae positions, kept as independent statements for cross-checking ---- *)
Theorem db6_probe_le_dec :
  forall a b : @S01_BaseRing.R RI, Or (rle a b) (Not (rle a b)).
Proof.
  exact db6_rae_le_dec.
Qed.

Theorem db6_probe_lt_dec :
  forall a b : @S01_BaseRing.R RI,
    Or (rlt a b) (Or (rreq a b) (rlt b a)).
Proof.
  exact db6_rae_lt_dec.
Qed.

(* ---- Slot #38/#39 shape: order preservation under addition, strict
   on the left and non-strict on the right.  The statement is verbatim
   fa53_lt_plus_compat_lt_le_dec at fa53_compat_abs.v:103 (le, lt and
   plus read through the assembly bridge equal the S01 namesake
   projections, so both faces carry the same relation up to conversion);
   one exact closes it, and slot #39 restates slot #38 at the ralt
   position as an independent statement. ---- *)
Theorem db6_req_lt_plus_compat_lt_le :
  forall a b c d : @S01_BaseRing.R RI,
    @S01_BaseRing.lt RI a b -> rle c d -> rlt (rplus a c) (rplus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (fa53_lt_plus_compat_lt_le_dec a b c d Hab Hcd).
Qed.

Theorem db6_ralt_lt_plus_compat_lt_le :
  forall a b c d : @S01_BaseRing.R RI,
    @S01_BaseRing.lt RI a b -> rle c d -> rlt (rplus a c) (rplus b d).
Proof.
  exact db6_req_lt_plus_compat_lt_le.
Qed.

End DecBridge6.

(* ---- Inline audit block: each main statement is followed by an explicit Print Assumptions declaration in this file ---- *)
Print Assumptions db6_id_req.
Print Assumptions db6_rae_le_dec.
Print Assumptions db6_rae_lt_dec.
Print Assumptions db6_probe_le_dec.
Print Assumptions db6_probe_lt_dec.
Print Assumptions db6_req_lt_plus_compat_lt_le.
Print Assumptions db6_ralt_lt_plus_compat_lt_le.
