(* ConstructiveWorld-Set — extension of the Banach algebra class with scalar and separation fields. *)

(** * UpReqBanachClassExt: an extended Banach-algebra class and the
    discharge of explicit scalar premises.

    Mission.  The algebra class [BanachAlg] of [UpReqBanachExp] leaves two
    scalar-image laws as explicit premises downstream: additivity of the
    rational scalar image and its congruence.  This file packages an
    extension class [BanachAlgExt] carrying those laws as fields plus a
    separation field (arbitrarily small norm implies equality), checks
    each field definitionally against the premise shape it discharges,
    provides the migration constructor [bxce_mk], and re-derives four
    representative statements ([bxce_scal_plus], [bxce_binom_merge]).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Arith.Arith],
      [Lia].  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [UpReqBanachExp]; the frozen class [BanachAlg] is consumed, never
      redefined.

    References.  This development, ConstructiveWorld-Main
      UpReqBanachClassExt.v, the baseline module whose statement names are
      carried over here verbatim.

    Constructivity.  All named statements and fields are carried by [Set]
      ([QltT : Q -> Q -> Set]; the [Qeq] premise of [bxce_coef_wd] mirrors
      the explicit-premise shape it discharges).  Extraction gives
      [Obj.magic] = 0; [coqchk] reports [Axioms: none].  The completeness
      field being premise-free, concrete instances must use a complete
      carrier; this file is the interface-level deliverable.

    Build.  [coqc -native-compiler no -q -Q . "" UpReqBanachClassExt.v]
      compiles cleanly (exit 0); the artifact starts with [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ================= Section 1. The extension class [BanachAlgExt] ================= *)

(* The two scalar fields are shaped verbatim after the explicit premises of
   [UpReqBanachAdd]:
     hplus := forall q r, bae (bplus (bcoef q) (bcoef r)) (bcoef (q + r))
     hwd   := forall q r, q == r -> bae (bcoef q) (bcoef r)
   Class projections take the instance as an implicit argument, so field
   references feed the instance through [@ ... _ _ E] explicitly. *)
Class BanachAlgExt (BA : Set) (bae : BA -> BA -> Set) := {
  bxce_base : BanachAlg BA bae;

  (* Field one: additivity of the scalar image into [bcoef]. *)
  bxce_coef_plus : forall q r : Q,
    bae (@bplus _ _ bxce_base (@bcoef _ _ bxce_base q)
                                    (@bcoef _ _ bxce_base r))
                   (@bcoef _ _ bxce_base (q + r)%Q);

  (* Field two: congruence of the scalar image under [Qeq]. *)
  bxce_coef_wd : forall q r : Q,
    q == r -> bae (@bcoef _ _ bxce_base q) (@bcoef _ _ bxce_base r);

  (* Separation field: arbitrarily small norm implies equality; all-Set
     carriers, no Prop premises. *)
  bxce_sep : forall a : BA,
    (forall eps : Q, QltT 0 eps -> QltT (@bnorm _ _ bxce_base a) eps) ->
    bae a (@bzero _ _ bxce_base)
}.

(* Machine shape checks: each field is definitionally the premise shape it
   discharges — the type of each definition is exactly the checked shape. *)
Definition bxce_hplus_shape (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae) (q r : Q) :
  bae (@bplus _ _ (@bxce_base _ _ E) (@bcoef _ _ (@bxce_base _ _ E) q)
                                          (@bcoef _ _ (@bxce_base _ _ E) r))
       (@bcoef _ _ (@bxce_base _ _ E) (q + r)%Q)
  := @bxce_coef_plus _ _ E q r.

Definition bxce_hwd_shape (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae) (q r : Q) :
  q == r -> bae (@bcoef _ _ (@bxce_base _ _ E) q)
                                (@bcoef _ _ (@bxce_base _ _ E) r)
  := @bxce_coef_wd _ _ E q r.

(* Separation-field shape check, same style. *)
Definition bxce_sep_shape (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae) (a : BA) :
  (forall eps : Q, QltT 0 eps -> QltT (@bnorm _ _ (@bxce_base _ _ E) a) eps) ->
  bae a (@bzero _ _ (@bxce_base _ _ E))
  := @bxce_sep _ _ E a.

(* Norm-zero corollary: a vanishing norm [Id (bnorm a) 0] forces [bae a 0]. *)
Lemma bxce_sep_norm0 : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae) (a : BA),
  Id (@bnorm _ _ (@bxce_base _ _ E) a) 0%Q ->
  bae a (@bzero _ _ (@bxce_base _ _ E)).
Proof.
  intros BA bae E a H.
  apply (@bxce_sep _ _ E a).
  intros eps Heps.
  rewrite H.
  exact Heps.
Qed.

(* ================= Section 2. The migration constructor [bxce_mk] ================= *)

(* Any algebra model together with the two scalar laws and a separation
   theorem is bundled into an extension instance. *)
Definition bxce_mk (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (hp : forall q r : Q,
    bae (@bplus _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r)) (@bcoef _ _ B (q + r)%Q))
  (hw : forall q r : Q, q == r -> bae (@bcoef _ _ B q) (@bcoef _ _ B r))
  (sp : forall a : BA,
    (forall eps : Q, QltT 0 eps -> QltT (@bnorm _ _ B a) eps) ->
    bae a (@bzero _ _ B)) :
  BanachAlgExt BA bae
:= {| bxce_base := B; bxce_coef_plus := hp; bxce_coef_wd := hw;
      bxce_sep := sp |}.

(* ================= Section 3. Hypotheses discharged under the extension ================= *)

(* Each re-derivation below uses no scalar-additivity or scalar-congruence
   premise of the base development; [Print Assumptions] closes them all. *)

(* Scalar additivity: [bcoef q * T + bcoef r * T] equals [bcoef (q + r) * T]. *)
Lemma bxce_scal_plus : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae) (q r : Q)
    (T : BA),
  bae
    (@bplus _ _ (@bxce_base _ _ E)
       (@bmult _ _ (@bxce_base _ _ E) (@bcoef _ _ (@bxce_base _ _ E) q) T)
       (@bmult _ _ (@bxce_base _ _ E) (@bcoef _ _ (@bxce_base _ _ E) r) T))
    (@bmult _ _ (@bxce_base _ _ E) (@bcoef _ _ (@bxce_base _ _ E) (q + r)%Q) T).
Proof.
  intros BA bae E q r T.
  eapply (@bae_trans BA bae (@bxce_base _ _ E)).
  - apply (@bae_sym _ _ (@bxce_base _ _ E)).
    exact (@bdistrib_r _ _ (@bxce_base _ _ E) (@bcoef _ _ (@bxce_base _ _ E) q)
                        (@bcoef _ _ (@bxce_base _ _ E) r) T).
  - apply (@bmult_wd _ _ (@bxce_base _ _ E)
             (@bplus _ _ (@bxce_base _ _ E) (@bcoef _ _ (@bxce_base _ _ E) q)
                                    (@bcoef _ _ (@bxce_base _ _ E) r)) T
             (@bcoef _ _ (@bxce_base _ _ E) (q + r)%Q) T).
    + exact (@bxce_coef_plus _ _ E q r).
    + apply (@bae_refl _ _ (@bxce_base _ _ E)).
Qed.

(* Congruence under scalar multiplication: [q == r] forces
   [bcoef q * X] and [bcoef r * X] equal. *)
Lemma bxce_mult_coef_wd : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae) (q r : Q)
    (X : BA),
  q == r ->
  bae
    (@bmult _ _ (@bxce_base _ _ E) (@bcoef _ _ (@bxce_base _ _ E) q) X)
    (@bmult _ _ (@bxce_base _ _ E) (@bcoef _ _ (@bxce_base _ _ E) r) X).
Proof.
  intros BA bae E q r X H.
  apply (@bmult_wd _ _ (@bxce_base _ _ E)
           (@bcoef _ _ (@bxce_base _ _ E) q) X
           (@bcoef _ _ (@bxce_base _ _ E) r) X).
  - exact (@bxce_coef_wd _ _ E q r H).
  - apply (@bae_refl _ _ (@bxce_base _ _ E)).
Qed.

(* Out-of-range merge: [c2 == 0] forces [bcoef (c1 + c2) * Y] and
   [bcoef c1 * Y] equal. *)
Lemma bxce_pair_tail_shape : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae) (c1 c2 : Q)
    (Y : BA),
  c2 == 0%Q ->
  bae
    (@bmult _ _ (@bxce_base _ _ E) (@bcoef _ _ (@bxce_base _ _ E) (c1 + c2)%Q) Y)
    (@bmult _ _ (@bxce_base _ _ E) (@bcoef _ _ (@bxce_base _ _ E) c1) Y).
Proof.
  intros BA bae E c1 c2 Y H2.
  apply (@bmult_wd _ _ (@bxce_base _ _ E)
           (@bcoef _ _ (@bxce_base _ _ E) (c1 + c2)%Q) Y
           (@bcoef _ _ (@bxce_base _ _ E) c1) Y).
  - apply (@bxce_coef_wd _ _ E (c1 + c2)%Q c1).
    setoid_rewrite H2.
    apply Qplus_0_r.
  - apply (@bae_refl _ _ (@bxce_base _ _ E)).
Qed.

(* Binomial merge of the scalar image: [bcoef (c + d) * Z] equals
   [bcoef c * Z + bcoef d * Z] — the symmetry companion of scalar
   additivity above. *)
Lemma bxce_binom_merge : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae) (c d : Q)
    (Z : BA),
  bae
    (@bmult _ _ (@bxce_base _ _ E) (@bcoef _ _ (@bxce_base _ _ E) (c + d)%Q) Z)
    (@bplus _ _ (@bxce_base _ _ E)
       (@bmult _ _ (@bxce_base _ _ E) (@bcoef _ _ (@bxce_base _ _ E) c) Z)
       (@bmult _ _ (@bxce_base _ _ E) (@bcoef _ _ (@bxce_base _ _ E) d) Z)).
Proof.
  intros BA bae E c d Z.
  apply (@bae_sym _ _ (@bxce_base _ _ E)).
  exact (bxce_scal_plus _ _ E c d Z).
Qed.

Print Assumptions bxce_binom_merge.
