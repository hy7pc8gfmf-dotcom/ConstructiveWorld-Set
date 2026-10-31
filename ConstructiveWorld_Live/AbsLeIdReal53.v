(* ==========================================================================
   AbsLeIdReal53.v — Real-layer (concrete) absolute-value identity family, le version.
   Mission. Formalization of the properties stated by this file's theorem declaration faces: the identity |a| = a for 0 <= a at the concrete Real layer, its strict / eq / le translate forms, and the multiplication compatibility lemma r53_real_abs_mult_id.  Dependencies. S01_BaseRing, fa53_compat_abs, S02_CauchyComplete, S03_QExp, S07_RealSetoidExpLog (the Require face below).  References. The abstract-interface counterpart is fa53_compat_abs, reused by Require only and not duplicated.  Constructivity. Every piece is Qed-closed, zero admission-style statements, no classical logic; statement faces are all Set-valued (the order predicates and the equality are Set-valued, zero Prop leakage). The closing Print Assumptions statements audit every piece.  Build. coqc -native-compiler no -q -Q . "".
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import fa53_compat_abs.

(* ============ Layer 1: the abstract interface level (direct match
   against the fa53 base lemma, statement face identical) ============ *)
(* Same context as fa53; the @ explicit-application form throughout
   (DO is the section variable the proof body consumes; explicit
   substitution reads better than the omitted form). *)
Section R53AbsBridge.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Theorem r53_abs_ge_zero_id : forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI DO a Ha).
Qed.

End R53AbsBridge.

(* ============ Layer 2: the concrete Real-level realization (main
   body of this file) ============ *)
(* Cauchy reals (S02: Real := sigT (fun u : Qseq => cauchy u));
   real_le = Or real_lt real_eq, decided branch by branch. *)
(* The Requires stand after the abstract section: concrete-layer
   names are kept apart from interface projection names so the
   latter's name resolution is not shadowed. real_abs is defined in
   S03_QExp — the statement faces use it, so it must be Required
   explicitly (Require Import does not transit through re-export). *)
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.

(* ---- Main piece: an independent recast at the Real layer
   (uses real_abs_pos_req and real_abs_zero_req) ---- *)
Theorem r53_real_abs_ge_zero_id :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a H.
  unfold real_le in H.
  destruct H as [Hlt | Heq].
  - (* 0 < a: the strict pointwise lemma supplies it directly (real_abs_pos_req) *)
    exact (real_abs_pos_req a Hlt).
  - (* 0 == a: |a| ≈ |0| ≈ 0 ≈ a (abs-compat + zero lemma + sym/trans chain;
       real_eq_trans is applied with the middle point left implicit) *)
    apply (real_eq_trans _ (real_abs real_zero)).
    + apply (RealSetoid.real_eq_abs_compat a real_zero).
      apply real_eq_sym.
      exact Heq.
    + apply (real_eq_trans _ real_zero).
      * exact real_abs_zero_req.
      * exact Heq.
Qed.

(* ---- Extension 1 (uses real_lt_plus_translate): the strict translate form.
   real_lt_plus_translate only shifts by left addition (b+c < b+d); here
   0 < a is first moved to b+0 < b+a, then the right endpoint b+a is
   restated as b+|a| through the real_eq congruence (|a| ≈ a comes from
   the main piece's lt branch; real_lt_id_r: real_eq y z -> real_lt x y ->
   real_lt x z). ---- *)
Theorem r53_real_abs_lt_translate :
  forall a b : Real, real_lt real_zero a ->
    real_lt (real_plus b real_zero) (real_plus b (real_abs a)).
Proof.
  intros a b Hlt.
  apply (RealSetoid.real_lt_id_r (real_plus b real_zero) (real_plus b a)
                                 (real_plus b (real_abs a))).
  - apply (RealSetoid.real_eq_plus_compat b a b (real_abs a)).
    + apply real_eq_refl.
    + apply real_eq_sym.
      exact (r53_real_abs_ge_zero_id a (inl Hlt)).
  - exact (real_lt_plus_translate b real_zero a Hlt).
Qed.

(* ---- Extension 2 (uses real_abs_zero_req): the eq-branch translate form ----
   For 0 == a: b+0 ≈ b+|a| — after sym, |a| ≈ |0| (abs-compat, with a ≈ 0
   supplied by sym of Heq) and |0| ≈ 0 (zero lemma) reach the goal with a
   single trans level; the plus positions go through real_eq_plus_compat
   (its argument order pairs (a,c)/(b,d)). Pitfall note: in a nested trans
   the tail middle term gets pinned to real_zero by the zero lemma, after
   which Heq no longer matches — the single-level arrangement avoids this. ---- *)
Theorem r53_real_abs_eq_translate :
  forall a b : Real, real_eq real_zero a ->
    real_eq (real_plus b real_zero) (real_plus b (real_abs a)).
Proof.
  intros a b Heq.
  apply (RealSetoid.real_eq_plus_compat b real_zero b (real_abs a)).
  - apply real_eq_refl.
  - apply real_eq_sym.
    apply (real_eq_trans _ (real_abs real_zero)).
    + apply (RealSetoid.real_eq_abs_compat a real_zero).
      apply real_eq_sym.
      exact Heq.
    + exact real_abs_zero_req.
Qed.

(* ---- Extension 3: the le-version Or-encoded combination (the two
   branches of real_le are decided out to Extension 1 / Extension 2) ----
   Statement-face Or is the Set-level sum type (S01: Or A B := A + B),
   constructed with inl/inr. ---- *)
Theorem r53_real_abs_plus_translate :
  forall a b : Real, real_le real_zero a ->
    Or (real_lt (real_plus b real_zero) (real_plus b (real_abs a)))
       (real_eq (real_plus b real_zero) (real_plus b (real_abs a))).
Proof.
  intros a b H.
  unfold real_le in H.
  destruct H as [Hlt | Heq].
  - exact (inl (r53_real_abs_lt_translate a b Hlt)).
  - exact (inr (r53_real_abs_eq_translate a b Heq)).
Qed.

(* ---- Extension 4: the Real-layer multiplication combination (the
   concrete counterpart of the abstract-layer ali_abs_id_mult_l).
   real_eq_mult_compat pairs its arguments (a,c)/(b,d):
   |a| ≈ a supplies the first premise, b ≈ b the second. ---- *)
Theorem r53_real_abs_mult_id :
  forall a b : Real, real_le real_zero a ->
    real_eq (real_mult (real_abs a) b) (real_mult a b).
Proof.
  intros a b H.
  apply (RealSetoid.real_eq_mult_compat (real_abs a) b a b).
  - exact (r53_real_abs_ge_zero_id a H).
  - apply real_eq_refl.
Qed.

(* ---- Closing self-audit: an explicit Print Assumptions statement
   for every piece ---- *)
Print Assumptions r53_abs_ge_zero_id.
Print Assumptions r53_real_abs_ge_zero_id.
Print Assumptions r53_real_abs_lt_translate.
Print Assumptions r53_real_abs_eq_translate.
Print Assumptions r53_real_abs_plus_translate.
Print Assumptions r53_real_abs_mult_id.
