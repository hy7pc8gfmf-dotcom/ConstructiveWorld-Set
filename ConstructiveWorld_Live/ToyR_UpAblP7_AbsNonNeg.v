(* ConstructiveWorld-Set -- ToyR_UpAblP7_AbsNonNeg: unconditional absolute
   value non-negativity on the concrete Cauchy real layer. *)
(** * ToyR_UpAblP7_AbsNonNeg: unconditional abs non-negativity on the
    concrete Cauchy real layer, carried on Set.

    Mission.  [uabp7an_abs_nonneg_uncond] derives [req (abs a) a] from the
      weakened premise [le zero a]; it strengthens the interface field
      [abs_pos], whose premise covers strict positivity [lt zero a] only.
      The file also carries nine Q-layer auxiliary lemmas, the main piece
      [uabp7an_core], and the two-directional bridge between the
      unconditional form and the interface per-eps form.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Lia] and
      [QArith.Qminmax]; the chain S01..S15 of this development and
      [UpReqAlgebra]; the [RealInterfaceEnhancedMod] interface fields.

    References.  Non-negativity of the absolute value in Bishop's
      constructive analysis; the plain-form companion of the [abs_nonneg]
      interface field.

    Constructivity.  Purely constructive; every proof ends in [Qed]; the
      [real_le] Or split is eliminated constructively on the premise
      side (the Q order is decidable), so no classical logic is used;
      [Print Assumptions] reports Closed for all thirteen statements.

    Build.  [rocq c -native-compiler no -q -Q . ""
      ToyR_UpAblP7_AbsNonNeg.v] on Rocq 9.1.0, compilation wrapped by
      the cpu_guard resource wrapper. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia QArith.Qminmax.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the
   global Real (same adaptation as UpReqAlgebra). *)
Notation R := Real.

(* Extraction-face configuration (r3 case-4 combination knife; zero
   statement-face change; kernel-neutral codegen directives).  Knife A (r1
   case1a): inline the transparent interface instance [RealEnhancedReal].
   Knife B (r1 case1b): inline the three type-position projections
   req/lt/le.  Knife D (r3, untried in r1/r2): notation re-carrier -- the
   class fields le/req/lt are DEFINITIONAL aliases of the concrete carriers
   real_le/real_eq/real_lt through the identity Instance RealEnhancedReal
   (S07_RealSetoidExpLog.v:8740: req := real_eq; lt := real_lt; le := real_le;
   zero := real_zero; plus := real_plus; abs := real_abs).  These notation
   abbreviations pin the elaboration of the three interface statements onto
   the very same concrete carriers, so the extractor renders the statement
   types concretely instead of as abstract class-projection types.  All
   thirteen statement sentences below remain byte-identical; no proof body
   is edited. *)
Notation le := real_le.
Notation req := real_eq.
Notation lt := real_lt.
Extraction Inline RealEnhancedReal.
Extraction Inline RealInterfaceEnhancedMod.req.
Extraction Inline RealInterfaceEnhancedMod.lt.
Extraction Inline RealInterfaceEnhancedMod.le.

(* ============================================================ *)
(* I. Q-layer auxiliary pieces (order relations of the half and  *)
(*    the quarter, Qabs lower-bound flip; zero classical logic)  *)
(* ============================================================ *)

(* Negative zero identity: QeqT (- 0)%Q 0%Q (reused in several places) *)
Lemma uabp7an_qneg0 : QeqT (- 0)%Q 0%Q.
Proof. apply qeq_imp_qeqT. ring. Qed.

(* e/2 strictly positive (QltT 0 (e/2) from QltT 0 e, via the decidable
   Q-order split and Qplus_le_compat) *)
Lemma uabp7an_qlt_half : forall e : Q, QltT 0 e -> QltT 0 (e / 2).
Proof.
  intros e He.
  assert (HeQ : 0 < e) by (apply QltT_to_Qlt; exact He).
  apply Qlt_to_QltT.
  assert (Hsum : e / 2 + e / 2 == e) by field.
  destruct (Qlt_le_dec 0 (e / 2)) as [Hc | Hc].
  - exact Hc.
  - exfalso.
    assert (Hle : e / 2 + e / 2 <= 0 + 0)
      by (apply (Qplus_le_compat (e / 2) 0 (e / 2) 0); [exact Hc | exact Hc]).
    assert (Hz1 : (0 + 0)%Q == 0%Q) by ring.
    rewrite Hz1 in Hle.
    rewrite Hsum in Hle.
    exact (Qlt_not_le 0 e HeQ Hle).
Qed.

(* Half-addition identity: QeqT (e/2 + e/2) e *)
Lemma uabp7an_half_add : forall e : Q, QeqT (e / 2 + e / 2) e.
Proof. intro e. apply qeq_imp_qeqT. field. Qed.

(* Half strictly below: QltT (e/2) e (from QltT 0 e) *)
Lemma uabp7an_half_lt : forall e : Q, QltT 0 e -> QltT (e / 2) e.
Proof.
  intros e He.
  apply Qlt_to_QltT.
  assert (Hh : QltT 0 (e / 2)) by (apply uabp7an_qlt_half; exact He).
  assert (HhQ : 0 < e / 2) by (apply QltT_to_Qlt; exact Hh).
  assert (H1 : e / 2 + 0 < e / 2 + e / 2)
    by (apply (proj2 (Qplus_lt_r 0 (e / 2) (e / 2))); exact HhQ).
  assert (Hz0 : (e / 2 + 0)%Q == (e / 2)%Q) by ring.
  rewrite Hz0 in H1.
  assert (Hsum : e / 2 + e / 2 == e) by field.
  rewrite Hsum in H1.
  exact H1.
Qed.

(* Half strictly below the negative-zero shape: QltT (e/2) (e - 0)
   (from QltT 0 e) -- matches the projection target form of the Cauchy
   representation *)
Lemma uabp7an_half_lt_m0 : forall e : Q, QltT 0 e -> QltT (e / 2) (e - 0).
Proof.
  intros e He.
  apply Qlt_to_QltT.
  assert (HhQ : 0 < e / 2)
    by (apply QltT_to_Qlt; apply uabp7an_qlt_half; exact He).
  assert (H1 : e / 2 + 0 < e / 2 + e / 2)
    by (apply (proj2 (Qplus_lt_r 0 (e / 2) (e / 2))); exact HhQ).
  assert (Hz0 : (e / 2 + 0)%Q == (e / 2)%Q) by ring.
  rewrite Hz0 in H1.
  assert (Hsum : e / 2 + e / 2 == e - 0) by field.
  rewrite Hsum in H1.
  exact H1.
Qed.

(* Half not above: QleT' (e/2) e (from QltT 0 e) *)
Lemma uabp7an_half_le : forall e : Q, QltT 0 e -> QleT' (e / 2) e.
Proof.
  intros e He.
  assert (HhQ : 0 < e / 2)
    by (apply QltT_to_Qlt; apply uabp7an_qlt_half; exact He).
  assert (H1 : e / 2 + 0 < e / 2 + e / 2)
    by (apply (proj2 (Qplus_lt_r 0 (e / 2) (e / 2))); exact HhQ).
  assert (Hz0 : (e / 2 + 0)%Q == (e / 2)%Q) by ring.
  rewrite Hz0 in H1.
  assert (Hsum : e / 2 + e / 2 == e) by field.
  rewrite Hsum in H1.
  apply Qle_to_QleT'. apply Qlt_le_weak. exact H1.
Qed.

(* Quarter strictly below the half: QltT (e/4) (e/2) (from QltT 0 e) *)
Lemma uabp7an_q4_lt_q2 : forall e : Q, QltT 0 e -> QltT (e / 4) (e / 2).
Proof.
  intros e He.
  apply Qlt_to_QltT.
  assert (Hq4 : QltT 0 (e / 4)) by (apply uabp7an_qlt_half; exact He).
  assert (Hq4Q : 0 < e / 4) by (apply QltT_to_Qlt; exact Hq4).
  assert (H1 : e / 4 + 0 < e / 4 + e / 4)
    by (apply (proj2 (Qplus_lt_r 0 (e / 4) (e / 4))); exact Hq4Q).
  assert (Hz0 : (e / 4 + 0)%Q == (e / 4)%Q) by ring.
  rewrite Hz0 in H1.
  assert (Hsum : e / 4 + e / 4 == e / 2) by field.
  rewrite Hsum in H1.
  exact H1.
Qed.

(* Qabs lower-bound flip: QltT (Qabs x) e and QltT 0 e give QltT (- e) x
   (decidable Q-order split plus Qopp_lt_compat) *)
Lemma uabp7an_abs_lb : forall x e : Q,
  QltT 0 e -> QltT (Qabs x) e -> QltT (- e) x.
Proof.
  intros x e He Hb.
  assert (HeQ : 0 < e) by (apply QltT_to_Qlt; exact He).
  assert (HbQ : Qabs x < e) by (apply QltT_to_Qlt; exact Hb).
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec x 0) as [Hx | Hx].
  - assert (Hx' : x <= 0) by (apply Qlt_le_weak; exact Hx).
    rewrite (Qabs_neg x Hx') in HbQ.
    rewrite <- (Qopp_involutive x).
    exact (Qopp_lt_compat (- x) e HbQ).
  - assert (H0 : (- e) < (- 0)) by (apply (Qopp_lt_compat 0 e HeQ)).
    assert (Hzq0 : (- 0)%Q == 0%Q)
      by (apply qeqT_imp_qeq; exact uabp7an_qneg0).
    rewrite Hzq0 in H0.
    exact (Qlt_le_trans (- e) 0 x H0 Hx).
Qed.

(* Pointwise tail auxiliary: QltT (- x) (eps/2) and QltT 0 eps give
   QltT (Qabs (Qabs x - x)) eps.
   Proof: decidable Q-order sign split; Qabs_pos/Qabs_neg locate the
   absolute value, and the core Q-layer step reduces to "weak non-negativity
   (per-eps lower bound) implies |a| == a". *)
Lemma uabp7an_pt_tail : forall x eps : Q,
  QltT 0 eps -> QltT (- x) (eps / 2) -> QltT (Qabs (Qabs x - x)) eps.
Proof.
  intros x eps Heps Hneg.
  assert (HepsQ : 0 < eps) by (apply QltT_to_Qlt; exact Heps).
  assert (HnegQ : - x < eps / 2) by (apply QltT_to_Qlt; exact Hneg).
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec x 0) as [Hx | Hx].
  - (* x < 0: |x| == -x, goal |-2x| == -2x < eps *)
    assert (Hx' : x <= 0) by (apply Qlt_le_weak; exact Hx).
    rewrite (Qabs_neg x Hx').
    assert (Hsp : (- x - x)%Q == (- (2 * x))%Q) by ring.
    rewrite Hsp.
    assert (H2xpos : 0 < - (2 * x)).
    { assert (Hlt2 : x + x < 0 + 0)
        by (apply (Qplus_lt_compat x 0 x 0); exact Hx).
      assert (Hz1 : (0 + 0)%Q == 0%Q) by ring.
      rewrite Hz1 in Hlt2.
      assert (Hz2 : (x + x)%Q == (2 * x)%Q) by ring.
      rewrite Hz2 in Hlt2.
      assert (H0 : (- 0)%Q < (- (2 * x)))
        by (apply (Qopp_lt_compat (2 * x) 0); exact Hlt2).
      assert (Hzq0 : (- 0)%Q == 0%Q)
        by (apply qeqT_imp_qeq; exact uabp7an_qneg0).
      rewrite Hzq0 in H0.
      exact H0. }
    rewrite (Qabs_pos (- (2 * x)) (Qlt_le_weak _ _ H2xpos)).
    assert (Hz3 : (- (2 * x))%Q == ((- x) + (- x))%Q) by ring.
    rewrite Hz3.
    assert (Hfin : (- x) + (- x) < eps / 2 + eps / 2)
      by (apply (Qplus_lt_compat (- x) (eps / 2) (- x) (eps / 2)); exact HnegQ).
    assert (HsumE : eps / 2 + eps / 2 == eps) by field.
    rewrite HsumE in Hfin.
    exact Hfin.
  - (* x >= 0: |x| == x, the difference collapses to zero *)
    rewrite (Qabs_pos x Hx).
    assert (Hzd : (x - x)%Q == 0%Q) by ring.
    rewrite Hzd.
    rewrite (Qabs_neg 0 (Qle_refl 0)).
    assert (Hzq0 : (- 0)%Q == 0%Q)
      by (apply qeqT_imp_qeq; exact uabp7an_qneg0).
    rewrite Hzq0.
    exact HepsQ.
Qed.

(* ============================================================ *)
(* II. Main piece: unconditional abs non-negativity on the       *)
(*     concrete layer (zero assumption slots beyond the          *)
(*     statement premise)                                        *)
(* ============================================================ *)

Lemma uabp7an_core : forall a : Real,
  real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a H. destruct a as [u Hu]. destruct H as [Hlt | Heq].
  - (* Strictly positive branch: the witness e locates Qabs_pos pointwise,
       the difference collapses to zero *)
    destruct Hlt as [e [He [N HN]]].
    unfold real_eq. intros eps Heps. exists N. intros n Hn.
    specialize (HN n Hn).
    change (QltT (Qabs (Qabs (u n) - u n)) eps).
    assert (HeQ : 0 < e) by (apply QltT_to_Qlt; exact He).
    assert (HNQ : e < u n - 0) by (apply QltT_to_Qlt; exact HN).
    assert (Hzq : (u n - 0)%Q == u n) by ring.
    rewrite Hzq in HNQ.
    assert (Hpos : 0 < u n) by exact (Qlt_trans 0 e (u n) HeQ HNQ).
    assert (Habs : Qabs (u n) == u n)
      by (apply Qabs_pos; apply Qlt_le_weak; exact Hpos).
    apply Qlt_to_QltT.
    assert (Hzd : (Qabs (u n) - u n)%Q == 0%Q) by (rewrite Habs; ring).
    rewrite Hzd.
    rewrite (Qabs_neg 0 (Qle_refl 0)).
    assert (Hzq0 : (- 0)%Q == 0%Q)
      by (apply qeqT_imp_qeq; exact uabp7an_qneg0).
    rewrite Hzq0.
    apply QltT_to_Qlt. exact Heps.
  - (* Weak branch real_eq: half-eps plus Qabs_triangle double allowance *)
    unfold real_eq. intros eps Heps.
    assert (Hhalf : QltT 0 (eps / 2))
      by (apply uabp7an_qlt_half; exact Heps).
    destruct (Heq (eps / 2)%Q Hhalf) as [N HN].
    exists N. intros n Hn. specialize (HN n Hn).
    change (QltT (Qabs (Qabs (u n) - u n)) eps).
    assert (HNQ : Qabs (0 - u n) < eps / 2) by (apply QltT_to_Qlt; exact HN).
    assert (Hzm : (0 - u n)%Q == (- u n)%Q) by ring.
    rewrite Hzm in HNQ.
    rewrite (Qabs_opp (u n)) in HNQ.
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (Qabs (u n) + Qabs (u n)) _).
    + assert (Hsp : (Qabs (u n) - u n)%Q
                    == (Qabs (u n) + (- u n))%Q) by ring.
      rewrite Hsp.
      apply (Qle_trans _ (Qabs (Qabs (u n)) + Qabs (- u n))).
      * apply Qabs_triangle.
      * rewrite (Qabs_pos (Qabs (u n)) (Qabs_nonneg (u n))).
        rewrite (Qabs_opp (u n)).
        apply Qle_refl.
    + assert (HsumE : eps / 2 + eps / 2 == eps)
        by (apply qeqT_imp_qeq; apply uabp7an_half_add).
      rewrite <- HsumE.
      exact (Qplus_lt_compat (Qabs (u n)) (eps / 2)
                             (Qabs (u n)) (eps / 2) HNQ HNQ).
Qed.

(* Interface-field statement forms (le/abs/req taken from the Instance
   RealEnhancedReal fields):                                                 *)
(* The unconditional "le zero a -> req (abs a) a" universal piece -- the      *)
(* interface field abs_pos covers only the strict premise lt zero a; this     *)
(* piece weakens that premise to le zero a.                                  *)
Lemma uabp7an_abs_nonneg_uncond : forall a : Real,
  le zero a -> req (abs a) a.
Proof. intros a H. exact (uabp7an_core a H). Qed.

(* ============================================================ *)
(* III. Bridge 1 (abstract interface layer): the unconditional    *)
(*   piece implies the interface per-eps abs_nonneg form (with    *)
(*   the le zero a premise).                                      *)
(*   Stated on the global Real carrier (the interface class in    *)
(*   this tree is unparameterized); derived from                  *)
(*   req_plus_le_lt_pos and the interface lt_le_iff/le_id_r.      *)
(* ============================================================ *)

Section Uabp7anUncondToEps.

Lemma uabp7an_uncond_to_eps : forall a : R,
  le zero a -> req (abs a) a ->
  forall eps : R, lt zero eps -> le zero (plus (abs a) eps).
Proof.
  intros a Hle Heq eps Heps.
  apply (lt_le_iff zero (plus (abs a) eps)). left.
  apply (req_plus_le_lt_pos (abs a) eps).
  - apply (le_id_r zero a (abs a) (req_sym (abs a) a Heq) Hle).
  - exact Heps.
Qed.

End Uabp7anUncondToEps.

(* ============================================================ *)
(* IV. Bridge 2 (concrete layer): the Bishop per-eps non-negativity  *)
(*   form implies the unconditional piece (reverse bridge).          *)
(*   Premise shape = the interface abs_nonneg field applied to a      *)
(*   itself (forall eps>0, le zero (a+eps)).                          *)
(*   Route: take the quarter-constant witness; extract the pointwise  *)
(*   lower bound (-a_n < eps/2) from each Or branch of real_le; then  *)
(*   close by the uabp7an_pt_tail sign split; the Q order is          *)
(*   decidable, zero classical logic.                                 *)
(* ============================================================ *)

Lemma uabp7an_eps_to_uncond : forall a : Real,
  (forall eps : Real, lt zero eps -> le zero (plus a eps)) ->
  req (abs a) a.
Proof.
  intros a Hbis. destruct a as [u Hu].
  assert (Hcore : real_eq (real_abs (existT (fun u : nat -> Q => cauchy u) u Hu)) (existT (fun u : nat -> Q => cauchy u) u Hu)).
  { intros eps Heps.
    assert (HepsQ : 0 < eps) by (apply QltT_to_Qlt; exact Heps).
    assert (Hhalf : QltT 0 (eps / 2))
      by (apply uabp7an_qlt_half; exact Heps).
    assert (Hq2 : 0 < eps / 2)
      by (apply QltT_to_Qlt; apply uabp7an_qlt_half; exact Heps).
    assert (Hq4 : 0 < eps / 4).
    { assert (Hz : eps / 4 == eps / 2 / 2) by field.
      rewrite Hz.
      apply QltT_to_Qlt. apply uabp7an_qlt_half. exact Hhalf. }
    assert (Hq4T : QltT 0 (eps / 4)) by (apply Qlt_to_QltT; exact Hq4).
    assert (Hq42 : eps / 4 < eps / 2)
      by (apply QltT_to_Qlt; apply uabp7an_q4_lt_q2; exact Heps).
    (* Strict-positivity witness of the quarter-constant real
       (real_lt construction, half of eps/4) *)
    assert (Hltc : lt zero (real_const (eps / 4))).
    { assert (Hltc2 : real_lt real_zero (real_const (eps / 4))).
      { unfold real_lt. exists (eps / 4 / 2)%Q. split.
        - apply uabp7an_qlt_half. exact Hq4T.
        - exists 0%nat. intros n _.
          apply uabp7an_half_lt_m0. exact Hq4T. }
      exact Hltc2. }
    destruct (Hbis (real_const (eps / 4)) Hltc) as [Hb | Hb].
    - (* inl strict branch: e1 < a_n + eps/4 gives -a_n < eps/2 *)
      unfold real_le in Hb. destruct Hb as [e1 [He1 [N1 HN1]]].
      exists N1. intros n Hn. specialize (HN1 n Hn).
      change (QltT (Qabs (Qabs (u n) - u n)) eps).
      assert (HN1Q : e1 < u n + eps / 4 - 0) by (apply QltT_to_Qlt; exact HN1).
      assert (Hzq : (u n + eps / 4 - 0)%Q
                    == (u n + eps / 4)%Q) by ring.
      rewrite Hzq in HN1Q.
      apply QltT_to_Qlt in He1.
      assert (Hpos2 : 0 < u n + eps / 4)
        by exact (Qlt_trans 0 e1 (u n + eps / 4) He1 HN1Q).
      assert (Hneg0 : - (u n + eps / 4) < 0).
      { assert (H0 : - (u n + eps / 4) < (- 0))
          by (apply (Qopp_lt_compat 0 (u n + eps / 4)); exact Hpos2).
        assert (Hzq0 : (- 0)%Q == 0%Q)
          by (apply qeqT_imp_qeq; exact uabp7an_qneg0).
        rewrite Hzq0 in H0. exact H0. }
      assert (Hs : eps / 4 + -(u n + eps / 4) < eps / 4 + 0)
        by (apply (proj2 (Qplus_lt_r (- (u n + eps / 4)) 0 (eps / 4)));
            exact Hneg0).
      assert (Hzs : (eps / 4 + -(u n + eps / 4))%Q
                    == (- u n)%Q) by ring.
      rewrite Hzs in Hs.
      assert (Hzs2 : (eps / 4 + 0)%Q == (eps / 4)%Q) by ring.
      rewrite Hzs2 in Hs.
      assert (Hneg : - u n < eps / 2)
        by exact (Qlt_trans (- u n) (eps / 4) (eps / 2) Hs Hq42).
      apply (uabp7an_pt_tail (u n) eps Heps).
      apply Qlt_to_QltT. exact Hneg.
    - (* inr equality branch: |a_n + eps/4| < eps/4, lower-bound flip,
         then -a_n < eps/2 *)
      unfold real_eq in Hb.
      destruct (Hb (eps / 4)%Q Hq4T) as [N2 HN2].
      exists N2. intros n Hn. specialize (HN2 n Hn).
      change (QltT (Qabs (Qabs (u n) - u n)) eps).
      assert (HN2Q : Qabs (0 - (u n + eps / 4)) < eps / 4)
        by (apply QltT_to_Qlt; exact HN2).
      assert (Hsp0 : (0 - (u n + eps / 4))%Q
                     == (-(u n + eps / 4))%Q) by ring.
      rewrite Hsp0 in HN2Q.
      rewrite (Qabs_opp (u n + eps / 4)) in HN2Q.
      assert (HN2QT : QltT (Qabs (u n + eps / 4)) (eps / 4))
        by (apply Qlt_to_QltT; exact HN2Q).
      assert (Hlb : - (eps / 4) < u n + eps / 4)
        by (apply QltT_to_Qlt;
            exact (uabp7an_abs_lb (u n + eps / 4) (eps / 4) Hq4T HN2QT)).
      assert (Hs : -(eps / 4) + -(eps / 4) < -(eps / 4) + (u n + eps / 4))
        by (apply (proj2 (Qplus_lt_r (- (eps / 4)) (u n + eps / 4) (- (eps / 4))));
            exact Hlb).
      assert (Hs1 : (-(eps / 4) + -(eps / 4))%Q == (-(eps / 2))%Q) by field.
      rewrite Hs1 in Hs.
      assert (Hs2 : (-(eps / 4) + (u n + eps / 4))%Q
                    == u n) by ring.
      rewrite Hs2 in Hs.
      assert (Hneg : - u n < eps / 2).
      { assert (H0 : - u n < - (-(eps / 2)))
          by (apply (Qopp_lt_compat (-(eps / 2)) (u n)); exact Hs).
        rewrite Qopp_involutive in H0.
        exact H0. }
      apply (uabp7an_pt_tail (u n) eps Heps).
      apply Qlt_to_QltT. exact Hneg. }
  exact Hcore.
Qed.

(* ============================================================ *)
(* V. Assumption-closure audit (Print Assumptions; each piece     *)
(*    must be Closed)                                             *)
(* ============================================================ *)

Print Assumptions uabp7an_qneg0.
Print Assumptions uabp7an_qlt_half.
Print Assumptions uabp7an_half_add.
Print Assumptions uabp7an_half_lt.
Print Assumptions uabp7an_half_le.
Print Assumptions uabp7an_q4_lt_q2.
Print Assumptions uabp7an_half_lt_m0.
Print Assumptions uabp7an_abs_lb.
Print Assumptions uabp7an_pt_tail.
Print Assumptions uabp7an_core.
Print Assumptions uabp7an_abs_nonneg_uncond.
Print Assumptions uabp7an_uncond_to_eps.
Print Assumptions uabp7an_eps_to_uncond.
