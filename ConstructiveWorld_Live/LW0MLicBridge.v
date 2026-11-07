(* ConstructiveWorld-Set — Cauchy-completeness adapters for the pi Leibniz partial-sum sequence. *)

(** * LW0MLicBridge: three adapter members for the pi Leibniz
       partial-sum sequence.

    Mission.  Cauchy-completeness adaptation of the pi Leibniz
    partial-sum sequence [lp_four * lp_odd]: the tail-controlled
    instance [lw0m_tail_bounded_pi] ([lic_tail_bounded]), the
    vanishing-window instance [lw0m_vanish_pi] ([lic_vanish]), and the
    metric congruence member [lw0m_metric_congr] ([real_metric]
    invariant under left-argument [real_eq] substitution), sharing the
    uniform window [lw0m_e n := 5 * pie_mag n].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Lia],
    [Lqa]; development members itemized in the provenance block below.

    References.  This development, LW0MLicBridge.v, the baseline
    module in ConstructiveWorld-Main whose statement names are carried
    over here verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].  The statement face is
      Set-carried, zero Prop leakage; the in-proof Prop scaffolding
      crosses the three bridges, so the conclusion face stays Set.

    Build.  [coqc -native-compiler no -q -Q . "" LW0MLicBridge.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia Lqa.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import UpReqIrrationalCriterion.

(* ============================================================ *)
(* Dependency provenance.  [S02_CauchyComplete]: [real_eq], [QltT],     *)
(* [Real], [real_plus], [real_opp], [QltT_to_Qlt], [Qlt_to_QltT],       *)
(* [QleT'_to_Qle], [qeqT_imp_qeq].  [S03_QExp]: [real_metric],          *)
(* [real_abs], [q_abs_abs_triangle].  [S10_KVQuantTrig]: [lp_four],     *)
(* [lp_odd].  [PiEnvelope]: [pie_tail4], [pie_modulus],                 *)
(* [pie_modulus_bound], [pie_v_eq], [pie_mag_pos], [pie_mag_antitone].  *)
(* [UpReqIrrationalCriterion]: [lic_tail_bounded], [lic_vanish].        *)
(* Naming: the [lw0m_] prefix has zero occupancy across the tree.  The  *)
(* pi projection sequence is [lw0m_xL n := lp_four * lp_odd n]; the     *)
(* in-proof Prop facts ([Qlt]/[Qle]/[Qeq]) cross through                *)
(* [QltT_to_Qlt]/[QleT'_to_Qle]/[qeqT_imp_qeq]; both lic interfaces and *)
(* [real_eq] are Set-valued.                                            *)
(* ============================================================ *)

(* ============================================================ *)
(* Section 0. The uniform window and the pi projection sequence.        *)
(* ============================================================ *)

(* Uniform window: e n := 5 * pie_mag n (shared by the three members; the
   factor 5 absorbs the two index lifts). *)
Definition lw0m_e (n : nat) : Q := 5 * pie_mag n.

(* Pi projection sequence: xL n := lp_four * lp_odd n. *)
Definition lw0m_xL (n : nat) : Q := lp_four * lp_odd n.

(* ============================================================ *)
(* Section 1. The tail-control bridge.                                  *)
(* The non-strict Qle of pie_tail4 plus a margin of 1 * pie_mag gives   *)
(* the strict QltT; the index lift pie_mag(2n+2) <= pie_mag n is        *)
(* pie_mag_antitone; the sequence seam pie_v_eq rewrites                *)
(* lp_four * lp_odd into 4 * pie_partial (2 * +2).                      *)
(* ============================================================ *)
Definition lw0m_tail_bounded_pi : lic_tail_bounded lw0m_xL lw0m_e.
Proof.
  intros n k Hn1 Hnk.
  unfold lw0m_xL, lw0m_e.
  apply Qlt_to_QltT.
  assert (Hanti : QleT' (pie_mag (2 * n + 2)) (pie_mag n))
    by (apply pie_mag_antitone; lia).
  pose proof (QleT'_to_Qle _ _ Hanti) as HantiQ.
  pose proof (QltT_to_Qlt _ _ (pie_mag_pos n)) as Hpm.
  apply (Qle_lt_trans _ (4 * pie_mag (2 * n + 2)) _).
  - rewrite (qeqT_imp_qeq _ _ (pie_v_eq k)).
    rewrite (qeqT_imp_qeq _ _ (pie_v_eq n)).
    apply QleT'_to_Qle. apply (pie_tail4 (2 * n + 2) (2 * k + 2)). lia.
  - lra.
Qed.

(* ============================================================ *)
(* Section 2. The vanishing-window bridge.                              *)
(* The modulus is recalibrated as N := pie_modulus (eps / 10)           *)
(* (pie_modulus is naturally paired with the factor-4 window, while the *)
(* lic window has factor 5); the point bound lifts to the eventual      *)
(* bound via pie_mag_antitone; one converter in each direction between  *)
(* QltT and Qlt (premise converted in, conclusion converted out).       *)
(* ============================================================ *)
Definition lw0m_vanish_pi : lic_vanish lw0m_e.
Proof.
  intros eps Heps.
  pose proof (QltT_to_Qlt 0%Q eps Heps) as Heps0.
  assert (Hd10 : Qlt 0 (eps * (1 # 10))) by lra.
  pose proof (pie_modulus_bound (eps * (1 # 10)) Hd10) as HbT.
  pose proof (QltT_to_Qlt _ _ HbT) as Hb.
  exists (pie_modulus (eps * (1 # 10))).
  intros n Hn.
  unfold lw0m_e.
  apply Qlt_to_QltT.
  assert (Hanti : QleT' (pie_mag n)
                      (pie_mag (pie_modulus (eps * (1 # 10)))))
    by (apply pie_mag_antitone; exact Hn).
  pose proof (QleT'_to_Qle _ _ Hanti) as HantiQ.
  lra.
Qed.

(* ============================================================ *)
(* Section 3. The real_metric congruence member.                        *)
(* Constructed eps by eps: the inverse triangle q_abs_abs_triangle      *)
(* gives the bound in one step; the projections unfold definitionally,  *)
(* real_metric := real_abs (real_plus x (real_opp z)), where            *)
(* real_plus/real_opp/real_abs are transparent Defined.                 *)
(* ============================================================ *)
Lemma lw0m_metric_congr : forall (x y z : Real), real_eq x y ->
  real_eq (real_metric x z) (real_metric y z).
Proof.
  intros x y z Hxy.
  destruct x as [u Hu]. destruct y as [v Hv]. destruct z as [w Hw].
  intros eps Heps.
  destruct (Hxy eps Heps) as [N HN].
  exists N. intros n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (u n - v n)) _).
  - cbv beta iota delta [real_metric real_abs real_plus real_opp].
    assert (Hr : (u n - v n == u n - w n - (v n - w n))%Q) by ring.
    rewrite Hr.
    apply QleT'_to_Qle. apply q_abs_abs_triangle.
  - apply QltT_to_Qlt. exact (HN n Hn).
Qed.
