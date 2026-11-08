(* ConstructiveWorld-Set -- strict positivity of the Pade approximant denominators. *)

(** * DenPosGeneral: strict positivity of the Pade denominator [pade_den] on [0, 2).

    Mission.  For the Pade approximant denominators this file carries the
      first-pair comparison [dpg_g1_lt_g0] (the g0 < g1 core), the main
      strict positivity statement [dpg_den_pos_strict] (1 <= n, 0 <= x < 2
      give [QltT 0 (pade_den n x)]), its transpose [dpg_den_pos_strict_T]
      with the nonnegativity premise in [QleT] form, the unit-interval
      corollary [dpg_den_pos_strict_le1], and the vm_compute numeric
      anchors [dpg_den2_one] and [dpg_den3_quarter].

    Dependencies.  [CW_ConstructiveWorld_219], [UpReqPadeExp],
      [UpReqPadeDenPos], [UpReqAltSumPos], [PadeDenPosB12]; Stdlib
      [QArith], [Arith], [Lia], [Setoid].

    References.  Positivity lemmas for denominator polynomials in Pade
      approximation theory, a standard component of Beukers/Apery-type
      irrationality proofs; this development, DenPosGeneral.v, the
      baseline module in ConstructiveWorld-Main whose statement names
      are carried over here verbatim; interface note: the [pdp_coeff_ratio] rewrite and the [pdp_den_altsum] / [qeq_ltT] passage ride the [QeqT] face of the new interface generation via [qeqT_imp_qeq] / [qeq_imp_qeqT] (UpReqPadeDenPos.v, S02_CauchyComplete.v; call-form precedent PadeDenPosB12.v), statement names untouched.

    Constructivity.  All named statements close by [Qed]; no classical
      logic; the statement face is [Set]-carried with zero [Prop]
      leakage; statements extract with [Obj.magic] = 0 and no erasure.

    Build.  [coqc -native-compiler no -q -Q . "" DenPosGeneral.v] compiles
      cleanly (exit 0); the artifact starts with [436f7121 000160bc]. *)
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
Require Import UpReqPadeExp UpReqPadeDenPos UpReqAltSumPos.
Require Import PadeDenPosB12.
From Stdlib Require Import QArith.QArith Arith.Arith Lia.
From Stdlib Require Import Setoid.

(* ===== part 1: the strict first pair -- x < 2 <= R_{n,0} implies       *)
(* ===== g(1) < g(0), for all n >= 1.                                   ===== *)
(*   pdq_g1_lt_g0 (DenPos12:183) carries the premise QltT 1 x and covers  *)
(*   only the segment (1, 2); this part generalizes to the whole segment  *)
(*   [0, 2) -- the strict-tier gap of the low segment [0, 1] sits exactly *)
(*   in this part.                                                        *)

Lemma dpg_g1_lt_g0 : forall (n : nat) (x : Q),
  (1 <= n)%nat -> QltT x 2%Q ->
  QltT (pdp_g n x 1%nat) (pdp_g n x 0%nat).
Proof.
  intros n x Hn Hhi.
  assert (Hk : (0 < n)%nat) by lia.
  assert (E0 : (0 <=? n)%nat = true) by (apply Nat.leb_le; lia).
  assert (E1 : (1 <=? n)%nat = true) by (apply Nat.leb_le; lia).
  unfold pdp_g. rewrite E1, E0. cbn [q_pow].
  apply Qlt_to_QltT.
  repeat rewrite Qmult_1_r.
  rewrite (qeqT_imp_qeq _ _ (pdp_coeff_ratio n 0%nat Hk)).
  assert (Hc : x * pade_coeff n (Datatypes.S 0)
               < pdp_R n 0 * pade_coeff n (Datatypes.S 0)).
  { apply (Qmult_lt_compat_r x (pdp_R n 0) (pade_coeff n (Datatypes.S 0))).
    - apply QltT_to_Qlt. apply pdp_coeff_pos_any.
    - apply (Qlt_le_trans x 2%Q (pdp_R n 0)).
      + apply QltT_to_Qlt. exact Hhi.
      + apply QleT'_to_Qle. apply pdpb_R_ge_2. exact Hk. }
  rewrite (Qmult_comm (pade_coeff n (Datatypes.S 0)) x).
  rewrite (Qmult_comm (pade_coeff n (Datatypes.S 0)) (pdp_R n 0)).
  exact Hc.
Qed.

(* ===== part 2 (main part, strict; fills the gap left inside the        *)
(* ===== library): 0 <= x < 2 and n >= 1 imply 0 < Q_n(x).             ===== *)
(*   skeleton as in pdpb_den_pos_le2 (B12:141); the decay step reuses     *)
(*   pdpb_term_decay (its x <= 2 face), the first-pair step swaps in      *)
(*   part 1, and altsum_pos_strict yields QltT directly.                  *)

Theorem dpg_den_pos_strict : forall (n : nat) (x : Q),
  (1 <= n)%nat -> QleT' 0 x -> QltT x 2%Q -> QltT 0 (pade_den n x).
Proof.
  intros n x Hn Hx Hhi.
  assert (Hb : QeqT (pade_den n x) (altsum (pdp_g n x) (Datatypes.S n)))
    by apply pdp_den_altsum.
  apply (qeq_ltT (altsum (pdp_g n x) (Datatypes.S n)) (pade_den n x)).
  - apply qeq_imp_qeqT. apply Qeq_sym. apply qeqT_imp_qeq. exact Hb.
  - apply altsum_pos_strict.
    + intro k. apply pdp_g_nonneg. exact Hx.
    + intro k. destruct (Nat.leb (Datatypes.S k) n) eqn:E.
      * apply (pdpb_term_decay n k x).
        -- apply Nat.leb_le in E. lia.
        -- exact Hx.
        -- apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt. exact Hhi.
      * apply (pdp_g_decay_hi n x k).
        -- exact Hx.
        -- apply Nat.leb_gt in E. lia.
    + apply (dpg_g1_lt_g0 n x Hn Hhi).
    + lia.
Qed.

(* ===== part 3: adaptation of the premise face to the or-form QleT       *)
(* ===== (same slot as pdpb_den_pos_le2_T).                             ===== *)

Theorem dpg_den_pos_strict_T : forall (n : nat) (x : Q),
  (1 <= n)%nat -> QleT 0 x -> QltT x 2%Q -> QltT 0 (pade_den n x).
Proof.
  intros n x Hn Hx Hhi.
  apply dpg_den_pos_strict.
  - exact Hn.
  - apply altsum_QleT_to_QleT'. exact Hx.
  - exact Hhi.
Qed.

(* ===== part 4: immediate corollary, strict version on the main segment  *)
(*   [0, 1] (premises in the same slots as the statement face of          *)
(*   pdp_den_pos, conclusion lifted to QltT -- the strict realization of  *)
(*   the 0 <= x segment)                                                ===== *)

Corollary dpg_den_pos_strict_le1 : forall (n : nat) (x : Q),
  (1 <= n)%nat -> QleT 0 x -> QleT x 1 -> QltT 0 (pade_den n x).
Proof.
  intros n x Hn Hx Hx1.
  apply dpg_den_pos_strict_T.
  - exact Hn.
  - exact Hx.
  - (* goal taken in the strict QltT x 2 form; QleT' x 1 and 1 < 2        *)
    (* turn strict via Qle_lt_trans                                       *)
    apply Qlt_to_QltT.
    apply (Qle_lt_trans x 1 2).
    + apply QleT'_to_Qle. apply altsum_QleT_to_QleT'. exact Hx1.
    + unfold Qlt. simpl. lia.
Qed.

(* ===== part 5: low-segment strict vm_compute anchors (contrast:        *)
(*   pdp_den2_one / pdp_den3_one @UpReqPadeDenPos.v:517/520 carry the     *)
(*   QleT' face only).                                                  ===== *)

Lemma dpg_den2_one : QltT 0 (pade_den 2%nat 1%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma dpg_den3_quarter : QltT 0 (pade_den 3%nat (1#4)%Q).
Proof. vm_compute. reflexivity. Qed.

(* ===== exit audit of the exported parts: all Closed (evidence in the   *)
(* ===== build log).                                                    ===== *)

Print Assumptions dpg_den_pos_strict.
Print Assumptions dpg_den_pos_strict_T.
Print Assumptions dpg_den_pos_strict_le1.
