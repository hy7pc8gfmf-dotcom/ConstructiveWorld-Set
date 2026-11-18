(* ConstructiveWorld-Set -- batch supply of Q-layer Archimedean/geometric bounds for the four sc_* use sites. *)

(** * UpAblArchGeomBatch: Q-side Archimedean bounds and their instantiation corollaries.

    Mission.  The Q-layer bridge lemmas [qbg_mult_inv] ([Qinv x == 1 / x]),
      [qbg_lt_eq_compat_r]/[qbg_ltT_eq_compat_r] (right Qeq rewriting under
      [Qlt]/[QltT]), the positivity lemmas [qbg_div_pos]/[qbg_Qinv_pos], and
      the main supply corollary [qbg_arch_geom_direct] (for all [B : Q] there
      is [N] with [(1+1)*B <= (t+1)#1] whenever [N <= t], matching the shape
      of [q_arch_geom]); the instantiation corollaries
      [qag_arch_geom_cos_cauchy], [qag_arch_geom_cs_sq],
      [qag_arch_geom_add_sin], [qag_arch_geom_add_cos] for the four host use
      sites.

    Dependencies.  The library modules listed in the in-file Require
      declarations: Stdlib [List], [Lia], [Lqa],
      [QArith.QArith]/[Qabs]/[Qring]; [S01_BaseRing] through
      [S15_TailFEPUp] and [UpAblAbsSumLeB2] of this development.

    References.  This development, UpAblArchGeomBatch.v, statement names
      carried over verbatim from the baseline module in
      ConstructiveWorld-Main.

    Constructivity.  All statements close by [Qed] with no admitted goals
      and no classical logic; statements are carried at the [Set] layer with
      zero [Prop] leakage; [Print Assumptions] reports Closed throughout.

    Build.  [coqc -native-compiler no -q -Q . "" UpAblArchGeomBatch.v] under
      Rocq 9.1; the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
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
Require Import UpAblAbsSumLeB2.

(* ================= Section 1: the qbg_mult_inv family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.

(* Section 0: signature audit of the library symbols (a mismatch fails at compile time) *)

Check QltT. Check QleT'.
Check QltT_to_Qlt. Check Qlt_to_QltT. Check Qle_to_QleT'.
Check qltT_eq_compat_l. Check qeq_le.
Check Qlt_le_dec. Check Qlt_le_weak. Check Qlt_le_trans.
Check Qinv. Check Qinv_lt_contravar. Check Qmult_1_l.
Check Qmult_lt_0_compat. Check Qmult_le_compat_r. Check Q2_pos. Check Q2_nonneg.
Check Qle_of_nat.
Check uabS4b_arch_N. Check uabS4b_null_lt.
Check q_arch_geom.

(* Section A: the two bridging lemmas (supplying the missing right Qeq rewriting and Qmult_inv) *)

(* A1: the Qmult_inv bridging lemma: names the Qinv-Qdiv relation (Qdiv x y unfolds to x * Qinv y, *)
(*      named by Qmult_1_l; this sidesteps the definitional rewrite blocked by the match in Qinv) *)
Lemma qbg_mult_inv : forall x : Q, Qinv x == 1 / x.
Proof.
  intro x. unfold Qdiv. symmetry. apply Qmult_1_l.
Qed.

(* A2: right Qeq rewriting on the Qlt base: rewriting the right Qeq operand passes freely in Qlt *)
Lemma qbg_lt_eq_compat_r : forall a x y : Q, x == y -> a < x -> a < y.
Proof.
  intros a x y Hxy Hlt. rewrite <- Hxy. exact Hlt.
Qed.

(* A3: right Qeq rewriting on the QltT Set base: dual to the leftward S02 lemma qltT_eq_compat_l *)
Lemma qbg_ltT_eq_compat_r : forall a x y : Q, x == y -> QltT a x -> QltT a y.
Proof.
  intros a x y Hxy H.
  apply Qlt_to_QltT.
  apply (qbg_lt_eq_compat_r a x y Hxy).
  apply QltT_to_Qlt.
  exact H.
Qed.

(* Section B: Qinv positivity lemmas (from the Qdiv form to the Qinv form; exit at the Set layer) *)

(* B1: Qdiv positivity: 0 < c implies 0 < 1/c (retraces the S02 q_arch_inv_pos step without the nat detour) *)
Lemma qbg_div_pos : forall c : Q, Qlt 0 c -> Qlt 0 (1 / c).
Proof.
  intro c. intro Hc.
  apply Qlt_shift_div_l; [ | ].
  - exact Hc.
  - setoid_replace (0 * c) with 0%Q by ring.
    unfold Qlt. exact Z.lt_0_1.
Qed.

(* B2: Qinv positivity at the Set layer: 0 <T x implies 0 <T Qinv x -- the entry point feeding Qfloor *)
Lemma qbg_Qinv_pos : forall x : Q, QltT 0 x -> QltT 0 (Qinv x).
Proof.
  intros x Hx.
  apply Qlt_to_QltT.
  rewrite (qbg_mult_inv x).
  apply qbg_div_pos. apply QltT_to_Qlt. exact Hx.
Qed.

(* main piece: the supply Corollary for the q_arch_geom call sites, one shape for all five instances *)
(* (template: sc_sin_partial_cauchy_bounded). *)
(* the statement is verbatim in the shape of q_arch_geom of S03_QExp (sigT/NatLe/QleT', all at the Set layer). *)
(* witness replacement: the opaque Qarchimedean index is replaced by a Qfloor index *)
(*   N := uabS4b_arch_N (Qinv (2B)); premise chain: uabS4b_null_lt (Qinv positivity *)
(*   supplied by lemma B2) gives 1#(Pos.of_succ_nat N) < Qinv 2B; lemma A1 plus the *)
(*   A2 right rewrite carry it into the Qdiv form, 1/(N+1) < 1/2B; the harmonic *)
(*   inversion proj2 of Qinv_lt_contravar turns it into 2B < (N+1)#1; monotonicity *)
(*   of Qle_of_nat closes 2B <= (t+1)#1. *)
Corollary qbg_arch_geom_direct : forall B : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intro B.
  destruct (Qlt_le_dec 0 B) as [Hpos | Hle].
  - (* case 0 < B: the Qfloor harmonic inversion supplies the index *)
    assert (Htwo : Qlt 0 ((1 + 1)%Q * B)).
    { apply (Qmult_lt_0_compat (1 + 1)%Q B);
      [apply QltT_to_Qlt; apply Q2_pos | exact Hpos]. }
    assert (HtwoT : QltT 0 ((1 + 1)%Q * B)) by (apply Qlt_to_QltT; exact Htwo).
    assert (Hinvpos : QltT 0 (Qinv ((1 + 1)%Q * B)))
      by (apply qbg_Qinv_pos; exact HtwoT).
    pose proof (uabS4b_null_lt (Qinv ((1 + 1)%Q * B)) Hinvpos) as Hfloor.
    pose proof (QltT_to_Qlt _ _ Hfloor) as HfloorP.
    assert (Hc1 : Qlt 0 (Z.of_nat (Datatypes.S (uabS4b_arch_N (Qinv ((1 + 1)%Q * B)))) # 1))
      by (unfold Qlt; cbn [Qnum Qden]; rewrite !Z.mul_1_r;
          change (Z.of_nat (Datatypes.S (uabS4b_arch_N (Qinv ((1 + 1)%Q * B)))))
            with (Z.pos (Pos.of_succ_nat (uabS4b_arch_N (Qinv ((1 + 1)%Q * B)))));
          exact (Pos2Z.is_pos _)).
    assert (Hkey : Qlt ((1 + 1)%Q * B)
                     (Z.of_nat (Datatypes.S (uabS4b_arch_N (Qinv ((1 + 1)%Q * B)))) # 1)).
    { apply (proj2 (Qinv_lt_contravar ((1 + 1)%Q * B)
              (Z.of_nat (Datatypes.S (uabS4b_arch_N (Qinv ((1 + 1)%Q * B)))) # 1)
              Htwo Hc1)).
      (* the left premise 1#(Pos.of_succ_nat N) is definitionally the same as 1/((N+1)#1) *)
      (* (canonical Qinv form: Zpos(QDen x)#p == 1#p), so no rewrite is needed to close; *)
      (* the Qdiv-side rewrite was already done by lemma A1 inside lemma B2 *)
      exact HfloorP. }
    exists (uabS4b_arch_N (Qinv ((1 + 1)%Q * B))).
    intros t Ht.
    apply Qle_to_QleT'.
    apply Qlt_le_weak.
    apply (Qlt_le_trans _ (Z.of_nat (Datatypes.S (uabS4b_arch_N (Qinv ((1 + 1)%Q * B)))) # 1) _).
    + exact Hkey.
    + apply QleT'_to_Qle. apply Qle_of_nat. apply NatLe_drop in Ht.
      rewrite PeanoNat.Nat.add_1_r.
      exact (proj1 (PeanoNat.Nat.succ_le_mono _ _) Ht).
  - (* case B <= 0: the trivial continuation N := 0 *)
    exists 0%nat.
    intros t Ht.
    apply Qle_to_QleT'.
    (* two steps: (1+1)*B <= 0 and 0 <= (t+1)#1 *)
    apply (Qle_trans _ 0 _).
    + (* (1+1)*B <= 0: via B*(1+1) <= 0*(1+1) == 0 (reordering by ring + monotonicity of right multiplication) *)
      apply (Qle_trans _ (0 * (1 + 1)%Q) _).
      * setoid_replace (Qmult (1 + 1)%Q B) with (B * (1 + 1)%Q) by ring.
        apply (Qmult_le_compat_r B 0 (1 + 1)%Q).
        -- exact Hle.
        -- apply QleT'_to_Qle. apply Q2_nonneg.
      * apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. ring.
    + (* 0 <= (t+1)#1: after unfold a literal Z comparison; nonnegativity of the nat-to-Z image closes directly *)
      unfold Qle. cbn [Qnum Qden]. rewrite !Z.mul_1_r.
      rewrite PeanoNat.Nat.add_1_r.
      change (Z.of_nat (Datatypes.S t)) with (Z.pos (Pos.of_succ_nat t)).
      exact (Pos2Z.is_nonneg (Pos.of_succ_nat t)).
Qed.

(* assumption audit: Print Assumptions reports Closed for each item below (no external unproved premises) *)

Print Assumptions qbg_mult_inv.
Print Assumptions qbg_lt_eq_compat_r.
Print Assumptions qbg_ltT_eq_compat_r.
Print Assumptions qbg_div_pos.
Print Assumptions qbg_Qinv_pos.
Print Assumptions qbg_arch_geom_direct.
(* ================= Section 2: the qag_arch_geom_cos_cauchy family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.

(* Section 0: dependency signature audit (identifier drift would surface at compile time) *)

Check qbg_arch_geom_direct.
Check q_arch_geom.
Check sigT.
Check NatLe. Check NatLe_lift. Check NatLe_drop.
Check QleT'. Check Qle_to_QleT'.

(* Section A1: the use site corresponding to sc_cos_partial_cauchy_bounded *)

Corollary qag_arch_geom_cos_cauchy : forall B : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intro B.
  destruct (qbg_arch_geom_direct B) as [N HN].
  exists N. intros t Ht. exact (HN t Ht).
Qed.

(* Section A2: the use site corresponding to sc_cs_sq_err_bound *)

Corollary qag_arch_geom_cs_sq : forall B : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intro B.
  destruct (qbg_arch_geom_direct B) as [N HN].
  exists N. intros t Ht. exact (HN t Ht).
Qed.

(* Section A3: the use site corresponding to sc_add_sin_err_bound *)

Corollary qag_arch_geom_add_sin : forall B : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intro B.
  destruct (qbg_arch_geom_direct B) as [N HN].
  exists N. intros t Ht. exact (HN t Ht).
Qed.

(* Section A4: the use site corresponding to sc_add_cos_err_bound *)

Corollary qag_arch_geom_add_cos : forall B : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intro B.
  destruct (qbg_arch_geom_direct B) as [N HN].
  exists N. intros t Ht. exact (HN t Ht).
Qed.

(* assumption audit: Print Assumptions reports Closed for all four items *)

Print Assumptions qag_arch_geom_cos_cauchy.
Print Assumptions qag_arch_geom_cs_sq.
Print Assumptions qag_arch_geom_add_sin.
Print Assumptions qag_arch_geom_add_cos.
