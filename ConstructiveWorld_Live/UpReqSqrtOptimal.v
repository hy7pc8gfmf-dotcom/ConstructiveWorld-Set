(* ========================================================================== *)
(*  UpReqSqrtOptimal.v -- optimality of the square-root iteration step        *)
(* ========================================================================== *)
(*  Mission. The optimality ledger of the (x + 1/2)/s descent step: the       *)
(*    one-le-sqrt characterization family, the sqrt-side transfer family,     *)
(*    the absorption chain with its optimal constant (sqo_absorb_half_le,     *)
(*    sqo_absorb_general, sqo_chain_bound, sqo_absorb_breaks,                 *)
(*    sqo_plus1_optimal, sqo_plus1_margin), the piecewise exact form          *)
(*    (sqo_piecewise) and the decidable threshold split                       *)
(*    (sqo_plus1_threshold_dec); 22 stations, names carried over verbatim.    *)
(*  Dependencies. Stdlib QArith (QArith, Qring), Lia, Lqa, Setoid; the tree   *)
(*    carriers S01_BaseRing (Id/And/Not over Empty_set) and                   *)
(*    S02_CauchyComplete (QltT/QleT'/QeqT with the registered bridges         *)
(*    QltT_to_Qlt, Qlt_to_QltT, QleT'_to_Qle, Qle_to_QleT', qeq_imp_qeqT,     *)
(*    qeqT_imp_qeq, qeq_imp_qle), consumed read-only. No other Require.       *)
(*  References. Baseline module UpReqSqrtOptimal.v of ConstructiveWorld_Live  *)
(*    (census 22=22 ordered identity); the optimal-constant analysis of the   *)
(*    descent iteration (x+1/2)/s with its Newton comparison face; the        *)
(*    PROPCLEAN recipe book statement-face formula table P1 and bridge        *)
(*    table B (recipe card 1484).                                             *)
(*  Constructivity. All 22 statement faces are Set-carried: strict and weak   *)
(*    order and equality on Q ride the boolean Id witnesses QltT/QleT'/QeqT,  *)
(*    conjunction and negation ride the Set products And and Not              *)
(*    (S01_BaseRing), the threshold split keeps its sumbool bracket form.     *)
(*    Axiom-free; all proofs close with Qed; Print Assumptions must report    *)
(*    Closed under the global context and bare extraction yields no           *)
(*    Obj.magic.                                                              *)
(*  Build. rocq c -native-compiler no -q -Q . "" (Rocq 9.1.0; single -Q root  *)
(*    with an empty logical prefix over the S-tree world directory).          *)
(* ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qring.
From Stdlib Require Import Lia Lqa Setoid.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.

Open Scope Q_scope.

(* ############ Section 0: Q bridge lemmas (Set-carried) ############ *)

(* QeqT -> QleT' bridge (statement type identical to the registered
   qeq_imp_qle, S02:161 -- direct certificate supply, B9 form). *)
Lemma sqo_qeq_le : forall x y : Q, QeqT x y -> QleT' x y.
Proof.
  intros x y H. exact (qeq_imp_qle x y H).
Qed.

(* Pitfall note: Q_scope <> lands on plain eq (not (@eq Q s 0)) and does not
   rule out the 0#ds-style representations -- Q-side disequality must be
   carried explicitly. Set-carried form: Not over QeqT (S01_BaseRing,
   Not := A -> Empty_set), premise in QltT form. *)
Lemma sqo_neq0_of_lt : forall s : Q, QltT 0 s -> Not (QeqT s 0).
Proof.
  intros s Hps Heq.
  assert (HpsQ : 0 < s) by (apply QltT_to_Qlt; exact Hps).
  assert (HeqQ : s == 0) by (apply qeqT_imp_qeq; exact Heq).
  exfalso.
  apply (Qlt_irrefl 0).
  apply (Qlt_le_trans 0 s 0).
  - exact HpsQ.
  - apply QleT'_to_Qle. apply sqo_qeq_le. exact Heq.
Qed.

(* Involutive self-multiplication identity: s * / s == 1 (QeqT meaning
   s <> 0; Zpos/Zneg branches one Pos2Z.inj_mul hop + ring; the Z0 branch
   consumes the premise contradiction -- Empty_set elimination). *)
Lemma sqo_mul_inv : forall s : Q, Not (QeqT s 0) -> QeqT (s * / s) 1.
Proof.
  intros [ns ds] Hne.
  destruct ns as [|p|p].
  - exfalso.
    assert (Hs0 : (0 # ds) == 0) by (unfold Qeq; reflexivity).
    destruct (Hne (qeq_imp_qeqT _ _ Hs0)).
  - apply qeq_imp_qeqT. unfold Qeq. cbn. repeat rewrite Pos2Z.inj_mul. ring.
  - apply qeq_imp_qeqT. unfold Qeq. cbn. repeat rewrite Pos2Z.inj_mul. ring.
Qed.

(* The sqrt(d) >= 1 implies inv(sqrt(d)) <= 1 lemma (monotone scaling by /s
   + self-multiplication cancellation; not component-wise). *)
Lemma sqo_inv_sqrt_le_one : forall s : Q, QleT' 1 s -> QleT' (/ s) 1.
Proof.
  intros s H.
  apply Qle_to_QleT'.
  assert (Hle1 : 1 <= s) by (apply QleT'_to_Qle; exact H).
  assert (Hps : 0 < s) by lra.
  assert (Hle0 : 0 <= / s) by (apply Qinv_le_0_compat; lra).
  assert (Hle : 1 * / s <= s * / s).
  { apply (Qmult_le_compat_r 1 s (/ s)); [exact Hle1 | exact Hle0]. }
  assert (Hcancel : s * / s == 1)
    by (apply qeqT_imp_qeq; apply sqo_mul_inv; apply sqo_neq0_of_lt;
        apply Qlt_to_QltT; lra).
  setoid_replace (1 * / s) with (/ s) in Hle by (field; lra).
  setoid_replace (s * / s) with 1 in Hle by exact Hcancel.
  exact Hle.
Qed.

(* Strict form of the same lemma: 1 < s implies /s < 1 (the inv strict
   reversal of the k >= 2 branch). *)
Lemma sqo_inv_sqrt_lt_one : forall s : Q, QltT 1 s -> QltT (/ s) 1.
Proof.
  intros s H.
  apply Qlt_to_QltT.
  assert (Hlt1 : 1 < s) by (apply QltT_to_Qlt; exact H).
  assert (Hps : 0 < s) by lra.
  assert (Hpos : 0 < / s) by (apply Qinv_lt_0_compat; exact Hps).
  assert (Hlt : 1 * / s < s * / s).
  { apply (Qmult_lt_compat_r 1 s (/ s)); [exact Hpos | exact Hlt1]. }
  assert (Hcancel : s * / s == 1)
    by (apply qeqT_imp_qeq; apply sqo_mul_inv; apply sqo_neq0_of_lt;
        apply Qlt_to_QltT; lra).
  setoid_replace (1 * / s) with (/ s) in Hlt by ring.
  setoid_replace (s * / s) with 1 in Hlt by exact Hcancel.
  exact Hlt.
Qed.

(* ############ Section 1: G1 absorptive optimality characterization ##### *)

(* Q positivity + one-hop square monotonicity: 1 <= sqrt(s) (non-strict). *)
Lemma sqo_one_le_sqrt : forall s : Q, QleT' 0 s -> QleT' 1 (s * s) -> QleT' 1 s.
Proof.
  intros s H0 Hsq.
  apply Qle_to_QleT'.
  assert (H0q : 0 <= s) by (apply QleT'_to_Qle; exact H0).
  assert (Hsqq : 1 <= s * s) by (apply QleT'_to_Qle; exact Hsq).
  destruct (Qlt_le_dec s 1) as [Hlt | Hle].
  - exfalso.
    assert (Hb : s * s <= 1 * s).
    { apply (Qmult_le_compat_r s 1 s);
        [apply Qlt_le_weak; exact Hlt | exact H0q]. }
    setoid_replace (1 * s) with s in Hb by ring.
    assert (H1 : 1 <= s) by (apply (Qle_trans 1 (s * s) s); assumption).
    apply (Qlt_irrefl 1). apply (Qle_lt_trans 1 s 1); [exact H1 | exact Hlt].
  - exact Hle.
Qed.

(* Equality boundary: s*s == 1 implies s == 1 (0 <= s; both strict branches
   constructed away). *)
Lemma sqo_sqrt_eq_one : forall s : Q, QleT' 0 s -> QeqT (s * s) 1 -> QeqT s 1.
Proof.
  intros s H0 Hsq.
  apply qeq_imp_qeqT.
  assert (H0q : 0 <= s) by (apply QleT'_to_Qle; exact H0).
  assert (Hsqq : s * s == 1) by (apply qeqT_imp_qeq; exact Hsq).
  assert (Hss1 : 1 <= s * s).
  { apply QleT'_to_Qle. apply sqo_qeq_le. apply qeq_imp_qeqT. apply Qeq_sym.
    exact Hsqq. }
  assert (Hss : s * s <= 1).
  { apply QleT'_to_Qle. apply sqo_qeq_le. apply qeq_imp_qeqT. exact Hsqq. }
  destruct (Qlt_le_dec s 1) as [Hlt | Hle].
  - exfalso.
    assert (Hb : s * s <= 1 * s).
    { apply (Qmult_le_compat_r s 1 s);
        [apply Qlt_le_weak; exact Hlt | exact H0q]. }
    setoid_replace (1 * s) with s in Hb by ring.
    assert (Hlt2 : s * s < 1)
      by (apply (Qle_lt_trans (s * s) s 1); [exact Hb | exact Hlt]).
    apply (Qlt_irrefl 1).
    apply (Qle_lt_trans 1 (s * s) 1); [exact Hss1 | exact Hlt2].
  - destruct (Qlt_le_dec 1 s) as [Hgt | Hge].
    + exfalso.
      assert (Hb : 1 * s <= s * s).
      { apply (Qmult_le_compat_r 1 s s);
          [apply Qlt_le_weak; exact Hgt | exact H0q]. }
      setoid_replace (1 * s) with s in Hb by ring.
      assert (Hlt2 : 1 < s * s)
        by (apply (Qlt_le_trans 1 s (s * s)); [exact Hgt | exact Hb]).
      apply (Qlt_irrefl 1).
      apply (Qlt_le_trans 1 (s * s) 1); [exact Hlt2 | exact Hss].
    + apply Qle_antisym; assumption.
Qed.

(* Equality boundary converse: s == 1 implies s*s == 1 (trivial branch,
   composing the iff ledger with the lemma above). *)
Lemma sqo_sq_one_of_one : forall s : Q, QeqT s 1 -> QeqT (s * s) 1.
Proof.
  intros s H. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq s 1 H). reflexivity.
Qed.

(* Strict boundary: 1 < s*s implies 1 < s (strictness of the d > 1 branch). *)
Lemma sqo_sqrt_gt_one : forall s : Q, QleT' 0 s -> QltT 1 (s * s) -> QltT 1 s.
Proof.
  intros s H0 Hss.
  apply Qlt_to_QltT.
  assert (H0q : 0 <= s) by (apply QleT'_to_Qle; exact H0).
  assert (Hssq : 1 < s * s) by (apply QltT_to_Qlt; exact Hss).
  destruct (Qlt_le_dec 1 s) as [Hge | Hle].
  - exact Hge.
  - exfalso.
    assert (Hb : s * s <= 1 * s).
    { apply (Qmult_le_compat_r s 1 s); [exact Hle | exact H0q]. }
    setoid_replace (1 * s) with s in Hb by ring.
    apply (Qlt_irrefl 1).
    apply (Qlt_le_trans 1 (s * s) 1).
    + exact Hssq.
    + apply (Qle_trans (s * s) s 1); [exact Hb | exact Hle].
Qed.

(* G1 master ledger: 1 <= sqrt(s) with the equality/strict boundary triple
   (the theorem form of the header claim "1 <= sqrt(d), equality at k = 1
   and strict for k >= 2"; conjunction carried by the Set product And). *)
Theorem sqo_one_le_sqrt_characterization : forall s : Q, QleT' 0 s ->
  And (QleT' 1 (s * s) -> QleT' 1 s)
      (And (QeqT (s * s) 1 -> QeqT s 1) (QltT 1 (s * s) -> QltT 1 s)).
Proof.
  intros s H0. split.
  - intros Hsq1. apply sqo_one_le_sqrt; [exact H0 | exact Hsq1].
  - split.
    + intros Hs1. apply sqo_sqrt_eq_one; [exact H0 | exact Hs1].
    + intros Hss1. apply sqo_sqrt_gt_one; [exact H0 | exact Hss1].
Qed.

(* Witness-interface form (the Q-layer copy of the G10 root_of: sqrt(d)
   carried by 0 <= s and s*s == d): 1 <= d implies 1 <= sqrt(d). *)
Lemma sqo_sqrt_ge_one_of_d : forall d s : Q,
  QleT' 0 s -> QeqT (s * s) d -> QleT' 1 d -> QleT' 1 s.
Proof.
  intros d s H0 Hsd Hd.
  apply sqo_one_le_sqrt; [exact H0 |].
  apply Qle_to_QleT'.
  assert (Hsdq : s * s == d) by (apply qeqT_imp_qeq; exact Hsd).
  assert (Hdq : 1 <= d) by (apply QleT'_to_Qle; exact Hd).
  setoid_replace (s * s) with d by exact Hsdq.
  exact Hdq.
Qed.

(* Direct translation of the header claim (1): (1/2)*inv(sqrt(s)) <= 1/2
   (equivalent to inv(sqrt(s)) <= 1, the s version). *)
Lemma sqo_absorb_half_le : forall s : Q, QleT' 1 s -> QleT' ((1#2) * / s) (1#2).
Proof.
  intros s H.
  apply Qle_to_QleT'.
  assert (Hle1 : 1 <= s) by (apply QleT'_to_Qle; exact H).
  setoid_replace ((1#2) * / s) with (/ s * (1#2)) by (field; lra).
  apply (Qle_trans (/ s * (1#2)) (1 * (1#2)) (1#2)).
  - apply (Qmult_le_compat_r (/ s) 1 (1#2)).
    + apply QleT'_to_Qle. apply sqo_inv_sqrt_le_one. exact H.
    + lra.
  - apply QleT'_to_Qle. apply sqo_qeq_le. apply qeq_imp_qeqT. reflexivity.
Qed.

(* Header claim (1) witness form: d >= 1 implies (1/2)*inv(sqrt(d)) <= 1/2
   (the +1 exact absorption lemma). *)
Lemma sqo_absorb_half_le_w : forall d s : Q,
  QleT' 0 s -> QeqT (s * s) d -> QleT' 1 d -> QleT' ((1#2) * / s) (1#2).
Proof.
  intros d s H0 Hsd Hd.
  apply sqo_absorb_half_le.
  apply (sqo_sqrt_ge_one_of_d d s); assumption.
Qed.

(* d == 1 iff the sqrt side == 1 (the equality point migrated to the
   dimension side; the iff carried by the Set product And). *)
Lemma sqo_sqrt_eq_one_iff_d : forall d s : Q,
  QleT' 0 s -> QeqT (s * s) d -> And (QeqT s 1 -> QeqT d 1) (QeqT d 1 -> QeqT s 1).
Proof.
  intros d s H0 Hsd. split; intros H.
  - apply qeq_imp_qeqT.
    assert (Hs1 : s * s == 1)
      by (apply qeqT_imp_qeq; apply sqo_sq_one_of_one; exact H).
    assert (Hssd : s * s == d) by (apply qeqT_imp_qeq; exact Hsd).
    rewrite <- Hssd. exact Hs1.
  - assert (Hdd : d == 1) by (apply qeqT_imp_qeq; exact H).
    assert (Hssd : s * s == d) by (apply qeqT_imp_qeq; exact Hsd).
    assert (Hs1 : s * s == 1) by (rewrite Hssd; exact Hdd).
    apply sqo_sqrt_eq_one; [exact H0 | apply qeq_imp_qeqT; exact Hs1].
Qed.

(* d > 1 implies sqrt(d) > 1 (strictness migrated to the dimension side). *)
Lemma sqo_sqrt_gt_one_of_d : forall d s : Q,
  QleT' 0 s -> QeqT (s * s) d -> QltT 1 d -> QltT 1 s.
Proof.
  intros d s H0 Hsd Hd.
  apply sqo_sqrt_gt_one; [exact H0 |].
  apply Qlt_to_QltT.
  assert (Hdq : 1 < d) by (apply QltT_to_Qlt; exact Hd).
  assert (Hssd : s * s == d) by (apply qeqT_imp_qeq; exact Hsd).
  setoid_replace d with (s * s) in Hdq by (symmetry; exact Hssd).
  exact Hdq.
Qed.

(* ############ Section 2: the G2 tightness theorem ##################### *)

(* General-h general-c absorption chain (the h argument slot = the eps
   pass-through slot of the G10 piece 2; this piece uses h := 1/2):
   h*inv(s) <= c implies (x+h)*inv(s) <= y*inv(s) + c (x <= y).
   Absorption point: after expanding the square, h*inv(s) is swallowed by c
   -- the tightness threshold is exactly h*inv(s). *)
Lemma sqo_absorb_general : forall x y s c h : Q,
  QltT 0 s -> QleT' x y -> QleT' (h * / s) c ->
  QleT' ((x + h) * / s) (y * / s + c).
Proof.
  intros x y s c h Hs Hxy Hhc.
  apply Qle_to_QleT'.
  assert (Hsq : 0 < s) by (apply QltT_to_Qlt; exact Hs).
  assert (Hxyq : x <= y) by (apply QleT'_to_Qle; exact Hxy).
  assert (Hhcq : h * / s <= c) by (apply QleT'_to_Qle; exact Hhc).
  assert (Hinvs : 0 <= / s)
    by (apply Qinv_le_0_compat; apply Qlt_le_weak; exact Hsq).
  apply (Qle_trans ((x + h) * / s) (x * / s + h * / s) (y * / s + c)).
  - apply QleT'_to_Qle. apply sqo_qeq_le. apply qeq_imp_qeqT. field; lra.
  - apply (Qplus_le_compat (x * / s) (y * / s) (h * / s) c).
    + apply (Qmult_le_compat_r x y (/ s)); assumption.
    + exact Hhcq.
Qed.

(* The G10 header-chain ideal form as a whole: piece-2 output-bound-form
   input X <= root product + 1/2, root product <= QK, c >= (1/2)*inv(s)
   implies the |logit|-shaped output X*inv(s) <= QK*inv(s) + c
   (the G10 empirical conclusion is the non-strict face -- faithfully
   aligned here). *)
Theorem sqo_chain_bound : forall X D QC s c : Q,
  QltT 0 s -> QleT' 1 s -> QleT' X (D + (1#2)) -> QleT' D QC ->
  QleT' ((1#2) * / s) c -> QleT' (X * / s) (QC * / s + c).
Proof.
  intros X D QC s c Hs H1 HX HD Hc.
  apply Qle_to_QleT'.
  assert (Hsq : 0 < s) by (apply QltT_to_Qlt; exact Hs).
  assert (H1q : 1 <= s) by (apply QleT'_to_Qle; exact H1).
  assert (HXq : X <= D + (1#2)) by (apply QleT'_to_Qle; exact HX).
  assert (HDq : D <= QC) by (apply QleT'_to_Qle; exact HD).
  assert (Hcq : (1#2) * / s <= c) by (apply QleT'_to_Qle; exact Hc).
  assert (Hinvs : 0 <= / s)
    by (apply Qinv_le_0_compat; apply Qlt_le_weak; exact Hsq).
  apply (Qle_trans (X * / s) ((D + (1#2)) * / s) (QC * / s + c)).
  - apply (Qmult_le_compat_r X (D + (1#2)) (/ s)); assumption.
  - apply (Qle_trans ((D + (1#2)) * / s) (D * / s + (1#2) * / s)
                     (QC * / s + c)).
    + apply QleT'_to_Qle. apply sqo_qeq_le. apply qeq_imp_qeqT. field; lra.
    + apply (Qplus_le_compat (D * / s) (QC * / s) ((1#2) * / s) c).
      * apply (Qmult_le_compat_r D QC (/ s)); assumption.
      * exact Hcq.
Qed.

(* Constructive boundary breaking (necessity): c < (1/2)*inv(s) implies the
   absorption chain strictly fails at the root-product = QK point (x
   arbitrary, q := k reachable) -- an explicit witness, not a proof by
   contradiction. *)
Lemma sqo_absorb_breaks : forall x s c : Q,
  QltT 0 s -> QltT c ((1#2) * / s) -> QltT (x * / s + c) ((x + (1#2)) * / s).
Proof.
  intros x s c Hs Hc.
  apply Qlt_to_QltT.
  assert (Hsq : 0 < s) by (apply QltT_to_Qlt; exact Hs).
  assert (Hcq : c < (1#2) * / s) by (apply QltT_to_Qlt; exact Hc).
  setoid_replace ((x + (1#2)) * / s) with (x * / s + (1#2) * / s) by (field; lra).
  remember (/ s) as u.
  lra.
Qed.

(* The G2 master four-fold ledger: the boundary-keeping condition of the +1
   for-general-c exchange, fully characterized.
   Fold 1 (sufficiency): c >= (1/2)*inv(s) implies the absorption chain holds
   for all x <= y.
   Fold 2 (necessity, constructive breaking): c < (1/2)*inv(s) implies a
   strict violation for every x.
   Fold 3 (explicit counterexample at the d = 1 degenerate point):
   c < 1/2 implies (0+1/2)*inv(1) > 0*inv(1) + c.
   Fold 4 (margin exactly zero characterized): the absorption identity holds
   for all x iff c is exactly the threshold (1/2)*inv(s) -- the machine form
   of "the absorption margin is exactly zero". *)
Theorem sqo_plus1_optimal : forall s : Q, QltT 0 s ->
  And (forall c x y : Q, QleT' ((1#2) * / s) c -> QleT' x y ->
        QleT' ((x + (1#2)) * / s) (y * / s + c))
      (And (forall c x : Q, QltT c ((1#2) * / s) ->
             QltT (x * / s + c) ((x + (1#2)) * / s))
           (And (forall c : Q, QltT c (1#2) ->
                  QltT (0 * / 1 + c) ((0 + (1#2)) * / 1))
                (forall c : Q, (forall x : Q, QeqT ((x + (1#2)) * / s)
                                                (x * / s + c)) ->
                               QeqT c ((1#2) * / s)))).
Proof.
  intros s Hs.
  assert (Hsq : 0 < s) by (apply QltT_to_Qlt; exact Hs).
  split.
  - intros c x y Hc Hxy. exact (sqo_absorb_general x y s c (1#2) Hs Hxy Hc).
  - split.
    + intros c x Hc. exact (sqo_absorb_breaks x s c Hs Hc).
    + split.
      * intros c Hc. apply Qlt_to_QltT.
        change (/ 1) with 1.
        assert (Hcq : c < (1#2)) by (apply QltT_to_Qlt; exact Hc).
        setoid_replace ((0 + (1#2)) * 1) with ((1#2)) by ring.
        setoid_replace (0 * 1 + c) with c by ring.
        exact Hcq.
      * intros c Hfam.
        assert (H0 : (0 + (1#2)) * / s == 0 * / s + c)
          by (apply qeqT_imp_qeq; apply Hfam).
        setoid_replace ((0 + (1#2)) * / s) with ((1#2) * / s) in H0 by (field; lra).
        setoid_replace (0 * / s + c) with c in H0 by (field; lra).
        apply qeq_imp_qeqT. exact (Qeq_sym _ _ H0).
Qed.

(* Decidable threshold split (the Set-layer exit): c >= / < (1/2)*inv(s)
   constructively decidable (sumbool bracket form, kept verbatim). *)
Lemma sqo_plus1_threshold_dec : forall s c : Q,
  { (1#2) * / s <= c } + { c < (1#2) * / s }.
Proof.
  intros s c.
  destruct (Qlt_le_dec c ((1#2) * / s)) as [Hlt | Hle].
  - right. exact Hlt.
  - left. exact Hle.
Qed.

(* The +1 margin quantitative ledger: the G10 Delta absorption margin
   1 - (1/2)*inv(sqrt(d)) >= 1/2 is positive everywhere (on the whole
   d >= 1 domain; the margin is exactly zero only at the threshold c*,
   see fold 4). *)
Theorem sqo_plus1_margin : forall s : Q, QltT 0 s -> QleT' 1 s ->
  QleT' (1#2) (1 - (1#2) * / s).
Proof.
  intros s Hs H1.
  apply Qle_to_QleT'.
  assert (Hsq : 0 < s) by (apply QltT_to_Qlt; exact Hs).
  assert (H1q : 1 <= s) by (apply QleT'_to_Qle; exact H1).
  assert (Hab : (1#2) * / s <= (1#2))
    by (apply QleT'_to_Qle; apply sqo_absorb_half_le; exact H1).
  remember (/ s) as u.
  lra.
Qed.

(* ############ Section 3: the G3 piecewise exact form ################## *)

(* The exact piecewise form of the header claim "equality at k = 1, strict
   for k >= 2": d == 1 implies (1/2)*inv(sqrt(d)) is exactly 1/2;
   d > 1 implies strictly below 1/2. *)
Theorem sqo_piecewise : forall d s : Q, QleT' 0 s -> QeqT (s * s) d ->
  And (QeqT d 1 -> QeqT ((1#2) * / s) (1#2))
      (QltT 1 d -> QltT ((1#2) * / s) (1#2)).
Proof.
  intros d s H0 Hsd. split.
  - intros Hd.
    apply qeq_imp_qeqT.
    assert (Hdd : d == 1) by (apply qeqT_imp_qeq; exact Hd).
    assert (Hssd : s * s == d) by (apply qeqT_imp_qeq; exact Hsd).
    assert (Hs1 : s * s == 1) by (rewrite Hssd; exact Hdd).
    assert (Heq : s == 1).
    { apply qeqT_imp_qeq. apply sqo_sqrt_eq_one.
      - exact H0.
      - apply qeq_imp_qeqT. exact Hs1. }
    setoid_replace s with 1 by exact Heq.
    change (/ 1) with 1.
    reflexivity.
  - intros Hd.
    apply Qlt_to_QltT.
    assert (Hdq : 1 < d) by (apply QltT_to_Qlt; exact Hd).
    assert (Hssd : s * s == d) by (apply qeqT_imp_qeq; exact Hsd).
    assert (Hgt1s : QltT 1 s).
    { apply sqo_sqrt_gt_one; [exact H0 |].
      apply Qlt_to_QltT.
      setoid_replace d with (s * s) in Hdq by (symmetry; exact Hssd).
      exact Hdq. }
    assert (Hgt1q : 1 < s) by (apply QltT_to_Qlt; exact Hgt1s).
    assert (Hps : 0 < s) by lra.
    setoid_replace ((1#2) * / s) with (/ s * (1#2)) by (field; lra).
    apply (Qmult_lt_compat_r (/ s) 1 (1#2)).
    + lra.
    + apply QltT_to_Qlt. apply sqo_inv_sqrt_lt_one. exact Hgt1s.
Qed.

Print Assumptions sqo_absorb_half_le_w.
