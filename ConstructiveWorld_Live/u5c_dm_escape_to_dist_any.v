(* ConstructiveWorld-Set -- margin-generalized escape-window separation with an explicit constant. *)

(** * u5c_dm_escape_to_dist_any: escape-to-distance separation with an explicit constant element.

    Mission.  Margin-generalized escape-to-distance separation: a rational
      [q] escaping the window [e n0] at some point [n0 >= 1], with [x]
      tail-bounded by [e] and [e] vanishing, is separated from the Cauchy
      limit of [x] by a positive constant; where [u5c_escape_to_dist] fixes
      that constant by halving the margin internally,
      [dmec_escape_to_dist_any] takes it as an explicit argument [c] under
      the premises [QltT 0 c] and [QleT' (c + c) (Qabs (q - x (n0)) - e (n0))],
      and [dmec_qleT'_qle] lowers [QleT'] to [Qle].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
      [Arith.Arith], [Bool.Bool], [Setoid], [Morphisms], [Qfield],
      [Extraction].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [SumInvFactEscape], [UpReqBanachNormOpp],
      [UpReqIrrationalCriterion] of this development.

    References.  This development, u5c_dm_escape_to_dist_any.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" u5c_dm_escape_to_dist_any.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Setoid Morphisms Qfield.

(* ================= Section 1. A self-carried adapter from [QleT'] down to [Qle] ================= *)

Lemma dmec_qleT'_qle : forall x y : Q, QleT' x y -> Qle x y.
Proof.
  intros x y H.
  unfold QleT' in H.
  (* The Require order matches [u5c_bridge]: development modules come
     before Stdlib, so the bare name [Qle_bool] resolves to the Stdlib
     constant and the [S02_CauchyComplete] constant unfolds by full name. *)
  unfold S02_CauchyComplete.Qle_bool in H.
  unfold Qcompare in H.
  unfold Qle.
  change ((Qnum x * QDen y ?= Qnum y * QDen x)%Z <> Gt).
  destruct (Qnum x * QDen y ?= Qnum y * QDen x)%Z eqn:E; simpl in H;
    try (inversion H); try (intro Hc; inversion Hc).
Qed.

(* ================= Section 2. The margin-generalized escape-to-distance separation lemma ================= *)

(* Margin-generalized escape-to-separation: if the rational [q] escapes the
   window [e (n0)] at some index [n0 >= 1] and the constant [c] satisfies
   [0 < c] together with [(c + c) <= |q - x (n0)| - e (n0)], then
   [real_const c] is [real_lt]-separated from the metric between the Cauchy
   limit of [x] (exported by tail boundedness and vanishing) and
   [real_const q]. *)
Lemma dmec_escape_to_dist_any :
  forall (x e : nat -> Q)
    (Ht : lic_tail_bounded x e) (Hv : lic_vanish e),
  forall (q : Q) (n0 : nat), (1 <= n0)%nat ->
    QltT (e n0) (Qabs ((q - x n0)%Q)) ->
    forall c : Q, QltT 0 c ->
    QleT' ((c + c)%Q) ((Qabs ((q - x n0)%Q) - e n0)%Q) ->
    sigT (fun c : Q => And (QltT 0 c)
      (real_lt (real_const c)
         (real_metric (existT (fun u : Qseq => cauchy u) x
                          (lic_seq_cauchy x e Ht Hv))
                      (real_const q)))).
Proof.
  intros x e Ht Hv q n0 Hn01 Hesc c Hc0 Hmarg.
  remember (Qabs ((q - x n0)%Q)) as A eqn:HA.
  pose proof (dmec_qleT'_qle (c + c) (A - e n0) Hmarg) as Hmarg'.
  exists c.
  split.
  - exact Hc0.
  - unfold real_lt.
    exists c.
    split.
    + exact Hc0.
    + exists n0. intros k HkN.
      apply NatLe_drop in HkN.
      pose proof (QltT_to_Qlt _ _ (Ht n0 k Hn01 HkN)) as Ht0'.
      assert (Hpre : (q - x n0)%Q == ((q - x k) + (x k - x n0))%Q)
        by exact (lic_qlt_tri_decomp q (x n0) (x k)).
      assert (Htri : Qle (Qabs ((q - x n0)%Q))
                         (Qabs ((q - x k)%Q) + Qabs ((x k - x n0)%Q))).
      { pose proof (Qabs_triangle ((q - x k)%Q) ((x k - x n0)%Q)) as HT.
        apply (Qle_trans (Qabs ((q - x n0)%Q))
                 (Qabs (((q - x k) + (x k - x n0))%Q))).
        - apply dmec_qleT'_qle. apply qeq_le. apply qeq_imp_qeqT.
          exact (Qabs_wd _ _ Hpre).
        - exact HT. }
      rewrite <- HA in Htri.
      remember (Qabs ((q - x k)%Q)) as Bk eqn:HB.
      remember (Qabs ((x k - x n0)%Q)) as Ek eqn:HE.
      assert (Hlt1 : Qlt (Bk + Ek) (Bk + e n0))
        by (apply (lic_qlt_add_l Bk Ek (e n0)); exact Ht0').
      assert (Hlt2 : Qlt A (Bk + e n0))
        by (apply (Qle_lt_trans A (Bk + Ek)); [exact Htri | exact Hlt1]).
      (* Generalized replacement step: rewrite [A == (A - e n0) + e n0] and
         cancel the right summand; this strict direct chain replaces the
         [Qlt_bool] case split by contradiction of the baseline theorem. *)
      assert (HA2 : A == ((A - e n0) + e n0)%Q).
      { symmetry. apply lic_qlt_minus_add_r. }
      rewrite HA2 in Hlt2.
      assert (Hltm : Qlt (A - e n0) Bk)
        by (apply (lic_qlt_add_r_cancel_r (A - e n0) Bk (e n0)); exact Hlt2).
      assert (HltQ : Qlt (c + c) Bk).
      { apply (Qle_lt_trans (c + c) (A - e n0) Bk).
        - exact Hmarg'.
        - exact Hltm. }
      (* The closing segment mirrors the baseline theorem [u5c_escape_to_dist]. *)
      assert (Hfin : Qlt c (Bk - c)%Q).
      { apply (lic_qlt_add_r_cancel_r c (Bk - c) c).
        rewrite (lic_qlt_minus_add_r Bk c). exact HltQ. }
      assert (HPr : projT1 (real_metric (existT (fun u : Qseq => cauchy u) x
                                   (lic_seq_cauchy x e Ht Hv)) (real_const q)) k
                  == Qabs ((x k - q)%Q))
        by apply lic_metric_proj.
      apply (lic_qltt_comp_r ((Qabs ((q - x k)%Q)) - c)
               (projT1 (real_metric (existT (fun u : Qseq => cauchy u) x
                                      (lic_seq_cauchy x e Ht Hv)) (real_const q)) k
                - projT1 (real_const c) k) c).
      -- rewrite (qeqT_imp_qeq _ _ (real_const_proj c k)). rewrite HPr.
         rewrite (Qabs_Qminus q (x k)). reflexivity.
      -- rewrite HB in Hfin. apply Qlt_to_QltT. exact Hfin.
(* The witness closes with [Defined] instead of [Qed]: the [sigT] witness
   must stay transparent so downstream assemblies can determine the
   constant by [Qeq]. *)
Defined.

From Stdlib Require Import Extraction.
Separate Extraction dmec_qleT'_qle dmec_escape_to_dist_any.

Print Assumptions dmec_escape_to_dist_any.
