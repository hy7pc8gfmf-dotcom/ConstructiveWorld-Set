(* ConstructiveWorld-Set -- escape-window separation for irrationality criteria. *)

(** * u5c_bridge: separation lemmas with an explicit escape point.

    Mission.  When a centre family [x] and a radius family [e] serve at
      once as tail bound ([lic_tail_bounded]), escape window
      ([lic_escape_window]) and vanishing width ([lic_vanish]), any rational
      [q] escaping the window [e n0] at some point [n0 >= 1] is separated
      from the Cauchy limit [X] of [x] by a positive rational constant; the
      escape-point choice inside [lic_irrational_criterion] becomes an
      explicit argument: [u5c_escape_to_dist] proves the pointwise form and
      [u5c_criterion_from_window] recovers it from the existential witness.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
      [Arith.Arith], [Bool.Bool], [Arith.Factorial], [Lia], [Setoid],
      [Morphisms], [Qfield], [Extraction].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [SumInvFactEscape],
      [UpReqBanachNormOpp], [UpReqIrrationalCriterion] of this development.

    References.  This development, u5c_bridge.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" u5c_bridge.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ================= Section 1. General separation lemma (explicit escape point) ================= *)

(* halving the escape margin: if [q] escapes the window [e n0] at [n0],
   then [c := (Qabs (q - x n0) - e n0) / 2] is positive and [real_const c]
   lies below the distance from the Cauchy limit [X] of [x] to [q]; the
   tail bound at the single point [n0] governs the whole tail, and the
   limit identification uses the vanishing width. *)
Lemma u5c_escape_to_dist :
  forall (x e : nat -> Q)
    (Ht : lic_tail_bounded x e) (Hv : lic_vanish e),
  forall (q : Q) (n0 : nat), (1 <= n0)%nat ->
    QltT (e n0) (Qabs ((q - x n0)%Q)) ->
    sigT (fun c : Q => And (QltT 0 c)
      (real_lt (real_const c)
         (real_metric (existT (fun u : Qseq => cauchy u) x
                         (lic_seq_cauchy x e Ht Hv))
                      (real_const q)))).
Proof.
  intros x e Ht Hv q n0 Hn01 Hesc.
  pose proof (QltT_to_Qlt _ _ Hesc) as Hesc'.
  remember (Qabs ((q - x n0)%Q)) as A eqn:HA.
  assert (Hcpos : Qlt 0 ((A - e n0) * (1 # 2))%Q).
  { apply (Qmult_lt_0_compat (A - e n0)%Q (1 # 2)%Q).
    - apply lic_qlt_0_minus. exact Hesc'.
    - unfold Qlt. cbn [Qnum Qden]. lia. }
  remember ((A - e n0) * (1 # 2))%Q as c eqn:HEc.
  assert (Hcv : (c + c == (A - e n0))%Q)
    by (apply lic_half_bridge; rewrite <- HEc; apply Qeq_refl).
  assert (HA2 : A == ((c + c) + e n0)%Q).
  { rewrite Hcv. symmetry. apply lic_qlt_minus_add_r. }
  exists c.
  split.
  - apply Qlt_to_QltT. exact Hcpos.
  - unfold real_lt.
    exists c.
    split.
    + apply Qlt_to_QltT. exact Hcpos.
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
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
          setoid_rewrite Hpre. apply Qeq_refl.
        - exact HT. }
      rewrite <- HA in Htri.
      remember (Qabs ((q - x k)%Q)) as Bk eqn:HB.
      remember (Qabs ((x k - x n0)%Q)) as Ek eqn:HE.
      assert (Hlt1 : Qlt (Bk + Ek) (Bk + e n0))
        by (apply (lic_qlt_add_l Bk Ek (e n0)); exact Ht0').
      assert (Hlt2 : Qlt A (Bk + e n0))
        by (apply (Qle_lt_trans A (Bk + Ek)); [exact Htri | exact Hlt1]).
      rewrite HA2 in Hlt2.
      setoid_rewrite (Qplus_comm (c + c) (e n0)) in Hlt2.
      setoid_rewrite (Qplus_comm Bk (e n0)) in Hlt2.
      assert (Hle3 : Qle (c + c) Bk).
      { apply (lic_qlt_dec_le (c + c) Bk).
        intro Hcontra.
        assert (Hbad : Qlt (Bk + e n0) ((c + c) + e n0))
          by (apply (lic_qlt_add_r Bk (c + c) (e n0)); exact Hcontra).
        setoid_rewrite (Qplus_comm (c + c) (e n0)) in Hbad.
        setoid_rewrite (Qplus_comm Bk (e n0)) in Hbad.
        exact (Qlt_not_eq (e n0 + Bk) (e n0 + Bk)
                 (Qlt_trans (e n0 + Bk) (e n0 + (c + c)) (e n0 + Bk)
                    Hbad Hlt2) (Qeq_refl (e n0 + Bk))). }
      destruct (Qlt_bool (c + c) Bk) eqn:Ecb.
      * assert (Hlt3 : Qlt (c + c) Bk) by exact (lic_qlt_bool_true _ _ Ecb).
        assert (Hfin : Qlt c (Bk - c)%Q).
        { apply (lic_qlt_add_r_cancel_r c (Bk - c) c).
          rewrite (lic_qlt_minus_add_r Bk c). exact Hlt3. }
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
      * exfalso.
        pose proof (lic_qlt_bool_false_le (c + c) Bk Ecb) as Hle4.
        assert (Hle5 : Qle (Bk + e n0) ((c + c) + e n0))
          by (apply (Qplus_le_compat Bk (c + c) (e n0) (e n0));
              [exact Hle4 | apply Qle_refl]).
        setoid_rewrite (Qplus_comm Bk (e n0)) in Hle5.
        setoid_rewrite (Qplus_comm (c + c) (e n0)) in Hle5.
        exact (Qlt_not_eq (e n0 + (c + c)) (e n0 + (c + c))
                 (Qlt_le_trans (e n0 + (c + c)) (e n0 + Bk) (e n0 + (c + c))
                    Hlt2 Hle5) (Qeq_refl (e n0 + (c + c))%Q)).
Qed.

(* recovery from the existential window witness: given the
   [lic_escape_window] assembly form (the original entry of the master
   theorem), select its witnessing escape point and apply
   [u5c_escape_to_dist]; the two entries converge on the same
   construction. *)
Lemma u5c_criterion_from_window : forall (x e : nat -> Q)
  (Ht : lic_tail_bounded x e) (Hw : lic_escape_window x e) (Hv : lic_vanish e),
  forall q : Q,
    sigT (fun c : Q => And (QltT 0 c)
      (real_lt (real_const c)
         (real_metric (existT (fun u : Qseq => cauchy u) x
                         (lic_seq_cauchy x e Ht Hv))
                      (real_const q)))).
Proof.
  intros x e Ht Hw Hv q.
  destruct (Hw q) as [n0 [Hn01 Hesc]].
  exact (u5c_escape_to_dist x e Ht Hv q n0 Hn01 Hesc).
Qed.

From Stdlib Require Import Extraction.
Separate Extraction u5c_escape_to_dist u5c_criterion_from_window.

Print Assumptions u5c_escape_to_dist.
Print Assumptions u5c_criterion_from_window.
