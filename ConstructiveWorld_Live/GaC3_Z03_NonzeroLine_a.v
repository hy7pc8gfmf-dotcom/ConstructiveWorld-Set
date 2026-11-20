(* ConstructiveWorld-Main - leaf a of the three-cosine racing engine: the rational transport kit. *)

(** * GaC3_Z03_NonzeroLine_a: leaf a of node C3-Z03.
    Mission.  Leaf a of the three-cosine racing engine (node C3-Z03,
    segment C3): the rational transport kit and the Q-level congruence
    kit, carried on Set-sorted order faces.  Part 0a moves the strict
    and weak rational orders along the Set-sorted rational identity
    (the transport goes through Qlt_alt/Qle_alt, the Qcompare_comp
    congruence, and the Set-face bridges); the two-sided
    absolute-value faces (the negation below the absolute value, the
    value itself below its absolute value, and the lower-bound
    transfer along an absolute value) feed the Real-level relax kit of
    the companion leaf.  The cosine term kit is ring-congruent through
    the q_pow setoid face [q_pow_wd], the consumption base of the
    pointwise cosine face in the companion leaf.
    Dependencies.  Stdlib [QArith.QArith] (with [Qabs] and [Qring]),
    [Setoid], [Morphisms]; the Require lines below supply the
    Set-sorted order faces ([QeqT], [QltT], [QleT']) with their two-way
    bridges, the rational exponential kit ([q_pow_wd]) and the
    rational trigonometric term kit ([cos_term], [cos_partial]).
    References.  ZZ theory (AFP PNT_with_Remainder) [logderiv_zeta_ineq]
    :136-163 (the three-cosine weighted inequality assembled on these
    term faces); drafts_C3.md C3-Z03 (the racing skeleton, the
    explicit-radius obligation); cards_C3 C3-Z03.
    Constructivity.  Set-sorted rational order transports and
    congruences; zero assumed constants, zero abandoned proofs, zero
    classical choice; Print Assumptions reads Closed.
    Build.  coqc -Q <world root> "" -o <stem>.vo <stem>.v (world-rooted
    build against the certified dependency tree). *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.

Local Open Scope Q_scope.

(* ===================================================================== *)
(* Part 0a. The rational transport kit: the Set-sorted rational identity *)
(* moves the strict and weak orders (the numeric Qlt/Qle definitions are *)
(* comparison-based, so the transport goes through Qlt_alt/Qle_alt and   *)
(* the Qcompare_comp congruence, lifted through the Set-face bridges).   *)
(* ===================================================================== *)

Lemma qeq_lt_l : forall a b c : Q, QeqT a b -> QltT b c -> QltT a c.
Proof.
  intros a b c Hab Hbc.
  apply Qlt_to_QltT. apply Qlt_alt.
  rewrite (Qcompare_comp a b (qeqT_imp_qeq a b Hab) c c (Qeq_refl c)).
  exact (proj2 (Qlt_alt b c) (QltT_to_Qlt b c Hbc)).
Defined.

Lemma qeq_lt_r : forall a b c : Q, QeqT b c -> QltT a b -> QltT a c.
Proof.
  intros a b c Hbc Hab.
  apply Qlt_to_QltT. apply Qlt_alt.
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b c (qeqT_imp_qeq b c Hbc)).
  exact (proj2 (Qlt_alt a b) (QltT_to_Qlt a b Hab)).
Defined.

Lemma qeq_le_l : forall a b c : Q, QeqT a b -> QleT' b c -> QleT' a c.
Proof.
  intros a b c Hab Hbc.
  apply Qle_to_QleT'. apply Qle_alt.
  rewrite (Qcompare_comp a b (qeqT_imp_qeq a b Hab) c c (Qeq_refl c)).
  exact (proj2 (Qle_alt b c) (QleT'_to_Qle b c Hbc)).
Defined.

Lemma qeq_le_r : forall a b c : Q, QeqT b c -> QleT' a b -> QleT' a c.
Proof.
  intros a b c Hbc Hab.
  apply Qle_to_QleT'. apply Qle_alt.
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b c (qeqT_imp_qeq b c Hbc)).
  exact (proj2 (Qle_alt a b) (QleT'_to_Qle a b Hab)).
Defined.

Lemma qeq_minus_r0 : forall a z : Q, QeqT z 0 -> QeqT (a - z) a.
Proof.
  intros a z Hz.
  assert (H1 : Qeq (a - z) (a - 0))
    by exact (Qminus_comp a a (Qeq_refl a) z 0 (qeqT_imp_qeq z 0 Hz)).
  assert (H2 : Qeq (a - 0) a) by ring.
  exact (qeq_imp_qeqT (a - z) a (Qeq_trans (a - z) (a - 0) a H1 H2)).
Defined.

(* The negation is below the absolute value (the weak half of the       *)
(* triangle fact). *)
Lemma qopp_le_abs : forall u : Q, QleT' (- u) (Qabs u).
Proof.
  intro u. destruct (Q_dec u 0) as [[Hclt | Hcgt] | Hc].
  - assert (Habs : Qabs u == - u) by (apply Qabs_neg; apply Qlt_le_weak; exact Hclt).
    exact (qeq_le_r (- u) (- u) (Qabs u)
             (qeq_imp_qeqT (- u) (Qabs u) (Qeq_sym (Qabs u) (- u) Habs))
             (qleT'_refl (- u))).
  - assert (Habs : Qabs u == u) by (apply Qabs_pos; apply Qlt_le_weak; exact Hcgt).
    assert (Hneg : Qle (- u) 0)
      by exact (Qopp_le_compat 0 u (Qlt_le_weak 0 u Hcgt)).
    exact (qeq_le_r (- u) u (Qabs u)
             (qeq_imp_qeqT u (Qabs u) (Qeq_sym (Qabs u) u Habs))
             (Qle_to_QleT' (- u) u
                (Qle_trans (- u) 0 u Hneg (Qlt_le_weak 0 u Hcgt)))).
  - assert (H0u : QleT' 0 u)
      by exact (qeq_le_l 0 u u (qeq_imp_qeqT 0 u (Qeq_sym u 0 Hc))
                  (qleT'_refl u)).
    exact (qeq_le_r (- u) u (Qabs u)
             (qeq_imp_qeqT u (Qabs u)
                (Qeq_sym (Qabs u) u (Qabs_pos u (QleT'_to_Qle 0 u H0u))))
             (Qle_to_QleT' (- u) u
                (Qle_trans (- u) 0 u
                   (Qopp_le_compat 0 u (QleT'_to_Qle 0 u H0u))
                   (QleT'_to_Qle 0 u H0u)))).
Defined.

(* The mirrored half: the value itself is below its absolute value. *)
Lemma qself_le_abs : forall u : Q, QleT' u (Qabs u).
Proof.
  intro u. destruct (Q_dec u 0) as [[Hclt | Hcgt] | Hc].
  - assert (Habs : Qabs u == - u) by (apply Qabs_neg; apply Qlt_le_weak; exact Hclt).
    assert (Hle : Qle u (- u)).
    { apply (Qle_trans u 0 (- u)).
      - apply Qlt_le_weak. exact Hclt.
      - exact (Qopp_le_compat u 0 (Qlt_le_weak u 0 Hclt)). }
    exact (qeq_le_r u (- u) (Qabs u)
             (qeq_imp_qeqT (- u) (Qabs u) (Qeq_sym (Qabs u) (- u) Habs))
             (Qle_to_QleT' u (- u) Hle)).
  - assert (Habs : Qabs u == u) by (apply Qabs_pos; apply Qlt_le_weak; exact Hcgt).
    exact (qeq_le_r u u (Qabs u)
             (qeq_imp_qeqT u (Qabs u) (Qeq_sym (Qabs u) u Habs))
             (qleT'_refl u)).
  - assert (H0u : QleT' 0 u)
      by exact (qeq_le_l 0 u u (qeq_imp_qeqT 0 u (Qeq_sym u 0 Hc))
                  (qleT'_refl u)).
    exact (qeq_le_r u u (Qabs u)
             (qeq_imp_qeqT u (Qabs u)
                (Qeq_sym (Qabs u) u (Qabs_pos u (QleT'_to_Qle 0 u H0u))))
             (qleT'_refl u)).
Defined.

(* The two-sided face: an absolute value below b puts -b below the value. *)
Lemma qabs_lb : forall a b : Q, QltT 0 b -> QltT (Qabs a) b -> QltT (- b) a.
Proof.
  intros a b Hb Hab.
  destruct (Q_dec a 0) as [[Hclt | Hcgt] | Hc].
  - assert (Habs : Qabs a == - a) by (apply Qabs_neg; apply Qlt_le_weak; exact Hclt).
    assert (Hneg : Qlt (- a) b)
      by exact (QltT_to_Qlt (- a) b
                  (qeq_lt_l (- a) (Qabs a) b
                     (qeq_imp_qeqT (- a) (Qabs a) (Qeq_sym (Qabs a) (- a) Habs)) Hab)).
    assert (Hopp : Qlt (- b) (- (- a))) by (apply (Qopp_lt_compat (- a) b); exact Hneg).
    assert (Hrr : Qeq (- (- a)) a) by ring.
    exact (qeq_lt_r (- b) (- (- a)) a (qeq_imp_qeqT (- (- a)) a Hrr)
                        (Qlt_to_QltT (- b) (- (- a)) Hopp)).
  - assert (Habs : Qabs a == a) by (apply Qabs_pos; apply Qlt_le_weak; exact Hcgt).
    assert (Hlowlt : Qlt (- b) (Qabs a)).
    { apply (Qlt_le_trans (- b) 0 (Qabs a)).
      - apply (Qopp_lt_compat 0 b). exact (QltT_to_Qlt 0 b Hb).
      - apply Qabs_nonneg. }
    exact (qeq_lt_r (- b) (Qabs a) a (qeq_imp_qeqT (Qabs a) a Habs)
                        (Qlt_to_QltT (- b) (Qabs a) Hlowlt)).
  - assert (Hblt : Qlt (- b) 0) by (apply (Qopp_lt_compat 0 b); exact (QltT_to_Qlt 0 b Hb)).
    exact (qeq_lt_r (- b) 0 a (qeq_imp_qeqT 0 a (Qeq_sym a 0 Hc))
                        (Qlt_to_QltT (- b) 0 Hblt)).
Defined.

(* The Q-level congruence of the cosine partial sums (the term kit is   *)
(* ring-congruent through the q_pow setoid face q_pow_wd). *)
Lemma z03_sc_cos_term_congr : forall (j : nat) (x y : Q),
  QeqT x y -> QeqT (cos_term j x) (cos_term j y).
Proof.
  intros j x y H. unfold cos_term.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (q_pow_wd x y (2 * j) H)).
  ring.
Defined.

Lemma z03_sc_cos_partial_congr : forall (n : nat) (x y : Q),
  QeqT x y -> QeqT (cos_partial n x) (cos_partial n y).
Proof.
  intros n x y H. induction n as [| n IH]; simpl.
  - apply z03_sc_cos_term_congr. exact H.
  - apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ IH).
    rewrite (qeqT_imp_qeq _ _ (z03_sc_cos_term_congr (Datatypes.S n) x y H)).
    reflexivity.
Defined.
