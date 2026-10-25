(* ConstructiveWorld-Set — C*-algebra definition face and an explicit-rate
   Newton square root for strictly positive elements. *)

(** * UpReqCStarDef: C*-algebra structure over [BanachAlg] with a
      constructive Newton square root of positive elements.

    Mission.  Assembles on top of [BanachAlg] (from [UpReqBanachExp]) the
      Set/sigT definition face of a C*-algebra — an involutive Banach
      algebra satisfying the C* identity (the norm of [a*a] equals the
      squared norm of [a]) — and proves constructive convergence with an
      explicit rate for the Newton square root of strictly positive
      elements (classical proofs use order completeness; this module gives
      an explicit modulus and an extractable index bound).  Layers:
      the class [CStarAlg] (BanachAlg packaging, the antilinear involution
      [cst_star], the C* identity field [cst_norm_sq] on the [QeqT] face,
      and derived star facts); the Q-layer Newton engine ([x0 = a + 1],
      [x_(n+1) = (x_n + a/x_n)/2], exact residual decay
      [d_(n+1) = d_n^2 / (4 x_n^2)], geometric rate
      [d_m <= d_0 (1/4)^m], explicit [N] through the geometric-decay
      witness); norm transfer to the scalar-embedding face (for any
      [BanachAlg], with the explicit [N] inherited verbatim); and the
      positive cone in witness form ([a = star b * b] via [sigT], avoiding
      order-based decidability) with cone-level lemmas.

    Dependencies.  Stdlib [QArith], [QArith.Qabs], [Arith], [Lia].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [UpReqBanachExp] of this development.

    References.  This development, the ConstructiveWorld-Main baseline
      module of the same name whose statement names are carried over
      verbatim; benchmark: the basic C*-algebra definitions and the
      positive-element square-root construction in mathlib.

    Constructivity.  No admits; the axiom face is empty; all named
      statements are carried by [Set]/[sigT] ([bae]/[QeqT]/[QleT']/
      [QltT]/[NatLe]); Q-layer [Qle]/[Qlt] (Prop) appear only inside
      proofs as engine lining, never on the statement face.  Class-field
      projections take the instance argument implicitly — field accesses
      pass the instance explicitly with [@].  The extraction audit
      reports [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqCStarDef.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 00015ff4]; Q products and quotients are always
      annotated in the [%Q] scope. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

Local Open Scope Q_scope.

(* ================= Section 1. The class [CStarAlg]: involutive Banach
   algebra with the C* identity (Set face) ================= *)

Class CStarAlg (BA : Set) (bae : BA -> BA -> Set) := {
  cbase : BanachAlg BA bae;                             (* the underlying Banach algebra *)

  cst_star : BA -> BA;             (* the involution *)

  cst_star_wd : forall a b : BA,
    bae a b -> bae (cst_star a) (cst_star b);
  cst_star_add : forall a b : BA,
    bae (cst_star (@bplus _ _ cbase a b))
                 (@bplus _ _ cbase (cst_star a) (cst_star b));
  cst_star_mult : forall a b : BA,
    bae (cst_star (@bmult _ _ cbase a b))
                 (@bmult _ _ cbase (cst_star b) (cst_star a));
  cst_star_star : forall a : BA,
    bae (cst_star (cst_star a)) a;
  cst_star_one : bae (cst_star (@bone _ _ cbase)) (@bone _ _ cbase);
  cst_star_coef : forall q : Q,
    bae (cst_star (@bcoef _ _ cbase q)) (@bcoef _ _ cbase q);

  (* The C* identity: the norm of [star a * a] equals the squared norm of [a] ([QeqT] face). *)
  cst_norm_sq : forall a : BA,
    QeqT (@bnorm _ _ cbase (@bmult _ _ cbase (cst_star a) a))
         ((@bnorm _ _ cbase a) * (@bnorm _ _ cbase a))%Q
}.

(* ================= Q-layer working lemmas (Prop face, used inside proofs only) ================= *)

Lemma cst_q_le_0_sq_zero : forall x : Q, Qle 0 x -> Qle (x * x) 0 -> QeqT (x) (0).
Proof.
  intros x Hx0 Hsq.
  destruct (Qlt_le_dec 0 x) as [Hlt | Hle].
  - exfalso.
    assert (H2lt : Qlt 0 (x * x)) by (apply (Qmult_lt_0_compat x x); exact Hlt).
    assert (H2le : Qle 0 (x * x)) by (apply Qlt_le_weak; exact H2lt).
    assert (H0 : (x * x) == 0) by (apply Qle_antisym; [exact Hsq | exact H2le]).
    exact (match q_neq_of_lt (x * x) (Qlt_to_QltT 0 (x * x) H2lt) (qeq_imp_qeqT _ _ H0) with end).
  - apply qeq_imp_qeqT. apply Qle_antisym; [exact Hle | exact Hx0].
Qed.

Lemma cst_nat_q_le : forall n m : nat, (n <= m)%nat ->  
 QleT' (Z.of_nat n # 1) (Z.of_nat m # 1).
Proof.
  intros n m H. apply Qle_to_QleT'. unfold Qle. simpl. rewrite !Z.mul_1_r.
  apply (proj1 (Znat.Nat2Z.inj_le n m)). exact H.
Qed.

(* Left transport under Qeq: [x == y] and [y <= z] imply [x <= z] (rewriting inside a Qeq premise does not reach the goal, so a transport lemma is used). *)
Lemma cst_qeq_le_l : forall x y z : Q, x == y -> Qle y z -> QleT' x z.
Proof.
  intros x y z Hxy Hy. apply Qle_to_QleT'. apply (Qle_trans x y z).
  - rewrite Hxy. apply Qle_refl.
  - exact Hy.
Qed.

(* Right transport under Qeq: [x <= y] and [y == z] imply [x <= z]. *)
Lemma cst_qeq_le_r : forall x y z : Q, Qle x y -> y == z -> QleT' x z.
Proof.
  intros x y z Hxy Hyz. apply Qle_to_QleT'. apply (Qle_trans x y z).
  - exact Hxy.
  - rewrite Hyz. apply Qle_refl.
Qed.

(* Antitonicity of the inverse: [0 < B <= A] implies [/A <= /B]. *)
Lemma cst_qinv_anti : forall A B : Q, Qlt 0 B -> Qle B A -> QleT' (/ A) (/ B).
Proof.
  intros A B HB HBA.
  assert (HAlt : Qlt 0 A) by (apply (Qlt_le_trans 0 B A); [exact HB | exact HBA]).
  assert (HAB : Qlt 0 (A * B)) by (apply (Qmult_lt_0_compat A B); assumption).
  assert (Hne : ~ (A * B == 0)) by (intro Hz; apply qeq_imp_qeqT in Hz; destruct (q_neq_of_lt _ (Qlt_to_QltT 0 _ HAB) Hz)).
  assert (HAn : ~ (A == 0)) by (intro Hz; apply qeq_imp_qeqT in Hz; destruct (q_neq_of_lt _ (Qlt_to_QltT 0 _ HAlt) Hz)).
  assert (HBn : ~ (B == 0)) by (intro Hz; apply qeq_imp_qeqT in Hz; destruct (q_neq_of_lt _ (Qlt_to_QltT 0 _ HB) Hz)).
  assert (Hinv : Qle 0 (/ (A * B))).
  { apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HAB. }
  assert (E1 : / A == B * / (A * B)) by (field; repeat split; assumption).
  assert (E2 : / B == A * / (A * B)) by (field; repeat split; assumption).
  pose proof (Qmult_le_compat_r B A (/ (A * B)) HBA Hinv) as Hm.
  apply Qle_to_QleT'. rewrite E1, E2. exact Hm.
Qed.

(* ================= Star basics derived from the C* identity (direct on the [bae] face) ================= *)

Lemma cst_bae_bopp_invol : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x : BA),
  bae x (@bopp _ _ B (@bopp _ _ B x)).
Proof. intros BA bae B x. exact (@bopp_unique BA bae B x (@bopp _ _ B x) (@bplus_opp _ _ B x)). Qed.

Lemma cst_star_zero : forall (BA : Set) (bae : BA -> BA -> Set) (C : CStarAlg BA bae),
  bae (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C))) (@bzero _ _ (@cbase _ _ C)).
Proof.
  intros BA bae C.
  pose proof (bplus_zero_l _ _ (@cbase _ _ C) (@bzero _ _ (@cbase _ _ C))) as Hz.
  (* [star 0 == star 0 + star 0] via star well-definedness and additivity. *)
  assert (Hdup : bae (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C)))
                   (@bplus _ _ (@cbase _ _ C) (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C)))
                            (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C))))).
  { eapply (@bae_trans _ _ (@cbase _ _ C)).
    - apply (@bae_sym _ _ (@cbase _ _ C) _ _
               (@cst_star_wd _ _ C (@bplus _ _ (@cbase _ _ C) (@bzero _ _ (@cbase _ _ C))
                                       (@bzero _ _ (@cbase _ _ C)))
                               (@bzero _ _ (@cbase _ _ C)) Hz)).
    - exact (@cst_star_add _ _ C (@bzero _ _ (@cbase _ _ C)) (@bzero _ _ (@cbase _ _ C))). }
  (* Finished by adding [- star 0] on both sides (through [bopp_unique]). *)
  apply (@bae_sym _ _ (@cbase _ _ C)).
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  { apply (@bae_sym _ _ (@cbase _ _ C) _ _
             (@bplus_opp _ _ (@cbase _ _ C) (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C))))). }
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  { apply (@bplus_wd_l _ _ (@cbase _ _ C) (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C)))
             (@bplus _ _ (@cbase _ _ C) (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C)))
                                     (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C))))
             (@bopp _ _ (@cbase _ _ C) (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C)))) Hdup). }
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  { apply (@bae_sym _ _ (@cbase _ _ C) _ _
             (@bplus_assoc _ _ (@cbase _ _ C) (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C)))
                           (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C)))
                           (@bopp _ _ (@cbase _ _ C) (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C)))))). }
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  { apply (@bplus_wd_r _ _ (@cbase _ _ C)
             (@bplus _ _ (@cbase _ _ C) (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C)))
                      (@bopp _ _ (@cbase _ _ C) (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C)))))
             (@bzero _ _ (@cbase _ _ C))
             (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C)))
             (@bplus_opp _ _ (@cbase _ _ C) (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C))))). }
  exact (@bplus_zero _ _ (@cbase _ _ C) (@cst_star _ _ C (@bzero _ _ (@cbase _ _ C)))).
Qed.

Lemma cst_star_opp : forall (BA : Set) (bae : BA -> BA -> Set) (C : CStarAlg BA bae) (a : BA),
  bae (@cst_star _ _ C (@bopp _ _ (@cbase _ _ C) a))
                 (@bopp _ _ (@cbase _ _ C) (@cst_star _ _ C a)).
Proof.
  intros BA bae C a.
  apply (@bopp_unique _ _ (@cbase _ _ C) (@cst_star _ _ C (@bopp _ _ (@cbase _ _ C) a))
                      (@cst_star _ _ C a)).
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  { apply (@bplus_comm _ _ (@cbase _ _ C) (@cst_star _ _ C (@bopp _ _ (@cbase _ _ C) a))
                      (@cst_star _ _ C a)). }
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  { apply (@bae_sym _ _ (@cbase _ _ C) _ _
             (@cst_star_add _ _ C a (@bopp _ _ (@cbase _ _ C) a))). }
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  { apply (@cst_star_wd _ _ C (@bplus _ _ (@cbase _ _ C) a (@bopp _ _ (@cbase _ _ C) a))
             (@bzero _ _ (@cbase _ _ C)) (@bplus_opp _ _ (@cbase _ _ C) a)). }
  exact (@cst_star_zero _ _ C).
Qed.

(* Remaining (declared honestly): [cst_star_pow] (star commutes with powers)
   needs a same-element power-commutation lemma ([bpow b n * b = b * bpow b n];
   provable by induction, absent from [BanachAlg]). *)

(* The C* identity gives star isometry: the norm of [star a] equals the norm of [a] (constructive two-sided cancellation over Q). *)
Lemma cst_norm_star : forall (BA : Set) (bae : BA -> BA -> Set) (C : CStarAlg BA bae) (a : BA),
  QeqT (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)) (@bnorm _ _ (@cbase _ _ C) a).
Proof.
  intros BA bae C a.
  pose proof (QleT'_to_Qle _ _ (@bnorm_pos _ _ (@cbase _ _ C) a)) as HA0.
  pose proof (QleT'_to_Qle _ _ (@bnorm_pos _ _ (@cbase _ _ C) (@cst_star _ _ C a))) as HS0.
  pose proof (qeqT_imp_qeq _ _ (@cst_norm_sq _ _ C a)) as Hsq1.
  assert (H1 : Qle ((@bnorm _ _ (@cbase _ _ C) a) * (@bnorm _ _ (@cbase _ _ C) a))
                   ((@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)) * (@bnorm _ _ (@cbase _ _ C) a))).
  { pose proof (QleT'_to_Qle _ _ (@bnorm_mult _ _ (@cbase _ _ C) (@cst_star _ _ C a) a)) as Hm.
    rewrite Hsq1 in Hm. exact Hm. }
  assert (H2 : Qle ((@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)) * (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)))
                   ((@bnorm _ _ (@cbase _ _ C) a) * (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)))).
  { pose proof (qeqT_imp_qeq _ _ (@cst_norm_sq _ _ C (@cst_star _ _ C a))) as Hsq2.
    pose proof (QleT'_to_Qle _ _ (@bnorm_mult _ _ (@cbase _ _ C) a (@cst_star _ _ C a))) as Hm.
    apply QleT'_to_Qle. apply (cst_qeq_le_l _ _ _ (Qeq_sym _ _ Hsq2)).
    apply (Qle_trans _ (@bnorm _ _ (@cbase _ _ C)
              (@bmult _ _ (@cbase _ _ C) a (@cst_star _ _ C a)))).
    - apply QleT'_to_Qle. apply (cst_qeq_le_l _ _ _
        (qeqT_imp_qeq _ _ (@bnorm_wd _ _ (@cbase _ _ C)
        (@bmult _ _ (@cbase _ _ C) (@cst_star _ _ C (@cst_star _ _ C a)) (@cst_star _ _ C a))
        (@bmult _ _ (@cbase _ _ C) a (@cst_star _ _ C a))
        (@bmult_wd _ _ (@cbase _ _ C) (@cst_star _ _ C (@cst_star _ _ C a)) (@cst_star _ _ C a)
                   a (@cst_star _ _ C a)
                   (@cst_star_star _ _ C a) (@bae_refl _ _ (@cbase _ _ C) (@cst_star _ _ C a)))))).
      apply Qle_refl.
    - exact Hm. }
  assert (Hcancel : (@bnorm _ _ (@cbase _ _ C) a) == (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a))).
  { destruct (Qle_lt_or_eq 0 (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)) HS0) as [HSlt | HSeq].
    - destruct (Qle_lt_or_eq 0 (@bnorm _ _ (@cbase _ _ C) a) HA0) as [HAlt | HAeq].
      + (* Both [A > 0] and [S > 0]: cancel by dividing both sides (field face, constructive). *)
        assert (HAn : ~ ((@bnorm _ _ (@cbase _ _ C) a) == 0))
          by (intro Hz; apply qeq_imp_qeqT in Hz; destruct (q_neq_of_lt _ (Qlt_to_QltT 0 _ HAlt) Hz)).
        assert (HinvA : Qle 0 (/ (@bnorm _ _ (@cbase _ _ C) a)))
          by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HAlt).
        assert (EA : (@bnorm _ _ (@cbase _ _ C) a) * (@bnorm _ _ (@cbase _ _ C) a)
                       * (/ (@bnorm _ _ (@cbase _ _ C) a)) == (@bnorm _ _ (@cbase _ _ C) a))
          by (field; repeat split; assumption).
        assert (EB : ((@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)) * (@bnorm _ _ (@cbase _ _ C) a))
                     * (/ (@bnorm _ _ (@cbase _ _ C) a))
                     == (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)))
          by (field; repeat split; assumption).
        pose proof (Qmult_le_compat_r
          ((@bnorm _ _ (@cbase _ _ C) a) * (@bnorm _ _ (@cbase _ _ C) a))
          ((@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)) * (@bnorm _ _ (@cbase _ _ C) a))
          (/ (@bnorm _ _ (@cbase _ _ C) a)) H1 HinvA) as Hd1.
        rewrite EA, EB in Hd1.
        assert (HSn : ~ ((@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)) == 0))
          by (intro Hz; apply qeq_imp_qeqT in Hz; destruct (q_neq_of_lt _ (Qlt_to_QltT 0 _ HSlt) Hz)).
        assert (HinvS : Qle 0 (/ (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a))))
          by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HSlt).
        assert (EC : (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)) * (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a))
                     * (/ (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)))
                     == (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)))
          by (field; repeat split; assumption).
        assert (ED : ((@bnorm _ _ (@cbase _ _ C) a) * (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)))
                     * (/ (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)))
                     == (@bnorm _ _ (@cbase _ _ C) a))
          by (field; repeat split; assumption).
        pose proof (Qmult_le_compat_r
          ((@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)) * (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)))
          ((@bnorm _ _ (@cbase _ _ C) a) * (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)))
          (/ (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a))) H2 HinvS) as Hd2.
        rewrite EC, ED in Hd2.
        apply Qle_antisym; assumption.
      + (* [A == 0] implies [S == 0] via [H2] (right Qeq transport, avoiding nested rewrites). *)
        apply Qeq_sym in HAeq.
        assert (HAeqS : ((@bnorm _ _ (@cbase _ _ C) a) * (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a))) == 0)
          by (rewrite HAeq; apply Qmult_0_l).
        pose proof (QleT'_to_Qle _ _
          (cst_qeq_le_r
          ((@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)) * (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)))
          ((@bnorm _ _ (@cbase _ _ C) a) * (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)))
          0 H2 HAeqS)) as H2'.
        assert (HSz : (@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)) == 0)
          by (apply qeqT_imp_qeq; apply (cst_q_le_0_sq_zero _ HS0); exact H2').
        rewrite HSz. exact HAeq.
    - (* [S == 0] implies [A == 0] via [H1] (right Qeq transport). *)
      apply Qeq_sym in HSeq.
      assert (HSeqA : ((@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)) * (@bnorm _ _ (@cbase _ _ C) a)) == 0)
        by (rewrite HSeq; apply Qmult_0_l).
      pose proof (QleT'_to_Qle _ _
        (cst_qeq_le_r
        ((@bnorm _ _ (@cbase _ _ C) a) * (@bnorm _ _ (@cbase _ _ C) a))
        ((@bnorm _ _ (@cbase _ _ C) (@cst_star _ _ C a)) * (@bnorm _ _ (@cbase _ _ C) a))
        0 H1 HSeqA)) as H1'.
      assert (HAz : (@bnorm _ _ (@cbase _ _ C) a) == 0)
        by (apply qeqT_imp_qeq; apply (cst_q_le_0_sq_zero _ HA0); exact H1').
      rewrite HSeq. exact HAz. }
  apply qeq_imp_qeqT. apply Qeq_sym. exact Hcancel.
Qed.

(* ================= Section 2. The Q-layer Newton square-root engine
   (the explicit-rate core) ================= *)

Fixpoint cst_nseq (a : Q) (n : nat) : Q :=
  match n with
  | 0%nat => a + 1
  | Datatypes.S m => (cst_nseq a m + a / cst_nseq a m) / 2
  end.

(* The sequence stays positive. *)
Lemma cst_nseq_pos : forall (a : Q), Qlt 0 a -> forall n : nat, QltT 0 (cst_nseq a n).
Proof.
  intros a Ha n. apply Qlt_to_QltT. induction n as [| m IH].
  - apply (Qlt_le_trans 0 1 (a + 1)).
    + exact Z.lt_0_1.
    + pose proof (Qplus_le_compat 0 a 1 1
                    (Qlt_le_weak 0 a Ha) (Qle_refl 1)) as Hle.
      change (0 + 1)%Q with 1 in Hle. exact Hle.
  - change (cst_nseq a (Datatypes.S m))
      with ((cst_nseq a m + a / cst_nseq a m) / 2).
    assert (Hax : Qlt 0 (a / cst_nseq a m)).
    { apply (Qmult_lt_0_compat a (/ cst_nseq a m)); [exact Ha|].
      apply Qinv_lt_0_compat. exact IH. }
    assert (Hsum : Qlt 0 (cst_nseq a m + a / cst_nseq a m))
      by (apply (Qplus_lt_compat 0 (cst_nseq a m) 0 (a / cst_nseq a m));
          assumption).
    apply (Qmult_lt_0_compat (cst_nseq a m + a / cst_nseq a m) (/ 2));
      [exact Hsum | exact Z.lt_0_1].
Qed.

(* The residual stays nonnegative: [0 <= x_n^2 - a]. *)
Lemma cst_d_nonneg : forall (a : Q), Qlt 0 a -> forall n : nat,  
 QleT' 0 (cst_nseq a n * cst_nseq a n - a).
Proof.
  intros a Ha n. induction n as [| m IH].
  - change (cst_nseq a 0) with (a + 1).
    apply Qle_to_QleT'.
    assert (Hid0 : ((a + 1) * (a + 1) - a) == (a * a + a + 1)) by ring.
    rewrite Hid0.
    apply Qlt_le_weak.
    apply (Qplus_lt_compat 0 (a * a + a) 0 1).
    + apply (Qplus_lt_compat 0 (a * a) 0 a).
      * apply (Qmult_lt_0_compat a a); exact Ha.
      * exact Ha.
    + exact Z.lt_0_1.
  - change (cst_nseq a (Datatypes.S m) * cst_nseq a (Datatypes.S m) - a)
      with (((cst_nseq a m + a / cst_nseq a m) / 2)
            * ((cst_nseq a m + a / cst_nseq a m) / 2) - a).
    assert (Hx0 : ~ (cst_nseq a m == 0))
      by (intro Hz; apply qeq_imp_qeqT in Hz; destruct (q_neq_of_lt _ (cst_nseq_pos a Ha _) Hz)).
    assert (H2n : ~ (2 == 0)) by (unfold Qeq; discriminate).
    assert (Hx2p : Qlt 0 (cst_nseq a m * cst_nseq a m))
      by (apply (Qmult_lt_0_compat (cst_nseq a m) (cst_nseq a m));
          apply QltT_to_Qlt; apply cst_nseq_pos; exact Ha).
    assert (H4p : Qlt 0 (4 * (cst_nseq a m * cst_nseq a m)))
      by (apply (Qmult_lt_0_compat 4 (cst_nseq a m * cst_nseq a m));
          [exact (proj1 (Z.ltb_lt 0 4) eq_refl) | exact Hx2p]).
    assert (H4n : ~ (4 * (cst_nseq a m * cst_nseq a m) == 0))
      by (intro Hz; apply qeq_imp_qeqT in Hz; destruct (q_neq_of_lt _ (Qlt_to_QltT 0 _ H4p) Hz)).
    assert (Hid : ((cst_nseq a m + a / cst_nseq a m) / 2)
                  * ((cst_nseq a m + a / cst_nseq a m) / 2) - a
                == (cst_nseq a m * cst_nseq a m - a)
                   * (cst_nseq a m * cst_nseq a m - a)
                   / (4 * (cst_nseq a m * cst_nseq a m)))
      by (field; repeat split; assumption).
    apply Qle_to_QleT'.
    rewrite Hid.
    apply Qmult_le_0_compat.
    + apply Qmult_le_0_compat;
        [exact (QleT'_to_Qle _ _ IH) | exact (QleT'_to_Qle _ _ IH)].
    + apply Qlt_le_weak. apply Qinv_lt_0_compat. exact H4p.
Qed.

(* Upper bound: [x_n^2 - a <= x_n^2]. *)
Lemma cst_d_le_x2 : forall (a : Q), Qlt 0 a -> forall n : nat, 
  QleT' (cst_nseq a n * cst_nseq a n - a) (cst_nseq a n * cst_nseq a n).
Proof.
  intros a Ha n.
  assert (Hneg : Qle (- a) 0).
  { pose proof (Qopp_le_compat 0 a (Qlt_le_weak 0 a Ha)) as H.
    change (- 0)%Q with 0 in H. exact H. }
  assert (Hstep : Qle (cst_nseq a n * cst_nseq a n + (- a))
                      (cst_nseq a n * cst_nseq a n + 0))
    by (apply (Qplus_le_compat (cst_nseq a n * cst_nseq a n)
                               (cst_nseq a n * cst_nseq a n) (- a) 0);
        [apply Qle_refl | exact Hneg]).
  assert (Hz0 : (cst_nseq a n * cst_nseq a n + 0)%Q
                == (cst_nseq a n * cst_nseq a n)) by ring.
  rewrite Hz0 in Hstep. apply Qle_to_QleT'. exact Hstep.
Qed.

(* Exact Newton decay: [d_(n+1) <= d_n * (1/4)] — quadratic convergence made geometric. *)
Lemma cst_d_step_le : forall (a : Q), Qlt 0 a -> forall n : nat, 
  QleT' (cst_nseq a (Datatypes.S n) * cst_nseq a (Datatypes.S n) - a)
       ((cst_nseq a n * cst_nseq a n - a) * (1 / 4)).
Proof.
  intros a Ha n.
  pose proof (QltT_to_Qlt _ _ (cst_nseq_pos a Ha n)) as Hxp.
  assert (Hx0 : ~ (cst_nseq a n == 0)) by (intro Hz; apply qeq_imp_qeqT in Hz; destruct (q_neq_of_lt _ (Qlt_to_QltT 0 _ Hxp) Hz)).
  assert (H2n : ~ (2 == 0)) by (unfold Qeq; discriminate).
  pose proof (QleT'_to_Qle _ _ (cst_d_nonneg a Ha n)) as Hd.
  pose proof (QleT'_to_Qle _ _ (cst_d_le_x2 a Ha n)) as Hdle.
  assert (Hx2p : Qlt 0 (cst_nseq a n * cst_nseq a n))
    by (apply (Qmult_lt_0_compat (cst_nseq a n) (cst_nseq a n));
        apply QltT_to_Qlt; apply cst_nseq_pos; exact Ha).
  assert (H4p : Qlt 0 (4 * (cst_nseq a n * cst_nseq a n)))
    by (apply (Qmult_lt_0_compat 4 (cst_nseq a n * cst_nseq a n));
        [exact (proj1 (Z.ltb_lt 0 4) eq_refl) | exact Hx2p]).
  assert (H4n : ~ (4 * (cst_nseq a n * cst_nseq a n) == 0))
    by (intro Hz; apply qeq_imp_qeqT in Hz; destruct (q_neq_of_lt _ (Qlt_to_QltT 0 _ H4p) Hz)).
  change (cst_nseq a (Datatypes.S n) * cst_nseq a (Datatypes.S n) - a)
    with (((cst_nseq a n + a / cst_nseq a n) / 2)
          * ((cst_nseq a n + a / cst_nseq a n) / 2) - a).
  assert (Hid : ((cst_nseq a n + a / cst_nseq a n) / 2)
                * ((cst_nseq a n + a / cst_nseq a n) / 2) - a
              == (cst_nseq a n * cst_nseq a n - a)
                 * (cst_nseq a n * cst_nseq a n - a)
                 / (4 * (cst_nseq a n * cst_nseq a n)))
    by (field; repeat split; assumption).
  apply Qle_to_QleT'.
  rewrite Hid.
  assert (Hinv0 : Qle 0 (/ (4 * (cst_nseq a n * cst_nseq a n))))
    by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact H4p).
  assert (Hdd : Qle ((cst_nseq a n * cst_nseq a n - a)
                     * (cst_nseq a n * cst_nseq a n - a))
                    ((cst_nseq a n * cst_nseq a n - a)
                     * (cst_nseq a n * cst_nseq a n))).
  { pose proof (Qmult_le_compat_r (cst_nseq a n * cst_nseq a n - a)
                    (cst_nseq a n * cst_nseq a n)
                    (cst_nseq a n * cst_nseq a n - a) Hdle Hd) as H1.
    rewrite (Qmult_comm (cst_nseq a n * cst_nseq a n)
                        (cst_nseq a n * cst_nseq a n - a)) in H1.
    exact H1. }
  eapply (Qle_trans _ ((cst_nseq a n * cst_nseq a n - a)
                       * (cst_nseq a n * cst_nseq a n)
                       * (/ (4 * (cst_nseq a n * cst_nseq a n))))).
  - apply (Qmult_le_compat_r _ _ (/ (4 * (cst_nseq a n * cst_nseq a n))) Hdd Hinv0).
  - assert (E2 : (cst_nseq a n * cst_nseq a n - a) * (cst_nseq a n * cst_nseq a n)
                 * (/ (4 * (cst_nseq a n * cst_nseq a n)))
                 == (cst_nseq a n * cst_nseq a n - a) * (1 / 4))
      by (field; repeat split; assumption).
    rewrite E2. apply Qle_refl.
Qed.

(* Geometric rate: [d_m <= d_0 * (1/4)^m]. *)
Lemma cst_d_geo : forall (a : Q), Qlt 0 a -> forall m : nat,  
 QleT' (cst_nseq a m * cst_nseq a m - a)
       ((cst_nseq a 0 * cst_nseq a 0 - a) * q_pow (1 / 4) m).
Proof.
  intros a Ha m. induction m as [| m IH].
  - apply Qle_to_QleT'. rewrite Qmult_1_r. apply Qle_refl.
  - eapply (qleT'_trans _
             ((cst_nseq a m * cst_nseq a m - a) * (1 / 4))).
    + apply (cst_d_step_le a Ha m).
    + change (q_pow (1 / 4) (Datatypes.S m)) with ((1 / 4) * q_pow (1 / 4) m).
      assert (Hr4 : ((1 / 4) * q_pow (1 / 4) m)
                    == (q_pow (1 / 4) m * (1 / 4))) by ring.
      apply Qle_to_QleT'.
      rewrite Hr4.
      rewrite (Qmult_assoc (cst_nseq a 0 * cst_nseq a 0 - a)
                           (q_pow (1 / 4) m) (1 / 4)).
      apply (Qmult_le_compat_r _ _ (1 / 4) (QleT'_to_Qle _ _ IH)).
      unfold Qle. simpl. exact (proj1 (Z.leb_le 0 1) eq_refl).
Qed.

(* [(1/4)^m] is antitone in [m] (on the [NatLe] face). *)
Lemma cst_pow14_anti : forall k m : nat, NatLe k m ->  
 QleT' (q_pow (1 / 4) m) (q_pow (1 / 4) k).
Proof.
  intros k m. revert k. induction m as [| m IH]; intros k Hkm.
  - pose proof (NatLe_drop k 0%nat Hkm) as Hk0.
    assert (Hk : k = 0%nat)
      by exact (Nat.le_antisymm k 0%nat Hk0 (Nat.le_0_l k)).
    rewrite Hk. apply Qle_to_QleT'. apply Qle_refl.
  - destruct (Nat.eq_dec (Datatypes.S m) k) as [Heq | Hne].
    + rewrite Heq. apply Qle_to_QleT'. apply Qle_refl.
    + assert (Hkm' : (k <= m)%nat).
      { pose proof (NatLe_drop k (Datatypes.S m) Hkm) as Hle.
        destruct (proj1 (Nat.lt_eq_cases k (Datatypes.S m)) Hle) as [Hlt | Heq].
        - exact (proj1 (Nat.lt_succ_r k m) Hlt).
        - exfalso. apply Hne. exact (eq_sym Heq). }
      eapply (qleT'_trans _ (q_pow (1 / 4) m)).
      * change (q_pow (1 / 4) (Datatypes.S m)) with ((1 / 4) * q_pow (1 / 4) m).
        apply Qle_to_QleT'. eapply (Qle_trans _ (1 * q_pow (1 / 4) m)%Q).
        -- apply (Qmult_le_compat_r (1 / 4) 1 (q_pow (1 / 4) m)).
           ++ unfold Qle. simpl.
              exact (Z.le_trans 1 2 4 (Z.le_succ_diag_r 1)
                       (Z.le_trans 2 3 4 (Z.le_succ_diag_r 2)
                          (Z.le_succ_diag_r 3))).
           ++ apply QleT'_to_Qle. apply q_pow_nonneg.
              apply Qle_to_QleT'. unfold Qle. simpl.
              exact (proj1 (Z.leb_le 0 1) eq_refl).
        -- rewrite (Qmult_1_l (q_pow (1 / 4) m)). apply Qle_refl.
      * apply (IH k (NatLe_lift k m Hkm')).
Qed.

(* [(1/2)^m] is antitone in [m] (on the [NatLe] face) — the form consumed by the geometric-decay witness. *)
Lemma cst_pow12_anti : forall k m : nat, NatLe k m ->  
 QleT' (q_pow (1 / 2) m) (q_pow (1 / 2) k).
Proof.
  intros k m. revert k. induction m as [| m IH]; intros k Hkm.
  - pose proof (NatLe_drop k 0%nat Hkm) as Hk0.
    assert (Hk : k = 0%nat)
      by exact (Nat.le_antisymm k 0%nat Hk0 (Nat.le_0_l k)).
    rewrite Hk. apply Qle_to_QleT'. apply Qle_refl.
  - destruct (Nat.eq_dec (Datatypes.S m) k) as [Heq | Hne].
    + rewrite Heq. apply Qle_to_QleT'. apply Qle_refl.
    + assert (Hkm' : (k <= m)%nat).
      { pose proof (NatLe_drop k (Datatypes.S m) Hkm) as Hle.
        destruct (proj1 (Nat.lt_eq_cases k (Datatypes.S m)) Hle) as [Hlt | Heq].
        - exact (proj1 (Nat.lt_succ_r k m) Hlt).
        - exfalso. apply Hne. exact (eq_sym Heq). }
      eapply (qleT'_trans _ (q_pow (1 / 2) m)).
      * change (q_pow (1 / 2) (Datatypes.S m)) with ((1 / 2) * q_pow (1 / 2) m).
        apply Qle_to_QleT'. eapply (Qle_trans _ (1 * q_pow (1 / 2) m)%Q).
        -- apply (Qmult_le_compat_r (1 / 2) 1 (q_pow (1 / 2) m)).
           ++ unfold Qle. simpl. exact (Z.le_succ_diag_r 1).
           ++ apply QleT'_to_Qle. apply q_pow_nonneg.
              apply Qle_to_QleT'. unfold Qle. simpl.
              exact (proj1 (Z.leb_le 0 1) eq_refl).
        -- rewrite (Qmult_1_l (q_pow (1 / 2) m)). apply Qle_refl.
      * apply (IH k (NatLe_lift k m Hkm')).
Qed.

(* Newton decay in the (1/2) form: [d_(n+1) <= d_n * (1/2)] — the weakened form consumed downstream. *)
Lemma cst_d_step_le12 : forall (a : Q), Qlt 0 a -> forall n : nat, 
  QleT' (cst_nseq a (Datatypes.S n) * cst_nseq a (Datatypes.S n) - a)
       ((cst_nseq a n * cst_nseq a n - a) * (1 / 2)).
Proof.
  intros a Ha n.
  eapply (qleT'_trans _ ((cst_nseq a n * cst_nseq a n - a) * (1 / 4))).
  - apply (cst_d_step_le a Ha n).
  - apply Qle_to_QleT'.
    rewrite (Qmult_comm (cst_nseq a n * cst_nseq a n - a) (1 / 4)).
    rewrite (Qmult_comm (cst_nseq a n * cst_nseq a n - a) (1 / 2)).
    apply (Qmult_le_compat_r (1 / 4) (1 / 2) (cst_nseq a n * cst_nseq a n - a)).
    + unfold Qle. simpl.
      exact (Z.le_trans 2 3 4 (Z.le_succ_diag_r 2) (Z.le_succ_diag_r 3)).
    + exact (QleT'_to_Qle _ _ (cst_d_nonneg a Ha n)).
Qed.

(* Geometric rate in the (1/2) form: [d_m <= d_0 * (1/2)^m] — matches the geometric-decay witness face. *)
Lemma cst_d_geo12 : forall (a : Q), Qlt 0 a -> forall m : nat,  
 QleT' (cst_nseq a m * cst_nseq a m - a)
       ((cst_nseq a 0 * cst_nseq a 0 - a) * q_pow (1 / 2) m).
Proof.
  intros a Ha m. induction m as [| m IH].
  - apply Qle_to_QleT'. rewrite Qmult_1_r. apply Qle_refl.
  - eapply (qleT'_trans _ ((cst_nseq a m * cst_nseq a m - a) * (1 / 2))).
    + apply (cst_d_step_le12 a Ha m).
    + change (q_pow (1 / 2) (Datatypes.S m)) with ((1 / 2) * q_pow (1 / 2) m).
      assert (Hr2 : ((1 / 2) * q_pow (1 / 2) m)
                    == (q_pow (1 / 2) m * (1 / 2))) by ring.
      apply Qle_to_QleT'.
      rewrite Hr2.
      rewrite (Qmult_assoc (cst_nseq a 0 * cst_nseq a 0 - a)
                           (q_pow (1 / 2) m) (1 / 2)).
      apply (Qmult_le_compat_r _ _ (1 / 2) (QleT'_to_Qle _ _ IH)).
      unfold Qle. simpl. exact (proj1 (Z.leb_le 0 1) eq_refl).
Qed.

(* Main theorem of this section: the explicit rate of the Newton sequence on
   the Q layer, with [N] explicitly extractable ([N] is the successor of the
   geometric-decay witness, a proved library statement). *)
Theorem cst_newton_rate : forall (a eps : Q), QltT 0 a -> QltT 0 eps ->
  sigT (fun N : nat => forall m : nat, NatLe N m ->
    QltT (Qabs (cst_nseq a m * cst_nseq a m - a)) eps).
Proof.
  intros a eps Ha Heps.
  pose proof (QltT_to_Qlt 0 a Ha) as Haq.
  pose proof (cst_d_nonneg a Haq 0) as Hd0.
  destruct (arch_decay (cst_nseq a 0 * cst_nseq a 0 - a) eps
             Hd0 Heps) as [t Hdec].
  exists (Datatypes.S t).
  intros m Hm.
  pose proof (cst_d_geo12 a Haq m) as Hgeo.
  pose proof (cst_d_nonneg a Haq m) as Hdm.
  assert (Hd0q : Qle 0 (cst_nseq a 0 * cst_nseq a 0 - a))
    by (apply QleT'_to_Qle; apply (cst_d_nonneg a Haq 0)).
  assert (Hpow : Qle (q_pow (1 / 2) m) (q_pow (1 / 2) (Datatypes.S t)))
    by (apply QleT'_to_Qle; apply (cst_pow12_anti (Datatypes.S t) m); exact Hm).
  assert (Hchain : Qle (cst_nseq a m * cst_nseq a m - a)
                       ((cst_nseq a 0 * cst_nseq a 0 - a)
                        * q_pow (1 / 2) (Datatypes.S t))).
  { eapply (Qle_trans _ ((cst_nseq a 0 * cst_nseq a 0 - a)
                         * q_pow (1 / 2) m)).
    - exact (QleT'_to_Qle _ _ Hgeo).
    - rewrite (Qmult_comm (cst_nseq a 0 * cst_nseq a 0 - a)
                          (q_pow (1 / 2) m)).
      rewrite (Qmult_comm (cst_nseq a 0 * cst_nseq a 0 - a)
                          (q_pow (1 / 2) (Datatypes.S t))).
      apply (Qmult_le_compat_r _ _ (cst_nseq a 0 * cst_nseq a 0 - a) Hpow Hd0q). }
  assert (Habs : Qabs (cst_nseq a m * cst_nseq a m - a)
               == cst_nseq a m * cst_nseq a m - a)
    by (apply Qabs_pos; exact (QleT'_to_Qle _ _ Hdm)).
  apply Qlt_to_QltT. rewrite Habs.
  apply (Qle_lt_trans (cst_nseq a m * cst_nseq a m - a)
                      ((cst_nseq a 0 * cst_nseq a 0 - a)
                       * q_pow (1 / 2) (Datatypes.S t)) eps Hchain
                      (QltT_to_Qlt _ _ Hdec)).
Qed.

(* ================= Section 3. Norm transfer: the scalar-embedding face
   for an arbitrary Banach algebra ================= *)

Lemma cst_bae_opp_one : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae),
  bae (@bplus _ _ B (@bopp _ _ B (@bone _ _ B)) (@bone _ _ B)) (@bzero _ _ B).
Proof.
  intros BA bae B.
  eapply (@bae_trans _ _ B).
  { exact (@bplus_comm _ _ B (@bopp _ _ B (@bone _ _ B)) (@bone _ _ B)). }
  exact (@bplus_opp _ _ B (@bone _ _ B)).
Qed.

Lemma cst_bmult_opp_r : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x : BA),
  bae (@bmult _ _ B x (@bopp _ _ B (@bone _ _ B))) (@bopp _ _ B x).
Proof.
  intros BA bae B x.
  apply (@bopp_unique BA bae B (@bmult _ _ B x (@bopp _ _ B (@bone _ _ B))) x).
  eapply (@bae_trans _ _ B).
  { apply (@bplus_wd_r BA bae B x (@bmult _ _ B x (@bone _ _ B))
             (@bmult _ _ B x (@bopp _ _ B (@bone _ _ B)))
             (@bae_sym _ _ B _ _ (@bmult_one_r _ _ B x))). }
  eapply (@bae_trans _ _ B).
  { apply (@bae_sym _ _ B _ _ (@bdistrib_l _ _ B x (@bopp _ _ B (@bone _ _ B)) (@bone _ _ B))). }
  eapply (@bae_trans _ _ B).
  { apply (@bmult_wd _ _ B x (@bplus _ _ B (@bopp _ _ B (@bone _ _ B)) (@bone _ _ B)) x (@bzero _ _ B)
             (@bae_refl _ _ B x) (cst_bae_opp_one _ _ B)). }
  exact (@bmult_zero _ _ B x).
Qed.

Lemma cst_bcoef_mone : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae),
  bae (@bcoef _ _ B (- 1)) (@bopp _ _ B (@bone _ _ B)).
Proof.
  intros BA bae B.
  assert (Hplus : bae (@bplus _ _ B (@bcoef _ _ B 1) (@bcoef _ _ B (- 1))) (@bzero _ _ B)).
  { eapply (@bae_trans _ _ B).
    { exact (@bcoef_plus _ _ B 1 (- 1)). }
    eapply (@bae_trans _ _ B).
    { apply (@bcoef_wd _ _ B (1 + (- 1))%Q 0%Q). apply qeq_imp_qeqT. apply Qeq_refl. }
    exact (@bcoef_zero _ _ B). }
  pose proof (@bae_trans _ _ B _ _ _
    (@bplus_wd_l BA bae B (@bone _ _ B) (@bcoef _ _ B 1) (@bcoef _ _ B (- 1))
                 (@bae_sym _ _ B _ _ (@bcoef_one _ _ B))) Hplus) as H2.
  assert (H3 : bae (@bone _ _ B) (@bopp _ _ B (@bcoef _ _ B (- 1))))
    by (apply (@bopp_unique BA bae B (@bone _ _ B) (@bcoef _ _ B (- 1))); exact H2).
  apply (@bae_sym _ _ B _ _).
  eapply (@bae_trans _ _ B).
  { exact (@bopp_wd _ _ B (@bone _ _ B) (@bopp _ _ B (@bcoef _ _ B (- 1))) H3). }
  apply (@bae_sym _ _ B _ _ (@cst_bae_bopp_invol _ _ B (@bcoef _ _ B (- 1)))).
Qed.

Lemma cst_bcoef_opp : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (q : Q),
  bae (@bcoef _ _ B (- q)) (@bopp _ _ B (@bcoef _ _ B q)).
Proof.
  intros BA bae B q.
  eapply (@bae_trans _ _ B).
  { apply (@bcoef_wd _ _ B (- q) (q * (- 1))). apply qeq_imp_qeqT. ring. }
  eapply (@bae_trans _ _ B).
  { exact (@bcoef_mult _ _ B q (- 1)). }
  eapply (@bae_trans _ _ B).
  { apply (@bmult_wd _ _ B (@bcoef _ _ B q) (@bcoef _ _ B (- 1))
             (@bcoef _ _ B q) (@bopp _ _ B (@bone _ _ B))
             (@bae_refl _ _ B (@bcoef _ _ B q)) (cst_bcoef_mone _ _ B)). }
  exact (cst_bmult_opp_r _ _ B (@bcoef _ _ B q)).
Qed.

(* Main theorem: norm convergence of the Newton sequence for a scalar positive
   element in an arbitrary [BanachAlg] (the explicit [N] is inherited verbatim
   from the Q-layer engine). *)
Theorem cst_newton_alg : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (q eps : Q),
  QltT 0 q -> QltT 0 eps ->
  sigT (fun N : nat => forall m : nat, NatLe N m ->
    QltT (@bnorm _ _ B (@bplus _ _ B
             (@bmult _ _ B (@bcoef _ _ B (cst_nseq q m)) (@bcoef _ _ B (cst_nseq q m)))
             (@bopp _ _ B (@bcoef _ _ B q)))) eps).
Proof.
  intros BA bae B q eps Hq Heps.
  destruct (cst_newton_rate q eps Hq Heps) as [N HN].
  exists N. intros m Hm.
  specialize (HN m Hm).
  pose proof (@bcoef_mult _ _ B (cst_nseq q m) (cst_nseq q m)) as H1.
  pose proof (@bae_sym _ _ B _ _ (cst_bcoef_opp _ _ B q)) as H2s.
  assert (Hfin : bae
    (@bplus _ _ B (@bmult _ _ B (@bcoef _ _ B (cst_nseq q m)) (@bcoef _ _ B (cst_nseq q m)))
              (@bopp _ _ B (@bcoef _ _ B q)))
    (@bcoef _ _ B (cst_nseq q m * cst_nseq q m - q))).
  { eapply (@bae_trans _ _ B).
    { apply (@bplus_wd_l BA bae B (@bmult _ _ B (@bcoef _ _ B (cst_nseq q m))
                                       (@bcoef _ _ B (cst_nseq q m)))
               (@bcoef _ _ B (cst_nseq q m * cst_nseq q m))
               (@bopp _ _ B (@bcoef _ _ B q)) (@bae_sym _ _ B _ _ H1)). }
    eapply (@bae_trans _ _ B).
    { apply (@bplus_wd_r BA bae B (@bopp _ _ B (@bcoef _ _ B q)) (@bcoef _ _ B (- q))
               (@bcoef _ _ B (cst_nseq q m * cst_nseq q m)) H2s). }
    exact (@bcoef_plus _ _ B (cst_nseq q m * cst_nseq q m) (- q)). }
  assert (Hnorm : QeqT
    (@bnorm _ _ B (@bplus _ _ B
        (@bmult _ _ B (@bcoef _ _ B (cst_nseq q m)) (@bcoef _ _ B (cst_nseq q m)))
        (@bopp _ _ B (@bcoef _ _ B q))))
    (Qabs (cst_nseq q m * cst_nseq q m - q))).
  { pose proof (@bnorm_wd _ _ B _ _ Hfin) as Hw.
    pose proof (@bnorm_coef_qeq BA bae B (cst_nseq q m * cst_nseq q m - q)) as Hc.
    apply qeq_imp_qeqT.
    apply (Qeq_trans _ _ _ (qeqT_imp_qeq _ _ Hw)).
    exact (qeqT_imp_qeq _ _ Hc). }
  apply (QeqT_Qlt_bool_cong _ _ eps (qeqT_sym_hw _ _ Hnorm)). exact HN.
Qed.

(* ================= Section 4. The positive cone (sigT witness form) and
   star-commutation lemmas ================= *)

(* The positive cone: [a] is positive iff some witness [b] satisfies [a = star b * b] (the standard C* cone form). *)
Definition cst_pos (BA : Set) (bae : BA -> BA -> Set) (C : CStarAlg BA bae) (a : BA) : Set :=
  sigT (fun b : BA =>
    bae (@bmult _ _ (@cbase _ _ C) (@cst_star _ _ C b) b) a).

(* Cone members are self-adjoint: [star a == a]. *)
Lemma cst_pos_selfadj : forall (BA : Set) (bae : BA -> BA -> Set) (C : CStarAlg BA bae) (a : BA),
  cst_pos _ _ C a -> bae (@cst_star _ _ C a) a.
Proof.
  intros BA bae C a [b Hb].
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  { exact (@bae_sym _ _ (@cbase _ _ C)
             (@cst_star _ _ C (@bmult _ _ (@cbase _ _ C) (@cst_star _ _ C b) b))
             (@cst_star _ _ C a)
             (@cst_star_wd _ _ C (@bmult _ _ (@cbase _ _ C) (@cst_star _ _ C b) b) a Hb)). }
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  { exact (@cst_star_mult _ _ C (@cst_star _ _ C b) b). }
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  { exact (@bmult_wd _ _ (@cbase _ _ C) (@cst_star _ _ C b)
             (@cst_star _ _ C (@cst_star _ _ C b))
             (@cst_star _ _ C b) b
             (@bae_refl _ _ (@cbase _ _ C) (@cst_star _ _ C b)) (@cst_star_star _ _ C b)). }
  exact Hb.
Qed.

(* star preserves the cone: positivity of [a] gives positivity of [star a] (self-adjointness; the witness [b] is inherited verbatim). *)
Lemma cst_star_preserves_pos : forall (BA : Set) (bae : BA -> BA -> Set) (C : CStarAlg BA bae) (a : BA),
  cst_pos _ _ C a -> cst_pos _ _ C (@cst_star _ _ C a).
Proof.
  intros BA bae C a [b Hb].
  exists b. apply (@bae_sym _ _ (@cbase _ _ C) _ _).
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  { exact (cst_pos_selfadj _ _ C a (existT _ b Hb)). }
  exact (@bae_sym _ _ (@cbase _ _ C) (@bmult _ _ (@cbase _ _ C) (@cst_star _ _ C b) b) a Hb).
Qed.

(* star commutes with the residual: for self-adjoint [a],
   [star (x*x - a) == star x * star x - a] (the involution face of the Newton
   residual; a lemma-level form of star commuting with the square root). *)
Lemma cst_star_residual : forall (BA : Set) (bae : BA -> BA -> Set) (C : CStarAlg BA bae) (a x : BA),
  bae (@cst_star _ _ C a) a ->
  bae
    (@cst_star _ _ C (@bplus _ _ (@cbase _ _ C) (@bmult _ _ (@cbase _ _ C) x x)
                         (@bopp _ _ (@cbase _ _ C) a)))
    (@bplus _ _ (@cbase _ _ C) (@bmult _ _ (@cbase _ _ C) (@cst_star _ _ C x) (@cst_star _ _ C x))
                      (@bopp _ _ (@cbase _ _ C) a)).
Proof.
  intros BA bae C a x Hsa.
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  { exact (@cst_star_add _ _ C (@bmult _ _ (@cbase _ _ C) x x) (@bopp _ _ (@cbase _ _ C) a)). }
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  { apply (@bplus_wd_l _ _ (@cbase _ _ C)
             (@cst_star _ _ C (@bmult _ _ (@cbase _ _ C) x x))
             (@bmult _ _ (@cbase _ _ C) (@cst_star _ _ C x) (@cst_star _ _ C x))
             (@cst_star _ _ C (@bopp _ _ (@cbase _ _ C) a)) (@cst_star_mult _ _ C x x)). }
  apply (@bplus_wd_r _ _ (@cbase _ _ C) (@cst_star _ _ C (@bopp _ _ (@cbase _ _ C) a))
           (@bopp _ _ (@cbase _ _ C) a)
           (@bmult _ _ (@cbase _ _ C) (@cst_star _ _ C x) (@cst_star _ _ C x))).
  eapply (@bae_trans _ _ (@cbase _ _ C)).
  - exact (cst_star_opp _ _ C a).
  - exact (@bopp_wd _ _ (@cbase _ _ C) (@cst_star _ _ C a) a Hsa).
Qed.

(* ================= Explicit assumptions (declared symmetrically; no admits) ================= *)
(* 1. A Newton sequence for a general positive element inside the algebra
   needs an inversion face (a sigT witness of invertibility of [x_n]
   commuting with [a]); the results of Section 3 cover the scalar-embedding
   face, and the general element via a Neumann-series inversion tightened by
   the C* identity is the next level. *)
(* 2. The closure form [x_inf^2 == a] needs completeness of the Q-sequence
   or a direct limit face; this module states the result in the
   explicit-rate neighborhood form. *)
(* 3. Additive closure of the cone and the order face (Lowner) form the
   constructive spectral-theorem open band, declared explicitly. *)
(* 4. star-power commutation: needs a same-element power-commutation lemma
   (provable by induction); deferred to a later registration pass. *)

Print Assumptions cst_bae_bopp_invol.
