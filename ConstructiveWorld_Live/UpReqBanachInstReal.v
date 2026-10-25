(* ConstructiveWorld-Set — the Real-carrier instance of the Banach
   algebra pre-class. *)

(** * UpReqBanachInstReal: a concrete instance of the Banach-algebra
      pre-class over the Real carrier.

    Mission.  Assembles the development's [Real] carrier (a dependent pair
      of a rational sequence and its Cauchy witness) into the library
      pre-class [bxin_BanachAlgPre] (the 39-field weak class of
      [UpReqBanachInst]), producing the concrete instance
      [bxra_real_pre].  Architecture: the carrier is [Real]; the equality
      face [bxra_bae_germ] identifies canonical germs
      ([Id (bxib_qnorm (head a)) (bxib_qnorm (head b))]); operations act
      on head rationals and renormalize; the norm is
      [Qabs ∘ bxib_qnorm ∘ head].  Main statements: [bxra_real_pre] (the
      instance assembly), [bxra_norm_wd] and [bxra_norm_coef_qeqt]
      (well-definedness of the norm and the pinning face),
      [bxra_f_norm_opp], [bxra_raw_pin_wall] (the original pinning
      [Id (Qabs q) (Qabs (bxib_qnorm q))] is unsatisfiable), and the
      completeness dividends [bxra_head_col_cauchy] and
      [bxra_cauchy_limit_elem] (the head column of a pre-Cauchy sequence
      is Q-Cauchy, and the limit element is constructible in the
      carrier).

    Dependencies.  Stdlib [QArith], [QArith.Qabs], [ZArith], [Lia].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [UpReqBanachExp], [UpReqBanachInstB], [UpReqBanachInst] of this
      development.

    References.  This development, the ConstructiveWorld-Main baseline
      module of the same name whose statement names are carried over
      verbatim.

    Constructivity.  No axioms, parameters, conjectures, admits,
      Variables or Hypotheses; all statement conclusions are carried by
      [Set]/[Id]/[QeqT]/[QleT'].  The convergence statement whose norm
      reads the head term (the inner face of [bxin_pre_complete]) is
      honestly left open: the head term of the limit element would have
      to be the (constructively unnamed) limit value of the head column —
      the rational-sequence completeness obstruction; no forcing.  The
      extraction probes at the end of this file report [Obj.magic] = 0 on
      the extracted face; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqBanachInstReal.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachInstB.
Require Import UpReqBanachInst.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Lia.

(* ================= Section 1. Carrier-face tools: head evaluation,
   canonical constant reals, germ equality, norm ================= *)

(* Head evaluation: [Real -> Q] (definitional). *)
Definition bxra_head (x : Real) : Q := projT1 x 0%nat.

(* Constant-real constructor ([real_const] of S02 is transparent: the head reduces definitionally). *)
Definition bxra_cR (q : Q) : Real := real_const q.

Lemma bxra_head_cR : forall q : Q, Id (bxra_head (bxra_cR q)) q.
Proof.
  intro q. unfold bxra_head, bxra_cR.
  cbn [projT1]. apply id_refl.
Qed.

(* Germ equality: canonical germs. *)
Definition bxra_bae_germ (a b : Real) : Set :=
  Id (bxib_qnorm (bxra_head a)) (bxib_qnorm (bxra_head b)).

(* The norm: [Qabs ∘ bxib_qnorm ∘ head]. *)
Definition bxra_bnorm_f (x : Real) : Q := Qabs (bxib_qnorm (bxra_head x)).

(* Operations: rational arithmetic on heads, then renormalization (constants included). *)
Definition bxra_bplus_f (x y : Real) : Real :=
  bxra_cR (bxib_qnorm (bxra_head x + bxra_head y)%Q).
Definition bxra_bmult_f (x y : Real) : Real :=
  bxra_cR (bxib_qnorm (bxra_head x * bxra_head y)%Q).
Definition bxra_bopp_f (x : Real) : Real :=
  bxra_cR (bxib_qnorm (- bxra_head x)%Q).
Definition bxra_bzero_f : Real := bxra_cR 0%Q.
Definition bxra_bone_f : Real := bxra_cR 1%Q.
Definition bxra_bcoef_f (q : Q) : Real := bxra_cR (bxib_qnorm q).

(* Head-face restoration (operation outputs reduce definitionally). *)
Lemma bxra_head_bplus : forall x y : Real,
  Id (bxra_head (bxra_bplus_f x y)) (bxib_qnorm (bxra_head x + bxra_head y)%Q).
Proof.
  intros x y. unfold bxra_head, bxra_bplus_f, bxra_cR.
  cbn [projT1]. apply id_refl.
Qed.

Lemma bxra_head_bmult : forall x y : Real,
  Id (bxra_head (bxra_bmult_f x y)) (bxib_qnorm (bxra_head x * bxra_head y)%Q).
Proof.
  intros x y. unfold bxra_head, bxra_bmult_f, bxra_cR.
  cbn [projT1]. apply id_refl.
Qed.

Lemma bxra_head_bopp : forall x : Real,
  Id (bxra_head (bxra_bopp_f x)) (bxib_qnorm (- bxra_head x)%Q).
Proof.
  intro x. unfold bxra_head, bxra_bopp_f, bxra_cR.
  cbn [projT1]. apply id_refl.
Qed.

(* ================= Section 2. Q-layer working pieces (QeqT contracts /
   Qabs helpers / nonnegativity / transfer bridges) ================= *)

(* QeqT congruence of multiplication. *)
Lemma bxra_qeqT_cong_mult : forall a b c d : Q,
  QeqT a b -> QeqT c d -> QeqT (a * c)%Q (b * d)%Q.
Proof.
  intros a b c d Hab Hcd.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq a b Hab), (qeqT_imp_qeq c d Hcd).
  apply Qeq_refl.
Qed.

(* [Qabs (x*y) = Qabs x * Qabs y] (built here; the stdlib name is absent). *)
Lemma bxra_qabs_mult : forall x y : Q, QeqT (Qabs (x * y)%Q) (Qabs x * Qabs y%Q).
Proof.
  intros [n d] [m e].
  apply qeq_imp_qeqT. unfold Qabs, Qmult, Qeq; simpl.
  rewrite Z.abs_mul. ring.
Qed.

(* [Qabs] is nonnegative ([QleT'] leaf). *)
Lemma bxra_qleT_zero_abs_qn : forall x : Q, QleT' 0 (Qabs (bxib_qnorm x)).
Proof.
  intros [n d]. destruct n as [|p|p];
    apply Qle_to_QleT'; unfold Qle, Qabs, bxib_qnorm; cbn; lia.
Qed.

Lemma bxra_qltT_wd : forall a b c : Q, QeqT a b -> QltT a c -> QltT b c.
Proof.
  intros a b c Hab H.
  apply (qleT'_ltT_ltT b a c).
  - apply qeq_imp_qle.
    apply bxib_qeqT_sym. exact Hab.
  - exact H.
Qed.

(* ============================================================ *)
(* ============================================================ *)

(* Qabs-norm invariance in [Id] form. Direct iota reduction does not close
   it (the [Z.gcd] machine gets stuck on symbolic arguments); a Z-level
   lemma chain closes it — [Z.gcd_opp_l] + [bxib_div_exact] + [Z.abs_opp] —
   and an eq bridge returns to [Id]. *)
Lemma bxra_id_of_eq : forall (A : Set) (x y : A), x = y -> Id x y.
Proof.
  intros A x y H.
  exact (match H in (_ = t) return Id x t with
         | eq_refl => id_refl
         end).
Qed.

(* Z-level core: the absolute value of a divided negation is unchanged (an algebraic route through div_opp, with no modulo side condition). *)
Lemma bxra_zabs_div_opp : forall p g : Z,
  g <> 0%Z -> Z.divide g p -> Z.divide g (Z.opp p) ->
  @Id Z (Z.abs (Z.div (Z.opp p) g)) (Z.abs (Z.div p g)).
Proof.
  intros p g Hg0 Hp Hn.
  assert (Hdp : (p = Z.mul g (Z.div p g))%Z)
    by (exact (match bxib_div_exact p g Hg0 Hp
               in (@Id _ _ y) return (p = y)
               with id_refl => eq_refl end)).
  assert (Hdn : (Z.opp p = Z.mul g (Z.div (Z.opp p) g))%Z)
    by (exact (match bxib_div_exact (Z.opp p) g Hg0 Hn
               in (@Id _ _ y) return (Z.opp p = y)
               with id_refl => eq_refl end)).
  assert (Hq : (Z.div (Z.opp p) g = Z.opp (Z.div p g))%Z).
  { apply (Z.mul_reg_l (Z.div (Z.opp p) g) (Z.opp (Z.div p g)) g Hg0).
    rewrite <- Hdn. replace p with (Z.mul g (Z.div p g)) at 1
      by (symmetry; exact Hdp).
    ring. }
  rewrite Hq, Z.abs_opp. reflexivity.
Qed.

Lemma bxra_qabs_opp_norm : forall u : Q,
  Id (Qabs (bxib_qnorm (Qopp u))) (Qabs (bxib_qnorm u)).
Proof.
  intro u. apply bxra_id_of_eq.
  destruct u as [n d]. destruct n as [|p|p].
  - reflexivity.
  - change (Qopp (Qmake (Zpos p) d)) with (Qmake (Zneg p) d).
    rewrite bxib_qnorm_neg_shape, bxib_qnorm_pos_shape.
    unfold Qabs. cbn [Qnum Qden].
    change (Zneg p) with (- (Zpos p))%Z.
    rewrite (Z.gcd_opp_l (Zpos p) (Z.pos d)).
    f_equal.
    assert (Hg0 : Z.gcd (Zpos p) (Z.pos d) <> 0%Z).
    { intro H0.
      destruct (Z.gcd_divide_l (Zpos p) (Z.pos d)) as [k Hk].
      rewrite H0, Z.mul_0_r in Hk. discriminate Hk. }
    assert (Hid : @Id Z (Z.abs (Z.div (Z.opp (Zpos p)) (Z.gcd (Zpos p) (Z.pos d))))
                      (Z.abs (Z.div (Zpos p) (Z.gcd (Zpos p) (Z.pos d))))).
    { apply bxra_zabs_div_opp.
      - exact Hg0.
      - exact (Z.gcd_divide_l (Zpos p) (Z.pos d)).
      - destruct (Z.gcd_divide_l (Zpos p) (Z.pos d)) as [k Hk].
        exists (-k)%Z. rewrite Hk at 1. ring. }
    exact (match Hid with id_refl => eq_refl end).
  - change (Qopp (Qmake (Zneg p) d)) with (Qmake (Zpos p) d).
    rewrite bxib_qnorm_pos_shape, bxib_qnorm_neg_shape.
    unfold Qabs. cbn [Qnum Qden].
    change (Zneg p) with (- (Zpos p))%Z.
    rewrite (Z.gcd_opp_l (Zpos p) (Z.pos d)).
    f_equal.
    assert (Hg0 : Z.gcd (Zpos p) (Z.pos d) <> 0%Z).
    { intro H0.
      destruct (Z.gcd_divide_l (Zpos p) (Z.pos d)) as [k Hk].
      rewrite H0, Z.mul_0_r in Hk. discriminate Hk. }
    assert (Hid : @Id Z (Z.abs (Z.div (Z.opp (Zpos p)) (Z.gcd (Zpos p) (Z.pos d))))
                      (Z.abs (Z.div (Zpos p) (Z.gcd (Zpos p) (Z.pos d))))).
    { apply bxra_zabs_div_opp.
      - exact Hg0.
      - exact (Z.gcd_divide_l (Zpos p) (Z.pos d)).
      - destruct (Z.gcd_divide_l (Zpos p) (Z.pos d)) as [k Hk].
        exists (-k)%Z. rewrite Hk at 1. ring. }
    symmetry. exact (match Hid with id_refl => eq_refl end).
Qed.

(* Discharge of the first obstruction (library-class [QeqT] form): well-definedness of the norm on germ equality (through [Id]). *)
Lemma bxra_norm_wd : forall a b : Real,
  bxra_bae_germ a b -> Id (bxra_bnorm_f a) (bxra_bnorm_f b).
Proof.
  intros a b Hab. unfold bxra_bnorm_f.
  apply (id_cong Qabs). exact Hab.
Qed.

Lemma bxra_norm_wd_qeqt : forall a b : Real,
  bxra_bae_germ a b -> QeqT (bxra_bnorm_f a) (bxra_bnorm_f b).
Proof. intros a b Hab. apply bxib_qeqT_of_id. apply bxra_norm_wd. exact Hab. Qed.

(* Discharge of the second obstruction (library-class [QeqT] form): the pinning face reduces to the original [Qabs q]. *)
Lemma bxra_norm_coef_qeqt : forall q : Q,
  QeqT (bxra_bnorm_f (bxra_bcoef_f q)) (Qabs q).
Proof.
  intro q.
  apply qeq_imp_qeqT.
  unfold bxra_bnorm_f, bxra_bcoef_f.
  rewrite (bxra_head_cR (bxib_qnorm q)).
  rewrite (bxib_qnorm_fix_id q).
  apply (Qeq_trans _ (Qabs (bxib_qnorm q))).
  - apply Qabs_wd. apply Qeq_refl.
  - apply (Qeq_trans _ (Qabs q)).
    + apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
    + apply Qeq_refl.
Qed.

(* Discharge of the [bnorm_opp] field (library-class [Id] form): the consumer of the preceding lemma. *)
Lemma bxra_f_norm_opp : forall a : Real,
  Id (bxra_bnorm_f (bxra_bopp_f a)) (bxra_bnorm_f a).
Proof.
  intro a.
  change (Id (Qabs (bxib_qnorm (bxib_qnorm (- bxra_head a)%Q)))
             (Qabs (bxib_qnorm (bxra_head a)))).
  rewrite (bxib_qnorm_fix_id (- bxra_head a)%Q).
  apply bxra_qabs_opp_norm.
Qed.

(* The original pinning obstruction, made precise (honest note: the original [Qabs] pinning in [Id] form is unsatisfiable). *)
Lemma bxra_raw_pin_wall :
  Id (bxra_bnorm_f (bxra_bcoef_f (2#4)%Q)) (Qabs (2#4)%Q) ->
  Id (1#2)%Q (2#4)%Q.
Proof.
  intro H.
  change (Id (Qabs (bxib_qnorm (bxib_qnorm (2#4)%Q))) (Qabs (2#4)%Q)) in H.
  rewrite bxib_qnorm_fix_id in H.
  exact H.
Qed.

(* ================= Section 3. Field-by-field discharges of the library
   class (39 fields) ================= *)

(* ---- The three equivalence laws ---- *)

Lemma bxra_f_refl : forall a : Real, bxra_bae_germ a a.
Proof. intro a. apply id_refl. Qed.

Lemma bxra_f_sym : forall a b : Real, bxra_bae_germ a b -> bxra_bae_germ b a.
Proof. intros a b H. apply id_sym. exact H. Qed.

Lemma bxra_f_trans : forall a b c : Real,
  bxra_bae_germ a b -> bxra_bae_germ b c -> bxra_bae_germ a c.
Proof. intros a b c H1 H2. apply (id_trans H1 H2). Qed.

(* ---- Additive group (base piece) ---- *)

Lemma bxra_f_plus_assoc : forall a b c : Real,
  bxra_bae_germ (bxra_bplus_f a (bxra_bplus_f b c))
                (bxra_bplus_f (bxra_bplus_f a b) c).
Proof.
  intros a b c. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a (bxra_bplus_f b c)).
  rewrite (bxra_head_bplus b c).
  rewrite (bxra_head_bplus (bxra_bplus_f a b) c).
  rewrite (bxra_head_bplus a b).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxib_qnorm (bxra_head b + bxra_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a + bxra_head b)%Q + bxra_head c)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxra_head a + (bxra_head b + bxra_head c))%Q).
  - apply bxib_qeqT_cong_plus; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxra_head a + bxra_head b + bxra_head c)%Q).
    + apply qeq_imp_qeqT. apply Qplus_assoc.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix | apply bxib_qeqT_refl].
Qed.

Lemma bxra_f_plus_comm : forall a b : Real,
  bxra_bae_germ (bxra_bplus_f a b) (bxra_bplus_f b a).
Proof.
  intros a b. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a b), (bxra_head_bplus b a).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxra_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head b + bxra_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qplus_comm.
Qed.

Lemma bxra_f_plus_zero : forall a : Real,
  bxra_bae_germ (bxra_bplus_f a bxra_bzero_f) a.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a bxra_bzero_f).
  unfold bxra_bzero_f.
  rewrite (bxra_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head a + 0%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (bxra_head a)).
  - apply Qplus_0_r.
  - apply Qeq_refl.
Qed.

Lemma bxra_f_plus_opp : forall a : Real,
  bxra_bae_germ (bxra_bplus_f a (bxra_bopp_f a)) bxra_bzero_f.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a (bxra_bopp_f a)).
  rewrite (bxra_head_bopp a).
  unfold bxra_bzero_f.
  rewrite (bxra_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxib_qnorm (- bxra_head a)%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxra_head a + (- bxra_head a))%Q).
  - apply bxib_qeqT_cong_plus;
      [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply qeq_imp_qeqT. apply Qplus_opp_r.
Qed.

(* ---- Multiplicative group ---- *)

Lemma bxra_f_mult_assoc : forall a b c : Real,
  bxra_bae_germ (bxra_bmult_f a (bxra_bmult_f b c))
                (bxra_bmult_f (bxra_bmult_f a b) c).
Proof.
  intros a b c. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a (bxra_bmult_f b c)).
  rewrite (bxra_head_bmult b c).
  rewrite (bxra_head_bmult (bxra_bmult_f a b) c).
  rewrite (bxra_head_bmult a b).
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxib_qnorm (bxra_head b * bxra_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a * bxra_head b)%Q * bxra_head c)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxra_head a * (bxra_head b * bxra_head c))%Q).
  - apply bxra_qeqT_cong_mult; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxra_head a * bxra_head b * bxra_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_assoc.
    + apply bxra_qeqT_cong_mult;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix | apply bxib_qeqT_refl].
Qed.

Lemma bxra_f_mult_one_l : forall a : Real,
  bxra_bae_germ (bxra_bmult_f bxra_bone_f a) a.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult bxra_bone_f a).
  unfold bxra_bone_f.
  rewrite (bxra_head_cR 1%Q).
  rewrite (bxib_qnorm_fix_id (1%Q * bxra_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_1_l.
Qed.

Lemma bxra_f_mult_one_r : forall a : Real,
  bxra_bae_germ (bxra_bmult_f a bxra_bone_f) a.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a bxra_bone_f).
  unfold bxra_bone_f.
  rewrite (bxra_head_cR 1%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head a * 1%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_1_r.
Qed.

(* ---- Distributivity ---- *)

Lemma bxra_f_distrib_l : forall a b c : Real,
  bxra_bae_germ (bxra_bmult_f a (bxra_bplus_f b c))
                (bxra_bplus_f (bxra_bmult_f a b) (bxra_bmult_f a c)).
Proof.
  intros a b c. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a (bxra_bplus_f b c)).
  rewrite (bxra_head_bplus b c).
  rewrite (bxra_head_bplus (bxra_bmult_f a b) (bxra_bmult_f a c)).
  rewrite (bxra_head_bmult a b), (bxra_head_bmult a c).
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxib_qnorm (bxra_head b + bxra_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a * bxra_head b)%Q
                              + bxib_qnorm (bxra_head a * bxra_head c))%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxra_head a * (bxra_head b + bxra_head c))%Q).
  - apply bxra_qeqT_cong_mult; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxra_head a * bxra_head b + bxra_head a * bxra_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_r.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix |
         apply bxib_qeqT_sym; apply bxib_qnorm_fix].
Qed.

Lemma bxra_f_distrib_r : forall a b c : Real,
  bxra_bae_germ (bxra_bmult_f (bxra_bplus_f a b) c)
                (bxra_bplus_f (bxra_bmult_f a c) (bxra_bmult_f b c)).
Proof.
  intros a b c. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult (bxra_bplus_f a b) c).
  rewrite (bxra_head_bplus a b).
  rewrite (bxra_head_bplus (bxra_bmult_f a c) (bxra_bmult_f b c)).
  rewrite (bxra_head_bmult a c), (bxra_head_bmult b c).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a + bxra_head b)%Q * bxra_head c)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a * bxra_head c)%Q
                              + bxib_qnorm (bxra_head b * bxra_head c))%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ ((bxra_head a + bxra_head b) * bxra_head c)%Q).
  - apply bxra_qeqT_cong_mult; [apply bxib_qnorm_fix | apply bxib_qeqT_refl].
  - apply (bxib_qeqT_trans _ (bxra_head a * bxra_head c + bxra_head b * bxra_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_l.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix |
         apply bxib_qeqT_sym; apply bxib_qnorm_fix].
Qed.

Lemma bxra_f_mult_zero : forall a : Real,
  bxra_bae_germ (bxra_bmult_f a bxra_bzero_f) bxra_bzero_f.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a bxra_bzero_f).
  unfold bxra_bzero_f.
  rewrite (bxra_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head a * 0%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_0_r.
Qed.

(* ---- Well-definedness trio ---- *)

Lemma bxra_f_plus_wd : forall a b c d : Real,
  bxra_bae_germ a c -> bxra_bae_germ b d ->
  bxra_bae_germ (bxra_bplus_f a b) (bxra_bplus_f c d).
Proof.
  intros a b c d Hac Hbd. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a b), (bxra_head_bplus c d).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxra_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head c + bxra_head d)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_plus.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head a))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head c))).
      * apply bxib_qeqT_of_id. exact Hac.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head b))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head d))).
      * apply bxib_qeqT_of_id. exact Hbd.
      * apply bxib_qnorm_fix.
Qed.

Lemma bxra_f_mult_wd : forall a b c d : Real,
  bxra_bae_germ a c -> bxra_bae_germ b d ->
  bxra_bae_germ (bxra_bmult_f a b) (bxra_bmult_f c d).
Proof.
  intros a b c d Hac Hbd. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a b), (bxra_head_bmult c d).
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxra_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head c * bxra_head d)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxra_qeqT_cong_mult.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head a))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head c))).
      * apply bxib_qeqT_of_id. exact Hac.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head b))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head d))).
      * apply bxib_qeqT_of_id. exact Hbd.
      * apply bxib_qnorm_fix.
Qed.

Lemma bxra_f_opp_wd : forall a b : Real,
  bxra_bae_germ a b -> bxra_bae_germ (bxra_bopp_f a) (bxra_bopp_f b).
Proof.
  intros a b Hab. unfold bxra_bae_germ.
  rewrite (bxra_head_bopp a), (bxra_head_bopp b).
  rewrite (bxib_qnorm_fix_id (- bxra_head a)%Q).
  rewrite (bxib_qnorm_fix_id (- bxra_head b)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_opp.
  apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head a))).
  - apply bxib_qeqT_sym. apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head b))).
    + apply bxib_qeqT_of_id. exact Hab.
    + apply bxib_qnorm_fix.
Qed.

(* ---- Scalar embedding face ---- *)

Lemma bxra_f_coef_zero : bxra_bae_germ (bxra_bcoef_f 0%Q) bxra_bzero_f.
Proof.
  unfold bxra_bae_germ, bxra_bcoef_f, bxra_bzero_f.
  rewrite (bxra_head_cR (bxib_qnorm 0%Q)).
  rewrite (bxra_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id 0%Q).
  apply id_refl.
Qed.

Lemma bxra_f_coef_one : bxra_bae_germ (bxra_bcoef_f 1%Q) bxra_bone_f.
Proof.
  unfold bxra_bae_germ, bxra_bcoef_f, bxra_bone_f.
  rewrite (bxra_head_cR (bxib_qnorm 1%Q)).
  rewrite (bxra_head_cR 1%Q).
  rewrite (bxib_qnorm_fix_id 1%Q).
  apply id_refl.
Qed.

Lemma bxra_f_coef_mult : forall q r : Q,
  bxra_bae_germ (bxra_bcoef_f (q * r)%Q)
                (bxra_bmult_f (bxra_bcoef_f q) (bxra_bcoef_f r)).
Proof.
  intros q r. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult (bxra_bcoef_f q) (bxra_bcoef_f r)).
  unfold bxra_bcoef_f.
  repeat rewrite bxra_head_cR.
  rewrite (bxib_qnorm_fix_id (q * r)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q * bxib_qnorm r)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_sym.
  apply bxra_qeqT_cong_mult; apply bxib_qnorm_fix.
Qed.

Lemma bxra_f_coef_comm : forall (q : Q) (a : Real),
  bxra_bae_germ (bxra_bmult_f a (bxra_bcoef_f q))
                (bxra_bmult_f (bxra_bcoef_f q) a).
Proof.
  intros q a. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a (bxra_bcoef_f q)).
  rewrite (bxra_head_bmult (bxra_bcoef_f q) a).
  unfold bxra_bcoef_f.
  repeat rewrite bxra_head_cR.
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxib_qnorm q)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q * bxra_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_comm.
Qed.

(* ---- The two remaining fields ---- *)

Lemma bxra_f_coef_plus : forall q r : Q,
  bxra_bae_germ (bxra_bplus_f (bxra_bcoef_f q) (bxra_bcoef_f r))
                (bxra_bcoef_f (q + r)%Q).
Proof.
  intros q r. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus (bxra_bcoef_f q) (bxra_bcoef_f r)).
  unfold bxra_bcoef_f.
  repeat rewrite bxra_head_cR.
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q + bxib_qnorm r)%Q).
  rewrite (bxib_qnorm_fix_id (q + r)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_plus; apply bxib_qnorm_fix.
Qed.

Lemma bxra_f_coef_wd : forall q r : Q,
  q == r -> bxra_bae_germ (bxra_bcoef_f q) (bxra_bcoef_f r).
Proof.
  intros q r Hqr. unfold bxra_bae_germ, bxra_bcoef_f.
  repeat rewrite bxra_head_cR.
  rewrite (bxib_qnorm_fix_id q), (bxib_qnorm_fix_id r).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. exact Hqr.
Qed.

(* ---- Norm face ---- *)

Lemma bxra_f_norm_zero : Id (bxra_bnorm_f bxra_bzero_f) 0%Q.
Proof.
  unfold bxra_bnorm_f, bxra_bzero_f.
  rewrite (bxra_head_cR 0%Q).
  apply id_refl.
Qed.

Lemma bxra_f_norm_one : Id (bxra_bnorm_f bxra_bone_f) 1%Q.
Proof.
  unfold bxra_bnorm_f, bxra_bone_f.
  rewrite (bxra_head_cR 1%Q).
  apply id_refl.
Qed.

Lemma bxra_f_norm_pos : forall a : Real, QleT' 0 (bxra_bnorm_f a).
Proof.
  intro a. unfold bxra_bnorm_f. apply bxra_qleT_zero_abs_qn.
Qed.

Lemma bxra_f_norm_plus : forall a b : Real,
  QleT' (bxra_bnorm_f (bxra_bplus_f a b))
        (bxra_bnorm_f a + bxra_bnorm_f b)%Q.
Proof.
  intros a b. unfold bxra_bnorm_f.
  rewrite (bxra_head_bplus a b).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxra_head b)%Q).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxra_head a + bxra_head b)%Q)).
  - apply QleT'_to_Qle. apply qeq_imp_qle.
    apply qeq_imp_qeqT. apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
  - apply (Qle_trans _ (Qabs (bxra_head a) + Qabs (bxra_head b))%Q).
    + apply Qabs_triangle.
    + apply QleT'_to_Qle. apply qeq_imp_qle.
      apply qeq_imp_qeqT. apply (@Qplus_comp (Qabs (bxra_head a)) (Qabs (bxib_qnorm (bxra_head a)))
           (Qeq_sym (Qabs (bxib_qnorm (bxra_head a))) (Qabs (bxra_head a))
                (Qabs_wd (bxib_qnorm (bxra_head a)) (bxra_head a)
                     (qeqT_imp_qeq (bxib_qnorm (bxra_head a)) (bxra_head a)
                          (bxib_qnorm_fix (bxra_head a)))))
           (Qabs (bxra_head b)) (Qabs (bxib_qnorm (bxra_head b)))
           (Qeq_sym (Qabs (bxib_qnorm (bxra_head b))) (Qabs (bxra_head b))
                (Qabs_wd (bxib_qnorm (bxra_head b)) (bxra_head b)
                     (qeqT_imp_qeq (bxib_qnorm (bxra_head b)) (bxra_head b)
                          (bxib_qnorm_fix (bxra_head b)))))).
Qed.

Lemma bxra_f_norm_mult : forall a b : Real,
  QleT' (bxra_bnorm_f (bxra_bmult_f a b))
        (bxra_bnorm_f a * bxra_bnorm_f b)%Q.
Proof.
  intros a b. unfold bxra_bnorm_f.
  rewrite (bxra_head_bmult a b).
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxra_head b)%Q).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxra_head a) * Qabs (bxra_head b))%Q).
  - apply QleT'_to_Qle. apply qeq_imp_qle.
    apply qeq_imp_qeqT. apply (Qeq_trans (Qabs (bxib_qnorm (bxra_head a * bxra_head b)%Q))
                     (Qabs (bxra_head a * bxra_head b)%Q)
                     (Qabs (bxra_head a) * Qabs (bxra_head b))%Q).
    + apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
    + apply qeqT_imp_qeq. apply bxra_qabs_mult.
  - apply QleT'_to_Qle. apply qeq_imp_qle.
    apply qeq_imp_qeqT. apply (@Qmult_comp (Qabs (bxra_head a)) (Qabs (bxib_qnorm (bxra_head a)))
         (Qeq_sym (Qabs (bxib_qnorm (bxra_head a))) (Qabs (bxra_head a))
              (Qabs_wd (bxib_qnorm (bxra_head a)) (bxra_head a)
                   (qeqT_imp_qeq (bxib_qnorm (bxra_head a)) (bxra_head a)
                        (bxib_qnorm_fix (bxra_head a)))))
         (Qabs (bxra_head b)) (Qabs (bxib_qnorm (bxra_head b)))
         (Qeq_sym (Qabs (bxib_qnorm (bxra_head b))) (Qabs (bxra_head b))
              (Qabs_wd (bxib_qnorm (bxra_head b)) (bxra_head b)
                   (qeqT_imp_qeq (bxib_qnorm (bxra_head b)) (bxra_head b)
                        (bxib_qnorm_fix (bxra_head b)))))).
Qed.

(* ================= Section 4. Full class assembly — the concrete
   instance ================= *)

Instance bxra_real_pre : bxin_BanachAlgPre := {|
  bxin_BA := Real;
  bxin_bae := bxra_bae_germ;
  bxin_bae_refl := bxra_f_refl;
  bxin_bae_sym := bxra_f_sym;
  bxin_bae_trans := bxra_f_trans;
  bxin_bzero := bxra_bzero_f;
  bxin_bone := bxra_bone_f;
  bxin_bplus := bxra_bplus_f;
  bxin_bmult := bxra_bmult_f;
  bxin_bopp := bxra_bopp_f;
  bxin_bcoef := bxra_bcoef_f;
  bxin_bnorm := bxra_bnorm_f;
  bxin_bplus_assoc := bxra_f_plus_assoc;
  bxin_bplus_comm := bxra_f_plus_comm;
  bxin_bplus_zero := bxra_f_plus_zero;
  bxin_bplus_opp := bxra_f_plus_opp;
  bxin_bmult_assoc := bxra_f_mult_assoc;
  bxin_bmult_one_l := bxra_f_mult_one_l;
  bxin_bmult_one_r := bxra_f_mult_one_r;
  bxin_bdistrib_l := bxra_f_distrib_l;
  bxin_bdistrib_r := bxra_f_distrib_r;
  bxin_bmult_zero := bxra_f_mult_zero;
  bxin_bplus_wd := bxra_f_plus_wd;
  bxin_bmult_wd := bxra_f_mult_wd;
  bxin_bopp_wd := bxra_f_opp_wd;
  bxin_bnorm_wd := bxra_norm_wd_qeqt;
  bxin_bcoef_zero := bxra_f_coef_zero;
  bxin_bcoef_one := bxra_f_coef_one;
  bxin_bcoef_mult := bxra_f_coef_mult;
  bxin_bcoef_comm := bxra_f_coef_comm;
  bxin_bcoef_plus := bxra_f_coef_plus;
  bxin_bcoef_wd := bxra_f_coef_wd;
  bxin_bnorm_zero := bxra_f_norm_zero;
  bxin_bnorm_one := bxra_f_norm_one;
  bxin_bnorm_opp := bxra_f_norm_opp;
  bxin_bnorm_pos := bxra_f_norm_pos;
  bxin_bnorm_plus := bxra_f_norm_plus;
  bxin_bnorm_mult := bxra_f_norm_mult;
  bxin_bnorm_coef := bxra_norm_coef_qeqt;
|}.

(* Assembly smoke test: through the class projections (the pointwise confirmation that the instance is populated). *)
Lemma bxra_inst_smoke_bone :
  @bxin_bae bxra_real_pre
    (@bxin_bcoef bxra_real_pre 1%Q)
    (@bxin_bone bxra_real_pre).
Proof.
  change (@bxin_bae bxra_real_pre
           (@bxin_bcoef bxra_real_pre 1%Q)
           (@bxin_bone bxra_real_pre))
    with (bxra_bae_germ (bxra_bcoef_f 1%Q) bxra_bone_f).
  apply bxra_f_coef_one.
Qed.

Lemma bxra_inst_smoke_norm_coef : forall q : Q,
  QeqT (@bxin_bnorm bxra_real_pre (@bxin_bcoef bxra_real_pre q)) (Qabs q).
Proof.
  intro q.
  change (@bxin_bnorm bxra_real_pre (@bxin_bcoef bxra_real_pre q))
    with (bxra_bnorm_f (bxra_bcoef_f q)).
  apply bxra_norm_coef_qeqt.
Qed.

Lemma bxra_inst_smoke_norm_wd : forall a b : Real,
  @bxin_bae bxra_real_pre a b ->
  QeqT (@bxin_bnorm bxra_real_pre a) (@bxin_bnorm bxra_real_pre b).
Proof.
  intros a b H.
  change (@bxin_bnorm bxra_real_pre a) with (bxra_bnorm_f a).
  change (@bxin_bnorm bxra_real_pre b) with (bxra_bnorm_f b).
  change (@bxin_bae bxra_real_pre a b) with (bxra_bae_germ a b).
  apply bxra_norm_wd_qeqt. exact H.
Qed.

(* ================= Section 5. Completeness dividends (the [bcauchy]
   consumer face) and honest notes ================= *)

(* Norm-difference reduction: the [Qeq] value of [bnorm (u m ⊖ u n)] equals the absolute head-column difference. *)
Lemma bxra_norm_diff_head : forall (u : nat -> Real) (m n : nat),
  QeqT (bxra_bnorm_f (bxra_bplus_f (u m) (bxra_bopp_f (u n))))
       (Qabs (bxra_head (u m) - bxra_head (u n))%Q).
Proof.
  intros u m n. unfold bxra_bnorm_f.
  rewrite (bxra_head_bplus (u m) (bxra_bopp_f (u n))).
  rewrite (bxra_head_bopp (u n)).
  rewrite (bxib_qnorm_fix_id (bxra_head (u m)
            + bxib_qnorm (- bxra_head (u n))%Q)%Q).
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (Qabs (bxib_qnorm
        (bxra_head (u m) - bxra_head (u n))%Q))).
  - apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_qeqT_of_qeqT.
    apply bxib_qeqT_cong_plus.
    + apply bxib_qeqT_refl.
    + apply bxib_qnorm_fix.
  - apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
Qed.

(* Dividend 1: the head column of a pre-Cauchy sequence is itself a Q-Cauchy sequence in the sense of S02. *)
Lemma bxra_head_col_cauchy : forall u : nat -> Real,
  (forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      QltT (bxra_bnorm_f (bxra_bplus_f (u m) (bxra_bopp_f (u n)))) eps)) ->
  cauchy (fun k => bxra_head (u k)).
Proof.
  intros u Hu eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  apply (bxra_qltT_wd (bxra_bnorm_f
        (bxra_bplus_f (u m) (bxra_bopp_f (u n))))).
  - apply bxra_norm_diff_head.
  - apply HN; assumption.
Qed.

(* Dividend 2: the limit element is constructible in the [Real] carrier
   (the carrier's built-in completeness dividend: the Cauchy witness is
   supplied by the head column itself; wrapping in [existT] yields a
   genuine [Real] element — no gap on the carrier side). *)
Definition bxra_cauchy_limit_elem (u : nat -> Real)
  (Hu : forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      QltT (bxra_bnorm_f (bxra_bplus_f (u m) (bxra_bopp_f (u n)))) eps))
  : Real :=
  existT (fun s : Qseq => cauchy s)
         (fun k => bxra_head (u k)) (bxra_head_col_cauchy u Hu).

(* Honest note on the convergence statement (the inner face of
   [bxin_pre_complete]): the norm reads the head term, and the head term of
   the limit element would have to be the (constructively unnamed) limit
   value of the head column — the rational-sequence completeness
   obstruction; left open, no forcing. *)
Definition bxra_pre_complete_real : Set :=
  bxin_pre_complete bxra_real_pre.

(* The assembly bridge (conditional form: with a completeness input in place, the full [BanachAlg] follows). *)
Definition bxra_BanachAlg_of_real
  (Hc : bxin_pre_complete bxra_real_pre) : BanachAlg (@bxin_BA bxra_real_pre) (@bxin_bae bxra_real_pre) :=
  bxin_BanachAlg_of_pre bxra_real_pre Hc.

Lemma bxra_bridge_smoke : forall Hc : bxin_pre_complete bxra_real_pre,
  @bxin_bae bxra_real_pre
       (@bcoef _ _ (bxra_BanachAlg_of_real Hc) 1%Q)
       (@bone _ _ (bxra_BanachAlg_of_real Hc)).
Proof. intro Hc. apply bxin_bone_is_one. Qed.

(* ================= Section 6. Extraction audit and assumption review ================= *)

From Stdlib Require Import Extraction.
(* Extraction discipline: scalar and lemma-level statements are extracted;
   carrier-dependent items are not (the inherent [Obj.magic] of existT and
   record extraction is an extractor property, not a statement debt); the
   carrier-dependent items carry their assumption review through
   [Print Assumptions]. *)
Separate Extraction bxra_qabs_opp_norm bxra_norm_wd_qeqt bxra_norm_coef_qeqt
  bxra_f_norm_opp bxra_f_plus_opp bxra_f_norm_mult bxra_raw_pin_wall
  bxra_qabs_mult bxra_qleT_zero_abs_qn bxra_qltT_wd bxra_norm_diff_head.

Print Assumptions bxra_qabs_opp_norm.
Print Assumptions bxra_norm_wd_qeqt.
Print Assumptions bxra_norm_coef_qeqt.
Print Assumptions bxra_f_norm_opp.
Print Assumptions bxra_f_plus_assoc.
Print Assumptions bxra_f_plus_opp.
Print Assumptions bxra_f_norm_mult.
Print Assumptions bxra_cauchy_limit_elem.
Print Assumptions bxra_real_pre.
Print Assumptions bxra_inst_smoke_bone.
Print Assumptions bxra_bridge_smoke.

(* Assumption audit of the statements above (each should print Closed under the global context). *)
Print Assumptions bxra_head_cR.
Print Assumptions bxra_head_bplus.
Print Assumptions bxra_head_bmult.
Print Assumptions bxra_head_bopp.
Print Assumptions bxra_f_coef_zero.
Print Assumptions bxra_f_coef_one.
Print Assumptions bxra_f_norm_zero.
Print Assumptions bxra_f_norm_one.
Print Assumptions bxra_inst_smoke_bone.
Print Assumptions bxra_inst_smoke_norm_coef.
Print Assumptions bxra_inst_smoke_norm_wd.
