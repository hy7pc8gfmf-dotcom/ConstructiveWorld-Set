(* ConstructiveWorld-Set — Banach-algebra instances over a gcd-canonical
   rational scalar form. *)

(** * UpReqBanachInstB: canonical-form instance battery for the rational
      free-term algebra.

    Mission.  [bxib_qnorm] maps every rational to a canonical
      representative: fully reduced by the gcd of numerator and
      denominator, positive denominator, zero mapped to [0#1].  Since
      [Id] pins exact representatives, numerically equal rationals are
      not interchangeable before normalization; equality obligations are
      discharged by reducing both sides to canonical form
      ([bxib_qnorm_id_of_qeqT]).  Main statements: [bxib_coef_half_canon],
      [bxib_zero_canon_lit], [bxib_zero_canon_all], [bxib_canon_pin_wall],
      and the [bxib_E] free-term-tree carrier batteries.

    Dependencies.  Stdlib [QArith], [ZArith], [Znumtheory], [Lia];
      requires [S01_BaseRing], [S02_CauchyComplete] of this development.

    References.  The ConstructiveWorld-Main baseline module of the same
      name; statement names carried over verbatim.

    Constructivity.  All named statements and fields are carried by
      [Set] ([Id], [QeqT], [QleT'], [And]); extraction reports
      [Obj.magic] = 0; [coqchk] reports [Axioms: none].  Positive
      division routes through [Z.div] plus [Z.to_pos]; goals containing
      [Z.gcd] or [Z.div] must not be [simpl]-ed.

    Build.  [coqc -native-compiler no -q -Q . "" UpReqBanachInstB.v]
      compiles cleanly (exit 0); artifact magic [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import ZArith.ZArith ZArith.Znumtheory.
From Stdlib Require Import Lia.

(* ================= Section 1. The canonical form [bxib_qnorm] ================= *)

Definition bxib_qnorm (q : Q) : Q :=
  match q with
  | Qmake n d =>
      match n with
      | Z0 => (0#1)%Q
      | _ => let g := Z.gcd n (Z.pos d) in
             Qmake (Z.div n g) (Z.to_pos (Z.div (Z.pos d) g))
      end
  end.

(* Canonical expanded shape (denominator positivity follows from d >= g >= 1; the shape lemmas serve rewriting). *)
Lemma bxib_qnorm_pos_shape : forall (p d : positive),
  (@Id Q (bxib_qnorm (Qmake (Zpos p) d))
    (Qmake (Z.div (Zpos p) (Z.gcd (Zpos p) (Z.pos d)))
        (Z.to_pos (Z.div (Z.pos d) (Z.gcd (Zpos p) (Z.pos d)))))).
Proof. intros p d. reflexivity. Qed.

Lemma bxib_qnorm_neg_shape : forall (p d : positive),
  (@Id Q (bxib_qnorm (Qmake (Zneg p) d))
    (Qmake (Z.div (Zneg p) (Z.gcd (Zneg p) (Z.pos d)))
        (Z.to_pos (Z.div (Z.pos d) (Z.gcd (Zneg p) (Z.pos d)))))).
Proof. intros p d. reflexivity. Qed.

(* ================= Base piece 1: the half pinning under the canonical
   coefficient norm.  With [bcnorm := Qabs ∘ bxib_qnorm] the equation
   pinning [2#4] to [1#2] becomes a definitional equality. ================= *)

Definition bxib_bcnorm (q : Q) : Q := Qabs (bxib_qnorm q).

Lemma bxib_coef_half_canon : Id (bxib_bcnorm (2#4)%Q) (Qabs (1#2)%Q).
Proof.
  unfold bxib_bcnorm, bxib_qnorm. cbv iota zeta.
  replace (Z.gcd (Zpos 2) (Zpos 4)) with (Zpos 2) by reflexivity.
  replace (Z.div (Zpos 2) (Zpos 2)) with 1%Z by reflexivity.
  replace (Z.div (Z.pos 4) (Zpos 2)) with (Zpos 2) by reflexivity.
  change (Z.to_pos (Zpos 2)) with 2%positive.
  apply id_refl.
Qed.

(* Comparison: the canonical-form, provable version of [Id (2#4) (1#2)]. *)
Lemma bxib_half_quarter_canon_id : Id (bxib_qnorm (2#4)%Q) (1#2)%Q.
Proof.
  unfold bxib_qnorm. cbv iota zeta.
  replace (Z.gcd (Zpos 2) (Zpos 4)) with (Zpos 2) by reflexivity.
  replace (Z.div (Zpos 2) (Zpos 2)) with 1%Z by reflexivity.
  replace (Z.div (Z.pos 4) (Zpos 2)) with (Zpos 2) by reflexivity.
  change (Z.to_pos (Zpos 2)) with 2%positive.
  apply id_refl.
Qed.

(* ================= Base piece 2: canonical consistency of zero (the [0#16]/[0#1] position) ================= *)

(* Literal position: the unreduced [0#16] produced by [Qplus] normalizes to [0#1]. *)
Lemma bxib_zero_canon_lit : Id (bxib_qnorm (Qplus (2#4)%Q (Qopp (2#4)%Q))) (0#1)%Q.
Proof.
  unfold bxib_qnorm.
  change (Qplus (2#4)%Q (Qopp (2#4)%Q))
    with (Qmake (2 * Z.pos 4 + Z.opp 2 * Z.pos 4)%Z
                (4 * 4)%positive).
  replace (2 * Z.pos 4 + Z.opp 2 * Z.pos 4)%Z with 0%Z by ring.
  cbv iota zeta.
  apply id_refl.
Qed.

(* General position 1: zero with any denominator normalizes to [0#1] (closes by iota). *)
Lemma bxib_zero_canon_all : forall d : positive, Id (bxib_qnorm (0#d)%Q) (0#1)%Q.
Proof.
  intros d. unfold bxib_qnorm. cbv iota zeta.
  apply id_refl.
Qed.

(* General position 2: any rational plus its opposite normalizes to [0#1]. *)
Lemma bxib_zero_canon_opp : forall q : Q, Id (bxib_qnorm (Qplus q (Qopp q))) (0#1)%Q.
Proof.
  intros q. destruct q as [n d].
  change (Qplus (Qmake n d) (Qopp (Qmake n d)))
    with (Qmake (n * Z.pos d + Z.opp n * Z.pos d)%Z (d * d)%positive).
  replace (n * Z.pos d + Z.opp n * Z.pos d) with 0%Z by ring.
  apply id_refl.
Qed.

(* ================= Section 2. Uniqueness of the canonical form ================= *)

(* Exactness of division: if [g] divides [n] then [n = g * (n / g)]. *)
Lemma bxib_div_exact : forall n g : Z, g <> 0 -> Z.divide g n -> @Id Z n (g * (n / g)%Z).
Proof.
  intros n g Hg Hn.
  pose proof (Z_div_mod_eq_full n g) as E.
  rewrite (Zdivide_mod _ _ Hn) in E. rewrite Z.add_0_r in E.
  exact (match E in (_ = y) return @Id Z n y with eq_refl => id_refl end).
Qed.

(* The gcd of a nonzero numerator is nonzero. *)
Lemma bxib_gcd_nz : forall n d : Z, n <> 0 -> (Z.gcd n d <> 0)%Z.
Proof.
  intros n d Hn Hc. exact (Hn (Z.gcd_eq_0_l n d Hc)).
Qed.

(* Coprime transfer: for [g = Z.gcd n d] with [n] and [d] nonzero, the reduced factors [n/g] and [d/g] are coprime. *)
Lemma bxib_coprime_cofactor : forall n d : Z, n <> 0 -> d <> 0 ->
  rel_prime (n / Z.gcd n d) (d / Z.gcd n d).
Proof.
  intros n d Hn Hd.
  assert (HG : (Z.gcd n d <> 0)%Z) by (apply bxib_gcd_nz; exact Hn).
  assert (HN : Z.divide (Z.gcd n d) n) by apply Z.gcd_divide_l.
  assert (HD : Z.divide (Z.gcd n d) d) by apply Z.gcd_divide_r.
  pose proof (bxib_div_exact n (Z.gcd n d) HG HN) as En.
  pose proof (bxib_div_exact d (Z.gcd n d) HG HD) as Ed.
  assert (En' : n = Z.gcd n d * (n / Z.gcd n d)%Z)
    by (exact (match En in (@Id _ _ y) return (n = y)
               with id_refl => eq_refl end)).
  assert (Ed' : d = Z.gcd n d * (d / Z.gcd n d)%Z)
    by (exact (match Ed in (@Id _ _ y) return (d = y)
               with id_refl => eq_refl end)).
  apply Zis_gcd_intro.
  - apply Z.divide_1_l.
  - apply Z.divide_1_l.
  - intros z Hz1 Hz2.
    destruct Hz1 as [k1 Ek1]. destruct Hz2 as [k2 Ek2].
    assert (Hzn : Z.divide (z * Z.gcd n d) n).
    { exists k1. rewrite En' at 1. rewrite Ek1. ring. }
    assert (Hzd : Z.divide (z * Z.gcd n d) d).
    { exists k2. rewrite Ed' at 1. rewrite Ek2. ring. }
    pose proof (Zgcd_is_gcd n d) as Hg3.
    destruct Hg3 as [_ _ Hdiv].
    destruct (Hdiv (z * Z.gcd n d) Hzn Hzd) as [j Ej].
    assert (E1 : (Z.gcd n d * 1 = Z.gcd n d * (z * j))%Z)
      by (rewrite Ej at 1; ring).
    pose proof (Z.mul_reg_l 1 (z * j) (Z.gcd n d) HG E1) as E2.
    exists j. rewrite Z.mul_comm. exact E2.
Qed.

(* A single-variable cancellation bridge avoiding nonlinear tactics (pure rewriting plus [Z.mul_reg_l]). *)
Lemma bxib_cancel_aux : forall N E M D X Y Z1 W G1 G2 : Z,
  N = G1 * X -> E = G2 * Y -> M = G2 * Z1 -> D = G1 * W ->
  N * E = M * D -> G1 * G2 <> 0 -> G1 <> 0 -> G2 <> 0 ->
  @Id Z (X * Y) (Z1 * W).
Proof.
  intros N E M D X Y Z1 W G1 G2 HN HE HM HD Hc HG12 HG1 HG2.
  assert (T : ((N * E) * (G1 * G2) = (M * D) * (G1 * G2))%Z)
    by (rewrite Hc; reflexivity).
  rewrite HN, HE, HM, HD in T.
  rewrite (Z.mul_comm _ (G1 * G2)) in T.
  rewrite (Z.mul_comm _ (G1 * G2)) in T.
  pose proof (Z.mul_reg_l _ _ (G1 * G2) HG12 T) as T1.
  rewrite (Z.mul_comm (G2 * Z1) (G1 * W)) in T1.
  assert (Hp : (G1 * G2 * (X * Y) = G1 * G2 * (Z1 * W))%Z).
  { transitivity ((G1 * X) * (G2 * Y))%Z.
    - ring.
    - rewrite T1. ring. }
  exact (match Z.mul_reg_l (X * Y) (Z1 * W) (G1 * G2) HG12 Hp
         in (_ = y) return @Id Z (X * Y) y
         with eq_refl => id_refl end).
Qed.

(* Core: uniqueness of reduced cross-products (Gauss / [rel_prime_cross_prod] face). *)
Lemma bxib_cross_unique : forall n d m e : Z,
  n <> 0 -> m <> 0 -> 0 < d -> 0 < e -> (n * e = m * d)%Z ->
  And (@Id Z (n / Z.gcd n d) (m / Z.gcd m e))
      (@Id Z (d / Z.gcd n d) (e / Z.gcd m e)).
Proof.
  intros n d m e Hn Hm Hd He Hcross.
  assert (HG1 : (Z.gcd n d <> 0)%Z) by (apply bxib_gcd_nz; exact Hn).
  assert (HG2 : (Z.gcd m e <> 0)%Z) by (apply bxib_gcd_nz; exact Hm).
  assert (HG1p : (0 < Z.gcd n d)%Z) by (pose proof (Z.gcd_nonneg n d); lia).
  assert (HG2p : (0 < Z.gcd m e)%Z) by (pose proof (Z.gcd_nonneg m e); lia).
  pose proof (bxib_div_exact n (Z.gcd n d) HG1 (Z.gcd_divide_l n d)) as En.
  pose proof (bxib_div_exact d (Z.gcd n d) HG1 (Z.gcd_divide_r n d)) as Ed.
  assert (En' : n = Z.gcd n d * (n / Z.gcd n d)%Z)
    by (exact (match En in (@Id _ _ y) return (n = y)
               with id_refl => eq_refl end)).
  assert (Ed' : d = Z.gcd n d * (d / Z.gcd n d)%Z)
    by (exact (match Ed in (@Id _ _ y) return (d = y)
               with id_refl => eq_refl end)).
  pose proof (bxib_div_exact m (Z.gcd m e) HG2 (Z.gcd_divide_l m e)) as Em.
  pose proof (bxib_div_exact e (Z.gcd m e) HG2 (Z.gcd_divide_r m e)) as Ee.
  assert (Em' : m = Z.gcd m e * (m / Z.gcd m e)%Z)
    by (exact (match Em in (@Id _ _ y) return (m = y)
               with id_refl => eq_refl end)).
  assert (Ee' : e = Z.gcd m e * (e / Z.gcd m e)%Z)
    by (exact (match Ee in (@Id _ _ y) return (e = y)
               with id_refl => eq_refl end)).
  assert (Hdz : ((d / Z.gcd n d) <> 0)%Z).
  { intro Hz. rewrite Hz in Ed'. lia. }
  assert (Hez : ((e / Z.gcd m e) <> 0)%Z).
  { intro Hz. rewrite Hz in Ee'. lia. }
  assert (Hbp : (0 < d / Z.gcd n d)%Z).
  { assert ((0 <= d / Z.gcd n d)%Z) by (apply Z.div_pos; lia). lia. }
  assert (Hdp : (0 < e / Z.gcd m e)%Z).
  { assert ((0 <= e / Z.gcd m e)%Z) by (apply Z.div_pos; lia). lia. }
  assert (HG12 : (Z.gcd n d * Z.gcd m e <> 0)%Z).
  { intro Hzz. apply (Z.mul_eq_0 (Z.gcd n d) (Z.gcd m e)) in Hzz.
    destruct Hzz as [E | E]; contradiction. }
  assert (Hc1 : ((n / Z.gcd n d) * (e / Z.gcd m e)
              = (m / Z.gcd m e) * (d / Z.gcd n d))%Z).
  { exact (match bxib_cancel_aux n e m d
      (n / Z.gcd n d) (e / Z.gcd m e) (m / Z.gcd m e) (d / Z.gcd n d)
      (Z.gcd n d) (Z.gcd m e) En' Ee' Em' Ed' Hcross HG12 HG1 HG2
      in (@Id _ _ y)
      return ((n / Z.gcd n d) * (e / Z.gcd m e)%Z = y)
      with id_refl => eq_refl end). }
  assert (Hbp2 : (d / Z.gcd n d > 0)%Z) by (apply (proj2 (Z.compare_gt_iff _ 0)); exact Hbp).
  assert (Hdp2 : (e / Z.gcd m e > 0)%Z) by (apply (proj2 (Z.compare_gt_iff _ 0)); exact Hdp).
  assert (Hc1' : (n / Z.gcd n d * (e / Z.gcd m e)
                = d / Z.gcd n d * (m / Z.gcd m e))%Z).
  { rewrite (Z.mul_comm (d / Z.gcd n d) (m / Z.gcd m e)). exact Hc1. }
  destruct (rel_prime_cross_prod (n / Z.gcd n d) (d / Z.gcd n d)
                                 (m / Z.gcd m e) (e / Z.gcd m e)
    (bxib_coprime_cofactor n d Hn ltac:(lia)) (bxib_coprime_cofactor m e Hm ltac:(lia))
    Hbp2 Hdp2 Hc1') as [E1 E2].
  split.
  - exact (match E1 in (_ = y) return @Id Z (n / Z.gcd n d) y
           with eq_refl => id_refl end).
  - exact (match E2 in (_ = y) return @Id Z (d / Z.gcd n d) y
           with eq_refl => id_refl end).
Qed.

(* Workhorse: the canonical form is unique under the decidable equality [QeqT], so [Id] obligations discharge. *)
Lemma bxib_qnorm_id_of_qeqT : forall x y : Q, QeqT x y -> Id (bxib_qnorm x) (bxib_qnorm y).
Proof.
  intros x y HT.
  assert (Heq : x == y) by (apply qeqT_imp_qeq; exact HT).
  destruct x as [n d]; destruct y as [m e].
  unfold Qeq in Heq; simpl in Heq.
  destruct n as [|p|p]; destruct m as [|q|q].
  - apply id_refl.
  - exfalso; nia.
  - exfalso; nia.
  - exfalso; nia.
  - (* Zpos Zpos *)
    destruct (bxib_cross_unique (Z.pos p) (Z.pos d) (Z.pos q) (Z.pos e)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heq) as [H1 H2].
    rewrite (bxib_qnorm_pos_shape p d), (bxib_qnorm_pos_shape q e).
    rewrite H1, H2. apply id_refl.
  - exfalso; nia.
  - exfalso; nia.
  - exfalso; nia.
  - (* Zneg Zneg *)
    destruct (bxib_cross_unique (Z.neg p) (Z.pos d) (Z.neg q) (Z.pos e)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heq) as [H1 H2].
    rewrite (bxib_qnorm_neg_shape p d), (bxib_qnorm_neg_shape q e).
    rewrite H1, H2. apply id_refl.
Qed.

(* Equivalent form: [Qeq] (the Prop engine face) in, [Id] (the Set face) out. *)
Lemma bxib_qnorm_id_of_qeq : forall x y : Q, x == y -> Id (bxib_qnorm x) (bxib_qnorm y).
Proof.
  intros x y H. exact (bxib_qnorm_id_of_qeqT x y (qeq_imp_qeqT x y H)).
Qed.

(* ---- QeqT utility lemmas ---- *)

Lemma bxib_qeqT_refl : forall x : Q, QeqT x x.
Proof. intro x. apply qeq_imp_qeqT. apply Qeq_refl. Qed.

Lemma bxib_qeqT_of_id : forall x y : Q, Id x y -> QeqT x y.
Proof.
  intros x y H. destruct H. apply bxib_qeqT_refl.
Qed.

Lemma bxib_qnorm_qeqT_of_qeqT : forall x y : Q,
  QeqT x y -> QeqT (bxib_qnorm x) (bxib_qnorm y).
Proof.
  intros x y H. apply bxib_qeqT_of_id.
  apply bxib_qnorm_id_of_qeqT. exact H.
Qed.

Lemma bxib_qeqT_sym : forall x y : Q, QeqT x y -> QeqT y x.
Proof.
  intros x y H. apply qeq_imp_qeqT. apply Qeq_sym.
  apply qeqT_imp_qeq. exact H.
Qed.

Lemma bxib_qeqT_trans : forall x y z : Q, QeqT x y -> QeqT y z -> QeqT x z.
Proof.
  intros x y z H1 H2. apply qeq_imp_qeqT.
  exact (Qeq_trans x y z (qeqT_imp_qeq _ _ H1) (qeqT_imp_qeq _ _ H2)).
Qed.

Lemma bxib_qeqT_cong_plus : forall a b c d : Q,
  QeqT a b -> QeqT c d -> QeqT (Qplus a c) (Qplus b d).
Proof.
  intros a b c d Hab Hcd.
  apply qeq_imp_qeqT.
  apply qeqT_imp_qeq in Hab. apply qeqT_imp_qeq in Hcd.
  rewrite <- Hab, <- Hcd. apply Qeq_refl.
Qed.

Lemma bxib_qeqT_cong_opp : forall a b : Q, QeqT a b -> QeqT (Qopp a) (Qopp b).
Proof.
  intros a b H. apply qeq_imp_qeqT.
  apply qeqT_imp_qeq in H.
  destruct a as [n d]; destruct b as [m e].
  unfold Qeq in H; simpl in H. unfold Qeq; simpl.
  assert (H2 : (Z.opp n * Z.pos e = Z.opp (n * Z.pos e))%Z) by ring.
  assert (H3 : (Z.opp m * Z.pos d = Z.opp (m * Z.pos d))%Z) by ring.
  rewrite H2, H3, H. reflexivity.
Qed.
(* The [Qeq] constructor at the [Qmake] level (avoids projections in goals). *)
Lemma bxib_qeq_make : forall (a1 : Z) (b1 : positive) (a2 : Z) (b2 : positive),
  (a1 * Z.pos b2 = a2 * Z.pos b1)%Z -> Qeq (Qmake a1 b1) (Qmake a2 b2).
Proof. intros a1 b1 a2 b2 H. unfold Qeq. simpl. exact H. Qed.

Lemma bxib_qnorm_fix : forall t : Q, QeqT (bxib_qnorm t) t.
Proof.
  intros t. apply qeq_imp_qeqT. destruct t as [n d]. unfold Qeq.
  destruct n as [|p|p].
  - change (bxib_qnorm (Qmake Z0 d)) with (0#1)%Q. simpl. lia.
  - change (Qeq (bxib_qnorm (Qmake (Zpos p) d)) (Qmake (Zpos p) d))
      with (Qeq (Qmake (Z.div (Zpos p) (Z.gcd (Zpos p) (Z.pos d)))
                        (Z.to_pos (Z.div (Z.pos d) (Z.gcd (Zpos p) (Z.pos d)))))
                (Qmake (Zpos p) d)).
    apply bxib_qeq_make.
    assert (HG : (Z.gcd (Zpos p) (Z.pos d) <> 0)%Z).
    { intro Hc. pose proof (Z.gcd_eq_0_r _ _ Hc). lia. }
    pose proof (bxib_div_exact (Zpos p) (Z.gcd (Zpos p) (Z.pos d)) HG
      (Z.gcd_divide_l (Zpos p) (Z.pos d))) as En.
    pose proof (bxib_div_exact (Z.pos d) (Z.gcd (Zpos p) (Z.pos d)) HG
      (Z.gcd_divide_r (Zpos p) (Z.pos d))) as Ed.
    assert (Edq : Z.pos d = Z.gcd (Zpos p) (Z.pos d)
                            * (Z.div (Z.pos d) (Z.gcd (Zpos p) (Z.pos d))))
      by (exact (match Ed in (@Id _ _ y) return (Z.pos d = y)
                 with id_refl => eq_refl end)).
    assert (HGp : (0 < Z.gcd (Zpos p) (Z.pos d))%Z)
      by (pose proof (Z.gcd_nonneg (Zpos p) (Z.pos d)); lia).
    assert (Hq : (0 < Z.div (Z.pos d) (Z.gcd (Zpos p) (Z.pos d)))%Z).
    { assert ((0 <= Z.div (Z.pos d) (Z.gcd (Zpos p) (Z.pos d)))%Z)
        by (apply Z.div_pos; lia).
      destruct (Z.eq_dec (Z.div (Z.pos d) (Z.gcd (Zpos p) (Z.pos d))) 0)
        as [Ez|Ez].
      - rewrite Ez in Edq. lia.
      - lia. }
    remember (Z.gcd (Zpos p) (Z.pos d)) as G eqn:HGm.
    remember (Z.div (Zpos p) G) as N1 eqn:HN1m.
    remember (Z.div (Z.pos d) G) as D1 eqn:HD1m.
    rewrite (Z2Pos.id D1 Hq).
    rewrite Ed, En. ring.
  - change (Qeq (bxib_qnorm (Qmake (Zneg p) d)) (Qmake (Zneg p) d))
      with (Qeq (Qmake (Z.div (Zneg p) (Z.gcd (Zneg p) (Z.pos d)))
                        (Z.to_pos (Z.div (Z.pos d) (Z.gcd (Zneg p) (Z.pos d)))))
                (Qmake (Zneg p) d)).
    apply bxib_qeq_make.
    assert (HG : (Z.gcd (Zneg p) (Z.pos d) <> 0)%Z).
    { intro Hc. pose proof (Z.gcd_eq_0_r _ _ Hc). lia. }
    pose proof (bxib_div_exact (Zneg p) (Z.gcd (Zneg p) (Z.pos d)) HG
      (Z.gcd_divide_l (Zneg p) (Z.pos d))) as En.
    pose proof (bxib_div_exact (Z.pos d) (Z.gcd (Zneg p) (Z.pos d)) HG
      (Z.gcd_divide_r (Zneg p) (Z.pos d))) as Ed.
    assert (Edq2 : Z.pos d = Z.gcd (Zneg p) (Z.pos d)
                             * (Z.div (Z.pos d) (Z.gcd (Zneg p) (Z.pos d))))
      by (exact (match Ed in (@Id _ _ y) return (Z.pos d = y)
                 with id_refl => eq_refl end)).
    assert (HGp : (0 < Z.gcd (Zneg p) (Z.pos d))%Z)
      by (pose proof (Z.gcd_nonneg (Zneg p) (Z.pos d)); lia).
    assert (Hq : (0 < Z.div (Z.pos d) (Z.gcd (Zneg p) (Z.pos d)))%Z).
    { assert ((0 <= Z.div (Z.pos d) (Z.gcd (Zneg p) (Z.pos d)))%Z)
        by (apply Z.div_pos; lia).
      destruct (Z.eq_dec (Z.div (Z.pos d) (Z.gcd (Zneg p) (Z.pos d))) 0)
        as [Ez|Ez].
      - rewrite Ez in Edq2. lia.
      - lia. }
    remember (Z.gcd (Zneg p) (Z.pos d)) as G eqn:HGm.
    remember (Z.div (Zneg p) G) as N1 eqn:HN1m.
    remember (Z.div (Z.pos d) G) as D1 eqn:HD1m.
    rewrite (Z2Pos.id D1 Hq).
    rewrite Ed, En. ring.
Qed.


(* [Qabs] is invariant under [Qopp] (closes by constructor-level iota). *)
Lemma bxib_qabs_opp_raw : forall w : Q, Id (Qabs (Qopp w)) (Qabs w).
Proof.
  intros w. destruct w as [n d]; destruct n as [|p|p]; simpl.
  - apply id_refl.
  - apply id_refl.
  - apply id_refl.
Qed.

(* [Qabs] is nonnegative ([QleT'] face: the [Qle_bool] comparison computes). *)
Lemma bxib_qabs_nonneg : forall w : Q, QleT' 0 (Qabs w).
Proof.
  intros w. apply Qle_to_QleT'. unfold Qle, Qabs.
  destruct w as [n d]; destruct n as [|p|p]; simpl;
    try discriminate;
    try (rewrite Pos.mul_1_r;
         apply (proj2 (Z.compare_lt_iff 0 (Z.pos p))); lia).
Qed.

(* The fixed-point property in [Id] form. *)
Lemma bxib_qnorm_fix_id : forall t : Q,
  Id (bxib_qnorm (bxib_qnorm t)) (bxib_qnorm t).
Proof.
  intro t. exact (bxib_qnorm_id_of_qeqT (bxib_qnorm t) t (bxib_qnorm_fix t)).
Qed.

(* The canonical-form lift of [QeqT] to [Id], paying the fixed-point [Id] on each end. *)
Lemma bxib_id_of_qeqT_canon : forall x y : Q,
  Id (bxib_qnorm x) x -> Id (bxib_qnorm y) y -> QeqT x y -> Id x y.
Proof.
  intros x y Hx Hy H.
  exact (id_trans (id_trans (id_sym Hx) (bxib_qnorm_id_of_qeqT _ _ H)) Hy).
Qed.

(* Norm invariance of the canonical form under [Qopp] — the bridge lemma
   for the zero-position and [bnorm_opp] fields. *)
(* Remaining: needs a lemma that [Qopp] commutes with [bxib_qnorm] (the gcd
   is unchanged by negating the numerator); see the Section 4 notes. *)
(* Lemma bxib_qabs_opp_norm : forall u : Q,                       *)
(*   Id (Qabs (bxib_qnorm (Qopp u))) (Qabs (bxib_qnorm u)).        *)
(* Proof. ... Qed.                                                *)


(* ================= Section 3. The original pinning field is unsatisfiable ================= *)

(* The canonical coefficient norm [Qabs ∘ bxib_qnorm] cannot satisfy the
   original pinning field: if [Id (Qabs q) (Qabs (bxib_qnorm q))] held for
   all [q], then [2#4] and [1#2] would be Leibniz-equal — a false equation.
   Conclusion: canonical uniqueness settles the equality-face obligations;
   the pinning-field statement itself must be re-said over the canonical
   norm (the [bxib_E] carrier of Section 4 is assembled accordingly). *)
Lemma bxib_canon_pin_wall :
  (forall q : Q, Id (Qabs (bxib_qnorm q)) (Qabs q)) ->
  Id (2#4)%Q (1#2)%Q.
Proof.
  intro H. exact (id_sym (H (2#4)%Q)).
Qed.

(* ================= Section 4. The [bxib_E] free-term-tree carrier.
   The carrier is a tree of free terms: [bxib_esc] stores the original
   rational (keeping the pinning face exact) while operation nodes
   normalize; [bxib_bae] equates evaluation images in canonical form. ================= *)

Inductive bxib_E : Set :=
| bxib_ez : bxib_E
| bxib_esc : Q -> bxib_E
| bxib_eplus : bxib_E -> bxib_E -> bxib_E
| bxib_emult : bxib_E -> bxib_E -> bxib_E
| bxib_eopp : bxib_E -> bxib_E.

Fixpoint bxib_ev (a : bxib_E) : Q :=
  match a with
  | bxib_ez => (0#1)%Q
  | bxib_esc q => q
  | bxib_eplus x y => bxib_qnorm (Qplus (bxib_ev x) (bxib_ev y))
  | bxib_emult x y => bxib_qnorm (Qmult (bxib_ev x) (bxib_ev y))
  | bxib_eopp x => Qopp (bxib_ev x)
  end.

Definition bxib_bae (a b : bxib_E) : Set :=
  Id (bxib_qnorm (bxib_ev a)) (bxib_qnorm (bxib_ev b)).

Definition bxib_bnorm (a : bxib_E) : Q := Qabs (bxib_qnorm (bxib_ev a)).

(* ---- The three equivalence laws of [bxib_bae] ---- *)

Lemma bxib_bae_refl : forall a : bxib_E, bxib_bae a a.
Proof.
  intro a. exact (@id_refl _ (bxib_qnorm (bxib_ev a))).
Qed.

Lemma bxib_bae_sym : forall a b : bxib_E, bxib_bae a b -> bxib_bae b a.
Proof. intros a b H. exact (id_sym H). Qed.

Lemma bxib_bae_trans : forall a b c : bxib_E,
  bxib_bae a b -> bxib_bae b c -> bxib_bae a c.
Proof. intros a b c H1 H2. exact (id_trans H1 H2). Qed.

(* ---- Well-definedness pieces (pure congruence under canonical [bxib_bae]) ---- *)

(* [bxib_bplus_wd] (double canonical contraction under canonical equality): remaining. *)
(* Lemma bxib_bplus_wd : forall a b c d : bxib_E, ... Qed.          *)


(* [bxib_bopp_wd]: same double-contraction position as [bxib_bplus_wd], likewise remaining. *)
(* Lemma bxib_bopp_wd : forall a b : bxib_E, ... Qed.               *)


Lemma bxib_bnorm_wd : forall a b : bxib_E,
  bxib_bae a b -> Id (bxib_bnorm a) (bxib_bnorm b).
Proof. intros a b H. exact (id_cong Qabs H). Qed.

(* ---- Additive abelian group ([QeqT] engine plus the Section 2 workhorse) ---- *)

Lemma bxib_bplus_comm : forall a b : bxib_E,
  bxib_bae (bxib_eplus a b) (bxib_eplus b a).
Proof.
  intros a b. exact (bxib_qnorm_id_of_qeqT (bxib_ev (bxib_eplus a b)) (bxib_ev (bxib_eplus b a)) (bxib_qnorm_qeqT_of_qeqT (bxib_ev a + bxib_ev b)%Q (bxib_ev b + bxib_ev a)%Q (qeq_imp_qeqT (bxib_ev a + bxib_ev b)%Q (bxib_ev b + bxib_ev a)%Q (Qplus_comm (bxib_ev a) (bxib_ev b))))).
Qed.

Lemma bxib_bplus_assoc : forall a b c : bxib_E,
  bxib_bae (bxib_eplus a (bxib_eplus b c))
           (bxib_eplus (bxib_eplus a b) c).
Proof.
  intros a b c.
  pose proof (bxib_qnorm_fix (Qplus (bxib_ev b) (bxib_ev c))) as F1.
  pose proof (bxib_qnorm_fix (Qplus (bxib_ev a) (bxib_ev b))) as F2.
  pose proof (bxib_qnorm_id_of_qeqT
    (Qplus (bxib_ev a) (Qplus (bxib_ev b) (bxib_ev c)))
    (Qplus (Qplus (bxib_ev a) (bxib_ev b)) (bxib_ev c))
    (qeq_imp_qeqT _ _ (Qplus_assoc _ _ _))) as Hm.
  pose proof (bxib_qnorm_id_of_qeqT
    (Qplus (bxib_ev a) (bxib_qnorm (Qplus (bxib_ev b) (bxib_ev c))))
    (Qplus (bxib_ev a) (Qplus (bxib_ev b) (bxib_ev c)))
    (bxib_qeqT_cong_plus _ _ _ _ (bxib_qeqT_refl (bxib_ev a)) F1)) as Hl.
  pose proof (bxib_qnorm_id_of_qeqT
    (Qplus (Qplus (bxib_ev a) (bxib_ev b)) (bxib_ev c))
    (Qplus (bxib_qnorm (Qplus (bxib_ev a) (bxib_ev b))) (bxib_ev c))
    (bxib_qeqT_cong_plus _ _ _ _ (bxib_qeqT_sym _ _ F2)
                         (bxib_qeqT_refl (bxib_ev c)))) as Hr.
  exact (bxib_qnorm_id_of_qeqT _ _
    (bxib_qeqT_of_id _ _ (id_trans (id_trans Hl Hm) Hr))).
Qed.

Lemma bxib_bplus_zero : forall a : bxib_E,
  bxib_bae (bxib_eplus a bxib_ez) a.
Proof.
  intro a. apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxib_qnorm (bxib_ev a)) _).
  - apply bxib_qnorm_qeqT_of_qeqT. apply qeq_imp_qeqT. apply Qplus_0_r.
  - apply bxib_qnorm_fix.
Qed.

Lemma bxib_bplus_opp : forall a : bxib_E,
  bxib_bae (bxib_eplus a (bxib_eopp a)) bxib_ez.
Proof.
  intro a. apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qnorm_qeqT_of_qeqT
    (Qplus (bxib_ev a) (Qopp (bxib_ev a))) (0#1)%Q).
  apply qeq_imp_qeqT. apply Qplus_opp_r.
Qed.

(* ---- Scalar embedding laws ---- *)

Lemma bxib_bcoef_zero : bxib_bae (bxib_esc 0%Q) bxib_ez.
Proof. apply id_refl. Qed.

Lemma bxib_bcoef_one : bxib_bae (bxib_esc 1%Q) (bxib_esc 1%Q).
Proof. apply id_refl. Qed.

Lemma bxib_bcoef_mult : forall q r : Q,
  bxib_bae (bxib_esc (q * r)%Q) (bxib_emult (bxib_esc q) (bxib_esc r)).
Proof.
  intros q r. apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_sym. apply bxib_qnorm_fix.
Qed.

Lemma bxib_bcoef_comm : forall (q : Q) (a : bxib_E),
  bxib_bae (bxib_emult a (bxib_esc q)) (bxib_emult (bxib_esc q) a).
Proof.
  intros q a. apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans
    (bxib_qnorm (Qmult (bxib_ev a) q)) (Qmult q (bxib_ev a))
    (bxib_qnorm (Qmult q (bxib_ev a)))).
  - apply (bxib_qeqT_trans
      (bxib_qnorm (Qmult (bxib_ev a) q)) (Qmult (bxib_ev a) q)
      (Qmult q (bxib_ev a))).
    + apply bxib_qnorm_fix.
    + apply qeq_imp_qeqT. apply Qmult_comm.
  - apply bxib_qeqT_sym. apply bxib_qnorm_fix.
Qed.

(* ---- Norm pinning family (statements taken over [Qabs ∘ bxib_qnorm], per Section 3) ---- *)

Lemma bxib_bnorm_zero : Id (bxib_bnorm bxib_ez) 0%Q.
Proof.
  unfold bxib_bnorm, bxib_ev, bxib_qnorm, Qabs. cbv iota zeta.
  replace (Z.abs 0)%Z with 0%Z by reflexivity.
  apply id_refl.
Qed.

Lemma bxib_bnorm_one : Id (bxib_bnorm (bxib_esc 1%Q)) 1%Q.
Proof.
  unfold bxib_bnorm, bxib_ev, bxib_qnorm, Qabs. cbv iota zeta.
  replace (Z.gcd (Zpos 1) (Z.pos 1)) with (Zpos 1) by reflexivity.
  replace (Z.div (Zpos 1) (Zpos 1)) with (Zpos 1) by reflexivity.
  replace (Z.abs (Zpos 1))%Z with (Zpos 1) by reflexivity.
  change (Z.to_pos (Zpos 1)) with 1%positive.
  apply id_refl.
Qed.

Lemma bxib_bnorm_pos : forall a : bxib_E, QleT' 0 (bxib_bnorm a).
Proof.
  intro a. unfold bxib_bnorm.
  exact (bxib_qabs_nonneg (bxib_qnorm (bxib_ev a))).
Qed.

(* The canonical-form pinning field (the [1/2] position, i.e. the carrier form of [bxib_coef_half_canon]). *)
Lemma bxib_bnorm_coef_canon : forall q : Q,
  Id (bxib_bnorm (bxib_esc q)) (Qabs (bxib_qnorm q)).
Proof.
  intro q. unfold bxib_bnorm. cbn [bxib_ev].
  apply id_refl.
Qed.

(* Pinning smoke test: [esc (2#4)] and [esc (1#2)] have equal norms. *)
Lemma bxib_bnorm_half_quarter_smoke :
  Id (bxib_bnorm (bxib_esc (2#4)%Q)) (bxib_bnorm (bxib_esc (1#2)%Q)).
Proof.
  unfold bxib_bnorm, bxib_ev, bxib_qnorm. cbv iota zeta.
  replace (Z.gcd (Zpos 2) (Zpos 4)) with (Zpos 2) by reflexivity.
  replace (Z.gcd (Zpos 1) (Z.pos 2)) with (Zpos 1) by reflexivity.
  replace (Z.div (Zpos 2) (Zpos 2)) with 1%Z by reflexivity.
  replace (Z.div (Z.pos 4) (Zpos 2)) with (Zpos 2) by reflexivity.
  replace (Z.div (Zpos 1) (Zpos 1)) with 1%Z by reflexivity.
  replace (Z.div (Z.pos 2) (Zpos 1)) with (Zpos 2) by reflexivity.
  change (Z.to_pos (Zpos 2)) with 2%positive.
  apply id_refl.
Qed.

(* ================= Remaining fields (declared honestly; no admits) ================= *)
(* 0'. The [bxib_bplus_wd] position: the double-contraction chain is
   identified but not yet closed (the other two wd pieces are present). *)
(* 0. The [bnorm_opp] position (the [Qabs ∘ Qopp] identity): needs a lemma
   that [Qopp] commutes with [bxib_qnorm] (the gcd is unchanged by
   negating the numerator; the mod-0 side condition of [Z.div_opp_l_z]
   is pending). *)
(* 1. Multiplicative associativity / unit / distributivity and the
   [bnorm_plus] / [bnorm_mult] fields: the carrier and [bxib_bae] are
   fixed; assembled as for addition (stdlib [Qmult]/[Qabs] engine plus
   the Section 2 workhorse). *)
(* 2. Completeness fields: remain as in the predecessor instance module
   (the [bxin_BanachAlgPre] plus assembly-bridge dependency stands). *)
(* 3. The unsatisfiability of the original [bnorm_coef] pinning statement
   under the canonical norm is shown in Section 3. *)

(* ================= Extraction audit ================= *)
From Stdlib Require Import Extraction.
Separate Extraction bxib_qnorm bxib_coef_half_canon bxib_zero_canon_lit
  bxib_zero_canon_opp bxib_qnorm_id_of_qeqT bxib_canon_pin_wall
  bxib_bplus_assoc bxib_bplus_opp bxib_bnorm_wd bxib_bnorm_coef_canon.

Print Assumptions bxib_qnorm_id_of_qeqT.
Print Assumptions bxib_coef_half_canon.
Print Assumptions bxib_zero_canon_opp.
Print Assumptions bxib_canon_pin_wall.

(* Canonical fixed point: [QeqT (bxib_qnorm t) t] — the lemma through which field chains re-root at the canonical form. *)

(* Assumption audit of the statements above (each should print Closed under the global context). *)
Print Assumptions bxib_coef_half_canon.
Print Assumptions bxib_half_quarter_canon_id.
Print Assumptions bxib_zero_canon_lit.
Print Assumptions bxib_zero_canon_all.
Print Assumptions bxib_bnorm_zero.
Print Assumptions bxib_bnorm_one.
Print Assumptions bxib_bnorm_coef_canon.
Print Assumptions bxib_bnorm_half_quarter_smoke.
Print Assumptions bxib_bnorm_pos.
