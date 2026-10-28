(* ConstructiveWorld-Set — factorial-sum escape machinery: an explicit escape
   rank witnessing that exponential partial sums never absorb a rational. *)
(** * SumInvFactEscape: factorial-sum escape certificates in exact rational
      arithmetic.

    Mission.  For the rational exponential series [exp_series n 1] (partial
      sums of [1/k!]), every rational [q] admits an explicit rank [n] with
      [1 < Qabs (q_fact n * (q - exp_series n 1))]: [n! * (q - s_n)] never
      converges to zero.  Main statements: [sif_escape] and [sif_escape_closed]
      (the corollary at the upstream shape [sif_sum_inv_fact_escape]).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
      [Arith.Arith], [Bool.Bool], [Arith.Factorial], [Lia], [Setoid],
      [Morphisms], [Extraction].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp] and [UpReqBanachNormOpp] of this
      development.

    References.  This development, UpReqBanachNormOpp.v, the
      ConstructiveWorld-Main baseline module whose escape goal on [1/k!]
      sums carries over verbatim, discharged by an integer-skeleton witness.

    Constructivity.  All named statements are carried by [Set]/[Type]
      ([sigT], [QltT], [QeqT], [Id], [NatLe]); witnesses come from the
      bounded enumeration [sif_enum] over decidable [Qlt_bool] tests;
      statements extract with [Obj.magic] = 0 and [Print Assumptions]
      reports [Closed under the global context].

    Build.  [rocq c -native-compiler no -q -Q . "" SumInvFactEscape.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachNormOpp.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lia Setoid Morphisms.

(* ============================================================ *)
(* Section 0. Generic Q-layer congruence lemmas (no division semantics) *)
(* ============================================================ *)

Lemma sif_posZ : forall p : positive, Id (Z.ltb 0%Z (Z.pos p)) true.
Proof. intro p. exact id_refl. Qed.

Lemma sif_Zpos_mul : forall (bp df : positive),
  Id (Z.pos (Pos.mul bp df)) (Z.pos bp * Z.pos df)%Z.
Proof. intros bp df. exact id_refl. Qed.

Lemma sif_Qmake_eta : forall q : Q, QeqT (Qmake (Qnum q) (Qden q))%Q q.
Proof. intro q. destruct q as [a b]. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma sif_minus_make : forall q r : Q,
  QeqT (q - r)%Q
       ((Qnum q * Zpos (Qden r) - Qnum r * Zpos (Qden q))
        # (Qden q * Qden r))%Q.
Proof.
  intros q r. apply qeq_imp_qeqT.
  destruct q as [a b]. destruct r as [c d].
  unfold Qminus, Qeq. cbn [Qnum Qden Qplus Qopp Qmult].
  ring.
Qed.

Lemma sif_minus_comp_r : forall x y z : Q, x == y -> QeqT (x - z)%Q (y - z)%Q.
Proof.
  intros x y z H. apply qeq_imp_qeqT.
  destruct x as [a b]. destruct y as [c d]. destruct z as [e f].
  unfold Qeq in H. unfold Qminus, Qeq.
  cbn [Qnum Qden Qplus Qopp Qmult] in *.
  rewrite (Pos2Z.inj_mul b f), (Pos2Z.inj_mul d f).
  (* The goal keeps atomic Z products (positivity of Q denominators
   cancels them away); linear lia has no witness at that depth, so nia
   finishes the goal. *)
  nia.
Qed.

Lemma sif_mult_comp_l : forall x y z : Q, x == y -> QeqT (x * z) (y * z).
Proof.
  intros x y z H. apply qeq_imp_qeqT.
  destruct x as [a b]. destruct y as [c d]. destruct z as [e f].
  unfold Qeq in H. unfold Qeq.
  cbn [Qnum Qden Qmult] in *.
  rewrite (Pos2Z.inj_mul b f), (Pos2Z.inj_mul d f).
  (* The goal is a degree-three Z monomial identity: from
   [H : a * Z.pos d = c * Z.pos b] multiplied by [Zpos f * e]
   (denominator positivity cancels).  nia multiplication depth does
   not suffice, so the identity is reduced to zero by ring rewrites
   and linear lia ([Qden] is a positive, hence the [Zpos] lifting). *)
  assert (Hd : ((a*e)*(Zpos d * Zpos f) = (c*e)*(Zpos b * Zpos f))%Z).
  { assert (Hd1 : ((a*e)*(Zpos d * Zpos f))%Z
                  = ((a * Zpos d) * (e * Zpos f))%Z) by ring.
    assert (Hd2 : ((c*e)*(Zpos b * Zpos f))%Z
                  = ((c * Zpos b) * (e * Zpos f))%Z) by ring.
    rewrite Hd1, Hd2, H. reflexivity. }
  lia.
Qed.

Lemma sif_mult_comp_r : forall x y z : Q, x == y -> QeqT (z * x) (z * y).
Proof.
  intros x y z H. apply qeq_imp_qeqT.
  destruct x as [a b]. destruct y as [c d]. destruct z as [e f].
  unfold Qeq in H. unfold Qeq.
  cbn [Qnum Qden Qmult] in *.
  rewrite (Pos2Z.inj_mul f b), (Pos2Z.inj_mul f d).
  (* The goal is a degree-three Z monomial identity; nia multiplication
   depth does not suffice, so ring rewrites reduce it to an instance
   of [H] and linear lia closes it (same method as
   [sif_mult_comp_l]). *)
  assert (Hd : ((e*a)*(Zpos f * Zpos d) = (e*c)*(Zpos f * Zpos b))%Z).
  { assert (Hd1 : ((e*a)*(Zpos f * Zpos d))%Z
                  = ((e * Zpos f) * (a * Zpos d))%Z) by ring.
    assert (Hd2 : ((e*c)*(Zpos f * Zpos b))%Z
                  = ((e * Zpos f) * (c * Zpos b))%Z) by ring.
    rewrite Hd1, Hd2, H. reflexivity. }
  lia.
Qed.

Lemma sif_plus_comp : forall a b c d : Q,
  a == c -> b == d -> QeqT (a + b)%Q (c + d)%Q.
Proof.
  intros a b c d H1 H2. apply qeq_imp_qeqT.
  destruct a as [a1 a2]. destruct b as [b1 b2].
  destruct c as [c1 c2]. destruct d as [d1 d2].
  unfold Qeq in H1, H2. unfold Qeq.
  cbn [Qnum Qden Qplus Qmult] in *.
  rewrite (Pos2Z.inj_mul a2 b2), (Pos2Z.inj_mul c2 d2).
  (* The goal is a two-product Z identity (expansion of Q addition);
   linear lia has no witness, so ring reshaping aligns the products
   into the [H1]/[H2] shapes and substitution finishes (same method
   as [sif_mult_comp_l]). *)
  assert (Hd : ((a1*Zpos b2 + b1*Zpos a2) * (Zpos c2 * Zpos d2)
                = (c1*Zpos d2 + d1*Zpos c2) * (Zpos a2 * Zpos b2))%Z).
  { assert (Hd1 : ((a1*Zpos b2 + b1*Zpos a2) * (Zpos c2 * Zpos d2))%Z
                  = ((a1 * Zpos c2) * (Zpos b2 * Zpos d2)
                     + (b1 * Zpos d2) * (Zpos a2 * Zpos c2))%Z) by ring.
    assert (Hd2 : ((c1*Zpos d2 + d1*Zpos c2) * (Zpos a2 * Zpos b2))%Z
                  = ((c1 * Zpos a2) * (Zpos b2 * Zpos d2)
                     + (d1 * Zpos b2) * (Zpos a2 * Zpos c2))%Z) by ring.
    rewrite Hd1, Hd2, H1, H2. reflexivity. }
  exact Hd.
Qed.

Lemma sif_mult_opp_r : forall x y : Q, QeqT (x * (- y))%Q ((- (x * y))%Q).
Proof.
  intros x y. apply qeq_imp_qeqT.
  destruct x as [a b]. destruct y as [c d].
  unfold Qopp, Qmult, Qeq. cbn [Qnum Qden Qmult].
  ring.
Qed.

Lemma sif_opp_comp : forall x y : Q, x == y -> QeqT (- x)%Q (- y)%Q.
Proof.
  intros x y H. apply qeq_imp_qeqT.
  destruct x as [a b]. destruct y as [c d].
  unfold Qeq in H. unfold Qopp, Qeq.
  cbn [Qnum Qden Qmult Pos.mul] in *.
  nia.
Qed.

Lemma sif_eq_id : forall (b1 b2 : bool), b1 = b2 -> Id b1 b2.
Proof. intros b1 b2 H. rewrite H. apply id_refl. Qed.

Lemma sif_qltt : forall x y : Q, Qlt x y -> QltT x y.
Proof.
  intros x y H. unfold QltT. unfold Qlt_bool.
  pose proof (proj1 (Qlt_alt x y) H) as Hc.
  rewrite Hc. apply id_refl.
Qed.

Lemma sif_qlt_one_comp_r : forall x y : Q, x == y -> Qlt 1%Q x -> QltT 1%Q y.
Proof.
  intros x y H Hlt. apply Qlt_to_QltT.
  destruct x as [a b]. destruct y as [c d].
  unfold Qlt, Qeq in *. cbn [Qnum Qden] in *.
  nia.
Qed.

(* ============================================================ *)
(* Section 1. Integer skeleton: [Zc] sampling, numerator, product bridge *)
(* ============================================================ *)

Fixpoint sif_Zc (n : nat) : Z :=
  match n with
  | O => 1%Z
  | Datatypes.S m => Z.of_nat (Datatypes.S m) * sif_Zc m + 1
  end.

Lemma sif_qfact_Z : forall n : nat,
  QeqT (q_fact n) ((Z.of_nat (fact n)) # 1)%Q.
Proof.
  induction n as [| m IH].
  - cbn [q_fact fact]. apply qeq_imp_qeqT.
    first [reflexivity | lia | ring].
  - cbn [q_fact fact]. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ IH).
    rewrite (Nat2Z.inj_mul (Datatypes.S m) (fact m)).
    unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
    first [lia | ring | nia | reflexivity].
Qed.

(* Multiplication-by-factorial normalization bridge
   (right-multiplication form, denominator 1, no division semantics):
   [(n! # 1) * exp_series n 1 == (Zc_n # 1)]. *)
Lemma sif_Zc_bridge : forall n : nat,
  QeqT (((Z.of_nat (fact n)) # 1)%Q * exp_series n 1%Q)
       (((sif_Zc n) # 1)%Q).
Proof.
  induction n as [| m IH].
  - cbn [exp_series q_pow fact]. cbn [Qmult Pos.mul].
    apply qeq_imp_qeqT. first [reflexivity | lia | ring].
  - cbn [exp_series q_pow]. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (bno_q_pow_one m)).
    cbn [fact].
    rewrite Qmult_plus_distr_r.
    (* Under the restricted cbn the second addend has the shape
   [(N # 1) * (1 * 1 / q_fact)], with no Qopp available for
   [sif_mult_opp_r]; the two products are commuted and
   [1 * 1 == 1] is normalized before the [H2]/[H1] chain applies. *)
    rewrite (Qmult_comm (Z.of_nat (Datatypes.S m * fact m) # 1)
                        (exp_series m 1)).
    rewrite (Qmult_comm (Z.of_nat (Datatypes.S m * fact m) # 1)
                        (1 * 1 / q_fact (Datatypes.S m))).
    cbn [Qmult sif_Zc].
    assert (H2 : (1%Q / q_fact (Datatypes.S m))%Q
                 * ((Z.of_nat (Datatypes.S m * fact m)) # 1)%Q
                 == 1%Q).
    { apply (Qeq_trans _ ((1%Q / q_fact (Datatypes.S m))%Q
                          * q_fact (Datatypes.S m)%Q)%Q).
      - apply qeqT_imp_qeq. apply sif_mult_comp_r.
        exact (Qeq_sym _ _ (qeqT_imp_qeq _ _ (sif_qfact_Z (Datatypes.S m)))).
      - rewrite Qmult_comm. apply qeqT_imp_qeq. apply bno_mul_div_self.
        intro Hc. apply (Qlt_not_eq 0%Q _ (QltT_to_Qlt 0%Q _ (q_fact_pos (Datatypes.S m)))).
        apply Qeq_sym. exact Hc. }
    assert (H1 : exp_series m 1%Q
                 * ((Z.of_nat (Datatypes.S m * fact m)) # 1)%Q
                 == ((Z.of_nat (Datatypes.S m) * sif_Zc m) # 1)%Q).
    { apply (Qeq_trans _ (exp_series m 1%Q
                  * (((Z.of_nat (Datatypes.S m)) # 1)
                     * ((Z.of_nat (fact m)) # 1))%Q)%Q).
      - apply qeqT_imp_qeq. apply sif_mult_comp_r.
        unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
        rewrite (Nat2Z.inj_mul (Datatypes.S m) (fact m)).
        first [lia | ring | nia | reflexivity].
      - apply (Qeq_trans _ (((Z.of_nat (Datatypes.S m)) # 1)
                            * (exp_series m 1%Q
                               * ((Z.of_nat (fact m)) # 1))%Q)%Q).
        + ring.
        + apply (Qeq_trans _ (((Z.of_nat (Datatypes.S m)) # 1)
                              * ((sif_Zc m) # 1))%Q).
          * apply qeqT_imp_qeq. apply sif_mult_comp_r.
            apply (Qeq_trans _ (((Z.of_nat (fact m)) # 1)
                                * exp_series m 1%Q)%Q).
            -- apply Qmult_comm.
            -- exact (qeqT_imp_qeq _ _ IH).
          * unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
            first [lia | ring | nia | reflexivity]. }
    rewrite H2. rewrite H1.
    unfold Qeq. cbn [Qnum Qden Qplus Qmult Pos.mul].
    first [lia | ring | nia | reflexivity].
Qed.

(* Numerator function: [d_n := Qnum q * n! - Zc_n * b] with
   [b := Z.pos (Qden q)]. *)
Definition sif_d (q : Q) (n : nat) : Z :=
  Qnum q * Z.of_nat (fact n) - sif_Zc n * Z.pos (Qden q).

Lemma sif_d_succ : forall (q : Q) (n : nat),
  Id (sif_d q (Datatypes.S n))
     (Z.of_nat (Datatypes.S n) * sif_d q n - Z.pos (Qden q))%Z.
Proof.
  intros q n.
  assert (H : sif_d q (Datatypes.S n) =
              (Z.of_nat (Datatypes.S n) * sif_d q n - Z.pos (Qden q))%Z).
  { unfold sif_d. cbn [sif_Zc fact].
    rewrite (Nat2Z.inj_mul (Datatypes.S n) (fact n)).
    ring. }
  rewrite H. apply id_refl.
Qed.

(* Product bridge: [n! * (q - s_n) == (d_n # b)]. *)
Lemma sif_frac_prod : forall (q : Q) (n : nat),
  QeqT ((q_fact n * (q - exp_series n 1)%Q)%Q)
       (((sif_d q n) # (Qden q))%Q).
Proof.
  intros q n. apply qeq_imp_qeqT.
  apply (Qeq_trans _ (((Z.of_nat (fact n)) # 1)
                      * (q - exp_series n 1)%Q)%Q).
  - apply qeqT_imp_qeq. apply sif_mult_comp_l.
    exact (qeqT_imp_qeq _ _ (sif_qfact_Z n)).
  - apply (Qeq_trans _ (((Z.of_nat (fact n)) # 1) * q%Q
                        + (- (((Z.of_nat (fact n)) # 1)
                              * exp_series n 1%Q))%Q)%Q).
    + unfold Qminus. rewrite Qmult_plus_distr_r.
      rewrite (qeqT_imp_qeq _ _
                 (sif_mult_opp_r ((Z.of_nat (fact n)) # 1) (exp_series n 1))).
      reflexivity.
    + apply (Qeq_trans _ ((Qmake (Z.of_nat (fact n) * Qnum q) (Qden q)
                           - ((sif_Zc n) # 1))%Q)).
      * apply qeqT_imp_qeq. apply sif_plus_comp.
        -- apply (Qeq_trans _
                    ((Qmake (Z.of_nat (fact n) * Qnum q) (Qden q))%Q)).
           ++ apply qeqT_imp_qeq. apply sif_mult_comp_r. symmetry.
              exact (qeqT_imp_qeq _ _ (sif_Qmake_eta q)).
           ++ unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
              first [lia | ring | nia | reflexivity].
        -- apply qeqT_imp_qeq. apply sif_opp_comp.
           exact (qeqT_imp_qeq _ _ (sif_Zc_bridge n)).
      * destruct q as [a b]. unfold sif_d in *. unfold Qminus, Qeq.
        cbn [Qnum Qden Qplus Qopp Qmult Pos.mul] in *.
        rewrite (Pos2Z.inj_mul b 1).
        first [lia | ring | nia | reflexivity].
Qed.

Lemma sif_abs_frac : forall (q : Q) (n : nat),
  QeqT (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))
       (((Z.abs (sif_d q n)) # (Qden q))%Q).
Proof.
  intros q n. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sif_frac_prod q n)). cbn [Qabs]. reflexivity.
Qed.

Lemma sif_hit_of_dd : forall (q : Q) (n : nat),
  (Z.pos (Qden q) < Z.abs (sif_d q n))%Z ->
  QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q)).
Proof.
  intros q n Hesc.
  apply (sif_qlt_one_comp_r
          ((Z.abs (sif_d q n)) # (Qden q))%Q
          (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))).
  - exact (Qeq_sym _ _ (qeqT_imp_qeq _ _ (sif_abs_frac q n))).
  - unfold Qlt. cbn [Qnum Qden Qmult]. lia.
Qed.

(* Two-step zero escape: [d_k = 0] implies
   [|d_(k+2)| = (k+3) * b > b]. *)
Lemma sif_zero_escape : forall (q : Q) (k : nat),
  sif_d q k = 0%Z ->
  Id (Z.ltb (Z.pos (Qden q))
        (Z.abs (sif_d q (Datatypes.S (Datatypes.S k))))) true.
Proof.
  intros q k H0.
  assert (Hbq : (0 < Z.pos (Qden q))%Z).
  { apply (proj1 (Z.ltb_lt 0%Z (Z.pos (Qden q)))).
    exact (match sif_posZ (Qden q) in (Id _ y)
           return (Z.ltb 0%Z (Z.pos (Qden q)) = y)
           with id_refl => eq_refl end). }
  assert (H1 : sif_d q (Datatypes.S k) = (- Z.pos (Qden q))%Z)
    by (rewrite (match sif_d_succ q k in (Id _ y)
                 return (sif_d q (Datatypes.S k) = y)
                 with id_refl => eq_refl end), H0; lia).
  assert (H2 : sif_d q (Datatypes.S (Datatypes.S k))
               = (- (Z.of_nat k + 3) * Z.pos (Qden q))%Z)
    by (rewrite (match sif_d_succ q (Datatypes.S k) in (Id _ y)
                 return (sif_d q (Datatypes.S (Datatypes.S k)) = y)
                 with id_refl => eq_refl end), H1; nia).
  assert (Hssk : (sif_d q (Datatypes.S (Datatypes.S k)) <= 0)%Z)
    by (rewrite H2; nia).
  assert (Hltb : Z.ltb (Z.pos (Qden q))
                       (Z.abs (sif_d q (Datatypes.S (Datatypes.S k))))
                 = true).
  { apply (proj2 (Z.ltb_lt _ _)). rewrite (Z.abs_neq _ Hssk). nia. }
  rewrite Hltb. apply id_refl.
Qed.

(* ============================================================ *)
(* Section 2. Window lemma and bounded enumeration *)
(* ============================================================ *)

Lemma sif_window : forall (q : Q), (0%Z < Z.pos (Qden q))%Z ->
  (forall k : nat, (k <= Z.to_nat (2 * Z.pos (Qden q) + 1))%nat ->
     sif_d q k <> 0%Z /\ (sif_d q k <= Z.pos (Qden q) /\ - Z.pos (Qden q) <= sif_d q k))%Z -> False.
Proof.
  intros q Hb Hall.
  assert (Hsucc : forall n : nat,
    sif_d q (Datatypes.S n) =
    (Z.of_nat (Datatypes.S n) * sif_d q n - Z.pos (Qden q))%Z)
    by (intro n; rewrite (match sif_d_succ q n in (Id _ y)
                         return (sif_d q (Datatypes.S n) = y)
                         with id_refl => eq_refl end); reflexivity).
  assert (Hpos : forall k : nat, (k < Z.to_nat (2 * Z.pos (Qden q) + 1))%nat ->
                 (0 < sif_d q k)%Z).
  { intros k HkN.
    destruct (Z_le_gt_dec 0 (sif_d q k)) as [Hle | Hgt].
    - destruct (Z.eq_dec (sif_d q k) 0) as [Heq | Hne].
      + exfalso. destruct (Hall k (Nat.lt_le_incl _ _ HkN)) as [Hne2 _].
        congruence.
      + lia.
    - exfalso.
      assert (Hge1 : (1 <= Z.of_nat (Datatypes.S k))%Z) by lia.
      assert (Hprod : (Z.of_nat (Datatypes.S k) * sif_d q k <= -1)%Z) by nia.
      assert (Hdn : (sif_d q (Datatypes.S k) < - Z.pos (Qden q))%Z)
        by (rewrite Hsucc; lia).
      destruct (Hall (Datatypes.S k) ltac:(lia)) as [_ [Hub Hlow]].
      lia. }
  assert (HN1 : (1 <= Z.to_nat (2 * Z.pos (Qden q) + 1))%nat) by lia.
  assert (HzN : (Z.of_nat (Z.to_nat (2 * Z.pos (Qden q) + 1)) = 2 * Z.pos (Qden q) + 1)%Z) by lia.
  assert (Hwin : (Z.of_nat (Z.to_nat (2 * Z.pos (Qden q) + 1))
                  * sif_d q (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 1))) <= 2 * Z.pos (Qden q))%Z).
  { assert (HSN : (Datatypes.S (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 1)))
                   = Z.to_nat (2 * Z.pos (Qden q) + 1))%nat) by lia.
    pose proof (Hsucc (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 1)))) as HH.
    rewrite HSN in HH.
    destruct (Hall (Z.to_nat (2 * Z.pos (Qden q) + 1)) (Nat.le_refl _)) as [_ [Hub _]].
    lia. }
  assert (Hpd : (0 < sif_d q (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 1))))%Z)
    by (apply Hpos; lia).
  nia.
Qed.

Lemma sif_dec_pt : forall (q : Q) (n : nat),
  (QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q)))
  + (QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))
      -> Empty_set).
Proof.
  intros q n. unfold QltT.
  destruct (Qlt_bool 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))) eqn:E.
  - left. apply id_refl.
  - right. intros Hc. inversion Hc.
Qed.

Fixpoint sif_enum (q : Q) (k : nat) :
  (sigT (fun n : nat => prod (n <= k)%nat
            (QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q)))))
  + (forall n : nat, NatLe n k ->
       QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))
       -> Empty_set) :=
  match k with
  | O =>
    match sif_dec_pt q O with
    | inl c => inl (existT _ O (pair (Nat.le_refl O) c))
    | inr c =>
        inr (fun (n : nat) (Hn0 : NatLe n 0) (Hcc : QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))) =>
          match Nat.eq_dec n O with
          | left E =>
              c (eq_rect n
                   (fun n1 : nat =>
                      QltT 1%Q
                        (Qabs ((q_fact n1 * (q - exp_series n1 1)%Q)%Q)))
                   Hcc O E)
          | right E => False_rect _ ltac:(pose proof (NatLe_drop _ _ Hn0); lia)
          end)
    end
  | Datatypes.S m =>
    match sif_enum q m with
    | inl f =>
        inl (match f with
             | existT _ n0 pf =>
                 match pf with
                 | pair Hn0 Hc0 =>
                     existT _ n0 (pair (le_S _ _ Hn0) Hc0)
                 end
             end)
    | inr g =>
      match sif_dec_pt q (Datatypes.S m) with
      | inl c => inl (existT _ (Datatypes.S m)
                          (pair (Nat.le_refl (Datatypes.S m)) c))
      | inr c =>
        inr (fun (n : nat) (Hn : NatLe n (Datatypes.S m)) (Hcc : QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))) =>
          match Nat.eq_dec n (Datatypes.S m) with
          | right E => g n ltac:(apply NatLe_lift; pose proof (NatLe_drop _ _ Hn); lia) Hcc
          | left E =>
              c (eq_rect n
                   (fun n1 : nat =>
                      QltT 1%Q
                        (Qabs ((q_fact n1 * (q - exp_series n1 1)%Q)%Q)))
                   Hcc (Datatypes.S m) E)
          end)
      end
    end
  end.

(* ============================================================ *)
(* Section 3. Escape statements in the target shape *)
(* ============================================================ *)

Definition sif_sum_inv_fact_escape : Type :=
  forall q : Q,
    sigT (fun n : nat => Qlt 1 (Qabs (q_fact n * (q - exp_series n 1))%Q)).

Theorem sif_escape : forall q : Q,
  sigT (fun n : nat =>
    Qlt 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))).
Proof.
  intro q.
  assert (Hbq : (0 < Z.pos (Qden q))%Z).
  { apply (proj1 (Z.ltb_lt 0%Z (Z.pos (Qden q)))).
    exact (match sif_posZ (Qden q) in (Id _ y)
           return (Z.ltb 0%Z (Z.pos (Qden q)) = y)
           with id_refl => eq_refl end). }
  destruct (sif_enum q (Z.to_nat (2 * Z.pos (Qden q) + 3)))
    as [[n [Hn Hc]] | Hno].
  - exists n. apply QltT_to_Qlt. exact Hc.
  - exfalso. apply (sif_window q Hbq).
    intros k HkN.
    assert (HkN3 : NatLe k (Z.to_nat (2 * Z.pos (Qden q) + 3)))
      by (apply NatLe_lift; lia).
    destruct (Qlt_bool 1%Q (Qabs ((q_fact k * (q - exp_series k 1)%Q)%Q)))
      eqn:EQ.
    + exfalso. destruct (Hno k HkN3 (sif_eq_id _ _ EQ)).
    + (* [EQ : Qlt_bool 1 (Qabs ...) = false] means no escape at rank [k],
   hence [|d_k| <= b]. *)
      assert (Hnb : ~ (1%Q < Qabs ((q_fact k * (q - exp_series k 1)%Q)%Q))).
      { intro Hlt.
        destruct (Hno k HkN3 (sif_qltt _ _ Hlt)). }
      pose proof (sif_abs_frac q k) as HF.
      assert (Habsb : (Z.abs (sif_d q k) <= Z.pos (Qden q))%Z).
      { destruct (Z_le_gt_dec (Z.abs (sif_d q k)) (Z.pos (Qden q)))
          as [Hle | Hgt].
        - exact Hle.
        - exfalso. apply Hnb.
          apply (QltT_to_Qlt 1%Q (Qabs ((q_fact k * (q - exp_series k 1)%Q)%Q))).
          apply (sif_qlt_one_comp_r
                   ((Z.abs (sif_d q k)) # (Qden q))%Q
                   (Qabs ((q_fact k * (q - exp_series k 1)%Q)%Q))).
          ++ exact (Qeq_sym _ _ (qeqT_imp_qeq _ _ HF)).
          ++ unfold Qlt. cbn [Qnum Qden Qmult]. lia. }
      assert (Hssk3 : NatLe (Datatypes.S (Datatypes.S k))
                            (Z.to_nat (2 * Z.pos (Qden q) + 3)))
        by (apply NatLe_lift; lia).
      destruct (Z.eq_dec (sif_d q k) 0) as [Hz | Hnz].
      { destruct (Hno (Datatypes.S (Datatypes.S k)) Hssk3
            ltac:(apply sif_hit_of_dd;
                  apply (proj1 (Z.ltb_lt (Z.pos (Qden q))
                               (Z.abs (sif_d q (Datatypes.S (Datatypes.S k))))));
                  exact (match sif_zero_escape q k Hz in (Id _ y)
                         return (Z.ltb (Z.pos (Qden q))
                                   (Z.abs (sif_d q (Datatypes.S (Datatypes.S k))))) = y
                         with id_refl => eq_refl end))). }
      split; [ exact Hnz | split; lia ].
Qed.

Corollary sif_escape_closed : sif_sum_inv_fact_escape.
Proof. exact sif_escape. Qed.

(* ============================================================ *)
(* Section 4. Extraction check and assumption audit *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction sif_escape sif_escape_closed sif_enum sif_dec_pt
  sif_window sif_abs_frac sif_frac_prod sif_hit_of_dd sif_d sif_d_succ
  sif_zero_escape sif_Zc sif_Zc_bridge sif_qfact_Z.

Print Assumptions sif_escape.
Print Assumptions sif_escape_closed.
