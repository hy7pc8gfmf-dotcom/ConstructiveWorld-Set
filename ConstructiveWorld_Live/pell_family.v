(* ConstructiveWorld-Set — convergent-family supply modules on the Q layer. *)

(** * pell_family: the general-D Pell convergent family for D = m^2 + 1.

    Mission.  For each m with 1 <= m, the convergents X_n/Y_n of sqrt(m^2+1)
      carried by the dual threads [pellpair]/[qelpair] (X_{n+2} = 2m*X_{n+1}
      + X_n with X_0 = 1, X_1 = m, and likewise Y) and the streams
      [pellx]/[pelly]; the norm layer [pell_norm] (the general-D Cassini
      identity X_n^2 - (m^2+1) Y_n^2 = powneg1 n), [pell_norm_abs1] (the
      family gap has absolute value exactly 1), [pell_det] and
      [m1_nonsquare]; the assembly layer [pell_member] = X_{j+1}/Y_{j+1}
      with [pell_family_sharp] (adjacent family distance = 1/(Y_{j+1}
      Y_{j+2}), equality attained), [pell_family_sep] (every a/b with
      a * Y_{j+1} - X_{j+1} b <> 0 stays at distance >= 1/(b * Y_{j+1}))
      and the Q-square sharpness [pell_q_square_sharp] with
      [pell_q_square_gap_instance] (|member^2 - D| = 1/Y^2, attained).

    Dependencies.  [S01_BaseRing] [S02_CauchyComplete] [fib_machine]
      [fib_qdomain]; Stdlib [ZArith] [Arith] [Bool] [Lia] [QArith] [Qabs].

    References.  ConstructiveWorld-Main [fib_family_sep] and
      [fib_family_sharp] (statement names carried over verbatim; the two
      theorems are the family-side analogues of the FIB pair), and the
      FIB3 separation certificate [q_square_gap], attained with equality.

    Constructivity.  All named statements are Set-carried ([QeqT], [QleT'],
      [Id], [And], [ZLeT] = [Id (Z.leb a b) true]); in-body elimination
      goes through [Id_eq], [eq_Id], [ZLeT_drop], [ZLeT_lift]; [coqchk]
      reports Axioms: none.
    Build.  [rocq c -native-compiler no -q -Q . "" pell_family.v]. *)

Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
Require Import S01_BaseRing.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* Preliminaries.  Equality elimination for [Id] and the Set-layer
   order kit on Z: [ZLeT a b] is [Id (Z.leb a b) true] with the transfer
   lemmas [ZLeT_drop] / [ZLeT_lift].  Note: after importing [S01_BaseRing]
   the short name [S] denotes the constant [S01_BaseRing.S], so every
   nat successor in this file is written [Datatypes.S]. *)
(* ============================================================ *)
Definition Id_eq {A : Set} (x y : A) (H : Id x y) : x = y.
Proof. destruct H. apply eq_refl. Defined.

Definition eq_Id {A : Set} (x y : A) (H : x = y) : Id x y.
Proof. destruct H. apply id_refl. Defined.

Definition ZLeT (a b : Z) : Set := Id (Z.leb a b) true.

Lemma ZLeT_drop : forall a b : Z, ZLeT a b -> (a <= b)%Z.
Proof. intros a b H. apply Z.leb_le. exact (Id_eq _ _ H). Defined.

Lemma ZLeT_lift : forall a b : Z, (a <= b)%Z -> ZLeT a b.
Proof. intros a b H. exact (eq_Id _ _ (proj2 (Z.leb_le a b) H)). Defined.

(* ============================================================ *)
(* Section C. Carrier layer: the dual thread [pellpair]/[qelpair], the streams
   [pellx]/[pelly], recursion lemmas *)
(* ============================================================ *)

(* X-stream: (X_{n+1}, X_n) with X_0 = 1, X_1 = m and X_{n+2} = 2m*X_{n+1} + X_n. *)
Fixpoint pellpair (m : Z) (n : nat) : Z * Z :=
  match n with
  | O => (m, 1%Z)
  | Datatypes.S k => match pellpair m k with pair x y => ((2 * m * x + y)%Z, x) end
  end.

(* Y-stream: (Y_{n+1}, Y_n) with Y_0 = 0, Y_1 = 1, same recurrence coefficients. *)
Fixpoint qelpair (m : Z) (n : nat) : Z * Z :=
  match n with
  | O => (1%Z, 0%Z)
  | Datatypes.S k => match qelpair m k with pair x y => ((2 * m * x + y)%Z, x) end
  end.

Definition pellx (m : Z) (n : nat) : Z := snd (pellpair m n).
Definition pelly (m : Z) (n : nat) : Z := snd (qelpair m n).

Lemma pellx_0 : forall m : Z, Id (pellx m 0) 1%Z.
Proof. intros m. apply id_refl. Qed.

Lemma pellx_1 : forall m : Z, Id (pellx m 1) m%Z.
Proof. intros m. apply id_refl. Qed.

Lemma pelly_0 : forall m : Z, Id (pelly m 0) 0%Z.
Proof. intros m. apply id_refl. Qed.

Lemma pelly_1 : forall m : Z, Id (pelly m 1) 1%Z.
Proof. intros m. apply id_refl. Qed.

Lemma pellpair_unfold : forall (m : Z) (n : nat),
  Id (pellpair m (Datatypes.S n))
     ((2 * m * fst (pellpair m n) + snd (pellpair m n))%Z, fst (pellpair m n)).
Proof.
  intros m n. cbn [pellpair]. destruct (pellpair m n) as [a b]. apply id_refl.
Qed.

Lemma qelpair_unfold : forall (m : Z) (n : nat),
  Id (qelpair m (Datatypes.S n))
     ((2 * m * fst (qelpair m n) + snd (qelpair m n))%Z, fst (qelpair m n)).
Proof.
  intros m n. cbn [qelpair]. destruct (qelpair m n) as [a b]. apply id_refl.
Qed.

Lemma pellx_rec : forall (m : Z) (n : nat),
  Id (pellx m (Datatypes.S (Datatypes.S n))) ((2 * m * pellx m (Datatypes.S n) + pellx m n)%Z).
Proof.
  intros m n. unfold pellx. cbn [pellpair]. destruct (pellpair m n) as [a b].
  apply id_refl.
Qed.

Lemma pelly_rec : forall (m : Z) (n : nat),
  Id (pelly m (Datatypes.S (Datatypes.S n))) ((2 * m * pelly m (Datatypes.S n) + pelly m n)%Z).
Proof.
  intros m n. unfold pelly. cbn [qelpair]. destruct (qelpair m n) as [a b].
  apply id_refl.
Qed.

(* Positivity layer: for 1 <= m every X_n and Y_{n+1} is at least 1 (this
   guards the Q denominator slot and the Zpos bridge; in-body conclusions on
   Z carry <= through [ZLeT] and conjunctions through [And], the Set product). *)
Lemma pellx_ge1_aux : forall (m : Z), (1 <= m)%Z -> forall n : nat,
  And (ZLeT 1%Z (pellx m n)) (ZLeT 1%Z (pellx m (Datatypes.S n))).
Proof.
  intros m Hm. induction n as [|n IH].
  - split.
    + apply ZLeT_lift. unfold pellx. cbn [pellpair fst snd]. lia.
    + apply ZLeT_lift. unfold pellx. cbn [pellpair fst snd]. exact Hm.
  - destruct IH as [IH1 IH2]. split.
    + exact IH2.
    + apply ZLeT_lift.
      pose proof (Id_eq _ _ (pellx_rec m n)) as Hrec. rewrite Hrec.
      pose proof (ZLeT_drop _ _ IH1). pose proof (ZLeT_drop _ _ IH2). nia.
Qed.

Lemma pelly_ge1_aux : forall (m : Z), (1 <= m)%Z -> forall n : nat,
  And (ZLeT 1%Z (pelly m (Datatypes.S n))) (ZLeT 1%Z (pelly m (Datatypes.S (Datatypes.S n)))).
Proof.
  intros m Hm. induction n as [|n IH].
  - split.
    + apply ZLeT_lift. unfold pelly. cbn [qelpair fst snd]. lia.
    + apply ZLeT_lift.
      pose proof (Id_eq _ _ (pelly_rec m 0)) as Hrec. rewrite Hrec.
      unfold pelly. cbn [qelpair fst snd]. nia.
  - destruct IH as [IH1 IH2]. split.
    + exact IH2.
    + apply ZLeT_lift.
      pose proof (Id_eq _ _ (pelly_rec m (Datatypes.S n))) as Hrec. rewrite Hrec.
      pose proof (ZLeT_drop _ _ IH1). pose proof (ZLeT_drop _ _ IH2). nia.
Qed.

Lemma pellx_ge1 : forall (m : Z), (1 <= m)%Z -> forall n : nat, ZLeT 1%Z (pellx m n).
Proof.
  intros m Hm n. destruct n as [|n].
  - apply (fst (pellx_ge1_aux m Hm 0)).
  - apply (snd (pellx_ge1_aux m Hm n)).
Qed.

Lemma pelly_ge1 : forall (m : Z), (1 <= m)%Z -> forall n : nat, ZLeT 1%Z (pelly m (Datatypes.S n)).
Proof.
  intros m Hm n. apply (fst (pelly_ge1_aux m Hm n)).
Qed.

(* ============================================================ *)
(* Section N. Norm layer: [pell_norm] (general-D Cassini), [pell_norm_abs1],
   [pell_det], [m1_nonsquare] *)
(* ============================================================ *)

Lemma powneg1_2 : forall n : nat, Id (powneg1 (Datatypes.S (Datatypes.S n))) (powneg1 n).
Proof. intro n. apply eq_Id. rewrite !powneg1_S. lia. Qed.

(* Three-invariant induction: the norm S_n, the shifted norm S_{n+1} and the
   cross term C_n = X_n X_{n+1} - D Y_n Y_{n+1} obey the recurrences
   S_{n+2} = 4m^2 S_{n+1} + 4m C_n + S_n and C_{n+1} = 2m S_{n+1} + C_n,
   using only the same three terms in the window. *)
Lemma pell_norm_tri : forall (m : Z), (1 <= m)%Z -> forall n : nat,
  And (Id ((pellx m n * pellx m n - (m*m+1) * (pelly m n * pelly m n))%Z) (powneg1 n))
      (And (Id ((pellx m (Datatypes.S n) * pellx m (Datatypes.S n) - (m*m+1) * (pelly m (Datatypes.S n) * pelly m (Datatypes.S n)))%Z) (powneg1 (Datatypes.S n)))
           (Id ((pellx m n * pellx m (Datatypes.S n) - (m*m+1) * (pelly m n * pelly m (Datatypes.S n)))%Z) ((m * powneg1 n)%Z))).
Proof.
  intros m Hm. induction n as [|n IH].
  - split; [| split].
    + apply eq_Id. unfold pellx, pelly. cbn [pellpair qelpair fst snd powneg1]. ring.
    + apply eq_Id. unfold pellx, pelly. cbn [pellpair qelpair fst snd powneg1]. ring.
    + apply eq_Id. unfold pellx, pelly. cbn [pellpair qelpair fst snd powneg1]. ring.
  - destruct IH as [IH1 [IH2 IH3]].
    pose proof (Id_eq _ _ IH1) as H1.
    pose proof (Id_eq _ _ IH2) as H2.
    pose proof (Id_eq _ _ IH3) as H3.
    split; [| split].
    + exact IH2.
    + apply eq_Id.
      pose proof (Id_eq _ _ (pellx_rec m n)) as HX.
      pose proof (Id_eq _ _ (pelly_rec m n)) as HY.
      pose proof (Id_eq _ _ (powneg1_2 n)) as HP2.
      rewrite HX, HY, HP2.
      transitivity ((4*m*m*(pellx m (Datatypes.S n) * pellx m (Datatypes.S n) - (m*m+1) * (pelly m (Datatypes.S n) * pelly m (Datatypes.S n)))
                    + 4*m*(pellx m n * pellx m (Datatypes.S n) - (m*m+1) * (pelly m n * pelly m (Datatypes.S n)))
                    + (pellx m n * pellx m n - (m*m+1) * (pelly m n * pelly m n)))%Z).
      * ring.
      * rewrite H2, H3, H1. rewrite powneg1_S. ring.
    + apply eq_Id.
      pose proof (Id_eq _ _ (pellx_rec m n)) as HX.
      pose proof (Id_eq _ _ (pelly_rec m n)) as HY.
      rewrite HX, HY.
      transitivity ((2*m*(pellx m (Datatypes.S n) * pellx m (Datatypes.S n) - (m*m+1) * (pelly m (Datatypes.S n) * pelly m (Datatypes.S n)))
                    + (pellx m n * pellx m (Datatypes.S n) - (m*m+1) * (pelly m n * pelly m (Datatypes.S n))))%Z).
      * ring.
      * rewrite H2, H3. rewrite powneg1_S. ring.
Qed.

(* Main statement: the general D = m^2 + 1 Cassini (Pell norm) identity; the family gap alternates between exactly 1 and -1. *)
Theorem pell_norm : forall (m : Z) (n : nat), (1 <= m)%Z ->
  Id ((pellx m n * pellx m n - (m*m+1) * (pelly m n * pelly m n))%Z) (powneg1 n).
Proof.
  intros m n Hm. exact (fst (pell_norm_tri m Hm n)).
Qed.

(* The family gap is exactly 1: the general lower bound of absolute value >= 1 is attained with equality on the family. *)
Theorem pell_norm_abs1 : forall (m : Z) (n : nat), (1 <= m)%Z ->
  Id (Z.abs ((pellx m n * pellx m n - (m*m+1) * (pelly m n * pelly m n))%Z)) 1%Z.
Proof.
  intros m n Hm. apply eq_Id.
  rewrite (Id_eq _ _ (pell_norm m n Hm)). exact (Id_eq _ _ (zabs_powneg1 n)).
Qed.

(* Determinant identity: X_{n+1} Y_{n+2} - X_{n+2} Y_{n+1} = powneg1 (S n), by single-step induction. *)
Lemma pell_det : forall (m : Z) (n : nat),
  Id ((pellx m (Datatypes.S n) * pelly m (Datatypes.S (Datatypes.S n)) - pellx m (Datatypes.S (Datatypes.S n)) * pelly m (Datatypes.S n))%Z)
     (powneg1 (Datatypes.S n)).
Proof.
  intro m. induction n as [|n IH].
  - apply eq_Id.
    pose proof (Id_eq _ _ (pellx_1 m)) as HX1.
    pose proof (Id_eq _ _ (pelly_1 m)) as HY1.
    pose proof (Id_eq _ _ (pellx_rec m 0)) as HXr.
    pose proof (Id_eq _ _ (pelly_rec m 0)) as HYr.
    pose proof (Id_eq _ _ (pellx_0 m)) as HX0.
    pose proof (Id_eq _ _ (pelly_0 m)) as HY0.
    rewrite HX1, HY1, HXr, HYr, HX1, HX0, HY1, HY0.
    cbn [powneg1]. ring.
  - apply eq_Id.
    pose proof (Id_eq _ _ IH) as HIP.
    rewrite powneg1_S.
    transitivity ((- (pellx m (Datatypes.S n) * pelly m (Datatypes.S (Datatypes.S n)) - pellx m (Datatypes.S (Datatypes.S n)) * pelly m (Datatypes.S n)))%Z).
    + rewrite (Id_eq _ _ (pellx_rec m (Datatypes.S n))), (Id_eq _ _ (pelly_rec m (Datatypes.S n))),
        (Id_eq _ _ (pellx_rec m n)), (Id_eq _ _ (pelly_rec m n)). ring.
    + rewrite HIP. reflexivity.
Qed.

(* D = m^2 + 1 is never a perfect square (contradiction from the bound on |c|);
   supplies the non-square premise consumed by [q_square_gap] at its use sites. *)
Lemma m1_nonsquare : forall m c : Z, (1 <= m)%Z -> (m*m+1 <> c*c)%Z.
Proof.
  intros m c Hm Hc.
  pose proof (Z.abs_square c) as Habs.
  pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = m*m+1)%Z) by lia.
  assert (Hgt : (m < Z.abs c)%Z).
  { destruct (Z_lt_le_dec m (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============================================================ *)
(* Section Q. Assembly layer: the Z-to-positive bridge, [pell_member], the two
   certificate theorems, Q-square sharpness *)
(* ============================================================ *)

(* The bridge from positive Z to [positive]: at a z with 0 < z it returns a
   true positive; a non-positive input falls back to 1 by convention, and every
   use site carries the positivity premise so the bridge is sound. *)
Definition Zpos_of (z : Z) : positive :=
  match z with Zpos p => p | _ => 1%positive end.

Lemma Zpos_of_pos : forall z : Z, (0 < z)%Z -> Id (Z.pos (Zpos_of z)) z.
Proof.
  intros z Hz. destruct z as [|p|p].
  - exfalso. cbn in Hz. lia.
  - apply id_refl.
  - exfalso. cbn in Hz. pose proof (Pos2Z.is_pos p). lia.
Qed.

Definition pellxp (m : Z) (j : nat) : positive := Zpos_of (pellx m (Datatypes.S j)).
Definition pellyp (m : Z) (j : nat) : positive := Zpos_of (pelly m (Datatypes.S j)).

Lemma pellxp_pos : forall (m : Z) (j : nat), (1 <= m)%Z ->
  Id (Z.pos (pellxp m j)) (pellx m (Datatypes.S j)).
Proof.
  intros m j Hm. unfold pellxp. apply Zpos_of_pos.
  pose proof (ZLeT_drop _ _ (pellx_ge1 m Hm (Datatypes.S j))). lia.
Qed.

Lemma pellyp_pos : forall (m : Z) (j : nat), (1 <= m)%Z ->
  Id (Z.pos (pellyp m j)) (pelly m (Datatypes.S j)).
Proof.
  intros m j Hm. unfold pellyp. apply Zpos_of_pos.
  pose proof (ZLeT_drop _ _ (pelly_ge1 m Hm j)). lia.
Qed.

(* Family member: X_{j+1} / Y_{j+1}, the j-th convergent of sqrt(m^2 + 1); for m = 1 this is the sqrt 2 family. *)
Definition pell_member (m : Z) (j : nat) : Q := (Z.pos (pellxp m j) # pellyp m j)%Q.

(* Family certificate sharpness (main statement one): the distance of adjacent
   convergents equals 1/(Y_{j+1} Y_{j+2}) exactly, realized through the +/-1 of
   [pell_det] (analogue of [fib_family_sharp]). *)
Theorem pell_family_sharp : forall (m : Z) (j : nat), (1 <= m)%Z ->
  QeqT (Qabs (pell_member m j - pell_member m (Datatypes.S j)))
       (Qinv ((Z.pos (pellyp m j * pellyp m (Datatypes.S j))) # 1)).
Proof.
  intros m j Hm.
  assert (Hd : (pell_member m j - pell_member m (Datatypes.S j))%Q ==
               ((Z.pos (pellxp m j) * Z.pos (pellyp m (Datatypes.S j))
                 - Z.pos (pellxp m (Datatypes.S j)) * Z.pos (pellyp m j))
                 # (pellyp m j * pellyp m (Datatypes.S j)))%Q).
  { unfold pell_member. apply qeqT_imp_qeq. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - pose proof (Id_eq _ _ (pellxp_pos m j Hm)) as HXj.
    pose proof (Id_eq _ _ (pellxp_pos m (Datatypes.S j) Hm)) as HXSj.
    rewrite HXj, HXSj.
    assert (Hd2 : (pellx m (Datatypes.S j) * Z.pos (pellyp m (Datatypes.S j))
                   - pellx m (Datatypes.S (Datatypes.S j)) * Z.pos (pellyp m j) = powneg1 (Datatypes.S j))%Z).
    { pose proof (pell_det m j) as Hdet0.
      pose proof (Id_eq _ _ Hdet0) as Hdet.
      pose proof (Id_eq _ _ (pellyp_pos m (Datatypes.S j) Hm)) as HYSj.
      pose proof (Id_eq _ _ (pellyp_pos m j Hm)) as HYj.
      rewrite <- HYSj, <- HYj in Hdet.
      exact Hdet. }
    rewrite Hd2.
    destruct (powneg1 (Datatypes.S j)) as [|p|p] eqn:E.
    + exfalso. pose proof (Id_eq _ _ (zabs_powneg1 (Datatypes.S j))) as Hz. rewrite E in Hz. cbn in Hz. discriminate.
    + pose proof (Id_eq _ _ (zabs_powneg1 (Datatypes.S j))) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.pos 1 # pellyp m j * pellyp m (Datatypes.S j))) with (Z.pos 1 # pellyp m j * pellyp m (Datatypes.S j))%Q.
      change (Qinv (Z.pos (pellyp m j * pellyp m (Datatypes.S j)) # 1)) with (1 # pellyp m j * pellyp m (Datatypes.S j))%Q.
      apply Qeq_refl.
    + pose proof (Id_eq _ _ (zabs_powneg1 (Datatypes.S j))) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.neg 1 # pellyp m j * pellyp m (Datatypes.S j))) with (Z.pos 1 # pellyp m j * pellyp m (Datatypes.S j))%Q.
      change (Qinv (Z.pos (pellyp m j * pellyp m (Datatypes.S j)) # 1)) with (1 # pellyp m j * pellyp m (Datatypes.S j))%Q.
      apply Qeq_refl.
Qed.

(* Family separation certificate (main statement two): when a * Y_{j+1} -
   X_{j+1} b <> 0, every a/b stays at distance >= 1/(b * Y_{j+1}) from the
   family member (analogue of [fib_family_sep]; the only premises are
   a * Y_{j+1} - X_{j+1} b <> 0 and 1 <= m). *)
Theorem pell_family_sep : forall (m : Z) (j : nat) (a : Z) (b : positive), (1 <= m)%Z ->
  (a * pelly m (Datatypes.S j) - pellx m (Datatypes.S j) * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * pellyp m j)) # 1))
        (Qabs ((a # b)%Q - pell_member m j)).
Proof.
  intros m j a b Hm Hk. unfold pell_member.
  assert (Hk2 : (a * Z.pos (pellyp m j) - Z.pos (pellxp m j) * Z.pos b <> 0)%Z).
  { pose proof (Id_eq _ _ (pellyp_pos m j Hm)) as HYj.
    pose proof (Id_eq _ _ (pellxp_pos m j Hm)) as HXj.
    rewrite HYj, HXj. exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (pellyp m j) - Z.pos (pellxp m j) * Z.pos b)
                  # (b * pellyp m j))%Q)
          (Qabs ((a # b)%Q - (Z.pos (pellxp m j) # pellyp m j)%Q))
          (Qinv ((Z.pos (b * pellyp m j)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (pellxp m j) # pellyp m j)%Q))
                   (Qabs ((a * Z.pos (pellyp m j) - Z.pos (pellxp m j) * Z.pos b)
                           # (b * pellyp m j))%Q)).
    apply qeqT_imp_qeq. apply fib_qabs_congr. apply qeqT_imp_qeq. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * pellyp m j)%positive).
    exact (ZLeT_drop _ _ (zabs_ge1 _ Hk2)).
Qed.

(* Q-square sharpness (main statement three, the family-side counterpart of the
   FIB3 separation certificate): |member^2 - D| = 1/Y^2 exactly, so the 1/b^2
   lower bound of [q_square_gap] is attained on the family (independently
   recomputed over the full grid). *)
Theorem pell_q_square_sharp : forall (m : Z) (j : nat), (1 <= m)%Z ->
  QeqT (Qabs (pell_member m j * pell_member m j - ((m*m+1) # 1)%Q))
       (Qinv ((Z.pos (pellyp m j * pellyp m j)) # 1)).
Proof.
  intros m j Hm.
  assert (Hd : (pell_member m j * pell_member m j - ((m*m+1) # 1))%Q ==
               ((Z.pos (pellxp m j) * Z.pos (pellxp m j)
                 - (m*m+1) * (Z.pos (pellyp m j) * Z.pos (pellyp m j)))
                 # (pellyp m j * pellyp m j))%Q).
  { unfold pell_member. apply qeqT_imp_qeq. apply (q_square_cross (Z.pos (pellxp m j)) (m*m+1) (pellyp m j)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - pose proof (Id_eq _ _ (pellxp_pos m j Hm)) as HXj.
    rewrite HXj.
    assert (Hn2 : (pellx m (Datatypes.S j) * pellx m (Datatypes.S j)
                   - (m*m+1) * (Z.pos (pellyp m j) * Z.pos (pellyp m j)) = powneg1 (Datatypes.S j))%Z).
    { pose proof (Id_eq _ _ (pell_norm m (Datatypes.S j) Hm)) as Hn.
      pose proof (Id_eq _ _ (pellyp_pos m j Hm)) as HYj.
      rewrite <- HYj in Hn. exact Hn. }
    rewrite Hn2.
    destruct (powneg1 (Datatypes.S j)) as [|p|p] eqn:E.
    + exfalso. pose proof (Id_eq _ _ (zabs_powneg1 (Datatypes.S j))) as Hz. rewrite E in Hz. cbn in Hz. discriminate.
    + pose proof (Id_eq _ _ (zabs_powneg1 (Datatypes.S j))) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.pos 1 # pellyp m j * pellyp m j)) with (Z.pos 1 # pellyp m j * pellyp m j)%Q.
      change (Qinv (Z.pos (pellyp m j * pellyp m j) # 1)) with (1 # pellyp m j * pellyp m j)%Q.
      apply Qeq_refl.
    + pose proof (Id_eq _ _ (zabs_powneg1 (Datatypes.S j))) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.neg 1 # pellyp m j * pellyp m j)) with (Z.pos 1 # pellyp m j * pellyp m j)%Q.
      change (Qinv (Z.pos (pellyp m j * pellyp m j) # 1)) with (1 # pellyp m j * pellyp m j)%Q.
      apply Qeq_refl.
Qed.

(* Instance invocation of [q_square_gap] (the FIB3 main statement instantiated
   on the family): combined with sharpness, the lower bound is exactly attained. *)
Lemma pell_q_square_gap_instance : forall (m : Z) (j : nat), (1 <= m)%Z ->
  QleT' (Qinv ((Z.pos (pellyp m j * pellyp m j)) # 1))
        (Qabs (pell_member m j * pell_member m j - ((m*m+1) # 1)%Q)).
Proof.
  intros m j Hm. unfold pell_member.
  apply (q_square_gap (m*m+1) (Z.pos (pellxp m j)) (pellyp m j)).
  - nia.
  - intro c. apply (m1_nonsquare m c Hm).
Qed.

(* ============================================================ *)
(* Section A. Audit: Print Assumptions, extraction, numerical anchors *)
(* ============================================================ *)

Print Assumptions pellx_rec.
Print Assumptions pelly_rec.
Print Assumptions pellx_ge1.
Print Assumptions pelly_ge1.
Print Assumptions pell_det.
Print Assumptions pell_norm.
Print Assumptions pell_norm_abs1.
Print Assumptions m1_nonsquare.
Print Assumptions Zpos_of_pos.
Print Assumptions pell_family_sep.
Print Assumptions pell_family_sharp.
Print Assumptions pell_q_square_sharp.
Print Assumptions pell_q_square_gap_instance.

(* Numerical anchor 1 (sqrt 2 family member): member 1 1 = X_2 / Y_2 = 3/2. *)
Lemma smoke_member_3_2 : Id (Qeq_bool (pell_member 1 1) (3 # 2)%Q) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 2 (sqrt 5 family member): member 2 1 = X_2 / Y_2 = 9/4. *)
Lemma smoke_member_9_4 : Id (Qeq_bool (pell_member 2 1) (9 # 4)%Q) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 3 (norm layer): |X_3^2 - 2 Y_3^2| = |49 - 50| = 1 (instance of [pell_norm_abs1]). *)
Lemma smoke_norm_1 : Id (Z.eqb (Z.abs ((pellx 1 3 * pellx 1 3 - 2 * (pelly 1 3 * pelly 1 3))%Z)) 1%Z) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 4 (sharpness): |3/2 - 7/5| = 1/10 = 1/(pellyp 1 1 * pellyp 1 2) (instance of [pell_family_sharp]). *)
Lemma smoke_sharp_1_10 :
  Id (Qeq_bool (Qabs (pell_member 1 1 - pell_member 1 2))
            (Qinv ((Z.pos (pellyp 1 1 * pellyp 1 2)) # 1))) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 5 (Q-square sharpness): |(3/2)^2 - 2| = 1/4 (instance of [pell_q_square_sharp]). *)
Lemma smoke_qsq_1_4 :
  Id (Qeq_bool (Qabs (pell_member 1 1 * pell_member 1 1 - (2 # 1)%Q))
            (Qinv ((Z.pos (pellyp 1 1 * pellyp 1 1)) # 1))) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 6 (Pell numbers): pellx 1 4 = 17 and pelly 1 4 = 12 (the convergent 17/12 of sqrt 2). *)
Lemma smoke_pell_17_12 :
  Id (Z.eqb (pellx 1 4) 17%Z, Z.eqb (pelly 1 4) 12%Z) (true, true).
Proof. vm_compute. apply id_refl. Qed.

Print Assumptions smoke_member_3_2.
Print Assumptions smoke_member_9_4.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_10.
Print Assumptions smoke_qsq_1_4.
Print Assumptions smoke_pell_17_12.

From Stdlib Require Import Extraction.
Separate Extraction pellpair qelpair pellx pelly Zpos_of pellxp pellyp
  pell_member pell_norm_abs1 pell_family_sep pell_family_sharp
  pell_q_square_sharp pell_q_square_gap_instance
  smoke_member_3_2 smoke_member_9_4 smoke_norm_1 smoke_sharp_1_10
  smoke_qsq_1_4 smoke_pell_17_12.
