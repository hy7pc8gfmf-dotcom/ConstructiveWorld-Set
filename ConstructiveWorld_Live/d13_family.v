(* ConstructiveWorld-Set — the D = 13 period-5 convergence subfamily. *)

(** * d13_family: the D = 13 period-5 convergence subfamily (first general
    period-class instance).

    Mission.  [sqrt(13) = [3; 1,1,1,1,6]] has period 5, so the convergents at
    indices [5k+4] obey a constant 5-step block recursion with matrix
    N = [[33,20],[5,3]] (det N = -1): [(p_{5(k+1)}, p_{5(k+1)-1}) = N (p_{5k},
    p_{5k-1})], the q-stream sharing the coefficients — the period-class dual
    of the period-one 2m one-step recursion.  Carries the dual streams
    [d13pair]/[e13pair], [d13x]/[d13y]/[d13z]/[d13w], the norm fold
    [d13_norm_quad], main statements [d13_norm_x]/[d13_norm_y]/
    [d13_norm_y_abs1], [d13_det] (constant 5), [d13_nonsquare], [d13_member],
    [d13_family_sharp]/[d13_family_sep], [d13_q_square_sharp],
    [d13_q_square_gap_instance], and six vm_compute numerical anchors.

    Dependencies.  Stdlib [ZArith.ZArith], [Arith.Arith], [Bool.Bool], [Lia],
    [QArith.QArith], [QArith.Qabs]; this development's [S01_BaseRing],
    [S02_CauchyComplete], [fib_machine], [fib_qdomain], [pell_family].

    References.  The period-one family [pell_family] (D = m^2+1), whose twin
    certificates this module instantiates at constant 5; see [fib_qdomain].

    Constructivity.  Statement faces all carried by [Set] ([QeqT]/[QleT']/
    [Id], [And]); in-body constructive Prop derivation is legal, bridged back
    by [zeq_id] at exit positions; the main statements close structurally
    with no solver; no global assumptions, no classical logic.

    Build.  [rocq c -native-compiler no -q -Q . "" d13_family.v] compiles
    cleanly (exit 0); extraction is free of [Obj.magic]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
Require Import pell_family.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* Set-carry micro-bridges (in-file toolbox for the all-true restatement)  *)
(* ============================================================ *)

(* Prop equality -> Set-carried Id (exit-position bridge; the canonical form of
   eq singleton elimination, same shape as S02 qeq_imp_qeqT: the premise may be
   Prop, the conclusion is Set-carried) *)
Definition zeq_id {A : Set} {a b : A} (h : a = b) : Id a b :=
  match h with
  | eq_refl => id_refl
  end.

(* Id witness -> Prop equality (in-proof bridge unfolding; consumed by rewrite/ring/lia) *)
Definition id_zeq {A : Set} {a b : A} (h : Id a b) : a = b :=
  match h with
  | id_refl => eq_refl
  end.

(* ============================================================ *)
(* Section C. Carrier layer: d13pair/e13pair dual threading, d13x/y/z/w, recursive unfoldings, positivity  *)
(* ============================================================ *)

(* X stream: (x_{k+1},y_{k+1}) = N (x_k,y_k) with N = [[33,20],[5,3]]; base (p_0,p_{-1}) = (3,1) *)
Fixpoint d13pair (n : nat) : Z * Z :=
  match n with
  | O => (3%Z, 1%Z)
  | Datatypes.S k => match d13pair k with pair x y => ((33 * x + 20 * y)%Z, (5 * x + 3 * y)%Z) end
  end.

(* Q stream: the same-coefficient 5-step recursion; base (q_0,q_{-1}) = (1,0) *)
Fixpoint e13pair (n : nat) : Z * Z :=
  match n with
  | O => (1%Z, 0%Z)
  | Datatypes.S k => match e13pair k with pair x y => ((33 * x + 20 * y)%Z, (5 * x + 3 * y)%Z) end
  end.

Definition d13x (n : nat) : Z := fst (d13pair n).
Definition d13y (n : nat) : Z := snd (d13pair n).
Definition d13z (n : nat) : Z := fst (e13pair n).
Definition d13w (n : nat) : Z := snd (e13pair n).

Lemma d13x_0 : Id (d13x 0) 3%Z.
Proof. vm_compute. apply id_refl. Qed.

Lemma d13y_0 : Id (d13y 0) 1%Z.
Proof. vm_compute. apply id_refl. Qed.

Lemma d13z_0 : Id (d13z 0) 1%Z.
Proof. vm_compute. apply id_refl. Qed.

Lemma d13w_0 : Id (d13w 0) 0%Z.
Proof. vm_compute. apply id_refl. Qed.

Lemma d13pair_unfold : forall n : nat,
  Id (d13pair (Datatypes.S n))
     ((33 * fst (d13pair n) + 20 * snd (d13pair n))%Z,
      (5 * fst (d13pair n) + 3 * snd (d13pair n))%Z).
Proof. intro n. cbn [d13pair]. destruct (d13pair n) as [a b]. exact id_refl. Qed.

Lemma e13pair_unfold : forall n : nat,
  Id (e13pair (Datatypes.S n))
     ((33 * fst (e13pair n) + 20 * snd (e13pair n))%Z,
      (5 * fst (e13pair n) + 3 * snd (e13pair n))%Z).
Proof. intro n. cbn [e13pair]. destruct (e13pair n) as [a b]. exact id_refl. Qed.

Lemma d13x_rec : forall n, Id (d13x (Datatypes.S n)) (33 * d13x n + 20 * d13y n)%Z.
Proof. intro n. unfold d13x, d13y. exact (id_cong fst (d13pair_unfold n)). Qed.

Lemma d13y_rec : forall n, Id (d13y (Datatypes.S n)) (5 * d13x n + 3 * d13y n)%Z.
Proof. intro n. unfold d13x, d13y. exact (id_cong snd (d13pair_unfold n)). Qed.

Lemma d13z_rec : forall n, Id (d13z (Datatypes.S n)) (33 * d13z n + 20 * d13w n)%Z.
Proof. intro n. unfold d13z, d13w. exact (id_cong fst (e13pair_unfold n)). Qed.

Lemma d13w_rec : forall n, Id (d13w (Datatypes.S n)) (5 * d13z n + 3 * d13w n)%Z.
Proof. intro n. unfold d13z, d13w. exact (id_cong snd (e13pair_unfold n)). Qed.

(* Positivity layer: x/y streams >= 1 throughout; z stream >= 1, w stream >= 0,
   and w_{n+1} >= 1 (guards the Q denominator position and the Zpos bridge)
   -- Z-order station form: Id (Z.leb b _) true (as in b1_kernel_pointwise) *)
Lemma d13xy_ge1 : forall n,
  And (Id (Z.leb 1 (d13x n)) true) (Id (Z.leb 1 (d13y n)) true).
Proof.
  induction n as [|n [IH1 IH2]].
  - split; vm_compute; apply id_refl.
  - split.
    + apply zeq_id. apply (proj2 (Z.leb_le 1 (d13x (Datatypes.S n)))).
      rewrite (id_zeq (d13x_rec n)).
      pose proof (proj1 (Z.leb_le 1 (d13x n)) (id_zeq IH1)).
      pose proof (proj1 (Z.leb_le 1 (d13y n)) (id_zeq IH2)). lia.
    + apply zeq_id. apply (proj2 (Z.leb_le 1 (d13y (Datatypes.S n)))).
      rewrite (id_zeq (d13y_rec n)).
      pose proof (proj1 (Z.leb_le 1 (d13x n)) (id_zeq IH1)).
      pose proof (proj1 (Z.leb_le 1 (d13y n)) (id_zeq IH2)). lia.
Qed.

Lemma d13zw_ge : forall n,
  And (Id (Z.leb 1 (d13z n)) true) (Id (Z.leb 0 (d13w n)) true).
Proof.
  induction n as [|n [IH1 IH2]].
  - split; vm_compute; apply id_refl.
  - split.
    + apply zeq_id. apply (proj2 (Z.leb_le 1 (d13z (Datatypes.S n)))).
      rewrite (id_zeq (d13z_rec n)).
      pose proof (proj1 (Z.leb_le 1 (d13z n)) (id_zeq IH1)).
      pose proof (proj1 (Z.leb_le 0 (d13w n)) (id_zeq IH2)). lia.
    + apply zeq_id. apply (proj2 (Z.leb_le 0 (d13w (Datatypes.S n)))).
      rewrite (id_zeq (d13w_rec n)).
      pose proof (proj1 (Z.leb_le 1 (d13z n)) (id_zeq IH1)).
      pose proof (proj1 (Z.leb_le 0 (d13w n)) (id_zeq IH2)). lia.
Qed.

Lemma d13w_ge1 : forall n, Id (Z.leb 1 (d13w (Datatypes.S n))) true.
Proof.
  intro n. apply zeq_id. apply (proj2 (Z.leb_le 1 (d13w (Datatypes.S n)))).
  rewrite (id_zeq (d13w_rec n)).
  destruct (d13zw_ge n) as [Hz Hw].
  pose proof (proj1 (Z.leb_le 1 (d13z n)) (id_zeq Hz)).
  pose proof (proj1 (Z.leb_le 0 (d13w n)) (id_zeq Hw)). lia.
Qed.

(* ============================================================ *)
(* Section N. Norm layer: the d13_norm_quad four-invariant fold + det + nonsquare  *)
(* ============================================================ *)

(* Four-invariant induction: S1 (x-stream norm +/-4), S2 (y-stream norm +/-1),
   C (cross term 3*(+/-1)), G (companion +/-1)
   Under the 5-step matrix N: S1' = 1089*S1 + 1320*C + 400*S2,
   S2' = 25*S1 + 30*C + 9*S2,
   C' = 165*S1 + 199*C + 60*S2, G' = -G (ring decomposition + powneg1 alternation)
   Conjunction stations are Set-level And; equality stations are Id with the
   zeq_id exit bridge (ring/lia stay inside the proof bodies) *)
Lemma d13_norm_quad : forall n : nat,
  And (Id ((d13x n * d13x n - 13 * (d13z n * d13z n))%Z)
          (4 * powneg1 (Datatypes.S n))%Z)
      (And (Id ((d13y n * d13y n - 13 * (d13w n * d13w n))%Z) (powneg1 n)%Z)
           (And (Id ((d13x n * d13y n - 13 * (d13z n * d13w n))%Z) (3 * powneg1 n)%Z)
                (Id ((d13y n * d13z n - d13x n * d13w n)%Z) (powneg1 n)%Z))).
Proof.
  induction n as [|n [H1 [H2 [H3 H4]]]].
  - split; [| split; [| split]].
    + apply zeq_id. unfold d13x, d13y, d13z, d13w. cbn [d13pair e13pair fst snd powneg1]. ring.
    + apply zeq_id. unfold d13x, d13y, d13z, d13w. cbn [d13pair e13pair fst snd powneg1]. ring.
    + apply zeq_id. unfold d13x, d13y, d13z, d13w. cbn [d13pair e13pair fst snd powneg1]. ring.
    + apply zeq_id. unfold d13x, d13y, d13z, d13w. cbn [d13pair e13pair fst snd powneg1]. ring.
  - split; [| split; [| split]].
    + apply zeq_id. rewrite (id_zeq (d13x_rec n)), (id_zeq (d13z_rec n)), powneg1_2.
      transitivity ((1089 * (d13x n * d13x n - 13 * (d13z n * d13z n))
                    + 1320 * (d13x n * d13y n - 13 * (d13z n * d13w n))
                    + 400 * (d13y n * d13y n - 13 * (d13w n * d13w n)))%Z).
      * ring.
      * rewrite (id_zeq H1), (id_zeq H3), (id_zeq H2). rewrite powneg1_S. ring.
    + apply zeq_id. rewrite (id_zeq (d13y_rec n)), (id_zeq (d13w_rec n)).
      transitivity ((25 * (d13x n * d13x n - 13 * (d13z n * d13z n))
                    + 30 * (d13x n * d13y n - 13 * (d13z n * d13w n))
                    + 9 * (d13y n * d13y n - 13 * (d13w n * d13w n)))%Z).
      * ring.
      * rewrite (id_zeq H1), (id_zeq H3), (id_zeq H2). rewrite powneg1_S. ring.
    + apply zeq_id. rewrite (id_zeq (d13x_rec n)), (id_zeq (d13y_rec n)),
              (id_zeq (d13z_rec n)), (id_zeq (d13w_rec n)).
      transitivity ((165 * (d13x n * d13x n - 13 * (d13z n * d13z n))
                    + 199 * (d13x n * d13y n - 13 * (d13z n * d13w n))
                    + 60 * (d13y n * d13y n - 13 * (d13w n * d13w n)))%Z).
      * ring.
      * rewrite (id_zeq H1), (id_zeq H3), (id_zeq H2). rewrite powneg1_S. ring.
    + apply zeq_id. rewrite (id_zeq (d13y_rec n)), (id_zeq (d13z_rec n)),
              (id_zeq (d13x_rec n)), (id_zeq (d13w_rec n)).
      transitivity ((- (d13y n * d13z n - d13x n * d13w n))%Z).
      * ring.
      * rewrite (id_zeq H4). rewrite powneg1_S. reflexivity.
Qed.

(* Main statement 1 (x-stream norm, the period-class novelty): x^2 - 13 z^2 = +/-4 alternating (the p_{5k} position, checked against all true convergents) *)
Theorem d13_norm_x : forall n : nat,
  Id ((d13x n * d13x n - 13 * (d13z n * d13z n))%Z) (4 * powneg1 (Datatypes.S n))%Z.
Proof. intro n. exact (fst (d13_norm_quad n)). Qed.

(* Main statement 2 (y-stream norm, the Pell mainline): y^2 - 13 w^2 = +/-1 alternating (the p_{5k-1} position, the +/-1 subfamily) *)
Theorem d13_norm_y : forall n : nat,
  Id ((d13y n * d13y n - 13 * (d13w n * d13w n))%Z) (powneg1 n)%Z.
Proof. intro n. exact (fst (snd (d13_norm_quad n))). Qed.

(* The integral gap is exactly 1 on the family (y stream: the gen_gapD_ne lower bound >= 1 attained exactly on the family) *)
Theorem d13_norm_y_abs1 : forall n : nat,
  Id (Z.abs ((d13y n * d13y n - 13 * (d13w n * d13w n))%Z)) 1%Z.
Proof. intro n. apply zeq_id. rewrite (id_zeq (d13_norm_y n)). exact (id_zeq (zabs_powneg1 n)). Qed.

(* Main statement 3 (subfamily determinant): y_n*w_{n+1} - y_{n+1}*w_n = 5*powneg1 n
   -- the sharpness-certificate constant 5 (the B_{21} entry of det N = -1);
   the period-class dual of pell_det *)
Theorem d13_det : forall n : nat,
  Id ((d13y n * d13w (Datatypes.S n) - d13y (Datatypes.S n) * d13w n)%Z)
     (5 * powneg1 n)%Z.
Proof.
  intro n. apply zeq_id.
  rewrite (id_zeq (d13w_rec n)), (id_zeq (d13y_rec n)).
  transitivity ((5 * (d13y n * d13z n - d13x n * d13w n))%Z).
  - ring.
  - rewrite (id_zeq (snd (snd (snd (d13_norm_quad n))))). reflexivity.
Qed.

(* 13 is not a perfect square (bounds 3^2 < 13 < 4^2 give a contradiction; supplies the non-square premise before any q_square_gap use) *)
Lemma d13_nonsquare : forall c : Z, (13 <> c * c)%Z.
Proof.
  intro c. intro Hc. exfalso.
  pose proof (Z.abs_square c) as Habs. pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = 13)%Z) by lia.
  assert (Hgt : (3 < Z.abs c)%Z).
  { destruct (Z_lt_le_dec 3 (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============================================================ *)
(* Section Q. Final assembly layer: the Zpos bridge + d13_member + the twin theorems + Q-square sharpness  *)
(* ============================================================ *)

Definition d13yp (k : nat) : positive := Zpos_of (d13y (Datatypes.S k)).
Definition d13wp (k : nat) : positive := Zpos_of (d13w (Datatypes.S k)).

Lemma d13yp_pos : forall k, Id (Z.pos (d13yp k)) (d13y (Datatypes.S k)).
Proof.
  intro k. unfold d13yp. apply Zpos_of_pos.
  destruct (d13xy_ge1 (Datatypes.S k)) as [_ Hy].
  pose proof (proj1 (Z.leb_le 1 (d13y (Datatypes.S k))) (id_zeq Hy)). lia.
Qed.

Lemma d13wp_pos : forall k, Id (Z.pos (d13wp k)) (d13w (Datatypes.S k)).
Proof.
  intro k. unfold d13wp. apply Zpos_of_pos.
  pose proof (d13w_ge1 k).
  pose proof (proj1 (Z.leb_le 1 (d13w (Datatypes.S k))) (id_zeq H)). lia.
Qed.

(* Family member: p_{5k+4}/q_{5k+4}, the (5k+4)-th convergent of sqrt(13) (the x^2 - 13 y^2 = +/-1 subfamily; k = 0 gives 18/5) *)
Definition d13_member (k : nat) : Q := (Z.pos (d13yp k) # d13wp k)%Q.

(* Family-certificate sharpness (main statement 1): the distance of adjacent
   family members equals 5/(w_{k+1} w_{k+2}) exactly
   -- the d13_det +/-5 equality realized (same shape as pell_family_sharp,
   constant 1 -> 5 period-class form) *)
Theorem d13_family_sharp : forall k : nat,
  QeqT (Qabs (d13_member k - d13_member (Datatypes.S k)))
       ((Z.pos 5) # (d13wp k * d13wp (Datatypes.S k)))%Q.
Proof.
  intro k.
  assert (Hd : (d13_member k - d13_member (Datatypes.S k))%Q ==
               ((Z.pos (d13yp k) * Z.pos (d13wp (Datatypes.S k))
                 - Z.pos (d13yp (Datatypes.S k)) * Z.pos (d13wp k))
                 # (d13wp k * d13wp (Datatypes.S k)))%Q).
  { unfold d13_member. apply qeqT_imp_qeq. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - rewrite (id_zeq (d13yp_pos k)), (id_zeq (d13yp_pos (Datatypes.S k))).
    assert (Hd2 : (d13y (Datatypes.S k) * Z.pos (d13wp (Datatypes.S k))
                   - d13y (Datatypes.S (Datatypes.S k)) * Z.pos (d13wp k)
                   = 5 * powneg1 (Datatypes.S k))%Z).
    { pose proof (d13_det (Datatypes.S k)) as Hdet.
      rewrite <- (id_zeq (d13wp_pos (Datatypes.S k))), <- (id_zeq (d13wp_pos k)) in Hdet.
      exact (id_zeq Hdet). }
    rewrite Hd2.
    unfold Qeq, Qabs. cbn [Qnum Qden].
    rewrite Z.abs_mul, (id_zeq (zabs_powneg1 (Datatypes.S k))). cbn [Z.abs]. ring.
Qed.

(* Family separation certificate (main statement 2): any a/b is at distance
   >= 1/(b*w_{k+1}) from the family member
   (same shape as pell_family_sep; the only premise is gap <> 0) *)
Theorem d13_family_sep : forall (a : Z) (b : positive) (k : nat),
  (a * d13w (Datatypes.S k) - d13y (Datatypes.S k) * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * d13wp k)) # 1))
        (Qabs ((a # b)%Q - d13_member k)).
Proof.
  intros a b k Hk. unfold d13_member.
  assert (Hk2 : (a * Z.pos (d13wp k) - Z.pos (d13yp k) * Z.pos b <> 0)%Z).
  { rewrite (id_zeq (d13wp_pos k)), (id_zeq (d13yp_pos k)). exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (d13wp k) - Z.pos (d13yp k) * Z.pos b)
                  # (b * d13wp k))%Q)
          (Qabs ((a # b)%Q - (Z.pos (d13yp k) # d13wp k)%Q))
          (Qinv ((Z.pos (b * d13wp k)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (d13yp k) # d13wp k)%Q))
                   (Qabs ((a * Z.pos (d13wp k) - Z.pos (d13yp k) * Z.pos b)
                           # (b * d13wp k))%Q)).
    apply qeqT_imp_qeq. apply fib_qabs_congr. apply qeqT_imp_qeq. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * d13wp k)%positive).
    exact (ZLeT_drop _ _ (zabs_ge1 _ Hk2)).
Qed.

(* Q-square sharpness (main statement 3, family-side confirmation of the FIB3
   separation certificate): |member^2 - 13| = 1/w^2 exactly
   -- the q_square_gap lower bound 1/b^2 is attained exactly on the +/-1
   subfamily (same shape as pell_q_square_sharp) *)
Theorem d13_q_square_sharp : forall k : nat,
  QeqT (Qabs (d13_member k * d13_member k - (13 # 1)%Q))
       (Qinv ((Z.pos (d13wp k * d13wp k)) # 1)).
Proof.
  intro k.
  assert (Hd : (d13_member k * d13_member k - (13 # 1))%Q ==
               ((Z.pos (d13yp k) * Z.pos (d13yp k)
                 - 13 * (Z.pos (d13wp k) * Z.pos (d13wp k)))
                 # (d13wp k * d13wp k))%Q).
  { unfold d13_member. apply qeqT_imp_qeq. apply (q_square_cross (Z.pos (d13yp k)) 13 (d13wp k)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - rewrite (id_zeq (d13yp_pos k)).
    assert (Hn2 : (d13y (Datatypes.S k) * d13y (Datatypes.S k)
                   - 13 * (Z.pos (d13wp k) * Z.pos (d13wp k)) = powneg1 (Datatypes.S k))%Z).
    { pose proof (d13_norm_y (Datatypes.S k)) as Hn.
      rewrite <- (id_zeq (d13wp_pos k)) in Hn. exact (id_zeq Hn). }
    rewrite Hn2.
    destruct (powneg1 (Datatypes.S k)) as [|p|p] eqn:E.
    + exfalso. pose proof (id_zeq (zabs_powneg1 (Datatypes.S k))) as Hz. rewrite E in Hz. cbn in Hz. discriminate.
    + pose proof (id_zeq (zabs_powneg1 (Datatypes.S k))) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.pos 1 # d13wp k * d13wp k)) with (Z.pos 1 # d13wp k * d13wp k)%Q.
      change (Qinv (Z.pos (d13wp k * d13wp k) # 1)) with (1 # d13wp k * d13wp k)%Q.
      apply Qeq_refl.
    + pose proof (id_zeq (zabs_powneg1 (Datatypes.S k))) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.neg 1 # d13wp k * d13wp k)) with (Z.pos 1 # d13wp k * d13wp k)%Q.
      change (Qinv (Z.pos (d13wp k * d13wp k) # 1)) with (1 # d13wp k * d13wp k)%Q.
      apply Qeq_refl.
Qed.

(* Instance invocation of q_square_gap (the FIB3 main statement instantiated on the D = 13 family; together with sharpness the lower bound is exactly attained) *)
Lemma d13_q_square_gap_instance : forall k : nat,
  QleT' (Qinv ((Z.pos (d13wp k * d13wp k)) # 1))
        (Qabs (d13_member k * d13_member k - (13 # 1)%Q)).
Proof.
  intro k. unfold d13_member.
  apply (q_square_gap 13 (Z.pos (d13yp k)) (d13wp k)).
  - cbn. lia.
  - intro c. apply (d13_nonsquare c).
Qed.

(* ============================================================ *)
(* Section A. Audit: Print Assumptions + Separate Extraction + vm_compute numerical anchors  *)
(* ============================================================ *)

Print Assumptions d13x_rec.
Print Assumptions d13y_rec.
Print Assumptions d13z_rec.
Print Assumptions d13w_rec.
Print Assumptions d13xy_ge1.
Print Assumptions d13zw_ge.
Print Assumptions d13w_ge1.
Print Assumptions d13_norm_quad.
Print Assumptions d13_norm_x.
Print Assumptions d13_norm_y.
Print Assumptions d13_norm_y_abs1.
Print Assumptions d13_det.
Print Assumptions d13_nonsquare.
Print Assumptions Zpos_of_pos.
Print Assumptions d13yp_pos.
Print Assumptions d13wp_pos.
Print Assumptions d13_family_sep.
Print Assumptions d13_family_sharp.
Print Assumptions d13_q_square_sharp.
Print Assumptions d13_q_square_gap_instance.

(* Anchor 1 (family member): member 0 = p_4/q_4 = 18/5 (x^2 - 13 y^2 = -1) *)
Lemma smoke_member_18_5 : Id (Qeq_bool (d13_member 0) (18 # 5)%Q) true.
Proof. vm_compute. apply id_refl. Qed.

(* Anchor 2 (family member): member 1 = p_9/q_9 = 649/180 (x^2 - 13 y^2 = +1) *)
Lemma smoke_member_649_180 : Id (Qeq_bool (d13_member 1) (649 # 180)%Q) true.
Proof. vm_compute. apply id_refl. Qed.

(* Anchor 3 (norm layer): |18^2 - 13*5^2| = 1 (instance of d13_norm_y_abs1) *)
Lemma smoke_norm_1 : Id (Z.eqb (Z.abs (d13y 1 * d13y 1 - 13 * (d13w 1 * d13w 1))) 1%Z) true.
Proof. vm_compute. apply id_refl. Qed.

(* Anchor 4 (sharpness layer): |18/5 - 649/180| = 1/180 = 5/(5*180) exactly (instance of d13_family_sharp) *)
Lemma smoke_sharp_1_180 :
  Id (Qeq_bool (Qabs (d13_member 0 - d13_member 1))
              ((Z.pos 5) # (d13wp 0 * d13wp 1))%Q) true.
Proof. vm_compute. apply id_refl. Qed.

(* Anchor 5 (Q-square sharpness): |(18/5)^2 - 13| = 1/25 (instance of d13_q_square_sharp, family-side equality of the FIB3 certificate) *)
Lemma smoke_qsq_1_25 :
  Id (Qeq_bool (Qabs (d13_member 0 * d13_member 0 - (13 # 1)%Q))
             (Qinv ((Z.pos (d13wp 0 * d13wp 0)) # 1))) true.
Proof. vm_compute. apply id_refl. Qed.

(* Anchor 6 (N-matrix step): x_1 = 119, z_1 = 33 (the p_5/q_5 carrier values) *)
Lemma smoke_step_119_33 :
  Id (Z.eqb (d13x 1) 119%Z, Z.eqb (d13z 1) 33%Z) (true, true).
Proof. vm_compute. apply id_refl. Qed.

Print Assumptions smoke_member_18_5.
Print Assumptions smoke_member_649_180.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_180.
Print Assumptions smoke_qsq_1_25.
Print Assumptions smoke_step_119_33.

From Stdlib Require Import Extraction.
Separate Extraction d13pair e13pair d13x d13y d13z d13w d13yp d13wp
  d13_member d13_norm_y_abs1 d13_det d13_family_sep d13_family_sharp
  d13_q_square_sharp d13_q_square_gap_instance
  smoke_member_18_5 smoke_member_649_180 smoke_norm_1 smoke_sharp_1_180
  smoke_qsq_1_25 smoke_step_119_33.
