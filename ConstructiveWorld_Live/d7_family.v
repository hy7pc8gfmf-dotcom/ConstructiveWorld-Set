(* ConstructiveWorld-Set — Pell-type convergence subfamilies via constant-coefficient matrix recursions. *)

(** * d7_family: the D = 7 period-4 convergence subfamily (T = 4 rung).

    Mission.  [sqrt(7) = [2; 1,1,1,4]] has period 4, so the convergents at
    indices [4k+3] obey a constant 4-step block recursion with matrix
    N = [[14,3],[9,2]] (det N = +1).  As [x^2 = -1 (mod 7)] has no solution,
    the negative Pell equation has none, and [x^2 - 7 y^2 = +1] has a single
    solution family with norm +1 at every index [4k+3].  Carries the streams
    [d7x]/[d7y]/[d7z]/[d7w], the norm invariants [d7_norm_quad],
    [d7_norm_x]/[d7_norm_y]/[d7_norm_y_abs3], [d7_det] (constant 3),
    [d7_nonsquare], [d7_member], [d7_family_sharp]/[d7_family_sep]/
    [d7_q_square_sharp], [d7_q_square_gap_instance].

    Dependencies.  Stdlib [ZArith.ZArith], [Arith.Arith], [Bool.Bool], [Lia],
    [QArith.QArith], [QArith.Qabs]; this development's [S01_BaseRing],
    [S02_CauchyComplete], [fib_machine], [fib_qdomain], [pell_family].

    References.  ConstructiveWorld-Main [d7_family] (statement names
    carried over verbatim); the sibling modules [d3_family] and
    [d6_family] instantiate the same constant-coefficient scheme.

    Constructivity.  All named statements are carried by [Set]
    ([QeqT]/[QleT']/[Id], [And]); solvers serve only auxiliary bookkeeping
    while the main statements close structurally; every proof ends in
    [Qed], with no global assumptions, no classical logic.

    Build.  [rocq c -native-compiler no -q -Q . "" d7_family.v] compiles
    cleanly (exit 0); extraction is free of [Obj.magic]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
Require Import pell_family.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* Section C. Carrier layer: the dual thread [d7pair]/[e7pair], the     *)
(*   component streams [d7x]/[d7y]/[d7z]/[d7w], the unfold lemmas,      *)
(*   and the positivity layer.                                          *)
(* ============================================================ *)

(* Canonical eq-to-[Id] bridge, same construction as [bxra_id_of_eq] of
   UpReqBanachInstReal.v: destruct along the index. *)
Lemma id_of_eq : forall (A : Set) (z w : A), z = w -> Id z w.
Proof.
  intros A z w H.
  exact (match H in (_ = t) return Id z t with
         | eq_refl => id_refl
         end).
Qed.

(* Set-level lift of [<=] on [Z], same construction as [NatLe_lift] of
   S01_BaseRing.v: decided through the [Z.leb] boolean. *)
Lemma zlebT_lift : forall (z w : Z), (z <= w)%Z -> Id (Z.leb z w) true.
Proof.
  intros z w H. destruct (Z.leb z w) eqn:E.
  - reflexivity.
  - exfalso. apply (proj1 (Z.leb_gt z w)) in E. lia.
Qed.

(* X-stream: [(x_{k+1}, y_{k+1}) = N (x_k, y_k)] with N = [[14,3],[9,2]],
   base [(p_3, p_2) = (8, 5)]. *)
Fixpoint d7pair (n : nat) : Z * Z :=
  match n with
  | O => (8%Z, 5%Z)
  | Datatypes.S k =>
      match d7pair k with pair x y => ((14 * x + 3 * y)%Z, (9 * x + 2 * y)%Z) end
  end.

(* Q-stream: same-coefficient 4-step recursion, base [(q_3, q_2) = (3, 2)]. *)
Fixpoint e7pair (n : nat) : Z * Z :=
  match n with
  | O => (3%Z, 2%Z)
  | Datatypes.S k =>
      match e7pair k with pair x y => ((14 * x + 3 * y)%Z, (9 * x + 2 * y)%Z) end
  end.

Definition d7x (n : nat) : Z := fst (d7pair n).
Definition d7y (n : nat) : Z := snd (d7pair n).
Definition d7z (n : nat) : Z := fst (e7pair n).
Definition d7w (n : nat) : Z := snd (e7pair n).

Lemma d7x_0 : Id (d7x 0) 8%Z.
Proof. reflexivity. Qed.

Lemma d7y_0 : Id (d7y 0) 5%Z.
Proof. reflexivity. Qed.

Lemma d7z_0 : Id (d7z 0) 3%Z.
Proof. reflexivity. Qed.

Lemma d7w_0 : Id (d7w 0) 2%Z.
Proof. reflexivity. Qed.

Lemma d7pair_unfold : forall n : nat,
  Id (d7pair (Datatypes.S n))
     ((14 * fst (d7pair n) + 3 * snd (d7pair n))%Z,
      (9 * fst (d7pair n) + 2 * snd (d7pair n))%Z).
Proof. intro n. cbn [d7pair]. destruct (d7pair n) as [a b]. reflexivity. Qed.

Lemma e7pair_unfold : forall n : nat,
  Id (e7pair (Datatypes.S n))
     ((14 * fst (e7pair n) + 3 * snd (e7pair n))%Z,
      (9 * fst (e7pair n) + 2 * snd (e7pair n))%Z).
Proof. intro n. cbn [e7pair]. destruct (e7pair n) as [a b]. reflexivity. Qed.

Lemma d7x_rec : forall n, Id (d7x (Datatypes.S n)) ((14 * d7x n + 3 * d7y n)%Z).
Proof.
  intro n. unfold d7x, d7y.
  exact (id_cong (fun p : Z * Z => fst p) (d7pair_unfold n)).
Qed.

Lemma d7y_rec : forall n, Id (d7y (Datatypes.S n)) ((9 * d7x n + 2 * d7y n)%Z).
Proof.
  intro n. unfold d7x, d7y.
  exact (id_cong (fun p : Z * Z => snd p) (d7pair_unfold n)).
Qed.

Lemma d7z_rec : forall n, Id (d7z (Datatypes.S n)) ((14 * d7z n + 3 * d7w n)%Z).
Proof.
  intro n. unfold d7z, d7w.
  exact (id_cong (fun p : Z * Z => fst p) (e7pair_unfold n)).
Qed.

Lemma d7w_rec : forall n, Id (d7w (Datatypes.S n)) ((9 * d7z n + 2 * d7w n)%Z).
Proof.
  intro n. unfold d7z, d7w.
  exact (id_cong (fun p : Z * Z => snd p) (e7pair_unfold n)).
Qed.

(* Positivity layer: the streams [d7x]/[d7y]/[d7z] stay >= 1 and [d7w]
   stays >= 0 (guards the Q denominator slot and the [Zpos] bridge);
   statement face carried by [Set]. *)
Lemma d7xy_ge1 : forall n : nat,
  And (Id (Z.leb 1 (d7x n)) true) (Id (Z.leb 1 (d7y n)) true).
Proof.
  intro n.
  assert (Hn : (1 <= d7x n)%Z /\ (1 <= d7y n)%Z).
  { induction n as [|n [IH1 IH2]].
    - split; cbn [d7x d7y d7pair fst snd]; lia.
    - split.
      + destruct (id_sym (d7x_rec n)). lia.
      + destruct (id_sym (d7y_rec n)). lia. }
  split.
  - apply (zlebT_lift 1 (d7x n)). exact (proj1 Hn).
  - apply (zlebT_lift 1 (d7y n)). exact (proj2 Hn).
Qed.

Lemma d7zw_ge : forall n : nat,
  And (Id (Z.leb 1 (d7z n)) true) (Id (Z.leb 0 (d7w n)) true).
Proof.
  intro n.
  assert (Hn : (1 <= d7z n)%Z /\ (0 <= d7w n)%Z).
  { induction n as [|n [IH1 IH2]].
    - split; cbn [d7z d7w e7pair fst snd]; lia.
    - split.
      + destruct (id_sym (d7z_rec n)). lia.
      + destruct (id_sym (d7w_rec n)). lia. }
  split.
  - apply (zlebT_lift 1 (d7z n)). exact (proj1 Hn).
  - apply (zlebT_lift 0 (d7w n)). exact (proj2 Hn).
Qed.

(* ============================================================ *)
(* Section N. Norm layer: the four constant invariants of               *)
(*   [d7_norm_quad], the determinant [d7_det], and [d7_nonsquare].      *)
(* ============================================================ *)

(* Induction over the four invariants (period-4 constant-coefficient
   shape): the base pairs (8,5)/(3,2) close by ring; the step identities
   S1' = 196*S1 + 84*C + 9*S2, S2' = 81*S1 + 36*C + 4*S2,
   C' = 126*S1 + 55*C + 6*S2, G' = G (det N = +1 reproduces itself) close
   the ring decomposition; the statement face is carried by [And] + [Id]
   over [Set]. *)
Lemma d7_norm_quad : forall n : nat,
  And (Id ((d7x n * d7x n - 7 * (d7z n * d7z n))%Z) 1%Z)
      (And (Id ((d7y n * d7y n - 7 * (d7w n * d7w n))%Z) (-3)%Z)
           (And (Id ((d7x n * d7y n - 7 * (d7z n * d7w n))%Z) (-2)%Z)
                (Id ((d7y n * d7z n - d7x n * d7w n)%Z) (-1)%Z))).
Proof.
  intro n.
  assert (Hq : (d7x n * d7x n - 7 * (d7z n * d7z n) = 1)%Z /\
               (d7y n * d7y n - 7 * (d7w n * d7w n) = (-3))%Z /\
               (d7x n * d7y n - 7 * (d7z n * d7w n) = (-2))%Z /\
               (d7y n * d7z n - d7x n * d7w n = (-1))%Z).
  { induction n as [|n [H1 [H2 [H3 H4]]]].
    - split; [| split; [| split]].
      + unfold d7x, d7y, d7z, d7w. cbn [d7pair e7pair fst snd]. ring.
      + unfold d7x, d7y, d7z, d7w. cbn [d7pair e7pair fst snd]. ring.
      + unfold d7x, d7y, d7z, d7w. cbn [d7pair e7pair fst snd]. ring.
      + unfold d7x, d7y, d7z, d7w. cbn [d7pair e7pair fst snd]. ring.
    - destruct (id_sym (d7x_rec n)). destruct (id_sym (d7z_rec n)).
      destruct (id_sym (d7y_rec n)). destruct (id_sym (d7w_rec n)).
      split; [| split; [| split]].
      + transitivity ((196 * (d7x n * d7x n - 7 * (d7z n * d7z n))
                    + 84 * (d7x n * d7y n - 7 * (d7z n * d7w n))
                    + 9 * (d7y n * d7y n - 7 * (d7w n * d7w n)))%Z).
        * ring.
        * rewrite H1, H3, H2. ring.
      + transitivity ((81 * (d7x n * d7x n - 7 * (d7z n * d7z n))
                    + 36 * (d7x n * d7y n - 7 * (d7z n * d7w n))
                    + 4 * (d7y n * d7y n - 7 * (d7w n * d7w n)))%Z).
        * ring.
        * rewrite H1, H3, H2. ring.
      + transitivity ((126 * (d7x n * d7x n - 7 * (d7z n * d7z n))
                    + 55 * (d7x n * d7y n - 7 * (d7z n * d7w n))
                    + 6 * (d7y n * d7y n - 7 * (d7w n * d7w n)))%Z).
        * ring.
        * rewrite H1, H3, H2. ring.
      + transitivity ((d7y n * d7z n - d7x n * d7w n)%Z).
        * ring.
        * exact H4. }
  split; [| split; [| split]].
  - exact (id_of_eq Z _ _ (proj1 Hq)).
  - exact (id_of_eq Z _ _ (proj1 (proj2 Hq))).
  - exact (id_of_eq Z _ _ (proj1 (proj2 (proj2 Hq)))).
  - exact (id_of_eq Z _ _ (proj2 (proj2 (proj2 Hq)))).
Qed.

(* Main statement 1 (member-stream norm): [x^2 - 7 z^2 = 1] on the single
   +1 family. *)
Theorem d7_norm_x : forall n : nat,
  Id ((d7x n * d7x n - 7 * (d7z n * d7z n))%Z) 1%Z.
Proof. intro n. exact (fst (d7_norm_quad n)). Qed.

(* Main statement 2 (companion-stream norm): [y^2 - 7 w^2 = -3]. *)
Theorem d7_norm_y : forall n : nat,
  Id ((d7y n * d7y n - 7 * (d7w n * d7w n))%Z) (-3)%Z.
Proof. intro n. exact (fst (snd (d7_norm_quad n))). Qed.

(* The integer gap on the companion stream is exactly 3. *)
Theorem d7_norm_y_abs3 : forall n : nat,
  Id (Z.abs (d7y n * d7y n - 7 * (d7w n * d7w n))) 3%Z.
Proof.
  intro n. destruct (id_sym (d7_norm_y n)). apply id_refl.
Qed.

(* Main statement 3 (subfamily determinant): [x_n z_{n+1} - x_{n+1} z_n = 3],
   the sharpness certificate constant 3 (the B_12 slot of the member row
   equals [q_3]). *)
Theorem d7_det : forall n : nat,
  Id ((d7x n * d7z (Datatypes.S n) - d7x (Datatypes.S n) * d7z n)%Z) 3%Z.
Proof.
  intro n.
  assert (Heq : (d7x n * d7z (Datatypes.S n)
                 - d7x (Datatypes.S n) * d7z n = 3)%Z).
  { destruct (id_sym (d7z_rec n)). destruct (id_sym (d7x_rec n)).
    transitivity ((- (3 * (d7y n * d7z n - d7x n * d7w n)))%Z).
    - ring.
    - destruct (id_sym (snd (snd (snd (d7_norm_quad n))))). reflexivity. }
  destruct Heq. apply id_refl.
Qed.

(* 7 is not a perfect square: the bounds [2^2 < 7 < 3^2] give a
   contradiction (discharges the side condition of [q_square_gap] at its
   use sites). *)
Lemma d7_nonsquare : forall c : Z, (7 <> c * c)%Z.
Proof.
  intro c. intro Hc. exfalso.
  pose proof (Z.abs_square c) as Habs. pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = 7)%Z) by lia.
  assert (Hgt : (2 < Z.abs c)%Z).
  { destruct (Z_lt_le_dec 2 (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============================================================ *)
(* Section Q. Final assembly layer: the [Zpos] bridge, [d7_member],     *)
(*   the family theorems, and the Q-square sharpness.                   *)
(* ============================================================ *)

Definition d7yp (k : nat) : positive := Zpos_of (d7x k).
Definition d7wp (k : nat) : positive := Zpos_of (d7z k).

Lemma d7yp_pos : forall k, Id (Z.pos (d7yp k)) (d7x k).
Proof.
  intro k.
  assert (Hpos : (0 < d7x k)%Z /\ (0 < d7y k)%Z).
  { induction k as [|k [IH1 IH2]].
    - split; cbn [d7x d7y d7pair fst snd]; lia.
    - split.
      + destruct (id_sym (d7x_rec k)). lia.
      + destruct (id_sym (d7y_rec k)). lia. }
  unfold d7yp. destruct (Zpos_of_pos (d7x k) (proj1 Hpos)). apply id_refl.
Qed.

Lemma d7wp_pos : forall k, Id (Z.pos (d7wp k)) (d7z k).
Proof.
  intro k.
  assert (Hpos : (0 < d7z k)%Z /\ (0 <= d7w k)%Z).
  { induction k as [|k [IH1 IH2]].
    - split; cbn [d7z d7w e7pair fst snd]; lia.
    - split.
      + destruct (id_sym (d7z_rec k)). lia.
      + destruct (id_sym (d7w_rec k)). lia. }
  unfold d7wp. destruct (Zpos_of_pos (d7z k) (proj1 Hpos)). apply id_refl.
Qed.

(* Family member: [p_{4k+3}/q_{4k+3}], the [4k+3]-th convergent of
   sqrt(7) (the [x^2 - 7 y^2 = +1] subfamily; k = 0 gives 8/3). *)
Definition d7_member (k : nat) : Q := (Z.pos (d7yp k) # d7wp k)%Q.

(* Family certificate sharpness (main theorem 1): the distance of adjacent
   family members equals [3/(z_k z_{k+1})] exactly, i.e. the constant 3 of
   [d7_det] is realized as an equality (period-4 analogue of
   [d3_family_sharp] with constant 1 replaced by 3). *)
Theorem d7_family_sharp : forall k : nat,
  QeqT (Qabs (d7_member k - d7_member (Datatypes.S k)))
       ((Z.pos 3) # (d7wp k * d7wp (Datatypes.S k)))%Q.
Proof.
  intro k.
  assert (Hd : (d7_member k - d7_member (Datatypes.S k))%Q ==
               ((Z.pos (d7yp k) * Z.pos (d7wp (Datatypes.S k))
                 - Z.pos (d7yp (Datatypes.S k)) * Z.pos (d7wp k))
                 # (d7wp k * d7wp (Datatypes.S k)))%Q).
  { unfold d7_member. apply qeqT_imp_qeq. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - destruct (id_sym (d7yp_pos k)). destruct (id_sym (d7yp_pos (Datatypes.S k))).
    assert (Hd2 : (d7x k * Z.pos (d7wp (Datatypes.S k))
                   - d7x (Datatypes.S k) * Z.pos (d7wp k) = 3)%Z).
    { destruct (id_trans
          (id_cong2 (fun u v : Z => (d7x k * v - d7x (Datatypes.S k) * u)%Z)
                    (d7wp_pos k) (d7wp_pos (Datatypes.S k)))
          (d7_det k)). reflexivity. }
    rewrite Hd2.
    unfold Qeq, Qabs. cbn [Qnum Qden Z.abs]. reflexivity.
Qed.

(* Family separation certificate (main theorem 2): every [a/b] stands at
   distance [>= 1/(b z_k)] from a family member (analogue of
   [d3_family_sep]; the sole premise is a nonzero gap). *)
Theorem d7_family_sep : forall (a : Z) (b : positive) (k : nat),
  (a * d7z k - d7x k * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * d7wp k)) # 1))
        (Qabs ((a # b)%Q - d7_member k)).
Proof.
  intros a b k Hk. unfold d7_member.
  assert (Hk2 : (a * Z.pos (d7wp k) - Z.pos (d7yp k) * Z.pos b <> 0)%Z).
  { destruct (id_sym (d7wp_pos k)). destruct (id_sym (d7yp_pos k)). exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (d7wp k) - Z.pos (d7yp k) * Z.pos b)
                  # (b * d7wp k))%Q)
          (Qabs ((a # b)%Q - (Z.pos (d7yp k) # d7wp k)%Q))
          (Qinv ((Z.pos (b * d7wp k)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (d7yp k) # d7wp k)%Q))
                   (Qabs ((a * Z.pos (d7wp k) - Z.pos (d7yp k) * Z.pos b)
                           # (b * d7wp k))%Q)).
    apply qeqT_imp_qeq. apply fib_qabs_congr. apply qeqT_imp_qeq. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * d7wp k)%positive).
    exact (ZLeT_drop _ _ (zabs_ge1 _ Hk2)).
Qed.

(* Q-square sharpness (main theorem 3): [|member^2 - 7| = 1/z^2] exactly,
   i.e. the lower bound [1/b^2] of [q_square_gap] is attained on the +1
   subfamily (analogue of [d3_q_square_sharp]; the constant norm 1 removes
   the alternating-sign case split). *)
Theorem d7_q_square_sharp : forall k : nat,
  QeqT (Qabs (d7_member k * d7_member k - (7 # 1)%Q))
       (Qinv ((Z.pos (d7wp k * d7wp k)) # 1)).
Proof.
  intro k.
  assert (Hd : (d7_member k * d7_member k - (7 # 1))%Q ==
               ((Z.pos (d7yp k) * Z.pos (d7yp k)
                 - 7 * (Z.pos (d7wp k) * Z.pos (d7wp k)))
                 # (d7wp k * d7wp k))%Q).
  { unfold d7_member. apply qeqT_imp_qeq. apply (q_square_cross (Z.pos (d7yp k)) 7 (d7wp k)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - destruct (id_sym (d7yp_pos k)).
    assert (Hn2 : (d7x k * d7x k
                   - 7 * (Z.pos (d7wp k) * Z.pos (d7wp k)) = 1)%Z).
    { destruct (id_trans
          (id_cong2 (fun u v : Z => (d7x k * d7x k - 7 * (u * v))%Z)
                    (d7wp_pos k) (d7wp_pos k))
          (d7_norm_x k)). reflexivity. }
    rewrite Hn2.
    change (Qabs (Z.pos 1 # d7wp k * d7wp k)) with (Z.pos 1 # d7wp k * d7wp k)%Q.
    change (Qinv (Z.pos (d7wp k * d7wp k) # 1)) with (1 # d7wp k * d7wp k)%Q.
    apply Qeq_refl.
Qed.

(* Instance use of [q_square_gap] (the FIB3 main statement instantiated on
   the D = 7 family; together with the sharpness theorem this says the
   lower bound is attained exactly). *)
Lemma d7_q_square_gap_instance : forall k : nat,
  QleT' (Qinv ((Z.pos (d7wp k * d7wp k)) # 1))
        (Qabs (d7_member k * d7_member k - (7 # 1)%Q)).
Proof.
  intro k. unfold d7_member.
  apply (q_square_gap 7 (Z.pos (d7yp k)) (d7wp k)).
  - cbn. lia.
  - intro c. apply (d7_nonsquare c).
Qed.

(* ============================================================ *)
(* Section A. Audit: [Print Assumptions], [Separate Extraction], and    *)
(*   [vm_compute] numerical anchors.                                    *)
(* ============================================================ *)

Print Assumptions d7x_rec.
Print Assumptions d7y_rec.
Print Assumptions d7z_rec.
Print Assumptions d7w_rec.
Print Assumptions d7xy_ge1.
Print Assumptions d7zw_ge.
Print Assumptions d7_norm_quad.
Print Assumptions d7_norm_x.
Print Assumptions d7_norm_y.
Print Assumptions d7_norm_y_abs3.
Print Assumptions d7_det.
Print Assumptions d7_nonsquare.
Print Assumptions Zpos_of_pos.
Print Assumptions d7yp_pos.
Print Assumptions d7wp_pos.
Print Assumptions d7_family_sep.
Print Assumptions d7_family_sharp.
Print Assumptions d7_q_square_sharp.
Print Assumptions d7_q_square_gap_instance.

(* Numerical anchor 1 (family member): [member 0 = p_3/q_3 = 8/3] with
   norm [x^2 - 7 y^2 = +1]. *)
Lemma smoke_member_8_3 : Id (Qeq_bool (d7_member 0) (8 # 3)%Q) true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 2 (family member): [member 1 = p_7/q_7 = 127/48] with
   norm [+1]. *)
Lemma smoke_member_127_48 : Id (Qeq_bool (d7_member 1) (127 # 48)%Q) true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 3 (norm layer): [|127^2 - 7*48^2| = 1] (instance of
   [d7_norm_x]). *)
Lemma smoke_norm_1 : Id (Z.eqb (Z.abs (d7x 1 * d7x 1 - 7 * (d7z 1 * d7z 1))) 1%Z) true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 4 (sharpness layer): [|8/3 - 127/48| = 1/48 =
   3/(3*48)] exactly (instance of [d7_family_sharp]). *)
Lemma smoke_sharp_1_48 :
  Id (Qeq_bool (Qabs (d7_member 0 - d7_member 1))
               ((Z.pos 3) # (d7wp 0 * d7wp 1))%Q) true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 5 (Q-square sharpness): [|(8/3)^2 - 7| = 1/9 = 1/3^2]
   (instance of [d7_q_square_sharp]). *)
Lemma smoke_qsq_1_9 :
  Id (Qeq_bool (Qabs (d7_member 0 * d7_member 0 - (7 # 1)%Q))
               (Qinv ((Z.pos (d7wp 0 * d7wp 0)) # 1))) true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 6 (matrix step): [x_1 = 127] and [z_1 = 48] (carrier
   values of [p_7/q_7]). *)
Lemma smoke_step_127_48 :
  Id (Z.eqb (d7x 1) 127%Z, Z.eqb (d7z 1) 48%Z) (true, true).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions smoke_member_8_3.
Print Assumptions smoke_member_127_48.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_48.
Print Assumptions smoke_qsq_1_9.
Print Assumptions smoke_step_127_48.

From Stdlib Require Import Extraction.
Separate Extraction d7pair e7pair d7x d7y d7z d7w d7yp d7wp
  d7_member d7_norm_y_abs3 d7_det d7_family_sep d7_family_sharp
  d7_q_square_sharp d7_q_square_gap_instance
  smoke_member_8_3 smoke_member_127_48 smoke_norm_1 smoke_sharp_1_48
  smoke_qsq_1_9 smoke_step_127_48.
