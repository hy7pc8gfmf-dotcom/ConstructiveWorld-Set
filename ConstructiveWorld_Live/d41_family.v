(* ConstructiveWorld-Set — the D = 41 period-3 two-family convergence subfamily via a constant-coefficient matrix recursion. *)

(** * d41_family: the D = 41 period-3 two-family convergence subfamily (T = 3 rung).

    Mission.  [sqrt(41) = [6; 2,2,12 ...]] has period 3, so the convergents at
    indices [3k+2] obey a constant 3-step block recursion with matrix
    N = [[62,25],[5,2]] (det N = -1).  As [x^2 = -1 (mod 41)] is solvable
    (witnesses 9 and 32), the negative Pell equation is solvable, and the
    family members at [3k+2] alternate norms [-1]/[+1], the [d13_family]
    two-family shape ([d3_family]/[d6_family] are single +1 families).
    Carries the streams [d41x]/[d41y]/[d41z]/[d41w], the norm invariants
    [d41_norm_quad]/[d41_norm_x]/[d41_norm_y]/[d41_norm_y_abs1], [d41_det]
    (sharpness constant 5), [d41_nonsquare], [d41yp]/[d41wp], [d41_member],
    and the main theorems [d41_family_sharp]/[d41_family_sep]/[d41_q_square_sharp] with [d41_q_square_gap_instance].

    Dependencies.  Stdlib [ZArith.ZArith], [Arith.Arith], [Bool.Bool], [Lia],
    [QArith.QArith], [QArith.Qabs]; this development's [S01_BaseRing],
    [S02_CauchyComplete], [fib_machine], [fib_qdomain], [fib_norm_gap].

    References.  ConstructiveWorld-Main [d41_family] (statement names
    carried over verbatim); the sibling modules [d3_family], [d6_family]
    and [d13_family] instantiate the same constant-coefficient scheme.

    Constructivity.  All named statements are carried by [Set]
    ([QeqT]/[QleT']/[Id], [And]); the main statements close structurally,
    with no global assumptions, no classical logic; proofs end in [Qed].

    Build.  [rocq c -native-compiler no -q -Q . "" d41_family.v] compiles
    cleanly (exit 0). *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
Require Import fib_norm_gap.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* Local toolbox: bridges between [Id] and [eq] on Set carriers.        *)
(* ============================================================ *)

(* Prop-level equality to a Set-carried [Id] (exit-side bridge; the
   canonical eq singleton elimination, of the same family as
   [qeq_imp_qeqT] in S02_CauchyComplete: a Prop premise with a
   Set-carried conclusion). *)
Definition zeq_id {A : Set} {a b : A} (h : a = b) : Id a b :=
  match h with
  | eq_refl => id_refl
  end.

(* [Id] witness back to a Prop equality (in-proof bridge: feeds
   rewrite/ring/lia). *)
Definition id_zeq {A : Set} {a b : A} (h : Id a b) : a = b :=
  match h with
  | id_refl => eq_refl
  end.

(* ============================================================ *)
(* Section C. Carrier layer: the dual thread [d41pair]/[e41pair], the   *)
(*   component streams and the positivity layer.                        *)
(* ============================================================ *)

(* X-stream: [(x_{k+1}, y_{k+1}) = N (x_k, y_k)] with N = [[62,25],[5,2]],
   base [(p_0, p_{-1}) = (6, 1)]. *)
Fixpoint d41pair (n : nat) : Z * Z :=
  match n with
  | O => (6%Z, 1%Z)
  | Datatypes.S k => match d41pair k with pair x y => ((62 * x + 25 * y)%Z, (5 * x + 2 * y)%Z) end
  end.

(* Q-stream: same-coefficient 3-step recursion, base [(q_0, q_{-1}) = (1, 0)]. *)
Fixpoint e41pair (n : nat) : Z * Z :=
  match n with
  | O => (1%Z, 0%Z)
  | Datatypes.S k => match e41pair k with pair x y => ((62 * x + 25 * y)%Z, (5 * x + 2 * y)%Z) end
  end.

Definition d41x (n : nat) : Z := fst (d41pair n).
Definition d41y (n : nat) : Z := snd (d41pair n).
Definition d41z (n : nat) : Z := fst (e41pair n).
Definition d41w (n : nat) : Z := snd (e41pair n).

Lemma d41x_0 : Id (d41x 0) 6%Z.
Proof. vm_compute. apply id_refl. Qed.

Lemma d41y_0 : Id (d41y 0) 1%Z.
Proof. vm_compute. apply id_refl. Qed.

Lemma d41z_0 : Id (d41z 0) 1%Z.
Proof. vm_compute. apply id_refl. Qed.

Lemma d41w_0 : Id (d41w 0) 0%Z.
Proof. vm_compute. apply id_refl. Qed.

Lemma d41pair_unfold : forall n : nat,
  Id (d41pair (Datatypes.S n))
     ((62 * fst (d41pair n) + 25 * snd (d41pair n))%Z,
      (5 * fst (d41pair n) + 2 * snd (d41pair n))%Z).
Proof. intro n. cbn [d41pair]. destruct (d41pair n) as [a b]. exact id_refl. Qed.

Lemma e41pair_unfold : forall n : nat,
  Id (e41pair (Datatypes.S n))
     ((62 * fst (e41pair n) + 25 * snd (e41pair n))%Z,
      (5 * fst (e41pair n) + 2 * snd (e41pair n))%Z).
Proof. intro n. cbn [e41pair]. destruct (e41pair n) as [a b]. exact id_refl. Qed.

Lemma d41x_rec : forall n, Id (d41x (Datatypes.S n)) (62 * d41x n + 25 * d41y n)%Z.
Proof. intro n. unfold d41x, d41y. exact (id_cong fst (d41pair_unfold n)). Qed.

Lemma d41y_rec : forall n, Id (d41y (Datatypes.S n)) (5 * d41x n + 2 * d41y n)%Z.
Proof. intro n. unfold d41x, d41y. exact (id_cong snd (d41pair_unfold n)). Qed.

Lemma d41z_rec : forall n, Id (d41z (Datatypes.S n)) (62 * d41z n + 25 * d41w n)%Z.
Proof. intro n. unfold d41z, d41w. exact (id_cong fst (e41pair_unfold n)). Qed.

Lemma d41w_rec : forall n, Id (d41w (Datatypes.S n)) (5 * d41z n + 2 * d41w n)%Z.
Proof. intro n. unfold d41z, d41w. exact (id_cong snd (e41pair_unfold n)). Qed.

(* Positivity layer: all [x]/[y] >= 1; [z] >= 1 and [w] >= 0 with
   [w_{n+1}] >= 1 (guards the Q-denominator position and the [Zpos]
   bridges); stated as [Id (Z.leb _ _) true], the same precedent shape
   as d6_family. *)
Lemma d41xy_ge1 : forall n,
  And (Id (Z.leb 1 (d41x n)) true) (Id (Z.leb 1 (d41y n)) true).
Proof.
  induction n as [|n [IH1 IH2]].
  - split; vm_compute; apply id_refl.
  - split.
    + apply zeq_id. apply (proj2 (Z.leb_le 1 (d41x (Datatypes.S n)))).
      rewrite (id_zeq (d41x_rec n)).
      pose proof (proj1 (Z.leb_le 1 (d41x n)) (id_zeq IH1)).
      pose proof (proj1 (Z.leb_le 1 (d41y n)) (id_zeq IH2)). lia.
    + apply zeq_id. apply (proj2 (Z.leb_le 1 (d41y (Datatypes.S n)))).
      rewrite (id_zeq (d41y_rec n)).
      pose proof (proj1 (Z.leb_le 1 (d41x n)) (id_zeq IH1)).
      pose proof (proj1 (Z.leb_le 1 (d41y n)) (id_zeq IH2)). lia.
Qed.

Lemma d41zw_ge : forall n,
  And (Id (Z.leb 1 (d41z n)) true) (Id (Z.leb 0 (d41w n)) true).
Proof.
  induction n as [|n [IH1 IH2]].
  - split; vm_compute; apply id_refl.
  - split.
    + apply zeq_id. apply (proj2 (Z.leb_le 1 (d41z (Datatypes.S n)))).
      rewrite (id_zeq (d41z_rec n)).
      pose proof (proj1 (Z.leb_le 1 (d41z n)) (id_zeq IH1)).
      pose proof (proj1 (Z.leb_le 0 (d41w n)) (id_zeq IH2)). lia.
    + apply zeq_id. apply (proj2 (Z.leb_le 0 (d41w (Datatypes.S n)))).
      rewrite (id_zeq (d41w_rec n)).
      pose proof (proj1 (Z.leb_le 1 (d41z n)) (id_zeq IH1)).
      pose proof (proj1 (Z.leb_le 0 (d41w n)) (id_zeq IH2)). lia.
Qed.

Lemma d41w_ge1 : forall n, Id (Z.leb 1 (d41w (Datatypes.S n))) true.
Proof.
  intro n. apply zeq_id. rewrite (id_zeq (d41w_rec n)).
  destruct (d41zw_ge n) as [Hz Hw].
  pose proof (proj1 (Z.leb_le 1 (d41z n)) (id_zeq Hz)).
  pose proof (proj1 (Z.leb_le 0 (d41w n)) (id_zeq Hw)). lia.
Qed.

(* ============================================================ *)
(* Section N. Norm layer: the four-invariant block [d41_norm_quad],     *)
(*   [d41_det] and [d41_nonsquare].                                     *)
(* ============================================================ *)

(* Four-invariant induction: S1 (norm of the x-stream, 5 * (+/-1)), S2
   (norm of the y-stream, (+/-1)), C (cross term, 6 * (+/-1)) and G
   (companion term, (+/-1)).  Under the 3-step matrix N:
   S1' = 3844*S1 + 3100*C + 625*S2, S2' = 25*S1 + 20*C + 4*S2,
   C' = 310*S1 + 249*C + 50*S2 and G' = -G; each step is a ring
   decomposition closed by the [powneg1] alternation.  Conjunctions are
   the Set-level [And]; equations are [Id] with the [zeq_id] exit bridge
   (ring/lia stay inside the proofs). *)
Lemma d41_norm_quad : forall n : nat,
  And (Id ((d41x n * d41x n - 41 * (d41z n * d41z n))%Z)
           (5 * powneg1 (Datatypes.S n))%Z)
      (And (Id ((d41y n * d41y n - 41 * (d41w n * d41w n))%Z) (powneg1 n)%Z)
           (And (Id ((d41x n * d41y n - 41 * (d41z n * d41w n))%Z) (6 * powneg1 n)%Z)
                (Id ((d41y n * d41z n - d41x n * d41w n)%Z) (powneg1 n)%Z))).
Proof.
  induction n as [|n [H1 [H2 [H3 H4]]]].
  - split; [| split; [| split]].
    + apply zeq_id. unfold d41x, d41y, d41z, d41w. cbn [d41pair e41pair fst snd powneg1]. ring.
    + apply zeq_id. unfold d41x, d41y, d41z, d41w. cbn [d41pair e41pair fst snd powneg1]. ring.
    + apply zeq_id. unfold d41x, d41y, d41z, d41w. cbn [d41pair e41pair fst snd powneg1]. ring.
    + apply zeq_id. unfold d41x, d41y, d41z, d41w. cbn [d41pair e41pair fst snd powneg1]. ring.
  - split; [| split; [| split]].
    + apply zeq_id. rewrite (id_zeq (d41x_rec n)), (id_zeq (d41z_rec n)),
                (id_zeq (powneg1_S (Datatypes.S n))), (id_zeq (powneg1_S n)).
      transitivity ((3844 * (d41x n * d41x n - 41 * (d41z n * d41z n))
                    + 3100 * (d41x n * d41y n - 41 * (d41z n * d41w n))
                    + 625 * (d41y n * d41y n - 41 * (d41w n * d41w n)))%Z).
      * ring.
      * rewrite (id_zeq H1), (id_zeq H3), (id_zeq H2). rewrite (id_zeq (powneg1_S n)). ring.
    + apply zeq_id. rewrite (id_zeq (d41y_rec n)), (id_zeq (d41w_rec n)).
      transitivity ((25 * (d41x n * d41x n - 41 * (d41z n * d41z n))
                    + 20 * (d41x n * d41y n - 41 * (d41z n * d41w n))
                    + 4 * (d41y n * d41y n - 41 * (d41w n * d41w n)))%Z).
      * ring.
      * rewrite (id_zeq H1), (id_zeq H3), (id_zeq H2). rewrite (id_zeq (powneg1_S n)). ring.
    + apply zeq_id. rewrite (id_zeq (d41x_rec n)), (id_zeq (d41y_rec n)),
                (id_zeq (d41z_rec n)), (id_zeq (d41w_rec n)).
      transitivity ((310 * (d41x n * d41x n - 41 * (d41z n * d41z n))
                    + 249 * (d41x n * d41y n - 41 * (d41z n * d41w n))
                    + 50 * (d41y n * d41y n - 41 * (d41w n * d41w n)))%Z).
      * ring.
      * rewrite (id_zeq H1), (id_zeq H3), (id_zeq H2). rewrite (id_zeq (powneg1_S n)). ring.
    + apply zeq_id. rewrite (id_zeq (d41y_rec n)), (id_zeq (d41z_rec n)),
                (id_zeq (d41x_rec n)), (id_zeq (d41w_rec n)).
      transitivity ((- (d41y n * d41z n - d41x n * d41w n))%Z).
      * ring.
      * rewrite (id_zeq H4). rewrite (id_zeq (powneg1_S n)). reflexivity.
Qed.

(* Main statement 1 (norm of the x-stream, alternating period shape):
   [x^2 - 41 z^2 = 5 * (+/-1)] at the [p_{3k}] positions. *)
Theorem d41_norm_x : forall n : nat,
  Id ((d41x n * d41x n - 41 * (d41z n * d41z n))%Z)
     (5 * powneg1 (Datatypes.S n))%Z.
Proof. intro n. exact (fst (d41_norm_quad n)). Qed.

(* Main statement 2 (norm of the y-stream, the Pell main line):
   [y^2 - 41 w^2 = (+/-1)] at the [p_{3k-1}] positions (the two-family). *)
Theorem d41_norm_y : forall n : nat,
  Id ((d41y n * d41y n - 41 * (d41w n * d41w n))%Z) (powneg1 n)%Z.
Proof. intro n. exact (fst (snd (d41_norm_quad n))). Qed.

(* The integer gap over the y-stream is exactly 1 on the family (the
   [>= 1] lower bound realized exactly by the family). *)
Theorem d41_norm_y_abs1 : forall n : nat,
  Id (Z.abs ((d41y n * d41y n - 41 * (d41w n * d41w n))%Z)) 1%Z.
Proof. intro n. apply zeq_id. rewrite (id_zeq (d41_norm_y n)).
  exact (id_zeq (zabs_powneg1 n)). Qed.

(* Main statement 3 (subfamily determinant): [y_n w_{n+1} - y_{n+1} w_n =
   5 * powneg1 n], the sharpness certificate constant 5. *)
Theorem d41_det : forall n : nat,
  Id ((d41y n * d41w (Datatypes.S n) - d41y (Datatypes.S n) * d41w n)%Z)
     (5 * powneg1 n)%Z.
Proof.
  intro n. apply zeq_id.
  rewrite (id_zeq (d41w_rec n)), (id_zeq (d41y_rec n)).
  transitivity ((5 * (d41y n * d41z n - d41x n * d41w n))%Z).
  - ring.
  - rewrite (id_zeq (snd (snd (snd (d41_norm_quad n))))). reflexivity.
Qed.

(* 41 is not a perfect square (contradiction out of 6^2 < 41 < 7^2);
   provides the nonsquare premise before [q_square_gap] is used. *)
Lemma d41_nonsquare : forall c : Z, (41 <> c * c)%Z.
Proof.
  intro c. intro Hc. exfalso.
  pose proof (Z.abs_square c) as Habs. pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = 41)%Z) by lia.
  assert (Hgt : (6 < Z.abs c)%Z).
  { destruct (Z_lt_le_dec 6 (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============================================================ *)
(* Section Q. Final assembly: the [Zpos] bridges, [d41_member], the     *)
(*   family theorems and the Q-square sharpness.                        *)
(* ============================================================ *)

Definition d41yp (k : nat) : positive :=
  match d41y (Datatypes.S k) with Zpos p => p | _ => 1%positive end.
Definition d41wp (k : nat) : positive :=
  match d41w (Datatypes.S k) with Zpos p => p | _ => 1%positive end.

Lemma d41yp_pos : forall k, Id (Z.pos (d41yp k)) (d41y (Datatypes.S k)).
Proof.
  intro k. unfold d41yp.
  destruct (d41y (Datatypes.S k)) as [|p|p] eqn:E.
  - exfalso. destruct (d41xy_ge1 (Datatypes.S k)) as [_ Hy].
    pose proof (proj1 (Z.leb_le 1 (d41y (Datatypes.S k))) (id_zeq Hy)). lia.
  - apply id_refl.
  - exfalso. destruct (d41xy_ge1 (Datatypes.S k)) as [_ Hy].
    pose proof (proj1 (Z.leb_le 1 (d41y (Datatypes.S k))) (id_zeq Hy)). lia.
Qed.

Lemma d41wp_pos : forall k, Id (Z.pos (d41wp k)) (d41w (Datatypes.S k)).
Proof.
  intro k. unfold d41wp.
  destruct (d41w (Datatypes.S k)) as [|p|p] eqn:E.
  - exfalso. pose proof (proj1 (Z.leb_le 1 (d41w (Datatypes.S k))) (id_zeq (d41w_ge1 k))). lia.
  - apply id_refl.
  - exfalso. pose proof (proj1 (Z.leb_le 1 (d41w (Datatypes.S k))) (id_zeq (d41w_ge1 k))). lia.
Qed.

(* Family member: [p_{3k+2}/q_{3k+2}], the convergent of sqrt(41) at
   index [3k+2] (two-family with [x^2 - 41 y^2 = +/-1]; k = 0 gives 32/5
   of norm -1). *)
Definition d41_member (k : nat) : Q := (Z.pos (d41yp k) # d41wp k)%Q.

(* Family certificate sharpness (main theorem 1): the distance between
   adjacent family members equals 5/(w_{k+1} w_{k+2}) exactly, realized
   by [d41_det] at constant 5 (same shape as d13_family_sharp). *)
Theorem d41_family_sharp : forall k : nat,
  QeqT (Qabs (d41_member k - d41_member (Datatypes.S k)))
       ((Z.pos 5) # (d41wp k * d41wp (Datatypes.S k)))%Q.
Proof.
  intro k.
  assert (Hd : (d41_member k - d41_member (Datatypes.S k))%Q ==
               ((Z.pos (d41yp k) * Z.pos (d41wp (Datatypes.S k))
                 - Z.pos (d41yp (Datatypes.S k)) * Z.pos (d41wp k))
                 # (d41wp k * d41wp (Datatypes.S k)))%Q).
  { unfold d41_member. apply qeqT_imp_qeq. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - rewrite (id_zeq (d41yp_pos k)), (id_zeq (d41yp_pos (Datatypes.S k))).
    assert (Hd2 : (d41y (Datatypes.S k) * Z.pos (d41wp (Datatypes.S k))
                   - d41y (Datatypes.S (Datatypes.S k)) * Z.pos (d41wp k) = 5 * powneg1 (Datatypes.S k))%Z).
    { pose proof (d41_det (Datatypes.S k)) as Hdet.
      rewrite <- (id_zeq (d41wp_pos (Datatypes.S k))), <- (id_zeq (d41wp_pos k)) in Hdet.
      exact (id_zeq Hdet). }
    rewrite Hd2.
    unfold Qeq, Qabs. cbn [Qnum Qden].
    rewrite Z.abs_mul, (id_zeq (zabs_powneg1 (Datatypes.S k))). cbn [Z.abs]. ring.
Qed.

(* Family separation certificate (main theorem 2): every a/b lies at
   distance >= 1/(b w_{k+1}) from the family member (same shape as
   d13_family_sep; the only premise is a nonzero gap). *)
Theorem d41_family_sep : forall (a : Z) (b : positive) (k : nat),
  (a * d41w (Datatypes.S k) - d41y (Datatypes.S k) * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * d41wp k)) # 1))
        (Qabs ((a # b)%Q - d41_member k)).
Proof.
  intros a b k Hk. unfold d41_member.
  assert (Hk2 : (a * Z.pos (d41wp k) - Z.pos (d41yp k) * Z.pos b <> 0)%Z).
  { rewrite (id_zeq (d41wp_pos k)), (id_zeq (d41yp_pos k)). exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (d41wp k) - Z.pos (d41yp k) * Z.pos b)
                  # (b * d41wp k))%Q)
          (Qabs ((a # b)%Q - (Z.pos (d41yp k) # d41wp k)%Q))
          (Qinv ((Z.pos (b * d41wp k)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (d41yp k) # d41wp k)%Q))
                   (Qabs ((a * Z.pos (d41wp k) - Z.pos (d41yp k) * Z.pos b)
                           # (b * d41wp k))%Q)).
    apply qeqT_imp_qeq. apply fib_qabs_congr.
    apply qeqT_imp_qeq. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * d41wp k)%positive).
    exact (proj1 (Z.leb_le 1 (Z.abs (a * Z.pos (d41wp k) - Z.pos (d41yp k) * Z.pos b)))
                 (id_zeq (zabs_ge1 _ Hk2))).
Qed.

(* Q-square sharpness (main theorem 3): [|member^2 - 41| = 1/w^2] exactly;
   the [q_square_gap] lower bound 1/b^2 is attained on the two-family
   (same shape as d13_q_square_sharp). *)
Theorem d41_q_square_sharp : forall k : nat,
  QeqT (Qabs (d41_member k * d41_member k - (41 # 1)%Q))
       (Qinv ((Z.pos (d41wp k * d41wp k)) # 1)).
Proof.
  intro k.
  assert (Hd : (d41_member k * d41_member k - (41 # 1))%Q ==
               ((Z.pos (d41yp k) * Z.pos (d41yp k)
                 - 41 * (Z.pos (d41wp k) * Z.pos (d41wp k)))
                 # (d41wp k * d41wp k))%Q).
  { unfold d41_member. apply qeqT_imp_qeq.
    apply (q_square_cross (Z.pos (d41yp k)) 41 (d41wp k)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - rewrite (id_zeq (d41yp_pos k)).
    assert (Hn2 : (d41y (Datatypes.S k) * d41y (Datatypes.S k)
                   - 41 * (Z.pos (d41wp k) * Z.pos (d41wp k)) = powneg1 (Datatypes.S k))%Z).
    { pose proof (d41_norm_y (Datatypes.S k)) as Hn.
      rewrite <- (id_zeq (d41wp_pos k)) in Hn. exact (id_zeq Hn). }
    rewrite Hn2.
    destruct (powneg1 (Datatypes.S k)) as [|p|p] eqn:E.
    + exfalso. pose proof (id_zeq (zabs_powneg1 (Datatypes.S k))) as Hz. rewrite E in Hz. cbn in Hz. discriminate.
    + pose proof (id_zeq (zabs_powneg1 (Datatypes.S k))) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.pos 1 # d41wp k * d41wp k)) with (Z.pos 1 # d41wp k * d41wp k)%Q.
      change (Qinv (Z.pos (d41wp k * d41wp k) # 1)) with (1 # d41wp k * d41wp k)%Q.
      apply Qeq_refl.
    + pose proof (id_zeq (zabs_powneg1 (Datatypes.S k))) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz. subst p.
      change (Qabs (Z.neg 1 # d41wp k * d41wp k)) with (Z.pos 1 # d41wp k * d41wp k)%Q.
      change (Qinv (Z.pos (d41wp k * d41wp k) # 1)) with (1 # d41wp k * d41wp k)%Q.
      apply Qeq_refl.
Qed.

(* Instance use of [q_square_gap] (the main statement instantiated on the
   D = 41 family; together with the sharpness theorem this says the lower
   bound is attained exactly). *)
Lemma d41_q_square_gap_instance : forall k : nat,
  QleT' (Qinv ((Z.pos (d41wp k * d41wp k)) # 1))
        (Qabs (d41_member k * d41_member k - (41 # 1)%Q)).
Proof.
  intro k. unfold d41_member.
  apply (q_square_gap 41 (Z.pos (d41yp k)) (d41wp k)).
  - cbn. lia.
  - intro c. apply (d41_nonsquare c).
Qed.

(* ============================================================ *)
(* Section A. Audit: [Print Assumptions], [Separate Extraction], and    *)
(*   [vm_compute] numerical anchors.                                    *)
(* ============================================================ *)

Print Assumptions d41x_rec.
Print Assumptions d41y_rec.
Print Assumptions d41z_rec.
Print Assumptions d41w_rec.
Print Assumptions d41xy_ge1.
Print Assumptions d41zw_ge.
Print Assumptions d41w_ge1.
Print Assumptions d41_norm_quad.
Print Assumptions d41_norm_x.
Print Assumptions d41_norm_y.
Print Assumptions d41_norm_y_abs1.
Print Assumptions d41_det.
Print Assumptions d41_nonsquare.
Print Assumptions d41yp_pos.
Print Assumptions d41wp_pos.
Print Assumptions d41_family_sep.
Print Assumptions d41_family_sharp.
Print Assumptions d41_q_square_sharp.
Print Assumptions d41_q_square_gap_instance.

(* Numerical anchor 1 (family member, negative side): member 0 = p_2/q_2 =
   32/5 (norm [x^2 - 41 y^2 = -1]). *)
Lemma smoke_member_32_5 : Id (Qeq_bool (d41_member 0) (32 # 5)%Q) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 2 (family member, positive side): member 1 = p_5/q_5 =
   2049/320 (norm [x^2 - 41 y^2 = +1]). *)
Lemma smoke_member_2049_320 : Id (Qeq_bool (d41_member 1) (2049 # 320)%Q) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 3 (norm layer): |32^2 - 41*5^2| = 1 (instance of
   [d41_norm_y_abs1]; two-family alternation anchor). *)
Lemma smoke_norm_1 : Id (Z.eqb (Z.abs (d41y 1 * d41y 1 - 41 * (d41w 1 * d41w 1))) 1%Z) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 4 (sharpness layer): |32/5 - 2049/320| = 1/320 =
   5/(5*320) exactly (instance of [d41_family_sharp]). *)
Lemma smoke_sharp_1_320 :
  Id (Qeq_bool (Qabs (d41_member 0 - d41_member 1))
               ((Z.pos 5) # (d41wp 0 * d41wp 1))%Q) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 5 (Q-square sharpness): |(32/5)^2 - 41| = 1/25
   (instance of [d41_q_square_sharp]). *)
Lemma smoke_qsq_1_25 :
  Id (Qeq_bool (Qabs (d41_member 0 * d41_member 0 - (41 # 1)%Q))
           (Qinv ((Z.pos (d41wp 0 * d41wp 0)) # 1))) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor 6 (matrix step): x_1 = 397 and z_1 = 62 (carrier
   values of p_3/q_3). *)
Lemma smoke_step_397_62 :
  Id (Z.eqb (d41x 1) 397%Z, Z.eqb (d41z 1) 62%Z) (true, true).
Proof. vm_compute. apply id_refl. Qed.

Print Assumptions smoke_member_32_5.
Print Assumptions smoke_member_2049_320.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_320.
Print Assumptions smoke_qsq_1_25.
Print Assumptions smoke_step_397_62.

From Stdlib Require Import Extraction.
Separate Extraction d41pair e41pair d41x d41y d41z d41w d41yp d41wp
  d41_member d41_norm_y_abs1 d41_det d41_family_sep d41_family_sharp
  d41_q_square_sharp d41_q_square_gap_instance
  smoke_member_32_5 smoke_member_2049_320 smoke_norm_1 smoke_sharp_1_320
  smoke_qsq_1_25 smoke_step_397_62.
