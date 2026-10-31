(* ConstructiveWorld-Set — period-2 convergent subfamily modules. *)

(** * d6_family: the period-2 convergent subfamily of [sqrt 6].

    Mission.  [sqrt 6] = [2; 2, 4, ...] has period 2, so the two-step
      block [N = [[9; 2]; [4; 1]]] (determinant +1) advances both
      streams with constant coefficients: [d6pair]/[e6pair] carry
      [(x k, y k) = (p (2k+1), p (2k))] and
      [(z k, w k) = (q (2k+1), q (2k))], stepped by [(9x + 2y, 4x + y)].
      [d6_norm_quad]: the invariants [x^2 - 6 z^2 = 1],
      [y^2 - 6 w^2 = -2], [x y - 6 z w = -2], [y z - x w = -1];
      [d6_det] = [2].  Main statements: [d6_member], [d6_family_sharp],
      [d6_family_sep], [d6_q_square_sharp], [d6_q_square_gap_instance].

    Dependencies.  Stdlib [ZArith.ZArith], [Arith.Arith], [Bool.Bool],
      [Lia], [QArith.QArith], [QArith.Qabs]; this development's
      [S01_BaseRing], [S02_CauchyComplete], [fib_machine], [fib_qdomain],
      [pell_family] — shared rational lemmas consumed without reproof, as in [d3_family].

    References.  This development; statement names carry over verbatim
      from the ConstructiveWorld-Main baseline [d6_family.v]
      (statement-face Set-carrier completion); cf. [d13_family].

    Constructivity.  All named statements are [Set]-carried ([QeqT],
      [QleT'], [Id], [And]); proofs may reason constructively in [Prop]
      internally, bridged to the [Set] carriers at statement exits by
      [zeq_id]/[id_zeq].  Definitions are transparent.

    Build.  [rocq c -native-compiler no -q -Q . "" d6_family.v] compiles
      cleanly (exit 0); every [Print Assumptions] reports [Closed]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
Require Import pell_family.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ================= Section 1. Equality bridges between Id and eq ================= *)

(* An [eq] proof to a [Set]-carried [Id] witness (the canonical [eq]
   singleton-elimination shape, as in [qeq_imp_qeqT] of
   [S02_CauchyComplete]: the premise lives in [Prop], the conclusion is
   [Set]-carried). *)
Definition zeq_id {A : Set} {a b : A} (h : a = b) : Id a b :=
  match h with
  | eq_refl => id_refl
  end.

(* An [Id] witness back to an [eq] proof (consumed by [rewrite], [ring]
   and [lia] inside proofs). *)
Definition id_zeq {A : Set} {a b : A} (h : Id a b) : a = b :=
  match h with
  | id_refl => eq_refl
  end.

(* ============ Section 2. Carrier layer: the two streams, their unfoldings, positivity ============ *)

(* The x stream: [(x_{k+1}, y_{k+1}) = N (x_k, y_k)] with
   [N = [[9; 2]; [4; 1]]]; base [(p_1, p_0) = (5, 2)]. *)
Fixpoint d6pair (n : nat) : Z * Z :=
  match n with
  | O => (5%Z, 2%Z)
  | Datatypes.S k => match d6pair k with pair x y => ((9 * x + 2 * y)%Z, (4 * x + y)%Z) end
  end.

(* The q stream: the same two-step recursion; base [(q_1, q_0) = (2, 1)]. *)
Fixpoint e6pair (n : nat) : Z * Z :=
  match n with
  | O => (2%Z, 1%Z)
  | Datatypes.S k => match e6pair k with pair x y => ((9 * x + 2 * y)%Z, (4 * x + y)%Z) end
  end.

Definition d6x (n : nat) : Z := fst (d6pair n).
Definition d6y (n : nat) : Z := snd (d6pair n).
Definition d6z (n : nat) : Z := fst (e6pair n).
Definition d6w (n : nat) : Z := snd (e6pair n).

Lemma d6x_0 : Id (d6x 0) 5%Z.
Proof. vm_compute. apply id_refl. Qed.

Lemma d6y_0 : Id (d6y 0) 2%Z.
Proof. vm_compute. apply id_refl. Qed.

Lemma d6z_0 : Id (d6z 0) 2%Z.
Proof. vm_compute. apply id_refl. Qed.

Lemma d6w_0 : Id (d6w 0) 1%Z.
Proof. vm_compute. apply id_refl. Qed.

Lemma d6pair_unfold : forall n : nat,
  Id (d6pair (Datatypes.S n))
     ((9 * fst (d6pair n) + 2 * snd (d6pair n))%Z,
      (4 * fst (d6pair n) + snd (d6pair n))%Z).
Proof. intro n. cbn [d6pair]. destruct (d6pair n) as [a b]. exact id_refl. Qed.

Lemma e6pair_unfold : forall n : nat,
  Id (e6pair (Datatypes.S n))
     ((9 * fst (e6pair n) + 2 * snd (e6pair n))%Z,
      (4 * fst (e6pair n) + snd (e6pair n))%Z).
Proof. intro n. cbn [e6pair]. destruct (e6pair n) as [a b]. exact id_refl. Qed.

Lemma d6x_rec : forall n, Id (d6x (Datatypes.S n)) (9 * d6x n + 2 * d6y n)%Z.
Proof. intro n. unfold d6x, d6y. exact (id_cong fst (d6pair_unfold n)). Qed.

Lemma d6y_rec : forall n, Id (d6y (Datatypes.S n)) (4 * d6x n + d6y n)%Z.
Proof. intro n. unfold d6x, d6y. exact (id_cong snd (d6pair_unfold n)). Qed.

Lemma d6z_rec : forall n, Id (d6z (Datatypes.S n)) (9 * d6z n + 2 * d6w n)%Z.
Proof. intro n. unfold d6z, d6w. exact (id_cong fst (e6pair_unfold n)). Qed.

Lemma d6w_rec : forall n, Id (d6w (Datatypes.S n)) (4 * d6z n + d6w n)%Z.
Proof. intro n. unfold d6z, d6w. exact (id_cong snd (e6pair_unfold n)). Qed.

(* Positivity layer: the x/y streams stay [>= 1]; z stays [>= 1] and
   w stays [>= 0] — guards for the Q-denominator positions and the
   [Zpos] bridge.  Each [Z.leb] statement is carried as
   [Id (Z.leb b _) true]. *)
Lemma d6xy_ge1 : forall n,
  And (Id (Z.leb 1 (d6x n)) true) (Id (Z.leb 1 (d6y n)) true).
Proof.
  induction n as [|n [IH1 IH2]].
  - split; vm_compute; apply id_refl.
  - split.
    + apply zeq_id. apply (proj2 (Z.leb_le 1 (d6x (Datatypes.S n)))).
      rewrite (id_zeq (d6x_rec n)).
      pose proof (proj1 (Z.leb_le 1 (d6x n)) (id_zeq IH1)).
      pose proof (proj1 (Z.leb_le 1 (d6y n)) (id_zeq IH2)). lia.
    + apply zeq_id. apply (proj2 (Z.leb_le 1 (d6y (Datatypes.S n)))).
      rewrite (id_zeq (d6y_rec n)).
      pose proof (proj1 (Z.leb_le 1 (d6x n)) (id_zeq IH1)).
      pose proof (proj1 (Z.leb_le 1 (d6y n)) (id_zeq IH2)). lia.
Qed.

Lemma d6zw_ge : forall n,
  And (Id (Z.leb 1 (d6z n)) true) (Id (Z.leb 0 (d6w n)) true).
Proof.
  induction n as [|n [IH1 IH2]].
  - split; vm_compute; apply id_refl.
  - split.
    + apply zeq_id. apply (proj2 (Z.leb_le 1 (d6z (Datatypes.S n)))).
      rewrite (id_zeq (d6z_rec n)).
      pose proof (proj1 (Z.leb_le 1 (d6z n)) (id_zeq IH1)).
      pose proof (proj1 (Z.leb_le 0 (d6w n)) (id_zeq IH2)). lia.
    + apply zeq_id. apply (proj2 (Z.leb_le 0 (d6w (Datatypes.S n)))).
      rewrite (id_zeq (d6w_rec n)).
      pose proof (proj1 (Z.leb_le 1 (d6z n)) (id_zeq IH1)).
      pose proof (proj1 (Z.leb_le 0 (d6w n)) (id_zeq IH2)). lia.
Qed.

(* ============ Section 3. Norm layer: the four invariants, the determinant, 6 not a square ============ *)

(* The four invariants are constant along the subfamily: the base case
   closes by [ring] on [(5, 2)], [(2, 1)]; the step identities decompose
   as S1' = 81 S1 + 36 C + 4 S2, S2' = 16 S1 + 8 C + S2,
   C' = 36 S1 + 17 C + 2 S2, G' = G.  Conjunctions are carried by the
   [Set]-level [And]; equations by [Id], with [ring]/[lia] acting inside
   the proofs behind the [zeq_id] exit bridge. *)
Lemma d6_norm_quad : forall n : nat,
  And (Id ((d6x n * d6x n - 6 * (d6z n * d6z n))%Z) 1%Z)
      (And (Id ((d6y n * d6y n - 6 * (d6w n * d6w n))%Z) (-2)%Z)
           (And (Id ((d6x n * d6y n - 6 * (d6z n * d6w n))%Z) (-2)%Z)
                (Id ((d6y n * d6z n - d6x n * d6w n)%Z) (-1)%Z))).
Proof.
  induction n as [|n [H1 [H2 [H3 H4]]]].
  - split; [| split; [| split]].
    + apply zeq_id. unfold d6x, d6y, d6z, d6w. cbn [d6pair e6pair fst snd]. ring.
    + apply zeq_id. unfold d6x, d6y, d6z, d6w. cbn [d6pair e6pair fst snd]. ring.
    + apply zeq_id. unfold d6x, d6y, d6z, d6w. cbn [d6pair e6pair fst snd]. ring.
    + apply zeq_id. unfold d6x, d6y, d6z, d6w. cbn [d6pair e6pair fst snd]. ring.
  - split; [| split; [| split]].
    + apply zeq_id. rewrite (id_zeq (d6x_rec n)), (id_zeq (d6z_rec n)).
      transitivity ((81 * (d6x n * d6x n - 6 * (d6z n * d6z n))
                    + 36 * (d6x n * d6y n - 6 * (d6z n * d6w n))
                    + 4 * (d6y n * d6y n - 6 * (d6w n * d6w n)))%Z).
      * ring.
      * rewrite (id_zeq H1), (id_zeq H3), (id_zeq H2). ring.
    + apply zeq_id. rewrite (id_zeq (d6y_rec n)), (id_zeq (d6w_rec n)).
      transitivity ((16 * (d6x n * d6x n - 6 * (d6z n * d6z n))
                    + 8 * (d6x n * d6y n - 6 * (d6z n * d6w n))
                    + (d6y n * d6y n - 6 * (d6w n * d6w n)))%Z).
      * ring.
      * rewrite (id_zeq H1), (id_zeq H3), (id_zeq H2). ring.
    + apply zeq_id.
      rewrite (id_zeq (d6x_rec n)), (id_zeq (d6y_rec n)),
              (id_zeq (d6z_rec n)), (id_zeq (d6w_rec n)).
      transitivity ((36 * (d6x n * d6x n - 6 * (d6z n * d6z n))
                    + 17 * (d6x n * d6y n - 6 * (d6z n * d6w n))
                    + 2 * (d6y n * d6y n - 6 * (d6w n * d6w n)))%Z).
      * ring.
      * rewrite (id_zeq H1), (id_zeq H3), (id_zeq H2). ring.
    + apply zeq_id.
      rewrite (id_zeq (d6y_rec n)), (id_zeq (d6z_rec n)),
              (id_zeq (d6x_rec n)), (id_zeq (d6w_rec n)).
      transitivity ((d6y n * d6z n - d6x n * d6w n)%Z).
      * ring.
      * exact (id_zeq H4).
Qed.

(* Main statement one (member-stream norm): [x^2 - 6 z^2 = 1], the +1
   subfamily. *)
Theorem d6_norm_x : forall n : nat,
  Id ((d6x n * d6x n - 6 * (d6z n * d6z n))%Z) 1%Z.
Proof. intro n. exact (fst (d6_norm_quad n)). Qed.

(* Main statement two (companion-stream norm): [y^2 - 6 w^2 = -2]. *)
Theorem d6_norm_y : forall n : nat,
  Id ((d6y n * d6y n - 6 * (d6w n * d6w n))%Z) (-2)%Z.
Proof. intro n. exact (fst (snd (d6_norm_quad n))). Qed.

(* The integral gap on the family is exactly 2 (companion stream). *)
Theorem d6_norm_y_abs2 : forall n : nat,
  Id (Z.abs ((d6y n * d6y n - 6 * (d6w n * d6w n))%Z)) 2%Z.
Proof. intro n. rewrite (id_zeq (d6_norm_y n)). exact id_refl. Qed.

(* Main statement three (subfamily determinant):
   [x_n z_{n+1} - x_{n+1} z_n = 2] — the constant 2 behind the
   sharpness certificate of the family. *)
Theorem d6_det : forall n : nat,
  Id ((d6x n * d6z (Datatypes.S n) - d6x (Datatypes.S n) * d6z n)%Z) 2%Z.
Proof.
  intro n. apply zeq_id.
  rewrite (id_zeq (d6z_rec n)), (id_zeq (d6x_rec n)).
  transitivity ((- (2 * (d6y n * d6z n - d6x n * d6w n)))%Z).
  - ring.
  - rewrite (id_zeq (snd (snd (snd (d6_norm_quad n))))). reflexivity.
Qed.

(* 6 is not a perfect square ([2^2 < 6 < 3^2], contradiction) — supplied
   ahead of its use in [q_square_gap]. *)
Lemma d6_nonsquare : forall c : Z, (6 <> c * c)%Z.
Proof.
  intro c. intro Hc. exfalso.
  pose proof (Z.abs_square c) as Habs. pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = 6)%Z) by lia.
  assert (Hgt : (2 < Z.abs c)%Z).
  { destruct (Z_lt_le_dec 2 (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============ Section 4. Rational assembly layer: the Zpos bridge, family members, sharpness and separation ============ *)

Definition d6yp (k : nat) : positive := Zpos_of (d6x k).
Definition d6wp (k : nat) : positive := Zpos_of (d6z k).

Lemma d6yp_pos : forall k, Id (Z.pos (d6yp k)) (d6x k).
Proof.
  intro k. unfold d6yp. apply Zpos_of_pos.
  destruct (d6xy_ge1 k) as [Hx _].
  pose proof (proj1 (Z.leb_le 1 (d6x k)) (id_zeq Hx)). lia.
Qed.

Lemma d6wp_pos : forall k, Id (Z.pos (d6wp k)) (d6z k).
Proof.
  intro k. unfold d6wp. apply Zpos_of_pos.
  destruct (d6zw_ge k) as [Hz _].
  pose proof (proj1 (Z.leb_le 1 (d6z k)) (id_zeq Hz)). lia.
Qed.

(* Family member: [p_{2k+1} / q_{2k+1}], the (2k+1)-th convergent of
   [sqrt 6] (the +1 subfamily; [k = 0] gives [5/2]). *)
Definition d6_member (k : nat) : Q := (Z.pos (d6yp k) # d6wp k)%Q.

(* Sharpness of the family certificate: the distance of neighboring
   members equals [2 / (z_k z_{k+1})] with exact equality — the constant
   2 of [d6_det] attained (isomorphic to [d13_family_sharp], with the
   endpoint constant 2 in place of 5). *)
Theorem d6_family_sharp : forall k : nat,
  QeqT (Qabs (d6_member k - d6_member (Datatypes.S k)))
       ((Z.pos 2) # (d6wp k * d6wp (Datatypes.S k)))%Q.
Proof.
  intro k.
  assert (Hd : (d6_member k - d6_member (Datatypes.S k))%Q ==
               ((Z.pos (d6yp k) * Z.pos (d6wp (Datatypes.S k))
                 - Z.pos (d6yp (Datatypes.S k)) * Z.pos (d6wp k))
                 # (d6wp k * d6wp (Datatypes.S k)))%Q).
  { unfold d6_member. apply qeqT_imp_qeq. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - rewrite (id_zeq (d6yp_pos k)), (id_zeq (d6yp_pos (Datatypes.S k))).
    assert (Hd2 : (d6x k * Z.pos (d6wp (Datatypes.S k))
                   - d6x (Datatypes.S k) * Z.pos (d6wp k) = 2)%Z).
    { pose proof (d6_det k) as Hdet.
      rewrite <- (id_zeq (d6wp_pos (Datatypes.S k))), <- (id_zeq (d6wp_pos k)) in Hdet.
      exact (id_zeq Hdet). }
    rewrite Hd2.
    unfold Qeq, Qabs. cbn [Qnum Qden Z.abs]. reflexivity.
Qed.

(* Separation certificate: the distance from any [a/b] to the family
   member is at least [1 / (b z_k)] (isomorphic to [d13_family_sep];
   the sole premise is [gap <> 0]). *)
Theorem d6_family_sep : forall (a : Z) (b : positive) (k : nat),
  (a * d6z k - d6x k * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * d6wp k)) # 1))
        (Qabs ((a # b)%Q - d6_member k)).
Proof.
  intros a b k Hk. unfold d6_member.
  assert (Hk2 : (a * Z.pos (d6wp k) - Z.pos (d6yp k) * Z.pos b <> 0)%Z).
  { rewrite (id_zeq (d6wp_pos k)), (id_zeq (d6yp_pos k)). exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (d6wp k) - Z.pos (d6yp k) * Z.pos b)
                  # (b * d6wp k))%Q)
          (Qabs ((a # b)%Q - (Z.pos (d6yp k) # d6wp k)%Q))
          (Qinv ((Z.pos (b * d6wp k)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (d6yp k) # d6wp k)%Q))
                   (Qabs ((a * Z.pos (d6wp k) - Z.pos (d6yp k) * Z.pos b)
                           # (b * d6wp k))%Q)).
    apply qeqT_imp_qeq. apply fib_qabs_congr. apply qeqT_imp_qeq. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * d6wp k)%positive).
    pose proof (zabs_ge1 (a * Z.pos (d6wp k) - Z.pos (d6yp k) * Z.pos b) Hk2) as Hz.
    apply Z.leb_le.
    exact (match Hz in (Id _ y)
             return (Z.leb 1 (Z.abs (a * Z.pos (d6wp k) - Z.pos (d6yp k) * Z.pos b)) = y)
           with id_refl => eq_refl end).
Qed.

(* Rational square sharpness: [|member^2 - 6| = 1/z^2] with exact
   equality — the [q_square_gap] lower bound [1/b^2] is attained on the
   +1 subfamily (constant norm 1; no alternating-sign case analysis). *)
Theorem d6_q_square_sharp : forall k : nat,
  QeqT (Qabs (d6_member k * d6_member k - (6 # 1)%Q))
       (Qinv ((Z.pos (d6wp k * d6wp k)) # 1)).
Proof.
  intro k.
  assert (Hd : (d6_member k * d6_member k - (6 # 1))%Q ==
               ((Z.pos (d6yp k) * Z.pos (d6yp k)
                 - 6 * (Z.pos (d6wp k) * Z.pos (d6wp k)))
                 # (d6wp k * d6wp k))%Q).
  { unfold d6_member. apply qeqT_imp_qeq. apply (q_square_cross (Z.pos (d6yp k)) 6 (d6wp k)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - rewrite (id_zeq (d6yp_pos k)).
    assert (Hn2 : (d6x k * d6x k
                   - 6 * (Z.pos (d6wp k) * Z.pos (d6wp k)) = 1)%Z).
    { pose proof (d6_norm_x k) as Hn.
      rewrite <- (id_zeq (d6wp_pos k)) in Hn.
      exact (id_zeq Hn). }
    rewrite Hn2.
    change (Qabs (Z.pos 1 # d6wp k * d6wp k)) with (Z.pos 1 # d6wp k * d6wp k)%Q.
    change (Qinv (Z.pos (d6wp k * d6wp k) # 1)) with (1 # d6wp k * d6wp k)%Q.
    apply Qeq_refl.
Qed.

(* Instance of [q_square_gap] on the D = 6 family; taken together with
   the sharpness above, the lower bound is exactly attained. *)
Lemma d6_q_square_gap_instance : forall k : nat,
  QleT' (Qinv ((Z.pos (d6wp k * d6wp k)) # 1))
        (Qabs (d6_member k * d6_member k - (6 # 1)%Q)).
Proof.
  intro k. unfold d6_member.
  apply (q_square_gap 6 (Z.pos (d6yp k)) (d6wp k)).
  - cbn. lia.
  - intro c. apply (d6_nonsquare c).
Qed.

(* ============ Section 5. Audit: assumption census and numerical anchors ============ *)

Print Assumptions d6x_rec.
Print Assumptions d6y_rec.
Print Assumptions d6z_rec.
Print Assumptions d6w_rec.
Print Assumptions d6xy_ge1.
Print Assumptions d6zw_ge.
Print Assumptions d6_norm_quad.
Print Assumptions d6_norm_x.
Print Assumptions d6_norm_y.
Print Assumptions d6_norm_y_abs2.
Print Assumptions d6_det.
Print Assumptions d6_nonsquare.
Print Assumptions Zpos_of_pos.
Print Assumptions d6yp_pos.
Print Assumptions d6wp_pos.
Print Assumptions d6_family_sep.
Print Assumptions d6_family_sharp.
Print Assumptions d6_q_square_sharp.
Print Assumptions d6_q_square_gap_instance.

(* Numerical anchor one (family member): [member 0 = p_1 / q_1 = 5/2]
   (norm +1). *)
Lemma smoke_member_5_2 : Id (Qeq_bool (d6_member 0) (5 # 2)%Q) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor two (family member): [member 1 = p_3 / q_3 = 49/20]
   (norm +1). *)
Lemma smoke_member_49_20 : Id (Qeq_bool (d6_member 1) (49 # 20)%Q) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor three (norm layer): [|49^2 - 6*20^2| = 1]
   (instance of [d6_norm_x]). *)
Lemma smoke_norm_1 : Id (Z.eqb (Z.abs (d6x 1 * d6x 1 - 6 * (d6z 1 * d6z 1))) 1%Z) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor four (sharpness): [|5/2 - 49/20| = 1/20 = 2/(2*20)]
   with exact equality (instance of [d6_family_sharp]). *)
Lemma smoke_sharp_1_20 :
  Id (Qeq_bool (Qabs (d6_member 0 - d6_member 1))
                ((Z.pos 2) # (d6wp 0 * d6wp 1))%Q) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor five (rational square sharpness):
   [|(5/2)^2 - 6| = 1/4] (instance of [d6_q_square_sharp]). *)
Lemma smoke_qsq_1_4 :
  Id (Qeq_bool (Qabs (d6_member 0 * d6_member 0 - (6 # 1)%Q))
             (Qinv ((Z.pos (d6wp 0 * d6wp 0)) # 1))) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numerical anchor six (matrix step): [x_1 = 49], [z_1 = 20] (the
   carrier values behind [p_3 / q_3]). *)
Lemma smoke_step_49_20 :
  Id (Z.eqb (d6x 1) 49%Z, Z.eqb (d6z 1) 20%Z) (true, true).
Proof. vm_compute. apply id_refl. Qed.

Print Assumptions smoke_member_5_2.
Print Assumptions smoke_member_49_20.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_20.
Print Assumptions smoke_qsq_1_4.
Print Assumptions smoke_step_49_20.

From Stdlib Require Import Extraction.
Separate Extraction d6pair e6pair d6x d6y d6z d6w d6yp d6wp
  d6_member d6_norm_y_abs2 d6_det d6_family_sep d6_family_sharp
  d6_q_square_sharp d6_q_square_gap_instance
  smoke_member_5_2 smoke_member_49_20 smoke_norm_1 smoke_sharp_1_20
  smoke_qsq_1_4 smoke_step_49_20.
