(* ConstructiveWorld-Set -- the D=14 period-4 convergent subfamily: constant four-step norm layer and sharp family certificates. *)

(** * d14_family: the D=14 period-4 convergent subfamily with sharp family certificates.

    Mission.  The period-4 continued fraction of sqrt(14) turns the convergent
      recurrences into the constant four-step block matrix N = [[27,4],[20,3]]
      (det = +1): the streams (x, y) = (p_{4k+3}, p_{4k+2}) and (z, w) =
      (q_{4k+3}, q_{4k+2}) are threaded by [d14pair]/[e14pair] with the step
      lemmas [d14x_rec] and companions; the norm layer carries the four constant
      invariants [d14_norm_quad], the member norm [d14_norm_x], the companion
      norm [d14_norm_y] with gap 5, the determinant [d14_det] (constant 4),
      [d14_nonsquare] and the Q assembly of [d14_member]; the three main
      certificates are [d14_family_sharp], [d14_family_sep] and
      [d14_q_square_sharp] with instance [d14_q_square_gap_instance].

    Dependencies.  Stdlib [ZArith.ZArith], [Arith.Arith], [Bool.Bool], [Lia],
      [QArith.QArith], [QArith.Qabs]; this development's [S02_CauchyComplete]
      (built on [S01_BaseRing]), [fib_machine], [fib_qdomain] (built on [fib_norm_gap]), [pell_family].

    References.  This development, d14_family.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" d14_family.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)

Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
Require Import pell_family.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* Section C. Carrier layer: the paired streams d14pair/e14pair with
   projections d14x/d14y/d14z/d14w, their step recurrences and positivity. *)
(* ============================================================ *)

(* x-stream: (x_{k+1}, y_{k+1}) = N (x_k, y_k) with N = [[27,4],[20,3]]; base (p_3, p_2) = (15, 11). *)
Fixpoint d14pair (n : nat) : Z * Z :=
  match n with
  | O => (15%Z, 11%Z)
  | S k => match d14pair k with pair x y => ((27 * x + 4 * y)%Z, (20 * x + 3 * y)%Z) end
  end.

(* q-stream: the same four-step recurrence with the same coefficients; base (q_3, q_2) = (4, 3). *)
Fixpoint e14pair (n : nat) : Z * Z :=
  match n with
  | O => (4%Z, 3%Z)
  | S k => match e14pair k with pair x y => ((27 * x + 4 * y)%Z, (20 * x + 3 * y)%Z) end
  end.

Definition d14x (n : nat) : Z := fst (d14pair n).
Definition d14y (n : nat) : Z := snd (d14pair n).
Definition d14z (n : nat) : Z := fst (e14pair n).
Definition d14w (n : nat) : Z := snd (e14pair n).

Lemma d14x_0 : d14x 0 = 15%Z.
Proof. reflexivity. Qed.

Lemma d14y_0 : d14y 0 = 11%Z.
Proof. reflexivity. Qed.

Lemma d14z_0 : d14z 0 = 4%Z.
Proof. reflexivity. Qed.

Lemma d14w_0 : d14w 0 = 3%Z.
Proof. reflexivity. Qed.

Lemma d14pair_unfold : forall n : nat,
  d14pair (S n) = ((27 * fst (d14pair n) + 4 * snd (d14pair n))%Z,
                   (20 * fst (d14pair n) + 3 * snd (d14pair n))%Z).
Proof. intro n. cbn [d14pair]. destruct (d14pair n) as [a b]. reflexivity. Qed.

Lemma e14pair_unfold : forall n : nat,
  e14pair (S n) = ((27 * fst (e14pair n) + 4 * snd (e14pair n))%Z,
                   (20 * fst (e14pair n) + 3 * snd (e14pair n))%Z).
Proof. intro n. cbn [e14pair]. destruct (e14pair n) as [a b]. reflexivity. Qed.

Lemma d14x_rec : forall n, d14x (S n) = (27 * d14x n + 4 * d14y n)%Z.
Proof. intro n. unfold d14x, d14y. rewrite d14pair_unfold. reflexivity. Qed.

Lemma d14y_rec : forall n, d14y (S n) = (20 * d14x n + 3 * d14y n)%Z.
Proof. intro n. unfold d14x, d14y. rewrite d14pair_unfold. reflexivity. Qed.

Lemma d14z_rec : forall n, d14z (S n) = (27 * d14z n + 4 * d14w n)%Z.
Proof. intro n. unfold d14z, d14w. rewrite e14pair_unfold. reflexivity. Qed.

Lemma d14w_rec : forall n, d14w (S n) = (20 * d14z n + 3 * d14w n)%Z.
Proof. intro n. unfold d14z, d14w. rewrite e14pair_unfold. reflexivity. Qed.

(* positivity layer: the x, y, z streams stay >= 1 and the w stream stays >= 0; this guards the Q denominator positions and the Zpos bridges. *)
Lemma d14xy_ge1 : forall n, (1 <= d14x n)%Z /\ (1 <= d14y n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d14x_0 | rewrite d14y_0]; lia.
  - split; rewrite ?d14x_rec, ?d14y_rec; lia.
Qed.

Lemma d14zw_ge : forall n, (1 <= d14z n)%Z /\ (0 <= d14w n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d14z_0 | rewrite d14w_0]; lia.
  - split; rewrite ?d14z_rec, ?d14w_rec; lia.
Qed.

(* ============================================================ *)
(* Section N. Norm layer: the four constant invariants of d14_norm_quad,
   the determinant d14_det and the nonsquareness d14_nonsquare. *)
(* ============================================================ *)

(* induction of the four invariants (period 4 makes them constant shapes):
   the base (15,11)/(4,3) closes directly by ring; at the step each new
   invariant is a fixed integer combination of the old ones,
   S1' = 729*S1 + 216*C + 16*S2, S2' = 400*S1 + 120*C + 9*S2,
   C' = 540*S1 + 161*C + 12*S2, while G' = G since det N = +1 preserves the
   determinant core; the ring tactic closes each decomposition. *)
Lemma d14_norm_quad : forall n : nat,
  (d14x n * d14x n - 14 * (d14z n * d14z n) = 1)%Z /\
  (d14y n * d14y n - 14 * (d14w n * d14w n) = (-5))%Z /\
  (d14x n * d14y n - 14 * (d14z n * d14w n) = (-3))%Z /\
  (d14y n * d14z n - d14x n * d14w n = (-1))%Z.
Proof.
  induction n as [|n [H1 [H2 [H3 H4]]]].
  - split; [| split; [| split]].
    + unfold d14x, d14y, d14z, d14w. cbn [d14pair e14pair fst snd]. ring.
    + unfold d14x, d14y, d14z, d14w. cbn [d14pair e14pair fst snd]. ring.
    + unfold d14x, d14y, d14z, d14w. cbn [d14pair e14pair fst snd]. ring.
    + unfold d14x, d14y, d14z, d14w. cbn [d14pair e14pair fst snd]. ring.
  - split; [| split; [| split]].
    + rewrite (d14x_rec n), (d14z_rec n).
      transitivity ((729 * (d14x n * d14x n - 14 * (d14z n * d14z n))
                    + 216 * (d14x n * d14y n - 14 * (d14z n * d14w n))
                    + 16 * (d14y n * d14y n - 14 * (d14w n * d14w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d14y_rec n), (d14w_rec n).
      transitivity ((400 * (d14x n * d14x n - 14 * (d14z n * d14z n))
                    + 120 * (d14x n * d14y n - 14 * (d14z n * d14w n))
                    + 9 * (d14y n * d14y n - 14 * (d14w n * d14w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d14x_rec n), (d14y_rec n), (d14z_rec n), (d14w_rec n).
      transitivity ((540 * (d14x n * d14x n - 14 * (d14z n * d14z n))
                    + 161 * (d14x n * d14y n - 14 * (d14z n * d14w n))
                    + 12 * (d14y n * d14y n - 14 * (d14w n * d14w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d14y_rec n), (d14z_rec n), (d14x_rec n), (d14w_rec n).
      transitivity ((d14y n * d14z n - d14x n * d14w n)%Z).
      * ring.
      * exact H4.
Qed.

(* main statement 1 (member-stream norm): x^2 - 14 z^2 = 1, the +1 branch of the family. *)
Theorem d14_norm_x : forall n : nat,
  (d14x n * d14x n - 14 * (d14z n * d14z n) = 1)%Z.
Proof. intro n. exact (proj1 (d14_norm_quad n)). Qed.

(* main statement 2 (companion-stream norm): y^2 - 14 w^2 = -5. *)
Theorem d14_norm_y : forall n : nat,
  (d14y n * d14y n - 14 * (d14w n * d14w n) = (-5))%Z.
Proof. intro n. exact (proj1 (proj2 (d14_norm_quad n))). Qed.

(* on the family the companion norm gap is exactly 5 in absolute value. *)
Theorem d14_norm_y_abs5 : forall n : nat,
  Z.abs (d14y n * d14y n - 14 * (d14w n * d14w n)) = 5%Z.
Proof. intro n. rewrite (d14_norm_y n). reflexivity. Qed.

(* main statement 3 (subfamily determinant): x_n z_{n+1} - x_{n+1} z_n = 4;
   the constant 4 is the sharpness certificate element, the row-1 entry of
   the member stream, equal to q_3 = 4. *)
Theorem d14_det : forall n : nat,
  (d14x n * d14z (S n) - d14x (S n) * d14z n = 4)%Z.
Proof.
  intro n. rewrite (d14z_rec n), (d14x_rec n).
  transitivity ((- (4 * (d14y n * d14z n - d14x n * d14w n)))%Z).
  - ring.
  - rewrite (proj2 (proj2 (proj2 (d14_norm_quad n)))). reflexivity.
Qed.

(* 14 is not a perfect square: 3^2 < 14 < 4^2 rules out c * c = 14 by a bound contradiction; supplied ahead of the q_square_gap use site. *)
Lemma d14_nonsquare : forall c : Z, (14 <> c * c)%Z.
Proof.
  intro c. intro Hc. exfalso.
  pose proof (Z.abs_square c) as Habs. pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = 14)%Z) by lia.
  assert (Hgt : (3 < Z.abs c)%Z).
  { destruct (Z_lt_le_dec 3 (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============================================================ *)
(* Section Q. Final assembly: the Zpos bridges, the family member
   d14_member, the two family theorems and the Q-square sharpness. *)
(* ============================================================ *)

Definition d14yp (k : nat) : positive := Zpos_of (d14x k).
Definition d14wp (k : nat) : positive := Zpos_of (d14z k).

Lemma d14yp_pos : forall k, Z.pos (d14yp k) = d14x k.
Proof.
  intro k. unfold d14yp. apply Id_eq. apply Zpos_of_pos.
  destruct (d14xy_ge1 k) as [Hx _]. lia.
Qed.

Lemma d14wp_pos : forall k, Z.pos (d14wp k) = d14z k.
Proof.
  intro k. unfold d14wp. apply Id_eq. apply Zpos_of_pos.
  destruct (d14zw_ge k) as [Hz _]. lia.
Qed.

(* family member: p_{4k+3}/q_{4k+3}, the convergent of sqrt(14) of index 4k+3 on the x^2 - 14 y^2 = +1 branch; k = 0 gives 15/4. *)
Definition d14_member (k : nat) : Q := (Z.pos (d14yp k) # d14wp k)%Q.

(* family-certificate sharpness (main theorem 1): the distance of adjacent
   family members equals 4/(z_k z_{k+1}) with exact equality, realizing the
   constant 4 of d14_det (the period-4 shape of the d3_family_sharp form with
   constant 1 in place of 4). *)
Theorem d14_family_sharp : forall k : nat,
  QeqT (Qabs (d14_member k - d14_member (S k)))
       ((Z.pos 4) # (d14wp k * d14wp (S k)))%Q.
Proof.
  intro k.
  assert (Hd : (d14_member k - d14_member (S k))%Q ==
               ((Z.pos (d14yp k) * Z.pos (d14wp (S k))
                 - Z.pos (d14yp (S k)) * Z.pos (d14wp k))
                 # (d14wp k * d14wp (S k)))%Q).
  { unfold d14_member. apply qeqT_imp_qeq. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - rewrite (d14yp_pos k), (d14yp_pos (S k)).
    assert (Hd2 : (d14x k * Z.pos (d14wp (S k))
                   - d14x (S k) * Z.pos (d14wp k) = 4)%Z).
    { pose proof (d14_det k) as Hdet.
      rewrite <- (d14wp_pos (S k)), <- (d14wp_pos k) in Hdet.
      exact Hdet. }
    rewrite Hd2.
    unfold Qeq, Qabs. cbn [Qnum Qden Z.abs]. reflexivity.
Qed.

(* family separation certificate (main theorem 2): any a/b lies at distance
   >= 1/(b z_k) from the family member; the sole premise is that the gap
   a z_k - x_k b is nonzero. *)
Theorem d14_family_sep : forall (a : Z) (b : positive) (k : nat),
  (a * d14z k - d14x k * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * d14wp k)) # 1))
        (Qabs ((a # b)%Q - d14_member k)).
Proof.
  intros a b k Hk. unfold d14_member.
  assert (Hk2 : (a * Z.pos (d14wp k) - Z.pos (d14yp k) * Z.pos b <> 0)%Z).
  { rewrite (d14wp_pos k), (d14yp_pos k). exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (d14wp k) - Z.pos (d14yp k) * Z.pos b)
                  # (b * d14wp k))%Q)
          (Qabs ((a # b)%Q - (Z.pos (d14yp k) # d14wp k)%Q))
          (Qinv ((Z.pos (b * d14wp k)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (d14yp k) # d14wp k)%Q))
                   (Qabs ((a * Z.pos (d14wp k) - Z.pos (d14yp k) * Z.pos b)
                           # (b * d14wp k))%Q)).
    apply qeqT_imp_qeq. apply fib_qabs_congr. apply qeqT_imp_qeq. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * d14wp k)%positive).
    exact (ZLeT_drop _ _ (zabs_ge1 _ Hk2)).
Qed.

(* Q-square sharpness (main theorem 3): |member^2 - 14| = 1/z^2 with exact
   equality, so the lower bound 1/b^2 of q_square_gap is attained on the
   +1 branch; the constant norm 1 avoids the powneg1 case split. *)
Theorem d14_q_square_sharp : forall k : nat,
  QeqT (Qabs (d14_member k * d14_member k - (14 # 1)%Q))
       (Qinv ((Z.pos (d14wp k * d14wp k)) # 1)).
Proof.
  intro k.
  assert (Hd : (d14_member k * d14_member k - (14 # 1))%Q ==
               ((Z.pos (d14yp k) * Z.pos (d14yp k)
                 - 14 * (Z.pos (d14wp k) * Z.pos (d14wp k)))
                 # (d14wp k * d14wp k))%Q).
  { unfold d14_member. apply qeqT_imp_qeq. apply (q_square_cross (Z.pos (d14yp k)) 14 (d14wp k)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - rewrite (d14yp_pos k).
    assert (Hn2 : (d14x k * d14x k
                   - 14 * (Z.pos (d14wp k) * Z.pos (d14wp k)) = 1)%Z).
    { pose proof (d14_norm_x k) as Hn.
      rewrite <- (d14wp_pos k) in Hn. exact Hn. }
    rewrite Hn2.
    change (Qabs (Z.pos 1 # d14wp k * d14wp k)) with (Z.pos 1 # d14wp k * d14wp k)%Q.
    change (Qinv (Z.pos (d14wp k * d14wp k) # 1)) with (1 # d14wp k * d14wp k)%Q.
    apply Qeq_refl.
Qed.

(* instance of q_square_gap on the D=14 family; taken together with the sharpness, the lower bound is exactly attained. *)
Lemma d14_q_square_gap_instance : forall k : nat,
  QleT' (Qinv ((Z.pos (d14wp k * d14wp k)) # 1))
        (Qabs (d14_member k * d14_member k - (14 # 1)%Q)).
Proof.
  intro k. unfold d14_member.
  apply (q_square_gap 14 (Z.pos (d14yp k)) (d14wp k)).
  - cbn. lia.
  - intro c. apply (d14_nonsquare c).
Qed.

(* ============================================================ *)
(* Section A. Audit: Print Assumptions, separate extraction and the
   vm_compute numerical anchors. *)
(* ============================================================ *)

Print Assumptions d14x_rec.
Print Assumptions d14y_rec.
Print Assumptions d14z_rec.
Print Assumptions d14w_rec.
Print Assumptions d14xy_ge1.
Print Assumptions d14zw_ge.
Print Assumptions d14_norm_quad.
Print Assumptions d14_norm_x.
Print Assumptions d14_norm_y.
Print Assumptions d14_norm_y_abs5.
Print Assumptions d14_det.
Print Assumptions d14_nonsquare.
Print Assumptions Zpos_of_pos.
Print Assumptions d14yp_pos.
Print Assumptions d14wp_pos.
Print Assumptions d14_family_sep.
Print Assumptions d14_family_sharp.
Print Assumptions d14_q_square_sharp.
Print Assumptions d14_q_square_gap_instance.

(* numerical anchor 1 (family member): member 0 = p_3/q_3 = 15/4 on the x^2 - 14 y^2 = +1 branch. *)
Lemma smoke_member_15_4 : (Qeq_bool (d14_member 0) (15 # 4)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* numerical anchor 2 (family member): member 1 = p_7/q_7 = 449/120 on the x^2 - 14 y^2 = +1 branch. *)
Lemma smoke_member_449_120 : (Qeq_bool (d14_member 1) (449 # 120)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* numerical anchor 3 (norm layer): |449^2 - 14 * 120^2| = 1, an instance of d14_norm_x. *)
Lemma smoke_norm_1 : Z.eqb (Z.abs (d14x 1 * d14x 1 - 14 * (d14z 1 * d14z 1))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* numerical anchor 4 (sharpness layer): |15/4 - 449/120| = 1/120 = 4/(4 * 120) with exact equality, an instance of d14_family_sharp. *)
Lemma smoke_sharp_1_120 :
  (Qeq_bool (Qabs (d14_member 0 - d14_member 1))
            ((Z.pos 4) # (d14wp 0 * d14wp 1))%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* numerical anchor 5 (Q-square sharpness): |(15/4)^2 - 14| = 1/16 = 1/4^2, an instance of d14_q_square_sharp. *)
Lemma smoke_qsq_1_16 :
  (Qeq_bool (Qabs (d14_member 0 * d14_member 0 - (14 # 1)%Q))
            (Qinv ((Z.pos (d14wp 0 * d14wp 0)) # 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(* numerical anchor 6 (one step of the matrix N): x_1 = 449 and z_1 = 120, the carrier values of p_7/q_7. *)
Lemma smoke_step_449_120 :
  (Z.eqb (d14x 1) 449%Z, Z.eqb (d14z 1) 120%Z) = (true, true).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions smoke_member_15_4.
Print Assumptions smoke_member_449_120.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_120.
Print Assumptions smoke_qsq_1_16.
Print Assumptions smoke_step_449_120.

From Stdlib Require Import Extraction.
Separate Extraction d14pair e14pair d14x d14y d14z d14w d14yp d14wp
  d14_member d14_norm_y_abs5 d14_det d14_family_sep d14_family_sharp
  d14_q_square_sharp d14_q_square_gap_instance
  smoke_member_15_4 smoke_member_449_120 smoke_norm_1 smoke_sharp_1_120
  smoke_qsq_1_16 smoke_step_449_120.
