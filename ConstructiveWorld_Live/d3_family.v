(* ConstructiveWorld-Set -- the D = 3 period-2 convergence subfamily. *)

(** * d3_family: the D = 3 period-2 convergence subfamily.

    Mission.  [sqrt(3) = [1; 1,2,1,2,...]] has period 2, so the odd-index
    convergents [(p_{2k+1}, p_{2k})] obey a constant 2-step block recursion
    with matrix N = [[3,1],[2,1]] (det N = 1) on the bases [(2, 1)] and
    [(1, 1)].  Carries the dual streams [d3pair]/[e3pair] with
    [d3x]/[d3y]/[d3z]/[d3w], the norm fold [d3_norm_quad] (four constant
    invariants), [d3_norm_x]/[d3_norm_y]/[d3_norm_y_abs2], [d3_det],
    [d3_nonsquare], [d3_member], [d3_family_sharp]/[d3_family_sep],
    [d3_q_square_sharp] with instance [d3_q_square_gap_instance], and six
    vm_compute numerical anchors.

    Dependencies.  Stdlib [ZArith.ZArith], [Arith.Arith], [Bool.Bool], [Lia],
      [QArith.QArith], [QArith.Qabs]; this development's [S02_CauchyComplete],
      [fib_machine], [fib_qdomain] (built on [fib_norm_gap]), [pell_family].

    References.  This development, d3_family.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" d3_family.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
Require Import S02_CauchyComplete.
Require Import fib_machine.
Require Import fib_qdomain.
Require Import pell_family.
From Stdlib Require Import ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* Section C.  Carrier layer: the d3pair/e3pair dual threading, the   *)
(* streams d3x/d3y/d3z/d3w, the recursion unfoldings, the positivity  *)
(* layer.                                                             *)
(* ============================================================ *)

(* X stream: (x_{k+1}, y_{k+1}) = N (x_k, y_k) with N = [[3,1],[2,1]], base (p_1, p_0) = (2, 1). *)
Fixpoint d3pair (n : nat) : Z * Z :=
  match n with
  | O => (2%Z, 1%Z)
  | S k => match d3pair k with pair x y => ((3 * x + y)%Z, (2 * x + y)%Z) end
  end.

(* Q stream: the same coefficients in the 2-step recursion, base (q_1, q_0) = (1, 1). *)
Fixpoint e3pair (n : nat) : Z * Z :=
  match n with
  | O => (1%Z, 1%Z)
  | S k => match e3pair k with pair x y => ((3 * x + y)%Z, (2 * x + y)%Z) end
  end.

Definition d3x (n : nat) : Z := fst (d3pair n).
Definition d3y (n : nat) : Z := snd (d3pair n).
Definition d3z (n : nat) : Z := fst (e3pair n).
Definition d3w (n : nat) : Z := snd (e3pair n).

Lemma d3x_0 : d3x 0 = 2%Z.
Proof. reflexivity. Qed.

Lemma d3y_0 : d3y 0 = 1%Z.
Proof. reflexivity. Qed.

Lemma d3z_0 : d3z 0 = 1%Z.
Proof. reflexivity. Qed.

Lemma d3w_0 : d3w 0 = 1%Z.
Proof. reflexivity. Qed.

Lemma d3pair_unfold : forall n : nat,
  d3pair (S n) = ((3 * fst (d3pair n) + snd (d3pair n))%Z,
                  (2 * fst (d3pair n) + snd (d3pair n))%Z).
Proof. intro n. cbn [d3pair]. destruct (d3pair n) as [a b]. reflexivity. Qed.

Lemma e3pair_unfold : forall n : nat,
  e3pair (S n) = ((3 * fst (e3pair n) + snd (e3pair n))%Z,
                  (2 * fst (e3pair n) + snd (e3pair n))%Z).
Proof. intro n. cbn [e3pair]. destruct (e3pair n) as [a b]. reflexivity. Qed.

Lemma d3x_rec : forall n, d3x (S n) = (3 * d3x n + d3y n)%Z.
Proof. intro n. unfold d3x, d3y. rewrite d3pair_unfold. reflexivity. Qed.

Lemma d3y_rec : forall n, d3y (S n) = (2 * d3x n + d3y n)%Z.
Proof. intro n. unfold d3x, d3y. rewrite d3pair_unfold. reflexivity. Qed.

Lemma d3z_rec : forall n, d3z (S n) = (3 * d3z n + d3w n)%Z.
Proof. intro n. unfold d3z, d3w. rewrite e3pair_unfold. reflexivity. Qed.

Lemma d3w_rec : forall n, d3w (S n) = (2 * d3z n + d3w n)%Z.
Proof. intro n. unfold d3z, d3w. rewrite e3pair_unfold. reflexivity. Qed.

(* Positivity layer: the x and y streams stay >= 1 throughout; z >= 1 and w >= 0 (guards the Q denominator positions and the Zpos bridge). *)
Lemma d3xy_ge1 : forall n, (1 <= d3x n)%Z /\ (1 <= d3y n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d3x_0 | rewrite d3y_0]; lia.
  - split; rewrite ?d3x_rec, ?d3y_rec; lia.
Qed.

Lemma d3zw_ge : forall n, (1 <= d3z n)%Z /\ (0 <= d3w n)%Z.
Proof.
  induction n as [|n [IH1 IH2]].
  - split; [rewrite d3z_0 | rewrite d3w_0]; lia.
  - split; rewrite ?d3z_rec, ?d3w_rec; lia.
Qed.

(* ============================================================ *)
(* Section N.  Norm layer: the four constant invariants of            *)
(* d3_norm_quad, the subfamily determinant, the nonsquare fact.       *)
(* ============================================================ *)

(* Induction for the four invariants (period 2 keeps each of them
   constant): the base (2,1)/(1,1) closes by ring; the step decompositions
   S1' = 9*S1 + 6*C + S2, S2' = 4*S1 + 4*C + S2, C' = 6*S1 + 5*C + S2 and
   G' = G close the ring argument. *)
Lemma d3_norm_quad : forall n : nat,
  (d3x n * d3x n - 3 * (d3z n * d3z n) = 1)%Z /\
  (d3y n * d3y n - 3 * (d3w n * d3w n) = (-2))%Z /\
  (d3x n * d3y n - 3 * (d3z n * d3w n) = (-1))%Z /\
  (d3y n * d3z n - d3x n * d3w n = (-1))%Z.
Proof.
  induction n as [|n [H1 [H2 [H3 H4]]]].
  - split; [| split; [| split]].
    + unfold d3x, d3y, d3z, d3w. cbn [d3pair e3pair fst snd]. ring.
    + unfold d3x, d3y, d3z, d3w. cbn [d3pair e3pair fst snd]. ring.
    + unfold d3x, d3y, d3z, d3w. cbn [d3pair e3pair fst snd]. ring.
    + unfold d3x, d3y, d3z, d3w. cbn [d3pair e3pair fst snd]. ring.
  - split; [| split; [| split]].
    + rewrite (d3x_rec n), (d3z_rec n).
      transitivity ((9 * (d3x n * d3x n - 3 * (d3z n * d3z n))
                    + 6 * (d3x n * d3y n - 3 * (d3z n * d3w n))
                    + (d3y n * d3y n - 3 * (d3w n * d3w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d3y_rec n), (d3w_rec n).
      transitivity ((4 * (d3x n * d3x n - 3 * (d3z n * d3z n))
                    + 4 * (d3x n * d3y n - 3 * (d3z n * d3w n))
                    + (d3y n * d3y n - 3 * (d3w n * d3w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d3x_rec n), (d3y_rec n), (d3z_rec n), (d3w_rec n).
      transitivity ((6 * (d3x n * d3x n - 3 * (d3z n * d3z n))
                    + 5 * (d3x n * d3y n - 3 * (d3z n * d3w n))
                    + (d3y n * d3y n - 3 * (d3w n * d3w n)))%Z).
      * ring.
      * rewrite H1, H3, H2. ring.
    + rewrite (d3y_rec n), (d3z_rec n), (d3x_rec n), (d3w_rec n).
      transitivity ((d3y n * d3z n - d3x n * d3w n)%Z).
      * ring.
      * exact H4.
Qed.

(* Main statement 1 (member-stream norm): x^2 - 3 z^2 = 1, the +1 subfamily of the norm fold. *)
Theorem d3_norm_x : forall n : nat,
  (d3x n * d3x n - 3 * (d3z n * d3z n) = 1)%Z.
Proof. intro n. exact (proj1 (d3_norm_quad n)). Qed.

(* Main statement 2 (companion-stream norm): y^2 - 3 w^2 = -2. *)
Theorem d3_norm_y : forall n : nat,
  (d3y n * d3y n - 3 * (d3w n * d3w n) = (-2))%Z.
Proof. intro n. exact (proj1 (proj2 (d3_norm_quad n))). Qed.

(* The norm gap on the family is exactly 2 in absolute value (companion stream). *)
Theorem d3_norm_y_abs2 : forall n : nat,
  Z.abs (d3y n * d3y n - 3 * (d3w n * d3w n)) = 2%Z.
Proof. intro n. rewrite (d3_norm_y n). reflexivity. Qed.

(* Main statement 3 (subfamily determinant): x_n z_{n+1} - x_{n+1} z_n = 1
   -- the sharpness certificate at constant 1 (the B_12 entry of the
   member stream). *)
Theorem d3_det : forall n : nat,
  (d3x n * d3z (S n) - d3x (S n) * d3z n = 1)%Z.
Proof.
  intro n. rewrite (d3z_rec n), (d3x_rec n).
  transitivity ((- (d3y n * d3z n - d3x n * d3w n))%Z).
  - ring.
  - rewrite (proj2 (proj2 (proj2 (d3_norm_quad n)))). reflexivity.
Qed.

(* 3 is not a perfect square: the bounds 1^2 < 3 < 2^2 contradict c * c = 3 (feeds the q_square_gap call sites). *)
Lemma d3_nonsquare : forall c : Z, (3 <> c * c)%Z.
Proof.
  intro c. intro Hc. exfalso.
  pose proof (Z.abs_square c) as Habs. pose proof (Z.abs_nonneg c) as Hnn.
  assert (Hd : (Z.abs c * Z.abs c = 3)%Z) by lia.
  assert (Hgt : (1 < Z.abs c)%Z).
  { destruct (Z_lt_le_dec 1 (Z.abs c)) as [Hp | Hp].
    - exact Hp.
    - exfalso. nia. }
  exfalso. nia.
Qed.

(* ============================================================ *)
(* Section Q.  Final assembly: the Zpos bridge, d3_member, the        *)
(* sharpness and separation theorems, the Q-square sharpness.         *)
(* ============================================================ *)

Definition d3yp (k : nat) : positive := Zpos_of (d3x k).
Definition d3wp (k : nat) : positive := Zpos_of (d3z k).

Lemma d3yp_pos : forall k, Z.pos (d3yp k) = d3x k.
Proof.
  intro k. unfold d3yp. apply Id_eq. apply Zpos_of_pos.
  destruct (d3xy_ge1 k) as [Hx _]. lia.
Qed.

Lemma d3wp_pos : forall k, Z.pos (d3wp k) = d3z k.
Proof.
  intro k. unfold d3wp. apply Id_eq. apply Zpos_of_pos.
  destruct (d3zw_ge k) as [Hz _]. lia.
Qed.

(* Family member: p_{2k+1} / q_{2k+1}, the (2k+1)-th convergent of sqrt(3) (the x^2 - 3 y^2 = +1 subfamily; k = 0 gives 2/1). *)
Definition d3_member (k : nat) : Q := (Z.pos (d3yp k) # d3wp k)%Q.

(* Certificate sharpness (main statement 1): the distance of adjacent
   family members equals 1/(z_k z_{k+1}) exactly -- the constant-1
   determinant d3_det realized as an equality (the period-2 analogue of
   d13_family_sharp, with the constant 5 replaced by 1). *)
Theorem d3_family_sharp : forall k : nat,
  QeqT (Qabs (d3_member k - d3_member (S k)))
       ((Z.pos 1) # (d3wp k * d3wp (S k)))%Q.
Proof.
  intro k.
  assert (Hd : (d3_member k - d3_member (S k))%Q ==
               ((Z.pos (d3yp k) * Z.pos (d3wp (S k))
                 - Z.pos (d3yp (S k)) * Z.pos (d3wp k))
                 # (d3wp k * d3wp (S k)))%Q).
  { unfold d3_member. apply qeqT_imp_qeq. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - rewrite (d3yp_pos k), (d3yp_pos (S k)).
    assert (Hd2 : (d3x k * Z.pos (d3wp (S k))
                   - d3x (S k) * Z.pos (d3wp k) = 1)%Z).
    { pose proof (d3_det k) as Hdet.
      rewrite <- (d3wp_pos (S k)), <- (d3wp_pos k) in Hdet.
      exact Hdet. }
    rewrite Hd2.
    unfold Qeq, Qabs. cbn [Qnum Qden Z.abs]. reflexivity.
Qed.

(* Family separation certificate (main statement 2): every a/b stays at
   distance >= 1/(b z_k) from the family member (the analogue of
   d13_family_sep; the only premise is a nonzero gap). *)
Theorem d3_family_sep : forall (a : Z) (b : positive) (k : nat),
  (a * d3z k - d3x k * Z.pos b <> 0)%Z ->
  QleT' (Qinv ((Z.pos (b * d3wp k)) # 1))
        (Qabs ((a # b)%Q - d3_member k)).
Proof.
  intros a b k Hk. unfold d3_member.
  assert (Hk2 : (a * Z.pos (d3wp k) - Z.pos (d3yp k) * Z.pos b <> 0)%Z).
  { rewrite (d3wp_pos k), (d3yp_pos k). exact Hk. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (d3wp k) - Z.pos (d3yp k) * Z.pos b)
                  # (b * d3wp k))%Q)
          (Qabs ((a # b)%Q - (Z.pos (d3yp k) # d3wp k)%Q))
          (Qinv ((Z.pos (b * d3wp k)) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (Z.pos (d3yp k) # d3wp k)%Q))
                   (Qabs ((a * Z.pos (d3wp k) - Z.pos (d3yp k) * Z.pos b)
                           # (b * d3wp k))%Q)).
    apply qeqT_imp_qeq. apply fib_qabs_congr. apply qeqT_imp_qeq. apply fib_cross_mult.
  - apply (fib_qle_abs_ge (b * d3wp k)%positive).
    exact (ZLeT_drop _ _ (zabs_ge1 _ Hk2)).
Qed.

(* Q-square sharpness (main statement 3): |member^2 - 3| = 1/z^2 as an
   exact equality -- the q_square_gap lower bound 1/b^2 is attained on the
   +1 subfamily (the analogue of d13_q_square_sharp; the constant norm 1
   needs no (-1)^n case split). *)
Theorem d3_q_square_sharp : forall k : nat,
  QeqT (Qabs (d3_member k * d3_member k - (3 # 1)%Q))
       (Qinv ((Z.pos (d3wp k * d3wp k)) # 1)).
Proof.
  intro k.
  assert (Hd : (d3_member k * d3_member k - (3 # 1))%Q ==
               ((Z.pos (d3yp k) * Z.pos (d3yp k)
                 - 3 * (Z.pos (d3wp k) * Z.pos (d3wp k)))
                 # (d3wp k * d3wp k))%Q).
  { unfold d3_member. apply qeqT_imp_qeq. apply (q_square_cross (Z.pos (d3yp k)) 3 (d3wp k)). }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - rewrite (d3yp_pos k).
    assert (Hn2 : (d3x k * d3x k
                   - 3 * (Z.pos (d3wp k) * Z.pos (d3wp k)) = 1)%Z).
    { pose proof (d3_norm_x k) as Hn.
      rewrite <- (d3wp_pos k) in Hn. exact Hn. }
    rewrite Hn2.
    change (Qabs (Z.pos 1 # d3wp k * d3wp k)) with (Z.pos 1 # d3wp k * d3wp k)%Q.
    change (Qinv (Z.pos (d3wp k * d3wp k) # 1)) with (1 # d3wp k * d3wp k)%Q.
    apply Qeq_refl.
Qed.

(* Instance call of q_square_gap (the FIB3 main statement instantiated on the D = 3 family; taken together with the sharpness, the lower bound is attained exactly). *)
Lemma d3_q_square_gap_instance : forall k : nat,
  QleT' (Qinv ((Z.pos (d3wp k * d3wp k)) # 1))
        (Qabs (d3_member k * d3_member k - (3 # 1)%Q)).
Proof.
  intro k. unfold d3_member.
  apply (q_square_gap 3 (Z.pos (d3yp k)) (d3wp k)).
  - cbn. lia.
  - intro c. apply (d3_nonsquare c).
Qed.

(* ============================================================ *)
(* Section A.  Audit: Print Assumptions, Separate Extraction and      *)
(* vm_compute numerical anchors.                                      *)
(* ============================================================ *)

Print Assumptions d3x_rec.
Print Assumptions d3y_rec.
Print Assumptions d3z_rec.
Print Assumptions d3w_rec.
Print Assumptions d3xy_ge1.
Print Assumptions d3zw_ge.
Print Assumptions d3_norm_quad.
Print Assumptions d3_norm_x.
Print Assumptions d3_norm_y.
Print Assumptions d3_norm_y_abs2.
Print Assumptions d3_det.
Print Assumptions d3_nonsquare.
Print Assumptions Zpos_of_pos.
Print Assumptions d3yp_pos.
Print Assumptions d3wp_pos.
Print Assumptions d3_family_sep.
Print Assumptions d3_family_sharp.
Print Assumptions d3_q_square_sharp.
Print Assumptions d3_q_square_gap_instance.

(* Numerical anchor 1 (family member): member 0 = p_1/q_1 = 2/1 (the x^2 - 3 y^2 = +1 subfamily). *)
Lemma smoke_member_2_1 : (Qeq_bool (d3_member 0) (2 # 1)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 2 (family member): member 1 = p_3/q_3 = 7/4 (the x^2 - 3 y^2 = +1 subfamily). *)
Lemma smoke_member_7_4 : (Qeq_bool (d3_member 1) (7 # 4)%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 3 (norm layer): |7^2 - 3*4^2| = 1 (instance of d3_norm_x). *)
Lemma smoke_norm_1 : Z.eqb (Z.abs (d3x 1 * d3x 1 - 3 * (d3z 1 * d3z 1))) 1%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 4 (sharpness layer): |2 - 7/4| = 1/4 = 1/(1*4) as an exact equality (instance of d3_family_sharp). *)
Lemma smoke_sharp_1_4 :
  (Qeq_bool (Qabs (d3_member 0 - d3_member 1))
            ((Z.pos 1) # (d3wp 0 * d3wp 1))%Q) = true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 5 (Q-square sharpness): |2^2 - 3| = 1 = 1/1^2 (instance of d3_q_square_sharp). *)
Lemma smoke_qsq_1_1 :
  (Qeq_bool (Qabs (d3_member 0 * d3_member 0 - (3 # 1)%Q))
            (Qinv ((Z.pos (d3wp 0 * d3wp 0)) # 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(* Numerical anchor 6 (N-matrix step): x_1 = 7, z_1 = 4 (the carrier values of p_3/q_3). *)
Lemma smoke_step_7_4 :
  (Z.eqb (d3x 1) 7%Z, Z.eqb (d3z 1) 4%Z) = (true, true).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions smoke_member_2_1.
Print Assumptions smoke_member_7_4.
Print Assumptions smoke_norm_1.
Print Assumptions smoke_sharp_1_4.
Print Assumptions smoke_qsq_1_1.
Print Assumptions smoke_step_7_4.

From Stdlib Require Import Extraction.
Separate Extraction d3pair e3pair d3x d3y d3z d3w d3yp d3wp
  d3_member d3_norm_y_abs2 d3_det d3_family_sep d3_family_sharp
  d3_q_square_sharp d3_q_square_gap_instance
  smoke_member_2_1 smoke_member_7_4 smoke_norm_1 smoke_sharp_1_4
  smoke_qsq_1_1 smoke_step_7_4.
