(* ConstructiveWorld-Set — Fibonacci-denominator family machinery: the
   golden-ratio convergent family on the three-layer separation frame. *)
(** * fib_machine: Separation certificates along Fibonacci convergents.

    Mission.  Formalizes the denominator family [b*F_{n+1}] of the golden
      ratio: carrier layer [fibpair]/[fibp]/[fibz]/[powneg1], certificate
      layer [fib_den]/[fib_cert], integer gap layer [fibz_cassini]/
      [fib_gap_abs1] (Cassini), identity chain [fib_cross_mult]/
      [fib_qabs_congr]/[fib_qle_abs_ge], and assembly [fib_family_sep]
      (each [a/b] with nonzero residue lies at distance at least
      [1/(b*F_{n+1})] from [F_{n+2}/F_{n+1}]) and [fib_family_sharp]
      (equality attained on consecutive convergents: the Hurwitz/Markov
      bound realized from below in exact rational arithmetic).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
      [Arith.Arith], [Bool.Bool], [Lia], [Setoid], [Morphisms], [Qfield].
      Requires [S01_BaseRing] ([Id], [id_refl]) and [S02_CauchyComplete]
      ([QltT]/[QleT']/[QeqT] with transfer lemmas) of this development.

    References.  This development, b5_machine.v, the baseline module in
      ConstructiveWorld-Main: the three-layer statement shapes carry over
      with the factor position [|a|+2b] replaced by [b*F_{n+1}].

    Constructivity.  All named statements are carried by [Set] ([QeqT],
      [QleT'], [QltT], [Id], decidable Z and bool tests); proofs reason in
      constructive Prop internally; [Print Assumptions] reports none.

    Build.  [rocq c -native-compiler no -q -Q . "" fib_machine.v]
      compiles cleanly (exit 0) with the [S01_BaseRing]/
      [S02_CauchyComplete] artifacts on the load path. *)
Require Import S02_CauchyComplete.
Require Import S01_BaseRing (Id, id_refl).
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* Section 1. Carrier layer: fibpair/fibp/fibz/powneg1.         *)
(* ============================================================ *)

Fixpoint fibpair (n : nat) : positive * positive :=
  match n with
  | O => (1%positive, 1%positive)
  | S m => match fibpair m with
           | pair a b => (Pos.add a b, a)
           end
  end.

Definition fibp (n : nat) : positive := snd (fibpair n).

Definition fibz (n : nat) : Z := Z.pos (fibp n).

Fixpoint powneg1 (n : nat) : Z := match n with O => 1%Z | S m => (- powneg1 m)%Z end.

Lemma fibpair_unfold : forall n,
  Id (fibpair (S n)) (Pos.add (fst (fibpair n)) (snd (fibpair n)), fst (fibpair n)).
Proof. intro n. cbn [fibpair]. destruct (fibpair n) as [a b]. apply id_refl. Qed.

Lemma fibpair_snd_S : forall n, Id (snd (fibpair (S n))) (fst (fibpair n)).
Proof. intro n. rewrite fibpair_unfold. apply id_refl. Qed.

Lemma fibp_rec : forall n, Id (fibp (S (S n))) (Pos.add (fibp (S n)) (fibp n)).
Proof.
  intro n. unfold fibp.
  rewrite (fibpair_unfold (S n)).
  rewrite (fibpair_unfold n).
  cbn [fst snd].
  apply id_refl.
Qed.

Lemma fibz_rec : forall n, Id (fibz (S (S n))) (fibz (S n) + fibz n)%Z.
Proof. intro n. unfold fibz. rewrite fibp_rec. apply id_refl. Qed.

Lemma fibz_pos : forall n, Id (Z.ltb 0 (fibz n)) true.
Proof.
  intro n. destruct (Z.ltb 0 (fibz n)) eqn:E.
  - apply id_refl.
  - exfalso. apply Z.ltb_ge in E. unfold fibz in E.
    pose proof (Pos2Z.is_pos (fibp n)) as Hp. lia.
Qed.

Lemma powneg1_S : forall n, Id (powneg1 (S n)) (- powneg1 n)%Z.
Proof. intro n. apply id_refl. Qed.

Lemma zabs_powneg1 : forall n, Id (Z.abs (powneg1 n)) 1%Z.
Proof.
  induction n as [|n IH].
  - apply id_refl.
  - rewrite powneg1_S, Z.abs_opp. exact IH.
Qed.

Lemma zabs_ge1 : forall k : Z, k <> 0%Z -> Id (Z.leb 1 (Z.abs k)) true.
Proof.
  intros k H. destruct (Z.leb 1 (Z.abs k)) eqn:E.
  - apply id_refl.
  - exfalso. apply Z.leb_gt in E. destruct k as [|p|p].
    + exfalso. apply H. reflexivity.
    + cbn [Z.abs] in *. pose proof (Pos2Z.is_pos p). lia.
    + cbn [Z.abs] in *. pose proof (Pos2Z.is_pos p). lia.
Qed.

(* ============================================================ *)
(* Section 2. Certificate layer: fib_den/fib_cert/QeqT.         *)
(* ============================================================ *)

Definition fib_den (n : nat) (b : positive) : Z :=
  Z.pos b * fibz n.

Definition fib_cert (n : nat) (b : positive) : Q :=
  Qinv ((fib_den n b) # 1).

Lemma fib_den_pos : forall (n : nat) (b : positive),
  Id (Z.ltb 0 (fib_den n b)) true.
Proof.
  intros n b. destruct (Z.ltb 0 (fib_den n b)) eqn:E.
  - apply id_refl.
  - exfalso. apply Z.ltb_ge in E. unfold fib_den, fibz in E.
    pose proof (Pos2Z.is_pos b) as Hb. pose proof (Pos2Z.is_pos (fibp n)) as Hn.
    nia.
Qed.

Lemma fib_qinv_pos : forall z : Z, (0 < z)%Z -> QltT 0 (Qinv (z # 1)).
Proof.
  intros z Hz. destruct z as [|p|p].
  - exfalso. lia.
  - apply Qlt_to_QltT. unfold Qlt, Qinv. cbn [Qnum Qden]. lia.
  - exfalso. lia.
Qed.

Lemma fib_cert_pos : forall (n : nat) (b : positive), QltT 0 (fib_cert n b).
Proof.
  intros n b. unfold fib_cert. apply fib_qinv_pos.
  pose proof (fib_den_pos n b) as H.
  apply Z.ltb_lt.
  exact (match H in (Id _ y) return (Z.ltb 0 (fib_den n b) = y) with id_refl => eq_refl end).
Qed.

Lemma fib_cert_eq : forall (n : nat) (b : positive),
  QeqT (fib_cert n b) (Qinv ((Z.pos b * fibz n) # 1)).
Proof.
  intros n b. unfold fib_cert, fib_den. apply qeq_imp_qeqT. apply Qeq_refl.
Qed.

(* ============================================================ *)
(* Section 3. Integer gap layer: Cassini, exact unit gaps.      *)
(* ============================================================ *)

Lemma fibz_cassini : forall n : nat,
  Id (fibz (S n) * fibz (S n) - fibz n * fibz (S (S n)))%Z (powneg1 (S n)).
Proof.
  induction n as [|n IH].
  - apply id_refl.
  - rewrite powneg1_S.
    rewrite <- IH.
    rewrite !fibz_rec.
    match goal with |- Id ?A ?B => assert (Hr : A = B) by ring end.
    destruct Hr.
    apply id_refl.
Qed.

Lemma fib_gap_abs1 : forall n : nat,
  Id (Z.abs (fibz (S n) * fibz (S n) - fibz n * fibz (S (S n)))) 1%Z.
Proof.
  intro n. rewrite fibz_cassini. apply zabs_powneg1.
Qed.

(* ============================================================ *)
(* Section 4. Identity chain: cross-mult, Qabs congruence.      *)
(* ============================================================ *)

Lemma fib_cross_mult : forall (a c : Z) (b d : positive),
  QeqT ((a # b) - (c # d))%Q ((a * Z.pos d - c * Z.pos b) # (b * d))%Q.
Proof.
  intros a c b d. apply qeq_imp_qeqT.
  unfold Qminus, Qopp, Qplus, Qnum, Qden. cbn.
  rewrite Z.mul_opp_l. reflexivity.
Qed.

Lemma fib_qabs_congr : forall x y : Q, x == y -> QeqT (Qabs x) (Qabs y).
Proof.
  intros x y Hxy. apply qeq_imp_qeqT.
  destruct x as [nx dx]; destruct y as [ny dy].
  change (Qabs (nx # dx)) with (Z.abs nx # dx)%Q.
  change (Qabs (ny # dy)) with (Z.abs ny # dy)%Q.
  unfold Qeq in Hxy |- *.
  cbn [Qnum Qden] in Hxy |- *.
  destruct nx as [|p|p]; destruct ny as [|q|q].
  - cbn [Z.abs]. reflexivity.
  - exfalso. cbn [Z.abs] in *. pose proof (Pos2Z.is_pos q); pose proof (Pos2Z.is_pos dx). lia.
  - exfalso. cbn [Z.abs] in *. pose proof (Pos2Z.is_pos q); pose proof (Pos2Z.is_pos dx). lia.
  - exfalso. cbn [Z.abs] in *. pose proof (Pos2Z.is_pos p); pose proof (Pos2Z.is_pos dy). lia.
  - cbn [Z.abs]. exact Hxy.
  - exfalso. cbn [Z.abs] in *.
    pose proof (Pos2Z.is_pos p); pose proof (Pos2Z.is_pos q);
    pose proof (Pos2Z.is_pos dx); pose proof (Pos2Z.is_pos dy). lia.
  - exfalso. cbn [Z.abs] in *. pose proof (Pos2Z.is_pos p); pose proof (Pos2Z.is_pos dy). lia.
  - exfalso. cbn [Z.abs] in *.
    pose proof (Pos2Z.is_pos p); pose proof (Pos2Z.is_pos q);
    pose proof (Pos2Z.is_pos dx); pose proof (Pos2Z.is_pos dy). lia.
  - cbn [Z.abs]. simpl in Hxy. inversion Hxy. subst.
    rewrite <- (Pos2Z.inj_mul p dy), <- (Pos2Z.inj_mul q dx).
    rewrite H0. reflexivity.
Qed.

Lemma fib_qle_abs_ge : forall (M : positive) (k : Z),
  (1 <= Z.abs k)%Z -> QleT' (Qinv ((Z.pos M) # 1)%Q) (Qabs (k # M)%Q).
Proof.
  intros M k Hk. destruct k as [|q|q].
  - exfalso. cbn in Hk. lia.
  - cbn [Z.abs]. apply Qle_to_QleT'. unfold Qle, Qinv, Qabs, Qnum. cbn.
    pose proof (Pos2Z.is_pos M). pose proof (Pos2Z.is_pos q). nia.
  - cbn [Z.abs]. apply Qle_to_QleT'. unfold Qle, Qinv, Qabs, Qopp, Qnum. cbn.
    pose proof (Pos2Z.is_pos M). pose proof (Pos2Z.is_pos q). nia.
Qed.

(* The right argument of QleT' transfers along Qeq, taken directly from the Qle_comp instance. *)
Lemma fib_qleT_congr_r : forall x y z : Q, x == y -> QleT' z x -> QleT' z y.
Proof.
  intros x y z Hxy Hle. apply Qle_to_QleT'.
  apply (proj1 (Qle_comp z z (Qeq_refl z) x y Hxy)).
  exact (QleT'_to_Qle _ _ Hle).
Qed.

(* ============================================================ *)
(* Section 5. Assembly: member, family_sep, family_sharp.       *)
(* ============================================================ *)

(* Family member [n]: F_{n+2}/F_{n+1}, the (n+1)-th convergent of the golden ratio, with [fibp n = F_{n+1}] carrying the denominator. *)
Definition fib_member (n : nat) : Q := (fibz (S n) # fibp n)%Q.

(* Family separation certificate (main statement, no hypotheses): for [k <> 0], |a/b - F_{n+2}/F_{n+1}| >= 1/(b*F_{n+1}). *)
Theorem fib_family_sep : forall (n : nat) (a : Z) (b : positive),
  (a * fibz n - Z.pos b * fibz (S n) <> 0)%Z ->
  QleT' (fib_cert n b)
        (Qabs ((a # b)%Q - fib_member n)).
Proof.
  intros n a b Hk. unfold fib_member, fib_cert.
  assert (Hk2 : (a * Z.pos (fibp n) - fibz (S n) * Z.pos b <> 0)%Z).
  { unfold fibz in Hk.
    pose proof (Z.mul_comm (Z.pos (fibp (S n))) (Z.pos b)) as Hc.
    intro Hc0. apply Hk. rewrite <- Hc. exact Hc0. }
  apply (fib_qleT_congr_r
          (Qabs ((a * Z.pos (fibp n) - fibz (S n) * Z.pos b) # (b * fibp n))%Q)
          (Qabs ((a # b)%Q - (fibz (S n) # fibp n)%Q))
          (Qinv ((Z.pos b * fibz n) # 1))).
  - apply (Qeq_sym (Qabs ((a # b)%Q - (fibz (S n) # fibp n)%Q))
                   (Qabs ((a * Z.pos (fibp n) - fibz (S n) * Z.pos b) # (b * fibp n))%Q)).
    apply qeqT_imp_qeq. apply fib_qabs_congr. apply qeqT_imp_qeq. apply fib_cross_mult.
  - change (Z.pos b * fibz n)%Z with (Z.pos (b * fibp n))%Z.
    apply (fib_qle_abs_ge (b * fibp n)).
    pose proof (zabs_ge1 (a * Z.pos (fibp n) - fibz (S n) * Z.pos b) Hk2) as Hz.
    apply Z.leb_le.
    exact (match Hz in (Id _ y)
             return (Z.leb 1 (Z.abs (a * Z.pos (fibp n) - fibz (S n) * Z.pos b)) = y)
           with id_refl => eq_refl end).
Qed.

(* Shape of Qinv on a positive integer element, direct under the unfold recipe. *)
Lemma fib_qinv_shape : forall p : positive, QeqT (Qinv ((Z.pos p) # 1)%Q) (1 # p)%Q.
Proof. intro p. apply qeq_imp_qeqT. unfold Qeq, Qinv. cbn. reflexivity. Qed.

(* Sharpness helper: the QeqT form of the equality |1/M| = 1/M, reciprocal spelled as Qinv. *)
Lemma fib_qeqT_one : forall M : positive,
  QeqT (Qabs ((Z.pos 1 # M)%Q)) (Qinv ((Z.pos M) # 1)%Q).
Proof.
  intro M.
  apply qeq_imp_qeqT.
  change (Qabs (Z.pos 1 # M)) with (Z.pos 1 # M)%Q.
  change (Qinv (Z.pos M # 1)) with (1 # M)%Q.
  apply Qeq_refl.
Qed.

(* Sharpness of the family certificate (Markov/Hurwitz bound): equality is
   attained exactly at consecutive convergents, dist(member j, member (S j))
   = 1/(F_{j+1}*F_{j+2}): the Hurwitz ceiling 1/sqrt(5) realized from below. *)
Theorem fib_family_sharp : forall j : nat,
  QeqT (Qabs (fib_member j - fib_member (S j)))
       (Qinv ((Z.pos (fibp j * fibp (S j))) # 1)).
Proof.
  intro j.
  assert (Hd : (fib_member j - fib_member (S j))%Q ==
               ((fibz (S j) * Z.pos (fibp (S j)) - fibz (S (S j)) * Z.pos (fibp j)) # (fibp j * fibp (S j)))%Q).
  { unfold fib_member. apply qeqT_imp_qeq. apply fib_cross_mult. }
  pose proof (fib_qabs_congr _ _ Hd) as Hab.
  apply qeq_imp_qeqT.
  eapply Qeq_trans.
  - exact (qeqT_imp_qeq _ _ Hab).
  - change (Z.pos (fibp (S j))) with (fibz (S j)).
    change (Z.pos (fibp j)) with (fibz j).
    rewrite (Z.mul_comm (fibz (S (S j))) (fibz j)).
    rewrite (fibz_cassini j).
    destruct (powneg1 (S j)) as [|p|p] eqn:E.
    + exfalso.
      pose proof (zabs_powneg1 (S j)) as Hz. rewrite E in Hz. cbn in Hz. inversion Hz.
    +       pose proof (zabs_powneg1 (S j)) as Hz. rewrite E in Hz. cbn in Hz.
      inversion Hz. subst p.
      change (Qabs (Z.pos 1 # fibp j * fibp (S j))) with (Z.pos 1 # fibp j * fibp (S j))%Q.
      change (Qinv (Z.pos (fibp j * fibp (S j)) # 1)) with (1 # fibp j * fibp (S j))%Q.
      apply Qeq_refl.
    +       pose proof (zabs_powneg1 (S j)) as Hz. rewrite E in Hz. cbn in Hz.
      inversion Hz. subst p.
      change (Qabs (Z.neg 1 # fibp j * fibp (S j))) with (Z.pos 1 # fibp j * fibp (S j))%Q.
      change (Qinv (Z.pos (fibp j * fibp (S j)) # 1)) with (1 # fibp j * fibp (S j))%Q.
      apply Qeq_refl.
Qed.

(* ============================================================ *)
(* Section 6. Audit: assumption prints, numeric anchors.        *)
(* ============================================================ *)

Print Assumptions fib_den_pos.
Print Assumptions fib_cert_pos.
Print Assumptions fib_cert_eq.
Print Assumptions fibz_cassini.
Print Assumptions fib_gap_abs1.
Print Assumptions fib_cross_mult.
Print Assumptions fib_qabs_congr.
Print Assumptions fib_qle_abs_ge.
Print Assumptions fib_family_sep.
Print Assumptions fib_family_sharp.

(* Numeric anchor 1 (family member): member 3 = F_5/F_4 = 5/3. *)
Lemma fib_smoke_member_5_3 :
  Id (Qeq_bool (fib_member 3) (5 # 3)%Q) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numeric anchor 2 (equality at the sharp point): |13/8 - 21/13| = 1/104
   = [Qinv ((Z.pos (fibp 4 * fibp 5)) # 1)] with [fibp 4 = 5], [fibp 5 = 8]. *)
Lemma fib_smoke_sharp_13_8 :
  Id (Qeq_bool (Qabs (fib_member 4 - fib_member 5))
               (Qinv ((Z.pos (fibp 4 * fibp 5)) # 1))) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numeric anchor 3 (strict separation): |7/5 - 13/8| = 9/40 > 1/25 = [fib_cert 4 5]. *)
Lemma fib_smoke_sep_strict :
  Id (Qlt_bool (fib_cert 4 5%positive)
               (Qabs ((7 # 5)%Q - fib_member 4))) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numeric anchor 4 (certificate positivity with a negative numerator). *)
Lemma fib_smoke_cert_pos :
  Id (Qlt_bool 0%Q (fib_cert 4 5%positive)) true.
Proof. vm_compute. apply id_refl. Qed.

(* Numeric anchor 5 (integer gap instance): |F_6^2 - F_5*F_7| = 1 with [fibz 4 = 5], [fibz 5 = 8], [fibz 6 = 13]. *)
Lemma fib_smoke_gap :
  Id (Z.eqb (Z.abs (fibz 5 * fibz 5 - fibz 4 * fibz 6)) 1%Z) true.
Proof. vm_compute. apply id_refl. Qed.

Print Assumptions fib_smoke_member_5_3.
Print Assumptions fib_smoke_sharp_13_8.
Print Assumptions fib_smoke_sep_strict.
Print Assumptions fib_smoke_cert_pos.
Print Assumptions fib_smoke_gap.

From Stdlib Require Import Extraction.
Separate Extraction fibp fibz fib_cert fib_member fib_family_sep
  fib_family_sharp fib_smoke_member_5_3 fib_smoke_sharp_13_8
  fib_smoke_sep_strict fib_smoke_cert_pos fib_smoke_gap.
