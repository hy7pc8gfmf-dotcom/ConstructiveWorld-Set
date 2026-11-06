(* ConstructiveWorld-Set -- discrete multiple-sum carrier for the Zeilberger-Zudilin coefficients A_j. *)

(** * piu_zz_kernel_sum: the discrete multiple sum for the coefficients A_j.

    Mission.  The coefficients A_j in the partial-fraction expansion of
      R(x) = 5 x^{2n} (x^4 + 6 x^2 + 25)^{2n} / ((5+x)^{3n+1} (5-x)^{3n+1})
      satisfy the explicit multiple sum of Zeilberger-Zudilin (Lemma 1,
      eq. (5)).  This file carries that sum on nat lists and Gauss rational
      pairs: the six-index binomial product [piu_zz_T], the index set
      [zz_Mj], the real part [piu_zz_Aj], the rationality exit
      [piu_zz_Aj_rational], the out-of-range value [piu_zz_Aj_out], the
      crude size bound [piu_zz_crude_size], and the numeric samples
      [piu_zz_sample_n1_j0], [piu_zz_sample_n1_j3].

    Dependencies.  Stdlib [QArith.QArith], [ZArith.ZArith], [Qring], [Lia],
      [List], [QArith.Qabs].  Requires [piu_zz_gauss_pair] of this
      development (the Gauss rational-pair carrier with the Set-valued
      equality [qeqT]).

    References.  This development, piu_zz_kernel_sum.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" piu_zz_kernel_sum.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import QArith.Qabs.
Import ListNotations.
Require Import piu_zz_gauss_pair.

(* ------------------------------------------------------------------ *)
(* A Set-carried order predicate on Q, mirroring qeqT                  *)
(* ------------------------------------------------------------------ *)

Inductive qleT : Q -> Q -> Set :=
| qleT_intro : forall a b : Q, (a <= b)%Q -> qleT a b.

(* The two projections qleT_to_Qle and qeqT_eq (Set-carried statements read
   back as propositions) are omitted from the interface: every former use
   site reads the wrapped premise directly through an in-proof match on the
   single constructor. *)
Lemma qleT_of_Qle : forall {x y : Q}, (x <= y)%Q -> qleT x y.
Proof. intros x y H. apply qleT_intro. exact H. Qed.

Lemma qleT_trans : forall x y z : Q, qleT x y -> qleT y z -> qleT x z.
Proof.
  intros x y z H1 H2. destruct H1 as [a1 b1 H1a]. destruct H2 as [a2 b2 H2b].
  apply qleT_intro. eapply Qle_trans; [ exact H1a | exact H2b ].
Qed.

Lemma qleT_eq_l : forall x y z : Q, (x == y)%Q -> qleT x z -> qleT y z.
Proof.
  intros x y z Heq Hz. destruct Hz as [a b Hz'].
  apply qleT_intro. rewrite <- Heq. exact Hz'.
Qed.

Lemma Qmult_le_compat_l_spec : forall {x y z : Q},
  qleT x y -> qleT (0 # 1)%Q z -> qleT (z * x) (z * y).
Proof.
  intros x y z H1 H2.
  pose proof (match H1 as H0 in qleT a b return (a <= b)%Q with
              | qleT_intro _ _ h => h end) as H1p.
  pose proof (match H2 as H0 in qleT a b return (a <= b)%Q with
              | qleT_intro _ _ h => h end) as H2p.
  apply qleT_intro. rewrite (Qmult_comm z x), (Qmult_comm z y).
  apply Qmult_le_compat_r; assumption.
Qed.

Lemma qleT_mul_le_compat_r : forall x y k : Q,
  (0 <= k)%Q -> qleT x y -> qleT (x * k) (y * k).
Proof.
  intros x y k Hk Hxy. apply qleT_of_Qle. apply Qmult_le_compat_r.
  - destruct Hxy as [a b Hxy']. exact Hxy'.
  - exact Hk.
Qed.

Lemma qleT_mul_le_compat_l : forall x y k : Q,
  (0 <= k)%Q -> qleT (x * k) (y * k) -> qleT (k * (x * k)) (k * (y * k)).
Proof.
  intros x y k Hk Hxy.
  pose proof (match Qmult_le_compat_l_spec Hxy (qleT_of_Qle Hk) as H0
              in qleT a b return (a <= b)%Q with
              | qleT_intro _ _ h => h end) as H.
  apply qleT_of_Qle. exact H.
Qed.

Lemma qleT_mul_r_pos : forall x y k : Q,
  (0 < k)%Q -> qleT (x * k) (y * k) -> qleT x y.
Proof.
  intros x y k Hk Hxy. apply qleT_of_Qle.
  apply (proj1 (Qmult_le_r x y k Hk)). destruct Hxy as [a b Hxy']. exact Hxy'.
Qed.

Lemma qle_0_qnat1 : forall k : nat, qleT (0 # 1)%Q ((Z.of_nat k # 1)%Q).
Proof.
  intros k. apply qleT_intro. unfold Qle. simpl. rewrite Z.mul_1_r.
  apply (proj1 (Nat2Z.inj_le 0 k)). lia.
Qed.

(* Auxiliary Set-carried strict order on Q, mirroring qleT: the standard
   library QArith_base provides Qeq_bool and Qle_bool but no boolean strict
   order, so QltT supplies it as an inductive.  The constructor name
   QltT_intro keeps the strict carrier distinct from the non-strict one
   across the development. *)
Inductive QltT : Q -> Q -> Set :=
| QltT_intro : forall a b : Q, (a < b)%Q -> QltT a b.

Lemma qpos_pow2 : forall k : nat, QltT (0 # 1)%Q ((Z.of_nat (2 ^ k)) # 1)%Q.
Proof.
  intros k. apply QltT_intro. unfold Qlt. simpl. rewrite Z.mul_1_r.
  apply (proj1 (Nat2Z.inj_lt 0 (2 ^ k))).
  assert (Hpos : (0 < 2 ^ k)%nat).
  { apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. }
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Q square and absolute-value bridges                                 *)
(* ------------------------------------------------------------------ *)

Lemma Qsq_nonneg : forall b : Q, qleT (0 # 1)%Q (b * b)%Q.
Proof.
  intros b. apply qleT_intro.
  destruct (Qlt_le_dec 0 b) as [Hlt | Hle].
  - assert (Hle0 : (0 <= b)%Q) by (apply Qlt_le_weak; exact Hlt).
    apply (Qle_trans _ (0 * b)%Q).
    + rewrite Qmult_0_l. apply Qle_refl.
    + apply Qmult_le_compat_r; [ exact Hle0 | exact Hle0 ].
  - assert (Hpos : (0 <= - b)%Q).
    { pose proof (Qopp_le_compat b 0 Hle) as H'.
      assert (H0 : (- 0)%Q == 0%Q) by reflexivity.
      rewrite H0 in H'. exact H'. }
    assert (Hbb : (b * b == (- b) * (- b))%Q) by ring.
    rewrite Hbb.
    apply (Qle_trans _ (0 * (- b))%Q).
    + rewrite Qmult_0_l. apply Qle_refl.
    + apply (Qmult_le_compat_r 0 (- b) (- b)); [ exact Hpos | exact Hpos ].
Qed.

Lemma pos_sq_le : forall u v : Q,
  qleT (0 # 1)%Q u -> qleT (0 # 1)%Q v -> qleT (u * u) (v * v) -> qleT u v.
Proof.
  intros u v Hu Hv Hsq.
  pose proof (match Hu as H0 in qleT a b return (a <= b)%Q with
              | qleT_intro _ _ h => h end) as Hu'.
  pose proof (match Hv as H0 in qleT a b return (a <= b)%Q with
              | qleT_intro _ _ h => h end) as Hv'.
  pose proof (match Hsq as H0 in qleT a b return (a <= b)%Q with
              | qleT_intro _ _ h => h end) as Hsq'.
  apply qleT_of_Qle.
  destruct (Qlt_le_dec v u) as [Hlt | Hge].
  - exfalso.
    assert (H1 : (v * v <= u * v)%Q)
      by (apply Qmult_le_compat_r; [ apply Qlt_le_weak; exact Hlt | exact Hv' ]).
    assert (Hpu : (0 < u)%Q) by (apply (Qle_lt_trans 0 v u Hv'); exact Hlt).
    assert (H2 : (u * v < u * u)%Q).
    { rewrite (Qmult_comm u v).
      apply (Qmult_lt_compat_r v u u); [ exact Hpu | exact Hlt ]. }
    apply (Qlt_irrefl (v * v)).
    apply (Qlt_le_trans (v * v) (u * u) (v * v)).
    + apply (Qle_lt_trans (v * v) (u * v) (u * u)); [ exact H1 | exact H2 ].
    + exact Hsq'.
  - exact Hge.
Qed.

Lemma sq_le_abs : forall a b : Q,
  qleT (0 # 1)%Q b -> qleT (a * a) (b * b) -> qleT (Qabs a) b.
Proof.
  intros a b Hb Hsq. apply qleT_of_Qle.
  destruct (Qlt_le_dec 0 a) as [Hlt | Hle].
  - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hlt)).
    pose proof (match pos_sq_le a b (qleT_of_Qle (Qlt_le_weak 0 a Hlt)) Hb Hsq
                as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as H.
    exact H.
  - rewrite (Qabs_neg a Hle).
    assert (Hn : (0 <= - a)%Q).
    { pose proof (Qopp_le_compat a 0 Hle) as H'.
      assert (H0 : (- 0)%Q == 0%Q) by reflexivity.
      rewrite H0 in H'. exact H'. }
    assert (Haa : ((- a) * (- a) == a * a)%Q) by ring.
    pose proof (qleT_eq_l _ _ _ (Qeq_sym _ _ Haa) Hsq) as Hsq2.
    pose proof (match pos_sq_le (- a) b (qleT_of_Qle Hn) Hb Hsq2
                as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as H.
    exact H.
Qed.

Lemma gz_Re_sq_le_norm : forall z : gz,
  qleT (gz_Re z * gz_Re z) (gz_norm z).
Proof.
  intros [a b]. cbn [gz_Re gz_norm]. apply qleT_intro.
  apply (Qle_trans _ (a * a + 0)%Q).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply Qplus_le_compat; [ apply Qle_refl | ].
    exact (match Qsq_nonneg b as H0 in qleT c d return (c <= d)%Q with
           | qleT_intro _ _ h => h end).
Qed.

(* ------------------------------------------------------------------ *)
(* Pascal-recursion binomial coefficients                              *)
(* ------------------------------------------------------------------ *)

Fixpoint binomP (n k : nat) {struct n} : nat :=
  match k with
  | O => 1
  | S k' =>
      match n with
      | O => 0
      | S n' => binomP n' k' + binomP n' (S k')
      end
  end.

Lemma binomP_le_pow2 : forall n k : nat, (Nat.leb (binomP n k) (2 ^ n)) = true.
Proof.
  intros n k. apply (proj2 (Nat.leb_le _ _)). revert k.
  induction n as [| n IH]; intros k; destruct k as [| k']; cbn [binomP].
  - cbn [Nat.pow]. lia.
  - cbn [Nat.pow]. lia.
  - cbn [Nat.pow].
    assert (Hpos : (0 < 2 ^ n)%nat).
    { apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. }
    lia.
  - rewrite Nat.pow_succ_r'.
    pose proof (IH k'). pose proof (IH (S k')). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The sign (-1)^(m1+..+m5)                                            *)
(* ------------------------------------------------------------------ *)

Definition zz_sign (s : nat) : Q := if Nat.even s then (1 # 1)%Q else (-1 # 1)%Q.

Lemma zz_sign_sq : forall s : nat, qeqT (zz_sign s * zz_sign s) (1 # 1)%Q.
Proof.
  intros s. unfold zz_sign. destruct (Nat.even s).
  - apply qeqT_intro. vm_compute. reflexivity.
  - apply qeqT_intro. vm_compute. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* T(m): the six-index binomial product, valued in Z                   *)
(* ------------------------------------------------------------------ *)

Definition zz6 : Set := (nat * nat * nat * nat * nat * nat)%type.

Definition zz_Tnat (n : nat) (m : zz6) : nat :=
  match m with
  | (m0, m1, m2, m3, m4, m5) =>
      binomP (3 * n + m0) m0 *
      (binomP (2 * n) m1 *
       (binomP (2 * n) m2 *
        (binomP (2 * n) m3 * (binomP (2 * n) m4 * binomP (2 * n) m5))))
  end.

Definition piu_zz_T (n : nat) (m : zz6) : Z := Z.of_nat (zz_Tnat n m).

Lemma zz_T_nat_le : forall (n : nat) (m0 m1 m2 m3 m4 m5 : nat),
  (Nat.leb (zz_Tnat n (m0, m1, m2, m3, m4, m5)) (2 ^ (13 * n + m0))) = true.
Proof.
  intros n m0 m1 m2 m3 m4 m5. unfold zz_Tnat.
  apply (proj2 (Nat.leb_le _ _)).
  eapply Nat.le_trans; [ | ].
  apply Nat.mul_le_mono;
    [ apply (proj1 (Nat.leb_le _ _)); apply binomP_le_pow2 | ].
  apply Nat.mul_le_mono;
    [ apply (proj1 (Nat.leb_le _ _)); apply binomP_le_pow2 | ].
  apply Nat.mul_le_mono;
    [ apply (proj1 (Nat.leb_le _ _)); apply binomP_le_pow2 | ].
  apply Nat.mul_le_mono;
    [ apply (proj1 (Nat.leb_le _ _)); apply binomP_le_pow2 | ].
  apply Nat.mul_le_mono;
    [ apply (proj1 (Nat.leb_le _ _)); apply binomP_le_pow2
    | apply (proj1 (Nat.leb_le _ _)); apply binomP_le_pow2 ].
  rewrite <- !Nat.pow_add_r. apply Nat.pow_le_mono_r; [ lia | lia ].
Qed.

(* ------------------------------------------------------------------ *)
(* The index set M_j as a list                                         *)
(* ------------------------------------------------------------------ *)

Fixpoint zz_seq (k : nat) : list nat :=
  match k with
  | O => []
  | S k' => k' :: zz_seq k'
  end.

Definition zz_one (total m1 m2 m3 m4 m5 : nat) : list zz6 :=
  if Nat.leb (m1 + m2 + m3 + m4 + m5) total
  then [((total - (m1 + m2 + m3 + m4 + m5))%nat, m1, m2, m3, m4, m5)]
  else [].

Definition zz_Mj (n j : nat) : list zz6 :=
  if Nat.leb j (3 * n) then
    flat_map
      (fun m1 =>
        flat_map
          (fun m2 =>
            flat_map
              (fun m3 =>
                flat_map
                  (fun m4 =>
                    flat_map (fun m5 => zz_one (3 * n - j) m1 m2 m3 m4 m5)
                              (zz_seq (2 * n + 1)))
                  (zz_seq (2 * n + 1)))
              (zz_seq (2 * n + 1)))
          (zz_seq (2 * n + 1)))
      (zz_seq (2 * n + 1))
  else [].

Lemma zz_seq_length : forall k : nat, length (zz_seq k) = k.
Proof.
  induction k as [| k IH]; cbn [zz_seq length];
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma length_flat_map_seq_le : forall (B : Type) (f : nat -> list B) (K N : nat),
  (forall x, (Nat.leb (length (f x)) N) = true) ->
  (Nat.leb (length (flat_map f (zz_seq K))) (K * N)) = true.
Proof.
  intros B f K N H. apply (proj2 (Nat.leb_le _ _)).
  induction K as [| K IH]; cbn [zz_seq flat_map length].
  - lia.
  - rewrite length_app.
    eapply Nat.le_trans; [ apply Nat.add_le_mono;
                           [ apply (proj1 (Nat.leb_le _ _)); apply H
                           | exact IH ] | ].
    rewrite Nat.mul_succ_l. lia.
Qed.

Lemma zz_len1 : forall n j m1 m2 m3 m4 : nat,
  (Nat.leb (length (flat_map (fun m5 => zz_one (3 * n - j) m1 m2 m3 m4 m5)
                            (zz_seq (2 * n + 1))))
           ((2 * n + 1) * 1)) = true.
Proof.
  intros. apply length_flat_map_seq_le. intros m5. unfold zz_one.
  destruct (Nat.leb (m1 + m2 + m3 + m4 + m5) (3 * n - j)).
  - apply (proj2 (Nat.leb_le _ _)). cbn [length]. lia.
  - cbn [length]. reflexivity.
Qed.

Lemma zz_len2 : forall n j m1 m2 m3 : nat,
  (Nat.leb (length (flat_map
             (fun m4 =>
               flat_map (fun m5 => zz_one (3 * n - j) m1 m2 m3 m4 m5)
                        (zz_seq (2 * n + 1)))
             (zz_seq (2 * n + 1))))
           ((2 * n + 1) * ((2 * n + 1) * 1))) = true.
Proof.
  intros. apply length_flat_map_seq_le. intros m4. apply zz_len1.
Qed.

Lemma zz_len3 : forall n j m1 m2 : nat,
  (Nat.leb (length (flat_map
             (fun m3 =>
               flat_map
                 (fun m4 =>
                   flat_map (fun m5 => zz_one (3 * n - j) m1 m2 m3 m4 m5)
                            (zz_seq (2 * n + 1)))
                 (zz_seq (2 * n + 1)))
             (zz_seq (2 * n + 1))))
   ((2 * n + 1) * ((2 * n + 1) * ((2 * n + 1) * 1)))) = true.
Proof.
  intros. apply length_flat_map_seq_le. intros m3. apply zz_len2.
Qed.

Lemma zz_len4 : forall n j m1 : nat,
  (Nat.leb (length (flat_map
             (fun m2 =>
               flat_map
                 (fun m3 =>
                   flat_map
                     (fun m4 =>
                       flat_map (fun m5 => zz_one (3 * n - j) m1 m2 m3 m4 m5)
                                (zz_seq (2 * n + 1)))
                     (zz_seq (2 * n + 1)))
                 (zz_seq (2 * n + 1)))
             (zz_seq (2 * n + 1))))
   ((2 * n + 1) * ((2 * n + 1) * ((2 * n + 1) * ((2 * n + 1) * 1))))) = true.
Proof.
  intros. apply length_flat_map_seq_le. intros m2. apply zz_len3.
Qed.

Lemma zz_len5 : forall n j : nat,
  (Nat.leb (length (zz_Mj n j))
     ((2 * n + 1) * ((2 * n + 1) * ((2 * n + 1) * ((2 * n + 1) * ((2 * n + 1) * 1)))))) = true.
Proof.
  intros n j. unfold zz_Mj. destruct (Nat.leb j (3 * n)) eqn:E.
  - cbn [length]. apply length_flat_map_seq_le. intros m1. apply zz_len4.
  - cbn [length]. reflexivity.
Qed.

(* Membership carrier for the premise of zz_Mj_member: a single-constructor
   Set wrapper whose constructor argument carries the list-membership
   premise, mirroring the qeqT and qleT doctrine; the names BidT and
   BidT_intro are local to this module. *)
Inductive BidT (n j m0 m1 m2 m3 m4 m5 : nat) : Set :=
| BidT_intro : In (m0, m1, m2, m3, m4, m5) (zz_Mj n j) ->
               BidT n j m0 m1 m2 m3 m4 m5.

Lemma Bid_intro : forall (n j m0 m1 m2 m3 m4 m5 : nat),
  In (m0, m1, m2, m3, m4, m5) (zz_Mj n j) -> BidT n j m0 m1 m2 m3 m4 m5.
Proof. intros n j m0 m1 m2 m3 m4 m5 H. apply BidT_intro. exact H. Qed.

Lemma zz_Mj_member : forall (n j m0 m1 m2 m3 m4 m5 : nat),
  BidT n j m0 m1 m2 m3 m4 m5 ->
  (Nat.leb j (3 * n)) && (Nat.eqb (m0 + (m1 + m2 + m3 + m4 + m5)) (3 * n - j)) = true.
Proof.
  intros n j m0 m1 m2 m3 m4 m5 H. destruct H as [H]. unfold zz_Mj in H.
  destruct (Nat.leb j (3 * n)) eqn:E.
  - rewrite Bool.andb_true_l.
    apply (proj2 (Nat.eqb_eq _ _)).
    apply in_flat_map in H. destruct H as [a1 [Hin1 Ha]].
      apply in_flat_map in Ha. destruct Ha as [a2 [Hin2 Hb]].
      apply in_flat_map in Hb. destruct Hb as [a3 [Hin3 Hc]].
      apply in_flat_map in Hc. destruct Hc as [a4 [Hin4 Hd]].
      apply in_flat_map in Hd. destruct Hd as [a5 [Hin5 He]].
      unfold zz_one in He.
      destruct (Nat.leb (a1 + a2 + a3 + a4 + a5) (3 * n - j)) eqn:E5.
      * simpl in He. destruct He as [Heq | []].
        injection Heq as H0 Ea1 Ea2 Ea3 Ea4 Ea5.
        rewrite <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5.
        apply Nat.leb_le in E5. lia.
      * destruct He.
  - destruct H.
Qed.

(* ------------------------------------------------------------------ *)
(* Q-level arithmetic helpers around the carrier                       *)
(* ------------------------------------------------------------------ *)

Definition gz_scale (c : Q) (z : gz) : gz := gz_mul (c, 0) z.

Definition gz_hi : gz := ((1 # 2)%Q, (1 # 2)%Q).
Definition gz_hj : gz := ((1 # 2)%Q, (- (1 # 2))%Q).

Lemma gz_q2pow_step : forall k : nat,
  qeqT (((Z.of_nat (2 ^ S k)) # 1)%Q) (((2 # 1)%Q * ((Z.of_nat (2 ^ k)) # 1)%Q)%Q).
Proof.
  intros k. rewrite Nat.pow_succ_r'. rewrite Nat2Z.inj_mul.
  apply qeqT_intro. vm_compute. reflexivity.
Qed.

Lemma gz_qZmul1 : forall a b : nat,
  qeqT (((Z.of_nat (a * b)) # 1)%Q)
       ((((Z.of_nat a) # 1)%Q * ((Z.of_nat b) # 1)%Q)%Q).
Proof.
  intros a b. rewrite Nat2Z.inj_mul. apply qeqT_intro.
  cbn [Qmult]. apply Qeq_refl.
Qed.

Lemma qeqT_sq_nat1 : forall a : Z,
  qeqT (((a # 1)%Q * (a # 1)%Q)%Q) (((a * a) # 1)%Q).
Proof.
  intros a. apply qeqT_intro. cbn [Qmult]. apply Qeq_refl.
Qed.

Lemma qeqT_prod4R_nat1 : forall a1 a2 a3 a4 : Z,
  qeqT (((a1 # 1)%Q * ((a2 # 1)%Q * ((a3 # 1)%Q * (a4 # 1)%Q)%Q)%Q)%Q)
       ((((a1 * (a2 * (a3 * a4)))) # 1)%Q).
Proof.
  intros a1 a2 a3 a4. apply qeqT_intro. cbn [Qmult]. apply Qeq_refl.
Qed.

Lemma gz_norm_pow_1i : forall m : nat,
  qeqT (gz_norm (gz_pow (1, 1) m)) (((Z.of_nat (2 ^ m)) # 1)%Q).
Proof.
  induction m as [| m IH].
  - vm_compute. apply qeqT_refl.
  - eapply qeqT_trans.
    + apply gz_norm_pow_step.
    + eapply qeqT_trans.
      * apply qeqT_mul_r. exact gz_norm_ii.
      * eapply qeqT_trans.
        -- apply qeqT_mul_l. exact IH.
        -- apply qeqT_sym. exact (gz_q2pow_step m).
Qed.

Lemma gz_norm_pow_1j : forall m : nat,
  qeqT (gz_norm (gz_pow (1, -1) m)) (((Z.of_nat (2 ^ m)) # 1)%Q).
Proof.
  induction m as [| m IH].
  - vm_compute. apply qeqT_refl.
  - eapply qeqT_trans.
    + apply gz_norm_pow_step.
    + eapply qeqT_trans.
      * apply qeqT_mul_r. exact gz_norm_ij.
      * eapply qeqT_trans.
        -- apply qeqT_mul_l. exact IH.
        -- apply qeqT_sym. exact (gz_q2pow_step m).
Qed.

Lemma gz_norm_hi : qeqT (gz_norm gz_hi) ((1 # 2)%Q).
Proof. apply qeqT_intro. vm_compute. reflexivity. Qed.

Lemma gz_norm_hj : qeqT (gz_norm gz_hj) ((1 # 2)%Q).
Proof. apply qeqT_intro. vm_compute. reflexivity. Qed.

Lemma gz_qhalf2one : qeqT (((1 # 2)%Q * (2 # 1)%Q)%Q) (1 # 1)%Q.
Proof. apply qeqT_intro. vm_compute. reflexivity. Qed.

Lemma gz_norm_pow_hi1 : forall m : nat,
  qeqT (gz_norm (gz_pow gz_hi m) * ((Z.of_nat (2 ^ m)) # 1)%Q) ((1 # 1)%Q).
Proof.
  induction m as [| m IH].
  - apply qeqT_intro. vm_compute. reflexivity.
  - assert (Hstep : (gz_norm (gz_pow gz_hi (S m)) ==
                     gz_norm gz_hi * gz_norm (gz_pow gz_hi m))%Q).
    { destruct (gz_norm_pow_step gz_hi m) as [w1 w2 Hw]. exact Hw. }
    assert (Hhi : (gz_norm gz_hi == (1 # 2)%Q)%Q).
    { destruct gz_norm_hi as [hn1 hn2 Hh]. exact Hh. }
    assert (Hk : ((Z.of_nat (2 ^ S m)) # 1 ==
                  (((2 # 1)%Q * ((Z.of_nat (2 ^ m)) # 1)%Q)%Q))%Q).
    { destruct (gz_q2pow_step m) as [p1 p2 Hp]. exact Hp. }
    assert (Hhalf : (((1 # 2)%Q * (2 # 1)%Q)%Q == (1 # 1)%Q)%Q).
    { destruct gz_qhalf2one as [q1 q2 Hh]. exact Hh. }
    assert (HIH : (gz_norm (gz_pow gz_hi m) * ((Z.of_nat (2 ^ m)) # 1)%Q ==
                   (1 # 1)%Q)%Q).
    { destruct IH as [wi wi2 Hw]. exact Hw. }
    apply qeqT_intro.
    rewrite Hstep. rewrite Hhi. rewrite Hk.
    assert (Hreg : (((1 # 2)%Q * gz_norm (gz_pow gz_hi m) *
                     ((2 # 1)%Q * ((Z.of_nat (2 ^ m)) # 1)%Q)%Q) ==
                    (((1 # 2)%Q * (2 # 1)%Q) *
                     (gz_norm (gz_pow gz_hi m) * ((Z.of_nat (2 ^ m)) # 1)%Q))%Q)%Q)
      by ring.
    rewrite Hreg. rewrite Hhalf. rewrite HIH.
    vm_compute. reflexivity.
Qed.

Lemma gz_norm_pow_hj1 : forall m : nat,
  qeqT (gz_norm (gz_pow gz_hj m) * ((Z.of_nat (2 ^ m)) # 1)%Q) ((1 # 1)%Q).
Proof.
  induction m as [| m IH].
  - apply qeqT_intro. vm_compute. reflexivity.
  - assert (Hstep : (gz_norm (gz_pow gz_hj (S m)) ==
                     gz_norm gz_hj * gz_norm (gz_pow gz_hj m))%Q).
    { destruct (gz_norm_pow_step gz_hj m) as [w1 w2 Hw]. exact Hw. }
    assert (Hhi : (gz_norm gz_hj == (1 # 2)%Q)%Q).
    { destruct gz_norm_hj as [hn1 hn2 Hh]. exact Hh. }
    assert (Hk : ((Z.of_nat (2 ^ S m)) # 1 ==
                  (((2 # 1)%Q * ((Z.of_nat (2 ^ m)) # 1)%Q)%Q))%Q).
    { destruct (gz_q2pow_step m) as [p1 p2 Hp]. exact Hp. }
    assert (Hhalf : (((1 # 2)%Q * (2 # 1)%Q)%Q == (1 # 1)%Q)%Q).
    { destruct gz_qhalf2one as [q1 q2 Hh]. exact Hh. }
    assert (HIH : (gz_norm (gz_pow gz_hj m) * ((Z.of_nat (2 ^ m)) # 1)%Q ==
                   (1 # 1)%Q)%Q).
    { destruct IH as [wi wi2 Hw]. exact Hw. }
    apply qeqT_intro.
    rewrite Hstep. rewrite Hhi. rewrite Hk.
    assert (Hreg : (((1 # 2)%Q * gz_norm (gz_pow gz_hj m) *
                     ((2 # 1)%Q * ((Z.of_nat (2 ^ m)) # 1)%Q)%Q) ==
                    (((1 # 2)%Q * (2 # 1)%Q) *
                     (gz_norm (gz_pow gz_hj m) * ((Z.of_nat (2 ^ m)) # 1)%Q))%Q)%Q)
      by ring.
    rewrite Hreg. rewrite Hhalf. rewrite HIH.
    vm_compute. reflexivity.
Qed.

Lemma gz_norm_mul4 : forall z1 z2 z3 z4 : gz,
  qeqT (gz_norm (gz_mul (gz_mul z1 z2) (gz_mul z3 z4)))
       ((gz_norm z1 * gz_norm z2 * (gz_norm z3 * gz_norm z4))%Q).
Proof.
  intros z1 z2 z3 z4.
  eapply qeqT_trans. apply gz_norm_mul.
  eapply qeqT_trans. apply qeqT_mul_l. apply gz_norm_mul.
  apply qeqT_mul_r. apply gz_norm_mul.
Qed.

(* ------------------------------------------------------------------ *)
(* The multiple-sum term and the carried coefficient A_j               *)
(* ------------------------------------------------------------------ *)

Definition zz_coef (n j : nat) (m0 m1 m2 m3 m4 m5 : nat) : Q :=
  zz_sign (m1 + m2 + m3 + m4 + m5) *
  ((piu_zz_T n (m0, m1, m2, m3, m4, m5)) # 1)%Q *
  ((Z.of_nat (2 ^ (4 * n + j + m1))) # 2)%Q *
  ((Z.of_nat (5 ^ j)) # 1)%Q.

Definition zz_big (m2 m3 m4 m5 : nat) : gz :=
  gz_mul (gz_mul (gz_pow gz_hi m4) (gz_pow gz_hj m5))
         (gz_mul (gz_pow (2, 1) (m2 + m5)) (gz_pow (2, -1) (m3 + m4))).

Definition zz_term (n j : nat) (m : zz6) : gz :=
  match m with
  | (m0, m1, m2, m3, m4, m5) =>
      gz_scale (zz_coef n j m0 m1 m2 m3 m4 m5) (zz_big m2 m3 m4 m5)
  end.

Fixpoint gz_lsum (L : list gz) : gz :=
  match L with
  | [] => (0, 0)%Q
  | t :: L' => gz_add t (gz_lsum L')
  end.

Definition zz_terms (n j : nat) : list gz := map (zz_term n j) (zz_Mj n j).

Definition piu_zz_Mj_gz (n j : nat) : gz := gz_lsum (zz_terms n j).

Definition piu_zz_Aj (n j : nat) : Q := gz_Re (piu_zz_Mj_gz n j).

Lemma gz_norm_big_cleared : forall m2 m3 m4 m5 : nat,
  qeqT (gz_norm (zz_big m2 m3 m4 m5) * ((Z.of_nat (2 ^ (m4 + m5))) # 1)%Q)
       (((Z.of_nat (5 ^ (m2 + m3 + m4 + m5))) # 1)%Q).
Proof.
  intros m2 m3 m4 m5. unfold zz_big.
  rewrite (Nat.pow_add_r 2 m4 m5).
  apply qeqT_intro.
  assert (Hsplit : ((Z.of_nat (2 ^ m4 * 2 ^ m5)) # 1 ==
                    (((Z.of_nat (2 ^ m4)) # 1)%Q * ((Z.of_nat (2 ^ m5)) # 1)%Q)%Q)%Q).
  { destruct (gz_qZmul1 (2 ^ m4) (2 ^ m5)) as [q1 q2 Hq]. exact Hq. }
  rewrite Hsplit.
  assert (Hmul4 : (gz_norm (gz_mul (gz_mul (gz_pow gz_hi m4) (gz_pow gz_hj m5))
                                   (gz_mul (gz_pow (2, 1) (m2 + m5))
                                           (gz_pow (2, -1) (m3 + m4)))) ==
                   ((gz_norm (gz_pow gz_hi m4) * gz_norm (gz_pow gz_hj m5)) *
                    (gz_norm (gz_pow (2, 1) (m2 + m5)) *
                     gz_norm (gz_pow (2, -1) (m3 + m4))))%Q)%Q).
  { destruct (gz_norm_mul4 (gz_pow gz_hi m4) (gz_pow gz_hj m5)
                           (gz_pow (2, 1) (m2 + m5)) (gz_pow (2, -1) (m3 + m4)))
      as [u1 u2 Hu]. exact Hu. }
  rewrite Hmul4.
  assert (Hh1 : (gz_norm (gz_pow gz_hi m4) * ((Z.of_nat (2 ^ m4)) # 1)%Q ==
                 (1 # 1)%Q)%Q).
  { destruct (gz_norm_pow_hi1 m4) as [x1 x2 Hx]. exact Hx. }
  assert (Hh2 : (gz_norm (gz_pow gz_hj m5) * ((Z.of_nat (2 ^ m5)) # 1)%Q ==
                 (1 # 1)%Q)%Q).
  { destruct (gz_norm_pow_hj1 m5) as [y1 y2 Hy]. exact Hy. }
  assert (Ha : (gz_norm (gz_pow (2, 1) (m2 + m5)) ==
                ((Z.of_nat (5 ^ (m2 + m5))) # 1)%Q)%Q).
  { destruct (gz_norm_pow_2i (m2 + m5)) as [v1 v2 Hv]. exact Hv. }
  assert (Hb : (gz_norm (gz_pow (2, -1) (m3 + m4)) ==
                ((Z.of_nat (5 ^ (m3 + m4))) # 1)%Q)%Q).
  { destruct (gz_norm_pow_2mi (m3 + m4)) as [w1 w2 Hw]. exact Hw. }
  rewrite Ha. rewrite Hb.
  assert (Hreg : ((gz_norm (gz_pow gz_hi m4) * gz_norm (gz_pow gz_hj m5) *
                   (((Z.of_nat (5 ^ (m2 + m5))) # 1)%Q * ((Z.of_nat (5 ^ (m3 + m4))) # 1)%Q)) *
                  (((Z.of_nat (2 ^ m4)) # 1)%Q * ((Z.of_nat (2 ^ m5)) # 1)%Q)) ==
                 (((gz_norm (gz_pow gz_hi m4) * ((Z.of_nat (2 ^ m4)) # 1)%Q)%Q) *
                  ((gz_norm (gz_pow gz_hj m5) * ((Z.of_nat (2 ^ m5)) # 1)%Q)%Q) *
                  (((Z.of_nat (5 ^ (m2 + m5))) # 1)%Q * ((Z.of_nat (5 ^ (m3 + m4))) # 1)%Q))%Q)
    by ring.
  rewrite Hreg. rewrite Hh1. rewrite Hh2. rewrite !Qmult_1_l.
  assert (Hfin : (((Z.of_nat (5 ^ (m2 + m5))) # 1)%Q * ((Z.of_nat (5 ^ (m3 + m4))) # 1)%Q ==
                  ((Z.of_nat (5 ^ (m2 + m3 + m4 + m5))) # 1)%Q)%Q).
  { assert (Hnat : (5 ^ (m2 + m5) * 5 ^ (m3 + m4) = 5 ^ (m2 + m3 + m4 + m5))%nat)
      by (rewrite <- !Nat.pow_add_r; f_equal; lia).
    assert (Hsp5 : ((Z.of_nat (5 ^ (m2 + m5) * 5 ^ (m3 + m4))) # 1 ==
                    (((Z.of_nat (5 ^ (m2 + m5))) # 1)%Q *
                     ((Z.of_nat (5 ^ (m3 + m4))) # 1)%Q)%Q)%Q).
    { destruct (gz_qZmul1 (5 ^ (m2 + m5)) (5 ^ (m3 + m4))) as [w1 w2 Hq]. exact Hq. }
    rewrite <- Hnat. exact (Qeq_sym _ _ Hsp5). }
  rewrite Hfin. apply Qeq_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Real-part exit of the carrier                                       *)
(* ------------------------------------------------------------------ *)

Lemma gz_Re_add : forall z w : gz,
  qeqT (gz_Re (gz_add z w)) ((gz_Re z + gz_Re w)%Q).
Proof.
  intros [a b] [c d]. apply qeqT_intro. cbn [gz_add gz_Re]. apply Qeq_refl.
Qed.

Lemma gz_Re_scale : forall (c : Q) (z : gz),
  qeqT (gz_Re (gz_scale c z)) ((c * gz_Re z)%Q).
Proof.
  intros c z. unfold gz_scale.
  eapply qeqT_trans. apply gz_Re_mul.
  apply qeqT_intro. cbn [gz_Re gz_Im]. ring.
Qed.

Definition zz_Qsum (L : list Q) : Q := fold_right Qplus 0 L.

Lemma gz_Re_lsum : forall L : list gz,
  qeqT (gz_Re (gz_lsum L)) (zz_Qsum (map gz_Re L)).
Proof.
  induction L as [| t L IH].
  - apply qeqT_intro. cbn [gz_lsum gz_Re map zz_Qsum fold_right]. apply Qeq_refl.
  - assert (HIH : (gz_Re (gz_lsum L) == zz_Qsum (map gz_Re L))%Q).
    { destruct IH as [w1 w2 HIH]. exact HIH. }
    destruct t as [ta tb].
    eapply qeqT_trans. apply gz_Re_add.
    apply qeqT_intro.
    cbn [map zz_Qsum fold_right].
    rewrite HIH. apply Qeq_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Crude bound, step 1: the per-term square bound                      *)
(* ------------------------------------------------------------------ *)

Lemma zz_master_nat_le : forall n j m0 m1 m2 m3 m4 m5 : nat,
  (Nat.leb j (3 * n)) = true ->
  (Nat.eqb (m0 + (m1 + m2 + m3 + m4 + m5)) (3 * n - j)) = true ->
  (Nat.leb ((zz_Tnat n (m0, m1, m2, m3, m4, m5) * zz_Tnat n (m0, m1, m2, m3, m4, m5)) *
            ((2 ^ (4 * n + j + m1) * 2 ^ (4 * n + j + m1)) *
             ((5 ^ j * 5 ^ j) * 5 ^ (m2 + m3 + m4 + m5))))
           (2 ^ (54 * n) * 2 ^ (m4 + m5))) = true.
Proof.
  intros n j m0 m1 m2 m3 m4 m5 Hj Hsum.
  apply (proj1 (Nat.leb_le _ _)) in Hj. apply (proj1 (Nat.eqb_eq _ _)) in Hsum.
  apply (proj2 (Nat.leb_le _ _)).
  assert (HT : (zz_Tnat n (m0, m1, m2, m3, m4, m5) <= 2 ^ (13 * n + m0))%nat).
    { apply (proj1 (Nat.leb_le _ _)). apply zz_T_nat_le. }
  assert (HT2 : (zz_Tnat n (m0, m1, m2, m3, m4, m5) *
                 zz_Tnat n (m0, m1, m2, m3, m4, m5) <= 2 ^ (26 * n + 2 * m0))%nat).
  { eapply Nat.le_trans; [ apply Nat.mul_le_mono; exact HT; exact HT | ].
    rewrite <- !Nat.pow_add_r. apply Nat.pow_le_mono_r; [ lia | lia ]. }
  assert (HP2 : (2 ^ (4 * n + j + m1) * 2 ^ (4 * n + j + m1)
                 <= 2 ^ (2 * (4 * n + j + m1)))%nat).
  { rewrite <- Nat.pow_add_r. apply Nat.pow_le_mono_r; lia. }
  assert (HP : ((5 ^ j * 5 ^ j) * 5 ^ (m2 + m3 + m4 + m5) <= 2 ^ (14 * n))%nat).
  { assert (H6 : (j + j + (m2 + m3 + m4 + m5) <= 6 * n)%nat).
    { assert (Hs : (m2 + m3 + m4 + m5 <= 3 * n - j)%nat) by lia.
      lia. }
    rewrite <- !Nat.pow_add_r.
    eapply Nat.le_trans; [ | ].
    - apply Nat.pow_le_mono_r; [ lia | exact H6 ].
    - rewrite Nat.pow_mul_r.
      rewrite (Nat.pow_mul_r 2 14 n).
      apply Nat.pow_le_mono_l. vm_compute. lia. }
  eapply Nat.le_trans; [ | ].
  apply Nat.mul_le_mono; [ exact HT2 | apply Nat.mul_le_mono; [ exact HP2 | exact HP ] ].
  rewrite <- !Nat.pow_add_r. apply Nat.pow_le_mono_r; [ lia | ].
  f_equal. lia.
Qed.

Lemma zz_term_sq_le : forall n j m0 m1 m2 m3 m4 m5 : nat,
  (j <= 3 * n)%nat ->
  (m0 + (m1 + m2 + m3 + m4 + m5) = 3 * n - j)%nat ->
  qleT (gz_Re (zz_term n j (m0, m1, m2, m3, m4, m5)) *
        gz_Re (zz_term n j (m0, m1, m2, m3, m4, m5)))
       ((Z.of_nat (2 ^ (54 * n)) # 1)%Q).
Proof.
  intros n j m0 m1 m2 m3 m4 m5 Hj Hsum.
  cbn [zz_term].
  assert (HRe : (gz_Re (gz_scale (zz_coef n j m0 m1 m2 m3 m4 m5)
                                  (zz_big m2 m3 m4 m5)) ==
                 (zz_coef n j m0 m1 m2 m3 m4 m5 * gz_Re (zz_big m2 m3 m4 m5))%Q)%Q).
  { destruct (gz_Re_scale (zz_coef n j m0 m1 m2 m3 m4 m5)
                          (zz_big m2 m3 m4 m5)) as [w1 w2 H]. exact H. }
  assert (HRe2 : (gz_Re (gz_scale (zz_coef n j m0 m1 m2 m3 m4 m5)
                                  (zz_big m2 m3 m4 m5)) *
                  gz_Re (gz_scale (zz_coef n j m0 m1 m2 m3 m4 m5)
                                  (zz_big m2 m3 m4 m5)) ==
                 ((zz_coef n j m0 m1 m2 m3 m4 m5 * gz_Re (zz_big m2 m3 m4 m5)) *
                  (zz_coef n j m0 m1 m2 m3 m4 m5 *
                   gz_Re (zz_big m2 m3 m4 m5)))%Q)%Q).
  { rewrite HRe. apply Qeq_refl. }
  apply (qleT_eq_l _ _ _ (Qeq_sym _ _ HRe2)).
  apply (qleT_mul_r_pos _ _ ((Z.of_nat (2 ^ (m4 + m5)) # 1)%Q)).
  - pose proof (match qpos_pow2 (m4 + m5) as H0 in QltT a b return (a < b)%Q with
                | QltT_intro _ _ h => h end) as Hpow.
    exact Hpow.
  - pose proof (match qle_0_qnat1 (2 ^ (m4 + m5)) as H0 in qleT c d
                return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as Hk0.
    eapply qleT_trans.
    + assert (Hreg2 : ((zz_coef n j m0 m1 m2 m3 m4 m5 *
                        gz_Re (zz_big m2 m3 m4 m5)) *
                       (zz_coef n j m0 m1 m2 m3 m4 m5 *
                        gz_Re (zz_big m2 m3 m4 m5)) ==
                      (zz_coef n j m0 m1 m2 m3 m4 m5 *
                       zz_coef n j m0 m1 m2 m3 m4 m5 *
                       (gz_Re (zz_big m2 m3 m4 m5) *
                        gz_Re (zz_big m2 m3 m4 m5)))%Q)%Q)
        by ring.
      assert (HmidQ : ((zz_coef n j m0 m1 m2 m3 m4 m5 *
                        gz_Re (zz_big m2 m3 m4 m5)) *
                       (zz_coef n j m0 m1 m2 m3 m4 m5 *
                        gz_Re (zz_big m2 m3 m4 m5)) <=
                      (zz_coef n j m0 m1 m2 m3 m4 m5 *
                       zz_coef n j m0 m1 m2 m3 m4 m5) *
                      gz_norm (zz_big m2 m3 m4 m5))%Q).
      { rewrite Hreg2.
        pose proof (match Qmult_le_compat_l_spec
                      (gz_Re_sq_le_norm (zz_big m2 m3 m4 m5))
                      (Qsq_nonneg (zz_coef n j m0 m1 m2 m3 m4 m5)) as H0
                    in qleT c d return (c <= d)%Q with
                    | qleT_intro _ _ h => h end) as Hmul.
        exact Hmul. }
      apply (qleT_mul_le_compat_r _ _ _ Hk0 (qleT_of_Qle HmidQ)).
    + assert (Hcl : (gz_norm (zz_big m2 m3 m4 m5) *
                     ((Z.of_nat (2 ^ (m4 + m5))) # 1)%Q ==
                     ((Z.of_nat (5 ^ (m2 + m3 + m4 + m5))) # 1)%Q)%Q).
      { destruct (gz_norm_big_cleared m2 m3 m4 m5) as [w1 w2 H]. exact H. }
      eapply qleT_eq_l.
      assert (Hassoc : (zz_coef n j m0 m1 m2 m3 m4 m5 *
                        zz_coef n j m0 m1 m2 m3 m4 m5 *
                        (gz_norm (zz_big m2 m3 m4 m5) *
                         ((Z.of_nat (2 ^ (m4 + m5))) # 1)%Q) ==
                        zz_coef n j m0 m1 m2 m3 m4 m5 *
                        zz_coef n j m0 m1 m2 m3 m4 m5 *
                        gz_norm (zz_big m2 m3 m4 m5) *
                        ((Z.of_nat (2 ^ (m4 + m5))) # 1)%Q)%Q)
        by ring.
      exact Hassoc.
      eapply qleT_eq_l.
      assert (Hstep1 : (zz_coef n j m0 m1 m2 m3 m4 m5 *
                        zz_coef n j m0 m1 m2 m3 m4 m5 *
                        ((Z.of_nat (5 ^ (m2 + m3 + m4 + m5))) # 1)%Q ==
                        zz_coef n j m0 m1 m2 m3 m4 m5 *
                        zz_coef n j m0 m1 m2 m3 m4 m5 *
                        (gz_norm (zz_big m2 m3 m4 m5) *
                         ((Z.of_nat (2 ^ (m4 + m5))) # 1)%Q))%Q)
        by (rewrite Hcl; apply Qeq_refl).
      exact Hstep1.
      assert (Hconsol : (zz_coef n j m0 m1 m2 m3 m4 m5 *
                          zz_coef n j m0 m1 m2 m3 m4 m5 *
                          ((Z.of_nat (5 ^ (m2 + m3 + m4 + m5))) # 1)%Q ==
                          (((piu_zz_T n (m0, m1, m2, m3, m4, m5) *
                             piu_zz_T n (m0, m1, m2, m3, m4, m5))%Z # 1)%Q *
                           (((Z.of_nat (2 ^ (4 * n + j + m1)) *
                              Z.of_nat (2 ^ (4 * n + j + m1)))%Z # 4)%Q *
                            (((Z.of_nat (5 ^ j) * Z.of_nat (5 ^ j))%Z # 1)%Q *
                             (((Z.of_nat (5 ^ (m2 + m3 + m4 + m5))) # 1))%Q)%Q)%Q)%Q)).
      { unfold zz_coef.
        assert (Hsg : (zz_sign (m1 + m2 + m3 + m4 + m5) *
                       zz_sign (m1 + m2 + m3 + m4 + m5) == (1 # 1)%Q)%Q).
        { destruct (zz_sign_sq (m1 + m2 + m3 + m4 + m5)) as [d1 d2 H]. exact H. }
        assert (HsqT : (((piu_zz_T n (m0, m1, m2, m3, m4, m5)) # 1)%Q *
                        ((piu_zz_T n (m0, m1, m2, m3, m4, m5)) # 1)%Q ==
                        (((piu_zz_T n (m0, m1, m2, m3, m4, m5) *
                           piu_zz_T n (m0, m1, m2, m3, m4, m5))%Z) # 1)%Q)%Q).
        { destruct (qeqT_sq_nat1 (piu_zz_T n (m0, m1, m2, m3, m4, m5)))
            as [e1 e2 H]. exact H. }
        assert (HsqX : (((Z.of_nat (2 ^ (4 * n + j + m1))) # 2)%Q *
                        ((Z.of_nat (2 ^ (4 * n + j + m1))) # 2)%Q ==
                        (((Z.of_nat (2 ^ (4 * n + j + m1)) *
                           Z.of_nat (2 ^ (4 * n + j + m1)))%Z) # 4)%Q)%Q).
        { apply Qeq_refl. }
        assert (HsqY : (((Z.of_nat (5 ^ j)) # 1)%Q *
                        ((Z.of_nat (5 ^ j)) # 1)%Q ==
                        (((Z.of_nat (5 ^ j) * Z.of_nat (5 ^ j))%Z) # 1)%Q)%Q).
        { destruct (qeqT_sq_nat1 (Z.of_nat (5 ^ j))) as [h1 h2 H]. exact H. }
        assert (Hreg : (((zz_sign (m1 + m2 + m3 + m4 + m5) *
                          ((piu_zz_T n (m0, m1, m2, m3, m4, m5)) # 1)%Q *
                          ((Z.of_nat (2 ^ (4 * n + j + m1))) # 2)%Q *
                          ((Z.of_nat (5 ^ j)) # 1)%Q) *
                         (zz_sign (m1 + m2 + m3 + m4 + m5) *
                          ((piu_zz_T n (m0, m1, m2, m3, m4, m5)) # 1)%Q *
                          ((Z.of_nat (2 ^ (4 * n + j + m1))) # 2)%Q *
                          ((Z.of_nat (5 ^ j)) # 1)%Q) *
                         ((Z.of_nat (5 ^ (m2 + m3 + m4 + m5))) # 1)%Q) ==
                        (((zz_sign (m1 + m2 + m3 + m4 + m5) *
                           zz_sign (m1 + m2 + m3 + m4 + m5)) *
                          (((piu_zz_T n (m0, m1, m2, m3, m4, m5)) # 1)%Q *
                           ((piu_zz_T n (m0, m1, m2, m3, m4, m5)) # 1)%Q)) *
                         ((((Z.of_nat (2 ^ (4 * n + j + m1))) # 2)%Q *
                            ((Z.of_nat (2 ^ (4 * n + j + m1))) # 2)%Q) *
                          ((((Z.of_nat (5 ^ j)) # 1)%Q *
                            ((Z.of_nat (5 ^ j)) # 1)%Q) *
                           ((Z.of_nat (5 ^ (m2 + m3 + m4 + m5))) # 1)%Q))))%Q)
          by ring.
        rewrite Hreg. rewrite Hsg. rewrite !Qmult_1_l.
        rewrite HsqT. rewrite HsqX. rewrite HsqY.
        apply Qeq_refl. }
      eapply qleT_eq_l. exact (Qeq_sym _ _ Hconsol).
      apply qleT_intro. unfold Qle. cbn [Qnum Qden Qmult].
      rewrite !Z.mul_1_r.
      change (Z.pos (1 * (4 * (1 * 1))%positive)) with (Z.of_nat 4).
      unfold piu_zz_T. rewrite <- !Nat2Z.inj_mul.
      apply (proj1 (Nat2Z.inj_le _ _)).
      pose proof (zz_master_nat_le n j m0 m1 m2 m3 m4 m5
                    (proj2 (Nat.leb_le _ _) Hj)
                    (proj2 (Nat.eqb_eq _ _) Hsum)) as Hmaster.
      eapply Nat.le_trans;
        [ apply (proj1 (Nat.leb_le _ _)); exact Hmaster
        | apply Nat.le_mul_r; lia ].
Qed.

(* ------------------------------------------------------------------ *)
(* Crude bound, step 2: from per-term to the whole sum                 *)
(* ------------------------------------------------------------------ *)

Lemma zz_lsum_Re_triangle : forall L : list gz,
  qleT (Qabs (gz_Re (gz_lsum L))) (zz_Qsum (map (fun t => Qabs (gz_Re t)) L)).
Proof.
  induction L as [| t L IH].
  - apply qleT_intro. cbn [gz_lsum gz_Re map zz_Qsum fold_right Qabs].
    apply Qle_refl.
  - destruct t as [ta tb].
    eapply qleT_trans.
    + assert (Heq : (Qabs (ta + gz_Re (gz_lsum L)) ==
                     Qabs (gz_Re (gz_lsum ((ta, tb) :: L))))%Q).
      { assert (Hadd : (gz_Re (gz_add (ta, tb) (gz_lsum L)) ==
                        (gz_Re (ta, tb) + gz_Re (gz_lsum L))%Q)%Q).
        { destruct (gz_Re_add (ta, tb) (gz_lsum L)) as [w1 w2 H3]. exact H3. }
        rewrite Hadd. cbn [gz_Re]. apply Qeq_refl. }
      apply (qleT_eq_l _ _ _ Heq). apply qleT_intro. apply Qabs_triangle.
    + pose proof (match IH as H0 in qleT c d return (c <= d)%Q with
                  | qleT_intro _ _ h => h end) as IHle.
      cbn [map zz_Qsum fold_right gz_Re].
      apply qleT_intro. apply Qplus_le_compat; [ apply Qle_refl | exact IHle ].
Qed.

Lemma zz_Qsum_abs_le : forall (L : list gz) (B : Q),
  (forall t, In t L -> qleT (Qabs (gz_Re t)) B) ->
  qleT (zz_Qsum (map (fun t => Qabs (gz_Re t)) L))
       ((B * (Z.of_nat (length L) # 1))%Q).
Proof.
  induction L as [| t L IH]; intros B Hall.
  - apply qleT_intro. cbn [zz_Qsum map length fold_right]. rewrite Nat2Z.inj_0.
    rewrite Qmult_0_r. apply Qle_refl.
  - destruct t as [ta tb].
    cbn [zz_Qsum map length fold_right]. cbn [gz_Re].
    pose proof (match Hall (ta, tb) (or_introl eq_refl) as H0 in qleT c d
                return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as Ha.
    cbn [gz_Re] in Ha.
    assert (Hrest : qleT (zz_Qsum (map (fun u => Qabs (gz_Re u)) L))
                         ((B * (Z.of_nat (length L) # 1))%Q)).
    { apply IH. intros u Hu. apply Hall. right. exact Hu. }
    pose proof (match Hrest as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as Hrest'.
    apply qleT_intro.
    eapply Qle_trans; [ apply Qplus_le_compat; [ exact Ha | apply Qle_refl ] | ].
    rewrite Nat2Z.inj_succ.
    assert (Hsucc : forall z : Z, (Z.succ z # 1)%Q == ((z # 1)%Q + 1)%Q).
    { intros z. unfold Qeq, Qplus. cbn [Qnum Qden Pos.mul]. lia. }
    rewrite Hsucc.
    rewrite Qmult_plus_distr_r. rewrite Qmult_1_r.
    rewrite (Qplus_comm (B * (Z.of_nat (length L) # 1)) B).
    apply Qplus_le_compat; [ apply Qle_refl | exact Hrest' ].
Qed.

Lemma zz_chain5_le_pow : forall n : nat,
  (Nat.leb ((2 * n + 1) * ((2 * n + 1) * ((2 * n + 1) * ((2 * n + 1) * (2 * n + 1)))))
           (2 ^ (10 * n))) = true.
Proof.
  intros n. apply (proj2 (Nat.leb_le _ _)).
  assert (Hb : (2 * n + 1 <= 2 ^ (2 * n))%nat).
  { induction n as [| n IH].
    - cbn [Nat.mul Nat.pow Nat.add]. lia.
    - replace (2 * S n)%nat with (S (S (2 * n)))%nat by lia.
      rewrite !Nat.pow_succ_r'.
      replace (2 * (2 * 2 ^ (2 * n)))%nat with (4 * 2 ^ (2 * n))%nat by lia.
      assert (Hmul : (4 * (2 * n + 1) <= 4 * 2 ^ (2 * n))%nat).
      { apply Nat.mul_le_mono_l. exact IH. }
      assert (Hmid : (S (S (2 * n)) + 1 <= 4 * (2 * n + 1))%nat) by lia.
      eapply Nat.le_trans; [ exact Hmid | exact Hmul ]. }
  eapply Nat.le_trans; [ | ].
  - apply Nat.mul_le_mono; [ exact Hb | ].
    apply Nat.mul_le_mono; [ exact Hb | ].
    apply Nat.mul_le_mono; [ exact Hb | ].
    apply Nat.mul_le_mono; [ exact Hb | exact Hb ].
  - rewrite <- !Nat.pow_add_r.
    replace (2 * n + (2 * n + (2 * n + (2 * n + 2 * n))))%nat
      with (10 * n)%nat by lia.
    apply Nat.pow_le_mono_r; lia.
Qed.

Theorem piu_zz_crude_size : forall n j : nat, (j <= 3 * n)%nat ->
  qleT (Qabs (piu_zz_Aj n j)) ((Z.of_nat (2 ^ (37 * n)) # 1)%Q).
Proof.
  intros n j Hj. unfold piu_zz_Aj. unfold piu_zz_Mj_gz.
  eapply qleT_trans; [ apply zz_lsum_Re_triangle | ].
  assert (Hlen : (length (zz_terms n j) <= 2 ^ (10 * n))%nat).
  { assert (Hml : (length (zz_terms n j) = length (zz_Mj n j))%nat).
    { unfold zz_terms. induction (zz_Mj n j) as [| a L IH];
        cbn [map length]; [ reflexivity | rewrite IH; reflexivity ]. }
    rewrite Hml. pose proof (zz_len5 n j) as HL.
    rewrite !Nat.mul_1_r in HL.
    eapply Nat.le_trans;
      [ apply (proj1 (Nat.leb_le _ _)); exact HL
      | apply (proj1 (Nat.leb_le _ _)); apply zz_chain5_le_pow ]. }
  assert (HB2 : (((Z.of_nat (2 ^ (27 * n))) # 1)%Q * ((Z.of_nat (2 ^ (27 * n))) # 1)%Q ==
                 ((Z.of_nat (2 ^ (54 * n))) # 1)%Q)%Q).
  { assert (Hq : (((Z.of_nat (2 ^ (27 * n))) # 1)%Q * ((Z.of_nat (2 ^ (27 * n))) # 1)%Q ==
                  ((Z.of_nat (2 ^ (27 * n) * 2 ^ (27 * n))) # 1)%Q)%Q).
    { destruct (qeqT_sym _ _ (gz_qZmul1 (2 ^ (27 * n)) (2 ^ (27 * n))))
        as [w1 w2 He]. exact He. }
    assert (Haa : (2 ^ (27 * n) * 2 ^ (27 * n) = 2 ^ (54 * n))%nat).
    { replace (54 * n)%nat with (27 * n + 27 * n)%nat by lia.
      symmetry. apply Nat.pow_add_r. }
    rewrite <- Haa. exact Hq. }
  assert (HperQ : forall m, In m (zz_Mj n j) ->
            (Qabs (gz_Re (zz_term n j m)) <= ((Z.of_nat (2 ^ (27 * n))) # 1)%Q)%Q).
   { intros m Hm. destruct m as [[[[[m0 m1] m2] m3] m4] m5].
    pose proof (zz_Mj_member n j m0 m1 m2 m3 m4 m5
                  (Bid_intro n j m0 m1 m2 m3 m4 m5 Hm)) as Hmem.
    apply Bool.andb_true_iff in Hmem. destruct Hmem as [Hj' Hsum'].
    apply (proj1 (Nat.leb_le _ _)) in Hj'. apply (proj1 (Nat.eqb_eq _ _)) in Hsum'.
    pose proof (match zz_term_sq_le n j m0 m1 m2 m3 m4 m5 Hj' Hsum'
                as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as Ht.
    assert (HCBB : (((Z.of_nat (2 ^ (54 * n))) # 1)%Q <=
                    (((Z.of_nat (2 ^ (27 * n))) # 1)%Q *
                     ((Z.of_nat (2 ^ (27 * n))) # 1)%Q)%Q)%Q).
    { rewrite (Qeq_sym _ _ HB2). apply Qle_refl. }
    pose proof (match sq_le_abs _ _ (qle_0_qnat1 (2 ^ (27 * n)))
                  (qleT_of_Qle (Qle_trans _ _ _ Ht HCBB))
                as H0 in qleT c d return (c <= d)%Q with
                | qleT_intro _ _ h => h end) as Habs.
    exact Habs. }
  assert (Hmid : qleT (zz_Qsum (map (fun t => Qabs (gz_Re t)) (zz_terms n j)))
                      (((Z.of_nat (2 ^ (27 * n))) # 1)%Q *
                       ((Z.of_nat (length (zz_terms n j))) # 1)%Q)).
  { apply (zz_Qsum_abs_le (zz_terms n j) ((Z.of_nat (2 ^ (27 * n))) # 1)%Q).
    intros t Ht.
    assert (HtQ : (Qabs (gz_Re t) <= ((Z.of_nat (2 ^ (27 * n))) # 1)%Q)%Q).
    { apply in_map_iff in Ht. destruct Ht as [m [Heq Hm]].
      subst t. apply HperQ. exact Hm. }
    apply qleT_of_Qle. exact HtQ. }
  eapply qleT_trans; [ exact Hmid | ].
  apply qleT_intro. unfold Qle. cbn [Qnum Qden Qmult].
  rewrite !Z.mul_1_r.
  rewrite <- !Nat2Z.inj_mul.
  assert (Hfin : (2 ^ (27 * n) * length (zz_terms n j) <= 2 ^ (37 * n))%nat).
  { eapply Nat.le_trans; [ | ].
    - apply Nat.mul_le_mono; [ apply Nat.le_refl | exact Hlen ].
    - rewrite <- Nat.pow_add_r. apply Nat.pow_le_mono_r; [ lia | lia ]. }
  apply (proj1 (Nat2Z.inj_le _ _)). exact Hfin.
Qed.

(* ------------------------------------------------------------------ *)
(* Rationality exit and the out-of-range value                         *)
(* ------------------------------------------------------------------ *)

Theorem piu_zz_Aj_rational : forall n j : nat,
  qeqT (piu_zz_Aj n j) (zz_Qsum (map gz_Re (zz_terms n j))).
Proof.
  intros n j. unfold piu_zz_Aj. unfold piu_zz_Mj_gz. apply gz_Re_lsum.
Qed.

Lemma piu_zz_Aj_out : forall n j : nat, (3 * n < j)%nat ->
  qeqT (piu_zz_Aj n j) (0 # 1)%Q.
Proof.
  intros n j H. unfold piu_zz_Aj. unfold piu_zz_Mj_gz.
  unfold zz_terms. unfold zz_Mj.
  apply Nat.leb_gt in H. rewrite H.
  apply qeqT_intro. cbn [gz_lsum gz_Re map]. apply Qeq_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Numeric samples for n = 1 (vm_compute-checked)                      *)
(* ------------------------------------------------------------------ *)

Lemma piu_zz_sample_n1_j0 : qeqT (piu_zz_Aj 1 0) ((-2392) # 1)%Q.
Proof. apply qeqT_intro. vm_compute. reflexivity. Qed.

Lemma piu_zz_sample_n1_j3 : qeqT (piu_zz_Aj 1 3) (8000 # 1)%Q.
Proof. apply qeqT_intro. vm_compute. reflexivity. Qed.

Print Assumptions qleT_of_Qle.
Print Assumptions qleT_trans.
Print Assumptions qleT_eq_l.
Print Assumptions Qmult_le_compat_l_spec.
Print Assumptions qleT_mul_le_compat_r.
Print Assumptions qleT_mul_le_compat_l.
Print Assumptions qleT_mul_r_pos.
Print Assumptions qle_0_qnat1.
Print Assumptions qpos_pow2.
Print Assumptions Qsq_nonneg.
Print Assumptions pos_sq_le.
Print Assumptions sq_le_abs.
Print Assumptions gz_Re_sq_le_norm.
Print Assumptions binomP_le_pow2.
Print Assumptions zz_sign_sq.
Print Assumptions zz_T_nat_le.
Print Assumptions zz_seq_length.
Print Assumptions length_flat_map_seq_le.
Print Assumptions zz_len1.
Print Assumptions zz_len2.
Print Assumptions zz_len3.
Print Assumptions zz_len4.
Print Assumptions zz_len5.
Print Assumptions zz_Mj_member.
Print Assumptions gz_q2pow_step.
Print Assumptions gz_qZmul1.
Print Assumptions qeqT_sq_nat1.
Print Assumptions qeqT_prod4R_nat1.
Print Assumptions gz_norm_pow_1i.
Print Assumptions gz_norm_pow_1j.
Print Assumptions gz_norm_hi.
Print Assumptions gz_norm_hj.
Print Assumptions gz_qhalf2one.
Print Assumptions gz_norm_pow_hi1.
Print Assumptions gz_norm_pow_hj1.
Print Assumptions gz_norm_mul4.
Print Assumptions gz_norm_big_cleared.
Print Assumptions gz_Re_add.
Print Assumptions gz_Re_scale.
Print Assumptions gz_Re_lsum.
Print Assumptions zz_master_nat_le.
Print Assumptions zz_term_sq_le.
Print Assumptions zz_lsum_Re_triangle.
Print Assumptions zz_Qsum_abs_le.
Print Assumptions zz_chain5_le_pow.
Print Assumptions piu_zz_crude_size.
Print Assumptions piu_zz_Aj_rational.
Print Assumptions piu_zz_Aj_out.
Print Assumptions piu_zz_sample_n1_j0.
Print Assumptions piu_zz_sample_n1_j3.
