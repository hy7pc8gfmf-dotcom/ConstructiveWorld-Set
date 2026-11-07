(* ConstructiveWorld-Set -- the Leibniz-series criterion-window boundary module. *)
(** * LW0LeibWindow: criterion-window boundary theorems for the alternating
    Leibniz series, with a computation certifier and the Real-layer glue.

    Mission.  (i) two-sided alternating-remainder bounds with the explicit
      gap [leiblw_gap]; (ii) common-denominator integrality
      ([leiblw_integrality], q'_n := (2n+1)!); (iii) the boundary main
      theorem ([leiblw_dist], [leiblw_dist_set]: the series' own limit x0
      stays at distance >= gap n from every later partial sum); (iv) the
      natural-window residual law, unboundedness, and the escape-window
      obstacle ([leiblw_natwin_residual], [leiblw_escape_obstacle]);
      (c) the Niven-vs-Leibniz separation ([leiblw_family_separation]);
      the certifier ([leiblw_cert]), the Real-layer glue
      ([leiblw_glue_dist]), the true limit ([leiblw_x0]), and the
      [real_lim] connection ([leiblw_S_real_lim]).

    Dependencies.  Stdlib [QArith], [ZArith], [Lia], [Extraction];
      [S01_BaseRing], [S02_CauchyComplete] of this development.

    References.  UpReqIrrationalCriterion.v :237/:242/:247 (lic_* shapes
      restated verbatim in Section 6, shape-only; no Require of the
      criterion body); S02_CauchyComplete.v :48, :399, :468, :859.

    Constructivity.  Zero axiom declarations; positive-form statements
      Set-carried ([sigT] plus the Id + bool form of S02:48); negative-face
      lemmas are Prop scaffolding only; no [arctan], no pi-geometry anywhere.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      LW0LeibWindow.v] compiles cleanly (exit 0); the first eight bytes of
      the artifact are [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import micromega.Lqa.
Require Import S01_BaseRing S02_CauchyComplete.

(* QArith.QArith opens Q_scope by default -- this file keeps nat_scope as the
   default and annotates every Q literal with %Q *)
Local Open Scope nat_scope.

(* ============================================================ *)
(* Section 0. tool layer: parity, Z bridges, a native-Q representation comparator, Qabs lemmas *)
(* ============================================================ *)

Fixpoint leiblw_even (n : nat) : bool :=
  match n with
  | 0 => true
  | Datatypes.S k => negb (leiblw_even k)
  end.


(* the constructive dichotomy k = 2*j or k = 2*j+1 *)
Lemma leiblw_par_decomp : forall k : nat,
  sum (sigT (fun j : nat => k = 2 * j)) (sigT (fun j : nat => k = 2 * j + 1)).
Proof.
  induction k as [|k IH].
  - left. exists 0. reflexivity.
  - destruct IH as [[j Hj]|[j Hj]].
    + right. exists j. rewrite Hj. lia.
    + left. exists (Datatypes.S j). rewrite Hj. lia.
Qed.

(* the Set-valued identity type (the Id shape of S02_CauchyComplete.v :48, provided
   locally: no library dependence) *)
Inductive leiblw_Id {A : Type} (a : A) : A -> Set := leiblw_id_intro : leiblw_Id a a.

Lemma leiblw_id_eq : forall b : bool, b = true -> leiblw_Id b true.
Proof. intros b H. rewrite H. apply leiblw_id_intro. Qed.

(* the generic Set equivalence bridge (carried on the leiblw_Id face, generic in
   A : Type): the statement face keeps the eq-to-Id positive form; the reverse
   direction (Id -> eq) has no named statement (its face has no Set form) -- use
   sites discharge it in place with destruct (<Id fact>); reflexivity (the J
   computation of Id elimination) *)
Lemma leiblw_eq_id : forall (A : Type) (x y : A), x = y -> leiblw_Id x y.
Proof. intros A x y H. rewrite H. apply leiblw_id_intro. Qed.

Lemma leiblw_even_2m : forall m : nat, leiblw_Id (leiblw_even (2 * m)) true.
Proof.
  intros m. apply leiblw_eq_id.
  induction m as [|m IH]; [reflexivity|].
  replace (2 * Datatypes.S m) with (Datatypes.S (Datatypes.S (2 * m))) by lia.
  cbn [leiblw_even]. rewrite IH. reflexivity.
Qed.

Lemma leiblw_even_2m1 : forall m : nat, leiblw_Id (leiblw_even (2 * m + 1)) false.
Proof.
  intros m. apply leiblw_eq_id.
  replace (2 * m + 1) with (Datatypes.S (2 * m)) by lia.
  cbn [leiblw_even].
  assert (H2 : leiblw_even (2 * m) = true).
  { induction m as [|m IH2]; [reflexivity|].
    replace (2 * Datatypes.S m) with (Datatypes.S (Datatypes.S (2 * m))) by lia.
    cbn [leiblw_even]. rewrite IH2. reflexivity. }
  rewrite H2. reflexivity.
Qed.

(* the Set-valued Q strict-order decider (this environment's QArith has no Qlt_bool
   -- a Q comparator provided locally, the S02:48 position) *)
Definition leiblw_Qltb (x y : Q) : bool :=
  match Qcompare x y with Lt => true | _ => false end.

Lemma leiblw_Qltb_true : forall x y : Q, Qlt x y -> leiblw_Id (leiblw_Qltb x y) true.
Proof.
  intros x y H. apply leiblw_id_eq. unfold leiblw_Qltb.
  destruct (Qcompare_spec x y) as [Heq|Hlt'|Hgt].
  - exfalso. unfold Qeq, Qlt in *. cbn [Qnum Qden] in *. nia.
  - reflexivity.
  - exfalso. unfold Qgt, Qlt in *. cbn [Qnum Qden] in *. nia.
Qed.

(* the Z.of_nat positivity bridge (this environment's lia has no zify built in;
   premise 1 <= n -- Z.of_nat 0 = 0 is impossible) *)
Lemma leiblw_znat_pos : forall n : nat, (1 <= n)%nat -> leiblw_Id (Z.ltb 0 (Z.of_nat n)) true.
Proof.
  intros n Hn. apply leiblw_eq_id. apply (proj2 (Z.ltb_lt _ _)).
  destruct n as [|k]; [lia|].
  cbn [Z.of_nat]. apply Pos2Z.is_pos.
Qed.

(* Z.pos (Pos.of_succ_nat k) = k+1 -- reduces every Q denominator to a lia/nia-solvable face *)
Lemma leiblw_pos_succ : forall k : nat, leiblw_Id (Z.pos (Pos.of_succ_nat k)) (Z.of_nat (Datatypes.S k)).
Proof.
  intros k. apply leiblw_eq_id.
  induction k as [|k IH]; [reflexivity|].
  simpl Pos.of_succ_nat. rewrite Pos2Z.inj_succ.
  assert (Heq : Z.pos (Pos.of_succ_nat k) = Z.of_nat (Datatypes.S k))
    by (destruct IH; reflexivity).
  rewrite Heq. lia.
Qed.

(* the linearization tactics: pos_succ (destruct the Id-face fact in place for its
   eq) then the inj family *)
Ltac leiblw_ps k :=
  let H := fresh "Hps" in
  assert (H : Z.pos (Pos.of_succ_nat k) = Z.of_nat (Datatypes.S k))
    by (destruct (leiblw_pos_succ k); reflexivity);
  rewrite H.

Ltac leiblw_zpos_goal :=
  match goal with
  | |- context [Z.pos (Pos.of_succ_nat ?k)] =>
      let H := fresh "Hps" in
      assert (H : Z.pos (Pos.of_succ_nat k) = Z.of_nat (Datatypes.S k))
        by (destruct (leiblw_pos_succ k); reflexivity);
      rewrite H; leiblw_zpos_goal
  | _ => idtac
  end.

Ltac leiblw_zlin := leiblw_zpos_goal;
  rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_add, ?Nat2Z.inj_mul, ?Pos2Z.inj_mul, ?Nat2Z.inj_sub in *.

(* the direct +1 form of pos_succ (bypassing the inj_succ re-reduction of the zlin chain) *)
Lemma leiblw_pos_succ1 : forall k : nat, leiblw_Id (Z.pos (Pos.of_succ_nat k)) (Z.of_nat k + 1)%Z.
Proof. intros k. apply leiblw_eq_id. leiblw_ps k. lia. Qed.

Lemma leiblw_qmake_eq : forall (a b : Z) (p q : positive),
  (a # p)%Q == (b # q)%Q -> leiblw_Id ((a * Z.pos q)%Z) ((b * Z.pos p)%Z).
Proof.
  intros a b p q H. apply leiblw_eq_id. unfold Qeq in H. cbn [Qnum Qden] in H. exact H.
Qed.

Lemma leiblw_qmake_lt : forall (a b : Z) (p q : positive),
  Qlt (a # p)%Q (b # q)%Q -> leiblw_Id (Z.ltb ((a * Z.pos q)%Z) ((b * Z.pos p)%Z)) true.
Proof.
  intros a b p q H. apply leiblw_eq_id. apply (proj2 (Z.ltb_lt _ _)).
  unfold Qlt in H. cbn [Qnum Qden] in H. apply Z.compare_lt_iff in H. exact H.
Qed.

Lemma leiblw_qmake_le : forall (a b : Z) (p q : positive),
  Qle (a # p)%Q (b # q)%Q -> leiblw_Id (Z.leb ((a * Z.pos q)%Z) ((b * Z.pos p)%Z)) true.
Proof.
  intros a b p q H. apply leiblw_eq_id. apply (proj2 (Z.leb_le _ _)).
  unfold Qle in H. cbn [Qnum Qden] in H. apply Z.compare_le_iff in H. exact H.
Qed.

Lemma leiblw_qabs_id : forall q : Q, Qle 0%Q q -> QeqT (Qabs q) q.
Proof.
  intros [z p] H. apply qeq_imp_qeqT. unfold Qle in H. cbn [Qnum Qden] in H.
  cbn [Qabs]. unfold Qeq. cbn [Qnum Qden]. destruct z as [|z'|z'].
  - reflexivity.
  - reflexivity.
  - exfalso. pose proof (Pos2Z.is_pos z') as Hp. simpl in H. lia.
Qed.

Lemma leiblw_qabs_neg : forall q : Q, Qle q 0%Q -> QeqT (Qabs q) (- q)%Q.
Proof.
  intros [z p] H. apply qeq_imp_qeqT. unfold Qle in H. cbn [Qnum Qden] in H.
  cbn [Qabs Qopp]. unfold Qeq. cbn [Qnum Qden]. destruct z as [|z'|z'].
  - reflexivity.
  - exfalso. pose proof (Pos2Z.is_pos z') as Hp. simpl in H. lia.
  - reflexivity.
Qed.

(* ============================================================ *)
(* Section 1. the series itself: t_k := 4*(-1)^k/(2k+1), S_n := Sum_{k<n} t_k *)
(* ============================================================ *)

Definition leiblw_t (k : nat) : Q :=
  if leiblw_even k
  then (4 # Pos.of_succ_nat (2 * k))%Q
  else ((-4) # Pos.of_succ_nat (2 * k))%Q.

Fixpoint leiblw_S (n : nat) : Q :=
  match n with
  | 0 => 0%Q
  | Datatypes.S m => leiblw_S m + leiblw_t m
  end.

Lemma leiblw_S_SS : forall n : nat,
  QeqT (leiblw_S (Datatypes.S (Datatypes.S n))) (leiblw_S n + leiblw_t n + leiblw_t (Datatypes.S n))%Q.
Proof. intros n. apply qeq_imp_qeqT. unfold Qeq. cbn [leiblw_S]. lia. Qed.

Lemma leiblw_S_step : forall n : nat, QeqT (leiblw_S (Datatypes.S n)) (leiblw_S n + leiblw_t n)%Q.
Proof. intros n. apply qeq_imp_qeqT. apply Qeq_refl. Qed.

Lemma leiblw_t_pos_case : forall k : nat,
  leiblw_even k = true -> QeqT (leiblw_t k) (4 # Pos.of_succ_nat (2 * k))%Q.
Proof. intros k H. apply qeq_imp_qeqT. unfold leiblw_t. rewrite H. reflexivity. Qed.

Lemma leiblw_t_neg_case : forall k : nat,
  leiblw_even k = false -> QeqT (leiblw_t k) ((-4) # Pos.of_succ_nat (2 * k))%Q.
Proof. intros k H. apply qeq_imp_qeqT. unfold leiblw_t. rewrite H. reflexivity. Qed.

Lemma leiblw_t_even : forall m : nat,
  QeqT (leiblw_t (2 * m)) (4 # Pos.of_succ_nat (4 * m))%Q.
Proof.
  intros m.
  assert (Hev : leiblw_even (2 * m) = true) by (destruct (leiblw_even_2m m); reflexivity).
  apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_pos_case (2 * m) Hev)) as Htp. rewrite Htp.
  replace (2 * (2 * m)) with (4 * m) by lia. reflexivity.
Qed.

Lemma leiblw_t_odd : forall m : nat,
  QeqT (leiblw_t (2 * m + 1)) ((-4) # Pos.of_succ_nat (4 * m + 2))%Q.
Proof.
  intros m.
  assert (Hev : leiblw_even (2 * m + 1) = false) by (destruct (leiblw_even_2m1 m); reflexivity).
  apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_neg_case (2 * m + 1) Hev)) as Htp. rewrite Htp.
  replace (2 * (2 * m + 1)) with (4 * m + 2) by lia. reflexivity.
Qed.

Lemma leiblw_t_even_pos : forall m : nat, QltT 0%Q (leiblw_t (2 * m))%Q.
Proof.
  intros m. apply Qlt_to_QltT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_even m)) as He. rewrite He.
  unfold Qlt. cbn [Qnum Qden]. apply Z.compare_lt_iff.
  leiblw_zlin.
  assert (0 <= Z.of_nat (4 * m))%Z by apply Nat2Z.is_nonneg. lia.
Qed.

Lemma leiblw_t_odd_neg : forall m : nat, QltT (leiblw_t (2 * m + 1))%Q 0%Q.
Proof.
  intros m. apply Qlt_to_QltT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd m)) as He. rewrite He.
  unfold Qlt. cbn [Qnum Qden]. apply Z.compare_lt_iff.
  leiblw_zlin. lia.
Qed.

(* ============================================================ *)
(* Section 1.5. the Q fraction-algebra working layer: the addition normal form / shunt / comparators *)
(* ============================================================ *)

(* addition normal form: (a#p)+(b#q) == ((a*q'+b*p')#(p*q)) *)
Lemma leiblw_qplus_norm : forall (a b : Z) (p q : positive),
  QeqT ((a # p) + (b # q))%Q ((a * Z.pos q + b * Z.pos p) # (Pos.mul p q))%Q.
Proof.
  intros a b p q. apply qeq_imp_qeqT. unfold Qeq. cbn [Qnum Qden Qplus Qmult Pos.mul].
  rewrite Pos2Z.inj_mul. ring.
Qed.

Lemma leiblw_qplus_lt0 : forall (a b : Z) (p q : positive),
  (0 < a * Z.pos q + b * Z.pos p)%Z -> QltT 0%Q (((a # p) + (b # q))%Q).
Proof.
  intros a b p q H. apply Qlt_to_QltT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qplus_norm a b p q)) as Hn. rewrite Hn.
  unfold Qlt. cbn [Qnum Qden]. apply Z.compare_lt_iff.
  rewrite Z.mul_0_l, Z.mul_1_r. exact H.
Qed.

Lemma leiblw_qplus_lt0b : forall (a b : Z) (p q : positive),
  (a * Z.pos q + b * Z.pos p < 0)%Z -> QltT ((a # p) + (b # q))%Q 0%Q.
Proof.
  intros a b p q H. apply Qlt_to_QltT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qplus_norm a b p q)) as Hn. rewrite Hn.
  unfold Qlt. cbn [Qnum Qden]. apply Z.compare_lt_iff.
  rewrite Z.mul_1_r, Z.mul_0_l. exact H.
Qed.

Lemma leiblw_qplus_le0 : forall (a b : Z) (p q : positive),
  (a * Z.pos q + b * Z.pos p <= 0)%Z -> QleT' (((a # p) + (b # q))%Q) 0%Q.
Proof.
  intros a b p q H. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qplus_norm a b p q)) as Hn. rewrite Hn.
  unfold Qle. cbn [Qnum Qden]. apply Z.compare_le_iff.
  rewrite Z.mul_1_r, Z.mul_0_l. exact H.
Qed.

Lemma leiblw_qplus_eq : forall (a b : Z) (p q : positive) (c : Z) (r : positive),
  ((a * Z.pos q + b * Z.pos p) * Z.pos r = c * Z.pos (Pos.mul p q))%Z ->
  QeqT ((a # p) + (b # q))%Q (c # r)%Q.
Proof.
  intros a b p q c r H. apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qplus_norm a b p q)) as Hn. rewrite Hn.
  unfold Qeq. cbn [Qnum Qden]. exact H.
Qed.

Lemma leiblw_qopp_distr : forall x y : Q, QeqT (-(x + y))%Q ((- x) + (- y))%Q.
Proof.
  intros x y. apply qeq_imp_qeqT. unfold Qeq. cbn [Qnum Qden Qplus Qopp]. ring.
Qed.

(* the normal form with the minus sign: -((a#p)+(b#q)) == (c#r) *)
Lemma leiblw_qneg_plus_eq : forall (a b : Z) (p q : positive) (c : Z) (r : positive),
  (((- a) * Z.pos q + (- b) * Z.pos p) * Z.pos r = c * Z.pos (Pos.mul p q))%Z ->
  QeqT (-((a # p) + (b # q)))%Q (c # r)%Q.
Proof.
  intros a b p q c r H. apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qopp_distr (a # p)%Q (b # q)%Q)) as Hd.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qplus_eq (- a)%Z (- b)%Z p q c r H)) as Hq.
  rewrite Hd. unfold Qopp. cbn [Qnum Qden]. rewrite Hq. apply Qeq_refl.
Qed.

(* shunt: ((A+U)+V)-A == U+V *)
Lemma leiblw_qshunt : forall A U V : Q, QeqT (((A + U) + V) - A)%Q (U + V)%Q.
Proof.
  intros A U V. apply qeq_imp_qeqT. unfold Qminus.
  rewrite <- (Qplus_assoc (A + U)%Q V (- A)%Q).
  rewrite <- (Qplus_assoc A U (V + (- A))%Q).
  rewrite (Qplus_assoc U V (- A)%Q).
  rewrite (Qplus_assoc A (U + V)%Q (- A)%Q).
  rewrite (Qplus_comm A (U + V)%Q).
  rewrite <- (Qplus_assoc (U + V)%Q A (- A)%Q).
  rewrite Qplus_opp_r. apply Qplus_0_r.
Qed.

Lemma leiblw_qplus_opp_l0 : forall A X : Q, QeqT (A + (-(A + X)))%Q (- X)%Q.
Proof. intros A X. apply qeq_imp_qeqT. lra. Qed.

(* the reverse shunt: A-((A+U)+V) == -(U+V) *)
Lemma leiblw_qshunt_neg : forall A U V : Q, QeqT (A - ((A + U) + V))%Q (-(U + V))%Q.
Proof.
  intros A U V. apply qeq_imp_qeqT.
  rewrite <- (Qplus_assoc A U V).
  unfold Qminus. exact (qeqT_imp_qeq _ _ (leiblw_qplus_opp_l0 A (U + V)%Q)).
Qed.

Lemma leiblw_qopp_lt : forall x : Q, Qlt 0%Q x -> QltT (- x)%Q 0%Q.
Proof.
  intros x H. apply Qlt_to_QltT. unfold Qlt in *. cbn [Qnum Qden Qopp] in *. lia.
Qed.

Lemma leiblw_qminus_flip : forall x y : Q, QeqT (y - x)%Q (-(x - y))%Q.
Proof. intros x y. apply qeq_imp_qeqT. lra. Qed.

Lemma leiblw_qle_add_r : forall A U : Q, Qle U 0%Q -> QleT' (A + U)%Q A.
Proof. intros A U H. apply Qle_to_QleT'. lra. Qed.

Lemma leiblw_qle_add2_r : forall A U V : Q, Qle (U + V)%Q 0%Q -> QleT' ((A + U) + V)%Q A.
Proof.
  intros A U V H. apply Qle_to_QleT'.
  assert (H2 : Qle (((A + U) + V) - A)%Q 0%Q)
    by (pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt A U V)) as Hs; rewrite Hs; exact H).
  lra.
Qed.

Lemma leiblw_qle_add_l : forall A W : Q, Qle 0%Q W -> QleT' A (A + W)%Q.
Proof. intros A W H. apply Qle_to_QleT'. lra. Qed.

Lemma leiblw_qplus_le0b : forall (a b : Z) (p q : positive),
  (0 <= a * Z.pos q + b * Z.pos p)%Z -> QleT' 0%Q ((a # p) + (b # q))%Q.
Proof.
  intros a b p q H. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (leiblw_qplus_norm a b p q)) as Hn. rewrite Hn.
  unfold Qle. cbn [Qnum Qden]. apply Z.compare_le_iff.
  rewrite Z.mul_0_l, Z.mul_1_r. exact H.
Qed.

Lemma leiblw_zpos_mul : forall j k : nat,
  leiblw_Id (Z.pos (Pos.mul (Pos.of_succ_nat j) (Pos.of_succ_nat k)))
            (Z.of_nat (Datatypes.S j) * Z.of_nat (Datatypes.S k))%Z.
Proof.
  intros j k. apply leiblw_eq_id. rewrite Pos2Z.inj_mul.
  leiblw_ps j. leiblw_ps k. reflexivity.
Qed.

(* the two-step conversion of an Id-face fact into a Prop-face Z order (destruct
   substitutes immediately when the goal carries the true position) *)
Ltac leiblw_id_inv_in Hx :=
  let T := type of Hx in
  match T with
  | leiblw_Id ?x ?y =>
      let He := fresh "Hid" in
      assert (He : x = y) by (destruct Hx; reflexivity);
      clear Hx; rename He into Hx
  end.

(* an Id-face Z-order fact into a Prop-face Z order (substitute the bool equation
   first, then project through Z.leb_le/Z.ltb_lt) *)
Ltac leiblw_zle_of Hx H :=
  let T := type of Hx in
  match T with
  | leiblw_Id (Z.leb ?a ?b) true =>
      let Hb := fresh "Hb" in
      assert (Hb : Z.leb a b = true) by (destruct Hx; reflexivity);
      assert (H : (a <= b)%Z) by (apply (proj1 (Z.leb_le _ _)); exact Hb);
      clear Hb
  end.

Ltac leiblw_zlt_of Hx H :=
  let T := type of Hx in
  match T with
  | leiblw_Id (Z.ltb ?a ?b) true =>
      let Hb := fresh "Hb" in
      assert (Hb : Z.ltb a b = true) by (destruct Hx; reflexivity);
      assert (H : (a < b)%Z) by (apply (proj1 (Z.ltb_lt _ _)); exact Hb);
      clear Hb
  end.

Ltac leiblw_zpmul j k := let H := fresh "Hzm" in
  assert (H : forall a b : nat,
              Z.pos (Pos.mul (Pos.of_succ_nat a) (Pos.of_succ_nat b)) =
              (Z.of_nat (Datatypes.S a) * Z.of_nat (Datatypes.S b))%Z)
    by (intros a b; destruct (leiblw_zpos_mul a b); reflexivity);
  rewrite (H j k).

(* ============================================================ *)
(* Section 2. (i) the two-sided alternating-remainder bounds: even steps up, odd steps down, interlaced *)
(* ============================================================ *)

Lemma leiblw_step_even_pos : forall m : nat,
  QltT 0%Q (leiblw_S (2 * m + 2) - leiblw_S (2 * m))%Q.
Proof.
  intros m. apply Qlt_to_QltT.
  replace (2 * m + 2) with (Datatypes.S (Datatypes.S (2 * m))) by lia.
  cbn [leiblw_S].
  pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt (leiblw_S (2 * m)) (leiblw_t (2 * m))
                                 (leiblw_t (Datatypes.S (2 * m))))) as Hs. rewrite Hs.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_even m)) as Ht1. rewrite Ht1.
  replace (2 * (2 * m)) with (4 * m) by lia.
  replace (Datatypes.S (2 * m)) with (2 * m + 1) by lia.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd m)) as Ht2. rewrite Ht2.
  apply QltT_to_Qlt. apply leiblw_qplus_lt0.
  leiblw_ps (4 * m). leiblw_ps (4 * m + 2).
  assert (H1 : (Z.of_nat (4 * m) + 2 = Z.of_nat (4 * m + 2))%Z).
  { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  lia.
Qed.

Lemma leiblw_step_odd_neg : forall m : nat,
  QltT (leiblw_S (2 * m + 3) - leiblw_S (2 * m + 1))%Q 0%Q.
Proof.
  intros m. apply Qlt_to_QltT.
  replace (2 * m + 3) with (Datatypes.S (Datatypes.S (2 * m + 1))) by lia.
  cbn [leiblw_S].
  pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt (leiblw_S (2 * m + 1)) (leiblw_t (2 * m + 1))
                                 (leiblw_t (Datatypes.S (2 * m + 1))))) as Hs. rewrite Hs.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd m)) as Ht1. rewrite Ht1.
  replace (Datatypes.S (2 * m + 1)) with (2 * m + 2) by lia.
  replace (2 * m + 2) with (2 * (m + 1)) by lia.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_even (m + 1))) as Ht2. rewrite Ht2.
  replace (4 * (m + 1)) with (4 * m + 4) by lia.
  apply QltT_to_Qlt. apply leiblw_qplus_lt0b.
  leiblw_ps (4 * m + 4). leiblw_ps (4 * m + 2).
  assert (H1 : (Z.of_nat (4 * m + 2) + 2 = Z.of_nat (4 * m + 4))%Z).
  { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  lia.
Qed.

Lemma leiblw_interlace : forall m : nat,
  QleT' (leiblw_S (2 * m + 2)) (leiblw_S (2 * m + 1))%Q.
Proof.
  intros m.
  replace (2 * m + 2) with (Datatypes.S (2 * m + 1)) by lia.
  cbn [leiblw_S].
  apply leiblw_qle_add_r.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd m)) as Ht. rewrite Ht.
  unfold Qle. cbn [Qnum Qden]. apply (proj2 (Z.compare_le_iff _ _)).
  leiblw_ps (4 * m + 2). lia.
Qed.

Lemma leiblw_mono_even : forall j m : nat, (m <= j)%nat ->
  QleT' (leiblw_S (2 * m)) (leiblw_S (2 * j))%Q.
Proof.
  intros j m Hm. apply Qle_to_QleT'. revert Hm.
  induction j as [|j IH]; intros Hm.
  - assert (m = 0) by lia. subst. apply Qle_refl.
  - destruct (Nat.eq_dec m (Datatypes.S j)) as [He|Hne].
    + subst. apply Qle_refl.
    + assert (Hmj : (m <= j)%nat) by lia.
      apply (Qle_trans _ (leiblw_S (2 * j))).
      * apply IH. exact Hmj.
      * replace (2 * Datatypes.S j) with (Datatypes.S (Datatypes.S (2 * j))) by lia.
        cbn [leiblw_S].
        rewrite <- (Qplus_assoc (leiblw_S (2 * j)) (leiblw_t (2 * j)) (leiblw_t (Datatypes.S (2 * j)))).
        assert (H0 : Qle 0%Q (leiblw_t (2 * j) + leiblw_t (Datatypes.S (2 * j)))%Q).
        { replace (Datatypes.S (2 * j)) with (2 * j + 1) by lia.
          pose proof (qeqT_imp_qeq _ _ (leiblw_t_even j)) as H1. setoid_rewrite H1.
          pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd j)) as H2. setoid_rewrite H2.
          replace (2 * (2 * j)) with (4 * j) by lia.
          assert (HZ : (0 <= 4 * Z.pos (Pos.of_succ_nat (4 * j + 2))
                              + (-4) * Z.pos (Pos.of_succ_nat (4 * j)))%Z).
          { leiblw_ps (4 * j). leiblw_ps (4 * j + 2).
            assert (H1z : (Z.of_nat (4 * j) + 2 = Z.of_nat (4 * j + 2))%Z).
            { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
            lia. }
          pose proof (leiblw_qplus_le0b 4%Z (-4)%Z
                        (Pos.of_succ_nat (4 * j)) (Pos.of_succ_nat (4 * j + 2)) HZ) as Hq0.
          exact (QleT'_to_Qle _ _ Hq0). }
        exact (QleT'_to_Qle _ _ (leiblw_qle_add_l (leiblw_S (2 * j))
                                   (leiblw_t (2 * j) + leiblw_t (Datatypes.S (2 * j)))%Q H0)).
Qed.

Lemma leiblw_mono_odd : forall j m : nat, (m <= j)%nat ->
  QleT' (leiblw_S (2 * j + 1)) (leiblw_S (2 * m + 1))%Q.
Proof.
  intros j m Hm. apply Qle_to_QleT'. revert Hm.
  induction j as [|j IH]; intros Hm.
  - assert (m = 0) by lia. subst. apply Qle_refl.
  - destruct (Nat.eq_dec m (Datatypes.S j)) as [He|Hne].
    + subst. apply Qle_refl.
    + assert (Hmj : (m <= j)%nat) by lia.
      apply (Qle_trans _ (leiblw_S (2 * j + 1))).
      * replace (2 * Datatypes.S j + 1) with (Datatypes.S (Datatypes.S (2 * j + 1))) by lia.
        cbn [leiblw_S].
        assert (Huv : Qle (leiblw_t (2 * j + 1) + leiblw_t (Datatypes.S (2 * j + 1)))%Q 0%Q).
        { replace (Datatypes.S (2 * j + 1)) with (2 * (j + 1)) by lia.
          pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd j)) as H1. setoid_rewrite H1.
          pose proof (qeqT_imp_qeq _ _ (leiblw_t_even (j + 1))) as H2. setoid_rewrite H2.
          replace (4 * (j + 1)) with (4 * j + 4) by lia.
          assert (HZ : ((-4) * Z.pos (Pos.of_succ_nat (4 * j + 4))
                        + 4 * Z.pos (Pos.of_succ_nat (4 * j + 2)) <= 0)%Z).
          { leiblw_ps (4 * j + 4). leiblw_ps (4 * j + 2).
            assert (H1z : (Z.of_nat (4 * j + 2) + 2 = Z.of_nat (4 * j + 4))%Z).
            { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
            lia. }
          pose proof (leiblw_qplus_le0 (-4)%Z 4%Z
                        (Pos.of_succ_nat (4 * j + 2)) (Pos.of_succ_nat (4 * j + 4)) HZ) as Hq0.
          exact (QleT'_to_Qle _ _ Hq0). }
        exact (QleT'_to_Qle _ _ (leiblw_qle_add2_r (leiblw_S (2 * j + 1)) _ _ Huv)).
      * apply IH. exact Hmj.
Qed.

(* ============================================================ *)
(* Section 3. the explicit gap: gap n := 8/((2n+1)(2n+3)), the same-side step between adjacent partial sums *)
(* ============================================================ *)

Definition leiblw_gap (n : nat) : Q :=
  (8 # (Pos.mul (Pos.of_succ_nat (2 * n)) (Pos.of_succ_nat (2 * n + 2))))%Q.

Lemma leiblw_gap_pos : forall n : nat, QltT 0%Q (leiblw_gap n).
Proof.
  intros n. apply Qlt_to_QltT. unfold leiblw_gap.
  unfold Qlt. cbn [Qnum Qden]. apply (proj2 (Z.compare_lt_iff _ _)).
  apply Pos2Z.is_pos.
Qed.

Lemma leiblw_gap_even_step : forall m : nat,
  QeqT (leiblw_S (2 * m + 2) - leiblw_S (2 * m))%Q (leiblw_gap (2 * m)).
Proof.
  intros m. apply qeq_imp_qeqT. unfold leiblw_gap.
  replace (2 * m + 2) with (Datatypes.S (Datatypes.S (2 * m))) by lia.
  cbn [leiblw_S].
  pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt (leiblw_S (2 * m)) (leiblw_t (2 * m))
                                 (leiblw_t (Datatypes.S (2 * m))))) as Hs. rewrite Hs.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_even m)) as Hte. setoid_rewrite Hte.
  replace (2 * (2 * m)) with (4 * m) by lia.
  replace (Datatypes.S (2 * m)) with (2 * m + 1) by lia.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd m)) as Hto. setoid_rewrite Hto.
  apply qeqT_imp_qeq. apply leiblw_qplus_eq.
  leiblw_ps (4 * m). leiblw_ps (4 * m + 2).
  assert (Hw : (Z.pos (Pos.mul (Pos.of_succ_nat (4 * m)) (Pos.of_succ_nat (4 * m + 2))) =
                Z.of_nat (4 * m + 1) * Z.of_nat (4 * m + 3))%Z)
    by (leiblw_zpmul (4 * m) (4 * m + 2); f_equal; lia).
  rewrite Hw.
  assert (H1 : (Z.of_nat (4 * m) + 2 = Z.of_nat (4 * m + 2))%Z).
  { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  assert (H2 : (Z.of_nat (4 * m) + 1 = Z.of_nat (4 * m + 1))%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  assert (H3 : (Z.of_nat (4 * m + 2) + 1 = Z.of_nat (4 * m + 3))%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  nia.
Qed.

Lemma leiblw_gap_odd_step : forall m : nat,
  QeqT (leiblw_S (2 * m + 1) - leiblw_S (2 * m + 3))%Q (leiblw_gap (2 * m + 1)).
Proof.
  intros m. apply qeq_imp_qeqT. unfold leiblw_gap.
  replace (2 * m + 3) with (Datatypes.S (Datatypes.S (2 * m + 1))) by lia.
  cbn [leiblw_S].
  pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt_neg (leiblw_S (2 * m + 1)) (leiblw_t (2 * m + 1))
                                   (leiblw_t (Datatypes.S (2 * m + 1))))) as Hs. rewrite Hs.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd m)) as Hto. setoid_rewrite Hto.
  replace (Datatypes.S (2 * m + 1)) with (2 * m + 2) by lia.
  replace (2 * m + 2) with (2 * (m + 1)) by lia.
  pose proof (qeqT_imp_qeq _ _ (leiblw_t_even (m + 1))) as Hte. setoid_rewrite Hte.
  replace (4 * (m + 1)) with (4 * m + 4) by lia.
  replace (2 * (2 * m + 1)) with (4 * m + 2) by lia.
  replace (2 * (2 * m + 1) + 2) with (4 * m + 4) by lia.
  apply qeqT_imp_qeq. apply leiblw_qneg_plus_eq.
  leiblw_ps (4 * m + 4). leiblw_ps (4 * m + 2).
  assert (Hw : (Z.pos (Pos.mul (Pos.of_succ_nat (4 * m + 2)) (Pos.of_succ_nat (4 * m + 4))) =
                Z.of_nat (4 * m + 3) * Z.of_nat (4 * m + 5))%Z)
    by (leiblw_zpmul (4 * m + 2) (4 * m + 4); f_equal; lia).
  rewrite Hw.
  assert (H1 : (Z.of_nat (4 * m + 2) + 2 = Z.of_nat (4 * m + 4))%Z).
  { replace 2%Z with (Z.of_nat 2) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  assert (H2 : (Z.of_nat (4 * m + 2) + 1 = Z.of_nat (4 * m + 3))%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  assert (H3 : (Z.of_nat (4 * m + 4) + 1 = Z.of_nat (4 * m + 5))%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity. rewrite Nat2Z.inj_add. lia. }
  nia.
Qed.

(* ============================================================ *)
(* Section 4. (ii) common-denominator integrality: q'_n := (2n+1)!, q'_n*S_n in Z (witness P_n) *)
(* ============================================================ *)

Fixpoint leiblw_zf (n : nat) : Z :=
  match n with
  | 0 => 1%Z
  | Datatypes.S k => Z.pos (Pos.of_succ_nat k) * leiblw_zf k
  end.

Definition leiblw_qf (n : nat) : Q := (leiblw_zf n # 1)%Q.

Lemma leiblw_zf_ge1 : forall n : nat, leiblw_Id (Z.leb 1 (leiblw_zf n)) true.
Proof.
  intros n. apply leiblw_eq_id. apply (proj2 (Z.leb_le _ _)).
  induction n as [|n IH]; cbn [leiblw_zf].
  - lia.
  - pose proof (Pos2Z.is_pos (Pos.of_succ_nat n)). nia.
Qed.

Lemma leiblw_zf_ge_id : forall n : nat, (1 <= n)%nat ->
  leiblw_Id (Z.leb (Z.of_nat n) (leiblw_zf n)) true.
Proof.
  intros n Hn. apply leiblw_eq_id. apply (proj2 (Z.leb_le _ _)).
  replace n with (Datatypes.S (n - 1)) by lia.
  cbn [leiblw_zf]. leiblw_ps (n - 1).
  assert (Hn' : (1 <= Datatypes.S (n - 1))%nat) by lia.
  assert (Hlt : Z.ltb 0 (Z.of_nat (Datatypes.S (n - 1))) = true)
    by (destruct (leiblw_znat_pos (Datatypes.S (n - 1)) Hn'); reflexivity).
  assert (Hn0 : (0 < Z.of_nat (Datatypes.S (n - 1)))%Z)
    by (apply (proj1 (Z.ltb_lt _ _)); exact Hlt).
  pose proof (leiblw_zf_ge1 (n - 1)) as Hg. leiblw_zle_of Hg H1.
  nia.
Qed.

(* the one-step/three-step native unfoldings of zf (2n+k is not a constructor head,
   so replace + cbn is needed) *)
Lemma leiblw_zf_2n1 : forall n : nat,
  leiblw_Id (leiblw_zf (2 * n + 1)) (Z.pos (Pos.of_succ_nat (2 * n)) * leiblw_zf (2 * n))%Z.
Proof.
  intros n. apply leiblw_eq_id.
  replace (2 * n + 1) with (Datatypes.S (2 * n)) by lia.
  cbn [leiblw_zf]. reflexivity.
Qed.

(* the native three-factor unfolding of (2n+1)!: zf(2n+3) = (2n+3)*(2n+2)*((2n+1)*zf(2n)) *)
Lemma leiblw_zf_2n3 : forall n : nat,
  leiblw_Id (leiblw_zf (2 * n + 3))
            (Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n)))) *
             (Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n))) *
              (Z.pos (Pos.of_succ_nat (2 * n)) * leiblw_zf (2 * n))))%Z.
Proof.
  intros n. apply leiblw_eq_id.
  replace (2 * n + 3) with (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) by lia.
  cbn [leiblw_zf]. reflexivity.
Qed.

Ltac leiblw_zf21 n := let H := fresh "Hzf" in
  assert (H : forall x : nat,
              leiblw_zf (2 * x + 1) = (Z.pos (Pos.of_succ_nat (2 * x)) * leiblw_zf (2 * x))%Z)
    by (intros x; destruct (leiblw_zf_2n1 x); reflexivity);
  rewrite (H n).
Ltac leiblw_zf21_in n Hx := let H := fresh "Hzf" in
  assert (H : forall x : nat,
              leiblw_zf (2 * x + 1) = (Z.pos (Pos.of_succ_nat (2 * x)) * leiblw_zf (2 * x))%Z)
    by (intros x; destruct (leiblw_zf_2n1 x); reflexivity);
  rewrite (H n) in Hx.
Ltac leiblw_zf23 n := let H := fresh "Hzf" in
  assert (H : forall x : nat,
              leiblw_zf (2 * x + 3) =
              (Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * x)))) *
               (Z.pos (Pos.of_succ_nat (Datatypes.S (2 * x))) *
                (Z.pos (Pos.of_succ_nat (2 * x)) * leiblw_zf (2 * x))))%Z)
    by (intros x; destruct (leiblw_zf_2n3 x); reflexivity);
  rewrite (H n).
Theorem leiblw_integrality : forall n : nat,
  sigT (fun p : Z => (leiblw_qf (2 * n + 1) * leiblw_S n)%Q == (p # 1)%Q).
Proof.
  induction n as [|n IH].
  - exists 0%Z. unfold leiblw_qf. cbn [leiblw_zf leiblw_S].
    unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. lia.
  - destruct IH as [p Hp].
    replace (2 * Datatypes.S n + 1) with (2 * n + 3) by lia.
    unfold leiblw_qf in Hp. leiblw_zf21_in n Hp.
    destruct (leiblw_even n) eqn:Hev.
    + exists (Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n)))) *
              (Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n))) *
               (p + 4 * leiblw_zf (2 * n)))%Z)%Z.
      cbn [leiblw_S]. pose proof (qeqT_imp_qeq _ _ (leiblw_t_pos_case n Hev)) as Htp. setoid_rewrite Htp.
      unfold leiblw_qf at 1. leiblw_zf23 n.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) Hp) as Hp2.
      rewrite Z.mul_1_r in Hp2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) +
                     (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite Hp2. ring.
    + exists (Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n)))) *
              (Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n))) *
               (p - 4 * leiblw_zf (2 * n)))%Z)%Z.
      cbn [leiblw_S]. pose proof (qeqT_imp_qeq _ _ (leiblw_t_neg_case n Hev)) as Htp. setoid_rewrite Htp.
      unfold leiblw_qf at 1. leiblw_zf23 n.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) Hp) as Hp2.
      rewrite Z.mul_1_r in Hp2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) -
                     (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite Hp2. ring.
Qed.

(* ============================================================ *)
(* Section 5. (iii) the boundary main theorem: distance >= gap n (one lemma per branch)
   plus the Set-face eps-def packaging *)
(* ============================================================ *)

(* even side, k even: j >= m+1 gives S_{2j} - S_{2m} >= gap(2m) *)
Lemma leiblw_lower_even_e : forall j m : nat, (m + 1 <= j)%nat ->
  QleT' (leiblw_gap (2 * m)) (leiblw_S (2 * j) - leiblw_S (2 * m))%Q.
Proof.
  intros j m Hj. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (leiblw_gap_even_step m)) as Hg. rewrite <- Hg.
  replace (2 * m + 2) with (2 * (m + 1)) by lia.
  assert (Hme : Qle (leiblw_S (2 * (m + 1))) (leiblw_S (2 * j)))
    by (apply QleT'_to_Qle; apply leiblw_mono_even; lia).
  lra.
Qed.

(* even side, k odd: j >= m gives S_{2j+1} - S_{2m} >= gap(2m) *)
Lemma leiblw_lower_even_o : forall j m : nat, (m <= j)%nat ->
  QleT' (leiblw_gap (2 * m)) (leiblw_S (2 * j + 1) - leiblw_S (2 * m))%Q.
Proof.
  intros j m Hj. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (leiblw_gap_even_step m)) as Hg. rewrite <- Hg.
  assert (Hme : Qle (leiblw_S (2 * m + 2)) (leiblw_S (2 * j + 2))).
  { replace (2 * m + 2) with (2 * (m + 1)) by lia.
    replace (2 * j + 2) with (2 * (j + 1)) by lia.
    apply QleT'_to_Qle. apply leiblw_mono_even. lia. }
  assert (Hi : Qle (leiblw_S (2 * j + 2)) (leiblw_S (2 * j + 1)))
    by (apply QleT'_to_Qle; apply leiblw_interlace).
  lra.
Qed.

(* odd side, k even: j >= m+1 gives S_{2m+1} - S_{2j} >= gap(2m+1) *)
Lemma leiblw_lower_odd_e : forall j m : nat, (m + 1 <= j)%nat ->
  QleT' (leiblw_gap (2 * m + 1)) ((leiblw_S (2 * m + 1) - leiblw_S (2 * j))%Q).
Proof.
  intros j m Hj. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (leiblw_gap_odd_step m)) as Hstep.
  pose proof (qeqT_imp_qeq _ _ (leiblw_S_step (2 * j))) as Hst.
  assert (Hsyn : (2 * j + 1 = Datatypes.S (2 * j))%nat) by lia.
  rewrite <- Hsyn in Hst.
  pose proof (QltT_to_Qlt _ _ (leiblw_t_even_pos j)) as Hp.
  pose proof (leiblw_mono_odd j (m + 1) Hj) as Hmo. apply QleT'_to_Qle in Hmo.
  replace (2 * (m + 1) + 1) with (2 * m + 3) in Hmo by lia.
  lra.
Qed.

(* odd side, k odd: j >= m+1 gives S_{2m+1} - S_{2j+1} >= gap(2m+1) *)
Lemma leiblw_lower_odd_o : forall j m : nat, (m + 1 <= j)%nat ->
  QleT' (leiblw_gap (2 * m + 1)) (leiblw_S (2 * m + 1) - leiblw_S (2 * j + 1))%Q.
Proof.
  intros j m Hj. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (leiblw_gap_odd_step m)) as Hg. rewrite <- Hg.
  replace (2 * m + 3) with (2 * (m + 1) + 1) by lia.
  assert (Hle : Qle (leiblw_S (2 * j + 1)) (leiblw_S (2 * (m + 1) + 1)))
    by (apply QleT'_to_Qle; apply leiblw_mono_odd; lia).
  lra.
Qed.

(* the main distance theorem (the Q layer, both branches unified): k >= n+1 gives
   gap n <= |S_k - S_n| *)
Theorem leiblw_dist : forall n k : nat, (Datatypes.S n <= k)%nat ->
  QleT' (leiblw_gap n) (Qabs (leiblw_S k - leiblw_S n))%Q.
Proof.
  intros n k Hk. apply Qle_to_QleT'.
  destruct (leiblw_par_decomp n) as [[m Hm]|Hm].
  - destruct (leiblw_par_decomp k) as [[j Hj]|Hj].
    + assert (Hc : (m + 1 <= j)%nat) by lia.
      pose proof (leiblw_lower_even_e j m Hc) as L. apply QleT'_to_Qle in L.
      assert (Hy : Qle 0%Q ((leiblw_S (2 * j) - leiblw_S (2 * m))%Q)).
      { pose proof (QltT_to_Qlt _ _ (leiblw_gap_pos (2 * m))). lra. }
      pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_id _ Hy)) as E1.
      assert (L2 : Qle (leiblw_gap (2 * m))
                       (Qabs ((leiblw_S (2 * j) - leiblw_S (2 * m))%Q))) by lra.
      exact (eq_ind (2 * m)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j)
                 (fun v => Qle (leiblw_gap (2 * m))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
    + destruct Hj as [j Hj].
      assert (Hc : (m <= j)%nat) by lia.
      pose proof (leiblw_lower_even_o j m Hc) as L. apply QleT'_to_Qle in L.
      assert (Hy : Qle 0%Q ((leiblw_S (2 * j + 1) - leiblw_S (2 * m))%Q)).
      { pose proof (QltT_to_Qlt _ _ (leiblw_gap_pos (2 * m))). lra. }
      pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_id _ Hy)) as E1.
      assert (L2 : Qle (leiblw_gap (2 * m))
                       (Qabs ((leiblw_S (2 * j + 1) - leiblw_S (2 * m))%Q))) by lra.
      exact (eq_ind (2 * m)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j + 1)
                 (fun v => Qle (leiblw_gap (2 * m))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
  - destruct Hm as [m Hm].
    destruct (leiblw_par_decomp k) as [[j Hj]|Hj].
    + assert (Hc : (m + 1 <= j)%nat) by lia.
      pose proof (leiblw_lower_odd_e j m Hc) as L0. apply QleT'_to_Qle in L0.
      assert (Hy2 : Qle ((leiblw_S (2 * j) - leiblw_S (2 * m + 1))%Q) 0%Q).
      { pose proof (QltT_to_Qlt _ _ (leiblw_gap_pos (2 * m + 1))). lra. }
      pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_neg _ Hy2)) as E1.
      pose proof (leiblw_qminus_flip (leiblw_S (2 * m + 1)) (leiblw_S (2 * j))) as Hz.
      assert (L2 : Qle (leiblw_gap (2 * m + 1))
                       (Qabs ((leiblw_S (2 * j) - leiblw_S (2 * m + 1))%Q))) by lra.
      exact (eq_ind (2 * m + 1)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j)
                 (fun v => Qle (leiblw_gap (2 * m + 1))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m + 1))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
    + destruct Hj as [j Hj].
      assert (Hc : (m + 1 <= j)%nat) by lia.
      pose proof (leiblw_lower_odd_o j m Hc) as L0. apply QleT'_to_Qle in L0.
      assert (Hy : Qle ((leiblw_S (2 * j + 1) - leiblw_S (2 * m + 1))%Q) 0%Q).
      { pose proof (QltT_to_Qlt _ _ (leiblw_gap_pos (2 * m + 1))). lra. }
      pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_neg _ Hy)) as E1.
      assert (L2 : Qle (leiblw_gap (2 * m + 1))
                       (Qabs ((leiblw_S (2 * j + 1) - leiblw_S (2 * m + 1))%Q))) by lra.
      exact (eq_ind (2 * m + 1)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j + 1)
                 (fun v => Qle (leiblw_gap (2 * m + 1))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m + 1))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
Qed.

(* the Set-valued Q non-strict order decider (a bool decider for <=, the same
   technique as Qltb) *)
Definition leiblw_Qleb (x y : Q) : bool :=
  match Qcompare x y with Gt => false | _ => true end.

Lemma leiblw_Qleb_true : forall x y : Q, Qle x y -> leiblw_Id (leiblw_Qleb x y) true.
Proof.
  intros x y H. apply leiblw_id_eq. unfold leiblw_Qleb.
  destruct (Qcompare_spec x y) as [Heq|Hlt'|Hgt].
  - reflexivity.
  - reflexivity.
  - exfalso. unfold Qgt, Qle in *. cbn [Qnum Qden] in *. nia.
Qed.

(* the Set-face eps-def packaging (the same Id + bool decider shape as
   S02:48; the stdlib QArith has no Qlt_bool -- QArith_base.v only provides
   Qeq_bool/Qle_bool -- so the locally provided [leiblw_Qleb] is the
   implementation; the draft's strict order gap n < |S_k - S_n| is false at
   k = n+2 where equality holds, so the statement takes the non-strict order
   gap n <= |S_k - S_n| per [leiblw_dist] -- a statement-face correction, the
   Set layer unchanged) *)
Theorem leiblw_dist_set : forall n : nat,
  sigT (fun N : nat => forall k : nat, (N <= k)%nat ->
    leiblw_Id (leiblw_Qleb (leiblw_gap n) (Qabs (leiblw_S k - leiblw_S n))) true).
Proof.
  intros n. exists (Datatypes.S n). intros k Hk.
  apply leiblw_Qleb_true.
  apply QleT'_to_Qle. apply leiblw_dist. exact Hk.
Qed.

(* ============================================================ *)
(* Section 6. (iv) the margin-unbounded theorem + the escape-window obstacle theorem;
   the lic interface-shape restatement *)
(* ============================================================ *)

(* margin_n := q'_n*gap_n = 8*(2n)!/(2n+3) (the natural witness-site residual lower
   bound of (ii)+(iii)) *)
Definition leiblw_margin (n : nat) : Q := (leiblw_qf (2 * n + 1) * leiblw_gap n)%Q.

(* -- the remaining Section 6 pieces: the natural certification window
   b*q'_n*|t_n| = 4b*(2n)! (the theorematized form of the observed window
   identity): the residual-law identity, the natural-window lower bound and
   monotonicity, the partial-sum range 0 <= S_n <= 4, (b) the near-limit q
   escape-window obstacle (the window-unreachability main piece), the
   natural-window unboundedness (Set face), the margin unboundedness
   (Set face). -- *)

(* the natural certification window: W b n := 4b*(2n)! (= b*q'_n*|t_n|; the residual
   law below) *)
Definition leiblw_natwin (b n : nat) : Q :=
  (4 * Z.of_nat b * leiblw_zf (2 * n) # 1)%Q.

Lemma leiblw_qabs_make : forall q : Q,
  QeqT (Qabs q) ((Z.abs (Qnum q)) # (Qden q))%Q.
Proof. intros [z p]. apply qeq_imp_qeqT. reflexivity. Qed.

(* the residual law (theorematized): W b n == b*q'_n*|t_n| -- the identity closing
   the observed window *)
Lemma leiblw_natwin_residual : forall b n : nat,
  QeqT (leiblw_natwin b n)%Q
       ((Z.of_nat b # 1) * (leiblw_qf (2 * n + 1) * Qabs (leiblw_t n)))%Q.
Proof.
  intros b n. apply qeq_imp_qeqT. unfold leiblw_natwin, leiblw_qf.
  destruct (leiblw_even n) eqn:Hev.
  - pose proof (qeqT_imp_qeq _ _ (leiblw_t_pos_case n Hev)) as Htp. rewrite Htp.
    unfold Qeq. cbn [Qnum Qden Qmult Qopp Pos.mul Qabs Z.abs].
    leiblw_zf21 n. ring.
  - pose proof (qeqT_imp_qeq _ _ (leiblw_t_neg_case n Hev)) as Htp. rewrite Htp.
    unfold Qeq. cbn [Qnum Qden Qmult Qopp Pos.mul Qabs Z.abs].
    leiblw_zf21 n. ring.
Qed.

Lemma leiblw_natwin_ge : forall b n : nat,
  (1 <= b)%nat -> QleT' (4 # 1)%Q (leiblw_natwin b n).
Proof.
  intros b n Hb. apply Qle_to_QleT'. unfold leiblw_natwin.
  unfold Qle. cbn [Qnum Qden]. apply (proj2 (Z.compare_le_iff _ _)).
  pose proof (leiblw_znat_pos b Hb) as Hpz. leiblw_zlt_of Hpz Hp.
  pose proof (leiblw_zf_ge1 (2 * n)) as Hfz. leiblw_zle_of Hfz Hf.
  nia.
Qed.

Lemma leiblw_natwin_mono : forall b n : nat,
  QleT' (leiblw_natwin b n) (leiblw_natwin b (Datatypes.S n)).
Proof.
  intros b n. apply Qle_to_QleT'. unfold leiblw_natwin.
  unfold Qle. cbn [Qnum Qden]. apply (proj2 (Z.compare_le_iff _ _)).
  rewrite !Z.mul_1_r.
  replace (2 * Datatypes.S n) with (Datatypes.S (Datatypes.S (2 * n))) by lia.
  cbn [leiblw_zf].
  leiblw_ps (Datatypes.S (2 * n)). leiblw_ps (2 * n).
  pose proof (Nat2Z.is_nonneg (Datatypes.S (Datatypes.S (2 * n)))) as Ha.
  pose proof (Nat2Z.is_nonneg (Datatypes.S (2 * n))) as Hc.
  pose proof (leiblw_zf_ge1 (2 * n)) as Hfz. leiblw_zle_of Hfz Hf.
  pose proof (Nat2Z.is_nonneg b) as Hd.
  nia.
Qed.

(* the partial-sum range: 0 <= S_n <= 4 (S_1 = 4 is the largest partial sum) --
   fuel for the obstacle theorem *)
Lemma leiblw_S1_4 : QeqT (leiblw_S 1) (4 # 1)%Q.
Proof. apply qeq_imp_qeqT. cbn [leiblw_S leiblw_t leiblw_even]. reflexivity. Qed.

Lemma leiblw_S_le4 : forall n : nat, QleT' (leiblw_S n) (4 # 1)%Q.
Proof.
  intros n. apply Qle_to_QleT'. destruct (leiblw_par_decomp n) as [[j Hj]|[j Hj]].
  - rewrite Hj. destruct j as [|j'].
    + replace (2 * 0) with 0 by lia. cbn [leiblw_S]. unfold Qle. cbn [Qnum Qden].
      apply (proj2 (Z.compare_le_iff _ _)). lia.
    + replace (2 * Datatypes.S j') with (Datatypes.S (2 * j' + 1)) by lia.
      cbn [leiblw_S].
      assert (Ht : Qle (leiblw_t (2 * j' + 1)) 0%Q).
      { pose proof (qeqT_imp_qeq _ _ (leiblw_t_odd j')) as Hto. rewrite Hto.
        assert (Hb : Z.leb ((-4) * Z.pos 1)
                           (0 * Z.pos (Pos.of_succ_nat (4 * j' + 2))) = true)
          by (leiblw_ps (4 * j' + 2); lia).
        unfold Qle. cbn [Qnum Qden].
        apply (proj1 (Z.compare_le_iff _ _)). apply (proj1 (Z.leb_le _ _)). exact Hb. }
      pose proof (leiblw_mono_odd j' 0 (Nat.le_0_l j')) as Hm. apply QleT'_to_Qle in Hm.
      replace (2 * 0 + 1) with 1 in Hm by lia.
      pose proof (qeqT_imp_qeq _ _ leiblw_S1_4) as Hs1.
      lra.
  - pose proof (leiblw_mono_odd j 0 (Nat.le_0_l j)) as Hm. apply QleT'_to_Qle in Hm.
    replace (2 * 0 + 1) with 1 in Hm by lia.
    rewrite Hj.
    pose proof (qeqT_imp_qeq _ _ leiblw_S1_4) as Hs1.
    lra.
Qed.

Lemma leiblw_S_ge0 : forall n : nat, QleT' 0%Q (leiblw_S n).
Proof.
  intros n. apply Qle_to_QleT'. destruct (leiblw_par_decomp n) as [[j Hj]|[j Hj]].
  - rewrite Hj. pose proof (leiblw_mono_even j 0 (Nat.le_0_l j)) as Hm.
    apply QleT'_to_Qle in Hm.
    assert (H0 : leiblw_S (2 * 0) == 0%Q) by reflexivity.
    lra.
  - rewrite Hj. pose proof (leiblw_interlace j) as Hi. apply QleT'_to_Qle in Hi.
    pose proof (leiblw_mono_even (j + 1) 0 (Nat.le_0_l (j + 1))) as Hm.
    apply QleT'_to_Qle in Hm.
    replace (2 * (j + 1)) with (2 * j + 2) in Hm by lia.
    assert (H0 : leiblw_S (2 * 0) == 0%Q) by reflexivity.
    lra.
Qed.

(* |x| <= c: two-sided squeezing (the three pointwise Qabs cases, no classical decision) *)
Lemma leiblw_qabs_bound : forall x c : Q,
  Qle x c -> Qle (- x)%Q c -> QleT' (Qabs x) c.
Proof.
  intros x c H1 H2. apply Qle_to_QleT'.
  destruct x as [z p]. cbn [Qabs]. cbn [Qopp] in H2.
  destruct z as [|z'|z']; [exact H1 | exact H1 | exact H2].
Qed.

(* (b) the window-unreachability main piece, the escape-window obstacle for
   near-limit q: when q lies inside the m-th envelope [S_{2m+2}, S_{2m+1}],
   |q - S_n| <= 4 < 8 <= W b n (2 <= b) holds for every n -- the escape is
   unreachable under the natural window.
   (a Prop-scaffolding face: a negative statement has no Set form; the Set
   delivery face = [leiblw_dist_set] / [leiblw_natwin_unbounded] /
   [leiblw_margin_unbounded]) *)
Theorem leiblw_escape_obstacle : forall (b m : nat) (q : Q), (2 <= b)%nat ->
  Qle (leiblw_S (2 * m + 2)) q -> Qle q (leiblw_S (2 * m + 1)) ->
  forall n : nat, QleT' (Qabs ((q - leiblw_S n)%Q)) (leiblw_natwin b n).
Proof.
  intros b m q Hb Hlo Hhi n.
  assert (Hb1 : (1 <= b)%nat) by lia.
  pose proof (leiblw_natwin_ge b n Hb1) as Hw.
  assert (Hq4 : Qle q (4 # 1)%Q).
  { pose proof (leiblw_mono_odd m 0 (Nat.le_0_l m)) as Hm. apply QleT'_to_Qle in Hm.
    replace (2 * 0 + 1) with 1 in Hm by lia.
    pose proof (qeqT_imp_qeq _ _ leiblw_S1_4) as Hs1.
    lra. }
  assert (Hq0 : Qle 0%Q q).
  { pose proof (leiblw_interlace m) as Hi. apply QleT'_to_Qle in Hi.
    pose proof (leiblw_mono_even (m + 1) 0 (Nat.le_0_l (m + 1))) as Hm.
    apply QleT'_to_Qle in Hm.
    replace (2 * (m + 1)) with (2 * m + 2) in Hm by lia.
    assert (H0 : leiblw_S (2 * 0) == 0%Q) by reflexivity.
    lra. }
  assert (Hs4 : Qle (leiblw_S n) (4 # 1)%Q) by (apply QleT'_to_Qle; apply leiblw_S_le4).
  assert (Hs0 : Qle 0%Q (leiblw_S n)) by (apply QleT'_to_Qle; apply leiblw_S_ge0).
  apply Qle_to_QleT'. apply (Qle_trans _ (4 # 1)%Q).
  - assert (Hb2 : QleT' (Qabs ((q - leiblw_S n)%Q)) (4 # 1)%Q).
    { apply leiblw_qabs_bound.
      + lra.
      + pose proof (qeqT_imp_qeq _ _ (leiblw_qminus_flip q (leiblw_S n))) as Hz.
        rewrite <- Hz. lra. }
    exact (QleT'_to_Qle _ _ Hb2).
  - exact (QleT'_to_Qle _ _ Hw).
Qed.

(* (iv) the natural window unbounded (Set face): any nat bound B is exceeded
   by the natural window at n := S (B+B) -- zf(2n) >= 2n >= B+1 > B and
   4b >= 4 *)
Theorem leiblw_natwin_unbounded : forall b B : nat, (1 <= b)%nat ->
  sigT (fun n : nat =>
    leiblw_Id (leiblw_Qltb ((Z.of_nat B # 1)%Q) (leiblw_natwin b n)) true).
Proof.
  intros b B Hb. exists (Datatypes.S (B + B)).
  apply leiblw_Qltb_true.
  unfold leiblw_natwin.
  unfold Qlt. cbn [Qnum Qden]. apply (proj2 (Z.compare_lt_iff _ _)).
  assert (H1 : (1 <= 2 * Datatypes.S (B + B))%nat) by lia.
  pose proof (leiblw_zf_ge_id (2 * Datatypes.S (B + B)) H1) as Hfz. leiblw_zle_of Hfz Hf.
  pose proof (leiblw_znat_pos b Hb) as Hpz. leiblw_zlt_of Hpz Hp.
  pose proof (Nat2Z.is_nonneg B) as Hnn.
  nia.
Qed.

(* (iv) the margin unbounded (Set face): q'_n*gap_n >= n+1 (n >= 2), any nat
   bound exceeded -- the natural witness-site residual lower bound of
   (ii)+(iii) diverges (the nontrivialized quantitative face) *)
Theorem leiblw_margin_unbounded : forall B : nat,
  sigT (fun n : nat =>
    leiblw_Id (leiblw_Qltb ((Z.of_nat B # 1)%Q) (leiblw_margin n)) true).
Proof.
  intros B. exists (B + 2).
  apply leiblw_Qltb_true.
  unfold leiblw_margin, leiblw_qf, leiblw_gap.
  unfold Qlt. cbn [Qnum Qden]. apply (proj2 (Z.compare_lt_iff _ _)).
  cbn [Qnum Qden Qmult Pos.mul].
  leiblw_zpmul (2 * (B + 2)) (2 * (B + 2) + 2).
  leiblw_zf21 (B + 2).
  assert (Hidx : (2 * (B + 2) = 2 * B + 4)%nat) by lia.
  rewrite Hidx.
  leiblw_ps (2 * B + 4).
  assert (Hidx2 : (2 * B + 4 = Datatypes.S (2 * B + 3))%nat) by lia.
  rewrite Hidx2. cbn [leiblw_zf].
  leiblw_ps (2 * B + 3).
  assert (H1 : (1 <= 2 * B + 3)%nat) by lia.
  pose proof (leiblw_zf_ge_id (2 * B + 3) H1) as Hfz. leiblw_zle_of Hfz Hf3.
  pose proof (Nat2Z.is_nonneg (2 * B + 3)) as Hnn.
  nia.
Qed.

(* -- the lic interface-shape restatement (same shapes as
   UpReqIrrationalCriterion.v :237/:242/:247; the original's Set-order wrapper
   + Prop conjunction become sigT nesting + leiblw_Id here, keeping the Set
   layer with the statement content unchanged verbatim; the deciders use the
   locally provided [leiblw_Qltb] of Section 0) -- *)

Definition leiblw_lic_tail_bounded (x e : nat -> Q) : Set :=
  forall n k : nat, (1 <= n)%nat -> (n <= k)%nat ->
    leiblw_Id (leiblw_Qltb (Qabs ((x k - x n)%Q)) (e n)) true.

Definition leiblw_lic_escape_window (x e : nat -> Q) : Set :=
  forall q : Q,
    sigT (fun n : nat =>
      sigT (fun _ : (1 <= n)%nat =>
        leiblw_Id (leiblw_Qltb (e n) (Qabs ((q - x n)%Q))) true)).

Definition leiblw_lic_vanish (e : nat -> Q) : Set :=
  forall eps : Q, leiblw_Id (leiblw_Qltb 0%Q eps) true ->
    sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
      leiblw_Id (leiblw_Qltb (e n) eps) true).

(* ============================================================ *)
(* Section 7. (c) the family-theorem nontrivialization: the factorial family
   (Niven-type) certification window bounded vs the Leibniz family natural
   window unbounded -- the separation contrast *)
(* ============================================================ *)

(* the factorial-family certification window (Niven type): w_niv n :=
   1/(2n+1) -- the standard form of a certified residual window with
   q*delta <= 1/(2n+1) < 1 (the window shape of criterion-reachable families) *)
Definition leiblw_nivwin (n : nat) : Q := (1 # Pos.of_succ_nat (n + n + 1))%Q.

(* the factorial-family window is always <= 1 (bounded) -- separated from leiblw_natwin_unbounded *)
Theorem leiblw_nivwin_bounded : forall n : nat, QleT' (leiblw_nivwin n) 1%Q.
Proof.
  intros n. apply Qle_to_QleT'. unfold leiblw_nivwin.
  unfold Qle. cbn [Qnum Qden]. apply (proj2 (Z.compare_le_iff _ _)).
  pose proof (Pos2Z.is_pos (Pos.of_succ_nat (n + n + 1))). nia.
Qed.

(* the separation main statement (Set face): the Leibniz natural window already
   exceeds 1 at n = 1 (4*(2*1)! = 8 > 1), while the factorial-family window
   stays <= 1 ([leiblw_nivwin_bounded]) -- the "window <= 1" nontriviality
   criterion is reachable for the Niven family and unreachable for the
   Leibniz family *)
Theorem leiblw_family_separation :
  sigT (fun n : nat => leiblw_Id (leiblw_Qltb 1%Q (leiblw_natwin 1 n)) true).
Proof.
  exists 1. apply leiblw_Qltb_true.
  unfold leiblw_natwin.
  unfold Qlt. cbn [Qnum Qden]. apply (proj2 (Z.compare_lt_iff _ _)).
  replace (2 * 1) with 2 by lia.
  cbn [leiblw_zf Z.of_nat Pos.of_succ_nat]. lia.
Qed.

(* ============================================================ *)
(* Section 8. computation-face spot checks + the Set delivery-face extraction + the global axiom audit (the tail PA) *)
(* ============================================================ *)

(* the margin table, a vm_compute spot check: the first four values of margin n = 8*(2n)!/(2n+3) *)
Lemma leiblw_margin_tbl :
  And (QeqT (leiblw_margin 0) (8 # 3)%Q)
       (And (QeqT (leiblw_margin 1) (16 # 5)%Q)
            (And (QeqT (leiblw_margin 2) (192 # 7)%Q)
                 (QeqT (leiblw_margin 3) (640 # 1)%Q))).
Proof.
  repeat split; vm_compute; apply id_refl.
Qed.

(* the natural-window table spot check: the first four values of W 1 n = 4*(2n)! (the divergence intuition) *)
Lemma leiblw_natwin_tbl :
  And (QeqT (leiblw_natwin 1 0) (4 # 1)%Q)
       (And (QeqT (leiblw_natwin 1 1) (8 # 1)%Q)
            (And (QeqT (leiblw_natwin 1 2) (96 # 1)%Q)
                 (QeqT (leiblw_natwin 1 3) (2880 # 1)%Q))).
Proof.
  repeat split; vm_compute; apply id_refl.
Qed.

(* the Set delivery-face extraction (the extraction-face magic count must be zero;
   on Rocq 9.1 the Extraction Require must come first) *)
From Stdlib Require Import Extraction.
Separate Extraction leiblw_dist_set leiblw_natwin leiblw_gap leiblw_nivwin.

(* the tail Print Assumptions (all Closed under the global context) *)
Print Assumptions leiblw_dist.
Print Assumptions leiblw_integrality.
Print Assumptions leiblw_dist_set.
Print Assumptions leiblw_natwin_residual.
Print Assumptions leiblw_natwin_unbounded.
Print Assumptions leiblw_margin_unbounded.
Print Assumptions leiblw_escape_obstacle.
Print Assumptions leiblw_nivwin_bounded.
Print Assumptions leiblw_family_separation.
Print Assumptions leiblw_margin_tbl.
Print Assumptions leiblw_natwin_tbl.

(* ============================================================ *)
(* Section 9. plan B, the computation certifier (a separate section, leaving
   Sections 0-8 untouched).
   the core is tactic-free: pof/cert_core are pure programs
   (Fixpoint/Definition) proved by vm_compute convergence; the specification
   statements are Set-face (forall n + sigT + product-type conjunction); the
   witness package = the two Q values of the alternating-remainder upper/lower
   bounds + the common-denominator (2n+1)! divisibility witness P_n + the gap
   value. *)
(* ============================================================ *)

(* the P_n common-denominator divisibility witness: a tactic-free Fixpoint
   (mirroring the Section 4 integrality construction step:
   p_{k+1} = (2k+3)*(2k+2)*(p_k +- 4*zf(2k)), the sign by the parity of k) *)
Fixpoint leiblw_pof (n : nat) : Z :=
  match n with
  | 0 => 0%Z
  | Datatypes.S k =>
      Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * k)))) *
      (Z.pos (Pos.of_succ_nat (Datatypes.S (2 * k))) *
       (match leiblw_even k with
        | true => leiblw_pof k + 4 * leiblw_zf (2 * k)
        | false => leiblw_pof k - 4 * leiblw_zf (2 * k)
        end)%Z)
  end.

Ltac leiblw_d2e m := let H := fresh "Hd2" in
  assert (H : Nat.div2 (2 * m) = m) by (apply Nat.div2_double);
  rewrite H.
Ltac leiblw_d2e_in m Hx := let H := fresh "Hd2" in
  assert (H : Nat.div2 (2 * m) = m) by (apply Nat.div2_double);
  rewrite H in Hx.
Ltac leiblw_d2o m := let H := fresh "Hd2" in
  assert (H : Nat.div2 (2 * m + 1) = m)
    by (replace (2 * m + 1) with (Datatypes.S (2 * m)) by lia;
        apply Nat.div2_succ_double);
  rewrite H.

(* the P_n specification (a Set-face statement: induction + a Set-valued IH + Qeq_bool
   computational closure) *)
Lemma leiblw_pof_spec : forall n : nat,
  leiblw_Id (Qeq_bool (leiblw_qf (2 * n + 1) * leiblw_S n) (leiblw_pof n # 1)) true.
Proof.
  induction n as [|n IH].
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    cbn [leiblw_pof leiblw_qf leiblw_zf leiblw_S Qnum Qden Qmult]. lra.
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    leiblw_id_inv_in IH. apply (proj1 (Qeq_bool_iff _ _)) in IH.
    unfold leiblw_qf in IH. leiblw_zf21_in n IH.
    replace (2 * Datatypes.S n + 1) with (2 * n + 3) by lia.
    cbn [leiblw_pof]. destruct (leiblw_even n) eqn:Hev.
    + cbn [leiblw_S]. pose proof (qeqT_imp_qeq _ _ (leiblw_t_pos_case n Hev)) as Htp. setoid_rewrite Htp.
      unfold leiblw_qf at 1. leiblw_zf23 n.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) IH) as IH2.
      rewrite Z.mul_1_r in IH2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) + (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite IH2. ring.
    + cbn [leiblw_S]. pose proof (qeqT_imp_qeq _ _ (leiblw_t_neg_case n Hev)) as Htp. setoid_rewrite Htp.
      unfold leiblw_qf at 1. leiblw_zf23 n.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (Datatypes.S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (Datatypes.S (Datatypes.S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) IH) as IH2.
      rewrite Z.mul_1_r in IH2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) - (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite IH2. ring.
Qed.

(* the certifier core: a pure-data quadruple (the lo lower-bound witness, the hi
   upper-bound witness, P_n, the gap value) -- tactic-free *)
Definition leiblw_cert_core (n : nat) : (Q * (Q * (Z * Q)))%type :=
  (leiblw_S (2 * Nat.div2 n),
   (leiblw_S (2 * Nat.div2 n + 1),
    (leiblw_pof n, leiblw_gap n))).

(* the certifier (form 1: forall n + sigT + product-type conjunction, Set face;
   all three core checks are Id + Qeq_bool) *)
Theorem leiblw_cert : forall n : nat,
  sigT (fun lo : Q =>
    sigT (fun hi : Q =>
      sigT (fun p : Z =>
        sigT (fun g : Q =>
          (leiblw_Id (Qeq_bool ((hi - lo)%Q) (leiblw_t (2 * Nat.div2 n))) true *
           (leiblw_Id (Qeq_bool (leiblw_qf (2 * n + 1) * leiblw_S n) (p # 1)) true *
            leiblw_Id (Qeq_bool (p # 1) (leiblw_qf (2 * n + 1) * leiblw_S n)) true))%type)))).
Proof.
  intros n.
  exists (leiblw_S (2 * Nat.div2 n)).
  exists (leiblw_S (2 * Nat.div2 n + 1)).
  exists (leiblw_pof n). exists (leiblw_gap n).
  split.
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    destruct (leiblw_par_decomp n) as [[m Hm]|[m Hm]].
    + rewrite Hm. leiblw_d2e m.
      replace (2 * m + 1) with (Datatypes.S (2 * m)) by lia.
      cbn [leiblw_S].
      match goal with |- ?G => idtac "TLW208P3:" G end.
      lra.
    + rewrite Hm. leiblw_d2o m.
      replace (2 * m + 1) with (Datatypes.S (2 * m)) by lia.
      cbn [leiblw_S].
      lra.
  - split.
    + exact (leiblw_pof_spec n).
    + apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
      pose proof (leiblw_pof_spec n) as Hps.
      leiblw_id_inv_in Hps. apply (proj1 (Qeq_bool_iff _ _)) in Hps.
      apply Qeq_sym. exact Hps.
Qed.

(* the executable demonstration: a vm_compute convergence record -- three shots n = 1,2,3 *)
Eval vm_compute in (leiblw_cert_core 1).
Eval vm_compute in (leiblw_cert_core 2).
Eval vm_compute in (leiblw_cert_core 3).

(* extraction: the certifier core itself extracts *)
Separate Extraction leiblw_pof leiblw_cert_core.

(* the tail Print Assumptions (the Section 9 face) *)
Print Assumptions leiblw_pof_spec.
Print Assumptions leiblw_cert.

(* ============================================================ *)
(* Section 10. the Real-layer glue segment (the LeibWindow Real-layer glue).
   Mission: to build the Real-layer theorem "the distance from the limit to the
     partial sums is >= the sibling gap" directly on the S02 eps-def face; the
     certifier lo/hi/g feed the eps-def predicate sites directly.
   Dependencies: the Section 9 certifier outputs of this file (the
     [leiblw_cert_core] accessor shape) + the Section 4 alternating-bound stock
     ([leiblw_gap_even_step]/[leiblw_gap_odd_step]/[leiblw_mono_even]/
     [leiblw_mono_odd]/[leiblw_interlace]/[leiblw_qabs_bound]/
     [leiblw_t_even_pos]) + the library face S01_BaseRing/S02_CauchyComplete
     ([Real]/[real_eq]/[real_lt]/[real_const]/[QleT']/[QltT]/[NatLe] =
     [Nat.leb] certificates; the S02 closure coqchk reports the axiom section
     <none>).
   Constructivity: the statement face is entirely Set ([sigT]/[real_lt]/
     [real_eq]/[And]/[QleT']/[QltT]/[leiblw_Id] product types); zero ==/Qeq
     statement atoms, zero lia statement atoms; the nat order = the [NatLe]
     certificate face; Qeq rewriting goes through bool-decider eq rewrites (no
     Prop transport); in-proof Q-layer lra and nat-counting lia follow the
     Sections 0-9 stock technique. Zero axioms (the tail PA adds 8).
   References: S02_CauchyComplete.v :48 (the QltT = Id + bool decider eps-def
     shape), :399 [real_eq], :468 [real_lt], :859 [real_const]; the Section 9
     core check 1 (the width hi-lo = t(2*div2 n)) is re-established on the glue
     supply shape.
   Build: the same recipe as the file header (S01/S02 supplied by the world
     root -Q mapping; no new recipe). *)
(* ============================================================ *)

Require Import S01_BaseRing S02_CauchyComplete.
Local Open Scope nat_scope.

(* -- Section 10.0. the certifier-component accessors: the Real-layer supply shape
   of the Section 9 outputs -- *)
Definition leiblw_env_lo (n : nat) : Q := fst (leiblw_cert_core n).
Definition leiblw_env_hi (n : nat) : Q := fst (snd (leiblw_cert_core n)).
Definition leiblw_env_g (n : nat) : Q := snd (snd (snd (leiblw_cert_core n))).

(* endpoint verification (the leiblw_Id + Qeq_bool face, the Section 9 shape): the
   accessor values equal the partial-sum endpoints / the sibling gap itself *)
Lemma leiblw_env_lo_val : forall n : nat,
  leiblw_Id (Qeq_bool (leiblw_env_lo n) (leiblw_S (2 * Nat.div2 n))) true.
Proof.
  intros n. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
  cbn [leiblw_env_lo leiblw_cert_core fst]. apply Qeq_refl.
Qed.

Lemma leiblw_env_hi_val : forall n : nat,
  leiblw_Id (Qeq_bool (leiblw_env_hi n) (leiblw_S (2 * Nat.div2 n + 1))) true.
Proof.
  intros n. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
  cbn [leiblw_env_hi leiblw_cert_core fst snd]. apply Qeq_refl.
Qed.

Lemma leiblw_env_g_val : forall n : nat,
  leiblw_Id (Qeq_bool (leiblw_env_g n) (leiblw_gap n)) true.
Proof.
  intros n. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
  cbn [leiblw_env_g leiblw_cert_core fst snd]. apply Qeq_refl.
Qed.

(* the Section 9 core check 1 (the width hi-lo = t(2*div2 n)) re-established on the
   glue supply shape -- the certifier use face *)
Lemma leiblw_cert_width_check : forall n : nat,
  leiblw_Id (Qeq_bool ((leiblw_env_hi n - leiblw_env_lo n)%Q)
                       (leiblw_t (2 * Nat.div2 n))) true.
Proof.
  intros n. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
  destruct (leiblw_par_decomp n) as [[m Hm]|[m Hm]].
  - rewrite Hm.
    cbn [leiblw_env_hi leiblw_env_lo leiblw_cert_core fst snd].
    leiblw_d2e m.
    replace (2 * m + 1) with (Datatypes.S (2 * m)) by (symmetry; apply Nat.add_1_r).
    cbn [leiblw_S].
    pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt (leiblw_S (2 * m)) (leiblw_t (2 * m)) 0%Q)) as Hs.
    rewrite (Qplus_0_r (leiblw_S (2 * m) + leiblw_t (2 * m))) in Hs.
    rewrite (Qplus_0_r (leiblw_t (2 * m))) in Hs.
    exact Hs.
  - rewrite Hm.
    cbn [leiblw_env_hi leiblw_env_lo leiblw_cert_core fst snd].
    leiblw_d2o m.
    replace (2 * m + 1) with (Datatypes.S (2 * m)) by (symmetry; apply Nat.add_1_r).
    cbn [leiblw_S].
    pose proof (qeqT_imp_qeq _ _ (leiblw_qshunt (leiblw_S (2 * m)) (leiblw_t (2 * m)) 0%Q)) as Hs.
    rewrite (Qplus_0_r (leiblw_S (2 * m) + leiblw_t (2 * m))) in Hs.
    rewrite (Qplus_0_r (leiblw_t (2 * m))) in Hs.
    exact Hs.
Qed.

(* the Qeq same-value transport (an eq-layer rewrite on the bool-decider face,
   Set-lawful with no Prop transport; Qcompare_comp = the Proper instance of
   QArith_base :537, the same usage as S02 real_const) *)
Lemma leiblw_QltT_comp_l : forall x y z : Q,
  leiblw_Id (Qeq_bool x y) true -> QltT x z -> QltT y z.
Proof.
  intros x y z Hxy H. leiblw_id_inv_in Hxy.
  apply (proj1 (Qeq_bool_iff _ _)) in Hxy.
  unfold QltT, Qlt_bool in *.
  rewrite (Qcompare_comp x y Hxy z z (Qeq_refl z)) in H. exact H.
Qed.

Lemma leiblw_QltT_comp_r : forall x y z : Q,
  leiblw_Id (Qeq_bool y z) true -> QltT x y -> QltT x z.
Proof.
  intros x y z Hyz H. leiblw_id_inv_in Hyz.
  apply (proj1 (Qeq_bool_iff _ _)) in Hyz.
  unfold QltT, Qlt_bool in *.
  rewrite (Qcompare_comp x x (Qeq_refl x) y z Hyz) in H. exact H.
Qed.

Lemma leiblw_QleT'_comp_l : forall x y z : Q,
  leiblw_Id (Qeq_bool x y) true -> QleT' x z -> QleT' y z.
Proof.
  intros x y z Hxy H. leiblw_id_inv_in Hxy.
  apply (proj1 (Qeq_bool_iff _ _)) in Hxy.
  unfold QleT', Qle_bool in *.
  rewrite (Qcompare_comp x y Hxy z z (Qeq_refl z)) in H. exact H.
Qed.

Lemma leiblw_QleT'_comp_r : forall x y z : Q,
  leiblw_Id (Qeq_bool y z) true -> QleT' x y -> QleT' x z.
Proof.
  intros x y z Hyz H. leiblw_id_inv_in Hyz.
  apply (proj1 (Qeq_bool_iff _ _)) in Hyz.
  unfold QleT', Qle_bool in *.
  rewrite (Qcompare_comp x x (Qeq_refl x) y z Hyz) in H. exact H.
Qed.

(* the width-value positivity (used by the (i) width witness): core check 1 times
   t_{2*div2 n} > 0 from stock -- the non-degeneracy certificate of the envelope *)
Lemma leiblw_glue_width_pos : forall m : nat,
  QltT 0%Q ((leiblw_env_hi (2 * m) - leiblw_env_lo (2 * m))%Q).
Proof.
  intros m.
  pose proof (leiblw_cert_width_check (2 * m)) as Hc.
  leiblw_id_inv_in Hc.
  apply (proj1 (Qeq_bool_iff _ _)) in Hc.
  leiblw_d2e_in m Hc.
  apply (leiblw_QltT_comp_r 0%Q (leiblw_t (2 * m))).
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)). symmetry. exact Hc.
  - exact (leiblw_t_even_pos m).
Qed.

(* -- Section 10.1. the eps-def glue lifting bridges (the predicates = the library
   Set faces real_lt/real_eq; the S02 :48 shape) -- *)

(* the lifting bridge, lower side: u j >= c eventually gives
   real_lt (real_const (c-d)) x for every d > 0
   (the delta-contraction construction of "x0 >= c" -- the Real-layer >=
   through the strict eps-def face) *)
Lemma leiblw_lift_low : forall (x : Real) (c : Q),
  sigT (fun N : nat => forall j : nat, NatLe N j -> QleT' c (projT1 x j)) ->
  forall d : Q, QltT 0 d -> real_lt (real_const ((c - d)%Q)) x.
Proof.
  intros x c [N HN] d Hd. unfold real_lt.
  exists (d / 2)%Q. split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l.
    + reflexivity.
    + simpl. apply QltT_to_Qlt. exact Hd.
  - exists N. intros j Hj.
    specialize (HN j Hj). apply QleT'_to_Qle in HN.
    pose proof (QltT_to_Qlt 0 d Hd) as Hdp.
    apply Qlt_to_QltT.
    change (projT1 (real_const ((c - d)%Q)) j) with ((c - d)%Q).
    apply (Qlt_shift_div_r d (2 # 1)%Q ((projT1 x j - (c - d))%Q)).
    + reflexivity.
    + lra.
Qed.

(* the lifting bridge, upper side (mirrored): u j <= c eventually gives real_lt x (real_const (c+d)) *)
Lemma leiblw_lift_high : forall (x : Real) (c : Q),
  sigT (fun N : nat => forall j : nat, NatLe N j -> QleT' (projT1 x j) c) ->
  forall d : Q, QltT 0 d -> real_lt x (real_const ((c + d)%Q)).
Proof.
  intros x c [N HN] d Hd. unfold real_lt.
  exists (d / 2)%Q. split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l.
    + reflexivity.
    + simpl. apply QltT_to_Qlt. exact Hd.
  - exists N. intros j Hj.
    specialize (HN j Hj). apply QleT'_to_Qle in HN.
    pose proof (QltT_to_Qlt 0 d Hd) as Hdp.
    apply Qlt_to_QltT.
    change (projT1 (real_const ((c + d)%Q)) j) with ((c + d)%Q).
    apply (Qlt_shift_div_r d (2 # 1)%Q (((c + d) - projT1 x j)%Q)).
    + reflexivity.
    + lra.
Qed.

(* the lifting bridge, equality (using the library Set face real_eq): u j = c
   eventually (two-sided QleT' certificates) gives real_eq x (real_const c) --
   the same technique as the S02 real_const self-proof (a Qeq_trans chain) *)
Lemma leiblw_lift_eq : forall (x : Real) (c : Q),
  sigT (fun N : nat => forall j : nat, NatLe N j ->
    And (QleT' c (projT1 x j)) (QleT' (projT1 x j) c)) ->
  real_eq x (real_const c).
Proof.
  intros x c [N HN] eps Heps. unfold real_eq.
  exists N. intros j Hj. specialize (HN j Hj). destruct HN as [H1 H2].
  apply QleT'_to_Qle in H1. apply QleT'_to_Qle in H2.
  assert (Hant : projT1 x j == c) by (apply Qle_antisym; [exact H2 | exact H1]).
  assert (Hz : Qabs ((projT1 x j - c)%Q) == 0%Q).
  { setoid_rewrite Hant.
    apply (Qeq_trans _ (Qabs 0%Q) _).
    - apply Qabs_wd. ring.
    - apply (Qeq_trans _ (- 0)%Q _).
      + apply Qabs_neg. apply Qle_refl.
      + apply Qeq_refl. }
  pose proof (QltT_to_Qlt 0 eps Heps) as Hlt0.
  apply Qlt_to_QltT. cbn [real_const projT1].
  setoid_rewrite Hz. exact Hlt0.
Qed.

(* -- Section 10.2. the width witness (3): the column eventually entering the
   envelope gives |x0-lo| <= hi-lo
   -- supported by the Section 4 alternating-bound stock ([leiblw_qabs_bound]);
   the width value carries the Section 9 core check 1 payload -- *)
Lemma leiblw_glue_width : forall (m : nat) (x : Real),
  sigT (fun N : nat => forall j : nat, NatLe N j ->
    And (QleT' (leiblw_env_lo (2 * m)) (projT1 x j))
        (QleT' (projT1 x j) (leiblw_env_hi (2 * m)))) ->
  sigT (fun N0 : nat => forall j : nat, NatLe N0 j ->
    QleT' (Qabs ((projT1 x j - leiblw_env_lo (2 * m))%Q))
          ((leiblw_env_hi (2 * m) - leiblw_env_lo (2 * m))%Q)).
Proof.
  intros m x [N HN]. exists N. intros j Hj.
  specialize (HN j Hj). destruct HN as [Hlo Hhi].
  apply QleT'_to_Qle in Hlo. apply QleT'_to_Qle in Hhi.
  apply leiblw_qabs_bound; lra.
Qed.

(* -- Section 10.3. the main glue theorem: "the distance from the limit to the
   partial sums is >= the sibling gap" -- the certifier lo/hi/g feed the eps-def
   predicate sites directly.
   band-membership assumption = the x0 representing column eventually enters the
   inner band [S_{2m+2}, S_{2m+3}] (the inner band of the m/(m+1) envelope, a
   delimiting property of the limit; lo+g = S_{2m+2} and hi-g = S_{2m+3} by the
   Section 3 gap_even_step/gap_odd_step stock equalities, see the Section 10.4
   band-membership instance):
   the lower side dist(x0, lo) >= env_g(2m), the sibling gap of lo (the
   delta-contraction form of x0 >= lo+gap(2m));
   the upper side dist(x0, hi) >= env_g(2m+1), the sibling gap of hi (the
   delta-contraction form of x0 <= hi-gap(2m+1)). *)
Theorem leiblw_glue_dist : forall (m : nat) (x : Real),
  sigT (fun N : nat => forall j : nat, NatLe N j ->
    And (QleT' ((leiblw_env_lo (2 * m) + leiblw_env_g (2 * m))%Q) (projT1 x j))
        (QleT' (projT1 x j)
               ((leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1))%Q))) ->
  And (forall d : Q, QltT 0 d ->
        real_lt (real_const (((leiblw_env_lo (2 * m) + leiblw_env_g (2 * m)) - d)%Q)) x)
      (forall d : Q, QltT 0 d ->
        real_lt x (real_const (((leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1)) + d)%Q))).
Proof.
  intros m x [N HN].
  assert (Hlow : sigT (fun N0 : nat => forall j : nat, NatLe N0 j ->
            QleT' ((leiblw_env_lo (2 * m) + leiblw_env_g (2 * m))%Q) (projT1 x j))).
  { exists N. intros j Hj. specialize (HN j Hj). destruct HN as [H1 _]. exact H1. }
  assert (Hhigh : sigT (fun N0 : nat => forall j : nat, NatLe N0 j ->
            QleT' (projT1 x j)
                  ((leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1))%Q))).
  { exists N. intros j Hj. specialize (HN j Hj). destruct HN as [_ H2]. exact H2. }
  split.
  - intros d Hd. exact (leiblw_lift_low x _ Hlow d Hd).
  - intros d Hd. exact (leiblw_lift_high x _ Hhigh d Hd).
Qed.

(* -- Section 10.4. the band-membership instance (the nonemptiness witness of the
   glue assumption): the partial-sum column itself eventually enters the inner
   band for j >= 2m+3 -- supplied directly by the (i) alternating-bound stock
   (mono_even/mono_odd/interlace); the equalities lo+g = S_{2m+2} and
   hi-g = S_{2m+3} carried by the Section 3 gap-step stock.
   (the construction of the true-limit Real = the cauchy witness + the
   t_n -> 0 vanishing, a later segment; this file delivers the direct
   "certifier x alternating bounds -> Real layer" connection.) *)
Lemma leiblw_glue_band_S : forall (m j : nat), NatLe (2 * m + 3) j ->
  And (QleT' ((leiblw_env_lo (2 * m) + leiblw_env_g (2 * m))%Q) (leiblw_S j))
      (QleT' (leiblw_S j)
             ((leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1))%Q)).
Proof.
  intros m j Hj. apply NatLe_drop in Hj.
  assert (HvL : leiblw_S (2 * m + 2)
                == (leiblw_env_lo (2 * m) + leiblw_env_g (2 * m))%Q).
  { cbn [leiblw_env_lo leiblw_env_g leiblw_cert_core fst snd].
    leiblw_d2e m.
    pose proof (qeqT_imp_qeq _ _ (leiblw_gap_even_step m)). lra. }
  assert (HvH : (leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1))%Q
                == leiblw_S (2 * m + 3)).
  { cbn [leiblw_env_hi leiblw_env_g leiblw_cert_core fst snd].
    leiblw_d2o m.
    pose proof (qeqT_imp_qeq _ _ (leiblw_gap_odd_step m)). lra. }
  split.
  - apply (leiblw_QleT'_comp_l (leiblw_S (2 * m + 2)));
      [apply leiblw_id_eq; apply (proj2 (Qeq_bool_iff _ _)); exact HvL|].
    apply Qle_to_QleT'.
    destruct (leiblw_par_decomp j) as [[i Hi]|[i Hi]]; rewrite Hi.
    + assert (Hij : (m + 1 <= i)%nat) by lia.
      pose proof (leiblw_mono_even i (m + 1) Hij) as H1. apply QleT'_to_Qle in H1.
      replace (2 * (m + 1)) with (2 * m + 2) in H1 by lia.
      lra.
    + assert (Hij : (m + 1 <= i)%nat) by lia.
      pose proof (leiblw_mono_even i (m + 1) Hij) as H1. apply QleT'_to_Qle in H1.
      pose proof (QltT_to_Qlt _ _ (leiblw_t_even_pos i)) as Ht.
      pose proof (QleT'_to_Qle _ _ (leiblw_qle_add_l (leiblw_S (2 * i)) (leiblw_t (2 * i))
                    (Qlt_le_weak _ _ Ht))) as H3.
      pose proof (qeqT_imp_qeq _ _ (leiblw_S_step (2 * i))) as H4.
      replace (2 * (m + 1)) with (2 * m + 2) in H1 by lia.
      replace (2 * i + 1) with (Datatypes.S (2 * i)) by (symmetry; apply Nat.add_1_r).
      lra.
  - apply (leiblw_QleT'_comp_r (leiblw_S j) (leiblw_S (2 * m + 3)));
      [apply leiblw_id_eq; apply (proj2 (Qeq_bool_iff _ _)); symmetry; exact HvH|].
    apply Qle_to_QleT'.
    destruct (leiblw_par_decomp j) as [[i Hi]|[i Hi]]; rewrite Hi.
    + assert (Hij : (m + 2 <= i)%nat) by lia.
      destruct i as [|i']; [lia|].
      assert (Hij2 : (m + 1 <= i')%nat) by lia.
      pose proof (leiblw_interlace i') as H2. apply QleT'_to_Qle in H2.
      pose proof (leiblw_mono_odd i' (m + 1) Hij2) as H3. apply QleT'_to_Qle in H3.
      replace (2 * (m + 1) + 1) with (2 * m + 3) in H3 by lia.
      replace (2 * Datatypes.S i') with (2 * i' + 2) by lia.
      lra.
    + assert (Hij : (m + 1 <= i)%nat) by lia.
      pose proof (leiblw_mono_odd i (m + 1) Hij) as H3. apply QleT'_to_Qle in H3.
      replace (2 * (m + 1) + 1) with (2 * m + 3) in H3 by lia.
      lra.
Qed.

(* -- Section 10.5. the executable demonstration and the axiom audit -- *)
(* a vm_compute record of the three certifier accessors (cross-checked against
   the Section 9 demonstration values: n=1 -> (0, 4, 8#15),
   n=2 -> (8#3, 52#15, 8#35)) *)
Eval vm_compute in (leiblw_env_lo 1, (leiblw_env_hi 1, leiblw_env_g 1)).
Eval vm_compute in (leiblw_env_lo 2, (leiblw_env_hi 2, leiblw_env_g 2)).

(* the tail Print Assumptions (the Section 10 face; thirteen Closed) *)
Print Assumptions leiblw_cert_width_check.
Print Assumptions leiblw_lift_low.
Print Assumptions leiblw_lift_high.
Print Assumptions leiblw_lift_eq.
Print Assumptions leiblw_glue_width_pos.
Print Assumptions leiblw_glue_width.
Print Assumptions leiblw_glue_band_S.
Print Assumptions leiblw_glue_dist.
(* ============================================================ *)
(* Section 11. the true-limit Real construction (the LeibWindow true-limit
     construction).
   Mission: with the S02 cauchy machinery, construct x0 as the cauchy-real limit
     of the series itself (no claim of pi/4 -- the separation argument only
     needs "how slow this family is", not "what it equals"); the |t_n| -> 0
     vanishing witness is supplied by the Section 4 alternating-remainder bound
     stock; once in place, instantiate [leiblw_glue_dist] + [leiblw_glue_band_S]
     -- the glue assumption is nonempty and the main glue theorem holds for the
     true x0 -- the boundary-theorem line fully through.
   Faces: win_even/odd (the tail envelope two-sided QleT' -- supplied by the
     mono_even/mono_odd/interlace + S_step + t_even_pos stock) + win_width (the
     Id + Qeq_bool width equality = |t_N| itself) + S_pair_win_even/odd +
     S_pair_abs_t (|S_m - S_n| <= |t_N|, using the qabs_bound stock) + t_abs +
     t_vanish (the |t_n| -> 0 vanishing witness: the nat witness
     N := 4*(Qden eps)+1, from 4/(2n+1) < eps through a Z-face monotone chain)
     + S_cauchy (the cauchy machine instance, closed by Qle_lt_trans) + x0 (the
     existT packaging = the cauchy-real limit of the series itself) + x0_proj +
     glue_x0_band (the Section 10.4 band membership instantiated at x0 = the
     glue assumption nonempty) + glue_x0 (the Section 10.3 main glue theorem
     instantiated at the true x0 = the boundary-theorem line fully through) +
     env_lo_2m/env_hi_2m (the Section 10.0 accessor-endpoint 2m specialization
     bridges) + glue_env_x0 + glue_width_x0 (the Section 10.2 width witness
     instantiated at x0 = the (i) width-witness use face).
   Constructivity: the statement face is entirely Set-sanctioned
     ([sigT]/[And]/[QleT']/[QltT]/[leiblw_Id] + [Qeq_bool]/[NatLe]/[cauchy]/
     [Real]/[real_lt]); the new-section statement face has zero ==, zero Qeq
     atoms, zero lia statement atoms; in-proof Q-layer lra/nia and nat-counting
     lia follow the Sections 0-10 stock technique.
   Zero axioms (the tail PA adds 7).
   Micro-check verdicts: Z.to_nat (Z.pos p) as the reference shape,
     Nat2Z.inj_le iff-apply feasibility, Z2Nat.id (Z.pos p), the Qopp double
     negation cbn+lia face, and the vanishing inequality chain closed by one
     nia shot. *)
(* ============================================================ *)

(* -- Section 11.0. the tail envelope (cauchy fuel, supplied directly by the (i)
   alternating-remainder two-sided bound stock): N <= k gives S_k caught in the
   window of width |t_N| -- the even/odd two faces -- *)

Lemma leiblw_win_even : forall j k : nat, NatLe (2 * j) k ->
  And (QleT' (leiblw_S (2 * j)) (leiblw_S k))
      (QleT' (leiblw_S k) (leiblw_S (2 * j + 1))).
Proof.
  intros j k Hk. apply NatLe_drop in Hk.
  destruct (leiblw_par_decomp k) as [[i Hi]|[i Hi]]; subst k.
  - split.
    + apply leiblw_mono_even. lia.
    + apply Qle_to_QleT'. apply (Qle_trans _ (leiblw_S (2 * i + 1))).
      * replace (2 * i + 1) with (Datatypes.S (2 * i)) by lia.
        pose proof (qeqT_imp_qeq _ _ (leiblw_S_step (2 * i))) as Hs. rewrite Hs.
        pose proof (leiblw_qle_add_l (leiblw_S (2 * i)) (leiblw_t (2 * i))
                      (Qlt_le_weak _ _ (QltT_to_Qlt _ _ (leiblw_t_even_pos i)))) as H3.
        exact (QleT'_to_Qle _ _ H3).
      * apply QleT'_to_Qle. apply leiblw_mono_odd. lia.
  - split.
    + apply Qle_to_QleT'. apply (Qle_trans _ (leiblw_S (2 * i))).
      * apply QleT'_to_Qle. apply leiblw_mono_even. lia.
      * replace (2 * i + 1) with (Datatypes.S (2 * i)) by lia.
        pose proof (qeqT_imp_qeq _ _ (leiblw_S_step (2 * i))) as Hs. rewrite Hs.
        pose proof (leiblw_qle_add_l (leiblw_S (2 * i)) (leiblw_t (2 * i))
                      (Qlt_le_weak _ _ (QltT_to_Qlt _ _ (leiblw_t_even_pos i)))) as H3.
        exact (QleT'_to_Qle _ _ H3).
    + apply leiblw_mono_odd. lia.
Qed.

Lemma leiblw_win_odd : forall j k : nat, NatLe (2 * j + 1) k ->
  And (QleT' (leiblw_S (2 * j + 2)) (leiblw_S k))
      (QleT' (leiblw_S k) (leiblw_S (2 * j + 1))).
Proof.
  intros j k Hk. apply NatLe_drop in Hk.
  destruct (leiblw_par_decomp k) as [[i Hi]|[i Hi]]; subst k.
  - split.
    + replace (2 * j + 2) with (2 * (j + 1)) by lia.
      apply leiblw_mono_even. lia.
    + apply Qle_to_QleT'. apply (Qle_trans _ (leiblw_S (2 * i + 1))).
      * replace (2 * i + 1) with (Datatypes.S (2 * i)) by lia.
        pose proof (qeqT_imp_qeq _ _ (leiblw_S_step (2 * i))) as Hs. rewrite Hs.
        pose proof (leiblw_qle_add_l (leiblw_S (2 * i)) (leiblw_t (2 * i))
                      (Qlt_le_weak _ _ (QltT_to_Qlt _ _ (leiblw_t_even_pos i)))) as H3.
        exact (QleT'_to_Qle _ _ H3).
      * apply QleT'_to_Qle. apply leiblw_mono_odd. lia.
  - split.
    + apply Qle_to_QleT'. apply (Qle_trans _ (leiblw_S (2 * i + 2))).
      * replace (2 * j + 2) with (2 * (j + 1)) by lia.
        replace (2 * i + 2) with (2 * (i + 1)) by lia.
        apply QleT'_to_Qle. apply leiblw_mono_even. lia.
      * apply QleT'_to_Qle. apply leiblw_interlace.
    + apply leiblw_mono_odd. lia.
Qed.

(* the envelope-width equality (the Id + Qeq_bool face): the window width =
   |t_N| itself -- the tail-remainder form of the (i) width witness
   (B-A = S_{N+1}-S_N = t_N; the odd branch takes the negative = Qabs) *)
Lemma leiblw_win_width_even : forall j : nat,
  leiblw_Id (Qeq_bool ((leiblw_S (2 * j + 1) - leiblw_S (2 * j))%Q)
                      (Qabs (leiblw_t (2 * j)))) true.
Proof.
  intros j. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
  assert (Hst : leiblw_S (2 * j + 1) == (leiblw_S (2 * j) + leiblw_t (2 * j))%Q).
  { replace (2 * j + 1) with (Datatypes.S (2 * j)) by lia.
    pose proof (leiblw_S_step (2 * j)) as Hs. exact (qeqT_imp_qeq _ _ Hs). }
  apply (Qeq_trans _ (leiblw_t (2 * j)) _).
  - lra.
  - symmetry.
    assert (Htp : Qle 0%Q (leiblw_t (2 * j)))
      by (apply Qlt_le_weak; apply QltT_to_Qlt; apply leiblw_t_even_pos).
    pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_id _ Htp)) as Hab.
    exact Hab.
Qed.

Lemma leiblw_win_width_odd : forall j : nat,
  leiblw_Id (Qeq_bool ((leiblw_S (2 * j + 1) - leiblw_S (2 * j + 2))%Q)
                      (Qabs (leiblw_t (2 * j + 1)))) true.
Proof.
  intros j. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
  assert (Hst : leiblw_S (2 * j + 2) == (leiblw_S (2 * j + 1) + leiblw_t (2 * j + 1))%Q).
  { replace (2 * j + 2) with (Datatypes.S (2 * j + 1)) by lia.
    pose proof (leiblw_S_step (2 * j + 1)) as Hs. exact (qeqT_imp_qeq _ _ Hs). }
  apply (Qeq_trans _ ((- leiblw_t (2 * j + 1))%Q) _).
  - lra.
  - symmetry.
    assert (Htn : Qle (leiblw_t (2 * j + 1)) 0%Q)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; apply leiblw_t_odd_neg).
    pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_neg _ Htn)) as Hab.
    exact Hab.
Qed.

(* -- Section 11.1. the cauchy main fuel: |S_m - S_n| <= |t_N| (two-sided in the
   same window, no triangle inequality) -- *)

Lemma leiblw_S_pair_win_even : forall j m n : nat,
  NatLe (2 * j) m -> NatLe (2 * j) n ->
  QleT' (Qabs ((leiblw_S m - leiblw_S n)%Q)) (Qabs (leiblw_t (2 * j))).
Proof.
  intros j m n Hm Hn.
  destruct (leiblw_win_even j m Hm) as [A1 B1].
  destruct (leiblw_win_even j n Hn) as [A2 B2].
  apply QleT'_to_Qle in A1. apply QleT'_to_Qle in B1.
  apply QleT'_to_Qle in A2. apply QleT'_to_Qle in B2.
  pose proof (leiblw_win_width_even j) as Hw.
  (* Qabs blocks lra: first produce the two-sided Qle with a Qabs-free window width
   D, compose through qabs_bound, then transport by comp_r *)
  assert (Hd1 : Qle ((leiblw_S m - leiblw_S n)%Q)
                    ((leiblw_S (2 * j + 1) - leiblw_S (2 * j))%Q)) by lra.
  assert (Hd2 : Qle ((- (leiblw_S m - leiblw_S n))%Q)
                    ((leiblw_S (2 * j + 1) - leiblw_S (2 * j))%Q)) by lra.
  pose proof (leiblw_qabs_bound _ _ Hd1 Hd2) as Habs.
  apply (leiblw_QleT'_comp_r (Qabs ((leiblw_S m - leiblw_S n)%Q))
                             ((leiblw_S (2 * j + 1) - leiblw_S (2 * j))%Q)).
  - exact Hw.
  - exact Habs.
Qed.

Lemma leiblw_S_pair_win_odd : forall j m n : nat,
  NatLe (2 * j + 1) m -> NatLe (2 * j + 1) n ->
  QleT' (Qabs ((leiblw_S m - leiblw_S n)%Q)) (Qabs (leiblw_t (2 * j + 1))).
Proof.
  intros j m n Hm Hn.
  destruct (leiblw_win_odd j m Hm) as [A1 B1].
  destruct (leiblw_win_odd j n Hn) as [A2 B2].
  apply QleT'_to_Qle in A1. apply QleT'_to_Qle in B1.
  apply QleT'_to_Qle in A2. apply QleT'_to_Qle in B2.
  pose proof (leiblw_win_width_odd j) as Hw.
  assert (Hd1 : Qle ((leiblw_S m - leiblw_S n)%Q)
                    ((leiblw_S (2 * j + 1) - leiblw_S (2 * j + 2))%Q)) by lra.
  assert (Hd2 : Qle ((- (leiblw_S m - leiblw_S n))%Q)
                    ((leiblw_S (2 * j + 1) - leiblw_S (2 * j + 2))%Q)) by lra.
  pose proof (leiblw_qabs_bound _ _ Hd1 Hd2) as Habs.
  apply (leiblw_QleT'_comp_r (Qabs ((leiblw_S m - leiblw_S n)%Q))
                             ((leiblw_S (2 * j + 1) - leiblw_S (2 * j + 2))%Q)).
  - exact Hw.
  - exact Habs.
Qed.

Lemma leiblw_S_pair_abs_t : forall N m n : nat, NatLe N m -> NatLe N n ->
  QleT' (Qabs ((leiblw_S m - leiblw_S n)%Q)) (Qabs (leiblw_t N)).
Proof.
  intros N m n Hm Hn.
  destruct (leiblw_par_decomp N) as [[j HN]|[j HN]]; subst N.
  - apply leiblw_S_pair_win_even; assumption.
  - apply leiblw_S_pair_win_odd; assumption.
Qed.

(* -- Section 11.2. the |t_n| -> 0 vanishing witness (2), supplied directly by the
   Section 4 alternating-remainder bound stock.
   |t_n| = 4/(2n+1) < eps follows from 4*Qden eps < Qnum eps*(2n+1) -- the nat
   witness N := 4*(Qden eps)+1: 2N+1 = 8*den+3 > 4*den (a Z-face monotone chain,
   in the micro-check verdict form) -- *)

Lemma leiblw_t_abs : forall n : nat,
  leiblw_Id (Qeq_bool (Qabs (leiblw_t n)) ((4 # Pos.of_succ_nat (2 * n))%Q)) true.
Proof.
  intros n. destruct (leiblw_even n) eqn:Hev.
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    pose proof (qeqT_imp_qeq _ _ (leiblw_t_pos_case n Hev)) as Htp. setoid_rewrite Htp.
    assert (Hp0 : Qle 0%Q (4 # Pos.of_succ_nat (2 * n))%Q).
    { assert (Hb0 : Z.leb (0 * Z.pos (Pos.of_succ_nat (2 * n))) (4 * Z.pos 1) = true) by lia.
      unfold Qle. cbn [Qnum Qden].
      apply (proj1 (Z.compare_le_iff _ _)). apply (proj1 (Z.leb_le _ _)). exact Hb0. }
    pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_id _ Hp0)) as Hab. exact Hab.
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    pose proof (qeqT_imp_qeq _ _ (leiblw_t_neg_case n Hev)) as Htp. setoid_rewrite Htp.
    assert (Hp1 : Qle ((-4) # Pos.of_succ_nat (2 * n))%Q 0%Q).
    { assert (Hb1 : Z.leb ((-4) * Z.pos 1) (0 * Z.pos (Pos.of_succ_nat (2 * n))) = true) by lia.
      unfold Qle. cbn [Qnum Qden].
      apply (proj1 (Z.compare_le_iff _ _)). apply (proj1 (Z.leb_le _ _)). exact Hb1. }
    pose proof (qeqT_imp_qeq _ _ (leiblw_qabs_neg _ Hp1)) as Han. rewrite Han.
    unfold Qeq. cbn [Qnum Qden Qopp]. lia.
Qed.

Lemma leiblw_t_vanish : forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QltT (Qabs (leiblw_t n)) eps).
Proof.
  intros eps Heps.
  pose proof (QltT_to_Qlt 0 eps Heps) as Hlt.
  destruct eps as [z p]. unfold Qlt in Hlt. cbn [Qnum Qden] in Hlt.
  assert (Hz1 : (1 <= z)%Z) by lia.
  assert (Hp1 : (0 <= Z.pos p)%Z) by apply Pos2Z.is_nonneg.
  exists (Datatypes.S (4 * Z.to_nat (Z.pos p))).
  intros n Hn.
  assert (Hle : (Datatypes.S (4 * Z.to_nat (Z.pos p)) <= n)%nat)
    by (apply NatLe_drop; exact Hn).
  assert (Hmono : (Z.of_nat (Datatypes.S (4 * Z.to_nat (Z.pos p))) <= Z.of_nat n)%Z)
    by (apply Nat2Z.inj_le; exact Hle).
  assert (HNval : Z.of_nat (Datatypes.S (4 * Z.to_nat (Z.pos p))) = (4 * Z.pos p + 1)%Z).
  { replace (Datatypes.S (4 * Z.to_nat (Z.pos p))) with (4 * Z.to_nat (Z.pos p) + 1)%nat by lia.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, (Z2Nat.id (Z.pos p) Hp1). lia. }
  assert (Hn2 : Z.of_nat (Datatypes.S (2 * n)) = (2 * Z.of_nat n + 1)%Z).
  { replace (Datatypes.S (2 * n)) with (2 * n + 1)%nat by lia.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul. lia. }
  apply (leiblw_QltT_comp_l ((4 # Pos.of_succ_nat (2 * n))%Q) (Qabs (leiblw_t n)) (z # p)%Q).
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    apply Qeq_sym. apply (proj1 (Qeq_bool_iff _ _)).
    assert (Hta := leiblw_t_abs n). leiblw_id_inv_in Hta. exact Hta.
  - apply Qlt_to_QltT.
    unfold Qlt. cbn [Qnum Qden]. apply (proj2 (Z.compare_lt_iff _ _)).
    leiblw_ps (2 * n). rewrite Hn2. nia.
Qed.

(* -- Section 11.3. the cauchy machine instance + the x0 packaging (1): the
   cauchy-real limit of the series itself.
   no claim of pi/4 -- the only payload of x0 is "how slow this family is"
   (|t_n| -> 0 + the envelope width), a value true with no pi premise. -- *)

Lemma leiblw_S_cauchy : cauchy (fun n : nat => leiblw_S n).
Proof.
  intros eps Heps.
  destruct (leiblw_t_vanish eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  apply Qlt_to_QltT. apply (Qle_lt_trans _ (Qabs (leiblw_t N))).
  - apply QleT'_to_Qle. apply leiblw_S_pair_abs_t.
    + exact Hm.
    + exact Hn.
  - apply QltT_to_Qlt. apply HN. apply NatLe_lift. apply Nat.le_refl.
Qed.

Definition leiblw_x0 : Real :=
  existT (fun u : Qseq => cauchy u) (fun n : nat => leiblw_S n) leiblw_S_cauchy.

(* the x0 representing column = the partial-sum column itself (the Id + Qeq_bool
   face, machine-checkable) *)
Lemma leiblw_x0_proj : forall n : nat,
  leiblw_Id (Qeq_bool (projT1 leiblw_x0 n) (leiblw_S n)) true.
Proof.
  intros n. apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)). reflexivity.
Qed.

(* -- Section 11.4. the glue instantiation (3): the glue assumption nonempty and
   the main glue theorem holding for the true x0 -- the boundary-theorem line
   fully through. -- *)

(* the Section 10.4 band membership at x0: j >= 2m+3 eventually enters the inner
   band (supplied directly by the glue_band_S stock -- the conversion of
   projT1 x0 j is leiblw_S j) *)
Lemma leiblw_glue_x0_band : forall m : nat,
  sigT (fun N : nat => forall j : nat, NatLe N j ->
    And (QleT' ((leiblw_env_lo (2 * m) + leiblw_env_g (2 * m))%Q) (projT1 leiblw_x0 j))
        (QleT' (projT1 leiblw_x0 j)
               ((leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1))%Q))).
Proof.
  intros m. exists (2 * m + 3). intros j Hj.
  exact (leiblw_glue_band_S m j Hj).
Qed.

(* the Section 10.3 main glue theorem at the true x0: dist(x0, lo) >= the sibling
   gap and dist(x0, hi) >= the sibling gap, both eps-def sides holding -- "the
   distance from the limit to the partial sums >= gap" fully through *)
Theorem leiblw_glue_x0 : forall m : nat,
  And (forall d : Q, QltT 0 d ->
        real_lt (real_const (((leiblw_env_lo (2 * m) + leiblw_env_g (2 * m)) - d)%Q)) leiblw_x0)
      (forall d : Q, QltT 0 d ->
        real_lt leiblw_x0 (real_const (((leiblw_env_hi (2 * m + 1) - leiblw_env_g (2 * m + 1)) + d)%Q))).
Proof.
  intros m. exact (leiblw_glue_dist m leiblw_x0 (leiblw_glue_x0_band m)).
Qed.

(* the Section 10.0 accessor-endpoint 2m specialization bridge: env_lo(2m) =
   S_{2m}, env_hi(2m) = S_{2m+1}
   (supplied by the env_*_val stock + the div2_even stock) *)
Lemma leiblw_env_lo_2m : forall m : nat,
  leiblw_Id (Qeq_bool (leiblw_env_lo (2 * m)) (leiblw_S (2 * m))) true.
Proof.
  intros m. pose proof (leiblw_env_lo_val (2 * m)) as H.
  leiblw_d2e_in m H. leiblw_id_inv_in H.
  apply leiblw_id_eq. exact H.
Qed.

Lemma leiblw_env_hi_2m : forall m : nat,
  leiblw_Id (Qeq_bool (leiblw_env_hi (2 * m)) (leiblw_S (2 * m + 1))) true.
Proof.
  intros m. pose proof (leiblw_env_hi_val (2 * m)) as H.
  leiblw_d2e_in m H. leiblw_id_inv_in H.
  apply leiblw_id_eq. exact H.
Qed.

(* the envelope premise of the Section 10.2 width witness at x0: j >= 2m
   eventually enters the envelope [env_lo(2m), env_hi(2m)]
   (the win_even stock + the 2m specialization bridge + the QleT' transport
   bridge) *)
Lemma leiblw_glue_env_x0 : forall m : nat,
  sigT (fun N : nat => forall j : nat, NatLe N j ->
    And (QleT' (leiblw_env_lo (2 * m)) (projT1 leiblw_x0 j))
        (QleT' (projT1 leiblw_x0 j) (leiblw_env_hi (2 * m)))).
Proof.
  intros m. exists (2 * m). intros j Hj.
  destruct (leiblw_win_even m j Hj) as [A B].
  apply QleT'_to_Qle in A. apply QleT'_to_Qle in B.
  pose proof (leiblw_env_lo_2m m) as HL. leiblw_id_inv_in HL.
  pose proof (leiblw_env_hi_2m m) as HH. leiblw_id_inv_in HH.
  split.
  - apply (leiblw_QleT'_comp_l (leiblw_S (2 * m))).
    + apply leiblw_id_eq. apply Qeq_bool_sym. exact HL.
    + apply Qle_to_QleT'. exact A.
  - apply (leiblw_QleT'_comp_r (projT1 leiblw_x0 j) (leiblw_S (2 * m + 1))).
    + apply leiblw_id_eq. apply Qeq_bool_sym. exact HH.
    + apply Qle_to_QleT'. exact B.
Qed.

(* the (i) width-witness use face: |x0 column - lo| <= the envelope width (supplied
   directly by the glue_width stock) *)
Lemma leiblw_glue_width_x0 : forall m : nat,
  sigT (fun N0 : nat => forall j : nat, NatLe N0 j ->
    QleT' (Qabs ((projT1 leiblw_x0 j - leiblw_env_lo (2 * m))%Q))
          ((leiblw_env_hi (2 * m) - leiblw_env_lo (2 * m))%Q)).
Proof.
  intros m. exact (leiblw_glue_width m leiblw_x0 (leiblw_glue_env_x0 m)).
Qed.

(* -- Section 11.5. the executable demonstration + extraction + the axiom audit -- *)
(* a two-shot vm_compute record of the x0 representing column (S_6/S_7 = the
   alternating partial-sum convergence record) + three self-check shots at n=20
   of |t_20| x the envelope width x Qeq_bool (the numeric form of core check 1:
   the width = |t_{2*div2 20}|, Qeq_bool should be true; the raw Q operations do
   not reduce, so the width prints with its large denominator, the mathematical
   value = 4/41) *)
Eval vm_compute in (projT1 leiblw_x0 6, projT1 leiblw_x0 7).
Eval vm_compute in (Qabs (leiblw_t 20), (leiblw_env_hi 20 - leiblw_env_lo 20)%Q,
                    Qeq_bool (Qabs (leiblw_t 20)) ((leiblw_env_hi 20 - leiblw_env_lo 20)%Q)).

(* extraction: the true-limit body itself extracts (the Real = (Qseq,cauchy) sigT
   extraction with zero artifacts) *)
Separate Extraction leiblw_x0.

(* the tail Print Assumptions (the Section 11 face; twenty-one Closed) *)
Print Assumptions leiblw_t_vanish.
Print Assumptions leiblw_S_cauchy.
Print Assumptions leiblw_x0.
Print Assumptions leiblw_glue_x0_band.
Print Assumptions leiblw_glue_x0.
Print Assumptions leiblw_glue_env_x0.
Print Assumptions leiblw_glue_width_x0.

(* ============================================================ *)
(* Section 12. the real_lim connection segment (a pure-glue addition): the
   partial-sum column (the Q-layer leiblw_S embedded into Real via real_const)
   converges real_lim to x0. *)
(* ============================================================ *)
(* Reading: the sanctioned statement face = QltT / sigT / And / NatLe / Real /
   real_lim (real_const/real_plus/real_opp are the definitional companions of
   the S02 real_lim face); zero == / zero Qeq atoms / zero lia statement atoms;
   every lra feed is a constant-multiple shape (micromega-Q does not split Qdiv
   division atoms -- the witness is taken as (1#2)*eps, any Q is lawful at the
   real_lt witness site, no division enters the proof).
   The tail-window method: the cauchy((1#2)*eps) witness N + the win stock
   (k >= N gives S_k caught in [min(S_N,S_{N+1}),max(S_N,S_{N+1})]) give the
   two-sided margin > eps - (1#2)*eps = the witness (the strict chain supplied
   directly by the cauchy strict bound; no triangle inequality, no t_vanish). *)

Lemma leiblw_S_tail_two_sided :
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall n k : nat, NatLe N n -> NatLe N k ->
    And (QltT ((1 # 2) * eps)%Q ((leiblw_S k + eps - leiblw_S n)%Q))
        (QltT ((1 # 2) * eps)%Q ((leiblw_S n - (leiblw_S k + (- eps)))%Q))).
Proof.
  intros eps Heps.
  assert (Hw0 : QltT 0 ((1 # 2) * eps)%Q).
  { apply Qlt_to_QltT.
    assert (H0 : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
    lra. }
  destruct (leiblw_S_cauchy ((1 # 2) * eps)%Q Hw0) as [Nc Hc].
  assert (Habs2 : forall x e : Q, QltT (Qabs x) e -> And (QltT (- e) x) (QltT x e)).
  { intros x e H.
    assert (Hl : Qlt (Qabs x) e) by (apply QltT_to_Qlt; exact H).
    destruct (Qlt_le_dec x 0) as [Hx0 | Hx0].
    - assert (Habs : Qabs x == - x) by (apply Qabs_neg; apply Qlt_le_weak; exact Hx0).
      rewrite Habs in Hl. split; apply Qlt_to_QltT; lra.
    - assert (Habs : Qabs x == x) by (apply Qabs_pos; exact Hx0).
      rewrite Habs in Hl. split; apply Qlt_to_QltT; lra. }
  exists Nc. intros n k Hn Hk.
  destruct (leiblw_par_decomp Nc) as [[j Hj]|[j Hj]]; subst Nc.
  - (* Nc = 2j (the even window: S_{2j} <= S_k <= S_{2j+1}) *)
    assert (Hrefl : NatLe (2 * j) (2 * j)) by (apply NatLe_lift; lia).
    assert (Hle1 : NatLe (2 * j) (2 * j + 1)) by (apply NatLe_lift; lia).
    assert (Hcn : QltT (Qabs ((leiblw_S (2 * j) - leiblw_S n)%Q))
                       ((1 # 2) * eps)%Q)
      by exact (Hc (2 * j) n Hrefl Hn).
    assert (Hcn1 : QltT (Qabs ((leiblw_S (2 * j + 1) - leiblw_S n)%Q))
                        ((1 # 2) * eps)%Q)
      by exact (Hc (2 * j + 1) n Hle1 Hn).
    destruct (leiblw_win_even j k Hk) as [A B].
    apply QleT'_to_Qle in A. apply QleT'_to_Qle in B.
    pose proof (Habs2 (leiblw_S (2 * j) - leiblw_S n)%Q ((1 # 2) * eps)%Q Hcn)
      as [Hlo1 Hhi1].
    apply QltT_to_Qlt in Hlo1.
    apply QltT_to_Qlt in Hhi1.
    pose proof (Habs2 (leiblw_S (2 * j + 1) - leiblw_S n)%Q ((1 # 2) * eps)%Q Hcn1)
      as [Hlo2 Hhi2].
    apply QltT_to_Qlt in Hlo2.
    apply QltT_to_Qlt in Hhi2.
    split.
    + apply Qlt_to_QltT. lra.
    + apply Qlt_to_QltT. lra.
  - (* Nc = 2j+1 (the odd window: S_{2j+2} <= S_k <= S_{2j+1}) *)
    assert (Hrefl : NatLe (2 * j + 1) (2 * j + 1)) by (apply NatLe_lift; lia).
    assert (Hle1 : NatLe (2 * j + 1) (2 * j + 2)) by (apply NatLe_lift; lia).
    assert (Hcn : QltT (Qabs ((leiblw_S (2 * j + 1) - leiblw_S n)%Q))
                        ((1 # 2) * eps)%Q)
      by exact (Hc (2 * j + 1) n Hrefl Hn).
    assert (Hcn0 : QltT (Qabs ((leiblw_S (2 * j + 2) - leiblw_S n)%Q))
                        ((1 # 2) * eps)%Q)
      by exact (Hc (2 * j + 2) n Hle1 Hn).
    destruct (leiblw_win_odd j k Hk) as [A B].
    apply QleT'_to_Qle in A. apply QleT'_to_Qle in B.
    pose proof (Habs2 (leiblw_S (2 * j + 1) - leiblw_S n)%Q ((1 # 2) * eps)%Q Hcn)
      as [Hlo1 Hhi1].
    apply QltT_to_Qlt in Hlo1.
    apply QltT_to_Qlt in Hhi1.
    pose proof (Habs2 (leiblw_S (2 * j + 2) - leiblw_S n)%Q ((1 # 2) * eps)%Q Hcn0)
      as [Hlo2 Hhi2].
    apply QltT_to_Qlt in Hlo2.
    apply QltT_to_Qlt in Hhi2.
    split.
    + apply Qlt_to_QltT. lra.
    + apply Qlt_to_QltT. lra.
Qed.

Theorem leiblw_S_real_lim :
  real_lim (fun n : nat => real_const (leiblw_S n)) leiblw_x0.
Proof.
  intros eps Heps.
  destruct (leiblw_S_tail_two_sided eps Heps) as [N HN].
  exists N. intros n Hn.
  assert (Hn' : NatLe N n) by (apply NatLe_lift; exact Hn).
  assert (Hw0 : QltT 0 ((1 # 2) * eps)%Q).
  { apply Qlt_to_QltT.
    assert (H0 : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
    lra. }
  split.
  - (* the upper side: real_lt (u n) (x0 + eps) -- the witness (1#2)*eps; exact
   discharges the projection conversion *)
    exists ((1 # 2) * eps)%Q. split.
    + exact Hw0.
    + exists N. intros k Hk.
      destruct (HN n k Hn' Hk) as [HA HB].
      exact HA.
  - (* the lower side: real_lt (x0 - eps) (u n) -- the second component in its real_lt
   reduction form, discharged by exact *)
    exists ((1 # 2) * eps)%Q. split.
    + exact Hw0.
    + exists N. intros k Hk.
      destruct (HN n k Hn' Hk) as [HA HB].
      exact HB.
Qed.

(* the tail Print Assumptions (the Section 12 face; twenty-eight Closed) *)
Print Assumptions leiblw_S_tail_two_sided.
Print Assumptions leiblw_S_real_lim.
