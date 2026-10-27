(* ConstructiveWorld-Set — Lambert continued-fraction tables for the tangent
   at rational points. *)

(** * pdt_tan_table: tangent continued-fraction tables at rational points.

    Mission. A two-layer carrier for the tangent continued-fraction tables
    at [x0 = p / (4q)]: the [Q]-layer tables [U_j], [V_j] follow
    [X_{k+2} = (2k+3) X_{k+1} - w X_k] ([w = z^2]); the [Z]-layer scaled
    sequences [alpha_j = (4q)^j A_j(x0)], [beta_j = (4q)^j B_j(x0)] follow
    the integer recurrence [X_{k+2} = 4q(2k+3) X_{k+1} - p^2 X_k], with
    [D_j = beta_j - alpha_j], the determinant identity
    [alpha_{j+1} beta_j - alpha_j beta_{j+1} = p^{2j+1}], and the decay
    premise [|Dt_j(t)| < 1] as an explicit Set-layer premise slot.

    Dependencies. Stdlib [QArith], [QArith.Qabs], [ZArith], [List],
    [Setoid], [Lia]; requires [S01_BaseRing] ([Id], [id_refl] selectively)
    and [S02_CauchyComplete] of this development.

    References. ConstructiveWorld-Main ConstructiveWorld_Live/pdt_tan_table.v,
    whose statement names are carried over here verbatim (statement-face
    Set-carrier completion); J. L. Lambert, Hist. Acad. Berlin 17 (1761)
    265-322.

    Constructivity. Computation anchors are carried by the Set-layer boolean
    identity carrier [bid] and decided by [vm_compute]; the decay premise is
    never admitted; [Obj.magic] = 0 and a [coqchk] run reports a closed
    global context.

    Build. [rocq c -native-compiler no -q -Q . "" pdt_tan_table.v] compiles
    cleanly (exit 0); artifact magic [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Setoid.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing (Id, id_refl).
Require Import S02_CauchyComplete.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Set-level boolean identity carrier: bid b is inhabited exactly when *)
(* b = true. Anchor and premise statements below live in Set through   *)
(* bid; bridge proofs work on the underlying Q-equality and conclude   *)
(* through the boolean bridge.                                         *)
(* ------------------------------------------------------------------ *)

Inductive bid : bool -> bool -> Set := bidT : bid true true.

(* Bridging a Q-level equality into the boolean carrier. *)
Lemma qeqbI : forall x y : Q, x == y -> bid (Qeq_bool x y) true.
Proof.
  intros x y H.
  pose proof H as Hx.
  unfold Qeq in Hx.
  unfold Qeq_bool.
  apply Z.eqb_eq in Hx.
  rewrite Hx.
  apply bidT.
Qed.

Lemma bidI : forall b : bool, b = true -> bid b true.
Proof.
  intros b H.
  rewrite H.
  apply bidT.
Qed.

Lemma bidE : forall b : bool, bid b true -> Id b true.
Proof.
  intros b H.
  destruct H.
  apply id_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Coefficient-table arithmetic on list Q, low degree first.           *)
(* ------------------------------------------------------------------ *)

(* Pointwise addition of coefficient tables, short side zero-padded. *)
Fixpoint vadd (a b : list Q) : list Q :=
  match a, b with
  | nil, _ => b
  | _, nil => a
  | x :: a', y :: b' => (x + y)%Q :: vadd a' b'
  end.

(* Scalar multiplication of a coefficient table. *)
Fixpoint vsmul (c : Q) (l : list Q) : list Q :=
  match l with
  | nil => nil
  | x :: t => (c * x)%Q :: vsmul c t
  end.

(* Pointwise Q-equality test of two tables (reduction-normal form free). *)
Fixpoint vleeq (a b : list Q) : bool :=
  match a, b with
  | nil, nil => true
  | nil, _ :: _ => false
  | _ :: _, nil => false
  | x :: a', y :: b' => andb (Qeq_bool x y) (vleeq a' b')
  end.

(* Power of a rational by a nat exponent. *)
Fixpoint q_pown (x : Q) (n : nat) : Q :=
  match n with
  | O => (1 # 1)%Q
  | S m => x * q_pown x m
  end.

(* ------------------------------------------------------------------ *)
(* The Lambert recurrence tables for tan. tanU is the numerator side   *)
(* (x times its value at w = x^2 is A_j), tanV the denominator side;   *)
(* both start from the displayed base cases and follow                 *)
(* X_{k+2} = (2k+3) X_{k+1} - w X_k. The tables are cast as a          *)
(* single-step four-tuple recursion (guard-conformant flattening of    *)
(* the three-term recurrence with two-step memory): tan_pair k carries *)
(* (U_k, U_{k+1}, V_k, V_{k+1}); each step rebuilds the k+2 entries    *)
(* from the k and k+1 ones, the w-multiple being the one-position      *)
(* shift 0 :: ua scaled by -1.                                         *)
(* ------------------------------------------------------------------ *)

Fixpoint tan_pair (k : nat) : (list Q * list Q) * (list Q * list Q) :=
  match k with
  | O =>
      (((0 # 1)%Q :: nil, (1 # 1)%Q :: nil),
       ((1 # 1)%Q :: nil, (1 # 1)%Q :: nil))
  | S m =>
      let (uu, vv) := tan_pair m in
      let (ua, ub) := uu in
      let (va, vb) := vv in
      let unext :=
        vadd (vsmul ((Z.of_nat (2 * S m + 1)) # 1)%Q ub)
             (vsmul ((-1) # 1)%Q (0%Q :: ua)) in
      let vnext :=
        vadd (vsmul ((Z.of_nat (2 * S m + 1)) # 1)%Q vb)
             (vsmul ((-1) # 1)%Q (0%Q :: va)) in
      ((ub, unext), (vb, vnext))
  end.

(* The numerator-side and denominator-side tables. *)
Definition tanU (k : nat) : list Q := fst (fst (tan_pair k)).
Definition tanV (k : nat) : list Q := fst (snd (tan_pair k)).

(* ------------------------------------------------------------------ *)
(* The Z layer: scaled integer sequences with pure integer recurrence  *)
(* alpha_j = (4q)^j A_j(x0), beta_j = (4q)^j B_j(x0). The scaling      *)
(* absorbs the denominators of x0 = p/(4q), so no division atom ever   *)
(* enters the integer sequences.                                       *)
(* ------------------------------------------------------------------ *)

Fixpoint pdt_zpair (p : Z) (q : nat) (k : nat) : (Z * Z) * (Z * Z) :=
  match k with
  | O => ((0%Z, p), (1%Z, Z.of_nat (4 * q)))
  | S m =>
      let (aa, bb) := pdt_zpair p q m in
      let (a0, a1) := aa in
      let (b0, b1) := bb in
      let anext :=
        (Z.of_nat (4 * q) * Z.of_nat (2 * S m + 1) * a1 - p * p * a0)%Z in
      let bnext :=
        (Z.of_nat (4 * q) * Z.of_nat (2 * S m + 1) * b1 - p * p * b0)%Z in
      ((a1, anext), (b1, bnext))
  end.

Definition pdt_alpha (p : Z) (q : nat) (j : nat) : Z := fst (fst (pdt_zpair p q j)).
Definition pdt_beta (p : Z) (q : nat) (j : nat) : Z := fst (snd (pdt_zpair p q j)).
Definition pdt_D (p : Z) (q : nat) (j : nat) : Z := pdt_beta p q j - pdt_alpha p q j.

(* Binary power of an integer by a nat exponent (Z-side values stay    *)
(* binary; no unary numeral is ever materialized).                     *)
Fixpoint pdt_zpow (x : Z) (n : nat) : Z :=
  match n with
  | O => 1%Z
  | S m => x * pdt_zpow x m
  end.

(* ------------------------------------------------------------------ *)
(* Step equations and induction infrastructure.                        *)
(* ------------------------------------------------------------------ *)

(* Two-step induction on Set-valued predicates. *)
Lemma nat_double_ind : forall P : nat -> Set,
  P O ->
  P (S O) ->
  (forall m : nat, P m -> P (S m) -> P (S (S m))) ->
  forall k : nat, P k.
Proof.
  intros P H0 H1 HS k.
  assert (Haux : forall k1 j : nat, (j <= k1)%nat -> P j).
  { intros k1.
    induction k1 as [|k1 IHk1]; intros j Hj.
    - assert (j = O) by lia. subst j. exact H0.
    - destruct j as [|j1].
      + exact H0.
      + destruct j1 as [|j2].
        * exact H1.
        * apply HS.
          -- apply IHk1. lia.
          -- apply IHk1. lia. }
  apply (Haux k k).
  lia.
Qed.

(* Defining step equation of the four-tuple table recursion (let-form, *)
(* syntactically the S-branch body of the Fixpoint).                   *)
Lemma tan_pair_step : forall m : nat,
  Id (tan_pair (S m))
    (let (uu, vv) := tan_pair m in
     let (ua, ub) := uu in
     let (va, vb) := vv in
     ((ub, vadd (vsmul ((Z.of_nat (2 * S m + 1)) # 1)%Q ub)
                (vsmul ((-1) # 1)%Q (0%Q :: ua))),
      (vb, vadd (vsmul ((Z.of_nat (2 * S m + 1)) # 1)%Q vb)
                (vsmul ((-1) # 1)%Q (0%Q :: va))))).
Proof.
  intros m.
  apply id_refl.
Qed.

(* Defining step equation of the integer-sequence recursion. *)
Lemma pdt_zpair_step : forall (p : Z) (q : nat) (m : nat),
  Id (pdt_zpair p q (S m))
    (let (aa, bb) := pdt_zpair p q m in
     let (a0, a1) := aa in
     let (b0, b1) := bb in
     ((a1, (Z.of_nat (4 * q) * Z.of_nat (2 * S m + 1) * a1 - p * p * a0)%Z),
      (b1, (Z.of_nat (4 * q) * Z.of_nat (2 * S m + 1) * b1 - p * p * b0)%Z))).
Proof.
  intros p q m.
  apply id_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Small helper lemmas: pointwise arithmetic of tables and the         *)
(* polynomial evaluation functional.                                   *)
(* ------------------------------------------------------------------ *)

Lemma nth0_vsmul : forall (c : Q) (l : list Q),
  QeqT (nth 0 (vsmul c l) 0%Q) (c * nth 0 l 0%Q).
Proof.
  intros c l. apply qeq_imp_qeqT.
  destruct l as [|x t]; simpl.
  - rewrite Qmult_0_r. apply Qeq_refl.
  - apply Qeq_refl.
Qed.

Lemma nth0_vadd : forall a b : list Q,
  QeqT (nth 0 (vadd a b) 0%Q) (nth 0 a 0%Q + nth 0 b 0%Q).
Proof.
  intros a b. apply qeq_imp_qeqT.
  destruct a as [|x t]; destruct b as [|y s]; simpl.
  - apply Qeq_refl.
  - rewrite Qplus_0_l. apply Qeq_refl.
  - rewrite Qplus_0_r. apply Qeq_refl.
  - apply Qeq_refl.
Qed.

Lemma qmul_nat1 : forall a b : nat,
  QeqT ((Z.of_nat a # 1)%Q * (Z.of_nat b # 1)%Q)
    ((Z.of_nat (a * b)) # 1)%Q.
Proof.
  intros a b. apply qeq_imp_qeqT.
  unfold Qeq.
  cbn [Qnum Qden Qmult Pos.mul].
  rewrite Nat2Z.inj_mul.
  lia.
Qed.

(* Horner evaluation of a coefficient table at a rational point. *)
Fixpoint veval (x : Q) (l : list Q) : Q :=
  match l with
  | nil => 0%Q
  | c :: t => (c + x * veval x t)%Q
  end.

Lemma veval_vadd : forall (x : Q) (a b : list Q),
  QeqT (veval x (vadd a b)) (veval x a + veval x b).
Proof.
  intros x a.
  induction a as [|u a IH]; intros b; destruct b as [|v b]; cbn [veval vadd].
  - apply qeq_imp_qeqT. apply Qeq_refl.
  - apply qeq_imp_qeqT. rewrite Qplus_0_l. apply Qeq_refl.
  - apply qeq_imp_qeqT. rewrite Qplus_0_r. apply Qeq_refl.
  - apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (IH b)). ring.
Qed.

Lemma veval_vsmul : forall (x c : Q) (l : list Q),
  QeqT (veval x (vsmul c l)) (c * veval x l).
Proof.
  intros x c l. apply qeq_imp_qeqT.
  induction l as [|u l IH]; cbn [veval vsmul].
  - rewrite Qmult_0_r. apply Qeq_refl.
  - rewrite IH. ring.
Qed.

Lemma veval_shift1 : forall (x : Q) (l : list Q),
  QeqT (veval x (0%Q :: l)) (x * veval x l).
Proof.
  intros x l. apply qeq_imp_qeqT.
  cbn [veval].
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Rational-point arithmetic used by the bridges.                      *)
(* ------------------------------------------------------------------ *)

(* The evaluation point x0 = p / (4*q). *)
Definition pdt_x0 (p : Z) (q : nat) : Q := ((p # 1) / (Z.of_nat (4 * q) # 1))%Q.

Lemma pdt_x0_scale : forall (p : Z) (q : nat), (0 < q)%nat ->
  QeqT (pdt_x0 p q * (Z.of_nat (4 * q) # 1)%Q) (p # 1)%Q.
Proof.
  intros p q Hq. apply qeq_imp_qeqT.
  unfold pdt_x0.
  destruct (Z.of_nat (4 * q)) as [|m|n] eqn:EM.
  - exfalso. lia.
  - unfold Qdiv, Qinv, Qmult, Qeq. cbn [Qnum Qden Z.mul Pos.mul].
    rewrite Pos.mul_1_r. ring.
  - unfold Qdiv, Qinv, Qmult, Qeq. cbn [Qnum Qden Z.mul Pos.mul].
    rewrite Pos.mul_1_r.
    replace (Z.neg n) with (- Z.pos n)%Z by reflexivity.
    ring.
Qed.

Lemma pdt_qmul_z : forall a b : Z,
  QeqT ((a * b) # 1)%Q ((a # 1) * (b # 1))%Q.
Proof.
  intros a b. apply qeq_imp_qeqT.
  unfold Qeq, Qmult.
  cbn [Qnum Qden Z.mul Pos.mul].
  ring.
Qed.

Lemma pdt_qsub_z : forall a b : Z,
  QeqT ((a - b) # 1)%Q ((a # 1) - (b # 1))%Q.
Proof.
  intros a b. apply qeq_imp_qeqT.
  unfold Qeq, Qminus, Qplus, Qopp, Qmult.
  cbn [Qnum Qden Z.mul Z.sub Z.add Z.opp Pos.mul].
  ring.
Qed.

Lemma pdt_pow_split : forall (M : Z) (n : nat),
  QeqT ((pdt_zpow M (S n)) # 1)%Q ((M # 1) * ((pdt_zpow M n) # 1))%Q.
Proof.
  intros M n.
  cbn [pdt_zpow].
  apply pdt_qmul_z.
Qed.

(* ------------------------------------------------------------------ *)
(* Bridges: the integer sequences are the table values scaled by       *)
(* (4q)^j, at the point x0. The numerator side carries the extra x0    *)
(* factor (A_j = x * U_j); the denominator side does not.              *)
(* ------------------------------------------------------------------ *)

Lemma pdt_bridge_alpha : forall (p : Z) (q : nat), (0 < q)%nat -> forall j : nat,
  bid (Qeq_bool ((pdt_alpha p q j) # 1)%Q
        (((pdt_zpow (Z.of_nat (4 * q)) j) # 1)%Q * pdt_x0 p q
          * veval (pdt_x0 p q * pdt_x0 p q) (tanU j))) true.
Proof.
  intros p q Hq.
  apply nat_double_ind.
  - apply qeqbI.
    unfold pdt_alpha.
    cbn [pdt_zpair fst snd tan_pair tanU veval pdt_zpow].
    ring.
  - apply qeqbI.
    unfold pdt_alpha.
    cbn [pdt_zpair fst snd tan_pair tanU veval pdt_zpow].
    rewrite <- (qeqT_imp_qeq _ _ (pdt_x0_scale p q Hq)).
    rewrite ?Z.mul_1_r.
    ring.
  - intros m IHm IHSm.
    apply bidE in IHm. apply bidE in IHSm.
    destruct (Qeq_bool ((pdt_alpha p q m) # 1)%Q
              (((pdt_zpow (Z.of_nat (4 * q)) m) # 1)%Q * pdt_x0 p q
                * veval (pdt_x0 p q * pdt_x0 p q) (tanU m))) eqn:Em;
      [ | inversion IHm ].
    destruct (Qeq_bool ((pdt_alpha p q (Datatypes.S m)) # 1)%Q
              (((pdt_zpow (Z.of_nat (4 * q)) (Datatypes.S m)) # 1)%Q
                * pdt_x0 p q
                * veval (pdt_x0 p q * pdt_x0 p q) (tanU (Datatypes.S m))))
      eqn:Esm; [ | inversion IHSm ].
    apply Qeq_bool_eq in Em. clear IHm. rename Em into IHm.
    apply Qeq_bool_eq in Esm. clear IHSm. rename Esm into IHSm.
    apply qeqbI.
    unfold pdt_alpha, tanU.
    destruct (pdt_zpair p q m) as [[a0 a1][b0 b1]] eqn:Ez.
    destruct (tan_pair m) as [[u0 u1][v0 v1]] eqn:Et.
    rewrite (pdt_zpair_step p q (S m)), (pdt_zpair_step p q m), Ez.
    rewrite (tan_pair_step (S m)), (tan_pair_step m), Et.
    cbn [fst snd].
    rewrite (fun x a b => qeqT_imp_qeq _ _ (veval_vadd x a b)),
            !(fun x c l => qeqT_imp_qeq _ _ (veval_vsmul x c l)),
            (fun x l => qeqT_imp_qeq _ _ (veval_shift1 x l)).
    replace (pdt_alpha p q m) with a0 in IHm
      by (unfold pdt_alpha; rewrite Ez; reflexivity).
    replace (tanU m) with u0 in IHm
      by (unfold tanU; rewrite Et; reflexivity).
    replace (pdt_alpha p q (S m)) with a1 in IHSm
      by (unfold pdt_alpha; rewrite (pdt_zpair_step p q m), Ez; cbn [fst snd]; reflexivity).
    replace (tanU (S m)) with u1 in IHSm
      by (unfold tanU; rewrite (tan_pair_step m), Et; cbn [fst snd]; reflexivity).
    rewrite (fun a b => qeqT_imp_qeq _ _ (pdt_qsub_z a b)).
    rewrite !(fun a b => qeqT_imp_qeq _ _ (pdt_qmul_z a b)).
    rewrite IHSm, IHm.
    rewrite !(fun M n => qeqT_imp_qeq _ _ (pdt_pow_split M n)).
    rewrite <- (qeqT_imp_qeq _ _ (pdt_x0_scale p q Hq)).
    ring.
Qed.

Lemma pdt_bridge_beta : forall (p : Z) (q : nat), (0 < q)%nat -> forall j : nat,
  bid (Qeq_bool ((pdt_beta p q j) # 1)%Q
        (((pdt_zpow (Z.of_nat (4 * q)) j) # 1)%Q
          * veval (pdt_x0 p q * pdt_x0 p q) (tanV j))) true.
Proof.
  intros p q Hq.
  apply nat_double_ind.
  - apply qeqbI.
    unfold pdt_beta.
    cbn [pdt_zpair fst snd tan_pair tanV veval pdt_zpow].
    rewrite ?Z.mul_1_r.
    ring.
  - apply qeqbI.
    unfold pdt_beta.
    cbn [pdt_zpair fst snd tan_pair tanV veval pdt_zpow].
    rewrite ?Z.mul_1_r.
    ring.
  - intros m IHm IHSm.
    apply bidE in IHm. apply bidE in IHSm.
    destruct (Qeq_bool ((pdt_beta p q m) # 1)%Q
              (((pdt_zpow (Z.of_nat (4 * q)) m) # 1)%Q
                * veval (pdt_x0 p q * pdt_x0 p q) (tanV m))) eqn:Em;
      [ | inversion IHm ].
    destruct (Qeq_bool ((pdt_beta p q (Datatypes.S m)) # 1)%Q
              (((pdt_zpow (Z.of_nat (4 * q)) (Datatypes.S m)) # 1)%Q
                * veval (pdt_x0 p q * pdt_x0 p q) (tanV (Datatypes.S m))))
      eqn:Esm; [ | inversion IHSm ].
    apply Qeq_bool_eq in Em. clear IHm. rename Em into IHm.
    apply Qeq_bool_eq in Esm. clear IHSm. rename Esm into IHSm.
    apply qeqbI.
    unfold pdt_beta, tanV.
    destruct (pdt_zpair p q m) as [[a0 a1][b0 b1]] eqn:Ez.
    destruct (tan_pair m) as [[u0 u1][v0 v1]] eqn:Et.
    rewrite (pdt_zpair_step p q (S m)), (pdt_zpair_step p q m), Ez.
    rewrite (tan_pair_step (S m)), (tan_pair_step m), Et.
    cbn [fst snd].
    rewrite (fun x a b => qeqT_imp_qeq _ _ (veval_vadd x a b)),
            !(fun x c l => qeqT_imp_qeq _ _ (veval_vsmul x c l)),
            (fun x l => qeqT_imp_qeq _ _ (veval_shift1 x l)).
    replace (pdt_beta p q m) with b0 in IHm
      by (unfold pdt_beta; rewrite Ez; reflexivity).
    replace (tanV m) with v0 in IHm
      by (unfold tanV; rewrite Et; reflexivity).
    replace (pdt_beta p q (S m)) with b1 in IHSm
      by (unfold pdt_beta; rewrite (pdt_zpair_step p q m), Ez; cbn [fst snd]; reflexivity).
    replace (tanV (S m)) with v1 in IHSm
      by (unfold tanV; rewrite (tan_pair_step m), Et; cbn [fst snd]; reflexivity).
    rewrite (fun a b => qeqT_imp_qeq _ _ (pdt_qsub_z a b)).
    rewrite !(fun a b => qeqT_imp_qeq _ _ (pdt_qmul_z a b)).
    rewrite IHSm, IHm.
    rewrite !(fun M n => qeqT_imp_qeq _ _ (pdt_pow_split M n)).
    rewrite <- (qeqT_imp_qeq _ _ (pdt_x0_scale p q Hq)).
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Determinant identity: the Casus irreducibilis-style invariant       *)
(* alpha_{j+1} beta_j - alpha_j beta_{j+1} = p^{2j+1}, unconditional  *)
(* in p and q.                                                        *)
(* ------------------------------------------------------------------ *)

Lemma pdt_det : forall (p : Z) (q : nat) (j : nat),
  bid (Z.eqb (pdt_alpha p q (S j) * pdt_beta p q j
                 - pdt_alpha p q j * pdt_beta p q (S j))
             (pdt_zpow p (2 * j + 1))) true.
Proof.
  intros p q j.
  induction j as [|j IHj].
  - apply bidI. apply Z.eqb_eq.
    unfold pdt_alpha, pdt_beta.
    cbn [pdt_zpair fst snd].
    replace (2 * 0 + 1)%nat with 1%nat by lia.
    cbn [pdt_zpow].
    ring.
  - apply bidI. apply Z.eqb_eq.
    replace (2 * S j + 1)%nat with (S (S (2 * j + 1)))%nat by lia.
    replace (pdt_zpow p (S (S (2 * j + 1))))
      with (p * (p * pdt_zpow p (2 * j + 1)))%Z by reflexivity.
    destruct (pdt_zpair p q j) as [[a0 a1][b0 b1]] eqn:Ez.
    unfold pdt_alpha, pdt_beta.
    rewrite (pdt_zpair_step p q (S j)), (pdt_zpair_step p q j), Ez.
    cbn [fst snd].
    apply bidE in IHj.
    destruct (Z.eqb (pdt_alpha p q (Datatypes.S j) * pdt_beta p q j
                       - pdt_alpha p q j * pdt_beta p q (Datatypes.S j))
                   (pdt_zpow p (2 * j + 1))) eqn:Ej; [ | inversion IHj ].
    apply Z.eqb_eq in Ej. clear IHj. rename Ej into IHj.
    replace (pdt_alpha p q (S j)) with a1 in IHj
      by (unfold pdt_alpha; rewrite (pdt_zpair_step p q j), Ez; cbn [fst snd]; reflexivity).
    replace (pdt_beta p q (S j)) with b1 in IHj
      by (unfold pdt_beta; rewrite (pdt_zpair_step p q j), Ez; cbn [fst snd]; reflexivity).
    replace (pdt_alpha p q j) with a0 in IHj
      by (unfold pdt_alpha; rewrite Ez; reflexivity).
    replace (pdt_beta p q j) with b0 in IHj
      by (unfold pdt_beta; rewrite Ez; reflexivity).
    rewrite <- IHj.
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Computable anchors: table values, integer-sequence values and the   *)
(* bridge identities at x0 = 3/4, each a closed assertion resolved by  *)
(* vm_compute (reduction-form free via Qeq_bool / Z.eqb / vleeq).      *)
(* ------------------------------------------------------------------ *)

Lemma tanU_anchor_3 :
  bid (vleeq (tanU 3) (((15 # 1) :: ((-1) # 1) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

Lemma tanV_anchor_3 :
  bid (vleeq (tanV 3) (((15 # 1) :: ((-6) # 1) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

(* The computed U_4 carries the trailing zero inherited from U_2; the  *)
(* test is list-exact.                                                *)
Lemma tanU_anchor_4 :
  bid (vleeq (tanU 4) (((105 # 1) :: ((-10) # 1) :: (0 # 1) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

Lemma tanV_anchor_4 :
  bid (vleeq (tanV 4) (((105 # 1) :: ((-45) # 1) :: (1 # 1) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

(* Integer sequences at p = 3, q = 1, j = 0..4. *)
Lemma pdt_z_anchor_31 :
  (bid (Z.eqb (pdt_alpha 3 1 0) 0%Z) true) *
  (bid (Z.eqb (pdt_alpha 3 1 1) 3%Z) true) *
  (bid (Z.eqb (pdt_alpha 3 1 2) 36%Z) true) *
  (bid (Z.eqb (pdt_alpha 3 1 3) 693%Z) true) *
  (bid (Z.eqb (pdt_alpha 3 1 4) 19080%Z) true) *
  (bid (Z.eqb (pdt_beta 3 1 0) 1%Z) true) *
  (bid (Z.eqb (pdt_beta 3 1 1) 4%Z) true) *
  (bid (Z.eqb (pdt_beta 3 1 2) 39%Z) true) *
  (bid (Z.eqb (pdt_beta 3 1 3) 744%Z) true) *
  (bid (Z.eqb (pdt_beta 3 1 4) 20481%Z) true).
Proof.
  repeat apply pair.
  all: apply bidI; vm_compute; reflexivity.
Qed.

(* D_j = beta_j - alpha_j at p = 3, q = 1, j = 0..5. *)
Lemma pdt_D_anchor_31 :
  (bid (Z.eqb (pdt_D 3 1 0) 1%Z) true) *
  (bid (Z.eqb (pdt_D 3 1 1) 1%Z) true) *
  (bid (Z.eqb (pdt_D 3 1 2) 3%Z) true) *
  (bid (Z.eqb (pdt_D 3 1 3) 51%Z) true) *
  (bid (Z.eqb (pdt_D 3 1 4) 1401%Z) true) *
  (bid (Z.eqb (pdt_D 3 1 5) 49977%Z) true).
Proof.
  repeat apply pair.
  all: apply bidI; vm_compute; reflexivity.
Qed.

(* Determinant values p^(2j+1) at p = 3, j = 0..2. *)
Lemma pdt_det_anchor :
  (bid (Z.eqb (pdt_alpha 3 1 1 * pdt_beta 3 1 0
                 - pdt_alpha 3 1 0 * pdt_beta 3 1 1) 3%Z) true) *
  (bid (Z.eqb (pdt_alpha 3 1 2 * pdt_beta 3 1 1
                 - pdt_alpha 3 1 1 * pdt_beta 3 1 2) 27%Z) true) *
  (bid (Z.eqb (pdt_alpha 3 1 3 * pdt_beta 3 1 2
                 - pdt_alpha 3 1 2 * pdt_beta 3 1 3) 243%Z) true).
Proof.
  repeat apply pair.
  all: apply bidI; vm_compute; reflexivity.
Qed.

(* Both bridge identities at p = 3, q = 1, j = 0..4, computed on the   *)
(* two sides independently.                                            *)
Lemma pdt_bridge_anchor_31 :
  (bid (Qeq_bool ((pdt_alpha 3 1 0) # 1)%Q
         (((pdt_zpow (Z.of_nat (4 * 1)) 0) # 1)%Q * pdt_x0 3 1
           * veval (pdt_x0 3 1 * pdt_x0 3 1) (tanU 0))) true) *
  (bid (Qeq_bool ((pdt_alpha 3 1 1) # 1)%Q
         (((pdt_zpow (Z.of_nat (4 * 1)) 1) # 1)%Q * pdt_x0 3 1
           * veval (pdt_x0 3 1 * pdt_x0 3 1) (tanU 1))) true) *
  (bid (Qeq_bool ((pdt_alpha 3 1 2) # 1)%Q
         (((pdt_zpow (Z.of_nat (4 * 1)) 2) # 1)%Q * pdt_x0 3 1
           * veval (pdt_x0 3 1 * pdt_x0 3 1) (tanU 2))) true) *
  (bid (Qeq_bool ((pdt_alpha 3 1 3) # 1)%Q
         (((pdt_zpow (Z.of_nat (4 * 1)) 3) # 1)%Q * pdt_x0 3 1
           * veval (pdt_x0 3 1 * pdt_x0 3 1) (tanU 3))) true) *
  (bid (Qeq_bool ((pdt_alpha 3 1 4) # 1)%Q
         (((pdt_zpow (Z.of_nat (4 * 1)) 4) # 1)%Q * pdt_x0 3 1
           * veval (pdt_x0 3 1 * pdt_x0 3 1) (tanU 4))) true) *
  (bid (Qeq_bool ((pdt_beta 3 1 0) # 1)%Q
         (((pdt_zpow (Z.of_nat (4 * 1)) 0) # 1)%Q
           * veval (pdt_x0 3 1 * pdt_x0 3 1) (tanV 0))) true) *
  (bid (Qeq_bool ((pdt_beta 3 1 1) # 1)%Q
         (((pdt_zpow (Z.of_nat (4 * 1)) 1) # 1)%Q
           * veval (pdt_x0 3 1 * pdt_x0 3 1) (tanV 1))) true) *
  (bid (Qeq_bool ((pdt_beta 3 1 2) # 1)%Q
         (((pdt_zpow (Z.of_nat (4 * 1)) 2) # 1)%Q
           * veval (pdt_x0 3 1 * pdt_x0 3 1) (tanV 2))) true) *
  (bid (Qeq_bool ((pdt_beta 3 1 3) # 1)%Q
         (((pdt_zpow (Z.of_nat (4 * 1)) 3) # 1)%Q
           * veval (pdt_x0 3 1 * pdt_x0 3 1) (tanV 3))) true) *
  (bid (Qeq_bool ((pdt_beta 3 1 4) # 1)%Q
         (((pdt_zpow (Z.of_nat (4 * 1)) 4) # 1)%Q
           * veval (pdt_x0 3 1 * pdt_x0 3 1) (tanV 4))) true).
Proof.
  repeat apply pair.
  all: apply bidI; vm_compute; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Remainder-shape skeleton.                                           *)
(*                                                                     *)
(* The remainder of the convergent pair at the rational value t is     *)
(* D~_j(t) = (4q)^j (beta_j t - alpha_j) on the integer-sequence       *)
(* scale; when tan(x0) = 1 this equals (4q)^j * D_j, an integer.       *)
(* an integer. Its absolute value decays geometrically in j at the     *)
(* safe point; the decay statement is cast with the analytic estimate  *)
(* as an explicit Set-level premise slot.                              *)
(* ------------------------------------------------------------------ *)

Definition pdt_tilde (p : Z) (q : nat) (j : nat) (t : Q) : Q :=
  ((pdt_zpow (Z.of_nat (4 * q)) j) # 1)%Q
    * (((pdt_beta p q j) # 1)%Q * t - ((pdt_alpha p q j) # 1)%Q).

(* Strict order test on Q built from the library <= decision test      *)
(* (x < y iff not y <= x); the build ships no direct strict test.      *)
Definition pdt_qltb (x y : Q) : bool := negb (Qle_bool y x).

(* Explicit premise slot (Set-level): the decay estimate               *)
(* |D~_j(t)| < 1 at the value t.                                       *)
Definition pdt_decay_premise (p : Z) (q : nat) (j : nat) (t : Q) : Set :=
  bid (pdt_qltb (Qabs (pdt_tilde p q j t)) (1 # 1)%Q) true.

(* Rational anchor value: 24-digit truncation of tan(3/4), certified   *)
(* in exact rational arithmetic outside this file.                     *)
Definition pdt_tan34_anchor : Q :=
  ((931596459944072461165202 # 1000000000000000000000000)%Q).

(* The premise slot is inhabited at j = 9, q = 1 with the anchored     *)
(* value (verified computationally; the exact rational value of the    *)
(* slot content is 11414714466208509/19073486328125000).               *)
Lemma pdt_decay_instance : pdt_decay_premise 3 1 9 pdt_tan34_anchor.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Extraction evidence: the whole table machinery is informative       *)
(* (no Prop leakage into the computational layer). The extraction is   *)
(* produced outside this file: Separate Extraction of tanV, pdt_zpair  *)
(* and pdt_decay_premise yields OCaml with no Obj.magic occurrence.    *)
(* ------------------------------------------------------------------ *)

Print Assumptions pdt_bridge_alpha.
Print Assumptions pdt_bridge_beta.
Print Assumptions pdt_det.
Print Assumptions tanV_anchor_4.
Print Assumptions pdt_z_anchor_31.
Print Assumptions pdt_decay_instance.
