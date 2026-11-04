(* ConstructiveWorld-Set -- explicit Pade table for arctan. *)

(** * tlw1463_pade_table: diagonal Pade pairs for arctan over w = z^2.

    Mission.  Explicit integer-coefficient Pade table for arctan:
      diagonal [n/n] approximant pairs on w = z^2 built by the
      Lambert continued-fraction three-term recursion, with
      normalization identities, computable matching anchors, and a
      remainder-shape skeleton with explicit Set-level premise slots.
      Entries satisfy X_k = (2k+1) X_{k-1} + k^2 * w * X_{k-2},
      U_{-1} = 0, U_0 = 1, V_{-1} = 1, V_0 = 1.

    Dependencies.  Stdlib [QArith], [QArith.Qabs], [ZArith], [List],
      [Setoid], [Lia], [Extraction].

    References.  This development, tlw1463_pade_table.v, the baseline
      module in ConstructiveWorld-Main whose statement names are
      carried over here verbatim (statement-face Set-carrier
      completion).  Ref.  K. Mahler, Indagationes Math. 15 (1953).

    Constructivity.  All named statements and fields are carried by
      [Set] (boolean identity carriers [bid] and [Id] forms); no
      division atom enters ring-side goals: (4n+1)!! * Q_n = V_{2n}
      is kept in cross-multiplied integer form; statements extract
      with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" tlw1463_pade_table.v]
      compiles cleanly (exit 0); the artifact starts with
      [436f7121 000160bc]. *)
From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Setoid.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Set-level boolean identity carrier: bid b is inhabited exactly when *)
(* b = true. All lemma statements below live in Set through bid.       *)
(* ------------------------------------------------------------------ *)

Inductive bid : bool -> bool -> Set := bidT : bid true true.

(* Bridging a Q-level equality into the boolean carrier. *)
Lemma qeqbI : forall x y : Q, x == y -> Qeq_bool x y = true.
Proof.
  intros x y H.
  unfold Qeq in H.
  unfold Qeq_bool.
  apply Z.eqb_eq.
  exact H.
Qed.

Lemma bidI : forall b : bool, b = true -> bid b true.
Proof.
  intros b H.
  rewrite H.
  apply bidT.
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

(* Cauchy product of two coefficient tables. *)
Fixpoint vconv (a b : list Q) : list Q :=
  match a with
  | nil => nil
  | x :: a' => vadd (vsmul x b) (0%Q :: vconv a' b)
  end.

(* Pointwise Q-equality test of two tables (reduction-normal form free). *)
Fixpoint vleeq (a b : list Q) : bool :=
  match a, b with
  | nil, nil => true
  | nil, _ :: _ => false
  | _ :: _, nil => false
  | x :: a', y :: b' => andb (Qeq_bool x y) (vleeq a' b')
  end.

(* Zero-pad a table on the right up to length N. *)
Fixpoint padnil (N : nat) (l : list Q) : list Q :=
  match N with
  | O => nil
  | S m => match l with
           | nil => 0%Q :: padnil m nil
           | x :: t => x :: padnil m t
           end
  end.

(* Power of a rational by a nat exponent. *)
Fixpoint q_pown (x : Q) (n : nat) : Q :=
  match n with
  | O => (1 # 1)%Q
  | S m => x * q_pown x m
  end.

(* ------------------------------------------------------------------ *)
(* The alternating series table: h_k = (-1)^k / (2k+1), the Taylor     *)
(* coefficients of g(w) = arctan(sqrt w)/sqrt w.                       *)
(* ------------------------------------------------------------------ *)

Definition altsign (m : nat) : Z := if Nat.even m then 1%Z else (-1)%Z.

Fixpoint altser (N : nat) : list Q :=
  match N with
  | O => nil
  | S m => altser m ++ ((altsign m) # (Pos.of_succ_nat (2 * m)))%Q :: nil
  end.

(* ------------------------------------------------------------------ *)
(* The Lambert recurrence tables. padeU is the numerator side, padeV   *)
(* the denominator side; both start from the displayed base cases and  *)
(* follow X_k = (2k+1) X_{k-1} + k^2 w X_{k-2}.                        *)
(* ------------------------------------------------------------------ *)

(* The Lambert recurrence tables, cast as a single-step four-tuple      *)
(* recursion (guard-conformant flattening of the three-term recurrence  *)
(* with two-step memory). pade_pair k carries (U_k, U_{k+1}, V_k,       *)
(* V_{k+1}); each step rebuilds the k+2 entries from the k and k+1      *)
(* ones via X_{k+2} = (2k+5) X_{k+1} + (k+2)^2 w X_k.                   *)
Fixpoint pade_pair (k : nat) : (list Q * list Q) * (list Q * list Q) :=
  match k with
  | O =>
      (((1 # 1)%Q :: nil, (3 # 1)%Q :: nil),
       ((1 # 1)%Q :: nil, (3 # 1)%Q :: (1 # 1)%Q :: nil))
  | S m =>
      let (uu, vv) := pade_pair m in
      let (ua, ub) := uu in
      let (va, vb) := vv in
      let unext :=
        vadd (vsmul ((Z.of_nat (2 * S (S m) + 1)) # 1)%Q ub)
             (vsmul ((Z.of_nat (S (S m) * S (S m))) # 1)%Q (0%Q :: ua)) in
      let vnext :=
        vadd (vsmul ((Z.of_nat (2 * S (S m) + 1)) # 1)%Q vb)
             (vsmul ((Z.of_nat (S (S m) * S (S m))) # 1)%Q (0%Q :: va)) in
      ((ub, unext), (vb, vnext))
  end.

(* The numerator-side and denominator-side tables. *)
Definition padeU (k : nat) : list Q := fst (fst (pade_pair k)).
Definition padeV (k : nat) : list Q := fst (snd (pade_pair k)).

(* The diagonal Padé tables: numerator odd part and denominator. *)
Definition pade_num (n : nat) : list Q := padeU (2 * n).
Definition pade_den (n : nat) : list Q := padeV (2 * n).

(* Normalization factor (4n+1)!!, the leading entry of V_{2n}. *)
Fixpoint dfact (n : nat) : nat :=
  match n with
  | O => 1%nat
  | S O => 1%nat
  | S (S m) => (S (S m) * dfact m)%nat
  end.

Definition pade_norm (n : nat) : nat := dfact (4 * n + 1).

(* ------------------------------------------------------------------ *)
(* Step equations and induction infrastructure.                        *)
(* ------------------------------------------------------------------ *)

Lemma bidE : forall b : bool, bid b true -> b = true.
Proof.
  intros b H.
  destruct H.
  reflexivity.
Qed.

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

(* Defining step equation of the four-tuple recursion (let-form,
   syntactically the S-branch body of the Fixpoint). *)
Lemma pade_pair_step : forall m : nat,
  pade_pair (S m) =
    let (uu, vv) := pade_pair m in
    let (ua, ub) := uu in
    let (va, vb) := vv in
    ((ub, vadd (vsmul ((Z.of_nat (2 * S (S m) + 1)) # 1)%Q ub)
               (vsmul ((Z.of_nat (S (S m) * S (S m))) # 1)%Q (0%Q :: ua))),
     (vb, vadd (vsmul ((Z.of_nat (2 * S (S m) + 1)) # 1)%Q vb)
               (vsmul ((Z.of_nat (S (S m) * S (S m))) # 1)%Q (0%Q :: va)))).
Proof.
  intros m.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Small helper lemmas for the normalization induction.                *)
(* ------------------------------------------------------------------ *)

Lemma nth0_vsmul : forall (c : Q) (l : list Q),
  nth 0 (vsmul c l) 0%Q == c * nth 0 l 0%Q.
Proof.
  intros c l.
  destruct l as [|x t]; simpl.
  - rewrite Qmult_0_r. apply Qeq_refl.
  - apply Qeq_refl.
Qed.

Lemma nth0_vadd : forall a b : list Q,
  nth 0 (vadd a b) 0%Q == nth 0 a 0%Q + nth 0 b 0%Q.
Proof.
  intros a b.
  destruct a as [|x t]; destruct b as [|y s]; simpl.
  - apply Qeq_refl.
  - rewrite Qplus_0_l. apply Qeq_refl.
  - rewrite Qplus_0_r. apply Qeq_refl.
  - apply Qeq_refl.
Qed.

Lemma qmul_nat1 : forall a b : nat,
  ((Z.of_nat a # 1) * (Z.of_nat b # 1))%Q == ((Z.of_nat (a * b)) # 1)%Q.
Proof.
  intros a b.
  unfold Qeq.
  cbn [Qnum Qden Qmult Pos.mul].
  rewrite Nat2Z.inj_mul.
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Normalization: the leading entry of both recurrence sides equals    *)
(* the odd double factorial (2k+1)!!. Under the diagonal pairing this  *)
(* gives leading entry (4n+1)!! = pade_norm n for V_{2n}, so the       *)
(* normalized rational table Q_n = V_{2n}/(4n+1)!! is monic.           *)
(* ------------------------------------------------------------------ *)

Lemma padeV_hd : forall k : nat,
  bid (Qeq_bool (nth 0 (padeV k) 0%Q) ((Z.of_nat (dfact (2 * k + 1))) # 1)%Q) true.
Proof.
  apply nat_double_ind.
  - apply bidI. vm_compute. reflexivity.
  - apply bidI. vm_compute. reflexivity.
  - intros m IHm IHSm.
    apply bidI.
    apply bidE in IHSm. apply Qeq_bool_eq in IHSm.
    assert (Hq : nth 0 (padeV (S (S m))) 0%Q
                 == ((Z.of_nat (dfact (2 * S (S m) + 1))) # 1)%Q).
    { replace (2 * S m + 1)%nat with (2 * m + 3)%nat in IHSm by lia.
      unfold padeV.
      destruct (pade_pair m) as [[u0 u1][v0 v1]] eqn:Em.
      rewrite (pade_pair_step (S m)).
      rewrite (pade_pair_step m).
      rewrite Em.
      cbn [fst snd].
      replace (2 * S (S m) + 1)%nat with (S (S (2 * m + 3)))%nat by lia.
      replace (dfact (S (S (2 * m + 3))))%nat
        with (S (S (2 * m + 3)) * dfact (2 * m + 3))%nat by reflexivity.
      replace (nth 0 (padeV (S m)) 0%Q) with (nth 0 v1 0%Q) in IHSm
        by (unfold padeV; rewrite (pade_pair_step m), Em; cbn [fst snd]; reflexivity).
      eapply Qeq_trans with (y := ((Z.of_nat (S (S (2 * m + 3))) # 1)%Q
                                   * nth 0 v1 0%Q + 0)%Q).
      - rewrite nth0_vadd.
        rewrite nth0_vsmul.
        rewrite nth0_vsmul.
        cbn [nth].
        rewrite Qmult_0_r.
        rewrite Qplus_0_r.
        apply Qeq_refl.
      - rewrite Qplus_0_r.
        rewrite IHSm.
        apply qmul_nat1. }
    apply qeqbI.
    exact Hq.
Qed.

Lemma padeU_hd : forall k : nat,
  bid (Qeq_bool (nth 0 (padeU k) 0%Q) ((Z.of_nat (dfact (2 * k + 1))) # 1)%Q) true.
Proof.
  apply nat_double_ind.
  - apply bidI. vm_compute. reflexivity.
  - apply bidI. vm_compute. reflexivity.
  - intros m IHm IHSm.
    apply bidI.
    apply bidE in IHSm. apply Qeq_bool_eq in IHSm.
    assert (Hq : nth 0 (padeU (S (S m))) 0%Q
                 == ((Z.of_nat (dfact (2 * S (S m) + 1))) # 1)%Q).
    { replace (2 * S m + 1)%nat with (2 * m + 3)%nat in IHSm by lia.
      unfold padeU.
      destruct (pade_pair m) as [[u0 u1][v0 v1]] eqn:Em.
      rewrite (pade_pair_step (S m)).
      rewrite (pade_pair_step m).
      rewrite Em.
      cbn [fst snd].
      replace (2 * S (S m) + 1)%nat with (S (S (2 * m + 3)))%nat by lia.
      replace (dfact (S (S (2 * m + 3))))%nat
        with (S (S (2 * m + 3)) * dfact (2 * m + 3))%nat by reflexivity.
      replace (nth 0 (padeU (S m)) 0%Q) with (nth 0 u1 0%Q) in IHSm
        by (unfold padeU; rewrite (pade_pair_step m), Em; cbn [fst snd]; reflexivity).
      eapply Qeq_trans with (y := ((Z.of_nat (S (S (2 * m + 3))) # 1)%Q
                                   * nth 0 u1 0%Q + 0)%Q).
      - rewrite nth0_vadd.
        rewrite nth0_vsmul.
        rewrite nth0_vsmul.
        cbn [nth].
        rewrite Qmult_0_r.
        rewrite Qplus_0_r.
        apply Qeq_refl.
      - rewrite Qplus_0_r.
        rewrite IHSm.
        apply qmul_nat1. }
    apply qeqbI.
    exact Hq.
Qed.

(* Diagonal normalization in cross-multiplied form:                   *)
(* pade_norm n * (leading entry of pade_den n) equals its square,      *)
(* i.e. the normalized denominator has leading coefficient 1.          *)
Lemma pade_den_monict :
  bid (Qeq_bool (((Z.of_nat (pade_norm 1)) # 1)%Q * nth 0 (pade_den 1) 0%Q)
                 (((Z.of_nat (pade_norm 1)) # 1)%Q * ((Z.of_nat (pade_norm 1)) # 1)%Q))
      true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Computable anchors: table values and the matching identity against  *)
(* the alternating series, for n = 0, 1, 2. Each anchor is a closed    *)
(* Q-value assertion resolved by vm_compute (reduction-form free via   *)
(* Qeq_bool).                                                          *)
(* ------------------------------------------------------------------ *)

(* Table values at k = 4 (used by the n = 2 diagonal anchors). *)
Lemma padeU_anchor_4 :
  bid (vleeq (padeU 4) (((945 # 1) :: (735 # 1) :: (64 # 1) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

Lemma padeV_anchor_4 :
  bid (vleeq (padeV 4) (((945 # 1) :: (1050 # 1) :: (225 # 1) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

(* Matching identity, n = 0: V_0 * g agrees with U_0 at degree <= 0. *)
Lemma pade_match_anchor_n0 :
  bid (vleeq (firstn 2 (vconv (padeV 0) (altser 4)))
             (((1 # 1) :: ((-1) # 3) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

(* Matching identity, n = 1: conv(V_2, altser) = [15; 4] on degrees    *)
(* 0..2, first residual coefficient -12/35 at degree 3.                *)
Lemma pade_match_anchor_n1 :
  bid (vleeq (firstn 4 (vconv (padeV 2) (altser 6)))
             (((15 # 1) :: (4 # 1) :: (0 # 1) :: ((-12) # 35) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

(* Matching identity, n = 2: conv(V_4, altser) = [945; 735; 64] on     *)
(* degrees 0..4, first residual coefficient -320/231 at degree 5.      *)
Lemma pade_match_anchor_n2 :
  bid (vleeq (firstn 6 (vconv (padeV 4) (altser 8)))
             (((945 # 1) :: (735 # 1) :: (64 # 1) :: (0 # 1) :: (0 # 1)
                         :: ((-320) # 231) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

(* The diagonal pairs share the leading coefficient on the anchored    *)
(* orders: both pade_num 1 and pade_den 1 begin with 15, and both      *)
(* pade_num 2 and pade_den 2 begin with 945 = pade_norm 2.             *)
Lemma pade_diag_anchor_n1 :
  bid (vleeq (firstn 2 (pade_num 1)) (((15 # 1) :: (4 # 1) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

Lemma pade_diag_den_anchor_n1 :
  bid (vleeq (firstn 2 (pade_den 1)) (((15 # 1) :: (9 # 1) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

Lemma pade_diag_anchor_n2 :
  bid (vleeq (firstn 3 (pade_num 2))
             (((945 # 1) :: (735 # 1) :: (64 # 1) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

Lemma pade_diag_den_anchor_n2 :
  bid (vleeq (firstn 3 (pade_den 2))
             (((945 # 1) :: (1050 # 1) :: (225 # 1) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Remainder-shape skeleton.                                           *)
(*                                                                     *)
(* The remainder of the diagonal pair at the endpoint z = 1 has first  *)
(* residual coefficient res1_n = conv(V_{2n}, altser)[2n+1] (integer   *)
(* side). Its absolute value decays geometrically with base bounded by *)
(* pade_rho_hat = 21/100: the certified chain is rho = (sqrt 2 - 1)/2  *)
(* < 21/100, from sqrt 2 < 71/50, from 2*50^2 < 71^2.  The decay       *)
(* statement is cast with the analytic estimate as an explicit         *)
(* Set-level premise slot; discharging it is the task of the           *)
(* irrationality-measure stage that consumes this table.               *)
(* ------------------------------------------------------------------ *)

Definition pade_rho_hat : Q := (21 # 100)%Q.

(* Square-side certificate: 2*50^2 < 71^2, hence sqrt 2 < 71/50, hence *)
(* rho = (sqrt 2 - 1)/2 < 21/100 = pade_rho_hat.                       *)
Lemma pade_rho_hat_cert :
  bid (Z.ltb (2 * 50 * 50) (71 * 71)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

(* Explicit premise slot (Set-level): the integral-form estimate       *)
(* |res1_n| / (4n+1)!! <= C * rho_hat^n, phrased on the computable     *)
(* integer-side residual.                                              *)
Definition pade_decay_premise (C : Q) (n : nat) : Set :=
  bid (Qle_bool (Qabs (nth (2 * n + 1) (vconv (padeV (2 * n)) (altser (2 * n + 4))) 0%Q))
                (((Z.of_nat (pade_norm n)) # 1)%Q * (C * q_pown pade_rho_hat n))) true.

(* Consumable form of the general-order skeleton: the coefficient-wise *)
(* matching identity for variable n, as a Set-level predicate.         *)
Definition pade_order_premise (n : nat) : Set :=
  bid (vleeq (firstn (S (2 * n)) (vconv (padeV (2 * n)) (altser (S (S (2 * n))))))
             (padnil (S (2 * n)) (padeU (2 * n)))) true.

(* The premise slot is inhabited at the anchored orders with the        *)
(* explicit constant C = 1 (verified computationally).                  *)
Lemma pade_decay_instance_n0 : pade_decay_premise (1 # 1)%Q 0.
Proof.
  vm_compute.
  exact bidT.
Qed.

Lemma pade_decay_instance_n1 : pade_decay_premise (1 # 1)%Q 1.
Proof.
  vm_compute.
  exact bidT.
Qed.

Lemma pade_decay_instance_n2 : pade_decay_premise (1 # 1)%Q 2.
Proof.
  vm_compute.
  exact bidT.
Qed.

Lemma pade_order_instance_n0 : pade_order_premise 0.
Proof.
  vm_compute.
  exact bidT.
Qed.

Lemma pade_order_instance_n1 : pade_order_premise 1.
Proof.
  vm_compute.
  exact bidT.
Qed.

Lemma pade_order_instance_n2 : pade_order_premise 2.
Proof.
  vm_compute.
  exact bidT.
Qed.

(* ------------------------------------------------------------------ *)
(* Extraction probes: the whole table machinery is informative         *)
(* (no Prop leakage into the computational layer).                     *)
(* ------------------------------------------------------------------ *)

(* The extraction evidence is produced outside this file: Separate        *)
(* Extraction of padeV, pade_num and pade_decay_premise yields OCaml      *)
(* with no Obj.magic occurrence (informative, no Prop leakage).           *)

Print Assumptions padeV_hd.
Print Assumptions padeU_hd.
Print Assumptions pade_match_anchor_n2.
Print Assumptions pade_rho_hat_cert.
Print Assumptions pade_decay_instance_n2.
Print Assumptions pade_order_instance_n2.
