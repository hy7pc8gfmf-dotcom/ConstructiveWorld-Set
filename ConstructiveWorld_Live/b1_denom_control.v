(* ConstructiveWorld-Set — denominator control for the Beukers-arctan
   linear forms (b1_ prefix, odd-clearance layer). *)

(** * b1_denom_control: double-factorial denominator control.

    Mission.  The double-factorial carriers [b1_dfact_odd] and
      [b1_dfact_even]; the power-of-two reading [b1_dfact_even_pow]
      ([b1_dfact_even n = 2^n * n!]); the odd-le-even domination
      [b1_dfact_odd_le_even] (nat-side bearing of the central
      binomial fold C(2n,n) <= 4^n; the Q-side Beta <= 1 decay leg
      lives with [b1_seg_beta_le1] via [pei_fact_le]); the odd
      denominator clearance witness [b1_odd_div_dfact] in sigT
      multiplier form (k <= n yields q with [q * (2k+1) =
      b1_dfact_odd (S n)]); the positivity [b1_dfact_odd_pos].

    Dependencies.  Stdlib [QArith.QArith], [ZArith.ZArith],
      [Arith.Arith], [Arith.Factorial], [Lia], [Setoid], [Morphisms];
      requires [S01_BaseRing] ([Id]/[NatLe] with lift/drop bridges).

    References.  ConstructiveWorld-Main, module [b1_denom_control];
      statement names carried over verbatim (statement-face
      Set-carrier completion).

    Constructivity.  Statement faces carried by [Set] (sigT
      multiplier witnesses, [Id], [NatLe]); extraction with
      [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -Q . "" b1_denom_control.v];
      artifact magic [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Arith.Factorial Lia.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing.

Open Scope nat_scope.

(* ================= Section 1. Double-factorial carriers ================= *)

Fixpoint b1_dfact_odd (n : nat) : nat :=
  match n with
  | O => 1
  | Datatypes.S k => (2 * k + 1) * b1_dfact_odd k
  end.

Fixpoint b1_dfact_even (n : nat) : nat :=
  match n with
  | O => 1
  | Datatypes.S k => (2 * Datatypes.S k) * b1_dfact_even k
  end.

(* The power-of-two reading of the even factorial: [2^n * n!]. *)
Theorem b1_dfact_even_pow : forall n : nat,
  Id (b1_dfact_even n) ((2 ^ n) * (fact n)).
Proof.
  intros n.
  assert (Heq : b1_dfact_even n = (2 ^ n) * (fact n)).
  { induction n as [| k IH].
    - reflexivity.
    - cbn [b1_dfact_even fact].
      rewrite IH. rewrite Nat.pow_succ_r'.
      ring. }
  destruct Heq. apply id_refl.
Qed.

(* Stepwise reading: [b1_dfact_odd (S k) = (2k+1) * b1_dfact_odd k]
   holds by definition. *)
Lemma b1_dfact_odd_unfold : forall k : nat,
  Id (b1_dfact_odd (Datatypes.S k)) ((2 * k + 1) * b1_dfact_odd k).
Proof. intros k. apply id_refl. Qed.

(* ================= Section 2. Odd-le-even domination (nat side of
   the central binomial fold) ================= *)

Theorem b1_dfact_odd_le_even : forall n : nat,
  NatLe (b1_dfact_odd n) (b1_dfact_even n).
Proof.
  induction n as [| k IH].
  - exact id_refl.
  - apply NatLe_lift.
    apply (Nat.le_trans ((2 * k + 1) * b1_dfact_odd k)
                        ((2 * k + 1) * b1_dfact_even k)
                        ((2 * Datatypes.S k) * b1_dfact_even k)).
    + apply NatLe_drop in IH. apply Nat.mul_le_mono_l. exact IH.
    + replace (2 * Datatypes.S k)%nat with (2 * k + 2)%nat by lia.
      apply Nat.mul_le_mono_r. lia.
Qed.

(* Positivity: [b1_dfact_odd n >= 1]. *)
Theorem b1_dfact_odd_pos : forall n : nat, NatLe 1 (b1_dfact_odd n).
Proof.
  induction n as [| k IH].
  - exact id_refl.
  - apply NatLe_lift.
    apply (Nat.le_trans 1 (1 * b1_dfact_odd k) ((2 * k + 1) * b1_dfact_odd k)).
    + replace (1 * b1_dfact_odd k) with (b1_dfact_odd k) by lia.
      apply NatLe_drop. exact IH.
    + apply Nat.mul_le_mono_r. lia.
Qed.

(* ================= Section 3. Odd denominator clearance (sigT
   multiplier witnesses) ================= *)

(* k <= n yields q with [q * (2k+1) = b1_dfact_odd (S n)]: the odd
   factor 2k+1 divides (2n+1)!!. *)
Theorem b1_odd_div_dfact : forall (n k : nat), (k <= n)%nat ->
  sigT (fun q : nat => Id (q * (2 * k + 1)) (b1_dfact_odd (Datatypes.S n))).
Proof.
  intros n. induction n as [| n' IHn]; intros k Hk.
  - (* n = 0: k = 0 and the witness is 1. *)
    assert (Hk0 : k = 0%nat) by lia.
    rewrite Hk0. exists 1%nat. reflexivity.
  - (* n = S n': either k is the top factor or k <= n' carries over. *)
    destruct (Nat.eq_dec k (Datatypes.S n')) as [Hke | Hkle].
    + rewrite Hke.
      exists (b1_dfact_odd (Datatypes.S n'))%nat.
      rewrite (Nat.mul_comm (b1_dfact_odd (Datatypes.S n'))
                            (2 * Datatypes.S n' + 1)).
      reflexivity.
    + assert (Hk' : (k <= n')%nat) by lia.
      destruct (IHn k Hk') as [q Hq].
      exists ((2 * Datatypes.S n' + 1) * q)%nat.
      apply (@Id_rec nat (q * (2 * k + 1))
               (fun d _ => Id (((2 * Datatypes.S n' + 1) * q) * (2 * k + 1))
                             ((2 * Datatypes.S n' + 1) * d))).
      * rewrite (Nat.mul_assoc (2 * Datatypes.S n' + 1) q (2 * k + 1)).
        apply id_refl.
      * exact Hq.
Qed.

(* ================= Section 4. Numeric anchors ================= *)

(* dfact_odd(4) = 1*3*5*7 = 105. *)
Lemma b1_dfact_odd_anchor : Id (b1_dfact_odd 4) 105.
Proof. reflexivity. Qed.

(* dfact_even(4) = 2*4*6*8 = 384 = 2^4 * 4!. *)
Lemma b1_dfact_even_anchor : Id (b1_dfact_even 4) 384.
Proof. reflexivity. Qed.

(* Clearance instance: 15*7 = 105 (k = 3, n = 3). *)
Lemma b1_odd_div_anchor :
  sigT (fun q : nat => Id (q * 7) (b1_dfact_odd 4)).
Proof. exists 15%nat. reflexivity. Qed.

(* Domination instance: 105 <= 384. *)
Lemma b1_dfact_le_anchor : NatLe (b1_dfact_odd 4) (b1_dfact_even 4).
Proof. exact id_refl. Qed.

(* ================= Section 5. Smoke checks and assumption audit ================= *)

Check b1_dfact_even_pow.
Check b1_dfact_odd_le_even.
Check b1_dfact_odd_pos.
Check b1_odd_div_dfact.
Check b1_dfact_odd_anchor.

Print Assumptions b1_dfact_even_pow.
Print Assumptions b1_dfact_odd_le_even.
Print Assumptions b1_dfact_odd_pos.
Print Assumptions b1_odd_div_dfact.
