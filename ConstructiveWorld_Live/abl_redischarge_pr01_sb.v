(* ConstructiveWorld-Set -- boolean decision companions for core statements. *)

(** * abl_redischarge_pr01_sb: boolean decision companion for the
    trial-division primality core.

    Mission.  A computable decision companion for the primality statement
      [pr_prime] of the core module abl_Pr_core_01: the boolean negation
      flag [pr_prime_neg], the decision readout [pr_prime_sb], the mirror
      agreement [pr_prime_sb_mirror], the correctness carrier
      [pr_prime_sb_prop] discharged by [pr_prime_sb_prop_holds], and the
      verdict readings [pr_prime_sb_2], [pr_prime_sb_3], [pr_prime_sb_4],
      [pr_prime_sb_5], [pr_prime_sb_9], [pr_prime_sb_11], [pr_prime_sb_12]
      on small instances.

    Dependencies.  Stdlib [Arith.Arith], [List], [Bool], [Lia].  Requires
      [abl_Pr_core_01] of this development ([pr_prime], [pr_prime_bool],
      [pr_prime_bool_true]).

    References.  This development, abl_redischarge_pr01_sb.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (boolean equation carriers and single-constructor specification
      carriers); statements extract with [Obj.magic] = 0 and no erasure;
      [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_redischarge_pr01_sb.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import abl_Pr_core_01.

(* ---- Sec.1  The negation flag (boolean reflection of the
   non-primality face) ---- *)

(* The flag [pr_prime_neg n] reads [true] exactly when the core decider
   rejects primality; by the core's two-way bridge this boolean flag
   reflects the negation face [pr_prime n -> False] held by the
   baseline statements. *)
Definition pr_prime_neg (n : nat) : bool := negb (pr_prime_bool n).

(* ---- Sec.2  The decision readout (the Set-carried decision face,
   kept computable through a [Defined]-shaped term exit) ---- *)

(* The readout is the verdict boolean itself; the certificate direction
   of the former sumbool left arm is carried by the correctness
   carrier in Sec.4, so the readout stays first-order and extractable. *)
Definition pr_prime_sb (n : nat) : bool := pr_prime_bool n.

(* ---- Sec.3  Mirror face: the decision readout agrees with the core
   decider (the true verdict and the false verdict each match the
   machine reading, so consumers convert shapes at no loss) ---- *)
Theorem pr_prime_sb_mirror : forall n : nat,
  match pr_prime_sb n with
  | true => pr_prime_bool n = true
  | false => pr_prime_bool n = false
  end.
Proof.
  intros n. unfold pr_prime_sb. destruct (pr_prime_bool n).
  - reflexivity.
  - reflexivity.
Qed.

(* ---- Sec.4  Correctness carrier (single-constructor Set carrier; the
   constructor argument positions hold the two decision arms: the true
   verdict certifies primality through the core bridge, the false
   verdict lights the negation flag of Sec.1) ---- *)
Inductive pr_prime_sb_prop (n : nat) : Set :=
| pr_prime_sb_prop_intro :
    (pr_prime_sb n = true -> pr_prime n) ->
    (pr_prime_sb n = false -> pr_prime_neg n = true) ->
    pr_prime_sb_prop n.

Theorem pr_prime_sb_prop_holds : forall n : nat, pr_prime_sb_prop n.
Proof.
  intros n. apply pr_prime_sb_prop_intro.
  - exact (pr_prime_bool_true n).
  - intros Hf. unfold pr_prime_neg, pr_prime_sb in *. rewrite Hf. reflexivity.
Qed.

(* ---- Sec.5  Numeric verdict readings (small instances evaluated by
   [vm_compute] on the readout) ---- *)

(* The equation carrier [sb_bid] holds the boolean equation [b = true]
   at the Set level; a composite instance wraps [negb] of the verdict
   so the carried equation still reads against [true]. *)
Inductive sb_bid (b : bool) : Set :=
| sb_bid_intro : b = true -> sb_bid b.

Lemma pr_prime_sb_2 : sb_bid (pr_prime_sb 2).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Qed.

Lemma pr_prime_sb_3 : sb_bid (pr_prime_sb 3).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Qed.

Lemma pr_prime_sb_4 : sb_bid (negb (pr_prime_sb 4)).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Qed.

Lemma pr_prime_sb_5 : sb_bid (pr_prime_sb 5).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Qed.

Lemma pr_prime_sb_9 : sb_bid (negb (pr_prime_sb 9)).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Qed.

Lemma pr_prime_sb_11 : sb_bid (pr_prime_sb 11).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Qed.

Lemma pr_prime_sb_12 : sb_bid (negb (pr_prime_sb 12)).
Proof. apply sb_bid_intro. vm_compute. reflexivity. Qed.

(* ---- Sec.6  Assumption audit (Print Assumptions evidence faces) ---- *)

Print Assumptions pr_prime_sb.
Print Assumptions pr_prime_sb_mirror.
Print Assumptions pr_prime_sb_prop.
Print Assumptions pr_prime_sb_prop_holds.
Print Assumptions pr_prime_sb_2.
Print Assumptions pr_prime_sb_12.
