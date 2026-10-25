(* ConstructiveWorld-Set — Bridge identity between two finite tails of the rational exponential series. *)

(** * QTailBridge: [qtail_sum] versus [exp_tail] on shifted indices.

    Mission.  The two finite tails [qtail_sum b m n = sum_{k=m}^{n-1}
    b^k/k!] (positive indices) and [exp_tail m n x = sum_{k=m}^{n-1}
    x^{S k}/(S k)!] (indices shifted by one) agree after unshifting:
    the main statements are [qtb_qtail_sum_eq_exp_tail] and its
    Set-carried form [qtb_qtail_sum_eq_exp_tail_T],
    [qtail_sum b m n == exp_tail (pred m) (pred n) b] for [m, n >= 1],
    proved by induction on the tail index.  The numerical instance
    [qtb_eval_example] checks [qtail_sum 3 1 5 = 3 + 9/2 + 9/2 + 27/8
    = 123/8] by [vm_compute].

    Dependencies.  Stdlib [QArith.QArith].  Requires [S01_BaseRing],
    [S02_CauchyComplete], [S03_QExp], [UpReqQExpTail] of this
    development.

    References.  This development, UpReqQExpTail.v, the baseline module
    in ConstructiveWorld-Main whose statement names are carried over
    here verbatim (statement-face Set-carrier completion).

    Constructivity.  Statements are carried by [Set] ([QeqT] at the
    export, [Qeq] companions for internal reasoning); the index
    premise [(1 <= m)%nat] is a [nat]-level condition.  No classical
    axioms; statements extract with [Obj.magic] = 0; [coqchk] reports
    [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" QTailBridge.v]
    compiles cleanly (exit 0); artifact magic [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqQExpTail.
From Stdlib Require Import QArith.QArith Arith.Arith Lia.
From Stdlib Require Import Setoid.

(* ===== Part 0. Conversion between [Nat.pred] and truncated subtraction ===== *)

Lemma qtb_pred_sub : forall m : nat, @Id nat (Nat.pred m) ((m - 1)%nat).
Proof.
  intros m.
  exact (match eq_sym (Nat.sub_1_r m) in (_ = y) return @Id nat (Nat.pred m) y
         with eq_refl => id_refl end).
Qed.

(* ===== Part 1. Induction core, with [m >= 1] fixed =====

   The statement is [qtail_sum b m (S n) == exp_tail (pred m) n b].
   The base case [n = 0] discharges the guard via [m >= 1]; the step
   converts both guards and aligns the term indices. *)

Lemma qtb_bridge_aux : forall (b : Q) (n m : nat),  
 (1 <= m)%nat -> QeqT (qtail_sum b m (Datatypes.S n)) (exp_tail (Nat.pred m) n b).
Proof.
  intros b n. induction n as [| n IH]; intros m Hm; apply qeq_imp_qeqT.
  - (* Base [n = 0]: the sum [qtail_sum b m 1] is empty for [m >= 1],
       while [exp_tail (pred m) 0] is definitionally [0]. *)
    change (qtail_sum b m (Datatypes.S 0))
      with ((if Nat.leb m 0 then q_pow b 0 / q_fact 0 else 0)
            + qtail_sum b m 0).
    destruct (Nat.leb m 0) eqn:E.
    + apply Nat.leb_le in E. exfalso.
      exact (Nat.nle_succ_0 0 (Nat.le_trans _ _ _ Hm E)).
    + reflexivity.
  - (* Step [n -> S n]: unfold one Fixpoint step on each side through
       [change] (plain [simpl] would over-expand). *)
    change (qtail_sum b m (Datatypes.S (Datatypes.S n)))
      with ((if Nat.leb m (Datatypes.S n)
             then q_pow b (Datatypes.S n) / q_fact (Datatypes.S n)
             else 0)
            + qtail_sum b m (Datatypes.S n)).
    change (exp_tail (Nat.pred m) (Datatypes.S n) b)
      with (exp_tail (Nat.pred m) n b
            + (if Nat.leb (Nat.pred m) n
               then q_pow b (Datatypes.S n) / q_fact (Datatypes.S n)
               else 0)).
    rewrite (qeqT_imp_qeq _ _ (IH m Hm)).
    destruct (Nat.leb m (Datatypes.S n)) eqn:E1;
      destruct (Nat.leb (Nat.pred m) n) eqn:E2.
    + (* Both guards true: identical terms, up to addition commutativity. *) ring.
    + (* Left true, right false: contradiction between [n < pred m]
       and [m <= S n]. *)
      apply Nat.leb_le in E1.
      apply Nat.leb_gt in E2. exfalso.
      pose proof (Nat.succ_pred_pos m Hm) as Hsp.
      rewrite <- Hsp in E1.
      apply Nat.succ_le_mono in E1.
      exact (Nat.lt_irrefl n (Nat.lt_le_trans _ _ _ E2 E1)).
    + (* Left false, right true: contradiction between [S n < m]
       and [pred m <= n]. *)
      apply Nat.leb_gt in E1.
      apply Nat.leb_le in E2. exfalso.
      pose proof (Nat.succ_pred_pos m Hm) as Hsp.
      rewrite <- Hsp in E1.
      apply Nat.succ_le_mono in E1.
      exact (Nat.lt_irrefl n (Nat.lt_le_trans _ _ _ E1 E2)).
    + (* Both guards false: two empty sums. *) ring.
Qed.


Theorem qtb_qtail_sum_eq_exp_tail : forall (b : Q) (m n : nat),  
 (1 <= m)%nat -> (1 <= n)%nat ->  
 QeqT (qtail_sum b m n) (exp_tail (Nat.pred m) (Nat.pred n) b).
Proof.
  intros b m n Hm Hn.
  destruct n as [| n'].
  - exfalso. exact (Nat.nle_succ_0 0 Hn).
  - change (Nat.pred (Datatypes.S n')) with n'.
    apply (qtb_bridge_aux b n' m Hm).
Qed.

(* ===== Part 3. Set-carried export ([QeqT] on the statement face) ===== *)

Theorem qtb_qtail_sum_eq_exp_tail_T : forall (b : Q) (m n : nat),
  (1 <= m)%nat -> (1 <= n)%nat ->
  QeqT (qtail_sum b m n) (exp_tail (Nat.pred m) (Nat.pred n) b).
Proof.
  intros b m n Hm Hn.
  exact (qtb_qtail_sum_eq_exp_tail b m n Hm Hn).
Qed.

(* ===== Part 4. Numerical instance closed by [vm_compute] ===== *)
(* qtail_sum 3 1 5 = sum_{k=1}^{4} 3^k/k! = 3 + 9/2 + 9/2 + 27/8 = 123/8;
   exp_tail 0 4 3  = sum_{k=0}^{3} 3^(k+1)/(k+1)! — the same terms after
   reindexing. *)

Lemma qtb_eval_example : QeqT (qtail_sum (3 # 1) 1%nat 5%nat)
                              (exp_tail 0%nat 4%nat (3 # 1)).
Proof. vm_compute. reflexivity. Qed.

(* Assumption audit of the main statements. *)

Print Assumptions qtb_qtail_sum_eq_exp_tail.
Print Assumptions qtb_qtail_sum_eq_exp_tail_T.
