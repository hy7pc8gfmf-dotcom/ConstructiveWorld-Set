(* ConstructiveWorld-Set — Banach-algebra exponential family: statement-cluster collection with instantiation carriers. *)

(** * Arch_Banach_01: statement-cluster collection and instantiation
      carriers for the Banach-algebra exponential.

    Mission.  Formalizes the following statement families: [bnhn_bnorm_plus],
      [bnhn_bnorm_mult], [bxcb_q_choose_out], [bxcb_binom_eq_choose],
      [bxcb_sentinel_bpa_4_2], [bxcb_sentinel_qchoose_4_2],
      [bxcb_sentinel_bridge_4_2], [bxcb_sentinel_out_bpa_1_2], and
      [bxcb_sentinel_out_qchoose_1_2], together with the merged member
      families carried by the section banners below (bxcb / bxdef / bxae /
      bxoo / s3c).

    Dependencies.  The library files listed in the Require face below.

    References.  This development; the baseline module of the same name in
      ConstructiveWorld-Main, whose statement names are carried over
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All proofs close by [Qed], zero admission tokens, no
      classical logic; the statement face is carried by the [Set] layer with
      zero Prop leakage.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      Arch_Banach_01.v] compiles cleanly (exit 0); the first eight bytes of
      the artifact are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqBanachInstB.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import UpReqBanachAdd.
Require Import UpReqBanachProd2.
From Stdlib Require Import Setoid.
Require Import UpReqBanachExp.
Require Import UpReqBanachExpDef.
Require Import UpReqBanachProd.
Require Import UpReqBanachExpAdd.
Require Import UpReqBanachClassExt.
Require Import UpReqBanachLimUniq.
Require Import UpReqNormConv.
Require Import BanachNoHyp.
From Stdlib Require Import Setoid Lia.
Require Import UpReqBanachCauchyD.
Require Import UpReqBanachDouble.
Require Import UpReqBanachInvPre.

(* ================= §1 the bnhn_bnorm_plus family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* Piece 1: the bnorm_plus field position (subadditivity) —                          *)
(*   QleT' (bnorm (eplus a b)) (bnorm a + bnorm b)                                   *)
(*   (the colocated theorem for the class field bnorm_plus on the E-carrier          *)
(*   bxib_E; the double qnorm degeneration plus a three-leg transport via            *)
(*   Qabs_triangle.)                                                                 *)

Lemma bnhn_bnorm_plus : forall a b : bxib_E,
  QleT' (bxib_bnorm (bxib_eplus a b))
        (bxib_bnorm a + bxib_bnorm b)%Q.
Proof.
  intros a b. unfold bxib_bnorm.
  change (bxib_ev (bxib_eplus a b))
    with (bxib_qnorm (Qplus (bxib_ev a) (bxib_ev b))).
  (* double qnorm degeneration (an Id fixed point; the Leibniz rewrite is legitimate inside the QleT' goal) *)
  rewrite (bxib_qnorm_fix_id (Qplus (bxib_ev a) (bxib_ev b))).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxib_ev a + bxib_ev b)%Q) _).
  - (* left-end transport: |qnorm (x+y)| ≤ |x+y| (Qeq transport, not a pinned position) *)
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    exact (Qabs_wd _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev a + bxib_ev b)%Q))).
  - apply (Qle_trans _ (Qabs (bxib_ev a)%Q + Qabs (bxib_ev b)%Q)%Q _).
    + (* the triangle inequality (stdlib [Qabs_triangle]) *)
      apply Qabs_triangle.
    + (* right-end transport: |x|+|y| ≤ |qnorm x|+|qnorm y|
         (the Qplus_comp Proper term with the interleaved argument order x x' Hx y y' Hy) *)
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      exact (Qplus_comp (Qabs (bxib_ev a)%Q) (Qabs (bxib_qnorm (bxib_ev a)))
               (Qabs_wd _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev a)))))
               (Qabs (bxib_ev b)%Q) (Qabs (bxib_qnorm (bxib_ev b)))
               (Qabs_wd _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev b)))))).
Qed.

(* Piece 2: the bnorm_mult field position (submultiplicativity) —                    *)
(*   QleT' (bnorm (emult a b)) (bnorm a * bnorm b)                                   *)
(*   (the colocated theorem for the class field bnorm_mult on the E-carrier          *)
(*   bxib_E; the same degeneration plus an equality transport by Qabs_Qmult —        *)
(*   Qeq is stronger than Qle and is demoted through qeq_le.)                        *)

Lemma bnhn_bnorm_mult : forall a b : bxib_E,
  QleT' (bxib_bnorm (bxib_emult a b))
        (bxib_bnorm a * bxib_bnorm b)%Q.
Proof.
  intros a b. unfold bxib_bnorm.
  change (bxib_ev (bxib_emult a b))
    with (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev b))).
  rewrite (bxib_qnorm_fix_id (Qmult (bxib_ev a) (bxib_ev b))).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxib_ev a * bxib_ev b)%Q) _).
  - (* left-end transport: |qnorm (x*y)| ≤ |x*y| *)
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    exact (Qabs_wd _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev a * bxib_ev b)%Q))).
  - apply (Qle_trans _ (Qabs (bxib_ev a)%Q * Qabs (bxib_ev b)%Q)%Q _).
    + (* |x*y| == |x|·|y| (stdlib [Qabs_Qmult]; Qeq demoted to Qle via qeq_le) *)
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
    + (* right-end transport: |x|·|y| ≤ |qnorm x|·|qnorm y|
         (the Qmult_comp Proper term with the interleaved argument order x x' Hx y y' Hy) *)
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      exact (Qmult_comp (Qabs (bxib_ev a)%Q) (Qabs (bxib_qnorm (bxib_ev a)))
               (Qabs_wd _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev a)))))
               (Qabs (bxib_ev b)%Q) (Qabs (bxib_qnorm (bxib_ev b)))
               (Qabs_wd _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev b)))))).
Qed.

(* Verification record (declared symmetrically, no admission-face pieces):          *)
(*   (1) this file closes unresolved item (1) of INSTB: the four multiplication-group  *)
(*     faces (the bxem_ series) plus bnorm_plus/bnorm_mult (this file's bnhn_) are     *)
(*     all filled in; the E-carrier has no remaining gaps in the frozen class's         *)
(*     algebra/norm field positions (the completeness fields are listed separately,     *)
(*     as in the INS precedent, and the bnorm_coef pinned-statement revision is an      *)
(*     upstream reshaping — both keep their original unresolved status).                *)
(*   (2) accompanying note: bxem_mult and bxib_emult are delta-identical definitions    *)
(*     (bxem_mult a b := bxib_emult a b); the statement face here takes the constructor *)
(*     direct form.                                                                     *)
(*   (3) degeneration-machinery homology: this file's double degeneration matches       *)
(*     bxem_mult_wd (the QleT' version of the fix_id -> qnorm_id_of_qeqT -> fix_id      *)
(*     chain), with Qabs_triangle/Qabs_Qmult replacing bxem's qeqT cong positions on    *)
(*     the order face.                                                                  *)

Separate Extraction bnhn_bnorm_plus bnhn_bnorm_mult.

Print Assumptions bnhn_bnorm_plus.
Print Assumptions bnhn_bnorm_mult.
(* ================= §2 the bxcb_q_choose_out family ================= *)
(* ================= §1 the bxcb_q_choose_out family ================= *)
(* ================= §1 the bxcb_q_choose_out family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* S1: out-of-range semantics alignment — making the Nat.sub truncation shape of    *)
(* q_choose explicit.  For k>n the (n−k) is truncated to 0 and the denominator      *)
(* q_fact 0 = 1, hence q_choose n k                                                 *)
(*   == q_fact n / q_fact k == q_fact n * Qinv (q_fact k) ≠ 0,                      *)
(* which keeps the two sides' out-of-range semantics in separate accounts against   *)
(* bpa_binom_out (== 0).                                                            *)

Lemma bxcb_q_choose_out : forall n k : nat, (n < k)%nat ->
  q_choose n k == q_fact n * Qinv (q_fact k).
Proof.
  intros n k H.
  unfold q_choose.
  assert (E : (n - k)%nat = 0%nat) by lia.
  rewrite E.
  change (q_fact 0%nat) with (1%Q).
  unfold Qdiv.
  setoid_rewrite (Qmult_1_r (q_fact k)).
  reflexivity.
Qed.

(* S2: the main bridge bxcb_binom_eq_choose (induction on n with a case split on k) *)
(*   forall n k, (k <= n)%nat -> bpa_binom n k == q_choose n k                      *)
(* Cases: k=0 (bpa_binom_0 ↔ q_choose_0); k=S n' the diagonal                       *)
(*   (bpa_binom_diag ↔ q_choose_n); the recursive step S k' < S n' — the left       *)
(*   Pascal side is the defining shape of bpa_binom (change/reflexivity level, the  *)
(*   BA technique); the right Pascal side takes S07's q_choose_succ (reused, not    *)
(*   rewritten); the final (S k'−1)≡k' is an iota conversion taken by Qeq_refl.     *)

Lemma bxcb_binom_eq_choose : forall n k : nat, (k <= n)%nat ->
  bpa_binom n k == q_choose n k.
Proof.
  intros n. induction n as [| n' IH]; intros k Hk.
  - destruct k as [| k']; [ apply Qeq_refl | lia ].
  - destruct k as [| k'].
    + rewrite bpa_binom_0.
      apply Qeq_sym. apply qeqT_imp_qeq. apply q_choose_0.
    + destruct (Nat.eq_dec k' n') as [Heq | Hne].
      * rewrite Heq.
        setoid_rewrite (qeqT_imp_qeq _ _ (bpa_binom_diag (Datatypes.S n'))).
        apply Qeq_sym. apply qeqT_imp_qeq. apply q_choose_n.
      * change (bpa_binom (Datatypes.S n') (Datatypes.S k'))
          with (bpa_binom n' k' + bpa_binom n' (Datatypes.S k'))%Q.
        setoid_rewrite (IH k' ltac:(lia)).
        setoid_rewrite (IH (Datatypes.S k') ltac:(lia)).
        setoid_rewrite (qeqT_imp_qeq _ _ (q_choose_succ n' (Datatypes.S k') ltac:(lia) ltac:(lia))).
        (* term order and the sub trap: the tail term of q_choose_succ is (S k'−1)
           (with k' a variable, Nat.sub does not reduce — in contrast to the S-shaped
           form where truncation is avoided); a lia-provided nat-level equation converts
           it back to k'; the bpa defining shape lists the k' term first, so a
           non-definitional Qplus swap reorders it — after these two steps both sides
           share the same shape and Qeq_refl closes *)
        assert (Esub : (Datatypes.S k' - 1)%nat = k'%nat) by lia.
        rewrite Esub.
        setoid_rewrite (Qplus_comm (q_choose n' k') (q_choose n' (Datatypes.S k'))).
        apply Qeq_refl.
Qed.

(* S3: numeric anchor face (reflexivity/vm_compute-level spot checks) *)

Lemma bxcb_sentinel_bpa_4_2 : bpa_binom 4%nat 2%nat == (6 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma bxcb_sentinel_qchoose_4_2 : q_choose 4%nat 2%nat == (6 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* check on the bridge: the main bridge instantiated at (4,2) gives ==6 on both sides *)
Lemma bxcb_sentinel_bridge_4_2 : bpa_binom 4%nat 2%nat == q_choose 4%nat 2%nat.
Proof. apply bxcb_binom_eq_choose. lia. Qed.

(* out-of-range anchor pair (a concrete counterexample on record): at n=1, k=2 the  *)
(* two sides diverge — the bpa side gives 0, the q_choose side gives 1!/2! = 1/2    *)
(* (Qinv (2#1)); the two together show that an assumption-free full-domain bridge   *)
(* cannot be established, so the semantics-aligned (k<=n) face is necessary.        *)
Lemma bxcb_sentinel_out_bpa_1_2 : bpa_binom 1%nat 2%nat == 0%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma bxcb_sentinel_out_qchoose_1_2 : q_choose 1%nat 2%nat == Qinv (2 # 1).
Proof. vm_compute. reflexivity. Qed.

(* S4: the main lemma bxcb_term_split — C(k,j)/k! == 1/(j!·(k−j)!)                  *)
(* the dependency shape of the downstream exp_term_split.  S07 already has an       *)
(* identical original, q_choose_div_fact, which is reused rather than rewritten;    *)
(* the BA-side (bpa coefficient) dependency shape bxcb_term_split_binom is added.   *)

Lemma bxcb_term_split : forall k j : nat,
  q_choose k j / q_fact k == Qinv (q_fact j) * Qinv (q_fact (k - j)%nat).
Proof.
  intros k j.
  apply qeqT_imp_qeq. apply (q_choose_div_fact k j).
Qed.

Lemma bxcb_term_split_binom : forall k j : nat, (j <= k)%nat ->
  bpa_binom k j / q_fact k == Qinv (q_fact j) * Qinv (q_fact (k - j)%nat).
Proof.
  intros k j Hj.
  setoid_rewrite (bxcb_binom_eq_choose k j Hj).
  apply qeqT_imp_qeq. apply (q_choose_div_fact k j).
Qed.

(* S5: a thin bridge — instantiating bpr2_q_choose (the Prod2 factorial-ratio       *)
(* ported shape).                                                                   *)
(* bpr2_q_choose n k := q_fact n / (q_fact k * q_fact (Nat.sub n k))                *)
(* is definitionally isomorphic to q_choose n k (delta level); after a change       *)
(* transport the main bridge applies directly.                                      *)
(* Division of labor: S07's q_choose is the frozen original; bpr2_ is the Prod2     *)
(* ported shape; bpa_binom is the Add-Pascal shape.  This bridge gathers the three  *)
(* shapes onto one equivalence face.                                                *)

Lemma bxcb_binom_eq_bpr2 : forall n k : nat, (k <= n)%nat ->
  bpa_binom n k == bpr2_q_choose n k.
Proof.
  intros n k H.
  change (bpr2_q_choose n k) with (q_choose n k).
  apply bxcb_binom_eq_choose. exact H.
Qed.

(*   "Closed under the global context"; Separate Extraction of                      *)
(*   UpReqBanachBinomBridge.ml gives an Obj.magic count of 0; coqchk -o passes       *)
(*   for all pieces.                                                                 *)

(* ---- assumption print-out: each listed piece's assumption face printed individually, all read Closed ---- *)
Print Assumptions bxcb_term_split.
(* ================= §2 the bxdef_emul family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* S0: bxdef_emul — the exp element multiplication (the connection position of the main lemma's left argument; a tree-wide census shows no earlier name) *)

Definition bxdef_emul (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x y : BA) : BA :=
  @bmult _ _ B x y.

(* S1: Q-layer utility lemmas (Prop-engine internals, zero lia) *)

Lemma bxae_1p1_neq_0 : ~ ((1 + 1)%Q == 0)%Q.
Proof. intros Hz. vm_compute in Hz. discriminate. Qed.

Lemma bxae_qlt_0_1 : Qlt 0 1%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma bxae_qlt_0_2 : Qlt 0 (1 + 1)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma bxae_qltT_0_1 : QltT 0 1%Q.
Proof. apply Qlt_to_QltT. exact bxae_qlt_0_1. Qed.

(* x ≤ x + y (0 ≤ y) *)
Lemma bxae_Qle_add_r : forall x y : Q, Qle 0 y -> Qle x (x + y)%Q.
Proof.
  intros x y Hy.
  apply (Qle_trans x (0 + x)%Q (x + y)%Q).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans (0 + x)%Q (y + x)%Q (x + y)%Q).
    + apply (Qplus_le_compat 0%Q y x x).
      * exact Hy.
      * apply Qle_refl.
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

(* x ≤ y + x (0 ≤ y) *)
Lemma bxae_Qle_add_l : forall x y : Q, Qle 0 y -> Qle x (y + x)%Q.
Proof.
  intros x y Hy.
  apply (Qle_trans x (0 + x)%Q (y + x)%Q).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - apply (Qplus_le_compat 0%Q y x x).
    + exact Hy.
    + apply Qle_refl.
Qed.

(* 1 ≤ 2 *)
Lemma bxae_Qle_1_2 : Qle 1%Q (1 + 1)%Q.
Proof. apply bxae_Qle_add_r. apply QleT'_to_Qle. apply Qle_0_1. Qed.

(* strict monotonicity of right multiplication (the Qmult_lt_r iff face) *)
Lemma bxae_mult_lt_r : forall x y z : Q,
  Qlt x y -> Qlt 0 z -> Qlt (x * z) (y * z)%Q.
Proof.
  intros x y z Hxy Hz.
  exact (proj2 (Qmult_lt_r x y z Hz) Hxy).
Qed.

(* field-law cancellation: e·/(y·x)·x == e·/y *)
Lemma bxae_cancel_mul : forall e x y : Q,
  ~ (y == 0) -> ~ (y * x == 0) -> (e * / (y * x)) * x == e * / y.
Proof.
  intros e x y Hy Hyx.
  assert (Hx0 : ~ (x == 0)).
  { intros Hx. apply Hyx. rewrite Hx. ring. }
  field. split; assumption.
Qed.

(* half-sum merge: e·/2 + e·/2 == e *)
Lemma bxae_half_add : forall e : Q, (e * / (1 + 1) + e * / (1 + 1))%Q == e%Q.
Proof. intros e. field. Qed.

(* series terms nonnegative: 0 ≤ X^k/k! *)
Lemma bxae_term_nonneg : forall (X : Q) (k : nat),
  Qle 0 X -> Qle 0 (q_pow X k / q_fact k)%Q.
Proof.
  intros X k HX. unfold Qdiv.
  assert (Hinv : Qlt 0 (Qinv (q_fact k)))
    by (apply Qinv_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos).
  apply (Qle_trans 0%Q (0 * Qinv (q_fact k))%Q
                   (q_pow X k * Qinv (q_fact k))%Q).
  - rewrite Qmult_0_l. apply Qle_refl.
  - apply (proj2 (Qmult_le_r 0 (q_pow X k) (Qinv (q_fact k)) Hinv)).
    apply QleT'_to_Qle. apply (q_pow_nonneg X k).
    apply Qle_to_QleT'. exact HX.
Qed.

(* the tail sum is nonnegative *)
Lemma bxae_etab_nonneg : forall (X : Q) (m n : nat),
  Qle 0 X -> Qle 0 (exp_tail_abs m n X).
Proof.
  intros X m n HX. induction n as [| n' IH].
  - simpl. apply Qle_refl.
  - change (exp_tail_abs m (Datatypes.S n') X)
      with (exp_tail_abs m n' X
            + (if Nat.leb m n'
               then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
               else 0)%Q).
    destruct (Nat.leb m n').
    + apply (Qplus_le_compat 0%Q (exp_tail_abs m n' X) 0%Q
               (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))).
      * exact IH.
      * exact (bxae_term_nonneg X (Datatypes.S n') HX).
    + apply (Qle_trans 0%Q (exp_tail_abs m n' X) (exp_tail_abs m n' X + 0)%Q).
      * exact IH.
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. symmetry. apply Qplus_0_r.
Qed.


(* the tail sum is antitone in its start: m1 ≤ m2 ⟹ tail(m2..n) ≤ tail(m1..n) *)
Lemma bxae_etab_mono_start : forall (X : Q) (m1 m2 n : nat),
  Qle 0 X -> (m1 <= m2)%nat -> Qle (exp_tail_abs m2 n X) (exp_tail_abs m1 n X).
Proof.
  intros X m1 m2 n HX Hm. revert m1 m2 Hm.
  induction n as [| n' IH]; intros m1 m2 Hm.
  - simpl. apply Qle_refl.
  - change (exp_tail_abs m1 (Datatypes.S n') X)
      with (exp_tail_abs m1 n' X
            + (if Nat.leb m1 n'
               then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
               else 0)%Q).
    change (exp_tail_abs m2 (Datatypes.S n') X)
      with (exp_tail_abs m2 n' X
            + (if Nat.leb m2 n'
               then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
               else 0)%Q).
    destruct (Nat.leb m2 n') eqn:Em2.
    { assert (Hm2n' : (m2 <= n')%nat) by (apply Nat.leb_le; exact Em2).
      assert (Hm1n' : (m1 <= n')%nat) by lia.
      rewrite (proj2 (Nat.leb_le m1 n') Hm1n').
      apply (Qplus_le_compat (exp_tail_abs m2 n' X) (exp_tail_abs m1 n' X)
               (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))
               (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))).
      - exact (IH m1 m2 Hm).
      - apply (Qle_refl (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))). }
    { assert (E0 : (exp_tail_abs m2 n' X + 0)%Q == exp_tail_abs m2 n' X) by ring.
      apply (Qle_trans _ (exp_tail_abs m1 n' X)).
      - apply (Qle_trans _ (exp_tail_abs m2 n' X)).
        + exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ E0))).
        + exact (IH m1 m2 Hm).
      - apply bxae_Qle_add_r. destruct (Nat.leb m1 n').
        + exact (bxae_term_nonneg X (Datatypes.S n') HX).
        + apply Qle_refl. }
Qed.
(* the tail sum splits additively: tail(m1..n) == tail(m1..m2) + tail(m2..n) *)
Lemma bxae_etab_split : forall (X : Q) (m1 m2 n : nat),
  (m1 <= m2)%nat -> (m2 <= n)%nat ->
  exp_tail_abs m1 n X == (exp_tail_abs m1 m2 X + exp_tail_abs m2 n X)%Q.
Proof.
  intros X m1 m2 n Hm12 Hm2n. revert m1 m2 Hm12 Hm2n.
  induction n as [| n' IH]; intros m1 m2 Hm12 Hm2n.
  - assert (Hm20 : m2 = 0%nat) by lia. subst m2.
    assert (Hm10 : m1 = 0%nat) by lia. subst m1.
    simpl. ring.
  - destruct (Nat.leb m2 n') eqn:Em2.
    + assert (Hm2n' : (m2 <= n')%nat) by (apply Nat.leb_le; exact Em2).
      assert (Hm1n' : (m1 <= n')%nat) by lia.
      change (exp_tail_abs m1 (Datatypes.S n') X)
        with (exp_tail_abs m1 n' X
              + (if Nat.leb m1 n'
                 then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
                 else 0)%Q).
      change (exp_tail_abs m2 (Datatypes.S n') X)
        with (exp_tail_abs m2 n' X
              + (if Nat.leb m2 n'
                 then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
                 else 0)%Q).
      rewrite (proj2 (Nat.leb_le m1 n') Hm1n').
      rewrite (IH m1 m2 Hm12 Hm2n').
      rewrite Em2.
      set (T := (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))%Q).
      ring.
    + assert (Hlt : (n' < m2)%nat) by (apply Nat.leb_gt; exact Em2).
      assert (Hm2 : m2 = Datatypes.S n') by lia. subst m2.
      rewrite (qeqT_imp_qeq _ _ (exp_tail_abs_le_m (Datatypes.S n') (Datatypes.S n') X
                 (Nat.le_refl _))).
      ring.
Qed.

(* the tail sum is arbitrarily small: ∃N, m ≥ N ⟹ tail(m..n) < e (any n) *)
Lemma bxae_etab_small : forall (X e : Q),
  Qle 0 X -> QltT 0 e ->
  sigT (fun N : nat => forall m n : nat, (N <= m)%nat ->
    Qlt (exp_tail_abs m n X) e).
Proof.
  intros X e HX Heps.
  destruct (q_arch_geom X) as [N0 HN0].
  assert (Harch : forall u : nat, (N0 <= u)%nat ->
            Qle (Qmult (1 + 1)%Q X) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply QleT'_to_Qle. apply (HN0 u). apply NatLe_lift. exact Hu. }
  assert (H0C : QleT' 0 ((q_pow X N0 / q_fact N0) * (1 + 1))%Q).
  { exact (q_pow_fact2_nonneg X N0 (Qle_to_QleT' 0 X HX)). }
  destruct (arch_decay ((q_pow X N0 / q_fact N0) * (1 + 1)%Q) e H0C Heps)
    as [t Hdec].
  exists (N0 + Datatypes.S t)%nat.
  intros m n Hm.
  destruct (Nat.leb m n) eqn:Emn.
  - apply Nat.leb_le in Emn.
    apply (Qle_lt_trans _ ((q_pow X m / q_fact m) * (1 + 1)%Q) e).
    + apply QleT'_to_Qle.
      exact (exp_tail_abs_geom2 X m n (Qle_to_QleT' 0 X HX)
               (fun t0 Ht => HN0 t0 (NatLe_lift _ _
                 (Nat.le_trans N0 m t0 ltac:(lia) (NatLe_drop _ _ Ht)))) Emn).
    + apply QltT_to_Qlt.
      apply (exp_tail_arch X N0 t m e (Qle_to_QleT' 0 X HX) HN0 Heps Hdec).
      lia.
  - apply Nat.leb_gt in Emn.
    assert (Hnm : (n <= m)%nat) by lia.
    exact (QltT_to_Qlt _ _
             (QeqT_Qlt_bool_cong 0 (exp_tail_abs m n X) e
                (qeqT_sym_hw _ _ (exp_tail_abs_le_m m n X Hnm)) Heps)).
Qed.

(* the α partial sum == 1 + tail (with α_k := X^k/k!) *)
Lemma bxae_ncvsum_alpha : forall (X : Q) (n : nat),
  ncv_qsum (fun i : nat => q_pow X i / q_fact i) (Datatypes.S n)
  == (1 + exp_tail_abs 0 n X)%Q.
Proof.
  intros X n. induction n as [| n' IH].
  - simpl. unfold Qdiv. vm_compute. reflexivity.
  - change (ncv_qsum (fun i : nat => q_pow X i / q_fact i)
              (Datatypes.S (Datatypes.S n')))
      with (ncv_qsum (fun i : nat => q_pow X i / q_fact i) (Datatypes.S n')
            + (q_pow X (Datatypes.S n') / q_fact (Datatypes.S n'))%Q).
    rewrite IH.
    change (exp_tail_abs 0 (Datatypes.S n') X)
      with (exp_tail_abs 0 n' X
            + (if Nat.leb 0 n'
               then q_pow X (Datatypes.S n') / q_fact (Datatypes.S n')
               else 0)%Q).
    assert (H0b : Nat.leb 0 n' = true) by (apply Nat.leb_le; lia).
    rewrite H0b.
    ring.
Qed.

(* qsum split (front window + shifted window) *)
Lemma bxae_ncvsum_split_eq : forall (f : nat -> Q) (n1 d : nat),
  ncv_qsum f (Datatypes.S (n1 + d))%nat
  == (ncv_qsum f (Datatypes.S n1)
      + ncv_qsum (fun i : nat => f ((Datatypes.S n1 + i)%nat)) d)%Q.
Proof.
  intros f n1 d. induction d as [| d' IH].
  - rewrite Nat.add_0_r.
    change (ncv_qsum (fun i : nat => f ((Datatypes.S n1 + i)%nat)) 0%nat)
      with 0%Q.
    ring.
  - replace ((n1 + Datatypes.S d')%nat) with (Datatypes.S (n1 + d')) by lia.
    change (ncv_qsum f (Datatypes.S (Datatypes.S (n1 + d'))))
      with (ncv_qsum f (Datatypes.S (n1 + d'))
            + f (Datatypes.S (n1 + d')))%Q.
    rewrite IH.
    change (ncv_qsum (fun i : nat => f ((Datatypes.S n1 + i)%nat))
              (Datatypes.S d'))
      with (ncv_qsum (fun i : nat => f ((Datatypes.S n1 + i)%nat)) d'
            + f (Datatypes.S (n1 + d'))%Q).
    ring.
Qed.

(* pointwise control within the window (a range-restricted premise, used for the front window's pointwise bound) *)
Lemma bxae_ncvsum_le_ranged : forall (f g : nat -> Q) (n : nat),
  (forall k : nat, (k < n)%nat -> QleT' (f k) (g k)) ->
  QleT' (ncv_qsum f n) (ncv_qsum g n).
Proof.
  intros f g n Hle. induction n as [| m IH].
  - change (ncv_qsum f 0%nat) with 0%Q. change (ncv_qsum g 0%nat) with 0%Q.
    apply qleT'_refl.
  - change (ncv_qsum f (Datatypes.S m)) with (ncv_qsum f m + f m)%Q.
    change (ncv_qsum g (Datatypes.S m)) with (ncv_qsum g m + g m)%Q.
    apply (qleT'_plus_compat _ _ _ _).
    + apply IH. intros k Hk. apply Hle. lia.
    + apply Hle. lia.
Qed.

(* the shifted α window sum == the tail sum *)
Lemma bxae_ncvsum_alpha_shift : forall (X : Q) (m d : nat),
  ncv_qsum (fun i : nat => q_pow X (Datatypes.S m + i) / q_fact (Datatypes.S m + i)) d
  == exp_tail_abs m (m + d)%nat X.
Proof.
  intros X m d. induction d as [| d' IH].
  - rewrite Nat.add_0_r.
    change (ncv_qsum (fun i : nat => q_pow X (Datatypes.S m + i) / q_fact (Datatypes.S m + i)) 0%nat)
      with 0%Q.
    apply Qeq_sym. apply qeqT_imp_qeq. apply (exp_tail_abs_le_m m m X (Nat.le_refl _)).
  - replace ((m + Datatypes.S d')%nat) with (Datatypes.S (m + d'))%nat by lia.
    change (ncv_qsum (fun i : nat => q_pow X (Datatypes.S m + i) / q_fact (Datatypes.S m + i))
              (Datatypes.S d'))
      with (ncv_qsum (fun i : nat => q_pow X (Datatypes.S m + i) / q_fact (Datatypes.S m + i)) d'
            + (q_pow X (Datatypes.S m + d') / q_fact (Datatypes.S m + d'))%Q).
    change (exp_tail_abs m (Datatypes.S (m + d'))%nat X)
      with (exp_tail_abs m (m + d')%nat X
            + (if Nat.leb m (m + d')%nat
               then q_pow X (Datatypes.S (m + d'))%nat / q_fact (Datatypes.S (m + d'))%nat
               else 0)%Q).
    assert (Hleb : Nat.leb m (m + d')%nat = true)
      by (apply Nat.leb_le; lia).
    rewrite Hleb.
    replace ((Datatypes.S m + d')%nat) with (Datatypes.S (m + d'))%nat by lia.
    rewrite IH. ring.
Qed.

(* the main Q lemma: block sums arbitrarily small (Mertens-style window splitting) *)
Lemma bxae_qblock_small : forall (X Y eps : Q),
  Qle 0 X -> Qle 0 Y -> QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qlt (ncv_qsum (fun i : nat =>
           q_pow X i / q_fact i * exp_tail_abs (Nat.sub n i) n Y)
         (Datatypes.S n)) eps).
Proof.
  intros X Y eps HX HY He.
  (* the Y tail below the 1 threshold ⟹ a global β-sum bound Bb *)
  destruct (bxae_etab_small Y 1%Q HY bxae_qltT_0_1) as [Ny Hy].
  assert (Hb : forall n : nat,
           Qle (1 + exp_tail_abs 0 n Y)%Q ((1 + 1)%Q + exp_tail_abs 0 Ny Y)).
  { intro n. destruct (Nat.leb_spec n Ny) as [Hle | Hgt].
    - assert (Hsp : exp_tail_abs 0 Ny Y
                    == (exp_tail_abs 0 n Y + exp_tail_abs n Ny Y)%Q)
        by (apply bxae_etab_split with (m2 := n); lia).
      rewrite Hsp.
      apply (Qplus_le_compat 1%Q (1 + 1)%Q
               (exp_tail_abs 0 n Y)
               (exp_tail_abs 0 n Y + exp_tail_abs n Ny Y)).
      + exact bxae_Qle_1_2.
      + apply bxae_Qle_add_r.
        exact (bxae_etab_nonneg Y n Ny HY).
    - assert (Hsp : exp_tail_abs 0 n Y
                    == (exp_tail_abs 0 Ny Y + exp_tail_abs Ny n Y)%Q)
        by (apply bxae_etab_split with (m2 := Ny); lia).
      rewrite Hsp.
      assert (E1a : (1 + (exp_tail_abs 0 Ny Y + exp_tail_abs Ny n Y))%Q
                    == ((1 + exp_tail_abs Ny n Y) + exp_tail_abs 0 Ny Y)%Q) by ring.
      apply (Qle_trans _ ((1 + exp_tail_abs Ny n Y) + exp_tail_abs 0 Ny Y)%Q).
      + exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ E1a))).
      + apply (Qplus_le_compat (1 + exp_tail_abs Ny n Y)%Q (1 + 1)%Q
                 (exp_tail_abs 0 Ny Y) (exp_tail_abs 0 Ny Y)).
        * apply (Qplus_le_compat 1%Q 1%Q (exp_tail_abs Ny n Y) 1%Q).
          -- apply Qle_refl.
          -- apply Qlt_le_weak. exact (Hy Ny n (Nat.le_refl Ny)).
        * apply Qle_refl. }
  (* the global β bound Bb with its positivity/cancellation identities (used in the HP2 scaling chain) *)
  set (Bb := ((1 + 1)%Q + exp_tail_abs 0 Ny Y)%Q).
  assert (HBb : Qlt 0 Bb).
  { unfold Bb.
    setoid_rewrite (Qplus_comm (1 + 1)%Q (exp_tail_abs 0 Ny Y)).
    apply (Qle_lt_trans 0%Q (exp_tail_abs 0 Ny Y + 0)%Q
             (exp_tail_abs 0 Ny Y + (1 + 1)%Q)).
    - rewrite Qplus_0_r. exact (bxae_etab_nonneg Y 0 Ny HY).
    - apply (proj2 (Qplus_lt_r 0%Q (1 + 1)%Q (exp_tail_abs 0 Ny Y))).
      exact bxae_qlt_0_2. }
  assert (HtwoBb : QltT 0 ((1 + 1) * Bb)%Q)
    by (apply (ncv_qmult_lt0 (1 + 1) Bb); [exact bxae_qlt_0_2 | exact HBb]).
  assert (HcanBb : ((eps * / ((1 + 1) * Bb)) * Bb == eps * / (1 + 1))%Q).
  { apply bxae_cancel_mul.
    - apply bxae_1p1_neq_0.
    - intros Hz.
      exact (match q_neq_of_lt ((1 + 1) * Bb)%Q HtwoBb
               (qeq_imp_qeqT _ _ Hz) with end). }
  (* the X-side window threshold (the eps·/(2·Bb) scaled quantity) *)
  assert (HltE : Qlt 0 (eps * / (1 + 1))%Q).
  { apply QltT_to_Qlt. apply (ncv_qmult_lt0 eps (Qinv (1 + 1))).
    - exact (QltT_to_Qlt 0 eps He).
    - apply Qinv_lt_0_compat. exact bxae_qlt_0_2. }
  destruct (bxae_etab_small X (eps * / ((1 + 1) * Bb))%Q HX
              (ncv_qmult_lt0 eps (Qinv ((1 + 1) * Bb))
                 (QltT_to_Qlt 0 eps He)
                 (Qinv_lt_0_compat _ (QltT_to_Qlt _ _ HtwoBb)))) as [Na Ha].
  set (SN := (1 + exp_tail_abs 0 Na X)%Q).
  assert (HposSN : Qlt 0 SN).
  { unfold SN. apply (Qlt_le_trans 0%Q 1%Q SN).
    - exact bxae_qlt_0_1.
    - apply bxae_Qle_add_r. exact (bxae_etab_nonneg X 0 Na HX). }
  assert (HtwoSN : QltT 0 ((1 + 1) * SN)%Q)
    by (apply (ncv_qmult_lt0 (1 + 1) SN); [exact bxae_qlt_0_2 | exact HposSN]).
  destruct (bxae_etab_small Y (eps * / ((1 + 1) * SN))%Q HY
              (ncv_qmult_lt0 eps (Qinv ((1 + 1) * SN))
                 (QltT_to_Qlt 0 eps He)
                 (Qinv_lt_0_compat _ (QltT_to_Qlt _ _ HtwoSN)))) as [Ny1 Hy1].
  exists (Na + Ny1)%nat. intros n Hn.
  assert (Hnd : n = (Na + (n - Na))%nat) by lia.
  set (d := (n - Na)%nat).
  assert (HcanSN : ((eps * / ((1 + 1) * SN)) * SN == eps * / (1 + 1))%Q).
  { apply bxae_cancel_mul.
    - apply bxae_1p1_neq_0.
    - intros Hz.
      exact (match q_neq_of_lt ((1 + 1) * SN)%Q HtwoSN
               (qeq_imp_qeqT _ _ Hz) with end). }
  (* window split *)
  set (F := fun i : nat =>
              (q_pow X i / q_fact i) * exp_tail_abs (Nat.sub n i) n Y).
  replace (ncv_qsum F (Datatypes.S n)) with (ncv_qsum F (Datatypes.S (Na + d)))%nat
    by (f_equal; lia).
  rewrite bxae_ncvsum_split_eq.
  (* front window: i ≤ Na *)
  assert (HP1 : Qlt (ncv_qsum F (Datatypes.S Na)) (eps * / (1 + 1))%Q).
  { assert (Hlt1 : Qlt (exp_tail_abs (Nat.sub n Na) n Y * SN)
                       ((eps * / ((1 + 1) * SN)) * SN)%Q).
    { apply (bxae_mult_lt_r (exp_tail_abs (Nat.sub n Na) n Y)
        (eps * / ((1 + 1) * SN)) SN).
      - apply (Hy1 (Nat.sub n Na) n). lia.
      - exact HposSN. }
    rewrite HcanSN in Hlt1.
    assert (Hpt : forall i : nat, (i <= Na)%nat ->
              QleT' (F i) (exp_tail_abs (Nat.sub n Na) n Y
                           * (q_pow X i / q_fact i))%Q).
    { intros i Hi. unfold F. apply Qle_to_QleT'.
      apply (Qle_trans _
               (exp_tail_abs (Nat.sub n i) n Y
                * (q_pow X i / q_fact i))%Q).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      - apply (Qmult_le_compat_r _ _ (q_pow X i / q_fact i)).
        + apply (bxae_etab_mono_start Y (Nat.sub n Na) (Nat.sub n i) n HY).
          lia.
        + apply (bxae_term_nonneg X i HX). }
    assert (Hle1 : QleT' (ncv_qsum F (Datatypes.S Na))
                   (ncv_qsum (fun i : nat =>
                      exp_tail_abs (Nat.sub n Na) n Y * (q_pow X i / q_fact i))
                      (Datatypes.S Na)))
      by (apply bxae_ncvsum_le_ranged; intros k Hk; apply Hpt; lia).
    assert (Hsc : ncv_qsum (fun i : nat =>
                 exp_tail_abs (Nat.sub n Na) n Y * (q_pow X i / q_fact i))
                 (Datatypes.S Na)
                 == (exp_tail_abs (Nat.sub n Na) n Y
                     * ncv_qsum (fun i : nat => q_pow X i / q_fact i)
                       (Datatypes.S Na))%Q)
      by (apply qeqT_imp_qeq; apply ncv_qsum_scalar_l).
    apply (Qle_lt_trans _ (exp_tail_abs (Nat.sub n Na) n Y * SN)%Q).
    - apply (Qle_trans _ (ncv_qsum (fun i : nat =>
                 exp_tail_abs (Nat.sub n Na) n Y * (q_pow X i / q_fact i))
                 (Datatypes.S Na))%Q).
      + exact (QleT'_to_Qle _ _ Hle1).
      + apply (Qle_trans _ (exp_tail_abs (Nat.sub n Na) n Y
                 * ncv_qsum (fun i : nat => q_pow X i / q_fact i)
                   (Datatypes.S Na))%Q).
        * exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Hsc))).
        * rewrite (Qmult_comm (exp_tail_abs (Nat.sub n Na) n Y)
                    (ncv_qsum (fun i : nat => q_pow X i / q_fact i)
                       (Datatypes.S Na))).
          rewrite (Qmult_comm (exp_tail_abs (Nat.sub n Na) n Y) SN).
          apply (Qmult_le_compat_r _ _ (exp_tail_abs (Nat.sub n Na) n Y)).
          -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. unfold SN. exact (bxae_ncvsum_alpha X Na).
          -- exact (bxae_etab_nonneg Y (Nat.sub n Na) n HY).
    - exact Hlt1. }
  (* rear window: i > Na (the shifted window) *)
  assert (HP2 : Qlt (ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)
                    (eps * / (1 + 1))%Q).
  { assert (Hpt : forall i : nat,
              QleT' (F ((Datatypes.S Na + i)%nat))
                (((1 + 1)%Q + exp_tail_abs 0 Ny Y)
                 * (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat)))%Q).
    { intros i. unfold F. apply Qle_to_QleT'.
      apply (Qle_trans _
               ((q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))
                * ((1 + 1)%Q + exp_tail_abs 0 Ny Y))%Q).
      - rewrite (Qmult_comm (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))
                  (exp_tail_abs (Nat.sub n ((Datatypes.S Na + i)%nat)) n Y)).
        rewrite (Qmult_comm (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))
                  ((1 + 1)%Q + exp_tail_abs 0 Ny Y)).
        apply (Qmult_le_compat_r _ _
                 (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))).
        + (* tail(n−j, n) ≤ 1 + tail(0, n) ≤ Bb *)
          apply (Qle_trans _ (1 + exp_tail_abs 0 n Y)%Q).
          * assert (Hsp2 : exp_tail_abs 0 n Y
                           == (exp_tail_abs 0 (Nat.sub n ((Datatypes.S Na + i)%nat)) Y
                               + exp_tail_abs (Nat.sub n ((Datatypes.S Na + i)%nat)) n Y)%Q)
              by (apply bxae_etab_split with (m2 := Nat.sub n ((Datatypes.S Na + i)%nat)); lia).
            assert (Ht1 : exp_tail_abs (Nat.sub n ((Datatypes.S Na + i)%nat)) n Y
                          <= exp_tail_abs 0 n Y).
            { apply (Qle_trans _
                       (exp_tail_abs 0 (Nat.sub n ((Datatypes.S Na + i)%nat)) Y
                        + exp_tail_abs (Nat.sub n ((Datatypes.S Na + i)%nat)) n Y)%Q).
              - apply bxae_Qle_add_l.
                exact (bxae_etab_nonneg Y 0%nat (Nat.sub n ((Datatypes.S Na + i)%nat)) HY).
              - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. symmetry. exact Hsp2. }
            apply (Qle_trans _ (exp_tail_abs 0 n Y)).
            -- exact Ht1.
            -- apply bxae_Qle_add_l. apply QleT'_to_Qle. apply Qle_0_1.
          * apply Hb.
        + apply (bxae_term_nonneg X ((Datatypes.S Na + i)%nat) HX).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply Qmult_comm. }
    assert (Hle2 : QleT' (ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)
                   (ncv_qsum (fun i : nat =>
                      ((1 + 1)%Q + exp_tail_abs 0 Ny Y)
                      * (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))) d))
      by (apply ncv_qsum_le; exact Hpt).
    assert (Hsc : ncv_qsum (fun i : nat =>
                 ((1 + 1)%Q + exp_tail_abs 0 Ny Y)
                 * (q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat))) d
                 == (((1 + 1)%Q + exp_tail_abs 0 Ny Y)
                     * ncv_qsum (fun i : nat =>
                          q_pow X ((Datatypes.S Na + i)%nat) / q_fact ((Datatypes.S Na + i)%nat)) d)%Q)
      by (apply qeqT_imp_qeq; apply ncv_qsum_scalar_l).
    pose proof Hle2 as Hle3.
    apply QleT'_to_Qle in Hle3.
    rewrite Hsc in Hle3.
    rewrite (bxae_ncvsum_alpha_shift X Na d) in Hle3.
    replace (Na + d)%nat with n in Hle3 by lia.
    assert (Hlt2 : Qlt (exp_tail_abs Na n X * Bb)
                       ((eps * / ((1 + 1) * Bb)) * Bb)%Q).
    { apply (bxae_mult_lt_r (exp_tail_abs Na n X)
              (eps * / ((1 + 1) * Bb)) Bb).
      - exact (Ha Na n (Nat.le_refl Na)).
      - exact HBb. }
    setoid_rewrite HcanBb in Hlt2.
    setoid_rewrite (Qmult_comm (exp_tail_abs Na n X) Bb) in Hlt2.
    apply (Qle_lt_trans _ (Bb * exp_tail_abs Na n X)%Q).
    - exact Hle3.
    - exact Hlt2. }
  (* confluence: P1 < e/2 and P2 < e/2 ⟹ P1 + P2 < e *)
  apply (Qle_lt_trans _
           (eps * / (1 + 1) + ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)%Q).
  - apply (Qplus_le_compat _ _ _ _).
    + apply Qlt_le_weak. exact HP1.
    + apply Qle_refl.
  - apply (Qlt_le_trans
             (eps * / (1 + 1)
              + ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)
             (eps * / (1 + 1) + eps * / (1 + 1))%Q eps).
    + apply (proj2 (Qplus_lt_r (ncv_qsum (fun i : nat => F ((Datatypes.S Na + i)%nat)) d)
                       (eps * / (1 + 1)) (eps * / (1 + 1)))).
      exact HP2.
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. apply bxae_half_add.
Qed.

(* S2: the Banach layer (row-shaped triangle + block decomposition + norm bounds + limit shift + the main lemma) *)

(* QleT' double monotonicity of multiplication (with 0 ≤ x2 and 0 ≤ y1 as explicit premises, covering the missing stdlib compat_l) *)
Lemma bxae_qleT'_mul_le : forall x1 y1 x2 y2 : Q,
  Qle x1 y1 -> Qle x2 y2 -> Qle 0 x2 -> Qle 0 y1 -> QleT' (x1 * x2) (y1 * y2)%Q.
Proof.
  intros x1 y1 x2 y2 H1 H2 H3a H3b.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (y1 * x2)%Q).
  - apply (Qmult_le_compat_r x1 y1 x2); assumption.
  - rewrite (Qmult_comm y1 x2). rewrite (Qmult_comm y1 y2).
    apply (Qmult_le_compat_r x2 y2 y1); assumption.
Qed.

(* a same-shape bridge between bsum and ncv_sum *)
Lemma bxae_bsum_ncvsum : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (x : nat -> BA) (n : nat),
  bae (bsum _ _ B n x) (ncv_sum _ _ B x n).
Proof.
  intros BA bae B x n. induction n as [| m IH].
  - apply (@bae_refl _ _ B).
  - change (bsum _ _ B (Datatypes.S m) x)
      with (@bplus _ _ B (bsum _ _ B m x) (x m)).
    change (ncv_sum _ _ B x (Datatypes.S m))
      with (@bplus _ _ B (ncv_sum _ _ B x m) (x m)).
    apply (@bplus_wd _ _ B).
    + exact IH.
    + apply (@bae_refl _ _ B).
Qed.

(* the zeroth-power term is the unit: bpow x 0·(1/0!) == bone *)
Lemma bxae_B0_one : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x : BA),
  bae (@bmult _ _ B (bpow _ _ B x 0%nat) (@bcoef _ _ B (/ q_fact 0%nat))) (@bone _ _ B).
Proof.
  intros BA bae B x.
  assert (Hq0 : (/ q_fact 0%nat)%Q = 1%Q) by reflexivity.
  rewrite Hq0.
  change (bpow _ _ B x 0%nat) with (@bone _ _ B).
  eapply bae_trans with (b := @bcoef _ _ B 1%Q).
  - exact (@bmult_one_l _ _ B (@bcoef _ _ B 1%Q)).
  - exact (@bcoef_one _ _ B).
Qed.

(* term reassociation: coef c·(a^j·b^i) == (a^j·coef x)·(b^i·coef y) (c == x·y) *)
Lemma bxae_term_reassoc : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
                                 (a b : BA) (j i : nat) (x y c : Q),
  c == (x * y)%Q ->
  bae (@bmult _ _ B (@bcoef _ _ B c) (@bmult _ _ B (bpow _ _ B a j) (bpow _ _ B b i)))
       (@bmult _ _ B (@bmult _ _ B (bpow _ _ B a j) (@bcoef _ _ B x))
                   (@bmult _ _ B (bpow _ _ B b i) (@bcoef _ _ B y))).
Proof.
  intros BA bae B a b j i x y c Hc.
  assert (Hswap : bae (@bmult _ _ B (@bmult _ _ B (bpow _ _ B b i) (@bcoef _ _ B x))
                                    (@bcoef _ _ B y))
                         (@bmult _ _ B (@bcoef _ _ B x)
                                   (@bmult _ _ B (bpow _ _ B b i) (@bcoef _ _ B y)))).
  { eapply bae_trans with
      (b := @bmult _ _ B (@bmult _ _ B (@bcoef _ _ B x) (bpow _ _ B b i)) (@bcoef _ _ B y)).
    - apply (@bmult_wd _ _ B).
      + exact (@bcoef_comm _ _ B x (bpow _ _ B b i)).
      + apply (@bae_refl _ _ B).
    - apply (@bae_sym _ _ B).
      exact (@bmult_assoc _ _ B (@bcoef _ _ B x) (bpow _ _ B b i) (@bcoef _ _ B y)). }
  eapply bae_trans with
    (b := @bmult _ _ B (@bmult _ _ B (bpow _ _ B a j) (bpow _ _ B b i))
                    (@bcoef _ _ B (x * y)%Q)).
  - eapply bae_trans with
      (b := @bmult _ _ B (@bmult _ _ B (bpow _ _ B a j) (bpow _ _ B b i)) (@bcoef _ _ B c)).
    + apply (@bae_sym _ _ B).
      exact (@bcoef_comm _ _ B c (@bmult _ _ B (bpow _ _ B a j) (bpow _ _ B b i))).
    + apply (@bmult_wd _ _ B).
      * apply (@bae_refl _ _ B).
        * apply (@bcoef_wd _ _ B). apply qeq_imp_qeqT. exact Hc.
  - eapply bae_trans with
      (b := @bmult _ _ B (bpow _ _ B a j)
                      (@bmult _ _ B (bpow _ _ B b i) (@bcoef _ _ B (x * y)%Q))).
    + apply (@bae_sym _ _ B).
      exact (@bmult_assoc _ _ B (bpow _ _ B a j) (bpow _ _ B b i)
                             (@bcoef _ _ B (x * y)%Q)).
    + eapply bae_trans with
        (b := @bmult _ _ B (bpow _ _ B a j)
                        (@bmult _ _ B (bpow _ _ B b i)
                                 (@bmult _ _ B (@bcoef _ _ B x) (@bcoef _ _ B y)))).
      * apply (@bmult_wd _ _ B).
        -- apply (@bae_refl _ _ B).
        -- apply (@bmult_wd _ _ B).
           ++ apply (@bae_refl _ _ B).
           ++ exact (@bcoef_mult _ _ B x y).
      * eapply bae_trans with
          (b := @bmult _ _ B (bpow _ _ B a j)
                          (@bmult _ _ B (@bmult _ _ B (bpow _ _ B b i) (@bcoef _ _ B x))
                                    (@bcoef _ _ B y))).
        -- apply (@bmult_wd _ _ B).
           ++ apply (@bae_refl _ _ B).
           ++ exact (@bmult_assoc _ _ B (bpow _ _ B b i) (@bcoef _ _ B x)
                                  (@bcoef _ _ B y)).
        -- eapply bae_trans with
             (b := @bmult _ _ B (bpow _ _ B a j)
                             (@bmult _ _ B (@bcoef _ _ B x)
                                       (@bmult _ _ B (bpow _ _ B b i)
                                                  (@bcoef _ _ B y)))).
           ++ apply (@bmult_wd _ _ B).
              ** apply (@bae_refl _ _ B).
              ** exact Hswap.
           ++ exact (@bmult_assoc _ _ B (bpow _ _ B a j) (@bcoef _ _ B x)
                                  (@bmult _ _ B (bpow _ _ B b i) (@bcoef _ _ B y))).
Qed.
(* (1)+(3) junction: (a+b)^k/k! == Σ_{j≤k} A j·B (k−j) (row shape; the CBR bridge supplies the coefficients) *)
Lemma bxae_binom_row : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall k : nat,
    bae (@bmult _ _ B (bpow _ _ B (@bplus _ _ B a b) k) (@bcoef _ _ B (/ q_fact k)))
           (bsum _ _ B (Datatypes.S k)
              (fun j : nat =>
                 @bmult _ _ B (@bmult _ _ B (bpow _ _ B a j) (@bcoef _ _ B (/ q_fact j)))
                          (@bmult _ _ B (bpow _ _ B b (Nat.sub k j))
                                   (@bcoef _ _ B (/ q_fact (Nat.sub k j)))))).
Proof.
  intros BA bae B a b hab k.
  eapply bae_trans.
  - exact (bnh_esp_term_binom _ _ B a b hab k).
  - apply (bsum_ext _ _ B (Datatypes.S k)
             (fun j : nat =>
                @bmult _ _ B (@bcoef _ _ B (bpa_binom k j * / q_fact k)%Q)
                         (@bmult _ _ B (bpow _ _ B a j)
                                  (bpow _ _ B b (Nat.sub k j))))
             (fun j : nat =>
                @bmult _ _ B (@bmult _ _ B (bpow _ _ B a j) (@bcoef _ _ B (/ q_fact j)))
                         (@bmult _ _ B (bpow _ _ B b (Nat.sub k j))
                                  (@bcoef _ _ B (/ q_fact (Nat.sub k j)))))).
    intros j Hj.
    apply (bxae_term_reassoc _ _ B a b j (Nat.sub k j)
               (/ q_fact j) (/ q_fact (Nat.sub k j))
               (bpa_binom k j * / q_fact k)%Q).
    + exact (bxcb_term_split_binom k j ltac:(lia)).
Qed.

(* (2) the square row shape: esp a n·esp b n == Σ_{i≤n} A i·esp b n *)
Lemma bxae_prod_row : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA) (n : nat),
  bae (@bmult _ _ B (exp_series_partial _ _ B a n) (exp_series_partial _ _ B b n))
         (bsum _ _ B (Datatypes.S n)
            (fun i : nat =>
               @bmult _ _ B (@bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))
                        (exp_series_partial _ _ B b n))).
Proof.
  intros BA bae B a b n.
  eapply bae_trans.
  - apply (@bmult_wd _ _ B).
    + exact (esp_as_bsum _ _ B a n).
    + apply (@bae_refl _ _ B).
  - apply (@bae_sym _ _ B).
    exact (bpa_bsum_mult_r _ _ B (Datatypes.S n) (exp_series_partial _ _ B b n)
             (fun i : nat =>
                @bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))).
Qed.

(* (4) the row-shaped triangle (own induction, avoiding the bd2 transpose):
   esp (a+b) n == Σ_{i≤n} A i·esp b (n−i) *)
Lemma bxae_tri_row : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall n : nat,
    bae (exp_series_partial _ _ B (@bplus _ _ B a b) n)
           (bsum _ _ B (Datatypes.S n)
              (fun i : nat =>
                 @bmult _ _ B (@bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))
                          (exp_series_partial _ _ B b (Nat.sub n i)))).
Proof.
  intros BA bae B a b hab n.
  induction n as [| n' IH].
  - (* base case: bone == bzero + A 0·esp b 0 *)
    assert (Hq0 : (/ q_fact 0%nat)%Q = 1%Q) by reflexivity.
    change (exp_series_partial _ _ B (@bplus _ _ B a b) 0%nat) with (@bone _ _ B).
    change (bsum _ _ B (Datatypes.S 0%nat)
              (fun i : nat =>
                 @bmult _ _ B (@bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))
                          (exp_series_partial _ _ B b (Nat.sub 0 i))))
      with (@bplus _ _ B (@bzero _ _ B)
              (@bmult _ _ B (@bmult _ _ B (bpow _ _ B a 0%nat) (@bcoef _ _ B (/ q_fact 0%nat)))
                       (exp_series_partial _ _ B b (Nat.sub 0 0)))).
    rewrite Hq0.
    change (bpow _ _ B a 0%nat) with (@bone _ _ B).
    change (exp_series_partial _ _ B b (Nat.sub 0 0)) with (@bone _ _ B).
    eapply bae_trans with
      (b := @bmult _ _ B (@bmult _ _ B (@bone _ _ B) (@bcoef _ _ B 1%Q)) (@bone _ _ B)).
    + eapply bae_trans with (b := @bmult _ _ B (@bcoef _ _ B 1%Q) (@bone _ _ B)).
      * eapply bae_trans with (b := @bcoef _ _ B 1%Q).
        -- apply (@bae_sym _ _ B). exact (@bcoef_one _ _ B).
        -- apply (@bae_sym _ _ B). exact (@bmult_one_r _ _ B (@bcoef _ _ B 1%Q)).
      * apply (@bmult_wd _ _ B).
        -- apply (@bae_sym _ _ B). exact (@bmult_one_l _ _ B (@bcoef _ _ B 1%Q)).
        -- apply (@bae_refl _ _ B).
    + apply (@bae_sym _ _ B).
      exact (@bplus_zero_l _ _ B (@bmult _ _ B (@bmult _ _ B (@bone _ _ B) (@bcoef _ _ B 1%Q)) (@bone _ _ B))).
  - (* inductive step: set-names the short-term structure *)
    assert (Esub : Nat.sub (Datatypes.S n') (Datatypes.S n') = 0%nat) by lia.
    set (Ai := fun i : nat => @bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i))).
    set (Bj := fun j : nat => @bmult _ _ B (bpow _ _ B b j) (@bcoef _ _ B (/ q_fact j))).
    set (Hrow := fun i : nat =>
                   @bmult _ _ B (Ai i) (exp_series_partial _ _ B b (Nat.sub n' i))).
    set (Fj := fun j : nat =>
                 @bmult _ _ B (Ai j) (Bj (Nat.sub (Datatypes.S n') j))).
    set (Tl := @bmult _ _ B (Ai (Datatypes.S n')) (Bj 0%nat)).
    set (R := fun i : nat =>
                @bmult _ _ B (Ai i)
                    (exp_series_partial _ _ B b (Nat.sub (Datatypes.S n') i))).
    (* leading change on the LHS: esp(S n') == esp n' + C; on the RHS, peel the last term of the bsum *)
    change (exp_series_partial _ _ B (@bplus _ _ B a b) (Datatypes.S n'))
      with (@bplus _ _ B (exp_series_partial _ _ B (@bplus _ _ B a b) n')
                (@bmult _ _ B (bpow _ _ B (@bplus _ _ B a b) (Datatypes.S n'))
                          (@bcoef _ _ B (/ q_fact (Datatypes.S n'))))).
    change (bsum _ _ B (Datatypes.S (Datatypes.S n')) R)
      with (@bplus _ _ B (bsum _ _ B (Datatypes.S n') R) (R (Datatypes.S n'))).
    (* R (S n') ≡ Tl (B0 ↔ esp b 0) *)
    assert (HRtl : bae Tl (R (Datatypes.S n'))).
    { unfold Tl, R, Ai, Bj. rewrite Esub.
      change (exp_series_partial _ _ B b 0%nat) with (@bone _ _ B).
      apply (@bmult_wd _ _ B); [apply (@bae_refl _ _ B) | exact (bxae_B0_one _ _ B b)]. }
    (* the C row shape *)
    assert (HC : bae (@bmult _ _ B (bpow _ _ B (@bplus _ _ B a b) (Datatypes.S n'))
                                  (@bcoef _ _ B (/ q_fact (Datatypes.S n'))))
                         (bsum _ _ B (Datatypes.S (Datatypes.S n')) Fj)).
    { unfold Fj. exact (bxae_binom_row _ _ B a b hab (Datatypes.S n')). }
    (* peel the last term: bsum (S (S n')) Fj == bsum (S n') Fj + Tl *)
    assert (Hpeel : bae (bsum _ _ B (Datatypes.S (Datatypes.S n')) Fj)
                           (@bplus _ _ B (bsum _ _ B (Datatypes.S n') Fj) Tl)).
    { unfold Fj, Tl, Ai, Bj.
      change (bsum _ _ B (Datatypes.S (Datatypes.S n'))
                (fun j : nat =>
                   @bmult _ _ B (@bmult _ _ B (bpow _ _ B a j) (@bcoef _ _ B (/ q_fact j)))
                            (@bmult _ _ B (bpow _ _ B b (Nat.sub (Datatypes.S n') j))
                                     (@bcoef _ _ B (/ q_fact (Nat.sub (Datatypes.S n') j))))))
        with (@bplus _ _ B (bsum _ _ B (Datatypes.S n')
                          (fun j : nat =>
                             @bmult _ _ B (@bmult _ _ B (bpow _ _ B a j)
                                                  (@bcoef _ _ B (/ q_fact j)))
                                      (@bmult _ _ B (bpow _ _ B b
                                                   (Nat.sub (Datatypes.S n') j))
                                               (@bcoef _ _ B
                                                  (/ q_fact (Nat.sub (Datatypes.S n') j))))))
                  (@bmult _ _ B (@bmult _ _ B (bpow _ _ B a (Datatypes.S n'))
                                      (@bcoef _ _ B (/ q_fact (Datatypes.S n'))))
                           (@bmult _ _ B (bpow _ _ B b
                                        (Nat.sub (Datatypes.S n') (Datatypes.S n')))
                                    (@bcoef _ _ B
                                       (/ q_fact (Nat.sub (Datatypes.S n') (Datatypes.S n'))))))).
      rewrite Esub. apply (@bae_refl _ _ B). }
    (* per-term merge: Hrow i + Fj i == R i (for i < S n') *)
    assert (HR : forall i : nat, (i < Datatypes.S n')%nat ->
                   bae (@bplus _ _ B (Hrow i) (Fj i)) (R i)).
    { intros i Hi. unfold Hrow, Fj, R, Ai, Bj.
      assert (E2 : Nat.sub (Datatypes.S n') i
                   = Datatypes.S (Nat.sub n' i)) by lia.
      rewrite E2.
      change (exp_series_partial _ _ B b (Datatypes.S (Nat.sub n' i)))
        with (@bplus _ _ B (exp_series_partial _ _ B b (Nat.sub n' i))
                  (@bmult _ _ B (bpow _ _ B b (Datatypes.S (Nat.sub n' i)))
                           (@bcoef _ _ B (/ q_fact (Datatypes.S (Nat.sub n' i)))))).
      apply (@bae_sym _ _ B). apply (@bdistrib_l _ _ B). }
    (* the total chain (the EXPADD5 rearrangement): esp+C -> esp+ΣFj -> esp+(ΣFj'+Tl) -> reassociate
       -> (ΣHrow+ΣFj)+Tl -> +R(S n') -> Σ(Hrow+Fj)+R(S n') -> the goal *)
    eapply bae_trans with
      (b := @bplus _ _ B (exp_series_partial _ _ B (@bplus _ _ B a b) n')
                      (bsum _ _ B (Datatypes.S (Datatypes.S n')) Fj)).
    { apply (@bplus_wd_r _ _ B). exact HC. }
    eapply bae_trans with
      (b := @bplus _ _ B (exp_series_partial _ _ B (@bplus _ _ B a b) n')
                      (@bplus _ _ B (bsum _ _ B (Datatypes.S n') Fj) Tl)).
    { apply (@bplus_wd_r _ _ B). exact Hpeel. }
    eapply bae_trans with
      (b := @bplus _ _ B (@bplus _ _ B (exp_series_partial _ _ B (@bplus _ _ B a b) n')
                            (bsum _ _ B (Datatypes.S n') Fj)) Tl).
    { apply (@bplus_assoc _ _ B). }
    eapply bae_trans with
      (b := @bplus _ _ B (@bplus _ _ B (bsum _ _ B (Datatypes.S n') Hrow)
                            (bsum _ _ B (Datatypes.S n') Fj)) Tl).
    { apply (@bplus_wd_l _ _ B). apply (@bplus_wd_l _ _ B). exact IH. }
    eapply bae_trans with
      (b := @bplus _ _ B (@bplus _ _ B (bsum _ _ B (Datatypes.S n') Hrow)
                            (bsum _ _ B (Datatypes.S n') Fj)) (R (Datatypes.S n'))).
    { apply (@bplus_wd_r _ _ B). exact HRtl. }
    apply (@bplus_wd_l _ _ B).
    eapply bae_trans with
      (b := bsum _ _ B (Datatypes.S n') (fun i : nat => @bplus _ _ B (Hrow i) (Fj i))).
    { apply (@bae_sym _ _ B). exact (bsum_plus _ _ B (Datatypes.S n') Hrow Fj). }
    { apply (bsum_ext _ _ B (Datatypes.S n')
                (fun i : nat => @bplus _ _ B (Hrow i) (Fj i)) R).
      intros i Hi. exact (HR i Hi). }
Qed.
(* difference = block sum: esp a n·esp b n − esp (a+b) n == Σ_{i≤n} A i·(esp b n − esp b (n−i)) *)
Lemma bxae_diff_block : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall (n : nat),
  bae (@bplus _ _ B (@bmult _ _ B (exp_series_partial _ _ B a n)
                             (exp_series_partial _ _ B b n))
                   (@bopp _ _ B (exp_series_partial _ _ B (@bplus _ _ B a b) n)))
         (bsum _ _ B (Datatypes.S n)
            (fun i : nat =>
               @bmult _ _ B (@bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))
                        (@bplus _ _ B (exp_series_partial _ _ B b n)
                                 (@bopp _ _ B (exp_series_partial _ _ B b
                                              (Nat.sub n i)))))).
Proof.
  intros BA bae B a b hab n.
  set (Ai := fun i : nat => @bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i))).
  set (Hrow := fun i : nat =>
                 @bmult _ _ B (Ai i) (exp_series_partial _ _ B b (Nat.sub n i))).
  set (Kf := fun i : nat =>
               @bmult _ _ B (Ai i)
                        (@bplus _ _ B (exp_series_partial _ _ B b n)
                                 (@bopp _ _ B (exp_series_partial _ _ B b
                                            (Nat.sub n i))))).
  (* per term: A i·esp b n == Hrow i + Kf i *)
  assert (Hpt : forall i : nat,
             bae (@bmult _ _ B (Ai i) (exp_series_partial _ _ B b n))
                    (@bplus _ _ B (Hrow i) (Kf i))).
  { intros i. unfold Hrow, Kf.
    (* A·u == A·(v+(u+−v)) == A·v + A·(u+−v) (distributing the inserted identity u == v+(u+−v), then group-law cancellation) *)
    eapply bae_trans with
      (b := @bmult _ _ B (Ai i)
                      (@bplus _ _ B (exp_series_partial _ _ B b (Nat.sub n i))
                               (@bplus _ _ B (exp_series_partial _ _ B b n)
                                        (@bopp _ _ B (exp_series_partial _ _ B b
                                                   (Nat.sub n i)))))).
    - apply (@bmult_wd _ _ B).
      + apply (@bae_refl _ _ B).
      + apply (@bae_sym _ _ B).
        eapply bae_trans with
          (b := @bplus _ _ B (@bplus _ _ B (exp_series_partial _ _ B b (Nat.sub n i))
                                  (exp_series_partial _ _ B b n))
                         (@bopp _ _ B (exp_series_partial _ _ B b
                                    (Nat.sub n i)))).
        * apply (@bplus_assoc _ _ B).
        * eapply bae_trans with
            (b := @bplus _ _ B (@bplus _ _ B (exp_series_partial _ _ B b n)
                                    (exp_series_partial _ _ B b (Nat.sub n i)))
                           (@bopp _ _ B (exp_series_partial _ _ B b
                                      (Nat.sub n i)))).
          -- apply (@bplus_wd_l _ _ B). apply (@bplus_comm _ _ B).
          -- eapply bae_trans with
               (b := @bplus _ _ B (exp_series_partial _ _ B b n)
                              (@bplus _ _ B (exp_series_partial _ _ B b (Nat.sub n i))
                                       (@bopp _ _ B (exp_series_partial _ _ B b
                                                  (Nat.sub n i))))).
             ++ apply (@bae_sym _ _ B). apply (@bplus_assoc _ _ B).
             ++ eapply bae_trans with
                  (b := @bplus _ _ B (exp_series_partial _ _ B b n) (@bzero _ _ B)).
                ** apply (@bplus_wd_r _ _ B).
                   exact (@bplus_opp _ _ B (exp_series_partial _ _ B b (Nat.sub n i))).
                ** apply (@bplus_zero _ _ B (exp_series_partial _ _ B b n)).
    - apply (@bdistrib_l _ _ B). }
  assert (H1 : bae (@bplus _ _ B (@bmult _ _ B (exp_series_partial _ _ B a n)
                                         (exp_series_partial _ _ B b n))
                              (@bopp _ _ B (exp_series_partial _ _ B
                                          (@bplus _ _ B a b) n)))
                     (@bplus _ _ B (bsum _ _ B (Datatypes.S n)
                                  (fun i : nat =>
                                     @bmult _ _ B (Ai i)
                                         (exp_series_partial _ _ B b n)))
                              (@bopp _ _ B (bsum _ _ B (Datatypes.S n) Hrow)))).
  { apply (@bplus_wd _ _ B).
    - exact (bxae_prod_row _ _ B a b n).
    - apply (@bopp_wd _ _ B).
      destruct n as [| n'].
      + exact (bxae_tri_row _ _ B a b hab 0%nat).
      + exact (bxae_tri_row _ _ B a b hab (Datatypes.S n')). }
  assert (H2 : bae (bsum _ _ B (Datatypes.S n)
                         (fun i : nat =>
                            @bmult _ _ B (Ai i) (exp_series_partial _ _ B b n)))
                     (@bplus _ _ B (bsum _ _ B (Datatypes.S n) Hrow)
                              (bsum _ _ B (Datatypes.S n) Kf))).
  { eapply bae_trans with
      (b := bsum _ _ B (Datatypes.S n)
               (fun i : nat => @bplus _ _ B (Hrow i) (Kf i))).
    - apply (bsum_ext _ _ B (Datatypes.S n)
                (fun i : nat => @bmult _ _ B (Ai i) (exp_series_partial _ _ B b n))
                (fun i : nat => @bplus _ _ B (Hrow i) (Kf i))).
      intros k _. exact (Hpt k).
    - exact (bsum_plus _ _ B (Datatypes.S n) Hrow Kf). }
  assert (H3 : bae (@bplus _ _ B (@bplus _ _ B (bsum _ _ B (Datatypes.S n) Hrow)
                                        (bsum _ _ B (Datatypes.S n) Kf))
                              (@bopp _ _ B (bsum _ _ B (Datatypes.S n) Hrow)))
                     (bsum _ _ B (Datatypes.S n) Kf)).
  { apply (@bae_sym _ _ B).
    eapply bae_trans with
      (b := @bplus _ _ B (bsum _ _ B (Datatypes.S n) Kf)
                   (@bplus _ _ B (bsum _ _ B (Datatypes.S n) Hrow)
                            (@bopp _ _ B (bsum _ _ B (Datatypes.S n) Hrow)))).
    - (* bsum Kf == bsum Kf + (bsum Hrow + -bsum Hrow): first == itself+0, then wd_r *)
      eapply bae_trans with
        (b := @bplus _ _ B (bsum _ _ B (Datatypes.S n) Kf) (@bzero _ _ B)).
      + apply (@bae_sym _ _ B).
        exact (@bplus_zero _ _ B (bsum _ _ B (Datatypes.S n) Kf)).
      + apply (@bplus_wd_r _ _ B). apply (@bae_sym _ _ B).
        exact (@bplus_opp _ _ B (bsum _ _ B (Datatypes.S n) Hrow)).
    - (* bsum Kf + (bsum Hrow + -bsum Hrow) == (bsum Hrow + bsum Kf) + -bsum Hrow *)
      eapply bae_trans with
        (b := @bplus _ _ B (@bplus _ _ B (bsum _ _ B (Datatypes.S n) Kf)
                                (bsum _ _ B (Datatypes.S n) Hrow))
                       (@bopp _ _ B (bsum _ _ B (Datatypes.S n) Hrow))).
      + apply (@bplus_assoc _ _ B _ _ _).
      + apply (@bplus_wd_l _ _ B).
        exact (@bplus_comm _ _ B (bsum _ _ B (Datatypes.S n) Kf)
                             (bsum _ _ B (Datatypes.S n) Hrow)). }
  eapply bae_trans with
    (b := @bplus _ _ B (bsum _ _ B (Datatypes.S n)
                       (fun i : nat =>
                          @bmult _ _ B (Ai i) (exp_series_partial _ _ B b n)))
                  (@bopp _ _ B (bsum _ _ B (Datatypes.S n) Hrow))).
  - exact H1.
  - eapply bae_trans with
      (b := @bplus _ _ B (@bplus _ _ B (bsum _ _ B (Datatypes.S n) Hrow)
                              (bsum _ _ B (Datatypes.S n) Kf))
                     (@bopp _ _ B (bsum _ _ B (Datatypes.S n) Hrow))).
    + apply (@bplus_wd_l _ _ B). exact H2.
    + exact H3.
Qed.
(* (4) the block-sum norm bound: ‖block n‖ ≤T Σ_{i≤n} ‖a‖^i/i!·tail(‖b‖; n−i..n) *)
Lemma bxae_block_norm_le : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall n : nat,
    QleT' (@bnorm _ _ B (@bplus _ _ B (@bmult _ _ B (exp_series_partial _ _ B a n)
                                                (exp_series_partial _ _ B b n))
                                  (@bopp _ _ B (exp_series_partial _ _ B
                                          (@bplus _ _ B a b) n))))
          (ncv_qsum (fun i : nat =>
                 q_pow (@bnorm _ _ B a) i / q_fact i
                 * exp_tail_abs (Nat.sub n i) n (@bnorm _ _ B b))
               (Datatypes.S n)).
Proof.
  intros BA bae B a b hab n.
  eapply (QeqT_Qle_bool_cong _ _ _
            (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _
               (bxae_diff_block _ _ B a b hab n)))).
  eapply qleT'_trans.
  - eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _
               (bxae_bsum_ncvsum _ _ B
                  (fun i : nat =>
                     @bmult _ _ B (@bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))
                              (@bplus _ _ B (exp_series_partial _ _ B b n)
                                       (@bopp _ _ B (exp_series_partial _ _ B b
                                                  (Nat.sub n i)))))
                  (Datatypes.S n))))).
    exact (ncv_norm_sum_le _ _ B
             (fun i : nat =>
                @bmult _ _ B (@bmult _ _ B (bpow _ _ B a i) (@bcoef _ _ B (/ q_fact i)))
                         (@bplus _ _ B (exp_series_partial _ _ B b n)
                                  (@bopp _ _ B (exp_series_partial _ _ B b
                                               (Nat.sub n i)))))
             (Datatypes.S n)).
  - apply ncv_qsum_le. intros i. destruct i as [| i'].
    + (* i = 0: ‖A 0‖ == 1 (via bcoef 1) *)
      assert (Hn0 : (Nat.sub n 0 <= n)%nat) by lia.
      assert (HA0 : bae (@bmult _ _ B (bpow _ _ B a 0%nat)
                                  (@bcoef _ _ B (/ q_fact 0%nat)))
                           (@bcoef _ _ B 1%Q)).
      { assert (Hq0 : (/ q_fact 0%nat)%Q = 1%Q) by reflexivity.
        rewrite Hq0.
        change (bpow _ _ B a 0%nat) with (@bone _ _ B).
        exact (@bmult_one_l _ _ B (@bcoef _ _ B 1%Q)). }
      eapply qleT'_trans.
      * exact (@bnorm_mult _ _ B (@bmult _ _ B (bpow _ _ B a 0%nat)
                                      (@bcoef _ _ B (/ q_fact 0%nat)))
                             (@bplus _ _ B (exp_series_partial _ _ B b n)
                                      (@bopp _ _ B (exp_series_partial _ _ B b
                                                  (Nat.sub n 0))))).
      * eapply qleT'_trans.
        { eapply (qleT'_mult_compat_r).
          { apply (@bnorm_pos _ _ B). }
          { eapply (QeqT_Qle_bool_cong _ _ _
                      (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _ HA0))).
            eapply (QeqT_Qle_bool_cong _ _ _
                      (qeqT_sym_hw _ _ (@bnorm_coef _ _ B 1%Q))).
            apply qleT'_refl. } }
        { apply (bxae_qleT'_mul_le (Qabs 1%Q)
                   (q_pow (@bnorm _ _ B a) 0%nat / q_fact 0%nat)%Q).
          -- apply Qle_refl.
          -- apply QleT'_to_Qle.
             exact (esp_diff_le_tail _ _ B b (Nat.sub n 0) n Hn0).
          -- apply QleT'_to_Qle. apply (@bnorm_pos _ _ B).
          -- exact (QleT'_to_Qle _ _ Qle_0_1). }
    + (* i = S i': bnorm_esp_term × esp_diff_le_tail *)
      assert (HnS : (Nat.sub n (Datatypes.S i') <= n)%nat) by lia.
      eapply qleT'_trans.
      * exact (@bnorm_mult _ _ B (@bmult _ _ B (bpow _ _ B a (Datatypes.S i'))
                                       (@bcoef _ _ B (/ q_fact (Datatypes.S i'))))
                             (@bplus _ _ B (exp_series_partial _ _ B b n)
                                      (@bopp _ _ B (exp_series_partial _ _ B b
                                                  (Nat.sub n (Datatypes.S i')))))).
      * apply (bxae_qleT'_mul_le).
        -- apply QleT'_to_Qle. apply (bnorm_esp_term _ _ B a i').
        -- apply QleT'_to_Qle.
           exact (esp_diff_le_tail _ _ B b (Nat.sub n (Datatypes.S i')) n HnS).
        -- apply QleT'_to_Qle. apply (@bnorm_pos _ _ B).
        -- apply (bxae_term_nonneg (@bnorm _ _ B a) (Datatypes.S i')).
           apply QleT'_to_Qle. exact (@bnorm_pos _ _ B a).
Qed.

(* (4) small difference: ∀eps>0 ∃N, n≥N ⟹ ‖esp a n·esp b n − esp (a+b) n‖ < eps *)
Lemma bxae_diff_small : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    QltT (@bnorm _ _ B (@bplus _ _ B (@bmult _ _ B (exp_series_partial _ _ B a n)
                                                (exp_series_partial _ _ B b n))
                                  (@bopp _ _ B (exp_series_partial _ _ B
                                          (@bplus _ _ B a b) n)))) eps).
Proof.
  intros BA bae B a b hab eps Heps.
  destruct (bxae_qblock_small (@bnorm _ _ B a) (@bnorm _ _ B b) eps
              (QleT'_to_Qle 0 (@bnorm _ _ B a) (@bnorm_pos _ _ B a))
              (QleT'_to_Qle 0 (@bnorm _ _ B b) (@bnorm_pos _ _ B b))
              Heps) as [N HN].
  exists N. intros n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _
           (ncv_qsum (fun i : nat =>
                 q_pow (@bnorm _ _ B a) i / q_fact i
                 * exp_tail_abs (Nat.sub n i) n (@bnorm _ _ B b))
               (Datatypes.S n)) eps).
  - exact (QleT'_to_Qle _ _
             (bxae_block_norm_le _ _ B a b hab n)).
  - exact (HN n Hn).
Qed.

(* limit shift: v→l and ‖u n − v n‖→0 ⟹ u→l *)
Lemma bxae_lim_shift : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (u v : nat -> BA) (l : BA),
  blim _ _ B v l ->
  (forall eps : Q, QltT 0 eps ->
     sigT (fun N : nat => forall n : nat, NatLe N n ->
       QltT (@bnorm _ _ B (@bplus _ _ B (u n) (@bopp _ _ B (v n)))) eps)) ->
  blim _ _ B u l.
Proof.
  intros BA bae B u v l Hv Hdiff eps Heps.
  assert (Hh : QltT 0 (eps / 2)%Q) by (apply bxuq_half_pos; exact Heps).
  destruct (Hdiff (eps / 2)%Q Hh) as [N1 HN1].
  destruct (Hv (eps / 2)%Q Hh) as [N2 HN2].
  exists (Nat.max N1 N2). intros n Hn.
  eapply (QeqT_Qlt_bool_cong _ _ _
            (qeqT_sym_hw _ _ (@bnorm_wd _ _ B _ _
               (bxuq_diff_split _ _ B (u n) (v n) l)))).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _
           ((@bnorm _ _ B (@bplus _ _ B (u n) (@bopp _ _ B (v n)))) +
            (@bnorm _ _ B (@bplus _ _ B (v n) (@bopp _ _ B l))))%Q eps).
  - exact (QleT'_to_Qle _ _
             (@bnorm_plus _ _ B (@bplus _ _ B (u n) (@bopp _ _ B (v n)))
                           (@bplus _ _ B (v n) (@bopp _ _ B l)))).
  - apply QltT_to_Qlt.
    apply (bxuq_sum_half_lt
             (@bnorm _ _ B (@bplus _ _ B (u n) (@bopp _ _ B (v n))))
             (@bnorm _ _ B (@bplus _ _ B (v n) (@bopp _ _ B l)))).
    + assert (Hle1 : (N1 <= n)%nat).
      * apply (Nat.le_trans N1 (Nat.max N1 N2) n).
        -- apply Nat.le_max_l.
        -- exact (NatLe_drop _ _ Hn).
      * exact (HN1 n (NatLe_lift _ _ Hle1)).
    + assert (Hle2 : (N2 <= n)%nat).
      * apply (Nat.le_trans N2 (Nat.max N1 N2) n).
        -- apply Nat.le_max_r.
        -- exact (NatLe_drop _ _ Hn).
      * exact (HN2 n (NatLe_lift _ _ Hle2)).
Qed.

(* six-link composition: (5) the left limit + (4) the small-difference shift + (6) uniqueness *)
(* migration note: the seven bxae_ pieces (term_reassoc/binom_row/tri_row/           *)
(* diff_block/block_norm_le/diff_small/exp_add) have their signatures narrowed to    *)
(* zero premises, with bnh_esp_term_binom supplying the same position and the        *)
(* hplus/hwd parameters removed entirely.                                            *)

Theorem bxae_exp_add : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae)
  (a b : BA),
  bae (@bmult _ _ (@bxce_base _ _ E) a b) (@bmult _ _ (@bxce_base _ _ E) b a) ->
  bae (@bxdef_emul _ _ (@bxce_base _ _ E) (bxdef_exp _ _ (@bxce_base _ _ E) a)
                    (bxdef_exp _ _ (@bxce_base _ _ E) b))
       (bxdef_exp _ _ (@bxce_base _ _ E) (@bplus _ _ (@bxce_base _ _ E) a b)).
Proof.
  intros BA bae E a b hab.
  unfold bxdef_emul.
  apply (bxuq_lim_uniq _ _ E
           (fun n : nat =>
              @bmult _ _ (@bxce_base _ _ E) (exp_series_partial _ _ (@bxce_base _ _ E) a n)
                                    (exp_series_partial _ _ (@bxce_base _ _ E) b n))).
  - exact (bxadd_esp_prod_blim _ _ (@bxce_base _ _ E) a b).
  - apply (bxae_lim_shift _ _ (@bxce_base _ _ E)
             (fun n : nat =>
                @bmult _ _ (@bxce_base _ _ E) (exp_series_partial _ _ (@bxce_base _ _ E) a n)
                                      (exp_series_partial _ _ (@bxce_base _ _ E) b n))
             (exp_series_partial _ _ (@bxce_base _ _ E) (@bplus _ _ (@bxce_base _ _ E) a b))
             (bxdef_exp _ _ (@bxce_base _ _ E) (@bplus _ _ (@bxce_base _ _ E) a b))).
    + exact (bxdef_exp_spec _ _ (@bxce_base _ _ E)
                (@bplus _ _ (@bxce_base _ _ E) a b)).
    + intros eps Heps.
      destruct (bxae_diff_small _ _ (@bxce_base _ _ E) a b hab eps Heps)
        as [N HN].
      exists N. intros n Hn.
      apply HN. exact (NatLe_drop _ _ Hn).
Qed.
(* ================= §2 the bxoo_lim_esp_zero_bone family ================= *)
(* ================= §1 the bxoo_lim_esp_zero_bone family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* S1 mechanical piece 1 (the bzero-neighborhood reframe): the zero-element series *)
(*   partial-sum sequence converges to bone.                                       *)
(*   The partial sums are constantly one (the same face as bxdef_esp_zero_series /  *)
(*   BXB bxb_series_zero)                                                          *)
(*   ⟹ the distance is constantly ‖bone+(−bone)‖ = 0 ⟹ the closed-form certificate *)
(*   N=0.                                                                          *)

Lemma bxoo_lim_esp_zero_bone : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae),
  blim _ _ B (fun n : nat => exp_series_partial _ _ B (@bzero _ _ B) n) (@bone _ _ B).
Proof.
  intros BA bae B q Hq.
  refine (existT (fun N : nat => forall n : nat, NatLe N n ->
            QltT (@bnorm _ _ B (@bplus _ _ B (exp_series_partial _ _ B (@bzero _ _ B) n)
                                     (@bopp _ _ B (@bone _ _ B)))) q) 0%nat _).
  intros n Hn.
  pose proof (@bnorm_wd _ _ B
      (@bplus _ _ B (exp_series_partial _ _ B (@bzero _ _ B) n)
               (@bopp _ _ B (@bone _ _ B)))
      (@bplus _ _ B (@bone _ _ B) (@bopp _ _ B (@bone _ _ B)))
      (@bplus_wd _ _ B (exp_series_partial _ _ B (@bzero _ _ B) n)
                  (@bopp _ _ B (@bone _ _ B))
                  (@bone _ _ B) (@bopp _ _ B (@bone _ _ B))
                  (bxdef_esp_zero_series _ _ B n)
                  (@bae_refl _ _ B (@bopp _ _ B (@bone _ _ B))))) as HW1.
  pose proof (@bnorm_wd _ _ B
      (@bplus _ _ B (@bone _ _ B) (@bopp _ _ B (@bone _ _ B)))
      (@bzero _ _ B)
      (@bplus_opp _ _ B (@bone _ _ B))) as HW2.
  eapply (QeqT_Qlt_bool_cong _ _ _ (qeqT_sym_hw _ _ HW1)).
  eapply (QeqT_Qlt_bool_cong _ _ _ (qeqT_sym_hw _ _ HW2)).
  rewrite (@bnorm_zero _ _ B).
  exact Hq.
Qed.

(* S1 mechanical piece 2 (the CD3-shape to blim reframe): the near-one neighborhood *)
(*   shape and the blim shape are verbatim isomorphic at l=bone (unfolding blim u   *)
(*   bone gives exactly this premise shape).                                        *)
(*   CD3 connection slot: if the actual shape of bxcd_prod_near_one is              *)
(*     forall B a q, QltT 0 q -> sigT N, forall n, NatLe N n ->                     *)
(*       QltT (bnorm (bplus (esp a n·esp(bopp a) n) (bopp bone))) q                 *)
(*   then bxoo_nearone_blim _ _ B _ (bxcd_prod_near_one _ _ B a) bridges in one     *)
(*   step.                                                                          *)

Lemma bxoo_nearone_blim : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (S : nat -> BA),
  (forall q : Q, QltT 0 q ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
      QltT (@bnorm _ _ B (@bplus _ _ B (S n) (@bopp _ _ B (@bone _ _ B)))) q)) ->
  blim _ _ B S (@bone _ _ B).
Proof.
  intros BA bae B S H q Hq. exact (H q Hq).
Qed.

(* S1 mechanical piece 3 (the emul tidying piece): the associative symmetry face of *)
(*   multiplication (the only tidying shape guaranteed under a noncommutative       *)
(*   class; the class has no bmult_comm, so a commutativity face cannot be built —  *)
(*   honestly not forced).                                                          *)

Lemma bxoo_bmult_assoc_sym : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (x y z : BA),
  bae (@bmult _ _ B (@bmult _ _ B x y) z) (@bmult _ _ B x (@bmult _ _ B y z)).
Proof.
  intros BA bae B x y z. exact (@bae_sym _ _ B _ _ (@bmult_assoc _ _ B x y z)).
Qed.

(* S2 the UNQ connection shape (Set face): two limits of the same sequence are      *)
(*   bae-equal — the shape pin of the main lemma's necessary piece.  Once UNQ is in *)
(*   place, if bxuq_lim_uniq has this same shape the connection is                  *)
(*   exact (bxuq_lim_uniq B); if the argument order / class indices differ, wrap a  *)
(*   reordering adapter around this shape (the eps record stays zero; a pure        *)
(*   argument-order migration).                                                     *)

Definition bxoo_uniq_shape (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) : Set :=
  forall (u : nat -> BA) (x y : BA),
    blim _ _ B u x -> blim _ _ B u y -> bae x y.

(* S3 the tail piece ((4), parameterized by (3)): bxdef_exp bzero == bone.          *)
(*   Two limit chains feed uniqueness together: bxdef_exp_spec (the ExpDef export)  *)
(*   + bxoo_lim_esp_zero_bone (S1 mechanical piece 1).                              *)

Lemma bxoo_bzero_eq_bone_assembly : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae),
  bxoo_uniq_shape _ _ B -> bae (bxdef_exp _ _ B (@bzero _ _ B)) (@bone _ _ B).
Proof.
  intros BA bae B Hunq.
  exact (Hunq (fun n : nat => exp_series_partial _ _ B (@bzero _ _ B) n)
              (bxdef_exp _ _ B (@bzero _ _ B)) (@bone _ _ B)
              (bxdef_exp_spec _ _ B (@bzero _ _ B))
              (bxoo_lim_esp_zero_bone _ _ B)).
Qed.

(* S4 the main assembly piece ((1)+(2)+(3)+(4) closed by conjunction,               *)
(*   parameterized by the two gates (2) and (3)):                                   *)
(*   bae (e^a·e^(−a)) (e^0) := bae_trans                                            *)
(*     (uniqueness: the sequence's left limit e^a·e^(−a) == the near-one limit      *)
(*     bone)                                                                        *)
(*     (the symmetry of the tail piece (4)).                                        *)
(*   Every assembly step is genuinely implemented (the bae_trans conjunction +      *)
(*   uniqueness used twice + the symmetric reversal); only (2)'s blim slot and      *)
(*   (3)'s uniq slot remain explicit premises.                                      *)

Theorem bxoo_exp_opp_one_assembly : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a : BA),
  bxoo_uniq_shape _ _ B ->
  blim _ _ B (fun n : nat => @bmult _ _ B (exp_series_partial _ _ B a n)
                                  (exp_series_partial _ _ B (@bopp _ _ B a) n))
         (@bone _ _ B) ->
  bae (@bmult _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B (@bopp _ _ B a)))
        (bxdef_exp _ _ B (@bzero _ _ B)).
Proof.
  intros BA bae B a Hunq Hnear.
  exact (@bae_trans _ _ B
           (@bmult _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B (@bopp _ _ B a)))
           (@bone _ _ B)
           (bxdef_exp _ _ B (@bzero _ _ B))
           (Hunq (fun n : nat => @bmult _ _ B (exp_series_partial _ _ B a n)
                                  (exp_series_partial _ _ B (@bopp _ _ B a) n))
                 (@bmult _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B (@bopp _ _ B a)))
                 (@bone _ _ B)
                 (bxadd_esp_prod_blim _ _ B a (@bopp _ _ B a))
                 Hnear)
           (@bae_sym _ _ B (bxdef_exp _ _ B (@bzero _ _ B)) (@bone _ _ B)
             (bxoo_bzero_eq_bone_assembly _ _ B Hunq))).
Qed.

(* S5 the UNQ-gate closing piece (obtained for the main ledger once the gate        *)
(* material is written and pre-verified): bxdef_exp bzero == bone — an              *)
(* unconditional bae equality on the Ext layer, closing the recorded open item      *)
(* "the exp(0)=one complete-equality face" for the Ext instance.                    *)

Corollary bxoo_bzero_eq_bone : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae),
  bae (bxdef_exp _ _ (@bxce_base _ _ E) (@bzero _ _ (@bxce_base _ _ E)))
      (@bone _ _ (@bxce_base _ _ E)).
Proof.
  intros BA bae E.
  apply (bxoo_bzero_eq_bone_assembly _ _ (@bxce_base _ _ E)).
  exact (bxuq_lim_uniq _ _ E).
Qed.

(*   (2) the CD12 genuine piece bxcd_prod_near_one (with its hplus/hwd premises     *)
(*     removed, the call sites accordingly drop the two arguments                   *)
(*     bxce_coef_plus/bxce_coef_wd — after removing hplus/hwd the fields no longer  *)
(*     need feeding; the final face stays pinned to the Ext layer).                 *)
(*   (3) bxuq_lim_uniq _ _ E, after stripping E, is isomorphic to bxoo_uniq_shape   *)
(*     on the base.                                                                 *)
(*   The main lemma bxoo_exp_opp_one: an unconditional bae equality —               *)
(*     bae_trans (uniqueness: the sequence's left limit e^a·e^(−a) == the near-one  *)
(*     limit bone) (the symmetry of the tail piece (4)), verbatim the same          *)
(*     conjunction face as the S4 assembly piece.                                   *)

Theorem bxoo_exp_opp_one : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae)
  (a : BA),
  bae (@bmult _ _ (@bxce_base _ _ E) (bxdef_exp _ _ (@bxce_base _ _ E) a)
                   (bxdef_exp _ _ (@bxce_base _ _ E) (@bopp _ _ (@bxce_base _ _ E) a)))
      (bxdef_exp _ _ (@bxce_base _ _ E) (@bzero _ _ (@bxce_base _ _ E))).
Proof.
  intros BA bae E a.
  apply (bxoo_exp_opp_one_assembly _ _ (@bxce_base _ _ E) a
           (bxuq_lim_uniq _ _ E)).
  apply (bxoo_nearone_blim _ _ (@bxce_base _ _ E)).
  exact (bxcd_prod_near_one _ _ (@bxce_base _ _ E) a).
Qed.
(* ================= §2 the s3c_hplus_of family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* the class-field to explicit-premise supply anchor (the bnh anchor-1 colocated position: the field shape ≡ the premise shape) *)
Definition s3c_hplus_of (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  : forall q r : Q,
    bae (@bplus _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r)) (@bcoef _ _ B (q + r)%Q)
  := @bcoef_plus _ _ B.

Definition s3c_hwd_of (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  : forall q r : Q, q == r -> bae (@bcoef _ _ B q) (@bcoef _ _ B r)
  := fun q r Hq => @bcoef_wd _ _ B q r (qeq_imp_qeqT _ _ Hq).

(* (1) the E-carrier's unconditional exp_add (removing the hplus/hwd explicit pins of bxae_exp_add) *)

Theorem s3c_exp_add_base : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae)
  (a b : BA),
  bae (@bmult _ _ (@bxce_base _ _ E) a b)
       (@bmult _ _ (@bxce_base _ _ E) b a) ->
  bae (@bxdef_emul _ _ (@bxce_base _ _ E) (bxdef_exp _ _ (@bxce_base _ _ E) a)
                    (bxdef_exp _ _ (@bxce_base _ _ E) b))
       (bxdef_exp _ _ (@bxce_base _ _ E) (@bplus _ _ (@bxce_base _ _ E) a b)).
Proof.
  intros BA bae E a b hab.
  exact (bxae_exp_add _ _ E a b hab).
Qed.

(* (2) the plain B-carrier exp_add assembly (the six-link confluence: (5) the left  *)
(*   limit + (4) the small-difference shift + (6) uniqueness (as a premise); the    *)
(*   uniqueness slot is given explicitly as bxoo_uniq_shape —                       *)
(*   the plain class has no sep field, the same caliber as bxoo_exp_opp_one_assembly) *)

Theorem s3c_exp_add_plain : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  bxoo_uniq_shape _ _ B ->
  bae (@bxdef_emul _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B b))
       (bxdef_exp _ _ B (@bplus _ _ B a b)).
Proof.
  intros BA bae B a b hab Hunq.
  unfold bxdef_emul.
  apply (Hunq (fun n : nat =>
                 @bmult _ _ B (exp_series_partial _ _ B a n)
                          (exp_series_partial _ _ B b n))).
  - (* (5) the left limit: the partial-product sequence -> e^a·e^b *)
    exact (bxadd_esp_prod_blim _ _ B a b).
  - (* (4) the small-difference shift: the partial-product sequence -> e^(a+b) *)
    apply (bxae_lim_shift _ _ B
             (fun n : nat =>
                @bmult _ _ B (exp_series_partial _ _ B a n)
                         (exp_series_partial _ _ B b n))
             (fun n : nat => exp_series_partial _ _ B (@bplus _ _ B a b) n)
             (bxdef_exp _ _ B (@bplus _ _ B a b))
             (bxdef_exp_spec _ _ B (@bplus _ _ B a b))).
    intros eps Heps.
    destruct (bxae_diff_small _ _ B a b hab eps Heps) as [N HN].
    exists N. intros n Hn.
    exact (HN n (NatLe_drop N n Hn)).
Qed.

(* (3) the invertibility confluence: the inverse of (e^a) is e^{-a}                 *)
(*   (3a) unconditional on the Ext carrier: the two lemmas e^a·e^{-a} == e^0 and    *)
(*   e^0 == bone                                                                    *)

Theorem s3c_exp_opp_one_base : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae)
  (a : BA),
  bae (@bmult _ _ (@bxce_base _ _ E) (bxdef_exp _ _ (@bxce_base _ _ E) a)
                    (bxdef_exp _ _ (@bxce_base _ _ E) (@bopp _ _ (@bxce_base _ _ E) a)))
       (bxdef_exp _ _ (@bxce_base _ _ E) (@bzero _ _ (@bxce_base _ _ E))).
Proof.
  intros BA bae E a. exact (bxoo_exp_opp_one _ _ E a).
Qed.

Theorem s3c_exp_inv_base : forall (BA : Set) (bae : BA -> BA -> Set) (E : BanachAlgExt BA bae)
  (a : BA),
  bae (@bmult _ _ (@bxce_base _ _ E) (bxdef_exp _ _ (@bxce_base _ _ E) a)
                    (bxdef_exp _ _ (@bxce_base _ _ E) (@bopp _ _ (@bxce_base _ _ E) a)))
       (@bone _ _ (@bxce_base _ _ E)).
Proof.
  intros BA bae E a.
  apply (@bae_trans _ _ (@bxce_base _ _ E)
           (@bmult _ _ (@bxce_base _ _ E) (bxdef_exp _ _ (@bxce_base _ _ E) a)
                        (bxdef_exp _ _ (@bxce_base _ _ E) (@bopp _ _ (@bxce_base _ _ E) a)))
           (bxdef_exp _ _ (@bxce_base _ _ E) (@bzero _ _ (@bxce_base _ _ E)))
           (@bone _ _ (@bxce_base _ _ E))).
  - exact (bxoo_exp_opp_one _ _ E a).
  - exact (bxoo_bzero_eq_bone _ _ E).
Qed.

(*   (3b) the plain carrier: the Hnear slot of bxoo_exp_opp_one_assembly is closed  *)
(*   — the hplus/hwd explicit premises of bxcd_prod_near_one are fed from the base  *)
(*   class fields (the earlier note "plain cannot be fed" was a pre-migration       *)
(*   issue; it resolves once the bnh anchor-1 is in place).                         *)

Theorem s3c_exp_opp_one_plain : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a : BA),
  bxoo_uniq_shape _ _ B ->
  bae (@bmult _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B (@bopp _ _ B a)))
       (bxdef_exp _ _ B (@bzero _ _ B)).
Proof.
  intros BA bae B a Hunq.
  apply (bxoo_exp_opp_one_assembly _ _ B a Hunq).
  apply (bxoo_nearone_blim _ _ B
           (fun n : nat =>
              @bmult _ _ B (exp_series_partial _ _ B a n)
                       (exp_series_partial _ _ B (@bopp _ _ B a) n))).
  exact (bxcd_prod_near_one _ _ B a).
Qed.

Theorem s3c_exp_inv_plain : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a : BA),
  bxoo_uniq_shape _ _ B ->
  bae (@bmult _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B (@bopp _ _ B a)))
       (@bone _ _ B).
Proof.
  intros BA bae B a Hunq.
  apply (@bae_trans _ _ B
           (@bmult _ _ B (bxdef_exp _ _ B a) (bxdef_exp _ _ B (@bopp _ _ B a)))
           (bxdef_exp _ _ B (@bzero _ _ B))
           (@bone _ _ B)).
  - exact (s3c_exp_opp_one_plain _ _ B a Hunq).
  - exact (bxoo_bzero_eq_bone_assembly _ _ B Hunq).
Qed.

(* assumption-face self-attestation (PA ≥ 1 for each of the four main pieces)       *)
Print Assumptions s3c_exp_add_base.
Print Assumptions s3c_exp_add_plain.
Print Assumptions s3c_exp_inv_base.
Print Assumptions s3c_exp_inv_plain.
