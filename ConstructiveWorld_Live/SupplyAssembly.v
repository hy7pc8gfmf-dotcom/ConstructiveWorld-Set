(* ConstructiveWorld-Set -- supply assembly for the Ln2 irrationality closure. *)

(** * SupplyAssembly: the Ln2 Pade supply assembly and its two-stage conditional closure.

    Mission.  The supply assembly for the irrationality of ln 2: three
      installed legs of the Pade supply [ln2i_pade_supply] -- the integer
      face [sa_A] with [sa_A_nonzeroT], [sa_norm_bridge]; the closed-form
      leg [sa_clo] with [sa_clo_posT], [sa_clo_int]; the theta leg
      [sa_theta] with [sa_theta_leg_scaffold], [sa_clo_in_theta_window];
      the gap interface [sa_supply_rem] left open on the P2 identity, the
      assembly [sa_supply_assemble], and the closure [sa_ln2_irrational].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
      [Arith.Arith], [Bool.Bool], [Lia], [Setoid], [Morphisms], [Qfield],
      [Extraction].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [UpReqIrrationalCriterion], [UpReqLn2Irrational],
      [BeukersLists], [BeukersIdentity], [Ln2Escape], [Ln2Bridge] of this
      development.

    References.  This development, SupplyAssembly.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" SupplyAssembly.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqLn2Irrational.
Require Import BeukersLists.
Require Import BeukersIdentity.
Require Import Ln2Escape.
Require Import Ln2Bridge.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* Section 1. The integer face of A_n (leg 2) and the normalization bridge.                                     *)
(* ============================================================ *)

(* The integer face of A_n := 2^(n+1) * qtilde_n, carried by Z.of_nat of a
   nat product. *)
Definition sa_A (n : nat) : Z :=
  Z.of_nat (2 ^ (Datatypes.S n) * bk_Qn_qtilde n).

(* The Q carrier of A_n equals 2^(n+1) * qtilde_n, via bi_q_pow_2 and
   bk_Qmul_nat. *)
Lemma sa_A_q : forall n : nat,
  ((sa_A n) # 1)%Q
  == ((q_pow (2 # 1)%Q (Datatypes.S n)) * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q.
Proof.
  intro n. rewrite (qeqT_imp_qeq _ _ (bi_q_pow_2 (Datatypes.S n))).
  symmetry.
  exact (qeqT_imp_qeq _ _ (bk_Qmul_nat (2 ^ Datatypes.S n) (bk_Qn_qtilde n))).
Qed.

(* Leg 2, fully proved: 0 < |A_n|, since qtilde_n >= 3^n >= 1 gives
   A_n >= 2. *)
Theorem sa_A_nonzeroT : forall n : nat, QltT 0 (Qabs ((sa_A n) # 1)%Q).
Proof.
  intro n.
  assert (Hge : (2 <= 2 ^ (Datatypes.S n) * bk_Qn_qtilde n)%nat).
  { rewrite Nat.pow_succ_r'.
    pose proof (NatLe_drop _ _ (bk_Qn_ge_3pow_nat n)) as H3.
    pose proof (NatLe_drop _ _ (ln2b_pow_ge1 3 n ltac:(lia))) as H31.
    pose proof (NatLe_drop _ _ (ln2b_pow_ge1 2 n ltac:(lia))) as H21.
    nia. }
  apply Qlt_to_QltT.
  unfold sa_A. unfold Qabs, Qlt. cbn [Qnum Qden].
  destruct (Z.of_nat (2 ^ Datatypes.S n * bk_Qn_qtilde n)) as [| z | z]
    eqn:HM; cbn in *; lia.
Qed.

(* Normalization bridge: sa_A n # 1 == 2^(2n+1) * Q_n(1/2), the closed form
   placement of the corrected normalization factor 2^(n+1) * qtilde_n through
   bi_norm_factor. *)
Theorem sa_norm_bridge : forall n : nat,
  QeqT ((sa_A n) # 1)%Q
       ((q_pow (2 # 1)%Q (Datatypes.S (2 * n))
          * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q).
Proof. intro n. unfold sa_A. exact (bi_norm_factor n). Qed.

(* ============================================================ *)
(* Section 2. The positivity leg of clo_n (leg 3) with its integrality and upper-bound support faces.                          *)
(* ============================================================ *)

(* Carrier: clo_n := lne_B n, the closed form (n!)^2 / (2n+1)! of the Beta
   integral of t^n (1-t)^n over [0,1]. *)
Definition sa_clo (n : nat) : Q := lne_B n.

(* Leg 3, fully proved: 0 < clo_n, supplied directly by the positivity of
   the Beta closed form. *)
Theorem sa_clo_posT : forall n : nat, QltT 0 (sa_clo n).
Proof. intro n. exact (lne_B_posT n). Qed.

(* Integrality face: clo_n * (2n+1)! == (n!)^2 holds with an integer witness
   ([sigT]); this is the combination material for the integer face of B_n,
   and the route by which r_n becomes an integer once the P2 numerator side
   is available. *)
Theorem sa_clo_int : forall n : nat,
  sigT (fun m : Z =>
    QeqT (sa_clo n * q_fact (Datatypes.S (n + n))%nat) (m # 1)).
Proof. exact lne_B_int. Qed.

(* Upper-bound face: clo_n <= 4^(-n), the Q-side material for
   I_n <= 2^(n+1) * clo_n <= 2^(1-n); the integral-side half,
   1/(1-t/2)^(n+1) <= 2^(n+1), remains open with the P2 identity. *)
Theorem sa_clo_le_p4 : forall n : nat, QleT' (sa_clo n) (Qinv (lne_p4 n)).
Proof. exact lne_B_le_p4. Qed.

(* ============================================================ *)
(* Section 3. The theta leg (leg 1) with the half-power conversions.                                          *)
(* ============================================================ *)

Definition sa_theta : Q := (1 # 2)%Q.

(* Leg 1, fully proved: theta = 1/2 < 1. *)
Theorem sa_theta_lt1 : QltT sa_theta (1 # 1)%Q.
Proof.
  apply Qlt_to_QltT. unfold Qlt, sa_theta. cbn [Qnum Qden]. lia.
Qed.

(* Positivity of theta: the premise face of the decay machinery ln2b_decay. *)
Theorem sa_theta_posT : QltT 0 sa_theta.
Proof.
  apply Qlt_to_QltT. unfold Qlt, sa_theta. cbn [Qnum Qden]. lia.
Qed.

(* Powers of one. *)
Lemma sa_qpow_one_q : forall n : nat, q_pow (1 # 1)%Q n == (1 # 1)%Q.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. reflexivity.
Qed.

(* Half-power inverse: q_pow (1/2) n * q_pow 2 n == 1, via ln2b_qpow_inv. *)
Lemma sa_half_pow : forall n : nat,
  q_pow (1 # 2)%Q n * q_pow (2 # 1)%Q n == (1 # 1)%Q.
Proof.
  intro n. rewrite (qeqT_imp_qeq _ _ (ln2b_qpow_inv 1%Z 2%positive n)).
  apply sa_qpow_one_q.
Qed.

(* Half-power conversion: 2^(-n) == (1/2)^n. *)
Theorem sa_theta_pow_inv2 : forall n : nat,
  Qinv (q_pow (2 # 1)%Q n) == q_pow (1 # 2)%Q n.
Proof.
  intro n.
  assert (Hnz : ~ (q_pow (2 # 1)%Q n == 0%Q)).
  { intro E.
    (* The positivity of the power (bi_q_pow_pos2) rules out the zero case:
       q_neq_of_lt yields the Set-layer absurdity, and the empty match
       lowers it to this Prop goal. *)
    exact (match q_neq_of_lt (q_pow (2 # 1)%Q n) (bi_q_pow_pos2 n)
             (qeq_imp_qeqT _ _ E) with end). }
  assert (Hm := sa_half_pow n).
  assert (H1 : (Qinv (q_pow (2 # 1)%Q n) * q_pow (2 # 1)%Q n)%Q
               == (q_pow (1 # 2)%Q n * q_pow (2 # 1)%Q n)%Q).
  { rewrite (Qmult_comm (Qinv (q_pow (2 # 1)%Q n)) (q_pow (2 # 1)%Q n)).
    rewrite (Qmult_inv_r (q_pow (2 # 1)%Q n) Hnz).
    rewrite Hm. reflexivity. }
  exact (qeqT_imp_qeq _ _
           (lne_mult_canc _ _ (q_pow (2 # 1)%Q n) H1 Hnz)).
Qed.

(* The Q inverse is antitone: 0 < a <= b implies 1/b <= 1/a. *)
Lemma sa_Qinv_le : forall a b : Q, Qlt 0%Q a -> Qle a b -> Qle (Qinv b) (Qinv a).
Proof.
  intros [an ad] [bn bd] Ha Hab.
  unfold Qlt, Qle in Ha, Hab. cbn [Qnum Qden] in Ha, Hab.
  unfold Qle, Qinv. cbn [Qnum Qden].
  destruct an; destruct bn; cbn in *; nia.
Qed.

(* Pure-Q conversion for the theta leg, fully proved:
   1/(2^(n+1) * qtilde_n) <= (1/2)^n = theta^n; with qtilde_n >= 3^n >= 1
   this closes the error end 2^(-2n)/qtilde_n <= theta^n of the corrected
   identity. *)
Theorem sa_theta_leg_scaffold : forall n : nat,
  QleT' (Qinv ((q_pow (2 # 1)%Q (Datatypes.S n)
                 * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q))
        (q_pow (1 # 2)%Q n).
Proof.
  intro n. apply Qle_to_QleT'.
  setoid_rewrite <- (sa_theta_pow_inv2 n).
  apply sa_Qinv_le.
  - apply QltT_to_Qlt. apply bi_q_pow_pos2.
  - assert (Hq1 : (1 <= bk_Qn_qtilde n)%nat).
    { pose proof (NatLe_drop _ _ (bk_Qn_ge_3pow_nat n)) as H3.
      pose proof (NatLe_drop _ _ (ln2b_pow_ge1 3 n ltac:(lia))) as H31. lia. }
    rewrite (qeqT_imp_qeq _ _ (bi_q_pow_2 (Datatypes.S n))).
    rewrite (qeqT_imp_qeq _ _ (bk_Qmul_nat (2 ^ Datatypes.S n) (bk_Qn_qtilde n))).
    rewrite (qeqT_imp_qeq _ _ (bi_q_pow_2 n)).
    apply (QleT'_to_Qle _ _). apply bk_Qle_nat. apply NatLe_lift.
    rewrite Nat.pow_succ_r'. nia.
Qed.

(* Window match, fully proved: clo_n < theta^n for n >= 1; the carrier falls
   strictly inside the theta decision window, transported from the 2^(-n)
   window of lne_B_lt_p2 through sa_theta_pow_inv2. *)
Theorem sa_clo_in_theta_window : forall n : nat, (1 <= n)%nat ->
  QltT (sa_clo n) (q_pow sa_theta n).
Proof.
  intros n Hn.
  apply (bi_qlt_eq (lne_B n) (Qinv (ln2i_p2 n)) (sa_clo n) (q_pow sa_theta n)).
  - exact (lne_B_lt_p2 n Hn).
  - apply qeq_imp_qeqT. reflexivity.
  - unfold sa_theta.
    apply qeq_imp_qeqT.
    rewrite ln2i_p2_Z. rewrite <- (qeqT_imp_qeq _ _ (bi_q_pow_2 n)).
    apply sa_theta_pow_inv2.
Qed.

(* ============================================================ *)
(* Section 4. The standalone package of the three installed legs.                                      *)
(* ============================================================ *)

(* The head type: the standalone package of legs 1-3 of the five-leg supply. *)
Definition sa_supply_head : Set :=
  sigT (fun A : nat -> Z =>
    sigT (fun clo : nat -> Q =>
      sigT (fun th : Q =>
        And (QltT th (1 # 1))
          (And (forall n : nat, QltT 0 (Qabs ((A n) # 1)))
               (forall n : nat, QltT 0 (clo n)))))).

Theorem sa_supply_three_legs : sa_supply_head.
Proof.
  exists sa_A. exists sa_clo. exists sa_theta.
  split.
  - exact sa_theta_lt1.
  - split.
    + apply sa_A_nonzeroT.
    + apply sa_clo_posT.
Qed.

(* ============================================================ *)
(* Section 5. The gap interface for legs 4-5 and the two-stage assembly closure.                          *)
(* ============================================================ *)

(* Gap interface: the integer face of B_n together with the two real legs,
   the lower and upper bounds; it is the instantiation slot that resolves
   once the P2 identity I_n = 2^(n+1) * qtilde_n * X - r_n with
   X := lim ln2i_x is available (its three subparts: the partial-fraction
   engine, the residue coefficient c_1 = 2^n * qtilde_n, and the
   identification ln 2 = lim ln2i_x).  Precisely: nonemptiness of this
   interface is exactly the existence of the theta-tier Pade approximants,
   and this file claims no unconditional existence. *)
Definition sa_supply_rem : Set :=
  sigT (fun B : nat -> Z =>
    And (ln2b_line_lower sa_A B sa_clo)
        (ln2b_line_upper sa_A B sa_theta)).

(* Two-stage assembly: the three installed legs plus the gap interface fill
   the full five-layer supply type. *)
Theorem sa_supply_assemble : forall Hm : sa_supply_rem, ln2i_pade_supply.
Proof.
  intros [B [Hlow Hup]].
  exists sa_A. exists B. exists sa_clo. exists sa_theta.
  split.
  - exact sa_theta_lt1.
  - split.
    + apply sa_A_nonzeroT.
    + split.
      * apply sa_clo_posT.
      * split.
        -- exact Hlow.
        -- exact Hup.
Qed.

(* Two-stage closure of the irrationality of ln 2: it delegates to the
   Ln2Bridge theorem ln2b_irrational_from_supply, which runs
   lic_irrational_criterion directly with no detour.  The statement face is
   the opened form of that conclusion, carried entirely by Set:
   sigT, And, QltT, real_lt. *)
Theorem sa_ln2_irrational : forall (Hm : sa_supply_rem) (q : Q),
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) ln2i_x
                         (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish))
       (real_const q)))).
Proof.
  intros Hm q. exact (ln2b_irrational_from_supply (sa_supply_assemble Hm) q).
Qed.

(* ============================================================ *)
(* Section 6. Numerical anchors by vm_compute: A_1 = 2^2 * qtilde_1 = 12,  *)
(*    A_2 = 2^3 * qtilde_2 = 104, clo_1 = 1/6, theta^2 = 1/4.                                       *)
(* ============================================================ *)

Theorem sa_A1_anchor : QeqT ((sa_A 1) # 1)%Q (12 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_A2_anchor : QeqT ((sa_A 2) # 1)%Q (104 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_clo1_anchor : QeqT (sa_clo 1) (1 # 6)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem sa_theta2_anchor : QeqT (q_pow sa_theta 2) (1 # 4)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* Section 7. Extraction check and the Print Assumptions self-audit.                                 *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction sa_ln2_irrational sa_supply_assemble
  sa_supply_three_legs sa_A_nonzeroT sa_clo_posT sa_clo_int
  sa_theta_leg_scaffold sa_clo_in_theta_window sa_norm_bridge.
Print Assumptions sa_ln2_irrational.
Print Assumptions sa_supply_assemble.
Print Assumptions sa_supply_three_legs.
Print Assumptions sa_theta_leg_scaffold.
Print Assumptions sa_clo_in_theta_window.
Print Assumptions sa_A_nonzeroT.
