(* ========================================================================== *)
(*  ToyR_SupplyAssembly.v - ln2 irrationality supply assembly (ToyR variant;   *)
(*   Mission.  Instantiate the Ln2Bridge five-component existential            *)
(*   ln2i_pade_supply and close ln2 irrationality via ln2b_irrational_from_    *)
(*   supply (no bypass).  Stations: A_n integer face (sa_A, sa_A_q,            *)
(*   sa_A_nonzeroT, sa_A1/sa_A2_anchor), normalization bridge sa_norm_bridge,  *)
(*   carrier/theta faces (sa_clo/sa_theta families), Q-power support           *)
(*   (sa_qpow_one_q, sa_half_pow), Q-inverse monotone sa_Qinv_le, theta-leg    *)
(*   scaffold, theta-window sa_clo_in_theta_window, three-leg pack             *)
(*   sa_supply_three_legs), conditional sa_supply_rem (the B_n integer face    *)
(*   and the lower/upper real limbs await the identity corpus                  *)
(*   I_n = 2^(n+1) q_n X - r_n), two-stage sa_supply_assemble, final closure   *)
(*   sa_ln2_irrational.                                                        *)
(*   Dependencies.  S01_BaseRing S02_CauchyComplete S03_QExp                   *)
(*   UpReqIrrationalCriterion UpReqLn2Irrational BeukersLists BeukersIdentity  *)
(*   Ln2Escape Ln2Bridge; Stdlib QArith Qabs ZArith Arith Bool Lia Setoid      *)
(*   Morphisms Qfield Extraction (tail).                                       *)
(*   References.  bi_norm_factor/bi_qlt_eq/bi_q_pow_pos2/bi_pow3_pos           *)
(*   (BeukersIdentity); lne_mult_canc and the lne_B family (Ln2Escape);        *)
(*   ln2b_qpow_inv/ln2b_pow_ge1/ln2b_irrational_from_supply (Ln2Bridge);       *)
(*   bk_Qn family (BeukersLists); carriers/bridges QltT/QleT'/QeqT/NatLe,      *)
(*   qeq_imp_qeqT/qeqT_imp_qeq/qeq_imp_qle/qleT'_trans, NatLe_drop/lift        *)
(*   (S01-S03).  Constructivity.  Zero axioms, zero suspended premises, zero   *)
(*   classical logic; all statement faces Set-layer                            *)
(*   (QeqT/QltT/QleT'/NatLe/real_lt); Q-layer Qeq/Qle serves proof bodies      *)
(*   only; the sa_clo_in_theta_window premise washed to NatLe 1 n;             *)
(*   extractable (tail Separate Extraction/Print Assumptions).  Build. rocq c  *)
(*   -native-compiler no -q (Rocq 9.1, guard-wrapped, ulimit -s 65532).        *)
(* ========================================================================== *)

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
(* Section 1: A_n integer face (leg 2) + normalization bridge   *)
(* ============================================================ *)

(* A_n := 2^{n+1} q_n with q_n := bk_Qn_qtilde n (nat carrier, Z-typed) *)
Definition sa_A (n : nat) : Z :=
  Z.of_nat (2 ^ (Datatypes.S n) * bk_Qn_qtilde n).

(* sa_A_q: the Q carrier of A_n equals 2^{n+1} q_n (bi_q_pow_2 + bk_Qmul_nat
   conversion; canonical QeqT face) *)
Lemma sa_A_q : forall n : nat,
  QeqT ((sa_A n) # 1)%Q
       ((q_pow (2 # 1)%Q (Datatypes.S n)) * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q.
Proof.
  intro n. unfold sa_A. apply qeq_imp_qeqT.
  rewrite <- (qeqT_imp_qeq _ _ (bk_Qmul_nat (2 ^ Datatypes.S n) (bk_Qn_qtilde n))).
  rewrite (qeqT_imp_qeq _ _ (bi_q_pow_2 (Datatypes.S n))).
  reflexivity.
Qed.

(* Leg-2 genuine proof: 0 < |A_n| (q_n >= 3^n >= 1 implies A_n >= 2) *)
Theorem sa_A_nonzeroT : forall n : nat, QltT 0 (Qabs ((sa_A n) # 1)%Q).
Proof.
  intro n.
  assert (Hge : (2 <= 2 ^ (Datatypes.S n) * bk_Qn_qtilde n)%nat).
  { rewrite Nat.pow_succ_r'.
    pose proof (NatLe_drop (3 ^ n) (bk_Qn_qtilde n) (bk_Qn_ge_3pow_nat n)) as H3.
    assert (Hp : (0 < 3 ^ n)%nat).
    { pose proof (bi_pow3_pos n) as Hpid.
      destruct (Nat.ltb 0 (3 ^ n)) eqn:E.
      - exact (proj1 (Nat.ltb_lt 0 (3 ^ n)) E).
      - inversion Hpid. }
    pose proof (NatLe_drop 1 (2 ^ n) (ln2b_pow_ge1 2 n ltac:(lia))) as H21.
    nia. }
  apply Qlt_to_QltT.
  unfold sa_A. unfold Qabs, Qlt. cbn [Qnum Qden].
  destruct (Z.of_nat (2 ^ Datatypes.S n * bk_Qn_qtilde n)) as [| z | z]
    eqn:HM; cbn in *; lia.
Qed.

(* sa_norm_bridge: sa_A n # 1 == 2^{2n+1} Q_n(1/2) (closed form of the true
   normalization factor 2^{n+1} q_n, via bi_norm_factor) *)
Theorem sa_norm_bridge : forall n : nat,
  QeqT ((sa_A n) # 1)%Q
       ((q_pow (2 # 1)%Q (Datatypes.S (2 * n))
          * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q).
Proof. intro n. exact (bi_norm_factor n). Qed.

(* ============================================================ *)
(* Section 2: carrier positivity (leg 3) + integrality/upper     *)
(*   bound support face                                          *)
(* ============================================================ *)

(* Carrier: clo_n := lne_B n = the closed form (n!)^2/(2n+1)! of the
   integral of t^n (1-t)^n over [0,1] *)
Definition sa_clo (n : nat) : Q := lne_B n.

(* Leg-3 genuine proof: 0 < clo_n (from lne_B_posT) *)
Theorem sa_clo_posT : forall n : nat, QltT 0 (sa_clo n).
Proof. intro n. apply lne_B_posT. Qed.

(* sa_clo_int: carrier integrality face clo_n * (2n+1)! == (n!)^2 with the
   witness in Z (existential witness; the combinatorial raw material for the
   B_n integer face; the numerator side Z-typing goes through here) *)
Theorem sa_clo_int : forall n : nat,
  sigT (fun m : Z =>
    QeqT (sa_clo n * q_fact (Datatypes.S (n + n))%nat) (m # 1)).
Proof. exact lne_B_int. Qed.

(* sa_clo_le_p4: carrier upper bound clo_n <= 4^{-n} (the Q-side raw material
   of I_n <= 2^{n+1} clo_n <= 2^{1-n}; the integral-side half 1/(1-t/2)^{n+1}
   <= 2^{n+1} awaits the identity corpus) *)
Theorem sa_clo_le_p4 : forall n : nat, QleT' (sa_clo n) (Qinv (lne_p4 n)).
Proof. exact lne_B_le_p4. Qed.

(* ============================================================ *)
(* Section 3: theta register (leg 1) + half-power conversion     *)
(* ============================================================ *)

Definition sa_theta : Q := (1 # 2)%Q.

(* Leg-1 genuine proof: theta = 1/2 < 1 *)
Theorem sa_theta_lt1 : QltT sa_theta (1 # 1)%Q.
Proof.
  apply Qlt_to_QltT. unfold Qlt, sa_theta. cbn [Qnum Qden]. lia.
Qed.

(* sa_theta_posT: theta positivity (prerequisite face of ln2b_decay) *)
Theorem sa_theta_posT : QltT 0 sa_theta.
Proof.
  apply Qlt_to_QltT. unfold Qlt, sa_theta. cbn [Qnum Qden]. lia.
Qed.

(* The power of one (canonical QeqT face) *)
Lemma sa_qpow_one_q : forall n : nat, QeqT (q_pow (1 # 1)%Q n) (1 # 1)%Q.
Proof.
  intro n. apply qeq_imp_qeqT. induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. reflexivity.
Qed.

(* Half-power inverse: q_pow (1/2) n * q_pow 2 n == 1 (conversion through
   ln2b_qpow_inv; canonical QeqT face) *)
Lemma sa_half_pow : forall n : nat,
  QeqT (q_pow (1 # 2)%Q n * q_pow (2 # 1)%Q n) (1 # 1)%Q.
Proof.
  intro n. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (ln2b_qpow_inv 1%Z 2%positive n)).
  exact (qeqT_imp_qeq _ _ (sa_qpow_one_q n)).
Qed.

(* Half-power inverse conversion: 2^{-n} == (1/2)^n (canonical QeqT face;
   closes through lne_mult_canc with its Set-layer conclusion) *)
Theorem sa_theta_pow_inv2 : forall n : nat,
  QeqT (Qinv (q_pow (2 # 1)%Q n)) (q_pow (1 # 2)%Q n).
Proof.
  intro n.
  assert (Hnz : ~ (q_pow (2 # 1)%Q n == 0%Q)).
  { intro E. pose proof (QltT_to_Qlt 0%Q (q_pow (2 # 1)%Q n)
                          (bi_q_pow_pos2 n)) as Hp.
    apply (Qlt_not_eq 0%Q (q_pow (2 # 1)%Q n) Hp). exact (Qeq_sym _ _ E). }
  pose proof (qeqT_imp_qeq _ _ (sa_half_pow n)) as Hm.
  apply (lne_mult_canc _ _ (q_pow (2 # 1)%Q n)).
  - rewrite (Qmult_comm (Qinv (q_pow (2 # 1)%Q n)) (q_pow (2 # 1)%Q n)).
    rewrite (Qmult_inv_r (q_pow (2 # 1)%Q n) Hnz).
    rewrite Hm. reflexivity.
  - exact Hnz.
Qed.

(* sa_Qinv_le: Q-inverse monotonicity 0 < a <= b implies 1/b <= 1/a
   (Q-layer support lemma; canonical QltT/QleT' faces; Z case split nia) *)
Lemma sa_Qinv_le : forall a b : Q,
  QltT 0%Q a -> QleT' a b -> QleT' (Qinv b) (Qinv a).
Proof.
  intros a b Ha Hab.
  pose proof (QltT_to_Qlt 0%Q a Ha) as Hlt.
  pose proof (QleT'_to_Qle a b Hab) as Hle.
  apply Qle_to_QleT'.
  destruct a as [an ad]. destruct b as [bn bd].
  unfold Qlt, Qle in Hlt, Hle. cbn [Qnum Qden] in Hlt, Hle.
  unfold Qle, Qinv. cbn [Qnum Qden].
  destruct an; destruct bn; cbn in *; nia.
Qed.

(* sa_theta_leg_scaffold (pure Q conversion, genuine proof): 1/(2^{n+1} q_n)
   <= (1/2)^n = theta^n -- the closing register of the error end
   2^{-2n}/q_n <= theta^n (q_n >= 3^n >= 1); Set-layer qleT'_trans chain *)
Theorem sa_theta_leg_scaffold : forall n : nat,
  QleT' (Qinv ((q_pow (2 # 1)%Q (Datatypes.S n)
                 * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q))
        (q_pow (1 # 2)%Q n).
Proof.
  intro n.
  assert (Hle2 : (2 ^ n <= 2 ^ Datatypes.S n * bk_Qn_qtilde n)%nat).
  { rewrite Nat.pow_succ_r'.
    pose proof (NatLe_drop (3 ^ n) (bk_Qn_qtilde n) (bk_Qn_ge_3pow_nat n)) as H3.
    assert (Hp : (0 < 3 ^ n)%nat).
    { pose proof (bi_pow3_pos n) as Hpid.
      destruct (Nat.ltb 0 (3 ^ n)) eqn:E.
      - exact (proj1 (Nat.ltb_lt 0 (3 ^ n)) E).
      - inversion Hpid. }
    nia. }
  apply (qleT'_trans _ (Qinv (q_pow (2 # 1)%Q n))).
  - apply sa_Qinv_le.
    + exact (bi_q_pow_pos2 n).
    + apply (qleT'_trans _ ((Z.of_nat (2 ^ Datatypes.S n * bk_Qn_qtilde n) # 1)%Q)).
      * apply (qleT'_trans _ ((Z.of_nat (2 ^ n) # 1)%Q)).
        -- exact (qeq_imp_qle _ _ (bi_q_pow_2 n)).
        -- exact (bk_Qle_nat (2 ^ n)
                    (2 ^ Datatypes.S n * bk_Qn_qtilde n)
                    (NatLe_lift _ _ Hle2)).
      * apply (qeq_imp_qle ((Z.of_nat (2 ^ Datatypes.S n * bk_Qn_qtilde n) # 1)%Q)
                 ((q_pow (2 # 1)%Q (Datatypes.S n)
                   * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q)).
        apply qeq_imp_qeqT.
        rewrite <- (qeqT_imp_qeq _ _
                     (bk_Qmul_nat (2 ^ Datatypes.S n) (bk_Qn_qtilde n))).
        rewrite (qeqT_imp_qeq _ _ (bi_q_pow_2 (Datatypes.S n))).
        reflexivity.
  - exact (qeq_imp_qle _ _ (sa_theta_pow_inv2 n)).
Qed.

(* sa_clo_in_theta_window (genuine proof): clo_n < theta^n (n >= 1, premise
   carried by NatLe) -- the carrier strictly enters the theta register window
   (the 2^{-n} window of lne_B_lt_p2 converted through sa_theta_pow_inv2) *)
Theorem sa_clo_in_theta_window : forall n : nat, NatLe 1 n ->
  QltT (sa_clo n) (q_pow sa_theta n).
Proof.
  intros n Hn. pose proof (NatLe_drop 1 n Hn) as Hn1.
  apply (bi_qlt_eq (lne_B n) (Qinv (ln2i_p2 n)) (sa_clo n) (q_pow sa_theta n)).
  - exact (lne_B_lt_p2 n Hn1).
  - apply qeq_imp_qeqT. reflexivity.
  - unfold sa_theta. apply qeq_imp_qeqT.
    assert (Hpq : ln2i_p2 n == q_pow (2 # 1)%Q n).
    { rewrite (ln2i_p2_Z n). symmetry. exact (qeqT_imp_qeq _ _ (bi_q_pow_2 n)). }
    rewrite Hpq. exact (qeqT_imp_qeq _ _ (sa_theta_pow_inv2 n)).
Qed.

(* ============================================================ *)
(* Section 4: three independent pack pieces (legs 1-3 mounted)   *)
(* ============================================================ *)

(* sa_supply_head: the independent pack of legs 1-3 of the five supply limbs *)
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
(* Section 5: conditional interface (legs 4-5) + two-stage       *)
(*   assembly closure                                            *)
(* ============================================================ *)

(* sa_supply_rem: conditional interface, the B_n integer face plus the
   lower/upper real limbs -- the instantiation slot that dissolves once the
   identity corpus (I_n = 2^{n+1} q_n X - r_n, three subpieces in the
   header) arrives.  Semantics precise: non-emptiness of this interface is
   the existence of the theta-register Pade approximant sequence; this file
   makes no claim beyond that. *)
Definition sa_supply_rem : Set :=
  sigT (fun B : nat -> Z =>
    And (ln2b_line_lower sa_A B sa_clo)
        (ln2b_line_upper sa_A B sa_theta)).

(* sa_supply_assemble: two-stage assembly -- the mounted three-leg face plus
   the conditional interface imply the full supply type *)
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

(* sa_ln2_irrational: the two-stage closure of ln2 irrationality -- through
   the Ln2Bridge L4 source module ln2b_irrational_from_supply (real path via
   lic_irrational_criterion, zero bypass).  Statement face = the expanded
   form of the L4 conclusion face (all Set: sigT/And/QltT/real_lt). *)
Theorem sa_ln2_irrational : forall (Hm : sa_supply_rem) (q : Q),
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) ln2i_x
                         (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish))
       (real_const q)))).
Proof.
  intros Hm q.
  exact (ln2b_irrational_from_supply (sa_supply_assemble Hm) q).
Qed.

(* ============================================================ *)
(* Section 6: numerical anchors (vm_compute exact decisions:     *)
(*   A_1 = 2^2 q_1 = 12, A_2 = 2^3 q_2 = 104, clo_1 = 1/6,       *)
(*   theta^2 half-power anchor)                                  *)
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
(* Section 7: extraction re-check and assumption audit           *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction sa_ln2_irrational sa_supply_assemble
  sa_supply_three_legs sa_A_nonzeroT sa_clo_posT sa_clo_int
  sa_theta_leg_scaffold sa_clo_in_theta_window sa_norm_bridge
  sa_qpow_one_q sa_half_pow sa_theta_pow_inv2 sa_Qinv_le.
Print Assumptions sa_ln2_irrational.
Print Assumptions sa_supply_assemble.
Print Assumptions sa_supply_three_legs.
Print Assumptions sa_theta_leg_scaffold.
Print Assumptions sa_clo_in_theta_window.
Print Assumptions sa_A_nonzeroT.
Print Assumptions sa_qpow_one_q.
Print Assumptions sa_half_pow.
Print Assumptions sa_theta_pow_inv2.
Print Assumptions sa_Qinv_le.
