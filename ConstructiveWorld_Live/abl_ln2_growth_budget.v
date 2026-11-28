(* ===================================================================== *)
(* Module   : abl_ln2_growth_budget                                      *)
(* Mission.  Growth budget for the ln 2 chain: q~_n := bk_Qn_qtilde =    *)
(*   sum_{k<=n} C(n,k)^2*2^(n-k) (central Delannoy number, Beukers       *)
(*   denominator scale), A_n := 2^n*q~_n.  Delivers                      *)
(*   C(n,k) <= 2^n (double Pascal induction); q~_n <= 6^n (pointwise     *)
(*   C^2 <= 2^n*C, sum monotonicity, falling-power binomial identity     *)
(*   sum C(n,k)*2^(n-k) = 3^n); hence A_n <= 12^n <= 16^n and 6^n <=     *)
(*   A_n (band [6,12]; K < 4/3 refuted by A_1 = 6 > 4/3*A_0; only        *)
(*   L_n := lcm(1..n) <= n! is claimed for the L limb); anchors          *)
(*   A_n = 1/6/52/504/5136 (n=0..4); bridge 2^n*q~_nQ == A_nQ; assembly  *)
(*   budget A_n*(3/4)^(m-2n) <= (64/3)^n*(3/4)^m (rate kappa := 64/3).   *)
(* Dependencies.  Stdlib QArith/Arith/Arith.Factorial/ZArith/Lia;        *)
(*   S01_BaseRing (Id, NatLe), S02_CauchyComplete (QeqT/QleT'), S03_QExp *)
(*   (q_pow/q_pow_add/q_pow_wd/q_pow_nonneg), BeukersLists (bkC, bk_psd, *)
(*   bk_Qn_qtilde, bk_psd_mono, bk_psd_binom, bk_Qn_ge_3pow_nat,         *)
(*   bk_Qle_nat, bk_Qmul_nat, bk_q_pow_mul), HansonLcm (hl_le_t bridges, *)
(*   hl_pow2_ge1, hl_lcm_upto, hl_lcm_le_fact_t), abl_ln2_numer_int      *)
(*   (lni_qpow2_nat); upstream q-polynomial supply (q~_4 = 321 pin and   *)
(*   power congruence) re-derived here (lng2_qtilde4_pin; q_pow_wd).     *)
(* Constructivity.  All statement faces are Set-carried: nat order as    *)
(*   the decidable face hl_le_t, nat equality as Id, rational equality   *)
(*   as QeqT, rational order as QleT'; zero Prop statement face, zero    *)
(*   sigT embedding of a Prop component, zero classical logic.  Every    *)
(*   proof ends Defined, definitions transparent (no Qed: no pure-Prop   *)
(*   bridge stands alone; Prop reasoning -- ring/lia/stdlib Q lemmas --  *)
(*   stays in proof bodies); vm_compute only on the five anchors and the q~_4 pin. *)
(* Build.  rocq c -native-compiler no -q -Q <Set Live root> "" -Q <world *)
(*   root> "" abl_ln2_growth_budget.v (driver r237_compile.py).          *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith Arith.Arith Arith.Factorial ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import BeukersLists HansonLcm.
Require Import abl_ln2_numer_int.

Open Scope nat_scope.

(* ============================================================ *)
(* Section 0.  Micro bridge: Leibniz equality to the Set-level  *)
(* equality Id (proof-body plumbing only).                      *)
(* ============================================================ *)

Lemma lng2_eq_id : forall (A : Set) (x y : A), x = y -> Id x y.
Proof.
  intros A x y H. rewrite H. apply id_refl.
Defined.

(* ============================================================ *)
(* Section A.  Binomial power bound: C(n,k) <= 2^n (double      *)
(* Pascal induction).                                           *)
(* ============================================================ *)

Lemma lng2_bkC_le_pow2 : forall n k : nat, hl_le_t (bkC n k) (2 ^ n)%nat.
Proof.
  induction n as [| n IH]; intro k.
  - destruct k as [| k'].
    + cbn [bkC Nat.pow]. apply hl_le_to_le_t. apply Nat.le_refl.
    + cbn [bkC Nat.pow]. apply hl_le_to_le_t. apply Nat.le_0_l.
  - destruct k as [| k'].
    + cbn [bkC Nat.pow]. apply hl_le_to_le_t.
      pose proof (hl_le_t_to_le 1 (2 ^ n) (hl_pow2_ge1 n)). lia.
    + cbn [bkC]. rewrite Nat.pow_succ_r'.
      pose proof (hl_le_t_to_le (bkC n k') (2 ^ n) (IH k')) as H1.
      pose proof (hl_le_t_to_le (bkC n (Datatypes.S k')) (2 ^ n)
                    (IH (Datatypes.S k'))) as H2.
      apply hl_le_to_le_t. lia.
Defined.

(* ============================================================ *)
(* Section B.  q~_n <= 6^n: pointwise C(n,k)^2 <= 2^n*C(n,k),   *)
(* sum monotonicity, falling-power binomial identity.           *)
(* ============================================================ *)

(* Constant pull-out: bk_psd is linear under a constant factor. *)
Lemma lng2_psd_scale : forall (N c : nat) (f : nat -> nat),
  Id (bk_psd (fun k => c * f k) N) (c * bk_psd f N).
Proof.
  induction N as [| N IH]; intros c f.
  - apply lng2_eq_id. cbn [bk_psd]. lia.
  - apply lng2_eq_id. cbn [bk_psd].
    rewrite (id_eq_SI _ _ _ (IH c f)). ring.
Defined.

(* Power of a product: (a*b)^n = a^n * b^n. *)
Lemma lng2_pow_mul_l : forall a b n : nat, Id ((a * b) ^ n) (a ^ n * b ^ n).
Proof.
  intros a b n. induction n as [| n IH].
  - apply lng2_eq_id. reflexivity.
  - apply lng2_eq_id. rewrite !Nat.pow_succ_r'.
    rewrite (id_eq_SI _ _ _ IH). ring.
Defined.

(* Main jump: q~_n <= 2^n * 3^n = 6^n. *)
Lemma lng2_qtilde_le_6pow : forall n : nat, hl_le_t (bk_Qn_qtilde n) (6 ^ n)%nat.
Proof.
  intro n. unfold bk_Qn_qtilde.
  assert (Hpt : forall k : nat, NatLe (Datatypes.S k) (Datatypes.S n) ->
            NatLe (bkC n k * bkC n k) (2 ^ n * bkC n k)).
  { intro k. intro Hk. apply NatLe_lift. apply Nat.mul_le_mono_r.
    apply hl_le_t_to_le. apply lng2_bkC_le_pow2. }
  pose proof (bk_psd_mono (Datatypes.S n) (fun k => bkC n k * bkC n k)
              (fun k => 2 ^ n * bkC n k) Hpt) as Hmono.
  apply hl_le_to_le_t.
  transitivity (2 ^ n * bk_psd (fun k => bkC n k) (Datatypes.S n))%nat.
  - rewrite <- (id_eq_SI _ _ _
                  (lng2_psd_scale (Datatypes.S n) (2 ^ n) (fun k => bkC n k))).
    apply NatLe_drop. exact Hmono.
  - rewrite (id_eq_SI _ _ _ (bk_psd_binom n)).
    replace 6 with (2 * 3)%nat by lia.
    rewrite (id_eq_SI _ _ _ (lng2_pow_mul_l 2 3 n)). lia.
Defined.

(* ============================================================ *)
(* Section C.  A_n := 2^n * q~_n and the main bounds            *)
(* (12^n sharp grade, 16^n coarse grade).                       *)
(* ============================================================ *)

Definition lng2_An (n : nat) : nat := 2 ^ n * bk_Qn_qtilde n.

(* Monotonicity of powers under a base bound. *)
Lemma lng2_pow_le_mono_base : forall a b n : nat,
  hl_le_t a b -> hl_le_t (a ^ n) (b ^ n)%nat.
Proof.
  intros a b n H. apply hl_le_to_le_t. apply hl_le_t_to_le in H.
  induction n as [| n IH].
  - apply Nat.le_refl.
  - rewrite !Nat.pow_succ_r'. apply Nat.mul_le_mono. exact H. exact IH.
Defined.

Theorem lng2_An_le_12pow : forall n : nat, hl_le_t (lng2_An n) (12 ^ n)%nat.
Proof.
  intro n. unfold lng2_An. apply hl_le_to_le_t.
  transitivity (2 ^ n * 6 ^ n)%nat.
  - apply Nat.mul_le_mono_l. apply hl_le_t_to_le. apply lng2_qtilde_le_6pow.
  - replace 12 with (2 * 6)%nat by lia.
    rewrite (id_eq_SI _ _ _ (lng2_pow_mul_l 2 6 n)). lia.
Defined.

Theorem lng2_An_le_12pow_t : forall n : nat, hl_le_t (lng2_An n) (12 ^ n)%nat.
Proof. intro n. apply lng2_An_le_12pow. Defined.

(* Coarse grade: A_n <= 16^n through the 12^n grade. *)
Theorem lng2_An_le_16pow : forall n : nat, hl_le_t (lng2_An n) (16 ^ n)%nat.
Proof.
  intro n. apply hl_le_to_le_t.
  transitivity (12 ^ n)%nat.
  - apply hl_le_t_to_le. apply lng2_An_le_12pow.
  - apply hl_le_t_to_le. apply lng2_pow_le_mono_base.
    apply hl_le_to_le_t. lia.
Defined.

Theorem lng2_An_le_16pow_t : forall n : nat, hl_le_t (lng2_An n) (16 ^ n)%nat.
Proof. intro n. apply lng2_An_le_16pow. Defined.

(* Lower anchor: 6^n <= A_n (3^n <= q~_n from BeukersLists). *)
Theorem lng2_An_ge_6pow : forall n : nat, hl_le_t (6 ^ n) (lng2_An n)%nat.
Proof.
  intro n. unfold lng2_An. apply hl_le_to_le_t.
  replace 6 with (2 * 3)%nat by lia.
  rewrite (id_eq_SI _ _ _ (lng2_pow_mul_l 2 3 n)).
  apply Nat.mul_le_mono.
  - apply Nat.le_refl.
  - apply NatLe_drop. apply bk_Qn_ge_3pow_nat.
Defined.

(* ============================================================ *)
(* Section D.  Numeric anchors (n = 0..4) and their rational-   *)
(* face transports.                                             *)
(* ============================================================ *)

(* Pin q~_4 = 321, re-derived here from the upstream q-polynomial piece. *)
Theorem lng2_qtilde4_pin : Id (bk_Qn_qtilde 4) 321%nat.
Proof. vm_compute. apply id_refl. Defined.

Theorem lng2_An_anchor0 : Id (lng2_An 0) 1%nat.
Proof. vm_compute. apply id_refl. Defined.

Theorem lng2_An_anchor1 : Id (lng2_An 1) 6%nat.
Proof. vm_compute. apply id_refl. Defined.

Theorem lng2_An_anchor2 : Id (lng2_An 2) 52%nat.
Proof. vm_compute. apply id_refl. Defined.

Theorem lng2_An_anchor3 : Id (lng2_An 3) 504%nat.
Proof. vm_compute. apply id_refl. Defined.

(* anchor4 consumes the q~_4 pin above. *)
Theorem lng2_An_anchor4 : Id (lng2_An 4) 5136%nat.
Proof.
  unfold lng2_An.
  rewrite (id_eq_SI nat (bk_Qn_qtilde 4) 321 lng2_qtilde4_pin).
  vm_compute. apply id_refl.
Defined.

Lemma lng2_AnQ_of_nat : forall a b : nat, Id a b ->
  QeqT ((Z.of_nat a # 1)%Q) ((Z.of_nat b # 1)%Q).
Proof.
  intros a b H. apply qeq_imp_qeqT.
  rewrite (id_eq_SI nat a b H). reflexivity.
Defined.

Theorem lng2_AnQ_anchor1 : QeqT ((Z.of_nat (lng2_An 1) # 1)%Q) (6 # 1)%Q.
Proof. exact (lng2_AnQ_of_nat (lng2_An 1) 6 lng2_An_anchor1). Defined.

Theorem lng2_AnQ_anchor2 : QeqT ((Z.of_nat (lng2_An 2) # 1)%Q) (52 # 1)%Q.
Proof. exact (lng2_AnQ_of_nat (lng2_An 2) 52 lng2_An_anchor2). Defined.

Theorem lng2_AnQ_anchor3 : QeqT ((Z.of_nat (lng2_An 3) # 1)%Q) (504 # 1)%Q.
Proof. exact (lng2_AnQ_of_nat (lng2_An 3) 504 lng2_An_anchor3). Defined.

Theorem lng2_AnQ_anchor4 : QeqT ((Z.of_nat (lng2_An 4) # 1)%Q) (5136 # 1)%Q.
Proof. exact (lng2_AnQ_of_nat (lng2_An 4) 5136 lng2_An_anchor4). Defined.

(* ============================================================ *)
(* Section E.  Rational bridge and the assembly-form budget     *)
(* (composition rate kappa := 64/3).                            *)
(* ============================================================ *)

(* A_nQ == 2^n * q~_nQ, with q_pow (2#1) n carrying 2^n. *)
Theorem lng2_AnQ_eq : forall n : nat,
  QeqT ((q_pow (2 # 1)%Q n * (Z.of_nat (bk_Qn_qtilde n) # 1)%Q)%Q)
       ((Z.of_nat (lng2_An n) # 1)%Q).
Proof.
  intro n. unfold lng2_An. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (lni_qpow2_nat n)).
  exact (qeqT_imp_qeq _ _ (bk_Qmul_nat (2 ^ n) (bk_Qn_qtilde n))).
Defined.

(* Additivity of q_pow exponents (Set face; landed S03 content). *)
Lemma lng2_qpow_add : forall (x : Q) (a b : nat),
  QeqT (q_pow x (a + b)) ((q_pow x a * q_pow x b)%Q).
Proof. intros x a b. exact (q_pow_add x a b). Defined.

(* Integer-base power on the rational face. *)
Lemma lng2_qpow_Znat : forall (c n : nat),
  QeqT (q_pow ((Z.of_nat c # 1)%Q) n) ((Z.of_nat (c ^ n) # 1)%Q).
Proof.
  intros c n. apply qeq_imp_qeqT. induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow Nat.pow]. rewrite IH.
    exact (qeqT_imp_qeq _ _ (bk_Qmul_nat c (c ^ n))).
Defined.

(* QeqT to QleT' transport with a Prop-face premise (proof-body plumbing). *)
Lemma lng2_qeq_leT' : forall a b : Q, a == b -> QleT' a b.
Proof. intros a b H. apply qeq_leT'. apply qeq_imp_qeqT. exact H. Defined.

(* Composition-rate core: (64/3)^n * (3/4)^m == 12^n * (3/4)^(m-2n). *)
Lemma lng2_budget_rhs_eq : forall (n m : nat), hl_le_t (2 * n) m ->
  QeqT ((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m)%Q)
       (((Z.of_nat (12 ^ n) # 1)%Q * q_pow (3 # 4)%Q (m - 2 * n))%Q).
Proof.
  intros n m Hm. apply qeq_imp_qeqT.
  pose proof (hl_le_t_to_le (2 * n) m Hm) as Hmle.
  pose proof (qeqT_imp_qeq _ _ (lng2_qpow_add (3 # 4)%Q (2 * n) (m - 2 * n)))
    as Hsplit.
  replace (2 * n + (m - 2 * n)) with m in Hsplit by lia.
  pose proof (qeqT_imp_qeq _ _ (lng2_qpow_add (3 # 4)%Q n n)) as Hnn.
  replace (n + n) with (2 * n) in Hnn by lia.
  pose proof (qeqT_imp_qeq _ _ (lng2_qpow_Znat 12 n)) as H12.
  pose proof (qeqT_imp_qeq _ _
                (bk_q_pow_mul (64 # 3)%Q ((3 # 4) * (3 # 4))%Q n)) as Hpm.
  pose proof (qeqT_imp_qeq _ _ (bk_q_pow_mul (3 # 4)%Q (3 # 4)%Q n)) as H44.
  assert (Eb : ((64 # 3) * ((3 # 4) * (3 # 4)))%Q == (12 # 1)%Q) by reflexivity.
  pose proof (qeqT_imp_qeq _ _
                (q_pow_wd ((64 # 3) * ((3 # 4) * (3 # 4)))%Q (12 # 1)%Q n
                   (qeq_imp_qeqT _ _ Eb))) as Hwd.
  rewrite Hsplit. rewrite Hnn. rewrite <- H12. rewrite <- Hwd.
  rewrite Hpm. rewrite H44. ring.
Defined.

(* Assembly budget: A_n * (3/4)^(m-2n) <= (64/3)^n * (3/4)^m. *)
Theorem lng2_budget_compose : forall (n m : nat), hl_le_t (2 * n) m ->
  QleT' ((q_pow (3 # 4)%Q (m - 2 * n) * (Z.of_nat (lng2_An n) # 1)%Q)%Q)
        ((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m)%Q).
Proof.
  intros n m Hm.
  assert (Hwpos : QleT' 0%Q (q_pow (3 # 4)%Q (m - 2 * n))).
  { apply q_pow_nonneg. apply id_refl. }
  eapply qleT'_trans.
  - apply qleT'_mult_compat_l.
    + exact Hwpos.
    + apply bk_Qle_nat. apply NatLe_lift.
      apply hl_le_t_to_le. apply lng2_An_le_12pow.
  - apply lng2_qeq_leT'. symmetry.
    transitivity ((Z.of_nat (12 ^ n) # 1)%Q * q_pow (3 # 4)%Q (m - 2 * n))%Q.
    + apply (qeqT_imp_qeq _ _ (lng2_budget_rhs_eq n m Hm)).
    + apply Qmult_comm.
Defined.

(* ============================================================ *)
(* Section F.  L_n limb usage face (HansonLcm content).         *)
(* ============================================================ *)

Definition lng2_Ln (n : nat) : nat := hl_lcm_upto n.

Theorem lng2_Ln_le_fact : forall n : nat, hl_le_t (lng2_Ln n) (fact n)%nat.
Proof. intro n. unfold lng2_Ln. apply hl_lcm_le_fact_t. Defined.

Theorem lng2_Ln_le_fact_t : forall n : nat, hl_le_t (lng2_Ln n) (fact n)%nat.
Proof. intro n. apply lng2_Ln_le_fact. Defined.

(* ============================================================ *)
(* Honest boundary (explicit, no overclaiming).                 *)
(* ============================================================ *)
(* (1) A per-level constant K < 4/3 is impossible for A_n: the anchor   *)
(*     A_1 = 6 > 4/3 * A_0 refutes it (numeric fact, not a formal gap); *)
(*     the assembly budget uses the composition-rate form kappa := 64/3.*)
(* (2) L_n <= 4^n is not delivered: the nat layer of the standard      *)
(*     library has no prime library, and the Hanson L(n) < 3^n and      *)
(*     Nair-style L(n) <= 4^n bounds both need prime machinery          *)
(*     (enumeration, primorial <= 4^n bootstrap, psi decomposition);    *)
(*     the weakest landed bound L_n <= n! is delivered and explicitly   *)
(*     marked as not the 4^n grade.                                     *)
(* (3) The true per-level ratio approaches K through the anchor         *)
(*     sequence (x6, x8.67, x9.69, x10.19); sharpening K inside [6,12]  *)
(*     (a Vandermonde-convolution step on q~) is future work.           *)

(* ============================================================ *)
(* Assumption audit (one line per delivered lemma/theorem).     *)
(* ============================================================ *)

Print Assumptions lng2_eq_id.
Print Assumptions lng2_bkC_le_pow2.
Print Assumptions lng2_psd_scale.
Print Assumptions lng2_pow_mul_l.
Print Assumptions lng2_qtilde_le_6pow.
Print Assumptions lng2_pow_le_mono_base.
Print Assumptions lng2_An_le_12pow.
Print Assumptions lng2_An_le_12pow_t.
Print Assumptions lng2_An_le_16pow.
Print Assumptions lng2_An_le_16pow_t.
Print Assumptions lng2_An_ge_6pow.
Print Assumptions lng2_qtilde4_pin.
Print Assumptions lng2_An_anchor0.
Print Assumptions lng2_An_anchor1.
Print Assumptions lng2_An_anchor2.
Print Assumptions lng2_An_anchor3.
Print Assumptions lng2_An_anchor4.
Print Assumptions lng2_AnQ_of_nat.
Print Assumptions lng2_AnQ_anchor1.
Print Assumptions lng2_AnQ_anchor2.
Print Assumptions lng2_AnQ_anchor3.
Print Assumptions lng2_AnQ_anchor4.
Print Assumptions lng2_AnQ_eq.
Print Assumptions lng2_qpow_add.
Print Assumptions lng2_qpow_Znat.
Print Assumptions lng2_qeq_leT'.
Print Assumptions lng2_budget_rhs_eq.
Print Assumptions lng2_budget_compose.
Print Assumptions lng2_Ln_le_fact.
Print Assumptions lng2_Ln_le_fact_t.

Separate Extraction lng2_An.
