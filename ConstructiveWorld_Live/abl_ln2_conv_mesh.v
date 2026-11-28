(* ===================================================================== *)
(* abl_ln2_conv_mesh.v -- convolution kernel x baseline-column assembly. *)
(* Mission.  Join the two-sided convolution engine for the Beukers-type  *)
(*   ln2 sequence x_k = sum_{j<=k} 1/(j*2^j) (denominators divide        *)
(*   L_n = lcm(1..n), Hanson 1972) with the modified numerators A_n/B_n: *)
(*   growth fact n <= n^n and L_n*qtilde_n <= (6n)^n; decay budget       *)
(*   4/5 < 1 and (4/5)^n < 1 (n >= 1); positivity of |A_n|; cm_supply    *)
(*   (clo positivity, clo_n <= |A_n*x - B_n| <= (4/5)^n) with its        *)
(*   five-legged form and projection; cm_bound: explicit positive c and  *)
(*   index K, c <= |u/v - x_k| for k >= K; n = 1 anchors; the identity   *)
(*   leg stays an honest open slot of cm_supply.                         *)
(* Dependencies.  Stdlib QArith.QArith QArith.Qabs Arith.Arith           *)
(*   Arith.Factorial ZArith.ZArith Lia; S01_BaseRing (Set pairing And),  *)
(*   S02_CauchyComplete (Real, real_const, real_le, QltT/QeqT/QleT'),    *)
(*   S03_QExp (q_pow), UpReqLn2Irrational (ln2i_x), Ln2Bridge,           *)
(*   BeukersLists, HansonLcm (hl_le_t two-way bridges); abl_ln2_tail_    *)
(*   bound (lnt_leT'_eq_r), abl_ln2_theta_total (lnt4_theta_budget_lt,   *)
(*   lng2_qtilde_le_6pow), abl_ln2_assembly (lna_* data, anchors),       *)
(*   abl_ln2_conv_core (cc_engine, cc_line, cc_band_anchor1).            *)
(* References.  ConstructiveWorld-Main module abl_ln2_conv_mesh (names   *)
(*   carried verbatim); Hanson, Canad. Math. Bull. 15 (1972) 33-37.      *)
(* Constructivity.  Every delivered statement face is Set-carried        *)
(*   (QltT/QeqT/QleT', leb-carried hl_le_t, real_le, sigT over And); no  *)
(*   Prop statement face; the only Prop atoms inside Set carriers are    *)
(*   the nat antecedents (1 <= n)/(K <= k), mirroring the consumed       *)
(*   faces lnt4_theta_budget_lt and cc_engine; all items end Defined     *)
(*   (no Qed), vm_compute only at the n = 1 pin, Prop reasoning stays    *)
(*   inside proof bodies.                                                *)
(* Build.  rocq c -native-compiler no -q -Q <Set Live root> "" -Q <world root> "" abl_ln2_conv_mesh.v (single shot). *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith
  Arith.Factorial ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import UpReqLn2Irrational Ln2Bridge.
Require Import BeukersLists HansonLcm.
Require Import abl_ln2_tail_bound abl_ln2_theta_total
  abl_ln2_assembly abl_ln2_conv_core.

Open Scope nat_scope.

(* ============================================================ *)
(* Section 1: the unconditional growth account.                  *)
(* ============================================================ *)

(* Factorial is bounded by the base power: n! <= n^n (induction). *)
Theorem cm_fact_le_pow : forall n : nat, hl_le_t (fact n) (n ^ n).
Proof.
  intro n. apply hl_le_to_le_t.
  induction n as [| n IH].
  - cbn. lia.
  - cbn [fact]. rewrite Nat.pow_succ_r'.
    apply Nat.mul_le_mono.
    + apply Nat.le_refl.
    + eapply Nat.le_trans.
      * exact IH.
      * apply Nat.pow_le_mono_l. lia.
Defined.

(* Canonical numerator growth: L_n*qtilde_n <= (6n)^n
   (chain: L_n <= n!, n! <= n^n, qtilde_n <= 6^n, power split). *)
Theorem cm_A_le : forall n : nat,
  hl_le_t (hl_lcm_upto n * bk_Qn_qtilde n) ((6 * n) ^ n).
Proof.
  intro n. apply hl_le_to_le_t.
  assert (Hsplit : forall m a b : nat, (a * b) ^ m = a ^ m * b ^ m).
  { intros m a b. induction m as [| m IH].
    - reflexivity.
    - rewrite !Nat.pow_succ_r'. rewrite IH.
      rewrite <- (Nat.mul_assoc a b (a ^ m * b ^ m)).
      rewrite <- (Nat.mul_assoc a (a ^ m) (b * b ^ m)).
      rewrite (Nat.mul_assoc b (a ^ m) (b ^ m)).
      rewrite (Nat.mul_comm b (a ^ m)).
      rewrite <- (Nat.mul_assoc (a ^ m) b (b ^ m)).
      reflexivity. }
  pose proof (hl_le_t_to_le (hl_lcm_upto n) (fact n) (hl_lcm_le_fact n)) as HL.
  pose proof (hl_le_t_to_le (fact n) (n ^ n) (cm_fact_le_pow n)) as HF.
  pose proof (lng2_qtilde_le_6pow n) as HQ.
  rewrite (Hsplit n 6 n).
  eapply Nat.le_trans.
  - apply Nat.mul_le_mono. exact HL. exact HQ.
  - eapply Nat.le_trans.
    + apply Nat.mul_le_mono. exact HF. apply Nat.le_refl.
    + rewrite (Nat.mul_comm (n ^ n) (6 ^ n)). apply Nat.le_refl.
Defined.

(* ============================================================ *)
(* Section 2: the decay budget.                                  *)
(* ============================================================ *)

(* The ratio is below one: 4/5 < 1. *)
Theorem cm_theta_lt1 : QltT (4 # 5)%Q (1 # 1)%Q.
Proof. apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia. Defined.

(* Budget face: (4/5)^n < 1 for n >= 1. *)
Theorem cm_theta_budget_lt1 : forall n : nat,
  (1 <= n)%nat -> QltT (q_pow (4 # 5)%Q n) (1 # 1)%Q.
Proof. intros n Hn. exact (lnt4_theta_budget_lt n Hn). Defined.

(* ============================================================ *)
(* Section 3: canonical numerator data.                          *)
(* ============================================================ *)

(* Positivity of the modified numerator face: 0 < |A_n|
   (transported along the canonical identities). *)
Theorem cm_A_pos : forall n : nat, QltT 0 (Qabs ((lna_Amod n) # 1)%Q).
Proof.
  intro n.
  pose proof (fst (snd lna_head_three_legs) n) as Hf.
  apply QltT_to_Qlt in Hf.
  assert (Heq : (Qabs ((lna_Aface n) # 1)%Q)
                == (Qabs ((lna_Amod n) # 1)%Q)).
  { apply Qabs_wd. eapply Qeq_trans.
    - apply qeqT_imp_qeq. apply lna_Aface_eq.
    - apply qeqT_imp_qeq. apply lna_lA_z. }
  rewrite Heq in Hf.
  apply Qlt_to_QltT. exact Hf.
Defined.

(* ============================================================ *)
(* Section 4: the supply types.                                  *)
(* ============================================================ *)

(* Delivered supply type: three legs (positivity of clo, lower bound
   clo_n <= line, upper bound line <= (4/5)^n).  The single open slot
   is the lower/upper pair carrying the identity leg. *)
Definition cm_supply : Set :=
  sigT (fun clo : nat -> Q =>
    And (forall n : nat, QltT 0 (clo n))
      (And (forall n : nat, real_le (real_const (clo n))
                                    (ln2b_line lna_Amod lna_Bmod n))
           (forall n : nat, real_le (ln2b_line lna_Amod lna_Bmod n)
                                    (real_const (q_pow (4 # 5)%Q n))))).

(* Five-legged supply type (the ratio face and the numerator positivity
   are discharged unconditionally by Sections 2/3; three legs remain). *)
Definition cm_pade_supply : Set :=
  sigT (fun clo : nat -> Q =>
    And (QltT (4 # 5)%Q (1 # 1)%Q)
      (And (forall n : nat, QltT 0 (Qabs ((lna_Amod n) # 1)%Q))
        (And (forall n : nat, QltT 0 (clo n))
          (And (forall n : nat, real_le (real_const (clo n))
                                        (ln2b_line lna_Amod lna_Bmod n))
               (forall n : nat, real_le (ln2b_line lna_Amod lna_Bmod n)
                                        (real_const (q_pow (4 # 5)%Q n))))))).

(* Projection: the ratio and positivity legs are dropped (Sections 2/3). *)
Theorem cm_pade_of_supply : cm_pade_supply -> cm_supply.
Proof.
  intros [clo [_ [_ [Hclop [Hlo Hup]]]]].
  exists clo. split.
  - exact Hclop.
  - split.
    + exact Hlo.
    + exact Hup.
Defined.

(* ============================================================ *)
(* Section 5: the separation final.                              *)
(* ============================================================ *)

(* Under cm_supply, for every rational u/v an explicit positive constant
   c and index K with c <= |u/v - x_k| for all k >= K.  The engine line
   cc_line ln2b_X (A n) (B n) and the bridge line ln2b_line A B n agree
   definitionally, so the bounds transfer by conversion alone; the
   engine reading is transported along the baseline projection. *)
Theorem cm_bound : forall (Hs : cm_supply) (u : Z) (v : positive),
  sigT (fun c : Q => And (QltT 0 c)
    (sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
      QleT' c (Qabs (((u # v)%Q - ln2i_x k)%Q))))).
Proof.
  intros [clo [Hclo [Hlo Hup]]] u v.
  assert (Hup' : forall n : nat,
    real_le (cc_line ln2b_X (lna_Amod n) (lna_Bmod n))
            (real_const (q_pow (4 # 5)%Q n))).
  { intro n. exact (Hup n). }
  assert (Hlo' : forall n : nat,
    real_le (real_const (clo n))
            (cc_line ln2b_X (lna_Amod n) (lna_Bmod n))).
  { intro n. exact (Hlo n). }
  destruct (cc_engine ln2b_X lna_Amod lna_Bmod clo Hup' Hlo' Hclo
             cm_A_pos u v) as [c [Hc0 [K HK]]].
  exists c. split.
  - exact Hc0.
  - exists K. intros k Hk.
    apply (lnt_leT'_eq_r c
             (Qabs (((u # v)%Q - projT1 ln2b_X k)%Q))
             (Qabs (((u # v)%Q - ln2i_x k)%Q))).
    + apply Qabs_wd.
      rewrite (qeqT_imp_qeq _ _ (ln2b_X_proj k)). reflexivity.
    + exact (HK k Hk).
Defined.

(* ============================================================ *)
(* Section 6: the numeric anchors.                               *)
(* ============================================================ *)

(* Band anchor at window q = 1: (4/5)^8 < 1/2. *)
Theorem cm_anchor_band1 : QltT (q_pow (4 # 5)%Q 8) ((1 # 2)%Q).
Proof. exact cc_band_anchor1. Defined.

(* Growth anchor: L_1*qtilde_1 <= 6. *)
Theorem cm_anchor_growth1 :
  hl_le_t (hl_lcm_upto 1 * bk_Qn_qtilde 1) ((6 * 1) ^ 1).
Proof. apply hl_le_to_le_t. vm_compute. lia. Defined.

(* Leading-term anchors: A_1 = 3 and B_1 = 4/2. *)
Theorem cm_anchor_chain1 :
  And (QeqT (3 # 1)%Q ((lna_Amod 1) # 1)%Q)
      (QeqT (4 # 2)%Q ((lna_Bmod 1) # 1)%Q).
Proof. split.
  - exact lna_A1_anchor.
  - exact lna_B1_anchor.
Defined.

(* ============================================================ *)
(* Extraction and closedness audit.                              *)
(* ============================================================ *)

Separate Extraction cm_bound cm_pade_of_supply.

Print Assumptions cm_fact_le_pow.
Print Assumptions cm_A_le.
Print Assumptions cm_theta_lt1.
Print Assumptions cm_theta_budget_lt1.
Print Assumptions cm_A_pos.
Print Assumptions cm_pade_of_supply.
Print Assumptions cm_bound.
Print Assumptions cm_anchor_band1.
Print Assumptions cm_anchor_growth1.
Print Assumptions cm_anchor_chain1.
