(* ===================================================================== *)
(* Module   : abl_ln2_conv_core                                          *)
(* Mission. Arithmetic convolution core for the rational lower bound      *)
(*   behind the irrationality of ln 2.  Layer 1: the integer heart        *)
(*   |p1*q2 - p2*q1| >= 1 gives 1 <= |p1/q1-p2/q2|*q1*q2 (cc_sep_core)    *)
(*   and 1/(q1*q2) <= |p1/q1-p2/q2| (cc_sep_div).  Layer 2: Bernoulli     *)
(*   bound 1 + n/4 <= (5/4)^n, base swap (4/5)^n == inverse((5/4)^n),     *)
(*   closed window (4/5)^(8q) < 1/(2q) for q >= 1 and pointwise form      *)
(*   (4/5)^(8*floor v) < 1/v.  Layer 3 engine: for a base real X and the  *)
(*   linear form |a*X - b| under an upper limb, a carrier lower limb and  *)
(*   two positivity premises, every rational u/v gets an explicit         *)
(*   positive constant c and index K with c <= |u/v - x_k| for k >= K;    *)
(*   the decidable split u*A_n0 = v*B_n0 (n0 = 8*floor v) yields          *)
(*   closed-Q branch constants.                                           *)
(* Dependencies. Stdlib QArith/Qabs/Setoid/Morphisms/Arith/ZArith/Lia;    *)
(*   S01_BaseRing (Set conjunction), S02_CauchyComplete (Real, real_le,   *)
(*   QeqT/QleT'/QltT bridges), S03_QExp (q_pow, real_abs),                *)
(*   UpReqLn2Irrational, UpReqIrrationalCriterion, Ln2Bridge              *)
(*   (ln2b_le_pt_slack/ln2b_line_q/ln2b_div_lt_of).                      *)
(* Constructivity. Conclusion faces fully Set-carried (QeqT/QleT'/QltT,   *)
(*   sigT with the Set conjunction of S01_BaseRing, real_le); premises    *)
(*   use decidable boolean faces, Prop mirroring only in Z-domain         *)
(*   disequalities (decidable via Z.eq_dec) and nat order; Qeq/Qle/Qlt    *)
(*   run inside proofs as scaffolding only.  Zero axioms, zero classical  *)
(*   logic, zero admits; witnesses are explicit closed Q/nat terms.       *)
(*   Qed marks proof-only bridges; the single data Definition cc_line is  *)
(*   transparent; vm_compute is confined to the anchor cc_band_anchor1.  *)
(* Build. rocq c -native-compiler no -q -Q <Set tree root> ""            *)
(*   abl_ln2_conv_core.v (single shot, this directory as workdir).       *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs Setoid Morphisms
  Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import UpReqLn2Irrational UpReqIrrationalCriterion.
Require Import Ln2Bridge.

Open Scope nat_scope.

(* Q carries field structure only; Qeq-face identities go through field. *)
Ltac cc_zring := field.
Ltac cc_zring_goal := field.

(* ============================================================ *)
(* Section 0: Qeq transport micro lemmas (Set-carried faces)    *)
(* ============================================================ *)

(* QleT' transport along a QeqT on the left. *)
Lemma cc_leT'_eq_l : forall x y z : Q, QeqT x y -> QleT' x z -> QleT' y z.
Proof.
  intros x y z H Hq. apply Qle_to_QleT'.
  apply (Qle_trans y x z).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    apply Qeq_sym. exact (qeqT_imp_qeq _ _ H).
  - apply QleT'_to_Qle. exact Hq.
Qed.

(* QleT' transport along a QeqT on the right. *)
Lemma cc_leT'_eq_r : forall x y z : Q, QeqT y z -> QleT' x y -> QleT' x z.
Proof.
  intros x y z H Hq. apply Qle_to_QleT'.
  apply (Qle_trans x y z).
  - apply QleT'_to_Qle. exact Hq.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    exact (qeqT_imp_qeq _ _ H).
Qed.

(* Positivity excludes zero; the Qeq face is used for rewriting. *)
Lemma cc_qinv_mul_cancel : forall z : Q, QltT 0 z -> QeqT (Qinv z * z) 1%Q.
Proof.
  intros z Hz. apply qeq_imp_qeqT.
  rewrite Qmult_comm. apply Qmult_inv_r.
  intro HC. pose proof (QltT_to_Qlt _ _ Hz) as Hlt.
  rewrite HC in Hlt. exact (Qlt_irrefl 0%Q Hlt).
Qed.

(* ============================================================ *)
(* Section 1: separation kernel for two distinct rationals      *)
(* ============================================================ *)

(* Integer heart: a nonzero integer w has |w| >= 1 (QleT' face). *)
Lemma cc_one_le_zabs : forall w : Z, w <> 0%Z -> QleT' 1%Q (Qabs (w # 1)%Q).
Proof.
  intros w Hw. apply Qle_to_QleT'.
  destruct w as [| p | p]; cbn [Qabs] in *;
    unfold Qle; cbn [Qnum Qden]; lia.
Qed.

(* Cross identity: (p1/q1 - p2/q2)*q1*q2 == p1*q2 - p2*q1. *)
Lemma cc_diff_cross : forall (p1 p2 : Z) (q1 q2 : positive),
  QeqT ((((p1 # q1)%Q - (p2 # q2)%Q) * ((Z.pos q1 # 1)%Q)
          * ((Z.pos q2 # 1)%Q))%Q)
        (((p1 * Z.pos q2 - p2 * Z.pos q1) # 1)%Q).
Proof.
  intros p1 p2 q1 q2. apply qeq_imp_qeqT.
  unfold Qmult, Qminus, Qplus, Qopp, Qeq. cbn [Qnum Qden Pos.mul]. lia.
Qed.

(* Product form: p1*q2 <> p2*q1 implies 1 <= |p1/q1 - p2/q2|*q1*q2. *)
Theorem cc_sep_core : forall (p1 p2 : Z) (q1 q2 : positive),
  (p1 * Z.pos q2 <> p2 * Z.pos q1)%Z ->
  QleT' 1%Q (Qabs (((p1 # q1)%Q - (p2 # q2)%Q)
                     * ((Z.pos q1 # 1)%Q) * ((Z.pos q2 # 1)%Q))%Q).
Proof.
  intros p1 p2 q1 q2 Hd.
  apply (cc_leT'_eq_r 1%Q
           (Qabs (((p1 * Z.pos q2 - p2 * Z.pos q1) # 1)%Q))
           (Qabs (((p1 # q1)%Q - (p2 # q2)%Q)
                    * ((Z.pos q1 # 1)%Q) * ((Z.pos q2 # 1)%Q)))%Q).
  - apply qeq_imp_qeqT. apply Qeq_sym. apply Qabs_wd.
    exact (qeqT_imp_qeq _ _ (cc_diff_cross p1 p2 q1 q2)).
  - apply cc_one_le_zabs. intro E. apply Hd. lia.
Qed.

(* Division form: p1*q2 <> p2*q1 implies 1/(q1*q2) <= |p1/q1 - p2/q2|. *)
Theorem cc_sep_div : forall (p1 p2 : Z) (q1 q2 : positive),
  (p1 * Z.pos q2 <> p2 * Z.pos q1)%Z ->
  QleT' (Qinv ((Z.pos (q1 * q2)) # 1)%Q)
        (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q).
Proof.
  intros p1 p2 q1 q2 Hd.
  pose proof (QleT'_to_Qle _ _ (cc_sep_core p1 p2 q1 q2 Hd)) as H1.
  (* |D*q1*q2| == |D|*(q1*q2)#1, via top-level Qeq assembly. *)
  assert (Habs_eq : Qabs (((p1 # q1)%Q - (p2 # q2)%Q)
                            * ((Z.pos q1 # 1)%Q) * ((Z.pos q2 # 1)%Q))
                    == Qabs ((p1 # q1)%Q - (p2 # q2)%Q)
                         * ((Z.pos (q1 * q2)) # 1)%Q).
  { transitivity ((Qabs (((p1 # q1)%Q - (p2 # q2)%Q) * ((Z.pos q1 # 1)%Q))
                     * Qabs ((Z.pos q2 # 1)%Q))%Q).
    - apply Qabs_Qmult.
    - assert (E12 : Qabs (((p1 # q1)%Q - (p2 # q2)%Q) * ((Z.pos q1 # 1)%Q))
                    == Qabs ((p1 # q1)%Q - (p2 # q2)%Q)
                         * Qabs ((Z.pos q1 # 1)%Q))
        by apply Qabs_Qmult.
      assert (E1 : Qabs ((Z.pos q1 # 1)%Q) == ((Z.pos q1 # 1)%Q)).
      { apply Qabs_pos. unfold Qle. cbn [Qnum Qden]. lia. }
      assert (E2 : Qabs ((Z.pos q2 # 1)%Q) == ((Z.pos q2 # 1)%Q)).
      { apply Qabs_pos. unfold Qle. cbn [Qnum Qden]. lia. }
      assert (Eq : (((Z.pos q1 # 1)%Q) * ((Z.pos q2 # 1)%Q))%Q
                   == ((Z.pos (q1 * q2)) # 1)%Q)
        by (unfold Qmult, Qeq; cbn [Qnum Qden Pos.mul]; lia).
      rewrite E12, E1, E2. rewrite <- Qmult_assoc, Eq. reflexivity. }
  assert (H1b : Qle 1%Q (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q
                             * ((Z.pos (q1 * q2)) # 1)%Q)).
  { apply (Qle_trans 1%Q
             (Qabs (((p1 # q1)%Q - (p2 # q2)%Q) * ((Z.pos q1 # 1)%Q)
                      * ((Z.pos q2 # 1)%Q)))%Q).
    - exact H1.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Habs_eq. }
  assert (HC0T : QltT 0 ((Z.pos (q1 * q2)) # 1)%Q).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (HCinvL : ((Z.pos (q1 * q2)) # 1)%Q
                     * Qinv ((Z.pos (q1 * q2)) # 1)%Q == 1%Q).
  { apply Qmult_inv_r.
    intro HC. pose proof (QltT_to_Qlt _ _ HC0T) as HC0.
    rewrite HC in HC0. exact (Qlt_irrefl 0%Q HC0). }
  assert (HQinvC0 : QltT 0 (Qinv ((Z.pos (q1 * q2)) # 1)%Q)).
  { apply Qlt_to_QltT. apply Qinv_lt_0_compat. apply QltT_to_Qlt. exact HC0T. }
  assert (Hle2 : QleT' ((Qinv ((Z.pos (q1 * q2)) # 1)%Q) * 1%Q)
                       ((Qinv ((Z.pos (q1 * q2)) # 1)%Q)
                          * (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q
                               * ((Z.pos (q1 * q2)) # 1)%Q))%Q).
  { apply (qleT'_mult_compat_l 1%Q
             (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q
                * ((Z.pos (q1 * q2)) # 1)%Q)
             (Qinv ((Z.pos (q1 * q2)) # 1)%Q)
             HQinvC0 (Qle_to_QleT' _ _ H1b)). }
  apply (cc_leT'_eq_l ((Qinv ((Z.pos (q1 * q2)) # 1)%Q) * 1%Q)
           (Qinv ((Z.pos (q1 * q2)) # 1)%Q)
           (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q)).
  - apply qeq_imp_qeqT. apply Qmult_1_r.
  - apply (cc_leT'_eq_r ((Qinv ((Z.pos (q1 * q2)) # 1)%Q) * 1%Q)
             ((Qinv ((Z.pos (q1 * q2)) # 1)%Q)
                * (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q
                     * ((Z.pos (q1 * q2)) # 1)%Q))%Q
             (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q)).
    + apply qeq_imp_qeqT.
      rewrite Qmult_assoc. rewrite (Qmult_comm (Qinv ((Z.pos (q1 * q2)) # 1)%Q)
                                         (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q)).
      rewrite <- Qmult_assoc.
      rewrite (Qmult_comm (Qinv ((Z.pos (q1 * q2)) # 1)%Q)
                                 ((Z.pos (q1 * q2)) # 1)%Q).
      rewrite HCinvL. apply Qmult_1_r.
    + exact Hle2.
Qed.

(* ============================================================ *)
(* Section 2: explicit window for the (4/5) powers              *)
(* ============================================================ *)

(* Bernoulli lower bound: 1 + n/4 <= (5/4)^n (induction on QleT'). *)
Lemma cc_bernoulli : forall n : nat,
  QleT' (((1 # 1)%Q + (Z.of_nat n # 1)%Q * (1 # 4)%Q)%Q) (q_pow (5 # 4)%Q n).
Proof.
  induction n as [| n IH].
  - cbn [q_pow]. change (Z.of_nat 0) with 0%Z.
    apply qeq_leT'. apply qeq_imp_qeqT.
    unfold Qeq, Qnum, Qmult, Qplus, Qminus, Qopp.
    cbn [Qnum Qden Pos.mul]. ring.
  - cbn [Nat.add]. cbn [q_pow].
    apply (qleT'_trans
             (((1 # 1)%Q + (Z.of_nat (Datatypes.S n) # 1)%Q * (1 # 4)%Q)%Q)
             (((5 # 4)%Q * ((1 # 1)%Q + (Z.of_nat n # 1)%Q * (1 # 4)%Q))%Q)
             (((5 # 4)%Q * q_pow (5 # 4)%Q n)%Q)).
    + apply Qle_to_QleT'.
      replace (Z.of_nat (Datatypes.S n)) with (Z.of_nat n + 1)%Z
        by (rewrite Nat2Z.inj_succ; lia).
      unfold Qle.
      cbn [Qnum Qden Qmult Qplus Qminus Qopp Qinv Qdiv Pos.mul].
      lia.
    + assert (Hth : QleT' 0 (5 # 4)%Q).
      { apply qltT_leT'. apply Qlt_to_QltT. unfold Qlt. cbn. lia. }
      apply (qleT'_mult_compat_l
               (((1 # 1)%Q + (Z.of_nat n # 1)%Q * (1 # 4)%Q)%Q)
               (q_pow (5 # 4)%Q n) (5 # 4)%Q Hth IH).
Qed.

(* Base swap: (4/5)^n == inverse((5/4)^n). *)
Lemma cc_qpow_swap : forall n : nat,
  QeqT (q_pow (4 # 5)%Q n) (Qinv (q_pow (5 # 4)%Q n)).
Proof.
  induction n as [| n IH].
  - apply qeq_imp_qeqT. reflexivity.
  - cbn [q_pow]. apply qeq_imp_qeqT. rewrite Qinv_mult_distr.
    rewrite (qeqT_imp_qeq _ _ IH). reflexivity.
Qed.

(* Index accounting: (8*q)*(1/4) == 2*q. *)
Lemma cc_q8_index : forall q : nat,
  QeqT (((Z.of_nat (8 * q) # 1)%Q * (1 # 4)%Q)%Q) ((Z.of_nat (2 * q) # 1)%Q).
Proof.
  intro q. apply qeq_imp_qeqT. unfold Qmult, Qeq. cbn [Qnum Qden Pos.mul].
  rewrite (Nat2Z.inj_mul 8 q), (Nat2Z.inj_mul 2 q). nia.
Qed.

(* Division by one: 1/z == z^-1 for an integer base z. *)
Lemma cc_div1_inv : forall z : Z,
  QeqT (((1 # 1)%Q / ((z # 1)%Q))%Q) (Qinv ((z # 1)%Q)).
Proof.
  intro z. apply qeq_imp_qeqT. unfold Qdiv.
  destruct z as [| p | p]; cbn [Qnum Qden Qinv Qmult];
    unfold Qeq, Qmult; cbn [Qnum Qden Pos.mul]; lia.
Qed.

(* QltT transport along QeqT, left and right. *)
Lemma cc_qltT_transfer_l : forall x y z : Q, QeqT x y -> QltT y z -> QltT x z.
Proof.
  intros x y z Hxy Hyz. apply Qlt_to_QltT.
  apply (Qle_lt_trans x y z).
  - apply QleT'_to_Qle. apply qeq_le. exact Hxy.
  - apply QltT_to_Qlt. exact Hyz.
Qed.

Lemma cc_qltT_transfer_r : forall x y z : Q, QeqT y z -> QltT x y -> QltT x z.
Proof.
  intros x y z Hyz Hxy. apply Qlt_to_QltT.
  apply (Qlt_le_trans x y z).
  - apply QltT_to_Qlt. exact Hxy.
  - apply QleT'_to_Qle. apply qeq_le. exact Hyz.
Qed.

(* Inverse injectivity on positives: 0 < u, 0 < v and v^-1 == u^-1
   give u == v (both sides multiplied by v*u, no ring registration). *)
Lemma cc_qinv_inj : forall u v : Q,
  QltT 0 u -> QltT 0 v -> QeqT (Qinv v) (Qinv u) -> QeqT u v.
Proof.
  intros u v Hu0 Hv0 h.
  pose proof (QltT_to_Qlt _ _ Hu0) as Hu.
  pose proof (QltT_to_Qlt _ _ Hv0) as Hv.
  pose proof (qeqT_imp_qeq _ _ h) as hq.
  assert (Ev : (Qinv v * v)%Q == 1%Q).
  { apply qeqT_imp_qeq. apply cc_qinv_mul_cancel. exact Hv0. }
  assert (Eu : (Qinv u * u)%Q == 1%Q).
  { apply qeqT_imp_qeq. apply cc_qinv_mul_cancel. exact Hu0. }
  assert (Hstep : (Qinv v * (v * u))%Q == (Qinv u * (v * u))%Q)
    by (rewrite hq; reflexivity).
  apply qeq_imp_qeqT.
  apply (Qeq_trans u (Qinv v * (v * u))%Q v).
  - apply (Qeq_trans u (1 * u)%Q (Qinv v * (v * u))%Q).
    + apply Qeq_sym. apply Qmult_1_l.
    + apply (Qeq_trans (1 * u)%Q ((Qinv v * v) * u)%Q (Qinv v * (v * u))%Q).
      * rewrite <- Ev. reflexivity.
      * rewrite <- Qmult_assoc. reflexivity.
  - apply (Qeq_trans (Qinv v * (v * u))%Q (Qinv u * (v * u))%Q v).
    + exact Hstep.
    + apply (Qeq_trans (Qinv u * (v * u))%Q (Qinv u * (u * v))%Q v).
      * rewrite (Qmult_comm v u). reflexivity.
      * rewrite Qmult_assoc. rewrite Eu. apply Qmult_1_l.
Qed.

(* Strict inverse order: 0 < u and u < v give v^-1 < u^-1 (the strict
   branch is discharged by the inverse injectivity above, no LPO). *)
Lemma cc_qinv_lt : forall u v : Q, QltT 0 u -> QltT u v -> QltT (Qinv v) (Qinv u).
Proof.
  intros u v Hu Hv. apply Qlt_to_QltT.
  pose proof (QltT_to_Qlt _ _ Hv) as Hltuv.
  assert (Hv0 : Qlt 0 v).
  { apply (Qlt_trans 0%Q u v).
    - apply QltT_to_Qlt. exact Hu.
    - exact Hltuv. }
  assert (Hle : Qle (Qinv v) (Qinv u)).
  { apply ln2i_inv_le.
    - apply QltT_to_Qlt. exact Hu.
    - apply Qlt_le_weak. exact Hltuv. }
  destruct (Qle_lt_or_eq (Qinv v) (Qinv u) Hle) as [Hlt | Heq].
  - exact Hlt.
  - exfalso. apply (Qlt_irrefl v).
    assert (HuvT : QeqT u v).
    { apply cc_qinv_inj.
      - exact Hu.
      - apply Qlt_to_QltT. exact Hv0.
      - apply qeq_imp_qeqT. exact Heq. }
    pose proof (qeqT_imp_qeq _ _ HuvT) as Huv.
    rewrite Huv in Hltuv. exact Hltuv.
Qed.

(* Closed window: 1 <= q gives (4/5)^(8q) < 1/(2q). *)
Theorem cc_band : forall q : nat, 1 <= q ->
  QltT (q_pow (4 # 5)%Q (8 * q))
       (((1 # 1)%Q / ((Z.of_nat (2 * q) # 1)%Q))%Q).
Proof.
  intros q Hq.
  pose proof (QleT'_to_Qle _ _ (cc_bernoulli (8 * q))) as Hb.
  assert (Hinner : ((1 # 1)%Q + (Z.of_nat (8 * q) # 1)%Q * (1 # 4)%Q)%Q
                   == ((1 # 1)%Q + (Z.of_nat (2 * q) # 1)%Q)%Q).
  { pose proof (qeqT_imp_qeq _ _ (cc_q8_index q)) as H8.
    rewrite H8. reflexivity. }
  assert (Hb2 : Qle (((1 # 1)%Q + (Z.of_nat (2 * q) # 1)%Q)%Q)
                    (q_pow (5 # 4)%Q (8 * q))).
  { apply (Qle_trans _ (((1 # 1)%Q + (Z.of_nat (8 * q) # 1)%Q * (1 # 4)%Q))%Q).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      apply Qeq_sym. exact Hinner.
    - exact Hb. }
  assert (Hstep : QltT ((Z.of_nat (2 * q) # 1)%Q)
                       (((1 # 1)%Q + (Z.of_nat (2 * q) # 1)%Q)%Q)).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden Qplus]. lia. }
  assert (HbandP : QltT ((Z.of_nat (2 * q) # 1)%Q)
                        (q_pow (5 # 4)%Q (8 * q)))
    by (apply (qltT_leT'_ltT _ _ _ Hstep (Qle_to_QleT' _ _ Hb2))).
  assert (Hu0 : Qlt 0 ((Z.of_nat (2 * q) # 1)%Q)).
  { unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (Ediv : ((1 # 1)%Q / ((Z.of_nat (2 * q) # 1)%Q))%Q
                 == Qinv ((Z.of_nat (2 * q) # 1)%Q))
    by exact (qeqT_imp_qeq _ _ (cc_div1_inv (Z.of_nat (2 * q)))).
  pose proof (cc_qinv_lt ((Z.of_nat (2 * q) # 1)%Q)
              (q_pow (5 # 4)%Q (8 * q)) (Qlt_to_QltT _ _ Hu0) HbandP) as Hinv.
  apply (cc_qltT_transfer_l (q_pow (4 # 5)%Q (8 * q))
           (Qinv (q_pow (5 # 4)%Q (8 * q)))
           (((1 # 1)%Q / ((Z.of_nat (2 * q) # 1)%Q))%Q)).
  - exact (cc_qpow_swap (8 * q)).
  - apply (cc_qltT_transfer_r (Qinv (q_pow (5 # 4)%Q (8 * q)))
             (Qinv ((Z.of_nat (2 * q) # 1)%Q))
             (((1 # 1)%Q / ((Z.of_nat (2 * q) # 1)%Q))%Q)).
    + apply qeq_imp_qeqT. apply Qeq_sym. exact Ediv.
    + exact Hinv.
Qed.

(* Inverse of a positive denominator: (v#1)^-1 == (1#v). *)
Lemma cc_qinv_pair : forall v : positive, QeqT (Qinv ((Z.pos v # 1)%Q)) ((1 # v)%Q).
Proof.
  intro v. apply qeq_imp_qeqT. cbn [Qinv]. destruct v; reflexivity.
Qed.

(* Pointwise window: (4/5)^(8*floor v) < 1/v for every positive v
   (chain v <= 2*floor v < 1 + 2*floor v <= (5/4)^(8*floor v), then
   reverse the inverses). *)
Theorem cc_band_v : forall v : positive,
  QltT (q_pow (4 # 5)%Q (8 * Z.to_nat (Z.pos v))) ((1 # v)%Q).
Proof.
  intro v.
  pose proof (QleT'_to_Qle _ _ (cc_bernoulli (8 * Z.to_nat (Z.pos v)))) as Hb.
  assert (Hinner : ((Z.of_nat (8 * Z.to_nat (Z.pos v)) # 1)%Q * (1 # 4)%Q)%Q
                   == ((Z.of_nat (2 * Z.to_nat (Z.pos v)) # 1)%Q)).
  { pose proof (qeqT_imp_qeq _ _ (cc_q8_index (Z.to_nat (Z.pos v)))) as H8.
    rewrite H8. reflexivity. }
  assert (Hb2 : QleT' ((Z.of_nat (2 * Z.to_nat (Z.pos v)) # 1)%Q)
                       (q_pow (5 # 4)%Q (8 * Z.to_nat (Z.pos v)))).
  { apply Qle_to_QleT'.
    apply (Qle_trans ((Z.of_nat (2 * Z.to_nat (Z.pos v)) # 1)%Q)
             (((1 # 1)%Q + (Z.of_nat (2 * Z.to_nat (Z.pos v)) # 1)%Q)%Q)).
    - unfold Qle. cbn [Qnum Qden Qmult Qplus]. lia.
    - apply (Qle_trans _ (((1 # 1)%Q
                             + (Z.of_nat (8 * Z.to_nat (Z.pos v)) # 1)%Q
                                * (1 # 4)%Q))%Q).
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        rewrite <- Hinner. reflexivity.
      + exact Hb. }
  assert (Hstep : QltT ((Z.pos v # 1)%Q)
                        ((Z.of_nat (2 * Z.to_nat (Z.pos v)) # 1)%Q)).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden].
    assert (Hz := Z2Nat.id (Z.pos v) ltac:(lia)).
    lia. }
  assert (HbandP : QltT ((Z.pos v # 1)%Q)
                         (q_pow (5 # 4)%Q (8 * Z.to_nat (Z.pos v))))
    by (apply (qltT_leT'_ltT _ _ _ Hstep Hb2)).
  assert (Hu0 : Qlt 0 ((Z.pos v # 1)%Q)).
  { unfold Qlt. cbn [Qnum Qden]. lia. }
  pose proof (cc_qinv_lt ((Z.pos v # 1)%Q)
              (q_pow (5 # 4)%Q (8 * Z.to_nat (Z.pos v)))
              (Qlt_to_QltT _ _ Hu0) HbandP) as Hinv.
  apply (cc_qltT_transfer_l (q_pow (4 # 5)%Q (8 * Z.to_nat (Z.pos v)))
           (Qinv (q_pow (5 # 4)%Q (8 * Z.to_nat (Z.pos v))))
           ((1 # v)%Q)).
  - exact (cc_qpow_swap (8 * Z.to_nat (Z.pos v))).
  - apply (cc_qltT_transfer_r (Qinv (q_pow (5 # 4)%Q (8 * Z.to_nat (Z.pos v))))
             (Qinv ((Z.pos v # 1)%Q))
             ((1 # v)%Q)).
    + exact (cc_qinv_pair v).
    + exact Hinv.
Qed.

(* Numeric anchor: at q = 1, (4/5)^8 < 1/2 (vm_compute pin). *)
Theorem cc_band_anchor1 : QltT (q_pow (4 # 5)%Q 8) ((1 # 2)%Q).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* Section 3: the two-branch convolution engine                 *)
(* ============================================================ *)

(* The integer linear form |a*X - b| as a real carrier over a base real X. *)
Definition cc_line (X : Real) (a b : Z) : Real :=
  real_abs (real_plus (real_mult (real_const ((a # 1)%Q)) X)
                      (real_opp (real_const ((b # 1)%Q)))).

(* Pointwise reading: the k-th reading of cc_line is |a*x_k - b|. *)
Lemma cc_line_pt : forall (X : Real) (a b : Z) (k : nat),
  QeqT (projT1 (cc_line X a b) k)
       (Qabs (((a # 1)%Q * projT1 X k - ((b # 1)%Q))%Q)).
Proof.
  intros X a b k. unfold cc_line.
  assert (Ha : projT1 (real_abs (real_plus (real_mult (real_const ((a # 1)%Q)) X)
                                 (real_opp (real_const ((b # 1)%Q))))) k
              == Qabs (projT1 (real_plus (real_mult (real_const ((a # 1)%Q)) X)
                                 (real_opp (real_const ((b # 1)%Q)))) k))
    by (apply qeqT_imp_qeq; apply real_abs_proj).
  assert (Hb : projT1 (real_plus (real_mult (real_const ((a # 1)%Q)) X)
                        (real_opp (real_const ((b # 1)%Q)))) k
              == projT1 (real_mult (real_const ((a # 1)%Q)) X) k
                 + projT1 (real_opp (real_const ((b # 1)%Q))) k)
    by (apply qeqT_imp_qeq; apply real_plus_proj).
  assert (Hc : projT1 (real_mult (real_const ((a # 1)%Q)) X) k
              == projT1 (real_const ((a # 1)%Q)) k * projT1 X k)
    by (apply qeqT_imp_qeq; apply real_mult_proj).
  assert (Hd : projT1 (real_opp (real_const ((b # 1)%Q))) k
              == (- projT1 (real_const ((b # 1)%Q)) k)%Q)
    by (apply qeqT_imp_qeq; apply real_opp_proj).
  assert (He1 : projT1 (real_const ((a # 1)%Q)) k == ((a # 1)%Q))
    by (apply qeqT_imp_qeq; apply real_const_proj).
  assert (He2 : projT1 (real_const ((b # 1)%Q)) k == ((b # 1)%Q))
    by (apply qeqT_imp_qeq; apply real_const_proj).
  apply qeq_imp_qeqT. rewrite Ha, Hb, Hc, Hd, He1, He2. reflexivity.
Qed.

(* Hit identity: a*q == b gives |a*t - b| == |a|*|t - q|. *)
Lemma cc_hit_abs : forall (a b : Z) (t q : Q),
  QeqT (((a # 1)%Q * q - ((b # 1)%Q))%Q) 0%Q ->
  QeqT (Qabs (((a # 1)%Q * t - ((b # 1)%Q))%Q))
       (Qabs ((a # 1)%Q) * Qabs ((t - q)%Q)%Q).
Proof.
  intros a b t q Hhit.
  pose proof (qeqT_imp_qeq _ _ Hhit) as Hh.
  assert (HB : ((b # 1)%Q) == ((a # 1)%Q * q)%Q).
  { apply Qeq_sym.
    apply (Qeq_trans ((a # 1)%Q * q)%Q
                     (((a # 1)%Q * q - ((b # 1)%Q)) + ((b # 1)%Q))%Q
                     ((b # 1)%Q)).
    - field.
    - rewrite Hh. apply Qplus_0_l. }
  apply qeq_imp_qeqT.
  transitivity (Qabs ((a # 1)%Q * (t - q)%Q)).
  - apply Qabs_wd.
    apply (Qeq_trans ((a # 1)%Q * t - ((b # 1)%Q))%Q
                     ((a # 1)%Q * t - (a # 1)%Q * q)%Q
                     ((a # 1)%Q * (t - q)%Q)).
    + rewrite HB. reflexivity.
    + assert (Hdistr : ((a # 1)%Q * t - (a # 1)%Q * q)%Q
                       == ((a # 1)%Q * (t - q))%Q) by field.
      exact Hdistr.
  - rewrite Qabs_Qmult. reflexivity.
Qed.

(* Triangle split: |a*q - b| <= |a|*|q - x_k| + |a*x_k - b| (k-th reading). *)
Lemma cc_tri : forall (X : Real) (a b : Z) (q : Q) (k : nat),
  QleT' (Qabs (((a # 1)%Q * q - ((b # 1)%Q))%Q))
        (Qabs ((a # 1)%Q) * Qabs ((q - projT1 X k)%Q)
         + projT1 (cc_line X a b) k)%Q.
Proof.
  intros X a b q k.
  assert (Hsplit : (((a # 1)%Q * q - ((b # 1)%Q))%Q
                    == ((a # 1)%Q * (q - projT1 X k)
                        + ((a # 1)%Q * projT1 X k - ((b # 1)%Q)))%Q)) by cc_zring.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs ((a # 1)%Q * (q - projT1 X k)
                             + ((a # 1)%Q * projT1 X k - ((b # 1)%Q)))%Q)).
  - assert (Hw : Qabs (((a # 1)%Q * q - ((b # 1)%Q))%Q)
                 == Qabs ((a # 1)%Q * (q - projT1 X k)
                          + ((a # 1)%Q * projT1 X k - ((b # 1)%Q)))%Q)
      by (apply Qabs_wd; exact Hsplit).
    rewrite Hw. apply Qle_refl.
  - pose proof (Qabs_triangle ((a # 1)%Q * (q - projT1 X k))
                  ((a # 1)%Q * projT1 X k - ((b # 1)%Q))) as HT.
    assert (HE : (Qabs ((a # 1)%Q * (q - projT1 X k))
                  + Qabs ((a # 1)%Q * projT1 X k - ((b # 1)%Q)))%Q
                 == (Qabs ((a # 1)%Q) * Qabs ((q - projT1 X k)%Q)
                     + projT1 (cc_line X a b) k)%Q).
    { rewrite Qabs_Qmult.
      rewrite (qeqT_imp_qeq _ _ (cc_line_pt X a b k)). reflexivity. }
    apply (Qle_trans _ _ _ HT). rewrite HE. apply Qle_refl.
Qed.

(* Two-branch engine: under the upper limb (line <= decay carrier), the
   carrier lower limb (clo <= line) and the two positivity premises, every
   rational u/v obtains an explicit positive constant c and an index K
   with c <= |u/v - x_k| for all k >= K.  The split on u*A_n0 = v*B_n0
   with n0 = 8*floor v is decidable (Z.eq_dec); hit branch constant
   (clo_n0/2)*|A_n0|^-1, miss branch constant ((1/v - (4/5)^n0)/2)*
   |A_n0|^-1; both are closed Q terms. *)
Theorem cc_engine : forall (X : Real) (A B : nat -> Z) (clo : nat -> Q),
  (forall n : nat, real_le (cc_line X (A n) (B n))
                           (real_const (q_pow (4 # 5)%Q n))) ->
  (forall n : nat, real_le (real_const (clo n))
                           (cc_line X (A n) (B n))) ->
  (forall n : nat, QltT 0 (clo n)) ->
  (forall n : nat, QltT 0 (Qabs ((A n) # 1)%Q)) ->
  forall (u : Z) (v : positive),
    sigT (fun c : Q => And (QltT 0 c)
      (sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
        QleT' c (Qabs (((u # v)%Q - projT1 X k)%Q))))).
Proof.
  intros X A B clo Hup Hlo Hclop HA u v.
  set (n0 := 8 * Z.to_nat (Z.pos v)).
  assert (Hband1v : QltT (q_pow (4 # 5)%Q n0) ((1 # v)%Q))
    by (apply cc_band_v).
  destruct (Z.eq_dec (u * A n0) (Z.pos v * B n0)) as [Hhit | Hmiss].
  - (* Hit branch: the approximation pair coincides with u/v; the carrier
       lower limb supplies the positive separation constant. *)
    assert (HhitQ : QeqT (((A n0) # 1)%Q * ((u # v)%Q) - ((B n0) # 1)%Q)%Q
                         0%Q).
    { pose proof (qeqT_imp_qeq _ _ (ln2b_line_q (A n0) (B n0) u v)) as HL.
      apply qeq_imp_qeqT. rewrite HL. rewrite Hhit.
      unfold Qeq. cbn [Qnum Qden Pos.mul]. lia. }
    assert (Heps0 : QltT 0 ((clo n0)%Q * (1 # 2)%Q)%Q).
    { apply qmult_ltT_0_compat.
      - exact (Hclop n0).
      - apply Qlt_to_QltT. unfold Qlt. cbn. lia. }
    destruct (ln2b_le_pt_slack (real_const (clo n0))
                (cc_line X (A n0) (B n0)) (Hlo n0)
                ((clo n0)%Q * (1 # 2)%Q)%Q Heps0) as [K HK].
    exists (((clo n0)%Q * (1 # 2)%Q) * Qinv (Qabs ((A n0) # 1)%Q))%Q.
    split.
    + apply qmult_ltT_0_compat.
      * exact Heps0.
      * apply Qlt_to_QltT. apply Qinv_lt_0_compat.
        exact (QltT_to_Qlt _ _ (HA n0)).
    + exists K. intros k Hk.
      pose proof (HK k Hk) as HKq0.
      pose proof (QltT_to_Qlt _ _ HKq0) as HKq.
      pose proof (qeqT_imp_qeq _ _ (real_const_proj (clo n0) k)) as Hrc.
      rewrite Hrc in HKq.
      (* clo < line + clo/2 gives clo - clo/2 < line (additive cancel). *)
      assert (Hred : Qlt ((clo n0)%Q - (clo n0)%Q * (1 # 2)%Q)
                          (projT1 (cc_line X (A n0) (B n0)) k)%Q).
      { apply (lic_qlt_add_r_cancel_r ((clo n0)%Q - (clo n0)%Q * (1 # 2)%Q)
                 (projT1 (cc_line X (A n0) (B n0)) k)
                 ((clo n0)%Q * (1 # 2)%Q)%Q).
        assert (Eclo : ((clo n0)%Q
                       == (((clo n0)%Q - (clo n0)%Q * (1 # 2)%Q)
                             + (clo n0)%Q * (1 # 2)%Q))%Q) by cc_zring.
        rewrite <- Eclo. exact HKq. }
      assert (Hhalf : Qlt ((clo n0)%Q * (1 # 2)%Q)
                           (projT1 (cc_line X (A n0) (B n0)) k)%Q).
      { assert (Er : ((clo n0)%Q - (clo n0)%Q * (1 # 2)%Q)%Q
                     == ((clo n0)%Q * (1 # 2)%Q)%Q) by cc_zring.
        rewrite Er in Hred. exact Hred. }
      pose proof (qeqT_imp_qeq _ _ (cc_line_pt X (A n0) (B n0) k)) as Hlp.
      rewrite Hlp in Hhalf.
      pose proof (qeqT_imp_qeq _ _
                   (cc_hit_abs (A n0) (B n0) (projT1 X k) ((u # v)%Q) HhitQ))
        as Hha.
      rewrite Hha in Hhalf.
      apply Qle_to_QleT'. apply Qlt_le_weak.
      rewrite (Qabs_Qminus ((u # v)%Q) (projT1 X k)).
      apply QltT_to_Qlt.
      exact (ln2b_div_lt_of ((clo n0)%Q * (1 # 2)%Q)
               (Qabs ((A n0) # 1)%Q)
               (Qabs ((projT1 X k - (u # v)%Q)%Q)) (HA n0) Hhalf).
  - (* Miss branch: integer heart + triangle split + closed window. *)
    assert (Hw0 : (u * A n0 - Z.pos v * B n0 <> 0)%Z)
      by (intro E; apply Hmiss; lia).
    assert (Hq : (((A n0) # 1)%Q * ((u # v)%Q) - ((B n0) # 1)%Q)%Q
                 == (((u * A n0 - Z.pos v * B n0) # v)%Q))
      by exact (qeqT_imp_qeq _ _ (ln2b_line_q (A n0) (B n0) u v)).
    (* 1/v <= |w/v| by the integer heart on w = u*A_n0 - v*B_n0. *)
    assert (Honev : Qle ((1 # v)%Q)
                      (Qabs (((u * A n0 - Z.pos v * B n0) # v)%Q))).
    { unfold Qle, Qabs. cbn [Qabs Qnum Qden].
      pose proof (proj2 (Z.abs_pos (u * A n0 - Z.pos v * B n0)) Hw0). nia. }
    (* Window margin W := 1/v - (4/5)^n0 > 0, margin half delta := W/2. *)
    assert (HW0 : Qlt 0 (((1 # v)%Q - q_pow (4 # 5)%Q n0)%Q)).
    { apply lic_qlt_0_minus. exact (QltT_to_Qlt _ _ Hband1v). }
    assert (Hdelta0 : QltT 0 (((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))%Q).
    { apply qmult_ltT_0_compat.
      - apply Qlt_to_QltT. exact HW0.
      - apply Qlt_to_QltT. unfold Qlt. cbn. lia. }
    destruct (ln2b_le_pt_slack (cc_line X (A n0) (B n0))
                (real_const (q_pow (4 # 5)%Q n0)) (Hup n0)
                (((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))%Q Hdelta0)
      as [K HK].
    exists ((((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))
              * Qinv (Qabs ((A n0) # 1)%Q))%Q.
    split.
    + apply qmult_ltT_0_compat.
      * exact Hdelta0.
      * apply Qlt_to_QltT. apply Qinv_lt_0_compat.
        exact (QltT_to_Qlt _ _ (HA n0)).
    + exists K. intros k Hk.
      pose proof (HK k Hk) as HKq0.
      pose proof (QltT_to_Qlt _ _ HKq0) as HKq.
      pose proof (qeqT_imp_qeq _ _
                   (real_const_proj (q_pow (4 # 5)%Q n0) k)) as Hrc.
      rewrite Hrc in HKq.
      assert (Hmid : ((q_pow (4 # 5)%Q n0)
                       + ((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))%Q
                     == ((1 # v)%Q
                         - ((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))%Q)
        by cc_zring.
      rewrite Hmid in HKq.
      pose proof (QleT'_to_Qle _ _ (cc_tri X (A n0) (B n0) ((u # v)%Q) k))
        as Htri.
      assert (Hleg1 : Qle (Qabs (((u * A n0 - Z.pos v * B n0) # v)%Q))
                       (Qabs (((A n0) # 1)%Q * ((u # v)%Q)
                                - ((B n0) # 1)%Q))%Q).
      { assert (Hw : Qabs (((u * A n0 - Z.pos v * B n0) # v)%Q)
                     == Qabs (((A n0) # 1)%Q * ((u # v)%Q)
                              - ((B n0) # 1)%Q))
          by (apply Qabs_wd; apply Qeq_sym; exact Hq).
        rewrite Hw. apply Qle_refl. }
      assert (Hleg2 : Qle (Qabs (((A n0) # 1)%Q * ((u # v)%Q)
                                   - ((B n0) # 1)%Q))
                       (Qabs ((A n0) # 1)%Q
                          * Qabs (((u # v)%Q - projT1 X k)%Q)
                          + projT1 (cc_line X (A n0) (B n0)) k)%Q)
        by exact Htri.
      pose proof (Qle_trans _ _ _ Honev
                   (Qle_trans _ _ _ Hleg1 Hleg2)) as Hchain1.
      assert (Hchain2 : Qlt (Qabs ((A n0) # 1)%Q
                              * Qabs (((u # v)%Q - projT1 X k)%Q)
                              + projT1 (cc_line X (A n0) (B n0)) k)%Q
                             (Qabs ((A n0) # 1)%Q
                              * Qabs (((u # v)%Q - projT1 X k)%Q)
                              + ((1 # v)%Q
                                 - ((1 # v)%Q - q_pow (4 # 5)%Q n0)
                                   * (1 # 2)))%Q)
        by (apply (lic_qlt_add_l (Qabs ((A n0) # 1)%Q
                                   * Qabs (((u # v)%Q - projT1 X k)%Q)));
            exact HKq).
      assert (Hpre : Qlt ((1 # v)%Q)
                      (Qabs ((A n0) # 1)%Q
                         * Qabs (((u # v)%Q - projT1 X k)%Q)
                         + ((1 # v)%Q
                            - ((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2)))%Q)
        by (apply (Qle_lt_trans (1 # v)%Q
                    (Qabs ((A n0) # 1)%Q
                       * Qabs (((u # v)%Q - projT1 X k)%Q)
                       + projT1 (cc_line X (A n0) (B n0)) k)%Q);
            assumption).
      assert (Hchain : Qlt (((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))
                         (Qabs ((A n0) # 1)%Q
                            * Qabs (((u # v)%Q - projT1 X k)%Q))).
      { pose proof (proj1 (Qlt_minus_iff (1 # v)%Q
                             (Qabs ((A n0) # 1)%Q
                                * Qabs (((u # v)%Q - projT1 X k)%Q)
                                + ((1 # v)%Q
                                   - ((1 # v)%Q - q_pow (4 # 5)%Q n0)
                                     * (1 # 2)))%Q)
                     Hpre) as Hm.
        assert (Hring : ((Qabs ((A n0) # 1)%Q
                            * Qabs (((u # v)%Q - projT1 X k)%Q)
                            + ((1 # v)%Q
                               - ((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2)))
                          - (1 # v)%Q)%Q
                        == (Qabs ((A n0) # 1)%Q
                              * Qabs (((u # v)%Q - projT1 X k)%Q)
                              - ((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))%Q)
          by cc_zring.
        rewrite Hring in Hm.
        assert (Hring2 : ((((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))
                            + (Qabs ((A n0) # 1)%Q
                                 * Qabs (((u # v)%Q - projT1 X k)%Q)
                                 - ((1 # v)%Q - q_pow (4 # 5)%Q n0)
                                   * (1 # 2)))%Q
                         == (Qabs ((A n0) # 1)%Q
                               * Qabs (((u # v)%Q - projT1 X k)%Q)))
          by cc_zring.
        apply (lic_qlt_comp_r
                 _ (Qabs ((A n0) # 1)%Q
                      * Qabs (((u # v)%Q - projT1 X k)%Q))
                 (((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))
                 Hring2 (lic_qlt_lt_add_r _ _ Hm)).
      }
      apply Qle_to_QleT'. apply Qlt_le_weak.
      exact (QltT_to_Qlt _ _
               (ln2b_div_lt_of (((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))
                  (Qabs ((A n0) # 1)%Q)
                  (Qabs (((u # v)%Q - projT1 X k)%Q)) (HA n0) Hchain)).
Qed.

(* ============================================================ *)
(* Extractability witness (Set-carried faces)                   *)
(* ============================================================ *)

Separate Extraction cc_sep_div cc_band cc_line.

(* ============================================================ *)
(* Premise audit: each stated face must print closed.           *)
(* ============================================================ *)

Print Assumptions cc_leT'_eq_l.
Print Assumptions cc_leT'_eq_r.
Print Assumptions cc_qinv_mul_cancel.
Print Assumptions cc_one_le_zabs.
Print Assumptions cc_diff_cross.
Print Assumptions cc_sep_core.
Print Assumptions cc_sep_div.
Print Assumptions cc_bernoulli.
Print Assumptions cc_qpow_swap.
Print Assumptions cc_q8_index.
Print Assumptions cc_div1_inv.
Print Assumptions cc_qltT_transfer_l.
Print Assumptions cc_qltT_transfer_r.
Print Assumptions cc_qinv_inj.
Print Assumptions cc_qinv_lt.
Print Assumptions cc_band.
Print Assumptions cc_qinv_pair.
Print Assumptions cc_band_v.
Print Assumptions cc_band_anchor1.
Print Assumptions cc_line_pt.
Print Assumptions cc_hit_abs.
Print Assumptions cc_tri.
Print Assumptions cc_engine.
