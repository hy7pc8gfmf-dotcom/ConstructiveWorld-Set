(* ========================================================================== *)
(* UpReqBanachLimUniq.v — Banach-algebra limit uniqueness and product limits. *)
(*                                                                            *)
(* Mission.  Three statements on the Set-carried Banach-algebra interface:    *)
(*   bxuq_lim_diff_small (two limits of one sequence have arbitrarily small   *)
(*   difference norm), bxuq_lim_uniq (limits coincide, discharged through     *)
(*   the separation field bxce_sep), and bxuq_prod_lim_joint (the product     *)
(*   sequence of exponential partial sums converges to the product of the     *)
(*   limit partial sums, through bxadd_bmult_lim).                            *)
(*                                                                            *)
(* Dependencies.  S01_BaseRing, S02_CauchyComplete, S03_QExp,                 *)
(*   UpReqBanachExp (interface BanachAlg with explicit carrier arguments),    *)
(*   UpReqBanachClassExt (extension class BanachAlgExt), UpReqBanachExpAdd    *)
(*   (bxadd_bmult_lim); Stdlib QArith, Lia, Arith.                            *)
(*                                                                            *)
(* References.  Uniqueness of limits in metric spaces and joint convergence   *)
(*   of the Cauchy product of the exponential series, in the Banach-algebra   *)
(*   setting; statement names carried over verbatim from the baseline         *)
(*   module of ConstructiveWorld-Main.                                        *)
(*                                                                            *)
(* Constructivity.  Every statement face is carried by Set: comparisons use   *)
(*   the decidable gates QltT/QleT'/QeqT, the carrier equality bae is a       *)
(*   Set-valued relation, limit witnesses arrive in sigT, and nat bounds      *)
(*   use NatLe.  Qeq premises are gated through QeqT; Stdlib rational         *)
(*   comparison premises are fed only inside proof bodies.  All items close   *)
(*   with Qed; the build is axiom-free.                                       *)
(*                                                                            *)
(* Build.  rocq c -native-compiler no -Q . "" UpReqBanachLimUniq.v compiles   *)
(*   cleanly (exit 0) against the compiled dependency tree.                   *)
(* ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachClassExt.
Require Import UpReqBanachExpAdd.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Q-layer toolkit: statement faces Set-carried; the rational    *)
(* comparison premises stay inside proof bodies.                 *)
(* ============================================================ *)

(* Nonzero gate for the radius constant: the Set-carried negation  *)
(* Not (QeqT 2 0), shaped after the in-tree qltT_not_eq_zero gate  *)
(* (Not lands in Empty_set, per S01_BaseRing); proof bodies        *)
(* recover the Stdlib Qeq premise through qeqT_imp_qeq.            *)
Lemma bxuq_2_neq_0 : Not (QeqT 2 0).
Proof.
  intros Hz.
  apply (False_rect Empty_set).
  apply qeqT_imp_qeq in Hz.
  vm_compute in Hz.
  discriminate.
Qed.

(* Radius positivity: QltT 0 e implies QltT 0 (e / 2). *)
Lemma bxuq_half_pos : forall e : Q, QltT 0 e -> QltT 0 (e / 2).
Proof.
  intros e H.
  assert (Hz2 : ~ (2 == 0)%Q)
    by (intro Hzz;
        exact (match bxuq_2_neq_0 (qeq_imp_qeqT 2 0 Hzz) with end)).
  assert (Hm : (e / 2 * 2)%Q == e%Q).
  { unfold Qdiv.
    rewrite <- Qmult_assoc.
    rewrite (Qmult_comm (Qinv 2) 2).
    rewrite (Qmult_inv_r 2 Hz2).
    apply Qmult_1_r. }
  apply Qlt_to_QltT.
  apply (proj1 (Qmult_lt_r 0 (e / 2) 2 (QltT_to_Qlt 0 2 qltT_0_2))).
  rewrite Qmult_0_l.
  setoid_replace (e / 2 * 2)%Q with e%Q by (exact Hm).
  exact (QltT_to_Qlt 0 e H).
Qed.

(* Half-sum identity: QeqT (e / 2 + e / 2) e; the Qdiv unfold must *)
(* be explicit, and the Qeq-level accounting stays in the body.    *)
Lemma bxuq_half_sum_eq : forall e : Q, QeqT (e / 2 + e / 2)%Q e%Q.
Proof.
  intros e.
  assert (Hz2 : ~ (2 == 0)%Q)
    by (intro Hzz;
        exact (match bxuq_2_neq_0 (qeq_imp_qeqT 2 0 Hzz) with end)).
  assert (He : (e / 2 + e / 2)%Q == e%Q).
  { unfold Qdiv.
    rewrite <- (Qmult_plus_distr_l e e (Qinv 2)).
    assert (Hee : (e + e)%Q == (2 * e)%Q) by ring.
    rewrite Hee.
    rewrite <- Qmult_assoc.
    rewrite (Qmult_comm 2 (e * Qinv 2)%Q).
    rewrite <- Qmult_assoc.
    rewrite (Qmult_comm (Qinv 2) 2).
    rewrite (Qmult_inv_r 2 Hz2).
    apply Qmult_1_r. }
  exact (qeq_imp_qeqT _ _ He).
Qed.

(* Radius addition: QltT x (e / 2) and QltT y (e / 2) imply        *)
(* QltT (x + y) e.                                                 *)
Lemma bxuq_sum_half_lt : forall x y e : Q,
  QltT x (e / 2) -> QltT y (e / 2) -> QltT (x + y) e.
Proof.
  intros x y e Hx Hy.
  apply Qlt_to_QltT.
  assert (Hs : (e / 2 + e / 2)%Q == e%Q)
    by (exact (qeqT_imp_qeq _ _ (bxuq_half_sum_eq e))).
  assert (H1 : (x + y < e / 2 + e / 2)%Q)
    by (apply Qplus_lt_compat; apply QltT_to_Qlt; assumption).
  rewrite Hs in H1.
  exact H1.
Qed.

(* ============================================================ *)
(* Additive-group toolkit over the generic Banach-algebra        *)
(* interface (no extension fields consumed).                     *)
(* ============================================================ *)

(* Right-add the zero point then equal: bae (a + (-b)) 0 implies   *)
(* bae a b (two bopp_unique steps).                                *)
Lemma bxuq_add_opp_zero_eq : forall (BA : Set) (bae : BA -> BA -> Set)
    (B : BanachAlg BA bae) (a b : BA),
  bae (@bplus BA bae B a (@bopp BA bae B b)) (@bzero BA bae B) -> bae a b.
Proof.
  intros BA bae B a b H.
  eapply (@bae_trans BA bae B).
  - exact (@bopp_unique BA bae B a (@bopp BA bae B b) H).
  - apply (@bae_sym BA bae B).
    exact (@bopp_unique BA bae B b (@bopp BA bae B b) (@bplus_opp BA bae B b)).
Qed.

(* Difference split: bae (a - c) ((a - b) + (b - c)), the          *)
(* algebraic premise of the triangle inequality, spelled with      *)
(* bplus/bopp.                                                     *)
Lemma bxuq_diff_split : forall (BA : Set) (bae : BA -> BA -> Set)
    (B : BanachAlg BA bae) (a b c : BA),
  bae (@bplus BA bae B a (@bopp BA bae B c))
    (@bplus BA bae B (@bplus BA bae B a (@bopp BA bae B b))
                     (@bplus BA bae B b (@bopp BA bae B c))).
Proof.
  intros BA bae B a b c.
  assert (H1 : bae (@bplus BA bae B (@bopp BA bae B b) b) (@bzero BA bae B)).
  { exact (@bae_trans BA bae B _ _ _ (@bplus_comm BA bae B (@bopp BA bae B b) b)
                        (@bplus_opp BA bae B b)). }
  assert (H3 : bae (@bplus BA bae B (@bopp BA bae B b)
                                (@bplus BA bae B b (@bopp BA bae B c)))
                      (@bopp BA bae B c)).
  { eapply (@bae_trans BA bae B).
    { exact (@bplus_assoc BA bae B (@bopp BA bae B b) b (@bopp BA bae B c)). }
    eapply (@bae_trans BA bae B).
    { exact (@bplus_wd_l BA bae B (@bplus BA bae B (@bopp BA bae B b) b)
                          (@bzero BA bae B) (@bopp BA bae B c) H1). }
    exact (@bplus_zero_l BA bae B (@bopp BA bae B c)). }
  assert (H4 : bae (@bplus BA bae B a (@bplus BA bae B (@bopp BA bae B b)
                                              (@bplus BA bae B b (@bopp BA bae B c))))
                      (@bplus BA bae B a (@bopp BA bae B c))).
  { exact (@bplus_wd_r BA bae B _ _ a H3). }
  eapply (@bae_trans BA bae B).
  { exact (@bae_sym BA bae B _ _ H4). }
  exact (@bplus_assoc BA bae B a (@bopp BA bae B b)
                     (@bplus BA bae B b (@bopp BA bae B c))).
Qed.

(* Negated difference bridge: bae (a - b) (-(b - a)); turns the    *)
(* u - l witness shape of blim into the l1 - u shape of the split  *)
(* algebra, as the special case of the split with a := c composed  *)
(* with bopp_unique.                                               *)
Lemma bxuq_diff_opp : forall (BA : Set) (bae : BA -> BA -> Set)
    (B : BanachAlg BA bae) (a b : BA),
  bae (@bplus BA bae B a (@bopp BA bae B b))
         (@bopp BA bae B (@bplus BA bae B b (@bopp BA bae B a))).
Proof.
  intros BA bae B a b.
  apply (@bopp_unique BA bae B (@bplus BA bae B a (@bopp BA bae B b))
                       (@bplus BA bae B b (@bopp BA bae B a))).
  eapply (@bae_trans BA bae B).
  { exact (@bae_sym BA bae B _ _ (bxuq_diff_split BA bae B a b a)). }
  exact (@bplus_opp BA bae B a).
Qed.

(* ============================================================ *)
(* Small-norm main lemma: two limits of one sequence differ by a  *)
(* norm below any positive radius (triangle plus Q accounting,    *)
(* generic in the interface).                                     *)
(* ============================================================ *)

Lemma bxuq_lim_diff_small : forall (BA : Set) (bae : BA -> BA -> Set)
    (B : BanachAlg BA bae) (u : nat -> BA) (l1 l2 : BA),
  blim BA bae B u l1 -> blim BA bae B u l2 ->
  forall eps : Q, QltT 0 eps ->
  QltT (@bnorm BA bae B (@bplus BA bae B l1 (@bopp BA bae B l2))) eps.
Proof.
  intros BA bae B u l1 l2 H1 H2 eps Heps.
  assert (He2 : QltT 0 (eps / 2)%Q) by (apply bxuq_half_pos; exact Heps).
  destruct (H1 (eps / 2)%Q He2) as [N1 HN1].
  destruct (H2 (eps / 2)%Q He2) as [N2 HN2].
  assert (Ha : QltT (@bnorm BA bae B (@bplus BA bae B (u (Nat.max N1 N2))
                                       (@bopp BA bae B l1))) (eps / 2)%Q).
  { exact (HN1 (Nat.max N1 N2) (NatLe_lift _ _ (Nat.le_max_l N1 N2))). }
  assert (Hb : QltT (@bnorm BA bae B (@bplus BA bae B (u (Nat.max N1 N2))
                                       (@bopp BA bae B l2))) (eps / 2)%Q).
  { exact (HN2 (Nat.max N1 N2) (NatLe_lift _ _ (Nat.le_max_r N1 N2))). }
  (* The blim witness has the u - l shape while the split algebra    *)
  (* gives the l1 - u shape; reorient through diff_opp and           *)
  (* bnorm_opp (Id-face rewrite inside the QltT goal).               *)
  assert (Hal : QltT (@bnorm BA bae B (@bplus BA bae B l1
                                 (@bopp BA bae B (u (Nat.max N1 N2)))))
                     (eps / 2)%Q).
  { pose proof (@bnorm_wd BA bae B _ _
                  (bxuq_diff_opp BA bae B l1 (u (Nat.max N1 N2)))) as HWd.
    eapply (QeqT_Qlt_bool_cong _ _ _ (qeqT_sym_hw _ _ HWd)).
    rewrite (@bnorm_opp BA bae B (@bplus BA bae B (u (Nat.max N1 N2))
                                        (@bopp BA bae B l1))).
    exact Ha. }
  (* Norm chain: the difference norm is bounded by the split sum,    *)
  (* and the split sum is below eps; carried through QleT'/QltT      *)
  (* bridges, with the Id-face rewrite confined to the QleT' goal.   *)
  eapply qleT'_ltT_ltT.
  - eapply qleT'_trans.
    + eapply (QeqT_Qle_bool_cong _ _ _
                (qeqT_sym_hw _ _ (@bnorm_wd BA bae B _ _
                  (bxuq_diff_split BA bae B l1 (u (Nat.max N1 N2)) l2)))).
      apply qleT'_refl.
    + exact (@bnorm_plus BA bae B (@bplus BA bae B l1 (@bopp BA bae B (u (Nat.max N1 N2))))
                           (@bplus BA bae B (u (Nat.max N1 N2)) (@bopp BA bae B l2))).
  - apply (bxuq_sum_half_lt
             (@bnorm BA bae B (@bplus BA bae B l1 (@bopp BA bae B (u (Nat.max N1 N2)))))
             (@bnorm BA bae B (@bplus BA bae B (u (Nat.max N1 N2)) (@bopp BA bae B l2)))).
    + exact Hal.
    + exact Hb.
Qed.

(* ============================================================ *)
(* Main statement: uniqueness of blim limits, discharged through  *)
(* the separation field.                                          *)
(* ============================================================ *)

Theorem bxuq_lim_uniq : forall (BA : Set) (bae : BA -> BA -> Set)
    (E : BanachAlgExt BA bae) (u : nat -> BA) (l1 l2 : BA),
  blim BA bae (@bxce_base _ _ E) u l1 ->
  blim BA bae (@bxce_base _ _ E) u l2 ->
  bae l1 l2.
Proof.
  intros BA bae E u l1 l2 H1 H2.
  apply (@bxuq_add_opp_zero_eq BA bae (@bxce_base _ _ E) l1 l2).
  apply (@bxce_sep _ _ E (@bplus BA bae (@bxce_base _ _ E) l1
                                 (@bopp BA bae (@bxce_base _ _ E) l2))).
  exact (bxuq_lim_diff_small BA bae (@bxce_base _ _ E) u l1 l2 H1 H2).
Qed.

(* ============================================================ *)
(* Joint statement: the limit of products (bxadd_bmult_lim)       *)
(* merged with uniqueness.                                        *)
(* ============================================================ *)

Corollary bxuq_prod_lim_joint : forall (BA : Set) (bae : BA -> BA -> Set)
    (E : BanachAlgExt BA bae) (a b : BA) (la lb l : BA),
  blim BA bae (@bxce_base _ _ E)
    (fun n : nat => exp_series_partial BA bae (@bxce_base _ _ E) a n) la ->
  blim BA bae (@bxce_base _ _ E)
    (fun n : nat => exp_series_partial BA bae (@bxce_base _ _ E) b n) lb ->
  blim BA bae (@bxce_base _ _ E)
    (fun n : nat => @bmult BA bae (@bxce_base _ _ E)
                (exp_series_partial BA bae (@bxce_base _ _ E) a n)
                (exp_series_partial BA bae (@bxce_base _ _ E) b n)) l ->
  bae l (@bmult BA bae (@bxce_base _ _ E) la lb).
Proof.
  intros BA bae E a b la lb l Ha Hb Hp.
  apply (bxuq_lim_uniq BA bae E
           (fun n : nat =>
              @bmult BA bae (@bxce_base _ _ E)
                (exp_series_partial BA bae (@bxce_base _ _ E) a n)
                (exp_series_partial BA bae (@bxce_base _ _ E) b n))).
  - exact Hp.
  - exact (bxadd_bmult_lim BA bae (@bxce_base _ _ E)
             (fun n : nat => exp_series_partial BA bae (@bxce_base _ _ E) a n)
             (fun n : nat => exp_series_partial BA bae (@bxce_base _ _ E) b n)
             la lb Ha Hb).
Qed.

(* Closing print: assumption census of the main statement. *)
Print Assumptions bxuq_lim_uniq.
