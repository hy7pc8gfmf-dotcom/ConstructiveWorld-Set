(* ==========================================================================
   UpReqBanachExpAdd.v — Banach exponential addition law and esp junctions.
   Mission. bxadd_prod_diff_join (product-difference joining),
            bxadd_esp_join (error-share joining),
            bxadd_bmult_lim (bounded-multiplication limit of products) and
            the corollary bxadd_esp_prod_blim; Q-layer arithmetic support.
   Dependencies. S01_BaseRing, S02_CauchyComplete, S03_QExp,
                 UpReqBanachExp, UpReqBanachExpDef, UpReqBanachInvPre;
                 Stdlib QArith, Arith, Lia, Setoid, Morphisms.
   References. Error-controlled form of the exponential law
               exp(a+b) = exp(a)*exp(b) for Banach-algebra exponentials.
   Constructivity. Every proof is closed with Qed and no proof is left
               unfinished; no classical logic; statements are carried at
               the Set level (order predicates and equalities are
               Set-valued; conclusion positions stay free of Prop).
   Build. Rocq 9.1, rocq c -q -native-compiler no with -Q . "" — the
               module recompiles in place against one load path.
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachExpDef.
Require Import UpReqBanachInvPre.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qminmax Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Setoid Morphisms.

(* ============================================================ *)
(* I. Q-layer utilities (eps accounting and Qmin conveniences;   *)
(*    all hand-derived, zero lia)                                *)
(* ============================================================ *)

Lemma bxadd_qpos_plus_one : forall u : Q, Qle 0 u -> QltT 0 (u + 1)%Q.
Proof.
  intros u Hu. apply Qlt_to_QltT.
  apply (Qle_lt_trans 0 (u + 0)%Q (u + 1)%Q).
  - rewrite Qplus_0_r. exact Hu.
  - apply (proj2 (Qplus_lt_r 0%Q 1%Q u)).
    exact (QltT_to_Qlt 0%Q 1%Q qltT_0_1).
Qed.

Lemma bxadd_qmin_pos : forall a b : Q, QltT 0 a -> QltT 0 b -> QltT 0 (Qmin a b).
Proof.
  intros a b Ha Hb.
  destruct (Q.min_dec a b) as [Hq | Hq].
  - exact (qeq_ltT a (Qmin a b)
             (qeq_imp_qeqT a (Qmin a b) (Qeq_sym (Qmin a b) a Hq)) Ha).
  - exact (qeq_ltT b (Qmin a b)
             (qeq_imp_qeqT b (Qmin a b) (Qeq_sym (Qmin a b) b Hq)) Hb).
Qed.

Lemma bxadd_qmin_le_l : forall a b : Q, QleT' (Qmin a b) a.
Proof. intros a b. apply Qle_to_QleT'. apply Q.le_min_l. Qed.

Lemma bxadd_qmin_le_r : forall a b : Q, QleT' (Qmin a b) b.
Proof. intros a b. apply Qle_to_QleT'. apply Q.le_min_r. Qed.

(* Division upper-bound transfer: 0 < b and a ≤ b·c imply a/b ≤ c *)
Lemma bxadd_div_mul_le : forall a b c : Q,
  QltT 0 b -> Qle a (b * c) -> QleT' (a / b) c.
Proof.
  intros a b c Hb Hac.
  assert (Hneq : ~ (b == 0)%Q)
    by (intro Hzz;
        exact (match qltT_not_eq_zero b Hb (qeq_imp_qeqT b 0 Hzz)
               with end)).
  apply Qle_to_QleT'.
  apply (proj1 (Qmult_le_r (a / b) c b (QltT_to_Qlt 0%Q b%Q Hb))).
  assert (Eab : ((a / b) * b == a)%Q).
  { unfold Qdiv. rewrite <- Qmult_assoc. rewrite (Qmult_comm (/ b) b).
    rewrite (Qmult_inv_r b Hneq). rewrite Qmult_1_r. ring. }
  rewrite (Qmult_comm b c) in Hac. rewrite Eab. exact Hac.
Qed.

(* Strict three-quarters: 0 < e implies 3·(e/4) < e *)
Lemma bxadd_three_quarter_lt : forall e : Q, QltT 0 e -> QltT (3 * (e / 4))%Q e.
Proof.
  intros e He. apply Qlt_to_QltT.
  assert (H4 : ~ (4 == 0)%Q)
    by (intro Hfz;
        exact (match qltT_not_eq_zero 4%Q qltT_0_4 (qeq_imp_qeqT 4%Q 0 Hfz)
               with end)).
  assert (H4pos : Qlt 0 4%Q) by exact (QltT_to_Qlt 0%Q 4%Q qltT_0_4).
  assert (H34 : Qlt 3 4).
  { assert (H34T : QltT 3 4) by reflexivity.
    exact (QltT_to_Qlt 3%Q 4%Q H34T). }
  assert (Hstep : (3 * e < e * 4)%Q).
  { assert (Ecomm : (e * 4 == 4 * e)%Q) by ring.
    rewrite Ecomm. exact (Qmult_lt_compat_r 3 4 e (QltT_to_Qlt 0%Q e%Q He) H34). }
  apply (proj1 (Qmult_lt_r (3 * (e / 4)) e 4%Q H4pos)).
  assert (Eprod : ((3 * (e / 4)) * 4 == 3 * e)%Q).
  { unfold Qdiv. rewrite <- !Qmult_assoc. rewrite (Qmult_comm (/ 4) 4).
    rewrite (Qmult_inv_r 4 H4). rewrite Qmult_1_r. ring. }
  rewrite Eprod. exact Hstep.
Qed.

(* ============================================================ *)
(* II. Banach side: distributing negation over multiplication    *)
(*     and difference joining (bae equality carrier)             *)
(* ============================================================ *)

(* z·(−x) is bae-equal to −(z·x) (general form; binv_mult_opp_r
   covers only the special shape x·(−x)) *)
Lemma bxadd_bmult_opp_r : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x z : BA),
  bae (@bmult BA bae B z (@bopp BA bae B x)) (@bopp BA bae B (@bmult BA bae B z x)).
Proof.
  intros BA bae B x z.
  apply (@bopp_unique BA bae B (@bmult BA bae B z (@bopp BA bae B x)) (@bmult BA bae B z x)).
  eapply bae_trans.
  - apply (@bae_sym BA bae B). exact (@bdistrib_l BA bae B z (@bopp BA bae B x) x).
  - eapply bae_trans.
    + apply (@bmult_wd BA bae B z (@bplus BA bae B (@bopp BA bae B x) x) z (@bzero BA bae B)).
      * apply (@bae_refl BA bae B).
      * apply (@bae_trans BA bae B _ (@bplus BA bae B x (@bopp BA bae B x)) _).
        -- exact (@bplus_comm BA bae B (@bopp BA bae B x) x).
        -- exact (@bplus_opp BA bae B x).
    + exact (@bmult_zero BA bae B z).
Qed.

(* x·z − y·z is bae-equal to (x−y)·z *)
Lemma bxadd_bminus_mult_l : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x y z : BA),
  bae (@bplus BA bae B (@bmult BA bae B x z) (@bopp BA bae B (@bmult BA bae B y z)))
         (@bmult BA bae B (@bplus BA bae B x (@bopp BA bae B y)) z).
Proof.
  intros BA bae B x y z.
  eapply bae_trans.
  - apply (@bplus_wd_r BA bae B (@bopp BA bae B (@bmult BA bae B y z)) (@bmult BA bae B (@bopp BA bae B y) z)
             (@bmult BA bae B x z)).
    apply (@bae_sym BA bae B). exact (binv_bmult_opp_l BA bae B y z).
  - apply (@bae_sym BA bae B). exact (@bdistrib_r BA bae B x (@bopp BA bae B y) z).
Qed.

(* z·x − z·y is bae-equal to z·(x−y) *)
Lemma bxadd_bminus_mult_r : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x y z : BA),
  bae (@bplus BA bae B (@bmult BA bae B z x) (@bopp BA bae B (@bmult BA bae B z y)))
         (@bmult BA bae B z (@bplus BA bae B x (@bopp BA bae B y))).
Proof.
  intros BA bae B x y z.
  eapply bae_trans.
  - apply (@bplus_wd_r BA bae B (@bopp BA bae B (@bmult BA bae B z y)) (@bmult BA bae B z (@bopp BA bae B y))
             (@bmult BA bae B z x)).
    apply (@bae_sym BA bae B). exact (bxadd_bmult_opp_r BA bae B y z).
  - apply (@bae_sym BA bae B). exact (@bdistrib_l BA bae B z x (@bopp BA bae B y)).
Qed.

(* (−a) + (a + b) is bae-equal to b (middle cancellation) *)
Lemma bxadd_opp_plus_cancel : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bplus BA bae B (@bopp BA bae B a) (@bplus BA bae B a b)) b.
Proof.
  intros BA bae B a b.
  eapply bae_trans.
  - exact (@bplus_assoc BA bae B (@bopp BA bae B a) a b).
  - eapply bae_trans.
    + apply (@bplus_wd BA bae B).
      * apply (@bae_trans BA bae B _ (@bplus BA bae B a (@bopp BA bae B a)) _).
        -- exact (@bplus_comm BA bae B (@bopp BA bae B a) a).
        -- exact (@bplus_opp BA bae B a).
      * apply (@bae_refl BA bae B).
    + exact (@bplus_zero_l BA bae B b).
Qed.

(* x·y − lx·ly is bae-equal to (x·y − lx·y) + (lx·y − lx·ly)
   (two-point interpolation) *)
Lemma bxadd_prod_diff_join : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x y lx ly : BA),
  bae (@bplus BA bae B (@bmult BA bae B x y) (@bopp BA bae B (@bmult BA bae B lx ly)))
         (@bplus BA bae B (@bplus BA bae B (@bmult BA bae B x y) (@bopp BA bae B (@bmult BA bae B lx y)))
                  (@bplus BA bae B (@bmult BA bae B lx y) (@bopp BA bae B (@bmult BA bae B lx ly)))).
Proof.
  intros BA bae B x y lx ly.
  apply (@bae_sym BA bae B).
  eapply bae_trans.
  - apply (@bae_sym BA bae B).
    exact (@bplus_assoc BA bae B (@bmult BA bae B x y) (@bopp BA bae B (@bmult BA bae B lx y))
             (@bplus BA bae B (@bmult BA bae B lx y) (@bopp BA bae B (@bmult BA bae B lx ly)))).
  - apply (@bplus_wd_r BA bae B
             (@bplus BA bae B (@bopp BA bae B (@bmult BA bae B lx y))
                (@bplus BA bae B (@bmult BA bae B lx y) (@bopp BA bae B (@bmult BA bae B lx ly))))
             (@bopp BA bae B (@bmult BA bae B lx ly)) (@bmult BA bae B x y)).
    exact (bxadd_opp_plus_cancel BA bae B (@bmult BA bae B lx y) (@bopp BA bae B (@bmult BA bae B lx ly))).
Qed.

(* u is bae-equal to (u − l) + l (self-joining of an element,
   used by the subadditivity chain of the norm) *)
Lemma bxadd_esp_join : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (u l : BA),
  bae u (@bplus BA bae B (@bplus BA bae B u (@bopp BA bae B l)) l).
Proof.
  intros BA bae B u l.
  eapply bae_trans.
  - apply (@bae_sym BA bae B). exact (@bplus_zero BA bae B u).
  - apply (@bae_trans BA bae B (@bplus BA bae B u (@bzero BA bae B))
             (@bplus BA bae B u (@bplus BA bae B (@bopp BA bae B l) l))
             (@bplus BA bae B (@bplus BA bae B u (@bopp BA bae B l)) l)).
    + apply (@bplus_wd_r BA bae B (@bzero BA bae B) (@bplus BA bae B (@bopp BA bae B l) l) u).
      apply (@bae_trans BA bae B (@bzero BA bae B) (@bplus BA bae B l (@bopp BA bae B l))
               (@bplus BA bae B (@bopp BA bae B l) l)).
      * apply (@bae_sym BA bae B). exact (@bplus_opp BA bae B l).
      * apply (@bae_sym BA bae B). exact (@bplus_comm BA bae B (@bopp BA bae B l) l).
    + exact (@bplus_assoc BA bae B u (@bopp BA bae B l) l).
Qed.

(* ============================================================ *)
(* III. Main lemma: multiplication continuity of limits.         *)
(*   x_n → lx and y_n → ly imply x_n·y_n → lx·ly                 *)
(*   (blim neighbourhood form).  Constructive triangle           *)
(*   expansion: ‖x_n·y_n − lx·ly‖ ≤ ‖x_n−lx‖·‖y_n‖               *)
(*   + ‖lx‖·‖y_n−ly‖; the cap eb = min(eps/4,1) closes over      *)
(*   the division re-bounding accounting.                        *)
(* ============================================================ *)

Lemma bxadd_bmult_lim : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
                                     (x y : nat -> BA) (lx ly : BA),
  blim BA bae B x lx -> blim BA bae B y ly ->
  blim BA bae B (fun n : nat => @bmult BA bae B (x n) (y n)) (@bmult BA bae B lx ly).
Proof.
  intros BA bae B x y lx ly Hx Hy eps Heps.
  set (nlx := @bnorm BA bae B lx).
  set (nly := @bnorm BA bae B ly).
  assert (Hlx0 : Qle 0 nlx) by (apply QleT'_to_Qle; exact (@bnorm_pos BA bae B lx)).
  assert (Hly0 : Qle 0 nly) by (apply QleT'_to_Qle; exact (@bnorm_pos BA bae B ly)).
  assert (Hlx1 : Qle nlx (nlx + 1)%Q)
    by (exact (Qle_plus_nonneg_r nlx 1%Q (QleT'_to_Qle 0%Q 1%Q Qle_0_1))).
  assert (Hly1 : Qle nly (nly + 1)%Q)
    by (exact (Qle_plus_nonneg_r nly 1%Q (QleT'_to_Qle 0%Q 1%Q Qle_0_1))).
  assert (Hcx0 : QltT 0 (nlx + 1)%Q) by (apply bxadd_qpos_plus_one; exact Hlx0).
  assert (Hcy0 : QltT 0 (nly + 1)%Q) by (apply bxadd_qpos_plus_one; exact Hly0).
  assert (Hcxne : ~ ((nlx + 1) == 0)%Q)
    by (intro Hzz;
        exact (match
                 qltT_not_eq_zero (nlx + 1)%Q Hcx0
                   (qeq_imp_qeqT (nlx + 1)%Q 0 Hzz)
               with end)).
  assert (Hcyne : ~ ((nly + 1) == 0)%Q)
    by (intro Hzz;
        exact (match
                 qltT_not_eq_zero (nly + 1)%Q Hcy0
                   (qeq_imp_qeqT (nly + 1)%Q 0 Hzz)
               with end)).
  assert (Hone_cx : Qle 1 (nlx + 1)%Q).
  { assert (Ec : ((nlx + 1) == 1 + nlx)%Q) by ring.
    rewrite Ec. exact (Qle_plus_nonneg_r 1%Q nlx Hlx0). }
  assert (Hone_cy : Qle 1 (nly + 1)%Q).
  { assert (Ec : ((nly + 1) == 1 + nly)%Q) by ring.
    rewrite Ec. exact (Qle_plus_nonneg_r 1%Q nly Hly0). }
  assert (He4 : QltT 0 (eps / 4)%Q)
    by (apply qltT_div_pos; [exact Heps | exact qltT_0_4]).
  set (eb := Qmin (eps / 4) 1%Q).
  assert (Heb0 : QltT 0 eb) by (apply bxadd_qmin_pos; [exact He4 | exact qltT_0_1]).
  assert (Heb1 : Qle eb 1%Q)
    by (exact (QleT'_to_Qle _ _ (bxadd_qmin_le_r (eps / 4) 1%Q))).
  assert (Heb4 : Qle eb (eps / 4)%Q)
    by (exact (QleT'_to_Qle _ _ (bxadd_qmin_le_l (eps / 4) 1%Q))).
  assert (Heb_bx : Qle eb (nlx + 1)%Q).
  { apply (Qle_trans eb 1%Q (nlx + 1)%Q); [exact Heb1 | exact Hone_cx]. }
  assert (Heb_by : Qle eb (nly + 1)%Q).
  { apply (Qle_trans eb 1%Q (nly + 1)%Q); [exact Heb1 | exact Hone_cy]. }
  assert (He1d : QltT 0 (eb / (nly + 1))%Q)
    by (apply qltT_div_pos; [exact Heb0 | exact Hcy0]).
  assert (Hcx1 : Qle (eb / (nlx + 1)) 1%Q).
  { apply QleT'_to_Qle. apply (bxadd_div_mul_le eb (nlx + 1) 1%Q).
    - exact Hcx0.
    - assert (E1 : ((nlx + 1) * 1 == nlx + 1)%Q) by ring.
      rewrite E1. exact Heb_bx. }
  assert (Hcy1 : Qle (eb / (nly + 1)) 1%Q).
  { apply QleT'_to_Qle. apply (bxadd_div_mul_le eb (nly + 1) 1%Q).
    - exact Hcy0.
    - assert (E1 : ((nly + 1) * 1 == nly + 1)%Q) by ring.
      rewrite E1. exact Heb_by. }
  (* Take the two witnesses from blim (radii: Qmin(eb/(‖ly‖+1),1) *)
  (* and eb/(‖lx‖+1)).                                            *)
  assert (Hpos1 : QltT 0 (Qmin (eb / (nly + 1)) 1%Q))
    by (apply bxadd_qmin_pos; [exact He1d | exact qltT_0_1]).
  assert (Hpos2 : QltT 0 (eb / (nlx + 1))%Q)
    by (apply qltT_div_pos; [exact Heb0 | exact Hcx0]).
  destruct (Hx (Qmin (eb / (nly + 1)) 1%Q) Hpos1) as [Nx HNx].
  destruct (Hy (eb / (nlx + 1))%Q Hpos2) as [Ny HNy].
  exists (Nat.max Nx Ny). intros n Hnmax.
  apply NatLe_drop in Hnmax.
  assert (Hn1 : (Nx <= n)%nat) by lia.
  assert (Hn2 : (Ny <= n)%nat) by lia.
  specialize (HNx n (NatLe_lift Nx n Hn1)).
  specialize (HNy n (NatLe_lift Ny n Hn2)).
  (* ‖y_n‖ < eb/(‖lx‖+1) + ‖ly‖ *)
  assert (Hyn : QltT (@bnorm BA bae B (y n)) (eb / (nlx + 1) + nly)%Q).
  { eapply (QeqT_Qlt_bool_cong _ _ _
      (qeqT_sym_hw _ _ (@bnorm_wd BA bae B (y n)
              (@bplus BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly)) ly)
              (bxadd_esp_join BA bae B (y n) ly)))).
    apply (qleT'_ltT_ltT _ (@bnorm BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly))
                              + @bnorm BA bae B ly)%Q _).
    - exact (@bnorm_plus BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly)) ly).
    - exact (qltT_plus_leT'_ltT
               (@bnorm BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly)))
               (eb / (nlx + 1)) (@bnorm BA bae B ly) (@bnorm BA bae B ly)
               HNy (qleT'_refl (@bnorm BA bae B ly))). }
  (* First term: ‖x_n·y_n − lx·y_n‖ < 2·eb *)
  assert (Hd1 : QltT (@bnorm BA bae B (@bplus BA bae B (@bmult BA bae B (x n) (y n))
                                (@bopp BA bae B (@bmult BA bae B lx (y n)))))
                     (2 * eb)%Q).
  { eapply (QeqT_Qlt_bool_cong _ _ _
      (qeqT_sym_hw _ _ (@bnorm_wd BA bae B
        (@bplus BA bae B (@bmult BA bae B (x n) (y n)) (@bopp BA bae B (@bmult BA bae B lx (y n))))
        (@bmult BA bae B (@bplus BA bae B (x n) (@bopp BA bae B lx)) (y n))
        (bxadd_bminus_mult_l BA bae B (x n) lx (y n))))).
    (* ‖(x_n−lx)·y_n‖ ≤ e1·‖y_n‖ ≤ (eb/(‖ly‖+1))·‖y_n‖ *)
    (* < (eb/(‖ly‖+1))·(eb/(‖lx‖+1)+‖ly‖) ≤ 2eb *)
    assert (Hstep1 : QleT' (@bnorm BA bae B (@bmult BA bae B (@bplus BA bae B (x n) (@bopp BA bae B lx)) (y n)))
                           ((Qmin (eb / (nly + 1)) 1%Q) * @bnorm BA bae B (y n))%Q).
    { apply (qleT'_trans _ (@bnorm BA bae B (@bplus BA bae B (x n) (@bopp BA bae B lx))
                              * @bnorm BA bae B (y n))%Q _).
      - exact (@bnorm_mult BA bae B (@bplus BA bae B (x n) (@bopp BA bae B lx)) (y n)).
      - apply Qle_to_QleT'.
        exact (Qmult_le_compat_r
                 (@bnorm BA bae B (@bplus BA bae B (x n) (@bopp BA bae B lx)))
                 (Qmin (eb / (nly + 1)) 1%Q) (@bnorm BA bae B (y n))
                 (QleT'_to_Qle (@bnorm BA bae B (@bplus BA bae B (x n) (@bopp BA bae B lx)))
                    (Qmin (eb / (nly + 1)) 1%Q)
                    (qltT_leT' (@bnorm BA bae B (@bplus BA bae B (x n) (@bopp BA bae B lx)))
                       (Qmin (eb / (nly + 1)) 1%Q) HNx))
                 (QleT'_to_Qle 0%Q (@bnorm BA bae B (y n))
                    (@bnorm_pos BA bae B (y n)))). }
    assert (Hstep2 : QleT' ((Qmin (eb / (nly + 1)) 1%Q) * @bnorm BA bae B (y n))%Q
                           ((eb / (nly + 1)) * @bnorm BA bae B (y n))%Q).
    { apply Qle_to_QleT'.
      exact (Qmult_le_compat_r (Qmin (eb / (nly + 1)) 1%Q)
               (eb / (nly + 1)) (@bnorm BA bae B (y n))
               (QleT'_to_Qle (Qmin (eb / (nly + 1)) 1%Q) (eb / (nly + 1))
                  (bxadd_qmin_le_l (eb / (nly + 1)) 1%Q))
               (QleT'_to_Qle 0%Q (@bnorm BA bae B (y n))
                  (@bnorm_pos BA bae B (y n)))). }
    assert (Hsum : Qle (eb / (nlx + 1) + nly)
                       ((nly + 1) + (nly + 1))%Q).
    { apply (Qle_trans (eb / (nlx + 1) + nly) (1%Q + (nly + 1))
              ((nly + 1) + (nly + 1))).
      - exact (Qplus_le_compat (eb / (nlx + 1)) 1%Q nly (nly + 1)
                 Hcx1 Hly1).
      - exact (Qplus_le_compat 1%Q (nly + 1) (nly + 1) (nly + 1)
                 Hone_cy (Qle_refl (nly + 1))). }
    apply (qleT'_ltT_ltT _ ((eb / (nly + 1)) * @bnorm BA bae B (y n))%Q _).
    - exact (qleT'_trans
               (@bnorm BA bae B (@bmult BA bae B (@bplus BA bae B (x n) (@bopp BA bae B lx)) (y n)))
               ((Qmin (eb / (nly + 1)) 1%Q) * @bnorm BA bae B (y n))
               ((eb / (nly + 1)) * @bnorm BA bae B (y n))
               Hstep1 Hstep2).
    - assert (Hcomm : QleT' ((eb / (nly + 1)) * @bnorm BA bae B (y n))
                             (@bnorm BA bae B (y n) * (eb / (nly + 1)))).
      { apply qeq_leT'. apply qeq_imp_qeqT.
        exact (Qmult_comm (eb / (nly + 1)) (@bnorm BA bae B (y n))). }
      assert (Hringc : QleT' ((eb / (nlx + 1) + nly) * (eb / (nly + 1)))
                              (2 * eb)%Q).
      { apply Qle_to_QleT'.
        apply (Qle_trans ((eb / (nlx + 1) + nly) * (eb / (nly + 1)))
                (((nly + 1) + (nly + 1)) * (eb / (nly + 1))) (2 * eb)).
        - exact (Qmult_le_compat_r (eb / (nlx + 1) + nly)
                   ((nly + 1) + (nly + 1)) (eb / (nly + 1)) Hsum
                   (QleT'_to_Qle 0%Q (eb / (nly + 1))
                      (qltT_leT' 0%Q (eb / (nly + 1))
                         (qltT_div_pos eb (nly + 1) Heb0 Hcy0)))).
        - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          unfold Qdiv. rewrite Qmult_plus_distr_l.
          rewrite !(Qmult_comm (nly + 1) (eb * / (nly + 1))).
          rewrite <- !Qmult_assoc.
          rewrite !(Qmult_comm (/ (nly + 1)) (nly + 1)).
          rewrite (Qmult_inv_r (nly + 1) Hcyne). rewrite !Qmult_1_r.
          ring. }
      exact (qleT'_ltT_ltT ((eb / (nly + 1)) * @bnorm BA bae B (y n))
               (@bnorm BA bae B (y n) * (eb / (nly + 1))) (2 * eb)
               Hcomm
               (qltT_leT'_ltT (@bnorm BA bae B (y n) * (eb / (nly + 1)))
                  ((eb / (nlx + 1) + nly) * (eb / (nly + 1))) (2 * eb)
                  (qltT_mult_ltT_compat_r (@bnorm BA bae B (y n))
                     (eb / (nlx + 1) + nly) (eb / (nly + 1))
                     (qltT_div_pos eb (nly + 1) Heb0 Hcy0) Hyn)
                  Hringc)). }
  (* Second term: ‖lx·y_n − lx·ly‖ < eb *)
  assert (Hd2 : QltT (@bnorm BA bae B (@bplus BA bae B (@bmult BA bae B lx (y n))
                                (@bopp BA bae B (@bmult BA bae B lx ly))))
                     eb%Q).
  { eapply (QeqT_Qlt_bool_cong _ _ _
      (qeqT_sym_hw _ _ (@bnorm_wd BA bae B
        (@bplus BA bae B (@bmult BA bae B lx (y n)) (@bopp BA bae B (@bmult BA bae B lx ly)))
        (@bmult BA bae B lx (@bplus BA bae B (y n) (@bopp BA bae B ly)))
        (bxadd_bminus_mult_r BA bae B (y n) ly lx)))).
    (* ‖lx·(y_n−ly)‖ ≤ ‖lx‖·‖y_n−ly‖ ≤ (‖lx‖+1)·‖y_n−ly‖ *)
    (* < (‖lx‖+1)·(eb/(‖lx‖+1)) == eb *)
    assert (Hstep1 : QleT' (@bnorm BA bae B (@bmult BA bae B lx (@bplus BA bae B (y n) (@bopp BA bae B ly))))
                           (nlx * @bnorm BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly)))%Q).
    { exact (@bnorm_mult BA bae B lx (@bplus BA bae B (y n) (@bopp BA bae B ly))). }
    assert (Hstep2 : QleT' (nlx * @bnorm BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly)))%Q
                           ((nlx + 1) * @bnorm BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly)))%Q).
    { apply Qle_to_QleT'.
      exact (Qmult_le_compat_r nlx (nlx + 1)
               (@bnorm BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly))) Hlx1
               (QleT'_to_Qle 0%Q (@bnorm BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly)))
                  (@bnorm_pos BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly))))). }
    apply (qleT'_ltT_ltT _
             ((nlx + 1) * @bnorm BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly)))%Q _).
    - exact (qleT'_trans
               (@bnorm BA bae B (@bmult BA bae B lx (@bplus BA bae B (y n) (@bopp BA bae B ly))))
               (nlx * @bnorm BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly)))
               ((nlx + 1) * @bnorm BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly)))
               Hstep1 Hstep2).
    - assert (Hcx : ((nlx + 1) * (eb / (nlx + 1)) == eb)%Q).
      { unfold Qdiv.
        rewrite (Qmult_comm (nlx + 1) (eb * / (nlx + 1))).
        rewrite <- Qmult_assoc.
        rewrite (Qmult_comm (/ (nlx + 1)) (nlx + 1)).
        rewrite (Qmult_inv_r (nlx + 1) Hcxne). rewrite Qmult_1_r.
        reflexivity. }
      set (w := @bnorm BA bae B (@bplus BA bae B (y n) (@bopp BA bae B ly))) in *.
      assert (Hcomm1 : QleT' ((nlx + 1) * w) (w * (nlx + 1))).
      { apply qeq_leT'. apply qeq_imp_qeqT.
        exact (Qmult_comm (nlx + 1) w). }
      assert (Hcx2 : ((eb / (nlx + 1)) * (nlx + 1) == eb)%Q).
      { unfold Qdiv. rewrite <- Qmult_assoc.
        rewrite (Qmult_comm (/ (nlx + 1)) (nlx + 1)).
        rewrite (Qmult_inv_r (nlx + 1) Hcxne). rewrite Qmult_1_r.
        reflexivity. }
      exact (qleT'_ltT_ltT ((nlx + 1) * w) (w * (nlx + 1)) eb Hcomm1
               (qltT_eq_compat_r eb ((eb / (nlx + 1)) * (nlx + 1))
                  (w * (nlx + 1))
                  (qeq_imp_qeqT eb ((eb / (nlx + 1)) * (nlx + 1))
                     (Qeq_sym ((eb / (nlx + 1)) * (nlx + 1)) eb Hcx2))
                  (qltT_mult_ltT_compat_r w (eb / (nlx + 1)) (nlx + 1)
                     Hcx0 HNy))).
  }
  (* Assembly: ‖x_n·y_n − lx·ly‖ ≤ ‖d1‖+‖d2‖ < 3eb ≤ 3·(eps/4) < eps *)
  assert (Hjoin : QleT' (@bnorm BA bae B (@bplus BA bae B (@bmult BA bae B (x n) (y n))
                                    (@bopp BA bae B (@bmult BA bae B lx ly))))
                        (((@bnorm BA bae B (@bplus BA bae B (@bmult BA bae B (x n) (y n))
                                     (@bopp BA bae B (@bmult BA bae B lx (y n)))))
                            + @bnorm BA bae B (@bplus BA bae B (@bmult BA bae B lx (y n))
                                          (@bopp BA bae B (@bmult BA bae B lx ly)))))%Q).
  { eapply (QeqT_Qle_bool_cong _ _ _
      (qeqT_sym_hw _ _ (@bnorm_wd BA bae B
      (@bplus BA bae B (@bmult BA bae B (x n) (y n)) (@bopp BA bae B (@bmult BA bae B lx ly)))
      (@bplus BA bae B (@bplus BA bae B (@bmult BA bae B (x n) (y n)) (@bopp BA bae B (@bmult BA bae B lx (y n))))
               (@bplus BA bae B (@bmult BA bae B lx (y n)) (@bopp BA bae B (@bmult BA bae B lx ly))))
      (bxadd_prod_diff_join BA bae B (x n) (y n) lx ly)))).
    exact (@bnorm_plus BA bae B
             (@bplus BA bae B (@bmult BA bae B (x n) (y n)) (@bopp BA bae B (@bmult BA bae B lx (y n))))
             (@bplus BA bae B (@bmult BA bae B lx (y n)) (@bopp BA bae B (@bmult BA bae B lx ly)))). }
  assert (Hthree : QltT (@bnorm BA bae B (@bplus BA bae B (@bmult BA bae B (x n) (y n))
                                     (@bopp BA bae B (@bmult BA bae B lx (y n))))
                          + @bnorm BA bae B (@bplus BA bae B (@bmult BA bae B lx (y n))
                                     (@bopp BA bae B (@bmult BA bae B lx ly))))%Q
                        (2 * eb + eb)%Q).
  { exact (qltT_plus_ltT
             (@bnorm BA bae B (@bplus BA bae B (@bmult BA bae B (x n) (y n))
                          (@bopp BA bae B (@bmult BA bae B lx (y n))))) (2 * eb)
             (@bnorm BA bae B (@bplus BA bae B (@bmult BA bae B lx (y n))
                          (@bopp BA bae B (@bmult BA bae B lx ly)))) eb
             Hd1 Hd2). }
  assert (Hfin : QltT (2 * eb + eb) eps).
  { apply (qleT'_ltT_ltT _ (3 * (eps / 4))%Q).
    - apply Qle_to_QleT'.
      apply (Qle_trans (2 * eb + eb) (eb * 3) (3 * (eps / 4))).
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      + apply (Qle_trans (eb * 3) ((eps / 4) * 3) (3 * (eps / 4))).
        * exact (Qmult_le_compat_r eb (eps / 4) 3%Q Heb4
                   (QleT'_to_Qle 0%Q 3%Q (qltT_leT' 0%Q 3%Q qltT_0_3))).
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
          exact (Qmult_comm (eps / 4) 3).
    - exact (bxadd_three_quarter_lt eps Heps). }
  apply (qleT'_ltT_ltT
           (@bnorm BA bae B (@bplus BA bae B (@bmult BA bae B (x n) (y n))
                        (@bopp BA bae B (@bmult BA bae B lx ly))))
           ((@bnorm BA bae B (@bplus BA bae B (@bmult BA bae B (x n) (y n))
                          (@bopp BA bae B (@bmult BA bae B lx (y n)))))
              + @bnorm BA bae B (@bplus BA bae B (@bmult BA bae B lx (y n))
                             (@bopp BA bae B (@bmult BA bae B lx ly))))%Q).
  - exact Hjoin.
  - exact (qltT_leT'_ltT
             (((@bnorm BA bae B (@bplus BA bae B (@bmult BA bae B (x n) (y n))
                          (@bopp BA bae B (@bmult BA bae B lx (y n)))))
                 + @bnorm BA bae B (@bplus BA bae B (@bmult BA bae B lx (y n))
                                (@bopp BA bae B (@bmult BA bae B lx ly)))))%Q
              (2 * eb + eb) eps Hthree (qltT_leT' (2 * eb + eb) eps Hfin)).
Qed.

(* ============================================================ *)
(* IV. Immediate corollary: e^a·e^b is the limit of the sequence *)
(*   (esp n a)·(esp n b) (left half assembled; joins the right   *)
(*   half given by bxdef_exp_spec (a+b)).                        *)
(* ============================================================ *)

Corollary bxadd_esp_prod_blim : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  blim BA bae B (fun n : nat => @bmult BA bae B (exp_series_partial BA bae B a n)
                                  (exp_series_partial BA bae B b n))
         (@bmult BA bae B (bxdef_exp BA bae B a) (bxdef_exp BA bae B b)).
Proof.
  intros BA bae B a b.
  apply (bxadd_bmult_lim BA bae B
           (fun n : nat => exp_series_partial BA bae B a n)
           (fun n : nat => exp_series_partial BA bae B b n)).
  - exact (bxdef_exp_spec BA bae B a).
  - exact (bxdef_exp_spec BA bae B b).
Qed.
