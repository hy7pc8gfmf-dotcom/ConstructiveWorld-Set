(* ============================================================
   LW0_SinPos.v -- the pointwise positivity of the sine over the open
   interval (0, pi).
   Mission. For any real t, an explicit witness of
   real_lt real_zero (cauchy_real_sin t) is constructed from
   real_lt real_zero t and real_lt t real_pi_geom (real_lt is the
   Set-layer sigT double-witness form: the positive precision eps and
   the tail-controlled index N).
   Dependencies. S01_BaseRing (NatLe, the Set-layer And/Or carriers),
   S02_CauchyComplete (Real, the real_lt/real_eq order-ring core and
   the projection faces), S07_RealSetoidExpLog, S08_RealMainlineDPO,
   S09_EntropyReal, S10_KVQuantTrig (cauchy_real_sin, the angle-addition
   faces, real_pi_geom), S12_B5RecycleSF, UpReqPadeTailPos,
   UpReqPadeTransport.
   References. I. Niven, Irrationality of pi, Bulletin of the AMS 53
   (1947), the positivity preliminary section: sin is positive inside
   (0, pi).
   Constructivity. The reflection is assembled from the angle-addition
   formula with the in-library endpoint values sin(pi)=0 and
   cos(pi)=-1; the gap bisection is constructed explicitly at 1/12
   precision with the Qcompare three-way test and the cauchy tail
   control; every statement is Set-carried, zero Prop premises, zero
   admissions.
   Build. coqc -q -Q <tree root> "" LW0_SinPos.v
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs Setoid Morphisms Arith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S12_B5RecycleSF.
Require Import UpReqPadeTailPos.
Require Import UpReqPadeTransport.

(* ===== Sine positivity on (0, pi) ===== *)

(* ---- The two-sided congruence of real_plus over real_eq ----
   the pointwise triangle inequality |(A+B)-(A'+B')| <= |A-A'| + |B-B'|, with the halved slack eps/2. *)

Lemma lw0_sin_plus_eq_compat : forall a a' b b' : Real,
  real_eq a a' -> real_eq b b' ->
  real_eq (real_plus a b) (real_plus a' b').
Proof.
  intros a a' b b' Ha Hb eps Heps.
  assert (Hh : QltT 0 (eps * (1 # 2))%Q).
  { apply Qlt_to_QltT.
    assert (Hlt : (0 < eps)%Q) by (apply QltT_to_Qlt; exact Heps).
    assert (Hc : (0 < (1 # 2))%Q) by (unfold Qlt; reflexivity).
    assert (Hm : (0 * (1 # 2) < eps * (1 # 2))%Q)
      by (apply (proj2 (Qmult_lt_r 0 eps (1 # 2) Hc)); exact Hlt).
    assert (Hcz : ((0 * (1 # 2)) == 0)%Q) by ring.
    setoid_rewrite Hcz in Hm.
    exact Hm. }
  destruct (Ha (eps * (1 # 2))%Q Hh) as [N1 HN1].
  destruct (Hb (eps * (1 # 2))%Q Hh) as [N2 HN2].
  destruct a as [u Hu]. destruct a' as [u' Hu'].
  destruct b as [v Hv]. destruct b' as [v' Hv'].
  exists (Nat.max N1 N2). intros n Hn.
  assert (Hn1 : NatLe N1 n).
  { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2).
    - apply Nat.le_max_l.
    - apply NatLe_drop. exact Hn. }
  assert (Hn2 : NatLe N2 n).
  { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2).
    - apply Nat.le_max_r.
    - apply NatLe_drop. exact Hn. }
  specialize (HN1 n Hn1). specialize (HN2 n Hn2).
  change (QltT (Qabs ((u n + v n) - (u' n + v' n))) eps).
  apply Qlt_to_QltT.
  assert (H1 : Qlt (Qabs (u n - u' n)) (eps * (1 # 2)))
    by (apply QltT_to_Qlt; exact HN1).
  assert (H2 : Qlt (Qabs (v n - v' n)) (eps * (1 # 2)))
    by (apply QltT_to_Qlt; exact HN2).
  assert (Hrw : (((u n + v n) - (u' n + v' n))
               == ((u n - u' n) + (v n - v' n)))%Q) by ring.
  setoid_rewrite Hrw.
  apply (Qle_lt_trans _ (Qabs (u n - u' n) + Qabs (v n - v' n))%Q _).
  - apply Qabs_triangle.
  - assert (Hs : Qlt (Qabs (u n - u' n) + Qabs (v n - v' n))
                     ((eps * (1 # 2)) + (eps * (1 # 2))))
      by (apply Qplus_lt_compat; [exact H1 | exact H2]).
    assert (Hrw2 : (((eps * (1 # 2)) + (eps * (1 # 2))) == eps)%Q) by ring.
    setoid_rewrite Hrw2 in Hs.
    exact Hs.
Qed.

(* ---- Definitional arithmetic of a constant difference: a + (-b) is pointwise a-b ---- *)

Lemma lw0_sin_const_plus_opp_const : forall a b : Q,
  real_eq (real_plus (real_const a) (real_opp (real_const b)))
          (real_const (a - b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_opp real_const].
  apply qeq_imp_qeqT. ring.
Qed.

(* ---- 10/3 - 4/3 == 2: the constant bridge (used by the right bank of the gap bisection) ---- *)

Lemma lw0_sin_ten_thirds_bridge :
  real_eq (real_plus (real_const (10 / 3)) (real_opp (real_const (4 / 3))))
          (real_const 2).
Proof.
  apply real_eq_of_zero_diff. intro n.
  vm_compute. reflexivity.
Qed.

(* ---- From t < pi_geom to 0 < pi_geom - t ----
   route: real_lt_plus_translate gives (-t) + t < (-t) + pi_geom;
   the left side equals zero via real_plus_opp, the right side is
   reordered via real_plus_comm. *)

Lemma lw0_sin_zero_lt_pi_minus : forall X : Real,
  real_lt X real_pi_geom ->
  real_lt real_zero (real_plus real_pi_geom (real_opp X)).
Proof.
  intros X Hp.
  apply (real_eq_lt_lt real_zero
    (real_plus (real_opp X) X)
    (real_plus real_pi_geom (real_opp X))).
  - apply (real_eq_trans real_zero
      (real_plus X (real_opp X)) (real_plus (real_opp X) X)).
    + apply (real_eq_sym _ _ (real_plus_opp X)).
    + apply real_plus_comm.
  - apply (real_lt_eq_lt
      (real_plus (real_opp X) X)
      (real_plus (real_opp X) real_pi_geom)
      (real_plus real_pi_geom (real_opp X))).
    + apply (real_lt_plus_translate (real_opp X) X real_pi_geom Hp).
    + apply real_plus_comm.
Qed.

(* ---- From 4/3 < t and pi_geom < 10/3 to pi_geom - t < 2 ---- *)

Lemma lw0_sin_pi_minus_lt_two : forall X : Real,
  real_lt (real_const (4 / 3)) X ->
  real_lt (real_plus real_pi_geom (real_opp X)) (real_const 2).
Proof.
  intros X H43.
  apply (real_lt_eq_lt
    (real_plus real_pi_geom (real_opp X))
    (real_plus (real_const (10 / 3)) (real_opp (real_const (4 / 3))))
    (real_const 2)).
  - apply (real_lt_plus_compat real_pi_geom (real_const (10 / 3))
             (real_opp X) (real_opp (real_const (4 / 3)))).
    + apply real_pi_geom_lt_ten_thirds.
    + apply (real_opp_lt_compat (real_const (4 / 3)) X H43).
  - apply lw0_sin_ten_thirds_bridge.
Qed.

(* ---- The gap bisection: every real lands in X < 2 or 4/3 < X ----
   the cauchy tail is sealed at 1/12 precision with the Qcompare
   three-way test of t_N against 5/3; 5/3 is the midpoint of 4/3 and
   2, leaving a 1/4 real gap to each bank. *)

Lemma lw0_gap_dichotomy : forall X : Real,
  Or (real_lt X (real_const 2)) (real_lt (real_const (4 / 3)) X).
Proof.
  intros X. destruct X as [u Hu].
  assert (Hpos12 : QltT 0 (1 # 12)%Q) by (apply Qlt_to_QltT; unfold Qlt; reflexivity).
  assert (Hpos6 : QltT 0 (1 # 6)%Q) by (apply Qlt_to_QltT; unfold Qlt; reflexivity).
  assert (Hc43 : ((4 / 3) == (4 # 3))%Q) by (vm_compute; reflexivity).
  destruct (Hu (1 # 12)%Q Hpos12) as [N HN].
  assert (HNN : NatLe N N) by (apply NatLe_lift, Nat.le_refl).
  destruct ((u N ?= (5 # 3))%Q) eqn:Hcmp.
  - (* case u N = 5/3: u m lands inside (5/3 - 1/12, 5/3 + 1/12), both banks reachable; take the right bank *)
    right. exists (1 # 6)%Q. split.
    + exact Hpos6.
    + exists N. intros m Hm.
      specialize (HN m N Hm HNN).
      change (projT1 (real_const (4 / 3)) m) with ((4 / 3)%Q).
      change (projT1 (existT (fun u0 : Qseq => cauchy u0) u Hu) m) with (u m).
      apply Qlt_to_QltT.
      assert (Habs : Qlt (Qabs (u m - u N)) (1 # 12))
        by (apply QltT_to_Qlt; exact HN).
      assert (Hlow : Qlt (- (1 # 12)) (u m - u N))
        by (apply QltT_to_Qlt; exact (q_abs_gt_neg _ _ Hpos12 HN)).
      assert (Hum : Qlt (u N + (- (1 # 12))) (u m)).
      { assert (H1 : Qlt ((- (1 # 12)) + u N) ((u m - u N) + u N))
          by (apply (proj2 (Qplus_lt_l _ _ _)); exact Hlow).
        assert (Hr1 : (((- (1 # 12)) + u N) == (u N + (- (1 # 12))))%Q) by ring.
        setoid_rewrite Hr1 in H1.
        assert (Hr2 : (((u m - u N) + u N) == u m)%Q) by ring.
        setoid_rewrite Hr2 in H1.
        exact H1. }
      assert (Hge : Qle ((5 # 3)) (u N)).
      { destruct (Qlt_le_dec (u N) (5 # 3)) as [Hc' | Hc'].
        - exfalso.
          assert (Hcc : (u N ?= 5 # 3)%Q = Lt)
            by (exact (proj1 (Qlt_alt (u N) (5 # 3)) Hc')).
          rewrite Hcmp in Hcc. discriminate Hcc.
        - exact Hc'. }
      assert (Hlelt : forall a0 b0 c0 d0 : Q,
        Qle a0 b0 -> Qlt (b0 + c0) d0 -> Qlt (a0 + c0) d0).
      { intros a0 b0 c0 d0 Hab Hbc.
        destruct (Qlt_le_dec a0 b0) as [Hl | Hl'].
        - apply (Qlt_trans _ (b0 + c0)).
          + apply (proj2 (Qplus_lt_l _ _ _)). exact Hl.
          + exact Hbc.
        - assert (Heqab : a0 == b0) by (apply Qle_antisym; [exact Hab | exact Hl']).
          assert (Hrc : ((a0 + c0) == (b0 + c0))%Q)
            by (rewrite Heqab; ring).
          setoid_rewrite Hrc.
          exact Hbc. }
      assert (Hge2 : Qlt ((5 # 3) + (- (1 # 12))) (u m))
        by (apply (Hlelt (5 # 3) (u N) (- (1 # 12)) (u m) Hge Hum)).
      assert (Hlit : Qlt ((4 # 3) + (1 # 6)) ((5 # 3) + (- (1 # 12))))
        by (unfold Qlt; reflexivity).
      assert (Hfin : Qlt ((4 # 3) + (1 # 6) + (- (4 # 3)))
                          (u m + (- (4 # 3))))
        by (apply (proj2 (Qplus_lt_l _ _ _));
            apply (Qlt_trans _ ((5 # 3) + (- (1 # 12))));
            [exact Hlit | exact Hge2]).
      assert (Hr3 : (((4 # 3) + (1 # 6) + (- (4 # 3))) == (1 # 6))%Q) by ring.
      setoid_rewrite Hr3 in Hfin.
      assert (Hr4 : ((u m + (- (4 # 3))) == (u m - (4 # 3)))%Q) by ring.
      setoid_rewrite Hr4 in Hfin.
      setoid_rewrite Hc43.
      exact Hfin.
  - (* case u N < 5/3: take the left bank X < 2 *)
    left. exists (1 # 6)%Q. split.
    + exact Hpos6.
    + exists N. intros m Hm.
      specialize (HN m N Hm HNN).
      change (projT1 (real_const 2) m) with 2%Q.
      change (projT1 (existT (fun u0 : Qseq => cauchy u0) u Hu) m) with (u m).
      apply Qlt_to_QltT.
      assert (Habs : Qlt (Qabs (u m - u N)) (1 # 12))
        by (apply QltT_to_Qlt; exact HN).
      (* to the bank: d < 0 gives d < 1/12 directly; d >= 0 replaces |d| by d pointwise *)
      assert (Hub : Qlt (u m - u N) (1 # 12)).
      { destruct (Qlt_le_dec (u m - u N) 0) as [Hnegd | Hnond].
        - apply (Qlt_le_trans _ 0 _).
          + exact Hnegd.
          + apply Qlt_le_weak. apply QltT_to_Qlt. exact Hpos12.
        - assert (Habsd : Qabs (u m - u N) == (u m - u N))
            by (apply Qabs_pos; exact Hnond).
          rewrite Habsd in Habs. exact Habs. }
      assert (Hum : Qlt (u m) (u N + (1 # 12))).
      { assert (H1 : Qlt ((u m - u N) + u N) ((1 # 12) + u N))
          by (apply (proj2 (Qplus_lt_l _ _ _)); exact Hub).
        assert (Hr1 : (((u m - u N) + u N) == u m)%Q) by ring.
        setoid_rewrite Hr1 in H1.
        assert (Hr2 : (((1 # 12) + u N) == (u N + (1 # 12)))%Q) by ring.
        setoid_rewrite Hr2 in H1.
        exact H1. }
      assert (HltN : Qlt (u N) ((5 # 3))) by (unfold Qlt; exact Hcmp).
      assert (Hlit : Qlt ((5 # 3) + (1 # 12)) (2 - (1 # 6)))
        by (unfold Qlt; reflexivity).
      assert (Hum2 : Qlt (u m) ((5 # 3) + (1 # 12))).
      { assert (H1' : Qlt (u N + (1 # 12)) ((5 # 3) + (1 # 12)))
          by (apply (proj2 (Qplus_lt_l _ _ _)); exact HltN).
        apply (Qlt_trans _ (u N + (1 # 12))).
        - exact Hum.
        - exact H1'. }
      assert (Hfin : Qlt (u m + (1 # 6)) (2 - (1 # 6) + (1 # 6)))
        by (apply (proj2 (Qplus_lt_l _ _ _));
            apply (Qlt_trans _ ((5 # 3) + (1 # 12)));
            [exact Hum2 | exact Hlit]).
      assert (Hr3 : ((2 - (1 # 6) + (1 # 6)) == 2)%Q) by ring.
      setoid_rewrite Hr3 in Hfin.
      assert (Hfin2 : Qlt ((1 # 6) + u m) ((2 - u m) + u m)).
      { assert (Hr4 : (((2 - u m) + u m) == 2)%Q) by ring.
        setoid_rewrite Hr4.
        assert (Hr5 : (((1 # 6) + u m) == (u m + (1 # 6)))%Q) by ring.
        setoid_rewrite Hr5.
        exact Hfin. }
      exact (proj1 (Qplus_lt_l _ _ _) Hfin2).
  - (* case u N > 5/3: take the right bank 4/3 < X *)
    right. exists (1 # 6)%Q. split.
    + exact Hpos6.
    + exists N. intros m Hm.
      specialize (HN m N Hm HNN).
      change (projT1 (real_const (4 / 3)) m) with ((4 / 3)%Q).
      change (projT1 (existT (fun u0 : Qseq => cauchy u0) u Hu) m) with (u m).
      apply Qlt_to_QltT.
      assert (Habs : Qlt (Qabs (u m - u N)) (1 # 12))
        by (apply QltT_to_Qlt; exact HN).
      assert (Hlow : Qlt (- (1 # 12)) (u m - u N))
        by (apply QltT_to_Qlt; exact (q_abs_gt_neg _ _ Hpos12 HN)).
      assert (Hum : Qlt (u N + (- (1 # 12))) (u m)).
      { assert (H1 : Qlt ((- (1 # 12)) + u N) ((u m - u N) + u N))
          by (apply (proj2 (Qplus_lt_l _ _ _)); exact Hlow).
        assert (Hr1 : (((- (1 # 12)) + u N) == (u N + (- (1 # 12))))%Q) by ring.
        setoid_rewrite Hr1 in H1.
        assert (Hr2 : (((u m - u N) + u N) == u m)%Q) by ring.
        setoid_rewrite Hr2 in H1.
        exact H1. }
      assert (Hge : Qle ((5 # 3)) (u N)).
      { destruct (Qlt_le_dec (u N) (5 # 3)) as [Hc' | Hc'].
        - exfalso.
          assert (Hcc : (u N ?= 5 # 3)%Q = Lt)
            by (exact (proj1 (Qlt_alt _ _) Hc')).
          congruence.
        - exact Hc'. }
      assert (Hlelt : forall a0 b0 c0 d0 : Q,
        Qle a0 b0 -> Qlt (b0 + c0) d0 -> Qlt (a0 + c0) d0).
      { intros a0 b0 c0 d0 Hab Hbc.
        destruct (Qlt_le_dec a0 b0) as [Hl | Hl'].
        - apply (Qlt_trans _ (b0 + c0)).
          + apply (proj2 (Qplus_lt_l _ _ _)). exact Hl.
          + exact Hbc.
        - assert (Heqab : a0 == b0) by (apply Qle_antisym; [exact Hab | exact Hl']).
          assert (Hrc : ((a0 + c0) == (b0 + c0))%Q)
            by (rewrite Heqab; ring).
          setoid_rewrite Hrc.
          exact Hbc. }
      assert (Hge2 : Qlt ((5 # 3) + (- (1 # 12))) (u m))
        by (apply (Hlelt (5 # 3) (u N) (- (1 # 12)) (u m) Hge Hum)).
      assert (Hlit : Qlt ((4 # 3) + (1 # 6)) ((5 # 3) + (- (1 # 12))))
        by (unfold Qlt; reflexivity).
      assert (Hfin : Qlt ((4 # 3) + (1 # 6) + (- (4 # 3)))
                          (u m + (- (4 # 3))))
        by (apply (proj2 (Qplus_lt_l _ _ _));
            apply (Qlt_trans _ ((5 # 3) + (- (1 # 12))));
            [exact Hlit | exact Hge2]).
      assert (Hr3 : (((4 # 3) + (1 # 6) + (- (4 # 3))) == (1 # 6))%Q) by ring.
      setoid_rewrite Hr3 in Hfin.
      assert (Hr4 : ((u m + (- (4 # 3))) == (u m - (4 # 3)))%Q) by ring.
      setoid_rewrite Hr4 in Hfin.
      setoid_rewrite Hc43.
      exact Hfin.
Qed.

(* ---- reflection：sin X == sin(pi_geom - X) ----
   one instantiation of the angle-addition formula:
   sin(pi + (-X)) = sin(pi)cos(-X) + cos(pi)sin(-X); after the endpoint
   values sin(pi) = 0 and cos(pi) = -1 are substituted there remains
   0·cos(-X) + (-1)·sin(-X) == 0 + (-1)·(-sin X) == sin X。 *)

Lemma lw0_sin_reflection : forall X : Real,
  real_eq (cauchy_real_sin X)
          (cauchy_real_sin (real_plus real_pi_geom (real_opp X))).
Proof.
  intros X. apply real_eq_sym.
  apply (real_eq_trans
    (cauchy_real_sin (real_plus real_pi_geom (real_opp X)))
    (real_plus (real_mult (cauchy_real_sin real_pi_geom)
                           (cauchy_real_cos (real_opp X)))
               (real_mult (cauchy_real_cos real_pi_geom)
                          (cauchy_real_sin (real_opp X))))
    (cauchy_real_sin X)).
  - apply rs_add_sin.
  - apply (real_eq_trans
      (real_plus (real_mult (cauchy_real_sin real_pi_geom)
                             (cauchy_real_cos (real_opp X)))
                 (real_mult (cauchy_real_cos real_pi_geom)
                            (cauchy_real_sin (real_opp X))))
      (real_plus real_zero (cauchy_real_sin X))
      (cauchy_real_sin X)).
    + apply lw0_sin_plus_eq_compat.
      * (* sin(pi)·cos(-X) == 0·cos(-X) == 0 *)
        apply (real_eq_trans
          (real_mult (cauchy_real_sin real_pi_geom)
                     (cauchy_real_cos (real_opp X)))
          (real_mult real_zero (cauchy_real_cos (real_opp X)))
          real_zero).
        -- apply (qtr_mult_eq_compat_l (cauchy_real_sin real_pi_geom)
                    real_zero (cauchy_real_cos (real_opp X))
                    b5p_sin_pi_geom_zero).
        -- apply (real_eq_trans
             (real_mult real_zero (cauchy_real_cos (real_opp X)))
             (real_mult (cauchy_real_cos (real_opp X)) real_zero)
             real_zero).
           ++ apply real_mult_comm.
           ++ apply real_mult_zero.
      * (* cos(pi)·sin(-X) == (-sin X)·(-1) == sin X *)
        apply (real_eq_trans
          (real_mult (cauchy_real_cos real_pi_geom)
                     (cauchy_real_sin (real_opp X)))
          (real_mult (real_opp (cauchy_real_sin X)) (real_opp real_one))
          (cauchy_real_sin X)).
        -- apply (real_eq_trans
             (real_mult (cauchy_real_cos real_pi_geom)
                        (cauchy_real_sin (real_opp X)))
             (real_mult (real_opp real_one) (cauchy_real_sin (real_opp X)))
             (real_mult (real_opp (cauchy_real_sin X)) (real_opp real_one))).
           ++ apply (qtr_mult_eq_compat_l (cauchy_real_cos real_pi_geom)
                       (real_opp real_one) (cauchy_real_sin (real_opp X))
                       b5p_cos_pi_geom_neg_one).
           ++ apply (real_eq_trans
                (real_mult (real_opp real_one) (cauchy_real_sin (real_opp X)))
                (real_mult (cauchy_real_sin (real_opp X)) (real_opp real_one))
                (real_mult (real_opp (cauchy_real_sin X)) (real_opp real_one))).
              ** apply real_mult_comm.
              ** apply (qtr_mult_eq_compat_l (cauchy_real_sin (real_opp X))
                          (real_opp (cauchy_real_sin X)) (real_opp real_one)
                          (real_sin_opp X)).
        -- (* (-sin X)*(-1) == sin X: the double negation cancels, assembled from two in-library multiplication negation lemmas *)
           apply (real_eq_trans
             (real_mult (real_opp (cauchy_real_sin X)) (real_opp real_one))
             (real_opp (real_opp (cauchy_real_sin X)))
             (cauchy_real_sin X)).
           ++ apply real_mult_opp_one_l.
           ++ apply real_opp_opp.
    + apply (real_eq_trans
        (real_plus real_zero (cauchy_real_sin X))
        (real_plus (cauchy_real_sin X) real_zero)
        (cauchy_real_sin X)).
      * apply real_plus_comm.
      * apply real_plus_zero.
Qed.

(* ---- The main statement: sin is pointwise positive inside (0, pi_geom) ----
   gap bisection: the X < 2 branch is supplied directly by the
   in-library positivity over the (0,2) segment; the 4/3 < X branch
   has pi_geom - X < 10/3 - 4/3 = 2 and pi_geom - X > 0, and the
   reflection carries the positivity from sin(pi_geom - X) back to
   sin X. *)

Lemma lw0_sin_pos_pi : forall X : Real,
  real_lt real_zero X -> real_lt X real_pi_geom ->
  real_lt real_zero (cauchy_real_sin X).
Proof.
  intros X H0 Hp.
  destruct (lw0_gap_dichotomy X) as [H2 | H43].
  - exact (real_sin_pos_lt_two X H0 H2).
  - assert (HY : real_lt real_zero
                   (cauchy_real_sin (real_plus real_pi_geom (real_opp X)))).
    { apply (real_sin_pos_lt_two (real_plus real_pi_geom (real_opp X))).
      - apply lw0_sin_zero_lt_pi_minus. exact Hp.
      - apply lw0_sin_pi_minus_lt_two. exact H43. }
    exact (real_lt_eq_lt real_zero
            (cauchy_real_sin (real_plus real_pi_geom (real_opp X)))
            (cauchy_real_sin X)
            HY (real_eq_sym _ _ (lw0_sin_reflection X))).
Qed.

(* Closing self-check: explicit verification of the assumption face of the main statement family (the in-library DecBridge6 embedded-section style) *)
Print Assumptions lw0_sin_reflection.
Print Assumptions lw0_gap_dichotomy.
Print Assumptions lw0_sin_pos_pi.
