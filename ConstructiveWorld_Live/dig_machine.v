(* Mission.  Constructive extractable form of the Beukers-type double    *)
(* integral of (x(1-x)y(1-y))^n / (1-xy)^(n+1).  Face 1 sup              *)
(* certificate dig_sup: 676*N <= 61*(1-xy).  With u=1-x, v=1-y,          *)
(* m=u+v, k=uv it becomes G = 61m - k(737-676m+676k); from               *)
(* k <= m^2/4 and B* = (676/4)(m-2)^2+61 >= 61 it is bounded             *)
(* by (m/16)*H(m), H = 976-2948m+2704m^2-676m^3, two closing             *)
(* cases (m <= 4/5: positive quadratic form; m >= 4/5: inner             *)
(* bracket >= 1352/5).  Face 2 dig_pointwise_decay:                      *)
(* 4*(676/61)^n*N^(n+1) <= (1-xy)^(n+2) (dmw2_N4_le_dsq base             *)
(* times the sup certificate).  Face 3 dig_carrier_decay:                *)
(* F_{m+1,M} <= (1/4)*(61/676)^m (zb2 truncation-family                  *)
(* interface).  Verdict dig_comp_verdict: (9/4)*(549/676)^m < 1          *)
(* for m >= 4 (the 1/11 variant needs m >= 5; sharpness anchors          *)
(* in this file).  Separation dig_sep_small: d <= 3^(m+1) times          *)
(* the family bound implies d^2*Isum < 1.                                *)
(* Rate theta = 61/676 (0.0902367...) beats 1/11 (0.0909091...) toward   *)
(* ((sqrt(5)-1)/2)^5 (0.0901699...); discriminants 61*11 = 671 < 676,    *)
(* 15127^2 > 6760^2*5 are exact here.  Scope: the bound feeds            *)
(* downstream measure estimates; the mu(pi) line instantiates the        *)
(* denominator-growth-vs-decay-rate verdict; Rhin-Viola's method is      *)
(* out of scope; no "first" or "stronger than" claims.                   *)
(* Dependencies.  Stdlib QArith/ZArith/Arith/Lia/Setoid; S01_BaseRing,   *)
(* S02_CauchyComplete, S03_QExp, BeukersLists, abl_z2_truncfam,          *)
(* abl_z2_itg_carrier, abl_dmw2_pointwise_sharp, abl_dmw2_sharpen_decay. *)
(* References.  Beukers, Bull. London Math. Soc. 11 (1979); sharpened    *)
(* generalization of the 1/11 variant; Hanson 1972 lcm <= 3^n step reused. *)
(* Constructivity.  All statements Set-carried; Print Assumptions all    *)
(* Closed; Separate Extraction Obj.magic=0; no real-number layer,        *)
(* no classical logic.                                                   *)
(* Build.  rocq c -native-compiler no -q -Q . "" dig_machine.v           *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_truncfam abl_z2_itg_carrier.
Require Import abl_dmw2_pointwise_sharp abl_dmw2_sharpen_decay.

Open Scope Q_scope.

(* ============================================================ *)
(* Sec 0. Machinery slots: the sharpened pointwise constant       *)
(* theta := 61/676 and the machinery weight                       *)
(* ============================================================ *)

(* The machinery's single tunable constant: the pointwise theta.      *)
(* 61/676 is a rational approximation from above of the known         *)
(* optimal theta* = phi^-5 = 0.0901699... (sharper than the 1/11      *)
(* integer variant).  Exact discrimination:                           *)
(*   61/676 < 1/11  iff  61*11 = 671 < 676;                           *)
(*   theta* < 61/676 iff (5*sqrt(5)-11)/2 < 61/676                    *)
(*   iff 15127^2 > 6760^2*5.                                          *)
Definition dig_theta : Q := (61#676).

(* Machinery weight output: the family bound (1/4)*theta^m (feeds     *)
(* downstream measure estimates) *)
Definition dig_weight (m : nat) : Q := (1#4) * q_pow dig_theta m.

Lemma dig_theta_ge0 : QleT' 0 dig_theta.
Proof. exact (id_refl (A:=bool) (x:=Qle_bool 0 dig_theta)). Qed.

Lemma dig_theta_le_one : QleT' dig_theta 1.
Proof. exact (id_refl (A:=bool) (x:=Qle_bool dig_theta 1)). Qed.

Lemma dig_weight_ge0 : forall m : nat, QleT' 0 (dig_weight m).
Proof.
  intro m. apply Qle_to_QleT'. apply Qmult_le_0_compat.
  - unfold Qle. simpl. lia.
  - apply QleT'_to_Qle. apply q_pow_nonneg. exact dig_theta_ge0.
Qed.

(* Slot sharpness anchor: the new weight (1/4)(61/676) <= the old     *)
(* weight (1/4)(1/11) (same slot as the 1/11 variant; decidable       *)
(* Qle_bool judgment; sharpness record at the theta level) *)
Lemma dig_weight_sharpen :
  QleT' ((1#4) * q_pow dig_theta 1) ((1#4) * q_pow (1#11) 1).
Proof.
  exact (id_refl (A:=bool)
    (x:=Qle_bool ((1#4) * q_pow dig_theta 1) ((1#4) * q_pow (1#11) 1))).
Qed.

(* ============================================================ *)
(* Sec A. sup certificate face (main theorem): 676*N <= 61*(1-xy), *)
(* i.e. N/(1-xy) <= 61/676                                         *)
(* ============================================================ *)

(* sup certificate (substituted form): 0<=u,v<=1 implies              *)
(* 676*u(1-u)v(1-v) <= 61*(u+v-uv). *)
Lemma dig_sup_uv : forall u v : Q,
  prod (QleT' 0 u) (QleT' u 1) -> prod (QleT' 0 v) (QleT' v 1) ->
  QleT' (676 * u * (1 - u) * v * (1 - v)) (61 * (u + v - u * v)).
Proof.
  intros u v [Hu1T Hu2T] [Hv1T Hv2T].
  pose proof (QleT'_to_Qle _ _ Hu1T) as Hu1.
  pose proof (QleT'_to_Qle _ _ Hu2T) as Hu2.
  pose proof (QleT'_to_Qle _ _ Hv1T) as Hv1.
  pose proof (QleT'_to_Qle _ _ Hv2T) as Hv2.
  apply Qle_to_QleT'.
  assert (Hk0 : 0 <= u * v) by (apply QleT'_to_Qle; apply dmw2_mult2_ge0; assumption).
  assert (Hm0 : 0 <= u + v).
  { apply (Qle_trans 0 (0 + 0) (u + v)).
    - rewrite Qplus_0_l. apply Qle_refl.
    - apply (Qplus_le_compat 0 u 0 v); assumption. }
  assert (Hm2 : (u + v) <= 2).
  { apply (Qle_trans (u + v) (1 + 1) 2).
    - apply (Qplus_le_compat u 1 v 1); assumption.
    - assert (Heq : 1 + 1 == 2) by ring.
      rewrite Heq. apply Qle_refl. }
  assert (H4k : 0 <= (u+v)*(u+v) - 4*(u*v)).
  { assert (Heq : (u+v)*(u+v) - 4*(u*v) == (u-v)*(u-v)) by ring.
    rewrite Heq. apply QleT'_to_Qle. apply dmw2_sq_ge0. }
  (* Linear consequences of H4k: 676k <= (676/4)m^2 and k <= m^2/4 *)
  assert (HBB : 676 * (u*v) <= (676#4)*(u+v)*(u+v)).
  { apply (Qle_trans (676 * (u*v))
      (676 * (u*v) + (676#4) * ((u+v)*(u+v) - 4*(u*v)))
      ((676#4)*(u+v)*(u+v))).
    - apply QleT'_to_Qle. apply dmw2_add_ge0_le.
      apply QleT'_to_Qle; apply (dmw2_mult2_ge0 (676#4) ((u+v)*(u+v) - 4*(u*v)))
      ; [ apply QleT'_to_Qle; apply (dmw2_qmake_pos 676 4); lia | exact H4k ].
    - assert (Heq : 676 * (u*v) + (676#4) * ((u+v)*(u+v) - 4*(u*v))
                 == (676#4)*(u+v)*(u+v)) by ring.
      rewrite Heq. apply Qle_refl. }
  assert (Hk_le : u * v <= ((u+v)*(u+v)) * (1#4)).
  { apply (Qle_trans (u * v)
      (u * v + ((u+v)*(u+v) - 4*(u*v)) * (1#4))
      (((u+v)*(u+v)) * (1#4))).
    - apply QleT'_to_Qle. apply dmw2_add_ge0_le.
      assert (Heqc : ((u+v)*(u+v) - 4*(u*v)) * (1#4)
                  == (1#4) * ((u+v)*(u+v) - 4*(u*v))) by ring.
      rewrite Heqc.
      apply QleT'_to_Qle; apply (dmw2_mult2_ge0 (1#4) ((u+v)*(u+v) - 4*(u*v)))
      ; [ apply QleT'_to_Qle; apply (dmw2_qmake_pos 1 4); lia | exact H4k ].
    - assert (Heq : u * v + ((u+v)*(u+v) - 4*(u*v)) * (1#4)
                 == ((u+v)*(u+v)) * (1#4)) by ring.
      rewrite Heq. apply Qle_refl. }
  (* Factor bound: B* = 737-676m+(676/4)m^2 = (676/4)(m-2)^2+61 >= 61 > 0 *)
  assert (HBp : 0 <= 737 - 676*(u+v) + (676#4)*(u+v)*(u+v)).
  { assert (Hid0 : 737 - 676*(u+v) + (676#4)*(u+v)*(u+v)
                == (676#4)*((2-(u+v))*(2-(u+v))) + 61) by ring.
    rewrite Hid0.
    assert (Hs : 0 <= (2-(u+v))*(2-(u+v))) by (apply QleT'_to_Qle; apply dmw2_sq_ge0).
    assert (HX : 0 <= (676#4)*((2-(u+v))*(2-(u+v)))).
    { apply QleT'_to_Qle; apply (dmw2_mult2_ge0 (676#4) ((2-(u+v))*(2-(u+v))))
      ; [ apply QleT'_to_Qle; apply (dmw2_qmake_pos 676 4); lia | exact Hs ]. }
    apply (Qle_trans 0 ((676#4)*((2-(u+v))*(2-(u+v))))
                      ((676#4)*((2-(u+v))*(2-(u+v))) + 61)).
    - exact HX.
    - apply QleT'_to_Qle. apply dmw2_add_ge0_le. apply QleT'_to_Qle. apply (dmw2_qmake_pos 61 1); lia. }
  assert (HBs : 737 - 676*(u+v) + 676*(u*v)
             <= 737 - 676*(u+v) + (676#4)*(u+v)*(u+v)).
  { apply (Qplus_le_compat (737 - 676*(u+v)) (737 - 676*(u+v))
             (676*(u*v)) ((676#4)*(u+v)*(u+v)))
    ; [ apply Qle_refl | exact HBB ]. }
  (* Step 1: k*B <= k*B* *)
  assert (HkBB : (u*v) * (737 - 676*(u+v) + 676*(u*v))
              <= (u*v) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))).
  { pose proof (Qmult_le_compat_r (737 - 676*(u+v) + 676*(u*v))
                  (737 - 676*(u+v) + (676#4)*(u+v)*(u+v)) (u*v) HBs Hk0) as H.
    assert (Heq1 : (u*v) * (737 - 676*(u+v) + 676*(u*v))
                == (737 - 676*(u+v) + 676*(u*v)) * (u*v)) by ring.
    assert (Heq2 : (u*v) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))
                == (737 - 676*(u+v) + (676#4)*(u+v)*(u+v)) * (u*v)) by ring.
    rewrite <- Heq1, <- Heq2 in H. exact H. }
  (* Step 2: k*B* <= (m^2/4)*B* *)
  assert (HkB2 : (u*v) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))
              <= (((u+v)*(u+v)) * (1#4)) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))).
  { pose proof (Qmult_le_compat_r (u*v) (((u+v)*(u+v)) * (1#4))
                  (737 - 676*(u+v) + (676#4)*(u+v)*(u+v)) Hk_le HBp) as H.
    exact H. }
  (* The remaining one-variable expression is nonnegative (two cases,   *)
(* m <= 4/5 and m >= 4/5) *)
  assert (Hlow : 0 <= ((u+v) * (1#16))
                   * (976 - 2948*(u+v) + 2704*(u+v)*(u+v)
                            - 676*(u+v)*(u+v)*(u+v))).
  { destruct (Qlt_le_dec (u+v) (4#5)) as [Hm45 | Hm45].
    - (* Case 1, m <= 4/5: z = 4/5-m,                                       *)
(* H = 256/125-(2012/25)z+(5408/5)z^2+676z^3 *)
      assert (Hz0 : 0 <= (4#5) - (u+v))
        by (apply QleT'_to_Qle; apply (dmw2_le_sub (u+v) (4#5)); exact (Qlt_le_weak _ _ Hm45)).
      assert (HidB : 976 - 2948*(u+v) + 2704*(u+v)*(u+v) - 676*(u+v)*(u+v)*(u+v)
                  == (256#125) - (2012#25)*((4#5)-(u+v))
                     + (5408#5)*(((4#5)-(u+v))*((4#5)-(u+v)))
                     + 676*(((4#5)-(u+v))*((4#5)-(u+v))*((4#5)-(u+v))))
        by ring.
      assert (Hcube0 : 0 <= (((4#5)-(u+v))*((4#5)-(u+v)))*((4#5)-(u+v))).
      { apply Qmult_le_0_compat.
        - apply QleT'_to_Qle. apply dmw2_sq_ge0.
        - exact Hz0. }
      assert (Hcube : 0 <= 676*(((4#5)-(u+v))*((4#5)-(u+v))*((4#5)-(u+v)))).
      { apply QleT'_to_Qle; apply (dmw2_mult2_ge0 676); [ apply (QleT'_to_Qle _ _ (dmw2_nat_pos 676)) | exact Hcube0 ]. }
      assert (Hsq : 0 <= (((4#5)-(u+v))-(503#13520))*(((4#5)-(u+v))-(503#13520)))
        by (apply QleT'_to_Qle; apply dmw2_sq_ge0).
      assert (Hin : 0 <= (5408#5)*(((4#5)-(u+v))-(503#13520))
                                 *(((4#5)-(u+v))-(503#13520))).
      { assert (Hasso : (5408#5)*(((4#5)-(u+v))-(503#13520))
                                   *(((4#5)-(u+v))-(503#13520))
                     == (5408#5)*((((4#5)-(u+v))-(503#13520))
                                   *(((4#5)-(u+v))-(503#13520)))) by ring.
        rewrite Hasso.
        apply QleT'_to_Qle; apply (dmw2_mult2_ge0 (5408#5)
                ((((4#5)-(u+v))-(503#13520))*(((4#5)-(u+v))-(503#13520))))
        ; [ apply QleT'_to_Qle; apply (dmw2_qmake_pos 5408 5); lia | exact Hsq ]. }
      assert (Hin2 : 0 <= (5408#5)*(((4#5)-(u+v))-(503#13520))
                                   *(((4#5)-(u+v))-(503#13520))
                          + (372412#676000)).
      { apply (Qle_trans 0
                 ((5408#5)*(((4#5)-(u+v))-(503#13520))
                           *(((4#5)-(u+v))-(503#13520))) _).
        - exact Hin.
        - apply QleT'_to_Qle. apply (dmw2_add_ge0_le
                   ((5408#5)*(((4#5)-(u+v))-(503#13520))
                             *(((4#5)-(u+v))-(503#13520)))
                   (372412#676000)).
          apply QleT'_to_Qle. apply (dmw2_qmake_pos 372412 676000); lia. }
      assert (Hquad : 0 <= (256#125) - (2012#25)*((4#5)-(u+v))
                           + (5408#5)*(((4#5)-(u+v))*((4#5)-(u+v)))).
      { assert (Hsos : (256#125) - (2012#25)*((4#5)-(u+v))
                           + (5408#5)*(((4#5)-(u+v))*((4#5)-(u+v)))
                    == (5408#5)*(((4#5)-(u+v))-(503#13520))
                                *(((4#5)-(u+v))-(503#13520))
                       + (372412#676000))
          by ring.
        rewrite Hsos. exact Hin2. }
      assert (HH : 0 <= 976 - 2948*(u+v) + 2704*(u+v)*(u+v)
                        - 676*(u+v)*(u+v)*(u+v)).
      { rewrite HidB.
        apply (Qle_trans _ ((256#125) - (2012#25)*((4#5)-(u+v))
                 + (5408#5)*(((4#5)-(u+v))*((4#5)-(u+v))))).
        - exact Hquad.
        - apply QleT'_to_Qle. apply dmw2_add_ge0_le. exact Hcube. }
      apply Qmult_le_0_compat.
      + apply QleT'_to_Qle; apply (dmw2_mult2_ge0 (u+v) (1#16))
        ; [ exact Hm0 | apply QleT'_to_Qle; apply (dmw2_qmake_pos 1 16); lia ].
      + exact HH.
    - (* Case 2, m >= 4/5: s = m-4/5 lies in [0,6/5],                       *)
(* H = 256/125 + s(2012/25 + s(5408/5-676s)) >= 256/125 > 0 *)
      assert (Hs0 : 0 <= (u+v) - (4#5))
        by (apply QleT'_to_Qle; apply (dmw2_le_sub (4#5) (u+v)); exact Hm45).
      assert (Hs2 : (u+v) - (4#5) <= (6#5)).
      { apply QleT'_to_Qle. apply (dmw2_sub_ge0 ((u+v)-(4#5)) (6#5)).
        assert (Heq : (6#5) - ((u+v)-(4#5)) == 2 - (u+v)) by ring.
        rewrite Heq. apply QleT'_to_Qle. apply (dmw2_le_sub (u+v) 2). exact Hm2. }
      (* 5408/5 - 676s >= 5408/5 - 676*(6/5) = 1352/5 > 0 *)
      assert (Hb1 : (5408#5) - 676*(6#5) == (1352#5)) by ring.
      assert (Hb2 : 676*((u+v)-(4#5)) <= 676*(6#5)).
      { pose proof (Qmult_le_compat_r ((u+v)-(4#5)) (6#5) 676 Hs2
                      (QleT'_to_Qle _ _ (dmw2_nat_pos 676))) as H.
        assert (Hc : 676*((u+v)-(4#5)) == ((u+v)-(4#5)) * 676) by ring.
        assert (Hc2 : 676*(6#5) == (6#5) * 676) by ring.
        rewrite Hc, Hc2. exact H. }
      assert (Hbr : 0 <= (5408#5) - 676*((u+v)-(4#5))).
      { assert (Hb3 : (5408#5) - 676*(6#5) <= (5408#5) - 676*((u+v)-(4#5)))
          by (apply QleT'_to_Qle; apply (dmw2_minus_le (5408#5) (676*((u+v)-(4#5))) (676*(6#5)))
            ; exact Hb2).
        apply (Qle_trans 0 ((5408#5) - 676*(6#5))).
        - rewrite Hb1. apply QleT'_to_Qle. apply (dmw2_qmake_pos 1352 5); lia.
        - exact Hb3. }
      assert (Hbrk : 0 <= (2012#25)
                          + ((u+v)-(4#5))*((5408#5) - 676*((u+v)-(4#5)))).
      { apply (Qle_trans 0 (2012#25) _).
        - apply QleT'_to_Qle. apply (dmw2_qmake_pos 2012 25); lia.
        - apply QleT'_to_Qle. apply dmw2_add_ge0_le.
          apply QleT'_to_Qle; apply (dmw2_mult2_ge0 ((u+v)-(4#5)) ((5408#5) - 676*((u+v)-(4#5))))
          ; [ exact Hs0 | exact Hbr ]. }
      assert (HidA : 976 - 2948*(u+v) + 2704*(u+v)*(u+v) - 676*(u+v)*(u+v)*(u+v)
                  == (256#125) + ((u+v)-(4#5))
                       *((2012#25) + ((u+v)-(4#5))
                                      *((5408#5) - 676*((u+v)-(4#5)))))
        by ring.
      assert (Hterm : 0 <= ((u+v)-(4#5))
                       *((2012#25) + ((u+v)-(4#5))
                                      *((5408#5) - 676*((u+v)-(4#5))))).
      { apply QleT'_to_Qle; apply (dmw2_mult2_ge0 ((u+v)-(4#5)))
        ; [ exact Hs0 | exact Hbrk ]. }
      assert (HH : 0 <= 976 - 2948*(u+v) + 2704*(u+v)*(u+v)
                        - 676*(u+v)*(u+v)*(u+v)).
      { rewrite HidA.
        apply (Qle_trans 0 (256#125) _).
        - apply QleT'_to_Qle. apply (dmw2_qmake_pos 256 125); lia.
        - apply QleT'_to_Qle. apply dmw2_add_ge0_le. exact Hterm. }
      apply Qmult_le_0_compat.
      + apply QleT'_to_Qle; apply (dmw2_mult2_ge0 (u+v) (1#16))
        ; [ exact Hm0 | apply QleT'_to_Qle; apply (dmw2_qmake_pos 1 16); lia ].
      + exact HH. }
  (* Chained composition: 0 <= (m/16)H = 61m-(m^2/4)B* <= 61m-k*B*      *)
(* <= 61m-k*B = G *)
  assert (Hid2 : 61*(u+v) - (((u+v)*(u+v)) * (1#4))
                       * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))
              == ((u+v) * (1#16))
                   * (976 - 2948*(u+v) + 2704*(u+v)*(u+v)
                            - 676*(u+v)*(u+v)*(u+v)))
    by ring.
  assert (HG : 0 <= 61*(u + v - u*v) - 676*u*(1-u)*v*(1-v)).
  { assert (HeqG : 61*(u + v - u*v) - 676*u*(1-u)*v*(1-v)
                == 61*(u+v) - (u*v)*(737 - 676*(u+v) + 676*(u*v))) by ring.
    rewrite HeqG.
    apply (Qle_trans _ (((u+v) * (1#16))
              * (976 - 2948*(u+v) + 2704*(u+v)*(u+v)
                       - 676*(u+v)*(u+v)*(u+v)))).
    - exact Hlow.
    - rewrite <- Hid2.
      apply (Qle_trans _ (61*(u+v) - (u*v)*(737 - 676*(u+v) + (676#4)*(u+v)*(u+v)))).
      + apply QleT'_to_Qle; apply (dmw2_minus_le (61*(u+v))
          ((u*v) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v)))
          ((((u+v)*(u+v)) * (1#4)) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))))
        ; exact HkB2.
      + apply QleT'_to_Qle; apply (dmw2_minus_le (61*(u+v))
          ((u*v) * (737 - 676*(u+v) + 676*(u*v)))
          ((u*v) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))))
        ; exact HkBB. }
  (* Final step: 61(u+v-uv) = 676N + G >= 676N *)
  apply (Qle_trans (676*u*(1-u)*v*(1-v))
    (676*u*(1-u)*v*(1-v) + (61*(u + v - u*v) - 676*u*(1-u)*v*(1-v)))
    (61*(u + v - u*v))).
  - apply QleT'_to_Qle. apply dmw2_add_ge0_le. exact HG.
  - assert (HeqF : 676*u*(1-u)*v*(1-v)
                 + (61*(u + v - u*v) - 676*u*(1-u)*v*(1-v))
                == 61*(u + v - u*v)) by ring.
    rewrite HeqF. apply Qle_refl.
Qed.

(* sup certificate (original variables): 0<=x,y<=1 implies            *)
(* 676*x(1-x)y(1-y) <= 61*(1-xy) (substitution u=1-x, v=1-y) *)
Lemma dig_sup : forall x y : Q,
  prod (QleT' 0 x) (QleT' x 1) -> prod (QleT' 0 y) (QleT' y 1) ->
  QleT' (676 * x * (1 - x) * y * (1 - y)) (61 * (1 - x * y)).
Proof.
  intros x y [Hx1T Hx2T] [Hy1T Hy2T].
  pose proof (QleT'_to_Qle _ _ Hx1T) as Hx1.
  pose proof (QleT'_to_Qle _ _ Hx2T) as Hx2.
  pose proof (QleT'_to_Qle _ _ Hy1T) as Hy1.
  pose proof (QleT'_to_Qle _ _ Hy2T) as Hy2.
  apply Qle_to_QleT'.
  assert (Hu1 : 0 <= 1 - x) by (apply QleT'_to_Qle; apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hu2 : (1 - x) <= 1) by (apply QleT'_to_Qle; apply (dmw2_minus_ge0 x 1); exact Hx1).
  assert (Hv1 : 0 <= 1 - y) by (apply QleT'_to_Qle; apply (dmw2_le_sub y 1); exact Hy2).
  assert (Hv2 : (1 - y) <= 1) by (apply QleT'_to_Qle; apply (dmw2_minus_ge0 y 1); exact Hy1).
  assert (Hu1T : QleT' 0 (1 - x)) by (apply Qle_to_QleT'; exact Hu1).
  assert (Hu2T : QleT' (1 - x) 1) by (apply Qle_to_QleT'; exact Hu2).
  assert (Hv1T : QleT' 0 (1 - y)) by (apply Qle_to_QleT'; exact Hv1).
  assert (Hv2T : QleT' (1 - y) 1) by (apply Qle_to_QleT'; exact Hv2).
  pose proof (dig_sup_uv (1 - x) (1 - y) (pair Hu1T Hu2T) (pair Hv1T Hv2T)) as H.
  pose proof (QleT'_to_Qle _ _ H) as Hq.
  assert (HeqL : 676 * x * (1 - x) * y * (1 - y)
              == 676 * (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y)))
    by ring.
  assert (HeqR : (1 - x) + (1 - y) - (1 - x) * (1 - y) == 1 - x * y) by ring.
  rewrite HeqR in Hq.
  apply (Qle_trans (676 * x * (1 - x) * y * (1 - y))
                   (676 * (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y)))
                   (61 * (1 - x * y))).
  - apply QleT'_to_Qle. apply (dmw2_le_eq _ _ HeqL).
  - exact Hq.
Qed.

(* Numerical anchor near the golden point: at u=v=38/100 one has      *)
(* 61T-676N = 22363/781250 > 0 (a rational neighborhood of the true   *)
(* supremum point u=v=((sqrt(5)-1)/2)^2 = 0.382...; margin record,    *)
(* machine-checkable) *)
Lemma dig_anchor_gold :
  QltT 0 (61 * ((38#100) + (38#100) - (38#100)*(38#100))
      - 676 * ((38#100)*(1 - (38#100))*(38#100)*(1 - (38#100)))).
Proof.
  exact (id_refl (A:=bool)
    (x:=Qlt_bool 0 (61 * ((38#100) + (38#100) - (38#100)*(38#100))
      - 676 * ((38#100)*(1 - (38#100))*(38#100)*(1 - (38#100)))))).
Qed.

(* Half-point sup anchor: 676/16 <= 183/4 (direct decidable           *)
(* judgment at x=y=1/2) *)
Lemma dig_anchor_sup_half :
  QleT' (676 * (1#2)*(1 - (1#2))*(1#2)*(1 - (1#2)))
        (61 * ((1#2) + (1#2) - (1#2)*(1#2))).
Proof.
  exact (id_refl (A:=bool)
    (x:=Qle_bool (676 * (1#2)*(1 - (1#2))*(1#2)*(1 - (1#2)))
                 (61 * ((1#2) + (1#2) - (1#2)*(1#2))))).
Qed.

(* ============================================================ *)
(* Sec B. Composite face: 4*(676/61)^n*N^(n+1) <= (1-xy)^(n+2)     *)
(* (division-free form, Set-carried).  The base case reuses         *)
(* dmw2_N4_le_dsq (4N <= (1-xy)^2, constant-independent layer)      *)
(* directly; the step case multiplies by the (676/61)*N <= 1-xy     *)
(* slot of the sup certificate dig_sup.                             *)
(* ============================================================ *)

Theorem dig_pointwise_decay : forall (n : nat) (x y : Q),
  prod (QleT' 0 x) (QleT' x 1) -> prod (QleT' 0 y) (QleT' y 1) ->
  QleT' (4 * q_pow (676#61) n * q_pow (x*(1-x)*y*(1-y)) (Datatypes.S n))
        (q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))).
Proof.
  induction n as [| n IH]; intros x y [Hx1T Hx2T] [Hy1T Hy2T];
    pose proof (QleT'_to_Qle _ _ Hx1T) as Hx1;
    pose proof (QleT'_to_Qle _ _ Hx2T) as Hx2;
    pose proof (QleT'_to_Qle _ _ Hy1T) as Hy1;
    pose proof (QleT'_to_Qle _ _ Hy2T) as Hy2.
  - apply Qle_to_QleT'.
    assert (Heq1 : 4 * q_pow (676#61) 0 * q_pow (x*(1-x)*y*(1-y)) 1
                == 4 * x * (1-x) * y * (1-y)) by (cbn [q_pow]; ring).
    assert (Heq2 : q_pow (1 - x*y) 2 == (1 - x*y)*(1 - x*y))
      by (cbn [q_pow]; ring).
    rewrite Heq1, Heq2.
    apply QleT'_to_Qle. apply dmw2_N4_le_dsq; [ split; assumption | split; assumption ].
  - apply Qle_to_QleT'.
    pose proof (IH x y (pair Hx1T Hx2T) (pair Hy1T Hy2T)) as HIHT.
    pose proof (QleT'_to_Qle _ _ HIHT) as HIH.
    pose proof (dig_sup x y (pair Hx1T Hx2T) (pair Hy1T Hy2T)) as HsupT.
    pose proof (QleT'_to_Qle _ _ HsupT) as Hsup.
    (* Reciprocal slot conversion: (676/61)*N <= 1-xy (multiply           *)
(* 676N <= 61T by 1/61) *)
    assert (Hz61 : 0 <= (1#61)) by (unfold Qle; simpl; lia).
    pose proof (Qmult_le_compat_r (676 * x*(1-x)*y*(1-y)) (61 * (1 - x*y))
                                  (1#61) Hsup Hz61) as Hmul.
    assert (Hth : (676#61) * x*(1-x)*y*(1-y) <= 1 - x*y).
    { assert (E1 : (676#61) * x*(1-x)*y*(1-y)
                == 676 * x*(1-x)*y*(1-y) * (1#61)) by ring.
      assert (E2 : 61 * (1 - x*y) * (1#61) == 1 - x*y) by ring.
      apply (Qle_trans _ (676 * x*(1-x)*y*(1-y) * (1#61))).
      - apply QleT'_to_Qle. apply (dmw2_le_eq _ _ E1).
      - apply (Qle_trans _ (61 * (1 - x*y) * (1#61))).
        + exact Hmul.
        + apply QleT'_to_Qle. apply (dmw2_le_eq _ _ E2). }
    (* Nonnegativity face *)
    assert (Hxb : 0 <= 1 - x) by (apply QleT'_to_Qle; apply (dmw2_le_sub x 1); exact Hx2).
    assert (Hyb : 0 <= 1 - y) by (apply QleT'_to_Qle; apply (dmw2_le_sub y 1); exact Hy2).
    assert (Hxyb : 0 <= 1 - x*y)
      by (apply QleT'_to_Qle; apply (dmw2_le_sub (x*y) 1); apply QleT'_to_Qle; apply (dmw2_xy_le_1 x y); assumption).
    assert (HN0 : 0 <= x*(1-x)*y*(1-y))
      by (apply QleT'_to_Qle; apply (dmw2_mult4_ge0 x (1-x) y (1-y))
        ; [ exact Hx1 | exact Hxb | exact Hy1 | exact Hyb ]).
    assert (HL0 : 0 <= (676#61) * x*(1-x)*y*(1-y)).
    { apply QleT'_to_Qle. apply (dmw2_mult2_ge0 ((676#61) * x * (1-x) * y) (1-y)).
      - apply QleT'_to_Qle. apply (dmw2_mult2_ge0 ((676#61) * x * (1-x)) y).
        + apply QleT'_to_Qle. apply (dmw2_mult2_ge0 ((676#61) * x) (1-x)).
          * apply QleT'_to_Qle. apply (dmw2_mult2_ge0 (676#61) x).
            -- unfold Qle. simpl. lia.
            -- exact Hx1.
          * exact Hxb.
        + exact Hy1.
      - exact Hyb. }
    assert (HTn : 0 <= q_pow (1 - x*y) (Datatypes.S (Datatypes.S n)))
      by (apply QleT'_to_Qle; apply q_pow_nonneg; apply Qle_to_QleT'; exact Hxyb).
    (* Step 1: LHS_n*(676/61)N <= RHS_n*(676/61)N *)
    assert (S1 : (4 * q_pow (676#61) n * q_pow (x*(1-x)*y*(1-y)) (Datatypes.S n))
                   * ((676#61) * x*(1-x)*y*(1-y))
              <= q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))
                   * ((676#61) * x*(1-x)*y*(1-y))).
    { apply (Qmult_le_compat_r
               (4 * q_pow (676#61) n * q_pow (x*(1-x)*y*(1-y)) (Datatypes.S n))
               (q_pow (1 - x*y) (Datatypes.S (Datatypes.S n)))
               ((676#61) * x*(1-x)*y*(1-y)) HIH HL0). }
    (* Step 2: <= RHS_n*(1-xy) *)
    assert (S2 : q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))
                   * ((676#61) * x*(1-x)*y*(1-y))
              <= q_pow (1 - x*y) (Datatypes.S (Datatypes.S n)) * (1 - x*y)).
    { pose proof (Qmult_le_compat_r ((676#61) * x*(1-x)*y*(1-y)) (1 - x*y)
                 (q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))) Hth HTn) as H.
      assert (Hc1 : q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))
                      * ((676#61) * x*(1-x)*y*(1-y))
                  == ((676#61) * x*(1-x)*y*(1-y))
                       * q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))) by ring.
      assert (Hc2 : q_pow (1 - x*y) (Datatypes.S (Datatypes.S n)) * (1 - x*y)
                  == (1 - x*y) * q_pow (1 - x*y) (Datatypes.S (Datatypes.S n)))
        by ring.
      rewrite Hc1, Hc2. exact H. }
    (* Composition and power rewriting *)
    assert (Eg1 : 4 * q_pow (676#61) (Datatypes.S n) * q_pow (x*(1-x)*y*(1-y)) (Datatypes.S (Datatypes.S n))
               == (4 * q_pow (676#61) n * q_pow (x*(1-x)*y*(1-y)) (Datatypes.S n))
                  * ((676#61) * x*(1-x)*y*(1-y)))
      by (cbn [q_pow]; ring).
    rewrite Eg1.
    apply (Qle_trans _ (q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))
                          * ((676#61) * x*(1-x)*y*(1-y)))).
    + exact S1.
    + apply (Qle_trans _ (q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))
                            * (1 - x*y))).
      * exact S2.
      * assert (Hsq : q_pow (1 - x*y) (Datatypes.S (Datatypes.S (Datatypes.S n)))
                   == q_pow (1 - x*y) (Datatypes.S (Datatypes.S n)) * (1 - x*y))
          by (rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 - x*y)
                (Datatypes.S (Datatypes.S n)))); ring).
        rewrite Hsq. apply Qle_refl.
Qed.

(* Numerical anchor: for n=1 and x=y=1/2 the composite left side      *)
(* 4*(676/61)*N^2 equals 169/976, machine-checkable *)
Lemma dig_anchor_decay_n1 :
  QeqT (4 * q_pow (676#61) 1
    * q_pow ((1#2)*(1-(1#2))*(1#2)*(1-(1#2))) 2) (169#976).
Proof.
  assert (Hcore : 4 * q_pow (676#61) 1
    * q_pow ((1#2)*(1-(1#2))*(1#2)*(1-(1#2))) 2 == (169#976)).
  { vm_compute. reflexivity. }
  apply qeq_imp_qeqT. exact Hcore.
Qed.

(* ============================================================ *)
(* Sec C. Machinery assembly face: truncated integrand family      *)
(* bound, competition verdict, conditional separation              *)
(* ============================================================ *)

(* Truncated integrand family bound: 0<=x,y<=1 implies                *)
(* F_{m+1,M}(x,y) <= (1/4)*(61/676)^m (the 61/676-variant recast      *)
(* of dmw2_dc_carrier_decay) *)
Theorem dig_carrier_decay : forall (m M : nat) (x y : Q),
  prod (QleT' 0 x) (QleT' x 1) -> prod (QleT' 0 y) (QleT' y 1) ->
  QleT' (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y) (dig_weight m).
Proof.
  intros m M x y [Hx1T Hx2T] [Hy1T Hy2T].
  pose proof (QleT'_to_Qle _ _ Hx1T) as Hx1.
  pose proof (QleT'_to_Qle _ _ Hx2T) as Hx2.
  pose proof (QleT'_to_Qle _ _ Hy1T) as Hy1.
  pose proof (QleT'_to_Qle _ _ Hy2T) as Hy2.
  assert (Hxb : 0 <= 1 - x) by (apply QleT'_to_Qle; apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply QleT'_to_Qle; apply (dmw2_le_sub y 1); exact Hy2).
  assert (Hxy0 : 0 <= x * y) by (apply Qmult_le_0_compat; assumption).
  assert (Hxy1 : x * y <= 1) by (apply QleT'_to_Qle; apply (dmw2_xy_le_1 x y); assumption).
  pose proof (zb2_ps_bound (Datatypes.S m) M (x * y) (conj Hxy0 Hxy1)) as HpsT.
  pose proof (QleT'_to_Qle _ _ HpsT) as Hps.
  pose proof (qeqT_imp_qeq _ _ (zb2_beval_segl (Datatypes.S m) M x y)) as Hseg.
  assert (Hmerge : q_pow (x * (1 - x)) (Datatypes.S m) * q_pow (y * (1 - y)) (Datatypes.S m)
                == q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)).
  { rewrite <- (qeqT_imp_qeq _ _ (zb2_q_pow_mul (x * (1 - x)) (y * (1 - y)) (Datatypes.S m))).
    assert (Hrg : (x * (1 - x)) * (y * (1 - y)) == x * (1 - x) * y * (1 - y)) by ring.
    exact (qeqT_imp_qeq _ _ (q_pow_wd _ _ _ (qeq_imp_qeqT _ _ Hrg))). }
  rewrite Hmerge in Hseg.
  assert (HN0 : 0 <= x * (1 - x) * y * (1 - y))
    by (apply QleT'_to_Qle; apply (dmw2_mult4_ge0 x (1 - x) y (1 - y)); assumption).
  assert (HK0 : 0 <= q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
    by (apply QleT'_to_Qle; apply q_pow_nonneg; apply Qle_to_QleT'; exact HN0).
  (* (A): T^(m+2)*F <= N^(m+1) *)
  assert (HA : q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                 * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
            <= q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)).
  { assert (Hrw : q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                    * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
               == (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                    * zb2_ps (Datatypes.S m) M (x * y))
                  * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
      by (rewrite Hseg; ring).
    rewrite Hrw.
    apply (Qle_trans _ (1 * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))).
    - apply (Qmult_le_compat_r (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                                 * zb2_ps (Datatypes.S m) M (x * y))
                               1 (q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
                               Hps HK0).
    - assert (H1K : 1 * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)
                 == q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)) by ring.
      rewrite H1K. apply Qle_refl. }
  (* (B): 4*(676/61)^m*N^(m+1) <= T^(m+2) (machinery composite face) *)
  pose proof (dig_pointwise_decay m x y (pair Hx1T Hx2T) (pair Hy1T Hy2T)) as Hdec0T.
  pose proof (QleT'_to_Qle _ _ Hdec0T) as Hdec0.
  assert (HKt : 0 <= 4 * q_pow (676#61) m).
  { apply Qmult_le_0_compat.
    - unfold Qle. simpl. lia.
    - apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. unfold Qle. simpl. lia. }
  (* Composition: right-multiply (A) by 4*(676/61)^m, then chain        *)
(* with (B) *)
  assert (HC : (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                 * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
               * (4 * q_pow (676#61) m)
            <= q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))).
  { apply (Qle_trans _ (q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)
                           * (4 * q_pow (676#61) m))).
    - apply (Qmult_le_compat_r (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                                 * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
                               (q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
                               (4 * q_pow (676#61) m) HA HKt).
    - assert (Hcomm : q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)
                        * (4 * q_pow (676#61) m)
                   == 4 * q_pow (676#61) m
                        * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
        by ring.
      rewrite Hcomm. exact Hdec0. }
  (* Case split on the sign of T = 1-xy *)
  destruct (Qlt_le_dec 0 (1 - x * y)) as [Hpos | Hneg].
  - (* Main case: T > 0; cancel the positive factor, then multiply by     *)
(* the weight *)
    pose proof (QltT_to_Qlt _ _
      (dmw2_dc_qp_pos (Datatypes.S (Datatypes.S m)) (1 - x * y) Hpos)) as HPpos.
    assert (Hrg : (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                    * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
                  * (4 * q_pow (676#61) m)
               == (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                    * (4 * q_pow (676#61) m))
                  * q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))) by ring.
    rewrite Hrg in HC.
    pose proof (dmw2_dc_cancel_one
                  (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                    * (4 * q_pow (676#61) m))
                  (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))) HPpos HC) as H1.
    pose proof (QleT'_to_Qle _ _ (dig_weight_ge0 m)) as HW0.
    pose proof (Qmult_le_compat_r
                  (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                    * (4 * q_pow (676#61) m))
                  1 (dig_weight m) H1 HW0) as Hmult.
    assert (Hunit : (4 * q_pow (676#61) m) * dig_weight m == 1).
    { unfold dig_weight.
      assert (Hpm : q_pow (676#61) m * q_pow (61#676) m == 1).
      { rewrite <- (qeqT_imp_qeq _ _ (zb2_q_pow_mul (676#61) (61#676) m)).
        assert (H676 : (676#61) * (61#676) == 1) by ring.
        rewrite H676. apply dmw2_dc_qp_one. }
      assert (Hre : (4 * q_pow (676#61) m) * ((1#4) * q_pow (61#676) m)
                 == (4 * (1#4)) * (q_pow (676#61) m * q_pow (61#676) m)) by ring.
      rewrite Hre, Hpm. ring. }
    assert (Hlhs : (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                     * (4 * q_pow (676#61) m))
                   * dig_weight m
                == zb2_beval_l (zb2_segl (Datatypes.S m) M) x y).
    { assert (Hre2 : (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                       * (4 * q_pow (676#61) m))
                      * dig_weight m
                  == zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                     * ((4 * q_pow (676#61) m) * dig_weight m)) by ring.
      rewrite Hre2, Hunit. ring. }
    assert (Hrhs : 1 * dig_weight m == dig_weight m) by ring.
    rewrite Hrhs in Hmult. rewrite Hlhs in Hmult.
    apply Qle_to_QleT'. exact Hmult.
  - (* Boundary case: T <= 0 together with xy <= 1 forces T = 0, hence    *)
(* x = y = 1 and F = 0 *)
    assert (HT0 : 0 <= 1 - x * y) by (apply QleT'_to_Qle; apply (dmw2_le_sub (x * y) 1); exact Hxy1).
    assert (HTeq : 1 - x * y == 0) by (apply Qle_antisym; [ exact Hneg | exact HT0 ]).
    assert (Hxyeq : x * y == 1).
    { assert (Ha : 1 - (1 - x * y) == 1 - 0) by (rewrite HTeq; ring).
      assert (Hb : 1 - (1 - x * y) == x * y) by ring.
      assert (Hc : 1 - 0 == 1) by ring.
      rewrite Hb, Hc in Ha. exact Ha. }
    assert (Hle1 : x * y <= x).
    { pose proof (Qmult_le_compat_r y 1 x Hy2 Hx1) as Hq.
      assert (Hd1 : y * x == x * y) by ring. assert (Hd2 : 1 * x == x) by ring.
      rewrite Hd1, Hd2 in Hq. exact Hq. }
    assert (Hle2 : x * y <= y).
    { pose proof (Qmult_le_compat_r x 1 y Hx2 Hy1) as Hq.
      assert (Hd2 : 1 * y == y) by ring. rewrite Hd2 in Hq. exact Hq. }
    assert (Hx1e : x == 1).
    { apply Qle_antisym.
      - exact Hx2.
      - apply (Qle_trans 1 (x * y) x).
        + apply QleT'_to_Qle. apply (dmw2_le_eq 1 (x * y)). symmetry. exact Hxyeq.
        + exact Hle1. }
    assert (Hy1e : y == 1).
    { apply Qle_antisym.
      - exact Hy2.
      - apply (Qle_trans 1 (x * y) y).
        + apply QleT'_to_Qle. apply (dmw2_le_eq 1 (x * y)). symmetry. exact Hxyeq.
        + exact Hle2. }
    assert (HN0e : x * (1 - x) * y * (1 - y) == 0) by (rewrite Hx1e, Hy1e; ring).
    assert (Hq0 : q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m) == 0)
      by (rewrite HN0e; cbn [q_pow]; apply Qmult_0_l).
    assert (Hc0 : zb2_beval_l (zb2_segl (Datatypes.S m) M) x y == 0)
      by (rewrite Hseg, Hq0; apply Qmult_0_l).
    apply Qle_to_QleT'. rewrite Hc0.
    apply QleT'_to_Qle. apply dig_weight_ge0.
Qed.

(* Competition identity: 9^(m+1)*(1/4)*(61/676)^m = (9/4)*(549/676)^m *)
Lemma dig_comp_id : forall m : nat,
  QeqT (q_pow 9 (Datatypes.S m) * dig_weight m) ((9#4) * q_pow (549#676) m).
Proof.
  intro m.
  assert (Hcore : q_pow 9 (Datatypes.S m) * dig_weight m
               == (9#4) * q_pow (549#676) m).
  { unfold dig_weight.
    assert (Hpm : q_pow 9 m * q_pow (61#676) m == q_pow (549#676) m).
    { rewrite <- (qeqT_imp_qeq _ _ (zb2_q_pow_mul 9 (61#676) m)).
      assert (H911 : 9 * (61#676) == (549#676)) by ring.
      rewrite H911. reflexivity. }
    assert (Hre : q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (61#676) m)
               == (9 * (1#4)) * (q_pow 9 m * q_pow (61#676) m))
      by (rewrite (qeqT_imp_qeq _ _ (q_pow_succ 9 m)); ring).
    rewrite Hre, Hpm.
    assert (H94 : 9 * (1#4) == (9#4)) by ring.
    rewrite H94. reflexivity. }
  apply qeq_imp_qeqT. exact Hcore.
Qed.

(* Competition base case: (9/4)*(549/676)^4 =                         *)
(* 817583065209/835308258304 < 1 (literal judgment) *)
Lemma dig_comp_base : QltT ((9#4) * q_pow (549#676) 4) 1.
Proof.
  exact (id_refl (A:=bool) (x:=Qlt_bool ((9#4) * q_pow (549#676) 4) 1)).
Qed.

(* Base-case literal value anchor: recomputed by vm_compute           *)
(* (agrees with the exact value of the corresponding 1/11-variant     *)
(* section) *)
Lemma dig_comp_base_val :
  QeqT ((9#4) * q_pow (549#676) 4) (817583065209#835308258304).
Proof.
  assert (Hcore : (9#4) * q_pow (549#676) 4 == (817583065209#835308258304)).
  { vm_compute. reflexivity. }
  apply qeq_imp_qeqT. exact Hcore.
Qed.

(* Threshold sharpness anchor (new variant): (9/4)*(549/676)^3 =      *)
(* 1489222341/1235663104 >= 1 -- m=3 falls short, so the verdict      *)
(* threshold m >= 4 is sharp (decidable Qle_bool judgment) *)
Lemma dig_comp_base3_ge : QleT' 1 ((9#4) * q_pow (549#676) 3).
Proof.
  exact (id_refl (A:=bool) (x:=Qle_bool 1 ((9#4) * q_pow (549#676) 3))).
Qed.

(* Competition step: (9/4)*(549/676)^(m+1) <= (9/4)*(549/676)^m       *)
(* (both sides multiplied by 549/676 <= 1) *)
Lemma dig_comp_step : forall m : nat,
  QleT' ((9#4) * q_pow (549#676) (Datatypes.S m)) ((9#4) * q_pow (549#676) m).
Proof.
  intro m.
  assert (Hge0 : 0 <= (9#4) * q_pow (549#676) m).
  { apply Qmult_le_0_compat.
    - unfold Qle. simpl. lia.
    - apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. unfold Qle. simpl. lia. }
  assert (Hs676 : (549#676) <= 1) by (unfold Qle; simpl; lia).
  apply Qle_to_QleT'.
  assert (Hrw : (9#4) * q_pow (549#676) (Datatypes.S m)
             == (549#676) * ((9#4) * q_pow (549#676) m))
    by (rewrite (qeqT_imp_qeq _ _ (q_pow_succ (549#676) m)); ring).
  rewrite Hrw.
  pose proof (Qmult_le_compat_r (549#676) 1 ((9#4) * q_pow (549#676) m)
                Hs676 Hge0) as Hle.
  assert (Hr2 : 1 * ((9#4) * q_pow (549#676) m) == (9#4) * q_pow (549#676) m)
    by ring.
  rewrite Hr2 in Hle. exact Hle.
Qed.

(* Competition shift: (9/4)*(549/676)^(m+d) <= (9/4)*(549/676)^m      *)
(* (induction on the shift amount d) *)
Lemma dig_comp_drop : forall (d m : nat),
  QleT' ((9#4) * q_pow (549#676) (m + d)) ((9#4) * q_pow (549#676) m).
Proof.
  induction d as [| d IH]; intro m.
  - assert (Hd : (m + 0 = m)%nat) by apply Nat.add_0_r.
    rewrite Hd. apply Qle_to_QleT'. apply Qle_refl.
  - assert (Hs : (m + Datatypes.S d = Datatypes.S (m + d))%nat)
      by apply Nat.add_succ_r.
    rewrite Hs.
    apply (qleT'_trans ((9#4) * q_pow (549#676) (Datatypes.S (m + d)))
                       ((9#4) * q_pow (549#676) (m + d))
                       ((9#4) * q_pow (549#676) m)).
    + apply dig_comp_step.
    + apply IH.
Qed.

(* Competition verdict: m >= 4 implies (9/4)*(549/676)^m < 1          *)
(* (decidable le_lt_dec case split: m > 4 falls back to the base      *)
(* case by stepping down; m <= 4 forces m+1 = 4 and lands on the      *)
(* base case directly) *)
Lemma dig_comp_verdict : forall m : nat, NatLe 4 m -> QltT ((9#4) * q_pow (549#676) m) 1.
Proof.
  induction m as [| m IH]; intro Hm.
  - exfalso. pose proof (NatLe_drop 4 0 Hm). lia.
  - destruct (le_lt_dec 4 m) as [Hle | Hlt].
    + apply (qleT'_ltT_ltT ((9#4) * q_pow (549#676) (Datatypes.S m))
                           ((9#4) * q_pow (549#676) m) 1).
      * apply dig_comp_step.
      * apply IH. apply NatLe_lift. exact Hle.
    + pose proof (NatLe_drop 4 (Datatypes.S m) Hm) as HmD.
      assert (Heq : (Datatypes.S m = 4)%nat) by lia.
      rewrite Heq. exact dig_comp_base.
Qed.

(* Square weight: 0 <= d <= 3^n implies d^2 <= 9^n (same shape as     *)
(* dmw2_dc_weight_sq) *)
Lemma dig_weight_sq : forall (n : nat) (d : Q),
  QleT' 0 d -> QleT' d (q_pow 3 n) -> QleT' (d * d) (q_pow 9 n).
Proof.
  intros n d Hd0 Hd.
  pose proof (QleT'_to_Qle _ _ Hd0) as Hd0q.
  pose proof (QleT'_to_Qle _ _ Hd) as Hdq.
  assert (H30 : 0 <= q_pow 3 n) by (apply QleT'_to_Qle; apply q_pow_nonneg; apply Qle_to_QleT'; unfold Qle; simpl; lia).
  assert (H1 : d * d <= q_pow 3 n * d)
    by (apply (Qmult_le_compat_r d (q_pow 3 n) d); assumption).
  assert (H2 : q_pow 3 n * d <= q_pow 3 n * q_pow 3 n).
  { assert (H2' : d * q_pow 3 n <= q_pow 3 n * q_pow 3 n)
      by (apply (Qmult_le_compat_r d (q_pow 3 n) (q_pow 3 n)); assumption).
    assert (Hc : q_pow 3 n * d == d * q_pow 3 n) by ring.
    rewrite Hc. exact H2'. }
  assert (Hfin : d * d <= q_pow 3 n * q_pow 3 n)
    by (apply (Qle_trans _ (q_pow 3 n * d)); assumption).
  assert (Hsq : q_pow 3 n * q_pow 3 n == q_pow 9 n).
  { rewrite <- (qeqT_imp_qeq _ _ (zb2_q_pow_mul 3 3 n)).
    assert (H33 : 3 * 3 == 9) by ring.
    rewrite H33. reflexivity. }
  rewrite Hsq in Hfin. apply Qle_to_QleT'. exact Hfin.
Qed.

(* Main conditional-separation theorem (linear-form readout           *)
(* interface, explicit premises, 61/676 variant): let d satisfy       *)
(* 0 <= d <= 3^(m+1) (the Hanson-chain slot instantiated at the       *)
(* same type) and let the integral value Isum satisfy                 *)
(* Isum <= (1/4)(61/676)^m (the family-bound premise); then for       *)
(* m >= 4, d^2*Isum < 1.  (The 1/11-variant counterpart               *)
(* dmw2_dc_sep_small has threshold m >= 5: a shift from 5 to 4.) *)
Theorem dig_sep_small : forall (m M : nat) (d : Q),
  NatLe 4 m ->
  QleT' 0 d ->
  QleT' d (q_pow 3 (Datatypes.S m)) ->
  QleT' (zb2_Isum (Datatypes.S m) M) (dig_weight m) ->
  QltT (d * d * zb2_Isum (Datatypes.S m) M) 1.
Proof.
  intros m M d Hm Hd0 Hd HI.
  pose proof (dig_weight_sq (Datatypes.S m) d Hd0 Hd) as Hsq.
  pose proof (zb2_Isum_pos (Datatypes.S m) M) as HposT.
  pose proof (QleT'_to_Qle _ _ (qltT_leT' _ _ HposT)) as HposI.
  pose proof (QleT'_to_Qle _ _ HI) as HIq.
  pose proof (QleT'_to_Qle _ _ Hsq) as Hsqq.
  assert (H9 : 0 <= q_pow 9 (Datatypes.S m))
    by (apply QleT'_to_Qle; apply q_pow_nonneg; apply Qle_to_QleT'; unfold Qle; simpl; lia).
  assert (Hstep1 : d * d * zb2_Isum (Datatypes.S m) M
                <= q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M)
    by (apply (Qmult_le_compat_r (d * d) (q_pow 9 (Datatypes.S m))
                                 (zb2_Isum (Datatypes.S m) M) Hsqq HposI)).
  assert (Hstep2 : q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M
                <= q_pow 9 (Datatypes.S m) * dig_weight m).
  { assert (H2' : zb2_Isum (Datatypes.S m) M * q_pow 9 (Datatypes.S m)
               <= dig_weight m * q_pow 9 (Datatypes.S m))
      by (apply (Qmult_le_compat_r (zb2_Isum (Datatypes.S m) M) (dig_weight m)
                                   (q_pow 9 (Datatypes.S m)) HIq H9)).
    assert (Hc1 : q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M
               == zb2_Isum (Datatypes.S m) M * q_pow 9 (Datatypes.S m)) by ring.
    assert (Hc2 : dig_weight m * q_pow 9 (Datatypes.S m)
               == q_pow 9 (Datatypes.S m) * dig_weight m) by ring.
    rewrite Hc1, <- Hc2. exact H2'. }
  assert (Hchain : d * d * zb2_Isum (Datatypes.S m) M
                <= (9#4) * q_pow (549#676) m).
  { apply (Qle_trans _ (q_pow 9 (Datatypes.S m) * dig_weight m)).
    - apply (Qle_trans _ (q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M)).
      + exact Hstep1.
      + exact Hstep2.
    - exact (QleT'_to_Qle _ _ (dmw2_le_eq _ _ (qeqT_imp_qeq _ _ (dig_comp_id m)))). }
  pose proof (QltT_to_Qlt _ _ (dig_comp_verdict m Hm)) as Hv.
  pose proof (Qle_lt_trans _ _ _ Hchain Hv) as Hfin.
  apply Qlt_to_QltT. exact Hfin.
Qed.

(* ============================================================ *)
(* Sec D. Old-variant comparison and the assumption audit (zero     *)
(* global premises, re-checked)                                    *)
(* ============================================================ *)

(* Old-variant comparison (anchors cited directly from the           *)
(* 1/11-variant file): the threshold record moves from m >= 5        *)
(* (the 1/11 variant, old base (9/4)*(9/11)^5 < 1,                   *)
(* dmw2_dc_comp_base) to m >= 4 (this machinery, new base            *)
(* (9/4)*(549/676)^4 < 1, dig_comp_base); sharpness anchors are      *)
(* present on both sides. *)
Lemma dig_anchor_thresh_shift :
  QleT' ((1#4) * q_pow dig_theta 1) ((1#4) * q_pow (1#11) 1).
Proof. exact dig_weight_sharpen. Qed.

Separate Extraction dig_comp_verdict dig_sep_small dig_carrier_decay.

Print Assumptions dig_sup_uv.
Print Assumptions dig_sup.
Print Assumptions dig_pointwise_decay.
Print Assumptions dig_carrier_decay.
Print Assumptions dig_comp_id.
Print Assumptions dig_comp_base.
Print Assumptions dig_comp_base_val.
Print Assumptions dig_comp_base3_ge.
Print Assumptions dig_comp_step.
Print Assumptions dig_comp_drop.
Print Assumptions dig_comp_verdict.
Print Assumptions dig_weight_sq.
Print Assumptions dig_sep_small.
Print Assumptions dig_weight_sharpen.
Print Assumptions dig_anchor_gold.
Print Assumptions dig_anchor_sup_half.
Print Assumptions dig_anchor_decay_n1.
Print Assumptions dig_anchor_thresh_shift.
