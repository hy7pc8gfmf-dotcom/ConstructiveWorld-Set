(* gcl_coefficient.v -- the group-theoretic coefficient layer.  Mission. *)
(* Polynomial-tier coefficient layer of the Rhin-Viola group-structure   *)
(* permutation method (method core of the zeta(2) double integral        *)
(* 5.0193784), above the carrier face of the group machinery dig_machine: *)
(* forging the symmetrization operator and its improvement theorems on   *)
(* the pointwise control constant.  Carrier: the four-element            *)
(* permutation group V4 = <Gsw=(y,x), Gco=(1-x,1-y)> (Gsc = Gco o Gsw)   *)
(* on (0,1)^2; the numerator N = x(1-x)y(1-y) is group-invariant         *)
(* (gcl_N_invar); the denominator orbit {T = 1-xy, Tbar = x+y-xy}        *)
(* (gcl_T_orbit_Gsw/Gco; Tbar is the dig_sup_uv form, coverage via the   *)
(* DIG two-form sup certificates).  Operator gcl_sym4 (V4 orbit average, *)
(* Defined, extractable), instance gcl_Tavg = (1/2)(1+x+y-2xy).  Main    *)
(* certificate gcl_sup_avg: 24N <= 1+x+y-2xy, i.e. N/Tavg <= 1/12, tight *)
(* at x=y=1/2; 61/676 = 0.090237 sharpens to 1/12 = 0.083333, crossing   *)
(* the family limit theta* = phi^-5 = 0.090170 (30^2*5 = 4500 >          *)
(* 67^2 = 4489, gcl_limit_cross_cert).  Competition verdict m >= 3 at    *)
(* rate 3/4 (DIG tier m >= 4: threshold 4 -> 3, sharpness anchors both   *)
(* sides); generic separation skeleton gcl_sep_generic (family-indexed,  *)
(* zero premise gap; the symmetrized truncation family stays a named     *)
(* gap slot).                                                            *)
(* Dependencies.  Stdlib QArith/ZArith/Arith/Lia/Setoid; S01_BaseRing,   *)
(* S02_CauchyComplete, S03_QExp, BeukersLists, abl_z2_truncfam,          *)
(* abl_z2_itg_carrier, abl_dmw2_pointwise_sharp, dig_machine.            *)
(* References.  Rhin-Viola, On a permutation group related to zeta(2),   *)
(* Acta Arith. 77 (1996); Fischler, Groupes de Rhin-Viola et integrales  *)
(* multiples, JTNB 15 (2003) 479-534.                                    *)
(* Constructivity.  All statements Set-carried; Print Assumptions all    *)
(* Closed; Separate Extraction Obj.magic = 0; no real-number layer, no   *)
(* classical logic.                                                      *)
(* Build.  rocq c -native-compiler no -q -Q . "" gcl_coefficient.v       *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_truncfam abl_z2_itg_carrier abl_dmw2_pointwise_sharp dig_machine.

Open Scope Q_scope.

(* ============================================================ *)
(* Sec G. Group-carrier face: the four-element permutation group  *)
(* V4 = <Gsw, Gco> and its action gcl_act                         *)
(* ============================================================ *)

(* Group-element carrier (Set-carried; four elements: identity /     *)
(* swap / double-complement / composite) *)
Inductive gcl_g : Set := Gid | Gsw | Gco | Gsc.

(* The group action (Defined transparent; polynomial-tier generators):
   Gid = (x,y), Gsw = (y,x), Gco = (1-x,1-y),
   Gsc = Gco o Gsw = (1-y,1-x). *)
Definition gcl_act (g : gcl_g) (x y : Q) : Q * Q :=
  match g with
  | Gid => (x, y)
  | Gsw => (y, x)
  | Gco => (1 - x, 1 - y)
  | Gsc => (1 - y, 1 - x)
  end.

(* Component face of the generator involutions (Gco self-inverse:      *)
(* 1-(1-x) = x; Gsw self-inverse: definitional) *)
Lemma gcl_copl_invol_x : forall x : Q, 1 - (1 - x) == x.
Proof. intro x. ring. Qed.

Lemma gcl_act_Gco_fst : forall x y : Q, fst (gcl_act Gco x y) == 1 - x.
Proof. reflexivity. Qed.

Lemma gcl_act_Gco_snd : forall x y : Q, snd (gcl_act Gco x y) == 1 - y.
Proof. reflexivity. Qed.

Lemma gcl_act_Gsc_fst : forall x y : Q, fst (gcl_act Gsc x y) == 1 - y.
Proof. reflexivity. Qed.

Lemma gcl_act_Gsc_snd : forall x y : Q, snd (gcl_act Gsc x y) == 1 - x.
Proof. reflexivity. Qed.

(* Numerator invariance face: N = x(1-x)y(1-y) is invariant on the full
   group orbit (the Beukers decay supply face -- the group action
   leaves the decay material unchanged and only permutes the
   denominator orbit). *)
Lemma gcl_N_invar : forall (g : gcl_g) (x y : Q),
  (match g with
   | Gid => x * (1 - x) * y * (1 - y)
   | Gsw => y * (1 - y) * x * (1 - x)
   | Gco => (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y))
   | Gsc => (1 - y) * (1 - (1 - y)) * (1 - x) * (1 - (1 - x))
   end) == x * (1 - x) * y * (1 - y).
Proof. intros g x y. destruct g; ring. Qed.

(* Denominator orbit face: T o Gsw = T (swap-invariant); T o Gco =
   Tbar = x+y-xy (the conjugate denominator).
   -- Record of the group action permuting the denominator orbit
   {T, Tbar}: dig_sup (the T form) and dig_sup_uv (the Tbar form,
   read out in the original variables) are exactly the two orbit
   representatives. *)
Lemma gcl_T_orbit_Gsw : forall x y : Q,
  1 - fst (gcl_act Gsw x y) * snd (gcl_act Gsw x y) == 1 - x * y.
Proof. intros x y. unfold gcl_act. simpl. ring. Qed.

Lemma gcl_T_orbit_Gco : forall x y : Q,
  1 - fst (gcl_act Gco x y) * snd (gcl_act Gco x y) == x + y - x * y.
Proof. intros x y. unfold gcl_act. simpl. ring. Qed.

(* Composite face: Gsc = Gco o Gsw (componentwise definitional      *)
(* agreement) *)
Lemma gcl_Gsc_co_sw : forall x y : Q,
  gcl_act Gsc x y = (1 - y, 1 - x).
Proof. reflexivity. Qed.

(* ============================================================ *)
(* Sec S. Symmetrization-operator face: the V4 orbit average       *)
(* gcl_sym4 and its denominator instance gcl_Tavg                  *)
(* ============================================================ *)

(* The symmetrization operator (Defined transparent, extractable): the
   average of a function over the full V4 orbit.  The coefficient step
   of the Rhin-Viola group-structure method: after the integral
   quantity is averaged over the group orbit, its pointwise control
   function gains the group symmetry and the sup becomes optimizable. *)
Definition gcl_sym4 (f : Q -> Q -> Q) (x y : Q) : Q :=
  (f x y + f y x + f (1 - x) (1 - y) + f (1 - y) (1 - x)) * (1#4).

(* The symmetrized denominator (the improvement carrier of this
   coefficient layer): Tavg = (T+Tbar)/2 = (1/2)(1+x+y-2xy) -- the
   instance of gcl_sym4 on the denominator function (the two-point
   Gsw orbit collapses). *)
Definition gcl_Tavg (x y : Q) : Q := (1#2) * (1 + x + y - 2 * x * y).

(* Operator instance agreement: sym4(denominator) == Tavg *)
Lemma gcl_sym4_Tavg : forall x y : Q,
  gcl_sym4 (fun a b : Q => 1 - a * b) x y == gcl_Tavg x y.
Proof.
  intros x y. unfold gcl_sym4, gcl_Tavg. cbv beta. ring.
Qed.

(* Operator fixed face: sym4(N) == N (numerator group-invariance ->   *)
(* the average restores it) *)
Lemma gcl_sym4_N : forall x y : Q,
  x * (1 - x) * y * (1 - y)
  == gcl_sym4 (fun a b : Q => a * (1 - a) * b * (1 - b)) x y.
Proof.
  intros x y. unfold gcl_sym4. cbv beta. ring.
Qed.

(* ============================================================ *)
(* Sec A. Coefficient-improvement certificate face (main theorem): *)
(* the symmetrized tight certificate 24N <= 1+x+y-2xy              *)
(* ============================================================ *)

(* The tau-conjugate slot (orbit coverage; the DIG two-form readout):
   the Tbar form of dig_sup_uv in the original variables -- the sup
   certificate of the complement-imaged denominator, which under the
   group-theoretic reading forms the second orbit member with
   dig_sup. *)
Theorem gcl_sup_copl : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  676 * x * (1 - x) * y * (1 - y) <= 61 * (x + y - x * y).
Proof. intros x y [Hx1 Hx2] [Hy1 Hy2].
  exact (QleT'_to_Qle _ _ (dig_sup_uv x y
           (Qle_to_QleT' _ _ Hx1, Qle_to_QleT' _ _ Hx2)
           (Qle_to_QleT' _ _ Hy1, Qle_to_QleT' _ _ Hy2))). Qed.

(* The symmetrized tight certificate (main theorem, new mathematics):
   0 <= x,y <= 1 implies 24N <= 1+x+y-2xy, i.e. N/Tavg <= 1/12 --
   sharper than the DIG tier 61/676 (-7.65%), and 1/12 crosses the
   original family's pointwise limit theta* = phi^-5 (group averaging
   shaves the golden-point ridge).  Proof chain (m = x+y, k = xy,
   B = 6(m-2)^2+2): Phi = 1+m-2k-24N >= 1+m-26k+24mk-6m^2k
   = 1+m-kB >= 1+m-(m^2/4)B = (m-1)^2 (1+(3/2)m(2-m)) >= 0. *)
Theorem gcl_sup_avg : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  24 * x * (1 - x) * y * (1 - y) <= 1 + x + y - 2 * x * y.
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  (* m = x+y in [0,2], k = xy >= 0, 4k <= m^2 *)
  assert (Hm0 : 0 <= x + y).
  { apply (Qle_trans 0 (0 + 0) (x + y)).
    - rewrite Qplus_0_l. apply Qle_refl.
    - apply (Qplus_le_compat 0 x 0 y); assumption. }
  assert (Hm2 : x + y <= 2).
  { apply (Qle_trans (x + y) (1 + 1) 2).
    - apply (Qplus_le_compat x 1 y 1); assumption.
    - assert (Heq : 1 + 1 == 2) by ring.
      rewrite Heq. apply Qle_refl. }
  assert (Hk0 : 0 <= x * y) by (apply Qmult_le_0_compat; assumption).
  assert (Hdsq : 0 <= (x + y) * (x + y) - 4 * (x * y)).
  { assert (Hd : (x + y) * (x + y) - 4 * (x * y) == (x - y) * (x - y)) by ring.
    rewrite Hd. apply QleT'_to_Qle. apply dmw2_sq_ge0. }
  assert (H4k : 4 * (x * y) <= (x + y) * (x + y))
    by (apply QleT'_to_Qle; apply (dmw2_sub_ge0 (4 * (x * y)) ((x + y) * (x + y))); exact Hdsq).
  assert (HkQ : x * y <= (x + y) * (x + y) * (1#4)).
  { assert (Heq : (x + y) * (x + y) * (1#4) - x * y
               == ((x + y) * (x + y) - 4 * (x * y)) * (1#4)) by ring.
    apply QleT'_to_Qle. apply (dmw2_sub_ge0 (x * y) ((x + y) * (x + y) * (1#4))).
    rewrite Heq. apply Qmult_le_0_compat.
    - exact Hdsq.
    - unfold Qle. simpl. lia. }
  (* B = 26-24m+6m^2 = 6(m-2)^2+2 >= 2 > 0 *)
  assert (HB : 0 <= 26 - 24 * (x + y) + 6 * (x + y) * (x + y)).
  { assert (Hid : 26 - 24 * (x + y) + 6 * (x + y) * (x + y)
               == 6 * (2 - (x + y)) * (2 - (x + y)) + 2) by ring.
    rewrite Hid.
    assert (Hs : 0 <= (2 - (x + y)) * (2 - (x + y)))
      by (apply QleT'_to_Qle; apply dmw2_sq_ge0).
    assert (HX : 0 <= 6 * (2 - (x + y)) * (2 - (x + y))).
    { apply Qmult_le_0_compat.
      - apply QleT'_to_Qle. apply (dmw2_mult2_ge0 6 (2 - (x + y)))
        ; [ unfold Qle; simpl; lia | ].
        apply QleT'_to_Qle. apply (dmw2_le_sub (x + y) 2). exact Hm2.
      - apply QleT'_to_Qle. apply (dmw2_le_sub (x + y) 2). exact Hm2. }
    apply (Qle_trans 0 (6 * (2 - (x + y)) * (2 - (x + y)))
                      (6 * (2 - (x + y)) * (2 - (x + y)) + 2)).
    - exact HX.
    - apply QleT'_to_Qle. apply dmw2_add_ge0_le. unfold Qle. simpl. lia. }
  (* Step 1: 24k^2 <= 6m^2k (4k <= m^2 multiplied by 6k >= 0) *)
  assert (H6k : 0 <= 6 * (x * y))
    by (apply QleT'_to_Qle; apply (dmw2_mult2_ge0 6 (x * y))
        ; [ unfold Qle; simpl; lia | exact Hk0 ]).
  assert (HS1 : 24 * (x * y) * (x * y) <= 6 * (x + y) * (x + y) * (x * y)).
  { pose proof (Qmult_le_compat_r (4 * (x * y)) ((x + y) * (x + y))
                  (6 * (x * y)) H4k H6k) as H.
    assert (E1 : (4 * (x * y)) * (6 * (x * y)) == 24 * (x * y) * (x * y)) by ring.
    assert (E2 : (x + y) * (x + y) * (6 * (x * y))
              == 6 * (x + y) * (x + y) * (x * y)) by ring.
    rewrite E1, E2 in H. exact H. }
  (* Step 2: kB <= (m^2/4)B (k <= m^2/4 with B >= 0) *)
  assert (Hle2 : 1 + x + y - (x + y) * (x + y) * (1#4)
                        * (26 - 24 * (x + y) + 6 * (x + y) * (x + y))
              <= 1 + x + y - (x * y) * (26 - 24 * (x + y) + 6 * (x + y) * (x + y))).
  { apply QleT'_to_Qle. apply (dmw2_minus_le (1 + x + y)
             ((x * y) * (26 - 24 * (x + y) + 6 * (x + y) * (x + y)))
             ((x + y) * (x + y) * (1#4)
               * (26 - 24 * (x + y) + 6 * (x + y) * (x + y)))).
    pose proof (Qmult_le_compat_r (x * y) ((x + y) * (x + y) * (1#4))
                  (26 - 24 * (x + y) + 6 * (x + y) * (x + y)) HkQ HB) as H.
    exact H. }
  (* Step 3: factorization of the final expression                       *)
(* ((m-1)^2 (1+(3/2)m(2-m)) >= 0) *)
  assert (Hprod : 0 <= ((x + y) - 1) * ((x + y) - 1)
                        * (1 + (3#2) * ((x + y) * (2 - (x + y))))).
  { apply Qmult_le_0_compat.
    - apply QleT'_to_Qle. apply dmw2_sq_ge0.
    - apply (Qle_trans 0 1 (1 + (3#2) * ((x + y) * (2 - (x + y))))).
      + unfold Qle. simpl. lia.
      + apply QleT'_to_Qle.
        apply (dmw2_add_ge0_le 1 ((3#2) * ((x + y) * (2 - (x + y))))).
        apply QleT'_to_Qle. apply (dmw2_mult2_ge0 (3#2) ((x + y) * (2 - (x + y))))
        ; [ unfold Qle; simpl; lia | ].
        apply QleT'_to_Qle. apply (dmw2_mult2_ge0 (x + y) (2 - (x + y)))
        ; [ exact Hm0
          | apply QleT'_to_Qle; apply (dmw2_le_sub (x + y) 2); exact Hm2 ]. }
  (* Chained composition *)
  assert (Hle1 : 1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y)
                       - 6 * (x + y) * (x + y) * (x * y)
              <= 1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y)
                       - 24 * (x * y) * (x * y)).
  { apply QleT'_to_Qle. apply (dmw2_minus_le (1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y))
             (24 * (x * y) * (x * y))
             (6 * (x + y) * (x + y) * (x * y))).
    exact HS1. }
  assert (Hchain : ((x + y) - 1) * ((x + y) - 1)
                     * (1 + (3#2) * ((x + y) * (2 - (x + y))))
              <= 1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y)
                       - 24 * (x * y) * (x * y)).
  { assert (Efin : ((x + y) - 1) * ((x + y) - 1)
                      * (1 + (3#2) * ((x + y) * (2 - (x + y))))
               == 1 + x + y - (x + y) * (x + y) * (1#4)
                        * (26 - 24 * (x + y) + 6 * (x + y) * (x + y))) by ring.
    rewrite Efin.
    apply (Qle_trans _ (1 + x + y - (x * y)
                          * (26 - 24 * (x + y) + 6 * (x + y) * (x + y)))).
    - exact Hle2.
    - assert (Hd2 : 1 + x + y - (x * y) * (26 - 24 * (x + y) + 6 * (x + y) * (x + y))
                 == 1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y)
                        - 6 * (x + y) * (x + y) * (x * y)) by ring.
      rewrite Hd2. exact Hle1. }
  assert (HPhi0 : 0 <= 1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y)
                        - 24 * (x * y) * (x * y)).
  { apply (Qle_trans 0 (((x + y) - 1) * ((x + y) - 1)
                          * (1 + (3#2) * ((x + y) * (2 - (x + y)))))).
    - exact Hprod.
    - exact Hchain. }
  (* Final step: Phi >= 0 implies 24N <= 1+x+y-2xy *)
  assert (E0 : 1 + x + y - 2 * x * y - 24 * x * (1 - x) * y * (1 - y)
            == 1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y)
                     - 24 * (x * y) * (x * y)) by ring.
  apply (Qle_trans (24 * x * (1 - x) * y * (1 - y))
    (24 * x * (1 - x) * y * (1 - y)
       + (1 + x + y - 2 * x * y - 24 * x * (1 - x) * y * (1 - y)))
    (1 + x + y - 2 * x * y)).
  - apply QleT'_to_Qle. apply dmw2_add_ge0_le.
    rewrite E0. exact HPhi0.
  - assert (HeqF : 24 * x * (1 - x) * y * (1 - y)
                + (1 + x + y - 2 * x * y - 24 * x * (1 - x) * y * (1 - y))
                == 1 + x + y - 2 * x * y) by ring.
    rewrite HeqF. apply Qle_refl.
Qed.

(* Main interface (Set face): N <= (1/12)*Tavg on the full square *)
Theorem gcl_avg_cert : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  QleT' (12 * x * (1 - x) * y * (1 - y)) (gcl_Tavg x y).
Proof.
  intros x y Hx Hy.
  pose proof (gcl_sup_avg x y Hx Hy) as H.
  assert (H12 : 0 <= (1#2)) by (unfold Qle; simpl; lia).
  pose proof (Qmult_le_compat_r (24 * x * (1 - x) * y * (1 - y))
                (1 + x + y - 2 * x * y) (1#2) H H12) as Hm.
  assert (E1 : (24 * x * (1 - x) * y * (1 - y)) * (1#2)
            == 12 * x * (1 - x) * y * (1 - y)) by ring.
  assert (E2 : (1 + x + y - 2 * x * y) * (1#2)
            == (1#2) * (1 + x + y - 2 * x * y)) by ring.
  rewrite E1, E2 in Hm.
  unfold gcl_Tavg. apply Qle_to_QleT'. exact Hm.
Qed.

(* Tight anchor: equality at the tau fixed point (1/2,1/2) --
   24N = 1+x+y-2xy = 3/2; the certificate constant 1/12 is the exact
   sup (cannot be lowered within this family) *)
Lemma gcl_anchor_avg_tight :
  24 * (1#2) * (1 - (1#2)) * (1#2) * (1 - (1#2))
  == 1 + (1#2) + (1#2) - 2 * (1#2) * (1#2).
Proof. vm_compute. reflexivity. Qed.

(* In-family limit crossing discrimination (integer certificate):
   1/12 < theta* = (5*sqrt(5)-11)/2 = phi^-5 iff 30*sqrt(5) > 67 iff
   30^2*5 = 4500 > 67^2 = 4489 -- the symmetrized coefficient layer's
   in-family limit is strictly below the original family's pointwise
   limit (a structural record of group averaging) *)
Lemma gcl_limit_cross_cert : QltT 4489 4500.
Proof. exact (id_refl (A:=bool) (x:=Qlt_bool 4489 4500)). Qed.

(* ============================================================ *)
(* Sec C. Competition/separation skeleton face: the 3/4 rate       *)
(* (symmetrized tier (1/4)(1/12)^m)                                *)
(* ============================================================ *)

(* Symmetrized-tier machinery weight: family interface                 *)
(* (1/4)*(1/12)^m (feeds downstream measure-tier estimates) *)
Definition gcl_weight_G (m : nat) : Q := (1#4) * q_pow (1#12) m.

Lemma gcl_weight_G_ge0 : forall m : nat, QleT' 0 (gcl_weight_G m).
Proof.
  intro m. apply Qle_to_QleT'. apply Qmult_le_0_compat.
  - unfold Qle. simpl. lia.
  - apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'.
    unfold Qle. simpl. lia.
Qed.

(* Weight sharpening anchor: (1/4)(1/12) <= (1/4)(61/676)              *)
(* (iff 676 <= 732; literal Qle_bool judgment) *)
Lemma gcl_weight_sharpen_G : QleT' (gcl_weight_G 1) (dig_weight 1).
Proof.
  exact (id_refl (A:=bool) (x:=Qle_bool (gcl_weight_G 1) (dig_weight 1))).
Qed.

(* Competition identity: 9^(m+1)*(1/4)*(1/12)^m = (9/4)*(3/4)^m        *)
(* (9*(1/12) = 3/4) *)
Lemma gcl_comp_id_G : forall m : nat,
  q_pow 9 (Datatypes.S m) * gcl_weight_G m == (9#4) * q_pow (3#4) m.
Proof.
  intro m. unfold gcl_weight_G.
  assert (Hpm : q_pow 9 m * q_pow (1#12) m == q_pow (3#4) m).
  { rewrite <- (qeqT_imp_qeq _ _ (zb2_q_pow_mul 9 (1#12) m)).
    assert (H912 : 9 * (1#12) == (3#4)) by ring.
    rewrite H912. reflexivity. }
  assert (Hre : q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (1#12) m)
             == (9 * (1#4)) * (q_pow 9 m * q_pow (1#12) m))
    by (rewrite (qeqT_imp_qeq _ _ (q_pow_succ 9 m)); ring).
  rewrite Hre, Hpm.
  assert (H94 : 9 * (1#4) == (9#4)) by ring.
  rewrite H94. reflexivity.
Qed.

(* Competition base tier: (9/4)*(3/4)^3 = 243/256 < 1 (literal         *)
(* judgment -- threshold m >= 3) *)
Lemma gcl_comp_base_G : QltT ((9#4) * q_pow (3#4) 3) 1.
Proof.
  exact (id_refl (A:=bool) (x:=Qlt_bool ((9#4) * q_pow (3#4) 3) 1)).
Qed.

(* Threshold sharpness anchor: (9/4)*(3/4)^2 = 81/64 >= 1 -- m = 2     *)
(* falls short; m >= 3 is the sharp threshold *)
Lemma gcl_comp_base2_ge_G : QleT' 1 ((9#4) * q_pow (3#4) 2).
Proof.
  exact (id_refl (A:=bool) (x:=Qle_bool 1 ((9#4) * q_pow (3#4) 2))).
Qed.

(* Competition step: (9/4)*(3/4)^(m+1) <= (9/4)*(3/4)^m *)
Lemma gcl_comp_step_G : forall m : nat,
  QleT' ((9#4) * q_pow (3#4) (Datatypes.S m)) ((9#4) * q_pow (3#4) m).
Proof.
  intro m.
  assert (Hge0 : 0 <= (9#4) * q_pow (3#4) m).
  { apply Qmult_le_0_compat.
    - unfold Qle. simpl. lia.
    - apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'.
      unfold Qle. simpl. lia. }
  assert (Hs34 : (3#4) <= 1) by (unfold Qle; simpl; lia).
  apply Qle_to_QleT'.
  assert (Hrw : (9#4) * q_pow (3#4) (Datatypes.S m)
             == (3#4) * ((9#4) * q_pow (3#4) m))
    by (rewrite (qeqT_imp_qeq _ _ (q_pow_succ (3#4) m)); ring).
  rewrite Hrw.
  pose proof (Qmult_le_compat_r (3#4) 1 ((9#4) * q_pow (3#4) m)
                Hs34 Hge0) as Hle.
  assert (Hr2 : 1 * ((9#4) * q_pow (3#4) m) == (9#4) * q_pow (3#4) m) by ring.
  rewrite Hr2 in Hle. exact Hle.
Qed.

(* Competition shift: induction on the shift amount d *)
Lemma gcl_comp_drop_G : forall (d m : nat),
  QleT' ((9#4) * q_pow (3#4) (m + d)) ((9#4) * q_pow (3#4) m).
Proof.
  induction d as [| d IH]; intro m.
  - assert (Hd : (m + 0 = m)%nat) by apply Nat.add_0_r.
    rewrite Hd. apply Qle_to_QleT'. apply Qle_refl.
  - assert (Hs : (m + Datatypes.S d = Datatypes.S (m + d))%nat)
      by apply Nat.add_succ_r.
    rewrite Hs.
    apply (qleT'_trans ((9#4) * q_pow (3#4) (Datatypes.S (m + d)))
                       ((9#4) * q_pow (3#4) (m + d))
                       ((9#4) * q_pow (3#4) m)).
    + apply gcl_comp_step_G.
    + apply IH.
Qed.

(* Competition verdict: m >= 3 implies (9/4)*(3/4)^m < 1
   (the DIG tier's 549/676-rate threshold is m >= 4 -- the symmetrized
   coefficient layer shifts 4 -> 3; both-side sharpness anchors
   gcl_comp_base_G / gcl_comp_base2_ge_G in place) *)
Lemma gcl_comp_verdict_G : forall m : nat, (3 <= m)%nat -> QltT ((9#4) * q_pow (3#4) m) 1.
Proof.
  induction m as [| m IH]; intro Hm.
  - exfalso. lia.
  - destruct (le_lt_dec 3 m) as [Hle | Hlt].
    + apply (qleT'_ltT_ltT ((9#4) * q_pow (3#4) (Datatypes.S m))
                           ((9#4) * q_pow (3#4) m) 1).
      * apply gcl_comp_step_G.
      * apply IH. exact Hle.
    + assert (Heq : (Datatypes.S m = 3)%nat) by lia.
      rewrite Heq. exact gcl_comp_base_G.
Qed.

(* Generic separation skeleton (family-indexed; zero premise gap; slot
   form): let Fam be the integral-value function of any symmetrized
   truncation family (nonnegative; family bound <= (1/4)(1/12)^m
   given), and let d satisfy the Hanson chain 0 <= d <= 3^(m+1); then
   for m >= 3, d^2 * Fam(m) < 1.
   -- Gap slot (declared as-is): the concrete symmetrized family (the
      Tavg-denominator truncation family) is not yet built; Fam is a
      named slot; instantiating the slot triggers the downstream
      mu_lib reduction. *)
Theorem gcl_sep_generic : forall (Fam : nat -> Q) (m : nat) (d : Q),
  (3 <= m)%nat ->
  QleT' 0 d ->
  QleT' d (q_pow 3 (Datatypes.S m)) ->
  QleT' 0 (Fam m) ->
  QleT' (Fam m) (gcl_weight_G m) ->
  QltT (d * d * Fam m) 1.
Proof.
  intros Fam m d Hm Hd0 Hd Hf0 Hf.
  pose proof (dig_weight_sq (Datatypes.S m) d Hd0 Hd) as Hsq.
  pose proof (QleT'_to_Qle _ _ Hsq) as Hsqq.
  pose proof (QleT'_to_Qle _ _ Hf0) as Hf0q.
  pose proof (QleT'_to_Qle _ _ Hf) as Hfq.
  assert (H9 : 0 <= q_pow 9 (Datatypes.S m))
    by (apply QleT'_to_Qle; apply q_pow_nonneg; apply Qle_to_QleT'
        ; unfold Qle; simpl; lia).
  assert (Hstep1 : d * d * Fam m <= q_pow 9 (Datatypes.S m) * Fam m)
    by (apply (Qmult_le_compat_r (d * d) (q_pow 9 (Datatypes.S m))
                                 (Fam m) Hsqq Hf0q)).
  assert (Hstep2 : q_pow 9 (Datatypes.S m) * Fam m
                <= q_pow 9 (Datatypes.S m) * gcl_weight_G m).
  { assert (H2' : Fam m * q_pow 9 (Datatypes.S m)
               <= gcl_weight_G m * q_pow 9 (Datatypes.S m))
      by (apply (Qmult_le_compat_r (Fam m) (gcl_weight_G m)
                                   (q_pow 9 (Datatypes.S m)) Hfq H9)).
    assert (Hc1 : q_pow 9 (Datatypes.S m) * Fam m
               == Fam m * q_pow 9 (Datatypes.S m)) by ring.
    assert (Hc2 : gcl_weight_G m * q_pow 9 (Datatypes.S m)
               == q_pow 9 (Datatypes.S m) * gcl_weight_G m) by ring.
    rewrite Hc1, <- Hc2. exact H2'. }
  assert (Hchain : d * d * Fam m <= (9#4) * q_pow (3#4) m).
  { apply (Qle_trans _ (q_pow 9 (Datatypes.S m) * gcl_weight_G m)).
    - apply (Qle_trans _ (q_pow 9 (Datatypes.S m) * Fam m)).
      + exact Hstep1.
      + exact Hstep2.
    - exact (QleT'_to_Qle _ _ (dmw2_le_eq _ _ (gcl_comp_id_G m))). }
  pose proof (QltT_to_Qlt _ _ (gcl_comp_verdict_G m Hm)) as Hv.
  pose proof (Qle_lt_trans _ _ _ Hchain Hv) as Hfin.
  apply Qlt_to_QltT. exact Hfin.
Qed.

(* ============================================================ *)
(* Sec D. Extraction and the closed-world audit (zero global       *)
(* premise recheck)                                                *)
(* ============================================================ *)

Separate Extraction gcl_comp_verdict_G gcl_sep_generic gcl_avg_cert
  gcl_sym4 gcl_Tavg gcl_act gcl_weight_G.

Print Assumptions gcl_N_invar.
Print Assumptions gcl_T_orbit_Gsw.
Print Assumptions gcl_T_orbit_Gco.
Print Assumptions gcl_sym4_Tavg.
Print Assumptions gcl_sym4_N.
Print Assumptions gcl_sup_copl.
Print Assumptions gcl_sup_avg.
Print Assumptions gcl_avg_cert.
Print Assumptions gcl_anchor_avg_tight.
Print Assumptions gcl_limit_cross_cert.
Print Assumptions gcl_weight_G_ge0.
Print Assumptions gcl_weight_sharpen_G.
Print Assumptions gcl_comp_id_G.
Print Assumptions gcl_comp_base_G.
Print Assumptions gcl_comp_base2_ge_G.
Print Assumptions gcl_comp_step_G.
Print Assumptions gcl_comp_drop_G.
Print Assumptions gcl_comp_verdict_G.
Print Assumptions gcl_sep_generic.
