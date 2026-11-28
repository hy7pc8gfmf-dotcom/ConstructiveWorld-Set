(* ========================================================================= *)
(* Module  : UpAblP6_StateSpace_inst                                        *)
(* Mission. A second fully-lawful instance of the StateSpace class over an  *)
(*   abstract constructive real interface: carrier R x R with pointwise     *)
(*   addition, scaling and negation, the L1 metric (sum of the component    *)
(*   metrics), and componentwise limits.  All 21 class fields are built     *)
(*   outright; the states (0,0)/(1,0)/(0,1) are pairwise non-identical, so  *)
(*   the instance is nontrivial.  A collapse theorem rules out every        *)
(*   squaring carrier (y + y = 0 pointwise degenerates to one point, since  *)
(*   each scalar factors as 4*(a*4^-1) with 4 = 1+1+1+1 > 0), so a lawful   *)
(*   nontrivial instance must be infinite.  The abstract list-summation     *)
(*   statements (idt_sumf vs bs_list_sum) are realized on this carrier.     *)
(* Dependencies. S01_BaseRing (RealInterface/Enhanced, StateSpace, Set-valued *)
(*   Id/le/lt, NatLe); IdSlotTranslate (idt_sumf, idt_list_sum,             *)
(*   idt_sum_eq_list, idt_slot_g01); AttnDoeblin (bs_list_sum); Stdlib List.*)
(* References. S01_BaseRing.v:184/:268/:1080/:1197 (interfaces, StateSpace, *)
(*   RealSelfSS); IdSlotTranslate.v:85/:139 (the realized statements);      *)
(*   AttnDoeblin.v:496 (bs_list_sum).                                       *)
(* Constructivity. Statement faces are Set-carried only: identities ride    *)
(*   the Set-valued inductive Id, order rides lt/le : R -> R -> Set, the    *)
(*   separations are Set-level Not (a function into Empty_set), and the     *)
(*   only existential face is sigT mirroring the cauchy_complete_S field    *)
(*   shape.  No Prop statements, no axioms, no admits; every definition     *)
(*   and proof is transparent (Defined), since every conclusion is          *)
(*   informative data; no Qed occurs in this file.                          *)
(* Build. rocq c -native-compiler no -q -Q <tree root> ""                   *)
(*   UpAblP6_StateSpace_inst.v                                              *)
(* ========================================================================= *)

Require Import S01_BaseRing.
Require IdSlotTranslate.
Require AttnDoeblin.
From Stdlib Require Import List.

(* ============================================================ *)
(* Section 1.  The product carrier R x R: operations, L1 metric, *)
(* componentwise convergence, and the 21 field laws.            *)
(* ============================================================ *)
Section ProductCarrier.

Context {RIE : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let Rb : RealInterface := @RI_base RIE.        (* the underlying real interface *)
Let prodRR : Set := prod (@R Rb) (@R Rb).      (* carrier type: real pairs *)

(* ---- pointwise operations, L1 metric, componentwise limit ---- *)
Definition prod_zero : prodRR := (@zero Rb, @zero Rb).

Definition prod_plus (x y : prodRR) : prodRR :=
  (@plus Rb (fst x) (fst y), @plus Rb (snd x) (snd y)).

Definition prod_smult (a : @R Rb) (x : prodRR) : prodRR :=
  (@mult Rb a (fst x), @mult Rb a (snd x)).

Definition prod_opp (x : prodRR) : prodRR :=
  (@opp Rb (fst x), @opp Rb (snd x)).

Definition prod_metric (x y : prodRR) : @R Rb :=
  @plus Rb (@metric Rb (fst x) (fst y)) (@metric Rb (snd x) (snd y)).

Definition prod_clim (u : nat -> prodRR) (l : prodRR) : Set :=
  prod (@lim Rb (fun n => fst (u n)) (fst l))
       (@lim Rb (fun n => snd (u n)) (snd l)).

(* ---- identity combinators: pair identity from component identities ---- *)
Definition pair_id_pair {A B : Set} {a a' : A} {b b' : B}
  (p : Id a a') (q : Id b b') : Id (pair a b) (pair a' b') :=
  id_trans (id_cong (fun x : A => (x, b)) p)
           (id_cong (fun y : B => (a', y)) q).

(* ---- self-supplied real left distributivity (a+b)*c == a*c + b*c ---- *)
(*   (the interface provides only a*(b+c) == a*b + a*c; three commutation *)
(*    steps assemble the left-hand form) *)
Definition mult_distrib_l (a b c : @R Rb) :
  Id (@mult Rb (@plus Rb a b) c) (@plus Rb (@mult Rb a c) (@mult Rb b c)) :=
  id_trans (@mult_comm Rb (@plus Rb a b) c)
    (id_trans (@distrib Rb c a b)
      (id_trans (id_cong (fun t => @plus Rb t (@mult Rb c b)) (@mult_comm Rb c a))
                (id_cong (fun t => @plus Rb (@mult Rb a c) t) (@mult_comm Rb c b)))).

(* ---- four-term regrouping (x+y)+(z+w) == (x+z)+(y+w) (L1 triangle) ---- *)
Definition plus_pair_swap (x y z w : @R Rb) :
  Id (@plus Rb (@plus Rb x y) (@plus Rb z w)) (@plus Rb (@plus Rb x z) (@plus Rb y w)) :=
  id_trans (id_sym (@plus_assoc Rb x y (@plus Rb z w)))
    (id_trans (id_cong (fun t => @plus Rb x t) (@plus_assoc Rb y z w))
      (id_trans (id_cong (fun t => @plus Rb x (@plus Rb t w)) (@plus_comm Rb y z))
        (id_trans (id_cong (fun t => @plus Rb x t) (id_sym (@plus_assoc Rb z y w)))
                  (@plus_assoc Rb x z (@plus Rb y w))))).

(* ---- component control of the L1 metric: m(fx,fy) <= m1+m2, m(sx,sy) <= m1+m2 ---- *)
Definition prod_metric_le_l (x y : prodRR) :
  @le Rb (@metric Rb (fst x) (fst y)) (prod_metric x y) :=
  le_id_l (@metric Rb (fst x) (fst y))
          (@plus Rb (@metric Rb (fst x) (fst y)) (@zero Rb))
          (prod_metric x y)
          (id_sym (@plus_zero Rb (@metric Rb (fst x) (fst y))))
          (le_plus_compat (@metric Rb (fst x) (fst y)) (@metric Rb (fst x) (fst y))
                          (@zero Rb) (@metric Rb (snd x) (snd y))
                          (@le_refl Rb (@metric Rb (fst x) (fst y)))
                          (@metric_pos Rb (snd x) (snd y))).

Definition prod_metric_le_r (x y : prodRR) :
  @le Rb (@metric Rb (snd x) (snd y)) (prod_metric x y) :=
  le_id_l (@metric Rb (snd x) (snd y))
          (@plus Rb (@zero Rb) (@metric Rb (snd x) (snd y)))
          (prod_metric x y)
          (id_trans (id_sym (@plus_zero Rb (@metric Rb (snd x) (snd y))))
                    (@plus_comm Rb (@metric Rb (snd x) (snd y)) (@zero Rb)))
          (le_plus_compat (@zero Rb) (@metric Rb (fst x) (fst y))
                          (@metric Rb (snd x) (snd y)) (@metric Rb (snd x) (snd y))
                          (@metric_pos Rb (fst x) (fst y))
                          (@le_refl Rb (@metric Rb (snd x) (snd y)))).

(* ---- eight algebra laws (pointwise, assembled by pair_id_pair) ---- *)
Definition prod_plus_assoc : forall a b c : prodRR,
  Id (prod_plus a (prod_plus b c)) (prod_plus (prod_plus a b) c) :=
  fun a b c =>
    pair_id_pair (@plus_assoc Rb (fst a) (fst b) (fst c))
                 (@plus_assoc Rb (snd a) (snd b) (snd c)).

Definition prod_plus_comm : forall a b : prodRR,
  Id (prod_plus a b) (prod_plus b a) :=
  fun a b => pair_id_pair (@plus_comm Rb (fst a) (fst b))
                          (@plus_comm Rb (snd a) (snd b)).

Definition prod_plus_zero : forall a : prodRR,
  Id (prod_plus a prod_zero) a.
Proof.
  intros [ax ay].
  exact (pair_id_pair (@plus_zero Rb ax) (@plus_zero Rb ay)).
Defined.

Definition prod_plus_opp : forall a : prodRR,
  Id (prod_plus a (prod_opp a)) prod_zero :=
  fun a => pair_id_pair (@plus_opp Rb (fst a)) (@plus_opp Rb (snd a)).

Definition prod_smult_one : forall a : prodRR,
  Id (prod_smult (@one Rb) a) a.
Proof.
  intros [ax ay].
  exact (pair_id_pair
           (id_trans (@mult_comm Rb (@one Rb) ax) (@mult_one Rb ax))
           (id_trans (@mult_comm Rb (@one Rb) ay) (@mult_one Rb ay))).
Defined.

Definition prod_smult_assoc : forall a b : @R Rb, forall x : prodRR,
  Id (prod_smult a (prod_smult b x)) (prod_smult (@mult Rb a b) x) :=
  fun a b x => pair_id_pair (@mult_assoc Rb a b (fst x)) (@mult_assoc Rb a b (snd x)).

Definition prod_smult_distrib_r : forall a : @R Rb, forall x y : prodRR,
  Id (prod_smult a (prod_plus x y))
     (prod_plus (prod_smult a x) (prod_smult a y)) :=
  fun a x y => pair_id_pair (@distrib Rb a (fst x) (fst y))
                            (@distrib Rb a (snd x) (snd y)).

Definition prod_smult_distrib_l : forall a b : @R Rb, forall x : prodRR,
  Id (prod_smult (@plus Rb a b) x)
     (prod_plus (prod_smult a x) (prod_smult b x)) :=
  fun a b x => pair_id_pair (mult_distrib_l a b (fst x))
                            (mult_distrib_l a b (snd x)).

(* ---- four metric laws ---- *)
Definition prod_metric_sym : forall x y : prodRR,
  Id (prod_metric x y) (prod_metric y x) :=
  fun x y =>
    id_trans (id_cong (fun t => @plus Rb t (@metric Rb (snd x) (snd y)))
                      (@metric_sym Rb (fst x) (fst y)))
             (id_cong (fun t => @plus Rb (@metric Rb (fst y) (fst x)) t)
                      (@metric_sym Rb (snd x) (snd y))).

Definition prod_metric_pos : forall x y : prodRR,
  @le Rb (@zero Rb) (prod_metric x y) :=
  fun x y =>
    le_id_l (@zero Rb) (@plus Rb (@zero Rb) (@zero Rb)) (prod_metric x y)
            (id_sym (@plus_zero Rb (@zero Rb)))
            (le_plus_compat (@zero Rb) (@metric Rb (fst x) (fst y))
                            (@zero Rb) (@metric Rb (snd x) (snd y))
                            (@metric_pos Rb (fst x) (fst y))
                            (@metric_pos Rb (snd x) (snd y))).

Definition prod_metric_zero : forall x y : prodRR,
  Id (prod_metric x y) (@zero Rb) -> Id x y.
Proof.
  intros [ax ay].
  intros [bx byy] H.
  apply (pair_id_pair
          (@metric_zero Rb ax bx
             (@le_antisym Rb (@metric Rb ax bx) (@zero Rb)
                (@le_id_r Rb (@metric Rb ax bx)
                            (prod_metric (ax, ay) (bx, byy)) (@zero Rb)
                            H (prod_metric_le_l (ax, ay) (bx, byy)))
                (@metric_pos Rb ax bx)))
          (@metric_zero Rb ay byy
             (@le_antisym Rb (@metric Rb ay byy) (@zero Rb)
                (@le_id_r Rb (@metric Rb ay byy)
                            (prod_metric (ax, ay) (bx, byy)) (@zero Rb)
                            H (prod_metric_le_r (ax, ay) (bx, byy)))
                (@metric_pos Rb ay byy)))).
Defined.

Definition prod_metric_triangle : forall x y z : prodRR,
  @le Rb (prod_metric x z)
         (@plus Rb (prod_metric x y) (prod_metric y z)) :=
  fun x y z =>
    le_id_r (prod_metric x z)
           (@plus Rb (@plus Rb (@metric Rb (fst x) (fst y)) (@metric Rb (fst y) (fst z)))
                     (@plus Rb (@metric Rb (snd x) (snd y)) (@metric Rb (snd y) (snd z))))
           (@plus Rb (prod_metric x y) (prod_metric y z))
           (plus_pair_swap (@metric Rb (fst x) (fst y)) (@metric Rb (fst y) (fst z))
                            (@metric Rb (snd x) (snd y)) (@metric Rb (snd y) (snd z)))
           (le_plus_compat (@metric Rb (fst x) (fst z))
             (@plus Rb (@metric Rb (fst x) (fst y)) (@metric Rb (fst y) (fst z)))
             (@metric Rb (snd x) (snd z))
             (@plus Rb (@metric Rb (snd x) (snd y)) (@metric Rb (snd y) (snd z)))
             (@metric_triangle Rb (fst x) (fst y) (fst z))
             (@metric_triangle Rb (snd x) (snd y) (snd z))).

(* ---- two convergence faces: limit uniqueness and Cauchy completeness ---- *)
Definition prod_clim_unique : forall (u : nat -> prodRR) (l1 l2 : prodRR),
  prod_clim u l1 -> prod_clim u l2 -> Id l1 l2.
Proof.
  intros u [a1 b1] [a2 b2] H1 H2.
  exact (pair_id_pair
          (@lim_unique Rb (fun n => fst (u n)) a1 a2 (fst H1) (fst H2))
          (@lim_unique Rb (fun n => snd (u n)) b1 b2 (snd H1) (snd H2))).
Defined.

Definition prod_cauchy_complete : forall (u : nat -> prodRR),
  (forall eps : @R Rb, @lt Rb (@zero Rb) eps ->
     sigT (fun N : nat => forall m n : nat,
       NatLe N m -> NatLe N n ->
       @lt Rb (prod_metric (u m) (u n)) eps)) ->
  sigT (fun l : prodRR => prod_clim u l).
Proof.
  intros u Hc.
  assert (Hf : forall eps : @R Rb, @lt Rb (@zero Rb) eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      @lt Rb (@metric Rb (fst (u m)) (fst (u n))) eps)).
  { intros eps Heps. destruct (Hc eps Heps) as [N HN].
    exists N. intros m n Hm Hn.
    exact (le_lt_trans (@metric Rb (fst (u m)) (fst (u n)))
                       (prod_metric (u m) (u n)) eps
            (prod_metric_le_l (u m) (u n)) (HN m n Hm Hn)). }
  assert (Hs : forall eps : @R Rb, @lt Rb (@zero Rb) eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      @lt Rb (@metric Rb (snd (u m)) (snd (u n))) eps)).
  { intros eps Heps. destruct (Hc eps Heps) as [N HN].
    exists N. intros m n Hm Hn.
    exact (le_lt_trans (@metric Rb (snd (u m)) (snd (u n)))
                       (prod_metric (u m) (u n)) eps
            (prod_metric_le_r (u m) (u n)) (HN m n Hm Hn)). }
  destruct (@cauchy_complete Rb (fun n => fst (u n)) Hf) as [a1 p1].
  destruct (@cauchy_complete Rb (fun n => snd (u n)) Hs) as [b1 p2].
  exists (a1, b1). exact (p1, p2).
Defined.

(* ---- the instance itself: all 21 fields constructed (second lawful
       StateSpace instance besides the interface self-instance) ---- *)
Instance prodRR_space : StateSpace Rb := {|
  S := prodRR;
  szero := prod_zero;
  splus := prod_plus;
  smult := prod_smult;
  sopp := prod_opp;
  splus_assoc := prod_plus_assoc;
  splus_comm := prod_plus_comm;
  splus_zero := prod_plus_zero;
  splus_opp := prod_plus_opp;
  smult_one := prod_smult_one;
  smult_assoc := prod_smult_assoc;
  smult_distrib_r := prod_smult_distrib_r;
  smult_distrib_l := prod_smult_distrib_l;
  smetric := prod_metric;
  smetric_sym := prod_metric_sym;
  smetric_pos := prod_metric_pos;
  smetric_zero := prod_metric_zero;
  smetric_triangle := prod_metric_triangle;
  clim := prod_clim;
  clim_unique := prod_clim_unique;
  cauchy_complete_S := prod_cauchy_complete
|}.

(* ============================================================ *)
(* Section 1b.  Three-point separation: the states (0,0)/(1,0)/ *)
(* (0,1) are pairwise non-identical, so the carrier has at      *)
(* least three elements.                                        *)
(* ============================================================ *)
(*   Route: project a pair identity down to the component identity *)
(*   Id zero one, combine with 0 < 1 and left substitution for the *)
(*   strict order, and hit irreflexivity of lt.                    *)

(* ---- component projections of a pair identity ---- *)
Definition pair_inj_l {A B : Set} {x x' : A} {y y' : B}
  (p : Id (pair x y) (pair x' y')) : Id x x' := id_cong (@fst A B) p.

Definition pair_inj_r {A B : Set} {x x' : A} {y y' : B}
  (p : Id (pair x y) (pair x' y')) : Id y y' := id_cong (@snd A B) p.

Definition state00_ne_state10 :
  Not (Id (@pair (@R Rb) (@R Rb) (@zero Rb) (@zero Rb))
          (@pair (@R Rb) (@R Rb) (@one Rb) (@zero Rb))).
Proof.
  intros H.
  apply (@lt_irrefl Rb (@one Rb)).
  exact (@lt_id_l Rb (@one Rb) (@zero Rb) (@one Rb)
           (id_sym (pair_inj_l H)) one_pos).
Defined.

Definition state00_ne_state01 :
  Not (Id (@pair (@R Rb) (@R Rb) (@zero Rb) (@zero Rb))
          (@pair (@R Rb) (@R Rb) (@zero Rb) (@one Rb))).
Proof.
  intros H.
  apply (@lt_irrefl Rb (@one Rb)).
  exact (@lt_id_l Rb (@one Rb) (@zero Rb) (@one Rb)
           (id_sym (pair_inj_r H)) one_pos).
Defined.

Definition state10_ne_state01 :
  Not (Id (@pair (@R Rb) (@R Rb) (@one Rb) (@zero Rb))
          (@pair (@R Rb) (@R Rb) (@zero Rb) (@one Rb))).
Proof.
  intros H.
  apply (@lt_irrefl Rb (@one Rb)).
  exact (@lt_id_l Rb (@one Rb) (@zero Rb) (@one Rb)
           (pair_inj_l H) one_pos).
Defined.

End ProductCarrier.

(* ============================================================ *)
(* Section 2.  Collapse of squaring carriers: any StateSpace    *)
(* carrier obeying the pointwise law y + y = 0 degenerates to   *)
(* the zero carrier, because each scalar factors as             *)
(* 4 * (a * 4^-1) with 4 = 1+1+1+1 > 0.  Finite carriers        *)
(* (bool pairs, enumerations) are thereby ruled out as lawful   *)
(* instances, and a nontrivial instance must be infinite.       *)
(* ============================================================ *)

Section SquaringCollapse.

Context {RIE : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let Rb : RealInterface := @RI_base RIE.
Let scalar_four : @R Rb :=
  @plus Rb (@plus Rb (@one Rb) (@one Rb)) (@plus Rb (@one Rb) (@one Rb)).

Variable SSc : StateSpace Rb.
Hypothesis sq_law : forall y : @S Rb SSc, Id (@splus Rb SSc y y) (@szero Rb SSc).

Definition scalar_four_pos : @lt Rb (@zero Rb) scalar_four.
Proof.
  assert (Htw : @lt Rb (@zero Rb) (@plus Rb (@one Rb) (@one Rb))).
  { exact (@lt_id_l Rb (@zero Rb) (@plus Rb (@zero Rb) (@zero Rb))
            (@plus Rb (@one Rb) (@one Rb))
            (id_sym (@plus_zero Rb (@zero Rb)))
            (@lt_plus_compat RIE (@zero Rb) (@one Rb) (@zero Rb) (@one Rb)
                              (@one_pos RIE) (@one_pos RIE))). }
  exact (@lt_id_l Rb (@zero Rb) (@plus Rb (@zero Rb) (@zero Rb)) scalar_four
          (id_sym (@plus_zero Rb (@zero Rb)))
          (@lt_plus_compat RIE (@zero Rb) (@plus Rb (@one Rb) (@one Rb))
                              (@zero Rb) (@plus Rb (@one Rb) (@one Rb))
                              Htw Htw)).
Defined.

(* scalar division: four * (a * four^-1) == a for every real scalar a *)
Definition scalar_four_div (a : @R Rb) :
  Id (@mult Rb scalar_four (@mult Rb a (@inv_pos Rb scalar_four scalar_four_pos))) a :=
  id_trans (@mult_assoc Rb scalar_four a (@inv_pos Rb scalar_four scalar_four_pos))
    (id_trans (id_cong (fun t => @mult Rb t (@inv_pos Rb scalar_four scalar_four_pos))
                       (@mult_comm Rb scalar_four a))
      (id_trans (id_sym (@mult_assoc Rb a scalar_four
                          (@inv_pos Rb scalar_four scalar_four_pos)))
        (id_trans (id_cong (fun t => @mult Rb a t)
                           (@inv_pos_correct Rb scalar_four scalar_four_pos))
                  (@mult_one Rb a)))).

(* action collapse: every scalar action sends every carrier element to szero *)
Definition smult_null :
  forall (a : @R Rb) (y : @S Rb SSc),
    Id (@smult Rb SSc a y) (@szero Rb SSc).
Proof.
  intros a y.
  set (i4 := @inv_pos Rb scalar_four scalar_four_pos).
  set (c := @mult Rb a i4).
  set (cy := @smult Rb SSc c y).
  set (twR := @plus Rb (@one Rb) (@one Rb)).
  (* H1: rewrite the scalar a as four * c (c := a * four^-1) *)
  assert (H1 : Id (@smult Rb SSc a y) (@smult Rb SSc (@mult Rb scalar_four c) y)).
  { exact (id_cong (fun t => @smult Rb SSc t y)
                   (id_sym (scalar_four_div a))). }
  (* H2: four * c == (two * c) + (two * c)  (left distributivity) *)
  assert (H2 : Id (@mult Rb scalar_four c)
                  (@plus Rb (@mult Rb twR c) (@mult Rb twR c))).
  { exact (@mult_distrib_l RIE twR twR c). }
  (* H3: one-limb action smult (two * c) y == cy + cy *)
  assert (H3 : Id (@smult Rb SSc (@mult Rb twR c) y)
                  (@splus Rb SSc cy cy)).
  { exact (id_trans
             (id_cong (fun t => @smult Rb SSc t y)
                       (@mult_distrib_l RIE (@one Rb) (@one Rb) c))
             (id_trans (@smult_distrib_l Rb SSc (@mult Rb (@one Rb) c)
                                         (@mult Rb (@one Rb) c) y)
               (id_trans
                  (id_cong (fun t => @splus Rb SSc t
                                              (@smult Rb SSc (@mult Rb (@one Rb) c) y))
                           (id_cong (fun t => @smult Rb SSc t y)
                                    (id_trans (@mult_comm Rb (@one Rb) c)
                                              (@mult_one Rb c))))
                  (id_cong (fun t => @splus Rb SSc cy t)
                           (id_cong (fun t => @smult Rb SSc t y)
                                    (id_trans (@mult_comm Rb (@one Rb) c)
                                              (@mult_one Rb c))))))). }
  (* H4: smult (four * c) y == (cy + cy) + (cy + cy) *)
  assert (H4 : Id (@smult Rb SSc (@mult Rb scalar_four c) y)
                  (@splus Rb SSc (@splus Rb SSc cy cy) (@splus Rb SSc cy cy))).
  { exact (id_trans (id_cong (fun t => @smult Rb SSc t y) H2)
            (id_trans (@smult_distrib_l Rb SSc (@mult Rb twR c) (@mult Rb twR c) y)
              (id_trans
                 (id_cong (fun t => @splus Rb SSc t
                                              (@smult Rb SSc (@mult Rb twR c) y)) H3)
                 (id_cong (fun t => @splus Rb SSc (@splus Rb SSc cy cy) t)
                           H3)))). }
  (* H5: (cy + cy) + (cy + cy) == szero (squaring law twice, then unit) *)
  assert (H5 : Id (@splus Rb SSc (@splus Rb SSc cy cy) (@splus Rb SSc cy cy))
                  (@szero Rb SSc)).
  { exact (id_trans
             (id_cong (fun t => @splus Rb SSc t (@splus Rb SSc cy cy)) (sq_law cy))
             (id_trans
                (id_cong (fun t => @splus Rb SSc (@szero Rb SSc) t) (sq_law cy))
                (@splus_zero Rb SSc (@szero Rb SSc)))). }
  exact (id_trans H1 (id_trans H4 H5)).
Defined.

Theorem squaring_carrier_collapse : forall y : @S Rb SSc, Id y (@szero Rb SSc).
Proof.
  intros y.
  exact (id_trans (id_sym (@smult_one Rb SSc y))
                  (smult_null (@one Rb) y)).
Defined.

End SquaringCollapse.

(* ============================================================ *)
(* Section 3.  Realization of the abstract list-summation       *)
(* statements on this carrier: the abstract summation machine   *)
(* idt_sumf agrees with the list fold idt_list_sum, and with    *)
(* the host fold machine bs_list_sum, at the product carrier.   *)
(* ============================================================ *)

Section SummationSlot.

Context {RIE : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Definition prodRR_sum_eq_list :
  forall (enum : list (@S (@RI_base RIE) prodRR_space))
         (g : @S (@RI_base RIE) prodRR_space -> @R (@RI_base RIE)),
    Id (@IdSlotTranslate.idt_sumf RIE prodRR_space enum g)
       (@IdSlotTranslate.idt_list_sum RIE prodRR_space g enum).
Proof.
  intros enum g.
  exact (@IdSlotTranslate.idt_sum_eq_list RIE prodRR_space enum g).
Defined.

Definition prodRR_idt_slot :
  forall (enum : list (@S (@RI_base RIE) prodRR_space))
         (g : @S (@RI_base RIE) prodRR_space -> @R (@RI_base RIE)),
    Id (@IdSlotTranslate.idt_sumf RIE prodRR_space enum g)
       (@AttnDoeblin.bs_list_sum RIE prodRR_space g enum).
Proof.
  intros enum g.
  exact (@IdSlotTranslate.idt_slot_g01 RIE prodRR_space enum g).
Defined.

End SummationSlot.

(* ============================================================ *)
(* Assumption audit: one line per named statement of this file. *)
(* ============================================================ *)
Print Assumptions pair_id_pair.
Print Assumptions mult_distrib_l.
Print Assumptions plus_pair_swap.
Print Assumptions prod_metric_le_l.
Print Assumptions prod_metric_le_r.
Print Assumptions prod_plus_assoc.
Print Assumptions prod_plus_comm.
Print Assumptions prod_plus_zero.
Print Assumptions prod_plus_opp.
Print Assumptions prod_smult_one.
Print Assumptions prod_smult_assoc.
Print Assumptions prod_smult_distrib_r.
Print Assumptions prod_smult_distrib_l.
Print Assumptions prod_metric_sym.
Print Assumptions prod_metric_pos.
Print Assumptions prod_metric_zero.
Print Assumptions prod_metric_triangle.
Print Assumptions prod_clim_unique.
Print Assumptions prod_cauchy_complete.
Print Assumptions prodRR_space.
Print Assumptions pair_inj_l.
Print Assumptions pair_inj_r.
Print Assumptions state00_ne_state10.
Print Assumptions state00_ne_state01.
Print Assumptions state10_ne_state01.
Print Assumptions scalar_four_pos.
Print Assumptions scalar_four_div.
Print Assumptions smult_null.
Print Assumptions squaring_carrier_collapse.
Print Assumptions prodRR_sum_eq_list.
Print Assumptions prodRR_idt_slot.
