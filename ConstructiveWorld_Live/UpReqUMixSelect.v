(* ConstructiveWorld-Set -- abstract-interface mixing-time selection family. *)

(** * UpReqUMixSelect: interface-layer mixing-time selector with explicit k selection.

    Mission.  This module ports the explicit k selection machine of the
      concrete Cauchy real layer to the abstract RealInterface layer:
      the nat-scale partial-sum accumulator [ums_scale] with its
      positivity lemmas, the interface ring small lemmas, the Bernoulli
      upper bound [ums_bernoulli_upper], the inverse-factor lemma
      [ums_le_inv], the tail chain [ums_pow_tail], and the selector
      theorems [ums_k_select], [ums_pow_budget] and [ums_k_select_le],
      producing k with [mult (r_pow kappa k) TV0] below budget.

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv] of this development.

    References.  This development, UpReqUMixSelect.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  Honest per-item disclosure: the interface order and
      identity faces are Set-valued fields ([lt]/[le]/[Id] : Set, S01
      RealInterface); statement bodies at a fixed interface instance are
      Set-carried, including the [sigT] witness heads of the selectors;
      closed statements are Type-carried via the Type-sorted interface
      class binder.  No Prop carrier anywhere.  Account: disclosure block.

    Build.  [coqc -native-compiler no -q -Q . "" UpReqUMixSelect.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc] (local 9.3.0). *)

Require Import S01_BaseRing.
Require Import S04_RealExpLogConv.

(* ===== Per-item constructivity disclosure (batch 10/11 correction) ====== *)
(* The former header blanket claim "all named statements and fields are     *)
(* carried by Set ... extract with [Obj.magic] = 0 and no erasure ...       *)
(* [coqchk] reports [Axioms: none]" was false as stated and is withdrawn.   *)
(* Machine-checked account (local Rocq 9.3.0 sort pins + ascriptions):      *)
(*   - Interface faces: [lt]/[le] : R -> R -> Set and [Id] : Set are        *)
(*     Set-valued fields of RealInterface/RealInterfaceEnhanced (S01_Base-  *)
(*     Ring.v lines 41, 112, 120-121); [Or]/[Not] are Set-level.  The pin   *)
(*     [lt zero one : Set] compiles; the same pin at Prop fails with        *)
(*     [Cannot enforce Set <= Prop].                                        *)
(*   - Main statements: [ums_pow_tail], [ums_k_select], [ums_pow_budget],   *)
(*     [ums_k_select_le] conclude in [sigT] witnesses over [nat] with       *)
(*     Set-valued [lt]; [sigT] at a Set instance is Set-sorted (template),  *)
(*     and the full statement bodies pin at Set (the whole [ums_k_select]   *)
(*     premise-conclusion shape pins at Set).  These are the extraction     *)
(*     targets: gate7 Separate Extraction over all 25 names runs rc=0 with  *)
(*     magic=0 on both faces and zero erasure candidates.                   *)
(*   - Support lemmas (Parts 1-6): statement bodies equally Set-carried at  *)
(*     a fixed instance; per the batch 10/11 review the Main-baseline       *)
(*     statements of these names are Prop-face, re-carried here on this     *)
(*     Set face and consumed only inside the proofs below -- reasoning      *)
(*     face, no separate extraction contract claimed for them.              *)
(*   - Closed form: every named constant quantifies over the interface      *)
(*     class, which is Type-sorted (About: Type, not universe polymorphic), *)
(*     so the closed statement sorts are Type@{Set+1}: the closed pin at    *)
(*     Set fails with [Cannot enforce Set+1 <= Set] and the same shape at   *)
(*     Type passes; the Set-carried content sits beneath the class binder.  *)
(*     Statement names and types are untouched by this disclosure.          *)
(*   - Audits: 12 closing [Print Assumptions] report Closed under the       *)
(*     global context; [coqchk] rechecks the module cleanly; the artifact   *)
(*     starts [436f7121 000160bc] -- the former [00015ff4] bytes were the   *)
(*     9.1-era vo version word (90100), superseded by 90300 on 9.3.0.       *)

Section UMixSelect.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* Unpack the RealInterface fields, as in UpEntropyGain and AttnDoeblin. *)
Let R := @R RI.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let lt   := @lt RI.
Let le   := @le RI.
(* minus stays a global definition, [minus a b := plus a (opp b)], used
   by definitional unfolding. *)

(* ===== Honest interface: the mixed lt+le monotonicity of plus ===== *)
(* The le side of the interface is an opaque Set field carrying no
   positivity data, so strict monotonicity of addition cannot be derived
   inside the interface layer; every strict warming step below rests on
   this single declared premise, as in the same-named Variables of the
   convergence sections. *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* ============================================================ *)
(* Part 1. the nat-scale partial-sum accumulator, mirroring mix_scale. *)
(* ============================================================ *)

Fixpoint ums_scale (k : nat) (w : R) : R :=
  match k with
  | Datatypes.O => zero
  | Datatypes.S m => plus w (ums_scale m w)
  end.

(* nat-scale nonnegativity: 0 <= w gives 0 <= k*w. *)
Lemma ums_scale_nonneg : forall (w : R) (k : nat),
  le zero w -> le zero (ums_scale k w).
Proof.
  intros w k Hw. induction k as [| k IH].
  - exact (le_refl zero).
  - exact (le_id_l zero (plus zero zero) (plus w (ums_scale k w))
             (id_sym (plus_zero zero))
             (le_plus_compat zero w zero (ums_scale k w) Hw IH)).
Defined.

(* nat-scale strict positivity: 0 < w gives 0 < (S k)*w, since
   (S k)*w = w + k*w >= w > 0. *)
Lemma ums_scale_S_pos : forall (w : R) (k : nat),
  lt zero w -> lt zero (ums_scale (Datatypes.S k) w).
Proof.
  intros w k Hw.
  exact (lt_id_l zero (plus zero zero) (plus w (ums_scale k w))
           (id_sym (plus_zero zero))
           (lt_plus_compat_lt_le zero w zero (ums_scale k w)
              Hw (ums_scale_nonneg w k (lt_le_iff zero w (inl Hw))))).
Defined.

(* boost positivity: 1 + k*w > 0, from 0 <= w alone. *)
Lemma ums_boost_pos : forall (w : R) (k : nat),
  le zero w -> lt zero (plus one (ums_scale k w)).
Proof.
  intros w k Hw.
  exact (lt_id_l zero (plus zero zero) (plus one (ums_scale k w))
           (id_sym (plus_zero zero))
           (lt_plus_compat_lt_le zero one zero (ums_scale k w)
              one_pos (ums_scale_nonneg w k Hw))).
Defined.

(* ============================================================ *)
(* Part 2. interface stand-ins for the concrete pointwise ring lemmas. *)
(*   R is an abstract field, so no case analysis on elements is
   available; every step goes through Id chains and congruence
   rewriting. *)
(* ============================================================ *)

(* 1*x == x, by swapping the left factor inside mult_one. *)
Lemma ums_mult_one_l : forall x : R, Id (mult one x) x.
Proof.
  intro x. exact (id_trans (mult_comm one x) (mult_one x)).
Defined.

(* x*(-y) == -(x*y): commute into the left-factor shape and read off
   opp_mult_r of S01 directly. *)
Lemma ums_mult_opp_r : forall x y : R, Id (mult x (opp y)) (opp (mult x y)).
Proof.
  intros x y.
  exact (id_trans (mult_comm x (opp y))
           (id_trans (opp_mult_r y x)
                     (id_cong (fun z => opp z) (mult_comm y x)))).
Defined.

(* multiplication swap: (a*b)*c == b*(a*c). *)
Lemma ums_mult_swap : forall a b c : R,
  Id (mult (mult a b) c) (mult b (mult a c)).
Proof.
  intros a b c.
  exact (id_trans (id_cong2 mult (mult_comm a b) (id_refl))
           (id_sym (mult_assoc b a c))).
Defined.

(* inverse cancellation: x*(y*inv(x)) == y for 0 < x, mirroring
   real_mult_div. *)
Lemma ums_mult_div : forall (x y : R) (H : lt zero x),
  Id (mult x (mult y (inv_pos x H))) y.
Proof.
  intros x y H.
  apply (id_trans (mult_assoc x y (inv_pos x H))).
  apply (id_trans (id_cong2 mult (mult_comm x y) (id_refl))).
  apply (id_trans (id_sym (mult_assoc y x (inv_pos x H)))).
  apply (id_trans (id_cong (fun z => mult y z) (inv_pos_correct x H))).
  exact (mult_one y).
Defined.

(* right addition shift under le: 0 <= d gives x <= x + d, the weak
   form of igr_le_plus_r. *)
Lemma ums_le_plus_r : forall x d : R, le zero d -> le x (plus x d).
Proof.
  intros x d Hd.
  exact (le_id_l x (plus x zero) (plus x d) (id_sym (plus_zero x))
           (le_plus_compat x x zero d (le_refl x) Hd)).
Defined.

(* subtraction is invertible: (a - b) + b == a. *)
Lemma ums_minus_plus_cancel : forall a b : R, Id (plus (minus a b) b) a.
Proof.
  intros a b. unfold minus.
  apply (id_trans (plus_comm (plus a (opp b)) b)).
  apply (id_trans (plus_assoc b a (opp b))).
  apply (id_trans (id_cong (fun z => plus z (opp b)) (plus_comm b a))).
  apply (id_trans (id_sym (plus_assoc a b (opp b)))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_opp b))).
  exact (plus_zero a).
Defined.

(* subtraction body for le: 0 <= d gives X - d <= X, via ums_le_plus_r
   and the invertibility swap, in the usage shape of igr_le_plus_r. *)
Lemma ums_minus_le : forall X d : R, le zero d -> le (minus X d) X.
Proof.
  intros X d Hd.
  exact (le_id_r (minus X d) (plus (minus X d) d) X
           (ums_minus_plus_cancel X d) (ums_le_plus_r (minus X d) d Hd)).
Defined.

(* ============================================================ *)
(* Part 3. rate certificate small lemmas and the power face. *)
(* ============================================================ *)

(* piece 3: 0 < w < 1 gives 0 < 1 - w, the target-book ums_omd_lt_one,
   isomorphic to eg_minus_pos. *)
Lemma ums_omd_lt_one : forall w : R,
  lt zero w -> lt w one -> lt zero (minus one w).
Proof.
  intros w Hw0 Hw1. unfold minus.
  apply (lt_id_l zero (plus w (opp w)) (plus one (opp w))
           (id_sym (plus_opp w))).
  exact (lt_plus_compat_lt_le w one (opp w) (opp w) Hw1 (le_refl (opp w))).
Defined.

(* double complement for omd: x == 1 - (1 - x), by an Id chain,
   mirroring mix_omd_id. *)
Lemma ums_omd_id : forall x : R, Id x (minus one (minus one x)).
Proof.
  intro x. apply id_sym.
  exact (id_trans (id_cong (fun z => plus one z) (opp_plus one (opp x)))
           (id_trans (id_cong (fun z => plus one (plus (opp one) z))
                       (double_neg x))
              (id_trans (plus_assoc one (opp one) x)
                 (id_trans (id_cong (fun z => plus z x) (plus_opp one))
                    (id_trans (plus_comm zero x) (plus_zero x)))))).
Defined.

(* congruence of powers: equal bases give equal powers. *)
Lemma ums_rpow_eq_compat : forall (x y : R) (k : nat),
  Id x y -> Id (r_pow x k) (r_pow y k).
Proof.
  intros x y k Hxy. induction k as [| k IH].
  - exact (@id_refl R one).
  - exact (id_cong2 mult Hxy IH).
Defined.

(* piece 2, power positivity: 0 < a gives 0 < a^k, mirroring
   r_pow_pos and mix_rpow_pos. *)
Lemma ums_rpow_pos : forall (a : R) (k : nat),
  lt zero a -> lt zero (r_pow a k).
Proof.
  intros a k Ha. induction k as [| k IH].
  - exact (one_pos).
  - exact (mult_positive a (r_pow a k) Ha IH).
Defined.

(* nat-scale distribution over the right factor: (k*x)*z == k*(x*z),
   by an Id chain. *)
Lemma ums_scale_mult_distrib : forall (k : nat) (x z : R),
  Id (mult (ums_scale k x) z) (ums_scale k (mult x z)).
Proof.
  intros k. induction k as [| k IH]; intros x z.
  - exact (id_trans (mult_comm zero z) (mult_zero z)).
  - apply (id_trans (mult_comm (plus x (ums_scale k x)) z)).
    apply (id_trans (distrib z x (ums_scale k x))).
    apply (id_trans (id_cong
                       (fun w => plus w (mult z (ums_scale k x)))
                       (mult_comm z x))).
    apply (id_trans (id_cong
                       (fun w => plus (mult x z) w)
                       (mult_comm z (ums_scale k x)))).
    apply (id_trans (id_cong (fun w => plus (mult x z) w) (IH x z))).
    apply id_refl.
Defined.

(* ============================================================ *)
(* Part 4. the Bernoulli upper form: the contraction core without exp
   or log.  Key lemma: (1-w)^k*(1 + k*w) <= 1 for 0 < w < 1; the
   proof structure mirrors mix_bernoulli_upper, with the ring exit
   given by ums_ring_sc. *)
(* ============================================================ *)

(* generic ring core in cancel-ready shape, used directly by the
   subtraction-le body:
   (1-w)*(1+w+s) + (w+s)*w == 1+s, by an Id chain (rewrite is
   unavailable under the Let-unpacked fields). *)
Lemma ums_bernoulli_cancel : forall w s : R,
  Id (plus (mult (minus one w) (plus one (plus w s))) (mult (plus w s) w))
     (plus one s).
Proof.
  intros w s. unfold minus.
  apply (id_trans (id_cong (fun z => plus z (mult (plus w s) w))
                     (distrib (plus one (opp w)) one (plus w s)))).
  apply (id_trans (id_cong
                     (fun z => plus (plus z (mult (plus one (opp w))
                                            (plus w s)))
                                (mult (plus w s) w))
                     (mult_one (plus one (opp w))))).
  apply (id_trans (id_cong
                     (fun z => plus (plus (plus one (opp w)) z)
                                (mult (plus w s) w))
                     (mult_comm (plus one (opp w)) (plus w s)))).
  apply (id_trans (id_cong
                     (fun z => plus (plus (plus one (opp w)) z)
                                (mult (plus w s) w))
                     (distrib (plus w s) one (opp w)))).
  apply (id_trans (id_cong
                     (fun z => plus (plus (plus one (opp w))
                                     (plus z (mult (plus w s) (opp w))))
                                (mult (plus w s) w))
                     (mult_one (plus w s)))).
  apply (id_trans (id_cong
                     (fun z => plus (plus (plus one (opp w))
                                     (plus (plus w s) z))
                                (mult (plus w s) w))
                     (ums_mult_opp_r (plus w s) w))).
  apply (id_trans (id_sym (plus_assoc (plus one (opp w))
                             (plus (plus w s) (opp (mult (plus w s) w)))
                             (mult (plus w s) w)))).
  apply (id_trans (id_cong (fun z => plus (plus one (opp w)) z)
                     (id_sym (plus_assoc (plus w s)
                                (opp (mult (plus w s) w))
                                (mult (plus w s) w))))).
  apply (id_trans (id_cong
                     (fun z => plus (plus one (opp w)) (plus (plus w s) z))
                     (id_trans (plus_comm (opp (mult (plus w s) w))
                                (mult (plus w s) w))
                        (plus_opp (mult (plus w s) w))))).
  apply (id_trans (id_cong (fun z => plus (plus one (opp w)) z)
                     (plus_zero (plus w s)))).
  apply (id_trans (id_sym (plus_assoc one (opp w) (plus w s)))).
  apply (id_trans (id_cong (fun z => plus one z)
                     (plus_assoc (opp w) w s))).
  apply (id_trans (id_cong (fun z => plus one (plus z s))
                     (id_trans (plus_comm (opp w) w) (plus_opp w)))).
  apply (id_trans (id_cong (fun z => plus one z) (plus_comm zero s))).
  apply (id_cong (fun z => plus one z) (plus_zero s)).
Defined.

(* from cancellation to subtraction: X + Y == Z gives X == Z - Y, the
   general bridge into the ring exit. *)
Lemma ums_cancel_to_minus : forall X Y Z : R,
  Id (plus X Y) Z -> Id X (minus Z Y).
Proof.
  intros X Y Z HC. unfold minus.
  exact (id_trans (id_sym (plus_zero X))
           (id_trans
              (id_cong (fun z => plus X z) (id_sym (plus_opp Y)))
              (id_trans (plus_assoc X Y (opp Y))
                 (id_cong (fun z => plus z (opp Y)) HC)))).
Defined.

(* the ring exit, mirroring the original mix_ring_sc:
   (1-u)*(1+u+a) == (1+a) - (u+a)*u. *)
Lemma ums_ring_sc : forall u a : R,
  Id (mult (minus one u) (plus one (plus u a)))
     (minus (plus one a) (mult (plus u a) u)).
Proof.
  intros u a.
  exact (ums_cancel_to_minus
           (mult (minus one u) (plus one (plus u a)))
           (mult (plus u a) u) (plus one a)
           (ums_bernoulli_cancel u a)).
Defined.

(* piece 4, the main wall: (1-w)^k*(1+k*w) <= 1 for 0 < w < 1. *)
Lemma ums_bernoulli_upper : forall (w : R) (k : nat),
  lt zero w -> lt w one ->
  le (mult (r_pow (minus one w) k) (plus one (ums_scale k w))) one.
Proof.
  intros w k Hwp Hwlt. induction k as [| k IH].
  - (* k = 0: 1*(1+0) == 1. *)
    change (le (mult one (plus one (ums_scale 0 w))) one).
    exact (le_id_l (mult one (plus one (ums_scale 0 w))) one one
             (id_trans (mult_comm one (plus one (ums_scale 0 w)))
                (id_trans (mult_one (plus one (ums_scale 0 w)))
                          (plus_zero one)))
             (le_refl one)).
  - (* induction step: the ring identity
       (1-w)*(1+(k+1)*w) == (1+k*w) - ((k+1)*w)*w <= 1+k*w,
       then the power-positivity factor and the transposed induction
       premise take the goal back to the IH. *)
    assert (Hbpos : lt zero (minus one w))
      by exact (ums_omd_lt_one w Hwp Hwlt).
    assert (HPk : lt zero (r_pow (minus one w) k))
      by exact (ums_rpow_pos (minus one w) k Hbpos).
    assert (HC : lt zero (mult (ums_scale (Datatypes.S k) w) w))
      by exact (mult_positive (ums_scale (Datatypes.S k) w) w
                  (ums_scale_S_pos w k Hwp) Hwp).
    assert (HSC : le (mult (minus one w)
                         (plus one (ums_scale (Datatypes.S k) w)))
                     (plus one (ums_scale k w))).
    { apply (le_id_l (mult (minus one w)
                         (plus one (plus w (ums_scale k w))))
                     (minus (plus one (ums_scale k w))
                            (mult (ums_scale (Datatypes.S k) w) w))
                     (plus one (ums_scale k w))).
      - exact (ums_ring_sc w (ums_scale k w)).
      - exact (ums_minus_le (plus one (ums_scale k w))
                 (mult (ums_scale (Datatypes.S k) w) w)
                 (lt_le_iff zero (mult (ums_scale (Datatypes.S k) w) w)
                              (inl HC))). }
    assert (HeqR : Id (mult (mult (minus one w) (r_pow (minus one w) k))
                            (plus one (ums_scale (Datatypes.S k) w)))
                       (mult (mult (minus one w)
                                   (plus one (ums_scale (Datatypes.S k) w)))
                             (r_pow (minus one w) k)))
      by exact (id_trans (ums_mult_swap (minus one w) (r_pow (minus one w) k)
                            (plus one (ums_scale (Datatypes.S k) w)))
                  (mult_comm (r_pow (minus one w) k)
                     (mult (minus one w)
                           (plus one (ums_scale (Datatypes.S k) w))))).
    assert (IH' : le (mult (plus one (ums_scale k w))
                           (r_pow (minus one w) k))
                     one).
    { exact (le_id_l (mult (plus one (ums_scale k w))
                           (r_pow (minus one w) k))
                     (mult (r_pow (minus one w) k)
                           (plus one (ums_scale k w)))
                     one
                     (mult_comm (plus one (ums_scale k w))
                                (r_pow (minus one w) k))
                     IH). }
    apply (le_trans _ (mult (plus one (ums_scale k w))
                            (r_pow (minus one w) k))).
    + exact (le_id_l (mult (r_pow (minus one w) (Datatypes.S k))
                             (plus one (ums_scale (Datatypes.S k) w)))
                     (mult (mult (minus one w)
                                 (plus one (ums_scale (Datatypes.S k) w)))
                           (r_pow (minus one w) k))
                     (mult (plus one (ums_scale k w))
                           (r_pow (minus one w) k))
                     HeqR
                     (le_mult_compat (mult (minus one w)
                                         (plus one (ums_scale (Datatypes.S k) w)))
                                     (plus one (ums_scale k w))
                                     (r_pow (minus one w) k) HPk HSC)).
    + exact IH'.
Defined.

(* ============================================================ *)
(* Part 5. the inverse-factor lemma: A*B <= 1 and 0 < B give
   A <= 1/B, mirroring mix_le_inv. *)
(* ============================================================ *)

Lemma ums_le_inv : forall (A B : R) (HB : lt zero B),
  le (mult A B) one -> le A (inv_pos B HB).
Proof.
  intros A B HB HAB.
  assert (HBp : lt zero (inv_pos B HB)) by exact (inv_pos_pos B HB).
  apply (le_trans A (mult (mult A B) (inv_pos B HB)) (inv_pos B HB)).
  - exact (le_id_l A (mult (mult A B) (inv_pos B HB))
                     (mult (mult A B) (inv_pos B HB))
             (id_trans (id_trans (id_sym (mult_one A))
                          (id_cong (fun z => mult A z)
                             (id_sym (inv_pos_correct B HB))))
                   (mult_assoc A B (inv_pos B HB)))
             (le_refl (mult (mult A B) (inv_pos B HB)))).
  - exact (le_id_r (mult (mult A B) (inv_pos B HB))
                     (mult one (inv_pos B HB)) (inv_pos B HB)
             (ums_mult_one_l (inv_pos B HB))
             (le_mult_compat (mult A B) one (inv_pos B HB) HBp HAB)).
Defined.

(* ============================================================ *)
(* Part 6. the k selection main theorem: the tail-chain core. *)
(*   The Arch witness is taken in the nat-scale shape
   [ums_scale (Datatypes.S N) one]: the interface has no real_const,
   the concrete layer bridges this shape to the constant form, n >= 1
   holds by construction, and the 2 <= n component dissolves.  The omd
   certificate is gathered as a premise shared by both selector heads;
   the chain mirrors the mix_pow_budget main chain. *)
(* ============================================================ *)

Lemma ums_pow_tail :
  forall (kappa TV0 budget w : R) (N : nat)
         (Hwb : lt zero (mult w budget)),
    lt zero w -> lt w one -> Id kappa (minus one w) ->
    le zero TV0 -> le zero budget ->
    lt (mult TV0 (inv_pos (mult w budget) Hwb))
       (ums_scale (Datatypes.S N) one) ->
    sigT (fun k : nat => lt (mult (r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget w N Hwb Hw0 Hwlt1 Heqk Ha Hbudget0 HN.
  assert (Hwle : le zero w) by exact (lt_le_iff zero w (inl Hw0)).
  set (wb := mult w budget).
  set (invwb := inv_pos wb Hwb).
  set (Ms := ums_scale (Datatypes.S N) w).
  set (boost := plus one Ms).
  assert (Hboost0 : lt zero boost)
    by exact (ums_boost_pos w (Datatypes.S N) Hwle).
  set (invB := inv_pos boost Hboost0).
  assert (HinvB : lt zero invB) by exact (inv_pos_pos boost Hboost0).
  (* ---- budget leg: TV0 < Ms*budget ---- *)
  assert (Hstep : lt (mult (mult TV0 invwb) wb)
                     (mult (ums_scale (Datatypes.S N) one) wb))
    by exact (lt_mult_compat (mult TV0 invwb)
                (ums_scale (Datatypes.S N) one) wb Hwb HN).
  assert (HeqL : Id (mult (mult TV0 invwb) wb) TV0)
    by exact (id_trans (mult_comm (mult TV0 invwb) wb)
                (ums_mult_div wb TV0 Hwb)).
  assert (HeqR : Id (mult (ums_scale (Datatypes.S N) one) wb)
                     (mult Ms budget))
    by exact (id_trans
           (id_trans (ums_scale_mult_distrib (Datatypes.S N) one wb)
              (id_cong (fun z => ums_scale (Datatypes.S N) z)
                       (ums_mult_one_l wb)))
           (id_sym (ums_scale_mult_distrib (Datatypes.S N) w budget))).
  assert (Hb0 : lt TV0 (mult Ms budget)).
  { exact (lt_id_r TV0 (mult (ums_scale (Datatypes.S N) one) wb)
             (mult Ms budget) HeqR
             (lt_id_l TV0 (mult (mult TV0 invwb) wb)
                (mult (ums_scale (Datatypes.S N) one) wb)
                (id_sym HeqL) Hstep)). }
  assert (HeqBud : Id (mult budget boost) (plus budget (mult Ms budget)))
    by exact (id_trans (distrib budget one Ms)
                (id_cong2 plus (mult_one budget) (mult_comm budget Ms))).
  assert (Hbud : lt TV0 (mult budget boost)).
  { exact (lt_id_r TV0 (plus (mult Ms budget) budget) (mult budget boost)
             (id_sym (id_trans HeqBud (plus_comm budget (mult Ms budget))))
             (lt_le_trans TV0 (mult Ms budget)
                (plus (mult Ms budget) budget) Hb0
                (ums_le_plus_r (mult Ms budget) budget Hbudget0))). }
  exists (Datatypes.S N).
  (* ---- main chain: kappa^(S N)*TV0 < budget ---- *)
  assert (Heqp : Id (r_pow kappa (Datatypes.S N))
                     (r_pow (minus one w) (Datatypes.S N)))
    by exact (ums_rpow_eq_compat kappa (minus one w) (Datatypes.S N) Heqk).
  assert (Hbern : le (mult (r_pow (minus one w) (Datatypes.S N)) boost) one)
    by exact (ums_bernoulli_upper w (Datatypes.S N) Hw0 Hwlt1).
  assert (Hinvleg : le (r_pow (minus one w) (Datatypes.S N)) invB)
    by exact (ums_le_inv (r_pow (minus one w) (Datatypes.S N)) boost
                Hboost0 Hbern).
  apply (le_lt_trans _ (mult invB TV0) budget).
  + exact (le_id_l (mult (r_pow kappa (Datatypes.S N)) TV0)
                   (mult (r_pow (minus one w) (Datatypes.S N)) TV0)
                   (mult invB TV0)
             (id_cong2 mult Heqp (id_refl))
             (le_mult_compat_weak (r_pow (minus one w) (Datatypes.S N))
                invB TV0 Ha Hinvleg)).
  + exact (lt_id_r (mult invB TV0)
              (mult (mult budget boost) invB) budget
              (id_trans (id_cong (fun z => mult z invB)
                           (mult_comm budget boost))
                 (id_trans (id_sym (mult_assoc boost budget invB))
                    (ums_mult_div boost budget Hboost0)))
              (lt_id_l (mult invB TV0) (mult TV0 invB)
                 (mult (mult budget boost) invB)
                 (mult_comm invB TV0)
                 (lt_mult_compat TV0 (mult budget boost) invB HinvB Hbud))).
Defined.

(* ============================================================ *)
(* Part 7. the two selector heads of the G1 main theorem. *)
(* ============================================================ *)

(* piece 5, main form: le premises with the le-shaped Arch given
   directly, the honest interface-layer form. *)
Lemma ums_k_select :
  forall (kappa TV0 budget : R),
    lt zero kappa -> lt kappa one ->
    le zero TV0 -> lt zero budget ->
    (forall x : R, le zero x ->
       sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => lt (mult (r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch.
  assert (hwp : lt zero (minus one kappa))
    by exact (ums_omd_lt_one kappa Hk1 Hk2).
  assert (hwlt : lt (minus one kappa) one).
  { apply (lt_id_r (minus one kappa)
             (plus kappa (minus one kappa)) one
             (id_trans (plus_comm kappa (minus one kappa))
                       (ums_minus_plus_cancel one kappa))).
    apply (lt_id_l (minus one kappa) (plus zero (minus one kappa))
             (plus kappa (minus one kappa))
             (id_sym (id_trans (plus_comm zero (minus one kappa))
                               (plus_zero (minus one kappa))))).
    exact (lt_plus_compat_lt_le zero kappa (minus one kappa)
               (minus one kappa) Hk1 (le_refl (minus one kappa))). }
  assert (Heqk : Id kappa (minus one (minus one kappa)))
    by exact (ums_omd_id kappa).
  assert (Hwb : lt zero (mult (minus one kappa) budget))
    by exact (mult_positive (minus one kappa) budget hwp Hbudget).
  assert (Hinvwbp : lt zero (inv_pos (mult (minus one kappa) budget) Hwb))
    by exact (inv_pos_pos (mult (minus one kappa) budget) Hwb).
  (* Arch application point: TV0*inv(w*budget) >= 0, the le premise
     routed through the weak multiplication compatibility. *)
  assert (Hxle : le zero (mult TV0
                     (inv_pos (mult (minus one kappa) budget) Hwb))).
  { exact (le_id_l zero
             (mult zero (inv_pos (mult (minus one kappa) budget) Hwb))
             (mult TV0 (inv_pos (mult (minus one kappa) budget) Hwb))
             (id_sym (id_trans
                (mult_comm zero (inv_pos (mult (minus one kappa) budget) Hwb))
                (mult_zero (inv_pos (mult (minus one kappa) budget) Hwb))))
             (le_mult_compat_weak zero TV0
                (inv_pos (mult (minus one kappa) budget) Hwb)
                (lt_le_iff zero
                   (inv_pos (mult (minus one kappa) budget) Hwb)
                   (inl Hinvwbp)) Ha)). }
  destruct (Harch (mult TV0 (inv_pos (mult (minus one kappa) budget) Hwb))
                  Hxle) as [N HN].
  exact (ums_pow_tail kappa TV0 budget (minus one kappa) N Hwb
           hwp hwlt Heqk Ha (lt_le_iff zero budget (inl Hbudget)) HN).
Defined.

(* strict version: lt premises with the lt-shaped Arch, isomorphic to
   the full mix_pow_budget form. *)
Lemma ums_pow_budget :
  forall (kappa TV0 budget : R),
    lt zero kappa -> lt kappa one ->
    lt zero TV0 -> lt zero budget ->
    (forall x : R, lt zero x ->
       sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => lt (mult (r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch.
  assert (hwp : lt zero (minus one kappa))
    by exact (ums_omd_lt_one kappa Hk1 Hk2).
  assert (hwlt : lt (minus one kappa) one).
  { apply (lt_id_r (minus one kappa)
             (plus kappa (minus one kappa)) one
             (id_trans (plus_comm kappa (minus one kappa))
                       (ums_minus_plus_cancel one kappa))).
    apply (lt_id_l (minus one kappa) (plus zero (minus one kappa))
             (plus kappa (minus one kappa))
             (id_sym (id_trans (plus_comm zero (minus one kappa))
                               (plus_zero (minus one kappa))))).
    exact (lt_plus_compat_lt_le zero kappa (minus one kappa)
               (minus one kappa) Hk1 (le_refl (minus one kappa))). }
  assert (Heqk : Id kappa (minus one (minus one kappa)))
    by exact (ums_omd_id kappa).
  assert (Hwb : lt zero (mult (minus one kappa) budget))
    by exact (mult_positive (minus one kappa) budget hwp Hbudget).
  assert (Hinvwbp : lt zero (inv_pos (mult (minus one kappa) budget) Hwb))
    by exact (inv_pos_pos (mult (minus one kappa) budget) Hwb).
  (* Arch application point: TV0*inv(w*budget) > 0, strict premises
     routed through the multiplication compatibility. *)
  assert (Hx : lt zero (mult TV0
                   (inv_pos (mult (minus one kappa) budget) Hwb)))
    by exact (mult_positive TV0
                (inv_pos (mult (minus one kappa) budget) Hwb) Ha Hinvwbp).
  destruct (Harch (mult TV0 (inv_pos (mult (minus one kappa) budget) Hwb))
                  Hx) as [N HN].
  exact (ums_pow_tail kappa TV0 budget (minus one kappa) N Hwb
           hwp hwlt Heqk (lt_le_iff zero TV0 (inl Ha))
           (lt_le_iff zero budget (inl Hbudget)) HN).
Defined.

(* piece 6: the le version, same premises with the conclusion cooled
   from lt to le. *)
Lemma ums_k_select_le :
  forall (kappa TV0 budget : R),
    lt zero kappa -> lt kappa one ->
    le zero TV0 -> lt zero budget ->
    (forall x : R, le zero x ->
       sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => le (mult (r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch.
  destruct (ums_k_select kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch)
    as [k Hk].
  exists k.
  exact (lt_le_iff (mult (r_pow kappa k) TV0) budget (inl Hk)).
Defined.

End UMixSelect.

(* evidence section: the closing Print Assumptions audits, each
   expected Closed. *)
Print Assumptions UpReqUMixSelect.ums_scale_S_pos.
Print Assumptions UpReqUMixSelect.ums_boost_pos.
Print Assumptions UpReqUMixSelect.ums_mult_one_l.
Print Assumptions UpReqUMixSelect.ums_mult_opp_r.
Print Assumptions UpReqUMixSelect.ums_mult_swap.
Print Assumptions UpReqUMixSelect.ums_le_plus_r.
Print Assumptions UpReqUMixSelect.ums_minus_plus_cancel.
Print Assumptions UpReqUMixSelect.ums_minus_le.
Print Assumptions UpReqUMixSelect.ums_omd_lt_one.
Print Assumptions UpReqUMixSelect.ums_omd_id.
Print Assumptions UpReqUMixSelect.ums_cancel_to_minus.
Print Assumptions UpReqUMixSelect.ums_ring_sc.
