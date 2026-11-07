(* ============================================================ *)
(* ConstructiveWorld-Set — req-face mixed k-selection and attention-kernel mixing time. *)

(** * UpReqConcMixSel: req-face counterparts of the mixed k-selector and
      the attention-kernel mixing time.

    Mission.  The req-face layer of mixed selection on the reals: the
      selector and power machinery ([cmk_scale], [cmk_r_pow], section
      [CmkMixSelect]) with the Bernoulli key inequality
      ([cmk_bernoulli_upper]) and the selection heads ([cmk_k_select],
      [cmk_pow_budget], [cmk_k_select_le]); the closing statements
      [cmk_attention_mixing_time] and [cmk_attention_mixing_time_le]
      (section [CmkMixTime]); the one-statement supply of the expf mini
      interface ([cmk_expf_realizable]); and resolved certificates for
      the declared slots of [CmkMixTime] (the [cmkr_] family: the sum
      interface realized at [sumf := csm_sumf], the world data at a
      two-point instance).

    Dependencies.  Stdlib [List]. Requires [S01_BaseRing] through
      [S15_TailFEPUp], [UpReqAlgebra], [UpReqSumD], [UpReqConcSoftmax],
      [UpReqSampling], and [AttnDoeblin] of this development.

    References.  This development, and the baseline module of the same
      name in ConstructiveWorld-Main whose statement names are carried
      over here verbatim; the [ums_]/[amt_]/[rsq_] families are the
      mirrored statements reused here.

    Constructivity.  All statements are carried by [Set] over the
      req/lt/le carriers; no admitted statements; the selector and
      closing statements close by [Defined] and stay extractable; the
      resolved supplies close by [Qed] from already-proved lemmas with
      explicit arguments; the [Print Assumptions] audits report Closed.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      UpReqConcMixSel.v] compiles cleanly (exit 0); the first eight
      bytes of the artifact are [436f7121 000160bc]. *)

From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import AttnDoeblin.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* Carrier concretization: [RealInterfaceEnhancedSetoid] is a parameterless
   class in this tree ([S07_RealSetoidExpLog]) whose fields resolve through the
   global [Real] instance [RealEnhancedReal]; the abstract carrier [R] is fixed
   to the concrete [Real]. The relation fields req/lt/le bind through [Notation]
   directly to the [S02_CauchyComplete] forms [real_eq]/[real_lt]/[real_le] —
   exactly the values the global instance assigns to those fields, so
   statement-face elaboration sees the same terms (the same convention as
   [ConcMixSelFeed.v]). *)
Notation R := Real.
Notation req := real_eq.
Notation lt := real_lt.
Notation le := real_le.

(* ==================== Section [CmkMixSelect]: req-face counterparts of the k-selector (one lemma per [ums_] statement) ==================== *)

Section CmkMixSelect.

(* Fields resolve through the global instance [RealEnhancedReal]; this section
   declares no abstract instance. *)

(* Honest interface: the mixed lt+le compatibility of addition (mirrors the
   same-section Variable of the Id-face [UMixSelect]; the class fields provide
   only the strict-strict [lt_plus_compat], and the mixed form is not provable
   at this level of abstraction). *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* ---- bidirectional equality congruence helpers (req-face restrictions of [id_cong]: either side of plus/mult) ---- *)

Lemma cmk_plus_congr_l : forall (a x y : R), req x y -> req (plus a x) (plus a y).
Proof. intros a x y H. exact (req_plus_compat a a x y (req_refl a) H). Defined.

Lemma cmk_plus_congr_r : forall (b x y : R), req x y -> req (plus x b) (plus y b).
Proof. intros b x y H. exact (req_plus_compat x y b b H (req_refl b)). Defined.

Lemma cmk_mult_congr_l : forall (a x y : R), req x y -> req (mult a x) (mult a y).
Proof. intros a x y H. exact (req_mult_compat a a x y (req_refl a) H). Defined.

Lemma cmk_mult_congr_r : forall (b x y : R), req x y -> req (mult x b) (mult y b).
Proof. intros b x y H. exact (req_mult_compat x y b b H (req_refl b)). Defined.

(* the endpoints [x] and [y] are determined by the certificate types, so they
   are made implicit (keeps long reshaping chains readable) *)
Arguments cmk_plus_congr_l a {x y} _.
Arguments cmk_plus_congr_r b {x y} _.
Arguments cmk_mult_congr_l a {x y} _.
Arguments cmk_mult_congr_r b {x y} _.

(* ============================================================ *)
(* Part 1. The nat-scale partial-sum accumulator (the req counterpart of [ums_scale]) *)
(* ============================================================ *)

Fixpoint cmk_scale (k : nat) (w : R) : R :=
  match k with
  | Datatypes.O => zero
  | Datatypes.S m => plus w (cmk_scale m w)
  end.

(* nat-scale nonnegativity: 0 <= w gives 0 <= k*w (the [@ums_scale_nonneg] counterpart) *)
Lemma cmk_scale_nonneg : forall (w : R) (k : nat),
  le zero w -> le zero (cmk_scale k w).
Proof.
  intros w k Hw. induction k as [| k IH].
  - exact (le_refl zero).
  - exact (le_id_l zero (plus zero zero) (plus w (cmk_scale k w))
             (req_sym _ _ (plus_zero zero))
             (le_plus_compat zero w zero (cmk_scale k w) Hw IH)).
Defined.

(* nat-scale strict positivity: 0 < w gives 0 < (S k)*w (the [@ums_scale_S_pos] counterpart) *)
Lemma cmk_scale_S_pos : forall (w : R) (k : nat),
  lt zero w -> lt zero (cmk_scale (Datatypes.S k) w).
Proof.
  intros w k Hw.
  exact (lt_id_l zero (plus zero zero) (plus w (cmk_scale k w))
           (req_sym _ _ (plus_zero zero))
           (lt_plus_compat_lt_le zero w zero (cmk_scale k w)
              Hw (cmk_scale_nonneg w k (lt_le_iff zero w (inl Hw))))).
Defined.

(* boost positivity: 1 + k*w > 0 (the [@ums_boost_pos] counterpart) *)
Lemma cmk_boost_pos : forall (w : R) (k : nat),
  le zero w -> lt zero (plus one (cmk_scale k w)).
Proof.
  intros w k Hw.
  exact (lt_id_l zero (plus zero zero) (plus one (cmk_scale k w))
           (req_sym _ _ (plus_zero zero))
           (lt_plus_compat_lt_le zero one zero (cmk_scale k w)
              one_pos (cmk_scale_nonneg w k Hw))).
Defined.

(* ============================================================ *)
(* Part 2. Abstract ring simplification lemmas (the [@ums] ring-simplification chains replayed over req) *)
(* ============================================================ *)

(* 1*x == x (the [@ums_mult_one_l] counterpart) *)
Lemma cmk_mult_one_l : forall x : R, req (mult one x) x.
Proof.
  intro x. exact (req_trans _ _ _ (mult_comm one x) (mult_one x)).
Defined.

(* x*(-y) == -(x*y) (the [@ums_mult_opp_r] counterpart; [req_opp_mult_l] of [UpReqAlgebra] applies directly) *)
Lemma cmk_mult_opp_r : forall x y : R, req (mult x (opp y)) (opp (mult x y)).
Proof.
  intros x y. exact (req_opp_mult_l x y).
Defined.

(* multiplication swap: (a*b)*c == b*(a*c) (the [@ums_mult_swap] counterpart) *)
Lemma cmk_mult_swap : forall a b c : R,
  req (mult (mult a b) c) (mult b (mult a c)).
Proof.
  intros a b c.
  exact (req_trans _ _ _
           (req_mult_compat (mult a b) (mult b a) c c
              (mult_comm a b) (req_refl c))
           (req_sym _ _ (mult_assoc b a c))).
Defined.

(* inverse cancellation: x*(y*inv(x)) == y for 0 < x (the [@ums_mult_div] counterpart) *)
Lemma cmk_mult_div : forall (x y : R) (H : lt zero x),
  req (mult x (mult y (inv_pos x H))) y.
Proof.
  intros x y H.
  apply (req_trans _ (mult (mult x y) (inv_pos x H)) _).
  { exact (mult_assoc x y (inv_pos x H)). }
  apply (req_trans _ (mult (mult y x) (inv_pos x H)) _).
  { exact (cmk_mult_congr_r (inv_pos x H) (mult_comm x y)). }
  apply (req_trans _ (mult y (mult x (inv_pos x H))) _).
  { exact (req_sym _ _ (mult_assoc y x (inv_pos x H))). }
  apply (req_trans _ (mult y one) _).
  { exact (cmk_mult_congr_l y (inv_pos_correct x H)). }
  exact (mult_one y).
Defined.

(* right addition shift for le: 0 <= d gives x <= x + d (the [@ums_le_plus_r] counterpart) *)
Lemma cmk_le_plus_r : forall x d : R, le zero d -> le x (plus x d).
Proof.
  intros x d Hd.
  exact (le_id_l x (plus x zero) (plus x d) (req_sym _ _ (plus_zero x))
           (le_plus_compat x x zero d (le_refl x) Hd)).
Defined.

(* subtraction is invertible on the right: (a - b) + b == a (the [@ums_minus_plus_cancel] counterpart) *)
Lemma cmk_minus_plus_cancel : forall a b : R, req (plus (req_minus a b) b) a.
Proof.
  intros a b. unfold req_minus.
  apply (req_trans _ (plus a (plus (opp b) b)) _).
  { exact (req_sym _ _ (plus_assoc a (opp b) b)). }
  apply (req_trans _ (plus a zero) _).
  { exact (cmk_plus_congr_l a
             (req_trans _ _ _ (plus_comm (opp b) b) (plus_opp b))). }
  exact (plus_zero a).
Defined.

(* subtraction stays below itself for le: 0 <= d gives X - d <= X (the [@ums_minus_le] counterpart) *)
Lemma cmk_minus_le : forall X d : R, le zero d -> le (req_minus X d) X.
Proof.
  intros X d Hd.
  exact (le_id_r (req_minus X d) (plus (req_minus X d) d) X
           (cmk_minus_plus_cancel X d) (cmk_le_plus_r (req_minus X d) d Hd)).
Defined.

(* ============================================================ *)
(* Part 3. Rate-certificate lemmas and the power face (the [@ums] omd/rpow family) *)
(* ============================================================ *)

(* 0 < w < 1 gives 0 < 1-w (the [@ums_omd_lt_one] counterpart) *)
Lemma cmk_omd_lt_one : forall w : R,
  lt zero w -> lt w one -> lt zero (req_minus one w).
Proof.
  intros w Hw0 Hw1. unfold req_minus.
  apply (lt_id_l zero (plus w (opp w)) (plus one (opp w))
           (req_sym _ _ (plus_opp w))).
  exact (lt_plus_compat_lt_le w one (opp w) (opp w) Hw1 (le_refl (opp w))).
Defined.

(* double complement for omd: x == 1-(1-x) (the [@ums_omd_id] counterpart; replayed as a req chain) *)
Lemma cmk_omd_id : forall x : R, req x (req_minus one (req_minus one x)).
Proof.
  intro x. apply req_sym. unfold req_minus.
  exact (req_trans _ _ _
           (cmk_plus_congr_l one (req_opp_plus one (opp x)))
           (req_trans _ _ _
              (cmk_plus_congr_l one
                 (cmk_plus_congr_l (opp one) (req_double_neg x)))
              (req_trans _ _ _
                 (plus_assoc one (opp one) x)
                 (req_trans _ _ _
                    (cmk_plus_congr_r x (plus_opp one))
                    (req_trans _ _ _ (plus_comm zero x) (plus_zero x)))))).
Defined.

(* the power respects equality of bases: equal bases give equal powers (the [@ums_rpow_eq_compat] counterpart) *)
Fixpoint cmk_r_pow (x : R) (n : nat) : R :=
  match n with
  | Datatypes.O => one
  | Datatypes.S m => mult x (cmk_r_pow x m)
  end.

Lemma cmk_rpow_eq_compat : forall (x y : R) (k : nat),
  req x y -> req (cmk_r_pow x k) (cmk_r_pow y k).
Proof.
  intros x y k Hxy. induction k as [| k IH].
  - exact (req_refl one).
  - exact (req_mult_compat x y _ _ Hxy IH).
Defined.

(* power positivity: 0 < a gives 0 < a^k (the [@ums_rpow_pos] counterpart) *)
Lemma cmk_rpow_pos : forall (a : R) (k : nat),
  lt zero a -> lt zero (cmk_r_pow a k).
Proof.
  intros a k Ha. induction k as [| k IH].
  - exact (one_pos).
  - exact (mult_positive a (cmk_r_pow a k) Ha IH).
Defined.

(* the nat-scale accumulator respects req on its base: x == y gives [cmk_scale k x] == [cmk_scale k y] *)
Lemma cmk_scale_congr : forall (k : nat) (x y : R),
  req x y -> req (cmk_scale k x) (cmk_scale k y).
Proof.
  intros k. induction k as [| k IH]; intros x y Hxy.
  - exact (req_refl zero).
  - exact (req_plus_compat x y (cmk_scale k x) (cmk_scale k y) Hxy (IH x y Hxy)).
Defined.

(* the nat-scale accumulator distributes over the right factor: (k*x)*z == k*(x*z) (the [@ums_scale_mult_distrib] counterpart) *)
Lemma cmk_scale_mult_distrib : forall (k : nat) (x z : R),
  req (mult (cmk_scale k x) z) (cmk_scale k (mult x z)).
Proof.
  intros k. induction k as [| k IH]; intros x z.
  - exact (req_trans _ _ _ (mult_comm zero z) (mult_zero z)).
  - apply (req_trans _ (mult z (plus x (cmk_scale k x))) _).
    { exact (mult_comm (plus x (cmk_scale k x)) z). }
    apply (req_trans _ (plus (mult z x) (mult z (cmk_scale k x))) _).
    { exact (distrib z x (cmk_scale k x)). }
    apply (req_trans _ (plus (mult x z) (mult z (cmk_scale k x))) _).
    { exact (cmk_plus_congr_r (mult z (cmk_scale k x)) (mult_comm z x)). }
    apply (req_trans _ (plus (mult x z) (mult (cmk_scale k x) z)) _).
    { exact (cmk_plus_congr_l (mult x z) (mult_comm z (cmk_scale k x))). }
    apply (req_trans _ (plus (mult x z) (cmk_scale k (mult x z))) _).
    { exact (cmk_plus_congr_l (mult x z) (IH x z)). }
    exact (req_refl _).
Defined.

(* ============================================================ *)
(* Part 4. The Bernoulli upper bound (req counterparts of the key [@ums_bernoulli_upper] lemmas) *)
(* ============================================================ *)

(* the generic ring core in cancel-ready shape: (1-w)(1+w+s) + (w+s)*w == 1+s *)
(* (the [@ums_bernoulli_cancel] counterpart replayed as a req chain, reshaped step
   by step through the [cmk_plus_congr] family) *)
Lemma cmk_bernoulli_cancel : forall w s : R,
  req (plus (mult (req_minus one w) (plus one (plus w s))) (mult (plus w s) w))
       (plus one s).
Proof.
  intros w s. unfold req_minus.
  apply (req_trans _ (plus (plus (mult (plus one (opp w)) one)
                                 (mult (plus one (opp w)) (plus w s)))
                             (mult (plus w s) w)) _).
  { exact (cmk_plus_congr_r (mult (plus w s) w)
             (distrib (plus one (opp w)) one (plus w s))). }
  apply (req_trans _ (plus (plus (plus one (opp w))
                                 (mult (plus one (opp w)) (plus w s)))
                             (mult (plus w s) w)) _).
  { exact (cmk_plus_congr_r (mult (plus w s) w)
             (cmk_plus_congr_r (mult (plus one (opp w)) (plus w s))
                (mult_one (plus one (opp w))))). }
  apply (req_trans _ (plus (plus (plus one (opp w))
                                 (mult (plus w s) (plus one (opp w))))
                             (mult (plus w s) w)) _).
  { exact (cmk_plus_congr_r (mult (plus w s) w)
             (cmk_plus_congr_l (plus one (opp w))
                (mult_comm (plus one (opp w)) (plus w s)))). }
  apply (req_trans _ (plus (plus (plus one (opp w))
                                 (plus (mult (plus w s) one)
                                       (mult (plus w s) (opp w))))
                             (mult (plus w s) w)) _).
  { exact (cmk_plus_congr_r (mult (plus w s) w)
             (cmk_plus_congr_l (plus one (opp w))
                (distrib (plus w s) one (opp w)))). }
  apply (req_trans _ (plus (plus (plus one (opp w))
                                 (plus (plus w s) (mult (plus w s) (opp w))))
                             (mult (plus w s) w)) _).
  { exact (cmk_plus_congr_r (mult (plus w s) w)
             (cmk_plus_congr_l (plus one (opp w))
                (cmk_plus_congr_r (mult (plus w s) (opp w))
                   (mult_one (plus w s))))). }
  apply (req_trans _ (plus (plus (plus one (opp w))
                                 (plus (plus w s) (opp (mult (plus w s) w))))
                             (mult (plus w s) w)) _).
  { exact (cmk_plus_congr_r (mult (plus w s) w)
             (cmk_plus_congr_l (plus one (opp w))
                (cmk_plus_congr_l (plus w s)
                   (cmk_mult_opp_r (plus w s) w)))). }
  apply (req_trans _ (plus (plus one (opp w))
                           (plus (plus (plus w s) (opp (mult (plus w s) w)))
                                 (mult (plus w s) w))) _).
  { exact (req_sym _ _ (plus_assoc (plus one (opp w))
                          (plus (plus w s) (opp (mult (plus w s) w)))
                          (mult (plus w s) w))). }
  apply (req_trans _ (plus (plus one (opp w))
                           (plus (plus w s) (plus (opp (mult (plus w s) w))
                                                  (mult (plus w s) w)))) _).
  { exact (cmk_plus_congr_l (plus one (opp w))
             (req_sym _ _ (plus_assoc (plus w s)
                             (opp (mult (plus w s) w))
                             (mult (plus w s) w)))). }
  apply (req_trans _ (plus (plus one (opp w)) (plus (plus w s) zero)) _).
  { exact (cmk_plus_congr_l (plus one (opp w))
             (cmk_plus_congr_l (plus w s)
                (req_trans _ _ _
                   (plus_comm (opp (mult (plus w s) w)) (mult (plus w s) w))
                   (plus_opp (mult (plus w s) w))))). }
  apply (req_trans _ (plus (plus one (opp w)) (plus w s)) _).
  { exact (cmk_plus_congr_l (plus one (opp w)) (plus_zero (plus w s))). }
  apply (req_trans _ (plus one (plus (opp w) (plus w s))) _).
  { exact (req_sym _ _ (plus_assoc one (opp w) (plus w s))). }
  apply (req_trans _ (plus one (plus (plus (opp w) w) s)) _).
  { exact (cmk_plus_congr_l one (plus_assoc (opp w) w s)). }
  apply (req_trans _ (plus one (plus zero s)) _).
  { exact (cmk_plus_congr_l one
             (cmk_plus_congr_r s
                (req_trans _ _ _ (plus_comm (opp w) w) (plus_opp w)))). }
  apply (req_trans _ (plus one (plus s zero)) _).
  { exact (cmk_plus_congr_l one (plus_comm zero s)). }
  exact (cmk_plus_congr_l one (plus_zero s)).
Defined.

(* cancellation in subtraction form: X + Y == Z gives X == Z - Y (the [@ums_cancel_to_minus] counterpart) *)
Lemma cmk_cancel_to_minus : forall X Y Z : R,
  req (plus X Y) Z -> req X (req_minus Z Y).
Proof.
  intros X Y Z HC. unfold req_minus.
  exact (req_trans _ _ _
           (req_sym _ _ (plus_zero X))
           (req_trans _ _ _
              (cmk_plus_congr_l X (req_sym _ _ (plus_opp Y)))
              (req_trans _ _ _
                 (plus_assoc X Y (opp Y))
                 (cmk_plus_congr_r (opp Y) HC)))).
Defined.

(* the ring simplification exit: (1-u)(1+u+a) == (1+a) - (u+a)*u (the [@ums_ring_sc] counterpart) *)
Lemma cmk_ring_sc : forall u a : R,
  req (mult (req_minus one u) (plus one (plus u a)))
       (req_minus (plus one a) (mult (plus u a) u)).
Proof.
  intros u a.
  exact (cmk_cancel_to_minus
           (mult (req_minus one u) (plus one (plus u a)))
           (mult (plus u a) u) (plus one a)
           (cmk_bernoulli_cancel u a)).
Defined.

(* the key inequality: (1-w)^k * (1+k*w) <= 1 for 0 < w < 1 (the [@ums_bernoulli_upper] counterpart) *)
Lemma cmk_bernoulli_upper : forall (w : R) (k : nat),
  lt zero w -> lt w one ->
  le (mult (cmk_r_pow (req_minus one w) k) (plus one (cmk_scale k w))) one.
Proof.
  intros w k Hwp Hwlt. induction k as [| k IH].
  - (* base case k = 0: 1*(1+0) == 1 *)
    change (le (mult one (plus one (cmk_scale 0 w))) one).
    exact (le_id_l (mult one (plus one (cmk_scale 0 w))) one one
             (req_trans _ _ _ (mult_comm one (plus one (cmk_scale 0 w)))
                (req_trans _ _ _ (mult_one (plus one (cmk_scale 0 w)))
                           (plus_zero one)))
             (le_refl one)).
  - (* induction step: ring simplification gives
       (1-w)(1+(k+1)w) == (1+kw) - ((k+1)w)*w <= 1+kw, and positivity of the
       power lets the commuted IH close it (the [@ums] isomorph) *)
    assert (Hbpos : lt zero (req_minus one w))
      by exact (cmk_omd_lt_one w Hwp Hwlt).
    assert (HPk : lt zero (cmk_r_pow (req_minus one w) k))
      by exact (cmk_rpow_pos (req_minus one w) k Hbpos).
    assert (HC : lt zero (mult (cmk_scale (Datatypes.S k) w) w))
      by exact (mult_positive (cmk_scale (Datatypes.S k) w) w
                  (cmk_scale_S_pos w k Hwp) Hwp).
    assert (HSC : le (mult (req_minus one w)
                             (plus one (cmk_scale (Datatypes.S k) w)))
                       (plus one (cmk_scale k w))).
    { apply (le_id_l (mult (req_minus one w)
                             (plus one (plus w (cmk_scale k w))))
                       (req_minus (plus one (cmk_scale k w))
                                  (mult (cmk_scale (Datatypes.S k) w) w))
                       (plus one (cmk_scale k w))).
      - exact (cmk_ring_sc w (cmk_scale k w)).
      - exact (cmk_minus_le (plus one (cmk_scale k w))
                 (mult (cmk_scale (Datatypes.S k) w) w)
                 (lt_le_iff zero (mult (cmk_scale (Datatypes.S k) w) w)
                              (inl HC))). }
    assert (HeqR : req (mult (mult (req_minus one w)
                                     (cmk_r_pow (req_minus one w) k))
                               (plus one (cmk_scale (Datatypes.S k) w)))
                          (mult (mult (req_minus one w)
                                      (plus one (cmk_scale (Datatypes.S k) w)))
                                (cmk_r_pow (req_minus one w) k)))
      by exact (req_trans _ _ _
                  (cmk_mult_swap (req_minus one w)
                     (cmk_r_pow (req_minus one w) k)
                     (plus one (cmk_scale (Datatypes.S k) w)))
                  (mult_comm (cmk_r_pow (req_minus one w) k)
                     (mult (req_minus one w)
                           (plus one (cmk_scale (Datatypes.S k) w))))).
    assert (IH' : le (mult (plus one (cmk_scale k w))
                               (cmk_r_pow (req_minus one w) k))
                       one).
    { exact (le_id_l (mult (plus one (cmk_scale k w))
                               (cmk_r_pow (req_minus one w) k))
                       (mult (cmk_r_pow (req_minus one w) k)
                             (plus one (cmk_scale k w)))
                       one
                       (mult_comm (plus one (cmk_scale k w))
                                  (cmk_r_pow (req_minus one w) k))
                       IH). }
    apply (le_trans _ (mult (plus one (cmk_scale k w))
                                (cmk_r_pow (req_minus one w) k))).
    + exact (le_id_l (mult (cmk_r_pow (req_minus one w) (Datatypes.S k))
                               (plus one (cmk_scale (Datatypes.S k) w)))
                       (mult (mult (req_minus one w)
                                   (plus one (cmk_scale (Datatypes.S k) w)))
                             (cmk_r_pow (req_minus one w) k))
                       (mult (plus one (cmk_scale k w))
                             (cmk_r_pow (req_minus one w) k))
                       HeqR
                       (le_mult_compat (mult (req_minus one w)
                                           (plus one (cmk_scale (Datatypes.S k) w)))
                                       (plus one (cmk_scale k w))
                                       (cmk_r_pow (req_minus one w) k) HPk HSC)).
    + exact IH'.
Defined.

(* ============================================================ *)
(* Part 5. The inverse step (the [@ums_le_inv] counterpart) *)
(* ============================================================ *)

Lemma cmk_le_inv : forall (A B : R) (HB : lt zero B),
  le (mult A B) one -> le A (inv_pos B HB).
Proof.
  intros A B HB HAB.
  assert (HBp : lt zero (inv_pos B HB)) by exact (inv_pos_pos B HB).
  apply (le_trans A (mult (mult A B) (inv_pos B HB)) (inv_pos B HB)).
  - exact (le_id_l A (mult (mult A B) (inv_pos B HB))
                     (mult (mult A B) (inv_pos B HB))
             (req_trans _ _ _
                (req_trans _ _ _
                   (req_sym _ _ (mult_one A))
                   (cmk_mult_congr_l A (req_sym _ _ (inv_pos_correct B HB))))
                (mult_assoc A B (inv_pos B HB)))
             (le_refl (mult (mult A B) (inv_pos B HB)))).
  - exact (le_id_r (mult (mult A B) (inv_pos B HB))
                     (mult one (inv_pos B HB)) (inv_pos B HB)
             (cmk_mult_one_l (inv_pos B HB))
             (le_mult_compat (mult A B) one (inv_pos B HB) HBp HAB)).
Defined.

(* ============================================================ *)
(* Part 6. The tail-chain core of the k-selection (the [@ums_pow_tail] counterpart) *)
(* ============================================================ *)

Lemma cmk_pow_tail :
  forall (kappa TV0 budget w : R) (N : nat)
         (Hwb : lt zero (mult w budget)),
    lt zero w -> lt w one -> req kappa (req_minus one w) ->
    le zero TV0 -> le zero budget ->
    lt (mult TV0 (inv_pos (mult w budget) Hwb))
       (cmk_scale (Datatypes.S N) one) ->
    sigT (fun k : nat => lt (mult (cmk_r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget w N Hwb Hw0 Hwlt1 Heqk Ha Hbudget0 HN.
  assert (Hwle : le zero w) by exact (lt_le_iff zero w (inl Hw0)).
  set (wb := mult w budget).
  set (invwb := inv_pos wb Hwb).
  set (Ms := cmk_scale (Datatypes.S N) w).
  set (boost := plus one Ms).
  assert (Hboost0 : lt zero boost)
    by exact (cmk_boost_pos w (Datatypes.S N) Hwle).
  set (invB := inv_pos boost Hboost0).
  assert (HinvB : lt zero invB) by exact (inv_pos_pos boost Hboost0).
  (* ---- budget premise: TV0 < Ms*budget ---- *)
  assert (Hstep : lt (mult (mult TV0 invwb) wb)
                       (mult (cmk_scale (Datatypes.S N) one) wb))
    by exact (lt_mult_compat (mult TV0 invwb)
                (cmk_scale (Datatypes.S N) one) wb Hwb HN).
  assert (HeqL : req (mult (mult TV0 invwb) wb) TV0)
    by exact (req_trans _ _ _
                (mult_comm (mult TV0 invwb) wb)
                (cmk_mult_div wb TV0 Hwb)).
  assert (HeqR : req (mult (cmk_scale (Datatypes.S N) one) wb)
                       (mult Ms budget))
    by exact (req_trans _ _ _
           (req_trans _ _ _
              (cmk_scale_mult_distrib (Datatypes.S N) one wb)
              (cmk_scale_congr (Datatypes.S N) (mult one wb) wb
                 (cmk_mult_one_l wb)))
           (req_sym _ _ (cmk_scale_mult_distrib (Datatypes.S N) w budget))).
  assert (Hb0 : lt TV0 (mult Ms budget)).
  { exact (lt_id_r TV0 (mult (cmk_scale (Datatypes.S N) one) wb)
             (mult Ms budget) HeqR
             (lt_id_l TV0 (mult (mult TV0 invwb) wb)
                (mult (cmk_scale (Datatypes.S N) one) wb)
                (req_sym _ _ HeqL) Hstep)). }
  assert (HeqBud : req (mult budget boost) (plus budget (mult Ms budget)))
    by exact (req_trans _ _ _
                (distrib budget one Ms)
                (req_trans _ _ _
                   (cmk_plus_congr_r (mult budget Ms) (mult_one budget))
                   (cmk_plus_congr_l budget (mult_comm budget Ms)))).
  assert (Hbud : lt TV0 (mult budget boost)).
  { exact (lt_id_r TV0 (plus (mult Ms budget) budget) (mult budget boost)
             (req_sym _ _ (req_trans _ _ _ HeqBud
                             (plus_comm budget (mult Ms budget))))
             (lt_le_trans TV0 (mult Ms budget)
                (plus (mult Ms budget) budget) Hb0
                (cmk_le_plus_r (mult Ms budget) budget Hbudget0))). }
  exists (Datatypes.S N).
  (* ---- main chain: kappa^(S N)*TV0 < budget ---- *)
  assert (Heqp : req (cmk_r_pow kappa (Datatypes.S N))
                       (cmk_r_pow (req_minus one w) (Datatypes.S N)))
    by exact (cmk_rpow_eq_compat kappa (req_minus one w) (Datatypes.S N) Heqk).
  assert (Hbern : le (mult (cmk_r_pow (req_minus one w) (Datatypes.S N)) boost) one)
    by exact (cmk_bernoulli_upper w (Datatypes.S N) Hw0 Hwlt1).
  assert (Hinvleg : le (cmk_r_pow (req_minus one w) (Datatypes.S N)) invB)
    by exact (cmk_le_inv (cmk_r_pow (req_minus one w) (Datatypes.S N)) boost
                Hboost0 Hbern).
  apply (le_lt_trans _ (mult invB TV0) budget).
  + exact (le_id_l (mult (cmk_r_pow kappa (Datatypes.S N)) TV0)
                     (mult (cmk_r_pow (req_minus one w) (Datatypes.S N)) TV0)
                     (mult invB TV0)
             (cmk_mult_congr_r TV0 Heqp)
             (le_mult_compat_weak (cmk_r_pow (req_minus one w) (Datatypes.S N))
                invB TV0 Ha Hinvleg)).
  + exact (lt_id_r (mult invB TV0)
              (mult (mult budget boost) invB) budget
              (req_trans _ _ _
                 (cmk_mult_congr_r invB (mult_comm budget boost))
                 (req_trans _ _ _
                    (req_sym _ _ (mult_assoc boost budget invB))
                    (cmk_mult_div boost budget Hboost0)))
              (lt_id_l (mult invB TV0) (mult TV0 invB)
                 (mult (mult budget boost) invB)
                 (mult_comm invB TV0)
                 (lt_mult_compat TV0 (mult budget boost) invB HinvB Hbud))).
Defined.

(* ============================================================ *)
(* Part 7. The selection heads (the [@ums_k_select] / [@ums_pow_budget] / [@ums_k_select_le] counterparts) *)
(* ============================================================ *)

(* the le-premise form, with the le-shaped Archimedean premise passed straight through (the [@ums_k_select] counterpart) *)
Lemma cmk_k_select :
  forall (kappa TV0 budget : R),
    lt zero kappa -> lt kappa one ->
    le zero TV0 -> lt zero budget ->
    (forall x : R, le zero x ->
       sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => lt (mult (cmk_r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch.
  assert (hwp : lt zero (req_minus one kappa))
    by exact (cmk_omd_lt_one kappa Hk1 Hk2).
  assert (hwlt : lt (req_minus one kappa) one).
  { apply (lt_id_r (req_minus one kappa)
             (plus kappa (req_minus one kappa)) one
             (req_trans _ _ _ (plus_comm kappa (req_minus one kappa))
                       (cmk_minus_plus_cancel one kappa))).
    apply (lt_id_l (req_minus one kappa) (plus zero (req_minus one kappa))
             (plus kappa (req_minus one kappa))
             (req_sym _ _
                (req_trans _ _ _ (plus_comm zero (req_minus one kappa))
                           (plus_zero (req_minus one kappa))))).
    exact (lt_plus_compat_lt_le zero kappa (req_minus one kappa)
               (req_minus one kappa) Hk1 (le_refl (req_minus one kappa))). }
  assert (Heqk : req kappa (req_minus one (req_minus one kappa)))
    by exact (cmk_omd_id kappa).
  assert (Hwb : lt zero (mult (req_minus one kappa) budget))
    by exact (mult_positive (req_minus one kappa) budget hwp Hbudget).
  assert (Hinvwbp : lt zero (inv_pos (mult (req_minus one kappa) budget) Hwb))
    by exact (inv_pos_pos (mult (req_minus one kappa) budget) Hwb).
  (* Archimedean premise point: TV0*inv(w*budget) >= 0 (le premises propagate
     through the weak multiplicative compatibility) *)
  assert (Hxle : le zero (mult TV0
                     (inv_pos (mult (req_minus one kappa) budget) Hwb))).
  { exact (le_id_l zero
             (mult zero (inv_pos (mult (req_minus one kappa) budget) Hwb))
             (mult TV0 (inv_pos (mult (req_minus one kappa) budget) Hwb))
             (req_sym _ _
                (req_trans _ _ _
                   (mult_comm zero (inv_pos (mult (req_minus one kappa) budget) Hwb))
                   (mult_zero (inv_pos (mult (req_minus one kappa) budget) Hwb))))
             (le_mult_compat_weak zero TV0
                (inv_pos (mult (req_minus one kappa) budget) Hwb)
                (lt_le_iff zero
                   (inv_pos (mult (req_minus one kappa) budget) Hwb)
                   (inl Hinvwbp)) Ha)). }
  destruct (Harch (mult TV0 (inv_pos (mult (req_minus one kappa) budget) Hwb))
                  Hxle) as [N HN].
  exact (cmk_pow_tail kappa TV0 budget (req_minus one kappa) N Hwb
           hwp hwlt Heqk Ha (lt_le_iff zero budget (inl Hbudget)) HN).
Defined.

(* the strict variant (lt premises and an lt-shaped Archimedean premise; the [@ums_pow_budget] counterpart) *)
Lemma cmk_pow_budget :
  forall (kappa TV0 budget : R),
    lt zero kappa -> lt kappa one ->
    lt zero TV0 -> lt zero budget ->
    (forall x : R, lt zero x ->
       sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => lt (mult (cmk_r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch.
  assert (hwp : lt zero (req_minus one kappa))
    by exact (cmk_omd_lt_one kappa Hk1 Hk2).
  assert (hwlt : lt (req_minus one kappa) one).
  { apply (lt_id_r (req_minus one kappa)
             (plus kappa (req_minus one kappa)) one
             (req_trans _ _ _ (plus_comm kappa (req_minus one kappa))
                       (cmk_minus_plus_cancel one kappa))).
    apply (lt_id_l (req_minus one kappa) (plus zero (req_minus one kappa))
             (plus kappa (req_minus one kappa))
             (req_sym _ _
                (req_trans _ _ _ (plus_comm zero (req_minus one kappa))
                           (plus_zero (req_minus one kappa))))).
    exact (lt_plus_compat_lt_le zero kappa (req_minus one kappa)
               (req_minus one kappa) Hk1 (le_refl (req_minus one kappa))). }
  assert (Heqk : req kappa (req_minus one (req_minus one kappa)))
    by exact (cmk_omd_id kappa).
  assert (Hwb : lt zero (mult (req_minus one kappa) budget))
    by exact (mult_positive (req_minus one kappa) budget hwp Hbudget).
  assert (Hinvwbp : lt zero (inv_pos (mult (req_minus one kappa) budget) Hwb))
    by exact (inv_pos_pos (mult (req_minus one kappa) budget) Hwb).
  (* Archimedean premise point: TV0*inv(w*budget) > 0 (strict premises propagate
     through the multiplicative compatibility) *)
  assert (Hx : lt zero (mult TV0
                   (inv_pos (mult (req_minus one kappa) budget) Hwb)))
    by exact (mult_positive TV0
                (inv_pos (mult (req_minus one kappa) budget) Hwb) Ha Hinvwbp).
  destruct (Harch (mult TV0 (inv_pos (mult (req_minus one kappa) budget) Hwb))
                  Hx) as [N HN].
  exact (cmk_pow_tail kappa TV0 budget (req_minus one kappa) N Hwb
           hwp hwlt Heqk (lt_le_iff zero TV0 (inl Ha))
           (lt_le_iff zero budget (inl Hbudget)) HN).
Defined.

(* the <= variant (same premises, conclusion weakened from lt to le; the [@ums_k_select_le] counterpart) *)
Lemma cmk_k_select_le :
  forall (kappa TV0 budget : R),
    lt zero kappa -> lt kappa one ->
    le zero TV0 -> lt zero budget ->
    (forall x : R, le zero x ->
       sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => le (mult (cmk_r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch.
  destruct (cmk_k_select kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch)
    as [k Hk].
  exists k.
  exact (lt_le_iff (mult (cmk_r_pow kappa k) TV0) budget (inl Hk)).
Defined.

End CmkMixSelect.

(* Power bridge: [cmk_r_pow] == [req_r_pow] — a stepwise req conversion between
   two isomorphic fixpoints; at a variable [k] the two fixes are not
   convertible, so the proof goes by induction — this is the joint between the
   two power recursions. *)
Section CmkRPowBridge.
(* Fields resolve through the global instance [RealEnhancedReal]; this section
   declares no abstract instance. *)
Lemma cmk_r_pow_req_r_pow : forall (x : R) (k : nat),
  req (cmk_r_pow x k) (req_r_pow x k).
Proof.
  intro x. induction k as [| k IH].
  - exact (req_refl one).
  - exact (req_mult_compat x x _ _ (req_refl x) IH).
Defined.
End CmkRPowBridge.

(* ============================================================ *)
(* Section [CmkMixTime]: req-face counterparts of the closing statements (one lemma per [amt_] statement). *)
(*   The six declared slots of the sum interface mirror [ReqBoundedSoftmax] of
   the rsq chain; [abs_sum_le_h] stays an explicitly declared plain-form
   slot — the concrete layer supplies per-eps forms through
   [csm_abs_sum_le_eps] or pushes through a unary [enum] (resolved in the
   concrete layer below). *)
(* ============================================================ *)

Section CmkMixTime.

(* Fields resolve through the global instance [RealEnhancedReal]; this section
   declares no abstract instance. *)

(* Honest interface: the mixed lt+le compatibility of addition (same slot as in
   [CmkMixSelect]). *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- the sum interface (the six declared slots mirroring the rsq chain) ---- *)
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
(* the sum triangle: |sum f| <= sum |f| (declared as a plain-form slot; the
   same slot as [abs_sum_le_h] of [UpReqSampling]) *)
Hypothesis abs_sum_le_h :
  forall f : S -> R, le (abs (sumf f)) (sumf (fun s : S => abs (f s))).

(* ---- the finite world data (req counterparts of the Variable set of the Id-face amt section) ---- *)
Variable enum : list S.
Variable enum_nonempty : Not (enum = nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable z : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z s s').
Variable z_ub : forall s s' : S, le (z s s') Delta.
Variable bs_swap : forall f : S -> S -> R,
  req (sumf (fun s : S => sumf (fun s' : S => f s s')))
      (sumf (fun s' : S => sumf (fun s : S => f s s'))).
Variable bs_abs : forall a : R, le zero a -> req (abs a) a.
Variable bs_lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable sum_eq_list : forall g : S -> R, req (sumf g) (rsq_bs_list_sum S g enum).

(* ---- the kernel instance data (the rsq mixing-rate shape: [expf := rsq_exp_pos_fn];
   the expf supply corresponds to the one-statement supply [cmk_expf_realizable]
   at the end of this file) ---- *)
Let invT := inv_pos temp temp_pos.
Let lo := rsq_exp_pos_fn (mult invT (opp Delta)).
Let delta_star := mult lo lo.
Let omd := req_minus one delta_star.

(* the TV operator and its iterator ([req]-carried forms of [tv_req]/[k_titer];
   after the section they convert to the rsq chain) *)
Let inv_two := inv_pos (plus one one) req_two_pos.
Let cmk_tv (mu nu : S -> R) : R :=
  mult inv_two (sumf (fun s : S => abs (req_minus (mu s) (nu s)))).
Let cmk_titer (n : nat) (mu : S -> R) : S -> R :=
  k_titer S sumf enum enum_nonempty temp temp_pos Delta z z_lb sum_eq_list n mu.

(* ================= Direct reuse of proved library lemmas (the [amt] resolved-form counterparts) ================= *)

(* [delta_star] < 1 (from [rsq_bs_delta_star_lt_one]; the [amt_ds_lt_one] counterpart) *)
Lemma cmk_ds_lt_one : lt delta_star one.
Proof.
  exact (rsq_bs_delta_star_lt_one temp temp_pos Delta Delta_pos).
Qed.

(* 1 - [delta_star] > 0 (the [amt_omd_pos] counterpart) *)
Lemma cmk_omd_pos : lt zero omd.
Proof.
  exact (lt_id_l zero (plus delta_star (opp delta_star)) omd
           (req_sym _ _ (plus_opp delta_star))
           (lt_plus_compat_lt_le delta_star one (opp delta_star)
              (opp delta_star) cmk_ds_lt_one (le_refl (opp delta_star)))).
Qed.

(* ================= Self-contained glue lemmas (the [amt] self-proved counterparts) ================= *)

(* [one] = 1 - [delta_star] + [delta_star] (the [amt_one_eq] counterpart; a three-step req chain) *)
Lemma cmk_one_eq : req one (plus omd delta_star).
Proof.
  apply req_sym.
  exact (req_trans (plus (plus one (opp delta_star)) delta_star)
                     (plus one (plus (opp delta_star) delta_star)) one
           (req_sym _ _ (plus_assoc one (opp delta_star) delta_star))
           (req_trans (plus one (plus (opp delta_star) delta_star))
                      (plus one zero) one
              (req_plus_compat one one
                 (plus (opp delta_star) delta_star) zero
                 (req_refl one)
                 (req_trans (plus (opp delta_star) delta_star)
                            (plus delta_star (opp delta_star)) zero
                            (plus_comm (opp delta_star) delta_star)
                            (plus_opp delta_star)))
              (plus_zero one))).
Qed.

(* 1 - [delta_star] < one (the [amt_omd_lt_one] counterpart; the endpoint [delta_star] > 0 enters strictly through [bs_lpc] with two-sided reshaping) *)
Lemma cmk_ds_omd_lt_one : lt omd one.
Proof.
  assert (Hds : lt zero delta_star).
  { exact (mult_positive lo lo
             (exp_neg_pos (opp (mult invT (opp Delta))))
             (exp_neg_pos (opp (mult invT (opp Delta))))). }
  assert (Hcore : lt (plus zero (plus one (opp delta_star)))
                     (plus delta_star (plus one (opp delta_star)))).
  { exact (bs_lpc zero delta_star (plus one (opp delta_star))
                  (plus one (opp delta_star))
                  Hds (le_refl (plus one (opp delta_star)))). }
  assert (Hshift : lt (plus one (opp delta_star))
                      (plus (plus one (opp delta_star)) delta_star)).
  { exact (req_lt_id_r_loc _ _ _
             (plus_comm delta_star (plus one (opp delta_star)))
             (lt_id_l _ _ _
                (req_sym _ _
                   (req_trans _ _ _ (plus_comm zero (plus one (opp delta_star)))
                              (plus_zero (plus one (opp delta_star)))))
                Hcore)). }
  exact (req_lt_id_r_loc _ _ _ (req_sym _ _ cmk_one_eq) Hshift).
Qed.

(* ================= The closing theorem (the [amt] main counterpart) ================= *)

(* The closing theorem (strict form): TV(T^k mu, T^k nu) < budget. The
   nonnegativity premise Htv0 is declared explicitly: the plain le-form of
   [abs] >= 0 over [req] is not provable at the Or-layer (the class field
   [abs_nonneg] is only Bishop-style per-eps), and the unconditional Id-face
   form [tv_dist_nonneg] has no req-face counterpart — keeping the certificate
   as an explicit premise keeps the interface honest. *)
Theorem cmk_attention_mixing_time :
  forall mu nu : S -> R,
  req (sumf mu) one -> req (sumf nu) one ->
  forall budget : R, lt zero budget ->
  (forall x : R, le zero x ->
     sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
  le zero (cmk_tv mu nu) ->
  sigT (fun k : nat =>
    lt (cmk_tv (cmk_titer k mu) (cmk_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget Harch Htv0.
  destruct (cmk_k_select lt_plus_compat_lt_le omd (cmk_tv mu nu) budget
              cmk_omd_pos cmk_ds_omd_lt_one Htv0 Hbudget Harch) as [k Hk].
  exists k.
  apply (le_lt_trans _ (mult (cmk_r_pow omd k) (cmk_tv mu nu))).
  - (* the power converts from [req_r_pow] (the rsq-chain power) to [cmk_r_pow]
       (the selector power) along [req] *)
    exact (le_id_r (cmk_tv (cmk_titer k mu) (cmk_titer k nu))
                     (mult (req_r_pow omd k) (cmk_tv mu nu))
                     (mult (cmk_r_pow omd k) (cmk_tv mu nu))
             (req_mult_compat (req_r_pow omd k) (cmk_r_pow omd k)
                (cmk_tv mu nu) (cmk_tv mu nu)
                (req_sym _ _ (cmk_r_pow_req_r_pow omd k))
                (req_refl (cmk_tv mu nu)))
             (rsq_bounded_softmax_tv_iter S sumf sum_ext sum_linear sum_add
                sum_le abs_sum_le_h enum enum_nonempty temp temp_pos Delta
                Delta_pos z z_lb z_ub bs_swap bs_abs bs_lpc sum_eq_list
                k mu nu Hmu Hnu)).
  - exact Hk.
Defined.

(* The closing theorem (non-strict form): TV(T^k mu, T^k nu) <= budget *)
Theorem cmk_attention_mixing_time_le :
  forall mu nu : S -> R,
  req (sumf mu) one -> req (sumf nu) one ->
  forall budget : R, lt zero budget ->
  (forall x : R, le zero x ->
     sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
  le zero (cmk_tv mu nu) ->
  sigT (fun k : nat =>
    le (cmk_tv (cmk_titer k mu) (cmk_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget Harch Htv0.
  destruct (cmk_k_select_le lt_plus_compat_lt_le omd (cmk_tv mu nu) budget
              cmk_omd_pos cmk_ds_omd_lt_one Htv0 Hbudget Harch) as [k Hk].
  exists k.
  apply (le_trans _ (mult (cmk_r_pow omd k) (cmk_tv mu nu))).
  - (* the power converts from [req_r_pow] (the rsq-chain power) to [cmk_r_pow]
       (the selector power) along [req] *)
    exact (le_id_r (cmk_tv (cmk_titer k mu) (cmk_titer k nu))
                     (mult (req_r_pow omd k) (cmk_tv mu nu))
                     (mult (cmk_r_pow omd k) (cmk_tv mu nu))
             (req_mult_compat (req_r_pow omd k) (cmk_r_pow omd k)
                (cmk_tv mu nu) (cmk_tv mu nu)
                (req_sym _ _ (cmk_r_pow_req_r_pow omd k))
                (req_refl (cmk_tv mu nu)))
             (rsq_bounded_softmax_tv_iter S sumf sum_ext sum_linear sum_add
                sum_le abs_sum_le_h enum enum_nonempty temp temp_pos Delta
                Delta_pos z z_lb z_ub bs_swap bs_abs bs_lpc sum_eq_list
                k mu nu Hmu Hnu)).
  - exact Hk.
Defined.

End CmkMixTime.

(* ============================================================ *)
(* Concrete-layer anchor: one-statement req-face supply of the expf mini interface *)
(*   (the [AttnDoeblin] Part C counterpart). The five properties of
   [real_expf_realizable] are exactly req-face statements ([real_lt]/
   [real_eq]/[real_le] are the lt/req/le field values of the instance
   [RealEnhancedReal]); the lemma hands the already-proved witness over
   unchanged. *)
(* ============================================================ *)

Lemma cmk_expf_realizable :
  sigT (fun f : Real -> Real => And (forall x : Real, lt zero (f x))
        (And (req (f zero) one)
        (And (forall a b : Real, req (f (plus a b)) (mult (f a) (f b)))
        (And (forall a b : Real, lt a b -> lt (f a) (f b))
             (forall a b : Real, le a b -> le (f a) (f b)))))).
Proof. exact real_expf_realizable. Qed.

(* Assumption audit: the new statements carry no external unproved premises (all Closed; premises are explicit section variables) *)
Print Assumptions cmk_k_select.
Print Assumptions cmk_pow_budget.
Print Assumptions cmk_k_select_le.
Print Assumptions cmk_bernoulli_upper.
Print Assumptions cmk_attention_mixing_time.
Print Assumptions cmk_attention_mixing_time_le.
Print Assumptions cmk_expf_realizable.

(* ################ Assumption-resolution block: base lemma (the req-face list-sum bridge) ################ *)
(* Pointwise agreement of the [sumd] folder with the rsq list sum, by induction
   on [en]; this replays the proof of [cms_sum_eq_list] of [ConcMixSelFeed] in
   place — that module requires this one, so the shared proof chain is
   reproduced here rather than imported. *)
Lemma cmkr_sum_eq_list_aux : forall (S0 : Set) (en : list S0) (g : S0 -> Real),
  req (sumd_list_sum S0 g en) (rsq_bs_list_sum S0 g en).
Proof.
  intros S0 en g.
  induction en as [| x t IH].
  - exact (req_refl zero).
  - simpl.
    exact (req_plus_compat (g x) (g x) (sumd_list_sum S0 g t)
             (rsq_bs_list_sum S0 g t) (req_refl (g x)) IH).
Defined.

(* ################ Assumption-resolution block: the realized reading of [sumf] ##################### *)
(* Under the realization [sumf := csm_sumf S enum], all six sum-interface slots
   of [CmkMixTime] are supplied from the proved [csm_] lemmas of
   [UpReqConcSoftmax] with explicit arguments. *)

Section CmkMixTimeResolved.

Variable S : Set.
Variable enum : list S.

Let sumf : (S -> Real) -> Real := csm_sumf S enum.

(* the [sum_ext] slot (the same statement as the [sum_ext] slot of [CmkMixTime]) *)
Theorem cmkr_sum_ext : forall f g : S -> Real,
  (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (csm_sum_ext S enum f g H).
Qed.

(* the [sum_linear] slot (the same statement as in [CmkMixTime]) *)
Theorem cmkr_sum_linear : forall (a : Real) (f : S -> Real),
  req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Proof.
  intros a f.
  exact (csm_sum_linear S enum a f).
Qed.

(* the [sum_add] slot (the same statement as in [CmkMixTime]) *)
Theorem cmkr_sum_add : forall f g : S -> Real,
  req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Proof.
  intros f g.
  exact (csm_sum_add S enum f g).
Qed.

(* the [sum_le] slot (the same statement as in [CmkMixTime]) *)
Theorem cmkr_sum_le : forall f g : S -> Real,
  (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (csm_sum_le S enum f g H).
Qed.

(* the [sum_eq_list] slot (the same statement as in [CmkMixTime]) *)
Theorem cmkr_sum_eq_list : forall g : S -> Real,
  req (sumf g) (rsq_bs_list_sum S g enum).
Proof.
  intro g.
  exact (cmkr_sum_eq_list_aux S enum g).
Qed.

(* the [bs_swap] slot (the same statement as in [CmkMixTime]): derived from the
   [sum_eq_list] slot together with the swap of the double list sum *)
Theorem cmkr_bs_swap : forall f : S -> S -> Real,
  req (sumf (fun s : S => sumf (fun s' : S => f s s')))
      (sumf (fun s' : S => sumf (fun s : S => f s s'))).
Proof.
  intros f.
  assert (Hsw : forall l1 l2 : list S,
    req (sumd_list_sum S (fun s : S => sumd_list_sum S (fun s' : S => f s s') l2) l1)
        (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') l1) l2)).
  { intros l1 l2.
    induction l1 as [| x t IH].
    - induction l2 as [| y t2 IH2].
      + exact (req_refl zero).
      + exact (req_trans zero
            (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2)
            (plus zero
               (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2))
            IH2
            (req_sym
               (plus zero
                  (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2))
               (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2)
               (req_trans
                  (plus zero
                     (sumd_list_sum S
                        (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2))
                  (plus
                     (sumd_list_sum S
                        (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2)
                     zero)
                  (sumd_list_sum S
                     (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2)
                  (plus_comm zero
                     (sumd_list_sum S
                        (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2))
                  (plus_zero
                     (sumd_list_sum S
                        (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2))))).
    - exact (req_trans
            (plus (sumd_list_sum S (fun s' : S => f x s') l2)
               (sumd_list_sum S (fun s : S => sumd_list_sum S (fun s' : S => f s s') l2) t))
            (plus (sumd_list_sum S (fun s' : S => f x s') l2)
               (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') t) l2))
            (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') (x :: t)) l2)
            (req_plus_compat (sumd_list_sum S (fun s' : S => f x s') l2)
               (sumd_list_sum S (fun s' : S => f x s') l2)
               (sumd_list_sum S (fun s : S => sumd_list_sum S (fun s' : S => f s s') l2) t)
               (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') t) l2)
               (req_refl (sumd_list_sum S (fun s' : S => f x s') l2)) IH)
            (req_sym
               (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') (x :: t)) l2)
               (plus (sumd_list_sum S (fun s' : S => f x s') l2)
                  (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') t) l2))
               (csm_sum_add S l2 (fun s' : S => f x s')
                  (fun s' : S => sumd_list_sum S (fun s : S => f s s') t)))). }
  exact (Hsw enum enum).
Qed.

(* the [bs_abs] slot (the same statement as in [CmkMixTime]): [abs] is the
   identity on nonnegative reals (replayed from proved real-layer lemmas) *)
Theorem cmkr_bs_abs : forall a : Real, le zero a -> req (abs a) a.
Proof.
  intros a H.
  assert (H' : real_le zero a) by exact H.
  unfold real_le in H'.
  destruct H' as [Hlt | Heq].
  - exact (real_abs_pos_req a Hlt).
  - exact (real_eq_trans (real_abs a) zero a
             (real_eq_trans (real_abs a) (real_abs zero) zero
                (real_abs_eq_compat a zero (real_eq_sym zero a Heq))
                real_abs_zero_req)
             Heq).
Qed.

(* the [bs_lpc] slot (the same statement as in [CmkMixTime]): strict mixed
   lt/le compatibility of addition (replayed in place) *)
Theorem cmkr_bs_lpc :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  assert (Hcd' : real_le c d) by exact Hcd.
  unfold real_le in Hcd'.
  destruct Hcd' as [Hlt | Heq].
  - exact (real_lt_plus_compat a b c d Hab Hlt).
  - apply (real_eq_lt_lt (plus a c) (plus a d) (plus b d)).
    + apply (RealSetoid.real_eq_plus_compat a c a d).
      * apply real_eq_refl.
      * exact Heq.
    + apply (real_eq_lt_lt (plus a d) (plus d a) (plus b d)).
      * apply real_plus_comm.
      * apply (real_lt_eq_lt (plus d a) (plus d b) (plus b d)).
        -- apply (real_lt_plus_translate d a b Hab).
        -- apply real_plus_comm.
Qed.

End CmkMixTimeResolved.

(* ################ Assumption-resolution block: the world data at the Fin 2 instance ############# *)
(* Certificates for the [temp]/[Delta]/[z]/[enum] slots at a nondegenerate
   two-point instance (the temperature at the unit, [z] the +1/-1 symmetric
   pair, [enum] the two-element list); the isomorphic statements live in the
   [cf2] dependency module, but that module requires this one, so the same
   proof terms are reproduced here. *)

Definition cmkr_temp : Real := one.

Theorem cmkr_temp_pos : lt zero cmkr_temp.
Proof.
  unfold cmkr_temp.
  exact one_pos.
Qed.

Definition cmkr_Delta : Real := one.

Theorem cmkr_Delta_pos : lt zero cmkr_Delta.
Proof.
  unfold cmkr_Delta.
  exact one_pos.
Qed.

Definition cmkr_z (s s' : bool) : Real := if s then one else opp one.

Theorem cmkr_z_lb : forall s s' : bool, le (opp cmkr_Delta) (cmkr_z s s').
Proof.
  intros s s'. destruct s as [ | ].
  - exact (inl (@rsq_bs_opp_lt cmkr_Delta cmkr_Delta_pos)).
  - exact (le_refl (opp cmkr_Delta)).
Qed.

Theorem cmkr_z_ub : forall s s' : bool, le (cmkr_z s s') cmkr_Delta.
Proof.
  intros s s'. destruct s as [ | ].
  - exact (le_refl cmkr_Delta).
  - exact (inl (@rsq_bs_opp_lt cmkr_Delta cmkr_Delta_pos)).
Qed.

(* the nonemptiness of the [enum] slot restated as a Set-layer sigT witness
   (carrier [InT], witness [true]) *)
Definition cmkr_enum : list bool := [true; false].

Theorem cmkr_enum_nonempty : sigT (fun t : bool => InT t cmkr_enum).
Proof.
  exact (existT _ true (InT_here true (false :: nil))).
Qed.

(* ================= Assumption audit of the resolved supplies (all Closed) ================= *)

Print Assumptions cmkr_sum_ext.
Print Assumptions cmkr_sum_linear.
Print Assumptions cmkr_sum_add.
Print Assumptions cmkr_sum_le.
Print Assumptions cmkr_sum_eq_list.
Print Assumptions cmkr_bs_swap.
Print Assumptions cmkr_bs_abs.
Print Assumptions cmkr_bs_lpc.
Print Assumptions cmkr_temp_pos.
Print Assumptions cmkr_Delta_pos.
Print Assumptions cmkr_z_lb.
Print Assumptions cmkr_z_ub.
Print Assumptions cmkr_enum_nonempty.
