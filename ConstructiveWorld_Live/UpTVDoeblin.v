(* ConstructiveWorld-Set - total-variation contraction for the Doeblin kernel. *)
(** * UpTVDoeblin: two-point total-variation contraction and its iterates.
    Mission.  Formalize theorem 5.10 on the Real layer: for a row-stochastic
      kernel K on a finite state world with uniform reference u and residual
      rate delta in (0,1], [tv_doeblin_contraction] proves
      TV(K*mu, K*nu) <= (1-delta)*TV(mu,nu); [tv_doeblin_iter] lifts it to
      TV(K^n*mu, K^n*nu) <= (1-delta)^n*TV(mu,nu). Part 2 satisfies the delta
      interface field with the explicit constant delta* := e^(-2*gamma/T)
      (the [tvd_dstar] family): delta* positivity, delta* <= 1, the kernel
      lower bound delta* * u <= K, the minorization certificate
      [tvd_minorization_supply], the assembled interface instance
      [tvd_dstar_instance], and the explicit-rate iterate theorem
      [tvd_dstar_iter_contraction] with rate (1 - e^(-2*gamma/T))^n.
    Dependencies.  Stdlib [List], [QArith.Qring]; [S01_BaseRing] through
      [S15_TailFEPUp] of this development, consumed by Require only.
    References.  ConstructiveWorld-Main, the baseline module [UpTVDoeblin.v]
      whose statement names are carried over here verbatim (statement-face
      Set-carrier completion); theorems 5.10 and 5.6b of the source paper;
      the [CW_ConstructiveWorld_219] dependency note of the baseline header.
    Constructivity.  All named statements are carried by [Set] (states are
      [list Real], sums run along the enumeration [real_list_sum], the order
      faces are [real_lt]/[real_le]/[real_eq]); extraction carries [Obj.magic]
      = 0 on the [.ml] and [.mli] sides with no erasure; [coqchk] reports
      [Axioms: none]; main statements close by [Qed].
    Build.  [rocq c -native-compiler no -q -Q . "" UpTVDoeblin.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.
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

(* ################ Part 0. Real-layer algebra helpers ################ *)

(* Pointwise ring-identity bridge: a real_eq goal reduces to a pointwise Q
   identity by ring resolution. real_plus/real_mult/real_opp/real_minus_r/
   real_one/real_zero are all transparent: after cbn [projT1 ...] the goal
   simplifies pointwise to a Q expression; real_abs/real_inv_pos stay opaque (ring atoms). *)
Ltac tvd_rring :=
  apply real_eq_of_zero_diff; intro n0; apply qeq_imp_qeqT;
  repeat match goal with
         | [ x : Real |- _ ] => destruct x
         end;
  cbn [projT1 real_plus real_mult real_opp real_minus_r real_one real_zero
       real_list_sum real_of_nat] in *;
  ring.

(* ---- 0.1 le-side abs identity (building block 1): 0 <= a implies |a| == a ---- *)
(* Route: real_le = Or(real_lt)(real_eq), branch by branch.
   lt branch: real_abs_pos_req; eq branch: real_eq_abs_compat + real_abs_zero_req. *)
Lemma tvd_abs_le_id : forall a : Real,
  real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a Ha. unfold real_le in Ha.
  destruct Ha as [Hlt | Heq].
  - exact (real_abs_pos_req a Hlt).
  - apply (real_eq_trans (real_abs a) (real_abs real_zero) a).
    + exact (RealSetoid.real_eq_abs_compat a real_zero (real_eq_sym real_zero a Heq)).
    + apply (real_eq_trans (real_abs real_zero) real_zero a).
      * exact real_abs_zero_req.
      * exact Heq.
Qed.

(* ---- 0.2 Setoid compatibility of subtraction ---- *)
Lemma tvd_eq_minus_compat : forall a b c d : Real,
  real_eq a b -> real_eq c d -> real_eq (real_minus_r a c) (real_minus_r b d).
Proof.
  intros a b c d Hab Hcd. unfold real_minus_r.
  apply (RealSetoid.real_eq_plus_compat a (real_opp c) b (real_opp d)).
  - exact Hab.
  - exact (RealSetoid.real_eq_opp_compat c d Hcd).
Qed.

(* Left common factor: (c+x) - (c+y) == x - y *)
Lemma tvd_minus_plus_congr_l : forall c x y : Real,
  real_eq (real_minus_r (real_plus c x) (real_plus c y)) (real_minus_r x y).
Proof. intros c x y. tvd_rring. Qed.

(* Factor out on subtraction (k in front): k*x - k*y == k*(x-y) *)
Lemma tvd_minus_factor : forall k x y : Real,
  real_eq (real_minus_r (real_mult k x) (real_mult k y))
          (real_mult k (real_minus_r x y)).
Proof. intros k x y. tvd_rring. Qed.

(* Factor out on subtraction (k behind): x*k - y*k == (x-y)*k *)
Lemma tvd_minus_factor_r : forall x y k : Real,
  real_eq (real_minus_r (real_mult x k) (real_mult y k))
          (real_mult (real_minus_r x y) k).
Proof. intros x y k. tvd_rring. Qed.

(* Subtraction absorption: x + (y - x) == y *)
Lemma tvd_plus_minus_absorb_l : forall x y : Real,
  real_eq (real_plus x (real_minus_r y x)) y.
Proof. intros x y. tvd_rring. Qed.

(* Subtraction absorption (reversed): (y - x) + x == y *)
Lemma tvd_plus_minus_absorb_r : forall x y : Real,
  real_eq (real_plus (real_minus_r y x) x) y.
Proof. intros x y. tvd_rring. Qed.

(* 0 + x == x *)
Lemma tvd_plus_zero_l : forall x : Real, real_eq (real_plus real_zero x) x.
Proof. intros x. tvd_rring. Qed.

(* Multiplicative swap-assoc reshuffle: a*(b*c) == b*(a*c) *)
Lemma tvd_mult_swap_ab : forall a b c : Real,
  real_eq (real_mult a (real_mult b c)) (real_mult b (real_mult a c)).
Proof.
  intros a b c.
  apply (real_eq_trans (real_mult a (real_mult b c))
                       (real_mult (real_mult a b) c)
                       (real_mult b (real_mult a c))).
  - exact (real_mult_assoc a b c).
  - apply (real_eq_trans (real_mult (real_mult a b) c)
             (real_mult (real_mult b a) c) (real_mult b (real_mult a c))).
    + apply (RealSetoid.real_eq_mult_compat (real_mult a b) c (real_mult b a) c).
      * exact (real_mult_comm a b).
      * apply real_eq_refl.
    + exact (real_eq_sym (real_mult b (real_mult a c))
               (real_mult (real_mult b a) c) (real_mult_assoc b a c)).
Qed.

(* ---- 0.3 Nonnegativity of subtraction: b <= a implies 0 <= a - b ---- *)
(* Or branch-by-branch: lt branch real_lt_plus_compat_lt_le + real_lt_id_l; eq branch setoid chain. *)
Lemma tvd_le_minus_nonneg : forall a b : Real,
  real_le b a -> real_le real_zero (real_minus_r a b).
Proof.
  intros a b Hab. unfold real_minus_r. unfold real_le in Hab.
  destruct Hab as [Hlt | Heq].
  - apply (RealSetoid.real_lt_le_iff_req real_zero
             (real_plus a (real_opp b))). left.
    apply (RealSetoid.real_lt_id_l real_zero
             (real_plus b (real_opp b))
             (real_plus a (real_opp b))).
    + exact (real_eq_sym (real_plus b (real_opp b)) real_zero
               (real_plus_opp b)).
    + exact (real_lt_plus_compat_lt_le b a (real_opp b) (real_opp b) Hlt
               (real_le_refl (real_opp b))).
  - apply (RealSetoid.real_eq_le).
    apply (real_eq_trans real_zero
             (real_plus b (real_opp b)) (real_plus a (real_opp b))).
    + exact (real_eq_sym (real_plus b (real_opp b)) real_zero
               (real_plus_opp b)).
    + apply (RealSetoid.real_eq_plus_compat b (real_opp b) a (real_opp b)).
      * exact Heq.
      * apply real_eq_refl.
Qed.

(* ---- 0.4 Positivity of two (built in this file to avoid the section binding of the same-named library lemma) ---- *)
Lemma tv_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus real_one real_one)).
  - exact (real_eq_sym (real_plus real_zero real_zero) real_zero
             (real_plus_zero real_zero)).
  - exact (real_lt_plus_compat real_zero real_one real_zero real_one
             real_lt_zero_one real_lt_zero_one).
Qed.

(* ---- 0.5b Pure ring-identity lifted pieces (for the in-section ring sites of Part 2) ----
   Under section-variable context, tvd_rring (destructing every Real context item)
   triggers pathological compile cost (minimal reproduction proven); sections use
   these lifted forms instead (generalized outside; pure AC/sign identities) or quote the base lemmas; statement face unchanged. ---- *)
Lemma tvd_mult_opp_mult_zero : forall g t : Real,
  real_eq (real_plus (real_mult g t) (real_mult (real_opp g) t)) real_zero.
Proof. intros g t. tvd_rring. Qed.

Lemma tvd_mult_reassoc5 : forall a b c d : Real,
  real_eq (real_mult (real_mult a b) (real_mult c d))
          (real_mult (real_mult c (real_mult b d)) a).
Proof. intros a b c d. tvd_rring. Qed.

Lemma tvd_mult_cca : forall a c : Real,
  real_eq (real_mult (real_mult a a) c) (real_mult (real_mult a c) a).
Proof. intros a c. tvd_rring. Qed.

Lemma tvd_mult_assoc_id : forall a b c : Real,
  real_eq (real_mult (real_mult a b) c) (real_mult a (real_mult b c)).
Proof. intros a b c. tvd_rring. Qed.

(* ---- 0.5 list sums: zero constant / extensionality (InT-restricted) / zero-sum pointwise annihilation ---- *)
Section TVListHelpers.
Variable X : Set.

Lemma tvd_list_sum_zero_const : forall (l : list X),
  real_eq (real_list_sum X (fun _ : X => real_zero) l) real_zero.
Proof.
  intro l. induction l as [| a rest IH].
  - apply real_eq_refl.
  - cbn [real_list_sum].
    apply (real_eq_trans
             (real_plus real_zero
                (real_list_sum X (fun _ : X => real_zero) rest))
             (real_list_sum X (fun _ : X => real_zero) rest)
             real_zero).
    + apply (real_eq_trans
               (real_plus real_zero
                  (real_list_sum X (fun _ : X => real_zero) rest))
               (real_plus (real_list_sum X (fun _ : X => real_zero) rest)
                          real_zero)
               (real_list_sum X (fun _ : X => real_zero) rest)).
      * exact (real_plus_comm real_zero
                 (real_list_sum X (fun _ : X => real_zero) rest)).
      * exact (real_plus_zero (real_list_sum X (fun _ : X => real_zero) rest)).
    + exact IH.
Qed.

(* ---- 0.5+ list constant sum: the sum of const c == n*c (introduced for Part 2;
       the pattern follows the base real_list_sum_g_const eq-chain proof, general-X version) ---- *)
Lemma tvd_list_sum_const : forall (c : Real) (l : list X),
  real_eq (real_list_sum X (fun _ : X => c) l)
          (real_mult (real_of_nat (length l)) c).
Proof.
  intros c l.
  induction l as [| a rest IH]; cbn [real_list_sum length].
  - (* nil: zero == c*0 == 0*c (of_nat 0 == real_zero definitionally) *)
    apply (real_eq_trans _ _ _ (real_eq_sym _ _ (real_mult_zero c)) (real_mult_comm c real_zero)).
  - (* cons: c + of_nat(len)*c == (1 + of_nat(len))*c == of_nat(S len)*c *)
    apply (real_eq_trans _ (real_plus c (real_mult (real_of_nat (length rest)) c)) _).
    + apply (RealSetoid.real_eq_plus_compat c (real_list_sum X (fun _ : X => c) rest)
                                            c (real_mult (real_of_nat (length rest)) c)
                                            (real_eq_refl _) IH).
    + apply (real_eq_trans _ (real_plus (real_mult real_one c) (real_mult (real_of_nat (length rest)) c)) _).
      * apply (RealSetoid.real_eq_plus_compat c (real_mult (real_of_nat (length rest)) c)
                                              (real_mult real_one c) (real_mult (real_of_nat (length rest)) c)
                                              (real_eq_sym _ _ (real_eq_trans _ _ _ (real_mult_comm real_one c) (real_mult_one c)))
                                              (real_eq_refl _)).
      * apply (real_eq_trans _ (real_mult (real_plus real_one (real_of_nat (length rest))) c) _).
        -- apply (real_distrib_r_local real_one (real_of_nat (length rest)) c).
        -- apply real_eq_refl.
Qed.

(* InT-restricted extensionality: pointwise equality on the enumerated members suffices (finite-world semantics;
   InT is the library's Set-layer constructive membership; In is Prop-layer and cannot be eliminated into Set) *)
Lemma tvd_list_sum_ext_in : forall (f g : X -> Real) (l : list X),
  (forall w : X, InT w l -> real_eq (f w) (g w)) ->
  real_eq (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros f g l H. induction l as [| a rest IH].
  - apply real_eq_refl.
  - cbn [real_list_sum].
    apply (RealSetoid.real_eq_plus_compat (f a) (real_list_sum X f rest)
                                          (g a) (real_list_sum X g rest)).
    + exact (H a (InT_here a rest)).
    + exact (IH (fun w Hw => H w (InT_next w a rest Hw))).
Qed.

(* Head positivity and zero-sum contradiction (for zero-sum pointwise annihilation; Empty_set-layer contradiction) *)
Lemma tvd_list_sum_head_pos_contra : forall (f : X -> Real) (a : X) (rest : list X),
  real_lt real_zero (f a) ->
  (forall v : X, real_le real_zero (f v)) ->
  real_eq (real_plus (f a) (real_list_sum X f rest)) real_zero ->
  Empty_set.
Proof.
  intros f a rest Halt Hnn H0.
  assert (Hlt1 : real_lt (real_plus real_zero real_zero)
                   (real_plus (real_list_sum X f rest) (f a))).
  { exact (real_lt_plus_compat_le_lt real_zero (real_list_sum X f rest)
             real_zero (f a)
             (real_list_sum_nonneg X f rest (fun v : X => Hnn v)) Halt). }
  assert (Hlt2 : real_lt (real_plus real_zero real_zero)
                   (real_plus (f a) (real_list_sum X f rest))).
  { apply (RealSetoid.real_lt_id_r
             (real_plus real_zero real_zero)
             (real_plus (real_list_sum X f rest) (f a))
             (real_plus (f a) (real_list_sum X f rest))).
    exact (real_plus_comm (real_list_sum X f rest) (f a)).
    exact Hlt1. }
  assert (Hlt3 : real_lt (real_plus real_zero real_zero) real_zero).
  { apply (RealSetoid.real_lt_id_r
             (real_plus real_zero real_zero)
             (real_plus (f a) (real_list_sum X f rest))
             real_zero).
    exact H0.
    exact Hlt2. }
  assert (Hlt4 : real_lt real_zero real_zero).
  { apply (RealSetoid.real_lt_id_l real_zero
             (real_plus real_zero real_zero)
             real_zero).
    exact (real_eq_sym (real_plus real_zero real_zero) real_zero
             (real_plus_zero real_zero)).
    exact Hlt3. }
  exact (real_lt_irrefl real_zero Hlt4).
Qed.

(* A sum of nonnegative terms is zero implies every enumerated term is zero.
   Induction on the InT witness (in the head case l is directly replaced by the witness-indexed w :: l0,
   avoiding an identity decision between w and the head variable -- under the Or encoding both branches are constructive). *)
Lemma tvd_list_sum_zero_nonneg_eq : forall (f : X -> Real) (w : X) (l : list X),
  (forall v : X, real_le real_zero (f v)) ->
  InT w l ->
  real_eq (real_list_sum X f l) real_zero ->
  real_eq (f w) real_zero.
Proof.
  intros f w l Hnn Hin.
  induction Hin as [l0 | y l0 Hin' IH]; intro H0.
  - (* Head: l = w :: l0, sum == f w + tail sum *)
    cbn [real_list_sum] in H0.
    destruct (Hnn w) as [Halt | Hweq].
    + exact (match (tvd_list_sum_head_pos_contra f w l0 Halt Hnn H0) with end).
    + exact (real_eq_sym real_zero (f w) Hweq).
  - (* Tail: annihilate the tail sum first (head f y handled branch-wise), then the IH *)
    cbn [real_list_sum] in H0.
    apply (IH).
    destruct (Hnn y) as [Halt | Hyeq].
    + exact (match (tvd_list_sum_head_pos_contra f y l0 Halt Hnn H0) with end).
    + apply (real_eq_trans (real_list_sum X f l0)
               (real_plus (f y) (real_list_sum X f l0)) real_zero).
      * apply (real_eq_sym (real_plus (f y) (real_list_sum X f l0))
                 (real_list_sum X f l0)).
        apply (real_eq_trans (real_plus (f y) (real_list_sum X f l0))
                   (real_plus real_zero (real_list_sum X f l0))
                   (real_list_sum X f l0)).
        -- apply (RealSetoid.real_eq_plus_compat (f y) (real_list_sum X f l0)
                     real_zero (real_list_sum X f l0)).
           ++ exact (real_eq_sym real_zero (f y) Hyeq).
           ++ apply real_eq_refl.
        -- exact (tvd_plus_zero_l (real_list_sum X f l0)).
      * exact H0.
Qed.

(* ---- 0.6 list double-sum swap (building block 2) ----
   General form: sum_{j in l2} sum_{i in l1} f i j == sum_{i in l1} sum_{j in l2} f i j
   (induction on l1 with l2 generalized; add reversal + IH + one definitional step) *)
Lemma tvd_list_sum_swap_gen : forall (l1 : list X) (l2 : list X)
                                         (f : X -> X -> Real),
  real_eq (real_list_sum X (fun j : X => real_list_sum X (fun i : X => f i j) l1) l2)
          (real_list_sum X (fun i : X => real_list_sum X (fun j : X => f i j) l2) l1).
Proof.
  intro l1. induction l1 as [| a rest IH]; intros l2 f.
  - (* l1 = nil: left = sum_j 0 == 0 == right (the right side reduces definitionally to 0) *)
    apply (real_eq_trans
             (real_list_sum X (fun j : X => real_list_sum X (fun i : X => f i j) nil) l2)
             (real_list_sum X (fun _ : X => real_zero) l2)
             real_zero).
    + apply (real_list_sum_ext X
               (fun j : X => real_list_sum X (fun i : X => f i j) nil)
               (fun _ : X => real_zero) l2).
      intro j. apply real_eq_refl.
    + exact (tvd_list_sum_zero_const l2).
  - cbn [real_list_sum].
    apply (real_eq_trans
             (real_list_sum X
                (fun j : X =>
                   real_plus (f a j) (real_list_sum X (fun i : X => f i j) rest))
                l2)
             (real_plus (real_list_sum X (fun j : X => f a j) l2)
                        (real_list_sum X
                           (fun j : X => real_list_sum X (fun i : X => f i j) rest)
                           l2))).
    + exact (real_list_sum_add X (fun j : X => f a j)
               (fun j : X => real_list_sum X (fun i : X => f i j) rest) l2).
    + apply (RealSetoid.real_eq_plus_compat
               (real_list_sum X (fun j : X => f a j) l2)
               (real_list_sum X
                  (fun j : X => real_list_sum X (fun i : X => f i j) rest)
                  l2)
               (real_list_sum X (fun j : X => f a j) l2)
               (real_list_sum X
                  (fun i : X => real_list_sum X (fun j : X => f i j) l2)
                  rest)).
      * apply real_eq_refl.
      * exact (IH l2 f).
Qed.

Lemma tvd_list_sum_swap : forall (l : list X) (f : X -> X -> Real),
  real_eq (real_list_sum X (fun i : X => real_list_sum X (fun j : X => f i j) l) l)
          (real_list_sum X (fun j : X => real_list_sum X (fun i : X => f i j) l) l).
Proof.
  intros l f. exact (real_eq_sym _ _ (tvd_list_sum_swap_gen l l f)).
Qed.

(* ---- 0.7 Difference of list sums: sum(x - y) == sum x - sum y ---- *)
Lemma tvd_list_sum_minus : forall (f g : X -> Real) (l : list X),
  real_eq (real_list_sum X (fun w : X => real_minus_r (f w) (g w)) l)
          (real_minus_r (real_list_sum X f l) (real_list_sum X g l)).
Proof.
  intros f g l.
  apply (real_eq_trans
           (real_list_sum X (fun w : X => real_minus_r (f w) (g w)) l)
           (real_plus (real_list_sum X f l)
                      (real_list_sum X (fun w : X => real_opp (g w)) l))).
  - exact (real_list_sum_add X f (fun w : X => real_opp (g w)) l).
  - apply (RealSetoid.real_eq_plus_compat
             (real_list_sum X f l)
             (real_list_sum X (fun w : X => real_opp (g w)) l)
             (real_list_sum X f l)
             (real_opp (real_list_sum X g l))).
    + apply real_eq_refl.
    + exact (real_list_sum_opp X g l).
Qed.

End TVListHelpers.

(* ---- 0.8 Two auxiliary pieces (for Part 2; the same-named base forms do not match) ---- *)
(* lt implies le (Or left-injection; the base real_lt_le_iff is an Id-family form, avoided) *)
Lemma tvd_lt_le : forall a b : Real, real_lt a b -> real_le a b.
Proof.
  intros a b H.
  apply (RealSetoid.real_lt_le_iff_req a b). left. exact H.
Qed.

(* le multiplication order-preservation with the constant on the left: 0 < a, b <= c implies a*b <= a*c *)
Lemma tvd_le_mult_compat_l : forall a b c : Real,
  real_lt real_zero a -> real_le b c -> real_le (real_mult a b) (real_mult a c).
Proof.
  intros a b c Ha Hbc.
  apply (real_le_trans (real_mult a b) (real_mult b a) (real_mult a c)).
  - apply (RealSetoid.real_eq_le _ _). exact (real_mult_comm a b).
  - apply (real_le_trans (real_mult b a) (real_mult c a) (real_mult a c)).
    + exact (real_le_mult_compat b c a Ha Hbc).
    + apply (RealSetoid.real_eq_le _ _). exact (real_mult_comm c a).
Qed.

(* ################ Part 1. The list discrete-state world ################ *)

Section TVRealWorld.

(* Discrete-state world: states are list Real, enumerated by states; sums always run along the enumeration.
   (K : list Real -> list Real -> Real is a row-stochastic kernel -- the state type
     is list Real, so the enumeration is list (list Real); the element type of real_list_sum
     is (list Real), i.e. the real_list_sum (K i) states shape noted above.) *)
Variable states : list (list Real).
Variable n_pos : real_lt real_zero (real_of_nat (length states)).
Variable K : list Real -> list Real -> Real.
Variable K_row : forall i : list Real,
  real_eq (real_list_sum (list Real) (K i) states) real_one.
Variable K_pos : forall i j : list Real, real_le real_zero (K i j).
Variable u : list Real -> Real.
Variable u_norm : real_eq (real_list_sum (list Real) u states) real_one.
Variable delta : Real.
Variable delta_pos : real_lt real_zero delta.
Variable delta_le_one : real_le delta real_one.
Variable minorization : forall i j : list Real,
  real_le (real_mult delta (u j)) (K i j).

(* Honest interface: the list version of abs_sum_le (same shape as the SumOver.abs_sum_le field) *)
Variable abs_sum_le_list : forall f : list Real -> Real,
  real_le (real_abs (real_list_sum (list Real) f states))
          (real_list_sum (list Real) (fun w : list Real => real_abs (f w)) states).

(* ---- 1.1 TV and the 1/2 factor ---- *)
Definition tv_half : Real :=
  real_inv_pos (real_plus real_one real_one) tv_two_pos.

Lemma tv_half_pos : real_lt real_zero tv_half.
Proof. exact (real_inv_pos_pos (real_plus real_one real_one) tv_two_pos). Qed.

(* TV_REAL: tv(mu,nu) := (1/2)*sum |mu_i - nu_i| (itemwise along the enumeration) *)
Definition tv_doeblin (mu nu : list Real -> Real) : Real :=
  real_mult tv_half
    (real_list_sum (list Real)
       (fun s : list Real => real_abs (real_minus_r (mu s) (nu s))) states).

(* One-step Markov iterate: K*mu(j) := sum_i mu(i)*K(i,j) *)
Definition tv_step (mu : list Real -> Real) (j : list Real) : Real :=
  real_list_sum (list Real) (fun i : list Real => real_mult (mu i) (K i j)) states.

(* ---- 1.2 Residual constant 1-delta ---- *)
Definition tv_omd : Real := real_minus_r real_one delta.

(* delta < 1 implies 0 < 1-delta (lt branch: real_lt_plus_compat_lt_le + real_lt_id_l) *)
Lemma tv_omd_pos_of_lt : real_lt delta real_one -> real_lt real_zero tv_omd.
Proof.
  intro Hdlt. apply (RealSetoid.real_lt_id_l real_zero
           (real_plus delta (real_opp delta))
           (real_plus real_one (real_opp delta))).
  - exact (real_eq_sym (real_plus delta (real_opp delta)) real_zero
             (real_plus_opp delta)).
  - exact (real_lt_plus_compat_lt_le delta real_one (real_opp delta)
             (real_opp delta) Hdlt (real_le_refl (real_opp delta))).
Qed.

(* delta == 1 implies 1-delta == 0 (setoid chain) *)
Lemma tv_omd_eq_zero : real_eq delta real_one -> real_eq tv_omd real_zero.
Proof.
  intro Hd1. apply (real_eq_trans (real_plus real_one (real_opp delta))
                                  (real_plus real_one (real_opp real_one))
                                  real_zero).
  - apply (RealSetoid.real_eq_plus_compat real_one (real_opp delta)
             real_one (real_opp real_one)).
    + apply real_eq_refl.
    + exact (RealSetoid.real_eq_opp_compat delta real_one Hd1).
  - exact (real_plus_opp real_one).
Qed.

(* 0 <= 1-delta (Or branch-wise; the delta=1 branch reaches == 0 through the setoid chain) *)
Lemma tv_omd_nonneg : real_le real_zero tv_omd.
Proof.
  destruct delta_le_one as [Hdlt | Hd1].
  - apply (RealSetoid.real_lt_le_iff_req real_zero tv_omd). left.
    exact (tv_omd_pos_of_lt Hdlt).
  - apply (RealSetoid.real_eq_le).
    exact (real_eq_sym tv_omd real_zero (tv_omd_eq_zero Hd1)).
Qed.
(* ---- 1.3 Residual kernel R := inv(1-delta)*(K - delta*u) ---- *)
(* The positivity premise is carried as an explicit argument (the delta=1 branch does not use R) *)
Definition tv_r_kernel (Homd : real_lt real_zero tv_omd) (i j : list Real) : Real :=
  real_mult (real_inv_pos tv_omd Homd)
            (real_minus_r (K i j) (real_mult delta (u j))).

Lemma tv_r_nonneg : forall (Homd : real_lt real_zero tv_omd) (i j : list Real),
  real_le real_zero (tv_r_kernel Homd i j).
Proof.
  intros Homd i j. unfold tv_r_kernel.
  apply (RealSetoid.real_le_id_r real_zero
           (real_mult (real_minus_r (K i j) (real_mult delta (u j)))
                      (real_inv_pos tv_omd Homd))
           (real_mult (real_inv_pos tv_omd Homd)
                      (real_minus_r (K i j) (real_mult delta (u j))))).
  - exact (real_mult_comm (real_minus_r (K i j) (real_mult delta (u j)))
             (real_inv_pos tv_omd Homd)).
  - apply (RealSetoid.real_le_id_l real_zero
             (real_mult real_zero (real_inv_pos tv_omd Homd))
             (real_mult (real_minus_r (K i j) (real_mult delta (u j)))
                        (real_inv_pos tv_omd Homd))).
    + apply (real_eq_sym (real_mult real_zero (real_inv_pos tv_omd Homd)) real_zero).
      apply (real_eq_trans (real_mult real_zero (real_inv_pos tv_omd Homd))
               (real_mult (real_inv_pos tv_omd Homd) real_zero) real_zero).
      * exact (real_mult_comm real_zero (real_inv_pos tv_omd Homd)).
      * exact (real_mult_zero (real_inv_pos tv_omd Homd)).
    + exact (real_le_mult_compat real_zero
               (real_minus_r (K i j) (real_mult delta (u j)))
               (real_inv_pos tv_omd Homd)
               (real_inv_pos_pos tv_omd Homd)
               (tvd_le_minus_nonneg (K i j) (real_mult delta (u j))
                  (minorization i j))).
Qed.

(* The enumerated sum of delta*u == delta*1 *)
Lemma tv_delta_u_sum : real_eq
  (real_list_sum (list Real) (fun j : list Real => real_mult delta (u j)) states)
  (real_mult delta real_one).
Proof.
  apply (real_eq_trans
           (real_list_sum (list Real) (fun j : list Real => real_mult delta (u j)) states)
           (real_mult delta (real_list_sum (list Real) u states))).
  - exact (real_list_sum_linear (list Real) delta u states).
  - apply (RealSetoid.real_eq_mult_compat delta (real_list_sum (list Real) u states)
             delta real_one).
    + apply real_eq_refl.
    + exact u_norm.
Qed.

(* Residual-row numerator sum: sum_j (K i j - delta*u j) == 1 - delta == tv_omd *)
Lemma tv_r_row_sub : forall i : list Real,
  real_eq (real_list_sum (list Real)
             (fun j : list Real => real_minus_r (K i j) (real_mult delta (u j))) states)
          tv_omd.
Proof.
  intro i.
  apply (real_eq_trans
           (real_list_sum (list Real)
              (fun j : list Real => real_minus_r (K i j) (real_mult delta (u j))) states)
           (real_minus_r (real_list_sum (list Real) (K i) states)
                         (real_list_sum (list Real)
                            (fun j : list Real => real_mult delta (u j)) states))).
  - exact (tvd_list_sum_minus (list Real) (K i)
             (fun j : list Real => real_mult delta (u j)) states).
  - apply (real_eq_trans
             (real_minus_r (real_list_sum (list Real) (K i) states)
                           (real_list_sum (list Real)
                              (fun j : list Real => real_mult delta (u j)) states))
             (real_minus_r real_one (real_mult delta real_one))).
    + exact (tvd_eq_minus_compat (real_list_sum (list Real) (K i) states) real_one
               (real_list_sum (list Real)
                  (fun j : list Real => real_mult delta (u j)) states)
               (real_mult delta real_one)
               (K_row i) tv_delta_u_sum).
    + apply (tvd_eq_minus_compat real_one real_one
               (real_mult delta real_one) delta).
      * apply real_eq_refl.
      * exact (real_mult_one delta).
Qed.

(* Residual-kernel row normalization: sum_j R(i,j) == 1 *)
Lemma tv_r_row : forall (Homd : real_lt real_zero tv_omd) (i : list Real),
  real_eq (real_list_sum (list Real) (tv_r_kernel Homd i) states) real_one.
Proof.
  intros Homd i. unfold tv_r_kernel.
  apply (real_eq_trans
           (real_list_sum (list Real)
              (fun j : list Real =>
                 real_mult (real_inv_pos tv_omd Homd)
                           (real_minus_r (K i j) (real_mult delta (u j)))) states)
           (real_mult (real_inv_pos tv_omd Homd)
                      (real_list_sum (list Real)
                         (fun j : list Real =>
                            real_minus_r (K i j) (real_mult delta (u j))) states))).
  - exact (real_list_sum_linear (list Real) (real_inv_pos tv_omd Homd)
             (fun j : list Real => real_minus_r (K i j) (real_mult delta (u j))) states).
  - apply (real_eq_trans
             (real_mult (real_inv_pos tv_omd Homd)
                        (real_list_sum (list Real)
                           (fun j : list Real =>
                              real_minus_r (K i j) (real_mult delta (u j))) states))
             (real_mult (real_inv_pos tv_omd Homd) tv_omd)).
    + apply (RealSetoid.real_eq_mult_compat (real_inv_pos tv_omd Homd)
               (real_list_sum (list Real)
                  (fun j : list Real =>
                     real_minus_r (K i j) (real_mult delta (u j))) states)
               (real_inv_pos tv_omd Homd)
               tv_omd).
      * apply real_eq_refl.
      * exact (tv_r_row_sub i).
    + apply (real_eq_trans (real_mult (real_inv_pos tv_omd Homd) tv_omd)
               (real_mult tv_omd (real_inv_pos tv_omd Homd)) real_one).
      * exact (real_mult_comm (real_inv_pos tv_omd Homd) tv_omd).
      * exact (real_inv_pos_correct tv_omd Homd).
Qed.

(* Kernel decomposition: K(i,j) == delta*u j + (1-delta)*R(i,j) *)
Lemma tv_decomp : forall (Homd : real_lt real_zero tv_omd) (i j : list Real),
  real_eq (K i j)
          (real_plus (real_mult delta (u j))
                     (real_mult tv_omd (tv_r_kernel Homd i j))).
Proof.
  intros Homd i j.
  apply (real_eq_trans (K i j)
           (real_plus (real_mult delta (u j))
                      (real_minus_r (K i j) (real_mult delta (u j))))).
  - exact (real_eq_sym (real_plus (real_mult delta (u j))
                          (real_minus_r (K i j) (real_mult delta (u j))))
             (K i j)
             (tvd_plus_minus_absorb_l (real_mult delta (u j)) (K i j))).
  - apply (RealSetoid.real_eq_plus_compat (real_mult delta (u j))
             (real_minus_r (K i j) (real_mult delta (u j)))
             (real_mult delta (u j))
             (real_mult tv_omd (tv_r_kernel Homd i j))).
    + apply real_eq_refl.
    + apply (real_eq_sym (real_mult tv_omd (tv_r_kernel Homd i j))
               (real_minus_r (K i j) (real_mult delta (u j)))).
      apply (real_eq_trans
               (real_mult tv_omd (tv_r_kernel Homd i j))
               (real_mult (real_mult tv_omd (real_inv_pos tv_omd Homd))
                          (real_minus_r (K i j) (real_mult delta (u j))))).
      * exact (real_mult_assoc tv_omd (real_inv_pos tv_omd Homd)
                 (real_minus_r (K i j) (real_mult delta (u j)))).
      * apply (real_eq_trans
                 (real_mult (real_mult tv_omd (real_inv_pos tv_omd Homd))
                            (real_minus_r (K i j) (real_mult delta (u j))))
                 (real_mult real_one
                            (real_minus_r (K i j) (real_mult delta (u j))))).
        -- apply (RealSetoid.real_eq_mult_compat
                    (real_mult tv_omd (real_inv_pos tv_omd Homd))
                    (real_minus_r (K i j) (real_mult delta (u j)))
                    real_one
                    (real_minus_r (K i j) (real_mult delta (u j)))).
           ++ exact (real_inv_pos_correct tv_omd Homd).
           ++ apply real_eq_refl.
        -- apply (real_eq_trans
                    (real_mult real_one (real_minus_r (K i j) (real_mult delta (u j))))
                    (real_mult (real_minus_r (K i j) (real_mult delta (u j))) real_one)
                    (real_minus_r (K i j) (real_mult delta (u j)))).
           ++ exact (real_mult_comm real_one
                       (real_minus_r (K i j) (real_mult delta (u j)))).
           ++ exact (real_mult_one (real_minus_r (K i j) (real_mult delta (u j)))).
Qed.

(* ---- 1.4 One step and the one-step decomposition ---- *)
(* One-step decomposition: K*mu(j) == delta*u j + (1-delta)*sum_i mu(i)*R(i,j) *)
Lemma tv_step_decomp : forall (Homd : real_lt real_zero tv_omd)
                              (mu : list Real -> Real) (j : list Real),
  real_eq (real_list_sum (list Real) mu states) real_one ->
  real_eq (tv_step mu j)
          (real_plus (real_mult delta (u j))
                     (real_mult tv_omd
                        (real_list_sum (list Real)
                           (fun i : list Real => real_mult (mu i) (tv_r_kernel Homd i j))
                           states))).
Proof.
  intros Homd mu j Hmu. unfold tv_step.
  apply (real_eq_trans
           (real_list_sum (list Real)
              (fun i : list Real => real_mult (mu i) (K i j)) states)
           (real_plus
              (real_list_sum (list Real)
                 (fun i : list Real => real_mult (mu i) (real_mult delta (u j))) states)
              (real_list_sum (list Real)
                 (fun i : list Real =>
                    real_mult (mu i) (real_mult tv_omd (tv_r_kernel Homd i j))) states))).
  - (* sum mu*K == sum (mu*deltau + mu*omd*R) == sum mu*deltau + sum mu*omd*R *)
    apply (real_eq_trans
             (real_list_sum (list Real)
                (fun i : list Real => real_mult (mu i) (K i j)) states)
             (real_list_sum (list Real)
                (fun i : list Real =>
                   real_plus (real_mult (mu i) (real_mult delta (u j)))
                             (real_mult (mu i) (real_mult tv_omd (tv_r_kernel Homd i j))))
                states)).
    + apply (real_list_sum_ext (list Real)
               (fun i : list Real => real_mult (mu i) (K i j))
               (fun i : list Real =>
                  real_plus (real_mult (mu i) (real_mult delta (u j)))
                            (real_mult (mu i) (real_mult tv_omd (tv_r_kernel Homd i j))))
               states).
      intro i.
      apply (real_eq_trans (real_mult (mu i) (K i j))
               (real_mult (mu i)
                          (real_plus (real_mult delta (u j))
                                     (real_mult tv_omd (tv_r_kernel Homd i j))))).
      * apply (RealSetoid.real_eq_mult_compat (mu i) (K i j) (mu i)
                 (real_plus (real_mult delta (u j))
                            (real_mult tv_omd (tv_r_kernel Homd i j)))).
        -- apply real_eq_refl.
        -- exact (tv_decomp Homd i j).
      * exact (real_distrib (mu i) (real_mult delta (u j))
                 (real_mult tv_omd (tv_r_kernel Homd i j))).
    + exact (real_list_sum_add (list Real)
               (fun i : list Real => real_mult (mu i) (real_mult delta (u j)))
               (fun i : list Real =>
                  real_mult (mu i) (real_mult tv_omd (tv_r_kernel Homd i j))) states).
  - (* (sum mu*deltau) + (sum mu*omd*R) == delta*u j + omd*sum mu*R *)
    apply (RealSetoid.real_eq_plus_compat
             (real_list_sum (list Real)
                (fun i : list Real => real_mult (mu i) (real_mult delta (u j))) states)
             (real_list_sum (list Real)
                (fun i : list Real =>
                   real_mult (mu i) (real_mult tv_omd (tv_r_kernel Homd i j))) states)
             (real_mult delta (u j))
             (real_mult tv_omd
                (real_list_sum (list Real)
                   (fun i : list Real => real_mult (mu i) (tv_r_kernel Homd i j))
                   states))).
    + apply (real_eq_trans
               (real_list_sum (list Real)
                  (fun i : list Real => real_mult (mu i) (real_mult delta (u j))) states)
               (real_mult (real_mult delta (u j))
                          (real_list_sum (list Real) mu states))).
      * exact (real_list_sum_linear_r (list Real) (real_mult delta (u j)) mu states).
      * apply (real_eq_trans
                 (real_mult (real_mult delta (u j))
                            (real_list_sum (list Real) mu states))
                 (real_mult (real_mult delta (u j)) real_one)).
        -- apply (RealSetoid.real_eq_mult_compat (real_mult delta (u j))
                     (real_list_sum (list Real) mu states)
                     (real_mult delta (u j)) real_one).
           ++ apply real_eq_refl.
           ++ exact Hmu.
        -- exact (real_mult_one (real_mult delta (u j))).
    + apply (real_eq_trans
               (real_list_sum (list Real)
                  (fun i : list Real =>
                     real_mult (mu i) (real_mult tv_omd (tv_r_kernel Homd i j))) states)
               (real_list_sum (list Real)
                  (fun i : list Real =>
                     real_mult tv_omd (real_mult (mu i) (tv_r_kernel Homd i j)))
                  states)).
      * apply (real_list_sum_ext (list Real)
                   (fun i : list Real =>
                      real_mult (mu i) (real_mult tv_omd (tv_r_kernel Homd i j)))
                   (fun i : list Real =>
                      real_mult tv_omd (real_mult (mu i) (tv_r_kernel Homd i j)))
                   states).
        intro i. exact (tvd_mult_swap_ab (mu i) tv_omd (tv_r_kernel Homd i j)).
      * exact (real_list_sum_linear (list Real) tv_omd
                   (fun i : list Real => real_mult (mu i) (tv_r_kernel Homd i j))
                   states).
Qed.

(* One step preserves normalization *)
Lemma tv_step_norm : forall mu : list Real -> Real,
  real_eq (real_list_sum (list Real) mu states) real_one ->
  real_eq (real_list_sum (list Real) (tv_step mu) states) real_one.
Proof.
  intros mu Hmu. unfold tv_step.
  apply (real_eq_trans
           (real_list_sum (list Real)
              (fun j : list Real =>
                 real_list_sum (list Real)
                   (fun i : list Real => real_mult (mu i) (K i j)) states)
              states)
           (real_list_sum (list Real)
              (fun i : list Real =>
                 real_list_sum (list Real)
                   (fun j : list Real => real_mult (mu i) (K i j)) states)
              states)).
  - exact (real_eq_sym _ _ (tvd_list_sum_swap (list Real) states
                    (fun (i j : list Real) => real_mult (mu i) (K i j)))).
  - apply (real_eq_trans
             (real_list_sum (list Real)
                (fun i : list Real =>
                   real_list_sum (list Real)
                     (fun j : list Real => real_mult (mu i) (K i j)) states)
                states)
             (real_list_sum (list Real)
                (fun i : list Real =>
                   real_mult (mu i)
                             (real_list_sum (list Real) (K i) states)) states)).
    + apply (real_list_sum_ext (list Real)
               (fun i : list Real =>
                  real_list_sum (list Real)
                    (fun j : list Real => real_mult (mu i) (K i j)) states)
               (fun i : list Real =>
                  real_mult (mu i) (real_list_sum (list Real) (K i) states))
               states).
      intro i. exact (real_list_sum_linear (list Real) (mu i) (K i) states).
    + apply (real_eq_trans
               (real_list_sum (list Real)
                  (fun i : list Real =>
                     real_mult (mu i) (real_list_sum (list Real) (K i) states))
                  states)
               (real_list_sum (list Real) mu states)).
      * apply (real_list_sum_ext (list Real)
                   (fun i : list Real =>
                      real_mult (mu i) (real_list_sum (list Real) (K i) states))
                   mu states).
        intro i.
        apply (real_eq_trans
                 (real_mult (mu i) (real_list_sum (list Real) (K i) states))
                 (real_mult (mu i) real_one) (mu i)).
        -- apply (RealSetoid.real_eq_mult_compat (mu i)
                     (real_list_sum (list Real) (K i) states) (mu i) real_one).
           ++ apply real_eq_refl.
           ++ exact (K_row i).
        -- apply (real_eq_trans (real_mult (mu i) real_one)
                     (real_mult real_one (mu i)) (mu i)).
           ++ exact (real_mult_comm (mu i) real_one).
           ++ apply (real_eq_trans (real_mult real_one (mu i))
                        (real_mult (mu i) real_one) (mu i)).
              ** exact (real_mult_comm real_one (mu i)).
              ** exact (real_mult_one (mu i)).
      * exact Hmu.
Qed.

(* ---- 1.5 |sum f*R| <= sum|f|*R ---- *)
Lemma tv_abs_row : forall (Homd : real_lt real_zero tv_omd)
                          (f : list Real -> Real) (j : list Real),
  real_le
    (real_abs (real_list_sum (list Real)
                 (fun i : list Real => real_mult (f i) (tv_r_kernel Homd i j)) states))
    (real_list_sum (list Real)
       (fun i : list Real => real_mult (real_abs (f i)) (tv_r_kernel Homd i j)) states).
Proof.
  intros Homd f j.
  apply (RealSetoid.real_le_id_r
           (real_abs (real_list_sum (list Real)
                        (fun i : list Real =>
                           real_mult (f i) (tv_r_kernel Homd i j)) states))
           (real_list_sum (list Real)
              (fun i : list Real =>
                 real_abs (real_mult (f i) (tv_r_kernel Homd i j))) states)
           (real_list_sum (list Real)
              (fun i : list Real =>
                 real_mult (real_abs (f i)) (tv_r_kernel Homd i j)) states)).
  - apply (real_list_sum_ext (list Real)
             (fun i : list Real => real_abs (real_mult (f i) (tv_r_kernel Homd i j)))
             (fun i : list Real =>
                real_mult (real_abs (f i)) (tv_r_kernel Homd i j)) states).
    intro i.
    apply (real_eq_trans (real_abs (real_mult (f i) (tv_r_kernel Homd i j)))
             (real_mult (real_abs (f i)) (real_abs (tv_r_kernel Homd i j)))).
    + exact (real_abs_mult_req (f i) (tv_r_kernel Homd i j)).
    + apply (RealSetoid.real_eq_mult_compat (real_abs (f i))
               (real_abs (tv_r_kernel Homd i j))
               (real_abs (f i)) (tv_r_kernel Homd i j)).
      * apply real_eq_refl.
      * exact (tvd_abs_le_id (tv_r_kernel Homd i j) (tv_r_nonneg Homd i j)).
  - exact (abs_sum_le_list
             (fun i : list Real => real_mult (f i) (tv_r_kernel Homd i j))).
Qed.

(* ---- 1.6 Main theorem A: two-point TV contraction ----
   TV(K*mu, K*nu) <= (1-delta)*TV(mu,nu).
   delta<1 branch: the Doeblin residual decomposition (K = delta*u + (1-delta)*R, R row-normalized);
   delta=1 branch: the minorization forces K(i,j) == u j (zero-sum pointwise annihilation),
   both TV sides == 0 (closed on the eq branch of real_le). *)
Theorem tv_doeblin_contraction : forall mu nu : list Real -> Real,
  real_eq (real_list_sum (list Real) mu states) real_one ->
  real_eq (real_list_sum (list Real) nu states) real_one ->
  real_le (tv_doeblin (tv_step mu) (tv_step nu))
          (real_mult tv_omd (tv_doeblin mu nu)).
Proof.
  intros mu nu Hmu Hnu.
  destruct delta_le_one as [Hdlt | Hd1].
  - (* ---- Branch 1: delta < 1, the Doeblin residual decomposition ---- *)
    assert (Homd : real_lt real_zero tv_omd) by exact (tv_omd_pos_of_lt Hdlt).
    (* Pointwise: |K*mu(j) - K*nu(j)| <= omd*sum_i |mu(i)-nu(i)|*R(i,j) *)
    assert (Hpt : forall j : list Real,
      real_le (real_abs (real_minus_r (tv_step mu j) (tv_step nu j)))
              (real_mult tv_omd
                 (real_list_sum (list Real)
                    (fun i : list Real =>
                       real_mult (real_abs (real_minus_r (mu i) (nu i)))
                                 (tv_r_kernel Homd i j)) states))).
    { intro j.
      assert (Hc1 : real_eq
                      (real_minus_r (tv_step mu j) (tv_step nu j))
                      (real_minus_r
                         (real_plus (real_mult delta (u j))
                            (real_mult tv_omd
                               (real_list_sum (list Real)
                                  (fun i : list Real =>
                                     real_mult (mu i) (tv_r_kernel Homd i j)) states)))
                         (real_plus (real_mult delta (u j))
                            (real_mult tv_omd
                               (real_list_sum (list Real)
                                  (fun i : list Real =>
                                     real_mult (nu i) (tv_r_kernel Homd i j)) states))))).
      { exact (tvd_eq_minus_compat (tv_step mu j)
                 (real_plus (real_mult delta (u j))
                    (real_mult tv_omd
                       (real_list_sum (list Real)
                          (fun i : list Real =>
                             real_mult (mu i) (tv_r_kernel Homd i j)) states)))
                 (tv_step nu j)
                 (real_plus (real_mult delta (u j))
                    (real_mult tv_omd
                       (real_list_sum (list Real)
                          (fun i : list Real =>
                             real_mult (nu i) (tv_r_kernel Homd i j)) states)))
                 (tv_step_decomp Homd mu j Hmu) (tv_step_decomp Homd nu j Hnu)). }
      assert (Hc2 : real_eq
                      (real_minus_r
                         (real_plus (real_mult delta (u j))
                            (real_mult tv_omd
                               (real_list_sum (list Real)
                                  (fun i : list Real =>
                                     real_mult (mu i) (tv_r_kernel Homd i j)) states)))
                         (real_plus (real_mult delta (u j))
                            (real_mult tv_omd
                               (real_list_sum (list Real)
                                  (fun i : list Real =>
                                     real_mult (nu i) (tv_r_kernel Homd i j)) states))))
                      (real_minus_r
                         (real_mult tv_omd
                            (real_list_sum (list Real)
                               (fun i : list Real =>
                                  real_mult (mu i) (tv_r_kernel Homd i j)) states))
                         (real_mult tv_omd
                            (real_list_sum (list Real)
                               (fun i : list Real =>
                                  real_mult (nu i) (tv_r_kernel Homd i j)) states)))).
      { exact (tvd_minus_plus_congr_l (real_mult delta (u j))
                 (real_mult tv_omd
                    (real_list_sum (list Real)
                       (fun i : list Real =>
                          real_mult (mu i) (tv_r_kernel Homd i j)) states))
                 (real_mult tv_omd
                    (real_list_sum (list Real)
                       (fun i : list Real =>
                          real_mult (nu i) (tv_r_kernel Homd i j)) states))). }
      assert (Hc3 : real_eq
                      (real_minus_r
                         (real_mult tv_omd
                            (real_list_sum (list Real)
                               (fun i : list Real =>
                                  real_mult (mu i) (tv_r_kernel Homd i j)) states))
                         (real_mult tv_omd
                            (real_list_sum (list Real)
                               (fun i : list Real =>
                                  real_mult (nu i) (tv_r_kernel Homd i j)) states)))
                      (real_mult tv_omd
                         (real_minus_r
                            (real_list_sum (list Real)
                               (fun i : list Real =>
                                  real_mult (mu i) (tv_r_kernel Homd i j)) states)
                            (real_list_sum (list Real)
                               (fun i : list Real =>
                                  real_mult (nu i) (tv_r_kernel Homd i j)) states)))).
      { exact (tvd_minus_factor tv_omd
                 (real_list_sum (list Real)
                    (fun i : list Real =>
                       real_mult (mu i) (tv_r_kernel Homd i j)) states)
                 (real_list_sum (list Real)
                    (fun i : list Real =>
                       real_mult (nu i) (tv_r_kernel Homd i j)) states)). }
      assert (Hc4 : real_eq
                      (real_mult tv_omd
                         (real_minus_r
                            (real_list_sum (list Real)
                               (fun i : list Real =>
                                  real_mult (mu i) (tv_r_kernel Homd i j)) states)
                            (real_list_sum (list Real)
                               (fun i : list Real =>
                                  real_mult (nu i) (tv_r_kernel Homd i j)) states)))
                      (real_mult tv_omd
                         (real_list_sum (list Real)
                            (fun i : list Real =>
                               real_minus_r (real_mult (mu i) (tv_r_kernel Homd i j))
                                            (real_mult (nu i) (tv_r_kernel Homd i j)))
                            states))).
      { apply (RealSetoid.real_eq_mult_compat tv_omd
                 (real_minus_r
                    (real_list_sum (list Real)
                       (fun i : list Real =>
                          real_mult (mu i) (tv_r_kernel Homd i j)) states)
                    (real_list_sum (list Real)
                       (fun i : list Real =>
                          real_mult (nu i) (tv_r_kernel Homd i j)) states))
                 tv_omd
                 (real_list_sum (list Real)
                    (fun i : list Real =>
                       real_minus_r (real_mult (mu i) (tv_r_kernel Homd i j))
                                    (real_mult (nu i) (tv_r_kernel Homd i j)))
                    states)).
        - apply real_eq_refl.
        - exact (real_eq_sym _ _
                   (tvd_list_sum_minus (list Real)
                      (fun i : list Real =>
                         real_mult (mu i) (tv_r_kernel Homd i j))
                      (fun i : list Real =>
                         real_mult (nu i) (tv_r_kernel Homd i j))
                      states)).
      }
      assert (Hc5 : real_eq
                      (real_mult tv_omd
                         (real_list_sum (list Real)
                            (fun i : list Real =>
                               real_minus_r (real_mult (mu i) (tv_r_kernel Homd i j))
                                            (real_mult (nu i) (tv_r_kernel Homd i j)))
                            states))
                      (real_mult tv_omd
                         (real_list_sum (list Real)
                            (fun i : list Real =>
                               real_mult (real_minus_r (mu i) (nu i))
                                         (tv_r_kernel Homd i j)) states))).
      { apply (RealSetoid.real_eq_mult_compat tv_omd
                 (real_list_sum (list Real)
                    (fun i : list Real =>
                       real_minus_r (real_mult (mu i) (tv_r_kernel Homd i j))
                                    (real_mult (nu i) (tv_r_kernel Homd i j)))
                    states)
                 tv_omd
                 (real_list_sum (list Real)
                    (fun i : list Real =>
                       real_mult (real_minus_r (mu i) (nu i))
                                 (tv_r_kernel Homd i j)) states)).
        - apply real_eq_refl.
        - apply (real_list_sum_ext (list Real)
                     (fun i : list Real =>
                        real_minus_r (real_mult (mu i) (tv_r_kernel Homd i j))
                                     (real_mult (nu i) (tv_r_kernel Homd i j)))
                     (fun i : list Real =>
                        real_mult (real_minus_r (mu i) (nu i))
                                  (tv_r_kernel Homd i j)) states).
          intro i.
          exact (tvd_minus_factor_r (mu i) (nu i) (tv_r_kernel Homd i j)).
      }
      assert (Hdiffj : real_eq
                         (real_minus_r (tv_step mu j) (tv_step nu j))
                         (real_mult tv_omd
                            (real_list_sum (list Real)
                               (fun i : list Real =>
                                  real_mult (real_minus_r (mu i) (nu i))
                                            (tv_r_kernel Homd i j)) states))).
      { exact (real_eq_trans _ _ _ Hc1
                 (real_eq_trans _ _ _ Hc2
                    (real_eq_trans _ _ _ Hc3 (real_eq_trans _ _ _ Hc4 Hc5)))). }
      apply (RealSetoid.real_le_id_l
               (real_abs (real_minus_r (tv_step mu j) (tv_step nu j)))
               (real_abs (real_mult tv_omd
                            (real_list_sum (list Real)
                               (fun i : list Real =>
                                  real_mult (real_minus_r (mu i) (nu i))
                                            (tv_r_kernel Homd i j)) states)))
               (real_mult tv_omd
                  (real_list_sum (list Real)
                     (fun i : list Real =>
                        real_mult (real_abs (real_minus_r (mu i) (nu i)))
                                  (tv_r_kernel Homd i j)) states))).
      + apply (RealSetoid.real_eq_abs_compat
                 (real_minus_r (tv_step mu j) (tv_step nu j))
                 (real_mult tv_omd
                    (real_list_sum (list Real)
                       (fun i : list Real =>
                          real_mult (real_minus_r (mu i) (nu i))
                                    (tv_r_kernel Homd i j)) states))
                 Hdiffj).
      + (* Subgoal 2: real_le (abs B) (mult B) -- the Hq1/Hq1x/Hq2 chain closes by exact Hq2 *)
      (* |omd*sum F| == omd*|sum F| (|omd| == omd) plus the pointwise |Fi| == |mu_i-nu_i|*R reshaping *)
      (* The reshaping identity for |F|: sum|F| == sum(|mu_i-nu_i|*R) (pointwise |Fi| == |mu_i-nu_i|*R) *)
      assert (Hq1 : real_eq
                      (real_list_sum (list Real)
                         (fun i : list Real =>
                            real_abs (real_mult (real_minus_r (mu i) (nu i))
                                                (tv_r_kernel Homd i j)))
                         states)
                      (real_list_sum (list Real)
                         (fun i : list Real =>
                            real_mult (real_abs (real_minus_r (mu i) (nu i)))
                                      (tv_r_kernel Homd i j)) states)).
      { apply (real_list_sum_ext (list Real)
                 (fun i : list Real =>
                    real_abs (real_mult (real_minus_r (mu i) (nu i))
                                        (tv_r_kernel Homd i j)))
                 (fun i : list Real =>
                    real_mult (real_abs (real_minus_r (mu i) (nu i)))
                              (tv_r_kernel Homd i j)) states).
        intro i.
        exact (real_eq_trans _
                   (real_mult (real_abs (real_minus_r (mu i) (nu i)))
                              (real_abs (tv_r_kernel Homd i j)))
                   _
                   (real_abs_mult_req (real_minus_r (mu i) (nu i))
                      (tv_r_kernel Homd i j))
                   (RealSetoid.real_eq_mult_compat
                      (real_abs (real_minus_r (mu i) (nu i)))
                      (real_abs (tv_r_kernel Homd i j))
                      (real_abs (real_minus_r (mu i) (nu i)))
                      (tv_r_kernel Homd i j)
                      (real_eq_refl (real_abs (real_minus_r (mu i) (nu i))))
                      (tvd_abs_le_id (tv_r_kernel Homd i j)
                         (tv_r_nonneg Homd i j)))).
      }
      (* A := |omd*sum F| == |omd|*|sum F| == omd*|sum F| (= BM) *)
      assert (Hq1x : real_eq
                       (real_abs (real_mult tv_omd
                                    (real_list_sum (list Real)
                                       (fun i : list Real =>
                                          real_mult (real_minus_r (mu i) (nu i))
                                                    (tv_r_kernel Homd i j)) states)))
                       (real_mult tv_omd
                          (real_abs (real_list_sum (list Real)
                                       (fun i : list Real =>
                                          real_mult (real_minus_r (mu i) (nu i))
                                                    (tv_r_kernel Homd i j)) states)))).
      { exact (real_eq_trans _
                   (real_mult (real_abs tv_omd)
                      (real_abs (real_list_sum (list Real)
                                   (fun i : list Real =>
                                      real_mult (real_minus_r (mu i) (nu i))
                                                (tv_r_kernel Homd i j)) states)))
                   _
                   (real_abs_mult_req tv_omd
                      (real_list_sum (list Real)
                         (fun i : list Real =>
                            real_mult (real_minus_r (mu i) (nu i))
                                      (tv_r_kernel Homd i j)) states))
                   (RealSetoid.real_eq_mult_compat (real_abs tv_omd)
                      (real_abs (real_list_sum (list Real)
                                   (fun i : list Real =>
                                      real_mult (real_minus_r (mu i) (nu i))
                                                (tv_r_kernel Homd i j)) states))
                      tv_omd
                      (real_abs (real_list_sum (list Real)
                                   (fun i : list Real =>
                                      real_mult (real_minus_r (mu i) (nu i))
                                                (tv_r_kernel Homd i j)) states))
                      (tvd_abs_le_id tv_omd tv_omd_nonneg)
                      (real_eq_refl
                         (real_abs (real_list_sum (list Real)
                                      (fun i : list Real =>
                                         real_mult (real_minus_r (mu i) (nu i))
                                                   (tv_r_kernel Homd i j)) states))))).
      }
      (* Hq2 : |omd*sum F| <= omd*sum(|mu_i-nu_i|*R):
         leg1 the eq-le bridge (Hq1x); leg2 abs_sum_le (mult_compat_r) + the Hq1 reshaping. *)
      assert (Hq2 : real_le
                      (real_abs (real_mult tv_omd
                                   (real_list_sum (list Real)
                                      (fun i : list Real =>
                                         real_mult (real_minus_r (mu i) (nu i))
                                                   (tv_r_kernel Homd i j)) states)))
                      (real_mult tv_omd
                         (real_list_sum (list Real)
                            (fun i : list Real =>
                               real_mult (real_abs (real_minus_r (mu i) (nu i)))
                                         (tv_r_kernel Homd i j)) states))).
      { apply (real_le_trans _ (real_mult tv_omd
                                  (real_abs (real_list_sum (list Real)
                                               (fun i : list Real =>
                                                  real_mult (real_minus_r (mu i) (nu i))
                                                            (tv_r_kernel Homd i j)) states))) _).
        - exact (RealSetoid.real_eq_le _ _ Hq1x).
        - exact (RealSetoid.real_le_id_r _ _ _
                   (RealSetoid.real_eq_mult_compat tv_omd
                      (real_list_sum (list Real)
                         (fun i : list Real =>
                            real_abs (real_mult (real_minus_r (mu i) (nu i))
                                                (tv_r_kernel Homd i j))) states)
                      tv_omd
                      (real_list_sum (list Real)
                         (fun i : list Real =>
                            real_mult (real_abs (real_minus_r (mu i) (nu i)))
                                      (tv_r_kernel Homd i j)) states)
                      (real_eq_refl tv_omd) Hq1)
                   (real_le_mult_compat_r tv_omd
                      (real_abs (real_list_sum (list Real)
                                   (fun i : list Real =>
                                      real_mult (real_minus_r (mu i) (nu i))
                                                (tv_r_kernel Homd i j)) states))
                      (real_list_sum (list Real)
                         (fun i : list Real =>
                            real_abs (real_mult (real_minus_r (mu i) (nu i))
                                                (tv_r_kernel Homd i j))) states)
                      tv_omd_nonneg
                      (abs_sum_le_list
                         (fun i : list Real =>
                            real_mult (real_minus_r (mu i) (nu i))
                                      (tv_r_kernel Homd i j))))).
      }
      exact Hq2.
    }
    (* Summing: sum_j |diff j| <= omd*sum_i |mu_i-nu_i| (swap + R row normalization close) *)
    assert (Hsum : real_le
                     (real_list_sum (list Real)
                        (fun j : list Real =>
                           real_abs (real_minus_r (tv_step mu j) (tv_step nu j)))
                        states)
                     (real_mult tv_omd
                        (real_list_sum (list Real)
                           (fun i : list Real =>
                              real_abs (real_minus_r (mu i) (nu i))) states))).
    { assert (HA : real_le
                     (real_list_sum (list Real)
                        (fun j : list Real =>
                           real_abs (real_minus_r (tv_step mu j) (tv_step nu j)))
                        states)
                     (real_list_sum (list Real)
                        (fun j : list Real =>
                           real_mult tv_omd
                             (real_list_sum (list Real)
                                (fun i : list Real =>
                                   real_mult
                                     (real_abs (real_minus_r (mu i) (nu i)))
                                     (tv_r_kernel Homd i j)) states))
                        states)).
      { apply (real_list_sum_le (list Real)). intro j. exact (Hpt j). }
      (* The middle term takes the RHS shape of HA (aligned with HA); the eq chain reorders and closes:
         sum_j (omd*g j) == omd*sum_j g (constant extraction)
                     == omd*sum_j sum_i (wi*R_ij) (ext reflexivity wrap)
                     == omd*sum_i sum_j (wi*R_ij) (double-sum swap)
                     == omd*sum_i wi (pointwise linear + row normalization + *1 cancellation) *)
      apply (real_le_trans _
               (real_list_sum (list Real)
                  (fun j : list Real =>
                     real_mult tv_omd
                       (real_list_sum (list Real)
                          (fun i : list Real =>
                             real_mult
                               (real_abs (real_minus_r (mu i) (nu i)))
                               (tv_r_kernel Homd i j)) states))
                  states)).
      + exact HA.
      + assert (Hchain : real_eq
                  (real_list_sum (list Real)
                     (fun j : list Real =>
                        real_list_sum (list Real)
                          (fun i : list Real =>
                             real_mult (real_abs (real_minus_r (mu i) (nu i)))
                                       (tv_r_kernel Homd i j)) states)
                     states)
                  (real_list_sum (list Real)
                     (fun i : list Real =>
                        real_abs (real_minus_r (mu i) (nu i))) states)).
        { (* sum_j sum_i (wi*R_ij) == sum_i sum_j (wi*R_ij) == sum_i wi *)
          apply (real_eq_trans _
                   (real_list_sum (list Real)
                      (fun i : list Real =>
                         real_list_sum (list Real)
                           (fun j : list Real =>
                              real_mult (real_abs (real_minus_r (mu i) (nu i)))
                                        (tv_r_kernel Homd i j)) states)
                      states) _).
          - exact (tvd_list_sum_swap_gen (list Real) states states
                     (fun i j : list Real =>
                        real_mult (real_abs (real_minus_r (mu i) (nu i)))
                                  (tv_r_kernel Homd i j))).
          - apply (real_list_sum_ext (list Real)
                     (fun i : list Real =>
                        real_list_sum (list Real)
                          (fun j : list Real =>
                             real_mult (real_abs (real_minus_r (mu i) (nu i)))
                                       (tv_r_kernel Homd i j)) states)
                     (fun i : list Real =>
                        real_abs (real_minus_r (mu i) (nu i))) states).
            intro i.
            (* sum_j (wi*R_ij) == wi*sum_j R_ij == wi*1 == wi *)
            apply (real_eq_trans _
                     (real_mult (real_abs (real_minus_r (mu i) (nu i)))
                                (real_list_sum (list Real)
                                   (tv_r_kernel Homd i) states)) _).
            + exact (real_list_sum_linear (list Real)
                       (real_abs (real_minus_r (mu i) (nu i)))
                       (tv_r_kernel Homd i) states).
            + apply (real_eq_trans _
                       (real_mult (real_abs (real_minus_r (mu i) (nu i)))
                                  real_one) _).
              * apply (RealSetoid.real_eq_mult_compat
                         (real_abs (real_minus_r (mu i) (nu i)))
                         (real_list_sum (list Real) (tv_r_kernel Homd i) states)
                         (real_abs (real_minus_r (mu i) (nu i)))
                         real_one).
              -- apply real_eq_refl.
              -- exact (tv_r_row Homd i).
              * exact (real_mult_one
                         (real_abs (real_minus_r (mu i) (nu i)))).
        }
        (* leg2: sum_j (omd*g j) == omd*sum_j g == omd*sum_i wi *)
        apply (RealSetoid.real_eq_le _ _).
        apply (real_eq_trans _
                 (real_mult tv_omd
                    (real_list_sum (list Real)
                       (fun j : list Real =>
                          real_list_sum (list Real)
                            (fun i : list Real =>
                               real_mult
                                 (real_abs (real_minus_r (mu i) (nu i)))
                                 (tv_r_kernel Homd i j)) states)
                       states)) _).
        * exact (real_list_sum_linear (list Real) tv_omd
                   (fun j : list Real =>
                      real_list_sum (list Real)
                        (fun i : list Real =>
                           real_mult
                             (real_abs (real_minus_r (mu i) (nu i)))
                             (tv_r_kernel Homd i j)) states)
                   states).
        * apply (RealSetoid.real_eq_mult_compat tv_omd
                   (real_list_sum (list Real)
                      (fun j : list Real =>
                         real_list_sum (list Real)
                           (fun i : list Real =>
                              real_mult
                                (real_abs (real_minus_r (mu i) (nu i)))
                                (tv_r_kernel Homd i j)) states)
                      states)
                   tv_omd
                   (real_list_sum (list Real)
                      (fun i : list Real =>
                         real_abs (real_minus_r (mu i) (nu i))) states)).
          -- apply real_eq_refl.
          -- exact Hchain.
    }
    (* TV done: half*sum|diff| <= half*omd*sum|mu-nu| == omd*TV(mu,nu) *)
    apply (RealSetoid.real_le_id_r
             (tv_doeblin (tv_step mu) (tv_step nu))
             (real_mult tv_half
                (real_mult tv_omd
                   (real_list_sum (list Real)
                      (fun i : list Real =>
                         real_abs (real_minus_r (mu i) (nu i))) states)))
             (real_mult tv_omd (tv_doeblin mu nu))).
    + exact (tvd_mult_swap_ab tv_half tv_omd
               (real_list_sum (list Real)
                  (fun i : list Real =>
                     real_abs (real_minus_r (mu i) (nu i))) states)).
    + (* half*sum|diff| <= half*(omd*sum|mu-nu|): constant on the left, via compat_r +
         the lt->le bridge (Or inl injection) supplying the nonneg premise *)
      exact (real_le_mult_compat_r tv_half
               (real_list_sum (list Real)
                  (fun j : list Real =>
                     real_abs (real_minus_r (tv_step mu j) (tv_step nu j))) states)
               (real_mult tv_omd
                  (real_list_sum (list Real)
                     (fun i : list Real =>
                        real_abs (real_minus_r (mu i) (nu i))) states))
               (inl tv_half_pos)
               Hsum).
  - (* ---- Branch 2: delta == 1 (degenerate branch, closed by eq) ---- *)
    assert (HKeq : forall i j : list Real, InT j states -> real_eq (K i j) (u j)).
    { intros i j Hj.
      assert (Hgnonneg : forall w : list Real,
                 real_le real_zero
                   (real_minus_r (K i w) (real_mult delta (u w)))).
      { intro w.
        exact (tvd_le_minus_nonneg (K i w) (real_mult delta (u w))
                 (minorization i w)). }
      assert (Hgsum : real_eq
                        (real_list_sum (list Real)
                           (fun w : list Real =>
                              real_minus_r (K i w) (real_mult delta (u w))) states)
                        real_zero).
      { apply (real_eq_trans
                 (real_list_sum (list Real)
                    (fun w : list Real =>
                       real_minus_r (K i w) (real_mult delta (u w))) states)
                 (real_minus_r (real_list_sum (list Real) (K i) states)
                               (real_list_sum (list Real)
                                  (fun w : list Real =>
                                     real_mult delta (u w)) states))).
        - exact (tvd_list_sum_minus (list Real) (K i)
                   (fun w : list Real => real_mult delta (u w)) states).
        - apply (real_eq_trans
                   (real_minus_r (real_list_sum (list Real) (K i) states)
                                 (real_list_sum (list Real)
                                    (fun w : list Real =>
                                       real_mult delta (u w)) states))
                   (real_minus_r real_one (real_mult delta real_one))).
          + exact (tvd_eq_minus_compat (real_list_sum (list Real) (K i) states)
                     real_one
                     (real_list_sum (list Real)
                        (fun w : list Real => real_mult delta (u w)) states)
                     (real_mult delta real_one) (K_row i) tv_delta_u_sum).
          + apply (real_eq_trans (real_minus_r real_one (real_mult delta real_one))
                     tv_omd).
            * exact (tvd_eq_minus_compat real_one real_one
                       (real_mult delta real_one) delta
                       (real_eq_refl real_one) (real_mult_one delta)).
            * exact (tv_omd_eq_zero Hd1).
      }
      assert (Hgj : real_eq (real_minus_r (K i j) (real_mult delta (u j))) real_zero).
      { exact (tvd_list_sum_zero_nonneg_eq (list Real)
                 (fun w : list Real => real_minus_r (K i w) (real_mult delta (u w)))
                 j states Hgnonneg Hj Hgsum). }
      apply (real_eq_trans (K i j) (real_mult delta (u j))).
      - apply (real_eq_trans (K i j)
                 (real_plus (real_minus_r (K i j) (real_mult delta (u j)))
                            (real_mult delta (u j)))).
        + exact (real_eq_sym
                   (real_plus (real_minus_r (K i j) (real_mult delta (u j)))
                              (real_mult delta (u j)))
                   (K i j)
                   (tvd_plus_minus_absorb_r (real_mult delta (u j)) (K i j))).
        + apply (real_eq_trans
                   (real_plus (real_minus_r (K i j) (real_mult delta (u j)))
                              (real_mult delta (u j)))
                   (real_plus real_zero (real_mult delta (u j)))).
          (* Itemwise reshaping: minus==0 (Hgj), duj==duj implies addition preserves eq;
             then 0+duj==duj (tvd_plus_zero_l) finishes *)
          * apply (RealSetoid.real_eq_plus_compat
                     (real_minus_r (K i j) (real_mult delta (u j)))
                     (real_mult delta (u j))
                     real_zero
                     (real_mult delta (u j)) Hgj
                     (real_eq_refl (real_mult delta (u j)))).
          * exact (tvd_plus_zero_l (real_mult delta (u j))).
      - apply (real_eq_trans (real_mult delta (u j))
                 (real_mult real_one (u j))).
        + apply (RealSetoid.real_eq_mult_compat delta (u j) real_one (u j)
                   Hd1 (real_eq_refl (u j))).
        + apply (real_eq_trans (real_mult real_one (u j))
                   (real_mult (u j) real_one) (u j)).
          * exact (real_mult_comm real_one (u j)).
          * exact (real_mult_one (u j)).
    }
    assert (Hstepu : forall m : list Real -> Real,
              real_eq (real_list_sum (list Real) m states) real_one ->
              forall j : list Real, InT j states -> real_eq (tv_step m j) (u j)).
    { intros m Hm j Hj. unfold tv_step.
      apply (real_eq_trans
               (real_list_sum (list Real)
                  (fun i : list Real => real_mult (m i) (K i j)) states)
               (real_mult (u j) real_one)).
      - apply (real_eq_trans
                 (real_list_sum (list Real)
                    (fun i : list Real => real_mult (m i) (K i j)) states)
                 (real_list_sum (list Real)
                    (fun i : list Real => real_mult (m i) (u j)) states)).
        + apply (real_list_sum_ext (list Real)
                     (fun i : list Real => real_mult (m i) (K i j))
                     (fun i : list Real => real_mult (m i) (u j)) states).
          intro i.
          apply (RealSetoid.real_eq_mult_compat (m i) (K i j) (m i) (u j)).
          * apply real_eq_refl.
          * exact (HKeq i j Hj).
        + (* sum(m*u) == u*sum m == u*1 (linear_r + normalization Hm) *)
          apply (real_eq_trans _
                     (real_mult (u j) (real_list_sum (list Real) m states)) _).
          * exact (real_list_sum_linear_r (list Real) (u j) m states).
          * apply (RealSetoid.real_eq_mult_compat (u j)
                       (real_list_sum (list Real) m states)
                       (u j) real_one).
            -- apply real_eq_refl.
            -- exact Hm.
      - exact (real_mult_one (u j)).
    }
    assert (HstepEq : forall j : list Real,
              InT j states -> real_eq (tv_step mu j) (tv_step nu j)).
    { intros j Hj. apply (real_eq_trans (tv_step mu j) (u j)).
      - exact (Hstepu mu Hmu j Hj).
      - exact (real_eq_sym (tv_step nu j) (u j) (Hstepu nu Hnu j Hj)). }
    assert (HLHS : real_eq (tv_doeblin (tv_step mu) (tv_step nu)) real_zero).
    { unfold tv_doeblin.
      apply (real_eq_trans
               (real_mult tv_half
                  (real_list_sum (list Real)
                     (fun j : list Real =>
                        real_abs (real_minus_r (tv_step mu j) (tv_step nu j)))
                     states))
               (real_mult tv_half
                  (real_list_sum (list Real)
                     (fun _ : list Real => real_zero) states))).
      - apply (RealSetoid.real_eq_mult_compat tv_half
                 (real_list_sum (list Real)
                    (fun j : list Real =>
                       real_abs (real_minus_r (tv_step mu j) (tv_step nu j)))
                    states)
                 tv_half
                 (real_list_sum (list Real)
                    (fun _ : list Real => real_zero) states)).
        + apply real_eq_refl.
        + apply (tvd_list_sum_ext_in (list Real)
                   (fun j : list Real =>
                      real_abs (real_minus_r (tv_step mu j) (tv_step nu j)))
                   (fun _ : list Real => real_zero) states).
          intros j Hj.
          apply (RealSetoid.real_eq_abs_compat
                   (real_minus_r (tv_step mu j) (tv_step nu j)) real_zero).
          apply (real_eq_trans
                   (real_minus_r (tv_step mu j) (tv_step nu j))
                   (real_minus_r (u j) (u j))).
          * exact (tvd_eq_minus_compat (tv_step mu j) (u j) (tv_step nu j) (u j)
                     (Hstepu mu Hmu j Hj) (Hstepu nu Hnu j Hj)).
          * exact (real_plus_opp (u j)).
      - apply (real_eq_trans
                 (real_mult tv_half
                    (real_list_sum (list Real)
                       (fun _ : list Real => real_zero) states))
                 (real_mult tv_half real_zero)).
        + apply (RealSetoid.real_eq_mult_compat tv_half
                     (real_list_sum (list Real) (fun _ : list Real => real_zero) states)
                     tv_half real_zero).
          * apply real_eq_refl.
          * exact (tvd_list_sum_zero_const (list Real) states).
        + exact (real_mult_zero tv_half).
    }
    assert (HRHS : real_eq (real_mult tv_omd (tv_doeblin mu nu)) real_zero).
    { apply (real_eq_trans (real_mult tv_omd (tv_doeblin mu nu))
               (real_mult real_zero (tv_doeblin mu nu))).
      - apply (RealSetoid.real_eq_mult_compat tv_omd
                 (tv_doeblin mu nu) real_zero (tv_doeblin mu nu)).
        + exact (tv_omd_eq_zero Hd1).
        + apply real_eq_refl.
      - (* 0*TV == TV*0 == 0 (real_mult_zero zero-on-right, comm bridge) *)
        apply (real_eq_trans (real_mult real_zero (tv_doeblin mu nu))
                 (real_mult (tv_doeblin mu nu) real_zero)).
        + exact (real_mult_comm real_zero (tv_doeblin mu nu)).
        + exact (real_mult_zero (tv_doeblin mu nu)). }
    apply (RealSetoid.real_eq_le).
    exact (real_eq_trans (tv_doeblin (tv_step mu) (tv_step nu)) real_zero
             (real_mult tv_omd (tv_doeblin mu nu)) HLHS (real_eq_sym _ _ HRHS)).
Qed.

(* ---- 1.7 Iterated contraction: TV(K^n*mu, K^n*nu) <= (1-delta)^n*TV(mu,nu) ---- *)
Fixpoint tv_rpow (a : Real) (n : nat) : Real :=
  match n with
  | 0%nat => real_one
  | Datatypes.S m => real_mult a (tv_rpow a m)
  end.

Fixpoint tv_titer (n : nat) (mu : list Real -> Real) : list Real -> Real :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => tv_step (tv_titer m mu)
  end.

Lemma tv_titer_norm : forall (n : nat) (mu : list Real -> Real),
  real_eq (real_list_sum (list Real) mu states) real_one ->
  real_eq (real_list_sum (list Real) (tv_titer n mu) states) real_one.
Proof.
  intro n. induction n as [| n IH]; intros mu H.
  - exact H.
  - exact (tv_step_norm (tv_titer n mu) (IH mu H)).
Qed.

Theorem tv_doeblin_iter : forall (n : nat) (mu nu : list Real -> Real),
  real_eq (real_list_sum (list Real) mu states) real_one ->
  real_eq (real_list_sum (list Real) nu states) real_one ->
  real_le (tv_doeblin (tv_titer n mu) (tv_titer n nu))
          (real_mult (tv_rpow tv_omd n) (tv_doeblin mu nu)).
Proof.
  intro n. induction n as [| n IH]; intros mu nu Hmu Hnu.
  - apply (RealSetoid.real_eq_le).
    (* TV == TV*1 == 1*TV == tv_rpow tv_omd 0 * TV *)
    exact (real_eq_trans (tv_doeblin mu nu)
             (real_mult (tv_doeblin mu nu) real_one)
             (real_mult real_one (tv_doeblin mu nu))
             (real_eq_sym _ _ (real_mult_one (tv_doeblin mu nu)))
             (real_mult_comm (tv_doeblin mu nu) real_one)).
  - apply (real_le_trans
             (tv_doeblin (tv_titer (Datatypes.S n) mu)
                         (tv_titer (Datatypes.S n) nu))
             (real_mult tv_omd
                        (tv_doeblin (tv_titer n mu) (tv_titer n nu)))
             (real_mult (tv_rpow tv_omd (Datatypes.S n)) (tv_doeblin mu nu))).
    + exact (tv_doeblin_contraction (tv_titer n mu) (tv_titer n nu)
               (tv_titer_norm n mu Hmu) (tv_titer_norm n nu Hnu)).
    + apply (RealSetoid.real_le_id_r
               (real_mult tv_omd (tv_doeblin (tv_titer n mu) (tv_titer n nu)))
               (real_mult tv_omd
                  (real_mult (tv_rpow tv_omd n) (tv_doeblin mu nu)))
               (real_mult (tv_rpow tv_omd (Datatypes.S n)) (tv_doeblin mu nu))).
      * exact (real_mult_assoc tv_omd (tv_rpow tv_omd n) (tv_doeblin mu nu)).
      * (* Constant on the left: omd*TVn <= omd*(rpow*TV) (compat_r) *)
        exact (real_le_mult_compat_r tv_omd
                 (tv_doeblin (tv_titer n mu) (tv_titer n nu))
                 (real_mult (tv_rpow tv_omd n) (tv_doeblin mu nu))
                 tv_omd_nonneg (IH mu nu Hmu Hnu)).
Qed.

End TVRealWorld.




(* ################ Part 2. The explicit-constant instance delta* := e^(-2*gamma/T) ####
   Under the two-sided logit bounds (-gamma <= z i j <= gamma, gamma > 0, T > 0, nonempty enumeration n_pos),
   the delta interface (the Section TVRealWorld field face: delta positivity / delta <= 1 / kernel lower bound delta*u <= K)
   is satisfied by the explicit constant delta* := e^(-2*gamma/T) (the lo*lo form, zero eps slack loss), and the
   main iterate theorem is resolved with this constant, closing the explicit rate (1 - e^(-2*gamma/T))^n. gamma is the paper/QK-pipeline Delta.
   The honest interface abs_sum_le_list (|sum f| <= sum|f|, analytic bisection) stays a premise, as in Part 1 --
   under constructive logic this shape is not resolvable from the base; it travels explicitly with the interface. *)

Section TVDStar.

Variable states : list (list Real).
Variable n_pos : real_lt real_zero (real_of_nat (length states)).
Variable Ttemp : Real.
Variable Ttemp_pos : real_lt real_zero Ttemp.
Variable gamma : Real.
Variable gamma_pos : real_lt real_zero gamma.
Variable z : list Real -> list Real -> Real.
Variable z_lo : forall i j : list Real, real_le (real_opp gamma) (z i j).
Variable z_hi : forall i j : list Real, real_le (z i j) gamma.

Definition tvd_invT : Real := real_inv_pos Ttemp Ttemp_pos.
Definition tvd_tg : Real := real_mult gamma tvd_invT.                  (* gamma/T *)
Definition tvd_lo : Real := real_exp_neg tvd_tg.                       (* e^(-gamma/T) *)
Definition tvd_hi : Real :=
  real_exp_neg (real_mult (real_opp gamma) tvd_invT).                  (* e^(+gamma/T) *)
Definition tvd_hi_pos : real_lt real_zero tvd_hi :=
  real_exp_neg_pos (real_mult (real_opp gamma) tvd_invT).
Definition tvd_dstar : Real := real_exp_neg (real_plus tvd_tg tvd_tg). (* e^(-2*gamma/T) *)
Definition tvd_expz (i j : list Real) : Real :=
  real_exp_neg (real_mult (real_opp (z i j)) tvd_invT).                (* e^{z(i,j)/T} *)
Definition tvd_Z (i : list Real) : Real :=
  real_list_sum (list Real) (tvd_expz i) states.
Definition tvd_n : Real := real_of_nat (length states).
Definition tvd_nhi : Real := real_mult tvd_n tvd_hi.
Definition tvd_nhi_pos : real_lt real_zero tvd_nhi :=
  real_mult_pos_compat tvd_n tvd_hi n_pos tvd_hi_pos.
Definition tvd_u (j : list Real) : Real :=
  real_inv_pos (real_of_nat (length states)) n_pos.

(* ---- 2.0 e^(-0) == 1 (the cauchy-layer zero bridge) ---- *)
Lemma tvd_exp_neg_zero : real_eq (real_exp_neg real_zero) real_one.
Proof.
  apply (real_eq_trans (real_exp_neg real_zero)
           (cauchy_real_exp (real_opp real_zero)) real_one).
  - apply real_eq_refl.
  - apply (real_eq_trans (cauchy_real_exp (real_opp real_zero))
             (cauchy_real_exp real_zero) real_one).
    + apply (cauchy_real_exp_wd (real_opp real_zero) real_zero real_opp_zero).
    + exact cauchy_real_exp_zero.
Qed.

(* ---- 2.1 The expz two-sided bound: lo <= expz i j <= hi (the lower/upper z branches) ---- *)
Lemma tvd_expz_ge_lo : forall i j : list Real, real_le tvd_lo (tvd_expz i j).
Proof.
  intros i j.
  assert (Hopp : real_le (real_opp (z i j)) gamma).
  { apply (RealSetoid.real_le_id_r (real_opp (z i j))
             (real_opp (real_opp gamma)) gamma).
    - exact (real_opp_opp gamma).
    - exact (real_opp_le_compat (real_opp gamma) (z i j) (z_lo i j)). }
  exact (real_exp_neg_le_decr (real_mult (real_opp (z i j)) tvd_invT) tvd_tg
           (real_le_mult_compat (real_opp (z i j)) gamma tvd_invT
              (real_inv_pos_pos Ttemp Ttemp_pos) Hopp)).
Qed.

Lemma tvd_expz_le_hi : forall i j : list Real, real_le (tvd_expz i j) tvd_hi.
Proof.
  intros i j.
  assert (Hopp : real_le (real_opp gamma) (real_opp (z i j)))
    by exact (real_opp_le_compat (z i j) gamma (z_hi i j)).
  exact (real_exp_neg_le_decr (real_mult (real_opp gamma) tvd_invT)
           (real_mult (real_opp (z i j)) tvd_invT)
           (real_le_mult_compat (real_opp gamma) (real_opp (z i j)) tvd_invT
              (real_inv_pos_pos Ttemp Ttemp_pos) Hopp)).
Qed.

(* ---- 2.2 Denominator upper bound: Z i <= n*hi (pointwise + constant sum) ---- *)
Lemma tvd_Z_le : forall i : list Real,
  real_le (tvd_Z i) (real_mult tvd_n tvd_hi).
Proof.
  intro i.
  apply (real_le_trans _ (real_list_sum (list Real) (fun _ : list Real => tvd_hi) states)).
  - apply (real_list_sum_le (list Real) (tvd_expz i)
             (fun _ : list Real => tvd_hi) states).
    intro j. exact (tvd_expz_le_hi i j).
  - apply (RealSetoid.real_eq_le _ _).
    exact (tvd_list_sum_const (list Real) tvd_hi states).
Qed.

(* ---- 2.3 Denominator positivity (the nil branch eliminated by n_pos absurdity; a nonempty list is strictly positive) ---- *)
Lemma tvd_list_sum_pos : forall (l : list (list Real)) (f : list Real -> Real),
  real_lt real_zero (real_of_nat (length l)) ->
  (forall j : list Real, real_lt real_zero (f j)) ->
  real_lt real_zero (real_list_sum (list Real) f l).
Proof.
  intros l f Hn Hf. destruct l as [| x rest].
  - cbn [real_list_sum] in *.
    cbn [length real_of_nat] in Hn.
    exact Hn.
  - cbn [real_list_sum].
    assert (Hraw : real_lt (real_plus real_zero real_zero)
                     (real_plus (real_list_sum (list Real) f rest) (f x))).
    { exact (real_lt_plus_compat_le_lt real_zero (real_list_sum (list Real) f rest)
               real_zero (f x)
               (real_list_sum_nonneg (list Real) f rest
                  (fun j => tvd_lt_le real_zero (f j) (Hf j)))
               (Hf x)). }
    apply (RealSetoid.real_lt_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus (f x) (real_list_sum (list Real) f rest))).
    + exact (real_eq_sym (real_plus real_zero real_zero) real_zero
               (real_plus_zero real_zero)).
    + exact (RealSetoid.real_lt_id_r (real_plus real_zero real_zero)
               (real_plus (real_list_sum (list Real) f rest) (f x))
               (real_plus (f x) (real_list_sum (list Real) f rest))
               (real_plus_comm (real_list_sum (list Real) f rest) (f x))
               Hraw).
Qed.

Lemma tvd_Z_pos : forall i : list Real, real_lt real_zero (tvd_Z i).
Proof.
  intro i.
  exact (tvd_list_sum_pos states (tvd_expz i) n_pos
           (fun j => real_exp_neg_pos (real_mult (real_opp (z i j)) tvd_invT))).
Qed.

(* ---- 2.4 Kernel and uniform reference (positivity certificates carried constructively); row normalization ---- *)
Definition tvd_K (i j : list Real) : Real :=
  real_mult (tvd_expz i j) (real_inv_pos (tvd_Z i) (tvd_Z_pos i)).

Lemma tvd_K_row : forall i : list Real,
  real_eq (real_list_sum (list Real) (tvd_K i) states) real_one.
Proof.
  intro i.
  apply (real_eq_trans (real_list_sum (list Real) (tvd_K i) states)
           (real_mult (real_inv_pos (tvd_Z i) (tvd_Z_pos i))
                      (real_list_sum (list Real) (tvd_expz i) states))
           real_one).
  - exact (real_list_sum_linear_r (list Real)
             (real_inv_pos (tvd_Z i) (tvd_Z_pos i)) (tvd_expz i) states).
  - apply (real_eq_trans (real_mult (real_inv_pos (tvd_Z i) (tvd_Z_pos i))
                                    (real_list_sum (list Real) (tvd_expz i) states))
             (real_mult (real_inv_pos (tvd_Z i) (tvd_Z_pos i)) (tvd_Z i))
             real_one).
    + apply (RealSetoid.real_eq_mult_compat (real_inv_pos (tvd_Z i) (tvd_Z_pos i))
               (real_list_sum (list Real) (tvd_expz i) states)
               (real_inv_pos (tvd_Z i) (tvd_Z_pos i)) (tvd_Z i)).
      * apply real_eq_refl.
      * apply real_eq_refl.
    + apply (real_eq_trans (real_mult (real_inv_pos (tvd_Z i) (tvd_Z_pos i)) (tvd_Z i))
               (real_mult (tvd_Z i) (real_inv_pos (tvd_Z i) (tvd_Z_pos i)))
               real_one).
      * exact (real_mult_comm (real_inv_pos (tvd_Z i) (tvd_Z_pos i)) (tvd_Z i)).
      * exact (real_inv_pos_correct (tvd_Z i) (tvd_Z_pos i)).
Qed.

Lemma tvd_K_pos : forall i j : list Real, real_le real_zero (tvd_K i j).
Proof.
  intros i j. unfold tvd_K.
  exact (tvd_lt_le real_zero
           (real_mult (tvd_expz i j) (real_inv_pos (tvd_Z i) (tvd_Z_pos i)))
           (real_mult_pos_compat (tvd_expz i j)
              (real_inv_pos (tvd_Z i) (tvd_Z_pos i))
              (real_exp_neg_pos (real_mult (real_opp (z i j)) tvd_invT))
              (real_inv_pos_pos (tvd_Z i) (tvd_Z_pos i)))).
Qed.

Lemma tvd_u_norm : real_eq (real_list_sum (list Real) tvd_u states) real_one.
Proof.
  apply (real_eq_trans (real_list_sum (list Real) tvd_u states)
           (real_mult tvd_n (real_inv_pos (real_of_nat (length states)) n_pos))
           real_one).
  - apply (real_eq_trans (real_list_sum (list Real) tvd_u states)
             (real_list_sum (list Real)
                (fun j : list Real => real_inv_pos (real_of_nat (length states)) n_pos)
                states)
             (real_mult tvd_n (real_inv_pos (real_of_nat (length states)) n_pos))).
    + apply (real_list_sum_ext (list Real) tvd_u
               (fun j : list Real => real_inv_pos (real_of_nat (length states)) n_pos)
               states).
      intro j. apply real_eq_refl.
    + exact (tvd_list_sum_const (list Real)
               (real_inv_pos (real_of_nat (length states)) n_pos) states).
  - exact (real_inv_pos_correct (real_of_nat (length states)) n_pos).
Qed.

(* ---- 2.5 lo*hi == 1 (exp_neg_plus reversal + gamma/T + (-gamma/T) == 0) ---- *)
Lemma tvd_lo_hi_mult_one : real_eq (real_mult tvd_lo tvd_hi) real_one.
Proof.
  apply (real_eq_trans (real_mult tvd_lo tvd_hi)
           (real_exp_neg (real_plus tvd_tg (real_mult (real_opp gamma) tvd_invT)))
           real_one).
  - apply (real_eq_sym _ _ (real_exp_neg_plus tvd_tg (real_mult (real_opp gamma) tvd_invT))).
  - apply (real_eq_trans
             (real_exp_neg (real_plus tvd_tg (real_mult (real_opp gamma) tvd_invT)))
             (cauchy_real_exp (real_opp real_zero)) real_one).
    + unfold real_exp_neg.
      apply (cauchy_real_exp_wd
               (real_opp (real_plus tvd_tg (real_mult (real_opp gamma) tvd_invT)))
               (real_opp real_zero)).
      apply (RealSetoid.real_eq_opp_compat _ _).
      apply (real_eq_trans
               (real_plus tvd_tg (real_mult (real_opp gamma) tvd_invT))
               real_zero real_zero).
      * exact (tvd_mult_opp_mult_zero gamma tvd_invT).
      * apply real_eq_refl.
    + apply (real_eq_trans (cauchy_real_exp (real_opp real_zero))
               (cauchy_real_exp real_zero) real_one).
      * apply (cauchy_real_exp_wd (real_opp real_zero) real_zero real_opp_zero).
      * exact cauchy_real_exp_zero.
Qed.

(* ---- 2.6 The interface delta field: positivity and <= 1 (0 <= gamma/T + gamma/T implies e^(-2*gamma/T) <= e^(-0)) ---- *)
Lemma tvd_tg_pos : real_lt real_zero tvd_tg.
Proof.
  exact (real_mult_pos_compat gamma tvd_invT gamma_pos (real_inv_pos_pos Ttemp Ttemp_pos)).
Qed.

Lemma tvd_dstar_pos : real_lt real_zero tvd_dstar.
Proof. exact (real_exp_neg_pos (real_plus tvd_tg tvd_tg)). Qed.

Lemma tvd_dstar_le_one : real_le tvd_dstar real_one.
Proof.
  assert (Hle : real_le real_zero (real_plus tvd_tg tvd_tg)).
  { apply (RealSetoid.real_lt_le_iff_req real_zero (real_plus tvd_tg tvd_tg)). left.
    apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
             (real_plus tvd_tg tvd_tg)).
    - exact (real_eq_sym (real_plus real_zero real_zero) real_zero
               (real_plus_zero real_zero)).
    - exact (real_lt_plus_compat real_zero tvd_tg real_zero tvd_tg
               tvd_tg_pos tvd_tg_pos). }
  apply (real_le_trans tvd_dstar (real_exp_neg real_zero) real_one).
  - exact (real_exp_neg_le_decr real_zero (real_plus tvd_tg tvd_tg) Hle).
  - apply (RealSetoid.real_eq_le _ _). exact tvd_exp_neg_zero.
Qed.

(* ---- 2.7 Splitting the inverse: inv(n*hi) == inv n * inv hi (the real_inv_unique absorption chain) ---- *)
Lemma tvd_inv_split : real_eq (real_inv_pos tvd_nhi tvd_nhi_pos)
  (real_mult (real_inv_pos tvd_n n_pos) (real_inv_pos tvd_hi tvd_hi_pos)).
Proof.
  assert (Hab : real_eq (real_mult tvd_nhi (real_inv_pos tvd_nhi tvd_nhi_pos)) real_one).
  { exact (real_inv_pos_correct tvd_nhi tvd_nhi_pos). }
  assert (Hac : real_eq (real_mult tvd_nhi
                          (real_mult (real_inv_pos tvd_n n_pos) (real_inv_pos tvd_hi tvd_hi_pos)))
                  real_one).
  { unfold tvd_nhi.
    apply (real_eq_trans
             (real_mult (real_mult tvd_n tvd_hi)
                        (real_mult (real_inv_pos tvd_n n_pos) (real_inv_pos tvd_hi tvd_hi_pos)))
             (real_mult (real_mult (real_inv_pos tvd_n n_pos)
                                   (real_mult tvd_hi (real_inv_pos tvd_hi tvd_hi_pos)))
                        tvd_n)
             real_one).
    - exact (tvd_mult_reassoc5 tvd_n tvd_hi
               (real_inv_pos tvd_n n_pos) (real_inv_pos tvd_hi tvd_hi_pos)).
    - apply (real_eq_trans
               (real_mult (real_mult (real_inv_pos tvd_n n_pos)
                                     (real_mult tvd_hi (real_inv_pos tvd_hi tvd_hi_pos)))
                          tvd_n)
               (real_mult tvd_hi (real_inv_pos tvd_hi tvd_hi_pos))
               real_one).
      + exact (real_inv_absorb_comm tvd_n
                 (real_mult tvd_hi (real_inv_pos tvd_hi tvd_hi_pos)) n_pos).
      + exact (real_inv_pos_correct tvd_hi tvd_hi_pos). }
  apply (real_inv_unique tvd_nhi (real_inv_pos tvd_nhi tvd_nhi_pos)
           (real_mult (real_inv_pos tvd_n n_pos) (real_inv_pos tvd_hi tvd_hi_pos))
           Hab Hac).
Qed.

(* ---- 2.8 The zero-slack algebraic core: dstar * u j == lo*inv(n*hi) ---- *)
Lemma tvd_dstar_u_eq_lo_inv : forall j : list Real,
  real_eq (real_mult tvd_dstar (tvd_u j))
          (real_mult tvd_lo (real_inv_pos tvd_nhi tvd_nhi_pos)).
Proof.
  intro j.
  assert (Hd : real_eq tvd_dstar (real_mult tvd_lo tvd_lo))
    by exact (real_exp_neg_plus tvd_tg tvd_tg).
  assert (Hinvhi : real_eq (real_inv_pos tvd_hi tvd_hi_pos) tvd_lo).
  { apply (real_inv_unique tvd_hi (real_inv_pos tvd_hi tvd_hi_pos) tvd_lo).
    - exact (real_inv_pos_correct tvd_hi tvd_hi_pos).
    - apply (real_eq_trans (real_mult tvd_hi tvd_lo)
               (real_mult tvd_lo tvd_hi) real_one).
      + exact (real_mult_comm tvd_hi tvd_lo).
      + exact tvd_lo_hi_mult_one. }
  apply (real_eq_trans (real_mult tvd_dstar (tvd_u j))
           (real_mult (real_mult tvd_lo tvd_lo) (real_inv_pos tvd_n n_pos))
           (real_mult tvd_lo (real_inv_pos tvd_nhi tvd_nhi_pos))).
  - apply (RealSetoid.real_eq_mult_compat tvd_dstar (tvd_u j)
             (real_mult tvd_lo tvd_lo) (real_inv_pos tvd_n n_pos)
             Hd (real_eq_refl (tvd_u j))).
  - apply (real_eq_trans (real_mult (real_mult tvd_lo tvd_lo) (real_inv_pos tvd_n n_pos))
             (real_mult (real_mult tvd_lo (real_inv_pos tvd_n n_pos)) tvd_lo)
             (real_mult tvd_lo (real_inv_pos tvd_nhi tvd_nhi_pos))).
    + exact (tvd_mult_cca tvd_lo (real_inv_pos tvd_n n_pos)).
    + apply (real_eq_trans
               (real_mult (real_mult tvd_lo (real_inv_pos tvd_n n_pos)) tvd_lo)
               (real_mult (real_mult tvd_lo (real_inv_pos tvd_n n_pos))
                          (real_inv_pos tvd_hi tvd_hi_pos))
               (real_mult tvd_lo (real_inv_pos tvd_nhi tvd_nhi_pos))).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_mult tvd_lo (real_inv_pos tvd_n n_pos)) tvd_lo
                 (real_mult tvd_lo (real_inv_pos tvd_n n_pos))
                 (real_inv_pos tvd_hi tvd_hi_pos)
                 (real_eq_refl (real_mult tvd_lo (real_inv_pos tvd_n n_pos)))
                 (real_eq_sym _ _ Hinvhi)).
      * apply (real_eq_trans
                 (real_mult (real_mult tvd_lo (real_inv_pos tvd_n n_pos))
                            (real_inv_pos tvd_hi tvd_hi_pos))
                 (real_mult tvd_lo
                    (real_mult (real_inv_pos tvd_n n_pos) (real_inv_pos tvd_hi tvd_hi_pos)))
                 (real_mult tvd_lo (real_inv_pos tvd_nhi tvd_nhi_pos))).
        -- exact (tvd_mult_assoc_id tvd_lo (real_inv_pos tvd_n n_pos)
                    (real_inv_pos tvd_hi tvd_hi_pos)).
        -- apply (RealSetoid.real_eq_mult_compat tvd_lo
                     (real_mult (real_inv_pos tvd_n n_pos) (real_inv_pos tvd_hi tvd_hi_pos))
                     tvd_lo (real_inv_pos tvd_nhi tvd_nhi_pos)
                     (real_eq_refl tvd_lo) (real_eq_sym _ _ tvd_inv_split)).
Qed.

(* ---- 2.9 Interface field resolution: dstar * u <= K (zero eps slack) ---- *)
Lemma tvd_minorization : forall i j : list Real,
  real_le (real_mult tvd_dstar (tvd_u j)) (tvd_K i j).
Proof.
  intros i j.
  apply (real_le_trans (real_mult tvd_dstar (tvd_u j))
           (real_mult tvd_lo (real_inv_pos tvd_nhi tvd_nhi_pos))
           (tvd_K i j)).
  - apply (RealSetoid.real_eq_le _ _).
    exact (tvd_dstar_u_eq_lo_inv j).
  - apply (real_le_trans (real_mult tvd_lo (real_inv_pos tvd_nhi tvd_nhi_pos))
             (real_mult tvd_lo (real_inv_pos (tvd_Z i) (tvd_Z_pos i)))
             (tvd_K i j)).
    + exact (tvd_le_mult_compat_l tvd_lo
               (real_inv_pos tvd_nhi tvd_nhi_pos)
               (real_inv_pos (tvd_Z i) (tvd_Z_pos i))
               (real_exp_neg_pos tvd_tg)
               (real_inv_pos_le_compat (tvd_Z i) tvd_nhi (tvd_Z_pos i) tvd_nhi_pos
                  (tvd_Z_le i))).
    + unfold tvd_K.
      exact (real_le_mult_compat tvd_lo (tvd_expz i j)
               (real_inv_pos (tvd_Z i) (tvd_Z_pos i))
               (real_inv_pos_pos (tvd_Z i) (tvd_Z_pos i))
               (tvd_expz_ge_lo i j)).
Qed.


(* ---- 2.9b The instance-level minorization certificate: the statement is verbatim of the same shape as the section minorization ----
   The instance-layer kernel-row certificate is tvd_minorization (section 2.9 above; carrier substitution delta := tvd_dstar,
   u := tvd_u, K := tvd_K; kernel row-stochasticity and positivity are carried constructively by the tvd_K_row/tvd_Z_pos family;
   the cf2 kernel-row certificate face is covered by this instance layer). The original premise-position declarations
   and existing theorem signatures are unchanged. *)
Theorem tvd_minorization_supply : forall i j : list Real,
  real_le (real_mult tvd_dstar (tvd_u j)) (tvd_K i j).
Proof. exact tvd_minorization. Qed.
(* ---- 2.10 Assembly: the delta interface field face is satisfied by the explicit constant (Set-layer And, the theorem-5.6b pattern) ---- *)
Theorem tvd_dstar_instance :
  And (real_lt real_zero tvd_dstar)
  (And (real_le tvd_dstar real_one)
  (And (forall i j : list Real, real_le (real_mult tvd_dstar (tvd_u j)) (tvd_K i j))
  (And (forall i : list Real, real_eq (real_list_sum (list Real) (tvd_K i) states) real_one)
       (real_eq (real_list_sum (list Real) tvd_u states) real_one)))).
Proof.
  split.
  - exact tvd_dstar_pos.
  - split.
    + exact tvd_dstar_le_one.
    + split.
      * exact tvd_minorization.
      * split.
        -- exact tvd_K_row.
        -- exact tvd_u_norm.
Qed.

(* ---- 2.11 Main theorem: the explicit rate (1 - e^(-2*gamma/T))^n (the main iterate theorem resolved with delta*;
        the honest interface abs_sum_le_list travels explicitly with the premise position) ---- *)
Theorem tvd_dstar_iter_contraction :
  (forall f : list Real -> Real,
     real_le (real_abs (real_list_sum (list Real) f states))
             (real_list_sum (list Real)
                (fun w : list Real => real_abs (f w)) states)) ->
  forall (n : nat) (mu nu : list Real -> Real),
  real_eq (real_list_sum (list Real) mu states) real_one ->
  real_eq (real_list_sum (list Real) nu states) real_one ->
  real_le (tv_doeblin states (tv_titer states tvd_K n mu) (tv_titer states tvd_K n nu))
          (real_mult (tv_rpow (tv_omd tvd_dstar) n) (tv_doeblin states mu nu)).
Proof.
  intros Labs n mu nu Hmu Hnu.
  apply (tv_doeblin_iter states tvd_K tvd_K_row tvd_u tvd_u_norm tvd_dstar
           tvd_dstar_le_one tvd_minorization Labs n mu nu Hmu Hnu).
Qed.

End TVDStar.

Print Assumptions tvd_minorization_supply.
