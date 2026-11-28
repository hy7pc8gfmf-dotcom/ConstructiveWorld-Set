(* ========================================================================== *)
(* Module  : abl_attn_step_calc                                              *)
(* Mission. Step witnesses for a Doeblin-type contraction mixing rate.       *)
(*   (1) nat face: a fuel-bounded fixed-point enumerator for the geometric   *)
(*   decay x -> ceil(kappa*x), kappa = p/q (0 < p, 0 < q), stopping at the   *)
(*   first value strictly below budget e, with strict-stop correctness and   *)
(*   the exact face x*p^N < e*q^N; (2) real face: the archimedean step       *)
(*   count for a0*kappa^N < eps (explicit premise certificate), its TV       *)
(*   mixing modulus as a sigT carrier; (3) real-face bridges: power laws,    *)
(*   inverse uniqueness, the nat-to-real monotone embedding, and the         *)
(*   rational-data correctness of the enumerator (le-face budget, for        *)
(*   kappa = p/q and for a direct omd == p/q certificate).                   *)
(* Dependencies. S01_BaseRing (Id/And/NatLe, RealInterface(Enhanced),        *)
(*   StateSpace, SumOver, order-field premises), S02_CauchyComplete,         *)
(*   S03_QExp, S04_RealExpLogConv (r_pow, r_pow_pos, r_pow_dec_iter,         *)
(*   nat_to_R), Arch_PA_02 (nat_to_R_mult_hom), AttnDoeblin (u_titer,        *)
(*   u_tv_iter; Required without Import), S06_DiffSamplingGibbs (tv_dist,    *)
(*   qualified); Stdlib Arith/Lia.                                           *)
(* References. Main-library module abl_attn_step_calc (item names carried    *)
(*   verbatim); the boolean-decision nat-lt face mirrors the landed NatLe    *)
(*   (S01_BaseRing) and lw5n_NatLt (LW5SepComplexity) conventions.           *)
(* Constructivity. Zero Prop statement faces: real-face order atoms are the  *)
(*   interface's Set-valued families (lt/le : R -> R -> Set); nat            *)
(*   inequalities are carried by NatLe and the local asc_natlt face (Id      *)
(*   (Nat.ltb .) true, the nat twin of the QltT/QeqT family); every sigT     *)
(*   carrier (termination certificate, archimedean step, mixing modulus)    *)
(*   embeds zero Prop components; all items end Defined, zero Qed; Prop     *)
(*   reasoning stays inside proof bodies; vm_compute only at the pin.        *)
(* Build. rocq c -native-compiler no -q -Q <Set Live root> "" single shot.   *)
(* ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import Arch_PA_02.
Require AttnDoeblin.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Part 2: the nat fixed-point enumerator for geometric decay    *)
(*   (true Fixpoint, strict-stop face). The contraction rate     *)
(*   omd := 1 - delta is carried by the common fixed-point scale *)
(*   kappa := p/q (0 < p, 0 < q); the enumerator counts the      *)
(*   first strict fall below the budget e.                       *)
(* ============================================================ *)

(* Set-carried strict order on nat: the boolean decision identity
   (same convention as NatLe, the nat twin of QltT). *)
Definition asc_natlt (n m : nat) : Set := Id (Nat.ltb n m) true.

(* Lift: Prop strict order to the boolean decision certificate. *)
Definition asc_natlt_intro (a b : nat) (H : (a < b)%nat) : asc_natlt a b.
Proof.
  unfold asc_natlt. destruct (Nat.ltb a b) eqn:E.
  - apply id_refl.
  - exfalso. apply (proj1 (Nat.ltb_ge a b)) in E. lia.
Defined.

(* Drop: read the Prop strict order out of the certificate. *)
Definition asc_natlt_elim (a b : nat) (Hc : asc_natlt a b) : (a < b)%nat :=
  proj1 (Nat.ltb_lt a b) (id_eq_SI bool (Nat.ltb a b) true Hc).

(* Leibniz equality into the Set identity face (mirror of id_eq_SI). *)
Definition asc_id_of_eq {A : Set} {x y : A} (H : x = y) : Id x y.
Proof. destruct H. apply id_refl. Defined.

(* Transport of the strict certificate along an identity. *)
Definition asc_natlt_transport {a b e : nat} (p : Id a b) (Hc : asc_natlt a e)
  : asc_natlt b e.
Proof. destruct p. exact Hc. Defined.

(* Ceiling integer division: ceil(a/q) := (a + q - 1) / q for q >= 1;
   the upward rounding keeps the product bound on the safe side. *)
Definition asc_ceil_div (a q : nat) : nat := Nat.div (a + q - 1) q.

Theorem asc_ceil_div_le : forall a q,
  asc_natlt 0 q -> NatLe a (asc_ceil_div a q * q).
Proof.
  intros a q Hq.
  pose proof (asc_natlt_elim 0 q Hq) as Hq'.
  unfold asc_ceil_div.
  pose proof (Nat.div_mod_eq (a + q - 1) q) as Hdm.
  pose proof (Nat.mod_upper_bound (a + q - 1) q (proj2 (Nat.neq_0_lt_0 q) Hq')) as Hmb.
  apply (NatLe_lift a (Nat.div (a + q - 1) q * q)).
  lia.
Defined.

(* One decay step: x maps to ceil(x * p / q) (the fixed-point multiply
   step of kappa = p/q). *)
Definition asc_iter (p q x : nat) : nat := asc_ceil_div (x * p) q.

Theorem asc_iter_step_bound : forall p q x,
  asc_natlt 0 q -> NatLe (x * p) (asc_iter p q x * q).
Proof.
  intros p q x Hq. unfold asc_iter.
  exact (asc_ceil_div_le (x * p) q Hq).
Defined.

(* Iterated decay: the k-fold composite of asc_iter (the ceiling face of
   the geometric sequence). *)
Fixpoint asc_pow_iter (p q x k : nat) : nat :=
  match k with
  | O => x
  | Datatypes.S k' => asc_iter p q (asc_pow_iter p q x k')
  end.

(* Composite commutation: one step then k iterates equals k iterates then
   one step (the same S+1-fold composite). *)
Theorem asc_pow_iter_comm : forall p q x k,
  Id (asc_pow_iter p q (asc_iter p q x) k) (asc_iter p q (asc_pow_iter p q x k)).
Proof.
  intros p q x k. induction k as [| k IH].
  - exact id_refl.
  - simpl. exact (id_cong (fun w => asc_iter p q w) IH).
Defined.

(* Exact-face invariant: the ceiling values cover the exact geometric
   value, x * p^k <= iter^k(x) * q^k. *)
Theorem asc_pow_iter_exact_ge : forall p q x k,
  asc_natlt 0 p -> asc_natlt 0 q ->
  NatLe (x * p ^ k) (asc_pow_iter p q x k * q ^ k).
Proof.
  intros p q x k Hp Hq.
  pose proof (asc_natlt_elim 0 p Hp) as Hp'.
  pose proof (asc_natlt_elim 0 q Hq) as Hq'.
  induction k as [| k IH].
  - apply (NatLe_lift _ _). simpl. lia.
  - apply (NatLe_lift _ _).
    pose proof (NatLe_drop (x * p ^ k) (asc_pow_iter p q x k * q ^ k) IH) as IH'.
    simpl.
    pose proof (asc_iter_step_bound p q (asc_pow_iter p q x k) Hq) as Hstep.
    pose proof (NatLe_drop (asc_pow_iter p q x k * p)
                  (asc_iter p q (asc_pow_iter p q x k) * q) Hstep) as Hstep'.
    apply (Nat.le_trans _ (asc_pow_iter p q x k * q ^ k * p)).
    + rewrite (Nat.mul_comm p (p ^ k)).
      rewrite (Nat.mul_assoc x (p ^ k) p).
      apply (Nat.mul_le_mono_r _ _ p). exact IH'.
    + rewrite <- (Nat.mul_assoc (asc_pow_iter p q x k) (q ^ k) p).
      rewrite (Nat.mul_comm (q ^ k) p).
      rewrite (Nat.mul_assoc (asc_pow_iter p q x k) p (q ^ k)).
      apply (Nat.le_trans _ (asc_iter p q (asc_pow_iter p q x k) * q * q ^ k)).
      * apply (Nat.mul_le_mono_r _ _ (q ^ k)). exact Hstep'.
      * rewrite (Nat.mul_assoc (asc_iter p q (asc_pow_iter p q x k)) q (q ^ k)).
        apply (Nat.le_refl _).
Defined.

(* q^k positivity (nat face, boolean decision certificate). *)
Theorem asc_pow_pos : forall q k, asc_natlt 0 q -> asc_natlt 0 (q ^ k).
Proof.
  intros q k Hq. induction k as [| k IH].
  - apply (asc_natlt_intro 0 1). lia.
  - pose proof (asc_natlt_elim 0 q Hq) as Hq'.
    pose proof (asc_natlt_elim 0 (q ^ k) IH) as Hk.
    simpl. apply (asc_natlt_intro 0 (q * q ^ k)). lia.
Defined.

(* The enumerator: bounded-fuel Fixpoint -- stop at once when x < e
   (strict first-crossing halt), otherwise take one decay step and
   search the remaining fuel. *)
Fixpoint asc_k_enum (fuel p q x e : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      if Nat.ltb x e then O else Datatypes.S (asc_k_enum f p q (asc_iter p q x) e)
  end.

(* Termination certificate as a Set carrier: some k within fuel whose
   decay iterate is already strictly below the budget. *)
Definition asc_term_cert (fuel p q x e : nat) : Set :=
  sigT (fun k : nat => And (NatLe k fuel) (asc_natlt (asc_pow_iter p q x k) e)).

(* Correctness (strict face): reachability within the fuel bound implies
   the returned step count lands strictly below the budget. *)
Theorem asc_k_enum_strict_correct : forall fuel p q x e,
  asc_term_cert fuel p q x e ->
  asc_natlt (asc_pow_iter p q x (asc_k_enum fuel p q x e)) e.
Proof.
  intros fuel. induction fuel as [| f IH]; intros p q x e [k [Hk Hbound]].
  - (* zero fuel: only the zeroth value can carry the certificate *)
    pose proof (NatLe_drop k 0 Hk) as Hk0.
    pose proof (asc_natlt_elim (asc_pow_iter p q x k) e Hbound) as Hb0.
    assert (Hkz : k = 0%nat) by lia. subst k. exact Hbound.
  - (* successor fuel: strict stop fires at once, or the first decay
       step hands the certificate to the remaining fuel *)
    unfold asc_k_enum. destruct (Nat.ltb x e) eqn:Hlt.
    + apply (asc_natlt_intro x e).
      exact (proj1 (Nat.ltb_lt x e) Hlt).
    + pose proof (proj1 (Nat.ltb_ge x e) Hlt) as Hge.
      destruct k as [| k'].
      * pose proof (asc_natlt_elim (asc_pow_iter p q x 0) e Hbound) as Hb.
        simpl in Hb. lia.
      * pose proof (asc_natlt_elim (asc_pow_iter p q x (Datatypes.S k')) e Hbound)
          as Hb.
        simpl in Hb.
        rewrite <- (id_eq_SI nat
                      (asc_pow_iter p q (asc_iter p q x) k')
                      (asc_iter p q (asc_pow_iter p q x k'))
                      (asc_pow_iter_comm p q x k')) in Hb.
        pose proof (NatLe_drop (Datatypes.S k') (Datatypes.S f) Hk) as Hk'.
        assert (Hrec : asc_term_cert f p q (asc_iter p q x) e).
        { exists k'. split.
          - apply (NatLe_lift k' f). lia.
          - apply (asc_natlt_intro (asc_pow_iter p q (asc_iter p q x) k') e).
            exact Hb. }
        specialize (IH p q (asc_iter p q x) e Hrec).
        change (asc_natlt (asc_iter p q (asc_pow_iter p q x
                            (asc_k_enum f p q (asc_iter p q x) e))) e).
        exact (asc_natlt_transport
                 (asc_pow_iter_comm p q x (asc_k_enum f p q (asc_iter p q x) e))
                 IH).
Defined.

(* Exact face of the enumeration: at the returned step count N the
   fixed-point values still cover the exact geometric value, so the
   discrete log-modulus equation holds in the strict nat form
   x * p^N < e * q^N. *)
Theorem asc_k_enum_ltface : forall fuel p q x e,
  asc_natlt 0 p -> asc_natlt 0 q ->
  asc_term_cert fuel p q x e ->
  asc_natlt (x * p ^ asc_k_enum fuel p q x e)
            (e * q ^ asc_k_enum fuel p q x e).
Proof.
  intros fuel p q x e Hp Hq Hterm.
  set (N := asc_k_enum fuel p q x e).
  pose proof (asc_k_enum_strict_correct fuel p q x e Hterm) as H1.
  pose proof (asc_natlt_elim (asc_pow_iter p q x N) e H1) as H1'.
  pose proof (asc_pow_iter_exact_ge p q x N Hp Hq) as H2.
  pose proof (NatLe_drop (x * p ^ N) (asc_pow_iter p q x N * q ^ N) H2) as H2'.
  pose proof (asc_natlt_elim 0 (q ^ N) (asc_pow_pos q N Hq)) as HqN.
  apply (asc_natlt_intro (x * p ^ N) (e * q ^ N)).
  apply (Nat.le_lt_trans _ (asc_pow_iter p q x N * q ^ N) _).
  - exact H2'.
  - exact (proj1 (Nat.mul_lt_mono_pos_r (q ^ N) (asc_pow_iter p q x N) e HqN) H1').
Defined.

(* Numeric pin (concrete data): kappa = 7/10, a0 = 1000, budget e = 10. *)
Eval vm_compute in (asc_k_enum 50 7 10 1000 10).

(* ============================================================ *)
(* Part 1 + Part 3: the real face (generic Section over the      *)
(* interface certificate subset) -- the archimedean step         *)
(* calculator, the mixing modulus, and the real-face bridges.    *)
(* ============================================================ *)

Section AscAttnStepCalc.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* Interface field unpacking (explicitly typed intermediate forms). *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
Let minus := @minus RI.
Let S := @S RI SS.
Let sum_over_S := @sum_over_S RI SS SO.
Let tv := @S06_DiffSamplingGibbs.tv_dist RI SS SO.

(* Honest-interface premises (the UContraction certificate subset the
   TV closure needs; transition_nonneg is pruned by the closure). *)
Variable u : S -> R.
Variable u_norm : Id (sum_over_S u) one.
Variable delta : R.
Variable delta_lt_one : lt delta one.
Variable delta_pos : lt zero delta.
Variable transition : S -> S -> R.
Variable transition_row : forall s : S, Id (sum_over_S (fun s' : S => transition s s')) one.
Variable minorization : forall s s' : S, le (mult delta (u s')) (transition s s').
Variable sum_swap_cc : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable abs_ge_zero_id_cc : forall a : R, le zero a -> Id (abs a) a.
Variable lt_plus_compat_lt_le_h : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* The uniform iterate (the u_titer closure with transition supplied). *)
Let asc_titer (n : nat) (mu : S -> R) : S -> R :=
  @AttnDoeblin.u_titer RI SS SO transition n mu.

(* Archimedean certificate (explicit premise): for any positive rate
   face and tolerance, a step count exists with rate^N * face < eps. *)
Variable omd_arch : forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun N : nat => lt (mult a (r_pow (minus one delta) N)) eps).

Let omd := minus one delta.

(* 1 - delta > 0. *)
Lemma asc_omd_pos : lt zero omd.
Proof.
  unfold omd, minus.
  apply (lt_id_l zero (plus delta (opp delta)) (plus one (opp delta))
                 (id_sym (plus_opp delta))
                 (lt_plus_compat_lt_le_h delta one (opp delta) (opp delta)
                                         delta_lt_one (le_refl (opp delta)))).
Defined.

(* 1 - delta < 1 (delta > 0 supplies the strict leg; multiplicative
   monotonicity runs the mixed strict/le leg; the absorption identity
   runs the S01 assoc/comm/opp canal). *)
Lemma asc_omd_lt_one : lt omd one.
Proof.
  assert (Habsorb : Id (plus delta omd) one).
  { unfold omd, minus.
    exact (id_trans (plus_assoc delta one (opp delta))
           (id_trans (id_cong (fun w => plus w (opp delta)) (plus_comm delta one))
           (id_trans (id_sym (plus_assoc one delta (opp delta)))
           (id_trans (id_cong (fun w => plus one w) (plus_opp delta))
                     (plus_zero one))))). }
  apply (lt_id_r omd (plus delta omd) one Habsorb).
  exact (lt_id_l omd (plus zero omd) (plus delta omd)
                 (id_trans (id_sym (plus_zero omd)) (plus_comm omd zero))
                 (lt_plus_compat_lt_le_h zero delta omd omd delta_pos
                                         (le_refl omd))).
Defined.

(* ===== Part 1: the archimedean step calculator ===== *)

Definition asc_step_calc (TV0 : R)
  (HTV0 : lt zero TV0)
  (eps : R) (Heps : lt zero eps) : nat :=
  projT1 (omd_arch TV0 HTV0 eps Heps).

(* Correctness half 1: the geometric rate budget at the returned count. *)
Theorem asc_step_calc_budget : forall (TV0 : R)
  (HTV0 : lt zero TV0)
  (eps : R) (Heps : lt zero eps),
  lt (mult TV0 (r_pow omd (asc_step_calc TV0 HTV0 eps Heps))) eps.
Proof.
  intros TV0 HTV0 eps Heps.
  exact (projT2 (omd_arch TV0 HTV0 eps Heps)).
Defined.

(* Correctness half 2: TV iteration face -- for every normalized pair
   with tv(mu,nu) <= TV0, the n-th iterates fall below eps for all
   n >= N (the u_tv_iter closure with the r_pow_dec_iter monotone
   bridge; multiplicative monotonicity on the right field). *)
Theorem asc_step_calc_correct : forall (TV0 : R)
  (HTV0 : lt zero TV0)
  (eps : R) (Heps : lt zero eps)
  (mu nu : S -> R) (Hmu : Id (sum_over_S mu) one) (Hnu : Id (sum_over_S nu) one)
  (HTV : le (tv mu nu) TV0) (n : nat),
  NatLe (asc_step_calc TV0 HTV0 eps Heps) n ->
  lt (tv (asc_titer n mu) (asc_titer n nu)) eps.
Proof.
  intros TV0 HTV0 eps Heps mu nu Hmu Hnu HTV n Hn.
  pose proof (NatLe_drop (asc_step_calc TV0 HTV0 eps Heps) n Hn) as Hn'.
  pose proof (@AttnDoeblin.u_tv_iter RI SS SO u u_norm delta delta_lt_one transition
              transition_row minorization sum_swap_cc abs_ge_zero_id_cc
              lt_plus_compat_lt_le_h n mu nu Hmu Hnu) as Hdec.
  pose proof (@r_pow_dec_iter RI omd asc_omd_pos asc_omd_lt_one
              (asc_step_calc TV0 HTV0 eps Heps) n Hn') as Hmono.
  pose proof (asc_step_calc_budget TV0 HTV0 eps Heps) as Hbud0.
  pose proof (lt_id_l (mult (r_pow omd (asc_step_calc TV0 HTV0 eps Heps)) TV0)
                      (mult TV0 (r_pow omd (asc_step_calc TV0 HTV0 eps Heps)))
                      eps
                      (mult_comm (r_pow omd (asc_step_calc TV0 HTV0 eps Heps)) TV0)
                      Hbud0) as Hbud.
  apply (le_lt_trans _ (mult (r_pow omd n) TV0)).
  - apply (le_trans _ (mult (r_pow omd n) (tv mu nu))).
    + exact Hdec.
    + exact (le_mult_compat_r (r_pow omd n) (tv mu nu) TV0
               (lt_le_iff zero (r_pow omd n)
                  (inl (r_pow_pos omd n asc_omd_pos))) HTV).
  - apply (le_lt_trans _ (mult (r_pow omd (asc_step_calc TV0 HTV0 eps Heps)) TV0)).
    + exact (le_mult_compat (r_pow omd n)
                            (r_pow omd (asc_step_calc TV0 HTV0 eps Heps))
                            TV0 HTV0 Hmono).
    + exact Hbud.
Defined.

(* sigT packaging: the mixing modulus {N | from step N on, every
   normalized pair with tv <= TV0 lands below eps}. *)
Theorem asc_mixing_modulus_sigT : forall (TV0 : R)
  (HTV0 : lt zero TV0)
  (eps : R) (Heps : lt zero eps),
  sigT (fun N : nat => forall (mu nu : S -> R),
        Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
        le (tv mu nu) TV0 ->
        forall n : nat, NatLe N n ->
        lt (tv (asc_titer n mu) (asc_titer n nu)) eps).
Proof.
  intros TV0 HTV0 eps Heps.
  exists (asc_step_calc TV0 HTV0 eps Heps).
  exact (asc_step_calc_correct TV0 HTV0 eps Heps).
Defined.

(* ===== Part 3: real-face bridges ===== *)

(* Left unit law companion (one Id hop). *)
Lemma asc_mult_one_l : forall t : R, Id (mult one t) t.
Proof.
  intros t. apply (id_trans (mult_comm one t)). apply (mult_one t).
Defined.

(* Inverse uniqueness: y * z == 1 implies z == inv y. *)
Lemma asc_inv_unique : forall (y z : R) (Hy : lt zero y),
  Id (mult y z) one -> Id z (inv_pos y Hy).
Proof.
  intros y z Hy Hz.
  exact (id_trans (id_sym (mult_one z))
         (id_trans (id_cong (fun t => mult z t) (id_sym (inv_pos_correct y Hy)))
         (id_trans (mult_assoc z y (inv_pos y Hy))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) (mult_comm z y))
         (id_trans (id_cong (fun t => mult t (inv_pos y Hy)) Hz)
         (asc_mult_one_l (inv_pos y Hy))))))).
Defined.

(* Power splitting over multiplication: r_pow(a*b,n) == r_pow(a,n)*r_pow(b,n). *)
Lemma asc_r_pow_mult : forall (a b : R) (n : nat),
  Id (r_pow (mult a b) n) (mult (r_pow a n) (r_pow b n)).
Proof.
  intros a b n. induction n as [| n IH].
  - simpl. exact (id_sym (mult_one one)).
  - simpl.
    exact (id_trans
             (id_cong (fun t => mult (mult a b) t) IH)
             (id_trans (id_sym (mult_assoc a b (mult (r_pow a n) (r_pow b n))))
             (id_trans (id_cong (fun t => mult a t) (mult_assoc b (r_pow a n) (r_pow b n)))
             (id_trans (id_cong (fun t => mult a t)
                                (id_cong (fun t => mult t (r_pow b n)) (mult_comm b (r_pow a n))))
             (id_trans (id_cong (fun t => mult a t)
                                (id_sym (mult_assoc (r_pow a n) b (r_pow b n))))
                       (mult_assoc a (r_pow a n) (mult b (r_pow b n)))))))).
Defined.

(* nat_to_R commutes with powers: r_pow(nat_to_R k,n) == nat_to_R(k^n)
   (multiplicative homomorphism, by induction). *)
Lemma asc_nat_r_pow : forall k n : nat,
  Id (r_pow (nat_to_R k) n) (nat_to_R (k ^ n)%nat).
Proof.
  intros k n. induction n as [| n IH].
  - exact (id_sym (plus_zero one)).
  - exact (id_trans
             (id_cong (fun t => mult (nat_to_R k) t) IH)
             (id_sym (nat_to_R_mult_hom k (k ^ n)%nat))).
Defined.

(* Power splitting over inversion: r_pow(inv x,n) == inv(r_pow x,n)
   (inverse uniqueness, by induction; the positivity premise Hp travels
   as an explicit slot). *)
Lemma asc_r_pow_inv : forall (x : R) (Hx : lt zero x) (n : nat) (Hp : lt zero (r_pow x n)),
  Id (r_pow (inv_pos x Hx) n) (inv_pos (r_pow x n) Hp).
Proof.
  intros x Hx n. induction n as [| n IH]; intros Hp.
  - exact (id_sym (id_trans (id_sym (asc_mult_one_l (inv_pos one Hp)))
                            (inv_pos_correct one Hp))).
  - specialize (IH (r_pow_pos x n Hx)).
    exact (id_trans
             (id_cong (fun t => mult (inv_pos x Hx) t) IH)
             (asc_inv_unique (mult x (r_pow x n))
                             (mult (inv_pos x Hx)
                                   (inv_pos (r_pow x n) (r_pow_pos x n Hx)))
                             Hp
                             (id_trans
                                (id_sym (mult_assoc x (r_pow x n)
                                           (mult (inv_pos x Hx)
                                                 (inv_pos (r_pow x n) (r_pow_pos x n Hx)))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (mult_assoc (r_pow x n) (inv_pos x Hx)
                                                     (inv_pos (r_pow x n) (r_pow_pos x n Hx))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (id_cong (fun t => mult t (inv_pos (r_pow x n) (r_pow_pos x n Hx)))
                                                  (mult_comm (r_pow x n) (inv_pos x Hx))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (id_sym (mult_assoc (inv_pos x Hx) (r_pow x n)
                                                        (inv_pos (r_pow x n) (r_pow_pos x n Hx)))))
                             (id_trans
                                (id_cong (fun t => mult x t)
                                         (id_cong (fun t => mult (inv_pos x Hx) t)
                                                  (inv_pos_correct (r_pow x n) (r_pow_pos x n Hx))))
                             (id_trans
                                (id_cong (fun t => mult x t) (mult_one (inv_pos x Hx)))
                                (inv_pos_correct x Hx))))))))).
Defined.

(* nat-to-real monotone embedding helper: nat_to_R m <= nat_to_R(n + m)
   (Set-level nat induction on the summand; no Prop elimination into
   the Set goal). *)
Lemma asc_nat_le_plus_aux : forall n m : nat, le (nat_to_R m) (nat_to_R (n + m)%nat).
Proof.
  intros n m. induction n as [| n IH].
  - simpl. apply le_refl.
  - simpl.
    apply (le_trans _ (nat_to_R (n + m)%nat)).
    + exact IH.
    + apply (le_id_l (nat_to_R (n + m)) (plus (nat_to_R (n + m)) zero)
              (plus one (nat_to_R (n + m)))
              (id_sym (plus_zero (nat_to_R (n + m))))).
      apply (le_id_r (plus (nat_to_R (n + m)) zero) (plus (nat_to_R (n + m)) one)
              (plus one (nat_to_R (n + m))) (plus_comm (nat_to_R (n + m)) one)).
      apply (le_plus_compat (nat_to_R (n + m)) (nat_to_R (n + m)) zero one
               (le_refl (nat_to_R (n + m)))).
      exact (lt_le_iff zero one (inl one_pos)).
Defined.

Lemma asc_nat_le_embed : forall m n : nat, NatLe m n -> le (nat_to_R m) (nat_to_R n).
Proof.
  intros m n Hmn. pose proof (NatLe_drop m n Hmn) as Hmn'.
  destruct (Nat.leb n m) eqn:E.
  - assert (Heq : n = m%nat).
    { apply (Nat.le_antisymm n m).
      - exact (proj1 (Nat.leb_le n m) E).
      - exact Hmn'. }
    rewrite Heq. apply le_refl.
  - destruct n as [| n'].
    + assert (Hc : (m < 0)%nat) by (apply (proj1 (Nat.leb_gt 0 m)); exact E).
      destruct (Nat.nlt_0_r m Hc).
    + assert (Hlt : (m < Datatypes.S n')%nat)
        by (apply (proj1 (Nat.leb_gt (Datatypes.S n') m)); exact E).
      assert (Hmn2 : (m <= n')%nat) by (apply (proj1 (Nat.lt_succ_r m n')); exact Hlt).
      replace (Datatypes.S n')%nat with ((Datatypes.S (n' - m)) + m)%nat by lia.
      apply (asc_nat_le_plus_aux (Datatypes.S (n' - m)) m).
Defined.

(* Geometric assembly, Id face: A*(p/q)^N == (A*p^N)*q^{-N}. *)
Lemma asc_geom_lhs_id : forall (A p q : nat) (Hqr : lt zero (nat_to_R q)) (N : nat),
  Id (mult (nat_to_R A)
            (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr)) N))
     (mult (mult (nat_to_R A) (nat_to_R (p ^ N)))
           (inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr))).
Proof.
  intros A p q Hqr N.
  set (w := inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr)).
  pose proof (asc_r_pow_mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr) N) as Hpm.
  pose proof (asc_nat_r_pow p N) as Hpo.
  pose proof (asc_r_pow_inv (nat_to_R q) Hqr N (r_pow_pos (nat_to_R q) N Hqr)) as Hpi.
  assert (Hs2 : Id (mult (r_pow (nat_to_R p) N)
                         (r_pow (inv_pos (nat_to_R q) Hqr) N))
                   (mult (nat_to_R (p ^ N)) w)).
  { apply (id_trans
             (id_cong (fun u => mult u (r_pow (inv_pos (nat_to_R q) Hqr) N)) Hpo)).
    exact (id_cong (fun u => mult (nat_to_R (p ^ N)) u) Hpi). }
  apply (id_trans (id_cong (fun t => mult (nat_to_R A) t) Hpm)).
  apply (id_trans (id_cong (fun t => mult (nat_to_R A) t) Hs2)).
  exact (mult_assoc (nat_to_R A) (nat_to_R (p ^ N)) w).
Defined.

(* Geometric assembly, Id face: (E*q^N)*q^{-N} == E. *)
Lemma asc_geom_rhs_id : forall (E q : nat) (Hqr : lt zero (nat_to_R q)) (N : nat),
  Id (mult (mult (nat_to_R E) (nat_to_R (q ^ N)))
           (inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr)))
     (nat_to_R E).
Proof.
  intros E q Hqr N.
  set (w := inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr)).
  exact (id_trans
           (id_sym (mult_assoc (nat_to_R E) (nat_to_R (q ^ N)) w))
           (id_trans
              (id_cong (fun t => mult (nat_to_R E) t)
                       (id_trans
                          (id_cong (fun u => mult u w)
                                   (id_sym (asc_nat_r_pow q N)))
                          (inv_pos_correct (r_pow (nat_to_R q) N)
                                           (r_pow_pos (nat_to_R q) N Hqr))))
              (mult_one (nat_to_R E)))).
Defined.

(* The enumerator's rational-data correctness, le face: for kappa := p/q
   with strict-stop termination in range, the returned count N satisfies
   the real-face budget le (A*kappa^N) E (the certificate-free dual of
   the archimedean calculator face). *)
Theorem asc_enum_real_correct : forall (fuel p q A E : nat)
  (Hqr : lt zero (nat_to_R q)),
  asc_natlt 0 p -> asc_natlt 0 q ->
  asc_term_cert fuel p q A E ->
  le (mult (nat_to_R A)
            (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr))
                   (asc_k_enum fuel p q A E)))
     (nat_to_R E).
Proof.
  intros fuel p q A E Hqr Hp Hq Hterm.
  pose proof (asc_natlt_elim 0 p Hp) as Hp'.
  pose proof (asc_natlt_elim 0 q Hq) as Hq'.
  set (N := asc_k_enum fuel p q A E).
  set (w := inv_pos (r_pow (nat_to_R q) N) (r_pow_pos (nat_to_R q) N Hqr)).
  pose proof (asc_k_enum_ltface fuel p q A E Hp Hq Hterm) as Hltf.
  pose proof (Nat.lt_le_incl _ _ (asc_natlt_elim (A * p ^ N) (E * q ^ N) Hltf)) as Hlog.
  pose proof (asc_nat_le_embed (A * p ^ N) (E * q ^ N) (NatLe_lift _ _ Hlog)) as Hemb.
  assert (Hsplit : le (mult (nat_to_R A) (nat_to_R (p ^ N)))
                      (mult (nat_to_R E) (nat_to_R (q ^ N)))).
  { apply (le_id_l (mult (nat_to_R A) (nat_to_R (p ^ N)))
                   (nat_to_R (A * p ^ N))).
    - exact (id_sym (nat_to_R_mult_hom A (p ^ N))).
    - apply (le_id_r (nat_to_R (A * p ^ N))
                     (nat_to_R (E * q ^ N))
                     (mult (nat_to_R E) (nat_to_R (q ^ N)))
                     (nat_to_R_mult_hom E (q ^ N))).
      exact Hemb. }
  assert (H3 : le (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                  (mult (mult (nat_to_R E) (nat_to_R (q ^ N))) w)).
  { exact (le_mult_compat (mult (nat_to_R A) (nat_to_R (p ^ N)))
                          (mult (nat_to_R E) (nat_to_R (q ^ N))) w
                          (inv_pos_pos (r_pow (nat_to_R q) N)
                             (r_pow_pos (nat_to_R q) N Hqr))
                          Hsplit). }
  apply (le_id_l (mult (nat_to_R A)
                         (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr)) N))
                 (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                 (nat_to_R E)
                 (asc_geom_lhs_id A p q Hqr N)).
  apply (le_id_r (mult (mult (nat_to_R A) (nat_to_R (p ^ N))) w)
                 (mult (mult (nat_to_R E) (nat_to_R (q ^ N))) w)
                 (nat_to_R E)
                 (asc_geom_rhs_id E q Hqr N) H3).
Defined.

(* The direct-rate variant: under a certificate omd == p/q, the returned
   count N satisfies the real-face budget le (A*omd^N) E (the real form
   of the step witness, feeding the rate budget directly). *)
Theorem asc_omd_enum_budget : forall (fuel p q A E : nat)
  (Hqr : lt zero (nat_to_R q)),
  asc_natlt 0 p -> asc_natlt 0 q ->
  Id omd (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr)) ->
  asc_term_cert fuel p q A E ->
  le (mult (nat_to_R A) (r_pow omd (asc_k_enum fuel p q A E))) (nat_to_R E).
Proof.
  intros fuel p q A E Hqr Hp Hq Homd Hterm.
  apply (le_id_l (mult (nat_to_R A) (r_pow omd (asc_k_enum fuel p q A E)))
                 (mult (nat_to_R A)
                       (r_pow (mult (nat_to_R p) (inv_pos (nat_to_R q) Hqr))
                              (asc_k_enum fuel p q A E)))
                 (nat_to_R E)
                 (id_cong (fun t => mult (nat_to_R A) t)
                          (id_cong (fun t => r_pow t (asc_k_enum fuel p q A E))
                                   Homd))).
  exact (asc_enum_real_correct fuel p q A E Hqr Hp Hq Hterm).
Defined.

End AscAttnStepCalc.

(* ============================================================ *)
(* Assumption audit: one Print Assumptions per theorem.          *)
(* ============================================================ *)

Print Assumptions asc_step_calc_budget.
Print Assumptions asc_step_calc_correct.
Print Assumptions asc_mixing_modulus_sigT.
Print Assumptions asc_k_enum_strict_correct.
Print Assumptions asc_k_enum_ltface.
Print Assumptions asc_enum_real_correct.
Print Assumptions asc_omd_enum_budget.

(* Extraction units: the four nat-face calculators (true Fixpoints,
   no stubs, no truncation). *)
Separate Extraction asc_ceil_div asc_iter asc_pow_iter asc_k_enum.
