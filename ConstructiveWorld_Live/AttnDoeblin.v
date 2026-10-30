(* ConstructiveWorld-Main -- AttnDoeblin: bounded-logits softmax Doeblin contraction. *)
(** * AttnDoeblin: explicit Doeblin contraction of the bounded-logits softmax
    attention kernel, carried on Set.

    Mission.  Part A (abstract layer) [u_tv_contraction]: two-point
      total-variation contraction -- the reference distribution [u] needs only
      normalization (no stationarity, no detailed balance) and the contraction
      holds between any two normalized distributions; the iterated [u_tv_iter]
      gives the geometric rate (1 - delta)^n.  Part B (main piece): the
      bounded-logits softmax kernel, under the explicit two-sided logit bound
      (-Delta <= z <= Delta), is pointwise at least delta* * U with
      delta* := lo*lo = e^{-2Delta/T} (lo := e^{-Delta/T}) -- an explicit
      function of temperature and logit diameter; instantiating Part A gives
      the rate (1 - e^{-2Delta/T})^n.  Part C: [real_expf_realizable] supplies
      the expf mini-interface on the Cauchy reals, so Part B's assumption
      class is nonempty.

    Dependencies.  [S01_BaseRing] .. [S15_TailFEPUp] of this development;
      Stdlib [List] and [Extraction].

    References.  [attention_tv_contraction] (the in-library Doeblin node); the
      explicit interface members [sum_swap_cc], [abs_ge_zero_id_cc],
      [lt_plus_compat] are library-style, plus [sum_eq_list].

    Constructivity.  No open statements; everything on [Set]; proofs end in
      [Qed]; the extraction check reports zero Obj.magic; sum swap and
      non-negativity are explicit Variable premises; 48 declarations.

    Build.  [rocq c -native-compiler no -q -Q . "" AttnDoeblin.v] compiles
      cleanly (exit 0, same-world vo-tree rebuild); bytes 1-8: [436f7121 00015ff4]. *)

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

(* ################ Part 0: general algebra helpers ################ *)

Section AlgHelpers.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* Rewriting the goal's right-hand side on Id (single-constructor Id, eliminated by destruct) *)
Lemma lt_id_r_loc : forall (a b c : R), Id b c -> lt a b -> lt a c.
Proof.
  intros a b c H Hlt. destruct H. exact Hlt.
Qed.

(* Four-term exchange: (a+c)+(b+d) == (a+b)+(c+d) *)
Lemma plus_exchange : forall a b c d : R,
  Id (plus (plus a c) (plus b d)) (plus (plus a b) (plus c d)).
Proof.
  intros a b c d.
  apply (id_trans (plus_assoc (plus a c) b d)).
  apply (id_trans (id_cong (fun t => plus t d)
         (id_trans (id_sym (plus_assoc a c b))
         (id_trans (id_cong (fun u => plus a u) (plus_comm c b))
                   (plus_assoc a b c))))).
  apply (id_sym (plus_assoc (plus a b) c d)).
Qed.

(* Subtracting a left common factor: (a+b) - (a+c) == b - c *)
Lemma minus_plus_congr_l : forall a b c : R,
  Id (minus (plus a b) (plus a c)) (minus b c).
Proof.
  intros a b c. unfold minus.
  apply (id_trans (id_cong (fun x => plus (plus a b) x) (opp_plus a c))).
  apply (id_trans (plus_exchange a (opp a) b (opp c))).
  apply (id_trans (id_cong (fun x => plus x (plus b (opp c))) (plus_opp a))).
  apply (id_trans (plus_comm zero (plus b (opp c)))).
  apply (plus_zero (plus b (opp c))).
Qed.

(* Factoring out a common left factor (k in front): k*x - k*y == k*(x-y) *)
Lemma minus_factor : forall k x y : R,
  Id (minus (mult k x) (mult k y)) (mult k (minus x y)).
Proof.
  intros k x y. unfold minus.
  apply (id_trans (id_cong (fun x0 => plus (mult k x) x0) (id_sym (opp_mult_l k y)))).
  apply (id_sym (distrib k x (opp y))).
Qed.

(* Factoring out a common left factor (k behind): x*k - y*k == (x-y)*k *)
Lemma minus_factor_pt : forall x y k : R,
  Id (minus (mult x k) (mult y k)) (mult (minus x y) k).
Proof.
  intros x y k. unfold minus.
  apply (id_trans (id_cong (fun x0 => plus (mult x k) x0) (id_sym (opp_mult_r y k)))).
  apply (id_trans (id_cong2 plus (mult_comm x k) (mult_comm (opp y) k))).
  apply (id_trans (id_sym (distrib k x (opp y)))).
  apply (mult_comm k (minus x y)).
Qed.

(* The inverse distributes over multiplication: inv(a*b) == inv a * inv b (positive elements) *)
Lemma inv_pos_mult_distr : forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
  Id (inv_pos (mult a b) (mult_positive a b Ha Hb))
     (mult (inv_pos a Ha) (inv_pos b Hb)).
Proof.
  intros a b Ha Hb.
  apply (mult_cancel_l (mult a b) _ _ (mult_positive a b Ha Hb)).
  apply (id_trans (inv_pos_correct (mult a b) (mult_positive a b Ha Hb))).
  apply id_sym.
  apply (id_trans (id_sym (mult_assoc a b (mult (inv_pos a Ha) (inv_pos b Hb))))).
  apply (id_trans (id_cong (fun x => mult a x)
            (id_trans (mult_comm b (mult (inv_pos a Ha) (inv_pos b Hb)))
            (id_trans (id_sym (mult_assoc (inv_pos a Ha) (inv_pos b Hb) b))
                      (id_cong (fun x => mult (inv_pos a Ha) x)
                               (mult_comm (inv_pos b Hb) b)))))).
  apply (id_trans (mult_assoc a (inv_pos a Ha) (mult b (inv_pos b Hb)))).
  apply (id_trans (id_cong (fun x => mult x (mult b (inv_pos b Hb)))
                           (inv_pos_correct a Ha))).
  apply (id_trans (mult_comm one (mult b (inv_pos b Hb)))).
  apply (id_trans (mult_one (mult b (inv_pos b Hb)))).
  exact (inv_pos_correct b Hb).
Qed.

(* nat -> R embedding and its positivity *)
Fixpoint nat_to_R (k : nat) : R :=
  match k with
  | 0%nat => zero
  | Datatypes.S m => plus one (nat_to_R m)
  end.

Lemma nat_to_R_pos : forall k : nat, lt zero (nat_to_R (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - apply (lt_id_r_loc _ _ _ (id_sym (plus_zero one))). exact one_pos.
  - apply plus_positive.
    + exact one_pos.
    + exact IH.
Qed.

End AlgHelpers.

(* ################ Part A: abstract two-point TV contraction ################ *)

Section UContraction.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let sum_over_S := @sum_over_S RI SS SO.
Let tv := @tv_dist RI SS SO.

Variable u : S -> R.
Variable u_norm : Id (sum_over_S u) one.
Variable delta : R.
Variable delta_lt_one : lt delta one.
Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s' : S, le zero (transition s s').
Variable transition_row : forall s : S, Id (sum_over_S (fun s' : S => transition s s')) one.
Variable minorization : forall s s' : S, le (mult delta (u s')) (transition s s').
Variable sum_swap_cc : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable abs_ge_zero_id_cc : forall a : R, le zero a -> Id (abs a) a.
Variable lt_plus_compat_lt_le_h : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

Let omd := minus one delta.

(* 1 - delta > 0 *)
Lemma u_omd_pos_next : lt zero omd.
Proof.
  unfold omd, minus.
  apply (lt_id_l zero (plus delta (opp delta)) (plus one (opp delta))
                 (id_sym (plus_opp delta))
                 (lt_plus_compat_lt_le_h delta one (opp delta) (opp delta)
                                         delta_lt_one (le_refl (opp delta)))).
Qed.

Let inv_omd := inv_pos omd u_omd_pos_next.

Definition u_r_kernel (s s' : S) : R :=
  mult inv_omd (minus (transition s s') (mult delta (u s'))).

Lemma u_r_nonneg : forall s s' : S, le zero (u_r_kernel s s').
Proof.
  intros s s'. unfold u_r_kernel.
  apply (le_mult_nonneg_t12 inv_omd
                            (minus (transition s s') (mult delta (u s')))).
  - exact (lt_le_iff _ _ (inl (inv_pos_pos omd u_omd_pos_next))).
  - exact (le_minus_nonneg (mult delta (u s')) (transition s s') (minorization s s')).
Qed.

Lemma u_r_norm : forall s : S, Id (sum_over_S (fun s' : S => u_r_kernel s s')) one.
Proof.
  intro s. unfold u_r_kernel.
  apply (id_trans (sum_over_S_linear inv_omd
           (fun s' : S => minus (transition s s') (mult delta (u s'))))).
  apply (id_trans (id_cong (fun x => mult inv_omd x)
  (id_trans (sum_over_S_minus (fun s' : S => transition s s')
                              (fun s' : S => mult delta (u s')))
            (id_cong2 minus (transition_row s)
                      (id_trans (sum_over_S_linear delta u)
                                (id_cong (fun x => mult delta x) u_norm)))))).
  apply (id_trans (id_cong (fun x => mult inv_omd x)
                           (id_cong (fun y => minus one y) (mult_one delta)))).
  apply (id_trans (mult_comm inv_omd omd) (inv_pos_correct omd u_omd_pos_next)).
Qed.

(* T == delta*u + (1-delta)*R *)
Lemma u_tr_decomp : forall s s' : S,
  Id (transition s s')
     (plus (mult delta (u s')) (mult omd (u_r_kernel s s'))).
Proof.
  intros s s'. unfold u_r_kernel.
  assert (Habs : Id (mult omd (mult inv_omd (minus (transition s s') (mult delta (u s')))))
                    (minus (transition s s') (mult delta (u s')))).
  { apply (id_trans (mult_assoc omd inv_omd
           (minus (transition s s') (mult delta (u s'))))).
    apply (id_trans (id_cong (fun x => mult x (minus (transition s s') (mult delta (u s'))))
                             (inv_pos_correct omd u_omd_pos_next))).
    apply (id_trans (mult_comm one (minus (transition s s') (mult delta (u s'))))
                    (mult_one (minus (transition s s') (mult delta (u s'))))). }
  apply (id_trans (id_sym (minus_plus_cancel_gap (transition s s') (mult delta (u s'))))).
  apply (id_trans (plus_comm (minus (transition s s') (mult delta (u s')))
                             (mult delta (u s')))).
  apply (id_cong (fun x => plus (mult delta (u s')) x) (id_sym Habs)).
Qed.

(* delta*a + (1-delta)*a == a *)
Lemma delta_absorb_u : forall a : R,
  Id (plus (mult delta a) (mult omd a)) a.
Proof.
  intro a.
  assert (H1 : Id (plus delta omd) one).
  { unfold omd, minus.
    apply (id_trans (plus_assoc delta one (opp delta))).
    apply (id_trans (id_cong (fun x => plus x (opp delta)) (plus_comm delta one))).
    apply (id_trans (id_sym (plus_assoc one delta (opp delta)))).
    apply (id_trans (id_cong (fun x => plus one x) (plus_opp delta))).
    exact (plus_zero one). }
  apply (id_trans (id_cong2 plus (mult_comm delta a) (mult_comm omd a))).
  apply (id_trans (id_sym (distrib a delta omd))).
  apply (id_trans (id_cong (fun x => mult a x) H1) (mult_one a)).
Qed.

Let u_step := @attention_step RI SS SO transition.

(* One-step decomposition: T mu == delta*u + (1-delta)*R mu *)
Lemma u_step_decomp : forall (mu : S -> R) (s' : S),
  Id (sum_over_S mu) one ->
  Id (u_step mu s')
     (plus (mult delta (u s'))
           (mult omd (sum_over_S (fun s : S => mult (mu s) (u_r_kernel s s'))))).
Proof.
  intros mu s' Hmu_norm. unfold u_step.
  apply (id_trans (sum_over_S_ext _ _
        (fun s : S => id_cong (fun x => mult (mu s) x) (u_tr_decomp s s')))).
  apply (id_trans (sum_over_S_ext _ _
        (fun s : S => distrib (mu s) (mult delta (u s'))
                                (mult omd (u_r_kernel s s'))))).
  apply (id_trans (sum_over_S_add (fun s : S => mult (mu s) (mult delta (u s')))
        (fun s : S => mult (mu s) (mult omd (u_r_kernel s s'))))).
  assert (Hfirst : Id (sum_over_S (fun s : S => mult (mu s) (mult delta (u s'))))
                      (mult delta (u s'))).
  { apply (id_trans (sum_over_S_ext _ _
          (fun s : S => mult_assoc (mu s) delta (u s')))).
    apply (id_trans (sum_over_S_ext _ _
          (fun s : S => id_cong (fun x => mult x (u s')) (mult_comm (mu s) delta)))).
    apply (id_trans (sum_over_S_ext _ _
          (fun s : S => id_sym (mult_assoc delta (mu s) (u s'))))).
    apply (id_trans (sum_over_S_linear delta (fun s : S => mult (mu s) (u s')))).
    apply (id_trans (id_cong (fun x => mult delta x)
    (id_trans (sum_over_S_ext _ _ (fun s : S => mult_comm (mu s) (u s')))
    (id_trans (sum_over_S_linear (u s') mu)
    (id_trans (mult_comm (u s') (sum_over_S mu))
              (id_cong (fun x => mult x (u s')) Hmu_norm)))))).
    apply (id_cong (fun x => mult delta x)
                   (id_trans (mult_comm one (u s')) (mult_one (u s')))). }
  exact (id_cong2 plus Hfirst
    (id_trans (sum_over_S_ext _ _
      (fun s : S => id_trans (mult_assoc (mu s) omd (u_r_kernel s s'))
      (id_trans (id_cong (fun x => mult x (u_r_kernel s s')) (mult_comm (mu s) omd))
                (id_sym (mult_assoc omd (mu s) (u_r_kernel s s'))))))
      (sum_over_S_linear omd (fun s : S => mult (mu s) (u_r_kernel s s'))))).
Qed.

(* One step preserves normalization *)
Lemma u_step_norm : forall mu : S -> R,
  Id (sum_over_S mu) one -> Id (sum_over_S (fun s' : S => u_step mu s')) one.
Proof.
  intros mu Hmu.
  apply (id_trans (sum_over_S_ext _ _ (fun s' : S => u_step_decomp mu s' Hmu))).
  apply (id_trans (sum_over_S_add (fun s' : S => mult delta (u s'))
        (fun s' : S => mult omd (sum_over_S (fun s : S => mult (mu s) (u_r_kernel s s')))))).
  apply (id_trans (id_cong2 plus
    (id_trans (sum_over_S_linear delta u) (id_cong (fun x => mult delta x) u_norm))
    (id_trans (sum_over_S_linear omd (fun s2 : S => sum_over_S (fun s : S => mult (mu s) (u_r_kernel s s2))))
    (id_cong (fun x => mult omd x)
    (id_trans (id_sym (sum_swap_cc (fun s s2 : S => mult (mu s) (u_r_kernel s s2))))
    (id_trans (sum_over_S_ext _ _ (fun s : S => sum_over_S_linear (mu s) (fun s2 : S => u_r_kernel s s2)))
    (id_trans (sum_over_S_ext _ _ (fun s : S => id_cong (fun x => mult (mu s) x) (u_r_norm s)))
              (sum_over_S_ext _ _ (fun s : S => mult_one (mu s)))))))))).
  apply (id_trans (id_cong (fun x => plus x (mult omd (sum_over_S mu)))
                           (mult_one delta))).
  apply (id_trans (id_cong (fun x => plus delta x)
                 (id_trans (id_cong (fun x => mult omd x) Hmu) (mult_one omd)))).
  apply (id_trans (plus_assoc delta one (opp delta))).
  apply (id_trans (id_cong (fun x => plus x (opp delta)) (plus_comm delta one))).
  apply (id_trans (id_sym (plus_assoc one delta (opp delta)))).
  apply (id_trans (id_cong (fun x => plus one x) (plus_opp delta))).
  exact (plus_zero one).
Qed.

(* |sum f*R| <= sum |f|*R *)
Lemma u_abs_row : forall (f : S -> R) (s' : S),
  le (abs (sum_over_S (fun s : S => mult (f s) (u_r_kernel s s'))))
     (sum_over_S (fun s : S => mult (abs (f s)) (u_r_kernel s s'))).
Proof.
  intros f s'.
  apply (le_id_r (abs (sum_over_S (fun s : S => mult (f s) (u_r_kernel s s'))))
                 (sum_over_S (fun s : S => abs (mult (f s) (u_r_kernel s s'))))
                 (sum_over_S (fun s : S => mult (abs (f s)) (u_r_kernel s s')))).
  - apply (sum_over_S_ext _ _ (fun s : S =>
      id_trans (abs_mult (f s) (u_r_kernel s s'))
               (id_cong (fun x => mult (abs (f s)) x)
                        (abs_ge_zero_id_cc (u_r_kernel s s') (u_r_nonneg s s'))))).
  - exact (abs_sum_le (fun s : S => mult (f s) (u_r_kernel s s'))).
Qed.

(* ========== Main theorem A: two-point TV contraction (no stationarity needed) ========== *)
Theorem u_tv_contraction : forall (mu nu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv (u_step mu) (u_step nu)) (mult omd (tv mu nu)).
Proof.
  intros mu nu Hmu Hnu.
  assert (Hge : le zero omd).
  { exact (le_minus_nonneg delta one (lt_le_iff _ _ (inl delta_lt_one))). }
  assert (Hpt : forall s' : S,
    le (abs (minus (u_step mu s') (u_step nu s')))
       (mult omd (sum_over_S (fun s : S => mult (abs (minus (mu s) (nu s))) (u_r_kernel s s'))))).
  { intro s'.
    assert (Hd : Id (minus (u_step mu s') (u_step nu s'))
                    (mult omd (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s'))))).
    { apply (id_trans (id_cong2 minus (u_step_decomp mu s' Hmu) (u_step_decomp nu s' Hnu))).
      apply (id_trans (minus_plus_congr_l (mult delta (u s'))
                (mult omd (sum_over_S (fun s : S => mult (mu s) (u_r_kernel s s'))))
                (mult omd (sum_over_S (fun s : S => mult (nu s) (u_r_kernel s s')))))).
      apply (id_trans (minus_factor omd
                (sum_over_S (fun s : S => mult (mu s) (u_r_kernel s s')))
                (sum_over_S (fun s : S => mult (nu s) (u_r_kernel s s'))))).
      apply (id_cong (fun x => mult omd x)
      (id_trans (id_sym (sum_over_S_minus (fun s : S => mult (mu s) (u_r_kernel s s'))
                                          (fun s : S => mult (nu s) (u_r_kernel s s'))))
                (sum_over_S_ext _ _
                  (fun s : S => minus_factor_pt (mu s) (nu s) (u_r_kernel s s'))))). }
    apply (le_id_l (abs (minus (u_step mu s') (u_step nu s')))
                   (mult omd (abs (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s')))))
                   (mult omd (sum_over_S (fun s : S => mult (abs (minus (mu s) (nu s))) (u_r_kernel s s'))))).
    - assert (Habsx : Id (abs (mult omd (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s')))))
                         (mult omd (abs (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s')))))).
      { apply (id_trans (abs_mult omd (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s'))))).
        exact (id_cong2 mult (abs_ge_zero_id_cc omd Hge)
                        (id_refl : Id (abs (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s'))))
                                      (abs (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s')))))). }
      exact (id_trans (id_cong abs Hd) Habsx).
    - exact (le_mult_compat_r omd
               (abs (sum_over_S (fun s : S => mult (minus (mu s) (nu s)) (u_r_kernel s s'))))
               (sum_over_S (fun s : S => mult (abs (minus (mu s) (nu s))) (u_r_kernel s s')))
               Hge (u_abs_row (fun s : S => minus (mu s) (nu s)) s')). }
  assert (Hsum : le (sum_over_S (fun s' : S => abs (minus (u_step mu s') (u_step nu s'))))
                   (mult omd (sum_over_S (fun s : S => abs (minus (mu s) (nu s)))))).
  { apply (le_id_r (sum_over_S (fun s' : S => abs (minus (u_step mu s') (u_step nu s'))))
                   (sum_over_S (fun s' : S => mult omd
                      (sum_over_S (fun s : S => mult (abs (minus (mu s) (nu s))) (u_r_kernel s s')))))
                   (mult omd (sum_over_S (fun s : S => abs (minus (mu s) (nu s)))))).
    - apply (id_trans (sum_over_S_linear omd (fun s' : S =>
                sum_over_S (fun s : S => mult (abs (minus (mu s) (nu s))) (u_r_kernel s s'))))).
      apply (id_cong (fun x => mult omd x)
      (id_trans (id_sym (sum_swap_cc (fun s s' : S => mult (abs (minus (mu s) (nu s))) (u_r_kernel s s'))))
      (id_trans (sum_over_S_ext _ _ (fun s : S => sum_over_S_linear (abs (minus (mu s) (nu s))) (fun s' : S => u_r_kernel s s')))
      (id_trans (sum_over_S_ext _ _ (fun s : S => id_cong (fun x => mult (abs (minus (mu s) (nu s))) x) (u_r_norm s)))
                (sum_over_S_ext _ _ (fun s : S => mult_one (abs (minus (mu s) (nu s))))))))).
    - apply (sum_over_S_le _ _ Hpt). }
  apply (le_trans _ (mult (inv_pos (plus one one) two_pos)
             (mult omd (sum_over_S (fun s : S => abs (minus (mu s) (nu s))))))).
  - exact (le_mult_compat_r (inv_pos (plus one one) two_pos)
             (sum_over_S (fun s' : S => abs (minus (u_step mu s') (u_step nu s'))))
             (mult omd (sum_over_S (fun s : S => abs (minus (mu s) (nu s)))))
             (lt_le_iff _ _ (inl (inv_pos_pos (plus one one) two_pos))) Hsum).
  - assert (Hswap : Id (mult (inv_pos (plus one one) two_pos)
                           (mult omd (sum_over_S (fun s : S => abs (minus (mu s) (nu s))))))
                       (mult omd (mult (inv_pos (plus one one) two_pos)
                                       (sum_over_S (fun s : S => abs (minus (mu s) (nu s))))))).
    { apply (id_trans (mult_assoc (inv_pos (plus one one) two_pos) omd
                        (sum_over_S (fun s : S => abs (minus (mu s) (nu s)))))).
      apply (id_trans (id_cong (fun y => mult y (sum_over_S (fun s : S => abs (minus (mu s) (nu s)))))
                                (mult_comm (inv_pos (plus one one) two_pos) omd))).
      apply (id_sym (mult_assoc omd (inv_pos (plus one one) two_pos)
                        (sum_over_S (fun s : S => abs (minus (mu s) (nu s)))))). }
    apply (le_id_l _ _ _ Hswap).
    exact (le_refl _).
Qed.

(* ========== Iterated contraction: geometric rate (1-delta)^n ========== *)
Fixpoint u_titer (n : nat) (mu : S -> R) : S -> R :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => u_step (u_titer m mu)
  end.

Lemma u_titer_norm : forall (n : nat) (mu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S (u_titer n mu)) one.
Proof.
  intro n. induction n as [| n IH]; intros mu H.
  - exact H.
  - exact (u_step_norm (u_titer n mu) (IH mu H)).
Qed.

Theorem u_tv_iter : forall (n : nat) (mu nu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv (u_titer n mu) (u_titer n nu))
     (mult (r_pow omd n) (tv mu nu)).
Proof.
  intro n. induction n as [| n IH]; intros mu nu Hmu Hnu.
  - exact (le_id_l _ _ _
             (id_trans (id_sym (mult_one (tv mu nu))) (mult_comm (tv mu nu) one))
             (le_refl (mult one (tv mu nu)))).
  - apply (le_trans _ (mult omd (tv (u_titer n mu) (u_titer n nu)))).
    + exact (u_tv_contraction (u_titer n mu) (u_titer n nu)
              (u_titer_norm n mu Hmu) (u_titer_norm n nu Hnu)).
    + exact (le_id_r _ _ _
              (mult_assoc omd (r_pow omd n) (tv mu nu))
              (le_mult_compat_r omd (tv (u_titer n mu) (u_titer n nu))
                (mult (r_pow omd n) (tv mu nu))
                (le_minus_nonneg delta one (lt_le_iff _ _ (inl delta_lt_one)))
                (IH mu nu Hmu Hnu))).
Qed.

End UContraction.

(* ################ Part B (main piece): the bounded-logits softmax kernel ################ *)

Section BoundedSoftmax.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let sum_over_S := @sum_over_S RI SS SO.
Let tv := @tv_dist RI SS SO.

(* Finite-world data *)
Variable enum : list S.
Variable enum_nonempty : Not (Id enum nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable z : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z s s').
Variable z_ub : forall s s' : S, le (z s s') Delta.

(* Constructive exponential mini-interface (Part C discharges its satisfiability) *)
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).
Variable expf_mono_le : forall a b : R, le a b -> le (expf a) (expf b).

(* Three explicit interface members (as in Part A, for instantiation in Part B) *)
Variable bs_swap : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable bs_abs : forall a : R, le zero a -> Id (abs a) a.
Variable bs_lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).

Fixpoint bs_list_sum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => zero
  | x :: t => plus (f x) (bs_list_sum f t)
  end.

(* Enumerated-sum normalization (finite-world axiom: the abstract sum is pinned by enum) *)
Variable sum_eq_list : forall g : S -> R, Id (sum_over_S g) (bs_list_sum g enum).

Lemma bs_list_const_sum : forall (c : R) (l : list S),
  Id (bs_list_sum (fun _ : S => c) l) (mult (nat_to_R (length l)) c).
Proof.
  intros c l. induction l as [| x t IH].
  - apply (id_sym (id_trans (mult_comm zero c) (mult_zero c))).
  - assert (Hstep : Id (plus c (bs_list_sum (fun _ : S => c) t))
                       (plus (mult c one) (mult c (nat_to_R (length t))))).
    { exact (id_cong2 plus (id_sym (mult_one c))
                           (id_trans IH (mult_comm (nat_to_R (length t)) c))). }
    apply (id_trans Hstep).
    apply (id_trans (id_sym (distrib c one (nat_to_R (length t))))).
    apply (mult_comm c (plus one (nat_to_R (length t)))).
Qed.

Lemma bs_list_le_const : forall (f : S -> R) (c : R) (l : list S),
  (forall x : S, le (f x) c) -> le (bs_list_sum f l) (mult (nat_to_R (length l)) c).
Proof.
  intros f c l H. induction l as [| x t IH].
  - exact (le_id_r zero zero (mult zero c)
             (id_sym (id_trans (mult_comm zero c) (mult_zero c))) (le_refl zero)).
  - apply (le_id_r _ (plus c (mult c (nat_to_R (length t))))
             (mult (nat_to_R (length (x :: t))) c)).
    + exact (id_sym (id_trans (mult_comm (plus one (nat_to_R (length t))) c)
             (id_trans (distrib c one (nat_to_R (length t)))
                       (id_cong (fun w : R => plus w (mult c (nat_to_R (length t))))
                                (mult_one c))))).
    + exact (le_plus_compat (f x) c (bs_list_sum f t) (mult c (nat_to_R (length t)))
                             (H x)
                             (le_id_r _ _ _ (mult_comm (nat_to_R (length t)) c) IH)).
Qed.

Lemma bs_list_ge_const : forall (f : S -> R) (c : R) (l : list S),
  (forall x : S, le c (f x)) -> le (mult (nat_to_R (length l)) c) (bs_list_sum f l).
Proof.
  intros f c l H. induction l as [| x t IH].
  - exact (le_id_l _ _ _ (id_trans (mult_comm zero c) (mult_zero c))
             (le_refl zero)).
  - apply (le_id_l _ (plus c (mult c (nat_to_R (length t))))
             (plus (f x) (bs_list_sum f t))).
    + exact (id_trans (mult_comm (plus one (nat_to_R (length t))) c)
             (id_trans (distrib c one (nat_to_R (length t)))
                       (id_cong (fun w : R => plus w (mult c (nat_to_R (length t))))
                                (mult_one c)))).
    + exact (le_plus_compat c (f x) (mult c (nat_to_R (length t))) (bs_list_sum f t)
                             (H x)
                             (le_id_l _ _ _ (id_sym (mult_comm (nat_to_R (length t)) c)) IH)).
Qed.

Let nR := nat_to_R (length enum).

Lemma bs_nR_pos : lt zero nR.
Proof.
  destruct enum as [| x t].
  - destruct (enum_nonempty id_refl).
  - exact (nat_to_R_pos (length t)).
Qed.

Let invT := inv_pos temp temp_pos.
Let factor (s s' : S) : R := expf (mult invT (z s s')).
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).
Let delta_star := mult lo lo.

Lemma bs_lo_pos : lt zero lo.
Proof. exact (expf_pos (mult invT (opp Delta))). Qed.

Lemma bs_hi_pos : lt zero hi.
Proof. exact (expf_pos (mult invT Delta)). Qed.

(* opp Delta < Delta (from Delta > 0) *)
Lemma bs_opp_lt : lt (opp Delta) Delta.
Proof.
  apply (le_lt_trans (opp Delta) zero Delta).
  - exact (le_id_r (opp Delta) (opp zero) zero opp_zero_t13
                   (opp_le_compat zero Delta (lt_le_iff _ _ (inl Delta_pos)))).
  - exact Delta_pos.
Qed.

Lemma bs_lo_lt_hi : lt lo hi.
Proof.
  apply (expf_mono_lt (mult invT (opp Delta)) (mult invT Delta)).
  apply (lt_id_l _ (mult (opp Delta) invT) _ (mult_comm invT (opp Delta))).
  apply (lt_id_r_loc _ _ _ (mult_comm Delta invT)).
  exact (lt_mult_compat (opp Delta) Delta invT
                        (inv_pos_pos temp temp_pos) bs_opp_lt).
Qed.

(* lo*hi == one (the exp homomorphism -- the algebraic core of bounded logits) *)
Lemma bs_lo_hi_eq : Id (mult lo hi) one.
Proof.
  assert (Hs : Id (plus (mult invT (opp Delta)) (mult invT Delta)) zero).
  { apply (id_trans (id_sym (distrib invT (opp Delta) Delta))).
    apply (id_trans (id_cong (fun w => mult invT w)
           (id_trans (plus_comm (opp Delta) Delta) (plus_opp Delta)))).
    exact (mult_zero invT). }
  apply (id_trans (id_sym (expf_plus (mult invT (opp Delta)) (mult invT Delta)))).
  apply (id_trans (id_cong expf Hs)).
  exact expf_zero.
Qed.

Lemma bs_delta_star_lt_one : lt delta_star one.
Proof.
  assert (Hone : Id (mult hi lo) one).
  { apply (id_trans (mult_comm hi lo)). exact bs_lo_hi_eq. }
  assert (Hx : lt (mult lo lo) (mult hi lo)).
  { exact (lt_mult_compat lo hi lo bs_lo_pos bs_lo_lt_hi). }
  apply (lt_id_r_loc _ _ _ Hone).
  exact Hx.
Qed.

Lemma bs_inv_hi_lo : Id (inv_pos hi bs_hi_pos) lo.
Proof.
  apply (mult_cancel_l hi _ _ bs_hi_pos).
  exact (id_trans (inv_pos_correct hi bs_hi_pos)
                  (id_sym (id_trans (mult_comm hi lo) bs_lo_hi_eq))).
Qed.

(* Factor lower bound: e^{z/T} >= e^{-Delta/T} *)
Lemma bs_factor_ge_lo : forall s s' : S, le lo (factor s s').
Proof.
  intros s s'. unfold factor, lo.
  apply (expf_mono_le (mult invT (opp Delta)) (mult invT (z s s'))).
  exact (le_mult_compat_r invT (opp Delta) (z s s')
           (lt_le_iff _ _ (inl (inv_pos_pos temp temp_pos))) (z_lb s s')).
Qed.

(* Factor upper bound: e^{z/T} <= e^{Delta/T} *)
Lemma bs_factor_le_hi : forall s s' : S, le (factor s s') hi.
Proof.
  intros s s'. unfold factor, hi.
  apply (expf_mono_le (mult invT (z s s')) (mult invT Delta)).
  exact (le_mult_compat_r invT (z s s') Delta
           (lt_le_iff _ _ (inl (inv_pos_pos temp temp_pos))) (z_ub s s')).
Qed.

Definition Zrow (s : S) : R := sum_over_S (fun s' : S => factor s s').

Lemma bs_Zrow_ge : forall s : S, le (mult nR lo) (Zrow s).
Proof.
  intro s.
  apply (le_id_r (mult nR lo) (bs_list_sum (fun s' : S => factor s s') enum) (Zrow s)
                   (id_sym (sum_eq_list (fun s' : S => factor s s')))).
  exact (bs_list_ge_const (fun s' : S => factor s s') lo enum (fun x : S => bs_factor_ge_lo s x)).
Qed.

Lemma bs_Zrow_le : forall s : S, le (Zrow s) (mult nR hi).
Proof.
  intro s.
  apply (le_id_l _ _ _ (sum_eq_list (fun s' : S => factor s s'))).
  exact (bs_list_le_const (fun s' : S => factor s s') hi enum (fun x : S => bs_factor_le_hi s x)).
Qed.

Lemma bs_Zrow_pos : forall s : S, lt zero (Zrow s).
Proof.
  intro s.
  exact (lt_le_trans zero (mult nR lo) (Zrow s)
                     (mult_positive nR lo bs_nR_pos bs_lo_pos) (bs_Zrow_ge s)).
Qed.

(* The softmax kernel (temperature T) *)
Definition bs_kernel (s s' : S) : R :=
  mult (factor s s') (inv_pos (Zrow s) (bs_Zrow_pos s)).

Lemma bs_kernel_pos : forall s s' : S, lt zero (bs_kernel s s').
Proof.
  intros s s'. unfold bs_kernel.
  exact (mult_positive (factor s s') (inv_pos (Zrow s) (bs_Zrow_pos s))
                       (expf_pos (mult invT (z s s')))
                       (inv_pos_pos (Zrow s) (bs_Zrow_pos s))).
Qed.

Lemma bs_kernel_nonneg : forall s s' : S, le zero (bs_kernel s s').
Proof.
  intros s s'. exact (lt_le_iff _ _ (inl (bs_kernel_pos s s'))).
Qed.

Lemma bs_kernel_row : forall s : S, Id (sum_over_S (fun s' : S => bs_kernel s s')) one.
Proof.
  intro s. unfold bs_kernel.
  apply (id_trans (sum_over_S_ext _ _
    (fun s' : S => mult_comm (factor s s') (inv_pos (Zrow s) (bs_Zrow_pos s))))).
  apply (id_trans (sum_over_S_linear (inv_pos (Zrow s) (bs_Zrow_pos s))
                                     (fun s' : S => factor s s'))).
  apply (id_trans (mult_comm (inv_pos (Zrow s) (bs_Zrow_pos s)) (Zrow s))
                  (inv_pos_correct (Zrow s) (bs_Zrow_pos s))).
Qed.

(* The uniform distribution U = 1/|enum| *)
Let Unif : S -> R := fun _ : S => inv_pos nR bs_nR_pos.

Lemma bs_Unif_norm : Id (sum_over_S Unif) one.
Proof.
  apply (id_trans (sum_eq_list Unif)).
  apply (id_trans (bs_list_const_sum (inv_pos nR bs_nR_pos) enum)).
  exact (inv_pos_correct nR bs_nR_pos).
Qed.

(* ===== Main-piece core: the explicit Doeblin lower bound =====
   P(s,s') >= delta* * U(s'), with delta* := lo*lo = e^{-2Delta/T} (exact, no loss) *)
Lemma bs_minorization : forall s s' : S,
  le (mult delta_star (Unif s')) (bs_kernel s s').
Proof.
  intros s s'.
  assert (Hchain : le (mult lo (inv_pos (mult nR hi)
                              (mult_positive nR hi bs_nR_pos bs_hi_pos)))
                      (bs_kernel s s')).
  { apply (le_trans _ (mult lo (inv_pos (Zrow s) (bs_Zrow_pos s)))).
    - apply (le_mult_compat_r lo (inv_pos (mult nR hi)
                    (mult_positive nR hi bs_nR_pos bs_hi_pos))
                              (inv_pos (Zrow s) (bs_Zrow_pos s))
                              (lt_le_iff _ _ (inl bs_lo_pos))).
      exact (inv_pos_le_compat (Zrow s) (mult nR hi) (bs_Zrow_pos s)
                               (mult_positive nR hi bs_nR_pos bs_hi_pos)
                               (bs_Zrow_le s)).
    - unfold bs_kernel.
      exact (le_id_l _ _ _ (mult_comm lo (inv_pos (Zrow s) (bs_Zrow_pos s)))
               (le_id_r _ _ _
                 (id_sym (mult_comm (factor s s') (inv_pos (Zrow s) (bs_Zrow_pos s))))
                 (le_mult_compat_r (inv_pos (Zrow s) (bs_Zrow_pos s)) lo
                                   (factor s s')
                                   (lt_le_iff _ _ (inl (inv_pos_pos (Zrow s) (bs_Zrow_pos s))))
                                   (bs_factor_ge_lo s s')))). }
  assert (Heq : Id (mult delta_star (Unif s'))
                   (mult lo (inv_pos (mult nR hi)
                              (mult_positive nR hi bs_nR_pos bs_hi_pos)))).
  { unfold delta_star, Unif.
    assert (Hd1 : Id (mult lo (inv_pos (mult nR hi)
                          (mult_positive nR hi bs_nR_pos bs_hi_pos)))
                     (mult lo (mult (inv_pos nR bs_nR_pos) (inv_pos hi bs_hi_pos)))).
    { exact (id_cong2 mult (id_refl : Id lo lo)
                       (inv_pos_mult_distr nR hi bs_nR_pos bs_hi_pos)). }
    assert (Hd2 : Id (mult lo (mult (inv_pos nR bs_nR_pos) (inv_pos hi bs_hi_pos)))
                     (mult (mult lo lo) (inv_pos nR bs_nR_pos))).
    { apply (id_trans (id_cong (fun w : R => mult lo (mult (inv_pos nR bs_nR_pos) w))
                               bs_inv_hi_lo)).
      apply (id_trans (id_cong (fun w : R => mult lo w)
                                (mult_comm (inv_pos nR bs_nR_pos) lo))).
      exact (mult_assoc lo lo (inv_pos nR bs_nR_pos)). }
    exact (id_sym (id_trans Hd1 Hd2)). }
exact (le_id_l _ _ _ Heq Hchain).
Qed.

(* ===== Main theorem 1: two-point TV contraction of the bounded softmax kernel =====
   Contraction rate explicit: 1 - e^{-2Delta/T} *)
Theorem bounded_softmax_tv_contraction : forall (mu nu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv (@attention_step RI SS SO bs_kernel mu) (@attention_step RI SS SO bs_kernel nu))
     (mult (minus one delta_star) (tv mu nu)).
Proof.
  intros mu nu Hmu Hnu.
  exact (@u_tv_contraction RI SS SO
           Unif bs_Unif_norm delta_star bs_delta_star_lt_one
           bs_kernel bs_kernel_row bs_minorization
           bs_swap bs_abs bs_lpc mu nu Hmu Hnu).
Qed.

(* ===== Main theorem 2: iterated contraction, explicit geometric rate (1 - e^{-2Delta/T})^n ===== *)
Theorem bounded_softmax_tv_iter : forall (n : nat) (mu nu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv (@u_titer RI SS SO bs_kernel n mu) (@u_titer RI SS SO bs_kernel n nu))
     (mult (r_pow (minus one delta_star) n) (tv mu nu)).
Proof.
  intros n mu nu Hmu Hnu.
  exact (@u_tv_iter RI SS SO
           Unif bs_Unif_norm delta_star bs_delta_star_lt_one
           bs_kernel bs_kernel_row bs_minorization
           bs_swap bs_abs bs_lpc n mu nu Hmu Hnu).
Qed.

End BoundedSoftmax.


(* ################ Part C: Real-layer discharge evidence ################ *)

(* Satisfiability of the expf mini-interface on the concrete Cauchy reals -- Part B's
   assumption class is nonempty: all five fields are supplied one by one by proved
   theorems about cauchy_real_exp (mono_le is discharged branchwise through the
   constructive disjunction real_le = Or (real_lt) (real_eq)). *)
Theorem real_expf_realizable :
  sigT (fun f : Real -> Real => And (forall x : Real, real_lt real_zero (f x))
        (And (real_eq (f real_zero) real_one)
        (And (forall a b : Real,
              real_eq (f (real_plus a b)) (real_mult (f a) (f b)))
        (And (forall a b : Real, real_lt a b -> real_lt (f a) (f b))
             (forall a b : Real, real_le a b -> real_le (f a) (f b)))))).
Proof.
  exact (existT _ cauchy_real_exp
    (pair cauchy_real_exp_pos
    (pair cauchy_real_exp_zero
    (pair cauchy_real_exp_plus
    (pair cauchy_real_exp_mono
          (fun a b H => match H with
                        | inl Hlt => inl (cauchy_real_exp_mono a b Hlt)
                        | inr Heq => inr (cauchy_real_exp_wd a b Heq)
                        end)))))).
Qed.

(* Extraction check: the Real-layer exponential constructor extracts to OCaml (zero Obj.magic) *)
From Stdlib Require Import Extraction.
Extraction "attn_doeblin.ml" cauchy_real_exp cauchy_real_exp_plus.

(* ---- Replacement-piece admitted-face self-check (file tail) ---- *)
Print Assumptions plus_exchange.
Print Assumptions bs_lo_hi_eq.
Print Assumptions bs_delta_star_lt_one.
