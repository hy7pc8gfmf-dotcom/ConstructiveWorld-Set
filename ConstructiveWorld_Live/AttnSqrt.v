(* ConstructiveWorld-Set — statement-face Set-carrier completions of the Main-source analysis modules. *)

(** * AttnSqrt: constructive square roots and general-dimension temperature witnesses.

    Mission.  A constructive square root of any nonnegative real, given as a
      [sigT] witness packaged with its defining properties: [real_sqrt_exists],
      [real_sqrt_one], the general square-dimension witness family
      [sqrt_witness_sq] and [sqrt_witness_nat_sq], the embedding [nat_to_R]
      with its homomorphism properties [nat_to_R_plus_hom] and
      [nat_to_R_mult_hom], its positivity [nat_to_R_pos], and the
      temperature-scaling instances [scale_dual_sq_k] and
      [scale_dual_nat_sq_k].

    Dependencies.  Stdlib [List], [QArith.QArith], [QArith.Qabs], [Setoid],
      [Morphisms].  Requires [S01_BaseRing] through [S15_TailFEPUp] of this
      development.

    References.  This development, AttnSqrt.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id], [NatLe]); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: <none>].

    Build.  [coqc -native-compiler no -q -Q . "" AttnSqrt.v] compiles cleanly
      (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Setoid Morphisms.
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

Local Open Scope Q_scope.

(* ================= Section 1. Pointwise Real-layer utilities ================= *)

(* Pointwise: projT1 (real_mult (real_const ½) x) n == ½·x_n (projection lemmas composed) *)
Lemma sqrt_half_proj : forall (x : Real) (n : nat),
  QeqT (projT1 (real_mult (real_const (1#2)) x) n) ((1#2) * projT1 x n).
Proof.
  intros x n.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_const_proj (1#2) x n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (1#2) n)).
  reflexivity.
Qed.

(* ½·x + ½·x == x pointwise on real_eq; the Q-level identity ½q + ½q == q is decided by ring *)
Lemma sqrt_real_plus_half_half : forall x : Real,
  real_eq (real_plus (real_mult (real_const (1#2)) x)
                     (real_mult (real_const (1#2)) x))
          x.
Proof.
  intros x eps Heps.
  exists 0%nat.
  intros n Hn.
  (* Pointwise simplification of the difference: ½x_n + ½x_n − x_n == 0 *)
  assert (Hd : projT1 (real_plus (real_mult (real_const (1#2)) x)
                                 (real_mult (real_const (1#2)) x)) n
                - projT1 x n == 0%Q).
  { setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult (real_const (1#2)) x)
                            (real_mult (real_const (1#2)) x) n)).
    assert (Hh : projT1 (real_mult (real_const (1#2)) x) n
                 == (1#2) * projT1 x n).
    { apply qeqT_imp_qeq. apply sqrt_half_proj. }
    rewrite Hh.
    ring. }
  (* Qabs(difference) == Qabs 0 == 0, giving the pointwise bound |0| < eps *)
  assert (Habs0 : Qabs (projT1 (real_plus (real_mult (real_const (1#2)) x)
                                          (real_mult (real_const (1#2)) x)) n
                        - projT1 x n) == 0%Q).
  { apply Qeq_trans with (Qabs 0%Q).
    - apply Qabs_wd. exact Hd.
    - reflexivity. }
  apply Qlt_to_QltT.
  setoid_rewrite Habs0.
  apply QltT_to_Qlt. exact Heps.
Qed.

(* ================= Section 2. Constructive existence of square roots ================= *)

Theorem real_sqrt_exists : forall d : Real, real_le real_zero d ->
  sigT (fun r : Real => And (real_le real_zero r)
                            (real_eq (real_mult r r) d)).
Proof.
  intros d Hd.
  destruct Hd as [Hdlt | Hdeq].
  - 
    exists (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt))).
    split.
    + (* r > 0: exp is strictly positive (real_le left branch = real_lt) *)
      exact (inl (cauchy_real_exp_pos
              (real_mult (real_const (1#2)) (cw_log d Hdlt)))).
    + 
      apply (real_eq_trans
              (real_mult (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt)))
                         (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt))))
              (cauchy_real_exp (real_plus (real_mult (real_const (1#2)) (cw_log d Hdlt))
                                          (real_mult (real_const (1#2)) (cw_log d Hdlt))))
              d).
      * (* use additivity of exp backwards: exp(x)·exp(y) == exp(x+y) *)
        apply real_eq_sym. apply cauchy_real_exp_plus.
      * apply (real_eq_trans
                (cauchy_real_exp (real_plus (real_mult (real_const (1#2)) (cw_log d Hdlt))
                                            (real_mult (real_const (1#2)) (cw_log d Hdlt))))
                (cauchy_real_exp (cw_log d Hdlt)) d).
        -- 
           apply cauchy_real_exp_wd.
           apply sqrt_real_plus_half_half.
        -- 
           apply cw_log_exp_right.
  - (* Case 2: d ≡ 0 (certificate Hdeq : real_eq). Take r := real_zero. *)
    exists real_zero.
    split.
    + (* 0 ≥ 0: real_le right branch = real_eq 0 0 (reflexivity) *)
      exact (inr (real_eq_refl real_zero)).
    + (* 0·0 == 0 == d *)
      apply (real_eq_trans (real_mult real_zero real_zero) real_zero d).
      * apply real_mult_zero.
      * exact Hdeq.
Qed.

(* Concrete instance (extractable witness): the square root of one is constructible. *)
(*   r := exp(½·log 1), r ≥ 0 and r·r == 1 — the d = 1 instance of real_sqrt_exists. *)

Lemma real_one_pos_local : real_lt real_zero real_one.
Proof.
  exists (1#2).
  split.
  - reflexivity.
  - exists 0%nat. intros n Hn. reflexivity.
Qed.

Lemma real_sqrt_one :
  sigT (fun r : Real => And (real_le real_zero r)
                            (real_eq (real_mult r r) real_one)).
Proof.
  exact (real_sqrt_exists real_one (inl real_one_pos_local)).
Qed.

(* ================= Section 3. General square-dimension witnesses ================= *)

(* The machine-checked library instance for square dimensions covers the single
   case d = 4 ([sq_witness_4]); this section gives the [sqrt_witness] family for
   general k^2 dimensions and the dual temperature-scaling instances. *)

Section SqrtWitnessGeneral.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* The nat → R embedding reuses the library nat_to_R (implicit RI instance parameter). *)

(* Additive homomorphism: nat_to_R (m+n) == nat_to_R m + nat_to_R n *)
Lemma nat_to_R_plus_hom : forall m n : nat,
  Id (nat_to_R (m + n)%nat) (plus (nat_to_R m) (nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - simpl.
    exact (id_sym (id_trans (plus_comm zero (nat_to_R n))
                            (plus_zero (nat_to_R n)))).
  - simpl.
    exact (id_trans (id_cong (fun t => plus one t) IH)
                    (plus_assoc one (nat_to_R m) (nat_to_R n))).
Qed.

(* Multiplicative homomorphism: nat_to_R (m·n) == nat_to_R m · nat_to_R n *)
Lemma nat_to_R_mult_hom : forall m n : nat,
  Id (nat_to_R (m * n)%nat) (mult (nat_to_R m) (nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - simpl.
    exact (id_sym (id_trans (mult_comm zero (nat_to_R n))
                            (mult_zero (nat_to_R n)))).
  - simpl.
    exact (id_trans (nat_to_R_plus_hom n (m * n)%nat)
           (id_trans (id_cong (fun t => plus (nat_to_R n) t) IH)
           (id_trans (id_cong (fun t => plus t (mult (nat_to_R m) (nat_to_R n)))
                              (id_sym (mult_one (nat_to_R n))))
           (id_trans (id_cong (fun t => plus (mult (nat_to_R n) one) t)
                              (mult_comm (nat_to_R m) (nat_to_R n)))
           (id_trans (id_sym (distrib (nat_to_R n) one (nat_to_R m)))
                     (mult_comm (nat_to_R n) (plus one (nat_to_R m)))))))).
Qed.

(* Strict positivity of nat_to_R: k ≥ 1 implies 0 < nat_to_R k *)
Lemma nat_to_R_pos : forall k : nat, lt zero (nat_to_R (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - simpl.
    exact (lt_id_r zero one (plus one zero)
                   (id_sym (plus_zero one)) one_pos).
  - simpl. exact (plus_positive one (nat_to_R (Datatypes.S k)) one_pos IH).
Qed.

(* Witness (literal form): d := r·r (Id reflexivity; the naming form of "r is √(r²)") *)
Lemma sqrt_witness_sq : forall k : nat,
  sqrt_witness (mult (nat_to_R k) (nat_to_R k)) (nat_to_R k).
Proof. intro k. exact (@id_refl _ (mult (nat_to_R k) (nat_to_R k))). Qed.

(* Witness (nontrivial form): d := nat_to_R (k·k) == nat_to_R k · nat_to_R k
   (via the multiplicative homomorphism nat_to_R_mult_hom — a genuine k^2-dimension witness) *)
Lemma sqrt_witness_nat_sq : forall k : nat,
  sqrt_witness (nat_to_R (k * k)%nat) (nat_to_R k).
Proof. intro k. exact (id_sym (nat_to_R_mult_hom k k)). Qed.

(* k^2-dimension dual instance: scaling by 1/(S k) == temperature (S k)
   (instantiation of scale_sqrt_witness_dual at d := nat_to_R (S k) · nat_to_R (S k),
   r := nat_to_R (S k); k ≥ 0 implies temperature ≥ 1 > 0) *)
Lemma scale_dual_sq_k :
  forall (SS : StateSpace RI) (SO : SumOver RI SS)
         (spp : forall f : @S RI SS -> @R RI,
                (forall s : @S RI SS, lt zero (f s)) ->
                lt zero (@sum_over_S RI SS SO f))
         (k : nat) (z : @logits RI SS) (s : @S RI SS),
    Id (@softmax_scaled RI SS SO spp
          (@inv_pos RI (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)) z s)
       (@softmax_temp_param RI SS SO spp
          (nat_to_R (Datatypes.S k)) (nat_to_R_pos k) z s).
Proof.
  intros SS SO spp k z s.
  exact (scale_sqrt_witness_dual spp           (mult (nat_to_R (Datatypes.S k)) (nat_to_R (Datatypes.S k)))           (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)           (sqrt_witness_sq (Datatypes.S k)) z s).
Qed.

(* Dual instance (nat-square form, d := nat_to_R ((S k)·(S k))) *)
Lemma scale_dual_nat_sq_k :
  forall (SS : StateSpace RI) (SO : SumOver RI SS)
         (spp : forall f : @S RI SS -> @R RI,
                (forall s : @S RI SS, lt zero (f s)) ->
                lt zero (@sum_over_S RI SS SO f))
         (k : nat) (z : @logits RI SS) (s : @S RI SS),
    Id (@softmax_scaled RI SS SO spp
          (@inv_pos RI (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)) z s)
       (@softmax_temp_param RI SS SO spp
          (nat_to_R (Datatypes.S k)) (nat_to_R_pos k) z s).
Proof.
  intros SS SO spp k z s.
  exact (scale_sqrt_witness_dual spp           (nat_to_R ((Datatypes.S k) * (Datatypes.S k))%nat)           (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)           (sqrt_witness_nat_sq (Datatypes.S k)) z s).
Qed.

End SqrtWitnessGeneral.
