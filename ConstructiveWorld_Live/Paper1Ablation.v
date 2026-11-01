(* Paper1Ablation.v - ablation C-slot construction bit CZD11 (group
   E-STAGING-CZD11) of paper 1 "Constructive ML Alignment: A Unified
   Formalization" (standalone module; zero edits to the source tree).
   pa1_ prefix guards name collisions; base ConstructiveWorld_vo_901 (268).
   Mission.  Formalize the properties stated by the five theorem/lemma
     declaration faces: three Real-layer paper openings, zero added
     interface premises.  Slot 1 pa1_grpo_unit_moment_pop (paper sec. 10.2
     item 1c): population-form unit moment (1/G) * sum (A_i/sigma)^2 == 1;
     the in-tree UpGRPO.real_grpo_standardized_unit_moment is the
     unnormalized form; assembled via real_list_sum_g_linear/ext,
     real_mult_exchange, real_inv_pos_correct.  Slot 2
     pa1_dpo_reward_relative_exact (sec. 9.2 opening 5.6 dual): at pi-star
     the implicit reward difference equals the true reward difference,
     via S08 real_dpo_reward_recovers_up_to_baseline (proved, Closed).
     Slot 3 pa1_raw_second_moment_decomp (sec. 9.2 obstruction 7.4 dual):
     sum r_i^2 == sum A_i^2 + G*mu^2 (unnormalized central second moment;
     A the within-group centered advantage), via S08
     real_grpo_advantage_zero_mean + real_list_sum_g_linear/add/const.
   Dependencies.  Stdlib List; tree modules S08_RealMainlineDPO, S03_QExp,
     S09_EntropyReal, S07_RealSetoidExpLog, S02_CauchyComplete,
     S01_BaseRing (read-only; import face exactly the source face, no
     added imports -- guards against mixed-generation .vo hazards).
   References.  The five declaration faces: pa1_opp_eq_compat (src line
     35), pa1_mult_exchange (71), pa1_grpo_unit_moment_pop (117),
     pa1_raw_second_moment_decomp (201), pa1_dpo_reward_relative_exact (389).
   Constructivity.  axiom-free by construction: purely constructive Set-
     layer statements, zero Prop leakage, all Qed-closed nontrivial; the
     trailing Print Assumptions census attests zero-assumption closure.
   Build.  rocq c -native-compiler no -q -Q . "" (Rocq 9.1 toolchain).
*)

From Stdlib Require Import List.
Require Import S08_RealMainlineDPO S03_QExp S09_EntropyReal
               S07_RealSetoidExpLog S02_CauchyComplete S01_BaseRing.

(* ############ Piece 0: equality compatibility of opp (slot-2
   assembly primitive) ############ *)
(* The tree lacks a real_opp equality-compatibility piece (only the
   order-facing opp_le_compat exists); this file self-proves it by a
   pure algebra chain over plus_opp/plus_zero/assoc, never touching the
   Q layer pointwise. *)
Lemma pa1_opp_eq_compat : forall a b : Real,
  real_eq a b -> real_eq (real_opp a) (real_opp b).
Proof.
  intros a b Hab.
  apply (real_eq_trans _ (real_plus (real_opp a) (real_plus b (real_opp b))) _).
  - (* opp a == opp a + (b + opp b): the bracketed right summand == 0 *)
    apply (real_eq_trans _ (real_plus (real_opp a) real_zero) _).
    + apply (real_eq_sym _ _ (real_plus_zero (real_opp a))).
    + apply (RealSetoid.real_eq_plus_compat (real_opp a) real_zero
               (real_opp a) (real_plus b (real_opp b))
               (real_eq_refl (real_opp a))
               (real_eq_sym _ _ (real_plus_opp b))).
  - (* opp a + (b + opp b) == opp b: swap a into the (opp a + b) term, zero the (opp a + a) term *)
    apply (real_eq_trans _ (real_plus (real_plus (real_opp a) b) (real_opp b)) _).
    + apply real_plus_assoc.
    + apply (real_eq_trans _ (real_plus (real_plus (real_opp a) a) (real_opp b)) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_plus (real_opp a) b) (real_opp b)
                 (real_plus (real_opp a) a) (real_opp b)
                 (RealSetoid.real_eq_plus_compat (real_opp a) b (real_opp a) a
                    (real_eq_refl (real_opp a)) (real_eq_sym _ _ Hab))
                 (real_eq_refl (real_opp b))).
      * apply (real_eq_trans _ (real_plus real_zero (real_opp b)) _).
        -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp a) a)
                    (real_opp b) real_zero (real_opp b)
                    (real_eq_trans _ (real_plus a (real_opp a)) _
                       (real_plus_comm (real_opp a) a) (real_plus_opp a))
                    (real_eq_refl (real_opp b))).
        -- apply (real_eq_trans _ (real_plus (real_opp b) real_zero) _).
           ++ apply real_plus_comm.
           ++ apply real_plus_zero.
Qed.

(* ############ Piece 0.5: four-factor multiplication exchange
   (self-contained inline, dropping the UpGRPO dependency) ############ *)
(* Isomorphic to UpGRPO.real_mult_exchange; so that this draft rides
   only the czc10+2 piece set, it is inlined and self-proven by the
   monolith/S02 base algebra. *)
Lemma pa1_mult_exchange : forall a b c d : Real,
  real_eq (real_mult (real_mult a c) (real_mult b d))
          (real_mult (real_mult a b) (real_mult c d)).
Proof.
  intros a b c d.
  apply (real_eq_trans _ (real_mult a (real_mult c (real_mult b d))) _).
  - apply (real_eq_sym (real_mult a (real_mult c (real_mult b d)))
                       (real_mult (real_mult a c) (real_mult b d))
                       (real_mult_assoc a c (real_mult b d))).
  - apply (real_eq_trans _ (real_mult a (real_mult (real_mult c b) d)) _
      (RealSetoid.real_eq_mult_compat a (real_mult c (real_mult b d))
         a (real_mult (real_mult c b) d)
         (real_eq_refl a) (real_mult_assoc c b d))).
    + apply (real_eq_trans _ (real_mult a (real_mult b (real_mult c d))) _
        (RealSetoid.real_eq_mult_compat a (real_mult (real_mult c b) d)
           a (real_mult b (real_mult c d))
           (real_eq_refl a)
           (real_eq_trans _ _ _
             (RealSetoid.real_eq_mult_compat (real_mult c b) d
                (real_mult b c) d
                (real_mult_comm c b) (real_eq_refl d))
             (real_eq_sym (real_mult b (real_mult c d))
                          (real_mult (real_mult b c) d)
                          (real_mult_assoc b c d))))
        (real_mult_assoc a b (real_mult c d))).
Qed.

(* ############ Slot 1 + Slot 3: GRPO population unit moment and the 7.4 identity dual ############ *)
Section PA1Grpo.

Variable Grp : Set.
Variable grp_enum : list Grp.
Variable real_size_pos : real_lt real_zero (real_of_nat (length grp_enum)).
Variable reward_grp : Grp -> Real.

Let sizeR : Real := real_of_nat (length grp_enum).
Let invG : Real := real_inv_pos sizeR real_size_pos.
Let mean : Real :=
  real_mult invG (real_list_sum_g Grp reward_grp grp_enum).
Let A (i : Grp) : Real := real_plus (reward_grp i) (real_opp mean).
Let Var : Real :=
  real_list_sum_g Grp (fun i : Grp => real_mult (A i) (A i)) grp_enum.

(* ---------- Slot 1 main theorem: population-form unit moment ---------- *)
(* Honest-minimal premise face: sigma and sigma^2 == invG*Var are given
   explicitly (the existence of sigma is supplied elsewhere by the
   AttnSqrt real_sqrt_exists family; only the unit moment itself is
   assembled here). *)
Theorem pa1_grpo_unit_moment_pop :
  forall (sig : Real) (Hsig : real_lt real_zero sig)
         (Hsq : real_eq (real_mult sig sig) (real_mult invG Var)),
    real_eq
      (real_mult invG
         (real_list_sum_g Grp
            (fun i : Grp =>
               real_mult (real_mult (A i) (real_inv_pos sig Hsig))
                         (real_mult (A i) (real_inv_pos sig Hsig)))
            grp_enum))
      real_one.
Proof.
  intros sig Hsig Hsq.
  set (u := real_inv_pos sig Hsig).
  (* Step A: per-term exchange inside the sum + linear pull-out, sum((A*u)*(A*u)) == (u*u)*Var *)
  assert (Hsum : real_eq
           (real_list_sum_g Grp
              (fun i : Grp =>
                 real_mult (real_mult (A i) u) (real_mult (A i) u)) grp_enum)
           (real_mult (real_mult u u) Var)).
  { apply (real_eq_trans _
      (real_list_sum_g Grp
         (fun i : Grp =>
            real_mult (real_mult (A i) (A i)) (real_mult u u)) grp_enum) _).
    - apply real_list_sum_g_ext.
      intro i. apply pa1_mult_exchange.
    - apply (real_eq_trans _
        (real_mult (real_mult u u)
                   (real_list_sum_g Grp
                      (fun i : Grp => real_mult (A i) (A i)) grp_enum)) _).
      + apply (real_eq_trans _
          (real_list_sum_g Grp
             (fun i : Grp =>
                real_mult (real_mult u u) (real_mult (A i) (A i))) grp_enum) _).
        * apply real_list_sum_g_ext.
          intro i. apply real_mult_comm.
        * apply real_list_sum_g_linear.
      + apply real_eq_refl. }
  (* Step B: scalar identity invG*((u*u)*Var) == 1 (Hsq absorption + inv correctness) *)
  assert (Hscal : real_eq
           (real_mult invG (real_mult (real_mult u u) Var)) real_one).
  { apply (real_eq_trans _ (real_mult (real_mult (real_mult u u) invG) Var) _).
    - apply (real_eq_trans _ (real_mult (real_mult invG (real_mult u u)) Var) _).
      + apply real_mult_assoc.
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult invG (real_mult u u)) Var
                 (real_mult (real_mult u u) invG) Var
                 (real_mult_comm invG (real_mult u u)) (real_eq_refl Var)).
    - apply (real_eq_trans _ (real_mult (real_mult u u) (real_mult invG Var)) _).
      + apply (real_eq_sym _ _ (real_mult_assoc (real_mult u u) invG Var)).
      + apply (real_eq_trans _ (real_mult (real_mult u u) (real_mult sig sig)) _).
        * apply (RealSetoid.real_eq_mult_compat
                   (real_mult u u) (real_mult invG Var)
                   (real_mult u u) (real_mult sig sig)
                   (real_eq_refl (real_mult u u)) (real_eq_sym _ _ Hsq)).
        * apply (real_eq_trans _ (real_mult (real_mult sig u) (real_mult sig u)) _).
          -- apply (real_eq_trans _ (real_mult (real_mult u sig) (real_mult u sig)) _).
             ++ apply pa1_mult_exchange.
             ++ apply (RealSetoid.real_eq_mult_compat
                         (real_mult u sig) (real_mult u sig)
                         (real_mult sig u) (real_mult sig u)
                         (real_mult_comm u sig) (real_mult_comm u sig)).
          -- apply (real_eq_trans _ (real_mult real_one real_one) _).
             ++ apply (RealSetoid.real_eq_mult_compat
                         (real_mult sig u) (real_mult sig u)
                         real_one real_one
                         (real_inv_pos_correct sig Hsig)
                         (real_inv_pos_correct sig Hsig)).
             ++ apply real_mult_one. }
  (* Main chain: invG*sum == invG*((u*u)*Var) == 1 *)
  apply (real_eq_trans _ (real_mult invG (real_mult (real_mult u u) Var)) _).
  - apply (RealSetoid.real_eq_mult_compat invG
             (real_list_sum_g Grp
                (fun i : Grp =>
                   real_mult (real_mult (A i) u) (real_mult (A i) u)) grp_enum)
             invG (real_mult (real_mult u u) Var)
             (real_eq_refl invG) Hsum).
  - exact Hscal.
Qed.

(* ---------- Slot 3 main theorem: Real dual of the 7.4 identity
   (unnormalized form) ---------- *)
(* sum r_i^2 == sum A_i^2 + G*mu^2; G := group size, mu := group mean,
   A := r - mu. *)
(* Assembly: pointwise square expansion (distrib_r + distrib) + sum
   three-way split + zero mean (uses S08 real_grpo_advantage_zero_mean)
   + constant sum. *)
Theorem pa1_raw_second_moment_decomp :
  real_eq
    (real_list_sum_g Grp
       (fun i : Grp => real_mult (reward_grp i) (reward_grp i)) grp_enum)
    (real_plus Var (real_mult sizeR (real_mult mean mean))).
Proof.
  (* Zero mean: sum A == 0 (S08 main-theorem piece + mult_one transport) *)
  assert (Hz : real_eq (real_list_sum_g Grp A grp_enum) real_zero).
  { pose proof (S08_RealMainlineDPO.real_grpo_advantage_zero_mean
                  Grp grp_enum real_size_pos reward_grp real_one) as Hz1.
    apply (real_eq_trans _
      (real_list_sum_g Grp (fun i : Grp => real_mult (A i) real_one) grp_enum) _).
    - apply real_list_sum_g_ext.
      intro i. apply (real_eq_sym _ _ (real_mult_one (A i))).
    - exact Hz1. }
  (* Left-scaled sum: sum(c*A) == c*sum A == c*0 == 0 *)
  assert (Hzl : forall c : Real,
           real_eq
             (real_list_sum_g Grp
                (fun i : Grp => real_mult c (A i)) grp_enum) real_zero).
  { intro c.
    apply (real_eq_trans _ (real_mult c (real_list_sum_g Grp A grp_enum)) _).
    - apply real_list_sum_g_linear.
    - apply (real_eq_trans _ (real_mult c real_zero) _).
      + apply (RealSetoid.real_eq_mult_compat c (real_list_sum_g Grp A grp_enum)
                 c real_zero (real_eq_refl c) Hz).
      + apply real_mult_zero. }
  (* Right-scaled sum: sum(A*c) == sum(c*A) == 0 *)
  assert (Hzr : forall c : Real,
           real_eq
             (real_list_sum_g Grp
                (fun i : Grp => real_mult (A i) c) grp_enum) real_zero).
  { intro c.
    apply (real_eq_trans _
      (real_list_sum_g Grp (fun i : Grp => real_mult c (A i)) grp_enum) _).
    - apply real_list_sum_g_ext.
      intro i. apply real_mult_comm.
    - apply Hzl. }
  (* Pointwise: r*r == (A*A + A*mean) + (mean*A + mean*mean) *)
  assert (Hpt : forall i : Grp,
           real_eq (real_mult (reward_grp i) (reward_grp i))
                   (real_plus (real_plus (real_mult (A i) (A i))
                                          (real_mult (A i) mean))
                              (real_plus (real_mult mean (A i))
                                         (real_mult mean mean)))).
  { intro i.
    (* r == A + mean (centering identity: r == (r - mean) + mean) *)
    assert (Hra : real_eq (reward_grp i) (real_plus (A i) mean)).
    { apply (real_eq_trans _ (real_plus (reward_grp i) real_zero) _).
      - apply (real_eq_sym _ _ (real_plus_zero (reward_grp i))).
      - apply (real_eq_trans _
                 (real_plus (reward_grp i) (real_plus (real_opp mean) mean)) _).
        + apply (RealSetoid.real_eq_plus_compat (reward_grp i) real_zero
                   (reward_grp i) (real_plus (real_opp mean) mean)
                   (real_eq_refl (reward_grp i))).
          apply (real_eq_trans _ (real_plus mean (real_opp mean)) _).
          * apply (real_eq_sym _ _ (real_plus_opp mean)).
          * apply (real_plus_comm mean (real_opp mean)).
        + apply real_plus_assoc. }
    (* Square expansion: r*r == (A+mean)*(A+mean) == A*(A+mean) + mean*(A+mean) *)
    apply (real_eq_trans _
      (real_mult (real_plus (A i) mean) (real_plus (A i) mean)) _).
    - apply (RealSetoid.real_eq_mult_compat (reward_grp i) (reward_grp i)
               (real_plus (A i) mean) (real_plus (A i) mean) Hra Hra).
    - apply (real_eq_trans _
        (real_plus (real_mult (A i) (real_plus (A i) mean))
                   (real_mult mean (real_plus (A i) mean))) _).
      + apply (real_eq_sym _ _ (real_distrib_r (A i) mean (real_plus (A i) mean))).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_mult (A i) (real_plus (A i) mean))
                 (real_mult mean (real_plus (A i) mean))
                 (real_plus (real_mult (A i) (A i)) (real_mult (A i) mean))
                 (real_plus (real_mult mean (A i)) (real_mult mean mean))
                 (real_distrib (A i) (A i) mean)
                 (real_distrib mean (A i) mean)). }
  (* Sum three-way split: sum r^2 == (sumX + sumY) + (sumZ + sumW), X=A^2 Y=A*mean Z=mean*A W=mean^2 *)
  apply (real_eq_trans _
    (real_list_sum_g Grp
       (fun i : Grp =>
          real_plus (real_plus (real_mult (A i) (A i)) (real_mult (A i) mean))
                    (real_plus (real_mult mean (A i)) (real_mult mean mean)))
       grp_enum) _).
  - apply real_list_sum_g_ext.
    intro i. apply Hpt.
  - apply (real_eq_trans _
      (real_plus (real_plus (real_list_sum_g Grp
                                (fun i : Grp => real_mult (A i) (A i)) grp_enum)
                            (real_list_sum_g Grp
                               (fun i : Grp => real_mult (A i) mean) grp_enum))
                 (real_plus (real_list_sum_g Grp
                                (fun i : Grp => real_mult mean (A i)) grp_enum)
                            (real_list_sum_g Grp
                               (fun i : Grp => real_mult mean mean) grp_enum))) _).
    + exact
        (real_eq_trans _
           (real_plus (real_list_sum_g Grp
                         (fun i : Grp =>
                            real_plus (real_mult (A i) (A i)) (real_mult (A i) mean))
                         grp_enum)
                      (real_list_sum_g Grp
                         (fun i : Grp =>
                            real_plus (real_mult mean (A i)) (real_mult mean mean))
                         grp_enum))
           _
           (real_list_sum_g_add Grp
              (fun i : Grp =>
                 real_plus (real_mult (A i) (A i)) (real_mult (A i) mean))
              (fun i : Grp =>
                 real_plus (real_mult mean (A i)) (real_mult mean mean))
              grp_enum)
           (RealSetoid.real_eq_plus_compat
              (real_list_sum_g Grp
                 (fun i : Grp =>
                    real_plus (real_mult (A i) (A i)) (real_mult (A i) mean)) grp_enum)
              (real_list_sum_g Grp
                 (fun i : Grp =>
                    real_plus (real_mult mean (A i)) (real_mult mean mean)) grp_enum)
              (real_plus (real_list_sum_g Grp
                            (fun i : Grp => real_mult (A i) (A i)) grp_enum)
                         (real_list_sum_g Grp
                            (fun i : Grp => real_mult (A i) mean) grp_enum))
              (real_plus (real_list_sum_g Grp
                            (fun i : Grp => real_mult mean (A i)) grp_enum)
                         (real_list_sum_g Grp
                            (fun i : Grp => real_mult mean mean) grp_enum))
              (real_list_sum_g_add Grp
                 (fun i : Grp => real_mult (A i) (A i))
                 (fun i : Grp => real_mult (A i) mean) grp_enum)
              (real_list_sum_g_add Grp
                 (fun i : Grp => real_mult mean (A i))
                 (fun i : Grp => real_mult mean mean) grp_enum))).
      + (* zero-term elimination + constant term: == Var + G*mean^2 *)
      apply (real_eq_trans _
        (real_plus (real_plus Var real_zero)
                   (real_plus real_zero
                              (real_mult sizeR (real_mult mean mean)))) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_plus (real_list_sum_g Grp
                                (fun i : Grp => real_mult (A i) (A i)) grp_enum)
                            (real_list_sum_g Grp
                               (fun i : Grp => real_mult (A i) mean) grp_enum))
                 (real_plus (real_list_sum_g Grp
                                (fun i : Grp => real_mult mean (A i)) grp_enum)
                            (real_list_sum_g Grp
                               (fun i : Grp => real_mult mean mean) grp_enum))
                 (real_plus Var real_zero)
                 (real_plus real_zero (real_mult sizeR (real_mult mean mean)))
                 (RealSetoid.real_eq_plus_compat
                    (real_list_sum_g Grp
                       (fun i : Grp => real_mult (A i) (A i)) grp_enum)
                    (real_list_sum_g Grp
                       (fun i : Grp => real_mult (A i) mean) grp_enum)
                    Var real_zero (real_eq_refl Var) (Hzr mean))
                 (RealSetoid.real_eq_plus_compat
                    (real_list_sum_g Grp
                       (fun i : Grp => real_mult mean (A i)) grp_enum)
                    (real_list_sum_g Grp
                       (fun i : Grp => real_mult mean mean) grp_enum)
                    real_zero (real_mult sizeR (real_mult mean mean))
                    (Hzl mean)
                    (real_list_sum_g_const Grp (real_mult mean mean) grp_enum))).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_plus Var real_zero)
                 (real_plus real_zero (real_mult sizeR (real_mult mean mean)))
                 Var (real_mult sizeR (real_mult mean mean))
                 (real_plus_zero Var)
                 (real_eq_trans _
                    (real_plus (real_mult sizeR (real_mult mean mean)) real_zero) _
                    (real_plus_comm real_zero
                       (real_mult sizeR (real_mult mean mean)))
                    (real_plus_zero (real_mult sizeR (real_mult mean mean))))).
Qed.

End PA1Grpo.

(* ############ Slot 2: DPO relative exactness 5.6 Real dual ############ *)
Section PA1Dpo.

Variable S : Type.
Variable reward : S -> Real.
Variable beta : Real.
Variable beta_pos : real_lt real_zero beta.
Variable pi_ref : S -> Real.
Variable pi_ref_pos : forall s : S, real_lt real_zero (pi_ref s).
Variable Z_align : Real.
Variable Z_align_pos : real_lt real_zero Z_align.

(* Paper 5.6: at pi-star the implicit reward difference equals the true reward difference (the baseline beta*log Z cancels). *)
Theorem pa1_dpo_reward_relative_exact : forall s_w s_l : S,
  real_eq
    (real_plus
       (real_dpo_reward_explicit S beta pi_ref pi_ref_pos
          (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
          (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos
             Z_align Z_align_pos) s_w)
       (real_opp
          (real_dpo_reward_explicit S beta pi_ref pi_ref_pos
             (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
             (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos
                Z_align Z_align_pos) s_l)))
    (real_plus (reward s_w) (real_opp (reward s_l))).
Proof.
  intros s_w s_l.
  pose proof (S08_RealMainlineDPO.real_dpo_reward_recovers_up_to_baseline
                S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos
                s_w) as Hw.
  pose proof (S08_RealMainlineDPO.real_dpo_reward_recovers_up_to_baseline
                S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos
                s_l) as Hl.
  set (M := real_mult beta (real_log Z_align Z_align_pos)) in *.
  set (uw := real_dpo_reward_explicit S beta pi_ref pi_ref_pos
               (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
               (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos
                  Z_align Z_align_pos) s_w) in *.
  set (ul := real_dpo_reward_explicit S beta pi_ref pi_ref_pos
               (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
               (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos
                  Z_align Z_align_pos) s_l) in *.
  (* Hw : uw == r_w - M; Hl : ul == r_l - M *)
  apply (real_eq_trans _
    (real_plus (real_plus (reward s_w) (real_opp M))
               (real_opp (real_plus (reward s_l) (real_opp M)))) _).
  - apply (RealSetoid.real_eq_plus_compat uw
             (real_opp ul)
             (real_plus (reward s_w) (real_opp M))
             (real_opp (real_plus (reward s_l) (real_opp M)))
             Hw (pa1_opp_eq_compat ul
                   (real_plus (reward s_l) (real_opp M)) Hl)).
    - (* (r_w - M) + opp(r_l - M) == r_w - r_l: the baseline M cancels *)
    apply (real_eq_trans _
      (real_plus (real_plus (reward s_w) (real_opp M))
                 (real_plus (real_opp (reward s_l)) (real_opp (real_opp M)))) _).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus (reward s_w) (real_opp M))
               (real_opp (real_plus (reward s_l) (real_opp M)))
               (real_plus (reward s_w) (real_opp M))
               (real_plus (real_opp (reward s_l)) (real_opp (real_opp M)))
               (real_eq_refl (real_plus (reward s_w) (real_opp M)))
               (real_opp_plus (reward s_l) (real_opp M))).
    + apply (real_eq_trans _
        (real_plus (real_plus (real_plus (reward s_w) (real_opp M))
                              (real_opp (reward s_l)))
                   (real_opp (real_opp M))) _).
      * apply real_plus_assoc.
        * (* ((r_w - M) + opp r_l) + opp(opp M) == r_w + opp r_l *)
        apply (real_eq_trans _
          (real_plus (real_plus (reward s_w)
                                (real_plus (real_opp (reward s_l)) (real_opp M)))
                     (real_opp (real_opp M))) _).
        -- apply (RealSetoid.real_eq_plus_compat
                    (real_plus (real_plus (reward s_w) (real_opp M))
                               (real_opp (reward s_l)))
                    (real_opp (real_opp M))
                    (real_plus (reward s_w)
                               (real_plus (real_opp (reward s_l)) (real_opp M)))
                    (real_opp (real_opp M))
                    (real_eq_trans _
                       (real_plus (reward s_w)
                                  (real_plus (real_opp M) (real_opp (reward s_l)))) _
                       (real_eq_sym _ _
                          (real_plus_assoc (reward s_w) (real_opp M)
                             (real_opp (reward s_l))))
                       (RealSetoid.real_eq_plus_compat (reward s_w)
                          (real_plus (real_opp M) (real_opp (reward s_l)))
                          (reward s_w)
                          (real_plus (real_opp (reward s_l)) (real_opp M))
                          (real_eq_refl (reward s_w))
                          (real_plus_comm (real_opp M) (real_opp (reward s_l)))))
                    (real_eq_refl (real_opp (real_opp M)))).
           -- (* r_w + (opp r_l - M) + opp(opp M) == r_w + opp r_l *)
           apply (real_eq_trans _
             (real_plus (reward s_w)
                        (real_plus (real_opp (reward s_l))
                                   (real_plus (real_opp M)
                                              (real_opp (real_opp M))))) _).
           ++ apply (real_eq_trans _
                (real_plus (reward s_w)
                           (real_plus (real_plus (real_opp (reward s_l))
                                                 (real_opp M))
                                      (real_opp (real_opp M)))) _).
                ** apply (real_eq_sym _ _
                       (real_plus_assoc (reward s_w)
                          (real_plus (real_opp (reward s_l)) (real_opp M))
                          (real_opp (real_opp M)))).
                ** apply (RealSetoid.real_eq_plus_compat (reward s_w)
                             (real_plus (real_plus (real_opp (reward s_l))
                                                   (real_opp M))
                                        (real_opp (real_opp M)))
                             (reward s_w)
                             (real_plus (real_opp (reward s_l))
                                        (real_plus (real_opp M)
                                                   (real_opp (real_opp M))))
                             (real_eq_refl (reward s_w))
                             (real_eq_sym _ _
                                (real_plus_assoc (real_opp (reward s_l))
                                   (real_opp M) (real_opp (real_opp M))))).
           ++ apply (real_eq_trans _
                     (real_plus (real_plus (reward s_w) (real_opp (reward s_l)))
                                (real_plus (real_opp M) (real_opp (real_opp M)))) _).
                ** apply real_plus_assoc.
                ** apply (real_eq_trans _
                            (real_plus (real_plus (reward s_w) (real_opp (reward s_l)))
                                       real_zero) _
                            (RealSetoid.real_eq_plus_compat
                               (real_plus (reward s_w) (real_opp (reward s_l)))
                               (real_plus (real_opp M) (real_opp (real_opp M)))
                               (real_plus (reward s_w) (real_opp (reward s_l)))
                               real_zero
                               (real_eq_refl
                                  (real_plus (reward s_w) (real_opp (reward s_l))))
                               (real_plus_opp (real_opp M)))
                            (real_plus_zero
                               (real_plus (reward s_w) (real_opp (reward s_l))))).
Qed.

End PA1Dpo.

(* ############ Acceptance census: Print Assumptions (G4 caliber) ############ *)
Print Assumptions pa1_opp_eq_compat.
Print Assumptions pa1_grpo_unit_moment_pop.
Print Assumptions pa1_raw_second_moment_decomp.
Print Assumptions pa1_dpo_reward_relative_exact.
