(* ========================================================================== *)
(*  abl_audit_base_v1.v - base-face bare-position independent audit carrier    *)
(*  file (form A, zero cascade).                                              *)
(*  Mission. Formalizes the carrier family aba_qlt_eps_sub,                   *)
(*  aba_cauchy_limit_raw, aba_const_seq_convergent, aba_gibbs_softmax_explicit *)
(*  - two light-use carriers that wrap the two bare main theorems in true use: *)
(*  S02 real_cauchy_complete (bare Top #1, in-degree 493, zero direct audit)  *)
(*  and S06 attention_is_gibbs (bare Top #2, the core claim of paper 2); the  *)
(*  tail bay runs a cross-file qualified direct audit of both bare main       *)
(*  theorems (Print Assumptions follow-up audit, per the Z-spec 2.1/2.4       *)
(*  reading).                                                                 *)
(*  Dependencies. S01_BaseRing S02_CauchyComplete S03_QExp S04_RealExpLogConv *)
(*  S05_AlignmentGRPO S06_DiffSamplingGibbs (Require full-chain pass-through) *)
(*  plus Stdlib QArith List Bool Arith Setoid Morphisms.                      *)
(*  References. S02:1476 q_half_lt, in-tree signature measured this session   *)
(*  (QltT 0 eps -> QltT (eps / 2) eps); the consumption site wraps it with    *)
(*  QltT_to_Qlt. S02:3180 real_cauchy_complete; S06:3840 attention_is_gibbs;  *)
(*  S02:1436 and S02:982 in-tree precedent shapes cited at their use sites.   *)
(*  Constructivity. Whole file Qed-closed, zero acknowledgement faces, no     *)
(*  classical logic; statement faces carried at Set level (sigT / S01.And /   *)
(*  QltT / real_lt / Id all Set-typed), zero Prop leakage; the three nat-le   *)
(*  slots of aba_cauchy_limit_raw sit in premise positions (lawful keep).     *)
(*  Build. source toolchain env; unset COQLIB ROCQLIB; ulimit -s 65532;       *)
(*  rocq c -native-compiler no -q -Q <world-dir> "" abl_audit_base_v1.v       *)
(*  (single -Q pool; world supplied by the Live tree generation).             *)
(* ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.

(* ============================================================ *)
(* Section 1 - bare position 1 (S02 real_cauchy_complete)        *)
(*   use-face wrapping. The carrier theorems lower the           *)
(*   completeness main theorem's conclusion from the real_lim    *)
(*   wrapper layer down to the raw eps/N two-sided sandwich      *)
(*   form (dist convergence wrapper), and give the constant      *)
(*   sequence as a concrete application instance - both close    *)
(*   by directly exercising the main theorem body.               *)
(* ============================================================ *)

(* Q-layer helper: 0 < eps gives eps/2 < eps - (q + (-q)).       *)
(* (Pointwise kernel of the two-sided Cauchy-premise targets of  *)
(*  the constant sequence; q + (-q) is transported onto eps via  *)
(*  Qcompare_comp, then closed by S02 q_half_lt - following the  *)
(*  S02:1436 precedent shape.)                                   *)
Lemma aba_qlt_eps_sub :
  forall (q eps : Q), S02_CauchyComplete.QltT 0%Q eps ->
    S02_CauchyComplete.QltT (eps / 2)%Q (eps - (q + - q)%Q).
Proof.
  intros q eps Heps.
  assert (H0lt : Qlt 0%Q eps)
    by (apply S02_CauchyComplete.QltT_to_Qlt; exact Heps).
  assert (Hhalf : Qlt (eps / 2)%Q eps)
    by exact (S02_CauchyComplete.QltT_to_Qlt _ _
                (S02_CauchyComplete.q_half_lt eps Heps)).
  assert (Hcmp0 : Qcompare (eps / 2)%Q eps = Lt)
    by (apply Qlt_alt; exact Hhalf).
  assert (Hsub : (eps - (q + - q))%Q == eps) by ring.
  assert (Hcmp : Qcompare (eps / 2)%Q (eps - (q + - q)) = Lt).
  { assert (Hc1 : Qcompare (eps / 2)%Q (eps - (q + - q)) = Qcompare (eps / 2)%Q eps).
    { exact (Qcompare_comp (eps / 2)%Q (eps / 2)%Q (Qeq_refl (eps / 2)%Q)
                           (eps - (q + - q))%Q eps Hsub). }
    rewrite Hc1. exact Hcmp0. }
  unfold S02_CauchyComplete.QltT, Qlt_bool. rewrite Hcmp. reflexivity.
Qed.

(* Carrier 1: the raw eps/N-form wrapper of Cauchy completeness   *)
(*   (dist convergence wrapper). The limit l together with its    *)
(*   two-sided eps/N sandwich is obtained straight from the       *)
(*   Cauchy premise - the statement face no longer shows the      *)
(*   real_lim wrapper layer; downstream receives the per-eps      *)
(*   witness form directly.                                       *)
Theorem aba_cauchy_limit_raw :
  forall (u : nat -> S02_CauchyComplete.Real),
    (forall eps : Q, S02_CauchyComplete.QltT 0%Q eps ->
      sigT (fun N : nat => forall m n : nat,
        (N <= m)%nat -> (N <= n)%nat ->
        S01_BaseRing.And
          (S02_CauchyComplete.real_lt
             (S02_CauchyComplete.real_plus (u m) (S02_CauchyComplete.real_opp (u n)))
             (S02_CauchyComplete.real_const eps))
          (S02_CauchyComplete.real_lt
             (S02_CauchyComplete.real_plus (u n) (S02_CauchyComplete.real_opp (u m)))
             (S02_CauchyComplete.real_const eps)))) ->
    sigT (fun l : S02_CauchyComplete.Real =>
      forall eps : Q, S02_CauchyComplete.QltT 0%Q eps ->
        sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
          S01_BaseRing.And
            (S02_CauchyComplete.real_lt (u n)
               (S02_CauchyComplete.real_plus l (S02_CauchyComplete.real_const eps)))
            (S02_CauchyComplete.real_lt
               (S02_CauchyComplete.real_plus l (S02_CauchyComplete.real_opp (S02_CauchyComplete.real_const eps)))
               (u n)))).
Proof.
  intros u Hcau.
  exact (S02_CauchyComplete.real_cauchy_complete u Hcau).
Qed.

(* Carrier 2: a concrete application instance of completeness -   *)
(*   the constant real sequence converges. The main theorem is    *)
(*   instantiated at u := fun _ => real_const q, with the Cauchy  *)
(*   premise witnessed explicitly at N := 0 and threshold eps/2   *)
(*   (the pointwise difference is q + (-q) identically; the       *)
(*   projT1 pointwise unfolding follows the S02:982 precedent),   *)
(*   genuinely exercising the main theorem body.                  *)
Theorem aba_const_seq_convergent :
  forall (q : Q),
    sigT (fun l : S02_CauchyComplete.Real =>
      S02_CauchyComplete.real_lim
        (fun _ : nat => S02_CauchyComplete.real_const q) l).
Proof.
  intro q.
  apply (S02_CauchyComplete.real_cauchy_complete
           (fun _ : nat => S02_CauchyComplete.real_const q)).
  intros eps Heps.
  assert (HhalfT : S02_CauchyComplete.QltT 0%Q (eps / 2)%Q).
  { apply S02_CauchyComplete.Qlt_to_QltT.
    apply Qlt_shift_div_l;
      [ reflexivity
      | simpl; apply S02_CauchyComplete.QltT_to_Qlt; exact Heps ]. }
  assert (Hkey : forall k : nat,
    S02_CauchyComplete.QltT (eps / 2)%Q
      (projT1 (S02_CauchyComplete.real_const eps) k
       - projT1
           (S02_CauchyComplete.real_plus
              (S02_CauchyComplete.real_const q)
              (S02_CauchyComplete.real_opp (S02_CauchyComplete.real_const q))) k)%Q).
  { intro k.
    (* projT1 (real_const eps) k reduces to eps and projT1          *)
    (* (real_plus ...) k reduces to q + (-q), both definitionally   *)
    (* (the real_const projection itself closes by reflexivity), so *)
    (* the pointwise goal goes to the Q-layer helper after          *)
    (* conversion checking.                                         *)
    exact (aba_qlt_eps_sub q eps Heps). }
  exists 0%nat. intros m n Hm Hn. split.
  - exists (eps / 2)%Q. split.
    + exact HhalfT.
    + exists 0%nat. intros k Hk. exact (Hkey k).
  - exists (eps / 2)%Q. split.
    + exact HhalfT.
    + exists 0%nat. intros k Hk. exact (Hkey k).
Qed.

(* ============================================================ *)
(* Section 2 - bare position 2 (S06 attention_is_gibbs)          *)
(*   use-face specialization. The carrier theorem specializes    *)
(*   the "softmax = Boltzmann notation form" down to the raw     *)
(*   interface primitives: softmax z s = e^(-z_s) * Z^(-1)       *)
(*   (Gibbs normal form); the conclusion face no longer shows    *)
(*   the S06 section abbreviations boltzmann_dist_attn /         *)
(*   boltzmann_factor - genuinely exercising the main theorem    *)
(*   body.                                                       *)
(* ============================================================ *)

Theorem aba_gibbs_softmax_explicit :
  forall (RI : RealInterfaceEnhanced) (SS : StateSpace RI) (SO : SumOver RI SS),
    forall (Hsum : forall f : @S RI SS -> @R RI,
              (forall s : @S RI SS, @lt RI (@zero RI) (f s)) ->
              @lt RI (@zero RI) (@sum_over_S RI SS SO f)),
      forall (D : @R RI) (D_pos : @lt RI (@zero RI) D)
             (energy z : @S06_DiffSamplingGibbs.logits RI SS),
        (@Id (@R RI) (@inv_pos RI D D_pos) (@one RI)) ->
        (forall s : @S RI SS, @Id (@R RI) (energy s) (@opp RI (z s))) ->
        (@Id (@R RI)
             (@S06_DiffSamplingGibbs.Z_thermo RI SS SO D D_pos energy)
             (@S06_DiffSamplingGibbs.partition_function RI SS SO z)) ->
        forall s : @S RI SS,
          @Id (@R RI)
              (@S06_DiffSamplingGibbs.softmax RI SS SO Hsum z s)
              (@mult RI
                 (@exp_neg RI (@opp RI (z s)))
                 (@inv_pos RI
                    (@S06_DiffSamplingGibbs.partition_function RI SS SO z)
                    (@S06_DiffSamplingGibbs.partition_function_pos RI SS SO Hsum z))).
Proof.
  intros RI SS SO Hsum D D_pos energy z HD Henergy HZ s.
  pose proof (@S06_DiffSamplingGibbs.attention_is_gibbs
                RI SS SO Hsum D D_pos energy z HD Henergy HZ s) as HG.
  (* HG : Id (softmax ...) (boltzmann_dist_attn ...) *)
  unfold S06_DiffSamplingGibbs.boltzmann_dist_attn,
         S06_DiffSamplingGibbs.boltzmann_factor in HG.
  rewrite HD in HG.
  assert (Hml : @Id (@R RI) (@mult RI (@one RI) (energy s)) (energy s))
    by exact (id_trans (mult_comm (@one RI) (energy s)) (mult_one (energy s))).
  rewrite Hml in HG.
  rewrite (Henergy s) in HG.
  assert (Hie : @Id (@R RI)
      (@inv_pos RI
         (@S06_DiffSamplingGibbs.Z_thermo RI SS SO D D_pos energy)
         (@S06_DiffSamplingGibbs.Z_thermo_pos RI SS SO Hsum D D_pos energy))
      (@inv_pos RI
         (@S06_DiffSamplingGibbs.partition_function RI SS SO z)
         (@S06_DiffSamplingGibbs.partition_function_pos RI SS SO Hsum z)))
    by exact (inv_pos_ext
                (@S06_DiffSamplingGibbs.Z_thermo RI SS SO D D_pos energy)
                (@S06_DiffSamplingGibbs.partition_function RI SS SO z)
                (@S06_DiffSamplingGibbs.Z_thermo_pos RI SS SO Hsum D D_pos energy)
                (@S06_DiffSamplingGibbs.partition_function_pos RI SS SO Hsum z)
                HZ).
  rewrite Hie in HG.
  (* HG : Id (softmax ...) (mult (inv ...) (exp_neg (opp (z s)))) -  *)
  (* swap the product order and the Gibbs normal form follows.       *)
  exact (id_trans HG
           (id_sym (mult_comm (@exp_neg RI (@opp RI (z s)))
                              (@inv_pos RI
                                 (@S06_DiffSamplingGibbs.partition_function RI SS SO z)
                                 (@S06_DiffSamplingGibbs.partition_function_pos RI SS SO Hsum z))))).
Qed.

(* ============================================================ *)
(* Tail bay: assumption-audit face (cross-file qualified direct   *)
(*   plus self-audit). Reading rule: all 6 outputs below must be  *)
(*   "Closed under the global context". The first three are       *)
(*   direct audits of the upstream bare main theorems (the        *)
(*   cross-file follow-up audit form - the bare Top #1/#2 claims  *)
(*   thereby enter the automatic recheck face that runs at every  *)
(*   compile); the last three are self-audits of this file's      *)
(*   carrier statements (above the PA >= 1 floor).                *)
(* ============================================================ *)
Print Assumptions S02_CauchyComplete.real_cauchy_complete.
Print Assumptions S06_DiffSamplingGibbs.attention_is_gibbs.
Print Assumptions S06_DiffSamplingGibbs.attention_is_gibbs_temp.
Print Assumptions aba_cauchy_limit_raw.
Print Assumptions aba_const_seq_convergent.
Print Assumptions aba_gibbs_softmax_explicit.
