(* ConstructiveWorld-Set -- real-layer instantiation hooks for the G04 projection family. *)

(** * G04ProjHook: the projection family realized on a two-point real carrier.

    Mission.  This file instantiates the closed-name projection statements
      of [G04_ProjFam] on the two-point family [I := bool] with [f := g4p_f],
      [P := g4p_P], [idx := g4p_idx]: the Real-layer bridge package [g4p_two],
      [g4p_half], [g4p_half_norm], [g4p_W2p_two_uniform_bridge], and the
      instantiations [g4p_ZP_pos_two], [g4p_ZP_le_one_two],
      [g4p_proj_normalized_two], [g4p_proj_drop_zero_two],
      [g4p_proj_keep_ge_two], [g4p_proj_uniform_full_two],
      [g4p_proj_minor_uncond_two], [g4p_kl_cost_two].

    Dependencies.  Stdlib [Lists.List].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [G04_ProjFam] of this development.

    References.  This development, G04ProjHook.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" G04ProjHook.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
Require Import G04_ProjFam.
From Stdlib Require Import Lists.List.
Import ListNotations.

(* ==================== Section 1. Real-layer supply for the two-point family ==================== *)
(* Real-layer transpose of the fa57 cluster-four blueprint:
   two := 1+1 and half := inv(two). *)

Definition g4p_two : Real := real_plus real_one real_one.

Lemma g4p_two_pos : real_lt real_zero g4p_two.
Proof.
  apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
           (real_plus real_one real_one)
           (real_eq_sym _ _ (real_plus_zero real_zero))).
  apply (real_lt_plus_compat real_zero real_one real_zero real_one
           real_lt_zero_one real_lt_zero_one).
Qed.

Definition g4p_half : Real := real_inv_pos g4p_two g4p_two_pos.

Lemma g4p_half_pos : real_lt real_zero g4p_half.
Proof.
  exact (real_inv_pos_pos g4p_two g4p_two_pos).
Qed.

(* Normalization chain: half+(half+0) == half+half == half*1+half*1
   == half*(1+1) == half*two == two*half == one, six real_eq segments
   transposing the Id four-segment chain of fa57_half_plus_half. *)
Lemma g4p_half_norm :
  real_eq (real_list_sum bool (fun _ : bool => g4p_half) [true; false]) real_one.
Proof.
  cbn [real_list_sum].
  apply (real_eq_trans _
           (real_plus (real_mult g4p_half real_one) (real_mult g4p_half real_one)) _).
  - apply (RealSetoid.real_eq_plus_compat g4p_half (real_plus g4p_half real_zero)
             (real_mult g4p_half real_one) (real_mult g4p_half real_one)).
    + apply real_eq_sym. apply real_mult_one.
    + apply (real_eq_trans _ g4p_half _).
      * apply real_plus_zero.
      * apply real_eq_sym. apply real_mult_one.
  - apply (real_eq_trans _ (real_mult g4p_half g4p_two) _).
    + apply real_eq_sym. apply real_distrib.
    + apply (real_eq_trans _ (real_mult g4p_two g4p_half) _).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* Retained witness: P constantly true, the two-point idx, and true listed
   in it (@InT_here applied explicitly, the CYB7 interface convention). *)
Definition g4p_witness :
  sigT (fun i : bool => And (Id ((fun _ : bool => true) i) true) (InT i [true; false]))
  := existT (fun i : bool => And (Id ((fun _ : bool => true) i) true) (InT i [true; false]))
            true (id_refl, @InT_here bool true [false]).

(* ==================== Section 2. Compatibility bridge: Real-layer transpose of the W2' seven-slot face ==================== *)
(* Real-layer isomorphic form of fa57_W2p_uniform_two_realized: a single
   package discharging the three slots f_norm, f_pos and P_witness together;
   the closed-name mother statements accept only this face, so it serves
   as the instantiation entry. *)

Theorem g4p_W2p_two_uniform_bridge :
  And (real_eq (real_list_sum bool (fun _ : bool => g4p_half) [true; false]) real_one)
      (And (forall i : bool, real_lt real_zero ((fun _ : bool => g4p_half) i))
           (sigT (fun i : bool =>
                    And (Id ((fun _ : bool => true) i) true)
                        (InT i [true; false])))).
Proof.
  exact (g4p_half_norm, ((fun _ : bool => g4p_half_pos), g4p_witness)).
Qed.

(* ==================== Section 3. Closed-name instantiation of the mother statements ==================== *)
(* Instance: I := bool, f pointwise half, P constantly true,
   idx := [true; false]. *)
(* Abbreviations: transparent definitions kept readable at the statement
   face; every use site converts by delta/beta/iota back to the mother
   form. *)

Definition g4p_f : bool -> Real := fun _ : bool => g4p_half.
Definition g4p_P : bool -> bool := fun _ : bool => true.
Definition g4p_idx : list bool := [true; false].
Definition g4p_Z : Real := Z_P bool g4p_f g4p_P g4p_idx.
Definition g4p_Proj (i : bool) : Real :=
  Proj bool g4p_f g4p_P g4p_idx (fun _ : bool => g4p_half_pos) g4p_witness i.

(* Piece 0a: retained mass positive (ZP_pos fed in its six-argument
   closed form, no f_norm argument). *)
Theorem g4p_ZP_pos_two : real_lt real_zero g4p_Z.
Proof.
  exact (ZP_pos bool g4p_f g4p_P g4p_idx
                (fun _ : bool => g4p_half_pos) g4p_witness).
Qed.

(* Piece 0b: retained mass at most one (ZP_le_one fed in its
   six-argument closed form, no P_witness argument). *)
Theorem g4p_ZP_le_one_two : real_le g4p_Z real_one.
Proof.
  exact (ZP_le_one bool g4p_f g4p_P g4p_idx
                   g4p_half_norm (fun _ : bool => g4p_half_pos)).
Qed.

(* Piece 1: row normalization, the Proj sum equals one. *)
Theorem g4p_proj_normalized_two :
  real_eq (real_list_sum bool g4p_Proj g4p_idx) real_one.
Proof.
  exact (proj_normalized bool g4p_f g4p_P g4p_idx
                         (fun _ : bool => g4p_half_pos) g4p_witness).
Qed.

(* Piece 3: the ejected branch drops to zero (premise-forwarding form:
   on this family P is constantly true with no false branch, so the
   absurd premise enters the signature only). *)
Theorem g4p_proj_drop_zero_two :
  forall i : bool, Id (g4p_P i) false -> real_eq (g4p_Proj i) real_zero.
Proof.
  intro i. intro Hb.
  exact (proj_drop_zero bool g4p_f g4p_P g4p_idx
                        (fun _ : bool => g4p_half_pos) g4p_witness i Hb).
Qed.

(* Piece 2: keepers dominate, f at most Proj pointwise. *)
Theorem g4p_proj_keep_ge_two :
  forall i : bool, Id (g4p_P i) true -> real_le (g4p_f i) (g4p_Proj i).
Proof.
  exact (fun (i : bool) (Hb : Id (g4p_P i) true) =>
           proj_keep_ge bool g4p_f g4p_P g4p_idx g4p_half_norm
                        (fun _ : bool => g4p_half_pos) g4p_witness i Hb).
Qed.

(* Piece 6: the degenerate image (P constantly true implies Proj
   coincides with f), the image link of the zero-temperature limit;
   the all-true premise is supplied pointwise by id_refl. *)
Theorem g4p_proj_uniform_full_two :
  (forall i : bool, Id (g4p_P i) true) ->
  forall i : bool, real_eq (g4p_Proj i) (g4p_f i).
Proof.
  intros P_all i.
  exact (proj_uniform_full bool g4p_f g4p_P g4p_idx g4p_half_norm
                           (fun _ : bool => g4p_half_pos) g4p_witness P_all i).
Qed.

(* Piece 5: minorization transport (take u := f and delta := one;
   the premise one*half == half comes from b4_one_mult via real_eq_le). *)
Theorem g4p_proj_minor_uncond_two :
  forall i : bool, real_le (real_mult real_one (g4p_f i)) (g4p_Proj i).
Proof.
  exact (fun i : bool =>
           proj_minor_uncond bool g4p_f g4p_P g4p_idx g4p_half_norm
                             (fun _ : bool => g4p_half_pos) g4p_witness
                             g4p_f real_one
                             (fun i0 : bool =>
                                RealSetoid.real_eq_le
                                  (real_mult real_one (g4p_f i0)) (g4p_f i0)
                                  (b4_one_mult (g4p_f i0)))
                             i).
Qed.

(* Piece 4, the main piece of the mother statement (cost identity):
   KL(q|f) == KL(q|Proj) + (-log Z) with q := Proj supplied by itself
   (normalization is Piece 1, pointwise positivity carries the
   keepK_pos certificate, ejected masses drop to zero through Piece 3;
   the mother statement thus closes over its own uses). *)
Definition g4p_kl_q : bool -> Real := g4p_Proj.

Definition g4p_kl_q_pos :
  forall i : bool, real_lt real_zero (g4p_kl_q i)
  := fun i : bool =>
       keepK_pos bool g4p_f g4p_P g4p_idx
                 (fun _ : bool => g4p_half_pos) g4p_witness i.

Definition g4p_KLqf : Real :=
  KLqf bool g4p_f g4p_idx
       (fun _ : bool => g4p_half_pos) g4p_kl_q g4p_kl_q_pos.

Definition g4p_KLqp : Real :=
  KLqp bool g4p_f g4p_P g4p_idx
       (fun _ : bool => g4p_half_pos) g4p_witness g4p_kl_q g4p_kl_q_pos.

Definition g4p_neglogZ : Real :=
  real_opp (real_log (ZK bool g4p_f g4p_P g4p_idx)
                     (ZP_pos bool g4p_f g4p_P g4p_idx
                             (fun _ : bool => g4p_half_pos) g4p_witness)).

Theorem g4p_kl_cost_two : real_eq g4p_KLqf (real_plus g4p_KLqp g4p_neglogZ).
Proof.
  exact (proj_kl_cost bool g4p_f g4p_P g4p_idx
                      (fun _ : bool => g4p_half_pos) g4p_witness
                      g4p_kl_q g4p_proj_normalized_two
                      g4p_kl_q_pos g4p_proj_drop_zero_two).
Qed.

(* ============ Assumption-face closure audit: Print Assumptions on all exported pieces ============ *)

Print Assumptions g4p_two_pos.
Print Assumptions g4p_half_pos.
Print Assumptions g4p_half_norm.
Print Assumptions g4p_W2p_two_uniform_bridge.
Print Assumptions g4p_ZP_pos_two.
Print Assumptions g4p_ZP_le_one_two.
Print Assumptions g4p_proj_normalized_two.
Print Assumptions g4p_proj_drop_zero_two.
Print Assumptions g4p_proj_keep_ge_two.
Print Assumptions g4p_proj_uniform_full_two.
Print Assumptions g4p_proj_minor_uncond_two.
Print Assumptions g4p_kl_cost_two.
