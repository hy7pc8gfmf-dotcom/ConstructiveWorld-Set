(* atan_expl_rate.v — explicit convergence rate for the arctan Cauchy sequence
   (route 2 work order R2-WB, C side: alternating tail bounds and explicit modulus).

   Mission. Place the arctan alternating-tail bound in Set-carried form
   (atan_tail_explicit), the uniform tail decay (atan_tail_decay, with its weak
   gap companion and one closed strict anchor), the explicit modulus function
   atan_N_of_eps, its strict variable-form specification atan_N_expl_spec, and
   the data-carrying Cauchy witness atan_cauchy_witness (sigT pair).
   Statements. atan_tail_explicit, atan_tail_decay, atan_decay_gap_nonneg,
   atan_decay_strict_sample, atan_N_of_eps, atan_num_pos_mk, atan_eps_ge_inv_mk,
   atan_N_strict_mk, atan_N_bound_strict, atan_N_expl_spec, atan_cauchy_witness.
   Dependencies. S01_BaseRing, S02_CauchyComplete (QltT/QleT' faces, bridges,
   transitivity combinators), S03_QExp (q_pow inside atan_mag), S11_TP3B5
   (arctan_term/arctan_partial/atan_mag and the Q-faced tail lemmas);
   Stdlib QArith.QArith, QArith.Qabs, Arith.Arith, Lia, Setoid, Morphisms.
   References. Work order R2-WB sections P1-P3; base anchors S11_TP3B5.v:301,
   :290, :395, :423 (atan_tail_bound/atan_mag_decr/atan_mag_le_denom/
   atan_inv_chain), S02_CauchyComplete.v:1684 (q_arch_inv, modulus convention
   1/(N+2) < eps; opaque, not consumed as data), :51, :60, :103, :115, :182,
   :201 (order-face bridges and combinators).
   Constructivity. Zero axioms, zero admitted goals; every statement face is
   Set-carried (QleT'/QltT/sigT); Prop occurs only at premise positions and in
   four auxiliary Prop-faced bridge lemmas (Qed per the transparency-rule
   exemption for erasure-face proof bridges); definitions and all Set-faced
   statements are transparent (Defined). The modulus is data-carrying:
   atan_N_of_eps eps = denominator of eps as a natural number; measured
   N = 8, 64, 512 at eps = 1/8, 1/64, 1/512 (growth linear in 1/eps).
   Build. coqc -native-compiler no -q -Q <sandbox> "" -Q <base_local> ""
   atan_expl_rate.v, under the cpu-guard wrapper, from the sandbox directory. *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S11_TP3B5.

(* ============================================================ *)
(* Section 1. P1: alternating tail bound, Set-carried face.      *)
(* The base lemma atan_tail_bound (S11_TP3B5.v:301) carries a    *)
(* Qle (Prop) conclusion; the Set face is obtained by the       *)
(* mechanical order bridge Qle_to_QleT' (S02_CauchyComplete     *)
(* .v:115), never by restating a Prop conclusion.               *)
(* ============================================================ *)

Lemma atan_tail_explicit : forall (x : Q) (m n : nat),
  QleT' (Qabs x) 1 -> (m <= n)%nat ->
  QleT' (Qabs (arctan_partial n x - arctan_partial m x))
        (atan_mag (Datatypes.S m) x).
Proof.
  intros x m n Hx Hmn.
  apply atan_tail_bound.
  - exact Hx.
  - exact Hmn.
Defined.

(* ============================================================ *)
(* Section 2. P2: uniform tail decay (weak, variable form), the  *)
(* weak gap companion, and one closed strict anchor. R6: the     *)
(* variable-form decay may be non-strict (QleT'); strictness is  *)
(* supplied at the modulus-selection step on closed anchors.     *)
(* ============================================================ *)

Lemma atan_tail_decay : forall (x : Q) (m k : nat), QleT' (Qabs x) 1 ->
  QleT' (atan_mag (m + k) x) (atan_mag m x).
Proof.
  intros x m k Hx.
  induction k as [| k IH].
  - replace (m + 0)%nat with m by lia.
    apply qleT'_refl.
  - replace (m + Datatypes.S k)%nat with (Datatypes.S (m + k)) by lia.
    apply (qleT'_trans _ (atan_mag (m + k) x)).
    + apply atan_mag_decr. exact Hx.
    + exact IH.
Defined.

Lemma atan_decay_gap_nonneg : forall (x : Q) (m k : nat), QleT' (Qabs x) 1 ->
  QleT' 0 (atan_mag m x - atan_mag (m + k) x).
Proof.
  intros x m k Hx.
  apply Qle_to_QleT'.
  apply (proj1 (Qle_minus_iff (atan_mag (m + k) x) (atan_mag m x))).
  exact (QleT'_to_Qle _ _ (atan_tail_decay x m k Hx)).
Defined.

(* Closed strict anchor (R6): at concrete instances QltT is the Qcompare
   boolean face and closes by direct computation. *)
Lemma atan_decay_strict_sample :
  QltT 0 (atan_mag 0 (1 # 5) - atan_mag 7 (1 # 5)).
Proof.
  reflexivity.
Defined.

(* ============================================================ *)
(* Section 3. P3: explicit modulus, its strict variable-form     *)
(* specification, and the data-carrying Cauchy witness.          *)
(*                                                               *)
(* Modulus design. atan_N_of_eps eps = Z.to_nat (QDen eps), the  *)
(* denominator of eps read as a natural number. For 0 < eps this *)
(* dominates the modulus convention 1/(N+2) < eps of             *)
(* S02_CauchyComplete.v:1684, because eps >= 1/den(eps) >        *)
(* 1/(den(eps)+2). The base witness q_arch_inv is Qed-opaque and *)
(* therefore not usable as data; this modulus is vm_compute-     *)
(* reducible. The helpers take the destructed shape (n # d) so   *)
(* every rational comparison stays linear at the Z layer.        *)
(* ============================================================ *)

Definition atan_N_of_eps (x : Q) (eps : Q) : nat := Z.to_nat (QDen eps).

Lemma atan_num_pos_mk : forall (n : Z) (d : positive),
  Qlt 0 (n # d) -> (1 <= n)%Z.
Proof.
  intros n d H0.
  unfold Qlt in H0. simpl in H0.
  lia.
Qed.

Lemma atan_eps_ge_inv_mk : forall (n : Z) (d : positive),
  Qlt 0 (n # d) -> Qle (1 / (Z.pos d # 1)) (n # d).
Proof.
  intros n d H0.
  assert (Hn : (1 <= n)%Z) by exact (atan_num_pos_mk n d H0).
  assert (Hd : (0 < Z.pos d)%Z) by lia.
  unfold Qdiv. simpl.
  unfold Qle. simpl.
  apply (proj1 (Z.mul_le_mono_pos_r 1 n (Z.pos d) Hd)).
  exact Hn.
Qed.

Lemma atan_N_strict_mk : forall (n : Z) (d : positive),
  Qlt 0 (n # d) ->
  Qlt (1 / (Z.of_nat (Z.to_nat (Z.pos d) + 2) # 1)) (n # d).
Proof.
  intros n d H0.
  assert (Hd : (0 < Z.pos d)%Z) by lia.
  assert (Hn : (1 <= n)%Z) by exact (atan_num_pos_mk n d H0).
  assert (Hge : Qle (1 / (Z.pos d # 1)) (n # d))
    by exact (atan_eps_ge_inv_mk n d H0).
  assert (Hc0 : Qlt 0 (Z.of_nat (Z.to_nat (Z.pos d) + 2) # 1))
    by (unfold Qlt; simpl; lia).
  assert (Ha0 : Qlt 0 (Z.pos d # 1)) by (unfold Qlt; simpl; lia).
  apply (Qlt_le_trans _ (1 / (Z.pos d # 1))).
  - setoid_replace (1 / (Z.of_nat (Z.to_nat (Z.pos d) + 2) # 1))
      with (/ (Z.of_nat (Z.to_nat (Z.pos d) + 2) # 1))
      by (unfold Qdiv; apply Qmult_1_l).
    setoid_replace (1 / (Z.pos d # 1)) with (/ (Z.pos d # 1))
      by (unfold Qdiv; apply Qmult_1_l).
    apply (proj1 (Qinv_lt_contravar (Z.pos d # 1)
                   (Z.of_nat (Z.to_nat (Z.pos d) + 2) # 1) Ha0 Hc0)).
    unfold Qlt. simpl. lia.
  - exact Hge.
Qed.

Lemma atan_N_bound_strict : forall eps : Q, Qlt 0 eps ->
  Qlt (1 / (Z.of_nat (Z.to_nat (QDen eps) + 2) # 1)) eps.
Proof.
  intros eps H0.
  destruct eps as [n d].
  exact (atan_N_strict_mk n d H0).
Qed.

(* Strict variable-form specification: the chain is
   |S_n - S_m| <= atan_mag (S m) x <= 1/(2m+3) <= 1/(N+2) < eps,
   where the last step is the strict anchor above. Set face by
   Qlt_to_QltT (S02_CauchyComplete.v:60). *)
Lemma atan_N_expl_spec : forall (x : Q) (eps : Q),
  QleT' (Qabs x) 1 -> Qlt 0 eps ->
  forall m n : nat, (atan_N_of_eps x eps <= m)%nat -> (m <= n)%nat ->
  QltT (Qabs (arctan_partial n x - arctan_partial m x)) eps.
Proof.
  intros x eps Hx Heps m n Hm Hmn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (1 / (Z.of_nat (2 * m + 3) # 1))).
  - apply (Qle_trans _ (atan_mag (Datatypes.S m) x)).
    + exact (QleT'_to_Qle _ _ (atan_tail_explicit x m n Hx Hmn)).
    + apply QleT'_to_Qle. apply atan_mag_le_denom. exact Hx.
  - apply (Qle_lt_trans _ (1 / (Z.of_nat (atan_N_of_eps x eps + 2) # 1))).
    + apply QleT'_to_Qle. apply atan_inv_chain. exact Hm.
    + exact (atan_N_bound_strict eps Heps).
Defined.

(* Data-carrying Cauchy witness (R8): explicit existT assembly of the
   modulus function with its specification; no tactic destructing of
   witnesses, projections only. *)
Definition atan_cauchy_witness (x : Q) (Hx : QleT' (Qabs x) 1) :
  sigT (fun Nf : Q -> nat => forall eps : Q, Qlt 0 eps ->
          forall m n : nat, (Nf eps <= m)%nat -> (m <= n)%nat ->
          QltT (Qabs (arctan_partial n x - arctan_partial m x)) eps) :=
  existT _ (fun eps => atan_N_of_eps x eps)
    (fun (eps : Q) (Heps : Qlt 0 eps) (m n : nat)
         (Hm : (atan_N_of_eps x eps <= m)%nat) (Hn : (m <= n)%nat) =>
     atan_N_expl_spec x eps Hx Heps m n Hm Hn).

(* Assumption-face print anchors: every statement must report
   "Closed under the global context". *)
Print Assumptions atan_tail_explicit.
Print Assumptions atan_tail_decay.
Print Assumptions atan_decay_gap_nonneg.
Print Assumptions atan_decay_strict_sample.
Print Assumptions atan_N_of_eps.
Print Assumptions atan_num_pos_mk.
Print Assumptions atan_eps_ge_inv_mk.
Print Assumptions atan_N_strict_mk.
Print Assumptions atan_N_bound_strict.
Print Assumptions atan_N_expl_spec.
Print Assumptions atan_cauchy_witness.
