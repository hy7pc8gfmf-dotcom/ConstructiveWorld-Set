(* ConstructiveWorld-Set — sign lemmas for the signed Pade approximation. *)

(** * UpReqPadeSign: station values and sign propagation for the Pade chain.

    Mission.  Closed-form evaluations of the Pade numerator and
      denominator at the stations zero and one ([pds_den0_one],
      [pds_sum2], [pds_c10], [pds_c11], [pds_den1_expl]) and the sign
      propagation lemma [pds_qlt0_eq_r].

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Lia].
      Requires the base modules [S01_BaseRing] up to [S08_RealMainlineDPO]
      of this development.
      Requires [UpReqPadeQLeg] of this development.

    References.  This development, [UpReqPadeSign.v], the baseline module
      in ConstructiveWorld-Main whose statement names are carried over
      here verbatim (statement-face Set-carrier completion: [==]
      equalities moved to [QeqT], the [Qlt] conclusion of
      [pds_qlt0_eq_r] to [QltT]).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqPadeSign.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 000160bc]. *)

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
Require Import UpReqPadeExp.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

Section PadeSignQ.

(* ===== S1 baseline: the concrete case [n = 0] ===== *)

(* The denominator at [n = 0] is constantly one: [sum_upto 1] keeps only
   the [k = 0] term, and [q_pow] recurses on the [nat] index without
   touching [x]; [q_pow x 0 == 1] reduces on the index for any [x], so
   the left-hand side is closed except for the index position of [x],
   and [vm_compute] normalizes it end to end. *)
Lemma pds_den0_one : forall x : Q, QeqT (pade_den 0 x) 1%Q.
Proof. intro x. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* S1 claim: [Q_0(x)] is constantly positive ([Qlt_bool] computes to a closed [true]; same style as [qltT_0_1]). *)
Lemma pds_den0_pos : forall x : Q, QltT 0 (pade_den 0 x).
Proof. intro x. unfold QltT. vm_compute. reflexivity. Qed.

(* ===== S2 baseline main statement: positivity of the denominator at [n = 1] ===== *)

(* Splitting the two-term sum: [sum_upto 2 f == f 0 + f 1] — the fold
   is left-associated with the higher index last ([iota] in two steps
   plus [Qplus_0_l]); the index positions of [f] are all [%nat] so that
   [Q_scope] cannot absorb the literals. *)
Lemma pds_sum2 : forall f : nat -> Q,
  QeqT (sum_upto (Datatypes.S 1%nat) f) (f 0%nat + f 1%nat).
Proof.
  intro f. apply qeq_imp_qeqT. cbn [sum_upto]. cbv beta. ring.
Qed.

(* Closed-form coefficient values at [n = 1] (checked by [vm_compute],
   the same caliber as [pade_den_1_half]; a truncated [Nat.sub] or an
   inverted alternation sign would produce a mismatch). *)
Lemma pds_c10 : QeqT (pade_coeff 1 0%nat) 1%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Lemma pds_c11 : QeqT (pade_coeff 1 1%nat) (1#2)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* The explicit form: [Q_1(x) == 1 + (-1) * (1/2) * x] — the semantic
   content of the two-term alternating sum.  Split the sum, [change]
   the [q_pow] index positions, rewrite with the coefficient values,
   then finish by [ring]: the negation stays atomic on the product
   structure, so [ring] closes the goal directly. *)
Lemma pds_den1_expl : forall x : Q, QeqT (pade_den 1 x) (1%Q + (- (1#2)%Q) * x).
Proof.
  intro x. apply qeq_imp_qeqT. unfold pade_den.
  assert (Hs2 := pds_sum2 (fun k : nat => q_pow (- 1)%Q k * (pade_coeff 1 k * q_pow x k))).
  apply qeqT_imp_qeq in Hs2.
  setoid_rewrite Hs2. cbv beta.
  change (q_pow (- 1)%Q 0%nat) with 1%Q.
  change (q_pow (- 1)%Q 1%nat) with (-1)%Q.
  change (q_pow x 0%nat) with 1%Q.
  change (q_pow x 1%nat) with (x * 1)%Q.
  assert (Hc10 := pds_c10). apply qeqT_imp_qeq in Hc10.
  setoid_rewrite Hc10.
  assert (Hc11 := pds_c11). apply qeqT_imp_qeq in Hc11.
  setoid_rewrite Hc11.
  ring.
Qed.

(* Transfer of positivity along [Qeq] (the minimal transfer lemma of
   this file): from [a == b], [0 < a] transports to [0 < b].  The
   statement face is unchanged; the proof body is the single-step Q
   monotonicity limb built in [UpReqPadeQLeg.pql_qlt0_eq_r] (explicit
   assembly of Z-multiplication monotonicity plus [lia]), which keeps
   the environment free of [Psatz]/[micromega] closures. *)
Lemma pds_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> QltT 0 b.
Proof.
  intros a b Hab Ha.
  exact (pql_qlt0_eq_r a b Hab Ha).
Qed.

(* Main statement: [0 < x < 2] implies [0 < Q_1(x) = 1 - x/2].
   Proof: transport positivity to the explicit product form
   [(1/2) * (2 - x)] — both factors positive via [Qmult_lt_0_compat];
   [0 < 2 - x] follows from [x < 2] by [Qlt_minus_iff]
   ([p < q <-> 0 < q + -p] in the stdlib).
*)
Lemma pds_den1_pos : forall x : Q,
  QltT 0 x -> QltT x (2#1) -> QltT 0 (pade_den 1 x).
Proof.
  intros x H0 H2.
  apply QltT_to_Qlt in H2.
  apply (pds_qlt0_eq_r ((1#2)%Q * (2 + - x)%Q) (pade_den 1 x)).
  - apply (Qeq_trans ((1#2)%Q * (2 + - x)%Q) (1%Q + (- (1#2)%Q) * x) (pade_den 1 x)).
    + ring.
    + apply Qeq_sym. exact (qeqT_imp_qeq _ _ (pds_den1_expl x)).
  - apply Qmult_lt_0_compat.
    + unfold Qlt. simpl. lia.
    + apply (proj1 (Qlt_minus_iff x (2#1))). exact H2.
Qed.

(* ===== S3 bonus: cross-check against the anchor value ===== *)

(* [Q_1(1/2) > 0]: a numerical cross-check against the closed value
   [pade_den_1_half] ([Q_1(1/2) == 3/4]) — [Qlt_bool 0 (3/4)] computes
   to [true] in closed form, discharged by [vm_compute]. *)
Lemma pds_den1_half : QltT 0 (pade_den 1 (1#2)).
Proof. unfold QltT. vm_compute. reflexivity. Qed.

(* ===== Explicit interface registration for the general [n] form of
   [den_pos] (genuine premises only; not to be fabricated). =====
   Instantiation route for general [n]:
     [den(x) := altsum (fun k => pade_coeff n k * q_pow x k) (n+1)]
     (the exit of the [UpReqAltSumPos] engine);
   per-term nonnegativity ([pade_coeff_pos]) together with the adjacent
   decrease
     [QleT (c_{k+1} x^{k+1}) (c_k x^k)] (on the [0 <= x] segment)
   feeds [altsum_nonneg] ([QleT] premise face) / [altsum_nonneg_leT]
   ([QleT'] face) to obtain [QleT' 0 (den x)]; when the first pair is
   strict and the term count is [>= 2], [altsum_pos_strict] raises it to
   [QltT 0] (the [n = 1] lemma of this file is its manual instance);
   [le_head] serves the [< c_0] use.
   Missing dependency: the adjacent decrease needs a monotonicity face
   for [c_k x^k] (the ratio [x^k / x^{k+1}] plus a coefficient ratio of
   the form [(k+1)(2n-k) / (2(k+1)(n-k))]); no such lemma exists in the
   library yet.
   The three lemmas of this file are the manual [n = 0] / [n = 1]
   instances and serve as cross-check anchors for the general lemma. *)

End PadeSignQ.

Print Assumptions pds_qlt0_eq_r.
