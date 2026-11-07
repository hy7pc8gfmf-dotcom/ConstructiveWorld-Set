(* ConstructiveWorld-Set — rewiring bridge for gap B of the ln2 supply chain. *)
(** * u5c_ln2_gap2_bridge: rewiring the true-family carrier onto the canonical ln2 line face.

    Mission.  Gap B of the ln2 supply chain: a rewiring bridge from the
      true-family line-value carrier ([I : nat -> Real], [lns_Ibreal]
      shape) to the canonical numerator pair ([A B : nat -> Z])
      [ln2b_line] face along the [real_eq] seams, merging with the three
      head legs ([th < 1], [0 < |A n|], [0 < clo n]) to inhabit the
      five-layer supply interface [u5c_ln2i_pade_supply].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
      [Arith.Arith], [Lia], [Setoid], [Qfield]; requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [UpReqBanachNormOpp],
      [UpReqIrrationalCriterion] of this development.

    References.  This development, u5c_ln2_gap2_bridge.v, the
      ConstructiveWorld-Main baseline (the output face replicates [ln2i_pade_supply] of Ln2Bridge; the seam premise is the cascade form of [lnb3_conv_slot]; the head legs correspond to [lna_head_three_legs]).

    Constructivity.  The statement face is entirely Set-layer
      ([sigT]/[And]/[Or]/[QeqT]/[QltT]/[real_le]/[real_lt]/[real_eq]); the
      bridge is a transparent [Defined] term (And destructuring, four sigT
      levels, real_le transferred along the real_eq seams by Or case
      analysis); zero admitted proofs, zero classical logic; the slot
      premises are explicit parameters rather than global assumptions
      (Print Assumptions still reports Closed).

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      u5c_ln2_gap2_bridge.v] compiles cleanly (exit 0); the artifact starts
      with [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith.
From Stdlib Require Import Lia Setoid Qfield.

Open Scope nat_scope.

(* =================== Section 0. Replicated canonical supply face (spec-shape 2, X-parameterized carrier) =================== *)

(* Canonical line object: |A_n * X - B_n| (replicates the Ln2Bridge [ln2b_line], X explicit). *)
Definition u5c_ln2b_line (X : Real) (A B : nat -> Z) (n : nat) : Real :=
  real_abs (real_plus (real_mult (real_const ((A n) # 1)%Q) X)
                      (real_opp (real_const ((B n) # 1)%Q))).

(* Lower-bound leg: clo_n <= |A_n * X - B_n| (the real_le Or encoding). *)
Definition u5c_ln2b_line_lower (X : Real) (A B : nat -> Z) (clo : nat -> Q)
  : Set :=
  forall n : nat, real_le (real_const (clo n)) (u5c_ln2b_line X A B n).

(* Upper-bound leg: |A_n * X - B_n| <= th^n. *)
Definition u5c_ln2b_line_upper (X : Real) (A B : nat -> Z) (th : Q) : Set :=
  forall n : nat, real_le (u5c_ln2b_line X A B n) (real_const (q_pow th n)).

(* Five-layer supply type (replicates the Ln2Bridge [ln2i_pade_supply]: *)
(* (1) th < 1, (2) 0 < |A n|, (3) 0 < clo n, (4) the lower-bound leg, *)
(* (5) the upper-bound leg; A B clo th all explicit at the sigT layer). *)
Definition u5c_ln2i_pade_supply (X : Real) : Set :=
  sigT (fun A : nat -> Z =>
    sigT (fun B : nat -> Z =>
      sigT (fun clo : nat -> Q =>
        sigT (fun th : Q =>
          And (QltT th (1 # 1))
            (And (forall n : nat, QltT 0 (Qabs ((A n) # 1)))
              (And (forall n : nat, QltT 0 (clo n))
                (And (u5c_ln2b_line_lower X A B clo)
                     (u5c_ln2b_line_upper X A B th)))))))).

(* =================== Section 1. Rewiring transfer legs (real_le moved along real_eq; Q-layer conversion helpers) =================== *)

(* Left transfer: x <= y and x == z give z <= y (case analysis on the two Or branches). *)
Lemma gap2_le_eq_l : forall x y z : Real,
  real_le x y -> real_eq x z -> real_le z y.
Proof.
  intros x y z Hle Heq. destruct Hle as [Hlt | Heqxy].
  - exact (inl (real_eq_lt_lt z x y (real_eq_sym x z Heq) Hlt)).
  - exact (inr (real_eq_trans z x y (real_eq_sym x z Heq) Heqxy)).
Qed.

(* Right transfer: x <= y and y == z give x <= z (case analysis on the two Or branches). *)
Lemma gap2_le_eq_r : forall x y z : Real,
  real_le x y -> real_eq y z -> real_le x z.
Proof.
  intros x y z Hle Heq. destruct Hle as [Hlt | Heqxy].
  - exact (inl (real_lt_eq_lt x y z Hlt Heq)).
  - exact (inr (real_eq_trans x y z Heqxy Heq)).
Qed.

(* QeqT transitivity (a Q-layer conversion helper). *)
Lemma gap2_qeqT_trans : forall a b c : Q, QeqT a b -> QeqT b c -> QeqT a c.
Proof.
  intros a b c H1 H2. apply qeq_imp_qeqT.
  apply (Qeq_trans a b c).
  - apply qeqT_imp_qeq. exact H1.
  - apply qeqT_imp_qeq. exact H2.
Qed.

Lemma gap2_qeqT_mult_l : forall c a b : Q, QeqT a b -> QeqT (c * a) (c * b).
Proof.
  intros c a b H. apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq a b H). apply Qeq_refl.
Qed.

(* Head leg (2) transfer: |a| > 0 moves along QeqT to b (the Q-layer core of *)
(* the canonical A-face conversion). *)
Lemma gap2_abs_pos_transfer : forall a b : Q,
  QeqT a b -> QltT 0 (Qabs a) -> QltT 0 (Qabs b).
Proof.
  intros a b Heq Hpos.
  assert (Habs : (Qabs a == Qabs b)%Q).
  { apply Qabs_wd. apply qeqT_imp_qeq. exact Heq. }
  assert (Hcmp : Qcompare 0%Q (Qabs a) = Qcompare 0%Q (Qabs b)).
  { apply (Qcompare_comp 0%Q 0%Q); [apply Qeq_refl | exact Habs]. }
  unfold QltT, Qlt_bool in *. rewrite <- Hcmp. exact Hpos.
Qed.

(* Anchor: th = 4/5 < 1 (the Q-layer witness for the in-place [lna_theta_mod] *)
(* value, the original head-leg (1) value). *)
Theorem gap2_theta_45_lt1 : QltT (4 # 5)%Q (1 # 1)%Q.
Proof. apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia. Qed.

(* =================== Section 2. The interface slot and the rewiring bridge =================== *)

(* The interface slot in total form (a six-leg And, all slots explicit):
   Hth/Hap/Hclo are the three head legs; Hw is the seam leg (the real_eq
   family between the true-family carrier I and the canonical line object,
   the cascade form of lnb3_conv_slot); Hlo/Hup are the true-family face
   lower/upper bound pair. *)
Definition u5c_gap2_slot (X : Real) (A B : nat -> Z) (clo : nat -> Q)
  (th : Q) (I : nat -> Real) : Set :=
  And (QltT th (1 # 1))
    (And (forall n : nat, QltT 0 (Qabs ((A n) # 1)))
      (And (forall n : nat, QltT 0 (clo n))
        (And (forall n : nat, real_eq (I n) (u5c_ln2b_line X A B n))
          (And (forall n : nat, real_le (real_const (clo n)) (I n))
               (forall n : nat, real_le (I n)
                                       (real_const (q_pow th n))))))).

(* The rewiring bridge: the interface slot given gives the five-layer supply
   inhabited (legs (4)/(5) move the true-family face bounds to the canonical
   line face by right transfer along the seam real_eq; legs (1)/(2)/(3)
   transfer slot by slot). *)
Definition u5c_gap2_bridge (X : Real) (A B : nat -> Z) (clo : nat -> Q)
  (th : Q) (I : nat -> Real) (Hs : u5c_gap2_slot X A B clo th I)
  : u5c_ln2i_pade_supply X.
Proof.
  unfold u5c_ln2i_pade_supply, u5c_gap2_slot in *.
  destruct Hs as [Hth [Hap [Hclo [Hw [Hlo Hup]]]]].
  exists A. exists B. exists clo. exists th.
  split.
  - (* (1) th < 1. *)
    exact Hth.
  - split.
    + (* (2) 0 < |A n|. *)
      exact Hap.
    + split.
      * (* (3) 0 < clo n. *)
        exact Hclo.
      * split.
        -- (* (4) The lower-bound leg: clo_n <= |A_n * X - B_n| (Hlo moved by *)
           (* right transfer along the seam). *)
           intro n.
           exact (gap2_le_eq_r (real_const (clo n)) (I n)
                    (u5c_ln2b_line X A B n) (Hlo n) (Hw n)).
        -- (* (5) The upper-bound leg: |A_n * X - B_n| <= th^n (Hup moved by *)
           (* left transfer along the seam). *)
           intro n.
           exact (gap2_le_eq_l (I n) (real_const (q_pow th n))
                    (u5c_ln2b_line X A B n) (Hup n) (Hw n)).
Defined.

(* Head leg (2) transfer, instantiated: the canonical A-face conversion closes *)
(* (the later assembly substitutes lna_Amod/Aface: *)
(* gap2_abs_pos_transfer (Aface n#1) (Amod n#1) (the face-transfer QeqT) *)
(* gives head leg (2)). *)
Theorem gap2_head2_rewire : forall (a b : Q),
  QeqT a b -> (forall n : nat, QltT 0 (Qabs a)) ->
  forall n : nat, QltT 0 (Qabs b).
Proof. intros a b Heq H n. exact (gap2_abs_pos_transfer a b Heq (H n)). Qed.

(* =================== Extraction and assumption audits (the zero-admission recheck) =================== *)

Separate Extraction u5c_gap2_bridge gap2_le_eq_l gap2_le_eq_r.

Print Assumptions gap2_le_eq_l.
Print Assumptions gap2_le_eq_r.
Print Assumptions gap2_qeqT_trans.
Print Assumptions gap2_qeqT_mult_l.
Print Assumptions gap2_abs_pos_transfer.
Print Assumptions gap2_theta_45_lt1.
Print Assumptions gap2_head2_rewire.
Print Assumptions u5c_gap2_bridge.
