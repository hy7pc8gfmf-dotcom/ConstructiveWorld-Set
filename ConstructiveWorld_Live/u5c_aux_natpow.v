(* u5c_aux_natpow - nat power bounds and Q micro-conversion base library for
   the sqrt(2) closed-form separation constant family.

   Mission. Group A: four nat power bounds (12k^2 <= 2^(k+5), 4k^2 <= 2^(k+3),
   2k < 2^(k+5), 64 <= 2^(k+5), k >= 1) feeding the integer-exponent margin
   chain of the downstream assembly (delta < mu from 4b^2 <= 2^(b+3); uniform
   escape point e(n0) <= 2^-(b+5), n0 = b+3 >= 4). Group B: four Q
   micro-conversions (addition right cancellation, subtraction nonnegativity,
   Qle to QleT' bridge pair) for pointwise lossless rewriting between
   Prop-layer Qle reasoning and the Set-layer carrier QleT'. Statement faces
   carry canonical Set-layer carriers (NatLe / Id (Nat.ltb ...) true / Id on
   nat; QleT' on Q); premise positions keep Prop faces. Honest interface note:
   the 64-bound premise (1 <= k)%nat is mathematically necessary (at k = 0,
   2^5 = 32 < 64); the escape point n0 = den(q) + 3 >= 4 is unaffected.
   Dependencies. S01_BaseRing, S02_CauchyComplete (Id/NatLe carriers;
   NatLe_drop/NatLe_lift bridges; QleT'/Qle_bool/Qcompare faces and Qle
   bridges), read-only; Stdlib QArith, ZArith, Lia (nia).
   References. S02_CauchyComplete.v Qle_to_QleT', QleT'_to_Qle, qeq_imp_qle;
   S01_BaseRing.v NatLe_drop, NatLe_lift; downstream four-branch margin chain.
   Constructivity. Group A: induction with numeric bases k = 1,2,3, the
   definitional step law 2^(S k + c) = 2 * 2^(k+c), terminal split to nia;
   lia/nia restricted to auxiliary bounds and micro rewrites per the
   registered stock-freeze clause. Group B: Qcompare three-way constructive
   decision split by the positive denominator; bridges by Qle_bool case
   analysis without Leibniz equality; the two Qle-facing bridge stations
   keep their registered family faces verbatim (same shapes as the tree
   forms Qle_to_QleT' and QleT'_to_Qle).
   Build. Rocq 9.1: rocq c -native-compiler no -q -Q . "" u5c_aux_natpow.v in
   the module directory after sourcing the toolchain environment; extraction
   reports Obj.magic = 0. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Group A: nat power bounds (12-square / 4-square / 2k / 64).   *)
(* ============================================================ *)

(* Definitional shift: folding of 2 to a successor exponent (nat addition and
   power are definitional here). The successor is fully qualified as
   Datatypes.S because the S constant of S01_BaseRing shadows the bare S
   constructor. Canonical face: the Set-layer identity carrier Id. *)
Lemma u5c_pow2_shift : forall k c : nat, Id ((2 ^ (Datatypes.S k + c))%nat) ((2 * 2 ^ (k + c))%nat).
Proof. intros k c. exact id_refl. Qed.

(* Base bound: 32 <= 2^(k+5) for all k (induction on k; every fold step is
   non-decreasing). Canonical face: NatLe (Id-carried nat order). *)
Lemma u5c_pow32 : forall k : nat, NatLe 32 (2 ^ (k + 5))%nat.
Proof.
  intro k. apply NatLe_lift.
  induction k as [| k IH].
  - cbn. lia.
  - change (2 ^ (Datatypes.S k + 5))%nat with (2 * 2 ^ (k + 5))%nat. lia.
Qed.

(* 12-square bound: 12k^2 <= 2^(k+5) (k >= 1). Quadratic growth is swallowed
   by exponential doubling: (k+1)^2 <= 2k^2 preserves the step from k >= 4
   on, and k = 1,2,3 close by pointwise computation. *)
Lemma u5c_pow12 : forall k : nat, (1 <= k)%nat -> NatLe (12 * k * k) (2 ^ (k + 5))%nat.
Proof.
  intro k.
  induction k as [| k IH]; intro Hk.
  - apply NatLe_lift. lia.
  - apply NatLe_lift.
    destruct k as [|[|[|k]]].
    + cbn. lia.
    + cbn. lia.
    + cbn. lia.
    + assert (Hk' : (1 <= Datatypes.S (Datatypes.S (Datatypes.S k)))%nat) by lia.
      pose proof (NatLe_drop _ _ (IH Hk')) as IHp.
      assert (Hsh : forall a b : nat,
                    (2 ^ (Datatypes.S a + b))%nat = (2 * 2 ^ (a + b))%nat)
        by (intros; reflexivity).
      rewrite !Hsh in IHp.
      rewrite !Hsh.
      assert (E1 : (12 * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k))) * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))
                    <= 2 * (12 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S (Datatypes.S (Datatypes.S k))))%nat) by nia.
      lia.
Qed.

(* 4-square bound: 4k^2 <= 2^(k+3) (k >= 1). Same shape as the 12 bound:
   (k+3)^2 <= 2(k+2)^2 holds for all k >= 1, so the step is preserved
   already from k >= 1 on. *)
Lemma u5c_pow4 : forall k : nat, (1 <= k)%nat -> NatLe (4 * k * k) (2 ^ (k + 3))%nat.
Proof.
  intro k.
  induction k as [| k IH]; intro Hk.
  - apply NatLe_lift. lia.
  - apply NatLe_lift.
    destruct k as [|[|[|k]]].
    + cbn. lia.
    + cbn. lia.
    + cbn. lia.
    + assert (Hk' : (1 <= Datatypes.S (Datatypes.S (Datatypes.S k)))%nat) by lia.
      pose proof (NatLe_drop _ _ (IH Hk')) as IHp.
      assert (Hsh : forall a b : nat,
                    (2 ^ (Datatypes.S a + b))%nat = (2 * 2 ^ (a + b))%nat)
        by (intros; reflexivity).
      rewrite !Hsh in IHp.
      rewrite !Hsh.
      assert (E1 : (4 * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k))) * Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))
                    <= 2 * (4 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S (Datatypes.S (Datatypes.S k))))%nat) by nia.
      lia.
Qed.

(* 2k bound: 2k < 2^(k+5) for all k (the base 32 >= 2 leaves strict margin at
   every fold step). Canonical face: Id (Nat.ltb ...) true - the Id-carried
   nat strict order (the NatLt alias lives only in S06; the direct Id face is
   the same definitional carrier and keeps the Require closure minimal). *)
Lemma u5c_pow2b : forall k : nat, Id ((Nat.ltb (2 * k) (2 ^ (k + 5)))%nat) true.
Proof.
  intro k.
  assert (Hlt : (2 * k < 2 ^ (k + 5))%nat).
  { induction k as [| k IH].
    - cbn. lia.
    - change (2 ^ (Datatypes.S k + 5))%nat with (2 * 2 ^ (k + 5))%nat.
      pose proof (NatLe_drop 32 (2 ^ (k + 5))%nat (u5c_pow32 k)) as Hm.
      lia. }
  destruct (Nat.ltb (2 * k) (2 ^ (k + 5)))%nat eqn:E.
  - exact id_refl.
  - exfalso.
    apply (proj1 (Nat.ltb_ge (2 * k) (2 ^ (k + 5))%nat)) in E.
    lia.
Qed.

(* 64 bound: 64 <= 2^(k+5) (k >= 1). The base 32 folds once to reach 64; the
   premise-free form is false at k = 0, hence the premise (kept per the
   honest-interface disclosure in the header). *)
Lemma u5c_pow64 : forall k : nat, (1 <= k)%nat -> NatLe 64 (2 ^ (k + 5))%nat.
Proof.
  intros k Hk.
  apply NatLe_lift.
  destruct k as [|[|k]].
  - lia.
  - cbn. lia.
  - assert (Hsh : forall a b : nat,
                  (2 ^ (Datatypes.S a + b))%nat = (2 * 2 ^ (a + b))%nat)
      by (intros; reflexivity).
    rewrite !Hsh.
    pose proof (NatLe_drop 32 (2 ^ (k + 5))%nat (u5c_pow32 k)) as Hm. lia.
Qed.

(* ============================================================ *)
(* Group B: Q micro-conversions (addition right cancellation,          *)
(* subtraction nonnegativity, Qle <-> QleT' bridge pair).              *)
(* ============================================================ *)

(* Addition right cancellation: x + z <= y + z implies x <= y. After the Z
   cross-product expansion both sides divide by the common square
   (Qden z)^2; the positive-denominator split preserves order, and
   Pos2Z.inj_mul normalizes the Zpos(Pos.mul ...) shapes into Z products
   before nia. *)
Lemma u5c_qle_add_cancel_r : forall x y z : Q, QleT' (x + z) (y + z) -> QleT' x y.
Proof.
  intros x y z H.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ H) as Hle.
  destruct x as [qx zx]; destruct y as [qy zy]; destruct z as [qz zz].
  unfold Qle in Hle |- *.
  cbn [Qnum Qden Qplus] in Hle |- *.
  rewrite ?Pos2Z.inj_mul in Hle |- *.
  assert (Hz : (0 < Z.pos zz)%Z) by apply Pos2Z.is_pos.
  nia.
Qed.

(* Subtraction nonnegativity: s <= t implies 0 <= t - s. The cross-product
   numerator of t - s is qt*zs - qs*zt, which cancels term-by-term against
   the premise; linear close at the Z layer. *)
Lemma u5c_qle_sub_r : forall s t : Q, QleT' s t -> QleT' 0%Q ((t - s)%Q).
Proof.
  intros s t H.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ H) as Hle.
  destruct s as [qs zs]; destruct t as [qt zt].
  unfold Qle in Hle |- *.
  cbn [Qnum Qden Qminus Qopp Qplus] in Hle |- *.
  rewrite ?Pos2Z.inj_mul in Hle |- *.
  lia.
Qed.

(* Constructive direction: Qle -> QleT' (Z comparison three-way split plus
   exclusion of the Gt branch from Qle; no Leibniz equality needed). Qle_bool
   is fully qualified because the same-named stdlib QArith_base lemma (leb
   form) shadows the S02 decision version - this names the S02 decision
   definition face. Bridge station: the Qle premise position keeps its Prop
   face per the premise-position rule; statement carried verbatim in the
   registered family form (same shape as S02 Qle_to_QleT'). *)
Lemma u5c_qle_qleT' : forall x y : Q, Qle x y -> QleT' x y.
Proof.
  intros x y H.
  unfold QleT', S02_CauchyComplete.Qle_bool, Qcompare.
  unfold Qle in H.
  destruct (Qnum x * QDen y ?= Qnum y * QDen x)%Z eqn:E; simpl; try reflexivity.
  - exfalso. exact (H E).
Qed.

(* Resolution direction: QleT' -> Qle (Qle unfolds to the Z cross-product
   comparison different from Gt; the boolean reflection resolves branch by
   branch). Reverse-bridge station: statement carried verbatim in its
   registered family form (same shape as S02 QleT'_to_Qle); the Qle
   conclusion face is the mission face of the conversion bridge and is
   exempt from mechanical carrier mapping (mapping it would collapse the
   bridge into an identity). *)
Lemma u5c_qleT'_qle : forall x y : Q, QleT' x y -> Qle x y.
Proof.
  intros x y H.
  unfold QleT' in H.
  unfold S02_CauchyComplete.Qle_bool, Qcompare in H.
  unfold Qle.
  change ((Qnum x * QDen y ?= Qnum y * QDen x)%Z <> Gt).
  destruct (Qnum x * QDen y ?= Qnum y * QDen x)%Z eqn:E; simpl in H;
    try (inversion H); try (intro Hc; inversion Hc).
Qed.

Print Assumptions u5c_pow12.
Print Assumptions u5c_pow4.
Print Assumptions u5c_pow2b.
Print Assumptions u5c_pow64.
Print Assumptions u5c_qle_add_cancel_r.
Print Assumptions u5c_qle_sub_r.
Print Assumptions u5c_qle_qleT'.
Print Assumptions u5c_qleT'_qle.
