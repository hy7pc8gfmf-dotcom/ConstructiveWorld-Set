(* ConstructiveWorld-Set — rational-order lemma leg of the signed Pade approximation. *)

(** * UpReqPadeQLeg: order laws at the rational layer for the Pade chain..

    Mission.  Rational-layer order laws feeding the signed Pade approximation:
 positivity of the positive denominator [pql_pos_den_pos], propagation of
 Q equality through strict order ([pql_qlt0_eq_r], [pql_qlt_eq_l],
 [pql_qlt_eq_r]), strict addition bridges ([pql_qlt_add_r],
 [pql_qle_lt_add], [pql_qlt_le_add]), and natural-ratio monotonicity in
 [Z] ([pql_nat_ratio_mono], [pql_nat_ratio_mono2]).

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [ZArith], [Lia].
 Requires [S01_BaseRing] (the [Id] carrier) and [S02_CauchyComplete]
 ([QltT]/[QleT'] carriers) of this development; local [Z]-layer carrier
 bridges [ZLtT]/[ZLeT] are defined in-file.

    References.  This development, UpReqPadeQLeg.v, the baseline module in
 ConstructiveWorld-Main whose statement names are carried over here
 verbatim (statement-face Set-carrier completion: Qlt/Qle conclusions
 moved to [QltT]/[QleT']; [Z]-conclusions to the in-file [ZLtT]/[ZLeT]
 carriers; the former nia-based proofs replaced by monotonicity
 assemblies with [lia] linear closure).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqPadeQLeg.v]
      compiles cleanly (exit 0); artifact magic [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith Arith.Arith Lia ZArith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.

Local Open Scope Q_scope.
Local Open Scope Z_scope.

(* ==================================================================
   Local Set-carried bridges for the integer layer (same shape as the S01
   NatLe/NatLt pair): ZLtT/ZLeT := Id (Z.ltb/Z.leb ..) true with the
   lift/drop conversion pair. *)
(* ================================================================== *)
Definition Id_eq {A : Set} (x y : A) (H : Id x y) : x = y.
Proof. destruct H. apply eq_refl. Defined.

Definition eq_Id {A : Set} (x y : A) (H : x = y) : Id x y.
Proof. destruct H. apply id_refl. Defined.

Definition ZLtT (a b : Z) : Set := Id (Z.ltb a b) true.
Definition ZLeT (a b : Z) : Set := Id (Z.leb a b) true.

Lemma ZLtT_drop : forall a b : Z, ZLtT a b -> (a < b)%Z.
Proof. intros a b H. apply Z.ltb_lt. exact (Id_eq _ _ H). Defined.

Lemma ZLtT_lift : forall a b : Z, (a < b)%Z -> ZLtT a b.
Proof. intros a b H. exact (eq_Id _ _ (proj2 (Z.ltb_lt a b) H)). Defined.

Lemma ZLeT_drop : forall a b : Z, ZLeT a b -> (a <= b)%Z.
Proof. intros a b H. apply Z.leb_le. exact (Id_eq _ _ H). Defined.

Lemma ZLeT_lift : forall a b : Z, (a <= b)%Z -> ZLeT a b.
Proof. intros a b H. exact (eq_Id _ _ (proj2 (Z.leb_le a b) H)). Defined.

(* 正分母正性（Qden 是 positive，显式钉定，不依赖 zify 隐式） *)
Lemma pql_pos_den_pos : forall d : positive, ZLtT 0 (Z.pos d).
Proof. intros d. exact (ZLtT_lift 0 (Z.pos d) (Pos2Z.is_pos d)). Qed.

(* ============================================================ *)
(* 族 A 基肢：Qeq 右传（0 起点）：a == b ⟹ 0 < a ⟹ 0 < b               *)
(*   Z 面：na·db = nb·da ∧ 1 ≤ na ⊢ 0 < nb（反证 + 乘单调）。          *)
(* ============================================================ *)
Lemma pql_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> QltT 0 b.
Proof.
  intros a b Hab Ha.
  apply Qlt_to_QltT.
  destruct a as [na da]. destruct b as [nb db].
  unfold Qeq in Hab. unfold Qlt in Ha |- *.
  cbn [Qnum Qden] in Hab, Ha |- *.
  pose proof (ZLtT_drop 0 (Z.pos da) (pql_pos_den_pos da)) as Hda.
  assert (Hda0 : (0 <= Z.pos da)%Z) by lia.
  pose proof (ZLtT_drop 0 (Z.pos db) (pql_pos_den_pos db)) as Hdb.
  (* Ha/goal 中的 *1 与 *0 由 lia 线性归一：得 1 <= na，目标 0 < nb *)
  assert (Hna : (1 <= na)%Z) by lia.
  (* 主等式：na * db = nb * da（注意：Q_scope 下 == 是 Qeq，Z 面写 =） *)
  assert (Hmul : (na * Z.pos db = nb * Z.pos da)%Z) by exact Hab.
  assert (Hdb0 : (0 <= Z.pos db)%Z) by lia.
  (* 反证：nb <= 0 则 nb*da <= 0，与 na*db >= 1*db >= 1 矛盾 *)
  destruct (Z_le_gt_dec nb 0) as [Hn0 | Hn0].
  - exfalso.
    pose proof (Z.mul_le_mono_nonneg_r nb 0 (Z.pos da) Hda0 Hn0) as Hneg.
    pose proof (Z.mul_le_mono_nonneg_r 1 na (Z.pos db) Hdb0 Hna) as Hpos.
    lia.
  - lia.
Qed.

(* 族 A 右传肢：a == b ⟹ c < a ⟹ c < b
   Z 面：nc·da < na·dc，na·db = nb·da ⊢ nc·db < nb·dc
   （两边乘 db 正数，na·dc·db = nb·dc·da 换形，再消 da）。 *)
Lemma pql_qlt_eq_r : forall a b c : Q, a == b -> Qlt c a -> QltT c b.
Proof.
  intros a b c Hab Hlt.
  apply Qlt_to_QltT.
  destruct a as [na da]. destruct b as [nb db]. destruct c as [nc dc].
  unfold Qeq in Hab. unfold Qlt in Hlt |- *.
  cbn [Qnum Qden] in Hab, Hlt |- *.
  pose proof (ZLtT_drop 0 (Z.pos da) (pql_pos_den_pos da)) as Hda.
  assert (Hda0 : (0 <= Z.pos da)%Z) by lia.
  pose proof (ZLtT_drop 0 (Z.pos db) (pql_pos_den_pos db)) as Hdb.
  pose proof (ZLtT_drop 0 (Z.pos dc) (pql_pos_den_pos dc)) as Hdc.
  (* 换形恒等式（ring 只收恒等肢） *)
  assert (E1 : (na * Z.pos dc * Z.pos db = (na * Z.pos db) * Z.pos dc)%Z) by ring.
  assert (E2 : (nc * Z.pos da * Z.pos db = (nc * Z.pos db) * Z.pos da)%Z) by ring.
  assert (E3 : ((nb * Z.pos da) * Z.pos dc = nb * Z.pos dc * Z.pos da)%Z) by ring.
  rewrite Hab in E1.
  rewrite E3 in E1.
  (* Hlt 两边乘 db > 0 *)
  assert (Hm : (nc * Z.pos da * Z.pos db < na * Z.pos dc * Z.pos db)%Z).
  { apply (proj1 (Z.mul_lt_mono_pos_r (Z.pos db) (nc * Z.pos da) (na * Z.pos dc) Hdb)).
    lia. }
  rewrite E2 in Hm. rewrite E1 in Hm.
  (* Hm : (nc*db)*da < nb*dc*da，消正因子 da *)
  destruct (Z_le_gt_dec (nb * Z.pos dc) (nc * Z.pos db)) as [Hbad | Hgood].
  - exfalso.
    pose proof (Z.mul_le_mono_nonneg_r (nb * Z.pos dc) (nc * Z.pos db) (Z.pos da) Hda0 Hbad) as Hc.
    lia.
  - lia.
Qed.

(* 族 A 左传肢：a == b ⟹ a < c ⟹ b < c
   Z 面：na·dc < nc·da，na·db = nb·da ⊢ nb·dc < nc·db（副本同法）。 *)
Lemma pql_qlt_eq_l : forall a b c : Q, a == b -> Qlt a c -> QltT b c.
Proof.
  intros a b c Hab Hlt.
  apply Qlt_to_QltT.
  destruct a as [na da]. destruct b as [nb db]. destruct c as [nc dc].
  unfold Qeq in Hab. unfold Qlt in Hlt |- *.
  cbn [Qnum Qden] in Hab, Hlt |- *.
  pose proof (ZLtT_drop 0 (Z.pos da) (pql_pos_den_pos da)) as Hda.
  assert (Hda0 : (0 <= Z.pos da)%Z) by lia.
  pose proof (ZLtT_drop 0 (Z.pos db) (pql_pos_den_pos db)) as Hdb.
  pose proof (ZLtT_drop 0 (Z.pos dc) (pql_pos_den_pos dc)) as Hdc.
  assert (E1 : (na * Z.pos dc * Z.pos db = (na * Z.pos db) * Z.pos dc)%Z) by ring.
  assert (E2 : (nc * Z.pos da * Z.pos db = (nc * Z.pos db) * Z.pos da)%Z) by ring.
  assert (E3 : ((nb * Z.pos da) * Z.pos dc = nb * Z.pos dc * Z.pos da)%Z) by ring.
  assert (Hm : (na * Z.pos dc * Z.pos db < nc * Z.pos da * Z.pos db)%Z).
  { apply (proj1 (Z.mul_lt_mono_pos_r (Z.pos db) (na * Z.pos dc) (nc * Z.pos da) Hdb)).
    lia. }
  (* Hm 两端换形到同一单调乘法框：nb·dc·da < nc·db·da *)
  assert (T1 : (na * Z.pos dc * Z.pos db = nb * Z.pos dc * Z.pos da)%Z).
  { transitivity ((na * Z.pos db) * Z.pos dc).
    - ring.
    - rewrite Hab. ring. }
  assert (T2 : (nc * Z.pos da * Z.pos db = nc * Z.pos db * Z.pos da)%Z) by ring.
  rewrite T1, T2 in Hm.
  (* 消正因子 da：iff 形 Z.mul_lt_mono_pos_r 反向一跳直达目标 *)
  apply (proj2 (Z.mul_lt_mono_pos_r (Z.pos da) (nb * Z.pos dc) (nc * Z.pos db) Hda)).
  exact Hm.
Qed.

(* ============================================================ *)
(* 族 B 加法严格桥三件                                                *)
(* ============================================================ *)

(* Qlt 0 b ⟹ a < a + b
   Q 层装配：Qplus_lt_r （iff 形）+ (a+0)==a 环换 + 左传肢。 *)
Lemma pql_qlt_add_r : forall a b : Q, Qlt 0 b -> QltT a (a + b)%Q.
Proof.
  intros a b Hb.
  assert (Ht : Qlt (a + 0)%Q (a + b)%Q)
    by (apply (proj2 (Qplus_lt_r 0 b a)); exact Hb).
  assert (Heq : (a + 0)%Q == a%Q) by ring.
  exact (pql_qlt_eq_l (a + 0)%Q a (a + b)%Q Heq Ht).
Qed.

(* Qle 0 a ⟹ Qlt 0 b ⟹ 0 < a + b
   Q 层装配：Qplus_lt_r + 左传腵 + Qle_lt_trans。 *)
Lemma pql_qle_lt_add : forall a b : Q, Qle 0 a -> Qlt 0 b -> QltT 0 (a + b)%Q.
Proof.
  intros a b Ha Hb.
  assert (Ht : Qlt (a + 0)%Q (a + b)%Q)
    by (apply (proj2 (Qplus_lt_r 0 b a)); exact Hb).
  assert (Heq : (a + 0)%Q == a%Q) by ring.
  assert (Hlt2 : Qlt a (a + b)%Q)
    by (apply QltT_to_Qlt; exact (pql_qlt_eq_l (a + 0)%Q a (a + b)%Q Heq Ht)).
  apply Qlt_to_QltT. exact (Qle_lt_trans 0%Q a (a + b)%Q Ha Hlt2).
Qed.

(* Qlt 0 a ⟹ Qle 0 b ⟹ 0 < a + b（副本件，Qplus_lt_l 形） *)
Lemma pql_qlt_le_add : forall a b : Q, Qlt 0 a -> Qle 0 b -> QltT 0 (a + b)%Q.
Proof.
  intros a b Ha Hb.
  assert (Ht : Qlt (0 + b)%Q (a + b)%Q)
    by (apply (proj2 (Qplus_lt_l 0 a b)); exact Ha).
  assert (Heq : (0 + b)%Q == b%Q) by ring.
  assert (Hlt2 : Qlt b (a + b)%Q)
    by (apply QltT_to_Qlt; exact (pql_qlt_eq_l (0 + b)%Q b (a + b)%Q Heq Ht)).
  apply Qlt_to_QltT. exact (Qle_lt_trans 0%Q b (a + b)%Q Hb Hlt2).
Qed.

(* ============================================================ *)
(* 族 C 系数比单调 Nat/Z 肢（DenPos / DenPos12 原nia 位形状）           *)
(*   数学核：k < n ⟹ S(n−S k) ≤ S(2n−S k)·S k                          *)
(*     （链：X ≤ 2X ≤ 2Y ≤ Y·S k）；k=0 时 Y = 2X lia 直解。            *)
(* ============================================================ *)
Lemma pql_nat_ratio_mono2 :
  forall n k : nat, (k < n)%nat ->
    ZLeT (2 * Z.of_nat (Datatypes.S (n - Datatypes.S k)))
         (Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) * Z.of_nat (Datatypes.S k)).
Proof.
  intros n k Hk.
  apply ZLeT_lift.
  assert (H1 : (Z.of_nat (Datatypes.S (n - Datatypes.S k)) <= Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)))%Z) by lia.
  destruct k as [| k'].
  - lia.
  - assert (H2 : (Z.of_nat (Datatypes.S (2 * n - Datatypes.S (Datatypes.S k'))) * 2
                  <= Z.of_nat (Datatypes.S (2 * n - Datatypes.S (Datatypes.S k'))) * Z.of_nat (Datatypes.S (Datatypes.S k')))%Z).
    { apply (Z.mul_le_mono_nonneg_l 2%Z (Z.of_nat (Datatypes.S (Datatypes.S k')))
               (Z.of_nat (Datatypes.S (2 * n - Datatypes.S (Datatypes.S k'))))); lia. }
    assert (H3 : (Z.of_nat (Datatypes.S (n - Datatypes.S (Datatypes.S k'))) * 2
                  <= Z.of_nat (Datatypes.S (2 * n - Datatypes.S (Datatypes.S k'))) * 2)%Z).
    { apply (Z.mul_le_mono_nonneg_r (Z.of_nat (Datatypes.S (n - Datatypes.S (Datatypes.S k'))))
               (Z.of_nat (Datatypes.S (2 * n - Datatypes.S (Datatypes.S k')))) 2%Z); lia. }
    lia.
Qed.

Lemma pql_nat_ratio_mono :
  forall n k : nat, (k < n)%nat ->
    ZLeT (Z.of_nat (Datatypes.S (n - Datatypes.S k)))
         (Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) * Z.of_nat (Datatypes.S k)).
Proof.
  intros n k Hk.
  apply ZLeT_lift.
  assert (H1 : (Z.of_nat (Datatypes.S (n - Datatypes.S k))
                <= 2 * Z.of_nat (Datatypes.S (n - Datatypes.S k)))%Z) by lia.
  apply Z.le_trans with (2 * Z.of_nat (Datatypes.S (n - Datatypes.S k)))%Z.
  - exact H1.
  - exact (ZLeT_drop _ _ (pql_nat_ratio_mono2 n k Hk)).
Qed.

Print Assumptions pql_pos_den_pos.
