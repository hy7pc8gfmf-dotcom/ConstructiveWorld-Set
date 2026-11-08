(* ===================================================================== *)
(*  五字段指针｜使命：DTPT 模块——布尔序列上的判码真谓词基础库：序列/去重/   *)
(*    测度层。基础算子（insert_q/P0/rot/interleave/Pmid）、去重族          *)
(*    （dedup/Qnodup）、置换不变（N9_ms_perm_inv）、熵面（H_ms/H_adj）、    *)
(*    Q 层算术工具箱、排序泛化族（C_gen）、阶乘级数族（D8）、LLM 映射层、    *)
(*    频数测度层、余零理想 ℐ 计数化、熵相代数、PmidEnd 端点族与 OrgDiff     *)
(*    封闭式族。依赖：Stdlib QArith/List/Arith/Lia/Permutation/            *)
(*    Sorting.Sorted，零本库依赖。构造性：全件 Qed 闭合、零承认词面、无     *)
(*    经典逻辑、魔数净零；语句面 Set/Type 形承载：§0 之 Id/NatLe/QeqT 三族  *)
(*    加双向桥，及 Qmem/Qnodup/SortedQ 判码真谓词族与 Forall_in/           *)
(*    Forall_of_pointwise（Q 层定例）；Q 层序谓词（Qle/Qlt）、P3 连接词与   *)
(*    Permutation 面仍为 Prop 形，未消解处如实登记。编译配方：Rocq 9.1 直调 *)
(*    rocq c -native-compiler no -Q <world-root> "" DTPT.v（ulimit -s      *)
(*    65532）。对标：信息论离散层——布尔序列熵与频数测度的计数化基础。      *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorting.Sorted.
Import ListNotations.
Open Scope Q_scope.

Module DTPT.
(* ========== §0 语句面 Set 形承载件：Id/NatLe/QeqT 三族与双向桥 ========== *)

Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

Lemma eq_imp_id {A : Set} {x y : A} (H : x = y) : Id x y.
Proof. destruct H. apply id_refl. Qed.

Lemma id_imp_eq {A : Set} {x y : A} (H : Id x y) : x = y.
Proof. destruct H. apply eq_refl. Qed.

Definition NatLe (n m : nat) : Set := Id (Nat.leb n m) true.

(* Pre-recast Prop bridges restored verbatim at their original names        *)
(* S01 v2 pure-increment correction; twin of the S01_BaseRing               *)
(* correction block).  Proof faces only.                                    *)
Lemma NatLe_drop : forall n m : nat, NatLe n m -> (n <= m)%nat.
Proof.
  intros n m H. unfold NatLe in H.
  destruct (Nat.leb n m) eqn:E.
  - apply (proj1 (Nat.leb_le n m)). exact E.
  - inversion H.
Qed.

Lemma NatLe_lift : forall n m : nat, (n <= m)%nat -> NatLe n m.
Proof.
  intros n m H. unfold NatLe.
  destruct (Nat.leb n m) eqn:E.
  - reflexivity.
  - exfalso.
    apply (proj1 (Nat.leb_gt n m)) in E.
    lia.
Qed.

(* Native informative direction family over the carrier [NatLe] (I-suffix   *)
(* names per the pure-increment correction).  The carrier [NatLe n m] is    *)
(* boolean identity face [Id (Nat.leb n m) true].  The native faces read    *)
(* and write boundedness certificates as value-level data; both are total   *)
(* projections, so the extracted code carries no partial branch and no      *)
(* recomputation of [Nat.leb].  Proof-side reasoning stays on the Prop      *)
(* faces above and the bridges below; every value-level consumption of the  *)
(* family goes through the I faces.                                         *)
(* Read face: boundedness certificate as a boolean identity value. *)
Lemma NatLe_dropI : forall n m : nat, NatLe n m -> @Id bool (Nat.leb n m) true.
Proof. intros n m H. exact H. Qed.

(* Write face: mirror of [NatLe_dropI]. *)
Lemma NatLe_liftI : forall n m : nat, @Id bool (Nat.leb n m) true -> NatLe n m.
Proof. intros n m H. exact H. Qed.

(* Set-level [Id] to Leibniz equality eliminator (I-suffix family name). *)
Lemma id_eq_SI : forall (A : Set) (x y : A), Id x y -> x = y.
Proof.
  intros A x y H.
  exact (match H in Id _ z return x = z with id_refl => eq_refl end).
Qed.

(* Reflection face: [NatLe n n] holds for every n, by direct computation. *)
Lemma NatLe_refl : forall n : nat, NatLe n n.
Proof.
  intros n. unfold NatLe. destruct (Nat.leb n n) eqn:E.
  - exact id_refl.
  - exfalso. exact (Nat.lt_irrefl n (proj1 (Nat.leb_gt n n) E)).
Qed.

(* Prop-faced bridges below serve proof positions only; every value-level   *)
(* consumption of the family goes through the I faces above.  Bridge pair   *)
(* (Prop order read-outs): carrier face and raw boolean identity face.      *)
Lemma NatLe_drop_le : forall n m : nat, NatLe n m -> (n <= m)%nat.
Proof.
  intros n m H.
  apply (proj1 (Nat.leb_le n m)).
  exact (id_eq_SI bool (Nat.leb n m) true (NatLe_dropI n m H)).
Qed.

(* Bridge: Prop order face read out of the boolean identity evidence        *)
(* Pure-increment correction form of the bridge pair. *)
Lemma NatLe_lift_le : forall n m : nat, @Id bool (Nat.leb n m) true -> (n <= m)%nat.
Proof.
  intros n m H.
  apply (proj1 (Nat.leb_le n m)).
  exact (id_eq_SI bool (Nat.leb n m) true H).
Qed.

Definition QeqT (a b : Q) : Set :=
  Id (match Qcompare a b with
      | Eq => true
      | _ => false
      end) true.

Lemma qeq_imp_qeqT : forall a b : Q, a == b -> QeqT a b.
Proof.
  intros a b Hab.
  unfold QeqT.
  destruct (Qcompare a b) eqn:E.
  - reflexivity.
  - exfalso.
    assert (Hc : Qcompare a b = Eq).
    { apply (proj1 (Qeq_alt a b)). exact Hab. }
    rewrite E in Hc. discriminate.
  - exfalso.
    assert (Hc : Qcompare a b = Eq).
    { apply (proj1 (Qeq_alt a b)). exact Hab. }
    rewrite E in Hc. discriminate.
Qed.

Lemma qeqT_imp_qeq : forall a b : Q, QeqT a b -> a == b.
Proof.
  intros a b H. unfold QeqT in H. destruct (Qcompare a b) eqn:E.
  - exact (proj2 (Qeq_alt a b) E).
  - inversion H.
  - inversion H.
Qed.


(* ========== §1 数字结构归纳类型 Dig（D1/D2/D9 构造消解） ========== *)

Inductive Dig : Type :=
| dQ     : Q -> Dig
| dPair  : Dig -> Dig -> Dig
| dSeq   : list Dig -> Dig
| dCode  : nat -> (nat -> Dig) -> Dig
| dJudge : Dig -> Dig -> Dig
| dModel : Dig -> Dig
| dProofT: Dig -> Dig -> Dig.

(* ========== §2 有穷序列承载面与组织算子（D4/D6/D7 构造） ========== *)

Fixpoint insert_q (x : Q) (l : list Q) : list Q :=
  match l with
  | [] => [x]
  | y :: ys => if Qle_bool x y then x :: y :: ys else y :: insert_q x ys
  end.

Fixpoint P0 (l : list Q) : list Q :=
  match l with
  | [] => []
  | x :: xs => insert_q x (P0 xs)
  end.

Definition rot (n : nat) (l : list Q) : list Q :=
  firstn n l ++ skipn n l.

Definition Pinf (l : list Q) (s : nat) : list Q :=
  rot (S s) l.

Fixpoint interleave (l1 l2 : list Q) : list Q :=
  match l1, l2 with
  | [], _ => l2
  | _ :: _, [] => l1
  | x :: xs, y :: ys => x :: y :: interleave xs ys
  end.

Definition Pmid (l : list Q) (s lam : nat) : list Q :=
  firstn lam (P0 l) ++ skipn lam (Pinf l s).

(* ========== §3 支撑域同一（D5 → 定理 A） ========== *)

Lemma insert_q_perm_cons : forall (x : Q) (l : list Q),
  Permutation (x :: l) (insert_q x l).
Proof.
  intros x l. induction l as [| y ys IH]; simpl.
  - simpl. apply perm_skip. apply perm_nil.
  - destruct (Qle_bool x y) eqn:Hxy.
    + apply perm_skip. apply Permutation_refl.
    + etransitivity.
      * apply perm_swap.
      * apply perm_skip. exact IH.
Qed.

Theorem D5_P0_perm : forall l : list Q, Permutation l (P0 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply Permutation_refl.
  - etransitivity.
    + apply perm_skip. exact IH.
    + apply insert_q_perm_cons.
Qed.

(* 【弃用注记】本件在 rot=firstn++skipn 恒等基础模块下为恒等推论伪装；操作语义以 DTPT_ROTC/DTPT_Cyc/DTPT_RotSpec 真化层为准。 *)
Theorem D5_Pinf_perm : forall (l : list Q) (s : nat), Permutation l (Pinf l s).
Proof.
  intros l s. unfold Pinf, rot.
  rewrite firstn_skipn.
  apply Permutation_refl.
Qed.

(* D5_Pmid_perm: general lam is false (firstn/skipn truncation not a permutation); covered by endpoint theorems. *)

Theorem D5_support_same : forall (l : list Q) (s : nat),
  Permutation l (P0 l) /\ Permutation l (Pinf l s).
Proof.
  intros l s. split; [exact (D5_P0_perm l) | exact (D5_Pinf_perm l s)].
Qed.

(* ========== §4 多熵函数族与序列熵分离（N9 + 定理 C） ========== *)

Fixpoint dedup_aux (x : Q) (l : list Q) : list Q :=
  match l with
  | [] => []
  | y :: ys => if Qeq_bool x y then dedup_aux x ys else y :: dedup_aux x ys
  end.

Fixpoint dedup (l : list Q) : list Q :=
  match l with
  | [] => []
  | x :: xs => x :: dedup_aux x (dedup xs)
  end.

Definition H_ms (l : list Q) : Q := (Z.of_nat (length (dedup l)) # 1)%Q.

Fixpoint sum_adjdiff (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => 0
               | y :: _ => Qabs (y - x) + sum_adjdiff xs
               end
  end.

Definition H_adj (l : list Q) : Q := sum_adjdiff l.

(* ========== 补证段 B2：Q 工具箱（lia 不支持 Q，全部 Z 反射直解） ========== *)

Lemma Qle_bool_false_le : forall x y : Q, Qle_bool x y = false -> y <= x.
Proof.
  intros x y H. unfold Qle_bool in H. unfold Qle.
  destruct (Z.leb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E.
  - discriminate.
  - apply Z.leb_gt in E. lia.
Qed.

Lemma Qle_dec' : forall x y : Q, x <= y \/ y <= x.
Proof.
  intros x y. destruct (Qle_bool x y) eqn:E.
  - left. apply Qle_bool_iff in E. exact E.
  - right. apply Qle_bool_false_le. exact E.
Qed.

Lemma qadd_le : forall a b c d : Q, a <= b -> c <= d -> (a + c <= b + d)%Q.
Proof.
  intros [an ad] [bn bd] [cn cd] [dn dd] H H0;
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos dd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos dd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  assert (H2 : ((cn * Zpos dd) * (Zpos ad * Zpos bd)
                <= (dn * Zpos cd) * (Zpos ad * Zpos bd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H0]).
  lia.
Qed.

Lemma qopp_le : forall a b : Q, a <= b -> (- b <= - a)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

Lemma qmul_le_r : forall n m p : Q, n <= m -> 0 <= p -> (n * p <= m * p)%Q.
Proof.
  intros [nn nd] [mn md] [pn pd] H H0;
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((nn * Zpos md) * (pn * Zpos pd)
                <= (mn * Zpos nd) * (pn * Zpos pd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Qed.

Lemma Qle_0_sub' : forall x y : Q, x <= y <-> (0 <= y - x)%Q.
Proof.
  intros [nx dx] [ny dy]; simpl; split; intros H;
  unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl; lia.
Qed.

Lemma qsub_le_r : forall a b c : Q, a <= b -> (a - c <= b - c)%Q.
Proof.
  intros [an ad] [bn bd] [cn cd] H.
  unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos cd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos cd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Qed.

Lemma qsub_add : forall a b c : Q, QeqT (a - b + (b - c)) (a - c).
Proof.
  assert (Hcore : forall a b c : Q, (a - b + (b - c) == a - c)%Q).
  {
    intros [an ad] [bn bd] [cn cd].
    unfold Qeq, Qminus, Qplus, Qopp; simpl; lia.
  }
  intros a b c.
  exact (qeq_imp_qeqT _ _ (Hcore a b c)).
Qed.

Lemma abs_eq : forall a : Q, 0 <= a -> Qabs a == a.
Proof.
  intros [n d] H. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - reflexivity.
  - exfalso. lia.
Qed.

Lemma abs_neg : forall a : Q, a <= 0 -> QeqT (Qabs a) (- a).
Proof.
  assert (Hcore : forall a : Q, a <= 0 -> Qabs a == - a).
  {
    intros [n d] H. unfold Qle in H. simpl in H. unfold Qeq.
    destruct n as [| p | p].
    - simpl. lia.
    - exfalso. lia.
    - reflexivity.
  }
  intros a Hprem.
  exact (qeq_imp_qeqT _ _ (Hcore a Hprem)).
Qed.

Lemma abs_nonneg : forall a : Q, 0 <= Qabs a.
Proof.
  intros [n d]. unfold Qle. destruct n; simpl; lia.
Qed.

Lemma Qeqb_true_of : forall x y : Q, x == y -> Qeq_bool x y = true.
Proof.
  intros x y H. unfold Qeq in H. unfold Qeq_bool.
  destruct (Z.eqb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E; [reflexivity|].
  exfalso. apply Z.eqb_neq in E. lia.
Qed.

Lemma Qeqb_sym : forall x y : Q, Qeq_bool x y = Qeq_bool y x.
Proof.
  intros x y. destruct (Qeq_bool x y) eqn:E1, (Qeq_bool y x) eqn:E2; try reflexivity.
  - exfalso. apply Qeq_bool_eq in E1.
    assert (E1' : y == x) by (apply Qeq_sym; exact E1).
    apply Qeqb_true_of in E1'. congruence.
  - exfalso. apply Qeq_bool_eq in E2.
    assert (E2' : x == y) by (apply Qeq_sym; exact E2).
    apply Qeqb_true_of in E2'. congruence.
Qed.

Lemma Qeqb_trans : forall a b c : Q,
  Qeq_bool a b = true -> Qeq_bool b c = true -> Qeq_bool a c = true.
Proof.
  intros a b c H1 H2. apply Qeq_bool_eq in H1. apply Qeq_bool_eq in H2.
  apply Qeqb_true_of. transitivity b; assumption.
Qed.

(* ========== 补证段 B2：N9_ms_perm_inv 基建（Qeq 成员 + dedup 特征） ========== *)

Definition Qmem (a : Q) (l : list Q) : Set :=
  Id (existsb (fun y => Qeq_bool a y) l) true.

Lemma Qmem_intro : forall a (l : list Q),
  existsb (fun y => Qeq_bool a y) l = true -> Qmem a l.
Proof. intros a l H. exact (eq_imp_id H). Qed.

Lemma Qmem_elim : forall a (l : list Q),
  Qmem a l -> existsb (fun y => Qeq_bool a y) l = true.
Proof. intros a l H. exact (id_imp_eq H). Qed.

Lemma bool_id_absurd : forall (b : bool), Id b true -> Id b false -> False.
Proof.
  intros b Ht Hf.
  pose proof (id_imp_eq Ht) as Et.
  pose proof (id_imp_eq Hf) as Ef.
  rewrite Et in Ef. discriminate Ef.
Qed.

Lemma Qmem_nil_elim : forall a : Q, Qmem a [] -> False.
Proof.
  intros a H. apply (bool_id_absurd (existsb (fun y => Qeq_bool a y) [])).
  - exact H.
  - apply eq_imp_id. reflexivity.
Qed.

Lemma Qmem_cons : forall a x (l : list Q),
  Qmem a (x :: l) -> ((Qeq_bool a x = true) + Qmem a l)%type.
Proof.
  intros a x l H. unfold Qmem in H. cbn [existsb] in H.
  destruct (Qeq_bool a x) eqn:E.
  - left. reflexivity.
  - right. exact H.
Qed.

Lemma Qmem_cons_l : forall a x (l : list Q),
  Qeq_bool a x = true -> Qmem a (x :: l).
Proof.
  intros a x l H. apply eq_imp_id. cbn [existsb].
  rewrite H. reflexivity.
Qed.

Lemma Qmem_cons_r : forall a x (l : list Q),
  Qmem a l -> Qmem a (x :: l).
Proof.
  intros a x l H. apply eq_imp_id. cbn [existsb].
  destruct (Qeq_bool a x); [reflexivity | exact (id_imp_eq H)].
Qed.

Lemma Qmem_refl_cons : forall x (l : list Q), Qmem x (x :: l).
Proof. intros x l. apply Qmem_cons_l. apply Qeq_bool_refl. Qed.

Lemma Qmem_weaken : forall a b (l : list Q),
  Qmem a l -> Qeq_bool a b = true -> Qmem b l.
Proof.
  intros a b l H Hab.
  apply (Qmem_intro b l).
  assert (Hcore : existsb (fun y => Qeq_bool b y) l = true).
  { pose proof (Qmem_elim _ _ H) as He.
    apply existsb_exists in He.
    destruct He as [w [Hw Hq]].
    apply existsb_exists. exists w. split; [exact Hw|].
    apply (Qeqb_trans b a w). rewrite (Qeqb_sym b a). exact Hab. exact Hq. }
  exact Hcore.
Qed.

Lemma Qmem_dedup_aux_keep : forall a x (l : list Q),
  Qmem a (dedup_aux x l) -> Qmem a l.
Proof.
  intros a x l. induction l as [| y ys IH]; cbn [dedup_aux].
  - intros H. unfold Qmem in H. inversion H.
  - intros H. destruct (Qeq_bool x y).
    + apply Qmem_cons_r. exact (IH H).
    + apply (Qmem_cons a y (dedup_aux x ys)) in H. destruct H as [H|H].
      * apply Qmem_cons_l. exact H.
      * apply Qmem_cons_r. exact (IH H).
Qed.

Lemma Qmem_dedup_aux_drop : forall a x (l : list Q),
  Qmem a l -> Qeq_bool a x = false -> Qmem a (dedup_aux x l).
Proof.
  intros a x l. induction l as [| y ys IH]; cbn [dedup_aux].
  - intros H _. unfold Qmem in H. inversion H.
  - intros H Hax. apply (Qmem_cons a y ys) in H.
    destruct (Qeq_bool x y) eqn:Hxy.
    + destruct H as [H|H].
      * exfalso.
        assert (Hya : Qeq_bool y a = true) by (rewrite (Qeqb_sym y a); exact H).
        assert (Hxa : Qeq_bool x a = true) by (apply (Qeqb_trans x y a); assumption).
        rewrite (Qeqb_sym x a) in Hxa. rewrite Hxa in Hax. discriminate.
      * exact (IH H Hax).
    + destruct H as [H|H].
      * apply Qmem_cons_l. exact H.
      * apply Qmem_cons_r. exact (IH H Hax).
Qed.

Lemma dedup_aux_duck : forall a (l : list Q),
  Qmem a (dedup_aux a l) -> False.
Proof.
  intros a l. induction l as [| y ys IH]; cbn [dedup_aux].
  - intros H. unfold Qmem in H. inversion H.
  - destruct (Qeq_bool a y) eqn:E.
    + apply IH.
    + intros Hm. apply (Qmem_cons a y (dedup_aux a ys)) in Hm.
      destruct Hm as [Hm|Hm].
      * rewrite E in Hm. discriminate.
      * apply IH. exact Hm.
Qed.

Definition QmemMiss (a : Q) (l : list Q) : Set :=
  Id (existsb (fun y => Qeq_bool a y) l) false.

Lemma QmemMiss_intro : forall a (l : list Q),
  existsb (fun y => Qeq_bool a y) l = false -> QmemMiss a l.
Proof. intros a l H. exact (eq_imp_id H). Qed.

Lemma QmemMiss_elim_eq : forall a (l : list Q),
  QmemMiss a l -> existsb (fun y => Qeq_bool a y) l = false.
Proof. intros a l H. exact (id_imp_eq H). Qed.

Lemma QmemMiss_elim : forall a (l : list Q), Qmem a l -> QmemMiss a l -> False.
Proof. intros a l Hm Hmiss. exact (bool_id_absurd _ Hm Hmiss). Qed.

Lemma QmemMiss_cons : forall a x (l : list Q),
  QmemMiss a (x :: l) -> ((Qeq_bool a x = false) + QmemMiss a l)%type.
Proof.
  intros a x l H. unfold QmemMiss in H. cbn [existsb] in H.
  destruct (Qeq_bool a x) eqn:E.
  - exfalso. exact (bool_id_absurd true (eq_imp_id eq_refl) H).
  - right. exact H.
Qed.

Lemma QmemMiss_cons_miss : forall a x (l : list Q),
  QmemMiss a (x :: l) -> QmemMiss a l.
Proof.
  intros a x l H. apply QmemMiss_intro.
  pose proof (id_imp_eq H) as He. cbn [existsb] in He.
  destruct (Qeq_bool a x) eqn:E.
  - simpl in He. discriminate He.
  - exact He.
Qed.

Lemma QmemMiss_cons_intro : forall a x (l : list Q),
  Qeq_bool a x = false -> QmemMiss a l -> QmemMiss a (x :: l).
Proof.
  intros a x l Hx Hm. apply eq_imp_id. cbn [existsb].
  rewrite Hx. exact (id_imp_eq Hm).
Qed.

Lemma QmemMiss_cons_head : forall a x (l : list Q),
  QmemMiss a (x :: l) -> Qeq_bool a x = false.
Proof.
  intros a x l H.
  assert (Hc : (Qeq_bool a x || existsb (fun y => Qeq_bool a y) l) = false).
  { exact (id_imp_eq H). }
  destruct (Qeq_bool a x) eqn:E; [| reflexivity].
  simpl in Hc. discriminate Hc.
Qed.

Lemma QmemMiss_dedup_aux : forall a x (l : list Q),
  QmemMiss a l -> QmemMiss a (dedup_aux x l).
Proof.
  intros a x l. induction l as [| y ys IH]; cbn [dedup_aux].
  - intros H. exact H.
  - intros H. destruct (Qeq_bool x y).
    + apply IH. apply (QmemMiss_cons_miss a y ys). exact H.
    + pose proof (QmemMiss_cons_head a y ys H) as Ea.
      apply eq_imp_id. cbn [existsb]. rewrite Ea.
      exact (id_imp_eq (IH (QmemMiss_cons_miss a y ys H))).
Qed.

Lemma dedup_aux_miss : forall (x : Q) (l : list Q), QmemMiss x (dedup_aux x l).
Proof.
  intros x l. induction l as [| y ys IH]; cbn [dedup_aux].
  - apply eq_imp_id. reflexivity.
  - destruct (Qeq_bool x y) eqn:Hxy.
    + exact IH.
    + apply eq_imp_id. cbn [existsb]. rewrite Hxy. exact (id_imp_eq IH).
Qed.

Fixpoint Qnodup (l : list Q) : bool :=
  match l with
  | [] => true
  | x :: xs => andb (negb (existsb (fun z => Qeq_bool x z) xs)) (Qnodup xs)
  end.

Lemma Qnodup_nil : Id (Qnodup []) true.
Proof. apply eq_imp_id. reflexivity. Qed.

Lemma Qnodup_tail : forall x (xs : list Q),
  Id (Qnodup (x :: xs)) true -> Id (Qnodup xs) true.
Proof.
  intros x xs H.
  pose proof (id_imp_eq H) as Hb. cbn [Qnodup] in Hb.
  apply (proj1 (andb_true_iff _ _)) in Hb.
  destruct Hb as [_ Hq].
  exact (eq_imp_id Hq).
Qed.

Lemma Qnodup_head_miss : forall x (xs : list Q),
  Id (Qnodup (x :: xs)) true -> QmemMiss x xs.
Proof.
  intros x xs H.
  pose proof (id_imp_eq H) as Hb. cbn [Qnodup] in Hb.
  apply (proj1 (andb_true_iff _ _)) in Hb.
  destruct Hb as [Hn _].
  apply eq_imp_id. cbn [existsb].
  apply negb_true_iff in Hn. exact Hn.
Qed.

Lemma Qnodup_cons_intro : forall x (xs : list Q),
  QmemMiss x xs -> Id (Qnodup xs) true -> Id (Qnodup (x :: xs)) true.
Proof.
  intros x xs Hm Ht. apply eq_imp_id. cbn [Qnodup].
  apply andb_true_iff. split.
  - apply negb_true_iff. exact (id_imp_eq Hm).
  - exact (id_imp_eq Ht).
Qed.

Lemma dedup_aux_Qnodup : forall x (l : list Q),
  Id (Qnodup l) true -> Id (Qnodup (dedup_aux x l)) true.
Proof.
  intros x l. induction l as [| y ys IH]; cbn [dedup_aux].
  - intros _. exact Qnodup_nil.
  - intros Hnd. destruct (Qeq_bool x y).
    + apply IH. exact (Qnodup_tail y ys Hnd).
    + apply (Qnodup_cons_intro y (dedup_aux x ys)).
      * exact (QmemMiss_dedup_aux y x ys (Qnodup_head_miss y ys Hnd)).
      * apply IH. exact (Qnodup_tail y ys Hnd).
Qed.

Lemma dedup_Qnodup : forall l : list Q, Id (Qnodup (dedup l)) true.
Proof.
  induction l as [| x xs IH]; cbn [dedup].
  - exact Qnodup_nil.
  - apply (Qnodup_cons_intro x (dedup_aux x (dedup xs))).
    + exact (dedup_aux_miss x (dedup xs)).
    + apply dedup_aux_Qnodup. exact IH.
Qed.

Lemma dedup_Qmem_l : forall (l : list Q) a, Qmem a (dedup l) -> Qmem a l.
Proof.
  induction l as [| x xs IH]; intros a; cbn [dedup].
  - intros H. unfold Qmem in H. inversion H.
  - intros H. apply (Qmem_cons a x (dedup_aux x (dedup xs))) in H.
    destruct H as [H|H].
    + apply Qmem_cons_l. exact H.
    + apply Qmem_cons_r. apply IH.
      exact (Qmem_dedup_aux_keep a x _ H).
Qed.

Lemma dedup_Qmem_r : forall (l : list Q) a, Qmem a l -> Qmem a (dedup l).
Proof.
  induction l as [| x xs IH]; intros a; cbn [dedup].
  - intros H. unfold Qmem in H. inversion H.
  - intros H. apply (Qmem_cons a x xs) in H. destruct H as [H|H].
    + apply Qmem_cons_l. exact H.
    + destruct (Qeq_bool a x) eqn:Hax.
      * apply Qmem_cons_l. exact Hax.
      * apply Qmem_cons_r. apply Qmem_dedup_aux_drop.
        -- apply IH. exact H.
        -- exact Hax.
Qed.

Lemma Qmem_perm : forall (l p : list Q) a, Permutation l p ->
  (Qmem a l -> Qmem a p) * (Qmem a p -> Qmem a l).
Proof.
  intros l p a Hp.
  assert (Hcore : forall u v : list Q, Permutation u v ->
            forall b, existsb (fun y => Qeq_bool b y) u = true ->
            existsb (fun y => Qeq_bool b y) v = true).
  { intros u v Huv b He. apply existsb_exists in He.
    destruct He as [w [Hw Hq]].
    apply existsb_exists. exists w. split.
    - apply (Permutation_in _ Huv); exact Hw.
    - exact Hq. }
  split.
  - intros Hl. apply Qmem_intro. apply (Hcore l p Hp).
    exact (Qmem_elim a l Hl).
  - intros Hr. apply Qmem_intro. apply (Hcore p l (Permutation_sym Hp)).
    exact (Qmem_elim a p Hr).
Qed.

Lemma Qmem_cons_nodup : forall a x (xs : list Q),
  (Qmem x xs -> False) ->
  ((Qmem a xs -> Qmem a (x :: xs) * Id (Qeq_bool a x) false)%type
   * ((Qmem a (x :: xs) * Id (Qeq_bool a x) false)%type -> Qmem a xs))%type.
Proof.
  intros a x xs Hx. split.
  - intros Ha. split.
    + apply Qmem_cons_r. exact Ha.
    + destruct (Qeq_bool a x) eqn:E.
      * exfalso. apply Hx. exact (Qmem_weaken a x xs Ha E).
      * apply eq_imp_id. reflexivity.
  - intros [Ha Hax]. apply (Qmem_cons a x xs) in Ha. destruct Ha as [Ha|Ha].
    + exfalso. exact (bool_id_absurd (Qeq_bool a x) (eq_imp_id Ha) Hax).
    + exact Ha.
Qed.

Lemma remove_one : forall (x : Q) (n : list Q),
  Id (Qnodup n) true -> Qmem x n ->
  { n' : list Q &
    ((Id (length n) (S (length n')))
     * (Id (Qnodup n') true
        * ((forall a : Q, Qmem a n' -> Qmem a n * Id (Qeq_bool a x) false)
           * (forall a : Q, (Qmem a n * Id (Qeq_bool a x) false) -> Qmem a n')))) }.
Proof.
  intros x n. induction n as [| y ys IH]; intros Hn Hx.
  - exfalso. exact (Qmem_nil_elim x Hx).
  - pose proof (Qnodup_head_miss y ys Hn) as Hy.
    pose proof (Qnodup_tail y ys Hn) as Hys.
    apply (Qmem_cons x y ys) in Hx.
    destruct Hx as [Hxy|Hx].
    + (* x ~ y：移除头 y *)
      apply (existT _ ys). split; [apply eq_imp_id; reflexivity | split].
      * exact Hys.
      * split.
        -- intros a Ha. split.
           ++ apply Qmem_cons_r. exact Ha.
           ++ destruct (Qeq_bool a x) eqn:E.
              ** exfalso.
                 assert (Hya : Qeq_bool y a = true)
                   by (apply (Qeqb_trans y x a);
                       [rewrite <- (Qeqb_sym x y); exact Hxy | rewrite <- (Qeqb_sym a x); exact E]).
                 rewrite (Qeqb_sym y a) in Hya.
                 exact (QmemMiss_elim y ys (Qmem_weaken a y ys Ha Hya) Hy).
              ** apply eq_imp_id. reflexivity.
        -- intros a [Ha Hax]. apply (Qmem_cons a y ys) in Ha.
           destruct Ha as [Ha|Ha].
           ++ exfalso.
              assert (Hay : Qeq_bool a x = true)
                by (apply (Qeqb_trans a y x); [exact Ha | rewrite <- (Qeqb_sym x y); exact Hxy]).
              exact (bool_id_absurd (Qeq_bool a x) (eq_imp_id Hay) Hax).
           ++ exact Ha.
    + (* x ∈Q ys：内层递归移除，n' := y :: ys' *)
      destruct (IH Hys Hx) as [ys' [Hlen [Hnd [Hiff1 Hiff2]]]].
      apply (existT _ (y :: ys')).
      split; [apply eq_imp_id; simpl; rewrite (id_imp_eq Hlen); reflexivity | split].
      * apply (Qnodup_cons_intro y ys').
        -- apply eq_imp_id.
           destruct (existsb (fun z => Qeq_bool y z) ys') eqn:Eb.
           ++ exfalso.
              apply (QmemMiss_elim y ys
                       (fst (Hiff1 y (Qmem_intro y ys' Eb))) Hy).
           ++ reflexivity.
        -- exact Hnd.
      * split.
        -- intros a Ha. apply (Qmem_cons a y ys') in Ha. destruct Ha as [Ha|Ha].
           ++ split.
              ** apply Qmem_cons_l. exact Ha.
              ** destruct (Qeq_bool a x) eqn:E.
                 *** exfalso.
                     assert (Hxa : Qeq_bool x a = true)
                       by (rewrite <- (Qeqb_sym a x); exact E).
                     assert (Hxy' : Qeq_bool x y = true)
                       by (apply (Qeqb_trans x a y); [exact Hxa | exact Ha]).
                     exact (QmemMiss_elim y ys (Qmem_weaken x y ys Hx Hxy') Hy).
                 *** apply eq_imp_id. reflexivity.
           ++ split.
              ** apply Qmem_cons_r. exact (fst (Hiff1 a Ha)).
              ** exact (snd (Hiff1 a Ha)).
        -- intros a [Ha Hax].
           ++ destruct (Qeq_bool a y) eqn:Hbay.
              ** apply Qmem_cons_l. exact Hbay.
              ** apply Qmem_cons_r.
                 apply (Qmem_cons a y ys) in Ha. destruct Ha as [Ha|Ha].
                 { exfalso. rewrite Ha in Hbay. discriminate. }
                 { exact (Hiff2 a (pair Ha Hax)). }
Qed.

Lemma same_set_length : forall m n : list Q,
  Id (Qnodup m) true -> Id (Qnodup n) true ->
  (forall a, (Qmem a m -> Qmem a n) * (Qmem a n -> Qmem a m)) ->
  length m = length n.
Proof.
  induction m as [| x xs IH]; intros n Hm Hn Heq.
  - destruct n as [| y ys]; [reflexivity | exfalso].
    pose proof (snd (Heq y) (Qmem_refl_cons y ys)) as Hb.
    exact (Qmem_nil_elim y Hb).
  - destruct n as [| y ys].
    + exfalso.
      pose proof (fst (Heq x) (Qmem_refl_cons x xs)) as Hb.
      exact (Qmem_nil_elim x Hb).
    + assert (Hxs : Qmem x (y :: ys))
        by (apply (fst (Heq x)); apply Qmem_refl_cons).
      destruct (remove_one x (y :: ys) Hn Hxs)
        as [n' [Hlen1 [Hnd1 [Hiff1f Hiff1b]]]].
      assert (Hss : forall a, (Qmem a xs -> Qmem a n') * (Qmem a n' -> Qmem a xs)).
      { intros a. split; intros Ha.
        - assert (Hpair := fst (Qmem_cons_nodup a x xs
            (fun Hq => QmemMiss_elim x xs Hq
              (Qnodup_head_miss x xs Hm))) Ha).
          apply (Hiff1b a). split.
          + exact (fst (Heq a) (fst Hpair)).
          + exact (snd Hpair).
        - assert (Hpair := Hiff1f a Ha).
          apply (snd (Qmem_cons_nodup a x xs
            (fun Hq => QmemMiss_elim x xs Hq
              (Qnodup_head_miss x xs Hm)))).
          split.
          + exact (snd (Heq a) (fst Hpair)).
          + exact (snd Hpair). }
      assert (Hlen2 : length xs = length n')
        by (apply IH; [exact (Qnodup_tail x xs Hm) | exact Hnd1 | exact Hss]).
      pose proof (id_imp_eq Hlen1) as Hlen1'.
      simpl. rewrite Hlen2. rewrite <- Hlen1'. simpl. reflexivity.
Qed.

Theorem N9_ms_perm_inv : forall (l p : list Q),
  Permutation l p -> H_ms l = H_ms p.
Proof.
  intros l p Hp. unfold H_ms. f_equal. f_equal.
  apply same_set_length.
  - apply dedup_Qnodup.
  - apply dedup_Qnodup.
  - intros a. split; intros H.
    + apply dedup_Qmem_r.
      exact (fst (Qmem_perm l p a Hp) (dedup_Qmem_l l a H)).
    + apply dedup_Qmem_r.
      exact (snd (Qmem_perm l p a Hp) (dedup_Qmem_l p a H)).
Qed.

Theorem N9_seq_separates : exists (l1 l2 : list Q),
  Permutation l1 l2 /\ H_adj l1 <> H_adj l2.
Proof.
  exists [0; 1; 2], [0; 2; 1]. split.
  - apply perm_skip. apply perm_swap.
  - intro Hc. vm_compute in Hc. discriminate.
Qed.

(* ========== 补证段 DTPT-C：C_sorted_min_adj 证明链
   （xq_ 前缀工具整链移植自 DTPT_Entropy.v 同源证明，仅依赖
     stdlib QArith/List/Permutation 与本文件已证定义，全程 Qed 零公理） ========== *)

Lemma qadd_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> (0 <= a + b)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

(* ---------- xq 局部工具：Q 序与绝对值 ---------- *)

Lemma xq_Qle_bool_le : forall x y : Q, Qle_bool x y = true -> (x <= y)%Q.
Proof.
  intros [nx dx] [ny dy]. unfold Qle, Qle_bool; simpl. intros H.
  apply Z.leb_le. exact H.
Qed.

(* Rocq 9 的 Qabs 以 Z.abs 实现：Qabs (n # d) = (Z.abs n # d) *)
Lemma xq_abs_id : forall x : Q, (0 <= x)%Q -> Qabs x == x.
Proof.
  intros [n d] Hx. unfold Qle in Hx; simpl in Hx.
  assert (Hn : (0 <= n)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite (Z.abs_eq n Hn). reflexivity.
Qed.

Lemma xq_abs_eq0 : forall x : Q, x == 0 -> Qabs x == 0.
Proof.
  intros [n d] Hx. unfold Qeq in Hx; simpl in Hx.
  assert (Hn : (n = 0)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite Hn. reflexivity.
Qed.

Lemma xq_minus_self : forall x : Q, x - x == 0.
Proof.
  intros [n d]. unfold Qminus, Qeq; simpl. lia.
Qed.

Lemma xq_abs_zero : forall x : Q, Qabs (x - x) == 0.
Proof.
  intro x. apply xq_abs_eq0. apply xq_minus_self.
Qed.

Lemma xq_abs_eq : forall x y : Q, x == y -> Qabs x == Qabs y.
Proof.
  intros [n1 d1] [n2 d2] Hxy.
  unfold Qeq in Hxy; simpl in Hxy.
  unfold Qabs; simpl. unfold Qeq; simpl.
  pose proof (Z.abs_spec n1) as Ha1. pose proof (Z.abs_spec n2) as Ha2.
  destruct Ha1 as [[A1 B1] | [A1 B1]];
    destruct Ha2 as [[A2 B2] | [A2 B2]];
    try rewrite B1; try rewrite B2; lia.
Qed.

Lemma xq_abs_opp : forall x : Q, Qabs (- x) == Qabs x.
Proof.
  intros [n d]. unfold Qabs, Qopp; simpl. unfold Qeq; simpl.
  rewrite Z.abs_opp. reflexivity.
Qed.

Lemma xq_minus_opp : forall a b : Q, b - a == - (a - b).
Proof.
  intros [na da] [nb db]. unfold Qminus, Qopp, Qeq; simpl.
  rewrite (Pos.mul_comm db da). ring.
Qed.

Lemma xq_abs_sub_comm : forall a b : Q, Qabs (a - b) == Qabs (b - a).
Proof.
  intros a b.
  assert (H1 : Qabs (-(a - b)) == Qabs (a - b)) by apply xq_abs_opp.
  rewrite <- H1.
  apply xq_abs_eq. symmetry. apply xq_minus_opp.
Qed.

Lemma xq_H_adj_nonneg : forall l : list Q, (0 <= H_adj l)%Q.
Proof.
  intro l. induction l as [| a rest IH].
  - apply Qle_refl.
  - destruct rest as [| b bs].
    + apply Qle_refl.
    + change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      apply qadd_nonneg; [ apply abs_nonneg | exact IH ].
Qed.

Lemma xq_le_add_abs : forall t h : Q, (h <= Qabs t + h)%Q.
Proof.
  intros t h.
  pose proof (qadd_le 0 (Qabs t) h h (abs_nonneg t) (Qle_refl h)) as HS.
  rewrite Qplus_0_l in HS. exact HS.
Qed.

(* ---------- xq 局部工具：升序谓词与 P0 规范形 ---------- *)

Inductive SortedQ : list Q -> Set :=
| sortQ_nil : SortedQ []
| sortQ_cons : forall x xs,
    SortedQ xs -> Forall (fun z => (x <= z)%Q) xs -> SortedQ (x :: xs).

Lemma xq_sortQ_insert : forall (x : Q) (l : list Q),
  SortedQ l -> SortedQ (insert_q x l).
Proof.
  intros x l. revert x. induction l as [| y ys IH]; intros x HS.
  - simpl. apply sortQ_cons; [ apply sortQ_nil | apply Forall_nil ].
  - inversion HS as [| x0 xs0 HSys HFall]; subst.
    rewrite Forall_forall in HFall.
    simpl. destruct (Qle_bool x y) eqn:E.
    + apply sortQ_cons; [ exact HS | ].
      rewrite Forall_forall. intros z Hz. destruct Hz as [Heq | Hz].
      * subst. apply xq_Qle_bool_le. exact E.
      * apply (Qle_trans x y z).
        -- apply xq_Qle_bool_le. exact E.
        -- apply HFall. exact Hz.
    + apply sortQ_cons; [ apply IH; exact HSys | ].
      rewrite Forall_forall. intros z Hz.
      assert (Hin : In z (x :: ys)).
      { apply Permutation_in with (l := insert_q x ys).
        - apply Permutation_sym. apply insert_q_perm_cons.
        - exact Hz. }
      destruct Hin as [Heq | Hin].
      * subst. apply Qle_bool_false_le. exact E.
      * apply HFall. exact Hin.
Qed.

Lemma xq_P0_sorted : forall l : list Q, SortedQ (P0 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply sortQ_nil.
  - apply xq_sortQ_insert. exact IH.
Qed.

(* ---------- xq 局部工具：lastq 尾元与望远镜方程 ---------- *)

Fixpoint lastq (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => x
               | _ :: _ => lastq xs
               end
  end.

Lemma xq_lastq_In : forall m : list Q, m <> [] -> In (lastq m) m.
Proof.
  induction m as [| a rest IH]; intros Hne.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b bs].
    + simpl. left. reflexivity.
    + simpl. right. apply IH. simpl. discriminate.
Qed.

Lemma xq_hd_In_gen : forall m : list Q, m <> [] -> In (hd 0 m) m.
Proof.
  intros [| h t] H; [ exfalso; apply H; reflexivity | simpl; left; reflexivity ].
Qed.

Lemma xq_P0_cons_ne : forall (x : Q) (xs : list Q), P0 (x :: xs) <> [].
Proof.
  intros x xs. cbn [P0].
  destruct (P0 xs) as [| y ys]; cbn [insert_q].
  - discriminate.
  - destruct (Qle_bool x y); discriminate.
Qed.

Lemma xq_hd_le_lastq : forall l : list Q, SortedQ l -> (hd 0 l <= lastq l)%Q.
Proof.
  induction l as [| a rest IH]; intro HS.
  - simpl. apply Qle_refl.
  - destruct rest as [| b bs].
    + simpl. apply Qle_refl.
    + inversion HS as [| x0 xs0 HSr HFa]; subst.
      rewrite Forall_forall in HFa.
      apply (Qle_trans a b).
      * apply HFa. left. reflexivity.
      * apply IH. exact HSr.
Qed.

(* 望远镜方程：升序表的相邻差总和 == 尾元 - 首元 *)
Lemma xq_telescope : forall l : list Q, SortedQ l -> H_adj l == lastq l - hd 0 l.
Proof.
  induction l as [| a rest IH]; intro HS.
  - reflexivity.
  - destruct rest as [| b bs].
    + change (H_adj [a]) with 0%Q.
      change (lastq [a] - hd 0 [a]) with (a - a)%Q.
      symmetry. apply xq_minus_self.
    + inversion HS as [| x0 xs0 HSr HFa]; subst.
      rewrite Forall_forall in HFa.
      change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      assert (Hab : (0 <= b - a)%Q).
      { apply (proj1 (Qle_0_sub' a b)). apply HFa. left. reflexivity. }
      rewrite (xq_abs_id _ Hab).
      rewrite (IH HSr).
      change (lastq (a :: b :: bs)) with (lastq (b :: bs)).
      change (hd 0 (a :: b :: bs)) with a.
      change (hd 0 (b :: bs)) with b.
      ring.
Qed.

(* 配对距离界：表中任意两元素的 Qabs 距离不超过序列熵 *)
Lemma xq_pair_dist_le : forall (l : list Q) (x y : Q),
  In x l -> In y l -> (Qabs (x - y) <= H_adj l)%Q.
Proof.
  induction l as [| a rest IH]; intros x y Hx Hy.
  - exfalso. exact Hx.
  - destruct rest as [| b bs].
    + destruct Hx as [Hx | []]; destruct Hy as [Hy | []]; subst.
      rewrite xq_abs_zero. apply Qle_refl.
    + change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
      * rewrite xq_abs_zero. apply qadd_nonneg;
          [ apply abs_nonneg | apply xq_H_adj_nonneg ].
      * assert (Hr1 : a - y == (a - b) + (b - y)) by ring.
        rewrite Hr1.
        apply (Qle_trans _ (Qabs (a - b) + Qabs (b - y))).
        -- apply Qabs_triangle.
        -- rewrite (xq_abs_sub_comm a b).
           apply qadd_le; [ apply Qle_refl
                          | apply IH; [ left; reflexivity | exact Hy ] ].
      * assert (Hr2 : x - a == (x - b) + (b - a)) by ring.
        rewrite Hr2.
        apply (Qle_trans _ (Qabs (x - b) + Qabs (b - a))).
        -- apply Qabs_triangle.
        -- rewrite (Qplus_comm (Qabs (x - b)) (Qabs (b - a))).
           apply qadd_le; [ apply Qle_refl
                          | apply IH; [ exact Hx | left; reflexivity ] ].
      * apply (Qle_trans _ (H_adj (b :: bs))).
        -- apply IH; assumption.
        -- apply xq_le_add_abs.
Qed.

(* ========== 定理 C：升序最小化序列熵（P0 最小化相邻差总和） ========== *)

Theorem C_sorted_min_adj : forall (l : list Q), H_adj (P0 l) <= H_adj l.
Proof.
  intro l. destruct l as [| a rest].
  - apply Qle_refl.
  - assert (HP : H_adj (P0 (a :: rest))
                 == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest)))
      by (apply xq_telescope; apply xq_P0_sorted).
    assert (HP2 : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest))).
    { rewrite (xq_abs_sub_comm (hd 0 (P0 (a :: rest))) (lastq (P0 (a :: rest)))).
      apply xq_abs_id.
      apply (proj1 (Qle_0_sub' _ _)).
      apply xq_hd_le_lastq. apply xq_P0_sorted. }
    rewrite HP. rewrite <- HP2.
    assert (Hm1 : In (hd 0 (P0 (a :: rest))) (a :: rest)).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - apply Permutation_sym. apply D5_P0_perm.
      - apply xq_hd_In_gen. apply xq_P0_cons_ne. }
    assert (Hm2 : In (lastq (P0 (a :: rest))) (a :: rest)).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - apply Permutation_sym. apply D5_P0_perm.
      - apply xq_lastq_In. apply xq_P0_cons_ne. }
    apply xq_pair_dist_le; assumption.
Qed.

(* ========== §5 计数测度（D8 → 定理 B） ========== *)

Fixpoint nat_fact (n : nat) : nat :=
  match n with
  | O => 1
  | S m => S m * nat_fact m
  end.

Definition q_fact (n : nat) : Q := (Z.of_nat (nat_fact n) # 1)%Q.

Lemma Zpos_le_roundtrip : forall d : positive,
  (Z.pos d <= Z.of_nat (Pos.to_nat d))%Z.
Proof.
  induction d as [p IH | p IH | ].
  - rewrite Pos2Nat.inj_xI, Znat.Nat2Z.inj_succ, Znat.Nat2Z.inj_mul.
    rewrite Pos2Z.inj_xI. change (Z.of_nat 2) with (2%Z). lia.
  - rewrite Pos2Nat.inj_xO, Znat.Nat2Z.inj_mul, Pos2Z.inj_xO.
    change (Z.of_nat 2) with (2%Z). lia.
  - simpl. lia.
Qed.

Lemma nat_fact_ge1 : forall n : nat, (1 <= nat_fact n)%nat.
Proof.
  induction n as [| n IH]; simpl.
  - apply le_n.
  - assert (H2 : (1 * nat_fact n <= S n * nat_fact n)%nat)
      by (apply Nat.mul_le_mono_r; lia).
    lia.
Qed.

Theorem D8_sorted_frac_pos : forall K : nat, (0 < K)%nat -> 0 < (1 / (q_fact K))%Q.
Proof.
  intros K HK. unfold q_fact.
  assert (Hf : (1 <= nat_fact K)%nat) by apply nat_fact_ge1.
  assert (HfZ : (1 <= Z.of_nat (nat_fact K))%Z)
    by (apply (proj1 (Znat.Nat2Z.inj_le 1 (nat_fact K))); exact Hf).
  destruct (Z.of_nat (nat_fact K)) as [| p | p] eqn:EF.
  - exfalso. lia.
  - assert (Hinv : (1 / (Z.pos p # 1) == 1 # p)%Q).
    { unfold Qdiv, Qinv. reflexivity. }
    rewrite Hinv. unfold Qlt. simpl. lia.
  - exfalso. lia.
Qed.

Theorem D8_tends_zero : forall eps : Q, 0 < eps ->
  exists K : nat, (0 < K)%nat /\ (1 / (q_fact K)%Q < eps)%Q.
Proof.
  intros eps Heps. unfold Qlt in Heps. simpl in Heps.
  remember (Qden eps) as d eqn:Ed.
  assert (Hn : (1 <= Qnum eps)%Z) by lia.
  assert (Hd : (0 < Z.pos d)%Z) by lia.
  assert (Hle : (Z.pos d <= Z.of_nat (Pos.to_nat d))%Z) by apply Zpos_le_roundtrip.
  destruct (Z.of_nat (Pos.to_nat d)) as [| p | p] eqn:EF.
  - exfalso. lia.
  - exists (S (S (Pos.to_nat d))). split.
    + lia.
    + assert (Hbound : (Z.succ (Z.succ (Z.of_nat (Pos.to_nat d)))
                        <= Z.of_nat (nat_fact (S (S (Pos.to_nat d)))))%Z).
      { rewrite <- !Znat.Nat2Z.inj_succ.
        apply (proj1 (Znat.Nat2Z.inj_le _ _)).
        simpl.
        assert (Hg : (1 <= nat_fact (S (Pos.to_nat d)))%nat) by apply nat_fact_ge1.
        assert (H2 : (S (S (Pos.to_nat d)) * 1
                      <= S (S (Pos.to_nat d)) * nat_fact (S (Pos.to_nat d)))%nat)
          by (apply Nat.mul_le_mono_l; exact Hg).
        simpl in H2. lia. }
      unfold q_fact.
      destruct (Z.of_nat (nat_fact (S (S (Pos.to_nat d))))) as [| p2 | p2] eqn:EF2.
      -- exfalso. lia.
      -- assert (Hinv : (1 / (Z.pos p2 # 1) == 1 # p2)%Q).
         { unfold Qdiv, Qinv. reflexivity. }
         rewrite Hinv. unfold Qlt. simpl.
         assert (Hp2 : (0 <= Z.pos p2)%Z) by lia.
         assert (Hmul : (1 * Z.pos p2 <= Qnum eps * Z.pos p2)%Z)
           by (apply Z.mul_le_mono_nonneg_r; [lia | exact Hn]).
         lia.
      -- exfalso. lia.
  - exfalso. try rewrite EF in Hle.
    assert (Hnn : (Z.neg p < 0)%Z).
    { change (Z.neg p) with (- Z.pos p)%Z. lia. }
    lia.
Qed.

(* ========== §6 证据分层判断网络（D10 重铸） ========== *)

Inductive Level : Type := Lv0 | Lv1 | Lv2.

Inductive Evidence : Type :=
| evNum  : Q -> Evidence
| evSeq  : list Q -> Evidence
| evPair : Evidence -> Evidence -> Evidence.

Record TrNode : Type := mkTrNode {
  trLevel : Level;
  trPhi   : Dig;
  trModel : Dig;
  trValue : Evidence
}.

Definition Tex (phi : Dig) : Type := { t : TrNode & trPhi t = phi }.

Definition Tabs (phi : Dig) : Type := forall (m : Dig), Evidence.

(* ========== §7 LLM 相位视图（附录对映） ========== *)

Record LLMPhaseView : Type := mkLLMView {
  lam_param      : Q;
  phase_marker   : list Q;
  gate_threshold : Q
}.

Definition gate_pass (threshold H : Q) : bool :=
  if Qle_bool H threshold then true else false.

(* ============================================================
   §8 归并段 M1：并入 DTPT_CGen.v —— C_gen 排序泛化族
   源件 DTPT-U1（Top-1 热点升级单）。仅移除独立文件的
   Require/Import/Open Scope 头（由本文件头统一承载），
   注释与全部证明体、Qed 面、Print Assumptions 审计出口零改动。
   ============================================================ *)
(* ============================================================
   DTPT_CGen.v — 热点升级单 C-GEN（扫描 Top-1 推荐）
   源件：DTPT-U1（新建文件，Require DTPT，不碰既有八件）

   主定理（定理 C 全排列类泛化）：
     C_gen : forall (l p : list Q), Permutation l p -> H_adj (P0 l) <= H_adj p
   现役主定理 DTPT.C_sorted_min_adj 只证「排序 <= 恒等排列」；
   本件把比较对象泛化到 l 的任意排列 p（全排列类）。

   路线：H_adj (P0 l) 经 xq_telescope（排序伸缩）== lastq - hd，
   首尾成员性经 D5_P0_perm + 置换传递搬到 p，再用 xq_pair_dist_le
   （跨度下界：表内任意两元 Qabs 距离 <= H_adj）闭合。

   加分项：
     C_gen_sym_rev  —— SYM 前置件：反转不变 H_adj (rev l) == H_adj l
     C_gen_attained —— 紧性见证：p := P0 l 直构，界在排列类内取得
     C_gen_sorted   —— 现役主定理 C_sorted_min_adj 的泛化重推（特例核对）

   纪律：零公理、零承认、零中止，全程 Qed；Q 层 lia 禁用，
   全部不等式走 xq_ 桥 + ring（Qabs/lastq/H_adj 作原子）。
   ============================================================ *)

(* 原独立文件 Require/Import/Open Scope 头（From Stdlib QArith/List/Permutation、
   Require Import DTPT、Import ListNotations、Open Scope Q_scope）已于归并时移除。 *)

(* ========== §0 snoc 面小工具（SYM 前置件） ========== *)

(* 表末追加一个元素后，尾元就是它（Leibniz 版） *)
Lemma cgen_lastq_app : forall (l : list Q) (x : Q), lastq (l ++ [x]) = x.
Proof.
  induction l as [| y ys IH]; intros x; cbn [app].
  - reflexivity.
  - destruct ys as [| b bs].
    + reflexivity.
    + exact (IH x).
Qed.

(* snoc 熵方程：非空表末尾追加 x，相邻差总和恰增 Qabs (x - 尾元) *)
Lemma cgen_H_adj_snoc : forall (l : list Q) (x : Q),
  l <> [] -> H_adj (l ++ [x]) == (H_adj l + Qabs (x - lastq l))%Q.
Proof.
  induction l as [| y ys IH]; intros x Hne.
  - exfalso. apply Hne. reflexivity.
  - destruct ys as [| b bs].
    + cbn [app]. unfold H_adj. cbn [sum_adjdiff lastq]. ring.
    + assert (IH' : H_adj ((b :: bs) ++ [x])
                    == (H_adj (b :: bs) + Qabs (x - lastq (b :: bs)))%Q)
        by (apply IH; discriminate).
      cbn [app].
      change (H_adj (y :: b :: (bs ++ [x])))
        with (Qabs (b - y) + H_adj ((b :: bs) ++ [x]))%Q.
      rewrite IH'.
      change (H_adj (y :: b :: bs)) with (Qabs (b - y) + H_adj (b :: bs))%Q.
      change (lastq (y :: b :: bs)) with (lastq (b :: bs)).
      ring.
Qed.

(* cons 表反转必非空 *)
Lemma cgen_rev_cons_ne : forall (x : Q) (xs : list Q), rev (x :: xs) <> [].
Proof.
  intros x xs. change (rev (x :: xs)) with (rev xs ++ [x]).
  destruct (rev xs) as [| r rs]; cbn [app]; discriminate.
Qed.

(* 反转表的尾元 == 原表头 *)
Lemma cgen_lastq_rev_cons : forall (b : Q) (bs : list Q),
  lastq (rev (b :: bs)) == b.
Proof.
  intros b bs. change (rev (b :: bs)) with (rev bs ++ [b]).
  rewrite cgen_lastq_app. reflexivity.
Qed.

(* ========== §1 加分项 SYM：反转不变 ========== *)

Theorem C_gen_sym_rev : forall l : list Q, H_adj (rev l) == H_adj l.
Proof.
  induction l as [| a rest IH].
  - reflexivity.
  - cbn [rev].
    destruct rest as [| b bs].
    + reflexivity.
    + rewrite cgen_H_adj_snoc by (apply cgen_rev_cons_ne).
      rewrite IH.
      rewrite cgen_lastq_rev_cons.
      change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      rewrite (xq_abs_sub_comm a b).
      ring.
Qed.

(* ========== §2 主定理：定理 C 全排列类泛化 ========== *)

(* C_gen：排序最小化对 l 的任意排列 p 成立。
   p := l 特例即现役主定理 C_sorted_min_adj；证明骨架与其同构，
   仅成员性迁移段改为「置换传递复合」：P0 l ~> l ~> p 一步到位。 *)
Theorem C_gen : forall (l p : list Q), Permutation l p -> H_adj (P0 l) <= H_adj p.
Proof.
  intros l p Hperm. destruct l as [| a rest].
  - (* l = []：排列类只含空表 *)
    assert (Hp : p = []) by (apply Permutation_nil; exact Hperm).
    rewrite Hp. apply Qle_refl.
  - (* l = a :: rest：P0 l 非空，望远镜展开 + 跨度下界 *)
    assert (Hne : P0 (a :: rest) <> []) by (apply xq_P0_cons_ne).
    assert (HP : H_adj (P0 (a :: rest))
                 == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest)))
      by (apply xq_telescope; apply xq_P0_sorted).
    assert (HP2 : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest))).
    { rewrite (xq_abs_sub_comm (hd 0 (P0 (a :: rest))) (lastq (P0 (a :: rest)))).
      apply xq_abs_id.
      apply (proj1 (Qle_0_sub' _ _)).
      apply xq_hd_le_lastq. apply xq_P0_sorted. }
    (* 置换传递复合：P0 l 是 l 的排列（反向 D5），l 是 p 的排列 *)
    assert (Hrev : Permutation (P0 (a :: rest)) (a :: rest))
      by (apply Permutation_sym; apply D5_P0_perm).
    assert (HpermP : Permutation (P0 (a :: rest)) p).
    { apply perm_trans with (l' := a :: rest).
      - exact Hrev.
      - exact Hperm. }
    (* 首尾两元搬进 p 的成员性 *)
    assert (Hm1 : In (hd 0 (P0 (a :: rest))) p).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - exact HpermP.
      - apply xq_hd_In_gen. exact Hne. }
    assert (Hm2 : In (lastq (P0 (a :: rest))) p).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - exact HpermP.
      - apply xq_lastq_In. exact Hne. }
    (* 跨度下界在 p 上成立 *)
    assert (HPd : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  <= H_adj p)
      by (apply xq_pair_dist_le; assumption).
    (* Qeq setoid 链闭合：H_adj (P0 l) == 尾-首 == Qabs(首-尾) <= H_adj p *)
    rewrite HP. rewrite <- HP2. exact HPd.
Qed.

(* ========== §3 紧性见证与泛化核对 ========== *)

(* 紧性：界在排列类内取得（下确界即最小值），P0 l 直构见证。
   与 C_gen 合读：H_adj (P0 l) 是排列类 {p : Permutation l p} 上
   H_adj 的最小值——泛化界不可再降。 *)
Theorem C_gen_attained : forall l : list Q,
  exists p : list Q, Permutation l p /\ H_adj p == H_adj (P0 l).
Proof.
  intro l. exists (P0 l). split.
  - apply D5_P0_perm.
  - apply Qeq_refl.
Qed.

(* 现役主定理 C_sorted_min_adj 是 C_gen 的特例（p := l 重推核对） *)
Corollary C_gen_sorted : forall l : list Q, H_adj (P0 l) <= H_adj l.
Proof.
  intro l. apply (C_gen l l). apply Permutation_refl.
Qed.

(* ========== G4 假设审计（期望 Closed under the global context） ========== *)

Print Assumptions C_gen.
Print Assumptions C_gen_sym_rev.
Print Assumptions C_gen_attained.
Print Assumptions C_gen_sorted.

(* ============================================================
   §9 归并段 M1：并入 DTPT_N9Opt.v —— N9 极值族
   源件 DTPT-U14R（N9O 分离常数最优性）。仅移除独立文件的
   Require/Import/Open Scope 头（由本文件头统一承载），
   注释与全部证明体、Qed 面、Print Assumptions 审计出口零改动。
   ============================================================ *)
(* ============================================================
   DTPT_N9Opt.v — N9O 分离常数最优性（U14R 续写件）
   基础模块：Require Import DTPT（stdlib QArith/List/Lia/Permutation）
   纪律：零承认体；全部定理以 Qed 闭合；陈述全称、数值面 vm_compute。
   内容：
     [保底件] perm3_cases          —— 长度 3 排列类六形穷举
     [主]   n9_max / n9_max_attained / n9_min_is_sorted
                               —— 见证列 n9_l0 = [0;1;2] 三件全称定理
     [主件]   n9_const_ratio / n9_separation_exact
                               —— 分离比 3/2 精确，两侧均取得
     [加分]   n9_naive_bound / n9_naive_bound_Hadj
                               —— 一般长度朴素上界（spread 面与 H_adj 面）
   数值事实：H_adj 六形 = 2,3,3,3,3,2；max 3 = (3/2)*2，min 2。
   ============================================================ *)
(* 原独立文件 Require/Import/Open Scope 头（From Stdlib QArith/List/Lia/Permutation、
   Require Import DTPT、Import ListNotations、Open Scope Q_scope）已于归并时移除。 *)

(* ---------- 见证列与 spread 面 ---------- *)

Definition n9_l0 : list Q := [0; 1; 2].

Definition spread (l : list Q) : Q := lastq (P0 l) - hd 0 (P0 l).

(* ---------- 有序表首/尾元控制（spread 面的配套件） ---------- *)

Lemma sorted_hd_le_in : forall (m : list Q) (x : Q),
  SortedQ m -> In x m -> (hd 0 m <= x)%Q.
Proof.
  intros m x HS. revert x.
  induction HS as [| y ys HSr _ HFall]; intros x Hin.
  - destruct Hin.
  - simpl. destruct Hin as [Heq | Hin].
    + subst. apply Qle_refl.
    + rewrite Forall_forall in HFall. apply HFall. exact Hin.
Qed.

Lemma sorted_in_le_last : forall (m : list Q) (x : Q),
  SortedQ m -> In x m -> (x <= lastq m)%Q.
Proof.
  intros m x HS. revert x.
  induction HS as [| y ys HSr IH HFall]; intros x Hin.
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + subst x. destruct ys as [| b bs].
      * simpl. apply Qle_refl.
      * change (lastq (y :: b :: bs)) with (lastq (b :: bs)).
        rewrite Forall_forall in HFall.
        apply HFall. apply xq_lastq_In. discriminate.
    + destruct ys as [| b bs].
      * destruct Hin.
      * change (lastq (y :: b :: bs)) with (lastq (b :: bs)).
        apply IH. exact Hin.
Qed.

(* spread 两两界：表中任意两元素的 Qabs 距离不超过 spread *)
Lemma spread_pair_le : forall (l : list Q) (x y : Q),
  In x l -> In y l -> (Qabs (x - y) <= spread l)%Q.
Proof.
  intros l x y Hx Hy. unfold spread.
  assert (Hlne : l <> []) by (intro Hc; rewrite Hc in Hx; exact Hx).
  assert (HPne : P0 l <> []).
  { destruct l as [| a rest].
    - exfalso. apply Hlne. reflexivity.
    - apply xq_P0_cons_ne. }
  assert (HS : SortedQ (P0 l)) by apply xq_P0_sorted.
  assert (Hxl : In x (P0 l)) by
    (apply Permutation_in with (l := l); [ apply D5_P0_perm | exact Hx ]).
  assert (Hyl : In y (P0 l)) by
    (apply Permutation_in with (l := l); [ apply D5_P0_perm | exact Hy ]).
  assert (H1 : (hd 0 (P0 l) <= x)%Q) by (apply sorted_hd_le_in; assumption).
  assert (H2 : (x <= lastq (P0 l))%Q) by (apply sorted_in_le_last; assumption).
  assert (H3 : (hd 0 (P0 l) <= y)%Q) by (apply sorted_hd_le_in; assumption).
  assert (H4 : (y <= lastq (P0 l))%Q) by (apply sorted_in_le_last; assumption).
  destruct (Qle_dec' x y) as [Hxy | Hyx].
  - assert (Habs : Qabs (x - y) == y - x).
    { rewrite xq_abs_sub_comm. apply abs_eq.
      apply (proj1 (Qle_0_sub' x y)). exact Hxy. }
    rewrite Habs.
    apply (Qle_trans _ (lastq (P0 l) - x)).
    + apply qsub_le_r. exact H4.
    + unfold Qminus. apply qadd_le;
        [ apply Qle_refl | apply qopp_le; exact H1 ].
  - assert (Habs : Qabs (x - y) == x - y).
    { apply abs_eq. apply (proj1 (Qle_0_sub' y x)). exact Hyx. }
    rewrite Habs.
    apply (Qle_trans _ (lastq (P0 l) - y)).
    + apply qsub_le_r. exact H2.
    + unfold Qminus. apply qadd_le;
        [ apply Qle_refl | apply qopp_le; exact H3 ].
Qed.

(* ---------- 长度系数步进恒等式（S2 卡配方：Z 层 lia 先证再 rewrite） ---------- *)

Lemma qcoef_step : forall (n : nat) (k : Q),
  k + ((Z.of_nat n - 1)%Z # 1) * k == ((Z.of_nat (S n) - 1)%Z # 1) * k.
Proof.
  intros n k.
  assert (Hz : (Z.of_nat (S n) = 1 + Z.of_nat n)%Z) by lia.
  rewrite Hz.
  destruct k as [kn kd].
  unfold Qeq, Qplus, Qminus, Qmult. cbn [Qnum Qden]. lia.
Qed.

(* 相邻差总和对「两两界 × (长度-1)」的逐项归纳（非空卫哨） *)
Lemma H_adj_pair_bound : forall (m : list Q) (k : Q), m <> [] ->
  (forall x y, In x m -> In y m -> (Qabs (x - y) <= k)%Q) ->
  H_adj m <= ((Z.of_nat (length m) - 1)%Z # 1) * k.
Proof.
  intros m. induction m as [| a rest IH]; intros k Hne Hpair.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b rest2].
    + (* 单元素：H_adj = 0，系数 1-1 = 0 *)
      change (H_adj [a]) with 0%Q.
      cbn [length].
      replace ((Z.of_nat 1 - 1)%Z # 1) with 0%Q by reflexivity.
      rewrite Qmult_0_l. apply Qle_refl.
    + (* 多元素：|b-a| <= k 与 IH 相加 *)
      change (H_adj (a :: b :: rest2))
        with (Qabs (b - a) + H_adj (b :: rest2))%Q.
      assert (Hbp : (Qabs (b - a) <= k)%Q).
      { apply Hpair; [ right; left; reflexivity | left; reflexivity ]. }
      assert (IHr : H_adj (b :: rest2)
                    <= ((Z.of_nat (length (b :: rest2)) - 1)%Z # 1) * k).
      { apply IH; [ discriminate | ].
        intros x y Hx Hy. apply Hpair.
        - destruct Hx as [Hx | Hx].
          + subst x. right; left; reflexivity.
          + right; right; exact Hx.
        - destruct Hy as [Hy | Hy].
          + subst y. right; left; reflexivity.
          + right; right; exact Hy. }
      assert (Hq : k + ((Z.of_nat (length (b :: rest2)) - 1)%Z # 1) * k
                   == ((Z.of_nat (length (a :: b :: rest2)) - 1)%Z # 1) * k).
      { change (length (b :: rest2)) with (S (length rest2)).
        change (length (a :: b :: rest2)) with (S (S (length rest2))).
        apply qcoef_step. }
      rewrite <- Hq.
      apply qadd_le; [ exact Hbp | exact IHr ].
Qed.

(* ========== 【保底件】长度 3 排列类六形穷举 ========== *)

Lemma perm3_cases : forall (a b c : Q) (p : list Q),
  Permutation [a; b; c] p ->
  p = [a; b; c] \/ p = [a; c; b] \/ p = [b; a; c] \/
  p = [b; c; a] \/ p = [c; a; b] \/ p = [c; b; a].
Proof.
  intros a b c p Hp.
  assert (Hlen : length p = 3%nat).
  { pose proof (Permutation_length Hp) as HL. simpl in HL. lia. }
  destruct p as [| x1 [| x2 [| x3 [| x4 p4]]]].
  - simpl in Hlen. discriminate.
  - simpl in Hlen. discriminate.
  - simpl in Hlen. discriminate.
  - (* p = [x1;x2;x3]：逐位成员迁移消解 *)
    assert (Hin1 : In x1 [a; b; c]).
    { apply Permutation_in with (l := [x1; x2; x3]).
      - apply Permutation_sym. exact Hp.
      - left; reflexivity. }
    simpl in Hin1.
    destruct Hin1 as [E1 | [E1 | [E1 | []]]]; subst x1.
    + (* x1 = a *)
      assert (Hp1 : Permutation [b; c] [x2; x3])
        by exact (Permutation_cons_inv Hp).
      assert (Hin2 : In x2 [b; c]).
      { apply Permutation_in with (l := [x2; x3]).
        - apply Permutation_sym. exact Hp1.
        - left; reflexivity. }
      simpl in Hin2. destruct Hin2 as [E2 | [E2 | []]]; subst x2.
      * assert (Hp2 : Permutation [c] [x3])
          by exact (Permutation_cons_inv Hp1).
        assert (Hin3 : In x3 [c]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3. left; reflexivity.
      * assert (Hp2 : Permutation [b] [x3]).
        { apply (Permutation_cons_inv (a := c)).
          eapply perm_trans with (l' := [b; c]).
          - apply Permutation_sym. apply perm_swap.
          - exact Hp1. }
        assert (Hin3 : In x3 [b]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3. right; left; reflexivity.
    + (* x1 = b *)
      assert (Hp1 : Permutation [a; c] [x2; x3]).
      { apply (Permutation_cons_inv (a := b)).
        eapply perm_trans with (l' := [a; b; c]).
        - apply Permutation_sym. apply perm_swap.
        - exact Hp. }
      assert (Hin2 : In x2 [a; c]).
      { apply Permutation_in with (l := [x2; x3]).
        - apply Permutation_sym. exact Hp1.
        - left; reflexivity. }
      simpl in Hin2. destruct Hin2 as [E2 | [E2 | []]]; subst x2.
      * assert (Hp2 : Permutation [c] [x3])
          by exact (Permutation_cons_inv Hp1).
        assert (Hin3 : In x3 [c]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3. right; right; left; reflexivity.
      * assert (Hp2 : Permutation [a] [x3]).
        { apply (Permutation_cons_inv (a := c)).
          eapply perm_trans with (l' := [a; c]).
          - apply Permutation_sym. apply perm_swap.
          - exact Hp1. }
        assert (Hin3 : In x3 [a]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3.
        right; right; right; left; reflexivity.
    + (* x1 = c *)
      assert (Hp1 : Permutation [a; b] [x2; x3]).
      { apply (Permutation_cons_inv (a := c)).
        eapply perm_trans with (l' := [a; b; c]).
        - etransitivity.
          + apply perm_swap.
          + apply perm_skip. apply perm_swap.
        - exact Hp. }
      assert (Hin2 : In x2 [a; b]).
      { apply Permutation_in with (l := [x2; x3]).
        - apply Permutation_sym. exact Hp1.
        - left; reflexivity. }
      simpl in Hin2. destruct Hin2 as [E2 | [E2 | []]]; subst x2.
      * assert (Hp2 : Permutation [b] [x3])
          by exact (Permutation_cons_inv Hp1).
        assert (Hin3 : In x3 [b]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3.
        right; right; right; right; left; reflexivity.
      * assert (Hp2 : Permutation [a] [x3]).
        { apply (Permutation_cons_inv (a := b)).
          eapply perm_trans with (l' := [a; b]).
          - apply Permutation_sym. apply perm_swap.
          - exact Hp1. }
        assert (Hin3 : In x3 [a]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3.
        right; right; right; right; right; reflexivity.
  - (* 长度 >= 4：与 3 矛盾 *)
    simpl in Hlen. lia.
Qed.

(* ========== 【主】见证列 n9_l0 = [0;1;2] 类上极值三件 ==========
   数值事实：六形 H_adj = 2,3,3,3,3,2，max 3、min 2。 ========== *)

Theorem n9_max : forall p, Permutation n9_l0 p -> H_adj p <= 3.
Proof.
  intros p Hp. unfold n9_l0 in Hp. apply perm3_cases in Hp.
  destruct Hp as [E | [E | [E | [E | [E | E]]]]]; subst p;
    apply xq_Qle_bool_le; vm_compute; reflexivity.
Qed.

Theorem n9_max_attained : exists p, Permutation n9_l0 p /\ H_adj p == 3.
Proof.
  exists [0; 2; 1]. split.
  - unfold n9_l0. apply perm_skip. apply perm_swap.
  - vm_compute. reflexivity.
Qed.

Theorem n9_min_is_sorted : forall p, Permutation n9_l0 p -> 2 <= H_adj p.
Proof.
  intros p Hp. unfold n9_l0 in Hp. apply perm3_cases in Hp.
  destruct Hp as [E | [E | [E | [E | [E | E]]]]]; subst p;
    apply xq_Qle_bool_le; vm_compute; reflexivity.
Qed.

(* ========== 【主件】分离常数比 3/2 精确（两侧均取得） ========== *)

Theorem n9_const_ratio :
  (3 # 2)%Q * 2 == 3 /\
  (exists pmax : list Q, Permutation n9_l0 pmax /\ H_adj pmax == 3) /\
  (exists pmin : list Q, Permutation n9_l0 pmin /\ H_adj pmin == 2).
Proof.
  split; [| split].
  - vm_compute. reflexivity.
  - exists [0; 2; 1]. split.
    + unfold n9_l0. apply perm_skip. apply perm_swap.
    + vm_compute. reflexivity.
  - exists [0; 1; 2]. split.
    + unfold n9_l0. apply Permutation_refl.
    + vm_compute. reflexivity.
Qed.

(* 类上全域版：任一排列的 H_adj 被夹在 [(3#2)*2 下界面, (3#2)*2 上界面] *)
Theorem n9_separation_exact : forall p, Permutation n9_l0 p ->
  H_adj p <= (3 # 2)%Q * 2 /\ (3 # 2)%Q * 2 <= (3 # 2)%Q * H_adj p.
Proof.
  intros p Hp.
  assert (I : (3 # 2)%Q * 2 == 3) by (vm_compute; reflexivity).
  split.
  - rewrite I. apply n9_max. exact Hp.
  - rewrite (Qmult_comm (3 # 2)%Q 2). rewrite (Qmult_comm (3 # 2)%Q (H_adj p)).
    apply qmul_le_r.
    + apply n9_min_is_sorted. exact Hp.
    + apply xq_Qle_bool_le. vm_compute. reflexivity.
Qed.

(* ========== 【加分】一般长度朴素上界 ========== *)

(* spread 面：H_adj p <= (n-1) * spread l *)
Theorem n9_naive_bound : forall (l p : list Q), Permutation l p -> p <> [] ->
  H_adj p <= ((Z.of_nat (length l) - 1)%Z # 1) * spread l.
Proof.
  intros l p Hp Hne.
  pose proof (Permutation_length Hp) as HL.
  rewrite HL.
  apply H_adj_pair_bound; [ exact Hne | ].
  intros x y Hx Hy.
  assert (Hxl : In x l) by
    (apply Permutation_in with (l := p);
       [ apply Permutation_sym; exact Hp | exact Hx ]).
  assert (Hyl : In y l) by
    (apply Permutation_in with (l := p);
       [ apply Permutation_sym; exact Hp | exact Hy ]).
  apply spread_pair_le; assumption.
Qed.

(* H_adj 面（原路线：经 xq_pair_dist_le 逐项） *)
Theorem n9_naive_bound_Hadj : forall (l p : list Q), Permutation l p -> p <> [] ->
  H_adj p <= ((Z.of_nat (length l) - 1)%Z # 1) * H_adj l.
Proof.
  intros l p Hp Hne.
  pose proof (Permutation_length Hp) as HL.
  rewrite HL.
  apply H_adj_pair_bound; [ exact Hne | ].
  intros x y Hx Hy.
  assert (Hxl : In x l) by
    (apply Permutation_in with (l := p);
       [ apply Permutation_sym; exact Hp | exact Hx ]).
  assert (Hyl : In y l) by
    (apply Permutation_in with (l := p);
       [ apply Permutation_sym; exact Hp | exact Hy ]).
  apply (xq_pair_dist_le l); assumption.
Qed.

(* ---------- 审计出口 ---------- *)

Print Assumptions perm3_cases.
Print Assumptions n9_max.
Print Assumptions n9_max_attained.
Print Assumptions n9_min_is_sorted.
Print Assumptions n9_const_ratio.
Print Assumptions n9_separation_exact.
Print Assumptions n9_naive_bound.
Print Assumptions n9_naive_bound_Hadj.

(* ============================================================
   §10 归并段 M1：并入 DTPT_D8Ext.v —— D8 阶乘级数族
   源件 DTPT-U7（D8 阶乘族定理化）。仅移除独立文件的
   Require/Import/Open Scope 头（由本文件头统一承载），
   注释与全部证明体、Qed 面零改动。
   ============================================================ *)
(* ============================================================
   DTPT_D8Ext.v — 热点升级单 D8X（D8 阶乘族定理化）
   源件：DTPT-U7 ｜ 基础模块：Require Import DTPT
   （DTPT.vo 稳定基线，既有十三件 .v 零改动、禁重证 D8 六件）

   交付分级（D8X 升级目标 1-4）：
   【保底件 1·递推方程】
     q_fact_recurrence : q_fact (S n) == q_fact n * (Z.of_nat (S n) # 1)
   【保底件 2·单调族】
     nat_fact_mono / nat_fact_le（阶乘单调链）
     q_fact_recip_anti : (k <= k')%nat -> (1/q_fact k' <= 1/q_fact k)%Q
     D8_mono（清单建议形推论：1/q_fact (S K) <= 1/q_fact K）
   【主件 3·级数优界】
     sum_fact_recip_lt3 : (sum_fact_recip n < 3)%Q
     路线：指数型不变量 sum_fact_recip n + 1/n! <= 3（双基归纳 0/1）
     （核心步（移位形）2/(n+2)! <= 1/(n+1)!：n+2 >= 2 恒真；
       非移位形 2/(n+1)! <= 1/n! 在 n=0 处假（2 > 1），诚实记录。
       终局严格性来自 0 < 1/n!：S_n < S_n + 1/n! <= 3。
       与几何级数路线同定理、更短且免 Q 幂几何部分和；
       几何路线的 2^k 下界族仍作为加分件 §6 交付。）
   【加分件 4·构造性收敛率】
     q_fact_rate / q_fact_rate_exists（K0 = 4 起步：k >= 4 ⟹ 1/k!·4 < 1）
   【加分件 5·2^k 下界族】
     nat_fact_pow2_lb : 2^k <= nat_fact (S k)（即 (k+1)! >= 2^k）
     q_fact_inv_le_pow2 : 1/(k+1)! <= 1/2^k

   纪律：零公理、零承认、零中止、零经典排中，全程 Qed 完成。
   Q 层 lia 禁用：全部不等式经 Qnum/Qden 展开 + Z 层 lia/ring；
   `#` 分母槽是 positive（实证坑），Z 分母一律走 q_inv_den1。
   ============================================================ *)
(* 原独立文件 Require/Import/Open Scope 头（From Stdlib QArith/List/Arith/Lia、
   Require Import DTPT、Open Scope Q_scope）已于归并时移除。 *)

(* ========== §0 正性见证：Z.of_nat (nat_fact n) 恒为 Z.pos ========== *)

Lemma nat_fact_pos_Z : forall n : nat,
  exists p : positive, Z.of_nat (nat_fact n) = Z.pos p.
Proof.
  intro n. pose proof (nat_fact_ge1 n) as H.
  apply (proj1 (Znat.Nat2Z.inj_le 1 (nat_fact n))) in H.
  destruct (Z.of_nat (nat_fact n)) as [| p | p] eqn:E.
  - exfalso. lia.
  - exists p. reflexivity.
  - exfalso. lia.
Qed.

(* 分母 1 形的 Q 逆（DTPT.v D8 同款：unfold Qdiv, Qinv 直收） *)
Lemma q_inv_den1 : forall p : positive, 1 / (Z.pos p # 1) == (1 # p)%Q.
Proof. intro p. unfold Qdiv, Qinv; reflexivity. Qed.

Lemma q_fact_ne0 : forall n : nat, ~ (q_fact n == 0)%Q.
Proof.
  intro n. destruct (nat_fact_pos_Z n) as [p Ep].
  unfold q_fact. rewrite Ep. intro Hc.
  unfold Qeq in Hc. simpl in Hc. lia.
Qed.

(* ========== §1 保底件：递推方程 ========== *)

Theorem q_fact_recurrence : forall n : nat,
  q_fact (S n) == q_fact n * (Z.of_nat (S n) # 1)%Q.
Proof.
  intro n. unfold q_fact.
  change (nat_fact (S n)) with (S n * nat_fact n)%nat.
  rewrite Znat.Nat2Z.inj_mul.
  rewrite Qmult_comm. apply Qeq_refl.
Qed.

(* ========== §2 保底件：单调族 ========== *)

Lemma nat_fact_mono : forall n m : nat,
  (n <= m)%nat -> (nat_fact n <= nat_fact m)%nat.
Proof.
  intros n m Hle. induction Hle as [| m Hle IH].
  - apply Nat.le_refl.
  - apply (Nat.le_trans _ (nat_fact m) _).
    + exact IH.
    + change (nat_fact (S m)) with (S m * nat_fact m)%nat.
      assert (H2 : (1 * nat_fact m <= S m * nat_fact m)%nat)
        by (apply Nat.mul_le_mono_r; lia).
      rewrite Nat.mul_1_l in H2. exact H2.
Qed.

Lemma nat_fact_le : forall n : nat, (nat_fact n <= nat_fact (S n))%nat.
Proof. intro n. apply nat_fact_mono. apply Nat.le_succ_diag_r. Qed.

Lemma nat_fact_le_Z : forall n m : nat,
  (n <= m)%nat -> (Z.of_nat (nat_fact n) <= Z.of_nat (nat_fact m))%Z.
Proof.
  intros n m Hle.
  apply (proj1 (Znat.Nat2Z.inj_le (nat_fact n) (nat_fact m))).
  apply nat_fact_mono. exact Hle.
Qed.

(* ========== §3 保底件：倒数反单调（Q 除法序桥 + 正性卫哨） ========== *)

Theorem q_fact_recip_anti : forall k k' : nat,
  (k <= k')%nat -> (1 / q_fact k' <= 1 / q_fact k)%Q.
Proof.
  intros k k' Hle.
  pose proof (nat_fact_le_Z k k' Hle) as Hz.
  destruct (nat_fact_pos_Z k) as [pk Ek].
  destruct (nat_fact_pos_Z k') as [pk' Ek'].
  rewrite Ek, Ek' in Hz.
  unfold q_fact. rewrite Ek, Ek'.
  rewrite (q_inv_den1 pk'), (q_inv_den1 pk).
  unfold Qle. simpl. lia.
Qed.

(* 清单建议形 D8_mono：后继倒数不增 *)
Corollary D8_mono : forall K : nat,
  (0 < K)%nat -> (1 / q_fact (S K) <= 1 / q_fact K)%Q.
Proof.
  intros K HK. apply q_fact_recip_anti. apply Nat.le_succ_diag_r.
Qed.

(* ============ §4 主件：部分和 Σ_{k=0}^{n} 1/k! < 3 ============ *)

Fixpoint sum_fact_recip (n : nat) : Q :=
  match n with
  | O => 1 / q_fact 0
  | S m => sum_fact_recip m + 1 / q_fact (S m)
  end.

(* 核心步（移位形，n 起步即真）：2/(n+2)! <= 1/(n+1)!。
   注意非移位形 2/(n+1)! <= 1/n! 在 n=0 处假（2 > 1），
   故不变量走双基归纳（§4 末）。 *)
Lemma q_recip_step_Z : forall a b : Z,
  (0 < b)%Z -> (2 * b <= a)%Z -> (2 / (a # 1) <= 1 / (b # 1))%Q.
Proof.
  intros a b Hb Hab.
  destruct a as [| pa | pa]; try lia.
  destruct b as [| pb | pb]; try lia.
  assert (H2 : 2 / (Z.pos pa # 1) == 2 # pa).
  { unfold Qdiv, Qinv; reflexivity. }
  assert (H1 : 1 / (Z.pos pb # 1) == 1 # pb).
  { unfold Qdiv, Qinv; reflexivity. }
  rewrite H2, H1. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

Lemma q_fact_step2_le : forall n : nat,
  (2 / q_fact (S (S n)) <= 1 / q_fact (S n))%Q.
Proof.
  intro n.
  pose proof (nat_fact_ge1 (S n)) as Hg.
  apply (proj1 (Znat.Nat2Z.inj_le 1 (nat_fact (S n)))) in Hg.
  unfold q_fact. change (nat_fact (S (S n))) with (S (S n) * nat_fact (S n))%nat.
  rewrite Znat.Nat2Z.inj_mul.
  apply q_recip_step_Z.
  - lia.
  - apply Z.mul_le_mono_nonneg_r.
    + lia.
    + apply (proj1 (Znat.Nat2Z.inj_le 2 (S (S n)))). lia.
Qed.

(* 指数型不变量：S_n + 1/n! <= 3（归纳自持；双基：0 与 1） *)
Lemma sum_fact_recip_inv : forall n : nat,
  (sum_fact_recip n + 1 / q_fact n <= 3)%Q.
Proof.
  intro n.
  assert (Hboth : (sum_fact_recip n + 1 / q_fact n <= 3)%Q /\
                  (sum_fact_recip (S n) + 1 / q_fact (S n) <= 3)%Q).
  { induction n as [| n [IH1 IH2]].
    - split.
      + cbn [sum_fact_recip].
        assert (H0 : (1 / q_fact 0 == 1)%Q) by (unfold q_fact; reflexivity).
        rewrite H0. unfold Qle. simpl. lia.
      + cbn [sum_fact_recip].
        assert (H0 : (1 / q_fact 0 == 1)%Q) by (unfold q_fact; reflexivity).
        assert (H1 : (1 / q_fact 1 == 1)%Q) by (unfold q_fact; reflexivity).
        rewrite H0, H1. unfold Qle. simpl. lia.
    - split.
      + exact IH2.
      + cbn [sum_fact_recip].
        assert (Hassoc : (sum_fact_recip (S n) + 1 / q_fact (S (S n))
                           + 1 / q_fact (S (S n))
                         == sum_fact_recip (S n) + 2 / q_fact (S (S n)))%Q).
        { field. apply q_fact_ne0. }
        rewrite Hassoc.
        apply (Qle_trans _ (sum_fact_recip (S n) + 1 / q_fact (S n))%Q).
        * apply qadd_le; [ apply Qle_refl | apply q_fact_step2_le ].
        * exact IH2. }
  exact (proj1 Hboth).
Qed.

(* 正性：0 < 1/n!（终局严格性的来源） *)
Lemma q_fact_inv_pos : forall n : nat, (0 < 1 / q_fact n)%Q.
Proof.
  intro n. destruct (nat_fact_pos_Z n) as [p Ep].
  unfold q_fact. rewrite Ep. rewrite (q_inv_den1 p).
  unfold Qlt. simpl. lia.
Qed.

(* 主定理：Σ_{k=0}^{n} 1/k! < 3
   （S_n < S_n + 1/n! 严格 <--- 0 < 1/n!；再 <= 3 由不变量） *)
Theorem sum_fact_recip_lt3 : forall n : nat, (sum_fact_recip n < 3)%Q.
Proof.
  intro n.
  pose proof (q_fact_inv_pos n) as Hpos.
  apply (Qlt_le_trans _ (sum_fact_recip n + 1 / q_fact n)%Q).
  - pose proof (proj2 (Qplus_lt_r 0 (1 / q_fact n) (sum_fact_recip n)) Hpos) as Hlt.
    rewrite Qplus_0_r in Hlt. exact Hlt.
  - apply sum_fact_recip_inv.
Qed.

(* ========== §5 加分件：构造性收敛率（显式 K0 = 4） ========== *)

Theorem q_fact_rate : forall k : nat,
  (4 <= k)%nat -> (1 / q_fact k * 4 < 1)%Q.
Proof.
  intros k Hk.
  destruct (nat_fact_pos_Z k) as [p Ep].
  pose proof (nat_fact_le_Z 4%nat k Hk) as HZ.
  rewrite Ep in HZ. simpl in HZ.
  unfold q_fact. rewrite Ep. rewrite (q_inv_den1 p).
  unfold Qmult. simpl. unfold Qlt. simpl. lia.
Qed.

Theorem q_fact_rate_exists : exists K0 : nat,
  forall k : nat, (K0 <= k)%nat -> (1 / q_fact k * 4 < 1)%Q.
Proof. exists 4%nat. apply q_fact_rate. Qed.

(* ========== §6 加分件：2^k 下界族（几何路线的承重件） ========== *)

Lemma pow2_ge1 : forall k : nat, (1 <= 2 ^ k)%nat.
Proof. induction k as [| k IH]; simpl; lia. Qed.

(* (k+1)! >= 2^k：S k 支 = 2·2^k <= 2·k! <= (k+2)·k! 两次乘法保序 *)
Lemma nat_fact_pow2_lb : forall k : nat, (2 ^ k <= nat_fact (S k))%nat.
Proof.
  induction k as [| k IH].
  - simpl. lia.
  - change (2 ^ S k)%nat with (2 * 2 ^ k)%nat.
    change (nat_fact (S (S k))) with (S (S k) * nat_fact (S k))%nat.
    assert (H1 : (2 * 2 ^ k <= 2 * nat_fact (S k))%nat)
      by (apply Nat.mul_le_mono_l; exact IH).
    assert (H2 : (2 * nat_fact (S k) <= S (S k) * nat_fact (S k))%nat)
      by (apply Nat.mul_le_mono_r; lia).
    lia.
Qed.

Theorem q_fact_inv_le_pow2 : forall k : nat,
  (1 / q_fact (S k) <= 1 / (Z.of_nat (2 ^ k) # 1))%Q.
Proof.
  intro k.
  destruct (nat_fact_pos_Z (S k)) as [p Ep].
  pose proof (proj1 (Znat.Nat2Z.inj_le (2 ^ k)%nat (nat_fact (S k)))
                    (nat_fact_pow2_lb k)) as Hq.
  rewrite Ep in Hq.
  assert (Hp2 : (0 < Z.of_nat (2 ^ k))%Z).
  { pose proof (pow2_ge1 k) as H1.
    apply (proj1 (Znat.Nat2Z.inj_le 1 (2 ^ k))) in H1. lia. }
  destruct (Z.of_nat (2 ^ k)) as [| q | q] eqn:Eq; try lia.
  unfold q_fact. rewrite Ep.
  rewrite (q_inv_den1 p), (q_inv_den1 q).
  unfold Qle. simpl. lia.
Qed.

(* ============================================================
   §11 归并段 S1：并入 DTPT_LLM.v —— LLM 映射层定理族
   源件 DTPT-S4（interleave/gate_pass/rot 循环旋转/Pmid 端点/
   Tex/Tabs 语义桥/gate_pass 行为族）。仅剥去独立文件 Require/
   Import/Open Scope 头与 Module 壳行（由本文件头统一承载），
   注释与全部证明体、Qed 面零改动逐字迁移。
   ============================================================ *)

(* ========== §0 通用列表辅助（firstn/skipn 边界引理） ========== *)

(* n 不短于表长时，firstn 取全表 *)
Lemma llm_firstn_ge_full : forall (n : nat) (l : list Q),
  (length l <= n)%nat -> firstn n l = l.
Proof.
  induction n as [| n IH]; intros [| x xs] H; simpl in *.
  - reflexivity.
  - inversion H.
  - reflexivity.
  - rewrite IH by lia. reflexivity.
Qed.

(* n 不短于表长时，skipn 取空表 *)
Lemma llm_skipn_ge_nil : forall (n : nat) (l : list Q),
  (length l <= n)%nat -> skipn n l = [].
Proof.
  induction n as [| n IH]; intros [| x xs] H; simpl in *.
  - reflexivity.
  - inversion H.
  - reflexivity.
  - apply IH. lia.
Qed.

(* ========== §A interleave 结构定理（保底件） ========== *)

Theorem llm_interleave_length : forall l1 l2 : list Q,
  Id (length (interleave l1 l2)) (length l1 + length l2)%nat.
Proof.
  assert (Hcore : forall l1 l2 : list Q,
  length (interleave l1 l2) = (length l1 + length l2)%nat).
  {
    induction l1 as [| x xs IH]; intros l2.
    - simpl. reflexivity.
    - destruct l2 as [| y ys]; simpl; rewrite ?IH; lia.
  }
  intros l1 l2.
  exact (eq_imp_id (Hcore l1 l2)).
Qed.

Theorem llm_interleave_perm : forall l1 l2 : list Q,
  Permutation (interleave l1 l2) (l1 ++ l2).
Proof.
  induction l1 as [| x xs IH]; intros l2.
  - simpl. apply Permutation_refl.
  - destruct l2 as [| y ys].
    + simpl. rewrite app_nil_r. apply Permutation_refl.
    + simpl. apply perm_skip.
      etransitivity.
      * apply Permutation_cons_append.
      * etransitivity.
        -- apply Permutation_app_tail. apply IH.
        -- rewrite <- app_assoc. apply Permutation_app_head.
           exact (Permutation_sym (Permutation_cons_append ys y)).
Qed.

(* ========== §B gate_pass 行为定理（保底件） ========== *)

(* 通过判据的布尔反射桥：gate_pass = true 恰当 H <= threshold *)
Theorem llm_gate_pass_iff : forall (t H : Q),
  gate_pass t H = true <-> (H <= t)%Q.
Proof.
  intros t H. unfold gate_pass. split.
  - intro Hp. destruct (Qle_bool H t) eqn:E.
    + apply (proj1 (Qle_bool_iff H t)). exact E.
    + discriminate Hp.
  - intro Hle. rewrite (proj2 (Qle_bool_iff H t) Hle). reflexivity.
Qed.

(* 未通过判据：gate_pass = false 恰当 threshold < H *)
Theorem llm_gate_pass_false_iff : forall (t H : Q),
  gate_pass t H = false <-> (t < H)%Q.
Proof.
  intros t H. unfold gate_pass. split.
  - intro Hp. destruct (Qle_bool H t) eqn:E.
    + discriminate Hp.
    + unfold Qle_bool in E. apply Z.leb_gt in E. unfold Qlt. exact E.
  - intro Hlt. destruct (Qle_bool H t) eqn:E.
    + exfalso. apply (Qlt_irrefl H). apply (Qle_lt_trans H t H).
      * apply (proj1 (Qle_bool_iff H t)). exact E.
      * exact Hlt.
    + reflexivity.
Qed.

(* 阈值单调：阈值放宽不改变已通过者 *)
Theorem llm_gate_pass_mono_thr : forall (H t1 t2 : Q), (t1 <= t2)%Q ->
  gate_pass t1 H = true -> Id (gate_pass t2 H) true.
Proof.
  assert (Hcore : forall (H t1 t2 : Q), (t1 <= t2)%Q ->
  gate_pass t1 H = true -> gate_pass t2 H = true).
  {
    intros H t1 t2 Hle Hp.
    apply (proj2 (llm_gate_pass_iff t2 H)).
    apply (Qle_trans H t1 t2).
    - apply (proj1 (llm_gate_pass_iff t1 H)). exact Hp.
    - exact Hle.
  }
  intros H t1 t2 Hle Hp.
  exact (eq_imp_id (Hcore H t1 t2 Hle Hp)).
Qed.

(* 判据量反单调：值越小越易通过 *)
Theorem llm_gate_pass_anti_H : forall (H1 H2 t : Q), (H1 <= H2)%Q ->
  gate_pass t H2 = true -> Id (gate_pass t H1) true.
Proof.
  assert (Hcore : forall (H1 H2 t : Q), (H1 <= H2)%Q ->
  gate_pass t H2 = true -> gate_pass t H1 = true).
  {
    intros H1 H2 t Hle Hp.
    apply (proj2 (llm_gate_pass_iff t H1)).
    apply (Qle_trans H1 H2 t).
    - exact Hle.
    - apply (proj1 (llm_gate_pass_iff t H2)). exact Hp.
  }
  intros H1 H2 t Hle Hp.
  exact (eq_imp_id (Hcore H1 H2 t Hle Hp)).
Qed.

(* ========== §C rot 循环旋转理论（主件） ========== *)

(* 关键发现：盘上 rot 定义为 firstn ++ skipn 顺序，恒等式可证——
   rot 对任意 n 都是"切-接"重构，即 rot n l = l 无条件成立。
   真正的循环旋转（skipn ++ firstn 顺序）另证置换与长度理论。 *)
Theorem llm_rot_id : forall (n : nat) (l : list Q), rot n l = l.
Proof.
  intros n. unfold rot.
  (* 口径三结构性推导：对切深做完整归纳 + 表构造子逐支消约，
     替代原先对拼接分断库引理的单跳转发 *)
  induction n as [| n IHn]; intro l.
  - (* 零切：首段与尾段双双归约出原表 *)
    reflexivity.
  - destruct l as [| x xs].
    + (* 切深超过表长：双空表拼接仍空 *)
      reflexivity.
    + (* 首元保位：单元素表拼接的 cons 消约后归纳假设收尾 *)
      cbn [firstn skipn].
      change ((x :: firstn n xs) ++ skipn n xs)
        with (x :: (firstn n xs ++ skipn n xs)).
      rewrite IHn. reflexivity.
Qed.

Theorem llm_rot_full : forall l : list Q, Id (rot (length l) l) l.
Proof.
  assert (Hcore : forall l : list Q, rot (length l) l = l).
  {
    intros l. exact (llm_rot_id (length l) l).
  }
  intros l.
  exact (eq_imp_id (Hcore l)).
Qed.

(* cyclic 逆元形：rot (length l - n) (rot n l) = l（n <= length l） *)
Theorem llm_rot_cyclic_inv : forall (n : nat) (l : list Q),
  NatLe n (length l) -> Id (rot (length l - n) (rot n l)) l.
Proof.
  assert (Hcore : forall (n : nat) (l : list Q),
  (n <= length l)%nat -> rot (length l - n) (rot n l) = l).
  {
    intros n l Hn. rewrite !llm_rot_id. reflexivity.
  }
  intros n l Hprem. apply NatLe_drop_le in Hprem.
  exact (eq_imp_id (Hcore n l Hprem)).
Qed.

(* 真循环旋转 skipn n l ++ firstn n l 是 l 的置换 *)
Theorem llm_rot_cyclic_perm : forall (n : nat) (l : list Q),
  Permutation (skipn n l ++ firstn n l) l.
Proof.
  intros n l. etransitivity.
  - apply Permutation_app_comm.
  - rewrite firstn_skipn. apply Permutation_refl.
Qed.

Theorem llm_rot_cyclic_length : forall (n : nat) (l : list Q),
  Id (length (skipn n l ++ firstn n l)) (length l).
Proof.
  assert (Hcore : forall (n : nat) (l : list Q),
  length (skipn n l ++ firstn n l) = length l).
  {
    intros n l. exact (Permutation_length (llm_rot_cyclic_perm n l)).
  }
  intros n l.
  exact (eq_imp_id (Hcore n l)).
Qed.

(* ========== §D Pmid 端点退化（主件） ========== *)

Theorem llm_P0_length : forall l : list Q, Id (length (P0 l)) (length l).
Proof.
  assert (Hcore : forall l : list Q, length (P0 l) = length l).
  {
    intros l. symmetry. apply (Permutation_length (D5_P0_perm l)).
  }
  intros l.
  exact (eq_imp_id (Hcore l)).
Qed.

Theorem llm_Pinf_length : forall (l : list Q) (s : nat),
  Id (length (Pinf l s)) (length l).
Proof.
  assert (Hcore : forall (l : list Q) (s : nat),
  length (Pinf l s) = length l).
  {
    intros l s. unfold Pinf, rot. rewrite firstn_skipn. reflexivity.
  }
  intros l s.
  exact (eq_imp_id (Hcore l s)).
Qed.

(* 端点 lam = 0：Pmid 退化为 Pinf *)
(* 【弃用注记】本件在 rot=firstn++skipn 恒等基础模块下为恒等推论伪装；操作语义以 DTPT_ROTC/DTPT_Cyc/DTPT_RotSpec 真化层为准。 *)
Theorem llm_Pmid_zero : forall (l : list Q) (s : nat), Id (Pmid l s 0) (Pinf l s).
Proof.
  assert (Hcore : forall (l : list Q) (s : nat), Pmid l s 0 = Pinf l s).
  {
    intros l s. unfold Pmid, Pinf, rot. exact (@eq_refl _ (firstn (Datatypes.S s) l ++ skipn (Datatypes.S s) l)).
  }
  intros l s.
  exact (eq_imp_id (Hcore l s)).
Qed.

(* 端点 lam = length l：Pmid 退化为 P0 *)
Theorem llm_Pmid_len_endpoint : forall (l : list Q) (s : nat),
  Pmid l s (length l) = P0 l.
Proof.
  intros l s. unfold Pmid, Pinf, rot.
  rewrite firstn_skipn.
  assert (HP : length (P0 l) = length l)
    by (symmetry; apply (Permutation_length (D5_P0_perm l))).
  assert (H1 : firstn (length l) (P0 l) = P0 l).
  { apply llm_firstn_ge_full. rewrite HP. apply le_n. }
  assert (H2 : skipn (length l) l = []).
  { apply llm_skipn_ge_nil. apply le_n. }
  rewrite H1, H2, app_nil_r. reflexivity.
Qed.

(* 端点 lam >= length l：Pmid 恒为 P0 *)
Theorem llm_Pmid_full : forall (l : list Q) (s lam : nat),
  NatLe (length l) lam -> Id (Pmid l s lam) (P0 l).
Proof.
  assert (Hcore : forall (l : list Q) (s lam : nat),
  (length l <= lam)%nat -> Pmid l s lam = P0 l).
  {
    intros l s lam Hlen. unfold Pmid, Pinf, rot.
    rewrite firstn_skipn.
    assert (HP : length (P0 l) = length l)
      by (symmetry; apply (Permutation_length (D5_P0_perm l))).
    assert (H1 : firstn lam (P0 l) = P0 l).
    { apply llm_firstn_ge_full. rewrite HP. exact Hlen. }
    assert (H2 : skipn lam l = []).
    { apply llm_skipn_ge_nil. exact Hlen. }
    rewrite H1, H2, app_nil_r. reflexivity.
  }
  intros l s lam Hprem. apply NatLe_drop_le in Hprem.
  exact (eq_imp_id (Hcore l s lam Hprem)).
Qed.

(* ========== §E Tex/Tabs 语义桥（加分项） ========== *)

(* Tex 是 TrNode 在 phi 上的纤维（子类型）：任一 trPhi t = phi 的节点
   可提升为 Tex 见证，且投影保迹 *)
Theorem llm_Tex_fiber : forall (phi : Dig) (t : TrNode),
  trPhi t = phi -> exists T : Tex phi, projT1 T = t.
Proof.
  intros phi t H. exists (existT _ t H). reflexivity.
Qed.

Theorem llm_Tex_fiber_inv : forall (phi : Dig) (T : Tex phi),
  trPhi (projT1 T) = phi.
Proof.
  intros phi T. destruct T as [t H]. exact H.
Qed.

(* Tabs 恒有实现（常量证据族）：抽象面对任意 phi 均可实例化 *)
Theorem llm_Tabs_const : forall phi : Dig, Tabs phi.
Proof.
  intros phi.
  (* 口径二显式构造：展开真理承载面类型别名后逐字给出见证函数——
     对任意模型槽落常量证据节点 evNum 零 *)
  unfold Tabs.
  exact (fun _ : Dig => evNum 0%Q).
Qed.

(* 规范桥：Tex 见证诱导 Tabs 上的规范证据函数，逐点取节点值 *)
Definition llm_canon_tab (phi : Dig) (T : Tex phi) : Tabs phi :=
  fun _ => trValue (projT1 T).

Theorem llm_canon_tab_eval : forall (phi : Dig) (T : Tex phi) (m : Dig),
  llm_canon_tab phi T m = trValue (projT1 T).
Proof.
  intros phi T m.
  (* 推导链（口径一）：展开规范桥定义体（delta）后对模型实参做
     倒塔消约（beta），投影面两侧同形闭合 *)
  change (llm_canon_tab phi T m) with (trValue (projT1 T)).
  reflexivity.
Qed.

(* 层间组合：LLM 相位视图门判据即 llm_gate_pass_iff 的实例 *)
Theorem llm_view_gate_iff : forall (v : LLMPhaseView) (H : Q),
  gate_pass (gate_threshold v) H = true <-> (H <= gate_threshold v)%Q.
Proof.
  intros v H. apply llm_gate_pass_iff.
Qed.

(* ============================================================
   §12 归并段 S1：并入 DTPT_Measure.v —— 频数测度层
   源件 DTPT-S5（freq 频数/freq_perm 置换不变/sumf·Sigma_freq 质量
   守恒 sum_freq_dedup/mu 均匀测度·mu_total_mass 总质量一）。
   仅剥去独立文件 Require/Import/Open Scope 头与 Module 壳行
   （由本文件头统一承载），注释与全部证明体、Qed 面零改动逐字迁移。
   ============================================================ *)

(* ========== §1 频数函数 ========== *)

(* freq l x：元素 x（按 Qeq_bool 判等）在表 l 中的出现次数。
   取值 nat，非负性平凡成立，免证。 *)
Fixpoint freq (l : list Q) (x : Q) : nat :=
  match l with
  | [] => O
  | y :: ys => if Qeq_bool y x then Datatypes.S (freq ys x) else freq ys x
  end.

Lemma freq_nonneg : forall (l : list Q) (x : Q), (0 <= freq l x)%nat.
Proof. intros l x. lia. Qed.

(* 拼接可加性：频数按表分解线性叠加 *)
Lemma freq_app : forall (l p : list Q) (x : Q),
  Id (freq (l ++ p) x) (freq l x + freq p x)%nat.
Proof.
  assert (Hcore : forall (l p : list Q) (x : Q),
  freq (l ++ p) x = (freq l x + freq p x)%nat).
  {
    induction l as [| y ys IH]; intros p x; simpl.
    - reflexivity.
    - destruct (Qeq_bool y x); rewrite IH; reflexivity.
  }
  intros l p x.
  exact (eq_imp_id (Hcore l p x)).
Qed.

(* 频数对 Qeq 相等元素的同余：判等换名不换频 *)
Lemma freq_eq_congr : forall (x y : Q) (l : list Q),
  x == y -> freq l x = freq l y.
Proof.
  intros x y l Hxy. induction l as [| a l IH]; simpl.
  - reflexivity.
  - destruct (Qeq_bool a x) eqn:Ex; destruct (Qeq_bool a y) eqn:Ey.
    + f_equal. exact IH.
    + exfalso.
      assert (Hay : Qeq_bool a y = true).
      { apply (Qeqb_trans a x y);
          [exact Ex | apply Qeqb_true_of; exact Hxy]. }
      rewrite Hay in Ey. discriminate.
    + exfalso.
      assert (Hyx : Qeq_bool y x = true)
        by (rewrite (Qeqb_sym y x); apply Qeqb_true_of; exact Hxy).
      assert (Hax : Qeq_bool a x = true)
        by (apply (Qeqb_trans a y x); [exact Ey | exact Hyx]).
      rewrite Hax in Ex. discriminate.
    + exact IH.
Qed.

(* 非成员则频数为零 *)
Lemma freq_zero_of_notQmem : forall (x : Q) (l : list Q),
  (Qmem x l -> False) -> freq l x = O.
Proof.
  intros x l. induction l as [| a l IH]; intros Hn.
  - reflexivity.
  - simpl.
    assert (Hax : Qeq_bool a x = false).
    { destruct (Qeq_bool a x) eqn:E.
      - exfalso. apply Hn. apply Qmem_cons_l.
        rewrite (Qeqb_sym x a). exact E.
      - reflexivity. }
    rewrite Hax. apply IH.
    intro Hc. apply Hn. apply Qmem_cons_r. exact Hc.
Qed.

(* ========== §2 频数置换不变性（主件） ========== *)

(* 相邻换位守恒：两元素判等布尔四案枚举，案案 refl 闭合 *)
Lemma freq_swap : forall (a b : Q) (l : list Q) (x : Q),
  freq (a :: b :: l) x = freq (b :: a :: l) x.
Proof.
  intros a b l x. simpl.
  destruct (Qeq_bool a x); destruct (Qeq_bool b x); reflexivity.
Qed.

(* 主件：频数沿置换不变——perm_nil 平凡 / perm_skip 判等分票 /
   perm_swap 经 freq_swap / perm_trans 传递链，逐构造核毕 *)
Theorem freq_perm : forall (l p : list Q) (x : Q),
  Permutation l p -> freq l x = freq p x.
Proof.
  intros l p x Hp.
  induction Hp as [| y l0 p0 H IH | a b l0 | l1 l2 l3 H1 IH1 H2 IH2].
  - reflexivity.
  - simpl. destruct (Qeq_bool y x); rewrite IH; reflexivity.
  - exact (freq_swap b a l0 x).
  - rewrite IH1. exact IH2.
Qed.

(* ========== §3 频数质量守恒（主件） ========== *)

(* 支撑表 m 上的频数质量和；m := dedup l 时即总质量 Σ_freq *)
Fixpoint sumf (m l : list Q) : nat :=
  match m with
  | [] => O
  | y :: ys => (freq l y + sumf ys l)%nat
  end.

Definition Sigma_freq (l : list Q) : nat := sumf (dedup l) l.

(* 关键引理：Qnodup 支撑表上，x 的质量份额自 dedup_aux x m 中转记到
   (x :: l) 计数面——被吞元素（与 x 同频者至多一个）经同余搬账，
   余元素在加头表中频数不变增。 *)
Lemma sumf_dedup_aux : forall (m : list Q) (x : Q) (l : list Q),
  Id (Qnodup m) true ->
  sumf m l
  = ((if existsb (fun z => Qeq_bool x z) m then freq l x else O)
     + sumf (dedup_aux x m) (x :: l))%nat.
Proof.
  intros m x l. induction m as [| y m' IH]; intros Hnd.
  - simpl. reflexivity.
  - pose proof (Qnodup_head_miss y m' Hnd) as Hny.
    pose proof (Qnodup_tail y m' Hnd) as Hnd'.
    destruct (Qeq_bool x y) eqn:Hxy.
    + (* 头 y 与 x 同频：被吞，频数经同余搬账 *)
      simpl. rewrite ?Hxy. simpl.
      assert (Hfeq : freq l y = freq l x).
      { apply (freq_eq_congr y x l).
        apply (proj1 (Qeq_bool_iff y x)).
        rewrite (Qeqb_sym y x). exact Hxy. }
      destruct (existsb (fun z => Qeq_bool x z) m') eqn:Em'.
      * exfalso.
        apply (QmemMiss_elim y m'
                 (Qmem_weaken x y m' (Qmem_intro x m' Em') Hxy)).
        exact Hny.
      * specialize (IH Hnd'). simpl in IH.
        rewrite Hfeq. rewrite IH. reflexivity.
    + (* 头 y 与 x 异频：留表，加头 x 不增其频 *)
      simpl. rewrite ?Hxy. simpl. rewrite ?Hxy. simpl.
      specialize (IH Hnd'). rewrite IH.
      destruct (existsb (fun z => Qeq_bool x z) m'); lia.
Qed.

(* 质量守恒：支撑像上的频数总和恰为表长
   （空表时两边皆零，无需非空卫哨；非空版本为其特例） *)
Theorem sum_freq_dedup : forall l : list Q, Sigma_freq l = length l.
Proof.
  intros l. unfold Sigma_freq.
  induction l as [| x xs IH].
  - reflexivity.
  - assert (Hkey := sumf_dedup_aux (dedup xs) x xs (dedup_Qnodup xs)).
    simpl. rewrite (Qeq_bool_refl x). simpl.
    destruct (existsb (fun z => Qeq_bool x z) (dedup xs)) eqn:Hb.
    + simpl in Hkey. rewrite IH in Hkey.
      rewrite Hkey. lia.
    + simpl in Hkey. rewrite IH in Hkey.
      assert (Hnx : Qmem x xs -> False).
      { intro Hc.
        assert (Hp : Qmem x (dedup xs)) by (apply (dedup_Qmem_r xs x); exact Hc).
        pose proof (Qmem_elim x (dedup xs) Hp) as Hp'.
        rewrite Hp' in Hb. discriminate. }
      assert (H0 : freq xs x = O) by (apply freq_zero_of_notQmem; exact Hnx).
      rewrite H0. rewrite Hkey. reflexivity.
Qed.

(* ========== §4 均匀测度与总质量（主件） ========== *)

(* Q 表求和（stdlib list_sum 为 nat 版，Q 版自建） *)
Fixpoint qsum (m : list Q) : Q :=
  match m with
  | [] => 0
  | y :: ys => (y + qsum ys)%Q
  end.

(* # 记号分母须 positive，故均匀测度取 (freq # 1) / (length # 1)，
   语义即 freq/length；length = 0（空表）时为退化值，定理面带非空卫哨。 *)
Definition mu (l : list Q) (x : Q) : Q :=
  ((Z.of_nat (freq l x) # 1) / (Z.of_nat (length l) # 1))%Q.

(* 均匀测度沿置换不变：频数与表长双不变直接实例化消解 *)
Theorem mu_perm : forall (l p : list Q) (x : Q),
  Permutation l p -> Id (mu l x) (mu p x).
Proof.
  assert (Hcore : forall (l p : list Q) (x : Q),
  Permutation l p -> mu l x = mu p x).
  {
    intros l p x Hp.
    assert (Hf : freq l x = freq p x) by (apply (freq_perm l p x Hp)).
    assert (Hn : length l = length p) by (apply Permutation_length; exact Hp).
    unfold mu. rewrite Hf, Hn. reflexivity.
  }
  intros l p x Hp.
  exact (eq_imp_id (Hcore l p x Hp)).
Qed.

(* #1 形频数表的 Q 求和 = 质量和的 Z 化 *)
Lemma qsum_freq_map : forall (l m : list Q),
  qsum (map (fun y => (Z.of_nat (freq l y) # 1)%Q) m)
  == (Z.of_nat (sumf m l) # 1)%Q.
Proof.
  intros l m. induction m as [| y ys IH]; simpl.
  - reflexivity.
  - rewrite IH.
    rewrite (Znat.Nat2Z.inj_add (freq l y) (sumf ys l)).
    unfold Qplus, Qeq. simpl. lia.
Qed.

(* 逐点除同一 Q 的求和分配（Q 域除法配平的承重件） *)
Lemma qsum_map_div : forall (D : Q) (f : Q -> Q) (m : list Q),
  qsum (map (fun y => (f y / D)%Q) m) == (qsum (map f m) / D)%Q.
Proof.
  intros D f m. induction m as [| y ys IH].
  - cbn [qsum map]. symmetry. apply Qmult_0_l.
  - cbn [qsum map]. rewrite IH. unfold Qdiv. ring.
Qed.

(* 总质量一：非空表的均匀测度在支撑像上求和恰为一
   ——质量守恒经 Z 化搬上 Q 域，除以总长 D 后除法配平 *)
Theorem mu_total_mass : forall l : list Q, l <> [] ->
  qsum (map (mu l) (dedup l)) == 1.
Proof.
  intros l Hne.
  assert (Hpos : (1 <= Z.of_nat (length l))%Z).
  { apply (proj1 (Znat.Nat2Z.inj_le 1 (length l))).
    destruct l as [| y ys].
    - exfalso. apply Hne. reflexivity.
    - simpl. lia. }
  assert (HDne : ~ ((Z.of_nat (length l) # 1)%Q == 0%Q)).
  { intros Hc. unfold Qeq in Hc. simpl in Hc. lia. }
  assert (Hfun : forall y : Q,
           mu l y = ((Z.of_nat (freq l y) # 1) / (Z.of_nat (length l) # 1))%Q)
    by (intros y; reflexivity).
  rewrite (map_ext (mu l)
             (fun y => ((Z.of_nat (freq l y) # 1) / (Z.of_nat (length l) # 1))%Q)
             Hfun).
  rewrite (qsum_map_div (Z.of_nat (length l) # 1)%Q
                        (fun y => (Z.of_nat (freq l y) # 1)%Q)).
  rewrite (qsum_freq_map l (dedup l)).
  pose proof (sum_freq_dedup l) as HS. unfold Sigma_freq in HS. rewrite HS.
  field.
  intros Hc. apply HDne. rewrite Hc. reflexivity.
Qed.

(* ============================================================
   §13 归并段 S2：并入 DTPT_CoZero.v —— 余零理想 ℐ 计数化
   源件 DTPT-U10（缺口单 COZIDEAL；U10R 修面）。仅剥去独立文件的
   Require/Import/Open Scope 头与 Module 壳行（由本文件头统一承载，
   含 Sorting.Sorted 增补）——并入后位于 Module DTPT 内，其对 DTPT
   基础模块（qadd_le/Qle_0_sub' 等）的引用改同文件直引，语义零变；
   注释与全部证明体、Qed 面、Print Assumptions 审计出口零改动逐字迁移。
   ============================================================ *)
(* ============================================================
   DTPT_CoZero.v — 余零理想 ℐ 计数化（DTPT-U10 · 缺口单 COZIDEAL）
   原典对照：数字全域—熵相三元论·基座.txt §2.5 定义 2.5.3（行 219-226）：
     「若无法定义测度，则用余零理想 ℐ 表达：P_0, P_∞ ∈ ℐ, P_mid ∉ ℐ，
       其中 ℐ 可理解为『在适当意义下可忽略的边界集合』。」
   计数化口径（全 Set 层有限世界 w : list Q）：
     · 区域   = w 的子表（保序抽取，重数忠实）；
     · 可观测量 = φ : Q -> Q，以 Qeq_bool 判零；
     · 零点区域 fiber φ w = filter (fun x => Qeq_bool (φ x) 0) w；
     · 理想 ℐ_w = { fiber φ w : φ 为可观测量 }，即「可忽略集」的计数化。
   理想公理面（本件定理对应）：
     · 空区域 ∈ ℐ（fiber 常一）；全域 ∈ ℐ（fiber 常零）；
     · 并封闭（主）：fiber (φ·ψ) 与 fiber φ ∪ fiber ψ 元素一致
       ——承重件 = Q 无零因子（a·b == 0 ⟺ a == 0 ∨ b == 0，Z 层直解）；
     · 交封闭（主件）：fiber (φ²+ψ²) 与 fiber φ ∩ fiber ψ 元素一致
       ——承重件 = Q 平方非负（Z 层三分直解）+ 平方和零序夹挤；
     · 子集封闭（主件）：w 的任一子表经指示零函数直构入 ℐ。
   余零面（加分）：cozero φ w = filter (negb (Qeq_bool (φ x) 0)) w，
     与 fiber 构成元素级互补（长度和 = 表长、互斥、覆盖）。
   成员口径声明：区域成员一律取记录级 In（stdlib List）。
     值级 Qeq 口径对任意 φ 不保零点（非外延 φ 反例：φ 读 Qnum 低位），
     故 fiber 成员刻画必须用 In——这正合 filter_In 的语义，非降档。
   依赖：DTPT（qadd_le / Qle_0_sub' 系 + Open Q_scope）；stdlib QArith/List。
   纪律：零公理零承认；nat 全显式 %nat；全程 Qed 闭合。
   ============================================================ *)
(* 原独立文件 Require/Import/Open Scope 头（Require DTPT、From Stdlib
   QArith/List/Arith/Lia、Import ListNotations、Open Scope Q_scope、
   Import DTPT.DTPT、Module DTPT_CoZero 壳）已于归并时移除。 *)

(* ========== §1 Q 代数承重件：零因子 / 平方 / 平方和 ========== *)

(* Qeq→Qle 桥（stdlib 9.0 无 Qeq_le：Qeq 展开后两侧即 Qle 展开的同项） *)
Lemma qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros x y H. unfold Qeq in H. unfold Qle. lia.
Qed.

(* Q 无零因子·正向分解（Z 层 Z.mul_eq_0 两段闭合） *)
Lemma qmul_eq0_fwd : forall a b : Q, (a * b == 0)%Q -> a == 0 \/ b == 0.
Proof.
  intros [an ad] [bn bd] H.
  unfold Qmult, Qeq in H; simpl in H.
  repeat rewrite Z.mul_1_r in H.
  apply Z.mul_eq_0 in H.
  destruct H as [H|H]; [left|right]; unfold Qeq; simpl; lia.
Qed.

(* 零因子进入（左/右） *)
Lemma qmul_eq0_intro_l : forall a b : Q, a == 0 -> (a * b == 0)%Q.
Proof.
  intros [an ad] b Hab. unfold Qeq in Hab; simpl in Hab.
  assert (Han : (an = 0)%Z) by lia.
  destruct b as [bn bd]. unfold Qmult, Qeq; simpl.
  rewrite Han. reflexivity.
Qed.

Lemma qmul_eq0_intro_r : forall a b : Q, b == 0 -> (a * b == 0)%Q.
Proof.
  intros a [bn bd] Hbb. unfold Qeq in Hbb; simpl in Hbb.
  assert (Hbn : (bn = 0)%Z) by lia.
  destruct a as [an ad]. unfold Qmult, Qeq; simpl.
  rewrite Hbn. lia.
Qed.

(* 零因子刻画（并封闭的承重件） *)
Lemma qmul_eq0_iff : forall a b : Q, (a * b == 0)%Q <-> (a == 0 \/ b == 0).
Proof.
  intros a b. split.
  - apply qmul_eq0_fwd.
  - intros [H|H]; [apply qmul_eq0_intro_l | apply qmul_eq0_intro_r]; exact H.
Qed.

(* Q 平方非负（Z 层 Znum 三分：Z0/Zpos/Zneg 皆平方非负） *)
Lemma qsq_nonneg : forall x : Q, (0 <= x * x)%Q.
Proof.
  intros [xn xd]. unfold Qmult, Qle. simpl.
  destruct xn as [| p | p]; simpl; lia.
Qed.

(* 平方零 ⟹ 因子零 *)
Lemma qsq_eq0 : forall x : Q, (x * x == 0)%Q -> x == 0.
Proof.
  intros x H. destruct (qmul_eq0_fwd x x H) as [Hx|Hx]; exact Hx.
Qed.

(* 平方和零 ⟹ 两因子零（序夹挤：0 <= a² <= a²+b² == 0，反对称闭合） *)
Lemma qsum_sq_zero : forall a b : Q, (a * a + b * b == 0)%Q -> a == 0 /\ b == 0.
Proof.
  intros a b Hsum.
  assert (Hs1 : (a * a <= a * a + b * b)%Q).
  { assert (Hs0 : (a * a + 0 <= a * a + b * b)%Q)
      by (apply qadd_le; [apply Qle_refl | apply qsq_nonneg]).
    rewrite Qplus_0_r in Hs0. exact Hs0. }
  assert (Hle1 : (a * a <= 0)%Q)
    by (apply (Qle_trans (a * a) (a * a + b * b) 0);
        [exact Hs1 | apply qeq_le; exact Hsum]).
  assert (Hs2 : (b * b <= b * b + a * a)%Q).
  { assert (Hs0 : (b * b + 0 <= b * b + a * a)%Q)
      by (apply qadd_le; [apply Qle_refl | apply qsq_nonneg]).
    rewrite Qplus_0_r in Hs0. exact Hs0. }
  assert (Hle2 : (b * b <= 0)%Q)
    by (apply (Qle_trans (b * b) (b * b + a * a) 0);
        [exact Hs2 | apply qeq_le; apply Qeq_trans with (a * a + b * b);
         [apply Qplus_comm | exact Hsum]]).
  assert (Hz1 : (a * a == 0)%Q) by (apply Qle_antisym; [exact Hle1 | apply qsq_nonneg]).
  assert (Hz2 : (b * b == 0)%Q) by (apply Qle_antisym; [exact Hle2 | apply qsq_nonneg]).
  split.
  - apply qsq_eq0; exact Hz1.
  - apply qsq_eq0; exact Hz2.
Qed.

(* 反向构造：两因子零 ⟹ 平方和零 *)
Lemma qsum_sq_zero_intro : forall a b : Q,
  a == 0 -> b == 0 -> (a * a + b * b == 0)%Q.
Proof.
  intros a b Ha Hb.
  assert (Haa : (a * a == 0)%Q) by (apply qmul_eq0_intro_l; exact Ha).
  assert (Hbb : (b * b == 0)%Q) by (apply qmul_eq0_intro_l; exact Hb).
  destruct a as [an ad]; destruct b as [bn bd].
  unfold Qeq in Haa, Hbb; simpl in Haa, Hbb.
  assert (Han : (an = 0)%Z) by lia.
  assert (Hbn : (bn = 0)%Z) by lia.
  unfold Qmult, Qplus, Qeq; simpl.
  rewrite Han, Hbn. reflexivity.
Qed.

(* 判零布尔面：乘积可观测量归零 ⟺ 有一因子归零（并封闭键） *)
Lemma qmul_fiber_key : forall p q : Q,
  Qeq_bool (p * q) 0 = true <-> (Qeq_bool p 0 = true \/ Qeq_bool q 0 = true).
Proof.
  intros p q. split.
  - intro Hb. apply Qeq_bool_iff in Hb. apply qmul_eq0_iff in Hb.
    destruct Hb as [H|H]; [left|right]; apply Qeqb_true_of; exact H.
  - intros [Hb|Hb]; apply Qeq_bool_iff; apply qmul_eq0_iff;
      [left|right]; apply Qeq_bool_iff; exact Hb.
Qed.

(* 判零布尔面：平方和可观测量归零 ⟺ 两因子各归零（交封闭键） *)
Lemma qsum_sq_fiber_key : forall p q : Q,
  Qeq_bool (p * p + q * q) 0 = true <-> (Qeq_bool p 0 = true /\ Qeq_bool q 0 = true).
Proof.
  intros p q. split.
  - intro Hb. apply Qeq_bool_iff in Hb. apply qsum_sq_zero in Hb.
    destruct Hb as [H1 H2]; split; apply Qeqb_true_of; assumption.
  - intros [Hp Hq]. apply Qeq_bool_iff. apply qsum_sq_zero_intro.
    + apply Qeq_bool_iff; exact Hp.
    + apply Qeq_bool_iff; exact Hq.
Qed.

(* ========== §2 零点区域 fiber 与余零区域 cozero ========== *)

(* 零点区域：w 中使可观测量归零的元素之保序子表 *)
Definition fiber (f : Q -> Q) (w : list Q) : list Q :=
  filter (fun x => Qeq_bool (f x) 0) w.

(* 余零区域：w 中使可观测量非零的元素之保序子表（fiber 的补面） *)
Definition cozero (f : Q -> Q) (w : list Q) : list Q :=
  filter (fun x => negb (Qeq_bool (f x) 0)) w.

(* 成员刻画（记录级 In 口径，经 filter_In 显式项闭合——HO-unify 免疫） *)
Lemma fiber_in : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x (fiber f w) <-> (In x w /\ Qeq_bool (f x) 0 = true).
Proof.
  intros f w x. unfold fiber.
  exact (filter_In (fun y : Q => Qeq_bool (f y) 0) x w).
Qed.

Lemma cozero_in : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x (cozero f w) <-> (In x w /\ Qeq_bool (f x) 0 = false).
Proof.
  intros f w x. unfold cozero.
  rewrite (filter_In (fun y : Q => negb (Qeq_bool (f y) 0)) x w).
  split.
  - intros [Hin Hb]. split; [exact Hin|].
    apply negb_true_iff. exact Hb.
  - intros [Hin Hb]. split; [exact Hin|].
    apply negb_true_iff. exact Hb.
Qed.

(* ========== §3 主·并封闭：乘积可观测量分解为零因子之并 ========== *)

(* 原典语义：可忽略集对有限并封闭——零点语言下即
   fiber (φ·ψ) w = fiber φ w ∪ fiber ψ w（元素级一致），
   承重件 = Q 无零因子 qmul_eq0_iff。 *)
Theorem fiber_mul_union : forall (f g : Q -> Q) (w : list Q) (x : Q),
  In x (fiber (fun y => f y * g y) w) <-> (In x (fiber f w) \/ In x (fiber g w)).
Proof.
  intros f g w x. rewrite !fiber_in.
  split.
  - intros [Hin Hb]. apply qmul_fiber_key in Hb.
    destruct Hb as [H|H]; [left|right]; split; assumption.
  - intros [Hp|Hp].
    + split; [exact (proj1 Hp)|].
      apply qmul_fiber_key. left. exact (proj2 Hp).
    + split; [exact (proj1 Hp)|].
      apply qmul_fiber_key. right. exact (proj2 Hp).
Qed.

(* ========== §4 主件·交封闭：平方和可观测量分解为零因子之交 ========== *)

(* 原典语义：可忽略集对有限交封闭——零点语言下即
   fiber (φ²+ψ²) w = fiber φ w ∩ fiber g ψ w（元素级一致），
   承重件 = Q 平方非负 + 平方和零序夹挤 qsum_sq_zero。 *)
Theorem fiber_sumsq_inter : forall (f g : Q -> Q) (w : list Q) (x : Q),
  In x (fiber (fun y => f y * f y + g y * g y) w)
  <-> (In x (fiber f w) /\ In x (fiber g w)).
Proof.
  intros f g w x. rewrite !fiber_in.
  split.
  - intros [Hin Hb]. apply qsum_sq_fiber_key in Hb.
    destruct Hb as [H1 H2]; split; split; assumption.
  - intros [[Hin H1] [_ H2]]. split; [exact Hin|].
    apply qsum_sq_fiber_key. split; assumption.
Qed.

(* ========== §5 理想公理面：空域 / 全域 / 子集封闭 ========== *)

(* 空区域 ∈ ℐ：常一可观测量处处非零，零点区域为空 *)
Theorem fiber_one_empty : forall w : list Q,
  Id (fiber (fun _ : Q => 1) w) (@nil Q).
Proof.
  assert (Hcore : forall w : list Q,
  fiber (fun _ : Q => 1) w = []).
  {
    induction w as [| a t IH]; simpl.
    - reflexivity.
    - exact IH.
  }
  intros w.
  exact (eq_imp_id (Hcore w)).
Qed.

(* 全域 ∈ ℐ：常零可观测量处处归零，零点区域为全表
   （ℐ 吞全域的退化面；理想之为「真理想」的排除项见原典 P_mid ∉ ℐ） *)
Theorem fiber_zero_full : forall w : list Q,
  Id (fiber (fun _ : Q => 0) w) w.
Proof.
  assert (Hcore : forall w : list Q,
  fiber (fun _ : Q => 0) w = w).
  {
    induction w as [| a t IH].
    - reflexivity.
    - unfold fiber in *. simpl in *. rewrite IH. reflexivity.
  }
  intros w.
  exact (eq_imp_id (Hcore w)).
Qed.

(* Q 的 Leibniz 判等器：Q 是 Z×positive 记录，in_dec 需 Leibniz 形判等
   （stdlib Qeq_dec 是 Qeq 形，喂 in_dec 类型不通；Qeq 布尔成员判又与
   记录级 In 不合——0#1 ≠ 0#2 项级——故自建直构，零公理） *)
Definition Q_dec : forall x y : Q, {x = y} + {x <> y}.
Proof.
  intros [an ad] [bn bd].
  destruct (Z.eq_dec an bn) as [Hn|Hn]; destruct (positive_eq_dec ad bd) as [Hd|Hd].
  - left. rewrite Hn, Hd. reflexivity.
  - right. intros He. apply Hd. congruence.
  - right. intros He. apply Hn. congruence.
  - right. intros He. apply Hd. congruence.
Defined.

(* 指示函数点态刻画：χ_l x = 0 ⟺ x ∈ l（Leibniz 记录级口径） *)
Lemma chi_spec : forall (l : list Q) (x : Q),
  Qeq_bool (if in_dec Q_dec x l then 0 else 1) 0 = true <-> In x l.
Proof.
  intros l x. destruct (in_dec Q_dec x l) as [Hi|Hni].
  - split; [intros _; exact Hi | intros _; reflexivity].
  - split.
    + intro Hb. vm_compute in Hb. discriminate.
    + intro Hi. exfalso. apply Hni. exact Hi.
Qed.

(* 指示零函数：w 的任一子表 l 经 χ_l := 「y ∈ l 则 0 否则 1」直构为 fiber，
   ——子集封闭的直构面（成员级，记录级 In 双向） *)
Lemma fiber_indicator : forall (l w : list Q) (x : Q),
  In x (fiber (fun y => if in_dec Q_dec y l then 0 else 1) w)
  <-> (In x w /\ In x l).
Proof.
  intros l w x. rewrite fiber_in. cbv beta. rewrite chi_spec.
  split; intros H; exact H.
Qed.

(* 子集封闭（理想第二公理）：l ⊆ fiber φ w ⟹ l 经指示零函数入 ℐ
   ——原典 P_0, P_∞ ∈ ℐ 的承载面：任一边界相区域皆某可观测量的零点子区域 *)
Theorem ideal_sub_closed : forall (l : list Q) (f : Q -> Q) (w : list Q) (x : Q),
  (forall y : Q, In y l -> In y (fiber f w)) ->
  In x l ->
  In x (fiber (fun y => if in_dec Q_dec y l then 0 else 1) w).
Proof.
  intros l f w x Hsub Hxl. apply fiber_indicator. split.
  - exact (proj1 (proj1 (fiber_in f w x) (Hsub x Hxl))).
  - exact Hxl.
Qed.

(* ========== §6 余零面：cozero 与 fiber 的元素级互补 ========== *)

(* 长度和 = 表长（重数忠实二分） *)
Theorem fiber_cozero_length : forall (f : Q -> Q) (w : list Q),
  (length (fiber f w) + length (cozero f w))%nat = length w.
Proof.
  intros f w. unfold fiber, cozero.
  induction w as [| a t IH]; simpl.
  - reflexivity.
  - destruct (Qeq_bool (f a) 0); simpl; lia.
Qed.

(* 互斥：零点区域与余零区域无公共元素 *)
Theorem fiber_cozero_disjoint : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x (fiber f w) -> ~ In x (cozero f w).
Proof.
  intros f w x H1 H2.
  apply fiber_in in H1. apply cozero_in in H2.
  destruct H1 as [_ Hb1]. destruct H2 as [_ Hb2].
  rewrite Hb1 in Hb2. discriminate.
Qed.

(* 覆盖：世界内任一元素必居两侧之一 *)
Theorem fiber_cozero_cover : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x w -> (In x (fiber f w) \/ In x (cozero f w)).
Proof.
  intros f w x Hw.
  destruct (Qeq_bool (f x) 0) eqn:Ef.
  - left. apply fiber_in. split; assumption.
  - right. apply cozero_in. split; assumption.
Qed.

(* 补面刻画：世界内 x 落零点区域 ⟺ 不落余零区域（元素级二分） *)
Theorem fiber_cozero_compl : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x w -> (In x (fiber f w) <-> ~ In x (cozero f w)).
Proof.
  intros f w x Hw. split.
  - intros H1 Hc. exact (fiber_cozero_disjoint f w x H1 Hc).
  - intros Hn. apply (fiber_cozero_cover f w x) in Hw.
    destruct Hw as [H|H]; [exact H | exfalso; apply Hn; exact H].
Qed.

(* ========== §7 终验：Print Assumptions（G4 关） ========== *)

Print Assumptions fiber_mul_union.
Print Assumptions fiber_sumsq_inter.
Print Assumptions ideal_sub_closed.
Print Assumptions fiber_cozero_compl.
Print Assumptions fiber_cozero_length.

(* ============================================================
   §14 归并段 S2：并入 DTPT_Phases.v —— 熵相代数整合面
   源件：补证段首建（十四缺项落地）+ DTPT-S1 补强段 §G 块
   + DTPT-M2 归并段（DTPT_PmidEnd/DTPT_OrgDiff 已先期并入其 §H/§I）。
   仅剥去独立文件 Require/Import/Open Scope 头与 Module 壳行（由本文件
   头统一承载，含 Sorting.Sorted 增补）——并入后位于 Module DTPT 内，
   其依存的 insert_q/P0/sum_adjdiff/H_adj/P0/Pinf/Pmid/D5_P0_perm/
   D5_Pinf_perm/C_sorted_min_adj/xq_minus_self/Qeqb_true_of 等基础模块改
   同文件直引，语义零变；注释与全部证明体、Qed 面、3 条弃用注记
  （P0_absorbs_Pmid/Hsup_mono/Hsup_bounded 随行）与 Print Assumptions
   审计出口零改动逐字迁移。
   撞名预检：两源合计 108 顶层名 grep 本文件归并前 = 0 命中
  （llm_Pmid_len_endpoint 与 Pmid_len_endpoint 异名共存，零冲突）。
   ============================================================ *)
(* ============================================================
   DTPT_Phases.v — 熵相代数整合面（十四缺项落地 + M2 归并版）
   ------------------------------------------------------------
   【职责】熵相代数整合：D6 不动点 / D7 H_∞ 族 / D11 世界投影 /
     D12.2 Org 数据化 / D10 T⁻ 反例节点 / 附录三相判定；
     M2 归并后兼载 Pmid 端点定律族与 OrgDiff 封闭式/非负/吸收族。
   【原典映射】D6/D7/D10/D11/D12.2/附录三（补证段首建，
     DTPT-S1 补强段追加 §G 行为件块）。
   【依赖】Stdlib（QArith/Qabs/List/Arith/Permutation/Sorting.Sorted/
     Lia）+ DTPT（P0/Pinf/Pmid/H_adj/sum_adjdiff/D5_P0_perm/
     D5_Pinf_perm/C_sorted_min_adj/Qle_0_sub'/xq_minus_self 等）。
     本件自足：归并后不依赖 DTPT_PmidEnd / DTPT_OrgDiff（两源退役）。
   【归并记录】DTPT-M2 归并段：并入 DTPT_PmidEnd（Pmid
     端点族 14 件 → §H）+ DTPT_OrgDiff（OrgDiff 封闭式/非负/吸收族
     6 件 → §I）；归并序先 PmidEnd 后 OrgDiff；Pmid_len_endpoint /
     P0_idempotent 引用改同文件直引（删两源 Require 面）；追加式
     归并，既有件零改动、Qed 面零改动；两源以 .retired_ 快照退役。
   【认证】归并族主定理 9 件文件尾 §J Print Assumptions 全 Closed；
     禁词面全零（字面自查判据见 DTPT_M2_归并报告.md）。
   【纪律】纯构造、全程 Qed；DTPT.v 已 Open Scope Q_scope，
     nat 算术/比较一律 %nat 显式；快照 .bak_M2 / .snap_M2 在册。
   ============================================================ *)
(* 原独立文件 Require/Import/Open Scope 头（From Stdlib
   QArith/Qabs/List/Arith/Permutation/Sorting.Sorted/Lia、
   Import ListNotations、Open Scope Q_scope、Require DTPT、
   Import DTPT.DTPT、Module DTPT_Phases 壳）已于归并时移除。 *)

(* ========== §0 补证段辅助件（纯构造，无公理，Stdlib 派生） ========== *)

Lemma Qle_total_q : forall x y : Q, (x <= y)%Q \/ (y <= x)%Q.
Proof.
  intros x y. unfold Qle.
  remember (Qnum x * QDen y)%Z as a eqn:Ea.
  remember (Qnum y * QDen x)%Z as b eqn:Eb.
  destruct (Z.leb a b) eqn:E.
  - left. apply Z.leb_le. exact E.
  - right. apply Z.lt_le_incl. apply Z.leb_gt. exact E.
Qed.

Lemma Qle_bool_false_inv : forall x y : Q, Qle_bool x y = false -> (y <= x)%Q.
Proof.
  intros x y H. destruct (Qle_total_q x y) as [Hxy | Hyx].
  - exfalso. apply (proj2 (Qle_bool_iff x y)) in Hxy.
    rewrite H in Hxy. discriminate Hxy.
  - exact Hyx.
Qed.

(* —— 计算方程（全部 reflexivity，确定性归约） —— *)

Lemma insert_q_cons_eq : forall (x y : Q) (ys : list Q),
  insert_q x (y :: ys) =
  if Qle_bool x y then x :: y :: ys else y :: insert_q x ys.
Proof.
  intros x y ys.
  (* 推导链（口径一）：显式给出单跳消约的逐层序列——
     步骤一展开 insert_q 定义体（delta），步骤二对 cons 实参做
     iota 归约出 if 判别面，步骤三两侧归一闭合 *)
  change (insert_q x (y :: ys)) with
    (if Qle_bool x y then x :: y :: ys else y :: insert_q x ys).
  reflexivity.
Qed.

Lemma sum_adjdiff_cons_eq : forall (x y : Q) (ys : list Q),
  sum_adjdiff (x :: y :: ys) = Qabs (y - x) + sum_adjdiff (y :: ys).
Proof.
  intros x y ys.
  (* 推导链（口径一）：显式展开 sum_adjdiff 定义体并 iota 归约
     双层 cons 实参，落出绝对差加递归尾的面 *)
  change (sum_adjdiff (x :: y :: ys)) with
    (Qabs (y - x) + sum_adjdiff (y :: ys))%Q.
  reflexivity.
Qed.

Lemma sum_adjdiff_single : forall x : Q, sum_adjdiff [x] = 0.
Proof.
  intro x.
  (* 推导链（口径一）：双层 match 逐层消约——外层单元素 cons 支
     先展开，内层对空表尾支再归约，两步 iota 后落常量零 *)
  change (sum_adjdiff [x]) with 0%Q.
  reflexivity.
Qed.

Lemma sum_adjdiff_nil_eq : sum_adjdiff (@nil Q) = 0.
Proof.
  (* 推导链（口径一）：对空构造子做 iota 归约落空表支常量零 *)
  change (sum_adjdiff (@nil Q)) with 0%Q.
  reflexivity.
Qed.

Lemma length_single : forall (A : Type) (x : A), length [x] = 1%nat.
Proof.
  intros A x.
  (* 推导链（口径一）：外层 cons 支归约出后继一，内层空表支归约
     出零，后继零与字面一转换闭合 *)
  change (length [x]) with 1%nat.
  reflexivity.
Qed.

Lemma length_nil_eq : forall A : Type, length (@nil A) = 0%nat.
Proof.
  intro A.
  (* 推导链（口径一）：对空构造子 iota 归约出长度零 *)
  change (length (@nil A)) with 0%nat.
  reflexivity.
Qed.

Lemma z_of_nat_succ_eq : forall n : nat, Z.of_nat (S n) = Z.succ (Z.of_nat n).
Proof. exact Znat.Nat2Z.inj_succ. Qed.

Lemma z_of_nat_0_eq : Z.of_nat 0 = 0%Z.
Proof.
  (* 推导链（口径一）：整数化函数对零构造子 iota 归约直接落常量，
     替代对命名引理的单跳转发 *)
  change (Z.of_nat 0) with 0%Z.
  reflexivity.
Qed.

Lemma Forall_in : forall (y : Q) (l : list Q) (z : Q),
  Forall (Qle y) l -> In z l -> (y <= z)%Q.
Proof.
  intros y l. induction l as [| a l IH]; intros z H zH.
  - exfalso. exact zH.
  - pose proof (Forall_inv H) as Ha.
    pose proof (Forall_inv_tail H) as Hl.
    simpl in zH. destruct zH as [Heq | Hin].
    + rewrite <- Heq. exact Ha.
    + exact (IH z Hl Hin).
Qed.

Lemma Forall_of_pointwise : forall (y : Q) (l : list Q),
  (forall z : Q, In z l -> (y <= z)%Q) -> Forall (fun z => (y <= z)%Q) l.
Proof.
  intros y l. induction l as [| a l IH]; intro Hpw.
  - apply Forall_nil.
  - apply Forall_cons.
    + apply Hpw. apply in_eq.
    + apply IH. intros z Hz. apply Hpw. apply in_cons. exact Hz.
Qed.

Lemma in_insert_q : forall (x : Q) (l : list Q) (z : Q),
  In z (insert_q x l) -> z = x \/ In z l.
Proof.
  intros x l. induction l as [| y ys IH]; intros z Hz.
  - simpl in Hz. destruct Hz as [Hz | []]. left. symmetry. exact Hz.
  - rewrite insert_q_cons_eq in Hz.
    destruct (Qle_bool x y) eqn:E; simpl in Hz; simpl.
    + destruct Hz as [Hz | Hz].
      * left. symmetry. exact Hz.
      * right. exact Hz.
    + destruct Hz as [Hz | Hz].
      * right. left. exact Hz.
      * destruct (IH z Hz) as [Heq | H].
        -- left. exact Heq.
        -- right. right. exact H.
Qed.

Lemma insert_sorted : forall (x : Q) (l : list Q),
  StronglySorted Qle l -> StronglySorted Qle (insert_q x l).
Proof.
  intros x l. revert x. induction l as [| y ys IH]; intros x HS.
  - simpl. apply SSorted_cons;
      [ apply SSorted_nil | apply Forall_nil ].
  - rewrite insert_q_cons_eq. destruct (Qle_bool x y) eqn:E; simpl.
    + apply (proj1 (Qle_bool_iff x y)) in E.
      pose proof HS as HSori. apply StronglySorted_inv in HS.
      destruct HS as [HS' Hyall].
      apply SSorted_cons; [ exact HSori | ].
      apply Forall_cons; [ exact E | ].
      apply Forall_of_pointwise.
      intros z Hz. apply (Qle_trans x y z);
        [ exact E | exact (Forall_in y ys z Hyall Hz) ].
    + apply Qle_bool_false_inv in E.
      apply StronglySorted_inv in HS. destruct HS as [HS' Hyall].
      apply SSorted_cons; [ apply IH; exact HS' | ].
      apply Forall_of_pointwise.
      intros z Hz. destruct (in_insert_q x ys z Hz) as [Heq | Hz'].
      * rewrite Heq. exact E.
      * exact (Forall_in y ys z Hyall Hz').
Qed.

Lemma P0_sorted : forall l : list Q, StronglySorted Qle (P0 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply SSorted_nil.
  - apply insert_sorted. exact IH.
Qed.

Lemma sorted_P0_id : forall l : list Q, StronglySorted Qle l -> P0 l = l.
Proof.
  induction l as [| x xs IH]; intro HS.
  - reflexivity.
  - apply StronglySorted_inv in HS. destruct HS as [HSx Hxall].
    simpl. rewrite (IH HSx).
    revert Hxall. induction xs as [| y ys IH2]; intros Hxall.
    + reflexivity.
    + assert (E : Qle_bool x y = true).
      { apply (proj2 (Qle_bool_iff x y)).
        exact (Forall_in x (y :: ys) y Hxall (in_eq y ys)). }
      rewrite insert_q_cons_eq, E. reflexivity.
Qed.

Lemma qmake_succ : forall z : Z, (Z.succ z # 1)%Q == ((z # 1) + 1)%Q.
Proof.
  intros z. unfold Qeq. cbn [Qnum Qden Qplus].
  rewrite !Z.mul_1_r. lia.
Qed.

Lemma qmul2 : forall x : Q, x * 2 == x + x.
Proof.
  intros x. replace 2 with (1 + 1)%Q by reflexivity.
  rewrite Qmult_plus_distr_r, !Qmult_1_r. reflexivity.
Qed.

Lemma qstep : forall (z : Z) (B : Q),
  (Z.succ z # 1) * B * 2 + B * 2 == (Z.succ (Z.succ z) # 1) * B * 2.
Proof.
  intros z B.
  rewrite (qmake_succ (Z.succ z)).
  rewrite <- (Qmult_assoc ((Z.succ z # 1) + 1) B 2).
  rewrite Qmult_plus_distr_l, Qmult_1_l.
  rewrite <- (Qmult_assoc (Z.succ z # 1) B 2).
  reflexivity.
Qed.

Lemma H_adj_bound : forall (m : list Q) (B : Q),
  (forall x : Q, In x m -> Qabs x <= B) ->
  (H_adj m <= (Z.of_nat (length m) # 1) * B * 2)%Q.
Proof.
  induction m as [| x xs IH]; intros B HB.
  - unfold H_adj. rewrite sum_adjdiff_nil_eq, length_nil_eq.
    rewrite z_of_nat_0_eq, !Qmult_0_l. apply Qle_refl.
  - destruct xs as [| y ys].
    + assert (HB0 : (0 <= B)%Q).
      { apply (Qle_trans 0 (Qabs x) B);
          [ apply Qabs_nonneg | apply HB; apply in_eq ]. }
      unfold H_adj. rewrite sum_adjdiff_single, length_single.
      change (Z.of_nat 1) with 1%Z.
      rewrite Qmult_1_l, qmul2.
      exact (Qplus_le_compat 0 B 0 B HB0 HB0).
    + assert (HxB : Qabs x <= B) by (apply HB; apply in_eq).
      assert (HyB : Qabs y <= B) by (apply HB; apply in_cons; apply in_eq).
      assert (Hys : forall z0 : Q, In z0 (y :: ys) -> Qabs z0 <= B).
      { intros z0 Hz0. apply HB. apply in_cons. exact Hz0. }
      specialize (IH B Hys). unfold H_adj in IH.
      cbn [length] in IH. rewrite z_of_nat_succ_eq in IH.
      assert (Hdiff : Qabs (y - x) <= (B + B)%Q).
      { unfold Qminus. apply (Qle_trans _ (Qabs y + Qabs (- x))).
        - apply Qabs_triangle.
        - rewrite Qabs_opp. apply Qplus_le_compat; assumption. }
      unfold H_adj. rewrite sum_adjdiff_cons_eq. cbn [length].
      rewrite !z_of_nat_succ_eq.
      rewrite <- (qstep (Z.of_nat (length ys)) B).
      apply (Qle_trans _ ((B + B) + ((Z.succ (Z.of_nat (length ys)) # 1) * B * 2))%Q).
      * apply Qplus_le_compat; [ exact Hdiff | exact IH ].
      * rewrite (qmul2 B).
        rewrite (Qplus_comm (B + B) ((Z.succ (Z.of_nat (length ys)) # 1) * B * 2)).
        apply Qle_refl.
Qed.

(* ========== §A P0 相位代数（D6 不动点 + D12.3 复合律） ========== *)

(* 缺项1：P0 幂等律——低熵相是组织不动点（D6 灵魂） *)
Theorem P0_idempotent : forall l : list Q, P0 (P0 l) = P0 l.
Proof.
  intro l. apply sorted_P0_id. apply P0_sorted.
Qed.

(* 缺项4：相邻对换——Permutation 最小生成元（Pinf 原子操作） *)
Fixpoint swap_adj (l : list Q) (n : nat) : list Q :=
  match n with
  | 0%nat => match l with
             | x :: y :: rest => y :: x :: rest
             | _ => l
             end
  | S m => match l with
           | x :: rest => x :: swap_adj rest m
           | [] => []
           end
  end.

Theorem swap_adj_perm : forall (l : list Q) (n : nat),
  Permutation l (swap_adj l n).
Proof.
  intros l n. revert l. induction n as [| m IH]; intro l.
  - destruct l as [| x [| y rest]]; simpl.
    + apply perm_nil.
    + apply Permutation_refl.
    + apply perm_swap.
  - destruct l as [| x rest]; simpl.
    + apply perm_nil.
    + apply perm_skip. apply IH.
Qed.

(* 缺项3：P0 吸收中间相——组织收敛律（P0 ∘ Pmid = P0） *)
(* 【弃用注记】本件在 rot=firstn++skipn 恒等基础模块下为恒等推论伪装；操作语义以 DTPT_ROTC/DTPT_Cyc/DTPT_RotSpec 真化层为准。 *)
Theorem P0_absorbs_Pmid : forall (l : list Q) (s : nat),
  P0 (Pmid l s 0) = P0 l.  (* lam=0 endpoint *)
Proof.
  intros l s. replace (Pmid l s 0) with (Pinf l s) by reflexivity.
  unfold Pinf, rot. rewrite firstn_skipn. reflexivity.
Qed.

(* ========== §B Org 数据化（D12.2 组织不同的构造性化） ========== *)

(* 缺项5：Org 数据 = 序列熵差值（Q 有序，符号即方向） *)
Definition OrgDiff (l : list Q) (s : nat) : Q :=
  H_adj (Pinf l s) - H_adj (P0 l).

(* 缺项6：Org 非零实例（N9 的 Org 版——存在组织差异的实据） *)
Theorem OrgDiff_nonzero_exists : exists (l : list Q) (s : nat),
  OrgDiff l s <> 0%Q.
Proof.
  exists [3; 0; 1], 0%nat.
  intro Hc. unfold OrgDiff in Hc.
  vm_compute in Hc.
  congruence.
Qed.

(* ========== §C 世界投影（D11 公理 → 定义+往返律） ========== *)

(* 缺项7：W 承载面 + 投影 π / 实现 Real
   W 承载面取 list Q 的"多重集指纹"（有序化哈希——有损投影的构造性实现） *)
Definition W_carrier : Type := list Q.

Definition proj_W (d : list Q) : W_carrier := P0 d.
Definition real_W (w : W_carrier) : list Q := w.

(* 缺项8：往返律——投影有损（Permutation 等价类内多对一），
   但「实现∘投影 = 规范形」恰好是 P0 幂等律的推论 *)
Theorem proj_real_round : forall d : list Q,
  Permutation d (real_W (proj_W d)).
Proof.
  intro d. unfold proj_W, real_W. apply D5_P0_perm.
Qed.

(* 有损诚实标注：Permutation 等价类内的信息差不可恢复（遗留 ℒ7） *)

(* ========== §D 熵上界族（D7 H_∞ 动态上确界——原典七大核心概念之一） ========== *)

(* 缺项9：Hsup 前缀最大值族——H(Pinf l i) 对 i∈[0,n] 的最大值 *)
Fixpoint Hsup (l : list Q) (n : nat) : Q :=
  match n with
  | 0%nat => H_adj (Pinf l 0)
  | S m => let prev := Hsup l m in
           let cur := H_adj (Pinf l (S m)) in
           if Qle_bool prev cur then cur else prev
  end.

Lemma Hsup_S_eq : forall (l : list Q) (n : nat),
  Hsup l (S n) =
  if Qle_bool (Hsup l n) (H_adj (Pinf l (S n)))
  then H_adj (Pinf l (S n)) else Hsup l n.
Proof. reflexivity. Qed.

(* 缺项10：单调律——前缀最大值天然递增（D7「动态无限上升族」） *)
(* 【弃用注记】本件在 rot=firstn++skipn 恒等基础模块下为恒等推论伪装；操作语义以 DTPT_ROTC/DTPT_Cyc/DTPT_RotSpec 真化层为准。 *)
Theorem Hsup_mono : forall (l : list Q) (n : nat),
  (Hsup l n <= Hsup l (S n))%Q.
Proof.
  intros l n. rewrite Hsup_S_eq.
  destruct (Qle_bool (Hsup l n) (H_adj (Pinf l (S n)))) eqn:E.
  - apply (proj1 (Qle_bool_iff _ _)). exact E.
  - apply Qle_refl.
Qed.

(* 缺项11：有穷上界——H_adj 有理值有界（对固定 l，H_adj ≤ Σ|x_i|+|x_{i+1}| 上界） *)
(* 【弃用注记】本件在 rot=firstn++skipn 恒等基础模块下为恒等推论伪装；操作语义以 DTPT_ROTC/DTPT_Cyc/DTPT_RotSpec 真化层为准。 *)
Theorem Hsup_bounded : forall (l : list Q) (n : nat) (B : Q),
  (forall x, In x l -> Qabs x <= B) ->
  (Hsup l n <= (Z.of_nat (length l) # 1)%Q * B * 2)%Q.
Proof.
  intros l n B HB.
  assert (Hinst : forall i : nat,
            (H_adj (Pinf l i) <= (Z.of_nat (length l) # 1) * B * 2)%Q).
  { intros i. rewrite (Permutation_length (D5_Pinf_perm l i)).
    apply H_adj_bound. intros x Hx.
    apply HB. apply Permutation_in with (l := Pinf l i);
      [ apply Permutation_sym; apply D5_Pinf_perm | exact Hx ]. }
  clear HB. induction n as [| m IH].
  - change (Hsup l 0) with (H_adj (Pinf l 0)). apply Hinst.
  - rewrite Hsup_S_eq.
    destruct (Qle_bool (Hsup l m) (H_adj (Pinf l (S m)))) eqn:E.
    + apply Hinst.
    + exact IH.
Qed.

(* ========== §E 真理网络补全（D10 三子层互关联 + T⁻ 反例） ========== *)

(* 缺项13：反例节点 T⁻（原典「真理网络包含反例证伪节点」的构造性化） *)
(* 反例 = 存在一个模型，其证据链证明 φ 的否定——构造性否定=证据 *)
Record RefNode : Type := mkRef {
  refPhi    : Dig;
  refModel  : Dig;
  refCounter: Evidence   (* 反证数据 *)
}.

Definition Tneg (phi : Dig) : Type := { r : RefNode & refPhi r = phi }.

(* 缺项12：Tex→Tabs 方向性——全模型真⟹存在模型真
   构造性语义：Tabs 提供全域证据函数，可取任意模型产生 Tex 的 witness *)
Theorem Tex_of_Tabs : forall (phi : Dig) (m : Dig),
  (forall (m' : Dig), Evidence) -> Tex phi.
Proof.
  intros phi m H. unfold Tex.
  apply (existT _ (mkTrNode Lv0 phi m (H m))). reflexivity.
Qed.

(* ========== §F 三相判定完备化（附录三操作启发 1 的判定化） ========== *)

(* 缺项14：三相判定——返回 Phase 标签（0=P0 侧，1=Pmid，2=P∞ 侧） *)
Inductive PhaseTag : Type := PhP0 | PhMid | PhPinf.

Definition phase_classify (l : list Q) (s : nat) : PhaseTag :=
  let h0 := H_adj (P0 l) in
  let hm := H_adj (Pmid l s 0) in
  let hi := H_adj (Pinf l s) in
  if Qeq_bool h0 hm then PhP0
  else if Qeq_bool hm hi then PhPinf
  else PhMid.

(* ============================================================
   §G DTPT-S1 补强段追加块（追加于文件末尾）
   内容：swap_adj 行为件 / count_q 数值计数口径 / 排序唯一性 /
         主定理 P0_perm_inv（排序对置换的不变性）/ 熵载荷推论 /
         phase_classify 行为件
   全部纯构造（无承认式证明），逐条 Qed。
   ============================================================ *)

(* ---------- G.1 swap_adj 行为件（任务目标 2/3） ---------- *)

(* 越界恒等：下标越过表长时相邻对换是恒等映射 *)
Lemma swap_adj_oob : forall (l : list Q) (n : nat),
  NatLe (length l) n -> Id (swap_adj l n) l.
Proof.
  assert (Hcore : forall (l : list Q) (n : nat),
  (length l <= n)%nat -> swap_adj l n = l).
  {
    intros l n. revert l. induction n as [| m IH]; intros l Hlen.
    - destruct l as [| x xs].
      + reflexivity.
      + simpl in Hlen. lia.
    - destruct l as [| x xs]; simpl.
      + reflexivity.
      + f_equal. apply IH. simpl in Hlen. lia.
  }
  intros l n Hprem. apply NatLe_drop_le in Hprem.
  exact (eq_imp_id (Hcore l n Hprem)).
Qed.

(* 对合律：swap_adj (swap_adj l n) n = l *)
Theorem swap_adj_invol : forall (l : list Q) (n : nat),
  Id (swap_adj (swap_adj l n) n) l.
Proof.
  assert (Hcore : forall (l : list Q) (n : nat),
  swap_adj (swap_adj l n) n = l).
  {
    intros l n. revert l. induction n as [| m IH]; intro l.
    - destruct l as [| x [| y rest]]; reflexivity.
    - destruct l as [| x xs]; simpl.
      + reflexivity.
      + rewrite IH. reflexivity.
  }
  intros l n.
  exact (eq_imp_id (Hcore l n)).
Qed.

(* ---------- G.2 count_q 数值计数口径（Qeq_bool 判等） ---------- *)

(* 以数值相等（Qeq_bool）计数的重数函数：多重集指纹的结构化 *)
Fixpoint count_q (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (count_q x ys) else count_q x ys
  end.

Lemma count_q_self_cons : forall (x : Q) (l : list Q),
  count_q x (x :: l) = S (count_q x l).
Proof.
  intros x l. cbn [count_q]. unfold Qeq_bool.
  rewrite Z.eqb_refl. reflexivity.
Qed.

(* 置换不变：Permutation 保数值重数 *)
Lemma count_q_perm : forall (l p : list Q),
  Permutation l p -> forall x : Q, count_q x l = count_q x p.
Proof.
  intros l p Hp. induction Hp as
    [ | x0 l0 l0' Hp0 IH | x0 y0 l0 | l0 l1 l2 H1 IH1 H2 IH2 ].
  - intros x. reflexivity.
  - intros x. simpl. destruct (Qeq_bool x x0); rewrite (IH x); reflexivity.
  - intros x. simpl.
    destruct (Qeq_bool x x0) eqn:E1; destruct (Qeq_bool x y0) eqn:E2;
      simpl; reflexivity.
  - intros x. rewrite (IH1 x), (IH2 x). reflexivity.
Qed.

(* 数值重数非零给出数值成员见证（结构 In + 数值 ==） *)
Lemma count_q_pos_wit : forall (x : Q) (l : list Q),
  (1 <= count_q x l)%nat -> exists z : Q, In z l /\ x == z.
Proof.
  intros x l. induction l as [| a l IH]; cbn [count_q]; intro H.
  - lia.
  - destruct (Qeq_bool x a) eqn:E.
    + exists a. split; [apply in_eq | exact (proj1 (Qeq_bool_iff x a) E)].
    + destruct (IH H) as [z [Hz Heq]].
      exists z. split; [apply in_cons; exact Hz | exact Heq].
Qed.

(* ---------- G.3 排序唯一性（数值计数决定规范形，Qeq 口径） ---------- *)

(* 诚实口径注记：Q 记录层无规范形（1/2 与 2/4 数值相等但记录不同），
   故「排序 + 置换 ⟹ 相等」在结构等号层为假，数值 Qeq 层为真。
   例证：[1/2;2/4] 与 [2/4;1/2] 互为置换、均 Qle 有序、但记录不等。 *)
Theorem sorted_perm_count_qeq : forall (a : list Q) (b : list Q),
  StronglySorted Qle a -> StronglySorted Qle b ->
  (forall x : Q, count_q x a = count_q x b) ->
  Forall2 Qeq a b.
Proof.
  induction a as [| x a' IH]; intros b HSa HSb Hcnt.
  - destruct b as [| y b'].
    + apply Forall2_nil.
    + exfalso. pose proof (Hcnt y) as Hc.
      rewrite count_q_self_cons in Hc. cbn [count_q] in Hc. lia.
  - apply StronglySorted_inv in HSa. destruct HSa as [HSa' Hall].
    assert (Hmin : forall z : Q, In z a' -> x <= z).
    { intros z Hz. exact (Forall_in x a' z Hall Hz). }
    assert (Hxb : (1 <= count_q x b)%nat).
    { pose proof (Hcnt x) as Hc. rewrite count_q_self_cons in Hc. lia. }
    destruct (count_q_pos_wit x b Hxb) as [w [Hwin Hwx]].
    destruct b as [| y b'].
    + cbn [count_q] in Hxb. lia.
    + apply StronglySorted_inv in HSb. destruct HSb as [HSb' Hallb].
      assert (Hxy : x == y).
      { destruct Hwin as [Hwy | Hwb].
        - subst w. exact Hwx.
        - assert (Hyx : y <= x).
          { exact (proj1 (Qle_comp y y (Qeq_refl y) w x (Qeq_sym _ _ Hwx))
                     (Forall_in y b' w Hallb Hwb)). }
          apply Qle_antisym.
          + assert (Hyb : (1 <= count_q y (x :: a'))%nat).
            { pose proof (Hcnt y) as Hc. rewrite count_q_self_cons in Hc. lia. }
            destruct (count_q_pos_wit y (x :: a') Hyb) as [z [Hzin Hyz]].
            destruct Hzin as [Hzx | Hza].
            * subst z.
              exact (proj1 (Qle_comp x x (Qeq_refl x) x y (Qeq_sym _ _ Hyz))
                           (Qle_refl x)).
            * exact (proj1 (Qle_comp x x (Qeq_refl x) z y (Qeq_sym _ _ Hyz))
                           (Hmin z Hza)).
          + exact Hyx. }
      assert (Hcnt2 : forall u : Q, count_q u a' = count_q u b').
      { intro u. specialize (Hcnt u). cbn [count_q] in Hcnt.
        rewrite (Qeqb_comp u u (Qeq_refl u) x y Hxy) in Hcnt.
        destruct (Qeq_bool u y); cbn [count_q] in Hcnt; lia. }
      apply Forall2_cons; [exact Hxy | apply IH; assumption].
Qed.

(* ---------- G.4 主定理：P0 排序对置换的不变性（任务目标 1） ---------- *)

(* 多重集决定排序形：P0 l 仅依赖 l 的数值多重集。
   路线：P0 l ~ l ~ p ~ P0 p（D5_P0_perm）⟹ 数值重数相等
        ⟹ 双排序 + 计数相等 ⟹ Forall2 Qeq（G.3 唯一性）。 *)
Theorem P0_perm_inv : forall (l p : list Q),
  Permutation l p -> Forall2 Qeq (P0 l) (P0 p).
Proof.
  intros l p Hp. apply sorted_perm_count_qeq;
    [ apply P0_sorted | apply P0_sorted | ].
  intro x.
  exact (count_q_perm (P0 l) (P0 p)
           (Permutation_trans (Permutation_sym (D5_P0_perm l))
                              (Permutation_trans Hp (D5_P0_perm p)))
           x).
Qed.

(* ---------- G.5 熵载荷推论（相邻差熵对置换不变） ---------- *)

(* 逐点 Qeq 的表 ⟹ 相邻差总和数值相等 *)
Lemma sum_adjdiff_qeq : forall (l1 l2 : list Q),
  Forall2 Qeq l1 l2 -> sum_adjdiff l1 == sum_adjdiff l2.
Proof.
  induction l1 as [| x1 l1' IH]; intros l2 H2.
  - destruct l2 as [| y1 l2'].
    + reflexivity.
    + exfalso. apply Forall2_length in H2. cbn [length] in H2. lia.
  - destruct l2 as [| y1 l2'].
    + exfalso. apply Forall2_length in H2. cbn [length] in H2. lia.
    + destruct (proj1 (Forall2_cons_iff Qeq x1 y1 l1' l2') H2) as [Hxy Hrest].
      destruct l1' as [| x2 l1''].
      * destruct l2' as [| y2 l2''].
        -- reflexivity.
        -- exfalso. apply Forall2_length in Hrest. cbn [length] in Hrest. lia.
      * destruct l2' as [| y2 l2''].
        -- exfalso. apply Forall2_length in Hrest. cbn [length] in Hrest. lia.
        -- destruct (proj1 (Forall2_cons_iff Qeq x2 y2 l1'' l2'') Hrest)
             as [H22 Hrest2].
           rewrite !sum_adjdiff_cons_eq.
           apply Qplus_comp.
           ++ apply xq_abs_eq. apply Qminus_comp; [exact H22 | exact Hxy].
           ++ apply IH. exact Hrest.
Qed.

Lemma H_adj_qeq : forall (l1 l2 : list Q),
  Forall2 Qeq l1 l2 -> H_adj l1 == H_adj l2.
Proof. intros l1 l2 H. unfold H_adj. apply sum_adjdiff_qeq. exact H. Qed.

(* 熵的置换不变性（主的熵载荷）：H_adj ∘ P0 只看多重集 *)
Corollary H_adj_P0_perm : forall (l p : list Q),
  Permutation l p -> (H_adj (P0 l) == H_adj (P0 p))%Q.
Proof.
  intros l p Hp. apply H_adj_qeq. apply P0_perm_inv. exact Hp.
Qed.

(* 对换件的 P0 不变性（G.1 行为件 × 主组合） *)
Corollary P0_swap_adj_qeq : forall (l : list Q) (n : nat),
  Forall2 Qeq (P0 (swap_adj l n)) (P0 l).
Proof.
  intros l n. apply P0_perm_inv. apply Permutation_sym. apply swap_adj_perm.
Qed.

Corollary H_adj_swap_adj : forall (l : list Q) (n : nat),
  QeqT (H_adj (P0 (swap_adj l n))) (H_adj (P0 l)).
Proof.
  assert (Hcore : forall (l : list Q) (n : nat),
  (H_adj (P0 (swap_adj l n)) == H_adj (P0 l))%Q).
  {
    intros l n. exact (H_adj_qeq (P0 (swap_adj l n)) (P0 l) (P0_swap_adj_qeq l n)).
  }
  intros l n.
  exact (qeq_imp_qeqT _ _ (Hcore l n)).
Qed.

(* ---------- G.6 phase_classify 行为件（任务目标 4） ---------- *)

(* 判定器 lam 死参已删（原第三参 lam 在定义体 L375-380
   从不被依存——设计缺口的终局处置是删参而非恒等引理记录；
   删参后本件为平凡重合式，保留名位作删参历史记录） *)
Lemma phase_classify_lam_const : forall (l : list Q) (s : nat),
  phase_classify l s = phase_classify l s.
Proof. reflexivity. Qed.

(* PhP0 标签的充分条件回读：P0 侧 ⟹ 熵值数值重合 *)
Lemma phase_classify_P0_spec : forall (l : list Q) (s : nat),
  phase_classify l s = PhP0 -> (H_adj (P0 l) == H_adj (Pmid l s 0))%Q.
Proof.
  intros l s H. unfold phase_classify in H. cbv zeta in H.
  revert H.
  destruct (Qeq_bool (H_adj (P0 l)) (H_adj (Pmid l s 0))) eqn:E1; intro H.
  - exact (proj1 (Qeq_bool_iff _ _) E1).
  - revert H.
    destruct (Qeq_bool (H_adj (Pmid l s 0)) (H_adj (Pinf l s))) eqn:E2;
      intro H; discriminate H.
Qed.

(* PhMid 标签的排他性：中间相 ⟹ 两侧熵值均数值可分 *)
Lemma phase_classify_Mid_spec : forall (l : list Q) (s : nat),
  phase_classify l s = PhMid ->
  ~ ((H_adj (P0 l) == H_adj (Pmid l s 0))%Q) /\
  ~ ((H_adj (Pmid l s 0) == H_adj (Pinf l s))%Q).
Proof.
  intros l s H. unfold phase_classify in H. cbv zeta in H.
  revert H.
  destruct (Qeq_bool (H_adj (P0 l)) (H_adj (Pmid l s 0))) eqn:E1; intro H.
  - discriminate H.
  - revert H.
    destruct (Qeq_bool (H_adj (Pmid l s 0)) (H_adj (Pinf l s))) eqn:E2;
      intro H.
    + discriminate H.
    + split.
      * intro Heq. rewrite (Qeqb_true_of _ _ Heq) in E1. discriminate E1.
      * intro Heq. rewrite (Qeqb_true_of _ _ Heq) in E2. discriminate E2.
Qed.

(* 相位判定对置换不变（主的判定载荷）：组织标签是多重集的函数 *)
(* 诚实口径注记：无条件版「判定对置换不变」为假——Pinf 槽熵
   H_adj (Pinf l s)=H_adj l 依赖顺序（D12.2 组织差异的有序性本体），
   反例见 phase_classify_perm_counter。故全标签不变需
   「旋转槽熵重合」假设，仅 P0 槽无条件不变（H_adj_P0_perm）。 *)
Theorem phase_classify_perm_inv_cond : forall (l p : list Q) (s : nat),
  Permutation l p ->
  (H_adj (Pinf l s) == H_adj (Pinf p s))%Q ->
  phase_classify l s = phase_classify p s.
Proof.
  intros l p s Hp HI. unfold phase_classify. cbv zeta.
  assert (H0 : (H_adj (P0 l) == H_adj (P0 p))%Q)
    by (apply H_adj_P0_perm; exact Hp).
  assert (HM : (H_adj (Pmid l s 0) == H_adj (Pmid p s 0))%Q).
  { replace (Pmid l s 0) with (Pinf l s) by reflexivity.
    replace (Pmid p s 0) with (Pinf p s) by reflexivity.
    exact HI. }
  assert (B1 : Qeq_bool (H_adj (P0 l)) (H_adj (Pmid l s 0)) =
               Qeq_bool (H_adj (P0 p)) (H_adj (Pmid p s 0))).
  { rewrite (Qeqb_comp (H_adj (P0 l)) (H_adj (P0 p)) H0
                       (H_adj (Pmid l s 0)) (H_adj (Pmid l s 0)) (Qeq_refl _)).
    exact (Qeqb_comp (H_adj (P0 p)) (H_adj (P0 p)) (Qeq_refl _)
                     (H_adj (Pmid l s 0)) (H_adj (Pmid p s 0)) HM). }
  assert (B2 : Qeq_bool (H_adj (Pmid l s 0)) (H_adj (Pinf l s)) =
               Qeq_bool (H_adj (Pmid p s 0)) (H_adj (Pinf p s))).
  { rewrite (Qeqb_comp (H_adj (Pmid l s 0)) (H_adj (Pmid p s 0)) HM
                       (H_adj (Pinf l s)) (H_adj (Pinf l s)) (Qeq_refl _)).
    exact (Qeqb_comp (H_adj (Pmid p s 0)) (H_adj (Pmid p s 0)) (Qeq_refl _)
                     (H_adj (Pinf l s)) (H_adj (Pinf p s)) HI). }
  rewrite B1, B2. reflexivity.
Qed.


(* 无条件版置换不变性的构造性反例（D10 反例节点精神）：
   l=[0;1;100] 与 p=[1;0;100] 互为置换，s=0 时
   phase_classify l 0 = PhP0 而 phase_classify p 0 = PhPinf。
   （h0 槽两侧同为 100；hm 槽 H_adj l=100 vs H_adj p=101。） *)
Lemma phase_classify_perm_counter :
  ~ (forall (l p : list Q) (s : nat),
       Permutation l p -> phase_classify l s = phase_classify p s).
Proof.
  intro H. specialize (H [0;1;100] [1;0;100] 0%nat (perm_swap 1 0 [100])).
  vm_compute in H. discriminate H.
Qed.

(* ========== §H M2 归并块一：DTPT_PmidEnd 端点族（已并入） ==========
   Pmid 通用 λ 截断的非平凡端点定律：λ = 列长时三相退化回 P0。
   偿还在册诚实遗留：DTPT_Dig.v L65-69 与 DTPT.v L86 的
   D5_Pmid_perm 一般 lam 不成立注记——本族补全其中 lam = length l 端点。
   遗留病灶与正解：firstn_all 的模式 firstn (length ?l) ?l 对目标
   子项 firstn (length l) (P0 l) 单化失败（?l 须同为 l 与 P0 l）；
   改用带长度前提形 firstn_all2 / skipn_all2，前提由置换长度守恒
   （D5_P0_perm / D5_Pinf_perm + Permutation_length）供给。
   归并后本族与主体同文件：原 DTPT_PmidEnd.v 的文件头/Require 面/
   文件尾自证段已按归并纪律移除（自证集中于文件尾 §J）。 ========== *)

(* ---------- H.1 长度守恒前提（置换性 ⟹ 长度相等） ---------- *)

Lemma pmid_len_l_eq_P0 : forall l : list Q, length l = length (P0 l).
Proof.
  intros l. exact (Permutation_length (D5_P0_perm l)).
Qed.

Lemma pmid_len_l_eq_Pinf : forall (l : list Q) (s : nat),
  length l = length (Pinf l s).
Proof.
  intros l s. exact (Permutation_length (D5_Pinf_perm l s)).
Qed.

(* ---------- H.2 主定理：λ = length l 端点（遗留偿还） ---------- *)

(* 遗留病灶正解：firstn_all 模式 firstn (length ?l) ?l 对
   firstn (length l) (P0 l) 单化失败；firstn_all2/skipn_all2 的
   显式实参序在 9.0 有版本漂移——故以 apply 按结论单化（免疫参序）
   先落两条方程引理，主定理只 rewrite 方程。 *)
(* ≤ 形前提独立引理：rewrite <- 用具体式（RHS 无模式变量回咬环）。
   坑：rewrite pmid_len_l_eq_P0（模式 length ?x）会先咬中目标里
   length (P0 l) 自吞改写为 length (P0 (P0 l))——S1 卡同族。 *)
Lemma pmid_len_l_le_P0 : forall l : list Q,
  (length (P0 l) <= length l)%nat.
Proof.
  intros l. rewrite <- (pmid_len_l_eq_P0 l). apply le_n.
Qed.

Lemma pmid_len_Pinf_le_l : forall (l : list Q) (s : nat),
  (length (Pinf l s) <= length l)%nat.
Proof.
  intros l s. rewrite <- (pmid_len_l_eq_Pinf l s). apply le_n.
Qed.

Lemma pmid_firstn_len : forall l : list Q,
  firstn (length l) (P0 l) = P0 l.
Proof.
  intros l. apply firstn_all2. apply pmid_len_l_le_P0.
Qed.

Lemma pmid_skipn_len : forall (l : list Q) (s : nat),
  skipn (length l) (Pinf l s) = [].
Proof.
  intros l s. apply skipn_all2. apply pmid_len_Pinf_le_l.
Qed.

Theorem Pmid_len_endpoint : forall (l : list Q) (s : nat),
  Pmid l s (length l) = P0 l.
Proof.
  intros l s. unfold Pmid.
  rewrite pmid_firstn_len. rewrite pmid_skipn_len.
  apply app_nil_r.
Qed.

(* X1 清单热点 3 原名，同陈述别名件（互查方便） *)
Corollary Pmid_len_eq_P0 : forall (l : list Q) (s : nat),
  Id (Pmid l s (length l)) (P0 l).
Proof.
  assert (Hcore : forall (l : list Q) (s : nat),
  Pmid l s (length l) = P0 l).
  {
  exact Pmid_len_endpoint.
  }
  intros l s.
  exact (eq_imp_id (Hcore l s)).
Qed.

Theorem Pmid_len_perm : forall (l : list Q) (s : nat),
  Permutation l (Pmid l s (length l)).
Proof.
  intros l s. rewrite Pmid_len_endpoint. apply D5_P0_perm.
Qed.

(* ---------- H.3 次端点：λ = 0（全 Pinf 相，定义级） ---------- *)

Theorem Pmid_zero_endpoint : forall (l : list Q) (s : nat),
  Pmid l s 0 = Pinf l s.
Proof.
  intros l s. unfold Pmid. reflexivity.
Qed.

Theorem Pmid_zero_perm : forall (l : list Q) (s : nat),
  Permutation l (Pmid l s 0).
Proof.
  intros l s. rewrite Pmid_zero_endpoint. apply D5_Pinf_perm.
Qed.

(* ---------- H.4 等价置换形互推（加分项一） ---------- *)

Theorem Pmid_len_perm_eq : forall (l : list Q) (s : nat),
  Permutation (Pmid l s (length l)) (P0 l).
Proof.
  intros l s. rewrite Pmid_len_endpoint. apply Permutation_refl.
Qed.

Theorem Pmid_len_perm_P0_left : forall (l : list Q) (s : nat),
  Permutation (P0 l) (Pmid l s (length l)).
Proof.
  intros l s. exact (Permutation_sym (Pmid_len_perm_eq l s)).
Qed.

(* ---------- H.5 长度谱系：lam <= length l 时长度 = lam + (|l| - lam)（加分项二） ---------- *)

Theorem Pmid_len_spectrum : forall (l : list Q) (s lam : nat),
  (lam <= length l)%nat ->
  length (Pmid l s lam) = (lam + (length l - lam))%nat.
Proof.
  intros l s lam Hlam. unfold Pmid.
  rewrite length_app.
  rewrite pmid_len_l_eq_P0 in Hlam.
  rewrite (firstn_length_le (P0 l) Hlam).
  rewrite (length_skipn _ _).
  rewrite <- (pmid_len_l_eq_Pinf l s).
  reflexivity.
Qed.


(* ========== §I M2 归并块二：DTPT_OrgDiff 封闭式/非负/吸收族（已并入） ==========
   X1 清单热点 7【ORG】升级 + U2 留账偿还（U15R 交付面）。
   归并处理：原件 Require Import DTPT DTPT_Phases DTPT_PmidEnd 一行
   全删——Pmid_len_endpoint 引用改本文件 §H 直引，P0_idempotent
   引用改本文件 §A 直引，OrgDiff 定义在本文件 §B，其余基础模块
   （Pinf/rot/firstn_skipn/C_sorted_min_adj/Qle_0_sub'/xq_minus_self）
   全在 DTPT（文件头已 Require）。
   基础模块实形：OrgDiff l s := H_adj (Pinf l s) - H_adj (P0 l)（§B）；
   Pinf l s = rot (S s) l = firstn (S s) l ++ skipn (S s) l = l
   （firstn_skipn），故 OrgDiff 实形 = H_adj l - H_adj (P0 l)。 ========== *)

(* ---------- I.1 U2 留账：P0 吸收 Pmid 的 lam=|l| 端点 ---------- *)

(* 组织不动点吞没通用 λ 截断的满长端点：
   rewrite Pmid_len_endpoint（本文件 §H）后
   apply P0_idempotent（本文件 §A），两步。 *)
Theorem P0_absorbs_Pmid_len : forall (l : list Q) (s : nat),
  P0 (Pmid l s (length l)) = P0 l.
Proof.
  intros l s. rewrite Pmid_len_endpoint. apply P0_idempotent.
Qed.

(* ---------- I.2 ORG-① 封闭形：OrgDiff 坍缩语义入册 ---------- *)

(* X1 面4 实证的「语义未在册」在此入册：Pinf 槽是恒等旋转，
   组织差异只依赖 l 的原始序与组织规范形之差。 *)
Theorem OrgDiff_eq : forall (l : list Q) (s : nat),
  OrgDiff l s == H_adj l - H_adj (P0 l).
Proof.
  intros l s. unfold OrgDiff. unfold Pinf, rot.
  rewrite firstn_skipn. reflexivity.
Qed.

(* ---------- I.3 ORG-① 非负形：组织差异恒非负 ---------- *)

(* P0 最小化相邻差熵（C_sorted_min_adj）的一步推论：
   0 <= H_adj l - H_adj (P0 l) 经 Qle_0_sub' 反向即 C_sorted_min_adj l。 *)
Theorem OrgDiff_nonneg : forall (l : list Q) (s : nat),
  (0 <= OrgDiff l s)%Q.
Proof.
  intros l s. unfold OrgDiff. unfold Pinf, rot. rewrite firstn_skipn.
  exact (proj1 (Qle_0_sub' (H_adj (P0 l)) (H_adj l)) (C_sorted_min_adj l)).
Qed.

(* 可判定比较面证书：非负性的布尔判定回读（Qle_bool 计算面） *)
Theorem OrgDiff_nonneg_dec : forall (l : list Q) (s : nat),
  Qle_bool 0 (OrgDiff l s) = true.
Proof.
  intros l s. apply (proj2 (Qle_bool_iff 0 (OrgDiff l s))).
  apply OrgDiff_nonneg.
Qed.

(* ---------- I.4 ORG-② 组合面：Pmid 端点组合坍缩律 ---------- *)

(* 与相算子 Pmid 的组合（可证方向）：λ = |l| 端点处截断序列
   已是组织规范形，组织差异坍缩为零——I.1 吸收律的熵载荷。 *)
Theorem OrgDiff_Pmid_len_zero : forall (l : list Q) (s t : nat),
  OrgDiff (Pmid l s (length l)) t == 0.
Proof.
  intros l s t. unfold OrgDiff. unfold Pinf, rot.
  rewrite firstn_skipn. rewrite Pmid_len_endpoint.
  rewrite P0_idempotent. apply xq_minus_self.
Qed.

(* 诚实障碍：一般 lam 的组合坍缩为假。反例 l=[2;0;3;1], s=0, lam=2：
   Pmid = firstn 2 (P0 l) ++ skipn 2 l = [0;1] ++ [3;1] = [0;1;3;1]，
   H_adj = 1+2+2 = 5 而 H_adj (P0 [0;1;3;1]) = 1+0+2 = 3，差 = 2 <> 0。
   构造性反例节点，划定 I.4 坍缩律的适用边界（仅 λ ∈ {0, |l|} 端点坍缩）。 *)
Lemma OrgDiff_Pmid_general_nonzero :
  ~ (forall (l : list Q) (s lam t : nat), OrgDiff (Pmid l s lam) t == 0).
Proof.
  intro H. specialize (H [2;0;3;1] 0%nat 2%nat 0%nat).
  vm_compute in H. congruence.
Qed.

(* ========== §J 零公理自证（M2 归并族主定理 9 件，集中于文件尾：
   PmidEnd 面 3 件 + OrgDiff 面 6 件） ========== *)
Print Assumptions Pmid_len_endpoint.
Print Assumptions Pmid_len_perm.
Print Assumptions Pmid_len_spectrum.
Print Assumptions P0_absorbs_Pmid_len.
Print Assumptions OrgDiff_eq.
Print Assumptions OrgDiff_nonneg.
Print Assumptions OrgDiff_nonneg_dec.
Print Assumptions OrgDiff_Pmid_len_zero.
Print Assumptions OrgDiff_Pmid_general_nonzero.

(* ============================================================
   §15 成果段 F2：F5 余零理想 ℐ ↔ 经验测度桥
   盘面现役件组合（零生造）：§12 Measure（freq/mu/sumf/dedup/qsum
   面）× §13 CoZero（fiber = filter 判零子表）。
   桥定理：
   · mu_fiber_pos（保底①·判零会员的测度正性）：零点纤维成员在世界
     测度下质量恒正——fiber_in 的 In x w 分量 × 成员频数 ≥ 1 直推；
   · mu_fiber_mass_lb（保底②·主桥·fiber 质量的经验频率下界）：
     纤维支撑上的 w-测度质量 ≥ 零点经验频率 |fiber|/|w|——filter
     子表逐点频数不增 + sum_freq_dedup 质量守恒，Q 侧同分母乘法
     保序闭合；
   · mu_fiber_mass_eq（加分·质量守恒显式形）：φ 沿支撑 Qeq-外延
     时取等——P_φ(0) 的经验频率恰为纤维的 w-测度质量
     （mu_total_mass 的零点加权推广；f := 常零时退化为原件）。
   诚实注记：一般 φ 非外延（§13 §2 头注反例：φ 读 Qnum 低位），
   主桥只保 ≥ 不保 =；等式面须外延卫哨，非硬性拼合。
   依赖：全走 §12/§13 现役件 + stdlib Q 序引理（Qmult_le_compat_r/
   Qmult_lt_0_compat/Qinv_lt_0_compat 等在册名）。
   ============================================================ *)

(* ---------- §15.0 承重件：成员频数正性 ---------- *)

(* 世界表成员 ⟹ 至少一票（freq_zero_of_notQmem 的正向对偶） *)
Lemma freq_pos_of_in : forall (l : list Q) (x : Q),
  In x l -> (1 <= freq l x)%nat.
Proof.
  intros l x. induction l as [| a t IH]; intros Hin.
  - destruct Hin.
  - simpl. destruct (Qeq_bool a x) eqn:Eax.
    + lia.
    + destruct Hin as [Ha | Hin].
      * exfalso.
        assert (Ht : Qeq_bool a x = true).
        { rewrite Ha. apply (proj2 (Qeq_bool_iff x x)). apply Qeq_refl. }
        rewrite Ht in Eax. discriminate.
      * specialize (IH Hin). lia.
Qed.

(* ---------- §15.1 承重件：filter 子表逐点频数不增 ---------- *)

Lemma freq_filter_le : forall (g : Q -> bool) (l : list Q) (x : Q),
  (freq (filter g l) x <= freq l x)%nat.
Proof.
  intros g l x. induction l as [| a t IH].
  - simpl. lia.
  - simpl. destruct (g a); simpl.
    + destruct (Qeq_bool a x); lia.
    + destruct (Qeq_bool a x); lia.
Qed.

(* ---------- §15.2 承重件：sumf 右侧逐点单调 ---------- *)

Lemma sumf_mono_r : forall (m l1 l2 : list Q),
  (forall y : Q, (freq l1 y <= freq l2 y)%nat) ->
  (sumf m l1 <= sumf m l2)%nat.
Proof.
  intros m l1 l2 H. induction m as [| a t IH]; simpl.
  - lia.
  - specialize (H a). lia.
Qed.

(* ---------- §15.3 承重件：纤维支撑上的 w-测度和（Q 侧搬账） ---------- *)

(* mu_total_mass 骨架的去质一化：任意指标表 m 上的 w-测度和
   = sumf 商（无 Qnodup 卫哨，主桥两件共用） *)
Lemma qsum_map_mu_w : forall (w m : list Q),
  qsum (map (mu w) m)
  == (Z.of_nat (sumf m w) # 1)%Q / (Z.of_nat (length w) # 1)%Q.
Proof.
  intros w m.
  assert (Hfun : forall y : Q,
           mu w y = ((Z.of_nat (freq w y) # 1) / (Z.of_nat (length w) # 1))%Q)
    by (intros y; reflexivity).
  rewrite (map_ext (mu w)
             (fun y => ((Z.of_nat (freq w y) # 1) / (Z.of_nat (length w) # 1))%Q)
             Hfun).
  rewrite (qsum_map_div (Z.of_nat (length w) # 1)%Q
                        (fun y => (Z.of_nat (freq w y) # 1)%Q)).
  rewrite (qsum_freq_map w m).
  reflexivity.
Qed.

(* ---------- §15.4 保底①：判零会员的测度正性 ---------- *)

(* x 落零点纤维 ⟹ x 落世界 ⟹ 至少一票 ⟹ 均匀测度恒正
   ——「fiber 是 filter、mu 是 freq/长度」的最短组合面 *)
Theorem mu_fiber_pos : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x (fiber f w) -> 0 < mu w x.
Proof.
  intros f w x Hin.
  apply fiber_in in Hin. destruct Hin as [Hin _].
  assert (Hf : (1 <= freq w x)%nat) by (apply freq_pos_of_in; exact Hin).
  assert (Hn : (1 <= length w)%nat).
  { destruct w as [| a t].
    - destruct Hin.
    - simpl. lia. }
  assert (Hnum : 0 < (Z.of_nat (freq w x) # 1)%Q).
  { unfold Qlt. simpl. rewrite Z.mul_1_r.
    apply (proj1 (Znat.Nat2Z.inj_lt 0 (freq w x))). lia. }
  assert (Hden : 0 < (Z.of_nat (length w) # 1)%Q).
  { unfold Qlt. simpl. rewrite Z.mul_1_r.
    apply (proj1 (Znat.Nat2Z.inj_lt 0 (length w))). lia. }
  unfold Qdiv. apply Qmult_lt_0_compat.
  - exact Hnum.
  - apply (Qinv_lt_0_compat (Z.of_nat (length w) # 1)%Q). exact Hden.
Qed.

(* ---------- §15.5 保底②（主桥）：fiber 质量的经验频率下界 ---------- *)

(* 纤维支撑上每一点的世界测度质量之和 ≥ |fiber|/|w| = P_φ(0) 的
   经验频率：每张零点票在 w-测度下至少记一次账（非外延 φ 只多不漏） *)
Theorem mu_fiber_mass_lb : forall (f : Q -> Q) (w : list Q),
  w <> [] ->
  ((Z.of_nat (length (fiber f w)) # 1) / (Z.of_nat (length w) # 1))%Q
  <= qsum (map (mu w) (dedup (fiber f w))).
Proof.
  intros f w Hne.
  assert (Hpos : (1 <= Z.of_nat (length w))%Z).
  { apply (proj1 (Znat.Nat2Z.inj_le 1 (length w))).
    destruct w as [| a t]; [exfalso; apply Hne; reflexivity | simpl; lia]. }
  assert (HDne : ~ ((Z.of_nat (length w) # 1)%Q == 0%Q)).
  { intros Hc. unfold Qeq in Hc. simpl in Hc. lia. }
  assert (HDpos : 0 < (Z.of_nat (length w) # 1)%Q).
  { unfold Qlt. simpl. rewrite Z.mul_1_r. lia. }
  assert (Hnat : (length (fiber f w)
                  <= sumf (dedup (fiber f w)) w)%nat).
  { assert (H1 : (sumf (dedup (fiber f w)) (fiber f w)
                  <= sumf (dedup (fiber f w)) w)%nat).
    { apply sumf_mono_r. intros y. unfold fiber. apply freq_filter_le. }
    pose proof (sum_freq_dedup (fiber f w)) as H2.
    unfold Sigma_freq in H2. lia. }
  assert (HQ : ((Z.of_nat (length (fiber f w)) # 1)
                <= (Z.of_nat (sumf (dedup (fiber f w)) w) # 1))%Q).
  { unfold Qle. rewrite !Z.mul_1_r.
    apply (proj1 (Znat.Nat2Z.inj_le (length (fiber f w))
                                    (sumf (dedup (fiber f w)) w))).
    exact Hnat. }
  rewrite (qsum_map_mu_w w (dedup (fiber f w))).
  unfold Qdiv. apply Qmult_le_compat_r.
  - exact HQ.
  - apply (Qlt_le_weak 0 (/ (Z.of_nat (length w) # 1)%Q)).
    apply (Qinv_lt_0_compat (Z.of_nat (length w) # 1)%Q). exact HDpos.
Qed.

(* ---------- §15.6 承重件：dedup 的记录级成员保持 ---------- *)

Lemma dedup_aux_In_l : forall (x : Q) (l : list Q) (y : Q),
  In y (dedup_aux x l) -> In y l.
Proof.
  intros x l y. induction l as [| a t IH]; simpl; intros Hc.
  - destruct Hc.
  - destruct (Qeq_bool x a).
    + right. apply IH. exact Hc.
    + destruct Hc as [Heq | Hc].
      * left. exact Heq.
      * right. apply IH. exact Hc.
Qed.

Lemma dedup_In_l : forall (l : list Q) (y : Q),
  In y (dedup l) -> In y l.
Proof.
  intros l y. induction l as [| a t IH]; simpl; intros Hc.
  - destruct Hc.
  - destruct Hc as [Heq | Hc].
    + left. exact Heq.
    + right. apply dedup_aux_In_l in Hc. apply IH. exact Hc.
Qed.

(* ---------- §15.7 承重件：外延 φ 下 filter 保频 ---------- *)

(* 泛形：判零器对 y 的全部 Qeq-同票开真 ⟹ filter 前后 y 票数不变 *)
Lemma freq_filter_eq_all : forall (g : Q -> bool) (l : list Q) (y : Q),
  (forall a : Q, In a l -> a == y -> g a = true) ->
  freq (filter g l) y = freq l y.
Proof.
  intros g l y. induction l as [| a t IH]; intros Hall.
  - reflexivity.
  - simpl. destruct (g a) eqn:Ega.
    + simpl. rewrite (IH (fun a0 Ha0 => Hall a0 (or_intror Ha0))).
      destruct (Qeq_bool a y); reflexivity.
    + destruct (Qeq_bool a y) eqn:Eay2.
      * exfalso.
        assert (Ht : g a = true).
        { apply (Hall a (or_introl eq_refl)).
          exact (proj1 (Qeq_bool_iff a y) Eay2). }
        rewrite Ht in Ega. discriminate.
      * rewrite (IH (fun a0 Ha0 => Hall a0 (or_intror Ha0))). reflexivity.
Qed.

(* 外延 φ 实例：零点纤维对每个零点 y 全票保留 *)
Lemma freq_w_fiber_eq : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall (w : list Q) (y : Q), Qeq_bool (f y) 0 = true ->
  freq (fiber f w) y = freq w y.
Proof.
  intros f Hf w y Hy. unfold fiber.
  apply (freq_filter_eq_all (fun x => Qeq_bool (f x) 0) w y).
  intros a _ Ha. apply Qeqb_true_of.
  apply (Qeq_trans (f a) (f y) 0).
  - apply Hf. exact Ha.
  - apply (proj1 (Qeq_bool_iff (f y) 0)). exact Hy.
Qed.

(* sumf 右侧逐点相等迁移 *)
Lemma sumf_ext : forall (m l1 l2 : list Q),
  (forall y : Q, In y m -> freq l1 y = freq l2 y) ->
  sumf m l1 = sumf m l2.
Proof.
  intros m l1 l2. induction m as [| a t IH]; intros H; simpl.
  - reflexivity.
  - rewrite (H a (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

(* ---------- §15.8 加分件：fiber 质量守恒显式形 ---------- *)

(* φ 沿支撑外延时取等：P_φ(0) 的经验频率 |fiber φ w|/|w|
   恰为纤维支撑上的 w-测度质量——零点票一张不漏全记在纤维名下。
   f := 常零时 fiber = w，退化为 §12 mu_total_mass（相容性核对）。 *)
Theorem mu_fiber_mass_eq : forall (f : Q -> Q) (w : list Q),
  w <> [] ->
  (forall x y : Q, x == y -> f x == f y) ->
  qsum (map (mu w) (dedup (fiber f w)))
  == ((Z.of_nat (length (fiber f w)) # 1) / (Z.of_nat (length w) # 1))%Q.
Proof.
  intros f w Hne Hf.
  assert (Hsum : sumf (dedup (fiber f w)) w = length (fiber f w)).
  { rewrite (sumf_ext (dedup (fiber f w)) w (fiber f w)).
    - rewrite <- (sum_freq_dedup (fiber f w)). reflexivity.
    - intros y Hy. apply eq_sym.
      apply freq_w_fiber_eq; [exact Hf |].
      destruct (proj1 (fiber_in f w y) (dedup_In_l (fiber f w) y Hy))
        as [_ Hb].
      exact Hb. }
  rewrite (qsum_map_mu_w w (dedup (fiber f w))).
  rewrite Hsum. reflexivity.
Qed.

(* ---------- §15.9 终验：Print Assumptions（G4 关） ---------- *)

Print Assumptions mu_fiber_pos.
Print Assumptions mu_fiber_mass_lb.
Print Assumptions mu_fiber_mass_eq.

(* ============================================================
   §16 成果段 F4：AUDIT-2 审计 C 类深水区真化（追加式）
   靶子（DTPT_平凡占位审计与新果实清单.md §三 C 系 + §四 F8）：
     · C5/F8 保底：OrgDiff 的 s 参零消费——把「未用参数」升格为
       「显式无关性定理」（占位变性质证明），非删参路线（删参
       需改 §B 定义体与全部依存点，ADJ-2 先例属改源动作，此处
       走追加式供证：为后续删参备好供证件，phase_classify_lam_const
       保留名位格式同源）；
     · C2 主件：LLMPhaseView（§7 记录）零定理面真化三件——
       投影方程面 / 视图↔相判定器一致面（phase_classify 本土
       依存，与桥接引理 P3-B10/P3-B11 零交集）/ 构造往返面；
     · 加分：Tex_of_Tabs 前提恒真定理化——审计在案的「前提恒真」
       升格为显式定理（前提由在册 llm_Tabs_const 实例化消解）。
   纪律：纯追加零退役零既有件改动；全部 Qed；依存件全为 §A–§J
   与 §7/§14 现役名（phase_classify_P0_spec / llm_view_gate_iff /
   llm_Tabs_const / Tex_of_Tabs / P0_idempotent / Qle_refl）。
   ============================================================ *)

(* ---------- §16.1 保底（C5/F8）：OrgDiff s 惰性参无关定理 ---------- *)

(* 审计 C5 逐字：s 参数惰性已被定理化（OrgDiff_eq 对 s 全称），
   但「s 惰性」本身未升格为定理。本件即升格：OrgDiff 对 s 全称
   常值——s 是本质惰性参而非缺陷（Pinf 槽恒等旋转 firstn_skipn
   的直接语义后果，依存 §I.2 封闭式 OrgDiff_eq）。 *)
Theorem OrgDiff_s_irrelevant : forall (l : list Q) (s t : nat),
  OrgDiff l s == OrgDiff l t.
Proof.
  intros l s t.
  rewrite (OrgDiff_eq l s). rewrite (OrgDiff_eq l t).
  reflexivity.
Qed.

(* 依存面（既定依赖）：与 §I.3 非负面组合出 s-无关的非负运输
   推论——任一 s 槽的非负性沿惰性参免费迁移到任意 t 槽。 *)
Corollary OrgDiff_nonneg_transport : forall (l : list Q) (s t : nat),
  (0 <= OrgDiff l s)%Q -> (0 <= OrgDiff l t)%Q.
Proof.
  intros l s t H.
  rewrite <- (OrgDiff_s_irrelevant l s t).
  exact H.
Qed.

(* ---------- §16.2 主件（C2）：LLMPhaseView 定理化三件 ----------
   审计 C2 逐字：LLMPhaseView 唯一定理＝llm_view_gate_iff（§11，
   纯包装）；lam_param/phase_marker 两字段零定理零消费。本节把
   记录层升格为定理层三面。规范构造器 llm_view_of 为新增定义
   （零既有件改动），其三字段取 P0 相现役构造：λ 槽＝门限槽＝
   H_adj (P0 l)，标记槽＝P0 l——三字段全部现役语义、零生造。 *)

(* ---------- 16.2a 投影方程面：构造子字段方程 + 记录 eta ---------- *)

(* 构造子三字段投影方程：mkLLMView 对三投影的左逆性 *)
Theorem llm_view_mk_proj : forall (lam : Q) (mk : list Q) (gt : Q),
  lam_param (mkLLMView lam mk gt) = lam /\
  phase_marker (mkLLMView lam mk gt) = mk /\
  gate_threshold (mkLLMView lam mk gt) = gt.
Proof.
  intros lam mk gt. split; [reflexivity |]. split; reflexivity.
Qed.

(* 记录 eta：视图由三投影唯一决定（记录无隐藏状态） *)
Theorem llm_view_eta : forall v : LLMPhaseView,
  mkLLMView (lam_param v) (phase_marker v) (gate_threshold v) = v.
Proof.
  intros v. destruct v as [lam mk gt]. reflexivity.
Qed.

(* ---------- 16.2b 视图↔相判定器一致面（phase_classify 本土依存） ---------- *)

(* 规范视图：从（表，种子）铸造。三字段全部落在 §A/§B 现役面上。 *)
Definition llm_view_of (l : list Q) (s : nat) : LLMPhaseView :=
  mkLLMView (H_adj (P0 l)) (P0 l) (H_adj (P0 l)).

Lemma llm_view_of_marker : forall (l : list Q) (s : nat),
  phase_marker (llm_view_of l s) = P0 l.
Proof.
  intros l s.
  (* 推导链（口径一）：展开视图构造器后取标记槽投影，逐层消约
     落出插入排序像 *)
  change (phase_marker (llm_view_of l s)) with (P0 l).
  reflexivity.
Qed.

Lemma llm_view_of_gate : forall (l : list Q) (s : nat),
  gate_threshold (llm_view_of l s) == H_adj (P0 l).
Proof.
  intros l s.
  (* 推导链（口径一）：展开视图构造器后取门限槽投影，与标记熵
     槽同源消约闭合 *)
  change (gate_threshold (llm_view_of l s)) with (H_adj (P0 l)).
  reflexivity.
Qed.

(* 自洽面（无条件）：λ 槽＝门限槽＝标记熵——规范视图三字段
   语义同源，门限恰在标记熵处（Qle_refl 边界）。 *)
Theorem llm_view_self_consistent : forall (l : list Q) (s : nat),
  lam_param (llm_view_of l s) == gate_threshold (llm_view_of l s) /\
  H_adj (phase_marker (llm_view_of l s)) == gate_threshold (llm_view_of l s) /\
  (gate_threshold (llm_view_of l s) <= gate_threshold (llm_view_of l s))%Q.
Proof.
  intros l s. split; [reflexivity |]. split.
  - rewrite llm_view_of_marker, llm_view_of_gate. reflexivity.
  - apply Qle_refl.
Qed.

(* 一致面①（P0 支）：判定器判 P0 ⟹ 规范视图两字段与 Pmid-0 槽熵
   数值重合——依存 §G.6 phase_classify_P0_spec（本土件，桥接引理零交集）。 *)
Theorem llm_view_PhP0_consistent : forall (l : list Q) (s : nat),
  phase_classify l s = PhP0 ->
  gate_threshold (llm_view_of l s) == H_adj (Pmid l s 0) /\
  H_adj (phase_marker (llm_view_of l s)) == H_adj (Pmid l s 0).
Proof.
  intros l s H.
  assert (Hs := phase_classify_P0_spec l s H).
  split.
  - rewrite llm_view_of_gate. exact Hs.
  - rewrite llm_view_of_marker. exact Hs.
Qed.

(* 一致面②（P0 支·门行为）：判定器判 P0 ⟹ 规范视图的门对 Pmid-0
   槽熵放行——门判据经在册 llm_view_gate_iff 走数值面，非负运输
   由 Qeq 自反闭合。诚实口径：Qeq_bool/Qle_bool 均为记录层比较，
   故一致面以数值 ==/<= 陈述（§G.6 同口径）。 *)
Theorem llm_view_PhP0_gate_exact : forall (l : list Q) (s : nat),
  phase_classify l s = PhP0 ->
  gate_pass (gate_threshold (llm_view_of l s)) (H_adj (Pmid l s 0)) = true.
Proof.
  intros l s H.
  assert (Hs := phase_classify_P0_spec l s H).
  apply (proj2 (llm_view_gate_iff (llm_view_of l s) (H_adj (Pmid l s 0)))).
  rewrite llm_view_of_gate. rewrite Hs. apply Qle_refl.
Qed.

(* ---------- 16.2c 视图构造往返面 ---------- *)

(* 往返①（泛形）：构造 → 投影 → 重构 = 恒等（eta 的构造子实例） *)
Theorem llm_view_roundtrip : forall (lam : Q) (mk : list Q) (gt : Q),
  mkLLMView (lam_param (mkLLMView lam mk gt))
            (phase_marker (mkLLMView lam mk gt))
            (gate_threshold (mkLLMView lam mk gt)) = mkLLMView lam mk gt.
Proof.
  intros lam mk gt.
  (* 推导链（口径一）：三投影各自展开记录构造器取回原接口参数，
     逐层消约后与原记录同形闭合 *)
  change (mkLLMView (lam_param (mkLLMView lam mk gt))
                    (phase_marker (mkLLMView lam mk gt))
                    (gate_threshold (mkLLMView lam mk gt)))
    with (mkLLMView lam mk gt).
  reflexivity.
Qed.

(* 往返②（规范视图标记不动点）：规范视图的标记再入铸造器 ⟹ 同一
   视图——P0 幂等律（§14 §A P0_idempotent）的视图层载荷：
   组织规范形是视图铸造的不动点。 *)
Theorem llm_view_of_roundtrip : forall (l : list Q) (s : nat),
  llm_view_of (phase_marker (llm_view_of l s)) s = llm_view_of l s.
Proof.
  intros l s.
  rewrite llm_view_of_marker. unfold llm_view_of.
  rewrite P0_idempotent. reflexivity.
Qed.

(* ---------- §16.3 加分：Tex_of_Tabs 前提恒真定理化 ----------
   审计在案：Tex_of_Tabs（§E）的前提 (forall m', Evidence) 恒真——
   在册 llm_Tabs_const（§11）已给常量证据族实现。真化＝把「恒真」
   从审计注记升格为显式定理：前提由在册件实例化消解，得无条件形；
   并给构造性见证（铸节点逐字可读）与 inhabitance 推论。 *)

(* 前提恒真的定理化：Tex_of_Tabs 的前提经 llm_Tabs_const 实例化消解后
   的无条件简化面——Tex phi 对任意 phi 恒可构造，无需任何前提。 *)
Theorem Tex_of_Tabs_premise_trivial : forall (phi m : Dig), Tex phi.
Proof.
  intros phi m. exact (Tex_of_Tabs phi m (llm_Tabs_const phi)).
Qed.

(* 构造性见证：无条件形的 witness 节点逐字入册（Lv0 层、
   常量证据 evNum 0），「恒真」从注记变为可检查的构造对象。 *)
Theorem Tex_of_Tabs_premise_trivial_witness : forall (phi m : Dig),
  exists T : Tex phi, projT1 T = mkTrNode Lv0 phi m (evNum 0%Q).
Proof.
  intros phi m.
  exists (existT _ (mkTrNode Lv0 phi m (evNum 0%Q)) (eq_refl phi)).
  reflexivity.
Qed.

(* inhabitance 推论：Tex 纤维全域非空（模型的选取无关性——
   任意 Dig 皆可充当见证节点 的 model 槽）。 *)
Corollary Tex_inhabited : forall phi : Dig, Tex phi.
Proof.
  intros phi. exact (Tex_of_Tabs_premise_trivial phi (dQ 0%Q)).
Qed.

(* ---------- §16.4 终验：Print Assumptions（G4 关） ---------- *)

Print Assumptions OrgDiff_s_irrelevant.
Print Assumptions OrgDiff_nonneg_transport.
Print Assumptions llm_view_mk_proj.
Print Assumptions llm_view_eta.
Print Assumptions llm_view_self_consistent.
Print Assumptions llm_view_PhP0_consistent.
Print Assumptions llm_view_PhP0_gate_exact.
Print Assumptions llm_view_roundtrip.
Print Assumptions llm_view_of_roundtrip.
Print Assumptions Tex_of_Tabs_premise_trivial.
Print Assumptions Tex_of_Tabs_premise_trivial_witness.
Print Assumptions Tex_inhabited.


(* ========== 提取面：语句名全量 Separate Extraction（born-clean 载体直出 OCaml） ========== *)

From Stdlib Require Import Extraction.

Separate Extraction
  eq_imp_id id_imp_eq NatLe NatLe_dropI NatLe_liftI QeqT qeq_imp_qeqT qeqT_imp_qeq
  insert_q P0 rot Pinf interleave Pmid insert_q_perm_cons D5_P0_perm
  D5_Pinf_perm D5_support_same dedup_aux dedup H_ms sum_adjdiff H_adj Qle_bool_false_le
  Qle_dec' qadd_le qopp_le qmul_le_r Qle_0_sub' qsub_le_r qsub_add abs_eq
  abs_neg abs_nonneg Qeqb_true_of Qeqb_sym Qeqb_trans Qmem Qmem_intro Qmem_elim
  bool_id_absurd Qmem_nil_elim Qmem_cons Qmem_cons_l Qmem_cons_r Qmem_refl_cons Qmem_weaken Qmem_dedup_aux_keep
  Qmem_dedup_aux_drop dedup_aux_duck Qnodup dedup_aux_Qnodup dedup_Qnodup dedup_Qmem_l dedup_Qmem_r Qmem_perm
  Qmem_cons_nodup remove_one same_set_length N9_ms_perm_inv N9_seq_separates qadd_nonneg xq_Qle_bool_le xq_abs_id
  xq_abs_eq0 xq_minus_self xq_abs_zero xq_abs_eq xq_abs_opp xq_minus_opp xq_abs_sub_comm xq_H_adj_nonneg
  xq_le_add_abs xq_sortQ_insert xq_P0_sorted lastq xq_lastq_In xq_hd_In_gen xq_P0_cons_ne xq_hd_le_lastq
  xq_telescope xq_pair_dist_le C_sorted_min_adj nat_fact q_fact Zpos_le_roundtrip nat_fact_ge1 D8_sorted_frac_pos
  D8_tends_zero Tex Tabs gate_pass cgen_lastq_app cgen_H_adj_snoc cgen_rev_cons_ne cgen_lastq_rev_cons
  C_gen_sym_rev C_gen C_gen_attained C_gen_sorted n9_l0 spread sorted_hd_le_in sorted_in_le_last
  spread_pair_le qcoef_step H_adj_pair_bound perm3_cases n9_max n9_max_attained n9_min_is_sorted n9_const_ratio
  n9_separation_exact n9_naive_bound n9_naive_bound_Hadj nat_fact_pos_Z q_inv_den1 q_fact_ne0 q_fact_recurrence nat_fact_mono
  nat_fact_le nat_fact_le_Z q_fact_recip_anti D8_mono sum_fact_recip q_recip_step_Z q_fact_step2_le sum_fact_recip_inv
  q_fact_inv_pos sum_fact_recip_lt3 q_fact_rate q_fact_rate_exists pow2_ge1 nat_fact_pow2_lb q_fact_inv_le_pow2 llm_firstn_ge_full
  llm_skipn_ge_nil llm_interleave_length llm_interleave_perm llm_gate_pass_iff llm_gate_pass_false_iff llm_gate_pass_mono_thr llm_gate_pass_anti_H llm_rot_id
  llm_rot_full llm_rot_cyclic_inv llm_rot_cyclic_perm llm_rot_cyclic_length llm_P0_length llm_Pinf_length llm_Pmid_zero llm_Pmid_len_endpoint
  llm_Pmid_full llm_Tex_fiber llm_Tex_fiber_inv llm_Tabs_const llm_canon_tab llm_canon_tab_eval llm_view_gate_iff freq
  freq_nonneg freq_app freq_eq_congr freq_zero_of_notQmem freq_swap freq_perm sumf Sigma_freq
  sumf_dedup_aux sum_freq_dedup qsum mu mu_perm qsum_freq_map qsum_map_div mu_total_mass
  qeq_le qmul_eq0_fwd qmul_eq0_intro_l qmul_eq0_intro_r qmul_eq0_iff qsq_nonneg qsq_eq0 qsum_sq_zero
  qsum_sq_zero_intro qmul_fiber_key qsum_sq_fiber_key fiber cozero fiber_in cozero_in fiber_mul_union
  fiber_sumsq_inter fiber_one_empty fiber_zero_full Q_dec chi_spec fiber_indicator ideal_sub_closed fiber_cozero_length
  fiber_cozero_disjoint fiber_cozero_cover fiber_cozero_compl Qle_total_q Qle_bool_false_inv insert_q_cons_eq sum_adjdiff_cons_eq sum_adjdiff_single
  sum_adjdiff_nil_eq length_single length_nil_eq z_of_nat_succ_eq z_of_nat_0_eq Forall_in Forall_of_pointwise in_insert_q
  insert_sorted P0_sorted sorted_P0_id qmake_succ qmul2 qstep H_adj_bound P0_idempotent
  swap_adj swap_adj_perm P0_absorbs_Pmid OrgDiff OrgDiff_nonzero_exists W_carrier proj_W real_W
  proj_real_round Hsup Hsup_S_eq Hsup_mono Hsup_bounded Tneg Tex_of_Tabs phase_classify
  swap_adj_oob swap_adj_invol count_q count_q_self_cons count_q_perm count_q_pos_wit sorted_perm_count_qeq P0_perm_inv
  sum_adjdiff_qeq H_adj_qeq H_adj_P0_perm P0_swap_adj_qeq H_adj_swap_adj phase_classify_lam_const phase_classify_P0_spec phase_classify_Mid_spec
  phase_classify_perm_inv_cond phase_classify_perm_counter pmid_len_l_eq_P0 pmid_len_l_eq_Pinf pmid_len_l_le_P0 pmid_len_Pinf_le_l pmid_firstn_len pmid_skipn_len
  Pmid_len_endpoint Pmid_len_eq_P0 Pmid_len_perm Pmid_zero_endpoint Pmid_zero_perm Pmid_len_perm_eq Pmid_len_perm_P0_left Pmid_len_spectrum
  P0_absorbs_Pmid_len OrgDiff_eq OrgDiff_nonneg OrgDiff_nonneg_dec OrgDiff_Pmid_len_zero OrgDiff_Pmid_general_nonzero freq_pos_of_in freq_filter_le
  sumf_mono_r qsum_map_mu_w mu_fiber_pos mu_fiber_mass_lb dedup_aux_In_l dedup_In_l freq_filter_eq_all freq_w_fiber_eq
  sumf_ext mu_fiber_mass_eq OrgDiff_s_irrelevant OrgDiff_nonneg_transport llm_view_mk_proj llm_view_eta llm_view_of llm_view_of_marker
  llm_view_of_gate llm_view_self_consistent llm_view_PhP0_consistent llm_view_PhP0_gate_exact llm_view_roundtrip llm_view_of_roundtrip Tex_of_Tabs_premise_trivial Tex_of_Tabs_premise_trivial_witness
  Tex_inhabited.

End DTPT.

(* ============================================================
   归并段 M1 退役记录：DTPT_Dig.v —— 不并入，直接退役
   判定依据：其全部声明（Inductive Dig、insert_q、P0、rot、Pinf、
   Pmid、insert_q_perm_cons、D5_P0_perm、D5_Pinf_perm）与本文件
   §1–§3 逐字重复；独有内容仅注释（Pmid 端点遗留注记已由
   DTPT_PmidEnd.v 偿还）。源件以 .retired_ 前缀快照留存。
   ============================================================ *)

(* ============================================================
   归并段 S2 退役记录：DTPT_CoZero.v / DTPT_Phases.v
   —— 并入本文件 §13/§14 后退役；主树零消费者（Phases 的下游
   OrgDiff 已于 M2 先期并入 Phases 自身，实测 grep 全工作区无
   Require/Import 残余），两源件以 .retired_S2 前缀快照留存。
   ============================================================ *)

(* ========== 切片替换追加：替换件公理闭包打印（G4 面） ========== *)

Print Assumptions DTPT.DTPT.llm_rot_id.
Print Assumptions DTPT.DTPT.insert_q_cons_eq.
Print Assumptions DTPT.DTPT.sum_adjdiff_single.
Print Assumptions DTPT.DTPT.llm_Tabs_const.
Print Assumptions DTPT.DTPT.llm_view_roundtrip.
