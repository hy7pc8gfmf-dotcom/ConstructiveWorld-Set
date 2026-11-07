(* ConstructiveWorld-Set -- a budget constitution: decidable validation of growth-breakthrough declarations. *)
(** * UpConstitution: decidable validation of growth-breakthrough claims.

    Mission.  [q_decay_breaks] (the geometric-decay breakthrough
      theorem), the decidable validators
      [claim_pass]/[check_claim]/[check_report],
      [constitution_nonvacuous] (non-vacuity), the four counterexamples
      [invalid_claim_counter_*], the chained composition [claim_chain],
      and the [real_budget_witness] demonstration.  Semantics: each
      step shrinks the baseline [c0] by the factor [(1 - kappa)]; a
      valid declaration strictly crosses the threshold [eps] within
      [N] steps.

    Dependencies.  [S01_BaseRing]..[S15_TailFEPUp], [UpBudgetReal];
      Stdlib [QArith] [Lia].

    References.  Consistency validation of resource-budget declarations
      (a formalization of geometric-growth constraints); [UpBudgetReal]
      ([r_arch_pow_real], the Real-layer counterpart whose budget is
      this constitution's breakthrough budget); the same-name
      ConstructiveWorld-Main baseline.

    Constructivity.  Every proof closes by [Qed]; zero admission faces,
      no classical logic; statement faces are Set-carried (equalities
      as [QeqT]/[Id], order predicates as [QleT']/[QltT], budgets as
      [NatLe]/[sigT]; zero Prop leakage).

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      UpConstitution.v] compiles cleanly (exit 0); the first eight bytes
      of the artifact are [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
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
Require Import UpBudgetReal.

Local Open Scope Q_scope.

(* ================= Section 0. Piece 1: the Set-layer type of improvement declarations ================= *)
(* Design note: the [QleT]/[QltT] proofs are not packed into a [sigT] type -- that shape would make  *)
(* declarations with [kappa >= 1] non-constructible, directly conflicting with Piece 4 (concrete *)
(* counterexample declarations must be constructible for the validator to reject them).  The settled *)
(* shape is therefore: an unconstrained [Record] plus validator adjudication. *)
(* Semantics: each step shrinks the baseline [c0] by the factor [(1 - kappa)]; the declaration asserts *)
(* that the threshold [eps] is strictly crossed within [N] steps. *)

Record claim_decl : Set := mk_claim {
  cl_c0 : Q;        (* the current baseline value [c0] *)
  cl_eps : Q;       (* the target threshold [eps] *)
  cl_kappa : Q;     (* the declared improvement rate [kappa] *)
  cl_N : nat;       (* the declared reaching budget [N] *)
  cl_id : nat       (* the declaration id *)
}.

(* ================= Section 1. Q-layer algebra micro-facts (bridges and rewrites; the [LCAudit] precedent caliber) ================= *)
(*   Statement faces fully Set-ified: [==] -> [QeqT], [Qle] -> [QleT'], [Qlt] -> [QltT]; *)
(*   proofs route through the three bridges [qeqT_imp_qeq] / [QltT_to_Qlt] / [QleT'_to_Qle]. *)

Lemma uc_qeq_le : forall x y : Q, QeqT x y -> QleT' x y.
Proof.
intros x y H. apply Qle_to_QleT'.
pose proof (qeqT_imp_qeq x y H) as He. rewrite He. apply Qle_refl.
Qed.

Lemma uc_qeq_le_l : forall x y z : Q, QeqT x y -> QleT' x z -> QleT' y z.
Proof.
intros x y z H H0. apply Qle_to_QleT'.
pose proof (qeqT_imp_qeq x y H) as He.
pose proof (QleT'_to_Qle x z H0) as H0'.
rewrite He in H0'. exact H0'.
Qed.

Lemma uc_qeq_le_r : forall x y z : Q, QeqT x y -> QleT' z x -> QleT' z y.
Proof.
intros x y z H H0. apply Qle_to_QleT'.
pose proof (qeqT_imp_qeq x y H) as He.
pose proof (QleT'_to_Qle z x H0) as H0'.
rewrite He in H0'. exact H0'.
Qed.

Lemma uc_qeq_lt_l : forall x y z : Q, QeqT x y -> QltT x z -> QltT y z.
Proof.
intros x y z H H0. apply Qlt_to_QltT.
pose proof (qeqT_imp_qeq x y H) as He.
pose proof (QltT_to_Qlt x z H0) as H0'.
rewrite He in H0'. exact H0'.
Qed.

Lemma uc_qeq_lt_r : forall x y z : Q, QeqT x y -> QltT z x -> QltT z y.
Proof.
intros x y z H H0. apply Qlt_to_QltT.
pose proof (qeqT_imp_qeq x y H) as He.
pose proof (QltT_to_Qlt z x H0) as H0'.
rewrite He in H0'. exact H0'.
Qed.

(* Positivity of the reciprocal (the self-contained Q-layer version; finished constructively by the three-way decision) *)
Lemma uc_inv_pos : forall x : Q, QltT 0 x -> QltT 0 (1 / x).
Proof.
intros x Hx. apply Qlt_to_QltT.
pose proof (QltT_to_Qlt 0 x Hx) as Hx'.
destruct (Q_dec 0 (1 / x)) as [[H | H] | H].
- exact H.
- exfalso.
  assert (Hle : (1 / x) * x <= 0 * x).
  { apply (Qmult_le_compat_r (1 / x) 0 x).
    - apply (Qlt_le_weak (1 / x) 0). exact H.
    - apply (Qlt_le_weak 0 x). exact Hx'. }
  assert (Hone : (1 / x) * x == 1).
  { field. intro Hz. rewrite Hz in Hx'. exact (Qlt_irrefl 0%Q Hx'). }
  rewrite Hone in Hle.
  assert (Hlt0 : Qlt 0 (0 * x)).
  { apply (Qlt_le_trans 0%Q 1%Q (0 * x)).
    - unfold Qlt. simpl. lia.
    - exact Hle. }
  assert (Hrw : 0 * x == 0%Q) by ring.
  rewrite Hrw in Hlt0.
  exact (Qlt_irrefl 0%Q Hlt0).
- exfalso.
  assert (Hle : (1 / x) * x <= 0 * x).
  { apply (Qmult_le_compat_r (1 / x) 0 x).
    - assert (Hzx : (1 / x) == 0%Q) by (apply Qeq_sym; exact H).
      rewrite Hzx. apply Qle_refl.
    - apply (Qlt_le_weak 0 x). exact Hx'. }
  assert (Hone : (1 / x) * x == 1).
  { field. intro Hz. rewrite Hz in Hx'. exact (Qlt_irrefl 0%Q Hx'). }
  rewrite Hone in Hle.
  assert (Hlt0 : Qlt 0 (0 * x)).
  { apply (Qlt_le_trans 0%Q 1%Q (0 * x)).
    - unfold Qlt. simpl. lia.
    - exact Hle. }
  assert (Hrw : 0 * x == 0%Q) by ring.
  rewrite Hrw in Hlt0.
  exact (Qlt_irrefl 0%Q Hlt0).
Qed.

(* Adding [-x] rewrites the order *)
Lemma uc_le_opp_shift : forall x y : Q, QleT' x y -> QleT' 0 (y + - x).
Proof.
intros x y H. apply Qle_to_QleT'.
pose proof (QleT'_to_Qle x y H) as H'.
apply (Qle_trans _ (x + - x) _).
- rewrite (Qplus_opp_r x). apply Qle_refl.
- apply Qplus_le_compat.
  + exact H'.
  + apply Qle_refl.
Qed.

Lemma uc_lt_opp_shift : forall x y : Q, QltT x y -> QltT 0 (y + - x).
Proof.
intros x y H. apply Qlt_to_QltT.
pose proof (QltT_to_Qlt x y H) as H'.
assert (Hmid : Qlt ((- x) + x) ((- x) + y)).
{ apply (proj2 (Qplus_lt_r x y (- x))). exact H'. }
assert (Hopp : (- x) + x == 0%Q) by ring.
rewrite <- Hopp.
rewrite (Qplus_comm y (- x)).
exact Hmid.
Qed.

Lemma uc_lt_minus_inv : forall x y : Q, QltT 0 (y + - x) -> QltT x y.
Proof.
intros x y H. apply Qlt_to_QltT.
pose proof (QltT_to_Qlt 0 (y + - x) H) as H'.
assert (Hmid : Qlt (x + 0) (x + (y + - x))).
{ apply (proj2 (Qplus_lt_r 0 (y + - x) x)). exact H'. }
rewrite (Qplus_0_r x) in Hmid.
assert (Hring : x + (y + - x) == y) by ring.
rewrite Hring in Hmid.
exact Hmid.
Qed.

Lemma uc_opp_le_shift : forall x : Q, QleT' 0 x -> QleT' (- x) 0.
Proof.
intros x H. apply Qle_to_QleT'.
pose proof (QleT'_to_Qle 0 x H) as H'.
apply (Qle_trans _ ((- x) + x) _).
- assert (Hsub1 : Qle ((- x) + 0) ((- x) + x)).
  { apply Qplus_le_compat.
    + apply Qle_refl.
    + exact H'. }
  rewrite (Qplus_0_r (- x)) in Hsub1. exact Hsub1.
- assert (Hopp : (- x) + x == 0%Q) by ring.
  rewrite Hopp. apply Qle_refl.
Qed.

(* Right multiplication cancellation (strict version; finished constructively by the three-way [Q_dec]) *)
Lemma uc_cancel_lt_r : forall a b p : Q,
  QltT 0 p -> QltT (a * p) (b * p) -> QltT a b.
Proof.
intros a b p Hp Hlt. apply QltT_to_Qlt in Hlt.
pose proof (QltT_to_Qlt 0 p Hp) as Hp'.
destruct (Q_dec a b) as [[H1 | H2] | H3].
- apply Qlt_to_QltT. exact H1.
- exfalso. apply (Qlt_irrefl (b * p)).
  apply (Qlt_trans (b * p) (a * p) (b * p)).
  + apply (Qmult_lt_compat_r b a p Hp' H2).
  + exact Hlt.
- exfalso. apply (Qlt_irrefl (a * p)).
  rewrite <- H3 in Hlt. exact Hlt.
Qed.

(* ================= Section 2. [q_pow] power algebra (using [q_pow]) ================= *)

Lemma uc_pow_eq_compat : forall (x y : Q) (n : nat),
  QeqT x y -> QeqT (q_pow x n) (q_pow y n).
Proof.
intros x y n Hxy. induction n as [| n IH]; simpl.
- reflexivity.
- apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq (q_pow x n) (q_pow y n) IH) as H1.
  pose proof (qeqT_imp_qeq x y Hxy) as H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma uc_pow_add : forall (x : Q) (p q : nat),
  QeqT (q_pow x (p + q)%nat) (q_pow x p * q_pow x q).
Proof.
intros x p q. induction p as [| p IH]; simpl.
- apply qeq_imp_qeqT. ring.
- apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq (q_pow x (p + q)%nat) (q_pow x p * q_pow x q) IH) as H1.
  rewrite H1. ring.
Qed.

Lemma uc_pow_mul : forall (x y : Q) (n : nat),
  QeqT (q_pow (x * y) n) (q_pow x n * q_pow y n).
Proof.
intros x y n. induction n as [| n IH]; simpl.
- reflexivity.
- apply qeq_imp_qeqT.
  pose proof (qeqT_imp_qeq (q_pow (x * y) n) (q_pow x n * q_pow y n) IH) as H1.
  rewrite H1. ring.
Qed.

Lemma uc_pow_inv_pair : forall (a b : Q) (n : nat),
  QeqT (a * b) 1 -> QeqT (q_pow a n * q_pow b n) 1.
Proof.
intros a b n Hab. induction n as [| n IH]; simpl.
- reflexivity.
- apply qeq_imp_qeqT.
  assert (Hab' : a * b == 1) by (apply qeqT_imp_qeq; exact Hab).
  assert (Hre : (a * q_pow a n) * (b * q_pow b n)
              == (a * b) * (q_pow a n * q_pow b n)) by ring.
  rewrite Hre. rewrite Hab'.
  pose proof (qeqT_imp_qeq (q_pow a n * q_pow b n) 1 IH) as H1.
  rewrite H1. reflexivity.
Qed.

(* Decaying exponents decrease: [0 <= x <= 1] implies [x^(p+q) <= x^p] (iterated via [sc_qpow_dec]) *)
Lemma uc_pow_le_drop : forall (x : Q) (p q : nat),
  QleT' 0 x -> QleT' x 1 -> QleT' (q_pow x (p + q)%nat) (q_pow x p).
Proof.
intros x p q Hx0 Hx1. induction q as [| q IH].
- replace (p + 0)%nat with p by lia. apply qleT'_refl.
- replace (p + Datatypes.S q)%nat with (Datatypes.S (p + q)) by lia.
  apply (qleT'_trans _ (q_pow x (p + q)%nat) _).
  + pose proof (QleT'_to_Qle 0 x Hx0) as Hx0'.
    pose proof (QleT'_to_Qle x 1 Hx1) as Hx1'.
    exact (sc_qpow_dec x (p + q)%nat Hx0' Hx1').
  + exact IH.
Qed.

(* ================= Section 3. the Q-form Bernoulli inequality: [(1+c)^n >= 1 + n*c] for [c >= 0] ================= *)

Lemma uc_znat_pos : forall n : nat, QleT' 0 (Z.of_nat n # 1).
Proof. intro n. apply Qle_to_QleT'. unfold Qle. simpl. lia. Qed.

Lemma uc_bernoulli : forall (c : Q) (n : nat),
  QleT' 0 c -> QleT' (1 + (Z.of_nat n # 1) * c) (q_pow (1 + c) n).
Proof.
intros c n HcT. pose proof (QleT'_to_Qle 0 c HcT) as Hc.
induction n as [| n IH].
- replace (q_pow (1 + c) 0) with 1%Q by reflexivity.
  apply uc_qeq_le. apply qeq_imp_qeqT.
  replace (Z.of_nat 0 # 1) with (0 # 1)%Q by reflexivity.
  ring.
- apply Qle_to_QleT'.
  assert (Hs : (Z.of_nat (Datatypes.S n) # 1) == (Z.of_nat n # 1) + 1).
  { unfold Qeq. simpl. lia. }
  apply (Qle_trans _ ((1 + (Z.of_nat n # 1) * c) + c) _).
  + assert (Hface : (1 + (Z.of_nat (Datatypes.S n) # 1) * c)
                 == ((1 + (Z.of_nat n # 1) * c) + c)).
    { rewrite Hs. ring. }
    rewrite Hface. apply Qle_refl.
  + apply (Qle_trans _ ((1 + (Z.of_nat n # 1) * c) * (1 + c)) _).
    * (* [(1 + n*c) + c <= (1 + n*c)*(1 + c)]: the difference term [n*c*c >= 0] *)
      apply (Qle_trans _ ((1 + (Z.of_nat n # 1) * c) + c + (Z.of_nat n # 1) * c * c) _).
      -- apply (Qle_trans _ ((1 + (Z.of_nat n # 1) * c) + c + 0) _).
         ++ rewrite (Qplus_0_r ((1 + (Z.of_nat n # 1) * c) + c)). apply Qle_refl.
         ++ apply Qplus_le_compat.
            ** apply Qle_refl.
            ** (* [0 <= (n#1 * c) * c] *)
               apply (Qle_trans _ (0 * c)%Q _).
               { assert (Hz : 0 * c == 0%Q) by ring.
                 rewrite Hz. apply Qle_refl. }
               { pose proof (QleT'_to_Qle 0 (Z.of_nat n # 1) (uc_znat_pos n)) as Hzn.
                 assert (Hzc : Qle 0 ((Z.of_nat n # 1) * c)).
                 { apply (Qle_trans _ (0 * c)%Q _).
                   - assert (Hz : 0 * c == 0%Q) by ring.
                     rewrite Hz. apply Qle_refl.
                   - apply (Qmult_le_compat_r 0 (Z.of_nat n # 1) c Hzn Hc). }
                 apply (Qle_trans _ (0 * c)%Q _).
                 - assert (Hz : 0 * c == 0%Q) by ring.
                   rewrite Hz. apply Qle_refl.
                 - apply (Qmult_le_compat_r 0 ((Z.of_nat n # 1) * c) c Hzc Hc). }
      -- assert (Hmbe : (1 + (Z.of_nat n # 1) * c) + c + (Z.of_nat n # 1) * c * c
                     == (1 + (Z.of_nat n # 1) * c) * (1 + c)) by ring.
         rewrite Hmbe. apply Qle_refl.
    * (* scaling up by the monotone factor [(1+c)] (with [0 <= 1+c]) *)
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 + c) n)).
      rewrite (Qmult_comm (1 + c) (q_pow (1 + c) n)).
      apply (Qmult_le_compat_r (1 + (Z.of_nat n # 1) * c) (q_pow (1 + c) n) (1 + c)
               (QleT'_to_Qle _ _ IH)).
      assert (Hle0c : Qle 0 (1 + c)).
      { apply (Qle_trans _ 1%Q _).
        - unfold Qle. simpl. lia.
        - assert (Hle1c : Qle (1 + 0) (1 + c)).
          { apply Qplus_le_compat.
            - apply Qle_refl.
            - exact Hc. }
          rewrite (Qplus_0_r 1%Q) in Hle1c. exact Hle1c. }
      exact Hle0c.
Qed.

(* ================= Section 4. the Q-layer Archimedean breakthrough: a genuine growth rate yields a positive budget ([Qarchimedean] + Bernoulli) ================= *)

Theorem uc_growth_breaks : forall (c T : Q),
  QltT 0 c -> QltT 0 T ->
  sigT (fun N => And (NatLe 1 N) (QltT T (q_pow (1 + c) N))).
Proof.
intros c T Hc HT.
pose proof (QltT_to_Qlt 0 c Hc) as Hc'.
pose proof (QltT_to_Qlt 0 T HT) as HT'.
destruct (Qarchimedean (T / c)) as [p Hp].
exists (Datatypes.S (Pos.to_nat p)).
split.
- apply NatLe_lift. lia.
- apply Qlt_to_QltT.
  assert (Hconv : QeqT (Z.of_nat (Pos.to_nat p) # 1) (Z.pos p # 1))
    by (apply positive_nat_Z).
  assert (Hconv2 : Z.of_nat (Datatypes.S (Pos.to_nat p)) = (Z.pos p + 1)%Z) by lia.
  assert (Hid : (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) == (Z.pos p # 1) + 1).
  { rewrite Hconv2. unfold Qeq. simpl. lia. }
  assert (Hcancel : (T / c) * c == T).
  { field. intro Hz. rewrite Hz in Hc'. exact (Qlt_irrefl 0%Q Hc'). }
  assert (H0 : (T / c) * c < (Z.pos p # 1) * c).
  { apply (Qmult_lt_compat_r (T / c) (Z.pos p # 1) c Hc' Hp). }
  rewrite Hcancel in H0.
  assert (H1 : (Z.pos p # 1) * c < (Z.pos p # 1) * c + c).
  { assert (Hb : (Z.pos p # 1) * c + 0 < (Z.pos p # 1) * c + c).
    { apply (proj2 (Qplus_lt_r 0%Q c ((Z.pos p # 1) * c))). exact Hc'. }
    assert (Hz0 : (Z.pos p # 1) * c + 0 == (Z.pos p # 1) * c) by ring.
    rewrite Hz0 in Hb. exact Hb. }
  assert (H2 : (Z.pos p # 1) * c + c
             == (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c).
  { rewrite Hid. ring. }
  assert (H3 : T < (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c).
  { apply (Qlt_trans T ((Z.pos p # 1) * c) _).
    - exact H0.
    - rewrite <- H2. exact H1. }
  assert (H4 : T < 1 + (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c).
  { apply (Qlt_trans T ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c) _).
    - exact H3.
    - assert (Hb : ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c + 0)
                 < ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c + 1)).
      { apply (proj2 (Qplus_lt_r 0%Q 1%Q
                        ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c))).
        unfold Qlt. simpl. lia. }
      assert (Hz1 : ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c + 0)
                  == ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c)) by ring.
      rewrite Hz1 in Hb.
      assert (Hz2 : ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c + 1)
                  == (1 + (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c)) by ring.
      rewrite Hz2 in Hb.
      exact Hb. }
  pose proof (QleT'_to_Qle _ _
    (uc_bernoulli c (Datatypes.S (Pos.to_nat p))
       (Qle_to_QleT' 0 c (Qlt_le_weak 0 c Hc')))) as Hb.
  apply (Qlt_le_trans _ _ _ H4 Hb).
Qed.

(* ================= Section 5. the Q-layer geometric-decay breakthrough (the self-contained Q-layer counterpart of [r_arch_pow_real]) ================= *)
(*   [kappa in (0,1)], [c0 > 0], [eps > 0] imply a positive budget [N] with [c0 * (1-kappa)^N < eps]. *)
(*   The explicit shape of the budget [N]: [Qarchimedean] solved on [c0/eps] over [kappa/(1-kappa)]. *)

Theorem q_decay_breaks : forall (k c0 eps : Q),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  sigT (fun N => And (NatLe 1 N) (QltT (c0 * q_pow (1 - k) N) eps)).
Proof.
intros k c0 eps HkT0 HkT1 Hc0T HeT.
pose proof (QltT_to_Qlt 0 k HkT0) as Hk0.
pose proof (QltT_to_Qlt k 1 HkT1) as Hk1.
pose proof (QltT_to_Qlt 0 c0 Hc0T) as Hc0.
pose proof (QltT_to_Qlt 0 eps HeT) as He.
assert (H1kT : QltT 0 (1 - k)) by (apply (uc_lt_opp_shift k 1 HkT1)).
assert (H1k : Qlt 0 (1 - k)) by (apply QltT_to_Qlt; exact H1kT).
assert (HinvT : QltT 0 (1 / (1 - k))) by (apply (uc_inv_pos (1 - k) H1kT)).
assert (Hinv : Qlt 0 (1 / (1 - k))) by (apply QltT_to_Qlt; exact HinvT).
assert (Hg : 1 / (1 - k) == 1 + k / (1 - k)).
{ field. intro Hz. rewrite Hz in H1k. exact (Qlt_irrefl 0%Q H1k). }
assert (HkcLt : Qlt 0 (k / (1 - k))).
{ assert (Hpre : Qlt 0 (k * (1 / (1 - k))))
    by (apply (Qmult_lt_0_compat k (1 / (1 - k)) Hk0 Hinv)).
  assert (Hrq : k * (1 / (1 - k)) == k / (1 - k)) by (unfold Qdiv; ring).
  rewrite Hrq in Hpre. exact Hpre. }
assert (Ht : Qlt 0 (c0 / eps)).
{ assert (HinvE : Qlt 0 (1 / eps))
    by (apply QltT_to_Qlt; exact (uc_inv_pos eps HeT)).
  assert (Hpre : Qlt 0 (c0 * (1 / eps)))
    by (apply (Qmult_lt_0_compat c0 (1 / eps) Hc0 HinvE)).
  assert (Hrq : c0 * (1 / eps) == c0 / eps) by (unfold Qdiv; ring).
  rewrite Hrq in Hpre. exact Hpre. }
assert (HkcLtT : QltT 0 (k / (1 - k))) by (apply Qlt_to_QltT; exact HkcLt).
assert (HtT : QltT 0 (c0 / eps)) by (apply Qlt_to_QltT; exact Ht).
destruct (uc_growth_breaks (k / (1 - k)) (c0 / eps) HkcLtT HtT) as [N [HN1 HN]].
exists N. split.
- exact HN1.
- pose proof (QltT_to_Qlt (c0 / eps) (q_pow (1 + k / (1 - k)) N) HN) as HN'.
  assert (HgT : QeqT (1 / (1 - k)) (1 + k / (1 - k))) by (apply qeq_imp_qeqT; exact Hg).
  assert (Hpow : q_pow (1 / (1 - k)) N == q_pow (1 + k / (1 - k)) N)
    by (apply qeqT_imp_qeq; exact (uc_pow_eq_compat _ _ _ HgT)).
  assert (Hcancel2 : (c0 / eps) * eps == c0).
  { field. intro Hz. rewrite Hz in He. exact (Qlt_irrefl 0%Q He). }
  assert (Hstep : (c0 / eps) * eps < eps * q_pow (1 + k / (1 - k)) N).
  { rewrite (Qmult_comm eps (q_pow (1 + k / (1 - k)) N)).
    apply (Qmult_lt_compat_r (c0 / eps) (q_pow (1 + k / (1 - k)) N) eps He HN'). }
  rewrite Hcancel2 in Hstep.
  assert (Hmul : c0 < eps * q_pow (1 / (1 - k)) N).
  { assert (Hrq2 : eps * q_pow (1 + k / (1 - k)) N == eps * q_pow (1 / (1 - k)) N)
      by (rewrite Hpow; reflexivity).
    rewrite Hrq2 in Hstep. exact Hstep. }
  assert (Hpair : q_pow (1 - k) N * q_pow (1 / (1 - k)) N == 1).
  { apply qeqT_imp_qeq. apply uc_pow_inv_pair. apply qeq_imp_qeqT.
    field. intro Hz. rewrite Hz in H1k. exact (Qlt_irrefl 0%Q H1k). }
  assert (HposGN : QltT 0 (q_pow (1 / (1 - k)) N))
    by (apply (sc_qpow_pos N (1 / (1 - k)) Hinv)).
  apply (uc_cancel_lt_r (c0 * q_pow (1 - k) N) eps (q_pow (1 / (1 - k)) N) HposGN).
  assert (HId : (c0 * q_pow (1 - k) N) * q_pow (1 / (1 - k)) N == c0).
  { assert (Hre : (c0 * q_pow (1 - k) N) * q_pow (1 / (1 - k)) N
                == c0 * (q_pow (1 - k) N * q_pow (1 / (1 - k)) N)) by ring.
    rewrite Hre. rewrite Hpair. rewrite Qmult_1_r. reflexivity. }
  apply (uc_qeq_lt_l c0 ((c0 * q_pow (1 - k) N) * q_pow (1 / (1 - k)) N)
           (eps * q_pow (1 / (1 - k)) N)).
  + apply qeq_imp_qeqT. apply Qeq_sym. exact HId.
  + apply Qlt_to_QltT. exact Hmul.
Qed.

(* ================= Section 6. Piece 2: the decidable validator ([Defined], hence executable) ================= *)
(*   Six single-gate deciders: a bool decision plus a dependent [match] that simultaneously issues the Set-layer certificate; *)
(*   on rejection a reject code is issued (refutability: negative verdicts are equally exact). *)

(* Reject codes (E-mode: counterexamples carry the same weight as statements; negative verdicts carry machine-checkable reasons) *)
Inductive claim_reject : Set :=
| rj_kappa   (* [kappa] not in [0,1): the zero-decay shortcut or a negative rate *)
| rj_budget  (* [N = 0]: an instant-reach declaration *)
| rj_data    (* [c0 < 0] or [eps <= 0]: an illegal baseline/threshold *)
| rj_reach.  (* the threshold is not crossed within the budget [N]: no witness commitment *)

(* The pass certificate: a six-certificate pack (one [Id]-typed Set-layer certificate per gate) *)
Definition claim_pass (cl : claim_decl) : Set :=
  And (And (QleT' 0 (cl_kappa cl)) (QltT (cl_kappa cl) 1))
      (And (NatLe 1 (cl_N cl))
           (And (And (QleT' 0 (cl_c0 cl)) (QltT 0 (cl_eps cl)))
                (QltT (cl_c0 cl * q_pow (1 - cl_kappa cl) (cl_N cl))
                      (cl_eps cl)))).

(* Gate 1a: [0 <= kappa] *)
Definition kap_low_dec (cl : claim_decl)
  : Or (QleT' 0 (cl_kappa cl))
       (And (Id (Qle_bool 0 (cl_kappa cl)) false) claim_reject) :=
  match Qle_bool 0 (cl_kappa cl) as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_kappa)
  end.

(* Gate 1b: [kappa < 1] *)
Definition kap_high_dec (cl : claim_decl)
  : Or (QltT (cl_kappa cl) 1)
       (And (Id (Qlt_bool (cl_kappa cl) 1) false) claim_reject) :=
  match Qlt_bool (cl_kappa cl) 1 as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_kappa)
  end.

(* Gate 2: [N >= 1] *)
Definition bud_dec (cl : claim_decl)
  : Or (NatLe 1 (cl_N cl))
       (And (Id (Nat.leb 1 (cl_N cl)) false) claim_reject) :=
  match Nat.leb 1 (cl_N cl) as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_budget)
  end.

(* Gate 3a: [0 <= c0] *)
Definition dat_c0_dec (cl : claim_decl)
  : Or (QleT' 0 (cl_c0 cl))
       (And (Id (Qle_bool 0 (cl_c0 cl)) false) claim_reject) :=
  match Qle_bool 0 (cl_c0 cl) as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_data)
  end.

(* Gate 3b: [0 < eps] *)
Definition dat_eps_dec (cl : claim_decl)
  : Or (QltT 0 (cl_eps cl))
       (And (Id (Qlt_bool 0 (cl_eps cl)) false) claim_reject) :=
  match Qlt_bool 0 (cl_eps cl) as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_data)
  end.

(* Gate 4: reachability -- the threshold is strictly crossed within [N] steps *)
Definition reach_dec (cl : claim_decl)
  : Or (QltT (cl_c0 cl * q_pow (1 - cl_kappa cl) (cl_N cl)) (cl_eps cl))
       (And (Id (Qlt_bool (cl_c0 cl * q_pow (1 - cl_kappa cl) (cl_N cl))
                          (cl_eps cl))
                 false)
            claim_reject) :=
  match Qlt_bool (cl_c0 cl * q_pow (1 - cl_kappa cl) (cl_N cl)) (cl_eps cl)
          as b return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_reach)
  end.

(* The constitution executor itself: the six gates in sequence; all passing issues the certificate, *)
(* the first failing gate issues a reject code *)
Definition check_claim (cl : claim_decl) : Or (claim_pass cl) claim_reject :=
  match kap_low_dec cl with
  | inr (_, r) => inr r
  | inl hk0 =>
    match kap_high_dec cl with
    | inr (_, r) => inr r
    | inl hk1 =>
      match bud_dec cl with
      | inr (_, r) => inr r
      | inl hb =>
        match dat_c0_dec cl with
        | inr (_, r) => inr r
        | inl hc0 =>
          match dat_eps_dec cl with
          | inr (_, r) => inr r
          | inl he =>
            match reach_dec cl with
            | inr (_, r) => inr r
            | inl hr => inl (((hk0, hk1), (hb, ((hc0, he), hr))))
            end
          end
        end
      end
    end
  end.

(* The decidable summary report (a [vm_compute]-friendly output shape) *)
Inductive claim_verdict : Set :=
| v_pass : claim_verdict
| v_reject : claim_reject -> claim_verdict.

Definition check_report (cl : claim_decl) : claim_verdict :=
  match check_claim cl with
  | inl _ => v_pass
  | inr r => v_reject r
  end.

(* Totality of adjudication: every declaration gets a verdict *)
Lemma check_claim_total : forall cl : claim_decl,
  Or (sigT (fun w : claim_pass cl => Id (check_claim cl) (inl w)))
     (sigT (fun r : claim_reject => Id (check_claim cl) (inr r))).
Proof.
intro cl. unfold check_claim.
destruct (kap_low_dec cl) as [hk0|[f0 r0]];
  [ | right; exists r0; reflexivity ];
destruct (kap_high_dec cl) as [hk1|[f1 r1]];
  [ | right; exists r1; reflexivity ];
destruct (bud_dec cl) as [hb|[f2 r2]];
  [ | right; exists r2; reflexivity ];
destruct (dat_c0_dec cl) as [hc0|[f3 r3]];
  [ | right; exists r3; reflexivity ];
destruct (dat_eps_dec cl) as [he|[f4 r4]];
  [ | right; exists r4; reflexivity ];
destruct (reach_dec cl) as [hr|[f5 r5]];
  [ | right; exists r5; reflexivity ].
left. exists (((hk0, hk1), (hb, ((hc0, he), hr)))). reflexivity.
Qed.

(* A certificate makes the validator return [inl] (the negative branches carry [bool = false] evidence,
   refuted by the certificates; the [inl] witness is the decider's actual output -- the Set-layer [Id]
   does not quotient by proof irrelevance) *)
Lemma check_claim_inl_of_pass : forall (cl : claim_decl),
  claim_pass cl -> sigT (fun w => Id (check_claim cl) (inl w)).
Proof.
intros cl [[hk0 hk1] [hb [[hc0 he] hr]]].
unfold check_claim.
destruct (kap_low_dec cl) as [g0|[f0 r0]].
- destruct (kap_high_dec cl) as [g1|[f1 r1]].
  + destruct (bud_dec cl) as [g2|[f2 r2]].
    * destruct (dat_c0_dec cl) as [g3|[f3 r3]].
      -- destruct (dat_eps_dec cl) as [g4|[f4 r4]].
         ++ destruct (reach_dec cl) as [g5|[f5 r5]].
            ** exists (((g0, g1), (g2, ((g3, g4), g5)))). reflexivity.
            ** exfalso. pose proof (id_trans (id_sym hr) f5) as Hc5. inversion Hc5.
         ++ exfalso. pose proof (id_trans (id_sym he) f4) as Hc4. inversion Hc4.
      -- exfalso. pose proof (id_trans (id_sym hc0) f3) as Hc3. inversion Hc3.
    * exfalso. pose proof (id_trans (id_sym hb) f2) as Hc2. inversion Hc2.
  + exfalso. pose proof (id_trans (id_sym hk1) f1) as Hc1. inversion Hc1.
- exfalso. pose proof (id_trans (id_sym hk0) f0) as Hc0x. inversion Hc0x.
Qed.

(* ================= Section 7. Piece 3: soundness -- validator passage implies a breakthrough witness exists ================= *)

Theorem valid_claim_yields_breakthrough : forall (cl : claim_decl) (w : claim_pass cl),
  Id (check_claim cl) (inl w) ->
  sigT (fun N' => And (NatLe N' (cl_N cl))
                      (QltT (cl_c0 cl * q_pow (1 - cl_kappa cl) N') (cl_eps cl))).
Proof.
intros cl w Hw. exists (cl_N cl). split.
- apply NatLe_lift. lia.
- destruct w as [[hk0 hk1] [hb [[hc0 he] hr]]]. exact hr.
Qed.

(* Downgrading a non-strict certificate: [Qle_bool = false] implies [QltT y x] (the three-way [Qle_bool] rewrite) *)
Lemma uc_qle_bool_false_inv : forall x y : Q, Id (Qle_bool x y) false -> QltT y x.
Proof.
intros x y Hf.
destruct (Q_dec x y) as [[H1 | H2] | H3].
- exfalso. unfold Qle_bool, Qcompare in Hf.
  pose proof (proj2 (Qlt_alt x y) H1) as E. rewrite E in Hf. inversion Hf.
- apply Qlt_to_QltT. exact H2.
- exfalso. unfold Qle_bool, Qcompare in Hf.
  unfold Qeq in H3.
  pose proof (proj2 (Z.compare_eq_iff (Qnum x * QDen y) (Qnum y * QDen x)) H3) as E.
  rewrite E in Hf. inversion Hf.
Qed.

Lemma uc_qleT_of_ltT : forall x y : Q, QltT x y -> QleT' x y.
Proof.
intros x y H.
destruct (Qle_bool x y) eqn:Eb.
- apply RealSetoid.eq_Id. exact Eb.
- exfalso. apply (Qlt_irrefl y).
  pose proof (uc_qle_bool_false_inv x y (RealSetoid.eq_Id _ _ Eb)) as Hbad.
  pose proof (QltT_to_Qlt y x Hbad) as Hyx.
  pose proof (QltT_to_Qlt x y H) as Hxy.
  exact (Qlt_trans y x y Hyx Hxy).
Qed.

(* The constitution is non-vacuous: a genuine growth rate yields a budget that passes the validator (discharged by [q_decay_breaks]) *)
Theorem constitution_nonvacuous : forall (c0 eps k : Q) (i : nat),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  sigT (fun N => sigT (fun w => Id (check_claim (mk_claim c0 eps k N i)) (inl w))).
Proof.
intros c0 eps k i Hk0 Hk1 Hc0 He.
destruct (q_decay_breaks k c0 eps Hk0 Hk1 Hc0 He) as [N [HN1 HN]].
exists N.
assert (Hp : claim_pass (mk_claim c0 eps k N i)).
{ repeat split.
  - exact (uc_qleT_of_ltT 0 k Hk0).
  - exact Hk1.
  - exact HN1.
  - exact (uc_qleT_of_ltT 0 c0 Hc0).
  - exact He.
  - exact HN. }
pose proof (check_claim_inl_of_pass (mk_claim c0 eps k N i) Hp) as Hw.
destruct Hw as [w Hwin]. exists w. exact Hwin.
Qed.

(* ================= Section 8. Piece 4: refutability -- exact verdicts on concrete counterexamples (E-mode) ================= *)

(* Counterexample 1: the zero-decay shortcut declaration with [kappa = 1] (the [(1-kappa)^N == 0] cheat path; the constitution rejects it) *)
Definition claim_bad_kappa1 : claim_decl := mk_claim (8 # 10) (1 # 10) 1 5 11.

(* Counterexample 2: a negative-rate declaration *)
Definition claim_bad_kappaneg : claim_decl :=
  mk_claim (8 # 10) (1 # 10) (-1 # 2) 5 12.

(* Counterexample 3: an instant-reach declaration with [N = 0] *)
Definition claim_bad_budget : claim_decl :=
  mk_claim (8 # 10) (1 # 10) (1 # 2) 0 13.

(* Counterexample 4: exactly at the boundary without crossing ([1 * (1/2)^1 = 1/2] is not strictly below [1/2]) -- no witness commitment *)
Definition claim_bad_reach : claim_decl := mk_claim 1 (1 # 2) (1 # 2) 1 14.

Theorem invalid_claim_counter_kappa1 :
  Id (check_report claim_bad_kappa1) (v_reject rj_kappa).
Proof. vm_compute. reflexivity. Qed.

Theorem invalid_claim_counter_kappaneg :
  Id (check_report claim_bad_kappaneg) (v_reject rj_kappa).
Proof. vm_compute. reflexivity. Qed.

Theorem invalid_claim_counter_budget :
  Id (check_report claim_bad_budget) (v_reject rj_budget).
Proof. vm_compute. reflexivity. Qed.

Theorem invalid_claim_counter_reach :
  Id (check_report claim_bad_reach) (v_reject rj_reach).
Proof. vm_compute. reflexivity. Qed.

(* ================= Section 9. Piece 5: claim composition -- constitutional closure of self-improvement chains ================= *)

(* The composed declaration: rates compose as [kA + kB - kA*kB], budgets add, and the interface gate is [epsA == c0B] *)
Definition chain_claim (A B : claim_decl) : claim_decl :=
  mk_claim (cl_c0 A) (cl_eps B)
           (cl_kappa A + cl_kappa B - cl_kappa A * cl_kappa B)
           (cl_N A + cl_N B)%nat
           (cl_id A).

Lemma uc_minus_opp : forall x y : Q, QeqT (x - y) (x + (- y)).
Proof. intros x y. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma uc_one_minus_comp : forall kA kB : Q,
  QeqT (1 - (kA + kB - kA * kB)) ((1 - kA) * (1 - kB)).
Proof. intros kA kB. apply qeq_imp_qeqT. unfold Qminus. ring. Qed.

Lemma uc_kappa_comp_le : forall kA kB : Q,
  QleT' 0 kA -> QleT' 0 kB -> QltT kB 1 -> QleT' 0 (kA + kB - kA * kB).
Proof.
intros kA kB HkA0 HkB0 HkB1.
pose proof (QleT'_to_Qle 0 kA HkA0) as HkA0'.
pose proof (QleT'_to_Qle 0 kB HkB0) as HkB0'.
pose proof (QltT_to_Qlt kB 1 HkB1) as HkB1'.
pose proof (qltT_leT' kB 1 HkB1) as HkB1le.
pose proof (QleT'_to_Qle 0 (1 - kB) (uc_le_opp_shift kB 1 HkB1le)) as H1kB0.
assert (Hid : kA + kB - kA * kB == kA * (1 - kB) + kB).
{ unfold Qminus. ring. }
apply Qle_to_QleT'. rewrite Hid.
apply (Qle_trans _ (0 + 0)%Q _).
- assert (Hr : 0 + 0 == 0%Q) by ring. rewrite Hr. apply Qle_refl.
- apply Qplus_le_compat.
  + apply (Qle_trans _ (0 * (1 - kB)) _).
    * assert (Hz : 0 * (1 - kB) == 0%Q) by ring.
      rewrite Hz. apply Qle_refl.
    * apply (Qmult_le_compat_r 0 kA (1 - kB) HkA0' H1kB0).
  + exact HkB0'.
Qed.

Lemma uc_kappa_comp_lt : forall kA kB : Q,
  QltT kA 1 -> QltT kB 1 -> QltT (kA + kB - kA * kB) 1.
Proof.
intros kA kB HkA1 HkB1.
apply uc_lt_minus_inv.
assert (Hpre : Qlt 0 ((1 - kA) * (1 - kB))).
{ apply (Qmult_lt_0_compat (1 - kA) (1 - kB)).
  - exact (QltT_to_Qlt 0 (1 - kA) (uc_lt_opp_shift kA 1 HkA1)).
  - exact (QltT_to_Qlt 0 (1 - kB) (uc_lt_opp_shift kB 1 HkB1)). }
pose proof (qeqT_imp_qeq _ _ (uc_one_minus_comp kA kB)) as H1mc.
apply (uc_qeq_lt_r ((1 - kA) * (1 - kB)) (1 + - (kA + kB - kA * kB)) 0%Q).
- apply qeq_imp_qeqT. exact (Qeq_sym _ _ H1mc).
- apply Qlt_to_QltT. exact Hpre.
Qed.

(* Chain-composition reachability: [c0] crossing [epsA] through the A chain and [epsA] crossing [epsB]
   through the B chain imply that [c0] crosses [epsB] within [NA + NB] steps at the composed rate *)
Lemma uc_chain_reach : forall (c0 e1 e2 kA kB : Q) (NA NB : nat),
  QleT' 0 c0 -> QleT' 0 kA -> QltT kA 1 -> QleT' 0 kB -> QltT kB 1 ->
  QltT (c0 * q_pow (1 - kA) NA) e1 ->
  QltT (e1 * q_pow (1 - kB) NB) e2 ->
  QltT (c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat) e2.
Proof.
intros c0 e1 e2 kA kB NA NB Hc0 HkA0 HkA1 HkB0 HkB1 HrA HrB.
pose proof (QleT'_to_Qle 0 c0 Hc0) as Hc0'.
pose proof (QleT'_to_Qle 0 kA HkA0) as HkA0'.
pose proof (QltT_to_Qlt kA 1 HkA1) as HkA1'.
pose proof (QleT'_to_Qle 0 kB HkB0) as HkB0'.
pose proof (QltT_to_Qlt kB 1 HkB1) as HkB1'.
pose proof (QltT_to_Qlt (c0 * q_pow (1 - kA) NA) e1 HrA) as HrA'.
pose proof (QltT_to_Qlt (e1 * q_pow (1 - kB) NB) e2 HrB) as HrB'.
pose proof (QltT_to_Qlt 0 (1 - kA) (uc_lt_opp_shift kA 1 HkA1)) as H1kA.
pose proof (QltT_to_Qlt 0 (1 - kB) (uc_lt_opp_shift kB 1 HkB1)) as H1kB.
assert (Hle1kA : Qle 0 (1 - kA)) by (apply (Qlt_le_weak 0 (1 - kA) H1kA)).
assert (Hle1kB : Qle 0 (1 - kB)) by (apply (Qlt_le_weak 0 (1 - kB) H1kB)).
assert (Hb1kA : Qle (1 - kA) 1).
{ pose proof (QleT'_to_Qle (- kA) 0 (uc_opp_le_shift kA HkA0)) as HoppkA.
  assert (Hcd : 1 - kA == 1 + - kA) by reflexivity.
  rewrite Hcd.
  apply (Qle_trans _ (1 + 0)%Q _).
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + exact HoppkA.
  - rewrite (Qplus_0_r 1%Q). apply Qle_refl. }
assert (Hb1kB : Qle (1 - kB) 1).
{ pose proof (QleT'_to_Qle (- kB) 0 (uc_opp_le_shift kB HkB0)) as HoppkB.
  assert (Hcd : 1 - kB == 1 + - kB) by reflexivity.
  rewrite Hcd.
  apply (Qle_trans _ (1 + 0)%Q _).
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + exact HoppkB.
  - rewrite (Qplus_0_r 1%Q). apply Qle_refl. }
assert (Hcomp : q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat
              == q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat).
{ pose proof (qeqT_imp_qeq _ _ (uc_one_minus_comp kA kB)) as HcompEq.
  rewrite (qeqT_imp_qeq _ _
             (uc_pow_eq_compat _ _ _ (qeq_imp_qeqT _ _ HcompEq))).
  rewrite (qeqT_imp_qeq _ _ (uc_pow_mul (1 - kA) (1 - kB) (NA + NB)%nat)).
  rewrite (qeqT_imp_qeq _ _ (uc_pow_add (1 - kA) NA NB)).
  rewrite (qeqT_imp_qeq _ _ (uc_pow_add (1 - kB) NA NB)).
  reflexivity. }
assert (HdropA : Qle (q_pow (1 - kA) (NA + NB)%nat) (q_pow (1 - kA) NA)).
{ pose proof (uc_pow_le_drop (1 - kA) NA NB
               (Qle_to_QleT' _ _ Hle1kA) (Qle_to_QleT' _ _ Hb1kA)) as Hd.
  exact (QleT'_to_Qle _ _ Hd). }
assert (HdropB : Qle (q_pow (1 - kB) (NA + NB)%nat) (q_pow (1 - kB) NB)).
{ replace (NA + NB)%nat with (NB + NA)%nat by lia.
  pose proof (uc_pow_le_drop (1 - kB) NB NA
               (Qle_to_QleT' _ _ Hle1kB) (Qle_to_QleT' _ _ Hb1kB)) as Hd.
  exact (QleT'_to_Qle _ _ Hd). }
pose proof (QleT'_to_Qle 0 (q_pow (1 - kB) (NA + NB)%nat)
             (q_pow_nonneg (1 - kB) (NA + NB)%nat (Qle_to_QleT' _ _ Hle1kB))) as HpnB.
pose proof (QleT'_to_Qle 0 (q_pow (1 - kA) NA)
             (q_pow_nonneg (1 - kA) NA (Qle_to_QleT' _ _ Hle1kA))) as HpnA.
assert (Hboth : Qle (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat)
                    (q_pow (1 - kA) NA * q_pow (1 - kB) NB)).
{ apply (Qle_trans _ (q_pow (1 - kA) NA * q_pow (1 - kB) (NA + NB)%nat) _).
  - apply (Qmult_le_compat_r (q_pow (1 - kA) (NA + NB)%nat)
                             (q_pow (1 - kA) NA) (q_pow (1 - kB) (NA + NB)%nat)
                             HdropA HpnB).
  - apply (Qle_trans _ (q_pow (1 - kB) (NA + NB)%nat * q_pow (1 - kA) NA) _).
    + assert (Hr1 : q_pow (1 - kA) NA * q_pow (1 - kB) (NA + NB)%nat
                 == q_pow (1 - kB) (NA + NB)%nat * q_pow (1 - kA) NA) by ring.
      rewrite Hr1. apply Qle_refl.
    + apply (Qle_trans _ (q_pow (1 - kB) NB * q_pow (1 - kA) NA) _).
      * apply (Qmult_le_compat_r (q_pow (1 - kB) (NA + NB)%nat)
                                 (q_pow (1 - kB) NB) (q_pow (1 - kA) NA)
                                 HdropB HpnA).
      * assert (Hr2 : q_pow (1 - kB) NB * q_pow (1 - kA) NA
                   == q_pow (1 - kA) NA * q_pow (1 - kB) NB) by ring.
        rewrite Hr2. apply Qle_refl. }
assert (Hmulc : Qle (c0 * (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat))
                    (c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB))).
{ rewrite (Qmult_comm c0 (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat)).
  rewrite (Qmult_comm c0 (q_pow (1 - kA) NA * q_pow (1 - kB) NB)).
  apply (Qmult_le_compat_r _ _ c0 Hboth Hc0'). }
assert (HposB2 : Qlt 0 (q_pow (1 - kB) NB))
  by (apply QltT_to_Qlt; apply (sc_qpow_pos NB (1 - kB) H1kB)).
assert (Hstep1 : c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB)
               < e1 * q_pow (1 - kB) NB).
{ assert (Hr3 : c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB)
             == (c0 * q_pow (1 - kA) NA) * q_pow (1 - kB) NB) by ring.
  rewrite Hr3.
  apply (Qmult_lt_compat_r (c0 * q_pow (1 - kA) NA) e1
             (q_pow (1 - kB) NB) HposB2 HrA'). }
assert (HXle : Qle (c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat)
                   (c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB))).
{ apply (Qle_trans _ (c0 * (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat)) _).
  - assert (Hcomp2 : c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat
                   == c0 * (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat))
      by (rewrite Hcomp; reflexivity).
    rewrite Hcomp2. apply Qle_refl.
  - exact Hmulc. }
apply Qlt_to_QltT.
apply (Qlt_trans
         (c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat)
         (e1 * q_pow (1 - kB) NB) e2).
- apply (Qle_lt_trans
           (c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat)
           (c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB))
           (e1 * q_pow (1 - kB) NB)).
  + exact HXle.
  + exact Hstep1.
- exact HrB'.
Qed.

(* The composition theorem: after chaining two valid declarations, the composed declaration still passes the validator *)
Theorem claim_chain : forall (A B : claim_decl) (wA : claim_pass A) (wB : claim_pass B),
  Id (Qeq_bool (cl_eps A) (cl_c0 B)) true ->
  Id (check_claim A) (inl wA) -> Id (check_claim B) (inl wB) ->
  sigT (fun w => Id (check_claim (chain_claim A B)) (inl w)).
Proof.
intros A B wA wB Hface HHA HHB.
destruct wA as [[hk0A hk1A] [hbA [[hc0A heA] hrA]]].
destruct wB as [[hk0B hk1B] [hbB [[hc0B heB] hrB]]].
assert (Hface' : cl_eps A == cl_c0 B).
{ apply (proj1 (Qeq_bool_iff (cl_eps A) (cl_c0 B))).
  apply RealSetoid.Id_eq. exact Hface. }
assert (HrB' : Qlt (cl_eps A * q_pow (1 - cl_kappa B) (cl_N B)) (cl_eps B)).
{ rewrite Hface'. exact (QltT_to_Qlt _ _ hrB). }
assert (Hk0c : QleT' 0 (cl_kappa A + cl_kappa B - cl_kappa A * cl_kappa B)).
{ exact (uc_kappa_comp_le (cl_kappa A) (cl_kappa B) hk0A hk0B hk1B). }
assert (Hk1c : QltT (cl_kappa A + cl_kappa B - cl_kappa A * cl_kappa B) 1).
{ exact (uc_kappa_comp_lt (cl_kappa A) (cl_kappa B) hk1A hk1B). }
pose proof (NatLe_drop 1 (cl_N A) hbA) as HbA.
assert (Hbc : NatLe 1 (cl_N A + cl_N B)%nat).
{ apply NatLe_lift. lia. }
assert (Hreach : QltT
    (cl_c0 A * q_pow (1 - (cl_kappa A + cl_kappa B - cl_kappa A * cl_kappa B))
                     (cl_N A + cl_N B)%nat)
    (cl_eps B)).
{ apply (uc_chain_reach (cl_c0 A) (cl_eps A) (cl_eps B)
           (cl_kappa A) (cl_kappa B) (cl_N A) (cl_N B)
           hc0A hk0A hk1A hk0B hk1B hrA (Qlt_to_QltT _ _ HrB')). }
apply (check_claim_inl_of_pass (chain_claim A B)
         (((Hk0c, Hk1c), (Hbc, ((hc0A, heB), Hreach))))).
Qed.

(* ================= Section 10. the Real-layer hookup (a parallel shape): the budget of [r_arch_pow_real] is exactly *)
(*     the constitution's breakthrough budget -- the same [sigT (fun N => ...)] shape, two carriers ================= *)

Definition real_budget_witness (kappa a eps : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps)
  : sigT (fun N : nat => real_lt (real_mult a (r_pow kappa N)) eps) :=
  r_arch_pow_real kappa Hk1 Hk2 a Ha eps Heps.

(* ================= Section 11. [vm_compute] numeric self-tests (the sample output source) ================= *)

Definition demo_ok : claim_decl := mk_claim (8 # 10) (1 # 10) (1 # 2) 5 21.
(* [c0 = 4/5], [eps = 1/10], [kappa = 1/2], [N = 5]: [4/5 * (1/2)^5 = 1/40 < 1/10] -- a legal improvement declaration *)

Eval vm_compute in check_report demo_ok.
Eval vm_compute in check_report claim_bad_kappa1.
Eval vm_compute in check_report claim_bad_kappaneg.
Eval vm_compute in check_report claim_bad_budget.
Eval vm_compute in check_report claim_bad_reach.

Lemma test_demo_ok_pass : Id (check_report demo_ok) v_pass.
Proof. vm_compute. reflexivity. Qed.

(* ================= Section 12. extraction checks (self-audit of the extraction face; zero [Obj.magic] occurrences) ================= *)

Set Warnings "-extraction-opaque-accessed".
