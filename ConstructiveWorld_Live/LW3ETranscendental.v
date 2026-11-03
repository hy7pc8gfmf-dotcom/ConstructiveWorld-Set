(* ========================================================================= *)
(* LW3ETranscendental - M3-C1 chief seat: the final-statement assembly layer  *)
(* for constructive transcendence of e.                                      *)
(* 模块名：LW3ETranscendental.  数学使命：given a nonzero integer            *)
(* coefficient polynomial p (Set-level explicit witness lw3_nz), assemble    *)
(* the evaluation of p at the constructive constant e and the Hermite        *)
(* integer-functional chain that carries its explicit lower-bound witness.   *)
(* 路线裁决：consume the M2 offerings verbatim, do not re-derive any         *)
(* Hermite identity: LW1ZPoly zpoly/eval_Z ring-hom exit, LW0QPoly Q-eval    *)
(* hom laws, LW2Hermite lw2_lambda/lw2_hermite_identity + lw2i integrality   *)
(* machine, LW2IntegMachine e^{-t} endpoint functional.  The M2 closing      *)
(* reconciliation named exactly one hard gap for this seat: the zpoly ring   *)
(* hom new file with its consistency bridge to QPoly — closed in Section 3.  *)
(* The second gap found by direct survey: the integrality closure of         *)
(* lw2i_intpoly under product (needed to build integer-coefficient Hermite   *)
(* integrands from p) — closed in Section 5; the integer Hermite integrand   *)
(* lw3_fbuild and its integer functional value lw3_K close Section 6.        *)
(* 依赖清单：S01_BaseRing (And/NatLe Set layer), S02_CauchyComplete          *)
(* (Real/real_lt/real_plus/real_mult/real_const/real_one), S03_QExp          *)
(* (cauchy_real_exp), LW0QPoly, LW1ZPoly, LW2Hermite, LW2IntegMachine;      *)
(* Stdlib QArith/Lia/Arith/ZArith.  LW0Endpoint stays outside this Require   *)
(* closure on purpose (same recipe as LW2IntegMachine).                      *)
(* 构造性注记：every statement is Set-sorted (sigT / Set-level And / Qeq /   *)
(* real_lt); the nonzero witness lw3_nz is decidable-comparison data, no     *)
(* negation anywhere; structurally recursive Fixpoints only; 编译配方：      *)
(* env COQLIB/ROCQLIB to the Rocq 9.1 library; coqc.exe -q -Q . "".          *)
(* 对标行：Hermite 1873 closing chapter; work order M3-C1 (2026-09).         *)
(* ========================================================================= *)

From Stdlib Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith_base.
From Stdlib Require Import QArith.Qabs.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW1ZPoly.
Require Import LW2Hermite.
Require Import LW2IntegMachine.
(* 终语句四项续装复用面（模块 140）：LW0FactGrowth 供阶乘压制定量（①），  *)
(* LW2UpperBound 供 Hermite 泛函上界系（②，模块 106 复核 PASS 正本       *)
(* 2445e252 沙箱同源先行绿）。                                          *)
Require Import LW0FactGrowth.
Require Import LW2UpperBound.
(* 终语句四项续装复用面：LW2NivenInt 供 Niven 源头多项式的首项         *)
(* 系数闭式（首项 =(−1)^n·b^n，b≠0 即非零），为 K≠0 见证生产件.        *)
Require Import LW2NivenInt.

(* ------------------------------------------------------------------ *)
(* Section 1.  The Set-level nonzero witness on zpoly.                 *)
(* ------------------------------------------------------------------ *)

(* A nonzero witness is an explicit index whose coefficient compares     *)
(* nonzero in the decidable Z order.  Both branches are Set-sorted data  *)
(* (Empty_set / unit), so lw3_nz : zpoly -> Set carries no proposition.  *)
Definition lw3_nz (p : zpoly) : Set :=
  sigT (fun i : nat =>
    match Z.compare (nth i p 0%Z) 0%Z with
    | Datatypes.Eq => Empty_set
    | _ => unit
    end).

(* Every witness indeed points at a coefficient that is nonzero; this is *)
(* the consumption contract used downstream.                             *)
Lemma lw3_nz_spec : forall (p : zpoly) (w : lw3_nz p),
  (nth (projT1 w) p 0%Z) <> 0%Z.
Proof.
  intros p w. destruct w as [i Hc]. cbn [projT1] in Hc. cbn [projT1].
  destruct (Z.compare (nth i p 0%Z) 0%Z) eqn:Hcmp.
  - destruct Hc.
  - intro Hz. rewrite Hz in Hcmp.
    rewrite Z.compare_refl in Hcmp. discriminate Hcmp.
  - intro Hz. rewrite Hz in Hcmp.
    rewrite Z.compare_refl in Hcmp. discriminate Hcmp.
Qed.

(* The zero polynomial admits no witness (decidable exhaustion). *)
Lemma lw3_nz_nil : lw3_nz nil -> Id 0%Z 1%Z.
Proof.
  intros w. destruct w as [i Hc].
  destruct i as [|i']; cbn [nth] in Hc;
    destruct (Z.compare 0%Z 0%Z) eqn:Hcmp.
  - destruct Hc.
  - discriminate Hcmp.
  - discriminate Hcmp.
  - destruct Hc.
  - discriminate Hcmp.
  - discriminate Hcmp.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 2.  The lift zpoly -> QPoly and the Z-exit consistency.     *)
(* ------------------------------------------------------------------ *)

(* Coefficient-wise embedding of an integer polynomial into QPoly. *)
Definition lw3_lift (p : zpoly) : QPoly := map (fun a : Z => (a # 1)%Q) p.

Lemma lw3_lift_cons : forall (a : Z) (p : zpoly),
  Id (lw3_lift (cons a p)) (cons ((a # 1)%Q) (lw3_lift p)).
Proof. intros a p. apply id_refl. Qed.

(* The consistency bridge demanded by the M2 reconciliation: the lift    *)
(* evaluates over Q at the rational image of an integer point exactly to *)
(* the integer value produced by the LW1 ring-hom exit.                  *)
Lemma lw3_lift_eval_Z : forall (p : zpoly) (z : Z),
  QeqT (qpoly_eval (lw3_lift p) ((z # 1)%Q)) ((zpoly_eval_Z p z) # 1)%Q.
Proof.
  induction p as [|a p' IH]; intros z.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. rewrite lw3_lift_cons.
    unfold zpoly_eval_Z; cbn [zpoly_eval_go].
    rewrite (zpoly_eval_go_pow p' z (z * 1)%Z).
    cbn [qpoly_eval].
    rewrite (qeqT_imp_qeq _ _ (IH z)).
    rewrite (qeqT_imp_qeq _ _ (lw2i_qmake_mul z (zpoly_eval_Z p' z))).
    rewrite (qeqT_imp_qeq _ _ (lw2_qmake_add a (z * zpoly_eval_Z p' z)%Z)).
    change (zpoly_eval_go z 1 p') with (zpoly_eval_Z p' z).
    unfold Qeq; cbn [Qnum Qden]; lia.
Qed.

(* The lift carries explicit integer coefficient witnesses: this is the  *)
(* entry ticket into the M2 integrality machine lw2i_*.                  *)
Lemma lw3_lift_intpoly : forall p : zpoly, lw2i_intpoly (lw3_lift p).
Proof.
  induction p as [|a p' IH].
  - intros i. exists 0%Z. reflexivity.
  - intros i. destruct i as [|i'].
    + exists a. apply qeq_imp_qeqT. apply Qeq_refl.
    + exact (IH i').
Qed.

(* ------------------------------------------------------------------ *)
(* Section 3.  Grouped Q-evaluation hom exit (Set-level packaging).    *)
(* ------------------------------------------------------------------ *)

(* One grouped exit in the LW1 zpoly_eval_Z_ring_hom packaging shape,    *)
(* every conjunct discharged by exact reference to a verified LW0QPoly   *)
(* law, carried over the Set-level product And.                         *)
Lemma lw3_qeval_ring_hom : forall (u v : QPoly) (c x : Q),
  And (QeqT (qpoly_eval (qpoly_add u v) x) (qpoly_eval u x + qpoly_eval v x))
      (And (QeqT (qpoly_eval (qpoly_mul u v) x) (qpoly_eval u x * qpoly_eval v x))
           (QeqT (qpoly_eval (qpoly_scalar c u) x) (c * qpoly_eval u x))).
Proof.
  intros u v c x.
  split.
  - exact (qeq_imp_qeqT _ _ (qpoly_eval_add u v x)).
  - split.
    + exact (qeq_imp_qeqT _ _ (qpoly_eval_mul u v x)).
    + exact (qeq_imp_qeqT _ _ (qpoly_eval_scalar c u x)).
Qed.

(* ------------------------------------------------------------------ *)
(* Section 4.  The Real layer: the constant e and Real evaluation.     *)
(* ------------------------------------------------------------------ *)

(* The constructive e: the Cauchy-real exponential at one. *)
Definition lw3_e : Real := cauchy_real_exp real_one.

(* Real-layer polynomial evaluation: the ascending-power fold over the   *)
(* S02 real operations; totality is inherited from the Real closure, no  *)
(* continuity argument is ever discharged by hand.                       *)
Fixpoint lw3_evalr_go (z pow : Real) (p : zpoly) : Real :=
  match p with
  | nil => real_zero
  | cons a p' =>
      real_plus (real_mult (real_const ((a # 1)%Q)) pow)
                (lw3_evalr_go z (real_mult z pow) p')
  end.

Definition lw3_evalr (p : zpoly) (x : Real) : Real := lw3_evalr_go x real_one p.

Lemma lw3_evalr_nil : forall z pow, real_eq (lw3_evalr_go z pow nil) real_zero.
Proof. intros z pow. exact (real_eq_refl real_zero). Qed.

(* The evaluation of the zero polynomial at e is zero in the Real layer. *)
Lemma lw3_evalr_zero : real_eq (lw3_evalr nil lw3_e) real_zero.
Proof. exact (real_eq_refl real_zero). Qed.

(* ------------------------------------------------------------------ *)
(* Section 5.  Integrality closure: sum, integer scalar, cons-shift,   *)
(* product — the surveyed gap in the M2 integrality machine.           *)
(* ------------------------------------------------------------------ *)

Fixpoint lw3_qpow (f : QPoly) (n : nat) : QPoly :=
  match n with
  | 0%nat => cons (1 # 1)%Q nil
  | Datatypes.S m => qpoly_mul f (lw3_qpow f m)
  end.

Lemma lw3_intpoly_add : forall u v : QPoly,
  lw2i_intpoly u -> lw2i_intpoly v -> lw2i_intpoly (qpoly_add u v).
Proof.
  intros u v Hu Hv i.
  destruct (Hu i) as [zu Hzu].
  destruct (Hv i) as [zv Hzv].
  exists (zu + zv)%Z.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (lw0_coef_add u v i)).
  rewrite (qeqT_imp_qeq _ _ Hzu), (qeqT_imp_qeq _ _ Hzv).
  exact (qeqT_imp_qeq _ _ (lw2_qmake_add zu zv)).
Qed.

(* Generalized integer-ratio scalar closure: the scalar may be any Q     *)
(* that carries an explicit integer witness (constant over indices).     *)
Lemma lw3_intpoly_scalar_gen : forall (c : Q) (f : QPoly),
  (forall i : nat, sigT (fun z : Z => QeqT c ((z # 1)%Q))) ->
  lw2i_intpoly f -> lw2i_intpoly (qpoly_scalar c f).
Proof.
  intros c f Hc Hf i.
  destruct (Hc 0%nat) as [zc Hzc].
  destruct (Hf i) as [z Hz].
  exists (zc * z)%Z.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (lw0_coef_scalar c f i)).
  rewrite (qeqT_imp_qeq _ _ Hzc), (qeqT_imp_qeq _ _ Hz).
  exact (qeqT_imp_qeq _ _ (lw2i_qmake_mul zc z)).
Qed.

Lemma lw3_intpoly_scalar : forall (c : Z) (f : QPoly),
  lw2i_intpoly f -> lw2i_intpoly (qpoly_scalar ((c # 1)%Q) f).
Proof.
  intros c f Hf. apply lw3_intpoly_scalar_gen.
  - intros i. exists c. apply qeq_imp_qeqT. apply Qeq_refl.
  - exact Hf.
Qed.

(* Shifting a list by one zero coefficient preserves integrality: this   *)
(* is the t-multiplication step of the product recursion.                *)
Lemma lw3_intpoly_cons0 : forall l : QPoly,
  lw2i_intpoly l -> lw2i_intpoly (cons 0%Q l).
Proof.
  intros l Hl i. destruct i as [|i'].
  - exists 0%Z. reflexivity.
  - exact (Hl i').
Qed.

(* The product closure: coefficients of a product are integer           *)
(* combinations of integer coefficients, by structural induction on the *)
(* first factor along the LW0QPoly product recursion shape.             *)
Lemma lw3_intpoly_mul : forall u v : QPoly,
  lw2i_intpoly u -> lw2i_intpoly v -> lw2i_intpoly (qpoly_mul u v).
Proof.
  intros u. induction u as [|a u' IH]; intros v Hu Hv.
  - intros i. exists 0%Z. reflexivity.
  - cbn [qpoly_mul].
    apply lw3_intpoly_add.
    + apply lw3_intpoly_scalar_gen.
      * intros i. exact (Hu 0%nat).
      * exact Hv.
    + apply lw3_intpoly_cons0.
      apply IH.
      * intros i. destruct (Hu (Datatypes.S i)) as [z Hz].
        exists z. exact Hz.
      * exact Hv.
Qed.

(* Iterated products stay integral. *)
Lemma lw3_intpoly_qpow : forall (f : QPoly) (n : nat),
  lw2i_intpoly f -> lw2i_intpoly (lw3_qpow f n).
Proof.
  intros f n Hf. induction n as [|m IH].
  - intros i. destruct i as [|i'].
    + exists 1%Z. reflexivity.
    + exists 0%Z. reflexivity.
  - cbn [lw3_qpow]. apply lw3_intpoly_mul.
    + exact Hf.
    + exact IH.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 6.  The integer Hermite integrand and its integer value.    *)
(* ------------------------------------------------------------------ *)

Fixpoint lw3_tpow (sg : nat) : QPoly :=
  match sg with
  | 0%nat => cons (1 # 1)%Q nil
  | Datatypes.S m => cons 0%Q (lw3_tpow m)
  end.

(* The Hermite integrand with integer coefficients: t^sigma * p(t)^N.   *)
(* The classical 1/(N-1)! suppression factor is carried by the caller   *)
(* at the bound stage, never inside the integrand, so the M2 integrality *)
(* machine consumes it verbatim.                                        *)
Definition lw3_fbuild (p : zpoly) (sg N : nat) : QPoly :=
  qpoly_mul (lw3_tpow sg) (lw3_qpow (lw3_lift p) N).

Lemma lw3_tpow_intpoly : forall sg : nat, lw2i_intpoly (lw3_tpow sg).
Proof.
  induction sg as [|m IH].
  - intros i. destruct i as [|i'].
    + exists 1%Z. reflexivity.
    + exists 0%Z. reflexivity.
  - intros i. cbn [lw3_tpow]. destruct i as [|i'].
    + exists 0%Z. reflexivity.
    + exact (IH i').
Qed.

Lemma lw3_fbuild_intpoly : forall (p : zpoly) (sg N : nat),
  lw2i_intpoly (lw3_fbuild p sg N).
Proof.
  intros p sg N.
  unfold lw3_fbuild.
  apply lw3_intpoly_mul.
  - apply lw3_tpow_intpoly.
  - apply lw3_intpoly_qpow.
    apply lw3_lift_intpoly.
Qed.

(* The integer functional value attached to the integrand: the M2       *)
(* integer lambda, consumed verbatim (lw2i_lambda_integer).             *)
Definition lw3_K (p : zpoly) (sg N n : nat) : Z :=
  match lw2i_lambda_integer n (lw3_fbuild p sg N) (lw3_fbuild_intpoly p sg N) with
  | existT _ w _ => w
  end.

Lemma lw3_K_spec : forall (p : zpoly) (sg N n : nat),
  QeqT (lw2_lambda n (lw3_fbuild p sg N)) ((lw3_K p sg N n) # 1)%Q.
Proof.
  intros p sg N n.
  unfold lw3_K.
  destruct (lw2i_lambda_integer n (lw3_fbuild p sg N)
              (lw3_fbuild_intpoly p sg N)) as [w Hw].
  exact Hw.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 8.  终语句四项续装（模块 140）：the quantitative contradiction *)
(* chain for the final statement, per the _tlw131 receipt SS5/SS6 pins.  *)
(* ------------------------------------------------------------------ *)

(* ① 阶 factorial suppression, consumed: the growth of the coefficient    *)
(* data C is swallowed by the double factorial (2N)! as soon as C <= N —  *)
(* the assembly-grade corollary of lw0_fact_lower_growth (div2 (2N)=N).   *)
Lemma lw3_fact_swallows : forall C N : nat, (C <= N)%nat ->
  QleT' (q_pow (lw0_q_of_nat C) N) (q_fact (2 * N)).
Proof.
  intros C N HC.
  apply (qleT'_trans _ (q_pow (lw0_q_of_nat N) N)).
  - apply (lw0_q_pow_mono_base (lw0_q_of_nat C) (lw0_q_of_nat N) N).
    + apply Qle_to_QleT'. unfold lw0_q_of_nat, Qle. cbn [Qnum Qden]. lia.
    + apply Qle_to_QleT'. unfold lw0_q_of_nat, Qle. cbn [Qnum Qden]. lia.
  - apply (lw2u_qleT'_eq_l _ (q_pow (lw0_q_of_nat (Nat.div2 (2 * N)))
                                   (Nat.div2 (2 * N)))).
    + exact (lw0_fact_lower_growth (2 * N)).
    + assert (Hd : Nat.div2 (2 * N) = N) by apply Nat.div2_double.
      rewrite Hd. reflexivity.
Qed.

(* ② Hermite functional upper bound, consumed on the built integrand:    *)
(* the node-count instance of lw2_L_upper_nodes with E caller-chosen,     *)
(* plus both closing members of the family (c_n form and the Zmake        *)
(* integerized exit) at the pi-grade base 10/3.                          *)
Lemma lw3_lambda_upper_fbuild : forall (p : zpoly) (sg N n : nat) (E : Q),
  (forall j k, Nat.le j (Datatypes.S n) -> Nat.lt k (length (lw3_fbuild p sg N)) ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k (lw3_fbuild p sg N))
                             (lw2_node j))) E) ->
  QleT' (Qabs (lw2_lambda n (lw3_fbuild p sg N)))
        (lw0_q_of_nat (Datatypes.S (Datatypes.S n) * length (lw3_fbuild p sg N)) * E).
Proof. intros p sg N n E H. exact (lw2_L_upper_nodes n (lw3_fbuild p sg N) E H). Qed.

Lemma lw3_lambda_upper_fbuild_cn : forall (p : zpoly) (sg N n : nat),
  (forall j k, Nat.le j (Datatypes.S n) -> Nat.lt k (length (lw3_fbuild p sg N)) ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k (lw3_fbuild p sg N)) (lw2_node j)))
           (q_pow (10 # 3) (22 + 2 * n)%nat)) ->
  QleT' (Qabs (lw2_lambda n (lw3_fbuild p sg N)))
        (lw2u_c_n n (length (lw3_fbuild p sg N))).
Proof. intros p sg N n H. exact (lw2_L_upper_hermite n (lw3_fbuild p sg N) H). Qed.

Lemma lw3_lambda_upper_fbuild_zmake : forall (p : zpoly) (sg N n : nat),
  (forall j k, Nat.le j (Datatypes.S n) -> Nat.lt k (length (lw3_fbuild p sg N)) ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k (lw3_fbuild p sg N)) (lw2_node j)))
           (q_pow (10 # 3) (22 + 2 * n)%nat)) ->
  QleT' (Qabs (lw2_lambda n (lw3_fbuild p sg N)))
        (((Z.of_nat (Datatypes.S (Datatypes.S n) * length (lw3_fbuild p sg N)) *
           (10 ^ Z.of_nat (22 + 2 * n))) # 1)%Q).
Proof. intros p sg N n H. exact (lw2_L_upper_hermite_zmake n (lw3_fbuild p sg N) H). Qed.

(* ③ the e^{-X} decay bound, explicit-constant version (work order       *)
(* LW2-C1 infinity-end recipe): the machine-scalar interface carries the  *)
(* factorial-reciprocal constant lw3_decay_E m = 1/(2m)!, which satisfies *)
(* the defining product equation, and ANY scalar E with that equation and *)
(* nonnegativity kills the C-growth factor dead (decay certified against *)
(* the ① suppression): m^m * E <= 1.  The positivity instantiation of     *)
(* lw3_decay_E is the registered remaining witness point (honest gap).    *)
Definition lw3_decay_E (m : nat) : Q := / (q_fact (2 * m))%Q.

Lemma lw3_decay_E_eq : forall m : nat,
  QeqT (q_fact (2 * m) * lw3_decay_E m) ((1 # 1)%Q).
Proof.
  intro m. apply qeq_imp_qeqT. unfold lw3_decay_E. apply Qmult_inv_r.
  intro Hz.
  assert (Hpos : Qlt 0%Q (q_fact (2 * m)))
    by exact (QltT_to_Qlt _ _ (q_fact_pos (2 * m))).
  apply (Qlt_not_eq 0%Q (q_fact (2 * m)) Hpos).
  exact (Qeq_sym _ _ Hz).
Qed.

Lemma lw3_decay_kills : forall (m : nat) (E : Q),
  q_fact (2 * m) * E == (1 # 1)%Q -> QleT' 0 E ->
  QleT' (q_pow (lw0_q_of_nat m) m * E) ((1 # 1)%Q).
Proof.
  intros m E HE H0E. apply Qle_to_QleT'.
  rewrite <- HE. apply Qmult_le_compat_r.
  - apply QleT'_to_Qle. apply lw3_fact_swallows. lia.
  - exact (QleT'_to_Qle _ _ H0E).
Qed.

(* ④ node-count instantiation: sg := deg p (length form), nodes          *)
(* n := sg + N * sg, and the instantiated integer functional value       *)
(* lw3_Kinst p N with its lambda-spec bridge; the Set-level gate         *)
(* collapses any integer trapped strictly inside (0,1) — the numerical   *)
(* half of the final contradiction, consumed by the apartness exit at    *)
(* the M0 master-statement assembly.                                     *)
Definition lw3_deg (p : zpoly) : nat := length p.

Definition lw3_nodecount (p : zpoly) (N : nat) : nat :=
  lw3_deg p + N * lw3_deg p.

Definition lw3_Kinst (p : zpoly) (N : nat) : Z :=
  lw3_K p (lw3_deg p) N (lw3_nodecount p N).

Lemma lw3_Kinst_spec : forall (p : zpoly) (N : nat),
  QeqT (lw2_lambda (lw3_nodecount p N) (lw3_fbuild p (lw3_deg p) N))
    ((lw3_Kinst p N) # 1)%Q.
Proof. intros p N. unfold lw3_Kinst. apply lw3_K_spec. Qed.

(* The Set-level contradiction gate: an integer with an explicit nonzero *)
(* witness cannot have absolute value strictly below one.                *)
Lemma lw3_gate : forall z : Z,
  z <> 0%Z -> QltT (Qabs (z # 1)%Q) (1 # 1)%Q -> Id 0%Z 1%Z.
Proof.
  intros z Hnz Hlt. apply QltT_to_Qlt in Hlt.
  unfold Qabs, Qlt in Hlt. cbn [Qnum Qden] in Hlt.
  exfalso. lia.
Qed.

Theorem lw3_Kinst_gate : forall (p : zpoly) (N : nat),
  lw3_Kinst p N <> 0%Z ->
  QltT (Qabs ((lw3_Kinst p N) # 1)%Q) (1 # 1)%Q -> Id 0%Z 1%Z.
Proof. intros p N Hnz Hlt. apply (lw3_gate (lw3_Kinst p N) Hnz Hlt). Qed.

(* ------------------------------------------------------------------ *)
(* Section 9.  终语句四件续装：decay 正性实例、K≠0 见证生产             *)
(* （Niven 首项复用）、p-尺度逐节点界、apartness 出口.                  *)
(* ------------------------------------------------------------------ *)

(* ① Q 倒数正性，make 字形逐支枚举（库面 Qinv_pos 为 make 交换恒等形，  *)
(* 非正性律，故按枚举自建；正分母支由 positive 的 zify 正性闭合）.       *)
Lemma lw3_Qinv_pos : forall (a : Z) (d : positive),
  (0 < a)%Z -> QltT 0 (/ (a # d)%Q).
Proof.
  intros a d H. apply Qlt_to_QltT. unfold Qlt.
  destruct a; cbn [Qinv Qnum Qden].
  - lia.
  - lia.
  - lia.
Qed.

(* ① 阶乘有理像正性：1 ≤ q_fact n（lw0_q_fact_ge_one）经 <≤ 传递.       *)
Lemma lw3_qfact_pos : forall n : nat, QltT 0 (q_fact n).
Proof.
  intro n. apply Qlt_to_QltT. apply (Qlt_le_trans 0%Q 1%Q).
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - exact (QleT'_to_Qle 1%Q (q_fact n) (lw0_q_fact_ge_one n)).
Qed.

(* ① decay 常数三形正性：Qlt（Prop 面）、QleT'（lw3_decay_kills 复用    *)
(* 形）、QltT（Set 面严格形），常数面实例 m^m·(1/(2m)!) ≤ 1.             *)
Lemma lw3_decay_E_pos : forall m : nat, QltT 0 (lw3_decay_E m).
Proof.
  intro m. unfold lw3_decay_E.
  assert (Hpos : Qlt 0%Q (q_fact (2 * m)))
    by exact (QltT_to_Qlt _ _ (lw3_qfact_pos (2 * m))).
  destruct (q_fact (2 * m)) as [a d] eqn:Hq.
  unfold Qlt in Hpos. cbn [Qnum Qden] in Hpos.
  apply (lw3_Qinv_pos a d).
  lia.
Qed.

Lemma lw3_decay_E_nonneg : forall m : nat, QleT' 0 (lw3_decay_E m).
Proof.
  intro m. apply Qle_to_QleT'. apply Qlt_le_weak.
  exact (QltT_to_Qlt _ _ (lw3_decay_E_pos m)).
Qed.

Lemma lw3_decay_E_posT : forall m : nat, QltT 0 (lw3_decay_E m).
Proof.
  intro m. exact (lw3_decay_E_pos m).
Qed.

Lemma lw3_decay_kills_inst : forall m : nat,
  QleT' (q_pow (lw0_q_of_nat m) m * lw3_decay_E m) ((1 # 1)%Q).
Proof.
  intro m.
  exact (lw3_decay_kills m (lw3_decay_E m) (qeqT_imp_qeq _ _ (lw3_decay_E_eq m))
           (lw3_decay_E_nonneg m)).
Qed.

(* ② Set 级 Q 非零见证（Qeq_bool 可判定比较数据，两支均 Set 排序——     *)
(* lw3_nz 同款枚举形在单有理数上的像）.                                  *)
Definition lw3_qnz (q : Q) : Set :=
  match Qeq_bool q 0%Q with
  | true => Empty_set
  | false => unit
  end.

(* ② K≠0 见证生产第一件：Niven 源头多项式首项系数的非零见证.            *)
(* 复用 lw2_niven_f_lc_closed（首项 =(−1)^n·b^n 闭式）：幂非零两件      *)
(* （(−1)^n≠0 直接判别、b^n≠0 由 b≠0 保幂）乘积非零闭合，纯 Z 判定面.   *)
Theorem lw3_niven_lc_nz : forall (a b : Z) (n : nat),
  b <> 0%Z -> lw3_qnz (lw0_coef (n + n) (lw2_niven_int_f a b n)).
Proof.
  intros a b n Hb. unfold lw3_qnz.
  destruct (Qeq_bool (lw0_coef (n + n) (lw2_niven_int_f a b n)) 0%Q) eqn:Hqb.
  - apply Qeq_bool_eq in Hqb.
    rewrite (qeqT_imp_qeq _ _ (lw2_niven_f_lc_closed a b n)) in Hqb.
    assert (Hs : (Z.pow (-1)%Z (Z.of_nat n) <> 0%Z)).
    { apply Z.pow_nonzero; [ intro Hz; discriminate Hz | apply Nat2Z.is_nonneg ]. }
    assert (Hp : (Z.pow b (Z.of_nat n) <> 0%Z)).
    { apply Z.pow_nonzero; [ exact Hb | apply Nat2Z.is_nonneg ]. }
    assert (Hm : ((Z.pow (-1)%Z (Z.of_nat n) * Z.pow b (Z.of_nat n))%Z <> 0%Z)).
    { intro Hz. apply Z.mul_eq_0 in Hz.
      destruct Hz as [Hc|Hc].
      - destruct (Hs Hc).
      - destruct (Hp Hc). }
    unfold Qeq in Hqb. cbn [Qnum Qden] in Hqb.
    repeat rewrite Z.mul_1_r in Hqb.
    destruct (Hm Hqb).
  - exact tt.
Qed.

(* ④ apartness 出口（M0 步6/7 同款矛盾复用工艺）：0<|K|<1 两端入闸，    *)
(* lw3_Kinst_gate 合拢 (0=1)%Z 后经判别消除构造性导出 Set 级分离见证     *)
(* （库内 apart 谓词以「正常数 c＋real_lt＋real_metric」模式实现，       *)
(* 沿模块 138 对照形）.                                                  *)
Theorem lw3_e_trans_exit : forall (p : zpoly) (N : nat),
  lw3_Kinst p N <> 0%Z ->
  QltT (Qabs ((lw3_Kinst p N) # 1)%Q) (1 # 1)%Q ->
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c) (real_metric (lw3_evalr p lw3_e) real_zero))).
Proof.
  intros p N Hnz Hlt.
  assert (H01 : Id 0%Z 1%Z) by exact (lw3_Kinst_gate p N Hnz Hlt).
  inversion H01.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 7.  Extraction probe and assumption checks.                 *)
(* ------------------------------------------------------------------ *)

Print Assumptions lw3_nz_spec.
Print Assumptions lw3_lift_eval_Z.
Print Assumptions lw3_lift_intpoly.
Print Assumptions lw3_qeval_ring_hom.
Print Assumptions lw3_intpoly_mul.
Print Assumptions lw3_fbuild_intpoly.
Print Assumptions lw3_K_spec.
Print Assumptions lw3_fact_swallows.
Print Assumptions lw3_lambda_upper_fbuild_zmake.
Print Assumptions lw3_decay_kills.
Print Assumptions lw3_Kinst_spec.
Print Assumptions lw3_Kinst_gate.
Print Assumptions lw3_Qinv_pos.
Print Assumptions lw3_qfact_pos.
Print Assumptions lw3_decay_E_pos.
Print Assumptions lw3_decay_E_nonneg.
Print Assumptions lw3_decay_E_posT.
Print Assumptions lw3_decay_kills_inst.
Print Assumptions lw3_niven_lc_nz.
Print Assumptions lw3_e_trans_exit.

From Stdlib Require Import Extraction.
(* The grouped hom exit lw3_qeval_ring_hom stays out of the extraction    *)
(* list on purpose: its S01 And packaging is informative-with-Prop-      *)
(* instance, which the OCaml extractor refuses; the data carriers below  *)
(* extract clean (G3 magic=0 verified on this very list).  lw3_qnz joins *)
(* as a pure data carrier; lw3_niven_lc_nz stays out (Prop-typed b<>0    *)
(* argument would be refused by the extractor).                          *)
Separate Extraction lw3_nz lw3_lift lw3_evalr lw3_e lw3_K lw3_fbuild
  lw3_decay_E lw3_Kinst lw3_qnz.

(* ------------------------------------------------------------------ *)
(* Section 10.  p-scale per-node bound, layer k=0 (work order ③        *)
(* first layer): the evaluation of the built integrand at any node     *)
(* unfolds explicitly into q_pow x sg * q_pow (lift-p eval) N, so the  *)
(* per-node magnitude is pinned by the node magnitude B and the        *)
(* lifted-polynomial node magnitude Cp.  All rewrites stay at Qeq /    *)
(* QleT' whole-argument positions (no rewrite inside Qabs).            *)
(* ------------------------------------------------------------------ *)

(* Nonnegative products preserve QleT' on both sides (nonneg multipliers). *)
Lemma lw3_qleT'_mult2 : forall a b c d : Q,
  QleT' a b -> QleT' c d -> QleT' 0 b -> QleT' 0 c ->
  QleT' (a * c) (b * d).
Proof.
  intros a b c d Hab Hcd Hb Hc.
  apply (qleT'_trans _ (b * c)%Q).
  - apply qleT'_mult_compat_r.
    + exact Hc.
    + exact Hab.
  - apply qleT'_mult_compat_l.
    + exact Hb.
    + exact Hcd.
Qed.

(* Power of a nonnegative base stays nonnegative (QleT' face). *)
Lemma lw3_qpow_nonnegT : forall (m : nat) (B : Q),
  QleT' 0 B -> QleT' 0 (q_pow B m).
Proof.
  intros m. induction m as [|m IH]; intros B HB.
  - vm_compute. reflexivity.
  - cbn [q_pow]. apply (qleT'_trans _ (0 * q_pow B m)%Q).
    + apply Qle_to_QleT'. rewrite Qmult_0_l. apply (Qle_refl 0%Q).
    + apply Qle_to_QleT'.
      apply (Qmult_le_compat_r 0%Q B (q_pow B m)).
      * exact (QleT'_to_Qle 0%Q B HB).
      * exact (QleT'_to_Qle 0%Q (q_pow B m) (IH B HB)).
Qed.

(* Absolute value is compatible with powers: |x|^m bounds |x^m|. *)
Lemma lw3_qpow_abs_mono : forall (m : nat) (x B : Q),
  QleT' (Qabs x) B -> QleT' (Qabs (q_pow x m)) (q_pow B m).
Proof.
  intros m x B H. induction m as [|m IH].
  - vm_compute. reflexivity.
  - assert (HB : QleT' 0 B).
    { apply (qleT'_trans 0%Q (Qabs x) B).
      - apply Qle_to_QleT'. apply Qabs_nonneg.
      - exact H. }
    cbn [q_pow].
    apply (lw2u_qleT'_eq_l _ (Qabs x * Qabs (q_pow x m))%Q _).
    + apply (lw3_qleT'_mult2 (Qabs x) B (Qabs (q_pow x m)) (q_pow B m)).
      * exact H.
      * exact IH.
      * exact HB.
      * apply Qle_to_QleT'. apply Qabs_nonneg.
    + exact (Qabs_Qmult x (q_pow x m)).
Qed.

(* The t^sg factor evaluates to the sg-th power of the point. *)
Lemma lw3_tpow_eval : forall (sg : nat) (x : Q),
  QeqT (qpoly_eval (lw3_tpow sg) x) (q_pow x sg).
Proof.
  induction sg as [|sg IH]; intro x.
  - apply qeq_imp_qeqT. cbn [lw3_tpow qpoly_eval q_pow]. ring.
  - apply qeq_imp_qeqT. cbn [lw3_tpow qpoly_eval q_pow].
    rewrite (qeqT_imp_qeq _ _ (IH x)). ring.
Qed.

(* Iterated power of a polynomial evaluates to the power of its evaluation. *)
Lemma lw3_qpow_eval : forall (f : QPoly) (N : nat) (x : Q),
  QeqT (qpoly_eval (lw3_qpow f N) x) (q_pow (qpoly_eval f x) N).
Proof.
  intros f N. induction N as [|N IH]; intro x.
  - apply qeq_imp_qeqT. cbn [lw3_qpow qpoly_eval q_pow]. ring.
  - apply qeq_imp_qeqT. cbn [lw3_qpow]. rewrite qpoly_eval_mul.
    rewrite (qeqT_imp_qeq _ _ (IH x)). reflexivity.
Qed.

(* Main layer-k=0 unfolding: the built integrand at any point factors
   into node-power times lifted-power. *)
Lemma lw3_fbuild_eval_scale : forall (p : zpoly) (sg N : nat) (x : Q),
  QeqT (qpoly_eval (lw3_fbuild p sg N) x)
       (q_pow x sg * q_pow (qpoly_eval (lw3_lift p) x) N).
Proof.
  intros p sg N x. apply qeq_imp_qeqT. unfold lw3_fbuild.
  rewrite qpoly_eval_mul. rewrite (qeqT_imp_qeq _ _ (lw3_tpow_eval sg x)).
  rewrite (qeqT_imp_qeq _ _ (lw3_qpow_eval (lw3_lift p) N x)). apply Qeq_refl.
Qed.

(* ③ per-node scale bound (layer k=0, product form): with node magnitude B
   and lifted-node magnitude Cp, the node-value product of the two power
   factors is pinned by q_pow B sg * q_pow Cp N — the explicit p-scale
   constant feeding the suppression side of the final separation.  The
   k=0 unfolding lw3_fbuild_eval_scale transports this bound to the built
   integrand itself once the Qabs-congruence bridge is registered. *)
Lemma lw3_fbuild_node_scale_prod : forall (p : zpoly) (sg N j : nat) (B Cp : Q),
  QleT' (Qabs (lw2_node j)) B ->
  QleT' (Qabs (qpoly_eval (lw3_lift p) (lw2_node j))) Cp ->
  QleT' (Qabs (q_pow (lw2_node j) sg *
                q_pow (qpoly_eval (lw3_lift p) (lw2_node j)) N))
        (q_pow B sg * q_pow Cp N)%Q.
Proof.
  intros p sg N j B Cp HB HCp.
  assert (HBp : QleT' 0 B).
  { apply (qleT'_trans 0%Q (Qabs (lw2_node j)) B).
    - apply Qle_to_QleT'. apply Qabs_nonneg.
    - exact HB. }
  apply (lw2u_qleT'_eq_l
    (Qabs (q_pow (lw2_node j) sg *
           q_pow (qpoly_eval (lw3_lift p) (lw2_node j)) N))
    (Qabs (q_pow (lw2_node j) sg) *
     Qabs (q_pow (qpoly_eval (lw3_lift p) (lw2_node j)) N))%Q
    (q_pow B sg * q_pow Cp N)%Q).
  - apply (lw3_qleT'_mult2
      (Qabs (q_pow (lw2_node j) sg)) (q_pow B sg)
      (Qabs (q_pow (qpoly_eval (lw3_lift p) (lw2_node j)) N)) (q_pow Cp N)).
    + apply lw3_qpow_abs_mono. exact HB.
    + apply lw3_qpow_abs_mono. exact HCp.
    + apply lw3_qpow_nonnegT. exact HBp.
    + apply Qle_to_QleT'. apply Qabs_nonneg.
  - exact (Qabs_Qmult (q_pow (lw2_node j) sg)
      (q_pow (qpoly_eval (lw3_lift p) (lw2_node j)) N)).
Qed.

Print Assumptions lw3_qleT'_mult2.
Print Assumptions lw3_qpow_nonnegT.
Print Assumptions lw3_qpow_abs_mono.
Print Assumptions lw3_tpow_eval.
Print Assumptions lw3_qpow_eval.
Print Assumptions lw3_fbuild_eval_scale.
Print Assumptions lw3_fbuild_node_scale_prod.

(* ------------------------------------------------------------------ *)
(* Section 11.  p-scale layers k>=1 and Cp datafication (work order ③  *)
(* second and third layers, seat 182 continuation).                    *)
(*                                                                     *)
(* 传力链（第二层）：lw0_coef_iter_fall drops the k-th derivative       *)
(* coefficients onto the base coefficients with the rising factorial   *)
(* lw2_fall j k = (j+1)(j+2)..(j+k); the identity                      *)
(* lw2_fall j k * q_fact j == q_fact (j + k) pins the falling factor   *)
(* by the factorial at the shifted index, and lw2_qsum0 turns the      *)
(* per-coefficient bounds into a node bound at EVERY derivative order  *)
(* k (lw3_fbuild_deriv_node_scale), closing the j,k-uniform premise of *)
(* lw3_lambda_upper_fbuild.                                            *)
(* Cp 数据化（第三层）：the lifted node magnitude is pinned by the      *)
(* explicit coefficient sum lw3_Cp read off p through lw0_coef.        *)
(* Q 深度红线（E-STAGING-LW3-QABSEQFACE 坑 1）：no rewrite inside      *)
(* Qabs/QleT' anywhere; every Qeq transport goes through the           *)
(* lw2u_qleT'_eq_l bridge with the identity supplied term-level.       *)
(* ------------------------------------------------------------------ *)

(* Qabs is a Qeq-congruence (whole-argument position only).
   Stdlib QArith/Qabs.v:17 锚：Qabs x = let (n,d):=x in Z.abs n # d，
   即 Qabs 就是 Z.abs —— the congruence closes on the raw Z layer through
   Z.abs_mul plus an eq-rewrite (no Qeq-rewrite anywhere). *)
Lemma lw3_Qabs_congr : forall a b : Q, a == b -> QeqT (Qabs a) (Qabs b).
Proof.
  intros [na da] [nb db] H. apply qeq_imp_qeqT.
  unfold Qeq in H. cbn [Qnum Qden] in H.
  unfold Qabs, Qeq. cbn [Qnum Qden].
  replace (Z.pos db) with (Z.abs (Z.pos db)) by lia.
  replace (Z.pos da) with (Z.abs (Z.pos da)) by lia.
  rewrite <- (Z.abs_mul na (Z.pos db)), <- (Z.abs_mul nb (Z.pos da)), H.
  reflexivity.
Qed.

(* ① fbuild-level transport: the k=0 per-node scale bound moves from
   the product face (lw3_fbuild_node_scale_prod) onto the built
   integrand itself through the eval unfolding lw3_fbuild_eval_scale. *)
Lemma lw3_fbuild_node_scale : forall (p : zpoly) (sg N j : nat) (B Cp : Q),
  QleT' (Qabs (lw2_node j)) B ->
  QleT' (Qabs (qpoly_eval (lw3_lift p) (lw2_node j))) Cp ->
  QleT' (Qabs (qpoly_eval (lw3_fbuild p sg N) (lw2_node j)))
        (q_pow B sg * q_pow Cp N)%Q.
Proof.
  intros p sg N j B Cp HB HCp.
  apply (lw2u_qleT'_eq_l
    (Qabs (qpoly_eval (lw3_fbuild p sg N) (lw2_node j)))
    (Qabs (q_pow (lw2_node j) sg *
           q_pow (qpoly_eval (lw3_lift p) (lw2_node j)) N))
    (q_pow B sg * q_pow Cp N)%Q).
  - apply lw3_fbuild_node_scale_prod; assumption.
  - exact (qeqT_imp_qeq _ _
      (lw3_Qabs_congr _ _
         (qeqT_imp_qeq _ _ (lw3_fbuild_eval_scale p sg N (lw2_node j))))).
Qed.

(* qsum0 head-split (the shift helper for the eval-coef bridge). *)
Lemma lw3_qsum0_tail : forall (g : nat -> Q) (L : nat),
  QeqT (lw2_qsum0 g (Datatypes.S L))
       (g 0%nat + lw2_qsum0 (fun j => g (Datatypes.S j)) L).
Proof.
  intros g L. induction L as [|L IH].
  - apply qeq_imp_qeqT. cbn [lw2_qsum0]. ring.
  - apply qeq_imp_qeqT. cbn [lw2_qsum0]. rewrite (qeqT_imp_qeq _ _ IH). ring.
Qed.

(* The eval-coef bridge: Horner evaluation is the qsum0 of the
   coefficient-power terms.  This is the shared gate feeding both the
   k>=1 force chain and the Cp datafication. *)
Lemma lw3_eval_qsum0 : forall (f : QPoly) (x : Q),
  QeqT (qpoly_eval f x)
       (lw2_qsum0 (fun j => (lw0_coef j f * q_pow x j)%Q) (length f)).
Proof.
  intro f. induction f as [|a f IH]; intro x.
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. cbn [length qpoly_eval].
    rewrite (qeqT_imp_qeq _ _
      (lw3_qsum0_tail (fun j => (lw0_coef j (cons a f) * q_pow x j)%Q)
                      (length f))).
    cbn [lw0_coef q_pow].
    assert (Hshift : lw2_qsum0 (fun j => (lw0_coef j f * (x * q_pow x j))%Q)
                       (length f)
             == x * lw2_qsum0 (fun j => (lw0_coef j f * q_pow x j)%Q) (length f)).
    { transitivity (lw2_qsum0 (fun j => (x * (lw0_coef j f * q_pow x j))%Q)
                              (length f)).
      - apply qeqT_imp_qeq. apply lw2_qsum0_ext.
        intros j _. apply qeq_imp_qeqT. ring.
      - rewrite (qeqT_imp_qeq _ _
          (lw2_qsum0_scale (length f) (fun j => (lw0_coef j f * q_pow x j)%Q) x)).
        apply Qeq_refl. }
    rewrite Hshift. rewrite (qeqT_imp_qeq _ _ (IH x)). ring.
Qed.

(* Pointwise QleT' transports through lw2_qsum0. *)
Lemma lw3_qsum0_mono : forall (L : nat) (g h : nat -> Q),
  (forall i, (i < L)%nat -> QleT' (g i) (h i)) ->
  QleT' (lw2_qsum0 g L) (lw2_qsum0 h L).
Proof.
  intros L. induction L as [|L IH]; intros g h H.
  - vm_compute. reflexivity.
  - cbn [lw2_qsum0].
    assert (Hrest : forall i, (i < L)%nat -> QleT' (g i) (h i)).
    { intros i Hi. apply H. lia. }
    apply Qle_to_QleT'. apply Qplus_le_compat.
    + exact (QleT'_to_Qle _ _ (IH g h Hrest)).
    + exact (QleT'_to_Qle _ _ (H L (Nat.lt_succ_diag_r L))).
Qed.

(* Triangle inequality for lw2_qsum0. *)
Lemma lw3_qsum0_abs_split : forall (L : nat) (g : nat -> Q),
  QleT' (Qabs (lw2_qsum0 g L)) (lw2_qsum0 (fun i => Qabs (g i)) L).
Proof.
  intros L. induction L as [|L IH]; intro g.
  - vm_compute. reflexivity.
  - cbn [lw2_qsum0].
    apply (qleT'_trans _ (Qabs (lw2_qsum0 g L) + Qabs (g L))%Q).
    + apply Qle_to_QleT'. apply Qabs_triangle.
    + apply Qle_to_QleT'. apply Qplus_le_compat.
      * exact (QleT'_to_Qle _ _ (IH g)).
      * apply Qle_refl.
Qed.

(* The rising factorial meets the factorial:
   lw2_fall j k * j! == (j + k)!. *)
Lemma lw3_fall_fact_eq : forall (k j : nat),
  QeqT (lw2_fall j k * q_fact j) (q_fact (j + k)%nat).
Proof.
  induction k as [|k IH]; intro j.
  - apply qeq_imp_qeqT. cbn [lw2_fall]. rewrite Nat.add_0_r, Qmult_1_l. apply Qeq_refl.
  - apply qeq_imp_qeqT. cbn [lw2_fall]. rewrite Nat.add_succ_r.
    transitivity (lw2_fall (Datatypes.S j) k *
                  ((Z.of_nat (Datatypes.S j) # 1)%Q * q_fact j))%Q.
    + ring.
    + exact (qeqT_imp_qeq _ _ (IH (Datatypes.S j))).
Qed.

(* The rising factorial is nonnegative. *)
Lemma lw3_fall_nonneg : forall (k j : nat), QleT' 0%Q (lw2_fall j k).
Proof.
  induction k as [|k IH]; intro j.
  - reflexivity.
  - cbn [lw2_fall].
    change 0%Q with ((Z.of_nat (Datatypes.S j) # 1)%Q * 0%Q)%Q.
    apply qleT'_mult_compat_l.
    + exact (lw0_q_of_nat_nonneg (Datatypes.S j)).
    + exact (IH (Datatypes.S j)).
Qed.

(* The falling factor is bounded by the factorial at the shifted index. *)
Lemma lw3_fall_le_qfact : forall (j k : nat),
  QleT' (lw2_fall j k) (q_fact (j + k)%nat).
Proof.
  intros j k.
  apply (lw2u_qleT'_eq_r _ (lw2_fall j k * q_fact j)%Q).
  - apply (lw2u_qleT'_eq_l _ (lw2_fall j k * 1)%Q).
    + apply qleT'_mult_compat_l.
      * exact (lw3_fall_nonneg k j).
      * exact (lw0_q_fact_ge_one j).
    + ring.
  - exact (qeqT_imp_qeq _ _ (lw3_fall_fact_eq k j)).
Qed.

(* q_fact is monotone in the nat order. *)
Lemma lw3_qfact_mono : forall (a b : nat),
  (a <= b)%nat -> QleT' (q_fact a) (q_fact b).
Proof.
  intros a b. induction b as [|b IH]; intro H.
  - assert (Ha : a = 0%nat) by lia. subst a.
    apply Qle_to_QleT'. apply Qle_refl.
  - destruct (Nat.eq_dec a (Datatypes.S b)) as [He|Hne].
    + subst a. apply Qle_to_QleT'. apply Qle_refl.
    + assert (Hab : (a <= b)%nat) by lia.
      assert (Hqb : QleT' 0%Q (q_fact b)).
      { apply (qleT'_trans 0%Q 1%Q _).
        - exact Qle_0_1.
        - exact (lw0_q_fact_ge_one b). }
      apply (qleT'_trans _ (lw0_q_of_nat (Datatypes.S a) * q_fact b)%Q).
      * apply (qleT'_trans _ (q_fact b)%Q).
        -- exact (IH Hab).
        -- apply (lw2u_qleT'_eq_l _ (1 * q_fact b)%Q).
           ++ apply qleT'_mult_compat_r.
              ** exact Hqb.
              ** change 1%Q with (lw0_q_of_nat 1%nat).
                 replace (Datatypes.S a)%nat with (1 + a)%nat by lia.
                 exact (lw0_q_of_nat_le_add 1 a).
           ++ ring.
      * apply (lw2u_qleT'_eq_r _ (lw0_q_of_nat (Datatypes.S b) * q_fact b)%Q).
        -- apply qleT'_mult_compat_r.
           ++ exact Hqb.
           ++ replace (Datatypes.S b)%nat
                with ((Datatypes.S a) + (b - a))%nat by lia.
              exact (lw0_q_of_nat_le_add (Datatypes.S a) (b - a)).
        -- symmetry. exact (qeqT_imp_qeq _ _ (lw0_q_fact_step b)).
Qed.

(* Power monotonicity in the exponent for a base of at least one. *)
Lemma lw3_qpow_mono_exp : forall (B : Q) (i m : nat),
  QleT' 1 B -> (i <= m)%nat -> QleT' (q_pow B i) (q_pow B m).
Proof.
  intros B i m H1 Hi. revert Hi. induction m as [|m IH]; intro Hi.
  - assert (Hi0 : i = 0%nat) by lia. subst i.
    apply Qle_to_QleT'. apply Qle_refl.
  - destruct (Nat.eq_dec i (Datatypes.S m)) as [He|Hne].
    + subst i. apply Qle_to_QleT'. apply Qle_refl.
    + assert (Him : (i <= m)%nat) by lia.
      apply (qleT'_trans _ (q_pow B m)).
      * exact (IH Him).
      * exact (lw0_q_pow_le_succ_pow B m H1).
Qed.

(* Constant sums meet the counted product. *)
Lemma lw3_qsum0_const : forall (m : nat) (T : Q),
  QeqT (lw2_qsum0 (fun _ => T) m) (T * lw0_q_of_nat m).
Proof.
  intros m. induction m as [|m IH]; intro T.
  - apply qeq_imp_qeqT. cbn [lw2_qsum0]. unfold lw0_q_of_nat. cbn [Z.of_nat]. ring.
  - apply qeq_imp_qeqT. cbn [lw2_qsum0].
    rewrite (qeqT_imp_qeq _ _ (IH T)),
            (qeqT_imp_qeq _ _ (lw2u_q_of_nat_succ m)). ring.
Qed.

(* ② force chain, level 1: the k-th derivative coefficients of the
   built integrand fall onto the base coefficients. *)
Lemma lw3_fbuild_coef_fall : forall (k : nat) (p : zpoly) (sg N j : nat),
  QeqT (lw0_coef j (qpoly_deriv_iter k (lw3_fbuild p sg N)))
       (lw2_fall j k * lw0_coef (j + k) (lw3_fbuild p sg N)).
Proof.
  intros k p sg N j. apply lw0_coef_iter_fall.
Qed.

(* ② force chain, level 2 (main): the k=0 per-node scale bound
   generalizes to EVERY derivative order k.  With |node j| <= Bn,
   1 <= Bn and a uniform coefficient bound C on the built integrand,
   the k-th derivative at any node is pinned by the explicit closed
   form m * (q_fact (m + k) * C * Bn^m), m = length (D^k fbuild).
   This closes the j,k-uniform per-node premise of
   lw3_lambda_upper_fbuild with caller-chosen data Bn, C. *)
Lemma lw3_fbuild_deriv_node_scale :
  forall (p : zpoly) (sg N k j : nat) (Bn C : Q),
  QleT' (Qabs (lw2_node j)) Bn ->
  QleT' 1 Bn ->
  (forall i, QleT' (Qabs (lw0_coef i (lw3_fbuild p sg N))) C) ->
  QleT' (Qabs (qpoly_eval (qpoly_deriv_iter k (lw3_fbuild p sg N))
                          (lw2_node j)))
        (lw0_q_of_nat (length (qpoly_deriv_iter k (lw3_fbuild p sg N))) *
         (q_fact (length (qpoly_deriv_iter k (lw3_fbuild p sg N)) + k) * C *
          q_pow Bn (length (qpoly_deriv_iter k (lw3_fbuild p sg N))))%Q).
Proof.
  intros p sg N k j Bn C HBn H1Bn HC.
  set (f := lw3_fbuild p sg N).
  set (m := length (qpoly_deriv_iter k f)).
  assert (HC0 : QleT' 0%Q C).
  { apply (qleT'_trans 0%Q (Qabs (lw0_coef 0 f)) C).
    - apply Qle_to_QleT'. apply Qabs_nonneg.
    - exact (HC 0%nat). }
  assert (HBn0 : QleT' 0%Q Bn).
  { apply (qleT'_trans 0%Q 1%Q Bn).
    - reflexivity.
    - exact H1Bn. }
  apply (lw2u_qleT'_eq_l
    (Qabs (qpoly_eval (qpoly_deriv_iter k f) (lw2_node j)))
    (Qabs (lw2_qsum0
            (fun i => (lw0_coef i (qpoly_deriv_iter k f) *
                      q_pow (lw2_node j) i)%Q)
            m))
    (lw0_q_of_nat m * (q_fact (m + k) * C * q_pow Bn m))%Q).
  - apply (qleT'_trans
      (Qabs (lw2_qsum0
              (fun i => (lw0_coef i (qpoly_deriv_iter k f) *
                        q_pow (lw2_node j) i)%Q)
              m))
      (lw2_qsum0
        (fun i => (Qabs (lw0_coef i (qpoly_deriv_iter k f) *
                        q_pow (lw2_node j) i))%Q)
        m)
      (lw0_q_of_nat m * (q_fact (m + k) * C * q_pow Bn m))%Q).
    + exact (lw3_qsum0_abs_split m (fun i =>
        (lw0_coef i (qpoly_deriv_iter k f) * q_pow (lw2_node j) i)%Q)).
    + apply (qleT'_trans
        (lw2_qsum0
           (fun i => (Qabs (lw0_coef i (qpoly_deriv_iter k f) *
                        q_pow (lw2_node j) i))%Q)
           m)
        (lw2_qsum0 (fun i => (q_fact (m + k) * C * q_pow Bn m)%Q) m)
        (lw0_q_of_nat m * (q_fact (m + k) * C * q_pow Bn m))%Q).
      * apply lw3_qsum0_mono. intros i Hi.
        apply (lw2u_qleT'_eq_l
          (Qabs (lw0_coef i (qpoly_deriv_iter k f) *
                 q_pow (lw2_node j) i))
          (Qabs (lw0_coef i (qpoly_deriv_iter k f)) *
           Qabs (q_pow (lw2_node j) i))%Q _).
        -- apply (lw3_qleT'_mult2
             (Qabs (lw0_coef i (qpoly_deriv_iter k f)))
             (q_fact (m + k) * C)
             (Qabs (q_pow (lw2_node j) i))
             (q_pow Bn m)).
           ++ (* |coef_i (D^k f)| <= q_fact (m+k) * C *)
               { apply (lw2u_qleT'_eq_l
                   (Qabs (lw0_coef i (qpoly_deriv_iter k f)))
                   (lw2_fall i k * Qabs (lw0_coef (i + k) f))%Q _).
                 - apply (qleT'_trans _
                     (q_fact (i + k)%nat * Qabs (lw0_coef (i + k) f))%Q).
                   + apply qleT'_mult_compat_r.
                     * exact (Qle_to_QleT' _ _
                            (Qabs_nonneg (lw0_coef (i + k) f))).
                     * exact (lw3_fall_le_qfact i k).
                   + apply (qleT'_trans _ (q_fact (i + k)%nat * C)%Q).
                     * apply qleT'_mult_compat_l.
                       -- { apply (qleT'_trans 0%Q 1%Q _).
                            - exact Qle_0_1.
                            - exact (lw0_q_fact_ge_one (i + k)). }
                       -- exact (HC (i + k)%nat).
                     * apply qleT'_mult_compat_r.
                       -- exact HC0.
                       -- apply lw3_qfact_mono. lia.
                 - transitivity (Qabs (lw2_fall i k *
                        lw0_coef (i + k) f)).
                   + exact (qeqT_imp_qeq _ _
                          (lw3_Qabs_congr _ _
                             (qeqT_imp_qeq _ _ (lw0_coef_iter_fall k f i)))).
                   + transitivity
                       (Qabs (lw2_fall i k) * Qabs (lw0_coef (i + k) f))%Q.
                     * exact (Qabs_Qmult (lw2_fall i k)
                            (lw0_coef (i + k) f)).
                     * rewrite (Qabs_pos (lw2_fall i k)
                          (QleT'_to_Qle _ _ (lw3_fall_nonneg k i))).
                       reflexivity.
               }
           ++ (* |(node j)^i| <= Bn^m *)
              apply (qleT'_trans _ (q_pow Bn i)).
              ** exact (lw3_qpow_abs_mono i (lw2_node j) Bn HBn).
              ** exact (lw3_qpow_mono_exp Bn i m H1Bn
                   (Nat.lt_le_incl i m Hi)).
            ++ apply (lw2u_qleT'_eq_l 0%Q (q_fact (m + k) * 0)%Q).
               ** apply qleT'_mult_compat_l.
                   --- apply (qleT'_trans 0%Q 1%Q _).
                       +++ reflexivity.
                       +++ exact (lw0_q_fact_ge_one (m + k)).
                   --- exact HC0.
               ** exact (Qeq_sym _ _ (Qmult_0_r (q_fact (m + k)))).
            ++ exact (Qle_to_QleT' _ _ (Qabs_nonneg (q_pow (lw2_node j) i))).
        -- exact (Qabs_Qmult (lw0_coef i (qpoly_deriv_iter k f))
                   (q_pow (lw2_node j) i)).
      * (* constant sum collapses onto the counted product *)
        apply (lw2u_qleT'_eq_r
          (lw2_qsum0 (fun i => (q_fact (m + k) * C * q_pow Bn m)%Q) m)
          ((q_fact (m + k) * C * q_pow Bn m) * lw0_q_of_nat m)%Q
          (lw0_q_of_nat m * (q_fact (m + k) * C * q_pow Bn m))%Q).
        -- exact (qeq_leT' _ _
             (lw3_qsum0_const m (q_fact (m + k) * C * q_pow Bn m)%Q)).
        -- apply Qmult_comm.
  - exact (qeqT_imp_qeq _ _
      (lw3_Qabs_congr _ _
         (qeqT_imp_qeq _ _ (lw3_eval_qsum0 (qpoly_deriv_iter k f) (lw2_node j))))).
Qed.

(* lift preserves length (the Cp indexing alignment). *)
Lemma lw3_lift_length : forall p : zpoly, Id (length (lw3_lift p)) (length p).
Proof.
  induction p as [|a p IH].
  - apply id_refl.
  - rewrite lw3_lift_cons. cbn [length]. rewrite IH. apply id_refl.
Qed.

(* ③ Cp datafication: the lifted node magnitude is pinned by the
   explicit coefficient sum lw3_Cp — p's own coefficient data read
   through lw0_coef on the lift, weighted by the node anchor Bn. *)
Definition lw3_Cp (p : zpoly) (Bn : Q) : Q :=
  lw2_qsum0 (fun i => (Qabs (lw0_coef i (lw3_lift p)) * q_pow Bn i)%Q)
            (length p).

Lemma lw3_lift_eval_le_Cp : forall (p : zpoly) (x Bn : Q),
  QleT' (Qabs x) Bn ->
  QleT' (Qabs (qpoly_eval (lw3_lift p) x)) (lw3_Cp p Bn).
Proof.
  intros p x Bn HB.
  apply (lw2u_qleT'_eq_l
    (Qabs (qpoly_eval (lw3_lift p) x))
    (Qabs (lw2_qsum0 (fun i => (lw0_coef i (lw3_lift p) * q_pow x i)%Q)
                     (length p)))
    (lw3_Cp p Bn)).
  - apply (qleT'_trans _
      (lw2_qsum0 (fun i => (Qabs (lw0_coef i (lw3_lift p) * q_pow x i))%Q)
                 (length p))).
    + exact (lw3_qsum0_abs_split (length p)
        (fun i => (lw0_coef i (lw3_lift p) * q_pow x i)%Q)).
    + apply lw3_qsum0_mono. intros i Hi.
      apply (lw2u_qleT'_eq_l
        (Qabs (lw0_coef i (lw3_lift p) * q_pow x i))
        (Qabs (lw0_coef i (lw3_lift p)) * Qabs (q_pow x i))%Q _).
      * apply qleT'_mult_compat_l.
        -- exact (Qle_to_QleT' _ _
               (Qabs_nonneg (lw0_coef i (lw3_lift p)))).
        -- exact (lw3_qpow_abs_mono i x Bn HB).
      * exact (Qabs_Qmult (lw0_coef i (lw3_lift p)) (q_pow x i)).
  - rewrite <- lw3_lift_length.
    exact (qeqT_imp_qeq _ _
      (lw3_Qabs_congr _ _
         (qeqT_imp_qeq _ _ (lw3_eval_qsum0 (lw3_lift p) x)))).
Qed.

Print Assumptions lw3_Qabs_congr.
Print Assumptions lw3_fbuild_node_scale.
Print Assumptions lw3_qsum0_tail.
Print Assumptions lw3_eval_qsum0.
Print Assumptions lw3_qsum0_mono.
Print Assumptions lw3_qsum0_abs_split.
Print Assumptions lw3_fall_fact_eq.
Print Assumptions lw3_fall_nonneg.
Print Assumptions lw3_fall_le_qfact.
Print Assumptions lw3_qfact_mono.
Print Assumptions lw3_qpow_mono_exp.
Print Assumptions lw3_qsum0_const.
Print Assumptions lw3_fbuild_coef_fall.
Print Assumptions lw3_fbuild_deriv_node_scale.
Print Assumptions lw3_lift_length.
Print Assumptions lw3_Cp.
Print Assumptions lw3_lift_eval_le_Cp.

(* ------------------------------------------------------------------ *)
(* Section 12.  The main statement (work order _tlw199 (2026-09)).      *)
(* Every nonzero integer polynomial p (explicit Set-level witness       *)
(* lw3_nz) has its evaluation at the constructive constant e explicitly *)
(* separated from zero, with an explicit positive rational witness.     *)
(* Every premise and the conclusion are Set-sorted: the nonzero side of *)
(* the integer functional value enters as the decidable data witness    *)
(* lw3_qnz, and the strict |K| < 1 side is discharged from a uniform    *)
(* per-node bound E (produced at every derivative order by the closed   *)
(* form of Section 11) through the node-count upper bound of Section 8  *)
(* and the QltT collapse of Section 9.                                  *)
(* ------------------------------------------------------------------ *)
Theorem lw3_e_transcendental :
  forall (p : zpoly) (N : nat) (E : Q),
    lw3_nz p ->
    lw3_qnz ((lw3_Kinst p N) # 1)%Q ->
    (forall j k : nat,
       Nat.le j (Datatypes.S (lw3_nodecount p N)) ->
       Nat.lt k (length (lw3_fbuild p (lw3_deg p) N)) ->
       QleT' (Qabs (qpoly_eval
                      (qpoly_deriv_iter k (lw3_fbuild p (lw3_deg p) N))
                      (lw2_node j))) E) ->
    QltT (lw0_q_of_nat (Datatypes.S (Datatypes.S (lw3_nodecount p N)) *
                        length (lw3_fbuild p (lw3_deg p) N)) * E)
         (1 # 1)%Q ->
    sigT (fun c : Q => And (QltT 0 c)
      (real_lt (real_const c)
         (real_metric (lw3_evalr p lw3_e) real_zero))).
Proof.
  intros p N E Hnz Hqnz Hnodes Hlt1.
  (* step 1: the Set-level nonzero witness on the integer functional   *)
  (* value yields the gate-family contract shape K <> 0.               *)
  assert (HK : lw3_Kinst p N <> 0%Z).
  { intro Hz. unfold lw3_qnz in Hqnz.
    rewrite Hz in Hqnz. rewrite Qeq_bool_refl in Hqnz.
    cbn in Hqnz. destruct Hqnz. }
  (* step 2: the integer functional value bridges to lambda.          *)
  assert (Hlam : QeqT (lw2_lambda (lw3_nodecount p N)
                        (lw3_fbuild p (lw3_deg p) N))
                      ((lw3_Kinst p N) # 1)%Q)
    by exact (lw3_Kinst_spec p N).
  (* step 3: the uniform per-node bound lifts to the node-count       *)
  (* upper bound on the absolute value of lambda.                     *)
  assert (Hub : QleT' (Qabs (lw2_lambda (lw3_nodecount p N)
                            (lw3_fbuild p (lw3_deg p) N)))
                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (lw3_nodecount p N)) *
                                     length (lw3_fbuild p (lw3_deg p) N)) * E))
    by exact (lw3_lambda_upper_fbuild p (lw3_deg p) N (lw3_nodecount p N) E
                Hnodes).
  (* step 4: strict collapse |K| < 1 out of the QleT' bound, the      *)
  (* strict comparison and the Qeq head change on the absolute value. *)
  assert (Hk1 : QltT (Qabs ((lw3_Kinst p N) # 1)%Q) (1 # 1)%Q).
  { exact (qltT_eq_compat_l
             (Qabs (lw2_lambda (lw3_nodecount p N)
                     (lw3_fbuild p (lw3_deg p) N)))
             (Qabs ((lw3_Kinst p N) # 1)%Q) (1 # 1)%Q
             (lw3_Qabs_congr _ _ (qeqT_imp_qeq _ _ Hlam))
             (qleT'_ltT_ltT _ _ _ Hub Hlt1)). }
  (* step 5: the contradiction gate and the apartness exit close the  *)
  (* chain with the explicit positive rational separation witness.    *)
  exact (lw3_e_trans_exit p N HK Hk1).
Qed.

Print Assumptions lw3_e_transcendental.
