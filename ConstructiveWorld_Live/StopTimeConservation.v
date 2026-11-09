(* ConstructiveWorld-Set -- stop-time conservation across the exchange and stopping-time families. *)

(** * StopTimeConservation: conservative accounting for eps exchange and honest stopping times.

    Mission.  Conservation of the rational quantity [eps] under affine exchange
      reparameterizations and of a chain budget at an honest stopping time:
      [ud_le_add_r], [bond], [bond_check], [edge_spec], [edge_map], [edge_diss],
      [edge_ok], [edge_bi], [edge_tame], [edge_compound_affine],
      [path_dissipation_additive], [resolve_total], [resolve_miss_iou],
      [honest_stop], [stoptime_conservation], [stoptime_conservation_master].

    Dependencies.  Stdlib [Lia], [List], [QArith.QArith], [QArith.Qabs],
      [Arith.PeanoNat].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpConstitution],
      [UpBudgetReal], [UpStopTime] of this development.

    References.  This development, StopTimeConservation.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" StopTimeConservation.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import Lia.
From Stdlib Require Import List.
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
Require Import UpConstitution.
Require Import UpBudgetReal.
Require Import UpStopTime.

(* ================= Section 1. The ud_le_add_r family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs.

Local Open Scope Q_scope.

(* Section 1. Q-level widget: the [UpConstitution] bridges supply the weak inequality for right addition. *)

Lemma ud_le_add_r : forall z w : Q, Qle 0 w -> Qle z (z + w).
Proof.
  intros z w Hw.
  apply (Qle_trans z (z + 0) (z + w)).
  - apply QleT'_to_Qle.
    apply (uc_qeq_le_r z (z + 0) z).
    + apply qeq_imp_qeqT. ring.
    + apply Qle_to_QleT'. apply Qle_refl.
  - apply Qplus_le_compat; [apply Qle_refl | exact Hw].
Qed.

(* Section 2. Piece 1, the [bond] record: a Set-level type bundling bound certificates. *)
(*   currency reading: the eps slot quantifies strictness as a resource, the amount of eps slack it carries. *)

Record bond : Set := mk_bond {
  bd_id : nat;        (* statement id *)
  bd_bound : Q;       (* the bound value: the upper limit not to exceed *)
  bd_eps : Q;         (* the eps slot: strictness slack *)
  bd_src : nat        (* the issuing source: which metric or format *)
}.

(* the bond-face checker, executable by [Defined]; the [inr] branch carries a rejection code, mirroring the constitution shape. *)
Inductive bond_reject : Set :=
| br_eps.              (* negative eps slot: no strictness slack left to concede *)

Definition bond_check (bd : bond)
  : Or (QleT' 0 (bd_eps bd)) (And (Id (Qle_bool 0 (bd_eps bd)) false) bond_reject) :=
  match Qle_bool 0 (bd_eps bd) as b
        return Or (Id b true) (And (Id b false) bond_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, br_eps)
  end.

(* Section 3. Piece 2, the exchange edge [edge_spec]: the conversion theorem for an affine eps reparameterization. *)
(*   eps_out = a * eps_in + b with a > 0: a positive slope preserves the strict order. *)

Record edge_spec : Set := mk_edge {
  ed_id : nat;        (* edge id *)
  ed_src : nat;       (* the source format (metric index) *)
  ed_dst : nat;       (* the target format *)
  ed_a : Q;           (* the slope a > 0 *)
  ed_b : Q            (* the intercept b *)
}.

Definition edge_map (e : edge_spec) (x : Q) : Q := ed_a e * x + ed_b e.
Definition edge_diss (e : edge_spec) (x : Q) : Q := x - edge_map e x.
Definition edge_ok (e : edge_spec) : bool := Qlt_bool 0 (ed_a e).
Definition edge_bi (e : edge_spec) : bool :=
  andb (Qlt_bool 0 (ed_a e)) (Qle_bool 0 (ed_b e)).
Definition edge_tame (e : edge_spec) : bool :=
  andb (Qlt_bool 0 (ed_a e)) (Qle_bool (ed_a e) 1).

(* the edge checker, executable by [Defined]; rejection-code shape. *)
Inductive edge_reject : Set :=
| er_slope.             (* nonpositive slope: the exchange fails to preserve the strict order *)

Definition edge_check (e : edge_spec)
  : Or (QltT 0 (ed_a e)) (And (Id (Qlt_bool 0 (ed_a e)) false) edge_reject) :=
  match Qlt_bool 0 (ed_a e) as b
        return Or (Id b true) (And (Id b false) edge_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, er_slope)
  end.

(* extracting Q facts from the boolean checks: the two facts of a regular edge (a > 0 and b >= 0). *)
Lemma edge_bi_spec : forall e : edge_spec,
  Id (edge_bi e) true -> And (QltT 0 (ed_a e)) (QleT' 0 (ed_b e)).
Proof.
  intros e H. unfold edge_bi in H.
  destruct (Qlt_bool 0 (ed_a e)) eqn:E1; destruct (Qle_bool 0 (ed_b e)) eqn:E2;
    rewrite ?E1 in H; rewrite ?E2 in H; simpl in H; try (inversion H).
  split.
  - apply RealSetoid.eq_Id. exact E1.
  - apply RealSetoid.eq_Id. exact E2.
Qed.

(* the two Q facts of a tame edge (a > 0 and a <= 1). *)
Lemma edge_tame_spec : forall e : edge_spec,
  Id (edge_tame e) true -> And (QltT 0 (ed_a e)) (QleT' (ed_a e) 1).
Proof.
  intros e H. unfold edge_tame, edge_ok in H.
  destruct (Qlt_bool 0 (ed_a e)) eqn:E1; destruct (Qle_bool (ed_a e) 1) eqn:E2;
    rewrite ?E1 in H; rewrite ?E2 in H; simpl in H; try (inversion H).
  split.
  - apply RealSetoid.eq_Id. exact E1.
  - apply RealSetoid.eq_Id. exact E2.
Qed.

(* order property of the edge as a conversion: a > 0 makes the affine eps reparameterization strictly order preserving. *)
Lemma edge_strict_mono : forall (e : edge_spec) (x y : Q),
  Qlt 0 (ed_a e) -> Qlt x y -> Qlt (edge_map e x) (edge_map e y).
Proof.
  intros e x y Ha Hxy. unfold edge_map.
  assert (H1 : Qlt (x * ed_a e) (y * ed_a e)).
  { apply (Qmult_lt_compat_r x y (ed_a e) Ha Hxy). }
  assert (H2a : Qlt (ed_a e * x) (y * ed_a e)).
  { apply QltT_to_Qlt.
    apply (uc_qeq_lt_l (x * ed_a e) (ed_a e * x) (y * ed_a e)).
    - apply qeq_imp_qeqT. ring.
    - exact (Qlt_to_QltT _ _ H1). }
  assert (H2 : Qlt (ed_a e * x) (ed_a e * y)).
  { apply QltT_to_Qlt.
    apply (uc_qeq_lt_r (y * ed_a e) (ed_a e * y) (ed_a e * x)).
    - apply qeq_imp_qeqT. ring.
    - exact (Qlt_to_QltT _ _ H2a). }
  assert (H3 : Qlt (ed_b e + ed_a e * x) (ed_b e + ed_a e * y)).
  { apply (proj2 (Qplus_lt_r (ed_a e * x) (ed_a e * y) (ed_b e))). exact H2. }
  assert (H4 : Qlt (ed_a e * x + ed_b e) (ed_b e + ed_a e * y)).
  { apply QltT_to_Qlt.
    apply (uc_qeq_lt_l (ed_b e + ed_a e * x)
                       (ed_a e * x + ed_b e)
                       (ed_b e + ed_a e * y)).
    - apply qeq_imp_qeqT. ring.
    - exact (Qlt_to_QltT _ _ H3). }
  apply QltT_to_Qlt.
  apply (uc_qeq_lt_r (ed_b e + ed_a e * y)
                     (ed_a e * y + ed_b e)
                     (ed_a e * x + ed_b e)).
  - apply qeq_imp_qeqT. ring.
  - exact (Qlt_to_QltT _ _ H4).
Qed.

(* a regular edge keeps the eps slot strictly positive: strictness is not annihilated by an exchange. *)
Lemma edge_map_pos : forall (e : edge_spec) (x : Q),
  QltT 0 x -> Id (edge_bi e) true -> QltT 0 (edge_map e x).
Proof.
  intros e x Hx Hbi.
  pose proof (edge_bi_spec e Hbi) as [Ha Hb].
  apply Qlt_to_QltT.
  apply (Qlt_le_trans 0 (ed_a e * x) (edge_map e x)).
  - apply (Qmult_lt_0_compat (ed_a e) x (QltT_to_Qlt 0 (ed_a e) Ha)
             (QltT_to_Qlt 0 x Hx)).
  - unfold edge_map.
    apply QleT'_to_Qle.
    apply (uc_qeq_le_l (ed_a e * x + 0) (ed_a e * x) (ed_a e * x + ed_b e)).
    + apply qeq_imp_qeqT. ring.
    + apply Qle_to_QleT'.
      apply Qplus_le_compat; [apply Qle_refl | exact (QleT'_to_Qle _ _ Hb)].
Qed.

(* exchanging a bond along an edge reparameterizes the eps slot by the affine map. *)
Definition bond_exchange (e : edge_spec) (bd : bond) : bond :=
  mk_bond (bd_id bd) (bd_bound bd) (edge_map e (bd_eps bd)) (ed_dst e).

Lemma bond_exchange_eps : forall (e : edge_spec) (bd : bond),
  bd_eps (bond_exchange e bd) == edge_map e (bd_eps bd).
Proof. intros e bd. exact (Qeq_refl (edge_map e (bd_eps bd))). Qed.

(* conservation at the bond level: the incoming eps equals the outgoing eps plus the dissipation. *)
Theorem bond_exchange_conservation : forall (e : edge_spec) (bd : bond),
  bd_eps bd == bd_eps (bond_exchange e bd) + edge_diss e (bd_eps bd).
Proof.
  intros e bd. rewrite bond_exchange_eps.
  unfold edge_diss, edge_map. ring.
Qed.

(* exchanges preserve strictness: along a regular edge the exchanged eps slot stays strictly positive. *)
Theorem bond_exchange_pos : forall (e : edge_spec) (bd : bond),
  Id (edge_bi e) true -> QltT 0 (bd_eps bd) ->
  QltT 0 (bd_eps (bond_exchange e bd)).
Proof.
  intros e bd Hbi Hx.
  unfold bond_exchange.
  exact (edge_map_pos e (bd_eps bd) Hx Hbi).
Qed.


(* Section 4. Piece 3 (the main piece), [edge_compound_affine]: edge composition equals affine composition of the eps maps. *)
(*   the composite slope a2 * a1 stays positive, decidable by linearity; *)
(*   path legality is positivity of the affine composite, decided linearly by the boolean decider [path2_ok]. *)

Definition edge_comp (e2 e1 : edge_spec) : edge_spec :=
  mk_edge (ed_id e1) (ed_src e1) (ed_dst e2)
          (ed_a e2 * ed_a e1) (ed_a e2 * ed_b e1 + ed_b e2).

Lemma edge_comp_slope : forall e1 e2 : edge_spec,
  ed_a (edge_comp e2 e1) == ed_a e2 * ed_a e1.
Proof. intros e1 e2. exact (Qeq_refl (ed_a e2 * ed_a e1)). Qed.

Lemma edge_comp_b : forall e1 e2 : edge_spec,
  ed_b (edge_comp e2 e1) == ed_a e2 * ed_b e1 + ed_b e2.
Proof. intros e1 e2. exact (Qeq_refl (ed_a e2 * ed_b e1 + ed_b e2)). Qed.

(* main statement: the eps map of the composite edge equals the affine composition of the two maps (path semantics). *)
Theorem edge_compound_affine : forall (e1 e2 : edge_spec) (x : Q),
  edge_map (edge_comp e2 e1) x == edge_map e2 (edge_map e1 x).
Proof.
  intros e1 e2 x. unfold edge_map.
  rewrite edge_comp_slope. rewrite edge_comp_b. ring.
Qed.

(* composite legality: two positive slopes give a positive composite slope. *)
Theorem edge_comp_legal : forall e1 e2 : edge_spec,
  QltT 0 (ed_a e1) -> QltT 0 (ed_a e2) -> QltT 0 (ed_a (edge_comp e2 e1)).
Proof.
  intros e1 e2 H1 H2.
  exact (Qlt_to_QltT 0 (ed_a (edge_comp e2 e1))
    (Qmult_lt_0_compat (ed_a e2) (ed_a e1)
      (QltT_to_Qlt 0 (ed_a e2) H2) (QltT_to_Qlt 0 (ed_a e1) H1))).
Qed.


(* the linear (boolean) decider of path legality: two-edge paths. *)
Definition path2_ok (e2 e1 : edge_spec) : bool :=
  andb (edge_ok e1) (edge_ok e2).

(* decider soundness: the boolean verdict true gives a positive composite slope (legality decided linearly). *)
Theorem path2_ok_sound : forall e1 e2 : edge_spec,
  Id (path2_ok e2 e1) true -> QltT 0 (ed_a (edge_comp e2 e1)).
Proof.
  intros e1 e2 H. unfold path2_ok, edge_ok in H.
  destruct (Qlt_bool 0 (ed_a e1)) eqn:E1; destruct (Qlt_bool 0 (ed_a e2)) eqn:E2;
    rewrite ?E1 in H; rewrite ?E2 in H; simpl in H; try (inversion H).
  apply edge_comp_legal.
  - apply RealSetoid.eq_Id. exact E1.
  - apply RealSetoid.eq_Id. exact E2.
Qed.

(* the composite of tame edges stays tame (slope product at most 1): dissipation accounting closes along the path. *)
Theorem edge_tame_comp : forall e1 e2 : edge_spec,
  Id (edge_tame e1) true -> Id (edge_tame e2) true ->
  Id (edge_tame (edge_comp e2 e1)) true.
Proof.
  intros e1 e2 H1 H2.
  pose proof (edge_tame_spec e1 H1) as [Ha1 Hb1].
  pose proof (edge_tame_spec e2 H2) as [Ha2 Hb2].
  assert (Hc : Qle (ed_a (edge_comp e2 e1)) 1).
  { assert (Ecomm : ed_a (edge_comp e2 e1) == ed_a e1 * ed_a e2).
    { rewrite edge_comp_slope. ring. }
    assert (Hbound : Qle (ed_a e1 * ed_a e2) 1).
    { apply (Qle_trans (ed_a e1 * ed_a e2) (1 * ed_a e2) 1).
      - apply (Qmult_le_compat_r (ed_a e1) 1 (ed_a e2)
                 (QleT'_to_Qle _ _ Hb1)).
        apply (Qlt_le_weak 0 (ed_a e2) (QltT_to_Qlt 0 (ed_a e2) Ha2)).
      - rewrite Qmult_1_l. exact (QleT'_to_Qle _ _ Hb2). }
    apply QleT'_to_Qle.
    apply (uc_qeq_le_l (ed_a e1 * ed_a e2) (ed_a (edge_comp e2 e1)) 1).
    - apply qeq_imp_qeqT. symmetry. exact Ecomm.
    - exact (Qle_to_QleT' _ _ Hbound). }
  pose proof (edge_comp_legal e1 e2 Ha1 Ha2) as Hp.
  pose proof (RealSetoid.Id_eq (Qlt_bool 0 (ed_a (edge_comp e2 e1))) true Hp) as EA.
  pose proof (Qle_to_QleT' (ed_a (edge_comp e2 e1)) 1 Hc) as HcT.
  pose proof (RealSetoid.Id_eq (Qle_bool (ed_a (edge_comp e2 e1)) 1) true HcT) as EB.
  unfold edge_tame, edge_ok.
  apply RealSetoid.eq_Id.
  rewrite EA. rewrite EB. reflexivity.
Qed.

(* Section 5. Piece 4, dissipation accounting [path_dissipation]. *)
(*   currency semantics: eps is the conserved quantity, each exchange satisfies eps_in = eps_out + dissipation; *)
(*   dissipation is additive along a path (each unit counted once, none minted); *)
(*   on a tame edge (a <= 1) dissipation is monotone in the incoming eps (larger exchanges dissipate more). *)

(* the conservation identity. *)
Theorem diss_conservation : forall (e : edge_spec) (x : Q),
  x == edge_map e x + edge_diss e x.
Proof.
  intros e x. unfold edge_diss, edge_map. ring.
Qed.

(* additivity along a path: the total dissipation of a composite path equals the sum of the segment dissipations (a telescoping identity). *)
Theorem path_dissipation_additive : forall (e1 e2 : edge_spec) (x : Q),
  edge_diss (edge_comp e2 e1) x == edge_diss e1 x + edge_diss e2 (edge_map e1 x).
Proof.
  intros e1 e2 x. unfold edge_diss, edge_map.
  rewrite edge_comp_slope. rewrite edge_comp_b. ring.
Qed.

(* monotonicity along a path: on a tame edge a larger incoming eps dissipates more. *)
Theorem path_dissipation_mono : forall (e : edge_spec) (x y : Q),
  Id (edge_tame e) true -> Qle y x -> Qle (edge_diss e y) (edge_diss e x).
Proof.
  intros e x y Ht Hyx.
  pose proof (edge_tame_spec e Ht) as [Ha Hb].
  assert (H1a : Qle 0 (1 - ed_a e)).
  { apply QleT'_to_Qle.
    exact (uc_le_opp_shift (ed_a e) 1 Hb). }
  assert (Hxy : Qle 0 (x - y)).
  { apply QleT'_to_Qle.
    exact (uc_le_opp_shift y x (Qle_to_QleT' _ _ Hyx)). }
  assert (Hprod : Qle 0 ((1 - ed_a e) * (x - y))).
  { apply (Qle_trans 0 (0 * (x - y)) ((1 - ed_a e) * (x - y))).
    - apply QleT'_to_Qle. apply uc_qeq_le. apply qeq_imp_qeqT. ring.
    - apply (Qmult_le_compat_r 0 (1 - ed_a e) (x - y) H1a Hxy). }
  assert (Heq : edge_diss e x == edge_diss e y + (1 - ed_a e) * (x - y)).
  { unfold edge_diss, edge_map, Qminus. ring. }
  rewrite Heq.
  apply (Qle_trans (edge_diss e y)
                   (edge_diss e y + 0)
                   (edge_diss e y + (1 - ed_a e) * (x - y))).
  - apply QleT'_to_Qle.
    apply (uc_qeq_le_r (edge_diss e y) (edge_diss e y + 0) (edge_diss e y)).
    + apply qeq_imp_qeqT. ring.
    + apply Qle_to_QleT'. apply Qle_refl.
  - apply Qplus_le_compat; [apply Qle_refl | exact Hprod].
Qed.

(* path-level corollary: dissipation stays monotone after composing two tame edges. *)
Theorem path_dissipation_mono_compound : forall (e1 e2 : edge_spec) (x y : Q),
  Id (edge_tame e1) true -> Id (edge_tame e2) true -> Qle y x ->
  Qle (edge_diss (edge_comp e2 e1) y) (edge_diss (edge_comp e2 e1) x).
Proof.
  intros e1 e2 x y H1 H2 Hyx.
  apply (path_dissipation_mono (edge_comp e2 e1) x y).
  - apply edge_tame_comp; assumption.
  - exact Hyx.
Qed.

(* Section 6. Piece 5, the [iou] record: the gap obligation issued on a query miss (re-enterable). *)
(*   mirroring the [check_claim] rejection-code shape of the constitution, the [inr] payload of [resolve] is an iou. *)
(*   a hit is an executable certificate chain: format continuation, positive slope, dissipation within budget, positive output; *)
(*   a miss is an iou: the from-to gap, the dissipation budget delta, the eps slot, the back-referenced query id. *)

Record query : Set := mk_query {
  qr_id : nat;        (* query id *)
  qr_from : nat;      (* the held format *)
  qr_to : nat;        (* the requested format *)
  qr_eps : Q;         (* the incoming eps, the slot of the held bond *)
  qr_delta : Q        (* the dissipation budget delta *)
}.

Record iou : Set := mk_iou {
  iou_from : nat;     (* the gap source format *)
  iou_to : nat;       (* the gap target format *)
  iou_eps : Q;        (* the eps slot to replay *)
  iou_delta : Q;      (* the dissipation budget delta *)
  iou_ref : nat       (* the back-referenced query id: a justified edge then grows into the graph *)
}.

(* issuing an iou: the gap obligation of the query, the only product of a miss; no error is raised. *)
Definition iou_issue (q : query) : iou :=
  mk_iou (qr_from q) (qr_to q) (qr_eps q) (qr_delta q) (qr_id q).

(* the boolean check on [b]: [true] carries the witness [Id b true], [false] carries the payload [(Id b false, iou)]. *)
Definition bool_gate (b : bool) (w : iou) : Or (Id b true) (And (Id b false) iou) :=
  match b as x return Or (Id x true) (And (Id x false) iou) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, w)
  end.

(* the five check functions, executable by [Defined]: source and target format continuation, positive slope, dissipation within budget, positive output. *)
Definition gate_src (e : edge_spec) (q : query)
  : Or (Id (Nat.eqb (ed_src e) (qr_from q)) true)
       (And (Id (Nat.eqb (ed_src e) (qr_from q)) false) iou) :=
  bool_gate (Nat.eqb (ed_src e) (qr_from q)) (iou_issue q).

Definition gate_dst (e : edge_spec) (q : query)
  : Or (Id (Nat.eqb (ed_dst e) (qr_to q)) true)
       (And (Id (Nat.eqb (ed_dst e) (qr_to q)) false) iou) :=
  bool_gate (Nat.eqb (ed_dst e) (qr_to q)) (iou_issue q).

Definition gate_slope (e : edge_spec) (q : query)
  : Or (Id (Qlt_bool 0 (ed_a e)) true)
       (And (Id (Qlt_bool 0 (ed_a e)) false) iou) :=
  bool_gate (Qlt_bool 0 (ed_a e)) (iou_issue q).

Definition gate_diss (e : edge_spec) (q : query)
  : Or (Id (Qle_bool (edge_diss e (qr_eps q)) (qr_delta q)) true)
       (And (Id (Qle_bool (edge_diss e (qr_eps q)) (qr_delta q)) false) iou) :=
  bool_gate (Qle_bool (edge_diss e (qr_eps q)) (qr_delta q)) (iou_issue q).

Definition gate_pos (e : edge_spec) (q : query)
  : Or (Id (Qlt_bool 0 (edge_map e (qr_eps q))) true)
       (And (Id (Qlt_bool 0 (edge_map e (qr_eps q))) false) iou) :=
  bool_gate (Qlt_bool 0 (edge_map e (qr_eps q))) (iou_issue q).

(* the hit certificate: a package of five witnesses, all Set-level [Id] over booleans, extractable. *)
Definition hit_cert (e : edge_spec) (q : query) : Set :=
  And (And (Id (Nat.eqb (ed_src e) (qr_from q)) true)
           (Id (Nat.eqb (ed_dst e) (qr_to q)) true))
      (And (Id (Qlt_bool 0 (ed_a e)) true)
           (And (Id (Qle_bool (edge_diss e (qr_eps q)) (qr_delta q)) true)
                (Id (Qlt_bool 0 (edge_map e (qr_eps q))) true))).

(* single-edge resolution: passing every check issues a certificate, failing any check issues an iou (the [inr] branch carries the payload). *)
Definition resolve1 (e : edge_spec) (q : query) : Or (hit_cert e q) iou :=
  match gate_src e q with
  | inr p => inr (snd p)
  | inl h1 =>
    match gate_dst e q with
    | inr p => inr (snd p)
    | inl h2 =>
      match gate_slope e q with
      | inr p => inr (snd p)
      | inl h3 =>
        match gate_diss e q with
        | inr p => inr (snd p)
        | inl h4 =>
          match gate_pos e q with
          | inr p => inr (snd p)
          | inl h5 => inl (((h1, h2), (h3, (h4, h5))))
          end
        end
      end
    end
  end.

(* the bridge from [Nat.eqb] true to the Set-level [Id] of Leibniz equality. *)
Lemma nat_eqb_id : forall (x y : nat), Id (Nat.eqb x y) true -> Id x y.
Proof.
  intro x. induction x as [| x IH]; intros y H; destruct y as [| y]; simpl in H.
  - apply id_refl.
  - inversion H.
  - inversion H.
  - apply (RealSetoid.eq_Id (Nat.succ x) (Nat.succ y)).
    f_equal. apply RealSetoid.Id_eq. apply IH. exact H.
Qed.

(* semantic shape of the hit certificate: direct witnesses of format continuation plus the Q-level facts. *)
Theorem hit_cert_honest : forall (e : edge_spec) (q : query) (w : hit_cert e q),
  And (And (Id (ed_src e) (qr_from q)) (Id (ed_dst e) (qr_to q)))
      (And (QltT 0 (ed_a e))
           (And (QleT' (edge_diss e (qr_eps q)) (qr_delta q))
                (QltT 0 (edge_map e (qr_eps q))))).
Proof.
  intros e q [[h1 h2] [h3 [h4 h5]]].
  split; [split | split].
  - apply nat_eqb_id. exact h1.
  - apply nat_eqb_id. exact h2.
  - exact h3.
  - split; [exact h4 | exact h5].
Qed.

(* on the rejection branch the payload is the issued iou itself. *)
Lemma bool_gate_inr : forall (b : bool) (w : iou) (p1 : Id b false) (p2 : iou),
  Id (bool_gate b w) (inr (p1, p2)) -> Id p2 w.
Proof.
  intros b w p1 p2 H.
  pose proof (RealSetoid.Id_eq (bool_gate b w) (inr (p1, p2)) H) as E.
  unfold bool_gate in E. destruct b; simpl in E.
  - discriminate E.
  - injection E as E1 E2.
    apply RealSetoid.eq_Id. symmetry. exact E2.
Qed.

(* main theorem of piece 5: a single-edge miss gives an iou carrying the gap obligation (from, to, eps, delta all refer back to the query). *)
Theorem resolve1_inr_fields : forall (e : edge_spec) (q : query) (r : iou),
  Id (resolve1 e q) (inr r) ->
  And (And (Id (iou_from r) (qr_from q)) (Id (iou_to r) (qr_to q)))
      (And (Id (iou_eps r) (qr_eps q)) (Id (iou_delta r) (qr_delta q))).
Proof.
  intros e q r H. unfold resolve1 in H.
  destruct (gate_src e q) as [h1 | [p11 p12]] eqn:Ep1;
    cbv beta iota in H.
  - destruct (gate_dst e q) as [h2 | [p21 p22]] eqn:Ep2;
      cbv beta iota in H.
    + destruct (gate_slope e q) as [h3 | [p31 p32]] eqn:Ep3;
        cbv beta iota in H.
      * destruct (gate_diss e q) as [h4 | [p41 p42]] eqn:Ep4;
          cbv beta iota in H.
        -- destruct (gate_pos e q) as [h5 | [p51 p52]] eqn:Ep5;
             cbv beta iota in H.
           ++ pose proof (RealSetoid.Id_eq _ _ H) as E. discriminate E.
           ++ pose proof (RealSetoid.Id_eq _ _ H) as E.
              injection E as E1.
              pose proof (bool_gate_inr _ _ _ _
                (RealSetoid.eq_Id _ _ Ep5)) as Hpay.
              rewrite <- E1. rewrite Hpay.
              split; [split; reflexivity | split; reflexivity].
        -- pose proof (RealSetoid.Id_eq _ _ H) as E.
           injection E as E1.
           pose proof (bool_gate_inr _ _ _ _
             (RealSetoid.eq_Id _ _ Ep4)) as Hpay.
           rewrite <- E1. rewrite Hpay.
           split; [split; reflexivity | split; reflexivity].
      * pose proof (RealSetoid.Id_eq _ _ H) as E.
        injection E as E1.
        pose proof (bool_gate_inr _ _ _ _
          (RealSetoid.eq_Id _ _ Ep3)) as Hpay.
        rewrite <- E1. rewrite Hpay.
        split; [split; reflexivity | split; reflexivity].
    + pose proof (RealSetoid.Id_eq _ _ H) as E.
      injection E as E1.
      pose proof (bool_gate_inr _ _ _ _
        (RealSetoid.eq_Id _ _ Ep2)) as Hpay.
      rewrite <- E1. rewrite Hpay.
      split; [split; reflexivity | split; reflexivity].
  - pose proof (RealSetoid.Id_eq _ _ H) as E.
    injection E as E1.
    pose proof (bool_gate_inr _ _ _ _
      (RealSetoid.eq_Id _ _ Ep1)) as Hpay.
    rewrite <- E1. rewrite Hpay.
    split; [split; reflexivity | split; reflexivity].
Qed.

(* the graph scan, executable by [Defined]: the first serving edge for the format key (from, to). *)
Fixpoint find_serving (g : list edge_spec) (f t : nat) : option edge_spec :=
  match g with
  | nil => None
  | e :: g' =>
      match Nat.eqb (ed_src e) f with
      | true =>
          match Nat.eqb (ed_dst e) t with
          | true => Some e
          | false => find_serving g' f t
          end
      | false => find_serving g' f t
      end
  end.

Lemma find_serving_cons_some : forall (e : edge_spec) (g : list edge_spec) (f t : nat),
  Nat.eqb (ed_src e) f = true -> Nat.eqb (ed_dst e) t = true ->
  Id (find_serving (e :: g) f t) (Some e).
Proof.
  intros e g f t H1 H2. simpl.
  rewrite H1. rewrite H2. reflexivity.
Qed.

(* graph-level resolution: [Some e] runs the single-edge decision, [None] issues an iou. *)
Definition resolve_opt (o : option edge_spec) (q : query)
  : Or (sigT (fun e => hit_cert e q)) iou :=
  match o with
  | None => inr (iou_issue q)
  | Some e =>
      match resolve1 e q with
      | inl w => inl (existT _ e w)
      | inr r => inr r
      end
  end.

Definition resolve (g : list edge_spec) (q : query)
  : Or (sigT (fun e => hit_cert e q)) iou :=
  resolve_opt (find_serving g (qr_from q) (qr_to q)) q.

Lemma resolve_opt_some : forall (e : edge_spec) (q : query) (w : hit_cert e q),
  Id (resolve1 e q) (inl w) ->
  Id (resolve_opt (Some e) q) (inl (existT _ e w)).
Proof.
  intros e q w H. unfold resolve_opt. rewrite H. reflexivity.
Qed.

(* totality of the decision: every query yields a hit or an iou (mirroring [check_claim_total] of the constitution). *)
Theorem resolve_total : forall (g : list edge_spec) (q : query),
  Or (sigT (fun e => sigT (fun w => Id (resolve g q) (inl (existT _ e w)))))
     (sigT (fun r => Id (resolve g q) (inr r))).
Proof.
  intros g q. unfold resolve, resolve_opt.
  destruct (find_serving g (qr_from q) (qr_to q)) as [e |].
  - destruct (resolve1 e q) as [w | r].
    + left. exists e. exists w. reflexivity.
    + right. exists r. reflexivity.
  - right. exists (iou_issue q). reflexivity.
Qed.

(* graph-level form of piece 5: a miss gives an iou carrying the gap obligation. *)
Theorem resolve_miss_iou : forall (g : list edge_spec) (q : query) (r : iou),
  Id (resolve g q) (inr r) ->
  And (And (Id (iou_from r) (qr_from q)) (Id (iou_to r) (qr_to q)))
      (And (Id (iou_eps r) (qr_eps q)) (Id (iou_delta r) (qr_delta q))).
Proof.
  intros g q r H. unfold resolve, resolve_opt in H.
  destruct (find_serving g (qr_from q) (qr_to q)) as [e |].
  - destruct (resolve1 e q) as [w | r0] eqn:Eq; cbv beta iota in H.
    + pose proof (RealSetoid.Id_eq _ _ H) as E. discriminate E.
    + pose proof (RealSetoid.Id_eq _ _ H) as E.
      injection E as E1.
      pose proof (resolve1_inr_fields e q r0
        (RealSetoid.eq_Id _ _ Eq)) as [[Hf Ht] [He Hd]].
      rewrite <- E1.
      split; [split; assumption | split; assumption].
  - pose proof (RealSetoid.Id_eq _ _ H) as E.
    injection E as E1. rewrite <- E1.
    split; [split; reflexivity | split; reflexivity].
Qed.

(* hit soundness: a hit gives a strictly positive output eps and dissipation within budget (executable certificate semantics). *)
Theorem resolve_hit_sound : forall (g : list edge_spec) (q : query)
                                   (e : edge_spec) (w : hit_cert e q),
  Id (resolve g q) (inl (existT _ e w)) ->
  And (QltT 0 (edge_map e (qr_eps q)))
      (QleT' (edge_diss e (qr_eps q)) (qr_delta q)).
Proof.
  intros g q e w _. destruct w as [_ [_ [h4 h5]]].
  split; assumption.
Qed.

(* Piece 5b, iou re-entry: redeem (justification) and reissue (the obligation persists). *)
(*   [dis_redeem io e] issues a certificate when e closes the gap of io (the new edge can then grow into the graph); *)
(*   an exchange that fails a check re-enters the iou unchanged (the obligation survives and can retry with a new edge). *)

Definition iou_query (io : iou) : query :=
  mk_query (iou_ref io) (iou_from io) (iou_to io) (iou_eps io) (iou_delta io).

Definition dis_redeem (io : iou) (e : edge_spec) : Or (hit_cert e (iou_query io)) iou :=
  resolve1 e (iou_query io).

(* re-entry: a rejection of [dis_redeem] returns an iou whose gap fields agree with the original one pointwise (obligation persistence). *)
Theorem redeem_reissue : forall (io : iou) (e : edge_spec) (r : iou),
  Id (dis_redeem io e) (inr r) ->
  And (And (Id (iou_from r) (iou_from io))
           (And (Id (iou_to r) (iou_to io)) (Id (iou_eps r) (iou_eps io))))
      (Id (iou_delta r) (iou_delta io)).
Proof.
  intros io e r H.
  pose proof H as H'.
  pose proof (resolve1_inr_fields e (iou_query io) r H') as [[Hf Ht] [He Hd]].
  split.
  - split; [exact Hf | split; [exact Ht | exact He]].
  - exact Hd.
Qed.

(* justification: a new edge closing the iou makes the edge grow into the graph and the original query hit (the graph growth theorem). *)
Theorem redeem_closes : forall (io : iou) (e : edge_spec) (g : list edge_spec)
                               (w : hit_cert e (iou_query io)),
  Id (dis_redeem io e) (inl w) ->
  sigT (fun w2 => Id (resolve (e :: g) (iou_query io)) (inl w2)).
Proof.
  intros io e g w Hred.
  destruct w as [[h1 h2] [h3 [h4 h5]]].
  pose proof Hred as Hred'.
  pose proof (RealSetoid.Id_eq (Nat.eqb (ed_src e) (qr_from (iou_query io))) true
                h1) as E1.
  pose proof (RealSetoid.Id_eq (Nat.eqb (ed_dst e) (qr_to (iou_query io))) true
                h2) as E2.
  pose proof (find_serving_cons_some e g (qr_from (iou_query io))
                (qr_to (iou_query io)) E1 E2) as Hfs.
  pose proof (RealSetoid.Id_eq _ _ Hfs) as Efs.
  pose proof (resolve_opt_some e (iou_query io)
              (((h1, h2), (h3, (h4, h5)))) Hred') as Hw2.
  exists (existT (fun e0 : edge_spec => hit_cert e0 (iou_query io)) e
                 (((h1, h2), (h3, (h4, h5))))).
  unfold resolve. rewrite Efs. exact Hw2.
Qed.

(* the decision report, a dependency-free shape: no [sigT], extractable whole, friendly to [vm_compute]. *)

Inductive resolve_verdict : Set :=
| rv_hit : edge_spec -> Q -> resolve_verdict
| rv_miss : iou -> resolve_verdict.

Definition resolve_report (g : list edge_spec) (q : query) : resolve_verdict :=
  match find_serving g (qr_from q) (qr_to q) with
  | None => rv_miss (iou_issue q)
  | Some e =>
      match resolve1 e q with
      | inl w => rv_hit e (Qred (edge_map e (qr_eps q)))
      | inr r => rv_miss r
      end
  end.

(* Section 7. Piece 6, a [vm_compute] numeric self-test: a three-edge graph chaining eps/2, eps/4, eps/8. *)
(*   the graph holds 3 primitive half-dissipating edges plus 2 composite edges (composite closure makes the routing reachable). *)

(* primitive edges fmt0 -> fmt1 -> fmt2 -> fmt3, each segment halving eps (a = 1/2, b = 0, zero injection). *)
Definition e_h1 : edge_spec := mk_edge 1 0 1 (1#2) 0.
Definition e_h2 : edge_spec := mk_edge 2 1 2 (1#2) 0.
Definition e_h3 : edge_spec := mk_edge 3 2 3 (1#2) 0.

(* composite edges grown into the graph: [ec12] spans fmt0 -> fmt2 with slope 1/4; [ec123] spans fmt0 -> fmt3 with slope 1/8. *)
Definition ec12 : edge_spec := edge_comp e_h2 e_h1.
Definition ec123 : edge_spec := edge_comp e_h3 ec12.

Definition atlas3 : list edge_spec := e_h1 :: e_h2 :: e_h3 :: ec12 :: ec123 :: nil.

(* query 7: holds fmt0 with eps slot 1, requests fmt3, dissipation budget delta = 1; hits [ec123]. *)
Definition q_chain : query := mk_query 7 0 3 1 1.
(* query 8: fmt3 -> fmt0 has no edge; a miss issues an iou. *)
Definition q_back : query := mk_query 8 3 0 1 1.
(* query 9: fmt0 -> fmt3 with budget delta = 1/2; the dissipation 7/8 exceeds the budget, an iou (the gap obligation). *)
Definition q_tight : query := mk_query 9 0 3 1 (1#2).

(* chain hit: the output eps is 1/8 (eps carried down to eps/8); the certificate is executable. *)
Theorem demo_chain_hit : Id (resolve_report atlas3 q_chain) (rv_hit ec123 (1#8)).
Proof. vm_compute. reflexivity. Qed.

(* path dissipation: 1 - 1/8 = 7/8 (additive accounting, the sum of the segment dissipations). *)
Theorem demo_diss_total : Id (Qred (edge_diss ec123 1)) (7#8).
Proof. vm_compute. reflexivity. Qed.

Theorem demo_diss_steps : edge_diss ec123 1
  == edge_diss ec12 1 + edge_diss e_h3 (edge_map ec12 1).
Proof. vm_compute. reflexivity. Qed.

(* numeric instance of the conservation identity: 1 = 1/8 + 7/8. *)
Theorem demo_conservation : 1 == edge_map ec123 1 + edge_diss ec123 1.
Proof. vm_compute. reflexivity. Qed.

(* the backward query finds no edge: a miss gives an iou (gap fmt3 -> fmt0, back-reference to query 8). *)
Theorem demo_miss_back : Id (resolve_report atlas3 q_back)
  (rv_miss (mk_iou 3 0 1 1 8)).
Proof. vm_compute. reflexivity. Qed.

(* budget shortfall: the dissipation 7/8 exceeds delta = 1/2, an iou (gap fmt0 -> fmt3, back-reference to query 9). *)
Theorem demo_tight_iou : Id (resolve_report atlas3 q_tight)
  (rv_miss (mk_iou 0 3 1 (1#2) 9)).
Proof. vm_compute. reflexivity. Qed.

(* numeric self-test of piece 5b, iou re-entry: a good edge closes the gap and the new edge grows into the graph. *)

Definition demo_io_tight : iou := mk_iou 0 3 1 (1#2) 9.

(* the good edge fmt0 -> fmt3 with slope 15/16: dissipation 1/16 within the budget 1/2, output 15/16 > 0. *)
Definition e_good : edge_spec := mk_edge 4 0 3 (15#16) 0.

(* [dis_redeem]: the iou [demo_io_tight] is justified by [e_good] (all five witnesses pass). *)
Definition cert_good : hit_cert e_good (iou_query demo_io_tight) :=
  ((@id_refl bool true, @id_refl bool true),
   (@id_refl bool true, (@id_refl bool true, @id_refl bool true))).

Theorem demo_redeem_ok : Id (dis_redeem demo_io_tight e_good) (inl cert_good).
Proof. vm_compute. reflexivity. Qed.

(* numeric instance of [redeem_closes]: with the new edge grown into the graph, the original query 9 hits [e_good]. *)
Definition atlas4 : list edge_spec := e_good :: atlas3.

Theorem demo_growth_closes :
  Id (resolve_report atlas4 q_tight) (rv_hit e_good (15#16)).
Proof. vm_compute. reflexivity. Qed.

(* numeric instance of the re-entry shape: the bad edge, whose negative intercept swallows the eps slot, fails to justify and the iou returns unchanged. *)
Definition e_bad : edge_spec := mk_edge 5 0 3 (15#16) (-1).

Theorem demo_redeem_reissue :
  sigT (fun r => Id (dis_redeem demo_io_tight e_bad) (inr r)).
Proof.
  exists (iou_issue (iou_query demo_io_tight)).
  unfold dis_redeem. vm_compute. reflexivity.
Qed.

(* Section 8. Decision report output: the source of the self-test samples. *)

Eval vm_compute in resolve_report atlas3 q_chain.
Eval vm_compute in resolve_report atlas3 q_back.
Eval vm_compute in resolve_report atlas3 q_tight.
Eval vm_compute in resolve_report atlas4 q_tight.
Eval vm_compute in edge_diss ec123 1.
Eval vm_compute in bond_check (mk_bond 1 (3#2) (1#4) 0).
Eval vm_compute in edge_check e_good.
(* ================= Section 2. The honest_stop family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.PeanoNat.

Local Open Scope Q_scope.

(* Section 0. The accounting objects: the honest stopping time and the chain-side accumulated dissipation. *)

(* the honest stopping time: tau is honest for the chain ch when the observation depth does not exceed the head budget of the chain *)
(*   (the discrete form of an optional stopping time: tau is a legal observation point inside the production window of the chain). *)
Definition honest_stop (tau : nat) (ch : GChain) : Set :=
  NatLe tau (gchain_budget ch).

(* the chain-side accumulated dissipation: each step dissipates this head budget minus the next head budget, *)
(*   the ground node [gstop] resets the count and records zero dissipation (the reset-to-zero convention, matching [gbudget_at]). *)
Fixpoint gdiss_at (n : nat) (ch : GChain) : nat :=
  match n with
  | O => 0%nat
  | Datatypes.S m =>
      match ch with
      | gstop _ _ => 0%nat
      | gstep b _ tl =>
          ((b - gchain_budget tl) + gdiss_at m tl)%nat
      end
  end.

(* Section 1. A-side support: the stopping-time prefix length lemma, the unbounded budget identity, and the explicit prefix dissipation formula. *)

(* stopping-time prefix length: by the A1 reshaping an honest stop puts tau inside the production window [0, b]. *)
Lemma honest_stop_le : forall (k : Q) (tau b : nat) (c : Q),
  honest_stop tau (grun k b c) -> (tau <= b)%nat.
Proof.
  intros k tau b c H.
  exact (NatLe_drop tau b
           (id_trans (id_sym (id_cong (Nat.leb tau) (grun_budget k b c))) H)).
Qed.

(* the unbounded budget identity, the A2 de-guarded saturated extension: at any depth *)
(*   (including the reset segment past the ground) [gbudget_at n (grun k b c) = b - n] holds, nat subtraction saturating at 0. *)
Lemma grun_budget_at_any : forall (k : Q) (n b : nat) (c : Q),
  Id (gbudget_at n (grun k b c)) (b - n)%nat.
Proof.
  intros k n. induction n as [| n IH]; intros b c.
  - destruct b as [| b']; reflexivity.
  - destruct b as [| b'].
    + reflexivity.
    + change (gbudget_at (Datatypes.S n) (grun k (Datatypes.S b') c))
        with (gbudget_at n (grun k b' (c * (1 - k)))).
      replace (Datatypes.S b' - Datatypes.S n)%nat with (b' - n)%nat by lia.
      apply IH.
Qed.

(* the explicit prefix dissipation formula: inside the honest window the chain-side accumulated prefix dissipation is exactly the step count tau *)
(*   (each step decreases the budget by exactly 1, S b' - b' = 1, expanded layer by layer through A1). *)
Lemma grun_diss_prefix : forall (k : Q) (n b : nat) (c : Q),
  NatLe n b -> Id (gdiss_at n (grun k b c)) n.
Proof.
  intros k n. induction n as [| n IH]; intros b c Hn.
  - reflexivity.
  - destruct b as [| b'].
    + apply NatLe_drop in Hn. lia.
    + change (gdiss_at (Datatypes.S n) (grun k (Datatypes.S b') c))
        with ((Datatypes.S b' - gchain_budget (grun k b' (c * (1 - k)))
               + gdiss_at n (grun k b' (c * (1 - k))))%nat).
      assert (Hg : gchain_budget (grun k b' (c * (1 - k))) = b').
      { apply RealSetoid.Id_eq. apply (grun_budget k b' (c * (1 - k))). }
      rewrite Hg.
      assert (Hd : gdiss_at n (grun k b' (c * (1 - k))) = n).
      { apply RealSetoid.Id_eq. apply IH. apply NatLe_lift.
        apply NatLe_drop in Hn. lia. }
      rewrite Hd. apply RealSetoid.eq_Id. lia.
Qed.

(* Section 2. The nat accounting main lemma: budget conservation at the stopping time. *)

(* the main lemma (the nat account): at an honest stopping time tau the remaining budget plus the accumulated dissipation equals the initial budget. *)
(*   assembly: [honest_stop_le] (the A1 reshaping) gives tau <= b, A2 gives the remainder b - tau, *)
(*   the prefix dissipation formula gives the accumulated dissipation tau, and the books close as (b - tau) + tau = b. *)
Theorem stoptime_conservation : forall (k : Q) (tau b : nat) (c : Q),
  honest_stop tau (grun k b c) ->
  Id (PeanoNat.Nat.add (gbudget_at tau (grun k b c)) (gdiss_at tau (grun k b c))) b%nat.
Proof.
  intros k tau b c Hstop.
  pose proof (honest_stop_le k tau b c Hstop) as Hle.
  pose proof (grun_budget_at k tau b c (NatLe_lift tau b Hle)) as Hb.
  pose proof (grun_diss_prefix k tau b c (NatLe_lift tau b Hle)) as Hd.
  apply (id_trans (id_cong2 PeanoNat.Nat.add Hb Hd)).
  apply RealSetoid.eq_Id. lia.
Qed.

(* corollary (the explicit account): the remainder at the stop is b - tau (the A2 original shape) and remainder + tau = b. *)
Corollary stoptime_ledger_explicit : forall (k : Q) (tau b : nat) (c : Q),
  honest_stop tau (grun k b c) ->
  And (Id (gbudget_at tau (grun k b c)) (b - tau)%nat)
      (Id (PeanoNat.Nat.add (gbudget_at tau (grun k b c)) tau) b%nat).
Proof.
  intros k tau b c Hstop.
  pose proof (honest_stop_le k tau b c Hstop) as Hle.
  split.
  - exact (grun_budget_at k tau b c (NatLe_lift tau b Hle)).
  - exact (id_trans
             (id_sym (id_cong2 PeanoNat.Nat.add
                (@id_refl nat (gbudget_at tau (grun k b c)))
                (grun_diss_prefix k tau b c (NatLe_lift tau b Hle))))
             (stoptime_conservation k tau b c Hstop)).
Qed.

(* Section 3. B-side assembly: the iterated eps exchange account, explicit conservation for a finite-step chain in n-step induction form. *)

(* the eps remainder after tau exchange steps (outermost first: each step crosses the edge, then recurses on the remainder). *)
Fixpoint exch_iter (t : nat) (e : edge_spec) (x : Q) : Q :=
  match t with
  | O => x
  | Datatypes.S m => exch_iter m e (edge_map e x)
  end.

(* the dissipation accumulated over tau steps: each station dissipates the [edge_diss] at its incoming value (the same convention as B1). *)
Fixpoint diss_iter (t : nat) (e : edge_spec) (x : Q) : Q :=
  match t with
  | O => 0%Q
  | Datatypes.S m => edge_diss e x + diss_iter m e (edge_map e x)
  end.

(* explicit finite-step conservation (the n-step inductive closure of B1): *)
(*   the initial eps equals the remainder after tau exchange steps plus the dissipation accumulated over tau steps. *)
Lemma diss_iter_conservation : forall (t : nat) (e : edge_spec) (x : Q),
  x == exch_iter t e x + diss_iter t e x.
Proof.
  induction t as [| m IH]; intros e x.
  - apply Qeq_sym. apply Qplus_0_r.
  - change (exch_iter (Datatypes.S m) e x) with (exch_iter m e (edge_map e x)).
    change (diss_iter (Datatypes.S m) e x)
      with (edge_diss e x + diss_iter m e (edge_map e x)).
    remember (edge_map e x) as w eqn:Ew.
    remember (exch_iter m e w) as a eqn:Ea.
    remember (diss_iter m e w) as c eqn:Ec.
    remember (edge_map e w) as b eqn:Eb.
    remember (edge_diss e w) as d eqn:Ed.
    pose proof (IH e w) as H1.
    rewrite <- Ea, <- Ec in H1.   (* H1 : w == a + c *)
    pose proof (diss_conservation e w) as H2.
    rewrite <- Eb, <- Ed in H2.   (* H2 : w == b + d *)
    pose proof (diss_conservation e x) as H3.
    rewrite <- Ew in H3.          (* H3 : x == w + edge_diss e x *)
    apply (Qeq_trans x (w + edge_diss e x) (a + (edge_diss e x + c))).
    + exact H3.
    + apply (Qeq_trans (w + edge_diss e x)
               (b + (d + edge_diss e x))
               (a + (edge_diss e x + c))).
      * rewrite H2. ring.
      * rewrite H2 in H1.
        apply (Qeq_trans (b + (d + edge_diss e x))
                   ((b + d) + edge_diss e x)
                   (a + (edge_diss e x + c))).
        -- ring.
        -- apply (Qeq_trans ((b + d) + edge_diss e x)
                     ((a + c) + edge_diss e x)
                     (a + (edge_diss e x + c))).
           ++ rewrite H1. ring.
           ++ ring.
Qed.

(* prefix additivity at stopping times: splitting the accumulated dissipation at a stop counts each unit once, none twice and none lost *)
(*   (the total over tau1 + tau2 equals the dissipation of the first tau1 segment plus that of the next tau2 segment from tau1 on). *)
Lemma diss_iter_split : forall (s t : nat) (e : edge_spec) (x : Q),
  diss_iter (s + t) e x == diss_iter s e x + diss_iter t e (exch_iter s e x).
Proof.
  induction s as [| m IH]; intros t e x.
  - change (0 + t)%nat with t.
    change (diss_iter 0 e x) with 0%Q.
    change (exch_iter 0 e x) with x.
    apply Qeq_sym. apply Qplus_0_l.
  - change (Datatypes.S m + t)%nat with (Datatypes.S (m + t))%nat.
    change (diss_iter (Datatypes.S (m + t)) e x)
      with (edge_diss e x + diss_iter (m + t) e (edge_map e x)).
    change (diss_iter (Datatypes.S m) e x)
      with (edge_diss e x + diss_iter m e (edge_map e x)).
    change (exch_iter (Datatypes.S m) e x)
      with (exch_iter m e (edge_map e x)).
    pose proof (IH t e (edge_map e x)) as H.
    rewrite H. ring.
Qed.

(* the stopping-time remainder and path dissipation of a two-edge path (the B2 decomposition). *)
Definition exch2 (e1 e2 : edge_spec) (x : Q) : Q :=
  edge_map e2 (edge_map e1 x).
Definition path_diss2 (e1 e2 : edge_spec) (x : Q) : Q :=
  edge_diss e1 x + edge_diss e2 (edge_map e1 x).

(* the B assembly lemma: conservation over a two-edge path combines B1 (one accounting of the composite edge) with B2 (the dissipation decomposition) *)
(*   (the initial eps equals the remainder after both exchanges plus the segment 1 and segment 2 dissipations). *)
Theorem path2_conservation : forall (e1 e2 : edge_spec) (x : Q),
  x == exch2 e1 e2 x + path_diss2 e1 e2 x.
Proof.
  intros e1 e2 x.
  apply (Qeq_trans x
           (edge_map (edge_comp e2 e1) x + edge_diss (edge_comp e2 e1) x)
           (exch2 e1 e2 x + path_diss2 e1 e2 x)).
  - exact (bond_exchange_conservation (edge_comp e2 e1)
             (mk_bond 0%nat 0 x 0%nat)).
  - rewrite edge_compound_affine. rewrite path_dissipation_additive.
    unfold exch2, path_diss2. reflexivity.
Qed.

(* the T-convention exit: the reflected [Qeq_bool] form (the T convention at the Q level). *)
Theorem path2_conservation_T : forall (e1 e2 : edge_spec) (x : Q),
  Id (Qeq_bool x (exch2 e1 e2 x + path_diss2 e1 e2 x)) true.
Proof.
  intros e1 e2 x.
  exact (sf_qeq_id x (exch2 e1 e2 x + path_diss2 e1 e2 x)
           (path2_conservation e1 e2 x)).
Qed.

(* Section 4. The combined main theorem: optional-stopping-time conservation accounting (the A and B accounts both close at the same tau). *)

(* combined main statement: given an honest stopping time tau (a GuardedChain stop, the A1/A2 convention), *)
(*   the nat budget account closes: the remainder at the stop plus the accumulated dissipation equals the initial budget b (total conservation at the stopping instant); *)
(*   the Q eps account closes: the initial eps equals the remainder after tau steps of composite exchange plus the dissipation accumulated over tau steps *)
(*   (B1 closes edge by edge along the tau-step iteration); *)
(*   the same tau closes both accounts at once, the complete shape of optional-stopping-time conservation accounting. *)
Theorem stoptime_conservation_master :
  forall (k : Q) (e1 e2 : edge_spec) (bd : bond) (tau b : nat) (c : Q),
  honest_stop tau (grun k b c) ->
  And (Id (PeanoNat.Nat.add (gbudget_at tau (grun k b c)) (gdiss_at tau (grun k b c)))
           b%nat)
      (bd_eps bd == exch_iter tau (edge_comp e2 e1) (bd_eps bd)
                  + diss_iter tau (edge_comp e2 e1) (bd_eps bd)).
Proof.
  intros k e1 e2 bd tau b c Hstop. split.
  - exact (stoptime_conservation k tau b c Hstop).
  - exact (diss_iter_conservation tau (edge_comp e2 e1) (bd_eps bd)).
Qed.

Print Assumptions stoptime_conservation_master.
Print Assumptions stoptime_conservation.
Print Assumptions path2_conservation.
